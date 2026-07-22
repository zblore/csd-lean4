/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
public import Mathlib.Tactic.IntervalCases
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval

/-!
# Reversible interleaved modular multiply — the general-`n` Horner LOOP  (ECDLP Phase 2, Stage S6.3d-2b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module delivers the **verified general-`n` interleaved MSB-first modular multiply** over `𝔽_p`,
folding the verified Horner loop body (`hornerStep`, S6.3d-2a) over all `n` bits of the multiplier `X`
to leave the accumulator holding `X · Y mod N`. It is the capstone of the modular-arithmetic chain:
the verified field-multiply atom `⟦c⟧ = (· * Yval) mod N` an exhibited EC point op would call.

```
mulLoop L = ((List.range n).map (fun j => hornerStep (L.bank j))).flatMap id
```

processing bits **MSB-first**: loop index `j = 0, …, n-1` runs `hornerStep` on bank `j`, whose control
is bound to `X (n-1-j)` — the `(n-1-j)`-th bit of the multiplier. Each body is one verified Horner step
`acc ← (2·acc + [X_{n-1-j}]·Y) mod N` (`hornerStep_correct`). The banks share the accumulator `B` and the
multiplicand `Y`; every other wire of each bank is FRESH and disjoint (the `Θ(n²)`-ancilla fresh-wire
model inherited from S6.3d-1 / S6.3c).

## The invariant (induction over the processed-bank prefix)

After processing banks `[0, …, k-1]` from `acc = 0`, the accumulator holds `hornerVal k · Yval mod N`,
where `hornerVal k` is the top-`k`-bits-of-`X` MSB-first reconstruction
(`hornerVal 0 = 0`, `hornerVal (k+1) = 2·hornerVal k + bit (n-1-k)`). The step `k → k+1` is exactly the
per-step reasoning of `mulStep2_correct`: `hornerStep_correct` on bank `k` maps
`(hornerVal k · Yval) mod N` to `((2·hornerVal k + bit)·Yval) mod N = (hornerVal (k+1) · Yval) mod N`;
`hornerStep_preserves_Y` keeps `Y`; `hornerStep_preserves_external` keeps the later banks' wires clean and
the not-yet-read `X` bits intact. The bridge `hornerVal n = Xval` (`hornerVal_full`) closes it.

## Carve line (what this is, and is NOT)

This is the **VERIFIED modular field-multiply** `X · Y mod N` — the `⟦c⟧ = op` payoff of the S6.3
Option-1 route — composing the verified Horner step (S6.3d-2a) over all `n` bits.

**Named residue:**

1. **Fresh per-iteration wires ⟹ `Θ(n²)` qubits + `Θ(n²)` Toffoli.** Each of the `n` Horner steps is
   supplied its OWN doubling scratch / carries / ancilla and controlled-add carries / ancilla, disjoint
   from every other step's. This is the honest fresh-ancilla cost. In-place reuse (`Θ(n)` qubits) needs
   the **carry-clean / ancilla-restoring** adder the corpus does NOT yet provide (Cuccaro-style inline
   carry-uncompute, or the self-cleaning high-bit modular adder). That carry-clean adder is the genuine
   orthogonal residue.
2. **This is NOT the EC point operation.** It is the verified modular MULTIPLY over registers
   (`X · Y mod N`), `ℕ` / `mod N` bit arithmetic — no field / group semantics. Assembling these
   field-multiplies into the full elliptic-curve point op (point add / double) is **S6.3e+**, NOT built
   here. And this is the `Θ(n²)`-qubit version, not the optimised in-place one.

## Honest cost

`mulLoop_toffoli` derives `30 * n²` Toffolis: `n` Horner steps, each `30n` (`hornerStep_toffoli`),
composed through `cost_comp_toffoli_count` over the fold (`multiplier_toffoli`).
-/

@[expose] public section

namespace Reversible

variable {m n : ℕ}

/-! ### The Horner reconstruction value (pure `ℕ`)

`hornerVal bits n k` is the top-`k`-bits MSB-first reconstruction of the `n`-bit number whose bits are
`bits 0, …, bits (n-1)` (each `bits i ∈ {0,1}` for the intended use, but the lemmas hold for any `bits`).
The bridge `hornerVal_full` (`hornerVal bits n n = ∑_{i<n} bits i · 2^i`) lets the loop's per-step
recurrence land on the full multiplier value. -/

/-- Top-`k`-bits MSB-first reconstruction: `hornerVal bits n 0 = 0`,
`hornerVal bits n (k+1) = 2 · hornerVal bits n k + bits (n-1-k)`. -/
def hornerVal (bits : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * hornerVal bits n k + bits (n - 1 - k)

@[simp] theorem hornerVal_zero (bits : ℕ → ℕ) (n : ℕ) : hornerVal bits n 0 = 0 := rfl

theorem hornerVal_succ (bits : ℕ → ℕ) (n k : ℕ) :
    hornerVal bits n (k + 1) = 2 * hornerVal bits n k + bits (n - 1 - k) := rfl

/-- **The Horner-reconstruction bridge (auxiliary, all prefixes).** For `k ≤ n`, the top-`k`-bits
reconstruction times `2^(n-k)`, plus the bottom `n-k` bits in place value, is the full value. -/
theorem hornerVal_aux (bits : ℕ → ℕ) (n : ℕ) :
    ∀ k, k ≤ n →
      hornerVal bits n k * 2 ^ (n - k) + (∑ i ∈ Finset.range (n - k), bits i * 2 ^ i)
        = ∑ i ∈ Finset.range n, bits i * 2 ^ i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk1
    have hk : k ≤ n := Nat.le_of_succ_le hk1
    have hnk : n - k = (n - (k + 1)) + 1 := by omega
    rw [hornerVal_succ]
    rw [hnk, Finset.sum_range_succ, pow_succ] at ih
    have hidx : n - 1 - k = n - (k + 1) := by omega
    rw [hidx, ← ih hk]
    ring_nf

/-- **The Horner-reconstruction bridge.** The full `n`-bit MSB-first reconstruction equals the place-value
sum `∑_{i<n} bits i · 2^i`. Specialised from `hornerVal_aux` at `k = n`. -/
theorem hornerVal_full (bits : ℕ → ℕ) (n : ℕ) :
    hornerVal bits n n = ∑ i ∈ Finset.range n, bits i * 2 ^ i := by
  have := hornerVal_aux bits n n (le_refl n)
  simpa using this

/-- The control-bit indicator `bit i = if s (X i) then 1 else 0`, as a `ℕ`. The place-value sum of these
indicators over `[0, n)` is exactly `regValRange X s n`. -/
theorem regValRange_eq_hornerVal_bits {m : ℕ} (X : ℕ → Fin m) (s : State m) (n : ℕ) :
    regValRange X s n = hornerVal (fun i => if s (X i) then 1 else 0) n n := by
  rw [hornerVal_full]
  simp only [regValRange]
  apply Finset.sum_congr rfl
  intro i _
  cases s (X i) <;> simp

/-! ### The `n`-bank multiply-loop layout

A `MulLoopLayout` bundles `n` per-bit `HornerStepLayout` banks (`bank j`, S6.3d-2a), all sharing the
accumulator `B` (`(bank j).B = B`) and the multiplicand `Y` (`(bank j).Y = Y`), with bank `j`'s control
bound to `X (n-1-j)` (MSB-first). The inter-bank geometry needed to fold the steps — bank `j`'s circuit
must not touch any of bank `k`'s clean / preset wires (`k ≠ k`), nor the not-yet-read control bits — is
carried by the membership-based footprints `Touches` / `Clean` and the single disjointness field
`hInter`. This is **bounded and inhabitable for every `n`** (no unbounded `ℕ → Fin m` injectivity
field): the witness assigns each bank a disjoint contiguous block of fresh wires and discharges `hInter`
/ `hCtrl*` by `omega`, and `Touches`/`Clean` are decidable finite disjunctions over the 18/14 families.

`Touches L j w` holds iff `w` is one of bank `j`'s 18 touched wire families; `Clean L k w` iff `w` is one
of bank `k`'s 14 clean/preset families (the ones whose initial value bank `k`'s `hornerStep_correct`
reads). The field `hInter` says: for `j ≠ k`, a clean wire of bank `k` is not touched by bank `j` — which
is exactly what `hornerStep_preserves_external` needs to transport bank `k`'s preconditions through bank
`j`'s step. -/

/-- The 18 wire families bank `j`'s `hornerStep` circuit touches (writes or reads), as a membership
predicate over wires. (The doubling block's `B` is the shared accumulator, listed once via `add.B`.) -/
def Touches (L : ℕ → HornerStepLayout m n) (j : ℕ) (w : Fin m) : Prop :=
  (∃ i, w = (L j).dbl.B i) ∨ (∃ i, w = (L j).dbl.Aop i) ∨
  (∃ i, w = (L j).dbl.addLayout.Cadd i) ∨ (∃ i, w = (L j).dbl.addLayout.A1 i) ∨
  (∃ i, w = (L j).dbl.addLayout.C1 i) ∨ (∃ i, w = (L j).dbl.addLayout.A2 i) ∨
  (∃ i, w = (L j).dbl.addLayout.C2 i) ∨ w = (L j).dbl.addLayout.anc ∨
  (∃ i, w = (L j).add.Aop i) ∨ (∃ i, w = (L j).add.B i) ∨ w = (L j).add.ctrl ∨
  (∃ i, w = (L j).add.Ccadd i) ∨ w = (L j).add.ancC ∨
  (∃ i, w = (L j).add.A1 i) ∨ (∃ i, w = (L j).add.C1 i) ∨ (∃ i, w = (L j).add.A2 i) ∨
  (∃ i, w = (L j).add.C2 i) ∨ w = (L j).add.anc

/-- The 14 wire families bank `k`'s `hornerStep_correct` reads as a clean / preset precondition: the
doubling scratch / carries / ancilla / presets and the controlled-add carries / ancilla / presets. (The
shared `B`, `Y` and the control bit are handled separately.) -/
def Clean (L : ℕ → HornerStepLayout m n) (k : ℕ) (w : Fin m) : Prop :=
  (∃ i, w = (L k).dbl.Aop i) ∨ (∃ i, w = (L k).dbl.addLayout.Cadd i) ∨
  (∃ i, w = (L k).dbl.addLayout.C1 i) ∨ (∃ i, w = (L k).dbl.addLayout.C2 i) ∨
  w = (L k).dbl.addLayout.anc ∨ (∃ i, w = (L k).dbl.addLayout.A1 i) ∨
  (∃ i, w = (L k).dbl.addLayout.A2 i) ∨ (∃ i, w = (L k).add.Ccadd i) ∨
  w = (L k).add.ancC ∨ (∃ i, w = (L k).add.C1 i) ∨ (∃ i, w = (L k).add.C2 i) ∨
  w = (L k).add.anc ∨ (∃ i, w = (L k).add.A1 i) ∨ (∃ i, w = (L k).add.A2 i)

/-- An `n`-bank modular-multiply loop layout on `Fin m`. The `n` banks share `B` and `Y`; bank `j`'s
control is `X (n-1-j)`; bank `j` does not touch bank `k`'s clean wires for `k ≠ j` (`hInter`), nor any
control bit `X i` other than its own (`hCtrlTouch`), and `X`/`B`/`Y` registers are injective on `[0,n)`.
All hypotheses are bounded (`< n`), so the schema is inhabitable for every `n`. -/
structure MulLoopLayout (m n : ℕ) where
  /-- The `n` per-bit Horner-step banks (`bank j` processes bit `n-1-j`). -/
  bank : ℕ → HornerStepLayout m n
  /-- Shared multiplier (control) register `X`; bank `j` reads bit `X (n-1-j)`. -/
  X : ℕ → Fin m
  /-- Sharing: every bank acts on the same accumulator `B`. -/
  hBshare : ∀ j j', (bank j).B = (bank j').B
  /-- Sharing: every bank reads the same multiplicand `Y`. -/
  hYshare : ∀ j j', (bank j).Y = (bank j').Y
  /-- Bank `j`'s control bit is `X (n-1-j)`. -/
  hctrl : ∀ j, (bank j).ctrl = X (n - 1 - j)
  /-- Inter-bank disjointness: for `j ≠ k`, bank `j`'s circuit does not touch bank `k`'s clean wires. -/
  hInter : ∀ j k w, j < n → k < n → j ≠ k → Clean bank k w → ¬ Touches bank j w
  /-- Bank `j`'s circuit does not touch the control bit `X i` unless `i = n-1-j` (its own). -/
  hCtrlTouch : ∀ j i, j < n → i < n → i ≠ n - 1 - j → ¬ Touches bank j (X i)
  /-- The control register is injective on `[0, n)`. -/
  hXinj : ∀ i i', i < n → i' < n → X i = X i' → i = i'

variable {L : MulLoopLayout m n}

/-- The shared accumulator register (`B` of bank `0`). -/
def MulLoopLayout.B (L : MulLoopLayout m n) : ℕ → Fin m := (L.bank 0).B

/-- The shared multiplicand register (`Y` of bank `0`). -/
def MulLoopLayout.Y (L : MulLoopLayout m n) : ℕ → Fin m := (L.bank 0).Y

/-- A wire not touched by bank `j` survives bank `j`'s Horner step. (The `Touches` predicate lists
exactly the 18 families `hornerStep_preserves_external` requires disjointness from.) -/
theorem notTouches_preserved (L : MulLoopLayout m n) (j : ℕ) (s : State m) (w : Fin m)
    (hw : ¬ Touches L.bank j w) :
    denote (hornerStep (L.bank j)) s w = s w := by
  -- unfold the disjunction once into the 18 negated existentials / equalities
  simp only [Touches, not_or, not_exists] at hw
  obtain ⟨hB, hAop, hCadd, hA1, hC1, hA2, hC2, hanc, haAop, haB, hactrl, haCcadd, haancC,
    haA1, haC1, haA2, haC2, haanc⟩ := hw
  exact hornerStep_preserves_external (L.bank j) s w hB hAop hCadd hA1 hC1 hA2 hC2 hanc
    (fun k _ => haAop k) haB hactrl (fun k _ => haCcadd k) haancC haA1 haC1 haA2 haC2 haanc

/-- A clean wire of bank `k` survives bank `j`'s Horner step (`j ≠ k`, both `< n`): by `hInter` it is
not touched, so `notTouches_preserved` applies. The 14 `Clean`-membership constructors are unfolded at
each call site (the `mulLoop_invariant` step transports bank `k`'s preconditions through bank `j`). -/
theorem bank_step_preserves_clean (L : MulLoopLayout m n) (j k : ℕ) (hj : j < n) (hk : k < n)
    (hjk : j ≠ k) (s : State m) (w : Fin m) (hw : Clean L.bank k w) :
    denote (hornerStep (L.bank j)) s w = s w :=
  notTouches_preserved L j s w (L.hInter j k w hj hk hjk hw)

/-- **The Horner arithmetic step.** Folding one MSB-first Horner digit through the running residue:
`(2·((H·Y) mod N) + [bit]·Y) mod N = ((2·H + [bit])·Y) mod N`, i.e. the value `hornerStep_correct`
produces from `c = (H·Y) mod N` is `(hornerVal-next · Y) mod N`. (`Nat.add_mod` / `Nat.mul_mod` absorb
the inner reduction; the `if` is the 0/1 digit.) -/
theorem horner_mod_step (H Yval N : ℕ) (b : Bool) :
    (2 * ((H * Yval) % N) + (if b then Yval else 0)) % N
      = ((2 * H + (if b then 1 else 0)) * Yval) % N := by
  -- (2 * (X % N)) % N = (2 * X) % N  (X := H * Yval), via Nat.mul_mod
  have hdbl : (2 * ((H * Yval) % N)) % N = (2 * (H * Yval)) % N := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  -- absorb the inner reduction, then rewrite the integrand by `ring` (cases on the digit)
  rw [Nat.add_mod, hdbl, ← Nat.add_mod]
  congr 1
  cases b <;> simp <;> ring

/-! ### The general-`n` multiply loop and its correctness -/

/-- **The general-`n` modular-multiply loop.** Process the multiplier bits MSB-first: bank `j`
(`j = 0, …, n-1`) runs one verified Horner step `acc ← (2·acc + [X_{n-1-j}]·Y) mod N`. The banks share
the accumulator `B` and the multiplicand `Y`; every other wire is fresh. -/
def mulLoop (L : MulLoopLayout m n) : Circuit m :=
  ((List.range n).map (fun j => hornerStep (L.bank j))).flatMap id

/-- The first `k` banks of the loop (prefix `[0, …, k-1]`), the induction handle for `mulLoop`. -/
def mulLoopUpto (L : MulLoopLayout m n) (k : ℕ) : Circuit m :=
  ((List.range k).map (fun j => hornerStep (L.bank j))).flatMap id

@[simp] theorem mulLoopUpto_zero (L : MulLoopLayout m n) : mulLoopUpto L 0 = [] := rfl

theorem mulLoop_eq_upto (L : MulLoopLayout m n) : mulLoop L = mulLoopUpto L n := rfl

/-- Split the prefix at its last bank: `mulLoopUpto L (k+1) = mulLoopUpto L k ++ hornerStep (bank k)`
(bank `k` runs LAST). From `List.range_succ`. -/
theorem mulLoopUpto_succ (L : MulLoopLayout m n) (k : ℕ) :
    mulLoopUpto L (k + 1) = mulLoopUpto L k ++ hornerStep (L.bank k) := by
  simp [mulLoopUpto, List.range_succ, List.map_append, List.flatMap_append]

/-- **Prefix frame.** A wire not touched by any bank `j < k` survives the whole prefix
`mulLoopUpto L k` (fold of `notTouches_preserved`). -/
theorem mulLoopUpto_preserves (L : MulLoopLayout m n) (k : ℕ) (s : State m) (w : Fin m)
    (hw : ∀ j, j < k → ¬ Touches L.bank j w) :
    denote (mulLoopUpto L k) s w = s w := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [mulLoopUpto_succ, denote_append,
      notTouches_preserved L k _ w (hw k (Nat.lt_succ_self k))]
    exact ih s (fun j hj => hw j (Nat.lt_succ_of_lt hj))

/-! ### Preservation of bank `k`'s preconditions through the prefix

Every clean / preset wire of bank `k` lies in `Clean L.bank k`, so (for `k ≤ n` and the prefix length
`≤ k`) it is untouched by every earlier bank `j < k` (`hInter`) and survives `mulLoopUpto`. The control
bit `X (n-1-k)` survives via `hCtrlTouch`. These are the lemmas the invariant's step consumes. -/

theorem clean_pres (L : MulLoopLayout m n) {k p : ℕ} (hk : k < n) (hpk : p ≤ k) (s : State m)
    (w : Fin m) (hw : Clean L.bank k w) : denote (mulLoopUpto L p) s w = s w :=
  mulLoopUpto_preserves L p s w
    (fun j hj => L.hInter j k w (by omega) hk (by omega) hw)

theorem clean_pres_reg (L : MulLoopLayout m n) {k p : ℕ} (hk : k < n) (hpk : p ≤ k)
    (s : State m) (f : ℕ → Fin m) (hf : ∀ i, Clean L.bank k (f i)) (q : ℕ) :
    regValRange f (denote (mulLoopUpto L p) s) q = regValRange f s q :=
  Finset.sum_congr rfl fun i _ => by
    show (denote (mulLoopUpto L p) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
    rw [clean_pres L hk hpk s (f i) (hf i)]

/-- **The multiply-loop invariant.** After the first `k` banks (`k ≤ n`), the accumulator holds
`(hornerVal bits n k · Yval) mod N` (`bits i = [X i]`) and the multiplicand still holds `Yval`. By
induction on `k`, splitting the last bank (`mulLoopUpto_succ`): the prefix preserves bank `k`'s clean /
preset wires (`clean_pres`) and its control bit (`hCtrlTouch`); `hornerStep_correct` then advances the
residue (`horner_mod_step`), `hornerStep_preserves_Y` keeps `Yval`. -/
theorem mulLoop_invariant (L : MulLoopLayout m n) (s : State m) {N Yval : ℕ}
    (h2N : 2 * N ≤ 2 ^ n) (hNpos : 0 < N) (hYN : Yval < N)
    -- shared accumulator starts at 0, multiplicand holds Yval
    (hB0 : regValRange L.B s n = 0) (hYv : regValRange L.Y s n = Yval)
    -- every bank's clean wires are false at the initial state
    (hcleanAop : ∀ j i, j < n → i < n → s ((L.bank j).dbl.Aop i) = false)
    (hcleanCadd : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.Cadd i) = false)
    (hcleandC1 : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.C1 i) = false)
    (hcleandC2 : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.C2 i) = false)
    (hcleandanc : ∀ j, j < n → s (L.bank j).dbl.addLayout.anc = false)
    (hcleanCcadd : ∀ j i, j < n → s ((L.bank j).add.Ccadd i) = false)
    (hcleanancC : ∀ j, j < n → s (L.bank j).add.ancC = false)
    (hcleanC1 : ∀ j i, j < n → s ((L.bank j).add.C1 i) = false)
    (hcleanC2 : ∀ j i, j < n → s ((L.bank j).add.C2 i) = false)
    (hcleananc : ∀ j, j < n → s (L.bank j).add.anc = false)
    -- every bank's reduce presets at the initial state
    (hA1dbl : ∀ j, j < n → regValRange (L.bank j).dbl.addLayout.A1 s n = 2 ^ n - N)
    (hA2dbl : ∀ j, j < n → regValRange (L.bank j).dbl.addLayout.A2 s n = N)
    (hA1add : ∀ j, j < n → regValRange (L.bank j).add.A1 s n = 2 ^ n - N)
    (hA2add : ∀ j, j < n → regValRange (L.bank j).add.A2 s n = N) :
    ∀ k, k ≤ n →
      regValRange L.B (denote (mulLoopUpto L k) s) n
        = (hornerVal (fun i => if s (L.X i) then 1 else 0) n k * Yval) % N
      ∧ regValRange L.Y (denote (mulLoopUpto L k) s) n = Yval := by
  intro k
  induction k with
  | zero => intro _; rw [mulLoopUpto_zero]; simp [hB0, hYv, hornerVal_zero]
  | succ k ih =>
    intro hk1
    have hk : k < n := by omega
    obtain ⟨ihB, ihY⟩ := ih (le_of_lt hk)
    set s1 := denote (mulLoopUpto L k) s with hs1def
    rw [mulLoopUpto_succ, denote_append, ← hs1def]
    -- abbreviations for bank k's value at s1
    set bits := fun i => if s (L.X i) then 1 else 0 with hbits
    set Hk := hornerVal bits n k with hHk
    -- bank k shares B and Y with bank 0
    have hBk_eq : (L.bank k).B = L.B := L.hBshare k 0
    have hYk_eq : (L.bank k).Y = L.Y := L.hYshare k 0
    -- B at s1 = (Hk * Yval) % N  (via the running accumulator), < N
    have hBk : regValRange (L.bank k).B s1 n = (Hk * Yval) % N := by rw [hBk_eq]; exact ihB
    have hcN : (Hk * Yval) % N < N := Nat.mod_lt _ hNpos
    have hYk : regValRange (L.bank k).Y s1 n = Yval := by rw [hYk_eq]; exact ihY
    -- bank k's clean wires survive the prefix (each is in Clean L.bank k)
    have hAop0' : ∀ i, i < n → s1 ((L.bank k).dbl.Aop i) = false := fun i hi => by
      rw [hs1def, clean_pres L hk (le_refl k) s _ (Or.inl ⟨i, rfl⟩)]; exact hcleanAop k i hk hi
    have hCadd' : ∀ i, s1 ((L.bank k).dbl.addLayout.Cadd i) = false := fun i => by
      rw [hs1def, clean_pres L hk (le_refl k) s _ (Or.inr (Or.inl ⟨i, rfl⟩))]; exact hcleanCadd k i hk
    have hdC1' : ∀ i, s1 ((L.bank k).dbl.addLayout.C1 i) = false := fun i => by
      rw [hs1def, clean_pres L hk (le_refl k) s _ (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))]
      exact hcleandC1 k i hk
    have hdC2' : ∀ i, s1 ((L.bank k).dbl.addLayout.C2 i) = false := fun i => by
      rw [hs1def, clean_pres L hk (le_refl k) s _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))]
      exact hcleandC2 k i hk
    have hdanc' : s1 (L.bank k).dbl.addLayout.anc = false := by
      rw [hs1def, clean_pres L hk (le_refl k) s _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hcleandanc k hk
    have hCcadd' : ∀ i, s1 ((L.bank k).add.Ccadd i) = false := fun i => by
      rw [hs1def, clean_pres L hk (le_refl k) s _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))))))]
      exact hcleanCcadd k i hk
    have hancC' : s1 (L.bank k).add.ancC = false := by
      rw [hs1def, clean_pres L hk (le_refl k) s _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) ]
      exact hcleanancC k hk
    have hC1' : ∀ i, s1 ((L.bank k).add.C1 i) = false := fun i => by
      rw [hs1def, clean_pres L hk (le_refl k) s _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))))))) ]
      exact hcleanC1 k i hk
    have hC2' : ∀ i, s1 ((L.bank k).add.C2 i) = false := fun i => by
      rw [hs1def, clean_pres L hk (le_refl k) s _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))))))))) ]
      exact hcleanC2 k i hk
    have hanc' : s1 (L.bank k).add.anc = false := by
      rw [hs1def, clean_pres L hk (le_refl k) s _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))) ]
      exact hcleananc k hk
    -- bank k's presets survive the prefix (A1, A2 are in Clean)
    have hA1dbl' : regValRange (L.bank k).dbl.addLayout.A1 s1 n = 2 ^ n - N := by
      rw [hs1def, clean_pres_reg L hk (le_refl k) s _
        (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))))]
      exact hA1dbl k hk
    have hA2dbl' : regValRange (L.bank k).dbl.addLayout.A2 s1 n = N := by
      rw [hs1def, clean_pres_reg L hk (le_refl k) s _
        (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))))]
      exact hA2dbl k hk
    have hA1add' : regValRange (L.bank k).add.A1 s1 n = 2 ^ n - N := by
      rw [hs1def, clean_pres_reg L hk (le_refl k) s _
        (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))))))))))]
      exact hA1add k hk
    have hA2add' : regValRange (L.bank k).add.A2 s1 n = N := by
      rw [hs1def, clean_pres_reg L hk (le_refl k) s _
        (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))))))))))))) ]
      exact hA2add k hk
    -- bank k's control bit X (n-1-k) survives the prefix
    have hctrlk : s1 (L.bank k).add.ctrl = s (L.X (n - 1 - k)) := by
      rw [show (L.bank k).add.ctrl = (L.bank k).ctrl from rfl, L.hctrl k, hs1def]
      apply mulLoopUpto_preserves L k s
      intro j hj
      exact L.hCtrlTouch j (n - 1 - k) (by omega) (by omega) (by omega)
    -- STEP: hornerStep_correct on bank k advances the residue
    have hstep := hornerStep_correct (L.bank k) s1 hAop0' hCadd' hdC1' hdC2' hdanc' hCcadd' hancC'
      hC1' hC2' hanc' h2N hA1dbl' hA2dbl' hA1add' hA2add' hBk hcN hYk hYN
    -- and preserves Y
    have hYstep := hornerStep_preserves_Y (L.bank k) s1 hCcadd' hancC' hYk
    refine ⟨?_, ?_⟩
    · -- value: (2*((Hk*Yval)%N) + [X(n-1-k)]*Yval) % N = (hornerVal (k+1) * Yval) % N
      rw [show L.B = (L.bank k).B from hBk_eq.symm, hstep, hctrlk]
      rw [horner_mod_step Hk Yval N (s (L.X (n - 1 - k)))]
      rw [hornerVal_succ, ← hHk]
    · rw [show L.Y = (L.bank k).Y from hYk_eq.symm]; exact hYstep

/-- **The verified general-`n` modular field multiply (the S6.3d-2b headline).** Under the accumulator
initialised `0`, the multiplicand `Y` holding `Yval < N`, `2N ≤ 2ⁿ`, `0 < N`, and every bank's
clean / preset wires set (carries / ancilla `false`, presets `A1 = 2ⁿ − N`, `A2 = N`), the loop leaves
the accumulator holding `(X · Yval) mod N`, with the multiplier `X` arbitrary:
`regValRange B (denote (mulLoop L) s) n = (regValRange X s n · Yval) % N`.

Proof: `mulLoop_invariant` at `k = n` gives `(hornerVal bits n n · Yval) % N`; `hornerVal_full` /
`regValRange_eq_hornerVal_bits` bridges `hornerVal bits n n = regValRange X s n` (top `n` bits of an
`n`-bit number is itself). -/
theorem mulLoop_correct (L : MulLoopLayout m n) (s : State m) {N Yval : ℕ}
    (h2N : 2 * N ≤ 2 ^ n) (hNpos : 0 < N) (hYN : Yval < N)
    (hB0 : regValRange L.B s n = 0) (hYv : regValRange L.Y s n = Yval)
    (hcleanAop : ∀ j i, j < n → i < n → s ((L.bank j).dbl.Aop i) = false)
    (hcleanCadd : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.Cadd i) = false)
    (hcleandC1 : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.C1 i) = false)
    (hcleandC2 : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.C2 i) = false)
    (hcleandanc : ∀ j, j < n → s (L.bank j).dbl.addLayout.anc = false)
    (hcleanCcadd : ∀ j i, j < n → s ((L.bank j).add.Ccadd i) = false)
    (hcleanancC : ∀ j, j < n → s (L.bank j).add.ancC = false)
    (hcleanC1 : ∀ j i, j < n → s ((L.bank j).add.C1 i) = false)
    (hcleanC2 : ∀ j i, j < n → s ((L.bank j).add.C2 i) = false)
    (hcleananc : ∀ j, j < n → s (L.bank j).add.anc = false)
    (hA1dbl : ∀ j, j < n → regValRange (L.bank j).dbl.addLayout.A1 s n = 2 ^ n - N)
    (hA2dbl : ∀ j, j < n → regValRange (L.bank j).dbl.addLayout.A2 s n = N)
    (hA1add : ∀ j, j < n → regValRange (L.bank j).add.A1 s n = 2 ^ n - N)
    (hA2add : ∀ j, j < n → regValRange (L.bank j).add.A2 s n = N) :
    regValRange L.B (denote (mulLoop L) s) n = (regValRange L.X s n * Yval) % N := by
  rw [mulLoop_eq_upto]
  have h := (mulLoop_invariant L s h2N hNpos hYN hB0 hYv hcleanAop hcleanCadd hcleandC1 hcleandC2
    hcleandanc hcleanCcadd hcleanancC hcleanC1 hcleanC2 hcleananc hA1dbl hA2dbl hA1add hA2add n
    (le_refl n)).1
  rw [h, ← regValRange_eq_hornerVal_bits]

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the general-`n` modular multiply**: `30 · n²` Toffolis. The loop is `n`
Horner steps (`hornerStep_toffoli`, `30n` each), composed through the fold; `multiplier_toffoli` turns the
concatenation cost into the sum of the per-step counts, which is `n · 30n = 30n²`.

Honest reading: this is the `Θ(n²)`-Toffoli, `Θ(n²)`-qubit fresh-ancilla figure — each of the `n` steps
uses its own fresh scratch / carries / ancilla. The optimised in-place (`Θ(n)`-qubit) version needs the
carry-clean / ancilla-restoring adder the corpus does not yet provide. -/
theorem mulLoop_toffoli (L : MulLoopLayout m n) :
    (circuitCost (mulLoop L)).toffoli = 30 * n ^ 2 := by
  rw [show mulLoop L = multiplier ((List.range n).map (fun j => hornerStep (L.bank j))) from rfl,
    multiplier_toffoli, List.map_map]
  have hconst : (List.range n).map ((fun c => (circuitCost c).toffoli) ∘ fun j => hornerStep (L.bank j))
      = (List.range n).map (fun _ => 30 * n) := by
    apply List.map_congr_left
    intro j _; simp only [Function.comp_apply, hornerStep_toffoli]
  rw [hconst, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  ring

/-! ### Concrete witness: a 3-bank (`n = 3`) modular multiply on `Fin 135`

A genuine `MulLoopLayout 135 3`, exhibiting `MulLoopLayout` is inhabited and `mulLoop_correct` applies.
Shared accumulator `B → {0,1,2}`, multiplicand `Y → {3,4,5}`, 3-bit multiplier `X → {6,7,8}` (bit `j`
on wire `6+j`, so bank `j` reads `X (2-j)` = wire `6+(2-j)` = the high-to-low MSB-first order). Each
bank `j` owns the disjoint fresh block `[9 + 42·j, 9 + 42·(j+1))` of `Fin 135`. All disjointness /
injectivity is linear-arithmetic on the wire indices (`omega`), so the schema is manifestly inhabitable;
the same stride formula inhabits every `n` (only the ambient `Fin m` grows). -/

/-- Bank `j`'s doubling sub-layout on `Fin 135`: private block `[base, base+22)` with `base = 9+42·j`.
All wire families are `⟨base + offset + min i width, _⟩`, so every geometry field is `omega`. -/
def wDbl (base : ℕ) (hlo : 9 ≤ base) (hb : base + 22 ≤ 135) : ModDoubleLayout 135 3 where
  addLayout :=
    { Aop i := ⟨base + 0 + min i 2, by omega⟩
      B i := ⟨min i 2, by omega⟩
      Cadd i := ⟨base + 3 + min i 3, by omega⟩
      A1 i := ⟨base + 7 + min i 2, by omega⟩
      C1 i := ⟨base + 10 + min i 3, by omega⟩
      A2 i := ⟨base + 14 + min i 2, by omega⟩
      C2 i := ⟨base + 17 + min i 3, by omega⟩
      anc := ⟨base + 21, by omega⟩
      hAopB i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hCaddinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hC1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hC2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hflagA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflagB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflagC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflaganc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hC2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hC2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega }

/-- Bank `j`'s controlled-add sub-layout on `Fin 135`: operand `Y → {3,4,5}`, control `X (2-j)` =
wire `6 + (2-j)`, private block `[base+22, base+42)` with `base = 9+42·j`. -/
def wAdd (base ctrl : ℕ) (hlo : 9 ≤ base) (hb : base + 42 ≤ 135) (hc1 : 6 ≤ ctrl) (hc2 : ctrl < 9) :
    CModAddLayout 135 3 where
  Aop i := ⟨3 + min i 2, by omega⟩
  B i := ⟨min i 2, by omega⟩
  Ccadd i := ⟨base + 22 + min i 3, by omega⟩
  ctrl := ⟨ctrl, by omega⟩
  ancC := ⟨base + 26, by omega⟩
  A1 i := ⟨base + 27 + min i 2, by omega⟩
  C1 i := ⟨base + 30 + min i 3, by omega⟩
  A2 i := ⟨base + 34 + min i 2, by omega⟩
  C2 i := ⟨base + 37 + min i 3, by omega⟩
  anc := ⟨base + 41, by omega⟩
  hAopB i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopCcadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBCcadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hCcaddinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hctrlAop i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlB i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlCcadd i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlancC := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCAop i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCB i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCCcadd i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hC1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hC2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hflagA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflagB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflagC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflaganc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hC2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hC2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCcaddA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCcaddC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCcaddA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCcaddC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCcaddanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hctrlanc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancCanc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega

/-- Bank `j` (`j < 3`) as a `HornerStepLayout 135 3`: doubling block `wDbl`, controlled-add block `wAdd`
(control `X (2-j)` = wire `6 + (2-j)`), sharing `B → {0,1,2}`. The 70 cross-disjointness fields are all
linear-arithmetic on the block offsets (`omega`). -/
def wBank (j : ℕ) : HornerStepLayout 135 3 where
  dbl := wDbl (9 + 42 * min j 2) (by omega) (by omega)
  add := wAdd (9 + 42 * min j 2) (6 + (2 - min j 2)) (by omega) (by omega) (by omega) (by omega)
  hBshared := by rfl
  hAopAop i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopctrl i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopCcadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopancC i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddAop i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddctrl i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddCcadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddancC i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hCaddanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1Aop i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1ctrl i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1Ccadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1ancC i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1A2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA1anc i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1Aop i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1ctrl i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1Ccadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1ancC i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1A2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC1anc i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2Aop i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2ctrl i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2Ccadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2ancC i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2A2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdA2anc i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2Aop i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2ctrl i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2Ccadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2ancC i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2A2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdC2anc i := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancAop j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancctrl := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancCcadd j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancancC := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega
  hdancanc := by rw [ne_eq, Fin.ext_iff]; dsimp only [wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B, HornerStepLayout.ctrl]; omega

/-- Every `Clean (wBank ·) k w` wire (`k < 3`) lies in bank `k`'s private block
`[9 + 42·k, 9 + 42·k + 42)`. (All 14 clean / preset families are private; none is `B`, `Y` or `X`.) -/
theorem wBank_clean_range (k : ℕ) (hk : k < 3) (w : Fin 135)
    (hw : Clean wBank k w) :
    9 + 42 * k ≤ w.val ∧ w.val < 9 + 42 * k + 42 := by
  simp only [Clean, wBank, wDbl, wAdd, ModDoubleLayout.Aop] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> (dsimp only; omega)

/-- Every `Touches (wBank ·) j w` wire (`j < 3`) lies in `{0,…,5} ∪ {6 + (2 - j)} ∪
[9 + 42·j, 9 + 42·j + 42)` — bank `j`'s shared `B`/`Y`, its own control bit, and its private block. -/
theorem wBank_touch_range (j : ℕ) (hj : j < 3) (w : Fin 135)
    (hw : Touches wBank j w) :
    w.val < 6 ∨ w.val = 6 + (2 - j) ∨ (9 + 42 * j ≤ w.val ∧ w.val < 9 + 42 * j + 42) := by
  simp only [Touches, wBank, wDbl, wAdd, ModDoubleLayout.Aop, ModDoubleLayout.B] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    | ⟨i, rfl⟩ | rfl <;> (dsimp only; omega)

/-- **The concrete 3-bank (`n = 3`) modular-multiply loop layout on `Fin 135`.** `B → {0,1,2}`,
`Y → {3,4,5}`, `X → {6,7,8}` (bit `i` on wire `6 + i`), bank `j` on the fresh block
`[9 + 42·j, 9 + 42·(j+1))`. The geometry fields reduce to the block-range lemmas
`wBank_clean_range` / `wBank_touch_range` and `omega`. -/
def wMulLoop : MulLoopLayout 135 3 where
  bank j := wBank j
  X i := ⟨6 + min i 2, by omega⟩
  hBshare j j' := by rfl
  hYshare j j' := by rfl
  hctrl j := by
    show (wBank j).add.ctrl = _
    rw [Fin.ext_iff]; dsimp only [wBank, wAdd]; omega
  hInter j k w hj hk hjk hclean htouch := by
    have hc := wBank_clean_range k hk w hclean
    have ht := wBank_touch_range j hj w htouch
    omega
  hXinj i i' hi hi' h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hCtrlTouch j i hj hi hineq htouch := by
    have ht := wBank_touch_range j hj _ htouch
    -- the control bit X i has value 6 + min i 2 = 6 + i (i < 3)
    have hval : (⟨6 + min i 2, by omega⟩ : Fin 135).val = 6 + i := by dsimp only; omega
    rw [hval] at ht
    omega

/-! ### Concrete `#eval` cross-check: the verified `n = 3`, `N = 3` modular multiply on `Fin 135`

`wState` sets the shared `B → {0,1,2}` to `0`, the multiplicand `Y → {3,4,5}` and the multiplier
`X → {6,7,8}` to the given bits, and presets every bank's reduce constants `A1 = 2³ − 3 = 5` and
`A2 = 3` (the 24 preset wires); every scratch / carry / ancilla is `false`. (`N = 3` is forced by the
modular reducer's `2N ≤ 2ⁿ`, i.e. `N ≤ 4` at `n = 3`; the multiplicand satisfies `Y < N = 3`.) Reading
register `B` (low 3 bits) off the strict `Array Bool` evaluator (`runArr`, via the proven bridge
`regValRangeArr_eq`) gives the value `mulLoop_correct` constrains, computed instantly. The three
witnesses below realise `X · Y mod 3` for `Y = 2`: `X = 3 ↦ 6 mod 3 = 0`; `X = 4 ↦ 8 mod 3 = 2`;
`X = 5 ↦ 10 mod 3 = 1`. -/

/-- Concrete input state on `Fin 135`: `B = 0`, `Y = (y0,y1,y2)` (wires `{3,4,5}`), `X = (x0,x1,x2)`
(wires `{6,7,8}`), every bank's presets `A1 = 5` (bits 0,2), `A2 = 3` (bits 0,1), all scratch / carries /
ancilla `false`. -/
def wState (y0 y1 y2 x0 x1 x2 : Bool) : State 135 := fun w =>
  if w.val = 3 then y0 else if w.val = 4 then y1 else if w.val = 5 then y2          -- Y
  else if w.val = 6 then x0 else if w.val = 7 then x1 else if w.val = 8 then x2      -- X
  -- bank 0 (base 9): dbl.A1 {16,18}, dbl.A2 {23,24}, add.A1 {36,38}, add.A2 {43,44}
  else if w.val = 16 ∨ w.val = 18 ∨ w.val = 36 ∨ w.val = 38 then true               -- A1 = 5
  else if w.val = 23 ∨ w.val = 24 ∨ w.val = 43 ∨ w.val = 44 then true               -- A2 = 3
  -- bank 1 (base 51): dbl.A1 {58,60}, dbl.A2 {65,66}, add.A1 {78,80}, add.A2 {85,86}
  else if w.val = 58 ∨ w.val = 60 ∨ w.val = 78 ∨ w.val = 80 then true               -- A1 = 5
  else if w.val = 65 ∨ w.val = 66 ∨ w.val = 85 ∨ w.val = 86 then true               -- A2 = 3
  -- bank 2 (base 93): dbl.A1 {100,102}, dbl.A2 {107,108}, add.A1 {120,122}, add.A2 {127,128}
  else if w.val = 100 ∨ w.val = 102 ∨ w.val = 120 ∨ w.val = 122 then true           -- A1 = 5
  else if w.val = 107 ∨ w.val = 108 ∨ w.val = 127 ∨ w.val = 128 then true           -- A2 = 3
  else false

-- `X = 3 (1,1,0), Y = 2 (0,1,0), N = 3 ↦ 6 mod 3 = 0`. Prints `0`, instantly.
#eval regValRangeArr wMulLoop.B (runArr (mulLoop wMulLoop) (ofState (wState false true false true true false))) 3
-- 0

-- `X = 4 (0,0,1), Y = 2 (0,1,0), N = 3 ↦ 8 mod 3 = 2`. Prints `2`, instantly.
#eval regValRangeArr wMulLoop.B (runArr (mulLoop wMulLoop) (ofState (wState false true false false false true))) 3
-- 2

-- `X = 5 (1,0,1), Y = 2 (0,1,0), N = 3 ↦ 10 mod 3 = 1`. Prints `1`, instantly.
#eval regValRangeArr wMulLoop.B (runArr (mulLoop wMulLoop) (ofState (wState false true false true false true))) 3
-- 1

/-- The cross-check is faithful to the real `denote`-based semantics: by `regValRangeArr_eq`, the fast
`Array` value (`0`, above) *is* the `regValRange (denote …)` quantity `mulLoop_correct` constrains. -/
example : regValRangeArr wMulLoop.B
    (runArr (mulLoop wMulLoop) (ofState (wState false true false true true false))) 3
      = regValRange wMulLoop.B (denote (mulLoop wMulLoop) (wState false true false true true false)) 3 :=
  regValRangeArr_eq wMulLoop.B (mulLoop wMulLoop) (wState false true false true true false) 3

/-- `min i 3` (and `min i 2`) ranges over `{0,1,2,3}`; this turns an `∀ i` clean-wire goal whose wire
depends on `i` only through `min i 3` into the four concrete `decide`-able cases. -/
theorem min3_cases (i : ℕ) : min i 3 = 0 ∨ min i 3 = 1 ∨ min i 3 = 2 ∨ min i 3 = 3 := by omega

-- **The headline `mulLoop_correct` instantiated at the witness.** For `X = 3`, `Y = 2`, `N = 3` the
-- verified general-`n` multiply leaves `B = (3 · 2) mod 3 = 0`. Every hypothesis (the clean / preset
-- wires, `B` init `0`, `Y = 2 < 3`, `2N ≤ 2³`) is discharged by `decide` on the concrete state, so this
-- is a fully proven instance of the general theorem (not merely the `#eval` value check).
set_option maxRecDepth 4000 in
example :
    regValRange wMulLoop.B (denote (mulLoop wMulLoop) (wState false true false true true false)) 3
      = (regValRange wMulLoop.X (wState false true false true true false) 3 * 2) % 3 := by
  have h := mulLoop_correct wMulLoop (wState false true false true true false)
    (N := 3) (Yval := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by intro j i hj hi; interval_cases j <;> interval_cases i <;> decide)
    (by intro j i hj; interval_cases j <;>
        (rcases min3_cases i with h | h | h | h <;>
          (dsimp only [wMulLoop, wBank, wDbl]; simp only [h]; rfl)))
    (by intro j i hj; interval_cases j <;>
        (rcases min3_cases i with h | h | h | h <;>
          (dsimp only [wMulLoop, wBank, wDbl]; simp only [h]; rfl)))
    (by intro j i hj; interval_cases j <;>
        (rcases min3_cases i with h | h | h | h <;>
          (dsimp only [wMulLoop, wBank, wDbl]; simp only [h]; rfl)))
    (by intro j hj; interval_cases j <;>
        (dsimp only [wMulLoop, wBank, wDbl]; decide))
    (by intro j i hj; interval_cases j <;>
        (rcases min3_cases i with h | h | h | h <;>
          (dsimp only [wMulLoop, wBank, wAdd]; simp only [h]; rfl)))
    (by intro j hj; interval_cases j <;>
        (dsimp only [wMulLoop, wBank, wAdd]; decide))
    (by intro j i hj; interval_cases j <;>
        (rcases min3_cases i with h | h | h | h <;>
          (dsimp only [wMulLoop, wBank, wAdd]; simp only [h]; rfl)))
    (by intro j i hj; interval_cases j <;>
        (rcases min3_cases i with h | h | h | h <;>
          (dsimp only [wMulLoop, wBank, wAdd]; simp only [h]; rfl)))
    (by intro j hj; interval_cases j <;>
        (dsimp only [wMulLoop, wBank, wAdd]; decide))
    (by intro j hj; interval_cases j <;> decide)
    (by intro j hj; interval_cases j <;> decide)
    (by intro j hj; interval_cases j <;> decide)
    (by intro j hj; interval_cases j <;> decide)
  exact h

end Reversible

