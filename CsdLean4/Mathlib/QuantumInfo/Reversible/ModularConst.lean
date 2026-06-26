import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
import Mathlib.Tactic.IntervalCases

/-!
# Reversible modular constant-multiply and negation — the last two field-op gadgets  (ECDLP Phase 2, Stage S6.3e-2a)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module verifies the **last two modular field-operation gadgets** the SLP → circuit router needs,
completing the toolkit `{modAdd, modSub, modDouble, mulLoop}`:

* **`modConstMul`** (`c · a mod N`, with `c` a CLASSICAL constant): repeated modular addition. From
  `acc = 0` and a fixed operand register `Aop = a`, run `c` successive `modAdd (Aop = a) → (B = acc)`
  on fresh per-step banks; each maps `acc ← (a + acc) mod N` (`modAdd_correct`), preserving `a`
  (`modAdd_preserves_operand`) and `acc < N` (`modAdd_in_range`). After `c` steps `acc = (c·a) mod N`.
* **`modNeg`** (`(N − b) mod N`, the additive inverse `(−b) mod N`): exactly `modSub` with the minuend
  register holding `0`. `modSub_correct` at `a := 0` gives `(0 + N − b) % N = (N − b) % N`.

```
modConstMul L c = ((List.range c).map (fun j => modAdd (L.bank j))).flatMap id
modNeg L        = modSub L                      -- with the minuend register init 0
```

## Carve line (what this is, and is NOT)

These are the **value-correct field-operation PRIMITIVES** in the fresh-ancilla model, completing the
gadget set. `ℕ` / `mod N` bit arithmetic; NO field / group / curve semantics here.

* `modConstMul` is repeated `modAdd`: an `O(c)`-add schedule. **An optional cost optimisation** is the
  double-and-add variant (`O(log c)` modular doublings + adds), which is the standard speedup; it is
  NOT built here, and is not needed for the SMALL EC coefficients (the `nsmul` coefficients the EC
  point op uses are constants `≤ 8`, which do not even count toward the free parameter `M`).
* `modNeg` is `modSub` with a zero minuend. `(N − b) % N` is `0` when `b = 0` and `N − b` when
  `0 < b < N` — the genuine additive inverse `(−b) mod N`.

**Named residue (same fresh-ancilla model as `modAdd` / `modSub`):** the per-bank carry chains and the
borrow chain / comparison flags are left **dirty**; correctness holds because each bank / use supplies
fresh wires (the `Cadd / C1 / C2 / anc` of each `modConstMul` bank, the `Bor / C / anc` of `modNeg`,
are required `false`). In-place reuse needs carry-clean / ancilla-restoring adders the corpus does NOT
yet provide. The SLP → circuit assembly of the EC point operation (routing ALL opcodes — `add`, `sub`,
`mul` / `sq`, `nsmul`, `neg` — and deriving `M` as an exhibited-circuit count) is **S6.3e-2b / S6.3e-3**,
NOT claimed here. This module supplies the two missing opcode gadgets.

## Honest cost

* `modConstMul_toffoli` derives `c · 12 · n` Toffolis: `c` modular adds, each `12n`
  (`modularAdd_toffoli`), composed through `cost_comp_toffoli_count` over the fold.
* `modNeg_toffoli` is `10n`, inherited verbatim from `modSub_toffoli`.
-/

namespace Reversible

variable {m n : ℕ}

/-! ## Part 1 — `modConstMul` (`c · a mod N`, repeated modular addition)

A `ConstMulLayout` bundles `c` per-step `ModAddLayout` banks (`bank j`, S6.3b), all sharing the operand
register `Aop` (the fixed addend `a`) and the accumulator `B`, with bank `j` supplying its OWN fresh
`Cadd / A1 / C1 / A2 / C2 / anc`. The inter-bank geometry — bank `j` must not touch bank `k`'s clean /
preset wires (`k ≠ j`) — is carried by the membership footprints `CTouches` / `CClean` and the single
disjointness field `hInter`, mirroring `mulLoop`'s `Touches` / `Clean` schema but SIMPLER: no control
bit, no doubling, and the operand `Aop` is FIXED (shared) across every bank. -/

/-- The wire families bank `j`'s `modAdd` circuit touches (writes or reads): the shared operand `Aop`,
the shared accumulator `B`, and bank `j`'s private carry chains / presets / ancilla. -/
def CTouches (L : ℕ → ModAddLayout m n) (j : ℕ) (w : Fin m) : Prop :=
  (∃ i, w = (L j).Aop i) ∨ (∃ i, w = (L j).B i) ∨ (∃ i, w = (L j).Cadd i) ∨
  (∃ i, w = (L j).A1 i) ∨ (∃ i, w = (L j).C1 i) ∨ (∃ i, w = (L j).A2 i) ∨
  (∃ i, w = (L j).C2 i) ∨ w = (L j).anc

/-- The wire families bank `k`'s `modAdd_correct` reads as a clean / preset precondition: the carry
chains `Cadd / C1 / C2` (`false`), the ancilla `anc` (`false`), and the constant presets `A1 / A2`.
(The shared `Aop` and `B` are handled separately by the running invariant.) -/
def CClean (L : ℕ → ModAddLayout m n) (k : ℕ) (w : Fin m) : Prop :=
  (∃ i, w = (L k).Cadd i) ∨ (∃ i, w = (L k).C1 i) ∨ (∃ i, w = (L k).C2 i) ∨
  w = (L k).anc ∨ (∃ i, w = (L k).A1 i) ∨ (∃ i, w = (L k).A2 i)

/-- A `c`-bank constant-multiply layout on `Fin m`. The `c` banks share the operand `Aop` and the
accumulator `B`; bank `j` does not touch bank `k`'s clean wires for `k ≠ j` (`hInter`). All hypotheses
are bounded, so the schema is inhabitable for every `c` (the witness assigns each bank a disjoint
contiguous block; see `constMulLayout2`). -/
structure ConstMulLayout (m n c : ℕ) where
  /-- The `c` per-step modular-addition banks (`bank j` runs the `j`-th `acc ← (a + acc) mod N`). -/
  bank : ℕ → ModAddLayout m n
  /-- Sharing: every bank reads the same operand `Aop` (the fixed addend `a`). -/
  hAopShare : ∀ j j', (bank j).Aop = (bank j').Aop
  /-- Sharing: every bank acts on the same accumulator `B`. -/
  hBShare : ∀ j j', (bank j).B = (bank j').B
  /-- Inter-bank disjointness: for `j ≠ k`, bank `j`'s circuit does not touch bank `k`'s clean wires. -/
  hInter : ∀ j k w, j < c → k < c → j ≠ k → CClean bank k w → ¬ CTouches bank j w

variable {c : ℕ} {L : ConstMulLayout m n c}

/-- The shared operand register (`Aop` of bank `0`). -/
def ConstMulLayout.Aop (L : ConstMulLayout m n c) : ℕ → Fin m := (L.bank 0).Aop

/-- The shared accumulator register (`B` of bank `0`). -/
def ConstMulLayout.B (L : ConstMulLayout m n c) : ℕ → Fin m := (L.bank 0).B

/-- A wire not touched by bank `j` survives bank `j`'s modular add. (The `CTouches` predicate lists
exactly the 8 families `modAdd_preserves_external` requires disjointness from.) -/
theorem notCTouches_preserved (L : ConstMulLayout m n c) (j : ℕ) (s : State m) (w : Fin m)
    (hw : ¬ CTouches L.bank j w) :
    denote (modAdd (L.bank j)) s w = s w := by
  simp only [CTouches, not_or, not_exists] at hw
  obtain ⟨hAop, hB, hCadd, hA1, hC1, hA2, hC2, hanc⟩ := hw
  exact modAdd_preserves_external (L.bank j) s w hAop hB hCadd hA1 hC1 hA2 hC2 hanc

/-- A clean wire of bank `k` survives bank `j`'s modular add (`j ≠ k`, both `< c`): by `hInter` it is
not touched, so `notCTouches_preserved` applies. -/
private theorem cbank_step_preserves_clean (L : ConstMulLayout m n c) (j k : ℕ) (hj : j < c)
    (hk : k < c) (hjk : j ≠ k) (s : State m) (w : Fin m) (hw : CClean L.bank k w) :
    denote (modAdd (L.bank j)) s w = s w :=
  notCTouches_preserved L j s w (L.hInter j k w hj hk hjk hw)

/-! ### The constant-multiply circuit and its prefix -/

/-- **The modular constant-multiply circuit.** Run `c` successive modular adds `acc ← (a + acc) mod N`,
one per bank, on the shared operand `Aop = a` and accumulator `B = acc`; every other wire is fresh. -/
def constMulCirc (L : ConstMulLayout m n c) : Circuit m :=
  ((List.range c).map (fun j => modAdd (L.bank j))).flatMap id

/-- The first `k` banks of the constant-multiply (prefix `[0, …, k-1]`), the induction handle. -/
def constMulUpto (L : ConstMulLayout m n c) (k : ℕ) : Circuit m :=
  ((List.range k).map (fun j => modAdd (L.bank j))).flatMap id

@[simp] theorem constMulUpto_zero (L : ConstMulLayout m n c) : constMulUpto L 0 = [] := rfl

theorem constMul_eq_upto (L : ConstMulLayout m n c) : constMulCirc L = constMulUpto L c := rfl

/-- Split the prefix at its last bank: `constMulUpto L (k+1) = constMulUpto L k ++ modAdd (bank k)`
(bank `k` runs LAST). From `List.range_succ`. -/
theorem constMulUpto_succ (L : ConstMulLayout m n c) (k : ℕ) :
    constMulUpto L (k + 1) = constMulUpto L k ++ modAdd (L.bank k) := by
  simp [constMulUpto, List.range_succ, List.map_append, List.flatMap_append]

/-- **Prefix frame.** A wire not touched by any bank `j < k` survives the whole prefix
`constMulUpto L k` (fold of `notCTouches_preserved`). -/
theorem constMulUpto_preserves (L : ConstMulLayout m n c) (k : ℕ) (s : State m) (w : Fin m)
    (hw : ∀ j, j < k → ¬ CTouches L.bank j w) :
    denote (constMulUpto L k) s w = s w := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [constMulUpto_succ, denote_append,
      notCTouches_preserved L k _ w (hw k (Nat.lt_succ_self k))]
    exact ih s (fun j hj => hw j (Nat.lt_succ_of_lt hj))

/-- A clean / preset wire of bank `k` survives every earlier-bank prefix (`p ≤ k < c`): each lies in
`CClean L.bank k`, so `hInter` keeps it untouched by every bank `j < p ≤ k`. -/
private theorem cclean_pres (L : ConstMulLayout m n c) {k p : ℕ} (hk : k < c) (hpk : p ≤ k)
    (s : State m) (w : Fin m) (hw : CClean L.bank k w) : denote (constMulUpto L p) s w = s w :=
  constMulUpto_preserves L p s w
    (fun j hj => L.hInter j k w (by omega) hk (by omega) hw)

private theorem cclean_pres_reg (L : ConstMulLayout m n c) {k p : ℕ} (hk : k < c) (hpk : p ≤ k)
    (s : State m) (f : ℕ → Fin m) (hf : ∀ i, CClean L.bank k (f i)) (q : ℕ) :
    regValRange f (denote (constMulUpto L p) s) q = regValRange f s q :=
  Finset.sum_congr rfl fun i _ => by
    show (denote (constMulUpto L p) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
    rw [cclean_pres L hk hpk s (f i) (hf i)]

/-! ### The constant-multiply invariant and correctness -/

/-- **The constant-multiply invariant.** After the first `k` banks (`k ≤ c`), from `acc = 0` the
accumulator holds `(k · aval) mod N` and the operand still holds `aval`. By induction on `k`, splitting
the last bank (`constMulUpto_succ`): the prefix preserves bank `k`'s clean / preset wires (`cclean_pres`)
and the running `Aop`/`B`; `modAdd_correct` then maps `acc = (k·aval) mod N` to
`(aval + (k·aval) mod N) mod N = ((k+1)·aval) mod N` (`Nat.add_mod`), and `modAdd_preserves_operand`
keeps `aval`. -/
theorem constMul_invariant (L : ConstMulLayout m n c) (s : State m) {N aval : ℕ}
    (h2N : 2 * N ≤ 2 ^ n) (haN : aval < N)
    -- shared accumulator starts at 0, operand holds aval
    (hB0 : regValRange L.B s n = 0) (hAv : regValRange L.Aop s n = aval)
    -- every bank's clean wires are false at the initial state
    (hCadd : ∀ j i, j < c → s ((L.bank j).Cadd i) = false)
    (hC1 : ∀ j i, j < c → s ((L.bank j).C1 i) = false)
    (hC2 : ∀ j i, j < c → s ((L.bank j).C2 i) = false)
    (hanc : ∀ j, j < c → s (L.bank j).anc = false)
    -- every bank's reduce presets at the initial state
    (hA1 : ∀ j, j < c → regValRange (L.bank j).A1 s n = 2 ^ n - N)
    (hA2 : ∀ j, j < c → regValRange (L.bank j).A2 s n = N) :
    ∀ k, k ≤ c →
      regValRange L.B (denote (constMulUpto L k) s) n = (k * aval) % N
      ∧ regValRange L.Aop (denote (constMulUpto L k) s) n = aval := by
  have hNpos : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le aval) haN
  intro k
  induction k with
  | zero =>
    intro _; rw [constMulUpto_zero]
    refine ⟨?_, ?_⟩
    · simp [hB0]
    · simp [hAv]
  | succ k ih =>
    intro hk1
    have hk : k < c := by omega
    obtain ⟨ihB, ihA⟩ := ih (le_of_lt hk)
    set s1 := denote (constMulUpto L k) s with hs1def
    rw [constMulUpto_succ, denote_append, ← hs1def]
    -- bank k shares Aop and B with bank 0
    have hAopk_eq : (L.bank k).Aop = L.Aop := L.hAopShare k 0
    have hBk_eq : (L.bank k).B = L.B := L.hBShare k 0
    -- accumulator value at s1 = (k * aval) % N, operand = aval, both < N
    have hBk : regValRange (L.bank k).B s1 n = (k * aval) % N := by rw [hBk_eq]; exact ihB
    have hAk : regValRange (L.bank k).Aop s1 n = aval := by rw [hAopk_eq]; exact ihA
    have hbN : (k * aval) % N < N := Nat.mod_lt _ hNpos
    -- bank k's clean wires survive the prefix (each is in CClean L.bank k)
    have hCadd' : ∀ i, s1 ((L.bank k).Cadd i) = false := fun i => by
      rw [hs1def, cclean_pres L hk (le_refl k) s _ (Or.inl ⟨i, rfl⟩)]; exact hCadd k i hk
    have hC1' : ∀ i, s1 ((L.bank k).C1 i) = false := fun i => by
      rw [hs1def, cclean_pres L hk (le_refl k) s _ (Or.inr (Or.inl ⟨i, rfl⟩))]; exact hC1 k i hk
    have hC2' : ∀ i, s1 ((L.bank k).C2 i) = false := fun i => by
      rw [hs1def, cclean_pres L hk (le_refl k) s _ (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))]
      exact hC2 k i hk
    have hanc' : s1 (L.bank k).anc = false := by
      rw [hs1def, cclean_pres L hk (le_refl k) s _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      exact hanc k hk
    have hA1' : regValRange (L.bank k).A1 s1 n = 2 ^ n - N := by
      rw [hs1def, cclean_pres_reg L hk (le_refl k) s _
        (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))]
      exact hA1 k hk
    have hA2' : regValRange (L.bank k).A2 s1 n = N := by
      rw [hs1def, cclean_pres_reg L hk (le_refl k) s _
        (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))))]
      exact hA2 k hk
    -- STEP: modAdd_correct on bank k maps acc to (aval + acc) % N
    have hstep := modAdd_correct (L.bank k) s1 hCadd' hC1' hC2' hanc' h2N hA1' hA2' hAk hBk haN hbN
    -- and preserves the operand
    have hAstep := modAdd_preserves_operand (L.bank k) s1 hCadd' hAk
    refine ⟨?_, ?_⟩
    · -- value: (aval + (k*aval)%N) % N = ((k+1)*aval) % N
      rw [show L.B = (L.bank k).B from hBk_eq.symm, hstep]
      -- (aval + (k*aval) % N) % N = (aval + k*aval) % N = ((k+1)*aval) % N
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have : aval + k * aval = (k + 1) * aval := by rw [Nat.succ_mul, Nat.add_comm]
      rw [this]
    · rw [show L.Aop = (L.bank k).Aop from hAopk_eq.symm]
      exact hAstep

/-- **The verified modular constant-multiply (the S6.3e-2a Part-1 headline).** Under the accumulator
initialised `0`, the operand `Aop` holding `aval < N`, `2N ≤ 2ⁿ`, and every bank's clean / preset
wires set (carries / ancilla `false`, presets `A1 = 2ⁿ − N`, `A2 = N`), the circuit leaves the
accumulator holding `(c · aval) mod N`:
`regValRange B (denote (constMulCirc L) s) n = (c · aval) % N`.

Proof: `constMul_invariant` at `k = c`. Both branches — the `c = 0` base (`acc = 0 = (0·aval)%N`) and
the `c → c+1` step (`(aval + (k·aval)%N)%N = ((k+1)·aval)%N`) — are genuinely covered by the
induction. -/
theorem modConstMul_correct (L : ConstMulLayout m n c) (s : State m) {N aval : ℕ}
    (h2N : 2 * N ≤ 2 ^ n) (haN : aval < N)
    (hB0 : regValRange L.B s n = 0) (hAv : regValRange L.Aop s n = aval)
    (hCadd : ∀ j i, j < c → s ((L.bank j).Cadd i) = false)
    (hC1 : ∀ j i, j < c → s ((L.bank j).C1 i) = false)
    (hC2 : ∀ j i, j < c → s ((L.bank j).C2 i) = false)
    (hanc : ∀ j, j < c → s (L.bank j).anc = false)
    (hA1 : ∀ j, j < c → regValRange (L.bank j).A1 s n = 2 ^ n - N)
    (hA2 : ∀ j, j < c → regValRange (L.bank j).A2 s n = N) :
    regValRange L.B (denote (constMulCirc L) s) n = (c * aval) % N := by
  rw [constMul_eq_upto]
  exact (constMul_invariant L s h2N haN hB0 hAv hCadd hC1 hC2 hanc hA1 hA2 c (le_refl c)).1

/-- **The operand register is intact.** `modConstMul` leaves `Aop` holding `aval` (read-only addend,
which the SLP may reuse). Read off the invariant's second clause at `k = c`. -/
theorem modConstMul_preserves_operand (L : ConstMulLayout m n c) (s : State m) {N aval : ℕ}
    (h2N : 2 * N ≤ 2 ^ n) (haN : aval < N)
    (hB0 : regValRange L.B s n = 0) (hAv : regValRange L.Aop s n = aval)
    (hCadd : ∀ j i, j < c → s ((L.bank j).Cadd i) = false)
    (hC1 : ∀ j i, j < c → s ((L.bank j).C1 i) = false)
    (hC2 : ∀ j i, j < c → s ((L.bank j).C2 i) = false)
    (hanc : ∀ j, j < c → s (L.bank j).anc = false)
    (hA1 : ∀ j, j < c → regValRange (L.bank j).A1 s n = 2 ^ n - N)
    (hA2 : ∀ j, j < c → regValRange (L.bank j).A2 s n = N) :
    regValRange L.Aop (denote (constMulCirc L) s) n = aval := by
  rw [constMul_eq_upto]
  exact (constMul_invariant L s h2N haN hB0 hAv hCadd hC1 hC2 hanc hA1 hA2 c (le_refl c)).2

/-- **The constant-multiply output is a genuine residue in `[0, N)`.** Corollary of
`modConstMul_correct` and `Nat.mod_lt`. -/
theorem modConstMul_in_range (L : ConstMulLayout m n c) (s : State m) {N aval : ℕ}
    (h2N : 2 * N ≤ 2 ^ n) (haN : aval < N)
    (hB0 : regValRange L.B s n = 0) (hAv : regValRange L.Aop s n = aval)
    (hCadd : ∀ j i, j < c → s ((L.bank j).Cadd i) = false)
    (hC1 : ∀ j i, j < c → s ((L.bank j).C1 i) = false)
    (hC2 : ∀ j i, j < c → s ((L.bank j).C2 i) = false)
    (hanc : ∀ j, j < c → s (L.bank j).anc = false)
    (hA1 : ∀ j, j < c → regValRange (L.bank j).A1 s n = 2 ^ n - N)
    (hA2 : ∀ j, j < c → regValRange (L.bank j).A2 s n = N) :
    regValRange L.B (denote (constMulCirc L) s) n < N := by
  rw [modConstMul_correct L s h2N haN hB0 hAv hCadd hC1 hC2 hanc hA1 hA2]
  exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le aval) haN)

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the modular constant-multiply**: `c · 12 · n` Toffolis, from the
exhibited gate list. The circuit is `c` modular adds (`modularAdd_toffoli`, `12n` each), composed
through the fold; the concatenation cost is the sum of the per-bank counts, `c · 12n`.

Honest reading: `O(c)` adds (fresh-ancilla model). The `O(log c)` double-and-add variant is the
standard speedup but is NOT built here (and is not needed for the small EC `nsmul` coefficients). -/
theorem modConstMul_toffoli (L : ConstMulLayout m n c) :
    (circuitCost (constMulCirc L)).toffoli = c * (12 * n) := by
  show (circuitCost (((List.range c).map (fun j => modAdd (L.bank j))).flatMap id)).toffoli
    = c * (12 * n)
  -- induct over the fold, composing modularAdd_toffoli (12n) per bank
  suffices h : ∀ k, (circuitCost (((List.range k).map (fun j => modAdd (L.bank j))).flatMap id)).toffoli
      = k * (12 * n) from h c
  intro k
  induction k with
  | zero => simp [circuitCost]
  | succ k ih =>
    have hsplit : ((List.range (k + 1)).map (fun j => modAdd (L.bank j))).flatMap id
        = ((List.range k).map (fun j => modAdd (L.bank j))).flatMap id ++ modAdd (L.bank k) := by
      rw [List.range_succ, List.map_append, List.flatMap_append]; simp
    rw [hsplit, cost_comp_toffoli_count, ih, modularAdd_toffoli]
    exact (Nat.succ_mul k (12 * n)).symm

/-! ### Non-vacuity witness: a 3-bank (`c = 3`) constant-multiply on `Fin 200`

A genuine `ConstMulLayout 200 4 3`, exhibiting that `ConstMulLayout` is inhabited and
`modConstMul_correct` applies. Shared operand `Aop → {0,1,2,3}`, shared accumulator `B → {4,5,6,7}`;
each bank `j` owns the disjoint fresh block `[8 + 24·j, 8 + 24·(j+1))` of `Fin 200` for its private
`Cadd / A1 / C1 / A2 / C2 / anc`. All disjointness is linear arithmetic on the wire indices (`omega`),
so the schema is manifestly inhabitable; the same stride formula inhabits every `c`.

`n = 4` is needed (not `n = 3`): the modular adder requires `2N ≤ 2ⁿ` so the add does not wrap; for
`N = 5` that forces `2ⁿ ≥ 10`, i.e. `n ≥ 4`. The registers (`Aop, B, A1, A2`) are 4-bit (`min i 3`);
the carry chains (`Cadd, C1, C2`) are 5-element (`min i 4`). -/

/-- Bank `j`'s `ModAddLayout 200 4` on the shared `Aop → {0,1,2,3}`, `B → {4,5,6,7}` and the private
block `[base, base+24)` with `base = 8 + 24·j`: `Cadd → [base,base+5)`, `A1 → [base+5,base+9)`,
`C1 → [base+9,base+14)`, `A2 → [base+14,base+18)`, `C2 → [base+18,base+23)`, `anc → base+23`. -/
def cBank (base : ℕ) (hlo : 8 ≤ base) (hb : base + 24 ≤ 200) : ModAddLayout 200 4 where
  Aop i := ⟨min i 3, by omega⟩
  B i := ⟨4 + min i 3, by omega⟩
  Cadd i := ⟨base + min i 4, by omega⟩
  A1 i := ⟨base + 5 + min i 3, by omega⟩
  C1 i := ⟨base + 9 + min i 4, by omega⟩
  A2 i := ⟨base + 14 + min i 3, by omega⟩
  C2 i := ⟨base + 18 + min i 4, by omega⟩
  anc := ⟨base + 23, by omega⟩
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
  hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega

/-- Every `CClean (cBank' ·) k w` wire (`k < 3`) lies in bank `k`'s private block
`[8 + 24·k, 8 + 24·k + 24)`. (All 6 clean / preset families are private; none is `Aop` or `B`.) -/
theorem cBank_clean_range (k : ℕ) (hk : k < 3) (w : Fin 200)
    (hw : CClean (fun j => cBank (8 + 24 * min j 2) (by omega) (by omega)) k w) :
    8 + 24 * k ≤ w.val ∧ w.val < 8 + 24 * k + 24 := by
  simp only [CClean, cBank] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    (dsimp only; omega)

/-- Every `CTouches (cBank' ·) j w` wire (`j < 3`) lies in `{0,…,7} ∪ [8 + 24·j, 8 + 24·j + 24)` —
the shared `Aop`/`B` and bank `j`'s private block. -/
theorem cBank_touch_range (j : ℕ) (hj : j < 3) (w : Fin 200)
    (hw : CTouches (fun j => cBank (8 + 24 * min j 2) (by omega) (by omega)) j w) :
    w.val < 8 ∨ (8 + 24 * j ≤ w.val ∧ w.val < 8 + 24 * j + 24) := by
  simp only [CTouches, cBank] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
    (dsimp only; omega)

/-- **The concrete 3-bank (`c = 3`) constant-multiply layout on `Fin 200`.** `Aop → {0,1,2,3}`,
`B → {4,5,6,7}`, bank `j` on the fresh block `[8 + 24·j, 8 + 24·(j+1))`. The geometry fields reduce to
the block-range lemmas `cBank_clean_range` / `cBank_touch_range` and `omega`. -/
def constMulLayout2 : ConstMulLayout 200 4 3 where
  bank j := cBank (8 + 24 * min j 2) (by omega) (by omega)
  hAopShare j j' := by rfl
  hBShare j j' := by rfl
  hInter j k w hj hk hjk hclean htouch := by
    have hc := cBank_clean_range k hk w hclean
    have ht := cBank_touch_range j hj w htouch
    omega

/-! ### Harness `#eval` cross-checks and proven instances (`c = 3, 8, 0, 1`)

`constMulState` sets the shared `Aop → {0,1,2,3}` to `aval`, the accumulator `B → {4,5,6,7}` to `0`, and
presets every bank's reduce constants `A1 = 2ⁿ − N = 11` (bits `0,1,3`) and `A2 = N = 5` (bits `0,2`);
every scratch / carry / ancilla is `false`. Reading register `B` (low 4 bits) off the strict
`Array Bool` evaluator (`runArr`, via the proven bridge `regValRangeArr_eq`) gives the value
`modConstMul_correct` constrains, computed instantly. `N = 5` (`2N = 10 ≤ 2⁴`) throughout. -/

/-- Concrete input state on `Fin 200` for `c, n = 4, N = 5`: `Aop = (a0,a1,a2)` on wires `{0,1,2}`
(top bit `Aop 3 = 0`), `B = 0` (wires `{4,5,6,7}`), every bank's presets `A1 = 11` (block bits `0,1,3`)
and `A2 = 5` (block bits `0,2`), all scratch / carries / ancilla `false`. Bank `j`'s `A1` is at wires
`{base+5, base+6, base+8}`, `A2` at `{base+14, base+16}` with `base = 8 + 24·j`. -/
def constMulState (a0 a1 a2 : Bool) : State 200 := fun w =>
  if w.val = 0 then a0 else if w.val = 1 then a1 else if w.val = 2 then a2          -- Aop = a (< 8)
  -- B = 0 (wires 4,5,6,7): all false (default)
  -- bank 0 (base 8):   A1 {13,14,16}, A2 {22,24}
  else if w.val = 13 ∨ w.val = 14 ∨ w.val = 16 ∨ w.val = 22 ∨ w.val = 24 then true
  -- bank 1 (base 32):  A1 {37,38,40}, A2 {46,48}
  else if w.val = 37 ∨ w.val = 38 ∨ w.val = 40 ∨ w.val = 46 ∨ w.val = 48 then true
  -- bank 2 (base 56):  A1 {61,62,64}, A2 {70,72}
  else if w.val = 61 ∨ w.val = 62 ∨ w.val = 64 ∨ w.val = 70 ∨ w.val = 72 then true
  else false

-- `c = 3, a = 4, N = 5 ↦ 12 mod 5 = 2`. Prints `2`, instantly.
#eval regValRangeArr constMulLayout2.B
  (runArr (constMulCirc constMulLayout2) (ofState (constMulState false false true))) 4
-- 2

-- `c = 3, a = 1, N = 5 ↦ 3 mod 5 = 3`. Prints `3`.
#eval regValRangeArr constMulLayout2.B
  (runArr (constMulCirc constMulLayout2) (ofState (constMulState true false false))) 4
-- 3

-- The operand is preserved across the whole circuit: `Aop` stays `4` (a = 4).
#eval regValRangeArr constMulLayout2.Aop
  (runArr (constMulCirc constMulLayout2) (ofState (constMulState false false true))) 4
-- 4

/-- The cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`, the fast
`Array` value (`2`, above) *is* the `regValRange (denote …)` quantity that `modConstMul_correct`
constrains. -/
example : regValRangeArr constMulLayout2.B
    (runArr (constMulCirc constMulLayout2) (ofState (constMulState false false true))) 4
      = regValRange constMulLayout2.B (denote (constMulCirc constMulLayout2)
        (constMulState false false true)) 4 :=
  regValRangeArr_eq constMulLayout2.B (constMulCirc constMulLayout2) (constMulState false false true) 4

/-- `min i 4` ranges over `{0,1,2,3,4}`; turns an `∀ i` carry-wire goal whose wire depends on `i` only
through `min i 4` into five concrete `decide`-able cases. -/
theorem cmin4_cases (i : ℕ) : min i 4 = 0 ∨ min i 4 = 1 ∨ min i 4 = 2 ∨ min i 4 = 3 ∨ min i 4 = 4 := by
  omega

/-- The clean / preset preconditions of `modConstMul_correct` hold at `constMulState`, for any operand
bits (`n = 4, N = 5`). The carry / ancilla families are `false`; the presets `A1 = 11`, `A2 = 5`.
Discharged by `interval_cases` over the 3 banks + `cmin4_cases` over the wire index. -/
private theorem constMulState_pre (a0 a1 a2 : Bool) :
    (∀ j i, j < 3 → constMulState a0 a1 a2 ((constMulLayout2.bank j).Cadd i) = false)
      ∧ (∀ j i, j < 3 → constMulState a0 a1 a2 ((constMulLayout2.bank j).C1 i) = false)
      ∧ (∀ j i, j < 3 → constMulState a0 a1 a2 ((constMulLayout2.bank j).C2 i) = false)
      ∧ (∀ j, j < 3 → constMulState a0 a1 a2 (constMulLayout2.bank j).anc = false)
      ∧ (∀ j, j < 3 → regValRange (constMulLayout2.bank j).A1 (constMulState a0 a1 a2) 4 = 2 ^ 4 - 5)
      ∧ (∀ j, j < 3 → regValRange (constMulLayout2.bank j).A2 (constMulState a0 a1 a2) 4 = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i hj; interval_cases j <;>
      (rcases cmin4_cases i with h | h | h | h | h <;>
        (dsimp only [constMulLayout2, cBank]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases cmin4_cases i with h | h | h | h | h <;>
        (dsimp only [constMulLayout2, cBank]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases cmin4_cases i with h | h | h | h | h <;>
        (dsimp only [constMulLayout2, cBank]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;>
      (dsimp only [constMulLayout2, cBank]; simp only [constMulState]; rfl)
  · intro j hj; interval_cases j <;>
      (simp only [constMulLayout2, cBank, regValRange, Finset.sum_range_succ, constMulState]; rfl)
  · intro j hj; interval_cases j <;>
      (simp only [constMulLayout2, cBank, regValRange, Finset.sum_range_succ, constMulState]; rfl)

-- **Proven instance, `c = 3`:** `c = 3, a = 4, N = 5 ↦ (3 · 4) mod 5 = 12 mod 5 = 2`. Every
-- hypothesis of the general `modConstMul_correct` is discharged on the concrete state, so this is a
-- fully proven instance (not merely the `#eval` value check).
set_option maxRecDepth 4000 in
example :
    regValRange constMulLayout2.B (denote (constMulCirc constMulLayout2) (constMulState false false true)) 4
      = (3 * 4) % 5 := by
  obtain ⟨hCadd, hC1, hC2, hanc, hA1, hA2⟩ := constMulState_pre false false true
  have hAv : regValRange constMulLayout2.Aop (constMulState false false true) 4 = 4 := by
    simp [regValRange, Finset.sum_range_succ, constMulLayout2, cBank, ConstMulLayout.Aop, constMulState]
  have hB0 : regValRange constMulLayout2.B (constMulState false false true) 4 = 0 := by
    simp [regValRange, Finset.sum_range_succ, constMulLayout2, cBank, ConstMulLayout.B, constMulState]
  exact modConstMul_correct constMulLayout2 (constMulState false false true)
    (N := 5) (aval := 4) (by decide) (by decide) hB0 hAv hCadd hC1 hC2 hanc hA1 hA2

/-- **Proven instance, `c = 1`:** `c = 1, a = 3, N = 5 ↦ (1 · 3) mod 5 = 3` (a single add). Uses a
`ConstMulLayout 200 4 1` — the same banks, `c = 1`. -/
def constMulLayout1 : ConstMulLayout 200 4 1 where
  bank j := cBank (8 + 24 * min j 2) (by omega) (by omega)
  hAopShare j j' := by rfl
  hBShare j j' := by rfl
  hInter j k w hj hk hjk hclean htouch := by
    have hc := cBank_clean_range k (by omega) w hclean
    have ht := cBank_touch_range j (by omega) w htouch
    omega

private theorem constMulState1_pre (a0 a1 a2 : Bool) :
    (∀ j i, j < 1 → constMulState a0 a1 a2 ((constMulLayout1.bank j).Cadd i) = false)
      ∧ (∀ j i, j < 1 → constMulState a0 a1 a2 ((constMulLayout1.bank j).C1 i) = false)
      ∧ (∀ j i, j < 1 → constMulState a0 a1 a2 ((constMulLayout1.bank j).C2 i) = false)
      ∧ (∀ j, j < 1 → constMulState a0 a1 a2 (constMulLayout1.bank j).anc = false)
      ∧ (∀ j, j < 1 → regValRange (constMulLayout1.bank j).A1 (constMulState a0 a1 a2) 4 = 2 ^ 4 - 5)
      ∧ (∀ j, j < 1 → regValRange (constMulLayout1.bank j).A2 (constMulState a0 a1 a2) 4 = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i hj; obtain rfl : j = 0 := by omega
    rcases cmin4_cases i with h | h | h | h | h <;>
      (dsimp only [constMulLayout1, cBank]; simp only [h]; rfl)
  · intro j i hj; obtain rfl : j = 0 := by omega
    rcases cmin4_cases i with h | h | h | h | h <;>
      (dsimp only [constMulLayout1, cBank]; simp only [h]; rfl)
  · intro j i hj; obtain rfl : j = 0 := by omega
    rcases cmin4_cases i with h | h | h | h | h <;>
      (dsimp only [constMulLayout1, cBank]; simp only [h]; rfl)
  · intro j hj; obtain rfl : j = 0 := by omega
    dsimp only [constMulLayout1, cBank]; simp only [constMulState]; rfl
  · intro j hj; obtain rfl : j = 0 := by omega
    simp only [constMulLayout1, cBank, regValRange, Finset.sum_range_succ, constMulState]; rfl
  · intro j hj; obtain rfl : j = 0 := by omega
    simp only [constMulLayout1, cBank, regValRange, Finset.sum_range_succ, constMulState]; rfl

set_option maxRecDepth 4000 in
example :
    regValRange constMulLayout1.B (denote (constMulCirc constMulLayout1) (constMulState true true false)) 4
      = (1 * 3) % 5 := by
  obtain ⟨hCadd, hC1, hC2, hanc, hA1, hA2⟩ := constMulState1_pre true true false
  have hAv : regValRange constMulLayout1.Aop (constMulState true true false) 4 = 3 := by
    simp [regValRange, Finset.sum_range_succ, constMulLayout1, cBank, ConstMulLayout.Aop, constMulState]
  have hB0 : regValRange constMulLayout1.B (constMulState true true false) 4 = 0 := by
    simp [regValRange, Finset.sum_range_succ, constMulLayout1, cBank, ConstMulLayout.B, constMulState]
  exact modConstMul_correct constMulLayout1 (constMulState true true false)
    (N := 5) (aval := 3) (by decide) (by decide) hB0 hAv hCadd hC1 hC2 hanc hA1 hA2

/-- **Proven instance, the `c = 0` base case:** `c = 0 ↦ 0` (empty circuit, accumulator unchanged at
`0`). Uses a `ConstMulLayout 200 4 0`; the headline lands on `(0 · aval) % N = 0` with NO add. -/
def constMulLayout0 : ConstMulLayout 200 4 0 where
  bank j := cBank (8 + 24 * min j 2) (by omega) (by omega)
  hAopShare j j' := by rfl
  hBShare j j' := by rfl
  hInter j k w hj hk hjk hclean htouch := by omega

example :
    regValRange constMulLayout0.B (denote (constMulCirc constMulLayout0) (constMulState false true false)) 4
      = (0 * 2) % 5 := by
  have hAv : regValRange constMulLayout0.Aop (constMulState false true false) 4 = 2 := by
    simp [regValRange, Finset.sum_range_succ, constMulLayout0, cBank, ConstMulLayout.Aop, constMulState]
  have hB0 : regValRange constMulLayout0.B (constMulState false true false) 4 = 0 := by
    simp [regValRange, Finset.sum_range_succ, constMulLayout0, cBank, ConstMulLayout.B, constMulState]
  exact modConstMul_correct constMulLayout0 (constMulState false true false)
    (N := 5) (aval := 2) (by decide) (by decide) hB0 hAv
    (by intro j i hj; omega) (by intro j i hj; omega) (by intro j i hj; omega)
    (by intro j hj; omega) (by intro j hj; omega) (by intro j hj; omega)

/-- **The `c = 8` wrap witness** (harness cross-check): `c = 8, a = 2, N = 5 ↦ 16 mod 5 = 1`. Needs a
`ConstMulLayout 200 4 8`; the strided block formula inhabits `c = 8` (`8 + 24·7 + 24 = 200`). The
`#eval` prints `1`, the genuinely-wrapped residue (`16 = 3·5 + 1`), confirming the running `acc < N`
maintenance across all 8 adds. -/
def constMulLayout8 : ConstMulLayout 200 4 8 where
  bank j := cBank (8 + 24 * min j 7) (by omega) (by omega)
  hAopShare j j' := by rfl
  hBShare j j' := by rfl
  hInter j k w hj hk hjk hclean htouch := by
    -- bank k's clean wires lie in [8+24·min k 7, …+24); bank j touches {0..7} ∪ its own block
    simp only [CClean, CTouches, cBank] at hclean htouch
    rcases hclean with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    · rcases htouch with ⟨i', h⟩ | ⟨i', h⟩ | ⟨i', h⟩ | ⟨i', h⟩ | ⟨i', h⟩ | ⟨i', h⟩ | ⟨i', h⟩ | h <;>
        (rw [Fin.ext_iff] at h; dsimp only at h; omega)

/-- `constMulState8` presets all 8 banks' `A1 = 11` and `A2 = 5` (blocks `base = 8 + 24·j`, `j < 8`),
`Aop = a`, `B = 0`. Bank `j`'s `A1` is `{base+5, base+6, base+8}`, `A2` is `{base+14, base+16}`. -/
def constMulState8 (a0 a1 a2 : Bool) : State 200 := fun w =>
  if w.val = 0 then a0 else if w.val = 1 then a1 else if w.val = 2 then a2          -- Aop = a (< 8)
  -- preset A1 = 11 ({base+5, base+6, base+8}) and A2 = 5 ({base+14, base+16}) for base = 8+24·j, j<8
  -- the in-block offset (w.val − 8) % 24 ∈ {5,6,8,14,16} flags A1's bits 0,1,3 and A2's bits 0,2,
  -- for every block (w.val ≥ 8); blocks beyond the 7th are never read (c = 8 banks fit in Fin 200).
  else if 8 ≤ w.val ∧ ((w.val - 8) % 24 = 5 ∨ (w.val - 8) % 24 = 6 ∨ (w.val - 8) % 24 = 8
              ∨ (w.val - 8) % 24 = 14 ∨ (w.val - 8) % 24 = 16) then true
  else false

-- `c = 8, a = 2, N = 5 ↦ 16 mod 5 = 1`. Prints `1` (the wrapped residue), instantly.
#eval regValRangeArr constMulLayout8.B
  (runArr (constMulCirc constMulLayout8) (ofState (constMulState8 false true false))) 4
-- 1

-- `c = 0` base: the empty circuit leaves `B = 0`. Prints `0`.
#eval regValRangeArr constMulLayout0.B
  (runArr (constMulCirc constMulLayout0) (ofState (constMulState true true true))) 4
-- 0

-- `c = 1, a = 3, N = 5 ↦ 3`. Prints `3`.
#eval regValRangeArr constMulLayout1.B
  (runArr (constMulCirc constMulLayout1) (ofState (constMulState true true false))) 4
-- 3

/-! ## Part 2 — `modNeg` (`(N − b) mod N`, the additive inverse)

`modNeg(b) = (N − b) mod N = (0 − b) mod N`, which is exactly `modSub` with the minuend register `B`
holding `0`. So `modNeg` IS `modSub`; the corollary `modNeg_correct` instantiates `modSub_correct` at
`a := 0`. `(N − b) % N` is `0` when `b = 0` and `N − b` when `0 < b < N` — the genuine additive inverse
`(−b) mod N`. -/

/-- **The modular-negation circuit.** Definitionally `modSub` (run with the minuend register `B`
initialised to `0`, so the output is `(N − b) mod N`). -/
def modNeg (L : ModSubLayout m n) : Circuit m := modSub L

/-- **The verified modular negation (the S6.3e-2a Part-2 headline).** For a disjoint-wire
`ModSubLayout` with the borrow chain `Bor`, the fix carry chain `C`, and the ancilla `anc` initialised
`false`, the constant register `Nreg` preset to `N`, the **minuend `B` holding `0`**, the subtrahend
`Sub` holding `b`, with `b < N`, `N ≤ 2ⁿ`: the circuit `modNeg L` leaves `B` holding `(N − b) mod N`.

A thin corollary of `modSub_correct` at `a := 0`: `(0 + N − b) % N = (N − b) % N`. Both branches are
covered — `b = 0` gives `(N − 0) % N = 0` (the borrow-clear branch, `a ≥ b`), and `0 < b < N` gives
`(N − b) % N = N − b` (the borrow-set WRAP branch). -/
theorem modNeg_correct (L : ModSubLayout m n) (s : State m)
    (hBor : ∀ j, s (L.Bor j) = false) (hC : ∀ j, s (L.C j) = false) (hanc : s L.anc = false)
    {N b : ℕ} (hN : N ≤ 2 ^ n) (hNpos : 0 < N) (hNreg : regValRange L.Nreg s n = N)
    (hB0 : regValRange L.B s n = 0) (hSub : regValRange L.Sub s n = b)
    (hbN : b < N) :
    regValRange L.B (denote (modNeg L) s) n = (N - b) % N := by
  rw [modNeg, modSub_correct L s hBor hC hanc hN hNreg hB0 hSub hNpos hbN]
  congr 1
  omega

/-- **The modular-negation output is a genuine residue in `[0, N)`.** Corollary of `modNeg_correct`
and `Nat.mod_lt`. -/
theorem modNeg_in_range (L : ModSubLayout m n) (s : State m)
    (hBor : ∀ j, s (L.Bor j) = false) (hC : ∀ j, s (L.C j) = false) (hanc : s L.anc = false)
    {N b : ℕ} (hN : N ≤ 2 ^ n) (hNpos : 0 < N) (hNreg : regValRange L.Nreg s n = N)
    (hB0 : regValRange L.B s n = 0) (hSub : regValRange L.Sub s n = b)
    (hbN : b < N) :
    regValRange L.B (denote (modNeg L) s) n < N := by
  rw [modNeg_correct L s hBor hC hanc hN hNpos hNreg hB0 hSub hbN]
  exact Nat.mod_lt _ hNpos

/-- **Derived Toffoli cost of the modular negation**: `10n` Toffolis, inherited verbatim from
`modSub_toffoli` (`modNeg` IS `modSub`). -/
theorem modNeg_toffoli (L : ModSubLayout m n) :
    (circuitCost (modNeg L)).toffoli = 10 * n := by
  rw [modNeg]; exact modSub_toffoli L

/-! ### `modNeg` non-vacuity + harness cross-checks (`b = 2, 0, 4`)

Reuse the `modSubLayout2` / `modSubState2` witness (`Fin 25`, `n = 3`, `N = 5`) from `ModularSub`, with
the minuend `B` set to `0`. The three runs cover `b = 2 ↦ 3`, `b = 0 ↦ 0` (the `B = b` zero / borrow-
clear branch), and `b = 4 ↦ 1` (the borrow-set WRAP branch). -/

/-- **Proven instance:** `b = 2, N = 5 ↦ (5 − 2) mod 5 = 3` (minuend `B = 0`, subtrahend `Sub = 2`).
The `ModularSub` borrow / fix-carry / ancilla / `Nreg = 5` preconditions are inlined `simp` facts on
`modSubState2` (independent of the data bits). -/
example : regValRange modSubLayout2.B
    (denote (modNeg modSubLayout2) (modSubState2 false false false false true false)) 3 = 3 := by
  have hBor : ∀ j, modSubState2 false false false false true false (modSubLayout2.Bor j) = false := by
    intro j; show modSubState2 false false false false true false (modSubLayout2.Bor j) = false
    simp only [modSubLayout2]; split_ifs <;> rfl
  have hC : ∀ j, modSubState2 false false false false true false (modSubLayout2.C j) = false := by
    intro j; show modSubState2 false false false false true false (modSubLayout2.C j) = false
    simp only [modSubLayout2]; split_ifs <;> rfl
  have hanc : modSubState2 false false false false true false modSubLayout2.anc = false := rfl
  have hNreg : regValRange modSubLayout2.Nreg
      (modSubState2 false false false false true false) 3 = 5 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hB0 : regValRange modSubLayout2.B
      (modSubState2 false false false false true false) 3 = 0 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hSub : regValRange modSubLayout2.Sub
      (modSubState2 false false false false true false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hN : (5 : ℕ) ≤ 2 ^ 3 := by decide
  rw [modNeg_correct modSubLayout2 (modSubState2 false false false false true false) hBor hC hanc
    hN (by decide) hNreg hB0 hSub (by decide)]

-- `b = 2, N = 5 ↦ (5 − 2) mod 5 = 3`. Prints `3`, instantly.
#eval regValRangeArr modSubLayout2.B
  (runArr (modNeg modSubLayout2) (ofState (modSubState2 false false false false true false))) 3
-- 3

-- `b = 0, N = 5 ↦ (5 − 0) mod 5 = 0` (the zero branch). Prints `0`.
#eval regValRangeArr modSubLayout2.B
  (runArr (modNeg modSubLayout2) (ofState (modSubState2 false false false false false false))) 3
-- 0

-- `b = 4, N = 5 ↦ (5 − 4) mod 5 = 1` (the borrow-set WRAP branch). Prints `1`.
#eval regValRangeArr modSubLayout2.B
  (runArr (modNeg modSubLayout2) (ofState (modSubState2 false false false false false true))) 3
-- 1

/-- The `modNeg` cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`,
the fast `Array` value (`3`, the `b = 2` run above) *is* the `regValRange (denote …)` quantity that
`modNeg_correct` constrains. -/
example : regValRangeArr modSubLayout2.B
    (runArr (modNeg modSubLayout2) (ofState (modSubState2 false false false false true false))) 3
      = regValRange modSubLayout2.B (denote (modNeg modSubLayout2)
        (modSubState2 false false false false true false)) 3 :=
  regValRangeArr_eq modSubLayout2.B (modNeg modSubLayout2)
    (modSubState2 false false false false true false) 3

end Reversible
