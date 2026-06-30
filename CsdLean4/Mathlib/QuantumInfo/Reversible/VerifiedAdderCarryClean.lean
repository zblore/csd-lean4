import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdder
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModMul

/-!
# A carry-clean adder-parametric modular multiplier  (ECDLP Phase 2, Stage S6.3-36b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module is the carry-clean (`Θ(n)`-qubit) counterpart of the fresh-ancilla keystone 36a
(`VerifiedAdder`). It bundles the carry-clean multiplier fold's consumption surface into a structure
`VerifiedAdderCarryClean`, proves the multiply correct + cost it **once, parametric** over any
conforming restored-clean step, and exhibits the existing carry-clean Cuccaro multiply
(`cuccaroModMul`, Stage 2b) as the faithfulness instance — recovering its proven `(X · Y) mod N`
correctness and `20·n² + 14·n` Toffoli figure exactly.

## The restored-clean discipline (the crux vs 36a)

36a's `VerifiedAdder` models the FRESH-ANCILLA memory model: each bank has a PRIVATE clean predicate
`clean k s` with a precondition-free inter-bank frame `cleanStable` (bank `j` never touches bank `k`'s
ancilla). That is exactly wrong for the carry-clean multiply, which reuses ONE scratch bank across all
`n` Horner steps. Modelling that single bank as `n` independently-fresh banks would make the
`Θ(n)`-qubit win vacuous.

So this variant carries a GLOBAL cleanliness predicate `clean : State m → Prop` (one bank, no per-bank
index) under a **restored-clean** discipline: each step has `clean` as a PRECONDITION of both its value
correctness and its cleanliness, and RE-ESTABLISHES `clean` as a POSTCONDITION (`cleanRestored`). The
fold maintains "the bank is clean" as a loop invariant (clean in → step → clean out), threaded step to
step — not "all banks independently clean throughout". This is the genuine single-bank-reuse invariant;
cf. `cuccaroModMul_clean` (the all-scratch-restored property that enables the reuse).

## What is proved

* `VerifiedAdderCarryClean` — the structure with the restored-clean fields (`correct` / `cleanRestored`
  / `presY` all gated on `clean s`, `digitStable`, `digit`, `toffoli`, `hNpos`, `hToffoli`).
* `genMulCC` / `genMulCC_correct` — the multiplier fold + its correctness
  `acc = (accVal digit · y) mod N`, the same induction as `cuccaroModMul_invariant`, now citing the
  abstract fields with the restored-clean loop invariant. REUSES `accVal` / `accVal_mod_step` /
  `accVal_succ` from 36a UNCHANGED.
* `genMulCC_clean` — the shared bank restored after the full multiply (the `Θ(n)` reuse is real).
* `genMulCC_toffoli` — the cost recurrence `n · step.toffoli`.
* `cuccaroAdder` — the faithfulness instance from a `CuccaroMulLayout` and the existing carry-clean
  Cuccaro step (the REAL `cuccaroModMulStep`, independently derived; NOT 36a's fresh-ancilla
  `hornerStep`); `genMulCC cuccaroAdder = cuccaroModMul` (definitionally),
  `genMulCC_cuccaroAdder_correct` reproduces `cuccaroModMul_correct`'s `(X · Y) mod N`, and
  `genMulCC_cuccaroAdder_toffoli = 20·n² + 14·n` recovers `cuccaroModMul_toffoli`. The abstraction is
  non-lossy.

## Honest scope

36b validates the keystone generalises across memory models (fresh-ancilla 36a + carry-clean here), and
gives the first generic-multiplier instance that moves the cost (`20n² + 14n` < the fresh-ancilla
`30n²` for `n ≥ 2`; equal-order, the genuine prize is the `Θ(n)`-vs-`Θ(n²)` qubit collapse below),
FULLY Boolean-verified (the whole stack is `CCX`-circuit `denote`, no amplitude wall, unlike a
measurement adder). This is the MULTIPLY cost; the score-dominant term is the INVERTER (36c, safegcd
parametric, the ~67%). **No ECDSA score change is claimed yet** (still needs 36c + harness #7). The
`Θ(n)`-qubit win is real: the restored-clean invariant (this module's `cleanRestored`, realised by
`cuccaroModMul_clean`) is exactly what lets the single scratch bank be reused across all `n` steps.
**Load-bearing hypothesis: `N` odd** (inherited from the doubler's parity flag-uncompute), which holds
for the ECDLP prime field.
-/

namespace Reversible

variable {m n N : ℕ}

/-! ### The carry-clean variant interface -/

/-- **A verified carry-clean per-bit modular-multiply step**, the substitutable atom of the
single-scratch-bank multiplier fold. Bundles exactly the carry-clean fold's consumption surface: a
per-step circuit `step k` over a shared accumulator `B` and multiplicand `Y`, the digit `digit k s`
step `k` folds, a GLOBAL cleanliness predicate `clean s` (one reused scratch bank, no per-bank index),
and the restored-clean facts the fold consumes. Unlike 36a's fresh-ancilla signature, `clean` is a
PRECONDITION of `correct` / `cleanRestored` / `presY` and is RE-ESTABLISHED by `cleanRestored`; the fold
threads "bank clean" as a loop invariant. `N` is the modulus; `hNpos` keeps the running residue
genuine. -/
structure VerifiedAdderCarryClean (m n N : ℕ) where
  /-- Step `k`'s circuit on the shared bank. -/
  step : ℕ → Circuit m
  /-- The shared accumulator register. -/
  B : ℕ → Fin m
  /-- The shared multiplicand register. -/
  Y : ℕ → Fin m
  /-- The digit (`0` / `1`) step `k` folds, read off the state. -/
  digit : ℕ → State m → ℕ
  /-- The GLOBAL single-bank cleanliness precondition (no per-bank index). -/
  clean : State m → Prop
  /-- The per-step Toffoli cost. -/
  toffoli : ℕ
  /-- The modulus is positive. -/
  hNpos : 0 < N
  /-- The step's gate-list Toffoli count is `toffoli`. -/
  hToffoli : ∀ k, (circuitCost (step k)).toffoli = toffoli
  /-- **Value correctness (clean PRECONDITION).** From a clean bank with `B = c < N` and
  `Y = Yval < N`, step `k` advances the residue: `B ← (2·c + digit·Yval) mod N`. -/
  correct : ∀ (k : ℕ) (s : State m) (c Yval : ℕ), k < n → clean s → Yval < N →
    regValRange B s n = c → c < N → regValRange Y s n = Yval →
    regValRange B (denote (step k) s) n = (2 * c + digit k s * Yval) % N
  /-- **Cleanliness restoration (the load-bearing POSTCONDITION).** From a clean bank with the same
  value preconditions, step `k` re-establishes `clean` on the output state. This is what makes the
  single-bank reuse sound: each step consumes a clean bank and gives one back. -/
  cleanRestored : ∀ (k : ℕ) (s : State m) (c Yval : ℕ), k < n → clean s → Yval < N →
    regValRange B s n = c → c < N → regValRange Y s n = Yval →
    clean (denote (step k) s)
  /-- **Multiplicand persistence.** Step `k` leaves `Y` at its value. -/
  presY : ∀ (k : ℕ) (s : State m) (c Yval : ℕ), k < n → clean s → Yval < N →
    regValRange B s n = c → c < N → regValRange Y s n = Yval →
    regValRange Y (denote (step k) s) n = Yval
  /-- **Digit frame.** Step `j` leaves step `k`'s digit intact (the digit lives on the read-only
  multiplier register, preserved by every step). -/
  digitStable : ∀ (j k : ℕ) (s : State m), digit k (denote (step j) s) = digit k s

/-! ### The generic carry-clean multiplier -/

/-- **The adder-parametric carry-clean modular multiplier.** Fold the restored-clean step over the `n`
banks on the single shared scratch bank. -/
def genMulCC (A : VerifiedAdderCarryClean m n N) : Circuit m :=
  ((List.range n).map (fun j => A.step j)).flatMap id

/-- The first `k` steps of the loop (the induction handle). -/
def genMulCCUpto (A : VerifiedAdderCarryClean m n N) (k : ℕ) : Circuit m :=
  ((List.range k).map (fun j => A.step j)).flatMap id

theorem genMulCC_eq_upto (A : VerifiedAdderCarryClean m n N) : genMulCC A = genMulCCUpto A n := rfl

theorem genMulCCUpto_succ (A : VerifiedAdderCarryClean m n N) (k : ℕ) :
    genMulCCUpto A (k + 1) = genMulCCUpto A k ++ A.step k := by
  simp [genMulCCUpto, List.range_succ, List.map_append, List.flatMap_append]

/-- Step `k`'s digit survives the prefix of steps `[0, p)` (every step preserves all digits, by
`digitStable`). -/
theorem genMulCC_digit_pres (A : VerifiedAdderCarryClean m n N) (s : State m) (k : ℕ) :
    ∀ p, A.digit k (denote (genMulCCUpto A p) s) = A.digit k s := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [genMulCCUpto_succ, denote_append, A.digitStable p k (denote (genMulCCUpto A p) s), ih]

/-- **The generic carry-clean multiply-loop invariant.** After the first `k` steps (`k ≤ n`) from a
clean bank with `B = 0`, the accumulator holds `(accVal digit k · y) mod N`, the bank is STILL clean
(the restored-clean loop invariant: clean in → `correct` + `cleanRestored` → clean out), and `Y` still
holds `y`. The same induction as `cuccaroModMul_invariant`, now citing the abstract fields. -/
theorem genMulCC_invariant (A : VerifiedAdderCarryClean m n N) (s : State m) {y : ℕ}
    (hy : y < N) (hclean : A.clean s)
    (hB0 : regValRange A.B s n = 0) (hY : regValRange A.Y s n = y) :
    ∀ k, k ≤ n →
      regValRange A.B (denote (genMulCCUpto A k) s) n = (accVal (fun j => A.digit j s) k * y) % N
      ∧ A.clean (denote (genMulCCUpto A k) s)
      ∧ regValRange A.Y (denote (genMulCCUpto A k) s) n = y := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simp [genMulCCUpto, hB0, accVal]
    · simpa [genMulCCUpto] using hclean
    · simpa [genMulCCUpto] using hY
  | succ k ih =>
    intro hk1
    have hk : k < n := by omega
    obtain ⟨ihB, ihclean, ihY⟩ := ih (by omega)
    set D := fun j => A.digit j s with hD
    set Hk := accVal D k with hHk
    set s1 := denote (genMulCCUpto A k) s with hs1
    rw [genMulCCUpto_succ, denote_append, ← hs1]
    have hdk : A.digit k s1 = D k := by rw [hs1]; exact genMulCC_digit_pres A s k k
    have hcN : (Hk * y) % N < N := Nat.mod_lt _ A.hNpos
    refine ⟨?_, ?_, ?_⟩
    · rw [A.correct k s1 ((Hk * y) % N) y hk ihclean hy ihB hcN ihY, hdk,
        accVal_mod_step Hk y N (D k), accVal_succ, ← hHk]
    · exact A.cleanRestored k s1 ((Hk * y) % N) y hk ihclean hy ihB hcN ihY
    · exact A.presY k s1 ((Hk * y) % N) y hk ihclean hy ihB hcN ihY

/-- **The adder-parametric carry-clean modular multiply (the keystone).** For any conforming
restored-clean step, with `B = 0`, `Y = y < N`, and the bank clean, `genMulCC A` leaves the
accumulator holding `(accVal digit n · y) mod N`. Proved ONCE, parametric over `A`. -/
theorem genMulCC_correct (A : VerifiedAdderCarryClean m n N) (s : State m) {y : ℕ}
    (hy : y < N) (hclean : A.clean s)
    (hB0 : regValRange A.B s n = 0) (hY : regValRange A.Y s n = y) :
    regValRange A.B (denote (genMulCC A) s) n = (accVal (fun j => A.digit j s) n * y) % N := by
  rw [genMulCC_eq_upto]
  exact (genMulCC_invariant A s hy hclean hB0 hY n (le_refl n)).1

/-- **The shared bank is restored clean after the full multiply** (so the `Θ(n)` reuse is real). -/
theorem genMulCC_clean (A : VerifiedAdderCarryClean m n N) (s : State m) {y : ℕ}
    (hy : y < N) (hclean : A.clean s)
    (hB0 : regValRange A.B s n = 0) (hY : regValRange A.Y s n = y) :
    A.clean (denote (genMulCC A) s) := by
  rw [genMulCC_eq_upto]
  exact (genMulCC_invariant A s hy hclean hB0 hY n (le_refl n)).2.1

/-- **Derived cost recurrence**: `n · A.toffoli`. The fold is `n` copies of the step composed through
the concatenation; `multiplier_toffoli` turns the gate list into the sum of the per-step counts. -/
theorem genMulCC_toffoli (A : VerifiedAdderCarryClean m n N) :
    (circuitCost (genMulCC A)).toffoli = n * A.toffoli := by
  rw [show genMulCC A = multiplier ((List.range n).map (fun j => A.step j)) from rfl,
    multiplier_toffoli, List.map_map]
  have hconst : (List.range n).map ((fun c => (circuitCost c).toffoli) ∘ fun j => A.step j)
      = (List.range n).map (fun _ => A.toffoli) := by
    apply List.map_congr_left
    intro j _; simp only [Function.comp_apply, A.hToffoli]
  rw [hconst, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

/-! ### The faithfulness instance: the carry-clean Cuccaro multiply (the non-lossy guard)

`cuccaroAdder` instantiates `VerifiedAdderCarryClean` with the existing Stage-2b carry-clean Cuccaro
step `cuccaroModMulStep` (= `cuccaroModDouble ++ cuccaroCModAdd`), reading the proven `cuccaroModDouble`
/ `cuccaroCModAdd` lemmas into the abstract fields via the per-step workhorse `cuccaroModMulStep_spec`.
The generic theorems then recover `cuccaroModMul`'s `(X · Y) mod N` correctness and `20·n² + 14·n` cost
exactly. -/

/-- The GLOBAL single-bank clean precondition for the Cuccaro multiply: every scratch wire of the
shared bank `mod` restored to `false`, plus the modulus preset `Nreg = N`. This is the carry-clean
"bank ready for a step" predicate; `cuccaroModMul_clean` is exactly its restoration. -/
def cuccaroClean (L : CuccaroMulLayout m n) (N : ℕ) (s : State m) : Prop :=
  s (L.mod.Acc n) = false
    ∧ s (L.mod.Nreg n) = false
    ∧ (∀ j, j < n + 1 → s (L.mod.Mask j) = false)
    ∧ (∀ j, j < n + 1 → s (L.mod.B j) = false)
    ∧ s L.mod.flag = false
    ∧ s L.mod.Z = false
    ∧ regValRange L.mod.Nreg s n = N

/-- The read-only multiplier register survives one Cuccaro step (both sub-gadgets leave it external). -/
theorem cuccaroModMulStep_preserves_X (L : CuccaroMulLayout m n) (s : State m) (j i : ℕ) :
    denote (cuccaroModMulStep L j) s (L.X i) = s (L.X i) := by
  rw [cuccaroModMulStep, denote_append,
    cuccaroCModAdd_preserves_external (L.cmod j) _ (L.X i)
      (fun k => L.hXAcc i k) (fun k => L.hXB i k) (fun k => L.hXN i k) (fun k => L.hXM i k)
      (L.hXflag i) (L.hXZ i),
    cuccaroModDouble_preserves_external L.mod s (L.X i)
      (fun k => L.hXAcc i k) (fun k => L.hXN i k) (fun k => L.hXM i k) (L.hXflag i) (L.hXZ i)]

/-- **The per-step Cuccaro workhorse (clean in → step → clean out).** From a clean bank with
`Acc = c < N` and `Y = y < N`, one Horner step (`cuccaroModDouble ++ cuccaroCModAdd`) advances the
residue to `(2·c + [X bit]·y) mod N`, restores the whole shared bank clean, and preserves `Y`. The
refactor of the `succ` case of `cuccaroModMul_invariant` to consume / produce `cuccaroClean`. -/
theorem cuccaroModMulStep_spec (L : CuccaroMulLayout m n) (s : State m) {N c y : ℕ}
    (hclean : cuccaroClean L N s)
    (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1) (hNpos : 0 < N)
    (hAcc : regValRange L.mod.Acc s n = c) (hcN : c < N)
    (hY : regValRange L.Y s n = y) (hyN : y < N) (k : ℕ) :
    regValRange L.mod.Acc (denote (cuccaroModMulStep L k) s) n
        = (2 * c + (if s (L.X (n - 1 - k)) then 1 else 0) * y) % N
      ∧ cuccaroClean L N (denote (cuccaroModMulStep L k) s)
      ∧ regValRange L.Y (denote (cuccaroModMulStep L k) s) n = y := by
  obtain ⟨hAccTop, hNtop, hMask0, hB0, hflag, hZ, hNval⟩ := hclean
  -- DOUBLE on the shared bank
  set sd := denote (cuccaroModDouble L.mod) s with hsddef
  have hdbl := cuccaroModDouble_spec L.mod s hAccTop hNtop hMask0 hflag hZ h2N hNodd hAcc hNval hcN
  obtain ⟨hdAcc, hdflag, hdMask, hdZ, hdAcctop, hdNval, hdNtop⟩ := hdbl
  rw [← hsddef] at hdAcc hdflag hdMask hdZ hdAcctop hdNval hdNtop
  -- B clean / Y / X survive the double (external to Acc,Nreg,Mask,flag,Z)
  have hdB : ∀ j, j < n + 1 → sd (L.mod.B j) = false := fun j hj => by
    rw [hsddef, cuccaroModDouble_preserves_external L.mod s (L.mod.B j)
      (fun i => (L.mod.hAccB i j).symm) (fun i => (L.mod.hBN j i)) (fun i => (L.mod.hBM j i))
      (L.mod.hBflag j) (L.mod.hBZ j)]
    exact hB0 j hj
  have hdY : regValRange L.Y sd n = y := by
    rw [show regValRange L.Y sd n = regValRange L.Y s n from
      Finset.sum_congr rfl (fun j _ => by
        rw [hsddef, cuccaroModDouble_preserves_external L.mod s (L.Y j)
          (fun i => L.hYAcc j i) (fun i => L.hYN j i) (fun i => L.hYM j i)
          (L.hYflag j) (L.hYZ j)]), hY]
  have hdX : ∀ i, sd (L.X i) = s (L.X i) := fun i => by
    rw [hsddef, cuccaroModDouble_preserves_external L.mod s (L.X i)
      (fun j => L.hXAcc i j) (fun j => L.hXN i j) (fun j => L.hXM i j) (L.hXflag i) (L.hXZ i)]
  set d := (2 * c) % N with hddef
  have hdN : d < N := by rw [hddef]; exact Nat.mod_lt _ hNpos
  have hAccd : regValRange L.mod.Acc sd n = d := hdAcc
  -- bit-gated ADD on the shared bank
  set K := L.cmod k with hKdef
  have hKmod : K.mod = L.mod := rfl
  have hKY : K.Y = L.Y := rfl
  have hcm := cuccaroCModAdd_spec K sd
    (by rw [hKmod]; exact hdAcctop) (by rw [hKmod]; exact hdB)
    (by rw [hKmod]; exact hdNtop.trans hNtop)
    (by rw [hKmod]; exact hdMask) (by rw [hKmod]; exact hdflag) (by rw [hKmod]; exact hdZ)
    h2N (by rw [hKmod]; exact hAccd) (by rw [hKmod]; exact hdNval) hdN
    (by rw [hKY]; exact hdY) hyN
  obtain ⟨hcmAcc, hcmflag, hcmAcctop, hcmMask, hcmB, hcmZ, hcmY, hcmctrl, hcmNval, hcmNtop⟩ := hcm
  have hctrlval : sd K.ctrl = s (L.X (n - 1 - k)) := hdX (n - 1 - k)
  have hstep : denote (cuccaroModMulStep L k) s = denote (cuccaroCModAdd K) sd := by
    rw [hKdef, hsddef, cuccaroModMulStep, denote_append]
  rw [hstep]
  refine ⟨?_, ?_, ?_⟩
  · -- VALUE: (2c + [X bit]·y) mod N
    rw [show L.mod.Acc = K.mod.Acc from rfl, hcmAcc, hctrlval, hddef, Nat.mod_add_mod]
    cases s (L.X (n - 1 - k)) <;> simp
  · -- CLEAN restored (the shared bank ready for the next step)
    refine ⟨hcmAcctop, ?_, hcmMask, hcmB, hcmflag, hcmZ, hcmNval⟩
    calc denote (cuccaroCModAdd K) sd (L.mod.Nreg n)
        = sd (L.mod.Nreg n) := hcmNtop
      _ = s (L.mod.Nreg n) := hdNtop
      _ = false := hNtop
  · -- Y preserved
    show regValRange L.Y (denote (cuccaroCModAdd K) sd) n = y
    rw [show L.Y = K.Y from rfl]; exact hcmY

/-- **The faithfulness instance**: the carry-clean Cuccaro multiply as a `VerifiedAdderCarryClean`. -/
def cuccaroAdder (L : CuccaroMulLayout m n) (N : ℕ) (hNpos : 0 < N) (hNodd : N % 2 = 1)
    (h2N : 2 * N ≤ 2 ^ n) : VerifiedAdderCarryClean m n N where
  step k := cuccaroModMulStep L k
  B := L.mod.Acc
  Y := L.Y
  digit k s := if s (L.X (n - 1 - k)) then 1 else 0
  clean := cuccaroClean L N
  toffoli := 20 * n + 14
  hNpos := hNpos
  hToffoli k := cuccaroModMulStep_toffoli L k
  correct := fun k s c Yval _ hclean hYN hAcc hcN hY =>
    (cuccaroModMulStep_spec L s hclean h2N hNodd hNpos hAcc hcN hY hYN k).1
  cleanRestored := fun k s c Yval _ hclean hYN hAcc hcN hY =>
    (cuccaroModMulStep_spec L s hclean h2N hNodd hNpos hAcc hcN hY hYN k).2.1
  presY := fun k s c Yval _ hclean hYN hAcc hcN hY =>
    (cuccaroModMulStep_spec L s hclean h2N hNodd hNpos hAcc hcN hY hYN k).2.2
  digitStable := fun j k s => by
    show (if denote (cuccaroModMulStep L j) s (L.X (n - 1 - k)) then (1 : ℕ) else 0)
        = (if s (L.X (n - 1 - k)) then 1 else 0)
    rw [cuccaroModMulStep_preserves_X L s j (n - 1 - k)]

/-- **Definitional faithfulness**: the generic carry-clean multiplier on the Cuccaro step IS the
existing `cuccaroModMul`. -/
theorem genMulCC_cuccaroAdder_eq (L : CuccaroMulLayout m n) (N : ℕ) (hNpos : 0 < N)
    (hNodd : N % 2 = 1) (h2N : 2 * N ≤ 2 ^ n) :
    genMulCC (cuccaroAdder L N hNpos hNodd h2N) = cuccaroModMul L := rfl

/-- **Correctness faithfulness (the non-lossy guard)**: `genMulCC_correct` on the Cuccaro instance
recovers `cuccaroModMul_correct`'s `(X · Y) mod N` statement exactly. The generic `accVal digit n`
lands on `regValRange X s n` via `accVal_eq_hornerVal` + `regValRange_eq_hornerVal_bits`. -/
theorem genMulCC_cuccaroAdder_correct (L : CuccaroMulLayout m n) (s : State m) {N Yval : ℕ}
    (hNpos : 0 < N) (hNodd : N % 2 = 1) (h2N : 2 * N ≤ 2 ^ n) (hyN : Yval < N)
    (hAccTop : s (L.mod.Acc n) = false) (hNtop : s (L.mod.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.mod.Mask j) = false)
    (hB0 : ∀ j, j < n + 1 → s (L.mod.B j) = false)
    (hflag : s L.mod.flag = false) (hZ : s L.mod.Z = false)
    (hAcc0 : regValRange L.mod.Acc s n = 0) (hNval : regValRange L.mod.Nreg s n = N)
    (hYval : regValRange L.Y s n = Yval) :
    regValRange L.mod.Acc (denote (genMulCC (cuccaroAdder L N hNpos hNodd h2N)) s) n
      = (regValRange L.X s n * Yval) % N := by
  have hclean : cuccaroClean L N s := ⟨hAccTop, hNtop, hMask0, hB0, hflag, hZ, hNval⟩
  have h := genMulCC_correct (cuccaroAdder L N hNpos hNodd h2N) s (y := Yval) hyN hclean hAcc0 hYval
  rw [show regValRange L.mod.Acc (denote (genMulCC (cuccaroAdder L N hNpos hNodd h2N)) s) n
        = (accVal (fun j => (cuccaroAdder L N hNpos hNodd h2N).digit j s) n * Yval) % N from h]
  have hbridge : accVal (fun j => (cuccaroAdder L N hNpos hNodd h2N).digit j s) n
      = regValRange L.X s n := by
    rw [show (fun j => (cuccaroAdder L N hNpos hNodd h2N).digit j s)
          = (fun j => (fun i => if s (L.X i) then (1 : ℕ) else 0) (n - 1 - j)) from rfl,
      accVal_eq_hornerVal (fun i => if s (L.X i) then (1 : ℕ) else 0) n n,
      ← regValRange_eq_hornerVal_bits]
  rw [hbridge]

/-- **Cost faithfulness (the non-lossy guard)**: the cost recurrence on the Cuccaro instance recovers
`cuccaroModMul_toffoli`'s figure `20·n² + 14·n` exactly — the first generic-multiplier instance below
the fresh-ancilla `30·n²` baseline, fully Boolean-verified. -/
theorem genMulCC_cuccaroAdder_toffoli (L : CuccaroMulLayout m n) (N : ℕ) (hNpos : 0 < N)
    (hNodd : N % 2 = 1) (h2N : 2 * N ≤ 2 ^ n) :
    (circuitCost (genMulCC (cuccaroAdder L N hNpos hNodd h2N))).toffoli = 20 * n ^ 2 + 14 * n := by
  rw [genMulCC_toffoli]
  show n * (20 * n + 14) = 20 * n ^ 2 + 14 * n
  ring

/-- **Non-vacuity**: the existing `n = 3` Cuccaro witness inhabits the carry-clean variant. -/
example : VerifiedAdderCarryClean 24 3 3 :=
  cuccaroAdder cuccaroMulLayout3 3 (by decide) (by decide) (by decide)

end Reversible
