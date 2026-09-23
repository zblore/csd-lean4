/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.MeasurementAdder
public import CsdLean4.Mathlib.QuantumInfo.Reversible.HybridLift

/-!
# The measurement-based AND-adder on the full register: the `n`-fold hybrid amplitude equality

**Category:** 3-Local (QM-validity content; no CSD ontology).

`MeasurementAdder.lean` (#21) re-costs the AND-adder by replacing its `3n` reverse-pass Toffolis
with measurement gadgets and proves the Toffoli count; what it left open was the
**amplitude-level** statement that the hybrid adder, run on the full register, produces the same
data as the unitary adder. This module proves it, with one correction to the picture #21 drew.

**The correction.** The reverse pass of a carry cell is three Toffolis with the same target,
`[CCX a b g, CCX a c g, CCX b c g]` reversed, and the ancilla `g` holds the **majority**
`ab ⊕ ac ⊕ bc` — not an AND — when the pass begins. Gidney's single-CZ gadget is correct only on
an AND-shaped ancilla, so replacing each of the three Toffolis by it is **not** amplitude-exact:
the first replacement, at ancilla `maj` with corrections for `bc`, leaves the data-dependent
phase `(−1)^{m(ab ⊕ ac)}` on the `m = 1` branch (`naive_cell_gadget_sign_flip` exhibits the
sign). The amplitude-exact hybrid replaces the cell's **whole** reverse block by **one**
measure-and-correct gadget with a CZ on each of the three input pairs (`cellGadget`): the
majority ancilla is exactly the parity those corrections cancel. This saves the same `3n`
Toffolis with `n` measurements instead of `3n`.

* `hybridAdd L mo` — the forward and sum passes as unitaries, then the measurement-based
  uncompute pass `hybridUncompute L mo n` (cells `n−1, …, 0`, one gadget each, outcomes `mo`).
* `wellFormed_hybridUncompute` — the run is well-formed: when cell `i`'s gadget fires, its
  ancilla `G (i+1)` holds the majority of `A i, B i, G i` (the forward carry invariant, carried
  through the sum pass and the later cells, which never touch these wires).
* ★★ `hybridAdd_amplitude` — **the `n`-fold hybrid amplitude equality**: on every basis input
  with clean ancillas the hybrid adder produces `(√2)⁻¹^n • |out⟩`, where `out` agrees with the
  unitary adder's output on every wire except the `n` carry ancillas
  (`hybridAdd_shadow_data`), which hold the outcomes (`hybridAdd_shadow_outcome`); in
  particular the sum register holds `(A + B) mod 2ⁿ` (`hybridAdd_sum`). By linearity the same
  holds for any superposition of clean-ancilla inputs (`hybridLin_sum`).
* `measureUncompute_eq_measureCorrect` — the general-wire gadget of `HybridLift.lean`, at
  wires `(0,1,2)` of `QReg 3` with the single correction `(0,1)`, **is** the operator
  `measureUncompute` of `MeasurementUncompute.lean` (#31): the same Hadamard, projector and
  CZ, entry for entry.

## Honest scope

The gadget is represented per outcome; the branch amplitude `(√2)⁻¹^n` says each of the `2ⁿ`
outcome strings has probability `2⁻ⁿ`, and every branch carries the right data. The Toffoli
count of the hybrid uncompute pass is `0` as before (each gadget is Hadamard, measurement and
Cliffords); its measurement count is `n`, not the `3n` that #21's per-Toffoli bookkeeping
implied. No ECDSA resource-score change is claimed.
-/

@[expose] public section

open scoped Matrix
open QuantumInfo
open Reversible

namespace CSD.Empirical.QM

variable {m n : ℕ}

/-! ## The general-wire gadget is #31's gadget -/

/-- `update w 2 mo` on three wires is the literal triple. -/
lemma update_two_eq (w : B3) (mo : Fin 2) : Function.update w 2 mo = ![w 0, w 1, mo] := by
  funext i
  fin_cases i <;> simp

/-- The single-pair correction phase is the data CZ phase at outcome `1`, and `1` at outcome
`0`. -/
lemma correctionPhase_single (mo : Fin 2) (z : B3) :
    correctionPhase [((0 : Fin 3), (1 : Fin 3))] mo z
      = if mo = 1 then czPhase (z 0) (z 1) else 1 := by
  unfold correctionPhase andParity czPhase
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  fin_cases mo
  · simp
  · simp only [Fin.isValue, Fin.mk_one, if_true, one_mul]
    exact neg_one_pow_fin_mul (z 0) (z 1)

/-- The entry identity behind the bridge: the general-wire gadget entry is the product of
#31's correction, projector and Hadamard entries. -/
lemma measureCorrect_entry (mo : Fin 2) (z w : B3) :
    measureCorrectMat [((0 : Fin 3), (1 : Fin 3))] 2 mo z w
      = (if mo = 1 then czPhase (z 0) (z 1) else 1)
          * ((if z 2 = mo then 1 else 0) * hadA z w) := by
  rw [measureCorrectMat_apply, hadA_apply, update_two_eq, correctionPhase_single]
  by_cases h : z = ![w 0, w 1, mo]
  · rw [if_pos h]
    have h' := (b3_eq_iff z (w 0) (w 1) mo).mp h
    rw [if_pos h'.2.2, if_pos (show z 0 = w 0 ∧ z 1 = w 1 from ⟨h'.1, h'.2.1⟩), h'.2.2]
    ring
  · rw [if_neg h]
    have h' : ¬ (z 0 = w 0 ∧ z 1 = w 1 ∧ z 2 = mo) :=
      fun hh => h ((b3_eq_iff z (w 0) (w 1) mo).mpr hh)
    by_cases h2 : z 2 = mo
    · rw [if_pos h2, if_neg (show ¬ (z 0 = w 0 ∧ z 1 = w 1) from fun hh => h' ⟨hh.1, hh.2, h2⟩)]
      ring
    · rw [if_neg h2]
      ring

/-- ★ **The general-wire gadget is #31's gadget.** On `QReg 3`, the measure-and-correct gadget
on ancilla `2` with the single correction `(0, 1)` is the operator `measureUncompute` of
`MeasurementUncompute.lean`, entry for entry. -/
theorem measureUncompute_eq_measureCorrect (mo : Fin 2) (ψ : QReg 3) :
    measureUncompute mo ψ
      = Matrix.toEuclideanLin (measureCorrectMat [((0 : Fin 3), (1 : Fin 3))] 2 mo) ψ := by
  ext z
  rw [measureUncompute, corr_apply, proj_apply, Matrix.toLpLin_apply, Matrix.toLpLin_apply]
  show (if mo = 1 then czPhase (z 0) (z 1) else 1)
      * ((if z 2 = mo then 1 else 0) * (hadA *ᵥ ψ.ofLp) z)
    = (measureCorrectMat [((0 : Fin 3), (1 : Fin 3))] 2 mo *ᵥ ψ.ofLp) z
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [measureCorrect_entry]
  ring

/-! ## Why one gadget per cell: the naive replacement's sign -/

/-- **The naive replacement is not amplitude-exact.** On the four wires `a, b, c, g` with
`a = b = 1`, `c = 0` and the ancilla `g = 1 = maj(a, b, c)`, the single-CZ gadget for the block
`CCX b c g` (corrections for `b ∧ c = 0` only) flips the sign of the `m = 1` branch: the data
survive, but with the relative phase `(−1)^{ab ⊕ ac} = −1` against the branches where it does
not fire. -/
theorem naive_cell_gadget_sign_flip :
    Matrix.toEuclideanLin (measureCorrectMat [((1 : Fin 4), (2 : Fin 4))] 3 1)
        (basisState ![1, 1, 0, 1])
      = -(Real.sqrt 2 : ℂ)⁻¹ • basisState ![1, 1, 0, 1] := by
  rw [measureCorrectMat_basisState]
  have hupd : Function.update (![1, 1, 0, 1] : Fin 4 → Fin 2) 3 1 = ![1, 1, 0, 1] := by
    funext i; fin_cases i <;> rfl
  rw [measureCorrect_scalar_of_ne _ _ _ (by decide) (by decide), hupd]

/-! ## The hybrid adder -/

/-- **The cell gadget:** measure the majority ancilla `G (i+1)` of cell `i` and correct with a
CZ on each input pair `(A i, B i)`, `(A i, G i)`, `(B i, G i)`. -/
def cellGadget (L : AndAddLayout m n) (i : ℕ) (mo : Fin 2) : HybridGate m :=
  .measure [(L.A i, L.B i), (L.A i, L.G i), (L.B i, L.G i)] (L.G (i + 1)) mo

/-- **The measurement-based uncompute pass** over cells `k−1, …, 0` (cell `k−1` first, as in
the reverse pass), one gadget per cell with outcomes `mo`. -/
def hybridUncompute (L : AndAddLayout m n) (mo : ℕ → Fin 2) : ℕ → List (HybridGate m)
  | 0 => []
  | k + 1 => cellGadget L k (mo k) :: hybridUncompute L mo k

/-- **The hybrid adder:** the forward and sum passes as unitaries, then the measurement-based
uncompute pass over all `n` cells. -/
def hybridAdd (L : AndAddLayout m n) (mo : ℕ → Fin 2) : List (HybridGate m) :=
  (andForward L ++ andSumPass L).map HybridGate.gate ++ hybridUncompute L mo n

lemma gadgetCount_hybridUncompute (L : AndAddLayout m n) (mo : ℕ → Fin 2) :
    ∀ k, gadgetCount (hybridUncompute L mo k) = k
  | 0 => rfl
  | k + 1 => by
    rw [hybridUncompute, cellGadget, gadgetCount, gadgetCount_hybridUncompute L mo k]

lemma gadgetCount_hybridAdd (L : AndAddLayout m n) (mo : ℕ → Fin 2) :
    gadgetCount (hybridAdd L mo) = n := by
  rw [hybridAdd, gadgetCount_gate_list_append, gadgetCount_hybridUncompute]

/-- The uncompute pass writes only the carry ancillas of its cells. -/
lemma shadow_hybridUncompute_of_ne (L : AndAddLayout m n) (mo : ℕ → Fin 2) :
    ∀ (k : ℕ) (u : Fin m → Fin 2) (i : Fin m), (∀ j, j < k → i ≠ L.G (j + 1)) →
      shadow (hybridUncompute L mo k) u i = u i
  | 0, _, _, _ => rfl
  | k + 1, u, i, hi => by
    rw [hybridUncompute, shadow_cons, cellGadget, HybridGate.shadow,
      shadow_hybridUncompute_of_ne L mo k _ i fun j hj => hi j (by omega),
      Function.update_of_ne (hi k (Nat.lt_succ_self k))]

/-- The uncompute pass writes each cell's outcome into its carry ancilla. -/
lemma shadow_hybridUncompute_anc (L : AndAddLayout m n) (mo : ℕ → Fin 2) :
    ∀ (k : ℕ), k ≤ n → ∀ (u : Fin m → Fin 2) (j : ℕ), j < k →
      shadow (hybridUncompute L mo k) u (L.G (j + 1)) = mo j
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, hk, u, j, hj => by
    rw [hybridUncompute, shadow_cons, cellGadget, HybridGate.shadow]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact shadow_hybridUncompute_anc L mo k (by omega) _ j hjk
    · have hjk' : j = k := by omega
      subst hjk'
      rw [shadow_hybridUncompute_of_ne L mo j _ _ fun j' hj' h =>
          by have := L.hGinj (j + 1) (j' + 1) (by omega) (by omega) h; omega,
        Function.update_self]

/-- `majority` as a `Fin 2` parity of pairwise ANDs, in the recast. -/
lemma regOfState_majority (a b c : Bool) :
    (if majority a b c then (1 : Fin 2) else 0)
      = (if a then (1 : Fin 2) else 0) * (if b then (1 : Fin 2) else 0)
        + ((if a then (1 : Fin 2) else 0) * (if c then (1 : Fin 2) else 0)
          + ((if b then (1 : Fin 2) else 0) * (if c then (1 : Fin 2) else 0) + 0)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- **The run is well-formed.** If `t` satisfies the carry invariant (each `G (i+1)` holds the
majority of `A i, B i, G i`), then on any register state agreeing with `t` on the wires of the
cells still to come, the uncompute pass over `k ≤ n` cells is well-formed: every gadget meets
its majority ancilla, and its corrections avoid it. -/
theorem wellFormed_hybridUncompute (L : AndAddLayout m n) (mo : ℕ → Fin 2) (t : State m)
    (hmaj : ∀ j, j < n → t (L.G (j + 1)) = majority (t (L.A j)) (t (L.B j)) (t (L.G j))) :
    ∀ (k : ℕ), k ≤ n → ∀ u : Fin m → Fin 2,
      (∀ j, j < k → u (L.A j) = regOfState t (L.A j) ∧ u (L.B j) = regOfState t (L.B j)
        ∧ u (L.G j) = regOfState t (L.G j)
        ∧ u (L.G (j + 1)) = regOfState t (L.G (j + 1))) →
      WellFormed (hybridUncompute L mo k) u
  | 0, _, _, _ => trivial
  | k + 1, hk, u, hu => by
    rw [hybridUncompute, cellGadget, wellFormed_measure_cons]
    obtain ⟨hA, hB, hG, hG1⟩ := hu k (Nat.lt_succ_self k)
    have hGG : L.G k ≠ L.G (k + 1) := fun h => by
      have := L.hGinj k (k + 1) (by omega) (by omega) h
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨L.hAG k (k + 1), L.hBG k (k + 1)⟩
      · exact ⟨L.hAG k (k + 1), hGG⟩
      · exact ⟨L.hBG k (k + 1), hGG⟩
    · rw [hG1]
      simp only [andParity, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hA, hB,
        hG, regOfState]
      rw [hmaj k (by omega)]
      exact regOfState_majority _ _ _
    · refine wellFormed_hybridUncompute L mo t hmaj k (by omega) _ fun j hj => ?_
      obtain ⟨hA', hB', hG', hG1'⟩ := hu j (by omega)
      have hGj : L.G j ≠ L.G (k + 1) := fun h => by
        have := L.hGinj j (k + 1) (by omega) (by omega) h
        omega
      have hGj1 : L.G (j + 1) ≠ L.G (k + 1) := fun h => by
        have := L.hGinj (j + 1) (k + 1) (by omega) (by omega) h
        omega
      exact ⟨by rw [Function.update_of_ne (L.hAG j (k + 1)), hA'],
        by rw [Function.update_of_ne (L.hBG j (k + 1)), hB'],
        by rw [Function.update_of_ne hGj, hG'], by rw [Function.update_of_ne hGj1, hG1']⟩

/-! ## The carry invariant after the forward and sum passes -/

/-- After the forward and sum passes, each carry ancilla holds the majority of its cell's
inputs: the forward carry invariant, untouched by the sum pass. -/
lemma unitaryPrefix_majority (L : AndAddLayout m n) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (j : ℕ) (hj : j < n) :
    denote (andForward L ++ andSumPass L) s (L.G (j + 1))
      = majority (denote (andForward L ++ andSumPass L) s (L.A j))
          (denote (andForward L ++ andSumPass L) s (L.B j))
          (denote (andForward L ++ andSumPass L) s (L.G j)) := by
  rw [denote_append]
  have hsum : ∀ w : Fin m, (∀ i, i < n → w ≠ L.S i) →
      denote (andSumPass L) (denote (andForward L) s) w = denote (andForward L) s w :=
    fun w hw => andSumPrefix_preserves_of_ne_S L _ n hw
  rw [hsum _ (fun i _ h => L.hSG i (j + 1) h.symm), hsum _ (fun i _ h => L.hAS j i h),
    hsum _ (fun i _ h => L.hBS j i h), hsum _ (fun i _ h => L.hSG i j h.symm)]
  obtain ⟨hcarry, -⟩ := andForward_carry L s hG0 n le_rfl
  rw [andForward, hcarry (j + 1) (by omega), hcarry j (by omega),
    andForwardPrefix_preserves_A, andForwardPrefix_preserves_B]
  rfl

/-! ## ★★ The n-fold hybrid amplitude equality -/

/-- The hybrid run is well-formed on every clean-ancilla basis input. -/
theorem wellFormed_hybridAdd (L : AndAddLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) :
    WellFormed (hybridAdd L mo) (regOfState s) := by
  rw [hybridAdd, wellFormed_gate_list_append, stateOfReg_regOfState]
  exact wellFormed_hybridUncompute L mo _ (unitaryPrefix_majority L s hG0) n le_rfl _
    fun j _ => ⟨rfl, rfl, rfl, rfl⟩

/-- ★★ **The `n`-fold hybrid amplitude equality.** On every basis input with clean carry
ancillas, the hybrid adder — forward and sum passes, then one measure-and-correct gadget per
carry cell with outcomes `mo` — produces `(√2)⁻¹^n • |out⟩`, `out` the run's shadow. -/
theorem hybridAdd_amplitude (L : AndAddLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) :
    hybridLin (hybridAdd L mo) (basisState (regOfState s))
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ n • basisState (shadow (hybridAdd L mo) (regOfState s)) := by
  rw [hybridLin_basisState _ _ (wellFormed_hybridAdd L mo s hG0), gadgetCount_hybridAdd]

/-- **The data agree with the unitary adder.** On every wire other than the `n` carry ancillas
`G 1, …, G n`, the hybrid output is the unitary adder's output: the uncompute pass — unitary or
measured — writes nothing else. -/
theorem hybridAdd_shadow_data (L : AndAddLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (i : Fin m) (hi : ∀ j, j < n → i ≠ L.G (j + 1)) :
    shadow (hybridAdd L mo) (regOfState s) i = regOfState (denote (andAdd L) s) i := by
  rw [hybridAdd, shadow_append, shadow_gate_list, stateOfReg_regOfState,
    shadow_hybridUncompute_of_ne L mo n _ i hi]
  have e : denote (andAdd L) s
      = denote (inverse (andForward L)) (denote (andForward L ++ andSumPass L) s) :=
    denote_append (andForward L ++ andSumPass L) (inverse (andForward L)) s
  rw [e]
  simp only [regOfState]
  rw [denote_apply_of_forall_not_mem_target (inverse (andForward L)) fun g hg hmem => ?_]
  rw [inverse, List.mem_reverse] at hg
  obtain ⟨j, hj, hgj⟩ := mem_andForwardPrefix hg
  exact hi j hj (andForwardSlice_target hgj hmem)

/-- **The ancillas hold the outcomes.** -/
theorem hybridAdd_shadow_outcome (L : AndAddLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (j : ℕ) (hj : j < n) :
    shadow (hybridAdd L mo) (regOfState s) (L.G (j + 1)) = mo j := by
  rw [hybridAdd, shadow_append, shadow_hybridUncompute_anc L mo n le_rfl _ j hj]

/-- **The sum is right on every branch.** The sum register of the hybrid output holds
`(A + B) mod 2ⁿ`, exactly as for the unitary adder (`andAdd_correct`). -/
theorem hybridAdd_sum (L : AndAddLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (hS0 : ∀ i, s (L.S i) = false) :
    regValRange L.S (stateOfReg (shadow (hybridAdd L mo) (regOfState s))) n
      = (regValRange L.A s n + regValRange L.B s n) % 2 ^ n := by
  rw [← andAdd_correct L s hG0 hS0]
  unfold regValRange
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := hybridAdd_shadow_data L mo s (L.S i) fun j _ => L.hSG i (j + 1)
  simp only [stateOfReg]
  rw [h]
  exact congrArg (fun b : Bool => b.toNat * 2 ^ i)
    (congrFun (stateOfReg_regOfState (denote (andAdd L) s)) (L.S i))

end CSD.Empirical.QM

end
