/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneRecovery
public import CsdLean4.Empirical.QM.QEC.ErrorDiscretization
public import CsdLean4.Mathlib.QuantumInfo.CliffordTUniversal

/-!
# The Steane code corrects an *arbitrary* error on one qubit

**Category:** 3-Local (Empirical, QM twin). BACKLOG #61, its discretization step; it closes the gap
`SteaneRecovery.lean`'s honest scope named ("Pauli errors only").

★★★ `steane_recovery_arbitrary`: **one channel corrects an arbitrary `2 × 2` error on any one of the
seven qubits**, returning the code state scaled by `tr(MᴴM)/2`; and ★★★
`steane_recovery_unitary_qubit`: for a unitary error that scalar is `1`, so the state is restored
exactly.

Two steps, and the first is general. In `KnillLaflamme.lean`, ★★ `recovery_apply_lin_comb`: the
correction property is **bilinear in the two error slots** and a channel is linear, so a recovery
that corrects a family corrects every linear combination of it, up to the scalar the coefficients
give. For a stabiliser code the family's Knill–Laflamme matrix is the identity
(`stabMat_knillLaflamme`), so the cross terms vanish and the scalar is `∑ᵢ |aᵢ|²`.

The second step is the Steane instance. `gateOf q M`, the `2 × 2` matrix `M` acting on qubit `q` of
the register, is linear in `M` (`gateOf_add`, `gateOf_smul`) and sends the four Paulis to the four
single-qubit Pauli *strings* of the code's error family (`gateOf_one_eq_pauliMat`,
`gateOf_pX_eq_pauliMat`, `gateOf_pZ_eq_pauliMat`, `gateOf_pXZ_eq_pauliMat`, through
`eq_add_unitErr_iff` and `bdot_unitErr`). With `ErrorDiscretization.lean`'s `pauli_decomposition`
that gives ★ `gateOf_eq_sum_pauliMat`: an arbitrary error on one qubit **is** a combination of the
code's own errors, with coefficients read off the entries of `M`. Summing their squares
(`sum_singleCoeff_sq`) turns `∑ᵢ |aᵢ|²` into `tr(MᴴM)/2`.

* `eq_add_unitErr_iff`, `bdot_unitErr` — the label arithmetic of a single-qubit Pauli;
* `gateOf_one_eq_pauliMat`, `gateOf_pX_eq_pauliMat`, `gateOf_pZ_eq_pauliMat`,
  `gateOf_pXZ_eq_pauliMat` — the four Paulis at one position as Pauli strings;
* `singleCoeff`, ★ `gateOf_eq_sum_pauliMat`, `sum_singleCoeff_sq`;
* `exists_steane_recovery_cross` — the recovery with its cross terms, which is what the span step
  consumes;
* ★★★ `steane_recovery_arbitrary`, ★★★ `steane_recovery_unitary_qubit`.

## Honest scope

⚠️ One qubit still. This removes the *Pauli* restriction, not the *weight-one* restriction: two
qubits in error are outside the Steane code's reach at level one, as before.
⚠️ The scalar `tr(MᴴM)/2` is the honest statement for a general `M`: an error that is not unitary is
trace-decreasing, and the recovery returns the code state with that weight. Nothing here normalises
it away.
⚠️ This is the discretization step of BACKLOG #61, not the row: the concatenated *quantum* recovery
at level `k` — the level-`(k+1)` code as seven blocks each carrying a level-`k` encoded qubit, a
block decoder, and the induction — still needs a tensor layer over the blocks. What this file gives
the induction is exactly the step its base case needs: an arbitrary *logical* error on one block is
corrected by the next level up, because the Paulis span the operators of a qubit.

References: E. Knill, R. Laflamme, W. Zurek, Science 279 (1998); M. Nielsen, I. Chuang, *Quantum
Computation and Quantum Information* §10.6; `Mathlib/QuantumInfo/KnillLaflamme.lean`;
`Empirical/QM/QEC/SteaneRecovery.lean`; `Empirical/QM/QEC/ErrorDiscretization.lean`;
`specs/BACKLOG.md` #61; `specs/steane-plan.md`.
-/

@[expose] public section

open Matrix QuantumInfo QuantumInfo.Controlled

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The four single-qubit Paulis at one position, as Pauli strings -/

theorem eq_add_unitErr_iff {q : Fin 7} {z w : Fin 7 → Fin 2} :
    w = z + unitErr q ↔ (∀ i, i ≠ q → z i = w i) ∧ z q ≠ w q := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [h, Pi.add_apply, unitErr_apply, if_neg hi, add_zero]
    · rw [h, Pi.add_apply, unitErr_apply, if_pos rfl]
      have hne : ∀ x : Fin 2, x ≠ x + 1 := by decide
      exact hne (z q)
  · intro ⟨hag, hne⟩
    funext i
    by_cases hi : i = q
    · subst hi
      rw [Pi.add_apply, unitErr_apply, if_pos rfl]
      have hstep : ∀ x y : Fin 2, x ≠ y → y = x + 1 := by decide
      exact hstep (z i) (w i) hne
    · rw [Pi.add_apply, unitErr_apply, if_neg hi, add_zero]
      exact (hag i hi).symm

theorem bdot_unitErr (q : Fin 7) (w : Fin 7 → Fin 2) : bdot (unitErr q) w = w q := by
  rw [bdot]
  rw [Finset.sum_eq_single q]
  · rw [unitErr_apply, if_pos rfl, one_mul]
  · intro i _ hi
    rw [unitErr_apply, if_neg hi, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem gateOf_one_eq_pauliMat (q : Fin 7) :
    gateOf q (1 : Matrix (Fin 2) (Fin 2) ℂ) = pauliMat 0 0 := by
  rw [gateOf_one, pauliMat_zero]

theorem gateOf_pX_eq_pauliMat (q : Fin 7) : gateOf q pX = pauliMat (unitErr q) 0 := by
  ext z w
  rw [pauliMat]
  by_cases hag : ∀ i, i ≠ q → z i = w i
  · rw [gateOf_apply_of_agree hag]
    by_cases hq : z q = w q
    · rw [if_neg (fun h => (eq_add_unitErr_iff.mp h).2 hq), pX, hq]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (w q) with h | h <;> rw [h] <;> simp
    · rw [if_pos (eq_add_unitErr_iff.mpr ⟨hag, hq⟩), pX, pauliSign, bdot]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, signChar_zero]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (z q) with h | h <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (w q) with h' | h' <;>
        rw [h, h'] at hq ⊢ <;> simp_all
  · rw [gateOf_apply_of_not_agree hag, if_neg]
    intro h
    exact hag (eq_add_unitErr_iff.mp h).1

theorem gateOf_pZ_eq_pauliMat (q : Fin 7) : gateOf q pZ = pauliMat 0 (unitErr q) := by
  ext z w
  rw [pauliMat, add_zero]
  by_cases hag : ∀ i, i ≠ q → z i = w i
  · rw [gateOf_apply_of_agree hag]
    by_cases hq : w = z
    · rw [if_pos hq, pauliSign, bdot_unitErr, hq]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (z q) with h | h <;> rw [h] <;>
        simp [pZ, signChar]
    · rw [if_neg hq]
      have hqq : z q ≠ w q := fun hc => hq (funext fun i => by
        by_cases hi : i = q
        · rw [hi, hc]
        · exact (hag i hi).symm)
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (z q) with h | h <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (w q) with h' | h' <;>
        rw [h, h'] at hqq ⊢ <;> simp_all [pZ]
  · rw [gateOf_apply_of_not_agree hag, if_neg]
    intro h
    exact hag fun i _ => by rw [h]

theorem gateOf_pXZ_eq_pauliMat (q : Fin 7) :
    gateOf q pXZ = pauliMat (unitErr q) (unitErr q) := by
  ext z w
  rw [pauliMat]
  by_cases hag : ∀ i, i ≠ q → z i = w i
  · rw [gateOf_apply_of_agree hag]
    by_cases hq : z q = w q
    · rw [if_neg (fun h => (eq_add_unitErr_iff.mp h).2 hq), pXZ_eq, hq]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (w q) with h | h <;> rw [h] <;> simp
    · rw [if_pos (eq_add_unitErr_iff.mpr ⟨hag, hq⟩), pXZ_eq, pauliSign, bdot_unitErr]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (z q) with h | h <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (w q) with h' | h' <;>
        rw [h, h'] at hq ⊢ <;> simp_all [signChar]
  · rw [gateOf_apply_of_not_agree hag, if_neg]
    intro h
    exact hag (eq_add_unitErr_iff.mp h).1

/-! ### An arbitrary single-qubit operator is a combination of the four -/

/-- The Pauli coefficients of a single-qubit operator, as a function on the error labels: supported
on the four labels at the given qubit. -/
noncomputable def singleCoeff (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) : SingleErr → ℂ
  | none => (M 0 0 + M 1 1) / 2
  | some (j, t) =>
      if j = q then
        (if t = 0 then (M 0 1 + M 1 0) / 2
          else if t = 1 then (M 0 0 - M 1 1) / 2 else (M 1 0 - M 0 1) / 2)
      else 0

/-- ★ **Discretization on the Steane register**: an arbitrary operator on one qubit is a
combination of the code's own error family. -/
theorem gateOf_eq_sum_pauliMat (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf q M = ∑ i : SingleErr, singleCoeff q M i • pauliMat (errA i) (errB i) := by
  have hsum : (∑ i : SingleErr, singleCoeff q M i • pauliMat (errA i) (errB i))
      = ((M 0 0 + M 1 1) / 2) • pauliMat 0 0
        + (((M 0 1 + M 1 0) / 2) • pauliMat (unitErr q) 0
          + ((M 0 0 - M 1 1) / 2) • pauliMat 0 (unitErr q)
          + ((M 1 0 - M 0 1) / 2) • pauliMat (unitErr q) (unitErr q)) := by
    rw [Fintype.sum_option]
    congr 1
    rw [Fintype.sum_prod_type, Finset.sum_eq_single q]
    · rw [Fin.sum_univ_three]
      simp only [singleCoeff, errA, errB, show ((2 : Fin 3) = 0) = False from by simp,
        show ((2 : Fin 3) = 1) = False from by simp, show ((1 : Fin 3) = 0) = False from by simp,
        if_false]
      norm_num
    · intro j _ hj
      simp [singleCoeff, hj]
    · intro h
      exact absurd (Finset.mem_univ q) h
  rw [hsum]
  conv_lhs => rw [pauli_decomposition M]
  rw [gateOf_add, gateOf_add, gateOf_add, gateOf_smul, gateOf_smul, gateOf_smul, gateOf_smul,
    gateOf_one_eq_pauliMat, gateOf_pX_eq_pauliMat, gateOf_pZ_eq_pauliMat, gateOf_pXZ_eq_pauliMat]
  abel

/-! ### The recovery, with its cross terms -/

/-- The Steane recovery with the full Knill–Laflamme correction property, cross terms included: the
error labels are distinguishable, so the matrix of scalars is the identity. -/
theorem exists_steane_recovery_cross :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ ρ, ρ = steaneProj * ρ * steaneProj →
        ∀ i j, R.apply (pauliMat (errA i) (errB i) * ρ * (pauliMat (errA j) (errB j))ᴴ)
          = (1 : Matrix SingleErr SingleErr ℂ) j i • ρ :=
  exists_recovery_of_knillLaflamme
    (isCodeProjector_stabMat steaneA_add steaneB_add steane_sigma_coherent)
    (stabMat_ne_zero steaneA_add steaneB_add steane_sigma_coherent steane_labels_injective)
    (stabMat_knillLaflamme steaneA_add steaneB_add steane_sigma_coherent errA errB
      steane_detects_pair)

/-! ### An arbitrary error on one qubit is corrected -/

theorem sum_singleCoeff_sq (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i : SingleErr, ∑ j : SingleErr,
        star (singleCoeff q M i) * singleCoeff q M j * (1 : Matrix SingleErr SingleErr ℂ) i j)
      = (star (M 0 0) * M 0 0 + star (M 0 1) * M 0 1 + star (M 1 0) * M 1 0
          + star (M 1 1) * M 1 1) / 2 := by
  have hdiag : ∀ i : SingleErr, (∑ j : SingleErr,
      star (singleCoeff q M i) * singleCoeff q M j * (1 : Matrix SingleErr SingleErr ℂ) i j)
      = star (singleCoeff q M i) * singleCoeff q M i := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, mul_one]
    · intro j _ hj
      rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl fun i _ => hdiag i, Fintype.sum_option, Fintype.sum_prod_type,
    Finset.sum_eq_single q]
  · rw [Fin.sum_univ_three]
    simp only [singleCoeff]
    have hs : ∀ x : ℂ, star (x / 2) = star x / 2 := by
      intro x
      rw [← starRingEnd_apply, map_div₀, map_ofNat, starRingEnd_apply]
    simp only [hs, star_add, star_sub, show ((2 : Fin 3) = 0) = False from by simp,
      show ((2 : Fin 3) = 1) = False from by simp, show ((1 : Fin 3) = 0) = False from by simp,
      show ((0 : Fin 3) = 1) = False from by simp, if_false, if_true]
    ring
  · intro j _ hj
    simp [singleCoeff, hj]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- ★★★ **The Steane recovery corrects an arbitrary error on one qubit.** For every qubit `q` and
every `2 × 2` matrix `M`, one channel returns the code state scaled by `tr(MᴴM)/2` — the Paulis span
the operators of a qubit, and the Knill–Laflamme correction property is bilinear in the two error
slots, so correcting the four Paulis corrects the whole continuum. -/
theorem steane_recovery_arbitrary :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ ρ, ρ = steaneProj * ρ * steaneProj → ∀ (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ),
        R.apply (gateOf q M * ρ * (gateOf q M)ᴴ)
          = ((star (M 0 0) * M 0 0 + star (M 0 1) * M 0 1 + star (M 1 0) * M 1 0
              + star (M 1 1) * M 1 1) / 2) • ρ := by
  obtain ⟨R, hR⟩ := exists_steane_recovery_cross
  refine ⟨R, fun ρ hρ q M => ?_⟩
  rw [gateOf_eq_sum_pauliMat q M,
    recovery_apply_lin_comb (fun ρ' hρ' i j => hR ρ' hρ' i j) (singleCoeff q M) hρ,
    sum_singleCoeff_sq]

/-- ★★★ **A unitary error on one qubit is undone exactly.** The scalar of
`steane_recovery_arbitrary` is `tr(MᴴM)/2 = 1` for a unitary block. -/
theorem steane_recovery_unitary_qubit :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ ρ, ρ = steaneProj * ρ * steaneProj → ∀ (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ),
        M ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        R.apply (gateOf q M * ρ * (gateOf q M)ᴴ) = ρ := by
  obtain ⟨R, hR⟩ := steane_recovery_arbitrary
  refine ⟨R, fun ρ hρ q M hM => ?_⟩
  obtain ⟨h1, h2, -, -⟩ := unitary_entries hM
  rw [hR ρ hρ q M]
  rw [show (star (M 0 0) * M 0 0 + star (M 0 1) * M 0 1 + star (M 1 0) * M 1 0
      + star (M 1 1) * M 1 1) / 2 = 1 by
    rw [← starRingEnd_apply, ← starRingEnd_apply, ← starRingEnd_apply, ← starRingEnd_apply]
    rw [show (starRingEnd ℂ) (M 0 0) * M 0 0 + (starRingEnd ℂ) (M 0 1) * M 0 1
        + (starRingEnd ℂ) (M 1 0) * M 1 0 + (starRingEnd ℂ) (M 1 1) * M 1 1
        = ((starRingEnd ℂ) (M 0 0) * M 0 0 + (starRingEnd ℂ) (M 1 0) * M 1 0)
          + ((starRingEnd ℂ) (M 0 1) * M 0 1 + (starRingEnd ℂ) (M 1 1) * M 1 1) by ring, h1, h2]
    norm_num, one_smul]

end Steane
end QEC
end QM
end Empirical
end CSD
