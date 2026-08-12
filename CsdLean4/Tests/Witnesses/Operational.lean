/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.WeakMeasurement
public import CsdLean4.LF6.Decoherence

/-!
# WS-F witness: mixed states, a genuine POVM, and a mixed reduced state

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-F).

Three concrete operational witnesses, each firing an existing production
surface:

* **Proper mixed state** — `mixedHalf : DensityOperator 2` (the maximally
  mixed qubit `½·I`), every structure field proved; `mixedHalf_ne_pure`
  separates it from the pure state `|0⟩⟨0|` by an explicit matrix entry, so
  the `DensityOperator` interface is inhabited *beyond* the rank-one image of
  `rankOneDensity`.
* **Genuine (non-projective) POVM** — the production unsharp family
  `weakPOVM η` at `η = ½`: `weakPOVM_half_weights` packages completeness
  fired on a unit preparation (`POVM.weights_sum_eq_normSq` → weights sum to
  `1`) with genuine unsharpness (`weak_partial_information_witness`: the
  plus-outcome weight on `e0` is strictly between `½` and `1` — more
  information than no measurement, less than projective).
* **Mixed reduced state of an entangled composite** — the de-isolation
  isometry `V` entangles system and pointer; `decohereReduced ψ` is the
  partial trace of the composite `V|ψ⟩⟨ψ|Vᴴ` over the pointer
  (`LF6/Decoherence.lean`). At the explicit unit superposition
  `plusVec = (e₀ + e₁)/√2`: the reduction has trace `1`
  (`plusVec_reduced_trace`, a genuine density operator) and purity strictly
  below `1` (`plusVec_reduced_strictly_mixed`) — a pure composite with a
  properly mixed marginal, the LF6-B.2 witness fired at a concrete state.

**Anti-duplication scope.** `weakPOVM`, `weights_sum_eq_normSq`,
`weak_partial_information_witness`, `decohereReduced_trace`, and
`decohere_purity_lt_one_of_superposition` are production and are cited;
the new content is the concrete inhabitants (`mixedHalf`, `plusVec`) and
their nontriviality clauses.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder
open CSD.LF2 CSD.LF6
open CSD.Empirical.CSDBridge.WeakMeasurement

namespace CSD
namespace Tests
namespace Witnesses

/-! ## The proper mixed state -/

/-- **The maximally mixed qubit `½·I` as a `DensityOperator`** — every field
proved: Hermitian, PSD (via the production `psd_smul`), trace `1`. -/
noncomputable def mixedHalf : LF2.DensityOperator 2 where
  M := ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    congr 1
    simp
  nonneg := psd_smul Matrix.PosSemidef.one (by norm_num)
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num

/-- **Nontriviality: the mixed state is not the pure state `|0⟩⟨0|`** — the
`(0,0)` entries differ (`½ ≠ 1`). So the `DensityOperator` interface is
inhabited beyond the rank-one image. -/
theorem mixedHalf_ne_pure :
    mixedHalf.M ≠ (LF2.rankOneDensity e0 e0_norm).M := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hL : mixedHalf.M 0 0 = ((1 / 2 : ℝ) : ℂ) := by
    show ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = _
    simp
  have hR : (LF2.rankOneDensity e0 e0_norm).M 0 0 = 1 := by
    show LF2.outerProduct e0 0 0 = 1
    rw [LF2.outerProduct, Matrix.vecMulVec_apply]
    simp [e0, EuclideanSpace.single]
  rw [hL, hR] at h00
  norm_num at h00

/-! ## The genuine POVM -/

/-- **The unsharp POVM at `η = ½`, exercised.** Completeness fired on the
unit preparation `e0` (the weights are a probability vector), and genuine
unsharpness: the plus-outcome weight is strictly between `½` (no measurement)
and `1` (the projective value on `e0`) — the production
`weak_partial_information_witness` on the production `weakPOVM`. -/
theorem weakPOVM_half_weights :
    (∑ i, (weakPOVM (1 / 2) (by norm_num) (by norm_num)).weight e0 i = 1)
      ∧ (1 : ℝ) / 2
          < (weakPOVM (1 / 2) (by norm_num) (by norm_num)).weight e0 0
      ∧ (weakPOVM (1 / 2) (by norm_num) (by norm_num)).weight e0 0 < 1 := by
  have hsum := (weakPOVM (1 / 2) (by norm_num) (by norm_num)).weights_sum_eq_normSq e0
  rw [e0_norm, one_pow] at hsum
  have hwit := weak_partial_information_witness
  rw [e0_ofLp_zero] at hwit
  refine ⟨hsum, ?_, ?_⟩
  · show (1 : ℝ) / 2
        < RCLike.re (inner ℂ e0 (Matrix.toEuclideanLin (weakPlusM (1 / 2)) e0))
    exact hwit.1
  · show RCLike.re (inner ℂ e0 (Matrix.toEuclideanLin (weakPlusM (1 / 2)) e0)) < 1
    have h1 := hwit.2
    simpa using h1

/-! ## The mixed reduced state -/

/-- The explicit unit superposition `(e₀ + e₁)/√2` on the qubit. -/
noncomputable def plusVec : EuclideanSpace ℂ (Fin 2) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) + EuclideanSpace.single (1 : Fin 2) (1 : ℂ))

theorem plusVec_apply (j : Fin 2) : plusVec j = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  fin_cases j <;>
    simp [plusVec, EuclideanSpace.single]

theorem plusVec_norm : ‖plusVec‖ = 1 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, plusVec_apply 0, plusVec_apply 1,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show ((Real.sqrt 2)⁻¹) ^ 2 + ((Real.sqrt 2)⁻¹) ^ 2 = 2 / Real.sqrt 2 ^ 2 from by ring,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Both Born weights of `plusVec` are `½ ≠ 0` (the superposition hypothesis
of the purity-drop witness, discharged concretely). -/
theorem plusVec_born_ne_zero (j : Fin 2) :
    ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) plusVec‖ ^ 2 ≠ 0 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, plusVec_apply,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- **The reduced state is a genuine density operator**: the partial trace of
the entangled composite `V|+⟩⟨+|Vᴴ` over the pointer has trace `1`.
Instantiates the production `decohereReduced_trace` at `plusVec`. -/
theorem plusVec_reduced_trace : (decohereReduced plusVec).trace = 1 := by
  rw [decohereReduced_trace, plusVec_norm]
  norm_num

/-- **WS-F headline: a pure entangled composite with a properly mixed
marginal.** The reduced state of the de-isolated `plusVec` has purity
strictly below `1` — the LF6-B.2 purity-drop witness fired at the explicit
superposition, both nonzero-weight hypotheses discharged by computation. -/
theorem plusVec_reduced_strictly_mixed :
    ((decohereReduced plusVec) * (decohereReduced plusVec)).trace.re < 1 :=
  decohere_purity_lt_one_of_superposition plusVec plusVec_norm
    (by decide : (0 : Fin 2) ≠ 1)
    (plusVec_born_ne_zero 0) (plusVec_born_ne_zero 1)

end Witnesses
end Tests
end CSD
