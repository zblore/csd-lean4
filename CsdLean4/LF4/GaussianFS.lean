import CsdLean4.LF4.MomentMarginal
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# LF4 plan B, Part 1 (step): unitary norm-preservation on `ℂ^N`

Toward discharging `fs_moment_pushforward_uniform` via the Gaussian route
(`specs/plan-b-detail.md` Part 1). This file lands the matrix-analytic core
that L3 (Gaussian unitary-invariance) needs: a unitary matrix's `toEuclideanLin`
action preserves the Euclidean norm.

**Blocker note (RESOLVED).** Building the `U(2)` action as a `≃ₗᵢ[ℝ]` for
`stdGaussian_map` via `(unitaryIsomC U).restrictScalars ℝ` hit an
instance-resolution ambiguity (`LinearMap.CompatibleSMul … ℝ ℂ` /
`IsScalarTower ℝ ℂ …` failing inside the full LF4 import chain). This was
resolved by taking the `ℝ`-isometry route (plan §Part 1 option (a)): `conjRN` /
`coordsN` in `GaussianCPN.lean` realise the real-scalar route in a genuine real
space, sidestepping the ℝ-over-ℂ instances, and the Gaussian → Fubini–Study
identification `gaussianCPN_eq_fubiniStudy` is proved there. The qubit DH fact
`fs_moment_pushforward_uniform` is consequently a theorem (`MomentUniform.lean`),
not an axiom.
-/

open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- A unitary matrix's `toEuclideanLin` action preserves the Euclidean norm
(`‖U v‖ = ‖v‖`), from `Uᴴ U = 1`. -/
lemma unitary_norm_preserving (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin U.val) v‖ = ‖v‖ := by
  have hUU : U.valᴴ * U.val = 1 := by
    have h := U.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    rwa [Matrix.star_eq_conjTranspose] at h
  have hL : ∀ (w : Fin N → ℂ), ∑ i, ‖w i‖ ^ 2 = (star w ⬝ᵥ w).re := by
    intro w
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have key : star (U.val *ᵥ WithLp.ofLp v) ⬝ᵥ (U.val *ᵥ WithLp.ofLp v)
      = star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hUU,
        Matrix.one_mulVec]
  have hsq : ‖(Matrix.toEuclideanLin U.val) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
    show ∑ i, ‖(U.val *ᵥ WithLp.ofLp v) i‖ ^ 2 = ∑ i, ‖WithLp.ofLp v i‖ ^ 2
    rw [hL (U.val *ᵥ WithLp.ofLp v), hL (WithLp.ofLp v), key]
  have h1 : 0 ≤ ‖(Matrix.toEuclideanLin U.val) v‖ := norm_nonneg _
  have h2 : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

/-- The unitary action on `ℂ²` as a **complex** linear isometry equiv (the real
form, needed for `stdGaussian_map`, is blocked on the `restrictScalars`
instance issue — see the module docstring). -/
noncomputable def unitaryIsomC (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  { toLinearEquiv := Matrix.UnitaryGroup.toEuclideanLinearEquiv U
    norm_map' := unitary_norm_preserving U }

end LF4
end CSD
