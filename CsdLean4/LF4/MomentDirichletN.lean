import CsdLean4.LF4.GaussianCPN
import CsdLean4.LF4.MomentMap
import CsdLean4.LF4.MomentRatioUniformN
import CsdLean4.LF4.MomentBridgeN

/-!
# LF4 general-N Slice E (headline): the joint Dirichlet moment pushforward

The general-N analogue of `fs_moment_pushforward_uniform` (which handled the qubit
scalar marginal `N = 2`). The **free-coordinate moment map** `ratioN ∘ momentMap`
pushes the genuine Fubini–Study measure on `ℂℙ^M` forward to `M!` times the uniform
measure on the open simplex — the Dirichlet(1,…,1) law,

```
(ratioN ∘ momentMap)∗ μ_FS = M! · vol|_{openSimplexFree}.
```

This is the joint Duistermaat–Heckman fact for general `N = M+1`, the object the
qubit marginal could not give (the single-coordinate marginal is `Beta(1, N-1)`, not
the Born weight, for `N ≥ 3`; only the joint simplex law feeds `born_eq_volume_ratio`).

The proof is the general-N assembly:
`gaussianCPN_eq_fubiniStudy` (Slice B) realises `μ_FS` as a projectivised Gaussian;
`map_pi_eq_stdGaussian` exposes the `ℝ^{N×2}` standard Gaussian as `gaussianReal^{⊗(N×2)}`;
`blockSqNormCurry_map_pi` (Slice E bridge) lands on `Exp(1/2)^{⊗N}`; and
`ratioSqNorm_map_expHalf_pi` (Slice D) is the Gamma→Dirichlet crux. The a.e.-off-`{0}`
pointwise identity `ratioN (momentMap [coordsN(toLp y)]) = ratioN (blockSqNorm (curry y))`
glues the geometric and coordinate routes.
-/

open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {M : ℕ}

/-- The standard Gaussian on `ℝ^{(M+1)×2}` has no atom at the origin. -/
theorem pi_gaussianReal_prod_singleton_zero :
    Measure.pi (fun _ : Fin (M + 1) × Fin 2 => gaussianReal 0 1)
        {(0 : (Fin (M + 1) × Fin 2) → ℝ)} = 0 := by
  rw [show ({(0 : (Fin (M + 1) × Fin 2) → ℝ)} : Set ((Fin (M + 1) × Fin 2) → ℝ))
        = Set.univ.pi (fun _ => {(0 : ℝ)}) by
      ext f; simp only [Set.mem_singleton_iff, Set.mem_univ_pi, funext_iff]; rfl,
    Measure.pi_pi]
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin (M + 1)), (0 : Fin 2)))
    (measure_singleton _)

/-- **Slice E headline: the joint Dirichlet moment pushforward (general N).** The
free-coordinate moment map `ratioN ∘ momentMap` pushes the Fubini–Study measure on
`ℂℙ^M` to `M!` times uniform measure on the open simplex (the Dirichlet(1,…,1) law).
The qubit `fs_moment_pushforward_uniform` is the `M = 1` shadow (its scalar marginal).
Foundational-triple-only; **no** `busch_effect_gleason`. -/
theorem fs_moment_joint_dirichlet_N (p₀ : CPN (M + 1)) :
    Measure.map (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i)) (fubiniStudyMeasure p₀)
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by
  haveI : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  have hratio_meas : Measurable (ratioN (M := M)) := by
    unfold ratioN
    apply measurable_pi_lambda; intro k
    exact (measurable_pi_apply _).div
      (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i))
  have hmoment_meas : Measurable (fun p : CPN (M + 1) => fun i => momentMap p i) := by
    apply measurable_pi_lambda; intro i; exact momentMap_measurable i
  have hblock_meas : Measurable (fun y : (Fin (M + 1) × Fin 2) → ℝ =>
      fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2) := by
    apply measurable_pi_lambda; intro i; fun_prop
  rw [← ratioSqNorm_map_expHalf_pi, ← blockSqNormCurry_map_pi,
    Measure.map_map hratio_meas hblock_meas,
    ← gaussianCPN_eq_fubiniStudy p₀, gaussianCPN, gaussianHN,
    show (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i))
        = ratioN ∘ (fun p => fun i => momentMap p i) from rfl,
    Measure.map_map (hratio_meas.comp hmoment_meas) (measurable_gaussianProjN p₀),
    Measure.map_map ((hratio_meas.comp hmoment_meas).comp (measurable_gaussianProjN p₀))
      coordsN.continuous.measurable,
    ← map_pi_eq_stdGaussian,
    Measure.map_map (((hratio_meas.comp hmoment_meas).comp (measurable_gaussianProjN p₀)).comp
      coordsN.continuous.measurable) (by fun_prop)]
  refine Measure.map_congr ?_
  have hae : ∀ᵐ y ∂(Measure.pi (fun _ : Fin (M + 1) × Fin 2 => gaussianReal 0 1)),
      y ≠ (0 : (Fin (M + 1) × Fin 2) → ℝ) := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [show {a : (Fin (M + 1) × Fin 2) → ℝ | a = 0} = {(0 : (Fin (M + 1) × Fin 2) → ℝ)} from by
        ext a; simp]
    exact pi_gaussianReal_prod_singleton_zero
  filter_upwards [hae] with y hy
  simp only [Function.comp_apply]
  set v : EuclideanSpace ℂ (Fin (M + 1)) := coordsN (WithLp.toLp 2 y) with hvdef
  have hv0 : v ≠ 0 := by
    rw [hvdef]; intro h; apply hy
    have hz : (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (M + 1) × Fin 2)) = 0 :=
      coordsN.injective (by rw [h, map_zero])
    simpa using congrArg (WithLp.equiv 2 ((Fin (M + 1) × Fin 2) → ℝ)) hz
  rw [gaussianProjN, dif_neg hv0]
  -- Per-coordinate: `‖v i‖² = y(i,0)² + y(i,1)²`, and `∑ᵢ ‖v i‖² = ‖v‖²`.
  have hvival : ∀ i, ‖v i‖ ^ 2 = (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2 := by
    intro i
    have hvieq : v i = ((y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I) := rfl
    rw [hvieq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hsum : ∑ i, ((y (i, 0)) ^ 2 + (y (i, 1)) ^ 2) = ‖v‖ ^ 2 := by
    rw [euclidean_norm_sq_eq_sum]
    exact (Finset.sum_congr rfl (fun i _ => (hvival i).symm))
  -- The two ratio maps agree coordinatewise (both normalise to `‖v(castSucc k)‖²/‖v‖²`).
  funext k
  simp only [ratioN]
  rw [momentMap_mk v hv0 (Fin.castSucc k), momentMap_sum_eq_one (Projectivization.mk ℂ v hv0),
    div_one, ← hvival (Fin.castSucc k), ← hsum]

end LF4
end CSD
