/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.PreparationQdensity
public import CsdLean4.LF2.ReducedDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The barycentre: the density operator of a preparation is `∫ |ψ⟩⟨ψ| d(π_* μprep)`

**Category:** 3-Local (W3 of `specs/qit-chain-scoping.md`; the ontic identification of the
density operator W2 obtained as a Gleason witness).

W2 (`LF2/PreparationQdensity.lean`) gave every preparation on `Σ` a density operator
`preparationDensity`, characterised *uniquely by its trace form* — `effect_gleason_representation`
on `fromPreparation`. That characterisation says what the operator does, not what it is. This
module says what it is: **the barycentre of the rank-one projectors `|rep ψ⟩⟨rep ψ|` along the
projective law `π_* μprep`**, an entrywise Bochner integral. So the density operator of a
preparation is the ontic average of pure-state projectors over the preparation's projective
distribution — the object Papers C and TN2 write as `∫ |ψ⟩⟨ψ| ρ_ep(ψ) dμ_FS(ψ)`.

* `entryFn`, `barycenterMatrix` — the entry functions `ψ ↦ ψⱼ conj ψₖ` and their integrals;
* `barycenterMatrix_isHermitian`, `barycenterMatrix_trace`, `barycenterMatrix_posSemidef` — the
  barycentre against a probability measure is Hermitian, has trace one (`∑ⱼ |ψⱼ|² = ‖ψ‖² = 1`
  under the integral), and is positive semidefinite (its quadratic form at `u` is
  `∫ |⟨u, ψ⟩|²`, `dotProduct_barycenterMatrix_mulVec`);
* `barycenterDensity` — the barycentre packaged as a `DensityOperator`, and
  `barycenterDensity_traceForm` — its trace form against an effect is the integral of the effect
  function (`trace_barycenterMatrix_mul`: the trace of `B · E` is the integral of
  `tr(|ψ⟩⟨ψ| E)`, which `effectProjFn_eq_sum` expands entrywise);
* `preparationBarycenter` — the barycentre of a preparation on `Σ`, along `π_* μprep`;
* ★★ `preparationDensity_eq_barycenter` — **the identification**: `preparationDensity` (the
  Gleason witness) equals `preparationBarycenter`, by the uniqueness half of
  `effect_gleason_representation`;
* ★★ `preparationDensity_apply` — **entrywise**: `ρ_{jk} = ∫ ψⱼ conj ψₖ d(π_* μprep)(ψ)`;
* ★ `preparationDensity_apply_rnDeriv` — **the `ρ_ep` form**: when `π_* μprep ≪ μFS`, with
  `ρ_ep` its Radon–Nikodym derivative, `ρ_{jk} = ∫ ρ_ep(ψ) ψⱼ conj ψₖ dμFS(ψ)`.

## Honest scope

⚠️ **The `ρ_ep` form takes absolute continuity as a hypothesis.** For region preparations in the
`SigmaLayer` interface it is a theorem (`SigmaLayer/PreparationDensity.lean`,
`projectivePreparationLaw_withDensity`); the two preparation interfaces (`SigmaLayer.Preparation`
with a `ProjectiveSector`, and `LF2.SectorData` with a `MeasureBridgeData`) are not yet identified
with each other, so that theorem is not composed here. The barycentre identification itself
(`preparationDensity_eq_barycenter`) needs no such hypothesis.

⚠️ **Same posits as W2.** The sector is posited (`specs/POSITS.md` Posit 2); what is proved is
that, given it, the density operator of a preparation is the barycentre.

References: `specs/qit-chain-scoping.md` (W3); `LF2/PreparationQdensity.lean` (W2);
`LF2/EffectGleason.lean` (`effect_gleason_representation`, `trace_mul_outerProduct`);
`LF2/Preparation.lean` (`fromPreparation`, `effectProjFn_integrable`).
-/

@[expose] public section

open MeasureTheory Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ} {ι : Type*} [Fintype ι] {Q : Type*} [MeasurableSpace Q]

/-! ### The barycentre of rank-one projectors, over any finite index -/
/-- The entry function `p ↦ (rep p)ⱼ · conj (rep p)ₖ` of the rank-one projector `|rep p⟩⟨rep p|`. -/
noncomputable def entryFn (rep : Q → EuclideanSpace ℂ ι) (j k : ι) (p : Q) : ℂ :=
  (rep p) j * star ((rep p) k)

/-- The entrywise barycentre of the rank-one projectors `|rep p⟩⟨rep p|` against `μ`. -/
noncomputable def barycenterMatrix (rep : Q → EuclideanSpace ℂ ι) (μ : Measure Q) :
    Matrix ι ι ℂ :=
  Matrix.of fun j k => ∫ p, entryFn rep j k p ∂μ

/-- Each coordinate of a unit vector has modulus at most `1`. -/
theorem norm_coord_le_one (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (j : ι) :
    ‖v j‖ ≤ 1 := hv ▸ PiLp.norm_apply_le v j

omit [Fintype ι] in
/-- The coordinate map `p ↦ (rep p) j` is measurable. -/
theorem measurable_coord (rep : Q → EuclideanSpace ℂ ι) (hrep_meas : Measurable rep)
    (j : ι) : Measurable fun p => (rep p) j :=
  (measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 (ι → ℂ)).comp hrep_meas)

omit [Fintype ι] in
theorem measurable_entryFn (rep : Q → EuclideanSpace ℂ ι) (hrep_meas : Measurable rep)
    (j k : ι) : Measurable (entryFn rep j k) :=
  (measurable_coord rep hrep_meas j).mul (continuous_star.measurable.comp (measurable_coord rep hrep_meas k))

/-- The entry functions are integrable: measurable and bounded by `1`. -/
theorem entryFn_integrable (rep : Q → EuclideanSpace ℂ ι) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (μ : Measure Q) [IsFiniteMeasure μ] (j k : ι) :
    Integrable (entryFn rep j k) μ := by
  refine Integrable.of_bound (measurable_entryFn rep hrep_meas j k).aestronglyMeasurable 1 ?_
  refine ae_of_all _ fun p => ?_
  unfold entryFn
  rw [norm_mul, norm_star]
  calc ‖(rep p) j‖ * ‖(rep p) k‖ ≤ 1 * 1 :=
        mul_le_mul (norm_coord_le_one _ (hrep_unit p) j) (norm_coord_le_one _ (hrep_unit p) k)
          (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! ### The barycentre is a density operator -/

omit [Fintype ι] in
/-- The barycentre is Hermitian: conjugating an entry integral conjugates the integrand, and
`conj ((rep p)ₖ conj (rep p)ⱼ) = (rep p)ⱼ conj (rep p)ₖ`. -/
theorem barycenterMatrix_isHermitian (rep : Q → EuclideanSpace ℂ ι) (μ : Measure Q) :
    (barycenterMatrix rep μ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun j k => ?_
  simp only [barycenterMatrix, Matrix.of_apply]
  rw [← starRingEnd_apply, ← integral_conj]
  congr 1
  funext p
  rw [starRingEnd_apply]
  unfold entryFn
  rw [star_mul, star_star]

omit [MeasurableSpace Q] in
/-- The diagonal entries of `|v⟩⟨v|` sum to `‖v‖² = 1`. -/
theorem sum_entryFn_diag (rep : Q → EuclideanSpace ℂ ι) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (p : Q) : ∑ j, entryFn rep j j p = 1 := by
  have h : ∑ j, entryFn rep j j p = ((‖rep p‖ ^ 2 : ℝ) : ℂ) := by
    rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold entryFn
    rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, hrep_unit p, one_pow, Complex.ofReal_one]

/-- The barycentre against a probability measure has trace one. -/
theorem barycenterMatrix_trace (rep : Q → EuclideanSpace ℂ ι)
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsProbabilityMeasure μ] : (barycenterMatrix rep μ).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag_apply, barycenterMatrix, Matrix.of_apply]
  rw [← integral_finsetSum _ (fun j _ => entryFn_integrable rep hrep_unit hrep_meas μ j j)]
  simp_rw [sum_entryFn_diag rep hrep_unit]
  simp

omit [MeasurableSpace Q] in
/-- Pointwise: the quadratic form of `|rep p⟩⟨rep p|` at `u` is `|⟨u, rep p⟩|²`, expanded. -/
theorem normSq_dotProduct_eq_sum (rep : Q → EuclideanSpace ℂ ι) (u : ι → ℂ) (p : Q) :
    ((Complex.normSq (star u ⬝ᵥ ⇑(rep p)) : ℝ) : ℂ)
      = ∑ j, ∑ k, star (u j) * (entryFn rep j k p * u k) := by
  rw [← Complex.mul_conj, starRingEnd_apply, ← star_dotProduct_star, star_star]
  simp only [dotProduct, Pi.star_apply, Finset.sum_mul_sum, entryFn]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The quadratic form of the barycentre at `u` is the integral of `|⟨u, rep p⟩|²`. -/
theorem dotProduct_barycenterMatrix_mulVec (rep : Q → EuclideanSpace ℂ ι)
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsFiniteMeasure μ] (u : ι → ℂ) :
    star u ⬝ᵥ (barycenterMatrix rep μ *ᵥ u)
      = ∫ p, ((Complex.normSq (star u ⬝ᵥ ⇑(rep p)) : ℝ) : ℂ) ∂μ := by
  simp_rw [normSq_dotProduct_eq_sum]
  simp only [dotProduct, mulVec, barycenterMatrix, Matrix.of_apply, Pi.star_apply]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    ((entryFn_integrable rep hrep_unit hrep_meas μ j k).mul_const _).const_mul _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ =>
    ((entryFn_integrable rep hrep_unit hrep_meas μ j k).mul_const _).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- The barycentre is positive semidefinite: its quadratic form is an integral of `|⟨u, ψ⟩|²`. -/
theorem barycenterMatrix_posSemidef (rep : Q → EuclideanSpace ℂ ι)
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsFiniteMeasure μ] : (barycenterMatrix rep μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (barycenterMatrix_isHermitian rep μ) fun u => ?_
  rw [dotProduct_barycenterMatrix_mulVec rep hrep_unit hrep_meas μ u, integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun p => Complex.normSq_nonneg _)

/-- **The barycentre density operator, index-parametric**: `∫ |rep p⟩⟨rep p| dμ(p)` as a
`DensityOperatorIx ι` (the structure partial traces live on). -/
noncomputable def barycenterDensityIx [DecidableEq ι] (rep : Q → EuclideanSpace ℂ ι)
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsProbabilityMeasure μ] : DensityOperatorIx ι where
  M := barycenterMatrix rep μ
  isHermitian := barycenterMatrix_isHermitian rep μ
  nonneg := barycenterMatrix_posSemidef rep hrep_unit hrep_meas μ
  trace_one := barycenterMatrix_trace rep hrep_unit hrep_meas μ

/-! ### The `Fin N` case: trace form against effects, and the `DensityOperator N` packaging -/

omit [MeasurableSpace Q] in
/-- The effect function is the real part of `tr(|rep p⟩⟨rep p| · E)`, and that trace is real
(both factors Hermitian), so as a complex number it IS the trace — expanded entrywise:
`∑ⱼₖ (rep p)ⱼ conj (rep p)ₖ E ₖⱼ`. -/
theorem effectProjFn_eq_sum (rep : Q → EuclideanSpace ℂ (Fin N)) (E : Effect N) (p : Q) :
    ((effectProjFn rep E p : ℝ) : ℂ)
      = ∑ j, ∑ k, entryFn rep j k p * E.M k j := by
  -- the quadratic form is the trace of `E · |v⟩⟨v|` (`trace_mul_outerProduct`), real by Hermiticity
  have htr : star (⇑(rep p) : Fin N → ℂ) ⬝ᵥ E.M *ᵥ ⇑(rep p)
      = (E.M * outerProduct (rep p)).trace := (trace_mul_outerProduct E.M (rep p)).symm
  have hreal : (E.M * outerProduct (rep p)).trace.im = 0 :=
    Complex.conj_eq_iff_im.mp (trace_mul_isHermitian_real E.isHermitian (outerProduct_isHermitian _))
  have h1 : ((effectProjFn rep E p : ℝ) : ℂ) = (E.M * outerProduct (rep p)).trace := by
    unfold effectProjFn
    rw [htr]
    exact Complex.ext (by simp) (by simp [hreal])
  rw [h1, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct, Matrix.vecMulVec_apply,
    entryFn]

/-- The trace form of the barycentre against an effect is the integral of the effect function. -/
theorem trace_barycenterMatrix_mul (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsFiniteMeasure μ] (E : Effect N) :
    (barycenterMatrix rep μ * E.M).trace = ∫ p, ((effectProjFn rep E p : ℝ) : ℂ) ∂μ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, barycenterMatrix, Matrix.of_apply]
  simp_rw [effectProjFn_eq_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    (entryFn_integrable rep hrep_unit hrep_meas μ j k).mul_const _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => (entryFn_integrable rep hrep_unit hrep_meas μ j k).mul_const _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const]

/-- **The barycentre density operator** `∫ |rep p⟩⟨rep p| dμ(p)` of a unit-norm measurable
representative against a probability measure. -/
noncomputable def barycenterDensity (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsProbabilityMeasure μ] : DensityOperator N where
  M := barycenterMatrix rep μ
  isHermitian := barycenterMatrix_isHermitian rep μ
  nonneg := barycenterMatrix_posSemidef rep hrep_unit hrep_meas μ
  trace_one := barycenterMatrix_trace rep hrep_unit hrep_meas μ

/-- The trace form of the barycentre density operator is the integral of the effect function. -/
theorem barycenterDensity_traceForm (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsProbabilityMeasure μ] (E : Effect N) :
    traceForm (barycenterDensity rep hrep_unit hrep_meas μ) E = ∫ p, effectProjFn rep E p ∂μ := by
  unfold traceForm barycenterDensity
  rw [trace_barycenterMatrix_mul rep hrep_unit hrep_meas μ E, integral_complex_ofReal]
  exact Complex.ofReal_re _

/-! ### The identification: the density operator of a preparation IS its barycentre -/

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

variable (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
  (bridge : MeasureBridgeData D μFS)
  (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
  (rep : P → EuclideanSpace ℂ (Fin N))
  (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)

/-- The projective law `π_* μprep` of a preparation is a probability measure. -/
theorem isProbabilityMeasure_projectiveLaw : IsProbabilityMeasure (Measure.map D.π μprep) :=
  Measure.isProbabilityMeasure_map' D.measurable_π.aemeasurable

/-- **The barycentre of a preparation**: `∫ |rep ψ⟩⟨rep ψ| d(π_* μprep)(ψ)`, packaged as a density
operator. -/
noncomputable def preparationBarycenter : DensityOperator N :=
  haveI := isProbabilityMeasure_projectiveLaw D μprep
  barycenterDensity rep hrep_unit hrep_meas (Measure.map D.π μprep)

/-- ★★ **The density operator of a preparation IS its barycentre.** The Gleason witness of
`fromPreparation` (W2) and the Bochner integral of the rank-one projectors along the projective law
have the same trace form, so by `effect_gleason_representation`'s uniqueness they are equal. -/
theorem preparationDensity_eq_barycenter :
    preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas
      = preparationBarycenter D μprep rep hrep_unit hrep_meas := by
  have := isProbabilityMeasure_projectiveLaw D μprep
  refine (preparation_qdensity_unique D μFS bridge μprep rep hrep_unit hrep_meas).unique
    (preparation_traceForm D μFS bridge μprep rep hrep_unit hrep_meas) fun E => ?_
  exact (barycenterDensity_traceForm rep hrep_unit hrep_meas (Measure.map D.π μprep) E).symm

/-- ★★ **Entrywise**: `ρ_{jk} = ∫ ψⱼ conj ψₖ d(π_* μprep)(ψ)`. -/
theorem preparationDensity_apply (j k : Fin N) :
    (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).M j k
      = ∫ p, (rep p) j * star ((rep p) k) ∂(Measure.map D.π μprep) := by
  rw [preparationDensity_eq_barycenter]
  rfl

/-- ★ **The `ρ_ep` form.** When the projective law is absolutely continuous with respect to the
reference measure `μFS` — `ρ_ep := d(π_* μprep)/dμFS` its Radon–Nikodym derivative — the density
operator is `∫ |ψ⟩⟨ψ| ρ_ep(ψ) dμFS(ψ)` entrywise. -/
theorem preparationDensity_apply_rnDeriv (habs : Measure.map D.π μprep ≪ μFS) (j k : Fin N) :
    (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).M j k
      = ∫ p, ((Measure.map D.π μprep).rnDeriv μFS p).toReal • ((rep p) j * star ((rep p) k)) ∂μFS := by
  have := isProbabilityMeasure_projectiveLaw D μprep
  have h := integral_withDensity_eq_integral_toReal_smul (μ := μFS)
    (Measure.measurable_rnDeriv (Measure.map D.π μprep) μFS)
    (Measure.rnDeriv_lt_top (Measure.map D.π μprep) μFS)
    (fun p => (rep p) j * star ((rep p) k))
  rw [Measure.withDensity_rnDeriv_eq _ _ habs] at h
  rw [preparationDensity_apply]
  exact h

end LF2
end CSD
