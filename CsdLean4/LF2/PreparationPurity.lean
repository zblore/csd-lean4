/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.PreparationBarycenter
public import CsdLean4.Mathlib.QuantumInfo.PureState
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitSection

/-!
# A preparation has zero entropy iff it is pure

**Category:** 3-Local (W4 of `specs/qit-chain-scoping.md`, the `= 0 ↔ pure` half).

W2 gave a preparation on `Σ` a von Neumann entropy (`preparationEntropy`, non-negative, at most
`log N`); W3 made its density operator the barycentre of the rank-one projectors along the
projective law. This module says when the entropy vanishes:

* `vonNeumannEntropy_eq_zero_iff_outerProduct` — the matrix-level characterisation
  (`Mathlib/QuantumInfo/PureState.lean`) in `outerProduct` form;
* `trace_outerProduct_mul_barycenterMatrix` — the overlap functional of a unit vector against a
  barycentre is the integral of the squared overlap;
* ★ `ae_outerProduct_eq_of_barycenterMatrix_eq` — **a barycentre is a projector only if the law
  sits on one ray**: if `∫ |rep p⟩⟨rep p| dμ = |φ⟩⟨φ|` then almost every `rep p` lies on the ray
  of `φ` (the squared overlap integrates to one and is at most one, so it is one almost
  everywhere, the equality case of Cauchy–Schwarz);
* `mk_eq_mk_of_outerProduct_eq`, `eq_dirac_of_ae_eq` — two unit vectors with one projector span
  one ray; a probability measure concentrated on a point is the Dirac mass;
* ★★ `preparationEntropy_eq_zero_iff` — **a preparation has zero entropy iff its projective law is
  a Dirac mass at a single ray**, with the canonical measurable unit section
  (`Projectivization.unitSection`) as representative.

## Honest scope

"Pure" here means the projective law of the preparation is concentrated on one ray. That is the
operational notion (the density operator is a rank-one projector); it says nothing about the
ontic preparation measure `μprep` itself beyond what its projection sees, and it is stated with
the canonical section so that "the representative of the ray" is a definite object. The
coarse-graining half of W4 (entropy is monotone under coarse-graining of regions) needs W8
(concavity) and is not here.

References: `specs/qit-chain-scoping.md` (W4); `LF2/PreparationQdensity.lean` (W2);
`LF2/PreparationBarycenter.lean` (W3); `Mathlib/QuantumInfo/PureState.lean`;
`Mathlib/LinearAlgebra/Projectivization/UnitSection.lean`.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder LinearAlgebra.Projectivization

/-! ### Preparations of zero entropy are pure -/

namespace CSD
namespace LF2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `outerProduct` form of `vonNeumannEntropy_eq_zero_iff`. -/
theorem vonNeumannEntropy_eq_zero_iff_outerProduct {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    vonNeumannEntropy hρ.1 = 0 ↔ ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ ρ = outerProduct ψ := by
  rw [vonNeumannEntropy_eq_zero_iff hρ htr]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    refine ⟨WithLp.toLp 2 ψ, ?_, rfl⟩
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 ψ)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    simp only [hψ, RCLike.one_re] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 ψ)]
  · rintro ⟨ψ, hψ, rfl⟩
    refine ⟨⇑ψ, ?_, rfl⟩
    rw [dotProduct_comm]
    exact dotProduct_self_star_of_unit_norm ψ hψ

variable {Q : Type*} [MeasurableSpace Q] {N : ℕ}

/-- The overlap functional of a fixed unit vector against a barycentre is the integral of the
squared overlap. -/
theorem trace_outerProduct_mul_barycenterMatrix (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsFiniteMeasure μ] (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (barycenterMatrix rep μ * outerProduct φ).trace
      = ((∫ p, ‖inner ℂ (rep p) φ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have h := trace_barycenterMatrix_mul rep hrep_unit hrep_meas μ (rankOneEffect φ hφ)
  simp only [effectProjFn_rankOne rep φ hφ] at h
  rw [integral_complex_ofReal] at h
  exact h

/-- **A barycentre is a projector only if the projective law sits on one ray.** If the barycentre
of `|rep p⟩⟨rep p|` along a probability measure is `|φ⟩⟨φ|`, then `μ`-almost every `rep p` lies on
the ray of `φ`: the squared overlap integrates to one and is at most one (Cauchy–Schwarz), so it is
one almost everywhere, which is the equality case. -/
theorem ae_outerProduct_eq_of_barycenterMatrix_eq (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (μ : Measure Q) [IsProbabilityMeasure μ] (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1)
    (h : barycenterMatrix rep μ = outerProduct φ) :
    ∀ᵐ p ∂μ, outerProduct (rep p) = outerProduct φ := by
  have h1 := trace_outerProduct_mul_barycenterMatrix rep hrep_unit hrep_meas μ φ hφ
  rw [h, outerProduct_mul_self_of_unit_norm φ hφ, outerProduct_trace_of_unit_norm φ hφ] at h1
  have hint : ∫ p, ‖inner ℂ (rep p) φ‖ ^ 2 ∂μ = 1 := by exact_mod_cast h1.symm
  -- the deficit 1 - |<rep p, φ>|^2 is non-negative, integrable, and integrates to zero
  have hle : ∀ p, ‖inner ℂ (rep p) φ‖ ^ 2 ≤ 1 := fun p => by
    have := norm_inner_le_norm (𝕜 := ℂ) (rep p) φ
    rw [hrep_unit p, hφ, one_mul] at this
    nlinarith [norm_nonneg (inner ℂ (rep p) φ)]
  have hint2 : Integrable (fun p => ‖inner ℂ (rep p) φ‖ ^ 2) μ := by
    have := effectProjFn_integrable rep hrep_unit hrep_meas (rankOneEffect φ hφ) μ
    rw [show effectProjFn rep (rankOneEffect φ hφ) = fun p => ‖inner ℂ (rep p) φ‖ ^ 2 from
      funext (effectProjFn_rankOne rep φ hφ)] at this
    exact this
  have hzero : ∫ p, (1 - ‖inner ℂ (rep p) φ‖ ^ 2) ∂μ = 0 := by
    rw [integral_sub (integrable_const _) hint2, hint]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg (fun p => sub_nonneg.mpr (hle p))
    ((integrable_const _).sub hint2)).mp hzero
  refine hae.mono fun p hp => ?_
  have hp' : ‖inner ℂ (rep p) φ‖ = 1 := by
    have : ‖inner ℂ (rep p) φ‖ ^ 2 = 1 := by
      have := hp; simp only [Pi.zero_apply] at this; linarith
    nlinarith [norm_nonneg (inner ℂ (rep p) φ)]
  -- equality in Cauchy–Schwarz: φ = r • rep p with ‖r‖ = 1
  have hne : rep p ≠ 0 := norm_ne_zero_iff.mp (by rw [hrep_unit p]; exact one_ne_zero)
  have hφne : φ ≠ 0 := norm_ne_zero_iff.mp (by rw [hφ]; exact one_ne_zero)
  obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hne hφne).mp
    (by rw [hp', hrep_unit p, hφ, one_mul])
  have hrn : ‖r‖ = 1 := by
    have := congrArg norm hr
    rw [norm_smul, hrep_unit p, mul_one, hφ] at this
    exact this.symm
  rw [hr, outerProduct_smul_of_norm_one hrn]

/-- Two unit vectors with the same projector span the same ray. -/
theorem mk_eq_mk_of_outerProduct_eq {ψ φ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h : outerProduct ψ = outerProduct φ) :
    Projectivization.mk ℂ ψ (norm_ne_zero_iff.mp (by rw [hψ]; exact one_ne_zero))
      = Projectivization.mk ℂ φ (norm_ne_zero_iff.mp (by rw [hφ]; exact one_ne_zero)) := by
  have hψne : ψ ≠ 0 := norm_ne_zero_iff.mp (by rw [hψ]; exact one_ne_zero)
  have hφne : φ ≠ 0 := norm_ne_zero_iff.mp (by rw [hφ]; exact one_ne_zero)
  -- the overlap is one: Tr(|ψ⟩⟨ψ| |φ⟩⟨φ|) = Tr(|φ⟩⟨φ|²) = 1
  have htr := outerProduct_mul_outerProduct_trace ψ φ
  rw [h, outerProduct_mul_self_of_unit_norm φ hφ, outerProduct_trace_of_unit_norm φ hφ] at htr
  have hsq : ‖inner ℂ ψ φ‖ ^ 2 = 1 := by exact_mod_cast htr.symm
  have hov : ‖inner ℂ ψ φ‖ = 1 := by nlinarith [norm_nonneg (inner ℂ ψ φ)]
  obtain ⟨r, hr0, hr⟩ := (norm_inner_eq_norm_iff hψne hφne).mp (by rw [hov, hψ, hφ, one_mul])
  symm
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨r, hr.symm⟩

/-- **A probability measure concentrated on a point is the Dirac mass.** -/
theorem eq_dirac_of_ae_eq {P : Type*} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    {q : P} (h : ∀ᵐ p ∂μ, p = q) : μ = Measure.dirac q := by
  have : Measure.map id μ = Measure.map (fun _ => q) μ := Measure.map_congr h
  rw [Measure.map_id, Measure.map_const, measure_univ, one_smul] at this
  exact this

/-! ### The preparation-level statement -/

section Preparation

variable {SigmaSpace G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]
  [MulAction.IsPretransitive G (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]

/-- ★★ **A preparation has zero entropy iff it is pure.** For a preparation on the projective sector,
with the canonical measurable unit section as representative, the von Neumann entropy of its
density operator vanishes iff its projective law is a Dirac mass at a single ray: zero entropy
forces the barycentre to be a rank-one projector, which forces almost every ray of the preparation
to be that projector's ray, which forces the law to be the Dirac mass there; conversely the
barycentre along a Dirac mass is the projector of its ray. -/
theorem preparationEntropy_eq_zero_iff
    (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin N))) G)
    (μFS : Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N)))) [IsProbabilityMeasure μFS]
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep] :
    preparationEntropy D μFS bridge μprep Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.measurable_unitSection = 0
      ↔ ∃ q, Measure.map D.π μprep = Measure.dirac q := by
  have hP := isProbabilityMeasure_projectiveLaw D μprep
  have hB : (preparationDensity D μFS bridge μprep Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.measurable_unitSection).M
      = barycenterMatrix Projectivization.unitSection (Measure.map D.π μprep) := by
    rw [preparationDensity_eq_barycenter]; rfl
  unfold preparationEntropy
  constructor
  · intro hS
    obtain ⟨φ, hφ, hM⟩ := (vonNeumannEntropy_eq_zero_iff_outerProduct
      (preparationDensity_posSemidef D μFS bridge μprep _ _ _)
      (preparationDensity_trace_one D μFS bridge μprep _ _ _)).mp hS
    rw [hB] at hM
    have hae := ae_outerProduct_eq_of_barycenterMatrix_eq Projectivization.unitSection
      Projectivization.norm_unitSection Projectivization.measurable_unitSection
      (Measure.map D.π μprep) φ hφ hM
    have hφne : φ ≠ 0 := norm_ne_zero_iff.mp (by rw [hφ]; exact one_ne_zero)
    refine ⟨Projectivization.mk ℂ φ hφne, eq_dirac_of_ae_eq _ (hae.mono fun p hp => ?_)⟩
    calc p = Projectivization.mk ℂ (Projectivization.unitSection p)
          (Projectivization.unitSection_ne_zero p) := (Projectivization.mk_unitSection p).symm
      _ = Projectivization.mk ℂ φ hφne :=
          mk_eq_mk_of_outerProduct_eq (Projectivization.norm_unitSection p) hφ hp
  · rintro ⟨q, hq⟩
    have hM : barycenterMatrix Projectivization.unitSection (Measure.map D.π μprep)
        = outerProduct (Projectivization.unitSection q) := by
      rw [hq]
      ext j k
      simp only [barycenterMatrix, Matrix.of_apply]
      rw [integral_dirac]
      rfl
    exact (vonNeumannEntropy_eq_zero_iff_outerProduct
      (preparationDensity_posSemidef D μFS bridge μprep _ _ _)
      (preparationDensity_trace_one D μFS bridge μprep _ _ _)).mpr
      ⟨Projectivization.unitSection q, Projectivization.norm_unitSection q, hB.trans hM⟩

end Preparation

end LF2
end CSD
