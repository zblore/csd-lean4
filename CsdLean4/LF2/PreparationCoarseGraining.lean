/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.PreparationBarycenter
public import CsdLean4.Mathlib.QuantumInfo.Concavity

/-!
# Coarse-graining a preparation does not decrease its entropy

**Category:** 3-Local (W8 applied; the coarse-graining half of W4 in `specs/qit-chain-scoping.md`).

A preparation on `Σ` that is a mixture of preparations, `μ = ∑ᵢ cᵢ μᵢ`, has for its density
operator the mixture of the components' density operators, because the barycentre is affine in
the measure (`barycenterMatrix_finset_sum_smul`). Concavity of the von Neumann entropy
(`Mathlib/QuantumInfo/Concavity.lean`) then says:

* ★★ `vonNeumannEntropy_barycenter_mixture_ge`, ★★ `preparationEntropy_mixture_ge` — **the entropy
  of the mixed preparation is at least the weighted average of the entropies of the
  components.** Forgetting which component prepared the system (coarse-graining the preparation)
  costs entropy on average, never gains it.

Supporting: `isProbabilityMeasure_finset_sum_smul` (a mixture of probability measures with
weights summing to one is one), `map_finset_sum_smul` (pushforward is affine).

## Honest scope

Klein's full-support condition is inherited: the mixture's density operator is assumed positive
definite. The components are arbitrary preparations on `Σ`; "coarse-graining of regions" is the
case where the `μᵢ` are the conditional measures of a partition of a region and the `cᵢ` their
Liouville weights, which is one instance of this statement.

References: `specs/qit-chain-scoping.md` (W4, W8); `LF2/PreparationQdensity.lean` (W2);
`LF2/PreparationBarycenter.lean` (W3); `Mathlib/QuantumInfo/Concavity.lean`.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder ENNReal

/-! ### Coarse-graining a preparation does not decrease its entropy -/

namespace CSD
namespace LF2

variable {ι : Type*} [Fintype ι] {Q : Type*} [MeasurableSpace Q] {N : ℕ}

/-- The barycentre is affine in the measure: along a finite mixture `∑ᵢ cᵢ • μᵢ` of finite
measures it is the mixture of the barycentres. -/
theorem barycenterMatrix_finset_sum_smul (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (μ : ι → Measure Q) [∀ i, IsFiniteMeasure (μ i)] :
    barycenterMatrix rep (∑ i, ENNReal.ofReal (c i) • μ i)
      = ∑ i, ((c i : ℝ) : ℂ) • barycenterMatrix rep (μ i) := by
  ext j k
  simp only [barycenterMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_finsetSum_measure fun i _ =>
    (entryFn_integrable rep hrep_unit hrep_meas (μ i) j k).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hc i), Complex.real_smul]

/-- A finite mixture of probability measures with non-negative weights summing to one is a
probability measure. -/
theorem isProbabilityMeasure_finset_sum_smul (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∑ i, c i = 1)
    (μ : ι → Measure Q) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (c i) • μ i) := by
  refine ⟨?_⟩
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hc i), hc1, ENNReal.ofReal_one]

/-- ★★ **Coarse-graining does not decrease entropy, on average.** For preparations `μᵢ` on the
projective target with weights `pᵢ`, the entropy of the barycentre of the mixture is at least
the weighted average of the entropies of the barycentres of the components (Klein's full-support
condition on the mixture). Forgetting which component prepared the system costs entropy. -/
theorem vonNeumannEntropy_barycenter_mixture_ge (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∑ i, c i = 1)
    (μ : ι → Measure Q) [∀ i, IsProbabilityMeasure (μ i)]
    (hpd : (barycenterMatrix rep (∑ i, ENNReal.ofReal (c i) • μ i)).PosDef) :
    ∑ i, c i * vonNeumannEntropy (barycenterMatrix_isHermitian rep (μ i))
      ≤ vonNeumannEntropy hpd.1 := by
  have hmix := barycenterMatrix_finset_sum_smul rep hrep_unit hrep_meas c hc μ
  have hpd' : (∑ i, ((c i : ℝ) : ℂ) • barycenterMatrix rep (μ i)).PosDef := hmix ▸ hpd
  have h := vonNeumannEntropy_mixture_ge c hc hc1 (fun i => barycenterMatrix rep (μ i))
    (fun i => barycenterMatrix_posSemidef rep hrep_unit hrep_meas (μ i))
    (fun i => barycenterMatrix_trace rep hrep_unit hrep_meas (μ i)) hpd'
  rw [vonNeumannEntropy_congr_of_eq hpd.1 hpd'.1 hmix]
  exact h

/-- Pushing a finite mixture of measures forward is the mixture of the pushforwards. -/
theorem map_finset_sum_smul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (f : α → β)
    (hf : Measurable f) (c : ι → ℝ≥0∞) (μ : ι → Measure α) :
    Measure.map f (∑ i, c i • μ i) = ∑ i, c i • Measure.map f (μ i) := by
  rw [← Measure.mapₗ_apply_of_measurable hf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, Measure.mapₗ_apply_of_measurable hf]

section Preparation

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- ★★ **Coarse-graining a preparation on `Σ` does not decrease its entropy, on average** (W4's
second half). For preparations `μᵢ` on `Σ` mixed with weights `cᵢ`, the entropy of the mixed
preparation is at least the weighted average of the entropies of the components, under Klein's
full-support condition on the mixture's density operator. -/
theorem preparationEntropy_mixture_ge (D : SectorData SigmaSpace P G) (μFS : Measure P)
    [IsProbabilityMeasure μFS] (bridge : MeasureBridgeData D μFS)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∑ i, c i = 1)
    (μprep : ι → Measure SigmaSpace) [∀ i, IsProbabilityMeasure (μprep i)]
    (rep : P → EuclideanSpace ℂ (Fin N)) (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (hpd : (haveI := isProbabilityMeasure_finset_sum_smul c hc hc1 μprep
      preparationDensity D μFS bridge (∑ i, ENNReal.ofReal (c i) • μprep i) rep hrep_unit
        hrep_meas).M.PosDef) :
    haveI := isProbabilityMeasure_finset_sum_smul c hc hc1 μprep
    ∑ i, c i * preparationEntropy D μFS bridge (μprep i) rep hrep_unit hrep_meas
      ≤ preparationEntropy D μFS bridge (∑ i, ENNReal.ofReal (c i) • μprep i) rep hrep_unit
          hrep_meas := by
  have := isProbabilityMeasure_finset_sum_smul c hc hc1 μprep
  have hmap := map_finset_sum_smul D.π D.measurable_π (fun i => ENNReal.ofReal (c i)) μprep
  have hB : ∀ (ν : Measure SigmaSpace) [IsProbabilityMeasure ν],
      (preparationDensity D μFS bridge ν rep hrep_unit hrep_meas).M
        = barycenterMatrix rep (Measure.map D.π ν) := fun ν _ => by
    rw [preparationDensity_eq_barycenter]; rfl
  have hpd' : (barycenterMatrix rep (∑ i, ENNReal.ofReal (c i) • Measure.map D.π (μprep i))).PosDef := by
    have h := hpd
    rw [hB, hmap] at h
    exact h
  have : ∀ i, IsProbabilityMeasure (Measure.map D.π (μprep i)) :=
    fun i => isProbabilityMeasure_projectiveLaw D (μprep i)
  have key := vonNeumannEntropy_barycenter_mixture_ge rep hrep_unit hrep_meas c hc hc1
    (fun i => Measure.map D.π (μprep i)) hpd'
  unfold preparationEntropy
  rw [vonNeumannEntropy_congr_of_eq _ hpd'.1 (by rw [hB, hmap])]
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vonNeumannEntropy_congr_of_eq _ (barycenterMatrix_isHermitian rep _) (hB (μprep i))]

end Preparation

end LF2
end CSD
