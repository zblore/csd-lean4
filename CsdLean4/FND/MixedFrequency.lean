import CsdLean4.FND.MixedOntic
import CsdLean4.LF4.BornFrequencyPartition

/-!
# FND/MixedFrequency: the mixed-state Born FREQUENCY on the unified model (#8 C, a.s. limit)

**Category:** 7-FND (the Choice A ontology layer).

`FiniteQMClosure.mixed_born` (`mixed_ontic_born_weight`) delivers the mixed Born content at the WEIGHT
level: the spectral-ensemble mixture of ontic Born-region measures equals `Tr(ρ Eᵢ)`. This module upgrades
it to a genuine almost-sure FREQUENCY limit — a **two-stage sampling process**: each shot draws a spectral
component `j` of `ρ` with probability `λⱼ` (its eigenvalue), then an ontic microstate from the unified
model's Liouville measure `μL`; the outcome is the pointer readout for the drawn component's eigenvector.
The frequency of outcome `i` over the trials converges a.s. to `Tr(ρ Eᵢ)`.

* `eigenvalueMeasure ρ` — the eigenvalue probability distribution as a measure on the component index;
* `mixtureMeasure` — the two-stage law `eigenvalueMeasure ⊗ μL` on `Fin(M+1) × Σ`;
* `mixtureRegion ρ i` — the outcome-`i` region `⋃ⱼ {j} × π⁻¹(bornRegion(eⱼ) i)`;
* `mixtureMeasure_region_toReal` — `μmix(mixtureRegion i) = Tr(ρ Eᵢ)` (the two-stage region measure IS the
  density-operator Born weight, via `mixed_ontic_born_weight`);
* `unified_mixed_born_frequency` — the a.s. frequency limit, by `born_frequency_convergence_partition`.

So the unified model carries mixed-state Born statistics as certified FREQUENCIES, not only as weights —
closing the last open QM item in `FiniteQMClosure` (its Tier-4 "mixed-state frequency LLN").

References: `FND/MixedOntic.lean` (`mixed_ontic_born_weight`), `FND/MixedEnsemble.lean`
(`eigenvalues_isProbability`), `LF4/BornFrequencyPartition.lean` (the general partition LLN).
-/

open MeasureTheory
open scoped ComplexOrder ENNReal

namespace CSD.FND

open CSD.LF2 CSD.LF4

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (M + 1))

/-- The single-outcome ontic Born region of `ρ`'s `j`-th eigenvector, pulled back through `π`. -/
noncomputable def eigRegion (ρ : DensityOperator (M + 1)) (j i : Fin (M + 1)) : Set (KSigma (M + 1)) :=
  (productSector H hH p₀).pi ⁻¹' bornRegion (ρ.isHermitian.eigenvectorBasis j) (eigenvectorBasis_ne_zero ρ j) i

theorem eigRegion_measurable (ρ : DensityOperator (M + 1)) (j i : Fin (M + 1)) :
    MeasurableSet (eigRegion H hH p₀ ρ j i) :=
  (bornRegion_measurable_uncond _ _ i).preimage (productSector H hH p₀).measurable_pi

/-- **The eigenvalue distribution as a probability measure** on the component index `Fin (M+1)`:
`∑ⱼ λⱼ · δⱼ`. -/
noncomputable def eigenvalueMeasure (ρ : DensityOperator (M + 1)) : Measure (Fin (M + 1)) :=
  ∑ j, ENNReal.ofReal (ρ.isHermitian.eigenvalues j) • Measure.dirac j

theorem eigenvalueMeasure_singleton (ρ : DensityOperator (M + 1)) (k : Fin (M + 1)) :
    eigenvalueMeasure ρ {k} = ENNReal.ofReal (ρ.isHermitian.eigenvalues k) := by
  rw [eigenvalueMeasure, Measure.finsetSum_apply]
  simp [Measure.dirac_apply, Set.indicator_apply, Finset.sum_ite_eq']

instance eigenvalueMeasure_isProbability (ρ : DensityOperator (M + 1)) :
    IsProbabilityMeasure (eigenvalueMeasure ρ) := by
  refine ⟨?_⟩
  rw [eigenvalueMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ _),
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => ρ.nonneg.eigenvalues_nonneg j),
    (eigenvalues_isProbability ρ).2, ENNReal.ofReal_one]

/-- **The two-stage mixture measure** on `Fin(M+1) × Σ`: draw a spectral component `~ λ`, then an ontic
microstate `~ μL`. -/
noncomputable def mixtureMeasure (ρ : DensityOperator (M + 1)) :
    Measure (Fin (M + 1) × KSigma (M + 1)) :=
  (eigenvalueMeasure ρ).prod ((productDynamics H hH p₀).muL)

/-- **The mixed outcome-`i` region:** component `j`'s eigenvector lands in the `i`-th ontic Born region. -/
def mixtureRegion (ρ : DensityOperator (M + 1)) (i : Fin (M + 1)) :
    Set (Fin (M + 1) × KSigma (M + 1)) :=
  ⋃ j, {j} ×ˢ eigRegion H hH p₀ ρ j i

theorem mixtureRegion_measurable (ρ : DensityOperator (M + 1)) (i : Fin (M + 1)) :
    MeasurableSet (mixtureRegion H hH p₀ ρ i) :=
  MeasurableSet.iUnion fun j =>
    (measurableSet_singleton j).prod (eigRegion_measurable H hH p₀ ρ j i)

/-- **The two-stage region measure IS the density-operator Born weight.** `μmix(mixtureRegion i).toReal =
Tr(ρ Eᵢ)`. The mixture measure of the disjoint rectangle union is `∑ⱼ λⱼ · μL(eigRegion j i)`, which is the
`mixed_ontic_born_weight` sum. -/
theorem mixtureMeasure_region_toReal (ρ : DensityOperator (M + 1)) (i : Fin (M + 1)) :
    (mixtureMeasure H hH p₀ ρ (mixtureRegion H hH p₀ ρ i)).toReal
      = traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one i)) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun j => ({j} ×ˢ eigRegion H hH p₀ ρ j i : Set (Fin (M + 1) × KSigma (M + 1))))) := by
    intro a b hab
    apply Set.disjoint_left.2
    rintro ⟨x, y⟩ hx hy
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hx hy
    exact hab (hx.1.symm.trans hy.1)
  have hrect : ∀ j, mixtureMeasure H hH p₀ ρ ({j} ×ˢ eigRegion H hH p₀ ρ j i)
      = ENNReal.ofReal (ρ.isHermitian.eigenvalues j)
        * ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1))) (eigRegion H hH p₀ ρ j i) := by
    intro j
    rw [mixtureMeasure, Measure.prod_prod, eigenvalueMeasure_singleton]
  rw [mixtureRegion,
    measure_iUnion hdisj (fun j => (measurableSet_singleton j).prod (eigRegion_measurable H hH p₀ ρ j i)),
    tsum_fintype]
  simp only [hrect]
  rw [ENNReal.toReal_sum (fun j _ => by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  rw [← mixed_ontic_born_weight H hH p₀ ρ i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ρ.nonneg.eigenvalues_nonneg j), eigRegion]

/-- **Mixed-state Born FREQUENCY on the unified model (#8 C, a.s. limit).** For i.i.d. two-stage trials `Y`
(draw a spectral component of `ρ ~ λ`, then an ontic microstate `~ μL`) whose law is `mixtureMeasure`, the
frequency of outcome `i` — the drawn component's eigenvector landing in the `i`-th ontic Born region —
converges almost surely to the density-operator Born weight `Tr(ρ Eᵢ)`. So the unified model
`productDynamics H hH p₀` carries mixed-state Born statistics as certified frequencies, not only weights. -/
theorem unified_mixed_born_frequency (ρ : DensityOperator (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (Y : ℕ → Ω → Fin (M + 1) × KSigma (M + 1)) (hY : ∀ n, Measurable (Y n))
    (hlaw : ∀ n, Measure.map (Y n) Pr = mixtureMeasure H hH p₀ ρ)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
        (fun n => Set.indicator ((Y n) ⁻¹' mixtureRegion H hH p₀ ρ i) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Filter.Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((Y k) ⁻¹' mixtureRegion H hH p₀ ρ i) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        Filter.atTop
        (nhds (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one i)))) :=
  born_frequency_convergence_partition (mixtureRegion H hH p₀ ρ)
    (mixtureRegion_measurable H hH p₀ ρ)
    (fun i => traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one i)))
    (mixtureMeasure_region_toReal H hH p₀ ρ) Y hY hlaw hindep

end CSD.FND
