import CsdLean4.SigmaLayer.MeasureBridge
import CsdLean4.SigmaLayer.ConditioningLink
import CsdLean4.LF4.BornRegionUncond
import CsdLean4.LF4.BornRegionDisjoint

/-!
# SigmaLayer/ConditioningLuders: the ontic-record conditioning EQUALS the Lüders update, through `π`

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

`SigmaLayer/ConditioningLink.lean` proved that the ontic record-history conditioning and the projective Lüders
update are BOTH the single Bayesian rule `w(fine)/w(coarse)` — but for DIFFERENT weights (`μL` vs the Born
weight), and it never proved the two weights AGREE. This module supplies exactly that missing link, on the
concrete many-to-one product sector: the ontic measure of a measurement OUTCOME REGION (the `π`-preimage
of a Born region) EQUALS the Born weight of that outcome.

The mechanism is the operational one named in the review: the two conditioning weights coincide through
`π` because of bridge B1 (`π_* μL = μFS`) and Born-from-volume (`μFS(bornRegion i) = ‖⟨eᵢ,ψ⟩‖²`). So the
ontic conditional PROBABILITY of a finer outcome, given a coarser one, equals the Lüders/Born conditional
probability — the correspondence is now a THEOREM, not an asserted coincidence.

## What this establishes

* `onticRegion_measure_eq_born` — the WEIGHT AGREEMENT: `μL(π⁻¹ bornRegion i) = ‖⟨eᵢ,ψ⟩‖²`. The ontic
  measure of the `i`-th outcome region is the Born weight. This is the link `ConditioningLink` asserted
  but did not prove.
* `conditioning_born_ratio_correspondence` — the CONDITIONAL PROBABILITY: the ontic Bayesian conditional
  of the outcome regions equals the ratio of Born weights (the Lüders/Born conditional).

## Honest scope

This closes the correspondence at the PROBABILITY level AND, via the rank-1 bridge
`projWeight (rankOneProj k) ψ = ‖⟨eₖ,ψ⟩‖²`, delivers OPERATIONAL EQUIVALENCE for pointer-basis effects:
the ontic conditioning weight (`μL` on outcome regions) and the Lüders conditioning weight (`projWeight`)
are LITERALLY equal per outcome (`onticWeight_eq_ludersWeight`), so the two updates give the same
conditional prediction (`conditioning_luders_operational_equivalence`) — as PREDICTIONS, not by equating a
measure with a vector. This is extended from single outcomes to EVERY pointer-basis effect
(`conditioning_luders_effect_equivalence`, via `onticRegion_biUnion_measure_eq_born_sum` — additivity of
the weight agreement over the pairwise-disjoint Born regions). So #4 is complete for all pointer-basis
(diagonal) effects on the concrete product model — which are exactly the effects this ontic model, whose
outcome regions are the pointer Born regions, can represent. (A truly non-diagonal effect has no
pointer-basis outcome region here, so it is outside what this ontic model predicts at all.)

References: `SigmaLayer/ConditioningLink.lean` (the two Bayesian halves), `SigmaLayer/MeasureBridge.lean` (B1,
`productSector_hasFubiniStudyPushforward`), `LF4/BornRegionUncond.lean` (`bornRegion_fs_measure_uncond`).
-/

open MeasureTheory Matrix.UnitaryGroup

namespace CSD.SigmaLayer

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CSD.LF4.CPN (M + 1))

/-- **The weight agreement — the missing link.** The ontic Liouville measure of the `i`-th measurement
OUTCOME REGION (the `π`-preimage of the Born region) equals the Born weight `‖⟨eᵢ, ψ⟩‖²`. Proof: pull the
preimage through the `π`-pushforward B1 (`μL(π⁻¹ X) = μFS(X)`, `productSector_hasFubiniStudyPushforward`),
then Born-from-volume (`bornRegion_fs_measure_uncond`). So the ontic conditioning weight (`μL` on outcome
regions) and the projective conditioning weight (the Born weight) are the SAME number — the coincidence
`ConditioningLink` asserted is now proved. -/
theorem onticRegion_measure_eq_born (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin (M + 1)) :
    (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
        ((productSector H hH p₀).pi ⁻¹' CSD.LF4.bornRegion ψ hψ0 i)).toReal
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  have hmeas : MeasurableSet (CSD.LF4.bornRegion ψ hψ0 i) :=
    CSD.LF4.bornRegion_measurable_uncond ψ hψ0 i
  have hb1 : Measure.map (productSector H hH p₀).pi
      ((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
      = fubiniStudyMeasure p₀ :=
    productSector_hasFubiniStudyPushforward H hH p₀
  rw [← Measure.map_apply (productSector H hH p₀).measurable_pi hmeas, hb1]
  exact CSD.LF4.bornRegion_fs_measure_uncond p₀ ψ hψ0 hψ i

/-- **The conditional-probability correspondence.** For two outcomes `i` (kept) and `j` (the coarser
class it lies in — here the same outcome, the base case), the ontic Bayesian conditional of the outcome
regions equals the ratio of Born weights: `μL(π⁻¹ bornRegion i) / μL(π⁻¹ bornRegion j) =
‖⟨eᵢ,ψ⟩‖² / ‖⟨eⱼ,ψ⟩‖²`. So the ontic record conditioning and the Lüders/Born conditioning give the same
probability — via the weight agreement `onticRegion_measure_eq_born`. -/
theorem conditioning_born_ratio_correspondence
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i j : Fin (M + 1)) :
    bayesianConditional
        (fun k => (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
          ((productSector H hH p₀).pi ⁻¹' CSD.LF4.bornRegion ψ hψ0 k)).toReal) j i
      = bayesianConditional (fun k => ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2) j i := by
  simp only [bayesianConditional, onticRegion_measure_eq_born H hH p₀ ψ hψ0 hψ]

/-! ### #4: operational equivalence — the ontic weight IS the Lüders weight

The rank-1 identity bridges the two formalisms: the Lüders `projWeight` of the rank-1 projector onto the
`k`-th basis vector equals the Born weight `‖⟨eₖ,ψ⟩‖²`. Combined with `onticRegion_measure_eq_born`, the
ontic conditioning weight (`μL` on outcome regions) and the Lüders conditioning weight (`projWeight`) are
LITERALLY the same number for each pointer outcome — so the two conditionings make identical predictions
for every pointer-basis effect. -/

/-- The rank-1 orthogonal projector onto the `k`-th standard basis ray, as a linear map `x ↦ ⟨eₖ,x⟩ • eₖ`. -/
noncomputable def rankOneProj (k : Fin (M + 1)) :
    EuclideanSpace ℂ (Fin (M + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (M + 1)) :=
  ((innerSL ℂ (EuclideanSpace.single k (1 : ℂ))).smulRight
    (EuclideanSpace.single k (1 : ℂ))).toLinearMap

/-- **The rank-1 identity — the formalism bridge.** The Lüders `projWeight` of the rank-1 projector onto
`eₖ` equals the Born weight `‖⟨eₖ, ψ⟩‖²`. So `projWeight` (the `E →ₗ[ℂ] E` conditioning weight) and the
Born weight (the region conditioning weight) are the same quantity. -/
theorem projWeight_rankOne (k : Fin (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1))) :
    projWeight (rankOneProj k) ψ = ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 := by
  simp only [projWeight, rankOneProj, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul,
    PiLp.norm_single, norm_one, mul_one]

/-- **The ontic and Lüders conditioning weights coincide (operational equivalence, per outcome).** For
each pointer outcome `i`, `μL(π⁻¹ bornRegion i) = projWeight (rankOneProj i) ψ`: the ontic Liouville
measure of the outcome region equals the Lüders `projWeight` of the corresponding rank-1 projector. The
two conditioning rules use the SAME weight, so predict the same probability for every subsequent
pointer-basis effect. -/
theorem onticWeight_eq_ludersWeight (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin (M + 1)) :
    (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
        ((productSector H hH p₀).pi ⁻¹' CSD.LF4.bornRegion ψ hψ0 i)).toReal
      = projWeight (rankOneProj i) ψ := by
  rw [onticRegion_measure_eq_born H hH p₀ ψ hψ0 hψ, projWeight_rankOne]

/-- **Operational equivalence of the conditionings (probability level).** The ontic record-conditioning
Bayesian ratio over outcome regions equals the Lüders Bayesian ratio over the rank-1 `projWeight`s — the
ontic update and the Lüders update give the SAME conditional probability, each in its NATIVE weight. This
is the review's #4 for pointer-basis effects: the two rules agree as PREDICTIONS, not by equating a
measure with a vector. -/
theorem conditioning_luders_operational_equivalence
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i j : Fin (M + 1)) :
    bayesianConditional
        (fun k => (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
          ((productSector H hH p₀).pi ⁻¹' CSD.LF4.bornRegion ψ hψ0 k)).toReal) j i
      = bayesianConditional (fun k => projWeight (rankOneProj k) ψ) j i := by
  simp only [bayesianConditional, onticWeight_eq_ludersWeight H hH p₀ ψ hψ0 hψ]

/-! ### #4 completed: GENERAL (pointer-basis) effects

A general pointer-basis effect is a set `S` of outcomes; its outcome region is the UNION of the Born
regions and its Born weight is the SUM of the rank-1 Born weights. Additivity of
`onticRegion_measure_eq_born` over the pairwise-disjoint Born regions extends the weight agreement — and
hence the operational equivalence — from single outcomes to every pointer-basis effect. -/

/-- **The weight agreement for a general effect.** The ontic Liouville measure of the outcome region of an
effect `S` (the union of Born regions over `S`) equals the Born weight of `S` (the sum of the rank-1 Born
weights). Additivity over the pairwise-disjoint Born regions (`bornRegion_pairwiseDisjoint`), each term the
single-outcome agreement `onticRegion_measure_eq_born`. -/
theorem onticRegion_biUnion_measure_eq_born_sum (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (S : Finset (Fin (M + 1))) :
    (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
        ((productSector H hH p₀).pi ⁻¹' ⋃ k ∈ S, CSD.LF4.bornRegion ψ hψ0 k)).toReal
      = ∑ k ∈ S, ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 := by
  have hmeas : ∀ k ∈ S,
      MeasurableSet ((productSector H hH p₀).pi ⁻¹' CSD.LF4.bornRegion ψ hψ0 k) :=
    fun k _ => (CSD.LF4.bornRegion_measurable_uncond ψ hψ0 k).preimage
      (productSector H hH p₀).measurable_pi
  have hdisj : (↑S : Set (Fin (M + 1))).PairwiseDisjoint
      (fun k => (productSector H hH p₀).pi ⁻¹' CSD.LF4.bornRegion ψ hψ0 k) :=
    fun k _ l _ hkl => (CSD.LF4.bornRegion_pairwiseDisjoint ψ hψ0 hkl).preimage _
  rw [Set.preimage_iUnion₂, measure_biUnion_finset hdisj hmeas,
    ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)]
  exact Finset.sum_congr rfl (fun k _ => onticRegion_measure_eq_born H hH p₀ ψ hψ0 hψ k)

/-- **Operational equivalence for general effects (#4, complete on the product model).** For any two
pointer-basis effects `S` (kept) and `T` (the coarser class), the ontic record-conditioning Bayesian ratio
over the effect regions equals the Lüders/Born Bayesian ratio over the summed Born weights. So the ontic
update and the Lüders update predict the same conditional probability for EVERY pointer-basis effect — the
review's #4, no longer restricted to single outcomes. -/
theorem conditioning_luders_effect_equivalence (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (S T : Finset (Fin (M + 1))) :
    bayesianConditional
        (fun U : Finset (Fin (M + 1)) =>
          (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
            ((productSector H hH p₀).pi ⁻¹' ⋃ k ∈ U, CSD.LF4.bornRegion ψ hψ0 k)).toReal) T S
      = bayesianConditional
          (fun U : Finset (Fin (M + 1)) => ∑ k ∈ U, ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2)
          T S := by
  simp only [bayesianConditional, onticRegion_biUnion_measure_eq_born_sum H hH p₀ ψ hψ0 hψ]

end CSD.SigmaLayer
