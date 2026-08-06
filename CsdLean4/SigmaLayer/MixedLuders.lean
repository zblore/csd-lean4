/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.MixedSwap
public import CsdLean4.SigmaLayer.SwapLuders
public import CsdLean4.Mathlib.Probability.ConditionalProbability

/-!
# SigmaLayer/MixedLuders: the outcome-conditioned mixed update

**Category:** dynamical measurement — `MixedSwap.lean`'s recorded extension, delivered
(the fourth external review's "mixed conditioned update" row).

Two theorems close the row:

★ **`mixed_post_bayes`** — the outcome-conditioned post-measurement ensemble of a mixed
preparation is the **Bayes-posterior mixture** of the per-eigenray post-ensembles: the
posterior weight of spectral component `j` after outcome `i` is
`λⱼ · pᵢ|ⱼ / Tr(ρ|eᵢ⟩⟨eᵢ|)` with likelihood `pᵢ|ⱼ = momentMap [ψⱼ] i` — classical Bayes
updating of classical ignorance, as a theorem about the protocol's `postMeasure`. The
engine is the new staged `ProbabilityTheory.cond_finsetSum` (Bayes for finite mixtures).

★★ **`mixed_luders_followup`** — **the record, not the pedigree, fixes the post-state**:
after outcome `i` on the mixed preparation, follow-up statistics in every context are
`c'.rate [eᵢ]` — exactly the pure preparation's rank-one Lüders update. At rank one the
posterior components all collapse to the same vertex state, so classical ignorance of the
preparation is *erased* by the record: the conditioned mixture behaves as a fresh
preparation of `eᵢ`. This is the density-operator update `ρ ↦ Πᵢ ρ Πᵢ / Tr(ρ Πᵢ)` at rank
one, dynamically.

The spine: `mixedSwapPrep` **factors** — the mixture lives entirely on the system-and-
register factor, with the calibrated bank common (`mixedSwapPrep_eq_prod`), so the pure
theorem `swap_luders_born` (already stated for an arbitrary probability preparation)
applies verbatim once the outcome has nonzero mixed Born weight (`mixed_outcome_pos`,
licensed by `Tr(ρ|eᵢ⟩⟨eᵢ|) ≠ 0` through the spectral bridge — no measure hypothesis).

⚠️ **Honest scope.** ~~Degenerate outcomes on mixtures (block-Lüders composed with Bayes)
would ride `JoinClosure` the same way and are not restated~~ **delivered 2026-08-06**
(`SigmaLayer/MixedJoinLuders.lean`, BACKLOG D3 first half): it rides `JoinClosure`
exactly as predicted, and at rank ≥ 2 the posterior components are proven genuinely
distinct — `mixed_join_luders` exhibits the conditioned mixture as the Bayes mixture of
the per-component block posts `epistemicMeasure [Πᵢψⱼ]`, nothing collapsing to a vertex.
The spectral ensemble is the canonical mixture realisation; nothing here depends on the
choice (`MixedSwap.lean`).

## References

`specs/BACKLOG.md` (the outcome-conditioned mixed update row — this discharges it; fourth
external review 2026-08-03); `SigmaLayer/MixedSwap.lean` (`mixedSwapPrep`, `eigRay`,
`spectral_born_eq_traceForm`, `mixed_swap_sector_born`), `SigmaLayer/SwapClosure.lean`
(`swapPrep`, `readyPrep`, `calibratedBank`, `prep_outcome_pos`, `swap_sector_born`),
`SigmaLayer/SwapLuders.lean` (`swap_luders_born`),
`CsdLean4/Mathlib/Probability/ConditionalProbability.lean` (`cond_finsetSum`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory CSD.LF2 CSD.SigmaLayer

variable {N : ℕ} [NeZero N]

/-! ### The mixture factors through the bank -/

/-- The mixed system-and-register preparation: the eigenvalue mixture of the pure ready
preparations — the bank is not part of the ignorance. -/
noncomputable def mixedReadyPrep (ρ : DensityOperator N) :
    Measure (LF4.KSigma N × LF4.KTorus) :=
  ∑ j, ENNReal.ofReal (ρ.isHermitian.eigenvalues j) • readyPrep (eigRay ρ j)

instance (ρ : DensityOperator N) : IsProbabilityMeasure (mixedReadyPrep ρ) := by
  constructor
  rw [mixedReadyPrep, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (eigenvalues_isProbability ρ).1 j),
    (eigenvalues_isProbability ρ).2, ENNReal.ofReal_one]

/-- **The mixed preparation factors**: the mixture lives on the system-and-register
factor, with the calibrated bank common to every spectral component. This is what lets
every pure-preparation theorem stated for an arbitrary `μ12` apply to mixtures
verbatim. -/
lemma mixedSwapPrep_eq_prod (ρ : DensityOperator N) :
    mixedSwapPrep ρ = (mixedReadyPrep ρ).prod (calibratedBank N) := by
  rw [mixedReadyPrep, ← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    mixedSwapPrep]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.prod_smul_left]
  rfl

/-- **`hpos` is a theorem for mixtures**: nonzero mixed Born weight `Tr(ρ|eᵢ⟩⟨eᵢ|) ≠ 0`
gives the outcome sector nonzero mixed measure — through the spectral bridge, some
component has both nonzero eigenvalue and nonzero pure Born weight, and
`prep_outcome_pos` does the rest. -/
theorem mixed_outcome_pos (ρ : DensityOperator N) (i : Fin N)
    (hpos : traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
      (single_norm_one' i)) ≠ 0) :
    mixedReadyPrep ρ ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0 := by
  have hsum : ∑ j, ρ.isHermitian.eigenvalues j * LF4.momentMap (eigRay ρ j) i ≠ 0 := by
    rw [spectral_born_eq_traceForm]
    exact hpos
  have hex : ∃ j, ρ.isHermitian.eigenvalues j * LF4.momentMap (eigRay ρ j) i ≠ 0 := by
    by_contra h
    exact hsum (Finset.sum_eq_zero fun j _ => not_not.mp (not_exists.mp h j))
  obtain ⟨j, hj⟩ := hex
  have hlam : ρ.isHermitian.eigenvalues j ≠ 0 := fun h => hj (by rw [h, zero_mul])
  have hmom : LF4.momentMap (eigRay ρ j) i ≠ 0 := fun h => hj (by rw [h, mul_zero])
  intro h0
  rw [mixedReadyPrep, Measure.finsetSum_apply] at h0
  simp only [Measure.smul_apply, smul_eq_mul] at h0
  have hzero := (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ j)
  refine absurd hzero (mul_ne_zero ?_ (prep_outcome_pos (eigRay ρ j) i hmom))
  rw [ENNReal.ofReal_ne_zero_iff]
  exact lt_of_le_of_ne ((eigenvalues_isProbability ρ).1 j) (Ne.symm hlam)

/-! ### ★ The Bayes-posterior ensemble -/

/-- ★ **The outcome-conditioned mixed post-measurement ensemble is the Bayes-posterior
mixture**: after outcome `i`, spectral component `j` carries posterior weight
`λⱼ · pᵢ|ⱼ / Tr(ρ|eᵢ⟩⟨eᵢ|)` — prior times likelihood over evidence — and the ensemble is
that mixture of the per-eigenray post-ensembles. Classical Bayes updating of the
classical ignorance, as a theorem about the protocol. -/
theorem mixed_post_bayes (ρ : DensityOperator N) (i : Fin N) :
    (swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).postMeasure (mixedSwapPrep ρ) i
      = ∑ j, (ENNReal.ofReal (ρ.isHermitian.eigenvalues j * LF4.momentMap (eigRay ρ j) i)
            / ENNReal.ofReal (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
                (single_norm_one' i))))
          • (swapProtocol (basinIndex (momentContext N))
              (measurable_basinIndex (momentContext N))).postMeasure
                (swapPrep (eigRay ρ j)) i := by
  have hT : ∑ k, ENNReal.ofReal (ρ.isHermitian.eigenvalues k)
        * swapPrep (eigRay ρ k) ((swapProtocol (basinIndex (momentContext N))
            (measurable_basinIndex (momentContext N))).outcomeSector i)
      = ENNReal.ofReal (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
          (single_norm_one' i))) := by
    have h := mixed_swap_sector_born ρ i
    rw [mixedSwapPrep, Measure.finsetSum_apply] at h
    simpa only [Measure.smul_apply, smul_eq_mul] using h
  ext A hA
  rw [MeasurementProtocol.postMeasure,
    Measure.map_apply ((swapProtocol _ _).measurable_evolve _ _) hA,
    MeasurementProtocol.selectedMeasure, mixedSwapPrep,
    ProbabilityTheory.cond_finsetSum Finset.univ _ _
      ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector_measurable i)]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · rw [swap_sector_born (eigRay ρ j) i, hT,
      ← ENNReal.ofReal_mul ((eigenvalues_isProbability ρ).1 j)]
  · rw [MeasurementProtocol.postMeasure, MeasurementProtocol.selectedMeasure,
      Measure.map_apply ((swapProtocol _ _).measurable_evolve _ _) hA]

/-! ### ★★ The record fixes the post-state -/

/-- ★★ **The record, not the pedigree, fixes the post-state**: after outcome `i` on the
*mixed* preparation, follow-up statistics in every context are exactly the pure rank-one
Lüders update's — `c'.rate [eᵢ]`. At rank one every Bayes-posterior component collapses
to the same vertex state, so the record erases the classical ignorance of the
preparation: the conditioned mixture is dynamically indistinguishable from a fresh
preparation of `eᵢ`. The density-operator update `ρ ↦ Πᵢ ρ Πᵢ / Tr(ρ Πᵢ)` at rank one. -/
theorem mixed_luders_followup (ρ : DensityOperator N) (i : Fin N)
    (hpos : traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
      (single_norm_one' i)) ≠ 0)
    (c' : ContextField N) (j : Fin N) :
    ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).postMeasure (mixedSwapPrep ρ) i)
      ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j) := by
  rw [mixedSwapPrep_eq_prod]
  exact swap_luders_born (mixedReadyPrep ρ) i (mixed_outcome_pos ρ i hpos) c' j

end CSD.RecordLayer
