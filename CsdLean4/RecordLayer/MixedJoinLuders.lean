/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MixedSwap
public import CsdLean4.RecordLayer.JoinClosure
public import CsdLean4.Mathlib.Probability.ConditionalProbability

/-!
# SigmaLayer/MixedJoinLuders: degenerate outcomes on mixed preparations (D3, first half)

**Category:** dynamical measurement — `specs/BACKLOG.md` **D3**'s first half: block Lüders
composed with Bayes, the degenerate counterpart of `MixedLuders.lean`, riding
`JoinClosure` exactly as that module's scope note predicted.

## What is proved

* `mixedJoinPrep` — the eigenvalue-weighted mixture of the pure join preparations at the
  spectral eigenvectors: two-stage sampling on the join arena, same shape as
  `mixedSwapPrep`.
* ★ `mixed_join_sector_born` — the mixed **block** Born rule: the mixture's mass on the
  outcome-`i` sector is `∑_{k : b k = i} Tr(ρ|eₖ⟩⟨eₖ|)` — the density-operator Born
  probability of the degenerate outcome, written as its rank-one sum. Spectral bridge:
  sum interchange + `spectral_born_eq_traceForm`, one rank-one bridge per block member.
* ★ `mixed_join_post_bayes` — conditioning the mixture on outcome `i` Bayes-updates the
  classical ignorance: component `j`'s posterior weight is `λⱼ · pᵢ|ⱼ / ∑ₖ…Tr(…)` with
  likelihood `pᵢ|ⱼ` the block Born weight of eigenvector `j`. Same engine as the rank-one
  case (`cond_finsetSum`).
* ★★ `mixed_join_luders` — **block Lüders composed with Bayes**: the outcome-conditioned
  post-measurement *system marginal* of the mixture is the Bayes-posterior mixture of the
  per-component degenerate Lüders posts `epistemicMeasure [Πᵢψⱼ]`. At rank ≥ 2 the
  posterior components are **genuinely distinct** — the record does *not* erase the
  classical ignorance (contrast `mixed_luders_followup`, where at rank one every posterior
  collapses to the same vertex): what survives conditioning is precisely the
  density-operator update `ρ ↦ Πᵢ ρ Πᵢ / Tr(ρ Πᵢ)`, realised as a mixture of the
  per-eigenvector block posts.

## ⚠️ Honest scope

* `mixed_join_luders` is stated under `hproj : ∀ j, blockProj b i ψⱼ ≠ 0` — every spectral
  component meets block `i`. A component with `Πᵢψⱼ = 0` has zero likelihood, hence zero
  Bayes weight, so nothing is *lost* — but its Lüders post `[Πᵢψⱼ]` does not exist as a
  ray, so the clean mixture statement needs the hypothesis. The refinement (sum over the
  components with nonzero block projection only) is bookkeeping over
  `mixed_join_post_bayes` and is deliberately left unstated rather than shipped as a
  weaker theorem wearing the same name.
* The spectral ensemble is the canonical mixture realisation; nothing depends on the
  choice (`MixedSwap.lean`). Per-protocol record facts hold under the mixture verbatim
  and are not restated (`JoinClosure`).

## References

`specs/BACKLOG.md` D3; `SigmaLayer/MixedLuders.lean` (the rank-one model this transports,
and whose scope note this discharges); `SigmaLayer/MixedSwap.lean` (`eigRay`,
`spectral_born_eq_traceForm`); `SigmaLayer/JoinClosure.lean` (`join_sector_born`);
`SigmaLayer/JoinLuders.lean` (`joinPrep`, `joinPostMarg`, `joinWitness_blockLuders`,
`sysRead`); `SigmaLayer/DegenerateLuders.lean` (`blockProj`);
`Mathlib/Probability/ConditionalProbability.lean` (`cond_finsetSum`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory CSD.LF2 CSD.SigmaLayer

variable {N K : ℕ} [NeZero N]

/-- **The mixed join preparation**: the eigenvalue-weighted mixture of the pure join
preparations at the spectral eigenvectors — two-stage sampling on the join arena. -/
noncomputable def mixedJoinPrep (ρ : DensityOperator N)
    (α : EuclideanSpace ℂ (Fin N)) : Measure (JoinSel N × LF4.KTorus) :=
  ∑ j, ENNReal.ofReal (ρ.isHermitian.eigenvalues j) •
    joinPrep (K := K) (ρ.isHermitian.eigenvectorBasis j) α (eigenvectorBasis_ne_zero' ρ j)

instance (ρ : DensityOperator N) (α : EuclideanSpace ℂ (Fin N)) :
    IsProbabilityMeasure (mixedJoinPrep (K := K) ρ α) := by
  constructor
  rw [mixedJoinPrep, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (eigenvalues_isProbability ρ).1 j),
    (eigenvalues_isProbability ρ).2, ENNReal.ofReal_one]

omit [NeZero N] in
/-- **The block spectral bridge**: the eigenvalue-weighted block Born weights of the
eigenvectors are the block sum of density-operator Born probabilities — sum interchange
plus one rank-one spectral bridge per block member. -/
lemma spectral_block_born_eq_traceForm (ρ : DensityOperator N) (b : Fin N → Fin K)
    (i : Fin K) :
    ∑ j, ρ.isHermitian.eigenvalues j
        * ∑ k ∈ Finset.univ.filter (fun k => b k = i),
            ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) (ρ.isHermitian.eigenvectorBasis j)‖ ^ 2
      = ∑ k ∈ Finset.univ.filter (fun k => b k = i),
          traceForm ρ (rankOneEffect (EuclideanSpace.single k (1 : ℂ))
            (single_norm_one' k)) := by
  rw [Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← spectral_born_eq_traceForm ρ k]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [eigRay, LF4.momentMap_mk_eq_inner_sq _ _ (eigenvectorBasis_norm_one ρ j) k]

/-- ★ **The mixed block Born rule**: the mixture's mass on the degenerate outcome-`i`
sector is the block sum `∑_{k : b k = i} Tr(ρ|eₖ⟩⟨eₖ|)` — the density-operator Born
probability of the coarse outcome, dynamically. Calibration-independent, as for the pure
case. -/
theorem mixed_join_sector_born (ρ : DensityOperator N) (b : Fin N → Fin K)
    (α : EuclideanSpace ℂ (Fin N)) (i : Fin K) :
    mixedJoinPrep (K := K) ρ α ((joinProtocol (N := N) b).outcomeSector i)
      = ENNReal.ofReal (∑ k ∈ Finset.univ.filter (fun k => b k = i),
          traceForm ρ (rankOneEffect (EuclideanSpace.single k (1 : ℂ))
            (single_norm_one' k))) := by
  rw [mixedJoinPrep, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => by
    rw [join_sector_born b _ α (eigenvectorBasis_ne_zero' ρ j)
      (eigenvectorBasis_norm_one ρ j) i]]
  rw [Finset.sum_congr rfl fun j _ =>
    (ENNReal.ofReal_mul ((eigenvalues_isProbability ρ).1 j)).symm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg ((eigenvalues_isProbability ρ).1 j)
      (Finset.sum_nonneg fun k _ => sq_nonneg _))]
  rw [spectral_block_born_eq_traceForm]

/-- ★ **Bayes updating on a degenerate outcome**: the outcome-conditioned post-measurement
ensemble of the mixed join preparation is the Bayes-posterior mixture of the per-component
post-ensembles — posterior weight `λⱼ · pᵢ|ⱼ / ∑ₖ Tr(ρ|eₖ⟩⟨eₖ|)` with likelihood `pᵢ|ⱼ`
the block Born weight of eigenvector `j`. -/
theorem mixed_join_post_bayes (ρ : DensityOperator N) (b : Fin N → Fin K)
    (α : EuclideanSpace ℂ (Fin N)) (i : Fin K) :
    (joinProtocol (N := N) b).postMeasure (mixedJoinPrep (K := K) ρ α) i
      = ∑ j, (ENNReal.ofReal (ρ.isHermitian.eigenvalues j
              * ∑ k ∈ Finset.univ.filter (fun k => b k = i),
                  ‖inner ℂ (EuclideanSpace.single k (1 : ℂ))
                    (ρ.isHermitian.eigenvectorBasis j)‖ ^ 2)
            / ENNReal.ofReal (∑ k ∈ Finset.univ.filter (fun k => b k = i),
                traceForm ρ (rankOneEffect (EuclideanSpace.single k (1 : ℂ))
                  (single_norm_one' k))))
          • (joinProtocol (N := N) b).postMeasure
              (joinPrep (K := K) (ρ.isHermitian.eigenvectorBasis j) α
                (eigenvectorBasis_ne_zero' ρ j)) i := by
  have hT : ∑ k, ENNReal.ofReal (ρ.isHermitian.eigenvalues k)
        * joinPrep (K := K) (ρ.isHermitian.eigenvectorBasis k) α
            (eigenvectorBasis_ne_zero' ρ k)
            ((joinProtocol (N := N) b).outcomeSector i)
      = ENNReal.ofReal (∑ k ∈ Finset.univ.filter (fun k => b k = i),
          traceForm ρ (rankOneEffect (EuclideanSpace.single k (1 : ℂ))
            (single_norm_one' k))) := by
    have h := mixed_join_sector_born ρ b α i
    rw [mixedJoinPrep, Measure.finsetSum_apply] at h
    simpa only [Measure.smul_apply, smul_eq_mul] using h
  ext A hA
  rw [MeasurementProtocol.postMeasure,
    Measure.map_apply ((joinProtocol b).measurable_evolve _ _) hA,
    MeasurementProtocol.selectedMeasure, mixedJoinPrep,
    ProbabilityTheory.cond_finsetSum Finset.univ _ _
      ((joinProtocol b).outcomeSector_measurable i)]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · rw [join_sector_born b _ α (eigenvectorBasis_ne_zero' ρ j)
      (eigenvectorBasis_norm_one ρ j) i, hT,
      ← ENNReal.ofReal_mul ((eigenvalues_isProbability ρ).1 j)]
  · rw [MeasurementProtocol.postMeasure, MeasurementProtocol.selectedMeasure,
      Measure.map_apply ((joinProtocol b).measurable_evolve _ _) hA]

/-- The outcome-conditioned post-measurement **system marginal** of the mixed join
preparation — `joinPostMarg`'s mixture counterpart, with the outcome-`i` calibration. -/
noncomputable def mixedJoinPostMarg (ρ : DensityOperator N) (b : Fin N → Fin K)
    (α : Fin K → EuclideanSpace ℂ (Fin N)) (i : Fin K) : Measure (LF4.KSigma N) :=
  Measure.map sysRead
    ((joinProtocol (N := N) b).postMeasure (mixedJoinPrep (K := K) ρ (α i)) i)

/-- ★★ **Block Lüders composed with Bayes** — D3's first half. After degenerate outcome
`i` on the mixed preparation, the post-measurement system marginal is the Bayes-posterior
mixture of the per-component **degenerate Lüders posts** `epistemicMeasure [Πᵢψⱼ]`. At
rank ≥ 2 these posteriors are genuinely distinct: the record does *not* erase the
classical ignorance, and what survives is exactly `ρ ↦ Πᵢ ρ Πᵢ / Tr(ρ Πᵢ)` realised as a
mixture. (Hypothesis `hproj`: every component meets block `i` — see the scope note.) -/
theorem mixed_join_luders (ρ : DensityOperator N) (b : Fin N → Fin K)
    (α : Fin K → EuclideanSpace ℂ (Fin N)) (hα : ∀ i, blockProj b i (α i) = α i)
    (i : Fin K)
    (hproj : ∀ j, blockProj b i (ρ.isHermitian.eigenvectorBasis j) ≠ 0) :
    mixedJoinPostMarg ρ b α i
      = ∑ j, (ENNReal.ofReal (ρ.isHermitian.eigenvalues j
              * ∑ k ∈ Finset.univ.filter (fun k => b k = i),
                  ‖inner ℂ (EuclideanSpace.single k (1 : ℂ))
                    (ρ.isHermitian.eigenvectorBasis j)‖ ^ 2)
            / ENNReal.ofReal (∑ k ∈ Finset.univ.filter (fun k => b k = i),
                traceForm ρ (rankOneEffect (EuclideanSpace.single k (1 : ℂ))
                  (single_norm_one' k))))
          • epistemicMeasure (Projectivization.mk ℂ
              (blockProj b i (ρ.isHermitian.eigenvectorBasis j)) (hproj j)) := by
  ext A hA
  rw [mixedJoinPostMarg, Measure.map_apply measurable_sysRead hA,
    mixed_join_post_bayes ρ b (α i) i]
  rw [Measure.finsetSum_apply, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply]
  congr 1
  have hmarg := joinWitness_blockLuders (b := b) α hα
    (ρ.isHermitian.eigenvectorBasis j) (eigenvectorBasis_ne_zero' ρ j) i (hproj j)
  rw [← hmarg, joinPostMarg, Measure.map_apply measurable_sysRead hA]

end CSD.RecordLayer
