/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapClosure
public import CsdLean4.SigmaLayer.MixedEnsemble

/-!
# SigmaLayer/MixedSwap: mixed preparations in the dynamical model

**Category:** dynamical measurement — the recorded "mixed preparations" extension of the
swap closure.

A mixed preparation is, ontically, a **two-stage sampling**: draw a spectral index `j` with
probability `λⱼ` (the eigenvalue), then prepare the pure eigenray `[ψⱼ]` and run the
measurement dynamics unchanged. This module makes that the definition —

  `mixedSwapPrep ρ = ∑ⱼ λⱼ • swapPrep [ψⱼ]`

— a probability measure on the swap arena because the eigenvalues are a probability
distribution (`eigenvalues_isProbability`), and derives the mixed dynamical Born rule:

★ **`mixed_swap_sector_born`** — the mixed preparation's mass on the outcome sector of the
measurement protocol is exactly the density-operator Born probability:

  `mixedSwapPrep ρ (outcomeSector i) = Tr(ρ |eᵢ⟩⟨eᵢ|)`.

The dynamics is untouched: the same propagator, the same sectors, the same protocol. What
mixing adds is *classical ignorance of the preparation*, and the theorem says the dynamical
outcome statistics respond exactly as `Tr(ρ ·)` demands — the spectral bridge is
`spectral_born_eq_traceForm`, composing the ontic sector weights (`swap_sector_born`, one
per eigenray) with the affine Born rule of the spectral ensemble
(`traceForm_eq_pureEnsemble`).

⚠️ **Honest scope.** Record creation, exclusivity, persistence, and no-record-when-ready
are *per-protocol* facts independent of the preparation — they hold under `mixedSwapPrep`
verbatim and are not restated. The i.i.d. frequency layer consumes a probability measure
and an event and applies as everywhere (`arena_mixed_born_frequency` is the two-stage LLN
precedent on the unified arena). The **conditional** post-measurement analysis of a mixture
— Bayes-updating the ensemble weights on the outcome and composing with the rank-one Lüders
posts — ~~is a recorded extension, not claimed here~~ *delivered 2026-08-03:
`RecordLayer/MixedLuders.lean` (`mixed_post_bayes`, `mixed_luders_followup`)*. The spectral decomposition is the
canonical ensemble; the mixture realisation is of course not unique (`density_isPureEnsemble`
states existence, not uniqueness), and nothing here depends on the choice.

## References

`specs/BACKLOG.md` (the mixed-preparations row — this discharges it);
`RecordLayer/SwapClosure.lean` (`swapPrep`, `swap_sector_born`),
`SigmaLayer/MixedEnsemble.lean` (`eigenvalues_isProbability`, `traceForm_eq_pureEnsemble`),
`SigmaLayer/MixedOntic.lean` (the kinematic counterpart, `mixed_ontic_born_weight`),
`LF2/BornWrapper.lean` (`born_quadratic`, `rankOneEffect`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory CSD.LF2 CSD.SigmaLayer
open scoped LinearAlgebra.Projectivization

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- Unit standard-basis vectors, at every dimension. -/
lemma single_norm_one' (i : Fin N) : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by
  rw [PiLp.norm_single, norm_one]

omit [NeZero N] in
/-- The eigenvectors of a density operator are nonzero, at every dimension. -/
lemma eigenvectorBasis_ne_zero' (ρ : DensityOperator N) (j : Fin N) :
    ρ.isHermitian.eigenvectorBasis j ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [eigenvectorBasis_norm_one ρ j]; norm_num)

/-- The `j`-th spectral eigenray of a density operator. -/
noncomputable def eigRay (ρ : DensityOperator N) (j : Fin N) : LF4.CPN N :=
  Projectivization.mk ℂ (ρ.isHermitian.eigenvectorBasis j) (eigenvectorBasis_ne_zero' ρ j)

/-- **The mixed preparation**: the eigenvalue-weighted mixture of the pure swap
preparations at the spectral eigenrays — two-stage sampling as a measure. -/
noncomputable def mixedSwapPrep (ρ : DensityOperator N) :
    Measure (SwapArena (LF4.KSigma N) N) :=
  ∑ j, ENNReal.ofReal (ρ.isHermitian.eigenvalues j) • swapPrep (eigRay ρ j)

instance (ρ : DensityOperator N) : IsProbabilityMeasure (mixedSwapPrep ρ) := by
  constructor
  rw [mixedSwapPrep, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (eigenvalues_isProbability ρ).1 j),
    (eigenvalues_isProbability ρ).2, ENNReal.ofReal_one]

omit [NeZero N] in
/-- **The spectral bridge**: the eigenvalue-weighted moment-map weights of the eigenrays
are the density-operator Born probability. -/
lemma spectral_born_eq_traceForm (ρ : DensityOperator N) (i : Fin N) :
    ∑ j, ρ.isHermitian.eigenvalues j * LF4.momentMap (eigRay ρ j) i
      = traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one' i)) := by
  rw [traceForm_eq_pureEnsemble]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [eigRay, LF4.momentMap_mk_eq_inner_sq _ _ (eigenvectorBasis_norm_one ρ j) i,
    born_quadratic (ρ.isHermitian.eigenvectorBasis j) (EuclideanSpace.single i (1 : ℂ))
      (eigenvectorBasis_norm_one ρ j) (single_norm_one' i)]
  have hnorm : ‖(inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (ρ.isHermitian.eigenvectorBasis j) : ℂ)‖
      = ‖(inner ℂ (ρ.isHermitian.eigenvectorBasis j)
          (EuclideanSpace.single i (1 : ℂ)) : ℂ)‖ := by
    rw [← inner_conj_symm (ρ.isHermitian.eigenvectorBasis j)
      (EuclideanSpace.single i (1 : ℂ)), RCLike.norm_conj]
  rw [hnorm]

/-- ★ **The mixed dynamical Born rule**: the mixed preparation's mass on the measurement
protocol's outcome sector is exactly `Tr(ρ |eᵢ⟩⟨eᵢ|)` — the same propagator, the same
sectors, with classical ignorance of the preparation responding precisely as the
density-operator Born rule demands. -/
theorem mixed_swap_sector_born (ρ : DensityOperator N) (i : Fin N) :
    mixedSwapPrep ρ
        ((swapProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).outcomeSector i)
      = ENNReal.ofReal
          (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
            (single_norm_one' i))) := by
  rw [mixedSwapPrep, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => by rw [swap_sector_born (eigRay ρ j) i]]
  rw [Finset.sum_congr rfl fun j _ =>
    (ENNReal.ofReal_mul ((eigenvalues_isProbability ρ).1 j)).symm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg ((eigenvalues_isProbability ρ).1 j) (LF4.momentMap_nonneg _ i))]
  rw [spectral_born_eq_traceForm]

end CSD.RecordLayer
