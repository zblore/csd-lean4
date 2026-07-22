/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.MomentBornN

/-!
# LF4 §14: observable correspondence for diagonal observables (general N)

**Category:** 3-Local (LF4 §14 discharge — the general-N, all-eigenvalue observable correspondence
for observables diagonal in the reference basis).

This module discharges the §14 **observable-correspondence** obligation for **diagonal**
self-adjoint observables `A = diagonal (lam ·)` on `Σ = ℂℙ^{N-1}`, at **general N** and for
**every real eigenvalue vector** `lam` — the general lift of `LF4/SingleQubitKahler.lean`'s
single-qubit projector result `sg_observable_correspondence`.

## What §14 means, and what is discharged here

The §14 obligation (see `BRIDGE-OBLIGATIONS.md`, `LF4-todo §14`) asks that each self-adjoint
Hilbert observable arise as the lift of a **measurable `Σ`-valued function** whose `Σ`-average is
the Hilbert expectation. For a diagonal observable this is delivered here:

* **`diag_expectation`** — the Hilbert side: `⟨ψ, diagonal(lam·) ψ⟩ = ∑ₖ lam k · ‖⟨e_k, ψ⟩‖²`
  (spectral expansion + the standard-basis Born weights).
* **`fsMeasure_bornRegionN`** — the ontic side: the Fubini–Study volume of the moment-sublevel
  region `bornRegionN ψ k` on `Σ` equals the Born weight `‖⟨e_k, ψ⟩‖²`, for **every** basis index
  `k : Fin N`. This unifies `fs_born_volume_ratio_N` (free coordinates) and
  `fs_born_volume_ratio_N_apex` (the apex coordinate) via `Fin.lastCases`.
* **`observable_correspondence_diagonal`** — the pointwise-volume form:
  `⟨ψ, diagonal(lam·) ψ⟩ = ∑ₖ lam k · vol(bornRegionN ψ k)`, i.e. the expectation is the
  eigenvalue-weighted sum of the ontic Born-region volumes.
* **`observable_correspondence_diagonal_integral`** — the canonical integral form
  `⟨ψ, diagonal(lam·) ψ⟩ = ∫ A_ontic dμ_FS`, with `A_ontic = ∑ₖ lam k · 𝟙_{Rₖ}` (`aOntic`) an
  explicit **measurable** `Σ`-function (`bornRegionN_measurableSet`), and the integral evaluated by
  finite additivity over the eigenvalue-weighted region indicators.

## Scope (honest)

**Diagonal observables only.** The reference-basis Born regions `bornRegionN ψ k` realise the
**standard-basis** projectors `|e_k⟩⟨e_k|`; an observable whose eigenbasis is *not* the reference
basis is not covered here (bridging an arbitrary eigenbasis needs a §13-style unitary-covariance
step, tracked as the residual §14 obligation). The **genericity** hypothesis `hpos`
(`∀ j, 0 < ‖⟨e_j, ψ⟩‖²`, no vanishing amplitude) is the same one carried by `fs_born_volume_ratio_N`
(it makes each barycentric region a homeomorphic image of the open simplex). This module builds
axiom-free (foundational triple), carving-free, Gleason-free.

References: `LF4/MomentBornN.lean` (`fs_born_volume_ratio_N`, `fs_born_volume_ratio_N_apex`,
`ratioN`, `momentMap`, `replaceMap`, `apexLin`, `openSimplexFree`); `LF4/SingleQubitKahler.lean`
(`sg_observable_correspondence`, the single-qubit projector precursor); `specs/LF4-todo.md §14`;
`specs/future-work.md`; `BRIDGE-OBLIGATIONS.md` (the §14 bundle fields).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {M : ℕ}

/-- The `k`-th coordinate of `toEuclideanLin (diagonal d) ψ` is `d k * ψ k`. -/
theorem toEuclideanLin_diagonal_apply (d : Fin (M + 1) → ℂ) (ψ : EuclideanSpace ℂ (Fin (M + 1)))
    (k : Fin (M + 1)) :
    (Matrix.toEuclideanLin (Matrix.diagonal d) ψ) k = d k * ψ k := by
  have : (Matrix.toEuclideanLin (Matrix.diagonal d) ψ) k
      = (Matrix.diagonal d *ᵥ (WithLp.ofLp ψ)) k := rfl
  rw [this, Matrix.mulVec_diagonal]

/-- **The Hilbert side of §14 for a diagonal observable.** For a real eigenvalue vector `lam`
and any `ψ`, the expectation of the diagonal matrix `diagonal (lam ·)` in the state `ψ` is the
`lam`-weighted sum of the coordinate Born weights `‖⟨e_k, ψ⟩‖²`. -/
theorem diag_expectation (lam : Fin (M + 1) → ℝ) (ψ : EuclideanSpace ℂ (Fin (M + 1))) :
    inner ℂ ψ ((Matrix.toEuclideanLin (Matrix.diagonal (fun k => (lam k : ℂ)))) ψ)
      = ∑ k, (lam k : ℂ) * (‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 : ℝ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [toEuclideanLin_diagonal_apply, RCLike.inner_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul, mul_assoc, RCLike.mul_conj]
  norm_num

/-- The free Born vector of `ψ` (the moment-ratio coordinates of `[ψ]`). -/
noncomputable def bornVecN (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) : Fin M → ℝ :=
  ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)

/-- The per-basis-index simplex Born region: the free `replaceMap` image for a `castSucc`
coordinate, the affine apex image for the last coordinate. -/
noncomputable def bornSimplexRegion (b : Fin M → ℝ) (k : Fin (M + 1)) : Set (Fin M → ℝ) :=
  Fin.lastCases ((fun x => apexLin b x + b) '' openSimplexFree)
    (fun i => replaceMap b i '' openSimplexFree) k

/-- The ontic Born region on `Σ = ℂℙ^{N-1}` for basis index `k`: the moment-ratio preimage of
`bornSimplexRegion`. Its Fubini–Study measure is the Born weight `‖⟨e_k, ψ⟩‖²`
(`fsMeasure_bornRegionN`). -/
noncomputable def bornRegionN (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    Fin (M + 1) → Set (CPN (M + 1)) :=
  fun k => (fun p => ratioN (fun j => momentMap p j)) ⁻¹' bornSimplexRegion (bornVecN ψ hψ0) k

/-- **The ontic side of §14 for basis projectors (general N).** The Fubini–Study measure of the
Born region for basis index `k` is exactly the Born weight `‖⟨e_k, ψ⟩‖²`. Unifies
`fs_born_volume_ratio_N` (free coordinates) and `fs_born_volume_ratio_N_apex` (apex) via
`Fin.lastCases`. -/
theorem fsMeasure_bornRegionN (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) (k : Fin (M + 1)) :
    fubiniStudyMeasure p₀ (bornRegionN ψ hψ0 k)
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2) := by
  refine Fin.lastCases ?_ ?_ k
  · show fubiniStudyMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j)) ⁻¹'
          bornSimplexRegion (bornVecN ψ hψ0) (Fin.last M)) = _
    rw [bornSimplexRegion, Fin.lastCases_last, bornVecN]
    exact fs_born_volume_ratio_N_apex p₀ ψ hψ0 hψ hpos
  · intro i
    show fubiniStudyMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j)) ⁻¹'
          bornSimplexRegion (bornVecN ψ hψ0) (Fin.castSucc i)) = _
    rw [bornSimplexRegion, Fin.lastCases_castSucc, bornVecN]
    exact fs_born_volume_ratio_N p₀ ψ hψ0 hψ hpos i

/-- **§14 observable correspondence for a diagonal observable (general N).** The Hilbert
expectation of the diagonal self-adjoint observable `A = diagonal (lam ·)` in the state `ψ` is the
eigenvalue-weighted sum of the Fubini–Study volumes of the ontic Born regions:
`⟨ψ, A ψ⟩ = ∑ₖ lam k · vol(Rₖ)`, where `Rₖ = bornRegionN ψ k` is the moment-sublevel region on
`Σ = ℂℙ^{N-1}` whose volume is the Born weight `‖⟨e_k, ψ⟩‖²`. This realises each diagonal
observable as (the average over `Σ` of) the eigenvalue-weighted indicator sum `∑ₖ lam k · 𝟙_{Rₖ}` —
the general-N, all-eigenvalue analogue of the single-qubit `sg_observable_correspondence`.
Foundational triple; carving-free, Gleason-free. -/
theorem observable_correspondence_diagonal (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    (lam : Fin (M + 1) → ℝ) :
    inner ℂ ψ ((Matrix.toEuclideanLin (Matrix.diagonal (fun k => (lam k : ℂ)))) ψ)
      = ((∑ k, lam k * (fubiniStudyMeasure p₀ (bornRegionN ψ hψ0 k)).toReal : ℝ) : ℂ) := by
  rw [diag_expectation, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, fsMeasure_bornRegionN p₀ ψ hψ0 hψ hpos k,
      ENNReal.toReal_ofReal (by positivity)]

/-! ### The integral form: `A_ontic` as an explicit measurable Σ-function -/

/-- The `i`-th free Born coordinate is the Born weight at `castSucc i`. -/
theorem bornVecN_apply (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin M) :
    bornVecN ψ hψ0 i = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2 := by
  rw [bornVecN, ratioN,
      show (∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j) = 1 from momentMap_sum_eq_one _,
      div_one, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc i)]

/-- The apex Born weight: `1 − ∑ᵢ bᵢ = ‖⟨e_last, ψ⟩‖²`. -/
theorem one_sub_sum_bornVecN (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    1 - ∑ i, bornVecN ψ hψ0 i
      = ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2 := by
  have hsum : ∑ i, bornVecN ψ hψ0 i
      = ∑ i : Fin M, momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.castSucc i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bornVecN_apply ψ hψ0 hψ, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc i)]
  have htot : (∑ k : Fin M, momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.castSucc k))
      + momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.last M) = 1 := by
    rw [← Fin.sum_univ_castSucc]; exact momentMap_sum_eq_one _
  rw [hsum]
  rw [momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.last M)] at htot
  linarith

/-- Each ontic Born region is measurable (an open-image moment-ratio preimage; the moment map is
measurable and each simplex Born region is an open set, being the image of the open simplex under a
determinant-`≠ 0` affine map). -/
theorem bornRegionN_measurableSet (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) (k : Fin (M + 1)) :
    MeasurableSet (bornRegionN ψ hψ0 k) := by
  have hopen : IsOpen (bornSimplexRegion (bornVecN ψ hψ0) k) := by
    refine Fin.lastCases ?_ ?_ k
    · rw [bornSimplexRegion, Fin.lastCases_last]
      have hdet : LinearMap.det (apexLin (bornVecN ψ hψ0)) ≠ 0 := by
        rw [apexLin_det, one_sub_sum_bornVecN ψ hψ0 hψ]; exact ne_of_gt (hpos _)
      have hopenLin : IsOpen (apexLin (bornVecN ψ hψ0) '' openSimplexFree) :=
        LinearMap.isOpenMap_of_finiteDimensional _
          (LinearMap.equivOfDetNeZero (apexLin (bornVecN ψ hψ0)) hdet).surjective _
          isOpen_openSimplexFree
      have hregion : (fun x => apexLin (bornVecN ψ hψ0) x + bornVecN ψ hψ0) '' openSimplexFree
          = (fun y => y + bornVecN ψ hψ0) '' (apexLin (bornVecN ψ hψ0) '' openSimplexFree) :=
        (Set.image_image (fun y : Fin M → ℝ => y + bornVecN ψ hψ0) _ openSimplexFree).symm
      rw [hregion]
      exact (Homeomorph.addRight (bornVecN ψ hψ0)).isOpenMap _ hopenLin
    · intro i
      rw [bornSimplexRegion, Fin.lastCases_castSucc]
      have hdet : LinearMap.det (replaceMap (bornVecN ψ hψ0) i) ≠ 0 := by
        rw [replaceMap_det, bornVecN_apply ψ hψ0 hψ]; exact ne_of_gt (hpos _)
      exact LinearMap.isOpenMap_of_finiteDimensional _
        (LinearMap.equivOfDetNeZero (replaceMap (bornVecN ψ hψ0) i) hdet).surjective _
        isOpen_openSimplexFree
  exact measurable_ratio_momentMap hopen.measurableSet

/-- **The ontic observable** realising a diagonal Hilbert observable: the eigenvalue-weighted sum
of the Born-region indicators, `A_ontic = ∑ₖ lam k · 𝟙_{Rₖ}` — a measurable simple function on
`Σ = ℂℙ^{N-1}`. -/
noncomputable def aOntic (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (lam : Fin (M + 1) → ℝ) : CPN (M + 1) → ℝ :=
  fun p => ∑ k, lam k * (bornRegionN ψ hψ0 k).indicator (1 : CPN (M + 1) → ℝ) p

/-- **The Σ-average of `A_ontic` is the weighted Born-volume sum** (finite additivity of the
integral over the eigenvalue-weighted indicators, each integrable since `μ_FS` is a probability
measure and each region is measurable). -/
theorem integral_aOntic (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    (lam : Fin (M + 1) → ℝ) :
    ∫ p, aOntic ψ hψ0 lam p ∂(fubiniStudyMeasure p₀)
      = ∑ k, lam k * (fubiniStudyMeasure p₀ (bornRegionN ψ hψ0 k)).toReal := by
  unfold aOntic
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul,
        integral_indicator_one (bornRegionN_measurableSet ψ hψ0 hψ hpos k), measureReal_def]
  · intro k _
    exact ((integrable_const (1 : ℝ)).indicator
      (bornRegionN_measurableSet ψ hψ0 hψ hpos k)).const_mul (lam k)

/-- **§14 observable correspondence, integral form (general N, diagonal observables).** The
Hilbert expectation of the diagonal observable `diagonal (lam ·)` equals the Fubini–Study
`Σ`-average of the ontic observable `A_ontic = ∑ₖ lam k · 𝟙_{Rₖ}`. This is the canonical §14
statement — `⟨ψ, A ψ⟩ = ∫ A_ontic dμ_FS`, with `A_ontic` an explicit measurable `Σ`-function —
of which `observable_correspondence_diagonal` is the pointwise-volume form. Foundational triple. -/
theorem observable_correspondence_diagonal_integral (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    (lam : Fin (M + 1) → ℝ) :
    inner ℂ ψ ((Matrix.toEuclideanLin (Matrix.diagonal (fun k => (lam k : ℂ)))) ψ)
      = ((∫ p, aOntic ψ hψ0 lam p ∂(fubiniStudyMeasure p₀) : ℝ) : ℂ) := by
  rw [observable_correspondence_diagonal p₀ ψ hψ0 hψ hpos lam,
      integral_aOntic p₀ ψ hψ0 hψ hpos lam]

end LF4
end CSD
