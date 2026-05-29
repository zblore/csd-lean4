import CsdLean4.LF4.Instance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# LF4 Tranche 1: the Born weights as the torus moment map on ℂℙ^{N-1}

The Kähler structure on `ℂℙ^{N-1}` carries a canonical object the CSD corpus
never invokes: the **moment map** of the maximal-torus action. For the standard
phase action of `Tᴺ` on `ℂℙ^{N-1}`, the moment map is

```
Φ : ℂℙ^{N-1} → Δ_{N-1},   Φ([z])ᵢ = |zᵢ|² / ‖z‖²
```

landing in the standard simplex (coordinates nonnegative, summing to one). Its
coordinates **are** the Born weights in the measurement eigenbasis: at a unit
preparation `ψ`,

```
Φ([ψ])ᵢ = |ψᵢ|² = ‖⟨eᵢ, ψ⟩‖²    (eᵢ = EuclideanSpace.single i 1).
```

This is a theorem of symplectic geometry, **forced** by the Fubini–Study Kähler
structure together with the torus action — not an arc carved to a target value
(`SingletKahler.kMuPsi_kRegion`) and not an operational-consistency postulate
(`busch_effect_gleason`). It exhibits the Born weight vector as a canonical
invariant of the very structure the programme takes as primitive (the compact
Kähler `Σ`). See `specs/carve-out-plan.md` (Tranche 1).

**Scope of this slice.** This module delivers the moment map, the simplex
constraints (`momentMap_nonneg`, `momentMap_sum_eq_one`), and the headline
Born-weight identity (`momentMap_mk_eq_inner_sq`). It does **not** yet prove the
Duistermaat–Heckman pushforward (`Φ∗μ_FS = uniform on Δ`) nor the full
`U(N)`-equivariance — those are the next slices and need symplectic-volume
machinery Mathlib lacks. The honest limit recorded in the plan stands: this
gives the Born weight as a moment *coordinate* of the preparation point, not as a
ψ-independent volume ratio; the ψ-dependence still enters through the preparation
measure `μψ`, whose principled construction is the open `G3b` content.

**Category:** conceptually 1-Mathlib (CSD-free projective/Kähler geometry); kept
here in `CSD.LF4` for now as it drives the carve-out programme. Extraction
candidate (cf. LF4-todo §10).
-/

open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- The torus moment map on `ℂℙ^{N-1}`, in coordinates: `Φ([z])ᵢ = |zᵢ|²/‖z‖²`.
Well-defined on the projective point (scale-invariant; see `momentMap_mk`). -/
noncomputable def momentMap (p : CPN N) (i : Fin N) : ℝ :=
  ‖p.rep i‖ ^ 2 / ‖p.rep‖ ^ 2

/-- `‖v‖² = ∑ᵢ ‖vᵢ‖²` on Euclidean space (Parseval in coordinate form). -/
lemma euclidean_norm_sq_eq_sum (v : EuclideanSpace ℂ (Fin N)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Each moment coordinate is nonnegative. -/
lemma momentMap_nonneg (p : CPN N) (i : Fin N) : 0 ≤ momentMap p i :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The moment coordinates sum to one: the image lands in the simplex, so the
Born weights form a probability vector. -/
lemma momentMap_sum_eq_one (p : CPN N) : ∑ i, momentMap p i = 1 := by
  have hrep2 : ‖p.rep‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr p.rep_nonzero)
  unfold momentMap
  rw [← Finset.sum_div, ← euclidean_norm_sq_eq_sum, div_self hrep2]

/-- The coordinate ratio `‖vᵢ‖²/‖v‖²` is invariant under nonzero rescaling of
`v` (the projective well-definedness of `momentMap`). -/
lemma momentRatio_smul (c : ℂ) (hc : c ≠ 0) (v : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    ‖(c • v) i‖ ^ 2 / ‖c • v‖ ^ 2 = ‖v i‖ ^ 2 / ‖v‖ ^ 2 := by
  rw [PiLp.smul_apply, smul_eq_mul, norm_smul, norm_mul, mul_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]

/-- The moment map evaluated at a representative `ψ`: `Φ([ψ])ᵢ = ‖ψᵢ‖²/‖ψ‖²`.
The value depends only on `ψ` (not on the chosen `rep`), by scale-invariance. -/
lemma momentMap_mk (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0) (i : Fin N) :
    momentMap (Projectivization.mk ℂ ψ hψ) i = ‖ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ ψ hψ).rep ψ
        (Projectivization.rep_nonzero _) hψ).mp (Projectivization.mk_rep _)
  unfold momentMap
  rw [← ha]
  simp only [Units.smul_def]
  exact momentRatio_smul (↑a) (Units.ne_zero a) ψ i

/-- **Headline (Tranche 1): the Born weight is the moment-map coordinate.**
For a unit preparation `ψ`, the `i`-th coordinate of the Fubini–Study torus
moment map at `[ψ]` equals the Born weight `‖⟨eᵢ, ψ⟩‖²` in the measurement
eigenbasis `eᵢ = EuclideanSpace.single i 1`. Forced by the Kähler structure +
torus action; no carving, no operational-consistency postulate. -/
theorem momentMap_mk_eq_inner_sq (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) :
    momentMap (Projectivization.mk ℂ ψ hψ0) i
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  rw [momentMap_mk ψ hψ0 i, hψ, one_pow, div_one,
      EuclideanSpace.inner_single_left, map_one, one_mul]

end LF4
end CSD
