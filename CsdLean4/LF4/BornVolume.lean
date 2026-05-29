import CsdLean4.LF4.MomentMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# LF4 Tranche M slice 3: the Born weights as barycentric volume ratios

Slice 1 (`MomentMap.lean`) showed the Born weight is the torus moment-map
coordinate `Φ([ψ])ᵢ = ‖⟨eᵢ,ψ⟩‖²` — a point coordinate in the moment polytope
`Δ_{N-1}`. This slice turns that coordinate into a genuine **volume ratio**, via
the barycentric subdivision of the polytope at the preparation point.

For a point `b ∈ Δ_{N-1}` (the Born vector), the `i`-th sub-simplex of the
subdivision at `b` is the image of the standard simplex under the
**vertex-replacement map** `replaceMap b i` — the linear map that replaces the
`i`-th standard basis vector with `b`. Its determinant is exactly the `i`-th
barycentric coordinate `bᵢ` (Cramer), so by `addHaar_image_linearMap` it scales
**Lebesgue volume by `bᵢ`**:

```
volume (replaceMap b i '' s) = ofReal (bᵢ) · volume s,      and  ∑ᵢ … = volume s.
```

Composing with slice 1 (`born_eq_volume_ratio`): the Born weight `‖⟨eᵢ,ψ⟩‖²` is
the volume ratio of the `i`-th subdivision region. The regions are defined by an
affine geometric rule (subdivide at `b`); the equality to the Born weight is the
barycentric-coordinate theorem, **not** a region carved to a target volume
(contrast `SingletKahler.kMuPsi_kRegion`) and **not** an operational-consistency
postulate (`busch_effect_gleason`). This is the literal realisation of Sigma0
§5.7's slogan "Born-form probabilities are operational representations of the
projected volume structure."

## Honest scope (see `specs/carve-out-plan.md` Tranche M)

1. `b` is the moment coordinate (slice 1), so this derives "Born = volume ratio"
   *given* the Fubini–Study Kähler structure as the ontic primitive. It does not
   manufacture Born from a metric-free structure.
2. The volume here is Lebesgue volume on the moment-polytope coordinates (the
   ratio is the same for the parallelepiped and the simplex). Lifting it to the
   μ_FS-volume on the ontic `Σ = ℂℙ^{N-1}` itself is the Duistermaat–Heckman
   pushforward `Φ∗μ_FS = uniform_Δ` (slice 2), which needs symplectic-volume
   machinery Mathlib lacks.

**Category:** conceptually 1-Mathlib (affine/measure geometry); kept in `CSD.LF4`
as it drives the carve-out programme. Extraction candidate (LF4-todo §10).
-/

open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- The **vertex-replacement map**: the linear map on `Fin N → ℝ` whose matrix is
the identity with column `i` replaced by `b`. Geometrically it sends the standard
simplex to the `i`-th sub-simplex of the barycentric subdivision at `b`. -/
noncomputable def replaceMap (b : Fin N → ℝ) (i : Fin N) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' ((1 : Matrix (Fin N) (Fin N) ℝ).updateCol i b)

/-- The determinant of the vertex-replacement map is the `i`-th barycentric
coordinate `bᵢ` (Cramer's rule on the identity). -/
lemma replaceMap_det (b : Fin N → ℝ) (i : Fin N) :
    LinearMap.det (replaceMap b i) = b i := by
  rw [replaceMap, LinearMap.det_toLin', ← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

/-- **The vertex-replacement map scales Lebesgue volume by `bᵢ`** (`bᵢ ≥ 0`).
Hence `volume (replaceMap b i '' s) / volume s = bᵢ`: the `i`-th subdivision
region is a `bᵢ`-fraction of the reference region. -/
lemma replaceMap_image_volume (b : Fin N → ℝ) (i : Fin N) (hb : 0 ≤ b i)
    (s : Set (Fin N → ℝ)) :
    volume (replaceMap b i '' s) = ENNReal.ofReal (b i) * volume s := by
  rw [Measure.addHaar_image_linearMap volume (replaceMap b i) s, replaceMap_det,
      abs_of_nonneg hb]

/-- The subdivision volumes sum to the reference volume (probability
normalisation), since the barycentric coordinates sum to one. -/
lemma replaceMap_image_volume_sum (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, b i = 1) (s : Set (Fin N → ℝ)) :
    ∑ i, volume (replaceMap b i '' s) = volume s := by
  simp_rw [fun i => replaceMap_image_volume b i (hb i) s]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hb i, hsum,
      ENNReal.ofReal_one, one_mul]

/-- **Headline (Tranche M slice 3): the Born weight is a barycentric volume
ratio.** For a unit preparation `ψ`, the `i`-th subdivision region of the moment
polytope at `Φ([ψ])` carries volume fraction `‖⟨eᵢ, ψ⟩‖²` of any reference region
— the Born weight realised as a genuine Lebesgue-volume ratio of a
geometrically-defined region (no carving, no operational-consistency postulate).
-/
theorem born_eq_volume_ratio (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) (s : Set (Fin N → ℝ)) :
    volume (replaceMap (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) i '' s)
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) * volume s := by
  rw [replaceMap_image_volume _ i (momentMap_nonneg _ i),
      momentMap_mk_eq_inner_sq ψ hψ0 hψ i]

end LF4
end CSD
