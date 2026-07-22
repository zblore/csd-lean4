/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.PhaseInvariance
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Volume-ratio projective effect function

**Category:** 3-Local (pre-LF4 plan Phase 2 — the volume-ratio
foundational object: given a unit-vector representative map
`rep : P → EuclideanSpace ℂ (Fin N)` from an abstract projective space
`P` and a finite-dimensional `Effect`, `effectProjFn rep E p` returns
the real number that, integrated against `π_*μprep`, gives the
probability of outcome `E` under a preparation pushing forward to a
measure on `P`. This is the CSD-foundational object: probability is
volume-integration of `effectProjFn` against the projective measure,
not a Busch-derived trace-form expression.

For rank-1 effects, the function evaluates pointwise to `‖⟨rep p, φ⟩‖²`
— the standard Born quadratic form at the representative vector. The
trace-form / density-operator description is a reformulation, available
via `traceForm` + `born_quadratic`; that reformulation is downstream of
the volume integral, not foundational.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ} {P : Type*}

/-- **Volume-ratio projective effect function.** Given a unit-vector
    representative map `rep : P → EuclideanSpace ℂ (Fin N)` and a
    finite-dimensional `Effect E`, returns the real number
    `RCLike.re (star v ⬝ᵥ E.M *ᵥ v)` where `v = (rep p).ofLp` is the
    underlying function. The probability assignment from a preparation
    measure `μprep` is then `∫ p, effectProjFn rep E p ∂(π_*μprep)`. -/
noncomputable def effectProjFn
    (rep : P → EuclideanSpace ℂ (Fin N)) (E : Effect N) : P → ℝ :=
  fun p =>
    RCLike.re (star (WithLp.ofLp (rep p) : Fin N → ℂ) ⬝ᵥ
                E.M *ᵥ WithLp.ofLp (rep p))

/-- For the rank-1 effect `|φ⟩⟨φ|`, the volume-ratio effect function
    evaluates pointwise to `‖⟨rep p, φ⟩‖²`. This is the standard Born
    quadratic form at the representative vector. -/
lemma effectProjFn_rankOne
    (rep : P → EuclideanSpace ℂ (Fin N))
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) (p : P) :
    effectProjFn rep (rankOneEffect φ hφ) p = ‖inner ℂ (rep p) φ‖ ^ 2 := by
  set v : Fin N → ℂ := WithLp.ofLp (rep p) with hv_def
  set ψ : Fin N → ℂ := WithLp.ofLp φ with hψ_def
  -- effectProjFn rep (rankOneEffect φ hφ) p = RCLike.re (star v ⬝ᵥ outerProduct φ *ᵥ v).
  -- outerProduct φ = vecMulVec ψ (star ψ).
  -- Use dotProduct_mulVec → vecMul_vecMulVec:
  --   star v ⬝ᵥ vecMulVec ψ (star ψ) *ᵥ v
  --     = (star v ᵥ* vecMulVec ψ (star ψ)) ⬝ᵥ v       [dotProduct_mulVec]
  --     = ((star v ⬝ᵥ ψ) • star ψ) ⬝ᵥ v               [vecMul_vecMulVec]
  --     = (star v ⬝ᵥ ψ) * (star ψ ⬝ᵥ v)               [smul_dotProduct]
  -- Then star ψ ⬝ᵥ v = conj (star v ⬝ᵥ ψ) by star_dotProduct.
  -- And inner ℂ (rep p) φ = star v ⬝ᵥ ψ via inner_eq_star_dotProduct + comm.
  -- Final: (X) * conj X = ‖X‖² (RCLike.mul_conj).
  show RCLike.re (star v ⬝ᵥ (outerProduct φ) *ᵥ v) = ‖inner ℂ (rep p) φ‖ ^ 2
  rw [show outerProduct φ = vecMulVec ψ (star ψ) from rfl,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec,
      smul_dotProduct, smul_eq_mul]
  have h_inner : inner ℂ (rep p) φ = star v ⬝ᵥ ψ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have h_conj : (star ψ ⬝ᵥ v : ℂ) = starRingEnd ℂ (star v ⬝ᵥ ψ) := by
    rw [Matrix.star_dotProduct]; rfl
  rw [h_conj, ← h_inner, RCLike.mul_conj]
  norm_cast

/-- The zero effect's volume-ratio function is identically zero. -/
@[simp]
lemma effectProjFn_zero (rep : P → EuclideanSpace ℂ (Fin N)) :
    effectProjFn rep (Effect.zero : Effect N) = 0 := by
  funext p
  simp [effectProjFn, Effect.zero]

/-- The identity effect's volume-ratio function is `‖rep p‖²` pointwise.
    For unit-norm `rep p` this is `1`. -/
lemma effectProjFn_one (rep : P → EuclideanSpace ℂ (Fin N)) (p : P) :
    effectProjFn rep (Effect.one : Effect N) p = ‖rep p‖ ^ 2 := by
  set v : Fin N → ℂ := WithLp.ofLp (rep p) with hv_def
  show RCLike.re (star v ⬝ᵥ (1 : Matrix (Fin N) (Fin N) ℂ) *ᵥ v) = ‖rep p‖ ^ 2
  rw [Matrix.one_mulVec]
  -- star v ⬝ᵥ v = ‖rep p‖² (via EuclideanSpace inner-product algebra).
  have hnorm : (star v ⬝ᵥ v : ℂ) = ((‖rep p‖ : ℂ)) ^ 2 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (rep p)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  rw [hnorm]
  norm_cast

/-- The volume-ratio effect function is additive in the effect argument
    (when the sum is itself an effect). -/
lemma effectProjFn_add
    (rep : P → EuclideanSpace ℂ (Fin N)) (E F : Effect N)
    (hLe : (1 - (E.M + F.M)).PosSemidef) (p : P) :
    effectProjFn rep (Effect.add E F hLe) p
      = effectProjFn rep E p + effectProjFn rep F p := by
  simp only [effectProjFn, Effect.add, Matrix.add_mulVec, dotProduct_add, map_add]

/-! ### Bounds

The volume-ratio effect function is non-negative (from `E.nonneg`) and
bounded by `1` for unit-norm `rep p` (from `E.le_one`).
-/

/-- The volume-ratio effect function is pointwise non-negative.
    Routes through `Matrix.PosSemidef.re_dotProduct_nonneg` applied to
    `E.M`'s PSD content. -/
lemma effectProjFn_nonneg
    (rep : P → EuclideanSpace ℂ (Fin N)) (E : Effect N) (p : P) :
    0 ≤ effectProjFn rep E p :=
  E.nonneg.re_dotProduct_nonneg (WithLp.ofLp (rep p))

/-- The volume-ratio effect function is pointwise bounded by `‖rep p‖²`.
    For unit-norm `rep p` this is `1`. Routes through `E.le_one` applied
    via the same `re_dotProduct_nonneg` mechanism on `1 - E.M`. -/
lemma effectProjFn_le_norm_sq
    (rep : P → EuclideanSpace ℂ (Fin N)) (E : Effect N) (p : P) :
    effectProjFn rep E p ≤ ‖rep p‖ ^ 2 := by
  set v : Fin N → ℂ := WithLp.ofLp (rep p) with hv_def
  -- 0 ≤ Re (star v ⬝ᵥ (1 - E.M) *ᵥ v) = Re (star v ⬝ᵥ v) - Re (star v ⬝ᵥ E.M *ᵥ v)
  --   = ‖rep p‖² - effectProjFn rep E p.
  have h := E.le_one.re_dotProduct_nonneg v
  -- h : 0 ≤ RCLike.re (star v ⬝ᵥ (1 - E.M) *ᵥ v)
  rw [show ((1 : Matrix (Fin N) (Fin N) ℂ) - E.M) *ᵥ v
        = v - E.M *ᵥ v from by rw [Matrix.sub_mulVec, Matrix.one_mulVec]] at h
  rw [show star v ⬝ᵥ (v - E.M *ᵥ v) = star v ⬝ᵥ v - star v ⬝ᵥ E.M *ᵥ v from
      dotProduct_sub _ _ _] at h
  rw [map_sub] at h
  -- h : 0 ≤ RCLike.re (star v ⬝ᵥ v) - RCLike.re (star v ⬝ᵥ E.M *ᵥ v)
  have h_norm : RCLike.re ((star v ⬝ᵥ v : ℂ)) = ‖rep p‖ ^ 2 := by
    have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (rep p)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hself
    rw [hself]
    norm_cast
  have h_effect : effectProjFn rep E p = RCLike.re (star v ⬝ᵥ E.M *ᵥ v) := rfl
  linarith

/-- Specialisation of `effectProjFn_le_norm_sq` to unit-norm `rep p`. -/
lemma effectProjFn_le_one
    (rep : P → EuclideanSpace ℂ (Fin N)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (E : Effect N) (p : P) :
    effectProjFn rep E p ≤ 1 := by
  have := effectProjFn_le_norm_sq rep E p
  rw [hrep_unit p] at this
  simpa using this

/-! ### Measurability

`effectProjFn rep E` is measurable when `rep` is measurable. The
function decomposes as `rep` composed with a continuous map
`EuclideanSpace ℂ (Fin N) → ℝ` (a real quadratic form). On
finite-dim normed spaces all polynomial expressions are continuous.
-/

/-- The volume-ratio effect function is measurable in its argument
    when `rep` is measurable. -/
@[fun_prop]
lemma effectProjFn_measurable
    {Q : Type*} [MeasurableSpace Q] (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_meas : Measurable rep) (E : Effect N) :
    Measurable (effectProjFn rep E) := by
  -- Decompose effectProjFn = F ∘ ofLp ∘ rep where:
  --   rep         : Q → EuclideanSpace ℂ (Fin N)   measurable (hypothesis)
  --   ofLp        : EuclideanSpace ℂ (Fin N) → Fin N → ℂ   measurable
  --   F u := RCLike.re (star u ⬝ᵥ E.M *ᵥ u)        continuous (finite-dim
  --                                                  quadratic polynomial).
  have h_F_meas : Measurable (fun u : Fin N → ℂ => RCLike.re (star u ⬝ᵥ E.M *ᵥ u)) := by
    have h_F_cont : Continuous (fun u : Fin N → ℂ =>
        RCLike.re (star u ⬝ᵥ E.M *ᵥ u)) := by
      refine RCLike.continuous_re.comp ?_
      -- Continuous (fun u => star u ⬝ᵥ E.M *ᵥ u) as a function on Fin N → ℂ.
      -- Decompose: star u = pointwise star (continuous); E.M *ᵥ u is linear
      -- (continuous on finite-dim Pi); dotProduct is bilinear continuous.
      have h_star : Continuous (fun u : Fin N → ℂ => (star u : Fin N → ℂ)) :=
        continuous_pi (fun i => Continuous.star (continuous_apply i))
      have h_mulVec : Continuous (fun u : Fin N → ℂ => E.M *ᵥ u) :=
        continuous_pi (fun i => by
          show Continuous (fun u : Fin N → ℂ => E.M i ⬝ᵥ u)
          exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
      -- dotProduct (a b : Fin N → ℂ) = Σ_i a i * b i: continuous in (a, b).
      have : Continuous (fun u : Fin N → ℂ => ∑ i, (star u) i * (E.M *ᵥ u) i) :=
        continuous_finsetSum _ (fun i _ =>
          ((continuous_apply i).comp h_star).mul ((continuous_apply i).comp h_mulVec))
      exact this
    exact h_F_cont.measurable
  -- effectProjFn rep E = h_F ∘ ofLp ∘ rep (definitionally).
  have h_ofLp_meas : Measurable (fun v : EuclideanSpace ℂ (Fin N) =>
      (WithLp.ofLp v : Fin N → ℂ)) :=
    WithLp.measurable_ofLp 2 (Fin N → ℂ)
  exact h_F_meas.comp (h_ofLp_meas.comp hrep_meas)

/-- The volume-ratio effect function is integrable against any finite
    measure when `rep` is measurable and unit-norm. Routes via
    `Integrable.of_bound`: measurable + pointwise bounded by 1 (via
    `effectProjFn_le_one`) + finite measure ⟹ integrable. -/
lemma effectProjFn_integrable
    {Q : Type*} [MeasurableSpace Q] (rep : Q → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (E : Effect N) (μ : MeasureTheory.Measure Q) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.Integrable (effectProjFn rep E) μ := by
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact (effectProjFn_measurable rep hrep_meas E).aestronglyMeasurable
  · refine MeasureTheory.ae_of_all _ fun p => ?_
    rw [Real.norm_of_nonneg (effectProjFn_nonneg rep E p)]
    exact effectProjFn_le_one rep hrep_unit E p

end LF2
end CSD
