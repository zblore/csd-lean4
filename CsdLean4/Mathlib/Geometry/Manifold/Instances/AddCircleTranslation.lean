/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `AddCircle T` charted by translation: the atlas whose transitions are translations

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).

`Instances/AddCircle.lean` (Q33) makes `AddCircle T` a manifold over `EuclideanSpace ℝ (Fin 1)` by
transport from `Circle`, whose charts are stereographic. That structure is the right one for
"`AddCircle T` is a manifold"; it is the wrong one for writing down a *form* on the circle or the
torus, because in stereographic coordinates the invariant form `dθ` is not constant and every
chart transition is a Möbius map.

This module carries the second, classical structure: **the translation atlas**, modelled on `ℝ`
itself. The chart with cut point `a` is the inverse of the quotient map on `(a, a + T)`
(Mathlib's `AddCircle.openPartialHomeomorphCoe`, read backwards), and any two charts differ by a
translation by a multiple of `T` on each component of their overlap. Consequently

* every transition is analytic (`instIsManifoldReal`, an `IsManifold 𝓘(ℝ, ℝ) ω` instance), and
* ★ `fderiv_chart_transition` — **the derivative of every chart transition is the identity**,
  which is what makes a constant alternating map a well-defined smooth form on the circle and on
  the torus (`TranslationAtlasForm.lean`).

The model is `ℝ`, not `EuclideanSpace ℝ (Fin 1)`, so the two charted-space instances on
`AddCircle T` are keyed on different model types and never compete.

## Honest scope

⚠️ **`0 < T` is a `Fact`**, as in Mathlib's `equivIco`. The corpus's torus `KTorus` has `T = 1`.

⚠️ **Two atlases, no comparison.** Nothing here relates the translation structure to the
stereographic one of `Instances/AddCircle.lean`; they are both manifold structures on the same
topological space, and a diffeomorphism between them is neither stated nor needed.

References: `Mathlib/Topology/Instances/AddCircle/Defs.lean` (`openPartialHomeomorphCoe`,
`equivIco`, `continuousAt_equivIco`); `Geometry/Manifold/Instances/AddCircle.lean` (the
stereographic structure); `Geometry/Manifold/TranslationAtlasForm.lean` (the consumer);
`specs/BACKLOG.md` (`R-016′`).
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-! ### The translation charts -/

/-- **The translation chart with cut point `a`**: the inverse of the quotient map on `(a, a + T)`.
Its source is the circle minus the point `a`, its target the open interval `(a, a + T)`. -/
def translationChart (a : ℝ) : OpenPartialHomeomorph (AddCircle T) ℝ :=
  (openPartialHomeomorphCoe T a).symm

@[simp] theorem translationChart_source (a : ℝ) :
    (translationChart (T := T) a).source = {(a : AddCircle T)}ᶜ := rfl

@[simp] theorem translationChart_target (a : ℝ) :
    (translationChart (T := T) a).target = Ioo a (a + T) := rfl

theorem translationChart_apply (a : ℝ) (x : AddCircle T) :
    translationChart a x = (equivIco T a x : ℝ) := rfl

@[simp] theorem translationChart_symm_apply (a y : ℝ) :
    (translationChart (T := T) a).symm y = (y : AddCircle T) := rfl

/-- The chart is a section of the quotient map. -/
@[simp] theorem coe_translationChart (a : ℝ) (x : AddCircle T) :
    ((translationChart a x : ℝ) : AddCircle T) = x := coe_equivIco

/-- The chart value differs from any lift by a multiple of the period. -/
theorem exists_translationChart_coe_eq (a y : ℝ) :
    ∃ n : ℤ, translationChart (T := T) a (y : AddCircle T) = y + n • T := by
  have h : ((translationChart (T := T) a (y : AddCircle T) - y : ℝ) : AddCircle T) = 0 := by
    rw [coe_sub, coe_translationChart, sub_self]
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff T).1 h
  exact ⟨n, by linarith⟩

/-! ### The cut point avoiding a given point, and the atlas -/

/-- A cut point the point `x` avoids: half a period past the lift of `x` in `[0, T)`. -/
def cutPoint (x : AddCircle T) : ℝ := (equivIco T 0 x : ℝ) + T / 2

theorem ne_coe_cutPoint (x : AddCircle T) : x ≠ (cutPoint x : AddCircle T) := by
  intro h
  rw [cutPoint, coe_add] at h
  -- `x = x + T/2` on the circle forces `T/2 = 0` there
  have h1 : x + ((T / 2 : ℝ) : AddCircle T) = x := by
    calc x + ((T / 2 : ℝ) : AddCircle T)
        = ((equivIco T 0 x : ℝ) : AddCircle T) + ((T / 2 : ℝ) : AddCircle T) := by
          rw [coe_equivIco]
      _ = x := h.symm
  have h0 : ((T / 2 : ℝ) : AddCircle T) = 0 := by
    simpa using congrArg (fun z => z - x) h1
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff T).1 h0
  have hTpos := hT.out
  rw [zsmul_eq_mul] at hn
  have h2 : ((n * 2 : ℤ) : ℝ) * T = 1 * T := by push_cast; linarith
  have h3 : (n * 2 : ℤ) = 1 := by exact_mod_cast mul_right_cancel₀ hTpos.ne' h2
  omega

/-- ★ **`AddCircle T` charted by translation**, modelled on `ℝ`. -/
instance instChartedSpaceReal : ChartedSpace ℝ (AddCircle T) where
  atlas := Set.range (translationChart (T := T))
  chartAt x := translationChart (cutPoint x)
  mem_chart_source x := ne_coe_cutPoint x
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem chartAt_eq (x : AddCircle T) : chartAt ℝ x = translationChart (cutPoint x) := rfl

theorem mem_atlas_iff (e : OpenPartialHomeomorph (AddCircle T) ℝ) :
    e ∈ atlas ℝ (AddCircle T) ↔ ∃ a, translationChart a = e := Iff.rfl

/-! ### Transitions are translations, locally -/

/-- The transition from the chart with cut `a` to the chart with cut `b`, as a function on `ℝ`:
read the point back on the circle and out through the second chart. Cut `a` plays no role in the
formula, only in the domain. -/
theorem transition_eq (a b : ℝ) :
    (translationChart (T := T) b ∘ (translationChart (T := T) a).symm)
      = fun y : ℝ => translationChart (T := T) b (y : AddCircle T) := rfl

theorem continuousAt_transition (b : ℝ) {y₀ : ℝ} (hy₀ : (y₀ : AddCircle T) ≠ (b : AddCircle T)) :
    ContinuousAt (fun y : ℝ => translationChart (T := T) b (y : AddCircle T)) y₀ := by
  have h1 : ContinuousAt (equivIco T b) (y₀ : AddCircle T) := continuousAt_equivIco T b hy₀
  exact continuousAt_subtype_val.comp (h1.comp (AddCircle.continuous_mk' T).continuousAt)

/-- Two multiples of the period closer than the period are equal. -/
theorem zsmul_eq_of_abs_sub_lt {m n : ℤ} (h : |m • T - n • T| < T) : m = n := by
  have hTpos := hT.out
  rw [← sub_smul, zsmul_eq_mul, abs_mul, abs_of_pos hTpos] at h
  have h1 : |((m - n : ℤ) : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith [abs_nonneg ((m - n : ℤ) : ℝ)]
  have h2 : |m - n| < 1 := by exact_mod_cast h1
  exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h2)

/-- ★ **A transition is a translation near every point of its domain.** -/
theorem transition_eventuallyEq (b : ℝ) {y₀ : ℝ}
    (hy₀ : (y₀ : AddCircle T) ≠ (b : AddCircle T)) :
    (fun y : ℝ => translationChart (T := T) b (y : AddCircle T))
      =ᶠ[𝓝 y₀] fun y => y + (translationChart (T := T) b (y₀ : AddCircle T) - y₀) := by
  have hTpos := hT.out
  set φ : ℝ → ℝ := fun y => translationChart (T := T) b (y : AddCircle T) with hφ
  have hc : ContinuousAt (fun y => φ y - y) y₀ :=
    (continuousAt_transition b hy₀).sub continuousAt_id
  have hev : ∀ᶠ y in 𝓝 y₀, dist (φ y - y) (φ y₀ - y₀) < T :=
    (Metric.tendsto_nhds.1 hc) T hTpos
  filter_upwards [hev] with y hy
  rw [Real.dist_eq] at hy
  obtain ⟨m, hm⟩ := exists_translationChart_coe_eq (T := T) b y
  obtain ⟨n, hn⟩ := exists_translationChart_coe_eq (T := T) b y₀
  have hm' : φ y - y = m • T := by simp only [hφ]; linarith
  have hn' : φ y₀ - y₀ = n • T := by simp only [hφ]; linarith
  rw [hm', hn'] at hy
  have := zsmul_eq_of_abs_sub_lt (T := T) hy
  subst this
  simp only [hφ] at hm hn ⊢
  linarith

theorem hasFDerivAt_transition (b : ℝ) {y₀ : ℝ}
    (hy₀ : (y₀ : AddCircle T) ≠ (b : AddCircle T)) :
    HasFDerivAt (fun y : ℝ => translationChart (T := T) b (y : AddCircle T))
      (ContinuousLinearMap.id ℝ ℝ) y₀ :=
  ((hasFDerivAt_id y₀).add_const _).congr_of_eventuallyEq (transition_eventuallyEq b hy₀)

theorem contDiffAt_transition (b : ℝ) {y₀ : ℝ}
    (hy₀ : (y₀ : AddCircle T) ≠ (b : AddCircle T)) :
    ContDiffAt ℝ ω (fun y : ℝ => translationChart (T := T) b (y : AddCircle T)) y₀ :=
  (contDiff_id.add contDiff_const).contDiffAt.congr_of_eventuallyEq
    (transition_eventuallyEq b hy₀)

/-- ★ **The translation atlas is analytic**: `AddCircle T` is a `C^ω` manifold over `ℝ`. -/
instance instIsManifoldReal : IsManifold 𝓘(ℝ, ℝ) ω (AddCircle T) := by
  refine isManifold_of_contDiffOn 𝓘(ℝ, ℝ) ω (AddCircle T) ?_
  rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id_eq, id, Function.comp_id, Function.id_comp]
  intro y hy
  have hy' : (y : AddCircle T) ≠ (b : AddCircle T) := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      translationChart_target, translationChart_symm_apply, Set.mem_inter_iff, Set.mem_preimage,
      translationChart_source, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    exact hy.2
  exact (contDiffAt_transition b hy').contDiffWithinAt

/-- ★ **The derivative of every chart transition is the identity**, in the form the
local-representative machinery of `ExteriorDerivative.lean` reads it. No membership hypothesis is
needed: a chart is a section of the quotient map on the whole circle, so the point read back is
`y` itself, which avoids its own cut point. -/
theorem fderiv_chart_transition (x₀ y : AddCircle T) :
    fderiv ℝ (chartAt ℝ y ∘ (chartAt ℝ x₀).symm) (chartAt ℝ x₀ y)
      = ContinuousLinearMap.id ℝ ℝ := by
  rw [chartAt_eq, chartAt_eq, transition_eq]
  refine (hasFDerivAt_transition (cutPoint y) ?_).fderiv
  rw [coe_translationChart]
  exact ne_coe_cutPoint y

end AddCircle

end
