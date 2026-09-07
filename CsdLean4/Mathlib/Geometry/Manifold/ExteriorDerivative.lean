/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.DifferentialForm
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# The exterior derivative on a manifold

**TERM-SCOPE(Kahler)** — this module names the "Kahler / symplectic manifold API" row of
`MATHLIB-GAPS.md`; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`, the
`## TODO` of `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`).

**Step (2b) of the manifold exterior-calculus plan** (`specs/exterior-derivative-scoping.md`,
route A). A differential form on a manifold (`DifferentialForm.lean`, step (2a)) is a smooth
section of the alternating bundle on the tangent bundle. Its exterior derivative is defined
chart by chart and glued by the flat naturality lemma `extDeriv_pullback`:

* `DifferentialForm.localRep s x₀` — the **local representative** of a family `s` of
  alternating maps in the chart at `x₀`: an unbundled flat form on the model space;
* `mextDeriv s x` — **the exterior derivative**: the flat `extDeriv` of the local
  representative in the chart at `x`, read at `x` (the tangent space at `x` is the model
  space definitionally, so no transport is needed at the base point);
* ★ `DifferentialForm.trivializationAt_snd` — the trivialisation of a section value is the
  pullback along the derivative of the chart transition (`VectorBundleCore.trivializationAt_symmL`
  and `tangentBundleCore_coordChange_achart`, read on the model);
* ★ `DifferentialForm.localRep_transition` — local representatives in two charts differ by the
  pullback along the transition (the tangent-bundle cocycle `VectorBundleCore.coordChange_comp`);
* ★★ `DifferentialForm.localRep_mextDeriv` — **the local representative of `d s` is the flat
  `d` of the local representative of `s`**, in every chart, at every point of the chart. This
  is where `extDeriv_pullback` is spent, and it is the whole content of chart-independence;
* ★★ `contMDiff_mextDeriv` — `d` of a `C^∞` section is a `C^∞` section, so `d` iterates:
  `DifferentialForm.mextDeriv` is the bundled operator
  `DifferentialForm 𝓘(ℝ, E) M ∞ (Fin k) G → DifferentialForm 𝓘(ℝ, E) M ∞ (Fin (k+1)) G`;
* ★★ `mextDeriv_mextDeriv`, `DifferentialForm.mextDeriv_mextDeriv` — **`d ∘ d = 0`**,
  transported from `extDeriv_extDeriv_apply`.

The design decisions the scoping note's §4 asked for, all taken the cheap way:

* **real, boundaryless model** `𝓘(ℝ, E)` — every finite-dimensional real manifold the corpus
  uses, `ℂℙⁿ` included; `range 𝓘 = univ`, so `fderivWithin` is `fderiv` and no `UniqueDiffOn`
  is ever supplied; `minSmoothness ℝ 2 = 2`;
* **smoothness `∞` only** — `d` of `C^∞` is `C^∞`, and no `n - 1` arithmetic leaks anywhere;
* **degrees `Fin k`** — the flat `extDeriv` is `Fin k → Fin (k + 1)`;
* **`toFlat`**, a definitional cast from the fibre `TₓM [⋀^k]→L G` to the model fibre, so that
  every identity is *stated* on the model space and rewriting never has to cross the
  `TangentSpace`-vs-model instance path (that crossing, done pointwise, is what
  `trivializationAt_snd` is for).

## Honest scope

⚠️ **`∞` and `𝓘(ℝ, E)` only.** No `C^n` bookkeeping, no boundary, no other field. A consumer
needing `d` on a `C^n` manifold or on a manifold with corners needs a generalisation, and the
smoothness arithmetic that this file deliberately avoids would come with it.

⚠️ **What is not here:** the Palais formula, naturality `d(f^*ω) = f^*(dω)` for maps of
manifolds, linearity, `d` of a `0`-form as the differential, and the Leibniz rule (which needs
the wedge of *sections*; `specs/exterior-derivative-scoping.md` §5).

⚠️ **The chart at `x` is `chartAt E x`**, the atlas's own choice. `mextDeriv` is defined through
it; `localRep_mextDeriv` is what shows the value is the same in every chart.

References: `specs/exterior-derivative-scoping.md` (the plan, and its §3a on why the
"walls" recorded before this file were not walls); `Geometry/Manifold/DifferentialForm.lean`
(step (2a)); `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (`extDeriv`,
`extDeriv_pullback`, `extDeriv_extDeriv_apply`); `MATHLIB-GAPS.md` (Kahler / symplectic
manifold API); `specs/BACKLOG.md` (XL, "Manifold exterior calculus"); `specs/future-work.md`.
Consumer: `Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (`fsForm_mextDeriv`).
-/

@[expose] public section

open Bundle Filter Topology Set
open scoped Manifold Bundle Topology ContDiff

noncomputable section

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over `ℝ`, the smoothness the flat pullback and `d² = 0` lemmas ask for is `2`. -/
theorem minSmoothness_two_le_infty : minSmoothness ℝ 2 ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  norm_cast

/-- Flat lemma: `extDeriv` of a `C^∞` form is `C^∞` (it is a continuous linear map applied to
the derivative of the form). -/
theorem ContDiffAt.extDeriv {s : E → E [⋀^Fin k]→L[ℝ] G} {w : E}
    (h : ContDiffAt ℝ ∞ s w) : ContDiffAt ℝ ∞ (_root_.extDeriv s) w := by
  have hrepr : _root_.extDeriv s
      = fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E G (fderiv ℝ s x) := by
    funext x; rw [_root_.extDeriv, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  rw [hrepr]
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ s) w := h.fderiv_right (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E G).contDiff.contDiffAt.comp w hfd

omit [IsManifold (modelWithCornersSelf ℝ E) ∞ M] in
/-- The chart transition, as `extChartAt` sees it, is the chart transition. -/
theorem extChartAt_comp_symm_eq (x₀ y : M) :
    (extChartAt (modelWithCornersSelf ℝ E) y ∘ (extChartAt (modelWithCornersSelf ℝ E) x₀).symm)
      = (chartAt E y ∘ (chartAt E x₀).symm) := by
  funext w
  simp

/-- The tangent coordinate change from the chart at `x₀` to the chart at `y` is the derivative
of the chart transition. -/
theorem tangent_symmL_eq_fderiv (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ y
      = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) := by
  have hy' : y ∈ (trivializationAt E
      (tangentBundleCore (modelWithCornersSelf ℝ E) M).Fiber x₀).baseSet := hy
  show (trivializationAt E (tangentBundleCore (modelWithCornersSelf ℝ E) M).Fiber x₀).symmL ℝ y = _
  rw [VectorBundleCore.trivializationAt_symmL _ hy']
  show fderivWithin ℝ (extChartAt (modelWithCornersSelf ℝ E) y ∘
      (extChartAt (modelWithCornersSelf ℝ E) x₀).symm)
      (Set.range (modelWithCornersSelf ℝ E)) (extChartAt (modelWithCornersSelf ℝ E) x₀ y) = _
  rw [extChartAt_comp_symm_eq, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

/-- Chart transitions are `C^∞` where defined. -/
theorem contDiffAt_chart_transition (x₀ y : M) {w : E} (hw : w ∈ (chartAt E x₀).target)
    (hy : (chartAt E x₀).symm w ∈ (chartAt E y).source) :
    ContDiffAt ℝ ∞ (chartAt E y ∘ (chartAt E x₀).symm) w := by
  rw [← contMDiffAt_iff_contDiffAt]
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (chartAt E x₀).symm w :=
    (contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt
      ((chartAt E x₀).open_target.mem_nhds hw)
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (chartAt E y) ((chartAt E x₀).symm w) :=
    (contMDiffOn_chart (n := ∞) (x := y)).contMDiffAt ((chartAt E y).open_source.mem_nhds hy)
  exact h2.comp w h1

/-- The cocycle: derivatives of chart transitions compose (`VectorBundleCore.coordChange_comp`
for the tangent bundle, read on the model). -/
theorem fderiv_chart_transition_comp (x₀ y z : M) (hz₀ : z ∈ (chartAt E x₀).source)
    (hzy : z ∈ (chartAt E y).source) :
    fderiv ℝ (chartAt E z ∘ (chartAt E x₀).symm) (chartAt E x₀ z)
      = (fderiv ℝ (chartAt E z ∘ (chartAt E y).symm) (chartAt E y z)).comp
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ z)) := by
  have h := (tangentBundleCore (modelWithCornersSelf ℝ E) M).coordChange_comp
    (achart E x₀) (achart E y) (achart E z) z ⟨⟨hz₀, hzy⟩, mem_chart_source E z⟩
  ext v
  have hv := h v
  simp only [tangentBundleCore_coordChange_achart, extChartAt_comp_symm_eq,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ] at hv
  rw [ContinuousLinearMap.comp_apply]
  exact hv.symm

namespace DifferentialForm

/-- Definitional identification of the fibre `TₓM [⋀^k]→L G` with the model fibre. -/
abbrev toFlat {x : M}
    (α : TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) :
    E [⋀^ι]→L[ℝ] G := α

/-- **The local representative** of a family of alternating maps in the chart at `x₀`: an
unbundled flat form on the model space. Outside the chart's target it is junk; every use is at
a point of the target. -/
def localRep (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ]
    Bundle.Trivial M G x) (x₀ : M) : E → E [⋀^ι]→L[ℝ] G :=
  fun w => (trivializationAt (E [⋀^ι]→L[ℝ] G)
    (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
    ⟨(chartAt E x₀).symm w, s ((chartAt E x₀).symm w)⟩).2

end DifferentialForm

open DifferentialForm

/-- **The exterior derivative** of a family of alternating maps on the tangent spaces: the flat
`extDeriv` of its local representative in the chart at `x`, read at `x`. -/
def mextDeriv (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x) (x : M) :
    TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin (k + 1)]→L[ℝ] Bundle.Trivial M G x :=
  (extDeriv (localRep s x) (chartAt E x x) : E [⋀^Fin (k + 1)]→L[ℝ] G)

namespace DifferentialForm

theorem toFlat_mextDeriv (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x) (x : M) :
    toFlat (mextDeriv s x) = extDeriv (localRep s x) (chartAt E x x) := rfl

omit [DecidableEq ι] in
/-- ★ The trivialisation of a section value, on the model: pull back along the derivative of
the chart transition. -/
theorem trivializationAt_snd (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ]
    Bundle.Trivial M G x) (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
      ⟨y, s y⟩).2
      = (toFlat (s y)).compContinuousLinearMap
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y)) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  simp only [ContinuousAlternatingMap.inCoordinates]
  have hclm : (trivializationAt G (Bundle.Trivial M G) x₀).continuousLinearMapAt ℝ y
      = ContinuousLinearMap.id ℝ G := by
    show (Bundle.Trivial.trivialization M G).continuousLinearMapAt ℝ y = _
    simp
  rw [hclm]
  ext v
  have hS : ∀ u : E,
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ y u
        = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u :=
    fun u => congrArg (fun L => L u) (tangent_symmL_eq_fderiv x₀ y hy)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousLinearMap.id_apply]
  have hfun : (⇑((trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ y) ∘ v)
      = (⇑(fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y)) ∘ v) :=
    funext fun i => hS (v i)
  exact congrArg (fun g => (toFlat (s y)) g) hfun

omit [DecidableEq ι] in
/-- ★ Local representatives in two charts differ by the pullback along the transition. -/
theorem localRep_transition (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ]
    Bundle.Trivial M G x) (x₀ y : M) {w : E} (hw : w ∈ (chartAt E x₀).target)
    (hy : (chartAt E x₀).symm w ∈ (chartAt E y).source) :
    localRep s x₀ w
      = (localRep s y (chartAt E y ((chartAt E x₀).symm w))).compContinuousLinearMap
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w) := by
  have hz₀ : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have hwz : chartAt E x₀ ((chartAt E x₀).symm w) = w := (chartAt E x₀).right_inv hw
  have hyz : (chartAt E y).symm (chartAt E y ((chartAt E x₀).symm w)) = (chartAt E x₀).symm w :=
    (chartAt E y).left_inv hy
  simp only [localRep]
  rw [hyz, trivializationAt_snd s x₀ _ hz₀, trivializationAt_snd s y _ hy, hwz]
  have hc := fderiv_chart_transition_comp x₀ y ((chartAt E x₀).symm w) hz₀ hy
  rw [hwz] at hc
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact congrArg (fun g => (toFlat (s ((chartAt E x₀).symm w))) g)
    (funext fun i => congrArg (fun L => L (v i)) hc)

/-- ★ A `C^∞` section has `C^∞` local representatives (on the chart's target). -/
theorem contDiffAt_localRep
    (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) x (s x)))
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    ContDiffAt ℝ ∞ (localRep s x₀) w := by
  rw [← contMDiffAt_iff_contDiffAt]
  have hy : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] G)) ∞
      (fun x => (trivializationAt (E [⋀^ι]→L[ℝ] G)
        (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
        x₀ ⟨x, s x⟩).2) ((chartAt E x₀).symm w) :=
    ((trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
      x₀).contMDiffAt_section_iff ⟨hy, Set.mem_univ _⟩).mp (hs _)
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (chartAt E x₀).symm w :=
    (contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt
      ((chartAt E x₀).open_target.mem_nhds hw)
  exact h1.comp w h2

variable (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x)

/-- ★★ **The local representative of `d s` is the flat `d` of the local representative of
`s`**, in every chart, at every point of its target. Chart-independence of `mextDeriv`, in the
only form a consumer needs; `extDeriv_pullback` is spent here. -/
theorem localRep_mextDeriv
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^Fin k]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (s x)))
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    localRep (mextDeriv s) x₀ w = extDeriv (localRep s x₀) w := by
  have hy₀ : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have hwy : chartAt E x₀ ((chartAt E x₀).symm w) = w := (chartAt E x₀).right_inv hw
  show (trivializationAt (E [⋀^Fin (k + 1)]→L[ℝ] G)
    (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin (k + 1)]→L[ℝ] Bundle.Trivial M G x)
    x₀ ⟨(chartAt E x₀).symm w, mextDeriv s ((chartAt E x₀).symm w)⟩).2 = _
  rw [trivializationAt_snd (mextDeriv s) x₀ _ hy₀, hwy, toFlat_mextDeriv]
  -- the chart of `y` at `y` is the transition applied to `w`
  have hτ : chartAt E ((chartAt E x₀).symm w) ((chartAt E x₀).symm w)
      = (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w := rfl
  rw [hτ]
  have hdiff : DifferentiableAt ℝ (localRep s ((chartAt E x₀).symm w))
      ((chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w) :=
    (contDiffAt_localRep s hs _ (mem_chart_target E _)).differentiableAt (by simp)
  rw [← extDeriv_pullback (f := chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) (x := w)
    hdiff (contDiffAt_chart_transition x₀ _ hw (mem_chart_source E _)) minSmoothness_two_le_infty]
  apply Filter.EventuallyEq.extDeriv_eq
  have hnhds : ∀ᶠ w' in 𝓝 w, w' ∈ (chartAt E x₀).target ∧
      (chartAt E x₀).symm w' ∈ (chartAt E ((chartAt E x₀).symm w)).source := by
    filter_upwards [(chartAt E x₀).open_target.mem_nhds hw,
      ((chartAt E x₀).continuousAt_symm hw).preimage_mem_nhds
        ((chartAt E ((chartAt E x₀).symm w)).open_source.mem_nhds (mem_chart_source E _))]
      with w' h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hnhds] with w' hw'
  exact (localRep_transition s x₀ _ hw'.1 hw'.2).symm

end DifferentialForm

variable (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x)

/-- ★★ **`d` of a `C^∞` section is a `C^∞` section.** -/
theorem contMDiff_mextDeriv
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^Fin k]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (s x))) :
    ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^Fin (k + 1)]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] G) x (mextDeriv s x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have hc : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ (chartAt E x₀) x₀ :=
    contMDiffAt_extChartAt (n := ∞) (I := modelWithCornersSelf ℝ E) (x := x₀)
  have hd : ContDiffAt ℝ ∞ (extDeriv (localRep s x₀)) (chartAt E x₀ x₀) :=
    (contDiffAt_localRep s hs x₀ (mem_chart_target E x₀)).extDeriv
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ (E [⋀^Fin (k + 1)]→L[ℝ] G)) ∞
      (fun y => extDeriv (localRep s x₀) (chartAt E x₀ y)) x₀ :=
    hd.contMDiffAt.comp x₀ hc
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  have h := localRep_mextDeriv s hs x₀ ((chartAt E x₀).map_source hy)
  simp only [localRep] at h
  rw [(chartAt E x₀).left_inv hy] at h
  exact h

/-- ★★ **`d ∘ d = 0`**, pointwise. -/
theorem mextDeriv_mextDeriv
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^Fin k]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (s x))) (x : M) :
    mextDeriv (mextDeriv s) x = 0 := by
  show extDeriv (localRep (mextDeriv s) x) (chartAt E x x) = 0
  have hev : localRep (mextDeriv s) x =ᶠ[𝓝 (chartAt E x x)] extDeriv (localRep s x) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with w hw
    exact localRep_mextDeriv s hs x hw
  rw [hev.extDeriv_eq]
  exact extDeriv_extDeriv_apply (contDiffAt_localRep s hs x (mem_chart_target E x))
    minSmoothness_two_le_infty

namespace DifferentialForm

/-- ★★ **The exterior derivative on differential forms**, as an operator
`DifferentialForm 𝓘(ℝ, E) M ∞ (Fin k) G → DifferentialForm 𝓘(ℝ, E) M ∞ (Fin (k + 1)) G`. -/
def mextDeriv (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin k) G) :
    DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin (k + 1)) G :=
  ⟨_root_.mextDeriv (fun x => α x), contMDiff_mextDeriv _ α.contMDiff_toFun⟩

@[simp] theorem mextDeriv_apply (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin k) G)
    (x : M) : α.mextDeriv x = _root_.mextDeriv (fun x => α x) x := rfl

/-- ★★ **`d ∘ d = 0`** on differential forms. -/
theorem mextDeriv_mextDeriv (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin k) G) :
    α.mextDeriv.mextDeriv = 0 := by
  apply ContMDiffSection.ext
  intro x
  exact _root_.mextDeriv_mextDeriv _ α.contMDiff_toFun x

end DifferentialForm
