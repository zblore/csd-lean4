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
the Mathlib-gaps register; the source repository's terms register records what is backed and what is
not.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`, the
`## TODO` of `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`).

A differential form on a manifold (`DifferentialForm.lean`) is a smooth
section of the alternating bundle on the tangent bundle. Its exterior derivative is defined
chart by chart and glued by the flat naturality lemma `extDeriv_pullback`:

* `DifferentialForm.localRep s x₀` — the **local representative** of a family `s` of
  alternating maps in the chart at `x₀`: an unbundled flat form on the model space;
**Naming.** `mextDerivFamily` acts on families `s : ∀ x, TₓM [⋀^k]→L ℝ`;
`DifferentialForm.mextDeriv` is the bundled operator on `C^∞` forms. (Until 2026-09-16 the family
operator was a root `mextDeriv`, which the bundled name shadowed inside
`namespace DifferentialForm`; external review asked for distinct names.)

* `mextDerivFamily s x` — **the exterior derivative** of a family `s : ∀ x, TₓM [⋀^k]→L ℝ`: the
  flat `extDeriv` of the local
  representative in the chart at `x`, read at `x` (the tangent space at `x` is the model
  space definitionally, so no transport is needed at the base point);
* ★ `DifferentialForm.trivializationAt_snd` — the trivialisation of a section value is the
  pullback along the derivative of the chart transition (`VectorBundleCore.trivializationAt_symmL`
  and `tangentBundleCore_coordChange_achart`, read on the model);
* ★ `DifferentialForm.localRep_transition` — local representatives in two charts differ by the
  pullback along the transition (the tangent-bundle cocycle `VectorBundleCore.coordChange_comp`);
* ★★ `DifferentialForm.localRep_mextDerivFamily` — **the local representative of `d s` is the flat
  `d` of the local representative of `s`**, in every chart, at every point of the chart. This
  is where `extDeriv_pullback` is spent, and it is the whole content of chart-independence;
* ★★ `contMDiff_mextDerivFamily` — `d` of a `C^∞` section is a `C^∞` section, so `d` iterates:
  `DifferentialForm.mextDeriv` is the bundled operator
  `DifferentialForm 𝓘(ℝ, E) M ∞ (Fin k) G → DifferentialForm 𝓘(ℝ, E) M ∞ (Fin (k+1)) G`;
* ★★ `mextDerivFamily_mextDerivFamily`, `DifferentialForm.mextDeriv_mextDeriv` — **`d ∘ d = 0`**,
  transported from `extDeriv_extDeriv_apply`;
* **`0`-forms:** `zeroFormFamily f`
  (a function `f : M → G` as a `0`-form family), `localRep_zeroFormFamily`,
  `contMDiff_zeroFormFamily` (the section is `C^∞` when `f` is), the bundled `zeroForm f hf`, and
  ★ `toFlat_mextDerivFamily_zeroFormFamily` / `toFlat_mextDeriv_zeroForm` — **the exterior
  derivative
  of a `0`-form is its differential**, `(df)_x = ofSubsingleton 0 (mfderiv f x)`, transported from
  `extDeriv_constOfIsEmpty`.

The design decisions the scoping note's §4 asked for, all taken the cheap way:

* **real, boundaryless model** `𝓘(ℝ, E)` — every finite-dimensional real manifold this tree
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
manifolds, linearity, and the Leibniz rule (which needs the wedge of *sections*).

⚠️ **The chart at `x` is `chartAt E x`**, the atlas's own choice. `mextDerivFamily` is defined
through
it; `localRep_mextDerivFamily` is what shows the value is the same in every chart.

**Provenance and references.** The exterior-derivative plan (the plan, and its §3a on why the
"walls" recorded before this file were not walls); `Geometry/Manifold/DifferentialForm.lean`
(step (2a)); `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (`extDeriv`,
`extDeriv_pullback`, `extDeriv_extDeriv_apply`); the Mathlib-gaps register (Kahler / symplectic
manifold API); the backlog (XL, "Manifold exterior calculus"); the completed-work ledger.
Consumers: `Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (`fsForm_mextDeriv`);
`Geometry/Manifold/HamiltonianVectorField.lean` (`IsHamiltonianVectorField.isLocallyHamiltonian`,
the
`0`-form API).
-/

@[expose] public section

open Bundle Filter Topology Set
open scoped Manifold Bundle Topology ContDiff

noncomputable section

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

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

omit [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The chart transition, as `extChartAt` sees it, is the chart transition. -/
theorem extChartAt_comp_symm_eq (x₀ y : M) :
    (extChartAt (𝓘(ℝ, E)) y ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm)
      = (chartAt E y ∘ (chartAt E x₀).symm) := by
  funext w
  simp

omit [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The transition from any atlas chart `e` to the chart at `y`, as `extChartAt` and `extend` see
it, is the chart transition. -/
theorem extChartAt_comp_extend_symm_eq (e : atlas E M) (y : M) :
    (extChartAt (𝓘(ℝ, E)) y ∘ (e.1.extend (𝓘(ℝ, E))).symm) = (chartAt E y ∘ e.1.symm) := by
  funext w
  simp

/-- The tangent trivialisation of any atlas chart `e`, read at `y ∈ e.source`, is the derivative
of the transition from `e` to the chart at `y` (`VectorBundleCore.localTriv_symmL`);
`tangent_symmL_eq_fderiv` is the case `e = achart E x₀`. -/
theorem tangent_localTriv_symmL_eq_fderiv (e : atlas E M) (y : M) (hy : y ∈ e.1.source) :
    ((tangentBundleCore (𝓘(ℝ, E)) M).localTriv e).symmL ℝ y
      = fderiv ℝ (chartAt E y ∘ e.1.symm) (e.1 y) := by
  have hy' : y ∈ ((tangentBundleCore (𝓘(ℝ, E)) M).localTriv e).baseSet := hy
  rw [VectorBundleCore.localTriv_symmL _ hy']
  show fderivWithin ℝ (extChartAt (𝓘(ℝ, E)) y ∘ (e.1.extend (𝓘(ℝ, E))).symm)
      (Set.range (𝓘(ℝ, E))) (e.1.extend (𝓘(ℝ, E)) y) = _
  rw [extChartAt_comp_extend_symm_eq, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

/-- The tangent coordinate change from the chart at `x₀` to the chart at `y` is the derivative
of the chart transition. -/
theorem tangent_symmL_eq_fderiv (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀).symmL ℝ y
      = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) := by
  have hy' : y ∈ (trivializationAt E
      (tangentBundleCore (𝓘(ℝ, E)) M).Fiber x₀).baseSet := hy
  show (trivializationAt E (tangentBundleCore (𝓘(ℝ, E)) M).Fiber x₀).symmL ℝ y = _
  rw [VectorBundleCore.trivializationAt_symmL _ hy']
  show fderivWithin ℝ (extChartAt (𝓘(ℝ, E)) y ∘
      (extChartAt (𝓘(ℝ, E)) x₀).symm)
      (Set.range (𝓘(ℝ, E))) (extChartAt (𝓘(ℝ, E)) x₀ y) = _
  rw [extChartAt_comp_symm_eq, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

/-- Chart transitions are `C^∞` where defined. -/
theorem contDiffAt_chart_transition (x₀ y : M) {w : E} (hw : w ∈ (chartAt E x₀).target)
    (hy : (chartAt E x₀).symm w ∈ (chartAt E y).source) :
    ContDiffAt ℝ ∞ (chartAt E y ∘ (chartAt E x₀).symm) w := by
  rw [← contMDiffAt_iff_contDiffAt]
  have h1 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
      (chartAt E x₀).symm w :=
    (contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt
      ((chartAt E x₀).open_target.mem_nhds hw)
  have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
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
  have h := (tangentBundleCore (𝓘(ℝ, E)) M).coordChange_comp
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
    (α : TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) :
    E [⋀^ι]→L[ℝ] G := α

/-- **The local representative** of a family of alternating maps in the chart at `x₀`: an
unbundled flat form on the model space. Outside the chart's target it is junk; every use is at
a point of the target. -/
def localRep (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ]
    Bundle.Trivial M G x) (x₀ : M) : E → E [⋀^ι]→L[ℝ] G :=
  fun w => (trivializationAt (E [⋀^ι]→L[ℝ] G)
    (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
    ⟨(chartAt E x₀).symm w, s ((chartAt E x₀).symm w)⟩).2

end DifferentialForm

open DifferentialForm

/-- **The exterior derivative** of a family of alternating maps on the tangent spaces: the flat
`extDeriv` of its local representative in the chart at `x`, read at `x`. -/
def mextDerivFamily (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x) (x : M) :
    TangentSpace (𝓘(ℝ, E)) x [⋀^Fin (k + 1)]→L[ℝ] Bundle.Trivial M G x :=
  (extDeriv (localRep s x) (chartAt E x x) : E [⋀^Fin (k + 1)]→L[ℝ] G)

namespace DifferentialForm

theorem toFlat_mextDerivFamily
    (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x) (x : M) :
    toFlat (mextDerivFamily s x) = extDeriv (localRep s x) (chartAt E x x) := rfl

omit [DecidableEq ι] in
/-- ★ The trivialisation of a section value, on the model: pull back along the derivative of
the chart transition. -/
theorem trivializationAt_snd (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ]
    Bundle.Trivial M G x) (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
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
      (trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀).symmL ℝ y u
        = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u :=
    fun u => congrArg (fun L => L u) (tangent_symmL_eq_fderiv x₀ y hy)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousLinearMap.id_apply]
  have hfun : (⇑((trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀).symmL ℝ y) ∘ v)
      = (⇑(fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y)) ∘ v) :=
    funext fun i => hS (v i)
  exact congrArg (fun g => (toFlat (s y)) g) hfun

omit [DecidableEq ι] in
/-- ★ Local representatives in two charts differ by the pullback along the transition. -/
theorem localRep_transition (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ]
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
    (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (hs : ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^ι]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) x (s x)))
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    ContDiffAt ℝ ∞ (localRep s x₀) w := by
  rw [← contMDiffAt_iff_contDiffAt]
  have hy : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have h1 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E [⋀^ι]→L[ℝ] G)) ∞
      (fun x => (trivializationAt (E [⋀^ι]→L[ℝ] G)
        (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
        x₀ ⟨x, s x⟩).2) ((chartAt E x₀).symm w) :=
    ((trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
      x₀).contMDiffAt_section_iff ⟨hy, Set.mem_univ _⟩).mp (hs _)
  have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
      (chartAt E x₀).symm w :=
    (contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt
      ((chartAt E x₀).open_target.mem_nhds hw)
  exact h1.comp w h2

variable (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x)

/-- ★★ **The local representative of `d s` is the flat `d` of the local representative of
`s`**, in every chart, at every point of its target. Chart-independence of `mextDerivFamily`, in the
only form a consumer needs; `extDeriv_pullback` is spent here. -/
theorem localRep_mextDerivFamily
    (hs : ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (s x)))
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    localRep (mextDerivFamily s) x₀ w = extDeriv (localRep s x₀) w := by
  have hy₀ : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have hwy : chartAt E x₀ ((chartAt E x₀).symm w) = w := (chartAt E x₀).right_inv hw
  show (trivializationAt (E [⋀^Fin (k + 1)]→L[ℝ] G)
    (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^Fin (k + 1)]→L[ℝ] Bundle.Trivial M G x)
    x₀ ⟨(chartAt E x₀).symm w, mextDerivFamily s ((chartAt E x₀).symm w)⟩).2 = _
  rw [trivializationAt_snd (mextDerivFamily s) x₀ _ hy₀, hwy, toFlat_mextDerivFamily]
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

variable (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^Fin k]→L[ℝ]
    Bundle.Trivial M G x)

/-- ★★ **`d` of a `C^∞` section is a `C^∞` section.** -/
theorem contMDiff_mextDerivFamily
    (hs : ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (s x))) :
    ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] G) x (mextDerivFamily s x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have hc : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (chartAt E x₀) x₀ :=
    contMDiffAt_extChartAt (n := ∞) (I := 𝓘(ℝ, E)) (x := x₀)
  have hd : ContDiffAt ℝ ∞ (extDeriv (localRep s x₀)) (chartAt E x₀ x₀) :=
    (contDiffAt_localRep s hs x₀ (mem_chart_target E x₀)).extDeriv
  have h1 : ContMDiffAt (𝓘(ℝ, E))
      (𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] G)) ∞
      (fun y => extDeriv (localRep s x₀) (chartAt E x₀ y)) x₀ :=
    hd.contMDiffAt.comp x₀ hc
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  have h := localRep_mextDerivFamily s hs x₀ ((chartAt E x₀).map_source hy)
  simp only [localRep] at h
  rw [(chartAt E x₀).left_inv hy] at h
  exact h

/-- ★★ **`d ∘ d = 0`**, pointwise. -/
theorem mextDerivFamily_mextDerivFamily
    (hs : ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (s x))) (x : M) :
    mextDerivFamily (mextDerivFamily s) x = 0 := by
  show extDeriv (localRep (mextDerivFamily s) x) (chartAt E x x) = 0
  have hev : localRep (mextDerivFamily s) x =ᶠ[𝓝 (chartAt E x x)] extDeriv (localRep s x) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with w hw
    exact localRep_mextDerivFamily s hs x hw
  rw [hev.extDeriv_eq]
  exact extDeriv_extDeriv_apply (contDiffAt_localRep s hs x (mem_chart_target E x))
    minSmoothness_two_le_infty

namespace DifferentialForm

/-- ★★ **The exterior derivative on differential forms**, as an operator
`DifferentialForm 𝓘(ℝ, E) M ∞ (Fin k) G → DifferentialForm 𝓘(ℝ, E) M ∞ (Fin (k + 1)) G`. -/
def mextDeriv (α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin k) G) :
    DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin (k + 1)) G :=
  ⟨mextDerivFamily (fun x => α x), contMDiff_mextDerivFamily _ α.contMDiff_toFun⟩

@[simp] theorem mextDeriv_apply (α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin k) G)
    (x : M) : α.mextDeriv x = mextDerivFamily (fun x => α x) x := rfl

/-- ★★ **`d ∘ d = 0`** on differential forms. -/
theorem mextDeriv_mextDeriv (α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin k) G) :
    α.mextDeriv.mextDeriv = 0 := by
  apply ContMDiffSection.ext
  intro x
  exact mextDerivFamily_mextDerivFamily _ α.contMDiff_toFun x

end DifferentialForm

/-! ### `0`-forms: the exterior derivative is the differential -/

namespace DifferentialForm

/-- A function `f : M → G` as a `0`-form family, `x ↦ constOfIsEmpty (f x)`. -/
def zeroFormFamily (f : M → G) (x : M) :
    TangentSpace (𝓘(ℝ, E)) x [⋀^Fin 0]→L[ℝ] Bundle.Trivial M G x :=
  (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f x) : E [⋀^Fin 0]→L[ℝ] G)

theorem trivializationAt_zeroFormFamily_snd (f : M → G) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^Fin 0]→L[ℝ] G)
      (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^Fin 0]→L[ℝ] Bundle.Trivial M G x)
      x₀ ⟨y, zeroFormFamily (E := E) f y⟩).2
      = ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f y) := by
  rw [trivializationAt_snd _ x₀ y hy]
  ext v
  simp [zeroFormFamily]

/-- The local representative of a `0`-form family is the function read in the chart. -/
theorem localRep_zeroFormFamily (f : M → G) (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    localRep (zeroFormFamily (E := E) f) x₀ w
      = ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f ((chartAt E x₀).symm w)) :=
  trivializationAt_zeroFormFamily_snd f x₀ _ ((chartAt E x₀).map_target hw)

/-- The `0`-form family of a `C^∞` function is a `C^∞` section. -/
theorem contMDiff_zeroFormFamily {f : M → G}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, G)) ∞ f) :
    ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^Fin 0]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin 0]→L[ℝ] G) x (zeroFormFamily (E := E) f x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have h1 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E [⋀^Fin 0]→L[ℝ] G)) ∞
      (fun x : M => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f x)) x₀ :=
    ((ContinuousAlternatingMap.constOfIsEmptyLIE (𝕜 := ℝ) (E := E) G (Fin 0)).contDiff.contDiffAt
      (x := f x₀)).contMDiffAt.comp x₀ (hf x₀)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_zeroFormFamily_snd f x₀ y hy

/-- ★ **The exterior derivative of a `0`-form is its differential**: for `f` differentiable at
`x`, `d (zeroFormFamily f) x = ofSubsingleton 0 (mfderiv f x)`, i.e. `(df)_x v = mfderiv f x (v 0)`.
Stated on the model, as every identity of this file is. -/
theorem toFlat_mextDerivFamily_zeroFormFamily {f : M → G} {x : M}
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, G)) f x) :
    toFlat (mextDerivFamily (zeroFormFamily (E := E) f) x)
      = ContinuousAlternatingMap.ofSubsingleton ℝ E G (0 : Fin 1)
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, G)) f x) := by
  rw [toFlat_mextDerivFamily]
  have hev : localRep (zeroFormFamily (E := E) f) x =ᶠ[𝓝 (chartAt E x x)]
      fun w => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f ((chartAt E x).symm w)) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with w hw
    exact localRep_zeroFormFamily f x hw
  rw [hev.extDeriv_eq, extDeriv_constOfIsEmpty]
  congr 1
  rw [hf.mfderiv]
  -- `MDifferentiableAt.mfderiv` reads `mfderiv f x` as the chart-space `fderivWithin`; on
  -- newer Mathlib it wraps that in the definitional `tangentSpaceCastModel` identifications,
  -- and this `change` strips them (a syntactic no-op where they are absent).
  change _ = fderivWithin ℝ (writtenInExtChartAt (𝓘(ℝ, E))
    (𝓘(ℝ, G)) x f) (Set.range (𝓘(ℝ, E)))
    ((extChartAt (𝓘(ℝ, E)) x) x)
  simp only [writtenInExtChartAt, Function.comp_def, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id, extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Set.range_id, fderivWithin_univ]

/-- A `C^∞` function as a `0`-form. -/
def zeroForm (f : M → G)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, G)) ∞ f) :
    DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 0) G :=
  ⟨zeroFormFamily (E := E) f, contMDiff_zeroFormFamily hf⟩

/-- ★ `d f` is the differential of `f`, for the bundled `0`-form. -/
theorem toFlat_mextDeriv_zeroForm {f : M → G}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, G)) ∞ f) (x : M) :
    toFlat ((zeroForm f hf).mextDeriv x)
      = ContinuousAlternatingMap.ofSubsingleton ℝ E G (0 : Fin 1)
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, G)) f x) :=
  toFlat_mextDerivFamily_zeroFormFamily ((hf x).mdifferentiableAt (by simp))

end DifferentialForm

/-! ### Analytic sections have analytic local representatives (G19) -/

namespace DifferentialForm

/-- ★ A `C^ω` section has `C^ω` local representatives (on the chart's target): the proof of
`contDiffAt_localRep` at `ω`, on an analytic manifold. -/
theorem contDiffAt_omega_localRep [IsManifold (𝓘(ℝ, E)) ω M]
    (s : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (hs : ContMDiff (𝓘(ℝ, E))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E [⋀^ι]→L[ℝ] G))) ω
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) x (s x)))
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    ContDiffAt ℝ ω (localRep s x₀) w := by
  rw [← contMDiffAt_iff_contDiffAt]
  have hy : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have h1 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E [⋀^ι]→L[ℝ] G)) ω
      (fun x => (trivializationAt (E [⋀^ι]→L[ℝ] G)
        (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
        x₀ ⟨x, s x⟩).2) ((chartAt E x₀).symm w) :=
    ((trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace (𝓘(ℝ, E)) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
      x₀).contMDiffAt_section_iff ⟨hy, Set.mem_univ _⟩).mp (hs _)
  have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ω
      (chartAt E x₀).symm w :=
    (contMDiffOn_chart_symm (n := ω) (x := x₀)).contMDiffAt
      ((chartAt E x₀).open_target.mem_nhds hw)
  exact h1.comp w h2

end DifferentialForm
