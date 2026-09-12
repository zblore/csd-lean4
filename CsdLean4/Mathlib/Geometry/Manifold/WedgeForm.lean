/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ExteriorDerivative
public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.WedgeCLM

/-!
# The wedge of differential forms on a manifold

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

Milestone **M2(c)–(d)** of `specs/top-power-scoping.md`. With the flat wedge bounded and
bilinear (`Alternating/WedgeCLM.lean`) and the local-representative machinery of
`ExteriorDerivative.lean`, the wedge of two smooth sections of alternating bundles is a smooth
section, and so is a reindexing and the constant `0`-form. Every smoothness proof is the same
three lines: the trivialisation of the new section in the chart at `x₀` is the flat operation
applied to the local representatives (`trivializationAt_*_snd`, from `trivializationAt_snd` and
the flat "commutes with pullback" lemma), the flat operation is `C^∞` in its arguments, and
`contMDiffAt_section` closes.

* `DifferentialForm.wedgeFamily`, ★ `trivializationAt_wedgeFamily_snd`, `localRep_wedgeFamily`,
  ★★ `contMDiff_wedgeFamily`, and the bundled ★★ `DifferentialForm.wedge B α β` — **the wedge of
  two differential forms**, an `(ιa ⊕ ιb)`-form;
* `domDomCongrFamily`, `trivializationAt_domDomCongrFamily_snd`, `contMDiff_domDomCongrFamily`,
  and ★ `DifferentialForm.domDomCongr σ α` — reindexing along an equivalence of index types
  (what brings `ιa ⊕ ιb` back to `Fin (a + b)`);
* `constZeroFamily`, `contMDiff_constZeroFamily`, `DifferentialForm.constZero c` — the constant
  `0`-form;
* ★★ `DifferentialForm.wedgePow α k` — **the `k`-th exterior power of a real 2-form**, a
  `2k`-form, by recursion (`powEquiv k : Fin (2k) ⊕ Fin 2 ≃ Fin (2(k+1))`); its flat twin
  `ContinuousAlternatingMap.wedgePow` with ★ `wedgePow_compContinuousLinearMap` (pullback
  commutes with the power), `wedgePow_smul` (homogeneity) and ★ `localRep_wedgePow` (the local representative of the power is
  the power of the local representative) — what lifts an invariance of a 2-form to its top power.

## Honest scope

⚠️ **Only the operations.** No algebraic law of the wedge is proved at section level —
associativity, graded commutativity, the Leibniz rule with `mextDeriv` — because none is proved
flat (`Wedge.lean`'s honest scope). `wedgePow` is a definition, and nothing here says it is
nonzero.

⚠️ **`∞` and `𝓘(ℝ, E)` only**, inherited from `ExteriorDerivative.lean`.

References: `specs/top-power-scoping.md` (M2); `Alternating/WedgeCLM.lean`;
`Geometry/Manifold/ExteriorDerivative.lean`; consumer
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (`fsTopForm`);
`specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology Set
open scoped Manifold Bundle Topology ContDiff

noncomputable section

section WedgeForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
  {ιa ιb ι ι' : Type*} [Fintype ιa] [Fintype ιb] [DecidableEq ιa] [DecidableEq ιb]
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

namespace DifferentialForm

/-! ### The wedge of two families -/

/-- The wedge of two families of alternating maps on the tangent spaces, fibrewise. -/
def wedgeFamily (B : F →L[ℝ] G →L[ℝ] H)
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa]→L[ℝ] Bundle.Trivial M F x)
    (β : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιb]→L[ℝ] Bundle.Trivial M G x)
    (x : M) :
    TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa ⊕ ιb]→L[ℝ] Bundle.Trivial M H x :=
  (ContinuousAlternatingMap.wedge B (toFlat (α x)) (toFlat (β x)) : E [⋀^ιa ⊕ ιb]→L[ℝ] H)

omit [IsManifold (modelWithCornersSelf ℝ E) ∞ M] in
theorem toFlat_wedgeFamily (B : F →L[ℝ] G →L[ℝ] H)
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa]→L[ℝ] Bundle.Trivial M F x)
    (β : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιb]→L[ℝ] Bundle.Trivial M G x)
    (x : M) :
    toFlat (wedgeFamily B α β x)
      = ContinuousAlternatingMap.wedge B (toFlat (α x)) (toFlat (β x)) := rfl

/-- ★ In the chart at `x₀`, a wedge trivialises to the wedge of the local representatives. -/
theorem trivializationAt_wedgeFamily_snd (B : F →L[ℝ] G →L[ℝ] H)
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa]→L[ℝ] Bundle.Trivial M F x)
    (β : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιb]→L[ℝ] Bundle.Trivial M G x)
    (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ιa ⊕ ιb]→L[ℝ] H)
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa ⊕ ιb]→L[ℝ] Bundle.Trivial M H x)
      x₀ ⟨y, wedgeFamily B α β y⟩).2
      = ContinuousAlternatingMap.wedge B (localRep α x₀ (chartAt E x₀ y))
          (localRep β x₀ (chartAt E x₀ y)) := by
  have hyy := (chartAt E x₀).left_inv hy
  simp only [localRep]
  rw [hyy, trivializationAt_snd _ x₀ y hy, trivializationAt_snd α x₀ y hy,
    trivializationAt_snd β x₀ y hy, toFlat_wedgeFamily,
    ContinuousAlternatingMap.wedge_compContinuousLinearMap]

/-- ★ The local representative of a wedge is the wedge of the local representatives. -/
theorem localRep_wedgeFamily (B : F →L[ℝ] G →L[ℝ] H)
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa]→L[ℝ] Bundle.Trivial M F x)
    (β : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιb]→L[ℝ] Bundle.Trivial M G x)
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    localRep (wedgeFamily B α β) x₀ w
      = ContinuousAlternatingMap.wedge B (localRep α x₀ w) (localRep β x₀ w) := by
  have h := trivializationAt_wedgeFamily_snd B α β x₀ _ ((chartAt E x₀).map_target hw)
  rw [(chartAt E x₀).right_inv hw] at h
  exact h

/-- ★★ The wedge of two `C^∞` sections is a `C^∞` section. -/
theorem contMDiff_wedgeFamily (B : F →L[ℝ] G →L[ℝ] H)
    {α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιa]→L[ℝ] Bundle.Trivial M F x}
    {β : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ιb]→L[ℝ] Bundle.Trivial M G x}
    (hα : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ιa]→L[ℝ] F))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ιa]→L[ℝ] F) x (α x)))
    (hβ : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ιb]→L[ℝ] G))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ιb]→L[ℝ] G) x (β x))) :
    ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ιa ⊕ ιb]→L[ℝ] H))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ιa ⊕ ιb]→L[ℝ] H) x (wedgeFamily B α β x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have hc : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ (chartAt E x₀) x₀ :=
    contMDiffAt_extChartAt (n := ∞) (I := modelWithCornersSelf ℝ E) (x := x₀)
  have hd : ContDiffAt ℝ ∞
      (fun w => ContinuousAlternatingMap.wedge B (localRep α x₀ w) (localRep β x₀ w))
      (chartAt E x₀ x₀) :=
    (contDiffAt_localRep α hα x₀ (mem_chart_target E x₀)).wedge B
      (contDiffAt_localRep β hβ x₀ (mem_chart_target E x₀))
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ (E [⋀^ιa ⊕ ιb]→L[ℝ] H)) ∞
      (fun y => ContinuousAlternatingMap.wedge B (localRep α x₀ (chartAt E x₀ y))
        (localRep β x₀ (chartAt E x₀ y))) x₀ :=
    hd.contMDiffAt.comp x₀ hc
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_wedgeFamily_snd B α β x₀ y hy

/-- ★★ **The wedge of two differential forms.** -/
def wedge (B : F →L[ℝ] G →L[ℝ] H) (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ιa F)
    (β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ιb G) :
    DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (ιa ⊕ ιb) H :=
  ⟨wedgeFamily B (fun x => α x) (fun x => β x),
    contMDiff_wedgeFamily B α.contMDiff_toFun β.contMDiff_toFun⟩

@[simp] theorem wedge_apply (B : F →L[ℝ] G →L[ℝ] H)
    (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ιa F)
    (β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ιb G) (x : M) :
    wedge B α β x = wedgeFamily B (fun x => α x) (fun x => β x) x := rfl

/-! ### Reindexing a family -/

/-- Reindexing a family of alternating maps along an equivalence of index types, fibrewise. -/
def domDomCongrFamily (σ : ι ≃ ι')
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x)
    (x : M) : TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι']→L[ℝ] Bundle.Trivial M F x :=
  (ContinuousAlternatingMap.domDomCongr σ (toFlat (α x)) : E [⋀^ι']→L[ℝ] F)

omit [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] in
theorem toFlat_domDomCongrFamily (σ : ι ≃ ι')
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x)
    (x : M) :
    toFlat (domDomCongrFamily σ α x) = ContinuousAlternatingMap.domDomCongr σ (toFlat (α x)) := rfl

omit [DecidableEq ι] [DecidableEq ι'] in
theorem trivializationAt_domDomCongrFamily_snd (σ : ι ≃ ι')
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x)
    (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ι']→L[ℝ] F)
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι']→L[ℝ] Bundle.Trivial M F x)
      x₀ ⟨y, domDomCongrFamily σ α y⟩).2
      = ContinuousAlternatingMap.domDomCongr σ (localRep α x₀ (chartAt E x₀ y)) := by
  have hyy := (chartAt E x₀).left_inv hy
  simp only [localRep]
  rw [hyy, trivializationAt_snd _ x₀ y hy, trivializationAt_snd α x₀ y hy,
    toFlat_domDomCongrFamily, ContinuousAlternatingMap.domDomCongr_compContinuousLinearMap]

omit [DecidableEq ι] [DecidableEq ι'] in
theorem localRep_domDomCongrFamily (σ : ι ≃ ι')
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x)
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    localRep (domDomCongrFamily σ α) x₀ w
      = ContinuousAlternatingMap.domDomCongr σ (localRep α x₀ w) := by
  have h := trivializationAt_domDomCongrFamily_snd σ α x₀ _ ((chartAt E x₀).map_target hw)
  rw [(chartAt E x₀).right_inv hw] at h
  exact h

omit [DecidableEq ι'] in
theorem contMDiff_domDomCongrFamily (σ : ι ≃ ι')
    {α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x}
    (hα : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] F))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] F) x (α x))) :
    ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι']→L[ℝ] F))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι']→L[ℝ] F) x (domDomCongrFamily σ α x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have hc : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ (chartAt E x₀) x₀ :=
    contMDiffAt_extChartAt (n := ∞) (I := modelWithCornersSelf ℝ E) (x := x₀)
  have hd : ContDiffAt ℝ ∞
      (fun w => ContinuousAlternatingMap.domDomCongr σ (localRep α x₀ w)) (chartAt E x₀ x₀) :=
    (contDiffAt_localRep α hα x₀ (mem_chart_target E x₀)).domDomCongr σ
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ (E [⋀^ι']→L[ℝ] F)) ∞
      (fun y => ContinuousAlternatingMap.domDomCongr σ (localRep α x₀ (chartAt E x₀ y))) x₀ :=
    hd.contMDiffAt.comp x₀ hc
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_domDomCongrFamily_snd σ α x₀ y hy

/-- ★ **Reindexing a differential form** along an equivalence of index types. -/
def domDomCongr (σ : ι ≃ ι') (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ι F) :
    DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ι' F :=
  ⟨domDomCongrFamily σ (fun x => α x), contMDiff_domDomCongrFamily σ α.contMDiff_toFun⟩

omit [DecidableEq ι'] in
@[simp] theorem domDomCongr_apply (σ : ι ≃ ι')
    (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ι F) (x : M) :
    domDomCongr σ α x = domDomCongrFamily σ (fun x => α x) x := rfl

/-! ### The constant `0`-form -/

/-- The constant `0`-form with value `c`, as a family. -/
def constZeroFamily [IsEmpty ι] (c : F) (x : M) :
    TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x :=
  (ContinuousAlternatingMap.constOfIsEmpty ℝ E ι c : E [⋀^ι]→L[ℝ] F)

omit [DecidableEq ι] in
theorem trivializationAt_constZeroFamily_snd [IsEmpty ι] (c : F) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ι]→L[ℝ] F)
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M F x)
      x₀ ⟨y, constZeroFamily c y⟩).2
      = ContinuousAlternatingMap.constOfIsEmpty ℝ E ι c := by
  rw [trivializationAt_snd _ x₀ y hy]
  ext v
  simp [constZeroFamily]

omit [DecidableEq ι] in
theorem contMDiff_constZeroFamily [IsEmpty ι] (c : F) :
    ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] F))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] F) x (constZeroFamily (E := E) (ι := ι) c x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] F)) ∞
      (fun _ : M => ContinuousAlternatingMap.constOfIsEmpty ℝ E ι c) x₀ := contMDiffAt_const
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_constZeroFamily_snd c x₀ y hy

/-- The constant `0`-form with value `c`. -/
def constZero [IsEmpty ι] (c : F) : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ ι F :=
  ⟨constZeroFamily (E := E) (ι := ι) c, contMDiff_constZeroFamily c⟩

/-! ### The iterated power of a real 2-form -/

/-- The equivalence `Fin (2k) ⊕ Fin 2 ≃ Fin (2(k+1))` the iterated power re-indexes along. -/
def powEquiv (k : ℕ) : Fin (2 * k) ⊕ Fin 2 ≃ Fin (2 * (k + 1)) :=
  finSumFinEquiv.trans (finCongr (by ring))

/-- ★★ **The `k`-th exterior power of a real 2-form**, as a `2k`-form. -/
def wedgePow (α₂ : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) :
    (k : ℕ) → DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin (2 * k)) ℝ
  | 0 => domDomCongr (finCongr (by simp) : Fin 0 ≃ Fin (2 * 0)) (constZero (ι := Fin 0) (1 : ℝ))
  | k + 1 => domDomCongr (powEquiv k) (wedge (ContinuousLinearMap.mul ℝ ℝ) (wedgePow α₂ k) α₂)

@[simp] theorem wedgePow_succ (α₂ : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ)
    (k : ℕ) :
    wedgePow α₂ (k + 1) = domDomCongr (powEquiv k) (wedge (ContinuousLinearMap.mul ℝ ℝ) (wedgePow α₂ k) α₂) :=
  rfl

end DifferentialForm

/-! ### The flat iterated power, and the local representative of a power -/

namespace ContinuousAlternatingMap

/-- The `k`-th exterior power of a flat real 2-form, as a `2k`-form (same recursion as
`DifferentialForm.wedgePow`). -/
def wedgePow (α : E [⋀^Fin 2]→L[ℝ] ℝ) : (k : ℕ) → E [⋀^Fin (2 * k)]→L[ℝ] ℝ
  | 0 => domDomCongr (finCongr (by simp) : Fin 0 ≃ Fin (2 * 0)) (constOfIsEmpty ℝ E (Fin 0) 1)
  | k + 1 => domDomCongr (DifferentialForm.powEquiv k)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) (wedgePow α k) α)

/-- Pullback commutes with the iterated power. -/
theorem wedgePow_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) (L : E' →L[ℝ] E) :
    ∀ k, (wedgePow α k).compContinuousLinearMap L = wedgePow (α.compContinuousLinearMap L) k
  | 0 => by
    simp only [wedgePow]
    rw [domDomCongr_compContinuousLinearMap]
    congr 1
  | k + 1 => by
    simp only [wedgePow]
    rw [domDomCongr_compContinuousLinearMap, wedge_compContinuousLinearMap,
      wedgePow_compContinuousLinearMap α L k]

/-- The iterated power is homogeneous of degree `k`: `(c • α)^{∧k} = c^k • α^{∧k}`. -/
theorem wedgePow_smul (c : ℝ) (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    ∀ k, wedgePow (c • α) k = c ^ k • wedgePow α k
  | 0 => by simp [wedgePow]
  | k + 1 => by
    simp only [wedgePow]
    rw [wedgePow_smul c α k, wedge_smul_left, wedge_smul_right]
    ext v
    simp [domDomCongr_apply, smul_smul, pow_succ, mul_comm]

end ContinuousAlternatingMap

namespace DifferentialForm

omit [DecidableEq ι] in
theorem localRep_constZeroFamily [IsEmpty ι] (c : F) (x₀ : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) :
    localRep (constZeroFamily (E := E) (M := M) (ι := ι) c) x₀ w
      = ContinuousAlternatingMap.constOfIsEmpty ℝ E ι c :=
  trivializationAt_constZeroFamily_snd c x₀ _ ((chartAt E x₀).map_target hw)

/-- ★ The local representative of the `k`-th power is the `k`-th power of the local
representative. -/
theorem localRep_wedgePow (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ)
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    ∀ k, localRep (fun x => wedgePow α k x) x₀ w
      = ContinuousAlternatingMap.wedgePow (localRep (fun x => α x) x₀ w) k
  | 0 => by
    show localRep (domDomCongrFamily (finCongr (by simp) : Fin 0 ≃ Fin (2 * 0))
      (constZeroFamily (E := E) (M := M) (ι := Fin 0) (1 : ℝ))) x₀ w = _
    rw [localRep_domDomCongrFamily _ _ x₀ hw, localRep_constZeroFamily _ x₀ hw]
    rfl
  | k + 1 => by
    show localRep (domDomCongrFamily (powEquiv k)
      (wedgeFamily (ContinuousLinearMap.mul ℝ ℝ) (fun x => wedgePow α k x) (fun x => α x))) x₀ w = _
    rw [localRep_domDomCongrFamily _ _ x₀ hw, localRep_wedgeFamily _ _ _ x₀ hw,
      localRep_wedgePow α x₀ hw k]
    rfl

end DifferentialForm

end WedgeForm
