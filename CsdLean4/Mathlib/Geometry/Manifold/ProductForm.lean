/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ProductSelfModel
public import CsdLean4.Mathlib.Geometry.Manifold.SymplecticForm
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerClosed
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The sum of two forms on a product of manifolds: `π₁^* α + π₂^* β`

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

Given a form `α` on `M` and a form `β` on `N` of the same degree, the product `M × N` carries
`π₁^* α + π₂^* β`. This module builds it on the product charted over `E × F`
(`ProductSelfModel.lean`) and proves the three facts the symplectic predicate needs:

* `ContinuousAlternatingMap.prodSum α β` — the flat version on `E × F`, `α ∘ fst + β ∘ snd`, with
  `prodSum_compContinuousLinearMap_prodMap` (**it pulls back along a block map factorwise**);
* `DifferentialForm.prodFamily α β` — the family `(x, y) ↦ prodSum (α x) (β y)`, with
  ★ `localRep_prodFamily` (**its local representative in a product chart is the `prodSum` of the
  factors' local representatives**, by `fderiv_chart_transition_prod`), and
  `contMDiff_prodFamily` (smooth when the factors are);
* ★ `DifferentialForm.prodForm α β` — the bundled `C^∞` form on `M × N`;
* ★★ `mextDeriv_prodFamily` — **`d (π₁^* α + π₂^* β) = π₁^* dα + π₂^* dβ`**, from the flat
  naturality `extDeriv_pullback` along the two projections;
* ★★ `IsSymplectic.prodForm` — **the product of two symplectic manifolds is symplectic**;
* `contMDiff_zeroFamily`, `mextDeriv_zeroFamily` — the zero family on any manifold over a self
  model is a smooth section with zero exterior derivative (used with the product to read constant
  interior products on a product).

## Honest scope

⚠️ **Same degree on both factors, valued in the same `G`.** That is what the sum needs. Wedge
products of forms of different degrees across the factors are not built (the corpus's
`WedgeForm.lean` wedges forms on one manifold).

⚠️ **Nothing about the top power or volumes.** That `(π₁^* α + π₂^* β)^{m+n}` is a multiple of
`π₁^* α^m ∧ π₂^* β^n` (the binomial identity for commuting even forms) is not stated; the
Liouville theorem of `HamiltonianFlowVolume.lean` applies to the product form's own top-power
measure, which is not here identified with a product measure.

References: `Geometry/Manifold/ProductSelfModel.lean` (the product charts and their transition
derivatives); `Geometry/Manifold/ExteriorDerivative.lean` (`localRep`, `trivializationAt_snd`,
`contDiffAt_localRep`); `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
(`extDeriv_pullback`, `extDeriv_add`); `Geometry/Manifold/TranslationAtlasForm.lean` (the torus
factor); `specs/BACKLOG.md` (`R-016′`).
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology
open scoped Manifold Bundle Topology ContDiff

/-! ### The flat sum -/

namespace ContinuousAlternatingMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*}

/-- **`π₁^* α + π₂^* β`** on `E × F`: the alternating map `v ↦ α (v.1) + β (v.2)`. -/
def prodSum (α : E [⋀^ι]→L[ℝ] G) (β : F [⋀^ι]→L[ℝ] G) : (E × F) [⋀^ι]→L[ℝ] G :=
  α.compContinuousLinearMap (ContinuousLinearMap.fst ℝ E F)
    + β.compContinuousLinearMap (ContinuousLinearMap.snd ℝ E F)

theorem prodSum_apply (α : E [⋀^ι]→L[ℝ] G) (β : F [⋀^ι]→L[ℝ] G) (v : ι → E × F) :
    prodSum α β v = α (fun i => (v i).1) + β (fun i => (v i).2) := rfl

@[simp] theorem prodSum_zero_zero : prodSum (0 : E [⋀^ι]→L[ℝ] G) (0 : F [⋀^ι]→L[ℝ] G) = 0 := by
  ext v
  simp [prodSum_apply]

/-- The `prodSum` of two 2-forms evaluated on a pair of pairs. -/
theorem prodSum_pair (a : E [⋀^Fin 2]→L[ℝ] G) (b : F [⋀^Fin 2]→L[ℝ] G) (v w : E × F) :
    prodSum a b ![v, w] = a ![v.1, w.1] + b ![v.2, w.2] := by
  rw [prodSum_apply]
  congr 1
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1; funext i; fin_cases i <;> rfl

/-- ★ **The sum pulls back factorwise along a block map.** -/
theorem prodSum_compContinuousLinearMap_prodMap {E' F' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (α : E [⋀^ι]→L[ℝ] G) (β : F [⋀^ι]→L[ℝ] G) (L : E' →L[ℝ] E) (K : F' →L[ℝ] F) :
    (prodSum α β).compContinuousLinearMap (L.prodMap K)
      = prodSum (α.compContinuousLinearMap L) (β.compContinuousLinearMap K) := by
  ext v
  rfl

end ContinuousAlternatingMap

/-! ### The family on a product of manifolds -/

namespace DifferentialForm

open ContinuousAlternatingMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]

/-- The family `(x, y) ↦ π₁^* (α x) + π₂^* (β y)` on the tangent spaces of `M × N`. -/
def prodFamily
    (α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y) (p : M × N) :
    TangentSpace 𝓘(ℝ, E × F) p [⋀^ι]→L[ℝ] Bundle.Trivial (M × N) G p :=
  prodSum (toFlat (α p.1)) (toFlat (β p.2))

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] [Fintype ι] in
theorem prodFamily_apply
    (α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y) (p : M × N) :
    prodFamily α β p = prodSum (toFlat (α p.1)) (toFlat (β p.2)) := rfl

/-- ★ Through the tangent trivialisation at `(x₀, y₀)`, the family reads as the `prodSum` of
the factors' trivialised values: the coordinate change of a product chart is the block map of
the factors' coordinate changes. -/
theorem trivializationAt_prodFamily_snd
    (α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y)
    (x₀ : M) (y₀ : N) {p : M × N} (hp : p ∈ (chartAt (E × F) (x₀, y₀)).source) :
    (trivializationAt ((E × F) [⋀^ι]→L[ℝ] G)
      (fun q : M × N => TangentSpace 𝓘(ℝ, E × F) q [⋀^ι]→L[ℝ] Bundle.Trivial (M × N) G q)
      (x₀, y₀) ⟨p, prodFamily α β p⟩).2
      = prodSum
          ((trivializationAt (E [⋀^ι]→L[ℝ] G)
            (fun x : M => TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
            ⟨p.1, α p.1⟩).2)
          ((trivializationAt (F [⋀^ι]→L[ℝ] G)
            (fun y : N => TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y) y₀
            ⟨p.2, β p.2⟩).2) := by
  obtain ⟨x, y⟩ := p
  rw [Prod.chartAt_prod_source] at hp
  obtain ⟨hx, hy⟩ := Set.mem_prod.1 hp
  rw [trivializationAt_snd (prodFamily α β) (x₀, y₀) (x, y)
    (by rw [Prod.chartAt_prod_source]; exact Set.mem_prod.2 ⟨hx, hy⟩),
    trivializationAt_snd α x₀ x hx, trivializationAt_snd β y₀ y hy, Prod.chartAt_prod_apply]
  rw [Prod.fderiv_chart_transition_prod x₀ x y₀ y (w := (chartAt E x₀ x, chartAt F y₀ y))
    ((chartAt E x₀).map_source hx)
    (by rw [(chartAt E x₀).left_inv hx]; exact mem_chart_source E x)
    ((chartAt F y₀).map_source hy)
    (by rw [(chartAt F y₀).left_inv hy]; exact mem_chart_source F y)]
  exact prodSum_compContinuousLinearMap_prodMap _ _ _ _

/-- ★ **The local representative of the sum in a product chart is the `prodSum` of the factors'
local representatives.** -/
theorem localRep_prodFamily
    (α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y)
    (x₀ : M) (y₀ : N) {w : E × F} (hw : w ∈ (chartAt (E × F) (x₀, y₀)).target) :
    localRep (prodFamily α β) (x₀, y₀) w
      = prodSum (localRep α x₀ w.1) (localRep β y₀ w.2) := by
  simp only [localRep]
  exact trivializationAt_prodFamily_snd α β x₀ y₀ ((chartAt (E × F) (x₀, y₀)).map_target hw)

/-- The sum of two `C^∞` families is a `C^∞` section on the product. -/
theorem contMDiff_prodFamily
    {α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x}
    {β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y}
    (hα : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^ι]→L[ℝ] G)) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) x (α x)))
    (hβ : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F [⋀^ι]→L[ℝ] G)) ∞
      (fun y : N => TotalSpace.mk' (F [⋀^ι]→L[ℝ] G) y (β y))) :
    ContMDiff 𝓘(ℝ, E × F) (𝓘(ℝ, E × F).prod 𝓘(ℝ, (E × F) [⋀^ι]→L[ℝ] G)) ∞
      (fun p : M × N => TotalSpace.mk' ((E × F) [⋀^ι]→L[ℝ] G) p (prodFamily α β p)) := by
  rintro ⟨x₀, y₀⟩
  rw [contMDiffAt_section]
  -- the two factor sections, trivialised at `x₀` and at `y₀`
  have hA : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E [⋀^ι]→L[ℝ] G) ∞
      (fun x : M => (trivializationAt (E [⋀^ι]→L[ℝ] G)
        (fun x : M => TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀ ⟨x, α x⟩).2)
      x₀ := (contMDiffAt_section x₀).1 (hα x₀)
  have hB : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F [⋀^ι]→L[ℝ] G) ∞
      (fun y : N => (trivializationAt (F [⋀^ι]→L[ℝ] G)
        (fun y : N => TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y) y₀ ⟨y, β y⟩).2)
      y₀ := (contMDiffAt_section y₀).1 (hβ y₀)
  -- composed with the projections and pulled back along `fst`, `snd`, then summed
  have hA' : ContMDiffAt 𝓘(ℝ, E × F) 𝓘(ℝ, (E × F) [⋀^ι]→L[ℝ] G) ∞
      (fun p : M × N => ((trivializationAt (E [⋀^ι]→L[ℝ] G)
        (fun x : M => TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
        ⟨p.1, α p.1⟩).2).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E F)) (x₀, y₀) := by
    have hf : ContMDiffAt 𝓘(ℝ, E × F) 𝓘(ℝ, E) ∞ (Prod.fst : M × N → M) (x₀, y₀) :=
      Prod.contMDiff_fst_self (x₀, y₀)
    have h1 := hA.comp (x₀, y₀) hf
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.fst ℝ E F)).contMDiff.contMDiffAt.comp (x₀, y₀) h1
  have hB' : ContMDiffAt 𝓘(ℝ, E × F) 𝓘(ℝ, (E × F) [⋀^ι]→L[ℝ] G) ∞
      (fun p : M × N => ((trivializationAt (F [⋀^ι]→L[ℝ] G)
        (fun y : N => TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y) y₀
        ⟨p.2, β p.2⟩).2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ E F)) (x₀, y₀) := by
    have hg : ContMDiffAt 𝓘(ℝ, E × F) 𝓘(ℝ, F) ∞ (Prod.snd : M × N → N) (x₀, y₀) :=
      Prod.contMDiff_snd_self (x₀, y₀)
    have h1 := hB.comp (x₀, y₀) hg
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.snd ℝ E F)).contMDiff.contMDiffAt.comp (x₀, y₀) h1
  refine (hA'.add hB').congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (E × F) (x₀, y₀)).open_source.mem_nhds (mem_chart_source _ (x₀, y₀))]
    with p hp
  rw [trivializationAt_prodFamily_snd α β x₀ y₀ hp]
  rfl

/-- ★ **`π₁^* α + π₂^* β` as a `C^∞` form on the product.** -/
def prodForm (α : DifferentialForm 𝓘(ℝ, E) M ∞ ι G) (β : DifferentialForm 𝓘(ℝ, F) N ∞ ι G) :
    DifferentialForm 𝓘(ℝ, E × F) (M × N) ∞ ι G :=
  ⟨prodFamily (fun x => α x) (fun y => β y),
    contMDiff_prodFamily α.contMDiff_toFun β.contMDiff_toFun⟩

@[simp] theorem prodForm_apply (α : DifferentialForm 𝓘(ℝ, E) M ∞ ι G)
    (β : DifferentialForm 𝓘(ℝ, F) N ∞ ι G) (p : M × N) :
    prodForm α β p = prodSum (toFlat (α p.1)) (toFlat (β p.2)) := rfl

/-! ### The exterior derivative of the sum -/

section ExtDeriv

variable {k : ℕ}

/-- The flat sum of two form-valued functions on the factors, pulled back to `E × F`. -/
theorem extDeriv_prodSum_comp {a : E → E [⋀^Fin k]→L[ℝ] G} {b : F → F [⋀^Fin k]→L[ℝ] G}
    {w : E × F} (ha : DifferentiableAt ℝ a w.1) (hb : DifferentiableAt ℝ b w.2) :
    extDeriv (fun u : E × F => prodSum (a u.1) (b u.2)) w
      = prodSum (extDeriv a w.1) (extDeriv b w.2) := by
  have hfst : ∀ u : E × F, (a u.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E F)
      = (a (Prod.fst u)).compContinuousLinearMap (fderiv ℝ Prod.fst u) := fun u => by
    rw [fderiv_fst]
  have hsnd : ∀ u : E × F, (b u.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ E F)
      = (b (Prod.snd u)).compContinuousLinearMap (fderiv ℝ Prod.snd u) := fun u => by
    rw [fderiv_snd]
  have hda : DifferentiableAt ℝ (fun u : E × F =>
      (a (Prod.fst u)).compContinuousLinearMap (fderiv ℝ Prod.fst u)) w := by
    simp_rw [fderiv_fst]
    exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.fst ℝ E F)).differentiableAt).comp w (ha.comp w differentiableAt_fst)
  have hdb : DifferentiableAt ℝ (fun u : E × F =>
      (b (Prod.snd u)).compContinuousLinearMap (fderiv ℝ Prod.snd u)) w := by
    simp_rw [fderiv_snd]
    exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.snd ℝ E F)).differentiableAt).comp w (hb.comp w differentiableAt_snd)
  have hr : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) := by simp [minSmoothness_of_isRCLikeNormedField]
  calc extDeriv (fun u : E × F => prodSum (a u.1) (b u.2)) w
      = extDeriv (fun u : E × F =>
          (a (Prod.fst u)).compContinuousLinearMap (fderiv ℝ Prod.fst u)
          + (b (Prod.snd u)).compContinuousLinearMap (fderiv ℝ Prod.snd u)) w := by
        congr 1
        funext u
        rw [prodSum, hfst u, hsnd u]
    _ = extDeriv (fun u : E × F =>
          (a (Prod.fst u)).compContinuousLinearMap (fderiv ℝ Prod.fst u)) w
        + extDeriv (fun u : E × F =>
          (b (Prod.snd u)).compContinuousLinearMap (fderiv ℝ Prod.snd u)) w :=
        extDeriv_fun_add hda hdb
    _ = (extDeriv a w.1).compContinuousLinearMap (fderiv ℝ Prod.fst w)
        + (extDeriv b w.2).compContinuousLinearMap (fderiv ℝ Prod.snd w) := by
        rw [extDeriv_pullback ha (contDiff_fst.contDiffAt (n := 2)) hr,
          extDeriv_pullback hb (contDiff_snd.contDiffAt (n := 2)) hr]
    _ = prodSum (extDeriv a w.1) (extDeriv b w.2) := by
        rw [prodSum, fderiv_fst, fderiv_snd]

/-- ★★ **`d (π₁^* α + π₂^* β) = π₁^* dα + π₂^* dβ`**, pointwise, for `C^∞` factors. -/
theorem mextDeriv_prodFamily
    {α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^Fin k]→L[ℝ] Bundle.Trivial M G x}
    {β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^Fin k]→L[ℝ] Bundle.Trivial N G y}
    (hα : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) x (α x)))
    (hβ : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] G)) ∞
      (fun y : N => TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] G) y (β y)))
    (p : M × N) :
    _root_.mextDeriv (prodFamily α β) p
      = prodSum (toFlat (_root_.mextDeriv α p.1)) (toFlat (_root_.mextDeriv β p.2)) := by
  obtain ⟨x, y⟩ := p
  show extDeriv (localRep (prodFamily α β) (x, y)) (chartAt (E × F) (x, y) (x, y)) = _
  have hev : localRep (prodFamily α β) (x, y) =ᶠ[𝓝 (chartAt (E × F) (x, y) (x, y))]
      fun w => prodSum (localRep α x w.1) (localRep β y w.2) := by
    filter_upwards [(chartAt (E × F) (x, y)).open_target.mem_nhds (mem_chart_target _ (x, y))]
      with w hw
    exact localRep_prodFamily α β x y hw
  rw [hev.extDeriv_eq]
  have hx : (chartAt (E × F) (x, y) (x, y)).1 ∈ (chartAt E x).target :=
    mem_chart_target E x
  have hy : (chartAt (E × F) (x, y) (x, y)).2 ∈ (chartAt F y).target :=
    mem_chart_target F y
  rw [extDeriv_prodSum_comp ((contDiffAt_localRep α hα x hx).differentiableAt (by simp))
    ((contDiffAt_localRep β hβ y hy).differentiableAt (by simp))]
  rfl

/-- ★★ **`d (prodForm α β) = prodForm (dα) (dβ)`.** -/
theorem prodForm_mextDeriv (α : DifferentialForm 𝓘(ℝ, E) M ∞ (Fin k) G)
    (β : DifferentialForm 𝓘(ℝ, F) N ∞ (Fin k) G) :
    (prodForm α β).mextDeriv = prodForm α.mextDeriv β.mextDeriv := by
  apply ContMDiffSection.ext
  intro p
  exact mextDeriv_prodFamily α.contMDiff_toFun β.contMDiff_toFun p

end ExtDeriv

/-! ### The zero family -/

section ZeroFamily

/-- The zero family reads as zero through every tangent trivialisation. -/
theorem trivializationAt_zero_snd (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
      ⟨y, (0 : TangentSpace 𝓘(ℝ, E) y [⋀^ι]→L[ℝ] Bundle.Trivial M G y)⟩).2 = 0 := by
  rw [trivializationAt_snd (fun x : M => (0 : TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ]
    Bundle.Trivial M G x)) x₀ y hy]
  exact ContinuousAlternatingMap.ext fun _ => rfl

theorem localRep_zeroFamily (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    localRep (fun x : M => (0 : TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)) x₀ w
      = 0 :=
  trivializationAt_zero_snd x₀ _ ((chartAt E x₀).map_target hw)

/-- The zero family is a `C^∞` section. -/
theorem contMDiff_zeroFamily :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^ι]→L[ℝ] G)) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) x
        (0 : TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)) := by
  intro x₀
  rw [contMDiffAt_section]
  refine (contMDiffAt_const (c := (0 : E [⋀^ι]→L[ℝ] G))).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_zero_snd x₀ y hy

/-- The exterior derivative of the zero family is zero. -/
theorem mextDeriv_zeroFamily {k : ℕ} (x : M) :
    _root_.mextDeriv (fun x : M => (0 : TangentSpace 𝓘(ℝ, E) x [⋀^Fin k]→L[ℝ]
      Bundle.Trivial M G x)) x = 0 := by
  show extDeriv (localRep _ x) (chartAt E x x) = 0
  have hev : localRep (fun x : M => (0 : TangentSpace 𝓘(ℝ, E) x [⋀^Fin k]→L[ℝ]
      Bundle.Trivial M G x)) x =ᶠ[𝓝 (chartAt E x x)] fun _ => (0 : E [⋀^Fin k]→L[ℝ] G) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with w hw
    exact localRep_zeroFamily x hw
  rw [hev.extDeriv_eq]
  exact extDeriv_const_apply 0 _

end ZeroFamily

/-! ### Symplectic products -/

/-- ★★ **The product of two symplectic manifolds is symplectic**, with the form
`π₁^* α + π₂^* β`. -/
theorem IsSymplectic.prodForm {α : DifferentialForm 𝓘(ℝ, E) M ∞ (Fin 2) ℝ}
    {β : DifferentialForm 𝓘(ℝ, F) N ∞ (Fin 2) ℝ} (hα : α.IsSymplectic) (hβ : β.IsSymplectic) :
    (DifferentialForm.prodForm α β).IsSymplectic := by
  refine ⟨?_, ?_⟩
  · rw [prodForm_mextDeriv, hα.closed, hβ.closed]
    apply ContMDiffSection.ext
    intro p
    exact prodSum_zero_zero
  · rintro ⟨x, y⟩ v hv
    have key : ∀ w : E × F, DifferentialForm.prodForm α β (x, y) ![v, w]
        = toFlat (α x) ![(v : E × F).1, w.1] + toFlat (β y) ![(v : E × F).2, w.2] :=
      fun w => prodSum_pair (toFlat (α x)) (toFlat (β y)) (v : E × F) w
    by_cases h1 : (v : E × F).1 = 0
    · have h2 : (v : E × F).2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
      obtain ⟨w₂, hw₂⟩ := hβ.nondegenerate y (v : E × F).2 h2
      refine ⟨((0 : E), w₂), ?_⟩
      rw [key]
      have hz : toFlat (α x) ![(v : E × F).1, (0 : E)] = 0 :=
        ContinuousMultilinearMap.map_coord_zero _ 1 rfl
      rw [hz, zero_add]
      exact hw₂
    · obtain ⟨w₁, hw₁⟩ := hα.nondegenerate x (v : E × F).1 h1
      refine ⟨(w₁, (0 : F)), ?_⟩
      rw [key]
      have hz : toFlat (β y) ![(v : E × F).2, (0 : F)] = 0 :=
        ContinuousMultilinearMap.map_coord_zero _ 1 rfl
      rw [hz, add_zero]
      exact hw₁

end DifferentialForm

end
