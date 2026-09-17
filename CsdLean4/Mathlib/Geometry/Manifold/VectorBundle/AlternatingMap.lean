/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# The bundle of continuous alternating maps is a `C^n` vector bundle

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Geometry.Manifold.VectorBundle`, beside `Hom.lean`).

Mathlib has the bundle of continuous alternating
maps as a **topological** vector bundle (`Topology/VectorBundle/ContinuousAlternatingMap.lean`)
and it has `Hom.lean` doing the smooth case for the bundle of continuous *linear* maps. It has
nothing alternating anywhere under `Geometry/Manifold/`.
MATHLIB-ABSENT(ContMDiffVectorBundle.continuousAlternatingMap)

* ★ `contMDiffOn_continuousAlternatingMapCoordChange` — the coordinate change is `C^n`;
* ★★ `ContMDiffVectorBundle.continuousAlternatingMap` — **the instance**: the alternating-map
  bundle of two `C^n` vector bundles is a `C^n` vector bundle.

The proof mirrors `Hom.lean` exactly once the coordinate change is available, and the
coordinate change decomposes — **by `rfl`** — as postcomposition after pullback:

    compContinuousAlternatingMapCLM (e₂.coordChangeL b)
      ∘L compContinuousLinearMapCLM (e₁'.coordChangeL b)

with both factors smooth by
[`Analysis/Normed/Module/Alternating/Pullback.lean`](../../../Analysis/Normed/Module/Alternating/Pullback.lean).

## ⚠️ The elaboration trap, recorded because it cost a full attempt

The first attempt at the coordinate-change lemma failed and was recorded — wrongly — as an
"instance-path mismatch" needing plumbing. It is not that. The two topologies on a
continuous-linear-map space **are the same instance** (`inferInstance = ContinuousLinearMap.topologicalSpace`
by `rfl`, checked). What fails is **elaboration order**: writing

    have h : ContDiff 𝕜 n (fun L : F₂ →L[𝕜] F₂ => (compContinuousAlternatingMapCLM L : … →L[𝕜] …))

re-synthesises the instances from the *ascription* and lands on the normed path, while the
term carries the topological-module path; the application check then runs at reducible
transparency and does not unfold them. Stating the same fact **through the term** —
`ContDiff 𝕜 n ⇑(compContinuousAlternatingMapCLM …)` — typechecks immediately. That is the whole
fix, and it is why this module states its two `ContDiff` hypotheses in that shape.

## Honest scope

⚠️ **What remains of step (2a) is the last mile, and it is not this.** With this instance,
differential forms on a manifold as smooth sections
(`ContMDiffSection I _ n fun x ↦ TangentSpace I x [⋀^ι]→L[𝕜] Bundle.Trivial M G x`) are one
definition away — but that definition needs the total-space topology instance to synthesise
for the specific (tangent bundle, trivial bundle) pair, which it does not do out of the box.
**Not built here**, and the row stays open until it is.

⚠️ **Still no exterior derivative.** That is step (2b), upstream's own TODO, and nothing here
touches it. And as with steps (0) and (1): no physics waits on any of this.

**Provenance and references.** The Mathlib-gaps register; the backlog (XL, "Manifold exterior calculus");
`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` (the template);
`CsdLean4/Mathlib/Analysis/Normed/Module/Alternating/Pullback.lean` (both factors).
-/

@[expose] public section

open Bundle Set ContinuousLinearMap Pretrivialization
open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ ι : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [Fintype ι] [DecidableEq ι]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

theorem contMDiffOn_continuousAlternatingMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) n
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  have hpost : ContDiff 𝕜 n
      ⇑(ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι) :=
    ContinuousLinearMap.contDiff _
  have hpre : ContDiff 𝕜 n (fun g : F₁ →L[𝕜] F₁ =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM g :
        (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
  have key : ∀ b, continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b
      = (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι
            (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)).comp
          (ContinuousAlternatingMap.compContinuousLinearMapCLM
            (e₁'.coordChangeL 𝕜 e₁ b : F₁ →L[𝕜] F₁)) := fun b => rfl
  rw [funext key]
  exact ContMDiffOn.clm_comp
    (hpost.contMDiff.comp_contMDiffOn (h₂.mono (by mfld_set_tac)))
    (hpre.contMDiff.comp_contMDiffOn (h₁.mono (by mfld_set_tac)))

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.ContinuousAlternatingMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange,
      continuousAlternatingMapCoordChange_apply⟩

instance ContMDiffVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[𝕜] F₂) (fun (b : B) => E₁ b [⋀^ι]→L[𝕜] E₂ b) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end
