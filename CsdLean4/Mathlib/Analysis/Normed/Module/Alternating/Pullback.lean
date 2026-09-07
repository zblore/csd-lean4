/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The pullback of a continuous alternating map is jointly analytic

**Category:** 1-Mathlib-staging (CSD-free; upstream targets
`Mathlib.Topology.Algebra.Module.Alternating` for the alternatization and
`Mathlib.Analysis.Analytic.CPolynomial` for the pullback, beside its multilinear twin).

The lemma that step (2a) of the manifold exterior-calculus plan ran aground on
(`MATHLIB-GAPS.md`, `specs/BACKLOG.md` XL). Making differential forms on a **manifold** into
smooth sections needs a `ContMDiffVectorBundle` instance for the alternating-map bundle,
whose crux is smoothness of the coordinate change — and that reduces to smoothness of the
**pullback** `(g, ω) ↦ ω ∘ g` in *both* arguments jointly.

⚠️ At the pin upstream has that for the **multilinear** pullback
(`ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap`,
`Analysis/Analytic/CPolynomial.lean`) and, for the **alternating** one, only
*continuity* and the *first* derivative
(`Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`). The obvious reduction fails:
the alternating pullback is the DIAGONAL restriction of the multilinear one — degree `card ι`
in `g`, not linear — so it is not itself a continuous multilinear map, and the existing
continuity proof reflects along an inducing embedding, an argument that does not carry to
`ContDiff`. MATHLIB-ABSENT(ContinuousAlternatingMap.analyticAt_uncurry_compContinuousLinearMap)

**What unlocks it is a left inverse.** Alternatization sends a continuous multilinear map to
a continuous alternating one, and on an already-alternating map it multiplies by
`(card ι)!` — so in characteristic zero it is a continuous linear **retraction** of the
inclusion. Analyticity then reflects for free: the alternating pullback is that retraction
applied to the multilinear pullback of the inclusion, along the diagonal.

## Contents

* `ContinuousMultilinearMap.continuous_alternatization` and
  ★ `ContinuousMultilinearMap.alternatizationCLM` — alternatization as a **continuous linear
  map**. Upstream has it only as an `AddMonoidHom` (`ContinuousMultilinearMap.alternatization`),
  which is the reason the retraction argument was not available;
  MATHLIB-ABSENT(ContinuousMultilinearMap.alternatizationCLM)
* `alternatizationCLM_of_alternating` — on an alternating map it is `(card ι)!`;
* `compContinuousLinearMap_eq_smul_alternatization` — the pullback written through the
  retraction, which is the whole idea in one equation;
* ★★ `ContinuousAlternatingMap.analyticAt_uncurry_compContinuousLinearMap` — the pullback is
  jointly analytic, and
* ★ `contDiffAt_uncurry_compContinuousLinearMap` / `contDiff_uncurry_compContinuousLinearMap`
  — the `ContDiff` corollaries, which is the form the bundle instance consumes.

## Honest scope

⚠️ **This unblocks step (2a); it does not perform it.** What still has to be built on top:
the `ContMDiffOn` lemma for the alternating bundle's coordinate change, the
`ContMDiffVectorBundle` instance (the analogue of `Geometry/Manifold/VectorBundle/Hom.lean`),
and only then differential forms on a manifold as smooth sections. **Three layers remain.**

⚠️ **Characteristic zero is essential, not incidental.** The retraction divides by
`(card ι)!`; over a field of positive characteristic the argument fails at exactly that step,
and nothing here says whether the conclusion survives.

⚠️ `contDiffAt_…` needs `[CompleteSpace G]`, inherited from `AnalyticAt.contDiffAt`. The
analyticity statement itself does not.

References: `MATHLIB-GAPS.md` (Kahler / symplectic manifold API, step (2a));
`specs/BACKLOG.md` (XL, "Manifold exterior calculus");
`Mathlib/Analysis/Analytic/CPolynomial.lean` (the multilinear twin this reflects from);
`Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
(`alternatization`, the `AddMonoidHom` this upgrades).
-/

@[expose] public section

open ContinuousAlternatingMap

namespace ContinuousMultilinearMap

variable {𝕜 ι M N : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]

/-- Alternatization is continuous: it is a finite signed sum of index permutations, and the
topology on the alternating maps is induced from the multilinear ones. -/
lemma continuous_alternatization :
    Continuous (alternatization :
      ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N → (M [⋀^ι]→L[𝕜] N)) := by
  refine isUniformEmbedding_toContinuousMultilinearMap.isInducing.continuous_iff.2 ?_
  simp only [Function.comp_def]
  have h : (fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N =>
        (alternatization f).toContinuousMultilinearMap)
      = fun f => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ := by
    funext f
    rw [alternatization_apply_toContinuousMultilinearMap]
    exact Finset.sum_congr rfl fun σ _ => by rw [Units.smul_def]
  rw [h]
  refine continuous_finsetSum _ fun σ _ => Continuous.const_smul ?_ _
  exact (domDomCongrₗᵢ 𝕜 M N σ).continuous

/-- ★ **Alternatization as a continuous linear map.** Upstream has this only as an
`AddMonoidHom`; the scalar action and the continuity are what make it usable as a
retraction. -/
noncomputable def alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N →L[𝕜] (M [⋀^ι]→L[𝕜] N) where
  toFun := alternatization
  map_add' f g := map_add alternatization f g
  map_smul' c f := by
    ext v
    have hl : alternatization (c • f) v
        = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • c • f (v ∘ (σ : Equiv.Perm ι)) := by
      simp [alternatization_apply_apply]
    have hr : (c • alternatization f) v
        = c • ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ (σ : Equiv.Perm ι)) := by
      simp [alternatization_apply_apply]
    rw [RingHom.id_apply, hl, hr, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _
  cont := continuous_alternatization

end ContinuousMultilinearMap

namespace ContinuousMultilinearMap
variable {𝕜 ι M N : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]

/-- Alternatizing something already alternating multiplies it by `(card ι)!` — so in
characteristic zero `alternatizationCLM` is a continuous linear **retraction** of the
inclusion of alternating maps into multilinear ones. -/
theorem alternatizationCLM_of_alternating (ω : M [⋀^ι]→L[𝕜] N) :
    alternatizationCLM (ω.toContinuousMultilinearMap) = (Fintype.card ι).factorial • ω := by
  ext v
  simp only [alternatizationCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, alternatization_apply_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap]
  have hperm : ∀ σ : Equiv.Perm ι, ω (v ∘ σ) = Equiv.Perm.sign σ • ω v := by
    intro σ
    simpa using ω.toAlternatingMap.map_perm v σ
  rw [Finset.sum_congr rfl (fun σ _ => by
    rw [hperm σ, smul_smul, Int.units_mul_self, one_smul])]
  simp [Finset.card_univ, Fintype.card_perm]

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap
open ContinuousMultilinearMap
variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CharZero 𝕜]

/-- **The idea, in one equation.** The pullback of an alternating map is the retraction
applied to the pullback of its inclusion — so anything true of the multilinear pullback and
stable under continuous linear maps transfers. -/
theorem compContinuousLinearMap_eq_smul_alternatization (g : E →L[𝕜] F) (ω : F [⋀^ι]→L[𝕜] G) :
    ω.compContinuousLinearMap g
      = ((Fintype.card ι).factorial : 𝕜)⁻¹ •
          alternatizationCLM
            (ω.toContinuousMultilinearMap.compContinuousLinearMap (fun _ => g)) := by
  have hfac : ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h : ω.toContinuousMultilinearMap.compContinuousLinearMap (fun _ => g)
      = (ω.compContinuousLinearMap g).toContinuousMultilinearMap := rfl
  rw [h, alternatizationCLM_of_alternating, ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ hfac]

/-- The bundled linear reindexing used in the analyticity proof. -/
noncomputable def pullbackPairCLM :
    ((E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G)) →L[𝕜]
      (((i : ι) → E →L[𝕜] F) × ContinuousMultilinearMap 𝕜 (fun _ : ι => F) G) :=
  (ContinuousLinearMap.pi fun _ : ι =>
      ContinuousLinearMap.fst 𝕜 (E →L[𝕜] F) (F [⋀^ι]→L[𝕜] G)).prod
    ((toContinuousMultilinearMapCLM 𝕜).comp
      (ContinuousLinearMap.snd 𝕜 (E →L[𝕜] F) (F [⋀^ι]→L[𝕜] G)))

/-- ★ **The missing lemma.** The pullback of a continuous alternating map along a continuous
linear map is **analytic in both arguments jointly**. -/
theorem analyticAt_uncurry_compContinuousLinearMap
    (q : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G)) :
    AnalyticAt 𝕜
      (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) => p.2.compContinuousLinearMap p.1) q := by
  have key : (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) => p.2.compContinuousLinearMap p.1)
      = fun p => (((Fintype.card ι).factorial : 𝕜)⁻¹ • alternatizationCLM)
            ((pullbackPairCLM p).2.compContinuousLinearMap (pullbackPairCLM p).1) := by
    funext p
    rw [compContinuousLinearMap_eq_smul_alternatization p.1 p.2]
    rfl
  rw [key]
  have hmul : AnalyticAt 𝕜
      (fun P : ((i : ι) → E →L[𝕜] F) × ContinuousMultilinearMap 𝕜 (fun _ : ι => F) G =>
        P.2.compContinuousLinearMap P.1) (pullbackPairCLM q) :=
    ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap
  exact (((((Fintype.card ι).factorial : 𝕜)⁻¹ • alternatizationCLM)).analyticAt _).comp
    (hmul.comp (pullbackPairCLM.analyticAt q))

end ContinuousAlternatingMap

namespace ContinuousAlternatingMap
variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CharZero 𝕜] [CompleteSpace G]

/-- ★ The `ContDiffAt` corollary — the form a smooth-bundle instance consumes. -/
theorem contDiffAt_uncurry_compContinuousLinearMap {n : WithTop ℕ∞}
    (q : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G)) :
    ContDiffAt 𝕜 n (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) =>
      p.2.compContinuousLinearMap p.1) q :=
  (analyticAt_uncurry_compContinuousLinearMap q).contDiffAt

/-- ★ The `ContDiff` corollary. -/
theorem contDiff_uncurry_compContinuousLinearMap {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun p : (E →L[𝕜] F) × (F [⋀^ι]→L[𝕜] G) =>
      p.2.compContinuousLinearMap p.1) :=
  contDiff_iff_contDiffAt.2 fun q => contDiffAt_uncurry_compContinuousLinearMap q

end ContinuousAlternatingMap
