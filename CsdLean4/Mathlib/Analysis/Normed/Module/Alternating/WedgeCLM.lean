/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.Wedge
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The wedge as a bounded bilinear map; reindexing as a continuous linear map

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Analysis.Normed.Module.Alternating`).

Milestone **M2(a)–(b)** of the top-power plan, and the norm bound that
`Wedge.lean`'s honest scope listed as "true and a natural follow-up". `Wedge.lean` proved the
exterior product of two continuous alternating maps continuous *in the vector family*; this
module proves it bilinear and bounded *in the pair of forms*, which is what makes the wedge of
two smooth sections smooth:

* `liftTensor_summand_mk''` — one summand of the shuffle sum, on a representative permutation:
  `sign σ • B (a (v ∘ σ ∘ inl)) (b (v ∘ σ ∘ inr))`;
* ★ `wedge_compContinuousLinearMap` — **pullback commutes with the wedge**,
  `(a ∧ b) ∘ L = (a ∘ L) ∧ (b ∘ L)`;
* `wedge_add_left`, `wedge_smul_left`, `wedge_add_right`, `wedge_smul_right` — bilinearity;
* ★ `norm_wedge_le` — `‖a ∧ b‖ ≤ card (shuffle classes) · ‖B‖ · ‖a‖ · ‖b‖`;
* ★ `wedgeL` — the wedge as a continuous bilinear map, and `contDiff_wedge`,
  `ContDiff.wedge`, `ContDiffAt.wedge` — it is `C^n` in the pair, so a wedge of `C^n` families
  of forms is `C^n`;
* `domDomCongr_compContinuousLinearMap`, `norm_domDomCongr_le`, `domDomCongrL`,
  `ContDiff.domDomCongr`, `ContDiffAt.domDomCongr` — the same for reindexing along an
  equivalence of index types, which the iterated power needs at every step.

## Honest scope

⚠️ The constant in `norm_wedge_le` is the crude one (the number of shuffle classes times
`‖B‖`); no sharp bound is claimed. ⚠️ Associativity, graded commutativity and the Leibniz rule
of the wedge are still not here (they are algebraic facts about `AlternatingMap.domCoprod`
first, and Mathlib does not have them either; MATHLIB-ABSENT(ContinuousAlternatingMap.wedgeL)).

**Provenance and references.** The top-power plan (M2); `Alternating/Wedge.lean` (the wedge);
`Geometry/Manifold/WedgeForm.lean` (the consumer: the wedge of sections); the completed-work ledger.
-/

@[expose] public section

open TensorProduct Equiv

namespace ContinuousAlternatingMap

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [DecidableEq ιa] [DecidableEq ιb]

/-- One summand of the wedge, on a representative permutation. -/
theorem liftTensor_summand_mk'' (B : F →L[𝕜] G →L[𝕜] H)
    (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) (σ : Perm (ιa ⊕ ιb)) (v : ιa ⊕ ιb → E) :
    liftTensor B (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap
        (Quotient.mk'' σ) v)
      = (Perm.sign σ : ℤ) • B (a fun i => v (σ (Sum.inl i))) (b fun i => v (σ (Sum.inr i))) := by
  rw [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, Units.smul_def,
    map_zsmul, liftTensor_tmul]
  rfl

/-- ★ **Pullback commutes with the wedge.** -/
theorem wedge_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (B : F →L[𝕜] G →L[𝕜] H) (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) (L : E' →L[𝕜] E) :
    (wedge B a b).compContinuousLinearMap L
      = wedge B (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [compContinuousLinearMap_apply, wedge_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ =>
    rw [liftTensor_summand_mk'', liftTensor_summand_mk'']
    rfl

theorem wedge_add_left (B : F →L[𝕜] G →L[𝕜] H) (a₁ a₂ : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) :
    wedge B (a₁ + a₂) b = wedge B a₁ b + wedge B a₂ b := by
  ext v
  simp only [wedge_apply, add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ => simp only [liftTensor_summand_mk'', add_apply, map_add, _root_.add_apply,
      smul_add]

theorem wedge_smul_left (B : F →L[𝕜] G →L[𝕜] H) (c : 𝕜) (a : E [⋀^ιa]→L[𝕜] F)
    (b : E [⋀^ιb]→L[𝕜] G) : wedge B (c • a) b = c • wedge B a b := by
  ext v
  simp only [wedge_apply, smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ => simp only [liftTensor_summand_mk'', smul_apply, map_smul, _root_.smul_apply,
      smul_comm (Perm.sign σ : ℤ) c]

theorem wedge_add_right (B : F →L[𝕜] G →L[𝕜] H) (a : E [⋀^ιa]→L[𝕜] F) (b₁ b₂ : E [⋀^ιb]→L[𝕜] G) :
    wedge B a (b₁ + b₂) = wedge B a b₁ + wedge B a b₂ := by
  ext v
  simp only [wedge_apply, add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ => simp only [liftTensor_summand_mk'', add_apply, map_add, smul_add]

theorem wedge_smul_right (B : F →L[𝕜] G →L[𝕜] H) (c : 𝕜) (a : E [⋀^ιa]→L[𝕜] F)
    (b : E [⋀^ιb]→L[𝕜] G) : wedge B a (c • b) = c • wedge B a b := by
  ext v
  simp only [wedge_apply, smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ => simp only [liftTensor_summand_mk'', smul_apply, map_smul,
      smul_comm (Perm.sign σ : ℤ) c]

/-- ★ **The norm bound**: the wedge is a bounded bilinear map. -/
theorem norm_wedge_le (B : F →L[𝕜] G →L[𝕜] H) (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) :
    ‖wedge B a b‖ ≤ (Fintype.card (Perm.ModSumCongr ιa ιb) : ℝ) * ‖B‖ * ‖a‖ * ‖b‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro v
  rw [wedge_apply]
  have hterm : ∀ σ : Perm.ModSumCongr ιa ιb,
      ‖liftTensor B (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap σ v)‖
        ≤ ‖B‖ * ‖a‖ * ‖b‖ * ∏ i, ‖v i‖ := by
    intro σ
    induction σ using Quotient.inductionOn' with
    | h σ =>
      rw [liftTensor_summand_mk'']
      have hsign : ‖(Perm.sign σ : ℤ) • B (a fun i => v (σ (Sum.inl i))) (b fun i => v (σ (Sum.inr i)))‖
          = ‖B (a fun i => v (σ (Sum.inl i))) (b fun i => v (σ (Sum.inr i)))‖ := by
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
      have hp : ∏ k, ‖v k‖ = (∏ i, ‖v (σ (Sum.inl i))‖) * ∏ j, ‖v (σ (Sum.inr j))‖ := by
        have := Fintype.prod_sum_type (fun k => ‖v (σ k)‖)
        rw [Equiv.prod_comp σ (fun k => ‖v k‖)] at this
        exact this
      rw [hsign]
      calc ‖B (a fun i => v (σ (Sum.inl i))) (b fun i => v (σ (Sum.inr i)))‖
          ≤ ‖B‖ * ‖a fun i => v (σ (Sum.inl i))‖ * ‖b fun i => v (σ (Sum.inr i))‖ :=
            le_opNorm₂ B _ _
        _ ≤ ‖B‖ * (‖a‖ * ∏ i, ‖v (σ (Sum.inl i))‖) * (‖b‖ * ∏ j, ‖v (σ (Sum.inr j))‖) := by
            gcongr
            · exact le_opNorm a _
            · exact le_opNorm b _
        _ = ‖B‖ * ‖a‖ * ‖b‖ * ∏ i, ‖v i‖ := by rw [hp]; ring
  calc ‖∑ σ, liftTensor B (AlternatingMap.domCoprod.summand a.toAlternatingMap
          b.toAlternatingMap σ v)‖
      ≤ ∑ σ, ‖liftTensor B (AlternatingMap.domCoprod.summand a.toAlternatingMap
          b.toAlternatingMap σ v)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Perm.ModSumCongr ιa ιb, ‖B‖ * ‖a‖ * ‖b‖ * ∏ i, ‖v i‖ :=
        Finset.sum_le_sum fun σ _ => hterm σ
    _ = (Fintype.card (Perm.ModSumCongr ιa ιb) : ℝ) * ‖B‖ * ‖a‖ * ‖b‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- ★ **The wedge as a continuous bilinear map.** -/
noncomputable def wedgeL (B : F →L[𝕜] G →L[𝕜] H) :
    (E [⋀^ιa]→L[𝕜] F) →L[𝕜] (E [⋀^ιb]→L[𝕜] G) →L[𝕜] (E [⋀^ιa ⊕ ιb]→L[𝕜] H) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (wedge B) (wedge_add_left B) (wedge_smul_left B) (wedge_add_right B)
      (wedge_smul_right B))
    ((Fintype.card (Perm.ModSumCongr ιa ιb) : ℝ) * ‖B‖)
    (fun a b => norm_wedge_le B a b)

@[simp] theorem wedgeL_apply (B : F →L[𝕜] G →L[𝕜] H) (a : E [⋀^ιa]→L[𝕜] F)
    (b : E [⋀^ιb]→L[𝕜] G) : wedgeL B a b = wedge B a b := rfl

/-- ★ The wedge is `C^n` in the pair of forms. -/
theorem contDiff_wedge (B : F →L[𝕜] G →L[𝕜] H) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun p : (E [⋀^ιa]→L[𝕜] F) × (E [⋀^ιb]→L[𝕜] G) => wedge B p.1 p.2) :=
  (wedgeL (E := E) (ιa := ιa) (ιb := ιb) B).isBoundedBilinearMap.contDiff

theorem _root_.ContDiff.wedge {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B : F →L[𝕜] G →L[𝕜] H) {n : WithTop ℕ∞} {f : X → E [⋀^ιa]→L[𝕜] F} {g : X → E [⋀^ιb]→L[𝕜] G}
    (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x => wedge B (f x) (g x)) := by
  have h := (contDiff_wedge (E := E) (ιa := ιa) (ιb := ιb) B (n := n)).comp (hf.prodMk hg)
  simp only [Function.comp_def] at h
  exact h

theorem _root_.ContDiffAt.wedge {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B : F →L[𝕜] G →L[𝕜] H) {n : WithTop ℕ∞} {f : X → E [⋀^ιa]→L[𝕜] F}
    {g : X → E [⋀^ιb]→L[𝕜] G} {x : X}
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => wedge B (f x) (g x)) x := by
  have h := (contDiff_wedge (E := E) (ιa := ιa) (ιb := ιb) B (n := n)).contDiffAt.comp x
    (hf.prodMk hg)
  simp only [Function.comp_def] at h
  exact h

/-- Reindexing commutes with pullback. -/
theorem domDomCongr_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {ι ι' : Type*} (σ : ι ≃ ι') (f : E [⋀^ι]→L[𝕜] F) (L : E' →L[𝕜] E) :
    (domDomCongr σ f).compContinuousLinearMap L = domDomCongr σ (f.compContinuousLinearMap L) := by
  ext v; rfl

/-- Reindexing is norm-preserving, hence a continuous linear map. -/
theorem norm_domDomCongr_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι')
    (f : E [⋀^ι]→L[𝕜] F) : ‖domDomCongr σ f‖ ≤ ‖f‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [domDomCongr_apply]
  calc ‖f fun i => v (σ i)‖ ≤ ‖f‖ * ∏ i, ‖v (σ i)‖ := le_opNorm f _
    _ = ‖f‖ * ∏ i, ‖v i‖ := by rw [Equiv.prod_comp σ (fun i => ‖v i‖)]

/-- Reindexing as a continuous linear map. -/
noncomputable def domDomCongrL {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') :
    (E [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι']→L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := domDomCongr σ
      map_add' := fun f g => by ext v; rfl
      map_smul' := fun c f => by ext v; rfl }
    1 (fun f => by simpa using norm_domDomCongr_le σ f)

@[simp] theorem domDomCongrL_apply {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι')
    (f : E [⋀^ι]→L[𝕜] F) : domDomCongrL σ f = domDomCongr σ f := rfl

theorem _root_.ContDiff.domDomCongr {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') {n : WithTop ℕ∞}
    {f : X → E [⋀^ι]→L[𝕜] F} (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (fun x => domDomCongr σ (f x)) := by
  have h := (domDomCongrL (E := E) (F := F) σ).contDiff (n := n) |>.comp hf
  exact h

theorem _root_.ContDiffAt.domDomCongr {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') {n : WithTop ℕ∞}
    {f : X → E [⋀^ι]→L[𝕜] F} {x : X} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => domDomCongr σ (f x)) x := by
  have h := (domDomCongrL (E := E) (F := F) σ).contDiff (n := n) |>.contDiffAt.comp x hf
  exact h

end ContinuousAlternatingMap
