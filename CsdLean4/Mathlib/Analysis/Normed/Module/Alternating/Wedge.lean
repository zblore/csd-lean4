/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# The exterior product of *continuous* alternating maps

**TERM-SCOPE(Kahler)** — the phrase "top-power identity" appears below in the *restricted*
sense `specs/TERMS.md` records: the identity is what this file makes **sayable**, and it is
neither stated nor proved here. (The marker is repository bookkeeping; it goes with the
`References` block if the file is ever sent upstream.)

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Analysis.Normed.Module.Alternating`).

Mathlib has the exterior product of two `AlternatingMap`s (`AlternatingMap.domCoprod`,
valued in the **tensor product** of the two codomains) and it has
`ContinuousAlternatingMap`. It does not have the exterior product of two *continuous*
alternating maps: `domCoprod` occurs in exactly three algebraic files, and
`ContinuousAlternatingMap.domCoprod` is zero declarations at the pin.
MATHLIB-ABSENT(ContinuousAlternatingMap.domCoprod)

⚠️ **And it cannot be stated in the tensor-valued form.** There is no topology on
`F ⊗[𝕜] G` at the pin, so `E [⋀^ιa ⊕ ιb]→L[𝕜] (F ⊗[𝕜] G)` is not a type. The standard
fix, and the one taken here, is to pair the two codomains through a **continuous bilinear
map** `B : F →L[𝕜] G →L[𝕜] H`. Every use in sight has that shape — for real-valued forms
`B` is multiplication — and the tensor-valued version is recovered from this one the
moment a topology on the tensor product exists, by taking `B` to be `TensorProduct.mk`.

## Contents

* `ContinuousLinearMap.liftTensor` — the linear map `F ⊗[𝕜] G →ₗ[𝕜] H` induced by a
  continuous bilinear `B`;
* `ContinuousAlternatingMap.continuous_liftTensor_summand` — each summand of the
  antisymmetrisation, paired through `B`, is continuous. This is the whole mathematical
  content of the file;
* ★ `ContinuousAlternatingMap.wedge` — the exterior product itself;
* `wedge_toAlternatingMap` (`rfl`) — it **is** the algebraic `AlternatingMap.domCoprod`
  postcomposed with `liftTensor B`, so every algebraic fact about `domCoprod` transfers
  and this file adds exactly one thing: boundedness;
* `wedge_apply` — the pointwise signed sum over `Equiv.Perm.ModSumCongr ιa ιb`.

## Honest scope

Delivered: the **binary** product and its two defining equations. NOT built here, and
not claimed:

* **associativity**, **graded commutativity** and the Leibniz rule for `extDeriv`. All
  three are algebraic facts about `domCoprod` before they are facts about its continuous
  form, so the transport route (`wedge_toAlternatingMap`) can only carry what the
  algebraic side already proves. None of them is proved here;
* the **iterated power**: the index type of `wedge` is `ιa ⊕ ιb`, so an iterated product
  on `Fin (2 * k)` needs a `domDomCongr` along `finSumFinEquiv` at each step plus a
  recursion on `k`. That is the next brick, not this one;
* any **nonvanishing** statement. A wedge can be zero for good reasons (a 1-form with
  itself), and nothing here rules that out in any particular case;
* a **norm bound**. The construction goes through continuity rather than
  `AlternatingMap.mkContinuous`, so no constant is produced. The bound is true and is a
  natural follow-up; it is not needed in order to state a top power.

The point of the file is narrow and worth stating plainly: with it, a top-power identity
of the shape `ω^(N-1)/(N-1)! = μ_FS` becomes **sayable in Lean**. It does not make any
such statement true, and nothing in this repository's physics waits on it
(`MATHLIB-GAPS.md`, the Kahler / symplectic manifold API row; step (1) of the staged plan
in the XL section of `specs/BACKLOG.md`).

References: `MATHLIB-GAPS.md`; `specs/BACKLOG.md` (XL, "Manifold exterior calculus");
`specs/TERMS.md` (`moment map`);
`CsdLean4/Mathlib/Analysis/InnerProductSpace/KahlerWedge.lean` (the consumer).
-/

@[expose] public section

open TensorProduct Equiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [DecidableEq ιa] [DecidableEq ιb]

namespace ContinuousLinearMap

/-- The linear map `F ⊗[𝕜] G →ₗ[𝕜] H` induced by a continuous bilinear map `B`.

This is `TensorProduct.lift` of the underlying bilinear map. The continuity of `B` is not
used here — there is no topology on the source — only downstream, where the composite is
shown to be a continuous function of the vector family. -/
noncomputable def liftTensor (B : F →L[𝕜] G →L[𝕜] H) : F ⊗[𝕜] G →ₗ[𝕜] H :=
  TensorProduct.lift ((ContinuousLinearMap.coeLM 𝕜).comp B.toLinearMap)

@[simp]
theorem liftTensor_tmul (B : F →L[𝕜] G →L[𝕜] H) (x : F) (y : G) :
    liftTensor B (x ⊗ₜ[𝕜] y) = B x y := by
  simp [liftTensor]

end ContinuousLinearMap

namespace ContinuousAlternatingMap

open ContinuousLinearMap

section DomDomCongr

variable {ι ι' : Type*}

/-- Reindex a continuous alternating map along an equivalence of index types.

Mathlib has this for `AlternatingMap` (`AlternatingMap.domDomCongr`) and for
`ContinuousMultilinearMap` (`ContinuousMultilinearMap.domDomCongr`), but not for
`ContinuousAlternatingMap` — MATHLIB-ABSENT(ContinuousAlternatingMap.domDomCongr).

It is needed here rather than merely wanted: `wedge` is indexed by `ιa ⊕ ιb`, while
`extDeriv` and every other differential-form API in Mathlib is indexed by `Fin n`, so
without a reindexing the product of two forms cannot be fed back into the calculus it
came from. -/
def domDomCongr (σ : ι ≃ ι') (f : E [⋀^ι]→L[𝕜] F) : E [⋀^ι']→L[𝕜] F where
  toContinuousMultilinearMap := f.toContinuousMultilinearMap.domDomCongr σ
  map_eq_zero_of_eq' v i j hv hij :=
    f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
      (by simpa using hv) (by simpa using hij)

@[simp]
theorem domDomCongr_apply (σ : ι ≃ ι') (f : E [⋀^ι]→L[𝕜] F) (v : ι' → E) :
    domDomCongr σ f v = f fun i => v (σ i) :=
  rfl

end DomDomCongr

/-- **The mathematical content of this file.** One summand of the antisymmetrisation,
paired through `B`, is a continuous function of the vector family.

The summand is a class in `Equiv.Perm.ModSumCongr ιa ιb`; on a representative `σ` it is
`Equiv.Perm.sign σ • (a (v ∘ σ ∘ Sum.inl) ⊗ₜ b (v ∘ σ ∘ Sum.inr))`. Pairing through `B`
and reading off continuity needs precomposition with `σ` (continuous coordinatewise), `a`
and `b`, and the **joint** continuity of `B` (`ContinuousLinearMap.continuous₂`) — being
separately continuous in each slot would not suffice. -/
theorem continuous_liftTensor_summand (B : F →L[𝕜] G →L[𝕜] H)
    (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) (σ : Perm.ModSumCongr ιa ιb) :
    Continuous fun v : ιa ⊕ ιb → E =>
      liftTensor B
        (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap σ v) := by
  induction σ using Quotient.inductionOn' with
  | h σ =>
    have key : ∀ v : ιa ⊕ ιb → E,
        liftTensor B (AlternatingMap.domCoprod.summand a.toAlternatingMap
            b.toAlternatingMap (Quotient.mk'' σ) v)
          = (Equiv.Perm.sign σ : ℤ) •
              B (a fun i => v (σ (Sum.inl i))) (b fun i => v (σ (Sum.inr i))) := by
      intro v
      rw [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply,
        MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, Units.smul_def,
        map_zsmul, liftTensor_tmul]
      rfl
    have hA : Continuous fun v : ιa ⊕ ιb → E => fun i : ιa => v (σ (Sum.inl i)) :=
      continuous_pi fun i => continuous_apply _
    have hB : Continuous fun v : ιa ⊕ ιb → E => fun i : ιb => v (σ (Sum.inr i)) :=
      continuous_pi fun i => continuous_apply _
    simp only [key]
    exact (B.continuous₂.comp₂ (a.cont.comp hA) (b.cont.comp hB)).const_smul
      ((Equiv.Perm.sign σ : ℤ))

/-- ★ **The exterior product of two continuous alternating maps**, with the codomains
paired through a continuous bilinear map `B`.

Its underlying alternating map is the algebraic `AlternatingMap.domCoprod` postcomposed
with `ContinuousLinearMap.liftTensor B` (`wedge_toAlternatingMap`, which is `rfl`); the
new content is that the result is continuous. -/
noncomputable def wedge (B : F →L[𝕜] G →L[𝕜] H)
    (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) : E [⋀^ιa ⊕ ιb]→L[𝕜] H where
  toMultilinearMap :=
    ((liftTensor B).compAlternatingMap
      (a.toAlternatingMap.domCoprod b.toAlternatingMap)).toMultilinearMap
  cont := by
    refine Continuous.congr
      (continuous_finsetSum Finset.univ fun σ _ => continuous_liftTensor_summand B a b σ)
      fun v => ?_
    show _ = (liftTensor B) ((a.toAlternatingMap.domCoprod b.toAlternatingMap) v)
    rw [AlternatingMap.domCoprod_apply, _root_.sum_apply]
    exact (_root_.map_sum _ _ _).symm
  map_eq_zero_of_eq' := ((liftTensor B).compAlternatingMap
    (a.toAlternatingMap.domCoprod b.toAlternatingMap)).map_eq_zero_of_eq'

/-- The continuous exterior product **is** the algebraic one, paired through `B`. Every
fact Mathlib proves about `AlternatingMap.domCoprod` transfers along this equation. -/
@[simp]
theorem wedge_toAlternatingMap (B : F →L[𝕜] G →L[𝕜] H)
    (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) :
    (wedge B a b).toAlternatingMap
      = (liftTensor B).compAlternatingMap
          (a.toAlternatingMap.domCoprod b.toAlternatingMap) :=
  rfl

/-- The pointwise formula: a signed sum over shuffle classes. -/
theorem wedge_apply (B : F →L[𝕜] G →L[𝕜] H)
    (a : E [⋀^ιa]→L[𝕜] F) (b : E [⋀^ιb]→L[𝕜] G) (v : ιa ⊕ ιb → E) :
    wedge B a b v = ∑ σ : Perm.ModSumCongr ιa ιb,
      liftTensor B
        (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap σ v) := by
  show (liftTensor B) ((a.toAlternatingMap.domCoprod b.toAlternatingMap) v) = _
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply]
  exact _root_.map_sum _ _ _

end ContinuousAlternatingMap
