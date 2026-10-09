/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.DiagonalOperator

/-!
# Conjugating an unbounded operator by a unitary

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #64(i), the first of the three pieces that row records itself as waiting on.

★★★ `LinearPMap.conjIsometry` — **`U T U⁻¹` for a unitary `U` and a partially defined operator
`T`**, with domain `U(dom T)`, and the two transfers that make it worth having:

* ★★★ `LinearPMap.adjoint_conjIsometry` — **the adjoint conjugates**: `(U T U⁻¹)† = U T† U⁻¹`, hence
  ★★★ `IsSelfAdjoint.conjIsometry` — **a unitary conjugate of a self-adjoint operator is
  self-adjoint**;
* ★★★ `LinearPMap.spectrum_conjIsometry` — **the spectrum is unchanged**, through
  ★★ `LinearPMap.resolventSet_conjIsometry`.

Mathlib has `LinearMap.compPMap` (a bounded map after a partial one, same domain) and
`LinearPMap.comp` (two partial ones, with a domain condition), and nothing that moves an operator
*across* a unitary — which is what a change of representation is. Unitary equivalence is the standard
way an unbounded operator becomes tractable: the free Hamiltonian is multiplication by a symbol in
the momentum representation and a differential operator in the position one, and this is the bridge.

## What makes it short

The `≤` order on `LinearPMap` does the work. Rather than computing the adjoint's domain through
`adjointDomain`'s continuity condition, `conjIsometry U T†` is shown to be a *formal* adjoint of
`conjIsometry U T` — a four-step inner-product computation, since a unitary preserves inner products
— so `IsFormalAdjoint.le_adjoint` gives one inclusion. The other comes from the same lemma applied
to `U⁻¹`, through ★ `LinearPMap.conjIsometry_symm_conjIsometry` (conjugation is an involution) and
★ `LinearPMap.conjIsometry_mono` (it is monotone), and `le_antisymm` closes it.

## Honest scope

⚠️ **Unitary, not merely isometric.** `U` is a `LinearIsometryEquiv`: the inverse has to exist for
the conjugate to be defined on all of `U(dom T)`, and surjectivity is what makes the domain dense
again. A non-surjective isometry gives a compression, not a conjugate, and nothing here covers it.

⚠️ **Same field.** `U` is `𝕜`-linear, so this is not the antiunitary (conjugate-linear) case, which
reverses the order of products and is a genuinely different statement.

⚠️ **No functional calculus.** That the conjugate has the same functional calculus, or that unitary
equivalence preserves the spectral measure, is not claimed — only the resolvent set, which is what
the spectrum is defined from here.

References: [`DiagonalOperator.lean`](DiagonalOperator.lean) (`LinearPMap.IsResolventAt`,
`LinearPMap.spectrum`), [`MultiplicationOperator.lean`](MultiplicationOperator.lean) (the
multiplication operators this is for), `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`
(`adjoint`, `IsFormalAdjoint`); `specs/BACKLOG.md` #64.
-/

@[expose] public section

open scoped ComplexConjugate LinearPMap

noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### The conjugate -/

/-- The image of a submodule under a unitary, as a set, is the set image — the bridge every
membership step below goes through. -/
theorem symm_mem_of_mem_map (U : E ≃ₗᵢ[𝕜] F) (p : Submodule 𝕜 E) {y : F}
    (hy : y ∈ p.map (U.toLinearEquiv : E →ₗ[𝕜] F)) : U.symm y ∈ p := by
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

/-- **`U T U⁻¹`**, with domain `U(dom T)`. -/
def conjIsometry (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) : F →ₗ.[𝕜] F where
  domain := T.domain.map (U.toLinearEquiv : E →ₗ[𝕜] F)
  toFun :=
    { toFun := fun y => U (T ⟨U.symm (y : F), symm_mem_of_mem_map U T.domain y.2⟩)
      map_add' := by
        intro y z
        have hstep : (⟨U.symm ((y + z : _) : F), symm_mem_of_mem_map U T.domain (y + z).2⟩
              : T.domain)
            = ⟨U.symm (y : F), symm_mem_of_mem_map U T.domain y.2⟩
              + ⟨U.symm (z : F), symm_mem_of_mem_map U T.domain z.2⟩ := by
          refine Subtype.ext ?_
          simp
        rw [hstep, T.map_add, U.map_add]
      map_smul' := by
        intro c y
        have hstep : (⟨U.symm ((c • y : _) : F), symm_mem_of_mem_map U T.domain (c • y).2⟩
              : T.domain)
            = c • ⟨U.symm (y : F), symm_mem_of_mem_map U T.domain y.2⟩ := by
          refine Subtype.ext ?_
          simp
        rw [hstep, T.map_smul, U.map_smul, RingHom.id_apply] }

@[simp]
theorem conjIsometry_domain (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) :
    (conjIsometry U T).domain = T.domain.map (U.toLinearEquiv : E →ₗ[𝕜] F) := rfl

theorem conjIsometry_apply (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) (y : (conjIsometry U T).domain) :
    conjIsometry U T y = U (T ⟨U.symm (y : F), symm_mem_of_mem_map U T.domain y.2⟩) := rfl

/-- Membership in the conjugate's domain, in the form every proof below wants. -/
theorem mem_conjIsometry_domain (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) {x : E} (hx : x ∈ T.domain) :
    U x ∈ (conjIsometry U T).domain :=
  ⟨x, hx, rfl⟩

/-- The conjugate's value at an image point, which is the computational form. -/
theorem conjIsometry_apply_image (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) (x : T.domain) :
    conjIsometry U T ⟨U (x : E), mem_conjIsometry_domain U T x.2⟩ = U (T x) := by
  rw [conjIsometry_apply]
  congr 2
  refine Subtype.ext ?_
  simp

/-- The conjugate's value at any element whose coordinate is an image point — the form that avoids
rewriting under a membership proof. -/
theorem conjIsometry_apply_of_eq (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) (x : T.domain)
    (y : (conjIsometry U T).domain) (hxy : (y : F) = U (x : E)) :
    conjIsometry U T y = U (T x) := by
  rw [conjIsometry_apply]
  congr 2
  refine Subtype.ext ?_
  have hstep : U.symm (y : F) = U.symm (U (x : E)) := congrArg U.symm hxy
  rwa [LinearIsometryEquiv.symm_apply_apply] at hstep

/-- ★ **Conjugation is an involution**, which is what gives the second half of the adjoint
identity. -/
theorem conjIsometry_symm_conjIsometry (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) :
    conjIsometry U.symm (conjIsometry U T) = T := by
  refine LinearPMap.ext ?_ ?_
  · refine Submodule.ext fun x => ?_
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    · intro hx
      exact ⟨U x, mem_conjIsometry_domain U T hx, by simp⟩
  · intro x y hxy
    rw [conjIsometry_apply, conjIsometry_apply, LinearIsometryEquiv.symm_apply_apply]
    congr 1
    refine Subtype.ext ?_
    simp

/-- The other direction of the involution, which the adjoint identity closes with. -/
theorem conjIsometry_conjIsometry_symm (U : E ≃ₗᵢ[𝕜] F) (X : F →ₗ.[𝕜] F) :
    conjIsometry U (conjIsometry U.symm X) = X := by
  have h := conjIsometry_symm_conjIsometry U.symm X
  rwa [LinearIsometryEquiv.symm_symm] at h

/-- ★ **Conjugation is monotone** for the extension order. -/
theorem conjIsometry_mono (U : E ≃ₗᵢ[𝕜] F) {S T : E →ₗ.[𝕜] E} (h : S ≤ T) :
    conjIsometry U S ≤ conjIsometry U T := by
  obtain ⟨hdom, hval⟩ := h
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hdom hx, rfl⟩
  · intro y z hyz
    rw [conjIsometry_apply, conjIsometry_apply]
    congr 1
    exact hval (congrArg U.symm hyz)

/-- The conjugate's domain is dense when the original's is, because a unitary is a
homeomorphism. -/
theorem dense_conjIsometry_domain (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E)
    (hT : Dense (T.domain : Set E)) : Dense ((conjIsometry U T).domain : Set F) := by
  have himg : ((conjIsometry U T).domain : Set F) = U '' (T.domain : Set E) := by
    rw [conjIsometry_domain, Submodule.map_coe]
    rfl
  rw [himg]
  exact U.toHomeomorph.isDenseEmbedding.dense_image.2 hT

/-! ### The spectrum is unchanged -/

/-- The conjugate of a bounded operator, as a bounded operator. -/
def conjCLM (U : E ≃ₗᵢ[𝕜] F) (S : E →L[𝕜] E) : F →L[𝕜] F :=
  (U.toContinuousLinearEquiv.toContinuousLinearMap.comp S).comp
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem conjCLM_apply (U : E ≃ₗᵢ[𝕜] F) (S : E →L[𝕜] E) (y : F) :
    conjCLM U S y = U (S (U.symm y)) := rfl

/-- **The conjugated resolvent is a resolvent of the conjugate.** -/
theorem IsResolventAt.conjIsometry (U : E ≃ₗᵢ[𝕜] F) {T : E →ₗ.[𝕜] E} {z : 𝕜}
    {S : E →L[𝕜] E} (h : T.IsResolventAt z S) :
    (LinearPMap.conjIsometry U T).IsResolventAt z (conjCLM U S) := by
  have hmaps : ∀ y : F, conjCLM U S y ∈ (LinearPMap.conjIsometry U T).domain := by
    intro y
    rw [conjCLM_apply]
    exact mem_conjIsometry_domain U T (h.maps_mem _)
  refine { maps_mem := hmaps, right_inv := ?_, left_inv := ?_ }
  · intro y
    have hval : LinearPMap.conjIsometry U T ⟨conjCLM U S y, hmaps y⟩
        = U (T ⟨S (U.symm y), h.maps_mem _⟩) :=
      conjIsometry_apply_of_eq U T _ _ (conjCLM_apply U S y)
    rw [hval, conjCLM_apply, ← U.map_smul, ← U.map_sub, h.right_inv,
      LinearIsometryEquiv.apply_symm_apply]
  · intro x
    obtain ⟨y, hy, hxy⟩ := x.2
    have hval : LinearPMap.conjIsometry U T x = U (T ⟨y, hy⟩) :=
      conjIsometry_apply_of_eq U T ⟨y, hy⟩ x hxy.symm
    have hcoe : (x : F) = U y := hxy.symm
    rw [hval, hcoe, conjCLM_apply, ← U.map_smul, ← U.map_sub,
      LinearIsometryEquiv.symm_apply_apply, h.left_inv]

/-- ★★ **The resolvent set is unchanged by a unitary conjugation.** -/
theorem resolventSet_conjIsometry (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) :
    resolventSet (conjIsometry U T) = resolventSet T := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro z hz
    obtain ⟨S, hS⟩ := hz
    refine ⟨conjCLM U.symm S, ?_⟩
    have h1 := hS.conjIsometry U.symm
    rwa [conjIsometry_symm_conjIsometry] at h1
  · intro z hz
    obtain ⟨S, hS⟩ := hz
    exact ⟨_, hS.conjIsometry U⟩

/-- ★★★ **The spectrum is unchanged by a unitary conjugation** — a change of representation does
not move the spectrum. -/
theorem spectrum_conjIsometry (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E) :
    LinearPMap.spectrum (conjIsometry U T) = LinearPMap.spectrum T := by
  rw [LinearPMap.spectrum, LinearPMap.spectrum, resolventSet_conjIsometry]

/-! ### The adjoint conjugates -/

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The conjugate of a formal adjoint is a formal adjoint of the conjugate: four inner products,
each step a unitary moving across. -/
theorem IsFormalAdjoint.conjIsometry (U : E ≃ₗᵢ[𝕜] F) {T S : E →ₗ.[𝕜] E}
    (h : T.IsFormalAdjoint S) :
    (LinearPMap.conjIsometry U T).IsFormalAdjoint (LinearPMap.conjIsometry U S) := by
  intro y z
  obtain ⟨a, ha, hay⟩ := y.2
  obtain ⟨b, hb, hbz⟩ := z.2
  have hy : (y : F) = U a := hay.symm
  have hz : (z : F) = U b := hbz.symm
  have h1 : LinearPMap.conjIsometry U T y = U (T ⟨a, ha⟩) := by
    have hrepl : y = ⟨U ((⟨a, ha⟩ : T.domain) : E), mem_conjIsometry_domain U T ha⟩ :=
      Subtype.ext hy
    rw [hrepl, conjIsometry_apply_image]
  have h2 : LinearPMap.conjIsometry U S z = U (S ⟨b, hb⟩) := by
    have hrepl : z = ⟨U ((⟨b, hb⟩ : S.domain) : E), mem_conjIsometry_domain U S hb⟩ :=
      Subtype.ext hz
    rw [hrepl, conjIsometry_apply_image]
  rw [h1, h2, hy, hz, U.inner_map_map, U.inner_map_map]
  exact h ⟨a, ha⟩ ⟨b, hb⟩

/-- ★★★ **The adjoint conjugates.** `(U T U⁻¹)† = U T† U⁻¹`. -/
theorem adjoint_conjIsometry (U : E ≃ₗᵢ[𝕜] F) (T : E →ₗ.[𝕜] E)
    (hT : Dense (T.domain : Set E)) :
    (conjIsometry U T)† = conjIsometry U (T†) := by
  -- one inclusion, from maximality of the adjoint
  have hle : conjIsometry U (T†) ≤ (conjIsometry U T)† := by
    refine LinearPMap.IsFormalAdjoint.le_adjoint (dense_conjIsometry_domain U T hT) ?_
    exact (LinearPMap.adjoint_isFormalAdjoint hT).symm.conjIsometry U
  -- the other, from the same statement for `U⁻¹` through the involution
  have hle' : (conjIsometry U T)† ≤ conjIsometry U (T†) := by
    have hdense : Dense ((conjIsometry U T).domain : Set F) := dense_conjIsometry_domain U T hT
    have h1 : conjIsometry U.symm ((conjIsometry U T)†) ≤ T† := by
      have h2 : conjIsometry U.symm (((conjIsometry U T))†)
          ≤ (conjIsometry U.symm (conjIsometry U T))† := by
        refine LinearPMap.IsFormalAdjoint.le_adjoint
          (dense_conjIsometry_domain U.symm (conjIsometry U T) hdense) ?_
        exact (LinearPMap.adjoint_isFormalAdjoint hdense).symm.conjIsometry U.symm
      rwa [conjIsometry_symm_conjIsometry] at h2
    have h3 := conjIsometry_mono U h1
    rwa [conjIsometry_conjIsometry_symm] at h3
  exact le_antisymm hle' hle

/-- ★★★ **A unitary conjugate of a self-adjoint operator is self-adjoint.** -/
theorem _root_.IsSelfAdjoint.conjIsometry {T : E →ₗ.[𝕜] E} (hT : IsSelfAdjoint T)
    (U : E ≃ₗᵢ[𝕜] F) : IsSelfAdjoint (LinearPMap.conjIsometry U T) := by
  rw [LinearPMap.isSelfAdjoint_def, LinearPMap.adjoint_conjIsometry U T hT.dense_domain]
  rw [LinearPMap.isSelfAdjoint_def] at hT
  rw [hT]

end LinearPMap

end

end
