/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace

/-!
# A linear equivalence induces an equivalence of projective spaces

**Category:** 1-Mathlib (staged upstream material).
BACKLOG #133, the piece everything else on that row needs.

Mathlib has `Projectivization.map`, which sends an **injective semilinear map** `V →ₛₗ[σ] W` to a map
`ℙ K V → ℙ L W`, and this repository's
[`Topology.lean`](Topology.lean) has `mapEquiv`, the action of a linear **self**-equivalence
`V ≃ₗ[K] V`. What is missing in both is the obvious thing in between: a linear equivalence of
**different** spaces induces an *equivalence* of their projectivizations.

Without it, two projective spaces that are the same up to a change of index — `ℙ ℂ (ℂ^(ι))` and
`ℙ ℂ (ℂ^(ι'))` for `ι ≃ ι'` — cannot be identified at all, only mapped one way with no inverse. That
is exactly the gap BACKLOG #133 records between the CV field arena
`ℙ ℂ (EuclideanSpace ℂ (FieldConfig K N))` and `LF4.CPN (N ^ K)`.

* `Projectivization.congr e` — the equivalence, with ★ `congr_mk` on representatives and
  `congr_symm` identifying its inverse as the equivalence of `e.symm`;
* `congr_refl`, `congr_trans` — it is functorial, so composing index changes composes;
* ★ `congr_continuous` — it is continuous when the linear equivalence is.

⚠️ **No measurability lemma here, deliberately.** `MeasureSpace.lean` installs the Borel
structure on `ℙ K V` only under `[RCLike K]` and finite-dimensional normed `V`, and a general
`congr_measurable` stated without those hypotheses resolves `MeasurableSpace (ℙ K V)` by some other
path — the unused-section-variable linter caught exactly that. Rather than land a measurability
claim whose σ-algebra is not pinned, measurability is left to the use site, where the spaces are
concrete and `(congr_continuous …).measurable` fires against the intended instance.

## Scope

The construction is for a **linear** equivalence over one ring. Mathlib's `map` is semilinear, and
the semilinear equivalence version would need `RingHomInvPair` bookkeeping on both sides; nothing in
this repository wants it, and the linear case is what an index change gives.

⚠️ Nothing here is about measures *yet*: `congr_measurable` says the map is measurable, not that it
pushes any particular measure to any particular measure. Measure preservation is a separate
statement about the two measures involved and is not claimed.

References: `Mathlib/LinearAlgebra/Projectivization/Basic.lean` (`map`, `map_mk`, `ind`,
`mk_eq_mk_iff'`); [`Topology.lean`](Topology.lean) (`mapOfInjective_continuous`, `mapEquiv`);
[`MeasureSpace.lean`](MeasureSpace.lean) (the Borel structure on `ℙ K V`);
`specs/BACKLOG.md` #133, #131.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K : Type*} [DivisionRing K]
variable {V W X : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X]

/-- **A linear equivalence of the underlying spaces induces an equivalence of their
projectivizations.** The two directions are `Projectivization.map` of `e` and of `e.symm`, and they
invert each other because they do so on representatives. -/
def congr (e : V ≃ₗ[K] W) : ℙ K V ≃ ℙ K W where
  toFun := map e.toLinearMap e.injective
  invFun := map e.symm.toLinearMap e.symm.injective
  left_inv := by
    intro p
    induction p using Projectivization.ind with
    | h v hv =>
        rw [map_mk, map_mk]
        exact (mk_eq_mk_iff' K _ _ _ _).mpr
          ⟨1, by rw [one_smul]; exact (e.symm_apply_apply v).symm⟩
  right_inv := by
    intro p
    induction p using Projectivization.ind with
    | h w hw =>
        rw [map_mk, map_mk]
        exact (mk_eq_mk_iff' K _ _ _ _).mpr
          ⟨1, by rw [one_smul]; exact (e.apply_symm_apply w).symm⟩

/-- The induced map, in `Projectivization.map` form — the shape `map_mk` rewrites with. -/
theorem congr_apply (e : V ≃ₗ[K] W) (p : ℙ K V) :
    congr e p = Projectivization.map e.toLinearMap e.injective p := rfl

/-- ★ **On representatives it is what it should be.** -/
theorem congr_mk (e : V ≃ₗ[K] W) (v : V) (hv : v ≠ 0) (hev : e v ≠ 0) :
    congr e (mk K v hv) = mk K (e v) hev := rfl

/-- ★ The inverse of the induced equivalence is the one induced by the inverse. -/
theorem congr_symm (e : V ≃ₗ[K] W) : (congr e).symm = congr e.symm := rfl

theorem congr_symm_mk (e : V ≃ₗ[K] W) (w : W) (hw : w ≠ 0) (hew : e.symm w ≠ 0) :
    (congr e).symm (mk K w hw) = mk K (e.symm w) hew := rfl

@[simp] theorem congr_refl : congr (LinearEquiv.refl K V) = Equiv.refl (ℙ K V) := by
  ext p
  induction p using Projectivization.ind with
  | h v hv => rfl

/-- **Functorial**: composing index changes composes the induced equivalences. -/
theorem congr_trans (e₁ : V ≃ₗ[K] W) (e₂ : W ≃ₗ[K] X) :
    congr (e₁.trans e₂) = (congr e₁).trans (congr e₂) := by
  ext p
  induction p using Projectivization.ind with
  | h v hv => rfl

/-! ### Continuity and measurability -/

section Topology

variable [TopologicalSpace V] [TopologicalSpace W]

/-- ★ **The induced equivalence is continuous** when the linear equivalence is. -/
theorem congr_continuous (e : V ≃ₗ[K] W) (he : Continuous (e : V → W)) :
    Continuous (congr e) :=
  mapOfInjective_continuous e.toLinearMap e.injective he

end Topology

end Projectivization

end
