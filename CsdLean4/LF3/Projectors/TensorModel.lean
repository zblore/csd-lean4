/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Hamiltonian
import CsdLean4.Mathlib.Topology.Algebra.Module.LinearMap

/-!
# LF3 Projectors / TensorModel: derive ProjectorAlgebra from a tensor structure

**Category:** 3-Local (LF3 v2 derivation: `ProjectorAlgebra` / `MeasurementUnitary` from `TensorEmbedding` / `UnitaryTensorEmbedding`).

Paper §9.7 v2 derivation target.

The abstract `ProjectorAlgebra` in `LF3/Projectors/Core.lean` carries the
four projection identities (self-adjointness, idempotence, mutual
orthogonality, completeness) as fields, per spec §9.7's "v1.00 takes the
algebra as data" carve-out. This module supplies the corresponding v2
derivation: given an abstract bipartite tensor-factor structure on `H_SA`
(encoded as a `TensorEmbedding K_A K_B H_SA`), the four projection-algebra
fields become *theorems* derived from the `BinaryPointerProjectors`
per-wing data plus the tensor-embedding algebraic laws.

This discharges the ProjectorAlgebra half of D4 / G6 (the composite tensor
structure debt) at the Lean level. The MeasurementUnitary half of D4 / G6
splits in two: the factorisation field is feasible by the same
TensorEmbedding-based derivation (immediate follow-up); the eigenstate-
action field requires operator-exponential / Stone machinery and is
explicitly LF4-or-later per spec §9.5.

## Design

A `TensorEmbedding` encodes the bipartite tensor structure of `H_SA`
through two lift functions `liftA`, `liftB` that embed per-wing operators
into `H_SA`-operators (the implicit "tensor with identity on the other
factor and on the system factor" map), together with the algebraic
properties that make them unital *-algebra homomorphisms with commuting
images.

This formulation avoids Mathlib's tensor-product-of-inner-product-spaces
API (uneven coverage). The system Hilbert space `H_AB` itself is not
exposed as a field; only the projections through `liftA` and `liftB`
matter for the ProjectorAlgebra derivation. Concrete instantiations
(matrix realisations via `Matrix.kroneckerMap`, or full Hilbert-space
constructions via `TensorProduct ℂ`) are left to LF4 or to callers; this
module gives the abstract derivation.

`ProjectorAlgebra.ofTensorEmbedding` builds the abstract projector
algebra from a `TensorEmbedding` plus the `SystemApparatusSetup`'s
per-wing `BinaryPointerProjectors`. The four fields are theorems.

Callers without a `TensorEmbedding` (LF3 v1.00 callers) continue to
construct `ProjectorAlgebra` directly; this module is additive, not
invasive.
-/

open scoped BigOperators

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]

/-! ### Helper: reverse pointer-projector orthogonality

`BinaryPointerProjectors.orthogonal` gives `proj .plus ∘L proj .minus = 0`
in that order. The `orthogonal` proof for `ProjectorAlgebra.ofTensorEmbedding`
also needs `proj .minus ∘L proj .plus = 0` (case `s = .minus, s' = .plus`).
It follows from completeness and idempotence:
`proj .minus ∘L proj .plus = proj .minus ∘L (1 - proj .minus)
= proj .minus - proj .minus ∘L proj .minus = proj .minus - proj .minus = 0`. -/

lemma BinaryPointerProjectors.orthogonal_rev {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (P : BinaryPointerProjectors K) :
    P.proj .minus ∘L P.proj .plus = 0 :=
  ContinuousLinearMap.comp_complement_of_idem
    (P.proj .plus) (P.proj .minus) (P.idem .minus) P.complete

/-! ### TensorEmbedding -/

/-- Abstract bipartite tensor-factor structure on `H_SA` with `K_A` and `K_B`
    as the two pointer-side factors. Encoded through lift functions
    `liftA : (K_A →L[ℂ] K_A) → (H_SA →L[ℂ] H_SA)` and similarly `liftB`,
    satisfying unital algebra-homomorphism laws (composition, identity,
    addition, zero) and commuting images.

    Mathematically: `liftA(f)` realises `f ⊗ I_AB ⊗ I_{K_B}` and `liftB(g)`
    realises `I_{K_A} ⊗ I_AB ⊗ g` under an implicit identification
    `H_SA ≅ H_AB ⊗ K_A ⊗ K_B`. The system Hilbert space `H_AB` itself is
    not a field of the structure; only the projections through `liftA` and
    `liftB` matter for the ProjectorAlgebra derivation. -/
structure TensorEmbedding (K_A K_B H_SA : Type*)
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    where
  /-- Lift of A-side operators to `H_SA`-operators. -/
  liftA : (K_A →L[ℂ] K_A) → (H_SA →L[ℂ] H_SA)
  /-- Lift of B-side operators. -/
  liftB : (K_B →L[ℂ] K_B) → (H_SA →L[ℂ] H_SA)
  /-- `liftA` preserves composition. -/
  liftA_comp : ∀ f g, liftA (f ∘L g) = liftA f ∘L liftA g
  /-- `liftB` preserves composition. -/
  liftB_comp : ∀ f g, liftB (f ∘L g) = liftB f ∘L liftB g
  /-- `liftA` preserves identity. -/
  liftA_one : liftA (1 : K_A →L[ℂ] K_A) = (1 : H_SA →L[ℂ] H_SA)
  /-- `liftB` preserves identity. -/
  liftB_one : liftB (1 : K_B →L[ℂ] K_B) = (1 : H_SA →L[ℂ] H_SA)
  /-- `liftA` preserves addition. -/
  liftA_add : ∀ f g, liftA (f + g) = liftA f + liftA g
  /-- `liftB` preserves addition. -/
  liftB_add : ∀ f g, liftB (f + g) = liftB f + liftB g
  /-- `liftA` preserves zero. -/
  liftA_zero : liftA 0 = 0
  /-- `liftB` preserves zero. -/
  liftB_zero : liftB 0 = 0
  /-- `liftA` preserves the inner-product self-adjointness predicate. -/
  liftA_selfAdjoint : ∀ (f : K_A →L[ℂ] K_A),
    (∀ x y : K_A, inner ℂ (f x) y = inner ℂ x (f y)) →
    (∀ x y : H_SA, inner ℂ (liftA f x) y = inner ℂ x (liftA f y))
  /-- `liftB` preserves the inner-product self-adjointness predicate. -/
  liftB_selfAdjoint : ∀ (f : K_B →L[ℂ] K_B),
    (∀ x y : K_B, inner ℂ (f x) y = inner ℂ x (f y)) →
    (∀ x y : H_SA, inner ℂ (liftB f x) y = inner ℂ x (liftB f y))
  /-- A-side and B-side lifts commute (tensor-factor independence). -/
  liftA_liftB_commute : ∀ f g, liftA f ∘L liftB g = liftB g ∘L liftA f

/-! ### Pointwise commutation lemma -/

/-- Pointwise consequence of `liftA_liftB_commute`. -/
lemma TensorEmbedding.liftA_liftB_commute_apply
    (T : TensorEmbedding K_A K_B H_SA)
    (f : K_A →L[ℂ] K_A) (g : K_B →L[ℂ] K_B) (y : H_SA) :
    T.liftB g (T.liftA f y) = T.liftA f (T.liftB g y) := by
  have h := T.liftA_liftB_commute f g
  -- h : T.liftA f ∘L T.liftB g = T.liftB g ∘L T.liftA f
  -- Apply at y; both sides unfold via composition.
  have hPoint := DFunLike.congr_fun h y
  -- hPoint : (T.liftA f ∘L T.liftB g) y = (T.liftB g ∘L T.liftA f) y
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hPoint
  exact hPoint.symm

/-! ### ProjectorAlgebra constructor -/

/-- ProjectorAlgebra from a TensorEmbedding. The pointer-sector projector
    `M_{st}` is `T.liftA (S.ptrA.proj s) ∘L T.liftB (S.ptrB.proj t)`,
    encoding `I_AB ⊗ Q^A_s ⊗ Q^B_t` under the implicit tensor
    identification of `H_SA`. The four projection-algebra fields are
    derived as theorems from the corresponding `BinaryPointerProjectors`
    fields plus the tensor-embedding algebraic laws. -/
def ProjectorAlgebra.ofTensorEmbedding
    {S : SystemApparatusSetup K_A K_B H_SA}
    (T : TensorEmbedding K_A K_B H_SA) : ProjectorAlgebra S where
  lift s t := T.liftA (S.ptrA.proj s) ∘L T.liftB (S.ptrB.proj t)
  selfAdjoint s t := by
    intro x y
    -- ⟨liftA Qs (liftB Qt x), y⟩
    -- = ⟨liftB Qt x, liftA Qs y⟩          [liftA selfAdjoint]
    -- = ⟨x, liftB Qt (liftA Qs y)⟩        [liftB selfAdjoint]
    -- = ⟨x, liftA Qs (liftB Qt y)⟩        [commute]
    show inner ℂ (T.liftA (S.ptrA.proj s) (T.liftB (S.ptrB.proj t) x)) y
       = inner ℂ x (T.liftA (S.ptrA.proj s) (T.liftB (S.ptrB.proj t) y))
    rw [T.liftA_selfAdjoint _ (S.ptrA.selfAdjoint s)]
    rw [T.liftB_selfAdjoint _ (S.ptrB.selfAdjoint t)]
    rw [T.liftA_liftB_commute_apply (S.ptrA.proj s) (S.ptrB.proj t) y]
  idem s t := by
    -- (liftA Qs ∘L liftB Qt) ∘L (liftA Qs ∘L liftB Qt)
    -- = liftA Qs ∘L (liftB Qt ∘L liftA Qs) ∘L liftB Qt       [assoc]
    -- = liftA Qs ∘L (liftA Qs ∘L liftB Qt) ∘L liftB Qt       [commute]
    -- = (liftA Qs ∘L liftA Qs) ∘L (liftB Qt ∘L liftB Qt)     [assoc]
    -- = liftA (Qs ∘L Qs) ∘L liftB (Qt ∘L Qt)                 [liftA_comp, liftB_comp]
    -- = liftA Qs ∘L liftB Qt                                 [BPP.idem]
    rw [ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc (T.liftB (S.ptrB.proj t)),
        ← T.liftA_liftB_commute,
        ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc (T.liftA (S.ptrA.proj s)),
        ← T.liftA_comp, ← T.liftB_comp,
        S.ptrA.idem s, S.ptrB.idem t]
  orthogonal s t s' t' h := by
    -- (liftA Qs ∘L liftB Qt) ∘L (liftA Qs' ∘L liftB Qt')
    -- = liftA Qs ∘L (liftB Qt ∘L liftA Qs') ∘L liftB Qt'      [assoc]
    -- = liftA Qs ∘L (liftA Qs' ∘L liftB Qt) ∘L liftB Qt'      [commute]
    -- = (liftA Qs ∘L liftA Qs') ∘L (liftB Qt ∘L liftB Qt')    [assoc]
    -- = liftA (Qs ∘L Qs') ∘L liftB (Qt ∘L Qt')                [liftA_comp, liftB_comp]
    -- if s ≠ s' or t ≠ t', one of the inner products is 0,
    -- so the whole product is 0 (via liftA_zero or liftB_zero + comp_zero).
    rw [ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc (T.liftB (S.ptrB.proj t)),
        ← T.liftA_liftB_commute,
        ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc (T.liftA (S.ptrA.proj s)),
        ← T.liftA_comp, ← T.liftB_comp]
    -- Goal: liftA (Qs ∘L Qs') ∘L liftB (Qt ∘L Qt') = 0
    rcases ne_or_eq s s' with hs | hs
    · -- s ≠ s'. Then Qs ∘L Qs' = 0 by orthogonality (BPP.orthogonal or orthogonal_rev)
      have hQA : S.ptrA.proj s ∘L S.ptrA.proj s' = 0 := by
        rcases s with - | -
        · rcases s' with - | -
          · exact absurd rfl hs
          · exact S.ptrA.orthogonal
        · rcases s' with - | -
          · exact S.ptrA.orthogonal_rev
          · exact absurd rfl hs
      rw [hQA, T.liftA_zero, ContinuousLinearMap.zero_comp]
    · -- s = s'. Since (s, t) ≠ (s', t'), we must have t ≠ t'.
      subst hs
      have ht : t ≠ t' := fun e => h (by rw [e])
      have hQB : S.ptrB.proj t ∘L S.ptrB.proj t' = 0 := by
        rcases t with - | -
        · rcases t' with - | -
          · exact absurd rfl ht
          · exact S.ptrB.orthogonal
        · rcases t' with - | -
          · exact S.ptrB.orthogonal_rev
          · exact absurd rfl ht
      rw [hQB, T.liftB_zero, ContinuousLinearMap.comp_zero]
  complete := by
    -- ∑ st : Sign × Sign, liftA Q^A_st.1 ∘L liftB Q^B_st.2
    -- Expand the sum as a 4-term sum over Sign × Sign
    rw [Fintype.sum_prod_type]
    -- Goal: ∑ s : Sign, ∑ t : Sign, liftA Qs ∘L liftB Qt = 1
    simp only [Sign.sum_univ]
    -- Goal: 4-term sum equals 1.
    -- LHS = liftA Q+ ∘L (liftB Q+ + liftB Q-) + liftA Q- ∘L (liftB Q+ + liftB Q-)
    --     = (liftA Q+ + liftA Q-) ∘L (liftB Q+ + liftB Q-)
    --     = liftA (Q+ + Q-) ∘L liftB (Q+ + Q-)
    --     = liftA 1 ∘L liftB 1
    --     = 1 ∘L 1 = 1
    rw [← ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_add,
        ← ContinuousLinearMap.add_comp,
        ← T.liftA_add, ← T.liftB_add,
        S.ptrA.complete, S.ptrB.complete,
        T.liftA_one, T.liftB_one]
    -- Goal: (1 : H_SA →L[ℂ] H_SA) ∘L 1 = 1
    exact one_mul _

/-! ### UnitaryTensorEmbedding and the MeasurementUnitary factorisation

The same bipartite tensor-factor structure of `H_SA`, in its unitary form:
per-wing unitaries `vA : K_A ≃ₗᵢ[ℂ] K_A` and `vB : K_B ≃ₗᵢ[ℂ] K_B` lift to
`H_SA ≃ₗᵢ[ℂ] H_SA` through unitary-preserving extensions of the
TensorEmbedding's algebra-homomorphism lifts.

Used to derive `MeasurementUnitary.factorises` (`u x = uA (uB x)`) from
the definition `u := uB.trans uA`. The eigenstate-action field
(`action`) remains data per spec §9.5 carve-out (operator-exponential
machinery).

The commutation condition `liftA_unitary vA` and `liftB_unitary vB`
commute is the unitary analogue of `TensorEmbedding.liftA_liftB_commute`:
tensor-factor independence at the unitary level. It is physically
required (per-wing unitaries act on independent Hilbert factors and
therefore commute) and is included for fidelity, even though
`MeasurementUnitary.factorises` itself does not consume it.

A `UnitaryTensorEmbedding` is intentionally a standalone structure rather
than an extension of `TensorEmbedding`: callers needing only the operator
algebra-hom (e.g. the `ProjectorAlgebra` derivation above) should not be
required to supply unitary lifts as well. Future work that needs a
single coherent abstraction (with `(liftA_unitary v).toContinuousLinearMap
= liftA v.toContinuousLinearMap` as a coherence field) can combine the
two; the current split keeps preconditions minimal.
-/

/-- Unitary bipartite tensor-factor structure on `H_SA`. Per-wing
    unitaries lift to `H_SA`-unitaries; A-wing and B-wing lifts commute. -/
structure UnitaryTensorEmbedding (K_A K_B H_SA : Type*)
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    where
  /-- Lift of A-wing unitary. -/
  liftA_unitary : (K_A ≃ₗᵢ[ℂ] K_A) → (H_SA ≃ₗᵢ[ℂ] H_SA)
  /-- Lift of B-wing unitary. -/
  liftB_unitary : (K_B ≃ₗᵢ[ℂ] K_B) → (H_SA ≃ₗᵢ[ℂ] H_SA)
  /-- A-wing and B-wing unitary lifts commute (tensor-factor independence at
      the unitary level; physically required because per-wing unitaries act
      on independent Hilbert factors). -/
  liftA_liftB_unitary_commute : ∀ (vA : K_A ≃ₗᵢ[ℂ] K_A) (vB : K_B ≃ₗᵢ[ℂ] K_B),
    (liftA_unitary vA).trans (liftB_unitary vB)
      = (liftB_unitary vB).trans (liftA_unitary vA)

/-- MeasurementUnitary from a UnitaryTensorEmbedding plus per-wing
    unitaries plus the joint-eigenstate / pointer-translation data.

    The full unitary is defined as `u := (liftB_unitary vB).trans
    (liftA_unitary vA)`. The `factorises` field then follows by definition
    of `LinearIsometryEquiv.trans`, discharged here as `rfl` (no separate
    proof needed). The `action` field remains caller-supplied per spec
    §9.5: it encodes the impulsive-readout idealisation and requires
    operator-exponential / Stone machinery, which is LF4-or-later. -/
def MeasurementUnitary.ofUnitaryTensorEmbedding
    {S : SystemApparatusSetup K_A K_B H_SA}
    (T : UnitaryTensorEmbedding K_A K_B H_SA)
    (vA : K_A ≃ₗᵢ[ℂ] K_A) (vB : K_B ≃ₗᵢ[ℂ] K_B)
    (jointEig : Sign × Sign → K_A → K_B → H_SA)
    (ptrTransA : Sign → K_A → K_A)
    (ptrTransB : Sign → K_B → K_B)
    (action : ∀ s t φA φB,
       T.liftA_unitary vA (T.liftB_unitary vB (jointEig (s, t) φA φB))
         = jointEig (s, t) (ptrTransA s φA) (ptrTransB t φB)) :
    MeasurementUnitary S where
  u := (T.liftB_unitary vB).trans (T.liftA_unitary vA)
  uA := T.liftA_unitary vA
  uB := T.liftB_unitary vB
  factorises := fun _ => rfl
  jointEig := jointEig
  ptrTransA := ptrTransA
  ptrTransB := ptrTransB
  action := action

end LF3
end CSD
