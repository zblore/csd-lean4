/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.SectorSeparation

/-!
# LF3 Projectors / Core: abstract pointer-sector projective algebra

**Category:** 3-Local (LF3 abstract four-projector pointer-sector algebra, v1.00 data form).

Paper §5 / §9.7.

The `ProjectorAlgebra` structure carries the four projective-decomposition
axioms (self-adjoint, idempotent, mutually orthogonal, summing to the
identity) for the four pointer-sector projectors `M_{st}` indexed by
`(s, t) : Sign × Sign`. Per spec §9.7 these are taken as data in v1.00,
deferring the derivation from a concrete tensor product to a future v2.

Self-adjointness is stated via the inner-product equation directly (matching
the convention in `BinaryPointerProjectors` and `TensorFactorReadoutAlgebra`,
avoiding `Star` typeclass synthesis on `H_SA →L[ℂ] H_SA`).
-/

@[expose] public section

open scoped BigOperators

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]

/-- Axiomatised projective decomposition of `H_SA` into pointer sectors
    `(s, t) : Sign × Sign`. Each `lift s t` is the operator
    `I_AB ⊗ Q^A_s ⊗ Q^B_t` lifted to `H_SA` through the abstract tensor-factor
    structure.

    **D4 / G6 disclosure.** In v1.00 this is taken as data (spec §9.7): the
    four projection identities (`selfAdjoint`, `idem`, `orthogonal`,
    `complete`) are fields rather than theorems. The composite tensor
    structure debt (D4 / G6 in the corpus) is the gap between this abstract
    `ProjectorAlgebra` and a derived construction.

    **v2 derivation landed.** `CsdLean4/LF3/Projectors/TensorModel.lean`
    introduces a `TensorEmbedding K_A K_B H_SA` structure encoding the
    bipartite tensor-factor structure of `H_SA` through unital algebra-
    homomorphism lift functions `liftA`, `liftB` with commuting images,
    and supplies `ProjectorAlgebra.ofTensorEmbedding : TensorEmbedding K_A
    K_B H_SA → ProjectorAlgebra S` whose four output fields are theorems
    rather than data. The abstract `ProjectorAlgebra` remains available
    for callers without a tensor embedding; the constructor builds one
    from the embedding plus the `SystemApparatusSetup`'s per-wing
    `BinaryPointerProjectors`. The ProjectorAlgebra half of D4 / G6 is
    therefore discharged at the Lean level. -/
structure ProjectorAlgebra (S : SystemApparatusSetup K_A K_B H_SA) where
  /-- The four pointer-sector projectors, indexed by `(s, t) : Sign × Sign`. -/
  lift          : Sign → Sign → H_SA →L[ℂ] H_SA
  /-- Each projector is self-adjoint with respect to the inner product. -/
  selfAdjoint   : ∀ s t x y, inner ℂ (lift s t x) y = inner ℂ x (lift s t y)
  /-- Each projector is idempotent. -/
  idem          : ∀ s t, lift s t ∘L lift s t = lift s t
  /-- The four projectors are pairwise orthogonal. -/
  orthogonal    : ∀ s t s' t', (s, t) ≠ (s', t') → lift s t ∘L lift s' t' = 0
  /-- The four projectors sum to the identity. -/
  complete      : ∑ st : Sign × Sign, lift st.1 st.2 = (1 : H_SA →L[ℂ] H_SA)

/-- Pointer-sector projector `M_{st} = I_AB ⊗ Q^A_s ⊗ Q^B_t`, lifted to
    `H_SA` via the abstract `ProjectorAlgebra` data. -/
noncomputable def mHat
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    (s t : Sign) : H_SA →L[ℂ] H_SA :=
  P.lift s t

/-! ### Theorem targets (spec §5.14 / §9.7) -/

/-- The pointer-sector projector is idempotent (paper §5.14). Field re-export. -/
theorem mHat_idem
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    (s t : Sign) :
    mHat P s t ∘L mHat P s t = mHat P s t :=
  P.idem s t

/-- The pointer-sector projector is self-adjoint (paper §5.14). Field re-export. -/
theorem mHat_isSelfAdjoint
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    (s t : Sign) :
    ∀ x y, inner ℂ (mHat P s t x) y = inner ℂ x (mHat P s t y) :=
  P.selfAdjoint s t

/-- Distinct pointer-sector projectors are orthogonal (paper §5.14). Field
    re-export. -/
theorem mHat_orthogonal
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    {s t s' t' : Sign} (h : (s, t) ≠ (s', t')) :
    mHat P s t ∘L mHat P s' t' = 0 :=
  P.orthogonal s t s' t' h

/-- The four pointer-sector projectors sum to the identity (paper §5.14). Field
    re-export. -/
theorem mHat_complete
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S) :
    ∑ st : Sign × Sign, mHat P st.1 st.2 = (1 : H_SA →L[ℂ] H_SA) :=
  P.complete

end LF3
end CSD
