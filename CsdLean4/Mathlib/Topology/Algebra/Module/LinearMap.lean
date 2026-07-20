import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Mathlib upstream candidates: `ContinuousLinearMap` complement lemmas

**Category:** 1-Mathlib (CSD-free helper lemmas staged as Mathlib upstream candidates).

Generalised forms of helper lemmas currently used in CSD-specific modules.
Each lemma here is stated in maximum-general Mathlib idiom: no CSD-specific
structure, Mathlib snake_case names, minimal imports.

Declarations live in their natural Mathlib symbol namespace (here:
`ContinuousLinearMap`), so dot notation is preserved and upstreaming
requires no symbol rename — only a file move to (or append onto)
`Mathlib/Topology/Algebra/Module/LinearMap.lean`.

If Mathlib already contains an equivalent lemma, the local helper here can
be replaced by the Mathlib citation. Provenance notes are inline so a
future upstreaming PR can write itself.

## Candidates in this file

- `ContinuousLinearMap.comp_complement_of_idem`: complement of an idempotent
  endomorphism composes to zero on the right. Generalises
  `BinaryPointerProjectors.orthogonal_rev` from
  `LF3/Projectors/TensorModel.lean`.
- `ContinuousLinearMap.complement_comp_of_idem`: symmetric companion,
  composition on the left.
-/

namespace ContinuousLinearMap

variable {𝕜 : Type*} [Ring 𝕜]
variable {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

/-- For continuous linear endomorphisms `P Q : M →L[𝕜] M`: if `Q` is
idempotent (`Q ∘L Q = Q`) and `P + Q = 1`, then `Q ∘L P = 0`.

Proof: `Q ∘L P = Q ∘L (1 - Q) = Q ∘L 1 - Q ∘L Q = Q - Q = 0`.

**Provenance.** Originally `BinaryPointerProjectors.orthogonal_rev` in
`CsdLean4/LF3/Projectors/TensorModel.lean`, where it gives the reverse
direction of pointer-projector orthogonality from completeness plus
idempotence. The generalised form here depends on no CSD-specific
structure. -/
theorem comp_complement_of_idem
    (P Q : M →L[𝕜] M) (hQ_idem : Q ∘L Q = Q) (h_complete : P + Q = 1) :
    Q ∘L P = 0 := by
  have hP : P = 1 - Q := eq_sub_of_add_eq h_complete
  rw [hP, ContinuousLinearMap.comp_sub,
      show ((1 : M →L[𝕜] M)) = ContinuousLinearMap.id 𝕜 M from rfl,
      ContinuousLinearMap.comp_id, hQ_idem]
  exact sub_self _

/-- Symmetric companion: if `Q` is idempotent and `P + Q = 1`, then
`P ∘L Q = 0`.

This is the version where `P` is the complement and we compose on the
*left* with `Q`. The proof mirrors `comp_complement_of_idem`. -/
theorem complement_comp_of_idem
    (P Q : M →L[𝕜] M) (hQ_idem : Q ∘L Q = Q) (h_complete : P + Q = 1) :
    P ∘L Q = 0 := by
  have hP : P = 1 - Q := eq_sub_of_add_eq h_complete
  rw [hP, ContinuousLinearMap.sub_comp,
      show ((1 : M →L[𝕜] M)) = ContinuousLinearMap.id 𝕜 M from rfl,
      ContinuousLinearMap.id_comp, hQ_idem]
  exact sub_self _

end ContinuousLinearMap
