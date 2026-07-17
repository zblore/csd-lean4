import CsdLean4.FND.TensorSolved
import CsdLean4.FND.CompositeInterface
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# FND/TensorReconstruction: locality + generation FORCE the tensor product (P3, the uniqueness half)

**Category:** 7-FND (the Choice A ontology layer).

`FND/TensorSolved.lean` proves SUFFICIENCY — the standard Kronecker composite satisfies locality and
local tomography. This module proves the converse, NECESSITY / uniqueness: **any composite algebra `𝒜`
carrying commuting local matrix algebras that GENERATE it must BE the tensor product** — there is no other
composite. That is the real "why `⊗`" reconstruction, and its dimension corollary discharges bridge B6
(`CompositeSector.tensor_dimension`, `NA · NB = Njoint`) as a THEOREM rather than a posit.

## The theorem

Given unital ℂ-algebra embeddings `ιA : M_m → 𝒜`, `ιB : M_n → 𝒜` with COMMUTING images that GENERATE
`𝒜` (`Algebra.adjoin ℂ (range ιA ∪ range ιB) = ⊤`), the lifted map

  `Φ = Algebra.TensorProduct.lift ιA ιB : M_m ⊗[ℂ] M_n → 𝒜`,   `A ⊗ B ↦ ιA A · ιB B`

is an ALGEBRA EQUIVALENCE (`compositeAlgReconstruction`). The mechanism is exactly the operational
argument: `M_m ⊗ M_n` is a SIMPLE ring (Artin–Wedderburn: it is `≃ M_{mn}`), so the unital `Φ` is
INJECTIVE (a ring hom out of a simple ring is injective); GENERATION makes it SURJECTIVE; hence bijective.

## The dimension corollary (discharging B6)

For a composite represented by `M_k(ℂ)`, `finrank` across the equivalence forces `k² = (mn)²`, i.e.
`k = mn` (`composite_dim_eq`). So the tensor-product dimension `NA · NB` is not a postulate but a
consequence of locality + generation — the reconstruction the sector interface (`CompositeInterface`,
`TensorSector`) previously took as the bridge-B6 field.

References: `specs/future-work.md` (P3 / FND-P3r, bridge B6); `FND/TensorSolved.lean`
(`composite_is_tensor_product`, the sufficiency half — the tensor model realizes the principles);
`FND/TensorGeneration.lean` (`joint_mem_span_local`, the quantum generation fact);
`FND/CompositeInterface.lean` (`CompositeSector.tensor_dimension`, the field this discharges).
-/

open scoped TensorProduct
open Matrix

namespace CSD.FND

/-! ### `M_m ⊗ M_n` is a simple ring -/

/-- **`M_m(ℂ) ⊗ M_n(ℂ)` is simple.** Transport `IsSimpleRing` along the Kronecker algebra equivalence
`M_m ⊗ M_n ≃ₐ M_{m×n}(ℂ ⊗ ℂ)` from the matrix ring over the simple `ℂ ⊗ ℂ`. This is the Artin–Wedderburn
fact that makes any unital map out of `M_m ⊗ M_n` injective. -/
instance matrixTensor_isSimpleRing (m n : ℕ) [NeZero m] [NeZero n] :
    IsSimpleRing (Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  -- ℂ ⊗[ℂ] ℂ is simple (≃ ℂ)
  haveI hcc : IsSimpleRing (ℂ ⊗[ℂ] ℂ) :=
    IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.lid ℂ ℂ).symm.toRingEquiv inferInstance
  -- M_{m×n}(ℂ⊗ℂ) is simple
  haveI hmat : IsSimpleRing (Matrix (Fin m × Fin n) (Fin m × Fin n) (ℂ ⊗[ℂ] ℂ)) :=
    IsSimpleRing.matrix (Fin m × Fin n) (ℂ ⊗[ℂ] ℂ)
  -- transport back along the Kronecker AlgEquiv
  exact IsSimpleRing.of_ringEquiv
    (Matrix.kroneckerTMulAlgEquiv (R := ℂ) (S := ℂ) (A := ℂ) (B := ℂ)
      (m := Fin m) (n := Fin n)).symm.toRingEquiv hmat

/-! ### The reconstruction -/

variable {m n : ℕ} {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

/-- **The reconstruction map** `Φ : M_m ⊗ M_n → 𝒜`, `A ⊗ B ↦ ιA A · ιB B`, from commuting local
embeddings. `Algebra.TensorProduct.lift` of the two algebra homs with commuting images. -/
noncomputable def reconMap
    (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] 𝒜) (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] 𝒜)
    (hc : ∀ A B, Commute (ιA A) (ιB B)) :
    Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] 𝒜 :=
  Algebra.TensorProduct.lift ιA ιB hc

@[simp] theorem reconMap_tmul
    (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] 𝒜) (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] 𝒜)
    (hc : ∀ A B, Commute (ιA A) (ιB B)) (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    reconMap ιA ιB hc (A ⊗ₜ[ℂ] B) = ιA A * ιB B :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- **THE RECONSTRUCTION — locality + generation force `⊗`.** With commuting local embeddings whose
images GENERATE `𝒜`, the reconstruction map `Φ` is an ALGEBRA EQUIVALENCE `M_m ⊗ M_n ≃ₐ 𝒜`: injective
because `M_m ⊗ M_n` is simple (so the unital `Φ` has trivial kernel), surjective because the images
generate. So the composite `𝒜` IS the tensor product — not chosen, forced. -/
noncomputable def compositeAlgReconstruction [NeZero m] [NeZero n] [Nontrivial 𝒜]
    (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] 𝒜) (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] 𝒜)
    (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hgen : Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤) :
    Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] 𝒜 := by
  refine AlgEquiv.ofBijective (reconMap ιA ιB hc) ⟨?_, ?_⟩
  · -- injective: ring hom out of a simple ring
    exact (reconMap ιA ιB hc).toRingHom.injective
  · -- surjective: the range contains both local images, hence the adjoin = ⊤
    rw [← AlgHom.range_eq_top]
    refine top_le_iff.mp ?_
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro x (⟨A, rfl⟩ | ⟨B, rfl⟩)
    · exact ⟨A ⊗ₜ[ℂ] 1, by simp [reconMap_tmul]⟩
    · exact ⟨1 ⊗ₜ[ℂ] B, by simp [reconMap_tmul]⟩

/-! ### The dimension corollary — discharging bridge B6 -/

/-- **The composite dimension is forced: `k = m · n`.** If a composite represented by `M_k(ℂ)` carries
commuting, generating local algebras `M_m, M_n`, then `k = m · n`. The reconstruction gives an algebra
(hence linear) equivalence `M_m ⊗ M_n ≃ M_k`, so `finrank` gives `(m·n)² = k²`, whence `k = m·n`. This
discharges bridge B6 (`CompositeSector.tensor_dimension`) as a theorem. -/
theorem composite_dim_eq {m n k : ℕ} [NeZero m] [NeZero n] [NeZero k]
    (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hgen : Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤) :
    k = m * n := by
  have e := compositeAlgReconstruction ιA ιB hc hgen
  have hfin := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, Module.finrank_matrix, Module.finrank_matrix,
    Module.finrank_matrix] at hfin
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hfin
  -- hfin : (m * m) * (n * n) = k * k
  have hsq : k * k = (m * n) * (m * n) := by rw [← hfin]; ring
  exact Nat.mul_self_inj.mp hsq

/-! ### Discharging bridge B6 in the sector interface

`CompositeSector.tensor_dimension` (`FND/CompositeInterface.lean`) is the `NA · NB = Njoint` FIELD that
posited B6. The smart constructor below builds a `CompositeSector` in which that field is DERIVED from the
reconstruction — the caller supplies the joint sector plus commuting, generating local observable
embeddings, and `composite_dim_eq` PROVES the dimension. So B6 need no longer be assumed: any composite
whose local algebras are commuting and generating gets its tensor dimension for free. -/

/-- **A composite sector with the tensor dimension DERIVED, not posited (B6 discharged).** Given the joint
`ChoiceASector` on `M_k` and commuting, generating local observable embeddings `M_NA, M_NB ↪ M_k`, this
constructs the `CompositeSector` whose `tensor_dimension : NA * NB = k` field is filled by
`composite_dim_eq` rather than taken on faith. -/
noncomputable def CompositeSector.ofReconstruction {NA NB k : ℕ} [NeZero NA] [NeZero NB] [NeZero k]
    {Sigma : Type*} [MeasurableSpace Sigma] {D : ConstraintDynamics Sigma}
    (jointSector : ChoiceASector k D)
    (ιA : Matrix (Fin NA) (Fin NA) ℂ →ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (ιB : Matrix (Fin NB) (Fin NB) ℂ →ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hgen : Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤) :
    CompositeSector NA NB k D where
  jointSector := jointSector
  tensor_dimension := (composite_dim_eq ιA ιB hc hgen).symm

end CSD.FND
