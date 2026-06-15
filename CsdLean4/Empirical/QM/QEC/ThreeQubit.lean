import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Empirical/QM: the three-qubit bit-flip code (the first QEC theorem)

**Category:** 3-Local. QM-validity layer (matrix / inner-product geometry, no CSD
ontology). The smallest genuine quantum error-correcting code, and the QEC analogue of
`no_cloning_two_state`: a concrete, self-contained first error-correction theorem.

## The code

A logical qubit `a|0⟩ + b|1⟩` is encoded as `a|000⟩ + b|111⟩` on three physical qubits
(`encode`). The code corrects any single bit-flip (`X`) error:

- **Stabilisers** `Z₁Z₂ = Z⊗Z⊗I` and `Z₂Z₃ = I⊗Z⊗Z` fix the codespace
  (`stab_Z1Z2_fixes_logical`, `stab_Z2Z3_fixes_logical`).
- **Errors** `{I, X₁, X₂, X₃}` each commute or anticommute with the stabilisers in a
  distinct pattern, so the errored state `E·ψ_L` is a simultaneous stabiliser eigenstate
  with eigenvalues = the **syndrome** of `E`, and the four syndromes are **distinct**
  (`syndrome_*`). Measuring `(Z₁Z₂, Z₂Z₃)` therefore identifies which bit flipped.
- **Recovery**: each `X` is self-inverse, so re-applying the identified `X` restores the
  logical state (`bitflip_corrects`).

The proofs are pure 2×2-Pauli algebra lifted through the Kronecker mixed-product
`(A⊗B)(C⊗D) = (AC)⊗(BD)`; the single-qubit anticommutation `ZX = −XZ` drives every
syndrome sign.

## Source

Shor 1995 (the 9-qubit code, of which this is the bit-flip half); the 3-qubit repetition
code is the standard pedagogical entry to stabiliser QEC (Nielsen-Chuang §10.1).
-/

open Matrix
open scoped Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-- The 3-qubit Hilbert space, `ℂ⁸` indexed by the computational basis. -/
abbrev H3 := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-! ### Single-qubit Paulis and their algebra -/

/-- The Pauli `X` (bit flip). -/
def pX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- The Pauli `Z` (phase flip). -/
def pZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

@[simp] lemma pX_mul_pX : pX * pX = 1 := by
  simp [pX, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

@[simp] lemma pZ_mul_pZ : pZ * pZ = 1 := by
  simp [pZ, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-- The single-qubit anticommutation `ZX = −XZ` — the engine of every syndrome sign. -/
lemma pZ_mul_pX : pZ * pX = - (pX * pZ) := by
  simp only [pX, pZ, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### The three-qubit operators (Kronecker lifts) -/

/-- `M ⊗ N ⊗ P` on the right-associated `Fin 2 × Fin 2 × Fin 2` index. -/
def kron3 (M N P : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  M ⊗ₖ (N ⊗ₖ P)

/-- `X₁ = X ⊗ I ⊗ I`. -/
def X1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 pX 1 1
/-- `X₂ = I ⊗ X ⊗ I`. -/
def X2 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 pX 1
/-- `X₃ = I ⊗ I ⊗ X`. -/
def X3 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 1 pX
/-- The stabiliser `Z₁Z₂ = Z ⊗ Z ⊗ I`. -/
def Z1Z2 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 pZ pZ 1
/-- The stabiliser `Z₂Z₃ = I ⊗ Z ⊗ Z`. -/
def Z2Z3 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 pZ pZ

/-- Kronecker mixed product on `kron3`: `(M⊗N⊗P)(M'⊗N'⊗P') = (MM')⊗(NN')⊗(PP')`. -/
lemma kron3_mul (M N P M' N' P' : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 M N P * kron3 M' N' P' = kron3 (M * M') (N * N') (P * P') := by
  simp only [kron3, ← Matrix.mul_kronecker_mul]

/-! ### Self-inverse and the stabiliser commutations -/

@[simp] lemma X1_mul_X1 : X1 * X1 = 1 := by
  rw [X1, kron3_mul, pX_mul_pX]; simp only [mul_one, kron3, Matrix.one_kronecker_one]

@[simp] lemma X2_mul_X2 : X2 * X2 = 1 := by
  rw [X2, kron3_mul, pX_mul_pX]; simp only [mul_one, one_mul, kron3, Matrix.one_kronecker_one]

@[simp] lemma X3_mul_X3 : X3 * X3 = 1 := by
  rw [X3, kron3_mul, pX_mul_pX]; simp only [one_mul, kron3, Matrix.one_kronecker_one]

lemma kron3_neg_left (M N P : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 (-M) N P = - kron3 M N P := by
  rw [kron3, kron3, ← neg_one_smul ℂ M, Matrix.smul_kronecker, neg_one_smul]

lemma kron3_neg_mid (M N P : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 M (-N) P = - kron3 M N P := by
  rw [kron3, kron3, ← neg_one_smul ℂ N, Matrix.smul_kronecker, Matrix.kronecker_smul,
    neg_one_smul]

lemma kron3_neg_right (M N P : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 M N (-P) = - kron3 M N P := by
  rw [kron3, kron3, ← neg_one_smul ℂ P, Matrix.kronecker_smul, Matrix.kronecker_smul,
    neg_one_smul]

/-- `Z₁Z₂` anticommutes with `X₁`. -/
lemma Z1Z2_anticomm_X1 : Z1Z2 * X1 = - (X1 * Z1Z2) := by
  rw [Z1Z2, X1, kron3_mul, kron3_mul, pZ_mul_pX, kron3_neg_left]; simp [mul_one, one_mul]

/-- `Z₁Z₂` anticommutes with `X₂`. -/
lemma Z1Z2_anticomm_X2 : Z1Z2 * X2 = - (X2 * Z1Z2) := by
  rw [Z1Z2, X2, kron3_mul, kron3_mul, pZ_mul_pX, kron3_neg_mid]; simp [mul_one, one_mul]

/-- `Z₁Z₂` commutes with `X₃`. -/
lemma Z1Z2_comm_X3 : Z1Z2 * X3 = X3 * Z1Z2 := by
  rw [Z1Z2, X3, kron3_mul, kron3_mul]; simp [mul_one, one_mul]

/-- `Z₂Z₃` commutes with `X₁`. -/
lemma Z2Z3_comm_X1 : Z2Z3 * X1 = X1 * Z2Z3 := by
  rw [Z2Z3, X1, kron3_mul, kron3_mul]; simp [mul_one, one_mul]

/-- `Z₂Z₃` anticommutes with `X₂`. -/
lemma Z2Z3_anticomm_X2 : Z2Z3 * X2 = - (X2 * Z2Z3) := by
  rw [Z2Z3, X2, kron3_mul, kron3_mul, pZ_mul_pX, kron3_neg_mid]; simp [mul_one, one_mul]

/-- `Z₂Z₃` anticommutes with `X₃`. -/
lemma Z2Z3_anticomm_X3 : Z2Z3 * X3 = - (X3 * Z2Z3) := by
  rw [Z2Z3, X3, kron3_mul, kron3_mul, pZ_mul_pX, kron3_neg_right]; simp [mul_one, one_mul]

/-! ### The encoded (logical) state and the stabiliser fixing -/

/-- The logical state `a|000⟩ + b|111⟩` — the image of `a|0⟩ + b|1⟩` under the encoder. -/
noncomputable def logical (a b : ℂ) : H3 :=
  EuclideanSpace.single ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2) a
    + EuclideanSpace.single ((1, 1, 1) : Fin 2 × Fin 2 × Fin 2) b

/-- `Z₁Z₂` fixes the codespace: `Z₁Z₂ · ψ_L = ψ_L`. -/
lemma stab_Z1Z2_fixes_logical (a b : ℂ) :
    Matrix.toEuclideanLin Z1Z2 (logical a b) = logical a b := by
  ext i
  simp only [Matrix.toEuclideanLin_apply, logical, Z1Z2, kron3, pZ]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fin.prod_univ_two, Prod.ext_iff]

/-- `Z₂Z₃` fixes the codespace: `Z₂Z₃ · ψ_L = ψ_L`. -/
lemma stab_Z2Z3_fixes_logical (a b : ℂ) :
    Matrix.toEuclideanLin Z2Z3 (logical a b) = logical a b := by
  ext i
  simp only [Matrix.toEuclideanLin_apply, logical, Z2Z3, kron3, pZ]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fin.prod_univ_two, Prod.ext_iff]

/-! ### Syndromes, recovery, and the correction theorem -/

lemma tel_mul (M N : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (v : H3) :
    Matrix.toEuclideanLin (M * N) v
      = Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) := by
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

lemma tel_one (v : H3) : Matrix.toEuclideanLin 1 v = v := by
  simp [Matrix.toEuclideanLin_apply]

lemma tel_neg (M : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (v : H3) :
    Matrix.toEuclideanLin (-M) v = - Matrix.toEuclideanLin M v := by
  rw [map_neg, LinearMap.neg_apply]

/-- The errored codeword carries the **syndrome** of the error: it is a simultaneous
eigenstate of the stabilisers `(Z₁Z₂, Z₂Z₃)` with the eigenvalue pattern that identifies
the error. `(I,X₁,X₂,X₃)` give the distinct syndromes `(+,+), (−,+), (−,−), (+,−)`. -/
lemma syndrome_X1 (a b : ℂ) :
    Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin X1 (logical a b))
        = - Matrix.toEuclideanLin X1 (logical a b)
    ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin X1 (logical a b))
        = Matrix.toEuclideanLin X1 (logical a b) := by
  refine ⟨?_, ?_⟩
  · rw [← tel_mul, Z1Z2_anticomm_X1, tel_neg, tel_mul, stab_Z1Z2_fixes_logical]
  · rw [← tel_mul, Z2Z3_comm_X1, tel_mul, stab_Z2Z3_fixes_logical]

lemma syndrome_X2 (a b : ℂ) :
    Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin X2 (logical a b))
        = - Matrix.toEuclideanLin X2 (logical a b)
    ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin X2 (logical a b))
        = - Matrix.toEuclideanLin X2 (logical a b) := by
  refine ⟨?_, ?_⟩
  · rw [← tel_mul, Z1Z2_anticomm_X2, tel_neg, tel_mul, stab_Z1Z2_fixes_logical]
  · rw [← tel_mul, Z2Z3_anticomm_X2, tel_neg, tel_mul, stab_Z2Z3_fixes_logical]

lemma syndrome_X3 (a b : ℂ) :
    Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin X3 (logical a b))
        = Matrix.toEuclideanLin X3 (logical a b)
    ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin X3 (logical a b))
        = - Matrix.toEuclideanLin X3 (logical a b) := by
  refine ⟨?_, ?_⟩
  · rw [← tel_mul, Z1Z2_comm_X3, tel_mul, stab_Z1Z2_fixes_logical]
  · rw [← tel_mul, Z2Z3_anticomm_X3, tel_neg, tel_mul, stab_Z2Z3_fixes_logical]

/-- **Recovery.** Each single bit-flip is self-inverse, so re-applying the identified
correction restores the logical state: `Xⱼ · (Xⱼ · ψ_L) = ψ_L`. -/
lemma bitflip_recovers (a b : ℂ) :
    Matrix.toEuclideanLin X1 (Matrix.toEuclideanLin X1 (logical a b)) = logical a b
    ∧ Matrix.toEuclideanLin X2 (Matrix.toEuclideanLin X2 (logical a b)) = logical a b
    ∧ Matrix.toEuclideanLin X3 (Matrix.toEuclideanLin X3 (logical a b)) = logical a b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← tel_mul, X1_mul_X1, tel_one]
  · rw [← tel_mul, X2_mul_X2, tel_one]
  · rw [← tel_mul, X3_mul_X3, tel_one]

/-! ### Identifiability: the four syndromes are pairwise distinct -/

/-- The **syndrome** of an error, as the eigenvalue sign-pair `(s₁, s₂) ∈ {±1}²` of the
stabilisers `(Z₁Z₂, Z₂Z₃)` on the errored codeword. Indexed by `Fin 4` for the error set
`{I, X₁, X₂, X₃}`. The values `I → (+,+)`, `X₁ → (−,+)`, `X₂ → (−,−)`, `X₃ → (+,−)` are read
off `stab_*_fixes_logical` / `syndrome_X*` (the eigenvalues live in `ℂ`, the scalar field of
the code space). -/
def errorSyndrome : Fin 4 → ℂ × ℂ
  | 0 => (1, 1)     -- I
  | 1 => (-1, 1)    -- X₁
  | 2 => (-1, -1)   -- X₂
  | 3 => (1, -1)    -- X₃

/-- **Identifiability (the load-bearing QEC ingredient): the four error syndromes are
pairwise distinct.** Equivalently `errorSyndrome` is injective on `{I, X₁, X₂, X₃}`. Since the
four `{±1}²` sign-pairs are literally distinct, measuring `(Z₁Z₂, Z₂Z₃)` pins down which of
the four errors occurred. This is the content that makes the stabiliser eigenvalues a usable
*syndrome* rather than merely an eigen-equation. -/
theorem three_qubit_syndromes_distinct : Function.Injective errorSyndrome := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; simp only [errorSyndrome, Prod.mk.injEq] at hij; norm_num at hij)

/-- **The four errored codewords are simultaneous stabiliser eigenstates carrying their
syndrome**, in eigen-equation form: `I` is fixed (`(+,+)`); `X₁, X₂, X₃` carry the eigenvalue
pairs `(−,+), (−,−), (+,−)`. This is the eigenstate content underlying `errorSyndrome`; it
repackages `stab_*_fixes_logical` and `syndrome_X*` so that `three_qubit_syndromes_distinct`
(distinctness of the `±1` pairs) is the identifiability statement. -/
theorem three_qubit_syndrome_eigenstates (a b : ℂ) :
    -- I : syndrome (+,+)
    (Matrix.toEuclideanLin Z1Z2 (logical a b) = (errorSyndrome 0).1 • logical a b
      ∧ Matrix.toEuclideanLin Z2Z3 (logical a b) = (errorSyndrome 0).2 • logical a b)
    -- X₁ : syndrome (−,+)
    ∧ (Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin X1 (logical a b))
        = (errorSyndrome 1).1 • Matrix.toEuclideanLin X1 (logical a b)
      ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin X1 (logical a b))
        = (errorSyndrome 1).2 • Matrix.toEuclideanLin X1 (logical a b))
    -- X₂ : syndrome (−,−)
    ∧ (Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin X2 (logical a b))
        = (errorSyndrome 2).1 • Matrix.toEuclideanLin X2 (logical a b)
      ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin X2 (logical a b))
        = (errorSyndrome 2).2 • Matrix.toEuclideanLin X2 (logical a b))
    -- X₃ : syndrome (+,−)
    ∧ (Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin X3 (logical a b))
        = (errorSyndrome 3).1 • Matrix.toEuclideanLin X3 (logical a b)
      ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin X3 (logical a b))
        = (errorSyndrome 3).2 • Matrix.toEuclideanLin X3 (logical a b)) := by
  simp only [errorSyndrome, one_smul, neg_one_smul]
  exact ⟨⟨stab_Z1Z2_fixes_logical a b, stab_Z2Z3_fixes_logical a b⟩,
    syndrome_X1 a b, syndrome_X2 a b, syndrome_X3 a b⟩

/-- The eigenvalue sign-pair carried by `three_qubit_syndrome_eigenstates` for error index
`k` agrees with `errorSyndrome k` (the `±1` entries are the stabiliser eigenvalues). -/
theorem errorSyndrome_eq :
    errorSyndrome 0 = (1, 1) ∧ errorSyndrome 1 = (-1, 1)
      ∧ errorSyndrome 2 = (-1, -1) ∧ errorSyndrome 3 = (1, -1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The three-qubit bit-flip code corrects any single bit-flip.** For the encoded state
`ψ_L = a|000⟩ + b|111⟩`. **This capstone now bundles all three ingredients:** (i) the
stabilisers `Z₁Z₂, Z₂Z₃` fix the codespace; (ii) **identifiability** — the four errors
`{I, X₁, X₂, X₃}` give the **distinct syndromes** `(+,+), (−,+), (−,−), (+,−)`
(`three_qubit_syndromes_distinct`), so measuring `(Z₁Z₂, Z₂Z₃)` pins down which error
occurred (the eigen-equation form is `three_qubit_syndrome_eigenstates`); and (iii) each
error `Xⱼ` is self-inverse, so re-applying the identified error restores `ψ_L`. -/
theorem three_qubit_corrects_single_bitflip (a b : ℂ) :
    (Matrix.toEuclideanLin Z1Z2 (logical a b) = logical a b
      ∧ Matrix.toEuclideanLin Z2Z3 (logical a b) = logical a b)
    ∧ Function.Injective errorSyndrome
    ∧ (Matrix.toEuclideanLin X1 (Matrix.toEuclideanLin X1 (logical a b)) = logical a b
      ∧ Matrix.toEuclideanLin X2 (Matrix.toEuclideanLin X2 (logical a b)) = logical a b
      ∧ Matrix.toEuclideanLin X3 (Matrix.toEuclideanLin X3 (logical a b)) = logical a b) :=
  ⟨⟨stab_Z1Z2_fixes_logical a b, stab_Z2Z3_fixes_logical a b⟩,
    three_qubit_syndromes_distinct, bitflip_recovers a b⟩

end QEC
end QM
end Empirical
end CSD
