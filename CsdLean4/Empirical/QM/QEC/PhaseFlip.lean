import CsdLean4.Empirical.QM.QEC.ThreeQubit

/-!
# Empirical/QM: the three-qubit phase-flip code (Hadamard dual of the bit-flip code)

**Category:** 3-Local. QM-validity layer. The phase-flip repetition code, the Hadamard
conjugate (`X ↔ Z`, `|0/1⟩ ↔ |±⟩`) of `ThreeQubit.lean`'s bit-flip code: it corrects any
single **phase** (`Z`) error.

A logical qubit is encoded as `a|+++⟩ + b|---⟩` (here `|+⟩ = |0⟩+|1⟩`, `|−⟩ = |0⟩−|1⟩`,
unnormalised — normalisation is irrelevant to correction). The stabilisers are
`X₁X₂ = X⊗X⊗I` and `X₂X₃ = I⊗X⊗X`; they fix the codespace (`stab_*_fixes_logicalPF`).
The errors `{I, Z₁, Z₂, Z₃}` each (anti)commute with the stabilisers in a **distinct**
pattern, so the errored codeword is a stabiliser eigenstate carrying the syndrome
`(+,+),(−,+),(−,−),(+,−)` (`syndromePF_*`); measuring `(X₁X₂, X₂X₃)` identifies the error,
and each `Z` is self-inverse so re-applying it recovers (`phaseflip_recovers`).

Everything reuses the bit-flip file's Pauli / Kronecker algebra; the syndrome signs are
driven by the same single-qubit anticommutation `pX·pZ = −(pZ·pX)`.

## Source

Shor 1995 (the phase-flip half of the 9-qubit code); Nielsen-Chuang §10.1.
-/

open Matrix
open scoped Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-! ### Phase errors and `X`-type stabilisers -/

/-- `Z₁ = Z ⊗ I ⊗ I` (a phase error on qubit 1). -/
def Z1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 pZ 1 1
/-- `Z₂ = I ⊗ Z ⊗ I`. -/
def Z2 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 pZ 1
/-- `Z₃ = I ⊗ I ⊗ Z`. -/
def Z3 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 1 pZ
/-- The stabiliser `X₁X₂ = X ⊗ X ⊗ I`. -/
def X1X2 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 pX pX 1
/-- The stabiliser `X₂X₃ = I ⊗ X ⊗ X`. -/
def X2X3 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 pX pX

/-- The single-qubit anticommutation in the form needed here, `XZ = −ZX`. -/
lemma pX_mul_pZ : pX * pZ = - (pZ * pX) := by rw [pZ_mul_pX]; exact (neg_neg _).symm

@[simp] lemma Z1_mul_Z1 : Z1 * Z1 = 1 := by
  rw [Z1, kron3_mul, pZ_mul_pZ]; simp only [mul_one, kron3, Matrix.one_kronecker_one]

@[simp] lemma Z2_mul_Z2 : Z2 * Z2 = 1 := by
  rw [Z2, kron3_mul, pZ_mul_pZ]; simp only [mul_one, one_mul, kron3, Matrix.one_kronecker_one]

@[simp] lemma Z3_mul_Z3 : Z3 * Z3 = 1 := by
  rw [Z3, kron3_mul, pZ_mul_pZ]; simp only [one_mul, kron3, Matrix.one_kronecker_one]

/-- `X₁X₂` anticommutes with `Z₁`. -/
lemma X1X2_anticomm_Z1 : X1X2 * Z1 = - (Z1 * X1X2) := by
  rw [X1X2, Z1, kron3_mul, kron3_mul, pX_mul_pZ, kron3_neg_left]; simp [mul_one, one_mul]

/-- `X₁X₂` anticommutes with `Z₂`. -/
lemma X1X2_anticomm_Z2 : X1X2 * Z2 = - (Z2 * X1X2) := by
  rw [X1X2, Z2, kron3_mul, kron3_mul, pX_mul_pZ, kron3_neg_mid]; simp [mul_one, one_mul]

/-- `X₁X₂` commutes with `Z₃`. -/
lemma X1X2_comm_Z3 : X1X2 * Z3 = Z3 * X1X2 := by
  rw [X1X2, Z3, kron3_mul, kron3_mul]; simp [mul_one, one_mul]

/-- `X₂X₃` commutes with `Z₁`. -/
lemma X2X3_comm_Z1 : X2X3 * Z1 = Z1 * X2X3 := by
  rw [X2X3, Z1, kron3_mul, kron3_mul]; simp [mul_one, one_mul]

/-- `X₂X₃` anticommutes with `Z₂`. -/
lemma X2X3_anticomm_Z2 : X2X3 * Z2 = - (Z2 * X2X3) := by
  rw [X2X3, Z2, kron3_mul, kron3_mul, pX_mul_pZ, kron3_neg_mid]; simp [mul_one, one_mul]

/-- `X₂X₃` anticommutes with `Z₃`. -/
lemma X2X3_anticomm_Z3 : X2X3 * Z3 = - (Z3 * X2X3) := by
  rw [X2X3, Z3, kron3_mul, kron3_mul, pX_mul_pZ, kron3_neg_right]; simp [mul_one, one_mul]

/-! ### The logical states `|+++⟩`, `|---⟩` and stabiliser fixing -/

/-- The `±` parity sign `(−1)^{i₁+i₂+i₃}` on a computational basis index. -/
def paritySign (i : Fin 2 × Fin 2 × Fin 2) : ℂ :=
  (-1) ^ (i.1.val + i.2.1.val + i.2.2.val)

/-- `|+⟩⊗|+⟩⊗|+⟩` (unnormalised): the equal superposition of all basis states. -/
noncomputable def lplus : H3 := ∑ i : Fin 2 × Fin 2 × Fin 2, EuclideanSpace.single i (1 : ℂ)
/-- `|−⟩⊗|−⟩⊗|−⟩` (unnormalised): the parity-signed superposition. -/
noncomputable def lminus : H3 := ∑ i : Fin 2 × Fin 2 × Fin 2, EuclideanSpace.single i (paritySign i)

/-- The phase-flip logical state `a|+++⟩ + b|---⟩`. -/
noncomputable def logicalPF (a b : ℂ) : H3 := a • lplus + b • lminus

set_option maxHeartbeats 2000000 in
/-- `X₁X₂` fixes the codespace: `X₁X₂ · ψ_L = ψ_L`. -/
lemma stab_X1X2_fixes_logicalPF (a b : ℂ) :
    Matrix.toEuclideanLin X1X2 (logicalPF a b) = logicalPF a b := by
  ext i
  simp only [Matrix.toEuclideanLin_apply, logicalPF, lplus, lminus, paritySign, X1X2, kron3, pX,
    map_add, map_smul]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Fin.prod_univ_two,
      Prod.ext_iff] <;> ring

set_option maxHeartbeats 2000000 in
/-- `X₂X₃` fixes the codespace: `X₂X₃ · ψ_L = ψ_L`. -/
lemma stab_X2X3_fixes_logicalPF (a b : ℂ) :
    Matrix.toEuclideanLin X2X3 (logicalPF a b) = logicalPF a b := by
  ext i
  simp only [Matrix.toEuclideanLin_apply, logicalPF, lplus, lminus, paritySign, X2X3, kron3, pX,
    map_add, map_smul]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Fin.prod_univ_two,
      Prod.ext_iff] <;> ring

/-! ### Syndromes, recovery, and the correction theorem -/

/-- The errored codeword carries the **syndrome** of the phase error: `(I,Z₁,Z₂,Z₃)` give
the distinct stabiliser-eigenvalue patterns `(+,+),(−,+),(−,−),(+,−)`. -/
lemma syndromePF_Z1 (a b : ℂ) :
    Matrix.toEuclideanLin X1X2 (Matrix.toEuclideanLin Z1 (logicalPF a b))
        = - Matrix.toEuclideanLin Z1 (logicalPF a b)
    ∧ Matrix.toEuclideanLin X2X3 (Matrix.toEuclideanLin Z1 (logicalPF a b))
        = Matrix.toEuclideanLin Z1 (logicalPF a b) := by
  refine ⟨?_, ?_⟩
  · rw [← tel_mul, X1X2_anticomm_Z1, tel_neg, tel_mul, stab_X1X2_fixes_logicalPF]
  · rw [← tel_mul, X2X3_comm_Z1, tel_mul, stab_X2X3_fixes_logicalPF]

lemma syndromePF_Z2 (a b : ℂ) :
    Matrix.toEuclideanLin X1X2 (Matrix.toEuclideanLin Z2 (logicalPF a b))
        = - Matrix.toEuclideanLin Z2 (logicalPF a b)
    ∧ Matrix.toEuclideanLin X2X3 (Matrix.toEuclideanLin Z2 (logicalPF a b))
        = - Matrix.toEuclideanLin Z2 (logicalPF a b) := by
  refine ⟨?_, ?_⟩
  · rw [← tel_mul, X1X2_anticomm_Z2, tel_neg, tel_mul, stab_X1X2_fixes_logicalPF]
  · rw [← tel_mul, X2X3_anticomm_Z2, tel_neg, tel_mul, stab_X2X3_fixes_logicalPF]

lemma syndromePF_Z3 (a b : ℂ) :
    Matrix.toEuclideanLin X1X2 (Matrix.toEuclideanLin Z3 (logicalPF a b))
        = Matrix.toEuclideanLin Z3 (logicalPF a b)
    ∧ Matrix.toEuclideanLin X2X3 (Matrix.toEuclideanLin Z3 (logicalPF a b))
        = - Matrix.toEuclideanLin Z3 (logicalPF a b) := by
  refine ⟨?_, ?_⟩
  · rw [← tel_mul, X1X2_comm_Z3, tel_mul, stab_X1X2_fixes_logicalPF]
  · rw [← tel_mul, X2X3_anticomm_Z3, tel_neg, tel_mul, stab_X2X3_fixes_logicalPF]

/-- **Recovery.** Each single phase flip is self-inverse, so re-applying the identified
correction restores the logical state: `Zⱼ · (Zⱼ · ψ_L) = ψ_L`. -/
lemma phaseflip_recovers (a b : ℂ) :
    Matrix.toEuclideanLin Z1 (Matrix.toEuclideanLin Z1 (logicalPF a b)) = logicalPF a b
    ∧ Matrix.toEuclideanLin Z2 (Matrix.toEuclideanLin Z2 (logicalPF a b)) = logicalPF a b
    ∧ Matrix.toEuclideanLin Z3 (Matrix.toEuclideanLin Z3 (logicalPF a b)) = logicalPF a b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← tel_mul, Z1_mul_Z1, tel_one]
  · rw [← tel_mul, Z2_mul_Z2, tel_one]
  · rw [← tel_mul, Z3_mul_Z3, tel_one]

/-- **The three-qubit phase-flip code corrects any single phase flip.** Hadamard dual of
`three_qubit_corrects_single_bitflip`. **This capstone bundles** the stabiliser-fixing and
the self-inverse-recovery ingredients; the **identifiability** ingredient (the four errors
give distinct syndromes) is the separate `syndromePF_*` lemmas above, not part of this
theorem's conjunction — read them together for the full correction claim. -/
theorem three_qubit_corrects_single_phaseflip (a b : ℂ) :
    (Matrix.toEuclideanLin X1X2 (logicalPF a b) = logicalPF a b
      ∧ Matrix.toEuclideanLin X2X3 (logicalPF a b) = logicalPF a b)
    ∧ (Matrix.toEuclideanLin Z1 (Matrix.toEuclideanLin Z1 (logicalPF a b)) = logicalPF a b
      ∧ Matrix.toEuclideanLin Z2 (Matrix.toEuclideanLin Z2 (logicalPF a b)) = logicalPF a b
      ∧ Matrix.toEuclideanLin Z3 (Matrix.toEuclideanLin Z3 (logicalPF a b)) = logicalPF a b) :=
  ⟨⟨stab_X1X2_fixes_logicalPF a b, stab_X2X3_fixes_logicalPF a b⟩, phaseflip_recovers a b⟩

end QEC
end QM
end Empirical
end CSD
