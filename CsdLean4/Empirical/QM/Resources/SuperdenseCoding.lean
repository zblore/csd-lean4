import CsdLean4.Empirical.QM.Gates.BellPrep

/-!
# Empirical/QM: Superdense coding

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

Superdense coding (Bennett-Wiesner 1992): two classical bits are
transmitted by sending a single qubit, provided the sender and receiver
share one half each of a Bell pair. The sender applies one of four
single-qubit operations `{I, X, Z, XZ}` to her half of `|Φ⁺⟩`; the four
results are the four **mutually orthogonal** Bell states, so the
receiver recovers the two-bit message by a Bell-basis measurement.

This file delivers the algebraic core: the four encoding maps carry
`|Φ⁺⟩` to the four Bell states (up to a phase on the last), and the
four Bell states are an orthonormal family — hence perfectly
distinguishable, i.e. exactly two classical bits.

## Basis and conventions

Two qubits live in `EuclideanSpace ℂ (Fin 4)` with the ordering
`|00⟩ = e₀, |01⟩ = e₁, |10⟩ = e₂, |11⟩ = e₃` (matching
`Empirical/QM/Gates/BellPrep.lean`). The four Bell states:

- `|Φ⁺⟩ = (e₀ + e₃)/√2` (imported as `qmKetPhiPlus`),
- `|Ψ⁺⟩ = (e₁ + e₂)/√2`,
- `|Φ⁻⟩ = (e₀ − e₃)/√2`,
- `|Ψ⁻⟩ = (e₁ − e₂)/√2`.

The encodings act on the **first** (high-bit) qubit; `X ⊗ I`, `Z ⊗ I`,
`XZ ⊗ I` are the explicit `4×4` matrices. `(XZ ⊗ I)|Φ⁺⟩ = −|Ψ⁻⟩`
(phase `−1`), which does not affect orthogonality.

## Source

Bennett and Wiesner 1992, *Phys. Rev. Lett.* **69**, 2881.
-/

open Matrix ComplexConjugate

namespace CSD
namespace Empirical
namespace QM
namespace SuperdenseCoding

open Gates (qmKetPhiPlus)

/-! ## The remaining three Bell states -/

/-- `|Ψ⁺⟩ = (e₁ + e₂)/√2`. -/
noncomputable def qmKetPsiPlus : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 1 (1 : ℂ) + EuclideanSpace.single 2 (1 : ℂ))

/-- `|Φ⁻⟩ = (e₀ − e₃)/√2`. -/
noncomputable def qmKetPhiMinus : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 0 (1 : ℂ) - EuclideanSpace.single 3 (1 : ℂ))

/-- `|Ψ⁻⟩ = (e₁ − e₂)/√2`. -/
noncomputable def qmKetPsiMinus : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 1 (1 : ℂ) - EuclideanSpace.single 2 (1 : ℂ))

/-! ## The three nontrivial single-qubit encodings (on the first qubit) -/

/-- `X ⊗ I`: bit flip on the high qubit. Swaps `|00⟩↔|10⟩`, `|01⟩↔|11⟩`. -/
noncomputable def pauliX_tensor_I : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j : Fin 4 =>
    (match i, j with
      | 0, 2 => 1 | 1, 3 => 1
      | 2, 0 => 1 | 3, 1 => 1
      | _, _ => 0 : ℂ))

/-- `Z ⊗ I`: phase flip on the high qubit. `diag(1, 1, −1, −1)`. -/
noncomputable def pauliZ_tensor_I : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j : Fin 4 =>
    (match i, j with
      | 0, 0 => 1 | 1, 1 => 1
      | 2, 2 => -1 | 3, 3 => -1
      | _, _ => 0 : ℂ))

/-- `XZ ⊗ I` on the high qubit, where `XZ = [[0, −1], [1, 0]]`. -/
noncomputable def pauliXZ_tensor_I : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j : Fin 4 =>
    (match i, j with
      | 0, 2 => -1 | 1, 3 => -1
      | 2, 0 => 1 | 3, 1 => 1
      | _, _ => 0 : ℂ))

/-! ## Component extraction for `|Φ⁺⟩`

`qmKetPhiPlus.ofLp` is `(1/√2)` at indices `0, 3` and `0` elsewhere
(re-derived locally; `BellPrep`'s versions are `private`). -/

private lemma phiPlus_ofLp_zero : qmKetPhiPlus.ofLp 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

private lemma phiPlus_ofLp_one : qmKetPhiPlus.ofLp 1 = (0 : ℂ) := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

private lemma phiPlus_ofLp_two : qmKetPhiPlus.ofLp 2 = (0 : ℂ) := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

private lemma phiPlus_ofLp_three : qmKetPhiPlus.ofLp 3 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

/-- For any row `k`, applying a matrix `M` to `|Φ⁺⟩` collapses to
`(M[k,0] + M[k,3]) / √2`. -/
private lemma mulVec_phiPlus (M : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) :
    (M *ᵥ qmKetPhiPlus.ofLp) k
      = (Real.sqrt 2 : ℂ)⁻¹ * (M k 0 + M k 3) := by
  show ∑ j, M k j * qmKetPhiPlus.ofLp j = _
  rw [Fin.sum_univ_four, phiPlus_ofLp_zero, phiPlus_ofLp_one,
      phiPlus_ofLp_two, phiPlus_ofLp_three]
  ring

/-! ## Image identities: the four encodings produce the four Bell states -/

/-- `(X ⊗ I)|Φ⁺⟩ = |Ψ⁺⟩`. -/
theorem encode_X :
    (Matrix.toEuclideanLin pauliX_tensor_I) qmKetPhiPlus = qmKetPsiPlus := by
  ext i
  show (Matrix.toLpLin 2 2 pauliX_tensor_I) qmKetPhiPlus i = qmKetPsiPlus i
  rw [Matrix.toLpLin_apply]
  show (pauliX_tensor_I *ᵥ qmKetPhiPlus.ofLp) i = qmKetPsiPlus.ofLp i
  rw [mulVec_phiPlus]
  fin_cases i <;>
    simp [pauliX_tensor_I, qmKetPsiPlus, EuclideanSpace.single, Matrix.of_apply]

/-- `(Z ⊗ I)|Φ⁺⟩ = |Φ⁻⟩`. -/
theorem encode_Z :
    (Matrix.toEuclideanLin pauliZ_tensor_I) qmKetPhiPlus = qmKetPhiMinus := by
  ext i
  show (Matrix.toLpLin 2 2 pauliZ_tensor_I) qmKetPhiPlus i = qmKetPhiMinus i
  rw [Matrix.toLpLin_apply]
  show (pauliZ_tensor_I *ᵥ qmKetPhiPlus.ofLp) i = qmKetPhiMinus.ofLp i
  rw [mulVec_phiPlus]
  fin_cases i <;>
    simp [pauliZ_tensor_I, qmKetPhiMinus, EuclideanSpace.single, Matrix.of_apply]

/-- `(XZ ⊗ I)|Φ⁺⟩ = −|Ψ⁻⟩` (phase `−1`; orthogonality is unaffected). -/
theorem encode_XZ :
    (Matrix.toEuclideanLin pauliXZ_tensor_I) qmKetPhiPlus = -qmKetPsiMinus := by
  ext i
  show (Matrix.toLpLin 2 2 pauliXZ_tensor_I) qmKetPhiPlus i = (-qmKetPsiMinus) i
  rw [Matrix.toLpLin_apply]
  show (pauliXZ_tensor_I *ᵥ qmKetPhiPlus.ofLp) i = (-qmKetPsiMinus).ofLp i
  rw [mulVec_phiPlus]
  fin_cases i <;>
    simp [pauliXZ_tensor_I, qmKetPsiMinus, EuclideanSpace.single, Matrix.of_apply]

/-- `(I ⊗ I)|Φ⁺⟩ = |Φ⁺⟩` (the trivial encoding). -/
theorem encode_I :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 4) (Fin 4) ℂ)) qmKetPhiPlus
      = qmKetPhiPlus := by
  ext i
  show (Matrix.toLpLin 2 2 (1 : Matrix (Fin 4) (Fin 4) ℂ)) qmKetPhiPlus i
      = qmKetPhiPlus i
  rw [Matrix.toLpLin_apply]
  show ((1 : Matrix (Fin 4) (Fin 4) ℂ) *ᵥ qmKetPhiPlus.ofLp) i
      = qmKetPhiPlus.ofLp i
  rw [Matrix.one_mulVec]

/-! ## The Bell basis is orthonormal (perfect distinguishability) -/

/-- The four Bell states form an orthonormal family: distinct states are
orthogonal and each is a unit vector. Combined with the image identities
above, the four single-qubit encodings carry `|Φ⁺⟩` to a perfectly
distinguishable family — exactly two classical bits.

Stated as the six pairwise-orthogonality identities plus the four
unit-norm identities. -/
theorem bell_basis_orthonormal :
    inner ℂ qmKetPhiPlus qmKetPsiPlus = (0 : ℂ) ∧
    inner ℂ qmKetPhiPlus qmKetPhiMinus = (0 : ℂ) ∧
    inner ℂ qmKetPhiPlus qmKetPsiMinus = (0 : ℂ) ∧
    inner ℂ qmKetPsiPlus qmKetPhiMinus = (0 : ℂ) ∧
    inner ℂ qmKetPsiPlus qmKetPsiMinus = (0 : ℂ) ∧
    inner ℂ qmKetPhiMinus qmKetPsiMinus = (0 : ℂ) ∧
    inner ℂ qmKetPhiPlus qmKetPhiPlus = (1 : ℂ) ∧
    inner ℂ qmKetPsiPlus qmKetPsiPlus = (1 : ℂ) ∧
    inner ℂ qmKetPhiMinus qmKetPhiMinus = (1 : ℂ) ∧
    inner ℂ qmKetPsiMinus qmKetPsiMinus = (1 : ℂ) := by
  -- (√2⁻¹)² = ½, the only nonalgebraic fact.
  have half : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  -- Expand every inner product to single-vector inner products via
  -- bilinearity *before* any `inner_self → ‖·‖²` simp lemma can fire,
  -- then reduce the basis-index `if`s and apply `half`.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [qmKetPhiPlus, qmKetPsiPlus, qmKetPhiMinus, qmKetPsiMinus,
        inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
        inner_sub_left, inner_sub_right, EuclideanSpace.inner_single_left,
        PiLp.single_apply, map_inv₀, Complex.conj_ofReal]
      norm_num [half, Fin.ext_iff] <;> linear_combination (2 : ℂ) * half

end SuperdenseCoding
end QM
end Empirical
end CSD
