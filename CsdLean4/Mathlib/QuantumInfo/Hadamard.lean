import CsdLean4.Mathlib.QuantumInfo.Register

/-!
# Hadamard transform on the n-qubit register (R2)

**Category:** 1-Mathlib (CSD-free).

Phase R2 of `specs/nqubit-register-plan.md`: the Hadamard transform `H^⊗n` on the n-qubit
register, with entries the product of single-qubit Hadamard entries,

  `Hn x y = ∏ᵢ hadEntry (xᵢ) (yᵢ) = (-1)^(x·y) / √(2ⁿ)`,

and the key fact that it sends the all-zeros state to the **uniform superposition**:

  `Hn |0ⁿ⟩ = (1/√2)ⁿ · ∑_y |y⟩`   (`Hn_apply_zero`).

This is the first step of every Hadamard-based algorithm (Deutsch–Jozsa, Grover). It needs
no unitarity (that is R3, via character orthogonality); only the action on `|0ⁿ⟩`.
-/

open scoped ComplexConjugate

namespace QuantumInfo

variable {n : ℕ}

/-- The single-qubit Hadamard matrix entry `H(a,b) = (-1)^{ab} / √2`. -/
noncomputable def hadEntry (a b : Fin 2) : ℂ := (-1) ^ (a.val * b.val) / Real.sqrt 2

@[simp] lemma hadEntry_zero_right (b : Fin 2) : hadEntry b 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [hadEntry]

/-- The **Hadamard transform** `H^⊗n` on the n-qubit register, as a matrix indexed by
bitstrings: `Hn x y = ∏ᵢ H(xᵢ, yᵢ)`. -/
noncomputable def Hn : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, hadEntry (x i) (y i)

@[simp] lemma Hn_apply (x y : Fin n → Fin 2) : Hn x y = ∏ i, hadEntry (x i) (y i) := rfl

/-- The action of the Hadamard transform on a register state. -/
noncomputable def applyHn (ψ : QReg n) : QReg n := Matrix.toEuclideanLin Hn ψ

lemma applyHn_apply (ψ : QReg n) (y : Fin n → Fin 2) :
    applyHn ψ y = ∑ x, Hn y x * ψ x := by
  rw [applyHn, Matrix.toLpLin_apply]
  rfl

/-- **Hadamard on the all-zeros state is the uniform superposition.**
`applyHn |0ⁿ⟩ y = (1/√2)ⁿ` for every basis outcome `y` — equal amplitude everywhere. -/
theorem Hn_apply_zero (y : Fin n → Fin 2) :
    applyHn (basisState 0) y = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  rw [applyHn_apply, Finset.sum_eq_single (0 : Fin n → Fin 2)]
  · rw [basisState_apply, if_pos rfl, mul_one, Hn_apply]
    rw [show (fun i => hadEntry (y i) ((0 : Fin n → Fin 2) i)) = fun _ => (Real.sqrt 2 : ℂ)⁻¹
        from funext fun i => by rw [Pi.zero_apply, hadEntry_zero_right]]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro x _ hx; rw [basisState_apply, if_neg hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end QuantumInfo
