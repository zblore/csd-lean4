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
open scoped Matrix

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

/-! ## R3 — character orthogonality ⟹ `H^⊗n` unitary

The Hadamard transform is **unitary** (`Hn_unitary`, `Hnᴴ * Hn = 1`), so the full output
distribution of any Hadamard circuit is a legitimate probability vector — not merely the
single all-zeros amplitude of R2.

The route is the per-qubit factorisation rather than a global XOR character sum: the matrix
statement `(Hnᴴ * Hn) x x' = [x = x']` *is* the multi-qubit character orthogonality, and it
factors over qubits (`Finset.prod_univ_sum`) into `n` copies of the single-qubit
orthogonality `∑_b H(b,a) H(b,a') = [a = a']` (`hadEntry_mul_sum`). This avoids defining
bitwise XOR on bitstrings; the per-qubit sum is the character sum on `Fin 2`. -/

/-- The single-qubit Hadamard entry is **symmetric**: `H(a,b) = H(b,a)`. -/
lemma hadEntry_comm (a b : Fin 2) : hadEntry a b = hadEntry b a := by
  rw [hadEntry, hadEntry, Nat.mul_comm]

/-- The single-qubit Hadamard entry is **real**: conjugation fixes it. -/
lemma hadEntry_conj (a b : Fin 2) : conj (hadEntry a b) = hadEntry a b := by
  simp only [hadEntry, map_div₀, map_pow, map_neg, map_one, Complex.conj_ofReal]

/-- `√2 · √2 = 2` over `ℂ` (the coerced real square root). -/
lemma sqrt2_mul_self : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

/-- **Single-qubit character orthogonality:** `∑_{b} H(b,a) H(b,a') = [a = a']`. The two
columns of the `2×2` Hadamard are orthonormal. -/
lemma hadEntry_mul_sum (a a' : Fin 2) :
    ∑ b : Fin 2, hadEntry b a * hadEntry b a' = if a = a' then 1 else 0 := by
  have key : ∀ b : Fin 2, hadEntry b a * hadEntry b a'
      = (-1) ^ (b.val * a.val) * (-1) ^ (b.val * a'.val) * 2⁻¹ := fun b => by
    rw [hadEntry, hadEntry, div_mul_div_comm, sqrt2_mul_self, div_eq_mul_inv]
  simp_rw [key, Fin.sum_univ_two]
  fin_cases a <;> fin_cases a' <;> norm_num

/-- **The Hadamard transform is Hermitian:** `Hnᴴ = Hn` (real entries, symmetric). -/
lemma Hn_conjTranspose : (Hn : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)ᴴ = Hn := by
  ext x y
  rw [Matrix.conjTranspose_apply, ← starRingEnd_apply, Hn_apply, Hn_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hadEntry_conj, hadEntry_comm]

/-- **The Hadamard transform is unitary:** `Hnᴴ * Hn = 1`. This is the multi-qubit character
orthogonality; entrywise it reads `∑_y H(x,y) H(y,x') = [x = x']`, which factors over qubits
into `n` single-qubit orthogonalities. Hence the output of any Hadamard circuit is a genuine
probability vector. -/
theorem Hn_unitary : (Hn : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)ᴴ * Hn = 1 := by
  rw [Hn_conjTranspose]
  ext x x'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have step : ∀ y : Fin n → Fin 2,
      Hn x y * Hn y x' = ∏ i, hadEntry (y i) (x i) * hadEntry (y i) (x' i) := by
    intro y
    rw [Hn_apply, Hn_apply, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hadEntry_comm (x i) (y i)]
  simp_rw [step]
  have hfac : (∑ y : Fin n → Fin 2, ∏ i, hadEntry (y i) (x i) * hadEntry (y i) (x' i))
      = ∏ i, ∑ b : Fin 2, hadEntry b (x i) * hadEntry b (x' i) := by
    rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
        (fun i b => hadEntry b (x i) * hadEntry b (x' i)), Fintype.piFinset_univ]
  rw [hfac]
  simp_rw [hadEntry_mul_sum]
  by_cases h : x = x'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **`H^⊗n` is an involution:** applying the Hadamard transform twice is the identity
(`Hn * Hn = 1`), since `Hn` is both Hermitian and unitary. -/
theorem Hn_mul_self : (Hn : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) * Hn = 1 := by
  nth_rewrite 1 [← Hn_conjTranspose]; exact Hn_unitary

end QuantumInfo
