/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.KnillLaflamme
public import CsdLean4.Mathlib.QuantumInfo.Stabilizer

/-!
# Stabiliser codes meet Knill–Laflamme: the recovery of a distance-detected error family

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #14(b), the general half.

`QuantumInfo/Stabilizer.lean` builds the stabiliser group average `P` on the register and
`QuantumInfo/KnillLaflamme.lean` constructs a recovery channel from the condition
`P Eᵢᴴ Eⱼ P = cᵢⱼ P`. This file connects them for **Pauli error families** on a stabiliser code:

* `pauliMat a b` — the Pauli `X^a Z^b` as a matrix on the register's coordinates, with
  `pauliMat_mulVec` identifying it with `pauliOp`; the Pauli group law `pauliMat_mul`, the
  commutation rule `pauliMat_comm`, and the adjoint `pauliMat_conjTranspose`
  (`(X^a Z^b)ᴴ = (−1)^{a·b} X^a Z^b`) all transported through `Matrix.ext_of_mulVec`;
* `stabMat A B σ` — the group average as a matrix; ★ `isCodeProjector_stabMat` (Hermitian:
  every signed group element is self-adjoint because coherence forces `bdot (B x) (A x) = 0`;
  idempotent by `stabProjector_idem`), `stabMat_ne_zero`, and the two-sided absorption
  `genMat_mul_stabMat`, `stabMat_mul_genMat`;
* ★ `stabMat_mul_pauliMat_mul_stabMat_eq_zero` — **a Pauli anticommuting with a generator is
  killed by the code**: `P M P = P (G M) P = −P (M G) P = −P M P`;
* ★★ `stabMat_knillLaflamme` — **a Pauli error family whose pairwise products are detected**
  (for `i ≠ j` some generator anticommutes with `Eᵢᴴ Eⱼ`, i.e. the syndromes differ) satisfies
  Knill–Laflamme with `c = 1`: the code is non-degenerate for the family;
* ★★ `exists_recovery_stabMat` — **the recovery channel**: `R (Eᵢ ρ Eᵢᴴ) = ρ` on every code
  state, for every error of the family. The Steane instance is
  `Empirical/QM/QEC/SteaneRecovery.lean`.

## Honest scope

⚠️ The detection hypothesis is stated as a syndrome condition on labels, not derived from a
distance: a code of distance `d` detects every Pauli of weight `< d`, but "weight" and
"distance" are not defined here. Degenerate families (products in the stabiliser) are covered by
`KnillLaflamme.lean` but not by this file's `c = 1` statement.

References: D. Gottesman, *Stabilizer codes and quantum error correction* (1997), §3;
Nielsen–Chuang Thm 10.8; `QuantumInfo/KnillLaflamme.lean`; `QuantumInfo/Stabilizer.lean`;
`specs/BACKLOG.md` #14; `specs/steane-plan.md`.
-/

@[expose] public section

open Matrix
open scoped ComplexConjugate

namespace QuantumInfo

variable {n m : ℕ}

/-! ### Matrices from their action -/

/-- Two matrices with the same action on every vector are equal. -/
theorem _root_.Matrix.ext_of_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℂ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-! ### Pauli matrices -/

/-- The Pauli `X^a Z^b` as a matrix on the register's coordinates:
`(X^a Z^b) z w = [w = z + a] · (−1)^{b·w}`. -/
noncomputable def pauliMat (a b : Fin n → Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun z w => if w = z + a then pauliSign b w else 0

theorem add_add_self (z a : Fin n → Fin 2) : z + a + a = z := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, fin2_add_self, add_zero]

/-- The Pauli matrix acts as `pauliOp`. -/
theorem pauliMat_mulVec (a b : Fin n → Fin 2) (v : (Fin n → Fin 2) → ℂ) :
    pauliMat a b *ᵥ v = WithLp.ofLp (pauliOp a b (WithLp.toLp 2 v)) := by
  funext z
  simp only [mulVec, dotProduct, pauliMat, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, pauliOp_apply]

theorem pauliMat_zero : pauliMat (0 : Fin n → Fin 2) 0 = 1 := by
  refine Matrix.ext_of_mulVec fun v => ?_
  rw [pauliMat_mulVec, pauliOp_zero, WithLp.ofLp_toLp, one_mulVec]

/-- The Pauli group law in matrix form. -/
theorem pauliMat_mul (a b a' b' : Fin n → Fin 2) :
    pauliMat a b * pauliMat a' b' = pauliSign b a' • pauliMat (a + a') (b + b') := by
  refine Matrix.ext_of_mulVec fun v => ?_
  rw [← mulVec_mulVec, pauliMat_mulVec, pauliMat_mulVec, WithLp.toLp_ofLp, pauliOp_mul,
    smul_mulVec, pauliMat_mulVec, WithLp.ofLp_smul]

/-- Commutation in matrix form: the symplectic sign. -/
theorem pauliMat_comm (a b a' b' : Fin n → Fin 2) :
    pauliMat a b * pauliMat a' b'
      = signChar (bdot a b' + bdot b a') • (pauliMat a' b' * pauliMat a b) := by
  refine Matrix.ext_of_mulVec fun v => ?_
  rw [← mulVec_mulVec, pauliMat_mulVec, pauliMat_mulVec, WithLp.toLp_ofLp, pauliOp_comm,
    smul_mulVec, ← mulVec_mulVec, pauliMat_mulVec, pauliMat_mulVec, WithLp.toLp_ofLp,
    WithLp.ofLp_smul]

/-- The adjoint of a Pauli: `(X^a Z^b)ᴴ = (−1)^{b·a} X^a Z^b`. -/
theorem pauliMat_conjTranspose (a b : Fin n → Fin 2) :
    (pauliMat a b)ᴴ = pauliSign b a • pauliMat a b := by
  ext z w
  simp only [conjTranspose_apply, pauliMat, Matrix.smul_apply, smul_eq_mul]
  have hiff : z = w + a ↔ w = z + a := by
    constructor
    · rintro rfl
      rw [add_add_self]
    · rintro rfl
      rw [add_add_self]
  by_cases h : w = z + a
  · rw [if_pos (hiff.mpr h), if_pos h, Complex.star_def, conj_pauliSign, h, pauliSign_add_right]
    linear_combination (-(pauliSign b z)) * pauliSign_mul_self b a
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, star_zero, mul_zero]

/-- A Pauli is unitary: `Eᴴ E = 1`. -/
theorem pauliMat_conjTranspose_mul_self (a b : Fin n → Fin 2) :
    (pauliMat a b)ᴴ * pauliMat a b = 1 := by
  rw [pauliMat_conjTranspose, Matrix.smul_mul, pauliMat_mul, smul_smul, pauliSign_mul_self,
    one_smul]
  have h : a + a = 0 := by
    funext i
    exact fin2_add_self _
  have h' : b + b = 0 := by
    funext i
    exact fin2_add_self _
  rw [h, h', pauliMat_zero]

/-! ### The stabiliser projector as a matrix -/

variable (A B : (Fin m → Fin 2) → (Fin n → Fin 2)) (σ : (Fin m → Fin 2) → Fin 2)

/-- The signed group element `χ(σx) X^{Ax} Z^{Bx}` as a matrix. -/
noncomputable def genMat (x : Fin m → Fin 2) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  signChar (σ x) • pauliMat (A x) (B x)

/-- The stabiliser group average as a matrix. -/
noncomputable def stabMat : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ((2 : ℂ) ^ m)⁻¹ • ∑ x, genMat A B σ x

theorem genMat_mulVec (x : Fin m → Fin 2) (v : (Fin n → Fin 2) → ℂ) :
    genMat A B σ x *ᵥ v
      = WithLp.ofLp (signChar (σ x) • pauliOp (A x) (B x) (WithLp.toLp 2 v)) := by
  rw [genMat, smul_mulVec, pauliMat_mulVec, WithLp.ofLp_smul]

/-- The matrix acts as `stabProjector`. -/
theorem stabMat_mulVec (v : (Fin n → Fin 2) → ℂ) :
    stabMat A B σ *ᵥ v = WithLp.ofLp (stabProjector A B σ (WithLp.toLp 2 v)) := by
  rw [stabMat, stabProjector, smul_mulVec, sum_mulVec, WithLp.ofLp_smul, WithLp.ofLp_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [genMat_mulVec, WithLp.ofLp_smul]

variable {A B σ}
variable (hA : ∀ x y, A (x + y) = A x + A y) (hB : ∀ x y, B (x + y) = B x + B y)
variable (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y))

include hB hσ in
/-- Coherence at `(x, x)` forces `bdot (B x) (A x) = 0`: every group element is Hermitian. -/
theorem bdot_B_A_eq_zero (x : Fin m → Fin 2) : bdot (B x) (A x) = 0 := by
  have h := hσ x x
  have hxx : x + x = 0 := by
    funext i
    exact fin2_add_self _
  rw [hxx, stab_sigma_zero hB hσ, fin2_add_self, zero_add] at h
  exact h.symm

include hB hσ in
theorem genMat_conjTranspose (x : Fin m → Fin 2) : (genMat A B σ x)ᴴ = genMat A B σ x := by
  rw [genMat, conjTranspose_smul, pauliMat_conjTranspose, pauliSign, bdot_B_A_eq_zero hB hσ,
    signChar_zero, one_smul, Complex.star_def, conj_signChar]

include hA hB hσ in
/-- Left absorption: `G P = P`. -/
theorem genMat_mul_stabMat (x : Fin m → Fin 2) :
    genMat A B σ x * stabMat A B σ = stabMat A B σ := by
  refine Matrix.ext_of_mulVec fun v => ?_
  rw [← mulVec_mulVec, stabMat_mulVec, genMat_mulVec, WithLp.toLp_ofLp,
    stabProjector_absorb hA hB hσ]

include hB hσ in
theorem stabMat_conjTranspose : (stabMat A B σ)ᴴ = stabMat A B σ := by
  rw [stabMat, conjTranspose_smul, conjTranspose_sum]
  simp only [genMat_conjTranspose hB hσ]
  congr 1
  simp

include hA hB hσ in
/-- Right absorption: `P G = P`. -/
theorem stabMat_mul_genMat (x : Fin m → Fin 2) :
    stabMat A B σ * genMat A B σ x = stabMat A B σ := by
  have h := congrArg conjTranspose (genMat_mul_stabMat hA hB hσ x)
  rwa [conjTranspose_mul, genMat_conjTranspose hB hσ, stabMat_conjTranspose hB hσ] at h

include hA hB hσ in
/-- ★ **The group average is a code projector.** -/
theorem isCodeProjector_stabMat : IsCodeProjector (stabMat A B σ) where
  conjTranspose_eq := stabMat_conjTranspose hB hσ
  mul_self := by
    refine Matrix.ext_of_mulVec fun v => ?_
    rw [← mulVec_mulVec, stabMat_mulVec, stabMat_mulVec, WithLp.toLp_ofLp,
      stabProjector_idem hA hB hσ]

include hA hB hσ in
/-- The code is nonzero (independent labels). -/
theorem stabMat_ne_zero (hinj : ∀ x, A x = 0 → B x = 0 → x = 0) : stabMat A B σ ≠ 0 := by
  obtain ⟨ψ, hψ, hPψ, -⟩ := stabState_exists hA hB hσ hinj
  intro h0
  apply hψ
  have h := stabMat_mulVec A B σ (WithLp.ofLp ψ)
  rw [h0, zero_mulVec, WithLp.toLp_ofLp, hPψ] at h
  exact (WithLp.ofLp_eq_zero (p := 2)).mp h.symm

/-! ### Detected Paulis are killed by the code -/

include hA hB hσ in
/-- ★ **A Pauli anticommuting with some generator is killed by the code**: `P M P = 0`. -/
theorem stabMat_mul_pauliMat_mul_stabMat_eq_zero {u v : Fin n → Fin 2} (x : Fin m → Fin 2)
    (hx : bdot (A x) v + bdot (B x) u = 1) :
    stabMat A B σ * pauliMat u v * stabMat A B σ = 0 := by
  have hanti : genMat A B σ x * pauliMat u v = -(pauliMat u v * genMat A B σ x) := by
    rw [genMat, Matrix.smul_mul, Matrix.mul_smul, pauliMat_comm (A x) (B x) u v, hx,
      show signChar (1 : Fin 2) = -1 from rfl, neg_one_smul, smul_neg]
  have h1 : stabMat A B σ * pauliMat u v * stabMat A B σ
      = stabMat A B σ * (genMat A B σ x * pauliMat u v) * stabMat A B σ := by
    rw [← Matrix.mul_assoc, stabMat_mul_genMat hA hB hσ]
  have h2 : stabMat A B σ * (genMat A B σ x * pauliMat u v) * stabMat A B σ
      = -(stabMat A B σ * pauliMat u v * stabMat A B σ) := by
    rw [hanti, Matrix.mul_neg, Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
    rw [genMat_mul_stabMat hA hB hσ]
  have h3 : stabMat A B σ * pauliMat u v * stabMat A B σ
      = -(stabMat A B σ * pauliMat u v * stabMat A B σ) := h1.trans h2
  have h4 : (2 : ℂ) • (stabMat A B σ * pauliMat u v * stabMat A B σ) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h3
  exact (smul_eq_zero.mp h4).resolve_left two_ne_zero

include hA hB hσ in
/-- ★★ **A detected Pauli error family satisfies Knill–Laflamme with `c = 1`**: for `i ≠ j` some
generator anticommutes with `Eᵢᴴ Eⱼ` (the labels `(aᵢ + aⱼ, bᵢ + bⱼ)` pair to `1` with some
generator), so the code is non-degenerate for the family. -/
theorem stabMat_knillLaflamme {ι : Type*} [DecidableEq ι]
    (a b : ι → Fin n → Fin 2)
    (hsyn : ∀ i j, i ≠ j → ∃ x, bdot (A x) (b i + b j) + bdot (B x) (a i + a j) = 1) :
    KnillLaflamme (stabMat A B σ) (fun i => pauliMat (a i) (b i)) 1 := by
  intro i j
  have h1 : (pauliMat (a i) (b i))ᴴ * pauliMat (a j) (b j)
      = (pauliSign (b i) (a i) * pauliSign (b i) (a j)) • pauliMat (a i + a j) (b i + b j) := by
    rw [pauliMat_conjTranspose, Matrix.smul_mul, pauliMat_mul, smul_smul]
  rw [Matrix.mul_assoc (stabMat A B σ), h1, Matrix.mul_smul, Matrix.smul_mul]
  by_cases hij : i = j
  · subst hij
    have h : a i + a i = 0 := by
      funext k
      exact fin2_add_self _
    have h' : b i + b i = 0 := by
      funext k
      exact fin2_add_self _
    rw [h, h', pauliMat_zero, Matrix.mul_one, (isCodeProjector_stabMat hA hB hσ).mul_self,
      pauliSign_mul_self, one_smul, Matrix.one_apply_eq, one_smul]
  · obtain ⟨x, hx⟩ := hsyn i j hij
    rw [stabMat_mul_pauliMat_mul_stabMat_eq_zero hA hB hσ x hx, smul_zero,
      Matrix.one_apply_ne hij, zero_smul]

include hA hB hσ in
/-- ★★ **The recovery channel of a stabiliser code for a detected Pauli error family**: every
error of the family is undone on every code state, `R (Eᵢ ρ Eᵢᴴ) = ρ` for `ρ = P ρ P`. -/
theorem exists_recovery_stabMat (hinj : ∀ x, A x = 0 → B x = 0 → x = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → Fin n → Fin 2)
    (hsyn : ∀ i j, i ≠ j → ∃ x, bdot (A x) (b i + b j) + bdot (B x) (a i + a j) = 1) :
    ∃ R : Channel (Fin n → Fin 2) (Fin n → Fin 2) (Option ι),
      ∀ ρ, ρ = stabMat A B σ * ρ * stabMat A B σ →
        ∀ i, R.apply (pauliMat (a i) (b i) * ρ * (pauliMat (a i) (b i))ᴴ) = ρ := by
  obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme (isCodeProjector_stabMat hA hB hσ)
    (stabMat_ne_zero hA hB hσ hinj) (stabMat_knillLaflamme hA hB hσ a b hsyn)
  refine ⟨R, fun ρ hρ i => ?_⟩
  have h := hR ρ hρ i i
  rwa [Matrix.one_apply_eq, one_smul] at h

end QuantumInfo

end
