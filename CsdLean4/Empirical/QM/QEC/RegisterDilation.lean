/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SyndromeRecovery
public import CsdLean4.Empirical.QM.QEC.BitFlipDilation
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive

/-!
# Empirical/QM: the register's single-error channel as a joint unitary with an environment

**Category:** 3-Local. QM-validity layer (the register-level companion of `BitFlipDilation.lean`;
matrix algebra over the K2 `Channel` / Stinespring layer, no CSD content).

`BitFlipDilation.lean` realises the one-qubit bit-flip channel as the environment marginal of a
joint unitary on qubit ⊗ qubit. This file does the same for the **three-qubit register** and its
mixed single-error channel `singleFlipChannel q` (`SyndromeRecovery.lean`): the environment is a
four-level "which-error" register, and

* `errorVec q = ∑ₖ √qₖ eₖ` is the unit environment vector carrying the error weights;
* `errorRotation q` is a unitary on the environment with `R e₀ = errorVec q`, obtained from
  `Matrix.UnitaryGroup.exists_unitary_single_eq` (a unitary with a prescribed first column);
* `controlledError = blockDiagonal errorOp` applies `Eₖ` to the register when the environment is
  `eₖ` — the controlled error, unitary because each `Eₖ` is;
* `registerUnitary q = controlledError · (1 ⊗ R_q)`, so
  `U_q (ψ ⊗ e₀) = ∑ₖ √qₖ (Eₖ ψ) ⊗ eₖ`;
* `krausBlock_registerUnitary_embedEnv` — the environment blocks of `U_q (· ⊗ e₀)` are exactly the
  Kraus operators `√qₖ Eₖ`, and ★ `stinespringChannel_registerUnitary` — **the single-error channel
  is the Stinespring channel of `U_q` with a ready environment**, as channels.

`Empirical/CSD/QEC/RegisterFlow.lean` reads `U_q` as a `Σ`-flow on register ⊗ environment.

## Source

Stinespring 1955; Nielsen–Chuang §8.2.3 (environmental models of noise), §10.1 (the three-qubit
bit-flip code).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-! ### The environment side: weights as a unit vector, and a unitary reaching it -/

/-- The environment amplitude vector `∑ₖ √qₖ eₖ`. -/
noncomputable def errorVec (q : Fin 4 → ℝ) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 fun k => ((Real.sqrt (q k) : ℝ) : ℂ)

@[simp] lemma errorVec_apply (q : Fin 4 → ℝ) (k : Fin 4) :
    errorVec q k = ((Real.sqrt (q k) : ℝ) : ℂ) := rfl

lemma norm_errorVec (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    ‖errorVec q‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp only [errorVec_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hq0 _), hq1]

/-- A unitary on the environment taking the ready vector `e₀` to `errorVec q`. -/
noncomputable def errorRotation (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (Classical.choose (Matrix.UnitaryGroup.exists_unitary_single_eq 0 (errorVec q) (norm_errorVec q hq0 hq1))).val

lemma errorRotation_apply_single (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix.toEuclideanLin (errorRotation q hq0 hq1) (EuclideanSpace.single (0 : Fin 4) (1 : ℂ))
      = errorVec q :=
  Classical.choose_spec (Matrix.UnitaryGroup.exists_unitary_single_eq 0 (errorVec q) (norm_errorVec q hq0 hq1))

lemma errorRotation_conjTranspose_mul (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    (errorRotation q hq0 hq1)ᴴ * errorRotation q hq0 hq1 = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp
    (Classical.choose (Matrix.UnitaryGroup.exists_unitary_single_eq 0 (errorVec q) (norm_errorVec q hq0 hq1))).property
  rwa [Matrix.star_eq_conjTranspose] at h

/-- The first column of the rotation is the weight vector: `R l 0 = √qₗ`. -/
lemma errorRotation_apply_zero (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (l : Fin 4) : errorRotation q hq0 hq1 l 0 = ((Real.sqrt (q l) : ℝ) : ℂ) := by
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v l) (errorRotation_apply_single q hq0 hq1)
  simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.single_apply] using h

/-! ### The controlled error and the joint unitary -/

/-- The controlled error: apply `Eₖ` to the register when the environment is `eₖ`. Index
`(register, environment)`. -/
noncomputable def controlledError :
    Matrix ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ℂ :=
  Matrix.blockDiagonal errorOp

theorem controlledError_conjTranspose_mul : controlledErrorᴴ * controlledError = 1 := by
  rw [controlledError, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_one]
  congr 1
  funext k
  rw [errorOp_conjTranspose, errorOp_mul_self]
  rfl

/-- **The register's joint unitary** `U_q = controlledError · (1 ⊗ R_q)`: rotate the environment
into the weight vector, then apply the error the environment names.
`U_q (ψ ⊗ e₀) = ∑ₖ √qₖ (Eₖ ψ) ⊗ eₖ`. -/
noncomputable def registerUnitary (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ℂ :=
  controlledError * ((1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    ⊗ₖ errorRotation q hq0 hq1)

theorem registerUnitary_conjTranspose_mul (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    (registerUnitary q hq0 hq1)ᴴ * registerUnitary q hq0 hq1 = 1 := by
  rw [registerUnitary, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc controlledErrorᴴ, controlledError_conjTranspose_mul, Matrix.one_mul,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul, errorRotation_conjTranspose_mul q hq0 hq1, Matrix.one_kronecker_one]

/-- Rotating the environment of a ready embedding: `(1 ⊗ R) (ψ ⊗ e₀) = ψ ⊗ (R e₀)`. -/
lemma kronecker_one_mul_embedEnv {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n]
    [DecidableEq e] (R : Matrix e e ℂ) (e₀ : EuclideanSpace ℂ e) :
    ((1 : Matrix n n ℂ) ⊗ₖ R) * CSD.LF2.embedEnv n e₀
      = CSD.LF2.embedEnv n (Matrix.toEuclideanLin R e₀) := by
  ext ⟨t, l⟩ b
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, CSD.LF2.embedEnv_apply,
    Fintype.sum_prod_type (α₁ := n) (α₂ := e), mul_ite, mul_zero, Matrix.one_apply, ite_mul,
    zero_mul, one_mul, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  split_ifs with h <;> simp [h]

/-- The environment blocks of a controlled error with environment vector `v`: `Eₖ` weighted by
`v k`. -/
lemma krausBlock_blockDiagonal_mul_embedEnv {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n]
    [DecidableEq e] (E : e → Matrix n n ℂ) (v : EuclideanSpace ℂ e) (k : e) :
    krausBlock (Matrix.blockDiagonal E * CSD.LF2.embedEnv n v) k = v k • E k := by
  ext a b
  simp only [krausBlock_apply, Matrix.mul_apply, Matrix.blockDiagonal_apply, CSD.LF2.embedEnv_apply,
    Fintype.sum_prod_type (α₁ := n) (α₂ := e), ite_mul, mul_ite, zero_mul, mul_zero,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The environment blocks of `U_q (· ⊗ e₀)` are the Kraus operators `√qₖ Eₖ` of the single-error
channel. -/
theorem krausBlock_registerUnitary_embedEnv (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) (k : Fin 4) :
    krausBlock (registerUnitary q hq0 hq1
        * CSD.LF2.embedEnv (Fin 2 × Fin 2 × Fin 2) (EuclideanSpace.single (0 : Fin 4) (1 : ℂ))) k
      = ((Real.sqrt (q k) : ℝ) : ℂ) • errorOp k := by
  rw [registerUnitary, Matrix.mul_assoc, kronecker_one_mul_embedEnv, errorRotation_apply_single,
    controlledError, krausBlock_blockDiagonal_mul_embedEnv, errorVec_apply]

/-- ★ **The single-error channel is the Stinespring channel of `U_q` with a ready environment**,
as channels (equal Kraus families). -/
theorem stinespringChannel_registerUnitary (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    CSD.LF2.stinespringChannel (registerUnitary q hq0 hq1)
        (registerUnitary_conjTranspose_mul q hq0 hq1)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
      = singleFlipChannel q hq0 hq1 := by
  have hk : (CSD.LF2.stinespringChannel (registerUnitary q hq0 hq1)
        (registerUnitary_conjTranspose_mul q hq0 hq1)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)).kraus
      = (singleFlipChannel q hq0 hq1).kraus := by
    funext k
    exact krausBlock_registerUnitary_embedEnv q hq0 hq1 k
  cases h : CSD.LF2.stinespringChannel (registerUnitary q hq0 hq1)
        (registerUnitary_conjTranspose_mul q hq0 hq1)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
  cases h' : singleFlipChannel q hq0 hq1
  rw [h] at hk; rw [h'] at hk
  simp only at hk
  subst hk
  rfl

end QEC
end QM
end Empirical
end CSD
