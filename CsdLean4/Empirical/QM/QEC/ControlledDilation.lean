/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.FlowChannel
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive

/-!
# Empirical/QM: the controlled-error dilation of a mixed-unitary channel

**Category:** 3-Local. QM-validity layer (matrix algebra over the K2 `Channel` / Stinespring
layer; no CSD content). BACKLOG #52, the generic half that #53 also needs.

A **mixed-unitary channel** `ρ ↦ ∑ₖ qₖ Eₖ ρ Eₖᴴ` (unitary errors `Eₖ` with weights `qₖ ≥ 0`,
`∑ qₖ = 1`) is the environment marginal of one joint unitary on system ⊗ environment, the
environment being the finite set of error labels:

* `weightVec q = ∑ₖ √qₖ eₖ` is the unit environment vector carrying the weights, and
  `weightRotation q e₀` a unitary on the environment with `R e₀ = weightVec q`
  (`Matrix.UnitaryGroup.exists_unitary_single_eq`);
* `blockDiagonal E` is the controlled error — apply `Eₖ` when the environment reads `eₖ` — unitary
  because each `Eₖ` is (`blockDiagonal_conjTranspose_mul`);
* `controlledUnitary E q e₀ = blockDiagonal E · (1 ⊗ R)`, so `U (ψ ⊗ e₀) = ∑ₖ √qₖ (Eₖ ψ) ⊗ eₖ`
  (`controlledUnitary_conjTranspose_mul`);
* ★ `stinespringChannel_controlledUnitary` — **the mixed-unitary channel
  `Channel.mixedUnitaryChannel E q` (Kraus operators `√qₖ Eₖ`, `CanonicalChannels.lean`) is the
  Stinespring channel of the controlled unitary with the environment ready in `e₀`**, as channels
  (`krausBlock_controlledUnitary_embedEnv`).

`RegisterDilation.lean` is the instance `e = Fin 4`, `E = errorOp` (the three-qubit single-error
channel); `IndependentNoise.lean` is the instance `e = Fin 2 × Fin 2 × Fin 2`, `E = flipOp`
(independent bit-flips); the Steane instance is BACKLOG #53.

## Source

Stinespring 1955; Nielsen–Chuang §8.2.3 (environmental models of noise).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

variable {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

/-! ### The environment side: weights as a unit vector, and a unitary reaching it -/

/-- The environment amplitude vector `∑ₖ √qₖ eₖ`. -/
noncomputable def weightVec (q : e → ℝ) : EuclideanSpace ℂ e :=
  WithLp.toLp 2 fun k => ((Real.sqrt (q k) : ℝ) : ℂ)

omit [Fintype e] [DecidableEq e] in
@[simp] lemma weightVec_apply (q : e → ℝ) (k : e) :
    weightVec q k = ((Real.sqrt (q k) : ℝ) : ℂ) := rfl

omit [DecidableEq e] in
lemma norm_weightVec (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    ‖weightVec q‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp only [weightVec_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hq0 _), hq1]

/-- A unitary on the environment taking the ready vector `e₀` to `weightVec q`. -/
noncomputable def weightRotation (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (e₀ : e) : Matrix e e ℂ :=
  (Classical.choose (Matrix.UnitaryGroup.exists_unitary_single_eq e₀ (weightVec q)
    (norm_weightVec q hq0 hq1))).val

lemma weightRotation_apply_single (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (e₀ : e) :
    Matrix.toEuclideanLin (weightRotation q hq0 hq1 e₀) (EuclideanSpace.single e₀ (1 : ℂ))
      = weightVec q :=
  Classical.choose_spec (Matrix.UnitaryGroup.exists_unitary_single_eq e₀ (weightVec q)
    (norm_weightVec q hq0 hq1))

lemma weightRotation_conjTranspose_mul (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (e₀ : e) :
    (weightRotation q hq0 hq1 e₀)ᴴ * weightRotation q hq0 hq1 e₀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp
    (Classical.choose (Matrix.UnitaryGroup.exists_unitary_single_eq e₀ (weightVec q)
      (norm_weightVec q hq0 hq1))).property
  rwa [Matrix.star_eq_conjTranspose] at h

/-- The ready column of the rotation is the weight vector: `R l e₀ = √qₗ`. -/
lemma weightRotation_apply_ready (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (e₀ l : e) : weightRotation q hq0 hq1 e₀ l e₀ = ((Real.sqrt (q l) : ℝ) : ℂ) := by
  have h := congrArg (fun v : EuclideanSpace ℂ e => v l)
    (weightRotation_apply_single q hq0 hq1 e₀)
  simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.single_apply] using h

/-! ### The controlled error and the joint unitary -/

/-- The controlled error `⊕ₖ Eₖ` is unitary when every `Eₖ` is. -/
theorem blockDiagonal_conjTranspose_mul (E : e → Matrix n n ℂ) (hE : ∀ k, (E k)ᴴ * E k = 1) :
    (Matrix.blockDiagonal E)ᴴ * Matrix.blockDiagonal E = 1 := by
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_one]
  congr 1
  funext k
  exact hE k

/-- **The controlled unitary** `U = (⊕ₖ Eₖ) · (1 ⊗ R_q)`: rotate the environment into the weight
vector, then apply the error the environment names. `U (ψ ⊗ e₀) = ∑ₖ √qₖ (Eₖ ψ) ⊗ eₖ`. Index
`(system, environment)`. -/
noncomputable def controlledUnitary (E : e → Matrix n n ℂ) (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) (e₀ : e) : Matrix (n × e) (n × e) ℂ :=
  Matrix.blockDiagonal E * ((1 : Matrix n n ℂ) ⊗ₖ weightRotation q hq0 hq1 e₀)

theorem controlledUnitary_conjTranspose_mul (E : e → Matrix n n ℂ)
    (hE : ∀ k, (E k)ᴴ * E k = 1) (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (e₀ : e) :
    (controlledUnitary E q hq0 hq1 e₀)ᴴ * controlledUnitary E q hq0 hq1 e₀ = 1 := by
  rw [controlledUnitary, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.blockDiagonal E)ᴴ, blockDiagonal_conjTranspose_mul E hE,
    Matrix.one_mul, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, weightRotation_conjTranspose_mul q hq0 hq1 e₀,
    Matrix.one_kronecker_one]

/-! ### The Stinespring identification -/

/-- Rotating the environment of a ready embedding: `(1 ⊗ R) (ψ ⊗ e₀) = ψ ⊗ (R e₀)`. -/
lemma kronecker_one_mul_embedEnv (R : Matrix e e ℂ) (e₀ : EuclideanSpace ℂ e) :
    ((1 : Matrix n n ℂ) ⊗ₖ R) * CSD.LF2.embedEnv n e₀
      = CSD.LF2.embedEnv n (Matrix.toEuclideanLin R e₀) := by
  ext ⟨t, l⟩ b
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, CSD.LF2.embedEnv_apply,
    Fintype.sum_prod_type (α₁ := n) (α₂ := e), mul_ite, mul_zero, Matrix.one_apply, ite_mul,
    zero_mul, one_mul, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  split_ifs with h <;> simp [h]

/-- The environment blocks of a controlled error with environment vector `v`: `Eₖ` weighted by
`v k`. -/
lemma krausBlock_blockDiagonal_mul_embedEnv (E : e → Matrix n n ℂ) (v : EuclideanSpace ℂ e)
    (k : e) :
    krausBlock (Matrix.blockDiagonal E * CSD.LF2.embedEnv n v) k = v k • E k := by
  ext a b
  simp only [krausBlock_apply, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    CSD.LF2.embedEnv_apply, Fintype.sum_prod_type (α₁ := n) (α₂ := e), ite_mul, mul_ite,
    zero_mul, mul_zero, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The environment blocks of `U (· ⊗ e₀)` are the Kraus operators `√qₖ Eₖ`. -/
theorem krausBlock_controlledUnitary_embedEnv (E : e → Matrix n n ℂ) (q : e → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) (e₀ k : e) :
    krausBlock (controlledUnitary E q hq0 hq1 e₀
        * CSD.LF2.embedEnv n (EuclideanSpace.single e₀ (1 : ℂ))) k
      = ((Real.sqrt (q k) : ℝ) : ℂ) • E k := by
  rw [controlledUnitary, Matrix.mul_assoc, kronecker_one_mul_embedEnv,
    weightRotation_apply_single, krausBlock_blockDiagonal_mul_embedEnv, weightVec_apply]

/-- ★ **The mixed-unitary channel is the Stinespring channel of the controlled unitary with a
ready environment**, as channels (equal Kraus families). -/
theorem stinespringChannel_controlledUnitary (E : e → Matrix n n ℂ)
    (hE : ∀ k, (E k)ᴴ * E k = 1) (q : e → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (e₀ : e) :
    CSD.LF2.stinespringChannel (controlledUnitary E q hq0 hq1 e₀)
        (controlledUnitary_conjTranspose_mul E hE q hq0 hq1 e₀)
        (EuclideanSpace.single e₀ (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
      = Channel.mixedUnitaryChannel E hE q hq0 hq1 := by
  have hk : (CSD.LF2.stinespringChannel (controlledUnitary E q hq0 hq1 e₀)
        (controlledUnitary_conjTranspose_mul E hE q hq0 hq1 e₀)
        (EuclideanSpace.single e₀ (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)).kraus
      = (Channel.mixedUnitaryChannel E hE q hq0 hq1).kraus := by
    funext k
    exact krausBlock_controlledUnitary_embedEnv E q hq0 hq1 e₀ k
  cases h : CSD.LF2.stinespringChannel (controlledUnitary E q hq0 hq1 e₀)
        (controlledUnitary_conjTranspose_mul E hE q hq0 hq1 e₀)
        (EuclideanSpace.single e₀ (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
  cases h' : Channel.mixedUnitaryChannel E hE q hq0 hq1
  rw [h] at hk; rw [h'] at hk
  simp only at hk
  subst hk
  rfl

end QEC
end QM
end Empirical
end CSD

end
