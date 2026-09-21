/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SyndromeRecovery
public import CsdLean4.Empirical.QM.QEC.BitFlipDilation
public import CsdLean4.Empirical.QM.QEC.ControlledDilation

/-!
# Empirical/QM: the register's single-error channel as a joint unitary with an environment

**Category:** 3-Local. QM-validity layer (the register-level companion of `BitFlipDilation.lean`;
matrix algebra over the K2 `Channel` / Stinespring layer, no CSD content).

`BitFlipDilation.lean` realises the one-qubit bit-flip channel as the environment marginal of a
joint unitary on qubit ⊗ qubit. This file does the same for the **three-qubit register** and its
mixed single-error channel `singleFlipChannel q` (`SyndromeRecovery.lean`), as the instance
`e = Fin 4`, `E = errorOp` of the generic controlled-error dilation of `ControlledDilation.lean`
(BACKLOG #52): the environment is a four-level "which-error" register, and

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

Every statement is the generic one specialised (`singleFlipChannel_eq_mixedUnitaryChannel` is
`rfl`); the names are kept for the consumers (`Empirical/CSD/QEC/RegisterFlow.lean` reads `U_q`
as a `Σ`-flow on register ⊗ environment).

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

/-- Each error `Eₖ ∈ {I, X₁, X₂, X₃}` is unitary. -/
lemma errorOp_conjTranspose_mul_self (k : Fin 4) : (errorOp k)ᴴ * errorOp k = 1 := by
  rw [errorOp_conjTranspose, errorOp_mul_self]

/-! ### The environment side: weights as a unit vector, and a unitary reaching it -/

/-- The environment amplitude vector `∑ₖ √qₖ eₖ`. -/
noncomputable def errorVec (q : Fin 4 → ℝ) : EuclideanSpace ℂ (Fin 4) :=
  weightVec q

@[simp] lemma errorVec_apply (q : Fin 4 → ℝ) (k : Fin 4) :
    errorVec q k = ((Real.sqrt (q k) : ℝ) : ℂ) := rfl

lemma norm_errorVec (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    ‖errorVec q‖ = 1 :=
  norm_weightVec q hq0 hq1

/-- A unitary on the environment taking the ready vector `e₀` to `errorVec q`. -/
noncomputable def errorRotation (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  weightRotation q hq0 hq1 0

lemma errorRotation_apply_single (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix.toEuclideanLin (errorRotation q hq0 hq1) (EuclideanSpace.single (0 : Fin 4) (1 : ℂ))
      = errorVec q :=
  weightRotation_apply_single q hq0 hq1 0

lemma errorRotation_conjTranspose_mul (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    (errorRotation q hq0 hq1)ᴴ * errorRotation q hq0 hq1 = 1 :=
  weightRotation_conjTranspose_mul q hq0 hq1 0

/-- The first column of the rotation is the weight vector: `R l 0 = √qₗ`. -/
lemma errorRotation_apply_zero (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (l : Fin 4) : errorRotation q hq0 hq1 l 0 = ((Real.sqrt (q l) : ℝ) : ℂ) :=
  weightRotation_apply_ready q hq0 hq1 0 l

/-! ### The controlled error and the joint unitary -/

/-- The controlled error: apply `Eₖ` to the register when the environment is `eₖ`. Index
`(register, environment)`. -/
noncomputable def controlledError :
    Matrix ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ℂ :=
  Matrix.blockDiagonal errorOp

theorem controlledError_conjTranspose_mul : controlledErrorᴴ * controlledError = 1 :=
  blockDiagonal_conjTranspose_mul errorOp errorOp_conjTranspose_mul_self

/-- **The register's joint unitary** `U_q = controlledError · (1 ⊗ R_q)`: rotate the environment
into the weight vector, then apply the error the environment names.
`U_q (ψ ⊗ e₀) = ∑ₖ √qₖ (Eₖ ψ) ⊗ eₖ`. -/
noncomputable def registerUnitary (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ((Fin 2 × Fin 2 × Fin 2) × Fin 4) ℂ :=
  controlledUnitary errorOp q hq0 hq1 0

lemma registerUnitary_eq (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    registerUnitary q hq0 hq1 = controlledError
      * ((1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
        ⊗ₖ errorRotation q hq0 hq1) := rfl

theorem registerUnitary_conjTranspose_mul (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    (registerUnitary q hq0 hq1)ᴴ * registerUnitary q hq0 hq1 = 1 :=
  controlledUnitary_conjTranspose_mul errorOp errorOp_conjTranspose_mul_self q hq0 hq1 0

/-- The environment blocks of `U_q (· ⊗ e₀)` are the Kraus operators `√qₖ Eₖ` of the single-error
channel. -/
theorem krausBlock_registerUnitary_embedEnv (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) (k : Fin 4) :
    krausBlock (registerUnitary q hq0 hq1
        * CSD.LF2.embedEnv (Fin 2 × Fin 2 × Fin 2) (EuclideanSpace.single (0 : Fin 4) (1 : ℂ))) k
      = ((Real.sqrt (q k) : ℝ) : ℂ) • errorOp k :=
  krausBlock_controlledUnitary_embedEnv errorOp q hq0 hq1 0 k

/-- The single-error channel is the mixed-unitary channel (`CanonicalChannels.lean`) of the error
family. -/
lemma singleFlipChannel_eq_mixedUnitaryChannel (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    singleFlipChannel q hq0 hq1
      = Channel.mixedUnitaryChannel errorOp errorOp_conjTranspose_mul_self q hq0 hq1 :=
  rfl

/-- ★ **The single-error channel is the Stinespring channel of `U_q` with a ready environment**,
as channels (equal Kraus families). -/
theorem stinespringChannel_registerUnitary (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    CSD.LF2.stinespringChannel (registerUnitary q hq0 hq1)
        (registerUnitary_conjTranspose_mul q hq0 hq1)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
      = singleFlipChannel q hq0 hq1 := by
  rw [singleFlipChannel_eq_mixedUnitaryChannel]
  exact stinespringChannel_controlledUnitary errorOp errorOp_conjTranspose_mul_self q hq0 hq1 0

end QEC
end QM
end Empirical
end CSD
