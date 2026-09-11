/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.BitFlipChannel
public import CsdLean4.LF2.FlowChannel

/-!
# Empirical/QM/QEC: the bit-flip channel as the environment marginal of a joint unitary

**Category:** 3-Local (QM-validity companion of `BitFlipChannel.lean`).

The bit-flip channel `Φ(ρ) = (1 − p) ρ + p X ρ X` has a concrete Stinespring dilation: the joint
unitary `U_p = CX · (I ⊗ R_p)` on `system ⊗ environment` (an environment qubit rotated by
`R_p |0⟩ = √(1−p) |0⟩ + √p |1⟩`, then a flip of the system controlled by the environment), with
the environment ready in `|0⟩`:

    `U_p (ψ ⊗ |0⟩) = √(1−p) ψ ⊗ |0⟩ + √p (Xψ) ⊗ |1⟩`.

* `flipRotation`, `controlledFlip`, `bitFlipUnitary` — the pieces and `U_p`;
  `bitFlipUnitary_conjTranspose_mul` — unitarity;
* `krausBlock_bitFlipUnitary_embedEnv` — the environment blocks of `U_p · (· ⊗ |0⟩)` are exactly
  the bit-flip Kraus operators `{√(1−p) I, √p X}`;
* ★ `stinespringChannel_bitFlipUnitary` — **the bit-flip channel IS the Stinespring channel of
  `U_p` with a ready environment**, as channels (equal Kraus families).

Consumer: `Empirical/CSD/QEC/ThreeQubit.lean`, where `U_p` lifted to a `Σ`-flow produces the
bit-flip channel on the density operators of preparations (W11 of `specs/qit-chain-scoping.md`).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder Kronecker


namespace CSD.Empirical.QM.QEC

/-! ### The bit-flip channel as the environment marginal of a joint unitary -/

/-- The real rotation `R_p` with `R_p |0⟩ = √(1−p) |0⟩ + √p |1⟩` on the environment qubit. -/
noncomputable def flipRotation (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt (1 - p) : ℝ) : ℂ), -((Real.sqrt p : ℝ) : ℂ);
     ((Real.sqrt p : ℝ) : ℂ), ((Real.sqrt (1 - p) : ℝ) : ℂ)]

/-- The controlled flip `CX` with the environment as control: applies `X` to the system when the
environment is `|1⟩`. Index `(system, environment)`. -/
def controlledFlip : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun q r => if q.2 = r.2 then (if q.2 = 1 then pX q.1 r.1 else (1 : Matrix (Fin 2) (Fin 2) ℂ) q.1 r.1) else 0

/-- **The bit-flip joint unitary** `U_p = CX · (I ⊗ R_p)`: rotate the environment, then flip the
system conditioned on it. `U_p (ψ ⊗ |0⟩) = √(1−p) ψ ⊗ |0⟩ + √p (Xψ) ⊗ |1⟩`. -/
noncomputable def bitFlipUnitary (p : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  controlledFlip * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ flipRotation p)

theorem flipRotation_conjTranspose_mul (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (flipRotation p)ᴴ * flipRotation p = 1 := by
  have h1 : ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) = 1 - (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have h2 : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipRotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.conj_ofReal] <;>
    · first
        | ring1
        | linear_combination h1 + h2

theorem controlledFlip_conjTranspose_mul : controlledFlipᴴ * controlledFlip = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [controlledFlip, pX, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply]

/-- `U_p` is unitary. -/
theorem bitFlipUnitary_conjTranspose_mul (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitFlipUnitary p)ᴴ * bitFlipUnitary p = 1 := by
  rw [bitFlipUnitary, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc controlledFlipᴴ, controlledFlip_conjTranspose_mul, Matrix.one_mul,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul, flipRotation_conjTranspose_mul p hp0 hp1, Matrix.one_kronecker_one]

/-- The environment blocks of `U_p · (· ⊗ |0⟩)` are the bit-flip Kraus operators
`{√(1−p) I, √p X}`. -/
theorem krausBlock_bitFlipUnitary_embedEnv (p : ℝ) (i : Fin 2) :
    krausBlock (bitFlipUnitary p * CSD.LF2.embedEnv (Fin 2) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))) i
      = (Real.sqrt (![1 - p, p] i) : ℂ) • (![1, pX] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) i := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [krausBlock_apply, bitFlipUnitary, controlledFlip, flipRotation, pX, CSD.LF2.embedEnv_apply,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, PiLp.single_apply]

/-- ★ **The bit-flip channel is the Stinespring channel of `U_p` with a ready environment**, as
channels (equal Kraus families). -/
theorem stinespringChannel_bitFlipUnitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    CSD.LF2.stinespringChannel (bitFlipUnitary p) (bitFlipUnitary_conjTranspose_mul p hp0 hp1)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
      = bitFlipChannel p hp0 hp1 := by
  have hk : (CSD.LF2.stinespringChannel (bitFlipUnitary p) (bitFlipUnitary_conjTranspose_mul p hp0 hp1)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)).kraus
      = (bitFlipChannel p hp0 hp1).kraus := by
    funext i
    exact krausBlock_bitFlipUnitary_embedEnv p i
  cases h : CSD.LF2.stinespringChannel (bitFlipUnitary p) (bitFlipUnitary_conjTranspose_mul p hp0 hp1)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
  cases h' : bitFlipChannel p hp0 hp1
  rw [h] at hk; rw [h'] at hk
  simp only at hk
  subst hk
  rfl

end CSD.Empirical.QM.QEC
