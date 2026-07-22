/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Singlet.Kernel

/-!
# LF3 Singlet / JointProjector: joint spin projector algebra + the Born expectation identity

**Category:** 3-Local (LF4 §3 discharge groundwork — the reusable physics
behind `MeasurementJointEig.born_eq_P_st`).

This module supplies the matrix-level facts about the joint two-qubit spin
projector `jointSpinProj s t a b = Πˢ(a) ⊗ Πᵗ(b)` that LF4 needs to construct
*genuine* joint spin eigenstates (rather than the closed-form `cAmp = √P_st`
placeholder of `Kernel.lean`):

- `jointSpinProj_isHermitian` — Hermitian (Kronecker of Hermitian projectors).
- `jointSpinProj_idem` — idempotent (mixed-product property + `spinProj_idem`).
- `spinProj_mul_orthogonal` / `jointSpinProj_mul_orthogonal` — distinct sectors
  multiply to zero (mutual orthogonality of the four joint projectors).
- **`singlet_jointSpinProj_expectation`** — the Born identity at the projector
  level: `⟨ψ⁻ | Πˢ(a)⊗Πᵗ(b) | ψ⁻⟩ = P_st a b s t = (1 − st·a·b)/4`. Proved by
  the same entry-evaluation technique as `singlet_pauli_correlation`.

The LF4 eigenstate `eig s t := (√P_st)⁻¹ • (jointSpinProj s t · ψ⁻)` is the
normalised projection of the singlet onto the sector; combined with the
expectation identity and Hermitian-idempotence it yields
`‖⟨ψ⁻, eig s t⟩‖² = P_st` and `‖eig s t‖ = 1`. That construction (and the
`Fin 2 × Fin 2 → Fin N` re-indexing) lives in the LF4 layer; this module is
the context-independent physics it consumes.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Matrix Kronecker

namespace CSD
namespace LF3

/-! ### Joint spin projector as a Kronecker product -/

/-- `jointSpinProj` is the Kronecker product of the two one-qubit spin
    projectors. (Definitional; restated for `⊗ₖ`-rewriting.) -/
lemma jointSpinProj_eq_kronecker (s t : Sign) (a b : DetectorSetting) :
    jointSpinProj s t a b = (spinProj s a) ⊗ₖ (spinProj t b) := rfl

/-- The joint spin projector is Hermitian. -/
theorem jointSpinProj_isHermitian (s t : Sign) (a b : DetectorSetting) :
    (jointSpinProj s t a b).IsHermitian := by
  apply Matrix.ext
  rintro ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [jointSpinProj, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, star_mul']
  rw [← Matrix.conjTranspose_apply (spinProj s a),
      ← Matrix.conjTranspose_apply (spinProj t b),
      spinProj_isHermitian s a, spinProj_isHermitian t b]

/-- The joint spin projector is idempotent: `(Πˢ⊗Πᵗ)² = Πˢ⊗Πᵗ`. -/
theorem jointSpinProj_idem (s t : Sign) (a b : DetectorSetting) :
    jointSpinProj s t a b * jointSpinProj s t a b = jointSpinProj s t a b := by
  rw [jointSpinProj_eq_kronecker, ← Matrix.mul_kronecker_mul,
      spinProj_idem s a, spinProj_idem t b]

/-- One-qubit spin projectors at **distinct** signs are mutually orthogonal:
    `Πˢ(a) · Πˢ'(a) = 0` when `s ≠ s'`. Expand
    `(1/4)(1 + sσ)(1 + s'σ) = (1/4)(1 + (s+s')σ + ss'·σ²)`; for `s ≠ s'`,
    `s + s' = 0` and `ss' = -1`, so it collapses to `(1/4)(1 - 1) = 0`. -/
theorem spinProj_mul_orthogonal {s s' : Sign} (a : DetectorSetting) (h : s ≠ s') :
    spinProj s a * spinProj s' a = 0 := by
  -- For distinct signs, `s.val + s'.val = 0` and `s.val * s'.val = -1`.
  have hsum : ((s.val : ℝ) : ℂ) + ((s'.val : ℝ) : ℂ) = 0 := by
    cases s <;> cases s' <;> simp_all [Sign.val]
  have hprod : ((s.val : ℝ) : ℂ) * ((s'.val : ℝ) : ℂ) = -1 := by
    cases s <;> cases s' <;> simp_all [Sign.val]
  unfold spinProj
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliDot_sq, hprod]
  -- Goal: (1/2*1/2) • (1 + s'•σ + (s•σ + (-1)•1)) = 0; the bracket is
  -- `(s.val + s'.val) • σ = 0` (using `hsum`), and `1 + (-1)•1 = 0`.
  have hzero : (((s.val : ℝ) : ℂ) + ((s'.val : ℝ) : ℂ)) • pauliDot a = 0 := by
    rw [hsum, zero_smul]
  rw [show ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((s'.val : ℝ) : ℂ) • pauliDot a
        + (((s.val : ℝ) : ℂ) • pauliDot a + (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
      = (((s.val : ℝ) : ℂ) + ((s'.val : ℝ) : ℂ)) • pauliDot a from by module]
  rw [hzero, smul_zero]

/-- The four joint spin projectors are mutually orthogonal: for distinct
    sectors `(s, t) ≠ (s', t')`, `(Πˢ(a)⊗Πᵗ(b))·(Πˢ'(a)⊗Πᵗ'(b)) = 0`. -/
theorem jointSpinProj_mul_orthogonal {s t s' t' : Sign} (a b : DetectorSetting)
    (h : (s, t) ≠ (s', t')) :
    jointSpinProj s t a b * jointSpinProj s' t' a b = 0 := by
  rw [jointSpinProj_eq_kronecker, jointSpinProj_eq_kronecker,
      ← Matrix.mul_kronecker_mul]
  have hor : s ≠ s' ∨ t ≠ t' := by
    by_contra hc
    push Not at hc
    exact h (Prod.ext hc.1 hc.2)
  rcases hor with hs | ht
  · rw [spinProj_mul_orthogonal a hs, Matrix.zero_kronecker]
  · rw [spinProj_mul_orthogonal b ht, Matrix.kronecker_zero]

/-! ### One-qubit spin projector entries -/

/-- `Πˢ(a) 0 0 = (1 + s·a_z)/2`. -/
lemma spinProj_apply_00 (s : Sign) (a : DetectorSetting) :
    spinProj s a 0 0 = (1 / 2 : ℂ) * (1 + (s.val : ℂ) * ((a.vec 2 : ℝ) : ℂ)) := by
  simp only [spinProj, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq,
             smul_eq_mul, pauliDot_apply_00]

/-- `Πˢ(a) 0 1 = s·(a_x − i a_y)/2`. -/
lemma spinProj_apply_01 (s : Sign) (a : DetectorSetting) :
    spinProj s a 0 1
      = (1 / 2 : ℂ) * ((s.val : ℂ) * (((a.vec 0 : ℝ) : ℂ) - Complex.I * ((a.vec 1 : ℝ) : ℂ))) := by
  simp only [spinProj, Matrix.smul_apply, Matrix.add_apply,
             Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
             smul_eq_mul, pauliDot_apply_01]
  ring

/-- `Πˢ(a) 1 0 = s·(a_x + i a_y)/2`. -/
lemma spinProj_apply_10 (s : Sign) (a : DetectorSetting) :
    spinProj s a 1 0
      = (1 / 2 : ℂ) * ((s.val : ℂ) * (((a.vec 0 : ℝ) : ℂ) + Complex.I * ((a.vec 1 : ℝ) : ℂ))) := by
  simp only [spinProj, Matrix.smul_apply, Matrix.add_apply,
             Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
             smul_eq_mul, pauliDot_apply_10]
  ring

/-- `Πˢ(a) 1 1 = (1 − s·a_z)/2`. -/
lemma spinProj_apply_11 (s : Sign) (a : DetectorSetting) :
    spinProj s a 1 1 = (1 / 2 : ℂ) * (1 - (s.val : ℂ) * ((a.vec 2 : ℝ) : ℂ)) := by
  simp only [spinProj, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq,
             smul_eq_mul, pauliDot_apply_11]
  ring

/-! ### The Born expectation identity -/

/-- **Born identity at the projector level.**
    `⟨ψ⁻ | Πˢ(a) ⊗ Πᵗ(b) | ψ⁻⟩ = P_st a b s t = (1 − st·a·b)/4`.

    This is the genuine spin computation underlying `MeasurementJointEig`'s
    `born_eq_P_st` field: it expresses the singlet expectation of the joint
    spin projector as the closed-form kernel `P_st`. Proved by reducing the
    expectation to the four-entry half-sum (`expectation_formula`), evaluating
    the joint-projector entries as products of one-qubit-projector entries
    (`Matrix.kroneckerMap_apply` + `spinProj_apply_*`), and simplifying with
    `Complex.I_sq` exactly as in `singlet_pauli_correlation`. -/
theorem singlet_jointSpinProj_expectation (s t : Sign) (a b : DetectorSetting) :
    expectation (jointSpinProj s t a b) = (P_st a b s t : ℂ) := by
  rw [expectation_formula]
  show (1 / 2 : ℂ) *
      (jointSpinProj s t a b (0, 1) (0, 1) - jointSpinProj s t a b (0, 1) (1, 0)
        - jointSpinProj s t a b (1, 0) (0, 1) + jointSpinProj s t a b (1, 0) (1, 0)) = _
  simp only [jointSpinProj, Matrix.kroneckerMap_apply,
             spinProj_apply_00, spinProj_apply_01, spinProj_apply_10, spinProj_apply_11]
  rw [P_st, dotR]
  push_cast
  ring_nf
  rw [show (Complex.I ^ 2 : ℂ) = -1 from Complex.I_sq]
  ring

end LF3
end CSD
