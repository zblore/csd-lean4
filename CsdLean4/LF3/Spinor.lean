/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Setup

/-!
# LF3/Spinor: the detector-axis spinors

**Category:** 3-Local (the local eigenbasis of `σ·a`).

## Why this exists

`SingletDeisolationFlow.nudgedSinglet` was documented as the singlet "transformed
by local basis rotations". **That description is false**, and the repository's own
proof shows why: inside `singletJointEig_born`,

    inner ℂ singlet (singletJointEig s t a b) = (Real.sqrt (P_st a b s t) : ℂ)

so `nudgedSinglet a b` is the vector `(√P_st)_{s,t}` — all real, all
non-negative, **every phase stripped**. Local unitaries preserve Schmidt spectra
and `ψ⁻` is maximally entangled, so a local-unitary image of `ψ⁻` is maximally
entangled; but at `a ⊥ b` all four `P_st = ¼`, making `nudgedSinglet = ½(1,1,1,1)`
a **product state**. No local unitary does that.

The defect is in `singletJointEig := (√P_st)⁻¹ • (Πˢ(a) ⊗ Πᵗ(b)) ψ⁻`, which fixes
each basis vector's phase by projecting `ψ⁻` itself: four independent phases,
where a product unitary supplies only separable ones (`αₛ + βₜ`).

This module builds the **local eigenbasis** that a genuine nudge-locality
statement needs. It sits in LF3 because every object here (`DetectorSetting`,
`spinProj`, `pauliDot`) is LF3's; the nudge theorem that consumes it belongs in
LF6. Nothing here depends on the old definition, and nothing here is claimed of
it.

## Contents

* `spinor s a` — the unit `s`-eigenvector of `σ·a`, defined by an explicit
  formula with a single case split at the pole `1 + s·a_z = 0` (where the
  eigenvector collapses to a basis vector).
* `spinor_normSq` — the spinor is a unit vector.
* ★★ `spinProj_eq_outer` — the projector **is** its outer product. This is what
  carries the Born identity downstream: it gives
  `Πˢ(a) ⊗ Πᵗ(b) = (u ⊗ w)(u ⊗ w)ᴴ`, hence
  `⟨ψ⁻, (Πˢ ⊗ Πᵗ) ψ⁻⟩ = |⟨u ⊗ w, ψ⁻⟩|²`.

## References

`LF3/Setup.lean` (`spinProj`, `pauliDot`, `DetectorSetting`);
`LF6/SingletDeisolationFlow.lean` (the object this replaces);
`specs/c1-correction-plan.md` §3b.
-/

@[expose] public section

open Matrix Complex

namespace CSD.LF3

/-! ### Preliminaries -/

lemma sign_sq (s : Sign) : (s.val : ℝ) ^ 2 = 1 := by
  cases s <;> norm_num [Sign.val]

lemma sign_ne_zero (s : Sign) : (s.val : ℝ) ≠ 0 := by
  cases s <;> norm_num [Sign.val]

/-- The `z`-component is bounded by one, from `‖a‖ = 1`. -/
lemma abs_vec_two_le_one (a : DetectorSetting) : |(a.vec 2 : ℝ)| ≤ 1 := by
  have h := a.sum_sq_components_eq_one
  nlinarith [sq_nonneg (a.vec 0), sq_nonneg (a.vec 1), sq_abs (a.vec 2),
    abs_nonneg (a.vec 2)]

/-- At the pole the transverse components vanish. -/
lemma transverse_eq_zero_of_pole (s : Sign) (a : DetectorSetting)
    (h : 1 + (s.val : ℝ) * (a.vec 2 : ℝ) = 0) :
    (a.vec 0 : ℝ) = 0 ∧ (a.vec 1 : ℝ) = 0 := by
  have hsum := a.sum_sq_components_eq_one
  have hs := sign_sq s
  have hz : (a.vec 2 : ℝ) ^ 2 = 1 := by nlinarith [h, hs]
  constructor <;> nlinarith [sq_nonneg (a.vec 0), sq_nonneg (a.vec 1)]

/-! ### The detector-axis spinor -/

/-- The **unnormalised** `s`-eigenvector of `σ·a`: the first column of `Πˢ(a)`
scaled by `2`. Its squared norm is `2(1 + s·a_z)`, so it is nonzero exactly away
from the pole. -/
noncomputable def spinorRaw (s : Sign) (a : DetectorSetting) : Fin 2 → ℂ :=
  ![(((1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ),
    (s.val : ℂ) * ((((a.vec 0 : ℝ)) : ℂ) + Complex.I * (((a.vec 1 : ℝ)) : ℂ))]

@[simp] lemma spinorRaw_zero (s : Sign) (a : DetectorSetting) :
    spinorRaw s a 0 = (((1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) := rfl

@[simp] lemma spinorRaw_one (s : Sign) (a : DetectorSetting) :
    spinorRaw s a 1
      = (s.val : ℂ) * ((((a.vec 0 : ℝ)) : ℂ) + Complex.I * (((a.vec 1 : ℝ)) : ℂ)) := rfl

@[simp] lemma star_spinorRaw_zero (s : Sign) (a : DetectorSetting) :
    star (spinorRaw s a 0) = (((1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) := by
  rw [spinorRaw_zero, RCLike.star_def, Complex.conj_ofReal]

@[simp] lemma star_spinorRaw_one (s : Sign) (a : DetectorSetting) :
    star (spinorRaw s a 1)
      = (s.val : ℂ) * ((((a.vec 0 : ℝ)) : ℂ) - Complex.I * (((a.vec 1 : ℝ)) : ℂ)) := by
  rw [spinorRaw_one, RCLike.star_def, map_mul, map_add, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

/-- The unit-vector relation, as a complex identity. -/
lemma sum_sq_components_eq_one_C (a : DetectorSetting) :
    ((a.vec 0 : ℝ) : ℂ) ^ 2 + ((a.vec 1 : ℝ) : ℂ) ^ 2 + ((a.vec 2 : ℝ) : ℂ) ^ 2 = 1 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, ← Complex.ofReal_add, a.sum_sq_components_eq_one,
    Complex.ofReal_one]

lemma sign_sq_C (s : Sign) : ((s.val : ℝ) : ℂ) ^ 2 = 1 := by
  rw [← Complex.ofReal_pow, sign_sq, Complex.ofReal_one]

/-- ★ **The division-free outer-product identity.**
`2(1 + s·a_z) · Πˢ(a)ᵢⱼ = rawᵢ · conj(rawⱼ)`. Away from the pole, dividing by the
positive scalar gives `Πˢ(a) = u uᴴ`. -/
lemma two_mul_spinProj_eq_raw_outer (s : Sign) (a : DetectorSetting) (i j : Fin 2) :
    ((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) * spinProj s a i j
      = spinorRaw s a i * star (spinorRaw s a j) := by
  have hsumC := sum_sq_components_eq_one_C a
  have hsC := sign_sq_C s
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, spinorRaw_zero, spinorRaw_one, spinProj, pauliDot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul, RCLike.star_def, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I] <;>
    push_cast
  · ring
  · ring
  · ring
  · linear_combination (-((s.val : ℝ) : ℂ) ^ 2) * hsumC - hsC
      + (((s.val : ℝ) : ℂ) ^ 2 * (((a.vec 1 : ℝ)) : ℂ) ^ 2) * Complex.I_sq

/-- The unnormalised spinor's squared norm. -/
lemma spinorRaw_normSq (s : Sign) (a : DetectorSetting) :
    ‖spinorRaw s a 0‖ ^ 2 + ‖spinorRaw s a 1‖ ^ 2
      = 2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) := by
  have hsum := a.sum_sq_components_eq_one
  have hs := sign_sq s
  simp only [spinorRaw, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_mul, mul_pow,
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  nlinarith [hsum, hs]

/-- **The unit `s`-eigenvector of `σ·a`.** Away from the pole it is `spinorRaw`
normalised; at the pole (`1 + s·a_z = 0`, forcing `a = -s·ẑ`) that vector
vanishes and `Πˢ(a) = diag(0,1)`, so the eigenvector is `e₁`. -/
noncomputable def spinor (s : Sign) (a : DetectorSetting) : Fin 2 → ℂ :=
  if 0 < 1 + (s.val : ℝ) * (a.vec 2 : ℝ) then
    ((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ)⁻¹ • spinorRaw s a
  else ![0, 1]

/-- At the pole, the transverse components vanish and `s·a_z = -1`. -/
lemma pole_facts (s : Sign) (a : DetectorSetting)
    (hpos : ¬ (0 < 1 + (s.val : ℝ) * (a.vec 2 : ℝ))) :
    (a.vec 0 : ℝ) = 0 ∧ (a.vec 1 : ℝ) = 0 ∧ (s.val : ℝ) * (a.vec 2 : ℝ) = -1 := by
  have hb := abs_vec_two_le_one a
  have hs := sign_sq s
  have hzero : 1 + (s.val : ℝ) * (a.vec 2 : ℝ) = 0 := by
    rcases abs_le.mp hb with ⟨h1, h2⟩
    cases s <;> simp only [Sign.val] at * <;> linarith
  obtain ⟨hx, hy⟩ := transverse_eq_zero_of_pole s a hzero
  exact ⟨hx, hy, by linarith⟩

/-! ### The spinor is a unit vector, and the projector is its outer product -/

/-- The spinor has unit norm, in both branches. -/
lemma spinor_normSq (s : Sign) (a : DetectorSetting) :
    ‖spinor s a 0‖ ^ 2 + ‖spinor s a 1‖ ^ 2 = 1 := by
  unfold spinor
  by_cases hpos : 0 < 1 + (s.val : ℝ) * (a.vec 2 : ℝ)
  · rw [if_pos hpos]
    have hraw := spinorRaw_normSq s a
    have hNpos : 0 < Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) :=
      Real.sqrt_pos.mpr (by linarith)
    have hN2 : (Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)))) ^ 2
        = 2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) := Real.sq_sqrt (by linarith)
    have hexp : ∀ i : Fin 2,
        ‖(((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ)⁻¹ • spinorRaw s a) i‖ ^ 2
          = (Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))))⁻¹ ^ 2 * ‖spinorRaw s a i‖ ^ 2 := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hNpos]
    rw [hexp 0, hexp 1, ← mul_add, hraw, inv_pow, hN2]
    field_simp
  · rw [if_neg hpos]
    simp

/-- ★★ **The projector is the spinor's outer product**: `Πˢ(a) = u uᴴ`.

This is the lemma that carries the Born identity downstream: it gives
`Πˢ(a) ⊗ Πᵗ(b) = (u ⊗ w)(u ⊗ w)ᴴ`, hence
`⟨ψ⁻, (Πˢ ⊗ Πᵗ) ψ⁻⟩ = |⟨u ⊗ w, ψ⁻⟩|²`. -/
lemma spinProj_eq_outer (s : Sign) (a : DetectorSetting) (i j : Fin 2) :
    spinProj s a i j = spinor s a i * star (spinor s a j) := by
  unfold spinor
  by_cases hpos : 0 < 1 + (s.val : ℝ) * (a.vec 2 : ℝ)
  · rw [if_pos hpos]
    have hNpos : 0 < Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) :=
      Real.sqrt_pos.mpr (by linarith)
    have hNne : ((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hNpos
    have hN2 : ((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ)
        * ((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ)
        = ((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hN2sq : ((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ) ^ 2
        = ((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) := by
      rw [sq]; exact hN2
    have hkey := two_mul_spinProj_eq_raw_outer s a i j
    simp only [RCLike.star_def] at hkey ⊢
    have hDne : ((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      intro h; linarith
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_inv₀,
      Complex.conj_ofReal]
    calc spinProj s a i j
        = ((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ)⁻¹
            * (((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ) * spinProj s a i j) := by
          rw [inv_mul_cancel_left₀ hDne]
      _ = ((2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ)) : ℝ) : ℂ)⁻¹
            * (spinorRaw s a i * (starRingEnd ℂ) (spinorRaw s a j)) := by rw [hkey]
      _ = (((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ)⁻¹ * spinorRaw s a i)
            * (((Real.sqrt (2 * (1 + (s.val : ℝ) * (a.vec 2 : ℝ))) : ℝ) : ℂ)⁻¹
              * (starRingEnd ℂ) (spinorRaw s a j)) := by
          rw [← hN2sq, sq, mul_inv]; ring
  · rw [if_neg hpos]
    obtain ⟨hx, hy, hz⟩ := pole_facts s a hpos
    have hzC : ((s.val : ℝ) : ℂ) * ((a.vec 2 : ℝ) : ℂ) = -1 := by
      rw [← Complex.ofReal_mul, hz]
      norm_num
    fin_cases i <;> fin_cases j <;>
      simp [spinProj, pauliDot, Matrix.cons_val_zero, Matrix.cons_val_one, hx, hy, hzC]
    all_goals norm_num


/-! ### The wing basis unitary

The two spinors are the columns of a unitary. Completeness of the spin
projectors gives `U Uᴴ = 1` in one step, with no orthogonality argument:
`(U Uᴴ)ᵢⱼ = Σₛ (u_s)ᵢ conj((u_s)ⱼ) = Σₛ Πˢ(a)ᵢⱼ = δᵢⱼ`. -/

/-- The two signs, indexed by `Fin 2`. -/
def signOfFin : Fin 2 → Sign := ![Sign.plus, Sign.minus]

@[simp] lemma signOfFin_zero : signOfFin 0 = Sign.plus := rfl
@[simp] lemma signOfFin_one : signOfFin 1 = Sign.minus := rfl

/-- **Completeness of the spin projectors**: `Π⁺(a) + Π⁻(a) = 1`. -/
theorem spinProj_add_eq_one (a : DetectorSetting) :
    spinProj Sign.plus a + spinProj Sign.minus a = 1 := by
  simp only [spinProj, Sign.val]
  rw [← smul_add]
  norm_num
  module

/-- Summing the projectors over both signs. -/
lemma sum_spinProj (a : DetectorSetting) (i j : Fin 2) :
    ∑ k : Fin 2, spinProj (signOfFin k) a i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  rw [Fin.sum_univ_two, signOfFin_zero, signOfFin_one]
  have := spinProj_add_eq_one a
  calc spinProj Sign.plus a i j + spinProj Sign.minus a i j
      = (spinProj Sign.plus a + spinProj Sign.minus a) i j := by
        rw [Matrix.add_apply]
    _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by rw [this]

/-- **The wing basis unitary.** Columns are the two detector-axis spinors, so
conjugating by it is the change of basis into the `σ·a` eigenbasis. -/
noncomputable def wingBasisUnitary (a : DetectorSetting) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i k => spinor (signOfFin k) a i

/-- ★★ **The wing basis matrix is unitary.** -/
theorem wingBasisUnitary_mem_unitaryGroup (a : DetectorSetting) :
    wingBasisUnitary a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstep : ∀ k : Fin 2,
      wingBasisUnitary a i k * (star (wingBasisUnitary a)) k j
        = spinProj (signOfFin k) a i j := by
    intro k
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, wingBasisUnitary,
      Matrix.of_apply, Matrix.of_apply, spinProj_eq_outer (signOfFin k) a i j]
  rw [Finset.sum_congr rfl (fun k _ => hstep k), sum_spinProj a i j, Matrix.one_apply]

/-- The wing basis unitary, as an element of the unitary group. -/
noncomputable def wingBasisU (a : DetectorSetting) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨wingBasisUnitary a, wingBasisUnitary_mem_unitaryGroup a⟩

@[simp] lemma wingBasisU_val (a : DetectorSetting) :
    (wingBasisU a : Matrix (Fin 2) (Fin 2) ℂ) = wingBasisUnitary a := rfl



/-! ### The two-qubit product spinor -/

/-- The product spinor `u_s(a) ⊗ w_t(b)` on the two-qubit space. -/
noncomputable def spinorPair (s t : Sign) (a b : DetectorSetting) : Fin 2 × Fin 2 → ℂ :=
  fun p => spinor s a p.1 * spinor t b p.2

/-- ★★ **The joint projector is the outer product of the product spinor**:
`Πˢ(a) ⊗ Πᵗ(b) = (u ⊗ w)(u ⊗ w)ᴴ`. -/
lemma jointSpinProj_eq_outer (s t : Sign) (a b : DetectorSetting) (I J : Fin 2 × Fin 2) :
    jointSpinProj s t a b I J = spinorPair s t a b I * star (spinorPair s t a b J) := by
  obtain ⟨i1, i2⟩ := I
  obtain ⟨j1, j2⟩ := J
  simp only [jointSpinProj, Matrix.kroneckerMap_apply, spinorPair,
    spinProj_eq_outer, star_mul']
  ring


end CSD.LF3
