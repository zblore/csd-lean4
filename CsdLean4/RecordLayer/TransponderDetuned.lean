/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderRabi

/-!
# Levels of different energy: the second level fills as `(|g|/Ω) |sin (Ω t)|`

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2), the caused return, for
a transponder whose two levels have different energies).

Every lower bound on what the meeting launches (UD-253 to UD-259) takes one energy for both
levels of the transponder. Then the level swap commutes with the free Hamiltonian and the
contributions of successive times add in phase. With energies `E₀ ≠ E₁` they do not. Here
the contact term with the gate removed is solved again: with `δ = (E₁ − E₀)/2` and
`Ω² = g² + δ²`,

  `E₀ P₀ + E₁ P₁ + g X = ((E₀ + E₁)/2) · 1 + Ω W`,   `W = (δ/Ω) (P₁ − P₀) + (g/Ω) X`,

and `W` is a Hermitian involution. So the orbit turns about `W` at the rate `Ω`, and the part
in the second level is `(|g|/Ω) |sin (Ω t)|` of the state, exactly, while the carriers are in
contact. **The detuning caps the launched amplitude at `|g|/Ω`**; for `|δ| ≫ |g|` that is
about `|g|/|δ|`. This is the phase cancellation, as an equality with an error term.

* ★★★ `norm_exp_sub_rabi_add_mul_le` — `H_c`, `W` Hermitian, `W² = 1`, `W` commuting with
  `H_c`; a Hermitian `V = c S₁ P'` with `‖S₁‖ ≤ 1` and `P'` commuting with `W`: the orbit of
  `X` under `H_c + Ω W + V` is `e^{−itH_c} (cos (Ω t) − i sin (Ω t) W) X` within
  `|c| ∫₀ᵗ ‖P' e^{−isH_c} X‖ ds`;
* `detunedAxis`, `levelProj_isHermitian`, `levelProj_zero_mul_levelSwap`,
  `detunedAxis_isHermitian`, ★ `detunedAxis_mul_self`, `detunedAxis_apply_of_ne`,
  `detunedAxis_mul_blockDiagonal_smul_one`, `blockDiagonal_smul_one_eq_add`;
* ★★★ `transponder_detuned_second_level` — the contact term of UA-19, `X` with the
  transponder in its first level: the part in the second level has norm within
  `|g| ∫₀ᵗ ‖P' e^{−isH_c} X‖ ds` of `(|g|/Ω) |sin (Ω t)| ‖X‖`;
* ★★★ `transponder_detuned_flatPacket` — **the flat packet in contact with a transponder at
  rest with level energies `E₀`, `E₁`: the second level's amplitude at `t` is within
  `|g| √(flatTailD t) · t` of `(|g|/Ω) |sin (Ω t)|`**;
* ★★ `transponder_detuned_flatPacket_le` — so it is at most `|g|/Ω + |g| √(flatTailD t) · t`.

## Honest scope

⚠️ **Contact from the flow time `0`.** As in UD-258, the error counts the amplitude "apart"
over the whole of `[0, t]`. A run that starts apart (the two-stage comparison of UD-259) is
not redone for levels of different energy.

⚠️ **The cap holds while the carriers are wholly in contact**, within the error. It is not a
bound over a whole passage: while the packet's box is only partly on the transponder's
sites nothing is shown here.

⚠️ **The reference orbit is that of the mean energy** `(E₀ + E₁)/2` for both levels; for a
state in the first level it differs from the free orbit by a phase.

⚠️ **The amplitude, not its place.** No pointer, no arena, no reading. `Ω > 0` is a
hypothesis, with `Ω² = g² + δ²`; `Ω = √(g² + δ²)` meets it unless `g = 0` and `E₀ = E₁`.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-258, UD-262); `RecordLayer/TransponderRabi.lean` (`exp_neg_I_add_smul_of_commute_invol`,
`norm_exp_sub_rabi_mul_le`, `norm_rabi_le_one`, `rabi_commute`,
`levelProj_one_mul_freeOrbit`, `levelProj_one_mul_swap_freeOrbit`,
`norm_le_norm_swap_freeOrbit`, `transponder_rabi_flatPacket_ge`);
`Mathlib/Analysis/Matrix/DuhamelState.lean` (`Matrix.norm_exp_neg_I_add_sub_mul_le`);
`RecordLayer/TransponderMeetingPacket.lean`
(`norm_coincProj_freeOrbit_flatPacket_resting_le`); `CV/DetunedExchange.lean` (the detuned
exchange of two sites, a different carrier); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The comparison with a turning reference orbit -/

section Compare

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- ★★★ **A perturbation of a solved turning orbit.** `H_c` and `W` are Hermitian, `W² = 1`,
`W` commutes with `H_c`; `V` is Hermitian, `V = c S₁ P'` with `‖S₁‖ ≤ 1` and `P'` commuting
with `W`. For a real `Ω` and `t ≥ 0` the orbit of `X` under `H_c + Ω W + V` is
`e^{−itH_c} (cos (Ω t) − i sin (Ω t) W) X` within `|c| ∫₀ᵗ ‖P' e^{−isH_c} X‖ ds`. -/
theorem norm_exp_sub_rabi_add_mul_le (Hc W S₁ P' V X : Matrix m m ℂ) (Ω c : ℝ)
    (hH : Hc.IsHermitian) (hWh : W.IsHermitian) (hWW : W * W = 1) (hWH : W * Hc = Hc * W)
    (hV : V.IsHermitian) (hVf : V = (c : ℂ) • (S₁ * P')) (hS₁ : ‖S₁‖ ≤ 1)
    (hP'W : P' * W = W * P') {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (Hc + (Ω : ℂ) • W + V)))
        - exp (t • ((-Complex.I) • Hc))
          * (Complex.cos ((Ω * t : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((Ω * t : ℝ) : ℂ)) • W)) * X‖
      ≤ |c| * ∫ s in (0 : ℝ)..t, ‖P' * exp (s • ((-Complex.I) • Hc)) * X‖ := by
  have hΩW : ((Ω : ℂ) • W).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hWh.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hH' : (Hc + (Ω : ℂ) • W).IsHermitian := hH.add hΩW
  have h := Matrix.norm_exp_neg_I_add_sub_mul_le (Hc + (Ω : ℂ) • W) V X hH' hV ht
  rw [exp_neg_I_add_smul_of_commute_invol hWH hWW Ω t] at h
  refine h.trans ?_
  have hWA : W * ((-Complex.I) • Hc) = ((-Complex.I) • Hc) * W := by
    rw [mul_smul_comm, smul_mul_assoc, hWH]
  have hpt : ∀ s : ℝ,
      ‖V * exp (s • ((-Complex.I) • (Hc + (Ω : ℂ) • W))) * X‖
        ≤ |c| * ‖P' * exp (s • ((-Complex.I) • Hc)) * X‖ := fun s => by
    have hWU := Matrix.mul_exp_smul_eq_of_commute hWA s
    have hMW : (P' * exp (s • ((-Complex.I) • Hc))) * W
        = W * (P' * exp (s • ((-Complex.I) • Hc))) := by
      rw [mul_assoc, ← hWU, ← mul_assoc, hP'W, mul_assoc]
    have hMR := rabi_commute hMW (Complex.cos ((Ω * s : ℝ) : ℂ))
      (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ))
    have e1 : S₁ * P' * (exp (s • ((-Complex.I) • Hc))
          * (Complex.cos ((Ω * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)) • W)) * X
        = S₁ * ((Complex.cos ((Ω * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)) • W)
          * (P' * exp (s • ((-Complex.I) • Hc)) * X)) := by
      calc S₁ * P' * (exp (s • ((-Complex.I) • Hc))
            * (Complex.cos ((Ω * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
              - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)) • W)) * X
          = S₁ * ((P' * exp (s • ((-Complex.I) • Hc)))
            * (Complex.cos ((Ω * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
              - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)) • W)) * X := by
            simp only [mul_assoc]
        _ = S₁ * ((Complex.cos ((Ω * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
              - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)) • W)
            * (P' * exp (s • ((-Complex.I) • Hc)))) * X := by rw [hMR]
        _ = _ := by simp only [mul_assoc]
    rw [exp_neg_I_add_smul_of_commute_invol hWH hWW Ω s, hVf, smul_mul_assoc, smul_mul_assoc,
      e1, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hS₁).trans ?_)
    exact (norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_rabi_le_one hWh hWW (Ω * s)))
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on ht
    ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
    ((continuous_const.mul
      (Matrix.continuous_norm_mul_exp_smul_mul _ P' X)).intervalIntegrable _ _)
    fun s _ => hpt s

end Compare

/-! ### The axis the two levels turn about -/

section Axis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The axis of the detuned contact term**, on the transponder's levels:
`a (P₁ − P₀) + b X`, with `P_l` the level projectors and `X` the level swap. -/
def detunedAxis (n : Type*) [DecidableEq n] (a b : ℝ) : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
  (a : ℂ) • (levelProj n 1 - levelProj n 0) + (b : ℂ) • levelSwap n

omit [Fintype n] in
/-- A level projector is Hermitian. -/
theorem levelProj_isHermitian (l : Fin 2) : (levelProj n l).IsHermitian := by
  rw [levelProj, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases hp : p.2 = l <;> simp [hp]

/-- The first level's projector passes the swap as the second's. -/
theorem levelProj_zero_mul_levelSwap :
    levelProj n 0 * levelSwap n = levelSwap n * levelProj n 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [levelProj, levelSwap, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp

omit [Fintype n] in
/-- The axis is Hermitian. -/
theorem detunedAxis_isHermitian (a b : ℝ) : (detunedAxis n a b).IsHermitian := by
  have hsm : ∀ (c : ℝ) {M : Matrix (n × Fin 2) (n × Fin 2) ℂ}, M.IsHermitian →
      ((c : ℂ) • M).IsHermitian := fun c {M} hM => by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM.eq, Complex.star_def,
      Complex.conj_ofReal]
  exact (hsm a ((levelProj_isHermitian 1).sub (levelProj_isHermitian 0))).add
    (hsm b (levelSwap_isHermitian n))

/-- ★ **The axis squares to `a² + b²`.** -/
theorem detunedAxis_mul_self (a b : ℝ) :
    detunedAxis n a b * detunedAxis n a b
      = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) • (1 : Matrix (n × Fin 2) (n × Fin 2) ℂ) := by
  have hZd : levelProj n 1 - levelProj n 0
      = Matrix.diagonal fun x : n × Fin 2 => if x.2 = 1 then (1 : ℂ) else -1 := by
    rw [levelProj, levelProj, Matrix.diagonal_sub]
    congr 1
    funext x
    obtain ⟨p, i⟩ := x
    fin_cases i <;> simp
  have hZZ : (levelProj n 1 - levelProj n 0) * (levelProj n 1 - levelProj n 0) = 1 := by
    rw [hZd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    split_ifs <;> simp
  have hZX : (levelProj n 1 - levelProj n 0) * levelSwap n
      = -(levelSwap n * (levelProj n 1 - levelProj n 0)) := by
    rw [sub_mul, mul_sub, levelProj_one_mul_levelSwap, levelProj_zero_mul_levelSwap, neg_sub]
  have hXX := levelSwap_mul_self (n := n)
  unfold detunedAxis
  generalize levelProj n 1 - levelProj n 0 = Z at hZZ hZX ⊢
  generalize levelSwap n = Xs at hZX hXX ⊢
  have e : ((a : ℂ) • Z + (b : ℂ) • Xs) * ((a : ℂ) • Z + (b : ℂ) • Xs)
      = ((a : ℂ) * a) • (Z * Z) + ((a : ℂ) * b) • (Z * Xs) + ((b : ℂ) * a) • (Xs * Z)
        + ((b : ℂ) * b) • (Xs * Xs) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  rw [e, hZZ, hZX, hXX]
  push_cast
  module

omit [Fintype n] in
/-- The axis has no entry between two transponder states at different sites. -/
theorem detunedAxis_apply_of_ne {S : Type*} (τ : n × Fin 2 → S)
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0) (a b : ℝ) :
    ∀ i j, τ i ≠ τ j → detunedAxis n a b i j = 0 := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (by rw [h])
  simp only [detunedAxis, levelProj, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.diagonal_apply_ne _ hne, hτ i j hij]
  simp

/-- The axis commutes with a transponder Hamiltonian that has one energy for both levels. -/
theorem detunedAxis_mul_blockDiagonal_smul_one (a b E : ℝ) :
    detunedAxis n a b
        * Matrix.blockDiagonal (fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = Matrix.blockDiagonal (fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        * detunedAxis n a b := by
  simp only [detunedAxis, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    levelProj_mul_blockDiagonal, levelSwap_mul_blockDiagonal_smul_one]

omit [Fintype n] in
/-- **Two level energies as their mean and half their difference**:
`E₀ P₀ + E₁ P₁ = ((E₀ + E₁)/2) · 1 + ((E₁ − E₀)/2) (P₁ − P₀)`. -/
theorem blockDiagonal_smul_one_eq_add (E : Fin 2 → ℝ) :
    Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = Matrix.blockDiagonal
          (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (((E 1 - E 0) / 2 : ℝ) : ℂ) • (levelProj n 1 - levelProj n 0) := by
  ext ⟨p, i⟩ ⟨q, j⟩
  simp only [Matrix.blockDiagonal_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, levelProj, Matrix.diagonal_apply, Prod.mk.injEq,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> by_cases h : p = q <;> simp [h] <;> ring

end Axis

/-! ### The second-level part of a turning orbit -/

section Turn

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The part of a turning orbit in a sector the state avoids.** If `W X = −a X + b S X`,
`S` commutes with `U`, `Q U X = 0` and `Q` fixes `S U X`, then
`Q U (c − d W) X = −(d b) S U X`. -/
theorem mul_turn_mul_of_split {Q U W Sx X : Matrix m m ℂ} {a b : ℂ}
    (hWX : W * X = (-a) • X + b • (Sx * X)) (hSU : Sx * U = U * Sx) (hq1 : Q * U * X = 0)
    (hq2 : Q * (Sx * U * X) = Sx * U * X) (c d : ℂ) :
    Q * (U * (c • (1 : Matrix m m ℂ) - d • W) * X) = -((d * b) • (Sx * U * X)) := by
  have e : U * (c • (1 : Matrix m m ℂ) - d • W) * X
      = c • (U * X) - d • ((-a) • (U * X) + b • (Sx * U * X)) := by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, mul_one, smul_mul_assoc,
      smul_mul_assoc, mul_assoc U W X, hWX, mul_add, mul_smul_comm, mul_smul_comm,
      ← mul_assoc U Sx X, ← hSU]
  rw [e, mul_sub, mul_smul_comm, mul_smul_comm, mul_add, mul_smul_comm, mul_smul_comm,
    ← mul_assoc Q U X, hq1, hq2]
  simp only [smul_zero, zero_add, zero_sub, smul_smul]

end Turn

/-! ### The transponder -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **Levels of different energy: the second level fills as `(|g|/Ω) |sin (Ω t)|`.** The
transponder has no hopping and the level energies `E 0`, `E 1`; `Ω > 0` with
`Ω² = g² + ((E 1 − E 0)/2)²`. For `X` with the transponder in its first level and `t ≥ 0`,
the part of the orbit of `X` with the transponder in its second level has norm within
`|g| ∫₀ᵗ ‖P' e^{−isH_c} X‖ ds` of `(|g|/Ω) |sin (Ω t)| ‖X‖`. Here `P'` projects on the
configurations where the two carriers are apart and `H_c` is the free Hamiltonian with the
mean energy for both levels. -/
theorem transponder_detuned_second_level (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian) (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2)
    (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) {t : ℝ} (ht : 0 ≤ t) :
    |‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀
              (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          * X‖ - |g| / Ω * |Real.sin (Ω * t)| * ‖X‖|
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
              fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖ := by
  have hTc : ∀ _ : Fin 2,
      ((((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hHc := compositeH_isHermitian hM (blockDiagonal_isHermitian hTc)
  have hab : ((E 1 - E 0) / 2 / Ω) ^ 2 + (g / Ω) ^ 2 = 1 := by
    calc ((E 1 - E 0) / 2 / Ω) ^ 2 + (g / Ω) ^ 2
        = (g ^ 2 + ((E 1 - E 0) / 2) ^ 2) / Ω ^ 2 := by ring
      _ = 1 := by rw [← hΩ2, div_self (pow_ne_zero 2 hΩ.ne')]
  have hWlsq : detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω)
      * detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω) = 1 := by
    rw [detunedAxis_mul_self, hab, Complex.ofReal_one, one_smul]
  have hWh : ((1 : Matrix ι ι ℂ)
      ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω)).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (detunedAxis_isHermitian _ _)
  have hWW : ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω))
      * ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, hWlsq, Matrix.one_kronecker_one]
  have hWH := one_kronecker_mul_compositeH M₀
    (detunedAxis_mul_blockDiagonal_smul_one (n := n) ((E 1 - E 0) / 2 / Ω) (g / Ω)
      ((E 0 + E 1) / 2))
  have hP'W := coincProj_mul_one_kronecker (ι := ι) σ τ (fun a b => ¬ r a b)
    (detunedAxis_apply_of_ne τ hτ ((E 1 - E 0) / 2 / Ω) (g / Ω))
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh hSS
  have hPS' := coincProj_mul_one_kronecker (ι := ι) σ τ (fun a b => ¬ r a b) hτ
  have hGS : gateOp σ τ r (levelSwap n) - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n
      = -(((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ (fun a b => ¬ r a b)) := by
    rw [← hPS', ← one_sub_coincProj σ τ r, gateOp, sub_mul, one_mul, neg_sub]
  have hG := gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ
  have hV : ((g : ℂ) • (gateOp σ τ r (levelSwap n)
      - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (hG.sub hSh).eq, Complex.star_def,
      Complex.conj_ofReal]
  have hVf : (g : ℂ) • (gateOp σ τ r (levelSwap n) - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
      = ((-g : ℝ) : ℂ) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * coincProj σ τ (fun a b => ¬ r a b)) := by
    rw [hGS, Complex.ofReal_neg, neg_smul, smul_neg]
  have e1r : Ω * ((E 1 - E 0) / 2 / Ω) = (E 1 - E 0) / 2 := by
    field_simp
  have e2r : Ω * (g / Ω) = g := by
    field_simp
  have hsum : compositeH M₀
        (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • gateOp σ τ r (levelSwap n)
      = compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
          + (Ω : ℂ) • ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω))
          + (g : ℂ) • (gateOp σ τ r (levelSwap n) - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) := by
    unfold compositeH
    rw [blockDiagonal_smul_one_eq_add E, detunedAxis]
    simp only [Matrix.kronecker_add, Matrix.kronecker_smul, smul_add, smul_smul,
      ← Complex.ofReal_mul, e1r, e2r]
    rw [smul_sub]
    abel
  have cmp := norm_exp_sub_rabi_add_mul_le _ _ _ _ _ X Ω (-g) hHc hWh hWW hWH hV hVf hS1
    hP'W ht
  rw [← hsum, abs_neg] at cmp
  -- the second-level part of the reference orbit
  have hQ0X : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) * X = X := by
    have hsum' : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) + ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        = 1 := by
      rw [← Matrix.kronecker_add, levelProj_zero_add_one, Matrix.one_kronecker_one]
    have := congrArg (· * X) hsum'
    simp only [add_mul, hX, add_zero, one_mul] at this
    exact this
  have hWX : ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω)) * X
      = (-(((E 1 - E 0) / 2 / Ω : ℝ) : ℂ)) • X
        + ((g / Ω : ℝ) : ℂ) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * X) := by
    have hks : (1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 - levelProj n 0)
        = (1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1 - (1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0 := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]
    rw [detunedAxis, Matrix.kronecker_add, Matrix.kronecker_smul, Matrix.kronecker_smul,
      hks, add_mul, smul_mul_assoc, smul_mul_assoc, sub_mul, hX, hQ0X,
      zero_sub, smul_neg, ← neg_smul]
  have hSA : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
      = ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) := by
    rw [mul_smul_comm, smul_mul_assoc,
      one_kronecker_mul_compositeH M₀ (levelSwap_mul_blockDiagonal_smul_one ((E 0 + E 1) / 2))]
  have hSU := Matrix.mul_exp_smul_eq_of_commute hSA t
  have hq1 := levelProj_one_mul_freeOrbit M₀
    (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) hX t
  have hq2 := levelProj_one_mul_swap_freeOrbit M₀
    (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) hX t
  have hmain := mul_turn_mul_of_split hWX hSU hq1 hq2 (Complex.cos ((Ω * t : ℝ) : ℂ))
    (Complex.I * Complex.sin ((Ω * t : ℝ) : ℂ))
  have hA := Matrix.conjTranspose_neg_I_smul hHc
  have hnorm : ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖
      = ‖X‖ := by
    refine le_antisymm ?_ (norm_le_norm_swap_freeOrbit hM hTc X t)
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg X)).trans ?_
    rw [Matrix.l2_opNorm_exp_smul_skew _ hA t, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg X) hS1
  have hc : ‖-((Complex.I * Complex.sin ((Ω * t : ℝ) : ℂ) * ((g / Ω : ℝ) : ℂ))
        • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X))‖
      = |g| / Ω * |Real.sin (Ω * t)| * ‖X‖ := by
    rw [norm_neg, norm_smul, hnorm, norm_mul, norm_mul, Complex.norm_I, one_mul,
      ← Complex.ofReal_sin, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_div, abs_of_pos hΩ]
    ring
  have hQ1 := norm_one_kronecker_levelProj_le (n := n) ι 1
  have hQD := ((norm_mul_le ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hQ1)).trans cmp
  have htri := abs_norm_sub_norm_le
    (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * exp (t • ((-Complex.I) • (compositeH M₀
          (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • gateOp σ τ r (levelSwap n)))) * X)
    (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
        * (Complex.cos ((Ω * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
          - (Complex.I * Complex.sin ((Ω * t : ℝ) : ℂ))
            • ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω))) * X))
  have hAB : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH M₀
            (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
          + (g : ℂ) • gateOp σ τ r (levelSwap n)))) * X
      - ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
          * (Complex.cos ((Ω * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
            - (Complex.I * Complex.sin ((Ω * t : ℝ) : ℂ))
              • ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω))) * X)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * ((exp (t • ((-Complex.I) • (compositeH M₀
              (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
              fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
            * (Complex.cos ((Ω * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
              - (Complex.I * Complex.sin ((Ω * t : ℝ) : ℂ))
                • ((1 : Matrix ι ι ℂ) ⊗ₖ detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω))))
          * X) := by
    rw [mul_assoc ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) _ X, ← mul_sub, ← sub_mul]
  rw [hAB, hmain, hc] at htri
  exact htri.trans hQD

end Transponder

/-! ### The packet -/

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **The flat packet in contact with a transponder whose levels differ in energy.** The
messenger is the flat packet of the lattice Dirac field of any dimension; the transponder is
at rest with the level energies `E 0`, `E 1`, in a state of norm `1` in its first level,
supported on the sites `B`; `Ω > 0` with `Ω² = g² + ((E 1 − E 0)/2)²`. If up to the flow
time `t` every site of the packet's moving box is related to every site of `B`, the part of
the state at `t` with the transponder in its second level has norm within
`|g| √(flatTailD t) · t` of `(|g|/Ω) |sin (Ω t)|`. -/
theorem transponder_detuned_flatPacket (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    (hφn : ∑ q, ‖φ q‖ ^ 2 = 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t : ℝ} (ht : 0 ≤ t)
    (hcon : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      r a b) :
    |Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
            ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I)
            • (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
        *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2)
        - (|g| / Ω * |Real.sin (Ω * t)|)|
      ≤ |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * t) := by
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  obtain ⟨hstar, hX1⟩ := norm_vecMulVec_star_of_sum_eq_one hΨ1
  have hM := latticeDiracHam_isHermitian (L := L) h J μ
  have hΨ0 : ((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1)
      *ᵥ (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) = 0 := by
    rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal]
    funext y
    rw [Matrix.mulVec_diagonal]
    by_cases hy : y.2.2 = 1
    · simp [hφ y.2 hy]
    · simp [hy]
  have hX0 : ((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1)
      * Matrix.vecMulVec
        (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
        (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) = 0 := by
    rw [Matrix.mul_vecMulVec, hΨ0]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have key := transponder_detuned_second_level
    (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r hτ hM E g hΩ hΩ2
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)) hX0 ht
  rw [norm_mul_vecMulVec, hstar, mul_one, hX1, mul_one] at key
  have hP' : ∀ s, 0 ≤ s → s ≤ t → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t) :=
    fun s hs hst => (norm_coincProj_freeOrbit_flatPacket_resting_le τ (fun a b => ¬ r a b) h
      he hn hμ ((E 0 + E 1) / 2) lo hN hNL k₀ hw0 hw hγ φ hφn B hφB hs
      (fun a ha b hb => not_not.2 (hcon s hs hst a ha b hb))).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hst))
  have hcont' := Matrix.continuous_norm_mul_exp_smul_mul
    ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
      (Matrix.blockDiagonal
        fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    (coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ (fun a b => ¬ r a b))
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2))
  have hIc := intervalIntegral.integral_mono_on ht (hcont'.intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t))) fun s hs => hP' s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at hIc
  exact key.trans (mul_le_mul_of_nonneg_left hIc (abs_nonneg g))

/-- ★★ **The detuning caps what is launched while in contact.** Under the hypotheses of
`transponder_detuned_flatPacket` the second level's amplitude at `t` is at most
`|g|/Ω + |g| √(flatTailD t) · t`. -/
theorem transponder_detuned_flatPacket_le (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    (hφn : ∑ q, ‖φ q‖ ^ 2 = 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t : ℝ} (ht : 0 ≤ t)
    (hcon : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      r a b) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
            ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I)
            • (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
        *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2)
      ≤ |g| / Ω + |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * t) := by
  have key := (abs_le.1 (transponder_detuned_flatPacket τ r hτ h he hn hμ E g hΩ hΩ2 lo hN
    hNL k₀ hw0 hw hγ φ hφ hφn B hφB ht hcon)).2
  have hc0 : 0 ≤ |g| / Ω := div_nonneg (abs_nonneg g) hΩ.le
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (Ω * t)) hc0
  rw [mul_one] at hs
  linarith

end Packet

end CSD.RecordLayer

end
