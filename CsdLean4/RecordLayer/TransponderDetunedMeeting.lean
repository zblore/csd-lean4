/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderDetuned
public import CsdLean4.RecordLayer.TransponderRabiMeeting

/-!
# Levels of different energy, apart and then in contact

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, items (1) and (2) in one run, the
caused return, for a transponder whose two levels have different energies).

`RecordLayer/TransponderDetuned.lean` treats carriers in contact from the flow time `0`. Here
the run has two parts, as in `RecordLayer/TransponderRabiMeeting.lean`: up to `t₁` it is
compared with the free orbit, and from `t₁` the statement of UD-262 is applied to the state
at `t₁`. A state with the transponder in its first level moves freely as it would with the
mean energy for both levels, up to a phase, so both error terms are read on one orbit.

* `norm_exp_skew_mul` — a skew generator's group keeps the norm;
* ★★ `abs_norm_mul_exp_sub_le_of_stages` — a run in two parts: what a contraction `Q` sees
  at `t` differs from what it sees after `t − t₁` from the reference state at `t₁` by at
  most the departure from the reference up to `t₁`;
* `levelProj_sub_mul_self`, `levelProj_zero_mul_of_firstLevel`;
* ★★ `exp_freeOrbit_mul_of_firstLevel` — **for a state in the first level the free orbit
  with level energies `E₀`, `E₁` is that of the mean energy times the phase `e^{iδs}`**,
  `δ = (E₁ − E₀)/2`; `norm_mul_freeOrbit_of_firstLevel`;
* ★★★ `transponder_detuned_meeting_second_level` — for `0 ≤ t₁ ≤ t` the part in the second
  level has norm within
  `|g| ∫₀^{t₁} ‖P e^{−isH_c} X‖ ds + |g| ∫_{t₁}^{t} ‖P' e^{−isH_c} X‖ ds` of
  `(|g|/Ω) |sin (Ω (t − t₁))| ‖X‖`;
* ★★★ `transponder_detuned_flatPacket_meeting` — **the flat packet and a transponder at rest
  with level energies `E₀`, `E₁`, the box apart up to `t₁` and wholly in contact from `t₂`:
  the second level's amplitude at `t` is within
  `|g| (√ε₁ t₁ + (t₂ − t₁)) + |g| √ε (t − t₂)` of `(|g|/Ω) |sin (Ω (t − t₂))|`**.

## Honest scope

⚠️ **The time of partial contact is counted as error in full**, as in UD-259.

⚠️ **The two box conditions are hypotheses.** No instance with numbers is given for
`E₀ ≠ E₁`. The reading of UD-260 (`transponder_meeting_record`) is stated on this bound.

⚠️ **`Ω > 0` is a hypothesis**, with `Ω² = g² + ((E₁ − E₀)/2)²`. With a large detuning the
leading term `|g|/Ω` is small against the error unless the tails and the time of partial
contact are small too.

⚠️ **The amplitude, not its place.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-259, UD-262, UD-263); `RecordLayer/TransponderDetuned.lean`
(`transponder_detuned_second_level`, `blockDiagonal_smul_one_eq_add`);
`RecordLayer/TransponderRabiMeeting.lean` (`exp_add_smul_eq_mul`,
`transponder_rabi_flatPacket_meeting_ge`); `RecordLayer/TransponderRabi.lean`
(`exp_neg_I_add_smul_of_commute_invol`, `levelProj_one_mul_freeOrbit`);
`Mathlib/Analysis/Matrix/DuhamelState.lean` (`Matrix.norm_exp_neg_I_add_sub_mul_le`);
`RecordLayer/TransponderMeetingPacket.lean`
(`norm_coincProj_freeOrbit_flatPacket_resting_le`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### A run in two parts -/

section Stages

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- The group of a skew generator keeps the norm of what it acts on. -/
theorem norm_exp_skew_mul {A : Matrix m m ℂ} (hA : Aᴴ = -A) (t : ℝ) (X : Matrix m m ℂ) :
    ‖exp (t • A) * X‖ = ‖X‖ := by
  refine le_antisymm ?_ ?_
  · refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_exp_smul_skew _ hA t, one_mul]
  · have hinv := Matrix.exp_smul_mul_exp_neg_smul A (-t)
    rw [neg_neg] at hinv
    have hX : X = exp ((-t) • A) * (exp (t • A) * X) := by
      rw [← mul_assoc, hinv, one_mul]
    calc ‖X‖ = ‖exp ((-t) • A) * (exp (t • A) * X)‖ := congrArg norm hX
      _ ≤ ‖exp ((-t) • A)‖ * ‖exp (t • A) * X‖ := norm_mul_le _ _
      _ = ‖exp (t • A) * X‖ := by rw [Matrix.l2_opNorm_exp_smul_skew _ hA (-t), one_mul]

/-- ★★ **A run in two parts.** `B` is a skew generator and `‖Q‖ ≤ 1`. What `Q` sees of the
orbit of `X` at `t` differs in norm from what it sees after `t − t₁` of the same group from
`e^{t₁ A₀} X` by at most `‖(e^{t₁ B} − e^{t₁ A₀}) X‖`. -/
theorem abs_norm_mul_exp_sub_le_of_stages {B A₀ Q : Matrix m m ℂ} (hB : Bᴴ = -B)
    (hQ : ‖Q‖ ≤ 1) (X : Matrix m m ℂ) (t₁ t : ℝ) :
    |‖Q * exp (t • B) * X‖ - ‖Q * exp ((t - t₁) • B) * (exp (t₁ • A₀) * X)‖|
      ≤ ‖(exp (t₁ • B) - exp (t₁ • A₀)) * X‖ := by
  have hBs : exp (t • B) = exp ((t - t₁) • B) * exp (t₁ • B) := by
    rw [← exp_add_smul_eq_mul, sub_add_cancel]
  have hdiff : Q * exp (t • B) * X - Q * exp ((t - t₁) • B) * (exp (t₁ • A₀) * X)
      = Q * (exp ((t - t₁) • B) * ((exp (t₁ • B) - exp (t₁ • A₀)) * X)) := by
    rw [hBs]
    noncomm_ring
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [hdiff]
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hQ).trans ?_)
  rw [norm_exp_skew_mul hB]

end Stages

/-! ### The free orbit of a state in the first level -/

section FirstLevel

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- The difference of the two level projectors is an involution. -/
theorem levelProj_sub_mul_self :
    (levelProj n 1 - levelProj n 0) * (levelProj n 1 - levelProj n 0) = 1 := by
  have hZd : levelProj n 1 - levelProj n 0
      = Matrix.diagonal fun x : n × Fin 2 => if x.2 = 1 then (1 : ℂ) else -1 := by
    rw [levelProj, levelProj, Matrix.diagonal_sub]
    congr 1
    funext x
    obtain ⟨p, i⟩ := x
    fin_cases i <;> simp
  rw [hZd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  split_ifs <;> simp

/-- A state with the transponder in its first level is fixed by the first level's
projector. -/
theorem levelProj_zero_mul_of_firstLevel {X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ}
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) * X = X := by
  have hsum : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) + ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      = 1 := by
    rw [← Matrix.kronecker_add, levelProj_zero_add_one, Matrix.one_kronecker_one]
  have := congrArg (· * X) hsum
  simp only [add_mul, hX, add_zero, one_mul] at this
  exact this

/-- ★★ **The free orbit of a state in the first level.** With level energies `E 0`, `E 1`
and no hopping, it is the orbit with the mean energy for both levels, times the phase
`cos (δ s) + i sin (δ s)`, `δ = (E 1 − E 0)/2`. -/
theorem exp_freeOrbit_mul_of_firstLevel (M₀ : Matrix ι ι ℂ) (E : Fin 2 → ℝ)
    {X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ}
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) (s : ℝ) :
    exp (s • ((-Complex.I) • compositeH M₀
        (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X
      = (Complex.cos (((E 1 - E 0) / 2 * s : ℝ) : ℂ)
          + Complex.I * Complex.sin (((E 1 - E 0) / 2 * s : ℝ) : ℂ))
        • (exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X) := by
  have hsplit : compositeH M₀
        (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (((E 1 - E 0) / 2 : ℝ) : ℂ)
          • ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 - levelProj n 0)) := by
    unfold compositeH
    rw [blockDiagonal_smul_one_eq_add E, Matrix.kronecker_add, Matrix.kronecker_smul,
      add_assoc]
  have hZZ : ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 - levelProj n 0))
      * ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 - levelProj n 0)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelProj_sub_mul_self, Matrix.one_kronecker_one]
  have hZc : (levelProj n 1 - levelProj n 0)
        * Matrix.blockDiagonal
          (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = Matrix.blockDiagonal
          (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        * (levelProj n 1 - levelProj n 0) := by
    simp only [sub_mul, mul_sub, levelProj_mul_blockDiagonal]
  have hZH := one_kronecker_mul_compositeH M₀ hZc
  have hks : (1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 - levelProj n 0)
      = (1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1 - (1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]
  have hZX : ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 - levelProj n 0)) * X = -X := by
    rw [hks, sub_mul, hX, levelProj_zero_mul_of_firstLevel hX, zero_sub]
  rw [hsplit, exp_neg_I_add_smul_of_commute_invol hZH hZZ ((E 1 - E 0) / 2) s, mul_assoc,
    sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hZX, smul_neg, sub_neg_eq_add,
    ← add_smul, mul_smul_comm]

/-- A matrix sees the free orbit of a state in the first level as it sees the orbit with the
mean energy for both levels. -/
theorem norm_mul_freeOrbit_of_firstLevel (M₀ : Matrix ι ι ℂ) (E : Fin 2 → ℝ)
    (A : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    {X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ}
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) (s : ℝ) :
    ‖A * exp (s • ((-Complex.I) • compositeH M₀
        (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖
      = ‖A * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖ := by
  have hz : ‖Complex.cos (((E 1 - E 0) / 2 * s : ℝ) : ℂ)
      + Complex.I * Complex.sin (((E 1 - E 0) / 2 * s : ℝ) : ℂ)‖ = 1 := by
    rw [mul_comm Complex.I, ← Complex.exp_mul_I, Complex.norm_exp_ofReal_mul_I]
  rw [mul_assoc, exp_freeOrbit_mul_of_firstLevel M₀ E hX s, mul_smul_comm, norm_smul, hz,
    one_mul, mul_assoc]

end FirstLevel

/-! ### The transponder -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **Levels of different energy, apart and then in contact.** The transponder has no
hopping and the level energies `E 0`, `E 1`; `Ω > 0` with `Ω² = g² + ((E 1 − E 0)/2)²`. For
`X` with the transponder in its first level and `0 ≤ t₁ ≤ t`, the part of the orbit of `X`
with the transponder in its second level has norm within
`|g| ∫₀^{t₁} ‖P e^{−isH_c} X‖ ds + |g| ∫_{t₁}^{t} ‖P' e^{−isH_c} X‖ ds` of
`(|g|/Ω) |sin (Ω (t − t₁))| ‖X‖`. `P` projects on the configurations in contact, `P'` on
those apart, and `H_c` is the free Hamiltonian with the mean energy for both levels. -/
theorem transponder_detuned_meeting_second_level (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian) (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2)
    (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) {t₁ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t) :
    |‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀
              (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          * X‖ - |g| / Ω * |Real.sin (Ω * (t - t₁))| * ‖X‖|
      ≤ |g| * (∫ s in (0 : ℝ)..t₁, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
              fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖)
        + |g| * ∫ s in t₁..t, ‖coincProj σ τ (fun a b => ¬ r a b)
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
              fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖ := by
  have hT : ∀ l : Fin 2, (((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun l =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hG := gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ
  have hV : ((g : ℂ) • gateOp σ τ r (levelSwap n)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hG.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh hSS
  have hGP : gateOp σ τ r (levelSwap n)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ r := by
    rw [gateOp, coincProj_mul_one_kronecker (ι := ι) σ τ r hτ]
  have hB := Matrix.conjTranspose_neg_I_smul (hH₀.add hV)
  have hA₀ := Matrix.conjTranspose_neg_I_smul hH₀
  have hQ1 := norm_one_kronecker_levelProj_le (n := n) ι 1
  have hτ' : 0 ≤ t - t₁ := sub_nonneg.2 h12
  -- the first part of the run: the departure from the free orbit up to `t₁`
  have hA1 := Matrix.norm_exp_neg_I_add_sub_mul_le _ ((g : ℂ) • gateOp σ τ r (levelSwap n)) X
    hH₀ hV h1
  have hI1 : (∫ s in (0 : ℝ)..t₁, ‖(g : ℂ) • gateOp σ τ r (levelSwap n)
          * exp (s • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
          * X‖)
      ≤ |g| * ∫ s in (0 : ℝ)..t₁, ‖coincProj σ τ r
          * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h1
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ (coincProj σ τ r) X)).intervalIntegrable _ _)
      fun s _ => ?_
    rw [← norm_mul_freeOrbit_of_firstLevel M₀ E (coincProj σ τ r) hX s, hGP]
    simp only [smul_mul_assoc, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)) (abs_nonneg g)
  have hstage := abs_norm_mul_exp_sub_le_of_stages
    (A₀ := (-Complex.I) • compositeH M₀
      (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    hB hQ1 X t₁ t
  -- the second part: UD-262 from the state at `t₁`
  have hY : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * (exp (t₁ • ((-Complex.I) • compositeH M₀
        (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X)
      = 0 := by
    rw [← mul_assoc]
    exact levelProj_one_mul_freeOrbit M₀ _ hX t₁
  have key := transponder_detuned_second_level σ τ r hτ hM E g hΩ hΩ2 _ hY hτ'
  rw [norm_exp_skew_mul hA₀] at key
  have hI2 : (∫ s in (0 : ℝ)..(t - t₁), ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
          * (exp (t₁ • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
            * X)‖)
      = ∫ s in t₁..t, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖ := by
    have hint : ∀ s : ℝ, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
          * (exp (t₁ • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
            * X)‖
        = ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp ((s + t₁) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖ :=
      fun s => by
        have hz : ‖Complex.cos (((E 1 - E 0) / 2 * t₁ : ℝ) : ℂ)
            + Complex.I * Complex.sin (((E 1 - E 0) / 2 * t₁ : ℝ) : ℂ)‖ = 1 := by
          rw [mul_comm Complex.I, ← Complex.exp_mul_I, Complex.norm_exp_ofReal_mul_I]
        rw [exp_freeOrbit_mul_of_firstLevel M₀ E hX t₁, mul_smul_comm, norm_smul, hz, one_mul,
          exp_add_smul_eq_mul]
        simp only [mul_assoc]
    simp only [hint]
    rw [intervalIntegral.integral_comp_add_right
      (fun u : ℝ => ‖coincProj σ τ (fun a b => ¬ r a b)
        * exp (u • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal
          fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) * X‖) t₁,
      zero_add, sub_add_cancel]
  rw [hI2] at key
  have h1' := hstage.trans (hA1.trans hI1)
  exact (abs_sub_le _ _ _).trans (add_le_add h1' key)

end Transponder

/-! ### The packet -/

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **The second level fills from the meeting, for levels of different energy.** The
messenger is the flat packet of the lattice Dirac field of any dimension; the transponder is
at rest with the level energies `E 0`, `E 1`, in a state of norm `1` in its first level,
supported on the sites `B`; `Ω > 0` with `Ω² = g² + ((E 1 − E 0)/2)²`. For
`0 ≤ t₁ ≤ t₂ ≤ t`: if no site of the packet's moving box is related to a site of `B` up to
`t₁`, and every site of it is related to every site of `B` from `t₂` to `t`, then the part
of the state at `t` with the transponder in its second level has norm within

`|g| (√ε₁ t₁ + (t₂ − t₁)) + |g| √ε (t − t₂)` of `(|g|/Ω) |sin (Ω (t − t₂))|`,

`ε₁ = flatTailD t₁`, `ε = flatTailD t`. -/
theorem transponder_detuned_flatPacket_meeting (τ : n × Fin 2 → κ → ZMod L)
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
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t₁ t₂ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (h2t : t₂ ≤ t)
    (hsep : ∀ s, 0 ≤ s → s ≤ t₁ → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b)
    (hcon : ∀ s, t₂ ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
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
        - (|g| / Ω * |Real.sin (Ω * (t - t₂))|)|
      ≤ |g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁))
        + |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * (t - t₂)) := by
  have ht2 : 0 ≤ t₂ := h1.trans h12
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  obtain ⟨hstar, hX1⟩ := norm_vecMulVec_star_of_sum_eq_one hΨ1
  have hTc : ∀ _ : Fin 2,
      ((((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hM := latticeDiracHam_isHermitian (L := L) h J μ
  have hA := Matrix.conjTranspose_neg_I_smul
    (compositeH_isHermitian hM (blockDiagonal_isHermitian hTc))
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
  have key := transponder_detuned_meeting_second_level
    (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r hτ hM E g hΩ hΩ2
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)) hX0 ht2 h2t
  rw [norm_mul_vecMulVec, hstar, mul_one, hX1, mul_one] at key
  have hP : ∀ s, 0 ≤ s → s ≤ t₁ → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) :=
    fun s hs hs1 => (norm_coincProj_freeOrbit_flatPacket_resting_le τ r h he hn hμ
      ((E 0 + E 1) / 2) lo hN hNL k₀ hw0 hw hγ φ hφn B hφB hs (hsep s hs hs1)).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hs1))
  have hP' : ∀ s, t₂ ≤ s → s ≤ t → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t) :=
    fun s hs hst => (norm_coincProj_freeOrbit_flatPacket_resting_le τ (fun a b => ¬ r a b) h
      he hn hμ ((E 0 + E 1) / 2) lo hN hNL k₀ hw0 hw hγ φ hφn B hφB (ht2.trans hs)
      (fun a ha b hb => not_not.2 (hcon s hs hst a ha b hb))).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hst))
  have hP1 : ‖coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r‖ ≤ 1 := by
    rw [coincProj]
    exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp
  have hcrude : ∀ s : ℝ, ‖coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r
      * exp (s • ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
          (Matrix.blockDiagonal
            fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
      * Matrix.vecMulVec
        (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
        (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)‖ ≤ 1 := fun s => by
    refine (norm_mul_le _ _).trans ?_
    rw [hX1, mul_one]
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_exp_smul_skew _ hA s, mul_one]
    exact hP1
  have hcont := Matrix.continuous_norm_mul_exp_smul_mul
    ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
      (Matrix.blockDiagonal
        fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    (coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r)
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2))
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
  have hIa := intervalIntegral.integral_mono_on h1 (hcont.intervalIntegrable 0 t₁)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t₁))) fun s hs => hP s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hIa
  have hIb := intervalIntegral.integral_mono_on h12 (hcont.intervalIntegrable t₁ t₂)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s _ => hcrude s
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hIb
  have hI1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 t₁) (hcont.intervalIntegrable t₁ t₂)).symm
  have hIc := intervalIntegral.integral_mono_on h2t (hcont'.intervalIntegrable t₂ t)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t))) fun s hs => hP' s hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hIc
  have hg := abs_nonneg g
  have e1 := mul_le_mul_of_nonneg_left (by linarith [hI1, hIa, hIb] :
    (∫ s in (0 : ℝ)..t₂, _) ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁)) hg
  have e2 := mul_le_mul_of_nonneg_left hIc hg
  exact key.trans (add_le_add e1 e2)

end Packet

end CSD.RecordLayer

end
