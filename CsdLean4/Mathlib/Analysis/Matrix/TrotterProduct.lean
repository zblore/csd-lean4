/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound

/-!
# The Lie–Trotter product formula for skew-Hermitian matrices

**Category:** 1-Mathlib (CSD-free, staged for upstream).

For skew-Hermitian `A, B` (so all exponentials are unitary),

  `(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`

in the L2 operator norm. The chain:

* `norm_exp_sub_one_sub_le` — the quantitative second-order remainder
  `‖exp X − 1 − X‖ ≤ ‖X‖² · e^{‖X‖}` (tail of the exponential series,
  termwise dominated);
* `norm_exp_mul_exp_sub_exp_add_le` — the one-step defect
  `‖exp X · exp Y − exp (X+Y)‖ ≤ (‖X‖+‖Y‖)²(3+‖X‖+‖Y‖)e^{‖X‖+‖Y‖}` for
  skew `X, Y` (the algebraic four-term split, with the unitary factors at
  norm one);
* `norm_pow_sub_pow_le_of_unitary` — the growth-free telescoping
  `‖Sⁿ − Tⁿ‖ ≤ n·‖S − T‖` for unitaries;
* ★★ `trotter_skew` — the product formula: the one-step defect is
  `O(1/n²)`, the telescoping multiplies by `n`, and the total `O(1/n)`
  squeezes to zero.

Consumed by the CSD chain as CV-12 (`specs/eft-stage4-plan.md`): the
interacting drive for an arbitrary Hermitian `V` becomes a limit of
constructible steps. No Trotter statement exists in Mathlib at the pin
(checked 2026-08-09); the skew-Hermitian case is the natural first
upstream cut, since unitarity removes all growth factors.

## Provenance

Staged as upstream Mathlib material; L2 operator norm scope, as
`DuhamelBound.lean`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- Skew-Hermitian exponentials are unitary (membership form). -/
theorem exp_mem_unitaryGroup_of_skew {X : Matrix m m ℂ} (hX : Xᴴ = -X) :
    exp X ∈ Matrix.unitaryGroup m ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, hX,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl X).neg_left),
    neg_add_cancel, exp_zero]

/-- Skew-Hermitian exponentials have unit norm. -/
theorem l2_opNorm_exp_skew {X : Matrix m m ℂ} (hX : Xᴴ = -X) :
    ‖exp X‖ = 1 := by
  have := l2_opNorm_exp_smul_skew X hX 1
  rwa [one_smul] at this

omit [Nonempty m] in
set_option maxHeartbeats 800000 in
/-- **The quantitative second-order remainder**:
`‖exp X − 1 − X‖ ≤ ‖X‖² · e^{‖X‖}`. -/
theorem norm_exp_sub_one_sub_le (X : Matrix m m ℂ) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  set f : ℕ → Matrix m m ℂ := fun n => ((n.factorial : ℂ))⁻¹ • X ^ n with hf
  have hsum : HasSum f (exp X) := exp_series_hasSum_exp' (𝕂 := ℂ) X
  have hsplit : (∑ i ∈ Finset.range 2, f i) + ∑' i, f (i + 2) = ∑' i, f i :=
    hsum.summable.sum_add_tsum_nat_add 2
  have hf01 : (∑ i ∈ Finset.range 2, f i) = 1 + X := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [hf]
  have htail : exp X - 1 - X = ∑' i, f (i + 2) := by
    rw [← hsum.tsum_eq, ← hsplit, hf01]
    abel
  -- termwise domination
  have hterm : ∀ i : ℕ, ‖f (i + 2)‖
      ≤ ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by
    intro i
    rw [hf]
    have hfe : (((i + 2).factorial : ℝ))⁻¹ ≤ ((i.factorial : ℝ))⁻¹ := by
      gcongr
      omega
    calc ‖(((i + 2).factorial : ℂ))⁻¹ • X ^ (i + 2)‖
        = (((i + 2).factorial : ℝ))⁻¹ * ‖X ^ (i + 2)‖ := by
          rw [norm_smul, norm_inv, Complex.norm_natCast]
      _ ≤ (((i + 2).factorial : ℝ))⁻¹ * ‖X‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_left (norm_pow_le' X (Nat.succ_pos _))
            (by positivity)
      _ ≤ ((i.factorial : ℝ))⁻¹ * ‖X‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_right hfe (by positivity)
      _ = ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by ring
  have hsummable_norm : Summable fun i : ℕ => ‖f (i + 2)‖ := by
    have h0 : Summable fun n : ℕ => ‖f n‖ := by
      have := norm_expSeries_summable_of_mem_ball' (𝕂 := ℂ) X
        ((expSeries_radius_eq_top ℂ (Matrix m m ℂ)).symm ▸ edist_lt_top _ _)
      exact this
    exact h0.comp_injective fun a b hab => by omega
  have hsummable_dom : Summable fun i : ℕ =>
      ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by
    refine Summable.mul_left _ ?_
    have := Real.summable_pow_div_factorial ‖X‖
    refine this.congr fun i => ?_
    rw [div_eq_mul_inv, mul_comm]
  calc ‖exp X - 1 - X‖
      = ‖∑' i, f (i + 2)‖ := by rw [htail]
    _ ≤ ∑' i, ‖f (i + 2)‖ := norm_tsum_le_tsum_norm hsummable_norm
    _ ≤ ∑' i, ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) :=
        hsummable_norm.tsum_le_tsum hterm hsummable_dom
    _ = ‖X‖ ^ 2 * ∑' i, ((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i := tsum_mul_left
    _ = ‖X‖ ^ 2 * Real.exp ‖X‖ := by
        congr 1
        have hexp := (exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ)).tsum_eq
        rw [Real.exp_eq_exp_ℝ, ← hexp]
        exact tsum_congr fun i => by rw [smul_eq_mul]

/-- **The one-step defect** for skew-Hermitian `X, Y`:
`‖exp X · exp Y − exp (X+Y)‖ ≤ (‖X‖+‖Y‖)²·(3+‖X‖+‖Y‖)·e^{‖X‖+‖Y‖}`. -/
theorem norm_exp_mul_exp_sub_exp_add_le {X Y : Matrix m m ℂ}
    (hY : Yᴴ = -Y) :
    ‖exp X * exp Y - exp (X + Y)‖
      ≤ (‖X‖ + ‖Y‖) ^ 2 * (3 + (‖X‖ + ‖Y‖)) * Real.exp (‖X‖ + ‖Y‖) := by
  set a := ‖X‖ with ha
  set b := ‖Y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hdecomp : exp X * exp Y - exp (X + Y)
      = (exp X - 1 - X) * exp Y + (1 + X) * (exp Y - 1 - Y)
        + (X * Y - (exp (X + Y) - 1 - (X + Y))) := by
    noncomm_ring
  have h1 : ‖(exp X - 1 - X) * exp Y‖ ≤ a ^ 2 * Real.exp a := by
    calc ‖(exp X - 1 - X) * exp Y‖
        ≤ ‖exp X - 1 - X‖ * ‖exp Y‖ := norm_mul_le _ _
      _ = ‖exp X - 1 - X‖ := by rw [l2_opNorm_exp_skew hY, mul_one]
      _ ≤ a ^ 2 * Real.exp a := norm_exp_sub_one_sub_le X
  have h2 : ‖(1 + X) * (exp Y - 1 - Y)‖ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
    calc ‖(1 + X) * (exp Y - 1 - Y)‖
        ≤ ‖(1 : Matrix m m ℂ) + X‖ * ‖exp Y - 1 - Y‖ := norm_mul_le _ _
      _ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
          have hone : ‖(1 : Matrix m m ℂ) + X‖ ≤ 1 + a := by
            calc ‖(1 : Matrix m m ℂ) + X‖ ≤ ‖(1 : Matrix m m ℂ)‖ + ‖X‖ :=
                  norm_add_le _ _
              _ = 1 + a := by rw [norm_one]
          exact mul_le_mul hone (norm_exp_sub_one_sub_le Y)
            (norm_nonneg _) (by positivity)
  have h3 : ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
      ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
    calc ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
        ≤ ‖X * Y‖ + ‖exp (X + Y) - 1 - (X + Y)‖ := norm_sub_le _ _
      _ ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
          refine add_le_add (norm_mul_le _ _) ?_
          calc ‖exp (X + Y) - 1 - (X + Y)‖
              ≤ ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ := norm_exp_sub_one_sub_le _
            _ ≤ (a + b) ^ 2 * Real.exp (a + b) := by
                have hab : ‖X + Y‖ ≤ a + b := norm_add_le _ _
                gcongr
  have hea : Real.exp a ≤ Real.exp (a + b) :=
    Real.exp_le_exp.mpr (by linarith)
  have heb : Real.exp b ≤ Real.exp (a + b) :=
    Real.exp_le_exp.mpr (by linarith)
  have he1 : (1 : ℝ) ≤ Real.exp (a + b) :=
    Real.one_le_exp (by linarith)
  have hepos : (0 : ℝ) < Real.exp (a + b) := Real.exp_pos _
  have hpoly : a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2)
      ≤ (a + b) ^ 2 * (3 + (a + b)) := by
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg (mul_nonneg ha0 ha0) hb0,
      mul_nonneg (mul_nonneg ha0 hb0) hb0, sq_nonneg a, sq_nonneg b]
  calc ‖exp X * exp Y - exp (X + Y)‖
      ≤ ‖(exp X - 1 - X) * exp Y‖ + ‖(1 + X) * (exp Y - 1 - Y)‖
        + ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖ := by
        rw [hdecomp]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ a ^ 2 * Real.exp a + (1 + a) * (b ^ 2 * Real.exp b)
        + (a * b + (a + b) ^ 2 * Real.exp (a + b)) :=
        add_le_add (add_le_add h1 h2) h3
    _ ≤ a ^ 2 * Real.exp (a + b) + (1 + a) * (b ^ 2 * Real.exp (a + b))
        + (a * b * Real.exp (a + b) + (a + b) ^ 2 * Real.exp (a + b)) := by
        refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ le_rfl)
        · exact mul_le_mul_of_nonneg_left hea (by positivity)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left heb (by positivity)) (by linarith)
        · calc a * b = a * b * 1 := by ring
            _ ≤ a * b * Real.exp (a + b) :=
              mul_le_mul_of_nonneg_left he1 (mul_nonneg ha0 hb0)
    _ = (a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2))
        * Real.exp (a + b) := by ring
    _ ≤ (a + b) ^ 2 * (3 + (a + b)) * Real.exp (a + b) :=
        mul_le_mul_of_nonneg_right hpoly hepos.le

set_option maxHeartbeats 800000 in
/-- **Growth-free telescoping**: for unitaries,
`‖Sⁿ − Tⁿ‖ ≤ n · ‖S − T‖`. -/
theorem norm_pow_sub_pow_le_of_unitary {S T : Matrix m m ℂ}
    (hS : S ∈ Matrix.unitaryGroup m ℂ) (hT : T ∈ Matrix.unitaryGroup m ℂ)
    (n : ℕ) : ‖S ^ n - T ^ n‖ ≤ n * ‖S - T‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdecomp : S ^ (n + 1) - T ^ (n + 1)
        = (S ^ n - T ^ n) * S + T ^ n * (S - T) := by
      rw [pow_succ, pow_succ, sub_mul, mul_sub]
      abel
    have hSn : ‖S‖ = 1 := CStarRing.norm_of_mem_unitary hS
    have hTn : ‖T ^ n‖ = 1 :=
      CStarRing.norm_of_mem_unitary (pow_mem hT n)
    have h1 : ‖S ^ (n + 1) - T ^ (n + 1)‖
        ≤ ‖S ^ n - T ^ n‖ * ‖S‖ + ‖T ^ n‖ * ‖S - T‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    rw [hSn, hTn, one_mul, mul_one] at h1
    have hexp : ((n + 1 : ℕ) : ℝ) * ‖S - T‖ = ↑n * ‖S - T‖ + ‖S - T‖ := by
      push_cast
      ring
    rw [hexp]
    linarith

set_option maxHeartbeats 1000000 in
/-- ★★ **The Lie–Trotter product formula, skew-Hermitian case**:
`(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`. The one-step defect is
`O(1/n²)`, the unitary telescoping multiplies by `n`, and the total
`O(1/n)` squeezes to zero. -/
theorem trotter_skew {A B : Matrix m m ℂ} (hA : Aᴴ = -A) (hB : Bᴴ = -B) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n)
      Filter.atTop (nhds (exp (A + B))) := by
  set s := ‖A‖ + ‖B‖ with hs
  have hs0 : 0 ≤ s := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
        ≤ (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp s) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hAs : ((n : ℝ)⁻¹ • A)ᴴ = -((n : ℝ)⁻¹ • A) :=
      conjTranspose_real_smul_skew hA _
    have hBs : ((n : ℝ)⁻¹ • B)ᴴ = -((n : ℝ)⁻¹ • B) :=
      conjTranspose_real_smul_skew hB _
    have hABskew : (A + B)ᴴ = -(A + B) := by
      rw [Matrix.conjTranspose_add, hA, hB]
      abel
    have hABs : ((n : ℝ)⁻¹ • (A + B))ᴴ = -((n : ℝ)⁻¹ • (A + B)) :=
      conjTranspose_real_smul_skew hABskew _
    have hexpAB : exp (A + B) = exp ((n : ℝ)⁻¹ • (A + B)) ^ n := by
      rw [← exp_nsmul, ← smul_assoc, nsmul_eq_mul,
        mul_inv_cancel₀ (ne_of_gt hnpos), one_smul]
    have hnormA : ‖(n : ℝ)⁻¹ • A‖ = (n : ℝ)⁻¹ * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
    have hnormB : ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * ‖B‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
    have hsn : ‖(n : ℝ)⁻¹ • A‖ + ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * s := by
      rw [hnormA, hnormB, hs]; ring
    have hstep := norm_exp_mul_exp_sub_exp_add_le (X := (n : ℝ)⁻¹ • A) hBs
    rw [hsn, ← smul_add] at hstep
    have htel := norm_pow_sub_pow_le_of_unitary
      (mul_mem (exp_mem_unitaryGroup_of_skew hAs)
        (exp_mem_unitaryGroup_of_skew hBs))
      (exp_mem_unitaryGroup_of_skew hABs) n
    have hsle : (n : ℝ)⁻¹ * s ≤ s := by
      calc (n : ℝ)⁻¹ * s ≤ 1 * s := by
            gcongr
            rw [inv_le_one_iff₀]
            right; exact_mod_cast hn
        _ = s := one_mul s
    calc ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
        = ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n
            - exp ((n : ℝ)⁻¹ • (A + B)) ^ n‖ := by rw [hexpAB]
      _ ≤ n * ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
            - exp ((n : ℝ)⁻¹ • (A + B))‖ := htel
      _ ≤ n * (((n : ℝ)⁻¹ * s) ^ 2 * (3 + (n : ℝ)⁻¹ * s)
            * Real.exp ((n : ℝ)⁻¹ * s)) := by
          gcongr
      _ = (n : ℝ)⁻¹ * (s ^ 2 * (3 + (n : ℝ)⁻¹ * s)
            * Real.exp ((n : ℝ)⁻¹ * s)) := by
          have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
          field_simp
          try ring
      _ ≤ (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp s) := by
          have hexp_le : Real.exp ((n : ℝ)⁻¹ * s) ≤ Real.exp s :=
            Real.exp_le_exp.mpr hsle
          have h3le : 3 + (n : ℝ)⁻¹ * s ≤ 3 + s := by linarith
          have hmono : s ^ 2 * (3 + (n : ℝ)⁻¹ * s) * Real.exp ((n : ℝ)⁻¹ * s)
              ≤ s ^ 2 * (3 + s) * Real.exp s := by
            have h1 : s ^ 2 * (3 + (n : ℝ)⁻¹ * s) ≤ s ^ 2 * (3 + s) :=
              mul_le_mul_of_nonneg_left h3le (by positivity)
            calc s ^ 2 * (3 + (n : ℝ)⁻¹ * s) * Real.exp ((n : ℝ)⁻¹ * s)
                ≤ s ^ 2 * (3 + s) * Real.exp ((n : ℝ)⁻¹ * s) :=
                  mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
              _ ≤ s ^ 2 * (3 + s) * Real.exp s := by
                  refine mul_le_mul_of_nonneg_left hexp_le ?_
                  have h30 : (0 : ℝ) ≤ 3 + s := by linarith
                  positivity
          exact mul_le_mul_of_nonneg_left hmono hninv
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp s))
      Filter.atTop (nhds 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (s ^ 2 * (3 + s) * Real.exp s)
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hbound n hn

end Matrix
