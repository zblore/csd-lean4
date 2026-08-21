/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.TrotterProduct

/-!
# The Lie–Trotter product formula in a Banach algebra

**Category:** 1-Mathlib (CSD-free, staged for upstream).

**Glossary:** https://glossary.constraintsurfacedynamics.com/lie-trotter-formula/
Plain-language, CSD-role and formal statements of the Lie-Trotter product formula, with
this module as the Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

For arbitrary elements `A, B` of a complete normed algebra over `ℝ` with
`‖1‖ = 1`,

  `(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`.

This de-skews the staged matrix `trotter_skew`
(`Mathlib/Analysis/Matrix/TrotterProduct.lean`): skewness entered that proof
exactly twice, and both uses generalize —

* `‖exp Y‖ = 1` in the one-step defect becomes `‖exp Y‖ ≤ e^{‖Y‖}`
  (`norm_exp_le_exp_norm`), absorbed by the same final constant since the
  original calc already relaxes every factor to `e^{‖X‖+‖Y‖}`;
* the norm-one telescoping becomes `‖Sⁿ − Tⁿ‖ ≤ n·Cⁿ·‖S − T‖` for
  `‖S‖, ‖T‖ ≤ C` with `1 ≤ C` (`norm_pow_sub_pow_le_of_norm_le`), and at
  step `n` the factors satisfy `C = e^{s/n}`, so `Cⁿ = e^s` stays bounded.

The chain:

* `norm_exp_le_exp_norm` — `‖exp X‖ ≤ e^{‖X‖}` (termwise domination);
* `norm_exp_sub_one_sub_le'` — the second-order remainder
  `‖exp X − 1 − X‖ ≤ ‖X‖²·e^{‖X‖}`, verbatim port of the matrix proof;
* `norm_exp_mul_exp_sub_exp_add_le'` — the one-step defect, hypothesis-free:
  `‖exp X · exp Y − exp (X+Y)‖ ≤ (‖X‖+‖Y‖)²(3+‖X‖+‖Y‖)e^{‖X‖+‖Y‖}`;
* `norm_pow_sub_pow_le_of_norm_le` — the growth-controlled telescoping;
* ★★ `trotter_product` — the product formula, with the explicit rate
  `‖(exp(A/n)exp(B/n))ⁿ − exp(A+B)‖ ≤ n⁻¹·s²(3+s)e^{2s}`, `s = ‖A‖+‖B‖`.

Consumed by `LF6/LindbladPositivity.lean` in the endomorphism algebra of
matrix space, where the two factors are the (positivity-preserving) drift and
jump flows of a GKSL generator.

## Provenance

Staged as upstream Mathlib material.
-/

@[expose] public section

open NormedSpace

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]

set_option maxHeartbeats 800000 in
/-- **The exponential norm bound**: `‖exp X‖ ≤ e^{‖X‖}` (termwise domination
of the exponential series). -/
theorem norm_exp_le_exp_norm (X : 𝔸) : ‖exp X‖ ≤ Real.exp ‖X‖ := by
  have hsum : HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • X ^ n) (exp X) :=
    exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hnorm : Summable fun n : ℕ => ‖((n.factorial : ℝ))⁻¹ • X ^ n‖ :=
    norm_expSeries_summable_of_mem_ball' (𝕂 := ℝ) X
      ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
  have hterm : ∀ n : ℕ, ‖((n.factorial : ℝ))⁻¹ • X ^ n‖
      ≤ ((n.factorial : ℝ))⁻¹ * ‖X‖ ^ n := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · exact mul_le_mul_of_nonneg_left (norm_pow_le' X hpos) (by positivity)
  have hdom : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ * ‖X‖ ^ n := by
    have := Real.summable_pow_div_factorial ‖X‖
    refine this.congr fun i => ?_
    rw [div_eq_mul_inv, mul_comm]
  calc ‖exp X‖ = ‖∑' n, ((n.factorial : ℝ))⁻¹ • X ^ n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n, ‖((n.factorial : ℝ))⁻¹ • X ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, ((n.factorial : ℝ))⁻¹ * ‖X‖ ^ n :=
        hnorm.tsum_le_tsum hterm hdom
    _ = Real.exp ‖X‖ := by
        have hexp := (exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ)).tsum_eq
        rw [Real.exp_eq_exp_ℝ, ← hexp]
        exact tsum_congr fun i => by rw [smul_eq_mul]

omit [NormOneClass 𝔸] in
set_option maxHeartbeats 800000 in
/-- **The quantitative second-order remainder**, Banach-algebra form:
`‖exp X − 1 − X‖ ≤ ‖X‖² · e^{‖X‖}`. -/
theorem norm_exp_sub_one_sub_le' (X : 𝔸) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  set f : ℕ → 𝔸 := fun n => ((n.factorial : ℝ))⁻¹ • X ^ n with hf
  have hsum : HasSum f (exp X) := exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hsplit : (∑ i ∈ Finset.range 2, f i) + ∑' i, f (i + 2) = ∑' i, f i :=
    hsum.summable.sum_add_tsum_nat_add 2
  have hf01 : (∑ i ∈ Finset.range 2, f i) = 1 + X := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [hf]
  have htail : exp X - 1 - X = ∑' i, f (i + 2) := by
    rw [← hsum.tsum_eq, ← hsplit, hf01]
    abel
  have hterm : ∀ i : ℕ, ‖f (i + 2)‖
      ≤ ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by
    intro i
    rw [hf]
    have hfe : (((i + 2).factorial : ℝ))⁻¹ ≤ ((i.factorial : ℝ))⁻¹ := by
      gcongr
      omega
    calc ‖(((i + 2).factorial : ℝ))⁻¹ • X ^ (i + 2)‖
        = (((i + 2).factorial : ℝ))⁻¹ * ‖X ^ (i + 2)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (((i + 2).factorial : ℝ))⁻¹ * ‖X‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_left (norm_pow_le' X (Nat.succ_pos _))
            (by positivity)
      _ ≤ ((i.factorial : ℝ))⁻¹ * ‖X‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_right hfe (by positivity)
      _ = ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by ring
  have hsummable_norm : Summable fun i : ℕ => ‖f (i + 2)‖ := by
    have h0 : Summable fun n : ℕ => ‖f n‖ :=
      norm_expSeries_summable_of_mem_ball' (𝕂 := ℝ) X
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
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

/-- **The one-step defect, hypothesis-free**: for any `X, Y`,
`‖exp X · exp Y − exp (X+Y)‖ ≤ (‖X‖+‖Y‖)²·(3+‖X‖+‖Y‖)·e^{‖X‖+‖Y‖}` —
the same constant as the skew case, since the skew proof already relaxed
every exponential factor to `e^{‖X‖+‖Y‖}`. -/
theorem norm_exp_mul_exp_sub_exp_add_le' (X Y : 𝔸) :
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
  have h1 : ‖(exp X - 1 - X) * exp Y‖ ≤ a ^ 2 * Real.exp a * Real.exp b := by
    calc ‖(exp X - 1 - X) * exp Y‖
        ≤ ‖exp X - 1 - X‖ * ‖exp Y‖ := norm_mul_le _ _
      _ ≤ (a ^ 2 * Real.exp a) * Real.exp b := by
          refine mul_le_mul (norm_exp_sub_one_sub_le' X)
            (norm_exp_le_exp_norm Y) (norm_nonneg _) (by positivity)
  have h2 : ‖(1 + X) * (exp Y - 1 - Y)‖ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
    calc ‖(1 + X) * (exp Y - 1 - Y)‖
        ≤ ‖(1 : 𝔸) + X‖ * ‖exp Y - 1 - Y‖ := norm_mul_le _ _
      _ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
          have hone : ‖(1 : 𝔸) + X‖ ≤ 1 + a := by
            calc ‖(1 : 𝔸) + X‖ ≤ ‖(1 : 𝔸)‖ + ‖X‖ := norm_add_le _ _
              _ = 1 + a := by rw [norm_one]
          exact mul_le_mul hone (norm_exp_sub_one_sub_le' Y)
            (norm_nonneg _) (by positivity)
  have h3 : ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
      ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
    calc ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
        ≤ ‖X * Y‖ + ‖exp (X + Y) - 1 - (X + Y)‖ := norm_sub_le _ _
      _ ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
          refine add_le_add (norm_mul_le _ _) ?_
          calc ‖exp (X + Y) - 1 - (X + Y)‖
              ≤ ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ := norm_exp_sub_one_sub_le' _
            _ ≤ (a + b) ^ 2 * Real.exp (a + b) := by
                have hab : ‖X + Y‖ ≤ a + b := norm_add_le _ _
                gcongr
  have heab : Real.exp a * Real.exp b = Real.exp (a + b) :=
    (Real.exp_add a b).symm
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
    _ ≤ a ^ 2 * Real.exp a * Real.exp b + (1 + a) * (b ^ 2 * Real.exp b)
        + (a * b + (a + b) ^ 2 * Real.exp (a + b)) :=
        add_le_add (add_le_add h1 h2) h3
    _ ≤ a ^ 2 * Real.exp (a + b) + (1 + a) * (b ^ 2 * Real.exp (a + b))
        + (a * b * Real.exp (a + b) + (a + b) ^ 2 * Real.exp (a + b)) := by
        refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ le_rfl)
        · rw [mul_assoc, heab]
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left heb (by positivity)) (by linarith)
        · calc a * b = a * b * 1 := by ring
            _ ≤ a * b * Real.exp (a + b) :=
              mul_le_mul_of_nonneg_left he1 (mul_nonneg ha0 hb0)
    _ = (a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2))
        * Real.exp (a + b) := by ring
    _ ≤ (a + b) ^ 2 * (3 + (a + b)) * Real.exp (a + b) :=
        mul_le_mul_of_nonneg_right hpoly hepos.le

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- **Growth-controlled telescoping**: for `‖S‖, ‖T‖ ≤ C` with `1 ≤ C`,
`‖Sⁿ − Tⁿ‖ ≤ n · Cⁿ · ‖S − T‖`. -/
theorem norm_pow_sub_pow_le_of_norm_le {S T : 𝔸} {C : ℝ} (hC : 1 ≤ C)
    (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C) (n : ℕ) :
    ‖S ^ n - T ^ n‖ ≤ n * C ^ n * ‖S - T‖ := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  induction n with
  | zero => simp
  | succ n ih =>
    have hdecomp : S ^ (n + 1) - T ^ (n + 1)
        = (S ^ n - T ^ n) * S + T ^ n * (S - T) := by
      rw [pow_succ, pow_succ, sub_mul, mul_sub]
      abel
    have hTn : ‖T ^ n‖ ≤ C ^ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · exact le_trans (norm_pow_le' T hpos) (by gcongr)
    have h1 : ‖S ^ (n + 1) - T ^ (n + 1)‖
        ≤ ‖S ^ n - T ^ n‖ * ‖S‖ + ‖T ^ n‖ * ‖S - T‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    have h2 : ‖S ^ n - T ^ n‖ * ‖S‖ ≤ (n * C ^ n * ‖S - T‖) * C :=
      mul_le_mul ih hS (norm_nonneg _) (by positivity)
    have h3 : ‖T ^ n‖ * ‖S - T‖ ≤ C ^ n * ‖S - T‖ :=
      mul_le_mul_of_nonneg_right hTn (norm_nonneg _)
    have hCn : C ^ n ≤ C ^ (n + 1) := by
      calc C ^ n = C ^ n * 1 := by ring
        _ ≤ C ^ n * C := by gcongr
        _ = C ^ (n + 1) := by ring
    calc ‖S ^ (n + 1) - T ^ (n + 1)‖
        ≤ (n * C ^ n * ‖S - T‖) * C + C ^ n * ‖S - T‖ := by
          refine le_trans h1 (add_le_add h2 h3)
      _ = n * (C ^ n * C) * ‖S - T‖ + C ^ n * ‖S - T‖ := by ring
      _ ≤ n * C ^ (n + 1) * ‖S - T‖ + C ^ (n + 1) * ‖S - T‖ := by
          rw [show C ^ n * C = C ^ (n + 1) from by ring]
          gcongr
      _ = ((n : ℝ) + 1) * C ^ (n + 1) * ‖S - T‖ := by ring
      _ = ((n + 1 : ℕ) : ℝ) * C ^ (n + 1) * ‖S - T‖ := by push_cast; ring

omit [NormOneClass 𝔸] in
/-- `exp x ^ n = exp (n • x)`, by induction from `exp_add_of_commute` (the
`exp_nsmul` route needs a `ℚ`-algebra instance a general real Banach algebra
does not carry). -/
theorem exp_pow_eq_exp_nsmul (x : 𝔸) (n : ℕ) : exp x ^ n = exp (n • x) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih,
      ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
        ((Commute.refl x).smul_left (k : ℕ))
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _),
      ← succ_nsmul]

set_option maxHeartbeats 1000000 in
/-- ★★ **The Lie–Trotter product formula in a Banach algebra**: for any
`A, B`, `(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`, at the explicit rate
`n⁻¹ · s²(3+s)e^{2s}` with `s = ‖A‖ + ‖B‖`. The one-step defect is
`O(1/n²)`, the telescoping costs `n · (e^{s/n})ⁿ = n·e^s`, and the total
`O(1/n)` squeezes to zero. -/
theorem trotter_product (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n)
      Filter.atTop (nhds (exp (A + B))) := by
  set s := ‖A‖ + ‖B‖ with hs
  have hs0 : 0 ≤ s := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
        ≤ (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hexpAB : exp (A + B) = exp ((n : ℝ)⁻¹ • (A + B)) ^ n := by
      rw [exp_pow_eq_exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hnpos), one_smul]
    have hnormA : ‖(n : ℝ)⁻¹ • A‖ = (n : ℝ)⁻¹ * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
    have hnormB : ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * ‖B‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
    have hsn : ‖(n : ℝ)⁻¹ • A‖ + ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * s := by
      rw [hnormA, hnormB, hs]; ring
    -- the uniform norm ceiling e^{s/n} on all three step factors
    set C := Real.exp ((n : ℝ)⁻¹ * s) with hC
    have hC1 : 1 ≤ C := Real.one_le_exp (mul_nonneg hninv hs0)
    have hfac : ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)‖ ≤ C := by
      calc ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)‖
          ≤ ‖exp ((n : ℝ)⁻¹ • A)‖ * ‖exp ((n : ℝ)⁻¹ • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖(n : ℝ)⁻¹ • A‖ * Real.exp ‖(n : ℝ)⁻¹ • B‖ :=
            mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _)
              (norm_nonneg _) (Real.exp_pos _).le
        _ = C := by rw [← Real.exp_add, hsn]
    have hfacAB : ‖exp ((n : ℝ)⁻¹ • (A + B))‖ ≤ C := by
      calc ‖exp ((n : ℝ)⁻¹ • (A + B))‖
          ≤ Real.exp ‖(n : ℝ)⁻¹ • (A + B)‖ := norm_exp_le_exp_norm _
        _ ≤ C := by
            rw [hC]
            refine Real.exp_le_exp.mpr ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
            have : ‖A + B‖ ≤ s := norm_add_le _ _
            exact mul_le_mul_of_nonneg_left this hninv
    have hCn : C ^ n ≤ Real.exp s := by
      rw [hC, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      rw [show (n : ℝ) * ((n : ℝ)⁻¹ * s) = ((n : ℝ) * (n : ℝ)⁻¹) * s from by
        ring, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul]
    have hstep := norm_exp_mul_exp_sub_exp_add_le'
      ((n : ℝ)⁻¹ • A) ((n : ℝ)⁻¹ • B)
    rw [hsn, ← smul_add] at hstep
    have htel := norm_pow_sub_pow_le_of_norm_le hC1 hfac hfacAB n
    have hsle : (n : ℝ)⁻¹ * s ≤ s := by
      calc (n : ℝ)⁻¹ * s ≤ 1 * s := by
            gcongr
            rw [inv_le_one_iff₀]
            right; exact_mod_cast hn
        _ = s := one_mul s
    have hstep' : ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
          - exp ((n : ℝ)⁻¹ • (A + B))‖
        ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s := by
      refine le_trans hstep ?_
      have h3le : 3 + (n : ℝ)⁻¹ * s ≤ 3 + s := by linarith
      have hele : Real.exp ((n : ℝ)⁻¹ * s) ≤ Real.exp s :=
        Real.exp_le_exp.mpr hsle
      have hsq : (0 : ℝ) ≤ ((n : ℝ)⁻¹ * s) ^ 2 := sq_nonneg _
      calc ((n : ℝ)⁻¹ * s) ^ 2 * (3 + (n : ℝ)⁻¹ * s)
            * Real.exp ((n : ℝ)⁻¹ * s)
          ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp ((n : ℝ)⁻¹ * s) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h3le hsq) (Real.exp_pos _).le
        _ ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s := by
            refine mul_le_mul_of_nonneg_left hele ?_
            have : (0 : ℝ) ≤ 3 + s := by linarith
            positivity
    calc ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
        = ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n
            - exp ((n : ℝ)⁻¹ • (A + B)) ^ n‖ := by rw [hexpAB]
      _ ≤ n * C ^ n * ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
            - exp ((n : ℝ)⁻¹ • (A + B))‖ := htel
      _ ≤ n * Real.exp s * (((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s) := by
          have hcoef : (n : ℝ) * C ^ n ≤ n * Real.exp s :=
            mul_le_mul_of_nonneg_left hCn hnpos.le
          refine mul_le_mul hcoef hstep' (norm_nonneg _) ?_
          positivity
      _ = ((n : ℝ) * (n : ℝ)⁻¹)
            * ((n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * (Real.exp s * Real.exp s))) := by
          ring
      _ = (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)) := by
          rw [mul_inv_cancel₀ (ne_of_gt hnpos), one_mul, ← Real.exp_add,
            ← two_mul]
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)))
      Filter.atTop (nhds 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (s ^ 2 * (3 + s) * Real.exp (2 * s))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hbound n hn

end NormedSpace
