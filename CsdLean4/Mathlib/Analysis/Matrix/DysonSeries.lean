/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Dyson series of a perturbed unitary group

**Category:** 1-Mathlib (CSD-free; staged for upstream).

For skew-Hermitian generators `A` (free) and `B` (interaction) on a finite-dimensional Hilbert
space, the propagator `exp (t (A + B))` is the sum of the **Dyson series**

  `exp (t (A + B)) = ∑ₙ Dₙ(t)`, `D₀(t) = exp (t A)`,
  `Dₙ₊₁(t) = exp (t A) · ∫₀ᵗ exp (−s A) · B · Dₙ(s) ds`,

the interaction-picture expansion in powers of the interaction. Each term is a primitive of a
continuous matrix-valued function, so the whole construction is ordinary Bochner integration on
`Matrix m m ℂ` under the L2 operator norm; the exponentials of the skew-Hermitian generators are
unitary, so every norm bound is free of growth factors, as in `TrotterProduct.lean` and
`DuhamelBound.lean`.

* `dysonTerm A B n t` — the `n`-th term, `dysonTerm_zero`, `dysonTerm_succ`;
  `continuous_dysonTerm` — each term is continuous in `t`;
* ★ `norm_dysonTerm_le` — `‖Dₙ(t)‖ ≤ (‖B‖ t)ⁿ / n!` for `0 ≤ t`;
* ★ `exp_add_sub_exp_eq` — **the Duhamel identity**,
  `exp (t (A + B)) − exp (t A) = exp (t A) · ∫₀ᵗ exp (−s A) · B · exp (s (A + B)) ds`, by the
  fundamental theorem of calculus on the interpolant `exp (−s A) · exp (s (A + B))`;
* `dysonRemainder A B n t = exp (t (A + B)) − ∑_{k < n} Dₖ(t)`, with
  ★ `dysonRemainder_succ` — the remainder satisfies the same Volterra recursion as the terms,
  and ★ `norm_dysonRemainder_le` — **the truncation error**, `‖Rₙ(t)‖ ≤ (‖B‖ t)ⁿ / n!`;
* ★★ `hasSum_dysonTerm` — **the Dyson series converges to the propagator**,
  `HasSum (fun n => Dₙ(t)) (exp (t (A + B)))`, and `summable_dysonTerm`;
* ★★ `hasSum_dysonTerm_of_isHermitian` — the same for a Hamiltonian `H₀ + V` split into two
  Hermitian parts, generators `−i H₀` and `−i V`: the propagator `exp (−i t (H₀ + V))` is the
  sum of the Dyson series in powers of `V`.

## Honest scope

⚠️ **Finite dimension, forward time.** The bounds and the convergence are stated for `0 ≤ t`
(the identities hold for every `t`). The exponentials are matrix exponentials; nothing here
concerns unbounded generators.

⚠️ **Skew-Hermitian generators.** Skewness is used exactly once per bound, to give the exponential
factors norm one. The recursion and the Duhamel identity hold for arbitrary `A`, `B`; the general
bound would carry `exp (t ‖A‖)`, as `TrotterGeneral.lean` de-skews the product formula.

References: F. J. Dyson, *The radiation theories of Tomonaga, Schwinger, and Feynman*, Phys. Rev.
75, 486 (1949); `Analysis/Matrix/DuhamelBound.lean` (the interpolant and `l2_opNorm_exp_smul_skew`);
`Analysis/Matrix/SumOverPaths.lean` (rung (a) of the same programme); `specs/BACKLOG.md` #36(b);
`specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix Nat Topology
open NormedSpace MeasureTheory intervalIntegral Filter

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-! ### The terms -/

/-- The Dyson terms in the interaction picture: `D₀(t) = exp (t A)` and
`Dₙ₊₁(t) = exp (t A) · ∫₀ᵗ exp (−s A) · B · Dₙ(s) ds`. -/
noncomputable def dysonTerm (A B : Matrix m m ℂ) : ℕ → ℝ → Matrix m m ℂ
  | 0 => fun t => exp (t • A)
  | n + 1 => fun t => exp (t • A) * ∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonTerm A B n s

omit [Nonempty m] in
theorem dysonTerm_zero (A B : Matrix m m ℂ) (t : ℝ) : dysonTerm A B 0 t = exp (t • A) :=
  rfl

omit [Nonempty m] in
theorem dysonTerm_succ (A B : Matrix m m ℂ) (n : ℕ) (t : ℝ) :
    dysonTerm A B (n + 1) t
      = exp (t • A) * ∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonTerm A B n s :=
  rfl

omit [Nonempty m] in
theorem continuous_exp_smul (A : Matrix m m ℂ) : Continuous fun t : ℝ => exp (t • A) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const A t).continuousAt

omit [Nonempty m] in
theorem continuous_exp_neg_smul (A : Matrix m m ℂ) : Continuous fun t : ℝ => exp ((-t) • A) :=
  (continuous_exp_smul A).comp continuous_neg

omit [Nonempty m] in
/-- Each Dyson term is continuous in time. -/
theorem continuous_dysonTerm (A B : Matrix m m ℂ) (n : ℕ) : Continuous (dysonTerm A B n) := by
  induction n with
  | zero => exact continuous_exp_smul A
  | succ n ih =>
    refine (continuous_exp_smul A).mul ?_
    exact intervalIntegral.continuous_primitive
      (fun a b =>
        (((continuous_exp_neg_smul A).mul continuous_const).mul ih).intervalIntegrable a b) 0

/-! ### The bound on the terms -/

/-- ★ `‖Dₙ(t)‖ ≤ (‖B‖ t)ⁿ / n!` for `0 ≤ t` and skew-Hermitian `A`. -/
theorem norm_dysonTerm_le {A : Matrix m m ℂ} (hA : Aᴴ = -A) (B : Matrix m m ℂ) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖dysonTerm A B n t‖ ≤ (‖B‖ * t) ^ n / n ! := by
  induction n generalizing t with
  | zero =>
    rw [dysonTerm_zero, l2_opNorm_exp_smul_skew A hA t]
    simp
  | succ n ih =>
    rw [dysonTerm_succ]
    have hint : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖exp ((-s) • A) * B * dysonTerm A B n s‖ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n !) := by
      intro s hs
      calc ‖exp ((-s) • A) * B * dysonTerm A B n s‖
          ≤ ‖exp ((-s) • A) * B‖ * ‖dysonTerm A B n s‖ := norm_mul_le _ _
        _ ≤ ‖exp ((-s) • A)‖ * ‖B‖ * ‖dysonTerm A B n s‖ := by
            gcongr; exact norm_mul_le _ _
        _ = ‖B‖ * ‖dysonTerm A B n s‖ := by
            rw [l2_opNorm_exp_smul_skew A hA (-s), one_mul]
        _ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n !) := by gcongr; exact ih hs.1
    have hcont : Continuous fun s : ℝ => exp ((-s) • A) * B * dysonTerm A B n s :=
      ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_dysonTerm A B n)
    calc ‖exp (t • A) * ∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonTerm A B n s‖
        ≤ ‖exp (t • A)‖ * ‖∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonTerm A B n s‖ :=
          norm_mul_le _ _
      _ = ‖∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonTerm A B n s‖ := by
          rw [l2_opNorm_exp_smul_skew A hA t, one_mul]
      _ ≤ ∫ s in (0 : ℝ)..t, ‖exp ((-s) • A) * B * dysonTerm A B n s‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, ‖B‖ * ((‖B‖ * s) ^ n / n !) := by
          refine intervalIntegral.integral_mono_on ht (hcont.norm.intervalIntegrable _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _) hint
      _ = (‖B‖ * t) ^ (n + 1) / (n + 1)! := by
          simp_rw [mul_pow, mul_div_assoc]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
          push_cast
          field_simp
          ring

/-! ### The Duhamel identity and the remainder -/

omit [Nonempty m] in
/-- The interpolant `s ↦ exp (−s A) · exp (s (A + B))` has derivative
`exp (−s A) · B · exp (s (A + B))`. -/
theorem hasDerivAt_exp_neg_smul_mul_exp_smul_add (A B : Matrix m m ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => exp ((-u) • A) * exp (u • (A + B)))
      (exp ((-s) • A) * B * exp (s • (A + B))) s := by
  have h1 : HasDerivAt (fun u : ℝ => exp ((-u) • A)) ((-1 : ℝ) • (exp ((-s) • A) * A)) s :=
    (hasDerivAt_exp_smul_const A (-s)).scomp s (hasDerivAt_neg s)
  have h2 : HasDerivAt (fun u : ℝ => exp (u • (A + B))) (exp (s • (A + B)) * (A + B)) s :=
    hasDerivAt_exp_smul_const (A + B) s
  have hmul := h1.mul h2
  have hcomm : exp (s • (A + B)) * (A + B) = (A + B) * exp (s • (A + B)) :=
    (((Commute.refl (A + B)).smul_left s).exp_left).eq
  have hD : (-1 : ℝ) • (exp ((-s) • A) * A) * exp (s • (A + B))
        + exp ((-s) • A) * (exp (s • (A + B)) * (A + B))
      = exp ((-s) • A) * B * exp (s • (A + B)) := by
    rw [neg_one_smul, hcomm]
    noncomm_ring
  exact hD ▸ hmul

omit [Nonempty m] in
/-- ★ **The Duhamel identity.**
`exp (t (A + B)) − exp (t A) = exp (t A) · ∫₀ᵗ exp (−s A) · B · exp (s (A + B)) ds`. -/
theorem exp_add_sub_exp_eq (A B : Matrix m m ℂ) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A)
      = exp (t • A) * ∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * exp (s • (A + B)) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_exp_neg_smul_mul_exp_smul_add A B s)
    ((((continuous_exp_neg_smul A).mul continuous_const).mul
      (continuous_exp_smul (A + B))).intervalIntegrable 0 t)
  have hcancel : exp (t • A) * exp ((-t) • A) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, exp_zero]
  rw [hftc]
  simp only [neg_zero, zero_smul, exp_zero, one_mul]
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcancel, one_mul]

/-- The remainder after `n` terms: `Rₙ(t) = exp (t (A + B)) − ∑_{k < n} Dₖ(t)`. -/
noncomputable def dysonRemainder (A B : Matrix m m ℂ) (n : ℕ) (t : ℝ) : Matrix m m ℂ :=
  exp (t • (A + B)) - ∑ k ∈ Finset.range n, dysonTerm A B k t

omit [Nonempty m] in
theorem dysonRemainder_zero (A B : Matrix m m ℂ) (t : ℝ) :
    dysonRemainder A B 0 t = exp (t • (A + B)) := by
  simp [dysonRemainder]

omit [Nonempty m] in
/-- The remainder is continuous in time. -/
theorem continuous_dysonRemainder (A B : Matrix m m ℂ) (n : ℕ) :
    Continuous (dysonRemainder A B n) :=
  (continuous_exp_smul (A + B)).sub (continuous_finsetSum _ fun k _ => continuous_dysonTerm A B k)

omit [Nonempty m] in
/-- ★ **The remainder obeys the Volterra recursion of the terms**:
`Rₙ₊₁(t) = exp (t A) · ∫₀ᵗ exp (−s A) · B · Rₙ(s) ds`. -/
theorem dysonRemainder_succ (A B : Matrix m m ℂ) (n : ℕ) (t : ℝ) :
    dysonRemainder A B (n + 1) t
      = exp (t • A) * ∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonRemainder A B n s := by
  induction n generalizing t with
  | zero =>
    simp only [dysonRemainder, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      dysonTerm_zero, sub_zero]
    exact exp_add_sub_exp_eq A B t
  | succ n ih =>
    have hsplit : dysonRemainder A B (n + 2) t
        = dysonRemainder A B (n + 1) t - dysonTerm A B (n + 1) t := by
      simp only [dysonRemainder, Finset.sum_range_succ]
      abel
    have hR : ∀ s, dysonRemainder A B (n + 1) s
        = dysonRemainder A B n s - dysonTerm A B n s := by
      intro s
      simp only [dysonRemainder, Finset.sum_range_succ]
      abel
    have hc₁ : Continuous fun s : ℝ => exp ((-s) • A) * B * dysonRemainder A B n s :=
      ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_dysonRemainder A B n)
    have hc₂ : Continuous fun s : ℝ => exp ((-s) • A) * B * dysonTerm A B n s :=
      ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_dysonTerm A B n)
    rw [hsplit, ih, dysonTerm_succ, ← Matrix.mul_sub,
      ← intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _)]
    congr 2
    funext s
    rw [hR s, Matrix.mul_sub]

/-- ★ **The truncation error**: `‖Rₙ(t)‖ ≤ (‖B‖ t)ⁿ / n!` for `0 ≤ t` and skew-Hermitian `A`,
`B`. -/
theorem norm_dysonRemainder_le {A B : Matrix m m ℂ} (hA : Aᴴ = -A) (hB : Bᴴ = -B) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖dysonRemainder A B n t‖ ≤ (‖B‖ * t) ^ n / n ! := by
  induction n generalizing t with
  | zero =>
    have hAB : (A + B)ᴴ = -(A + B) := by rw [conjTranspose_add, hA, hB, neg_add]
    rw [dysonRemainder_zero, l2_opNorm_exp_smul_skew (A + B) hAB t]
    simp
  | succ n ih =>
    rw [dysonRemainder_succ]
    have hint : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖exp ((-s) • A) * B * dysonRemainder A B n s‖ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n !) := by
      intro s hs
      calc ‖exp ((-s) • A) * B * dysonRemainder A B n s‖
          ≤ ‖exp ((-s) • A) * B‖ * ‖dysonRemainder A B n s‖ := norm_mul_le _ _
        _ ≤ ‖exp ((-s) • A)‖ * ‖B‖ * ‖dysonRemainder A B n s‖ := by
            gcongr; exact norm_mul_le _ _
        _ = ‖B‖ * ‖dysonRemainder A B n s‖ := by
            rw [l2_opNorm_exp_smul_skew A hA (-s), one_mul]
        _ ≤ ‖B‖ * ((‖B‖ * s) ^ n / n !) := by gcongr; exact ih hs.1
    have hcont : Continuous fun s : ℝ => exp ((-s) • A) * B * dysonRemainder A B n s :=
      ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_dysonRemainder A B n)
    calc ‖exp (t • A) * ∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonRemainder A B n s‖
        ≤ ‖exp (t • A)‖ * ‖∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonRemainder A B n s‖ :=
          norm_mul_le _ _
      _ = ‖∫ s in (0 : ℝ)..t, exp ((-s) • A) * B * dysonRemainder A B n s‖ := by
          rw [l2_opNorm_exp_smul_skew A hA t, one_mul]
      _ ≤ ∫ s in (0 : ℝ)..t, ‖exp ((-s) • A) * B * dysonRemainder A B n s‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, ‖B‖ * ((‖B‖ * s) ^ n / n !) := by
          refine intervalIntegral.integral_mono_on ht (hcont.norm.intervalIntegrable _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _) hint
      _ = (‖B‖ * t) ^ (n + 1) / (n + 1)! := by
          simp_rw [mul_pow, mul_div_assoc]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
          push_cast
          field_simp
          ring

/-! ### Convergence -/

/-- The Dyson terms are summable. -/
theorem summable_dysonTerm {A : Matrix m m ℂ} (hA : Aᴴ = -A) (B : Matrix m m ℂ) {t : ℝ}
    (ht : 0 ≤ t) : Summable fun n => dysonTerm A B n t :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial (‖B‖ * t))
    fun n => norm_dysonTerm_le hA B n ht

/-- ★★ **The Dyson series converges to the propagator**: for skew-Hermitian `A`, `B` and `0 ≤ t`,
`∑ₙ Dₙ(t) = exp (t (A + B))`. -/
theorem hasSum_dysonTerm {A B : Matrix m m ℂ} (hA : Aᴴ = -A) (hB : Bᴴ = -B) {t : ℝ}
    (ht : 0 ≤ t) : HasSum (fun n => dysonTerm A B n t) (exp (t • (A + B))) := by
  have hsum := (summable_dysonTerm hA B ht).hasSum
  have hlim : Tendsto (fun n => ∑ k ∈ Finset.range n, dysonTerm A B k t) atTop
      (𝓝 (exp (t • (A + B)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (FloorSemiring.tendsto_pow_div_factorial_atTop (‖B‖ * t))
    rw [norm_sub_rev]
    exact norm_dysonRemainder_le hA hB n ht
  rwa [tendsto_nhds_unique hsum.tendsto_sum_nat hlim] at hsum

omit [Fintype m] [DecidableEq m] [Nonempty m] in
/-- For Hermitian `H`, the generator `−i H` is skew-Hermitian. -/
theorem conjTranspose_neg_I_smul_of_isHermitian {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    ((-Complex.I) • H)ᴴ = -((-Complex.I) • H) := by
  rw [Matrix.conjTranspose_smul, hH.eq, ← neg_smul]
  congr 1
  simp

/-- ★★ **The Dyson series of a split Hamiltonian.** For Hermitian `H₀` and `V` and `0 ≤ t`, the
propagator `exp (−i t (H₀ + V))` is the sum of the Dyson series with free generator `−i H₀` and
interaction `−i V`: the expansion in powers of the interaction. -/
theorem hasSum_dysonTerm_of_isHermitian {H₀ V : Matrix m m ℂ} (h₀ : H₀.IsHermitian)
    (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n => dysonTerm ((-Complex.I) • H₀) ((-Complex.I) • V) n t)
      (exp (t • ((-Complex.I) • (H₀ + V)))) := by
  rw [smul_add]
  exact hasSum_dysonTerm (conjTranspose_neg_I_smul_of_isHermitian h₀)
    (conjTranspose_neg_I_smul_of_isHermitian hV) ht

end Matrix
