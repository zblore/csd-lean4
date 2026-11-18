/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelFirstOrder

/-!
# The second-order remainder in terms of the unperturbed orbit

**Category:** 1-Mathlib (CSD-free upstream candidates). BACKLOG #437, third brick (the
return caused at the event; obligation UO-26, assumption UA-19; remainder (b) of the row).

`DuhamelFirstOrder.lean` bounds the second-order remainder by `‖V‖² ‖X‖ t² / 2`, whatever
the state. That bound is not small merely because the unperturbed orbit avoids `V`. Here
the remainder is bounded by the accumulated action of `V` on the unperturbed orbit:

  `‖(e^{tC} − e^{tA}) X − duhamelFirst A (C − A) X t‖ ≤ ‖C − A‖ · (∫₀ᵗ ‖(C − A) e^{sA} X‖ ds) · t`.

So before the unperturbed orbit reaches the place where `V` acts, both the first-order term
and the remainder are small, and after it the remainder is the first-order bound times
`‖V‖ t`.

* `continuous_norm_mul_exp_smul_mul`, `integral_norm_mul_exp_smul_mul_mono`;
* ★★ `norm_duhamelKernel_le_integral` (`‖∫₀ᵗ e^{−sA} W e^{sA} X ds‖ ≤ ∫₀ᵗ ‖W e^{sA} X‖ ds`);
* ★★★ `norm_exp_sub_exp_mul_sub_duhamelFirst_le_orbit` (skew-Hermitian `C`, `A`);
* ★★★ `norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit` (Hermitian `H₀`, `V`);
* ★★★ `le_norm_mul_exp_neg_I_add_mul_orbit` (when `Q e^{−itH₀} X = 0`:
  `‖Q · duhamelFirst‖ − ‖Q‖ ‖V‖ (∫₀ᵗ ‖V e^{−isH₀} X‖ ds) t ≤ ‖Q e^{−it(H₀+V)} X‖`).

## Honest scope

⚠️ **The first-order term is still not evaluated.** No launch is shown for any choice of
`H₀`, `V`, `X`, `Q`.

⚠️ **Relative to the first-order bound the remainder is `‖V‖ t`.** It is the smaller one only
for `‖V‖ t < 1`: weak coupling or short times after the meeting. Nothing beyond first order.

⚠️ **`t ≥ 0`, square `X`, the L2 operator norm. No model**: no carrier, coupling or arena.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-211, UD-212, UD-216); `DuhamelFirstOrder.lean` (`duhamelFirst`, `duhamelKernel`,
`hasDerivAt_duhamelRemainder`, `duhamelRemainder_eq`,
`norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le`); `DuhamelState.lean`
(`norm_exp_neg_I_add_sub_mul_le`); `specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- What the perturbation does to the unperturbed orbit of `X` is continuous in the time. -/
theorem continuous_norm_mul_exp_smul_mul (A W X : Matrix m m ℂ) :
    Continuous fun s : ℝ => ‖W * exp (s • A) * X‖ :=
  ((continuous_const.mul (continuous_exp_smul A)).mul continuous_const).norm

omit [Nonempty m] in
/-- **The accumulated action of `W` on the unperturbed orbit grows with the time.** -/
theorem integral_norm_mul_exp_smul_mul_mono (A W X : Matrix m m ℂ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    ∫ r in (0 : ℝ)..s, ‖W * exp (r • A) * X‖ ≤ ∫ r in (0 : ℝ)..t, ‖W * exp (r • A) * X‖ :=
  intervalIntegral.integral_mono_interval le_rfl hs hst
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((continuous_norm_mul_exp_smul_mul A W X).intervalIntegrable _ _)

/-- ★★ **The first-order term is at most the accumulated action of `W` on the unperturbed
orbit**: `‖∫₀ᵗ e^{−sA} W e^{sA} X ds‖ ≤ ∫₀ᵗ ‖W e^{sA} X‖ ds`, for `t ≥ 0`. -/
theorem norm_duhamelKernel_le_integral (A W X : Matrix m m ℂ) (hA : Aᴴ = -A) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖duhamelKernel A W X t‖ ≤ ∫ s in (0 : ℝ)..t, ‖W * exp (s • A) * X‖ := by
  unfold duhamelKernel
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
  refine intervalIntegral.integral_mono_on ht
    ((continuous_duhamelIntegrand A W X).norm.intervalIntegrable _ _)
    ((continuous_norm_mul_exp_smul_mul A W X).intervalIntegrable _ _) fun s _ => ?_
  calc ‖exp ((-s) • A) * W * exp (s • A) * X‖
      = ‖exp ((-s) • A) * (W * exp (s • A) * X)‖ := by simp only [mul_assoc]
    _ ≤ ‖exp ((-s) • A)‖ * ‖W * exp (s • A) * X‖ := norm_mul_le _ _
    _ = ‖W * exp (s • A) * X‖ := by rw [l2_opNorm_exp_smul_skew A hA (-s), one_mul]

/-- ★★★ **The second-order remainder is small when the unperturbed orbit avoids the
perturbation.** For skew-Hermitian `C`, `A`, any `X` and `t ≥ 0`,

  `‖(exp (t • C) − exp (t • A)) X − duhamelFirst A (C − A) X t‖`
  `  ≤ ‖C − A‖ · (∫₀ᵗ ‖(C − A) exp (s • A) X‖ ds) · t`. -/
theorem norm_exp_sub_exp_mul_sub_duhamelFirst_le_orbit (C A X : Matrix m m ℂ)
    (hC : Cᴴ = -C) (hA : Aᴴ = -A) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • C) - exp (t • A)) * X - duhamelFirst A (C - A) X t‖
      ≤ ‖C - A‖ * (∫ s in (0 : ℝ)..t, ‖(C - A) * exp (s • A) * X‖) * t := by
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖exp ((-s) • C) * ((C - A) * exp (s • A) * duhamelKernel A (C - A) X s)‖
        ≤ ‖C - A‖ * ∫ r in (0 : ℝ)..t, ‖(C - A) * exp (r • A) * X‖ := by
    intro s hs
    calc ‖exp ((-s) • C) * ((C - A) * exp (s • A) * duhamelKernel A (C - A) X s)‖
        ≤ ‖exp ((-s) • C)‖ * (‖C - A‖ * ‖exp (s • A)‖ * ‖duhamelKernel A (C - A) X s‖) := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ = ‖C - A‖ * ‖duhamelKernel A (C - A) X s‖ := by
          rw [l2_opNorm_exp_smul_skew C hC (-s), l2_opNorm_exp_smul_skew A hA s, one_mul,
            mul_one]
      _ ≤ ‖C - A‖ * ∫ r in (0 : ℝ)..t, ‖(C - A) * exp (r • A) * X‖ :=
          mul_le_mul_of_nonneg_left
            ((norm_duhamelKernel_le_integral A (C - A) X hA hs.1).trans
              (integral_norm_mul_exp_smul_mul_mono A (C - A) X hs.1 hs.2.le))
            (norm_nonneg _)
  have hB : ∀ x : ℝ, HasDerivAt
      (fun u : ℝ => ‖C - A‖ * (∫ r in (0 : ℝ)..t, ‖(C - A) * exp (r • A) * X‖) * u)
      (‖C - A‖ * ∫ r in (0 : ℝ)..t, ‖(C - A) * exp (r • A) * X‖) x := fun x => by
    simpa using (hasDerivAt_id x).const_mul
      (‖C - A‖ * ∫ r in (0 : ℝ)..t, ‖(C - A) * exp (r • A) * X‖)
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun u : ℝ => X - exp ((-u) • C) * exp (u • A) * (X + duhamelKernel A (C - A) X u))
    (a := 0) (b := t)
    (fun x _ => (hasDerivAt_duhamelRemainder C A X x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_duhamelRemainder C A X x).hasDerivWithinAt)
    (B := fun u : ℝ => ‖C - A‖ * (∫ r in (0 : ℝ)..t, ‖(C - A) * exp (r • A) * X‖) * u)
    (by simp [duhamelKernel]) hB hbound (Set.right_mem_Icc.2 ht)
  rw [duhamelRemainder_eq]
  refine (norm_mul_le _ _).trans ?_
  rw [l2_opNorm_exp_smul_skew C hC t, one_mul]
  exact hmain

/-- ★★★ **The same for Hamiltonians**: for Hermitian `H₀`, `V`, any `X` and `t ≥ 0`, the
perturbed evolution of `X` is the unperturbed one plus the first-order term of `−iV`, within
`‖V‖ · (∫₀ᵗ ‖V e^{−isH₀} X‖ ds) · t`. -/
theorem norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit (H₀ V X : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + V))) - exp (t • ((-Complex.I) • H₀))) * X
        - duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t‖
      ≤ ‖V‖ * (∫ s in (0 : ℝ)..t, ‖V * exp (s • ((-Complex.I) • H₀)) * X‖) * t := by
  have h := norm_exp_sub_exp_mul_sub_duhamelFirst_le_orbit ((-Complex.I) • (H₀ + V))
    ((-Complex.I) • H₀) X (conjTranspose_neg_I_smul (hH₀.add hV))
    (conjTranspose_neg_I_smul hH₀) ht
  have hdiff : (-Complex.I) • (H₀ + V) - (-Complex.I) • H₀ = (-Complex.I) • V := by
    rw [smul_add, add_sub_cancel_left]
  have hn : ∀ s : ℝ, ‖(-Complex.I) • V * exp (s • ((-Complex.I) • H₀)) * X‖
      = ‖V * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [smul_mul_assoc, smul_mul_assoc, norm_smul, norm_neg, Complex.norm_I, one_mul]
  rw [hdiff, norm_smul, norm_neg, Complex.norm_I, one_mul] at h
  simpa only [hn] using h

/-- ★★★ **What reaches a sector the unperturbed orbit avoids, with the remainder in terms of
the orbit**: for Hermitian `H₀`, `V` and `Q` with `Q e^{−itH₀} X = 0`, `t ≥ 0`,

  `‖Q · duhamelFirst‖ − ‖Q‖ ‖V‖ (∫₀ᵗ ‖V e^{−isH₀} X‖ ds) t ≤ ‖Q exp (−i t (H₀ + V)) X‖`. -/
theorem le_norm_mul_exp_neg_I_add_mul_orbit (H₀ V X Q : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    (hQ : Q * exp (t • ((-Complex.I) • H₀)) * X = 0) :
    ‖Q * duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t‖
        - ‖Q‖ * (‖V‖ * (∫ s in (0 : ℝ)..t, ‖V * exp (s • ((-Complex.I) • H₀)) * X‖) * t)
      ≤ ‖Q * exp (t • ((-Complex.I) • (H₀ + V))) * X‖ := by
  have hsplit : Q * duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t
      = Q * exp (t • ((-Complex.I) • (H₀ + V))) * X
        - Q * ((exp (t • ((-Complex.I) • (H₀ + V))) - exp (t • ((-Complex.I) • H₀))) * X
          - duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t) := by
    rw [mul_sub, sub_mul, mul_sub, ← mul_assoc, ← mul_assoc, hQ]
    noncomm_ring
  have h1 := norm_sub_le (Q * exp (t • ((-Complex.I) • (H₀ + V))) * X)
    (Q * ((exp (t • ((-Complex.I) • (H₀ + V))) - exp (t • ((-Complex.I) • H₀))) * X
      - duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t))
  have h2 := (norm_mul_le Q _).trans (mul_le_mul_of_nonneg_left
    (norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit H₀ V X hH₀ hV ht) (norm_nonneg Q))
  rw [← hsplit] at h1
  linarith

end Matrix
