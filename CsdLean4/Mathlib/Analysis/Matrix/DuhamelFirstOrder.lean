/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelState

/-!
# The first-order term of a perturbed group

**Category:** 1-Mathlib (CSD-free upstream candidates). BACKLOG #437, second brick (the
return caused at the event; obligation UO-26, assumption UA-19).

`DuhamelState.lean` bounds from above what a perturbation moves off the unperturbed orbit.
Here the moved part is identified to first order, with a remainder of second order:

  `‖(e^{tC} − e^{tA}) X − ∫₀ᵗ e^{(t−s)A} (C − A) e^{sA} X ds‖ ≤ ‖C − A‖² ‖X‖ t² / 2`,  `t ≥ 0`.

So the perturbed orbit is the unperturbed one plus what the perturbation launches from it at
each time `s`, carried on by the unperturbed group. The integral is written in the
interaction picture, `e^{tA} ∫₀ᵗ e^{−sA} (C − A) e^{sA} X ds`, which has a derivative by the
fundamental theorem; the remainder is compared with `t²/2` by
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`.

* `exp_smul_mul_exp_neg_smul`, `duhamelKernel`, ★ `duhamelFirst`,
  `continuous_duhamelIntegrand`, `hasDerivAt_duhamelKernel`, `norm_duhamelKernel_le`,
  `norm_duhamelFirst_le` (`≤ ‖W‖ ‖X‖ |t|`);
* `hasDerivAt_duhamelRemainder`, `duhamelRemainder_eq` (the interpolant of the remainder and
  its derivative; shared with `DuhamelOrbitRemainder.lean`);
* ★★★ `norm_exp_sub_exp_mul_sub_duhamelFirst_le` (skew-Hermitian `C`, `A`);
* `conjTranspose_neg_I_smul`, ★★★ `norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le` (Hermitian
  `H₀`, `V`: remainder `‖V‖² ‖X‖ t² / 2`);
* ★★★ `le_norm_mul_exp_neg_I_add_mul` (**something does reach the sector**: when `Q`
  annihilates the unperturbed orbit at `t`,
  `‖Q · duhamelFirst‖ − ‖Q‖ ‖V‖² ‖X‖ t² / 2 ≤ ‖Q e^{−it(H₀+V)} X‖`).

## Honest scope

⚠️ **The first-order term is not evaluated.** `le_norm_mul_exp_neg_I_add_mul` is a lower bound
in terms of `‖Q · duhamelFirst‖`. For no `H₀`, `V`, `X`, `Q` is that norm computed or shown
positive here. Until it is, nothing is shown to be launched.

⚠️ **Useful only for weak coupling or short times.** With `V = g V₁` the first-order term is
proportional to `g` and the remainder to `g² t²`. Where the bound says anything, the launched
part is small.

⚠️ **The remainder uses `‖V‖`, not the orbit.** Unlike the first-order bound of
`DuhamelState.lean`, the remainder is not small merely because the unperturbed orbit avoids
`V`. A remainder in terms of the orbit is not here.

⚠️ **`t ≥ 0`, square `X`, the L2 operator norm. No model**: no carrier, coupling or arena.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-211, UD-212); `specs/unified-m7-feasibility.md` (§4, §7); `DuhamelState.lean`
(`norm_exp_neg_I_add_sub_mul_le`, `norm_mul_exp_neg_I_add_mul_le`, `continuous_exp_smul`);
`DuhamelBound.lean` (`l2_opNorm_exp_smul_skew`); `DysonSeries.lean`; `specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- The group of `A` at `s` and at `−s` are inverse. -/
theorem exp_smul_mul_exp_neg_smul (A : Matrix m m ℂ) (s : ℝ) :
    exp (s • A) * exp ((-s) • A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right (-s)),
    ← add_smul, add_neg_cancel, zero_smul, exp_zero]

/-- **The first-order term in the interaction picture**: `∫₀ᵗ e^{−sA} W e^{sA} X ds`. -/
noncomputable def duhamelKernel (A W X : Matrix m m ℂ) (t : ℝ) : Matrix m m ℂ :=
  ∫ s in (0 : ℝ)..t, exp ((-s) • A) * W * exp (s • A) * X

/-- ★ **The first-order term of the perturbed group** applied to `X`:
`e^{tA} ∫₀ᵗ e^{−sA} W e^{sA} X ds = ∫₀ᵗ e^{(t−s)A} W e^{sA} X ds`. What `W` does to the
unperturbed orbit at each time `s`, carried on by the unperturbed group. -/
noncomputable def duhamelFirst (A W X : Matrix m m ℂ) (t : ℝ) : Matrix m m ℂ :=
  exp (t • A) * duhamelKernel A W X t

omit [Nonempty m] in
theorem continuous_duhamelIntegrand (A W X : Matrix m m ℂ) :
    Continuous fun s : ℝ => exp ((-s) • A) * W * exp (s • A) * X :=
  (((((continuous_exp_smul A).comp continuous_neg).mul continuous_const).mul
    (continuous_exp_smul A)).mul continuous_const)

omit [Nonempty m] in
theorem hasDerivAt_duhamelKernel (A W X : Matrix m m ℂ) (s : ℝ) :
    HasDerivAt (duhamelKernel A W X) (exp ((-s) • A) * W * exp (s • A) * X) s :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_duhamelIntegrand A W X).intervalIntegrable _ _)
    ((continuous_duhamelIntegrand A W X).stronglyMeasurableAtFilter _ _)
    (continuous_duhamelIntegrand A W X).continuousAt

/-- The first-order term is at most `|t| ‖W‖ ‖X‖`. -/
theorem norm_duhamelKernel_le (A W X : Matrix m m ℂ) (hA : Aᴴ = -A) (t : ℝ) :
    ‖duhamelKernel A W X t‖ ≤ ‖W‖ * ‖X‖ * |t| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := ‖W‖ * ‖X‖)
    (f := fun s : ℝ => exp ((-s) • A) * W * exp (s • A) * X) fun s _ => by
      calc ‖exp ((-s) • A) * W * exp (s • A) * X‖
          ≤ ‖exp ((-s) • A)‖ * ‖W‖ * ‖exp (s • A)‖ * ‖X‖ := by
            refine (norm_mul_le _ _).trans ?_
            gcongr
            refine (norm_mul_le _ _).trans ?_
            gcongr
            exact norm_mul_le _ _
        _ = ‖W‖ * ‖X‖ := by
            rw [l2_opNorm_exp_smul_skew A hA (-s), l2_opNorm_exp_smul_skew A hA s, one_mul,
              mul_one]
  rwa [sub_zero] at h

theorem norm_duhamelFirst_le (A W X : Matrix m m ℂ) (hA : Aᴴ = -A) (t : ℝ) :
    ‖duhamelFirst A W X t‖ ≤ ‖W‖ * ‖X‖ * |t| := by
  refine (norm_mul_le _ _).trans ?_
  rw [l2_opNorm_exp_smul_skew A hA t, one_mul]
  exact norm_duhamelKernel_le A W X hA t

omit [Nonempty m] in
/-- **The interpolant of the remainder and its derivative.** With `K` the first-order term in
the interaction picture, `X − e^{−sC} e^{sA} (X + K s)` has derivative
`e^{−sC} (C − A) e^{sA} K s`. -/
theorem hasDerivAt_duhamelRemainder (C A X : Matrix m m ℂ) (s : ℝ) :
    HasDerivAt
      (fun u : ℝ => X - exp ((-u) • C) * exp (u • A) * (X + duhamelKernel A (C - A) X u))
      (exp ((-s) • C) * ((C - A) * exp (s • A) * duhamelKernel A (C - A) X s)) s := by
  have hneg : HasDerivAt (fun u : ℝ => -u) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 0
  have h1 : HasDerivAt (fun u : ℝ => exp ((-u) • C))
      ((-1 : ℝ) • (exp ((-s) • C) * C)) s :=
    (hasDerivAt_exp_smul_const C (-s)).scomp s hneg
  have h2 : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
    hasDerivAt_exp_smul_const A s
  have h3 : HasDerivAt (fun u : ℝ => X + duhamelKernel A (C - A) X u)
      (exp ((-s) • A) * (C - A) * exp (s • A) * X) s :=
    (hasDerivAt_duhamelKernel A (C - A) X s).const_add X
  have h4 := ((h1.mul h2).mul h3).const_sub X
  have hcomm : exp (s • A) * A = A * exp (s • A) :=
    (((Commute.refl A).smul_left s).exp_left).eq
  have hinv : exp ((-s) • C) * exp (s • A) * (exp ((-s) • A) * (C - A) * exp (s • A) * X)
      = exp ((-s) • C) * ((C - A) * exp (s • A) * X) := by
    rw [mul_assoc (exp ((-s) • C)) (exp (s • A))]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, exp_smul_mul_exp_neg_smul, one_mul]
  refine h4.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [hinv, neg_one_smul, hcomm]
  noncomm_ring

omit [Nonempty m] in
/-- **The remainder is the perturbed group applied to the interpolant.** -/
theorem duhamelRemainder_eq (C A X : Matrix m m ℂ) (t : ℝ) :
    (exp (t • C) - exp (t • A)) * X - duhamelFirst A (C - A) X t
      = exp (t • C)
        * (X - exp ((-t) • C) * exp (t • A) * (X + duhamelKernel A (C - A) X t)) := by
  have e : exp (t • C) * (exp ((-t) • C) * exp (t • A) * (X + duhamelKernel A (C - A) X t))
      = exp (t • A) * (X + duhamelKernel A (C - A) X t) := by
    rw [← mul_assoc, ← mul_assoc, exp_smul_mul_exp_neg_smul, one_mul]
  rw [mul_sub, e, duhamelFirst]
  noncomm_ring

/-- ★★★ **The perturbed group to first order, with a second-order remainder.** For
skew-Hermitian `C`, `A`, any `X` and `t ≥ 0`,

  `‖(exp (t • C) − exp (t • A)) X − duhamelFirst A (C − A) X t‖ ≤ ‖C − A‖² ‖X‖ t² / 2`. -/
theorem norm_exp_sub_exp_mul_sub_duhamelFirst_le (C A X : Matrix m m ℂ)
    (hC : Cᴴ = -C) (hA : Aᴴ = -A) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • C) - exp (t • A)) * X - duhamelFirst A (C - A) X t‖
      ≤ ‖C - A‖ ^ 2 * ‖X‖ / 2 * t ^ 2 := by
  set K : ℝ → Matrix m m ℂ := duhamelKernel A (C - A) X with hK
  set f : ℝ → Matrix m m ℂ := fun s =>
    X - exp ((-s) • C) * exp (s • A) * (X + K s) with hf
  have hderiv : ∀ s : ℝ,
      HasDerivAt f (exp ((-s) • C) * ((C - A) * exp (s • A) * K s)) s :=
    fun s => hasDerivAt_duhamelRemainder C A X s
  have hKb : ∀ s : ℝ, 0 ≤ s → ‖K s‖ ≤ ‖C - A‖ * ‖X‖ * s := fun s hs => by
    have := norm_duhamelKernel_le A (C - A) X hA s
    rwa [abs_of_nonneg hs] at this
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖exp ((-s) • C) * ((C - A) * exp (s • A) * K s)‖ ≤ ‖C - A‖ ^ 2 * ‖X‖ * s := by
    intro s hs
    calc ‖exp ((-s) • C) * ((C - A) * exp (s • A) * K s)‖
        ≤ ‖exp ((-s) • C)‖ * (‖C - A‖ * ‖exp (s • A)‖ * ‖K s‖) := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ = ‖C - A‖ * ‖K s‖ := by
          rw [l2_opNorm_exp_smul_skew C hC (-s), l2_opNorm_exp_smul_skew A hA s, one_mul,
            mul_one]
      _ ≤ ‖C - A‖ * (‖C - A‖ * ‖X‖ * s) :=
          mul_le_mul_of_nonneg_left (hKb s hs.1) (norm_nonneg _)
      _ = ‖C - A‖ ^ 2 * ‖X‖ * s := by ring
  have hB : ∀ x : ℝ, HasDerivAt (fun u : ℝ => ‖C - A‖ ^ 2 * ‖X‖ / 2 * u ^ 2)
      (‖C - A‖ ^ 2 * ‖X‖ * x) x := fun x => by
    have h := (hasDerivAt_pow 2 x).const_mul (‖C - A‖ ^ 2 * ‖X‖ / 2)
    refine h.congr_deriv ?_
    norm_num
    ring
  have hK0 : K 0 = 0 := by
    simp [hK, duhamelKernel]
  have hf0 : f 0 = 0 := by
    simp [hf, hK0]
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := f) (a := 0) (b := t)
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
    (fun x _ => (hderiv x).hasDerivWithinAt)
    (B := fun u : ℝ => ‖C - A‖ ^ 2 * ‖X‖ / 2 * u ^ 2)
    (by simp [hf0]) hB hbound (Set.right_mem_Icc.2 ht)
  have hR := duhamelRemainder_eq C A X t
  rw [hR]
  refine (norm_mul_le _ _).trans ?_
  rw [l2_opNorm_exp_smul_skew C hC t, one_mul]
  exact hmain

omit [Fintype m] [DecidableEq m] [Nonempty m] in
/-- `−i` times a Hermitian matrix is skew-Hermitian. -/
theorem conjTranspose_neg_I_smul {M : Matrix m m ℂ} (hM : M.IsHermitian) :
    ((-Complex.I) • M)ᴴ = -((-Complex.I) • M) := by
  have hstar : star (-Complex.I) = Complex.I := by simp
  rw [Matrix.conjTranspose_smul, hM.eq, hstar, ← neg_smul, neg_neg]

/-- ★★★ **The same for Hamiltonians**: for Hermitian `H₀`, `V`, any `X` and `t ≥ 0`, the
perturbed evolution of `X` is the unperturbed one plus the first-order term of `−iV`, within
`‖V‖² ‖X‖ t² / 2`. -/
theorem norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le (H₀ V X : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + V))) - exp (t • ((-Complex.I) • H₀))) * X
        - duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t‖
      ≤ ‖V‖ ^ 2 * ‖X‖ / 2 * t ^ 2 := by
  have h := norm_exp_sub_exp_mul_sub_duhamelFirst_le ((-Complex.I) • (H₀ + V))
    ((-Complex.I) • H₀) X (conjTranspose_neg_I_smul (hH₀.add hV))
    (conjTranspose_neg_I_smul hH₀) ht
  have hdiff : (-Complex.I) • (H₀ + V) - (-Complex.I) • H₀ = (-Complex.I) • V := by
    rw [smul_add, add_sub_cancel_left]
  rw [hdiff, norm_smul, norm_neg, Complex.norm_I, one_mul] at h
  exact h

/-- ★★★ **Something does reach the sector**: for Hermitian `H₀`, `V`, a `Q` that annihilates
the unperturbed orbit of `X` at the time `t ≥ 0`, the part of the perturbed orbit under `Q` is
at least the first-order term's less the second-order remainder,

  `‖Q · duhamelFirst‖ − ‖Q‖ ‖V‖² ‖X‖ t² / 2 ≤ ‖Q exp (−i t (H₀ + V)) X‖`. -/
theorem le_norm_mul_exp_neg_I_add_mul (H₀ V X Q : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    (hQ : Q * exp (t • ((-Complex.I) • H₀)) * X = 0) :
    ‖Q * duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • V) X t‖
        - ‖Q‖ * (‖V‖ ^ 2 * ‖X‖ / 2 * t ^ 2)
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
    (norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le H₀ V X hH₀ hV ht) (norm_nonneg Q))
  rw [← hsplit] at h1
  linarith

end Matrix
