/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound

/-!
# The Duhamel bound on a prepared subspace

**Category:** 1-Mathlib (CSD-free upstream candidates). BACKLOG #437, first brick (the return
caused at the event; obligation UO-26).

`DuhamelBound.lean` prices a perturbation in the operator norm: `‖e^{tC} − e^{tA}‖ ≤ |t| ‖C − A‖`,
whatever the state. Here the price is paid only along the unperturbed orbit of what was
prepared:

  `‖(e^{tC} − e^{tA}) X‖ ≤ ∫₀ᵗ ‖(C − A) e^{sA} X‖ ds`,  `t ≥ 0`.

If the unperturbed orbit of `X` stays where the perturbation vanishes, the perturbed orbit is
the unperturbed one. Proved without operator-valued integrals: the interpolant
`e^{(t−s)C} e^{sA} X` has derivative of norm at most the integrand, and
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` compares it with the integral.

* `continuous_exp_smul`;
* ★★ `norm_exp_smul_sub_exp_smul_mul_le` (`C` skew-Hermitian; `A` and `X` any);
* ★★ `norm_exp_neg_I_add_sub_mul_le` (Hermitian `H₀`, `V`:
  `‖(e^{−it(H₀+V)} − e^{−itH₀}) X‖ ≤ ∫₀ᵗ ‖V e^{−isH₀} X‖ ds`);
* ★★★ `norm_mul_exp_neg_I_add_mul_le` (**nothing reaches a sector the unperturbed orbit
  avoids, except through the perturbation acting on that orbit**:
  `‖Q e^{−it(H₀+V)} X‖ ≤ ‖Q‖ ∫₀ᵗ ‖V e^{−isH₀} X‖ ds` when `Q e^{−itH₀} X = 0`).

## Honest scope

⚠️ **An upper bound.** It says how little can be transferred. It does not say that anything
is. The matching statement, that the transferred part is `−i ∫₀ᵗ e^{−i(t−s)H₀} V e^{−isH₀} X ds`
up to second order in `V`, is not here.

⚠️ **`t ≥ 0`, square `X`, the L2 operator norm.** `X` stands for the prepared subspace: a
projector, or the rank-one matrix of a state.

⚠️ **No model.** No carrier, coupling or arena appears. Its intended use (UO-26) is for `V` a
contact term between two carriers, where the integrand is the unperturbed orbit's weight at
a meeting; that use is not made here.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UO-17, UO-26,
UD-211); `specs/unified-m7-feasibility.md` (§4, §7); `DuhamelBound.lean`
(`norm_exp_smul_sub_exp_smul_le`, `l2_opNorm_exp_smul_skew`); `CV/InteractionPrice.lean`;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- The unperturbed group is continuous in its parameter. -/
theorem continuous_exp_smul (A : Matrix m m ℂ) : Continuous fun s : ℝ => exp (s • A) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_const A s).continuousAt

/-- ★★ **The Duhamel bound on a prepared subspace.** For a skew-Hermitian generator `C`, any
`A` and `X`, and `t ≥ 0`,

  `‖(exp (t • C) − exp (t • A)) X‖ ≤ ∫₀ᵗ ‖(C − A) exp (s • A) X‖ ds`.

The perturbation enters only through what it does to the unperturbed orbit of `X`. -/
theorem norm_exp_smul_sub_exp_smul_mul_le (C A X : Matrix m m ℂ)
    (hC : Cᴴ = -C) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • C) - exp (t • A)) * X‖
      ≤ ∫ s in (0 : ℝ)..t, ‖(C - A) * exp (s • A) * X‖ := by
  set f : ℝ → Matrix m m ℂ := fun s =>
    exp ((t - s) • C) * exp (s • A) * X - exp (t • C) * X with hf
  set g : ℝ → ℝ := fun s => ‖(C - A) * exp (s • A) * X‖ with hg
  have hderiv : ∀ s : ℝ,
      HasDerivAt f (-(exp ((t - s) • C) * ((C - A) * exp (s • A) * X))) s := by
    intro s
    have hsub : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h1 : HasDerivAt (fun u : ℝ => exp ((t - u) • C))
        ((-1 : ℝ) • (exp ((t - s) • C) * C)) s :=
      (hasDerivAt_exp_smul_const C (t - s)).scomp s hsub
    have h2 : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have h3 := ((h1.mul h2).mul_const X).sub_const (exp (t • C) * X)
    have hcomm : exp (s • A) * A = A * exp (s • A) :=
      (((Commute.refl A).smul_left s).exp_left).eq
    have hD : ((-1 : ℝ) • (exp ((t - s) • C) * C) * exp (s • A)
          + exp ((t - s) • C) * (exp (s • A) * A)) * X
        = -(exp ((t - s) • C) * ((C - A) * exp (s • A) * X)) := by
      rw [neg_one_smul, hcomm]
      noncomm_ring
    exact hD ▸ h3
  have hbound : ∀ s : ℝ, ‖-(exp ((t - s) • C) * ((C - A) * exp (s • A) * X))‖ ≤ g s := by
    intro s
    rw [norm_neg]
    calc ‖exp ((t - s) • C) * ((C - A) * exp (s • A) * X)‖
        ≤ ‖exp ((t - s) • C)‖ * ‖(C - A) * exp (s • A) * X‖ := norm_mul_le _ _
      _ = g s := by rw [l2_opNorm_exp_smul_skew C hC (t - s), one_mul]
  have hgc : Continuous g :=
    ((continuous_const.mul (continuous_exp_smul A)).mul continuous_const).norm
  have hB : ∀ x : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, g s) (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  have hf0 : f 0 = 0 := by
    simp [hf]
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := f) (a := 0) (b := t)
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
    (fun x _ => (hderiv x).hasDerivWithinAt)
    (B := fun u : ℝ => ∫ s in (0 : ℝ)..u, g s)
    (by simp [hf0]) hB (fun x _ => hbound x) (Set.right_mem_Icc.2 ht)
  have hft : f t = -((exp (t • C) - exp (t • A)) * X) := by
    simp only [hf, sub_self, zero_smul, exp_zero, one_mul]
    noncomm_ring
  rw [hft, norm_neg] at hmain
  exact hmain

/-- ★★ **The same for Hamiltonians**: for Hermitian `H₀` and `V`, any `X` and `t ≥ 0`,

  `‖(exp (−i t (H₀ + V)) − exp (−i t H₀)) X‖ ≤ ∫₀ᵗ ‖V exp (−i s H₀) X‖ ds`. -/
theorem norm_exp_neg_I_add_sub_mul_le (H₀ V X : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + V))) - exp (t • ((-Complex.I) • H₀))) * X‖
      ≤ ∫ s in (0 : ℝ)..t, ‖V * exp (s • ((-Complex.I) • H₀)) * X‖ := by
  have hskew : ∀ (M : Matrix m m ℂ), M.IsHermitian →
      ((-Complex.I) • M)ᴴ = -((-Complex.I) • M) := by
    intro M hM
    have hstar : star (-Complex.I) = Complex.I := by simp
    rw [Matrix.conjTranspose_smul, hM.eq, hstar, ← neg_smul, neg_neg]
  have h := norm_exp_smul_sub_exp_smul_mul_le ((-Complex.I) • (H₀ + V)) ((-Complex.I) • H₀) X
    (hskew _ (hH₀.add hV)) ht
  have hdiff : (-Complex.I) • (H₀ + V) - (-Complex.I) • H₀ = (-Complex.I) • V := by
    rw [smul_add, add_sub_cancel_left]
  have hn : ∀ s : ℝ, ‖(-Complex.I) • V * exp (s • ((-Complex.I) • H₀)) * X‖
      = ‖V * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [smul_mul_assoc, smul_mul_assoc, norm_smul, norm_neg, Complex.norm_I, one_mul]
  rw [hdiff] at h
  simpa only [hn] using h

/-- ★★★ **Nothing reaches a sector the unperturbed orbit avoids, except through the
perturbation acting on that orbit.** For Hermitian `H₀` and `V`, a `Q` that annihilates the
unperturbed orbit of `X` at the time `t ≥ 0`,

  `‖Q exp (−i t (H₀ + V)) X‖ ≤ ‖Q‖ ∫₀ᵗ ‖V exp (−i s H₀) X‖ ds`. -/
theorem norm_mul_exp_neg_I_add_mul_le (H₀ V X Q : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    (hQ : Q * exp (t • ((-Complex.I) • H₀)) * X = 0) :
    ‖Q * exp (t • ((-Complex.I) • (H₀ + V))) * X‖
      ≤ ‖Q‖ * ∫ s in (0 : ℝ)..t, ‖V * exp (s • ((-Complex.I) • H₀)) * X‖ := by
  have hsplit : Q * exp (t • ((-Complex.I) • (H₀ + V))) * X
      = Q * ((exp (t • ((-Complex.I) • (H₀ + V))) - exp (t • ((-Complex.I) • H₀))) * X) := by
    rw [sub_mul, mul_sub, ← mul_assoc, ← mul_assoc, hQ, sub_zero]
  rw [hsplit]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_exp_neg_I_add_sub_mul_le H₀ V X hH₀ hV ht) (norm_nonneg _))

end Matrix
