/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.StoneC1

/-!
# The Duhamel bound: unitary groups of nearby generators stay close

**Category:** 1-Mathlib (CSD-free upstream candidates).

For skew-Hermitian generators `C, A` on a finite-dimensional Hilbert space,

  `‖exp (t • C) − exp (t • A)‖ ≤ |t| · ‖C − A‖`

in the L2 operator norm. The classical Duhamel-formula estimate, here proved without integrals: the
interpolant `φ(s) = exp (s • C) · exp ((t−s) • A)` has endpoints `exp (t • C)` and `exp (t • A)`,
its derivative is `exp (s • C) · (C − A) · exp ((t−s) • A)` — norm at most `‖C − A‖`, the two
exponential factors being **unitary** — and the mean-value inequality
(`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) does the rest.

This is the quantitative engine of A5 (`(ε,T)`-projectability): a Hamiltonian `ε`-close in operator
norm to a sector-projectable one generates dynamics that the sector dynamics **shadows** to within
`ε·T` over the time window `[−T, T]`. Consumed by `SigmaLayer/ApproxProjectability.lean`.

## Provenance

Staged as upstream Mathlib material; no `CsdLean4`-namespace content beyond the `Matrix.StoneC1`
unitarity input. Generalized 2026-08-07 from `Fin n` to an arbitrary finite index (the CV pricing
route, CV-9, needs it at `FieldConfig K N`): every ingredient — `exp_conjTranspose`,
`exp_add_of_commute`, `hasDerivAt_exp_smul_const`, the scoped C*-instances, the mean-value
inequality — is index-generic, so the unitarity input is inlined and `[NeZero n]` becomes
`[Nonempty m]`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Fintype m] [DecidableEq m] [Nonempty m] in
/-- Real scaling preserves skew-Hermiticity. -/
theorem conjTranspose_real_smul_skew {A : Matrix m m ℂ} (hA : Aᴴ = -A) (s : ℝ) :
    (s • A)ᴴ = -(s • A) := by
  rw [Matrix.conjTranspose_smul, hA]
  ext i j
  simp

/-- A skew-Hermitian generator exponentiates to a matrix of **unit L2 operator norm** — it is
unitary, and the L2 operator norm is a C*-norm. -/
theorem l2_opNorm_exp_smul_skew (A : Matrix m m ℂ)
    (hA : Aᴴ = -A) (t : ℝ) : ‖exp (t • A)‖ = 1 := by
  have hskew : (t • A)ᴴ = -(t • A) := conjTranspose_real_smul_skew hA t
  have hcomm : Commute (-(t • A)) (t • A) := (Commute.refl (t • A)).neg_left
  have h1 : (exp (t • A))ᴴ * exp (t • A) = 1 := by
    rw [← Matrix.exp_conjTranspose, hskew, ← Matrix.exp_add_of_commute _ _ hcomm,
      neg_add_cancel, exp_zero]
  have h2 : exp (t • A) * (exp (t • A))ᴴ = 1 := mul_eq_one_comm.mp h1
  have hu : exp (t • A) ∈ unitary (Matrix m m ℂ) :=
    ⟨show star (exp (t • A)) * exp (t • A) = 1 from h1,
     show exp (t • A) * star (exp (t • A)) = 1 from h2⟩
  exact CStarRing.norm_of_mem_unitary hu

/-- **The Duhamel bound.** For skew-Hermitian generators `C, A`,
`‖exp (t • C) − exp (t • A)‖ ≤ |t| · ‖C − A‖` in the L2 operator norm.

Proof without integrals: the interpolant `φ(s) = exp (s • C) · exp ((t−s) • A)` has derivative
`exp (s • C) · (C − A) · exp ((t−s) • A)`, of norm at most `‖C − A‖` since both exponentials are
unitary; the mean-value inequality on `[0, t]` finishes. -/
theorem norm_exp_smul_sub_exp_smul_le (C A : Matrix m m ℂ)
    (hC : Cᴴ = -C) (hA : Aᴴ = -A) (t : ℝ) :
    ‖exp (t • C) - exp (t • A)‖ ≤ |t| * ‖C - A‖ := by
  set φ : ℝ → Matrix m m ℂ := fun s => exp (s • C) * exp ((t - s) • A) with hφ
  -- The derivative of the interpolant.
  have hderiv : ∀ s : ℝ, HasDerivAt φ (exp (s • C) * (C - A) * exp ((t - s) • A)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • C)) (exp (s • C) * C) s :=
      hasDerivAt_exp_smul_const C s
    have hg : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h2 : HasDerivAt (fun u : ℝ => exp ((t - u) • A))
        ((-1 : ℝ) • (exp ((t - s) • A) * A)) s :=
      (hasDerivAt_exp_smul_const A (t - s)).scomp s hg
    have hmul := h1.mul h2
    -- Rearrange `f'·g + f·g'` into the middle-factor form.
    have hcomm : exp ((t - s) • A) * A = A * exp ((t - s) • A) :=
      (((Commute.refl A).smul_left (t - s)).exp_left).eq
    have hD : exp (s • C) * C * exp ((t - s) • A)
          + exp (s • C) * ((-1 : ℝ) • (exp ((t - s) • A) * A))
        = exp (s • C) * (C - A) * exp ((t - s) • A) := by
      rw [neg_one_smul, mul_neg, ← sub_eq_add_neg, hcomm]
      noncomm_ring
    exact hD ▸ hmul
  -- The derivative is bounded by `‖C − A‖`, the exponential factors being unitary.
  have hbound : ∀ s : ℝ, ‖exp (s • C) * (C - A) * exp ((t - s) • A)‖ ≤ ‖C - A‖ := by
    intro s
    calc ‖exp (s • C) * (C - A) * exp ((t - s) • A)‖
        ≤ ‖exp (s • C) * (C - A)‖ * ‖exp ((t - s) • A)‖ := norm_mul_le _ _
      _ ≤ ‖exp (s • C)‖ * ‖C - A‖ * ‖exp ((t - s) • A)‖ := by
          gcongr
          exact norm_mul_le _ _
      _ = ‖C - A‖ := by
          rw [l2_opNorm_exp_smul_skew C hC s, l2_opNorm_exp_smul_skew A hA (t - s),
            one_mul, mul_one]
  -- Mean value inequality on the segment from `0` to `t`.
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := φ) (f' := fun s => exp (s • C) * (C - A) * exp ((t - s) • A))
    (s := Set.uIcc (0 : ℝ) t) (C := ‖C - A‖)
    (fun s _ => (hderiv s).hasDerivWithinAt)
    (fun s _ => hbound s)
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  -- Identify the endpoints.
  have hφt : φ t = exp (t • C) := by
    simp [hφ, sub_self]
  have hφ0 : φ 0 = exp (t • A) := by
    simp [hφ]
  rw [hφt, hφ0] at hmvt
  simpa [abs_mul, mul_comm] using hmvt

/-- **The Duhamel bound for Hamiltonians.** For Hermitian `H, H₀`, the Schrödinger unitaries stay
within `|t| · ‖H − H₀‖` of one another:

  `‖exp (t • (−i H)) − exp (t • (−i H₀))‖ ≤ |t| · ‖H − H₀‖`. -/
theorem norm_exp_smul_neg_I_sub_le (H H₀ : Matrix m m ℂ)
    (hH : H.IsHermitian) (hH₀ : H₀.IsHermitian) (t : ℝ) :
    ‖exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀))‖ ≤ |t| * ‖H - H₀‖ := by
  have hskew : ∀ (M : Matrix m m ℂ), M.IsHermitian →
      ((-Complex.I) • M)ᴴ = -((-Complex.I) • M) := by
    intro M hM
    have hstar : star (-Complex.I) = Complex.I := by simp
    rw [Matrix.conjTranspose_smul, hM.eq, hstar, ← neg_smul, neg_neg]
  have h := norm_exp_smul_sub_exp_smul_le ((-Complex.I) • H) ((-Complex.I) • H₀)
    (hskew H hH) (hskew H₀ hH₀) t
  have hdiff : (-Complex.I) • H - (-Complex.I) • H₀ = (-Complex.I) • (H - H₀) := by
    rw [smul_sub]
  rw [hdiff, norm_smul] at h
  simpa using h

end Matrix
