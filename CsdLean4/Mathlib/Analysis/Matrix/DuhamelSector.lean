/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelState

/-!
# The Duhamel bound for a sector the unperturbed generator conserves

**Category:** 1-Mathlib (CSD-free upstream candidates). BACKLOG #437, fourth brick (the
return caused at the event; obligation UO-26, assumption UA-19).

`DuhamelState.lean` bounds what reaches a sector `Q` that annihilates the unperturbed orbit
at the time `t`. When `Q` commutes with the unperturbed Hamiltonian and annihilates the
prepared subspace, that hypothesis holds at every time, and the bound reads

  `‖Q e^{−it(H₀+V)} X‖ ≤ ‖Q‖ ∫₀ᵗ ‖V e^{−isH₀} X‖ ds`.

* `mul_exp_smul_eq_of_commute`;
* ★★★ `norm_mul_exp_neg_I_add_mul_le_of_commute`;
* ★★★ `norm_mul_exp_neg_I_add_smul_mul_le_of_commute` (the coupling `V = g G` with its
  strength displayed: `‖Q‖ |g| ∫₀ᵗ ‖G e^{−isH₀} X‖ ds`).

## Honest scope

⚠️ **An upper bound.** It does not show that anything reaches the sector. `t ≥ 0`, square `X`,
the L2 operator norm. No carrier or arena; `RecordLayer/UnifiedTransponder.lean` applies it.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-211, UD-224); `DuhamelState.lean` (`norm_mul_exp_neg_I_add_mul_le`);
`specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- A matrix that commutes with `A` commutes with the group of `A`. -/
theorem mul_exp_smul_eq_of_commute {Q A : Matrix m m ℂ} (h : Q * A = A * Q) (t : ℝ) :
    Q * exp (t • A) = exp (t • A) * Q :=
  ((show Commute Q A from h).smul_right t).exp_right.eq

/-- ★★★ **Nothing reaches a sector that the unperturbed Hamiltonian conserves and the
preparation avoids, except through the perturbation acting on the unperturbed orbit.** For
Hermitian `H₀`, `V`, a `Q` that commutes with `H₀` and annihilates `X`, and `t ≥ 0`,

  `‖Q exp (−i t (H₀ + V)) X‖ ≤ ‖Q‖ ∫₀ᵗ ‖V exp (−i s H₀) X‖ ds`. -/
theorem norm_mul_exp_neg_I_add_mul_le_of_commute (H₀ V X Q : Matrix m m ℂ)
    (hH₀ : H₀.IsHermitian) (hV : V.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    (hc : Q * H₀ = H₀ * Q) (hQX : Q * X = 0) :
    ‖Q * exp (t • ((-Complex.I) • (H₀ + V))) * X‖
      ≤ ‖Q‖ * ∫ s in (0 : ℝ)..t, ‖V * exp (s • ((-Complex.I) • H₀)) * X‖ := by
  refine norm_mul_exp_neg_I_add_mul_le H₀ V X Q hH₀ hV ht ?_
  have hc' : Q * ((-Complex.I) • H₀) = ((-Complex.I) • H₀) * Q := by
    rw [mul_smul_comm, smul_mul_assoc, hc]
  rw [mul_exp_smul_eq_of_commute hc' t, mul_assoc, hQX, mul_zero]

/-- ★★★ **The same with the strength of the coupling displayed**: for a real `g` and a
Hermitian `G`, the part under `Q` at the time `t` is at most
`‖Q‖ |g| ∫₀ᵗ ‖G exp (−i s H₀) X‖ ds`. -/
theorem norm_mul_exp_neg_I_add_smul_mul_le_of_commute (H₀ G X Q : Matrix m m ℂ) (g : ℝ)
    (hH₀ : H₀.IsHermitian) (hG : G.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    (hc : Q * H₀ = H₀ * Q) (hQX : Q * X = 0) :
    ‖Q * exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G))) * X‖
      ≤ ‖Q‖ * (|g| * ∫ s in (0 : ℝ)..t, ‖G * exp (s • ((-Complex.I) • H₀)) * X‖) := by
  have hgG : ((g : ℂ) • G).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hG.eq, Complex.star_def,
      Complex.conj_ofReal]
  have h := norm_mul_exp_neg_I_add_mul_le_of_commute H₀ ((g : ℂ) • G) X Q hH₀ hgG ht hc hQX
  have e : ∀ s : ℝ, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖
      = |g| * ‖G * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [smul_mul_assoc, smul_mul_assoc, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  simp only [e] at h
  rwa [intervalIntegral.integral_const_mul] at h

end Matrix
