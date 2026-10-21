/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.AdiabaticBornFock

/-!
# An explicit adiabatic constant

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #166 (out of ~~#162~~): the constant of Kato's comparison as a formula in the gap and the
derivatives of the path.

#162 proved `‖U_T(s) − U_A(s)‖ ≤ C / T` with `C = 2 sup‖Y‖ + sup‖Ẏ + Y K‖` by compactness. Here
every quantity is bounded in terms of the gap `g`, `M₁ ≥ sup_{[0,1]} ‖Ḣ‖` and `M₂ ≥ sup_{[0,1]} ‖Ḧ‖`:

  `C = 8 M₁ / g² + 4 M₂ / g² + 80 M₁² / g³`.

The row expected this to need the derivative of the Riesz projector as a contour integral. It
does not: differentiating `H P = P H` and multiplying by the reduced resolvent `X` gives
**`Ṗ = X Ḣ P + P Ḣ X`** (Kato's formula) by pure algebra from `X (λ − H) = 1 − P`, `X P = P X = 0`,
`P Ṗ P = 0`; differentiating `X (λ − H) = 1 − P` and `X P = 0` gives `Ẋ` likewise, with
`λ̇ P = P Ḣ P` for the eigenvalue's derivative. The norms then follow from `‖P‖ ≤ 1` and
`‖X‖ ≤ 1/g` (the operator norm of `U diag(d) U†` is `sup |dⱼ|`).

* `Matrix.IsHermitian.norm_conjD_le`, `GappedPath.norm_rr_le`, ★ `norm_redRes_le` — `‖X‖ ≤ 1/g`;
* `one_le_norm_of_mul_self_eq`, `GappedPath.proj_ne_zero`, `one_le_norm_proj` — `‖P‖ ≥ 1`;
* `GappedPath.hasDerivAt_H`, `hasDerivAt_lam`, `hasDerivAt_redRes`, `hasDerivAt_deriv_H`,
  `hasDerivAt_deriv_proj`, `contDiff_one_deriv_of_two` — the derivatives that exist;
* `GappedPath.redRes_mul_H`, `H_mul_redRes`, `deriv_H_mul_proj_add` — `X H = λ X − (1 − P)` and
  `Ḣ P + H Ṗ = Ṗ H + P Ḣ`;
* ★★ `GappedPath.deriv_proj_mul_proj`, `proj_mul_deriv_proj`, `deriv_proj_eq_redRes` —
  **`Ṗ P = X Ḣ P`, `P Ṗ = P Ḣ X`, `Ṗ = X Ḣ P + P Ḣ X`**;
* ★ `GappedPath.proj_mul_deriv_H_mul_proj` — **`P Ḣ P = λ̇ P`**, and `norm_deriv_lam_le`:
  `|λ̇| ≤ ‖Ḣ‖`;
* ★★ `GappedPath.deriv_redRes_eq` — **`Ẋ = −Ṗ X − λ̇ X² + X Ḣ X − X Ṗ`**;
* `GappedPath.hasDerivAt_deriv_proj_eq`, `hasDerivAt_Y` — `P̈` and `Ẏ` by the product rule;
* `GappedPath.norm_deriv_proj_le`, `norm_deriv_redRes_le`, `norm_deriv_deriv_proj_le`,
  `norm_Y_le`, `norm_K_le`, `norm_deriv_Y_add_le` — the pointwise bounds
  `‖Ṗ‖ ≤ 2M₁/g`, `‖Ẋ‖ ≤ 6M₁/g²`, `‖P̈‖ ≤ 16M₁²/g² + 2M₂/g`, `‖Y‖ ≤ 4M₁/g²`, `‖K‖ ≤ 4M₁/g`,
  `‖Ẏ + Y K‖ ≤ 80M₁²/g³ + 4M₂/g²`;
* ★★★ `GappedPath.norm_sub_le_explicit` — **Kato's comparison with an explicit constant**.

## Honest scope

* The constants `8, 4, 80` are what the termwise triangle inequality gives; they are not optimal
  (Teufel's Thm 2.2 has the same shape with smaller numbers obtained by a sharper route). The
  spin-½ instance (#165) has an exact overlap error `≤ (2π(π+2)/g) · ω/(2π)`, well inside this.
* `M₁`, `M₂` bound `‖Ḣ‖`, `‖Ḧ‖` on `[0, 1]` in the `L2Operator` norm; `C²` path, uniform gap, the
  branch an eigenvalue, as in #162.

References: T. Kato, *Perturbation Theory for Linear Operators*, II-§2.3 (the derivative of the
reduced resolvent); S. Teufel, *Adiabatic Perturbation Theory in Quantum Dynamics*, Thm 2.2;
`AdiabaticComparison.lean` (#162, `norm_sub_le_of_bounds`); `specs/BACKLOG.md` #166, ~~#162~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology
open Matrix Metric Set Complex Filter

section General

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `C²` function has a `C¹` derivative. -/
theorem contDiff_one_deriv_of_two {n : ℕ∞} (hn : 2 ≤ n) {f : ℝ → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ 1 (deriv f) := by
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) f := by
    rw [one_add_one_eq_two]
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
    exact hf.of_le (by simpa using h2)
  exact (contDiff_succ_iff_deriv.1 h2).2.2

end General

section NormHelpers

variable {R : Type*} [NonUnitalSeminormedRing R]

theorem norm_mul_mul_le (A B C : R) : ‖A * (B * C)‖ ≤ ‖A‖ * (‖B‖ * ‖C‖) :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))

theorem norm_mul_mul_le' (A B C : R) : ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem norm_mul_add_mul_le (A B C D E : R) :
    ‖A * (B * C + D * E)‖ ≤ ‖A‖ * (‖B‖ * ‖C‖ + ‖D‖ * ‖E‖) :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) (norm_nonneg _))

theorem norm_add_mul_mul_le (A B C D E : R) :
    ‖(A * B + C * D) * E‖ ≤ (‖A‖ * ‖B‖ + ‖C‖ * ‖D‖) * ‖E‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) (norm_nonneg _))

end NormHelpers

namespace Matrix

variable {N : ℕ}

/-- `‖U diag(d) U†‖ ≤ sup |dⱼ|`. -/
theorem IsHermitian.norm_conjD_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (d : Fin N → ℂ) : ‖hH.conjD d‖ ≤ ‖d‖ := by
  have hU : ‖hH.eigU‖ ≤ 1 := norm_le_one_of_conjTranspose_mul_self (by
    rw [← star_eq_conjTranspose]; exact hH.star_eigU_mul_eigU)
  have hU' : ‖star hH.eigU‖ ≤ 1 := by rw [norm_star]; exact hU
  unfold IsHermitian.conjD
  calc ‖hH.eigU * diagonal d * star hH.eigU‖
      ≤ ‖hH.eigU * diagonal d‖ * ‖star hH.eigU‖ := norm_mul_le _ _
    _ ≤ ‖hH.eigU‖ * ‖diagonal d‖ * ‖star hH.eigU‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖d‖ * 1 := by rw [l2_opNorm_diagonal]; gcongr
    _ = ‖d‖ := by ring

/-- A nonzero idempotent has operator norm `≥ 1`. -/
theorem one_le_norm_of_mul_self_eq {P : Matrix (Fin N) (Fin N) ℂ} (hP : P * P = P) (h0 : P ≠ 0) :
    1 ≤ ‖P‖ := by
  have hpos : 0 < ‖P‖ := norm_pos_iff.2 h0
  have h : ‖P‖ * 1 ≤ ‖P‖ * ‖P‖ := by
    rw [mul_one]
    calc ‖P‖ = ‖P * P‖ := by rw [hP]
      _ ≤ ‖P‖ * ‖P‖ := norm_mul_le _ _
  exact le_of_mul_le_mul_left h hpos

end Matrix

namespace Matrix.GappedPath

variable {N : ℕ} (Γ : GappedPath N)

/-! ### `‖X‖ ≤ 1/g` and `‖P‖ ≥ 1` -/

theorem norm_rr_le (s : ℝ) : ‖Γ.rr s‖ ≤ 1 / Γ.g := by
  have hg0 : 0 ≤ 1 / Γ.g := div_nonneg zero_le_one Γ.g_pos.le
  rw [pi_norm_le_iff_of_nonneg hg0]
  intro j
  unfold rr
  split_ifs with h
  · rw [norm_zero]; exact hg0
  · rw [norm_inv, one_div]
    apply inv_anti₀ Γ.g_pos
    rw [← dist_eq_norm, dist_comm, Γ.dist_eigC]
    rcases Γ.gap s j with h1 | h1
    · exact absurd ((Γ.eigC_eq_iff s j _).2 h1) h
    · exact h1

/-- ★ **`‖X‖ ≤ 1/g`**: the reduced resolvent is bounded by the inverse gap. -/
theorem norm_redRes_le (s : ℝ) : ‖Γ.redRes s‖ ≤ 1 / Γ.g := by
  rw [Γ.redRes_eq_conjD]
  exact ((Γ.isHermitian s).norm_conjD_le _).trans (Γ.norm_rr_le s)

theorem proj_ne_zero {s : ℝ} (hex : ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    Γ.proj s ≠ 0 := by
  intro h
  have ht := Γ.trace_proj s
  rw [h, trace_zero] at ht
  have hm : (Γ.mult s : ℂ) = 0 := ht.symm
  exact (Γ.mult_pos hex).ne' (by exact_mod_cast hm)

theorem one_le_norm_proj {s : ℝ} (hex : ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    1 ≤ ‖Γ.proj s‖ :=
  one_le_norm_of_mul_self_eq (Γ.proj_mul_self s) (Γ.proj_ne_zero hex)

/-! ### The derivatives that exist -/

theorem hasDerivAt_H {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    HasDerivAt Γ.H (deriv Γ.H s) s := by
  have hn' : n ≠ 0 := by
    rintro rfl
    simp at hn
  exact ((hH.differentiable (by exact_mod_cast hn')) s).hasDerivAt

theorem hasDerivAt_lam {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    HasDerivAt Γ.lam (deriv Γ.lam s) s := by
  have hn' : n ≠ 0 := by
    rintro rfl
    simp at hn
  exact (((Γ.contDiff_lam hH hex).differentiable (by exact_mod_cast hn')) s).hasDerivAt

theorem hasDerivAt_redRes {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    HasDerivAt Γ.redRes (deriv Γ.redRes s) s := by
  have hn' : n ≠ 0 := by
    rintro rfl
    simp at hn
  exact (((Γ.contDiff_redRes hH hex).differentiable (by exact_mod_cast hn')) s).hasDerivAt

theorem hasDerivAt_deriv_H {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    HasDerivAt (deriv Γ.H) (deriv (deriv Γ.H) s) s :=
  ((contDiff_one_deriv_of_two hn hH).differentiable one_ne_zero s).hasDerivAt

theorem hasDerivAt_deriv_proj {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    HasDerivAt (deriv Γ.proj) (deriv (deriv Γ.proj) s) s :=
  ((contDiff_one_deriv_of_two hn (Γ.contDiff_proj hH)).differentiable one_ne_zero s).hasDerivAt

/-! ### The algebra: `Ṗ = X Ḣ P + P Ḣ X`, `P Ḣ P = λ̇ P`, `Ẋ` -/

/-- `X H = λ X − (1 − P)`. -/
theorem redRes_mul_H (s : ℝ) :
    Γ.redRes s * Γ.H s = (Γ.lam s : ℂ) • Γ.redRes s - (1 - Γ.proj s) := by
  have h := Γ.redRes_mul_smul_one_sub_H s
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at h
  linear_combination (norm := module) -h

/-- `H X = λ X − (1 − P)`. -/
theorem H_mul_redRes (s : ℝ) :
    Γ.H s * Γ.redRes s = (Γ.lam s : ℂ) • Γ.redRes s - (1 - Γ.proj s) := by
  have h := Γ.smul_one_sub_H_mul_redRes s
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
  linear_combination (norm := module) -h

/-- Differentiating `H P = P H`: `Ḣ P + H Ṗ = Ṗ H + P Ḣ`. -/
theorem deriv_H_mul_proj_add {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    deriv Γ.H s * Γ.proj s + Γ.H s * deriv Γ.proj s
      = deriv Γ.proj s * Γ.H s + Γ.proj s * deriv Γ.H s := by
  have h1 : HasDerivAt (fun u => Γ.H u * Γ.proj u)
      (deriv Γ.H s * Γ.proj s + Γ.H s * deriv Γ.proj s) s :=
    (Γ.hasDerivAt_H hn hH s).mul (Γ.hasDerivAt_proj hn hH s)
  have h2 : HasDerivAt (fun u => Γ.proj u * Γ.H u)
      (deriv Γ.proj s * Γ.H s + Γ.proj s * deriv Γ.H s) s :=
    (Γ.hasDerivAt_proj hn hH s).mul (Γ.hasDerivAt_H hn hH s)
  have hfun : (fun u => Γ.H u * Γ.proj u) = fun u => Γ.proj u * Γ.H u :=
    funext fun u => by rw [Γ.H_mul_proj, Γ.proj_mul_H]
  rw [hfun] at h1
  exact h1.unique h2

theorem proj_mul_H_mul (s : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Γ.proj s * (Γ.H s * M) = (Γ.lam s : ℂ) • (Γ.proj s * M) := by
  rw [← Matrix.mul_assoc, Γ.proj_mul_H, Matrix.smul_mul]

theorem redRes_mul_proj_mul (s : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Γ.redRes s * (Γ.proj s * M) = 0 := by
  rw [← Matrix.mul_assoc, Γ.redRes_mul_proj, Matrix.zero_mul]

theorem proj_mul_proj_mul (s : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Γ.proj s * (Γ.proj s * M) = Γ.proj s * M := by
  rw [← Matrix.mul_assoc, Γ.proj_mul_self]

theorem proj_mul_deriv_proj_mul_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    Γ.proj s * (deriv Γ.proj s * Γ.proj s) = 0 := by
  rw [← Matrix.mul_assoc, Γ.proj_mul_deriv_mul_proj hn hH]

theorem redRes_mul_H_mul (s : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Γ.redRes s * (Γ.H s * M) = (Γ.lam s : ℂ) • (Γ.redRes s * M) - M + Γ.proj s * M := by
  rw [← Matrix.mul_assoc, Γ.redRes_mul_H, Matrix.sub_mul, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.one_mul]
  abel

/-- ★★ **`Ṗ P = X Ḣ P`.** -/
theorem deriv_proj_mul_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    deriv Γ.proj s * Γ.proj s = Γ.redRes s * (deriv Γ.H s * Γ.proj s) := by
  have h1 := congrArg (fun M => Γ.redRes s * (M * Γ.proj s)) (Γ.deriv_H_mul_proj_add hn hH s)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Γ.redRes_mul_H_mul,
    Γ.H_mul_proj, Γ.redRes_mul_proj_mul, Γ.proj_mul_deriv_proj_mul_proj hn hH, Γ.proj_mul_self,
    Matrix.mul_smul, add_zero] at h1
  linear_combination (norm := module) -h1

/-- ★★ **`P Ṗ = P Ḣ X`.** -/
theorem proj_mul_deriv_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    Γ.proj s * deriv Γ.proj s = Γ.proj s * (deriv Γ.H s * Γ.redRes s) := by
  have h1 := congrArg (fun M => Γ.proj s * (M * Γ.redRes s)) (Γ.deriv_H_mul_proj_add hn hH s)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Γ.H_mul_redRes, Γ.proj_mul_H_mul,
    Γ.proj_mul_redRes, Γ.proj_mul_proj_mul, Γ.proj_mul_deriv_proj_mul_proj hn hH, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero, zero_add] at h1
  linear_combination (norm := module) h1

/-- ★★ **Kato's formula `Ṗ = X Ḣ P + P Ḣ X`**, by algebra alone. -/
theorem deriv_proj_eq_redRes {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    deriv Γ.proj s
      = Γ.redRes s * (deriv Γ.H s * Γ.proj s) + Γ.proj s * (deriv Γ.H s * Γ.redRes s) := by
  rw [← Γ.deriv_proj_mul_proj hn hH, ← Γ.proj_mul_deriv_proj hn hH]
  exact Γ.deriv_proj_eq hn hH s

/-- Differentiating `H P = λ P`: `Ḣ P + H Ṗ = λ̇ P + λ Ṗ`. -/
theorem deriv_H_mul_proj_add_eq {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    deriv Γ.H s * Γ.proj s + Γ.H s * deriv Γ.proj s
      = ((deriv Γ.lam s : ℝ) : ℂ) • Γ.proj s + (Γ.lam s : ℂ) • deriv Γ.proj s := by
  have h1 : HasDerivAt (fun u => Γ.H u * Γ.proj u)
      (deriv Γ.H s * Γ.proj s + Γ.H s * deriv Γ.proj s) s :=
    (Γ.hasDerivAt_H hn hH s).mul (Γ.hasDerivAt_proj hn hH s)
  have h2 : HasDerivAt (fun u => (Γ.lam u : ℂ) • Γ.proj u)
      ((Γ.lam s : ℂ) • deriv Γ.proj s + ((deriv Γ.lam s : ℝ) : ℂ) • Γ.proj s) s :=
    (Γ.hasDerivAt_lam hn hH hex s).ofReal_comp.smul (Γ.hasDerivAt_proj hn hH s)
  have hfun : (fun u => Γ.H u * Γ.proj u) = fun u => (Γ.lam u : ℂ) • Γ.proj u :=
    funext fun u => Γ.H_mul_proj u
  rw [hfun] at h1
  rw [h1.unique h2, add_comm]

/-- ★ **`P Ḣ P = λ̇ P`**: the eigenvalue's derivative is the branch expectation of `Ḣ`. -/
theorem proj_mul_deriv_H_mul_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    Γ.proj s * (deriv Γ.H s * Γ.proj s) = ((deriv Γ.lam s : ℝ) : ℂ) • Γ.proj s := by
  have h1 := congrArg (fun M => Γ.proj s * (M * Γ.proj s)) (Γ.deriv_H_mul_proj_add_eq hn hH hex s)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Γ.proj_mul_H_mul, Γ.proj_mul_self,
    Matrix.smul_mul, Matrix.mul_smul] at h1
  linear_combination (norm := module) h1

/-- `|λ̇| ≤ ‖Ḣ‖`. -/
theorem norm_deriv_lam_le {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    |deriv Γ.lam s| ≤ ‖deriv Γ.H s‖ := by
  have h := congrArg norm (Γ.proj_mul_deriv_H_mul_proj hn hH hex s)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  have hP1 : ‖Γ.proj s‖ ≤ 1 := Γ.norm_proj_le s
  have hP0 : 0 < ‖Γ.proj s‖ := lt_of_lt_of_le zero_lt_one (Γ.one_le_norm_proj (hex s))
  have h2 : |deriv Γ.lam s| * ‖Γ.proj s‖ ≤ ‖deriv Γ.H s‖ * ‖Γ.proj s‖ := by
    rw [← h]
    calc ‖Γ.proj s * (deriv Γ.H s * Γ.proj s)‖
        ≤ ‖Γ.proj s‖ * (‖deriv Γ.H s‖ * ‖Γ.proj s‖) :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ 1 * (‖deriv Γ.H s‖ * ‖Γ.proj s‖) := by gcongr
      _ = ‖deriv Γ.H s‖ * ‖Γ.proj s‖ := one_mul _
  exact le_of_mul_le_mul_right h2 hP0

/-- Differentiating `X P = 0`: `Ẋ P + X Ṗ = 0`. -/
theorem deriv_redRes_mul_proj_add {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    deriv Γ.redRes s * Γ.proj s + Γ.redRes s * deriv Γ.proj s = 0 := by
  have h1 : HasDerivAt (fun u => Γ.redRes u * Γ.proj u)
      (deriv Γ.redRes s * Γ.proj s + Γ.redRes s * deriv Γ.proj s) s :=
    (Γ.hasDerivAt_redRes hn hH hex s).mul (Γ.hasDerivAt_proj hn hH s)
  have hfun : (fun u => Γ.redRes u * Γ.proj u) = fun _ => (0 : Matrix (Fin N) (Fin N) ℂ) :=
    funext fun u => Γ.redRes_mul_proj u
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_const _ _)

/-- Differentiating `X (λ − H) = 1 − P`: `Ẋ (λ − H) + X (λ̇ − Ḣ) = −Ṗ`. -/
theorem deriv_redRes_mul_add {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    deriv Γ.redRes s * ((Γ.lam s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s)
      + Γ.redRes s * (((deriv Γ.lam s : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - deriv Γ.H s)
      = -deriv Γ.proj s := by
  have hLH : HasDerivAt (fun u => (Γ.lam u : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H u)
      (((deriv Γ.lam s : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - deriv Γ.H s) s :=
    ((Γ.hasDerivAt_lam hn hH hex s).ofReal_comp.smul_const _).sub (Γ.hasDerivAt_H hn hH s)
  have h1 := (Γ.hasDerivAt_redRes hn hH hex s).mul hLH
  have h2 : HasDerivAt (fun u => (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.proj u) (-deriv Γ.proj s) s := by
    simpa using (Γ.hasDerivAt_proj hn hH s).const_sub (1 : Matrix (Fin N) (Fin N) ℂ)
  have h3 : HasDerivAt (fun u => (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.proj u)
      (deriv Γ.redRes s * ((Γ.lam s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s)
        + Γ.redRes s * (((deriv Γ.lam s : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - deriv Γ.H s))
      s := by
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    rw [Pi.mul_apply]
    exact (Γ.redRes_mul_smul_one_sub_H u).symm
  exact h3.unique h2

/-- ★★ **The derivative of the reduced resolvent**: `Ẋ = −Ṗ X − λ̇ X² + X Ḣ X − X Ṗ`
(Kato II-§2.3). -/
theorem deriv_redRes_eq {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    deriv Γ.redRes s
      = -(deriv Γ.proj s * Γ.redRes s) - ((deriv Γ.lam s : ℝ) : ℂ) • (Γ.redRes s * Γ.redRes s)
        + Γ.redRes s * (deriv Γ.H s * Γ.redRes s) - Γ.redRes s * deriv Γ.proj s := by
  have h1 := congrArg (fun M => M * Γ.redRes s) (Γ.deriv_redRes_mul_add hn hH hex s)
  have h2 := Γ.deriv_redRes_mul_proj_add hn hH hex s
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, Γ.H_mul_redRes,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul] at h1
  linear_combination (norm := module) h1 + h2

/-! ### `P̈` and `Ẏ` -/

/-- `P̈` by differentiating `Ṗ = X Ḣ P + P Ḣ X`. -/
theorem hasDerivAt_deriv_proj_eq {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    deriv (deriv Γ.proj) s
      = deriv Γ.redRes s * (deriv Γ.H s * Γ.proj s)
        + Γ.redRes s * (deriv (deriv Γ.H) s * Γ.proj s + deriv Γ.H s * deriv Γ.proj s)
        + (deriv Γ.proj s * (deriv Γ.H s * Γ.redRes s)
          + Γ.proj s * (deriv (deriv Γ.H) s * Γ.redRes s + deriv Γ.H s * deriv Γ.redRes s)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have h := ((Γ.hasDerivAt_redRes hn1 hH hex s).mul
      ((Γ.hasDerivAt_deriv_H hn hH s).mul (Γ.hasDerivAt_proj hn1 hH s))).add
    ((Γ.hasDerivAt_proj hn1 hH s).mul
      ((Γ.hasDerivAt_deriv_H hn hH s).mul (Γ.hasDerivAt_redRes hn1 hH hex s)))
  simp only [Pi.mul_apply] at h
  have h' : HasDerivAt (deriv Γ.proj)
      (deriv Γ.redRes s * (deriv Γ.H s * Γ.proj s)
        + Γ.redRes s * (deriv (deriv Γ.H) s * Γ.proj s + deriv Γ.H s * deriv Γ.proj s)
        + (deriv Γ.proj s * (deriv Γ.H s * Γ.redRes s)
          + Γ.proj s * (deriv (deriv Γ.H) s * Γ.redRes s + deriv Γ.H s * deriv Γ.redRes s))) s := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply, Pi.mul_apply]
    exact Γ.deriv_proj_eq_redRes hn1 hH u
  exact h'.deriv

/-- `Ẏ` by the product rule. -/
theorem hasDerivAt_Y {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (s : ℝ) :
    HasDerivAt Γ.Y
      ((deriv Γ.redRes s * deriv Γ.proj s + Γ.redRes s * deriv (deriv Γ.proj) s) * Γ.proj s
          + Γ.redRes s * deriv Γ.proj s * deriv Γ.proj s
        + ((deriv Γ.proj s * deriv Γ.proj s + Γ.proj s * deriv (deriv Γ.proj) s) * Γ.redRes s
          + Γ.proj s * deriv Γ.proj s * deriv Γ.redRes s)) s := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have h := (((Γ.hasDerivAt_redRes hn1 hH hex s).mul (Γ.hasDerivAt_deriv_proj hn hH s)).mul
      (Γ.hasDerivAt_proj hn1 hH s)).add
    (((Γ.hasDerivAt_proj hn1 hH s).mul (Γ.hasDerivAt_deriv_proj hn hH s)).mul
      (Γ.hasDerivAt_redRes hn1 hH hex s))
  simp only [Pi.mul_apply] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, Pi.mul_apply, GappedPath.Y]

/-! ### The pointwise bounds -/

/-- `‖Ṗ‖ ≤ 2 M₁ / g`. -/
theorem norm_deriv_proj_le {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) {s M₁ : ℝ}
    (hM₁ : 0 ≤ M₁) (h₁ : ‖deriv Γ.H s‖ ≤ M₁) : ‖deriv Γ.proj s‖ ≤ 2 * M₁ * (1 / Γ.g) := by
  have hg := Γ.g_pos
  have hx := Γ.norm_redRes_le s
  have hP := Γ.norm_proj_le s
  rw [Γ.deriv_proj_eq_redRes hn hH s]
  calc ‖Γ.redRes s * (deriv Γ.H s * Γ.proj s) + Γ.proj s * (deriv Γ.H s * Γ.redRes s)‖
      ≤ ‖Γ.redRes s‖ * (‖deriv Γ.H s‖ * ‖Γ.proj s‖)
          + ‖Γ.proj s‖ * (‖deriv Γ.H s‖ * ‖Γ.redRes s‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_mul_le _ _ _) (norm_mul_mul_le _ _ _))
    _ ≤ (1 / Γ.g) * (M₁ * 1) + 1 * (M₁ * (1 / Γ.g)) := by gcongr
    _ = 2 * M₁ * (1 / Γ.g) := by ring

/-- `‖Ẋ‖ ≤ 6 M₁ / g²`. -/
theorem norm_deriv_redRes_le {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) {s M₁ : ℝ} (hM₁ : 0 ≤ M₁)
    (h₁ : ‖deriv Γ.H s‖ ≤ M₁) : ‖deriv Γ.redRes s‖ ≤ 6 * M₁ * (1 / Γ.g) ^ 2 := by
  have hg := Γ.g_pos
  have hx := Γ.norm_redRes_le s
  have hQ := Γ.norm_deriv_proj_le hn hH hM₁ h₁
  have hl := (Γ.norm_deriv_lam_le hn hH hex s).trans h₁
  have hQ0 : 0 ≤ 2 * M₁ * (1 / Γ.g) := by positivity
  rw [Γ.deriv_redRes_eq hn hH hex s]
  have t2 : ‖((deriv Γ.lam s : ℝ) : ℂ) • (Γ.redRes s * Γ.redRes s)‖
      ≤ |deriv Γ.lam s| * (‖Γ.redRes s‖ * ‖Γ.redRes s‖) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)
  calc ‖-(deriv Γ.proj s * Γ.redRes s) - ((deriv Γ.lam s : ℝ) : ℂ) • (Γ.redRes s * Γ.redRes s)
          + Γ.redRes s * (deriv Γ.H s * Γ.redRes s) - Γ.redRes s * deriv Γ.proj s‖
      ≤ ‖deriv Γ.proj s‖ * ‖Γ.redRes s‖ + |deriv Γ.lam s| * (‖Γ.redRes s‖ * ‖Γ.redRes s‖)
          + ‖Γ.redRes s‖ * (‖deriv Γ.H s‖ * ‖Γ.redRes s‖) + ‖Γ.redRes s‖ * ‖deriv Γ.proj s‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ t2)) (norm_mul_mul_le _ _ _)))
          (norm_mul_le _ _))
        rw [norm_neg]
        exact norm_mul_le _ _
    _ ≤ 2 * M₁ * (1 / Γ.g) * (1 / Γ.g) + M₁ * ((1 / Γ.g) * (1 / Γ.g))
          + (1 / Γ.g) * (M₁ * (1 / Γ.g)) + (1 / Γ.g) * (2 * M₁ * (1 / Γ.g)) := by gcongr
    _ = 6 * M₁ * (1 / Γ.g) ^ 2 := by ring

/-- `‖P̈‖ ≤ 16 M₁² / g² + 2 M₂ / g`. -/
theorem norm_deriv_deriv_proj_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) {s M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (h₁ : ‖deriv Γ.H s‖ ≤ M₁) (h₂ : ‖deriv (deriv Γ.H) s‖ ≤ M₂) :
    ‖deriv (deriv Γ.proj) s‖ ≤ 16 * M₁ ^ 2 * (1 / Γ.g) ^ 2 + 2 * M₂ * (1 / Γ.g) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hg := Γ.g_pos
  have hx := Γ.norm_redRes_le s
  have hP := Γ.norm_proj_le s
  have hQ := Γ.norm_deriv_proj_le hn1 hH hM₁ h₁
  have hX' := Γ.norm_deriv_redRes_le hn1 hH hex hM₁ h₁
  have hQ0 : 0 ≤ 2 * M₁ * (1 / Γ.g) := by positivity
  have hX'0 : 0 ≤ 6 * M₁ * (1 / Γ.g) ^ 2 := by positivity
  rw [Γ.hasDerivAt_deriv_proj_eq hn hH hex s]
  calc ‖deriv Γ.redRes s * (deriv Γ.H s * Γ.proj s)
          + Γ.redRes s * (deriv (deriv Γ.H) s * Γ.proj s + deriv Γ.H s * deriv Γ.proj s)
          + (deriv Γ.proj s * (deriv Γ.H s * Γ.redRes s)
            + Γ.proj s * (deriv (deriv Γ.H) s * Γ.redRes s + deriv Γ.H s * deriv Γ.redRes s))‖
      ≤ ‖deriv Γ.redRes s‖ * (‖deriv Γ.H s‖ * ‖Γ.proj s‖)
          + ‖Γ.redRes s‖ * (‖deriv (deriv Γ.H) s‖ * ‖Γ.proj s‖ + ‖deriv Γ.H s‖ * ‖deriv Γ.proj s‖)
          + (‖deriv Γ.proj s‖ * (‖deriv Γ.H s‖ * ‖Γ.redRes s‖)
            + ‖Γ.proj s‖ * (‖deriv (deriv Γ.H) s‖ * ‖Γ.redRes s‖
              + ‖deriv Γ.H s‖ * ‖deriv Γ.redRes s‖)) :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans
            (add_le_add (norm_mul_mul_le _ _ _) (norm_mul_add_mul_le _ _ _ _ _)))
          ((norm_add_le _ _).trans
            (add_le_add (norm_mul_mul_le _ _ _) (norm_mul_add_mul_le _ _ _ _ _))))
    _ ≤ 6 * M₁ * (1 / Γ.g) ^ 2 * (M₁ * 1)
          + (1 / Γ.g) * (M₂ * 1 + M₁ * (2 * M₁ * (1 / Γ.g)))
          + (2 * M₁ * (1 / Γ.g) * (M₁ * (1 / Γ.g))
            + 1 * (M₂ * (1 / Γ.g) + M₁ * (6 * M₁ * (1 / Γ.g) ^ 2))) := by gcongr
    _ = 16 * M₁ ^ 2 * (1 / Γ.g) ^ 2 + 2 * M₂ * (1 / Γ.g) := by ring

/-- `‖Y‖ ≤ 4 M₁ / g²`. -/
theorem norm_Y_le {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) {s M₁ : ℝ} (hM₁ : 0 ≤ M₁)
    (h₁ : ‖deriv Γ.H s‖ ≤ M₁) : ‖Γ.Y s‖ ≤ 4 * M₁ * (1 / Γ.g) ^ 2 := by
  have hg := Γ.g_pos
  have hx := Γ.norm_redRes_le s
  have hP := Γ.norm_proj_le s
  have hQ := Γ.norm_deriv_proj_le hn hH hM₁ h₁
  have hQ0 : 0 ≤ 2 * M₁ * (1 / Γ.g) := by positivity
  unfold Y
  calc ‖Γ.redRes s * deriv Γ.proj s * Γ.proj s + Γ.proj s * deriv Γ.proj s * Γ.redRes s‖
      ≤ ‖Γ.redRes s‖ * ‖deriv Γ.proj s‖ * ‖Γ.proj s‖
          + ‖Γ.proj s‖ * ‖deriv Γ.proj s‖ * ‖Γ.redRes s‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_mul_le' _ _ _) (norm_mul_mul_le' _ _ _))
    _ ≤ (1 / Γ.g) * (2 * M₁ * (1 / Γ.g)) * 1 + 1 * (2 * M₁ * (1 / Γ.g)) * (1 / Γ.g) := by gcongr
    _ = 4 * M₁ * (1 / Γ.g) ^ 2 := by ring

/-- `‖K‖ ≤ 4 M₁ / g`. -/
theorem norm_K_le {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) {s M₁ : ℝ} (hM₁ : 0 ≤ M₁)
    (h₁ : ‖deriv Γ.H s‖ ≤ M₁) : ‖Γ.K s‖ ≤ 4 * M₁ * (1 / Γ.g) := by
  have hg := Γ.g_pos
  have hP := Γ.norm_proj_le s
  have hQ := Γ.norm_deriv_proj_le hn hH hM₁ h₁
  have hQ0 : 0 ≤ 2 * M₁ * (1 / Γ.g) := by positivity
  unfold K
  calc ‖deriv Γ.proj s * Γ.proj s - Γ.proj s * deriv Γ.proj s‖
      ≤ ‖deriv Γ.proj s‖ * ‖Γ.proj s‖ + ‖Γ.proj s‖ * ‖deriv Γ.proj s‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ 2 * M₁ * (1 / Γ.g) * 1 + 1 * (2 * M₁ * (1 / Γ.g)) := by gcongr
    _ = 4 * M₁ * (1 / Γ.g) := by ring

/-- `‖Ẏ + Y K‖ ≤ 80 M₁² / g³ + 4 M₂ / g²`. -/
theorem norm_deriv_Y_add_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) {s M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (h₁ : ‖deriv Γ.H s‖ ≤ M₁) (h₂ : ‖deriv (deriv Γ.H) s‖ ≤ M₂) :
    ‖deriv Γ.Y s + Γ.Y s * Γ.K s‖ ≤ 80 * M₁ ^ 2 * (1 / Γ.g) ^ 3 + 4 * M₂ * (1 / Γ.g) ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hg := Γ.g_pos
  have hx := Γ.norm_redRes_le s
  have hP := Γ.norm_proj_le s
  have hQ := Γ.norm_deriv_proj_le hn1 hH hM₁ h₁
  have hX' := Γ.norm_deriv_redRes_le hn1 hH hex hM₁ h₁
  have hQ' := Γ.norm_deriv_deriv_proj_le hn hH hex hM₁ hM₂ h₁ h₂
  have hY := Γ.norm_Y_le hn1 hH hM₁ h₁
  have hK := Γ.norm_K_le hn1 hH hM₁ h₁
  have hQ0 : 0 ≤ 2 * M₁ * (1 / Γ.g) := by positivity
  have hX'0 : 0 ≤ 6 * M₁ * (1 / Γ.g) ^ 2 := by positivity
  have hQ'0 : 0 ≤ 16 * M₁ ^ 2 * (1 / Γ.g) ^ 2 + 2 * M₂ * (1 / Γ.g) := by positivity
  have hY0 : 0 ≤ 4 * M₁ * (1 / Γ.g) ^ 2 := by positivity
  have hK0 : 0 ≤ 4 * M₁ * (1 / Γ.g) := by positivity
  rw [(Γ.hasDerivAt_Y hn hH hex s).deriv]
  calc ‖(deriv Γ.redRes s * deriv Γ.proj s + Γ.redRes s * deriv (deriv Γ.proj) s) * Γ.proj s
          + Γ.redRes s * deriv Γ.proj s * deriv Γ.proj s
          + ((deriv Γ.proj s * deriv Γ.proj s + Γ.proj s * deriv (deriv Γ.proj) s) * Γ.redRes s
            + Γ.proj s * deriv Γ.proj s * deriv Γ.redRes s) + Γ.Y s * Γ.K s‖
      ≤ (‖deriv Γ.redRes s‖ * ‖deriv Γ.proj s‖ + ‖Γ.redRes s‖ * ‖deriv (deriv Γ.proj) s‖)
            * ‖Γ.proj s‖
          + ‖Γ.redRes s‖ * ‖deriv Γ.proj s‖ * ‖deriv Γ.proj s‖
          + ((‖deriv Γ.proj s‖ * ‖deriv Γ.proj s‖ + ‖Γ.proj s‖ * ‖deriv (deriv Γ.proj) s‖)
              * ‖Γ.redRes s‖
            + ‖Γ.proj s‖ * ‖deriv Γ.proj s‖ * ‖deriv Γ.redRes s‖) + ‖Γ.Y s‖ * ‖Γ.K s‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans
            (add_le_add (norm_add_mul_mul_le _ _ _ _ _) (norm_mul_mul_le' _ _ _)))
          ((norm_add_le _ _).trans
            (add_le_add (norm_add_mul_mul_le _ _ _ _ _) (norm_mul_mul_le' _ _ _)))))
          (norm_mul_le _ _))
    _ ≤ (6 * M₁ * (1 / Γ.g) ^ 2 * (2 * M₁ * (1 / Γ.g))
            + (1 / Γ.g) * (16 * M₁ ^ 2 * (1 / Γ.g) ^ 2 + 2 * M₂ * (1 / Γ.g))) * 1
          + (1 / Γ.g) * (2 * M₁ * (1 / Γ.g)) * (2 * M₁ * (1 / Γ.g))
          + ((2 * M₁ * (1 / Γ.g) * (2 * M₁ * (1 / Γ.g))
              + 1 * (16 * M₁ ^ 2 * (1 / Γ.g) ^ 2 + 2 * M₂ * (1 / Γ.g))) * (1 / Γ.g)
            + 1 * (2 * M₁ * (1 / Γ.g)) * (6 * M₁ * (1 / Γ.g) ^ 2))
          + 4 * M₁ * (1 / Γ.g) ^ 2 * (4 * M₁ * (1 / Γ.g)) := by gcongr
    _ = 80 * M₁ ^ 2 * (1 / Γ.g) ^ 3 + 4 * M₂ * (1 / Γ.g) ^ 2 := by ring

/-! ### Kato's comparison with an explicit constant -/

/-- ★★★ **Kato's comparison with an explicit constant.** Along a gapped `C²` path whose branch
is an eigenvalue, with `‖Ḣ‖ ≤ M₁` and `‖Ḧ‖ ≤ M₂` on `[0, 1]`, for every speed `T > 0`,

  `‖U_T(s) − U_A(s)‖ ≤ (8 M₁ / g² + 4 M₂ / g² + 80 M₁² / g³) / T`  on `[0, 1]`. -/
theorem norm_sub_le_explicit {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (h₁ : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv Γ.H s‖ ≤ M₁)
    (h₂ : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv (deriv Γ.H) s‖ ≤ M₂) {T : ℝ} (hT : 0 < T)
    {UT UA : ℝ → Matrix (Fin N) (Fin N) ℂ} (hUT : Γ.IsPhysPropagator T UT)
    (hUA : Γ.IsAdPropagator T UA) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ‖UT s - UA s‖ ≤ (8 * M₁ / Γ.g ^ 2 + 4 * M₂ / Γ.g ^ 2 + 80 * M₁ ^ 2 / Γ.g ^ 3) / T := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hMY : ∀ s ∈ Icc (0 : ℝ) 1, ‖Γ.Y s‖ ≤ 4 * M₁ * (1 / Γ.g) ^ 2 := fun s hs =>
    Γ.norm_Y_le hn1 hH hM₁ (h₁ s hs)
  have hME : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv Γ.Y s + Γ.Y s * Γ.K s‖ ≤ 80 * M₁ ^ 2 * (1 / Γ.g) ^ 3 + 4 * M₂ * (1 / Γ.g) ^ 2 :=
    fun s hs => Γ.norm_deriv_Y_add_le hn hH hex hM₁ hM₂ (h₁ s hs) (h₂ s hs)
  have h := Γ.norm_sub_le_of_bounds hn hH hex hMY hME hT hUT hUA
  have hg := Γ.g_pos
  have hC : 2 * (4 * M₁ * (1 / Γ.g) ^ 2) + (80 * M₁ ^ 2 * (1 / Γ.g) ^ 3 + 4 * M₂ * (1 / Γ.g) ^ 2)
      = 8 * M₁ / Γ.g ^ 2 + 4 * M₂ / Γ.g ^ 2 + 80 * M₁ ^ 2 / Γ.g ^ 3 := by
    field_simp
    ring
  rw [hC] at h
  exact h

end Matrix.GappedPath

end
