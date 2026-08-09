/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Dispersion

/-!
# CV-14: boost covariance of the mass shell

**Category:** CV (continuous variables — the multi-mode field).

`CV/Dispersion.lean` proved the mass shell `ω² − p² = m²` and read the
Lorentz content off its *shape*. This module makes that content a
theorem: the 1+1D boost acts on energy–momentum pairs, and the shell is
its invariant.

* `boostE` / `boostP` — the 1+1D boost at rapidity `χ`:
  `E ↦ E cosh χ − p sinh χ`, `p ↦ p cosh χ − E sinh χ`.
* `boost_zero`, `boostE_add` / `boostP_add` — the boosts form a
  one-parameter group: rapidities add (`cosh`/`sinh` addition formulas).
  So "boost" is earned, not a name for an arbitrary map.
* ★ `boost_invariant` — `E'² − p'² = E² − p²` for every rapidity: the
  quadratic form is preserved (`cosh² − sinh² = 1`).
* ★★ `boost_mass_shell` — the boosted dispersion pair satisfies the SAME
  shell: `(ω')² − (p')² = m²`. **The Lorentz content of the dispersion
  relation, as a theorem rather than a reading.**
* `boost_forward` — the forward shell is preserved (`0 ≤ ω'`), using
  `abs_le_omega` and `|sinh| ≤ cosh`: boosts cannot turn a physical mode
  into a negative-energy one.
* ★ `boost_omega` — the sharp form: the boosted energy IS the dispersion
  evaluated at the boosted momentum, `ω' = ω(m, p')`. The dispersion
  relation is boost-covariant on the nose.

⚠️ Honest scope: this is **one-particle kinematic** covariance, at the
level of the dispersion relation. There is no claim of a boost action on
the mode lattice — a finite lattice of modes is not boost-invariant, and
that asymmetry is the standard cutoff honesty rather than an oversight
(the mode structure is a cutoff artefact; the dispersion is what survives
the limit). No continuum claims (`ApproxCCR.no_exact_finite_ccr` stands).

## References

`CV/Dispersion.lean` (`omega`, `omega_sq_sub_sq`, `abs_le_omega`);
`specs/eft-stage4-plan.md` (row CV-14); `specs/future-work.md`.
-/

@[expose] public section

namespace CSD.CV

/-! ### The 1+1D boost -/

/-- The boosted **energy** at rapidity `χ`. -/
noncomputable def boostE (χ E p : ℝ) : ℝ :=
  E * Real.cosh χ - p * Real.sinh χ

/-- The boosted **momentum** at rapidity `χ`. -/
noncomputable def boostP (χ E p : ℝ) : ℝ :=
  p * Real.cosh χ - E * Real.sinh χ

@[simp] lemma boostE_zero (E p : ℝ) : boostE 0 E p = E := by
  rw [boostE, Real.cosh_zero, Real.sinh_zero]
  ring

@[simp] lemma boostP_zero (E p : ℝ) : boostP 0 E p = p := by
  rw [boostP, Real.cosh_zero, Real.sinh_zero]
  ring

/-- Rapidities add on the energy component. -/
theorem boostE_add (χ₁ χ₂ E p : ℝ) :
    boostE χ₂ (boostE χ₁ E p) (boostP χ₁ E p) = boostE (χ₁ + χ₂) E p := by
  rw [boostE, boostE, boostP, boostE, Real.cosh_add, Real.sinh_add]
  ring

/-- Rapidities add on the momentum component. -/
theorem boostP_add (χ₁ χ₂ E p : ℝ) :
    boostP χ₂ (boostE χ₁ E p) (boostP χ₁ E p) = boostP (χ₁ + χ₂) E p := by
  rw [boostP, boostE, boostP, boostP, Real.cosh_add, Real.sinh_add]
  ring

/-! ### The invariant -/

/-- ★ **The boost preserves the quadratic form** `E² − p²`. -/
theorem boost_invariant (χ E p : ℝ) :
    (boostE χ E p) ^ 2 - (boostP χ E p) ^ 2 = E ^ 2 - p ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq χ
  rw [boostE, boostP]
  nlinarith [h, sq_nonneg (Real.cosh χ), sq_nonneg (Real.sinh χ)]

/-- ★★ **Boost covariance of the mass shell**: the boosted
energy–momentum pair of a mode satisfies the same shell, with the same
mass. The Lorentz content of the dispersion relation, as a theorem. -/
theorem boost_mass_shell (m p χ : ℝ) :
    (boostE χ (omega m p) p) ^ 2 - (boostP χ (omega m p) p) ^ 2 = m ^ 2 := by
  rw [boost_invariant]
  exact omega_sq_sub_sq m p

/-! ### The forward shell -/

/-- `|sinh χ| ≤ cosh χ`. -/
lemma abs_sinh_le_cosh (χ : ℝ) : |Real.sinh χ| ≤ Real.cosh χ := by
  have h := Real.cosh_sq_sub_sinh_sq χ
  have hpos : 0 < Real.cosh χ := Real.cosh_pos χ
  have hsq : Real.sinh χ ^ 2 ≤ Real.cosh χ ^ 2 := by nlinarith
  calc |Real.sinh χ| = Real.sqrt (Real.sinh χ ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Real.cosh χ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.cosh χ := by
        rw [Real.sqrt_sq hpos.le]

/-- **The forward shell is preserved**: a boost never turns a physical
mode into a negative-energy one. -/
theorem boost_forward (m p χ : ℝ) : 0 ≤ boostE χ (omega m p) p := by
  have hω : 0 ≤ omega m p := omega_nonneg m p
  have hp : |p| ≤ omega m p := abs_le_omega m p
  have hs : |Real.sinh χ| ≤ Real.cosh χ := abs_sinh_le_cosh χ
  have hc : 0 < Real.cosh χ := Real.cosh_pos χ
  have hbound : p * Real.sinh χ ≤ omega m p * Real.cosh χ := by
    calc p * Real.sinh χ ≤ |p * Real.sinh χ| := le_abs_self _
      _ = |p| * |Real.sinh χ| := abs_mul p (Real.sinh χ)
      _ ≤ omega m p * Real.cosh χ := by
          refine mul_le_mul hp hs (abs_nonneg _) hω
  rw [boostE]
  linarith

/-- ★ **The dispersion relation is boost-covariant on the nose**: the
boosted energy IS the dispersion evaluated at the boosted momentum. -/
theorem boost_omega (m p χ : ℝ) :
    boostE χ (omega m p) p = omega m (boostP χ (omega m p) p) := by
  have hshell := boost_mass_shell m p χ
  have hfwd := boost_forward m p χ
  have hrw : omega m (boostP χ (omega m p) p)
      = Real.sqrt ((boostE χ (omega m p) p) ^ 2) := by
    rw [omega]
    congr 1
    linarith
  rw [hrw, Real.sqrt_sq hfwd]

end CSD.CV
