/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyForm
public import CsdLean4.Mathlib.Geometry.Manifold.SymplecticForm

/-!
# `ℂℙⁿ` with the Fubini–Study form is a symplectic manifold

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

`ProjectiveSpaceFubiniStudyForm.lean` built the Fubini–Study form `fsForm` as a `C^∞` global
2-form on `ℂℙⁿ` and proved it closed (`fsForm_mextDeriv`). This module proves it
**non-degenerate at every point** and concludes that `ℂℙⁿ` is a symplectic manifold:

* `Kahler.metric_mul_fundamentalForm_complexStructure_sub` — the taming bracket of the chart
  form's components, `g(x,v) ω(x,Jv) − g(x,Jv) ω(x,v) = |⟪x,v⟫|²`;
* `Kahler.fsChartForm_apply_complexStructure` — hence
  `fsChartForm x (v, Jv) = -4 (1+‖x‖²)⁻² ((1+‖x‖²) ‖v‖² − |⟪x,v⟫|²)` at every chart point;
* ★ `Kahler.fsChartForm_complexStructure_self_neg` — **taming at every chart point**: for
  `v ≠ 0` that value is negative, by Cauchy–Schwarz (`|⟪x,v⟫|² ≤ ‖x‖² ‖v‖² < (1+‖x‖²) ‖v‖²`).
  At the origin it is `-4 ‖v‖²`, the flat taming identity `fundamentalForm_complexStructure_self`
  scaled by the normalisation of `fsChartForm_zero`;
* ★★ `fsForm_nondegenerate` — **non-degeneracy of the Fubini–Study form at every point of
  `ℂℙⁿ`**: the section at `x` is the model form at `x`'s own chart coordinate, so the witness is
  `i • v` in the model;
* ★★★ `fsForm_isSymplectic` — **`ℂℙⁿ` with the Fubini–Study form is a symplectic manifold**
  (`DifferentialForm.IsSymplectic`: closed by `fsForm_mextDeriv`, non-degenerate by
  `fsForm_nondegenerate`). Real dimension `2n`, even, as the word requires.

## Honest scope

⚠️ **Symplectic, not yet "Kähler manifold".** Compatibility of `fsForm` with the complex
structure at manifold level (that `fsForm x (v, i • v) < 0` for every `v ≠ 0` is stated here
in the model, `fsSection_smul_I_neg`, and is the taming half) and with a metric are not
packaged as a manifold-level Kähler predicate; the pointwise triple remains
`IsFubiniStudyKahler` on the flat model.

⚠️ **No volume.** Non-degeneracy plus closedness does not produce the top-power identity
`ωⁿ/n! = μ_FS`; that is step (3), top forms → measures, and is not attempted.

⚠️ **Sign convention.** With `fsChartForm = dd^c log(1+‖z‖²)` the taming value is negative
(`-4` at the origin); nothing downstream depends on the sign, only on non-vanishing.

References: `Geometry/Manifold/SymplecticForm.lean` (the predicate);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (`fsForm`, `fsForm_mextDeriv`);
`Analysis/InnerProductSpace/KahlerPotential.lean` (`fsChartForm_apply`);
`Analysis/InnerProductSpace/KahlerForm.lean` (the taming identity, `complexStructure`);
`MATHLIB-GAPS.md` (Kahler / symplectic manifold API); `specs/BACKLOG.md` (XL, "Manifold
exterior calculus"); `specs/TERMS.md` ("symplectic / manifold"); `specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The taming bracket of the Fubini–Study chart-form components:
`g(x,v) ω(x,Jv) − g(x,Jv) ω(x,v) = |⟪x,v⟫|²`. -/
theorem metric_mul_fundamentalForm_complexStructure_sub (x v : E) :
    metric x v * fundamentalForm x (complexStructure v)
      - metric x (complexStructure v) * fundamentalForm x v
      = Complex.normSq (inner ℂ x v) := by
  have h1 : fundamentalForm x (complexStructure v) = metric x v :=
    (metric_eq_fundamentalForm_complexStructure x v).symm
  have h2 : metric x (complexStructure v) = - fundamentalForm x v := by
    rw [metric_eq_fundamentalForm_complexStructure, complexStructure_involutive]
    simp [fundamentalForm, inner_neg_right]
  rw [h1, h2]
  simp only [metric, fundamentalForm, Complex.normSq_apply]
  ring

/-- Taming at every chart point:
`fsChartForm x (v, Jv) = -4 (1+‖x‖²)⁻² ((1+‖x‖²) ‖v‖² − |⟪x,v⟫|²)`. -/
theorem fsChartForm_apply_complexStructure (x v : E) :
    fsChartForm x ![v, complexStructure v]
      = -4 * (1 + ‖x‖ ^ 2)⁻¹ ^ 2 * ((1 + ‖x‖ ^ 2) * ‖v‖ ^ 2 - Complex.normSq (inner ℂ x v)) := by
  rw [fsChartForm_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fundamentalForm_complexStructure_self, metric_mul_fundamentalForm_complexStructure_sub]
  have h : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  field_simp

/-- ★ **Taming at every chart point**: for `v ≠ 0`, `fsChartForm x (v, Jv) < 0`
(Cauchy–Schwarz: `|⟪x,v⟫|² ≤ ‖x‖² ‖v‖² < (1+‖x‖²) ‖v‖²`). -/
theorem fsChartForm_complexStructure_self_neg (x : E) {v : E} (hv : v ≠ 0) :
    fsChartForm x ![v, complexStructure v] < 0 := by
  rw [fsChartForm_apply_complexStructure]
  have hv' : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  have hcs : Complex.normSq (inner ℂ x v) ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm x v) 2
  have hpos : 0 < (1 + ‖x‖ ^ 2) * ‖v‖ ^ 2 - Complex.normSq (inner ℂ x v) := by nlinarith
  have hinv : 0 < (1 + ‖x‖ ^ 2)⁻¹ ^ 2 := by positivity
  have := mul_pos hinv hpos
  linarith

end Kahler

namespace Projectivization

open Kahler

variable {n : ℕ}

/-- Taming for the model form: `fsModelForm w (v, i • v) < 0` for `v ≠ 0`. -/
theorem fsModelForm_smul_I_neg (w : Fin n → ℂ) {v : Fin n → ℂ} (hv : v ≠ 0) :
    fsModelForm w ![v, Complex.I • v] < 0 := by
  have h : fsModelForm w ![v, Complex.I • v]
      = fsChartForm (toLpCLM w) ![toLpCLM v, complexStructure (toLpCLM v)] := by
    simp only [fsModelForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    ext i
    fin_cases i <;> simp [complexStructure_apply]
  rw [h]
  refine fsChartForm_complexStructure_self_neg _ ?_
  intro h0
  apply hv
  have := congrArg WithLp.ofLp h0
  simpa using this

/-- Taming for the section, in the model: `fsSection x (v, i • v) < 0` for `v ≠ 0`. -/
theorem fsSection_smul_I_neg (x : ℙ ℂ (Ambient n)) {v : Fin n → ℂ} (hv : v ≠ 0) :
    fsSection x ![v, Complex.I • v] < 0 :=
  fsModelForm_smul_I_neg _ hv

/-- ★★ **Non-degeneracy of the Fubini–Study form at every point of `ℂℙⁿ`.** -/
theorem fsForm_nondegenerate (x : ℙ ℂ (Ambient n))
    (v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) (hv : v ≠ 0) :
    ∃ w, fsForm x ![v, w] ≠ 0 :=
  ⟨Complex.I • (show Fin n → ℂ from v), (fsSection_smul_I_neg x hv).ne⟩

/-- ★★★ **`ℂℙⁿ` with the Fubini–Study form is a symplectic manifold**: closed
(`fsForm_mextDeriv`) and non-degenerate at every point (`fsForm_nondegenerate`). -/
theorem fsForm_isSymplectic (n : ℕ) : (fsForm (n := n)).IsSymplectic :=
  ⟨fsForm_mextDeriv, fsForm_nondegenerate⟩

end Projectivization
