/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.Metrology.Ramsey
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Empirical/Metrology A2: Quantum Fisher Information = Fubini-Study metric

**Category:** 3-Local (QM-validity metrology layer; no CSD ontology beyond the A1
Ramsey phase flow it reuses).

This is **item A2** of `specs/metrology-plan.md`: the pure-state Quantum Fisher
Information as the Fubini-Study metric, and the proof that the A1 Ramsey family
saturates the quantum Cramer-Rao bound (the computational-basis `|0⟩` readout is
Fisher-optimal at every working point).

## Definitions

For a smooth normalized pure-state family `ψ : ℝ → EuclideanSpace ℂ (Fin d)` with
derivative vector `dψ`, the **Fubini-Study metric** (generator-variance form, the
projective line element) is
`g = ‖dψ‖² − ‖⟪ψ, dψ⟫‖²`,
and the **Quantum Fisher Information** is `F_Q = 4·g`. The **classical Fisher
information** of a binary outcome with probability `P(θ)` is
`F_C = (P')² / (P·(1−P))`, with `F_C ≤ F_Q` always; equality is a Fisher-optimal
(QCRB-saturating) measurement.

## The Ramsey computation (single-qubit instance)

For `ψ(φ) = ramseyVec φ` (the A1 interferometer output, proved equal to the genuine
circuit `qmH·diag(1,e^{iφ})·qmH·|0⟩` in `Ramsey.ramseyVec_eq_circuit`):

- `dψ(φ) = ramseyDeriv φ`, with component 0 `= i·e^{iφ}/2` and component 1
  `= −i·e^{iφ}/2`. This is the **genuine derivative**, certified by
  `ramseyVec_hasDerivAt : HasDerivAt ramseyVec (ramseyDeriv φ) φ` (proved
  componentwise via `HasDerivAt`, not asserted), mirroring
  `Ramsey.ramsey_fringe_hasDerivAt`.
- `‖dψ‖² = 1/2`, `⟪ψ, dψ⟫ = i/2`, so `‖⟪ψ,dψ⟫‖² = 1/4`.
- `g = 1/2 − 1/4 = 1/4` (`ramsey_fs_metric`), hence `F_Q = 4·(1/4) = 1`
  (`ramsey_qfi`), constant in `φ`.
- The `|0⟩` readout `P(φ) = ramseyFringe φ = cos²(φ/2)` has `P'(φ) = −sin(φ)/2` (A1)
  and `P(1−P) = (1/4)sin²φ`, so `F_C = (sin²φ/4)/((1/4)sin²φ) = 1 = F_Q`
  (`ramsey_classical_fisher`, `ramsey_qcrb_saturation`) wherever `sin φ ≠ 0` (off the
  fringe extrema, where the readout is deterministic and the classical Fisher info is
  degenerate). The computational-basis measurement is therefore Fisher-optimal.

## What is and is not claimed

`F_Q = 1` is the standard-quantum-limit per-shot information; the quantum Cramer-Rao
bound `Var(θ̂) ≥ 1/(n·F_Q)` over `n` shots is the operational reading (stated in this
docstring; the per-shot `F_Q` and the matching `F_C` are the Lean content).

**Honest scope / not covered.** The FS metric and QFI here are defined on the state
vector together with its derivative vector along the trajectory (the honest pullback
of the metric to the curve `φ ↦ ψ(φ)` via the vector derivative). They are **not** the
intrinsic Fubini-Study Riemannian/Kähler metric *tensor* on the manifold `ℂℙ^{d−1}`
(an `(0,2)`-tensor independent of any chosen curve); that heavier object is the
remaining A2/A3 infrastructure, deferred. This is a single-qubit (`d = 2`) instance.
QM-validity layer: no CSD ontology is introduced beyond reuse of the A1 Ramsey
machinery (`ramseyVec`, `ramseyFringe`, `ramsey_fringe_hasDerivAt`).
-/

open scoped ComplexConjugate

namespace CSD
namespace Empirical
namespace Metrology

/-! ### General pure-state Fubini-Study metric and Quantum Fisher Information -/

/-- The **Fubini-Study metric** (generator-variance / projective line-element form),
evaluated on a state vector `ψ` and a derivative vector `dψ`:
`g = ‖dψ‖² − ‖⟪ψ, dψ⟫‖²`. This is the pullback of the FS metric to a trajectory via
the vector derivative, not the intrinsic `(0,2)`-tensor on `ℂℙ^{d−1}` (see the file
docstring). -/
noncomputable def fsMetric {d : ℕ} (ψ dψ : EuclideanSpace ℂ (Fin d)) : ℝ :=
  ‖dψ‖ ^ 2 - ‖(inner ℂ ψ dψ : ℂ)‖ ^ 2

/-- The **Quantum Fisher Information** of a pure-state family, `F_Q = 4·g`, with `g`
the Fubini-Study metric. The quantum Cramer-Rao bound reads `Var(θ̂) ≥ 1/(n·F_Q)`. -/
noncomputable def qfi {d : ℕ} (ψ dψ : EuclideanSpace ℂ (Fin d)) : ℝ :=
  4 * fsMetric ψ dψ

/-- The **classical Fisher information** of a binary outcome with probability `P` and
slope `P'`: `F_C = (P')² / (P·(1−P))`. -/
noncomputable def classicalFisher (P P' : ℝ) : ℝ := P' ^ 2 / (P * (1 - P))

/-! ### The Ramsey derivative vector and its genuine `HasDerivAt` -/

/-- The **Ramsey derivative vector** `dψ(φ)`: component 0 `= i·e^{iφ}/2`, component 1
`= −i·e^{iφ}/2`. Certified to be the genuine derivative of `ramseyVec` in
`ramseyVec_hasDerivAt`. -/
noncomputable def ramseyDeriv (φ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (Complex.I * Complex.exp ((φ : ℂ) * Complex.I) / 2)
    + EuclideanSpace.single 1 (-(Complex.I * Complex.exp ((φ : ℂ) * Complex.I) / 2))

lemma ramseyDeriv_ofLp_zero (φ : ℝ) :
    (ramseyDeriv φ).ofLp 0 = Complex.I * Complex.exp ((φ : ℂ) * Complex.I) / 2 := by
  simp [ramseyDeriv, EuclideanSpace.single]

lemma ramseyDeriv_ofLp_one (φ : ℝ) :
    (ramseyDeriv φ).ofLp 1 = -(Complex.I * Complex.exp ((φ : ℂ) * Complex.I) / 2) := by
  simp [ramseyDeriv, EuclideanSpace.single]

/-- `EuclideanSpace.single i`, packaged as an **ℝ-linear** continuous map
`ℂ →L[ℝ] EuclideanSpace ℂ (Fin 2)`. Built ℝ-linear from the start so that composing the
ℝ-valued `HasDerivAt` of a scalar trajectory with it needs no `restrictScalars` (which
triggers the ℝ-ℂ-`EuclideanSpace` module diamond and makes `HasDerivAt.smul_const`
unusable here). -/
noncomputable def singleRL (i : Fin 2) : ℂ →L[ℝ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := EuclideanSpace.single i
      map_add' := fun x y => by
        ext j; simp only [PiLp.single_apply, PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun (r : ℝ) x => by
        ext j; simp only [PiLp.single_apply, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

/-- Componentwise lift: a scalar `HasDerivAt a a' φ` lifts to a vector
`HasDerivAt (fun φ => single i (a φ)) (single i a') φ`, via the ℝ-linear CLM `singleRL`. -/
lemma hasDerivAt_single (i : Fin 2) {a : ℝ → ℂ} {a' : ℂ} {φ : ℝ}
    (h : HasDerivAt a a' φ) :
    HasDerivAt (fun φ => EuclideanSpace.single i (a φ)) (EuclideanSpace.single i a') φ := by
  have := ((singleRL i).hasFDerivAt (x := a φ)).comp_hasDerivAt φ h
  exact this

/-- **`ramseyDeriv` is the genuine derivative of `ramseyVec`.** Proved componentwise:
each component `φ ↦ (1 ± e^{iφ})/2` has derivative `±i·e^{iφ}/2`, via the chain rule
`HasDerivAt.cexp` on `φ ↦ exp((φ:ℂ)·I)` and `HasDerivAt.const_add/const_sub/div_const`,
then assembled through `EuclideanSpace.single`. This earns the "derivative" label; it is
not asserted. Mirrors `Ramsey.ramsey_fringe_hasDerivAt`. -/
theorem ramseyVec_hasDerivAt (φ : ℝ) :
    HasDerivAt ramseyVec (ramseyDeriv φ) φ := by
  have hlin : HasDerivAt (fun φ : ℝ => (↑φ : ℂ) * Complex.I) Complex.I φ := by
    simpa [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasDerivAt (x := φ)).mul_const Complex.I
  have hexp : HasDerivAt (fun φ : ℝ => Complex.exp ((↑φ : ℂ) * Complex.I))
      (Complex.exp ((↑φ : ℂ) * Complex.I) * Complex.I) φ := hlin.cexp
  have ha : HasDerivAt (fun φ : ℝ => (1 + Complex.exp ((↑φ : ℂ) * Complex.I)) / 2)
      (Complex.exp ((↑φ : ℂ) * Complex.I) * Complex.I / 2) φ :=
    (hexp.const_add 1).div_const 2
  have hb : HasDerivAt (fun φ : ℝ => (1 - Complex.exp ((↑φ : ℂ) * Complex.I)) / 2)
      (-(Complex.exp ((↑φ : ℂ) * Complex.I) * Complex.I) / 2) φ :=
    (hexp.const_sub 1).div_const 2
  have D0 := hasDerivAt_single 0 ha
  have D1 := hasDerivAt_single 1 hb
  have hsum := D0.add D1
  have hderiv : ramseyDeriv φ
      = EuclideanSpace.single 0 (Complex.exp ((↑φ : ℂ) * Complex.I) * Complex.I / 2)
        + EuclideanSpace.single 1 (-(Complex.exp ((↑φ : ℂ) * Complex.I) * Complex.I) / 2) := by
    unfold ramseyDeriv
    rw [mul_comm Complex.I (Complex.exp ((↑φ : ℂ) * Complex.I)), neg_div]
  rw [hderiv]
  exact hsum

/-! ### The two inner products: `‖dψ‖² = 1/2` and `⟪ψ, dψ⟫ = i/2` -/

/-- `‖e^{iφ}‖ = 1`. -/
lemma norm_exp_phase (φ : ℝ) : ‖Complex.exp ((↑φ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero]

/-- **`‖dψ‖² = 1/2`** for the Ramsey derivative vector. -/
lemma ramseyDeriv_normSq (φ : ℝ) : ‖ramseyDeriv φ‖ ^ 2 = 1 / 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_two, ramseyDeriv_ofLp_zero, ramseyDeriv_ofLp_one]
  rw [norm_neg]
  have h : ‖Complex.I * Complex.exp ((↑φ : ℂ) * Complex.I) / 2‖ = 1 / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, norm_exp_phase, RCLike.norm_two]
  rw [h]; norm_num

/-- **`⟪ψ, dψ⟫ = i/2`** for the Ramsey state and its derivative. The cross term
collapses via `e^{iφ}·conj(e^{iφ}) = 1`. -/
lemma ramsey_inner (φ : ℝ) :
    (inner ℂ (ramseyVec φ) (ramseyDeriv φ) : ℂ) = Complex.I / 2 := by
  have hconjw : (starRingEnd ℂ) (Complex.exp ((↑φ : ℂ) * Complex.I))
      = Complex.exp (-((↑φ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hww : Complex.exp ((↑φ : ℂ) * Complex.I) * star (Complex.exp ((↑φ : ℂ) * Complex.I))
      = 1 := by
    rw [show star (Complex.exp ((↑φ : ℂ) * Complex.I))
          = (starRingEnd ℂ) (Complex.exp ((↑φ : ℂ) * Complex.I)) from rfl,
        hconjw, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [Pi.star_apply, ramseyDeriv_ofLp_zero, ramseyDeriv_ofLp_one,
    ramseyVec_ofLp_zero, ramseyVec_ofLp_one, star_div₀, star_add, star_sub,
    star_one, star_ofNat]
  linear_combination (Complex.I / 2) * hww

/-! ### The headline QFI computation -/

/-- **The Ramsey Fubini-Study line element `g = 1/4`.** `g = ‖dψ‖² − ‖⟪ψ,dψ⟫‖²
= 1/2 − 1/4`. -/
theorem ramsey_fs_metric (φ : ℝ) :
    fsMetric (ramseyVec φ) (ramseyDeriv φ) = 1 / 4 := by
  rw [fsMetric, ramseyDeriv_normSq, ramsey_inner]
  have hi : ‖(Complex.I / 2 : ℂ)‖ ^ 2 = 1 / 4 := by
    rw [norm_div, Complex.norm_I, RCLike.norm_two]; norm_num
  rw [hi]; norm_num

/-- **The Ramsey Quantum Fisher Information `F_Q = 1`** (the standard-quantum-limit
per-shot information), constant in `φ`. `F_Q = 4·g = 4·(1/4)`. -/
theorem ramsey_qfi (φ : ℝ) :
    qfi (ramseyVec φ) (ramseyDeriv φ) = 1 := by
  rw [qfi, ramsey_fs_metric]; norm_num

/-! ### Classical Fisher information of the `|0⟩` readout and QCRB saturation -/

/-- **The classical Fisher information of the `|0⟩` Ramsey readout equals 1**, for
`sin φ ≠ 0` (off the fringe extrema). With `P = cos²(φ/2)` and `P' = −sin(φ)/2`:
`P·(1−P) = (1/4)sin²φ` and `(P')² = sin²φ/4`, so `F_C = 1`. -/
theorem ramsey_classical_fisher (φ : ℝ) (hφ : Real.sin φ ≠ 0) :
    classicalFisher (ramseyFringe φ) (-(Real.sin φ) / 2) = 1 := by
  rw [classicalFisher, ramseyFringe]
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  have hPP : Real.cos (φ / 2) ^ 2 * (1 - Real.cos (φ / 2) ^ 2) = Real.sin φ ^ 2 / 4 := by
    have hsc := Real.sin_sq_add_cos_sq (φ / 2)
    rw [hs]; nlinarith [hsc]
  rw [hPP]
  have hne : Real.sin φ ^ 2 ≠ 0 := pow_ne_zero 2 hφ
  field_simp
  ring

/-- **The computational-basis Ramsey measurement saturates the quantum Cramer-Rao
bound** (it is Fisher-optimal at every working point `sin φ ≠ 0`): the classical
Fisher information of the `|0⟩` readout equals the Quantum Fisher Information,
`F_C = F_Q = 1`. -/
theorem ramsey_qcrb_saturation (φ : ℝ) (hφ : Real.sin φ ≠ 0) :
    qfi (ramseyVec φ) (ramseyDeriv φ)
      = classicalFisher (ramseyFringe φ) (-(Real.sin φ) / 2) := by
  rw [ramsey_qfi, ramsey_classical_fisher φ hφ]

end Metrology
end Empirical
end CSD
