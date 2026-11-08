/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFSDistance
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceUncertainty

/-!
# The quantum speed limit

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #331 (geometric QM, item 4 of the 2026-11-08 plan, second half).

The Schrödinger curve `s ↦ exp(-isTH) • p` on `[0, 1]` has velocity `T · X_H`, so its
Fubini–Study length is `2 T ΔH` (#329), and every path is at least `2 arccos √P` long (#330). So
**the Anandan–Aharonov / Mandelstam–Tamm bound**: the angle the state turns through in time `T`
is at most `T ΔH`,

`arccos √P(p, exp(-iTH) • p) ≤ T ΔH`,

and a state with energy spread `ΔH > 0` needs at least `arccos √P / ΔH` to reach a ray at
transition probability `P` (`ħ = 1`).

* `hasMFDerivAt_schrodingerUnitary_smul_mul` — the reparametrised Schrödinger curve has velocity
  `T · X_H`;
* ★★ `fsPathLength_schrodingerUnitary_smul` — **its length on `[0, 1]` is `2 T ΔH`**;
* ★★★ `fsAngle_schrodingerUnitary_smul_le` — **`arccos √P(p, exp(-iTH) • p) ≤ T ΔH`**;
* ★★ `arccos_div_le_time` — **the time needed is at least `arccos √P / ΔH`** when `ΔH > 0`.

## Honest scope

⚠️ **`ħ = 1`, and the corpus's metric.** The length is `2 T ΔH` because the corpus's metric is
four times the textbook one (#327, #329) and the distance is `2 arccos √P` (#330); the factors of
`2` cancel in the bound, which is the textbook statement.

⚠️ **Time-independent `H`.** The Hamiltonian is a fixed Hermitian matrix; the bound for a
time-dependent `H(t)` (with `∫ ΔH`) is not stated.

## References

J. Anandan, Y. Aharonov, Phys. Rev. Lett. 65 (1990) 1697; L. Mandelstam, I. Tamm, J. Phys. USSR 9
(1945) 249; `Instances/ProjectiveSpaceFSDistance.lean` (#330),
`Instances/ProjectiveSpaceUncertainty.lean` (#329); `specs/BACKLOG.md` #331;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization ENNReal Matrix.Norms.L2Operator
open Kahler DifferentialForm Set MeasureTheory

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- The Schrödinger curve run at speed `T`, `s ↦ exp(-isTH) • p`, has velocity `T · X_H`. -/
theorem hasMFDerivAt_schrodingerUnitary_smul_mul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) (T s : ℝ) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ))
      (fun s : ℝ => Matrix.schrodingerUnitary hH (s * T) • p) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (T • schrodingerField H (Matrix.schrodingerUnitary hH (s * T) • p))) := by
  have hγ := isMIntegralCurve_schrodingerUnitary_smul hH p (s * T)
  have hf : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s * T) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight T) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasDerivAt_mul_const T).hasFDerivAt
  have h := hγ.comp s hf
  refine h.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
  change ((1 : ℝ) • T) • (schrodingerField H (Matrix.schrodingerUnitary hH (s * T) • p) :
      Fin n → ℂ) = (1 : ℝ) • (T • schrodingerField H (Matrix.schrodingerUnitary hH (s * T) • p))
  rw [one_smul, one_smul]

/-- ★★ **The Schrödinger curve run at speed `T ≥ 0` has length `2 T ΔH` on `[0, 1]`.** -/
theorem fsPathLength_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) {T : ℝ} (hT : 0 ≤ T) :
    fsPathLength (fun s : ℝ => Matrix.schrodingerUnitary hH (s * T) • p) 0 1
      = ENNReal.ofReal (2 * (T * √(variance H p))) := by
  rw [fsPathLength_eq]
  have hspeed : ∀ s : ℝ, ENNReal.ofReal
      √(fsMetric (Matrix.schrodingerUnitary hH (s * T) • p)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ))
          (fun s : ℝ => Matrix.schrodingerUnitary hH (s * T) • p) s (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ))
          (fun s : ℝ => Matrix.schrodingerUnitary hH (s * T) • p) s (1 : ℝ)))
      = ENNReal.ofReal (2 * (T * √(variance H p))) := by
    intro s
    have hm : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ))
        (fun s : ℝ => Matrix.schrodingerUnitary hH (s * T) • p) s (1 : ℝ)
        = T • schrodingerField H (Matrix.schrodingerUnitary hH (s * T) • p) := by
      rw [(hasMFDerivAt_schrodingerUnitary_smul_mul hH p T s).mfderiv]
      change (1 : ℝ) • (T • schrodingerField H (Matrix.schrodingerUnitary hH (s * T) • p) :
        Fin n → ℂ) = _
      rw [one_smul]
    rw [hm, fsMetric_smul_smul, fsMetric_schrodingerField_self hH,
      variance_schrodingerUnitary_smul hH]
    congr 1
    rw [show T ^ 2 * (4 * variance H p) = (2 * (T * √(variance H p))) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt (variance_nonneg hH p)]
      ring]
    exact Real.sqrt_sq (by positivity)
  refine (lintegral_congr hspeed).trans ?_
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- ★★★ **The quantum speed limit** (Anandan–Aharonov, Mandelstam–Tamm): in time `T ≥ 0` the
state turns through an angle at most `T ΔH`, `arccos √P(p, exp(-iTH) • p) ≤ T ΔH`. -/
theorem fsAngle_schrodingerUnitary_smul_le {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) {T : ℝ} (hT : 0 ≤ T) :
    fsAngle p (Matrix.schrodingerUnitary hH T • p) ≤ T * √(variance H p) := by
  set γ : ℝ → ℙ ℂ (Ambient n) := fun s => Matrix.schrodingerUnitary hH (s * T) • p
  have hd : ∀ s, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s := fun s =>
    (hasMFDerivAt_schrodingerUnitary_smul_mul hH p T s).mdifferentiableAt
  have hc : ContinuousOn γ (Icc 0 1) := fun s _ => (hd s).continuousAt.continuousWithinAt
  have h := ofReal_two_mul_fsAngle_le_fsPathLength_of hc fun s _ => hd s
  rw [fsPathLength_schrodingerUnitary_smul hH p hT] at h
  have h0 : γ 0 = p := by
    show Matrix.schrodingerUnitary hH (0 * T) • p = p
    rw [zero_mul, schrodingerUnitary_zero_smul hH]
  have h1 : γ 1 = Matrix.schrodingerUnitary hH T • p := by
    show Matrix.schrodingerUnitary hH (1 * T) • p = _
    rw [one_mul]
  rw [h0, h1, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

/-- ★★ **The time needed to reach a ray at transition probability `P` is at least
`arccos √P / ΔH`**, for a state with energy spread `ΔH > 0`. -/
theorem arccos_div_le_time {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian)
    (p : ℙ ℂ (Ambient n)) {T : ℝ} (hT : 0 ≤ T) (hv : 0 < variance H p) :
    Real.arccos √(transProb p (Matrix.schrodingerUnitary hH T • p)) / √(variance H p) ≤ T := by
  rw [div_le_iff₀ (Real.sqrt_pos.2 hv)]
  exact fsAngle_schrodingerUnitary_smul_le hH p hT

end Projectivization
