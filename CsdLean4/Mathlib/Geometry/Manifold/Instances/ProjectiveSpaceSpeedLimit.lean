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

## Time-dependent Hamiltonians (#335)

For a family `H(t)` of Hermitian matrices and any curve `γ` with `γ'(t) = X_{H(t)}(γ t)` on
`[0, T]`:

* ★★ `fsPathLength_eq_lintegral_sqrt_variance` — **the length of `γ` on `[0, T]` is
  `∫ 2 ΔH(t)`**, with `ΔH(t)` the spread of `H(t)` in the state `γ t`;
* ★★★ `ofReal_fsAngle_le_lintegral_sqrt_variance` — **`arccos √P(γ 0, γ T) ≤ ∫₀ᵀ ΔH(t) dt`**
  (in `ℝ≥0∞`, no integrability needed), through the reparametrisation `s ↦ γ (s T)` of `[0, 1]`;
* ★★ `fsAngle_le_integral_sqrt_variance` — the same in `ℝ` when `t ↦ ΔH(t)` is integrable.

## Honest scope

⚠️ **`ħ = 1`, Anandan–Aharonov's normalisation.** The length is `2 T ΔH` because the metric is
Anandan–Aharonov's `ds² = 4(1 − |⟨ψ|ψ + dψ⟩|²)` (#327, #329), four times
`⟨dψ, dψ⟩ − |⟨ψ, dψ⟩|²`, and the distance is `2 arccos √P` (#330); the factors of `2` cancel in
the bound, which is the textbook statement.

⚠️ **Time-dependent `H` assumes the solution.** The `H(t)` bounds (#335) hold for any curve
solving `γ'(t) = X_{H(t)}(γ t)` on `[0, T]` (a two-sided derivative at each `t` of `[0, T]`);
that such a curve exists — the time-ordered exponential — is not proved here.

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

/-! ### Time-dependent Hamiltonians (#335) -/

attribute [local instance] fsENorm fsENormSMulClass

/-- ★★ **The length of a solution of `γ' = X_{H(t)}(γ)` on `[0, T]` is `∫ 2 ΔH(t)`.** -/
theorem fsPathLength_eq_lintegral_sqrt_variance {H : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : ∀ t, (H t).IsHermitian) {γ : ℝ → ℙ ℂ (Ambient n)} {T : ℝ}
    (hγ : ∀ t ∈ Icc 0 T, HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (schrodingerField (H t) (γ t)))) :
    fsPathLength γ 0 T = ∫⁻ t in Icc 0 T, ENNReal.ofReal (2 * √(variance (H t) (γ t))) := by
  rw [fsPathLength_eq]
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  have hm : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ)
      = schrodingerField (H t) (γ t) := by
    rw [(hγ t ht).mfderiv]
    change (1 : ℝ) • (schrodingerField (H t) (γ t) : Fin n → ℂ) = _
    rw [one_smul]
  rw [hm, fsMetric_schrodingerField_self (hH t)]
  congr 1
  rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- ★★★ **The quantum speed limit for a time-dependent Hamiltonian**:
`arccos √P(γ 0, γ T) ≤ ∫₀ᵀ ΔH(t) dt` along any solution of `γ' = X_{H(t)}(γ)`. -/
theorem ofReal_fsAngle_le_lintegral_sqrt_variance
    {H : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : ∀ t, (H t).IsHermitian)
    {γ : ℝ → ℙ ℂ (Ambient n)} {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc 0 T, HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (schrodingerField (H t) (γ t)))) :
    ENNReal.ofReal (fsAngle (γ 0) (γ T))
      ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal √(variance (H t) (γ t)) := by
  have hdiff : ∀ t ∈ Icc 0 T, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t :=
    fun t ht => (hγ t ht).mdifferentiableAt
  have hfI : ∀ s ∈ Icc (0 : ℝ) 1, s * T ∈ Icc 0 T := fun s hs =>
    ⟨mul_nonneg hs.1 hT, by nlinarith [hs.2]⟩
  have hfd : ∀ s : ℝ, HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s * T) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight T) :=
    fun s => hasMFDerivAt_iff_hasFDerivAt.2 (hasDerivAt_mul_const T).hasFDerivAt
  have hδd : ∀ s ∈ Icc (0 : ℝ) 1,
      MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (γ ∘ fun s : ℝ => s * T) s :=
    fun s hs => (hdiff _ (hfI s hs)).comp s (hfd s).mdifferentiableAt
  have hc : ContinuousOn (γ ∘ fun s : ℝ => s * T) (Icc 0 1) :=
    fun s hs => (hδd s hs).continuousAt.continuousWithinAt
  have h := ofReal_two_mul_fsAngle_le_fsPathLength_of hc
    fun s hs => hδd s (Ioo_subset_Icc_self hs)
  have hre : fsPathLength (γ ∘ fun s : ℝ => s * T) 0 1 = fsPathLength γ 0 T := by
    have hr := Manifold.pathELength_comp_of_monotoneOn (I := 𝓘(ℝ, Fin n → ℂ)) (γ := γ)
      (a := 0) (b := 1) (f := fun s : ℝ => s * T) zero_le_one
      (fun x _ y _ hxy => mul_le_mul_of_nonneg_right hxy hT)
      (fun s _ => (hasDerivAt_mul_const T).differentiableAt.differentiableWithinAt)
      (fun t ht => (hdiff t (by simpa using ht)).mdifferentiableWithinAt)
    simpa [fsPathLength] using hr
  rw [hre, fsPathLength_eq_lintegral_sqrt_variance hH hγ] at h
  have h0 : (γ ∘ fun s : ℝ => s * T) 0 = γ 0 := by simp
  have h1 : (γ ∘ fun s : ℝ => s * T) 1 = γ T := by simp
  rw [h0, h1] at h
  have h2 : ∫⁻ t in Icc 0 T, ENNReal.ofReal (2 * √(variance (H t) (γ t)))
      = 2 * ∫⁻ t in Icc 0 T, ENNReal.ofReal √(variance (H t) (γ t)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at h
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) ENNReal.ofNat_ne_top).1 h

/-- ★★ **The time-dependent speed limit in `ℝ`**: `arccos √P(γ 0, γ T) ≤ ∫₀ᵀ ΔH(t) dt` when
`t ↦ ΔH(t)` is integrable on `[0, T]`. -/
theorem fsAngle_le_integral_sqrt_variance {H : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : ∀ t, (H t).IsHermitian) {γ : ℝ → ℙ ℂ (Ambient n)} {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc 0 T, HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (schrodingerField (H t) (γ t))))
    (hi : IntegrableOn (fun t => √(variance (H t) (γ t))) (Icc 0 T)) :
    fsAngle (γ 0) (γ T) ≤ ∫ t in (0 : ℝ)..T, √(variance (H t) (γ t)) := by
  have h := ofReal_fsAngle_le_lintegral_sqrt_variance hH hT hγ
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
  have hnn : 0 ≤ ∫ t in Icc 0 T, √(variance (H t) (γ t)) :=
    setIntegral_nonneg measurableSet_Icc fun t _ => Real.sqrt_nonneg _
  rw [← ENNReal.ofReal_le_ofReal_iff hnn,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => Real.sqrt_nonneg _)]
  exact h

end Projectivization
