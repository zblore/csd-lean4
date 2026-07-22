/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.WeakMeasurement

/-!
# Empirical/CSD: the quantum Zeno effect (Build 15d)

**Category:** 3-Local (CSD-ontic volume layer; the freezing-under-frequent-measurement
entry of the open-system tranche, after einselection (15a), QEC-decoherence (15b), and
weak measurement (15c)).

A **watched system does not evolve.** Frequent projective measurements onto the initial
state freeze the dynamics: the survival probability tends to one as the number of
measurements grows. This file derives the mechanism and the limit, then states the honest
CSD reading.

## Part A: the Zeno mechanism (quadratic short-time decay, DERIVED)

For a Hermitian `H` and unit `ψ` the survival amplitude is `a(s) = ⟨ψ, exp(-isH) ψ⟩` and
the survival probability `P(s) = ‖a(s)‖²`. The Zeno mechanism is the *quadratic* short-time
behaviour: the initial decay slope vanishes (`P'(0) = 0`) and the leading correction is
`-(ΔH)²s²` for the variance `(ΔH)² = ⟨ψ,H²ψ⟩ − ⟨ψ,Hψ⟩²`.

**Concrete qubit witness.** This file realises the mechanism on the witness `H = σx`,
`ψ = |0⟩`, where the evolution is the closed-form qubit rotation
`exp(-isσx) = cos s · I − i sin s · σx` (`zenoU`; the standard matrix-exponential identity
for the involution `σx²=I`, taken as the closed form, not re-derived from `Matrix.exp`).
Everything downstream is then *derived*:

- the survival amplitude `a(s) = ⟨0, zenoU s · 0⟩ = cos s` (`survAmp_eq`), so
  `P(s) = cos² s` (`survProb_eq`) -- the genuine matrix computation, not asserted;
- the variance `(ΔH)² = ⟨0,σx²·0⟩ − ⟨0,σx·0⟩² = 1 − 0 = 1` (`varH_eq`), computed from the
  matrices (`meanH_eq`, `meanHsq_eq`);
- the **quadratic bound** `P(s) ≥ 1 − (ΔH)²·s²` (`zeno_survival_quadratic`), derived from
  `cos²s = 1 − sin²s ≥ 1 − s²` (`Real.sin_sq_le_sq`); the coefficient is exactly the
  variance, not a free parameter -- this is the physics, not a hypothesis;
- the **zero initial slope** `P'(0) = 0` (`zeno_survival_slope_zero`), via `HasDerivAt` on
  `s ↦ cos² s`. This zero slope is *why* frequent measurement freezes evolution.

## Part B: the Zeno limit (freezing, DERIVED)

`n` equally-spaced projective re-measurements onto `|0⟩` over a fixed total time `t` give
survival `P_n = P(t/n)^n` (`zenoSurvival`). Then:

- `zeno_survival_lower_bound`: `P_n ≥ 1 − (ΔH)²t²/n`, derived from the Part-A quadratic
  bound plus Bernoulli's inequality `(1−x)^n ≥ 1 − nx` (`one_add_mul_le_pow`);
- `zeno_freezing` (headline): `Tendsto (fun n => P_n) atTop (nhds 1)` -- frequent
  measurement freezes the state -- by squeezing `1 − (ΔH)²t²/n ≤ P_n ≤ 1` between two
  sequences tending to one (`tendsto_of_tendsto_of_tendsto_of_le_of_le`). The full squeeze
  is proved, not just the lower bound.

**Non-vacuity.** `(ΔH)² = 1 > 0` (`zeno_variance_pos`): `|0⟩` is *not* a `σx`-eigenstate,
so absent measurement the state genuinely evolves -- at `s = π/2` the survival is `0`
(`zeno_no_measurement_decays`, the state has fully precessed away). The freezing is a real
effect of the repeated measurement, not a fixed-point triviality. (For an eigenstate
`(ΔH)²=0` the result is trivial; the genuine Zeno case is `(ΔH)²>0`.)

## Part C: the CSD reading and its D1 gating

The honest CSD reading: each projective measurement **re-carves the Σ-volume onto the
initial sector** `|0⟩`; frequent re-carving freezes the ontic-volume evolution, and the
survival probability `P_n → 1` is the ontic volume staying concentrated on the initial
sector. The single-step survival `P(s) = ‖⟨0, zenoU s·0⟩‖²` is the rank-1 Born weight of
the `|0⟩` outcome, which the moment-map / Duistermaat-Heckman cluster
(`fs_born_volume_ratio_N`, imported one layer down, Gleason-free) reads as a
Fubini-Study volume ratio on the ontic `Σ`; this file does not re-prove that and does not
fake a new volume theorem.

The **dynamical** realisation -- the measurement-interspersed Σ-flow `Φ` whose iteration
freezes the ontic trajectory, the Zeno limit as a property of the de-isolation flow -- is
**D1-gated to LF6** (`Φ = id` in every concrete `SectorData`). What is delivered here is
the operational / survival-probability freezing; the ontic-flow realisation is not claimed.

All exports are foundational-triple-only (no `busch_effect_gleason`): concrete `Matrix`
algebra over `EuclideanSpace ℂ (Fin 2)`, real trigonometric inequalities, and the Bernoulli
/ squeeze limit.
-/

open Matrix Filter
open scoped ComplexOrder

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QuantumZeno

open WeakMeasurement

/-! ### The witness observable and the closed-form qubit rotation -/

/-- The measurement observable `σx = !![0,1;1,0]` (the unit Pauli-X axis). The preparation
`|0⟩` (`WeakMeasurement.e0`) is not an eigenstate of `σx`, so it genuinely evolves. -/
noncomputable def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- `σx² = I` (the Pauli involution). -/
lemma σx_mul_self : σx * σx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, Matrix.mul_apply, Fin.sum_univ_two]

/-- The closed-form qubit rotation `zenoU s = cos s · I − i sin s · σx`, i.e.
`exp(-isσx)` (the standard matrix-exponential identity for the involution `σx²=I`, with
`θ = -is`; taken as the closed form, not re-derived from `Matrix.exp`). It is the
deterministic, unitary evolution generated by `σx` for a time `s`. -/
noncomputable def zenoU (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos s : ℂ), -(Complex.I * (Real.sin s : ℂ));
     -(Complex.I * (Real.sin s : ℂ)), (Real.cos s : ℂ)]

/-- `zenoU s = cos s · I − i sin s · σx` (the closed-form linkage to `exp(-isσx)`). -/
lemma zenoU_closed_form (s : ℝ) :
    zenoU s = (Real.cos s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - (Complex.I * (Real.sin s : ℂ)) • σx := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zenoU, σx]

/-! ### The `⟨0, M·0⟩` sandwich on the qubit -/

private lemma toEuclideanLin_ofLp (M : Matrix (Fin 2) (Fin 2) ℂ)
    (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (Matrix.toEuclideanLin M v).ofLp i = (M *ᵥ v.ofLp) i := rfl

private lemma mulVec_e0 (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (M *ᵥ e0.ofLp) i = M i 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e0_ofLp_zero, e0_ofLp_one]

/-- The diagonal sandwich `⟨0, M·0⟩ = M₀₀` on the `|0⟩` preparation. -/
private lemma inner_e0_M (M : Matrix (Fin 2) (Fin 2) ℂ) :
    inner ℂ e0 (Matrix.toEuclideanLin M e0) = M 0 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [toEuclideanLin_ofLp, mulVec_e0, Pi.star_apply, e0_ofLp_zero, e0_ofLp_one,
    star_one, star_zero, mul_one, mul_zero, add_zero]

/-! ### Part A: survival amplitude, probability, and the variance -/

/-- The **survival amplitude** `a(s) = ⟨0, exp(-isσx)·0⟩` on the `|0⟩` preparation. -/
noncomputable def survAmp (s : ℝ) : ℂ := inner ℂ e0 (Matrix.toEuclideanLin (zenoU s) e0)

/-- The **survival probability** `P(s) = ‖a(s)‖²`. -/
noncomputable def survProb (s : ℝ) : ℝ := ‖survAmp s‖ ^ 2

/-- **(Part A) The survival amplitude is `cos s`** -- derived from the matrix `zenoU s`,
not asserted. -/
lemma survAmp_eq (s : ℝ) : survAmp s = (Real.cos s : ℂ) := by
  rw [survAmp, inner_e0_M]; simp [zenoU]

/-- **(Part A) The survival probability is `cos² s`.** -/
lemma survProb_eq (s : ℝ) : survProb s = Real.cos s ^ 2 := by
  rw [survProb, survAmp_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma survProb_nonneg (s : ℝ) : 0 ≤ survProb s := by rw [survProb]; positivity

lemma survProb_le_one (s : ℝ) : survProb s ≤ 1 := by
  rw [survProb_eq]; nlinarith [Real.neg_one_le_cos s, Real.cos_le_one s]

/-- The mean `⟨H⟩ = ⟨0, σx·0⟩`. -/
noncomputable def meanH : ℝ := RCLike.re (inner ℂ e0 (Matrix.toEuclideanLin σx e0))

/-- The second moment `⟨H²⟩ = ⟨0, σx²·0⟩`. -/
noncomputable def meanHsq : ℝ := RCLike.re (inner ℂ e0 (Matrix.toEuclideanLin (σx * σx) e0))

/-- The variance `(ΔH)² = ⟨H²⟩ − ⟨H⟩²`. -/
noncomputable def varH : ℝ := meanHsq - meanH ^ 2

/-- `⟨H⟩ = 0`: `|0⟩` is centred on the `σx` axis (computed from the matrix). -/
lemma meanH_eq : meanH = 0 := by rw [meanH, inner_e0_M]; simp [σx]

/-- `⟨H²⟩ = 1`: from `σx² = I` and `‖|0⟩‖ = 1`. -/
lemma meanHsq_eq : meanHsq = 1 := by
  rw [meanHsq, σx_mul_self, inner_e0_M]; simp

/-- **(Part A) The variance `(ΔH)² = 1`** -- computed from the matrices, not assumed. This
is the coefficient in the quadratic bound below. -/
lemma varH_eq : varH = 1 := by rw [varH, meanHsq_eq, meanH_eq]; norm_num

/-- **(Part A, non-vacuity) `(ΔH)² > 0`**: `|0⟩` is not a `σx`-eigenstate, so the state
genuinely evolves absent measurement. -/
theorem zeno_variance_pos : 0 < varH := by rw [varH_eq]; norm_num

/-- **(Part A core) The Zeno mechanism: quadratic short-time bound**
`P(s) ≥ 1 − (ΔH)²·s²`. Derived from `cos²s = 1 − sin²s ≥ 1 − s²` with the coefficient
equal to the computed variance. The quadratic (not linear) leading behaviour is the
freezing mechanism. -/
theorem zeno_survival_quadratic (s : ℝ) : 1 - varH * s ^ 2 ≤ survProb s := by
  rw [varH_eq, survProb_eq, one_mul]
  have hsin : Real.sin s ^ 2 ≤ s ^ 2 := Real.sin_sq_le_sq
  have hpyth := Real.sin_sq_add_cos_sq s
  linarith

/-- **(Part A) Zero initial decay slope `P'(0) = 0`.** The survival probability has a
vanishing first derivative at `s = 0`; this is the precise sense in which a watched system
does not begin to evolve. Proved via `HasDerivAt` on `s ↦ cos² s`. -/
theorem zeno_survival_slope_zero : HasDerivAt survProb 0 0 := by
  have hfun : survProb = Real.cos ^ 2 := by funext s; rw [survProb_eq]; rfl
  rw [hfun]
  simpa using (Real.hasDerivAt_cos 0).pow 2

/-! ### Part B: the Zeno limit (freezing under frequent measurement) -/

/-- Bernoulli + monotonicity helper: if `0 ≤ P`, `1 − u ≤ P`, `0 ≤ u`, then
`1 − n·u ≤ P^n`. -/
private lemma pow_lower {P u : ℝ} (n : ℕ) (hP : 0 ≤ P) (hPu : 1 - u ≤ P) (_hu : 0 ≤ u) :
    1 - n * u ≤ P ^ n := by
  by_cases hu1 : u ≤ 1
  · have hb : (0 : ℝ) ≤ 1 - u := by linarith
    have h1 : (1 - u) ^ n ≤ P ^ n := pow_le_pow_left₀ hb hPu n
    have h2 : 1 - (n : ℝ) * u ≤ (1 - u) ^ n := by
      have h := one_add_mul_le_pow (a := -u) (by linarith) n
      have e1 : 1 + (n : ℝ) * -u = 1 - (n : ℝ) * u := by ring
      have e2 : (1 : ℝ) + -u = 1 - u := by ring
      rw [e1, e2] at h; exact h
    linarith
  · have hu1' : 1 < u := not_le.mp hu1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnu : (1 : ℝ) ≤ (n : ℝ) * u := by nlinarith
      exact le_trans (by linarith) (pow_nonneg hP n)

/-- `n` equally-spaced projective re-measurements onto `|0⟩` over total time `t`: the
survival probability `P_n = P(t/n)^n`. -/
noncomputable def zenoSurvival (t : ℝ) (n : ℕ) : ℝ := survProb (t / n) ^ n

lemma zenoSurvival_le_one (t : ℝ) (n : ℕ) : zenoSurvival t n ≤ 1 := by
  rw [zenoSurvival]; exact pow_le_one₀ (survProb_nonneg _) (survProb_le_one _)

/-- **(Part B) The Zeno lower bound** `P_n ≥ 1 − (ΔH)²t²/n`. Derived from the Part-A
quadratic bound plus Bernoulli's inequality. -/
theorem zeno_survival_lower_bound (t : ℝ) (n : ℕ) :
    1 - varH * t ^ 2 / n ≤ zenoSurvival t n := by
  rw [varH_eq, one_mul, zenoSurvival]
  have hrel : (n : ℝ) * (t / n) ^ 2 = t ^ 2 / n := by
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · simp [h]
    · field_simp
  have hq : 1 - (t / n) ^ 2 ≤ survProb (t / n) := by
    have := zeno_survival_quadratic (t / n)
    rwa [varH_eq, one_mul] at this
  have hlow := pow_lower (P := survProb (t / n)) (u := (t / n) ^ 2) n
    (survProb_nonneg _) hq (sq_nonneg _)
  rwa [hrel] at hlow

/-- **(Part B headline) The Zeno freezing theorem.** Under `n → ∞` equally-spaced
projective re-measurements over a fixed total time `t`, the survival probability tends to
one: a watched system does not evolve. Proved by squeezing `1 − (ΔH)²t²/n ≤ P_n ≤ 1`. -/
theorem zeno_freezing (t : ℝ) :
    Tendsto (fun n => zenoSurvival t n) atTop (nhds 1) := by
  have hlow : Tendsto (fun n : ℕ => 1 - varH * t ^ 2 / n) atTop (nhds 1) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => 1 - varH * t ^ 2 * (1 / (n : ℝ))) atTop (nhds 1) := by
      have hc := (h0.const_mul (varH * t ^ 2))
      rw [mul_zero] at hc
      simpa using tendsto_const_nhds.sub hc
    have e : (fun n : ℕ => 1 - varH * t ^ 2 / (n : ℝ))
        = (fun n : ℕ => 1 - varH * t ^ 2 * (1 / (n : ℝ))) := by
      funext n; rw [mul_one_div]
    rw [e]; exact h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => zeno_survival_lower_bound t n) (fun n => zenoSurvival_le_one t n)

/-- **(Part B, non-vacuity) Without measurement the state decays.** At the single time
`s = π/2` the survival probability is `0`: `|0⟩` precesses entirely off the `σx` axis. So
the freezing `zeno_freezing` is a genuine effect of the repeated measurement, contrasting
the free evolution that would carry the state away. -/
theorem zeno_no_measurement_decays : survProb (Real.pi / 2) = 0 := by
  rw [survProb_eq, Real.cos_pi_div_two]; norm_num

/-- **(Non-vacuity bundle)** The genuine Zeno regime: positive variance (the state would
evolve) together with full free decay at `s = π/2` (it does evolve, maximally), against
which the freezing limit is non-trivial. -/
theorem zeno_nonvacuous : 0 < varH ∧ survProb (Real.pi / 2) = 0 :=
  ⟨zeno_variance_pos, zeno_no_measurement_decays⟩

end QuantumZeno
end CSDBridge
end Empirical
end CSD
