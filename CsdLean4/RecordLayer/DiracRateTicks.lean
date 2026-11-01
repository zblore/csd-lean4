/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracDeviceTicks

/-!
# An uncalibrated tick counter

**Category:** 7-SigmaLayer (the record layer). BACKLOG #273 (residue of ~~#271~~).

~~#271~~'s detector integrates the device's rectified reading and writes tick `n` at the threshold
`2gn|C₀|/R`: it must be told the device's own rate `R`. #253 and #256 set those thresholds from the
moving clocks' dilated rates, so the dilation was put into the counters by hand. Here a counter
calibrated at another rate `R₀` is shown to stay locked only for `n |R/R₀ − 1| < 1/2` turns, and a
counter that needs no rate is built: it integrates the positive part of the reading's **rate**.
That rate is the splitting coherence `S = i dC/dt`, a quadratic observable of the device built from
its Hamiltonian; for an exact turn it is `R e^{−iRt} C₀`, so each turn adds `2|C₀|` to the register
whatever `R` is, and tick `n`'s threshold is `2gn|C₀|`. #253's and #256's clocks are now counted
this way, with their tick windows unchanged.

## The splitting coherence

* `splitCoherence`, `continuous_splitCoherence`; ★★ `hasDerivAt_deviceCoherence` — **along the
  device `dC/dt = −i S`**; `norm_exp_I_mul_sub_le`;
* ★★ `splitCoherence_devicePacket` (each momentum's coherence weighted by its splitting `R_m`),
  ★ `splitCoherence_single` (**one mode: `S = R e^{−iRt} C₀` exactly**);
* `deviceProp_devicePacket_shift` (moved from `DiracDoppler.lean`), `levelWeight_mul_rate_le`;
  ★★★ `splitCoherence_shift_sharp` — **from any start `t₁`, `S(t₁ + s)` is within `(1 + R|s|)` times
  the sharp drift of `R e^{−iRs} C(t₁)`**.

## A counter calibrated at another rate

* `integral_max_cos_of_near`, ★ `integral_max_cos_lobe` (the register at a lobe's edges is
  `(2n ± 1)κ/R`);
* ★★ `calibrated_lock` — **thresholds `2n|C₀|/R₀` on a reading turning exactly at `R` are crossed
  within a quarter turn of `2πn/R` while `n |R/R₀ − 1| < 1/2`**; ★★ `calibrated_slip` — **beyond
  that they are crossed before the `n`-th lobe or not before the `(n + 1)`-th**.

## The rate counter

* `weightFlow` (a register integrating any weight; `tickFlow_eq_weightFlow`), `state_weightFlow`,
  `register_weightFlow`, `weightFlow_zero`, `continuous_weight_deviceProp`, `weightFlow_add`,
  `continuous_weightFlow`, `measurable_weightFlow`, `weightEvolve`, `weightEvolve_self`,
  `weightEvolve_comp`, `measurable_weightEvolve`;
* `rateWeight`, `rateWeight_nonneg`, `continuous_rateWeight`, ★ `hasDerivAt_quarterReading` (**the
  rate weight's argument is the derivative of the reading against the quarter-turned mark**),
  ★ `rateWeight_tickMark`, ★ `abs_rateWeight_sub_le`, `integral_rateWeight_mono`,
  ★★ `abs_integral_rateWeight_sub_le` (a drift `(1 + R|s|) ε` moves the register by at most
  `ε (t + R t²/2)`);
* ★★★ `rateTickDetector` — **tick `n` written at exactly `2πn/R`, threshold `2gn|C₀|`**;
  ★★★ `rateDriftDetector` — **for a drifting device, inside `[2πn/R − δ, 2πn/R + δ]`** whenever
  `δ ≤ 1/R` and `ε ((2πn/R + δ)² + 2(2πn/R + δ)/R) < |C₀| δ`.

## The devices

* ★★★ `singleRateTick` (~~#271~~'s device in one mode, exact), ★★★ `deviceRateTick` (#262's device);
* ★★★ `dirac_rate_ticks` — **#262's device read by the rate counter: `dC/dt = −i S`; `S` drifts
  from `R e^{−iRt} C₀` by at most `(1 + R|t|)` times the sharp drift; every tick an occurrence of one
  evolution, which carries the device; threshold `2gn|C₀|`, free of `R`; tick `n` written inside
  `[2πn/R − δ, 2πn/R + δ]`.**

## The findings

1. **A counter calibrated at rest loses a moving clock's turns.** With `R/R₀ = 3/5` (#253's moving
   clock) the lock condition `n |R/R₀ − 1| < 1/2` holds only up to tick `1`; with `4/5` (#256's) only
   up to tick `2` (the arithmetic of `calibrated_lock` and `calibrated_slip`, not separate theorems).
2. **Counting the rate needs no rate.** The register gains `2|C₀|` per turn at any `R`, so the same
   counter, set from the device's own starting reading, counts the turns of the device at rest and
   in motion. #253's `dirac_two_observers` and #256's `dirac_doppler` now use it, with the same
   tick windows: the dilation and the Doppler factor they read off are no longer put in by the
   counters' thresholds.

## Honest scope

⚠️ **The counter still reads the device's starting reading**: its mark is `C₀/|C₀|` and its
thresholds scale with `|C₀|`, both taken from the state at the start, not from the rate.

⚠️ **The weight is a stated law**: the register integrates `max(Re(ū S), 0)` by fiat, a test
detector without back-reaction (#251, #266).

⚠️ **The horizon is finite**, as in ~~#272~~: the drift condition gains the term `2(2πn/R + δ)/R`,
negligible in #253's and #256's instances.

References: `specs/BACKLOG.md` #273, #271, #272, #262, #253, #256, #251, #266, #39;
`RecordLayer/DiracTicks.lean` (`tickDetector`, `tickFlow`, `tickMark`, `re_star_tickMark_mul`,
`integral_max_cos`); `RecordLayer/DiracDeviceTicks.lean` (`driftTickDetector`, `deviceTick_facts`,
`deviceDrift`, `le_integral_max_cos_near`); `CV/DiracDevice.lean` (`hasDerivAt_devicePacket`,
`levelCoherence_eq`, `abs_levelClockRate_sub_le`); `RecordLayer/DiracTwin.lean`
(`dirac_two_observers`); `RecordLayer/DiracDoppler.lean` (`dirac_doppler`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### The splitting coherence -/

/-- **The splitting coherence** `S(Ψ) = Σ_p (ψ̄₀ (HΨ)₁ − conj((HΨ)₀) ψ₁)`: the coherence between the
device's levels weighted by their energies; along the evolution it is `i dC/dt`
(`hasDerivAt_deviceCoherence`). -/
noncomputable def splitCoherence (J μ₀ μ₁ : ℝ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℂ :=
  ∑ p, (star (Ψ (p, 0)) * (deviceHam J μ₀ μ₁ *ᵥ Ψ) (p, 1)
    - star ((deviceHam J μ₀ μ₁ *ᵥ Ψ) (p, 0)) * Ψ (p, 1))

theorem continuous_splitCoherence (J μ₀ μ₁ : ℝ) :
    Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => splitCoherence J μ₀ μ₁ Ψ := by
  have hH : Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => deviceHam (L := L) J μ₀ μ₁ *ᵥ Ψ :=
    Continuous.matrix_mulVec continuous_const continuous_id
  refine continuous_finsetSum _ fun p _ => ?_
  have h := ((continuous_star.comp (continuous_apply (p, 0))).mul
    ((continuous_apply (p, 1)).comp hH)).sub
    ((continuous_star.comp ((continuous_apply (p, 0)).comp hH)).mul (continuous_apply (p, 1)))
  exact h

/-- ★★ **The splitting coherence is the rate of the reading**: along the device,
`dC/dt = −i S`. -/
theorem hasDerivAt_deviceCoherence (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    HasDerivAt (fun s => deviceCoherence (devicePacket (L := L) J μ₀ μ₁ W β s))
      (-I * splitCoherence J μ₀ μ₁ (devicePacket (L := L) J μ₀ μ₁ W β t)) t := by
  have h := hasDerivAt_devicePacket (L := L) J μ₀ μ₁ W β t
  have hc := fun x => hasDerivAt_pi.1 h x
  unfold deviceCoherence splitCoherence
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun p _ =>
    ((hc (p, 0)).star).mul (hc (p, 1))
  convert hs using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_neg, Complex.star_def, Complex.conj_I]
  ring

/-- **A phase's drift**: `‖e^{ias} − e^{ibs}‖ ≤ |s| |a − b|`. -/
theorem norm_exp_I_mul_sub_le (a b s : ℝ) :
    ‖exp (I * ((a : ℂ) * (s : ℂ))) - exp (I * ((b : ℂ) * (s : ℂ)))‖ ≤ |s| * |a - b| := by
  have e : exp (I * ((a : ℂ) * (s : ℂ))) - exp (I * ((b : ℂ) * (s : ℂ)))
      = exp (I * ((b : ℂ) * (s : ℂ))) * (exp (I * (((a - b) * s : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, norm_exp_I_mul_ofReal_mul, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [Real.norm_eq_abs, abs_mul, mul_comm]

/-- ★★ **The splitting coherence, exactly**: each momentum's coherence weighted by its splitting
`R_m`, turning at `−R_m`. -/
theorem splitCoherence_devicePacket (J μ₀ μ₁ : ℝ) {W : Finset ℤ} (hD : Distinct L W) (β : ℤ → ℂ)
    (t : ℝ) :
    splitCoherence J μ₀ μ₁ (devicePacket (L := L) J μ₀ μ₁ W β t)
      = (1 / 2) * ∑ m ∈ W, levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m
          * ((levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ)
          * exp (I * (((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) * t)) := by
  set w := levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β)
  set Δ : ℤ → ℝ := fun m => bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m)
  have hF : (fun s => deviceCoherence (devicePacket (L := L) J μ₀ μ₁ W β s))
      = fun s : ℝ => (1 / 2) * ∑ m ∈ W, w m * exp (I * ((Δ m : ℂ) * (s : ℂ))) := by
    funext s
    rw [(device_observables J μ₀ μ₁ W β s).2.2, levelCoherence_eq J μ₀ μ₁ hD]
  have he : ∀ m, HasDerivAt (fun s : ℝ => w m * exp (I * ((Δ m : ℂ) * (s : ℂ))))
      (w m * (I * (Δ m : ℂ) * exp (I * ((Δ m : ℂ) * (t : ℂ))))) t := fun m => by
    have h1 := (((hasDerivAt_id t).ofReal_comp).const_mul (I * (Δ m : ℂ))).cexp.const_mul (w m)
    convert h1 using 1
    · funext s
      simp only [id]
      ring_nf
    · simp only [id, Complex.ofReal_one, mul_one]
      ring_nf
  have hG := (HasDerivAt.fun_sum (u := W) fun m _ => he m).const_mul (1 / 2 : ℂ)
  have hd := hasDerivAt_deviceCoherence (L := L) J μ₀ μ₁ W β t
  rw [hF] at hd
  have hu := hd.unique hG
  have hS : splitCoherence J μ₀ μ₁ (devicePacket (L := L) J μ₀ μ₁ W β t)
      = I * (-I * splitCoherence J μ₀ μ₁ (devicePacket (L := L) J μ₀ μ₁ W β t)) := by
    rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]
  rw [hS, hu, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hR : ((levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ) = -(Δ m : ℂ) := by
    simp only [Δ, levelClockRate, bandE]
    push_cast
    ring
  have hx : ((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) = (Δ m : ℂ) := rfl
  rw [hR, hx]
  linear_combination (1 / 2 * w m * (Δ m : ℂ) * exp (I * ((Δ m : ℂ) * (t : ℂ)))) * Complex.I_sq

/-- ★ **The device in one mode**: its splitting coherence is `R e^{−iRt} C₀` exactly. -/
theorem splitCoherence_single (J μ₀ μ₁ : ℝ) (m : ℤ) (β : ℤ → ℂ) (t : ℝ) :
    splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ t *ᵥ devicePacket J μ₀ μ₁ {m} β 0)
      = ((levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ)
        * (exp (I * (((-levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ) * t))
          * deviceCoherence (devicePacket (L := L) J μ₀ μ₁ {m} β 0)) := by
  rw [deviceProp_devicePacket, splitCoherence_devicePacket J μ₀ μ₁ (distinct_singleton m),
    (device_observables J μ₀ μ₁ {m} β 0).2.2, levelCoherence_eq J μ₀ μ₁ (distinct_singleton m),
    Finset.sum_singleton, Finset.sum_singleton]
  have e : ((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ)
      = ((-levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ) := by
    rw [levelClockRate, bandE, bandE]
    push_cast
    ring
  rw [e]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  ring

/-- **The device evolves from any start**: `e^{−itH_dev}` carries the device at `s` to `s + t`. -/
theorem deviceProp_devicePacket_shift (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (s t : ℝ) :
    deviceProp (L := L) J μ₀ μ₁ t *ᵥ devicePacket J μ₀ μ₁ W β s = devicePacket J μ₀ μ₁ W β (s + t) := by
  rw [← deviceProp_devicePacket _ _ _ _ _ s, ← deviceProp_devicePacket _ _ _ _ _ (s + t),
    Matrix.mulVec_mulVec, deviceProp_add]

/-- **One momentum's weight times its splitting's offset**: at most `‖β_m‖²` times the sharp rate
`c D (2c|p₀| + c D)(μ₁ − μ₀)/(2μ₀²)`. -/
theorem levelWeight_mul_rate_le {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (hℓ : 0 < ℓ) {m : ℤ} (hm : |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ) :
    ‖levelWeight (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (unitAmp L (scaledHop c (ℓ / L)) μ₀ β)
        (unitAmp L (scaledHop c (ℓ / L)) μ₁ β) m‖
      * |levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (angleZ L m))
        - levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀))|
      ≤ ‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2)) := by
  have hw := (levelWeight_unitAmp_bounds (L := L) (J := scaledHop c (ℓ / L)) h0 h01 β m).2
  have hK : |levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (angleZ L m))
      - levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀))|
      ≤ c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2) := by
    refine (abs_levelClockRate_sub_le h0 h01 _ _).trans ?_
    have hΔ : 0 ≤ μ₁ - μ₀ := by linarith
    have hX := abs_sq_sub_sq_scaled_le (L := L) hc hℓ hm
    gcongr
  exact mul_le_mul hw hK (abs_nonneg _) (sq_nonneg _)

/-- ★★★ **The splitting coherence of #262's device from any start**: at `t₁ + s` it is within
`(1 + R|s|)` times the sharp drift of `R e^{−iRs} C(t₁)`. -/
theorem splitCoherence_shift_sharp {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (hℓ : 0 < ℓ) {W : Finset ℤ} (hD : Distinct L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₁ s : ℝ) :
    ‖splitCoherence (scaledHop c (ℓ / L)) μ₀ μ₁
          (deviceProp (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ s
            *ᵥ devicePacket (scaledHop c (ℓ / L)) μ₀ μ₁ W β t₁)
        - ((levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) : ℝ) : ℂ)
          * (exp (I * (((-levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) : ℝ)
              : ℂ) * s))
            * deviceCoherence (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t₁))‖
      ≤ (1 + levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) * |s|)
        * deviceDrift c μ₀ μ₁ D p₀ := by
  set J := scaledHop c (ℓ / L)
  set R := levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))
  have hR0 : 0 ≤ R := (levelClockRate_pos h0 h01 _).le
  set w := levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β)
  set Rm : ℤ → ℝ := fun m => levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))
  have hΔ : ∀ m, ((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) = ((-Rm m : ℝ) : ℂ) :=
    fun m => by
      simp only [Rm, levelClockRate, bandE]
      push_cast
      ring
  rw [deviceProp_devicePacket_shift, splitCoherence_devicePacket J μ₀ μ₁ hD,
    (device_observables J μ₀ μ₁ W β t₁).2.2, levelCoherence_eq J μ₀ μ₁ hD]
  simp only [hΔ]
  have e : (1 / 2 : ℂ) * ∑ m ∈ W, w m * (Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * ((t₁ + s : ℝ) : ℂ)))
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * (s : ℂ)))
        * ((1 / 2 : ℂ) * ∑ m ∈ W, w m * exp (I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))))
      = (1 / 2 : ℂ) * ∑ m ∈ W, w m * exp (I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))
          * ((Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
            - (R : ℂ) * exp (I * (((-R : ℝ) : ℂ) * (s : ℂ)))) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : exp (I * (((-Rm m : ℝ) : ℂ) * ((t₁ + s : ℝ) : ℂ)))
        = exp (I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ))) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  rw [e, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have hterm : ∀ m ∈ W, ‖w m * exp (I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))
      * ((Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
        - (R : ℂ) * exp (I * (((-R : ℝ) : ℂ) * (s : ℂ))))‖
      ≤ (1 + R * |s|) * (‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2))) := by
    intro m hm
    have hb := levelWeight_mul_rate_le (L := L) hc h0 h01.le hℓ (hWD m hm) β
    rw [norm_mul, norm_mul, norm_exp_I_mul_ofReal_mul, mul_one]
    have hsplit : (Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
        - (R : ℂ) * exp (I * (((-R : ℝ) : ℂ) * (s : ℂ)))
        = ((Rm m - R : ℝ) : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
          + (R : ℂ) * (exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
            - exp (I * (((-R : ℝ) : ℂ) * (s : ℂ)))) := by
      push_cast
      ring
    have h1 : ‖(Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
        - (R : ℂ) * exp (I * (((-R : ℝ) : ℂ) * (s : ℂ)))‖
          ≤ |Rm m - R| + R * (|s| * |Rm m - R|) := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_exp_I_mul_ofReal_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
        refine mul_le_mul_of_nonneg_left ((norm_exp_I_mul_sub_le _ _ s).trans_eq ?_) hR0
        rw [show -Rm m - -R = -(Rm m - R) by ring, abs_neg]
    calc ‖w m‖ * ‖(Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
          - (R : ℂ) * exp (I * (((-R : ℝ) : ℂ) * (s : ℂ)))‖
        ≤ ‖w m‖ * (|Rm m - R| + R * (|s| * |Rm m - R|)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (1 + R * |s|) * (‖w m‖ * |Rm m - R|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  calc 1 / 2 * ‖∑ m ∈ W, w m * exp (I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))
          * ((Rm m : ℂ) * exp (I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
            - (R : ℂ) * exp (I * (((-R : ℝ) : ℂ) * (s : ℂ))))‖
      ≤ 1 / 2 * ∑ m ∈ W, (1 + R * |s|)
          * (‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2))) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (by norm_num)
    _ = (1 + R * |s|) * deviceDrift c μ₀ μ₁ D p₀ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, hβ, deviceDrift]
        ring

/-! ### A counter calibrated at another rate -/

/-- **The rectified reading near a mark, exactly**: on `[a, b]` within a quarter turn of the `n`-th
mark it is the reading itself, with integral `κ (sin Rb − sin Ra)/R`. -/
theorem integral_max_cos_of_near {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) (n : ℕ) {a b : ℝ}
    (hab : a ≤ b) (ha : n * (2 * Real.pi) - Real.pi / 2 ≤ R * a)
    (hb : R * b ≤ n * (2 * Real.pi) + Real.pi / 2) :
    ∫ s in a..b, max (κ * Real.cos (R * s)) 0 = κ * (Real.sin (R * b) - Real.sin (R * a)) / R := by
  rw [intervalIntegral.integral_congr (g := fun s => κ * Real.cos (R * s)) fun s hs => by
    rw [Set.uIcc_of_le hab] at hs
    refine max_eq_left (mul_nonneg hκ ?_)
    rw [← Real.cos_sub_nat_mul_two_pi (R * s) n]
    have h1 := mul_le_mul_of_nonneg_left hs.1 hR.le
    have h2 := mul_le_mul_of_nonneg_left hs.2 hR.le
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun v => Real.cos v) hR.ne', integral_cos, smul_eq_mul]
  field_simp

/-- ★ **The edges of a lobe**: the rectified reading's integral is `(2n + 1)κ/R` a quarter turn
after the `n`-th mark, and `(2n − 1)κ/R` a quarter turn before it. -/
theorem integral_max_cos_lobe {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) (n : ℕ) :
    (∫ s in (0 : ℝ)..2 * Real.pi * n / R + Real.pi / (2 * R), max (κ * Real.cos (R * s)) 0)
      = (2 * n + 1) * κ / R
    ∧ (∫ s in (0 : ℝ)..2 * Real.pi * n / R - Real.pi / (2 * R), max (κ * Real.cos (R * s)) 0)
      = (2 * n - 1) * κ / R := by
  have hc : Continuous fun s => max (κ * Real.cos (R * s)) 0 := by fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s => max (κ * Real.cos (R * s)) 0) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hI := integral_max_cos hκ hR n
  have hq : 0 < Real.pi / (2 * R) := by positivity
  have e0 : R * (2 * Real.pi * n / R) = n * (2 * Real.pi) := by field_simp
  have e1 : R * (2 * Real.pi * n / R + Real.pi / (2 * R)) = n * (2 * Real.pi) + Real.pi / 2 := by
    field_simp
  have e2 : R * (2 * Real.pi * n / R - Real.pi / (2 * R)) = n * (2 * Real.pi) - Real.pi / 2 := by
    field_simp
  have s0 : Real.sin (n * (2 * Real.pi)) = 0 := by
    rw [← zero_add (n * (2 * Real.pi)), Real.sin_add_nat_mul_two_pi, Real.sin_zero]
  have s1 : Real.sin (n * (2 * Real.pi) + Real.pi / 2) = 1 := by
    rw [add_comm, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have s2 : Real.sin (n * (2 * Real.pi) - Real.pi / 2) = -1 := by
    rw [sub_eq_neg_add, Real.sin_add_nat_mul_two_pi, Real.sin_neg, Real.sin_pi_div_two]
  constructor
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * Real.pi * n / R)) (hi _ _),
      hI, integral_max_cos_of_near hκ hR n (a := 2 * Real.pi * n / R)
        (b := 2 * Real.pi * n / R + Real.pi / (2 * R)) (by linarith)
        (by rw [e0]; linarith [Real.pi_pos]) (by rw [e1]),
      e0, e1, s0, s1]
    field_simp
    ring
  · have h := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 (2 * Real.pi * n / R - Real.pi / (2 * R))) (hi _ (2 * Real.pi * n / R))
    rw [hI, integral_max_cos_of_near hκ hR n (a := 2 * Real.pi * n / R - Real.pi / (2 * R))
      (b := 2 * Real.pi * n / R) (by linarith) (by rw [e2]) (by rw [e0]; linarith [Real.pi_pos]),
      e0, e2, s0, s2] at h
    field_simp at h ⊢
    linarith

/-- ★★ **A counter calibrated at `R₀` stays locked for a while**: for a reading turning exactly at
`R`, the register crosses the threshold `2n|C₀|/R₀` inside the `n`-th lobe (within a quarter turn
of `2πn/R`) while `n |R/R₀ − 1| < 1/2`. -/
theorem calibrated_lock {κ R R₀ : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hR₀ : 0 < R₀) (n : ℕ)
    (hlock : n * |R / R₀ - 1| < 1 / 2) :
    (∀ t, t < 2 * Real.pi * n / R - Real.pi / (2 * R) →
      ∫ s in (0 : ℝ)..t, max (κ * Real.cos (R * s)) 0 < 2 * n * κ / R₀)
    ∧ ∀ t, 2 * Real.pi * n / R + Real.pi / (2 * R) ≤ t →
      2 * n * κ / R₀ ≤ ∫ s in (0 : ℝ)..t, max (κ * Real.cos (R * s)) 0 := by
  obtain ⟨hhi, hlo⟩ := integral_max_cos_lobe hκ.le hR n
  have hx : 2 * n * κ / R₀ = 2 * n * (R / R₀) * κ / R := by field_simp
  have hl := abs_lt.1 (show |n * (R / R₀) - n| < 1 / 2 by
    rw [show (n : ℝ) * (R / R₀) - n = n * (R / R₀ - 1) by ring, abs_mul, Nat.abs_cast]
    exact hlock)
  have hm1 : (2 * n - 1) * κ / R < 2 * n * κ / R₀ := by
    rw [hx]
    exact div_lt_div_of_pos_right (by nlinarith) hR
  have hm2 : 2 * n * κ / R₀ < (2 * n + 1) * κ / R := by
    rw [hx]
    exact div_lt_div_of_pos_right (by nlinarith) hR
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := integral_max_cos_mono (R := R) hκ.le ht.le
    linarith
  · have := integral_max_cos_mono (R := R) hκ.le ht
    linarith

/-- ★★ **…and then slips**: once `n |R/R₀ − 1| > 1/2` the threshold `2n|C₀|/R₀` is crossed either
before the `n`-th lobe begins or not before the `(n + 1)`-th lobe begins: the counter has lost the
device's turns. -/
theorem calibrated_slip {κ R R₀ : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hR₀ : 0 < R₀) (n : ℕ)
    (hslip : 1 / 2 < n * |R / R₀ - 1|) :
    2 * n * κ / R₀ < ∫ s in (0 : ℝ)..2 * Real.pi * n / R - Real.pi / (2 * R),
        max (κ * Real.cos (R * s)) 0
    ∨ ∀ t, t ≤ 2 * Real.pi * (n + 1 : ℕ) / R - Real.pi / (2 * R) →
      ∫ s in (0 : ℝ)..t, max (κ * Real.cos (R * s)) 0 < 2 * n * κ / R₀ := by
  have hx : 2 * n * κ / R₀ = 2 * n * (R / R₀) * κ / R := by field_simp
  have habs : 1 / 2 < |n * (R / R₀) - n| := by
    rw [show (n : ℝ) * (R / R₀) - n = n * (R / R₀ - 1) by ring, abs_mul, Nat.abs_cast]
    exact hslip
  rcases lt_abs.1 habs with h | h
  · right
    intro t ht
    have hlo := (integral_max_cos_lobe hκ.le hR (n + 1)).2
    have := integral_max_cos_mono (R := R) hκ.le ht
    have hm : (2 * ((n + 1 : ℕ) : ℝ) - 1) * κ / R < 2 * n * κ / R₀ := by
      rw [hx]
      push_cast
      exact div_lt_div_of_pos_right (by nlinarith) hR
    linarith
  · left
    rw [(integral_max_cos_lobe hκ.le hR n).2, hx]
    exact div_lt_div_of_pos_right (by nlinarith) hR

/-! ### The register of a weight -/

section WeightFlow

variable (J μ₀ μ₁ g : ℝ) (f : ((ZMod L × Fin 2) × Fin 2 → ℂ) → ℝ)

/-- **The device with a register integrating a weight `f`** with gain `g`: the device evolves by
`e^{−itH_dev}`; `tickFlow` is the case `f = tickWeight u`. -/
noncomputable def weightFlow (t : ℝ) (x : TickArena L) : TickArena L :=
  (deviceProp J μ₀ μ₁ t *ᵥ x.1, x.2 + g * ∫ s in (0 : ℝ)..t, f (deviceProp J μ₀ μ₁ s *ᵥ x.1))

theorem tickFlow_eq_weightFlow (u : ℂ) :
    tickFlow (L := L) J μ₀ μ₁ g u = weightFlow J μ₀ μ₁ g (tickWeight u) := rfl

theorem state_weightFlow (t : ℝ) (x : TickArena L) :
    (weightFlow J μ₀ μ₁ g f t x).1 = deviceProp J μ₀ μ₁ t *ᵥ x.1 := rfl

theorem register_weightFlow (t : ℝ) (x : TickArena L) :
    (weightFlow J μ₀ μ₁ g f t x).2
      = x.2 + g * ∫ s in (0 : ℝ)..t, f (deviceProp J μ₀ μ₁ s *ᵥ x.1) := rfl

theorem weightFlow_zero (x : TickArena L) : weightFlow J μ₀ μ₁ g f 0 x = x := by
  ext
  · simp [weightFlow, deviceProp_zero]
  · simp [weightFlow]

variable {f}

theorem continuous_weight_deviceProp (hf : Continuous f) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    Continuous fun s => f (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ) :=
  hf.comp ((continuous_deviceProp_mulVec J μ₀ μ₁).comp (continuous_const.prodMk continuous_id))

theorem weightFlow_add (hf : Continuous f) (s t : ℝ) (x : TickArena L) :
    weightFlow J μ₀ μ₁ g f (s + t) x = weightFlow J μ₀ μ₁ g f t (weightFlow J μ₀ μ₁ g f s x) := by
  ext
  · simp only [weightFlow, deviceProp_add, Matrix.mulVec_mulVec]
  · simp only [weightFlow, Matrix.mulVec_mulVec, ← deviceProp_add]
    have hi : ∀ a b : ℝ, IntervalIntegrable
        (fun v => f (deviceProp (L := L) J μ₀ μ₁ v *ᵥ x.1)) volume a b :=
      fun a b => (continuous_weight_deviceProp J μ₀ μ₁ hf x.1).intervalIntegrable a b
    have hs : (∫ v in (0 : ℝ)..t, f (deviceProp (L := L) J μ₀ μ₁ (s + v) *ᵥ x.1))
        = ∫ v in s..s + t, f (deviceProp (L := L) J μ₀ μ₁ v *ᵥ x.1) := by
      rw [intervalIntegral.integral_comp_add_left
        (fun v => f (deviceProp (L := L) J μ₀ μ₁ v *ᵥ x.1)) s, add_zero]
    rw [hs, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s (s + t))]
    ring

theorem continuous_weightFlow (hf : Continuous f) (t : ℝ) :
    Continuous (weightFlow (L := L) J μ₀ μ₁ g f t) := by
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_deviceProp_mulVec J μ₀ μ₁).comp (continuous_fst.prodMk continuous_const)
  · refine continuous_snd.add (continuous_const.mul ?_)
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : TickArena L) s => f (deviceProp J μ₀ μ₁ s *ᵥ x.1)) ?_ 0 t
    exact hf.comp
      ((continuous_deviceProp_mulVec J μ₀ μ₁).comp (continuous_fst.fst.prodMk continuous_snd))

theorem measurable_weightFlow (hf : Continuous f) (t : ℝ) :
    Measurable (weightFlow (L := L) J μ₀ μ₁ g f t) :=
  (continuous_weightFlow J μ₀ μ₁ g hf t).measurable

variable (f)

/-- The two-time evolution. -/
noncomputable def weightEvolve (s t : OnticTime) : TickArena L → TickArena L :=
  weightFlow J μ₀ μ₁ g f (t - s)

theorem weightEvolve_self (t : OnticTime) :
    weightEvolve J μ₀ μ₁ g f t t = (id : TickArena L → TickArena L) := by
  funext x
  simp only [weightEvolve, sub_self, weightFlow_zero, id]

variable {f}

theorem weightEvolve_comp (hf : Continuous f) (s t v : OnticTime) :
    weightEvolve J μ₀ μ₁ g f t v ∘ weightEvolve J μ₀ μ₁ g f s t
      = (weightEvolve J μ₀ μ₁ g f s v : TickArena L → TickArena L) := by
  funext x
  simp only [weightEvolve, Function.comp]
  rw [show v - s = (t - s) + (v - t) by ring, weightFlow_add J μ₀ μ₁ g hf]

theorem measurable_weightEvolve (hf : Continuous f) (s t : OnticTime) :
    Measurable (weightEvolve (L := L) J μ₀ μ₁ g f s t) :=
  measurable_weightFlow J μ₀ μ₁ g hf (t - s)

end WeightFlow

/-! ### The rate counter -/

/-- **The rate weight**: the splitting coherence read against the mark `u`, rectified: the rate at
which the reading against the quarter-turned mark `−iu` grows, while it grows. -/
noncomputable def rateWeight (J μ₀ μ₁ : ℝ) (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℝ :=
  max (star u * splitCoherence J μ₀ μ₁ Ψ).re 0

theorem rateWeight_nonneg (J μ₀ μ₁ : ℝ) (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    0 ≤ rateWeight J μ₀ μ₁ u Ψ :=
  le_max_right _ _

theorem continuous_rateWeight (J μ₀ μ₁ : ℝ) (u : ℂ) :
    Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => rateWeight J μ₀ μ₁ u Ψ :=
  (Complex.continuous_re.comp (continuous_const.mul (continuous_splitCoherence J μ₀ μ₁))).max
    continuous_const

/-- **The rate read against the quarter-turned mark**: `Re(ū S)` is the derivative of
`Re(conj(−iu) C)` along the device. -/
theorem hasDerivAt_quarterReading (J μ₀ μ₁ : ℝ) (u : ℂ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    HasDerivAt (fun s => (star (-I * u) * deviceCoherence (devicePacket (L := L) J μ₀ μ₁ W β s)).re)
      (star u * splitCoherence J μ₀ μ₁ (devicePacket (L := L) J μ₀ μ₁ W β t)).re t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_deviceCoherence (L := L) J μ₀ μ₁ W β t).const_mul (star (-I * u)))
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  convert h using 2
  rw [star_mul', star_neg, show star I = -I from Complex.conj_I]
  linear_combination (star u * splitCoherence J μ₀ μ₁ (devicePacket (L := L) J μ₀ μ₁ W β t))
    * Complex.I_sq

/-- ★ **An exact turn, read by its rate**: if the splitting coherence is `R e^{−iRs} C₀`, the rate
weight against the mark is `max(R|C₀| cos(Rs), 0)`. -/
theorem rateWeight_tickMark {J μ₀ μ₁ : ℝ} {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) {R s : ℝ}
    (h : splitCoherence J μ₀ μ₁ Ψ
      = (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)) :
    rateWeight J μ₀ μ₁ (tickMark Ψ₀) Ψ = max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0 := by
  rw [rateWeight, h, mul_left_comm, Complex.re_ofReal_mul, re_star_tickMark_mul hC, mul_assoc]

/-- ★ **A drifting rate moves the rate weight by at most its drift.** -/
theorem abs_rateWeight_sub_le {J μ₀ μ₁ : ℝ} {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) {R s ε : ℝ}
    (h : ‖splitCoherence J μ₀ μ₁ Ψ
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ ε) :
    |rateWeight J μ₀ μ₁ (tickMark Ψ₀) Ψ - max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0|
      ≤ ε := by
  have e : R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)
      = (star (tickMark Ψ₀)
        * ((R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀))).re := by
    rw [mul_left_comm, Complex.re_ofReal_mul, re_star_tickMark_mul hC, mul_assoc]
  rw [rateWeight, e]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star, norm_tickMark hC, one_mul]
  exact h

section Rate

variable (J μ₀ μ₁ : ℝ) {R ε : ℝ} {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ}

theorem integral_rateWeight_mono {t₁ t : ℝ} (h : t₁ ≤ t) :
    (∫ s in (0 : ℝ)..t₁, rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      ≤ ∫ s in (0 : ℝ)..t,
        rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun s => rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      volume a b :=
    fun a b => (continuous_weight_deviceProp J μ₀ μ₁ (continuous_rateWeight J μ₀ μ₁ _)
      Ψ₀).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun s _ =>
    rateWeight_nonneg J μ₀ μ₁ (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
  linarith

/-- ★★ **The register of a drifting rate**: if the splitting coherence drifts by at most
`(1 + R|s|) ε`, the register is within `ε (t + R t²/2)` of the exact one. -/
theorem abs_integral_rateWeight_sub_le (hC : deviceCoherence Ψ₀ ≠ 0)
    (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε)
    {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      - ∫ s in (0 : ℝ)..t, max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0|
      ≤ ε * (t + R * t ^ 2 / 2) := by
  have hG := (continuous_weight_deviceProp J μ₀ μ₁ (continuous_rateWeight J μ₀ μ₁ (tickMark Ψ₀))
    Ψ₀).intervalIntegrable (μ := volume) 0 t
  have hF : IntervalIntegrable (fun s => max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0)
      volume 0 t :=
    (by fun_prop : Continuous fun s =>
      max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0).intervalIntegrable 0 t
  rw [← intervalIntegral.integral_sub hG hF, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun s => ε * (1 + R * s)) ht
    (Filter.Eventually.of_forall fun s hs => ?_)
    ((by fun_prop : Continuous fun s : ℝ => ε * (1 + R * s)).intervalIntegrable
      (μ := volume) 0 t)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    have h := abs_rateWeight_sub_le hC (hdrift s)
    rw [abs_of_pos hs.1] at h
    exact h.trans_eq (mul_comm _ ε)
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => R * x).intervalIntegrable 0 t),
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
    ring

end Rate

/-- ★★★ **A tick counted by the rate, exactly**: for a device whose splitting coherence turns
exactly as `R e^{−iRs} C₀`, `C₀ ≠ 0`, the register integrating the rate weight against the mark
`C₀/|C₀|` reaches the threshold `2gn|C₀|` (**no rate in it**) at **exactly** `2πn/R`, and holds it
for any window. -/
noncomputable def rateTickDetector (J μ₀ μ₁ g R : ℝ) (hg : 0 < g) (hR : 0 < R)
    (Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (hrot : ∀ t, splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ t *ᵥ Ψ₀)
      = (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * t)) * deviceCoherence Ψ₀))
    (hC : deviceCoherence Ψ₀ ≠ 0) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L where
  evolve := weightEvolve J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀))
  evolve_self := weightEvolve_self J μ₀ μ₁ g _
  evolve_comp := weightEvolve_comp J μ₀ μ₁ g (continuous_rateWeight J μ₀ μ₁ _)
  measurable_evolve := measurable_weightEvolve J μ₀ μ₁ g (continuous_rateWeight J μ₀ μ₁ _)
  readout := tickRead (g * (2 * n * ‖deviceCoherence Ψ₀‖))
  measurable_readout := measurable_tickRead _
  ready := {x | x.2 = 0}
  measurableSet_ready := measurableSet_eq_fun measurable_snd measurable_const
  prep := (Ψ₀, 0)
  prep_mem := rfl
  site := Finset.univ
  start := 0
  value := 1
  writeStart := 2 * Real.pi * n / R
  writeEnd := 2 * Real.pi * n / R
  window := w
  isWrite :=
    have hκ : 0 < R * ‖deviceCoherence Ψ₀‖ := mul_pos hR (norm_pos_iff.2 hC)
    have hreg : ∀ t, (weightFlow J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀)) (t - 0) (Ψ₀, 0)).2
        = g * ∫ s in (0 : ℝ)..t, max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0 := fun t => by
      rw [sub_zero, register_weightFlow, zero_add]
      congr 1
      exact intervalIntegral.integral_congr fun s _ => rateWeight_tickMark hC (hrot s)
    have hI : (∫ s in (0 : ℝ)..2 * Real.pi * n / R,
        max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0) = 2 * n * ‖deviceCoherence Ψ₀‖ := by
      rw [integral_max_cos hκ.le hR n]
      field_simp
    { start_le := by positivity
      interval := le_rfl
      window_nonneg := hw
      before := fun t _ ht => by
        show tickRead _
          (weightFlow J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀)) (t - 0) (Ψ₀, 0)) ≠ 1
        rw [tickRead, hreg]
        have hlt := integral_max_cos_lt hκ hR n ht
        rw [hI] at hlt
        split_ifs with h
        · exact absurd h (not_le.2 (mul_lt_mul_of_pos_left hlt hg))
        · decide
      holds := fun t ht _ => by
        show tickRead _
          (weightFlow J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀)) (t - 0) (Ψ₀, 0)) = 1
        rw [tickRead, hreg]
        have hle := integral_max_cos_mono (R := R) hκ.le ht
        rw [hI] at hle
        split_ifs with h
        · rfl
        · exact absurd (mul_le_mul_of_nonneg_left hle hg.le) h }

/-- ★★★ **A tick of a drifting device, counted by the rate**: for a device whose splitting
coherence drifts from `R e^{−iRs} C₀` by at most `(1 + R|s|) ε`, tick `n` (threshold `2gn|C₀|`, no
rate in it) is written inside `[2πn/R − δ, 2πn/R + δ]` whenever `δ ≤ 1/R` and
`ε ((2πn/R + δ)² + 2(2πn/R + δ)/R) < |C₀| δ`. -/
noncomputable def rateDriftDetector (J μ₀ μ₁ g R ε : ℝ) (hg : 0 < g) (hR : 0 < R)
    (Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε)
    (hC : deviceCoherence Ψ₀ ≠ 0) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδR : δ ≤ 1 / R)
    (hm : ε * ((2 * Real.pi * n / R + δ) ^ 2 + 2 * (2 * Real.pi * n / R + δ) / R)
      < ‖deviceCoherence Ψ₀‖ * δ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L where
  evolve := weightEvolve J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀))
  evolve_self := weightEvolve_self J μ₀ μ₁ g _
  evolve_comp := weightEvolve_comp J μ₀ μ₁ g (continuous_rateWeight J μ₀ μ₁ _)
  measurable_evolve := measurable_weightEvolve J μ₀ μ₁ g (continuous_rateWeight J μ₀ μ₁ _)
  readout := tickRead (g * (2 * n * ‖deviceCoherence Ψ₀‖))
  measurable_readout := measurable_tickRead _
  ready := {x | x.2 = 0}
  measurableSet_ready := measurableSet_eq_fun measurable_snd measurable_const
  prep := (Ψ₀, 0)
  prep_mem := rfl
  site := Finset.univ
  start := 0
  value := 1
  writeStart := max 0 (2 * Real.pi * n / R - δ)
  writeEnd := 2 * Real.pi * n / R + δ
  window := w
  isWrite :=
    have hε : 0 ≤ ε := by
      have h0 := hdrift 0
      rw [abs_zero, mul_zero, add_zero, one_mul] at h0
      exact (norm_nonneg _).trans h0
    have hκ : 0 ≤ R * ‖deviceCoherence Ψ₀‖ := mul_nonneg hR.le (norm_nonneg _)
    have htn : 0 ≤ 2 * Real.pi * n / R := by positivity
    have hRinv : 0 < 1 / R := by positivity
    have hreg : ∀ t, (weightFlow J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀)) (t - 0) (Ψ₀, 0)).2
        = g * ∫ s in (0 : ℝ)..t,
          rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀) :=
      fun t => by rw [sub_zero, register_weightFlow, zero_add]
    have hI : (∫ s in (0 : ℝ)..2 * Real.pi * n / R,
        max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0) = 2 * n * ‖deviceCoherence Ψ₀‖ := by
      rw [integral_max_cos hκ hR n]
      field_simp
    have hcI : ∀ a b : ℝ, IntervalIntegrable
        (fun s => max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0) volume a b :=
      fun a b => (by fun_prop : Continuous fun s =>
        max (R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0).intervalIntegrable a b
    have hE : ε * ((2 * Real.pi * n / R + δ) + R * (2 * Real.pi * n / R + δ) ^ 2 / 2)
        < R * ‖deviceCoherence Ψ₀‖ / 2 * δ := by
      have h1 := mul_lt_mul_of_pos_right hm (show 0 < R / 2 by positivity)
      have e : ε * ((2 * Real.pi * n / R + δ) ^ 2 + 2 * (2 * Real.pi * n / R + δ) / R) * (R / 2)
          = ε * ((2 * Real.pi * n / R + δ) + R * (2 * Real.pi * n / R + δ) ^ 2 / 2) := by
        field_simp
        ring
      rw [e] at h1
      linarith
    { start_le := le_max_left _ _
      interval := max_le (by positivity) (by linarith)
      window_nonneg := hw
      before := fun t ht0 ht => by
        show tickRead _
          (weightFlow J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀)) (t - 0) (Ψ₀, 0)) ≠ 1
        rw [tickRead, hreg]
        set tn := 2 * Real.pi * n / R
        have htl : t < tn - δ := by
          rcases lt_max_iff.1 ht with h | h
          · linarith
          · exact h
        have hb := (abs_le.1 (abs_integral_rateWeight_sub_le J μ₀ μ₁ hC hdrift ht0)).2
        have hmono := integral_max_cos_mono (R := R) hκ htl.le
        have hnear := le_integral_max_cos_near hκ hR n (a := tn - δ) (b := tn) (by linarith)
          (by linarith) (by linarith)
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcI 0 (tn - δ))
          (hcI (tn - δ) tn)
        have hEt : ε * (t + R * t ^ 2 / 2) ≤ ε * ((tn + δ) + R * (tn + δ) ^ 2 / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hε
          have h2 : t ^ 2 ≤ (tn + δ) ^ 2 := pow_le_pow_left₀ ht0 (by linarith) 2
          have h3 : R * t ^ 2 ≤ R * (tn + δ) ^ 2 := mul_le_mul_of_nonneg_left h2 hR.le
          linarith
        have hlt : (∫ s in (0 : ℝ)..t,
            rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀))
            < 2 * n * ‖deviceCoherence Ψ₀‖ := by
          rw [← hI]
          linarith
        split_ifs with h
        · exact absurd h (not_le.2 (mul_lt_mul_of_pos_left hlt hg))
        · decide
      holds := fun t ht _ => by
        show tickRead _
          (weightFlow J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark Ψ₀)) (t - 0) (Ψ₀, 0)) = 1
        rw [tickRead, hreg]
        set tn := 2 * Real.pi * n / R
        have hmono := integral_rateWeight_mono J μ₀ μ₁ (Ψ₀ := Ψ₀) ht
        have hb := (abs_le.1 (abs_integral_rateWeight_sub_le J μ₀ μ₁ hC hdrift
          (t := tn + δ) (by linarith))).1
        have hnear := le_integral_max_cos_near hκ hR n (a := tn) (b := tn + δ) (by linarith)
          (by linarith) (by linarith)
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcI 0 tn)
          (hcI tn (tn + δ))
        have hle : 2 * n * ‖deviceCoherence Ψ₀‖
            ≤ ∫ s in (0 : ℝ)..t,
              rateWeight J μ₀ μ₁ (tickMark Ψ₀) (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀) := by
          rw [← hI]
          linarith
        split_ifs with h
        · rfl
        · exact absurd (mul_le_mul_of_nonneg_left hle hg.le) h }

/-! ### The ticks of a device, counted by the rate -/

/-- ★★★ **The ticks of a device in one mode, counted by the rate**: tick `n` of the device at
momentum `m`, written at exactly `2πn/R`, its threshold `2gn|C₀|` free of `R`. -/
noncomputable def singleRateTick (J μ₀ μ₁ g : ℝ) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) (β : ℤ → ℂ) (hβ : β m ≠ 0) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  rateTickDetector J μ₀ μ₁ g (levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))) hg
    (levelClockRate_pos h0 h01 _) (devicePacket J μ₀ μ₁ {m} β 0)
    (splitCoherence_single J μ₀ μ₁ m β) (deviceCoherence_single_ne_zero h0 h01.le h10 m hβ) n hw

section Device

variable {c μ₀ μ₁ ℓ P D p₀ : ℝ} {W : Finset ℤ} {lo : ℤ}

/-- ★★★ **Tick `n` of #262's device, counted by the rate**: written within `δ` of `2πn/R`, its
threshold `2gn|C₀|` free of `R`. -/
noncomputable def deviceRateTick {g : ℝ} (hc : 0 < c) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδR : δ ≤ 1 / levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)))
    (hm : deviceDrift c μ₀ μ₁ D p₀
        * ((2 * Real.pi * n
            / levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) + δ) ^ 2
          + 2 * (2 * Real.pi * n
            / levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) + δ)
            / levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)))
      < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 * δ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  have hf := deviceTick_facts (L := L) hc h0 h01 h10 hℓ hp₀ hD0 hWin hWD β hβ
  rateDriftDetector (scaledHop c (ℓ / L)) μ₀ μ₁ g _ (deviceDrift c μ₀ μ₁ D p₀) hg
    (levelClockRate_pos h0 h01 _) (devicePacket (scaledHop c (ℓ / L)) μ₀ μ₁ W β 0)
    (splitCoherence_shift_sharp hc h0 h01 hℓ (noWrap_distinct_of_window hWin).2 hWD β hβ 0)
    (norm_pos_iff.1 (hf.1.trans_le hf.2.1)) n hδ hδR
    (hm.trans_le (mul_le_mul_of_nonneg_right hf.2.1 hδ.le)) hw

/-- ★★★ **The ticks of #262's device, counted by the rate** (BACKLOG #273). The device with a
position (a window of modes within `D` of `p₀`, normalised, `μ₀ < μ₁ < 2μ₀`, on a ring of length
`ℓ`), read by the rate counter:

* **the counter reads the rate of the reading**: `dC/dt = −i S`, `S` the splitting coherence the
  counter integrates;
* **the rate turns with the reading**: `S(t)` is within `(1 + R|t|)` times the sharp drift of
  `R e^{−iRt} C₀`;
* **every tick is an occurrence of one evolution**, which carries the device;
* **tick `n`'s threshold is `2gn|C₀|`**: it holds no rate, so the counter needs no calibration of
  the device's rate, at rest or in motion;
* **tick `n` is written inside `[2πn/R − δ, 2πn/R + δ]`** for every `δ ≤ 1/R` with
  `deviceDrift · ((2πn/R + δ)² + 2(2πn/R + δ)/R) < κ₀ δ`, `κ₀ = (1 − ((μ₁ − μ₀)/μ₀)²)/2 > 0`. -/
theorem dirac_rate_ticks {g : ℝ} (hc : 0 < c) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {w : ℝ} (hw : 0 ≤ w) :
    let J := scaledHop c (ℓ / L)
    let Ψ := devicePacket (L := L) J μ₀ μ₁ W β
    let R := levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))
    0 < R ∧ 0 < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2
    ∧ (∀ t, HasDerivAt (fun s => deviceCoherence (Ψ s)) (-I * splitCoherence J μ₀ μ₁ (Ψ t)) t)
    ∧ (∀ t, ‖splitCoherence J μ₀ μ₁ (Ψ t)
        - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * t)) * deviceCoherence (Ψ 0))‖
        ≤ (1 + R * |t|) * deviceDrift c μ₀ μ₁ D p₀)
    ∧ ∀ (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδR : δ ≤ 1 / R)
      (hm : deviceDrift c μ₀ μ₁ D p₀ * ((2 * Real.pi * n / R + δ) ^ 2 + 2 * (2 * Real.pi * n / R + δ) / R)
        < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 * δ),
      let o := deviceRateTick (g := g) hc hg h0 h01 h10 hℓ hp₀ hD0 hWin hWD β hβ n hδ hδR hm hw
      o.evolve = weightEvolve J μ₀ μ₁ g (rateWeight J μ₀ μ₁ (tickMark (Ψ 0)))
      ∧ o.prep = (Ψ 0, 0) ∧ (∀ t, (o.evolve 0 t o.prep).1 = Ψ t)
      ∧ o.readout = tickRead (g * (2 * n * ‖deviceCoherence (Ψ 0)‖))
      ∧ o.writeStart = max 0 (2 * Real.pi * n / R - δ) ∧ o.writeEnd = 2 * Real.pi * n / R + δ := by
  intro J Ψ R
  refine ⟨levelClockRate_pos h0 h01 _,
    (deviceTick_facts (L := L) hc h0 h01 h10 hℓ hp₀ hD0 hWin hWD β hβ).1,
    fun t => hasDerivAt_deviceCoherence J μ₀ μ₁ W β t, fun t => ?_,
    fun n δ hδ hδR hm => ⟨rfl, rfl, fun t => ?_, rfl, rfl, rfl⟩⟩
  · have h := splitCoherence_shift_sharp (L := L) hc h0 h01 hℓ (noWrap_distinct_of_window hWin).2
      hWD β hβ 0 t
    rwa [deviceProp_devicePacket_shift, zero_add] at h
  · show deviceProp J μ₀ μ₁ (t - 0) *ᵥ Ψ 0 = Ψ t
    rw [sub_zero, deviceProp_devicePacket]

end Device

end CSD.RecordLayer
