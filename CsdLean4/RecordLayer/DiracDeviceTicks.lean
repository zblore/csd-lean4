/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTicks

/-!
# The ticks of a device with a position

**Category:** 7-SigmaLayer (the record layer). BACKLOG #272 (residue of ~~#271~~).

~~#271~~'s ticks needed a coherence that turns **exactly**, which only a device in one mode has, and
such a device has no position. #262's device — a window of modes within `D` of `p₀` — turns only
within an error growing linearly in time. Here the tick detector absorbs that drift: tick `n` is
still written, inside a window around `2πn/R`, for as long as the integrated drift stays below the
tick's margin. With the sharp drift of `dirac_device` (quadratic in `D` at rest), #269's signal is
timed by a device with a position, on a ring a hundred times shorter than the chain's.

## A drifting reading

* `half_le_max_cos` (within one radian of a mark the rectified reading is at least half its
  amplitude), ★ `le_integral_max_cos_near` (it gains `κ(b − a)/2` there);
* ★ `abs_tickWeight_sub_le` — **a drift `ε` in the coherence moves the tick weight by at most
  `ε`**; ★★ `abs_integral_tickWeight_sub_le` — **a drift `|s| ε` moves the register by at most
  `ε t²/2`**; `integral_tickWeight_mono`;
* ★★★ `driftTickDetector` — **tick `n` written inside `[2πn/R − δ, 2πn/R + δ]`** whenever `δ ≤ 1/R`
  and `ε (2πn/R + δ)² < |C₀| δ`.

## The ticks of #262's device

* `deviceDrift` (`c D (2c|p₀| + c D)(μ₁ − μ₀)/(4μ₀²)`, from `dirac_device`'s sharp conjunct),
  `deviceTick_facts`, `deviceTick`;
* ★★★ `dirac_device_ticks` — **the device's position is bounded as in `dirac_device`; every tick is
  an occurrence of one evolution, which carries the device; tick `n` is written inside
  `[2πn/R − δ, 2πn/R + δ]` whenever `δ ≤ 1/R` and `deviceDrift · (2πn/R + δ)² < κ₀ δ`**,
  `κ₀ = (1 − ((μ₁ − μ₀)/μ₀)²)/2`.

## The signal timed by a device with a position

* `pairAmp`, `pair_norm`, `pair_win`, `pair_spread` (two modes, spread `10⁻⁷`, on a ring of length
  `2π·10⁷`), `located_rate` (`R = 10⁻⁶` at rest), ★ `located_margin` (the margin holds through tick
  `641`), `locatedTick`, `locatedStart`, `locatedArrival`, `locatedTimedTick`;
* ★★★ `dirac_located_signal` — **the departure record, the arrival record and ticks `0` to `641` of
  #262's device at rest are occurrences of one evolution, which carries the device; tick `n` is
  written inside `[nT − 1, nT + 1]`; the departure lies between ticks `12` and `14`, the arrival
  between `562` and `641`; and the speed in ticks lies in `[450/629, 125/137] ∋ 4/5`, below `c`.**

## The findings

1. **A device with a position keeps time as records**, to within `δ` of each mark, up to the tick
   where `ε (2πn/R)²` reaches `κ₀ δ`: the integrated drift grows quadratically in time, so the horizon
   is finite.
2. **The sharp drift is what makes the device small.** With `dirac_device`'s first bound `c D`,
   ticks to `±10⁶` through tick `641` would need `D < 2·10⁻¹⁴`, a device spread over more than
   `10¹⁴`, larger than the chain; at rest the splitting is stationary in the momentum, the drift is
   `c²D²(μ₁ − μ₀)/(4μ₀²)`, and `D = 10⁻⁷` gives ticks to `±1` on a ring of `2π·10⁷`.

## Honest scope

⚠️ **The device's position is a translation phase of two modes**: it is spread over its own ring,
a hundred times shorter than the chain's, not at the start arc. It sits beside the chain,
uncoupled, and is compared with the records by the one evolution they share; a single local
observer needs the signal back (#270), and moving observers are #253.

⚠️ **The horizon is finite**: tick `n` exists for `n ≤ 641` in the instance, and in general while the
margin holds — the drift bound is linear in time.

⚠️ **The detector is calibrated** as in ~~#271~~ (#273).

References: `specs/BACKLOG.md` #272, #271, #262, #269, #273, #270, #253, #39;
`RecordLayer/DiracTicks.lean` (`tickDetector`, `tickWeight`, `re_star_tickMark_mul`,
`integral_max_cos`, `ActualOccurrence.liftFst`); `CV/DiracDevice.lean` (`dirac_device`,
`levelCoherence_rate_sharp`, `abs_levelClockRate_sub_le`); `RecordLayer/DiracSignal.lean`
(`startDetector`, `separation_arcs`); `RecordLayer/DiracTiming.lean` (`sharpDetector`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### The rectified reading near a mark -/

/-- **Near a mark the rectified reading is at least half its amplitude**: within one radian of the
`n`-th turn, `max(κ cos(Rs), 0) ≥ κ/2`. -/
theorem half_le_max_cos {κ R s : ℝ} (hκ : 0 ≤ κ) (n : ℕ)
    (hs : |R * s - n * (2 * Real.pi)| ≤ 1) : κ / 2 ≤ max (κ * Real.cos (R * s)) 0 := by
  have hcos : 1 / 2 ≤ Real.cos (R * s) := by
    rw [← Real.cos_sub_nat_mul_two_pi (R * s) n]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := R * s - n * (2 * Real.pi))
    have h2 : (R * s - n * (2 * Real.pi)) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (R * s - n * (2 * Real.pi))]
    linarith
  exact le_max_of_le_left (by nlinarith)

/-- ★ **The rectified reading gains at least `κ(b − a)/2`** on any interval within `1/R` of the
`n`-th mark. -/
theorem le_integral_max_cos_near {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) (n : ℕ) {a b : ℝ}
    (hab : a ≤ b) (ha : 2 * Real.pi * n / R - 1 / R ≤ a) (hb : b ≤ 2 * Real.pi * n / R + 1 / R) :
    κ / 2 * (b - a) ≤ ∫ s in a..b, max (κ * Real.cos (R * s)) 0 := by
  have hc : Continuous fun s => max (κ * Real.cos (R * s)) 0 := by fun_prop
  have e1 : R * (2 * Real.pi * n / R - 1 / R) = n * (2 * Real.pi) - 1 := by
    field_simp
  have e2 : R * (2 * Real.pi * n / R + 1 / R) = n * (2 * Real.pi) + 1 := by
    field_simp
  have h := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (μ := volume))
    (hc.intervalIntegrable a b) fun s hs => half_le_max_cos (R := R) (s := s) hκ n
      (abs_le.2 ⟨by linarith [mul_le_mul_of_nonneg_left (ha.trans hs.1) hR.le],
        by linarith [mul_le_mul_of_nonneg_left (hs.2.trans hb) hR.le]⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-! ### A reading that drifts -/

/-- ★ **A drifting reading moves the tick weight by at most its drift**: if the coherence is within
`ε` of the exact turn, the tick weight is within `ε` of `max(|C₀| cos(Rs), 0)`. -/
theorem abs_tickWeight_sub_le {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) {R s ε : ℝ}
    (h : ‖deviceCoherence Ψ - exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀‖ ≤ ε) :
    |tickWeight (tickMark Ψ₀) Ψ - max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0| ≤ ε := by
  rw [tickWeight_eq, ← re_star_tickMark_mul hC R s]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star, norm_tickMark hC, one_mul]
  exact h

section Drift

variable (J μ₀ μ₁ : ℝ) {R ε : ℝ} {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ}

/-- ★★ **The register of a drifting reading**: if the coherence drifts by at most `|s| ε` from the
exact turn, the integrated tick weight is within `ε t²/2` of the exact one. -/
theorem abs_integral_tickWeight_sub_le (hC : deviceCoherence Ψ₀ ≠ 0)
    (hdrift : ∀ s, ‖deviceCoherence (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀‖ ≤ |s| * ε) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, tickWeight (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      - ∫ s in (0 : ℝ)..t, max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0| ≤ ε * t ^ 2 / 2 := by
  have hG := (continuous_tickWeight_deviceProp J μ₀ μ₁ (tickMark Ψ₀) Ψ₀).intervalIntegrable
    (μ := volume) 0 t
  have hF : IntervalIntegrable (fun s => max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0)
      volume 0 t :=
    (by fun_prop : Continuous fun s => max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0).intervalIntegrable 0 t
  rw [← intervalIntegral.integral_sub hG hF, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun s => ε * s) ht
    (Filter.Eventually.of_forall fun s hs => ?_)
    ((continuous_const.mul continuous_id : Continuous fun s : ℝ => ε * s).intervalIntegrable
      (μ := volume) 0 t)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    have h := abs_tickWeight_sub_le hC (hdrift s)
    rw [abs_of_pos hs.1] at h
    exact h.trans_eq (mul_comm s ε)
  · rw [intervalIntegral.integral_const_mul, integral_id]
    ring

theorem integral_tickWeight_mono {t₁ t : ℝ} (h : t₁ ≤ t) :
    (∫ s in (0 : ℝ)..t₁, tickWeight (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      ≤ ∫ s in (0 : ℝ)..t, tickWeight (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun s => tickWeight (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)) volume a b :=
    fun a b => (continuous_tickWeight_deviceProp J μ₀ μ₁ (tickMark Ψ₀) Ψ₀).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun s _ =>
    tickWeight_nonneg (tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
  linarith

end Drift

/-- ★★★ **A tick of a drifting device as an actual occurrence**: for a device whose coherence drifts
from the exact turn at rate `R` by at most `|s| ε`, tick `n` (threshold `2gn|C₀|/R`) is written
inside `[2πn/R − δ, 2πn/R + δ]` whenever `δ ≤ 1/R` and `ε (2πn/R + δ)² < |C₀| δ`. -/
noncomputable def driftTickDetector (J μ₀ μ₁ g R ε : ℝ) (hg : 0 < g) (hR : 0 < R)
    (Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (hdrift : ∀ s, ‖deviceCoherence (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀‖ ≤ |s| * ε)
    (hC : deviceCoherence Ψ₀ ≠ 0) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδR : δ ≤ 1 / R)
    (hm : ε * (2 * Real.pi * n / R + δ) ^ 2 < ‖deviceCoherence Ψ₀‖ * δ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L where
  evolve := tickEvolve J μ₀ μ₁ g (tickMark Ψ₀)
  evolve_self := tickEvolve_self J μ₀ μ₁ g _
  evolve_comp := tickEvolve_comp J μ₀ μ₁ g _
  measurable_evolve := measurable_tickEvolve J μ₀ μ₁ g _
  readout := tickRead (g * (2 * n * ‖deviceCoherence Ψ₀‖ / R))
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
      have h1 := hdrift 1
      rw [abs_one, one_mul] at h1
      exact (norm_nonneg _).trans h1
    have hκ := norm_nonneg (deviceCoherence Ψ₀)
    have htn : 0 ≤ 2 * Real.pi * n / R := by positivity
    have hRinv : 0 < 1 / R := by positivity
    have hreg : ∀ t, (tickFlow J μ₀ μ₁ g (tickMark Ψ₀) (t - 0) (Ψ₀, 0)).2
        = g * ∫ s in (0 : ℝ)..t, tickWeight (tickMark Ψ₀) (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀) :=
      fun t => by rw [sub_zero, register_tickFlow, zero_add]
    have hI := integral_max_cos hκ hR n
    have hcI : ∀ a b : ℝ, IntervalIntegrable
        (fun s => max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0) volume a b :=
      fun a b => (by fun_prop : Continuous fun s => max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0).intervalIntegrable a b
    { start_le := le_max_left _ _
      interval := max_le (by positivity) (by linarith)
      window_nonneg := hw
      before := fun t ht0 ht => by
        show tickRead _ (tickFlow J μ₀ μ₁ g (tickMark Ψ₀) (t - 0) (Ψ₀, 0)) ≠ 1
        rw [tickRead, hreg]
        set tn := 2 * Real.pi * n / R
        have htl : t < tn - δ := by
          rcases lt_max_iff.1 ht with h | h
          · linarith
          · exact h
        have hb := (abs_le.1 (abs_integral_tickWeight_sub_le J μ₀ μ₁ hC hdrift ht0)).2
        have hmono := integral_max_cos_mono (R := R) hκ htl.le
        have hnear := le_integral_max_cos_near hκ hR n (a := tn - δ) (b := tn) (by linarith)
          (by linarith) (by linarith)
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcI 0 (tn - δ))
          (hcI (tn - δ) tn)
        have ht2 : ε * t ^ 2 ≤ ε * (tn + δ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 (by linarith) 2) hε
        have hlt : (∫ s in (0 : ℝ)..t, tickWeight (tickMark Ψ₀) (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀))
            < 2 * n * ‖deviceCoherence Ψ₀‖ / R := by
          rw [← hI]
          linarith
        split_ifs with h
        · exact absurd h (not_le.2 (mul_lt_mul_of_pos_left hlt hg))
        · decide
      holds := fun t ht _ => by
        show tickRead _ (tickFlow J μ₀ μ₁ g (tickMark Ψ₀) (t - 0) (Ψ₀, 0)) = 1
        rw [tickRead, hreg]
        set tn := 2 * Real.pi * n / R
        have hmono := integral_tickWeight_mono J μ₀ μ₁ (Ψ₀ := Ψ₀) ht
        have hb := (abs_le.1 (abs_integral_tickWeight_sub_le J μ₀ μ₁ hC hdrift
          (t := tn + δ) (by linarith))).1
        have hnear := le_integral_max_cos_near hκ hR n (a := tn) (b := tn + δ) (by linarith)
          (by linarith) (by linarith)
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcI 0 tn)
          (hcI tn (tn + δ))
        have hle : 2 * n * ‖deviceCoherence Ψ₀‖ / R
            ≤ ∫ s in (0 : ℝ)..t, tickWeight (tickMark Ψ₀) (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀) := by
          rw [← hI]
          linarith
        split_ifs with h
        · rfl
        · exact absurd (mul_le_mul_of_nonneg_left hle hg.le) h }

/-! ### The ticks of #262's device -/

/-- **The sharp coherence drift of #262's device**: `c D (2c|p₀| + c D)(μ₁ − μ₀)/(4μ₀²)` per unit
time. -/
noncomputable def deviceDrift (c μ₀ μ₁ D p₀ : ℝ) : ℝ :=
  c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (4 * μ₀ ^ 2)

section Device

variable {c μ₀ μ₁ ℓ P D p₀ : ℝ} {W : Finset ℤ} {lo : ℤ}

/-- **What a tick of #262's device needs**: its starting coherence is at least `κ₀ > 0`, and its
coherence drifts from the exact turn by at most `|s|` times `deviceDrift`. -/
theorem deviceTick_facts (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀)
    (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) :
    0 < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2
    ∧ (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2
      ≤ ‖deviceCoherence (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β 0)‖
    ∧ ∀ s, ‖deviceCoherence (deviceProp (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ s
          *ᵥ devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β 0)
        - exp (I * (((-levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) : ℝ)
            : ℂ) * s))
          * deviceCoherence (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β 0)‖
        ≤ |s| * deviceDrift c μ₀ μ₁ D p₀ := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -⟩ :=
    dirac_device (L := L) hc h0 h01.le hℓ hp₀ hD0 hWin hWD β hβ
  refine ⟨?_, h7, fun s => ?_⟩
  · have h1 : (μ₁ - μ₀) / μ₀ < 1 := (div_lt_one h0).2 (by linarith)
    have h2 : 0 ≤ (μ₁ - μ₀) / μ₀ := div_nonneg (by linarith) h0.le
    nlinarith
  · rw [deviceProp_devicePacket]
    exact h6 s

/-- ★★★ **Tick `n` of #262's device**, an actual occurrence written within `δ` of `2πn/R`. -/
noncomputable def deviceTick {g : ℝ} (hc : 0 < c) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδR : δ ≤ 1 / levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)))
    (hm : deviceDrift c μ₀ μ₁ D p₀
        * (2 * Real.pi * n / levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀))
          + δ) ^ 2
      < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 * δ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  have hf := deviceTick_facts (L := L) hc h0 h01 h10 hℓ hp₀ hD0 hWin hWD β hβ
  driftTickDetector (scaledHop c (ℓ / L)) μ₀ μ₁ g _ (deviceDrift c μ₀ μ₁ D p₀) hg
    (levelClockRate_pos h0 h01 _) (devicePacket (scaledHop c (ℓ / L)) μ₀ μ₁ W β 0) hf.2.2
    (norm_pos_iff.1 (hf.1.trans_le hf.2.1)) n hδ hδR
    (hm.trans_le (mul_le_mul_of_nonneg_right hf.2.1 hδ.le)) hw

/-- ★★★ **The ticks of #262's device** (BACKLOG #272). The device with a position — a window of
modes within `D` of `p₀`, normalised, `μ₀ < μ₁ < 2μ₀`, on a ring of fixed length `ℓ` — read by the
tick detector:

* **its position**: its translation phase turns at `k v₀` within `|t|` times the levels' errors and
  their velocity gap (`dirac_device`);
* **every tick is an occurrence of one evolution**, `e^{−itH_dev}` with the register, which carries
  the device;
* **tick `n` is written inside `[2πn/R − δ, 2πn/R + δ]`** for every `δ ≤ 1/R` with
  `deviceDrift · (2πn/R + δ)² < κ₀ δ`, `κ₀ = (1 − ((μ₁ − μ₀)/μ₀)²)/2 > 0`. -/
theorem dirac_device_ticks {g : ℝ} (hc : 0 < c) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {w : ℝ} (hw : 0 ≤ w) :
    let J := scaledHop c (ℓ / L)
    let Ψ := devicePacket (L := L) J μ₀ μ₁ W β
    let R := levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))
    0 < R ∧ 0 < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2
    ∧ (∀ t, ‖deviceTrans (Ψ t)
        - exp (I * (((2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) : ℝ) : ℂ) * t)) * deviceTrans (Ψ 0)‖
        ≤ |t| * ((limitErr c μ₀ ℓ D P (ℓ / L) + limitErr c μ₁ ℓ D P (ℓ / L)) / 2
          + 2 * Real.pi / ℓ * |vRel c μ₁ (c * p₀) - vRel c μ₀ (c * p₀)| / 2))
    ∧ ∀ (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδR : δ ≤ 1 / R)
      (hm : deviceDrift c μ₀ μ₁ D p₀ * (2 * Real.pi * n / R + δ) ^ 2
        < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 * δ),
      let o := deviceTick (g := g) hc hg h0 h01 h10 hℓ hp₀ hD0 hWin hWD β hβ n hδ hδR hm hw
      o.evolve = tickEvolve J μ₀ μ₁ g (tickMark (Ψ 0)) ∧ o.prep = (Ψ 0, 0)
      ∧ (∀ t, (o.evolve 0 t o.prep).1 = Ψ t)
      ∧ o.writeStart = max 0 (2 * Real.pi * n / R - δ) ∧ o.writeEnd = 2 * Real.pi * n / R + δ := by
  intro J Ψ R
  obtain ⟨-, -, h3, -⟩ := dirac_device (L := L) hc h0 h01.le hℓ hp₀ hD0 hWin hWD β hβ
  refine ⟨levelClockRate_pos h0 h01 _,
    (deviceTick_facts (L := L) hc h0 h01 h10 hℓ hp₀ hD0 hWin hWD β hβ).1, h3,
    fun n δ hδ hδR hm => ⟨rfl, rfl, fun t => ?_, rfl, rfl⟩⟩
  show deviceProp J μ₀ μ₁ (t - 0) *ᵥ Ψ 0 = Ψ t
  rw [sub_zero, deviceProp_devicePacket]

end Device

/-! ### The signal timed by a device with a position -/

section Located

variable {N : ℕ} [NeZero N]

/-- **The located clock's amplitudes**: two neighbouring modes, equal weight. -/
noncomputable def pairAmp : ℤ → ℂ := fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem pair_norm : ∑ m ∈ ({0, 1} : Finset ℤ), ‖pairAmp m‖ ^ 2 = 1 := by
  rw [Finset.sum_pair (by norm_num)]
  simp only [pairAmp, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 two_pos), inv_pow, Real.sq_sqrt two_pos.le]
  norm_num

omit [NeZero N] in
theorem pair_win (hN : 3 ≤ N) : ∀ m ∈ ({0, 1} : Finset ℤ), (0 : ℤ) ≤ m ∧ m + 1 < 0 + N := by
  have h3 : (3 : ℤ) ≤ N := by exact_mod_cast hN
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl <;> omega

theorem pair_spread : ∀ m ∈ ({0, 1} : Finset ℤ),
    |2 * Real.pi * m / (2 * Real.pi * 10 ^ 7) - 0| ≤ 1 / 10 ^ 7 := by
  have hπ := Real.pi_pos
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · norm_num
  · rw [show 2 * Real.pi * ((1 : ℤ) : ℝ) / (2 * Real.pi * 10 ^ 7) - 0 = 1 / 10 ^ 7 by
      push_cast
      field_simp
      norm_num]
    rw [abs_of_pos (by norm_num)]

omit [NeZero N] in
/-- The located clock at rest turns at the rest splitting `10⁻⁶`. -/
theorem located_rate :
    levelClockRate 1 (1 + 1 / 10 ^ 6)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 7 / N) * Real.sin (2 * Real.pi * 10 ^ 7 / N * 0))
      = 1 / 10 ^ 6 := by
  rw [mul_zero, Real.sin_zero, mul_zero, levelClockRate, dispE, dispE,
    show ((1 : ℝ) + 1 / 10 ^ 6) ^ 2 + 0 ^ 2 = (1 + 1 / 10 ^ 6) ^ 2 by ring,
    Real.sqrt_sq (by norm_num), show (1 : ℝ) ^ 2 + 0 ^ 2 = 1 ^ 2 by ring,
    Real.sqrt_sq (by norm_num)]
  ring

/-- **The margin holds through tick `641`**: the drift `10⁻²⁰/4` over `(2πn·10⁶ + 1)²` stays below
`κ₀ = (1 − 10⁻¹²)/2`. -/
theorem located_margin (n : ℕ) (hn : n ≤ 641) :
    deviceDrift 1 1 (1 + 1 / 10 ^ 6) (1 / 10 ^ 7) 0 * (2 * Real.pi * n / (1 / 10 ^ 6) + 1) ^ 2
      < (1 - ((1 + 1 / 10 ^ 6 - 1) / 1) ^ 2) / 2 * 1 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  have hn' : (n : ℝ) ≤ 641 := by exact_mod_cast hn
  have hx0 : 0 ≤ 2 * Real.pi * n / (1 / 10 ^ 6) + 1 := by positivity
  have hx1 : 2 * Real.pi * n / (1 / 10 ^ 6) + 1 ≤ 5128000001 := by
    have e : 2 * Real.pi * n / (1 / 10 ^ 6) = 2 * Real.pi * n * 10 ^ 6 := by field_simp
    rw [e]
    nlinarith [mul_le_mul hπ4 hn' (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 4)]
  have hsq := pow_le_pow_left₀ hx0 hx1 2
  have hd : deviceDrift 1 1 (1 + 1 / 10 ^ 6) (1 / 10 ^ 7) 0 = 1 / (4 * 10 ^ 20) := by
    simp only [deviceDrift, abs_zero]
    norm_num
  rw [hd]
  calc 1 / (4 * 10 ^ 20) * (2 * Real.pi * n / (1 / 10 ^ 6) + 1) ^ 2
      ≤ 1 / (4 * 10 ^ 20) * 5128000001 ^ 2 := by gcongr
    _ < _ := by norm_num

/-- **Tick `n` of the located clock** (`n ≤ 641`): #262's device at rest with two modes, spread
`D = 10⁻⁷` on a ring of length `2π·10⁷`, rest energies `1` and `1 + 10⁻⁶`, gain `1`, written within
`1` of `n · 2π·10⁶`. -/
noncomputable def locatedTick (hN : 3 ≤ N) (n : ℕ) (hn : n ≤ 641) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena N) ℕ N :=
  deviceTick (L := N) (c := 1) (μ₀ := 1) (μ₁ := 1 + 1 / 10 ^ 6) (ℓ := 2 * Real.pi * 10 ^ 7)
    (P := 0) (D := 1 / 10 ^ 7) (p₀ := 0) (W := {0, 1}) (lo := 0) (g := 1) one_pos one_pos one_pos
    (by norm_num) (by norm_num) (by positivity) (by simp) (by positivity) (pair_win hN)
    pair_spread pairAmp pair_norm n (δ := 1) one_pos (by rw [located_rate]; norm_num)
    (by rw [located_rate]; exact located_margin n hn) hw

variable (hL : 10 ^ 13 ≤ L)

/-- **The departure record, with the located clock beside the chain.** -/
noncomputable def locatedStart (hN : 3 ≤ N) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (WholeArena L × TickArena N) ℕ L :=
  (startDetector hL hw).liftFst (locatedTick hN 0 (by norm_num) hw).evolve
    (locatedTick hN 0 (by norm_num) hw).evolve_self (locatedTick hN 0 (by norm_num) hw).evolve_comp
    (locatedTick hN 0 (by norm_num) hw).measurable_evolve (locatedTick hN 0 (by norm_num) hw).prep

/-- **The arrival record, with the located clock beside the chain.** -/
noncomputable def locatedArrival (hN : 3 ≤ N) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (WholeArena L × TickArena N) ℕ L :=
  (sharpDetector hL hw).liftFst (locatedTick hN 0 (by norm_num) hw).evolve
    (locatedTick hN 0 (by norm_num) hw).evolve_self (locatedTick hN 0 (by norm_num) hw).evolve_comp
    (locatedTick hN 0 (by norm_num) hw).measurable_evolve (locatedTick hN 0 (by norm_num) hw).prep

/-- **Tick `n` of the located clock, beside the chain.** -/
noncomputable def locatedTimedTick (hN : 3 ≤ N) (n : ℕ) (hn : n ≤ 641) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (WholeArena L × TickArena N) ℕ N :=
  (locatedTick hN n hn hw).liftSnd (startDetector hL hw).evolve (startDetector hL hw).evolve_self
    (startDetector hL hw).evolve_comp (startDetector hL hw).measurable_evolve
    (startDetector hL hw).prep

include hL in
/-- ★★★ **#269's signal timed by a clock with a position** (BACKLOG #272). The chain with its
start-arc and far-arc detectors, and beside it #262's device at rest — two modes, spread
`D = 10⁻⁷`, on a ring of length `2π·10⁷`, a hundred times shorter than the chain's — with its tick
detector (period `T = 2π·10⁶`):

* **one evolution**: the departure record, the arrival record and ticks `0` to `641` are actual
  occurrences of the same evolution from the same preparation, which carries the device;
* **the ticks**: tick `n` is written inside `[nT − 1, nT + 1]`;
* **the records between the ticks**: the departure between ticks `12` and `14`, the arrival between
  ticks `562` and `641`;
* **the speed in ticks** lies in `[450/629, 125/137] ∋ 4/5`, below `c` — as `dirac_timed_signal`,
  now with a device that has a position. -/
theorem dirac_located_signal (hN : 3 ≤ N) {w : ℝ} (hw : 0 ≤ w) :
    let T : ℝ := 2 * Real.pi * 10 ^ 6
    let dep := locatedStart (N := N) hL hN hw
    let arr := locatedArrival (N := N) hL hN hw
    let tick := fun (n : ℕ) (hn : n ≤ 641) => locatedTimedTick (N := N) hL hN n hn hw
    (∀ n hn, (tick n hn).evolve = dep.evolve ∧ (tick n hn).prep = dep.prep
      ∧ (tick n hn).evolve = arr.evolve ∧ (tick n hn).prep = arr.prep)
    ∧ (∀ n hn t, ((tick n hn).evolve 0 t (tick n hn).prep).2.1
        = devicePacket (L := N) (scaledHop 1 (2 * Real.pi * 10 ^ 7 / N)) 1 (1 + 1 / 10 ^ 6) {0, 1}
          pairAmp t)
    ∧ (∀ n hn, (tick n hn).writeStart = max 0 ((n : ℝ) * T - 1)
      ∧ (tick n hn).writeEnd = (n : ℝ) * T + 1)
    ∧ (tick 12 (by norm_num)).writeEnd ≤ dep.writeStart
    ∧ dep.writeEnd ≤ (tick 14 (by norm_num)).writeStart
    ∧ (tick 562 (by norm_num)).writeEnd ≤ arr.writeStart
    ∧ arr.writeEnd ≤ (tick 641 le_rfl).writeStart
    ∧ (∀ k ∈ nearArc L, ∀ j ∈ farArc L,
        9 * Real.pi / 10 ≤ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L|
          ∧ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L| ≤ 2 * Real.pi - 9 * Real.pi / 10)
    ∧ 9 * Real.pi * 10 ^ 9 / 10 = 450 * T ∧ Real.pi * 10 ^ 9 = 500 * T
    ∧ 450 * T / ((641 - 12) * T) = 450 / 629 ∧ 500 * T / ((562 - 14) * T) = 125 / 137
    ∧ (0 : ℝ) < 450 / 629 ∧ (450 / 629 : ℝ) ≤ 4 / 5 ∧ (4 / 5 : ℝ) ≤ 125 / 137
    ∧ (125 / 137 : ℝ) < 1 := by
  intro T dep arr tick
  have hπ := Real.pi_pos
  have hπ2 := Real.two_le_pi
  have hT : 0 < T := by positivity
  have htick : ∀ n hn, (tick n hn).writeStart = max 0 ((n : ℝ) * T - 1)
      ∧ (tick n hn).writeEnd = (n : ℝ) * T + 1 := fun n hn => by
    have e : 2 * Real.pi * (n : ℝ) / (1 / 10 ^ 6) = n * T := by
      simp only [T]
      field_simp
    refine ⟨?_, ?_⟩
    · show max 0 (2 * Real.pi * n / levelClockRate 1 (1 + 1 / 10 ^ 6)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 7 / N) * Real.sin (2 * Real.pi * 10 ^ 7 / N * 0))
          - 1) = _
      rw [located_rate, e]
    · show 2 * Real.pi * n / levelClockRate 1 (1 + 1 / 10 ^ 6)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 7 / N) * Real.sin (2 * Real.pi * 10 ^ 7 / N * 0))
          + 1 = _
      rw [located_rate, e]
  have hdep0 : dep.writeStart = Real.pi * 10 ^ 9 / 40 := rfl
  have hdep1 : dep.writeEnd = Real.pi * 10 ^ 9 / 36 := rfl
  have harr0 : arr.writeStart = 9 * Real.pi * 10 ^ 9 / 8 := rfl
  have harr1 : arr.writeEnd = 41 * Real.pi * 10 ^ 9 / 32 := rfl
  refine ⟨fun n hn => ⟨rfl, rfl, rfl, rfl⟩, fun n hn t => ?_, htick, ?_, ?_, ?_, ?_,
    fun k hk j hj => ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · show deviceProp _ _ _ (t - 0) *ᵥ devicePacket (L := N) (scaledHop 1 (2 * Real.pi * 10 ^ 7 / N))
      1 (1 + 1 / 10 ^ 6) {0, 1} pairAmp 0 = _
    rw [sub_zero, deviceProp_devicePacket]
  · rw [(htick 12 _).2, hdep0]
    simp only [T]
    push_cast
    nlinarith
  · rw [(htick 14 _).1, hdep1]
    refine le_max_of_le_right ?_
    simp only [T]
    push_cast
    nlinarith
  · rw [(htick 562 _).2, harr0]
    simp only [T]
    push_cast
    nlinarith
  · rw [(htick 641 _).1, harr1]
    refine le_max_of_le_right ?_
    simp only [T]
    push_cast
    nlinarith
  · obtain ⟨h1, h2⟩ := separation_arcs hL hk hj
    exact ⟨h1, by linarith⟩
  · simp only [T]
    ring
  · simp only [T]
    ring
  · field_simp
    norm_num
  · field_simp
    norm_num

end Located

end CSD.RecordLayer

end
