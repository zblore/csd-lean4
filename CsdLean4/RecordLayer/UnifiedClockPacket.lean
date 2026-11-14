/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedDiracClockTicks

/-!
# A clock packet at a reference momentum: a dephasing bound linear in the horizon

**Category:** 7-SigmaLayer (the record layer). BACKLOG #388 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (2) of the plan of
2026-11-14, the probe of the moving observer. No new assumption.

The author decided (2026-11-14) that the moving observer is a localised packet of the clock
carrier with a coincidence detector. This module is about that observer's clock only. #358
(`clock_tick_device`) has the tick law for a localised clock packet, but its localisation
error grows as the square of the horizon and no packet of positive width was shown to meet
its conditions. Here, on a fibre where the pointer's profile vanishes, the error bound is
linear in the horizon.

**How.** On such a fibre the pointer is turned by the uncoupled reading. For a packet on a
window of distinct modes that reading is a sum over the modes, each turning at its own rate,
so the accumulated reading is exactly the sum of the modes' hands
(`integral_clockFreeRead_packet`). Two hands of one coherence at rates `R₁, R₂ ≥ ρ > 0`
differ by at most `‖C‖ |R₁ − R₂| (2t/ρ + 3/ρ²)` (`abs_clockHand_sub_le`).

* `clockHand_sum`, ★ `abs_clockHand_sub_le`;
* `modeRate`, `modeCoh`, `bandE_sub_eq_neg_modeRate`, ★ `deviceCoherence_packet_shift`,
  `deviceCoherence_packet_eq_sum`, ★★ `integral_clockFreeRead_packet`;
* `packetSwingErr`, ★★ `abs_clockPointerShift_packet_sub_swing_le`,
  ★★★ `isSwing_clockPointerFlow_packet` — a clock packet is a swing up to a horizon, with an
  error linear in the horizon;
* `sum_norm_modeCoh_mul_le`, ★★★ `clock_packet_ticks` — for the localised packet of #262's
  device with the strength `g = R/(16 Im C₀)`: if
  `R ε (2T/ρ + 3/ρ² + π/(2R²)) < κ/3`, the pointer is a swing up to `T` and every tick count
  `N` at `T` has `|2π N/(μ₁ − μ₀) − √(1 − (v/c)²) T| ≤ 2π/(μ₁ − μ₀) + ((μ₁ − μ₀)/E₀) T`.

## Exact scope

* **A clock, not an observer.** The arena is the clock arena of #358: the clock carrier and
  its own pointer. There is no messenger, no detector, no meeting and no second observer.
  The coincidence detector of the author's decision is not built.
* **The conditions are hypotheses, explicit and linear in `T`.** They are `κ > 0`,
  `R ε (2T/ρ + 3/ρ² + π/(2R²)) < κ/3`, and a lower bound `ρ > 0` of the modes' rates and of
  the reference rate. A single mode on the lattice (`D = 0`, `μ₁ < 2μ₀`, `ρ = R`) has
  `ε = 0` and meets them at every horizon; that is a calculation, not in Lean, and is the
  case #358 already has. No packet of positive width is shown to meet them. That a lower
  bound `ρ` follows from the window (through `clockRate_mem`) is a calculation, not in Lean.
* **One fibre and one start.** The pointer's profile is `trainF` on the fibre `0`, where it
  vanishes and the pointer does not act back on the clock; the pointer starts at `1/12`; the
  packet is prepared a quarter turn early. A null set. Off that fibre the back-reaction term
  of #358, quadratic in the horizon, remains.
* **The velocity is a function of the momentum.** `v = vRel c μ₀ σ` is the relativistic
  velocity at the reference momentum and the lower level. That the packet moves at that
  velocity is not shown here, and no position of the clock is recorded.
* **The count is compared with the flow time** (UA-7). No record holds `T`.
* **The dilation error is the finite splitting**, `((μ₁ − μ₀)/E₀) T`, as in #358; it does not
  shrink with the packet's width.
* **Not shown: that a tick exists.** The conclusion bounds every tick count at `T`; it does
  not show that the count is positive. The horizon the condition allows is not shown to be
  longer than one period `2π/R`, and for a shorter one the count is zero and the bound is
  its own slack term.
* **Not shown: that the horizon is long enough for a radar exchange.** An estimate (a
  calculation, not in Lean): the horizon allowed is of order `1/ε`, within which the packet
  travels of order `E/(μ₁ − μ₀)` of its own widths.
* **Earlier.** #358 (`clock_tick_device`, the same statement with the localisation error
  `ε T²` and on every fibre); #273 (the sharp drift, on another arena); #249 (the dilation
  bound). What is new is the exact sum over modes and the linear bound.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UO-14, UO-16, UD-58 to UD-65, UD-137, UD-138);
`RecordLayer/UnifiedDiracClockTicks.lean` (#358: `clock_tick_device`,
`isSwing_of_abs_shift_sub_le`, `IsSwing.abs_clockOpTime_sub_dilated_le`, `clockSwingAmp`);
`RecordLayer/UnifiedDiracClock.lean` (#357: `clockPointerShift`, `clockHand`,
`integral_clockQuad`, `clockFreeRead_deviceRay`); `RecordLayer/DiracRateTicks.lean` (#273:
`levelWeight_mul_rate_le`, `deviceProp_devicePacket_shift`);
`RecordLayer/DiracDeviceTicks.lean` (`deviceDrift`); `CV/DiracDevice.lean`
(`levelCoherence_eq`, `device_observables`); `CV/DiracClockChain.lean` (#249:
`abs_clockRate_div_sub_le`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Two hands at nearby rates -/

/-- The hand is additive in the coherence. -/
theorem clockHand_sum {ι : Type*} (s : Finset ι) (R : ℝ) (c : ι → ℂ) (t : ℝ) :
    clockHand R (∑ m ∈ s, c m) t = ∑ m ∈ s, clockHand R (c m) t := by
  simp only [clockHand, Complex.re_sum, Complex.im_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.sum_div]

/-- ★ **Two hands of one coherence at nearby rates stay close, linearly in the flow time.**
For rates `R₁, R₂ ≥ ρ > 0` and `t ≥ 0`:
`|clockHand R₁ C t − clockHand R₂ C t| ≤ ‖C‖ |R₁ − R₂| (2t/ρ + 3/ρ²)`. -/
theorem abs_clockHand_sub_le {R₁ R₂ ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ R₁) (h2 : ρ ≤ R₂) (C : ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    |clockHand R₁ C t - clockHand R₂ C t| ≤ ‖C‖ * |R₁ - R₂| * (2 * t / ρ + 3 / ρ ^ 2) := by
  have hR1 : 0 < R₁ := hρ.trans_le h1
  have hR2 : 0 < R₂ := hρ.trans_le h2
  have hre := Complex.abs_re_le_norm C
  have him := Complex.abs_im_le_norm C
  have hC := norm_nonneg C
  set d := |R₁ - R₂| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hs : |Real.sin (R₁ * t) - Real.sin (R₂ * t)| ≤ t * d := by
    refine (Real.abs_sin_sub_sin_le _ _).trans_eq ?_
    rw [← sub_mul, abs_mul, abs_of_nonneg ht, mul_comm]
  have hc : |Real.cos (R₁ * t) - Real.cos (R₂ * t)| ≤ t * d := by
    refine (Real.abs_cos_sub_cos_le _ _).trans_eq ?_
    rw [← sub_mul, abs_mul, abs_of_nonneg ht, mul_comm]
  -- the numerators
  set N₁ := C.re * Real.sin (R₁ * t) + C.im * (1 - Real.cos (R₁ * t)) with hN₁
  set N₂ := C.re * Real.sin (R₂ * t) + C.im * (1 - Real.cos (R₂ * t)) with hN₂
  have hNd : |N₁ - N₂| ≤ 2 * ‖C‖ * (t * d) := by
    have e : N₁ - N₂ = C.re * (Real.sin (R₁ * t) - Real.sin (R₂ * t))
        - C.im * (Real.cos (R₁ * t) - Real.cos (R₂ * t)) := by
      rw [hN₁, hN₂]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    have a := mul_le_mul hre hs (abs_nonneg _) hC
    have b := mul_le_mul him hc (abs_nonneg _) hC
    linarith
  have hN2 : |N₂| ≤ 3 * ‖C‖ := by
    rw [hN₂]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have a := mul_le_mul hre (Real.abs_sin_le_one (R₂ * t)) (abs_nonneg _) hC
    have hcos : |1 - Real.cos (R₂ * t)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [Real.cos_le_one (R₂ * t), Real.neg_one_le_cos (R₂ * t)]
    have b := mul_le_mul him hcos (abs_nonneg _) hC
    linarith
  have e : clockHand R₁ C t - clockHand R₂ C t
      = (N₁ - N₂) / R₁ + N₂ * (R₂ - R₁) / (R₁ * R₂) := by
    simp only [clockHand, ← hN₁, ← hN₂]
    field_simp
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(N₁ - N₂) / R₁| ≤ 2 * ‖C‖ * (t * d) / ρ := by
    rw [abs_div, abs_of_pos hR1]
    exact (div_le_div_of_nonneg_right hNd hR1.le).trans
      (div_le_div_of_nonneg_left (by positivity) hρ h1)
  have t2 : |N₂ * (R₂ - R₁) / (R₁ * R₂)| ≤ 3 * ‖C‖ * d / ρ ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hR1 hR2), abs_sub_comm R₂ R₁, ← hd]
    have hnum : |N₂| * d ≤ 3 * ‖C‖ * d := mul_le_mul_of_nonneg_right hN2 hd0
    have hden : ρ ^ 2 ≤ R₁ * R₂ := by nlinarith
    exact (div_le_div_of_nonneg_right hnum (mul_pos hR1 hR2).le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  have e2 : ‖C‖ * d * (2 * t / ρ + 3 / ρ ^ 2)
      = 2 * ‖C‖ * (t * d) / ρ + 3 * ‖C‖ * d / ρ ^ 2 := by ring
  rw [e2]
  exact add_le_add t1 t2

/-! ### The packet's pointer is the sum of its modes' hands -/

section Packet

variable (M : ℕ) (J μ₀ μ₁ : ℝ)

/-- **The rate of the clock's mode `m`**: the level splitting at that mode's lattice
momentum. -/
noncomputable def modeRate (m : ℤ) : ℝ :=
  levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))

/-- **The coherence carried by mode `m`** of the device's packet prepared at `t₁`. -/
noncomputable def modeCoh (β : ℤ → ℂ) (t₁ : ℝ) (m : ℤ) : ℂ :=
  (1 / 2) * levelWeight (L := M + 1) J μ₀ μ₁ (unitAmp (M + 1) J μ₀ β) (unitAmp (M + 1) J μ₁ β) m
    * Complex.exp (Complex.I * (((-modeRate M J μ₀ μ₁ m : ℝ) : ℂ) * (t₁ : ℂ)))

variable {M J μ₀ μ₁}

theorem bandE_sub_eq_neg_modeRate (m : ℤ) :
    ((bandE J μ₀ (angleZ (M + 1) m) - bandE J μ₁ (angleZ (M + 1) m) : ℝ) : ℂ)
      = ((-modeRate M J μ₀ μ₁ m : ℝ) : ℂ) := by
  simp only [modeRate, levelClockRate, bandE]
  push_cast
  ring

/-- ★ **The packet's coherence, mode by mode, from any start**: each mode's coherence turns at
its own rate. -/
theorem deviceCoherence_packet_shift {W : Finset ℤ} (hD : Distinct (M + 1) W) (β : ℤ → ℂ)
    (t₁ s : ℝ) :
    deviceCoherence (deviceProp (L := M + 1) J μ₀ μ₁ s *ᵥ devicePacket J μ₀ μ₁ W β t₁)
      = ∑ m ∈ W, Complex.exp (Complex.I * (((-modeRate M J μ₀ μ₁ m : ℝ) : ℂ) * s))
          * modeCoh M J μ₀ μ₁ β t₁ m := by
  rw [deviceProp_devicePacket_shift, (device_observables J μ₀ μ₁ W β (t₁ + s)).2.2,
    levelCoherence_eq J μ₀ μ₁ hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [bandE_sub_eq_neg_modeRate, modeCoh]
  have h : Complex.exp (Complex.I * (((-modeRate M J μ₀ μ₁ m : ℝ) : ℂ) * ((t₁ + s : ℝ) : ℂ)))
      = Complex.exp (Complex.I * (((-modeRate M J μ₀ μ₁ m : ℝ) : ℂ) * (s : ℂ)))
        * Complex.exp (Complex.I * (((-modeRate M J μ₀ μ₁ m : ℝ) : ℂ) * (t₁ : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]
  ring

/-- The packet's coherence at its start is the sum of its modes' coherences. -/
theorem deviceCoherence_packet_eq_sum {W : Finset ℤ} (hD : Distinct (M + 1) W) (β : ℤ → ℂ)
    (t₁ : ℝ) :
    deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)
      = ∑ m ∈ W, modeCoh M J μ₀ μ₁ β t₁ m := by
  rw [(device_observables J μ₀ μ₁ W β t₁).2.2, levelCoherence_eq J μ₀ μ₁ hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [bandE_sub_eq_neg_modeRate, modeCoh]
  ring

/-- ★★ **The accumulated uncoupled reading of the packet is the sum of its modes' hands**,
exactly, when every mode's rate is non-zero. -/
theorem integral_clockFreeRead_packet {W : Finset ℤ} (hD : Distinct (M + 1) W) (β : ℤ → ℂ)
    (t₁ : ℝ) (hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β t₁ ≠ 0)
    (hR : ∀ m ∈ W, modeRate M J μ₀ μ₁ m ≠ 0) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, clockFreeRead J μ₀ μ₁ (deviceRay _ hΨ) s
      = 2 * (∑ m ∈ W, clockHand (modeRate M J μ₀ μ₁ m) (modeCoh M J μ₀ μ₁ β t₁ m) t)
        / (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re := by
  have h : ∀ s, clockFreeRead J μ₀ μ₁ (deviceRay _ hΨ) s
      = 2 * (∑ m ∈ W, clockQuad (modeRate M J μ₀ μ₁ m) (modeCoh M J μ₀ μ₁ β t₁ m) s)
        / (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re := fun s => by
    rw [clockFreeRead_deviceRay, deviceCoherence_packet_shift hD, Complex.re_sum]
    simp only [re_exp_mul_eq_clockQuad]
  simp only [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum
      (fun m _ => (continuous_clockQuad _ _).intervalIntegrable 0 t)]
  congr 2
  exact Finset.sum_congr rfl fun m hm => integral_clockQuad (hR m hm) _ t

end Packet

/-! ### The swing of a clock packet, with an error linear in the horizon -/

section Swing

variable {M : ℕ} {f : ℝ → ℝ} {J μ₀ μ₁ : ℝ} (g : ℝ) (hf : Function.Periodic f 1)

/-- **The swing's error for a packet, up to `T`**: the dephasing term
`4 |g f'| ε (2T/ρ + 3/ρ²)/n`, linear in the horizon, and the phase term
`4 |g f'| |Re C₀| / (R n)` of a device not started at a turning point. Here `ε` bounds the
sum over the modes of `‖C_m‖ |R_m − R|` and `ρ` is a lower bound of the rates. -/
noncomputable def packetSwingErr (φ : AddCircle (1 : ℝ)) (R n ρ : ℝ) (C₀ : ℂ) (ε T : ℝ) : ℝ :=
  4 * |g * hf.deriv_periodic.lift φ| * (ε * (2 * T / ρ + 3 / ρ ^ 2)) / n
    + 4 * |g * hf.deriv_periodic.lift φ| * |C₀.re| / (R * n)

/-- ★★ **The pointer of a clock packet against the swing, linearly in the horizon.** On a
fibre where the profile vanishes, for the device's packet on a window of distinct modes whose
rates are all at least `ρ > 0`, a reference rate `R ≥ ρ`, and `ε` at least the sum over the
modes of `‖C_m‖ |R_m − R|`: up to the horizon `T` the pointer's displacement is within
`packetSwingErr` of `clockSwingAmp` times `1 − cos R t`. -/
theorem abs_clockPointerShift_packet_sub_swing_le {φ : AddCircle (1 : ℝ)}
    (h0 : hf.lift φ = 0) {W : Finset ℤ} (hD : Distinct (M + 1) W) (β : ℤ → ℂ) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β t₁ ≠ 0) {R ρ ε : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) (hρm : ∀ m ∈ W, ρ ≤ modeRate M J μ₀ μ₁ m)
    (hε : ∑ m ∈ W, ‖modeCoh M J μ₀ μ₁ β t₁ m‖ * |modeRate M J μ₀ μ₁ m - R| ≤ ε)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |clockPointerShift J μ₀ μ₁ g hf φ (deviceRay _ hΨ) t
        - clockSwingAmp g hf φ R (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re
            (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁))
          * (1 - Real.cos (R * t))|
      ≤ packetSwingErr g hf φ R (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re ρ
          (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)) ε T := by
  set n := (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re with hn
  set C₀ := deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁) with hC₀
  set d := hf.deriv_periodic.lift φ with hd
  have hn0 : 0 < n := deviceNorm_re_pos hΨ
  have hR : 0 < R := hρ.trans_le hρR
  have hRm : ∀ m ∈ W, modeRate M J μ₀ μ₁ m ≠ 0 := fun m hm => (hρ.trans_le (hρm m hm)).ne'
  set S := ∑ m ∈ W, clockHand (modeRate M J μ₀ μ₁ m) (modeCoh M J μ₀ μ₁ β t₁ m) t with hS
  have hshift : clockPointerShift J μ₀ μ₁ g hf φ (deviceRay _ hΨ) t = -(4 * g) * d * S / n := by
    rw [clockPointerShift]
    simp only [clockRead_of_lift_eq_zero J μ₀ μ₁ g hf h0]
    rw [integral_clockFreeRead_packet hD β t₁ hΨ hRm t]
    ring
  have hH : clockHand R C₀ t = ∑ m ∈ W, clockHand R (modeCoh M J μ₀ μ₁ β t₁ m) t := by
    rw [hC₀, deviceCoherence_packet_eq_sum hD, clockHand_sum]
  have hε0 : 0 ≤ ε := (Finset.sum_nonneg fun m _ =>
    mul_nonneg (norm_nonneg _) (abs_nonneg _)).trans hε
  have hfac : 0 ≤ 2 * t / ρ + 3 / ρ ^ 2 := by positivity
  have hfacT : 2 * t / ρ + 3 / ρ ^ 2 ≤ 2 * T / ρ + 3 / ρ ^ 2 := by
    have : 2 * t / ρ ≤ 2 * T / ρ := div_le_div_of_nonneg_right (by linarith) hρ.le
    linarith
  have hSH : |S - clockHand R C₀ t| ≤ ε * (2 * T / ρ + 3 / ρ ^ 2) := by
    rw [hH, hS, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ W, |clockHand (modeRate M J μ₀ μ₁ m) (modeCoh M J μ₀ μ₁ β t₁ m) t
            - clockHand R (modeCoh M J μ₀ μ₁ β t₁ m) t|
        ≤ ∑ m ∈ W, ‖modeCoh M J μ₀ μ₁ β t₁ m‖ * |modeRate M J μ₀ μ₁ m - R|
            * (2 * t / ρ + 3 / ρ ^ 2) :=
          Finset.sum_le_sum fun m hm => abs_clockHand_sub_le hρ (hρm m hm) hρR _ ht
      _ = (∑ m ∈ W, ‖modeCoh M J μ₀ μ₁ β t₁ m‖ * |modeRate M J μ₀ μ₁ m - R|)
            * (2 * t / ρ + 3 / ρ ^ 2) := by rw [Finset.sum_mul]
      _ ≤ ε * (2 * T / ρ + 3 / ρ ^ 2) := mul_le_mul hε hfacT hfac hε0
  have e : -(4 * g) * d * S / n - clockSwingAmp g hf φ R n C₀ * (1 - Real.cos (R * t))
      = -(4 * (g * d)) * (S - clockHand R C₀ t) / n
        + -(4 * (g * d)) * C₀.re * Real.sin (R * t) / (R * n) := by
    unfold clockSwingAmp clockHand
    rw [← hd]
    field_simp
    ring
  rw [hshift, e]
  refine (abs_add_le _ _).trans ?_
  unfold packetSwingErr
  rw [← hd]
  refine add_le_add ?_ ?_
  · rw [abs_div, abs_of_pos hn0, abs_mul, abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSH (by positivity)) hn0.le
  · rw [abs_div, abs_of_pos (mul_pos hR hn0), abs_mul, abs_mul, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 4)]
    refine div_le_div_of_nonneg_right ?_ (mul_pos hR hn0).le
    calc 4 * |g * d| * |C₀.re| * |Real.sin (R * t)|
        ≤ 4 * |g * d| * |C₀.re| * 1 := by
          gcongr
          exact Real.abs_sin_le_one _
      _ = 4 * |g * d| * |C₀.re| := mul_one _

/-- ★★★ **A clock packet is a swing up to a horizon, with an error linear in the horizon.**
Under the joint flow `clockPointerFlow`, on a fibre where the profile vanishes, for the
device's packet on a window of distinct modes with rates at least `ρ > 0`: with the half
amplitude `A = clockSwingAmp` at the reference rate `R` and the error `δ = packetSwingErr` up
to `T`, a pointer started inside the ready arc by more than `δ` whose swing reaches the
displayed arc and stays in it is a swing history at the rate `R` up to `T`. -/
theorem isSwing_clockPointerFlow_packet (hc : ContDiff ℝ ∞ f) {W : Finset ℤ}
    (hD : Distinct (M + 1) W) (β : ℤ → ℂ) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β t₁ ≠ 0) {R ρ ε : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) (hρm : ∀ m ∈ W, ρ ≤ modeRate M J μ₀ μ₁ m)
    (hε : ∑ m ∈ W, ‖modeCoh M J μ₀ μ₁ β t₁ m‖ * |modeRate M J μ₀ μ₁ m - R| ≤ ε)
    (q : KTorus) (h0 : hf.lift q.2 = 0) {T A δ : ℝ}
    (hAe : A = clockSwingAmp g hf q.2 R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re
      (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)))
    (hδe : δ = packetSwingErr g hf q.2 R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)).re ρ
      (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)) ε T)
    (hδ0 : 0 ≤ δ) (hA : 0 < A) (h₁ : δ < rep q.1) (h₂ : rep q.1 + δ ≤ 1 / 6)
    (h₃ : 1 / 3 < rep q.1 + 2 * A - δ) (h₄ : rep q.1 + 2 * A + δ ≤ 5 / 6) :
    IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g hf hc t (clockArenaEquiv M (deviceRay _ hΨ), q))
      R (1 - (1 / 3 - rep q.1 - δ) / A) (1 - (1 / 3 - rep q.1 + δ) / A) T := by
  refine isSwing_of_abs_shift_sub_le (hρ.trans_le hρR) hA hδ0
    (fun t _ _ => clockPointerFlow_snd J μ₀ μ₁ g hf hc t _ q) (fun t ht htT => ?_) h₁ h₂ h₃ h₄
  rw [hAe, hδe]
  exact abs_clockPointerShift_packet_sub_swing_le g hf h0 hD β t₁ hΨ hρ hρR hρm hε ht htT

end Swing

/-! ### The localised packet of #262's device meets the conditions on a stated horizon -/

section Device

variable {M : ℕ}

/-- The sum over the modes of `‖C_m‖ |R_m − R|` is at most the sharp drift `deviceDrift`. -/
theorem sum_norm_modeCoh_mul_le {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀)
    (h01 : μ₀ ≤ μ₁) (hℓ : 0 < ℓ) {W : Finset ℤ}
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₁ : ℝ) :
    ∑ m ∈ W, ‖modeCoh M (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁ β t₁ m‖
        * |modeRate M (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁ m
          - levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / (M + 1 : ℕ))
              * Real.sin (ℓ / (M + 1 : ℕ) * p₀))|
      ≤ deviceDrift c μ₀ μ₁ D p₀ := by
  have hterm : ∀ m ∈ W, ‖modeCoh M (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁ β t₁ m‖
        * |modeRate M (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁ m
          - levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / (M + 1 : ℕ))
              * Real.sin (ℓ / (M + 1 : ℕ) * p₀))|
      ≤ ‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (4 * μ₀ ^ 2)) := by
    intro m hm
    have hb := levelWeight_mul_rate_le (L := M + 1) hc h0 h01 hℓ (hWD m hm) β
    rw [modeCoh, norm_mul, norm_mul, norm_exp_I_mul_ofReal_mul, mul_one,
      show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, modeRate,
      show ∀ x y : ℝ, 1 / 2 * x * y = x * y / 2 from fun x y => by ring]
    have e : ‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (4 * μ₀ ^ 2))
        = ‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2)) / 2 := by
      ring
    rw [e]
    linarith
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [← Finset.sum_mul, hβ, deviceDrift, one_mul]

/-- ★★★ **The localised clock packet ticks, and its count obeys the dilated clock law, on a
horizon limited linearly by its dephasing.** The packet of #262's device on a ring of
`M + 1` sites, prepared a quarter turn early, with the clock's own pointer of profile `trainF`
started at the angle `1/12` on the fibre `0` and the strength `g = R/(16 Im C₀)`. Let `ε` be
the sharp drift `deviceDrift`, `ρ > 0` a lower bound of the rates of the modes and of the
reference rate `R`, and `κ = (1 − ((μ₁ − μ₀)/μ₀)²)/2 − (π/(2R)) ε`. If `κ > 0` and
`R ε (2T/ρ + 3/ρ² + π/(2R²)) < κ/3`, then up to the flow time `T`

* the pointer's readout history is a swing at the rate `R`, with an error `δ < 1/12`;
* every tick count `N` at `T` has
  `|2π N/(μ₁ − μ₀) − √(1 − (v/c)²) T| ≤ 2π/(μ₁ − μ₀) + ((μ₁ − μ₀)/E₀) T`.

The condition is linear in `T`. `T` is the flow parameter (UA-7); the count does not hold
it. -/
theorem clock_packet_ticks {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (hℓ : 0 < ℓ) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {J σ R ε : ℝ} (hJ : J = scaledHop c (ℓ / (M + 1 : ℕ)))
    (hσ : σ = 2 * J * Real.sin (ℓ / (M + 1 : ℕ) * p₀)) (hR : R = levelClockRate μ₀ μ₁ σ)
    (hε : ε = deviceDrift c μ₀ μ₁ D p₀) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hρm : ∀ m ∈ W, ρ ≤ modeRate M J μ₀ μ₁ m) {g : ℝ}
    (hg : g = R / (16 * (deviceCoherence
      (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).im))
    (hκ : 0 < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2))
      < ((1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε) / 3) :
    ∃ (hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))) ≠ 0) (δ : ℝ),
      0 ≤ δ ∧ δ < 1 / 12
      ∧ IsSwing (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M J μ₀ μ₁ g trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          R (1 - (1 / 3 - 1 / 12 - δ) / (1 / 4)) (1 - (1 / 3 - 1 / 12 + δ) / (1 / 4)) T
      ∧ ∀ N : ℕ, IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M J μ₀ μ₁ g trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))) T N →
        |clockOpTime μ₀ μ₁ N - Real.sqrt (1 - (vRel c μ₀ σ / c) ^ 2) * T|
          ≤ 2 * Real.pi / (μ₁ - μ₀) + (μ₁ - μ₀) / dispE μ₀ σ * T := by
  have hπ := Real.pi_pos
  have h1 : 0 < μ₁ := h0.trans h01
  have hR0 : 0 < R := hρ.trans_le hρR
  have hD := (noWrap_distinct_of_window (L := M + 1) hWin).2
  have hdev := clock_tick_device (M := M) trainF_periodic contDiff_trainF hc h0 h01 hℓ hWin hWD
    β hβ (0 : ℝ)
  simp only [← hJ, ← hσ, ← hR, ← hε] at hdev
  obtain ⟨hΨ, hre, him, -⟩ := hdev
  set C₀ := deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R)))) with hC₀
  set κ := (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε with hκd
  have him0 : 0 < C₀.im := hκ.trans_le him
  have hn1 : (deviceNorm
      (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re = 1 := by
    rw [deviceNorm_devicePacket h0 h1 hD, hβ]
    simp
  have hg0 : 0 < g := by rw [hg]; positivity
  have hε0 : 0 ≤ ε := by
    have := (abs_nonneg _).trans hre
    have h2 : 0 < Real.pi / (2 * R) := by positivity
    exact nonneg_of_mul_nonneg_right this h2
  have hsum : ∑ m ∈ W, ‖modeCoh M J μ₀ μ₁ β (-(Real.pi / (2 * R))) m‖
      * |modeRate M J μ₀ μ₁ m - R| ≤ ε := by
    rw [hε, hR, hσ, hJ]
    exact sum_norm_modeCoh_mul_le hc h0 h01.le hℓ hWD β hβ _
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  set δ := packetSwingErr g trainF_periodic (0 : AddCircle (1 : ℝ)) R
    (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re ρ C₀ ε T with hδd
  have hfac : 0 ≤ 2 * T / ρ + 3 / ρ ^ 2 := by positivity
  have hδeq : δ = R / (4 * C₀.im) * (ε * (2 * T / ρ + 3 / ρ ^ 2) + |C₀.re| / R) := by
    rw [hδd, packetSwingErr, hn1, trainF_deriv_lift_zero, mul_neg_one, abs_neg,
      abs_of_pos hg0, hg]
    field_simp
    ring
  have hδ0 : 0 ≤ δ := by
    rw [hδeq]
    have : 0 ≤ |C₀.re| / R := div_nonneg (abs_nonneg _) hR0.le
    have h3 : 0 ≤ ε * (2 * T / ρ + 3 / ρ ^ 2) := mul_nonneg hε0 hfac
    positivity
  have hδlt : δ < 1 / 12 := by
    have hreR : |C₀.re| / R ≤ ε * (Real.pi / (2 * R ^ 2)) := by
      rw [div_le_iff₀ hR0]
      calc |C₀.re| ≤ Real.pi / (2 * R) * ε := hre
        _ = ε * (Real.pi / (2 * R ^ 2)) * R := by field_simp
    have hb : ε * (2 * T / ρ + 3 / ρ ^ 2) + |C₀.re| / R
        ≤ ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) := by
      rw [mul_add]
      linarith
    have hpos : 0 < R / (4 * C₀.im) := by positivity
    have hstep : δ ≤ R / (4 * C₀.im)
        * (ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2))) := by
      rw [hδeq]
      exact mul_le_mul_of_nonneg_left hb hpos.le
    have hE : R / (4 * C₀.im) * (ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)))
        = R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) / (4 * C₀.im) := by
      ring
    have hlt : R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) / (4 * C₀.im)
        < 1 / 12 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hA : (1 / 4 : ℝ) = clockSwingAmp g trainF_periodic (0 : AddCircle (1 : ℝ)) R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re C₀ := by
    rw [clockSwingAmp, hn1, trainF_deriv_lift_zero, hg]
    field_simp
    ring
  have hsw := isSwing_clockPointerFlow_packet g trainF_periodic contDiff_trainF hD β
    (-(Real.pi / (2 * R))) hΨ hρ hρR hρm hsum
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) trainF_lift_zero hA hδd hδ0
    (by norm_num) (by rw [hrep]; linarith) (by rw [hrep]; linarith) (by rw [hrep]; linarith)
    (by rw [hrep]; linarith)
  simp only [hrep] at hsw
  refine ⟨hΨ, δ, hδ0, hδlt, hsw, fun N hN => ?_⟩
  have hsw' : IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g trainF_periodic contDiff_trainF t
        (clockArenaEquiv M (deviceRay _ hΨ),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
      (levelClockRate μ₀ μ₁ σ) (1 - (1 / 3 - 1 / 12 - δ) / (1 / 4))
      (1 - (1 / 3 - 1 / 12 + δ) / (1 / 4)) T := by
    rw [← hR]
    exact hsw
  exact hsw'.abs_clockOpTime_sub_dilated_le hc.ne' h0 h01 hT hN

end Device

end CSD.RecordLayer

end
