/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracDevice
public import CsdLean4.RecordLayer.DiracSignal
public import CsdLean4.RecordLayer.MovingRadarPair

/-!
# The device's ticks as records, and a signal timed by them

**Category:** 7-SigmaLayer (the record layer). BACKLOG #271 (residue of ~~#262~~ and ~~#269~~).

~~#262~~'s `dirac_device` gives the clock's reading as a phase of the device's state, and ~~#269~~'s
`dirac_signal` reads a speed off two detector records in the chain's time. Here the reading is
**written**: a detector on the device's internal levels writes a record each time the reading
returns to its starting mark, as an actual occurrence of the device's evolution `e^{−itH_dev}`;
and, with the device beside the chain, the departure and arrival of #269's signal are timed in the
device's **ticks**.

## The device's evolution

* `deviceProp` (`e^{−itH_dev}`), `deviceProp_zero`, `deviceProp_add`, `continuous_deviceProp`;
  `levelLift` (one level carrying a chain state), `deviceHam_mulVec_levelLift`,
  ★ `deviceProp_levelLift_mode`, `devicePacket_eq_sum`; ★★ `deviceProp_devicePacket` — **the
  device's evolution carries the device**.

## The tick detector

* `readWeight` (the Born weight of the internal readout `(|0⟩ + u|1⟩)/√2`); ★ `readWeight_sub` —
  **the readout's excess over its partner `|−u⟩` is `2 Re(ū C)`**, `C` the device's coherence;
* `tickWeight` (that excess, halved and rectified: the detector responds only while the reading is
  near the mark `u`), `tickWeight_eq`, `tickWeight_nonneg`, `continuous_tickWeight`;
* `TickArena`, `tickFlow` (the device by `e^{−itH_dev}`, its register integrating the tick weight
  with gain `g`), `tickFlow_zero`, `tickFlow_add`, `measurable_tickFlow`, `tickEvolve`,
  `tickRead`;
* ★★ `integral_max_cos` (**`∫₀^{2πn/R} max(κ cos(Rs), 0) ds = 2nκ/R`**),
  ★ `integral_max_cos_lt` (strictly below before the mark), `integral_max_cos_mono`;
* `tickMark`, `re_star_tickMark_mul`, `norm_tickMark`, ★ `tickWeight_tickMark` (a reading turning at
  rate `R` gives the weight `max(|C₀| cos(Rs), 0)`); ★★★ `tickDetector` — **tick `n` as an actual occurrence, written at
  exactly `2πn/R`**.

## The device in one mode

* `distinct_singleton`; ★★ `deviceCoherence_single` — **a device in one mode turns exactly** at the
  level splitting of its momentum; `deviceCoherence_single_ne_zero`, `levelClockRate_pos`;
  `singleTick`;
* ★★★ `dirac_ticks` — **the ticks are occurrences of one evolution, which carries the device; tick
  `n` is written at exactly `2πn/R`, consecutive ticks one period `2π/R` apart; and `R/(μ₁ − μ₀)` is
  within `(μ₁ − μ₀)/E₀` of `√(1 − (v/c)²)`**: a moving device's ticks are dilated (~~#249~~).

## The signal timed by the device

* `sideEvolve` (two systems side by side, uncoupled), `sideEvolve_self`, `sideEvolve_comp`,
  `measurable_sideEvolve`; ★ `ActualOccurrence.liftFst`, `ActualOccurrence.liftSnd` — **an
  occurrence of either system is an occurrence of both** (by `ActualOccurrence.pullback`);
* `restTick` (a device at rest, rest energies `1` and `1 + 10⁻⁶`, period `T = 2π·10⁶`), `restRate`;
  `timedStart`, `timedArrival`, `timedTick`;
* ★★★ `dirac_timed_signal` — **the departure record, the arrival record and every tick are
  occurrences of one evolution from one preparation; the departure is written between ticks `12`
  and `14`, the arrival between ticks `562` and `641`; the arcs are `450 cT` to `500 cT` apart; and
  the speed read in ticks lies in `[450/629, 125/137] ∋ 4/5`, below `c`.**

## The findings

1. **The clock's reading is written as records.** A detector integrating a rectified Born weight of
   the device's own levels writes tick `n` at exactly the `n`-th return of the reading to its mark;
   for a moving device the ticks are dilated by `√(1 − (v/c)²)` within `(μ₁ − μ₀)/E₀`.
2. **A speed is read in a device's ticks.** The bracket `[450/629, 125/137]` is a little wider than
   #269's `[144/201, 72/79]` in the chain's time (each record is placed only between two ticks), and
   still contains `4/5` and stays below `1`.

## Honest scope

⚠️ **The device is in one mode.** It is exact (no spread, no drift), and it is spread over its own
ring: it has no position. A localized device (#262's window) turns only within an error linear in `t`;
`DiracDeviceTicks.lean` (#272) absorbs it.

⚠️ **The detector is calibrated.** Its mark is the device's starting reading, and its thresholds are
set in units of one turn's integral `2g|C₀|/R`, which needs `R` and `|C₀|`. The rectified readout is
a stated detector law (#251, #266).

⚠️ **The device sits beside the chain, uncoupled**, and is compared with the records by the one
evolution they share. An observer at the start arc learns of the arrival only by a signal back
(#270), and moving observers are `DiracTwin.lean` (#253); the device timing #269's signal is at rest.

⚠️ **The speed needs `c T` in the chain's units**: the arcs' separation is converted to light-ticks
with the device's rest splitting `10⁻⁶`.

References: `specs/BACKLOG.md` #271, #262, #269, #249, #251, #253, #266, #270, #39;
`CV/DiracDevice.lean` (`deviceHam`, `devicePacket`, `deviceCoherence`, `device_observables`,
`levelCoherence_eq`, `levelWeight_unitAmp_bounds`); `CV/DiracClockChain.lean` (`levelClockRate`,
`clockRate_mem`, `abs_clockRate_div_sub_le`); `RecordLayer/DiracArrival.lean` (`chainProp`,
`exp_mulVec_of_mulVec_eq_smul`, `wholeEvolve`); `RecordLayer/DiracSignal.lean` (`startDetector`,
`dirac_signal`, `separation_arcs`); `RecordLayer/DiracTiming.lean` (`sharpDetector`);
`RecordLayer/MovingRadarPair.lean` (`ActualOccurrence.pullback`); `RecordLayer/RecordOccurrence.lean`
(`ActualOccurrence`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### The device's evolution -/

theorem blockDiagonal_mulVec_apply {n : Type*} [Fintype n] (M : Fin 2 → Matrix n n ℂ)
    (Ψ : n × Fin 2 → ℂ) (p : n) (i : Fin 2) :
    (Matrix.blockDiagonal M *ᵥ Ψ) (p, i) = (M i *ᵥ fun q => Ψ (q, i)) p := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **The device's evolution** `e^{−itH_dev}`. -/
noncomputable def deviceProp (J μ₀ μ₁ t : ℝ) :
    Matrix ((ZMod L × Fin 2) × Fin 2) ((ZMod L × Fin 2) × Fin 2) ℂ :=
  NormedSpace.exp ((-(I * t)) • deviceHam J μ₀ μ₁)

theorem deviceProp_zero (J μ₀ μ₁ : ℝ) : deviceProp (L := L) J μ₀ μ₁ 0 = 1 := by
  simp [deviceProp]

theorem deviceProp_add (J μ₀ μ₁ s t : ℝ) :
    deviceProp (L := L) J μ₀ μ₁ (s + t) = deviceProp J μ₀ μ₁ t * deviceProp J μ₀ μ₁ s := by
  rw [deviceProp, deviceProp, deviceProp, ← Matrix.exp_add_of_commute _ _
    (((Commute.refl (deviceHam (L := L) J μ₀ μ₁)).smul_left _).smul_right _), ← add_smul]
  congr 1
  push_cast
  ring_nf

open scoped Matrix.Norms.L2Operator in
theorem continuous_deviceProp (J μ₀ μ₁ : ℝ) :
    Continuous fun t => deviceProp (L := L) J μ₀ μ₁ t := by
  have h : Continuous fun u : ℂ => NormedSpace.exp (u • deviceHam (L := L) J μ₀ μ₁) :=
    continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_exp_smul_const' (𝕂 := ℂ) (deviceHam (L := L) J μ₀ μ₁) u).continuousAt
  exact h.comp (by fun_prop)

/-- **Level `i` of the device carrying the chain state `v`**, the other level empty. -/
def levelLift (i : Fin 2) (v : ZMod L × Fin 2 → ℂ) : (ZMod L × Fin 2) × Fin 2 → ℂ :=
  fun x => if x.2 = i then v x.1 else 0

omit [NeZero L] in
theorem levelLift_smul (i : Fin 2) (c : ℂ) (v : ZMod L × Fin 2 → ℂ) :
    levelLift i (c • v) = c • levelLift i v := by
  funext x
  simp only [levelLift, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

omit [NeZero L] in
theorem levelLift_sum (i : Fin 2) (W : Finset ℤ) (v : ℤ → ZMod L × Fin 2 → ℂ) :
    levelLift i (∑ m ∈ W, v m) = ∑ m ∈ W, levelLift i (v m) := by
  funext x
  simp only [levelLift, Finset.sum_apply]
  split_ifs <;> simp

theorem deviceHam_mulVec_levelLift (J μ₀ μ₁ : ℝ) (i : Fin 2) (v : ZMod L × Fin 2 → ℂ) :
    deviceHam J μ₀ μ₁ *ᵥ levelLift i v = levelLift i (diracHam J (levelMass μ₀ μ₁ i) *ᵥ v) := by
  funext ⟨p, j⟩
  rw [deviceHam_mulVec_apply]
  by_cases h : j = i
  · subst h
    simp [levelLift]
  · have h0 : (fun q => levelLift (L := L) i v (q, j)) = 0 := by
      funext q
      simp [levelLift, h]
    rw [h0, Matrix.mulVec_zero]
    simp [levelLift, h]

/-- ★ **A mode on one level evolves by its phase under the device's evolution.** -/
theorem deviceProp_levelLift_mode (J μ₀ μ₁ t : ℝ) (i : Fin 2) (m : ℤ) :
    deviceProp (L := L) J μ₀ μ₁ t *ᵥ levelLift i (diracMode J (levelMass μ₀ μ₁ i) (m : ZMod L))
      = exp (-(I * bandE J (levelMass μ₀ μ₁ i) (angleZ L m)) * t)
        • levelLift i (diracMode J (levelMass μ₀ μ₁ i) (m : ZMod L)) := by
  have h : ((-(I * t)) • deviceHam (L := L) J μ₀ μ₁)
        *ᵥ levelLift i (diracMode J (levelMass μ₀ μ₁ i) (m : ZMod L))
      = (-(I * t) * bandE J (levelMass μ₀ μ₁ i) (angleZ L m))
        • levelLift i (diracMode J (levelMass μ₀ μ₁ i) (m : ZMod L)) := by
    rw [Matrix.smul_mulVec, deviceHam_mulVec_levelLift, diracHam_mulVec_diracMode,
      dispE_modeS_intCast, levelLift_smul, smul_smul]
  rw [deviceProp, exp_mulVec_of_mulVec_eq_smul h, ← Complex.exp_eq_exp_ℂ]
  congr 2
  ring

theorem devicePacket_eq_sum (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    devicePacket (L := L) J μ₀ μ₁ W β t = ∑ i : Fin 2, levelLift i
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • packet J (levelMass μ₀ μ₁ i) W
        (unitAmp L J (levelMass μ₀ μ₁ i) β) t) := by
  funext ⟨p, j⟩
  rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [levelLift, Ne.symm hi])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp [levelLift, devicePacket]

/-- ★★ **The device's evolution carries the device**: `e^{−itH_dev}` applied to the device at time
`0` is the device at time `t`. -/
theorem deviceProp_devicePacket (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    deviceProp (L := L) J μ₀ μ₁ t *ᵥ devicePacket J μ₀ μ₁ W β 0 = devicePacket J μ₀ μ₁ W β t := by
  rw [devicePacket_eq_sum, devicePacket_eq_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [packet, Finset.smul_sum, levelLift_sum, Matrix.mulVec_sum, smul_smul, levelLift_smul,
    Matrix.mulVec_smul, deviceProp_levelLift_mode]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  ring

/-! ### The tick readout -/

/-- **The weight of the device's level readout `|u⟩`**: the Born weight of the internal state
`(|0⟩ + u|1⟩)/√2` over the device's chain. -/
noncomputable def readWeight (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℝ :=
  ∑ p, ‖Ψ (p, 0) + star u * Ψ (p, 1)‖ ^ 2 / 2

/-- ★ **The readout's excess over its partner is the coherence**: the weights of `|u⟩` and `|−u⟩`
differ by `2 Re(ū C)`, `C` the device's coherence. -/
theorem readWeight_sub (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    readWeight u Ψ - readWeight (-u) Ψ = 2 * (star u * deviceCoherence Ψ).re := by
  rw [readWeight, readWeight, ← Finset.sum_sub_distrib, deviceCoherence, Finset.mul_sum,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, star_neg, Complex.neg_re, Complex.neg_im]
  ring

/-- **The tick weight**: the readout's excess over its partner, halved and rectified — the detector
responds only while the reading is near the mark `u`. -/
noncomputable def tickWeight (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℝ :=
  max ((readWeight u Ψ - readWeight (-u) Ψ) / 2) 0

theorem tickWeight_eq (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    tickWeight u Ψ = max (star u * deviceCoherence Ψ).re 0 := by
  rw [tickWeight, readWeight_sub]
  ring_nf

theorem tickWeight_nonneg (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : 0 ≤ tickWeight u Ψ :=
  le_max_right _ _

theorem continuous_tickWeight (u : ℂ) :
    Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => tickWeight u Ψ := by
  simp only [tickWeight_eq, deviceCoherence]
  refine (Complex.continuous_re.comp (continuous_const.mul ?_)).max continuous_const
  exact continuous_finsetSum _ fun p _ =>
    (continuous_star.comp (continuous_apply _)).mul (continuous_apply _)

/-- **The device with its tick register**: the device's state and one register. -/
abbrev TickArena (L : ℕ) : Type := ((ZMod L × Fin 2) × Fin 2 → ℂ) × ℝ

theorem continuous_deviceProp_mulVec (J μ₀ μ₁ : ℝ) :
    Continuous fun p : ((ZMod L × Fin 2) × Fin 2 → ℂ) × ℝ =>
      deviceProp (L := L) J μ₀ μ₁ p.2 *ᵥ p.1 :=
  Continuous.matrix_mulVec ((continuous_deviceProp J μ₀ μ₁).comp continuous_snd) continuous_fst

section Flow

variable (J μ₀ μ₁ g : ℝ) (u : ℂ)

/-- **The device with its tick detector**: the device evolves by `e^{−itH_dev}`, and the register
integrates the tick weight with gain `g`. -/
noncomputable def tickFlow (t : ℝ) (x : TickArena L) : TickArena L :=
  (deviceProp J μ₀ μ₁ t *ᵥ x.1,
    x.2 + g * ∫ s in (0 : ℝ)..t, tickWeight u (deviceProp J μ₀ μ₁ s *ᵥ x.1))

theorem state_tickFlow (t : ℝ) (x : TickArena L) :
    (tickFlow J μ₀ μ₁ g u t x).1 = deviceProp J μ₀ μ₁ t *ᵥ x.1 := rfl

theorem register_tickFlow (t : ℝ) (x : TickArena L) :
    (tickFlow J μ₀ μ₁ g u t x).2
      = x.2 + g * ∫ s in (0 : ℝ)..t, tickWeight u (deviceProp J μ₀ μ₁ s *ᵥ x.1) := rfl

theorem continuous_tickWeight_deviceProp (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    Continuous fun s => tickWeight u (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ) :=
  (continuous_tickWeight u).comp
    ((continuous_deviceProp_mulVec J μ₀ μ₁).comp (continuous_const.prodMk continuous_id))

theorem tickFlow_zero (x : TickArena L) : tickFlow J μ₀ μ₁ g u 0 x = x := by
  ext
  · simp [tickFlow, deviceProp_zero]
  · simp [tickFlow]

theorem tickFlow_add (s t : ℝ) (x : TickArena L) :
    tickFlow J μ₀ μ₁ g u (s + t) x = tickFlow J μ₀ μ₁ g u t (tickFlow J μ₀ μ₁ g u s x) := by
  ext
  · simp only [tickFlow, deviceProp_add, Matrix.mulVec_mulVec]
  · simp only [tickFlow, Matrix.mulVec_mulVec, ← deviceProp_add]
    have hi : ∀ a b : ℝ, IntervalIntegrable
        (fun v => tickWeight u (deviceProp (L := L) J μ₀ μ₁ v *ᵥ x.1)) volume a b :=
      fun a b => (continuous_tickWeight_deviceProp J μ₀ μ₁ u x.1).intervalIntegrable a b
    have hs : (∫ v in (0 : ℝ)..t, tickWeight u (deviceProp (L := L) J μ₀ μ₁ (s + v) *ᵥ x.1))
        = ∫ v in s..s + t, tickWeight u (deviceProp (L := L) J μ₀ μ₁ v *ᵥ x.1) := by
      rw [intervalIntegral.integral_comp_add_left
        (fun v => tickWeight u (deviceProp (L := L) J μ₀ μ₁ v *ᵥ x.1)) s, add_zero]
    rw [hs, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s (s + t))]
    ring

theorem continuous_tickFlow (t : ℝ) : Continuous (tickFlow (L := L) J μ₀ μ₁ g u t) := by
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_deviceProp_mulVec J μ₀ μ₁).comp (continuous_fst.prodMk continuous_const)
  · refine continuous_snd.add (continuous_const.mul ?_)
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : TickArena L) s => tickWeight u (deviceProp J μ₀ μ₁ s *ᵥ x.1)) ?_ 0 t
    exact (continuous_tickWeight u).comp
      ((continuous_deviceProp_mulVec J μ₀ μ₁).comp (continuous_fst.fst.prodMk continuous_snd))

theorem measurable_tickFlow (t : ℝ) : Measurable (tickFlow (L := L) J μ₀ μ₁ g u t) :=
  (continuous_tickFlow J μ₀ μ₁ g u t).measurable

/-- The two-time evolution. -/
noncomputable def tickEvolve (s t : OnticTime) : TickArena L → TickArena L :=
  tickFlow J μ₀ μ₁ g u (t - s)

theorem tickEvolve_self (t : OnticTime) :
    tickEvolve J μ₀ μ₁ g u t t = (id : TickArena L → TickArena L) := by
  funext x
  simp only [tickEvolve, sub_self, tickFlow_zero, id]

theorem tickEvolve_comp (s t v : OnticTime) :
    tickEvolve J μ₀ μ₁ g u t v ∘ tickEvolve J μ₀ μ₁ g u s t
      = (tickEvolve J μ₀ μ₁ g u s v : TickArena L → TickArena L) := by
  funext x
  simp only [tickEvolve, Function.comp]
  rw [show v - s = (t - s) + (v - t) by ring, tickFlow_add]

theorem measurable_tickEvolve (s t : OnticTime) :
    Measurable (tickEvolve (L := L) J μ₀ μ₁ g u s t) :=
  measurable_tickFlow J μ₀ μ₁ g u (t - s)

end Flow

/-- **The tick readout**: `1` once the register has reached `θ`. -/
noncomputable def tickRead (θ : ℝ) (x : TickArena L) : ℕ := if θ ≤ x.2 then 1 else 0

omit [NeZero L] in
theorem measurable_tickRead (θ : ℝ) : Measurable (tickRead (L := L) θ) :=
  Measurable.ite (measurableSet_le measurable_const measurable_snd) measurable_const
    measurable_const

/-! ### A rotating reading, rectified -/

/-- ★★ **The rectified reading over `n` turns**: `∫₀^{2πn/R} max(κ cos(Rs), 0) ds = 2nκ/R`. -/
theorem integral_max_cos {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) (n : ℕ) :
    ∫ s in (0 : ℝ)..2 * Real.pi * n / R, max (κ * Real.cos (R * s)) 0 = 2 * n * κ / R := by
  set f : ℝ → ℝ := fun v => max (κ * Real.cos v) 0 with hf_def
  have hfc : Continuous f := by fun_prop
  have hint : ∀ a b, IntervalIntegrable f volume a b := fun a b => hfc.intervalIntegrable a b
  have hper : Function.Periodic f (2 * Real.pi) := fun v => by simp [hf_def, Real.cos_add_two_pi]
  have hcomp := intervalIntegral.integral_comp_mul_left f (a := 0) (b := 2 * Real.pi * n / R)
    hR.ne'
  simp only [hf_def] at hcomp
  rw [hcomp, mul_zero,
    show R * (2 * Real.pi * n / R) = 0 + (n : ℤ) • (2 * Real.pi) by
      rw [zsmul_eq_mul, Int.cast_natCast, zero_add]; field_simp,
    hper.intervalIntegral_add_zsmul_eq n 0 hint, hper.intervalIntegral_add_eq 0 (-(Real.pi / 2)),
    ← intervalIntegral.integral_add_adjacent_intervals (hint _ (Real.pi / 2)) (hint _ _)]
  have h1 : ∫ v in -(Real.pi / 2)..Real.pi / 2, f v = 2 * κ := by
    rw [intervalIntegral.integral_congr (g := fun v => κ * Real.cos v) fun v hv => by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hv
      exact max_eq_left (mul_nonneg hκ (Real.cos_nonneg_of_neg_pi_div_two_le_of_le hv.1 hv.2))]
    rw [intervalIntegral.integral_const_mul, integral_cos, Real.sin_neg, Real.sin_pi_div_two]
    ring
  have h2 : ∫ v in Real.pi / 2..-(Real.pi / 2) + 2 * Real.pi, f v = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun v hv => by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hv
      exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hκ
        (Real.cos_nonpos_of_pi_div_two_le_of_le hv.1 (by linarith [hv.2])))]
    exact intervalIntegral.integral_zero
  rw [h1, h2, zsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- ★ **The rectified reading strictly grows into each mark**: before `2πn/R` its integral is below
the value at the mark. -/
theorem integral_max_cos_lt {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (n : ℕ) {t : ℝ}
    (ht : t < 2 * Real.pi * n / R) :
    ∫ s in (0 : ℝ)..t, max (κ * Real.cos (R * s)) 0
      < ∫ s in (0 : ℝ)..2 * Real.pi * n / R, max (κ * Real.cos (R * s)) 0 := by
  set tn := 2 * Real.pi * n / R
  set F : ℝ → ℝ := fun s => max (κ * Real.cos (R * s)) 0 with hF
  have hFc : Continuous F := by fun_prop
  have hint : ∀ a b, IntervalIntegrable F volume a b := fun a b => hFc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t tn)]
  set a := max t (tn - 1 / R)
  have hRinv : 0 < 1 / R := by positivity
  have hat : t ≤ a := le_max_left _ _
  have hatn : a < tn := max_lt ht (by linarith)
  have hmono : ∫ s in a..tn, F s ≤ ∫ s in t..tn, F s :=
    intervalIntegral.integral_mono_interval hat hatn.le le_rfl
      (Filter.Eventually.of_forall fun s => le_max_right _ _) (hint t tn)
  have hlow : ∫ _ in a..tn, (κ / 2) ≤ ∫ s in a..tn, F s := by
    refine intervalIntegral.integral_mono_on hatn.le intervalIntegrable_const (hint a tn)
      fun s hs => ?_
    have hs1 : tn - 1 / R ≤ s := (le_max_right _ _).trans hs.1
    have e1 : R * (tn - 1 / R) = n * (2 * Real.pi) - 1 := by
      simp only [tn]
      field_simp
    have e2 : R * tn = n * (2 * Real.pi) := by
      simp only [tn]
      field_simp
    have hx1 : -1 ≤ R * s - n * (2 * Real.pi) := by
      have := mul_le_mul_of_nonneg_left hs1 hR.le
      linarith
    have hx2 : R * s - n * (2 * Real.pi) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hs.2 hR.le
      linarith
    have hcos : 1 / 2 ≤ Real.cos (R * s) := by
      rw [← Real.cos_sub_nat_mul_two_pi (R * s) n]
      have := Real.one_sub_sq_div_two_le_cos (x := R * s - n * (2 * Real.pi))
      nlinarith
    exact le_max_of_le_left (by nlinarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have : 0 < (tn - a) * (κ / 2) := mul_pos (by linarith) (by linarith)
  linarith

theorem integral_max_cos_mono {κ R : ℝ} (hκ : 0 ≤ κ) {t₁ t : ℝ} (h : t₁ ≤ t) :
    ∫ s in (0 : ℝ)..t₁, max (κ * Real.cos (R * s)) 0
      ≤ ∫ s in (0 : ℝ)..t, max (κ * Real.cos (R * s)) 0 := by
  have hc : Continuous fun s => max (κ * Real.cos (R * s)) 0 := by fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s => max (κ * Real.cos (R * s)) 0) volume a b :=
    fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun s _ =>
    le_max_right (κ * Real.cos (R * s)) 0
  have _hκ := hκ
  linarith

/-- **The mark**: the direction of the device's coherence at the start. -/
noncomputable def tickMark (Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℂ :=
  deviceCoherence Ψ₀ / (‖deviceCoherence Ψ₀‖ : ℂ)

/-- **The exact turn read against the mark**: `Re(ū e^{−iRs} C₀) = |C₀| cos(Rs)`. -/
theorem re_star_tickMark_mul {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ} (hC : deviceCoherence Ψ₀ ≠ 0)
    (R s : ℝ) :
    (star (tickMark Ψ₀) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)).re
      = ‖deviceCoherence Ψ₀‖ * Real.cos (R * s) := by
  rw [tickMark]
  set C₀ := deviceCoherence Ψ₀
  have hn : ((‖C₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hC
  have hstar : star C₀ * C₀ = ((‖C₀‖ : ℝ) : ℂ) * ((‖C₀‖ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', sq]
  have hs : star ((‖C₀‖ : ℝ) : ℂ) = ((‖C₀‖ : ℝ) : ℂ) := Complex.conj_ofReal _
  have e : star (C₀ / ((‖C₀‖ : ℝ) : ℂ)) * (exp (I * (((-R : ℝ) : ℂ) * s)) * C₀)
      = ((‖C₀‖ : ℝ) : ℂ) * exp (((-R * s : ℝ) : ℂ) * I) := by
    rw [star_div₀, hs]
    calc star C₀ / ((‖C₀‖ : ℝ) : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * C₀)
        = star C₀ * C₀ / ((‖C₀‖ : ℝ) : ℂ) * exp (I * (((-R : ℝ) : ℂ) * s)) := by ring
      _ = _ := by
        rw [hstar, mul_div_cancel_right₀ _ hn]
        congr 2
        push_cast
        ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, neg_mul, Real.cos_neg]

/-- The mark is a phase. -/
theorem norm_tickMark {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ} (hC : deviceCoherence Ψ₀ ≠ 0) :
    ‖tickMark Ψ₀‖ = 1 := by
  rw [tickMark, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hC)]

/-- ★ **A rotating reading, read against its mark**: if the coherence has turned through `−Rs` from
`C₀`, the tick weight is `max(|C₀| cos(Rs), 0)`. -/
theorem tickWeight_tickMark {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ} (hC : deviceCoherence Ψ₀ ≠ 0)
    {R s : ℝ} (h : deviceCoherence Ψ = exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀) :
    tickWeight (tickMark Ψ₀) Ψ = max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0 := by
  rw [tickWeight_eq, h, re_star_tickMark_mul hC]

/-- ★★★ **A tick of the device as an actual occurrence**: for a device whose coherence turns
exactly at rate `R` from `C₀ ≠ 0`, the register integrating the tick weight against the mark
`C₀/|C₀|` reaches the threshold `2 g n |C₀|/R` at **exactly** `2πn/R` — the `n`-th time the reading
returns to the mark — and holds it for any window. -/
noncomputable def tickDetector (J μ₀ μ₁ g R : ℝ) (hg : 0 < g) (hR : 0 < R)
    (Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (hrot : ∀ t, deviceCoherence (deviceProp (L := L) J μ₀ μ₁ t *ᵥ Ψ₀)
      = exp (I * (((-R : ℝ) : ℂ) * t)) * deviceCoherence Ψ₀)
    (hC : deviceCoherence Ψ₀ ≠ 0) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
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
  writeStart := 2 * Real.pi * n / R
  writeEnd := 2 * Real.pi * n / R
  window := w
  isWrite :=
    have hreg : ∀ t, (tickFlow J μ₀ μ₁ g (tickMark Ψ₀) (t - 0) (Ψ₀, 0)).2
        = g * ∫ s in (0 : ℝ)..t, max (‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) 0 := fun t => by
      rw [sub_zero, register_tickFlow, zero_add]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact tickWeight_tickMark hC (hrot s)
    have hI := integral_max_cos (norm_nonneg (deviceCoherence Ψ₀)) hR n
    { start_le := by positivity
      interval := le_rfl
      window_nonneg := hw
      before := fun t _ ht => by
        show tickRead _ (tickFlow J μ₀ μ₁ g (tickMark Ψ₀) (t - 0) (Ψ₀, 0)) ≠ 1
        rw [tickRead, hreg]
        have hlt := integral_max_cos_lt (norm_pos_iff.2 hC) hR n ht
        rw [hI] at hlt
        split_ifs with h
        · exact absurd h (not_le.2 (mul_lt_mul_of_pos_left hlt hg))
        · decide
      holds := fun t ht _ => by
        show tickRead _ (tickFlow J μ₀ μ₁ g (tickMark Ψ₀) (t - 0) (Ψ₀, 0)) = 1
        rw [tickRead, hreg]
        have hle := integral_max_cos_mono (R := R) (norm_nonneg (deviceCoherence Ψ₀)) ht
        rw [hI] at hle
        split_ifs with h
        · rfl
        · exact absurd (mul_le_mul_of_nonneg_left hle hg.le) h }

/-! ### The device in one mode -/

omit [NeZero L] in
theorem distinct_singleton (m : ℤ) : Distinct L {m} := fun a ha b hb => by
  rw [Finset.mem_singleton] at ha hb
  subst ha hb
  simp

/-- ★★ **A device in one mode turns exactly**: its coherence turns through `−R t`, `R` the level
splitting at its momentum — no spread, no error. -/
theorem deviceCoherence_single (J μ₀ μ₁ : ℝ) (m : ℤ) (β : ℤ → ℂ) (t : ℝ) :
    deviceCoherence (deviceProp (L := L) J μ₀ μ₁ t *ᵥ devicePacket J μ₀ μ₁ {m} β 0)
      = exp (I * (((-levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ) * t))
        * deviceCoherence (devicePacket (L := L) J μ₀ μ₁ {m} β 0) := by
  rw [deviceProp_devicePacket, (device_observables J μ₀ μ₁ {m} β t).2.2,
    (device_observables J μ₀ μ₁ {m} β 0).2.2, levelCoherence_eq J μ₀ μ₁ (distinct_singleton m),
    levelCoherence_eq J μ₀ μ₁ (distinct_singleton m), Finset.sum_singleton, Finset.sum_singleton]
  have e : ((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ)
      = ((-levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ) := by
    rw [levelClockRate, bandE, bandE]
    push_cast
    ring
  rw [e]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  ring

/-- **A device in one mode has a reading at the start**: for `μ₀ ≤ μ₁ < 2μ₀` and a nonzero amplitude,
its coherence has positive real part. -/
theorem deviceCoherence_single_ne_zero {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) :
    deviceCoherence (devicePacket (L := L) J μ₀ μ₁ {m} β 0) ≠ 0 := by
  rw [(device_observables J μ₀ μ₁ {m} β 0).2.2,
    levelCoherence_eq J μ₀ μ₁ (distinct_singleton m), Finset.sum_singleton]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  intro h
  have hre := congrArg Complex.re h
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
    Complex.zero_re] at hre
  have hw := (levelWeight_unitAmp_bounds (L := L) (J := J) h0 h01 β m).1
  have hq : 0 < 1 - ((μ₁ - μ₀) / μ₀) ^ 2 := by
    have h1 : (μ₁ - μ₀) / μ₀ < 1 := (div_lt_one h0).2 (by linarith)
    have h2 : 0 ≤ (μ₁ - μ₀) / μ₀ := div_nonneg (by linarith) h0.le
    nlinarith
  have hb : 0 < ‖β m‖ ^ 2 := by positivity
  nlinarith [mul_pos hq hb]

/-- **The device's rate is positive** above the lower rest energy. -/
theorem levelClockRate_pos {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (s : ℝ) :
    0 < levelClockRate μ₀ μ₁ s :=
  lt_of_lt_of_le (mul_pos (by linarith) (div_pos h0 (dispE_pos h0 s)))
    (clockRate_mem h0 h01.le s).1

/-- ★★★ **The ticks of a device in one mode**: tick `n` of the device at momentum `m`, an actual
occurrence of the device's evolution, written at exactly `2πn/R`. -/
noncomputable def singleTick (J μ₀ μ₁ g : ℝ) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) (β : ℤ → ℂ) (hβ : β m ≠ 0) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  tickDetector J μ₀ μ₁ g (levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))) hg
    (levelClockRate_pos h0 h01 _) (devicePacket J μ₀ μ₁ {m} β 0)
    (deviceCoherence_single J μ₀ μ₁ m β) (deviceCoherence_single_ne_zero h0 h01.le h10 m hβ) n hw

/-- ★★★ **The device's tick records** (BACKLOG #271 (a)). A device in one mode `m` — rest energies
`μ₀ < μ₁ < 2μ₀`, its two levels carried by `e^{−itH_dev}` — with a detector integrating the tick
weight (the excess of the readout `|u⟩` over `|−u⟩` at the start's mark `u`, rectified):

* **its ticks are occurrences of one evolution**: every tick has the same evolution and the same
  preparation, and the evolution carries the device itself;
* **tick `n` is written at exactly `2πn/R`**, `R > 0` the level splitting at the device's momentum:
  consecutive ticks are one period `2π/R` apart;
* **the period is dilated by the motion**: `R/(μ₁ − μ₀)` is within `(μ₁ − μ₀)/E₀` of
  `√(1 − (v/c)²)`, `v` the velocity of the momentum `2J sin(2πm/L)` (~~#249~~). -/
theorem dirac_ticks {c J μ₀ μ₁ g : ℝ} (hc : c ≠ 0) (hg : 0 < g) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {w : ℝ} (hw : 0 ≤ w) :
    let s := 2 * J * Real.sin (angleZ L m)
    let R := levelClockRate μ₀ μ₁ s
    let o := fun n : ℕ => singleTick (L := L) J μ₀ μ₁ g hg h0 h01 h10 m β hβ n hw
    (∀ n n', (o n).evolve = (o n').evolve ∧ (o n).prep = (o n').prep)
    ∧ (∀ n t, ((o n).evolve 0 t (o n).prep).1 = devicePacket J μ₀ μ₁ {m} β t)
    ∧ 0 < R
    ∧ (∀ n : ℕ, (o n).writeStart = 2 * Real.pi * n / R ∧ (o n).writeEnd = 2 * Real.pi * n / R)
    ∧ (∀ n : ℕ, (o (n + 1)).writeStart - (o n).writeEnd = 2 * Real.pi / R)
    ∧ |R / (μ₁ - μ₀) - Real.sqrt (1 - (vRel c μ₀ s / c) ^ 2)| ≤ (μ₁ - μ₀) / dispE μ₀ s := by
  intro s R o
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun n t => ?_, levelClockRate_pos h0 h01 s,
    fun _ => ⟨rfl, rfl⟩, fun n => ?_, abs_clockRate_div_sub_le hc h0 h01 s⟩
  · show deviceProp J μ₀ μ₁ (t - 0) *ᵥ devicePacket J μ₀ μ₁ {m} β 0 = _
    rw [sub_zero, deviceProp_devicePacket]
  · show 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / R - 2 * Real.pi * n / R = 2 * Real.pi / R
    push_cast
    ring

/-! ### Two systems side by side -/

section Side

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {Ω : Type*} [MeasurableSpace Ω]
  {K : ℕ}

/-- **Two systems side by side**, uncoupled: each evolves by its own law. -/
def sideEvolve (e₁ : OnticTime → OnticTime → X → X) (e₂ : OnticTime → OnticTime → Y → Y) :
    OnticTime → OnticTime → X × Y → X × Y := fun s t z => (e₁ s t z.1, e₂ s t z.2)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem sideEvolve_self {e₁ : OnticTime → OnticTime → X → X} {e₂ : OnticTime → OnticTime → Y → Y}
    (h₁ : ∀ t, e₁ t t = id) (h₂ : ∀ t, e₂ t t = id) (t : OnticTime) :
    sideEvolve e₁ e₂ t t = id := by
  funext z
  simp [sideEvolve, h₁, h₂]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem sideEvolve_comp {e₁ : OnticTime → OnticTime → X → X} {e₂ : OnticTime → OnticTime → Y → Y}
    (h₁ : ∀ s t u, e₁ t u ∘ e₁ s t = e₁ s u) (h₂ : ∀ s t u, e₂ t u ∘ e₂ s t = e₂ s u)
    (s t u : OnticTime) : sideEvolve e₁ e₂ t u ∘ sideEvolve e₁ e₂ s t = sideEvolve e₁ e₂ s u := by
  funext z
  exact Prod.ext (congrFun (h₁ s t u) z.1) (congrFun (h₂ s t u) z.2)

theorem measurable_sideEvolve {e₁ : OnticTime → OnticTime → X → X}
    {e₂ : OnticTime → OnticTime → Y → Y} (h₁ : ∀ s t, Measurable (e₁ s t))
    (h₂ : ∀ s t, Measurable (e₂ s t)) (s t : OnticTime) : Measurable (sideEvolve e₁ e₂ s t) :=
  ((h₁ s t).comp measurable_fst).prodMk ((h₂ s t).comp measurable_snd)

/-- ★ **An occurrence of the first system is an occurrence of both side by side**, at any state of
the second. -/
def ActualOccurrence.liftFst (o : ActualOccurrence X Ω K) (e : OnticTime → OnticTime → Y → Y)
    (e_self : ∀ t, e t t = id) (e_comp : ∀ s t u, e t u ∘ e s t = e s u)
    (he : ∀ s t, Measurable (e s t)) (y₀ : Y) : ActualOccurrence (X × Y) Ω K :=
  o.pullback (sideEvolve o.evolve e) (sideEvolve_self o.evolve_self e_self)
    (sideEvolve_comp o.evolve_comp e_comp) (measurable_sideEvolve o.measurable_evolve he) Prod.fst
    measurable_fst (fun _ _ _ => rfl) (o.prep, y₀) rfl

/-- ★ **An occurrence of the second system is an occurrence of both side by side**, at any state of
the first. -/
def ActualOccurrence.liftSnd (o : ActualOccurrence Y Ω K) (e : OnticTime → OnticTime → X → X)
    (e_self : ∀ t, e t t = id) (e_comp : ∀ s t u, e t u ∘ e s t = e s u)
    (he : ∀ s t, Measurable (e s t)) (x₀ : X) : ActualOccurrence (X × Y) Ω K :=
  o.pullback (sideEvolve e o.evolve) (sideEvolve_self e_self o.evolve_self)
    (sideEvolve_comp e_comp o.evolve_comp) (measurable_sideEvolve he o.measurable_evolve) Prod.snd
    measurable_snd (fun _ _ _ => rfl) (x₀, o.prep) rfl

end Side

/-! ### The signal timed by the device -/

section Timed

variable {N : ℕ} [NeZero N]

/-- **The observer's clock**: a device at rest — mode `0` — with rest energies `1` and `1 + 10⁻⁶`,
read with gain `1`; tick `n` of it. -/
noncomputable def restTick (J : ℝ) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena N) ℕ N :=
  singleTick J 1 (1 + 1 / 10 ^ 6) 1 one_pos one_pos (by norm_num) (by norm_num) 0 (fun _ => 1)
    one_ne_zero n hw

omit [NeZero N] in
/-- The clock at rest turns at the rest splitting `10⁻⁶`. -/
theorem restRate (J : ℝ) :
    levelClockRate 1 (1 + 1 / 10 ^ 6) (2 * J * Real.sin (angleZ N 0)) = 1 / 10 ^ 6 := by
  have h : angleZ N 0 = 0 := by simp [angleZ]
  rw [h, Real.sin_zero, mul_zero, levelClockRate, dispE, dispE,
    show ((1 : ℝ) + 1 / 10 ^ 6) ^ 2 + 0 ^ 2 = (1 + 1 / 10 ^ 6) ^ 2 by ring,
    Real.sqrt_sq (by norm_num), show (1 : ℝ) ^ 2 + 0 ^ 2 = 1 ^ 2 by ring,
    Real.sqrt_sq (by norm_num)]
  ring

variable (hL : 10 ^ 13 ≤ L)

/-- **The departure record, with the observer's clock beside the chain.** -/
noncomputable def timedStart (J : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (WholeArena L × TickArena N) ℕ L :=
  (startDetector hL hw).liftFst (restTick J 0 hw).evolve (restTick J 0 hw).evolve_self
    (restTick J 0 hw).evolve_comp (restTick J 0 hw).measurable_evolve (restTick J 0 hw).prep

/-- **The arrival record, with the observer's clock beside the chain.** -/
noncomputable def timedArrival (J : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (WholeArena L × TickArena N) ℕ L :=
  (sharpDetector hL hw).liftFst (restTick J 0 hw).evolve (restTick J 0 hw).evolve_self
    (restTick J 0 hw).evolve_comp (restTick J 0 hw).measurable_evolve (restTick J 0 hw).prep

/-- **Tick `n` of the observer's clock, beside the chain.** -/
noncomputable def timedTick (J : ℝ) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (WholeArena L × TickArena N) ℕ N :=
  (restTick J n hw).liftSnd (startDetector hL hw).evolve (startDetector hL hw).evolve_self
    (startDetector hL hw).evolve_comp (startDetector hL hw).measurable_evolve
    (startDetector hL hw).prep

include hL in
/-- ★★★ **#269's signal timed by a clock device** (BACKLOG #271 (b)). The chain with its start-arc
and far-arc detectors, and beside it a device at rest with its tick detector (`dirac_ticks`, period
`T = 2π·10⁶`):

* **one evolution**: the departure record, the arrival record and every tick are actual occurrences
  of the same evolution from the same preparation;
* **the ticks**: tick `n` is written at exactly `nT`;
* **the records between the ticks**: the departure's write lies between ticks `12` and `14`, the
  arrival's between ticks `562` and `641`;
* **the arcs** are between `0.45 ℓ = 450 cT` and `ℓ/2 = 500 cT` apart (`ℓ = 2π·10⁹`, `c = 1`);
* **the speed in ticks**: at least `450` over the most ticks between the records (`641 − 12`), at most
  `500` over the fewest (`562 − 14`): `[450/629, 125/137] ∋ 4/5`, inside `(0, 1)` — **below `c`**,
  read off the records and the device's ticks. -/
theorem dirac_timed_signal (J : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    let T := 2 * Real.pi * 10 ^ 6
    let dep := timedStart (N := N) hL J hw
    let arr := timedArrival (N := N) hL J hw
    let tick := fun n : ℕ => timedTick (N := N) hL J n hw
    (∀ n, (tick n).evolve = dep.evolve ∧ (tick n).prep = dep.prep
      ∧ (tick n).evolve = arr.evolve ∧ (tick n).prep = arr.prep)
    ∧ (∀ n : ℕ, (tick n).writeStart = n * T ∧ (tick n).writeEnd = n * T)
    ∧ (tick 12).writeEnd ≤ dep.writeStart ∧ dep.writeEnd ≤ (tick 14).writeStart
    ∧ (tick 562).writeEnd ≤ arr.writeStart ∧ arr.writeEnd ≤ (tick 641).writeStart
    ∧ (∀ k ∈ nearArc L, ∀ j ∈ farArc L,
        9 * Real.pi / 10 ≤ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L|
          ∧ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L| ≤ 2 * Real.pi - 9 * Real.pi / 10)
    ∧ 9 * Real.pi * 10 ^ 9 / 10 = 450 * T ∧ Real.pi * 10 ^ 9 = 500 * T
    ∧ 450 * T / ((641 - 12) * T) = 450 / 629 ∧ 500 * T / ((562 - 14) * T) = 125 / 137
    ∧ (0 : ℝ) < 450 / 629 ∧ (450 / 629 : ℝ) ≤ 4 / 5 ∧ (4 / 5 : ℝ) ≤ 125 / 137
    ∧ (125 / 137 : ℝ) < 1 := by
  intro T dep arr tick
  have hπ := Real.pi_pos
  have hT : 0 < T := by positivity
  have htick : ∀ n : ℕ, (tick n).writeStart = n * T ∧ (tick n).writeEnd = n * T := fun n => by
    have h : (tick n).writeStart
        = 2 * Real.pi * n / levelClockRate 1 (1 + 1 / 10 ^ 6) (2 * J * Real.sin (angleZ N 0)) :=
      rfl
    rw [restRate] at h
    have h' : (tick n).writeEnd = (tick n).writeStart := rfl
    have e : 2 * Real.pi * (n : ℝ) / (1 / 10 ^ 6) = n * T := by
      simp only [T]
      field_simp
    exact ⟨h.trans e, h'.trans (h.trans e)⟩
  have hdep0 : dep.writeStart = Real.pi * 10 ^ 9 / 40 := rfl
  have hdep1 : dep.writeEnd = Real.pi * 10 ^ 9 / 36 := rfl
  have harr0 : arr.writeStart = 9 * Real.pi * 10 ^ 9 / 8 := rfl
  have harr1 : arr.writeEnd = 41 * Real.pi * 10 ^ 9 / 32 := rfl
  refine ⟨fun n => ⟨rfl, rfl, rfl, rfl⟩, htick, ?_, ?_, ?_, ?_, fun k hk j hj => ?_, ?_, ?_, ?_,
    ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [(htick 12).2, hdep0]
    simp only [T]
    push_cast
    nlinarith
  · rw [(htick 14).1, hdep1]
    simp only [T]
    push_cast
    nlinarith
  · rw [(htick 562).2, harr0]
    simp only [T]
    push_cast
    nlinarith
  · rw [(htick 641).1, harr1]
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

end Timed

end CSD.RecordLayer

end
