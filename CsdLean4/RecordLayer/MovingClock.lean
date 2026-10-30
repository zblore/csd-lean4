/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.HandClock

/-!
# A clock that moves: the control candidate

**Category:** 7-SigmaLayer (the record layer). BACKLOG #241 (the author's fourth operational-geometry
brief, step 1).

The brief asks first whether the present dynamics can carry a clock from site to site under one
autonomous evolution, ticking and keeping its records. **The transport now in the corpus cannot**:
#190's and #203's chains move an excitation by switching edges on in a prescribed order, which is an
externally imposed trajectory, and a uniform hopping chain disperses (the header of
`CV/ChainExchange.lean`). The smallest viable extension is a **degree of freedom that moves by its own
momentum**. This module builds the brief's control candidate (A) on it: a device with a position and a
momentum under the free energy `p²/(2m)`, carrying #201's hand clock and a memory register, passing
stationary detectors on a line of `L` sites. Everything is one autonomous flow; the velocity is the
device's conserved momentum divided by its mass, an initial condition, not a schedule.

## Occupancy

* `siteInd`, `occTime` — the time a device moving uniformly spends at site `k`;
  `siteInd_comp_intervalIntegrable`, ★ `occTime_add` (occupancy times add along the motion),
  `occTime_eq_zero_of_before`, ★★ `occTime_eq_inv_of_crossed` (**a site fully crossed has seen the
  device for exactly `1/v`**).

## The device

* `MovingState L` — the carried clock (`ActiveArena`), position, momentum, carried memory, and one
  detector register per site; `motionEnergy` (`p²/(2m)`);
* ★★ `movingFlow` — **the autonomous flow**; `movingFlow_zero`, ★★ `movingFlow_add` (the group law);
  ★ `hasDerivAt_pos_movingFlow` — Hamilton's equations for the motion, `ẋ = ∂H/∂p = p/m`;
  `pos_movingFlow`, `mom_movingFlow` (the momentum conserved);
* `siteOf` (the cell the position occupies — the site index is microscopic input);
  ★★ `siteOf_movingFlow_eq_iff` — **transport through the sites**: the device occupies site `k` exactly
  during `[(k − x)/v, (k + 1 − x)/v)`; ★ `siteOf_movingFlow_mono` — it never moves back;
  `movingFlow_instance` — a concrete instance at momentum `1` crossing sites `0, 1, 2`;
* `mem_movingFlow` — **the memory is retained**; `clock_movingFlow`, ★★ `abs_movingReading_sub_le` —
  **the carried clock keeps time during transport**, within #201's `τ_tick + 1/(2ω)`, whatever the
  momentum;
* ★★ `det_movingFlow_passage` — **a detector records the device's passage**: nothing before arrival,
  exactly `g_d m / p` once crossed;
* ★★ `clock_movingFlow_indep` — **no time dilation**: two devices carrying the same clock read the same
  at every time, whatever their momenta;
* ★★★ `moving_clock_control` — the package.

## The finding, and why this is the control

The device's clock and its motion are **decoupled**: the energy is `p²/(2m)` plus the clock's own,
with no term coupling them, so the moving clock's reading is a function of `t` alone. This is a
Galilean device — a preferred time shared by all motions — exactly what the brief counts as a useful
negative: the control (A) of #241's amendment. Its dispersion class is that of a free classical
particle, `E = p²/(2m)`, with no limiting speed. The test (B) — a two-band chain near its crossing,
where the band oscillation is the clock and its dilation can emerge — is #249.

## Honest scope

⚠️ **The position is a continuous ontic coordinate with sites as unit cells.** Transport is exact
(no dispersion) because the device is a free particle, not a lattice excitation; `siteOf` reads the
cell, which is microscopic input, as the brief requires.

⚠️ **The detectors read without back-reaction.** A Hamiltonian detector term `g_d χ_k(x) η_k` would
push the device by `−g_d χ_k'(x) η_k`; here the detectors are test detectors and their indicator
profile is not smooth. Their generation, with back-reaction, belongs to #242's disturbance bound.

⚠️ **The ticks during transport are #201's**, inherited through `clock_movingFlow`; their statement as
`ActualOccurrence`s of the joint evolution is #242.

⚠️ **One device and no signals between devices.** Two observers in one model are #243.

References: `specs/BACKLOG.md` #241, #242, #243, #247, #249, #201, #194, #190, #203, #39;
`RecordLayer/HandClock.lean` (`hand`, `abs_handReading_sub_le`), `RecordLayer/ActivatedWrite.lean`
(`activeFlow`, `activeFlow_add`), `CV/ChainExchange.lean`, `CV/WalkSchedule.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Occupancy along uniform motion -/

/-- The indicator of site `k`: the cell `[k, k + 1)` of the line. -/
noncomputable def siteInd (k : ℤ) (u : ℝ) : ℝ := (Set.Ico (k : ℝ) (k + 1)).indicator (fun _ => 1) u

/-- **The time a device moving uniformly from `x` at velocity `v` spends at site `k` during
`[0, t]`.** -/
noncomputable def occTime (k : ℤ) (x v t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, siteInd k (x + v * s)

theorem siteInd_comp_intervalIntegrable (k : ℤ) (x v a b : ℝ) :
    IntervalIntegrable (fun s => siteInd k (x + v * s)) volume a b := by
  have hS : MeasurableSet ((fun s : ℝ => x + v * s) ⁻¹' Set.Ico (k : ℝ) (k + 1)) :=
    (by fun_prop : Measurable fun s : ℝ => x + v * s) measurableSet_Ico
  have h : (fun s => siteInd k (x + v * s))
      = ((fun s : ℝ => x + v * s) ⁻¹' Set.Ico (k : ℝ) (k + 1)).indicator (fun _ => (1 : ℝ)) := by
    funext s
    simp only [siteInd, Set.indicator, Set.mem_preimage]
  rw [h, intervalIntegrable_iff]
  exact (integrableOn_const (by simp [Real.volume_uIoc])).indicator hS

/-- ★ **Occupancy times add along the motion**: the time at site `k` during `[0, s + t]` is the time
during `[0, s]` plus the time during the next `t`, started from where the device then is. -/
theorem occTime_add (k : ℤ) (x v s t : ℝ) :
    occTime k x v (s + t) = occTime k x v s + occTime k (x + v * s) v t := by
  unfold occTime
  rw [← intervalIntegral.integral_add_adjacent_intervals (siteInd_comp_intervalIntegrable k x v 0 s)
    (siteInd_comp_intervalIntegrable k x v s (s + t))]
  congr 1
  have h := intervalIntegral.integral_comp_add_right (fun u => siteInd k (x + v * u)) (a := 0)
    (b := t) s
  rw [zero_add, add_comm t s] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun u _ => ?_
  show siteInd k (x + v * (u + s)) = siteInd k (x + v * s + v * u)
  congr 1
  ring

/-- **Before the device reaches site `k`, the site has seen nothing of it.** -/
theorem occTime_eq_zero_of_before {k : ℤ} {x v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t)
    (hbefore : x + v * t < k) : occTime k x v t = 0 := by
  unfold occTime
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_,
    intervalIntegral.integral_zero]
  rw [Set.uIcc_of_le ht] at hs
  have hle : x + v * s ≤ x + v * t := by nlinarith [hs.2]
  simp only [siteInd, Set.indicator, Set.mem_Ico]
  rw [ite_eq_right (by intro h; linarith [h.1])]

/-- ★★ **Once the device has crossed site `k`, the site has seen it for exactly `1/v`.** -/
theorem occTime_eq_inv_of_crossed {k : ℤ} {x v t : ℝ} (hv : 0 < v) (hx : x < k)
    (hcross : (k : ℝ) + 1 ≤ x + v * t) : occTime k x v t = v⁻¹ := by
  unfold occTime
  have hsub := intervalIntegral.integral_comp_mul_add (a := 0) (b := t)
    (fun u => siteInd k u) hv.ne' x
  simp only [mul_zero, zero_add] at hsub
  rw [show (fun s => siteInd k (x + v * s)) = fun s => siteInd k (v * s + x) from
    funext fun s => by rw [add_comm], hsub, smul_eq_mul]
  have hb : x ≤ v * t + x := by linarith
  rw [intervalIntegral.integral_of_le hb]
  have hS : Set.Ico (k : ℝ) (k + 1) ⊆ Set.Ioc x (v * t + x) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hint : ∫ u in Set.Ioc x (v * t + x), siteInd k u = 1 := by
    simp only [siteInd]
    rw [integral_indicator_const _ measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
      Set.inter_eq_left.2 hS]
    simp [Measure.real, Real.volume_Ico]
  rw [hint, mul_one]

/-! ### The device and its arena -/

/-- **The moving device's state, with the stationary detectors of an `L`-site network**: the hand
clock it carries (#201: carrier and pointer), its position and momentum on the line of sites, a
memory register it carries, and one detector register per site. -/
structure MovingState (L : ℕ) where
  /-- The carried hand clock. -/
  clock : ActiveArena
  /-- The device's position on the line; site `k` is the cell `[k, k + 1)`. -/
  pos : ℝ
  /-- The device's momentum. -/
  mom : ℝ
  /-- The carried memory register. -/
  mem : LF4.KTorus
  /-- The stationary detectors' lifted registers. -/
  det : Fin L → ℝ

section Flow

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) {L : ℕ} (m gd : ℝ)

/-- The free energy of the device's motion, `p² / (2m)`. -/
noncomputable def motionEnergy (p : ℝ) : ℝ := p ^ 2 / (2 * m)

/-- ★★ **The autonomous flow of the moving clock**: the hand clock by #194's activated flow, the
position by the free flow of `p²/(2m)` (velocity `p/m`, the momentum conserved), the memory left
alone, and each site's detector advanced at rate `g_d` while the device occupies the site. -/
noncomputable def movingFlow (t : ℝ) (z : MovingState L) : MovingState L where
  clock := activeFlow J ħ g hf t z.clock
  pos := z.pos + z.mom / m * t
  mom := z.mom
  mem := z.mem
  det := fun k => z.det k + gd * occTime (k : ℕ) z.pos (z.mom / m) t

theorem movingFlow_zero : movingFlow J ħ g hf m gd 0 = (id : MovingState L → MovingState L) := by
  funext z
  cases z
  simp only [movingFlow, activeFlow_zero, mul_zero, add_zero, occTime,
    intervalIntegral.integral_same, id]

/-- ★★ **The group law**: one autonomous evolution, nothing switched on from outside. -/
theorem movingFlow_add (s t : ℝ) :
    movingFlow J ħ g hf m gd (s + t)
      = (movingFlow J ħ g hf m gd t ∘ movingFlow J ħ g hf m gd s : MovingState L → MovingState L) := by
  funext z
  simp only [movingFlow, Function.comp, activeFlow_add]
  congr 1
  · ring
  · funext k
    rw [occTime_add]
    ring

theorem pos_movingFlow (t : ℝ) (z : MovingState L) :
    (movingFlow J ħ g hf m gd t z).pos = z.pos + z.mom / m * t := rfl

theorem mom_movingFlow (t : ℝ) (z : MovingState L) : (movingFlow J ħ g hf m gd t z).mom = z.mom := rfl

/-- ★ **Hamilton's equations for the motion**: `ẋ = ∂H/∂p = p/m`, `ṗ = 0 = −∂H/∂x`. -/
theorem hasDerivAt_pos_movingFlow (t : ℝ) (z : MovingState L) :
    HasDerivAt (fun s => (movingFlow J ħ g hf m gd s z).pos) (z.mom / m) t
      ∧ HasDerivAt (motionEnergy m) (z.mom / m) z.mom := by
  refine ⟨?_, ?_⟩
  · have h := ((hasDerivAt_id t).const_mul (z.mom / m)).const_add z.pos
    simp only [id, mul_one] at h
    exact h
  · have h := (hasDerivAt_pow 2 z.mom).div_const (2 * m)
    unfold motionEnergy
    convert h using 1
    by_cases hm : m = 0
    · simp [hm]
    · field_simp
      ring

/-- **The device's site**: the cell its position occupies. Read from the position; the site index is
microscopic input. -/
noncomputable def siteOf (x : ℝ) : ℤ := ⌊x⌋

/-- ★★ **Transport through the sites**: moving at `v = p/m > 0`, the device occupies site `k` exactly
during `[(k − x)/v, (k + 1 − x)/v)`. -/
theorem siteOf_movingFlow_eq_iff {z : MovingState L} (hv : 0 < z.mom / m) (t : ℝ) (k : ℤ) :
    siteOf (movingFlow J ħ g hf m gd t z).pos = k
      ↔ ((k : ℝ) - z.pos) / (z.mom / m) ≤ t ∧ t < ((k : ℝ) + 1 - z.pos) / (z.mom / m) := by
  rw [siteOf, pos_movingFlow, Int.floor_eq_iff, div_le_iff₀ hv, lt_div_iff₀ hv]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- ★ **The device never moves back**: with `v ≥ 0` its site is non-decreasing in time. -/
theorem siteOf_movingFlow_mono {z : MovingState L} (hv : 0 ≤ z.mom / m) {s t : ℝ} (hst : s ≤ t) :
    siteOf (movingFlow J ħ g hf m gd s z).pos ≤ siteOf (movingFlow J ħ g hf m gd t z).pos := by
  rw [siteOf, siteOf, pos_movingFlow, pos_movingFlow]
  exact Int.floor_mono (by nlinarith)

/-- **The memory is retained during transport.** -/
theorem mem_movingFlow (t : ℝ) (z : MovingState L) : (movingFlow J ħ g hf m gd t z).mem = z.mem := rfl

/-- **The carried clock runs by its own flow, whatever the motion.** -/
theorem clock_movingFlow (t : ℝ) (z : MovingState L) :
    (movingFlow J ħ g hf m gd t z).clock = activeFlow J ħ g hf t z.clock := rfl

/-- ★★ **No time dilation in the control**: two devices carrying the same clock read the same at every
time, whatever their momenta. -/
theorem clock_movingFlow_indep {z z' : MovingState L} (h : z.clock = z'.clock) (t : ℝ) :
    (movingFlow J ħ g hf m gd t z).clock = (movingFlow J ħ g hf m gd t z').clock := by
  rw [clock_movingFlow, clock_movingFlow, h]

/-- ★★ **The carried clock keeps time during transport**: prepared as #201's hand clock, it reads
within `τ_tick + 1/(2ω)` of `t` over the horizon, whatever the device's momentum. -/
theorem abs_movingReading_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {z : MovingState L}
    (hz : z.clock = (msgPoint 1, q)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |handReading K (tickTime K (handRate J ħ g hf q)) (movingFlow J ħ g hf m gd t z).clock.2 - t|
      ≤ tickTime K (handRate J ħ g hf q) + 1 / (2 * handFreq J ħ g hf q) := by
  rw [clock_movingFlow, hz]
  exact abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht

/-- ★★ **A detector records the device's passage**: before the device reaches site `k` the site's
register is unchanged; once the device has crossed it, the register has advanced by exactly
`g_d · m / p`. -/
theorem det_movingFlow_passage {z : MovingState L} (hv : 0 < z.mom / m) (k : Fin L) {t : ℝ}
    (ht : 0 ≤ t) :
    (z.pos + z.mom / m * t < (k : ℕ) → (movingFlow J ħ g hf m gd t z).det k = z.det k)
      ∧ (z.pos < (k : ℕ) → ((k : ℕ) : ℝ) + 1 ≤ z.pos + z.mom / m * t →
          (movingFlow J ħ g hf m gd t z).det k = z.det k + gd * (z.mom / m)⁻¹) := by
  refine ⟨fun hb => ?_, fun hx hc => ?_⟩
  · show z.det k + gd * occTime ((k : ℕ) : ℤ) z.pos (z.mom / m) t = z.det k
    rw [occTime_eq_zero_of_before hv.le ht (by push_cast; linarith), mul_zero, add_zero]
  · show z.det k + gd * occTime ((k : ℕ) : ℤ) z.pos (z.mom / m) t = _
    rw [occTime_eq_inv_of_crossed hv (by exact_mod_cast hx) (by push_cast; linarith)]

/-- **A concrete moving instance**: mass `1`, momentum `1`, starting at the middle of site `0`, the
device is at site `0` at time `0`, at site `1` at time `1` and at site `2` at time `2`. -/
theorem movingFlow_instance (z : MovingState L) (hx : z.pos = 1 / 2) (hp : z.mom = 1) :
    siteOf (movingFlow J ħ g hf 1 gd 0 z).pos = 0 ∧ siteOf (movingFlow J ħ g hf 1 gd 1 z).pos = 1
      ∧ siteOf (movingFlow J ħ g hf 1 gd 2 z).pos = 2 := by
  simp only [siteOf, pos_movingFlow, hx, hp]
  norm_num [Int.floor_eq_iff]

/-- ★★★ **The control candidate for a moving clock (#241).** One autonomous evolution — the free
flow of the device's momentum, the activated flow of its hand clock, stationary detectors driven by
its occupancy — in which the device is transported through the sites in order, never moves back,
keeps its memory, keeps time by its own flow within `τ_tick + 1/(2ω)` whatever its momentum, reads
the same as an identical clock at rest at every time, and is recorded by each detector it passes:
nothing before arrival, exactly `g_d m / p` after crossing. -/
theorem moving_clock_control (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {z : MovingState L}
    (hz : z.clock = (msgPoint 1, q)) (hv : 0 < z.mom / m) :
    (∀ s t, movingFlow J ħ g hf m gd (s + t)
      = (movingFlow J ħ g hf m gd t ∘ movingFlow J ħ g hf m gd s : MovingState L → MovingState L))
    ∧ (∀ t (k : ℤ), siteOf (movingFlow J ħ g hf m gd t z).pos = k
        ↔ ((k : ℝ) - z.pos) / (z.mom / m) ≤ t ∧ t < ((k : ℝ) + 1 - z.pos) / (z.mom / m))
    ∧ (∀ s t, s ≤ t →
        siteOf (movingFlow J ħ g hf m gd s z).pos ≤ siteOf (movingFlow J ħ g hf m gd t z).pos)
    ∧ (∀ t, (movingFlow J ħ g hf m gd t z).mem = z.mem)
    ∧ (∀ t, 0 ≤ t → t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q) →
        |handReading K (tickTime K (handRate J ħ g hf q)) (movingFlow J ħ g hf m gd t z).clock.2 - t|
          ≤ tickTime K (handRate J ħ g hf q) + 1 / (2 * handFreq J ħ g hf q))
    ∧ (∀ (z' : MovingState L), z'.clock = z.clock → ∀ t,
        (movingFlow J ħ g hf m gd t z').clock = (movingFlow J ħ g hf m gd t z).clock)
    ∧ (∀ (k : Fin L) t, 0 ≤ t → z.pos < (k : ℕ) → ((k : ℕ) : ℝ) + 1 ≤ z.pos + z.mom / m * t →
        (movingFlow J ħ g hf m gd t z).det k = z.det k + gd * (z.mom / m)⁻¹) :=
  ⟨movingFlow_add J ħ g hf m gd, siteOf_movingFlow_eq_iff J ħ g hf m gd hv,
    fun _ _ hst => siteOf_movingFlow_mono J ħ g hf m gd hv.le hst,
    fun t => mem_movingFlow J ħ g hf m gd t z,
    fun _ ht0 ht => abs_movingReading_sub_le J ħ g hf m gd hJ hħ hK hq hκ hz ht0 ht,
    fun _ h t => clock_movingFlow_indep J ħ g hf m gd h t,
    fun k _ ht hx hc => (det_movingFlow_passage J ħ g hf m gd hv k ht).2 hx hc⟩

end Flow

end CSD.RecordLayer

end
