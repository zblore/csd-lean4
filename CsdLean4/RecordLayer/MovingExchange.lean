/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TwoObservers

/-!
# Two-way exchanges with the moving observer

**Category:** 7-SigmaLayer (the record layer). BACKLOG #244 (the author's fourth operational-geometry
brief, step 4), for the control candidate (A).

~~#243~~ put a stationary and a moving observer in one arena and read their relative speed from one
encounter. Here they **exchange signals at a distance**. The carrier is a messenger — a free particle
that **reflects elastically off the moving observer**. In the moving observer's frame the messenger's
position is `−|ρ + w t|`, with `ρ + w t` an **unfolded coordinate** that moves freely (the method of
images), so the flow with the reflections is still one autonomous flow with a group law. The first
observer's register counts the messenger's passages: one passage is the emission record, two the
return; the moving observer's register records the reception.

## Occupancy along a reflected path

* `siteInd_nonneg`, `siteInd_comp_intervalIntegrable'`, ★ `occTime_mono`;
  `occTime_eq_zero_of_before_neg`, ★★ `occTime_eq_inv_of_crossed_neg` — a device moving backwards
  across a site;
* `msgRel`, `continuous_msgRel`, `bounceOcc`, `msgRel_shift`, ★ `bounceOcc_add`,
  `bounceOcc_eq_occTime_of_le`, `bounceOcc_zero_eq_occTime`, ★ `measurable_bounceOcc`.

## One exchange

* `outSpeed` (`y + w`), `retSpeed` (`w − y`), `bounceTime`, `bounceSep`, `exchEmitStart`,
  `exchEmitEnd`, `exchReturnStart`, `exchReturnEnd`; `ExchGeom` — the geometry of an exchange, with
  its ordering lemmas;
* ★★ `ExchGeom.bounceOcc_before`, `ExchGeom.bounceOcc_between`, `ExchGeom.bounceOcc_le`,
  `ExchGeom.bounceOcc_after` — **the first observer's register through an exchange**: nothing before
  the emission, exactly `1/(y + w)` from the emission's completion until the return begins,
  `1/(y + w) + 1/(w − y)` after the return.

## The arena and the records

* `ExchArena` (two observers, `N` messengers, a register per messenger for each observer),
  `exchSep`, `exchSepVel`; ★★ `exchFlow` — **the exchange flow**; `exchSep_exchFlow`,
  `exchFlow_zero`, ★★ `exchFlow_add` (the group law, reflections included), `exchEvolve`,
  `exchEvolve_self`, `exchEvolve_comp`, ★ `measurable_exchFlow`; `regS_exchFlow`,
  ★★ `regM_exchFlow_received`;
* `passCount`, `emitLevel`, `returnLevel`; ★★★ `emissionWrite` — **the emission as an
  `ActualOccurrence`, retained only until the return begins** (a finite window, overwritten by the
  next record); ★★★ `returnWrite` — **the return**; `receiveRead`; ★★★ `receptionWrite` — **the
  reception at the moving observer**;
* ★★ `abs_restReading_sub_le`, `abs_movingObsReading_sub_le` — **the timestamps**: each observer's
  clock reads within its error at the completion of each write over its horizon;
* ★★ `elastic_exchange` — **the back-reaction of one bounce**: momentum and energy conserved, relative
  velocity reversed, the observer's velocity moved by at most `2(μ/m)|u − v|`, the messenger's
  outgoing velocity off the rigid mirror's by the same;
* ★★ `exchange_train`, `trainState`, `trainState_geom` — **repeated exchanges**: emissions over
  `[1/8 + k, 3/8 + k]`, returns over `[17/4 + 2k, 19/4 + 2k]` — emissions one unit apart return two
  apart, the Galilean Doppler factor of a receding mirror;
* ★★★ `moving_exchange` — the package.

## Honest scope

⚠️ **The moving observer is a rigid mirror in the flow.** A bounce's recoil is computed exactly by
`elastic_exchange` and is `O(μ/m)`; the flow is the `μ/m → 0` limit. Exchanges whose recoil
accumulates in the flow are #255.

⚠️ **The messengers are prepared upstream.** The first observer records each messenger's departure
from its window; it does not launch it. An observer that emits on its own clock's tick is #254.

⚠️ **The messengers pass through each other and through the observer at rest**, which only detects
them, and the detectors are test detectors (#251).

⚠️ **This is the control (A).** The messenger has no universal speed — its outward and return speeds
relative to the observer at rest are `y + w` and `w − y` — so the radar coordinates of #245 will
depend on the messenger's preparation: the expected negative result of the control. Exchanges on the
Dirac chain (B) are #256.

References: `specs/BACKLOG.md` #244, #243, #245, #251, #254, #255, #256, #212, #204, #39;
`RecordLayer/TwoObservers.lean` (`observerFlow`, `handClockErr`); `RecordLayer/MovingClock.lean`
(`occTime`, `occTime_add`, `occTime_eq_inv_of_crossed`); `RecordLayer/TransportedClock.lean`
(`measurable_occTime`); `RecordLayer/RecordOccurrence.lean` (`ActualOccurrence`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Occupancy along any path, and along a reflected one -/

theorem siteInd_nonneg (k : ℤ) (u : ℝ) : 0 ≤ siteInd k u := by
  unfold siteInd
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) u

theorem siteInd_comp_intervalIntegrable' (k : ℤ) {γ : ℝ → ℝ} (hγ : Measurable γ) (a b : ℝ) :
    IntervalIntegrable (fun s => siteInd k (γ s)) volume a b := by
  have hS : MeasurableSet (γ ⁻¹' Set.Ico (k : ℝ) (k + 1)) := hγ measurableSet_Ico
  have h : (fun s => siteInd k (γ s)) = (γ ⁻¹' Set.Ico (k : ℝ) (k + 1)).indicator (fun _ => (1 : ℝ)) := by
    funext s
    simp only [siteInd, Set.indicator, Set.mem_preimage]
  rw [h, intervalIntegrable_iff]
  exact (integrableOn_const (by simp [Real.volume_uIoc])).indicator hS

/-- ★ **Occupancy times are monotone in time.** -/
theorem occTime_mono (k : ℤ) (x v : ℝ) {s t : ℝ} (hst : s ≤ t) :
    occTime k x v s ≤ occTime k x v t := by
  rw [show t = s + (t - s) by ring, occTime_add]
  have : 0 ≤ occTime k (x + v * s) v (t - s) :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ => siteInd_nonneg k _
  linarith

/-- **Before a device moving backwards reaches site `k`, the site has seen nothing of it.** -/
theorem occTime_eq_zero_of_before_neg {k : ℤ} {x v t : ℝ} (hv : v ≤ 0) (ht : 0 ≤ t)
    (hbefore : (k : ℝ) + 1 ≤ x + v * t) : occTime k x v t = 0 := by
  unfold occTime
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_,
    intervalIntegral.integral_zero]
  rw [Set.uIcc_of_le ht] at hs
  have hle : x + v * t ≤ x + v * s := by nlinarith [hs.2]
  simp only [siteInd, Set.indicator, Set.mem_Ico]
  rw [ite_eq_right (by intro h; linarith [h.2])]

/-- ★★ **Once a device moving backwards has crossed site `k`, the site has seen it for exactly
`1/|v|`.** -/
theorem occTime_eq_inv_of_crossed_neg {k : ℤ} {x v t : ℝ} (hv : v < 0) (hx : (k : ℝ) + 1 ≤ x)
    (hcross : x + v * t ≤ k) : occTime k x v t = (-v)⁻¹ := by
  unfold occTime
  have hsub := intervalIntegral.integral_comp_mul_add (a := 0) (b := t)
    (fun u => siteInd k u) hv.ne x
  simp only [mul_zero, zero_add] at hsub
  rw [show (fun s => siteInd k (x + v * s)) = fun s => siteInd k (v * s + x) from
    funext fun s => by rw [add_comm], hsub, smul_eq_mul]
  have hb : v * t + x ≤ x := by linarith
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hb]
  have hint : ∫ u in Set.Ioc (v * t + x) x, siteInd k u = 1 := by
    simp only [siteInd]
    rw [integral_indicator_const _ measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico]
    have h1 : Set.Ioo (k : ℝ) (k + 1) ⊆ Set.Ico (k : ℝ) (k + 1) ∩ Set.Ioc (v * t + x) x :=
      fun u hu => ⟨⟨hu.1.le, hu.2⟩, by linarith [hu.1], by linarith [hu.2]⟩
    have h2 : Set.Ico (k : ℝ) (k + 1) ∩ Set.Ioc (v * t + x) x ⊆ Set.Ico (k : ℝ) (k + 1) :=
      Set.inter_subset_left
    have hm1 := measure_mono (μ := volume) h1
    have hm2 := measure_mono (μ := volume) h2
    rw [Real.volume_Ioo] at hm1
    rw [Real.volume_Ico] at hm2
    have he : volume (Set.Ico (k : ℝ) (k + 1) ∩ Set.Ioc (v * t + x) x) = ENNReal.ofReal 1 := by
      refine le_antisymm (by simpa using hm2) (by simpa using hm1)
    simp [Measure.real, he]
  rw [hint, mul_neg, mul_one, neg_inv]

/-- **The messenger's position relative to the observer at rest**, when the moving observer is at
`d + y s` relative to it and the messenger's unfolded coordinate relative to the moving observer is
`ρ + w s`: the reflected coordinate is `−|ρ + w s|`. -/
noncomputable def msgRel (d y ρ w s : ℝ) : ℝ := d + y * s - |ρ + w * s|

theorem continuous_msgRel (d y ρ w : ℝ) : Continuous (msgRel d y ρ w) := by
  unfold msgRel
  fun_prop

/-- **The time the reflected messenger spends within half a cell of the observer at rest.** -/
noncomputable def bounceOcc (d y ρ w t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, siteInd 0 (msgRel d y ρ w s + 1 / 2)

theorem msgRel_shift (d y ρ w s u : ℝ) :
    msgRel (d + y * s) y (ρ + w * s) w u = msgRel d y ρ w (s + u) := by
  unfold msgRel
  congr 1
  · ring
  · congr 1
    ring

/-- ★ **Occupancy along the reflected path adds along the motion.** -/
theorem bounceOcc_add (d y ρ w s t : ℝ) :
    bounceOcc d y ρ w (s + t) = bounceOcc d y ρ w s + bounceOcc (d + y * s) y (ρ + w * s) w t := by
  have hm : Measurable fun u => msgRel d y ρ w u + 1 / 2 :=
    ((continuous_msgRel d y ρ w).add continuous_const).measurable
  unfold bounceOcc
  rw [← intervalIntegral.integral_add_adjacent_intervals (siteInd_comp_intervalIntegrable' 0 hm 0 s)
    (siteInd_comp_intervalIntegrable' 0 hm s (s + t))]
  congr 1
  have h := intervalIntegral.integral_comp_add_right
    (fun u => siteInd 0 (msgRel d y ρ w u + 1 / 2)) (a := 0) (b := t) s
  rw [zero_add, add_comm t s] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [msgRel_shift, add_comm u s]

/-- **Before the bounce the messenger moves uniformly** at `y + w` relative to the observer at rest. -/
theorem bounceOcc_eq_occTime_of_le {d y ρ w t : ℝ} (hw : 0 ≤ w) (ht : 0 ≤ t) (hτ : ρ + w * t ≤ 0) :
    bounceOcc d y ρ w t = occTime 0 (d + ρ + 1 / 2) (y + w) t := by
  unfold bounceOcc occTime
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht] at hs
  have : ρ + w * s ≤ 0 := by nlinarith [hs.2]
  simp only [msgRel, abs_of_nonpos this]
  congr 1
  ring

/-- **After the bounce it moves uniformly** at `y − w`, from the moving observer's position. -/
theorem bounceOcc_zero_eq_occTime {d y w t : ℝ} (hw : 0 ≤ w) (ht : 0 ≤ t) :
    bounceOcc d y 0 w t = occTime 0 (d + 1 / 2) (y - w) t := by
  unfold bounceOcc occTime
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht] at hs
  have : 0 ≤ 0 + w * s := by nlinarith [hs.1]
  simp only [msgRel, abs_of_nonneg this]
  congr 1
  ring

/-- ★ **The reflected occupancy is measurable** in the separation, its rate, and the messenger's
unfolded coordinate and speed. -/
theorem measurable_bounceOcc (t : ℝ) :
    Measurable fun z : ℝ × ℝ × ℝ × ℝ => bounceOcc z.1 z.2.1 z.2.2.1 z.2.2.2 t := by
  have hF : StronglyMeasurable (Function.uncurry fun (z : ℝ × ℝ × ℝ × ℝ) (s : ℝ) =>
      siteInd 0 (msgRel z.1 z.2.1 z.2.2.1 z.2.2.2 s + 1 / 2)) := by
    refine Measurable.stronglyMeasurable ?_
    have h : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
        msgRel p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 + 1 / 2 := by
      unfold msgRel
      fun_prop
    exact (measurable_const.indicator measurableSet_Ico).comp h
  have h1 := (hF.integral_prod_right (ν := volume.restrict (Ioc 0 t))).measurable
  have h2 := (hF.integral_prod_right (ν := volume.restrict (Ioc t 0))).measurable
  have : (fun z : ℝ × ℝ × ℝ × ℝ => bounceOcc z.1 z.2.1 z.2.2.1 z.2.2.2 t)
      = fun z => (∫ s in Ioc 0 t, siteInd 0 (msgRel z.1 z.2.1 z.2.2.1 z.2.2.2 s + 1 / 2))
          - ∫ s in Ioc t 0, siteInd 0 (msgRel z.1 z.2.1 z.2.2.1 z.2.2.2 s + 1 / 2) := by
    funext z
    rfl
  rw [this]
  exact h1.sub h2

/-! ### One exchange: its times and the observer's register -/

/-- The messenger's speed away from the observer at rest before the bounce, `y + w`. -/
def outSpeed (y w : ℝ) : ℝ := y + w

/-- Its speed back towards the observer at rest after the bounce, `w − y`. -/
def retSpeed (y w : ℝ) : ℝ := w - y

/-- The time of the bounce, when the unfolded coordinate crosses zero. -/
noncomputable def bounceTime (ρ w : ℝ) : ℝ := -ρ / w

/-- The separation of the two observers at the bounce. -/
noncomputable def bounceSep (d y ρ w : ℝ) : ℝ := d + y * bounceTime ρ w

/-- The messenger enters the observer's window. -/
noncomputable def exchEmitStart (d y ρ w : ℝ) : ℝ := (-(1 / 2) - (d + ρ)) / outSpeed y w

/-- It leaves the window outwards. -/
noncomputable def exchEmitEnd (d y ρ w : ℝ) : ℝ := (1 / 2 - (d + ρ)) / outSpeed y w

/-- It re-enters the window on its way back. -/
noncomputable def exchReturnStart (d y ρ w : ℝ) : ℝ :=
  bounceTime ρ w + (bounceSep d y ρ w - 1 / 2) / retSpeed y w

/-- It leaves the window, returned. -/
noncomputable def exchReturnEnd (d y ρ w : ℝ) : ℝ :=
  bounceTime ρ w + (bounceSep d y ρ w + 1 / 2) / retSpeed y w

/-- **The geometry of one exchange**: the messenger approaches the moving observer (`w > 0`), moves
away from the observer at rest before the bounce and back towards it after (`y + w > 0`,
`w − y > 0`), starts upstream of the observer at rest and more than half a cell short of the moving
one, and the moving observer is beyond the window of the one at rest when the bounce happens. -/
structure ExchGeom (d y ρ w : ℝ) : Prop where
  w_pos : 0 < w
  out_pos : 0 < outSpeed y w
  ret_pos : 0 < retSpeed y w
  upstream : d + ρ < -(1 / 2)
  behind : ρ < -(1 / 2)
  beyond : 1 / 2 ≤ bounceSep d y ρ w

namespace ExchGeom

variable {d y ρ w : ℝ} (h : ExchGeom d y ρ w)
include h

theorem bounceTime_nonneg : 0 ≤ bounceTime ρ w :=
  div_nonneg (by linarith [h.behind]) h.w_pos.le

theorem rho_add_bounce : ρ + w * bounceTime ρ w = 0 := by
  rw [bounceTime]
  field_simp [h.w_pos.ne']
  ring

theorem start_add_bounce : d + ρ + 1 / 2 + outSpeed y w * bounceTime ρ w = bounceSep d y ρ w + 1 / 2 := by
  have := h.rho_add_bounce
  rw [bounceSep, outSpeed]
  linarith

theorem emitStart_nonneg : 0 ≤ exchEmitStart d y ρ w :=
  div_nonneg (by linarith [h.upstream]) h.out_pos.le

theorem emitStart_le_emitEnd : exchEmitStart d y ρ w ≤ exchEmitEnd d y ρ w :=
  div_le_div_of_nonneg_right (by linarith) h.out_pos.le

theorem emitEnd_le_bounceTime : exchEmitEnd d y ρ w ≤ bounceTime ρ w := by
  rw [exchEmitEnd, div_le_iff₀ h.out_pos]
  linarith [h.start_add_bounce, h.beyond]

theorem bounceTime_le_returnStart : bounceTime ρ w ≤ exchReturnStart d y ρ w := by
  rw [exchReturnStart]
  have := div_nonneg (by linarith [h.beyond] : 0 ≤ bounceSep d y ρ w - 1 / 2) h.ret_pos.le
  linarith

theorem returnStart_le_returnEnd : exchReturnStart d y ρ w ≤ exchReturnEnd d y ρ w := by
  rw [exchReturnStart, exchReturnEnd]
  have := div_le_div_of_nonneg_right (by linarith : bounceSep d y ρ w - 1 / 2 ≤ bounceSep d y ρ w + 1 / 2)
    h.ret_pos.le
  linarith

/-- Before the bounce, the observer's register sees a uniform passage. -/
theorem bounceOcc_of_le {t : ℝ} (ht : 0 ≤ t) (htτ : t ≤ bounceTime ρ w) :
    bounceOcc d y ρ w t = occTime 0 (d + ρ + 1 / 2) (outSpeed y w) t :=
  bounceOcc_eq_occTime_of_le h.w_pos.le ht (by nlinarith [h.rho_add_bounce, h.w_pos])

/-- After the bounce, the outward passage is complete and the return is a uniform passage back. -/
theorem bounceOcc_of_ge {t : ℝ} (htτ : bounceTime ρ w ≤ t) :
    bounceOcc d y ρ w t = (outSpeed y w)⁻¹
      + occTime 0 (bounceSep d y ρ w + 1 / 2) (-retSpeed y w) (t - bounceTime ρ w) := by
  rw [show t = bounceTime ρ w + (t - bounceTime ρ w) by ring, bounceOcc_add, h.rho_add_bounce,
    h.bounceOcc_of_le h.bounceTime_nonneg le_rfl, bounceOcc_zero_eq_occTime h.w_pos.le (by linarith),
    occTime_eq_inv_of_crossed h.out_pos (by push_cast; linarith [h.upstream])
      (by push_cast; linarith [h.start_add_bounce, h.beyond])]
  simp only [add_sub_cancel_left, bounceSep, retSpeed, neg_sub]

/-- ★★ **The register before the emission**: nothing. -/
theorem bounceOcc_before {t : ℝ} (ht : 0 ≤ t) (hte : t < exchEmitStart d y ρ w) :
    bounceOcc d y ρ w t = 0 := by
  rw [h.bounceOcc_of_le ht (hte.le.trans (h.emitStart_le_emitEnd.trans h.emitEnd_le_bounceTime))]
  refine occTime_eq_zero_of_before h.out_pos.le ht ?_
  rw [exchEmitStart, lt_div_iff₀ h.out_pos] at hte
  push_cast
  linarith

/-- ★★ **The register between emission and return**: exactly one passage, `1/(y + w)`. -/
theorem bounceOcc_between {t : ℝ} (h1 : exchEmitEnd d y ρ w ≤ t) (h2 : t ≤ exchReturnStart d y ρ w) :
    bounceOcc d y ρ w t = (outSpeed y w)⁻¹ := by
  have ht0 : 0 ≤ t := h.emitStart_nonneg.trans (h.emitStart_le_emitEnd.trans h1)
  rcases le_total t (bounceTime ρ w) with hτ | hτ
  · rw [h.bounceOcc_of_le ht0 hτ]
    refine occTime_eq_inv_of_crossed h.out_pos (by push_cast; linarith [h.upstream]) ?_
    rw [exchEmitEnd, div_le_iff₀ h.out_pos] at h1
    push_cast
    linarith
  · rw [h.bounceOcc_of_ge hτ, occTime_eq_zero_of_before_neg (by linarith [h.ret_pos]) (by linarith),
      add_zero]
    rw [exchReturnStart] at h2
    have h3 : t - bounceTime ρ w ≤ (bounceSep d y ρ w - 1 / 2) / retSpeed y w := by linarith
    rw [le_div_iff₀ h.ret_pos] at h3
    push_cast
    linarith

/-- **Until the return, the register holds at most one passage.** -/
theorem bounceOcc_le {t : ℝ} (ht : 0 ≤ t) (h2 : t ≤ exchReturnStart d y ρ w) :
    bounceOcc d y ρ w t ≤ (outSpeed y w)⁻¹ := by
  rcases le_total t (exchEmitEnd d y ρ w) with h1 | h1
  · rw [h.bounceOcc_of_le ht (h1.trans h.emitEnd_le_bounceTime),
      ← h.bounceOcc_between le_rfl (h.emitEnd_le_bounceTime.trans h.bounceTime_le_returnStart),
      h.bounceOcc_of_le (h.emitStart_nonneg.trans h.emitStart_le_emitEnd) h.emitEnd_le_bounceTime]
    exact occTime_mono 0 _ _ h1
  · exact (h.bounceOcc_between h1 h2).le

/-- ★★ **The register after the return**: two passages, `1/(y + w) + 1/(w − y)`. -/
theorem bounceOcc_after {t : ℝ} (h3 : exchReturnEnd d y ρ w ≤ t) :
    bounceOcc d y ρ w t = (outSpeed y w)⁻¹ + (retSpeed y w)⁻¹ := by
  have hτ : bounceTime ρ w ≤ t :=
    h.bounceTime_le_returnStart.trans (h.returnStart_le_returnEnd.trans h3)
  rw [h.bounceOcc_of_ge hτ, occTime_eq_inv_of_crossed_neg (by linarith [h.ret_pos])
    (by push_cast; linarith [h.beyond]) ?_, neg_neg]
  rw [exchReturnEnd] at h3
  have h4 : (bounceSep d y ρ w + 1 / 2) / retSpeed y w ≤ t - bounceTime ρ w := by linarith
  rw [div_le_iff₀ h.ret_pos] at h4
  push_cast
  linarith

end ExchGeom

/-! ### The arena: two observers and `N` messengers -/

/-- **The exchange arena**: the observer at rest, the moving observer, `N` messengers (each its
unfolded coordinate and speed relative to the moving observer), the first observer's register for
each messenger, and the moving observer's. -/
abbrev ExchArena (N : ℕ) : Type :=
  ObsArena × ObsArena × (Fin N → ℝ × ℝ) × (Fin N → ℝ) × (Fin N → ℝ)

variable {N : ℕ}

/-- The separation of the moving observer from the first. -/
def exchSep (x : ExchArena N) : ℝ := x.2.1.2.1.1 - x.1.2.1.1

/-- Its rate. -/
noncomputable def exchSepVel (m : ℝ) (x : ExchArena N) : ℝ := x.2.1.2.1.2 / m - x.1.2.1.2 / m

section Flow

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- ★★ **The exchange flow**: each observer by its own flow; each messenger's unfolded coordinate
moves freely, its physical position relative to the moving observer being `−|ρ + w t|` — **it
reflects off the moving observer**; the first observer's register advances while the messenger is
within half a cell of it, the moving observer's while the messenger is within half a cell of it. -/
noncomputable def exchFlow (t : ℝ) (x : ExchArena N) : ExchArena N :=
  (observerFlow J ħ g hf m t x.1, observerFlow J ħ g hf m t x.2.1,
    fun k => ((x.2.2.1 k).1 + (x.2.2.1 k).2 * t, (x.2.2.1 k).2),
    fun k => x.2.2.2.1 k
      + gd * bounceOcc (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 t,
    fun k => x.2.2.2.2 k + gd * occTime 0 ((x.2.2.1 k).1 + 1 / 2) (x.2.2.1 k).2 t)

theorem exchSep_exchFlow (t : ℝ) (x : ExchArena N) :
    exchSep (exchFlow J ħ g hf m gd t x) = exchSep x + exchSepVel m x * t := by
  simp only [exchSep, exchSepVel, exchFlow, observerFlow]
  ring

theorem exchFlow_zero : exchFlow J ħ g hf m gd 0 = (id : ExchArena N → ExchArena N) := by
  funext x
  simp only [exchFlow, observerFlow_zero, bounceOcc, occTime, intervalIntegral.integral_same,
    mul_zero, add_zero, id]

/-- ★★ **The group law**: one autonomous evolution, the reflections included. -/
theorem exchFlow_add (s t : ℝ) :
    exchFlow J ħ g hf m gd (s + t)
      = (exchFlow J ħ g hf m gd t ∘ exchFlow J ħ g hf m gd s : ExchArena N → ExchArena N) := by
  funext x
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp only [exchFlow, Function.comp, observerFlow_add]
  · simp only [exchFlow, Function.comp, observerFlow_add]
  · funext k
    simp only [exchFlow, Function.comp]
    exact Prod.ext (by ring) rfl
  · funext k
    show x.2.2.2.1 k + gd * bounceOcc (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 (s + t)
      = x.2.2.2.1 k + gd * bounceOcc (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 s
        + gd * bounceOcc (exchSep (exchFlow J ħ g hf m gd s x)) (exchSepVel m x)
          ((x.2.2.1 k).1 + (x.2.2.1 k).2 * s) (x.2.2.1 k).2 t
    rw [exchSep_exchFlow, bounceOcc_add]
    ring
  · funext k
    show x.2.2.2.2 k + gd * occTime 0 ((x.2.2.1 k).1 + 1 / 2) (x.2.2.1 k).2 (s + t)
      = x.2.2.2.2 k + gd * occTime 0 ((x.2.2.1 k).1 + 1 / 2) (x.2.2.1 k).2 s
        + gd * occTime 0 ((x.2.2.1 k).1 + (x.2.2.1 k).2 * s + 1 / 2) (x.2.2.1 k).2 t
    rw [occTime_add, show (x.2.2.1 k).1 + 1 / 2 + (x.2.2.1 k).2 * s
      = (x.2.2.1 k).1 + (x.2.2.1 k).2 * s + 1 / 2 by ring]
    ring

/-- The two-time evolution. -/
noncomputable def exchEvolve (s t : OnticTime) : ExchArena N → ExchArena N :=
  exchFlow J ħ g hf m gd (t - s)

theorem exchEvolve_self (t : OnticTime) :
    exchEvolve J ħ g hf m gd t t = (id : ExchArena N → ExchArena N) := by
  rw [exchEvolve, sub_self, exchFlow_zero]

theorem exchEvolve_comp (s t u : OnticTime) :
    exchEvolve J ħ g hf m gd t u ∘ exchEvolve J ħ g hf m gd s t
      = (exchEvolve J ħ g hf m gd s u : ExchArena N → ExchArena N) := by
  rw [exchEvolve, exchEvolve, exchEvolve, ← exchFlow_add]
  congr 1
  ring

theorem measurable_msg (k : Fin N) : Measurable fun x : ExchArena N => x.2.2.1 k :=
  (measurable_pi_apply k).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))

theorem measurable_regS (k : Fin N) : Measurable fun x : ExchArena N => x.2.2.2.1 k :=
  (measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_regM (k : Fin N) : Measurable fun x : ExchArena N => x.2.2.2.2 k :=
  (measurable_pi_apply k).comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

/-- ★ **Each step of the exchange flow is measurable.** -/
theorem measurable_exchFlow (hf1 : ContDiff ℝ 1 f) (t : ℝ) :
    Measurable (exchFlow (N := N) J ħ g hf m gd t) := by
  have hS : Measurable fun x : ExchArena N => exchSep x := by
    unfold exchSep
    fun_prop
  have hV : Measurable fun x : ExchArena N => exchSepVel m x := by
    unfold exchSepVel
    fun_prop
  refine ((measurable_observerFlow J ħ g hf m hf1 t).comp measurable_fst).prodMk
    (((measurable_observerFlow J ħ g hf m hf1 t).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_iff.2 fun k => ?_).prodMk
        ((measurable_pi_iff.2 fun k => ?_).prodMk (measurable_pi_iff.2 fun k => ?_))))
  · have hk := measurable_msg (N := N) k
    exact (hk.fst.add (hk.snd.mul_const t)).prodMk hk.snd
  · have hk := measurable_msg (N := N) k
    have hb := (measurable_bounceOcc t).comp (hS.prodMk (hV.prodMk (hk.fst.prodMk hk.snd)))
    exact (measurable_regS k).add (hb.const_mul gd)
  · have hk := measurable_msg (N := N) k
    have ho := (measurable_occTime 0 t).comp ((hk.fst.add_const (1 / 2)).prodMk hk.snd)
    exact (measurable_regM k).add (ho.const_mul gd)

theorem regS_exchFlow (k : Fin N) (t : ℝ) (x : ExchArena N) :
    (exchFlow J ħ g hf m gd t x).2.2.2.1 k
      = x.2.2.2.1 k + gd * bounceOcc (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 t :=
  rfl

/-- ★★ **The reception, as the moving observer's register sees it**: once the messenger has bounced
and left its window, the register has advanced by exactly `g_d / w`. -/
theorem regM_exchFlow_received {x : ExchArena N} (k : Fin N) (hw : 0 < (x.2.2.1 k).2)
    (hρ : (x.2.2.1 k).1 < -(1 / 2)) {t : ℝ} (ht : 1 / 2 ≤ (x.2.2.1 k).1 + (x.2.2.1 k).2 * t) :
    (exchFlow J ħ g hf m gd t x).2.2.2.2 k = x.2.2.2.2 k + gd * ((x.2.2.1 k).2)⁻¹ := by
  show x.2.2.2.2 k + gd * occTime 0 ((x.2.2.1 k).1 + 1 / 2) (x.2.2.1 k).2 t = _
  rw [occTime_eq_inv_of_crossed hw (by push_cast; linarith) (by push_cast; linarith)]

/-! ### The three records -/

/-- **The first observer's passage count**: `2` once the register holds two passages' worth, `1`
once it holds one. -/
noncomputable def passCount (θ₁ θ₂ : ℝ) (k : Fin N) (x : ExchArena N) : ℕ :=
  if θ₂ ≤ x.2.2.2.1 k then 2 else if θ₁ ≤ x.2.2.2.1 k then 1 else 0

theorem measurable_passCount (θ₁ θ₂ : ℝ) (k : Fin N) : Measurable (passCount (N := N) θ₁ θ₂ k) := by
  refine Measurable.ite (measurableSet_le measurable_const (measurable_regS k)) measurable_const
    (Measurable.ite (measurableSet_le measurable_const (measurable_regS k)) measurable_const
      measurable_const)

/-- The emission threshold: one outward passage. -/
noncomputable def emitLevel (y w : ℝ) : ℝ := gd * (outSpeed y w)⁻¹

/-- The return threshold: an outward and a return passage. -/
noncomputable def returnLevel (y w : ℝ) : ℝ := gd * ((outSpeed y w)⁻¹ + (retSpeed y w)⁻¹)

theorem emitLevel_lt_returnLevel {y w : ℝ} (hgd : 0 < gd) (hb : 0 < retSpeed y w) :
    emitLevel gd y w < returnLevel gd y w := by
  rw [emitLevel, returnLevel]
  have := inv_pos.2 hb
  nlinarith

/-- ★★★ **The emission as an actual occurrence**: the first observer's count reaches `1` as the
messenger leaves its window outwards and **holds only until the return begins** — a record with a
finite retention, overwritten by the next. -/
noncomputable def emissionWrite (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (site : Finset (Fin K)) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.1 k = 0)
    (hG : ExchGeom (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2) :
    ActualOccurrence (ExchArena N) ℕ K where
  evolve := exchEvolve J ħ g hf m gd
  evolve_self := exchEvolve_self J ħ g hf m gd
  evolve_comp := exchEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_exchFlow J ħ g hf m gd hf1 (t - s)
  readout := passCount (emitLevel gd (exchSepVel m x₀) (x₀.2.2.1 k).2)
    (returnLevel gd (exchSepVel m x₀) (x₀.2.2.1 k).2) k
  measurable_readout := measurable_passCount _ _ k
  ready := {x | x.2.2.2.1 k = 0}
  measurableSet_ready := measurableSet_eq_fun (measurable_regS k) measurable_const
  prep := x₀
  prep_mem := hreg
  site := site
  start := 0
  value := 1
  writeStart := exchEmitStart (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2
  writeEnd := exchEmitEnd (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2
  window := exchReturnStart (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2
    - exchEmitEnd (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2
  isWrite :=
    { start_le := hG.emitStart_nonneg
      interval := hG.emitStart_le_emitEnd
      window_nonneg := by linarith [hG.emitEnd_le_bounceTime, hG.bounceTime_le_returnStart]
      before := fun t ht0 ht => by
        have h1 := emitLevel_lt_returnLevel gd hgd hG.ret_pos
        have h0 : 0 < emitLevel gd (exchSepVel m x₀) (x₀.2.2.1 k).2 :=
          mul_pos hgd (inv_pos.2 hG.out_pos)
        show passCount _ _ k (exchFlow J ħ g hf m gd (t - 0) x₀) ≠ 1
        rw [sub_zero, passCount, regS_exchFlow, hreg, hG.bounceOcc_before ht0 ht, mul_zero,
          add_zero, ite_eq_right (by intro h; linarith), ite_eq_right (by intro h; linarith)]
        decide
      holds := fun t ht₁ ht₂ => by
        have h1 := emitLevel_lt_returnLevel gd hgd hG.ret_pos
        show passCount _ _ k (exchFlow J ħ g hf m gd (t - 0) x₀) = 1
        rw [sub_zero, passCount, regS_exchFlow, hreg, hG.bounceOcc_between ht₁ (by linarith),
          zero_add, ← emitLevel, ite_eq_right (by intro h; linarith), ite_eq_left le_rfl] }

/-- ★★★ **The return as an actual occurrence**: the first observer's count reaches `2` as the
returned messenger leaves its window, and holds. -/
noncomputable def returnWrite (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (site : Finset (Fin K)) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.1 k = 0)
    (hG : ExchGeom (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2) :
    ActualOccurrence (ExchArena N) ℕ K where
  evolve := exchEvolve J ħ g hf m gd
  evolve_self := exchEvolve_self J ħ g hf m gd
  evolve_comp := exchEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_exchFlow J ħ g hf m gd hf1 (t - s)
  readout := passCount (emitLevel gd (exchSepVel m x₀) (x₀.2.2.1 k).2)
    (returnLevel gd (exchSepVel m x₀) (x₀.2.2.1 k).2) k
  measurable_readout := measurable_passCount _ _ k
  ready := {x | x.2.2.2.1 k = 0}
  measurableSet_ready := measurableSet_eq_fun (measurable_regS k) measurable_const
  prep := x₀
  prep_mem := hreg
  site := site
  start := 0
  value := 2
  writeStart := exchReturnStart (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2
  writeEnd := exchReturnEnd (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2
  window := 1
  isWrite :=
    { start_le := hG.emitStart_nonneg.trans (hG.emitStart_le_emitEnd.trans
        (hG.emitEnd_le_bounceTime.trans hG.bounceTime_le_returnStart))
      interval := hG.returnStart_le_returnEnd
      window_nonneg := zero_le_one
      before := fun t ht0 ht => by
        have h1 := emitLevel_lt_returnLevel gd hgd hG.ret_pos
        have hle := hG.bounceOcc_le ht0 ht.le
        have hle' : gd * bounceOcc (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2 t
            ≤ emitLevel gd (exchSepVel m x₀) (x₀.2.2.1 k).2 :=
          mul_le_mul_of_nonneg_left hle hgd.le
        show passCount _ _ k (exchFlow J ħ g hf m gd (t - 0) x₀) ≠ 2
        rw [sub_zero, passCount, regS_exchFlow, hreg, zero_add, ite_eq_right (by intro h; linarith)]
        split_ifs <;> decide
      holds := fun t ht₁ _ => by
        show passCount _ _ k (exchFlow J ħ g hf m gd (t - 0) x₀) = 2
        rw [sub_zero, passCount, regS_exchFlow, hreg, hG.bounceOcc_after ht₁, zero_add,
          ← returnLevel, ite_eq_left le_rfl] }

/-- The moving observer's reception readout: whether its register has reached `θ`. -/
noncomputable def receiveRead (θ : ℝ) (k : Fin N) (x : ExchArena N) : ℕ :=
  if θ ≤ x.2.2.2.2 k then 1 else 0

theorem measurable_receiveRead (θ : ℝ) (k : Fin N) : Measurable (receiveRead (N := N) θ k) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_regM k)) measurable_const
    measurable_const

/-- ★★★ **The reception as an actual occurrence**: the moving observer's register, prepared at zero
with threshold `0 < θ ≤ g_d / w`, is written as the messenger bounces off it. -/
noncomputable def receptionWrite (hf1 : ContDiff ℝ 1 f) {K : ℕ} (site : Finset (Fin K)) (θ : ℝ)
    (hθ0 : 0 < θ) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.2 k = 0) (hw : 0 < (x₀.2.2.1 k).2)
    (hρ : (x₀.2.2.1 k).1 < -(1 / 2)) (hθ : θ ≤ gd * ((x₀.2.2.1 k).2)⁻¹) :
    ActualOccurrence (ExchArena N) ℕ K where
  evolve := exchEvolve J ħ g hf m gd
  evolve_self := exchEvolve_self J ħ g hf m gd
  evolve_comp := exchEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_exchFlow J ħ g hf m gd hf1 (t - s)
  readout := receiveRead θ k
  measurable_readout := measurable_receiveRead θ k
  ready := {x | x.2.2.2.2 k = 0}
  measurableSet_ready := measurableSet_eq_fun (measurable_regM k) measurable_const
  prep := x₀
  prep_mem := hreg
  site := site
  start := 0
  value := 1
  writeStart := (-(1 / 2) - (x₀.2.2.1 k).1) / (x₀.2.2.1 k).2
  writeEnd := (1 / 2 - (x₀.2.2.1 k).1) / (x₀.2.2.1 k).2
  window := 1 / (x₀.2.2.1 k).2
  isWrite :=
    { start_le := div_nonneg (by linarith) hw.le
      interval := div_le_div_of_nonneg_right (by linarith) hw.le
      window_nonneg := by positivity
      before := fun t ht0 ht => by
        rw [lt_div_iff₀ hw] at ht
        show receiveRead θ k (exchFlow J ħ g hf m gd (t - 0) x₀) ≠ 1
        rw [sub_zero, receiveRead]
        show (if θ ≤ x₀.2.2.2.2 k + gd * occTime 0 ((x₀.2.2.1 k).1 + 1 / 2) (x₀.2.2.1 k).2 t
          then 1 else 0) ≠ 1
        rw [occTime_eq_zero_of_before hw.le ht0 (by push_cast; linarith), hreg, mul_zero,
          add_zero, ite_eq_right (by intro h; linarith)]
        decide
      holds := fun t ht₁ _ => by
        rw [div_le_iff₀ hw] at ht₁
        show receiveRead θ k (exchFlow J ħ g hf m gd (t - 0) x₀) = 1
        rw [sub_zero, receiveRead, regM_exchFlow_received J ħ g hf m gd k hw hρ (by linarith), hreg,
          zero_add, ite_eq_left hθ] }

/-! ### Timestamps, and the back-reaction of a bounce -/

/-- ★★ **The first observer's timestamps**: its clock read at any time of the horizon, in particular
at the completion of an emission or a return, is within its clock error of that time. -/
theorem abs_restReading_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {x : ExchArena N}
    (hx : x.1.1 = (msgPoint 1, q)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |handReading K (tickTime K (handRate J ħ g hf q)) (exchFlow J ħ g hf m gd t x).1.1.2 - t|
      ≤ handClockErr J ħ g hf K q := by
  show |handReading K (tickTime K (handRate J ħ g hf q)) (activeFlow J ħ g hf t x.1.1).2 - t| ≤ _
  rw [hx]
  exact abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht

/-- ★★ **The moving observer's timestamps**, likewise. -/
theorem abs_movingObsReading_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {x : ExchArena N}
    (hx : x.2.1.1 = (msgPoint 1, q)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |handReading K (tickTime K (handRate J ħ g hf q)) (exchFlow J ħ g hf m gd t x).2.1.1.2 - t|
      ≤ handClockErr J ħ g hf K q := by
  show |handReading K (tickTime K (handRate J ħ g hf q)) (activeFlow J ħ g hf t x.2.1.1).2 - t| ≤ _
  rw [hx]
  exact abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht

end Flow

/-- ★★ **The back-reaction of one bounce**: an elastic exchange between a messenger of mass `μ` at
velocity `u` and an observer of mass `m` at velocity `v` conserves momentum and energy and reverses
the relative velocity; the observer's velocity moves by at most `2(μ/m)|u − v|`, and the messenger's
outgoing velocity differs from the rigid mirror's `2v − u` by the same. The exchange flow is the
rigid-mirror limit `μ/m → 0`. -/
theorem elastic_exchange {μ m u v : ℝ} (hμ : 0 < μ) (hm : 0 < m) :
    let u' := ((μ - m) * u + 2 * m * v) / (μ + m)
    let v' := ((m - μ) * v + 2 * μ * u) / (μ + m)
    μ * u' + m * v' = μ * u + m * v
      ∧ μ * u' ^ 2 + m * v' ^ 2 = μ * u ^ 2 + m * v ^ 2
      ∧ u' - v' = -(u - v)
      ∧ |v' - v| ≤ 2 * (μ / m) * |u - v|
      ∧ |u' - (2 * v - u)| ≤ 2 * (μ / m) * |u - v| := by
  intro u' v'
  have hs : 0 < μ + m := by linarith
  have hv : v' - v = 2 * μ / (μ + m) * (u - v) := by
    simp only [v']
    field_simp
    ring
  have hu : u' - (2 * v - u) = 2 * μ / (μ + m) * (u - v) := by
    simp only [u']
    field_simp
    ring
  have hb : |2 * μ / (μ + m) * (u - v)| ≤ 2 * (μ / m) * |u - v| := by
    rw [abs_mul, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hμ.le hm (by linarith)) zero_le_two
  refine ⟨?_, ?_, ?_, hv ▸ hb, hu ▸ hb⟩
  · simp only [u', v']
    field_simp
    ring
  · simp only [u', v']
    field_simp
    ring
  · simp only [u', v']
    field_simp
    ring

/-! ### Repeated exchanges -/

/-- ★★ **A concrete train of exchanges**: the observer at rest at `0`, the moving observer at `4`
receding at `1`, messenger `k` starting at `−1 − 4k` at speed `4` (unfolded coordinate `−5 − 4k`
and speed `3` relative to the moving observer). Every exchange has the stated geometry; messenger
`k`'s emission is written over `[1/8 + k, 3/8 + k]` and its return over `[17/4 + 2k, 19/4 + 2k]` —
**emissions one unit apart return two units apart**, the Galilean Doppler factor `(w + v)/(w − v)`
of a receding mirror. -/
theorem exchange_train (k : ℝ) (hk : 0 ≤ k) :
    ExchGeom 4 1 (-5 - 4 * k) 3
      ∧ exchEmitStart 4 1 (-5 - 4 * k) 3 = 1 / 8 + k ∧ exchEmitEnd 4 1 (-5 - 4 * k) 3 = 3 / 8 + k
      ∧ exchReturnStart 4 1 (-5 - 4 * k) 3 = 17 / 4 + 2 * k
      ∧ exchReturnEnd 4 1 (-5 - 4 * k) 3 = 19 / 4 + 2 * k := by
  refine ⟨⟨by norm_num, by norm_num [outSpeed], by norm_num [retSpeed], by linarith, by linarith,
      ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [bounceSep, bounceTime]
    linarith
  · simp only [exchEmitStart, outSpeed]
    ring
  · simp only [exchEmitEnd, outSpeed]
    ring
  · simp only [exchReturnStart, bounceSep, bounceTime, retSpeed]
    ring
  · simp only [exchReturnEnd, bounceSep, bounceTime, retSpeed]
    ring

/-- The train's initial state: mass `1`, the observers' clocks prepared at `q₀`, `q₁`, every register
at zero. -/
noncomputable def trainState (N : ℕ) (q₀ q₁ mem₀ mem₁ : LF4.KTorus) : ExchArena N :=
  (((msgPoint 1, q₀), (0, 0), mem₀), ((msgPoint 1, q₁), (4, 1), mem₁),
    fun k => (-5 - 4 * ((k : ℕ) : ℝ), 3), 0, 0)

theorem trainState_geom (q₀ q₁ mem₀ mem₁ : LF4.KTorus) (k : Fin N) :
    exchSep (trainState N q₀ q₁ mem₀ mem₁) = 4 ∧ exchSepVel 1 (trainState N q₀ q₁ mem₀ mem₁) = 1
      ∧ (trainState N q₀ q₁ mem₀ mem₁).2.2.1 k = (-5 - 4 * ((k : ℕ) : ℝ), 3) := by
  refine ⟨?_, ?_, rfl⟩ <;> norm_num [trainState, exchSep, exchSepVel]

section Capstone

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- ★★★ **Two-way exchanges with the moving observer (#244).** In one autonomous, measurable
evolution of the two observers and `N` messengers reflecting off the moving one, for every messenger
with the exchange geometry and registers prepared at zero: the first observer's register is empty
before the emission, holds exactly one passage from the emission's completion until the return
begins, and two passages after the return; the moving observer's register holds the reception; and
both observers' clocks timestamp these within their own errors over their horizons. -/
theorem moving_exchange (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁) {x : ExchArena N}
    (hx₀ : x.1.1 = (msgPoint 1, q₀)) (hx₁ : x.2.1.1 = (msgPoint 1, q₁))
    (hS : x.2.2.2.1 = 0) (hM : x.2.2.2.2 = 0)
    (hG : ∀ k, ExchGeom (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2) :
    (∀ s t, exchFlow J ħ g hf m gd (s + t)
      = (exchFlow J ħ g hf m gd t ∘ exchFlow J ħ g hf m gd s : ExchArena N → ExchArena N))
    ∧ (∀ t, Measurable (exchFlow (N := N) J ħ g hf m gd t))
    ∧ (∀ k t, 0 ≤ t → t < exchEmitStart (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 →
        (exchFlow J ħ g hf m gd t x).2.2.2.1 k = 0)
    ∧ (∀ k t, exchEmitEnd (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 ≤ t →
        t ≤ exchReturnStart (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 →
        (exchFlow J ħ g hf m gd t x).2.2.2.1 k = emitLevel gd (exchSepVel m x) (x.2.2.1 k).2)
    ∧ (∀ k t, exchReturnEnd (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2 ≤ t →
        (exchFlow J ħ g hf m gd t x).2.2.2.1 k = returnLevel gd (exchSepVel m x) (x.2.2.1 k).2)
    ∧ (∀ k t, (1 / 2 - (x.2.2.1 k).1) / (x.2.2.1 k).2 ≤ t →
        (exchFlow J ħ g hf m gd t x).2.2.2.2 k = gd * ((x.2.2.1 k).2)⁻¹)
    ∧ (∀ t, 0 ≤ t → t ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀) →
        |handReading K (tickTime K (handRate J ħ g hf q₀)) (exchFlow J ħ g hf m gd t x).1.1.2 - t|
          ≤ handClockErr J ħ g hf K q₀)
    ∧ (∀ t, 0 ≤ t → t ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁) →
        |handReading K (tickTime K (handRate J ħ g hf q₁)) (exchFlow J ħ g hf m gd t x).2.1.1.2 - t|
          ≤ handClockErr J ħ g hf K q₁) := by
  refine ⟨exchFlow_add J ħ g hf m gd, measurable_exchFlow J ħ g hf m gd hf1, fun k t ht0 ht => ?_,
    fun k t h1 h2 => ?_, fun k t h3 => ?_, fun k t ht => ?_,
    fun _ ht0 ht => abs_restReading_sub_le J ħ g hf m gd hJ hħ hK hq₀ hκ₀ hx₀ ht0 ht,
    fun _ ht0 ht => abs_movingObsReading_sub_le J ħ g hf m gd hJ hħ hK hq₁ hκ₁ hx₁ ht0 ht⟩
  · rw [regS_exchFlow, hS, (hG k).bounceOcc_before ht0 ht]
    simp
  · rw [regS_exchFlow, hS, (hG k).bounceOcc_between h1 h2, emitLevel]
    simp
  · rw [regS_exchFlow, hS, (hG k).bounceOcc_after h3, returnLevel]
    simp
  · rw [div_le_iff₀ (hG k).w_pos] at ht
    rw [regM_exchFlow_received J ħ g hf m gd k (hG k).w_pos (hG k).behind (by linarith), hM]
    simp

end Capstone

end CSD.RecordLayer

end
