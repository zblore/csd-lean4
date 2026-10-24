/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ActivatedWrite

/-!
# Coupled reception: the activated write against the uncoupled transfer

**Category:** 7-SigmaLayer (the record layer). BACKLOG #196 (out of #39; the author's second
operational-geometry brief, #191–#197; the brief's §6 acceptance criterion).

#183 transferred the excitation exactly and read it by a schedule; #194 let the receiver's own
pointer be set in motion by the arriving carrier, at the price of a detuning `Δ = g f(θ₂)` on the
carrier. This module is the compatibility theorem between the two: how far the coupled reception is
from the uncoupled one, when the receiver still tells the two messages apart, when the write forms,
and where its event sits in the causal order of the hop graph.

* `detuned_readout_one_zero_detuning` — **at `Δ = 0` the coupled occupancy is the uncoupled
  `sin²(Jt/ħ)`** of #183: the detuned law contains the exact transfer;
* `abs_sin_sq_sub_sin_sq_le`, `rabiFreq_sub_le`, ★★ `occupancy_loss_le` — **the loss is
  continuous, quadratic in the detuning**: `|n_B^Δ(t) − n_B^0(t)| ≤ (1/(4J²) + |t|/(8Jħ)) Δ²`, hence
  `≤ C |Δ|` for `|Δ| ≤ 1` (`occupancy_loss_le_of_abs_le_one`); the two pieces are the peak loss
  `(Δ/2)²/Ω²` and the phase drift `|Ω − J| |t|/ħ`;
* ★★ `readBit_detuned_one`, `readBit_detuned_zero`, ★★ `receiver_bit_distinguishes` — **the
  receiver's thresholded bit of #186 still distinguishes the two preparations at the detuned hop
  time whenever `|Δ| ≤ 2J`**, i.e. whenever the peak loss stays at or below the threshold `1/2`;
* ★ `formation_interval` — **the formation interval of the write from the occupancy integral and
  the preparation**: the write of #194 is an `IsRecordWrite` with interval `[1/(6κ), 2/(3κ) +
  1/(2ω)]`, and the lifted displacement is pinched between `0` and `κ t`; retention per #194
  (`message_one_returns`);
* `ClockedArena`, `clockedEvolve` — **the arena of #194 with the record clock of #185**: a two-time,
  measure-preserving dynamics (`clockedEvolve_comp`, `clockedEvolve_measurePreserving`);
  ★★ `clockedRegister` — the activated write registered on it as an `ActualOccurrence` (#191);
  `clockedReading`, `emissionEvent`, ★★ `emission_causalPrecedes_reception` — **the occurrence's
  event, labelled by the arena clock, is causally preceded on the hop graph by the emission**, as
  soon as the clock has ticked once before the write completes; `receptionEvent_time_le` bounds the
  label by the periods elapsed;
* ★★★ `coupled_reception` — the package.

## Honest scope

* The clock is #185's: a scheduled device, a modelling input indexed by `t_Σ`, exactly as there.
  What is internal is the activation of the *write*; the labelling of its event by the clock is a
  reading of a second device in the arena, not a second internal activation.
* The loss bound is stated for message `1` from the vacuum at `B`; the hypotheses `0 < J`, `0 < ħ`
  are those of #183. Nothing is claimed about a universal rate or a metric; the event order is
  `CausalPrecedes` on the assumed hop graph, permitted influence, as in #186.

References: `specs/BACKLOG.md` #196, #194, #195, #186, #185, #183, #39;
`CV/DetunedExchange.lean` (`detuned_readout_one`, `detuned_readout_one_peak`,
`one_sub_div_rabiFreq_sq`), `CV/SignalExchange.lean` (`receiver_readout_one`),
`RecordLayer/ActivatedWrite.lean` (`activatedRegister`, `message_one_returns`),
`RecordLayer/RecordedExchange.lean` (`readBit`, `hopGraph`, `causal_chain`),
`RecordLayer/RecordClock.lean` (`tickCount_ge`, `tickCount_le`), `CV/RecordCausalOrder.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Compatibility with the uncoupled transfer -/

/-- **At zero detuning the coupled occupancy is the uncoupled one** of #183. -/
theorem detuned_readout_one_zero_detuning {J : ℝ} (hJ : 0 < J) (ħ t : ℝ) :
    arenaObs occB ((detunedFlow J ħ 0).arenaFlow t (msgPoint 1))
      = Real.sin (hopAngle J ħ t) ^ 2 := by
  rw [detuned_readout_one hJ, rabiFreq_zero hJ.le, div_self hJ.ne', one_pow, one_mul, rabiAngle,
    rabiRate, rabiFreq_zero hJ.le, hopAngle]

/-- `sin²` is `1`-Lipschitz. -/
theorem abs_sin_sq_sub_sin_sq_le (a b : ℝ) : |Real.sin a ^ 2 - Real.sin b ^ 2| ≤ |a - b| := by
  have h : Real.sin a ^ 2 - Real.sin b ^ 2 = (Real.cos (2 * b) - Real.cos (2 * a)) / 2 := by
    rw [Real.sin_sq, Real.sin_sq, Real.cos_sq, Real.cos_sq]
    ring
  rw [h, abs_div, abs_two]
  have h1 := Real.abs_cos_sub_cos_le (2 * b) (2 * a)
  have h2 : |2 * b - 2 * a| = 2 * |a - b| := by
    rw [show 2 * b - 2 * a = -(2 * (a - b)) by ring, abs_neg, abs_mul, abs_two]
  rw [h2] at h1
  linarith [div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Rabi energy exceeds `J` by at most `Δ²/(8J)`. -/
theorem rabiFreq_sub_le {J : ℝ} (hJ : 0 < J) (Δ : ℝ) : rabiFreq J Δ - J ≤ Δ ^ 2 / (8 * J) := by
  have hJΩ := le_rabiFreq hJ.le Δ
  rw [le_div_iff₀ (by positivity)]
  have h1 : (rabiFreq J Δ - J) * (2 * J) ≤ (rabiFreq J Δ - J) * (rabiFreq J Δ + J) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (rabiFreq J Δ - J) * (rabiFreq J Δ + J) = (Δ / 2) ^ 2 := by
    linear_combination rabiFreq_sq J Δ
  have h3 : (rabiFreq J Δ - J) * (8 * J) = 4 * ((rabiFreq J Δ - J) * (2 * J)) := by ring
  rw [h3]
  nlinarith [h1, h2]

/-- The peak loss is at most `Δ²/(4J²)`. -/
theorem one_sub_div_rabiFreq_sq_le {J : ℝ} (hJ : 0 < J) (Δ : ℝ) :
    1 - (J / rabiFreq J Δ) ^ 2 ≤ Δ ^ 2 / (4 * J ^ 2) := by
  rw [one_sub_div_rabiFreq_sq hJ]
  have hΩ := rabiFreq_pos hJ Δ
  rw [div_le_div_iff₀ (by positivity) (by positivity), rabiFreq_sq]
  nlinarith [sq_nonneg Δ, sq_nonneg (Δ ^ 2)]

/-- The phase drift: `|Ωt/ħ − Jt/ħ| ≤ |t| Δ²/(8Jħ)`. -/
theorem abs_rabiAngle_sub_hopAngle_le {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ t : ℝ) :
    |rabiAngle J ħ Δ t - hopAngle J ħ t| ≤ |t| * Δ ^ 2 / (8 * J * ħ) := by
  have hJΩ := le_rabiFreq hJ.le Δ
  have h := rabiFreq_sub_le hJ Δ
  rw [rabiAngle, rabiRate, hopAngle,
    show rabiFreq J Δ / ħ * t - J / ħ * t = (rabiFreq J Δ - J) * t / ħ by ring, abs_div, abs_mul,
    abs_of_pos hħ, abs_of_nonneg (by linarith), div_le_div_iff₀ hħ (by positivity)]
  have h' : (rabiFreq J Δ - J) * (8 * J) ≤ Δ ^ 2 := by
    rwa [le_div_iff₀ (by positivity)] at h
  have h'' := mul_le_mul_of_nonneg_left h' (mul_nonneg (abs_nonneg t) hħ.le)
  nlinarith [h'']

/-- ★★ **The loss of coupled reception is continuous in the detuning, quadratically**: the
occupancy of `B` for message `1` under detuning `Δ` differs from the uncoupled occupancy by at most
`(1/(4J²) + |t|/(8Jħ)) Δ²`. -/
theorem occupancy_loss_le {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ t : ℝ) :
    |arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1))
        - arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1))|
      ≤ (1 / (4 * J ^ 2) + |t| / (8 * J * ħ)) * Δ ^ 2 := by
  rw [detuned_readout_one hJ, receiver_readout_one]
  have hsplit : (J / rabiFreq J Δ) ^ 2 * Real.sin (rabiAngle J ħ Δ t) ^ 2
        - Real.sin (hopAngle J ħ t) ^ 2
      = ((J / rabiFreq J Δ) ^ 2 - 1) * Real.sin (rabiAngle J ħ Δ t) ^ 2
        + (Real.sin (rabiAngle J ħ Δ t) ^ 2 - Real.sin (hopAngle J ħ t) ^ 2) := by ring
  rw [hsplit]
  have hr : |((J / rabiFreq J Δ) ^ 2 - 1) * Real.sin (rabiAngle J ħ Δ t) ^ 2|
      ≤ Δ ^ 2 / (4 * J ^ 2) := by
    have h0 : (0 : ℝ) ≤ 1 - (J / rabiFreq J Δ) ^ 2 := by linarith [div_rabiFreq_sq_le_one hJ Δ]
    rw [abs_mul, abs_sub_comm, abs_of_nonneg h0,
      abs_of_nonneg (sq_nonneg (Real.sin (rabiAngle J ħ Δ t)))]
    exact (mul_le_of_le_one_right h0 (Real.sin_sq_le_one _)).trans
      (one_sub_div_rabiFreq_sq_le hJ Δ)
  have hsin : |Real.sin (rabiAngle J ħ Δ t) ^ 2 - Real.sin (hopAngle J ħ t) ^ 2|
      ≤ |t| * Δ ^ 2 / (8 * J * ħ) :=
    (abs_sin_sq_sub_sin_sq_le _ _).trans (abs_rabiAngle_sub_hopAngle_le hJ hħ Δ t)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ Δ ^ 2 / (4 * J ^ 2) + |t| * Δ ^ 2 / (8 * J * ħ) := add_le_add hr hsin
    _ = _ := by ring

/-- The row's form: for `|Δ| ≤ 1` the loss is at most `C |Δ|`. -/
theorem occupancy_loss_le_of_abs_le_one {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {Δ : ℝ}
    (hΔ : |Δ| ≤ 1) (t : ℝ) :
    |arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1))
        - arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1))|
      ≤ (1 / (4 * J ^ 2) + |t| / (8 * J * ħ)) * |Δ| := by
  refine (occupancy_loss_le hJ hħ Δ t).trans ?_
  have hC : 0 ≤ 1 / (4 * J ^ 2) + |t| / (8 * J * ħ) := by positivity
  have hsq : Δ ^ 2 ≤ |Δ| := by
    rw [← sq_abs]
    exact pow_le_of_le_one (abs_nonneg Δ) hΔ (by norm_num)
  exact mul_le_mul_of_nonneg_left hsq hC

/-! ### The receiver's thresholded bit still distinguishes the messages -/

/-- Under `|Δ| ≤ 2J` the peak occupancy is at least the threshold `1/2`. -/
theorem half_le_div_rabiFreq_sq {J Δ : ℝ} (hJ : 0 < J) (hΔ : |Δ| ≤ 2 * J) :
    1 / 2 ≤ (J / rabiFreq J Δ) ^ 2 := by
  have hΩ := rabiFreq_pos hJ Δ
  have hΔ2 : Δ ^ 2 ≤ (2 * J) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg Δ) hΔ 2
  rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity), rabiFreq_sq]
  nlinarith

/-- ★★ **The receiver's bit reads `1` for message `1`** at the detuned hop time whenever
`|Δ| ≤ 2J`. -/
theorem readBit_detuned_one {J ħ Δ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hΔ : |Δ| ≤ 2 * J) :
    readBit excB ((detunedFlow J ħ Δ).arenaFlow (detunedHopTime J ħ Δ) (msgPoint 1)) = 1 := by
  have h := detuned_readout_one_peak hJ hħ Δ
  unfold occB at h
  unfold readBit
  rw [← arenaObs_single_eq_momentMap, h]
  exact ite_eq_left (half_le_div_rabiFreq_sq hJ hΔ)

/-- The receiver's bit reads `0` for message `0`, at every time and every detuning. -/
theorem readBit_detuned_zero {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    readBit excB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 0)) = 0 := by
  have h := detuned_readout_zero hJ ħ Δ t
  unfold occB at h
  unfold readBit
  rw [← arenaObs_single_eq_momentMap, h]
  exact ite_eq_right (by norm_num)

/-- ★★ **The thresholded reception bit distinguishes the two messages under detuning** whenever the
peak loss stays below the threshold: `|Δ| ≤ 2J`. -/
theorem receiver_bit_distinguishes {J ħ Δ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hΔ : |Δ| ≤ 2 * J) :
    readBit excB ((detunedFlow J ħ Δ).arenaFlow (detunedHopTime J ħ Δ) (msgPoint 1))
      ≠ readBit excB ((detunedFlow J ħ Δ).arenaFlow (detunedHopTime J ħ Δ) (msgPoint 0)) := by
  rw [readBit_detuned_one hJ hħ hΔ, readBit_detuned_zero hJ]
  decide

/-! ### The formation interval of the write -/

section Formation

variable {f : ℝ → ℝ} {J ħ : ℝ} (g : ℝ) (hf : Function.Periodic f 1)

/-- ★ **The formation interval from the occupancy integral and the preparation**: the write of #194
is an `IsRecordWrite` on `[1/(6κ), 2/(3κ) + 1/(2ω)]`, and the lifted displacement from the
occupancy integral is pinched between `0` and `κ t`. -/
theorem formation_interval (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2)) :
    IsRecordWrite (fun t => displayed (activeEvolve J ħ g hf 0 t (msgPoint 1, q))) 0
        (writeStart (driftRate J ħ g hf q.2))
        (writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)))
        (retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) true
      ∧ ∀ t, 0 ≤ t → 0 ≤ pointerAmount J ħ g hf t (msgPoint 1, q)
          ∧ pointerAmount J ħ g hf t (msgPoint 1, q) ≤ driftRate J ħ g hf q.2 * t := by
  refine ⟨(activatedRegister g hf hJ hħ hf1 hq hκ hslow).isWrite, fun t ht => ?_⟩
  rw [pointerAmount_msgPoint_one J ħ g hf hJ hħ]
  exact ⟨pointerDrift_nonneg hκ.le (rabiRate_pos hJ hħ _) ht,
    pointerDrift_le hκ.le (rabiRate_pos hJ hħ _) ht⟩

end Formation

/-! ### The arena with the record clock, and the event order -/

section Clocked

variable {K : ℕ} {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- **The arena of the activated write with the record clock of #185.** -/
abbrev ClockedArena (K : ℕ) := ActiveArena × ClockArena K

/-- The joint two-time propagator: the activated dynamics and the clock. -/
noncomputable def clockedEvolve (T : ℝ) (s t : OnticTime) : ClockedArena K → ClockedArena K :=
  Prod.map (activeEvolve J ħ g hf s t) (clockEvolve T s t)

theorem clockedEvolve_self (T : ℝ) (t : OnticTime) : clockedEvolve (K := K) J ħ g hf T t t = id := by
  rw [clockedEvolve, activeEvolve_self, clockEvolve_self, Prod.map_id]

/-- The two-time law on the clocked arena. -/
theorem clockedEvolve_comp (T : ℝ) (s t u : OnticTime) :
    clockedEvolve (K := K) J ħ g hf T t u ∘ clockedEvolve J ħ g hf T s t
      = clockedEvolve J ħ g hf T s u := by
  rw [clockedEvolve, clockedEvolve, clockedEvolve, Prod.map_comp_map, activeEvolve_comp,
    clockEvolve_comp]

theorem measurable_clockedEvolve (hf1 : ContDiff ℝ 1 f) (T : ℝ) (s t : OnticTime) :
    Measurable (clockedEvolve (K := K) J ħ g hf T s t) :=
  (measurable_activeEvolve J ħ g hf hf1 s t).prodMap (measurable_clockEvolve T s t)

/-- Liouville on the clocked arena. -/
theorem clockedEvolve_measurePreserving (hf1 : ContDiff ℝ 1 f) (T : ℝ) (s t : OnticTime)
    (p₀ : FieldArena 2 2) :
    MeasurePreserving (clockedEvolve (K := K) J ħ g hf T s t)
      (((fsMeasure p₀).prod volume).prod volume) (((fsMeasure p₀).prod volume).prod volume) :=
  (activeEvolve_measurePreserving J ħ g hf hf1 s t p₀).prod (clockEvolve_measurePreserving T s t)

/-- ★★ **The activated write registered on the clocked arena** (#191), the clock ready alongside
the pointer. -/
noncomputable def clockedRegister (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f)
    {q : LF4.KTorus} (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2))
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) : ActualOccurrence (ClockedArena K) Bool 2 where
  evolve := clockedEvolve J ħ g hf T
  evolve_self := clockedEvolve_self J ħ g hf T
  evolve_comp := clockedEvolve_comp J ħ g hf T
  measurable_evolve := measurable_clockedEvolve J ħ g hf hf1 T
  readout := fun x => displayed x.1
  measurable_readout := measurable_displayed.comp measurable_fst
  ready := {x | x.1.2 ∈ readyArc 2 ∧ x.2 ∈ ClockReady K}
  measurableSet_ready :=
    ((measurable_snd.comp measurable_fst) measurableSet_readyArc).inter
      (measurable_snd measurableSet_clockReady)
  prep := ((msgPoint 1, q), c)
  prep_mem := ⟨hq, hc⟩
  site := {1}
  start := 0
  value := true
  writeStart := writeStart (driftRate J ħ g hf q.2)
  writeEnd := writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
  window := retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
  isWrite := (activatedRegister g hf hJ hħ hf1 hq hκ hslow).isWrite

/-- The arena clock's reading. -/
noncomputable def clockedReading (x : ClockedArena K) : ℕ := tickCount x.2

/-- The emission event: the message at `A`, period `0`. -/
def emissionEvent : RecordEvent 2 := ⟨{0}, 0⟩

theorem receptionEvent_region (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2))
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ((clockedRegister J ħ g hf hJ hħ hf1 hq hκ hslow hc T).toRecordEvent clockedReading).region
      = {1} := rfl

/-- The reception event's period is the clock's tick count at the completion of the write. -/
theorem receptionEvent_time (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2))
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ((clockedRegister J ħ g hf hJ hħ hf1 hq hκ hslow hc T).toRecordEvent clockedReading).time
      = tickCount (clockEvolve T 0
          (writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) c) := rfl

/-- The label is at most the number of periods elapsed at the completion of the write. -/
theorem receptionEvent_time_le (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2))
    {c : ClockArena K} (hc : c ∈ ClockReady K) {T : ℝ} (hT : 0 < T) {n : ℕ}
    (hn : writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) ≤ n * T) :
    ((clockedRegister J ħ g hf hJ hħ hf1 hq hκ hslow hc T).toRecordEvent clockedReading).time ≤ n := by
  rw [receptionEvent_time]
  exact tickCount_le hT hc n hn

/-- ★★ **The emission causally precedes the reception on the hop graph**, as soon as the clock has
ticked once before the write completes (`T ≤ writeEnd`). -/
theorem emission_causalPrecedes_reception (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f)
    {q : LF4.KTorus} (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2))
    (hK : 0 < K) {c : ClockArena K} (hc : c ∈ ClockReady K) {T : ℝ} (hT : 0 < T)
    (hone : T ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) :
    CausalPrecedes hopGraph emissionEvent
      ((clockedRegister J ħ g hf hJ hħ hf1 hq hκ hslow hc T).toRecordEvent clockedReading) := by
  rw [CausalPrecedes, receptionEvent_time, receptionEvent_region]
  refine ⟨Nat.zero_le _, ?_⟩
  have h1 : 1 ≤ tickCount (clockEvolve T 0
      (writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) c) := by
    have := tickCount_ge hK hT hc ⟨0, hK⟩ (by simpa using hone)
    simpa using this
  show ({1} : Finset (Fin 2)) ⊆ graphBall hopGraph {0} (_ - 0)
  rw [Nat.sub_zero]
  exact (show ({1} : Finset (Fin 2)) ⊆ graphBall hopGraph {0} 1 by decide).trans
    (graphBall_mono hopGraph {0} h1)

/-! ### The package -/

/-- ★★★ **Coupled reception.** The occupancy of `B` under the detuning `Δ` is the detuned Rabi
law, exact transfer at `Δ = 0`, with a loss quadratic in `Δ`; the receiver's thresholded bit
distinguishes the two messages whenever `|Δ| ≤ 2J`; the write of #194 forms on its explicit
interval with the displacement pinched by the occupancy integral; the retention is finite; and the
occurrence's event, labelled by the arena clock, is causally preceded by the emission on the hop
graph once the clock has ticked. -/
theorem coupled_reception (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2))
    (hK : 0 < K) {c : ClockArena K} (hc : c ∈ ClockReady K) {T : ℝ} (hT : 0 < T)
    (hone : T ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) :
    (∀ Δ t : ℝ, arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1))
        = (J / rabiFreq J Δ) ^ 2 * Real.sin (rabiAngle J ħ Δ t) ^ 2)
      ∧ (∀ t : ℝ, arenaObs occB ((detunedFlow J ħ 0).arenaFlow t (msgPoint 1))
          = Real.sin (hopAngle J ħ t) ^ 2)
      ∧ (∀ Δ t : ℝ, |arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1))
          - arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1))|
          ≤ (1 / (4 * J ^ 2) + |t| / (8 * J * ħ)) * Δ ^ 2)
      ∧ (∀ Δ : ℝ, |Δ| ≤ 2 * J →
          readBit excB ((detunedFlow J ħ Δ).arenaFlow (detunedHopTime J ħ Δ) (msgPoint 1))
            ≠ readBit excB ((detunedFlow J ħ Δ).arenaFlow (detunedHopTime J ħ Δ) (msgPoint 0)))
      ∧ IsRecordWrite (fun t => displayed (activeEvolve J ħ g hf 0 t (msgPoint 1, q))) 0
          (writeStart (driftRate J ħ g hf q.2))
          (writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)))
          (retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) true
      ∧ (∃ t, writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
            + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) < t
          ∧ (activeFlow J ħ g hf t (msgPoint 1, q)).2 = q)
      ∧ CausalPrecedes hopGraph emissionEvent
          ((clockedRegister J ħ g hf hJ hħ hf1 hq hκ hslow hc T).toRecordEvent clockedReading) :=
  ⟨fun Δ t => detuned_readout_one hJ ħ Δ t, detuned_readout_one_zero_detuning hJ ħ,
    fun Δ t => occupancy_loss_le hJ hħ Δ t, fun _ hΔ => receiver_bit_distinguishes hJ hħ hΔ,
    (formation_interval g hf hJ hħ hf1 hq hκ hslow).1, message_one_returns g hf hJ hħ q hκ,
    emission_causalPrecedes_reception J ħ g hf hJ hħ hf1 hq hκ hslow hK hc hT hone⟩

end Clocked

end CSD.RecordLayer

end
