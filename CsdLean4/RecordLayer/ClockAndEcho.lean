/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.EchoRadar
public import CsdLean4.RecordLayer.HandClock

/-!
# The autonomous clock-and-echo model on one arena

**Category:** 7-SigmaLayer (the record layer). BACKLOG #202, the dynamics half (out of #39; the
author's third operational-geometry brief's one exact deliverable: *a finite autonomous clock-and-echo
model whose emission and return timestamps are physical records at the same station, with a derived
round-trip timing bound and explicit detector back-reaction*).

#200 read the round trip off `A`'s two records against #185's scheduled clock. Here the clock is
#201's hand clock — one more carrier and one more pointer, at `A` — and the whole device sits on one
arena with one two-time evolution:

  `ClockEchoArena = EchoArena × ActiveArena`,

the echo's carrier with its two pointers, and the clock's carrier with its hand. **Nothing in the
evolution tests `t_Σ`**: the echo's writes are activated by the echo's carrier, the clock's ticks by
the clock's carrier, and the timestamps are the hand's count, read while `A`'s emission record and
`A`'s return record display. Every detector's back-reaction is in the model as the detuning of its
own carrier.

* `ClockEchoArena`, `clockEchoEvolve` — **one two-time, autonomous, measure-preserving evolution**
  (`clockEchoEvolve_comp`, `clockEchoEvolve_shift`, `clockEchoEvolve_measurePreserving`);
* ★★ `clockEchoEmission`, `clockEchoReception`, `clockEchoReturn`, `clockEchoTick` — **the echo's
  three writes and the clock's ticks as `ActualOccurrence`s on the one arena** (#191), every one of
  them activated by a carrier; `clockEchoLabel` — the hand's count as the clock label;
  `emissionLabel_time`, `returnLabel_time` — the two events labelled by the hand;
* `clockReadingAt`, `clockEchoReadings` — **the radar timestamps are the hand's readings** at a time
  while the emission record displays and at a time while the return record displays; ★★
  `clockEchoReadings_eq_labels` — at the write completions they are `τ_tick` times the two events'
  hand labels;
* `clockEchoBudget` — **the derived round-trip budget**: the clock's resolution
  `τ_tick + 1/(2ω_c)` (#201, derived) in place of #185's `T`, the emission write's completion, the
  return write's response, the two transfers, and the retention window (input); ★★
  `abs_clockEchoReadings_emit_sub_le`, `abs_clockEchoReadings_ret_sub_le`;
* ★★★ `autonomous_clock_and_echo` — **the deliverable**: on one arena with one autonomous evolution,
  both timestamps are readings of the autonomous clock at `A` taken at `A`'s two records, and the
  radar time, separation and distance are within the derived budget of the ideal round trip
  `(0, 2τ_hop)`, whose separation is `τ_hop`.

## Honest scope

* The echo and the clock are two carrier–pointer systems on a product arena; they do not interact.
  The clock is colocated with `A` by fiat of the model — a shared site label — not by a coupling.
  Coupling the two (the clock's carrier detuned by the echo's pointer) is ~~#212~~
  (`RecordLayer/ClockEchoCoupling.lean`, the dynamics; its generation is BACKLOG #225).
* Hamiltonian generation of the combined arena, `(ℂℙ³ × T² × T²) × (ℂℙ³ × T²)`, is the second half
  of #202 (`RecordLayer/EchoHamiltonian.lean` for the echo factor; the clock factor is #195).
* The input bounds are the two retention windows and the clock's horizon (one turn of the hand).
* **No universal `c`, no Lorentz invariance.** `c₀` is a calibration constant. The #187 and #190
  headers stand.

References: `specs/BACKLOG.md` #202, #199, #200, #201, #194, #195, #39; `RecordLayer/EchoArena.lean`,
`RecordLayer/EchoRadar.lean` (`echoReturnDelay`, `abs_detunedRoundTrip_sub_roundTrip_le`),
`RecordLayer/HandClock.lean` (`hand`, `handReading`, `abs_handReading_sub_le`, `handCount_mono`,
`tickWrite`), `CV/RadarCoordinates.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The arena and its evolution -/

section Arena

variable (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (C : PointerCoupling)

/-- **The arena of the clock-and-echo model**: the echo arena and the clock's carrier–pointer system. -/
abbrev ClockEchoArena := EchoArena × ActiveArena

/-- The product instance, which instance search does not find at this depth. -/
instance : OpensMeasurableSpace ClockEchoArena := Prod.opensMeasurableSpace

/-- The product instance, which instance search does not find at this depth. -/
instance : BorelSpace ClockEchoArena := Prod.borelSpace

/-- **The one two-time evolution**: the echo's and the clock's, side by side. -/
noncomputable def clockEchoEvolve (s t : OnticTime) : ClockEchoArena → ClockEchoArena :=
  Prod.map (echoEvolve J ħ A B s t) (activeEvolve Jc ħ C.g C.periodic s t)

theorem clockEchoEvolve_self (t : OnticTime) : clockEchoEvolve J ħ A B Jc C t t = id := by
  rw [clockEchoEvolve, echoEvolve_self, activeEvolve_self, Prod.map_id]

/-- The two-time law. -/
theorem clockEchoEvolve_comp (s t u : OnticTime) :
    clockEchoEvolve J ħ A B Jc C t u ∘ clockEchoEvolve J ħ A B Jc C s t
      = clockEchoEvolve J ħ A B Jc C s u := by
  rw [clockEchoEvolve, clockEchoEvolve, clockEchoEvolve, Prod.map_comp_map, echoEvolve_comp,
    activeEvolve_comp]

/-- ★ **Autonomy**: no test of `t_Σ` anywhere in the device. -/
theorem clockEchoEvolve_shift (s t a : OnticTime) :
    clockEchoEvolve J ħ A B Jc C (s + a) (t + a) = clockEchoEvolve J ħ A B Jc C s t := by
  rw [clockEchoEvolve, clockEchoEvolve, echoEvolve_shift, activeEvolve_shift]

theorem measurable_clockEchoEvolve (s t : OnticTime) :
    Measurable (clockEchoEvolve J ħ A B Jc C s t) :=
  (measurable_echoEvolve J ħ A B s t).prodMap
    (measurable_activeEvolve Jc ħ C.g C.periodic C.smooth s t)

/-- Liouville on the clock-and-echo arena. -/
theorem clockEchoEvolve_measurePreserving (s t : OnticTime) (p₀ p₁ : FieldArena 2 2) :
    MeasurePreserving (clockEchoEvolve J ħ A B Jc C s t)
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)) :=
  (echoEvolve_measurePreserving J ħ A B s t p₀).prod
    (activeEvolve_measurePreserving Jc ħ C.g C.periodic C.smooth s t p₁)

/-- The clock label: the hand's count. -/
noncomputable def clockEchoLabel (K : ℕ) (x : ClockEchoArena) : ℕ := handCount K x.2.2

end Arena

/-! ### The writes on the one arena -/

section Records

variable {J ħ : ℝ} (A B : PointerCoupling) {Jc : ℝ} (C : PointerCoupling) {qA qB qc : LF4.KTorus}
  {K : ℕ}

/-- The ready set: both echo pointers ready, the hand in its first half-arc. -/
def clockEchoReady (K : ℕ) : Set ClockEchoArena :=
  {x | x.1 ∈ echoReady ∧ x.2.2 ∈ handReady K}

theorem measurableSet_clockEchoReady (K : ℕ) : MeasurableSet (clockEchoReady K) :=
  (measurable_fst measurableSet_echoReady).inter
    (measurable_snd.snd (measurableSet_handReady K))

/-- ★★ **The emission record on the one arena**: `A`'s first arc, written by the echo's carrier. -/
noncomputable def clockEchoEmission (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    (hqc : qc ∈ handReady K) : ActualOccurrence ClockEchoArena (Fin 3) 2 where
  evolve := clockEchoEvolve J ħ A B Jc C
  evolve_self := clockEchoEvolve_self J ħ A B Jc C
  evolve_comp := clockEchoEvolve_comp J ħ A B Jc C
  measurable_evolve := measurable_clockEchoEvolve J ħ A B Jc C
  readout := fun x => senderRead x.1
  measurable_readout := measurable_senderRead.comp measurable_fst
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := ((msgPoint 1, (qA, qB)), (msgPoint 1, qc))
  prep_mem := ⟨⟨hqA, hqB⟩, hqc⟩
  site := {0}
  start := 0
  value := 1
  writeStart := emitStart (senderRate A ħ qA)
  writeEnd := emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  window := senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  isWrite := (emissionRecord A B hJ hħ hqA hqB hr hslow).isWrite

/-- ★★ **The reception record on the one arena**: `B`'s arc. -/
noncomputable def clockEchoReception (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hκ : 0 < receiverDrift A B J ħ qA qB)
    (hslow : 3 * receiverDrift A B J ħ qA qB ≤ 2 * echoRate A B J ħ qA qB) (hqc : qc ∈ handReady K) :
    ActualOccurrence ClockEchoArena Bool 2 where
  evolve := clockEchoEvolve J ħ A B Jc C
  evolve_self := clockEchoEvolve_self J ħ A B Jc C
  evolve_comp := clockEchoEvolve_comp J ħ A B Jc C
  measurable_evolve := measurable_clockEchoEvolve J ħ A B Jc C
  readout := fun x => receiverRead x.1
  measurable_readout := measurable_receiverRead.comp measurable_fst
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := ((msgPoint 1, (qA, qB)), (msgPoint 1, qc))
  prep_mem := ⟨⟨hqA, hqB⟩, hqc⟩
  site := {1}
  start := 0
  value := true
  writeStart := writeStart (receiverDrift A B J ħ qA qB)
  writeEnd := writeEnd (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
  window := retention (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
  isWrite := (receptionRecord A B hJ hħ hqA hqB hκ hslow).isWrite

/-- ★★ **The return record on the one arena**: `A`'s second arc. -/
noncomputable def clockEchoReturn (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    (hqc : qc ∈ handReady K) : ActualOccurrence ClockEchoArena (Fin 3) 2 where
  evolve := clockEchoEvolve J ħ A B Jc C
  evolve_self := clockEchoEvolve_self J ħ A B Jc C
  evolve_comp := clockEchoEvolve_comp J ħ A B Jc C
  measurable_evolve := measurable_clockEchoEvolve J ħ A B Jc C
  readout := fun x => senderRead x.1
  measurable_readout := measurable_senderRead.comp measurable_fst
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := ((msgPoint 1, (qA, qB)), (msgPoint 1, qc))
  prep_mem := ⟨⟨hqA, hqB⟩, hqc⟩
  site := {0}
  start := 0
  value := 2
  writeStart := returnStart (senderRate A ħ qA)
  writeEnd := returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  window := senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  isWrite := (returnRecord A B hJ hħ hqA hqB hr hslow).isWrite

/-- ★★ **Tick `n` of the clock on the one arena**, written by the clock's carrier. -/
noncomputable def clockEchoTick (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hK : 0 < K) (hqc : qc ∈ handReady K)
    (hκc : 0 < handRate Jc ħ C.g C.periodic qc)
    (hslowc : K * handRate Jc ħ C.g C.periodic qc ≤ handFreq Jc ħ C.g C.periodic qc) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K) : ActualOccurrence ClockEchoArena ℕ 2 where
  evolve := clockEchoEvolve J ħ A B Jc C
  evolve_self := clockEchoEvolve_self J ħ A B Jc C
  evolve_comp := clockEchoEvolve_comp J ħ A B Jc C
  measurable_evolve := measurable_clockEchoEvolve J ħ A B Jc C
  readout := clockEchoLabel K
  measurable_readout := (measurable_handCount K).comp measurable_snd.snd
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := ((msgPoint 1, (qA, qB)), (msgPoint 1, qc))
  prep_mem := ⟨⟨hqA, hqB⟩, hqc⟩
  site := {0}
  start := 0
  value := n
  writeStart := tickStart K (handRate Jc ħ C.g C.periodic qc) n
  writeEnd := tickEnd K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc) n
  window := tickWindow K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc)
  isWrite :=
    (tickWrite Jc ħ C.g C.periodic hJc hħ C.smooth hK hqc hκc hslowc hn1 hnK).isWrite

/-- The emission event, labelled by the hand: the hand's count at the completion of the emission
write. -/
theorem emissionLabel_time (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    (hqc : qc ∈ handReady K) :
    ((clockEchoEmission A B C (Jc := Jc) hJ hħ hqA hqB hr hslow hqc).toRecordEvent
        (clockEchoLabel K)).time
      = handCount K (hand Jc ħ C.g C.periodic
          (emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) qc) := by
  show handCount K (activeFlow Jc ħ C.g C.periodic
    (emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) - 0)
      (msgPoint 1, qc)).2 = _
  rw [sub_zero]
  rfl

/-- The return event, labelled by the hand. -/
theorem returnLabel_time (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    (hqc : qc ∈ handReady K) :
    ((clockEchoReturn A B C (Jc := Jc) hJ hħ hqA hqB hr hslow hqc).toRecordEvent
        (clockEchoLabel K)).time
      = handCount K (hand Jc ħ C.g C.periodic
          (returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) qc) := by
  show handCount K (activeFlow Jc ħ C.g C.periodic
    (returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) - 0)
      (msgPoint 1, qc)).2 = _
  rw [sub_zero]
  rfl

end Records

/-! ### The readings, the budget and the bound -/

section Radar

variable {J ħ : ℝ} (A B : PointerCoupling) {Jc : ℝ} (C : PointerCoupling) {qA qB qc : LF4.KTorus}
  {K : ℕ}

/-- **The clock's reading at time `t`**: the hand's count times the derived calibration. -/
noncomputable def clockReadingAt (Jc ħ : ℝ) (C : PointerCoupling) (K : ℕ) (qc : LF4.KTorus)
    (t : ℝ) : ℝ :=
  handReading K (tickTime K (handRate Jc ħ C.g C.periodic qc)) (hand Jc ħ C.g C.periodic t qc)

/-- The clock's resolution: `τ_tick + 1/(2ω_c)`. -/
noncomputable def clockResolution (Jc ħ : ℝ) (C : PointerCoupling) (K : ℕ) (qc : LF4.KTorus) : ℝ :=
  tickTime K (handRate Jc ħ C.g C.periodic qc) + 1 / (2 * handFreq Jc ħ C.g C.periodic qc)

theorem clockReadingAt_mono (hJc : 0 < Jc) (hħ : 0 < ħ) (hK : 0 < K) (hqc : qc ∈ handReady K)
    (hκc : 0 < handRate Jc ħ C.g C.periodic qc) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ handHorizon K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc)) :
    clockReadingAt Jc ħ C K qc s ≤ clockReadingAt Jc ħ C K qc t :=
  mul_le_mul_of_nonneg_right
    (Nat.cast_le.2 (handCount_mono Jc ħ C.g C.periodic hJc hħ hK hqc hκc hs hst ht))
    (tickTime_pos hK hκc).le

/-- **The measured readings**: the hand at a time `t₁` while the emission record displays and at a
time `t₂` while the return record displays, both within the clock's horizon. -/
noncomputable def clockEchoReadings (hJc : 0 < Jc) (hħ : 0 < ħ) (hK : 0 < K)
    (hqc : qc ∈ handReady K) (hκc : 0 < handRate Jc ħ C.g C.periodic qc) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁)
    (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ handHorizon K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc)) :
    RadarReadings :=
  ⟨clockReadingAt Jc ħ C K qc t₁, clockReadingAt Jc ħ C K qc t₂,
    clockReadingAt_mono C hJc hħ hK hqc hκc h₁ h₁₂ h₂⟩

/-- ★★ **At the write completions the two timestamps are `τ_tick` times the hand labels of `A`'s two
events.** -/
theorem clockEchoReadings_eq_labels (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) (hJc : 0 < Jc)
    (hK : 0 < K) (hqc : qc ∈ handReady K) (hκc : 0 < handRate Jc ħ C.g C.periodic qc)
    (h₂ : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
      ≤ handHorizon K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc)) :
    (clockEchoReadings C hJc hħ hK hqc hκc
        (emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
          (echoRate_pos A B hJ hħ qA qB))
        (emitEnd_le_returnEnd hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
          (echoRate_pos A B hJ hħ qA qB) hslow) h₂).emit
      = (((clockEchoEmission A B C (Jc := Jc) hJ hħ hqA hqB hr hslow hqc).toRecordEvent
          (clockEchoLabel K)).time : ℝ) * tickTime K (handRate Jc ħ C.g C.periodic qc)
    ∧ (clockEchoReadings C hJc hħ hK hqc hκc
        (emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
          (echoRate_pos A B hJ hħ qA qB))
        (emitEnd_le_returnEnd hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
          (echoRate_pos A B hJ hħ qA qB) hslow) h₂).ret
      = (((clockEchoReturn A B C (Jc := Jc) hJ hħ hqA hqB hr hslow hqc).toRecordEvent
          (clockEchoLabel K)).time : ℝ) * tickTime K (handRate Jc ħ C.g C.periodic qc) := by
  rw [emissionLabel_time, returnLabel_time]
  exact ⟨rfl, rfl⟩

/-- **The derived round-trip budget**: the clock's resolution, the retention window, the emission
write's completion, the return write's response, the two transfers. -/
noncomputable def clockEchoBudget (J ħ : ℝ) (qA qB : LF4.KTorus) (Jc : ℝ) (C : PointerCoupling)
    (K : ℕ) (qc : LF4.KTorus) : ℝ :=
  clockResolution Jc ħ C K qc
    + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    + emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    + |echoReturnDelay A B J ħ qA qB| + 2 * transferError J ħ (echoDetuning A B qA qB)

/-- ★★ **The emission timestamp is within the budget of `0`.** -/
theorem abs_clockEchoReadings_emit_sub_le (hJ : 0 < J) (hħ : 0 < ħ) (hJc : 0 < Jc) (hK : 0 < K) (hqc : qc ∈ handReady K)
    (hκc : 0 < handRate Jc ħ C.g C.periodic qc) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ handHorizon K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc))
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).emit - 0|
      ≤ clockEchoBudget A B J ħ qA qB Jc C K qc := by
  show |clockReadingAt Jc ħ C K qc t₁ - 0| ≤ _
  rw [sub_zero]
  have h1 : |clockReadingAt Jc ħ C K qc t₁ - t₁| ≤ clockResolution Jc ħ C K qc :=
    abs_handReading_sub_le Jc ħ C.g C.periodic hJc hħ hK hqc hκc h₁ (by linarith)
  have h2 : |t₁| ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
      + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) := by
    rw [abs_of_nonneg h₁]
    exact hemit.2
  have h3 := abs_nonneg (echoReturnDelay A B J ħ qA qB)
  have h4 := transferError_nonneg hJ hħ (echoDetuning A B qA qB)
  calc |clockReadingAt Jc ħ C K qc t₁|
      = |(clockReadingAt Jc ħ C K qc t₁ - t₁) + t₁| := by rw [sub_add_cancel]
    _ ≤ |clockReadingAt Jc ħ C K qc t₁ - t₁| + |t₁| := abs_add_le _ _
    _ ≤ clockEchoBudget A B J ħ qA qB Jc C K qc := by
        unfold clockEchoBudget
        linarith

/-- ★★ **The return timestamp is within the budget of `2τ_hop`.** -/
theorem abs_clockEchoReadings_ret_sub_le (hJ : 0 < J) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hJc : 0 < Jc) (hK : 0 < K) (hqc : qc ∈ handReady K)
    (hκc : 0 < handRate Jc ħ C.g C.periodic qc) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ handHorizon K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc))
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).ret - roundTrip J ħ|
      ≤ clockEchoBudget A B J ħ qA qB Jc C K qc := by
  show |clockReadingAt Jc ħ C K qc t₂ - roundTrip J ħ| ≤ _
  set r := senderRate A ħ qA
  set l := echoLoss A B J qA qB
  set ω := echoRate A B J ħ qA qB
  set Δ := echoDetuning A B qA qB
  have hE := emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
    (echoRate_pos A B hJ hħ qA qB)
  have h1 : |clockReadingAt Jc ħ C K qc t₂ - t₂| ≤ clockResolution Jc ħ C K qc :=
    abs_handReading_sub_le Jc ħ C.g C.periodic hJc hħ hK hqc hκc (by linarith) h₂
  have h2 : |t₂ - returnEnd r l ω| ≤ senderWindow r l ω := by
    rw [abs_le]
    constructor <;> linarith [hret.1, hret.2]
  have h3 : |returnEnd r l ω - detunedRoundTrip J ħ Δ| = |echoReturnDelay A B J ħ qA qB| := rfl
  have h4 := abs_detunedRoundTrip_sub_roundTrip_le hJ hħ Δ
  calc |clockReadingAt Jc ħ C K qc t₂ - roundTrip J ħ|
      ≤ |clockReadingAt Jc ħ C K qc t₂ - t₂| + |t₂ - roundTrip J ħ| := abs_sub_le _ _ _
    _ ≤ |clockReadingAt Jc ħ C K qc t₂ - t₂|
        + (|t₂ - returnEnd r l ω| + |returnEnd r l ω - roundTrip J ħ|) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ |clockReadingAt Jc ħ C K qc t₂ - t₂|
        + (|t₂ - returnEnd r l ω|
          + (|returnEnd r l ω - detunedRoundTrip J ħ Δ| + |detunedRoundTrip J ħ Δ - roundTrip J ħ|)) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ clockEchoBudget A B J ħ qA qB Jc C K qc := by
        rw [h3]
        unfold clockEchoBudget
        linarith

/-- ★★★ **The autonomous clock-and-echo model — the brief's deliverable.** On one arena with one
autonomous two-time measure-preserving evolution: the emission, the reception, the return and the
clock's ticks are `ActualOccurrence`s, every one activated by a carrier; both radar timestamps are
readings of the autonomous clock at `A`, taken while `A`'s emission record (value `1`) and `A`'s
return record (value `2`) display; and against the ideal round trip `(0, 2τ_hop)`, whose radar
separation is `τ_hop`, the measured radar time, separation and distance are within the derived
budget `(τ_tick + 1/(2ω_c)) + senderWindow + emitEnd + |echoReturnDelay| + 2 transferError`. -/
theorem autonomous_clock_and_echo (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    (hκ : 0 < receiverDrift A B J ħ qA qB)
    (hslowB : 3 * receiverDrift A B J ħ qA qB ≤ 2 * echoRate A B J ħ qA qB) (hJc : 0 < Jc)
    (hK : 0 < K) (hqc : qc ∈ handReady K) (hκc : 0 < handRate Jc ħ C.g C.periodic qc)
    (hslowc : K * handRate Jc ħ C.g C.periodic qc ≤ handFreq Jc ħ C.g C.periodic qc) {t₁ t₂ : ℝ}
    (h₂ : t₂ ≤ handHorizon K (handRate Jc ħ C.g C.periodic qc) (handFreq Jc ħ C.g C.periodic qc))
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    (∀ s t u : OnticTime, clockEchoEvolve J ħ A B Jc C t u ∘ clockEchoEvolve J ħ A B Jc C s t
        = clockEchoEvolve J ħ A B Jc C s u)
      ∧ (∀ s t a : OnticTime,
          clockEchoEvolve J ħ A B Jc C (s + a) (t + a) = clockEchoEvolve J ħ A B Jc C s t)
      ∧ (∀ (s t : OnticTime) (p₀ p₁ : FieldArena 2 2),
          MeasurePreserving (clockEchoEvolve J ħ A B Jc C s t)
            (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
            (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)))
      ∧ (clockEchoEmission A B C (Jc := Jc) hJ hħ hqA hqB hr hslow hqc).site = {0}
      ∧ (clockEchoReception A B C (Jc := Jc) hJ hħ hqA hqB hκ hslowB hqc).site = {1}
      ∧ (clockEchoReturn A B C (Jc := Jc) hJ hħ hqA hqB hr hslow hqc).site = {0}
      ∧ (∀ (n : ℕ) (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K),
          (clockEchoTick (J := J) A B C hJc hħ hqA hqB hK hqc hκc hslowc hn1 hnK).site = {0}
            ∧ (clockEchoTick (J := J) A B C hJc hħ hqA hqB hK hqc hκc hslowc hn1 hnK).value = n)
      ∧ ∃ (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂),
          senderRead (echoFlow J ħ A B t₁ (msgPoint 1, (qA, qB))) = 1
          ∧ senderRead (echoFlow J ħ A B t₂ (msgPoint 1, (qA, qB))) = 2
          ∧ (idealEchoReadings hJ hħ).radarSep = hopTime J ħ
          ∧ |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).radarTime
              - (idealEchoReadings hJ hħ).radarTime| ≤ clockEchoBudget A B J ħ qA qB Jc C K qc
          ∧ |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).radarSep
              - (idealEchoReadings hJ hħ).radarSep| ≤ clockEchoBudget A B J ħ qA qB Jc C K qc
          ∧ |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).radarDist c₀
              - (idealEchoReadings hJ hħ).radarDist c₀|
            ≤ c₀ * clockEchoBudget A B J ħ qA qB Jc C K qc := by
  have hE := emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
    (echoRate_pos A B hJ hħ qA qB)
  have h₁ : 0 ≤ t₁ := by linarith [hemit.1]
  have h₁₂ : t₁ ≤ t₂ := by
    have := emitEnd_add_window_lt_returnEnd hr (echoLoss_pos A B hJ qA qB).le
      (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) hslow
    linarith [hemit.2, hret.1]
  refine ⟨clockEchoEvolve_comp J ħ A B Jc C, clockEchoEvolve_shift J ħ A B Jc C,
    fun s t p₀ p₁ => clockEchoEvolve_measurePreserving J ħ A B Jc C s t p₀ p₁, rfl, rfl, rfl,
    fun _ _ _ => ⟨rfl, rfl⟩, h₁, h₁₂, sender_emitted A B hJ hħ hqA hr qB hemit.1 hemit.2,
    sender_returned A B hJ hħ hqA hr qB hret.1 hret.2, idealEchoReadings_radarSep hJ hħ, ?_, ?_, ?_⟩
  all_goals
    have he : |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).emit - (idealEchoReadings hJ hħ).emit|
        ≤ clockEchoBudget A B J ħ qA qB Jc C K qc := by
      rw [idealEchoReadings_emit]
      exact abs_clockEchoReadings_emit_sub_le A B C hJ hħ hJc hK hqc hκc h₁ h₁₂ h₂ hemit
    have hre : |(clockEchoReadings C hJc hħ hK hqc hκc h₁ h₁₂ h₂).ret - (idealEchoReadings hJ hħ).ret|
        ≤ clockEchoBudget A B J ħ qA qB Jc C K qc := by
      rw [idealEchoReadings_ret]
      exact abs_clockEchoReadings_ret_sub_le A B C hJ hħ hr hJc hK hqc hκc h₁ h₁₂ h₂ hret
  · exact RadarReadings.abs_radarTime_sub_le he hre
  · exact RadarReadings.abs_radarSep_sub_le he hre
  · exact RadarReadings.abs_radarDist_sub_le hc₀ he hre

end Radar

end CSD.RecordLayer

end
