/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.RecordedExchange
public import CsdLean4.RecordLayer.ChainClocks

/-!
# The occurrence registry: actual record writes, with their provenance

**Category:** 7-SigmaLayer (the record layer — the registry of the clock-and-echo programme).
BACKLOG #191 (out of #39; the first of #191–#197, the author's second operational-geometry brief).

Three things have been called "an event" in the programme and they are not the same thing:

1. **an actual record occurrence** — a carrier whose readout *changes*, along the constructed
   dynamics, from a preparation that was ready, to a value it then holds for a stated window;
2. **a possible observation** of a subsystem — a measurable readout and nothing else, which can be
   evaluated at any time without anything having been written (the receiver readouts of #190);
3. **a region label** — `CV.RecordEvent`, a read region with a period index, which is what the
   causal order `CausalPrecedes` is about.

This file keeps the three apart and names the maps between them.

* `IsRecordWrite h t₀ τ₀ τ₁ w v` — **a readout history writes `v`**: not `v` on `[t₀, τ₀)`, `v` on
  `[τ₁, τ₁ + w]`; the write interval is `[τ₀, τ₁]` (sharp when `τ₀ = τ₁`), the window `w` finite;
* ★ `not_isRecordWrite_of_eq`, `IsRecordWrite.not_within` — **inside a write's window there is no
  second write of that carrier**, for any value: inspecting an unchanged register is not an
  occurrence;
* `Observation X Ω` — kind 2; `ActualOccurrence X Ω K` — kind 1, carrying the carrier's two-time
  measurable evolution, its readout, its ready set, **the actual preparation**, the recorded value,
  the write interval and the window, and the write itself **as a proof field discharged from the
  dynamics** (`isWrite`); `toObservation` forgets to kind 2, `toRecordEvent clk` forgets to kind 3 by
  labelling the carrier's site with a clock readout at the completion of the write;
* `recordSet`, `measurableSet_recordSet`, `recordPattern`, ★ `factorsThrough_recordSet` — the
  record predicate "this occurrence's value is displayed" is measurable and factors through the
  pattern projection of `MacroProjection.lean`;
* **instances, each discharged from an existing dynamics**: `exchangeRegister i` — the emission,
  reception and return registers of #186 (sharp writes at the readout times, `toRecordEvent` is
  #186's `eventOf`); `clockSlot n` — every slot of the record clock of #185 (write interval
  `[nT, (n+1)T]`); ★ `exchange_no_second_write` — after its readout a register of #186 admits no
  further write;
* **the chain of #190 has readouts, not registers**: `receiverObservation k` is kind 2. So
  `ChainXArena n K` adds a reception register at every site, `chainXEvolve` is its two-time
  (★ `chainXEvolve_comp`), measurable, ★ measure-preserving skew-product propagator,
  ★★ `chainRegister_written` writes register `k` with the message from the transmitted state at
  `k τ_hop` and `chainRegister_frozen` keeps it, `chainRegister k` is the actual occurrence, and
  ★★★ `siteEvent_eq_toRecordEvent` — **the chain's site events are the forgetful images of actual
  writes on the common arena**, their period labels the ticks of the site's own clock, which are
  writes themselves (`clockSlot`). That is the brief's §2 acceptance criterion;
* ★★★ `record_occurrences` — the package.

## Honest scope

* ⚠️ The chain registers are written on the crossing of `k τ_hop` by the bit read off the exchange
  state at that time: the **schedule** still triggers the write, exactly as in #186. What is new is
  that the receptions of the chain are now writes with provenance rather than readouts; a write
  activated by the arriving carrier itself is #194.
* ⚠️ `ActualOccurrence` carries its `evolve` as a field so that one registry serves several arenas;
  the two-time law and measurability are proof fields, and every instance below supplies the
  corpus's constructed evolution. Nothing physical is carried by an unproved field.
* The period label of `toRecordEvent` is whatever clock readout is supplied; under the stated
  calibration `T = τ_hop` it is the site index, as in #186 and #190.
* Clock calibration and synchronisation stay hypotheses; the clocks' horizon must cover the chain.

References: `specs/BACKLOG.md` #191, #185, #186, #190, #39; `RecordLayer/RecordedExchange.lean`,
`RecordLayer/RecordClock.lean`, `RecordLayer/ChainClocks.lean`, `RecordLayer/MacroProjection.lean`,
`CV/RecordCausalOrder.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K : ℕ}

/-! ### Record writes along a readout history -/

/-- **A readout history writes the value `v`**, from the start `t₀`, with write interval `[τ₀, τ₁]`
and window `w`: it does not display `v` on `[t₀, τ₀)`, and displays `v` on `[τ₁, τ₁ + w]`. -/
structure IsRecordWrite {Ω : Type*} (h : ℝ → Ω) (t₀ τ₀ τ₁ w : ℝ) (v : Ω) : Prop where
  /-- The write starts after the start. -/
  start_le : t₀ ≤ τ₀
  /-- The write interval is an interval. -/
  interval : τ₀ ≤ τ₁
  /-- The window is a window. -/
  window_nonneg : 0 ≤ w
  /-- Before the write the value is not displayed. -/
  before : ∀ t, t₀ ≤ t → t < τ₀ → h t ≠ v
  /-- Through the window the value is displayed. -/
  holds : ∀ t, τ₁ ≤ t → t ≤ τ₁ + w → h t = v

/-- A history that displays the same value at a time before a candidate write interval and at a
time inside the candidate window admits no write there: **an unchanged readout is not a write.** -/
theorem not_isRecordWrite_of_eq {Ω : Type*} {h : ℝ → Ω} {t₀ τ₀ τ₁ w : ℝ} {v : Ω} {a b : ℝ}
    (ha₀ : t₀ ≤ a) (ha₁ : a < τ₀) (hb₀ : τ₁ ≤ b) (hb₁ : b ≤ τ₁ + w) (hab : h a = h b) :
    ¬ IsRecordWrite h t₀ τ₀ τ₁ w v := fun hw =>
  hw.before a ha₀ ha₁ (hab.trans (hw.holds b hb₀ hb₁))

/-- ★ **No second write inside a write's window.** Once `h` has written `v` by `τ₁` and holds it
through `τ₁ + w`, there is no write — of any value — whose interval starts after `τ₁` and completes
within the window, from any start at or before `τ₁`. Repeated inspection of the unchanged register
creates no occurrence. -/
theorem IsRecordWrite.not_within {Ω : Type*} {h : ℝ → Ω} {t₀ τ₀ τ₁ w : ℝ} {v : Ω}
    (hw : IsRecordWrite h t₀ τ₀ τ₁ w v) {t₀' τ₀' τ₁' w' : ℝ} {v' : Ω} (hstart : t₀' ≤ τ₁)
    (hlt : τ₁ < τ₀') (hend : τ₁' ≤ τ₁ + w) : ¬ IsRecordWrite h t₀' τ₀' τ₁' w' v' := by
  intro hw'
  have h1 : h τ₁ = v := hw.holds τ₁ le_rfl (by linarith [hw.window_nonneg])
  have h2 : h τ₁' = v := hw.holds τ₁' (by linarith [hw'.interval]) hend
  exact not_isRecordWrite_of_eq hstart hlt le_rfl (by linarith [hw'.window_nonneg])
    (h1.trans h2.symm) hw'

/-! ### The three kinds -/

/-- **A possible observation** of the arena: a measurable readout and nothing else. It can be
evaluated at any time; nothing need have been written. -/
structure Observation (X : Type*) [MeasurableSpace X] (Ω : Type*) [MeasurableSpace Ω] where
  /-- The readout. -/
  obs : X → Ω
  /-- It is measurable. -/
  measurable_obs : Measurable obs

/-- **An actual record occurrence** on the arena `X`, with values in `Ω` and sites in `Fin K`: the
carrier's evolution (a two-time, measurable dynamics), its readout, its ready set, the actual
preparation, the site of the carrier, the start, the recorded value, the write interval
`[writeStart, writeEnd]`, the window, and **the write itself, as a proof** along the history
`t ↦ readout (evolve start t prep)`. -/
structure ActualOccurrence (X : Type*) [MeasurableSpace X] (Ω : Type*) [MeasurableSpace Ω]
    (K : ℕ) where
  /-- The evolution producing the write. -/
  evolve : OnticTime → OnticTime → X → X
  /-- Nothing happens in no time. -/
  evolve_self : ∀ t, evolve t t = id
  /-- The two-time law. -/
  evolve_comp : ∀ s t u, evolve t u ∘ evolve s t = evolve s u
  /-- Each time-step is measurable. -/
  measurable_evolve : ∀ s t, Measurable (evolve s t)
  /-- The carrier's readout. -/
  readout : X → Ω
  /-- It is measurable. -/
  measurable_readout : Measurable readout
  /-- The ready-state condition. -/
  ready : Set X
  /-- It is measurable. -/
  measurableSet_ready : MeasurableSet ready
  /-- The actual preparation. -/
  prep : X
  /-- It is ready. -/
  prep_mem : prep ∈ ready
  /-- The site of the carrier. -/
  site : Finset (Fin K)
  /-- The start of the history. -/
  start : OnticTime
  /-- The recorded value. -/
  value : Ω
  /-- The write interval begins. -/
  writeStart : ℝ
  /-- The write interval ends. -/
  writeEnd : ℝ
  /-- The finite persistence window. -/
  window : ℝ
  /-- **The write**, discharged from the dynamics. -/
  isWrite : IsRecordWrite (fun t => readout (evolve start t prep)) start writeStart writeEnd window
    value

namespace ActualOccurrence

variable {X : Type*} [MeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω]

/-- The readout history of the occurrence. -/
def history (o : ActualOccurrence X Ω K) (t : ℝ) : Ω := o.readout (o.evolve o.start t o.prep)

theorem isRecordWrite_history (o : ActualOccurrence X Ω K) :
    IsRecordWrite o.history o.start o.writeStart o.writeEnd o.window o.value := o.isWrite

/-- Forget to kind 2: the readout alone. -/
def toObservation (o : ActualOccurrence X Ω K) : Observation X Ω := ⟨o.readout, o.measurable_readout⟩

/-- Forget to kind 3: the region is the carrier's site, the period is the supplied clock readout at
the completion of the write. -/
def toRecordEvent (o : ActualOccurrence X Ω K) (clk : X → ℕ) : RecordEvent K :=
  ⟨o.site, clk (o.evolve o.start o.writeEnd o.prep)⟩

theorem toRecordEvent_region (o : ActualOccurrence X Ω K) (clk : X → ℕ) :
    (o.toRecordEvent clk).region = o.site := rfl

/-- The record predicate: at the completion of the write, the carrier displays the value. -/
def recordSet (o : ActualOccurrence X Ω K) : Set X :=
  {x | o.readout (o.evolve o.start o.writeEnd x) = o.value}

theorem measurableSet_recordSet [MeasurableSingletonClass Ω] (o : ActualOccurrence X Ω K) :
    MeasurableSet o.recordSet :=
  (o.measurable_readout.comp (o.measurable_evolve _ _)) (measurableSet_singleton o.value)

/-- The actual preparation lies in the record predicate: the write happened. -/
theorem prep_mem_recordSet (o : ActualOccurrence X Ω K) : o.prep ∈ o.recordSet :=
  o.isWrite.holds o.writeEnd le_rfl (by linarith [o.isWrite.window_nonneg])

/-- The preparation displays the value throughout the window. -/
theorem history_eq_value (o : ActualOccurrence X Ω K) {t : ℝ} (h₁ : o.writeEnd ≤ t)
    (h₂ : t ≤ o.writeEnd + o.window) : o.history t = o.value := o.isWrite.holds t h₁ h₂

/-- Before the write interval the preparation does not display the value. -/
theorem history_ne_value (o : ActualOccurrence X Ω K) {t : ℝ} (h₁ : o.start ≤ t)
    (h₂ : t < o.writeStart) : o.history t ≠ o.value := o.isWrite.before t h₁ h₂

/-- **The macroscopic coordinate of a finite family of occurrences**: the pattern projection of their
record predicates. -/
noncomputable def recordPattern [MeasurableSingletonClass Ω] {k : ℕ}
    (os : Fin k → ActualOccurrence X Ω K) : MacroProjection X (Fin k → Bool) :=
  patternProjection (fun j => (os j).recordSet) fun j => (os j).measurableSet_recordSet

/-- ★ **Every record predicate of the family factors through the family's pattern projection.** -/
theorem factorsThrough_recordSet [MeasurableSingletonClass Ω] {k : ℕ}
    (os : Fin k → ActualOccurrence X Ω K) (i : Fin k) :
    FactorsThrough (recordPattern os) (os i).recordSet :=
  factorsThrough_patternMap (fun j => (os j).recordSet) i

end ActualOccurrence

/-! ### The arc readout of a register -/

open Classical in
/-- The readout of a two-outcome register: `0` or `1` when the pointer sits in that pointer arc,
`2` when it displays no record. -/
noncomputable def arcReadout (q : LF4.KTorus) : Fin 3 :=
  if q ∈ pointerArc 2 0 then 0 else if q ∈ pointerArc 2 1 then 1 else 2

theorem measurable_arcReadout : Measurable arcReadout := by
  unfold arcReadout
  exact Measurable.ite (measurableSet_pointerArc 0) measurable_const
    (Measurable.ite (measurableSet_pointerArc 1) measurable_const measurable_const)

theorem arcReadout_of_mem_zero {q : LF4.KTorus} (hq : q ∈ pointerArc 2 0) : arcReadout q = 0 := by
  unfold arcReadout
  exact ite_eq_left hq

theorem arcReadout_of_mem_one {q : LF4.KTorus} (hq : q ∈ pointerArc 2 1) : arcReadout q = 1 := by
  have h0 : q ∉ pointerArc 2 0 :=
    Set.disjoint_right.mp (pointerArc_pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)) hq
  unfold arcReadout
  rw [ite_eq_right h0, ite_eq_left hq]

/-- A pointer in the pointer arc of `b` reads `b`. -/
theorem arcReadout_of_mem {q : LF4.KTorus} {b : Fin 2} (hq : q ∈ pointerArc 2 b) :
    arcReadout q = Fin.castSucc b := by
  fin_cases b
  · exact arcReadout_of_mem_zero hq
  · exact arcReadout_of_mem_one hq

/-- A ready pointer displays no record. -/
theorem arcReadout_of_ready {q : LF4.KTorus} (hq : q ∈ readyArc 2) : arcReadout q = 2 := by
  have h0 : q ∉ pointerArc 2 0 := Set.disjoint_left.mp (readyArc_disjoint_pointerArc 0) hq
  have h1 : q ∉ pointerArc 2 1 := Set.disjoint_left.mp (readyArc_disjoint_pointerArc 1) hq
  unfold arcReadout
  rw [ite_eq_right h0, ite_eq_right h1]

theorem castSucc_ne_two (b : Fin 2) : (Fin.castSucc b : Fin 3) ≠ 2 := by
  fin_cases b <;> decide

/-! ### Instance: the three registers of the recorded exchange (#186) -/

/-- A register of the exchange is still ready before its readout time, from the preparation
`xPrep b c r` with ready registers (no condition on the clock is needed). -/
theorem xPrep_register_before {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) (i : Fin 3) {t : OnticTime}
    (ht : t < readTime J ħ i) : (xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i ∈ readyArc 2 := by
  rw [xEvolve_register, arrived_of_lt ht,
    arrived_of_lt (show (-1 : ℝ) < readTime J ħ i by linarith [readTime_nonneg hJ hħ i]),
    sub_self, zero_mul, pshift_zero]
  exact hr i

/-- **Register `i` of the recorded exchange as an actual occurrence**: carrier the register, readout
its arc, ready set its ready arc, preparation `xPrep b c r`, site `readSite i`, a sharp write at the
readout time with any window `w ≥ 0` — the write discharged from `register_written`. -/
noncomputable def exchangeRegister {J ħ : ℝ} (T : ℝ) (hJ : 0 < J) (hħ : 0 < ħ) (i : Fin 3)
    (b : Fin 2) (c : ClockArena K) {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {w : ℝ}
    (hw : 0 ≤ w) : ActualOccurrence (XArena K) (Fin 3) 2 where
  evolve := xEvolve J ħ T
  evolve_self := xEvolve_self J ħ T
  evolve_comp := xEvolve_comp J ħ T
  measurable_evolve := measurable_xEvolve J ħ T
  readout x := arcReadout (x.2.2 i)
  measurable_readout :=
    measurable_arcReadout.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
  ready := {x | x.2.2 i ∈ readyArc 2}
  measurableSet_ready :=
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) measurableSet_readyArc
  prep := xPrep b c r
  prep_mem := hr i
  site := {readSite i}
  start := -1
  value := Fin.castSucc b
  writeStart := readTime J ħ i
  writeEnd := readTime J ħ i
  window := w
  isWrite :=
    { start_le := by linarith [readTime_nonneg hJ hħ i]
      interval := le_rfl
      window_nonneg := hw
      before := fun t _ ht => by
        rw [arcReadout_of_ready (xPrep_register_before hJ hħ hr b i ht)]
        exact (castSucc_ne_two b).symm
      holds := fun t ht _ => arcReadout_of_mem (register_written hJ hħ hr b i ht) }

/-- The forgetful image of the emission register is #186's `eventOf` of the emission. -/
theorem toRecordEvent_exchangeRegister_zero {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2)
    (c : ClockArena K) {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {w : ℝ} (hw : 0 ≤ w) :
    (exchangeRegister T hJ hħ 0 b c hr hw).toRecordEvent (fun x => tickCount x.2.1)
      = eventOf J ħ T (xPrep b c r) (emission b) := rfl

/-- The forgetful image of the reception register is #186's `eventOf` of the reception. -/
theorem toRecordEvent_exchangeRegister_one {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2)
    (c : ClockArena K) {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {w : ℝ} (hw : 0 ≤ w) :
    (exchangeRegister T hJ hħ 1 b c hr hw).toRecordEvent (fun x => tickCount x.2.1)
      = eventOf J ħ T (xPrep b c r) (reception J ħ b) := rfl

/-- The forgetful image of the return register is #186's `eventOf` of the return. -/
theorem toRecordEvent_exchangeRegister_two {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2)
    (c : ClockArena K) {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {w : ℝ} (hw : 0 ≤ w) :
    (exchangeRegister T hJ hħ 2 b c hr hw).toRecordEvent (fun x => tickCount x.2.1)
      = eventOf J ħ T (xPrep b c r) (returnOcc J ħ b) := rfl

/-- ★ **After its readout a register of the exchange admits no further write**: for every candidate
write interval starting after the readout time, from any start at or before it, the register's
history is not a write of any value. Reading the register again is not an occurrence. -/
theorem exchange_no_second_write {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (i : Fin 3) (b : Fin 2)
    (c : ClockArena K) {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {t₀' τ₀' τ₁' w' : ℝ}
    {v' : Fin 3} (hstart : t₀' ≤ readTime J ħ i) (hlt : readTime J ħ i < τ₀') :
    ¬ IsRecordWrite (fun t => arcReadout ((xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i)) t₀' τ₀' τ₁' w'
      v' := by
  intro hw'
  have h1 : arcReadout ((xEvolve J ħ T (-1) (readTime J ħ i) (xPrep b c r)).2.2 i)
      = Fin.castSucc b := arcReadout_of_mem (register_written hJ hħ hr b i le_rfl)
  have h2 : arcReadout ((xEvolve J ħ T (-1) τ₁' (xPrep b c r)).2.2 i) = Fin.castSucc b :=
    arcReadout_of_mem (register_written hJ hħ hr b i (by linarith [hw'.interval]))
  exact not_isRecordWrite_of_eq hstart hlt le_rfl (by linarith [hw'.window_nonneg])
    (h1.trans h2.symm) hw'

/-! ### Instance: the slots of the record clock (#185) -/

open Classical in
/-- The readout of slot `n`: whether it has been written. -/
noncomputable def slotReadout (n : Fin K) (x : ClockArena K) : Bool :=
  if x.2 n ∈ writtenArc K then true else false

theorem measurable_slotReadout (n : Fin K) : Measurable (slotReadout n) := by
  unfold slotReadout
  exact Measurable.ite (((measurable_pi_apply n).comp measurable_snd) measurableSet_writtenArc)
    measurable_const measurable_const

/-- **Slot `n` of the record clock as an actual occurrence**: the write interval is the window
`[nT, (n+1)T]` of #185, the value `true`, any window `w ≥ 0`; the site is the supplied label. -/
noncomputable def clockSlot (hK : 0 < K) {T : ℝ} (hT : 0 < T) (n : Fin K) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {w : ℝ} (hw : 0 ≤ w) {L : ℕ} (site : Finset (Fin L)) :
    ActualOccurrence (ClockArena K) Bool L where
  evolve := clockEvolve T
  evolve_self := clockEvolve_self T
  evolve_comp := clockEvolve_comp T
  measurable_evolve := measurable_clockEvolve T
  readout := slotReadout n
  measurable_readout := measurable_slotReadout n
  ready := ClockReady K
  measurableSet_ready := measurableSet_clockReady
  prep := c
  prep_mem := hc
  site := site
  start := 0
  value := true
  writeStart := (n : ℕ) * T
  writeEnd := ((n : ℕ) + 1) * T
  window := w
  isWrite :=
    { start_le := mul_nonneg (Nat.cast_nonneg _) hT.le
      interval := by rw [add_mul, one_mul]; linarith [hT.le]
      window_nonneg := hw
      before := fun t _ ht => by
        have hmem := slot_ready_before hT hc n ht.le
        have hnot : (clockEvolve T 0 t c).2 n ∉ writtenArc K :=
          Set.disjoint_left.mp readyArc_disjoint_writtenArc hmem
        unfold slotReadout
        rw [ite_eq_right hnot]
        decide
      holds := fun t ht _ => by
        unfold slotReadout
        exact ite_eq_left (slot_written_after hK hT hc n ht) }

/-! ### The chain of #190: readouts at the sites, then registers at the sites -/

variable {n : ℕ}

/-- The bit read off a chain state at site `k`: its occupancy weight, thresholded at `1/2`. -/
noncomputable def chainReadBit (k : Fin (n + 1)) (p : FieldArena (n + 1) 2) : Fin 2 :=
  if 1 / 2 ≤ momentMap p (excAt k) then 1 else 0

theorem measurable_chainReadBit (k : Fin (n + 1)) : Measurable (chainReadBit k) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_momentMap (excAt k))) measurable_const
    measurable_const

/-- **The receiver readout at site `k` is a possible observation** of the chain arena — kind 2, which
is all the chain of #190 has at its sites. -/
noncomputable def receiverObservation (k : Fin (n + 1)) : Observation (ChainArena n K) (Fin 2) :=
  ⟨fun x => chainReadBit k x.1, (measurable_chainReadBit k).comp measurable_fst⟩

/-- The occupancy weight at site `k` is the arena observable of `occAt k`. -/
theorem momentMap_eq_arenaObs_occAt (k : Fin (n + 1)) (p : FieldArena (n + 1) 2) :
    momentMap p (excAt k) = arenaObs (occAt k) p := by
  conv_rhs => rw [← p.mk_rep]
  rw [occAt, arenaObs_single_mk]
  rfl

/-- At `k τ_hop` the readout at site `k` of message `1` is `1`. -/
theorem chainReadBit_one {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (k : Fin (n + 1)) :
    chainReadBit k (chainArenaFlow J ħ ((k : ℕ) * hopTime J ħ) (chainMsg n 1)) = 1 := by
  unfold chainReadBit
  rw [momentMap_eq_arenaObs_occAt, chainReadout_one hJ hħ (Nat.le_of_lt_succ k.isLt) k, Fin.eta,
    ite_eq_left rfl]
  norm_num

/-- At every time the readout at site `k` of message `0` is `0`. -/
theorem chainReadBit_zero (J ħ t : ℝ) (k : Fin (n + 1)) :
    chainReadBit k (chainArenaFlow J ħ t (chainMsg n 0)) = 0 := by
  unfold chainReadBit
  rw [momentMap_eq_arenaObs_occAt, chainReadout_zero]
  norm_num

/-- **The chain arena with a reception register at every site.** -/
abbrev ChainXArena (n K : ℕ) := ChainArena n K × (Fin (n + 1) → LF4.KTorus)

/-- The bit register `k` reads: the occupancy of site `k` in the exchange state at `k τ_hop`, when
the propagator starts at `s`. -/
noncomputable def chainReadAt (J ħ : ℝ) (k : Fin (n + 1)) (s : OnticTime) (p : FieldArena (n + 1) 2) :
    Fin 2 :=
  chainReadBit k (arenaKick ((chainSchedule n J ħ).evolve s ((k : ℕ) * hopTime J ħ)) p)

/-- The bit read at `k τ_hop` does not depend on where the propagator is cut. -/
theorem chainReadAt_evolve (J ħ : ℝ) (k : Fin (n + 1)) (s t : OnticTime) (p : FieldArena (n + 1) 2) :
    chainReadAt J ħ k t (arenaKick ((chainSchedule n J ħ).evolve s t) p) = chainReadAt J ħ k s p := by
  unfold chainReadAt
  rw [← arenaKick_mul, Schedule.evolve_comp]

theorem measurable_chainReadAt (J ħ : ℝ) (k : Fin (n + 1)) (s : OnticTime) :
    Measurable (chainReadAt J ħ k s) :=
  (measurable_chainReadBit k).comp (measurable_chainKick _)

/-- **The joint two-time propagator with registers**: the chain of #190, and register `k` translated
by `shearAmt 2 (bit)` on the crossing of `k τ_hop`, the bit read off the exchange state then. -/
noncomputable def chainXEvolve (J ħ T : ℝ) (s t : OnticTime) : ChainXArena n K → ChainXArena n K :=
  fun x => (chainEvolve J ħ T s t x.1,
    fun k => pshift ((arrived ((k : ℕ) * hopTime J ħ) t - arrived ((k : ℕ) * hopTime J ħ) s)
      * shearAmt 2 (chainReadAt J ħ k s x.1.1)) (x.2 k))

theorem chainXEvolve_fst (J ħ T : ℝ) (s t : OnticTime) (x : ChainXArena n K) :
    (chainXEvolve J ħ T s t x).1 = chainEvolve J ħ T s t x.1 := rfl

theorem chainXEvolve_register (J ħ T : ℝ) (s t : OnticTime) (x : ChainXArena n K) (k : Fin (n + 1)) :
    (chainXEvolve J ħ T s t x).2 k
      = pshift ((arrived ((k : ℕ) * hopTime J ħ) t - arrived ((k : ℕ) * hopTime J ħ) s)
          * shearAmt 2 (chainReadAt J ħ k s x.1.1)) (x.2 k) := rfl

theorem chainXEvolve_self (J ħ T : ℝ) (t : OnticTime) :
    chainXEvolve (n := n) (K := K) J ħ T t t = id := by
  funext x
  simp [chainXEvolve, chainEvolve_self]

/-- ★ **The two-time composition law on the arena with registers.** -/
theorem chainXEvolve_comp (J ħ T : ℝ) (s t u : OnticTime) :
    chainXEvolve (n := n) (K := K) J ħ T t u ∘ chainXEvolve J ħ T s t = chainXEvolve J ħ T s u := by
  funext x
  simp only [Function.comp_apply, chainXEvolve]
  refine Prod.ext ?_ ?_
  · exact congrFun (chainEvolve_comp J ħ T s t u) x.1
  · funext k
    simp only
    rw [chainEvolve_exchange, chainReadAt_evolve, pshift_add]
    congr 1
    ring

theorem measurable_chainXEvolve (J ħ T : ℝ) (s t : OnticTime) :
    Measurable (chainXEvolve (n := n) (K := K) J ħ T s t) := by
  refine Measurable.prodMk ((measurable_chainEvolve J ħ T s t).comp measurable_fst)
    (measurable_pi_iff.mpr fun k => ?_)
  have hcoef : Measurable fun x : ChainXArena n K =>
      (arrived ((k : ℕ) * hopTime J ħ) t - arrived ((k : ℕ) * hopTime J ħ) s)
        * shearAmt 2 (chainReadAt J ħ k s x.1.1) :=
    measurable_const.mul ((Measurable.of_discrete (f := shearAmt 2)).comp
      ((measurable_chainReadAt J ħ k s).comp (measurable_fst.comp measurable_fst)))
  exact continuous_pshift_uncurry.measurable.comp
    (hcoef.prodMk ((measurable_pi_apply k).comp measurable_snd))

/-- ★ **The joint propagator preserves Liouville measure** — the measure of #190 on the chain arena,
Haar on every register: a skew product over the chain arena, since the register shifts depend on the
exchange state. -/
theorem chainXEvolve_measurePreserving (J ħ T : ℝ) (s t : OnticTime) (p₀ : FieldArena (n + 1) 2) :
    MeasurePreserving (chainXEvolve (n := n) (K := K) J ħ T s t)
      (((fsMeasure p₀).prod volume).prod volume) (((fsMeasure p₀).prod volume).prod volume) := by
  have hfib : ∀ a : ChainArena n K, MeasurePreserving
      (fun r : Fin (n + 1) → LF4.KTorus => fun k : Fin (n + 1) =>
        pshift ((arrived ((k : ℕ) * hopTime J ħ) t - arrived ((k : ℕ) * hopTime J ħ) s)
          * shearAmt 2 (chainReadAt J ħ k s a.1)) (r k)) volume volume := by
    intro a
    rw [volume_pi]
    exact measurePreserving_pi _ _ fun k => measurePreserving_pshift _
  have hgm : Measurable (Function.uncurry fun (a : ChainArena n K) (r : Fin (n + 1) → LF4.KTorus) =>
      fun k : Fin (n + 1) =>
        pshift ((arrived ((k : ℕ) * hopTime J ħ) t - arrived ((k : ℕ) * hopTime J ħ) s)
          * shearAmt 2 (chainReadAt J ħ k s a.1)) (r k)) := by
    refine measurable_pi_iff.mpr fun k => ?_
    have hcoef : Measurable fun x : ChainArena n K × (Fin (n + 1) → LF4.KTorus) =>
        (arrived ((k : ℕ) * hopTime J ħ) t - arrived ((k : ℕ) * hopTime J ħ) s)
          * shearAmt 2 (chainReadAt J ħ k s x.1.1) :=
      measurable_const.mul ((Measurable.of_discrete (f := shearAmt 2)).comp
        ((measurable_chainReadAt J ħ k s).comp (measurable_fst.comp measurable_fst)))
    exact continuous_pshift_uncurry.measurable.comp
      (hcoef.prodMk ((measurable_pi_apply k).comp measurable_snd))
  exact (chainEvolve_measurePreserving J ħ T s t p₀).skew_product hgm
    (Filter.Eventually.of_forall fun a => (hfib a).map_eq)

/-! ### What the chain registers read and write -/

/-- The preparation with message `b`: the chain preparation and the registers `r`. -/
noncomputable def chainXPrep (b : Fin 2) (c : Fin (n + 1) → ClockArena K)
    (r : Fin (n + 1) → LF4.KTorus) : ChainXArena n K :=
  (chainPrep b c, r)

/-- From a start before the switch-on, the exchange factor at `k τ_hop` is the scheduled arena
flow. -/
theorem chainReadAt_neg_one (J ħ : ℝ) (k : Fin (n + 1)) (p : FieldArena (n + 1) 2) :
    chainReadAt J ħ k (-1) p = chainReadBit k (chainArenaFlow J ħ ((k : ℕ) * hopTime J ħ) p) := by
  unfold chainReadAt chainArenaFlow
  rw [Schedule.evolve, Schedule.propagator_of_nonpos (chainSchedule n J ħ) (t := -1) (by norm_num),
    inv_one, mul_one]

/-- ★ **Register `k` reads the message at `k τ_hop`**: `1` for message `1` (the transfer), `0` for
message `0` (the vacuum never moves). -/
theorem chainReadAt_chainMsg {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (k : Fin (n + 1)) (b : Fin 2) :
    chainReadAt J ħ k (-1) (chainMsg n b) = b := by
  rw [chainReadAt_neg_one]
  fin_cases b
  · exact chainReadBit_zero J ħ _ k
  · exact chainReadBit_one hJ hħ k

/-- Before `k τ_hop` register `k` is still ready. -/
theorem chainRegister_before {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2)
    (c : Fin (n + 1) → ClockArena K) {r : Fin (n + 1) → LF4.KTorus} (hr : ∀ k, r k ∈ readyArc 2)
    (k : Fin (n + 1)) {t : OnticTime} (ht : t < (k : ℕ) * hopTime J ħ) :
    (chainXEvolve J ħ T (-1) t (chainXPrep b c r)).2 k ∈ readyArc 2 := by
  have hk : (0 : ℝ) ≤ (k : ℕ) * hopTime J ħ := mul_nonneg (Nat.cast_nonneg _) (hopTime_pos hJ hħ).le
  rw [chainXEvolve_register, arrived_of_lt ht, arrived_of_lt (by linarith), sub_self, zero_mul,
    pshift_zero]
  exact hr k

/-- ★★ **Register `k` is written with the message** from `k τ_hop` on, from the transmitted state:
the reception at site `k` is now a write with provenance, not a readout. -/
theorem chainRegister_written {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2)
    (c : Fin (n + 1) → ClockArena K) {r : Fin (n + 1) → LF4.KTorus} (hr : ∀ k, r k ∈ readyArc 2)
    (k : Fin (n + 1)) {t : OnticTime} (ht : (k : ℕ) * hopTime J ħ ≤ t) :
    (chainXEvolve J ħ T (-1) t (chainXPrep b c r)).2 k ∈ pointerArc 2 b := by
  have hk : (0 : ℝ) ≤ (k : ℕ) * hopTime J ħ := mul_nonneg (Nat.cast_nonneg _) (hopTime_pos hJ hħ).le
  rw [chainXEvolve_register, arrived_of_le ht, arrived_of_lt (by linarith), sub_zero, one_mul]
  change pshift (shearAmt 2 (chainReadAt J ħ k (-1) (chainMsg n b))) (r k) ∈ pointerArc 2 b
  rw [chainReadAt_chainMsg hJ hħ k b]
  exact pshift_shearAmt_mem_pointerArc b (hr k)

/-- After `k τ_hop` register `k` is frozen. -/
theorem chainRegister_frozen (J ħ T : ℝ) {s t : OnticTime} (k : Fin (n + 1))
    (hs : (k : ℕ) * hopTime J ħ ≤ s) (hst : s ≤ t) (x : ChainXArena n K) :
    (chainXEvolve J ħ T s t x).2 k = x.2 k := by
  rw [chainXEvolve_register, arrived_of_le hs, arrived_of_le (hs.trans hst), sub_self, zero_mul,
    pshift_zero]

/-- **Register `k` of the chain as an actual occurrence**: a sharp write at `k τ_hop` with the
message, from the ready preparation, any window `w ≥ 0`. -/
noncomputable def chainRegister {J ħ : ℝ} (T : ℝ) (hJ : 0 < J) (hħ : 0 < ħ) (k : Fin (n + 1))
    (b : Fin 2) (c : Fin (n + 1) → ClockArena K) {r : Fin (n + 1) → LF4.KTorus}
    (hr : ∀ k, r k ∈ readyArc 2) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (ChainXArena n K) (Fin 3) (n + 1) where
  evolve := chainXEvolve J ħ T
  evolve_self := chainXEvolve_self J ħ T
  evolve_comp := chainXEvolve_comp J ħ T
  measurable_evolve := measurable_chainXEvolve J ħ T
  readout x := arcReadout (x.2 k)
  measurable_readout := measurable_arcReadout.comp ((measurable_pi_apply k).comp measurable_snd)
  ready := {x | x.2 k ∈ readyArc 2}
  measurableSet_ready := ((measurable_pi_apply k).comp measurable_snd) measurableSet_readyArc
  prep := chainXPrep b c r
  prep_mem := hr k
  site := {k}
  start := -1
  value := Fin.castSucc b
  writeStart := (k : ℕ) * hopTime J ħ
  writeEnd := (k : ℕ) * hopTime J ħ
  window := w
  isWrite :=
    { start_le := by
        linarith [mul_nonneg (Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ _) (hopTime_pos hJ hħ).le]
      interval := le_rfl
      window_nonneg := hw
      before := fun t _ ht => by
        rw [arcReadout_of_ready (chainRegister_before hJ hħ b c hr k ht)]
        exact (castSucc_ne_two b).symm
      holds := fun t ht _ => arcReadout_of_mem (chainRegister_written hJ hħ b c hr k ht) }

/-- ★★★ **The chain's site events are the forgetful images of actual writes on the common arena.**
Under the calibration `T = τ_hop`, with the period read off the clock at site `k` — whose ticks are
writes themselves (`clockSlot`) — the actual occurrence of register `k` maps to `siteEvent k`, the
event #190's causal chain is built from. -/
theorem siteEvent_eq_toRecordEvent {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ)
    (hK : 0 < K) (hnK : n ≤ K) (k : Fin (n + 1)) (b : Fin 2) {c : Fin (n + 1) → ClockArena K}
    (hc : ∀ j, c j ∈ ClockReady K) {r : Fin (n + 1) → LF4.KTorus} (hr : ∀ k, r k ∈ readyArc 2)
    {w : ℝ} (hw : 0 ≤ w) :
    (chainRegister T hJ hħ k b c hr hw).toRecordEvent (fun x => tickCount (x.1.2 k)) = siteEvent k := by
  have hTpos : 0 < T := hT ▸ hopTime_pos hJ hħ
  unfold ActualOccurrence.toRecordEvent siteEvent
  congr 1
  change tickCount (clockEvolve T (-1) ((k : ℕ) * hopTime J ħ) (c k)) = k.val
  rw [tickCount_clock_neg_one hTpos, ← hT]
  exact tickCount_at_period hK hTpos (hc k) (le_trans (Nat.le_of_lt_succ k.isLt) hnK)

/-! ### The package -/

/-- ★★★ **The occurrence registry.** No carrier is written twice inside a write's window; the three
registers of the exchange and every clock slot are actual occurrences discharged from their
dynamics, the exchange's forgetful images being #186's events; the chain of #190 carries registers
on one two-time measure-preserving dynamics, each written with the message at `k τ_hop` and frozen
after, and the site events of #190's causal chain are the forgetful images of those writes, labelled
by the site's own clock. -/
theorem record_occurrences {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    (hnK : n ≤ K) {c : Fin (n + 1) → ClockArena K} (hc : ∀ j, c j ∈ ClockReady K)
    {r : Fin (n + 1) → LF4.KTorus} (hr : ∀ k, r k ∈ readyArc 2) {w : ℝ} (hw : 0 ≤ w) :
    (∀ (Ω : Type) (h : ℝ → Ω) (t₀ τ₀ τ₁ w₁ : ℝ) (v : Ω), IsRecordWrite h t₀ τ₀ τ₁ w₁ v →
        ∀ (t₀' τ₀' τ₁' w' : ℝ) (v' : Ω), t₀' ≤ τ₁ → τ₁ < τ₀' → τ₁' ≤ τ₁ + w₁ →
          ¬ IsRecordWrite h t₀' τ₀' τ₁' w' v')
      ∧ (∀ s t u : OnticTime,
          chainXEvolve (n := n) (K := K) J ħ T t u ∘ chainXEvolve J ħ T s t = chainXEvolve J ħ T s u)
      ∧ (∀ (s t : OnticTime) (p₀ : FieldArena (n + 1) 2),
          MeasurePreserving (chainXEvolve (n := n) (K := K) J ħ T s t)
            (((fsMeasure p₀).prod volume).prod volume) (((fsMeasure p₀).prod volume).prod volume))
      ∧ (∀ (b : Fin 2) (k : Fin (n + 1)) (t : OnticTime), (k : ℕ) * hopTime J ħ ≤ t →
          (chainXEvolve J ħ T (-1) t (chainXPrep b c r)).2 k ∈ pointerArc 2 b)
      ∧ (∀ (b : Fin 2) (k : Fin (n + 1)),
          (chainRegister T hJ hħ k b c hr hw).toRecordEvent (fun x => tickCount (x.1.2 k))
            = siteEvent k)
      ∧ (∀ (b : Fin 2) (k : Fin (n + 1)),
          FactorsThrough (ActualOccurrence.recordPattern fun j => chainRegister T hJ hħ j b c hr hw)
            (chainRegister T hJ hħ k b c hr hw).recordSet) :=
  ⟨fun _ _ _ _ _ _ _ hw' _ _ _ _ _ hs hl he => hw'.not_within hs hl he, chainXEvolve_comp J ħ T,
    fun s t p₀ => chainXEvolve_measurePreserving J ħ T s t p₀,
    fun b k _ ht => chainRegister_written hJ hħ b c hr k ht,
    fun b k => siteEvent_eq_toRecordEvent hJ hħ hT hK hnK k b hc hr hw,
    fun _ k => ActualOccurrence.factorsThrough_recordSet _ k⟩

end CSD.RecordLayer

end
