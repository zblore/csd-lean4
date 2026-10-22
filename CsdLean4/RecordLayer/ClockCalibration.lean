/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OperationalGeometry
public import CsdLean4.CV.CausalDistance

/-!
# Two clocks: calibration consistency, and clock time against chain length

**Category:** 7-SigmaLayer (the record layer — the second clock of the clock-and-echo programme).
BACKLOG #188 (out of #39; the sixth of #183–#189).

A second physical clock of the kind built in #185, on one arena with the first, with a product
evolution. Three questions, each answered with its hypothesis visible:

1. **Colocated clocks.** Two clocks of periods `T₁, T₂`, each **calibrated to its own period** — the
   justified calibration, since `abs_tickReading_sub_lt` says each then reads `t_Σ` to within one of
   its ticks — agree to within `T₁ + T₂` over the common horizon (★★ `colocated_agreement`). Under the
   **hypothesis** of equal rates `T₁ = T₂` they agree exactly at every tick boundary
   (`equal_rate_agreement_at_period`). A clock whose unit is not its period **drifts linearly** from
   `t_Σ` (`miscalibrated_drift`): calibration is necessary, not decorative, and nothing here reports
   agreement as a dynamical fact.
2. **A separated clock at the receiver.** A clock at `B`, calibrated to the hop time and **started at
   the switch-on together with `A`'s** — the synchronisation convention, stated as a hypothesis —
   reads, at the reception of the signal, exactly `A`'s radar time of that exchange
   (★★ `reception_reading_eq_radarTime`). The transmission delay is one tick, and `B` is one edge from
   `A` (`delay_eq_graph_separation`): in this witness the clock delay equals the graph separation.
3. **Clock time against the longest chain.** The clock's elapsed time from emission to return is `2`
   ticks (`elapsed_ticks_emission_return`), and the experiment's own chain
   `emission ≺ reception ≺ return` has two steps, so `causalDist ≥ 2` (`two_le_causalDist`). But
   `causalDist` is the longest chain over **all** record events, and inserting the event "both sites
   at period `1`" between emission and reception lengthens the chain to three
   (★★ `three_le_causalDist`): **the longest-chain separation exceeds the clock's elapsed time**, and
   the two agree only at the fixed resolution of the experiment's three events. This is the
   distinction the row asked for, proved on the witness rather than asserted.

## Honest scope

* ⚠️ Two sites only. For a longer chain of sites the relation between clock readings, per-edge
  delays and graph separation needs a sequentially activated coupling schedule that this corpus
  does not build; it is BACKLOG #190.
* The synchronisation of `B`'s clock with `A`'s is a hypothesis (common start at switch-on). It is
  the Einstein convention of this witness, not a derived fact; a different start shifts `B`'s
  reading by the offset, as `radarTime_shift` says of `A`'s.
* `causalDist` carries no resolution parameter; the "fixed resolution" statement is the pair of
  strict precedences of the experiment's three events, not a restricted distance.

References: `specs/BACKLOG.md` #188, #185, #187, #190, #39; `RecordLayer/RecordClock.lean`,
`RecordLayer/OperationalGeometry.lean`, `CV/CausalDistance.lean` (`causalDist`,
`causalDist_add_le`, `causalDist_pos_iff`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K K' : ℕ}

/-! ### Two clocks on one arena -/

/-- Two record clocks on one arena. -/
abbrev TwoClocks (K K' : ℕ) := ClockArena K × ClockArena K'

/-- The product evolution: each clock runs on its own period. -/
noncomputable def twoClockEvolve (T₁ T₂ : ℝ) (s t : OnticTime) :
    TwoClocks K K' → TwoClocks K K' :=
  Prod.map (clockEvolve T₁ s t) (clockEvolve T₂ s t)

theorem twoClockEvolve_self (T₁ T₂ : ℝ) (t : OnticTime) :
    twoClockEvolve (K := K) (K' := K') T₁ T₂ t t = id := by
  rw [twoClockEvolve, clockEvolve_self, clockEvolve_self, Prod.map_id]

theorem twoClockEvolve_comp (T₁ T₂ : ℝ) (s t u : OnticTime) :
    twoClockEvolve (K := K) (K' := K') T₁ T₂ t u ∘ twoClockEvolve T₁ T₂ s t
      = twoClockEvolve T₁ T₂ s u := by
  rw [twoClockEvolve, twoClockEvolve, twoClockEvolve, Prod.map_comp_map, clockEvolve_comp,
    clockEvolve_comp]

theorem measurable_twoClockEvolve (T₁ T₂ : ℝ) (s t : OnticTime) :
    Measurable (twoClockEvolve (K := K) (K' := K') T₁ T₂ s t) :=
  (measurable_clockEvolve T₁ s t).prodMap (measurable_clockEvolve T₂ s t)

theorem twoClockEvolve_measurePreserving (T₁ T₂ : ℝ) (s t : OnticTime) :
    MeasurePreserving (twoClockEvolve (K := K) (K' := K') T₁ T₂ s t) volume volume := by
  rw [twoClockEvolve, Measure.volume_eq_prod]
  exact (clockEvolve_measurePreserving T₁ s t).prod (clockEvolve_measurePreserving T₂ s t)

/-- The reading of the first clock, unit `τ₁`, at ontic time `t`. -/
noncomputable def reading₁ (T₁ T₂ τ₁ : ℝ) (x : TwoClocks K K') (t : OnticTime) : ℝ :=
  tickReading τ₁ (twoClockEvolve T₁ T₂ 0 t x).1

/-- The reading of the second clock, unit `τ₂`, at ontic time `t`. -/
noncomputable def reading₂ (T₁ T₂ τ₂ : ℝ) (x : TwoClocks K K') (t : OnticTime) : ℝ :=
  tickReading τ₂ (twoClockEvolve T₁ T₂ 0 t x).2

theorem reading₁_eq (T₁ T₂ τ₁ : ℝ) (x : TwoClocks K K') (t : OnticTime) :
    reading₁ T₁ T₂ τ₁ x t = tickReading τ₁ (clockEvolve T₁ 0 t x.1) := rfl

theorem reading₂_eq (T₁ T₂ τ₂ : ℝ) (x : TwoClocks K K') (t : OnticTime) :
    reading₂ T₁ T₂ τ₂ x t = tickReading τ₂ (clockEvolve T₂ 0 t x.2) := rfl

/-! ### Colocated clocks -/

/-- ★★ **Colocated clocks, each calibrated to its own period, agree to within `T₁ + T₂`** over the
common horizon. Both read `t_Σ` to within one of their own ticks; the bound is the sum. -/
theorem colocated_agreement (hK : 0 < K) (hK' : 0 < K') {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    {x : TwoClocks K K'} (hx₁ : x.1 ∈ ClockReady K) (hx₂ : x.2 ∈ ClockReady K') {t : OnticTime}
    (ht0 : 0 ≤ t) (ht₁ : t ≤ K * T₁) (ht₂ : t ≤ K' * T₂) :
    |reading₁ T₁ T₂ T₁ x t - reading₂ T₁ T₂ T₂ x t| < T₁ + T₂ := by
  rw [reading₁_eq, reading₂_eq]
  have h₁ := abs_tickReading_sub_lt hK hT₁ hx₁ ht0 ht₁
  have h₂ := abs_tickReading_sub_lt hK' hT₂ hx₂ ht0 ht₂
  rw [abs_sub_lt_iff] at h₁ h₂ ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **Under the hypothesis of equal rates**, two ready clocks agree exactly at every tick boundary
within both horizons (with a common unit `τ`). The equality of rates is assumed, not derived. -/
theorem equal_rate_agreement_at_period (hK : 0 < K) (hK' : 0 < K') {T : ℝ} (hT : 0 < T) (τ : ℝ)
    {x : TwoClocks K K'} (hx₁ : x.1 ∈ ClockReady K) (hx₂ : x.2 ∈ ClockReady K') {m : ℕ}
    (hm : m ≤ K) (hm' : m ≤ K') :
    reading₁ T T τ x (m * T) = reading₂ T T τ x (m * T) := by
  rw [reading₁_eq, reading₂_eq, tickReading, tickReading, tickCount_at_period hK hT hx₁ hm,
    tickCount_at_period hK' hT hx₂ hm']

/-- **A miscalibrated clock drifts linearly**: with unit `τ` instead of its period `T`, its reading
at the `m`-th tick boundary differs from `t_Σ` by exactly `m (τ − T)`. -/
theorem miscalibrated_drift (hK : 0 < K) {T : ℝ} (hT : 0 < T) (τ : ℝ) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {m : ℕ} (hm : m ≤ K) :
    tickReading τ (clockEvolve T 0 (m * T) c) - m * T = m * (τ - T) := by
  rw [tickReading, tickCount_at_period hK hT hc hm]
  ring

/-! ### A separated clock at the receiver -/

/-- ★★ **A clock at `B`, calibrated to the hop time and started at the switch-on with `A`'s, reads
`A`'s radar time of the exchange at the reception.** The common start is the synchronisation
convention, a hypothesis; the agreement is what it buys. -/
theorem reception_reading_eq_radarTime {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K)
    (hT : 0 < T) (hTcal : T = hopTime J ħ) (hτ : 0 ≤ τtick) {x : XArena K} (hx : x ∈ XReady K)
    (hK2 : 2 ≤ K) (hK' : 1 ≤ K') {cB : ClockArena K'} (hcB : cB ∈ ClockReady K') :
    tickReading τtick (clockEvolve T 0 (hopTime J ħ) cB)
      = (cycleReadings hJ hħ hK hT hτ hx 0).radarTime := by
  rw [radarTime_cycle hJ hħ hK hT hTcal hτ hx (by omega), tickReading, ← hTcal]
  have h := tickCount_at_period (Nat.lt_of_lt_of_le Nat.zero_lt_one hK') hT hcB (m := 1) hK'
  rw [Nat.cast_one, one_mul] at h
  rw [h]
  push_cast
  ring

/-- **The transmission delay is one tick and `B` is one edge from `A`**: `B` is outside the
zero-period cone of `A` and inside its one-period cone. In this witness the clock delay of the
signal equals the graph separation of the sites. -/
theorem delay_eq_graph_separation :
    (1 : Fin 2) ∉ graphBall hopGraph {0} 0 ∧ (1 : Fin 2) ∈ graphBall hopGraph {0} 1 := by
  constructor <;> decide

/-! ### Clock time against the longest chain -/

/-- The clock's elapsed time from emission to return is two ticks. -/
theorem elapsed_ticks_emission_return {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ)
    (hK : 2 ≤ K) {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    (eventOf J ħ T x (returnOcc J ħ b)).time - (eventOf J ħ T x (emission b)).time = 2 := by
  rw [eventOf_return hJ hħ hT hK hx b, eventOf_emission hJ hħ hT (by omega) hx b]
  rfl

theorem emission_ne_reception : (⟨{0}, 0⟩ : RecordEvent 2) ≠ ⟨{1}, 1⟩ := by
  intro h
  exact absurd (congrArg RecordEvent.time h) (by norm_num)

theorem reception_ne_return : (⟨{1}, 1⟩ : RecordEvent 2) ≠ ⟨{0}, 2⟩ := by
  intro h
  exact absurd (congrArg RecordEvent.time h) (by norm_num)

/-- **The experiment's own chain has two steps**: `causalDist ≥ 2`, matching the clock. -/
theorem two_le_causalDist {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 2 ≤ K)
    {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    2 ≤ causalDist hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (returnOcc J ħ b)) := by
  obtain ⟨h01, h12, _⟩ := causal_chain hJ hħ hT hK hx b
  rw [eventOf_emission hJ hħ hT (by omega) hx b, eventOf_reception hJ hħ hT (by omega) hx b,
    eventOf_return hJ hħ hT hK hx b] at *
  have hd1 : 0 < causalDist hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{1}, 1⟩ :=
    causalDist_pos_iff.mpr ⟨h01, emission_ne_reception⟩
  have hd2 : 0 < causalDist hopGraph (⟨{1}, 1⟩ : RecordEvent 2) ⟨{0}, 2⟩ :=
    causalDist_pos_iff.mpr ⟨h12, reception_ne_return⟩
  have := causalDist_add_le h01 h12
  omega

/-- The inserted event: both sites, at period `1`. -/
def bothSitesAtOne : RecordEvent 2 := ⟨{0, 1}, 1⟩

theorem emission_precedes_bothSites : CausalPrecedes hopGraph (⟨{0}, 0⟩ : RecordEvent 2) bothSitesAtOne := by
  refine ⟨Nat.zero_le _, ?_⟩
  show ({0, 1} : Finset (Fin 2)) ⊆ graphBall hopGraph {0} (1 - 0)
  decide

theorem bothSites_precedes_reception : CausalPrecedes hopGraph bothSitesAtOne (⟨{1}, 1⟩ : RecordEvent 2) := by
  refine ⟨le_rfl, ?_⟩
  show ({1} : Finset (Fin 2)) ⊆ graphBall hopGraph {0, 1} (1 - 1)
  decide

theorem emission_ne_bothSites : (⟨{0}, 0⟩ : RecordEvent 2) ≠ bothSitesAtOne := by
  intro h
  exact absurd (congrArg RecordEvent.time h) (by norm_num [bothSitesAtOne])

theorem bothSites_ne_reception : bothSitesAtOne ≠ (⟨{1}, 1⟩ : RecordEvent 2) := by
  intro h
  have := congrArg RecordEvent.region h
  simp [bothSitesAtOne] at this

/-- ★★ **Inserting an event lengthens the chain**: through "both sites at period `1`" the longest
chain from emission to return has at least three steps, while the clock's elapsed time is two
ticks. The longest-chain separation over all record events is not the clock time; they agree only
at the fixed resolution of the experiment's three events. -/
theorem three_le_causalDist {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 2 ≤ K)
    {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    3 ≤ causalDist hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (returnOcc J ħ b)) := by
  obtain ⟨_, h12, _⟩ := causal_chain hJ hħ hT hK hx b
  rw [eventOf_reception hJ hħ hT (by omega) hx b, eventOf_return hJ hħ hT hK hx b] at h12
  rw [eventOf_emission hJ hħ hT (by omega) hx b, eventOf_return hJ hħ hT hK hx b]
  have hd0 : 0 < causalDist hopGraph (⟨{0}, 0⟩ : RecordEvent 2) bothSitesAtOne :=
    causalDist_pos_iff.mpr ⟨emission_precedes_bothSites, emission_ne_bothSites⟩
  have hd1 : 0 < causalDist hopGraph bothSitesAtOne (⟨{1}, 1⟩ : RecordEvent 2) :=
    causalDist_pos_iff.mpr ⟨bothSites_precedes_reception, bothSites_ne_reception⟩
  have hd2 : 0 < causalDist hopGraph (⟨{1}, 1⟩ : RecordEvent 2) ⟨{0}, 2⟩ :=
    causalDist_pos_iff.mpr ⟨h12, reception_ne_return⟩
  have hA := causalDist_add_le emission_precedes_bothSites bothSites_precedes_reception
  have hB := causalDist_add_le (causalPrecedes_trans emission_precedes_bothSites
    bothSites_precedes_reception) h12
  omega

/-- **Clock time is not chain length**: the elapsed ticks are `2`, the longest chain is at least `3`. -/
theorem elapsed_ticks_ne_causalDist {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ)
    (hK : 2 ≤ K) {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    (eventOf J ħ T x (returnOcc J ħ b)).time - (eventOf J ħ T x (emission b)).time
      ≠ causalDist hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (returnOcc J ħ b)) := by
  rw [elapsed_ticks_emission_return hJ hħ hT hK hx b]
  have := three_le_causalDist hJ hħ hT hK hx b
  omega

/-! ### The package -/

/-- ★★ **Calibration consistency.** Colocated clocks calibrated to their own periods agree within
`T₁ + T₂`; equal rates give exact agreement at tick boundaries; a miscalibrated clock drifts
linearly; a synchronised clock at `B` reads `A`'s radar time at reception; the clock delay is one
tick and one edge; and the clock's elapsed time between emission and return is `2` while the
longest chain is at least `3`. -/
theorem clock_calibration (hK : 0 < K) (hK' : 0 < K') {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    {x : TwoClocks K K'} (hx₁ : x.1 ∈ ClockReady K) (hx₂ : x.2 ∈ ClockReady K') :
    (∀ t : OnticTime, 0 ≤ t → t ≤ K * T₁ → t ≤ K' * T₂ →
        |reading₁ T₁ T₂ T₁ x t - reading₂ T₁ T₂ T₂ x t| < T₁ + T₂)
      ∧ (∀ (τ : ℝ) (m : ℕ), m ≤ K → tickReading τ (clockEvolve T₁ 0 (m * T₁) x.1) - m * T₁
          = m * (τ - T₁))
      ∧ ((1 : Fin 2) ∉ graphBall hopGraph {0} 0 ∧ (1 : Fin 2) ∈ graphBall hopGraph {0} 1) :=
  ⟨fun _ ht0 ht₁ ht₂ => colocated_agreement hK hK' hT₁ hT₂ hx₁ hx₂ ht0 ht₁ ht₂,
    fun τ _ hm => miscalibrated_drift hK hT₁ τ hx₁ hm, delay_eq_graph_separation⟩

end CSD.RecordLayer

end
