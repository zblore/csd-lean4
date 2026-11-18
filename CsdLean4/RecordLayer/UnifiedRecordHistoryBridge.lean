/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRecordSpacetimeBridge
public import CsdLean4.SigmaLayer.MeasurementRecord

/-!
# Tick counts as recorded facts of the SigmaLayer

**Category:** 7-SigmaLayer (the record layer). BACKLOG #436 (Task 1 of the author's plan
"Unified records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R).

The radar theorem of M6 (`csd_operational_lorentz_from_records`, UD-201) speaks of tick counts,
`IsTickCount`: a property of one path. The SigmaLayer speaks of recorded facts, whose events
are measurable sets of ontic states (`RecordSemantics`), and of histories of them
(`compatibleSet`). This file joins the two for any dynamics with a continuous flow, and then
for the arena of the radar theorem. No new notion of record is introduced.

## Crossings and measurability

* `disp_time_mono`, ★★ `hasTicks_succ_iff` (**one more tick, through two rational times**: for
  disjoint resting and displaying sets the real times of a passage can be bracketed by
  rationals, and the strict order of the passages follows from the disjointness);
* `IsSigmaClosed` (a countable union of closed sets), `IsClosed.isSigmaClosed`,
  `IsSigmaClosed.preimage`; `hitSet`, ★ `isClosed_hitSet` (meeting a closed set during a closed
  interval of times is a closed condition on the start: projection along a compact interval),
  `measurableSet_hitSet`;
* ★★ `measurableSet_hasTicks`, ★★ `measurableSet_isTickCount` (**the starts whose path has the
  count `N` at `T` form a measurable set**, for a family of maps continuous in the time and the
  start together and resting and displaying sets that are disjoint countable unions of closed
  sets). The pointer arcs are half-open, neither open nor closed, which is why the statement is
  for countable unions of closed sets.

## The record semantics

* `tickSignature` (a context is a pointer and the length of the window of flow time over which
  its ticks are counted; an outcome is the number of ticks), `TickReadout`;
* `TickReadout.windowEvent`, `measurableSet_windowEvent`, `nowSemantics` (the event as a set of
  states at the reading), `semantics` (**the event as a set of initial states**: the preimage
  under the flow), ★ `mem_semantics_event_iff`, `startFact`, ★★ `mem_event_startFact`;
* ★★ `crossings_of_mem_event` (**a recorded count is a number of crossings of the orbit**);
* `model` (a `DeisolationModel`: the interaction is the flow, the outcome regions are the
  events at the reading), ★ `recordsEstablishedOutcome`, ★★ `establishedFact_eq_some_iff`
  (**flowing and reading establishes the fact exactly on its event**);
* ★★ `mem_compatibleSet_startFacts` (**counts of one orbit are a record history of it**).

## The radar arena

* `isSigmaClosed_repArc`, `isSigmaClosed_readyArc`, `isSigmaClosed_displayArc`;
* `isFiniteMeasure_pentaMuL`, `fiveCoupledFlow_zero`, `fiveCoupledFlow_add`,
  ★ `continuous_fiveCoupledFlow_prod`, `pentaDynamics` (the five-pointer arena as a
  `ConstraintDynamics`), `pentaPointer`, `continuous_pentaPointer`, `pentaReadout`;
* `wallDynamics`, `wallReadout`, `radarStart`, ★ `wallRunAt_eq_flow` (the walled chain's run is
  the orbit of its start under that dynamics), `radarHistory`, `WallRadarRecords`,
  ★★★ `WallRadarGeometry.records`;
* ★★★ `csd_radar_record_history` (**the radar family's five readings are a record history**:
  for the family and the open set of pointer angles of UD-201, the start of the run is in the
  compatible region of five recorded facts, each is established by flowing and reading, and
  their counts satisfy the Lorentz statement).

## Honest scope

⚠️ **Three things are kept apart.** (1) *A crossing of the trajectory*: given by the
radar theorem, restated by `crossings_of_mem_event`. (2) *A recorded fact describing it*: an event
of `semantics`, a measurable set of initial states, with `establishedFact` returning the fact
on it. This file proves (2) from (1). (3) *A persistent physical register holding the fact*:
not provided. The count is a property of a segment of the orbit. No coordinate of the arena
stores it, and the outcome region at the reading is defined by following the orbit backward.

⚠️ **No preparation.** The radar theorem fixes the carriers' rays and gives an open set of
pointer angles. A fixed ray has measure zero for `μ_FS`, so the compatible region found here
is not shown to have positive measure for the arena's measure `μ_FS ⊗ vol⁵`, and no
`HistoryPreparation` is built. That is Task 2 of the plan, and it is open.

⚠️ **The readout is defined, not built.** `model.readout` returns the count when there is
one; it is a function of the state through the flow, not a second apparatus. `TickReadout` is
inhabited by empty sets with every count `0`; what rules that out here is the radar theorem,
whose counts are of the order of `k` (UD-201).

⚠️ **The reading windows are in the flow time**, as in UD-201; the time of a fact is a flow
time.

References: `specs/BACKLOG.md` #436, ~~#432~~; `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UO-25, UD-201, UD-202, UD-208); `SigmaLayer/RecordedFact.lean` (`RecordSemantics`,
`compatibleSet`); `SigmaLayer/MeasurementRecord.lean` (`DeisolationModel`, `establishedFact`);
`SigmaLayer/IsolationPreparation.lean` (`HistoryPreparation`);
`RecordLayer/UnifiedDiracClockTicks.lean` (`HasTicks`, `IsTickCount`);
`RecordLayer/UnifiedRecordSpacetimeBridge.lean` (`IsTickCount.exists_crossings`,
`wallRunAt_orbit`); `RecordLayer/UnifiedRadarGeometry.lean`
(`csd_operational_lorentz_from_records`); `LF4/PentaCoupledFlow.lean`; `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.SigmaLayer MeasureTheory Set
open scoped ContDiff Manifold

namespace CSD.RecordLayer

universe u w

/-! ### Crossings of one path -/

section Paths

variable {X : Type*} {rest disp : Set X} {γ : ℝ → X}

/-- The display times of successive passages increase. -/
theorem disp_time_mono {T : ℝ} {n : ℕ} {a b : ℕ → ℝ}
    (h1 : ∀ i, i < n → 0 ≤ a i ∧ a i < b i ∧ b i ≤ T ∧ γ (a i) ∈ rest ∧ γ (b i) ∈ disp)
    (h2 : ∀ i, i + 1 < n → b i < a (i + 1)) : ∀ j, j < n → ∀ i, i ≤ j → b i ≤ b j := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    rw [Nat.le_zero.1 hi]
  | succ j ih =>
    intro hj i hi
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact le_rfl
    · have h3 := ih (by omega) i (by omega)
      have h4 := h2 j hj
      have h5 := (h1 (j + 1) hj).2.1
      linarith

/-- ★★ **One more tick, through two rational times.** For disjoint resting and displaying
sets, a path has `N + 1` ticks by `T` exactly when, for some rationals `q₁`, `q₂`, it has `N`
ticks by `q₁`, is in the resting set at some time of `[max q₁ 0, q₂]`, and is in the
displaying set at some time of `[q₂, T]`. The strict order of the passages is not asked for
on the right: two of the times can coincide only at a point of both sets. -/
theorem hasTicks_succ_iff (hd : Disjoint rest disp) (T : ℝ) (N : ℕ) :
    HasTicks rest disp γ T (N + 1) ↔ ∃ q₁ q₂ : ℚ, HasTicks rest disp γ q₁ N
      ∧ (∃ a ∈ Icc (max (q₁ : ℝ) 0) q₂, γ a ∈ rest) ∧ ∃ b ∈ Icc (q₂ : ℝ) T, γ b ∈ disp := by
  constructor
  · rintro ⟨a, b, h1, h2⟩
    have hmono := disp_time_mono h1 h2
    obtain ⟨hN0, hNab, hNT, hNr, hNd⟩ := h1 N (Nat.lt_succ_self N)
    obtain ⟨q₁, hq₁a, hq₁b⟩ : ∃ q₁ : ℚ, (q₁ : ℝ) < a N ∧ ∀ i, i < N → b i < q₁ := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · obtain ⟨q, hq⟩ := exists_rat_lt (a N)
        exact ⟨q, hq, fun i hi => absurd hi (by omega)⟩
      · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (h2 m (by omega))
        exact ⟨q, hq2, fun i hi => (hmono m (by omega) i (by omega)).trans_lt hq1⟩
    obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn hNab
    refine ⟨q₁, q₂, ⟨a, b, fun i hi => ?_, fun i hi => h2 i (by omega)⟩,
      ⟨a N, ⟨max_le hq₁a.le hN0, hq₂a.le⟩, hNr⟩, ⟨b N, ⟨hq₂b.le, hNT⟩, hNd⟩⟩
    obtain ⟨x1, x2, -, x4, x5⟩ := h1 i (by omega)
    exact ⟨x1, x2, (hq₁b i hi).le, x4, x5⟩
  · rintro ⟨q₁, q₂, ⟨a, b, h1, h2⟩, ⟨a', ⟨ha1, ha2⟩, har⟩, ⟨b', ⟨hb1, hb2⟩, hbd⟩⟩
    have hne : ∀ {s t : ℝ}, γ s ∈ rest → γ t ∈ disp → s ≠ t := fun hs ht hst =>
      Set.disjoint_left.1 hd hs (hst ▸ ht)
    have hq : (q₁ : ℝ) ≤ a' := (le_max_left _ _).trans ha1
    refine ⟨fun i => if i < N then a i else a', fun i => if i < N then b i else b',
      fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hiN : i < N
      · simp only [hiN, ↓reduceIte]
        obtain ⟨x1, x2, x3, x4, x5⟩ := h1 i hiN
        exact ⟨x1, x2, by linarith, x4, x5⟩
      · simp only [hiN, ↓reduceIte]
        exact ⟨(le_max_right _ _).trans ha1, lt_of_le_of_ne (ha2.trans hb1) (hne har hbd),
          hb2, har, hbd⟩
    · have hiN : i < N := by omega
      by_cases h' : i + 1 < N
      · simp only [hiN, h', ↓reduceIte]
        exact h2 i h'
      · simp only [hiN, h', ↓reduceIte]
        obtain ⟨-, -, x3, -, x5⟩ := h1 i hiN
        exact lt_of_le_of_ne (x3.trans hq) (hne har x5).symm

end Paths

/-! ### Measurability of the set of starts with a given count -/

section Measurability

variable {X : Type w} [TopologicalSpace X]

/-- **A countable union of closed sets.** -/
def IsSigmaClosed (S : Set X) : Prop := ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ S = ⋃ n, C n

theorem IsClosed.isSigmaClosed {S : Set X} (h : IsClosed S) : IsSigmaClosed S :=
  ⟨fun _ => S, fun _ => h, (iUnion_const S).symm⟩

/-- The preimage of a countable union of closed sets under a continuous map is one. -/
theorem IsSigmaClosed.preimage {Y : Type*} [TopologicalSpace Y] {S : Set Y}
    (h : IsSigmaClosed S) {f : X → Y} (hf : Continuous f) : IsSigmaClosed (f ⁻¹' S) := by
  obtain ⟨C, hC, rfl⟩ := h
  exact ⟨fun n => f ⁻¹' C n, fun n => (hC n).preimage hf, preimage_iUnion⟩

variable {F : ℝ → X → X}

/-- **The starts whose path meets `S` during `[s, t]`.** -/
def hitSet (F : ℝ → X → X) (S : Set X) (s t : ℝ) : Set X := {x | ∃ a ∈ Icc s t, F a x ∈ S}

/-- ★ **Meeting a closed set during a closed interval of times is a closed condition on the
start**, for a family of maps continuous in the time and the start together: the projection
along the compact interval is a closed map. -/
theorem isClosed_hitSet (hF : Continuous fun p : ℝ × X => F p.1 p.2) {S : Set X}
    (hS : IsClosed S) (s t : ℝ) : IsClosed (hitSet F S s t) := by
  have : CompactSpace (Icc s t) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc : IsClosed {p : Icc s t × X | F p.1 p.2 ∈ S} :=
    hS.preimage (hF.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  have h : hitSet F S s t = Prod.snd '' {p : Icc s t × X | F p.1 p.2 ∈ S} := by
    ext x
    constructor
    · rintro ⟨a, ha, hx⟩
      exact ⟨(⟨a, ha⟩, x), hx, rfl⟩
    · rintro ⟨⟨a, y⟩, hp, rfl⟩
      exact ⟨a.1, a.2, hp⟩
  rw [h]
  exact isClosedMap_snd_of_compactSpace _ hc

variable [MeasurableSpace X] [OpensMeasurableSpace X]

theorem measurableSet_hitSet (hF : Continuous fun p : ℝ × X => F p.1 p.2) {S : Set X}
    (hS : IsSigmaClosed S) (s t : ℝ) : MeasurableSet (hitSet F S s t) := by
  obtain ⟨C, hC, rfl⟩ := hS
  have h : hitSet F (⋃ n, C n) s t = ⋃ n, hitSet F (C n) s t := by
    ext x
    simp only [hitSet, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨a, ha, n, hn⟩
      exact ⟨n, a, ha, hn⟩
    · rintro ⟨n, a, ha, hn⟩
      exact ⟨a, ha, n, hn⟩
  rw [h]
  exact MeasurableSet.iUnion fun n => (isClosed_hitSet hF (hC n) s t).measurableSet

/-- ★★ **The starts whose path has `N` ticks by `T` form a measurable set**, for resting and
displaying sets that are disjoint countable unions of closed sets and a family of maps
continuous in the time and the start together. The times of the passages range over the
reals; `hasTicks_succ_iff` replaces them by two rationals for each tick. -/
theorem measurableSet_hasTicks (hF : Continuous fun p : ℝ × X => F p.1 p.2) {rest disp : Set X}
    (hr : IsSigmaClosed rest) (hp : IsSigmaClosed disp) (hd : Disjoint rest disp) (N : ℕ) :
    ∀ T : ℝ, MeasurableSet {x | HasTicks rest disp (fun t => F t x) T N} := by
  induction N with
  | zero =>
    intro T
    have h : {x | HasTicks rest disp (fun t => F t x) T 0} = univ :=
      eq_univ_of_forall fun x => hasTicks_zero rest disp (fun t => F t x) T
    rw [h]
    exact MeasurableSet.univ
  | succ N ih =>
    intro T
    have h : {x | HasTicks rest disp (fun t => F t x) T (N + 1)}
        = ⋃ q₁ : ℚ, ⋃ q₂ : ℚ, ({x | HasTicks rest disp (fun t => F t x) q₁ N}
            ∩ hitSet F rest (max (q₁ : ℝ) 0) q₂) ∩ hitSet F disp q₂ T := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, hitSet]
      rw [hasTicks_succ_iff hd]
      constructor
      · rintro ⟨q₁, q₂, h1, h2, h3⟩
        exact ⟨q₁, q₂, ⟨h1, h2⟩, h3⟩
      · rintro ⟨q₁, q₂, ⟨h1, h2⟩, h3⟩
        exact ⟨q₁, q₂, h1, h2, h3⟩
    rw [h]
    exact MeasurableSet.iUnion fun q₁ => MeasurableSet.iUnion fun q₂ =>
      ((ih q₁).inter (measurableSet_hitSet hF hr _ _)).inter (measurableSet_hitSet hF hp _ _)

/-- ★★ **The starts whose path has the count `N` at `T` form a measurable set.** -/
theorem measurableSet_isTickCount (hF : Continuous fun p : ℝ × X => F p.1 p.2)
    {rest disp : Set X} (hr : IsSigmaClosed rest) (hp : IsSigmaClosed disp)
    (hd : Disjoint rest disp) (T : ℝ) (N : ℕ) :
    MeasurableSet {x | IsTickCount rest disp (fun t => F t x) T N} :=
  (measurableSet_hasTicks hF hr hp hd N T).inter
    (measurableSet_hasTicks hF hr hp hd (N + 1) T).compl

end Measurability

/-! ### The record semantics of tick counts -/

/-- **The signature of tick readings.** A context is a pointer and the length of the window
of flow time over which its ticks are counted; an outcome is the number of ticks. -/
def tickSignature (ι : Type u) : RecordSignature := ⟨ι × ℝ, fun _ => ℕ⟩

variable {X : Type w} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **A tick readout of a dynamics**: for each pointer a resting set and a displaying set of
states, disjoint, each a countable union of closed sets; and the flow continuous in the time
and the state together.

It is inhabited by empty sets, with every count `0`: an instance says nothing by itself. -/
structure TickReadout (D : ConstraintDynamics X) (ι : Type u) where
  /-- The states in which pointer `i` rests. -/
  rest : ι → Set X
  /-- The states in which pointer `i` displays. -/
  disp : ι → Set X
  /-- The flow is continuous in the time and the state together. -/
  continuous_flow : Continuous fun p : ℝ × X => D.flow p.1 p.2
  rest_sigmaClosed : ∀ i, IsSigmaClosed (rest i)
  disp_sigmaClosed : ∀ i, IsSigmaClosed (disp i)
  disjoint : ∀ i, Disjoint (rest i) (disp i)

namespace TickReadout

variable {D : ConstraintDynamics X} {ι : Type u} (A : TickReadout D ι)

/-- **The states whose last `W` of flow time holds `N` ticks of pointer `i`.** A condition
on the state at the reading: its orbit is followed backward for `W`. -/
def windowEvent (i : ι) (W : ℝ) (N : ℕ) : Set X :=
  {y | IsTickCount (A.rest i) (A.disp i) (fun s => D.flow (s - W) y) W N}

theorem measurableSet_windowEvent (i : ι) (W : ℝ) (N : ℕ) :
    MeasurableSet (A.windowEvent i W N) :=
  measurableSet_isTickCount (F := fun s y => D.flow (s - W) y)
    (A.continuous_flow.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd))
    (A.rest_sigmaClosed i) (A.disp_sigmaClosed i) (A.disjoint i) W N

/-- **The semantics at the reading.** The fact "pointer `i` counted `N` over the window `W`"
is the set of states whose last `W` of flow time holds `N` ticks. It does not depend on the
time of the fact. -/
def nowSemantics : RecordSemantics X (tickSignature ι) where
  event r := A.windowEvent r.context.1 r.context.2 r.outcome
  measurable_event _ := A.measurableSet_windowEvent _ _ _
  exclusive _ _ _ _ _ ha hb := IsTickCount.unique ha hb

/-- **The semantics on initial states.** The fact "pointer `i` counted `N` over the window
`W` ending at the flow time `t`" is the set of initial states that the flow carries at `t`
into the event at the reading. -/
def semantics : RecordSemantics X (tickSignature ι) where
  event r := D.flow r.time ⁻¹' A.windowEvent r.context.1 r.context.2 r.outcome
  measurable_event _ := D.measurable_flow _ (A.measurableSet_windowEvent _ _ _)
  exclusive _ _ _ _ _ ha hb := IsTickCount.unique ha hb

/-- ★ **An initial state is in the event exactly when its own orbit has the count over the
window `[t − W, t]`.** -/
theorem mem_semantics_event_iff (i : ι) (W : ℝ) (N : ℕ) (t : ℝ) (x : X) :
    x ∈ A.semantics.event ⟨(i, W), N, t⟩
      ↔ IsTickCount (A.rest i) (A.disp i) (fun s => D.flow (s + (t - W)) x) W N := by
  have h : (fun s => D.flow (s - W) (D.flow t x)) = fun s => D.flow (s + (t - W)) x := by
    funext s
    rw [← D.flow_add]
    congr 1
    ring
  change IsTickCount (A.rest i) (A.disp i) (fun s => D.flow (s - W) (D.flow t x)) W N ↔ _
  rw [h]

/-- **The fact that pointer `i` counted `N` from the start until `T`.** -/
def startFact (i : ι) (T : ℝ) (N : ℕ) : RecordedFact (tickSignature ι) := ⟨(i, T), N, T⟩

/-- ★★ **The event of a count from the start is the count of the orbit**: an initial state
is in it exactly when `t ↦ Φ_t x` has the count `N` at `T`. -/
theorem mem_event_startFact (i : ι) (T : ℝ) (N : ℕ) (x : X) :
    x ∈ A.semantics.event (startFact i T N)
      ↔ IsTickCount (A.rest i) (A.disp i) (fun s => D.flow s x) T N := by
  rw [startFact, mem_semantics_event_iff]
  simp only [sub_self, add_zero]

/-- ★★ **A recorded count is a number of crossings of the orbit.** If an initial state is in
the event of the count `N` from the start until `T`, its orbit is in the resting set and then
in the displaying set `N` times in succession before `T`, and not `N + 1` times. -/
theorem crossings_of_mem_event (i : ι) (T : ℝ) (N : ℕ) (x : X)
    (h : x ∈ A.semantics.event (startFact i T N)) :
    (∃ a b : ℕ → ℝ,
      (∀ j, j < N → 0 ≤ a j ∧ a j < b j ∧ b j ≤ T ∧ D.flow (a j) x ∈ A.rest i
          ∧ D.flow (b j) x ∈ A.disp i)
        ∧ ∀ j, j + 1 < N → b j < a (j + 1))
      ∧ ¬ HasTicks (A.rest i) (A.disp i) (fun s => D.flow s x) T (N + 1) :=
  ((A.mem_event_startFact i T N x).1 h).exists_crossings

open Classical in
/-- **The de-isolation model of tick readings.** The interaction at the flow time `t` is the
flow for `t`. The outcome region of the count `N` in the context `(i, W)` is the event at the
reading. The readout gives the count when there is one. -/
def model : DeisolationModel D (tickSignature ι) A.nowSemantics PUnit.{1} where
  interaction t _ := D.flow t
  measurable_interaction t _ := D.measurable_flow t
  interaction_preserves t _ := D.flow_preserves t
  outcomeRegion _ c N := A.windowEvent c.1 c.2 N
  measurable_outcomeRegion _ c N := A.measurableSet_windowEvent c.1 c.2 N
  pairwise_disjoint _ c := fun N _ N' _ hne =>
    Set.disjoint_left.2 fun _ h h' => hne (IsTickCount.unique h h')
  readout _ c y := if h : ∃ N, y ∈ A.windowEvent c.1 c.2 N then some h.choose else none
  readout_eq_some_iff _ c y N := by
    constructor
    · intro h
      split_ifs at h with hex
      · rw [← Option.some.inj h]
        exact hex.choose_spec
    · intro h
      split_ifs with hex
      · exact congrArg some (IsTickCount.unique hex.choose_spec h)
      · exact absurd ⟨N, h⟩ hex

/-- ★ **A readout that gives a count leaves the state in that count's event** (the B5
predicate of the interface, for this model). -/
theorem recordsEstablishedOutcome : A.model.RecordsEstablishedOutcome :=
  fun p c _ x N h => (A.model.readout_eq_some_iff p c (D.flow _ x) N).1 h

/-- ★★ **The established fact is the fact, exactly on its event.** Flowing an initial state
for `t` and reading pointer `i` over the window `W` establishes the fact `⟨(i, W), N, t⟩`
exactly when the initial state is in that fact's event. -/
theorem establishedFact_eq_some_iff (i : ι) (W : ℝ) (N : ℕ) (t : ℝ) (x : X) :
    A.model.establishedFact PUnit.unit (i, W) t x = some ⟨(i, W), N, t⟩
      ↔ x ∈ A.semantics.event ⟨(i, W), N, t⟩ := by
  change (A.model.readout PUnit.unit (i, W) (D.flow t x)).map
      (fun N' => (⟨(i, W), N', t⟩ : RecordedFact (tickSignature ι))) = some ⟨(i, W), N, t⟩ ↔ _
  constructor
  · intro h
    obtain ⟨N', hN', hfact⟩ := Option.map_eq_some_iff.1 h
    cases hfact
    exact (A.model.readout_eq_some_iff PUnit.unit (i, W) (D.flow t x) N).1 hN'
  · intro h
    rw [(A.model.readout_eq_some_iff PUnit.unit (i, W) (D.flow t x) N).2 h]
    rfl

/-- ★★ **Counts of one orbit are a record history of it.** If the orbit of `x` has the count
`r.2.2` of pointer `r.1` at `r.2.1` for every entry of a list, then `x` is in the compatible
region of the history of those facts. -/
theorem mem_compatibleSet_startFacts (l : List (ι × ℝ × ℕ)) (x : X)
    (h : ∀ r ∈ l, IsTickCount (A.rest r.1) (A.disp r.1) (fun s => D.flow s x) r.2.1 r.2.2) :
    x ∈ compatibleSet A.semantics (l.map fun r => startFact r.1 r.2.1 r.2.2) := by
  rw [mem_compatibleSet]
  intro f hf
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
  exact (A.mem_event_startFact r.1 r.2.1 r.2.2 x).2 (h r hr)

end TickReadout

/-! ### The pointer arcs -/

/-- An arc `{rep ∈ (a, b]}` of the first angle is a countable union of closed sets. -/
theorem isSigmaClosed_repArc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    IsSigmaClosed {q : LF4.KTorus | rep q.1 ∈ Ioc a b} := by
  refine ⟨fun n : ℕ => Prod.fst ⁻¹' ((fun y : ℝ => (y : CircleFibre)) ''
    Icc (a + 1 / ((n : ℝ) + 1)) b), fun n => ?_, ?_⟩
  · exact ((isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed).preimage
      continuous_fst
  · ext q
    constructor
    · intro hq
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hq.1)
      exact mem_iUnion.2 ⟨n, rep q.1, ⟨by linarith, hq.2⟩, coe_rep q.1⟩
    · intro hq
      obtain ⟨n, y, ⟨hy1, hy2⟩, hyq⟩ := mem_iUnion.1 hq
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hy : rep q.1 = y := by
        rw [← hyq]
        exact rep_coe_of_mem_Ioc ⟨by linarith, hy2.trans hb⟩
      change rep q.1 ∈ Ioc a b
      rw [hy]
      exact ⟨by linarith, hy2⟩

theorem isSigmaClosed_readyArc : IsSigmaClosed (readyArc 2) :=
  isSigmaClosed_repArc le_rfl (by rw [shearWidth_two]; norm_num)

theorem isSigmaClosed_displayArc : IsSigmaClosed displayArc :=
  isSigmaClosed_repArc (by rw [shearWidth_two]; norm_num) (by rw [shearWidth_two]; norm_num)

/-! ### The five-pointer arena as a dynamics with a tick readout -/

section Penta

open CSD.LF4

variable {N : ℕ} {A BA BB BC BD BE : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
  {f g k l r : ℝ → ℝ}

theorem isFiniteMeasure_pentaMuL (p₀ : CPN (N + 1)) : IsFiniteMeasure (pentaMuL p₀) := by
  unfold pentaMuL quadMuL triMuL echoMuL
  infer_instance

variable (A BA BB BC BD BE) in
/-- The five-pointer flow at the flow time `0` is the identity. -/
theorem fiveCoupledFlow_zero (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (x : PentaSigma N) :
    fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr 0 x = x :=
  integralFlow_zero ((pentaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_fiveCoupledEnergy A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr)) x

variable (A BA BB BC BD BE) in
/-- The five-pointer flow is a one-parameter group. -/
theorem fiveCoupledFlow_add (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (s t : ℝ) (x : PentaSigma N) :
    fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr (s + t) x
      = fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr s
          (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t x) :=
  integralFlow_add ((pentaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_fiveCoupledEnergy A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr)) s t x

variable (A BA BB BC BD BE) in
/-- ★ **The five-pointer flow is continuous in the flow time and the state together.** -/
theorem continuous_fiveCoupledFlow_prod (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) :
    Continuous fun p : ℝ × PentaSigma N =>
      fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr p.1 p.2 :=
  continuous_integralFlow ((pentaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_fiveCoupledEnergy A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr))

set_option synthInstance.maxSize 4096 in
/-- **The five-pointer arena as a `ConstraintDynamics`**: the Hamiltonian flow of
`fiveCoupledEnergy` for `pentaForm`, with the measure `μ_FS ⊗ vol⁵`. The group law is the
flow's; the measure is preserved for Hermitian matrices (`pentaMuL_map_fiveCoupledFlow`). -/
def pentaDynamics (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hBC : BC.IsHermitian) (hBD : BD.IsHermitian) (hBE : BE.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (hcr : ContDiff ℝ ∞ r) (p₀ : CPN (N + 1)) : ConstraintDynamics (PentaSigma N) where
  muL := ⟨pentaMuL p₀, isFiniteMeasure_pentaMuL p₀⟩
  flow := fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr
  measurable_flow t := ((pentaForm_isSymplectic N).continuous_hamiltonianFlow _ t).measurable
  flow_zero x := fiveCoupledFlow_zero A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr x
  flow_add s t x :=
    fiveCoupledFlow_add A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr s t x
  flow_preserves t :=
    ⟨((pentaForm_isSymplectic N).continuous_hamiltonianFlow _ t).measurable,
      pentaMuL_map_fiveCoupledFlow hA hBA hBB hBC hBD hBE hf hg hk hl hr hc hcg hck hcl hcr
        p₀ t⟩

/-- **The five pointers of the arena**, in the order in which they were added. -/
def pentaPointer : Fin 5 → PentaSigma N → KTorus
  | 0, x => x.1.1.1.1.2
  | 1, x => x.1.1.1.2
  | 2, x => x.1.1.2
  | 3, x => x.1.2
  | 4, x => x.2

theorem continuous_pentaPointer : ∀ i : Fin 5, Continuous (pentaPointer (N := N) i)
  | 0 => continuous_snd.comp (continuous_fst.comp (continuous_fst.comp
      (continuous_fst.comp continuous_fst)))
  | 1 => continuous_snd.comp (continuous_fst.comp (continuous_fst.comp continuous_fst))
  | 2 => continuous_snd.comp (continuous_fst.comp continuous_fst)
  | 3 => continuous_snd.comp continuous_fst
  | 4 => continuous_snd

set_option synthInstance.maxSize 4096 in
/-- **The tick readout of the five pointers**: pointer `i` rests when its first angle is in
`readyArc 2` and displays when it is in `displayArc`. -/
def pentaReadout (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hBC : BC.IsHermitian) (hBD : BD.IsHermitian) (hBE : BE.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (hcr : ContDiff ℝ ∞ r) (p₀ : CPN (N + 1)) :
    TickReadout (pentaDynamics hA hBA hBB hBC hBD hBE hf hg hk hl hr hc hcg hck hcl hcr p₀)
      (Fin 5) where
  rest i := pentaPointer i ⁻¹' readyArc 2
  disp i := pentaPointer i ⁻¹' displayArc
  continuous_flow :=
    continuous_fiveCoupledFlow_prod A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr
  rest_sigmaClosed i := isSigmaClosed_readyArc.preimage (continuous_pentaPointer i)
  disp_sigmaClosed i := isSigmaClosed_displayArc.preimage (continuous_pentaPointer i)
  disjoint _ := readyArc_disjoint_displayArc.preimage _

end Penta

/-! ### The radar experiment on the walled chain -/

section Wall

open CSD.LF4 CSD.CV

variable (n N M : ℕ) (μ Δ w gA gB : ℝ) {D : ℕ}
  (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
    × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1))

/-- **The walled chain's arena as a `ConstraintDynamics`**: the flow of `wallRunAt`, for the
messenger, the two clocks and the five wall gates, with the measure `μ_FS ⊗ vol⁵`. -/
def wallDynamics : ConstraintDynamics (PentaSigma D) :=
  pentaDynamics
    ((compositeH_isHermitian
      (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
      (compositeH_isHermitian
        (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
        (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)))).submatrix
          e.symm)
    ((gateOp_snd_isHermitian (κa := (ZMod (M + 1) × Fin 2) × Fin 2)
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne).submatrix e.symm)
    ((gateOp_snd_isHermitian (κa := (ZMod (M + 1) × Fin 2) × Fin 2)
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
      (fun a b => ¬ wallNear (M + 1) w a b)
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne).submatrix e.symm)
    ((kronecker_isHermitian (Matrix.isHermitian_one (n := ZMod (M + 1) × Fin 2))
      (gateOp_isHermitian (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun a b => ¬ wallNear (M + 1) w a b)
        (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
        levelSwap_apply_eq_zero_of_site_ne)).submatrix e.symm)
    ((gateOp_fst_isHermitian (κb := (ZMod (M + 1) × Fin 2) × Fin 2)
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
      (fun a b => ¬ wallNear (M + 1) w a b)
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne).submatrix e.symm)
    ((kronecker_isHermitian (Matrix.isHermitian_one (n := ZMod (M + 1) × Fin 2))
      (gateOpL_isHermitian (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun a b => ¬ wallNear (M + 1) w a b)
        (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
        levelSwap_apply_eq_zero_of_site_ne)).submatrix e.symm)
    (scaledTrainF_periodic gB) (scaledTrainF_periodic gB) (scaledTrainF_periodic gB)
    (scaledTrainF_periodic gA) (scaledTrainF_periodic gA)
    (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB)
    (contDiff_scaledTrainF gA) (contDiff_scaledTrainF gA) p₀

/-- **The tick readout of the walled chain's five pointers.** -/
def wallReadout : TickReadout (wallDynamics n N M μ Δ w gA gB e p₀) (Fin 5) :=
  pentaReadout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p₀

variable {M}

/-- **The start of a run**: the product ray of the three carriers and the five pointer
angles, as one point of the arena. -/
def radarStart (p : GenArena (ZMod (M + 1) × Fin 2))
    (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ χ ξ ζ : KTorus) : PentaSigma D :=
  (((((idxArenaEquiv e (prodRay p (prodRay qa qb)), θ), ψ), χ), ξ), ζ)

variable (M)

/-- ★ **The walled chain's run is the orbit of its start under the dynamics.** -/
theorem wallRunAt_eq_flow (p : GenArena (ZMod (M + 1) × Fin 2))
    (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ χ ξ ζ : KTorus) (t : ℝ) :
    wallRunAt n N M μ Δ w gA gB e p qa qb θ ψ χ ξ ζ t
      = (wallDynamics n N M μ Δ w gA gB e p₀).flow t (radarStart e p qa qb θ ψ χ ξ ζ) :=
  rfl

/-- **The five facts of one radar run**: the emission, return and meeting counts of the
moving observer's clock (pointers `0`, `1`, `2`) and the relay and meeting counts of the
resting observer's (pointers `3`, `4`), each counted from the start until its reading time. -/
def radarHistory (se sr sμ sρ sm : ℝ) (Ne Nr Nμ Nρ Nm : ℕ) :
    RecordHistory (tickSignature (Fin 5)) :=
  [TickReadout.startFact 0 se Ne, TickReadout.startFact 1 sr Nr, TickReadout.startFact 2 sμ Nμ,
    TickReadout.startFact 3 sρ Nρ, TickReadout.startFact 4 sm Nm]

set_option synthInstance.maxSize 4096 in
/-- **The radar statement in the record semantics.** For every labelling, every base point
of the measure and every choice of flow times in the five reading windows there are five
counts such that: the start of the run is in the compatible region of the history of the
five facts; flowing the start and reading establishes each of the five facts; and the counts
satisfy the four inequalities of `WallRadarGeometry`. -/
def WallRadarRecords (p : GenArena (ZMod (M + 1) × Fin 2))
    (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ χ ξ ζ : KTorus)
    (R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ T₀ B : ℝ) : Prop :=
  ∀ (D : ℕ) (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1)),
    ∀ se, tb ≤ se → se ≤ t3 → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbM ≤ sμ → sμ ≤ tcM →
    ∀ sρ, tbR ≤ sρ → sρ ≤ tcR → ∀ sm, tbM ≤ sm → sm ≤ tcM →
    ∃ Ne Nr Nμ Nρ Nm : ℕ,
      radarStart e p qa qb θ ψ χ ξ ζ
          ∈ compatibleSet (wallReadout n N M μ Δ w gA gB e p₀).semantics
            (radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm)
      ∧ (∀ f ∈ radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm,
          (wallReadout n N M μ Δ w gA gB e p₀).model.establishedFact PUnit.unit f.context
            f.time (radarStart e p qa qb θ ψ χ ξ ζ) = some f)
      ∧ |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1 - (movingEvent R₀ Ne Nr Nμ).1| ≤ E₁
      ∧ |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2 - (movingEvent R₀ Ne Nr Nμ).2| ≤ E₂
      ∧ |(restEvent R₀ Nρ Nm).1 - T₀| ≤ B
      ∧ |radarInterval (movingEvent R₀ Ne Nr Nμ) - radarInterval (restEvent R₀ Nρ Nm)|
          ≤ E₁ * (2 * ((|T₀| + B) / Real.sqrt (1 - v ^ 2)) + E₁)
            + E₂ * (2 * ((|T₀| + B) / Real.sqrt (1 - v ^ 2)) + E₂)

variable {n N M μ Δ w gA gB}

set_option synthInstance.maxSize 4096 in
/-- ★★★ **The five tick counts of the radar theorem are a record history of the run's own
orbit.** From the conclusion of the radar theorem for a run of the walled chain: the start
of the run lies in the compatible region of the five facts in the SigmaLayer's record
semantics, whose events are sets of initial states of the arena defined by the Hamiltonian
flow; and the de-isolation model of the readings establishes each fact from that start. -/
theorem WallRadarGeometry.records {p : GenArena (ZMod (M + 1) × Fin 2)}
    {qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)} {θ ψ χ ξ ζ : KTorus}
    {R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ T₀ B : ℝ}
    (h : WallRadarGeometry M (fun e => wallRunAt n N M μ Δ w gA gB e p qa qb θ ψ χ ξ ζ)
      R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ T₀ B) :
    WallRadarRecords n N M μ Δ w gA gB p qa qb θ ψ χ ξ ζ R₀ v tb t3 t4 t5 tbM tcM tbR tcR
      E₁ E₂ T₀ B := by
  intro D e p₀ se hse1 hse2 sr hsr1 hsr2 sμ hsμ1 hsμ2 sρ hsρ1 hsρ2 sm hsm1 hsm2
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, i1, i2, i3, i4⟩ :=
    h D e se hse1 hse2 sr hsr1 hsr2 sμ hsμ1 hsμ2 sρ hsρ1 hsρ2 sm hsm1 hsm2
  have hx : radarStart e p qa qb θ ψ χ ξ ζ
      ∈ compatibleSet (wallReadout n N M μ Δ w gA gB e p₀).semantics
        (radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm) := by
    refine (wallReadout n N M μ Δ w gA gB e p₀).mem_compatibleSet_startFacts
      [(0, se, Ne), (1, sr, Nr), (2, sμ, Nμ), (3, sρ, Nρ), (4, sm, Nm)] _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [c1, c2, c3, c4, c5]
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, hx, fun f hf => ?_, i1, i2, i3, i4⟩
  exact ((wallReadout n N M μ Δ w gA gB e p₀).establishedFact_eq_some_iff f.context.1
    f.context.2 f.outcome f.time _).2 (mem_event_of_mem_compatibleSet _ hx hf)

end Wall

/-! ### The radar theorem in the record semantics -/

section Family

open CSD.LF4 CSD.CV

set_option synthInstance.maxSize 4096 in
/-- ★★★ **The radar family's five readings are a record history in the SigmaLayer's
semantics.** For `k ≥ 100` and a ring with an even number of sites, with the carriers, the
strengths and the open set `U` of pointer angles of `csd_operational_lorentz_from_records`:
from every five pointer angles in `U`, for every labelling and every choice of flow times in
the five reading windows, the start of the run is in the compatible region of the history of
five recorded facts, the de-isolation model of the readings establishes each of them from
that start, and their counts satisfy the Lorentz statement, the bound on the rest observer's
time and the comparison of intervals of `csd_operational_lorentz_from_records`.

The carriers' rays are fixed. The compatible region is not shown to have positive measure
for the arena's measure `μ_FS ⊗ vol⁵`, so this is not a `HistoryPreparation`. -/
theorem csd_radar_record_history {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ (hψ : oddWall (L := M + 1) 1 (wallMu k) (ringLen (1200 * wallN k * wallN k))
          (Finset.Ico (600 * (wallN k : ℤ) * wallN k) (600 * (wallN k : ℤ) * wallN k + wallN k))
          (flatAmpN (wallN k)) (radarRateB k * radarTau k M / radarRateA k) ≠ 0)
      (gA gB : ℝ)
      (hΨA : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (wallWindow (wallN k) ∪ negWin (wallWindow (wallN k)))
        (oddExt (wallWindow (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)))) ≠ 0)
      (hΨB : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (flatWindow (wallN k) (wallN k) ∪ negWin (flatWindow (wallN k) (wallN k)))
        (oddExt (flatWindow (wallN k) (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)))) ≠ 0)
      (U : Set (KTorus × KTorus × KTorus × KTorus × KTorus)),
      0 < gA ∧ gA ≤ ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) / 5
      ∧ 0 < gB ∧ gB ≤ ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5
      ∧ IsOpen U ∧ 0 < MeasureTheory.volume U
      ∧ (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) ∈ U
      ∧ (∀ Θ : KTorus × KTorus × KTorus × KTorus × KTorus,
          NearStart (1 / (12000 * (k : ℝ) ^ 2)) Θ.1 → NearStart (1 / (12000 * (k : ℝ) ^ 2)) Θ.2.1 →
          NearStart (1 / (12000 * (k : ℝ) ^ 2)) Θ.2.2.1 →
          NearStart (1 / (12000 * (k : ℝ) ^ 2)) Θ.2.2.2.1 →
          NearStart (1 / (12000 * (k : ℝ) ^ 2)) Θ.2.2.2.2 → Θ ∈ U)
      ∧ ∀ Θ ∈ U, WallRadarRecords (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
          gA gB (chainRay _ hψ)
          (deviceRay (deviceShift (H : ZMod (M + 1)) _)
            (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB)
          Θ.1 Θ.2.1 Θ.2.2.1 Θ.2.2.2.1 Θ.2.2.2.2
          (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) (vRel 1 1 (1 / 2))
          (famTb k) (famT3 k) (famT4 k) (famT5 k) (famTbM k M) (famTcM k M) (famTbR k M)
          (famTcR k M) (151 * (wallK k / k)) (151 * (wallK k / k))
          (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
          (52 * (wallK k / k)) := by
  obtain ⟨hψ, gA, gB, hΨA, hΨB, U, c1, c2, c3, c4, c5, c6, c7, c8, hall⟩ :=
    csd_operational_lorentz_from_records hk hM hH
  exact ⟨hψ, gA, gB, hΨA, hΨB, U, c1, c2, c3, c4, c5, c6, c7, c8,
    fun Θ hΘ => (hall Θ hΘ).records⟩

end Family

end CSD.RecordLayer

end
