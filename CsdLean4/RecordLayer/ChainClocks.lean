/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ChainExchange
public import CsdLean4.CV.CausalDistance
public import CsdLean4.RecordLayer.RecordClock
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# Clocks along the chain: clock delay against graph distance, and chain length

**Category:** 7-SigmaLayer (the record layer — the network witness of the clock-and-echo programme).
BACKLOG #190 (out of #39; the residue of #188).

The scheduled chain of `CV/ChainExchange.lean` carries one excitation from site `0` to site `k` in
exactly `k` hop times. Here a physical record clock of #185 sits at every site, all started at the
switch-on and all calibrated to the hop time — the synchronisation and calibration conventions of
#186 and #188, stated as hypotheses — on one arena with the exchange, under one two-time
measure-preserving evolution.

* `ChainArena n K`, `chainEvolve J ħ T s t` — **the common arena and its two-time propagator**:
  the scheduled exchange and the `n + 1` clocks; `chainEvolve_self`, ★ `chainEvolve_comp` (the
  two-time law, from `Schedule.evolve_comp` and `clockEvolve_comp`), `measurable_chainEvolve`,
  ★ `chainEvolve_measurePreserving` — Liouville (Fubini–Study × Haar on every clock) is preserved:
  **it is a dynamics**;
* `ChainReady`, `chainPrep b c` — the ready preparation with message `b`; `siteReading` — the
  reading of site `j`'s clock at ontic time `t`;
* ★★ `reception_reading` — **the clock at site `k` reads `k τ_hop` when the signal arrives**, i.e.
  `tickCount_at_reception`: `k` ticks; ★★★ `clock_delay_eq_graphDist` — **and `k` is the graph
  distance from site `0` to site `k` on the path graph**: on this witness, with this schedule, clock
  delay equals graph distance, for every site; ★★ `reception_readout` — at the same moment the
  receiver at `k` reads the message;
* `eventOfReception`, `eventOfReception_eq` — **the reception at `k` as a `RecordEvent` labelled by
  the physical clock**: `⟨{k}, k⟩` (`siteEvent k`); `pairEvent k = ⟨{k, k+1}, k+1⟩`;
  `siteEvent_precedes_pairEvent`, `pairEvent_precedes_siteEvent`, `siteEvent_zero_precedes` — the
  site events form a `CausalPrecedes` chain on the path graph;
* ★ `le_causalDist_siteEvents` — **the experiment's own chain of site events gives `causalDist ≥ k`**,
  matching the clock; ★★ `two_mul_le_causalDist` — **inserting the event "both ends of edge `j` at
  period `j+1`" between consecutive site events doubles the chain: `causalDist ≥ 2k`**; hence
  ★★ `clock_time_lt_causalDist`: for `k ≥ 1` the clock's elapsed ticks `k` are strictly less than
  the longest-chain separation. This is #188's inflation (`three_le_causalDist`) for every `k`: the
  longest-chain distance over all record events is not clock time; they agree only at the fixed
  resolution of the site events;
* ★★★ `chain_clocks` — the package.

## What this says about an effective cone

The clock delay equals the graph distance because every edge is switched on for the same hop time
`τ_hop = πħ/2J`: the schedule gives the network one edge per `τ_hop`, and that is the only reason
the two agree. A universal effective cone for this network would have to be exactly that — the same
hop time on every edge, supplied by the schedule, not derived from the graph. Nothing here says the
cone is universal, and nothing identifies `1 / τ_hop` with a limiting speed; cf. the containment,
never identification, of `CV/TwoCones.lean`.

## Honest scope

* ⚠️ The schedule is a modelling input (the brief's own warning); a uniform chain Hamiltonian does
  not transfer exactly, and no claim is made about one.
* ⚠️ All clocks are started at the switch-on (`0`) and calibrated to `τ_hop`: the synchronisation
  convention and the calibration are hypotheses (`hT : T = hopTime J ħ`, the common start in
  `chainEvolve`), as in #186 and #188. A different start at site `k` shifts its reading by the offset.
* `causalDist` carries no resolution parameter; "the fixed resolution of the site events" is the
  chain `le_causalDist_siteEvents` exhibits, not a restricted distance.
* The clocks' horizon must cover the chain: `n ≤ K`.

References: `specs/BACKLOG.md` #190, #188, #186, #185, #39; `CV/ChainExchange.lean`,
`RecordLayer/RecordClock.lean`, `RecordLayer/ClockCalibration.lean`, `CV/CausalDistance.lean`
(`causalDist`, `causalDist_add_le`, `causalDist_pos_iff`), `CV/TwoCones.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {n K : ℕ}

/-! ### The arena and its two-time propagator -/

/-- The common arena: the scheduled exchange on `n + 1` sites and a record clock at every site. -/
abbrev ChainArena (n K : ℕ) := FieldArena (n + 1) 2 × (Fin (n + 1) → ClockArena K)

theorem chainKick_eq_smul (U : Matrix.unitaryGroup (ChainConfig (n + 1)) ℂ)
    (p : FieldArena (n + 1) 2) : arenaKick U p = U • p := by
  conv_rhs => rw [← p.mk_rep]
  rw [smul_mk_eq_mk_toEuclideanLin]
  rfl

theorem measurable_chainKick (U : Matrix.unitaryGroup (ChainConfig (n + 1)) ℂ) :
    Measurable (arenaKick U : FieldArena (n + 1) 2 → FieldArena (n + 1) 2) := by
  have h : (arenaKick U : FieldArena (n + 1) 2 → FieldArena (n + 1) 2) = fun p => U • p :=
    funext (chainKick_eq_smul U)
  rw [h]
  exact (continuous_const_smul U).measurable

theorem chainKick_one (p : FieldArena (n + 1) 2) :
    arenaKick (1 : Matrix.unitaryGroup (ChainConfig (n + 1)) ℂ) p = p := by
  rw [chainKick_eq_smul, one_smul]

/-- **The joint two-time propagator**: the scheduled exchange from `s` to `t`, and every clock on its
own schedule, all started at the switch-on `0`. -/
noncomputable def chainEvolve (J ħ T : ℝ) (s t : OnticTime) : ChainArena n K → ChainArena n K :=
  fun x => (arenaKick ((chainSchedule n J ħ).evolve s t) x.1, fun j => clockEvolve T s t (x.2 j))

theorem chainEvolve_exchange (J ħ T : ℝ) (s t : OnticTime) (x : ChainArena n K) :
    (chainEvolve J ħ T s t x).1 = arenaKick ((chainSchedule n J ħ).evolve s t) x.1 := rfl

theorem chainEvolve_clock (J ħ T : ℝ) (s t : OnticTime) (x : ChainArena n K) (j : Fin (n + 1)) :
    (chainEvolve J ħ T s t x).2 j = clockEvolve T s t (x.2 j) := rfl

theorem chainEvolve_self (J ħ T : ℝ) (t : OnticTime) :
    chainEvolve (n := n) (K := K) J ħ T t t = id := by
  funext x
  simp [chainEvolve, Schedule.evolve_self, chainKick_one, clockEvolve_self]

/-- ★ **The two-time composition law on the common arena.** -/
theorem chainEvolve_comp (J ħ T : ℝ) (s t u : OnticTime) :
    chainEvolve (n := n) (K := K) J ħ T t u ∘ chainEvolve J ħ T s t = chainEvolve J ħ T s u := by
  funext x
  simp only [Function.comp_apply, chainEvolve, ← arenaKick_mul, Schedule.evolve_comp]
  congr 1
  funext j
  exact congrFun (clockEvolve_comp T s t u) (x.2 j)

theorem measurable_chainEvolve (J ħ T : ℝ) (s t : OnticTime) :
    Measurable (chainEvolve (n := n) (K := K) J ħ T s t) := by
  refine Measurable.prodMk ((measurable_chainKick _).comp measurable_fst) ?_
  exact measurable_pi_iff.mpr fun j =>
    (measurable_clockEvolve T s t).comp ((measurable_pi_apply j).comp measurable_snd)

/-- ★ **The joint propagator preserves Liouville measure** — Fubini–Study on the exchange, Haar on
every clock — for every reference point of the Fubini–Study measure: it is a dynamics. -/
theorem chainEvolve_measurePreserving (J ħ T : ℝ) (s t : OnticTime) (p₀ : FieldArena (n + 1) 2) :
    MeasurePreserving (chainEvolve (n := n) (K := K) J ħ T s t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  have h : chainEvolve (n := n) (K := K) J ħ T s t
      = Prod.map (fun p => (chainSchedule n J ħ).evolve s t • p)
          (fun c : Fin (n + 1) → ClockArena K => fun j : Fin (n + 1) => clockEvolve T s t (c j)) := by
    funext x
    rw [chainEvolve, chainKick_eq_smul]
    rfl
  rw [h, volume_pi]
  exact MeasurePreserving.prod ⟨(continuous_const_smul _).measurable, fsMeasure_smul_invariant _ p₀⟩
    (measurePreserving_pi _ _ fun _ => clockEvolve_measurePreserving T s t)

/-! ### Readiness, preparation, readings -/

/-- Every clock ready. -/
def ChainReady (n K : ℕ) : Set (ChainArena n K) := {x | ∀ j, x.2 j ∈ ClockReady K}

/-- The ready preparation with message `b`: the message point and the clocks `c`. -/
noncomputable def chainPrep (b : Fin 2) (c : Fin (n + 1) → ClockArena K) : ChainArena n K :=
  (chainMsg n b, c)

theorem chainPrep_mem_ready {c : Fin (n + 1) → ClockArena K} (hc : ∀ j, c j ∈ ClockReady K)
    (b : Fin 2) : chainPrep b c ∈ ChainReady n K := hc

/-- The reading of site `j`'s clock, unit `τ`, at ontic time `t` from the switch-on. -/
noncomputable def siteReading (J ħ T τ : ℝ) (x : ChainArena n K) (j : Fin (n + 1)) (t : OnticTime) :
    ℝ :=
  tickReading τ ((chainEvolve J ħ T 0 t x).2 j)

theorem siteReading_eq (J ħ T τ : ℝ) (x : ChainArena n K) (j : Fin (n + 1)) (t : OnticTime) :
    siteReading J ħ T τ x j t = tickReading τ (clockEvolve T 0 t (x.2 j)) := rfl

/-- From the switch-on, the exchange factor is the scheduled arena flow. -/
theorem chainEvolve_exchange_zero (J ħ T : ℝ) (t : OnticTime) (x : ChainArena n K) :
    (chainEvolve J ħ T 0 t x).1 = chainArenaFlow J ħ t x.1 := by
  rw [chainEvolve_exchange, Schedule.evolve_zero]
  rfl

/-! ### Clock delay against graph distance -/

/-- **The clock at site `k` shows `k` ticks when the signal arrives.** -/
theorem tickCount_at_reception {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    (hnK : n ≤ K) {x : ChainArena n K} (hx : x ∈ ChainReady n K) (k : Fin (n + 1)) :
    tickCount ((chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) x).2 k) = k := by
  have hTpos : 0 < T := by rw [hT]; exact hopTime_pos hJ hħ
  rw [chainEvolve_clock, ← hT]
  exact tickCount_at_period hK hTpos (hx k) (le_trans (Nat.le_of_lt_succ k.isLt) hnK)

/-- ★★ **The clock at site `k`, calibrated to the hop time, reads `k τ_hop` when the signal
arrives** — the transmission delay in the clock's own units. -/
theorem reception_reading {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    (hnK : n ≤ K) {x : ChainArena n K} (hx : x ∈ ChainReady n K) (k : Fin (n + 1)) :
    siteReading J ħ T T x k ((k : ℕ) * hopTime J ħ) = (k : ℕ) * hopTime J ħ := by
  rw [siteReading, tickReading, tickCount_at_reception hJ hħ hT hK hnK hx k, hT]

/-- ★★★ **Clock delay equals graph distance** on this witness: the ticks shown at site `k` when the
signal arrives are the graph distance from site `0` to site `k` on the path graph. -/
theorem clock_delay_eq_graphDist {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ)
    (hK : 0 < K) (hnK : n ≤ K) {x : ChainArena n K} (hx : x ∈ ChainReady n K) (k : Fin (n + 1)) :
    tickCount ((chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) x).2 k) = graphDist (pathGraph n) {0} k := by
  rw [tickCount_at_reception hJ hħ hT hK hnK hx k, graphDist_pathGraph]

/-- ★★ **At the same moment the receiver at `k` reads the message**: `1` for message `1`, `0` for
message `0`. -/
theorem reception_readout {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (c : Fin (n + 1) → ClockArena K)
    (k : Fin (n + 1)) :
    arenaObs (occAt k) (chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) (chainPrep 1 c)).1 = 1
      ∧ arenaObs (occAt k) (chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) (chainPrep 0 c)).1 = 0 := by
  rw [chainEvolve_exchange_zero, chainEvolve_exchange_zero]
  exact receiver_distinguishes_chain hJ hħ k

/-! ### The reception as a record event labelled by the clock -/

/-- The reception at site `k`, as a record event: the site, at the period its own clock shows. -/
noncomputable def eventOfReception (J ħ T : ℝ) (x : ChainArena n K) (k : Fin (n + 1)) :
    RecordEvent (n + 1) :=
  ⟨{k}, tickCount ((chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) x).2 k)⟩

/-- The site event `⟨{k}, k⟩`. -/
def siteEvent (k : Fin (n + 1)) : RecordEvent (n + 1) := ⟨{k}, k.val⟩

/-- The inserted event: both ends of edge `(k, k+1)`, at period `k + 1`. -/
def pairEvent (k : Fin n) : RecordEvent (n + 1) := ⟨{Fin.castSucc k, Fin.succ k}, k.val + 1⟩

/-- **The reception at `k` is the site event `⟨{k}, k⟩`**, under the stated calibration. -/
theorem eventOfReception_eq {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    (hnK : n ≤ K) {x : ChainArena n K} (hx : x ∈ ChainReady n K) (k : Fin (n + 1)) :
    eventOfReception J ħ T x k = siteEvent k := by
  rw [eventOfReception, tickCount_at_reception hJ hħ hT hK hnK hx k]
  rfl

theorem mem_graphBall_of_mem {E : Finset (Fin (n + 1) × Fin (n + 1))} {R : Finset (Fin (n + 1))}
    {k : Fin (n + 1)} (hk : k ∈ R) (d : ℕ) : k ∈ graphBall E R d :=
  graphBall_mono E R (Nat.zero_le d) (by rwa [graphBall_zero])

theorem succ_mem_graphBall_one (k : Fin n) :
    Fin.succ k ∈ graphBall (pathGraph n) {Fin.castSucc k} 1 := by
  show Fin.succ k ∈ graphNeighborhood (pathGraph n) {Fin.castSucc k}
  rw [graphNeighborhood, Finset.mem_union, Finset.mem_biUnion]
  refine Or.inr ⟨(Fin.castSucc k, Fin.succ k), ?_, ?_⟩
  · rw [Finset.mem_filter, mem_pathGraph]
    exact ⟨⟨k, rfl⟩, Or.inl (Finset.mem_singleton_self _)⟩
  · rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr rfl

theorem siteEvent_precedes_pairEvent (k : Fin n) :
    CausalPrecedes (pathGraph n) (siteEvent (Fin.castSucc k)) (pairEvent k) := by
  refine ⟨?_, ?_⟩
  · show (Fin.castSucc k).val ≤ k.val + 1
    rw [Fin.val_castSucc]
    exact Nat.le_succ _
  · show ({Fin.castSucc k, Fin.succ k} : Finset (Fin (n + 1)))
      ⊆ graphBall (pathGraph n) {Fin.castSucc k} (k.val + 1 - (Fin.castSucc k).val)
    rw [Fin.val_castSucc, Nat.add_sub_cancel_left]
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact mem_graphBall_of_mem (Finset.mem_singleton_self _) 1
    · exact succ_mem_graphBall_one k

theorem pairEvent_precedes_siteEvent (k : Fin n) :
    CausalPrecedes (pathGraph n) (pairEvent k) (siteEvent (Fin.succ k)) := by
  refine ⟨?_, ?_⟩
  · show k.val + 1 ≤ (Fin.succ k).val
    exact (Fin.val_succ k).ge
  · show ({Fin.succ k} : Finset (Fin (n + 1)))
      ⊆ graphBall (pathGraph n) {Fin.castSucc k, Fin.succ k} ((Fin.succ k).val - (k.val + 1))
    rw [Fin.val_succ, Nat.sub_self, graphBall_zero]
    intro j hj
    rw [Finset.mem_singleton] at hj
    rw [hj]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Consecutive site events are causally ordered. -/
theorem siteEvent_precedes_succ (k : Fin n) :
    CausalPrecedes (pathGraph n) (siteEvent (Fin.castSucc k)) (siteEvent (Fin.succ k)) :=
  causalPrecedes_trans (siteEvent_precedes_pairEvent k) (pairEvent_precedes_siteEvent k)

/-- The emission precedes every reception. -/
theorem siteEvent_zero_precedes (j : Fin (n + 1)) :
    CausalPrecedes (pathGraph n) (siteEvent 0) (siteEvent j) := by
  refine ⟨Nat.zero_le _, ?_⟩
  show ({j} : Finset (Fin (n + 1))) ⊆ graphBall (pathGraph n) {0} (j.val - (0 : Fin (n + 1)).val)
  rw [Fin.val_zero, Nat.sub_zero]
  intro i hi
  rw [Finset.mem_singleton] at hi
  rw [hi]
  exact (mem_graphBall_pathGraph j.val j).mpr le_rfl

theorem siteEvent_ne_pairEvent (k : Fin n) : siteEvent (Fin.castSucc k) ≠ pairEvent k := by
  intro h
  have := congrArg RecordEvent.time h
  simp [siteEvent, pairEvent] at this

theorem pairEvent_ne_siteEvent (k : Fin n) : pairEvent k ≠ siteEvent (Fin.succ k) := by
  intro h
  have hreg := congrArg RecordEvent.region h
  simp only [pairEvent, siteEvent] at hreg
  have hmem : Fin.castSucc k ∈ ({Fin.succ k} : Finset (Fin (n + 1))) :=
    hreg ▸ Finset.mem_insert_self _ _
  rw [Finset.mem_singleton] at hmem
  exact Fin.castSucc_lt_succ.ne hmem

theorem siteEvent_ne_succ (k : Fin n) : siteEvent (Fin.castSucc k) ≠ siteEvent (Fin.succ k) := by
  intro h
  have := congrArg RecordEvent.time h
  simp [siteEvent] at this

/-- One edge of the chain already has two strict steps through the inserted event. -/
theorem two_le_causalDist_step (k : Fin n) :
    2 ≤ causalDist (pathGraph n) (siteEvent (Fin.castSucc k)) (siteEvent (Fin.succ k)) := by
  have h1 := causalDist_pos_iff.mpr ⟨siteEvent_precedes_pairEvent k, siteEvent_ne_pairEvent k⟩
  have h2 := causalDist_pos_iff.mpr ⟨pairEvent_precedes_siteEvent k, pairEvent_ne_siteEvent k⟩
  have := causalDist_add_le (siteEvent_precedes_pairEvent k) (pairEvent_precedes_siteEvent k)
  omega

/-- ★ **The experiment's own chain of site events gives `causalDist ≥ k`**, matching the clock. -/
theorem le_causalDist_siteEvents :
    ∀ m (hm : m ≤ n),
      m ≤ causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) := by
  intro m
  induction m with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
      intro hm
      have hlt : m < n := hm
      have hcast : (⟨m, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩ : Fin (n + 1))
          = Fin.castSucc ⟨m, hlt⟩ := rfl
      have hsucc : (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, hlt⟩ := rfl
      have h1 := ih (Nat.le_of_lt hlt)
      rw [hcast] at h1
      have h2 := causalDist_pos_iff.mpr
        ⟨siteEvent_precedes_succ (⟨m, hlt⟩ : Fin n), siteEvent_ne_succ ⟨m, hlt⟩⟩
      have h3 := causalDist_add_le (siteEvent_zero_precedes (Fin.castSucc ⟨m, hlt⟩))
        (siteEvent_precedes_succ ⟨m, hlt⟩)
      rw [hsucc]
      omega

/-- ★★ **Inserting events doubles the chain**: through the pair events the longest chain from the
emission to the reception at site `m` has at least `2m` steps, while the clock shows `m` ticks. -/
theorem two_mul_le_causalDist :
    ∀ m (hm : m ≤ n),
      2 * m ≤ causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) := by
  intro m
  induction m with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
      intro hm
      have hlt : m < n := hm
      have hcast : (⟨m, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩ : Fin (n + 1))
          = Fin.castSucc ⟨m, hlt⟩ := rfl
      have hsucc : (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, hlt⟩ := rfl
      have h1 := ih (Nat.le_of_lt hlt)
      rw [hcast] at h1
      have h2 := two_le_causalDist_step (⟨m, hlt⟩ : Fin n)
      have h3 := causalDist_add_le (siteEvent_zero_precedes (Fin.castSucc ⟨m, hlt⟩))
        (siteEvent_precedes_succ ⟨m, hlt⟩)
      rw [hsucc]
      omega

/-- ★★ **Clock time is not chain length**: for every site `m ≥ 1` the clock's elapsed ticks `m` are
strictly less than the longest-chain separation from the emission. -/
theorem clock_time_lt_causalDist {m : ℕ} (hm : m ≤ n) (hm1 : 1 ≤ m) :
    m < causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) := by
  have := two_mul_le_causalDist m hm
  omega

/-! ### The package -/

/-- ★★★ **Clocks along the chain.** One two-time measure-preserving dynamics carries the scheduled
exchange and a clock at every site; for every ready preparation the clock at site `k` shows `k`
ticks when the signal arrives, which is the graph distance from site `0` to site `k`; the receiver
at `k` reads the message at that moment; the reception is the record event `⟨{k}, k⟩`; the site
events alone give `causalDist ≥ k`, the inserted events give `≥ 2k`, so clock time is below the
longest chain for every `k ≥ 1`. -/
theorem chain_clocks {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    (hnK : n ≤ K) {c : Fin (n + 1) → ClockArena K} (hc : ∀ j, c j ∈ ClockReady K) :
    (∀ s t u : OnticTime,
        chainEvolve (n := n) (K := K) J ħ T t u ∘ chainEvolve J ħ T s t = chainEvolve J ħ T s u)
      ∧ (∀ (s t : OnticTime) (p₀ : FieldArena (n + 1) 2),
          MeasurePreserving (chainEvolve (n := n) (K := K) J ħ T s t) ((fsMeasure p₀).prod volume)
            ((fsMeasure p₀).prod volume))
      ∧ (∀ (b : Fin 2) (k : Fin (n + 1)),
          tickCount ((chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) (chainPrep b c)).2 k)
            = graphDist (pathGraph n) {0} k)
      ∧ (∀ k : Fin (n + 1),
          arenaObs (occAt k) (chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) (chainPrep 1 c)).1 = 1
            ∧ arenaObs (occAt k) (chainEvolve J ħ T 0 ((k : ℕ) * hopTime J ħ) (chainPrep 0 c)).1 = 0)
      ∧ (∀ (b : Fin 2) (k : Fin (n + 1)), eventOfReception J ħ T (chainPrep b c) k = siteEvent k)
      ∧ (∀ m (hm : m ≤ n),
          m ≤ causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩)
            ∧ 2 * m ≤ causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩)) :=
  ⟨fun s t u => chainEvolve_comp J ħ T s t u, fun s t p₀ => chainEvolve_measurePreserving J ħ T s t p₀,
    fun b k => clock_delay_eq_graphDist hJ hħ hT hK hnK (chainPrep_mem_ready hc b) k,
    fun k => reception_readout hJ hħ c k,
    fun b k => eventOfReception_eq hJ hħ hT hK hnK (chainPrep_mem_ready hc b) k,
    fun m hm => ⟨le_causalDist_siteEvents m hm, two_mul_le_causalDist m hm⟩⟩

end CSD.RecordLayer

end
