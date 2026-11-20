# Plans for the outstanding tasks of "Unified records, quantum measurement and emergent spacetime"

Written 2026-11-19 at the author's request ("plans in place for all the outstanding tasks at
a minimum"). The plan of twelve tasks is the author's, of 2026-11-18; its obligations are
UO-17, UO-19, UO-25 and UO-26 of [`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md).
This note says, for each task that is not finished, what is in hand, the theorems that are
to be proved in order, where a decision of the author is needed, and where the honest
outcome may be an obstruction. It claims nothing. A theorem named here in italics does not
exist; a name in code type does.

Prices are the usual letters and are not estimates of time.

## 0. Where the plan stands

| Task | State | Register |
|---|---|---|
| 1. Tick counts as recorded facts | done | UD-208 |
| 2. A preparation of non-zero measure | done, counts not named | UD-213 to UD-215, UD-218, UD-219 |
| 3. Macroscopic projection | projection and the radar's cell done; stability owed | UD-223, UD-225 |
| 4. Causal bridge | not started | — |
| 5. Recursive physical apparatus | not started | — |
| 6. Born bridge or obstruction | not started | — |
| 7. Dynamical Born selection | not started; exploratory | UO-20 |
| 8. Packets in `d` dimensions | done for `μ > 0` and a flat window; clock and `μ = 0` owed | UD-209, UD-210, UD-217, UD-220 to UD-222 |
| 9. Detectors and the cone in `d` dimensions | not started | — |
| 10. `2 + 1` radar | not started | — |
| 11. `3 + 1` radar | not started | UO-17 |
| 12. Capstone | not started | UO-19 |
| The caused return (choice (c)) | item (1) of five done for the contact term | UA-19, UD-211, UD-212, UD-216, UD-224, UD-226 |

Safeguards of the plan, which every item below keeps: a record event is not a persistent
register; conditioning on a history is not an interaction; positive measure in a fibre is
not positive measure in the arena; the Born weights of a `globalBasin` are not the
probabilities of a threshold click; a causal order read off an assumed graph does not derive
the graph; the length of a causal chain is not a Lorentzian metric; Posit 11 remains; an
operational time does not derive the flow parameter; a conditional theorem that compiles
does not discharge a posit.

## 1. Task 3 — the macroscopic projection: what is left

In hand: `TickReadout.tickMacro`, `TickReadout.compatibleSet_eq_preimage_singleton`,
`csd_radar_macrostate`. The author's five requirements and their state:

1. Measurability — done (`TickReadout.measurable_tickCode`).
2. Factorisation of the record events — done (`TickReadout.countEvent_eq_preimage`).
3. Record probabilities under the pushforward — done 2026-11-19:
   `TickReadout.map_tickMacro_singleton`, the pushed-forward measure of a string is the arena
   measure of the history's compatible region.
4. A quantitative stability statement — owed. **Corrected 2026-11-19**: the first plan
   (the count is a function of the history, so the string is constant on the start set) is
   not available. A gated history fixes the count only within
   `3 v (t_b − t_a) + 7/2` ticks (`IsGatedHistory.exists_count`): between the end of the
   swing and the closing of the gate the pointer drifts at a bounded rate, not a known one.
   Two starts with the same history can have different counts. What can be proved:
   * A count is bounded by the run's duration — done 2026-11-19 for any history:
     `HasTicks.mul_le`, `IsTickCount.le_div` (`n d ≤ K T`). For the radar — done 2026-11-19
     (`RecordLayer/PointerCountCap.lean`, UD-232): `wallCount_le`, a count at `T` is at most
     `12 max(|g_A|, |g_B|) T` from every start.
   * One history's share — done 2026-11-19: `wall_exists_history_measure_ge`, for any set `S`
     of starts there are five counts at most `B` whose history's compatible region holds at
     least `1 / (B + 1)^5` of the measure of `S`. That those counts satisfy
     `RadarCountBounds` on the start set of UD-219 — done 2026-11-19
     (`RecordLayer/RadarHistoryShare.lean`, UD-237): `csd_radar_history_share`, by
     uniqueness of a count. Owed: the reading windows in `t ≥ 0`; the start set's measure.
   * A sharper history that does fix the count (the drift's rate known between `t_a` and
     `t_b`) would give constancy; whether the family's runs have it is to be examined, not
     assumed. (M–L)
   * Stability under the flow, in the sense of `RecordLayer/MacrostateStability.lean`
     (`recordMacro_sigmaShift`): by `fiveCoupledFlow_shiftPenta` turning a pointer's
     starting angle turns its angle at every time, so its count can change; no stability
     under that turn is to be claimed. A reading is fixed during its window (UA-18 (e)),
     and that is the statement available. (M)
5. Dependence on a declared context — done by construction: the family of readings is an
   argument of `TickReadout.tickMacro`.

The cell does split in general; the statements are about a finite set of cells.

## 2. Task 4 — the causal bridge

Target: a module for the radar's causal relations (the plan's `UnifiedRadarCausalBridge`).
Reuse: `CV/RecordCausalOrder.lean` (`RecordEvent`, `CausalPrecedes`,
`isPartialOrder_causalPrecedes`), `CV/RecordInfluence.lean` (`Influences`, `Spacelike`,
`not_influences_of_spacelike`), `CV/CausalDistance.lean` (`causalDist`),
`RecordLayer/UnifiedCausalOrder.lean` (the cone bound for the coupled generators).

**Decided 2026-11-19 (the author): the events keep their real flow times; the graph relation
is stated for them directly, with no map to whole periods.** First brick done 2026-11-19
(`RecordLayer/FlowEventCone.lean`, UD-239, BACKLOG #442): `FlowEvent`, `HopSeparated`,
`FlowEvent.PermittedWithin`, `FlowEvent.kick_response_le`. `RecordEvent` (whole periods) is
not used for the radar.

The three notions the author asks to be kept apart, and what is to be proved for each:

1. *Permitted by the graph.* *radarEvent*: each of the five readings as a `RecordEvent`: the
   region is the set of sites its gate reads at the window, the time is the window's end.
   *radarEvents_causalPrecedes*: emission precedes relay precedes return, and the two
   meeting readings are related as the graph allows, from the gate times of UD-196 and the
   hop of the chain. This is a statement about the graph and the times; it derives neither.
   (M)
2. *Demonstrated under a non-zero coupling.* The corpus shows a remote kick is felt only at
   distance one (UD-82, UD-83). For the radar the demonstration is the experiment itself:
   *relay_count_depends_on_messenger*: with the messenger removed (its amplitude set to
   zero in the prepared ray) the relay reading's count differs from the count with it, by
   the gated history. That is influence carried by the flow over the whole chain. (M–L;
   needs the histories without a messenger, which is a new but simpler run)
3. *The order of the flow parameter.* *radar_windows_ordered*: the reading windows are
   ordered in flow time. Stated separately so that it is not mistaken for (1) or (2). (S)

Then *radar_macrostate_causal*: the five events of (1) are the five coordinates of the
macrostate of Task 3. (S)

Not to be done: assigning an interval to a pair of records. `causalDist` counts links; it
is not a metric and the bridge does not make it one.

Possible failure: (2) may only be provable as "the two runs differ by at least so much in
displacement", not as a difference of counts, if the margins do not separate them.

## 3. Task 5 — a record that controls a second apparatus

The obstacle is already a theorem. On every arena built so far no pointer's moving angle is
in the energy, so the flow commutes with turning a pointer
(`hamiltonianFlow_stepEnergy_shiftMoving`, `clockMessengerFlow_shiftPointers`; UO-24,
UD-106, UD-107). A second apparatus therefore cannot depend on what a pointer displays.

**Recommended by the charter (2026-11-19, on the author's "recommend CSD aligned
solutions"; the author has not yet confirmed it).** In CSD a record is the ontic selection
in the fibre: here, a pointer's moving angle having crossed its arcs. A carrier's level is
part of the base ray and is not a record. So "information established by one apparatus
controls a subsequent interaction" means that a pointer's moving angle enters the energy
of what follows. That is UO-24 and Route C below. It is the faithful reading; it is also a
term of a new kind, so it needs the author's word and a clause before any theorem.

Three routes:

* **Route B: the obstruction on the five-pointer arena — done 2026-11-19.**
  `fiveCoupledFlow_shiftPenta` (`LF4/PentaPointerInert.lean`, UD-227): the flow commutes
  with turning each of the five pointers, so nothing on the arena of UA-18 depends on a
  record held by a pointer.
* **Route C: a pointer whose moving angle acts back (UO-24).** The faithful route. Plan:
  a clause for a step whose observable is multiplied by a profile of an earlier pointer's
  moving angle; *controlledStepFlow* solved as a skew product in the other order (the
  earlier pointer first); a two-stage run in which the second pointer ticks only when the
  first has displayed; the two facts as a record history with `HistoryPreparation.appendFact`.
  The symplectic form and Liouville's theorem are not at risk (the energy is still a
  function on the same arena); what changes is that the earlier pointer's conserved angle
  is no longer conserved. (L)
* **Route A: carrier-mediated succession.** The transponder of UA-19: the contact term
  changes its level, and a pointer gated by the projector on the second level ticks only
  after. This is two apparatus reading one carrier in turn. It is to be stated as
  succession through the carrier and not as record control. (L; shares its hard step with
  the caused return)

Route C's first theorem is done (2026-11-19, `LF4/ControlledStep.lean`, UD-233):
`hamiltonianFlow_controlledEnergy_of_lift_eq_zero`, `controlled_pointer_fixed_of_window_eq_zero`,
`map_hamiltonianFlow_controlledEnergy`. The order of the two displays is done (2026-11-19,
`RecordLayer/ControlledOrder.lean`, UD-241): `controlled_display_after_first`, the first
half of the theorem named below. Next: the two-stage run as records. The first
pointer's tick record on its own arena is in hand (UD-58 onward); wanted is
*controlled_second_ticks_after_first*: with the window `b` supported in the displaying arc,
the second pointer has no tick before the first pointer's first display, and has one after
the first has stayed displayed for long enough; then the two facts as a record history.

Route C's term is admitted as UA-20 of the contract (2026-11-19, on "Continue all of
them"; to be struck if that was not meant). Its first theorem is the controlled step's
flow, an instance of `hamiltonianFlow_stepEnergy` once the observable `b(θ₁) K` is shown
smooth on the arena with one pointer.

## 4. Task 6 — the Born bridge or its obstruction

What must not be confused: `globalBasin` events carry Born weights for a supplied rate field
(`RecordLayer/GlobalBasin.lean`); a threshold click of a drift coupling does not
(`RecordLayer/DiracPointerClick.lean`, gate A, UD-50 to UD-52).

For the tick records of Task 1 the quantity is, for a prepared carrier ray `ψ` and the
pointer angles distributed by Haar measure in a declared set, the probability that pointer
`i` shows the count `N` at `T`.

1. The exact law of a count — done 2026-11-19 for a pointer that only advances:
   `isTickCount_pointer` (the count is the number of integers `k` with `rep q ≤ 1/6 + k` and
   `1/3 + k < rep q + D(T)`), and `integral_card_tickIndices_pointer` (its mean over the
   starting angle is `D(T) − 1/6`). **This changes the expected conclusion.** The click
   probability saturates because it asks only whether the count is at least one; the mean
   count does not saturate. It is linear in the displacement with a dead zone of one gap.
2. *pointer_displacement_monotone*: for a pointer coupled to a positive observable `G` with a
   strength of one sign, on the fibre where the profile vanishes, the displacement is
   `2 |z| ∫₀ᵀ ⟨G⟩` along the free orbit: continuous, non-decreasing, zero at zero. From the
   flow's formula (`pentaRun_fibre`) and `0 ≤ ⟨G⟩`. (M)
3. *mean_tick_count_eq*: with 1 and 2, the mean count is `2 |z| ∫₀ᵀ ⟨G⟩ − 1/6`. For a
   projector `G = Π_i` and a preparation whose weight `w = ⟨Π_i⟩` is constant over the
   window, that is `2 |z| w T − 1/6`: the mean tick rate is the Born weight, within
   `1/(6 · 2|z| T)` in relative terms. This is the conditional bridge, and its assumptions
   are: a positive observable; a stationary weight; the pointer's start uniform; the fibre
   where the profile vanishes. (M)
4. What is to be stated beside it, so that it is not over-read:
   * the count's distribution is two adjacent values, and a single run's count is not the
     weight;
   * for a weight that varies over the window the mean count is the accumulated weight,
     which is not `|⟨i|ψ⟩|²` at any one time (*mean_tick_count_not_instantaneous*, by two
     preparations with the same weight at `T` and different accumulations);
   * the click law of UD-50 is the statement about `count ≥ 1` and saturates: both are
     true;
   * this is not the cell law. Posit 1 asks that the *rates* that allocate cells are
     generators; here a rate is `2 |z| ⟨G⟩`, a moment-map coordinate by construction of the
     coupling. UO-20 is unchanged. (M)

**Author's instruction, 2026-11-19.** The Born weight is already proven
(`csd_nstep_born`, `RecordLayer/NStepChain.lean`; the `globalBasin` weights) and is not to
be re-derived. Items 2 and 3 as written build a weight from a pointer's displacement, which
is that re-derivation. They are withdrawn until restated as a relation between the tick
statistic of item 1 and the weights those theorems already give. Item 1 stands as the law
of a count given a displacement.

Acceptance as the author wrote it: a conditional bridge with every assumption stated, or an
obstruction. After item 1 the expectation is a conditional bridge for the mean count of
a pointer coupled to a projector, with the obstructions of item 4 stated beside it.

## 5. Task 7 — dynamical Born selection (UO-20), exploratory

In hand: `torusGenerated_eq_momentMap` (generation forces the moment map),
`rate_field_not_forced_by_torus_symmetry` (invariance does not). Open: whether the
interaction that writes a record forces `IsTorusGenerated`.

Plan, each step ending in a theorem or a counterexample:

1. *drift_rate_field*: the rate field that the drift coupling of UA-5 defines (the pointer's
   rate as a function of the base point) and whether it is generated in the sense of
   `IsGeneratedRateField`. For a projector `Π` the rate is `2 g ⟨Π⟩`, which is the moment
   map coordinate of the phase rotation generated by `Π`: so the *rate* is torus-generated
   while the *click probability* is not Born (Task 6). State both. (M)
2. *selection_or_no_go*: either the generator condition follows for every coupling of the
   form "profile times a Hermitian observable", or a coupling of that form with a rate
   field that is not generated. (M–L)
3. If neither closes: the physical assumption that is needed, named, with a proof that
   without it the conclusion fails (the necessity the author asks for).

This must not block workstream S, and nothing in §§6 to 8 depends on it.

## 6. Task 8 — what is left of packets

* The two-level clock, first part — done 2026-11-19 (`CV/DiracClockPacketD.lean`, UD-235):
  `levelCoherenceD_rate`, `hasDerivAt_devicePacketD`, `deviceCoherenceD_devicePacketD`. Left:
  *levelClockRateD_dilation* (the splitting at `k₀` against the rest splitting over the
  Lorentz factor of `groupVelD`), the error from the window's width, the normalised device.
* The two-level clock, second part — done 2026-11-19 (`CV/DiracClockDilationD.lean`, UD-238):
  `levelClockRateD_dilation`, `sq_div_latticeED`, `levelCoherenceD_rate_width`. Left: the
  lattice term `(Σ s_i⁴)/((2J)² E²)` against a spacing; the normalised device.
* **The two-level clock on a packet.** The carrier with two levels of different mass on the
  torus: `deviceHam` with the `d`-dimensional Hamiltonian in each block; the clock overlap
  rotating at the difference of the two bands' energies at the centre of the window, as
  `clockOverlap_rate` on the ring. *deviceHamD*, *clockOverlapD_rate*. (M)
* **`μ = 0`.** The energy is `|s|`, not differentiable at `s = 0`, and the `1/μ` bounds of
  UD-209 and UD-221 do not apply. For a window that stays away from zero momentum
  (`|s| ≥ s₀ > 0` on the window) the same proofs go through with `s₀` in place of `μ`:
  *abs_groupVelD_sub_le_massless*, *re_spinOverlapD_succ_ge_massless* (the spinor norm is
  `2 E²` and the alignment defect is `(2π |J| / (L s₀))²`). The ring's
  `dirac_massless_limit` is the template. Nothing is to be claimed for a window containing
  zero momentum. (M)
* **A family of lattices.** Done 2026-11-19 for the drift rate:
  `tendsto_two_pi_div_mul_windowStepErrD`. A limit of the whole bound, with the window
  re-chosen at each `L`, is not stated.

## 7. Task 9 — detectors and the cone on the torus

In hand: `RecordLayer/ChainCone.lean` (`SiteSupp`, `grow`, `growIter`,
`norm_commutator_chain_le`, `chain_record_kick_order`) for ring sites;
`RecordLayer/UnifiedCausalOrder.lean` for the coupled generators; `regionWeightD` and the
moving box for the torus.

Items 1 and 2 are done (2026-11-19, `RecordLayer/GraphCone.lean`, UD-230):
`norm_commutator_graph_le`, `hopsG_latticeDiracHam`, `norm_commutator_latticeDirac_le`. The
ring's theorems were not re-proved from the general ones; `HopsOne.hopsG` and `coe_growIter`
show they are the ring's case.

Items 3 and 4 are done in part (2026-11-19, `RecordLayer/GraphDetector.lean`, UD-231):
`graphDetector_not_displayed`, `torusDetector_not_displayed` (no display before the growth
reaches the carrier), `graphDetector_displayed` (display from a hypothesis on the occupancy).
The packet's box weight is joined to the arena's observable (2026-11-19,
`RecordLayer/TorusDetector.lean`, UD-234): `arenaObs_siteSetProj_packetD`,
`torusDetector_displayed_flatPacket`. Arrival and display in one run, and a `TickReadout` for
the arena, are done in conditional form (2026-11-20, `RecordLayer/TorusArrival.lean`, UD-242):
`torusDetector_arrival_flatPacket`, `arenaReadout`, `graphDetector_arrival_records`. An
instance with numbers is done (2026-11-20, `RecordLayer/TorusArrivalInstance.lean`, UD-243):
`torusDetector_arrival_instance`, two dimensions, `L = 8M`, `M ≥ 4·10⁶`. The pointer's
profile and the Clifford family are exhibited (2026-11-20,
`RecordLayer/TorusArrivalExhibit.lean`, UD-244): `torusDetector_arrival_exhibited`. A
detector given in advance is done (2026-11-20, `RecordLayer/TorusArrivalBox.lean`, UD-245):
`torusDetector_arrival_box`, the fixed box of arcs `arrivalBox`. Left: the composition with
the bound against the graph distance.

1. **The cone for any nearest-neighbour graph.** *SiteSuppG*, *growG*, *growIterG* for a site
   map into any finite type with an adjacency relation, and *norm_commutator_graph_le* with
   the same factorial bound. The ring's statements become instances (rule of two); the
   existing names are kept as corollaries, not duplicated. (M)
2. **The torus instance.** Adjacency "differ by one on one axis"; `latticeDiracHam` hops one
   (`latticeDiracHam_apply_eq_zero`). *latticeDiracHam_cone*. (S after 1)
3. **A region detector on the torus as a tick readout.** A pointer coupled to the projector
   on a box of sites; its record through `TickReadout` (Task 1's interface), so that it
   enters the record histories with no new semantics. *boxDetector_record*: the pointer
   displays once the packet's box (UD-221) has been inside the detector's box for long
   enough, and not before it arrives, with the times from the group velocity. (M–L)
4. **Record timing against the cone.** *boxDetector_not_before_cone*: no record before the
   graph distance over the hop rate allows. (M)

Acceptance: a two-dimensional carrier and detector whose record is a `RecordedFact`.

## 8. Tasks 10 and 11 — radar in `2 + 1` and `3 + 1`

Decided by the author (2026-11-18): M7 is marked on the three statements S1 to S3 of
[`unified-m7-feasibility.md`](unified-m7-feasibility.md); the moving group's chart needs the
caused return (§9).

Order, following the note's §8, with what each needs:

1. **Clocks on the torus**, at rest and moving in any direction: Task 8's clock on a packet
   and the tick readout. (M–L)
2. **Box gates for two carriers separating at an angle.** The coincidence of two moving
   boxes; open while they overlap, closed after. *boxGate_open*, *boxGate_closed*, with the
   weights from UD-221 for each carrier. This is the note's second risk and the first
   place a real obstruction could appear. (M)
3. **S2: a moving observer's count is its proper time**, for motion in any direction.
   Reuse `properTime_worldline`. (M)
4. **S1: a resting group's chart in `2 + 1`** (three observers) and `3 + 1` (four): `d + 1`
   messengers from one place, each observer's count at arrival, `trilateration_stable`.
   This is Task 10's and Task 11's first conjunct for a resting group. (M each)
5. **The mirror of one axis and the wall in four components**, then **S3: a moving
   observer's radar from a wall** with `radar_boostD`. (M, M)
6. **`m` pointers and `m` carriers on one arena**, and the open set of angles for them. (M–L)
7. **The moving group's chart from records** — only after §9 gives a return from a point
   event. Then the author's Task 11 conjuncts: a common event reconstructed, two groups
   with Lorentz-related coordinates, their intervals, a scaling family, and the anisotropy
   of UD-207 kept explicit. (L)

UO-17 is to be closed only with item 7 and an independent audit, as the author wrote.
Items 1 to 6 give Task 10 and Task 11 for what records give on the frozen arena.

## 9. The caused return (UO-26), items (2) to (5)

In hand: `transponder_launch_le_coincidence` (nothing before the meeting),
`Matrix.norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit` (first order, remainder small
before the meeting).

1. *coincidence_weight_of_boxes*: for a product of two packets, `‖P e^{−isH₀} X‖` is at most
   the square root of the weight of each packet outside its box plus an indicator that the
   two boxes are within the gate's relation. So the integrand of item (1) is zero until the
   boxes meet, up to the tails of UD-221. This makes "before the meeting" a statement
   about times. (M)
   Done in part 2026-11-19 (`RecordLayer/CoincidenceBoxes.lean`, UD-236):
   `sum_norm_sq_coincProj_mulVec_prod_le`, the bound at one time for one product vector, with
   the tails as `regionWeightD` of the complements on tori. The composite's free orbit of
   a product is the product of orbits — done 2026-11-19 (`RecordLayer/CoincidenceOrbit.lean`,
   UD-240): `sum_norm_sq_coincProj_freeOrbit_prod_le`. Left: the moving boxes; the passage
   from the vector's sum of squares to the operator norm under the integral of UD-226.
2. *launch_first_order*: the first-order term for the contact term and a product of
   packets, evaluated: its norm squared is `g²` times the square of the time the boxes
   overlap times the overlap weight, to leading order, with the remainder of UD-216. This
   is item (2): a signal does leave, with its weight. (M–L)
3. *launch_place_and_time*: the launched part is supported, up to tails, in the box where
   the meeting took place and is launched during the overlap. Its later motion is the free
   motion of the second level, at that level's group velocity. (M)
4. *echo_gate_reading*: a gate between the second level and an observer's clock, with a
   budget for a weight of order `g²`: the present gates need nearly full weight, so this
   needs either a strength that makes the launched weight of order one (beyond first
   order: a two-level Rabi estimate for the pair, exact when the two packets sit still) or
   a reading theorem for small weight. This is the first risk of UA-19 and the step most
   likely to change the plan. (L)
5. *radar_from_echo*: the radar identities of `RecordLayer/RadarTrilateration.lean` for a
   moving observer from the two readings. (M after 4)
6. The same on one arena: the contact term is the pointer's action on the fibres where its
   profile does not vanish, and the pointer also moves there. (L)

**Recommended by the charter (2026-11-19; not yet confirmed by the author): read the weak
echo by fibre typicality, not by a tuned resonance.** A strongly coupled transponder at
rest gives a full-weight return only when the strength times the overlap time is tuned,
which is a calibration put in by hand. In CSD a record is an ontic selection over the
fibre, and a weak signal writes a record on a set of fibres whose measure is proportional
to its weight: that is the click law (`diracClickProb_eq_lintegral`), exact and linear below
the cut-off. So step 4 becomes: *echo_click_law*, the echo's pointer displays on a set of
starting angles of measure proportional to the launched weight; and step 5 is stated on
that set, as a conditional statement with the record as the condition
(`HistoryPreparation`, as in UD-219). The radar identities then hold for the runs in which
the echo was recorded, which is how a weak return is used. The price: the echo's record
has probability of order `g²`, and the statement is about a set of fibres of that measure,
not about every run.

## 10. Task 12 — the capstone

One theorem on one arena, with seven conjuncts. For each, the theorem that would supply it
and what stands between:

| Conjunct | Supplied by | Gap |
|---|---|---|
| 1. Records on trajectories of the flow | `wallRunRay_eq_flow`, UD-208 | none in `1 + 1` |
| 2. A realised outcome is a record | `TickReadout.model`, `establishedFact_eq_some_iff` | none in `1 + 1` |
| 3. Recursion | `HistoryPreparation.appendFact`, UD-219 | the physical recursion is Task 5 |
| 4. Macroscopic description | `csd_radar_macrostate` | stability (§1) |
| 5. Causal structure | Task 4 | first brick (UD-239): events at flow times and the bound; the radar's events are open |
| 6. Operational geometry in `3 + 1` | Tasks 10, 11 | the arena of UD-219 is `1 + 1` |
| 7. Born statistics | Task 6 | conditional at best |

The honest shape today is a capstone in `1 + 1` on the walled chain's arena with conjuncts
1, 2, 4 and the `1 + 1` Lorentz statement, conjunct 3 as history concatenation, and 5 and 7
named as open. It should be written only when Task 4 has landed, and re-stated in `3 + 1`
when Task 11 has. A capstone that conjoins witnesses from different arenas is not to be
written.

## 11. Order of work

Critical path for workstream R: §1 item 4 (names the cell and the counts) → §2 → §4 → §3
Route B → §10 in `1 + 1`.

Critical path for workstream S: §6 clock on a packet → §7 items 1 to 3 → §8 items 1 to 4 →
§8 items 5, 6.

The caused return (§9) runs beside both and joins at §8 item 7 and §3 Route A.

Items that can each be done now with nothing in front of them: §1 item 4; §2
items 1 and 3; §3 Route B; §4 item 1; §6 (all three); §7 item 1; §9 item 1.

## 12. What would count as failure, by task

* Task 3: the string is not constant on the start set, and no finite description of its
  cells there is found.
* Task 4: the demonstrated influence cannot be separated from the permitted one by any
  theorem (only bounds from above exist).
* Task 5: Route A's second stage cannot be read (the launched weight is too small for any
  gate), and Route C is not admitted. Then the result is Route B's obstruction.
* Task 6: neither the obstruction nor the conditional bridge can be stated exactly.
* Task 9: the box detector's record cannot be timed against the group velocity.
* Tasks 10, 11: the box gate for carriers separating at an angle cannot be shown open and
  then closed with nearly full weight.
* The caused return: no reading of the launched level within any budget.

Each of these is to be reported with the inequality that fails.

References: [`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md) (UA-18,
UA-19, UO-17, UO-19, UO-20, UO-24, UO-25, UO-26, UD-50 to UD-52, UD-82, UD-83, UD-106, UD-107,
UD-196, UD-207 to UD-226); [`unified-m7-feasibility.md`](unified-m7-feasibility.md);
[`beyond-1p1-scoping.md`](beyond-1p1-scoping.md); `specs/BACKLOG.md` #296, #297, #298, #437,
~~#438~~, #439; `specs/future-work.md`.
