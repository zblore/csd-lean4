# M6 feasibility and error budget (Task 1 of the research delivery plan)

**Status: feasibility gate. Verdict at the end of §1. Written 2026-11-16 against `main` at
BACKLOG ~~#415~~ (the delivery plan names commit `6e41a448` as its baseline; ~~#413~~ to
~~#415~~ landed after it and are counted here).**

This note answers one question: can the packet, clock and gate constructions already in the
repository meet, together, every inequality that the top-down statement of UO-16
(`radar_lorentz_of_histories`, UD-164; `tri_radar_lorentz`, UD-170) needs, with a total
error that tends to zero along a family while the experiment keeps a fixed size? It is
reading and arithmetic. Nothing in it is a Lean theorem unless a name is given, and the
names given were checked against the source on the date above.

It does not restate the contract. The registers are in
[`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md); the residual list
R1 to R7 is under UD-164 there.

## 1. Verdict

**No obstruction was found. A compatible family exists on paper, and each of its
inequalities is either a theorem already or of a kind the repository has proved once on the
ring (UD-165, UD-166).** The total error is of order `16/k` in relative size, dominated by
the fixed number of ticks lost in reading five counts; every other term is `O(1/k²)` or
smaller. The experiment does not shrink: the two observers start a whole chain apart, the
moving observer has velocity `1/√5`, and a run holds about `1.1 k` ticks.

Three things came out of the work that the plan did not have, and each changes what has to
be built:

1. **The geometry is forced.** The swing theorems prepare a clock packet a quarter turn
   early, at the packet time `−π/(2R)`, and a flat packet sits at the angle `0` at packet
   time `0`. So the moving observer `B` necessarily starts within the angle `π v/(2k)` of
   the wall at `0`, and the messenger with it. The stationary observer `A` must therefore
   sit at the *other* wall, the angle `π`. This agrees with UA-18 (b). It means the
   distance is the whole chain (`d = π` in angle), not a free parameter.
   *Correction, 2026-11-16 (UD-194).* "The messenger with it" was wrong in one respect.
   The clock is prepared before the wall and moving into it. A messenger started at the
   clock's own angle and moving with it would be reflected and meet the clock a second time
   at once. The messenger has to start at the mirror place, moving away from the wall, and
   the emission is a coincidence with the clock's mirror image. The clock is reflected at
   the flow time `τ = π/(2 R_B)` and only then sets out, so against the times of §2 the
   relay is early by `b τ/a` and the meeting late by `τ`, a quarter of a tick: of relative
   size `O(1/k)`, the order of the tick discretisation. This is arithmetic on paper.
2. **`A` at the far wall is not built.** The clock at rest of UD-175 sits at the wall at
   `0`. A packet at the angle `π` is its translate by half the ring. No translation lemma
   exists in the repository. This is a new, necessary brick.
3. **The clock's bound must be taken at each packet time.** The bound of UD-176, taken at
   the end of the horizon `4π n/Δ`, carries `1/(20000 Δ n N)`, which does not vanish when
   the gap goes to zero. UD-184 restates it without the horizon; the test of §4 passes only
   with that version.

**Stop condition: not triggered.** The permitted couplings (coincidence projectors and
their complements times a clock's level swap, UA-18 (c)) and the flat packets are enough on
paper. The real risks that remain are listed in §6; two of them (the open set of pointer
angles, and the reading theorems' own size conditions on the walled chain) are unproved and
could still fail.

## 2. The construction that the theorems force

One ring of `M + 1` sites and length `2π K`, `K = 1200 n N`, with the mirror (reflect the
sites, change the sign of the lower component). The walled chain is its mirror-odd sector
(UA-18 (a)); the walls are the two self-mirror sites, at the angles `0` and `π`. Every
carrier is a wall state, a packet minus its mirror packet (UD-173), which is one packet on
`W ∪ −W` with odd amplitudes (`ringPacket_oddExt`, UD-174).

| Carrier | Packet | Starts | Moves |
|---|---|---|---|
| Messenger | `N` modes at momentum `1/2`, rest energy `μ = 1/k` (UD-182) | with `B` | at `u ≥ 1 − 2/k²` |
| Clock `B` | `N` modes at momentum `1/2`, levels `1`, `1 + Δ` (UD-177) | at the angle `−π v/(2k)`, beside the wall at `0` | at `v = 1/√5 ≈ 0.447` toward `π` |
| Clock `A` | modes `±1, …, ±N`, levels `1`, `1 + Δ` (UD-175), translated by half the ring | at the wall at `π` | at rest |

The run, in the angle measured from `A`'s wall, with `d = π`:

| Event | Kinematic time (UD-181) | Gate that marks it |
|---|---|---|
| Emission | `0` | messenger–`B` "near" closes at `(w − 2δ)/(u − v)` in angular units |
| Relay | `T_R = d` | messenger–`A` "apart" closes when the messenger reaches `π` |
| Return | `T_Ret = 2d/(1 + v)` | messenger–`B` "apart" closes; the messenger meets `B`'s mirror image |
| Meeting | `T_M = d/v` | `A`–`B` "apart" closes |

The five pointers of UA-18 (d) and their gates, as `triRun` (UD-170) takes them:

| Pointer | Clock | Gate | Open |
|---|---|---|---|
| 1, emission | `B` | messenger near `B` | from `0` until the emission |
| 2, return | `B` | messenger apart from `B` | from the emission until the return |
| 3, `B`'s meeting | `B` | `A` apart from `B` | from `0` until the meeting |
| 4, relay | `A` | messenger apart from `A` | from `0` until the relay |
| 5, `A`'s meeting | `A` | `A` apart from `B` | from `0` until the meeting |

"Near" is `wallNear w` (UD-178): within the angle `w` of a site or of its mirror image.
It is invariant under the mirror in either argument, so every gate commutes with the mirror
of each carrier and the coupled flow keeps the odd sector, also off the fibres where the
profiles vanish. That is a calculation here, not a theorem.

## 3. The family

For `k ≥ 2` (the values of `wall_values`, UD-184, with the margin of §4 still to be added):

| Quantity | Value | Why |
|---|---|---|
| `n = N` | `10¹⁶ k⁴` | the budget `≈ 16 k/N` must beat `ε δ²/5` |
| `K` | `1200 n N` | fixed by the flat windows |
| `M` | `≥ 210000 n² N` | the lattice term of UD-143; `a = 2π K/(M + 1) ≤ 1/(27 n)` |
| gap `Δ` | `k/K` | a run of length `≈ 7 K` holds `≈ 7 k` of phase |
| arcs' half-angle `δ` | `1/(10⁵ k)` | closing `4δ K/(u − v)` is `≤ 10⁻³` of a phase |
| gate width `w` | `3δ` | `w ≥ 2δ`; emission closes after `δ K/(u − v)` |
| messenger rest energy `μ` | `1/k` | `1 − u ≤ 2μ² = 2/k²` (`one_sub_vRel_half_le`) |
| gate weight `ε` | `1/(1000 k)` | `Δ · (run) · ε ≤ 10⁻²` |
| swing index `j` | any `j ≤ n/(2k)` | horizon `2π n/(j R) ≥ T_M`, error `1/(24 j)` |

The comparison scale does not shrink: `d = π`, `v = 1/√5` so `√(1 − v²) ≈ 0.894`, the run
lasts `T_M = π K/v ≈ 7.0 K` in the flow time and `R₀ T_M/(2π) ≈ 1.1 k` ticks.

## 4. The error ledger

Each line is one contribution to the bound of `penta_radar_lorentz` (UD-168), in relative
size against `T_M`. "Proved" means a theorem with that bound exists for the carrier on the
walled chain; "owed" names what is missing.

| Contribution | Source | Size along the family | Status |
|---|---|---|---|
| Tick discretisation (five counts: `7/2` ticks each gated, `7` for the away count) | `gatedErr`, `awayErr` (UD-163) | `≈ 18` ticks of `1.1 k`: **`≈ 16/k`** | proved as a function of the histories; histories owed |
| Messenger slower than `1`, at the relay and the return | `abs_crossRelay_sub`, `abs_crossReturn_sub_le`, `one_sub_vRel_half_le` | `≤ 2 v (1 − u)/u ≤ 4/k²` | proved (arithmetic); not yet joined to the gates' flow times |
| Gate closing intervals as timing tolerances | `gate_open_at_emission`, `gate_closed_away`, `gate_open_at_return` (UD-183) | `≈ 4δ v/(π (u − v)) ≈ 10⁻⁵/k` | proved for `2d ≤ π`; **owed for `d = π`** (§6, item 3) |
| Gate closing inside the count (`3 v_ptr (t_b − t_a)`) | `gatedErr` | `≤ 10⁻³` of a tick | follows from `wall_values` (ii) |
| Moving clock's rate against `√(1 − v²) R₀` | `abs_ringRate_sub_le` (UD-171), `κ = Δ` | `Δ = k/K < 10⁻³⁵` | proved |
| Velocity in the rate (lattice term `σ`) against the velocity of the packets (`p₀`) | `σ = 2J sin(a p₀)`, `|σ − p₀| ≤ a² p₀³/6` | `≤ a² ≤ 1/(729 n²)` | **owed** (one Lipschitz estimate) |
| Clock's two levels move at different velocities | `vRel 1 1 ·` against `vRel 1 (1 + Δ) ·` | relative `≤ Δ` | owed (the arcs already cover both levels; the intervals are not intersected) |
| Packet localisation, messenger | `one_sub_sum_arenaObs_wallArc_lightWall_le` (UD-182) | weight `≤ 4 · lightBudget/(1 − cos δ)` | proved |
| Packet localisation, clock `B` | `one_sub_sum_arenaObs_wallArcs_icoDevice_time_le` (UD-184) | the same with `μ = 1` | proved |
| Packet localisation, clock `A` at `π` | — | the same, after translation | **owed** (§6, item 2) |
| Both localisations against the gate | `wall_values` (i) | `ε ≤ 1/(1000 k)` | proved |
| Lattice dispersion | inside `limitErr` (`a²` term), hence inside the budgets | negligible | proved |
| Reflection | the wall state stays in its double arc through the wall | inside the budgets | proved (`light_wall_gate_open_return`) |
| Clock dephasing over the run | `wall_clock_swing_fine`, `wall_moving_clock_swing_fine` (UD-180) | `≤ 1/(24 j)` of the swing | proved; for `A`, after translation |
| Back-reaction of five pointers | — | to be made small by the choice of angles, for each `k` | **owed** (R7; §6, item 1) |

The gate weight and the dephasing do not add to the final error: they are absorbed by the
strict margins of the histories (`δ < 1/12`), which is what costs the fixed `7/2` ticks.
So

`ε_total ≈ 16/k + 4/k² + (terms below 10⁻⁵/k)`,

on the comparison scale `T_M`, and it tends to zero. This is bookkeeping from the proved
shape of the bound, not yet one inequality in Lean.

**The competing requirements, checked.** Making the messenger fast (`μ → 0`) raises its
budget by `1/μ` and `1/μ²` (`lightBudget`). With `μ = 1/k`: the start term is
`k²/(4K²)`, far below `1/N`; the drift term over a run is `k/(30 N)`. Both are beaten by
`N = 10¹⁶ k⁴`. `wall_values` proves this for the gate's bound, the closing interval and the
messenger's speed together.

## 5. The size conditions of the reading theorems

The histories come from UD-148, UD-157 and UD-159, which have conditions of their own. On
the ring `lap_radar_reading` (UD-165) reduced them to seven scalar inequalities. The same
seven, read for the family of §3:

| Condition (UD-165) | Family | Holds |
|---|---|---|
| `1 ≤ Δ K` | `k` | yes |
| `8 ≤ δ K` | `≈ 10²⁸ k⁷` | yes |
| `52 Δ ≤ δ ≤ 1/100` | `Δ < 10⁻³⁵` | yes |
| budget `≤ ε δ²/5` | `wall_values` (i) | yes, by a factor of about `12` |
| `Δ δ K ≤ 1/1000` | `10⁻⁵` | yes |
| `Δ K ε ≤ 1/1000` | `1/1000` | yes, with no margin |
| `18 Δ K ≤ n` | `18 k ≤ 10¹⁶ k⁴` | yes |

Two cautions. The walled run is about seven times a lap in phase, so the constants of the
sixth condition will need `ε` smaller by about ten; that is met by raising `N` by a
constant factor, which `wall_values` has room for only after its constants are redone.
And these are the ring's conditions: the walled chain's reading theorem has not been
stated, and its conditions may differ in constants. This table is evidence that they can
be met, not a proof.

The phase condition of UD-159 (`1/6 < |cos R t_a|`) holds because the emission is at the
start: `R t_a ≈ k δ/(u − v) < 10⁻⁴`. A later emission is not in this construction, and the
preparations it excludes are those with the emission late in the clock's phase (decision
(ii) of 2026-11-15 under UO-16).

## 6. What is not yet known, in order of risk

1. **The open set of pointer angles (R7).** All of the above is on the fibres where the
   five profiles vanish. Off them the route is a Duhamel bound (the template is UD-109,
   `fineFibres`): the carrier's propagator moves by at most the run length times the sum of
   the profile values, the displacements by that times the run length again, and the
   profile's derivative changes continuously. The histories have strict margins, so for
   each `k` a neighbourhood of the zero angles should work, of a size that shrinks with
   `k`. Nothing of this is built for five pointers and gated operators. It is the largest
   unproved step.
2. **Clock `A` at the far wall.** Needs the translation by half the ring: it commutes with
   the energy and with the mirror, and carries a ring packet to the ring packet with
   amplitudes `(−1)^m β_m`. Then UD-175 and UD-180 give `A`'s ticks and swing unchanged
   (they hold for any normalised amplitudes) and the localisation moves with it. Not built;
   no obstruction seen. The ring must have an even number of sites.
3. **Gate times for the whole chain.** UD-183 is proved for `2d ≤ π`. With `d = π` the
   angles run through a full turn, and the arithmetic needs the form of
   `cos_lt_cos_of_between` (`RecordLayer/UnifiedEmissionValues.lean`, UD-153's module) in place of monotonicity on a half turn.
   Routine; not done.
4. **The histories at the level of displacements.** `tri_radar_lorentz` asks for
   `IsGatedHistory` and `IsAwayHistory` of `coincShift`s. UD-148, UD-157 and UD-159
   conclude counts for the two-pointer flow; their inner steps (`abs_coincShift_sub_le`,
   `coincShift_stop_le`) are what the histories need, and have to be restated as histories.
5. **The walled chain's reading theorem and its constants** (§5).
6. **The odd sector as a chain** (Task 3). BACKLOG ~~#275~~ has the even sector as a
   segment (`segOf_diracHam_mulVec`); the odd one is not built, and the end hop `√2` of
   UA-18 (a) is unverified. This does not affect the feasibility of the Lorentz statement,
   which lives on the odd sector whatever it is called, but it does affect what the result
   may be said to be about.
7. **The speed margin.** `u − v ≥ 1/20` is taken in `wall_values`. For `k ≥ 3`,
   `u ≥ 7/9` and the margin is about `0.33`; for `k = 2` it is about `0.05`. To be proved
   from `one_sub_vRel_half_le` and the value of `vRel 1 1 (1/2)`.

None of these is a known obstruction. Items 1 and 5 are the ones that could still turn out
to be one.

## 7. The plan's tasks against what exists

| Task | State on 2026-11-16 |
|---|---|
| 1. Feasibility and error budget | this note |
| 2. Fast messenger on the wall | done as UD-182, UD-183 (`regionWeight_lightWall_away_le`, `one_sub_vRel_half_le`, `light_wall_gate_open_return`); the plan's three proposed names are these, and no aliases are added |
| 3. The odd sector as a chain | done the same day as UD-186 (`odd_sector_chain_flow_equiv`, BACKLOG ~~#416~~): the boundary condition of UA-18 (a) is confirmed, the `√2` end hop included |
| 4. Event times from propagation | the kinematic times and two relations (UD-181); gate intervals (UD-183) and, since UD-188, for the whole chain and at an observer at a wall, with the tolerances `τ_R`, `τ_Ret`, `τ_M` from a gate window. The seven conditions for the wall states' angles, both levels, from thirteen inequalities: `radar_gate_intervals` (UD-194); explicit times meeting the thirteen under six conditions: `radar_gate_times`. Owed: the six conditions for the family (Task 8) |
| 5. Both clocks' readings | `B`: ticks, swing, place (UD-177, UD-180, UD-184). `A`: swing and place at any translate, the far wall included (UD-187); its count not restated. Rate relation with the packets' velocity: `wall_observer_clock_rate_relation` (UD-188) |
| 6. Five histories | the reduction (UD-170), the gates for a messenger and a clock (UD-179, UD-182, UD-183), the two clocks' gate for any rays (UD-185). The two kinds of history from where two carriers are: `isGatedHistory_coincShift`, `isAwayHistory_coincShift` (UD-189). Two of the five applied: the moving observer's emission and return histories (`wall_observer_radar_histories`, UD-190). The other three: `wall_relay_history`, `wall_meeting_history_moving`, `wall_meeting_history_rest` (UD-191, UD-192). All five are theorems for the wall states, and are joined for one prepared state with one strength per clock in `tri_wall_radar_lorentz` (UD-193). The sizes are owed |
| 7. The return reading's band | derived from sizes for an emission at the start, inside `wall_observer_radar_histories` (UD-190); the inequality is not yet checked for the family |
| 8. A family meeting every inequality | `wall_values` (UD-184) for the budget; the six conditions of the gate times and the sizes of UD-193 for `k ≥ 100`, gate weight `1/(500 k)`, swing index `k`: `radar_family_gate_conditions`, `radar_family_all_conditions` (UD-195). Joined with UD-193 in `radar_family_lorentz` (UD-196) |
| 9. An open set of interacting starts | scoped only (the paragraph after the scope of UD-175) |
| 10. Capstone | a first form on the fibres where the profiles vanish, conditional on the angle conditions and the sizes: `tri_wall_radar_lorentz` (UD-193). For the family, with no hypothesis about angles, sizes or histories and an error of `150 K/k` (about `21/k` of the run): `radar_family_lorentz` (UD-196). Owed: the open set of pointer angles (Task 9), without which this is not the plan's capstone |
| 11 to 12 | not started |

## 8. What would count as failure

If, for the family of §3 with any choice of constants, the walled chain's reading theorem
needs a condition that contradicts `wall_values`; or if the Duhamel bound of §6, item 1
cannot be made smaller than the histories' margins for any non-empty open set of angles:
then the arrangement of UA-18 cannot meet UO-16, and that is to be reported as an
obstruction with the inequality that fails.

References: [`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md) (UA-18,
UO-16, UD-163 to UD-185); `specs/BACKLOG.md` ~~#402~~ to ~~#415~~;
`RecordLayer/UnifiedRadarSkeleton.lean`, `RecordLayer/UnifiedPentaRun.lean`,
`RecordLayer/UnifiedTriCarrier.lean`, `RecordLayer/UnifiedWallValues.lean`,
`RecordLayer/UnifiedReturnValues.lean`.
