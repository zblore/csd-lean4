# M7 feasibility on the unified arena

**Status: feasibility gate for UO-17. Verdict in §1. Written 2026-11-17 against `main` at
BACKLOG ~~#295~~ (commit `6d855bff`).**

This note answers one question: can the arena and the theorems of M6 (UA-18, UO-16) carry
the statements of BACKLOG #296 to #298 to `d` space dimensions, and what has to be built or
decided first? It is reading and arithmetic. Nothing in it is a Lean theorem unless a name
is given, and the names given were checked against the source on the date above. Every
calculation marked "on paper" is unchecked by Lean.

It does not restate the contract. The registers are in
[`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md); the rows are in
[`beyond-1p1-scoping.md`](beyond-1p1-scoping.md); the form of this note follows
[`unified-m6-feasibility.md`](unified-m6-feasibility.md).

## 1. Verdict

**Feasible in part. One statement of #298 cannot be had on the arena as it is frozen, and
that needs the author's decision (§7).**

* **No obstruction was found for the carriers.** The lattice of UD-206 takes packets,
  clocks, box-shaped coincidence gates and tick counts in `d` dimensions by the methods M6
  used on the ring. The work is the size of M6's ring-typed layer again (§2), and #296 is
  part of it: it cannot be skipped.
* **No obstruction was found for three record statements in `d + 1`** (§5): a resting
  group's spatial chart of one event by trilateration (S1); a moving observer's count
  against proper time, for motion in any direction (S2); a moving observer's radar time and
  distance of an event on a wall against the boost, for motion in any direction (S3).
* **Obstruction: a moving group in general position cannot radar one event** (§4). The
  only reflectors the arena has are flat walls, and a messenger that goes out to an event
  and straight back reaches only observers on one line through that event. So "a moving
  group's chart is the Lorentz transformation of a resting group's"
  (`trilateration_chart_boostD`, #293) has no instance on this arena. It stays a theorem
  of kinematics.

Four more things came out of the reading. Each changes what has to be built.

1. **A two-component field in `d = 2` has no wall.** The wall of UA-18 (a) is a mirror-odd
   sector. A mirror of axis `i` needs a spinor matrix that anticommutes with `α_i` and
   commutes with the other `α_j` and with `β`. For `cliffordTwo` (`σ_x`, `σ_y`; `σ_z`) no
   such matrix exists: commuting with `σ_y` and `σ_z` forces commuting with `σ_x`. For
   `cliffordThree` (`σ_x ⊗ σ_i`; `σ_z ⊗ 1`) the matrix is `σ_z ⊗ σ_i`. On paper.
2. **Walls on two axes need more components.** In `cliffordThree` the mirror matrices of
   two axes anticommute, and they are fixed up to a factor, so the two mirrors have no
   joint odd sector. A box with walls on every axis needs four components at `d = 2`
   (mirrors `σ_z ⊗ σ_1` and `1 ⊗ σ_1` for the family `σ_x ⊗ σ_1`, `σ_x ⊗ σ_2`; `σ_z ⊗ 1`)
   and eight at `d = 3` (a second two-level factor carrying one Pauli matrix per axis). On
   paper. UD-206 holds for any Clifford family on any finite spinor type, so it covers
   these families; they are a choice of carrier under UA-8.
3. **M6's results do not transfer by the stability theorem.** A packet localised across the
   direction of motion uses a window of `N'` transverse modes. On that window the
   `d`-dimensional symbol differs from the one-axis symbol by `|s_⊥|` in norm, first order
   in the transverse momentum, although the energies differ only at second order. The bound
   of `abs_arenaObs_idxFreeU_sub_le` (UD-198) is the run length times that norm, which is
   of order `N' ≥ 1` for a run of M6's length. So the ring's theorems have to be proved
   again on the torus, by the translation phase of each axis (#296), not carried over.
4. **The exact reduction to the ring is not local.** Carriers with transverse mode number
   zero obey the one-axis chain exactly. They are sheets, uniform across the motion, and a
   gate that reads them with nearly full weight must be a slab: one where the two carriers
   are close along one axis at any transverse separation. That is not a coincidence in
   `d` dimensions, so UA-18 (c) does not admit it.

**Stop condition: triggered for one statement only** (the moving group's chart), by the
argument of §4. Not triggered for the carriers or for S1 to S3.

## 2. What of M6 is free of the dimension

Counted on the date above over `RecordLayer/Unified*.lean` (78 modules).

| Layer | Modules, lines | Typed to | Carries to `d` dimensions |
|---|---|---|---|
| The count arithmetic, the run, the histories from where two carriers are, stability, the open set (`radar_lorentz_of_histories`, `penta_radar_lorentz`, `tri_radar_lorentz`, `isGatedHistory_coincShift`, `isAwayHistory_coincShift`, `IsGatedHistory.of_drift`, `tri_radar_lorentz_open`) | 25 modules, about 9,200 lines | any finite carrier index, any site type, any relation | as it stands, for five pointers, three carriers and the head-on geometry |
| Packets, walls, clocks, gate times, values, the family | 53 modules, about 27,700 lines | `ZMod L × Fin 2` | to be proved again on `(ι → ZMod L) × S` |

Three limits of the first layer. The flows exist for two, three, four and five pointers,
each built by hand (`LF4/EchoVolume.lean`, `LF4/TriCoupledFlow.lean`,
`LF4/QuadCoupledFlow.lean`, `LF4/PentaCoupledFlow.lean`); the step that adds one pointer
is general (`LF4/PointerStep.lean`), a flow for `m` pointers is not built. The composite
is of three carriers (`triRun`). And the relations `TR − TE = v (TM − TE)`,
`TRet − TR = v (TM − TRet)` of `radar_lorentz_of_histories` are those of two observers on
one line.

The gates need no change: `coincProj` and `gateOp` take any site type and any relation, so
"within a box" on the torus is an instance.

## 3. The carrier layer on the torus

What M6 used, and its counterpart. "Paper" means no obstruction seen; nothing is built.

| M6 on the ring | On the torus of UD-206 | State |
|---|---|---|
| Modes, dispersion, clock dilation | `latticeDiracHam_mulVec_diracModeD`, `abs_clockRate_div_sub_le` at `s := ‖s‖` | proved (UD-206) |
| The rate's velocity against the packet's velocity | `abs_scaledVelD_sub_le`, each component | proved (UD-207) |
| The packet's place: the translation phase and `limitErr` | one phase per axis, a box for the arc, the weight outside the box at most the sum over the axes | paper (#296) |
| The wall and the wall state (UD-173, UD-174) | one mirror: `σ_z ⊗ σ_i` at four components; a box: §1, item 2 | paper |
| Clock at rest, moving clock, swing (UD-175, UD-177, UD-180) | the same with a product window; the moving clock's momentum in any direction | paper |
| `ringNear`, `wallNear` | near in every axis; with walls, near any mirror image | paper |
| Gate times (UD-183, UD-194) | separation of two straight motions in `d` dimensions; closing speed at least `1 − v` | paper |
| The cone (`RecordLayer/UnifiedCausalOrder.lean`, `norm_commutator_chain_le`) | graph distance on the torus (#297) | paper; independent of the rest |

**The error budget does not change in kind.** For a window of half-width `D` in momentum on
a ring of length `2π K`, M6's term is the run length times the mode spacing times the
spread of the group velocity over the window, `7 k D` up to constants (`limitErr`). A
transverse axis adds a term of the same form: the transverse group velocity is
`c² p_⊥/E`, zero at the centre, with the same spread. The longitudinal phase gets a cross
term of second order, `D D'`. The union over `d` axes multiplies the weight outside the
box by at most `d`. M6 met `budget ≤ ε δ²/5` by a factor of about `12`, so the constants
have to be redone and `N` raised by a constant factor. On paper.

**The lattice's preferred directions are far below the budget.** A massless messenger along
the unit direction `n` loses `(a p)² Σ n_i⁴` of `c²` in its squared speed
(`massless_anisotropy`, UD-207). Along M6's family `a ≤ 1/(27 n)` with `n = 10¹⁶ k⁴` and
`p = 1/2`, so the term is below `10⁻³⁵/k⁸`, against a total error of order `16/k`. It
enters S1 as an explicit error in each distance. It does not threaten any inequality.

## 4. A wall returns a messenger, a point does not

On the fibres where the profiles vanish a gate does not move a carrier (UD-198: the
carrier follows its free orbit). So a messenger turns round only at a wall, and a wall
reflects as a flat mirror: the reflected state is the mirror image's free motion.

Radar of an event `P` by an observer at `b` with velocity `u` needs the messenger to go
from the observer to `P` and straight back to the observer. Let `m` be the mirror that
acts at `P` (one wall on a face, two on an edge, all `d` at a corner). The return reaches
the observer at the time `t` exactly when `m (b + u t − P) = −λ (b − P)` for some
`λ > 0`, with `t = ‖b − P‖ (1 + λ)`. That is `d + 1` equations in `b`, `λ` and `t`,
homogeneous in `b − P`: the solutions are one ray from `P`. At a corner the ray is the
line of `u`. For `u = 0` and `P` a corner every `b` is a solution. On paper.

So:

* **A resting group can radar a corner from any positions.** The corner reflects every
  messenger back along its path. This needs walls on all `d` axes (§1, item 2).
* **Moving observers who radar one event are collinear with it.** Their displacements do
  not span space, `RadarGeneralPosition` fails, and trilateration has nothing to work on.
* **Returns by two or more reflections do not help.** The event is then one reflection on
  a longer path, and `(r − e)/2` is not the distance to it.
* **A small obstacle does not help with the present readings.** It scatters a small part
  of the messenger toward each observer. The histories need nearly all of the messenger's
  weight at the observer (`isGatedHistory_coincShift`, the hypotheses `hopen`, `hclosed`).

Not examined: a moving observer who locates itself by radar from `d` walls. Each wall is a
moving plane in its frame, and #293 has no theorem for radar from a plane.

## 5. What can be stated

Each needs the carrier layer of §3 first. Counts are for `d` space dimensions.

| | Statement | Arena | Carriers, pointers | Kinematics used |
|---|---|---|---|---|
| S0 | M6's run along one axis, with boxes for arcs | one wall axis, four components | 3, 5 | `radar_lorentz_of_histories` as it stands |
| S1 | **A resting group's spatial chart.** `d + 1` messengers leave one place at the common start, one toward each of `d + 1` resting observers in general position. Each observer's count when its messenger arrives is its distance from that place. The only point with those distances is within `K Σ (errors)` of the place | plain torus, any family | `2 (d + 1)`, `d + 1` | `trilateration_stable` (#293) |
| S2 | **A moving observer's count against proper time.** The same reading by an observer moving in any direction: its count is `√(1 − v²)` times the resting rate times the kinematic arrival time | plain torus, any family | 2, 1 for each observer | `properTime_worldline` (#292) |
| S3 | **A moving observer's radar from a wall.** For motion in any direction, the emission and return counts give the boosted time of the reflection and its distance in the observer's frame | one wall axis, four components | 2, 2 for each observer | `radar_boostD` (#293), one observer |

S0 has no content beyond `1 + 1`. It would show that the torus carries UO-16's statement.

S1 is the first statement with `d` coordinates read from records. Its clocks need no
exchange of signals to agree: every gate is open from the common start, as in M6. That is
the reason it cannot be given to a moving group. A moving group's clocks, started together
in the lattice's frame, are not synchronous in their own, and the offsets are what radar
would have removed.

S2 and S3 are statements about one observer and one messenger at a time. Observers do not
interact, so on the fibres where the profiles vanish the run of several of them is a
product of runs for two carriers. The two-carrier flow with two gates exists for any
carriers (`coincFlow`, `coincFlow_gated_reading`). Joining them in one composite ray on
one arena with `m` pointers is owed (§2).

S3 with the observer moving along the wall is the light clock: the moving observer and a
resting one at the same height read the same radar distance to the wall.

## 6. What is not yet known, in order of risk

1. **The packet layer in `d` dimensions (#296).** Everything rests on it. The method is
   M6's, one axis at a time; the cross terms and the union over the axes are on paper only.
2. **The readings for motion at an angle.** M6's gate times are for motion on one line.
   For S2 and S3 the messenger and the observer separate at an angle, and the box gate
   closes when the first axis leaves its arc.
3. **The wall in four components.** The mirror `σ_z ⊗ σ_i`, the odd sector as a lattice
   with a hard face, and its boundary condition. M6's Task 3 did this for the chain
   (UD-186). It affects what S0 and S3 may be said to be about.
4. **`m` pointers and `m` carriers on one arena.** Needed for S1 as one theorem, and for
   M9's one arena. The step is general; the run and its solution on a fibre are built for
   five.
5. **The open set of pointer angles.** M6 has it for five pointers (UD-200, UD-205). For
   the runs of §5 it has to be had again, for two pointers or for `m`.
6. **The family's constants** (§3).

None of these is a known obstruction. Items 1 and 2 are the ones that could turn out to
be one.

## 7. The decision for the author

UO-17 reads "#294–#298, on the unified arena", and #298 asks that the chain's records give
"a trilateration chart within `ε` of a Lorentz transformation". By §4 the arena gives a
trilateration chart to a resting group only. The choices:

* **(a) Mark M7 on S1 to S3.** A spatial chart from records for the resting group; for
  moving observers, proper time and radar from a wall in any direction, one observer at a
  time. The statement "a moving group's chart is the boost of a resting group's" is then
  the kinematic theorem of #293 and is not instantiated by records. UO-17 would say so.
* **(b) A prepared echo.** For each moving observer a second messenger is prepared at the
  event, leaving toward that observer when the first arrives. The out and back legs are
  then joined by the preparation, not by a record. This stays within UA-18 (c). It needs a
  new clause saying what such a pair of readings is.
* **(c) A new mechanism for the return.** A reading from a small scattered part of the
  messenger, or a coupling that turns a messenger round. Neither is of the kind admitted by
  UA-18 (c), which the author fixed on 2026-11-14 as coincidence only. It would need a new
  assumption and a new reading theorem.

The charter does not settle this. UA-18 (c) rules out (c) as it stands. Between (a) and
(b) the difference is what M7 is allowed to claim.

**Decided by the author, 2026-11-18.** (a) now: M7 is marked on S1 to S3. (c) is to be
worked through as obligation UO-26 of the contract (BACKLOG #437). (b) is not admitted: a
prepared echo joins the two legs by the preparation, which assumes the causal relation it
would show. The first brick of UO-26 is `Mathlib/Analysis/Matrix/DuhamelState.lean`
(`norm_mul_exp_neg_I_add_mul_le`): a term of the energy moves a state off its free orbit by
at most the time integral of that term on the free orbit.

## 8. An order of work that does not wait for the decision

Every item is needed under (a), (b) and (c). Prices are the usual letters and are not
estimates of time.

1. Packets on the torus: one phase per axis, the box, the budget (#296; L).
2. Clocks on the torus: at rest and moving in any direction; ticks, swing and place (M–L).
3. Box gates and the two readings for motion at an angle (M).
4. S2, then S1 with its `d + 1` runs side by side (M each).
5. The cone on the torus (#297; M). Independent of 1 to 4.
6. The mirror of one axis and the wall in four components (M), then S3 (M).
7. `m` pointers and `m` carriers on one arena; the open set (M–L).

## 9. What would count as failure

If the weight of a `d`-dimensional packet outside its box cannot be brought under the
gate's budget for any family with a fixed experiment; or if a box gate for two carriers
separating at an angle cannot be shown open and then closed with nearly full weight: then
the arena does not carry S1 to S3, and that is to be reported with the inequality that
fails.

References: [`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md) (UA-8,
UA-18, UO-16, UO-17, UD-186, UD-198, UD-200, UD-205, UD-206, UD-207);
[`beyond-1p1-scoping.md`](beyond-1p1-scoping.md); `specs/BACKLOG.md` ~~#292~~ to ~~#295~~,
#296 to #298; `CV/DiracLatticeD.lean`, `CV/DiracAnisotropy.lean`, `CV/DiracPacketLimit.lean`;
`RecordLayer/LorentzKinematics.lean`, `RecordLayer/RadarTrilateration.lean`,
`RecordLayer/UnifiedRadarSkeleton.lean`, `RecordLayer/UnifiedTriCarrier.lean`,
`RecordLayer/UnifiedWallHistories.lean`, `RecordLayer/UnifiedFibreDrift.lean`,
`RecordLayer/UnifiedCoincidenceFlow.lean`, `RecordLayer/UnifiedGatedReading.lean`,
`RecordLayer/UnifiedCausalOrder.lean`, `RecordLayer/ChainCone.lean`; `LF4/PointerStep.lean`,
`LF4/PentaCoupledFlow.lean`.
