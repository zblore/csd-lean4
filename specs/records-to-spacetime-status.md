# Records to spacetime: where the line stands (2026-11-04)

**Purpose.** One page on BACKLOG #38/#39's line after the 2026-11-03/04 rows: what the Lean proves,
what it assumes, what is open. [`records-to-spacetime-scoping.md`](records-to-spacetime-scoping.md)
(2026-09-19) said "nothing of it is in Lean"; that is no longer true, and this note says what is. Every
item is `sorry`-free and pinned to the foundational triple. Everything is in 1+1 dimensions.

## What is proved

1. **Observers recover Lorentz kinematics from their own records, with explicit errors.** Detectors,
   clocks and radar built from the lattice Dirac chain; the radar chart equals the Lorentz map to an
   error that scales away (`radar_lorentz_exact`, `radar_lorentz_scaling`, ~~#278~~, ~~#280~~); the
   measurement floor is a theorem (`sine_packet_floor`, ~~#284~~); clock reading errors are bounded
   (`quad_clock_reading_error`, ~~#283~~).
2. **No record statistic singles out a frame**, within those errors: the radar relation
   (`radar_frame_covariant`, ~~#285~~) and every Lipschitz statistic of encounter readings
   (`record_statistic_covariant`, ~~#287~~). The lattice frame shows only at order `a²`
   (`lattice_frame_residue`).
3. **The ontic order of spacelike writes is invisible** to Σ records (`sigma_record_write_order_indep`,
   `sigma_record_kick_order`, `chain_record_kick_order`, ~~#285~~, ~~#286~~) and to QM statistics
   (`twoRecordLaw_props`).
4. **Entangled pairs carry a hidden preferred slicing.** The order in which Σ selects the two wings
   fixes individual outcomes, never statistics (`selection_order_dependent`); order-independent outcomes
   with local first writes are excluded by Bell (`no_order_indep_local_first_selection`, ~~#288~~). With
   the author's choice that the ontic time decides (~~#290~~), a boost of the preparation that reverses
   two spacelike writes changes individual outcomes on positive measure and no probability
   (`spacelike_boost_changes_outcomes`); timelike writes are unaffected (`timelike_onticCell_boost`).
5. **One click.** Each ontic point writes exactly one site at one time; site frequencies over
   preparations are the packet's site weights (`dirac_packet_one_click`, on `T²`, ~~#266~~).
6. **Detectors that push.** A coupling generates the detectors; the device's kick is bounded uniformly
   in time (`mom_mem_Icc`), the passage is still written (`coupledPassageWrite`, ~~#251~~), and the
   coupled flow preserves Lebesgue measure (`measurePreserving_coupledEvolve`, ~~#291~~).

## What is assumed

* **Relativity is input.** The Dirac chain was chosen with a relativistic continuum limit, so light
  speed and dilation are in the model; items 1–2 show the chain's matter realises them in records.
* **Detector laws are stated where not generated:** #252's register gain, #266's click rate `κ` and
  record arcs; only #251's control-device detectors come from a coupling.
* **QM's weights are input**, never constructed: site weights and joint tables size the record cells.
* **Locality is chosen** (product dynamics for the two wings, `LF6.localDeisolation_factorises`).
* **Which wing is selected first** for an entangled pair: the author's choice (a), not derived.
* **Every record layer here is kinematic**: no `H_int` generates the cells (R-016).

The programme that takes these results to one shared Hamiltonian arena, with its registers of what is
assumed, derived and owed, is [`unified-record-spacetime-plan.md`](unified-record-spacetime-plan.md).
Its gate A is answered (BACKLOG ~~#355~~): on that arena the click probability of the pointer is
fixed by the flow and is not the expectation of an operator (`RecordLayer/DiracPointerClick.lean`,
`diracPointer_clickLaw`). The entry *QM's weights are input* above stands.
Given that input, the basin statistic along the coupled flow is within a stated back-reaction term
of QM's weight (BACKLOG ~~#356~~, `RecordLayer/DiracPointerBasin.lean`,
`abs_diracBasinProb_sub_zero_coupling_le`).
A two-level clock is in the joint energy of an extension of that arena, and the pointer coupled to
it follows the clock's hand at the dilated rate within stated errors (BACKLOG ~~#357~~,
`RecordLayer/UnifiedDiracClock.lean`, `clock_pointer_device`). Those statements are in the flow
parameter. A time recovered from clock records is not derived there.
Read through a threshold, each swing of that pointer is a tick record of the same flow. The count of
ticks uses no value of the flow parameter, and the count times the rest period is within one tick
plus the finite-splitting term of the dilated flow time (BACKLOG ~~#358~~,
`RecordLayer/UnifiedDiracClockTicks.lean`, `clock_tick_device`). The swing is proved outright for
one mode on a null set of fibres and is a hypothesis elsewhere. No degree of freedom holds the count
(`not_ae_count_advances_clockPointerFlow`).
One arena now carries this clock's pointer and a site pointer under one flow, and another carries
two site pointers on the Dirac ring (BACKLOG ~~#359~~, `RecordLayer/UnifiedTwoPointer.lean`,
`clockSiteFlow_apply`, `diracTwoPointerFlow_apply`). Each restricts exactly to the one-pointer flow
on the fibres where the other profile vanishes, and elsewhere the departure is bounded and grows as
the square of the time.
On the first of these a tick record of the clock's pointer and a position record of the site pointer
are occurrences of the one flow from one start state (BACKLOG ~~#360~~,
`RecordLayer/UnifiedClockSiteRecords.lean`, `clockSite_records_train`). That holds outright for one
momentum mode on the fibres where both profiles vanish, a null set, where the device moves freely
and the record does not single out its site. Elsewhere the swing and the write are conditional on
stated inequalities, with the cross-talk as one more error term. All record times are flow times. No
record is read on the arena of two site pointers.
The coupled generators of both arenas hop at most one site of the ring, and the cone bound holds for
them (BACKLOG ~~#361~~, `RecordLayer/UnifiedCausalOrder.lean`, `norm_commutator_hopsOne_le`). A site
pointer's displacement responds to a kick of the carrier far away, or to the other site pointer's
conserved angle, by at most a factorial tail in the distance (`abs_diracTwoKickResponseSnd_le`,
`abs_diracTwoAngleResponseSnd_le`), and the position record of ~~#360~~ survives a remote kick
within margins (`isRecordWrite_clockSiteFlow_site_of_kick`). These are upper bounds: suppression
and not exclusion, exact only at time `0`, with no response shown to arrive. No order between record
events is built. No such bound is proved for the clock's pointer: the level swap is supported on no
proper set of sites, so the argument does not apply to it. No instance in which the record's
margins hold is exhibited.
The interventions are changes of the initial point and are assumed.

## What is open

* **The one large gap: beyond 1+1** (#289, split 2026-11-04 into #292–#301;
  [`beyond-1p1-scoping.md`](beyond-1p1-scoping.md)): Lorentz kinematics, a spatial radar chart,
  the lattice's preferred directions at `O((ap)²)`, packets and records in `d` dimensions.
* **Polish in 1+1**: #263 (packet shape, M), #281 (moving observer's speed calibration, M–L), #276
  (sharp return window, L), #254 (self-launched signals, M–L), #255 (recoil, L), #282 (parked).
* **Generation**: the click clock from a coupling on the Dirac chain (not yet a row); `H_int` (R-016).

## Reading

In 1+1, the record layer is Lorentz compatible in the sense row #285 asked for: no record statistic
shows the ontic frame, within explicit errors that vanish in the continuum limit, and the frame survives
only in individual entangled outcomes, as in Bohmian mechanics. The open choice is whether to take the
same statements to 3+1 (#289) or to generate what is now stated (detector laws, `H_int`).

References: `specs/BACKLOG.md` #38, #39, #278–#291; `records-to-spacetime-scoping.md`;
`RecordLayer/FrameCovariance.lean`, `SelectionOrder.lean`, `OneClick.lean`, `CoupledDetector.lean`,
`CoupledLiouville.lean`, `ChainCone.lean`; `CV/SigmaSlicing.lean`; `specs/future-work.md`.
