# M6 audit: the proof-dependency audit of `csd_operational_lorentz_from_records`

**Status:** written 2026-11-17 (Task 12 of the research delivery plan for UO-16; BACKLOG
~~#432~~). Contract: `specs/unified-record-spacetime-plan.md` (UO-16, UD-164, UD-193, UD-196,
UD-200, UD-201, UD-202). This note audits one theorem,
`CSD.RecordLayer.csd_operational_lorentz_from_records`
(`RecordLayer/UnifiedRadarGeometry.lean`), against the plan's list and against the test of
UO-16. The mark of UO-16 (§6) is the author's, made 2026-11-17 after this audit.

## 1. The theorem and its hypotheses

Hypotheses: `100 ≤ k`; `210000 · N² · N ≤ M` with `N = wallN k`; `M + 1 = 2H`. Nothing else.
Conclusion: three packets' non-vanishing, two strengths `0 < g_A ≤ R₀/5`, `0 < g_B ≤ R_B/5`,
and a set `U` of the ten pointer angles that is open, of positive measure, and contains the
start `(1/12, 0)` of every pointer; from every point of `U`, `WallRadarGeometry` for
`wallRunAt`: five counts at every choice of flow times in the five reading windows, the
comparison of `restEvent` boosted by `v = vRel 1 1 (1/2)` with `movingEvent` within
`151 K/k` in both components, and the comparison of the two intervals.

Axioms (pinned in `Tests/AxiomAudit/SigmaLayer.lean`): `propext`, `Classical.choice`,
`Quot.sound`, for the theorem and for every declaration of the six modules of ~~#430~~ to
~~#432~~.

## 2. The dependency chain

| Layer | Object | Where | What is proved |
|---|---|---|---|
| Ontic | one point of `PentaSigma D`: a product ray of three packets and five pointer angles | `wallRunAt_orbit` (UD-202) | the run is `t ↦ Φ_t x₀`, a definitional equality |
| Geometric | `pentaForm`, `fiveCoupledEnergy`, `pentaMuL` | `LF4/PentaCoupledFlow.lean`; `triFlow_map_pentaMuL` (UD-202) | `Φ_t` is the Hamiltonian flow of the energy for a symplectic form and preserves `μ_FS ⊗ vol⁵` |
| Carriers | the solved flow on every fibre | `pentaRun_fibre` (UD-198) | the carrier moves by the free flow of the fibre's matrix; each pointer by its accumulated gate expectation |
| Measurement | tick counts of five pointers | `IsTickCount.exists_crossings` (UD-202); `radar_lorentz_of_histories` (UD-164) | a count is a number of crossings of the one orbit between two disjoint regions; five histories give five counts |
| Histories | the five histories for wall states | UD-190 to UD-193; off the zero fibres UD-197 to UD-200 | from where the carriers are (packet bounds), on a neighbourhood of the zero fibres |
| Family | rates, gate times, sizes | UD-194 to UD-196, UD-201 | every hypothesis discharged for `k ≥ 100` |
| Operational | `restEvent`, `movingEvent` | UD-202 | functions of the counts alone |
| Spacetime | boost comparison, interval comparison | `WallRadarLorentz.geometry` (UD-202) | within `151 K/k`; intervals within `4600 K²/k` (UD-203) |

## 3. The plan's nine checks

| Check | Verdict | Evidence |
|---|---|---|
| No new axiom declarations | pass | `check-axiom-imports`, `check-axiom-sweep`; the pins of §1 |
| No `sorry` or `admit` | pass | `check-placeholder-status`; the pins exclude `sorryAx` |
| No theorem proved by assuming its conclusion through a renamed field | pass | the hypotheses of §1 are three inequalities on naturals; `IsGatedHistory` and `IsAwayHistory` are hypotheses of UD-164 only, and are proved for the model in UD-190 to UD-200 |
| No unrecorded dependence on the target Lorentz formula | pass, with F3 | the formula is the conclusion of UD-164 from five histories, two relations between flow times (`radar_times_relay`, `radar_times_return`, proved for the kinematic times at speed `1`) and the rate relation `R_B ≈ √(1 − v²) R₀` (`wall_observer_clock_rate_relation`, proved from the carriers' energies with the error `κ`) |
| No reliance on a disconnected witness from another arena | pass | every statement is about `wallRunAt`, one flow on UA-18's arena (`wallRunAt_orbit`) |
| No unverified substitution of continuum velocity for lattice velocity | pass | `v = vRel 1 1 (1/2)`; the lattice correction is the term `(a p)² p/6`-type in `κ` (UD-188) and the messenger's speed deficit is in the gate times (UD-194, UD-195) |
| No silent exclusion of preparations | pass, stated | the preparations are three specific packets and pointer angles in `U`; everything else is outside the theorem and the scope says so |
| No loss of positivity and interaction | pass, with F2 | strengths positive; `U` open of positive measure, so it contains fibres where the profiles do not vanish and the pointers act back; no lower bound on its measure |
| No confusion between reconstruction and derivation | pass, with F3 | see F3 |

## 4. Against the test of UO-16

* *"Radar coordinates computed only from emission, reception and clock records written by
  the flow."* `restEvent` and `movingEvent` are functions of five tick counts; each count is
  read off the one orbit in a window of flow time. **Qualification:** the windows are given
  in the flow time, and no register of the arena holds a count (as recorded under UO-14).
* *"Two observers assign the same Minkowski interval within stated errors."* Stated:
  `|I_moving − I_rest| ≤ E₁ (2|b₁| + E₁) + E₂ (2|b₂| + E₂)`.
* *"The residual tends to zero along a scaling family that is instantiated on the arenas."*
  For the coordinates: `151 K/k` is `151/(π k)` of the distance `π K`
  (`radar_error_relative`, `tendsto_radar_error_relative`). For the interval: `4600/(π² k)`
  of the squared distance (~~#433~~).
* *The test.* No hypothesis fixes the messenger at speed `1` or the clock at `√(1 − v²)`:
  both are properties of the carriers' packets, proved with errors.

## 5. Findings

* **F1. CLOSED 2026-11-17 (~~#433~~, UD-203).** As first written: the interval's residual
  was bounded in terms of the boosted coordinates and no bound on the counts was exported.
  Now the chain exports the size of the rest observer's coordinate (`6K` for the family) and
  the residual is at most `4600 K²/k`, `4600/(π² k)` of the squared distance
  (`radar_interval_error_le`, `tendsto_radar_interval_error_relative`). The residue, a lower
  bound on the interval itself, is `radar_rest_time_ge` (~~#434~~, UD-204): at least `9 K²`.
* **F2. The open set is not explicit.** Its radius exists for each `k`; the one the proof
  finds shrinks as `k` grows. The plan's Task 9 does not ask for a uniform bound.
* **F3. Reconstruction, not derivation.** The carriers are lattice Dirac particles: their
  band velocities are bounded by `1` and a moving clock's gap is the rest gap times
  `√(1 − v²)` up to `κ`. The theorem shows that records written by the flow reproduce that
  kinematics operationally. It does not derive the kinematics from `Σ`; that is Posit 11 of
  `specs/POSITS.md`, and it is what the contract means by "an operational reconstruction".
* **F4. The strengths exist; they are not given by a formula** (UD-179, UD-187).
* **F5. One family**: one velocity, one distance (the whole chain), `1 + 1` dimensions, the
  emission at a coincidence with the moving clock's mirror image (UD-194).
* **F6. Born statistics.** No probability enters. The obstruction of UD-45 to UD-53 stands.

## 6. Verdict

The build, the tests and the guards pass, and the nine checks pass with the qualifications
above. With F1 closed (~~#433~~, ~~#434~~) each clause of UO-16's statement has a theorem on
the arena of UA-18. **The author marked UO-16 complete on 2026-11-17**, with F2 to F6 and
the windows in flow time standing as the scope of the mark, not as bars to it.

## References

`specs/unified-record-spacetime-plan.md` (UO-16; UD-164, UD-188, UD-190 to UD-202);
`specs/unified-m6-feasibility.md` (Task 1); `specs/POSITS.md` (Posit 11);
`specs/connectivity-manifest.md` (L10); `specs/BACKLOG.md` ~~#402~~, ~~#423~~, ~~#426~~,
~~#430~~, ~~#431~~, ~~#432~~; `specs/future-work.md` (records to spacetime).
