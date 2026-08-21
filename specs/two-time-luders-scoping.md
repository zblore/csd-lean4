# Two-time Lüders on one arena — scoping note (Q25)

> **EXECUTED 2026-08-21, same day as scoped.** B1–B4 landed:
> `RecordLayer/TwoTimeLuders.lean` (new module) + `swap_sector_born_ctx` family
> in `SwapClosure.lean` (extended in place); 5 pins in the SigmaLayer part.
> Delivered exactly as scoped: `TwoStageArena` / `regroup` / `stageOne` /
> `stageTwo` / `twoStage` with STRUCTURAL persistence (`stageTwo_register₁`,
> `stageTwo_bank₁` — both `rfl`), the reusable `cond_map`, ★★ `two_stage_joint`
> (generic), ★ `swap_sector_born_ctx` (arbitrary context), and the CSD
> capstones ★★ `two_time_born`, ★ `two_time_repeat`, ★ `two_time_other_fate`,
> plus `two_stage_first_record` (no retro-action on the first record's law) and
> `two_stage_readouts` (both records on display at `t₂`). The B2 gate never
> fired — the map-factoring route went through directly; the only snags were
> rw-pattern set-form mismatches (fixed by TYPE-ASCRIBED measurability `have`s
> so `Measure.map_apply`/`cond_map` instantiate with the `setOf` form) and
> missing probability instances on `postMeasure` (provided via
> `cond_isProbabilityMeasure` + `Measure.isProbabilityMeasure_map` `have`s).
> **Gated residue stands as recorded below** (clock-glued two-epoch protocol;
> entangled/composite two-time = Q27's mixed tier).

Created 2026-08-21, the Q11 mold: feasibility checked before scoping, gates and
abort criteria fixed in advance. Companion to `RecordLayer/SwapLuders.lean` /
`RecordLayer/SwapClosure.lean` (the one-measurement engine this composes),
`Empirical/CSD/SequentialMeasurement.lean` (the conditional sequential tier),
`specs/BACKLOG.md` (Q25, queued 2026-08-20 from the external review), and
`specs/record-layer-plan.md` §4.

## The gap

The corpus has the ONE-measurement dynamical story complete on the swap arena:
the dynamical Born (`swap_sector_born`), the Lüders update as a pushforward
(`swap_luders_marginal` / `swap_luders_born`), repeatability and sequential
Born as CONDITIONAL statements (`csd_repeatability`, `csd_sequential_born` —
probabilities of the second outcome GIVEN the first, read off the
post-measurement ensemble). What the external review asked for and the corpus
does not have: the **composed two-time statement on ONE arena** — records at
`t₁` then `t₂` on a single composite space, the JOINT probability of the
record pair, with the first record persisting through the second measurement.
That is "what happens to `Ω_j` when outcome `i` is realised": the conditioned
re-partition the next context sees, stated where both records live.

## The route (and the feasibility discovery)

Extend the swap arena with a **second apparatus** — a fresh register and a
fresh bank ("one measurement consumes one bank" is the standing scope note, so
a second measurement carries its own):

    TwoStageArena Xsel K := SwapArena Xsel K × (T²_R × (Fin K → Xsel))

Stage 1 = `swapEvolve idx₁ 0 1` lifted (second apparatus spectator). Stage 2 =
`swapEvolve idx₂ 0 1` conjugated by the coordinate `regroup` that brings
(system, register₂, bank₂) together while the stage-1 record coordinates
(register₁, bank₁) ride in the spectator slot. **Record persistence through
stage 2 is then structural** — the stage-2 evolution provably never touches
register₁ (definitional, the same reason `swapG_register` was free).

**The feasibility discovery that keeps this M, not L:** the stage-2 record
event never reads the stage-1 record coordinates, so the composition needs
only the **system marginal** of the conditioned post-measurement state — which
is exactly `swap_luders_marginal`, already proven. No joint factorisation of
the conditioned law, no `Measure.pi` decomposition, no Fubini. The chain is:
condition on the stage-1 pointer cylinder (`cond_prod_cylinder`, exists),
commute `cond` with `map` (one small new helper via `Measure.restrict_map`),
recognise the marginal (`swap_luders_marginal`), reassemble the second-stage
input as `swapPrep (vertexPoint i)` (`prodAssoc`), and read the stage-2 sector
with the dynamical Born.

## Bricks, in order

* **B1 (S)** — `RecordLayer/TwoTimeLuders.lean`: the arena, the two lifted
  stage evolutions, `regroup`, measurability, and the structural persistence
  lemmas (stage 2 fixes register₁ and bank₁).
* **B2 (M)** — the measure engine: `cond_map` (conditioning commutes with a
  measurable pushforward — reusable, no CSD content) + the generic two-stage
  joint theorem: initial `(μ12 ⊗ Π ν₁) ⊗ app₂`, the joint record event
  factors as (stage-1 sector measure) × (stage-2 sector measure at the
  relocated state). GATE: if the measure-level rewriting hits the
  module-system defeq wall, go SETWISE (`Measure.ext` + `_apply` — the Q28
  snag-ledger fallback); abort to a Fubini-style `prod_apply` computation if
  the map-factoring itself fights.
* **B3 (S)** — `swap_sector_born_ctx` in `SwapClosure.lean` (extend in place,
  §8.3b): the dynamical sector Born for an ARBITRARY context field
  (`swapPrep p (sector_{basinIndex c} i) = c.rate p i` — the same three-step
  assembly as `swap_sector_born`, with `globalBasin_prob c` general; the
  existing momentContext version becomes a special case but is NOT removed).
* **B4 (S) ★★** — the CSD capstones: ★★ `two_time_born` (the joint law:
  `P(record i at t₁ ∧ record j at t₂) = momentMap p i · c₂.rate [eᵢ] j` for
  any second context `c₂`), ★ `two_time_repeat` (`c₂ = momentContext` ⇒ joint
  `= momentMap p i · δᵢⱼ` — von Neumann repeatability in fully composed
  two-time form), ★ `two_time_other_fate` (the row's literal question:
  conditioned on record `i` at `t₁`, the stage-2 partition carries the
  collapsed weights — the other `Ω_j` of the SAME context become null, a
  fresh context `c₂` sees `c₂.rate [eᵢ]`).

## Gated residue (recorded, not attempted)

* The **clock-glued two-epoch `MeasurementProtocol` instance** on `[0,2]` — a
  genuine two-time propagator family through both readout crossings. The
  composition law is a `swapEvolve_comp`-style case analysis SQUARED
  (two crossing times); the composed-map form below carries all the physics,
  the clock gluing is presentation. Fresh-session go decision.
* The **entangled/composite two-time version** (measure a subsystem of an
  entangled composite, then follow up — Q27's mixed-tier territory): needs the
  swap witness rebuilt over the composite arena with `reducedDM` weights. Not
  scoped here; Q27's residue row records it.

## Non-goals (standing scope, unchanged)

Degenerate first measurements (`DegenerateLuders.lean`'s recorded open
construction); bank reset/erasure (Landauer-priced, outside the protocol);
Hamiltonian generation of the propagators (§2a scope note).

## Wall-check record

`Measure.map_prod_map` ✓ (`MeasureTheory/Measure/Prod.lean:833`, note the
direction: `(map f μ).prod (map g ν) = map (Prod.map f g) (μ.prod ν)`);
`Measure.restrict_map` ✓ (`Measure/Restrict.lean:322`); `Measure.map_smul` ✓
(`Measure/Map.lean:128`, protected); `measurePreserving_prodAssoc` ✓ (used in
`SwapWitness.lean`); `cond_prod_cylinder` ✓ (`SwapLuders.lean`, reusable
as-is); `swap_luders_marginal` ✓ (the marginal engine, hpos on the SHEAR
sector); `measure_basinIndex_fibre` + `globalBasin_prob` ✓ both general in
`c : ContextField N`; `momentMap_vertex` ✓ (`DegenerateLuders.lean:114`,
`= if k = j then 1 else 0`); `swapPrep` unfolds to
`((epistemicMeasure p ⊗ readyMeasure) ⊗ calibratedBank)` ✓ so the
reassociated second-stage input is definitionally `swapPrep (vertexPoint i)`.
Known traps carried in: beta-unreduced congr-ae goals (`dsimp only`), the
`show`-idiom for `cond` (the `cond_prod_cylinder` precedent), setwise fallback
for measure-level rewrites. Home: new module `RecordLayer/TwoTimeLuders.lean`
+ `SwapClosure.lean` extended in place; pins in the SigmaLayer part.
