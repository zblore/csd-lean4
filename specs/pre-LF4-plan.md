# Pre-LF4 execution plan

Active execution plan for the work that lands between v0.3.4-lf3 and the start
of LF4 proper (mixed states, POVMs, subsystem reduction). Companion to
[`LF4-todo.md`](LF4-todo.md), which records *deferred* items with rationale;
this file is the *execution order* with phases, spikes, and exit criteria.

The architectural commitment of this plan is **option (b)-volume-forward**
("(b3)") from the 2026-05-18 design discussion: an OP-from-preparation
construction that carries the symmetry axiom **structurally** via its
type signature (`MeasureBridgeData` argument), with the chain capstone
for the pure-state singlet case proved by **direct volume integration
against the Dirac pushforward**, not via Busch / density-operator
reformulation. Reasons:

1. **CSD's volume-forward foundational claim.** CSD is geometric quantum
   mechanics: probability is volume ratio on Σ, pushed to P, integrated
   against effect functions. Branch counting is not a thing; the trace
   formula is a *reformulation*, not the foundation. The chain capstone
   should reflect this. Routing the singlet chain through Busch (which
   characterises probability assignments as trace-form expressions)
   would be gratuitous reformulation when direct Dirac integration on
   the pushforward measure evaluates to `|⟨ψ,φ⟩|²` on its own.
2. **LF4 readiness without retrofit.** Mixed states, POVM completeness,
   and the maximally-mixed / Fubini-Study identification *do* require
   the symmetry axiom structurally. Carrying `MeasureBridgeData` on
   `OperationalPackage.fromPreparation` means LF4 inherits the right
   base. The trace-form reformulation (Busch + `born_quadratic`) is
   available as a corollary for callers who want density-operator
   language, but is **not on the chain critical path**.
3. **No repeated rework.** The reviewer's option (a) carried the Dirac
   concentration as a free hypothesis and shipped a Busch-only chain
   capstone, leaving LF4 to redo the OP construction. (b3) provides the
   right base now.

For the trade-off in detail (volume-forward Route 1 vs Busch-mediated
Route 2; what symmetry buys you in the pure-state case vs the mixed /
POVM case), see the 2026-05-18 discussion summary at the bottom of this
document.

## Goal

The four LF3 chain capstones consume an `LF2.PurePreparation` directly
and are proved by volume-forward integration:

```
OP.fromPreparation.p (rankOneEffect φ hφ)
  = ∫ p, effectProjFn rep (rankOneEffect φ hφ) p ∂(Measure.map D.π μprep)
  = ∫ p, ‖⟨rep p, φ⟩‖² ∂(Measure.dirac PP.ray_point)   [PP.push_dirac]
  = ‖⟨rep PP.ray_point, φ⟩‖²                            [integral_dirac']
  = ‖⟨PP.ψ, φ⟩‖²                                        [PP.rep_at_ray]
```

`#print axioms` on `hLF2_of_singlet_purePreparation` cites
`invariant_measure_uniqueness` (structurally, via the
`MeasureBridgeData` argument's type) but **not** `busch_effect_gleason`
(because Busch is not extensionally invoked in the volume-forward
proof). The trace-form reformulation is shipped as a separate theorem
(`PurePreparation.born_rank_one_via_trace_form`) for callers who want
the density-operator language; it cites both axioms but is not on the
chain critical path.

Phase 7 retires `PureSingletPreparation.ofHypothesis` and rewrites the
four LF3 chain capstones to consume `LF2.PurePreparation` directly.

After Phase 7 the four LF3 capstones go from
`propext, Classical.choice, Quot.sound` to
`propext, Classical.choice, Quot.sound, invariant_measure_uniqueness`.
This is a deliberate, honest regression: the chain previously parked
its volume-bridge dependence in a free hypothesis (`hLF2`); now the
hypothesis is discharged structurally and the symmetry axiom comes
with. Operations (Busch) does **not** propagate into the chain; it
remains in `pure_state_born_weights_of_certainty` / the trace-form
reformulation theorem, used where mixed-state / POVM work actually
needs it.

## Module structure

Add new modules under `CsdLean4/LF2/`:

- `CsdLean4/LF2/PhaseInvariance.lean` — phase invariance of `outerProduct`
  and the rank-1 effect/density wrappers. No `Projectivization` commitment
  (per Spike 1).
- `CsdLean4/LF2/EffectFn.lean` — the volume-forward projective effect
  function `effectProjFn (rep : P → EuclideanSpace ℂ (Fin N)) : Effect → P → ℝ`,
  measurability, pointwise algebra. The CSD-foundational object: probability
  is `∫ effectProjFn rep E p ∂(π_*μprep)`.
- `CsdLean4/LF2/Preparation.lean` — `MeasureBridgeData`,
  `OperationalPackage.fromPreparation`, `PurePreparation`,
  `PurePreparation.born_rank_one` (proved by direct Dirac integration —
  Route 1), and the optional trace-form reformulation
  `PurePreparation.born_rank_one_via_trace_form`.

LF3-side additions go under existing `CsdLean4/LF3/`:

- `CsdLean4/LF3/SingletProjective.lean` — `SingletProjectiveOutcome`,
  measurability, partition structure, `projectiveWeight_singlet_eq_P_st`,
  and `hLF2_of_singlet_purePreparation`.

The four LF3 chain capstones in `CsdLean4/LF3/Interface.lean` are rewritten
in place (not appended): they consume `LF2.PurePreparation` directly. The
transitional `PureSingletPreparation.ofHypothesis` constructor in
`CsdLean4/LF3/PurePreparation.lean` is retired.

## Phases

### Phase 1 — Algebraic foundations (phase invariance)

No measure theory, no symmetry, no `Projectivization` commitment
(per Spike 1, deferred to LF4-todo §12 as a Cat-1 Mathlib contribution).
Mechanical. ~30 min.

- `outerProduct_phase_invariant : ‖c‖ = 1 → outerProduct (c • φ) = outerProduct φ`.
- `rankOneEffect_phase_invariant`, `rankOneDensity_phase_invariant`.

**Exit criterion.** Phase-invariance lemmas land. `lake build` clean.

**Maps to reviewer's plan.** §3 first half (phase invariance). The §2
(`ProjectiveHilbert` abbrev) and §3 second half (`rankOneEffectProj`,
`rankOneDensityProj`) are **deferred** to LF4-todo §12 (waits on
Mathlib's `Projectivization` measure-space API).

### Phase 2 — Volume-forward effect function

The CSD-foundational object: `effectProjFn` is the function whose
integral against `π_*μprep` *is* the probability assignment. Not "a
function extracted from the operational package" — the operational
package's `p` field is *defined* as this integral. ~1-2 h.

- `noncomputable def effectProjFn (rep : P → EuclideanSpace ℂ (Fin N)) (E : Effect N) (p : P) : ℝ`
  := `RCLike.re (inner ℂ (rep p) (E.M *ᵥ rep p))`. Caller-supplied
  `rep` is a unit-vector representative; `P` stays abstract per the
  Spike 1 revision.
- `effectProjFn_nonneg`, `effectProjFn_le_one` from `E.nonneg` /
  `E.le_one` (PSD content).
- `effectProjFn_rankOne : effectProjFn rep (rankOneEffect φ hφ) p = ‖inner ℂ (rep p) φ‖²`.
  Algebraic identity from rank-1 outer-product expansion.
- `effectProjFn_add`, `effectProjFn_one`, `effectProjFn_zero` —
  pointwise linearity / boundary cases.
- `effectProjFn_measurable : Measurable rep → Measurable (effectProjFn rep E)`.
  Routes through continuity of the bilinear form `(v, w) ↦ ⟨v, E.M *ᵥ w⟩`
  on finite-dim `EuclideanSpace`.

**Architectural note.** `effectProjFn` should be documented as the
*volume-forward effect function* — the CSD foundational quantity that
turns a projective volume measure into a probability assignment via
integration. The trace-form / density-operator description (Busch /
`born_quadratic`) is a reformulation, not the foundation.

**Exit criterion.** Pointwise + measurability lemmas land. `lake build`
clean.

### Phase 3 — `OperationalPackage.fromPreparation`

The structural construction that ties an OP to a `μprep` via
`measure_bridge`. The symmetry axiom enters the type signature here. ~5-7 h.

- `structure MeasureBridgeData (D : SectorData ...) (μFS : Measure P)`
  bundling `IsProbabilityMeasure μFS`, `G`-invariance, the bridge constant
  `c : ENNReal`, and `Measure.map D.π D.μL = c • μFS`.
- `MeasureBridgeData.ofSectorData` — primary constructor fed by
  `measure_bridge`. Cites `invariant_measure_uniqueness`.
- `noncomputable def OperationalPackage.fromPreparation
    (D : SectorData SigmaSpace P G) (μFS : Measure P)
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (rep : P → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    : OperationalPackage N`
  with `OP.p E := (∫ p, effectProjFn rep E p ∂(Measure.map D.π μprep))`.
- Operational-axiom proofs for `fromPreparation`:
  - `nonneg` — pointwise non-negativity + integral monotonicity.
  - `le_one` — pointwise `≤ 1` + total measure `= 1`.
  - `total_one` — `effectProjFn rep Effect.one ≡ 1`, integral is `μprep(Σ) = 1`.
  - `additivity` — integral linearity + `effectProjFn_add`.

**Architectural point — structural-vs-extensional axiom citation.** For
the pure-state Dirac case, the operational-axiom proofs do not
extensionally need the bridge data — `δ_{[ψ]}` does not depend on `μFS`.
But the **type signature** of `fromPreparation` forces every caller to
supply a `MeasureBridgeData`, and the only construction route to a
`MeasureBridgeData` for a `SectorData`-derived setup is
`MeasureBridgeData.ofSectorData`, which calls `measure_bridge`. Hence
`invariant_measure_uniqueness` propagates by construction even when not
extensionally invoked. This is the volume-forward architectural choice:
the symmetry axiom is the *background structure fix* that makes the
volume integral well-defined, even when a specific case (Dirac) does
not need the structural identification.

**Exit criterion.** `OperationalPackage.fromPreparation` typechecks,
operational-axiom fields prove, and a `#print axioms` test confirms
`invariant_measure_uniqueness` in its citation set. **Busch is not
invoked here** — `fromPreparation` is *the* volume-forward
construction, not a wrapper around the Busch extraction.

### Phase 4 — `PurePreparation` and direct volume-forward Born theorem

~2-3 h.

- `structure PurePreparation (D : SectorData SigmaSpace P G) (μprep : Measure SigmaSpace)` with fields:
  - `ψ : EuclideanSpace ℂ (Fin N)`,
  - `unit_ψ : ‖ψ‖ = 1`,
  - `ray_point : P` (the abstract projective-side point — no
    `Projectivization` needed, per Spike 1),
  - `push_dirac : Measure.map D.π μprep = Measure.dirac ray_point`,
  - parametrised by the same `rep : P → EuclideanSpace ℂ (Fin N)` used
    at OP-construction time, with `rep_at_ray : rep ray_point = ψ`.

- **Volume-forward Born theorem (Route 1 — chain critical path):**
  ```
  theorem PurePreparation.born_rank_one
      (PP : PurePreparation D μprep) (φ : EuclideanSpace ℂ (Fin N))
      (hφ : ‖φ‖ = 1) :
    (OperationalPackage.fromPreparation D μFS bridge μprep rep
       hrep_unit hrep_meas).p (rankOneEffect φ hφ)
      = ‖inner ℂ PP.ψ φ‖² := by
    simp only [OperationalPackage.fromPreparation]
    rw [PP.push_dirac, MeasureTheory.integral_dirac' _ _ (by exact effectProjFn_stronglyMeasurable rep _ hrep_meas)]
    rw [effectProjFn_rankOne, PP.rep_at_ray]
  ```
  Proof is direct Dirac integration: unfold OP definition, substitute
  `push_dirac`, apply `integral_dirac'`, evaluate `effectProjFn` on the
  rank-1 effect, substitute `rep_at_ray`. **Busch is not invoked.**
  `#print axioms` shows
  `propext, Classical.choice, Quot.sound, invariant_measure_uniqueness`
  — symmetry propagates structurally via the `bridge` argument; Busch
  does not appear.

- **Trace-form reformulation (Route 2 — corollary, not on chain
  critical path):**
  ```
  theorem PurePreparation.born_rank_one_via_trace_form
      (PP : PurePreparation D μprep) (φ : EuclideanSpace ℂ (Fin N))
      (hφ : ‖φ‖ = 1) :
    (OperationalPackage.fromPreparation D μFS bridge μprep rep ...)
      = traceForm (rankOneDensity PP.ψ PP.unit_ψ) (rankOneEffect φ hφ) := ...
  ```
  Composes Busch (via `busch_effect_gleason` + the rank-1 uniqueness
  theorem from BornWrapper) to identify the OP-extracted density
  operator as `|ψ⟩⟨ψ|`. Provides density-operator language for callers
  who want it. `#print axioms` cites both LF2 axioms. Not on the chain
  critical path; available for downstream POVM / mixed-state work.

**Exit criterion.** `#print axioms PurePreparation.born_rank_one`
lists `invariant_measure_uniqueness` only (volume-forward path).
`#print axioms PurePreparation.born_rank_one_via_trace_form` lists
both axioms (reformulation path). Two `#guard_msgs` regressions added
to `Tests/AxiomAudit.lean`.

**Maps to reviewer's plan.** §4 (pure preparation structure), realised
in the option-(b3) volume-forward form. Reviewer's option-(a)
short-circuit and option-(b2) Busch-mediated chain are both rejected;
volume-forward Dirac evaluation is the foundational route.

### Phase 5 — `SectorData.outcomeOfProjective`

LF4-todo §7 (projective-first outcome specification). The current
`LF1_main_theorem_projective` requires callers to supply both an ontic
outcome and the correspondence proof; this constructor removes the
caller burden. ~2-3 h.

- `def SectorData.outcomeOfProjective (D : SectorData ...)
    (Oep : Set (ProjectiveHilbert N)) (hOep : MeasurableSet Oep) :
    D.toOntic.OutcomeRegion` with `Ω := D.π ⁻¹' Oep` (or
  `Φ ⁻¹' (π ⁻¹' Oep)` depending on what the `OutcomeRegion` requires).
- `outcomeOfProjective_preEvent`, `outcomeOfProjective_measurable`,
  `outcomeOfProjective_weight_eq_projectiveWeight`.

**Maps to reviewer's plan.** §5 (projective outcome constructor).

### Phase 6 — Singlet projective outcomes

LF3-side preparation for the chain closure. ~3-4 h.

- `SingletProjectiveOutcome (ctx : MeasurementContext) (s t : Sign) : Set P` —
  the projective region for the `(s, t)` joint eigenstate. `P` stays
  abstract (per Spike 1 revision). The region is the preimage under the
  caller-supplied `rep` map of a neighbourhood / singleton of the
  Hilbert-space joint eigenstate (precise definition pinned at
  implementation time).
- `SingletProjectiveOutcome.measurable`,
  `SingletProjectiveOutcome.disjoint_distinct` for the `Sign × Sign`
  partition structure.
- `projectiveWeight_singlet_eq_P_st` — for a `PurePreparation` whose
  `ψ` is the singlet, the OP-derived integral over the `(s, t)`
  projective region equals `P_st(a, b, s, t)`. Proof:
  `PurePreparation.born_rank_one` applied to `ψ = singlet` and
  `φ = jointEig (s, t) ctx.a ctx.b`, then composed with the
  singlet-correlation algebra in `LF3/Singlet/Kernel.lean` to identify
  `‖inner ℂ singlet (jointEig (s,t) ctx.a ctx.b)‖² = P_st(...)`.

**Maps to reviewer's plan.** §6 (LF3 hLF2 discharge objects).

### Phase 7 — Chain closure and `PureSingletPreparation` retirement

The payoff. ~2-3 h.

- `hLF2_of_singlet_purePreparation : ∀ ctx s t,
    projectiveWeight D μprep (SingletProjectiveOutcome ctx s t)
      = ENNReal.ofReal (P_st ctx.a ctx.b s t)`.
  Volume-forward proof routing through `PurePreparation.born_rank_one`
  (Route 1). Cites `invariant_measure_uniqueness` only.
- **Refactor `LF3/PurePreparation.lean`.** Retire
  `PureSingletPreparation.ofHypothesis`. Replace with
  `PureSingletPreparation.ofPurePreparation` constructing the bundle from
  an `LF2.PurePreparation` via `hLF2_of_singlet_purePreparation`. Per the
  2026-05-17 Q4 decision logged in `AXIOMS.md §3.6`: this is a rewrite of
  the capstone bodies, not a wrap.
- **Refactor the four LF3 chain capstones** in `LF3/Interface.lean`
  (`LF3_singlet_frequency_convergence`,
   `LF3_singlet_frequency_convergence_born`,
   `LF3_singlet_frequency_convergence_born_inner`,
   `LF3_main_theorem` / `LF3_finite_leakage_theorem` as relevant) to
  consume an `LF2.PurePreparation` directly rather than a
  `PureSingletPreparation`.
- **AxiomAudit update.** The four LF3 capstones go from
  `propext, Classical.choice, Quot.sound` to
  `propext, Classical.choice, Quot.sound, invariant_measure_uniqueness`.
  Update `Tests/AxiomAudit.lean` `#guard_msgs` lines in lockstep. This
  is a deliberate, documented regression: the chain previously parked
  its volume-bridge dependence in a free hypothesis (`hLF2`); now the
  hypothesis is discharged structurally and the symmetry axiom comes
  with. **Operations (Busch) does not propagate to the chain** — it
  remains in `pure_state_born_weights_of_certainty` /
  `PurePreparation.born_rank_one_via_trace_form`, available where
  mixed-state / POVM work actually needs the density-operator
  language.

### Phase 8 — Joint partition convergence (LF4-todo §9)

Originally triaged as "premature" because no LF3 export consumes it. The
user has not requested it. Including here as deferred-with-rationale to
keep the option clear; revisit at LF4 proper if POVM completeness needs
the joint statement at scale. **Not part of the option-(b) critical path.**

### Phase 9 — `MeasurementUnitary` tensor constructor (LF4-todo §10.x / D4-G6 continuation)

`TensorModel.lean` already has `ProjectorAlgebra.ofTensorEmbedding`. The
remaining D4/G6 debt is the `MeasurementUnitary` side. Independent of the
option-(b) chain; can run as a parallel small thread. ~3-5 h.

- `TensorEmbedding.liftUnitaryA`, `TensorEmbedding.liftUnitaryB`.
- `MeasurementUnitary.ofTensorEmbedding`.
- `MeasurementUnitary.factorises_ofTensorEmbedding`.

Do **not** prove the eigenstate-action field. That requires operator
exponentials / Stone-on-bounded-self-adjoint-operators infrastructure and
is LF4-or-later (spec §9.5).

### Phase 10 — Unitary covariance of `OperationalPackage` (LF4-todo §1)

Originally triaged "defer to LF4." Including here as deferred-with-rationale.
The covariant-vs-invariance reading question hasn't been resolved
structurally, and no current chain capstone consumes it. **Not part of
option-(b) critical path.** Revisit at LF4 proper when unitary evolution
enters non-trivially.

### Phase 11 — LF3 terminology audit (branch → volume rename)

Optional pre-LF4 churn, ~3-4 h. The goal is to align LF3's naming with
CSD's geometric-quantum-mechanics framing: volume ratios are the
foundational quantity, "branches" are not. LF3 currently carries
`branchState`, `branchWeight`, `BranchSeparation`,
`wrongPointerReadoutMass`, etc. Mechanically the content is
volume-based — `branchWeight s t` is the norm-squared of the
post-measurement state on the `(s, t)` eigenspace, a volume in
projective amplitude space, not a count. But the **terminology**
invites Everettian / many-worlds reading and obscures the volume claim.

**Rename targets (proposal):**

- `branchState` → `eigenSectorState` or `sectorState`.
- `branchWeight` → `sectorVolume` or `eigenSectorVolume`.
- `BranchSeparation.lean` → `SectorSeparation.lean`.
- `branch_separation_leakage_bound` → `sector_separation_leakage_bound`.
- `wrongPointerReadoutMass` → `crossSectorReadoutMass`.

**Scope and risk.** Rename is mechanical (`Find All`/`Replace All` with
Lean awareness). Risk is breakage of consumers in `LF3/Projectors/`,
`LF3/Singlet/`, `LF3/Interface.lean`. A clean rename pass + `lake build`
+ AxiomAudit verification is the workflow.

**Decision needed pre-LF4.** Do this in pre-LF4 (reader gets the
volume-forward terminology aligned with the foundational claim) or
defer to LF4 (one churn pass at LF4 start time alongside other
refactors). My read: **do it pre-LF4** — the cost is bounded
(~3-4 h) and it's much harder to do consistently once LF4 adds POVM /
mixed-state machinery on top. If deferred, log as LF4-todo §13.

**Maps to reviewer's plan.** Not on the reviewer's list — surfaced by
the 2026-05-18 volume-forward discussion.

### Documentation sync

After Phase 7 lands:

- **`AXIOMS.md`** — add §2.x entry for the LF3 capstones now citing
  `invariant_measure_uniqueness` (volume-bridge dependency, structural
  via the `MeasureBridgeData` argument of `OperationalPackage.fromPreparation`).
  Note explicitly that `busch_effect_gleason` does **not** propagate to
  the chain capstones — operations is reserved for the trace-form
  reformulation theorem and downstream mixed-state / POVM work. Remove
  §3.6 (`PureSingletPreparation` bundle as physical assumption) since
  the bundle is now constructed structurally. Update §5 table.
- **`README.md`** — update LF3 axiom-posture text. Currently says "LF3
  imports zero axioms beyond Lean's foundational set." Honest after
  Phase 7: LF3 capstones cite `invariant_measure_uniqueness` via the
  `hLF2` discharge. Add the architectural reasoning (CSD's volume-forward
  foundational claim + LF4 readiness for mixed states / POVMs) to the
  LF3 axiom-posture paragraph. Frame the chain explicitly as volume
  ratios on `Σ` → pushforward on `P` → integration against the
  volume-forward effect function. The trace-form / density-operator
  description is a reformulation, available via
  `PurePreparation.born_rank_one_via_trace_form`.
- **`CLAUDE.md`** — same updates. Add a one-line note in the LF3
  description that "branches" terminology is volume-based (per Phase 11
  rename if done, or as a clarification if Phase 11 is deferred).
- **`specs/LF4-todo.md`** — retire §2 (preparation-to-Hilbert
  correspondence, done), §3 (projective rank-1 constructors, partially
  done — projective constructors deferred to §12 until Mathlib's
  Projectivization API lands), §5 (rank-1 effects from projective
  points, deferred to §12), §7 (projective-first outcomes, done).
  Promote §1 (unitary covariance) and §8 (concrete `(SigmaSpace, P, G)`
  instantiation) to top priority for LF4 proper.
- **This file** — mark phases as `DONE` in place rather than deleting,
  so the execution history is preserved.

## Spikes

Two open technical questions investigated 2026-05-18 against Mathlib at
v4.29.0-rc8.

### Spike 1 — Borel-measurability on `Projectivization`

**Question.** Does Mathlib provide a `MeasurableSpace` instance on
`Projectivization ℂ (EuclideanSpace ℂ (Fin N))` with the lift-measurability
glue we need?

**Result: outcome (iii) — blocker.** Mathlib `Projectivization` is a
bare `Quotient (projectivizationSetoid K V)` in
`Mathlib/LinearAlgebra/Projectivization/Basic.lean`. No `TopologicalSpace`,
`MeasurableSpace`, or `BorelSpace` instance anywhere in Mathlib. The only
adjacent file is `Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean`,
which gives the projective line a topology via one-point compactification
— specific to the line case, not the general quotient. A full
contribution covering quotient topology, Borel structure,
`MeasurableSingletonClass`, and `Projectivization.lift` measurability
for arbitrary `K`, `V` is several days of focused Mathlib work.

**Architectural consequence.** Do **not** commit to
`ProjectiveHilbert N := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` at
the LF2 level. Keep `P` abstract in `SectorData` (which is the original
LF2 design anyway — `P : Type*` with `[MeasurableSpace P]`). The
projective-effect-function construction takes a caller-supplied
`representative : P → EuclideanSpace ℂ (Fin N)` map plus measurability +
unit-norm hypotheses. LF4 instantiations supply their own `rep` for
whatever concrete `P` they pick.

This revision is actually cleaner than the reviewer's original
`ProjectiveHilbert` commitment, which would have forced the abstraction
to specialise at LF2 time. The abstract design lets LF4 pick the
concrete realisation (Kähler manifold quotient, projective sphere quotient,
or — once Mathlib lands the missing API — `Projectivization` proper).

### Spike 2 — Bochner integration against `Measure.map` and Dirac

**Question.** With a `MeasurableSpace` on `P` and `Measure.map D.π μprep`
on `P`, does Bochner integration `∫ effectProjFn E ∂(Measure.map D.π μprep)`
work? Does the Dirac specialisation `∫ f ∂(Measure.dirac a) = f a` work?

**Result: outcome (i) — healthy.** Mathlib provides:

- `MeasureTheory.integral_map : AEMeasurable φ μ → AEStronglyMeasurable f (Measure.map φ μ) → ∫ x, f x ∂(Measure.map φ μ) = ∫ x, f (φ x) ∂μ`
  in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.
- `MeasureTheory.integral_dirac : [MeasurableSingletonClass α] → ∫ x, f x ∂(Measure.dirac a) = f a`.
- `MeasureTheory.integral_dirac'`: the same without the
  `MeasurableSingletonClass` requirement, using `StronglyMeasurable f`.

Both will be needed: `integral_map` to evaluate the OP integral, and
`integral_dirac'` to specialise to the pure-preparation case.

`MeasurableSingletonClass` on the abstract `SectorData.P` would need to
be added as a hypothesis (or carried on `SectorData` as an instance
constraint) if we want the simpler `integral_dirac`. Alternatively use
`integral_dirac'` everywhere, paying the cost of supplying
`StronglyMeasurable` for the effect-projective-function.

**Action plan.** Use `integral_dirac'` with explicit `StronglyMeasurable`
hypotheses. Avoids forcing a `MeasurableSingletonClass` constraint on
arbitrary `P` at the SectorData level.

## Revised architecture (post-spike)

The spike findings revise the module-level plan as follows.

### `effectProjFn` signature — caller-supplied representative

Replace:
```
effectProjFn (E : Effect N) ([ψ'] : ProjectiveHilbert N) : ℝ
```
with:
```
def effectProjFn (rep : P → EuclideanSpace ℂ (Fin N)) (E : Effect N) (p : P) : ℝ
  := RCLike.re (inner ℂ (rep p) (E.M *ᵥ rep p))
```
The phase-invariance content moves to a hypothesis-on-`rep` shape:
caller asserts `rep` lifts a phase-equivalence class consistently. The
definition itself doesn't see Projectivization at all.

### `MeasureBridgeData` signature — abstract `P`

```
structure MeasureBridgeData (D : SectorData SigmaSpace P G)
    (μFS : Measure P) where
  is_prob : IsProbabilityMeasure μFS
  is_inv : ∀ g : G, Measure.map (D.epAction g) μFS = μFS
  c : ENNReal
  bridge_eq : Measure.map D.π D.μL = c • μFS
```

`MeasureBridgeData.ofSectorData` cites `measure_bridge` and thereby
`invariant_measure_uniqueness`.

### `OperationalPackage.fromPreparation` signature — abstract `P` + `rep`

```
noncomputable def OperationalPackage.fromPreparation
    (D : SectorData SigmaSpace P G)
    (μFS : Measure P)
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (rep : P → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    : OperationalPackage N
```

Implementation:
```
{ p := fun E => ∫ p, effectProjFn rep E p ∂(Measure.map D.π μprep)
  nonneg := ...
  le_one := ...
  total_one := ...
  additivity := ... }
```

### `PurePreparation` signature

```
structure PurePreparation (D : SectorData ...) (μprep : Measure SigmaSpace) where
  ψ : EuclideanSpace ℂ (Fin N)
  unit_ψ : ‖ψ‖ = 1
  ray_point : P
  rep_at_ray : (rep : P → EuclideanSpace ℂ (Fin N)) → rep ray_point = ψ  -- or in a phase-equivalent form
  push_dirac : Measure.map D.π μprep = Measure.dirac ray_point
```

The `ray_point : P` is the abstract projective-side representative; the
Hilbert vector `ψ` is the concrete vector; the link is via the `rep` map
supplied at OP-construction time.

### Phase estimates after spike + volume-forward revision

| Phase | Was (pre-spike, b2) | Now (post-spike, b3) |
|---|---|---|
| 1 (algebraic / phase invariance) | ~2 h | ~30 min |
| 2 (volume-forward effect function) | ~2-3 h | ~1-2 h |
| 3 (`fromPreparation`) | ~5-7 h | ~5-7 h |
| 4 (`PurePreparation` + Born theorem) | ~2-3 h | ~2-3 h |
| 5 (`outcomeOfProjective`) | ~2-3 h | ~2-3 h |
| 6 (singlet projective outcomes) | ~3-4 h | ~3-4 h |
| 7 (chain closure + retirement) | ~2-3 h | ~2-3 h |
| **Total critical path** | **~17-22 h** | **~12-17 h** |

Phase 1 shrinks because the `Projectivization` commitment is deferred
(Spike 1). Phase 2 simplifies because `effectProjFn` is now caller-
parameterised by an abstract `rep : P → EuclideanSpace ℂ (Fin N)` map,
no `Projectivization` measurability question to resolve. Phases 3-7
estimates unchanged. The integration glue (Spike 2 outcome) is
healthy; `integral_map` and `integral_dirac'` are the load-bearing
Mathlib lemmas.

The volume-forward (b3) revision over the Busch-mediated (b2) version
does not change time estimates — Route 1 (direct Dirac integration)
and Route 2 (Busch composition) are comparable effort; the choice is
architectural, not time-cost.

## Order and time

**Spikes complete (2026-05-18):** Architecture revised. See "Revised
architecture (post-spike)" section above. `P` stays abstract;
`Projectivization` API contribution is parked as an LF4-todo item rather
than pre-LF4 critical path.

**Critical path:** Phase 1 (revised, ~30 min) → Phase 2 (revised, ~1-2 h)
→ Phase 3 (~5-7 h) → Phase 4 (~2-3 h) → Phase 5 (~2-3 h) → Phase 6
(~3-4 h) → Phase 7 (~2-3 h) → documentation sync (~1 h).

**Parallelisable side track:** Phase 9 (MeasurementUnitary tensor
constructor) is fully independent of the option-(b) chain. Could run
concurrent with Phases 2-6 if there is bandwidth.

**Deferred to LF4 proper:**
- Phase 8 (joint partition convergence — premature, no current consumer).
- Phase 10 (unitary covariance — reading question unresolved, no current
  consumer).
- The `Projectivization` topology / measure / lift API as a Cat-1
  Mathlib contribution (~ several days of focused Mathlib work). Track
  in `LF4-todo.md` with the spike note as rationale.

**Total revised critical-path estimate:** ~12-17 h focused Lean work +
~1 h documentation. (Down from ~17-22 h pre-spike.) The Spike 1 finding
saves the Mathlib-contribution time that would otherwise have been
pre-LF4 critical path.

**Recommended checkpoint tags:**
- `v0.4.0-pre-lf4` after Phase 4 lands (`PurePreparation.born_rank_one`
  proved volume-forward, citing `invariant_measure_uniqueness` only;
  `PurePreparation.born_rank_one_via_trace_form` as reformulation
  corollary citing both axioms; AxiomAudit `#guard_msgs` regressions
  for both).
- `v0.4.1-pre-lf4` after Phase 7 lands (LF3 capstones refactored,
  `PureSingletPreparation.ofHypothesis` retired, AxiomAudit updated to
  cite `invariant_measure_uniqueness` on the four LF3 capstones).
- The major bump to `v0.5.0-lf4-base` is reserved for the start of LF4
  proper (mixed states / POVMs / reduction), not for the option-(b3)
  base. Pre-LF4 is structural plumbing; LF4 proper is new mathematics.

## Triage of the reviewer's pre-LF4 plan (2026-05-18)

The external reviewer's pre-LF4 punch list was triaged against the
v0.3.4-lf3 tree state. Mapping to this plan:

| Reviewer item | Status | Maps to |
|---|---|---|
| §0 Update README "Two layers" → "Three layers" | **Stale** (already done) | — |
| §0 Update `ProjectorAlgebra` status text | **Stale** (already done) | — |
| §1 `OperationalPackage.conjugateBy` | **Deferred to LF4** | Phase 10 |
| §2 `ProjectiveHilbert` abbreviation | Included | Phase 1 |
| §3 Phase-invariance + projective rank-1 | Included | Phase 1 |
| §4 `PurePreparation` structure | Included **in option-(b) form** | Phases 3-4 |
| §5 `SectorData.outcomeOfProjective` | Included | Phase 5 |
| §6 LF3 `hLF2` discharge objects | Included | Phases 6-7 |
| §7 Joint partition convergence | **Deferred to LF4** | Phase 8 |
| §8 `MeasurementUnitary` tensor constructor | Included (parallel track) | Phase 9 |
| §9 Axiom audit objects | **Stale** (already done) | — |

The reviewer's "minimal version" is roughly the Phase 1 → Phase 7 critical
path of this document. The substantive divergence from the reviewer's
plan is in §4: the reviewer proposed a `PurePreparation` structure
carrying `push_dirac` as a hypothesis (option (a) in the design-space
discussion). This plan instead routes the OP construction through
`measure_bridge` (option (b3) volume-forward), so the chain capstones
cite `invariant_measure_uniqueness` structurally and are proved by
direct Dirac integration. Reason: CSD's volume-forward foundational
claim + LF4 readiness for mixed states / POVMs.

## 2026-05-18 design discussion summary

### First question

> Why isn't symmetry + operations a requirement for the Born rule as per
> Paper B?

The honest answer in three layers:

1. **`born_quadratic` is not the Born rule.** It is an algebraic identity:
   assuming the trace-form ansatz, `Tr(|ψ⟩⟨ψ| · |φ⟩⟨φ|) = |⟨ψ,φ⟩|²`.
   Three lines of Hilbert-space algebra, no physical content.

2. **Operations (Busch) buys you the trace-form ansatz.** Effect-additive
   probability assignment ⟹ unique density operator `ρ` such that
   `p(E) = Tr(ρE)`. The trace form is *derived*, not assumed.

3. **Symmetry (invariant measure uniqueness) buys you the
   measure-theoretic background.** `π_*μL ∝ μFS` identifies the
   projective background measure (Fubini-Study). For *mixed* states,
   POVM completeness, and the general projective-probability-as-integral
   story, the symmetry axiom is load-bearing. For *pure preparations*
   specifically, the Dirac concentration `π_*μprep = δ_{[ψ]}` is a
   definitional input that does not directly invoke the symmetry axiom
   extensionally.

### Second question

> Does the plan help deliver CSD as it was envisaged? Geometric quantum
> mechanics using volume as the key, not branches. Branch counting
> should not be a thing. It should be volume ratios.

This question revised the architectural choice from
option (b)-Busch-mediated to option (b3)-volume-forward.

The CSD foundational claim is volume-forward:
- Probability is volume ratio on `Σ` (LF1: `prepMeasure_apply`).
- Pushforward to `P` is volume on `P` (LF2: `measure_bridge`).
- Probability of an effect is `∫ effectProjFn rep E p ∂(π_*μprep)` —
  an integral of an effect function against the projective volume
  measure. The effect function `effectProjFn` is the CSD-foundational
  object that turns projective volume into probability.

For rank-1 effects this integral evaluates directly:
- Pure preparation: `π_*μprep = δ_{[ψ]}` (Dirac), so the integral is
  `effectProjFn rep (rankOneEffect φ hφ) ray_point = ‖⟨ψ, φ⟩‖²` by
  Dirac evaluation. No density operator, no Busch, no trace.

The trace-form description (`Tr(ρE)`) is a *reformulation* of this
volume integral, available via Busch + `born_quadratic` for callers
who want density-operator language. It is not the foundation.

The earlier plan (option (b)-Busch-mediated) routed
`PurePreparation.born_rank_one` through `pure_state_born_weights_of_certainty`,
which would have invoked Busch unnecessarily and reformulated volume
into trace before evaluating. The volume-forward revision (option (b3))
proves the rank-1 Born theorem by direct Dirac integration, without
Busch. The trace-form reformulation is shipped as a separate corollary.

The chain capstones now cite `invariant_measure_uniqueness` only —
symmetry propagates structurally via the `MeasureBridgeData` argument.
`busch_effect_gleason` does **not** propagate to the chain. This is
faithful to the volume-forward foundational claim and aligns the Lean
tree's `#print axioms` output with what the chain actually invokes.

### Where both axioms enter

For *mixed states* and *general POVMs*, the volume integral against
non-Dirac `π_*μprep` requires identifying the projective measure
structure (where `invariant_measure_uniqueness` enters), and Busch's
characterisation of effect-additive probabilities as trace-form
expressions becomes load-bearing. That is LF4 territory. The
trace-form reformulation theorem (`PurePreparation.born_rank_one_via_trace_form`)
ships in pre-LF4 as the corollary that LF4 will build on for the
mixed-state case.

### Decision log

- **Option (a)** (Dirac as free hypothesis, Busch-only chain): rejected
  on the "build on it over and over again" anti-pattern.
- **Option (b)-Busch-mediated** (Busch in chain, both axioms cited):
  rejected for being foundational-reformulation rather than
  foundational-direct. Cites Busch gratuitously for the pure-state case.
- **Option (b3)-volume-forward** (Direct Dirac integration, symmetry
  structural via bridge type, Busch reserved for reformulation
  corollary): adopted. Matches CSD's volume-forward foundational claim.

### LF3 terminology

`branchState` / `branchWeight` / `BranchSeparation` carry
Everettian-suggestive names but volume-based content. The rename pass
to `eigenSectorState` / `sectorVolume` / `SectorSeparation` (Phase 11)
aligns terminology with the volume-forward foundational claim. Cost
~3-4 h; ideally done pre-LF4 before POVM / mixed-state work adds more
consumers.
