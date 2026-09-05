# Structural posits: what the corpus assumes rather than derives

**Status:** created 2026-09-04. Companion to `specs/TERMS.md` (what words mean) and
`specs/residues.tsv` (what is unfinished). This file records the third category: places where the
corpus **posits** a piece of structure, the machinery downstream is correct, and the posit itself is
not derived from anything more primitive.

**Why it exists.** A posit is not a defect and not a residue. It does not shrink when a proof lands
elsewhere, and it will not show up in a build failure or an axiom pin — the Lean is honest, because
the posited object is a *definition* or a *structure field*, and definitions are always true of
themselves. The risk is entirely in prose: a posit restated often enough starts to read as a result.
Each entry below therefore names **what would discharge it**, so that the difference between
"assumed" and "established" stays visible.

**How to read an entry.** *Statement* is what is assumed. *Where it enters* is the Lean object.
*What backs it short of derivation* is the honest support — usually a standard unformalised
argument, or agreement with a target. *What would discharge it* is the concrete missing theorem.

---

## Posit 1 — the cell law (a context's rates generate its pointer torus)

* **Statement.** *(Restated 2026-09-04; see the ⚠️ below for what the original said.)* The rates a
  measurement context assigns are Hamiltonian **generators** of that context's coordinate phase
  rotations. Given that, they are the `i`-th Fubini–Study torus moment-map coordinate
  `momentMap p i = ‖p.rep i‖²/‖p.rep‖²` — a theorem, not a stipulation.
* **Where it enters.** `RecordLayer/GlobalBasin.lean`: `momentContext (N) : ContextField N`, a
  *definition*. Everything downstream (`globalBasin_prob`, `globalBasin_born`,
  `MomentMapRace.bornRate_eq_momentMap`, `Measurement.bornMeasurement_prob_momentMap`) is generic in
  the `ContextField` and simply returns whatever rate the chosen field supplies.
* **What backs it short of derivation.**
  1. **The standard symplectic argument, unformalised.** A moment map for the `Tⁿ` action on
     connected `ℂℙ^{N−1}` is unique up to an additive constant; sum-one and non-negativity pin the
     constant to zero, at the form's fixed scale (`IsFubiniStudyKahler`'s `ω u (J u) = ‖u‖²`;
     rescaling `ω ↦ λω` readmits a family). This argument is sound and is **not** disputed here.
     ⚠️ *Updated 2026-09-04:* the corpus now states `ι_{X_i} ω = dΦᵢ` at the **linear** level
     (`RecordLayer/CellLawForced.lean`, `IsPhaseHamiltonian`), which is what the restatement above
     rests on; only the **manifold** form is still absent, Mathlib having no symplectic manifold API.
     See the boundary note in `LF4/MomentMap.lean` and `MATHLIB-GAPS.md`.
  2. **Two proved asymmetries** that fall short of characterisation: the moment map's `μ_FS`
     pushforward is flat / Dirichlet (`fs_moment_pushforward_uniform`,
     `fs_moment_joint_dirichlet_N`), which rival fields do not match; and `bornRate` has a
     flow-carved witness (`shearDeIsolationInteraction`), which rival fields lack.
  3. **Empirical adequacy** — it reproduces the Born weights. ⚠️ *Superseded 2026-09-04 as the
     operative reason:* `torusGenerated_eq_momentMap` is an in-corpus selection theorem whose premise
     mentions no probability, so agreement with the Born target is no longer what picks the field out.
* **⚠️ RESTATED 2026-09-04, and this is the entry's live form.** The posit is no longer *the rates
  are the formula* but **the rates generate the phase rotations of the context's pointer torus**.
  Two theorems fix that boundary from both sides:
  * `RecordLayer/CellLawFreedom.lean` — torus *invariance* does **not** pin the field.
    `sqContext` is torus-invariant (`sqRate_phaseDiag_invariant`), normalised, measurable and
    same-support (`sqRate_eq_zero_iff`), and still differs from the moment map at `[(2,1,1)] ∈ ℂℙ²`
    (`rate_field_not_forced_by_torus_symmetry`).
  * `RecordLayer/CellLawForced.lean` — torus **generation** does pin it, exactly and with no side
    hypothesis. Stated for a **bare rate field** (`generatedRateField_eq_momentMap`): no
    `ContextField` structure is used, so the simplex axioms are visibly not what does the work —
    the additive constant dies by homogeneity. `torusGenerated_eq_momentMap` is the `ContextField`
    corollary; `sqContext_not_torusGenerated` shows the rival fails the generating condition.

  **The posit count is unchanged; its quality is not.** `IsTorusGenerated` is extensionally
  equivalent to the conclusion, so this is a *characterisation*, not a discharge. What it buys is
  anti-circularity: the old premise was a Born-shaped formula feeding a derivation of Born, and the
  new premise `ι_{X_i} ω = dF` mentions no probability, no amplitude and no Born target. It is also
  **not** a noncontextuality assumption — single-context, no cross-basis family — so "Gleason-free"
  survives for the cell law as well as the volume theorem.
* **What would discharge it.** Derive `IsTorusGenerated` from the de-isolation dynamics: show that
  the interaction which creates the record generates the pointer torus, rather than assuming it.
  That is the `H_int` frontier, with `SigmaLayer/ChartIntegralCurve.lean` (chart-level Hamiltonian
  generation) the nearest precedent and `R-016` the adjacent open item. No cheap brick is expected
  there; recorded so the boundary stays visible, not as queued work.

## Posit 2 — the sector (`μ_FS` as the typicality measure)

* **Statement.** The ontic typicality measure on the projective base is Fubini–Study.
* **Where it enters.** The sector structure's measure field; Paper C **A5** (*projectability* —
  never "the origin of Σ").
* **What backs it short of derivation.** `fubiniStudyMeasure_unique`: `μ_FS` is the unique
  `U(N)`-invariant probability measure. This is a genuine forcing result **given the symmetry**, so
  the posit is narrow — it is the symmetry requirement, not the measure, that is assumed.
* **⚠️ Not derivable from the dynamics.** `SigmaLayer/SectorPostulateNoGo.lean`
  (`flow_admits_invariant_ne_fubiniStudy`) proves a deterministic flow does not pin the sector, and
  `LF4/TypicalityForcing.lean` records the same wall. Attempts to "derive Σ" are a non-question
  (`specs/CSD-CHARTER.md`); *constraining* it, as `fubiniStudyMeasure_unique` does, is the live form.
* **⚠️ This entry covers the MEASURE half only.** `AXIOMS.md` §3.3 posits more: nothing forces `π`
  to project onto the quantum-effective sector specifically, and nothing forces `G = SU(N)`. That
  `(π, G)` half is posited structural data with only two coherence conditions constraining it, and
  it is **not** discharged by `fubiniStudyMeasure_unique`, which presupposes the symmetry.
* **What would discharge it.** Nothing is expected to: this is close to the floor. The honest
  statement is that the sector is posited and tightly constrained, not derived.

## Posit 3 — Liouville preservation of the flow

* **Statement.** Every time-`t` map of the constraint dynamics preserves `μL`.
* **Where it enters.** `ConstraintDynamics.flow_preserves` / `flow_preserves_volume` — a **structure
  field**, posited of every model, not derived (see `specs/TERMS.md`, "Liouville").
* **What backs it short of derivation.** The dynamics sense is what the downstream typicality
  arguments actually use (`LF4/BornFlowLinkage.lean`), and it is standard for a Hamiltonian flow.
* **⚠️ Scope.** That this measure **is** the Kähler top-power volume `ω^{∧n}/n!` is *not*
  established — same manifold wall as Posit 1. `LF4/KahlerVolumeForced.lean` proves the
  normalisation core and leaves the top-power identity open.
* **What would discharge it.** Constructing the flow from a Hamiltonian and proving preservation,
  rather than positing it as a field — blocked on the same manifold API.

## Posit 4 — the typicality reading (probability *is* volume ratio)

* **Statement.** The outcome weight is the `μL`-volume ratio
  `μL(π⁻¹Ωᵢ(M) ∩ Ω₀) / μL(Ω₀)`. Not that it *equals* a probability numerically — that it **is** one.
* **Where it enters.** Its Lean entry point is the **i.i.d. product structure of LF1's
  repeated-trial law** — where the reading stops being interpretation and becomes mathematics.
  `AXIOMS.md` §3 names it one of the three load-bearing postulates, alongside the ontic substrate
  and the sector.
* **⚠️ A second commitment rides along:** that one preparation law serves every trial — i.i.d.
  *across preparations*. Bohmian quantum equilibrium carries the analogous assumption. It is
  implicit in the product measure and is registered in its own right as **Posit 8** (measurement
  independence); `specs/sigma-fibre-contextuality.md` calls it measurement-independence.
* **What backs it short of derivation.** Self-consistency: the strong law shows the reading does not
  contradict itself — typical trajectories reproduce the volume ratios as frequencies
  (`born_frequency_convergence_N`). That is a coherence check, not a derivation.
* **⚠️ This is the interpretive posit, and it is the one that cannot be argued down.** Distinct from
  Posit 2: Posit 2 says *which* measure; this says that measure *is* the probability. Every
  typicality-based programme (Boltzmann, Bohmian equivariance) carries a posit of this shape.
* **What would discharge it.** Nothing, and the register should not pretend otherwise. It is a
  choice about what probability means, not a theorem with a missing proof.

## Posit 5 — the calibrated bank (apparatus preparation)

* **Statement.** The apparatus starts in a known state: the swap witness's ancilla bank in the
  computational vertex states, the join witness's slot block-supported.
* **Where it enters.** `calibratedBank` (`RecordLayer/SwapClosure.lean`) and `join_block_luders`'s
  `hα` — definitions and hypotheses, never `axiom`s. `AXIOMS.md` §3.8. The definition site names it
  as this posit, so the code and the register agree.
* **⚠️ Its cost: one bank per measurement.** A depth-`n` record chain is an `n`-bank construction,
  so this posit is **renewed at every step**, not paid once. That is what makes the chain's status
  worth stating precisely rather than loosely.
* **⚠️ Three scope conditions travel with it,** and they are conditions on the result rather than
  gaps in it: a **rank-one, computational-basis first measurement** (degenerate first measurements
  are the recorded open construction, `RecordLayer/DegenerateLuders.lean`); **one bank per
  measurement**, as above; and the **§2a-scoped Hamiltonian origin** of the swap propagator, which
  is stated and not formalised (`R-016`'s family).
* **What backs it short of derivation.** Two results keep it honest rather than free: the Dirac form
  of the calibration is **forced** by `collapse_accuracy_bound` (approximate collapse is priced in
  ready-state improbability), and `swap_not_blockLuders` proves no fixed ray-level calibration
  serves both witnesses — so the posit is constrained from two sides.
* **⚠️ The chain is now proved to arbitrary depth, GIVEN `n` banks** (2026-09-05, CR-16).
  `csd_nstep_born` (`RecordLayer/NStepChain.lean`) proves the depth-`n` law for every sequence of
  contexts and outcomes, by induction, with each step's rate read at `chainState` — the preparation
  first, the collapsed vertex thereafter. One measurement consumes one bank, so a depth-`n` chain
  renews this posit `n` times, and that renewal is visible in the statement as the per-step
  `epistemicMeasure` rather than hidden. `csd_nstep_repeatable` supplies non-vacuity: repeating one
  basis reproduces the first outcome with probability one at every depth.
  ⚠️ State-level, not a single-arena factorisation — `two_stage_joint` does the harder `n = 2`
  arena version and generalising *it* is not done.
* **⚠️ This is "the pointer starts at zero".** A preparation-of-the-apparatus assumption, of the
  same family every measurement account makes.
* **What would discharge it.** Deriving the ready state from the dynamics rather than positing it —
  adjacent to Posit 1's discharge condition, and blocked by the same `H_int` frontier.

## Posit 6 — the unitary class

* **Statement.** The projected flow is projectively unitary (`ProjUnitary`, `LF4/BargmannSelection.lean`);
  equivalently the generator is a Fubini–Study isometry generator, equivalently the expectation of a
  self-adjoint operator.
* **Where it enters.** `LF4/ProjectedDynamics.lean`: `projectedFlow_eq_unitary_family` takes
  `hU : ∀ t, ProjUnitary d t` as a hypothesis and *chooses* the family (`choose U hU'`), so nothing
  there establishes unitarity.
* **What backs it short of derivation.** The forward half is a **theorem**: unitary ⇒ Schrödinger
  generator (`projectedFlow_schrodinger_form_of_continuous_flow`, ledger `CL-063`). What is posited
  is the class, not the consequence. It is also *motivated*: nonlinear projective evolution with
  tensor structure and local Born statistics permits signalling (Gisin 1990), which no-signalling
  forbids — a reason to believe the posit, not a derivation of it.
* **⚠️ An optional upgrade exists.** A derivation from no-signalling (Gisin's argument) would turn
  this into a theorem — queued as `CR-11`/`CR-10` in `specs/cr-queue.md`, four to eight weeks, and
  explicitly optional. Until then it is a posit with a known route out, which is a better position
  than most entries here.
* **What would discharge it.** That derivation.

## Posit 7 — composite structure (local tomography)

* **Statement.** Local subsystems carry full matrix algebras and the composite is locally
  tomographic.
* **What backs it short of derivation.** A great deal: Artin–Wedderburn then **forces** the tensor
  product and `N_AB = N_A · N_B` (`compositeAlgReconstruction`, `CV/CompositeArena.lean`), and the
  algebraic premise is provably the record-level statement in both directions
  (`recordLocallyTomographic_iff_adjoin_eq_top`). So the posit is stated in record vocabulary rather
  than lattice vocabulary — that conversion is what brick 2 bought.
* **⚠️ Permanent boundary, registered as `R-017`.** It cannot be derived: a composite carrying
  commuting local algebras need not be locally tomographic (real-Hilbert-space QM is the
  counterexample), and local tomography alone does not select the complex field.
* **What would discharge it.** Nothing. This is a boundary, not a gap — the entry exists so that
  "the tensor product is derived" is never written without its premise.

## Posit 8 — measurement independence

* **Statement.** One preparation measure serves every measurement context.
* **What backs it short of derivation.** **Nothing, and that is the honest entry.** It is shared
  with every deterministic theory — the assumption Bell-type arguments call measurement
  independence or no-conspiracy.
* **⚠️ Settings are not represented in Σ.** The corpus does not model the apparatus setting as a
  Σ-degree of freedom, so the independence is a modelling choice rather than a derived fact. It also
  rides inside Posit 4's product structure, which is why the two entries cross-reference.
* **What would discharge it.** Nothing available. Denying it is superdeterminism, which is a
  different theory rather than a proof.

## Posit 9 — the product form of the preparation measure

* **Statement.** `μL` is a product: the base factor is `μ_FS`, the fibre factor uniform.
* **What backs it short of derivation.** The **base half is proved** — `fubiniStudyMeasure_unique`
  (Posit 2). The fibre half is the product form itself
  (`epistemicMeasure_eq_disintegration`, `RecordLayer/EpistemicDisintegration.lean`).
* **⚠️ Preservation is not the same as selection, and the pair is now named.**
  `csd_equivariance` (`SigmaLayer/Equivariance.lean`) proves that on the concrete arena the flow
  carries the epistemic measure to the epistemic measure at the evolved ray *and* leaves `μL`
  invariant — unconditionally, since `manyToOneSetup` discharges `flow_preserves_volume` with a
  proof rather than positing it. None of that selects `μ_FS`; symmetry does. Cite the two together
  or the no-go below reads more negatively than the position warrants.
* **⚠️ A posit by necessity, not by omission.** The dynamical route is closed *by theorem*:
  `flow_admits_invariant_ne_fubiniStudy` (`SigmaLayer/SectorPostulateNoGo.lean`) shows a
  deterministic flow does not pin the measure. So this cannot be derived from the dynamics, and
  saying so is a result rather than an admission.
* **What would discharge it.** Nothing from the dynamics, by that theorem. Extends Posit 2 to the
  fibred Σ.

---

## Correspondence with the external review's Part II

⚠️ **Two registers, two numberings.** This file's numbers are the repository's and are frozen; the
review's Part II numbers its own. They agree at Posit 1 and diverge after. The map:

| Review Part II | Here | Note |
|---|---|---|
| 1 — cell law | **1** | agree; but see the correction below |
| 2 — calibrated bank | **5** | |
| 3 — preparation measure | **9** (+ base half in **2**) | |
| 4 — unitary class | **6** | |
| 5 — composite structure | **7** | |
| 6 — measurement independence | **8** | |
| *(not in the review)* | **3** | Liouville preservation of the flow |
| *(not in the review)* | **4** | the typicality reading |

⚠️ **The review's Posit 1 characterisation paragraph is superseded, and in one respect refuted.**
It proposed that "`T^N`-equivariance plus a normalisation condition forces the rate field to be
exactly `momentMap`" as "a bounded, plausible theorem worth attempting (see CR-15)". CR-15 was
attempted, and **that conjecture is false**: `rate_field_not_forced_by_torus_symmetry`
(`RecordLayer/CellLawFreedom.lean`) exhibits `sqContext`, torus-invariant and normalised and
same-support, which is not the moment map. What *does* force the rate field is torus **generation**
— the moment-map equation, not the symmetry (`torusGenerated_eq_momentMap`). So the review's
"one genuine characterisation gap" is closed, but by a different theorem than the one proposed, and
the proposed one is a counterexample rather than a target. See `specs/cell-law-scoping.md`.

The review also records the measurement **trilemma** as a theorem rather than a posit — correct, and
it is deliberately absent from this register.

---

## What "frontier" means here — three different things

Three dated statements of frontier status looked contradictory, and the disagreement was real but
verbal. They were written either side of the MD-1 closure (2026-08-31) and each used "frontier" for
a different object. The trichotomy that dissolves it:

1. **Permanent boundary** — an input the Lean claim can never supply. `R-015` (which `H_int` a given
   apparatus physically realises) and `R-017` (local tomography). These never close. *Not gaps.*
   ⚠️ The two are boundaries for different reasons and the comparison only fits one: `R-015` is a
   modelling input Bohm and Everett take too, whereas `R-017` is a **structural posit on the
   composite sector** — Bohm and Everett do not assume local tomography, they assume the tensor
   product outright.
2. **Open mathematics** — a statement with a concrete Lean shape and no proof yet. `R-016` (the
   chart→arena transport of Hamiltonian generation). Closes when someone proves it.
3. **Open foundations** — a posit whose discharge condition is known but is not a Lean-shaped task.
   Posit 1's: derive `IsTorusGenerated` from the de-isolation dynamics. This is *the* reconstruction
   frontier, and it is not on any queue because it is not a brick.
   ⚠️ The definite article is a **decision**, not an oversight. The ranked-out candidate is
   **base-only context-fixed regions at `N ≥ 3`**: discharged on the fibre at every `N`
   (`GlobalBasin`), with the base-only question parked, open in both directions, and by author
   decision characterising a special case rather than gating the axiom
   (`specs/sigma-fibre-contextuality.md`). Posit 5's discharge is the same `H_int` family, so the
   singular holds.

Read that way the three statements agree:

* `specs/reconstruction-status.md` §1 — "the goal is NOT met." **True**, by (3): the reconstruction
  is complete only when the cell law is derived rather than posited.
* `specs/CSD-CHARTER.md` — what remains is "not a foundational frontier." **True of the record
  layer's machinery**, by (1) **and** (2): the charter names both residuals, so the residue there is
  a permanent boundary *plus* one open-mathematics item — not a gap in the account.
* `specs/BACKLOG.md` E5 — "the two research frontiers." **Partly stale**: the fibre-from-dynamics
  question in its mixing form was retired as mis-specified (2026-08-24) and re-executed in honest
  form (2026-08-27, `ShearDeIsolation.lean`); what survives of it is (3).

⚠️ **`G3b` / carve-out `L2` ("outcome region generated by the dynamics, not posited") is not a
single open target and should not be cited as one.** It splits: the choice of interaction is (1),
the generation statement is (2), and deriving the rate field is (3). `ShearDeIsolation.lean`
discharges `basin_rate` from a *constructed* propagator — a witness, not a derivation, and the
propagator's Hamiltonian generation is stated-not-formalised. Retiring `G3b` outright would
overclaim; splitting it is the accurate move.

---

## Numbering

⚠️ **These numbers are the repository's.** They are cited from `AXIOMS.md` §3.10,
`specs/CSD-CHARTER.md`, `specs/reconstruction-status.md` §7a, several module headers and the
glossary, so they are **stable and must not be renumbered** — add, never resequence. The external
review's "Part II" uses its own numbering; the correspondence table above is authoritative. If a
document cites "Posit N", check which register it means.

---

## Where the posits are also listed

Keep these in step with this file, or the register stops being a register:
`AXIOMS.md` §3 (the postulate ledger — the cell law is §3.10), `specs/INDEX.md`'s AXIOMS row,
`specs/CSD-CHARTER.md` "The picture", `specs/reconstruction-status.md` §7a, and the glossary entry
`is-the-born-rule-derived`. The external review that prompted the register is tracked in
`specs/cr-queue.md`.

⚠️ **`AXIOMS.md` §3 currently registers Posits 1–5 only.** Posits 6–9 arrived 2026-09-05 from the
review's Part II and have no §3 section yet; `CR-6` covers the unitary class specifically. Adding
them is queued, not forgotten.

⚠️ **Known undercount, deliberately not fixed here.** `README.md` and `docs/TOUR.md` both carry a
"what is posited and not derived" inventory that omits the cell law. Those are landing-surface
documents (CONVENTIONS §10) and change only when a headline claim changes, so the line is queued
for the next headline-touching landing rather than patched now. Recorded so it is not lost.

## Adding an entry

A new entry belongs here when all three hold: the object is a definition or structure field; prose
elsewhere describes it in language stronger than "posited"; and no theorem in the corpus derives it.
Give it the five headings above, and in particular **do not add an entry without a "what would
discharge it" line** — an entry that cannot say what would settle it is a confession, not a record.
