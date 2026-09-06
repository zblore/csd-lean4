# The CR queue — external review, execution order

**Status:** recorded 2026-09-05. **Why this file exists:** the queue lived only in a chat
transcript. Two items had been executed and the remaining fourteen existed nowhere in the
repository, so a lost session would have lost the plan. The titles, sizes, dependencies and
execution order below were recovered from the session log; ⚠️ **the per-item bodies were not fully
recoverable**. ⚠️ Where an item's body is not recovered the detail must be re-supplied by the
author before it is worked: **do not infer the scope from the title** (author instruction,
2026-09-05). As of 2026-09-05 every body has been supplied or recovered; CR-9's is recorded below
and deferred.

## Execution order (as set by the author)

> **CR-1 + CR-15 together** → **CR-2** → **CR-3, CR-6, CR-8, CR-12** → **CR-13** → **CR-16** →
> **CR-7** → **CR-5** → **CR-11** → **CR-4** → CR-9 (background) → CR-14-as-fallback → **CR-10**

## The items

| # | Item | Size | Status |
|---|------|------|--------|
| CR-1 | Governance layer: posit-plus-characterisation wording | days | **DONE 2026-09-05** (`edb34d1`) |
| CR-2 | Posit register | days | **DONE 2026-09-05** — `specs/POSITS.md`, the frontier trichotomy, this file |
| CR-3 | The three priced witnesses as a first-class statement | days | **DONE 2026-09-05** — TOUR section, the horn named in `FiniteQMClosure.lean` (**seams**), the everywhere-only scope recorded at `no_everywhere_correlation`, the Q12-d retirement in `KahlerFibreMixing.lean`, A2 pointer |
| CR-4 | BELL-MIGRATE (28 files) | 1–2 weeks | **DONE 2026-09-06** — every result that was stated over `bornRegion` / `bornRegionN` is now on the fibred arena; nothing in `Empirical` or `LF6` states a Born-region result on the base any more. ⚠️ Its "no new theorem" premise was false: the files prove *frequency* statements, and the fibred side had no frequency theorem. Seven engine pieces were built for it (`globalBasin_born_frequency`, `povm_born_frequency_basin`, `context_born_frequency_basin`, `block_born_frequency_basin`, `vnDilation_pointer_frequency_basin`, `vnDilation_pointer_volume_basin`, `pure_state_born_prob_eq_basin`) plus the weight bridge `globalBasin_toReal_eq_bornRegion_toReal` and the generic i.i.d. process `Mathlib/MeasureTheory/IidTrials.lean`. **Two base-side engines are kept on purpose** (`context_born_frequency_volume`, `block_born_frequency_volume`): the bridge is stated between the two routes, so deleting them would leave the fibred statements with nothing to be compared to |
| CR-5 | Promote the calibrated bank to a named posit **in code** | days | **DONE 2026-09-05** — named at `calibratedBank`, chain status in four headers, POSITS Posit 5 gains the one-bank cost and the three travelling scope conditions. ⚠️ Its "there is no n-step theorem" premise was stale: CR-16 landed one, so the headers say what is proved and what is not |
| CR-6 | Unitary-class posit recorded | days | **DONE 2026-09-05** — TOUR (both halves), `LF4/ProjectedDynamics.lean` header, reconstruction-status A5, Posit 6, Gisin1990 registered |
| CR-7 | Label-space and infrastructure hygiene | days | **DONE 2026-09-05** — CONVENTIONS §12 (not §10, which was taken), `scripts/check-labels.sh` + baseline + 2 probes + CI. ⚠️ The five collisions are **grandfathered, not renamed**; reasons in §12 |
| CR-8 | Naming and residue paragraphs in CV and Empirical | hours | **DONE 2026-09-05** — mode-disjoint commutation (not Haag–Kastler), boost covariance of a posited cone (not Lorentz content), CV Born wording, CV residue paragraph, TOUR three-localities, and CL-049's scope as a theorem (`unitary_invariant_of_recordStatistics_invariant`, pinned) |
| CR-9 | Mathlib upstream batch | weeks, background | ⛔ **DEFERRED by author decision 2026-09-05** — not blocked, not scheduled. Body recorded below so it survives; do not re-raise as pending work |
| CR-10 | *Optional:* unitarity from no-signalling | 4–8 weeks | ⛔ **DECLINED 2026-09-05, with reasons** — premises point the wrong way and the conclusion overshoots Gisin. Successor named below: the Bargmann continuity datum |
| CR-11 | Moving-fibre witness | 1–2 weeks | **DONE 2026-09-05** — `SigmaLayer/MovingFibreWitness.lean` (`movingFibreEnergy`, `_epsProjectable`, ★★ `_not_projectable`, `catStroke` + 3 properties; 3 pins, CL-071), reconstruction-status §7 narrowed. ⚠️ Its `quantum_effective_shadowing` step does not typecheck: that theorem is about matrices, not `EpsProjectable` on `KSigma` |
| CR-12 | Recurrence and persistence scope | days | **DONE 2026-09-05** (incl. the E5 spike retained-not-required annotation) — two new theorems making register-freezing checkable (`unifiedDeisolationModel_interaction_register`, `…_readout_register_irrelevant`, 2 pins), plus FiniteQMClosure header and TOUR |
| CR-13 | Name the equivariance theorem | days | **DONE 2026-09-05** — new `SigmaLayer/Equivariance.lean` (`epistemicMeasure_equivariant`, ★★ `csd_equivariance`, 2 pins, CL-069), POSITS Posit 9, TOUR, Headlines. ⚠️ Corrects the item's premise: µL-preservation is **proved** on the concrete arena, not posited |
| CR-14 | Exploration only: relaxation H-theorem | — | **FALLBACK DONE 2026-09-06** (`relaxation_requires_hyperbolic_fibre`, pinned). ⛔ The H-theorem itself is **not scheduled** — the item says so and it is blocked on first-passage asymptotics; registered as `R-019` |
| CR-15 | *Optional:* characterise the cell law | weeks | **DONE 2026-09-04** (`aa7c3cb`, `e6ba209`) |
| CR-16 | *Optional:* the n-step chain theorem | weeks | **DONE 2026-09-05** — `RecordLayer/NStepChain.lean` (`csd_nstep_born`, `_succ`, `csd_twostep_born`, `csd_nstep_repeatable`, `chainState_shift`; 3 pins, CL-070), POSITS Posit 5. ⚠️ State-level; the n-stage **arena** construction is explicitly not built |

## What CR-15 and CR-1 settled, for anyone reading the later items

CR-15 was executed first on the author's instruction, being the only item that could convert the
programme's weakest posit into a theorem. It did, by a route the queue did not anticipate — torus
**generation**, not the `T^N`-equivariance-plus-normalisation package Part II proposed (which is
false; see the numbering warning below) and not the frame-function route, which was declined. Consequences the
remaining items should not re-litigate:

* The Gleason/frame-function route is **declined, not refuted** (`specs/cell-law-scoping.md`).
* Posit 1 is **restated, not discharged** — the posit count is unchanged.
* "Gleason-free" is a **provenance** claim only (`specs/CSD-CHARTER.md`, drift red flags).

⚠️ **CR-1's literal acceptance test was not met, deliberately.** It asked that a grep for
"gleason-free" return only historical lines, but the same item says to keep the phrase where it
means provenance — which is what ~130 of the uses mean, across 59 module headers, backed by two
guards. Deleting them would have orphaned machine-checked claims. The *meaning* was narrowed at the
governance sites instead. Do not re-raise the grep as an outstanding acceptance failure.

## CR-9 — the upstream batch, recorded but DEFERRED

⛔ **Author decision 2026-09-05: not to be done at this point.** Recorded in full because the whole
purpose of this file is that a plan should not live only in a chat window. Not blocked, not
scheduled, and not to be re-raised as pending work.

**Upstreaming order** (all twelve modules verified present 2026-09-05):

1. `Mathlib/Dynamics/Kac.lean`
2. `Mathlib/Topology/Algebra/CompactRecurrence.lean`, with
   `Mathlib/Dynamics/{CompactGroupNoMixing, CorrelationDecay, CorrelationDecayWitness, CatMapWitness}.lean`
3. The invariant measure on `ℙ(ℂⁿ)`:
   `Mathlib/LinearAlgebra/Projectivization/{Unitary, UnitaryTransitive, FubiniStudy, FubiniStudyUnique}.lean`
   with `Mathlib/LinearAlgebra/Matrix/UnitaryHaar.lean`
4. `Mathlib/MeasureTheory/MutuallySingularMap.lean`

**Process constraints, which are the part most easily lost:**

* **Zulip "Is there code for X?" first**, and specifically ask whether a *Haar-pushforward
  construction* is wanted before building toward one.
* **Wigner rigidity goes last**, and only after maintainer contact.
* ⚠️ **The `QuantumInfo` and `Reversible` trees are NOT Mathlib material.** Do not include them in
  any upstreaming pass.

## ⚠️ CR-4: what the premise got wrong, and what unblocks it

CR-4 says "Numbers are identical by `globalBasin_born`, so no new theorem." The **weights** are
identical — that half is right. But the 28 files do not prove weights, they prove **frequency**
statements, calling `born_frequency_convergence_N` / `_uncond` at 32 sites, and those are almost-sure
limits over i.i.d. draws from `fubiniStudyMeasure` on `ℂℙ^{N−1}`. The fibred side had **no frequency
theorem at all**. So the migration needed a new theorem, and it was the prerequisite rather than a
corollary.

Two further signs it is not textual: the events occur as `(X n) ⁻¹' bornRegion …`, so the random
variables change with the ambient space; and the five files already on the canonical route are all
sequential/record-layer, not frequency-volume, so there was no precedent migration to copy.

**Built 2026-09-05:** `RecordLayer/BasinFrequency.lean` — `globalBasin_born_frequency` and the
`ContextField`-generic `globalBasin_born_frequency_context`, instantiating the already-generic engine
`born_frequency_convergence_partition`. It carries **no positivity hypothesis**, unlike the base-side
twin. The 28 files can now be migrated by application.

✅ **DONE 2026-09-06.** The migration is finished. What it actually cost, and what it bought:

**Cost.** Seven engine theorems, not one. `BasinFrequency.lean` (the prerequisite, CL-072) covers the
direct frequency statements and the POVM family; `ContextVolume.lean` gained the rotated-basis and
degenerate-block twins; `LF5/FlowBornFrequency.lean` gained the pointer-frequency twin and then, in
the last pass, the pointer-**volume** twin that the LF6 flow files needed; `MixedStateBornVolume.lean`
carries the pure-state twin `pure_state_born_prob_eq_basin`, its only consumer. The weight statements
go through one bridge, `globalBasin_toReal_eq_bornRegion_toReal`. The canonical corollaries needed a
law-generic i.i.d. process, so `LF4/TrialWitness.lean`'s `fsTrial*` block was generalised into
`Mathlib/MeasureTheory/IidTrials.lean` (the `fsTrial*` block is left in place with a fold note).

**Bought.** Two things beyond the arena change. (1) `p₀` leaves nearly every statement: the fibred
law is fixed by the prepared ray, so there is no basepoint left to quantify over. The exceptions are
genuine base-arena claims — the flow capstones' `MeasurePreserving (measurementFlow …)` conjuncts —
which keep theirs. (2) **Genericity hypotheses die.** The fibred engines are unconditional where the
base ones carry `hpos`, so migration strictly weakens hypothesis sets: `hardy_max_born_frequency_volume`
lost its `hpos` earlier in the campaign, and `mixed_state_born_eq_ensemble_volume` lost the
`∀ i j, 0 < ‖⟨e_j, Wᴴ eᵢ⟩‖²` bundle entirely (CL-074) — every density operator and every pure
outcome is now covered, where before the outcome had to overlap every eigenvector of `ρ`.

⚠️ **What still names `fubiniStudyMeasure`, and why none of it is unfinished migration.** The
scope of this item was the `bornRegion` / `bornRegionN` consumers; three other families legitimately
keep the base measure, and they are not leftovers.

1. **The retained base engines** — `context_born_frequency_volume`, `block_born_frequency_volume`,
   `context_born_frequency_volume_canonical`, `LF4.pure_state_born_prob_eq_volume`. These are the
   base-side statements the fibred twins are documented against, and
   `globalBasin_toReal_eq_bornRegion_toReal` is an equality *between the two routes*. They have no
   downstream consumers, and that is deliberate.
2. **The moment-map sublevel-set family** — Malus, Stern–Gerlach, Elitzur–Vaidman, Leggett–Garg,
   `QuantumChaos/DerivedCoupling`, `Metrology/Ramsey`. Their region family is
   `{p | momentMap p 0 ≤ momentMap [ψ] 0}`, not a Born region, so they were never in scope. Migrating
   them is a **separate** question with its own engine cost, and it is not opened here.
3. **Genuine base-arena claims** — the flow capstones' `MeasurePreserving (measurementFlow …)`
   conjuncts, `Gates/WignerDischarge`'s `MeasureBridgeData`, `LF6/BlochContraction`. These are
   statements *about* the Fubini–Study measure (invariance, measure-preservation); there is nothing
   to migrate.

`HongOuMandelVolume.lean` mentions `bornRegionN` only to explain why the volume route is unavailable
there, which is still true and still worth saying.

## ⛔ CR-10: declined, and what to do instead

Assessed 2026-09-05 and **not** attempted. Three reasons, none of them effort.

1. **Its premises point the wrong way.** The item says it upgrades the unitary-class posit "using
   premises already carried (marginal stability, Paper C A6)". The corpus's marginal-stability
   object is `reduceB_local_flow_invariant` (`RecordLayer/OnticMarginals.lean`), whose statement
   *takes* `schrodingerUnitary hHA t`. That is **unitary ⇒ marginal stability**. CR-10 needs the
   converse, so using the carried premise would be circular; the converse is not in the corpus.
   ⚠️ Note also that "Paper C A6" is **not** the corpus's `A6`, which is Tsirelson's bound
   (`Empirical/QM/Bell.lean`) — the CONVENTIONS §12 collision, in the wild.
2. **Gisin does not reach unitarity.** Gisin 1990 shows *nonlinear* evolution permits signalling;
   the contrapositive gives **linearity**, not unitarity. Norm preservation and then Wigner-type
   rigidity are still needed, and Wigner lands on *semi*-unitary (unitary **or** antiunitary). The
   argument also turns on an ensemble semantics that is a modelling choice with a live literature of
   objections — a research programme with a posit at its heart, not a derivation.
3. **The corpus already has a shorter route, and it is nearly closed.** Unitarity is reached here via
   Wigner, not no-signalling. Branch exclusivity is **proved**
   (`not_projUnitary_and_projAntiunitary`, by the Bargmann invariant being conjugated on the
   antiunitary branch), and `projectedFlow_unitary_of_bargmann_continuous` closes the selection given
   `hTPP`, a probe triple, and one remaining hypothesis.

**The successor target is that remaining hypothesis:** `hcont`, continuity of the *scalar* Bargmann
observable `t ↦ Δ(Φ_t p, Φ_t q, Φ_t r)` along the flow (`LF4/BargmannSelection.lean`). Concrete,
small, and already reduced. Attack that rather than no-signalling.

**And `hcont` reduces further, which is the useful part.** It is a bespoke condition on a scalar
observable; it should be replaced by a primitive one. Two steps:

1. **`bargmann : ℙ³ → ℂ` is continuous** — *new, and the only real work.* ⚠️ It cannot go through
   `Projectivization.rep`, which is choice-defined and **not** continuous; the route is that
   `bargmann` descends from `bargmannVec` on nonzero vectors and the projection is an *open quotient
   map*, so the descended function is continuous. `Mathlib/LinearAlgebra/Projectivization/Bargmann.lean`
   currently contains **no** continuity infrastructure at all (zero occurrences of `Continuous`).
2. Given (1), `hcont` follows from **continuity of the projected flow in `t`**, which is a natural
   primitive assumption and far weaker than unitarity. ⚠️ It is *not* a field of `KahlerOnticSetup`
   — that structure carries only `measurable_projectedFlow` — so it would be an added hypothesis,
   but a standard one rather than a technical artefact.

So the discharge condition for this posit can be reduced from "the Bargmann observable is
continuous along the flow" to "**the flow is continuous**", at the cost of one continuity lemma.

✅ **DONE 2026-09-05.** `Projectivization.continuous_bargmann`
(`Mathlib/LinearAlgebra/Projectivization/BargmannContinuity.lean`, CSD-free and upstreamable) and
`projectedFlow_unitary_of_flow_continuous` (`LF4/BargmannSelection.lean`, CL-073). The posit's
discharge condition is now plain continuity of the projected flow.

⚠️ Do not attempt to discharge `hcont` on the *concrete* arena as evidence: there the flow is
`schrodingerUnitary • ·`, so `ProjUnitary` holds by construction and
`bargmannObservable_of_projUnitary` makes the observable constant. Trivially continuous, and
circular — the selection theorem exists for *abstract* setups where unitarity is not yet known.


## CR-14: the fallback was the target, and the item agrees

CR-14 proposes a relaxation H-theorem and then says of it: *"Do not schedule this as a result."* Its
own fallback is *"state and prove the obstruction for the compact-group class"*. That fallback was
built on 2026-09-06 and the H-theorem was not attempted.

**Done:** `relaxation_requires_hyperbolic_fibre`
(`SigmaLayer/MovingFibreWitness.lean`). On **one and the same fibre** `KTorus`, the corpus's own
translation `kFlow sh` admits **no summable decay envelope** — for every shift and every summable
`ε` — while the hyperbolic `catStroke` has a finitely supported one. That converts "CSD has no
relaxation account" into "relaxation requires a hyperbolic fibre, and here is the proof that
translations cannot supply it".

⚠️ **Not a relaxation theorem.** It says which dynamics *could* relax, not that any does. No
coarse-grained distribution is shown to approach Haar and no H-theorem is claimed.

⚠️ **Not "Σ cannot mix" either.** The obstruction is the choice of *map*: the compact-group theorem
rules out flows whose iterates are powers of a compact-group element, and a torus *translation* is
one while a toral *automorphism* is not (`LF4/KahlerFibreMixing.lean`).

**Left open as `R-019`,** with the reasons it is not scheduled: the binding problem is first-passage
asymptotics for small sets (research-grade, absent from Mathlib), `HasCorrelationDecayUpTo` is the
untouched finite-scale escape, and route 2 was closed for `kFlow` specifically by
`exists_lag_le_envelope`, so an attempt needs a different fibre map. This is the one place a rival
programme is ahead, and it is the only route to Track B.

⚠️ The item also asks for a paragraph in **Paper D §8**. Manuscripts are not edited here; that
paragraph is the author's, and the repository side is `R-019` plus this entry.

## Numbering warning

The review's own "Part II" numbers posits 1–6; `specs/POSITS.md` numbers the repository's. They
agree at Posit 1 (the cell law) and **diverge after**: review 2 (calibrated bank) = repo 5, review 3
(preparation measure) = repo 9, review 4 (unitary class) = repo 6, review 5 (composite structure) =
repo 7, review 6 (measurement independence) = repo 8; repo 3 (Liouville preservation) and repo 4
(typicality reading) have no review counterpart. When an item below says "Posit N", check which
register is meant. The review's Part II was supplied by the author on 2026-09-05 and the
correspondence is now recorded in `specs/POSITS.md` ("Correspondence with the external review's
Part II").

⚠️ **One Part II claim is refuted, not merely superseded.** Its Posit 1 proposed that
`T^N`-equivariance plus normalisation forces the rate field to be `momentMap`, calling this "a
bounded, plausible theorem worth attempting (see CR-15)". CR-15 showed it **false** —
`rate_field_not_forced_by_torus_symmetry` is a counterexample to exactly that package. The rate
field is forced by torus *generation* instead. Do not re-queue the proposed theorem.

## References

`specs/POSITS.md` (the register, and what "frontier" means);
`specs/cell-law-scoping.md` (CR-15's route, and the declined one); `AXIOMS.md` §3 (the postulate
ledger); `specs/residues.tsv` + `specs/BACKLOG.md` (unfinished work, distinct from posits);
`specs/future-work.md`.
