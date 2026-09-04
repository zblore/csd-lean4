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
    hypothesis (`torusGenerated_eq_momentMap`); `sqContext_not_torusGenerated` shows the rival fails
    the generating condition.

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

---

## Adding an entry

A new entry belongs here when all three hold: the object is a definition or structure field; prose
elsewhere describes it in language stronger than "posited"; and no theorem in the corpus derives it.
Give it the five headings above, and in particular **do not add an entry without a "what would
discharge it" line** — an entry that cannot say what would settle it is a confession, not a record.
