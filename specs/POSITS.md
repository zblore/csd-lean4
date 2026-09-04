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

## Posit 1 — the cell law (outcome rates are the torus moment map)

* **Statement.** The rate a measurement context assigns to outcome `i` at ontic base point `p` is
  the `i`-th Fubini–Study torus moment-map coordinate, `momentMap p i = ‖p.rep i‖²/‖p.rep‖²`.
* **Where it enters.** `RecordLayer/GlobalBasin.lean`: `momentContext (N) : ContextField N`, a
  *definition*. Everything downstream (`globalBasin_prob`, `globalBasin_born`,
  `MomentMapRace.bornRate_eq_momentMap`, `Measurement.bornMeasurement_prob_momentMap`) is generic in
  the `ContextField` and simply returns whatever rate the chosen field supplies.
* **What backs it short of derivation.**
  1. **The standard symplectic argument, unformalised.** A moment map for the `Tⁿ` action on
     connected `ℂℙ^{N−1}` is unique up to an additive constant; sum-one and non-negativity pin the
     constant to zero, at the form's fixed scale (`IsFubiniStudyKahler`'s `ω u (J u) = ‖u‖²`;
     rescaling `ω ↦ λω` readmits a family). This argument is sound and is **not** disputed here —
     but Mathlib has no symplectic API, so the corpus never states `ι_{X_i} ω = dΦᵢ`. See the
     boundary note in `LF4/MomentMap.lean` and `MATHLIB-GAPS.md`.
  2. **Two proved asymmetries** that fall short of characterisation: the moment map's `μ_FS`
     pushforward is flat / Dirichlet (`fs_moment_pushforward_uniform`,
     `fs_moment_joint_dirichlet_N`), which rival fields do not match; and `bornRate` has a
     flow-carved witness (`shearDeIsolationInteraction`), which rival fields lack.
  3. **Empirical adequacy** — it reproduces the Born weights. This is the operative reason, and it
     is the thing MD-1 wants derived rather than assumed.
* **⚠️ Provably not forced by the verified properties.**
  `RecordLayer/CellLawFreedom.lean` exhibits `sqContext`, a second `ContextField` that is
  torus-invariant (`sqRate_phaseDiag_invariant`), normalised, measurable, and has the same support
  (`sqRate_eq_zero_iff`), and proves `rate_field_not_forced_by_torus_symmetry` — it differs from the
  moment map at `[(2,1,1)] ∈ ℂℙ²`. So `Tⁿ`-symmetry plus normalisation plus support, which is the
  whole of what Lean verifies about `momentMap`, does not single it out.
* **What would discharge it.** Either (a) the symplectic route — a moment-map equation in Lean,
  blocked on the manifold API (`MATHLIB-ABSENT(file:Mathlib/Geometry/Manifold/DifferentialForm)`);
  or (b) a cross-basis consistency (frame-function) characterisation — stage 2 of
  `specs/cell-law-scoping.md`, which carries its own caveat about what that would cost.

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
