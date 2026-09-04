/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerForm

/-!
# W2: the Kähler ontic-sector interface

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler ontic-sector interface).

**Glossary:** https://glossary.constraintsurfacedynamics.com/kahler-form/
Plain-language, CSD-role and formal statements of the Kahler form, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

This module packages the CSD Kähler-sector assumptions as a single Lean
structure, `KahlerOnticSetup N`, whose fields are sector-level HYPOTHESES.
There are NO global axioms: the CSD postulates (the ontic substrate `Σ`, the
Kähler-sector posit, typicality via a Liouville measure) live as structure
fields, so they never appear in `#print axioms`. This is the standing CSD
posture (postulates carried as hypotheses, not axioms; AXIOMS.md §0).

## Honest scope

This is the sector INTERFACE, the forward-direction scaffold that the chain

    Σ-flow → projected ℂℙ^{N-1} flow → FS-isometry / transProb-preserving flow
           → unitary Schrödinger dynamics

will consume (W3 Wigner-selection and W5 projected Schrödinger dynamics build
on it). It is **not** a proof of `Σ`, **not** a derivation of the posited CSD sector (SO-1)
posit, and **not** a claim the ontology is closed. The load-bearing dynamical
content is carried by the `flow` / `projectable` / `flow_preserves_volume`
fields; the Kähler-geometry data is carried by the concrete pointwise /
normalization fields (see the ledger below), whose manifold-level residual
stays outside the structure. Do not read this file as deriving anything.

## Field ledger (all fields concrete — interface tightened 2026-08-06, F-04)

Every field is now real Mathlib content, forced on any inhabitant:
- `instMeasurable`, `instTopological` : bundled instances on `Σ`;
- `compact_sigma : CompactSpace Σ` : genuine typeclass value (compactness of the
  ontic sector, per the compact-Kähler requirement on `Σ`);
- `kahler_pointwise : IsFubiniStudyKahler N` : the pointwise Fubini–Study
  Kähler-compatibility triple on the tangent model (`g = re⟪·,·⟫`,
  `ω = im⟪·,·⟫`, `J = i•·` with `J² = -1`, `ω = g∘J`, `g = ω∘J`, `ω` a
  `(1,1)`-form, `ω u (Ju) = ‖u‖²`), proved axiom-free via
  `Kahler.fubiniStudy_pointwise_kahler_compatibility`; the FLAT closedness
  `dω = 0` is also proved (`Kahler.extDeriv_fundamentalFormAlt`,
  `KahlerClosed.lean`, 2026-08-06), leaving only the `ℂℙ^{N-1}` manifold
  spelling open;
- `liouvilleMeasure : Measure Σ` + `liouville_isProbability` : the typicality /
  Liouville measure, normalized (an instance, so
  `[IsProbabilityMeasure S.liouvilleMeasure]` is automatic);
- `pi : Σ → ℙ ℂ (EuclideanSpace ℂ (Fin N))` + `pi_measurable` : the projection
  onto the operational projective space. The target is EXACTLY Wigner's
  `ℙ ℂ (EuclideanSpace ℂ (Fin N))`, so W3 can feed `pi`-images to
  `wigner_rigidity` / `transProbPreserving_unitary` directly;
- `flow : ℝ → Σ → Σ` + `flow_preserves_volume` : the deterministic,
  Liouville-preserving ontic flow (`MeasurePreserving`, genuine);
- `projectedFlow` + `projectable` : the flow descends to a well-defined flow on
  `ℙ ℂ (EuclideanSpace ℂ (Fin N))`. This is the load-bearing dynamical field the
  W3/W5 chain consumes: it makes the projected dynamics `Σ`-covariant.

## History: the abstract-placeholder pairs (removed 2026-08-06)

Until 2026-08-06 the two Kähler-geometry conditions were carried as
instance-supplied abstract pairs (`IsKahlerSector : Prop` +
`kahler_condition`, `IsLiouvilleKahlerVolume : Prop` +
`liouville_eq_kahler_volume`). Every concrete instance already supplied the
genuine cores (`IsFubiniStudyKahler N`, `IsProbabilityMeasure`; never
`True`), but a consumer quantified over `KahlerOnticSetup` could not extract
those laws from the abstract fields — the F-04 finding of the 2026-08-06
external review. The pairs were therefore replaced by the concrete fields
`kahler_pointwise` / `liouville_isProbability` above, with no change to any
instance's proof obligations.

The **manifold** residual is honestly open, and narrowed 2026-08-06: the FLAT
closedness `dω = 0` on the tangent model is now proved
(`Kahler.extDeriv_fundamentalFormAlt`, `KahlerClosed.lean`); what remains is
the quotient/manifold spelling on `ℂℙ^{N-1}` — closedness there and the
top-power identity `ω^{∧(N-1)}/(N-1)! = μ_FS` — pending Mathlib
manifold-form API. When Mathlib grows that API,
`kahler_pointwise` is the slot to strengthen from the pointwise
`IsFubiniStudyKahler` to the full closed-2-form condition; the dynamical
fields are unaffected. See `specs/connectivity-manifest.md` (link L1) and
`PLACEHOLDERS.md`.
-/

@[expose] public section

open MeasureTheory
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- **The genuine formalizable core of the Kähler-sector posit.** On the tangent model
`EuclideanSpace ℂ (Fin N)` of `ℂℙ^{N-1}`, the Fubini–Study triple
`g = re⟪·,·⟫` (metric), `ω = im⟪·,·⟫` (fundamental form), `J = i • ·` (complex
structure) satisfies the defining almost-Kähler relations:

* `J² = -1` (complex structure);
* `ω u v = g (J u) v` (the form is the metric twisted by `J`);
* `g u v = ω u (J v)` (the metric is recovered from `ω` and `J`);
* `ω (J u) (J v) = ω u v` (`ω` is a `(1,1)`-form);
* `ω u (J u) = ‖u‖²` (positivity / taming).

This is the linear-algebra core of "`Σ` is a Kähler sector" — the *compatible with
the complex structure and positive* content — proved axiom-free
(`Kahler.fubiniStudy_pointwise_kahler_compatibility`). It is the type of the
structure's `kahler_pointwise` field (2026-08-06 tightening; formerly an
instance-supplied abstract `Prop`, historically `True` before 2026-07-19).
The manifold-level closedness `dω = 0` and the top-power identity
`ω^{∧(N-1)}/(N-1)! = μ_FS` need exterior calculus absent from Mathlib and remain the
honestly-named residual (connectivity link L1). -/
def IsFubiniStudyKahler (N : ℕ) : Prop :=
  ∀ u v : EuclideanSpace ℂ (Fin N),
    Kahler.complexStructure (Kahler.complexStructure u) = -u
    ∧ Kahler.fundamentalForm u v = Kahler.metric (Kahler.complexStructure u) v
    ∧ Kahler.metric u v = Kahler.fundamentalForm u (Kahler.complexStructure v)
    ∧ Kahler.fundamentalForm (Kahler.complexStructure u) (Kahler.complexStructure v)
        = Kahler.fundamentalForm u v
    ∧ Kahler.fundamentalForm u (Kahler.complexStructure u) = ‖u‖ ^ 2

/-- The Fubini–Study Kähler compatibility holds on the tangent model of `ℂℙ^{N-1}`
(axiom-free; `Kahler.fubiniStudy_pointwise_kahler_compatibility`). This discharges the
`kahler_pointwise` field genuinely on every `ℂℙ`-based instance. -/
theorem isFubiniStudyKahler (N : ℕ) : IsFubiniStudyKahler N :=
  fun u v => Kahler.fubiniStudy_pointwise_kahler_compatibility u v

/-- **The Kähler ontic-sector interface (W2).** Sector-level hypotheses bundled
as structure fields (no global axioms). `N` is the operational Hilbert
dimension; the projective target `ℙ ℂ (EuclideanSpace ℂ (Fin N))` matches
Wigner's, so W3 consumes `wigner_rigidity` on `pi`-images directly.

See the module docstring for the field ledger. Every field is concrete
(interface tightened 2026-08-06, F-04): the Kähler-geometry content is the
pointwise `kahler_pointwise : IsFubiniStudyKahler N` plus the normalization
`liouville_isProbability`; the manifold-level differential-form data
(`dω = 0`, top-power = `μ_FS`) stays outside the structure, honestly open at
connectivity link L1. -/
structure KahlerOnticSetup (N : ℕ) where
  /-- The ontic sector state space `Σ`. -/
  Sigma : Type*
  /-- Bundled measurable-space instance on `Σ`. -/
  [instMeasurable : MeasurableSpace Sigma]
  /-- Bundled topological-space instance on `Σ`. -/
  [instTopological : TopologicalSpace Sigma]
  /-- GENUINE: `Σ` is compact (the compact-Kähler requirement). -/
  compact_sigma : CompactSpace Sigma
  /-- GENUINE (the pointwise core of the Kähler-sector posit, tightened
  2026-08-06 — formerly an instance-supplied abstract `Prop` pair, which
  consumers could not unpack; F-04): the Fubini–Study Kähler compatibility
  triple on the tangent model of the projective target — `J² = -1`,
  `ω = g∘J`, `g = ω∘J`, `ω` a `(1,1)`-form, `ω u (Ju) = ‖u‖²`. The
  **manifold** residual (closedness `dω = 0` and the top-power identity
  `ω^{∧(N-1)}/(N-1)! = μ_FS`) needs exterior calculus absent from Mathlib
  and stays the honestly-named open piece (connectivity link L1). -/
  kahler_pointwise : IsFubiniStudyKahler N
  /-- GENUINE: the Liouville / typicality measure on `Σ`. -/
  liouvilleMeasure : Measure Sigma
  /-- GENUINE (the normalization core of "Liouville = Kähler top-power
  volume", tightened 2026-08-06 from the abstract `Prop` pair; F-04):
  `liouvilleMeasure` is a probability measure. Registered as an instance,
  so `[IsProbabilityMeasure S.liouvilleMeasure]` is automatic for every
  setup `S`. -/
  liouville_isProbability : IsProbabilityMeasure liouvilleMeasure
  /-- GENUINE: the projection onto the operational projective space (Wigner's
  target). -/
  pi : Sigma → ℙ ℂ (EuclideanSpace ℂ (Fin N))
  /-- GENUINE: `pi` is measurable. -/
  pi_measurable : Measurable pi
  /-- GENUINE: the deterministic ontic flow. -/
  flow : ℝ → Sigma → Sigma
  /-- GENUINE: each time-`t` flow map preserves the Liouville measure. -/
  flow_preserves_volume :
    ∀ t, MeasurePreserving (flow t) liouvilleMeasure liouvilleMeasure
  /-- GENUINE: the induced flow on the projective target. -/
  projectedFlow :
    ℝ → ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))
  /-- GENUINE (load-bearing for W3/W5): the ontic flow descends to
  `projectedFlow` along `pi`. This is what makes the projected dynamics
  `Σ`-covariant, the hinge the Wigner-selection / Schrödinger chain consumes. -/
  projectable : ∀ t x, pi (flow t x) = projectedFlow t (pi x)

attribute [instance] KahlerOnticSetup.instMeasurable KahlerOnticSetup.instTopological
attribute [instance] KahlerOnticSetup.compact_sigma
attribute [instance] KahlerOnticSetup.liouville_isProbability

/-- **Inhabitation witness (non-vacuity).** The degenerate base case
`Σ = ℙ ℂ (EuclideanSpace ℂ (Fin N))`, `π = id`, the trivial flow-family
`flow t = id`, and `liouvilleMeasure = fubiniStudyMeasure p₀`. This confirms the
`KahlerOnticSetup N` fields are mutually satisfiable (the interface is
non-empty), exactly the `π = id` base-case role `LF4.cpSectorData` plays for
`SectorData`. The two Kähler-geometry fields are the concrete
`kahler_pointwise := isFubiniStudyKahler N` (the pointwise FS Kähler
compatibility, proved) and `liouville_isProbability` (μ_FS is normalized,
an instance); the
dynamical fields are the identity flow (`Φ = id`), so this witness carries no
dynamics (structural debt D1, as elsewhere in LF4). A genuine `Φ ≠ id`
inhabitant is available by reusing `kFlow` on `KSigma`; this witness only
certifies inhabitability. -/
noncomputable def trivialKahlerOnticSetup
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    KahlerOnticSetup N where
  Sigma := ℙ ℂ (EuclideanSpace ℂ (Fin N))
  compact_sigma := inferInstance
  kahler_pointwise := isFubiniStudyKahler N
  liouvilleMeasure := Matrix.UnitaryGroup.fubiniStudyMeasure p₀
  liouville_isProbability := inferInstance
  pi := id
  pi_measurable := measurable_id
  flow := fun _ => id
  flow_preserves_volume := fun _ => MeasurePreserving.id _
  projectedFlow := fun _ => id
  projectable := fun _ _ => rfl

/-- The witness's Liouville measure is a probability measure (Fubini-Study is
normalised). Records that the base case is a genuine typicality law. -/
instance instIsProbabilityMeasureTrivialLiouville
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    IsProbabilityMeasure (trivialKahlerOnticSetup N p₀).liouvilleMeasure :=
  Matrix.UnitaryGroup.instIsProbabilityMeasureFubiniStudyMeasure p₀

end LF4
end CSD
