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

**Category:** 3-Local (the Kähler ontic-sector interface).

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
on it). It is **not** a proof of `Σ`, **not** a derivation of the A5 sector
posit, and **not** a claim the ontology is closed. The load-bearing dynamical
content is carried by the `flow` / `projectable` / `flow_preserves_volume`
fields; the Kähler-geometry data is carried by explicitly-labelled abstract
placeholder fields (see below). Do not read this file as deriving anything.

## Genuine vs abstract-placeholder fields

GENUINE (real Mathlib content, forced on any inhabitant):
- `instMeasurable`, `instTopological` : bundled instances on `Σ`;
- `compact_sigma : CompactSpace Σ` : genuine typeclass value (compactness of the
  ontic sector, per the compact-Kähler requirement on `Σ`);
- `liouvilleMeasure : Measure Σ` : the typicality / Liouville measure;
- `pi : Σ → ℙ ℂ (EuclideanSpace ℂ (Fin N))` + `pi_measurable` : the projection
  onto the operational projective space. The target is EXACTLY Wigner's
  `ℙ ℂ (EuclideanSpace ℂ (Fin N))`, so W3 can feed `pi`-images to
  `wigner_rigidity` / `transProbPreserving_unitary` directly;
- `flow : ℝ → Σ → Σ` + `flow_preserves_volume` : the deterministic,
  Liouville-preserving ontic flow (`MeasurePreserving`, genuine);
- `projectedFlow` + `projectable` : the flow descends to a well-defined flow on
  `ℙ ℂ (EuclideanSpace ℂ (Fin N))`. This is the load-bearing dynamical field the
  W3/W5 chain consumes: it makes the projected dynamics `Σ`-covariant.

ABSTRACT PLACEHOLDER (the corpus does not yet formalise symplectic/Kähler
differential forms on an abstract measurable+topological `Σ`; these fields
carry the geometric posit honestly, as a `Prop` the instance must supply, and
are NOT dressed as proved conditions):
- `IsKahlerSector : Prop` + `kahler_condition : IsKahlerSector` : stands for
  "`Σ` carries a closed 2-form `ω` compatible with a complex structure" (the
  Kähler condition). Its **formalizable core is now genuine and consumed**: every
  `ℂℙ`-based instance supplies `IsKahlerSector := IsFubiniStudyKahler N` — the
  pointwise Fubini–Study Kähler-compatibility triple (`g = re⟪·,·⟫`,
  `ω = im⟪·,·⟫`, `J = i•·` with `J² = -1`, `ω = g∘J`, `g = ω∘J`, `ω` a `(1,1)`-form,
  `ω u (Ju) = ‖u‖²`), proved axiom-free via
  `Kahler.fubiniStudy_pointwise_kahler_compatibility` (no longer `True`). The
  **manifold** residual — closedness `dω = 0` and `ω^{∧(N-1)}/(N-1)! = μ_FS` — needs
  exterior calculus absent from Mathlib and stays the honestly-named open piece
  (connectivity link L1).
- `IsLiouvilleKahlerVolume : Prop` + `liouville_eq_kahler_volume :
  IsLiouvilleKahlerVolume` : stands for "`liouvilleMeasure` is the top-power
  Kähler volume `ω^{∧ n} / n!`". Its **formalizable core** — that the volume is
  *normalized* (a probability measure) — is now a genuine, consumed condition on
  ALL concrete instances (`unitaryFlowSetup`, `manyToOneSetup`, and the trivial
  witness `trivialKahlerOnticSetup`, each supplying `IsProbabilityMeasure`;
  `unitaryFlowSetup_liouville_isProbability` consumes it, fix C5). No instance
  supplies `True`.

Both Kähler-geometry fields now carry their genuine formalizable core; only the
**manifold** residual stays open (closedness `dω = 0` and `ω^{∧ n}/n! = μ_FS`,
needing exterior calculus absent from Mathlib). When Mathlib grows that API, the
`IsKahlerSector` predicate is the slot to strengthen from the pointwise
`IsFubiniStudyKahler` to the full closed-2-form condition; the dynamical fields are
unaffected. See `specs/connectivity-manifest.md` (link L1) and `PLACEHOLDERS.md`.
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
(`Kahler.fubiniStudy_pointwise_kahler_compatibility`). It is the genuine predicate the
concrete `ℂℙ`-based instances now supply for `IsKahlerSector`, in place of the earlier
`True`. The manifold-level closedness `dω = 0` and the top-power identity
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
`IsKahlerSector` field genuinely on every `ℂℙ`-based instance. -/
theorem isFubiniStudyKahler (N : ℕ) : IsFubiniStudyKahler N :=
  fun u v => Kahler.fubiniStudy_pointwise_kahler_compatibility u v

/-- **The Kähler ontic-sector interface (W2).** Sector-level hypotheses bundled
as structure fields (no global axioms). `N` is the operational Hilbert
dimension; the projective target `ℙ ℂ (EuclideanSpace ℂ (Fin N))` matches
Wigner's, so W3 consumes `wigner_rigidity` on `pi`-images directly.

See the module docstring for the genuine-vs-placeholder field ledger. In short:
`compact_sigma`, `liouvilleMeasure`, `pi`/`pi_measurable`, `flow`/
`flow_preserves_volume`, `projectedFlow`/`projectable` are genuine; the two
`Prop`-valued Kähler-geometry pairs (`kahler_condition`,
`liouville_eq_kahler_volume`) are honest abstract placeholders for the
symplectic/Kähler differential-form data the corpus does not yet formalise. -/
structure KahlerOnticSetup (N : ℕ) where
  /-- The ontic sector state space `Σ`. -/
  Sigma : Type*
  /-- Bundled measurable-space instance on `Σ`. -/
  [instMeasurable : MeasurableSpace Sigma]
  /-- Bundled topological-space instance on `Σ`. -/
  [instTopological : TopologicalSpace Sigma]
  /-- GENUINE: `Σ` is compact (the compact-Kähler requirement). -/
  compact_sigma : CompactSpace Sigma
  /-- ABSTRACT PLACEHOLDER: the proposition "`Σ` is a Kähler sector" (a closed
  2-form `ω` compatible with a complex structure). Supplied by the instance;
  the corpus does not yet formalise the differential-form content. -/
  IsKahlerSector : Prop
  /-- ABSTRACT PLACEHOLDER: proof of the Kähler condition. -/
  kahler_condition : IsKahlerSector
  /-- GENUINE: the Liouville / typicality measure on `Σ`. -/
  liouvilleMeasure : Measure Sigma
  /-- ABSTRACT PLACEHOLDER: the proposition "`liouvilleMeasure` is the top-power
  Kähler volume `ω^{∧ n}/n!`". Supplied by the instance. -/
  IsLiouvilleKahlerVolume : Prop
  /-- ABSTRACT PLACEHOLDER: proof that Liouville = Kähler top-power volume. -/
  liouville_eq_kahler_volume : IsLiouvilleKahlerVolume
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

/-- **Inhabitation witness (non-vacuity).** The degenerate base case
`Σ = ℙ ℂ (EuclideanSpace ℂ (Fin N))`, `π = id`, the trivial flow-family
`flow t = id`, and `liouvilleMeasure = fubiniStudyMeasure p₀`. This confirms the
`KahlerOnticSetup N` fields are mutually satisfiable (the interface is
non-empty), exactly the `π = id` base-case role `LF4.cpSectorData` plays for
`SectorData`. The two Kähler-geometry fields are supplied GENUINELY:
`IsKahlerSector := IsFubiniStudyKahler N` (the pointwise FS Kähler compatibility,
proved) and `IsLiouvilleKahlerVolume := IsProbabilityMeasure μ_FS` (the normalized-
volume core, proved) — no longer `True`; the
dynamical fields are the identity flow (`Φ = id`), so this witness carries no
dynamics (structural debt D1, as elsewhere in LF4). A genuine `Φ ≠ id`
inhabitant is available by reusing `kFlow` on `KSigma`; this witness only
certifies inhabitability. -/
noncomputable def trivialKahlerOnticSetup
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    KahlerOnticSetup N where
  Sigma := ℙ ℂ (EuclideanSpace ℂ (Fin N))
  compact_sigma := inferInstance
  IsKahlerSector := IsFubiniStudyKahler N
  kahler_condition := isFubiniStudyKahler N
  liouvilleMeasure := Matrix.UnitaryGroup.fubiniStudyMeasure p₀
  IsLiouvilleKahlerVolume := IsProbabilityMeasure (Matrix.UnitaryGroup.fubiniStudyMeasure p₀)
  liouville_eq_kahler_volume := inferInstance
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
