/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable structure on projectivization

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidates).

Under `[RCLike K]` and finite-dimensional normed `V`, the projectivization
`ℙ K V` carries a canonical Borel `MeasurableSpace` structure derived from
its quotient topology (`Topology.lean`). This file installs:

- `Projectivization.instMeasurableSpace`: the Borel σ-algebra from the
  quotient topology.
- `Projectivization.instBorelSpace`: witness that the installed
  measurable space coincides with `borel _` (definitionally `rfl`).
- `Projectivization.instMeasurableSingletonClass`: every singleton is
  measurable, from `T2Space` (closed singletons) + `BorelSpace`.
- `Projectivization.measurable_mk'`: the canonical surjection is
  measurable, from its continuity (`Topology.lean`'s `continuous_mk'`)
  via `Continuous.measurable`.
- `Projectivization.borel_eq_map_mk'`: the Borel σ-algebra on `ℙ K V`
  equals the coinduced σ-algebra `MeasurableSpace.map mk' (borel V₀)`.
  Mathlib's `Continuous.map_borel_eq` (Polish.Basic) discharges this
  given `PolishSpace` on the nonzero subtype (via `IsOpen.polishSpace`).
- `Projectivization.lift_measurable`: a scale-invariant measurable
  function on `{v : V // v ≠ 0}` descends to a measurable function on
  `ℙ K V`. Load-bearing user-facing lemma for LF4 §3 + §8.
- `Projectivization.measurable_iff_measurable_comp_mk'`: a function
  out of `ℙ K V` is measurable iff its precomposition with `mk'` is.

## Provenance

Staged as upstream Mathlib material. All declarations live under
`namespace Projectivization` with no `CsdLean4`-namespace prefix; the
file is intended to land in
`Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` once usage
stabilises. Discharges items 4.1–4.6 of `specs/projectivization-plan.md`
(the full `MeasureSpace.lean` mathematical scope).

## Hypothesis pattern

`[RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]`,
matching the `Topology.lean` `NormedFiniteDim` section. Under these
hypotheses, `ℙ K V` is a compact Hausdorff space; the Borel σ-algebra is
the natural measurable structure. `lift_measurable` and
`measurable_iff_measurable_comp_mk'` additionally take
`[MeasurableSpace V] [BorelSpace V]` so the source subtype
`{v : V // v ≠ 0}` inherits a Borel structure via `Subtype.borelSpace`
that agrees with the Mathlib-canonical `borel _` (callers typically
`borelize V`).

## Tags

projectivization, projective space, Borel measurable space,
quotient measurable space, scale-invariant measurable function
-/

@[expose] public section

open MeasureTheory Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]

/-- Second-countability of `Projectivization K V`. Free consequence of
the open-quotient-map structure (`Topology.lean`'s `isOpenMap_mk'` +
`isQuotientMap_mk'`) and second-countability of the source: `V` is
second-countable (finite-dim normed over `RCLike` is proper via
`FiniteDimensional.proper_rclike`, and proper metric spaces are
second-countable via `secondCountable_of_proper`), so the open subtype
`{v : V // v ≠ 0}` is second-countable
(`Subtype.secondCountableTopology`), and the open quotient map carries
that to `ℙ K V` (`Topology.IsQuotientMap.secondCountableTopology`). -/
instance instSecondCountableTopology : SecondCountableTopology (ℙ K V) := by
  haveI : ProperSpace V := FiniteDimensional.proper_rclike K V
  exact isQuotientMap_mk'.secondCountableTopology isOpenMap_mk'

/-- The Borel σ-algebra on `Projectivization K V`, derived from its
quotient topology (`Topology.lean`).

Gated on `[RCLike K]` and finite-dim normed `V` so it does not shadow
the generic `Quotient.instMeasurableSpace` in algebraic-geometry
contexts (where `K` is an abstract field and the analytic structure is
not relevant). -/
instance instMeasurableSpace : MeasurableSpace (ℙ K V) := borel _

/-- `Projectivization K V` is a `BorelSpace`: the installed measurable
space agrees with `borel _` by definition. -/
instance instBorelSpace : BorelSpace (ℙ K V) := ⟨rfl⟩

/-- Singletons in `ℙ K V` are measurable. Follows from T2 (closed
singletons; established in `Topology.lean`'s
`Projectivization.instT2Space`) plus the Borel structure (closed sets
are measurable). -/
instance instMeasurableSingletonClass : MeasurableSingletonClass (ℙ K V) :=
  ⟨fun _ => (isClosed_singleton).measurableSet⟩

omit [FiniteDimensional K V] in
/-- The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is measurable.
Follows from continuity (`Topology.lean`'s `continuous_mk'`) via
`Continuous.measurable`.

Stated under additional `[MeasurableSpace V] [BorelSpace V]` hypotheses
so the source subtype `{v : V // v ≠ 0}` inherits a Borel `MeasurableSpace`
via `Subtype.borelSpace`. Most callers will supply these (typically via
`borelize V`); the resulting `MeasurableSpace V` agrees with `borel V`. -/
theorem measurable_mk' [MeasurableSpace V] [BorelSpace V] :
    Measurable (mk' K : { v : V // v ≠ 0 } → ℙ K V) :=
  continuous_mk'.measurable

/-! ### Coincidence of Borel and coinduced σ-algebras

The key fact underwriting `lift_measurable`: under `[RCLike K]` +
finite-dim normed `V`, the Borel σ-algebra on `ℙ K V` (the one
installed as `instMeasurableSpace`) coincides with the σ-algebra
obtained by pushing the Borel σ-algebra on `{v : V // v ≠ 0}` along
`mk'`. Mathlib's `Continuous.map_borel_eq` (`Polish.Basic`) discharges
this given `PolishSpace` on the source.

`PolishSpace V` is automatic for finite-dim normed `V` over `[RCLike K]`
(separable + completely metrizable). The subtype `{v : V // v ≠ 0}` is
open in `V` (complement of the closed singleton `{0}`), hence Polish
via `IsOpen.polishSpace`. -/

/-- The Borel σ-algebra on `ℙ K V` coincides with the σ-algebra
coinduced from the Borel σ-algebra on `{v : V // v ≠ 0}` via `mk'`.

This is the coincidence lemma: it lets `lift_measurable` (below) reduce
measurability of `Projectivization.lift f hf` (against the Borel
σ-algebra) to measurability of `f` (against the Borel σ-algebra on the
nonzero subtype). Without this lemma, the two σ-algebras might differ
and `measurable_from_quotient` (which works with the coinduced version)
would not suffice.

`V` is Polish under our hypotheses (`ProperSpace V` via
`FiniteDimensional.proper_rclike` gives second-countable + complete +
metrizable, hence Polish via the `Mathlib.Topology.MetricSpace.Polish`
`PolishSpace` instance for separable + completely metrizable). The
nonzero subtype is open in `V`, hence also Polish via
`IsOpen.polishSpace`. -/
theorem borel_eq_map_mk' :
    MeasurableSpace.map
      (mk' K : { v : V // v ≠ 0 } → ℙ K V)
      (borel _) = borel (ℙ K V) := by
  haveI : ProperSpace V := FiniteDimensional.proper_rclike K V
  haveI : PolishSpace V := inferInstance
  haveI : PolishSpace ({ v : V // v ≠ 0 }) :=
    isClosed_singleton.isOpen_compl.polishSpace
  exact continuous_mk'.map_borel_eq Quot.mk_surjective

/-! ### `lift_measurable` and the measurability characterisation -/

/-- A scale-invariant measurable function on the nonzero subtype
descends to a measurable function on `ℙ K V`. Routes the measurability
of `Projectivization.lift f hf` through the coincidence lemma
`borel_eq_map_mk'`.

Hypotheses: `f : {v : V // v ≠ 0} → α` is `K`-scale-invariant
(`hf`, the same hypothesis required by `Projectivization.lift`); `f`
is measurable for the Borel σ-algebra on the nonzero subtype (callers
typically supply `[MeasurableSpace V] [BorelSpace V]` so this is the
natural σ-algebra).

This is the **load-bearing user-facing lemma for LF4 §3 + §8** — it
lets callers build measurable functions on `ℙ K V` from measurable
scale-invariant functions on `V \ {0}`, which is how preparations
encode rep-maps in the LF2 / LF3 chain. -/
theorem lift_measurable [MeasurableSpace V] [BorelSpace V]
    {α : Type*} [MeasurableSpace α]
    (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (hf_meas : Measurable f) :
    Measurable (Projectivization.lift f hf) := by
  intro B hB
  -- `mk' ⁻¹' (lift f hf ⁻¹' B) = f ⁻¹' B` (by `Projectivization.lift_mk`, definitionally).
  have h_preimg :
      (mk' K : _ → ℙ K V) ⁻¹' (Projectivization.lift f hf ⁻¹' B) = f ⁻¹' B := by
    ext ⟨v, hv⟩; rfl
  -- `f ⁻¹' B` is Borel-measurable in V₀ (by hf_meas), hence so is the preimage form.
  -- The subtype's `Subtype.instMeasurableSpace` coincides with `borel _` via
  -- `Subtype.borelSpace` (since `[BorelSpace V]` is in scope).
  haveI : BorelSpace ({ v : V // v ≠ 0 }) := Subtype.borelSpace _
  have h_meas :
      @MeasurableSet { v : V // v ≠ 0 } (borel _)
        ((mk' K : _ → ℙ K V) ⁻¹' (Projectivization.lift f hf ⁻¹' B)) := by
    rw [← ‹BorelSpace ({ v : V // v ≠ 0 })›.measurable_eq, h_preimg]
    exact hf_meas hB
  -- Transport `h_meas` along `borel_eq_map_mk'`. By definition of `MeasurableSpace.map`,
  -- `MeasurableSet[map mk' (borel V₀)] S` is `MeasurableSet[borel V₀] (mk' ⁻¹' S)`
  -- (via `MeasurableSpace.map_def`, which is `Iff.rfl`).
  have h1 : @MeasurableSet (ℙ K V)
              (MeasurableSpace.map (mk' K : _ → ℙ K V) (borel _))
              (Projectivization.lift f hf ⁻¹' B) :=
    MeasurableSpace.map_def.mpr h_meas
  rwa [borel_eq_map_mk'] at h1

/-- A function out of `ℙ K V` is measurable iff its precomposition with
`mk'` is measurable. Companion to `lift_measurable` for the case where
the function is already defined on `ℙ K V` (rather than constructed via
`Projectivization.lift`). -/
theorem measurable_iff_measurable_comp_mk' [MeasurableSpace V] [BorelSpace V]
    {α : Type*} [MeasurableSpace α] (g : ℙ K V → α) :
    Measurable g ↔ Measurable (g ∘ (mk' K : _ → ℙ K V)) := by
  refine ⟨fun hg => hg.comp measurable_mk', fun hg => ?_⟩
  intro B hB
  -- Same coincidence-lemma transport as `lift_measurable`.
  haveI : BorelSpace ({ v : V // v ≠ 0 }) := Subtype.borelSpace _
  have h_subtype :
      @MeasurableSet { v : V // v ≠ 0 } (borel _) ((mk' K : _ → ℙ K V) ⁻¹' (g ⁻¹' B)) := by
    rw [← ‹BorelSpace ({ v : V // v ≠ 0 })›.measurable_eq]
    exact hg hB
  have h1 : @MeasurableSet (ℙ K V)
              (MeasurableSpace.map (mk' K : _ → ℙ K V) (borel _))
              (g ⁻¹' B) :=
    MeasurableSpace.map_def.mpr h_subtype
  rwa [borel_eq_map_mk'] at h1

end Projectivization
