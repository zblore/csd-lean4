/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Framework
public import CsdLean4.Empirical.QM.Uncertainty
public import CsdLean4.LF4.SingleQubitKahler

/-!
# Empirical/CSD: Robertson uncertainty relation (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Uncertainty.lean`).

Pairs with `Empirical/QM/Uncertainty.lean` (Robertson 1929). The QM file
states the bound as a pure inner-product-geometry theorem:
`Var_ψ(A) · Var_ψ(B) ≥ ¼ |⟨ψ, [A,B] ψ⟩|²` for self-adjoint `A, B`. No
CSD ontology in the proof.

This file states the **CSD volume-ratio reading**: the same inequality
applied to CSD-realised observables and a CSD-realised preparation. A
Hilbert state `ψ` corresponds to a CSD preparation (a posited fibre law
on `Σ`); each self-adjoint operator `A` corresponds to a measurable
function `Σ → ℝ` whose integral against `μψ` gives the Hilbert
expectation `⟨ψ, A ψ⟩`. Under that correspondence the Robertson bound
constrains the ontic variances.

## LF4 obligations carried (new realisability content)

The realisability content here is **different from the §13 cloning /
deletion / N-qubit-unitary bundles**: those are about isometries
realised as `Σ`-flows. Uncertainty is about *observables* — self-adjoint
operators realised as **measurable `Σ`-valued functions** whose
`μψ`-integral matches the Hilbert expectation.

This is **LF4-todo §14** (observable correspondence; added 2026-05-28).
Pre-LF4, the bundle carries the Hilbert-side data and the realisability
is prose-only. Post-LF4, the concrete `SectorData` instantiation
discharges the correspondence and the ontic variances match the
Hilbert variances by an integration identity.

See `BRIDGE-OBLIGATIONS.md` §2.4 (observable correspondence row) for the
canonical ledger entry, and `PLACEHOLDERS.md §7` for the
schema-mismatch position (the bundle's fields are Hilbert-side; the
ontic correspondence is prose-only).

## Polarity (transport, not negative-existential)

Unlike `NoCloning` / `NoDeleting` (negative-existential, "no such bundle
exists for non-orthogonal states"), Uncertainty is a positive-content
transport: every bundle satisfies the Robertson bound, by direct
appeal to the QM-side theorem. There is no inhabitability obstruction.

## Experimental verification

The uncertainty bound is checked wherever joint measurements of
non-commuting observables are performed — Stern-Gerlach in two
non-aligned directions, photon polarisation in non-orthogonal bases,
neutron interferometry. The exact lower bound `¼|⟨[A,B]⟩|²` is saturated
by minimum-uncertainty states (coherent states for position–momentum).

## Source

Robertson 1929, *Phys. Rev.* **34**, 163. Schrödinger 1930 (stronger
form with anticommutator term, not formalised here or on the QM side).
-/

@[expose] public section

open MeasureTheory ComplexConjugate

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Uncertainty

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does
not carry.** Fields are Hilbert-side; the observable-correspondence
claim is prose-only. See module docstring + `PLACEHOLDERS.md §7`.

**CSD uncertainty bundle.** Structural carrier for a pair of self-adjoint
Hilbert-space observables `A, B` and a state `ψ`, packaged in a
`SectorData D` context. Extends `CSDBridge.Context D` (the LF2-level
discharge data) and adds the Hilbert-side observable/state structure.

The fields match the argument list of
`Empirical.QM.Uncertainty.robertson_uncertainty` exactly, so the
proof reduction in `csd_robertson_uncertainty` is mechanical.

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDUncertaintyBundle`, callers implicitly
assert:

1. `ψ` arises as the Hilbert-space lift of a CSD preparation (a
   posited fibre law `μψ` on `Σ`);
2. `A, B` each arise as the Hilbert-space lift of a measurable
   real-valued function on `Σ` (the ontic observable), with
   `⟨ψ, A ψ⟩ = ∫ A_ontic dμψ` (and likewise for `B`);
3. `μψ`-variance of `A_ontic` equals Hilbert variance `Var_ψ(A)`.

Together these realise the QM-side Robertson bound at the ontic level.

**Status: ONTIC-BACKED (§14 CONNECTED 2026-07-19).** The observable correspondence
is proved in `LF4/SingleQubitKahler.lean` (`pauliDot_observable_correspondence`:
the Hilbert expectation `⟨ψ, (n·σ) ψ⟩` equals the `sgMuPsi`-integral of the ontic
observable function `pauliDotOntic`), re-exported below as
`csd_uncertainty_ontic_observable_correspondence`; the genuine volume derivation is
in `UncertaintyVolume.lean`. Honest scope: the bundle type still carries only a
`Context` (`PLACEHOLDERS.md §7`); the ontic content lives in the cited theorem.
LF4-todo §14. -/
structure CSDUncertaintyBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The Hilbert-side state. -/
  ψ        : H
  /-- The first observable. -/
  A        : Module.End ℂ H
  /-- The second observable. -/
  B        : Module.End ℂ H
  /-- `A` is self-adjoint. -/
  hA_sym   : A.IsSymmetric
  /-- `B` is self-adjoint. -/
  hB_sym   : B.IsSymmetric

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's Hilbert-side
fields and calls the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**Robertson uncertainty in the CSD reading.** For any CSD uncertainty
bundle on a `SectorData D`,
`Var_ψ(A) · Var_ψ(B) ≥ ¼ |⟨ψ, [A,B] ψ⟩|²`. Reduces to the QM-side
`Empirical.QM.Uncertainty.robertson_uncertainty` by direct field
extraction.

**Interpretation.** Under CSD, the bound constrains the joint
spread of two ontic observables on the posited fibre law `μψ`,
through the LF4-todo §14 Hilbert ↔ ontic-observable correspondence.
Pre-LF4 the ontic side is implicit in the bundle's existence; post-LF4
it is provable from the concrete `SectorData` instantiation.

**Experimental verification:** Stern-Gerlach in non-aligned
directions; polarisation in non-orthogonal bases; minimum-uncertainty
states (coherent states for `x, p`). -/
theorem csd_robertson_uncertainty
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : CSDUncertaintyBundle D H) :
    CSD.Empirical.Uncertainty.variance b.A b.ψ
        * CSD.Empirical.Uncertainty.variance b.B b.ψ
      ≥ (1 / 4) * ‖inner ℂ b.ψ ((b.A * b.B - b.B * b.A) b.ψ)‖ ^ 2 :=
  CSD.Empirical.Uncertainty.robertson_uncertainty
    b.A b.B b.hA_sym b.hB_sym b.ψ

/-- **Ontic observable correspondence (§14).** The Hilbert expectation of a spin
observable `n·σ` on `|+z⟩` equals the `sgMuPsi`-integral of its ontic observable
function `pauliDotOntic` — the observable-as-ontic-function correspondence, proved
axiom-free in `CSD.LF4.pauliDot_observable_correspondence`. Re-exported so the CSD
uncertainty reading cites its ontic derivation, not only the QM identity. -/
alias csd_uncertainty_ontic_observable_correspondence :=
  CSD.LF4.pauliDot_observable_correspondence

end Uncertainty
end CSDBridge
end Empirical
end CSD
