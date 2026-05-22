import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.NoCloning

/-!
# Empirical/CSD: No-cloning theorem (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/NoCloning.lean`).

Pairs with `Empirical/QM/NoCloning.lean` (Wootters-Zurek 1982 / Dieks
1982). The QM file states no-cloning as a pure linear-algebra theorem
on an abstract tensor structure: given an isometry `U : Htensor → Htensor`
that clones two unit states from a fixed blank, `⟨ψ, φ⟩ ∈ {0, 1}`. No
CSD ontology in the proof.

This file states the **CSD volume-ratio reading**: no cloning operation
realisable through CSD's ontic substrate (a measure-preserving
π-equivariant flow on `Σ × Σ` projecting to a Hilbert-space isometry
on the tensor space) can clone two non-orthogonal non-equal unit
states from the same blank.

## Polarity inversion vs Bell

Unlike `Empirical/CSD/Bell.lean` (whose bundle *enables* a positive
frequency-convergence claim via the LF3 chain capstones), the cloning
bundle *would assert* something forbidden: the existence of an
isometry doing the cloning. The headline theorem refutes the bundle's
inhabitability for non-orthogonal non-equal states.

This is the first negative-existential CSD-side reading in the
corpus. The bundle template still matches `PureSingletPreparation`
(extends `CSDBridge.Context D`, carries phenomenon-specific fields)
but the theorem's conclusion is `¬ ∃ b : CSDCloningBundle ...` rather
than the positive frequency-convergence statement Bell uses.

## LF4 obligations carried

The bundle's load-bearing LF4-discharge content is the **realisability
of the cloning isometry through the CSD ontic substrate**: that the
Hilbert-space `U` carried by the bundle arises as the projective-action
lift of a measure-preserving π-equivariant flow on `Σ × Σ`. This is
**LF4-todo §13** (added 2026-05-21 in the same change-set that lands
this file, per the bridge-discipline rules at the top of
`specs/LF4-todo.md`).

Pre-LF4, the bundle's Hilbert-side data (tensor structure, isometry,
cloning identities) matches the QM-side `no_universal_cloner_of_witness`
argument list exactly, and the CSD-vs-QM distinction is in the
*meaning* of constructing a `CSDCloningBundle`: implicitly, callers
commit to the LF4-todo §13 realisability of the bundle's components.
Post-LF4, the `Context D`'s ontic substrate makes that realisability
provable from a measure-preserving symplectomorphism.

See `BRIDGE-OBLIGATIONS.md` §2.2 for the canonical ledger row.

## Proof strategy

The headline theorem `no_csd_cloning_bundle` reduces to the QM-side
`Empirical.QM.NoCloning.no_universal_cloner_of_witness` by direct
field extraction. The bundle's `tensor`, `h_tensor_inner`, `blank`,
`h_blank_unit`, `ψ`, `φ`, `hψ`, `hφ`, `U`, `U_isometry`, `clone_ψ`,
`clone_φ` line up one-for-one with the QM theorem's arguments.

The reduction is honest about the CSD-vs-QM relationship: if a CSD
substrate could realise cloning, the QM theorem says it cannot
because the realisation would yield a Hilbert-space isometry with
the cloning property, which QM forbids.

## Experimental verification

Same as the QM-side file: Lamas-Linares et al. 2002,
*Science* **296**, 712 (optimal approximate cloning bound 5/6
saturated; the exact bound `< 1` follows from this theorem).

## Honest reading

This file states the CSD-no-cloning theorem and reduces it to QM. It
does **not** establish "the CSD ontic substrate forbids cloning by an
independent ontic-level argument"; that would require formalising
no-cloning natively in CSD's volume-ratio terms (multi-week LF2
expansion, deferred). The reduction-via-QM approach is the right
shape for a Cat-3 empirical-prediction file pre-LF4: CSD reproduces
QM at the projective level (via the bundle's `Context D`), and QM
forbids cloning, so CSD forbids cloning at the projective level.

Post-LF4, the `Context D`'s ontic substrate can be made concrete, and
the realisability obligation in LF4-todo §13 becomes provable rather
than externally supplied. The headline theorem here is then strictly
stronger than just a "transport of QM no-cloning to CSD", because it
also carries the LF4 realisability content.
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge
namespace NoCloning

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does not carry.**

The fields below — `tensor`, `h_tensor_inner`, `blank`, `h_blank_unit`,
`ψ`, `φ`, `hψ`, `hφ`, `U`, `U_isometry`, `clone_ψ`, `clone_φ` — are
**all QM-side data**. No field carries a `Σ × Σ` flow, no field asserts
`π`-equivariance, no field asserts measure-preservation. The
"projective-action lift of a measure-preserving π-equivariant flow on
`Σ × Σ`" claim below is **non-syntactic prose**; Lean cannot check it.

See `PLACEHOLDERS.md §7` for the canonical schema-mismatch ledger.

## Original (over-claiming) docstring follows

**CSD cloning bundle.** Structural carrier for the data of a
hypothetical cloning operation realised through CSD's ontic substrate
on a `SectorData D`. The bundle extends `CSDBridge.Context D` (carrying
the LF2-level discharge data: `μFS`, the probability witness, the
measure bridge) and adds the Hilbert-side cloning structure.

The fields match the argument list of
`Empirical.QM.NoCloning.no_universal_cloner_of_witness` exactly,
which is what enables the proof reduction in
`no_csd_cloning_bundle` below.

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDCloningBundle`, callers implicitly assert
that the carried `U` arises as the projective-action lift of a
measure-preserving π-equivariant flow on `Σ × Σ` for the bundle's
`SectorData D`. Pre-LF4 this is asserted at construction site;
post-LF4, it follows from the concrete Kähler instantiation
discharging LF4-todo §13.

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §13.

(The above "status" applies to the *prose claim*, not to any field of
this structure. See `PLACEHOLDERS.md §7` discharge route for the
fields that would need to be added for the type to actually carry the
CSD-side claim.) -/
structure CSDCloningBundle
    (D : CSD.LF2.SectorData SigmaSpace P G) (N : ℕ)
    (Htensor : Type*) [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The abstract tensor pairing. Matches the QM-side signature. -/
  tensor          : EuclideanSpace ℂ (Fin N) → EuclideanSpace ℂ (Fin N) → Htensor
  /-- Inner-product factorisation across the tensor pairing. -/
  h_tensor_inner  :
    ∀ a b c d : EuclideanSpace ℂ (Fin N),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d
  /-- The fixed "blank" state from which cloning starts. -/
  blank           : EuclideanSpace ℂ (Fin N)
  h_blank_unit    : ‖blank‖ = 1
  /-- The two unit states the bundle attempts to clone. -/
  ψ               : EuclideanSpace ℂ (Fin N)
  φ               : EuclideanSpace ℂ (Fin N)
  hψ              : ‖ψ‖ = 1
  hφ              : ‖φ‖ = 1
  /-- The Hilbert-space cloning isometry. -/
  U               : Htensor → Htensor
  /-- `U` preserves the inner product. -/
  U_isometry      : ∀ x y : Htensor, inner ℂ (U x) (U y) = inner ℂ x y
  /-- `U` clones `ψ` from `blank`. -/
  clone_ψ         : U (tensor ψ blank) = tensor ψ ψ
  /-- `U` clones `φ` from `blank`. -/
  clone_φ         : U (tensor φ blank) = tensor φ φ

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's QM-side fields
and calls the QM-side theorem.** See `PLACEHOLDERS.md §7` (the bundle
this quantifies over is a schema-mismatch bundle, so the proof can
only consume QM-side content).

**No CSD cloning bundle exists for non-orthogonal non-equal unit
states.** The CSD volume-ratio companion to
`Empirical.QM.NoCloning.no_cloning_two_state`.

Reduces to the QM-side
`Empirical.QM.NoCloning.no_universal_cloner_of_witness` by direct
extraction of the bundle's Hilbert-side fields. The bundle carries
those fields one-for-one with the QM theorem's argument list, so the
reduction is mechanical.

**Interpretation.** Under CSD, a "cloning operation" is a
measure-preserving π-equivariant flow on `Σ × Σ → Σ × Σ` whose
projective lift to the tensor Hilbert space is an isometry with the
cloning property. This theorem shows: such a bundle is uninhabitable
for non-orthogonal non-equal unit states. Combined with the LF4-todo
§13 realisability discharge, this establishes that CSD's ontic
substrate is no more permissive of cloning than QM is.

**Experimental verification:** Lamas-Linares et al. 2002,
*Science* **296**, 712. -/
theorem no_csd_cloning_bundle
    {D : CSD.LF2.SectorData SigmaSpace P G} {N : ℕ}
    {Htensor : Type*} [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
    {ψ φ : EuclideanSpace ℂ (Fin N)}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h_neither : inner ℂ ψ φ ≠ 0 ∧ inner ℂ ψ φ ≠ 1) :
    ¬ ∃ b : CSDCloningBundle D N Htensor, b.ψ = ψ ∧ b.φ = φ := by
  rintro ⟨b, hbψ, hbφ⟩
  apply CSD.Empirical.NoCloning.no_universal_cloner_of_witness
    b.tensor b.h_tensor_inner b.blank b.h_blank_unit ψ φ hψ hφ h_neither
  refine ⟨b.U, b.U_isometry, ?_, ?_⟩
  · rw [← hbψ]; exact b.clone_ψ
  · rw [← hbφ]; exact b.clone_φ

end NoCloning
end CSDBridge
end Empirical
end CSD
