/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.NoDeleting

/-!
# Empirical/CSD: No-deleting theorem (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/NoDeleting.lean`).

Pairs with `Empirical/QM/NoDeleting.lean` (Pati-Braunstein 2000). The QM
file states no-deleting as a pure linear-algebra theorem on an abstract
tensor structure: if an isometry `U : Htensor → Htensor` deletes the
second copy of two unit states `ψ, φ` against a fixed blank `e0`, then
`⟨ψ, φ⟩ ∈ {0, 1}`. No CSD ontology in the proof.

This file states the **CSD volume-ratio reading**: no deletion operation
realisable through CSD's ontic substrate (a measure-preserving
π-equivariant flow on `Σ × Σ` projecting to a Hilbert-space isometry on
the tensor space) can delete a copy of two non-orthogonal non-equal
unit states against the same blank.

The logical dual of `Empirical/CSD/NoCloning.lean` and a direct sibling
of its template.

## LF4 obligations carried

Same realisability content as `NoCloning.lean`: the bundle's
Hilbert-space `U` arises as the projective-action lift of a
measure-preserving π-equivariant flow on `Σ × Σ`. This is **LF4-todo
§13.3** (deletion case, parallel to §13.1 cloning).

Pre-LF4, the bundle's Hilbert-side data matches the QM-side
`no_universal_deleter_of_witness` argument list exactly. Post-LF4, the
`Context D`'s ontic substrate makes the realisability provable from a
measure-preserving symplectomorphism.

See `BRIDGE-OBLIGATIONS.md` §2.2 (deletion row) for the canonical ledger
entry.

## Schema-mismatch acknowledgement

Following the NoCloning template's honesty discipline: the bundle's
fields below — `tensor`, `h_tensor_inner`, `blank`, `h_blank_unit`,
`ψ`, `φ`, `hψ`, `hφ`, `U`, `U_isometry`, `delete_ψ`, `delete_φ` — are
all QM-side data. No field carries a `Σ × Σ` flow, no field asserts
π-equivariance, no field asserts measure-preservation. The
"projective-action lift of a measure-preserving π-equivariant flow on
`Σ × Σ`" claim is **non-syntactic prose**; Lean cannot check it.

See `PLACEHOLDERS.md §7` for the canonical schema-mismatch ledger.

## Experimental verification

Pati-Braunstein 2000 *Nature* **404**, 164. The no-deleting bound
underwrites the information-conservation reading of quantum erasure
experiments (e.g. Scully-Englert-Walther 1991, Kim et al. 2000): exact
deletion of an unknown state would violate the bound.
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge
namespace NoDeleting

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does
not carry.** Fields are QM-side; the CSD-realisability claim is
prose-only. See module docstring + `PLACEHOLDERS.md §7`.

**CSD deletion bundle.** Structural carrier for the data of a
hypothetical deletion operation realised through CSD's ontic substrate
on a `SectorData D`. The bundle extends `CSDBridge.Context D` (carrying
the LF2-level discharge data: `μFS`, the probability witness, the
measure bridge) and adds the Hilbert-side deletion structure.

The fields match the argument list of
`Empirical.QM.NoDeleting.no_universal_deleter_of_witness` exactly,
which enables the proof reduction in `no_csd_deleting_bundle` below.

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDDeletingBundle`, callers implicitly assert
that the carried `U` arises as the projective-action lift of a
measure-preserving π-equivariant flow on `Σ × Σ` for the bundle's
`SectorData D`. Pre-LF4 this is asserted at construction site; post-LF4
it follows from the concrete Kähler instantiation discharging
LF4-todo §13.3.

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §13.3. -/
structure CSDDeletingBundle
    (D : CSD.LF2.SectorData SigmaSpace P G) (N : ℕ)
    (Htensor : Type*) [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The abstract tensor pairing. Matches the QM-side signature. -/
  tensor          : EuclideanSpace ℂ (Fin N) → EuclideanSpace ℂ (Fin N) → Htensor
  /-- Inner-product factorisation across the tensor pairing. -/
  h_tensor_inner  :
    ∀ a b c d : EuclideanSpace ℂ (Fin N),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d
  /-- The fixed "blank" state used as the deletion target. -/
  blank           : EuclideanSpace ℂ (Fin N)
  h_blank_unit    : ‖blank‖ = 1
  /-- The two unit states the bundle attempts to delete a copy of. -/
  ψ               : EuclideanSpace ℂ (Fin N)
  φ               : EuclideanSpace ℂ (Fin N)
  hψ              : ‖ψ‖ = 1
  hφ              : ‖φ‖ = 1
  /-- The Hilbert-space deletion isometry. -/
  U               : Htensor → Htensor
  /-- `U` preserves the inner product. -/
  U_isometry      : ∀ x y : Htensor, inner ℂ (U x) (U y) = inner ℂ x y
  /-- `U` deletes the second copy of `ψ` against `blank`. -/
  delete_ψ        : U (tensor ψ ψ) = tensor ψ blank
  /-- `U` deletes the second copy of `φ` against `blank`. -/
  delete_φ        : U (tensor φ φ) = tensor φ blank

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's QM-side fields and
calls the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**No CSD deletion bundle exists for non-orthogonal non-equal unit
states.** The CSD volume-ratio companion to
`Empirical.QM.NoDeleting.no_deleting_two_state`.

Reduces to the QM-side
`Empirical.QM.NoDeleting.no_universal_deleter_of_witness` by direct
extraction of the bundle's Hilbert-side fields. Mechanical.

**Interpretation.** Under CSD, a "deletion operation" is a
measure-preserving π-equivariant flow on `Σ × Σ → Σ × Σ` whose
projective lift to the tensor Hilbert space is an isometry with the
deletion property. This theorem shows: such a bundle is uninhabitable
for non-orthogonal non-equal unit states. Combined with the LF4-todo
§13.3 realisability discharge, CSD's ontic substrate is no more
permissive of deletion than QM is.

**Experimental verification:** Pati-Braunstein 2000, *Nature* **404**,
164. The exact bound `< 1` on deletion fidelity for unknown states
follows immediately. -/
theorem no_csd_deleting_bundle
    {D : CSD.LF2.SectorData SigmaSpace P G} {N : ℕ}
    {Htensor : Type*} [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
    {ψ φ : EuclideanSpace ℂ (Fin N)}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h_neither : inner ℂ ψ φ ≠ 0 ∧ inner ℂ ψ φ ≠ 1) :
    ¬ ∃ b : CSDDeletingBundle D N Htensor, b.ψ = ψ ∧ b.φ = φ := by
  rintro ⟨b, hbψ, hbφ⟩
  apply CSD.Empirical.NoDeleting.no_universal_deleter_of_witness
    b.tensor b.h_tensor_inner b.blank b.h_blank_unit ψ φ hψ hφ h_neither
  refine ⟨b.U, b.U_isometry, ?_, ?_⟩
  · rw [← hbψ]; exact b.delete_ψ
  · rw [← hbφ]; exact b.delete_φ

end NoDeleting
end CSDBridge
end Empirical
end CSD
