import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Contextuality.MerminPeres

/-!
# Empirical/CSD: Mermin–Peres magic square (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Contextuality/MerminPeres.lean`).

Pairs with `Empirical/QM/Contextuality/MerminPeres.lean` (Mermin 1990;
Peres 1990). The QM file proves `no_lhv_mermin_peres`: no
`λ : Fin 3 × Fin 3 → ℤ` taking values in `{±1}` can satisfy the six
row/column product constraints driven by the operator identities on
the 3×3 two-qubit Pauli grid (three rows all `+I`; columns
`+I, +I, −I`). Plus the six matrix-level operator identities
`mermin_peres_R0..R2, C0..C2`.

This file states the **CSD volume-ratio reading**: no global
non-contextual ontic value assignment to the 9 two-qubit Pauli
observables in the Mermin–Peres grid satisfies the row/column product
constraints required by the QM operator identities.

Under CSD, a "value assignment to a Pauli observable" corresponds, at
the ontic level, to a measurable real-valued function on `Σ` (the
§14 observable correspondence). A *non-contextual* assignment is one
that does not depend on which row vs which column the observable is
being measured in — both contexts impose simultaneous-measurability
constraints (the three operators in any single row commute, likewise
for any column), so non-contextuality is the natural minimal
hidden-variable requirement.

## Polarity

Negative-existential, matching the QM-side combinatorial impossibility
and the KS18 template.

## LF4 obligations carried

LF4-todo §14 (observable correspondence): the nine two-qubit Pauli
observables in the grid are realised through Hilbert ↔ ontic-function
correspondence. Pre-LF4 this is prose-only on the bundle; post-LF4 it
is provable from the concrete `SectorData` instantiation.

## Schema-mismatch acknowledgement

The bundle's `lambda` field carries QM-side data (an integer
assignment to the 3×3 grid). The CSD-realisability claim — that
`lambda` represents the ontic values of the nine Pauli observables
through §14 — is prose-only. See `PLACEHOLDERS.md §7`.

## Experimental verification

- Kirchmair et al. 2009 *Nature* **460**, 494 (trapped ions).
- Amselem et al. 2009 *Phys. Rev. Lett.* **103**, 160405 (photons).
- Bartosik et al. 2009 *Phys. Rev. Lett.* **103**, 040403 (neutrons).

## Source

- Mermin 1990 *Phys. Rev. Lett.* **65**, 3373.
- Peres 1990 *Phys. Lett. A* **151**, 107.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace MerminPeres

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: bundle fields are QM-side; the CSD-realisability
claim is prose-only.** See module docstring + `PLACEHOLDERS.md §7`.

**CSD Mermin–Peres assignment bundle.** Extends `CSDBridge.Context D`
with a hypothetical non-contextual `Fin 3 × Fin 3 → ℤ` value
assignment to the 9 cells of the Mermin–Peres grid, satisfying the
six row/column product constraints required by the QM operator
identities.

The fields match the argument list of
`Empirical.QM.MerminPeres.no_lhv_mermin_peres` exactly, which enables
the proof reduction in `no_csd_mermin_peres_assignment` below.

## LF4-discharge content (prose-only)

By calling the structure `CSDMerminPeresBundle`, callers implicitly
assert that the carried `lambda` represents the ontic values of the
nine two-qubit Pauli observables through the LF4-todo §14 observable
correspondence. Pre-LF4 this is structural; post-LF4 it becomes
provable from the concrete `SectorData` instantiation.

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §14. -/
structure CSDMerminPeresBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The hypothetical non-contextual value assignment. -/
  lambda    : Fin 3 → Fin 3 → ℤ
  /-- Each value is `±1`. -/
  pm        : ∀ i j, lambda i j = 1 ∨ lambda i j = -1
  /-- Row 0 product: `+1` (from `(σ_x⊗I)(I⊗σ_x)(σ_x⊗σ_x) = +I`). -/
  r0        : lambda 0 0 * lambda 0 1 * lambda 0 2 = 1
  /-- Row 1 product: `+1` (from `(I⊗σ_y)(σ_y⊗I)(σ_y⊗σ_y) = +I`). -/
  r1        : lambda 1 0 * lambda 1 1 * lambda 1 2 = 1
  /-- Row 2 product: `+1` (from `(σ_x⊗σ_y)(σ_y⊗σ_x)(σ_z⊗σ_z) = +I`). -/
  r2        : lambda 2 0 * lambda 2 1 * lambda 2 2 = 1
  /-- Column 0 product: `+1`. -/
  c0        : lambda 0 0 * lambda 1 0 * lambda 2 0 = 1
  /-- Column 1 product: `+1`. -/
  c1        : lambda 0 1 * lambda 1 1 * lambda 2 1 = 1
  /-- Column 2 product: `−1` (from `(σ_x⊗σ_x)(σ_y⊗σ_y)(σ_z⊗σ_z) = −I`,
      the load-bearing identity). -/
  c2        : lambda 0 2 * lambda 1 2 * lambda 2 2 = -1

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's QM-side fields
and calls the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**No CSD Mermin–Peres assignment bundle exists.** The CSD volume-ratio
companion to `Empirical.QM.MerminPeres.no_lhv_mermin_peres`.

Reduces to the QM-side theorem by direct field extraction: the
bundle's `lambda` + `pm` + the six product identities `r0..r2, c0..c2`
give exactly the existential the QM theorem rules out.

**Interpretation.** Under CSD, a "non-contextual value assignment"
corresponds to a choice of measurable `Σ → ℤ` functions (one per
Pauli observable in the grid) satisfying the product constraints
required by the QM operator identities. This theorem shows: such an
assignment is uninhabitable. Combined with the LF4-todo §14 observable
correspondence, CSD's ontic substrate is no more permissive of
non-contextual hidden-variable assignments to two-qubit Pauli
observables than QM is.

**Experimental verification:** Kirchmair 2009, Amselem 2009,
Bartosik 2009 (see module docstring). -/
theorem no_csd_mermin_peres_assignment
    {D : CSD.LF2.SectorData SigmaSpace P G} :
    ¬ ∃ b : CSDMerminPeresBundle D, True := by
  rintro ⟨b, _⟩
  exact CSD.Empirical.MerminPeres.no_lhv_mermin_peres
    ⟨b.lambda, b.pm, b.r0, b.r1, b.r2, b.c0, b.c1, b.c2⟩

end MerminPeres
end CSDBridge
end Empirical
end CSD
