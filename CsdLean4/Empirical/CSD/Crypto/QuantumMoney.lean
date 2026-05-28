import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Crypto.QuantumMoney

/-!
# Empirical/CSD: Wiesner quantum money (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Crypto/QuantumMoney.lean`).

Pairs with the QM-side file (Wiesner 1983). The QM file proves
`quantum_money_unforgeable`: over any tensor structure with the
inner-product factorisation, no isometry can forge (clone) both Wiesner
money states `|0⟩` and `|+⟩` against the same blank. The proof reduces
to `no_universal_cloner_of_witness` via the proved non-orthogonality
`⟨0|+⟩ = 1/√2 ∉ {0, 1}`.

This file states the **CSD volume-ratio reading**: no forging operation
realisable through CSD's ontic substrate (a measure-preserving
π-equivariant flow on `Σ²` projecting to a Hilbert-space isometry on
the tensor space) can duplicate both Wiesner money states against a
fixed blank.

The Wiesner unforgeability is the security root of quantum money;
combined with the CSD no-cloning reading (`Empirical/CSD/NoCloning.lean`),
it transports cleanly to the CSD substrate.

## Polarity (negative-existential, parameterised bundle)

Like `NoCloning` and `NoDeleting`, the CSD-side theorem is negative-
existential: no such forging bundle exists for the (fixed)
non-orthogonal Wiesner state pair. The bundle carries the tensor
structure and blank as parameters (matching the QM theorem's argument
list).

## LF4 obligations carried

Same realisability content as `NoCloning` / `NoDeleting`: the bundle's
Hilbert-space `U` arises as the projective-action lift of a
measure-preserving π-equivariant flow on `Σ × Σ` for the bundle's
`SectorData D`. **LF4-todo §13.1** (cloning case; the same physical
realisability — a forging isometry IS a cloning isometry on the
specific state pair `(|0⟩, |+⟩)`).

## Schema-mismatch acknowledgement

Bundle fields are QM-side; the CSD-realisability claim is prose-only.
See `PLACEHOLDERS.md §7`.

## Experimental verification

Bartkiewicz et al. 2017 *Phys. Rev. Lett.* **118**, 030501 (experimental
demonstration of Wiesner-style quantum money with photonic states;
upper bound on forgery probability consistent with no-cloning).

## Source

Wiesner 1983, *SIGACT News* **15**(1), 78. Unforgeability via
Wootters-Zurek 1982 / Dieks 1982 no-cloning.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QuantumMoney

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: bundle fields are QM-side; the
CSD-realisability claim is prose-only.** See module docstring +
`PLACEHOLDERS.md §7`.

**CSD quantum-money bundle.** Carries the tensor structure and blank
needed to state a hypothetical forging isometry for the Wiesner money
states `|0⟩` and `|+⟩`. Extends `CSDBridge.Context D` with the
QM-side parameters (mirroring the argument list of
`Empirical.QM.QuantumMoney.quantum_money_unforgeable`).

The two Wiesner states (`ket0`, `ketPlus`) are FIXED — they live in the
imported QM module — so the bundle carries only the tensor structure
and blank, not the states themselves.

## LF4-discharge content (prose-only)

By calling the structure `CSDQuantumMoneyBundle`, callers implicitly
assert: the carried `U` arises as the projective-action lift of a
measure-preserving π-equivariant flow on `Σ × Σ` for the bundle's
`SectorData D`. **Status: load-bearing, externally supplied,
undischarged.** LF4-todo §13.1. -/
structure CSDQuantumMoneyBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (Htensor : Type*) [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The abstract tensor pairing on the single-qubit money space. -/
  tensor          : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) → Htensor
  /-- Inner-product factorisation across the tensor pairing. -/
  h_tensor_inner  :
    ∀ a b c d : EuclideanSpace ℂ (Fin 2),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d
  /-- The fixed "blank" qubit from which the forger attempts cloning. -/
  blank           : EuclideanSpace ℂ (Fin 2)
  h_blank_unit    : ‖blank‖ = 1
  /-- The hypothetical forging isometry. -/
  U               : Htensor → Htensor
  /-- `U` preserves the inner product. -/
  U_isometry      : ∀ x y : Htensor, inner ℂ (U x) (U y) = inner ℂ x y
  /-- `U` clones the `|0⟩` money state. -/
  forge_ket0      : U (tensor CSD.Empirical.QuantumMoney.ket0 blank)
                      = tensor CSD.Empirical.QuantumMoney.ket0
                               CSD.Empirical.QuantumMoney.ket0
  /-- `U` clones the `|+⟩` money state. -/
  forge_ketPlus   : U (tensor CSD.Empirical.QuantumMoney.ketPlus blank)
                      = tensor CSD.Empirical.QuantumMoney.ketPlus
                               CSD.Empirical.QuantumMoney.ketPlus

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's Hilbert-side
fields and calls the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**No CSD quantum-money forging bundle exists.** The CSD volume-ratio
companion to `Empirical.QM.QuantumMoney.quantum_money_unforgeable`.

Reduces to the QM-side theorem by direct field extraction:
the bundle's `U_isometry`, `forge_ket0`, `forge_ketPlus` give exactly
the existential the QM theorem rules out.

**Interpretation.** Under CSD, a "forging operation" is a
measure-preserving π-equivariant flow on `Σ × Σ → Σ × Σ` whose
projective lift to the tensor Hilbert space is an isometry cloning the
Wiesner money states. This theorem shows: such a bundle is uninhabitable.
Combined with the LF4-todo §13.1 realisability discharge, CSD's ontic
substrate is no more permissive of quantum-money forgery than QM is.

**Experimental verification:** Bartkiewicz et al. 2017,
*Phys. Rev. Lett.* **118**, 030501. -/
theorem no_csd_quantum_money_forger
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {Htensor : Type*} [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor] :
    ¬ ∃ _b : CSDQuantumMoneyBundle D Htensor, True := by
  rintro ⟨b, _⟩
  exact CSD.Empirical.QuantumMoney.quantum_money_unforgeable
    b.tensor b.h_tensor_inner b.blank b.h_blank_unit
    ⟨b.U, b.U_isometry, b.forge_ket0, b.forge_ketPlus⟩

end QuantumMoney
end CSDBridge
end Empirical
end CSD
