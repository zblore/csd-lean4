/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Resources.SuperdenseCoding

/-!
# Empirical/CSD: superdense coding (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Resources/SuperdenseCoding.lean`).

Pairs with the QM-side file (Bennett-Wiesner 1992). The QM file proves
the four encoding identities `(I⊗I)|Φ⁺⟩ = |Φ⁺⟩`, `(X⊗I)|Φ⁺⟩ = |Ψ⁺⟩`,
`(Z⊗I)|Φ⁺⟩ = |Φ⁻⟩`, `(XZ⊗I)|Φ⁺⟩ = −|Ψ⁻⟩` and the ten-conjunct
`bell_basis_orthonormal`. Together these give the two-classical-bits
content: the four single-qubit operations on Alice's half of a Bell
pair carry `|Φ⁺⟩` to four orthonormal Bell states, perfectly
distinguishable by a Bell-basis measurement on Bob's side.

This file states the **CSD volume-ratio reading**: under CSD's ontic
substrate, each two-qubit encoding unitary is realised as a
measure-preserving π-equivariant flow on `Σ²` (LF4-todo §13.2), and
the Bell-basis measurement is realised through the §14 observable
correspondence on the four Bell projectors. The protocol's two-bit
content lifts to the ontic level.

## Polarity (transport, tag bundle)

Parameter-free numerical content (specific encoding identities + the
orthonormality theorem). The bundle is a **tag bundle** like
`SternGerlach`: extends `CSDBridge.Context D` with no new fields; its
existence is the load-bearing realisability assertion.

## LF4 obligations carried

- **§13.2** (general N-qubit unitary realised as Σ-flow): for the
  three encoding unitaries `X⊗I`, `Z⊗I`, `XZ⊗I` (acting on the 2-qubit
  tensor space).
- **§14** (observable correspondence): for the four Bell-state
  projectors used in Bob's measurement.

Both are extant LF4-todo obligations; the bundle does not introduce
new ones.

## Schema-mismatch acknowledgement

Bundle fields are Hilbert-side only (in fact, no fields beyond
`Context D`). The CSD-realisability claim is prose-only; Lean does
not check it. See `PLACEHOLDERS.md §7`.

## Experimental verification

Mattle, Weinfurter, Kwiat, Zeilinger 1996 *Phys. Rev. Lett.* **76**,
4656 (first experimental superdense coding with polarisation-entangled
photons).

## Source

Bennett and Wiesner 1992, *Phys. Rev. Lett.* **69**, 2881.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace SuperdenseCoding

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: tag bundle; no fields beyond `Context D`.**
See module docstring + `PLACEHOLDERS.md §7`.

**CSD superdense-coding bundle.** Extends `CSDBridge.Context D` with
no additional fields. Its *existence* is the load-bearing assertion
that:

1. The three encoding unitaries `X⊗I`, `Z⊗I`, `XZ⊗I` on the 2-qubit
   tensor space are realised as measure-preserving π-equivariant
   flows on `Σ²` (LF4-todo §13.2);
2. The four Bell-state projectors are realised as ontic observables
   through the §14 observable correspondence.

Together these underwrite the protocol's two-classical-bits-per-qubit
content at the ontic level.

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §13.2 + §14. -/
structure CSDSuperdenseCodingBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D

/-! ### Transport-only encoding identities (CSD reading)

Each theorem below transports a QM-side superdense-coding encoding
identity through the bundle. Foundational triple only. -/

variable {D : CSD.LF2.SectorData SigmaSpace P G}

/-- **CSD `(I⊗I)|Φ⁺⟩ = |Φ⁺⟩` (trivial encoding, two-bit message `00`).**
Transported from `Empirical.QM.SuperdenseCoding.encode_I`. -/
theorem csd_sdc_encode_I (_b : CSDSuperdenseCodingBundle D) :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 4) (Fin 4) ℂ))
        CSD.Empirical.QM.Gates.qmKetPhiPlus
      = CSD.Empirical.QM.Gates.qmKetPhiPlus :=
  CSD.Empirical.QM.SuperdenseCoding.encode_I

/-- **CSD `(X⊗I)|Φ⁺⟩ = |Ψ⁺⟩` (encoding two-bit message `01`).**
Transported from `Empirical.QM.SuperdenseCoding.encode_X`. -/
theorem csd_sdc_encode_X (_b : CSDSuperdenseCodingBundle D) :
    (Matrix.toEuclideanLin CSD.Empirical.QM.SuperdenseCoding.pauliX_tensor_I)
        CSD.Empirical.QM.Gates.qmKetPhiPlus
      = CSD.Empirical.QM.SuperdenseCoding.qmKetPsiPlus :=
  CSD.Empirical.QM.SuperdenseCoding.encode_X

/-- **CSD `(Z⊗I)|Φ⁺⟩ = |Φ⁻⟩` (encoding two-bit message `10`).**
Transported from `Empirical.QM.SuperdenseCoding.encode_Z`. -/
theorem csd_sdc_encode_Z (_b : CSDSuperdenseCodingBundle D) :
    (Matrix.toEuclideanLin CSD.Empirical.QM.SuperdenseCoding.pauliZ_tensor_I)
        CSD.Empirical.QM.Gates.qmKetPhiPlus
      = CSD.Empirical.QM.SuperdenseCoding.qmKetPhiMinus :=
  CSD.Empirical.QM.SuperdenseCoding.encode_Z

/-- **CSD `(XZ⊗I)|Φ⁺⟩ = −|Ψ⁻⟩` (encoding two-bit message `11`; phase
`−1` does not affect orthogonality).** Transported from
`Empirical.QM.SuperdenseCoding.encode_XZ`. -/
theorem csd_sdc_encode_XZ (_b : CSDSuperdenseCodingBundle D) :
    (Matrix.toEuclideanLin CSD.Empirical.QM.SuperdenseCoding.pauliXZ_tensor_I)
        CSD.Empirical.QM.Gates.qmKetPhiPlus
      = -CSD.Empirical.QM.SuperdenseCoding.qmKetPsiMinus :=
  CSD.Empirical.QM.SuperdenseCoding.encode_XZ

/-- **CSD Bell-basis orthonormality** (perfect distinguishability).
The ten-conjunct theorem: six pairwise-orthogonality identities + four
unit-norm identities. Transported from
`Empirical.QM.SuperdenseCoding.bell_basis_orthonormal`. -/
theorem csd_sdc_bell_basis_orthonormal (_b : CSDSuperdenseCodingBundle D) :
    inner ℂ CSD.Empirical.QM.Gates.qmKetPhiPlus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPsiPlus = (0 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.Gates.qmKetPhiPlus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPhiMinus = (0 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.Gates.qmKetPhiPlus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPsiMinus = (0 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.SuperdenseCoding.qmKetPsiPlus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPhiMinus = (0 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.SuperdenseCoding.qmKetPsiPlus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPsiMinus = (0 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.SuperdenseCoding.qmKetPhiMinus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPsiMinus = (0 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.Gates.qmKetPhiPlus
        CSD.Empirical.QM.Gates.qmKetPhiPlus = (1 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.SuperdenseCoding.qmKetPsiPlus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPsiPlus = (1 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.SuperdenseCoding.qmKetPhiMinus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPhiMinus = (1 : ℂ) ∧
    inner ℂ CSD.Empirical.QM.SuperdenseCoding.qmKetPsiMinus
        CSD.Empirical.QM.SuperdenseCoding.qmKetPsiMinus = (1 : ℂ) :=
  CSD.Empirical.QM.SuperdenseCoding.bell_basis_orthonormal

end SuperdenseCoding
end CSDBridge
end Empirical
end CSD
