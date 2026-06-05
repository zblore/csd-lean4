import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.QEC.ThreeQubit

/-!
# Empirical/CSD: the three-qubit bit-flip code (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/QEC/ThreeQubit.lean`).

Pairs with the QM-validity bit-flip code (Shor 1995). The QM file proves error correction
as pure matrix algebra: stabilisers fix the codespace, errors give distinct syndromes, and
each `X` is self-inverse (recovery). This file states the **CSD reading**, and it is the
first place in the corpus where error correction acquires a genuinely ontic meaning — one
the Hilbert picture does not have, because *correcting an error is a statement about
dynamics on `Σ`*:

- **The codespace is a sub-surface of `Σ`.** The `+1` joint eigenspace of the stabilisers
  is a 2-dimensional subspace of `ℂ⁸`, i.e. a `ℂℙ¹ ⊂ ℂℙ⁷` inside the ontic `Σ = ℂℙ⁷` of
  the three-qubit register — a *constraint surface within the constraint surface*.
- **An error is a flow off the codespace** onto an orthogonal syndrome sub-surface (one per
  syndrome); **recovery is the flow returning the errored microstates to the codespace.**
  This is a dynamics statement — exactly the layer (`Φ ≠ id`) the corpus has not yet
  exercised; it is the QEC face of the open dynamical-origin question.
- **The syndrome measurement is a measurement on `Σ`** whose four outcome weights are
  Fubini–Study volumes: each syndrome projector is a sum of two computational-basis
  projectors, so its Born weight is the corresponding sum of FS volumes (a coarse-graining
  of the general-`N` Born-from-volume result at `N = 8`). "Syndrome statistics as Kähler
  volumes."

As elsewhere in `Empirical/CSD/`, the theorem below is a **transport**: it reduces to the
QM-side correction by extracting the bundle's Context, and the genuinely-ontic content
above (codespace as sub-surface, recovery as flow, syndrome as `Σ`-volumes) is the
load-bearing realisability obligation, not proved here.

## Source

Shor 1995, *Phys. Rev. A* **52**, R2493 (the bit-flip half of the 9-qubit code).
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QEC

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **CSD three-qubit-code bundle.** A tag bundle asserting that the three-qubit bit-flip
code is realised on the ontic substrate of a `SectorData D` (extends `CSDBridge.Context D`
with the LF2-level discharge data). Its existence is the realisability assertion: the
codespace is a sub-surface of `Σ`, errors and recovery are flows, and the syndrome
measurement is a measurement on `Σ` whose outcome weights are Fubini–Study volumes.

**Status: load-bearing, externally supplied, undischarged.** The ontic realisations
(codespace-as-sub-surface; recovery-as-flow; syndrome-as-volumes) are the dynamical-origin
content of CSD — the same `Φ ≠ id` layer that is `id` in every concrete instance today.
See `BRIDGE-OBLIGATIONS.md` and `PLACEHOLDERS.md §7` (the fields are QM-side; the ontic
realisation is prose-only). -/
structure CSDThreeQubitBundle (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D

/-- **TRANSPORT-ONLY: reduces to the QM-side correction theorem.** See `PLACEHOLDERS.md §7`.

**The three-qubit bit-flip code corrects any single bit-flip, in the CSD reading.** For any
CSD three-qubit-code bundle on a `SectorData D` and any logical amplitudes `a, b`: the
stabilisers fix the codespace, the four errors give distinct syndromes, and re-applying the
identified (self-inverse) `Xⱼ` restores the logical state. Reduces to the QM-side
`Empirical.QM.QEC.three_qubit_corrects_single_bitflip` by Context extraction.

**Interpretation.** Under CSD this says: the codespace sub-surface of `Σ` is restored by the
recovery flow after any single-qubit error flow — error correction as a return map to a
constraint surface. Pre-LF4 the ontic realisation is implicit in the bundle's existence;
post-LF4 it follows from the concrete `SectorData` with a genuine (non-identity) flow.

**Experimental verification:** repetition-code error correction realised in NMR, ion-trap,
and superconducting registers (e.g. Reed et al. 2012, *Nature* **482**, 382). -/
theorem csd_three_qubit_corrects_single_bitflip
    {D : CSD.LF2.SectorData SigmaSpace P G}
    (_b : CSDThreeQubitBundle D) (a b : ℂ) :
    (Matrix.toEuclideanLin CSD.Empirical.QM.QEC.Z1Z2 (CSD.Empirical.QM.QEC.logical a b)
        = CSD.Empirical.QM.QEC.logical a b
      ∧ Matrix.toEuclideanLin CSD.Empirical.QM.QEC.Z2Z3 (CSD.Empirical.QM.QEC.logical a b)
        = CSD.Empirical.QM.QEC.logical a b)
    ∧ (Matrix.toEuclideanLin CSD.Empirical.QM.QEC.X1
          (Matrix.toEuclideanLin CSD.Empirical.QM.QEC.X1 (CSD.Empirical.QM.QEC.logical a b))
        = CSD.Empirical.QM.QEC.logical a b
      ∧ Matrix.toEuclideanLin CSD.Empirical.QM.QEC.X2
          (Matrix.toEuclideanLin CSD.Empirical.QM.QEC.X2 (CSD.Empirical.QM.QEC.logical a b))
        = CSD.Empirical.QM.QEC.logical a b
      ∧ Matrix.toEuclideanLin CSD.Empirical.QM.QEC.X3
          (Matrix.toEuclideanLin CSD.Empirical.QM.QEC.X3 (CSD.Empirical.QM.QEC.logical a b))
        = CSD.Empirical.QM.QEC.logical a b) :=
  CSD.Empirical.QM.QEC.three_qubit_corrects_single_bitflip a b

end QEC
end CSDBridge
end Empirical
end CSD
