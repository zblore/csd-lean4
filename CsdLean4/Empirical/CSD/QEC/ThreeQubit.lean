import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.QEC.ThreeQubit

/-!
# Empirical/CSD: the three-qubit bit-flip code (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/QEC/ThreeQubit.lean`).

Pairs with the QM-validity bit-flip code (Shor 1995). The QM file proves error correction
as pure matrix algebra: stabilisers fix the codespace, the discretised Pauli errors give
distinct syndromes, and each `X` is self-inverse (recovery). This file states the **CSD
reading** — but the ontic content is subtler than "a flow off the codespace", and getting
it right is what makes QEC the corpus's sharpest pointer at the dynamics layer.

- **The codespace is a sub-surface of `Σ`.** The `+1` joint eigenspace of the stabilisers
  is a 2-dimensional subspace of `ℂ⁸`, i.e. a `ℂℙ¹ ⊂ ℂℙ⁷` inside the ontic `Σ = ℂℙ⁷` of
  the three-qubit register — a *constraint surface within the constraint surface*.
- **The physical error is decoherence, which is volume flow — not a volume-preserving flow
  on the system alone.** A *coherent* (stray-unitary) error would be a symplectomorphism of
  `Σ_sys` (volume-preserving, no information lost). But the dominant error is the system
  **entangling with the environment**, `|ψ_L⟩|e₀⟩ ↦ Σ_E (E|ψ_L⟩)|e_E⟩`: the *joint* flow
  on `Σ_sys × Σ_env` is volume-preserving (Liouville — the `hΦ_pres` field), while the
  system **marginal** spreads as its coherence leaks into system–environment correlation.
  That is the "volume loss": lost *from the system to the environment*, conserved jointly.
  The Pauli errors `{I, X₁, X₂, X₃}` formalised on the QM side are the **discretised**
  representation of this channel (the QEC discretisation theorem), not coherent rotations.
- **The syndrome measurement is the entropy-extraction step** — the part that actually
  undoes decoherence. Measuring the stabilisers reads the environment's "which-error"
  record, *re-concentrating* the system's spread reduced state back to a pure state in one
  branch; the unitary recovery afterwards is the easy, volume-preserving return to the
  codespace. The four syndrome weights *are* the decoherence probabilities, and each is a
  sum of two computational-basis Fubini–Study volumes (a coarse-graining of the general-`N`
  Born-from-volume result at `N = 8`): "syndrome statistics as Kähler volumes."

So the honest ontic statement of QEC needs the environment `Σ_env`, the joint Liouville
flow, and partial trace — i.e. **CPTP channels** (the QI-infrastructure keystone, not yet
built). The error model *is* a channel and the "volume loss" *is* the partial-trace step.
The theorem below is therefore a **transport** of the discretised correctness statement; the
genuinely-ontic content (decoherence as system→environment volume flow, syndrome as the
recovery of that volume) is the load-bearing realisability obligation, gated on channels +
the dynamical-origin (`Φ ≠ id`) layer, and not proved here.

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
codespace is a sub-surface of `Σ`, the error is **decoherence** (system→environment volume
flow, Liouville-conserved on the joint `Σ_sys × Σ_env`), the syndrome measurement extracts
the environment's record and re-concentrates the system, and recovery is the unitary return
to the codespace.

**Status: load-bearing, externally supplied, undischarged.** The ontic realisation needs
`Σ_env`, the joint Liouville flow, and partial trace — i.e. CPTP channels — plus the
dynamical-origin (`Φ ≠ id`) layer that is `id` in every concrete instance today. The error
model *is* a channel and the "volume loss" *is* the partial-trace step. See the module
docstring, `BRIDGE-OBLIGATIONS.md`, and `PLACEHOLDERS.md §7`. -/
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
    ∧ Function.Injective CSD.Empirical.QM.QEC.errorSyndrome
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
