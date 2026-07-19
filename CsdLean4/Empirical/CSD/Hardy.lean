import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Hardy
import CsdLean4.LF4.HardyKahler

/-!
# Empirical/CSD: Hardy's 9% paradox (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Hardy.lean`).

Pairs with `Empirical/QM/Hardy.lean` (Hardy 1992; Hardy 1993). The QM
file proves the combinatorial LHV impossibility `no_lhv_hardy`: no
non-negative weight assignment `p : Fin 2 × Fin 2 × Fin 2 × Fin 2 → ℝ`
on the four-observable outcome quadruples (Alice's `A`, `A'`; Bob's
`B`, `B'`) satisfies the four Hardy constraints simultaneously:

- `P(A=1, B=1) > 0` (positive coincidence);
- `P(A=1, B'=0) = 0`;
- `P(A'=0, B=1) = 0`;
- `P(A'=1, B'=1) = 0`.

(Plus the QM realisation: a specific 2-qubit state achieves these four
probabilities; the maximum-probability variant attains the closed-form
golden-ratio value `(5√5 − 11)/2 ≈ 0.0902`.)

This file states the **CSD volume-ratio reading**: no global ontic
weight assignment over the four-observable outcome quadruples can
satisfy the four Hardy constraints. Under CSD, a weight `p(x)` for
an outcome quadruple `x` corresponds to a `μψ`-measure of the joint
event "Alice measures `A → x.1`, `A' → x.2.1`; Bob measures `B → x.2.2.1`,
`B' → x.2.2.2`" through the §14 observable correspondence on the four
single-qubit Pauli observables.

## Polarity

Negative-existential, matching the QM-side combinatorial impossibility
and the KS18 / Mermin–Peres templates.

## LF4 obligations carried

LF4-todo §14 (observable correspondence): the four single-qubit Pauli
observables `A`, `A'`, `B`, `B'` are realised through Hilbert ↔
ontic-function correspondence. Pre-LF4 this is prose-only on the
bundle; post-LF4 it is provable from the concrete `SectorData`
instantiation.

## Schema-mismatch acknowledgement

The bundle's `p` field is QM-side data (a non-negative weight
assignment on `Outcome`). The CSD-realisability claim — that `p`
represents the joint `μψ`-measure of the outcome quadruples through
the §14 observable correspondence — is prose-only. See
`PLACEHOLDERS.md §7`.

## Experimental verification

- Lundeen, Steinberg 2009 *Phys. Rev. Lett.* **102**, 020404
  (photonic Hardy test; ~9% paradoxical coincidence rate observed).
- Aharonov et al. 2002, Resch et al. 2004 (weak-value tests).

## Source

- Hardy 1992 *Phys. Rev. Lett.* **68**, 2981.
- Hardy 1993 *Phys. Rev. Lett.* **71**, 1665 (golden-ratio maximum).
-/

open Finset

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Hardy

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: bundle fields are QM-side; the CSD-realisability
claim is prose-only.** See module docstring + `PLACEHOLDERS.md §7`.

**CSD Hardy assignment bundle.** Extends `CSDBridge.Context D` with a
hypothetical non-negative weight assignment on the four-observable
outcome quadruples, satisfying the four Hardy probability constraints
required by the QM realisation. The fields match the argument list of
`Empirical.QM.Hardy.no_lhv_hardy` exactly, enabling the proof
reduction in `no_csd_hardy_assignment` below.

## LF4-discharge content (prose-only)

By calling the structure `CSDHardyBundle`, callers implicitly assert:
the carried `p` represents the joint `μψ`-measure of outcome
quadruples for Alice's `A`, `A'` and Bob's `B`, `B'` Pauli observables
through the LF4-todo §14 observable correspondence.

**Status: ONTIC-BACKED (§14 CONNECTED 2026-07-19).** The four Alice/Bob joint
observable correspondences are proved in `LF4/HardyKahler.lean`
(`hardy_observable_correspondence_{AB, AB'minus, A'minus_B, A'_B'}`: each Hilbert
joint expectation equals its ontic-measure value), re-exported below; the genuine
volume derivation is in `HardyVolume.lean`. Honest scope: the bundle type still
carries only a `Context` (`PLACEHOLDERS.md §7`); the ontic content lives in the cited
theorems.
LF4-todo §14. -/
structure CSDHardyBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The hypothetical non-negative weight assignment on outcome
      quadruples. -/
  p              : CSD.Empirical.Hardy.Outcome → ℝ
  /-- Non-negativity. -/
  p_nonneg       : ∀ x, 0 ≤ p x
  /-- Hardy constraint 1: `P(A=1, B=1) > 0` (positive coincidence). -/
  hardy_AB_pos   :
    0 < (∑ x ∈ univ.filter
            (fun x : CSD.Empirical.Hardy.Outcome => x.1 = 1 ∧ x.2.2.1 = 1), p x)
  /-- Hardy constraint 2: `P(A=1, B'=0) = 0`. -/
  hardy_AB'_zero :
    (∑ x ∈ univ.filter
            (fun x : CSD.Empirical.Hardy.Outcome => x.1 = 1 ∧ x.2.2.2 = 0), p x) = 0
  /-- Hardy constraint 3: `P(A'=0, B=1) = 0`. -/
  hardy_A'B_zero :
    (∑ x ∈ univ.filter
            (fun x : CSD.Empirical.Hardy.Outcome => x.2.1 = 0 ∧ x.2.2.1 = 1), p x) = 0
  /-- Hardy constraint 4: `P(A'=1, B'=1) = 0`. -/
  hardy_A'B'_zero :
    (∑ x ∈ univ.filter
            (fun x : CSD.Empirical.Hardy.Outcome => x.2.1 = 1 ∧ x.2.2.2 = 1), p x) = 0

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's QM-side fields
and calls the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**No CSD Hardy assignment bundle exists.** The CSD volume-ratio
companion to `Empirical.QM.Hardy.no_lhv_hardy`.

Reduces to the QM-side theorem by direct field extraction: the
bundle's `p`, `p_nonneg`, and the four Hardy constraints give exactly
the existential the QM theorem rules out.

**Interpretation.** Under CSD, a "weight assignment to outcome
quadruples" corresponds to the `μψ`-measure of joint events for the
four Alice/Bob Pauli observables, through the §14 observable
correspondence. This theorem shows: no such assignment can satisfy
the four Hardy constraints simultaneously. Combined with the LF4-todo
§14 realisability discharge, CSD's ontic substrate is no more
permissive of Hardy-style non-contextual assignments than QM is.

**Experimental verification:** Lundeen-Steinberg 2009 (~9% paradoxical
coincidences observed); cf. the golden-ratio max `(5√5 − 11)/2 ≈ 0.0902`
on the QM side. -/
theorem no_csd_hardy_assignment
    {D : CSD.LF2.SectorData SigmaSpace P G} :
    ¬ ∃ _b : CSDHardyBundle D, True := by
  rintro ⟨b, _⟩
  exact CSD.Empirical.Hardy.no_lhv_hardy
    ⟨b.p, b.p_nonneg, b.hardy_AB_pos, b.hardy_AB'_zero,
     b.hardy_A'B_zero, b.hardy_A'B'_zero⟩

/-! ### Genuine ontic backing (§14 CONNECTED 2026-07-19)

The four Alice/Bob joint observable correspondences for the Hardy configuration are
proved axiom-free in `LF4/HardyKahler.lean`; re-exported here so the CSD Hardy reading
cites its ontic derivation. Each states the Hilbert joint expectation equals the
corresponding ontic-measure value. -/

/-- Ontic correspondence for the `A·B` observable (§14). -/
alias csd_hardy_ontic_correspondence_AB := CSD.LF4.hardy_observable_correspondence_AB
/-- Ontic correspondence for the `A·B'` observable (§14). -/
alias csd_hardy_ontic_correspondence_AB'minus :=
  CSD.LF4.hardy_observable_correspondence_AB'minus
/-- Ontic correspondence for the `A'·B` observable (§14). -/
alias csd_hardy_ontic_correspondence_A'minus_B :=
  CSD.LF4.hardy_observable_correspondence_A'minus_B
/-- Ontic correspondence for the `A'·B'` observable (§14). -/
alias csd_hardy_ontic_correspondence_A'_B' := CSD.LF4.hardy_observable_correspondence_A'_B'

end Hardy
end CSDBridge
end Empirical
end CSD
