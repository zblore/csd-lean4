/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PovmDynamics
public import CsdLean4.RecordLayer.JoinClosure

/-!
# SigmaLayer/PovmSectorBorn: the POVM Born rule at the protocol-sector level

**Category:** dynamical measurement — `specs/BACKLOG.md` **B4**, discharging the scope
note the 2026-08-04 audit added to `PovmDynamics.lean`.

## What was wrong, and what this fixes

`povm_selector_born` was described in prose as "the **dynamical** POVM Born rule". It is
not: its statement is an `epistemicMeasure` of a **selector fibre**
`blockIndex (localBlock N K) ⁻¹' {i}` — i.e. `degenerate_selector_born` transported along
the dilation. No protocol, no propagator and no outcome *sector* appear in its type. The
corpus draws exactly this distinction in `SwapClosure.lean`:

> `sector_born` is the dynamical Born, **not** the kinematic selector Born: the measure of
> the *outcome sector* (initial states destined for record `i`) equals the Born weight.

The audit corrected the prose and recorded the sector-level lift as an extension. This
module delivers it.

★★ `povm_sector_born` — for a POVM `P`, any Naimark dilation `D`, and any block-supported
calibration, the **join protocol's outcome sector** at the dilated preparation carries
exactly `⟨ψ, Eᵢψ⟩`:

  `joinPrep (Vψ) α ((joinProtocol (localBlock N K)).outcomeSector i) = Tr(ρ… ) = ⟨ψ, Eᵢψ⟩`.

This is the *dynamical* statement — initial states destined for record `i`, under the join
protocol's own propagator — and it now earns the description the prose used to give the
selector-level one.

## Why it is short

Because the two halves already existed and only needed composing: `join_sector_born`
(`JoinClosure.lean`) does the protocol-sector work for an arbitrary block structure — the
`preimage_sector_ae` + `volume_goodTheta` spine — and `sum_block_normSq_dilate`
(`PovmDynamics.lean`) identifies the block sum at the dilated preparation with the POVM
weight. The dilation is isometric (`norm_dilateFlat`), so the unit-norm hypothesis
transports. That the lift is a two-line composition is itself the evidence that the
original defect was one of *description*, not of missing mathematics.

⚠️ **Honest scope.** (i) The instrument remains dilation-relative — a POVM does not
determine its instrument, and `PovmDynamics.lean`'s scope items (ii)–(iv) are unchanged.
(ii) Realising the isometry `V` as a unitary-plus-ancilla stroke *inside* the record
dynamics is still a recorded extension: this theorem, like the selector-level one, takes
the dilated ray `[Vψ]` as its entry point. (iii) The calibration `α` is quantified, so the
statistics cannot depend on it.

## References

`specs/BACKLOG.md` B4; `RecordLayer/PovmDynamics.lean` (`povm_selector_born`,
`sum_block_normSq_dilate`, and the scope note this discharges);
`RecordLayer/JoinClosure.lean` (`join_sector_born`, the protocol-sector template);
`RecordLayer/SwapClosure.lean` (the selector-vs-sector distinction, stated there first).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory CSD.LF2 CSD.SigmaLayer

variable {N K : ℕ} [NeZero N] [NeZero K] {P : POVM N (Fin K)}

/-- ★★ **The POVM Born rule at the protocol-sector level.** The join protocol's outcome
sector — the initial states destined for record `i` — carries exactly the POVM weight
`⟨ψ, Eᵢψ⟩` at the dilated preparation. This is the *dynamical* form that
`povm_selector_born` was mis-described as; the selector-level statement remains as the
kinematic ingredient. -/
theorem povm_sector_born (P : POVM N (Fin K)) (D : LF4.NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (α : EuclideanSpace ℂ (Fin (N * K))) (i : Fin K) :
    joinPrep (K := K) (dilateFlat D ψ) α (dilateFlat_ne_zero D hψ0)
        ((joinProtocol (N := N * K) (localBlock N K)).outcomeSector i)
      = ENNReal.ofReal (P.weight ψ i) := by
  rw [join_sector_born (localBlock N K) (dilateFlat D ψ) α (dilateFlat_ne_zero D hψ0)
      (by rw [norm_dilateFlat, hψ]) i,
    sum_block_normSq_dilate P D ψ i]

/-- ★★ **Every POVM**, via the canonical dilation. -/
theorem povm_sector_born_canonical (P : POVM N (Fin K))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (α : EuclideanSpace ℂ (Fin (N * K))) (i : Fin K) :
    joinPrep (K := K) (dilateFlat (LF4.canonicalNaimark P) ψ) α
        (dilateFlat_ne_zero (LF4.canonicalNaimark P) hψ0)
        ((joinProtocol (N := N * K) (localBlock N K)).outcomeSector i)
      = ENNReal.ofReal (P.weight ψ i) :=
  povm_sector_born P (LF4.canonicalNaimark P) ψ hψ0 hψ α i

end CSD.RecordLayer
