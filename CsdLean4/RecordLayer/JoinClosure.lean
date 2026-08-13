/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.JoinLuders
public import CsdLean4.RecordLayer.RecordPersistence

/-!
# SigmaLayer/JoinClosure: the degenerate one-protocol package

**Category:** dynamical measurement — the degenerate counterpart of
`SwapMeasurementClosure`/`UnifiedArenaClosure`, requested by the fourth external review
(2026-08-03): the degenerate pieces existed as theorems on the join protocol but had never
been packaged as **one closure on one protocol**.

★★ **`degenerateMeasurementClosure`** — for every block structure `b` and preparation `ψ`,
the join protocol simultaneously carries:

* **ready ⇒ no record**, **record created** (the outcome the selector had fixed),
  **outcomes exclusive**, **record persists** across the operational window — the standard
  record architecture, all fields proved of the constructed propagator;
* **Liouville preservation** of the join arena measure at every time pair;
* ★ **the coarse dynamical Born mass** (`join_sector_born`, new here): the outcome-`i`
  sector of the canonical join preparation carries exactly the block Born weight
  `∑_{j : b j = i} ‖⟨eⱼ, ψ⟩‖²` — and the mass is independent of the ancilla calibration;
* **the ψ-dependent degenerate Lüders update** (`joinWitness_blockLuders`): conditioning
  on outcome `i` relocates the system to `epistemicMeasure [Πᵢψ]`.

The spine of `join_sector_born`: the preparation pulls the sector back to a cylinder over
the good system fibres (`preimage_sector_ae`), whose Haar volume is a **Dirac slice** of
the selector Born theorem — `volume (goodTheta) = epistemicMeasure [ψ] (blockIndex⁻¹ i)`
(`volume_goodTheta`), evaluated by `degenerate_selector_born`.

⚠️ **Honest scope.** The Born mass is stated at the **canonical join preparation**
(`joinPrep`: phase-orbit join point, Haar fibres, ready register) — the same preparation
the Lüders theorem conditions; the calibration vector `α` is quantified, so the statistics
provably cannot leak the calibration. The i.i.d. frequency layer is not restated: it
consumes any probability measure and event and applies verbatim. The rank-one specialisation
(`K = N`, `b = id`) is the swap closure's territory and is not duplicated here.

## References

`specs/BACKLOG.md` (the degenerate one-protocol package row — this discharges it; fourth
external review 2026-08-03); `SigmaLayer/DegenerateLuders.lean`
(`degenerate_selector_born`, `BlockLudersObligation`), `SigmaLayer/JoinProtocol.lean`
(`joinProtocol`, `join_correlates`, `join_pointerInvariant`,
`joinEvolve_measurePreserving`), `SigmaLayer/JoinLuders.lean` (`joinPrep`, `goodTheta`,
`preimage_sector_ae`, `joinWitness_blockLuders`), `SigmaLayer/SwapClosure.lean`
(`SwapMeasurementClosure`, the rank-one precedent), `SigmaLayer/MeasurementCapstone.lean`
(whose `degenerate` field this upgrades).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N K : ℕ} [NeZero N]

/-! ### ★ The coarse Born mass of the good fibres -/

/-- **The good-fibre volume is the block Born weight** — the Dirac slice of
`degenerate_selector_born`: `epistemicMeasure [ψ] = δ_{[ψ]} ⊗ Haar`, so the selector-Born
mass IS the Haar volume of the good system fibres. -/
lemma volume_goodTheta {b : Fin N → Fin K} {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin K) :
    (volume : Measure LF4.KTorus) (goodTheta b ψ hψ0 i)
      = ENNReal.ofReal (∑ j ∈ Finset.univ.filter (fun j => b j = i),
          ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) := by
  have h := degenerate_selector_born b ψ hψ0 hψ i
  rw [epistemicMeasure, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left
      (measurable_blockIndex b (measurableSet_singleton i))] at h
  exact h

/-- ★ **The coarse dynamical Born mass on the join protocol**: the canonical join
preparation gives the outcome-`i` sector exactly the block Born weight — independently of
the ancilla calibration `α`, which the statement quantifies. -/
theorem join_sector_born (b : Fin N → Fin K) (ψ α : EuclideanSpace ℂ (Fin N))
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin K) :
    joinPrep (K := K) ψ α hψ0 ((joinProtocol (N := N) b).outcomeSector i)
      = ENNReal.ofReal (∑ j ∈ Finset.univ.filter (fun j => b j = i),
          ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) := by
  have hready : readyMeasure K (readyArc K) = 1 :=
    ProbabilityTheory.cond_apply_self volume_readyArc_ne_zero (measure_ne_top _ _)
  rw [joinPrep, Measure.map_apply (measurable_jF ψ α hψ0)
      ((joinProtocol b).outcomeSector_measurable i),
    measure_congr (preimage_sector_ae b ψ α hψ0 i),
    paramMeasure, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, hready, one_mul, mul_one, mul_one]
  exact volume_goodTheta hψ0 hψ i

/-! ### ★★ The package -/

/-- **The degenerate measurement package, on one protocol** — what the fourth external
review asked for: ready/record/exclusivity/persistence, Liouville preservation, the coarse
dynamical Born mass, and the ψ-dependent degenerate Lüders update, all carried by the join
protocol for the block structure `b`. -/
structure DegenerateMeasurementClosure (b : Fin N → Fin K)
    (ψ : EuclideanSpace ℂ (Fin N)) : Prop where
  /-- **Ready ⇒ no record.** -/
  ready_no_record : ∀ x : JoinSel N × LF4.KTorus, x.2 ∈ readyArc K →
    (joinProtocol (N := N) b).readout x = none
  /-- **A record is created**, and it is the outcome the hidden selector had fixed. -/
  record_created : ∀ (i : Fin K) (x : JoinSel N × LF4.KTorus),
    x ∈ selReady (joinIdx b) i →
    (joinProtocol b).readout ((joinProtocol b).evolve 0 1 x) = some i
  /-- Distinct outcomes are exclusive. -/
  outcomes_exclusive :
    Pairwise (Function.onFun Disjoint (joinProtocol (N := N) b).outcomeSector)
  /-- **The record persists** across the operational window. -/
  record_persists : ∀ (i : Fin K) (x : JoinSel N × LF4.KTorus)
    (t : CSD.SigmaLayer.OnticTime),
    x ∈ (joinProtocol b).outcomeSector i → 1 ≤ t → t ≤ 1 + 1 →
    (joinProtocol b).readout ((joinProtocol b).evolve 0 t x) = some i
  /-- **The full propagator preserves the join arena Liouville measure.** -/
  liouville : ∀ (p₀ : LF4.CPN (N + N)) (s t : CSD.SigmaLayer.OnticTime),
    MeasurePreserving (joinEvolve (N := N) b s t)
      (joinArenaMeasure p₀) (joinArenaMeasure p₀)
  /-- **★ The coarse dynamical Born mass**, calibration-independent. -/
  sector_born : ∀ (hψ0 : ψ ≠ 0) (α : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → ∀ i : Fin K,
    joinPrep (K := K) ψ α hψ0 ((joinProtocol b).outcomeSector i)
      = ENNReal.ofReal (∑ j ∈ Finset.univ.filter (fun j => b j = i),
          ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
  /-- **The ψ-dependent degenerate Lüders update**, from a fixed block-supported
  calibration family, through Liouville-preserving dynamics. -/
  luders : ∀ (α : Fin K → EuclideanSpace ℂ (Fin N)),
    (∀ i, blockProj b i (α i) = α i) →
    ∀ (hψ0 : ψ ≠ 0) (i : Fin K) (h : blockProj b i ψ ≠ 0),
    joinPostMarg b α ψ hψ0 i
      = epistemicMeasure (Projectivization.mk ℂ (blockProj b i ψ) h)

/-- ★★ **The degenerate one-protocol package holds** — for every block structure and every
preparation, with the correlation and pointer-invariance proved of the constructed
propagator, never assumed. -/
theorem degenerateMeasurementClosure (b : Fin N → Fin K)
    (ψ : EuclideanSpace ℂ (Fin N)) : DegenerateMeasurementClosure b ψ where
  ready_no_record _ hx := (joinProtocol b).readout_ready_eq_none hx
  record_created i _ hx :=
    (joinProtocol b).readout_evolve_outcomeSector (join_correlates (b := b) i hx)
  outcomes_exclusive := (joinProtocol b).outcomeSector_pairwiseDisjoint
  record_persists _ _ _ hx ht₁ ht₂ :=
    (joinProtocol b).readout_persists_on_interval (join_pointerInvariant (b := b))
      hx ht₁ ht₂
  liouville p₀ s t := joinEvolve_measurePreserving p₀ b s t
  sector_born hψ0 α hψ i := join_sector_born b ψ α hψ0 hψ i
  luders α hα hψ0 i h := joinWitness_blockLuders (b := b) α hα ψ hψ0 i h

end CSD.RecordLayer
