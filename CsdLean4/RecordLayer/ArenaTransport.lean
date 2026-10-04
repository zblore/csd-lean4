/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerDynamics
public import CsdLean4.RecordLayer.ShearDeIsolation

/-!
# The record layer transports to a de-isolation arena

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #107, out of #106's surviving route.

Rows #102–#106 are statements about `globalBasin`s of a `ContextField` under `epistemicMeasure`. The
pointer the corpus actually *constructs* lives elsewhere:
[`ShearDeIsolation.lean`](ShearDeIsolation.lean)'s outcome sectors are **preimages** of those basins
under a de-isolation propagator, on a fibred arena with its own preparation measure
(`readyPrep [ψ] = epistemicMeasure [ψ] ⊗ readyMeasure`). #107 asks for the bridge, so that the
stability and robustness results apply to the flow-carved sectors rather than to posited cells.

The bridge is one condition, and this file isolates it.

## The condition, and why it is the right one

* `ReadsEpistemic p μ Φ` — the arena's preparation measure **pushes forward** along `Φ` to the
  epistemic measure. Every statement below is a transport along that single identity, so nothing is
  assumed about the arena's type, its fibre, or its dynamics;
* ★★★ `readsEpistemic_of_measurePreserving` — **and the condition reduces to a preparation-preserving
  flow.** On a product arena `Σ × (ready register)` with a probability measure on the register, if the
  de-isolation flow `F` preserves the preparation measure then reading `Σ` after the flow reads the
  epistemic measure. That is exactly the shape `readyPrep` has and exactly the property a propagator
  is built to have, so the bridge is not an extra posit about the arena — it is measure preservation;
* ★★★ `readsEpistemic_readyPrep_of_measurePreserving` — **and the corpus's own preparation measure is
  that product.** `readyPrep p = epistemicMeasure p ⊗ readyMeasure N` literally, so for the shear arena
  the bridge is a single property of the propagator and nothing else: it preserves `readyPrep`.

## What transports

* ★ `measure_preimage_eq` — any measurable record event has the same probability in the arena as in
  `Σ`, and ★ `isProbabilityMeasure_of_readsEpistemic`: the arena's preparation is a probability
  measure for free;
* ★★ `measure_preimage_globalBasin` — **the flow-carved sector carries the Born weight**, which is the
  shape of `shear_sector_born` obtained here from the pushforward alone;
* ★★ `measure_preimage_robustBasin_ge` — the robust part of a sector is at least `rate − δ`, and
  ★★★ `one_sub_le_robust_fraction_preimage` — **#106's robust fraction holds for the flow-carved
  sector**: within the sector the realised record survives a write of size `δ` on all but `δ / rate`
  of it;
* ★★★ `measure_preimage_recordString_ne_le` — **#103's relabelling bound holds for the arena**: the
  arena's microstates whose record string a write of size `δ` changes have preparation measure at most
  `k · N · δ`.

So once the flow preserves the preparation, the record layer's stability results are statements about
the pointer the de-isolation flow produces.

## Honest scope

⚠️ **The shear propagator is not shown to satisfy this.** The corpus has the per-sector Born identity
(`shear_sector_born`) but **not** the pushforward identity, and
`readsEpistemic_readyPrep_of_measurePreserving` reduces the gap to exactly one hypothesis —
`MeasurePreserving F (readyPrep p) (readyPrep p)` for the shear propagator — which is **not proved
here**, and sits upstream of `ShearWitness` item 1 (the propagator's Hamiltonian generation is stated,
not formalised). That is BACKLOG #108, and nothing below claims the connection is made for the shear
construction specifically.

⚠️ **A pushforward is not a dynamics.** `ReadsEpistemic` says where the preparation goes, not how. No
generator, no interaction Hamiltonian, no time parameter appears, and the de-isolation obligation of
[`DeIsolationFlow.lean`](DeIsolationFlow.lean) is untouched by anything here.

⚠️ **Transport preserves scope, including the limits.** Everything carried over keeps its own
caveats: #103's bound is robustness and not invariance, #106's fraction is conditional on the realised
outcome and claims no cell is large, and the write is a translation of the record coordinate. Pulling
them back along `Φ` adds nothing and removes nothing.

⚠️ **One preparation.** The transport is stated at a fixed base point `p`; nothing here varies the
preparation or integrates over it.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `PointerDynamics.lean` (#106),
`PointerConcentration.lean` (#105(a)), `MacrostateStability.lean` (#103), `ShearDeIsolation.lean`,
`DeIsolationFlow.lean`; `specs/BACKLOG.md` #107, #108, #106, #103, #102.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ} {α : Type*} [MeasurableSpace α]

/-! ### The bridge condition -/

/-- **The arena reads the epistemic measure**: its preparation measure pushes forward along `Φ` to the
epistemic measure at `p`. One identity, and every transport below is an instance of it. -/
structure ReadsEpistemic (p : LF4.CPN N) (μ : Measure α) (Φ : α → LF4.KSigma N) : Prop where
  /-- The reading map is measurable. -/
  measurable_map : Measurable Φ
  /-- The preparation pushes forward to the epistemic measure. -/
  pushforward : μ.map Φ = epistemicMeasure p

/-- ★ **The arena's preparation is a probability measure for free.** -/
theorem isProbabilityMeasure_of_readsEpistemic {p : LF4.CPN N} {μ : Measure α}
    {Φ : α → LF4.KSigma N} (h : ReadsEpistemic p μ Φ) : IsProbabilityMeasure μ := by
  refine ⟨?_⟩
  have h1 : μ univ = (epistemicMeasure p) univ := by
    have hc := congrArg (fun ν : Measure (LF4.KSigma N) => ν univ) h.pushforward
    rwa [Measure.map_apply h.measurable_map MeasurableSet.univ, Set.preimage_univ] at hc
  rw [h1]
  exact measure_univ

/-- ★ **Every measurable record event has the same probability in the arena as in `Σ`.** -/
theorem measure_preimage_eq {p : LF4.CPN N} {μ : Measure α} {Φ : α → LF4.KSigma N}
    (h : ReadsEpistemic p μ Φ) {S : Set (LF4.KSigma N)} (hS : MeasurableSet S) :
    μ (Φ ⁻¹' S) = epistemicMeasure p S := by
  rw [← h.pushforward, Measure.map_apply h.measurable_map hS]

/-- ★★★ **The condition reduces to a preparation-preserving flow.** On a product arena
`Σ × (ready register)` whose register carries a probability measure, a de-isolation flow preserving the
preparation measure reads the epistemic measure when `Σ` is read after the flow.

This is the shape `readyPrep = epistemicMeasure ⊗ readyMeasure` has, so the bridge is not a new posit
about the arena: it is measure preservation of the propagator. -/
theorem readsEpistemic_of_measurePreserving {p : LF4.CPN N} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {F : LF4.KSigma N × β → LF4.KSigma N × β}
    (hF : MeasurePreserving F ((epistemicMeasure p).prod ν) ((epistemicMeasure p).prod ν)) :
    ReadsEpistemic p ((epistemicMeasure p).prod ν) (Prod.fst ∘ F) where
  measurable_map := measurable_fst.comp hF.measurable
  pushforward := by
    rw [← Measure.map_map measurable_fst hF.measurable, hF.map_eq]
    simp

/-- ★★★ **And the corpus's own preparation measure is that product.** `readyPrep` — the ontic
preparation of the shear arena — is `epistemicMeasure p ⊗ readyMeasure N` by definition, so a
de-isolation flow on that arena which preserves it reads the epistemic measure.

This is the bridge for the *construction* rather than for an abstract product arena: what #108 owes is
one hypothesis about the shear propagator, `MeasurePreserving F (readyPrep p) (readyPrep p)`, and
nothing further about records, cells or basins. -/
theorem readsEpistemic_readyPrep_of_measurePreserving {p : LF4.CPN N}
    {F : LF4.KSigma N × LF4.KTorus → LF4.KSigma N × LF4.KTorus}
    (hF : MeasurePreserving F (readyPrep p) (readyPrep p)) :
    ReadsEpistemic p (readyPrep p) (Prod.fst ∘ F) := by
  rw [readyPrep] at hF ⊢
  exact readsEpistemic_of_measurePreserving (readyMeasure N) hF

/-! ### What transports -/

/-- ★★ **The flow-carved sector carries the Born weight.** The shape of `shear_sector_born`, obtained
from the pushforward alone. -/
theorem measure_preimage_globalBasin {p : LF4.CPN N} {μ : Measure α} {Φ : α → LF4.KSigma N}
    (h : ReadsEpistemic p μ Φ) (c : ContextField N) (i : Fin N) :
    μ (Φ ⁻¹' globalBasin c i) = ENNReal.ofReal (c.rate p i) := by
  rw [measure_preimage_eq h (measurableSet_globalBasin c i), globalBasin_prob]

/-- ★★ **The robust part of a sector is at least `rate − δ`.** -/
theorem measure_preimage_robustBasin_ge {p : LF4.CPN N} {μ : Measure α} {Φ : α → LF4.KSigma N}
    (h : ReadsEpistemic p μ Φ) (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin N) :
    ENNReal.ofReal (c.rate p i - δ) ≤ μ (Φ ⁻¹' robustBasin c δ i) := by
  rw [measure_preimage_eq h (measurableSet_robustBasin c δ i)]
  exact measure_robustBasin_ge c hδ i p

/-- ★★★ **#106's robust fraction holds for the flow-carved sector.** Within the sector the realised
record survives a write of size `δ` on all but `δ / rate` of it — with no concentration hypothesis, as
in #106. -/
theorem one_sub_le_robust_fraction_preimage {p : LF4.CPN N} {μ : Measure α} {Φ : α → LF4.KSigma N}
    (h : ReadsEpistemic p μ Φ) (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin N)
    (hrate : 0 < c.rate p i) :
    1 - δ / c.rate p i ≤ (μ (Φ ⁻¹' robustBasin c δ i)).toReal / c.rate p i := by
  rw [measure_preimage_eq h (measurableSet_robustBasin c δ i)]
  exact one_sub_le_robust_fraction c hδ i p hrate

/-- ★★★ **#103's relabelling bound holds for the arena.** The arena's microstates whose record string
a write of size `δ` changes have preparation measure at most `k · N · δ`. -/
theorem measure_preimage_recordString_ne_le {p : LF4.CPN N} {μ : Measure α} {Φ : α → LF4.KSigma N}
    (h : ReadsEpistemic p μ Φ) {k : ℕ} (c : Fin k → ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ (Φ ⁻¹' {x | recordString c (sigmaShift δ x) ≠ recordString c x})
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ) := by
  have hmeasR : Measurable (recordString c) := measurable_recordString c
  have hshift : Measurable (fun x : LF4.KSigma N => recordString c (sigmaShift δ x)) :=
    hmeasR.comp (measurable_sigmaShift δ)
  have heq : {x : LF4.KSigma N | recordString c (sigmaShift δ x) = recordString c x}
      = ⋃ v : Fin k → Fin (N + 1),
          ((fun x => recordString c (sigmaShift δ x)) ⁻¹' {v}) ∩ (recordString c ⁻¹' {v}) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨recordString c x, hx, rfl⟩, fun ⟨v, h1, h2⟩ => h1.trans h2.symm⟩
  have hmeasEq : MeasurableSet
      {x : LF4.KSigma N | recordString c (sigmaShift δ x) = recordString c x} := by
    rw [heq]
    exact MeasurableSet.iUnion fun v =>
      (hshift (measurableSet_singleton v)).inter (hmeasR (measurableSet_singleton v))
  have hmeas : MeasurableSet
      {x : LF4.KSigma N | recordString c (sigmaShift δ x) ≠ recordString c x} := by
    rw [show {x : LF4.KSigma N | recordString c (sigmaShift δ x) ≠ recordString c x}
        = {x : LF4.KSigma N | recordString c (sigmaShift δ x) = recordString c x}ᶜ from by
      ext x
      simp]
    exact hmeasEq.compl
  rw [measure_preimage_eq h hmeas]
  exact measure_recordString_ne_le c hδ p

end CSD.RecordLayer

end
