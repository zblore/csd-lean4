/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ArenaTransport

/-!
# The shear propagator reads the epistemic measure — and why, which is not what #108 recorded

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #108, out of #107.

#107 reduced the record-layer-to-arena bridge to one hypothesis about the de-isolation propagator and
recorded two routes to it. Route (i) was: build the shear propagator explicitly and prove it
**preserves `readyPrep`**.

**That route is refuted here, and the bridge holds anyway.**

## Why the recorded route fails

A record *is* the pointer leaving the ready arc for a pointer arc. The shear propagator is built to do
exactly that, and `shearProtocol`'s own `ready_disjoint_pointer` says the two arcs are disjoint. So
★★★ `not_measurePreserving_shearEvolve_readyPrep`: the propagator **cannot** preserve `readyPrep` —
the ready region has `readyPrep` measure `1` and its preimage has measure `0`. Route (i) was not
unfinished; it asked for the negation of the construction's purpose.

(`shear_measurePreserving` is not a counterexample to this: it preserves `μ ⊗ volume`, the *unconditioned*
Haar measure on the register. `readyPrep` conditions on the ready arc, and conditioning is what the
shift destroys.)

## What is true instead, and it discharges #108

* ★★★ `readsEpistemic_of_fst_eq` — **a propagator that does not move the system reads the epistemic
  measure.** No measure preservation, no hypothesis on the register: if `(F x).1 = x.1` then reading
  `Σ` after `F` pushes the preparation forward to `epistemicMeasure p`;
* ★★★ `readsEpistemic_readyPrep_fst` and ★★★ `readsEpistemic_shearEvolve` — **the shear propagator
  satisfies it**, at every pair of times, because the shear moves only the pointer. So #107's
  `ReadsEpistemic` holds for the constructed propagator and every transport in `ArenaTransport.lean`
  applies to it:
* ★★ `readyPrep_preimage_globalBasin` — the transported basin carries the Born weight;
  ★★★ `readyPrep_outcomeSector_eq_preimage_globalBasin` — **and it is the same weight the flow-carved
  outcome sector carries** (`shear_sector_born`), outcome by outcome;
* ★★★ `readyPrep_recordString_ne_le` — #103's relabelling bound on the shear arena, and
  ★★★ `one_sub_le_robust_fraction_readyPrep` — #106's robust fraction there.

## The price, and it is one the corpus already knows

The property that discharges the bridge — **no back-reaction on the system factor** — is the same
property that `shear_base_marginal_unchanged` identifies as the witness's limitation: the shear gives
repeatability but **not** the Lüders update, and the tension is structural rather than an oversight. So
#108 is discharged *because* the witness does not collapse the state. A propagator that did disturb the
system would need #107's other sufficient condition (`readsEpistemic_readyPrep_of_measurePreserving`)
or a new argument, and neither is supplied here.

## Honest scope

⚠️ **Equality of measures, not of sets.** `readyPrep_outcomeSector_eq_preimage_globalBasin` says the
flow-carved sector and the transported basin have the same probability for every outcome. It does
**not** say they agree as sets, or `readyPrep`-almost everywhere; that would need the injectivity of
the arc labelling and is not claimed.

⚠️ **The de-isolation obligation is untouched.** `ShearWitness` item 1 — the propagator's Hamiltonian
generation is stated, not formalised — is upstream of everything here, and nothing below makes the
shear propagator a Hamiltonian flow.

⚠️ **One preparation, the canonical context.** The sector statements are at a fixed `p` and use
`basinIndex (momentContext N)`, the standard-basis context, as the selector.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `ArenaTransport.lean` (#107),
`ShearDeIsolation.lean` (`shear_sector_born`, `readyPrep_selReady`), `ShearWitness.lean`
(`shearEvolve`, `shear_correlates`, `shear_measurePreserving`, `shear_base_marginal_unchanged`),
`MacrostateStability.lean` (#103), `PointerDynamics.lean` (#106);
`specs/BACKLOG.md` #108, #107, #106, #103, #102.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {N : ℕ}

/-! ### The weaker condition the bridge actually needs -/

/-- ★★★ **A propagator that does not move the system reads the epistemic measure.** No measure
preservation and no hypothesis on the register: if the flow leaves the `Σ` factor alone then reading
`Σ` after it pushes the preparation forward to the epistemic measure.

This is #107's condition bought for less, and it is what the shear propagator satisfies. -/
theorem readsEpistemic_of_fst_eq {p : LF4.CPN N} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {F : LF4.KSigma N × β → LF4.KSigma N × β}
    (hfst : ∀ x, (F x).1 = x.1) :
    ReadsEpistemic p ((epistemicMeasure p).prod ν) (Prod.fst ∘ F) where
  measurable_map := by
    rw [show (Prod.fst ∘ F : LF4.KSigma N × β → LF4.KSigma N) = Prod.fst from funext hfst]
    exact measurable_fst
  pushforward := by
    rw [show (Prod.fst ∘ F : LF4.KSigma N × β → LF4.KSigma N) = Prod.fst from funext hfst]
    simp

/-! ### The shear propagator satisfies it -/

/-- The shear moves only the pointer: the system factor is fixed pointwise. -/
@[simp] theorem fst_shearEvolve (idx : LF4.KSigma N → Fin N) (s t : OnticTime)
    (x : LF4.KSigma N × LF4.KTorus) : (shearEvolve idx s t x).1 = x.1 := rfl

/-- ★★★ **The canonical ready preparation reads the epistemic measure.** `readyPrep` is
`epistemicMeasure p ⊗ readyMeasure N`, so its system marginal is the preparation. -/
theorem readsEpistemic_readyPrep_fst (p : LF4.CPN N) :
    ReadsEpistemic p (readyPrep p) (Prod.fst : LF4.KSigma N × LF4.KTorus → LF4.KSigma N) := by
  rw [readyPrep]
  exact readsEpistemic_of_fst_eq (readyMeasure N) (F := id) fun _ => rfl

/-- ★★★ **#108 DISCHARGED: the bridge holds for the shear propagator**, at every pair of times, and
it holds because the shear does not move the system — not because it preserves the preparation, which
`not_measurePreserving_shearEvolve_readyPrep` shows it cannot. -/
theorem readsEpistemic_shearEvolve (p : LF4.CPN N) (idx : LF4.KSigma N → Fin N) (s t : OnticTime) :
    ReadsEpistemic p (readyPrep p) (Prod.fst ∘ shearEvolve idx s t) := by
  rw [show (Prod.fst ∘ shearEvolve idx s t : LF4.KSigma N × LF4.KTorus → LF4.KSigma N)
      = Prod.fst from funext fun _ => rfl]
  exact readsEpistemic_readyPrep_fst p

/-! ### The recorded route is refuted -/

/-- The ready region carries the whole canonical ready preparation. -/
theorem readyPrep_readyRegion (p : LF4.CPN N) :
    readyPrep p (Prod.snd ⁻¹' readyArc N) = 1 := by
  rw [show (Prod.snd ⁻¹' readyArc N : Set (LF4.KSigma N × LF4.KTorus))
      = univ ×ˢ readyArc N from by ext x; simp,
    readyPrep, Measure.prod_prod, measure_univ, readyMeasure_readyArc, one_mul]

/-- ★★★ **#108's recorded route (i) is refuted.** The shear propagator does **not** preserve
`readyPrep`, and it cannot: a record *is* the pointer leaving the ready arc, the arcs are disjoint
(`shearProtocol`'s own `ready_disjoint_pointer`), so the ready region has measure `1` while its
preimage has measure `0`.

`shear_measurePreserving` is no counterexample: it preserves `μ ⊗ volume`, the unconditioned Haar
measure on the register, and `readyPrep` conditions on the ready arc. -/
theorem not_measurePreserving_shearEvolve_readyPrep [NeZero N] (p : LF4.CPN N) :
    ¬ MeasurePreserving (shearEvolve (basinIndex (momentContext N)) 0 1)
        (readyPrep p) (readyPrep p) := by
  intro hMP
  set idx := basinIndex (momentContext N) with hidxdef
  have hidx : Measurable idx := measurable_basinIndex (momentContext N)
  have hmeasF : Measurable (shearEvolve idx 0 1) :=
    (shearProtocol idx hidx).measurable_evolve 0 1
  have hmeasReady : MeasurableSet (Prod.snd ⁻¹' readyArc N :
      Set (LF4.KSigma N × LF4.KTorus)) := measurable_snd measurableSet_readyArc
  -- the preimage of the ready region misses the ready region
  have hsub : (shearEvolve idx 0 1) ⁻¹' (Prod.snd ⁻¹' readyArc N)
      ⊆ (Prod.snd ⁻¹' readyArc N)ᶜ := by
    intro x hx hx'
    have hcorr : x ∈ (shearProtocol idx hidx).outcomeSector (idx x.1) :=
      shear_correlates idx hidx (idx x.1) ⟨rfl, hx'⟩
    have hmem : shearEvolve idx 0 1 x ∈ (shearProtocol idx hidx).pointerRegion (idx x.1) := hcorr
    exact (Set.disjoint_left.1 ((shearProtocol idx hidx).ready_disjoint_pointer (idx x.1)))
      hx hmem
  have hzero : readyPrep p ((shearEvolve idx 0 1) ⁻¹' (Prod.snd ⁻¹' readyArc N)) = 0 := by
    refine measure_mono_null hsub ?_
    have h1 := readyPrep_readyRegion p
    have : readyPrep p (Prod.snd ⁻¹' readyArc N)ᶜ
        = readyPrep p univ - readyPrep p (Prod.snd ⁻¹' readyArc N) :=
      measure_compl hmeasReady (measure_ne_top _ _)
    rw [this, h1, measure_univ, tsub_self]
  have hone : readyPrep p ((shearEvolve idx 0 1) ⁻¹' (Prod.snd ⁻¹' readyArc N)) = 1 := by
    rw [← Measure.map_apply hmeasF hmeasReady, hMP.map_eq]
    exact readyPrep_readyRegion p
  rw [hzero] at hone
  exact zero_ne_one hone

/-! ### What the bridge delivers on the shear arena -/

/-- ★★ **The transported basin carries the Born weight** under the canonical ready preparation. -/
theorem readyPrep_preimage_globalBasin (p : LF4.CPN N) (c : ContextField N) (i : Fin N) :
    readyPrep p (Prod.fst ⁻¹' globalBasin c i) = ENNReal.ofReal (c.rate p i) :=
  measure_preimage_globalBasin (readsEpistemic_readyPrep_fst p) c i

/-- ★★★ **And it is the same weight the flow-carved outcome sector carries.** The sector the shear
propagator actually produces and the record event transported along the reading map agree in
probability, outcome by outcome.

⚠️ This is equality of *measures*. It does not say the two sets agree, or agree almost everywhere. -/
theorem readyPrep_outcomeSector_eq_preimage_globalBasin [NeZero N] (p : LF4.CPN N) (i : Fin N) :
    readyPrep p ((shearProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector i)
      = readyPrep p (Prod.fst ⁻¹' globalBasin (momentContext N) i) := by
  rw [shear_sector_born, readyPrep_preimage_globalBasin, momentContext_rate]

/-- ★★★ **#103's relabelling bound holds on the shear arena**: the arena microstates whose record
string a write of size `δ` changes have `readyPrep` measure at most `k · N · δ`. -/
theorem readyPrep_recordString_ne_le (p : LF4.CPN N) {k : ℕ} (c : Fin k → ContextField N) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    readyPrep p (Prod.fst ⁻¹' {x | recordString c (sigmaShift δ x) ≠ recordString c x})
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ) :=
  measure_preimage_recordString_ne_le (readsEpistemic_readyPrep_fst p) c hδ

/-- ★★★ **#106's robust fraction holds on the shear arena**: within the transported sector the
realised record survives a write of size `δ` on all but `δ / rate` of it. -/
theorem one_sub_le_robust_fraction_readyPrep (p : LF4.CPN N) (c : ContextField N) {δ : ℝ}
    (hδ : 0 ≤ δ) (i : Fin N) (hrate : 0 < c.rate p i) :
    1 - δ / c.rate p i
      ≤ (readyPrep p (Prod.fst ⁻¹' robustBasin c δ i)).toReal / c.rate p i :=
  one_sub_le_robust_fraction_preimage (readsEpistemic_readyPrep_fst p) c hδ i hrate

end CSD.RecordLayer

end
