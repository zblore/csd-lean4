/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OutcomeField
public import CsdLean4.SigmaLayer.FiniteQMClosure
public import CsdLean4.RecordLayer.SwapLuders

/-!
# SigmaLayer/DynamicMeasurementClosure: the dynamical capstone (item 8)

**Category:** 7-SigmaLayer (the record layer — the capstone).

## ★ Additive, not destabilising

The plan is explicit: **do not immediately destabilise the working capstone.** So `FiniteQMClosure`
is untouched — it still runs on `unifiedDeisolationModel` / `vnPointerOutcome ψ'` /
preparation-indexed `bornRegion`, and every one of its theorems stands exactly as before. This file
*adds* a second, independent bundle and a combining capstone; it deprecates nothing and migrates
nothing.

⚠️ **`FiniteQMClosure` is `operational` finite-QM closure**, and should be described that way rather
than as finite-QM closure *simpliciter*: its readout is preparation-indexed and its records are not
dynamically created. `CsdFiniteQMClosure` below is what the combined claim looks like.

## What is proved

* `DynamicMeasurementClosure` — the five dynamical facts, for the shear witness at preparation `ψ`:
  ready ⇒ no record; a record is created and it is the outcome the selector fixed; the outcome
  sectors are disjoint; the record persists across the operational window; the selector weights are
  the Born weights. ⚠️ The **post-measurement/Lüders** field is deliberately *not* among them —
  `postMeasure_supported_pointerRegion` exists but the Lüders bridge needs a system-reduction map the
  corpus lacks for this arena (`RecordPersistence.lean`), so bundling it would overstate.
  *(Strengthened 2026-08-27: the **externality pair** joined the bundle — `outcome_system_dependent`,
  the contentful before half, and `record_system_invariant`, the after half, vacuous by
  architecture and carried as documentation. See `ShearWitness.lean`'s externality section.)*
* `dynamicMeasurementClosure` — discharged. ★ **Note what is *not* among its hypotheses:**
  `CorrelatesOn` and `PointerInvariantOn` do not appear, because `ShearWitness` proved them. The
  bundle rests on a constructed propagator, not on assumed dynamics.
* **`luders_followup` (added 2026-08-02)** — the rank-one Lüders update, from the calibrated-swap
  witness: after outcome `i`, follow-up statistics for *any* context are the collapsed state's Born
  weights. With this field the plan's boxed completion criterion is met line-by-line for
  nondegenerate computational-basis measurements.
* `CsdFiniteQMClosure` — the combining capstone: operational closure **and** dynamical measurement.

## ⚠️ What the combined capstone does and does not assert

It asserts the two bundles hold. It does **not** assert they are about the same arena — the
operational closure lives on `productDynamics` over `ℂℙ^M × T²` and the dynamical one on
`Σ_sel × T²_R`. Unifying the arenas is the engine migration, and is **not** done. Read
`CsdFiniteQMClosure` as *"both hold"*, not as *"one theory covers both"*.

⚠️ And the standing residue of item 3 is unchanged: the propagator is explicit and every property is
proved of it, but **the Hamiltonian generation is stated, not formalised**. A capstone cannot launder
that.

## References

`SigmaLayer/FiniteQMClosure.lean` (the operational closure, untouched);
`RecordLayer/ShearWitness.lean`, `RecordLayer/DynamicBorn.lean`, `RecordLayer/RecordPersistence.lean`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {N : ℕ} [NeZero N]

/-- **The dynamical measurement closure.** The five facts a measurement must exhibit *as a process*,
as against as a partition. -/
structure DynamicMeasurementClosure (N : ℕ) [NeZero N]
    (ψ : EuclideanSpace ℂ (Fin N)) : Prop where
  /-- **Ready ⇒ no record.** Before the interaction the apparatus displays nothing. -/
  ready_no_record : ∀ x : LF4.KSigma N × LF4.KTorus, x.2 ∈ readyArc N →
    (shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).readout x = none
  /-- **A record is created**, and it is the outcome the hidden selector had fixed. -/
  record_created : ∀ (i : Fin N) (x : LF4.KSigma N × LF4.KTorus),
    x ∈ selReady (basinIndex (momentContext N)) i →
    (shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).readout
        ((shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).evolve 0 1 x) = some i
  /-- Distinct outcomes are exclusive. -/
  outcomes_exclusive : Pairwise (Function.onFun Disjoint
    (shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector)
  /-- **The record persists** across the operational window `[T_M, T_M + τ_R]`. -/
  record_persists : ∀ (i : Fin N) (x : LF4.KSigma N × LF4.KTorus) (t : OnticTime),
    x ∈ (shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i →
    1 ≤ t → t ≤ 1 + 1 →
    (shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).readout
        ((shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).evolve 0 t x) = some i
  /-- **The selector weights are the Born weights**, so the transported outcome weight is Born. -/
  selector_born : ∀ (hψ0 : ψ ≠ 0), ‖ψ‖ = 1 → ∀ i : Fin N,
    epistemicMeasure (Projectivization.mk ℂ ψ hψ0)
        (basinIndex (momentContext N) ⁻¹' {i})
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
  /-- **★ The Lüders update (rank-one), on the calibrated-swap witness.** After outcome `i`, the
  system behaves in *every* subsequent measurement as a fresh preparation of `eᵢ`: for any context
  field `c'`, the follow-up outcome-`j` probability is the collapsed state's Born weight
  `c'.rate [eᵢ] j`.

  ⚠️ Stated for the **swap** witness (`swapProtocol`), where fields 1–5 concern the shear; the swap
  discharges the same five hypotheses (`swap_correlates`, `swap_pointerInvariant`), and it alone
  supplies collapse — `shear_base_marginal_unchanged` proves the shear cannot. Nondegenerate case
  only; see `SwapLuders.lean` for the full scope notes. -/
  luders_followup : ∀ (μ12 : Measure (LF4.KSigma N × LF4.KTorus))
    [IsProbabilityMeasure μ12] (i : Fin N)
    (_ : μ12 ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0)
    (c' : ContextField N) (j : Fin N),
    ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).postMeasure
      (μ12.prod (Measure.pi fun k => epistemicMeasure (vertexPoint k))) i)
      ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j)
  /-- ★ **Externality, the before half (A1, added 2026-08-27).** Before the stroke a system-only
  transformation moving the selector across basins changes which outcome gets recorded: the
  outcome information is still in the system, and the stroke is what exports it to the
  register. -/
  outcome_system_dependent : ∀ (i j : Fin N), i ≠ j →
    ∀ (s s' : LF4.KSigma N), basinIndex (momentContext N) s = i →
      basinIndex (momentContext N) s' = j →
      ∀ (q : LF4.KTorus), q ∈ readyArc N →
        (shearProtocol (basinIndex (momentContext N))
            (measurable_basinIndex (momentContext N))).readout
            ((shearProtocol (basinIndex (momentContext N))
              (measurable_basinIndex (momentContext N))).evolve 0 1 (s, q))
          ≠ (shearProtocol (basinIndex (momentContext N))
              (measurable_basinIndex (momentContext N))).readout
              ((shearProtocol (basinIndex (momentContext N))
                (measurable_basinIndex (momentContext N))).evolve 0 1 (s', q))
  /-- ⚠️ **Externality, the after half (A2, added 2026-08-27) — vacuous by architecture, carried
  as documentation, not content:** the displayed record is invariant under *every* system-side
  map because the readout reads the register factor only (`rfl`-backed,
  `readout_system_invariant`). The contentful half is `outcome_system_dependent`. -/
  record_system_invariant : ∀ (f : LF4.KSigma N → LF4.KSigma N)
      (x : LF4.KSigma N × LF4.KTorus),
    (shearProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).readout (f x.1, x.2)
      = (shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).readout x

/-- **★ The dynamical measurement closure holds** — for every state, with no hypotheses about the
dynamics.

★ Note what is absent from the hypotheses: **`CorrelatesOn` and `PointerInvariantOn` do not appear.**
`ShearWitness` discharged them from an explicitly constructed propagator, so this bundle rests on a
construction rather than on assumed physics. That is the difference between this and every earlier
record-layer bundle in the corpus. -/
theorem dynamicMeasurementClosure (ψ : EuclideanSpace ℂ (Fin N)) :
    DynamicMeasurementClosure N ψ where
  ready_no_record _ hx := shear_readout_ready _ _ hx
  record_created _ _ hx := shear_readout_after _ _ hx
  outcomes_exclusive := (shearProtocol _ _).outcomeSector_pairwiseDisjoint
  record_persists _ _ _ hx ht₁ ht₂ :=
    (shearProtocol _ _).readout_persists_on_interval
      (shear_pointerInvariant _ _) hx ht₁ ht₂
  selector_born hψ0 hψ i := shear_selector_born ψ hψ0 hψ i
  luders_followup μ12 _ i hpos c' j := swap_luders_born μ12 i hpos c' j
  outcome_system_dependent := fun _i _j hij _s _s' hs hs' _q hq =>
    outcome_system_dependent_before _ _ hij hs hs' hq
  record_system_invariant f x := readout_system_invariant _ _ f x

/-- **The combining capstone**: operational finite-QM closure **and** dynamical measurement.

⚠️ **It asserts that both bundles hold. It does NOT assert they are about the same arena.** The
operational closure lives on `productDynamics` over `ℂℙ^M × T²` for a composite system indexed by
`Fin Nsub × Fin Nsub ≃ Fin (M+1)`; the dynamical one lives on `Σ_sel × T²_R` in dimension `Nsys`.
The parameter lists are disjoint, and that is not an accident of the encoding — it is the honest
state of the corpus. Unifying the arenas is the **engine migration**, and it is not done.

Read this as *"both hold"*, not *"one theory covers both"*. A capstone that bundled them while
implying otherwise would be exactly the kind of claim this project keeps having to retract. -/
structure CsdFiniteQMClosure
    {Nsys : ℕ} [NeZero Nsys] (ψsys : EuclideanSpace ℂ (Fin Nsys))
    {Nsub M : ℕ} [NeZero Nsub]
    (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
    (p₀ : LF4.CPN (M + 1)) (e : Fin Nsub × Fin Nsub ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) : Prop where
  /-- The existing **operational** closure, untouched. -/
  operational : CSD.SigmaLayer.FiniteQMClosure H hH p₀ e ψ' hψ'0 ψ hψ0
  /-- Measurement as a *process*: records created, persistent, Born-weighted. -/
  dynamic : DynamicMeasurementClosure Nsys ψsys

/-- The combining capstone holds. -/
theorem csdFiniteQMClosure
    {Nsys : ℕ} [NeZero Nsys] (ψsys : EuclideanSpace ℂ (Fin Nsys))
    {Nsub M : ℕ} [NeZero Nsub]
    (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
    (p₀ : LF4.CPN (M + 1)) (e : Fin Nsub × Fin Nsub ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ' : ‖ψ'‖ = 1) (hψ : ‖ψ‖ = 1) :
    CsdFiniteQMClosure ψsys H hH p₀ e ψ' hψ'0 ψ hψ0 where
  operational := CSD.SigmaLayer.unifiedFiniteQMClosure H hH p₀ e ψ' hψ'0 ψ hψ0 hψ' hψ
  dynamic := dynamicMeasurementClosure ψsys

end CSD.RecordLayer
