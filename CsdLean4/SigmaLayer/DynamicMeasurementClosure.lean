/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.OutcomeField
public import CsdLean4.SigmaLayer.FiniteQMClosure

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
* `dynamicMeasurementClosure` — discharged. ★ **Note what is *not* among its hypotheses:**
  `CorrelatesOn` and `PointerInvariantOn` do not appear, because `ShearWitness` proved them. The
  bundle rests on a constructed propagator, not on assumed dynamics.
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
`SigmaLayer/ShearWitness.lean`, `SigmaLayer/DynamicBorn.lean`, `SigmaLayer/RecordPersistence.lean`.
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
