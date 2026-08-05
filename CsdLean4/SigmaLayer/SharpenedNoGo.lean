/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerArena
public import CsdLean4.SigmaLayer.MeasurementConstraints

/-!
# SigmaLayer/SharpenedNoGo: a positive-width ready region cannot hide the no-record set

**Category:** dynamical measurement — `specs/BACKLOG.md` **B5**, the trilemma's third leg.

## The question

The third horn (`NullSeamWitness.lean`) achieves continuity **and** exact Born **and**
records exact off a null seam — at the price of a **Dirac-calibrated** ready state. The
trilemma claims that price is unavoidable: that with a ready region of *positive width* the
no-record set stops being null. This module proves the qualitative half of that.

★ `posMeasure_noRecord_of_isOpenMap`: if the propagator is an **open map** and the ready
set `A` is **open**, then as soon as some ready state is carried to a point in the closure
of the no-record interior, the no-record preimage has **positive measure**.

The mechanism is exactly why a Dirac calibration escapes: `Φ '' A` is open, so it is not
merely *a* point near the boundary — it contains a whole neighbourhood, and any
neighbourhood of a boundary point of the no-record set meets that set's **interior**. A
single calibrated point has no neighbourhood to spare, which is how the null-seam witness
threads the kissing state exactly.

## ⚠️ What this does **not** prove — a correction to my own earlier claim

`NullSeamWitness.lean` asserted that a positive-width ready region fattens the seam "to a
positive-measure set **of order the calibration width**". The *order* is a quantitative
claim, and it is **not** proved here and does not follow from this argument, which is
purely topological. Getting `O(δ)` needs an estimate on how far the landing moments move
as the ready state moves — real analysis, not soft topology. That over-assertion has been
corrected at its source; what stands is the qualitative statement above.

Two further gaps, stated rather than papered over:

* ~~The forcing step is a hypothesis, not a conclusion.~~ **Closed in the same session**:
  `exists_noRecord_of_meets_two` inverts `no_everywhere_correlation` — a correlating
  propagator on a preconnected ready set *must* carry some state outside every record
  region — and `posMeasure_noRecord_of_correlates` chains it to the measure bound. The
  hypotheses now split by kind: everything about the **dynamics** is discharged, and what
  remains is one assumption about the **record geometry**.
* ~~The one remaining hypothesis is `hreg`~~ **Discharged 2026-08-05**
  (`SigmaLayer/NoRecordGeometry.lean`): the no-record set IS contained in the closure of
  its interior — the perturbation (feed weight into the ready component, fixing every
  record numerator while the norm strictly grows) is now constructed, and
  `posMeasure_noRecord_pointer` instantiates this theorem for the pointer's record regions
  with **no geometric hypothesis left**. B5 is closed outright.

## References

`specs/BACKLOG.md` B5; `SigmaLayer/NullSeamWitness.lean` (the third horn, and the scope
note corrected alongside this); `SigmaLayer/MeasurementConstraints.lean`
(`no_everywhere_correlation`, whose connectedness argument the forcing step would reuse);
`SigmaLayer/NoRecordGeometry.lean` (the geometric hypothesis `hreg`, discharged
2026-08-05); `docs/TOUR.md` §"Which horn is the right one?".
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix.UnitaryGroup

/-- ★ **A positive-width ready region cannot hide the no-record set.** For an open-map,
continuous propagator and an *open* ready set, if some ready state is carried into the
closure of the no-record interior then the no-record preimage carries positive measure.

The hypothesis `hpos` — that the measure is positive on nonempty opens — is exactly what
Fubini–Study satisfies (`LF4.fubiniStudyMeasure_pos_of_isOpen`), and is what makes "open"
the operative word: a **Dirac** calibration has no open neighbourhood, which is precisely
how the null-seam witness threads the boundary point exactly and keeps its seam null. -/
theorem posMeasure_noRecord_of_isOpenMap
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
    (hpos : ∀ U : Set X, IsOpen U → U.Nonempty → μ U ≠ 0)
    {Φ : X → X} (hopen : IsOpenMap Φ) (hcont : Continuous Φ)
    {A R : Set X} (hA : IsOpen A) {a : X} (ha : a ∈ A)
    (hΦa : Φ a ∈ closure (interior R)) :
    μ (A ∩ Φ ⁻¹' interior R) ≠ 0 := by
  -- the image of the ready set is an open neighbourhood of `Φ a`
  have hImg : IsOpen (Φ '' A) := hopen A hA
  have hmemImg : Φ a ∈ Φ '' A := ⟨a, ha, rfl⟩
  -- a neighbourhood of a point of `closure (interior R)` meets `interior R`
  obtain ⟨y, hyImg, hyInt⟩ :=
    mem_closure_iff.mp hΦa (Φ '' A) hImg hmemImg
  obtain ⟨x, hxA, rfl⟩ := hyImg
  -- so the no-record preimage contains a nonempty open set
  refine hpos _ (hA.inter (isOpen_interior.preimage hcont)) ⟨x, hxA, hyInt⟩

/-- The same statement for the pointer factor under a unitary stroke: a unitary acts as a
homeomorphism of `ℂℙ^K`, so it is an open map, and Fubini–Study is positive on nonempty
opens. This is the form the third horn's price takes. -/
theorem posMeasure_noRecord_unitary {K : ℕ} (q₀ : Pointer K)
    (U : Matrix.unitaryGroup (Fin (K + 1)) ℂ)
    {A R : Set (Pointer K)} (hA : IsOpen A) {a : Pointer K} (ha : a ∈ A)
    (hUa : U • a ∈ closure (interior R)) :
    fubiniStudyMeasure q₀ (A ∩ (fun q : Pointer K => U • q) ⁻¹' interior R) ≠ 0 := by
  refine posMeasure_noRecord_of_isOpenMap
    (fun V hV hVne => LF4.fubiniStudyMeasure_pos_of_isOpen q₀ hV hVne)
    (IsOpenMap.of_inverse (continuous_const_smul U⁻¹) (fun q => by simp)
      (fun q => by simp)) (continuous_const_smul U) hA ha hUa

/-! ### ★ The forcing step — no longer a hypothesis -/

/-- ★ **A correlating propagator must pass through the no-record set.** The inverse of
`no_everywhere_correlation`: rather than assuming the image is covered by two record
regions and deriving `False`, conclude that it is **not** covered — some ready state lands
outside both. Same connectedness argument, contrapositive shape. -/
theorem exists_noRecord_of_meets_two
    {X : Type*} [TopologicalSpace X] {Φ : X → X} (hcont : Continuous Φ)
    {A : Set X} (hconn : IsPreconnected A)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hmeetU : ∃ x ∈ A, Φ x ∈ U) (hmeetV : ∃ x ∈ A, Φ x ∈ V) :
    ∃ x ∈ A, Φ x ∉ U ∪ V := by
  by_contra hcon
  have hall : ∀ x ∈ A, Φ x ∈ U ∪ V := by
    intro x hx
    by_contra hx2
    exact hcon ⟨x, hx, hx2⟩
  have himg : IsPreconnected (Φ '' A) := hconn.image Φ hcont.continuousOn
  obtain ⟨xu, hxu, hxuU⟩ := hmeetU
  obtain ⟨xv, hxv, hxvV⟩ := hmeetV
  have hsub : Φ '' A ⊆ U ∪ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hall x hx
  have hne : (Φ '' A ∩ U).Nonempty := ⟨Φ xu, ⟨xu, hxu, rfl⟩, hxuU⟩
  have hin : Φ '' A ⊆ U := himg.subset_left_of_subset_union hU hV hUV hsub hne
  exact (hUV.le_bot ⟨hin ⟨xv, hxv, rfl⟩, hxvV⟩ : Φ xv ∈ (⊥ : Set X))

/-- ★★ **The trilemma's third leg, with only a geometric hypothesis left.** A continuous
open-map propagator that correlates two outcomes on an **open preconnected** ready set
gives the no-record set **positive measure** — provided the no-record set is *regular*
(contained in the closure of its interior).

The hypotheses now split cleanly by kind: everything about the *dynamics* is discharged
(continuity, openness, correlation), and the single remaining assumption `hreg` is a
property of the **record geometry** alone. For the corpus's moment regions
`{m_{j+1} > 1/2}` regularity is now a theorem — `recordRegion_pair_compl_regular`
(`SigmaLayer/NoRecordGeometry.lean`, 2026-08-05) constructs the perturbation toward the
ready vertex, and `posMeasure_noRecord_pointer` instantiates this statement with `hreg`
discharged.

This is why the Dirac calibration escapes: `hA : IsOpen A` fails for a point. -/
theorem posMeasure_noRecord_of_correlates
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
    (hpos : ∀ W : Set X, IsOpen W → W.Nonempty → μ W ≠ 0)
    {Φ : X → X} (hopen : IsOpenMap Φ) (hcont : Continuous Φ)
    {A : Set X} (hA : IsOpen A) (hconn : IsPreconnected A)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hreg : (U ∪ V)ᶜ ⊆ closure (interior ((U ∪ V)ᶜ)))
    (hmeetU : ∃ x ∈ A, Φ x ∈ U) (hmeetV : ∃ x ∈ A, Φ x ∈ V) :
    μ (A ∩ Φ ⁻¹' interior ((U ∪ V)ᶜ)) ≠ 0 := by
  obtain ⟨x, hxA, hxOut⟩ :=
    exists_noRecord_of_meets_two hcont hconn hU hV hUV hmeetU hmeetV
  exact posMeasure_noRecord_of_isOpenMap hpos hopen hcont hA hxA (hreg hxOut)

end CSD.RecordLayer
