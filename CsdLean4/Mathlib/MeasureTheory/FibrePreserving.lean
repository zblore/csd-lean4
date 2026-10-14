/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Fibre-preserving maps of a product, and readouts that read the fibre only

**Category:** 1-Mathlib (CSD-free upstream candidate).
BACKLOG #19-A; consumed by `RecordLayer/BackReactionNecessity.lean`.

A map `Φ : B × F → B × F` is **fibre-preserving** for a measure `ν` on `F` if it fixes the base
coordinate and acts on the fibre over each base point by a `ν`-preserving map
(`FibrePreserving`). A set `S ⊆ B × F` **reads the fibre only** if it is `univ ×ˢ R`.

The one theorem: under the Dirac-at-`b` preparation `(dirac b).prod ν`, the mass a fibre-preserving
map sends into a fibre-only readout is `ν R`, whatever `b` is
(`FibrePreserving.measure_preimage_univ_prod`). So the statistics of such a readout under such a
dynamics **cannot depend on the base point**. A corollary says the same for `Φ = id`: a fibre-only
set has base-independent Dirac-product measure (`measure_dirac_prod_univ_prod`).

References: `Mathlib/MeasureTheory/Measure/Prod.lean` (`Measure.dirac_prod`); `specs/BACKLOG.md`
#19.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {B F : Type*} [MeasurableSpace B] [MeasurableSpace F]

/-- `Φ` is **fibre-preserving** for `ν`: it fixes the base coordinate and acts on the fibre over
each base point by a `ν`-preserving map. -/
structure FibrePreserving (Φ : B × F → B × F) (ν : Measure F) : Prop where
  /-- The base coordinate is fixed. -/
  fst_eq : ∀ x, (Φ x).1 = x.1
  /-- Over each base point the fibre map preserves `ν`. -/
  measurePreserving_snd : ∀ b, MeasurePreserving (fun y => (Φ (b, y)).2) ν ν

/-- A fibre-only set has base-independent measure under every Dirac-product preparation. -/
theorem measure_dirac_prod_univ_prod (ν : Measure F) [SFinite ν] (b : B) {R : Set F}
    (hR : MeasurableSet R) :
    ((Measure.dirac b).prod ν) (univ ×ˢ R) = ν R := by
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (MeasurableSet.univ.prod hR)]
  simp

/-- ★ **A fibre-preserving map cannot make a fibre-only readout depend on the base point**: under
the preparation `(dirac b).prod ν`, the mass sent into `univ ×ˢ R` is `ν R` for every `b`. -/
theorem FibrePreserving.measure_preimage_univ_prod {Φ : B × F → B × F} {ν : Measure F} [SFinite ν]
    (hΦ : FibrePreserving Φ ν) (hm : Measurable Φ) (b : B) {R : Set F} (hR : MeasurableSet R) :
    ((Measure.dirac b).prod ν) (Φ ⁻¹' (univ ×ˢ R)) = ν R := by
  rw [Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left (hm (MeasurableSet.univ.prod hR))]
  have e : Prod.mk b ⁻¹' (Φ ⁻¹' (univ ×ˢ R)) = (fun y => (Φ (b, y)).2) ⁻¹' R := by
    ext y
    simp
  rw [e]
  exact (hΦ.measurePreserving_snd b).measure_preimage hR.nullMeasurableSet

omit [MeasurableSpace B] in
/-- The identity is fibre-preserving. -/
theorem fibrePreserving_id (ν : Measure F) : FibrePreserving (id : B × F → B × F) ν :=
  ⟨fun _ => rfl, fun _ => MeasurePreserving.id ν⟩

omit [MeasurableSpace B] in
/-- A map that translates the fibre over each base point by a base-dependent amount is
fibre-preserving whenever each translation preserves `ν`. -/
theorem fibrePreserving_of_measurePreserving {φ : B → F → F} {ν : Measure F}
    (h : ∀ b, MeasurePreserving (φ b) ν ν) :
    FibrePreserving (fun x : B × F => (x.1, φ x.1 x.2)) ν :=
  ⟨fun _ => rfl, fun b => h b⟩

end MeasureTheory

end
