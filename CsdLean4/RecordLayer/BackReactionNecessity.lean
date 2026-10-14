/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin
public import CsdLean4.RecordLayer.ShearWitness
public import CsdLean4.Mathlib.MeasureTheory.FibrePreserving

/-!
# RecordLayer/BackReactionNecessity: where the preparation can enter a Σ-local measurement

**Category:** 7-SigmaLayer (the record layer — the shape of Posit 1's discharge, BACKLOG #19-A).

The record layer's preparation is `epistemicMeasure p = δ_p ⊗ vol_{T²}`: the epistemic state is a
**point** of the calculation space `ℂℙ^{N−1}`, and all ontic ignorance lives in the fibre `T²`,
uniformly. A measurement is a flow on `Σ` read against a readout. This file asks the one question
that shape forces: **through which door can the preparation reach the outcome statistics?**

## The theorem

Call a map `Φ : Σ → Σ` *fibre-preserving* if it fixes the base point and acts on the fibre over
each base point by a volume-preserving map (`FibrePreserving`, the Category-1 notion), and call a
readout *fibre-only* if it is `univ ×ˢ R` for a set `R ⊆ T²` of fibre points.

* ★ `epistemicMeasure_preimage_univ_prod`: under `δ_p ⊗ vol`, a fibre-preserving map sends mass
  `vol R` into a fibre-only readout — **for every `p`**. The statistics cannot see the preparation.
* ★★ `no_fibrePreserving_born`: hence no fibre-preserving map with fibre-only readouts has Born
  statistics `vol(Φ⁻¹ R_i) = momentMap p i` (two basis rays already disagree).
* ★★★ `exists_fst_ne_of_born`: contrapositively, **a Σ-local measurement with Born statistics and
  a fibre-only readout must move the base point** — back-reaction on the calculation space is
  necessary, not optional.
* ★ `globalBasin_not_fibreOnly`: the corpus's own basins are **not** fibre-only: `globalBasin`
  reads the rate at the ontic base point, which is exactly the other door.
* `shearEvolve_fibrePreserving`: the constructed de-isolation witness is fibre-preserving, so it
  takes that other door — its readout reads the selector, not the fibre alone.

## What this says about Posit 1 (BACKLOG #19)

The preparation reaches the outcome through one of two doors and no third: **the readout reads
the base** (the cell law as the corpus has it: a context-fixed partition whose arcs are sized by
the rate *at the ontic point*), or **the flow moves the base** (back-reaction, the register acting
on the calculation space). Every landed witness takes the first door with a fibre-preserving flow;
the back-reacting `jointLift` moves the base only along the torus directions, with the rates
conserved, so it takes the first door too. A *derivation* of the rates from the dynamics, which is
what #19 asks for, is therefore a theorem about the second door: a flow whose base motion is what
sizes the sectors. That is a Σ-local statement — manifold-locality of a flow on `Σ` — and it is
where the epistemic point, the state QM calculates with, is acted on by the ontic register.

## Honest scope

* Nothing here decides #19, names an interaction (R-015) or formalises generation (R-016).
* "Fibre-preserving" is stated pointwise over every base point, which is what the witnesses
  satisfy (`measurePreserving_pshift`). A flow preserving `μ_FS ⊗ vol` need only preserve the fibre
  measure over almost every base point; the almost-everywhere version is not stated.
* The readout is on the fibre `T²` of `Σ` itself. The pointer-arena witnesses carry a second
  torus `T²_R` for the register and read *that*; the same argument applies verbatim with
  `readyPrep p = epistemicMeasure p ⊗ readyMeasure`, and is not repeated.

References: `specs/BACKLOG.md` #19, #137; `specs/POSITS.md` Posit 1; `RecordLayer/GlobalBasin.lean`
(`epistemicMeasure`, `globalBasin`, `globalBasin_prob`); `RecordLayer/ShearWitness.lean`
(`shearEvolve`, `measurePreserving_pshift`); `RecordLayer/JointLift.lean` (`jointLift`);
`Mathlib/MeasureTheory/FibrePreserving.lean`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The two basis rays that disagree -/

/-- The ray of the `i`-th standard basis vector. -/
noncomputable def basisRay (i : Fin N) : LF4.CPN N :=
  Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ))
    (by simp)

lemma momentMap_basisRay_self (i : Fin N) : LF4.momentMap (basisRay i) i = 1 := by
  rw [basisRay, LF4.momentMap_mk_eq_inner_sq _ _ (by simp), EuclideanSpace.inner_single_left]
  simp

lemma momentMap_basisRay_of_ne {i j : Fin N} (h : j ≠ i) : LF4.momentMap (basisRay i) j = 0 := by
  rw [basisRay, LF4.momentMap_mk_eq_inner_sq _ _ (by simp), EuclideanSpace.inner_single_left]
  simp [h]

/-! ### Fibre-preserving maps against fibre-only readouts -/

/-- ★ Under `δ_p ⊗ vol`, a fibre-preserving map sends mass `vol R` into a fibre-only readout, for
every preparation `p`. -/
theorem epistemicMeasure_preimage_univ_prod {Φ : LF4.KSigma N → LF4.KSigma N}
    (hΦ : FibrePreserving Φ (volume : Measure LF4.KTorus)) (hm : Measurable Φ) (p : LF4.CPN N)
    {R : Set LF4.KTorus} (hR : MeasurableSet R) :
    epistemicMeasure p (Φ ⁻¹' (univ ×ˢ R)) = volume R := by
  rw [epistemicMeasure]
  exact hΦ.measure_preimage_univ_prod hm p hR

/-- ★★ **No fibre-preserving measurement with fibre-only readouts has Born statistics.** -/
theorem no_fibrePreserving_born (hN : 2 ≤ N) {Φ : LF4.KSigma N → LF4.KSigma N}
    (hΦ : FibrePreserving Φ (volume : Measure LF4.KTorus)) (hm : Measurable Φ)
    {R : Fin N → Set LF4.KTorus} (hR : ∀ i, MeasurableSet (R i)) :
    ¬ ∀ (p : LF4.CPN N) (i : Fin N),
        epistemicMeasure p (Φ ⁻¹' (univ ×ˢ R i)) = ENNReal.ofReal (LF4.momentMap p i) := by
  intro h
  set i₀ : Fin N := ⟨0, by omega⟩
  set i₁ : Fin N := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := fun e => absurd (Fin.mk.inj e) zero_ne_one
  have h0 := h (basisRay i₀) i₀
  have h1 := h (basisRay i₁) i₀
  rw [epistemicMeasure_preimage_univ_prod hΦ hm _ (hR i₀), momentMap_basisRay_self] at h0
  rw [epistemicMeasure_preimage_univ_prod hΦ hm _ (hR i₀), momentMap_basisRay_of_ne hne] at h1
  rw [h0] at h1
  simp at h1

/-- ★★★ **Back-reaction is necessary.** A measurement on `Σ` whose fibre maps preserve volume
over every base point, read against fibre-only readouts with Born statistics, moves some base
point: the register acts on the calculation space. -/
theorem exists_fst_ne_of_born (hN : 2 ≤ N) {Φ : LF4.KSigma N → LF4.KSigma N} (hm : Measurable Φ)
    (hfib : ∀ b, MeasurePreserving (fun y => (Φ (b, y)).2) (volume : Measure LF4.KTorus) volume)
    {R : Fin N → Set LF4.KTorus} (hR : ∀ i, MeasurableSet (R i))
    (hborn : ∀ (p : LF4.CPN N) (i : Fin N),
      epistemicMeasure p (Φ ⁻¹' (univ ×ˢ R i)) = ENNReal.ofReal (LF4.momentMap p i)) :
    ∃ x, (Φ x).1 ≠ x.1 := by
  by_contra h
  refine no_fibrePreserving_born hN ⟨fun x => ?_, hfib⟩ hm hR hborn
  by_contra hx
  exact h ⟨x, hx⟩

/-! ### The corpus's witnesses take the other door -/

/-- ★ **The basins read the base.** `globalBasin (momentContext N) i` is not a fibre-only set:
its epistemic measure is the rate at the preparation, which two basis rays already distinguish. -/
theorem globalBasin_not_fibreOnly (hN : 2 ≤ N) :
    ¬ ∃ R : Set LF4.KTorus, globalBasin (momentContext N) ⟨0, by omega⟩ = univ ×ˢ R := by
  rintro ⟨R, hR⟩
  set i₀ : Fin N := ⟨0, by omega⟩
  set i₁ : Fin N := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := fun e => absurd (Fin.mk.inj e) zero_ne_one
  have h0 := globalBasin_prob (momentContext N) i₀ (basisRay i₀)
  have h1 := globalBasin_prob (momentContext N) i₀ (basisRay i₁)
  rw [hR, epistemicMeasure, Measure.prod_prod, measure_univ, one_mul, momentContext_rate] at h0 h1
  rw [momentMap_basisRay_self] at h0
  rw [momentMap_basisRay_of_ne hne] at h1
  rw [h0] at h1
  simp at h1

/-- The constructed de-isolation witness is fibre-preserving: it translates the fibre over each
selector point by a volume-preserving shift. Its readout reads the selector. -/
theorem shearEvolve_fibrePreserving {Xsel : Type*} {K : ℕ}
    (idx : Xsel → Fin K) (s t : SigmaLayer.OnticTime) :
    FibrePreserving (shearEvolve idx s t) (volume : Measure LF4.KTorus) :=
  ⟨fun _ => rfl, fun b => by
    show MeasurePreserving (pshift ((elapsed t - elapsed s) * shearAmt K (idx b))) volume volume
    exact measurePreserving_pshift _⟩

end CSD.RecordLayer

end
