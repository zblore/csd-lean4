/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.UntriggeredReadout
public import CsdLean4.RecordLayer.MeasurementConstraints
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# SigmaLayer/UntriggeredVolume: the untriggered flow preserves chart volume, and is unique

**Category:** dynamical measurement — `specs/frozen-base-obstruction-scoping.md` brick 2, the
two gaps its own honest scope left open: measure preservation and uniqueness.

## What this closes

Brick 2 (`SigmaLayer/UntriggeredFlow.lean`) built one Hamiltonian flow that records and
back-reacts. Its readout half (`SigmaLayer/UntriggeredReadout.lean`) showed the record is
faithful for *every* preparation `μ` — but said nothing about which `μ` the dynamics itself
preserves, and every necessary condition in `RecordLayer/MeasurementConstraints.lean` takes
measure preservation as its hypothesis. This module supplies it.

The whole argument is one observation: **the time-`t` map is linear in the initial state**,
block-diagonal on `Chart n = (Fin n → ℝ) × (Fin n → ℝ)`, and each block is a rank-one
perturbation of the identity — a shear. Its determinant is `(1 + t·c_k)(1 − t·c_k) = 1` by the
matrix determinant lemma, because `c k = 0`.

* `untriggeredLin` — the time-`t` map as a linear endomorphism; `untriggeredLin_apply` identifies
  it with `untriggeredCurve`.
* `det_untriggeredLin` — its determinant is `1`.
* ★★ `untriggeredCurve_measurePreserving` — therefore the flow preserves Lebesgue measure on the
  chart. This is `MeasurePreserving` in the corpus's own sense (`ConstraintDynamics.flow_preserves`,
  `MeasurementRecord`), so it plugs directly into the necessary conditions.
* ★ `untriggered_no_exact_collapse` — one such plug-in, `MeasurementConstraints.no_exact_collapse`
  instantiated on this flow: a positive-volume set of preparations cannot be driven into a
  null set. Collapse, on this flow too, is relocation of a null slice.
* ★ `untriggeredCurve_unique` — the same linearity makes the field Lipschitz, so brick 0's
  `hamiltonianCurve_unique` upgrades *an* integral curve to *the* integral curve. This is the
  claim brick 2's docstring promised and then withdrew; it is now proved.

## Not reinvented

Everything measure-theoretic is Mathlib: `Measure.map_linearMap_addHaar_eq_smul_addHaar`
(pushforward of a Haar measure by a linear map is `|det⁻¹|` times itself), `LinearMap.det_prodMap`
(block-diagonal determinants multiply), `LinearMap.det_toLin'` and
`Matrix.det_one_add_replicateCol_mul_replicateRow` (the matrix determinant lemma). The chart's
Lebesgue measure is Haar by instance. No volume computation is done by hand.

## ⚠️ Honest scope

**This is measure preservation of the chart flow, not Born.** There is still no moment map in a
Darboux chart, so nothing here weights outcomes; the readout half's caveat stands unchanged.
It is a *chart* statement: `Chart n` is globally `ℝ^{2n}`, the arena is not, and the
chart→arena transport **remains open** (⚠️ RESIDUE(R-016)). Which interaction an apparatus
realises is a permanent boundary rather than open work (⚠️ RESIDUE(R-015)).

`c k = 0` is a hypothesis throughout, as in `untriggeredCurve_isHamiltonianCurve`. Without it
the block determinants are `1 ± t·c_k` and the map is not volume-preserving — but then it is not
the Hamiltonian flow either, so nothing is lost.

## References

`specs/frozen-base-obstruction-scoping.md` (brick 2, remaining gaps); `specs/future-work.md`;
`SigmaLayer/UntriggeredFlow.lean` (`untriggeredCurve`, `interactionH`);
`SigmaLayer/UntriggeredReadout.lean` (the readout half); `SigmaLayer/ChartIntegralCurve.lean`
(`hamiltonianCurve_unique`, `lipschitzWith_momentumH_field` — the idiom reused here);
`RecordLayer/MeasurementConstraints.lean` (`no_exact_collapse`, the consumer);
`SigmaLayer/ConstraintDynamics.lean` (`flow_preserves`, the predicate).
-/

@[expose] public section

namespace CSD.SigmaLayer

open MeasureTheory Matrix

variable {n : ℕ}

/-! ### The time-`t` map is linear: the two blocks -/

/-- The position block of the time-`t` map, `x ↦ x + t (c ⬝ x) e_k`, as the rank-one
perturbation of the identity `1 + (t e_k) cᵀ`. -/
noncomputable def posBlock (c : Fin n → ℝ) (k : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + vecMulVec (t • (Pi.single k 1 : Fin n → ℝ)) c

/-- The momentum block, `y ↦ y − t y_k c`, as `1 − (t c) e_kᵀ`. -/
noncomputable def momBlock (c : Fin n → ℝ) (k : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + vecMulVec (-(t • c)) (Pi.single k 1 : Fin n → ℝ)

/-- A rank-one matrix acting on a vector: `(u vᵀ) x = (v ⬝ x) u`, entrywise. -/
theorem vecMulVec_mulVec_apply (u v x : Fin n → ℝ) (j : Fin n) :
    (vecMulVec u v *ᵥ x) j = u j * (v ⬝ᵥ x) := by
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

theorem posBlock_mulVec (c : Fin n → ℝ) (k : Fin n) (t : ℝ) (x : Fin n → ℝ) :
    posBlock c k t *ᵥ x = fun j => if j = k then x k + t * ∑ i, c i * x i else x j := by
  classical
  funext j
  rw [posBlock, add_mulVec, one_mulVec, Pi.add_apply, vecMulVec_mulVec_apply]
  by_cases h : j = k
  · subst h
    simp [dotProduct]
  · simp [h]

theorem momBlock_mulVec (c : Fin n → ℝ) (k : Fin n) (t : ℝ) (y : Fin n → ℝ) :
    momBlock c k t *ᵥ y = fun j => y j - t * (c j * y k) := by
  funext j
  rw [momBlock, add_mulVec, one_mulVec, Pi.add_apply, vecMulVec_mulVec_apply,
    single_dotProduct]
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

/-- **The time-`t` map of the untriggered flow, as a linear endomorphism of the chart.** -/
noncomputable def untriggeredLin (c : Fin n → ℝ) (k : Fin n) (t : ℝ) : Chart n →ₗ[ℝ] Chart n :=
  (Matrix.toLin' (posBlock c k t)).prodMap (Matrix.toLin' (momBlock c k t))

/-- The linear map is the flow: `untriggeredLin c k t z = untriggeredCurve c k z t`. -/
theorem untriggeredLin_apply (c : Fin n → ℝ) (k : Fin n) (t : ℝ) (z : Chart n) :
    untriggeredLin c k t z = untriggeredCurve c k z t := by
  refine Prod.ext ?_ ?_
  · show Matrix.toLin' (posBlock c k t) z.1 = (untriggeredCurve c k z t).1
    rw [Matrix.toLin'_apply, posBlock_mulVec]
    rfl
  · show Matrix.toLin' (momBlock c k t) z.2 = (untriggeredCurve c k z t).2
    rw [Matrix.toLin'_apply, momBlock_mulVec]
    rfl

/-! ### The determinant is one -/

/-- The position shear has unit determinant: `det (1 + (t e_k) cᵀ) = 1 + t·c_k = 1`. -/
theorem det_posBlock (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (t : ℝ) :
    (posBlock c k t).det = 1 := by
  rw [posBlock, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, dotProduct_single, hck]
  simp

/-- The momentum shear has unit determinant: `det (1 − (t c) e_kᵀ) = 1 − t·c_k = 1`. -/
theorem det_momBlock (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (t : ℝ) :
    (momBlock c k t).det = 1 := by
  rw [momBlock, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_neg, dotProduct_smul, single_dotProduct, hck]
  simp

/-- **The time-`t` map has determinant one.** Block-diagonal, so the determinants multiply. -/
theorem det_untriggeredLin (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (t : ℝ) :
    LinearMap.det (untriggeredLin c k t) = 1 := by
  rw [untriggeredLin, LinearMap.det_prodMap, LinearMap.det_toLin', LinearMap.det_toLin',
    det_posBlock c k hck t, det_momBlock c k hck t, one_mul]

/-! ### ★★ Measure preservation -/

/-- Lebesgue measure on the chart is a Haar measure: the product of the two Haar measures on
the position and momentum blocks. (Instance search does not find the `Measure.prod` instance
through `volume` on the product by itself; this registers it for `Chart n`.) -/
instance instIsAddHaarMeasureVolumeChart :
    Measure.IsAddHaarMeasure (volume : Measure (Chart n)) :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℝ)) volume

/-- ★★ **The untriggered flow preserves chart volume.** A unit-determinant linear map pushes
Lebesgue measure to itself (`Measure.map_linearMap_addHaar_eq_smul_addHaar`). This is
`MeasurePreserving` in the corpus's own sense — the hypothesis every necessary condition in
`RecordLayer/MeasurementConstraints.lean` takes. -/
theorem untriggeredCurve_measurePreserving (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0)
    (t : ℝ) :
    MeasurePreserving (fun z => untriggeredCurve c k z t)
      (volume : Measure (Chart n)) volume := by
  have hfun : (fun z => untriggeredCurve c k z t) = ⇑(untriggeredLin c k t) := by
    funext z; exact (untriggeredLin_apply c k t z).symm
  rw [hfun]
  have hdet := det_untriggeredLin c k hck t
  refine ⟨(untriggeredLin c k t).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact one_ne_zero),
    hdet]
  simp

/-- Volume flows without compression or dilation: the set of initial states carried into a
measurable `A` has exactly the volume of `A`. -/
theorem volume_untriggered_preimage (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (t : ℝ)
    {A : Set (Chart n)} (hA : MeasurableSet A) :
    volume ((fun z => untriggeredCurve c k z t) ⁻¹' A) = volume A :=
  (untriggeredCurve_measurePreserving c k hck t).measure_preimage hA.nullMeasurableSet

/-- ★ **`no_exact_collapse` on the untriggered flow.** A positive-volume set of preparations
cannot be driven into a null set of states: on this flow too, collapse can only be relocation
of a null slice, never contraction of a positive-measure one. The first consumer of
`untriggeredCurve_measurePreserving`, showing it plugs into the existing constraints. -/
theorem untriggered_no_exact_collapse (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (t : ℝ)
    {C T : Set (Chart n)} (hT : NullMeasurableSet T volume) (hTnull : volume T = 0)
    (hsub : C ⊆ (fun z => untriggeredCurve c k z t) ⁻¹' T) (hCpos : volume C ≠ 0) : False :=
  RecordLayer.no_exact_collapse (untriggeredCurve_measurePreserving c k hck t) hT hTnull hsub
    hCpos

/-! ### ★ The field is linear, so the flow is *the* flow -/

/-- The Hamiltonian field of the coupling as a continuous linear map,
`z ↦ ((Σᵢ cᵢ xᵢ) e_k, −y_k c)`. -/
noncomputable def untriggeredField (c : Fin n → ℝ) (k : Fin n) : Chart n →L[ℝ] Chart n :=
  ((posCLM c).smulRight (Pi.single k 1 : Fin n → ℝ)).prod ((momCoord k).smulRight (-c))

/-- The field of `interactionH` is `untriggeredField` — linear, hence Lipschitz. -/
theorem hamiltonianField_interactionH (c : Fin n → ℝ) (k : Fin n) :
    hamiltonianField (interactionH (n := n) c k) = untriggeredField c k := by
  classical
  funext z
  refine Prod.ext ?_ ?_
  · funext i
    show dMom (interactionH c k) z i = _
    rw [dMom_interactionH]
    simp [untriggeredField, Pi.single_apply]
  · funext i
    show -(dPos (interactionH c k) z i) = _
    rw [dPos_interactionH]
    simp [untriggeredField]
    ring

/-- The coupling's field is Lipschitz, with constant the operator norm. -/
theorem lipschitzWith_interactionH_field (c : Fin n → ℝ) (k : Fin n) :
    LipschitzWith ‖untriggeredField c k‖₊ (hamiltonianField (interactionH (n := n) c k)) := by
  rw [hamiltonianField_interactionH]
  exact (untriggeredField c k).lipschitz

/-- ★ **The untriggered curve is THE integral curve.** Any integral curve of the coupling
through `z₀` at time `0` is `untriggeredCurve c k z₀` — the uniqueness brick 2's honest scope
left open, discharged from linearity via brick 0. -/
theorem untriggeredCurve_unique (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (z₀ : Chart n)
    {γ : ℝ → Chart n} (hγ : IsHamiltonianCurve (interactionH (n := n) c k) γ) (h₀ : γ 0 = z₀) :
    γ = untriggeredCurve c k z₀ :=
  hamiltonianCurve_unique (lipschitzWith_interactionH_field c k) hγ
    (untriggeredCurve_isHamiltonianCurve c k hck z₀) (t₀ := 0)
    (by rw [untriggeredCurve_zero]; exact h₀)

end CSD.SigmaLayer
