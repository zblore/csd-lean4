/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MomentMapRace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# SigmaLayer/FibredSigma: the fibred ontic space Σ = base × fibre (MD-1)

**Category:** 7-SigmaLayer (the record layer — the base×fibre ontic space).

Assembles the honest CSD ontic space as a **product** `Σ = base × fibre = CPN n × ℝ`, realising the
epistemic/ontic split of Papers C/D directly in the geometry:

* the **base** `CPN n = ℂℙⁿ⁻¹` carries the *epistemic* projective point — for a sharp preparation `ψ`
  it is pinned to `[ψ]` (`baseProj_sharpTypicality`), matching Paper C's epistemic outcome regions
  `Ωᵢ(M)` living on projective space;
* the **fibre** `ℝ` carries the *ontic* record coordinate — the measurement carves the fibre into the
  Born partition (`cdfCell`), and the outcome is the fibre point's basin;
* the **projection** `baseProj = π : Σ → base` recovers the epistemic point from the ontic state.

For a sharp preparation the typicality measure is `sharpTypicality = δ_{[ψ]} ⊗ fibreTypicality` — the
base pinned (Dirac), the fibre uniform — so the ontic support is `{[ψ]} × [0,1)`. The Born weight of an
outcome is then the product-measure typicality of its fibre event, which is exactly the fibre measure
(`sharpTypicality_fibredEvent`): `‖ψ i‖²`, the Kähler moment map (`sharpTypicality_fibredEvent_momentMap`).

So this ties `SigmaLayer/FibreRecord.lean` (the fibre) to the projective base: the ψ-dependence sits in
the *base* (the epistemic point / the preparation), the *fibre* carries the context-fixed outcome
partition, and Born is the ontic typicality of the fibre event over the pinned base — the epistemic
(base) / ontic (fibre) split made literal. Foundational-triple, no `sorry`.

## References
`specs/record-layer-plan.md` (record layer, MD-1; epistemic base / ontic fibre); `SigmaLayer/FibreRecord.lean`
(the fibre partition + record); `SigmaLayer/MomentMapRace.lean` (`bornRate_eq_momentMap`); Paper C A7
(epistemic `Ωᵢ(M)` ⊂ ℂℙⁿ⁻¹), Paper D (ontic/epistemic split).
-/

@[expose] public section

open MeasureTheory Set
open CSD.LF4

namespace CSD.RecordLayer

variable {n : ℕ}

/-- The **fibred ontic space** `Σ = base × fibre = CPN n × ℝ`: the base is the epistemic projective
point, the fibre the ontic record coordinate. -/
abbrev FibredSigma (n : ℕ) := CPN n × ℝ

/-- The **projection to the epistemic base** `π : Σ → CPN n`. -/
def baseProj : FibredSigma n → CPN n := Prod.fst

/-- The **sharp-preparation typicality measure**: `δ_{[ψ]} ⊗ fibreTypicality` — the base pinned at the
epistemic point `[ψ]`, the fibre uniform on `[0,1)`. Ontic support `{[ψ]} × [0,1)`. -/
noncomputable def sharpTypicality (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) :
    Measure (FibredSigma n) :=
  (Measure.dirac (Projectivization.mk ℂ ψ hψ0)).prod fibreTypicality

instance (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) :
    IsProbabilityMeasure (sharpTypicality ψ hψ0) := by
  rw [sharpTypicality]; infer_instance

/-- The **fibre event** of outcome `i`: the ontic states whose fibre coordinate lies in the Born
partition cell `i` (any base). The outcome depends only on the fibre. -/
def fibredEvent (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) : Set (FibredSigma n) :=
  Set.univ ×ˢ cdfCell (bornRate ψ) i

theorem mem_fibredEvent_iff (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) (ω : FibredSigma n) :
    ω ∈ fibredEvent ψ i ↔ ω.2 ∈ cdfCell (bornRate ψ) i := by
  simp [fibredEvent]

/-- **The base is pinned to the epistemic point.** For a sharp preparation the projection `π` sends the
typicality measure to the Dirac at `[ψ]`: the base coordinate is epistemically fixed at `[ψ]`. -/
theorem baseProj_sharpTypicality (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) :
    Measure.map baseProj (sharpTypicality ψ hψ0) = Measure.dirac (Projectivization.mk ℂ ψ hψ0) := by
  rw [baseProj, sharpTypicality]
  exact Measure.fst_prod

/-- **Born = the ontic typicality of the fibre event on the assembled Σ.** For a unit state the
`sharpTypicality` measure of the outcome-`i` fibre event is exactly `‖ψ i‖²` — the base being pinned
(Dirac, mass `1`) contributes nothing, so the Born weight is the fibre typicality of the cell. -/
theorem sharpTypicality_fibredEvent (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin n) :
    sharpTypicality ψ hψ0 (fibredEvent ψ i) = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  rw [sharpTypicality, fibredEvent, Measure.prod_prod, measure_univ, one_mul,
    fibreTypicality_bornCell ψ hψ i]

/-- The Born weight of the fibre event is the Kähler moment-map coordinate at `[ψ]`. -/
theorem sharpTypicality_fibredEvent_momentMap (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin n) :
    sharpTypicality ψ hψ0 (fibredEvent ψ i)
      = ENNReal.ofReal (momentMap (Projectivization.mk ℂ ψ hψ0) i) := by
  rw [sharpTypicality_fibredEvent ψ hψ0 hψ i]
  congr 1
  exact bornRate_eq_momentMap ψ hψ0 hψ i

end CSD.RecordLayer
