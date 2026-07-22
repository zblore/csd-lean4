/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ConstraintDynamics
public import CsdLean4.SigmaLayer.RecordedFact
public import CsdLean4.LF1.Preparation

/-!
# SigmaLayer/IsolationPreparation: preparations and isolation as conditioning on a record history

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

A `Preparation` restricts the ontic state to a measurable region of nonzero Liouville measure. The LF1
adapter (`Preparation.toOnticSetup`) turns a preparation plus a time into an existing `LF1.OnticSetup`,
so the isolated epistemic law reuses LF1's normalised conditional measure `prepMeasure` rather than a
second independent normalisation.

Postulate P6: during isolation no new record is established, and the probability law is conditional
uncertainty over `Sigma` given the existing record history. `HistoryPreparation` realises this: its
region is the compatible region of the history (`compatibleSet`), and its conditional measure is the
ordinary conditioning `muH(A) = muL(A ∩ compatible) / muL(compatible)`. This is the epistemic law
conditional on the record history, not an additional ontic state.
-/

@[expose] public section

open MeasureTheory

namespace CSD.SigmaLayer

universe u v w

variable {Sigma : Type w} [MeasurableSpace Sigma] [Nonempty Sigma]

/-- **A preparation.** A measurable ontic region of nonzero Liouville measure. -/
structure Preparation (D : ConstraintDynamics Sigma) where
  /-- The preparation region. -/
  region : Set Sigma
  /-- The region is measurable. -/
  measurable_region : MeasurableSet region
  /-- The region has nonzero Liouville measure, so normalisation is well defined. -/
  nonzero_region : (D.muL : Measure Sigma) region ≠ 0

namespace Preparation

variable {D : ConstraintDynamics Sigma}

/-- **The LF1 adapter (fixed time step).** A preparation and a time `t` yield an existing
`LF1.OnticSetup`: `muL` to `μL`, `flow t` to `Φ`, `flow_preserves t` to `hΦ_pres`, `region` to `Ω0`. -/
def toOnticSetup (P : Preparation D) (t : OnticTime) : CSD.LF1.OnticSetup Sigma where
  μL := D.muL
  Φ := D.flow t
  hΦ_pres := D.flow_preserves t
  Ω0 := P.region
  hΩ0_meas := P.measurable_region
  hΩ0_nonzero := P.nonzero_region

/-- **The isolated (conditional) preparation law.** Reuses LF1's normalised conditional measure
`prepMeasure`; it depends only on `muL` and `region`, so `t = 0` instantiates the adapter. This is the
epistemic law conditional on the preparation region, not an additional ontic state. -/
noncomputable def conditionalMeasure (P : Preparation D) : ProbabilityMeasure Sigma :=
  (P.toOnticSetup 0).prepMeasure

/-- The conditional preparation law is the LF1 normalised conditional measure: for measurable `A`,
`muH(A) = muL(A ∩ region) / muL(region)` (reusing `LF1.OnticSetup.prepMeasure_apply`). -/
theorem conditionalMeasure_apply (P : Preparation D) (A : Set Sigma) (hA : MeasurableSet A) :
    ((P.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma) A =
      (D.muL : Measure Sigma) (A ∩ P.region) / (D.muL : Measure Sigma) P.region :=
  (P.toOnticSetup 0).prepMeasure_apply A hA

end Preparation

/-- **An isolation preparation from a record history (postulate P6).** No new record is established;
the compatible region of the existing history has nonzero Liouville measure. -/
structure HistoryPreparation (D : ConstraintDynamics Sigma) (R : RecordSignature)
    (S : RecordSemantics Sigma R) where
  /-- The existing record history. -/
  history : RecordHistory R
  /-- The compatible region of the history has nonzero Liouville measure. -/
  nonzero_compatible : (D.muL : Measure Sigma) (compatibleSet S history) ≠ 0

namespace HistoryPreparation

variable {D : ConstraintDynamics Sigma} {R : RecordSignature} {S : RecordSemantics Sigma R}

/-- The isolation preparation as an SigmaLayer `Preparation`, with region the compatible region of the
history. -/
def toPreparation (HP : HistoryPreparation D R S) : Preparation D where
  region := compatibleSet S HP.history
  measurable_region := compatibleSet_measurable S HP.history
  nonzero_region := HP.nonzero_compatible

/-- **The isolated epistemic law.** For measurable `A`,
`muH(A) = muL(A ∩ compatibleSet history) / muL(compatibleSet history)`: ordinary conditioning on the
record history, reusing the LF1 normalised conditional measure. -/
theorem conditionalMeasure_apply (HP : HistoryPreparation D R S) (A : Set Sigma)
    (hA : MeasurableSet A) :
    ((HP.toPreparation.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma) A =
      (D.muL : Measure Sigma) (A ∩ compatibleSet S HP.history) /
        (D.muL : Measure Sigma) (compatibleSet S HP.history) :=
  HP.toPreparation.conditionalMeasure_apply A hA

end HistoryPreparation

end CSD.SigmaLayer
