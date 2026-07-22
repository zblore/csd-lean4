/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.SigmaLayer.ProjectiveSector
import CsdLean4.SigmaLayer.TheoremTargets
import CsdLean4.LF4.ManyToOnePillars
import CsdLean4.LF4.KahlerVolumeForced

/-!
# SigmaLayer/MeasureBridge: the projective measure bridge and its concrete product proof

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Bridge assumption B1: the ontic measure pushes forward under `pi` to the required projective measure.
This is an explicit assumption interface in the abstract theory (`ProjectiveMeasureBridge`,
`HasFubiniStudyPushforward`), and a THEOREM for concrete models. Here the concrete model is the
many-to-one product sector `Sigma = CP^{N-1} x T^2`, `pi = Prod.fst`, `muL = muFS ⊗ vol`, adapted to the
SigmaLayer core from `manyToOneSchrodingerSetup`; the pushforward `pi_* muL = muFS` is discharged by the
existing `manyToOneSetup_baseVolume_eq_fubiniStudy` (which reuses `Measure.fst_prod`).

We do NOT install the Fubini-Study equality as a typeclass instance for every projective sector; it is a
named field / predicate, proved only where a concrete model supplies it.
-/

open MeasureTheory Matrix.UnitaryGroup

namespace CSD.SigmaLayer

universe u

/-- **Projective measure bridge (B1 interface).** A named assumption that `pi_* muL` equals a specified
target projective measure. Passive data, not a typeclass. -/
structure ProjectiveMeasureBridge {N : ℕ} {Sigma : Type u} [MeasurableSpace Sigma]
    {D : ConstraintDynamics Sigma} (Q : ProjectiveSector N D) where
  /-- The target projective measure. -/
  targetMeasure : Measure (ProjectiveState N)
  /-- The pushforward of the Liouville measure under `pi` equals the target. -/
  map_muL : Measure.map Q.pi (D.muL : Measure Sigma) = targetMeasure

/-- **The Fubini-Study pushforward predicate (B1 with a fixed target).** `pi_* muL = muFS`. A theorem
target for concrete models, not a global instance. -/
def HasFubiniStudyPushforward {N : ℕ} {Sigma : Type u} [MeasurableSpace Sigma]
    {D : ConstraintDynamics Sigma} (Q : ProjectiveSector N D)
    (p₀ : ProjectiveState N) : Prop :=
  Measure.map Q.pi (D.muL : Measure Sigma) = fubiniStudyMeasure p₀

/-! ### The concrete many-to-one product instance (B1 proved) -/

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CSD.LF4.CPN (M + 1))

/-- The many-to-one product sector as an SigmaLayer `ConstraintDynamics`, adapted from
`manyToOneSchrodingerSetup` (unitary flow `exp(-itH)` on the base ray, fibre fixed). The one-parameter
group laws come from `expNegITH_unitary_group`. -/
noncomputable def productDynamics : ConstraintDynamics (CSD.LF4.KSigma (M + 1)) :=
  haveI : IsFiniteMeasure (CSD.LF4.manyToOneSchrodingerSetup H hH p₀).liouvilleMeasure :=
    inferInstanceAs (IsFiniteMeasure (CSD.LF4.kMuL p₀))
  kahlerConstraintDynamics (CSD.LF4.manyToOneSchrodingerSetup H hH p₀)
    (fun x => by
      show (CSD.LF4.schrodingerUnitary hH 0 • x.1, x.2) = (x.1, x.2)
      rw [(CSD.LF4.expNegITH_unitary_group hH).2, one_smul])
    (fun s t x => by
      show (CSD.LF4.schrodingerUnitary hH (s + t) • x.1, x.2)
          = (CSD.LF4.schrodingerUnitary hH s • CSD.LF4.schrodingerUnitary hH t • x.1, x.2)
      rw [(CSD.LF4.expNegITH_unitary_group hH).1, mul_smul])

/-- The many-to-one product projective sector: `pi = Prod.fst` onto the ray space. -/
noncomputable def productSector : ProjectiveSector (M + 1) (productDynamics H hH p₀) :=
  kahlerProjectiveSector (CSD.LF4.manyToOneSchrodingerSetup H hH p₀)

/-- **B1 proved for the product model.** The projective law of the product Liouville measure is the
Fubini-Study measure: `pi_* (muFS ⊗ vol) = muFS`. Discharged by
`manyToOneSetup_baseVolume_eq_fubiniStudy`. This is the concrete instance of the measure bridge, not an
assumption. -/
theorem productSector_hasFubiniStudyPushforward :
    HasFubiniStudyPushforward (productSector H hH p₀) p₀ :=
  CSD.LF4.manyToOneSetup_baseVolume_eq_fubiniStudy (CSD.LF4.schrodingerUnitary hH) p₀

/-- The product measure bridge as a bundled `ProjectiveMeasureBridge` with target `muFS`. -/
noncomputable def productMeasureBridge : ProjectiveMeasureBridge (productSector H hH p₀) where
  targetMeasure := fubiniStudyMeasure p₀
  map_muL := productSector_hasFubiniStudyPushforward H hH p₀

end CSD.SigmaLayer
