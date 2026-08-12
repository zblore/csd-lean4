/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.SingletKahler

/-!
# WS-D witness: the LF2 measure bridge, concretely consumed

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-D).

The 2026-08-06 external review (F-01) observed that `MeasureBridgeData` was
carried type-level only; the G1 response added the two transport theorems in
which `bridge_eq` is **extensionally consumed** —
`MeasureBridgeData.integral_comp_pi` and
`OperationalPackage.fromPreparation_liouville_apply` (guarded by
`check-semantic-mutations.sh` CL-003). This module instantiates both on the
concrete Kähler bridge `kBridge p₀ : MeasureBridgeData (kSectorData p₀) μFS`
(`c = 1`, axiom-free), so the bridge is exercised as *data doing work* on an
actual instance, not phantom structure:

* `kBridge_integral_comp_pi` — the ontic integral over `Σ = ℂℙ³ × T²` of any
  projective integrand equals its Fubini–Study integral: an ontic volume
  computation carried into the projective probability, concretely;
* `kBridge_c_ne_zero` — nontriviality: the bridge constant is `1 ≠ 0`, so
  the transport is not the degenerate zero-scaling;
* `kSectorData_fromPreparation_liouville_apply` — the operational package
  built from the **ontic Liouville preparation** assigns every effect exactly
  its `μFS`-integral, on the concrete instance;
* `kPurePrep_born_rank_one` — the Born-form consequence recovered: the
  package built from the concrete fibre preparation assigns every rank-one
  effect the Born quadratic form `‖⟨ψ, φ⟩‖²`, via the production
  `born_rank_one_direct` (Busch-free, ontic stratum).

**Anti-duplication scope.** All four are instantiations: the transport
theorems, the bridge (`kBridge`), the preparation (`kPurePrep`), and the Born
step (`born_rank_one_direct`) are production; nothing is re-proved.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open CSD.LF4

namespace CSD
namespace Tests
namespace Witnesses

/-- **The bridge consumed on the concrete instance (transport form).** For any
`μFS`-a.e. strongly measurable projective integrand, the ontic integral over
`Σ = ℂℙ³ × T²` of its pullback along `π = Prod.fst` equals its Fubini–Study
integral. Instantiates `MeasureBridgeData.integral_comp_pi` at `kBridge p₀`
(where `c = 1`): `bridge_eq` is doing the work on an actual instance. -/
theorem kBridge_integral_comp_pi (p₀ : CPN 4) {f : CPN 4 → ℝ}
    (hf : AEStronglyMeasurable f (fubiniStudyMeasure p₀)) :
    ∫ σ : KSigma 4, f σ.1 ∂(kMuL p₀) = ∫ p, f p ∂(fubiniStudyMeasure p₀) := by
  have h := LF2.MeasureBridgeData.integral_comp_pi (kBridge p₀) hf
  simp only [show (kBridge p₀).c = 1 from rfl, ENNReal.toReal_one, one_smul] at h
  exact h

/-- **Nontriviality.** The concrete bridge constant is `1`, not `0`: the
transport `π_*μL = c • μFS` is a genuine identification of the two volumes,
not the degenerate zero-scaling. -/
theorem kBridge_c_ne_zero (p₀ : CPN 4) : (kBridge p₀).c ≠ 0 := by
  rw [show (kBridge p₀).c = 1 from rfl]
  exact one_ne_zero

/-- The concrete instance's Liouville measure is a probability measure,
surfaced on the `SectorData` projection (`(kSectorData p₀).μL = kMuL p₀`
definitionally; the production instance is `instProbKMuL`). -/
instance instProbKSectorDataMuL (p₀ : CPN 4) :
    IsProbabilityMeasure (kSectorData p₀).μL := by
  show IsProbabilityMeasure (kMuL p₀)
  infer_instance

/-- **The bridge consumed on the concrete instance (operational form).** The
operational package built from the **ontic Liouville preparation** `kMuL p₀`
assigns to every effect exactly its `μFS`-integral. Instantiates
`OperationalPackage.fromPreparation_liouville_apply` at `kBridge p₀` with
`hc : c = 1` discharged by `rfl`. -/
theorem kSectorData_fromPreparation_liouville_apply (p₀ : CPN 4) (E : LF2.Effect 4) :
    (LF2.OperationalPackage.fromPreparation (kSectorData p₀) (fubiniStudyMeasure p₀)
        (kBridge p₀) ((kSectorData p₀).μL) kRep kRep_unit kRep_meas).p E
      = ∫ p, LF2.effectProjFn kRep E p ∂(fubiniStudyMeasure p₀) :=
  LF2.OperationalPackage.fromPreparation_liouville_apply
    (kSectorData p₀) (fubiniStudyMeasure p₀) (kBridge p₀) rfl
    kRep kRep_unit kRep_meas E

/-- **The Born-form consequence on the concrete instance.** The operational
package built from the concrete fibre preparation `kMuPsi` assigns every
rank-one effect the Born quadratic form `‖⟨ψ, φ⟩‖²` (`ψ = singletPsi`).
Instantiates the production `born_rank_one_direct` (Busch-free) at
`kPurePrep p₀`. -/
theorem kPurePrep_born_rank_one (p₀ : CPN 4)
    (φ : EuclideanSpace ℂ (Fin 4)) (hφ : ‖φ‖ = 1) :
    (LF2.OperationalPackage.fromPreparation (kSectorData p₀) (fubiniStudyMeasure p₀)
        (kBridge p₀) kMuPsi kRep kRep_unit kRep_meas).p (LF2.rankOneEffect φ hφ)
      = ‖inner ℂ singletPsi φ‖ ^ 2 :=
  LF2.PurePreparation.born_rank_one_direct (kSectorData p₀) (fubiniStudyMeasure p₀)
    (kBridge p₀) kMuPsi (kPurePrep p₀) φ hφ

end Witnesses
end Tests
end CSD
