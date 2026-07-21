import CsdLean4.SigmaLayer.DynamicsBridge
import CsdLean4.SigmaLayer.MeasurementRecord

/-!
# FND/ForwardCapstone: the product-model forward capstone

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

The first achievable FND capstone, combining only currently proved components on the concrete
many-to-one product sector `Sigma = CP^{N-1} x T^2`, `pi = Prod.fst`, `muL = muFS ⊗ vol`, with the
`exp(-itH)` unitary flow on the base ray:

1. deterministic measure-preserving ontic flow (`ConstraintDynamics.flow_preserves`);
2. projectability through `pi` to the projected flow `exp(-itH) • ·` (`ProjectiveDynamicsBridge`);
3. a Hamiltonian (Schrödinger) realisation of the projected flow (theorem target T5, inhabited);
4. the Fubini-Study measure bridge `pi_* muL = muFS` (bridge B1, proved for this product model).

## What this capstone does NOT claim

It is named `product_projectiveSector_forward_capstone`, not `finiteQM_complete`. It does NOT claim: general
Born-from-flow; general unitary dynamics beyond this instance; general Lüders update; composite-system
results; no-signalling; Bell reconstruction; nor the contextual pointer readout and almost-everywhere
unique outcome (which need a concrete `DeisolationModel` instance from the LF5 pointer machinery, the
named Tranche 2b piece). The independent-trial Born-frequency theorem
`LF4.manyToOneSetup_born_frequency` applies to sampling this model's `muL`; the connection is
`productDynamics_muL_eq`.

## Assumption report

The capstone `product_projectiveSector_forward_capstone` has NO hypotheses beyond `(H, hH, p₀)` (a Hermitian
generator and a basepoint). Every conjunct is discharged by a proved theorem; there are no bridge
assumptions left open in the statement. `#print axioms` shows the foundational triple only.
-/

open MeasureTheory Matrix.UnitaryGroup

namespace CSD.SigmaLayer

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CSD.LF4.CPN (M + 1))

/-- The FND product Liouville measure is the LF4 product measure `muFS ⊗ vol`, so the existing
independent-trial Born-frequency theorem `LF4.manyToOneSetup_born_frequency` (stated for
`liouvilleMeasure`) applies directly to sampling the FND `productDynamics.muL`. -/
theorem productDynamics_muL_eq :
    ((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
      = (CSD.LF4.manyToOneSchrodingerSetup H hH p₀).liouvilleMeasure := rfl

/-- **The product-model projective sector forward capstone.** For the many-to-one product sector with the
`exp(-itH)` flow, the following hold with no open hypotheses:

* the ontic flow is measure-preserving;
* it projects through `pi = Prod.fst` to `exp(-itH) • ·`;
* the projected flow has a Hamiltonian (Schrödinger) realisation (target T5);
* `pi_*(muFS ⊗ vol) = muFS` (bridge B1).

This is the forward delivery of the projective dynamics and the measure bridge from the projective sector ontic
sector for this concrete model, combining only proved components. -/
theorem product_projectiveSector_forward_capstone :
    (∀ t x, (productSector H hH p₀).pi ((productDynamics H hH p₀).flow t x)
        = productProjectedFlow H hH t ((productSector H hH p₀).pi x))
    ∧ HasHamiltonianRealisation (productProjectedFlow H hH)
    ∧ HasFubiniStudyPushforward (productSector H hH p₀) p₀
    ∧ (∀ t, MeasurePreserving ((productDynamics H hH p₀).flow t)
        ((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
        ((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))) :=
  ⟨(productDynamicsBridge H hH p₀).projectable,
    productProjectedFlow_hasHamiltonianRealisation H hH,
    productSector_hasFubiniStudyPushforward H hH p₀,
    (productDynamics H hH p₀).flow_preserves⟩

end CSD.SigmaLayer

