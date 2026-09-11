/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.FlowChannel
public import CsdLean4.LF6.DecoherenceChannel
public import CsdLean4.Thermo.SigmaSecondLaw
public import CsdLean4.LF5.MeasurementFlow

/-!
# LF5's measurement flow produces the de-isolation channel

**Category:** 3-Local (W6′ of `specs/qit-chain-scoping.md`; the joint-index instance that closes
the loop from LF5's ontic flow to the channel of `LF6/DecoherenceChannel.lean`).

`LF2/FlowChannel.lean` proves that a flow lifting a unitary produces the Stinespring channel of
that unitary, with the lift hypothesis a theorem for the projective unitary action at index
`Fin N` (`isUnitaryLift_of_smul`). LF5's measurement flow (`LF5/MeasurementFlow.lean`) is such an
action, but on the dilated space reindexed along `e : Fin N × Fin N ≃ Fin m`, because the
Fubini-Study infrastructure is `Fin m`-indexed. This module carries the lift back across the
reindexing and instantiates the W6/W7 theorems on LF5's flow:

* `isUnitaryLift_measurementFlow` — an ontic sector over the dilated projective space whose flow
  projects to `measurementFlow N e`, with any unit section of the ray map, lifts `vnUnitary N` on
  the joint index through the representative transported back along `e`
  (`isUnitaryLift_of_reindex`, `LF2/FlowChannel.lean`);
* ★★ `measurementFlow_traceRight_barycenter` — for a preparation on that sector, product with the
  apparatus ready in `a₀`, the reduced density operator of the flowed preparation is
  `deisolationChannel N` applied to the system's density operator: **the de-isolation channel is
  the environment marginal of LF5's flow**;
* ★ `measurementFlow_vonNeumannEntropy_le` — the second law under LF5's flow: the system's
  reduced entropy after the flow is at least its entropy before (TH2's full-support hypothesis).

## Honest scope

**The unit section.** The general theorems take a unit-norm measurable section `rep'` of the ray
map (`mk (rep' p) = p`), as `fromPreparation` does; `Projectivization.unitSection`
(`Mathlib/LinearAlgebra/Projectivization/UnitSection.lean`, W6″) is one, canonical and Borel
measurable, and `measurementFlow_traceRight_barycenter_unitSection` is the theorem with it
supplied, so no section hypothesis remains.

⚠️ **The product form is a hypothesis.** That the joint preparation is the system preparation
tensored with the ready apparatus, at the projector level and almost everywhere, is what "the
apparatus starts in `a₀`" means for a preparation; it is not derived from the sector.

References: `specs/qit-chain-scoping.md` (W6′); `LF2/FlowChannel.lean` (W6);
`LF6/DecoherenceChannel.lean` (W5 witness); `Thermo/SigmaSecondLaw.lean` (W7);
`LF5/MeasurementFlow.lean` (`measurementFlow`, `vnUnitaryReindexed`).
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CSD

/-! ### LF5's measurement flow lifts the von Neumann coupling -/

namespace LF6

open CSD.LF2 CSD.LF5

variable {N : ℕ} [NeZero N] {m : ℕ}
  {SigmaSpace G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G (ℙ ℂ (EuclideanSpace ℂ (Fin m)))]
  [MulAction.IsPretransitive G (ℙ ℂ (EuclideanSpace ℂ (Fin m)))]

/-- **The joint-index instance (W6′).** An ontic sector over the dilated projective space whose
flow projects to LF5's `measurementFlow N e` (the projective action of the reindexed von Neumann
coupling), with any unit section `rep'` of the ray map, lifts `vnUnitary N` on the joint index
`Fin N × Fin N`, through the representative transported back along `e`. -/
theorem isUnitaryLift_measurementFlow (e : Fin N × Fin N ≃ Fin m)
    (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin m))) G)
    (Φ : SigmaSpace → SigmaSpace)
    (hproj : ∀ x, D.π (Φ x) = measurementFlow N e (D.π x))
    (rep' : ℙ ℂ (EuclideanSpace ℂ (Fin m)) → EuclideanSpace ℂ (Fin m))
    (hrep_unit : ∀ p, ‖rep' p‖ = 1) (hrep_ne : ∀ p, rep' p ≠ 0)
    (hsec : ∀ p, Projectivization.mk ℂ (rep' p) (hrep_ne p) = p) :
    IsUnitaryLift D Φ (fun p => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm (rep' p))
      (vnUnitary N) := by
  have : NeZero m := ⟨fun h => Fin.elim0 (h ▸ e ((0 : Fin N), 0))⟩
  refine isUnitaryLift_of_reindex D Φ e _ (vnUnitary N) fun x => ?_
  have h := isUnitaryLift_of_smul D Φ (vnUnitaryReindexed N e) hproj rep' hrep_unit hrep_ne hsec x
  rw [vnUnitaryReindexed_val] at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

/-! ### The de-isolation channel is the environment marginal of that flow -/

/-- ★★ **LF5's measurement flow produces the de-isolation channel.** For a preparation on a sector
over the dilated projective space whose flow projects to `measurementFlow N e`, with a unit
section of the ray map and the preparation a product with the apparatus ready in `a₀` (a.e., at
the projector level, in the representative transported back to `Fin N × Fin N`), the reduced
density operator of the flowed preparation is `deisolationChannel N` applied to the system's
density operator. The loop from the ontic flow of LF5 to the channel of `LF6/DecoherenceChannel`
closes: the de-isolation channel is the environment marginal of that flow. -/
theorem measurementFlow_traceRight_barycenter (e : Fin N × Fin N ≃ Fin m)
    (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin m))) G)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (hproj : ∀ x, D.π (Φ x) = measurementFlow N e (D.π x))
    (rep' : ℙ ℂ (EuclideanSpace ℂ (Fin m)) → EuclideanSpace ℂ (Fin m))
    (hrep_unit : ∀ p, ‖rep' p‖ = 1) (hrep_ne : ∀ p, rep' p ≠ 0)
    (hsec : ∀ p, Projectivization.mk ℂ (rep' p) (hrep_ne p) = p) (hrep_meas : Measurable rep')
    (repS : ℙ ℂ (EuclideanSpace ℂ (Fin m)) → EuclideanSpace ℂ (Fin N)) (hrepS_meas : Measurable repS)
    (hprod : ∀ᵐ x ∂μprep,
      outerProduct ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm (rep' (D.π x)))
        = outerProduct (repS (D.π x)) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin N) (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix
        (fun p => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm (rep' p))
        (Measure.map D.π (Measure.map Φ μprep)))
      = (deisolationChannel N).apply (barycenterMatrix repS (Measure.map D.π μprep)) :=
  traceRight_barycenter_flow D μprep Φ hΦ _
    (fun p => by simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, hrep_unit])
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.continuous.measurable.comp hrep_meas)
    repS hrepS_meas (vnUnitary N) vnUnitary_conjTranspose_mul _
    (by rw [PiLp.norm_single]; exact norm_one)
    (isUnitaryLift_measurementFlow e D Φ hproj rep' hrep_unit hrep_ne hsec) hprod

/-- ★ **The second law under LF5's measurement flow**: the entropy of the system's reduced
density operator after the flow is at least its entropy before (full support of the system
state assumed, TH2's hypothesis). -/
theorem measurementFlow_vonNeumannEntropy_le (e : Fin N × Fin N ≃ Fin m)
    (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin m))) G)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (hproj : ∀ x, D.π (Φ x) = measurementFlow N e (D.π x))
    (rep' : ℙ ℂ (EuclideanSpace ℂ (Fin m)) → EuclideanSpace ℂ (Fin m))
    (hrep_unit : ∀ p, ‖rep' p‖ = 1) (hrep_ne : ∀ p, rep' p ≠ 0)
    (hsec : ∀ p, Projectivization.mk ℂ (rep' p) (hrep_ne p) = p) (hrep_meas : Measurable rep')
    (repS : ℙ ℂ (EuclideanSpace ℂ (Fin m)) → EuclideanSpace ℂ (Fin N))
    (hrepS_unit : ∀ p, ‖repS p‖ = 1) (hrepS_meas : Measurable repS)
    (hprod : ∀ᵐ x ∂μprep,
      outerProduct ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm (rep' (D.π x)))
        = outerProduct (repS (D.π x)) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin N) (1 : ℂ)))
    (hpos : ∀ i, 0 < ((barycenterMatrix repS (Measure.map D.π μprep)) i i).re) :
    vonNeumannEntropy (barycenterMatrix_isHermitian repS (Measure.map D.π μprep))
      ≤ vonNeumannEntropy (barycenterMatrix_isHermitian
          (fun p => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm (rep' p))
          (Measure.map D.π (Measure.map Φ μprep))).traceRight :=
  Thermo.vonNeumannEntropy_le_deisolation D μprep Φ hΦ _
    (fun p => by simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, hrep_unit])
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.continuous.measurable.comp hrep_meas)
    repS hrepS_unit hrepS_meas
    (isUnitaryLift_measurementFlow e D Φ hproj rep' hrep_unit hrep_ne hsec) hprod hpos

/-- ★★ **Unconditional form**: with the canonical measurable unit section as representative, the
section hypotheses disappear. The reduced density operator of the flowed preparation is the
de-isolation channel applied to the system's density operator, for every preparation on a sector
whose flow projects to LF5's measurement flow and is a product with the apparatus ready. -/
theorem measurementFlow_traceRight_barycenter_unitSection (e : Fin N × Fin N ≃ Fin m)
    (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin m))) G)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (hproj : ∀ x, D.π (Φ x) = measurementFlow N e (D.π x))
    (repS : ℙ ℂ (EuclideanSpace ℂ (Fin m)) → EuclideanSpace ℂ (Fin N)) (hrepS_meas : Measurable repS)
    (hprod : ∀ᵐ x ∂μprep,
      outerProduct ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm
          (Projectivization.unitSection (D.π x)))
        = outerProduct (repS (D.π x)) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin N) (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix
        (fun p => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm (Projectivization.unitSection p))
        (Measure.map D.π (Measure.map Φ μprep)))
      = (deisolationChannel N).apply (barycenterMatrix repS (Measure.map D.π μprep)) :=
  measurementFlow_traceRight_barycenter e D μprep Φ hΦ hproj Projectivization.unitSection
    Projectivization.norm_unitSection Projectivization.unitSection_ne_zero
    Projectivization.mk_unitSection Projectivization.measurable_unitSection repS hrepS_meas hprod

end LF6
end CSD
