/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QEC.ThreeQubit
public import CsdLean4.Empirical.QM.QEC.RegisterDilation

/-!
# Empirical/CSD: the three-qubit register ⊗ environment as one `Σ`-flow, and QEC on `Σ`

**Category:** 3-Local (CSD-side companion to `Empirical/QM/QEC/RegisterDilation.lean`; closes the
register ⊗ environment residue of `Empirical/CSD/QEC/ThreeQubit.lean`).

`QEC/ThreeQubit.lean` produced the *one-qubit* bit-flip channel from a `Σ`-flow on qubit ⊗ qubit
(`bitFlipFlow_traceRight_barycenter`) and read the code and the syndrome as regions of `Σ`.
`QM/QEC/SyndromeRecovery.lean` then made the syndrome-conditioned recovery one channel on the
mixed state. This file puts the pieces on the **whole register**:

* `registerFlow q` — the projective action of the register's joint unitary `U_q`
  (`QM/QEC/RegisterDilation.lean`) on `ℂℙ³¹`, the joint projective space of the three-qubit
  register ⊗ the four-level "which-error" environment; a flow of the corpus's `cpSectorData` over
  `ℂℙ³¹`, lifting `U_q` with no hypothesis (`isUnitaryLift_registerFlow`, through the canonical
  measurable unit section);
* ★★ `registerFlow_traceRight_barycenter` — **the register's single-error channel is the
  environment marginal of the joint `Σ`-flow**: for a preparation that is a product with the
  environment ready, the reduced density operator of the flowed preparation is
  `singleFlipChannel q` applied to the register's density operator;
* ★★★ `registerFlow_recovery` — **QEC on `Σ`, end to end**: if the register preparation lives in
  the code region (`P₀ (rep x) = rep x` a.e.), then the syndrome-conditioned recovery channel
  applied to the environment marginal of the flowed preparation returns the register's density
  operator. The error is the `Σ`-flow's leak into the environment; the syndrome measurement is
  the projective measurement whose outcomes are the four disjoint error regions of `Σ`
  (`syndromeProj_fixes_errorRegion`); the recovery undoes the leak exactly.

What is not here: the independent-noise channel `(bit-flip_p)^{⊗3}` (its double- and triple-flip
branches are not correctable; `singleFlipChannel` is the correctable part with free weights), and
a Hamiltonian generating `U_q` (the flow is the time-one map of the projective action, as for
`bitFlipFlow`).

## Source

Shor 1995, *Phys. Rev. A* **52**, R2493; Knill–Laflamme 1997, *Phys. Rev. A* **55**, 900.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QEC

open CSD.LF2 CSD.Empirical.QM.QEC

/-! ### The joint index as `Fin 32`, and the flow on `ℂℙ³¹` -/

/-- The joint index `(register) × (environment) = (Fin 2 × Fin 2 × Fin 2) × Fin 4` as `Fin 32`. -/
def registerEquiv : (Fin 2 × Fin 2 × Fin 2) × Fin 4 ≃ Fin 32 :=
  (Equiv.prodCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv)
    (Equiv.refl (Fin 4))).trans finProdFinEquiv

/-- The register's joint unitary as an element of `U(32)`, reindexed to `Fin 32`. -/
noncomputable def registerU32 (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix.unitaryGroup (Fin 32) ℂ :=
  ⟨Matrix.reindex registerEquiv registerEquiv (registerUnitary q hq0 hq1),
    CSD.LF5.reindex_mem_unitaryGroup registerEquiv
      (Matrix.mem_unitaryGroup_iff'.mpr (by
        rw [Matrix.star_eq_conjTranspose]; exact registerUnitary_conjTranspose_mul q hq0 hq1))⟩

theorem registerU32_val (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    ((registerU32 q hq0 hq1 : Matrix.unitaryGroup (Fin 32) ℂ) : Matrix (Fin 32) (Fin 32) ℂ)
      = Matrix.reindex registerEquiv registerEquiv (registerUnitary q hq0 hq1) := rfl

/-- **The register's de-isolation flow** on `ℂℙ³¹`: the projective action of `U_q`. A flow of the
corpus's `cpSectorData` (`Σ = P = ℂℙ³¹`, `π = id`). -/
noncomputable def registerFlow (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    CSD.LF4.CPN 32 → CSD.LF4.CPN 32 :=
  fun x => registerU32 q hq0 hq1 • x

theorem measurable_registerFlow (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Measurable (registerFlow q hq0 hq1) :=
  (continuous_const_smul (registerU32 q hq0 hq1)).measurable

/-- The joint representative: the canonical unit section of `ℂℙ³¹`, transported to the joint
index. -/
noncomputable def registerRep : CSD.LF4.CPN 32 → EuclideanSpace ℂ ((Fin 2 × Fin 2 × Fin 2) × Fin 4) :=
  fun x => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ registerEquiv).symm (Projectivization.unitSection x)

theorem registerRep_norm (x : CSD.LF4.CPN 32) : ‖registerRep x‖ = 1 := by
  simp only [registerRep, LinearIsometryEquiv.norm_map, Projectivization.norm_unitSection]

theorem measurable_registerRep : Measurable registerRep :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ registerEquiv).symm.continuous.measurable.comp
    Projectivization.measurable_unitSection

/-- ★ **The register flow lifts `U_q`**, with no hypotheses. -/
theorem isUnitaryLift_registerFlow (p₀ : CSD.LF4.CPN 32) (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    IsUnitaryLift (CSD.LF4.cpSectorData p₀) (registerFlow q hq0 hq1) registerRep
      (registerUnitary q hq0 hq1) :=
  isUnitaryLift_of_reindex (CSD.LF4.cpSectorData p₀) (registerFlow q hq0 hq1) registerEquiv _ _
    (by
      have h := isUnitaryLift_of_smul (CSD.LF4.cpSectorData p₀) (registerFlow q hq0 hq1)
        (registerU32 q hq0 hq1) (fun _ => rfl) Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.unitSection_ne_zero
        Projectivization.mk_unitSection
      intro x
      have hx := h x
      rw [registerU32_val] at hx
      simpa only [registerRep, LinearIsometryEquiv.apply_symm_apply] using hx)

/-! ### The single-error channel as the environment marginal of the flow, and QEC on `Σ` -/

/-- ★★ **The register's single-error channel is the environment marginal of the joint `Σ`-flow.**
For a preparation on `ℂℙ³¹` that is a product with the environment ready (a.e., in the canonical
representative, with register representative `repS`), the reduced density operator of the flowed
preparation is `singleFlipChannel q` applied to the register's density operator. -/
theorem registerFlow_traceRight_barycenter (p₀ : CSD.LF4.CPN 32)
    (μprep : Measure (CSD.LF4.CPN 32)) [IsProbabilityMeasure μprep]
    (repS : CSD.LF4.CPN 32 → EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)) (hrepS_meas : Measurable repS)
    (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (hprod : ∀ᵐ x ∂μprep, outerProduct (registerRep x)
      = outerProduct (repS x) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin 4) (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix registerRep
        (Measure.map (CSD.LF4.cpSectorData p₀).π (Measure.map (registerFlow q hq0 hq1) μprep)))
      = (singleFlipChannel q hq0 hq1).apply
          (barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep)) := by
  rw [← stinespringChannel_registerUnitary q hq0 hq1]
  exact traceRight_barycenter_flow (CSD.LF4.cpSectorData p₀) μprep (registerFlow q hq0 hq1)
    (measurable_registerFlow q hq0 hq1) registerRep registerRep_norm measurable_registerRep
    repS hrepS_meas (registerUnitary q hq0 hq1) (registerUnitary_conjTranspose_mul q hq0 hq1) _
    (by rw [PiLp.norm_single]; exact norm_one) (isUnitaryLift_registerFlow p₀ q hq0 hq1) hprod

/-- ★★★ **QEC on `Σ`, end to end.** Let the register preparation live in the code region
(`P₀ (repS x) = repS x` a.e.: every prepared ray lies in the codespace `ℂℙ¹ ⊂ ℂℙ⁷`), the
environment be ready, and the joint `Σ`-flow be `registerFlow q`. Then the syndrome-conditioned
recovery channel, applied to the environment marginal of the flowed preparation, returns the
register's density operator: the flow's leak into the environment is undone exactly. -/
theorem registerFlow_recovery (p₀ : CSD.LF4.CPN 32)
    (μprep : Measure (CSD.LF4.CPN 32)) [IsProbabilityMeasure μprep]
    (repS : CSD.LF4.CPN 32 → EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))
    (hrepS_unit : ∀ x, ‖repS x‖ = 1) (hrepS_meas : Measurable repS)
    (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (hprod : ∀ᵐ x ∂μprep, outerProduct (registerRep x)
      = outerProduct (repS x) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)))
    (hcode : ∀ᵐ x ∂μprep, Matrix.toEuclideanLin codeProj (repS x) = repS x) :
    recoveryChannel.apply (Matrix.traceRight (barycenterMatrix registerRep
        (Measure.map (CSD.LF4.cpSectorData p₀).π (Measure.map (registerFlow q hq0 hq1) μprep))))
      = barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep) := by
  rw [registerFlow_traceRight_barycenter p₀ μprep repS hrepS_meas q hq0 hq1 hprod]
  refine recoveryChannel_apply_singleFlipChannel_apply q hq0 hq1 _ ?_
  have h := barycenterMatrix_conj_self_of_ae repS hrepS_unit hrepS_meas
    (Measure.map (CSD.LF4.cpSectorData p₀).π μprep) codeProj
    (by
      have hπ : (CSD.LF4.cpSectorData p₀).π = id := rfl
      rw [hπ, Measure.map_id]
      exact hcode)
  rwa [codeProj_conjTranspose] at h

end QEC
end CSDBridge
end Empirical
end CSD
