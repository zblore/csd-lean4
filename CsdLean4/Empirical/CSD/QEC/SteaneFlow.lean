/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QEC.RegisterFlow
public import CsdLean4.Empirical.QM.QEC.SteaneRecovery

/-!
# Empirical/CSD: the Steane register ⊗ environment as one `Σ`-flow, and QEC on `Σ`

**Category:** 3-Local (CSD-side companion to `Empirical/QM/QEC/SteaneRecovery.lean`). BACKLOG #53,
**the `Σ`-twin of the Steane recovery** — the twin the cell promised for link 12's seven-qubit code.

`QM/QEC/SteaneRecovery.lean` built the recovery on the QM side: one channel undoes every
single-qubit Pauli on a code state. This file gives the same physics as one flow on `Σ`, on the
pattern of `RegisterFlow.lean` (three qubits) and `IndependentNoiseFlow.lean`:

* `steaneJointMat q` — the joint unitary of register ⊗ environment, the controlled-error dilation of
  #52 (`ControlledDilation.lean`) instantiated at the Steane code's own error family: the
  seven-qubit register (`128` rays) times the `22` single-error labels, `Option (Fin 7 × Fin 3)`;
* `steaneFlow q` — its projective action on `ℂℙ²⁸¹⁵`, the joint projective space, a flow of the
  corpus's `cpSectorData`, lifting the joint unitary with no hypothesis
  (★ `isUnitaryLift_steaneFlow`, through the canonical measurable unit section);
* ★★ `steaneFlow_traceRight_barycenter` — **the single-qubit Pauli channel is the environment
  marginal of the joint `Σ`-flow**: for a preparation that is a product with the environment ready,
  the reduced density operator of the flowed preparation is the mixed-unitary Pauli channel applied
  to the register's density operator;
* `exists_steane_recovery_mixedUnitary` — one recovery undoes the whole channel, not only each error
  separately, because the channel is a convex combination of the errors and a channel is linear;
* ★★★ `exists_steaneFlow_recovery` — **QEC on `Σ`, end to end**: one recovery channel, the code's
  own and independent of both the preparation and the noise weights, applied to the environment
  marginal of the flowed preparation, returns the register's density operator.

**The CSD reading.** The error is not a separate axiom: it is the `Σ`-flow's leak into the
environment factor, which is what de-isolation means here. The codespace is a region of `Σ` (the
hypothesis `P₀ (repS x) = repS x`, every prepared ray in `ℂℙ¹ ⊂ ℂℙ¹²⁷`); the regions are epistemic
and the measure weighting them is ontic, so the preparation is a probability measure over rays and
the register's state is its barycentre. The recovery then undoes the leak exactly.

## Honest scope

⚠️ No Hamiltonian generates the joint unitary here: the flow is the time-one map of the projective
action, as for `bitFlipFlow`, `registerFlow` and `indepFlow`.
⚠️ Single-qubit Pauli errors with free weights. Two qubits in error are outside the Steane code at
this level, exactly as on the QM side; the arbitrary (non-Pauli) single-qubit error is
`QM/QEC/SteaneArbitrary.lean` (#61) and is not fed through the flow here.
⚠️ The code region is a hypothesis on the preparation, not a derivation: nothing here says why a
preparation would live in the codespace.

## Source

A. Steane, *Error correcting codes in quantum theory*, PRL 77 (1996); E. Knill, R. Laflamme,
*Phys. Rev. A* 55 (1997) 900; `Empirical/QM/QEC/ControlledDilation.lean` (#52);
`Empirical/CSD/QEC/RegisterFlow.lean`; `specs/BACKLOG.md` #53; `specs/steane-plan.md`.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QEC

open CSD.LF2 CSD.Empirical.QM.QEC CSD.Empirical.QM.QEC.Steane

/-! ### The joint index of register ⊗ environment -/

/-- The joint index `(seven-qubit register) × (the 22 single-error labels)` as `Fin 2816`. -/
noncomputable def steaneEquiv : ((Fin 7 → Fin 2) × SingleErr) ≃ Fin 2816 :=
  Fintype.equivFinOfCardEq (by simp)

/-- The single-qubit Pauli errors of the Steane code are unitary. -/
theorem steaneErr_conjTranspose_mul (i : SingleErr) :
    (pauliMat (errA i) (errB i))ᴴ * pauliMat (errA i) (errB i) = 1 :=
  pauliMat_conjTranspose_mul_self (errA i) (errB i)

/-- The joint unitary of the Steane register and its environment: the controlled-error dilation of
the single-qubit Pauli channel with weights `q`. -/
noncomputable def steaneJointMat (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix ((Fin 7 → Fin 2) × SingleErr) ((Fin 7 → Fin 2) × SingleErr) ℂ :=
  controlledUnitary (fun i => pauliMat (errA i) (errB i)) q hq0 hq1 none

theorem steaneJointMat_conjTranspose_mul (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) :
    (steaneJointMat q hq0 hq1)ᴴ * steaneJointMat q hq0 hq1 = 1 :=
  controlledUnitary_conjTranspose_mul _ steaneErr_conjTranspose_mul q hq0 hq1 none

/-- The joint unitary as an element of `U(2816)`. -/
noncomputable def steaneU2816 (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Matrix.unitaryGroup (Fin 2816) ℂ :=
  ⟨Matrix.reindex steaneEquiv steaneEquiv (steaneJointMat q hq0 hq1),
    CSD.LF5.reindex_mem_unitaryGroup steaneEquiv
      (Matrix.mem_unitaryGroup_iff'.mpr (by
        rw [Matrix.star_eq_conjTranspose]
        exact steaneJointMat_conjTranspose_mul q hq0 hq1))⟩

theorem steaneU2816_val (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    ((steaneU2816 q hq0 hq1 : Matrix.unitaryGroup (Fin 2816) ℂ) :
        Matrix (Fin 2816) (Fin 2816) ℂ)
      = Matrix.reindex steaneEquiv steaneEquiv (steaneJointMat q hq0 hq1) := rfl

/-! ### The flow on `ℂℙ²⁸¹⁵` -/

/-- **The Steane register's de-isolation flow**: the projective action of the joint unitary on
`ℂℙ²⁸¹⁵`, a flow of the corpus's `cpSectorData`. -/
noncomputable def steaneFlow (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    CSD.LF4.CPN 2816 → CSD.LF4.CPN 2816 :=
  fun x => steaneU2816 q hq0 hq1 • x

theorem measurable_steaneFlow (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Measurable (steaneFlow q hq0 hq1) :=
  (continuous_const_smul (steaneU2816 q hq0 hq1)).measurable

/-- The joint representative: the canonical unit section, transported to the joint index. -/
noncomputable def steaneRep :
    CSD.LF4.CPN 2816 → EuclideanSpace ℂ ((Fin 7 → Fin 2) × SingleErr) :=
  fun x => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ steaneEquiv).symm
    (Projectivization.unitSection x)

theorem steaneRep_norm (x : CSD.LF4.CPN 2816) : ‖steaneRep x‖ = 1 := by
  simp only [steaneRep, LinearIsometryEquiv.norm_map, Projectivization.norm_unitSection]

theorem measurable_steaneRep : Measurable steaneRep :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ steaneEquiv).symm.continuous.measurable.comp
    Projectivization.measurable_unitSection

/-- ★ **The Steane flow lifts the joint unitary**, with no hypotheses. -/
theorem isUnitaryLift_steaneFlow (p₀ : CSD.LF4.CPN 2816) (q : SingleErr → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    IsUnitaryLift (CSD.LF4.cpSectorData p₀) (steaneFlow q hq0 hq1) steaneRep
      (steaneJointMat q hq0 hq1) :=
  isUnitaryLift_of_reindex (CSD.LF4.cpSectorData p₀) (steaneFlow q hq0 hq1) steaneEquiv _ _
    (by
      have h := isUnitaryLift_of_smul (CSD.LF4.cpSectorData p₀) (steaneFlow q hq0 hq1)
        (steaneU2816 q hq0 hq1) (fun _ => rfl) Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.unitSection_ne_zero
        Projectivization.mk_unitSection
      intro x
      have hx := h x
      rw [steaneU2816_val] at hx
      simpa only [steaneRep, LinearIsometryEquiv.apply_symm_apply] using hx)

/-! ### The Pauli channel as the environment marginal -/

/-- ★★ **The Steane register's single-qubit Pauli channel is the environment marginal of the joint
`Σ`-flow.** For a preparation that is a product with the environment ready, the reduced density
operator of the flowed preparation is the mixed-unitary Pauli channel applied to the register's
density operator. -/
theorem steaneFlow_traceRight_barycenter (p₀ : CSD.LF4.CPN 2816)
    (μprep : Measure (CSD.LF4.CPN 2816)) [IsProbabilityMeasure μprep]
    (repS : CSD.LF4.CPN 2816 → EuclideanSpace ℂ (Fin 7 → Fin 2)) (hrepS_meas : Measurable repS)
    (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (hprod : ∀ᵐ x ∂μprep, outerProduct (steaneRep x)
      = outerProduct (repS x) ⊗ₖ outerProduct (EuclideanSpace.single (none : SingleErr) (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix steaneRep
        (Measure.map (CSD.LF4.cpSectorData p₀).π (Measure.map (steaneFlow q hq0 hq1) μprep)))
      = (Channel.mixedUnitaryChannel (fun i => pauliMat (errA i) (errB i))
          steaneErr_conjTranspose_mul q hq0 hq1).apply
          (barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep)) := by
  rw [← stinespringChannel_controlledUnitary (fun i => pauliMat (errA i) (errB i))
    steaneErr_conjTranspose_mul q hq0 hq1 none]
  exact traceRight_barycenter_flow (CSD.LF4.cpSectorData p₀) μprep (steaneFlow q hq0 hq1)
    (measurable_steaneFlow q hq0 hq1) steaneRep steaneRep_norm measurable_steaneRep
    repS hrepS_meas (steaneJointMat q hq0 hq1) (steaneJointMat_conjTranspose_mul q hq0 hq1) _
    (by rw [PiLp.norm_single]; exact norm_one) (isUnitaryLift_steaneFlow p₀ q hq0 hq1) hprod

/-! ### The recovery undoes the leak -/

/-- The Steane recovery undoes the whole Pauli channel, not only each error separately: the channel
is a convex combination of the errors and a recovery is linear. One channel serves every weight
vector. -/
theorem exists_steane_recovery_mixedUnitary :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
        (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ), ρ = steaneProj * ρ * steaneProj →
        R.apply ((Channel.mixedUnitaryChannel (fun i => pauliMat (errA i) (errB i))
          steaneErr_conjTranspose_mul q hq0 hq1).apply ρ) = ρ := by
  obtain ⟨R, hR⟩ := exists_steane_recovery
  refine ⟨R, fun q hq0 hq1 ρ hρ => ?_⟩
  have hρ' := hR ρ hρ
  rw [Channel.apply_def (Channel.mixedUnitaryChannel (fun i => pauliMat (errA i) (errB i))
    steaneErr_conjTranspose_mul q hq0 hq1) ρ, Channel.apply_sum]
  have hterm : ∀ i : SingleErr,
      R.apply ((Channel.mixedUnitaryChannel (fun i => pauliMat (errA i) (errB i))
          steaneErr_conjTranspose_mul q hq0 hq1).kraus i * ρ *
        ((Channel.mixedUnitaryChannel (fun i => pauliMat (errA i) (errB i))
          steaneErr_conjTranspose_mul q hq0 hq1).kraus i)ᴴ) = (q i : ℂ) • ρ := by
    intro i
    have hk : (Channel.mixedUnitaryChannel (fun i => pauliMat (errA i) (errB i))
        steaneErr_conjTranspose_mul q hq0 hq1).kraus i
        = (Real.sqrt (q i) : ℂ) • pauliMat (errA i) (errB i) := rfl
    rw [hk, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Channel.apply_smul, hρ' i]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hq0 i)]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul]
  rw [show (∑ i : SingleErr, (q i : ℂ)) = ((∑ i : SingleErr, q i : ℝ) : ℂ) from by push_cast; rfl,
    hq1]
  simp

/-- ★★★ **QEC on `Σ` for the Steane code, end to end.** One recovery channel — the code's own,
independent of the preparation and of the noise weights — serves every case: let the register
preparation live in the code region (`P₀ (repS x) = repS x` a.e.: every prepared ray lies in the
codespace `ℂℙ¹ ⊂ ℂℙ¹²⁷`), the environment be ready, and the joint `Σ`-flow be `steaneFlow q`. Then
the recovery applied to the environment marginal of the flowed preparation returns the register's
density operator: the flow's leak into the 22-level environment is undone exactly. -/
theorem exists_steaneFlow_recovery :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (p₀ : CSD.LF4.CPN 2816) (μprep : Measure (CSD.LF4.CPN 2816))
        [IsProbabilityMeasure μprep]
        (repS : CSD.LF4.CPN 2816 → EuclideanSpace ℂ (Fin 7 → Fin 2)),
        (∀ x, ‖repS x‖ = 1) → Measurable repS →
        ∀ (q : SingleErr → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1),
        (∀ᵐ x ∂μprep, outerProduct (steaneRep x)
          = outerProduct (repS x) ⊗ₖ
            outerProduct (EuclideanSpace.single (none : SingleErr) (1 : ℂ))) →
        (∀ᵐ x ∂μprep, Matrix.toEuclideanLin steaneProj (repS x) = repS x) →
        R.apply (Matrix.traceRight (barycenterMatrix steaneRep
            (Measure.map (CSD.LF4.cpSectorData p₀).π
              (Measure.map (steaneFlow q hq0 hq1) μprep))))
          = barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep) := by
  obtain ⟨R, hR⟩ := exists_steane_recovery_mixedUnitary
  refine ⟨R, fun p₀ μprep _ repS hrepS_unit hrepS_meas q hq0 hq1 hprod hcode => ?_⟩
  rw [steaneFlow_traceRight_barycenter p₀ μprep repS hrepS_meas q hq0 hq1 hprod]
  refine hR q hq0 hq1 _ ?_
  have h := barycenterMatrix_conj_self_of_ae repS hrepS_unit hrepS_meas
    (Measure.map (CSD.LF4.cpSectorData p₀).π μprep) steaneProj
    (by
      have hπ : (CSD.LF4.cpSectorData p₀).π = id := rfl
      rw [hπ, Measure.map_id]
      exact hcode)
  rw [isCodeProjector_steaneProj.conjTranspose_eq] at h
  exact h.symm

end QEC
end CSDBridge
end Empirical
end CSD
