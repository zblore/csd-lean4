/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QEC.RegisterFlow
public import CsdLean4.Empirical.QM.QEC.IndependentNoise

/-!
# Empirical/CSD: independent bit-flip noise as one `Σ`-flow, and the residual failure on `Σ`

**Category:** 3-Local (CSD-side companion to `Empirical/QM/QEC/IndependentNoise.lean`; BACKLOG
#52, the `Σ` half — the independent-noise channel `RegisterFlow.lean` left out).

`RegisterFlow.lean` read the register's *single-error* channel as the environment marginal of a
`Σ`-flow on `ℂℙ³¹` and showed the syndrome recovery undoes that leak exactly. The physical noise
is independent: **each qubit flips on its own with probability `p`**, so the environment is the
eight-level register of flip patterns and the leak has a part the code cannot undo. This file:

* `indepFlow p` — the projective action of the joint unitary
  `controlledUnitary flipOp (indepWeight p)` (`ControlledDilation.lean`) on `ℂℙ⁶³`, the joint
  projective space of the register ⊗ the pattern environment; a flow of the corpus's
  `cpSectorData` over `ℂℙ⁶³`, lifting the unitary with no hypothesis (`isUnitaryLift_indepFlow`);
* ★★ `indepFlow_traceRight_barycenter` — **the independent bit-flip channel is the environment
  marginal of the joint `Σ`-flow**: for a preparation that is a product with the environment
  ready (no flip), the reduced density operator of the flowed preparation is
  `indepFlipChannel p` applied to the register's density operator;
* ★★★ `indepFlow_recovery` — **QEC on `Σ` under independent noise, with its residual failure**:
  if the register preparation lives in the code region, the syndrome-conditioned recovery applied
  to the environment marginal of the flowed preparation returns
  `(1 − p_fail) σ + p_fail X̄ σ X̄`, `p_fail = 3p² − 2p³`. The leak into the one-flip regions is
  undone; the leak into the two- and three-flip regions — weight `3p² − 2p³` — is mis-read by the
  syndrome as its complementary single flip and corrected into the logical flip `X̄`. Below
  `p = 1/2` this is less than the bare flip probability (`failProb_lt_of_lt_half`).

What is not here: a Hamiltonian generating the joint unitary (the flow is its time-one projective
action, as for `bitFlipFlow`), and concatenation or a threshold (BACKLOG #51).

## Source

Nielsen–Chuang §10.1.1; Shor 1995, *Phys. Rev. A* **52**, R2493.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QEC

open CSD.LF2 CSD.Empirical.QM.QEC

/-! ### The joint index as `Fin 64`, and the flow on `ℂℙ⁶³` -/

/-- A flip pattern `Fin 2 × Fin 2 × Fin 2` as `Fin 8`. -/
def patternEquiv : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv

/-- The joint index `(register) × (pattern environment)` as `Fin 64`. -/
def indepEquiv : (Fin 2 × Fin 2 × Fin 2) × FlipPattern ≃ Fin 64 :=
  (Equiv.prodCongr patternEquiv patternEquiv).trans finProdFinEquiv

/-- The ready pattern: no qubit flipped. -/
abbrev readyPattern : FlipPattern := (0, 0, 0)

/-- **The joint unitary of independent noise**: the controlled error of the pattern family with the
independent weights, on register ⊗ pattern environment. -/
noncomputable def indepUnitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Matrix ((Fin 2 × Fin 2 × Fin 2) × FlipPattern) ((Fin 2 × Fin 2 × Fin 2) × FlipPattern) ℂ :=
  controlledUnitary flipOp (indepWeight p) (indepWeight_nonneg hp0 hp1) (sum_indepWeight p)
    readyPattern

theorem indepUnitary_conjTranspose_mul (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (indepUnitary p hp0 hp1)ᴴ * indepUnitary p hp0 hp1 = 1 :=
  controlledUnitary_conjTranspose_mul flipOp flipOp_conjTranspose_mul_self (indepWeight p)
    (indepWeight_nonneg hp0 hp1) (sum_indepWeight p) readyPattern

/-- ★ **The independent bit-flip channel is the Stinespring channel of the joint unitary with the
environment ready**, as channels. -/
theorem stinespringChannel_indepUnitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    CSD.LF2.stinespringChannel (indepUnitary p hp0 hp1) (indepUnitary_conjTranspose_mul p hp0 hp1)
        (EuclideanSpace.single readyPattern (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)
      = indepFlipChannel p hp0 hp1 :=
  stinespringChannel_controlledUnitary flipOp flipOp_conjTranspose_mul_self (indepWeight p)
    (indepWeight_nonneg hp0 hp1) (sum_indepWeight p) readyPattern

/-- The joint unitary as an element of `U(64)`, reindexed to `Fin 64`. -/
noncomputable def indepU64 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Matrix.unitaryGroup (Fin 64) ℂ :=
  ⟨Matrix.reindex indepEquiv indepEquiv (indepUnitary p hp0 hp1),
    CSD.LF5.reindex_mem_unitaryGroup indepEquiv
      (Matrix.mem_unitaryGroup_iff'.mpr (by
        rw [Matrix.star_eq_conjTranspose]; exact indepUnitary_conjTranspose_mul p hp0 hp1))⟩

theorem indepU64_val (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((indepU64 p hp0 hp1 : Matrix.unitaryGroup (Fin 64) ℂ) : Matrix (Fin 64) (Fin 64) ℂ)
      = Matrix.reindex indepEquiv indepEquiv (indepUnitary p hp0 hp1) := rfl

/-- **The independent-noise de-isolation flow** on `ℂℙ⁶³`: the projective action of the joint
unitary. A flow of the corpus's `cpSectorData` (`Σ = P = ℂℙ⁶³`, `π = id`). -/
noncomputable def indepFlow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    CSD.LF4.CPN 64 → CSD.LF4.CPN 64 :=
  fun x => indepU64 p hp0 hp1 • x

theorem measurable_indepFlow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measurable (indepFlow p hp0 hp1) :=
  (continuous_const_smul (indepU64 p hp0 hp1)).measurable

/-- The joint representative: the canonical unit section of `ℂℙ⁶³`, transported to the joint
index. -/
noncomputable def indepRep :
    CSD.LF4.CPN 64 → EuclideanSpace ℂ ((Fin 2 × Fin 2 × Fin 2) × FlipPattern) :=
  fun x => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ indepEquiv).symm (Projectivization.unitSection x)

theorem indepRep_norm (x : CSD.LF4.CPN 64) : ‖indepRep x‖ = 1 := by
  simp only [indepRep, LinearIsometryEquiv.norm_map, Projectivization.norm_unitSection]

theorem measurable_indepRep : Measurable indepRep :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ indepEquiv).symm.continuous.measurable.comp
    Projectivization.measurable_unitSection

/-- ★ **The independent-noise flow lifts the joint unitary**, with no hypotheses. -/
theorem isUnitaryLift_indepFlow (p₀ : CSD.LF4.CPN 64) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    IsUnitaryLift (CSD.LF4.cpSectorData p₀) (indepFlow p hp0 hp1) indepRep
      (indepUnitary p hp0 hp1) :=
  isUnitaryLift_of_reindex (CSD.LF4.cpSectorData p₀) (indepFlow p hp0 hp1) indepEquiv _ _
    (by
      have h := isUnitaryLift_of_smul (CSD.LF4.cpSectorData p₀) (indepFlow p hp0 hp1)
        (indepU64 p hp0 hp1) (fun _ => rfl) Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.unitSection_ne_zero
        Projectivization.mk_unitSection
      intro x
      have hx := h x
      rw [indepU64_val] at hx
      simpa only [indepRep, LinearIsometryEquiv.apply_symm_apply] using hx)

/-! ### The independent bit-flip channel as the environment marginal of the flow, and QEC on `Σ` -/

/-- ★★ **The independent bit-flip channel is the environment marginal of the joint `Σ`-flow.**
For a preparation on `ℂℙ⁶³` that is a product with the environment ready — no qubit flipped —
(a.e., in the canonical representative, with register representative `repS`), the reduced density
operator of the flowed preparation is `indepFlipChannel p` applied to the register's density
operator. -/
theorem indepFlow_traceRight_barycenter (p₀ : CSD.LF4.CPN 64)
    (μprep : Measure (CSD.LF4.CPN 64)) [IsProbabilityMeasure μprep]
    (repS : CSD.LF4.CPN 64 → EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)) (hrepS_meas : Measurable repS)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hprod : ∀ᵐ x ∂μprep, outerProduct (indepRep x)
      = outerProduct (repS x) ⊗ₖ outerProduct (EuclideanSpace.single readyPattern (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix indepRep
        (Measure.map (CSD.LF4.cpSectorData p₀).π (Measure.map (indepFlow p hp0 hp1) μprep)))
      = (indepFlipChannel p hp0 hp1).apply
          (barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep)) := by
  rw [← stinespringChannel_indepUnitary p hp0 hp1]
  exact traceRight_barycenter_flow (CSD.LF4.cpSectorData p₀) μprep (indepFlow p hp0 hp1)
    (measurable_indepFlow p hp0 hp1) indepRep indepRep_norm measurable_indepRep
    repS hrepS_meas (indepUnitary p hp0 hp1) (indepUnitary_conjTranspose_mul p hp0 hp1) _
    (by rw [PiLp.norm_single]; exact norm_one) (isUnitaryLift_indepFlow p₀ p hp0 hp1) hprod

/-- ★★★ **QEC on `Σ` under independent noise, with its residual failure.** Let the register
preparation live in the code region (`P₀ (repS x) = repS x` a.e.: every prepared ray lies in the
codespace `ℂℙ¹ ⊂ ℂℙ⁷`), the environment be ready, and the joint `Σ`-flow be `indepFlow p`. Then
the syndrome-conditioned recovery channel, applied to the environment marginal of the flowed
preparation, returns `(1 − p_fail) σ + p_fail X̄ σ X̄` with `σ` the register's density operator and
`p_fail = 3p² − 2p³`: the flow's leak into the one-flip regions is undone, its leak into the two-
and three-flip regions is corrected into the logical flip. -/
theorem indepFlow_recovery (p₀ : CSD.LF4.CPN 64)
    (μprep : Measure (CSD.LF4.CPN 64)) [IsProbabilityMeasure μprep]
    (repS : CSD.LF4.CPN 64 → EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))
    (hrepS_unit : ∀ x, ‖repS x‖ = 1) (hrepS_meas : Measurable repS)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hprod : ∀ᵐ x ∂μprep, outerProduct (indepRep x)
      = outerProduct (repS x) ⊗ₖ outerProduct (EuclideanSpace.single readyPattern (1 : ℂ)))
    (hcode : ∀ᵐ x ∂μprep, Matrix.toEuclideanLin codeProj (repS x) = repS x) :
    recoveryChannel.apply (Matrix.traceRight (barycenterMatrix indepRep
        (Measure.map (CSD.LF4.cpSectorData p₀).π (Measure.map (indepFlow p hp0 hp1) μprep))))
      = ((1 - failProb p : ℝ) : ℂ)
          • barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep)
        + ((failProb p : ℝ) : ℂ)
          • (logicalX * barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep)
            * logicalX) := by
  rw [indepFlow_traceRight_barycenter p₀ μprep repS hrepS_meas p hp0 hp1 hprod]
  refine recoveryChannel_apply_indepFlipChannel_apply p hp0 hp1 _ ?_
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
