/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapWitness
public import CsdLean4.RecordLayer.RecordPersistence
public import CsdLean4.RecordLayer.OutcomeBasin

/-!
# SigmaLayer/SwapLuders: the Lüders update as a pushforward theorem

**Category:** 7-SigmaLayer (the record layer — the collapse theorem).

## The headline

For the calibrated-swap witness, **conditioned on outcome `i`, the post-measurement system marginal
IS the slot-`i` calibration**:

  `map projSys (postMeasure μ_in i) = ν i`.

With the CSD instantiation — slots calibrated to `epistemicMeasure [eⱼ]` — the system state after
outcome `i` is *literally* `epistemicMeasure [eᵢ]`, the same object the corpus uses for a fresh
isolated preparation of `eᵢ`. Not "concentrates near": **equals**. Every existing single-measurement
theorem then applies to the follow-up unchanged, which is what makes sequential statistics Lüders.

## Why this does not contradict the no-collapse results

* `shear_base_marginal_unchanged` said the *shear* cannot move the system. The swap stage is what
  moves it — by **relocation**, not contraction: the involution `swapG` exchanges the system's
  selector coordinate with a bank slot, so Liouville volume is exchanged 1:1 and
  `no_exact_collapse` is not in play. What moves is *which null slice the epistemic measure
  occupies*.
* After the swap, slot `i` holds the *pre-measurement* system state and the depleted fibre — a
  perfect ontic memory. Collapse is conservation plus relocation; irreversibility enters only when
  a slot is reset (erasure, priced by `collapse_accuracy_bound`).

## What is proved

* `swap_outcomeSector_cylinder` — the outcome sector is a base cylinder: the bank plays no part in
  *which* outcome occurs.
* `cond_prod_cylinder` — conditioning a product measure on a first-factor event conditions the
  first factor. (Reusable; no CSD content.)
* `swap_luders_marginal` — ★★ the headline above, for arbitrary calibrations `ν`.
* `swap_luders_iff_calibrated` — ★ the **minimal calibration theorem** (F-05 discharge,
  2026-08-06): post-marginal `= τ` ⟺ `ν i = τ`. The scope note below ("the calibration is a
  posit") is thereby a theorem in both directions: calibration ⇒ Lüders AND Lüders ⇒ that exact
  calibration — the update is calibration-encoded, provably, not an artifact of one construction.
* `swap_luders_born` — the CSD form: the post-outcome-`i` system marginal is
  `epistemicMeasure [eᵢ]`, so for **any** context field `c'` the follow-up outcome-`j` probability
  is `c'.rate [eᵢ] j` — the Born weight of the *collapsed* state. Sequential statistics are Lüders.

## ⚠️ Scope

* **Nondegenerate case only.** For rank-one projectors the Lüders channel *is* measure-and-reprepare
  (a standard quantum-information fact); for **degenerate** projectors it is not, and this witness
  does not cover them. That different mechanism has since landed: the boundary is the theorem
  `swap_not_blockLuders` (`RecordLayer/DegenerateLuders.lean`), the witness is
  `joinWitness_blockLuders` (`RecordLayer/JoinLuders.lean`), packaged as
  `degenerateMeasurementClosure` (`RecordLayer/JoinClosure.lean`).
* **The calibration is a context-fixed epistemic posit**, exactly parallel to pointer-readiness:
  slot `j` is prepared in `epistemicMeasure [eⱼ]`, which depends on the measurement basis alone,
  never on `ψ` — so it is A7-compatible. Its Liouville-nullity is *forced* by `no_exact_collapse`,
  not chosen for convenience.
* **One measurement consumes one bank.** Sequential measurements need fresh banks; resetting is
  erasure and is deliberately outside the protocol. (The composed two-measurement statement, with
  its fresh second apparatus, is `RecordLayer/TwoTimeLuders.lean` — Q25, 2026-08-21.)
* **The Hamiltonian generation of the swap stage is stated, not formalised** — as for the shear.

## References

`RecordLayer/SwapWitness.lean` (the witness); `RecordLayer/MeasurementConstraints.lean`
(`no_exact_collapse` — why relocation is the only shape); `RecordLayer/GlobalBasin.lean`
(`epistemicMeasure`, `globalBasin_prob`); `RecordLayer/ShearWitness.lean`
(`shear_base_marginal_unchanged` — the defect this repairs).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {Xsel : Type*} [MeasurableSpace Xsel] {K : ℕ}

/-! ### The outcome sector is a base cylinder -/

/-- **The bank plays no part in which outcome occurs**: the swap witness's outcome sector is the
shear's outcome sector, cylindered over the bank. -/
theorem swap_outcomeSector_cylinder (idx : Xsel → Fin K) (hidx : Measurable idx) (i : Fin K) :
    (swapProtocol idx hidx).outcomeSector i
      = ((shearProtocol idx hidx).outcomeSector i) ×ˢ (univ : Set (Fin K → Xsel)) := by
  ext x
  show swapEvolve idx 0 1 x ∈ {y : SwapArena Xsel K | y.1.2 ∈ pointerArc K i}
    ↔ (x.1 ∈ (shearProtocol idx hidx).outcomeSector i ∧ x.2 ∈ univ)
  rw [swapEvolve_fwd idx (by norm_num) le_rfl]
  simp only [Function.comp_apply, Set.mem_ofPred_eq, swapG_register, Set.mem_univ, and_true]
  exact Iff.rfl

/-- On the outcome-`i` sector, the post-evolution system coordinate is bank slot `i`. -/
theorem swap_evolve_sys_on_sector (idx : Xsel → Fin K) (hidx : Measurable idx) (i : Fin K)
    {x : SwapArena Xsel K} (hx : x ∈ (swapProtocol idx hidx).outcomeSector i) :
    (swapEvolve idx 0 1 x).1.1 = x.2 i := by
  have hreg : (liftShear idx 0 1 x).1.2 ∈ pointerArc K i := by
    have := hx
    rw [swap_outcomeSector_cylinder] at this
    exact this.1
  rw [swapEvolve_fwd idx (by norm_num) le_rfl]
  simp only [Function.comp_apply]
  rw [swapG_of_mem hreg]
  rfl

/-! ### Conditioning a product on a first-factor event -/

/-- **Conditioning a product measure on a first-factor cylinder conditions the first factor.**
Reusable, no CSD content. -/
theorem cond_prod_cylinder {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [IsProbabilityMeasure ν]
    (C : Set X) :
    ProbabilityTheory.cond (μ.prod ν) (C ×ˢ (univ : Set Y))
      = (ProbabilityTheory.cond μ C).prod ν := by
  show ((μ.prod ν) (C ×ˢ univ))⁻¹ • (μ.prod ν).restrict (C ×ˢ univ)
    = ((μ C)⁻¹ • μ.restrict C).prod ν
  rw [Measure.prod_prod, measure_univ, mul_one, ← Measure.restrict_prod_eq_prod_univ,
    Measure.prod_smul_left]

/-! ### ★★ The Lüders theorem -/

/-- **★★ The Lüders update, as a pushforward.**

Initial state: system-and-register `μ12`, bank slots independently calibrated to `ν j`. Conditioned
on outcome `i`, the post-measurement **system marginal is the slot-`i` calibration** — collapse as
measure-preserving relocation. The proof is a computation: on the outcome sector the evolved system
coordinate *is* bank slot `i`, the sector is a base cylinder so conditioning never touches the bank,
and evaluation pushes the bank product to its `i`-th factor. -/
theorem swap_luders_marginal (idx : Xsel → Fin K) (hidx : Measurable idx)
    (μ12 : Measure (Xsel × LF4.KTorus)) [IsProbabilityMeasure μ12]
    (ν : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν j)] (i : Fin K)
    (hpos : μ12 ((shearProtocol idx hidx).outcomeSector i) ≠ 0) :
    Measure.map (fun y : SwapArena Xsel K => y.1.1)
      ((swapProtocol idx hidx).postMeasure (μ12.prod (Measure.pi ν)) i) = ν i := by
  classical
  set P := swapProtocol idx hidx
  set C := (shearProtocol idx hidx).outcomeSector i with hC
  have hCmeas : MeasurableSet C := (shearProtocol idx hidx).outcomeSector_measurable i
  -- The conditioned measure, with the cylinder structure exposed.
  have hcond : P.selectedMeasure (μ12.prod (Measure.pi ν)) i
      = (ProbabilityTheory.cond μ12 C).prod (Measure.pi ν) := by
    rw [MeasurementProtocol.selectedMeasure, swap_outcomeSector_cylinder idx hidx i,
      cond_prod_cylinder]
  -- Push the composite system-projection-after-evolution through.
  have hmeas_ev : Measurable (P.evolve P.startTime P.readoutTime) := P.measurable_evolve _ _
  have hmeas_proj : Measurable (fun y : SwapArena Xsel K => y.1.1) :=
    measurable_fst.comp measurable_fst
  rw [MeasurementProtocol.postMeasure,
    Measure.map_map hmeas_proj hmeas_ev]
  -- On the (full-measure) outcome sector the composite is `x ↦ x.2 i`.
  have hae : ((fun y : SwapArena Xsel K => y.1.1) ∘ P.evolve P.startTime P.readoutTime)
      =ᵐ[P.selectedMeasure (μ12.prod (Measure.pi ν)) i]
      (fun x : SwapArena Xsel K => x.2 i) := by
    have hnull : P.selectedMeasure (μ12.prod (Measure.pi ν)) i
        ((P.outcomeSector i)ᶜ) = 0 := by
      rw [MeasurementProtocol.selectedMeasure,
        ProbabilityTheory.cond_apply (P.outcomeSector_measurable i)]
      rw [Set.inter_compl_self, measure_empty, mul_zero]
    filter_upwards [MeasureTheory.mem_ae_iff.mpr hnull] with x hx
    exact swap_evolve_sys_on_sector idx hidx i hx
  rw [Measure.map_congr hae, hcond]
  -- `x ↦ x.2 i` factors as evaluation after the bank projection.
  have hfactor : (fun x : SwapArena Xsel K => x.2 i)
      = (Function.eval i) ∘ (Prod.snd : SwapArena Xsel K → (Fin K → Xsel)) := rfl
  rw [hfactor, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod]
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ12 C) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  rw [measure_univ, one_smul, Measure.map_eval_pi']

/-! ### ★ The minimal calibration theorem (F-05 discharge, 2026-08-06) -/

/-- **★ The apparatus hypothesis exactly equivalent to Lüders behavior is the
calibration.** For the swap witness, the post-outcome-`i` system marginal equals
a target state `τ` **iff** bank slot `i` is calibrated to `τ`:

    map projSys (postMeasure (μ12 ⊗ Π ν) i) = τ  ↔  ν i = τ.

The forward direction is `swap_luders_marginal` (calibration ⇒ Lüders); the
converse is what makes the scope note "the Lüders map is encoded in the
apparatus calibration, not forced by record creation alone" a THEOREM: no
choice of calibration other than `ν i = epistemicMeasure [eᵢ]` produces the
Lüders post-state, and any calibration produces *its own* post-state. This is
the minimal calibration theorem the 2026-08-06 external review (F-05) asked
for — the update is calibration-encoded, provably, in both directions. -/
theorem swap_luders_iff_calibrated (idx : Xsel → Fin K) (hidx : Measurable idx)
    (μ12 : Measure (Xsel × LF4.KTorus)) [IsProbabilityMeasure μ12]
    (ν : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν j)] (i : Fin K)
    (hpos : μ12 ((shearProtocol idx hidx).outcomeSector i) ≠ 0)
    (τ : Measure Xsel) :
    Measure.map (fun y : SwapArena Xsel K => y.1.1)
        ((swapProtocol idx hidx).postMeasure (μ12.prod (Measure.pi ν)) i) = τ
      ↔ ν i = τ := by
  rw [swap_luders_marginal idx hidx μ12 ν i hpos]

/-! ### The CSD form: sequential statistics are Lüders -/

variable {N : ℕ} [NeZero N]

/-- The vertex preparation `[eⱼ]` as a projective point. -/
noncomputable def vertexPoint (j : Fin N) : LF4.CPN N :=
  Projectivization.mk ℂ (EuclideanSpace.single j (1 : ℂ)) (by
    intro h
    have := congrFun (congrArg (fun v : EuclideanSpace ℂ (Fin N) => (v : Fin N → ℂ)) h) j
    simp at this)

/-- **★★ Lüders for CSD: after outcome `i`, follow-up statistics are the collapsed state's Born
weights.** With the bank calibrated to the vertex preparations, the post-outcome-`i` system marginal
is `epistemicMeasure (vertexPoint i)` — so for **any** context field `c'`, the follow-up outcome-`j`
probability is `c'.rate [eᵢ] j`. The system state after the measurement behaves, in every subsequent
measurement, exactly as a fresh preparation of `eᵢ`: that is the Lüders update
`ρ ↦ Πᵢ ρ Πᵢ / Tr(ρ Πᵢ)` at rank one. -/
theorem swap_luders_born
    (μ12 : Measure (LF4.KSigma N × LF4.KTorus)) [IsProbabilityMeasure μ12] (i : Fin N)
    (hpos : μ12 ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0)
    (c' : ContextField N) (j : Fin N) :
    ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).postMeasure
      (μ12.prod (Measure.pi fun k => epistemicMeasure (vertexPoint k))) i)
      ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j) := by
  have hmarg := swap_luders_marginal (basinIndex (momentContext N))
    (measurable_basinIndex (momentContext N)) μ12
    (fun k => epistemicMeasure (vertexPoint k)) i hpos
  have hmeas_proj : Measurable (fun y : SwapArena (LF4.KSigma N) N => y.1.1) :=
    measurable_fst.comp measurable_fst
  rw [← Measure.map_apply hmeas_proj (measurableSet_globalBasin c' j), hmarg]
  exact globalBasin_prob c' j (vertexPoint i)

end CSD.RecordLayer
