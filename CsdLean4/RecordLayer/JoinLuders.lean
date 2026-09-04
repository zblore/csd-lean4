/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.JoinProtocol
public import CsdLean4.Mathlib.MeasureTheory.MapProbability
public import CsdLean4.Mathlib.Probability.ConditionalProbability

/-!
# SigmaLayer/JoinLuders: `BlockLudersObligation`, inhabited — the degenerate arc closed

**Category:** 7-SigmaLayer (dynamical measurement — degenerate Lüders, brick 5: the
conditioned marginal).

## The headline

★★ `joinWitness_blockLuders`: **the join witness satisfies `BlockLudersObligation`** — the
§8.3 demand that `swap_not_blockLuders` proved *no fixed ray-level calibration can meet* is
**inhabited** by the join protocol. For every preparation `ψ` with nonvanishing block-`i`
component, the sector-conditioned post-measurement system readout is **exactly**
`epistemicMeasure [Πᵢψ]` — the ψ-dependent Lüders update, from a **fixed** block-supported
calibration family, through Liouville-preserving dynamics.

## How the marginal computation runs (`join_luders_marginal`)

The canonical preparation is a pushforward from a parameter space
`(phase θ, system fibre θₛ, ancilla fibre θₐ, register r)`: join point = the phase-orbit point
`[χ(θ)ψ ⊕ α]`, fibres Haar, register ready. Then:

1. conditioning commutes with the pushforward (`cond_map`);
2. on the ready support, the outcome-`i` sector pulls back to a **cylinder over the system
   fibre alone** — `θₛ ∈ goodTheta` (the block's basin cells) — because the phase orbit has
   constant system ray, so the selector never sees `θ`;
3. conditioning the product on that cylinder conditions only the `θₛ` factor
   (`cond_prod_prod`);
4. on the conditioned support the evolved readout is **constant in everything but `θₐ`**:
   the ray is `[Πᵢψ]` at every phase (`joinPoint_collapse`, from `join_block_luders`), and
   the post-measurement system fibre is the ancilla's;
5. so the marginal is `δ_{[Πᵢψ]} ⊗ Haar = epistemicMeasure [Πᵢψ]`. The conditioned original
   fibre (the `θₛ` factor) integrates out — it was moved to the ancilla slot, stored.

`goodTheta_vol_pos` discharges the conditioning positivity from `Πᵢψ ≠ 0` alone (a nonzero
block coordinate has a positive-width basin cell), so the obligation carries no measure
hypothesis. *(The generic conditioning toolkit was extracted to
`CsdLean4/Mathlib/Probability/ConditionalProbability.lean` on 2026-08-02.)*

## What this closes

The degenerate-Lüders arc, bricks 1–5: relocation target (`BlockCollapse`) → phase-slot
mechanism (`PhaseSlot`) → Liouville-preserving pointwise update on the join (`JoinArena`) →
the `MeasurementProtocol` (`JoinProtocol`) → **the obligation itself** (here). The rank-one
and degenerate Lüders updates now stand on the same architectural footing: explicit
propagators, measure-preserving, records created and persistent, post-states as pushforward
theorems. `swap_not_blockLuders` stands as the theorem explaining why the *ray-pair* arena
could not host this.

## References

`RecordLayer/DegenerateLuders.lean` (`BlockLudersObligation`, `swap_not_blockLuders`);
`RecordLayer/JoinProtocol.lean` (the protocol); `RecordLayer/JoinArena.lean`
(`join_block_luders` — the pointwise input); `RecordLayer/SwapLuders.lean` (the rank-one
precedent whose conditioning toolkit this mirrors); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N K : ℕ}

/-! ### Conditioning toolkit — moved to the staging tree 2026-08-02
(`CsdLean4/Mathlib/Probability/ConditionalProbability.lean`: `ProbabilityTheory.cond_map`,
`cond_prod_prod`, `cond_eq_self`). -/

/-- The ready register never leaves the ready arc. -/
lemma readyMeasure_compl (K : ℕ) : readyMeasure K ((readyArc K)ᶜ) = 0 := by
  rw [readyMeasure, ProbabilityTheory.cond_apply measurableSet_readyArc,
    Set.inter_compl_self, measure_empty, mul_zero]

/-- Conditioning a probability measure on the whole space does nothing. -/
lemma cond_of_ae {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {S : Set X} (hS : MeasurableSet S) (h : μ Sᶜ = 0) :
    ProbabilityTheory.cond μ S = μ := by
  have hfull : μ S = 1 := by
    have := measure_add_measure_compl (μ := μ) hS
    rw [h, add_zero] at this
    rw [this, measure_univ]
  show (μ S)⁻¹ • μ.restrict S = μ
  rw [hfull, inv_one, one_smul, Measure.restrict_eq_self_of_ae_mem]
  rw [MeasureTheory.ae_iff]
  exact h

/-! ### The sector, characterised on the ready support -/

/-- On the ready arc, the shear's outcome-`i` sector is exactly the selector-`i` fibre. -/
theorem shear_sector_iff_of_ready {Xs : Type*} [MeasurableSpace Xs]
    (idx : Xs → Fin K) (hidx : Measurable idx) (i : Fin K)
    {x : Xs × LF4.KTorus} (hr : x.2 ∈ readyArc K) :
    x ∈ (shearProtocol idx hidx).outcomeSector i ↔ idx x.1 = i := by
  constructor
  · intro hx
    by_contra hne
    have h1 := shear_correlates idx hidx (idx x.1) ⟨rfl, hr⟩
    have hxarc : (shearEvolve idx 0 1 x).2 ∈ pointerArc K i := hx
    have h1arc : (shearEvolve idx 0 1 x).2 ∈ pointerArc K (idx x.1) := h1
    exact Set.disjoint_left.mp
      (pointerArc_pairwiseDisjoint (fun h => hne h.symm)) hxarc h1arc
  · intro h
    exact shear_correlates idx hidx i ⟨h, hr⟩

variable [NeZero N] (b : Fin N → Fin K)

/-- The join protocol's outcome sector is the shear's — the record trigger never moves the
register. -/
theorem join_outcomeSector_eq (i : Fin K) :
    (joinProtocol (N := N) b).outcomeSector i
      = (shearProtocol (joinIdx b) (measurable_joinIdx b)).outcomeSector i := by
  ext x
  show joinEvolve b 0 1 x ∈ Prod.snd ⁻¹' pointerArc K i
    ↔ shearEvolve (joinIdx b) 0 1 x ∈ Prod.snd ⁻¹' pointerArc K i
  rw [joinEvolve_fwd b (by norm_num) le_rfl]
  simp only [Function.comp_apply, Set.mem_preimage, joinG_register]

/-! ### The canonical preparation -/

variable (ψ α : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)

/-- One phase-orbit join point. -/
noncomputable def joinPoint (θ : AddCircle (1 : ℝ)) : LF4.CPN (N + N) :=
  Projectivization.mk ℂ (dblVec (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) α)
    (dblVec_ne_zero (smul_ne_zero (Circle.coe_ne_zero _) hψ0) α)

/-- The first-copy embedding, linearly. -/
noncomputable def dblVecFst : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin (N + N)) where
  toFun v := dblVec v 0
  map_add' v w := by
    apply PiLp.ext
    intro j
    obtain ⟨s, rfl⟩ : ∃ s, j = finSumFinEquiv s :=
      ⟨finSumFinEquiv.symm j, (Equiv.apply_symm_apply _ _).symm⟩
    rcases s with k | k
    · show dblVec (v + w) 0 (finSumFinEquiv (Sum.inl k))
        = (dblVec v 0 + dblVec w 0) (finSumFinEquiv (Sum.inl k))
      calc dblVec (v + w) 0 (finSumFinEquiv (Sum.inl k)) = (v + w) k := dblVec_inl _ _ _
        _ = v k + w k := rfl
        _ = dblVec v 0 (finSumFinEquiv (Sum.inl k))
            + dblVec w 0 (finSumFinEquiv (Sum.inl k)) := by rw [dblVec_inl, dblVec_inl]
        _ = (dblVec v 0 + dblVec w 0) (finSumFinEquiv (Sum.inl k)) := rfl
    · show dblVec (v + w) 0 (finSumFinEquiv (Sum.inr k))
        = (dblVec v 0 + dblVec w 0) (finSumFinEquiv (Sum.inr k))
      calc dblVec (v + w) 0 (finSumFinEquiv (Sum.inr k))
          = (0 : EuclideanSpace ℂ (Fin N)) k := dblVec_inr _ _ _
        _ = (0 : EuclideanSpace ℂ (Fin N)) k + (0 : EuclideanSpace ℂ (Fin N)) k := by simp
        _ = dblVec v 0 (finSumFinEquiv (Sum.inr k))
            + dblVec w 0 (finSumFinEquiv (Sum.inr k)) := by rw [dblVec_inr, dblVec_inr]
        _ = (dblVec v 0 + dblVec w 0) (finSumFinEquiv (Sum.inr k)) := rfl
  map_smul' c v := by
    apply PiLp.ext
    intro j
    obtain ⟨s, rfl⟩ : ∃ s, j = finSumFinEquiv s :=
      ⟨finSumFinEquiv.symm j, (Equiv.apply_symm_apply _ _).symm⟩
    rcases s with k | k
    · show dblVec (c • v) 0 (finSumFinEquiv (Sum.inl k))
        = (c • dblVec v 0) (finSumFinEquiv (Sum.inl k))
      calc dblVec (c • v) 0 (finSumFinEquiv (Sum.inl k)) = (c • v) k := dblVec_inl _ _ _
        _ = c • (v k) := rfl
        _ = c • dblVec v 0 (finSumFinEquiv (Sum.inl k)) := by rw [dblVec_inl]
        _ = (c • dblVec v 0) (finSumFinEquiv (Sum.inl k)) := rfl
    · show dblVec (c • v) 0 (finSumFinEquiv (Sum.inr k))
        = (c • dblVec v 0) (finSumFinEquiv (Sum.inr k))
      calc dblVec (c • v) 0 (finSumFinEquiv (Sum.inr k))
          = (0 : EuclideanSpace ℂ (Fin N)) k := dblVec_inr _ _ _
        _ = c • ((0 : EuclideanSpace ℂ (Fin N)) k) := by simp
        _ = c • dblVec v 0 (finSumFinEquiv (Sum.inr k)) := by rw [dblVec_inr]
        _ = (c • dblVec v 0) (finSumFinEquiv (Sum.inr k)) := rfl

omit [NeZero N] in
/-- The doubled vector is the linear first part plus the constant slot part. -/
lemma dblVec_split (v : EuclideanSpace ℂ (Fin N)) :
    dblVec v α = dblVecFst v + dblVec 0 α := by
  apply PiLp.ext
  intro j
  obtain ⟨s, rfl⟩ : ∃ s, j = finSumFinEquiv s :=
    ⟨finSumFinEquiv.symm j, (Equiv.apply_symm_apply _ _).symm⟩
  rcases s with k | k
  · show dblVec v α (finSumFinEquiv (Sum.inl k))
      = (dblVecFst v + dblVec 0 α) (finSumFinEquiv (Sum.inl k))
    show dblVec v α (finSumFinEquiv (Sum.inl k))
      = (dblVec v 0 + dblVec 0 α) (finSumFinEquiv (Sum.inl k))
    calc dblVec v α (finSumFinEquiv (Sum.inl k)) = v k := dblVec_inl _ _ _
      _ = v k + (0 : EuclideanSpace ℂ (Fin N)) k := by simp
      _ = dblVec v 0 (finSumFinEquiv (Sum.inl k))
          + dblVec 0 α (finSumFinEquiv (Sum.inl k)) := by rw [dblVec_inl, dblVec_inl]
      _ = (dblVec v 0 + dblVec 0 α) (finSumFinEquiv (Sum.inl k)) := rfl
  · show dblVec v α (finSumFinEquiv (Sum.inr k))
      = (dblVecFst v + dblVec 0 α) (finSumFinEquiv (Sum.inr k))
    show dblVec v α (finSumFinEquiv (Sum.inr k))
      = (dblVec v 0 + dblVec 0 α) (finSumFinEquiv (Sum.inr k))
    calc dblVec v α (finSumFinEquiv (Sum.inr k)) = α k := dblVec_inr _ _ _
      _ = (0 : EuclideanSpace ℂ (Fin N)) k + α k := by simp
      _ = dblVec v 0 (finSumFinEquiv (Sum.inr k))
          + dblVec 0 α (finSumFinEquiv (Sum.inr k)) := by rw [dblVec_inr, dblVec_inr]
      _ = (dblVec v 0 + dblVec 0 α) (finSumFinEquiv (Sum.inr k)) := rfl

omit [NeZero N] in
lemma measurable_joinPoint : Measurable (joinPoint ψ α hψ0) := by
  have hcont : Continuous fun θ : AddCircle (1 : ℝ) =>
      dblVec (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) α := by
    have hχ : Continuous fun θ : AddCircle (1 : ℝ) =>
        ((AddCircle.toCircle θ : Circle) : ℂ) • ψ :=
      ((continuous_subtype_val.comp AddCircle.continuous_toCircle).smul continuous_const)
    have hsplit : (fun θ : AddCircle (1 : ℝ) =>
        dblVec (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) α)
        = fun θ => dblVecFst (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) + dblVec 0 α := by
      funext θ
      rw [dblVec_split]
    rw [hsplit]
    exact ((LinearMap.continuous_of_finiteDimensional dblVecFst).comp hχ).add
      continuous_const
  have hsub : Measurable fun θ : AddCircle (1 : ℝ) =>
      (⟨dblVec (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) α,
        dblVec_ne_zero (smul_ne_zero (Circle.coe_ne_zero _) hψ0) α⟩
        : { w : EuclideanSpace ℂ (Fin (N + N)) // w ≠ 0 }) :=
    hcont.measurable.subtype_mk
  exact Projectivization.continuous_mk'.measurable.comp hsub

/-- The parameter space of the canonical preparation: phase, system fibre, ancilla fibre,
register. -/
noncomputable def paramMeasure (K : ℕ) :
    Measure (((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus) :=
  (((volume.prod volume).prod volume).prod (readyMeasure K))

/-- The parameter measure, as its defining product (interface lemma, §9.1). -/
lemma paramMeasure_def (K : ℕ) :
    paramMeasure K = (((volume.prod volume).prod volume).prod (readyMeasure K)) := rfl

instance : IsProbabilityMeasure (paramMeasure K) := by
  unfold paramMeasure
  infer_instance

/-- The preparation map: phase-orbit join point, fibres and register threaded through. -/
noncomputable def jF (q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus) :
    JoinSel N × LF4.KTorus :=
  (((joinPoint ψ α hψ0 q.1.1.1, q.1.1.2), q.1.2), q.2)

omit [NeZero N] in
lemma measurable_jF : Measurable (jF ψ α hψ0) := by
  refine Measurable.prodMk (Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_) ?_
  · exact (measurable_joinPoint ψ α hψ0).comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))
  · exact measurable_snd.comp (measurable_fst.comp measurable_fst)
  · exact measurable_snd.comp measurable_fst
  · exact measurable_snd

/-- **The canonical preparation**: phase-orbit join point, Haar fibres, ready register. -/
noncomputable def joinPrep : Measure (JoinSel N × LF4.KTorus) :=
  Measure.map (jF ψ α hψ0) (paramMeasure K)

instance : IsProbabilityMeasure (joinPrep (K := K) ψ α hψ0) :=
  MeasureTheory.Measure.isProbabilityMeasure_map' (measurable_jF ψ α hψ0).aemeasurable

/-! ### The selector on the orbit -/

/-- The phase orbit has constant system ray. -/
lemma joinFst_joinPoint (θ : AddCircle (1 : ℝ)) :
    joinFst (joinPoint ψ α hψ0 θ) = Projectivization.mk ℂ ψ hψ0 := by
  unfold joinPoint
  rw [joinFst_mk _ (by
    rw [fstPart_dblVec]
    exact smul_ne_zero (Circle.coe_ne_zero _) hψ0)]
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨((AddCircle.toCircle θ : Circle) : ℂ), (fstPart_dblVec _ _).symm⟩

/-- The good system fibres: those whose basin lies in block `i`. -/
def goodTheta (i : Fin K) : Set LF4.KTorus :=
  {θs | b (basinIndex (momentContext N) (Projectivization.mk ℂ ψ hψ0, θs)) = i}

lemma measurableSet_goodTheta (i : Fin K) :
    MeasurableSet (goodTheta b ψ hψ0 i) := by
  have hm : Measurable fun θs : LF4.KTorus =>
      b (basinIndex (momentContext N) (Projectivization.mk ℂ ψ hψ0, θs)) :=
    (Measurable.of_discrete (f := b)).comp
      ((measurable_basinIndex (momentContext N)).comp
        (measurable_const.prodMk measurable_id))
  exact hm (measurableSet_singleton i)

/-- The selector at a preparation point reads the system fibre alone. -/
lemma joinIdx_jF (q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus) :
    joinIdx b (jF ψ α hψ0 q).1
      = b (basinIndex (momentContext N) (Projectivization.mk ℂ ψ hψ0, q.1.1.2)) := by
  unfold joinIdx jF
  rw [joinFst_joinPoint]

/-! ### The sector pulls back to a fibre cylinder -/

lemma jF_mem_sector_iff (i : Fin K)
    {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus}
    (hr : q.2 ∈ readyArc K) :
    jF ψ α hψ0 q ∈ (joinProtocol (N := N) b).outcomeSector i
      ↔ q.1.1.2 ∈ goodTheta b ψ hψ0 i := by
  rw [join_outcomeSector_eq b i,
    shear_sector_iff_of_ready (joinIdx b) (measurable_joinIdx b) i (by exact hr),
    joinIdx_jF]
  exact Iff.rfl

/-- The pulled-back sector agrees a.e. with the fibre cylinder. -/
lemma preimage_sector_ae (i : Fin K) :
    (jF ψ α hψ0 ⁻¹' (joinProtocol (N := N) b).outcomeSector i)
      =ᵐ[paramMeasure K]
    (((univ ×ˢ goodTheta b ψ hψ0 i) ×ˢ (univ : Set LF4.KTorus)) ×ˢ readyArc K
      : Set (((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus)) := by
  have hnull : paramMeasure K {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus)
      × LF4.KTorus | q.2 ∉ readyArc K} = 0 := by
    have hset : {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus |
        q.2 ∉ readyArc K}
        = (univ : Set ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus)) ×ˢ (readyArc K)ᶜ := by
      ext q
      simp [Set.mem_prod]
    rw [hset, paramMeasure, Measure.prod_prod, readyMeasure_compl, mul_zero]
  rw [Filter.eventuallyEq_set, MeasureTheory.ae_iff]
  refine measure_mono_null (fun q hq => ?_) hnull
  show q.2 ∉ readyArc K
  intro hr
  apply hq
  show q ∈ _ ↔ q ∈ _
  rw [Set.mem_preimage]
  constructor
  · intro hmem
    exact ⟨⟨⟨trivial, (jF_mem_sector_iff b ψ α hψ0 i hr).mp hmem⟩, trivial⟩, hr⟩
  · rintro ⟨⟨⟨-, hgood⟩, -⟩, -⟩
    exact (jF_mem_sector_iff b ψ α hψ0 i hr).mpr hgood

/-! ### Positivity from the block component -/

/-- A nonzero block component gives the good-fibre set positive measure. -/
theorem goodTheta_vol_pos (i : Fin K) (hPi : blockProj b i ψ ≠ 0) :
    (volume : Measure LF4.KTorus) (goodTheta b ψ hψ0 i) ≠ 0 := by
  obtain ⟨j, hbj, hψj⟩ : ∃ j, b j = i ∧ ψ j ≠ 0 := by
    by_contra h
    push Not at h
    apply hPi
    apply PiLp.ext
    intro k
    show (if b k = i then ψ k else 0) = 0
    by_cases hk : b k = i
    · rw [if_pos hk]
      exact h k hk
    · rw [if_neg hk]
  have hsub : torusCell (LF4.momentMap (Projectivization.mk ℂ ψ hψ0)) j
      ⊆ goodTheta b ψ hψ0 i := by
    intro θs hθ
    show b (basinIndex (momentContext N) (Projectivization.mk ℂ ψ hψ0, θs)) = i
    have hmem : ((Projectivization.mk ℂ ψ hψ0 : LF4.CPN N), θs)
        ∈ globalBasin (momentContext N) j := by
      show θs.1 ∈ circleCell ((momentContext N).rate (Projectivization.mk ℂ ψ hψ0)) j
      rw [momentContext_rate]
      exact (mem_torusCell_iff _ j θs).mp hθ
    rw [basinIndex_eq_of_mem hmem, hbj]
  intro h0
  have hv : (volume : Measure LF4.KTorus)
      (torusCell (LF4.momentMap (Projectivization.mk ℂ ψ hψ0)) j) = 0 :=
    le_zero_iff.mp (h0 ▸ measure_mono hsub)
  rw [volume_torusCell _ (LF4.momentMap_nonneg _)
    (fun k => by
      have := (momentContext N).loSum_le_one (Projectivization.mk ℂ ψ hψ0) k
      rwa [momentContext_rate] at this) j] at hv
  have hpos : 0 < LF4.momentMap (Projectivization.mk ℂ ψ hψ0) j := by
    rw [LF4.momentMap_mk ψ hψ0 j]
    have h1 : 0 < ‖ψ j‖ := norm_pos_iff.mpr hψj
    have h2 : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ0
    positivity
  rw [ENNReal.ofReal_eq_zero] at hv
  linarith

/-! ### The readout on the sector -/

/-- The post-measurement system readout: system ray and system fibre of the join state. -/
noncomputable def sysRead : JoinSel N × LF4.KTorus → LF4.KSigma N :=
  fun x => (joinFst x.1.1.1, x.1.1.2)

lemma measurable_sysRead : Measurable (sysRead (N := N)) :=
  ((measurable_joinFst).comp
    (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_fst))

/-- On the sector, the evolved readout is the collapsed ray with the ancilla's fibre. -/
lemma sysRead_evolve_on_sector (i : Fin K) {x : JoinSel N × LF4.KTorus}
    (hx : x ∈ (joinProtocol (N := N) b).outcomeSector i) :
    sysRead (joinEvolve b 0 1 x) = (joinFst (joinSwap b i x.1.1.1), x.1.2) := by
  have hreg : (shearEvolve (joinIdx b) 0 1 x).2 ∈ pointerArc K i := by
    have := hx
    rw [join_outcomeSector_eq b i] at this
    exact this
  rw [joinEvolve_fwd b (by norm_num) le_rfl]
  simp only [Function.comp_apply]
  rw [joinG_of_mem b hreg]
  rfl

/-- The collapsed ray at every phase. -/
lemma joinPoint_collapse (i : Fin K) (hPi : blockProj b i ψ ≠ 0)
    (hα : blockProj b i α = α) (θ : AddCircle (1 : ℝ)) :
    joinFst (joinSwap b i (joinPoint ψ α hψ0 θ))
      = Projectivization.mk ℂ (blockProj b i ψ) hPi := by
  have hψθ : (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) ≠ 0 :=
    smul_ne_zero (Circle.coe_ne_zero _) hψ0
  have hPiθ : blockProj b i (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) ≠ 0 := by
    rw [map_smul]
    exact smul_ne_zero (Circle.coe_ne_zero _) hPi
  have h1 := join_block_luders b i hψθ hPiθ hα
  unfold joinPoint
  rw [h1, Projectivization.mk_eq_mk_iff']
  exact ⟨((AddCircle.toCircle θ : Circle) : ℂ), by rw [map_smul]⟩

/-! ### ★★ The conditioned marginal -/

/-- **★★ The degenerate Lüders marginal.** For the canonical preparation, conditioned on the
coarse outcome `i`, the post-measurement system readout is exactly the collapsed epistemic
state `epistemicMeasure [Πᵢψ]`. -/
theorem join_luders_marginal (i : Fin K) (hPi : blockProj b i ψ ≠ 0)
    (hα : blockProj b i α = α) :
    Measure.map sysRead
        ((joinProtocol (N := N) b).postMeasure (joinPrep (K := K) ψ α hψ0) i)
      = epistemicMeasure (Projectivization.mk ℂ (blockProj b i ψ) hPi) := by
  classical
  set P := joinProtocol (N := N) b
  have hGood := goodTheta_vol_pos b ψ hψ0 i hPi
  have hsec_meas : MeasurableSet (P.outcomeSector i) := P.outcomeSector_measurable i
  -- 1. Conditioning commutes with the preparation pushforward.
  have hsel : P.selectedMeasure (joinPrep (K := K) ψ α hψ0) i
      = Measure.map (jF ψ α hψ0)
          (ProbabilityTheory.cond (paramMeasure K)
            (jF ψ α hψ0 ⁻¹' P.outcomeSector i)) := by
    rw [MeasurementProtocol.selectedMeasure, joinPrep,
      ProbabilityTheory.cond_map (paramMeasure K) (measurable_jF ψ α hψ0) hsec_meas]
  -- 2. Replace the pulled-back sector by the fibre cylinder (a.e. equal sets).
  have hae_set := preimage_sector_ae b ψ α hψ0 i
  have hcond_eq : ProbabilityTheory.cond (paramMeasure K)
        (jF ψ α hψ0 ⁻¹' P.outcomeSector i)
      = ProbabilityTheory.cond (paramMeasure K)
        (((univ ×ˢ goodTheta b ψ hψ0 i) ×ˢ (univ : Set LF4.KTorus)) ×ˢ readyArc K) := by
    show ((paramMeasure K) _)⁻¹ • (paramMeasure K).restrict _
      = ((paramMeasure K) _)⁻¹ • (paramMeasure K).restrict _
    rw [measure_congr hae_set, Measure.restrict_congr_set hae_set]
  -- 3. The cylinder conditioning factorises onto the system-fibre factor.
  have hfact : ProbabilityTheory.cond (paramMeasure K)
        (((univ ×ˢ goodTheta b ψ hψ0 i) ×ˢ (univ : Set LF4.KTorus)) ×ˢ readyArc K)
      = (((volume.prod (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i))).prod
          volume).prod (readyMeasure K)) := by
    rw [paramMeasure, ProbabilityTheory.cond_prod_prod _ _ _ (readyArc K),
      ProbabilityTheory.cond_prod_prod _ _ _ (univ : Set LF4.KTorus),
      ProbabilityTheory.cond_prod_prod _ _ (univ : Set (AddCircle (1 : ℝ)))
        (goodTheta b ψ hψ0 i),
      ProbabilityTheory.cond_univ, ProbabilityTheory.cond_univ,
      ProbabilityTheory.cond_eq_self (readyMeasure K) measurableSet_readyArc
        (readyMeasure_compl K)]
  -- 4. Push through the propagator and the readout; a.e. the composite is constant in all
  --    but the ancilla fibre.
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i)) :=
    ProbabilityTheory.cond_isProbabilityMeasure hGood
  have hmeas_ev : Measurable (P.evolve P.startTime P.readoutTime) := P.measurable_evolve _ _
  rw [MeasurementProtocol.postMeasure, Measure.map_map measurable_sysRead hmeas_ev, hsel,
    hcond_eq, hfact, Measure.map_map
      (measurable_sysRead.comp hmeas_ev) (measurable_jF ψ α hψ0)]
  set ρc := ((((volume : Measure (AddCircle (1 : ℝ))).prod
      (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i))).prod
        (volume : Measure LF4.KTorus)).prod (readyMeasure K))
  have hae : ((sysRead ∘ P.evolve P.startTime P.readoutTime) ∘ jF ψ α hψ0)
      =ᵐ[ρc] fun q => (Projectivization.mk ℂ (blockProj b i ψ) hPi, q.1.2) := by
    have hnullG : ρc {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus |
        q.1.1.2 ∉ goodTheta b ψ hψ0 i} = 0 := by
      have hset : {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus |
          q.1.1.2 ∉ goodTheta b ψ hψ0 i}
          = (((univ ×ˢ (goodTheta b ψ hψ0 i)ᶜ) ×ˢ univ) ×ˢ univ) := by
        ext q
        simp [Set.mem_prod]
      have hG : (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i))
          ((goodTheta b ψ hψ0 i)ᶜ) = 0 := by
        rw [ProbabilityTheory.cond_apply (measurableSet_goodTheta b ψ hψ0 i),
          Set.inter_compl_self, measure_empty, mul_zero]
      rw [hset]
      show ρc _ = 0
      rw [show ρc = (((volume.prod (ProbabilityTheory.cond volume
          (goodTheta b ψ hψ0 i))).prod volume).prod (readyMeasure K)) from rfl,
        Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hG]
      simp
    have hnullR : ρc {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus |
        q.2 ∉ readyArc K} = 0 := by
      have hset : {q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus |
          q.2 ∉ readyArc K}
          = ((univ : Set ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus))
              ×ˢ (readyArc K)ᶜ) := by
        ext q
        simp [Set.mem_prod]
      rw [hset]
      show ρc _ = 0
      rw [show ρc = (((volume.prod (ProbabilityTheory.cond volume
          (goodTheta b ψ hψ0 i))).prod volume).prod (readyMeasure K)) from rfl,
        Measure.prod_prod, readyMeasure_compl, mul_zero]
    filter_upwards [MeasureTheory.mem_ae_iff.mpr hnullG,
      MeasureTheory.mem_ae_iff.mpr hnullR] with q hqG hqR
    have hgood : q.1.1.2 ∈ goodTheta b ψ hψ0 i := hqG
    have hready : q.2 ∈ readyArc K := hqR
    have hsector : jF ψ α hψ0 q ∈ P.outcomeSector i :=
      (jF_mem_sector_iff b ψ α hψ0 i hready).mpr hgood
    simp only [Function.comp_apply]
    have hread := sysRead_evolve_on_sector b i hsector
    show sysRead (P.evolve P.startTime P.readoutTime (jF ψ α hψ0 q)) = _
    rw [show P.evolve P.startTime P.readoutTime = joinEvolve b 0 1 from rfl, hread]
    show (joinFst (joinSwap b i (joinPoint ψ α hψ0 q.1.1.1)), q.1.2) = _
    rw [joinPoint_collapse b ψ α hψ0 i hPi hα]
  rw [Measure.map_congr hae]
  -- 5. The marginal: constant ray, ancilla fibre → `δ ⊗ Haar`.
  have hsplit : (fun q : ((AddCircle (1 : ℝ) × LF4.KTorus) × LF4.KTorus) × LF4.KTorus =>
      (Projectivization.mk ℂ (blockProj b i ψ) hPi, q.1.2))
      = (Prod.mk (Projectivization.mk ℂ (blockProj b i ψ) hPi))
        ∘ ((Prod.snd) ∘ (Prod.fst)) := rfl
  rw [hsplit, ← Measure.map_map (measurable_prodMk_left) (measurable_snd.comp measurable_fst),
    ← Measure.map_map measurable_snd measurable_fst]
  have hfstmarg : Measure.map Prod.fst ρc
      = (((volume : Measure (AddCircle (1 : ℝ))).prod
          (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i))).prod
        (volume : Measure LF4.KTorus)) := by
    show (ρc).fst = _
    rw [show ρc = (((volume.prod (ProbabilityTheory.cond volume
        (goodTheta b ψ hψ0 i))).prod volume).prod (readyMeasure K)) from rfl,
      Measure.fst_prod]
  have hsndmarg : Measure.map Prod.snd
      (((volume : Measure (AddCircle (1 : ℝ))).prod
          (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i))).prod
        (volume : Measure LF4.KTorus))
      = (volume : Measure LF4.KTorus) := by
    show ((((volume : Measure (AddCircle (1 : ℝ))).prod
      (ProbabilityTheory.cond volume (goodTheta b ψ hψ0 i))).prod
        (volume : Measure LF4.KTorus))).snd = _
    rw [Measure.snd_prod]
  rw [hfstmarg, hsndmarg, ← Measure.dirac_prod]
  rfl

/-! ### ★★ The obligation, inhabited -/

/-- The join witness's post-measurement system marginal, for calibration family `α`. -/
noncomputable def joinPostMarg (α : Fin K → EuclideanSpace ℂ (Fin N))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (i : Fin K) : Measure (LF4.KSigma N) :=
  Measure.map sysRead
    ((joinProtocol (N := N) b).postMeasure (joinPrep (K := K) ψ (α i) hψ0) i)

/-- **★★ `BlockLudersObligation`, inhabited.** With any block-supported calibration family,
the join witness satisfies the §8.3 degenerate-Lüders demand — the construction
`swap_not_blockLuders` proved impossible for every fixed ray-level calibration, delivered by
the phase-carrying join arena through Liouville-preserving dynamics. -/
theorem joinWitness_blockLuders (α : Fin K → EuclideanSpace ℂ (Fin N))
    (hα : ∀ i, blockProj b i (α i) = α i) :
    BlockLudersObligation b (joinPostMarg b α) :=
  fun ψ hψ0 i hPi => join_luders_marginal b ψ (α i) hψ0 i hPi (hα i)

end CSD.RecordLayer
