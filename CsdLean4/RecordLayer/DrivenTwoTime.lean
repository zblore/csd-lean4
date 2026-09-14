/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TwoTimeLuders
public import CsdLean4.RecordLayer.RotatedSwap
public import CsdLean4.RecordLayer.RotatedContext
public import CsdLean4.RecordLayer.MixedLuders

/-!
# RecordLayer/DrivenTwoTime: measure, DRIVE, measure — the two-time law with a flow between the readouts

**Category:** 7-SigmaLayer (the record layer — Q25's two-stage arena with a sector flow inserted
between the two measurements, and the first measurement in an arbitrary orthonormal basis; the
record-layer engine TH5d consumes, `specs/BACKLOG.md` ▶ OPEN QUEUE #4).

## What was missing

`RecordLayer/TwoTimeLuders.lean` composes two measurements on one arena, but nothing happens
to the system BETWEEN them: the second apparatus reads the relocated state `[eᵢ]` as it was left.
Every "measure, evolve, measure" statement — a two-point-measurement protocol, a Ramsey sequence,
an echo — needs a flow in the gap. This module inserts one, and lets the first measurement read
an arbitrary orthonormal basis (the two-stage arena's first context was the computational
basis), with a MIXED preparation.

## The construction

`driveStage Φ` moves the system coordinate by `Φ : Xsel → Xsel` and touches nothing else;
`drivenTwoStage idx₁ Φ idx₂ = stageTwo idx₂ ∘ driveStage Φ ∘ stageOne idx₁`. The first register
and bank ride through the drive (`driveStage_register₁`, `driveStage_bank₁`), so the `t₁` record
still persists structurally.

★ **The reindexing identity** (`drivenJointRecordSector_eq`): the joint record sector of the driven
propagator is the joint record sector of the UNDRIVEN propagator at the reindexed second context
`idx₂ ∘ Φ`. The second register's reading depends on the system only through `idx₂`, and the
system it sees is `Φ` of the relocated one (`swapEvolve_register_comp`). So the drive is, at the
level of records, a change of the second context — and Q25's generic engine `two_stage_joint`
applies verbatim.

## Main results

* **Generic (`Xsel`):** `driveStage`, `drivenTwoStage`, `drivenJointRecordSector`;
  ★ `drivenJointRecordSector_eq`; ★★ `driven_two_stage_joint` — the joint law factors as
  (stage-1 sector) × (stage-2 sector at `idx₂ ∘ Φ`).
* **On `Σ = ℂℙ^{N−1} × T²`:** `baseLift Φ'` (a base map lifted to the sector, the fibre untouched —
  `baseLift_unitary_smul`: for a unitary it is the corpus's `U(N)` action on `KSigma`);
  `ContextField.pullback` (the context "measure after the flow"), with ★ `basinIndex_pullback`
  (`basinIndex (c.pullback Φ') = basinIndex c ∘ baseLift Φ'`).
* **The mixed first stage in a rotated basis:** `mixedReadyPrep_prod_sector` (the mixed
  preparation's sector weight under ANY context and ANY bank is the eigenvalue mixture of the
  context's rates), `mixed_outcome_pos_ctx` (positivity licenses conditioning),
  ★ `spectral_born_ctx_eq_traceForm` (that mixture, in an orthonormal basis `b`, is
  `Tr(ρ ∣bᵢ⟩⟨bᵢ∣)` — `spectral_born_eq_traceForm` at a general basis).
* ★★ `driven_mixed_two_time_born` — **the two-time law with a drive**: for a density operator `ρ`,
  first readout in the orthonormal basis `b`, a measurable base flow `Φ'` between the readouts,
  and an arbitrary second context `c₂`,

    `P(record i at t₁ ∧ record j at t₂) = Tr(ρ ∣bᵢ⟩⟨bᵢ∣) · c₂.rate (Φ' [bᵢ]) j`;

  `driven_mixed_two_time_first_record` — the drive and the second apparatus cannot retro-act on
  the first record.

## ⚠️ Honest scope

* The drive acts on the BASE and leaves the pointer fibre alone (`baseLift`): between the two
  readouts the system is isolated from both apparatus, and its ontic base point moves by the
  flow. A drive that also stirs the fibre is not modelled.
* The drive sits between the two crossings as a composed map, exactly as the two stages do; the
  clock-glued single-propagator form remains `two-time-luders-scoping.md`'s gated presentation
  item.
* Rank-one readouts, one bank per measurement, the vertex-calibrated bank for the second
  apparatus (any probability bank would do — `sector_born_ctx` is bank-generic).

## References

`specs/BACKLOG.md` (▶ OPEN QUEUE #4 = TH5d, the consumer; Q25); `specs/two-time-luders-scoping.md`;
`RecordLayer/TwoTimeLuders.lean` (`stageOne`, `stageTwo`, `regroup`, `two_stage_joint`,
`two_stage_first_record`); `RecordLayer/SwapWitness.lean` (`swapEvolve_fwd`, `swapG_register`);
`RecordLayer/RotatedSwap.lean` (`basisPoint`, `sector_born_ctx`, `prep_outcome_pos_ctx`);
`RecordLayer/RotatedContext.lean` (`basisContext`, `basisContext_rate_mk`);
`RecordLayer/MixedLuders.lean` (`mixedReadyPrep`, `mixed_outcome_pos`);
`RecordLayer/MixedSwap.lean` (`eigRay`, `spectral_born_eq_traceForm`);
`LF4/KahlerInstance.lean` (`instSMulKSigma`); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer CSD.LF2

variable {Xsel : Type*} [MeasurableSpace Xsel] {K : ℕ}

/-! ### The drive between the two measurements -/

/-- **The drive**: move the system coordinate by `Φ`; both registers and both banks ride. -/
def driveStage (Φ : Xsel → Xsel) (x : TwoStageArena Xsel K) : TwoStageArena Xsel K :=
  (((Φ x.1.1.1, x.1.1.2), x.1.2), x.2)

omit [MeasurableSpace Xsel] in
theorem driveStage_register₁ (Φ : Xsel → Xsel) (x : TwoStageArena Xsel K) :
    (driveStage Φ x).1.1.2 = x.1.1.2 := rfl

omit [MeasurableSpace Xsel] in
theorem driveStage_bank₁ (Φ : Xsel → Xsel) (x : TwoStageArena Xsel K) :
    (driveStage Φ x).1.2 = x.1.2 := rfl

theorem measurable_driveStage {Φ : Xsel → Xsel} (hΦ : Measurable Φ) :
    Measurable (driveStage (K := K) Φ) :=
  (((hΦ.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd

/-- **The driven two-time propagator**: stage 1, the drive, stage 2. -/
noncomputable def drivenTwoStage (idx₁ : Xsel → Fin K) (Φ : Xsel → Xsel) (idx₂ : Xsel → Fin K) :
    TwoStageArena Xsel K → TwoStageArena Xsel K :=
  stageTwo idx₂ ∘ driveStage Φ ∘ stageOne idx₁

theorem measurable_drivenTwoStage (idx₁ : Xsel → Fin K) {Φ : Xsel → Xsel} (idx₂ : Xsel → Fin K)
    (h₁ : Measurable idx₁) (hΦ : Measurable Φ) (h₂ : Measurable idx₂) :
    Measurable (drivenTwoStage (K := K) idx₁ Φ idx₂) :=
  (measurable_stageTwo idx₂ h₂).comp ((measurable_driveStage hΦ).comp (measurable_stageOne idx₁ h₁))

/-- **The driven joint record sector**: the initial states destined to display record `i` at `t₁`
and, after the drive, record `j` at `t₂`. -/
def drivenJointRecordSector (idx₁ : Xsel → Fin K) (Φ : Xsel → Xsel) (idx₂ : Xsel → Fin K)
    (i j : Fin K) : Set (TwoStageArena Xsel K) :=
  drivenTwoStage idx₁ Φ idx₂ ⁻¹' (recordOneEvent i ∩ recordTwoEvent j)

/-! ### ★ The drive is a reindexing of the second context -/

omit [MeasurableSpace Xsel] in
/-- The register after the crossing depends on the system only through the index: driving the
system by `Φ` before a swap protocol at `idx` reads as the swap protocol at `idx ∘ Φ`. -/
theorem swapEvolve_register_comp (idx : Xsel → Fin K) (Φ : Xsel → Xsel) (x : SwapArena Xsel K) :
    (swapEvolve idx 0 1 ((Φ x.1.1, x.1.2), x.2)).1.2 = (swapEvolve (idx ∘ Φ) 0 1 x).1.2 := by
  rw [swapEvolve_fwd idx (by norm_num) le_rfl, swapEvolve_fwd (idx ∘ Φ) (by norm_num) le_rfl]
  simp only [Function.comp_apply, swapG_register]
  rfl

omit [MeasurableSpace Xsel] in
/-- The second register after the driven stage 2 is the second register after the undriven
stage 2 at the reindexed context. -/
theorem stageTwo_driveStage_register₂ (idx₂ : Xsel → Fin K) (Φ : Xsel → Xsel)
    (y : TwoStageArena Xsel K) :
    (stageTwo idx₂ (driveStage Φ y)).2.1 = (stageTwo (idx₂ ∘ Φ) y).2.1 :=
  swapEvolve_register_comp idx₂ Φ ((y.1.1.1, y.2.1), y.2.2)

omit [MeasurableSpace Xsel] in
/-- ★ **The drive is a reindexing of the second context, at the level of record sectors**: the
driven joint sector at `(idx₁, Φ, idx₂)` IS the undriven joint sector at `(idx₁, idx₂ ∘ Φ)`. The
first record never sees the drive; the second register's reading depends on the system only
through the index, and the system it reads is `Φ` of the relocated one. -/
theorem drivenJointRecordSector_eq (idx₁ idx₂ : Xsel → Fin K) (Φ : Xsel → Xsel) (i j : Fin K) :
    drivenJointRecordSector idx₁ Φ idx₂ i j = jointRecordSector idx₁ (idx₂ ∘ Φ) i j := by
  ext x
  show ((stageTwo idx₂ (driveStage Φ (stageOne idx₁ x))).1.1.2 ∈ pointerArc K i
      ∧ (stageTwo idx₂ (driveStage Φ (stageOne idx₁ x))).2.1 ∈ pointerArc K j)
    ↔ ((stageTwo (idx₂ ∘ Φ) (stageOne idx₁ x)).1.1.2 ∈ pointerArc K i
      ∧ (stageTwo (idx₂ ∘ Φ) (stageOne idx₁ x)).2.1 ∈ pointerArc K j)
  rw [stageTwo_register₁, stageTwo_register₁, driveStage_register₁,
    stageTwo_driveStage_register₂]

omit [MeasurableSpace Xsel] in
/-- The drive does not move the first-record event. -/
theorem drivenTwoStage_preimage_recordOne (idx₁ idx₂ : Xsel → Fin K) (Φ : Xsel → Xsel)
    (i : Fin K) :
    drivenTwoStage idx₁ Φ idx₂ ⁻¹' recordOneEvent i
      = twoStage idx₁ (idx₂ ∘ Φ) ⁻¹' recordOneEvent i := by
  ext x
  show (stageTwo idx₂ (driveStage Φ (stageOne idx₁ x))).1.1.2 ∈ pointerArc K i
    ↔ (stageTwo (idx₂ ∘ Φ) (stageOne idx₁ x)).1.1.2 ∈ pointerArc K i
  rw [stageTwo_register₁, stageTwo_register₁, driveStage_register₁]

/-- ★★ **The generic driven two-stage composition**: the joint two-record probability with a drive
`Φ` between the readouts factors as (stage-1 sector measure) × (stage-2 sector measure at the
relocated state, for the reindexed context `idx₂ ∘ Φ`). `two_stage_joint` through the
reindexing identity. -/
theorem driven_two_stage_joint (idx₁ idx₂ : Xsel → Fin K) {Φ : Xsel → Xsel}
    (h₁ : Measurable idx₁) (hΦ : Measurable Φ) (h₂ : Measurable idx₂)
    (μ12 : Measure (Xsel × LF4.KTorus)) [IsProbabilityMeasure μ12]
    (ν₁ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₁ j)]
    (μR₂ : Measure LF4.KTorus) [IsProbabilityMeasure μR₂]
    (ν₂ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₂ j)] (i j : Fin K)
    (hpos : μ12 ((shearProtocol idx₁ h₁).outcomeSector i) ≠ 0) :
    twoStagePrep μ12 ν₁ μR₂ ν₂ (drivenJointRecordSector idx₁ Φ idx₂ i j)
      = (μ12.prod (Measure.pi ν₁)) ((swapProtocol idx₁ h₁).outcomeSector i)
        * (((ν₁ i).prod μR₂).prod (Measure.pi ν₂))
            ((swapProtocol (idx₂ ∘ Φ) (h₂.comp hΦ)).outcomeSector j) := by
  rw [drivenJointRecordSector_eq]
  exact two_stage_joint idx₁ (idx₂ ∘ Φ) h₁ (h₂.comp hΦ) μ12 ν₁ μR₂ ν₂ i j hpos

/-! ### The sector flow of a base map, and the pulled-back context -/

variable {N : ℕ} [NeZero N]

/-- **A base map lifted to the sector**: the ontic base point moves, the pointer fibre rides. -/
def baseLift (Φ' : LF4.CPN N → LF4.CPN N) : LF4.KSigma N → LF4.KSigma N :=
  Prod.map Φ' id

omit [NeZero N] in
@[simp] theorem baseLift_apply (Φ' : LF4.CPN N → LF4.CPN N) (x : LF4.KSigma N) :
    baseLift Φ' x = (Φ' x.1, x.2) := rfl

omit [NeZero N] in
theorem measurable_baseLift {Φ' : LF4.CPN N → LF4.CPN N} (hΦ' : Measurable Φ') :
    Measurable (baseLift Φ') :=
  hΦ'.prodMap measurable_id

omit [NeZero N] in
/-- For a unitary, the lifted base action IS the corpus's `U(N)` action on `Σ`
(`LF4/KahlerInstance.lean`, `instSMulKSigma`). -/
theorem baseLift_unitary_smul (U : Matrix.unitaryGroup (Fin N) ℂ) :
    baseLift (fun p : LF4.CPN N => U • p) = fun x : LF4.KSigma N => U • x := rfl

/-- **The pulled-back context**: the apparatus `c` read AFTER the base flow `Φ'` — its rate at
`p` is `c`'s rate at `Φ' p`. -/
noncomputable def ContextField.pullback (c : ContextField N) (Φ' : LF4.CPN N → LF4.CPN N)
    (hΦ' : Measurable Φ') : ContextField N where
  rate p i := c.rate (Φ' p) i
  measurable_rate i := (c.measurable_rate i).comp hΦ'
  nonneg p i := c.nonneg (Φ' p) i
  sum_one p := c.sum_one (Φ' p)

omit [NeZero N] in
@[simp] theorem ContextField.pullback_rate (c : ContextField N) (Φ' : LF4.CPN N → LF4.CPN N)
    (hΦ' : Measurable Φ') (p : LF4.CPN N) (i : Fin N) :
    (c.pullback Φ' hΦ').rate p i = c.rate (Φ' p) i := rfl

omit [NeZero N] in
/-- The basins of the pulled-back context are the pulled-back basins. -/
theorem globalBasin_pullback (c : ContextField N) (Φ' : LF4.CPN N → LF4.CPN N)
    (hΦ' : Measurable Φ') (i : Fin N) :
    globalBasin (c.pullback Φ' hΦ') i = baseLift Φ' ⁻¹' globalBasin c i := rfl

/-- ★ **The pulled-back selector is the selector after the flow**: reading the basin index of `c`
after moving the base by `Φ'` is reading the basin index of `c.pullback Φ'`. -/
theorem basinIndex_pullback (c : ContextField N) (Φ' : LF4.CPN N → LF4.CPN N)
    (hΦ' : Measurable Φ') :
    basinIndex (c.pullback Φ' hΦ') = basinIndex c ∘ baseLift Φ' := rfl

/-! ### The mixed preparation under an arbitrary context and bank -/

/-- **The mixed preparation's sector weight, for any context and any bank**: the eigenvalue
mixture of the context's rates at the spectral eigenrays. -/
theorem mixedReadyPrep_prod_sector (ρ : DensityOperator N) (c : ContextField N)
    (ν : Fin N → Measure (LF4.KSigma N)) [∀ k, IsProbabilityMeasure (ν k)] (i : Fin N) :
    ((mixedReadyPrep ρ).prod (Measure.pi ν))
        ((swapProtocol (basinIndex c) (measurable_basinIndex c)).outcomeSector i)
      = ENNReal.ofReal (∑ j, ρ.isHermitian.eigenvalues j * c.rate (eigRay ρ j) i) := by
  rw [mixedReadyPrep, ← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.finsetSum_apply]
  simp only [Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => by rw [sector_born_ctx c ν (eigRay ρ j) i]]
  rw [Finset.sum_congr rfl fun j _ =>
    (ENNReal.ofReal_mul ((eigenvalues_isProbability ρ).1 j)).symm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg ((eigenvalues_isProbability ρ).1 j) (c.nonneg _ i))]

/-- **Positivity licenses the conditioning, for any context**: a nonzero mixed rate gives the
outcome sector nonzero mixed measure. `mixed_outcome_pos` at a general context field. -/
theorem mixed_outcome_pos_ctx (ρ : DensityOperator N) (c : ContextField N) (i : Fin N)
    (hpos : ∑ j, ρ.isHermitian.eigenvalues j * c.rate (eigRay ρ j) i ≠ 0) :
    mixedReadyPrep ρ ((shearProtocol (basinIndex c) (measurable_basinIndex c)).outcomeSector i)
      ≠ 0 := by
  have hex : ∃ j, ρ.isHermitian.eigenvalues j * c.rate (eigRay ρ j) i ≠ 0 := by
    by_contra h
    exact hpos (Finset.sum_eq_zero fun j _ => not_not.mp (not_exists.mp h j))
  obtain ⟨j, hj⟩ := hex
  have hlam : ρ.isHermitian.eigenvalues j ≠ 0 := fun h => hj (by rw [h, zero_mul])
  have hrate : c.rate (eigRay ρ j) i ≠ 0 := fun h => hj (by rw [h, mul_zero])
  intro h0
  rw [mixedReadyPrep, Measure.finsetSum_apply] at h0
  simp only [Measure.smul_apply, smul_eq_mul] at h0
  have hzero := (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ j)
  refine absurd hzero (mul_ne_zero ?_ (prep_outcome_pos_ctx c (eigRay ρ j) i hrate))
  rw [ENNReal.ofReal_ne_zero_iff]
  exact lt_of_le_of_ne ((eigenvalues_isProbability ρ).1 j) (Ne.symm hlam)

omit [NeZero N] in
/-- ★ **The spectral bridge in an arbitrary orthonormal basis**: the eigenvalue mixture of the
basis-`b` rates at the eigenrays is the density-operator Born probability `Tr(ρ ∣bᵢ⟩⟨bᵢ∣)`.
`spectral_born_eq_traceForm` with the standard basis replaced by `b`. -/
theorem spectral_born_ctx_eq_traceForm (ρ : DensityOperator N)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ∑ j, ρ.isHermitian.eigenvalues j * (basisContext b).rate (eigRay ρ j) i
      = traceForm ρ (rankOneEffect (b i) (b.orthonormal.1 i)) := by
  rw [traceForm_eq_pureEnsemble]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [eigRay, basisContext_rate_mk b _ (eigenvectorBasis_ne_zero' ρ j)
      (eigenvectorBasis_norm_one ρ j) i,
    born_quadratic (ρ.isHermitian.eigenvectorBasis j) (b i) (eigenvectorBasis_norm_one ρ j)
      (b.orthonormal.1 i),
    ← inner_conj_symm (ρ.isHermitian.eigenvectorBasis j) (b i), RCLike.norm_conj]

/-! ### ★★ The two-time law with a drive, for a mixed preparation in a rotated basis -/

/-- **The two-stage preparation of a mixed system whose first readout is in the orthonormal
basis `b`**: `mixedReadyPrep ρ` with the bank calibrated to the rotated vertices `[bₖ]`
(`rotatedBank b`), and a fresh ready register with the vertex-calibrated bank for the second
apparatus. -/
noncomputable def rotatedMixedTwoPrep (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ρ : DensityOperator N) : Measure (TwoStageArena (LF4.KSigma N) N) :=
  twoStagePrep (mixedReadyPrep ρ) (fun k => epistemicMeasure (basisPoint b k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k))

instance (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (ρ : DensityOperator N) :
    IsProbabilityMeasure (rotatedMixedTwoPrep b ρ) := by
  unfold rotatedMixedTwoPrep
  infer_instance

/-- ★★ **Measure, drive, measure — the two-time law with a flow between the readouts.** For a
density operator `ρ`, a first readout in the orthonormal basis `b`, a measurable base flow `Φ'`
applied between the readouts, and an ARBITRARY second context `c₂`:

  `P(record i at t₁ ∧ record j at t₂) = Tr(ρ ∣bᵢ⟩⟨bᵢ∣) · c₂.rate (Φ' [bᵢ]) j`.

The first factor is the mixed dynamical Born weight in the basis `b`; the second is the Born
weight, in the second context, of the collapsed state `[bᵢ]` TRANSPORTED by the flow. -/
theorem driven_mixed_two_time_born (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ρ : DensityOperator N) {Φ' : LF4.CPN N → LF4.CPN N} (hΦ' : Measurable Φ')
    (c₂ : ContextField N) (i j : Fin N)
    (hpos : traceForm ρ (rankOneEffect (b i) (b.orthonormal.1 i)) ≠ 0) :
    rotatedMixedTwoPrep b ρ
        (drivenJointRecordSector (basinIndex (basisContext b)) (baseLift Φ') (basinIndex c₂) i j)
      = ENNReal.ofReal (traceForm ρ (rankOneEffect (b i) (b.orthonormal.1 i)))
        * ENNReal.ofReal (c₂.rate (Φ' (basisPoint b i)) j) := by
  rw [drivenJointRecordSector_eq, ← basinIndex_pullback c₂ Φ' hΦ', rotatedMixedTwoPrep,
    two_stage_joint (basinIndex (basisContext b)) (basinIndex (c₂.pullback Φ' hΦ'))
      (measurable_basinIndex _) (measurable_basinIndex _)
      (mixedReadyPrep ρ) (fun k => epistemicMeasure (basisPoint b k)) (readyMeasure N)
      (fun k => epistemicMeasure (vertexPoint k)) i j
      (mixed_outcome_pos_ctx ρ (basisContext b) i (by rwa [spectral_born_ctx_eq_traceForm]))]
  congr 1
  · rw [mixedReadyPrep_prod_sector, spectral_born_ctx_eq_traceForm]
  · exact sector_born_ctx (c₂.pullback Φ' hΦ') (fun k => epistemicMeasure (vertexPoint k))
      (basisPoint b i) j

/-- **No retro-action**: neither the drive nor the second apparatus disturbs the first record's
mixed Born law in the basis `b`. -/
theorem driven_mixed_two_time_first_record
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ρ : DensityOperator N) (Φ' : LF4.CPN N → LF4.CPN N) (c₂ : ContextField N) (i : Fin N) :
    rotatedMixedTwoPrep b ρ
        (drivenTwoStage (basinIndex (basisContext b)) (baseLift Φ') (basinIndex c₂)
          ⁻¹' recordOneEvent i)
      = ENNReal.ofReal (traceForm ρ (rankOneEffect (b i) (b.orthonormal.1 i))) := by
  rw [drivenTwoStage_preimage_recordOne, rotatedMixedTwoPrep,
    two_stage_first_record (basinIndex (basisContext b)) (basinIndex c₂ ∘ baseLift Φ')
      (measurable_basinIndex _)
      (mixedReadyPrep ρ) (fun k => epistemicMeasure (basisPoint b k)) (readyMeasure N)
      (fun k => epistemicMeasure (vertexPoint k)) i,
    mixedReadyPrep_prod_sector, spectral_born_ctx_eq_traceForm]

end CSD.RecordLayer
