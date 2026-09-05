/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapClosure
public import CsdLean4.Mathlib.MeasureTheory.MapProbability

/-!
# RecordLayer/TwoTimeLuders: records at t₁ then t₂, on one arena (Q25)

**Category:** 7-SigmaLayer (the record layer — the two-time composition).

## The chain, and its exact status

The chain is: a **record fixes the state** (the collapse — the post-measurement marginal is the
slot-`i` calibration), **Born gives the next volume fractions** at that state, and **repeat**. Each
repetition consumes a fresh bank.

⚠️ **Status, and it changed on 2026-09-05 — do not repeat the older wording.** Iteration beyond two
steps used to be an argument from self-similarity. It is now a **theorem**: `csd_nstep_born`
(`RecordLayer/NStepChain.lean`) proves the depth-`n` law for every sequence of contexts and
outcomes, by induction, with `csd_nstep_repeatable` for non-vacuity. What is *still* an argument is
one level up: that an **`n`-stage arena** assembles to give it. `two_stage_joint` builds that arena
for `n = 2`; the general construction is not done. So the honest split is — the chain **law** is
proved to arbitrary depth given `n` banks; the chain **arena** is built for two.

⚠️ This module is the **arena** half for `n = 2`, which is the half that is *not* general. The
chain law itself is `csd_nstep_born`. The calibration is `specs/POSITS.md` Posit 5.

## The question this answers

"What happens to the OTHER regions `Ω_j` when outcome `i` is realised?" The corpus had the
one-measurement dynamics complete (`swap_sector_born`, `swap_luders_marginal`) and the sequential
statistics as CONDITIONAL statements about the post-measurement ensemble (`csd_sequential_born`,
`csd_repeatability`). This module composes them into the **two-time statement on one arena**: a
single composite space carrying BOTH measurements, the JOINT law of the record pair, and the first
record persisting — structurally — through the second measurement.

## The construction

Extend the swap arena with a **second apparatus** — a fresh register and a fresh bank ("one
measurement consumes one bank" is the standing scope note, so a second measurement carries its
own):

  `TwoStageArena Xsel K = SwapArena Xsel K × (T²_R × (Fin K → Xsel))`.

Stage 1 is the first swap propagator with the second apparatus as a spectator (`stageOne`). Stage 2
is the second swap propagator conjugated by the coordinate shuffle `regroup` that brings
(system, register₂, bank₂) together while the stage-1 record coordinates ride untouched
(`stageTwo`). Because the stage-2 evolution provably never touches register₁ or bank₁
(`stageTwo_register₁`, `stageTwo_bank₁` — definitional, the same reason `swapG_register` was
free), **the `t₁` record is still on display at `t₂`**.

## What is proved

* `cond_map` — conditioning commutes with a measurable pushforward. (Reusable; no CSD content.)
* `two_stage_first_record` — the stage-1 record marginal is untouched by composing: the second
  apparatus cannot retro-act on the first record's probability.
* `two_stage_joint` — ★★ the generic composition: the joint record probability factors as
  (stage-1 sector measure) × (stage-2 sector measure at the relocated state). The engine is
  `swap_luders_marginal`: the stage-2 record event never reads the stage-1 record coordinates, so
  only the SYSTEM marginal of the conditioned post-measurement state enters — no joint
  factorisation of the conditioned law is ever needed.
* `two_time_born` — ★★ the CSD form: for the canonical ready preparation at `p`,
  `P(record i at t₁ ∧ record j at t₂) = momentMap p i · c₂.rate [eᵢ] j` for ANY second context
  `c₂`. Two-time statistics are Born-then-Lüders-Born, as one number on one arena.
* `two_time_repeat` — ★ von Neumann repeatability in composed form: with the same context twice,
  the joint law is `momentMap p i · δᵢⱼ`.
* `two_time_other_fate` — ★ the row's literal question: CONDITIONED on record `i` at `t₁`, the
  stage-2 partition carries the collapsed weights `c₂.rate [eᵢ]` — for the repeated context the
  other `Ω_j` are null and `Ω_i` is certain; a fresh context sees the collapsed state's rates.
* `two_stage_readouts` — both records are on display at the end: on the joint sector the final
  state's first register reads `some i` and its second register reads `some j`.

## ⚠️ Scope

* Rank-one, nondegenerate measurements — the scope of the swap witness; the stage-1 context is the
  computational basis (`momentContext`, matching the vertex calibration), the stage-2 context is
  arbitrary. Degenerate first measurements remain the recorded open construction
  (`DegenerateLuders.lean`).
* The **clock-glued two-epoch `MeasurementProtocol`** on `[0,2]` (one propagator family through
  both readout crossings) is deliberately NOT built: the composed-map form here carries the
  physics; the gluing is presentation, recorded as gated residue in
  `specs/two-time-luders-scoping.md`.
* The **entangled/composite two-time version** (measure a subsystem of an entangled composite,
  then follow up) is Q27's mixed-tier territory — the swap witness over the composite arena with
  `reducedDM` weights — and is not scoped here.
* Hamiltonian generation of the propagators is stated, not formalised, exactly as for the shear
  and swap witnesses.

## References

`specs/two-time-luders-scoping.md` (the Q25 scoping note this executes);
`RecordLayer/SwapLuders.lean` (`swap_luders_marginal`, `cond_prod_cylinder` — the engine);
`RecordLayer/SwapClosure.lean` (`swapPrep`, `swap_sector_born`, `swap_sector_born_ctx`,
`prep_outcome_pos`); `RecordLayer/SwapWitness.lean` (the arena and propagator);
`Empirical/CSD/SequentialMeasurement.lean` (the conditional tier this upgrades);
`specs/BACKLOG.md` (Q25).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {Xsel : Type*} [MeasurableSpace Xsel] {K : ℕ}

/-! ### The two-stage arena and its evolutions -/

/-- The two-stage arena: the swap arena of the first measurement, together with the second
apparatus — a fresh register and a fresh bank. -/
abbrev TwoStageArena (Xsel : Type*) (K : ℕ) :=
  SwapArena Xsel K × (LF4.KTorus × (Fin K → Xsel))

/-- The regrouping shuffle: bring (system, register₂, bank₂) together as a swap arena, with the
stage-1 record coordinates (register₁, bank₁) as spectators. An involution. -/
def regroup (x : TwoStageArena Xsel K) : TwoStageArena Xsel K :=
  (((x.1.1.1, x.2.1), x.2.2), (x.1.1.2, x.1.2))

omit [MeasurableSpace Xsel] in
theorem regroup_regroup (x : TwoStageArena Xsel K) : regroup (regroup x) = x := rfl

theorem measurable_regroup : Measurable (regroup (Xsel := Xsel) (K := K)) := by
  refine Measurable.prodMk (Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_)
    (Measurable.prodMk ?_ ?_)
  · exact measurable_fst.comp (measurable_fst.comp measurable_fst)
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd
  · exact measurable_snd.comp (measurable_fst.comp measurable_fst)
  · exact measurable_snd.comp measurable_fst

/-- Stage 1: the first swap propagator runs on its own arena; the second apparatus is a
spectator. -/
noncomputable def stageOne (idx₁ : Xsel → Fin K) :
    TwoStageArena Xsel K → TwoStageArena Xsel K :=
  Prod.map (swapEvolve idx₁ 0 1) id

/-- Stage 2: the second swap propagator runs on (system, register₂, bank₂); the stage-1 record
coordinates are spectators. The lifted evolution, conjugated by the regrouping shuffle. -/
noncomputable def stageTwo (idx₂ : Xsel → Fin K) :
    TwoStageArena Xsel K → TwoStageArena Xsel K :=
  regroup ∘ Prod.map (swapEvolve idx₂ 0 1) id ∘ regroup

/-- The composed two-time propagator: stage 1, then stage 2. -/
noncomputable def twoStage (idx₁ idx₂ : Xsel → Fin K) :
    TwoStageArena Xsel K → TwoStageArena Xsel K :=
  stageTwo idx₂ ∘ stageOne idx₁

theorem measurable_stageOne (idx₁ : Xsel → Fin K) (h₁ : Measurable idx₁) :
    Measurable (stageOne (K := K) idx₁) :=
  ((measurable_swapEvolve idx₁ h₁ 0 1).comp measurable_fst).prodMk measurable_snd

theorem measurable_stageTwo (idx₂ : Xsel → Fin K) (h₂ : Measurable idx₂) :
    Measurable (stageTwo (K := K) idx₂) :=
  measurable_regroup.comp
    ((((measurable_swapEvolve idx₂ h₂ 0 1).comp measurable_fst).prodMk
      measurable_snd).comp measurable_regroup)

theorem measurable_twoStage (idx₁ idx₂ : Xsel → Fin K)
    (h₁ : Measurable idx₁) (h₂ : Measurable idx₂) :
    Measurable (twoStage (K := K) idx₁ idx₂) :=
  (measurable_stageTwo idx₂ h₂).comp (measurable_stageOne idx₁ h₁)

/-! ### ★ The first record persists — structurally -/

omit [MeasurableSpace Xsel] in
/-- **★ The second measurement never touches the first register.** Definitional: the stage-2
evolution acts through the shuffle, and register₁ rides in the spectator slot. This is what makes
the `t₁` record readable at `t₂`. -/
theorem stageTwo_register₁ (idx₂ : Xsel → Fin K) (x : TwoStageArena Xsel K) :
    (stageTwo idx₂ x).1.1.2 = x.1.1.2 := rfl

omit [MeasurableSpace Xsel] in
/-- The second measurement never touches the first bank — the ontic memory of the first
measurement (the relocated pre-measurement state) survives the second. -/
theorem stageTwo_bank₁ (idx₂ : Xsel → Fin K) (x : TwoStageArena Xsel K) :
    (stageTwo idx₂ x).1.2 = x.1.2 := rfl

/-! ### The record events -/

/-- The event "the first register displays outcome `i`". -/
def recordOneEvent (i : Fin K) : Set (TwoStageArena Xsel K) :=
  {x | x.1.1.2 ∈ pointerArc K i}

/-- The event "the second register displays outcome `j`". -/
def recordTwoEvent (j : Fin K) : Set (TwoStageArena Xsel K) :=
  {x | x.2.1 ∈ pointerArc K j}

/-- **The joint two-record sector**: the initial states destined to display record `i` at `t₁`
and record `j` at `t₂`. -/
def jointRecordSector (idx₁ idx₂ : Xsel → Fin K) (i j : Fin K) :
    Set (TwoStageArena Xsel K) :=
  twoStage idx₁ idx₂ ⁻¹' (recordOneEvent i ∩ recordTwoEvent j)

omit [MeasurableSpace Xsel] in
/-- The first-record event is a cylinder over the first pointer region. -/
theorem recordOneEvent_eq (i : Fin K) :
    recordOneEvent (Xsel := Xsel) i
      = ({y : SwapArena Xsel K | y.1.2 ∈ pointerArc K i}
          ×ˢ (univ : Set (LF4.KTorus × (Fin K → Xsel)))) := by
  ext x
  simp [recordOneEvent, Set.mem_prod]

theorem measurableSet_recordOneEvent (i : Fin K) :
    MeasurableSet (recordOneEvent (Xsel := Xsel) i) :=
  ((measurable_snd.comp (measurable_fst.comp measurable_fst)))
    (measurableSet_pointerArc i)

/-! ### Persistence at the event level -/

omit [MeasurableSpace Xsel] in
/-- **★ Stage 2 does not move the first-record event**: reading register₁ after the second
measurement is reading it before. The event-level form of persistence. -/
theorem stageTwo_preimage_recordOne (idx₂ : Xsel → Fin K) (i : Fin K) :
    stageTwo (Xsel := Xsel) idx₂ ⁻¹' recordOneEvent i = recordOneEvent i := by
  ext x
  show (stageTwo idx₂ x).1.1.2 ∈ pointerArc K i ↔ x.1.1.2 ∈ pointerArc K i
  rw [stageTwo_register₁]

/-- The second-record event pulls back through stage 2 to the second protocol's outcome sector,
cylindered by the shuffle. -/
theorem stageTwo_preimage_recordTwo (idx₂ : Xsel → Fin K) (h₂ : Measurable idx₂) (j : Fin K) :
    stageTwo (Xsel := Xsel) idx₂ ⁻¹' recordTwoEvent j
      = regroup ⁻¹' (((swapProtocol idx₂ h₂).outcomeSector j)
          ×ˢ (univ : Set (LF4.KTorus × (Fin K → Xsel)))) := by
  ext x
  show (stageTwo idx₂ x).2.1 ∈ pointerArc K j
    ↔ (regroup x).1 ∈ (swapProtocol idx₂ h₂).outcomeSector j ∧ (regroup x).2 ∈ univ
  constructor
  · intro h
    exact ⟨h, mem_univ _⟩
  · intro h
    exact h.1

/-! ### Conditioning commutes with a pushforward -/

/-- **Conditioning commutes with a measurable pushforward.** Reusable, no CSD content. -/
theorem cond_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f) {A : Set Y} (hA : MeasurableSet A) :
    ProbabilityTheory.cond (Measure.map f μ) A
      = Measure.map f (ProbabilityTheory.cond μ (f ⁻¹' A)) := by
  show ((Measure.map f μ) A)⁻¹ • (Measure.map f μ).restrict A
    = Measure.map f ((μ (f ⁻¹' A))⁻¹ • μ.restrict (f ⁻¹' A))
  rw [Measure.map_apply hf hA, Measure.restrict_map hf hA, Measure.map_smul' _ _ hf]

/-! ### The generic two-stage composition -/

/-- The generic two-stage preparation: stage-1 system-and-register `μ12` with bank `ν₁`; second
apparatus register `μR₂` with bank `ν₂` — all independent, as fresh apparatus is. -/
noncomputable def twoStagePrep (μ12 : Measure (Xsel × LF4.KTorus))
    (ν₁ : Fin K → Measure Xsel) (μR₂ : Measure LF4.KTorus) (ν₂ : Fin K → Measure Xsel) :
    Measure (TwoStageArena Xsel K) :=
  ((μ12.prod (Measure.pi ν₁)).prod (μR₂.prod (Measure.pi ν₂)))

instance (μ12 : Measure (Xsel × LF4.KTorus)) [IsProbabilityMeasure μ12]
    (ν₁ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₁ j)]
    (μR₂ : Measure LF4.KTorus) [IsProbabilityMeasure μR₂]
    (ν₂ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₂ j)] :
    IsProbabilityMeasure (twoStagePrep μ12 ν₁ μR₂ ν₂) := by
  unfold twoStagePrep
  infer_instance

/-- **The stage-1 record marginal is untouched by composing** — the second apparatus cannot
retro-act on the first record's probability. -/
theorem two_stage_first_record (idx₁ idx₂ : Xsel → Fin K)
    (h₁ : Measurable idx₁)
    (μ12 : Measure (Xsel × LF4.KTorus)) [IsProbabilityMeasure μ12]
    (ν₁ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₁ j)]
    (μR₂ : Measure LF4.KTorus) [IsProbabilityMeasure μR₂]
    (ν₂ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₂ j)] (i : Fin K) :
    twoStagePrep μ12 ν₁ μR₂ ν₂ (twoStage idx₁ idx₂ ⁻¹' recordOneEvent i)
      = (μ12.prod (Measure.pi ν₁)) ((swapProtocol idx₁ h₁).outcomeSector i) := by
  have hpre : twoStage (Xsel := Xsel) idx₁ idx₂ ⁻¹' recordOneEvent i
      = stageOne idx₁ ⁻¹' recordOneEvent i := by
    unfold twoStage
    rw [Set.preimage_comp, stageTwo_preimage_recordOne]
  have hcyl : stageOne (Xsel := Xsel) idx₁ ⁻¹' recordOneEvent i
      = ((swapProtocol idx₁ h₁).outcomeSector i)
          ×ˢ (univ : Set (LF4.KTorus × (Fin K → Xsel))) := by
    ext x
    show (swapEvolve idx₁ 0 1 x.1).1.2 ∈ pointerArc K i
      ↔ x.1 ∈ (swapProtocol idx₁ h₁).outcomeSector i ∧ x.2 ∈ univ
    constructor
    · intro h
      exact ⟨h, mem_univ _⟩
    · intro h
      exact h.1
  rw [hpre, hcyl]
  rw [twoStagePrep, Measure.prod_prod, measure_univ, mul_one]

/-- **★★ The generic two-stage composition.** The joint two-record probability factors as
(stage-1 sector measure) × (stage-2 sector measure at the relocated state): conditioned on the
first record, the second apparatus sees the slot-`i` calibration as its system
(`swap_luders_marginal`) with its own fresh register and bank, so the stage-2 record probability
is the single-measurement sector probability at that input. The stage-2 record event never reads
the stage-1 record coordinates — only the system marginal of the conditioned state enters. -/
theorem two_stage_joint (idx₁ idx₂ : Xsel → Fin K)
    (h₁ : Measurable idx₁) (h₂ : Measurable idx₂)
    (μ12 : Measure (Xsel × LF4.KTorus)) [IsProbabilityMeasure μ12]
    (ν₁ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₁ j)]
    (μR₂ : Measure LF4.KTorus) [IsProbabilityMeasure μR₂]
    (ν₂ : Fin K → Measure Xsel) [∀ j, IsProbabilityMeasure (ν₂ j)] (i j : Fin K)
    (hpos : μ12 ((shearProtocol idx₁ h₁).outcomeSector i) ≠ 0) :
    twoStagePrep μ12 ν₁ μR₂ ν₂ (jointRecordSector idx₁ idx₂ i j)
      = (μ12.prod (Measure.pi ν₁)) ((swapProtocol idx₁ h₁).outcomeSector i)
        * (((ν₁ i).prod μR₂).prod (Measure.pi ν₂))
            ((swapProtocol idx₂ h₂).outcomeSector j) := by
  classical
  set μ₁ := μ12.prod (Measure.pi ν₁) with hμ₁
  set app₂ := μR₂.prod (Measure.pi ν₂) with happ₂
  set E₁ := swapEvolve idx₁ 0 1 with hE₁
  have hE₁meas : Measurable E₁ := measurable_swapEvolve idx₁ h₁ 0 1
  have : IsProbabilityMeasure (Measure.map E₁ μ₁) :=
    Measure.isProbabilityMeasure_map' hE₁meas.aemeasurable
  have hA₁meas : MeasurableSet {y : SwapArena Xsel K | y.1.2 ∈ pointerArc K i} :=
    (measurable_snd.comp measurable_fst) (measurableSet_pointerArc i)
  have hsec0 : μ₁ ((swapProtocol idx₁ h₁).outcomeSector i) ≠ 0 := by
    rw [hμ₁, swap_outcomeSector_cylinder idx₁ h₁ i, Measure.prod_prod, measure_univ,
      mul_one]
    exact hpos
  have hselprob : IsProbabilityMeasure ((swapProtocol idx₁ h₁).selectedMeasure μ₁ i) := by
    rw [MeasurementProtocol.selectedMeasure]
    exact ProbabilityTheory.cond_isProbabilityMeasure hsec0
  have hpostprob : IsProbabilityMeasure ((swapProtocol idx₁ h₁).postMeasure μ₁ i) := by
    rw [MeasurementProtocol.postMeasure]
    exact Measure.isProbabilityMeasure_map'
      ((swapProtocol idx₁ h₁).measurable_evolve _ _).aemeasurable
  -- the events, downstairs
  set C := recordOneEvent (Xsel := Xsel) i with hCdef
  set D := regroup (Xsel := Xsel) (K := K) ⁻¹'
    (((swapProtocol idx₂ h₂).outcomeSector j)
      ×ˢ (univ : Set (LF4.KTorus × (Fin K → Xsel)))) with hDdef
  have hCmeas : MeasurableSet C := measurableSet_recordOneEvent i
  have hDmeas : MeasurableSet D :=
    measurable_regroup (((swapProtocol idx₂ h₂).outcomeSector_measurable j).prod
      MeasurableSet.univ)
  -- Step 1: the joint sector is the stage-one preimage of C ∩ D.
  have hjoint : jointRecordSector (Xsel := Xsel) idx₁ idx₂ i j
      = stageOne idx₁ ⁻¹' (C ∩ D) := by
    unfold jointRecordSector twoStage
    rw [Set.preimage_comp, Set.preimage_inter, stageTwo_preimage_recordOne,
      stageTwo_preimage_recordTwo idx₂ h₂]
  -- Step 2: push the preparation through stage one.
  have hmap1 : Measure.map (stageOne (K := K) idx₁) (twoStagePrep μ12 ν₁ μR₂ ν₂)
      = (Measure.map E₁ μ₁).prod app₂ := by
    show Measure.map (Prod.map E₁ id) (μ₁.prod app₂) = (Measure.map E₁ μ₁).prod app₂
    rw [← Measure.map_prod_map _ _ hE₁meas measurable_id, Measure.map_id]
  have hpush : twoStagePrep μ12 ν₁ μR₂ ν₂ (jointRecordSector idx₁ idx₂ i j)
      = ((Measure.map E₁ μ₁).prod app₂) (C ∩ D) := by
    rw [hjoint, ← Measure.map_apply (measurable_stageOne idx₁ h₁) (hCmeas.inter hDmeas),
      hmap1]
  -- Step 3: the C-probability is the stage-1 sector measure.
  have hsector₁ : E₁ ⁻¹' {y : SwapArena Xsel K | y.1.2 ∈ pointerArc K i}
      = (swapProtocol idx₁ h₁).outcomeSector i := rfl
  have hC : ((Measure.map E₁ μ₁).prod app₂) C
      = μ₁ ((swapProtocol idx₁ h₁).outcomeSector i) := by
    rw [hCdef, recordOneEvent_eq, Measure.prod_prod, measure_univ, mul_one,
      Measure.map_apply hE₁meas hA₁meas, hsector₁]
  -- and it is nonzero, from the shear-sector positivity.
  have hC0 : ((Measure.map E₁ μ₁).prod app₂) C ≠ 0 := by
    rw [hC]
    exact hsec0
  -- Step 4: split off the conditioning on C.
  have hsplit : ((Measure.map E₁ μ₁).prod app₂) (C ∩ D)
      = ((Measure.map E₁ μ₁).prod app₂) C
        * ProbabilityTheory.cond ((Measure.map E₁ μ₁).prod app₂) C D := by
    rw [ProbabilityTheory.cond_apply hCmeas, ← mul_assoc,
      ENNReal.mul_inv_cancel hC0 (measure_ne_top _ _), one_mul]
  -- Step 5: the conditioned measure is the post-measurement state with fresh apparatus.
  have hcond : ProbabilityTheory.cond ((Measure.map E₁ μ₁).prod app₂) C
      = ((swapProtocol idx₁ h₁).postMeasure μ₁ i).prod app₂ := by
    rw [hCdef, recordOneEvent_eq, cond_prod_cylinder]
    congr 1
    rw [cond_map μ₁ hE₁meas hA₁meas]
    rw [MeasurementProtocol.postMeasure, MeasurementProtocol.selectedMeasure]
    rfl
  -- Step 6: the D-probability under the conditioned measure — only the system marginal enters.
  have hD : (((swapProtocol idx₁ h₁).postMeasure μ₁ i).prod app₂) D
      = (((ν₁ i).prod μR₂).prod (Measure.pi ν₂))
          ((swapProtocol idx₂ h₂).outcomeSector j) := by
    -- the event reads only (system, register₂, bank₂)
    have hg : D = (fun x : TwoStageArena Xsel K =>
        (MeasurableEquiv.prodAssoc.symm
          (Prod.map (fun y : SwapArena Xsel K => y.1.1) id x)))
        ⁻¹' ((swapProtocol idx₂ h₂).outcomeSector j) := by
      ext x
      show (regroup x).1 ∈ (swapProtocol idx₂ h₂).outcomeSector j ∧ (regroup x).2 ∈ univ
        ↔ ((x.1.1.1, x.2.1), x.2.2) ∈ (swapProtocol idx₂ h₂).outcomeSector j
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, mem_univ _⟩
    have hproj : Measurable fun y : SwapArena Xsel K => y.1.1 :=
      measurable_fst.comp measurable_fst
    have hpm : Measurable (Prod.map (fun y : SwapArena Xsel K => y.1.1)
        (id : LF4.KTorus × (Fin K → Xsel) → LF4.KTorus × (Fin K → Xsel))) :=
      (hproj.comp measurable_fst).prodMk measurable_snd
    have hgmeas : Measurable (fun x : TwoStageArena Xsel K =>
        (MeasurableEquiv.prodAssoc.symm
          (Prod.map (fun y : SwapArena Xsel K => y.1.1) id x))) :=
      MeasurableEquiv.prodAssoc.symm.measurable.comp hpm
    -- the law of that block is the relocated state with fresh apparatus
    have hlaw : Measure.map (fun x : TwoStageArena Xsel K =>
        (MeasurableEquiv.prodAssoc.symm
          (Prod.map (fun y : SwapArena Xsel K => y.1.1) id x)))
        (((swapProtocol idx₁ h₁).postMeasure μ₁ i).prod app₂)
        = ((ν₁ i).prod μR₂).prod (Measure.pi ν₂) := by
      rw [show (fun x : TwoStageArena Xsel K =>
          (MeasurableEquiv.prodAssoc.symm
            (Prod.map (fun y : SwapArena Xsel K => y.1.1) id x)))
          = (⇑MeasurableEquiv.prodAssoc.symm
              ∘ Prod.map (fun y : SwapArena Xsel K => y.1.1) id) from rfl]
      rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable hpm]
      rw [← Measure.map_prod_map _ _ hproj measurable_id, Measure.map_id]
      rw [hμ₁, swap_luders_marginal idx₁ h₁ μ12 ν₁ i hpos, happ₂]
      exact ((measurePreserving_prodAssoc (ν₁ i) μR₂ (Measure.pi ν₂)).symm
        MeasurableEquiv.prodAssoc).map_eq
    rw [hg, ← Measure.map_apply hgmeas ((swapProtocol idx₂ h₂).outcomeSector_measurable j),
      hlaw]
  calc twoStagePrep μ12 ν₁ μR₂ ν₂ (jointRecordSector idx₁ idx₂ i j)
      = ((Measure.map E₁ μ₁).prod app₂) (C ∩ D) := hpush
    _ = ((Measure.map E₁ μ₁).prod app₂) C
        * ProbabilityTheory.cond ((Measure.map E₁ μ₁).prod app₂) C D := hsplit
    _ = μ₁ ((swapProtocol idx₁ h₁).outcomeSector i)
        * (((ν₁ i).prod μR₂).prod (Measure.pi ν₂))
            ((swapProtocol idx₂ h₂).outcomeSector j) := by
        rw [hC, hcond, hD]

/-! ### The CSD forms -/

variable {N : ℕ} [NeZero N]

/-- The canonical two-stage preparation: system at `p` with ready register and vertex-calibrated
bank for the first measurement, fresh ready register and vertex-calibrated bank for the second. -/
noncomputable def csdTwoPrep (p : LF4.CPN N) : Measure (TwoStageArena (LF4.KSigma N) N) :=
  twoStagePrep (readyPrep p) (fun k => epistemicMeasure (vertexPoint k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k))

instance (p : LF4.CPN N) : IsProbabilityMeasure (csdTwoPrep p) := by
  unfold csdTwoPrep
  infer_instance

/-- **★★ The two-time Born law, on one arena.** For the canonical ready preparation at `p`,
measured in the computational basis at `t₁` and in an ARBITRARY context `c₂` at `t₂`:

  `P(record i at t₁ ∧ record j at t₂) = momentMap p i · c₂.rate [eᵢ] j`.

The first factor is the dynamical Born weight of the preparation; the second is the Born weight of
the COLLAPSED state `[eᵢ]` in the second context — Born-then-Lüders-Born as one number, with both
records on one arena and the first persisting through the second measurement. This is the composed
two-time statement `csd_sequential_born` (a conditional) could not express. -/
theorem two_time_born (p : LF4.CPN N) (i : Fin N) (hpos : LF4.momentMap p i ≠ 0)
    (c₂ : ContextField N) (j : Fin N) :
    csdTwoPrep p (jointRecordSector (basinIndex (momentContext N)) (basinIndex c₂) i j)
      = ENNReal.ofReal (LF4.momentMap p i) * ENNReal.ofReal (c₂.rate (vertexPoint i) j) := by
  rw [csdTwoPrep, two_stage_joint (basinIndex (momentContext N)) (basinIndex c₂)
    (measurable_basinIndex (momentContext N)) (measurable_basinIndex c₂)
    (readyPrep p) (fun k => epistemicMeasure (vertexPoint k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k)) i j (prep_outcome_pos p i hpos)]
  congr 1
  · exact swap_sector_born p i
  · exact swap_sector_born_ctx c₂ (vertexPoint i) j

/-- **★ Von Neumann repeatability, in composed two-time form.** Measure the computational basis
twice: the joint law is `momentMap p i · δᵢⱼ` — the same outcome recurs, any other pair of records
has probability zero, as ONE statement about the two-record sector. -/
theorem two_time_repeat (p : LF4.CPN N) (i : Fin N) (hpos : LF4.momentMap p i ≠ 0)
    (j : Fin N) :
    csdTwoPrep p (jointRecordSector (basinIndex (momentContext N))
      (basinIndex (momentContext N)) i j)
      = ENNReal.ofReal (LF4.momentMap p i) * (if j = i then 1 else 0) := by
  rw [two_time_born p i hpos (momentContext N) j, momentContext_rate, momentMap_vertex]
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- The stage-1 record marginal, in CSD form: composing does not disturb the first Born law. -/
theorem two_time_first_record (p : LF4.CPN N) (c₂ : ContextField N) (i : Fin N) :
    csdTwoPrep p (twoStage (basinIndex (momentContext N)) (basinIndex c₂)
      ⁻¹' recordOneEvent i)
      = ENNReal.ofReal (LF4.momentMap p i) := by
  rw [csdTwoPrep, two_stage_first_record (basinIndex (momentContext N)) (basinIndex c₂)
    (measurable_basinIndex (momentContext N))
    (readyPrep p) (fun k => epistemicMeasure (vertexPoint k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k)) i]
  exact swap_sector_born p i

/-- **★ The fate of the other `Ω_j` — the conditioned re-partition the next context sees.**
CONDITIONED on record `i` at `t₁`, the probability of record `j` at `t₂` is the collapsed state's
rate `c₂.rate [eᵢ] j`. For the repeated context (`c₂ = momentContext`) this makes every other
`Ω_j` NULL and `Ω_i` certain (`momentMap_vertex`); for a fresh context it is the Lüders-updated
Born law. The post-outcome fate of the other regions, stated as a conditional probability on the
composed arena. -/
theorem two_time_other_fate (p : LF4.CPN N) (i : Fin N) (hpos : LF4.momentMap p i ≠ 0)
    (c₂ : ContextField N) (j : Fin N) :
    ProbabilityTheory.cond (csdTwoPrep p)
        (twoStage (basinIndex (momentContext N)) (basinIndex c₂) ⁻¹' recordOneEvent i)
        (twoStage (basinIndex (momentContext N)) (basinIndex c₂) ⁻¹' recordTwoEvent j)
      = ENNReal.ofReal (c₂.rate (vertexPoint i) j) := by
  have hmeas₁ : MeasurableSet (twoStage (basinIndex (momentContext N)) (basinIndex c₂)
      ⁻¹' recordOneEvent (Xsel := LF4.KSigma N) i) :=
    measurable_twoStage _ _ (measurable_basinIndex (momentContext N))
      (measurable_basinIndex c₂) (measurableSet_recordOneEvent i)
  rw [ProbabilityTheory.cond_apply hmeas₁, ← Set.preimage_inter, two_time_first_record p c₂ i]
  have hjoint : twoStage (basinIndex (momentContext N)) (basinIndex c₂)
      ⁻¹' (recordOneEvent i ∩ recordTwoEvent j)
      = jointRecordSector (basinIndex (momentContext N)) (basinIndex c₂) i j := rfl
  rw [hjoint, two_time_born p i hpos c₂ j, ← mul_assoc,
    ENNReal.inv_mul_cancel (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_le_of_ne (LF4.momentMap_nonneg p i) (Ne.symm hpos))
      ENNReal.ofReal_ne_top, one_mul]

/-! ### Both records on display -/

/-- **★ Both records are visible at `t₂`.** On the joint sector, the final state's first register
reads `some i` — the persisting `t₁` record — and its second register reads `some j`, through each
protocol's own readout. -/
theorem two_stage_readouts (idx₁ idx₂ : Xsel → Fin K)
    (h₁ : Measurable idx₁) (h₂ : Measurable idx₂) {i j : Fin K}
    {x : TwoStageArena Xsel K} (hx : x ∈ jointRecordSector idx₁ idx₂ i j) :
    (swapProtocol idx₁ h₁).readout (twoStage idx₁ idx₂ x).1 = some i
      ∧ (swapProtocol idx₂ h₂).readout (regroup (twoStage idx₁ idx₂ x)).1 = some j := by
  obtain ⟨hx₁, hx₂⟩ := hx
  constructor
  · exact ((swapProtocol idx₁ h₁).readout_eq_some_iff _ i).mpr hx₁
  · exact ((swapProtocol idx₂ h₂).readout_eq_some_iff _ j).mpr hx₂

end CSD.RecordLayer
