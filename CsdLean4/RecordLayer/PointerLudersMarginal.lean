/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerLuders
public import CsdLean4.RecordLayer.SwapLuders
public import CsdLean4.Mathlib.MeasureTheory.PiecewisePreserving

/-!
# SigmaLayer/PointerLudersMarginal: the smooth horn's Lüders theorem (B3b, brick 2)

**Category:** dynamical measurement — `specs/BACKLOG.md` **B3b**, second (final) brick.

**Glossary:** https://glossary.constraintsurfacedynamics.com/luders-rule/
Plain-language, CSD-role and formal statements of the Luders rule, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

## What brick 1 owed, delivered here

Brick 1 (`PointerLuders.lean`) built the composed arena `(Σ × ℂℙ^N) × bank` and *defined*
the two-stroke composite — smooth record stroke, then record-triggered relocation — while
explicitly not claiming two things. Both are proved here:

* ★ `pointerRelocate_measurePreserving` — the **piecewise invariance**. The relocation is a
  case split on the readout, so its invariance is the partition argument the torus witness
  used for `swapG`, with **record cylinders in place of register arcs**: the arena splits
  into the no-record piece (where the relocation is the identity) and one record cylinder
  per outcome (where it is the slot swap, measure-preserving by brick 1, and *fixes its own
  piece* because the relocation never moves the pointer). `measurePreserving_of_partition`
  does the rest. Corollary ★ `pointerLudersStroke_measurePreserving`: the **whole two-stroke
  composite conserves Liouville measure** — collapse as relocation, not contraction, on the
  smooth horn too.
* ★★ `pointer_luders_marginal` — the **conditioned post-measurement marginal**, the actual
  Lüders theorem: conditioned on the outcome-`i` sector, the post-stroke **system marginal
  is the slot-`i` calibration**, exactly the swap witness's headline
  (`swap_luders_marginal`) with the trigger read off the pointer's record region instead of
  a torus arc. The proof has the same three moves: the sector is a **base cylinder** (the
  bank plays no part in which outcome occurs), so conditioning never touches the bank
  (`cond_prod_cylinder`); on the sector the post-stroke system coordinate *is* bank slot
  `i`; and evaluation pushes the bank product to its `i`-th factor (`Measure.map_eval_pi'`).
* ★ `pointer_luders_born` — the CSD form: slots calibrated to the vertex preparations make
  every follow-up outcome-`j` probability `c'.rate [eᵢ] j` — Born of the **collapsed**
  state, for any context field.
* ★★ `pointer_luders_born_prep` — the payoff, on the witness's **own** preparation
  `pointerPrep`: whenever `2ε < rate i`, the `ε`-Born lower bound makes the conditioning
  non-vacuous, so the smooth witness now delivers records (ε-Born, brick 4b/B3a) **and** a
  Lüders update (this module) on one arena. **B3b closes.**

## Why this does not contradict the no-collapse results

`pointerEvolve_base_marginal_unchanged` still holds: the *smooth stroke* does not collapse.
The update is the *second* stroke, and it moves the system by **relocation** — the slot
swap exchanges volume 1:1 (`pointerRelocate_measurePreserving`), so `no_exact_collapse` is
not in play. After the swap, slot `i` holds the pre-measurement system state: a perfect
ontic memory, with irreversibility priced only at erasure (`collapse_accuracy_bound`).

## ⚠️ Honest scope

* **Rank-one / nondegenerate only**, exactly as for the swap witness: the bank calibration
  is one preparation per outcome. Degenerate blocks live on the join witness
  (`JoinClosure`), not here.
* **The calibration is a context-fixed epistemic posit** (`epistemicMeasure (vertexPoint k)`
  depends on the basis alone, never on `ψ`) — A7-compatible, same status as the swap's.
* **One measurement consumes one bank**; resetting is erasure, outside the protocol.
* **The two-stroke composite is not packaged as a `MeasurementProtocol`**: the relocation is
  a triggered map, not a flow, so the composite has no two-time law to offer. The sector
  conditioned on is the *smooth protocol's own* outcome sector, cylindered over the bank —
  which is also the honest statement that the bank plays no part in outcome selection.
  Realising the relocation as a Hamiltonian stroke is the same recorded extension it is for
  the swap witness.
* The `ε`-horn price stands: the sector mass is bracketed, not pinned
  (`pointer_born_lower`/`_upper`), and `pointer_luders_born_prep` needs `2ε < rate i`. The
  *conditioned* marginal, by contrast, is **exact** — the ε lives in which outcome occurs,
  not in the post-measurement state.

## References

`specs/BACKLOG.md` B3b; `SigmaLayer/PointerLuders.lean` (brick 1 — arena, relocation, slot
swap); `SigmaLayer/SwapLuders.lean` (`swap_luders_marginal`, `cond_prod_cylinder` — the
torus-triggered original whose shape this transports); `Mathlib/MeasureTheory/`
`PiecewisePreserving.lean` (`measurePreserving_of_partition`, `Measure.map_eval_pi'`);
`SigmaLayer/PointerBorn.lean` (`pointerPrep`, `pointer_born_lower` — the non-vacuity
supply); `SigmaLayer/GlobalBasin.lean` (`epistemicMeasure`, `globalBasin_prob`);
`SigmaLayer/PointerGeneration.lean` (`pointerEvolve_base_marginal_unchanged` — why the
update needed a second stroke at all).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Set Matrix.UnitaryGroup

variable {N : ℕ} [NeZero N]

/-! ### The relocation partition: record cylinders and the no-record piece -/

/-- The relocation's partition piece for label `k`: the record cylinder for `some j`, the
no-record set for `none`. -/
def relocPiece (N : ℕ) : Option (Fin N) → Set (PointerLudersArena N)
  | none => (⋃ j, {y : PointerLudersArena N | y.1.2 ∈ recordRegion j})ᶜ
  | some j => {y : PointerLudersArena N | y.1.2 ∈ recordRegion j}

/-- The relocation's piece map for label `k`: the slot swap on a record cylinder, the
identity on the no-record piece. -/
def relocMap (N : ℕ) : Option (Fin N) → PointerLudersArena N → PointerLudersArena N
  | none => id
  | some j => pointerBankSwap j

omit [NeZero N] in
theorem measurableSet_relocPiece (k : Option (Fin N)) :
    MeasurableSet (relocPiece N k) := by
  have hcyl : ∀ j : Fin N,
      MeasurableSet {y : PointerLudersArena N | y.1.2 ∈ recordRegion j} := fun j =>
    (measurable_snd.comp measurable_fst) (measurableSet_recordRegion j)
  match k with
  | none => exact (MeasurableSet.iUnion hcyl).compl
  | some j => exact hcyl j

omit [NeZero N] in
theorem relocPiece_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint (relocPiece N)) := by
  intro k l hkl
  match k, l with
  | none, none => exact absurd rfl hkl
  | none, some j =>
    refine Set.disjoint_left.mpr fun y hy hyj => ?_
    exact hy (Set.mem_iUnion.mpr ⟨j, hyj⟩)
  | some j, none =>
    refine Set.disjoint_left.mpr fun y hyj hy => ?_
    exact hy (Set.mem_iUnion.mpr ⟨j, hyj⟩)
  | some j, some l' =>
    have hjl : j ≠ l' := fun h => hkl (by rw [h])
    refine Set.disjoint_left.mpr fun y hyj hyl => ?_
    have h1 : y.1.2 ∈ recordRegion j := hyj
    have h2 : y.1.2 ∈ recordRegion l' := hyl
    exact Set.disjoint_left.mp (recordRegion_pairwiseDisjoint hjl) h1 h2

omit [NeZero N] in
theorem relocPiece_cover : (⋃ k, relocPiece N k) = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases h : ∃ j, y.1.2 ∈ recordRegion j
  · obtain ⟨j, hj⟩ := h
    exact ⟨some j, hj⟩
  · refine ⟨none, fun hmem => h ?_⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    exact ⟨j, hj⟩

omit [NeZero N] in
/-- The readout is `none` off every record region. -/
theorem pointerIndex_eq_none {q : Pointer N} (h : ¬∃ j, q ∈ recordRegion j) :
    pointerIndex q = none := by
  classical
  rw [pointerIndex, dif_neg h]

omit [NeZero N] in
/-- Off every record region, the relocation does nothing. -/
theorem pointerRelocate_of_noRecord {y : PointerLudersArena N}
    (h : ¬∃ j, y.1.2 ∈ recordRegion j) : pointerRelocate y = y := by
  unfold pointerRelocate
  rw [pointerIndex_eq_none h]

omit [NeZero N] in
/-- The relocation agrees with the piece map on each piece. -/
theorem pointerRelocate_agree (k : Option (Fin N)) :
    ∀ y ∈ relocPiece N k, pointerRelocate y = relocMap N k y := by
  match k with
  | none =>
    intro y hy
    refine pointerRelocate_of_noRecord fun hex => ?_
    obtain ⟨j, hj⟩ := hex
    exact hy (Set.mem_iUnion.mpr ⟨j, hj⟩)
  | some j =>
    intro y hy
    have h1 : y.1.2 ∈ recordRegion j := hy
    exact pointerRelocate_of_record h1

omit [NeZero N] in
/-- Each piece map fixes its own piece as a preimage — the slot swap never moves the
pointer, so a record cylinder is invariant. -/
theorem relocMap_fixes_piece (k : Option (Fin N)) :
    relocMap N k ⁻¹' relocPiece N k = relocPiece N k := by
  match k with
  | none => exact Set.preimage_id
  | some j =>
    ext y
    exact Iff.rfl

omit [NeZero N] in
theorem measurable_pointerBankSwap (j : Fin N) :
    Measurable (pointerBankSwap (N := N) j) := by
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · exact (measurable_pi_apply j).comp measurable_snd
  · exact measurable_snd.comp measurable_fst
  · exact measurable_update'.comp
      (measurable_snd.prodMk (measurable_fst.comp measurable_fst))

omit [NeZero N] in
theorem measurable_relocMap (k : Option (Fin N)) : Measurable (relocMap N k) := by
  match k with
  | none => exact measurable_id
  | some j => exact measurable_pointerBankSwap j

omit [NeZero N] in
/-- **The relocation is measurable** — piecewise, over the record-cylinder partition. -/
theorem measurable_pointerRelocate : Measurable (pointerRelocate (N := N)) :=
  measurable_of_partition measurableSet_relocPiece relocPiece_cover
    measurable_relocMap pointerRelocate_agree

omit [NeZero N] in
/-- ★ **The record-triggered relocation preserves the arena measure** — brick 1's
explicitly-owed piecewise invariance. On each record cylinder the relocation is the slot
swap (measure-preserving, `pointerBankSwap_measurePreserving`) and the cylinder is its own
preimage (`pointerRelocate_pointer`: the relocation never moves the pointer); off every
record region it is the identity. `measurePreserving_of_partition` assembles the pieces —
the same argument the torus witness used for `swapG`, with record cylinders in place of
register arcs. -/
theorem pointerRelocate_measurePreserving (μs : Measure (LF4.KSigma N))
    [IsProbabilityMeasure μs] (q₀ : Pointer N) :
    MeasurePreserving (pointerRelocate (N := N))
      (pointerLudersMeasure μs q₀) (pointerLudersMeasure μs q₀) := by
  refine measurePreserving_of_partition measurableSet_relocPiece
    relocPiece_pairwiseDisjoint relocPiece_cover measurable_pointerRelocate
    (fun k => ?_) pointerRelocate_agree relocMap_fixes_piece
  match k with
  | none => exact MeasurePreserving.id _
  | some j => exact pointerBankSwap_measurePreserving μs q₀ j

/-! ### The smooth stroke on the composed arena -/

omit [NeZero N] in
/-- The smooth stroke preserves `μs ⊗ μ_FS` for **any** s-finite sector measure — the skew
product over the pointer factor, with each slice an FS-preserving unitary. (The brick-2b
statement `pointerEvolve_measurePreserving` is the `pointerLiouville` instance.) -/
theorem pointerEvolve_measurePreserving_prod (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ)
    (μs : Measure (LF4.KSigma N)) [SFinite μs] (q₀ : Pointer N) :
    MeasurePreserving (pointerEvolve c ε)
      (μs.prod (fubiniStudyMeasure q₀)) (μs.prod (fubiniStudyMeasure q₀)) := by
  unfold pointerEvolve
  exact (MeasurePreserving.id μs).skew_product
    (continuous_pointerEvolve_snd c hc ε).measurable
    (Filter.Eventually.of_forall fun x =>
      (couplingUU_measurePreserving (pointerWeights c ε x) q₀).map_eq)

omit [NeZero N] in
theorem measurable_pointerLudersStroke (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) :
    Measurable (pointerLudersStroke c ε) :=
  measurable_pointerRelocate.comp
    (((continuous_pointerEvolve c hc ε).measurable.comp measurable_fst).prodMk
      measurable_snd)

omit [NeZero N] in
/-- ★ **The two-stroke composite conserves Liouville measure**: record stroke (skew
product) then relocation (piecewise slot swap). Collapse as relocation, not contraction —
`no_exact_collapse` is respected because volume is exchanged 1:1, on the smooth horn
exactly as on the exact horns. -/
theorem pointerLudersStroke_measurePreserving (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ)
    (μs : Measure (LF4.KSigma N)) [IsProbabilityMeasure μs] (q₀ : Pointer N) :
    MeasurePreserving (pointerLudersStroke c ε)
      (pointerLudersMeasure μs q₀) (pointerLudersMeasure μs q₀) := by
  have h1 : MeasurePreserving
      (fun y : PointerLudersArena N => (pointerEvolve c ε y.1, y.2))
      (pointerLudersMeasure μs q₀) (pointerLudersMeasure μs q₀) := by
    unfold pointerLudersMeasure
    exact (pointerEvolve_measurePreserving_prod c hc ε μs q₀).prod
      (MeasurePreserving.id _)
  exact (pointerRelocate_measurePreserving μs q₀).comp h1

/-! ### The conditioned post-measurement marginal -/

omit [NeZero N] in
/-- **The sector identification**: the smooth protocol's outcome sector is the brick-2b
propagator's preimage of the record cylinder. Pins down the trigger the relocation reads. -/
theorem pointerProtocol_outcomeSector (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hδ : δ ≤ 1 / 2) (i : Fin N) :
    (pointerProtocol c hc ε hδ).outcomeSector i
      = pointerEvolve c ε ⁻¹' arenaRecord N i := by
  have h : (pointerProtocol c hc ε hδ).outcomeSector i
      = (pointerProtocol c hc ε hδ).evolve 0 1 ⁻¹' arenaRecord N i := rfl
  rw [h, pointerProtocol_evolve_stroke]

omit [NeZero N] in
/-- On the outcome-`i` sector, the post-stroke system coordinate is bank slot `i`: the
stroke lands the pointer in `recordRegion i`, so the relocation is the slot-`i` swap. -/
theorem pointerLudersStroke_sys_on_sector (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hδ : δ ≤ 1 / 2) (i : Fin N)
    {y : PointerLudersArena N}
    (hy : y.1 ∈ (pointerProtocol c hc ε hδ).outcomeSector i) :
    (pointerLudersStroke c ε y).1.1 = y.2 i := by
  rw [pointerProtocol_outcomeSector c hc hδ i] at hy
  have hmem : pointerEvolve c ε y.1
      ∈ (Set.univ ×ˢ recordRegion i : Set (PointerArena N N)) := hy
  have hrec : (pointerEvolve c ε y.1).2 ∈ recordRegion i := (Set.mem_prod.mp hmem).2
  have hstroke : pointerLudersStroke c ε y
      = pointerBankSwap i (pointerEvolve c ε y.1, y.2) := by
    show pointerRelocate (pointerEvolve c ε y.1, y.2)
        = pointerBankSwap i (pointerEvolve c ε y.1, y.2)
    exact pointerRelocate_of_record hrec
  rw [hstroke]
  rfl

omit [NeZero N] in
/-- ★★ **The Lüders update for the smooth horn, as a pushforward.**

Initial state: system-and-pointer `μsp`, bank slots independently calibrated to `ν j`.
Conditioned on the outcome-`i` sector — the *smooth protocol's own* sector, cylindered over
the bank, which is the statement that the bank plays no part in which outcome occurs — the
post-stroke **system marginal is the slot-`i` calibration**. Collapse as measure-preserving
relocation, now on the smooth horn: the same three moves as `swap_luders_marginal`, with
the trigger read off the pointer's record region instead of a torus arc. The conditioned
marginal is **exact**; the `ε` lives only in which outcome occurs. -/
theorem pointer_luders_marginal (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hδ : δ ≤ 1 / 2)
    (μsp : Measure (PointerArena N N)) [IsProbabilityMeasure μsp]
    (ν : Fin N → Measure (LF4.KSigma N)) [∀ j, IsProbabilityMeasure (ν j)] (i : Fin N)
    (hpos : μsp ((pointerProtocol c hc ε hδ).outcomeSector i) ≠ 0) :
    Measure.map (fun y : PointerLudersArena N => y.1.1)
      (Measure.map (pointerLudersStroke c ε)
        (ProbabilityTheory.cond (μsp.prod (Measure.pi ν))
          ((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)))
      = ν i := by
  classical
  have hCmeas : MeasurableSet ((pointerProtocol c hc ε hδ).outcomeSector i) :=
    (pointerProtocol c hc ε hδ).outcomeSector_measurable i
  -- conditioning on the base cylinder conditions the base factor
  have hcond : ProbabilityTheory.cond (μsp.prod (Measure.pi ν))
      ((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)
      = (ProbabilityTheory.cond μsp
          ((pointerProtocol c hc ε hδ).outcomeSector i)).prod (Measure.pi ν) :=
    cond_prod_cylinder μsp (Measure.pi ν) _
  have hmeas_st : Measurable (pointerLudersStroke c ε) :=
    measurable_pointerLudersStroke c hc ε
  have hmeas_proj : Measurable (fun y : PointerLudersArena N => y.1.1) :=
    measurable_fst.comp measurable_fst
  rw [Measure.map_map hmeas_proj hmeas_st]
  -- a.e. on the conditioned measure, projection-after-stroke is evaluation at slot `i`
  have hnull : ProbabilityTheory.cond (μsp.prod (Measure.pi ν))
      ((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)
      (((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)ᶜ) = 0 := by
    rw [ProbabilityTheory.cond_apply (hCmeas.prod MeasurableSet.univ),
      Set.inter_compl_self, measure_empty, mul_zero]
  have hae : ((fun y : PointerLudersArena N => y.1.1) ∘ pointerLudersStroke c ε)
      =ᵐ[ProbabilityTheory.cond (μsp.prod (Measure.pi ν))
          ((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)]
      (fun y : PointerLudersArena N => y.2 i) := by
    filter_upwards [MeasureTheory.mem_ae_iff.mpr hnull] with y hy
    exact pointerLudersStroke_sys_on_sector c hc hδ i (Set.mem_prod.mp hy).1
  rw [Measure.map_congr hae, hcond]
  -- evaluation pushes the bank product to its `i`-th factor
  have hfactor : (fun y : PointerLudersArena N => y.2 i)
      = (Function.eval i) ∘ (Prod.snd : PointerLudersArena N → (Fin N → LF4.KSigma N)) :=
    rfl
  rw [hfactor, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod]
  have : IsProbabilityMeasure (ProbabilityTheory.cond μsp
      ((pointerProtocol c hc ε hδ).outcomeSector i)) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  rw [measure_univ, one_smul, Measure.map_eval_pi']

/-! ### The CSD form: sequential statistics are Lüders on the smooth horn -/

omit [NeZero N] in
/-- ★ **Lüders for CSD on the smooth horn**: with the bank calibrated to the vertex
preparations, the post-outcome-`i` system marginal is `epistemicMeasure (vertexPoint i)`,
so for **any** context field `c'` the follow-up outcome-`j` probability is
`c'.rate [eᵢ] j` — Born of the *collapsed* state. The system after the measurement behaves,
in every subsequent measurement, exactly as a fresh preparation of `eᵢ`. -/
theorem pointer_luders_born (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hδ : δ ≤ 1 / 2)
    (μsp : Measure (PointerArena N N)) [IsProbabilityMeasure μsp] (i : Fin N)
    (hpos : μsp ((pointerProtocol c hc ε hδ).outcomeSector i) ≠ 0)
    (c' : ContextField N) (j : Fin N) :
    (Measure.map (pointerLudersStroke c ε)
        (ProbabilityTheory.cond
          (μsp.prod (Measure.pi fun k => epistemicMeasure (vertexPoint k)))
          ((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)))
      ((fun y : PointerLudersArena N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j) := by
  have hmarg := pointer_luders_marginal c hc hδ μsp
    (fun k => epistemicMeasure (vertexPoint k)) i hpos
  have hmeas_proj : Measurable (fun y : PointerLudersArena N => y.1.1) :=
    measurable_fst.comp measurable_fst
  rw [← Measure.map_apply hmeas_proj (measurableSet_globalBasin c' j), hmarg]
  exact globalBasin_prob c' j (vertexPoint i)

omit [NeZero N] in
/-- ★★ **The composite on the witness's own preparation — B3b closes.** For the smooth
witness's ready-conditioned preparation `pointerPrep`, whenever the context gives outcome
`i` a rate above the `ε`-floor (`2ε < rate i`), the `ε`-Born lower bound makes the
conditioning non-vacuous, and follow-up statistics after outcome `i` are exactly the
collapsed state's Born weights. The smooth horn now delivers records (`ε`-Born,
`smoothWitnessClosure`/`pointer_born_frequency`) **and** a Lüders update, on one arena. -/
theorem pointer_luders_born_prep (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) (p : LF4.CPN N) (q₀ : Pointer N) (i : Fin N)
    (hi : 2 * ε < c.rate p i) (c' : ContextField N) (j : Fin N) :
    (Measure.map (pointerLudersStroke c ε)
        (ProbabilityTheory.cond
          ((pointerPrep p q₀ δ).prod
            (Measure.pi fun k => epistemicMeasure (vertexPoint k)))
          ((pointerProtocol c hc ε hδ).outcomeSector i ×ˢ Set.univ)))
      ((fun y : PointerLudersArena N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j) := by
  have := isProbabilityMeasure_pointerPrep p q₀ hδpos
  have hpos : pointerPrep p q₀ δ ((pointerProtocol c hc ε hδ).outcomeSector i) ≠ 0 := by
    intro h0
    have hlow := pointer_born_lower c hc hε hδpos hδ p q₀ i
    rw [h0] at hlow
    have hzero : ENNReal.ofReal (c.rate p i - 2 * ε) = 0 := le_zero_iff.mp hlow
    rw [ENNReal.ofReal_eq_zero] at hzero
    linarith
  exact pointer_luders_born c hc hδ (pointerPrep p q₀ δ) i hpos c' j

end CSD.RecordLayer
