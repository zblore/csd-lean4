/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.JoinArena
public import CsdLean4.SigmaLayer.SwapClosure

/-!
# SigmaLayer/JoinProtocol: the degenerate measurement as a `MeasurementProtocol`

**Category:** 7-SigmaLayer (dynamical measurement — degenerate Lüders, brick 4: the protocol
plumbing).

## What this is

`JoinArena.lean` proved the degenerate Lüders update is a Liouville-preserving unitary with a
pointwise-correct readout. This module runs that update inside the corpus's standard
measurement architecture — the same two-time-propagator, ready/pointer-region,
record-triggered shape as `SwapWitness`:

* the ontic space is `Xj × T²_R`: join point `ℙ(ℂ^{N+N})`, system fibre, **ancilla fibre**,
  pointer register;
* the selector is the coarse block index read off the join point's system ray and the system
  fibre (`joinIdx` — `b ∘ basinIndex ∘ (joinFst, fibre)`);
* the propagator `joinEvolve` shears the register (record creation, as always) and, at the
  readout crossing, fires the record-triggered `joinG`: apply the join unitary to the join
  point **and exchange the system fibre with the ancilla fibre**. The fibre exchange is the
  degenerate analogue of the rank-one witness's fresh slot: the post-measurement system fibre
  is the ancilla's (fresh), while the outcome-conditioned original fibre is **stored**, not
  destroyed.

Because the arena is literally a shear arena over `Xsel = Xj`, the whole record apparatus —
regions, readout, sectors, persistence — is inherited from `shearProtocol` by structure
update; only the propagator cluster is new.

## What is proved

* `joinG_joinG` — the record-triggered map is an involution (`joinSwap` is a permutation
  unitary squared to `1`; the fibre exchange is its own inverse; the register is untouched).
* `joinEvolve_comp` — the two-time law, the same eight readout-crossing cases as
  `swapEvolve_comp`.
* `joinProtocol` — the `MeasurementProtocol` instance.
* `join_correlates` / `join_pointerInvariant` — `CorrelatesOn` and `PointerInvariantOn`
  discharged from the constructed propagator, never assumed.
* ★ `joinEvolve_measurePreserving` — the **full propagator preserves the join-arena Liouville
  measure** `(μ_FS ⊗ vol ⊗ vol) ⊗ vol`, at every time pair: the shear part by the generic
  shear theorem, the crossing part by `joinSwap_measurePreserving` (FS unitary invariance) +
  the fibre-transposition shuffle, glued by the register-arc partition.

## ⚠️ What brick 5 (the last one) owes

The conditioned-marginal bookkeeping: the sector-conditioned post-measurement system readout
for the canonical phase-orbit preparation equals `epistemicMeasure [Πᵢψ]` — the
`BlockLudersObligation` instance, mirroring `SwapLuders`. The pointwise input is
`join_block_luders`; the plumbing is conditioning + pushforward (`specs/BACKLOG.md`).

## References

`SigmaLayer/JoinArena.lean` (`joinSwap`, `join_block_luders`, `joinFst`);
`SigmaLayer/SwapWitness.lean` (the transcribed architecture: `arcIndex`, the crossing
propagator, the partition argument); `SigmaLayer/ShearWitness.lean` (`shearEvolve` and the
generic record machinery, inherited); `SigmaLayer/DegenerateLuders.lean`
(`swap_not_blockLuders` — why the rank-one architecture could not host this);
`specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N K : ℕ}

/-! ### The join selector space -/

/-- The join selector space: join point, system fibre, ancilla fibre. -/
abbrev JoinSel (N : ℕ) := (LF4.CPN (N + N) × LF4.KTorus) × LF4.KTorus

/-- The coarse selector: block index of the join point's system ray at the system fibre. -/
noncomputable def joinIdx [NeZero N] (b : Fin N → Fin K) : JoinSel N → Fin K :=
  fun x => b (basinIndex (momentContext N) (joinFst x.1.1, x.1.2))

theorem measurable_joinIdx [NeZero N] (b : Fin N → Fin K) : Measurable (joinIdx b) :=
  (Measurable.of_discrete (f := b)).comp
    ((measurable_basinIndex (momentContext N)).comp
      (((measurable_joinFst).comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)))

/-! ### The record-triggered join map -/

/-- **The record-triggered join map `G`**: if the pointer displays outcome `i`, apply the join
unitary for block `i` and exchange the system fibre with the ancilla fibre; otherwise do
nothing. The register is untouched. -/
noncomputable def joinG (b : Fin N → Fin K) :
    JoinSel N × LF4.KTorus → JoinSel N × LF4.KTorus := fun x =>
  match arcIndex K x.2 with
  | none => x
  | some i => (((joinSwap b i x.1.1.1, x.1.2), x.1.1.2), x.2)

theorem joinG_register (b : Fin N → Fin K) (x : JoinSel N × LF4.KTorus) :
    (joinG b x).2 = x.2 := by
  unfold joinG
  rcases h : arcIndex K x.2 with _ | i <;> simp

theorem joinG_of_mem (b : Fin N → Fin K) {x : JoinSel N × LF4.KTorus} {i : Fin K}
    (h : x.2 ∈ pointerArc K i) :
    joinG b x = (((joinSwap b i x.1.1.1, x.1.2), x.1.1.2), x.2) := by
  unfold joinG
  rw [(arcIndex_eq_some_iff _ i).mpr h]

theorem joinG_of_none (b : Fin N → Fin K) {x : JoinSel N × LF4.KTorus}
    (h : ∀ i, x.2 ∉ pointerArc K i) :
    joinG b x = x := by
  unfold joinG
  rw [(arcIndex_eq_none_iff _).mpr h]

/-- The join matrix squares to the identity — the permutation is an involution. -/
lemma joinMat_mul_self (b : Fin N → Fin K) (i : Fin K) :
    joinMat b i * joinMat b i = 1 := by
  ext j k
  simp only [Matrix.mul_apply, joinMat, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply]
  rw [joinPerm_involutive b i j]
  exact if_congr eq_comm rfl rfl

/-- The join swap on rays is an involution. -/
theorem joinSwap_joinSwap (b : Fin N → Fin K) (i : Fin K) (p : LF4.CPN (N + N)) :
    joinSwap b i (joinSwap b i p) = p := by
  unfold joinSwap
  rw [smul_smul, show joinU b i * joinU b i = 1 from Subtype.ext (joinMat_mul_self b i),
    one_smul]

/-- **`G` is an involution** — the join unitary squares to the identity, the fibre exchange is
its own inverse, and the register (the trigger) is untouched. -/
theorem joinG_joinG (b : Fin N → Fin K) (x : JoinSel N × LF4.KTorus) :
    joinG b (joinG b x) = x := by
  rcases h : arcIndex K x.2 with _ | i
  · rw [joinG_of_none b ((arcIndex_eq_none_iff _).mp h),
      joinG_of_none b ((arcIndex_eq_none_iff _).mp h)]
  · have hi : x.2 ∈ pointerArc K i := (arcIndex_eq_some_iff _ i).mp h
    rw [joinG_of_mem b hi]
    have hreg : ((((joinSwap b i x.1.1.1, x.1.2), x.1.1.2), x.2)
        : JoinSel N × LF4.KTorus).2 ∈ pointerArc K i := hi
    rw [joinG_of_mem b hreg]
    simp [joinSwap_joinSwap]

/-! ### `G` preserves the join-arena Liouville measure -/

variable (p₀ : LF4.CPN (N + N))

/-- The join-selector Liouville measure: Fubini–Study on the join point, Haar on both
fibres. -/
noncomputable def joinSelMeasure (p₀ : LF4.CPN (N + N)) : Measure (JoinSel N) :=
  ((Matrix.UnitaryGroup.fubiniStudyMeasure p₀).prod (volume : Measure LF4.KTorus)).prod
    (volume : Measure LF4.KTorus)

instance : IsProbabilityMeasure (joinSelMeasure (N := N) p₀) := by
  unfold joinSelMeasure
  infer_instance

/-- The join-arena Liouville measure: selector ⊗ register Haar. -/
noncomputable def joinArenaMeasure (p₀ : LF4.CPN (N + N)) :
    Measure (JoinSel N × LF4.KTorus) :=
  (joinSelMeasure p₀).prod (volume : Measure LF4.KTorus)

/-- The join arena measure, as its defining product (interface lemma, §9.1). -/
lemma joinArenaMeasure_def (p₀ : LF4.CPN (N + N)) :
    joinArenaMeasure p₀ = (joinSelMeasure p₀).prod (volume : Measure LF4.KTorus) := rfl

instance : IsProbabilityMeasure (joinArenaMeasure (N := N) p₀) := by
  unfold joinArenaMeasure
  infer_instance

/-- The fired-branch map on the selector: join swap on the point, fibre exchange. -/
noncomputable def joinGm (b : Fin N → Fin K) (i : Fin K) : JoinSel N → JoinSel N :=
  fun y => ((joinSwap b i y.1.1, y.2), y.1.2)

lemma measurable_joinGm (b : Fin N → Fin K) (i : Fin K) : Measurable (joinGm b i) := by
  refine Measurable.prodMk (Measurable.prodMk ?_ measurable_snd)
    (measurable_snd.comp measurable_fst)
  exact (continuous_const_smul (joinU b i)).measurable.comp
    (measurable_fst.comp measurable_fst)

lemma measurePreserving_joinGm (b : Fin N → Fin K) (i : Fin K) :
    MeasurePreserving (joinGm b i) (joinSelMeasure p₀) (joinSelMeasure p₀) := by
  have h1 : MeasurePreserving
      (Prod.map (Prod.map (joinSwap b i) (id : LF4.KTorus → LF4.KTorus))
        (id : LF4.KTorus → LF4.KTorus))
      (joinSelMeasure p₀) (joinSelMeasure p₀) := by
    unfold joinSelMeasure
    exact ((joinSwap_measurePreserving b i p₀).prod
      (MeasurePreserving.id _)).prod (MeasurePreserving.id _)
  have h2 : MeasurePreserving
      (fun y : JoinSel N => ((y.1.1, y.2), y.1.2))
      (joinSelMeasure p₀) (joinSelMeasure p₀) := by
    unfold joinSelMeasure
    have hR := measurePreserving_prodAssoc
      (Matrix.UnitaryGroup.fubiniStudyMeasure p₀) (volume : Measure LF4.KTorus)
      (volume : Measure LF4.KTorus)
    have hmid := (MeasurePreserving.id (Matrix.UnitaryGroup.fubiniStudyMeasure p₀)).prod
      (Measure.measurePreserving_swap (μ := (volume : Measure LF4.KTorus))
        (ν := (volume : Measure LF4.KTorus)))
    have hRinv := (measurePreserving_prodAssoc
      (Matrix.UnitaryGroup.fubiniStudyMeasure p₀) (volume : Measure LF4.KTorus)
      (volume : Measure LF4.KTorus)).symm
      (MeasurableEquiv.prodAssoc (α := LF4.CPN (N + N)) (β := LF4.KTorus) (γ := LF4.KTorus))
    have htot := hRinv.comp (hmid.comp hR)
    have hfun : (fun y : JoinSel N => ((y.1.1, y.2), y.1.2))
        = (⇑(MeasurableEquiv.prodAssoc
              (α := LF4.CPN (N + N)) (β := LF4.KTorus) (γ := LF4.KTorus)).symm
          ∘ ((Prod.map id Prod.swap)
          ∘ ⇑(MeasurableEquiv.prodAssoc
              (α := LF4.CPN (N + N)) (β := LF4.KTorus) (γ := LF4.KTorus)))) := by
      funext y
      rfl
    rw [hfun]
    exact htot
  have hfun : joinGm b i
      = (fun y : JoinSel N => ((y.1.1, y.2), y.1.2))
        ∘ (Prod.map (Prod.map (joinSwap b i) id) id) := by
    funext y
    rfl
  rw [hfun]
  exact h2.comp h1

/-- The register-arc pieces of the join arena. -/
def joinArcPiece (K : ℕ) (o : Option (Fin K)) : Set (JoinSel N × LF4.KTorus) :=
  match o with
  | none => {x | ∀ i, x.2 ∉ pointerArc K i}
  | some i => {x | x.2 ∈ pointerArc K i}

theorem measurableSet_joinArcPiece (o : Option (Fin K)) :
    MeasurableSet (joinArcPiece (N := N) K o) := by
  rcases o with _ | i
  · have h : joinArcPiece (N := N) K none
        = (⋃ i, {x : JoinSel N × LF4.KTorus | x.2 ∈ pointerArc K i})ᶜ := by
      ext x
      simp [joinArcPiece]
    rw [h]
    exact (MeasurableSet.iUnion fun i =>
      measurable_snd (measurableSet_pointerArc i)).compl
  · exact measurable_snd (measurableSet_pointerArc i)

theorem joinArcPiece_disjoint :
    Pairwise (Function.onFun Disjoint (joinArcPiece (N := N) K)) := by
  intro o o' hoo
  rcases o with _ | i <;> rcases o' with _ | i'
  · exact absurd rfl hoo
  · exact Set.disjoint_left.mpr fun x hx hx' => hx i' hx'
  · exact Set.disjoint_left.mpr fun x hx hx' => hx' i hx
  · have hii : i ≠ i' := fun h => hoo (h ▸ rfl)
    exact Set.disjoint_left.mpr fun x hx hx' =>
      Set.disjoint_left.mp (pointerArc_pairwiseDisjoint hii) hx hx'

theorem joinArcPiece_cover : (⋃ o, joinArcPiece (N := N) K o) = univ := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases h : ∃ i, x.2 ∈ pointerArc K i
  · obtain ⟨i, hi⟩ := h
    exact ⟨some i, hi⟩
  · exact ⟨none, by simpa [joinArcPiece] using fun i hi => h ⟨i, hi⟩⟩

theorem joinG_agree (b : Fin N → Fin K) (o : Option (Fin K)) (x : JoinSel N × LF4.KTorus)
    (hx : x ∈ joinArcPiece (N := N) K o) :
    joinG b x = (match o with
      | none => id
      | some i => Prod.map (joinGm b i) id) x := by
  rcases o with _ | i
  · exact joinG_of_none b hx
  · rw [joinG_of_mem b hx]
    rfl

theorem measurable_joinG (b : Fin N → Fin K) :
    Measurable (joinG (N := N) (K := K) b) := by
  classical
  refine measurable_of_partition measurableSet_joinArcPiece joinArcPiece_cover
    (Tk := fun o => match o with
      | none => id
      | some i => Prod.map (joinGm b i) id)
    (fun o => ?_) (joinG_agree b)
  rcases o with _ | i
  · exact measurable_id
  · exact (measurable_joinGm b i).prodMap measurable_id

/-- **★ The record-triggered join map preserves the arena Liouville measure** — each register
arc's piece map preserves it, and each piece is invariant under its own map because the
trigger coordinate is untouched. -/
theorem measurePreserving_joinG (b : Fin N → Fin K) :
    MeasurePreserving (joinG (N := N) (K := K) b)
      (joinArenaMeasure p₀) (joinArenaMeasure p₀) := by
  classical
  refine measurePreserving_of_partition measurableSet_joinArcPiece joinArcPiece_disjoint
    joinArcPiece_cover (measurable_joinG b)
    (Tk := fun o => match o with
      | none => id
      | some i => Prod.map (joinGm b i) id)
    (fun o => ?_) (joinG_agree b) (fun o => ?_)
  · rcases o with _ | i
    · exact MeasurePreserving.id _
    · unfold joinArenaMeasure
      exact (measurePreserving_joinGm p₀ b i).prod (MeasurePreserving.id _)
  · rcases o with _ | i
    · rfl
    · ext x
      exact Iff.rfl

/-! ### The crossing propagator -/

section Propagator

variable [NeZero N] (b : Fin N → Fin K)

/-- **The join propagator**: shear the register; fire the record-triggered join map when the
window crosses readout, in either direction (`G` is an involution). -/
noncomputable def joinEvolve (s t : CSD.SigmaLayer.OnticTime) :
    JoinSel N × LF4.KTorus → JoinSel N × LF4.KTorus :=
  if s < 1 ∧ 1 ≤ t then joinG b ∘ shearEvolve (joinIdx b) s t
  else if t < 1 ∧ 1 ≤ s then shearEvolve (joinIdx b) s t ∘ joinG b
  else shearEvolve (joinIdx b) s t

theorem joinEvolve_fwd {s t : CSD.SigmaLayer.OnticTime} (hs : s < 1) (ht : 1 ≤ t) :
    joinEvolve (N := N) b s t = joinG b ∘ shearEvolve (joinIdx b) s t := if_pos ⟨hs, ht⟩

theorem joinEvolve_bwd {s t : CSD.SigmaLayer.OnticTime} (ht : t < 1) (hs : 1 ≤ s) :
    joinEvolve (N := N) b s t = shearEvolve (joinIdx b) s t ∘ joinG b := by
  rw [joinEvolve, if_neg (fun h => absurd hs (not_le.mpr h.1)), if_pos ⟨ht, hs⟩]

theorem joinEvolve_lo {s t : CSD.SigmaLayer.OnticTime} (hs : s < 1) (ht : t < 1) :
    joinEvolve (N := N) b s t = shearEvolve (joinIdx b) s t := by
  rw [joinEvolve, if_neg (fun h => absurd h.2 (not_le.mpr ht)),
    if_neg (fun h => absurd h.2 (not_le.mpr hs))]

theorem joinEvolve_hi {s t : CSD.SigmaLayer.OnticTime} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    joinEvolve (N := N) b s t = shearEvolve (joinIdx b) s t := by
  rw [joinEvolve, if_neg (fun h => absurd h.1 (not_lt.mpr hs)),
    if_neg (fun h => absurd h.1 (not_lt.mpr ht))]

/-- Pointwise shear composition. -/
lemma sE_comp (s t u : CSD.SigmaLayer.OnticTime) (x : JoinSel N × LF4.KTorus) :
    shearEvolve (joinIdx b) t u (shearEvolve (joinIdx b) s t x)
      = shearEvolve (joinIdx b) s u x :=
  congrFun (shearEvolve_comp' (joinIdx b) s t u) x

lemma sE_congr {s t t' : CSD.SigmaLayer.OnticTime} (h : elapsed t = elapsed t')
    (x : JoinSel N × LF4.KTorus) :
    shearEvolve (joinIdx b) s t x = shearEvolve (joinIdx b) s t' x := by
  simp only [shearEvolve, h]

lemma sE_congr_left {s s' t : CSD.SigmaLayer.OnticTime} (h : elapsed s = elapsed s')
    (x : JoinSel N × LF4.KTorus) :
    shearEvolve (joinIdx b) s t x = shearEvolve (joinIdx b) s' t x := by
  simp only [shearEvolve, h]

/-- **The two-time composition law** — the same eight readout-crossing cases as
`swapEvolve_comp`, closing on `G² = id` and the frozen shear. -/
theorem joinEvolve_comp (s t u : CSD.SigmaLayer.OnticTime) :
    joinEvolve (N := N) b t u ∘ joinEvolve b s t = joinEvolve b s u := by
  funext x
  simp only [Function.comp_apply]
  rcases lt_or_ge s 1 with hs | hs <;> rcases lt_or_ge t 1 with ht | ht <;>
    rcases lt_or_ge u 1 with hu | hu
  · rw [joinEvolve_lo b hs ht, joinEvolve_lo b ht hu, joinEvolve_lo b hs hu, sE_comp]
  · rw [joinEvolve_lo b hs ht, joinEvolve_fwd b ht hu, joinEvolve_fwd b hs hu]
    simp only [Function.comp_apply]
    rw [sE_comp]
  · rw [joinEvolve_fwd b hs ht, joinEvolve_bwd b hu ht, joinEvolve_lo b hs hu]
    simp only [Function.comp_apply]
    rw [joinG_joinG, sE_comp]
  · rw [joinEvolve_fwd b hs ht, joinEvolve_hi b ht hu, joinEvolve_fwd b hs hu]
    simp only [Function.comp_apply]
    have he : elapsed t = elapsed u := by
      rw [elapsed_of_one_le ht, elapsed_of_one_le hu]
    rw [shearEvolve_frozen (joinIdx b) ht hu]
    simp only [id_eq]
    exact congrArg (joinG b) (sE_congr b he x)
  · rw [joinEvolve_bwd b ht hs, joinEvolve_lo b ht hu, joinEvolve_bwd b hu hs]
    simp only [Function.comp_apply]
    rw [sE_comp]
  · rw [joinEvolve_bwd b ht hs, joinEvolve_fwd b ht hu, joinEvolve_hi b hs hu]
    simp only [Function.comp_apply]
    rw [sE_comp, shearEvolve_frozen (joinIdx b) hs hu]
    simp only [id_eq]
    rw [joinG_joinG]
  · rw [joinEvolve_hi b hs ht, joinEvolve_bwd b hu ht, joinEvolve_bwd b hu hs]
    simp only [Function.comp_apply]
    have he : elapsed t = elapsed s := by
      rw [elapsed_of_one_le ht, elapsed_of_one_le hs]
    rw [shearEvolve_frozen (joinIdx b) hs ht]
    simp only [id_eq]
    exact sE_congr_left b he (joinG b x)
  · rw [joinEvolve_hi b hs ht, joinEvolve_hi b ht hu, joinEvolve_hi b hs hu, sE_comp]

theorem measurable_joinEvolve (s t : CSD.SigmaLayer.OnticTime) :
    Measurable (joinEvolve (N := N) (K := K) b s t) := by
  unfold joinEvolve
  split_ifs with h1 h2
  · exact (measurable_joinG b).comp
      ((shearProtocol (joinIdx b) (measurable_joinIdx b)).measurable_evolve s t)
  · exact ((shearProtocol (joinIdx b) (measurable_joinIdx b)).measurable_evolve s t).comp
      (measurable_joinG b)
  · exact (shearProtocol (joinIdx b) (measurable_joinIdx b)).measurable_evolve s t

/-- **The degenerate-measurement protocol on the join arena.** All region and readout
structure is inherited from the shear protocol; only the propagator cluster is new. -/
noncomputable def joinProtocol : MeasurementProtocol (JoinSel N × LF4.KTorus) K :=
  { shearProtocol (joinIdx b) (measurable_joinIdx b) with
    evolve := joinEvolve b
    evolve_self := fun t => by
      rcases lt_or_ge t 1 with h | h
      · rw [joinEvolve_lo b h h]
        exact (shearProtocol (joinIdx b) (measurable_joinIdx b)).evolve_self t
      · rw [joinEvolve_hi b h h]
        exact (shearProtocol (joinIdx b) (measurable_joinIdx b)).evolve_self t
    evolve_comp := joinEvolve_comp b
    measurable_evolve := measurable_joinEvolve b }

/-- **`CorrelatesOn` discharged**: the register dynamics is the shear's, and `G` never moves
the register. -/
theorem join_correlates :
    (joinProtocol (N := N) b).CorrelatesOn (selReady (joinIdx b)) := by
  intro i x hx
  have hshear := shear_correlates (joinIdx b) (measurable_joinIdx b) i hx
  have hreg : (shearEvolve (joinIdx b) 0 1 x).2 ∈ pointerArc K i := hshear
  show (joinProtocol b).evolve 0 1 x ∈ (joinProtocol b).pointerRegion i
  show joinEvolve b 0 1 x ∈ Prod.snd ⁻¹' pointerArc K i
  rw [joinEvolve_fwd b one_pos le_rfl]
  simp only [Function.comp_apply, Set.mem_preimage]
  rw [joinG_register]
  exact hreg

/-- **`PointerInvariantOn` discharged**: right of readout the propagator is frozen. -/
theorem join_pointerInvariant :
    (joinProtocol (N := N) (K := K) b).PointerInvariantOn := by
  intro i s t hs hst _ x hx
  have hs1 : (1 : ℝ) ≤ s := hs
  have ht1 : (1 : ℝ) ≤ t := le_trans hs1 hst
  have hid : (joinProtocol b).evolve s t x = x := by
    show joinEvolve b s t x = x
    rw [joinEvolve_hi b hs1 ht1]
    exact congrFun (shearEvolve_frozen (joinIdx b) hs1 ht1) x
  rw [hid]
  exact hx

/-- **★ The full join propagator preserves the arena Liouville measure**, at every time
pair. -/
theorem joinEvolve_measurePreserving (s t : CSD.SigmaLayer.OnticTime) :
    MeasurePreserving (joinEvolve (N := N) b s t)
      (joinArenaMeasure p₀) (joinArenaMeasure p₀) := by
  have hshear : MeasurePreserving (shearEvolve (joinIdx b) s t)
      (joinArenaMeasure p₀) (joinArenaMeasure p₀) := by
    unfold joinArenaMeasure
    exact shear_measurePreserving (joinIdx b) (measurable_joinIdx b)
      (joinSelMeasure p₀) s t
  unfold joinEvolve
  split_ifs with h1 h2
  · exact (measurePreserving_joinG p₀ b).comp hshear
  · exact hshear.comp (measurePreserving_joinG p₀ b)
  · exact hshear

end Propagator

end CSD.RecordLayer
