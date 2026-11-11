/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedSplitCarrier
public import CsdLean4.RecordLayer.DiracPointerBasin

/-!
# Site cells: one outcome for a split carrier, and why it cannot be site-local

**Category:** 7-SigmaLayer (the record layer). BACKLOG #371 — the author's programme "From `Σ` to
physical spacetime", obligation UO-10; Remainder (a) of #370.
`RecordLayer/UnifiedSplitCarrier.lean` showed that two pointers driven by the occupancy of their
sites both display for a split carrier. This module is the conditional alternative, on `Σ_*`
with one fibre angle. If the outcome is read from the cell of the arena point, at most one site
is selected at every arena point, and some site with probability `1` under every preparation
law; and no family of readouts local to their sites can do that with the weights of the carrier.

**The site cells** (`siteCell`): the region of `Σ_* = ℂℙ × T²` where the fibre angle `θ₁` lies in
the arc that a rate field `c` gives, at the point's own base point, to one of the two basis
states of the site `j`. It is a union of two basins of `RecordLayer/GlobalBasin.lean`, and no
preparation appears in it.

* **At most one site, for every arena point and every carrier**: the cells of two different
  sites are disjoint (`siteCell_disjoint`). No measure and no hypothesis on `c` is used.
* **The weights, conditional on UA-6**: for a torus-generated rate field the probability of the
  cell of `j`, under the preparation law at the carrier `p`, is the occupancy of `j`
  (`epistemicMeasure_siteCell`), and some site is selected with probability `1`
  (`epistemicMeasure_iUnion_siteCell`).
* **The split carrier**: each of its two sites has probability `1/2`, and both together
  probability `0` (`epistemicMeasure_siteCell_splitRay`).

**No site-local readout does this.** Call a family of readout regions `S j p` of a fibre *local
to its site* if `S j p` depends on the carrier `p` only through the occupancy of `j`. On a chain
with three different sites, and for any probability law on the fibre that does not depend on the
carrier: no family that is local to its site has both one outcome almost surely
(`μ (S j p ∩ S k p) = 0`) and the weights of the carrier (`μ (S j p) = occupancy of j`)
(`not_siteLocal_of_one_outcome`). The proof uses the three carriers split over the three pairs
of sites. Locality gives each site one region at occupancy `1/2`. The three regions are pairwise
almost disjoint and each has probability `1/2`, which is `3/2` in a space of probability `1`
(`measure_add_add_le_one`). So the site cells are not all local to their sites
(`siteCell_not_siteLocal`): for at least one site the fibre region of its cell is not a function
of that site's occupancy alone. For the cells as ordered here the regions of the first and the
last site are such functions, and a site in between has its arc placed by the occupancies before
it in the order of the index (a calculation, not in Lean).

## Exact scope

* **Kinematic.** A site cell is a region of the arena. No flow of this corpus writes it, no
  pointer displays it, and no `IsRecordWrite` is built. What is proved is what such a selection
  would have to be, not that a dynamics produces it.
* **The weights are assumed.** `epistemicMeasure_siteCell` is conditional on `IsTorusGenerated c`
  (UA-6, Posit 1): the weights are in the rate field. The disjointness is not conditional.
* **What "local" means here.** The readout region of `j` is a function of the occupancy of `j`
  and of the fibre point. The fibre point is shared by all sites; it is at no site. In this
  reading the torus is not a detector's pointer, and the coupling of UA-5 is not used. The law of
  the fibre does not depend on the carrier (UA-2: the preparation law is `δ_p ⊗ Haar`). A model in
  which the hidden variable is a position whose law is the carrier's weights is outside this
  hypothesis: it is local and gives one outcome. The theorem is about `Σ_*`, where the ontic
  state is the ray and a fibre point.
* **Exact equality** of regions is asked in the definition of locality, not equality up to null
  sets. The regions are null-measurable, and the exclusion and the weights are assumed for all
  carriers; the proof uses three.
* **Three sites are needed.** With two sites the theorem says nothing.
* **Not vacuous.** The moment-map field is torus-generated (`isTorusGenerated_momentContext`),
  so the hypothesis of `siteCell_not_siteLocal` holds for it on any chain with three sites.
* **One carrier, no settings.** This is not Bell's theorem. It is the exclusion of two clicks for
  one carrier.
* **The order of the arcs** in a cell is the order of the index, a convention. The theorem says
  that some dependence on the carrier beyond the site's own occupancy is unavoidable; it does not
  say which. A dependence on other data of the same site is not excluded by the statement.
* **Definite facts.** Which cell holds the arena point is a fact of the point. The measures are
  the preparation law over the unknown fibre point.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-2,
UA-6, UO-10, UD-21, UD-99, UD-100, UD-101, UD-102); `RecordLayer/GlobalBasin.lean`
(`globalBasin`, `globalBasin_pairwiseDisjoint`, `globalBasin_prob`, `globalBasin_ae_total`,
`epistemicMeasure`); `RecordLayer/CellLawForced.lean` (`IsTorusGenerated`,
`isTorusGenerated_momentContext`); `RecordLayer/DiracPointerBasin.lean`
(`rate_diracArenaEquiv_of_isTorusGenerated`); `RecordLayer/DiracPointerHamiltonian.lean`
(`diracIdx`, `diracArenaEquiv`, `arenaObs_siteProj`); `RecordLayer/UnifiedSplitCarrier.lean`
(`splitRay`, `arenaObs_siteProj_splitRay_fst`, `arenaObs_siteProj_splitRay_snd`,
`diracTwoPointerFlow_double_display`); `RecordLayer/SelectionOrder.lean` (the selection of two
wings).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization MeasureTheory Set
open scoped ENNReal

namespace CSD.RecordLayer

/-! ### Three almost disjoint events -/

/-- ★ **Three pairwise almost disjoint events have total probability at most `1`.** -/
theorem measure_add_add_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A B C : Set Ω} (hB : NullMeasurableSet B μ)
    (hC : NullMeasurableSet C μ) (hAB : μ (A ∩ B) = 0) (hAC : μ (A ∩ C) = 0)
    (hBC : μ (B ∩ C) = 0) : μ A + μ B + μ C ≤ 1 := by
  have dAB : AEDisjoint μ A B := hAB
  have dAC : AEDisjoint μ A C := hAC
  have dBC : AEDisjoint μ B C := hBC
  rw [← measure_union₀ hB dAB, ← measure_union₀ hC (dAC.union_left dBC)]
  exact prob_le_one

/-! ### The site cells -/

section Cells

variable {M : ℕ}

/-- **The cell of the site `j`** cut by the rate field `c`: the arena points whose fibre angle
lies in the arc of one of the two basis states of `j`. -/
noncomputable def siteCell (c : ContextField (2 * M + 1 + 1)) (j : ZMod (M + 1)) :
    Set (KSigma (2 * M + 1 + 1)) :=
  globalBasin c (diracIdx M (j, 0)) ∪ globalBasin c (diracIdx M (j, 1))

/-- A site cell is measurable. -/
theorem measurableSet_siteCell (c : ContextField (2 * M + 1 + 1)) (j : ZMod (M + 1)) :
    MeasurableSet (siteCell c j) :=
  (measurableSet_globalBasin c _).union (measurableSet_globalBasin c _)

/-- ★★★ **At most one site is selected, for every arena point and every carrier.** The cells of
two different sites are disjoint. -/
theorem siteCell_disjoint (c : ContextField (2 * M + 1 + 1)) {j k : ZMod (M + 1)}
    (hjk : j ≠ k) : Disjoint (siteCell c j) (siteCell c k) := by
  have hne : ∀ s s' : Fin 2, diracIdx M (j, s) ≠ diracIdx M (k, s') := fun s s' e =>
    hjk (congrArg Prod.fst ((diracIdx M).injective e))
  simp only [siteCell, Set.disjoint_union_left, Set.disjoint_union_right]
  exact ⟨⟨globalBasin_pairwiseDisjoint c (hne 0 0), globalBasin_pairwiseDisjoint c (hne 1 0)⟩,
    ⟨globalBasin_pairwiseDisjoint c (hne 0 1), globalBasin_pairwiseDisjoint c (hne 1 1)⟩⟩

/-- Every basin lies in a site cell. -/
theorem globalBasin_subset_iUnion_siteCell (c : ContextField (2 * M + 1 + 1))
    (i : Fin (2 * M + 1 + 1)) : globalBasin c i ⊆ ⋃ j : ZMod (M + 1), siteCell c j := by
  obtain ⟨⟨j, s⟩, rfl⟩ := (diracIdx M).surjective i
  refine fun x hx => Set.mem_iUnion.2 ⟨j, ?_⟩
  fin_cases s
  · exact Or.inl hx
  · exact Or.inr hx

/-- ★★ **The probability of a site cell is the occupancy of the site**, under the preparation
law at the carrier `p`. Conditional on the rate field being torus-generated (UA-6): the weights
are in `c`. -/
theorem epistemicMeasure_siteCell {c : ContextField (2 * M + 1 + 1)} (h : IsTorusGenerated c)
    (j : ZMod (M + 1)) (p : GenArena (ZMod (M + 1) × Fin 2)) :
    epistemicMeasure (diracArenaEquiv M p) (siteCell c j)
      = ENNReal.ofReal (arenaObs (siteProj j) p) := by
  have hne : diracIdx M (j, 0) ≠ diracIdx M (j, 1) := fun e => by
    simpa using (diracIdx M).injective e
  rw [siteCell, measure_union (globalBasin_pairwiseDisjoint c hne) (measurableSet_globalBasin c _),
    globalBasin_prob, globalBasin_prob, rate_diracArenaEquiv_of_isTorusGenerated h,
    rate_diracArenaEquiv_of_isTorusGenerated h, arenaObs_siteProj,
    ENNReal.ofReal_add (momentMap_nonneg _ _) (momentMap_nonneg _ _)]

/-- ★ **Some site is selected with probability `1`.** -/
theorem epistemicMeasure_iUnion_siteCell (c : ContextField (2 * M + 1 + 1))
    (p : CPN (2 * M + 1 + 1)) :
    epistemicMeasure p (⋃ j : ZMod (M + 1), siteCell c j) = 1 := by
  refine le_antisymm prob_le_one ?_
  have hsub : ⋃ i, globalBasin c i ⊆ ⋃ j : ZMod (M + 1), siteCell c j :=
    Set.iUnion_subset (globalBasin_subset_iUnion_siteCell c)
  have h0 := globalBasin_ae_total c p
  have h1 : epistemicMeasure p (⋃ i, globalBasin c i) = 1 := by
    have hc : (⋃ i, globalBasin c i)ᶜ = univ \ ⋃ i, globalBasin c i := by
      rw [Set.compl_eq_univ_sdiff]
    have := prob_compl_eq_zero_iff
      (MeasurableSet.iUnion (measurableSet_globalBasin c)) (μ := epistemicMeasure p)
    exact this.1 (by rw [hc]; exact h0)
  calc (1 : ℝ≥0∞) = epistemicMeasure p (⋃ i, globalBasin c i) := h1.symm
    _ ≤ _ := measure_mono hsub

/-- ★★★ **One outcome for the split carrier.** For a torus-generated rate field and the equal
superposition over two sites: each site's cell has probability `1/2`, and the two cells share
no arena point. -/
theorem epistemicMeasure_siteCell_splitRay {c : ContextField (2 * M + 1 + 1)}
    (h : IsTorusGenerated c) {j k : ZMod (M + 1)} (hjk : j ≠ k) :
    epistemicMeasure (diracArenaEquiv M (splitRay hjk)) (siteCell c j) = ENNReal.ofReal (1 / 2)
      ∧ epistemicMeasure (diracArenaEquiv M (splitRay hjk)) (siteCell c k)
        = ENNReal.ofReal (1 / 2)
      ∧ siteCell c j ∩ siteCell c k = ∅ := by
  refine ⟨?_, ?_, (siteCell_disjoint c hjk).inter_eq⟩
  · rw [epistemicMeasure_siteCell h, arenaObs_siteProj_splitRay_fst]
  · rw [epistemicMeasure_siteCell h, arenaObs_siteProj_splitRay_snd]

end Cells

/-! ### No site-local readout has one outcome with the weights -/

section NoGo

variable {M : ℕ}

/-- ★★★ **No readout that is local to its site has one outcome with the weights of the
carrier.** On a chain with three different sites, for a probability law `μ` on a fibre and
readout regions `S j p`: if two different sites are almost never both selected, and each site is
selected with probability its occupancy, then `S j p` is not a function of the occupancy of `j`
alone. -/
theorem not_siteLocal_of_one_outcome {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : ZMod (M + 1) → GenArena (ZMod (M + 1) × Fin 2) → Set Ω)
    {a b d : ZMod (M + 1)} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hmeas : ∀ j p, NullMeasurableSet (S j p) μ)
    (hexcl : ∀ j k p, j ≠ k → μ (S j p ∩ S k p) = 0)
    (hweight : ∀ j p, μ (S j p) = ENNReal.ofReal (arenaObs (siteProj j) p)) :
    ¬ ∃ r : ZMod (M + 1) → ℝ → Set Ω, ∀ j p, S j p = r j (arenaObs (siteProj j) p) := by
  rintro ⟨r, hr⟩
  -- each site's region at occupancy `1/2`, read off two split carriers
  have ea₁ : S a (splitRay hab) = r a (1 / 2) := by rw [hr, arenaObs_siteProj_splitRay_fst]
  have ea₂ : S a (splitRay had) = r a (1 / 2) := by rw [hr, arenaObs_siteProj_splitRay_fst]
  have eb₁ : S b (splitRay hab) = r b (1 / 2) := by rw [hr, arenaObs_siteProj_splitRay_snd]
  have eb₂ : S b (splitRay hbd) = r b (1 / 2) := by rw [hr, arenaObs_siteProj_splitRay_fst]
  have ed₁ : S d (splitRay had) = r d (1 / 2) := by rw [hr, arenaObs_siteProj_splitRay_snd]
  have ed₂ : S d (splitRay hbd) = r d (1 / 2) := by rw [hr, arenaObs_siteProj_splitRay_snd]
  have hAB : μ (r a (1 / 2) ∩ r b (1 / 2)) = 0 := by
    rw [← ea₁, ← eb₁]
    exact hexcl a b _ hab
  have hAD : μ (r a (1 / 2) ∩ r d (1 / 2)) = 0 := by
    rw [← ea₂, ← ed₁]
    exact hexcl a d _ had
  have hBD : μ (r b (1 / 2) ∩ r d (1 / 2)) = 0 := by
    rw [← eb₂, ← ed₂]
    exact hexcl b d _ hbd
  have mA : μ (r a (1 / 2)) = ENNReal.ofReal (1 / 2) := by
    rw [← ea₁, hweight, arenaObs_siteProj_splitRay_fst]
  have mB : μ (r b (1 / 2)) = ENNReal.ofReal (1 / 2) := by
    rw [← eb₁, hweight, arenaObs_siteProj_splitRay_snd]
  have mD : μ (r d (1 / 2)) = ENNReal.ofReal (1 / 2) := by
    rw [← ed₁, hweight, arenaObs_siteProj_splitRay_snd]
  have nB : NullMeasurableSet (r b (1 / 2)) μ := eb₁ ▸ hmeas b _
  have nD : NullMeasurableSet (r d (1 / 2)) μ := ed₁ ▸ hmeas d _
  have hsum := measure_add_add_le_one μ nB nD hAB hAD hBD
  rw [mA, mB, mD, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.ofReal_le_one] at hsum
  norm_num at hsum

/-- ★★★ **The site cells are not all local to their sites.** For a torus-generated rate field
on a chain with three different sites there is no family `r` such that, for every site `j` and
carrier `p`, the fibre points at which the cell of `j` holds `p` are `r j` at the occupancy of
`j`. So for at least one site the region is not a function of its own occupancy alone. -/
theorem siteCell_not_siteLocal {c : ContextField (2 * M + 1 + 1)} (h : IsTorusGenerated c)
    {a b d : ZMod (M + 1)} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ¬ ∃ r : ZMod (M + 1) → ℝ → Set KTorus, ∀ j p,
      Prod.mk (diracArenaEquiv M p) ⁻¹' siteCell c j = r j (arenaObs (siteProj j) p) := by
  have hpre : ∀ (j : ZMod (M + 1)) (p : GenArena (ZMod (M + 1) × Fin 2)) (E : Set _),
      MeasurableSet E → epistemicMeasure (diracArenaEquiv M p) E
        = volume (Prod.mk (diracArenaEquiv M p) ⁻¹' E) := fun j p E hE => by
    rw [epistemicMeasure, Measure.prod_apply hE,
      lintegral_dirac' _ (measurable_measure_prodMk_left hE)]
  refine not_siteLocal_of_one_outcome (volume : Measure KTorus)
    (fun j p => Prod.mk (diracArenaEquiv M p) ⁻¹' siteCell c j) hab had hbd
    (fun j p => ((measurableSet_siteCell c j).preimage measurable_prodMk_left).nullMeasurableSet)
    (fun j k p hjk => ?_) (fun j p => ?_)
  · rw [← Set.preimage_inter, (siteCell_disjoint c hjk).inter_eq, Set.preimage_empty,
      measure_empty]
  · rw [← hpre j p _ (measurableSet_siteCell c j), epistemicMeasure_siteCell h]

end NoGo

end CSD.RecordLayer

end
