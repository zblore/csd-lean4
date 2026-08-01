/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.DynamicBorn
public import CsdLean4.Mathlib.MeasureTheory.PiecewisePreserving

/-!
# SigmaLayer/SwapWitness: the calibrated-swap witness — collapse as relocation

**Category:** 7-SigmaLayer (the record layer — the second dynamical witness).

## Why a second witness

`shear_base_marginal_unchanged` proved the shear cannot implement the Lüders update: the property
that makes its correlation proof work — no back-reaction on the selector — is exactly the property
that prevents collapse. And the collapse no-gos (`MeasurementConstraints.lean`) show the repair
cannot be a contraction: `no_exact_collapse` kills any measure-preserving map sending a
positive-measure set of states onto the (null) basis vertices, and `collapse_accuracy_bound` prices
approximate contraction in ready-state improbability. **The only shape left is relocation**: a
globally measure-preserving bijection that permutes *null slices*, moving the epistemic Dirac from
`[ψ]` to `[eᵢ]` without shrinking anything.

## The construction

Enlarge the arena with an **ancilla bank**: `K` reference cells inside the apparatus, one per
outcome, each a full copy of the selector space —

  `SwapArena Xsel K = (Xsel × T²_R) × (Fin K → Xsel)`.

The propagator is `swapG ∘ (lifted shear)`: run the shear, then — **triggered by the record, not by
the selector** — exchange the system's selector coordinate with bank slot `j` when the pointer sits
in arc `j`.

★ **The record-trigger is forced, not stylistic.** The pieces `{register ∈ arc j}` are invariant
under the slot-`j` swap because the swap never touches the register — which is what makes `swapG` a
piecewise map with invariant pieces, hence measure-preserving
(`measurePreserving_of_partition`). Conditioning on the *selector* index instead would move the very
coordinate the pieces are defined by, and the bookkeeping fails. The physically right causal story
("the written pointer back-acts on the system") coincides with the only version whose measure theory
works.

★ **The crossing propagator is symmetric, correcting the design as reviewed.** The proposal defined
the swap to fire on forward crossings of the readout time only; the two-time composition law
`Φ_{t→u} ∘ Φ_{s→t} = Φ_{s→u}` is quantified over *all* time triples, and a forward-only flag fails
it on non-monotone triples (go past readout, come back: the swap is applied and never undone).
Because `swapG` is an **involution**, the repair is to fire it on crossings in *either* direction —
`G ∘ shear` forward, `shear ∘ G` backward — and all eight side-of-readout cases then close, using
`G² = id` and the shear being frozen right of readout.

## What is proved

* `swapG` — the record-triggered bank swap; involutive, measurable, **measure-preserving**.
* `swapProtocol` — a genuine `MeasurementProtocol` on the enlarged arena.
* `swapEvolve_measurePreserving` — the full propagator preserves the Liouville measure at every
  time pair. It is a *dynamics*.
* `swap_correlates` — `CorrelatesOn` discharged: the correlation is inherited from the shear, since
  the swap never moves the register.
* `swap_pointerInvariant` — `PointerInvariantOn` discharged: after readout the propagator is the
  identity.
* `swapG_register`, `swapEvolve_cross_fwd`, … — the algebra the Lüders module consumes.

## ⚠️ Scope

* **The Lüders theorem is NOT in this file** — see `SwapLuders.lean` for the post-measurement
  marginal. This file supplies the witness and its protocol properties.
* **The Hamiltonian generation is stated, not formalised**, exactly as for the shear: the swap stage
  is the ontic analogue of a controlled kick applied at the readout time, but Mathlib has no
  manifold Hamiltonian-flow API, so no claim is made that this propagator arises from an `H_int`.
* The bank is *consumed*: one measurement uses one calibration of the slots. Resetting a slot is
  erasure, with the Landauer cost `collapse_accuracy_bound` prices; the reset is deliberately
  outside the protocol.

## References

`SigmaLayer/ShearWitness.lean` (the shear this composes with);
`SigmaLayer/MeasurementConstraints.lean` (`no_exact_collapse`, `collapse_accuracy_bound` — why
relocation is the only shape); `Mathlib/MeasureTheory/PiecewisePreserving.lean` (`swapSlot`,
`measurePreserving_of_partition`); `SigmaLayer/MeasurementProtocol.lean`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {Xsel : Type*} [MeasurableSpace Xsel] {K : ℕ}

/-! ### The arena -/

/-- The swap arena: selector × register, together with the ancilla bank — one reference cell per
outcome, each a full copy of the selector space. -/
abbrev SwapArena (Xsel : Type*) (K : ℕ) := (Xsel × LF4.KTorus) × (Fin K → Xsel)

/-! ### Classifying the register -/

theorem pointerArc_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint (pointerArc K)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun r hri hrj => ?_
  simp only [pointerArc, Set.mem_setOf_eq, Set.mem_Ioc] at hri hrj
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
  · exact absurd (lt_of_le_of_lt hri.2 (shearAmt_strictMono h)) (not_lt.mpr hrj.1.le)
  · exact absurd (lt_of_le_of_lt hrj.2 (shearAmt_strictMono h)) (not_lt.mpr hri.1.le)

/-- Which pointer arc the register occupies, if any. -/
noncomputable def arcIndex (K : ℕ) (r : LF4.KTorus) : Option (Fin K) :=
  open Classical in
  if h : ∃ j, r ∈ pointerArc K j then some h.choose else none

theorem arcIndex_eq_some_iff (r : LF4.KTorus) (j : Fin K) :
    arcIndex K r = some j ↔ r ∈ pointerArc K j := by
  classical
  constructor
  · intro h
    unfold arcIndex at h
    split at h
    · next hex =>
      have := hex.choose_spec
      rw [Option.some_inj] at h
      exact h ▸ this
    · exact absurd h (by simp)
  · intro hr
    unfold arcIndex
    split
    · next hex =>
      have hchoose := hex.choose_spec
      by_cases hjj : hex.choose = j
      · rw [hjj]
      · exact absurd (Set.disjoint_left.mp (pointerArc_pairwiseDisjoint hjj) hchoose)
          (by simpa using hr)
    · next hne => exact absurd ⟨j, hr⟩ hne

theorem arcIndex_eq_none_iff (r : LF4.KTorus) :
    arcIndex K r = none ↔ ∀ j, r ∉ pointerArc K j := by
  classical
  constructor
  · intro h j hj
    unfold arcIndex at h
    rw [dif_pos ⟨j, hj⟩] at h
    simp at h
  · intro h
    unfold arcIndex
    rw [dif_neg (not_exists.mpr h)]

/-! ### The record-triggered bank swap -/

/-- The slot-`j` swap on the arena: exchange the system's selector coordinate with bank slot `j`.
The register is untouched. -/
def bankSwap (j : Fin K) (x : SwapArena Xsel K) : SwapArena Xsel K :=
  ((x.2 j, x.1.2), Function.update x.2 j x.1.1)

/-- **The record-triggered swap `G`**: if the pointer displays outcome `j`, exchange the system with
bank slot `j`; otherwise do nothing. ★ Triggered by the *record* — the register arc — not by the
selector index; see the module docstring for why the measure theory forces this. -/
noncomputable def swapG : SwapArena Xsel K → SwapArena Xsel K := fun x =>
  match arcIndex K x.1.2 with
  | none => x
  | some j => bankSwap j x

/-- The swap never moves the register. -/
theorem swapG_register (x : SwapArena Xsel K) : (swapG x).1.2 = x.1.2 := by
  unfold swapG
  rcases h : arcIndex K x.1.2 with _ | j <;> simp [bankSwap]

theorem swapG_of_mem {x : SwapArena Xsel K} {j : Fin K} (h : x.1.2 ∈ pointerArc K j) :
    swapG x = bankSwap j x := by
  unfold swapG
  rw [(arcIndex_eq_some_iff _ j).mpr h]

theorem swapG_of_none {x : SwapArena Xsel K} (h : ∀ j, x.1.2 ∉ pointerArc K j) :
    swapG x = x := by
  unfold swapG
  rw [(arcIndex_eq_none_iff _).mpr h]

/-- **`G` is an involution** — which is what lets the crossing propagator fire it symmetrically in
both time directions and still satisfy the two-time composition law. -/
theorem swapG_swapG (x : SwapArena Xsel K) : swapG (swapG x) = x := by
  classical
  rcases h : arcIndex K x.1.2 with _ | j
  · rw [swapG_of_none ((arcIndex_eq_none_iff _).mp h),
      swapG_of_none ((arcIndex_eq_none_iff _).mp h)]
  · have hj : x.1.2 ∈ pointerArc K j := (arcIndex_eq_some_iff _ j).mp h
    rw [swapG_of_mem hj]
    have hreg : (bankSwap j x).1.2 ∈ pointerArc K j := hj
    rw [swapG_of_mem hreg]
    simp [bankSwap, Function.update_eq_self]

/-! ### `G` preserves the measure -/

variable (μs : Measure Xsel) [IsProbabilityMeasure μs]

/-- The Liouville measure of the swap arena: selector ⊗ register-Haar ⊗ bank. -/
noncomputable def swapMeasure (μs : Measure Xsel) (K : ℕ) : Measure (SwapArena Xsel K) :=
  (μs.prod (volume : Measure LF4.KTorus)).prod (Measure.pi fun _ : Fin K => μs)

instance : IsProbabilityMeasure (swapMeasure μs K) := by
  unfold swapMeasure; infer_instance

/-- **The slot swap preserves the arena measure** — by conjugating `swapSlot` through the shuffle
that brings the register out front. -/
theorem measurePreserving_bankSwap (j : Fin K) :
    MeasurePreserving (bankSwap (Xsel := Xsel) j) (swapMeasure μs K) (swapMeasure μs K) := by
  unfold swapMeasure
  have hR := (measurePreserving_prodAssoc (volume : Measure LF4.KTorus) μs
      (Measure.pi fun _ : Fin K => μs)).comp
    ((Measure.measurePreserving_swap (μ := μs) (ν := (volume : Measure LF4.KTorus))).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin K => μs)))
  have hmid := (MeasurePreserving.id (volume : Measure LF4.KTorus)).prod
    (measurePreserving_swapSlot μs j)
  have hRinv := ((Measure.measurePreserving_swap
      (μ := (volume : Measure LF4.KTorus)) (ν := μs)).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin K => μs))).comp
    ((measurePreserving_prodAssoc (volume : Measure LF4.KTorus) μs
      (Measure.pi fun _ : Fin K => μs)).symm
      (MeasurableEquiv.prodAssoc (α := LF4.KTorus) (β := Xsel) (γ := (Fin K → Xsel))))
  have htot := hRinv.comp (hmid.comp hR)
  have hfun : bankSwap (Xsel := Xsel) j
      = ((Prod.map Prod.swap id ∘ ⇑(MeasurableEquiv.prodAssoc
            (α := LF4.KTorus) (β := Xsel) (γ := (Fin K → Xsel))).symm)
        ∘ ((Prod.map id (swapSlot (α := Xsel) (ι := Fin K) j))
        ∘ (⇑(MeasurableEquiv.prodAssoc
            (α := LF4.KTorus) (β := Xsel) (γ := (Fin K → Xsel)))
          ∘ Prod.map Prod.swap id))) := by
    funext x
    rfl
  rw [hfun]
  exact htot

theorem measurable_bankSwap (j : Fin K) : Measurable (bankSwap (Xsel := Xsel) j) := by
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · exact (measurable_pi_apply j).comp measurable_snd
  · exact measurable_snd.comp measurable_fst
  · exact measurable_update'.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))

/-- The pieces of the swap: which arc the register occupies (or none). -/
def arcPiece (K : ℕ) (o : Option (Fin K)) : Set (SwapArena Xsel K) :=
  match o with
  | none => {x | ∀ j, x.1.2 ∉ pointerArc K j}
  | some j => {x | x.1.2 ∈ pointerArc K j}

theorem measurableSet_arcPiece (o : Option (Fin K)) :
    MeasurableSet (arcPiece (Xsel := Xsel) K o) := by
  have hreg : Measurable fun x : SwapArena Xsel K => x.1.2 :=
    measurable_snd.comp measurable_fst
  rcases o with _ | j
  · have : arcPiece (Xsel := Xsel) K none
        = (⋃ j, {x : SwapArena Xsel K | x.1.2 ∈ pointerArc K j})ᶜ := by
      ext x; simp [arcPiece]
    rw [this]
    exact (MeasurableSet.iUnion fun j => hreg (measurableSet_pointerArc j)).compl
  · exact hreg (measurableSet_pointerArc j)

theorem arcPiece_disjoint :
    Pairwise (Function.onFun Disjoint (arcPiece (Xsel := Xsel) K)) := by
  intro o o' hoo
  rcases o with _ | j <;> rcases o' with _ | j'
  · exact absurd rfl hoo
  · exact Set.disjoint_left.mpr fun x hx hx' => hx j' hx'
  · exact Set.disjoint_left.mpr fun x hx hx' => hx' j hx
  · have hjj : j ≠ j' := fun h => hoo (h ▸ rfl)
    exact Set.disjoint_left.mpr fun x hx hx' =>
      Set.disjoint_left.mp (pointerArc_pairwiseDisjoint hjj) hx hx'

theorem arcPiece_cover : (⋃ o, arcPiece (Xsel := Xsel) K o) = univ := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases h : ∃ j, x.1.2 ∈ pointerArc K j
  · obtain ⟨j, hj⟩ := h
    exact ⟨some j, hj⟩
  · exact ⟨none, by simpa [arcPiece] using fun j hj => h ⟨j, hj⟩⟩

theorem swapG_agree (o : Option (Fin K)) (x : SwapArena Xsel K)
    (hx : x ∈ arcPiece (Xsel := Xsel) K o) :
    swapG x = (match o with | none => id | some j => bankSwap j) x := by
  rcases o with _ | j
  · exact swapG_of_none hx
  · exact swapG_of_mem hx

theorem measurable_swapG : Measurable (swapG (Xsel := Xsel) (K := K)) := by
  classical
  refine measurable_of_partition measurableSet_arcPiece arcPiece_cover
    (Tk := fun o => match o with | none => id | some j => bankSwap j)
    (fun o => ?_) swapG_agree
  rcases o with _ | j
  · exact measurable_id
  · exact measurable_bankSwap j

/-- **★ The record-triggered swap preserves the Liouville measure.** Each piece's map preserves the
measure, and each piece is invariant under its own map — because the swap never moves the register,
which is the coordinate the pieces are defined by. This is where the record-trigger design choice
pays. -/
theorem measurePreserving_swapG :
    MeasurePreserving (swapG (Xsel := Xsel) (K := K)) (swapMeasure μs K) (swapMeasure μs K) := by
  classical
  refine measurePreserving_of_partition measurableSet_arcPiece arcPiece_disjoint arcPiece_cover
    measurable_swapG
    (Tk := fun o => match o with | none => id | some j => bankSwap j)
    (fun o => ?_) swapG_agree (fun o => ?_)
  · rcases o with _ | j
    · exact MeasurePreserving.id _
    · exact measurePreserving_bankSwap μs j
  · rcases o with _ | j
    · rfl
    · ext x
      exact Iff.rfl

/-! ### The crossing propagator -/

/-- The shear, lifted to the arena: it acts on selector × register and leaves the bank alone. -/
noncomputable def liftShear (idx : Xsel → Fin K) (s t : OnticTime) :
    SwapArena Xsel K → SwapArena Xsel K :=
  Prod.map (shearEvolve idx s t) id

theorem liftShear_comp (idx : Xsel → Fin K) (s t u : OnticTime) (x : SwapArena Xsel K) :
    liftShear idx t u (liftShear idx s t x) = liftShear idx s u x := by
  unfold liftShear
  have h := congrFun (shearEvolve_comp' idx s t u) x.1
  simp only [Prod.map, id_eq]
  simp only [Function.comp_apply] at h
  rw [h]

theorem liftShear_frozen (idx : Xsel → Fin K) {s t : OnticTime} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (x : SwapArena Xsel K) : liftShear idx s t x = x := by
  unfold liftShear
  simp only [Prod.map, id_eq]
  rw [shearEvolve_frozen idx hs ht]
  rfl

theorem liftShear_congr (idx : Xsel → Fin K) {s t t' : OnticTime}
    (h : elapsed t = elapsed t') (x : SwapArena Xsel K) :
    liftShear idx s t x = liftShear idx s t' x := by
  unfold liftShear
  simp only [Prod.map, id_eq, shearEvolve, h]

theorem liftShear_congr_left (idx : Xsel → Fin K) {s s' t : OnticTime}
    (h : elapsed s = elapsed s') (x : SwapArena Xsel K) :
    liftShear idx s t x = liftShear idx s' t x := by
  unfold liftShear
  simp only [Prod.map, id_eq, shearEvolve, h]

/-- **The swap propagator**: run the shear; fire the record-triggered swap `G` when the time window
crosses the readout time `1` — in **either** direction, `G` being an involution.

★ The symmetric firing is a correction to the reviewed design, which fired forward only: the
two-time law `Φ_{t→u} ∘ Φ_{s→t} = Φ_{s→u}` is quantified over all triples, and a forward-only flag
fails on go-past-and-come-back paths. -/
noncomputable def swapEvolve (idx : Xsel → Fin K) (s t : OnticTime) :
    SwapArena Xsel K → SwapArena Xsel K :=
  if s < 1 ∧ 1 ≤ t then swapG ∘ liftShear idx s t
  else if t < 1 ∧ 1 ≤ s then liftShear idx s t ∘ swapG
  else liftShear idx s t

theorem swapEvolve_fwd (idx : Xsel → Fin K) {s t : OnticTime} (hs : s < 1) (ht : 1 ≤ t) :
    swapEvolve idx s t = swapG ∘ liftShear idx s t := if_pos ⟨hs, ht⟩

theorem swapEvolve_bwd (idx : Xsel → Fin K) {s t : OnticTime} (ht : t < 1) (hs : 1 ≤ s) :
    swapEvolve idx s t = liftShear idx s t ∘ swapG := by
  rw [swapEvolve, if_neg (fun h => absurd hs (not_le.mpr h.1)), if_pos ⟨ht, hs⟩]

theorem swapEvolve_lo (idx : Xsel → Fin K) {s t : OnticTime} (hs : s < 1) (ht : t < 1) :
    swapEvolve idx s t = liftShear idx s t := by
  rw [swapEvolve, if_neg (fun h => absurd h.2 (not_le.mpr ht)),
    if_neg (fun h => absurd h.2 (not_le.mpr hs))]

theorem swapEvolve_hi (idx : Xsel → Fin K) {s t : OnticTime} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    swapEvolve idx s t = liftShear idx s t := by
  rw [swapEvolve, if_neg (fun h => absurd h.1 (not_lt.mpr hs)),
    if_neg (fun h => absurd h.1 (not_lt.mpr ht))]

/-- **The two-time composition law**, all eight side-of-readout cases. Closes on `G² = id` and the
shear being frozen right of readout. -/
theorem swapEvolve_comp (idx : Xsel → Fin K) (s t u : OnticTime) :
    swapEvolve idx t u ∘ swapEvolve idx s t = swapEvolve idx s u := by
  funext x
  simp only [Function.comp_apply]
  rcases lt_or_ge s 1 with hs | hs <;> rcases lt_or_ge t 1 with ht | ht <;>
    rcases lt_or_ge u 1 with hu | hu
  · -- L L L
    rw [swapEvolve_lo idx hs ht, swapEvolve_lo idx ht hu, swapEvolve_lo idx hs hu,
      liftShear_comp]
  · -- L L R
    rw [swapEvolve_lo idx hs ht, swapEvolve_fwd idx ht hu, swapEvolve_fwd idx hs hu]
    simp only [Function.comp_apply]
    rw [liftShear_comp]
  · -- L R L
    rw [swapEvolve_fwd idx hs ht, swapEvolve_bwd idx hu ht, swapEvolve_lo idx hs hu]
    simp only [Function.comp_apply]
    rw [swapG_swapG, liftShear_comp]
  · -- L R R
    rw [swapEvolve_fwd idx hs ht, swapEvolve_hi idx ht hu, swapEvolve_fwd idx hs hu]
    simp only [Function.comp_apply]
    have he : elapsed t = elapsed u := by
      rw [elapsed_of_one_le ht, elapsed_of_one_le hu]
    rw [liftShear_frozen idx ht hu (swapG (liftShear idx s t x))]
    exact congrArg swapG (liftShear_congr idx he x)
  · -- R L L
    rw [swapEvolve_bwd idx ht hs, swapEvolve_lo idx ht hu, swapEvolve_bwd idx hu hs]
    simp only [Function.comp_apply]
    rw [liftShear_comp]
  · -- R L R
    rw [swapEvolve_bwd idx ht hs, swapEvolve_fwd idx ht hu, swapEvolve_hi idx hs hu]
    simp only [Function.comp_apply]
    rw [liftShear_comp, liftShear_frozen idx hs hu (swapG x), swapG_swapG,
      liftShear_frozen idx hs hu x]
  · -- R R L
    rw [swapEvolve_hi idx hs ht, swapEvolve_bwd idx hu ht, swapEvolve_bwd idx hu hs]
    simp only [Function.comp_apply]
    have he : elapsed t = elapsed s := by
      rw [elapsed_of_one_le ht, elapsed_of_one_le hs]
    rw [liftShear_frozen idx hs ht x]
    exact liftShear_congr_left idx he (swapG x)
  · -- R R R
    rw [swapEvolve_hi idx hs ht, swapEvolve_hi idx ht hu, swapEvolve_hi idx hs hu,
      liftShear_comp]

/-! ### The protocol -/

theorem measurable_liftShear (idx : Xsel → Fin K) (hidx : Measurable idx) (s t : OnticTime) :
    Measurable (liftShear (Xsel := Xsel) idx s t) := by
  have hshear : Measurable (shearEvolve idx s t) :=
    (shearProtocol idx hidx).measurable_evolve s t
  exact (hshear.comp measurable_fst).prodMk measurable_snd

theorem measurable_swapEvolve (idx : Xsel → Fin K) (hidx : Measurable idx) (s t : OnticTime) :
    Measurable (swapEvolve (Xsel := Xsel) idx s t) := by
  unfold swapEvolve
  split_ifs with h1 h2
  · exact measurable_swapG.comp (measurable_liftShear idx hidx s t)
  · exact (measurable_liftShear idx hidx s t).comp measurable_swapG
  · exact measurable_liftShear idx hidx s t

/-- **The calibrated-swap witness as a `MeasurementProtocol`.** Ready and pointer regions are read
off the register, exactly as for the shear. -/
noncomputable def swapProtocol (idx : Xsel → Fin K) (hidx : Measurable idx) :
    MeasurementProtocol (SwapArena Xsel K) K where
  evolve := swapEvolve idx
  evolve_self t := by
    rcases lt_or_ge t 1 with h | h
    · rw [swapEvolve_lo idx h h]
      funext x
      show liftShear idx t t x = x
      unfold liftShear
      simp [Prod.map, shearEvolve]
    · rw [swapEvolve_hi idx h h]
      funext x
      exact liftShear_frozen idx h h x
  evolve_comp := swapEvolve_comp idx
  measurable_evolve := measurable_swapEvolve idx hidx
  startTime := 0
  readoutTime := 1
  recordDuration := 1
  readyRegion := {x | x.1.2 ∈ readyArc K}
  pointerRegion i := {x | x.1.2 ∈ pointerArc K i}
  measurableSet_ready := (measurable_snd.comp measurable_fst) measurableSet_readyArc
  measurableSet_pointer i := (measurable_snd.comp measurable_fst) (measurableSet_pointerArc i)
  pointer_pairwiseDisjoint := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    exact Set.disjoint_left.mp (pointerArc_pairwiseDisjoint hij) hxi hxj
  ready_disjoint_pointer i := by
    refine Set.disjoint_left.mpr fun x hxr hxp => ?_
    simp only [Set.mem_setOf_eq, readyArc, pointerArc, Set.mem_Ioc] at hxr hxp
    have h1 : shearWidth K < shearAmt K i := by
      have hw := shearWidth_lt_gap (K := K)
      have hg := shearGap_pos (K := K)
      have hi : (1:ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by
        have h0 : (0:ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      unfold shearAmt
      nlinarith
    linarith [hxr.2, hxp.1]

/-- **The propagator preserves the Liouville measure at every time pair** — shear stage and swap
stage separately, composed per branch. It is a *dynamics*, not a relabelling. -/
theorem swapEvolve_measurePreserving (idx : Xsel → Fin K) (hidx : Measurable idx)
    (s t : OnticTime) :
    MeasurePreserving (swapEvolve (Xsel := Xsel) idx s t)
      (swapMeasure μs K) (swapMeasure μs K) := by
  have hshear : MeasurePreserving (liftShear (Xsel := Xsel) idx s t)
      (swapMeasure μs K) (swapMeasure μs K) := by
    unfold swapMeasure liftShear
    exact (shear_measurePreserving idx hidx μs s t).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin K => μs))
  unfold swapEvolve
  split_ifs with h1 h2
  · exact (measurePreserving_swapG μs).comp hshear
  · exact hshear.comp (measurePreserving_swapG μs)
  · exact hshear

/-! ### The hypotheses discharged -/

/-- The selector-and-ready sector on the arena: the bank is unconstrained. -/
def selReadyBank (idx : Xsel → Fin K) (i : Fin K) : Set (SwapArena Xsel K) :=
  {x | idx x.1.1 = i ∧ x.1.2 ∈ readyArc K}

/-- **★ `CorrelatesOn` discharged for the swap witness.** Inherited from the shear: the swap stage
never moves the register, so the outcome sector is read off the sheared register exactly as
before. -/
theorem swap_correlates (idx : Xsel → Fin K) (hidx : Measurable idx) :
    (swapProtocol idx hidx).CorrelatesOn (selReadyBank idx) := by
  intro i x hx
  have hx1 : x.1 ∈ selReady idx i := ⟨hx.1, hx.2⟩
  have hshear := shear_correlates idx hidx i hx1
  have hreg : (shearEvolve idx 0 1 x.1).2 ∈ pointerArc K i := hshear
  show (swapEvolve idx 0 1 x) ∈ {y : SwapArena Xsel K | y.1.2 ∈ pointerArc K i}
  rw [swapEvolve_fwd idx (by norm_num) le_rfl]
  simp only [Function.comp_apply, Set.mem_setOf_eq]
  rw [swapG_register]
  exact hreg

/-- **★ `PointerInvariantOn` discharged for the swap witness**: right of readout, no crossing fires
and the shear is frozen, so the propagator is the identity. -/
theorem swap_pointerInvariant (idx : Xsel → Fin K) (hidx : Measurable idx) :
    (swapProtocol idx hidx).PointerInvariantOn := by
  intro i s t hs hst _ x hx
  have hs1 : (1:ℝ) ≤ s := hs
  have ht1 : (1:ℝ) ≤ t := le_trans hs1 hst
  have hid : (swapProtocol idx hidx).evolve s t x = x := by
    show swapEvolve idx s t x = x
    rw [swapEvolve_hi idx hs1 ht1]
    exact liftShear_frozen idx hs1 ht1 x
  rw [hid]
  exact hx

end CSD.RecordLayer
