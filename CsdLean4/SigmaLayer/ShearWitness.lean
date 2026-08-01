/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.RecordPersistence

/-!
# SigmaLayer/ShearWitness: a concrete de-isolating interaction (item 3)

**Category:** 7-SigmaLayer (the record layer — the dynamical witness).

## What this is

The first **concrete measurement witness**: an explicit propagator on `Σ_sel × T²_R` that takes an
apparatus-ready pointer into a pointer displaying the outcome the hidden selector had already fixed.
It **discharges both standing hypotheses** of the interface — `CorrelatesOn` *and*
`PointerInvariantOn` — so neither is assumed here.

## The physics: the von Neumann shear

Couple the selector's **outcome-index observable** `ι` to the pointer momentum,

  `H_int(t) = g(t) · (ι(x_sel) + 1) · δ · p_R`

Hamilton's equations give `q̇_R = g(t)(ι+1)δ`, `ṗ_R = 0`, and — the point —
`ẋ_sel ∝ ∇ι = 0` **almost everywhere, because `ι` is locally constant off the seams between selector
sectors**. So the coupling translates the pointer at an outcome-dependent rate and does not disturb
the selector, except exactly on the measure-zero seam.

★ That is where `no_everywhere_correlation` said the exceptional set *had* to live. The constraint
predicted the location of the singularity before the construction existed, and the construction puts
it there. Two independent routes agreeing is the reason to believe this is the right shape.

## Design choices, and why each is forced

* **Shifts of `(i+1)·δ`, not `i·δ`.** With `i·δ` the outcome-`0` region would *be* the ready region,
  breaking `ready_disjoint_pointer` and letting "no record" masquerade as a record. The `+1` is what
  keeps `readout_ready_eq_none` true.
* **`g` switched off after `T_M`.** This is why the interface uses a **two-time** propagator rather
  than a one-parameter group: after readout the propagator is the identity, so
  `PointerInvariantOn` is **proved, not assumed**. A group could not express the switch-off.
* **`ε = δ/2` with `δ = 1/(K+1)`.** Keeps the `K` pointer arcs and the ready arc pairwise disjoint
  inside one turn, and — separately — keeps every shifted ready state below `1`, so no wraparound
  occurs and `rep` is additive on the states that matter (`rep_pshift_of_mem`).

## What is proved

* `shearProtocol` — a genuine `MeasurementProtocol` on `Σ_sel × T²_R`: propagator laws,
  measurability, disjoint pointer regions, and a ready region disjoint from all of them.
* `shear_correlates` — **`CorrelatesOn` discharged.** `Sᵢ × R₀` lands in `Bᵢ`.
* `shear_pointerInvariant` — **`PointerInvariantOn` discharged**, because the interaction is off.
* `shear_measurePreserving` — **the propagator preserves the Liouville measure.** What makes this a
  *dynamics* rather than an arbitrary relabelling, and the hypothesis every necessary condition in
  `MeasurementConstraints.lean` assumes. A skew product: selector held fixed, each fibre translated
  by a Haar-preserving shift.
* `shear_readout_ready`, `shear_readout_after` — the non-triviality pair: **no record before, a
  unique record after**.

## ⚠️ Honest scope — what this is NOT

1. **The Hamiltonian generation is stated, not formalised.** The propagator is *constructed
   explicitly* and every required property is proved of it. That it is the time-`T_M` flow of the
   `H_int` above is a calculation in symplectic geometry, and Mathlib has no manifold symplectic /
   Hamiltonian-flow API (`reconstruction-status.md` §2a, the *permanently scoped* row). So the plan's
   "an explicit propagator **proved to arise from** that Hamiltonian" is **half done**: explicit
   propagator yes, proof of Hamiltonian origin no. Do not cite this as a formalised `H_int`.
2. **It is a witness, not a derivation.** The coupling is *engineered* to work. That is what
   constructing a witness means, and it is the same standard the rest of the corpus's witness models
   meet — but it does not show that a physically natural interaction must do this.
3. **`ι` is the outcome index.** One may object that the apparatus is "coupled to the answer". That
   objection applies verbatim to the textbook von Neumann coupling `H ∝ Â ⊗ p̂`, which this is the
   ontic analogue of. Recorded so the reader can weigh it rather than discover it.
4. **`Σ_sel` is abstract here.** The witness needs only a measurable index function, so it is proved
   at that generality; instantiating `ι` from `globalBasin` is a separate step and is not done here.
5. ~~Measure preservation is not proved.~~ **RESOLVED** — `shear_measurePreserving`. *(An earlier
   draft of this docstring listed the theorem before it existed; the claim was withdrawn and is now
   restored because the proof is in.)* The witness is therefore known to satisfy the standing
   hypothesis of every necessary condition in `MeasurementConstraints.lean`.
6. **Not connected to the Born weights.** `measure_outcomeSector_eq_of_correlates` would turn
   `shear_correlates` into a dynamical Born statement, but that needs the selector sectors to be
   `globalBasin`'s and their measures to be the Born weights. **Now unblocked by (5)**, and the
   remaining work is the instantiation, not a missing ingredient.

## References

`SigmaLayer/MeasurementProtocol.lean` (`MeasurementProtocol`, `CorrelatesOn`);
`SigmaLayer/RecordPersistence.lean` (`PointerInvariantOn`);
`SigmaLayer/MeasurementConstraints.lean` (`no_everywhere_correlation` — which predicted the seam);
`SigmaLayer/CircleFibre.lean` (`rep`); `LF4/KahlerInstance.lean` (`KTorus`).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Translating the pointer -/

/-- Translate the first torus coordinate by a real amount. The pointer's `q`; the second coordinate
is its symplectic partner and is untouched. -/
noncomputable def pshift (a : ℝ) (x : LF4.KTorus) : LF4.KTorus :=
  (x.1 + (a : AddCircle (1 : ℝ)), x.2)

@[simp] theorem pshift_zero (x : LF4.KTorus) : pshift 0 x = x := by
  simp [pshift]

theorem pshift_add (a b : ℝ) (x : LF4.KTorus) :
    pshift a (pshift b x) = pshift (a + b) x := by
  simp [pshift, add_assoc, add_comm, add_left_comm]

theorem continuous_pshift_uncurry :
    Continuous fun ar : ℝ × LF4.KTorus => pshift ar.1 ar.2 := by
  unfold pshift
  fun_prop

/-- `rep` is additive under a shift that does not wrap around the circle. The whole reason the
region arithmetic below stays on the real line. -/
theorem rep_pshift_of_mem (x : LF4.KTorus) (a : ℝ) (h : rep x.1 + a ∈ Ioc (0 : ℝ) 1) :
    rep (pshift a x).1 = rep x.1 + a := by
  have hcoe : ((rep x.1 : ℝ) : AddCircle (1 : ℝ)) = x.1 :=
    (AddCircle.equivIoc (1 : ℝ) 0).symm_apply_apply x.1
  have hadd : ((rep x.1 + a : ℝ) : AddCircle (1 : ℝ))
      = ((rep x.1 : ℝ) : AddCircle (1 : ℝ)) + ((a : ℝ) : AddCircle (1 : ℝ)) := rfl
  have hx : (pshift a x).1 = ((rep x.1 + a : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [pshift, hadd, hcoe]
  rw [hx]
  show toIocMod (by norm_num : (0:ℝ) < 1) 0 (rep x.1 + a) = rep x.1 + a
  exact (toIocMod_eq_self _).mpr (by simpa using h)

/-! ### Arc measures

`volume_circleCell` computes the measure of a CDF cell. The witness needs the same fact for arcs
specified by arbitrary endpoints, so the general statement is extracted here. -/

/-- **The Haar measure of a circle arc**, for endpoints within one turn. -/
theorem volume_repPreimage {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (volume : Measure CircleFibre) (rep ⁻¹' Ioc a b) = ENNReal.ofReal (b - a) := by
  have hS : MeasurableSet (Subtype.val ⁻¹' Ioc a b : Set (Ioc (0:ℝ) ((0:ℝ) + 1))) :=
    measurable_subtype_coe measurableSet_Ioc
  have hpre : rep ⁻¹' Ioc a b
      = (AddCircle.equivIoc (1:ℝ) 0) ⁻¹' (Subtype.val ⁻¹' Ioc a b) := rfl
  rw [hpre, (AddCircle.measurePreserving_equivIoc (T := (1:ℝ)) (a := 0)).measure_preimage
    hS.nullMeasurableSet,
    Measure.comap_apply _ Subtype.val_injective
      (fun s hs => measurableSet_Ioc.subtype_image hs) _ hS]
  have himg : (Subtype.val '' (Subtype.val ⁻¹' Ioc a b : Set (Ioc (0:ℝ) ((0:ℝ) + 1))))
      = Ioc a b := by
    rw [Subtype.image_preimage_coe]
    apply Set.inter_eq_self_of_subset_right
    intro x hx
    exact ⟨lt_of_le_of_lt h0 hx.1, le_trans hx.2 (by simpa using hb)⟩
  rw [himg, Real.volume_Ioc]

/-! ### The witness -/

variable {Xsel : Type*} [MeasurableSpace Xsel] {K : ℕ}

/-- The arc width `ε`. -/
noncomputable def shearWidth (K : ℕ) : ℝ := 1 / (2 * (K + 1))

/-- The arc spacing `δ`. -/
noncomputable def shearGap (K : ℕ) : ℝ := 1 / (K + 1)

/-- The total shift applied to the pointer when the selector reads outcome `i`. -/
noncomputable def shearAmt (K : ℕ) (i : Fin K) : ℝ := (((i : ℕ) : ℝ) + 1) * shearGap K

/-- How much of the interaction has run by time `u`: the coupling is switched on over `[0,1]` and
off thereafter. This is what makes the propagator two-time rather than a group. -/
noncomputable def elapsed (u : ℝ) : ℝ := max 0 (min u 1)

theorem elapsed_zero : elapsed 0 = 0 := by simp [elapsed]

theorem elapsed_one : elapsed 1 = 1 := by norm_num [elapsed]

theorem elapsed_of_one_le {u : ℝ} (hu : 1 ≤ u) : elapsed u = 1 := by
  simp [elapsed, min_eq_right hu]

/-- The apparatus-ready arc: `rep ∈ (0, ε]`. -/
noncomputable def readyArc (K : ℕ) : Set LF4.KTorus :=
  {x | rep x.1 ∈ Ioc (0 : ℝ) (shearWidth K)}

/-- The pointer arc displaying outcome `i`. -/
noncomputable def pointerArc (K : ℕ) (i : Fin K) : Set LF4.KTorus :=
  {x | rep x.1 ∈ Ioc (shearAmt K i) (shearAmt K i + shearWidth K)}

theorem measurableSet_readyArc : MeasurableSet (readyArc K) :=
  (measurable_rep.comp measurable_fst) measurableSet_Ioc

theorem measurableSet_pointerArc (i : Fin K) : MeasurableSet (pointerArc K i) :=
  (measurable_rep.comp measurable_fst) measurableSet_Ioc

/-! ### Arithmetic of the arcs -/

theorem shearWidth_pos : 0 < shearWidth K := by
  unfold shearWidth; positivity

theorem shearGap_pos : 0 < shearGap K := by
  unfold shearGap; positivity

theorem shearWidth_lt_gap : shearWidth K < shearGap K := by
  unfold shearWidth shearGap
  have hK : (0:ℝ) < (K : ℝ) + 1 := by positivity
  exact one_div_lt_one_div_of_lt hK (by linarith)

theorem shearAmt_pos (i : Fin K) : 0 < shearAmt K i := by
  unfold shearAmt
  have := shearGap_pos (K := K)
  positivity

/-- Every shifted ready state stays below `1`: no wraparound. -/
theorem shearAmt_add_width_le_one (i : Fin K) : shearAmt K i + shearWidth K ≤ 1 := by
  unfold shearAmt shearWidth shearGap
  have hK : (0:ℝ) < (K : ℝ) + 1 := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have expand : 1 - ((((i : ℕ) : ℝ) + 1) * (1 / ((K : ℝ) + 1)) + 1 / (2 * ((K : ℝ) + 1)))
      = (2 * (K : ℝ) - 2 * ((i : ℕ) : ℝ) - 1) / (2 * ((K : ℝ) + 1)) := by
    field_simp; ring
  have hnn : 0 ≤ 1 - ((((i : ℕ) : ℝ) + 1) * (1 / ((K : ℝ) + 1)) + 1 / (2 * ((K : ℝ) + 1))) := by
    rw [expand]
    apply div_nonneg _ (by positivity)
    linarith
  linarith

theorem shearAmt_strictMono {i j : Fin K} (h : (i : ℕ) < (j : ℕ)) :
    shearAmt K i + shearWidth K < shearAmt K j := by
  have hg := shearGap_pos (K := K)
  have hw := shearWidth_lt_gap (K := K)
  have hij : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
  unfold shearAmt
  nlinarith

/-- The ready arc has positive Haar measure, so conditioning on it is legitimate. -/
theorem volume_readyArc :
    (volume : Measure LF4.KTorus) (readyArc K) = ENNReal.ofReal (shearWidth K) := by
  have h : readyArc K
      = (rep ⁻¹' Ioc (0:ℝ) (shearWidth K)) ×ˢ (univ : Set (AddCircle (1:ℝ))) := by
    ext x; simp [readyArc]
  have hle : shearWidth K ≤ 1 := by
    unfold shearWidth
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _
    linarith
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one,
    volume_repPreimage le_rfl (le_of_lt shearWidth_pos) hle, sub_zero]

theorem volume_readyArc_ne_zero : (volume : Measure LF4.KTorus) (readyArc K) ≠ 0 := by
  rw [volume_readyArc]
  simp [ENNReal.ofReal_eq_zero, not_le, shearWidth_pos (K := K)]

/-! ### The propagator -/

/-- **The shear propagator.** Over `[s,t]` the pointer is translated by
`(elapsed t - elapsed s) · (ι+1)δ`; the selector is untouched. -/
noncomputable def shearEvolve (idx : Xsel → Fin K) (s t : OnticTime) :
    Xsel × LF4.KTorus → Xsel × LF4.KTorus :=
  fun x => (x.1, pshift ((elapsed t - elapsed s) * shearAmt K (idx x.1)) x.2)

/-- **The measurement witness as a `MeasurementProtocol`.** -/
noncomputable def shearProtocol (idx : Xsel → Fin K) (hidx : Measurable idx) :
    MeasurementProtocol (Xsel × LF4.KTorus) K where
  evolve := shearEvolve idx
  evolve_self t := by funext x; simp [shearEvolve]
  evolve_comp s t u := by
    funext x
    simp only [shearEvolve, Function.comp_apply, pshift_add]
    congr 1
    ring
  measurable_evolve s t := by
    refine Measurable.prodMk measurable_fst ?_
    have h1 : Measurable fun x : Xsel × LF4.KTorus =>
        ((elapsed t - elapsed s) * shearAmt K (idx x.1), x.2) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact (Measurable.of_discrete (f := fun i : Fin K =>
        (elapsed t - elapsed s) * shearAmt K i)).comp (hidx.comp measurable_fst)
    exact continuous_pshift_uncurry.measurable.comp h1
  startTime := 0
  readoutTime := 1
  recordDuration := 1
  readyRegion := Prod.snd ⁻¹' readyArc K
  pointerRegion i := Prod.snd ⁻¹' pointerArc K i
  measurableSet_ready := measurable_snd measurableSet_readyArc
  measurableSet_pointer i := measurable_snd (measurableSet_pointerArc i)
  pointer_pairwiseDisjoint := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    simp only [Set.mem_preimage, pointerArc, Set.mem_setOf_eq, Set.mem_Ioc] at hxi hxj
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
    · exact absurd (lt_of_le_of_lt hxi.2 (shearAmt_strictMono h)) (not_lt.mpr hxj.1.le)
    · exact absurd (lt_of_le_of_lt hxj.2 (shearAmt_strictMono h)) (not_lt.mpr hxi.1.le)
  ready_disjoint_pointer i := by
    refine Set.disjoint_left.mpr fun x hxr hxp => ?_
    simp only [Set.mem_preimage, readyArc, pointerArc, Set.mem_setOf_eq, Set.mem_Ioc] at hxr hxp
    have h1 : shearWidth K < shearAmt K i := by
      have := shearWidth_lt_gap (K := K)
      have hg := shearGap_pos (K := K)
      have hi : (1:ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by
        have : (0:ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      unfold shearAmt
      nlinarith
    linarith [hxr.2, hxp.1]

/-! ### Measure preservation -/

/-- Haar measure on the register is translation invariant. Not found by instance search: `volume` on
a product is *definitionally* the product measure but the invariance instance does not fire through
the `MeasureSpace` instance, so it is supplied here. -/
instance instIsAddLeftInvariantKTorus :
    (volume : Measure LF4.KTorus).IsAddLeftInvariant := by
  have h : (volume : Measure LF4.KTorus)
      = (volume : Measure (AddCircle (1:ℝ))).prod volume :=
    Measure.volume_eq_prod _ _
  rw [h]
  infer_instance

/-- Translating the pointer preserves Haar measure on the register — translation invariance of Haar
on the compact group `T²`. -/
theorem measurePreserving_pshift (a : ℝ) :
    MeasurePreserving (pshift a) (volume : Measure LF4.KTorus) volume := by
  have he : pshift a
      = fun x : LF4.KTorus => (((a : AddCircle (1:ℝ)), (0 : AddCircle (1:ℝ))) + x) := by
    funext x
    simp [pshift, Prod.ext_iff, add_comm]
  rw [he]
  exact measurePreserving_add_left _ _

/-- ★ **The shear propagator preserves the Liouville measure.**

This is what makes the witness a **dynamics** rather than an arbitrary relabelling of states, and it
is the hypothesis every necessary condition in `MeasurementConstraints.lean` assumes. A skew product:
the selector is held fixed and each fibre is translated by a Haar-preserving shift. -/
theorem shear_measurePreserving (idx : Xsel → Fin K) (hidx : Measurable idx)
    (μ : Measure Xsel) [SFinite μ] (s t : OnticTime) :
    MeasurePreserving (shearEvolve idx s t)
      (μ.prod (volume : Measure LF4.KTorus)) (μ.prod volume) := by
  have hgm : Measurable (Function.uncurry
      fun (x : Xsel) (r : LF4.KTorus) =>
        pshift ((elapsed t - elapsed s) * shearAmt K (idx x)) r) := by
    have h1 : Measurable fun p : Xsel × LF4.KTorus =>
        ((elapsed t - elapsed s) * shearAmt K (idx p.1), p.2) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact (Measurable.of_discrete (f := fun i : Fin K =>
        (elapsed t - elapsed s) * shearAmt K i)).comp (hidx.comp measurable_fst)
    exact continuous_pshift_uncurry.measurable.comp h1
  exact (MeasurePreserving.id μ).skew_product hgm
    (Filter.Eventually.of_forall fun x => (measurePreserving_pshift _).map_eq)

/-! ### ⚠️ The system state does not collapse -/

/-- **★ The interaction does not change the system's marginal.**

`Prod.fst ∘ evolve = Prod.fst` — the shear moves only the pointer — so the base marginal of the
post-measurement ensemble is the base marginal of the *selected* ensemble. Nothing about the system
has moved.

⚠️ **This is a genuine limitation of the witness, and it is worth stating rather than burying.** It
means the shear gives **repeatability** (re-reading the same observable returns the same outcome —
`readout_persists_on_interval`) but it does **not** implement the **Lüders update**: after outcome
`i` the system is still at `[ψ]`, not at `[eᵢ]`. A subsequent *incompatible* measurement would
therefore see the original preparation, which is not what quantum mechanics predicts.

★ And the tension is structural, not an oversight: the property that makes this witness work —
`ẋ_sel ∝ ∇ι = 0`, no back-reaction on the selector — is exactly the property that prevents collapse.
A witness that reproduces Lüders must disturb the selector, and then the clean correlation argument
has to be redone. So **item 6's Lüders half is not merely unbuilt here; this witness cannot supply
it**, and a different coupling is required. -/
theorem shear_base_marginal_unchanged (idx : Xsel → Fin K) (hidx : Measurable idx)
    (μ : Measure (Xsel × LF4.KTorus)) (i : Fin K) :
    Measure.map Prod.fst ((shearProtocol idx hidx).postMeasure μ i)
      = Measure.map Prod.fst ((shearProtocol idx hidx).selectedMeasure μ i) := by
  rw [MeasurementProtocol.postMeasure,
    Measure.map_map measurable_fst ((shearProtocol idx hidx).measurable_evolve _ _)]
  rfl

/-- The selector-and-ready sector for outcome `i`. -/
def selReady (idx : Xsel → Fin K) (i : Fin K) : Set (Xsel × LF4.KTorus) :=
  {p | idx p.1 = i ∧ p.2 ∈ readyArc K}

/-- **★ `CorrelatesOn` DISCHARGED.** The interaction carries a ready pointer, over a selector
reading `i`, into the pointer arc displaying `i`. This is the correlation theorem the Paper D
obligation asks for — here proved of an explicit propagator rather than assumed. -/
theorem shear_correlates (idx : Xsel → Fin K) (hidx : Measurable idx) :
    (shearProtocol idx hidx).CorrelatesOn (selReady idx) := by
  intro i p hp
  obtain ⟨hidxp, hready⟩ := hp
  simp only [MeasurementProtocol.outcomeSector, Set.mem_preimage]
  show (shearEvolve idx 0 1 p).2 ∈ pointerArc K i
  simp only [readyArc, Set.mem_setOf_eq, Set.mem_Ioc] at hready
  have hamt : (elapsed 1 - elapsed 0) * shearAmt K (idx p.1) = shearAmt K i := by
    rw [elapsed_zero, elapsed_one, hidxp]; ring
  have hno : rep p.2.1 + shearAmt K i ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · have := shearAmt_pos (K := K) i
      linarith [hready.1]
    · linarith [hready.2, shearAmt_add_width_le_one (K := K) i]
  simp only [shearEvolve, pointerArc, Set.mem_setOf_eq, Set.mem_Ioc]
  rw [hamt, rep_pshift_of_mem p.2 _ hno]
  exact ⟨by linarith [hready.1], by linarith [hready.2]⟩

/-- **★ `PointerInvariantOn` DISCHARGED** — and for a reason that is physics, not bookkeeping: after
the readout time the coupling is **switched off**, so the propagator is the identity and the record
cannot move. A one-parameter group could not have expressed the switch-off; this is what the
two-time propagator was for. -/
theorem shear_pointerInvariant (idx : Xsel → Fin K) (hidx : Measurable idx) :
    (shearProtocol idx hidx).PointerInvariantOn := by
  intro i s t hs hst _ x hx
  have hs1 : (1:ℝ) ≤ s := hs
  have ht1 : (1:ℝ) ≤ t := le_trans hs1 hst
  have : (shearProtocol idx hidx).evolve s t x = x := by
    show shearEvolve idx s t x = x
    simp [shearEvolve, elapsed_of_one_le hs1, elapsed_of_one_le ht1]
  rw [this]
  exact hx

/-- **★ The non-triviality pair.** Before the interaction the apparatus reads nothing; after it, it
reads exactly the outcome the hidden selector had fixed. Together these rule out an identity flow or
a pre-existing label being presented as a created record. -/
theorem shear_readout_ready (idx : Xsel → Fin K) (hidx : Measurable idx)
    {x : Xsel × LF4.KTorus} (hx : x.2 ∈ readyArc K) :
    (shearProtocol idx hidx).readout x = none :=
  (shearProtocol idx hidx).readout_ready_eq_none hx

theorem shear_readout_after (idx : Xsel → Fin K) (hidx : Measurable idx)
    {i : Fin K} {x : Xsel × LF4.KTorus} (hx : x ∈ selReady idx i) :
    (shearProtocol idx hidx).readout
      ((shearProtocol idx hidx).evolve 0 1 x) = some i :=
  (shearProtocol idx hidx).readout_evolve_outcomeSector (shear_correlates idx hidx i hx)

end CSD.RecordLayer
