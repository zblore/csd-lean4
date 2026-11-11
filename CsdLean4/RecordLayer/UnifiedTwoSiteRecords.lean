/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedSiteRecord

/-!
# Two site detectors in one run: one writes and the other does not

**Category:** 7-SigmaLayer (the record layer). BACKLOG #364 — the author's programme "From `Σ` to
physical spacetime", obligation UO-10 on the arena of two site pointers; Remainder (a) of #363,
Remainder (c) of #361 and Remainder (e) of #360. `RecordLayer/UnifiedTwoPointer.lean` solved the
flow of a Dirac carrier coupled to two site pointers and put no readout on it.
`RecordLayer/UnifiedSiteRecord.lean` showed that a position record depends on where the carrier
is, by comparing two arenas with the one detector placed at two sites. This module puts a readout
and a ready arc on each torus of the two-pointer arena and proves the statement for one run: the
detector at the carrier's site writes, and the other detector is not displayed.

**A pointer driven by an occupancy** (any finite index). Let `U` be a continuous family of
unitaries with `‖U s − 1‖ ≤ |s| N`, and `D` an observable with `‖D‖ ≤ 1` and expectation in
`[0, 1]`. Write `I t = ∫₀ᵗ ⟨D⟩` along `U`, and `q` for the expectation of `D` at the start. Then
`I` is monotone and at most `t` (`integral_arenaObs_mono`, `integral_arenaObs_le`), and it is
within `N t²` of `t q` (`abs_integral_arenaObs_sub_mul_le`). For a pointer at `pshift (κ I t)`
from a ready angle, with `κ > 0` and `16 N ≤ 3 κ`:

* if `q ≥ 7/8` the readout history is an `IsRecordWrite` of `true` with write interval
  `[1/(6κ), 1/(2κ)]` and window `1/(6κ)` (`isRecordWrite_of_occupancy`);
* if `q ≤ 1/8` the readout is not `true` at any time up to `2/(3κ)`
  (`not_shown_of_occupancy`).

**The arena.** `echoFstReady`, `echoFstDisplay`, `echoFstShown` are the ready arc, the displayed
arc and the readout of the first torus. The second torus has `echoSiteReady`, `echoSiteDisplay`,
`echoSiteShown` of #360. All are apparatus input (UA-4). Under `diracTwoPointerFlow` each pointer
is its start turned by its displacement (`diracTwoPointerFlow_fst_pointer`,
`diracTwoPointerFlow_snd_pointer`), each displacement is its rate times the accumulated occupancy
of its site (`diracTwoShiftFst_eq_rateAt`, `diracTwoShiftSnd_eq_rateAt`), and the carrier's
propagator is within `|t| ‖H‖` of the identity, `H = diracTwoH`
(`norm_diracTwoCarrierU_sub_one_le`, `norm_diracTwoH_le`).

**The record fibres** (`twoSiteRecordFibres`): the pairs of conserved angles `(θ₂, ψ₂)` with
`16 B < 3 κ₁`, `16 B < 3 κ₂`, `3 κ₂ < 4 κ₁` and `3 κ₁ < 4 κ₂`, where
`B = ‖H_D‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|` and `κ₁`, `κ₂` are the two rates. The set is open
(`isOpen_twoSiteRecordFibres`). With both profiles `trainF` and equal strengths `g` with
`16 ‖H_D‖ < 6 g` it contains `(0, 0)` and has positive Haar measure
(`volume_twoSiteRecordFibres_trainF_pos`, `exists_volume_twoSiteRecordFibres_pos`).

**One run, two detectors.** On a record fibre, from two ready pointers, for detectors at two
different sites `j ≠ k` and a carrier with at least `7/8` of its occupancy on site `j`: the
first detector's readout history is an `IsRecordWrite` of `true` on `[1/(6κ₁), 1/(2κ₁)]` with
window `1/(6κ₁)`, and the second detector's readout is not `true` at any flow time up to
`1/(2κ₁)`, the time at which the first write is complete
(`diracTwoPointerFlow_record_fst_only`). The same with the detectors exchanged
(`diracTwoPointerFlow_record_snd_only`). Both histories are read along the one orbit.

## Exact scope

* **Up to the completion of the write.** The other detector is shown not to display up to
  `1/(2κ)` of the writing detector. Nothing is said about it afterwards. The carrier moves on
  the scale `1/‖H‖`, and a later write by the other detector is not excluded.
* **Fast detectors.** `16 ‖H‖ < 3 κ` for both: each write is complete in a time short against
  `1/‖H‖`, by which the occupancy of a detector's site has changed by at most `3/16`. No moving
  packet is followed. A packet followed to a distant detector, with the write on arrival, is in
  `RecordLayer/UnifiedArrivalRecord.lean` (#365), on an arena with one pointer.
* **Comparable rates.** The two rates are within a factor `4/3` of each other on a record
  fibre. Without that the slower detector's bound does not reach the faster one's write.
* **The carrier is a class of rays**: at least `7/8` of the occupancy on one detector's site.
  The carrier on that site (`siteRay`) is a member, and no other is exhibited. A carrier split
  between the two sites, or mostly on a third, is not covered. One trial, one
  outcome is shown for that class only.
* **A definite fact, not a statistic.** Which detector writes is decided by where the carrier
  is. No probability is stated and no weight of quantum mechanics is derived (UO-11 is not
  touched). The cross-talk between the detectors is inside the bound through `‖H‖`.
* **No clock.** This arena has two site pointers and no clock's pointer. All times are flow
  times (UA-7).
* **No signalling statement.** UO-13 is not addressed.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-8, UA-13, UO-10, UD-86 to UD-88); `RecordLayer/UnifiedTwoPointer.lean`
(`diracTwoPointerFlow_apply`, `diracTwoShiftFst`, `diracTwoShiftSnd`, `diracTwoH`);
`RecordLayer/UnifiedSiteRecord.lean` (the two-arena statement this replaces by one run);
`RecordLayer/UnifiedClockSiteRecords.lean` (`echoSiteShown`, `echoSiteReady`);
`RecordLayer/UnifiedCausalOrder.lean` (`diracTwoH_isHermitian`, `continuous_diracTwoCarrierU`);
`RecordLayer/DiracPointerRecord.lean` (`pshift_notMem_displayArc_of_le`);
`RecordLayer/DiracPointerThreshold.lean` (`pshift_mem_displayArc`);
`RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A pointer driven by an occupancy -/

section Driven

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- An expectation moves by at most `2 ‖D‖ ε` under a unitary within `ε` of the identity. -/
theorem abs_arenaObs_arenaKick_sub_self_le (U : Matrix.unitaryGroup ι ℂ) (D : Matrix ι ι ℂ)
    (p : GenArena ι) :
    |arenaObs D (arenaKick U p) - arenaObs D p| ≤ 2 * ‖D‖ * ‖U.val - 1‖ := by
  have h1 : arenaObs D p = arenaObs D (arenaKick (1 : Matrix.unitaryGroup ι ℂ) p) := by
    rw [arenaObs_kick_conj]
    simp
  have h := abs_arenaObs_arenaKick_sub_le U 1 D p
  rwa [← h1] at h

variable {U : ℝ → Matrix.unitaryGroup ι ℂ} {D : Matrix ι ι ℂ}

omit [Nonempty ι] in
/-- The accumulated expectation is monotone in time when the expectation is nonnegative. -/
theorem integral_arenaObs_mono (hUc : Continuous U) (hpos : ∀ q, 0 ≤ arenaObs D q)
    (p : GenArena ι) {s t : ℝ} (hst : s ≤ t) :
    (∫ u in (0 : ℝ)..s, arenaObs D (arenaKick (U u) p))
      ≤ ∫ u in (0 : ℝ)..t, arenaObs D (arenaKick (U u) p) := by
  have hc : Continuous fun u : ℝ => arenaObs D (arenaKick (U u) p) :=
    (continuous_arenaObs D).comp (hUc.arenaKick continuous_const)
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => arenaObs D (arenaKick (U u) p))
      volume a b := fun a b => hc.intervalIntegrable a b
  have hsub := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s)
  have hn : 0 ≤ ∫ u in s..t, arenaObs D (arenaKick (U u) p) :=
    intervalIntegral.integral_nonneg hst fun u _ => hpos _
  linarith

omit [Nonempty ι] in
/-- The accumulated expectation is at most the elapsed time when the expectation is at most
one. -/
theorem integral_arenaObs_le (hUc : Continuous U) (hle : ∀ q, arenaObs D q ≤ 1) (p : GenArena ι)
    {t : ℝ} (ht : 0 ≤ t) : (∫ u in (0 : ℝ)..t, arenaObs D (arenaKick (U u) p)) ≤ t := by
  have hc : Continuous fun u : ℝ => arenaObs D (arenaKick (U u) p) :=
    (continuous_arenaObs D).comp (hUc.arenaKick continuous_const)
  have h1 := intervalIntegral.integral_mono_on ht (hc.intervalIntegrable 0 t)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t)
    (fun u _ => hle _)
  rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1

/-- ★★ **The accumulated expectation is within `N t²` of `t` times its starting value**, for a
family of unitaries within `|s| N` of the identity and an observable of norm at most one. -/
theorem abs_integral_arenaObs_sub_mul_le (hUc : Continuous U) {N : ℝ}
    (hU : ∀ s, ‖(U s).val - 1‖ ≤ |s| * N) (hD : ‖D‖ ≤ 1) (p : GenArena ι) {t : ℝ}
    (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) - t * arenaObs D p| ≤ N * t ^ 2 := by
  have hc : Continuous fun u : ℝ => arenaObs D (arenaKick (U u) p) :=
    (continuous_arenaObs D).comp (hUc.arenaKick continuous_const)
  have hconst : (∫ _ in (0 : ℝ)..t, arenaObs D p) = t * arenaObs D p := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← hconst, ← intervalIntegral.integral_sub (hc.intervalIntegrable 0 t)
    intervalIntegrable_const]
  have hlin : Continuous fun s : ℝ => 2 * s * N := by fun_prop
  have hab : Continuous fun s : ℝ => |arenaObs D (arenaKick (U s) p) - arenaObs D p| :=
    (hc.sub continuous_const).abs
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine (intervalIntegral.integral_mono_on ht (hab.intervalIntegrable 0 t)
    (hlin.intervalIntegrable 0 t) fun s hs => ?_).trans_eq ?_
  · have h := abs_arenaObs_arenaKick_sub_self_le (U s) D p
    have hs' := hU s
    rw [abs_of_nonneg hs.1] at hs'
    have h0 : 0 ≤ ‖(U s).val - 1‖ := norm_nonneg _
    have hDn : 0 ≤ ‖D‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hD h0]
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring

/-- ★★★ **A fast pointer on a mostly occupied site writes.** A pointer starts ready and sits at
`pshift (κ I t)`, `I t` the accumulated expectation of `D`. With `κ > 0`, `16 N ≤ 3 κ` and a
starting expectation of at least `7/8`, its readout history is an `IsRecordWrite` of `true` with
write interval `[1/(6κ), 1/(2κ)]` and window `1/(6κ)`. -/
theorem isRecordWrite_of_occupancy (hUc : Continuous U) {N : ℝ}
    (hU : ∀ s, ‖(U s).val - 1‖ ≤ |s| * N) (hD : ‖D‖ ≤ 1) (hpos : ∀ q, 0 ≤ arenaObs D q)
    (hle : ∀ q, arenaObs D q ≤ 1) {κ : ℝ} (hκ : 0 < κ) (hN : 16 * N ≤ 3 * κ) (p : GenArena ι)
    (hq : 7 / 8 ≤ arenaObs D p) {a : KTorus} (ha : a ∈ readyArc 2) {hist : ℝ → Bool}
    (hhist : ∀ t, hist t = true
      ↔ pshift (κ * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) a ∈ displayArc) :
    IsRecordWrite hist 0 (1 / (6 * κ)) (1 / (2 * κ)) (1 / (6 * κ)) true := by
  have hκne : κ ≠ 0 := hκ.ne'
  have hmono : ∀ {s t : ℝ}, s ≤ t →
      κ * (∫ u in (0 : ℝ)..s, arenaObs D (arenaKick (U u) p))
        ≤ κ * ∫ u in (0 : ℝ)..t, arenaObs D (arenaKick (U u) p) := fun hst =>
    mul_le_mul_of_nonneg_left (integral_arenaObs_mono hUc hpos p hst) hκ.le
  have hzero : κ * (∫ u in (0 : ℝ)..(0 : ℝ), arenaObs D (arenaKick (U u) p)) = 0 := by
    rw [intervalIntegral.integral_same, mul_zero]
  have hup : ∀ {t : ℝ}, 0 ≤ t →
      κ * (∫ u in (0 : ℝ)..t, arenaObs D (arenaKick (U u) p)) ≤ κ * t := fun ht =>
    mul_le_mul_of_nonneg_left (integral_arenaObs_le hUc hle p ht) hκ.le
  have hthird : 1 / 3
      ≤ κ * ∫ u in (0 : ℝ)..(1 / (2 * κ)), arenaObs D (arenaKick (U u) p) := by
    have key := (abs_le.1 (abs_integral_arenaObs_sub_mul_le hUc hU hD p
      (t := 1 / (2 * κ)) (by positivity))).1
    have hNκ : N / κ ≤ 3 / 16 := by
      rw [div_le_iff₀ hκ]
      linarith
    have key' := mul_le_mul_of_nonneg_left key hκ.le
    have e1 : κ * -(N * (1 / (2 * κ)) ^ 2) = -(N / κ / 4) := by
      field_simp
      ring
    have e2 : κ * ((∫ u in (0 : ℝ)..(1 / (2 * κ)), arenaObs D (arenaKick (U u) p))
          - 1 / (2 * κ) * arenaObs D p)
        = κ * (∫ u in (0 : ℝ)..(1 / (2 * κ)), arenaObs D (arenaKick (U u) p))
          - arenaObs D p / 2 := by
      field_simp
    rw [e1, e2] at key'
    linarith
  have v₀ : κ * (1 / (6 * κ)) = 1 / 6 := by field_simp
  have v₂ : κ * (2 / (3 * κ)) = 2 / 3 := by field_simp
  have e : 1 / (2 * κ) + 1 / (6 * κ) = 2 / (3 * κ) := by
    field_simp
    ring
  refine ⟨by positivity, ?_, by positivity, fun t ht0 ht => ?_, fun t ht₁ ht₂ => ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro hshown
    refine pshift_notMem_displayArc_of_le ha ?_ ?_ ((hhist t).1 hshown)
    · have := hmono ht0
      rwa [hzero] at this
    · have h1 := (hmono ht.le).trans (hup (t := 1 / (6 * κ)) (by positivity))
      rwa [v₀] at h1
  · rw [e] at ht₂
    refine (hhist t).2 (pshift_mem_displayArc ha (hthird.trans (hmono ht₁)) ?_)
    have h1 := (hmono ht₂).trans (hup (t := 2 / (3 * κ)) (by positivity))
    rwa [v₂] at h1

/-- ★★★ **A fast pointer on a mostly empty site does not display.** With `κ > 0`, `16 N ≤ 3 κ`
and a starting expectation of at most `1/8`, the readout is not `true` at any time in
`[0, 2/(3κ)]`. -/
theorem not_shown_of_occupancy (hUc : Continuous U) {N : ℝ}
    (hU : ∀ s, ‖(U s).val - 1‖ ≤ |s| * N) (hD : ‖D‖ ≤ 1) (hpos : ∀ q, 0 ≤ arenaObs D q)
    {κ : ℝ} (hκ : 0 < κ) (hN : 16 * N ≤ 3 * κ) (p : GenArena ι)
    (hq : arenaObs D p ≤ 1 / 8) {a : KTorus} (ha : a ∈ readyArc 2) {hist : ℝ → Bool}
    (hhist : ∀ t, hist t = true
      ↔ pshift (κ * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) a ∈ displayArc)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / (3 * κ)) : ¬ hist t = true := by
  have hκne : κ ≠ 0 := hκ.ne'
  intro hshown
  refine pshift_notMem_displayArc_of_le ha ?_ ?_ ((hhist t).1 hshown)
  · have h := mul_le_mul_of_nonneg_left (integral_arenaObs_mono hUc hpos p ht0) hκ.le
    rwa [intervalIntegral.integral_same, mul_zero] at h
  · refine (mul_le_mul_of_nonneg_left (integral_arenaObs_mono hUc hpos p ht) hκ.le).trans ?_
    have key := (abs_le.1 (abs_integral_arenaObs_sub_mul_le hUc hU hD p
      (t := 2 / (3 * κ)) (by positivity))).2
    have hNκ : N / κ ≤ 3 / 16 := by
      rw [div_le_iff₀ hκ]
      linarith
    have key' := mul_le_mul_of_nonneg_left key hκ.le
    have e1 : κ * (N * (2 / (3 * κ)) ^ 2) = 4 * (N / κ) / 9 := by
      field_simp
      ring
    have e2 : κ * ((∫ u in (0 : ℝ)..(2 / (3 * κ)), arenaObs D (arenaKick (U u) p))
          - 2 / (3 * κ) * arenaObs D p)
        = κ * (∫ u in (0 : ℝ)..(2 / (3 * κ)), arenaObs D (arenaKick (U u) p))
          - 2 * arenaObs D p / 3 := by
      field_simp
    rw [e1, e2] at key'
    linarith

end Driven

/-! ### The readout of the first torus -/

section Readout

variable (N : ℕ)

/-- **The first pointer's ready region**: `θ₁` in the arc `(0, 1/6]`. Apparatus input. -/
noncomputable def echoFstReady : Set (EchoSigma N) := {x | x.1.2 ∈ readyArc 2}

theorem measurableSet_echoFstReady : MeasurableSet (echoFstReady N) :=
  (measurable_snd.comp measurable_fst) (measurableSet_readyArc (K := 2))

/-- **The first pointer's displayed region**: `θ₁` in the arc `(1/3, 5/6]`. Apparatus input. -/
noncomputable def echoFstDisplay : Set (EchoSigma N) := {x | x.1.2 ∈ displayArc}

theorem measurableSet_echoFstDisplay : MeasurableSet (echoFstDisplay N) :=
  (measurable_snd.comp measurable_fst) measurableSet_displayArc

open Classical in
/-- **The first pointer's readout**: is `θ₁` in the displayed arc? It reads the first pointer's
angle only. -/
noncomputable def echoFstShown (x : EchoSigma N) : Bool :=
  if x.1.2 ∈ displayArc then true else false

theorem measurable_echoFstShown : Measurable (echoFstShown N) := by
  unfold echoFstShown
  exact Measurable.ite ((measurable_snd.comp measurable_fst) measurableSet_displayArc)
    measurable_const measurable_const

theorem echoFstShown_eq_true_iff (x : EchoSigma N) :
    echoFstShown N x = true ↔ x ∈ echoFstDisplay N := by
  unfold echoFstShown echoFstDisplay
  simp

end Readout

/-! ### The arena of two site pointers -/

section DiracTwo

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (j k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The first pointer under the joint flow: turned by its displacement. -/
theorem diracTwoPointerFlow_fst_pointer (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)).1.2
      = pshift (diracTwoShiftFst J μ g₁ g₂ j k hf hh θ.2 ψ.2 p t) θ := by
  rw [diracTwoPointerFlow_apply]
  rfl

/-- The second pointer under the joint flow: turned by its displacement. -/
theorem diracTwoPointerFlow_snd_pointer (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)).2
      = pshift (diracTwoShiftSnd J μ g₁ g₂ j k hf hh θ.2 ψ.2 p t) ψ := by
  rw [diracTwoPointerFlow_apply]
  rfl

/-- The first pointer's displacement is its rate times the accumulated occupancy of site `j`. -/
theorem diracTwoShiftFst_eq_rateAt (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ p t
      = rateAt g₁ 1 hf φ * ∫ s in (0 : ℝ)..t, arenaObs (siteProj j)
          (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s) p) := by
  rw [diracTwoShiftFst, rateAt, div_one]

/-- The second pointer's displacement is its rate times the accumulated occupancy of site `k`. -/
theorem diracTwoShiftSnd_eq_rateAt (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ p t
      = rateAt g₂ 1 hh χ * ∫ s in (0 : ℝ)..t, arenaObs (siteProj k)
          (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s) p) := by
  rw [diracTwoShiftSnd, rateAt, div_one]

/-- **The coupled propagator is within `|t| ‖H‖` of the identity**, `H` the Hamiltonian with
both detectors. -/
theorem norm_diracTwoCarrierU_sub_one_le (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ t).val - 1‖
      ≤ |t| * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ := by
  have h := Matrix.norm_exp_smul_neg_I_sub_le (diracTwoH J μ g₁ g₂ j k hf hh φ χ) 0
    (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ) Matrix.isHermitian_zero t
  rw [smul_zero, smul_zero, NormedSpace.exp_zero, sub_zero] at h
  rwa [diracTwoCarrierU_val]

/-- The carrier's Hamiltonian is no larger than the free chain's plus the two site potentials. -/
theorem norm_diracTwoH_le (φ χ : AddCircle (1 : ℝ)) :
    ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖
      ≤ ‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift φ| + |g₂ * hh.lift χ| := by
  rw [diracTwoH]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_siteProj_le j)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_siteProj_le k)

/-- The occupancies of two different sites of the ring sum to at most one. -/
theorem arenaObs_siteProj_le_one_sub {j k : ZMod (M + 1)} (hjk : j ≠ k)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    arenaObs (siteProj k) p ≤ 1 - arenaObs (siteProj j) p := by
  have hsum : ∑ y : ZMod (M + 1), arenaObs (siteProj y) p = 1 := by
    have h := momentMap_sum_eq_one p
    rw [Fintype.sum_prod_type] at h
    rw [← h]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [arenaObs_siteProj, Fin.sum_univ_two]
  have hle := Finset.add_le_sum (f := fun y : ZMod (M + 1) => arenaObs (siteProj y) p)
    (fun y _ => arenaObs_siteProj_nonneg y p) (Finset.mem_univ j) (Finset.mem_univ k) hjk
  rw [hsum] at hle
  linarith

end DiracTwo

/-! ### The record fibres -/

section Fibres

variable (M : ℕ) {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ)
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- **The record fibres of the two-detector arena**: the pairs of conserved angles `(θ₂, ψ₂)`
at which both detectors are fast, `16 (‖H_D‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 3 κ₁` and `< 3 κ₂`, and
their rates are comparable, `3 κ₂ < 4 κ₁` and `3 κ₁ < 4 κ₂`. -/
def twoSiteRecordFibres : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 16 * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|)
        < 3 * rateAt g₁ 1 hf x.1
    ∧ 16 * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|)
        < 3 * rateAt g₂ 1 hh x.2
    ∧ 3 * rateAt g₂ 1 hh x.2 < 4 * rateAt g₁ 1 hf x.1
    ∧ 3 * rateAt g₁ 1 hf x.1 < 4 * rateAt g₂ 1 hh x.2}

/-- The record fibres are open. -/
theorem isOpen_twoSiteRecordFibres (hf1 : ContDiff ℝ 1 f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (twoSiteRecordFibres M J μ g₁ g₂ hf hh) := by
  have hκ₁ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₁ 1 hf x.1 :=
    (continuous_rateAt g₁ 1 hf hf1).comp continuous_fst
  have hκ₂ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₂ 1 hh x.2 :=
    (continuous_rateAt g₂ 1 hh hh1).comp continuous_snd
  have hB : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      16 * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) :=
    continuous_const.mul ((continuous_const.add
      (continuous_const.mul
        ((continuous_periodicLift hf hf1.continuous).comp continuous_fst)).abs).add
      (continuous_const.mul
        ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs)
  exact (isOpen_lt hB (continuous_const.mul hκ₁)).inter
    ((isOpen_lt hB (continuous_const.mul hκ₂)).inter
      ((isOpen_lt (continuous_const.mul hκ₂) (continuous_const.mul hκ₁)).inter
        (isOpen_lt (continuous_const.mul hκ₁) (continuous_const.mul hκ₂))))

variable {M}

/-- On a record fibre both rates are positive, `16 ‖H‖ ≤ 3 κ` for each, and the rates are
within a factor `4/3` of each other, for detectors at any two sites. -/
theorem twoSiteRecordFibres_bounds {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ twoSiteRecordFibres M J μ g₁ g₂ hf hh) (j k : ZMod (M + 1)) :
    0 < rateAt g₁ 1 hf φ ∧ 0 < rateAt g₂ 1 hh χ
      ∧ 16 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ≤ 3 * rateAt g₁ 1 hf φ
      ∧ 16 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ≤ 3 * rateAt g₂ 1 hh χ
      ∧ 3 * rateAt g₂ 1 hh χ ≤ 4 * rateAt g₁ 1 hf φ
      ∧ 3 * rateAt g₁ 1 hf φ ≤ 4 * rateAt g₂ 1 hh χ := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hH := mul_le_mul_of_nonneg_left (norm_diracTwoH_le J μ g₁ g₂ j k hf hh φ χ)
    (by norm_num : (0 : ℝ) ≤ 16)
  have h0 : 0 ≤ 16 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ := by positivity
  have h1' : (16 : ℝ) * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift φ| + |g₂ * hh.lift χ|)
      < 3 * rateAt g₁ 1 hf φ := h1
  have h2' : (16 : ℝ) * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift φ| + |g₂ * hh.lift χ|)
      < 3 * rateAt g₂ 1 hh χ := h2
  have h3' : 3 * rateAt g₂ 1 hh χ < 4 * rateAt g₁ 1 hf φ := h3
  have h4' : 3 * rateAt g₁ 1 hf φ < 4 * rateAt g₂ 1 hh χ := h4
  exact ⟨by linarith, by linarith, by linarith, by linarith, h3'.le, h4'.le⟩

variable (M)

/-- **With both profiles `trainF` and equal strengths `g`, the pair `(0, 0)` is a record fibre**
once `16 ‖H_D‖ < 6 g`. -/
theorem zero_mem_twoSiteRecordFibres_trainF {g : ℝ}
    (hg : 16 * ‖diracHam (L := M + 1) J μ‖ < 6 * g) :
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ∈ twoSiteRecordFibres M J μ g g trainF_periodic trainF_periodic := by
  have h0 : 0 ≤ ‖diracHam (L := M + 1) J μ‖ := norm_nonneg _
  show _ ∧ _ ∧ _ ∧ _
  rw [rateAt_trainF_zero, trainF_lift_zero, mul_zero, abs_zero, add_zero, add_zero]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- ★★ **The record fibres have positive measure** for two detectors with the profile `trainF`
and equal strengths `g`, `16 ‖H_D‖ < 6 g`. -/
theorem volume_twoSiteRecordFibres_trainF_pos {g : ℝ}
    (hg : 16 * ‖diracHam (L := M + 1) J μ‖ < 6 * g) :
    0 < volume (twoSiteRecordFibres M J μ g g trainF_periodic trainF_periodic) :=
  (isOpen_twoSiteRecordFibres M J μ g g trainF_periodic trainF_periodic
    (contDiff_trainF.of_le (by simp)) (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(0, 0), zero_mem_twoSiteRecordFibres_trainF M J μ hg⟩

/-- ★ **For every ring and every `J`, `μ` there is a detector strength** at which the record
fibres have positive measure. -/
theorem exists_volume_twoSiteRecordFibres_pos :
    ∃ g : ℝ, 0 < volume (twoSiteRecordFibres M J μ g g trainF_periodic trainF_periodic) :=
  ⟨(16 * ‖diracHam (L := M + 1) J μ‖ + 1) / 6,
    volume_twoSiteRecordFibres_trainF_pos M J μ (by
      rw [mul_div_cancel₀ _ (by norm_num : (6 : ℝ) ≠ 0)]
      linarith)⟩

end Fibres

/-! ### One run, two detectors -/

section OneRun

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (j k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The first readout along the joint flow, in terms of the first pointer's displacement. -/
theorem echoFstShown_diracTwoPointerFlow_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) (t : ℝ) :
    echoFstShown (2 * M + 1)
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)) = true
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (siteProj j)
          (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2 s) p)) θ ∈ displayArc := by
  rw [echoFstShown_eq_true_iff, ← diracTwoShiftFst_eq_rateAt,
    ← diracTwoPointerFlow_fst_pointer J μ g₁ g₂ j k hf hh hc hch t p θ ψ]
  rfl

/-- The second readout along the joint flow, in terms of the second pointer's displacement. -/
theorem echoSiteShown_diracTwoPointerFlow_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) (t : ℝ) :
    echoSiteShown (2 * M + 1)
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)) = true
      ↔ pshift (rateAt g₂ 1 hh ψ.2 * ∫ s in (0 : ℝ)..t, arenaObs (siteProj k)
          (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2 s) p)) ψ ∈ displayArc := by
  rw [echoSiteShown_eq_true_iff, ← diracTwoShiftSnd_eq_rateAt,
    ← diracTwoPointerFlow_snd_pointer J μ g₁ g₂ j k hf hh hc hch t p θ ψ]
  rfl

/-- ★★★ **One run, two detectors: the detector at the carrier's site writes and the other does
not.** On a record fibre, from two ready pointers, for detectors at two different sites and a
carrier with at least `7/8` of its occupancy on the first detector's site `j`: the first
readout's history along `diracTwoPointerFlow` is an `IsRecordWrite` of `true` from time `0`,
with write interval `[1/(6κ₁), 1/(2κ₁)]` and window `1/(6κ₁)`; and the second readout, along the
same orbit, is not `true` at any flow time up to `1/(2κ₁)`, when the first write is complete.
The times are flow times (UA-7). -/
theorem diracTwoPointerFlow_record_fst_only (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hjk : j ≠ k) {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ twoSiteRecordFibres M J μ g₁ g₂ hf hh) {κ₁ : ℝ}
    (hκ₁ : κ₁ = rateAt g₁ 1 hf θ.2) (p : GenArena (ZMod (M + 1) × Fin 2))
    (hq : 7 / 8 ≤ arenaObs (siteProj j) p) :
    IsRecordWrite
        (fun t => echoFstShown (2 * M + 1)
          (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)))
        0 (1 / (6 * κ₁)) (1 / (2 * κ₁)) (1 / (6 * κ₁)) true
      ∧ ∀ t, 0 ≤ t → t ≤ 1 / (2 * κ₁) →
          ¬ echoSiteShown (2 * M + 1)
            (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
              ((diracArenaEquiv M p, θ), ψ)) = true := by
  obtain ⟨hp₁, hp₂, hN₁, hN₂, h34, -⟩ := twoSiteRecordFibres_bounds J μ g₁ g₂ hf hh hx j k
  have hUc := continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2
  have hU := norm_diracTwoCarrierU_sub_one_le J μ g₁ g₂ j k hf hh θ.2 ψ.2
  have hqk : arenaObs (siteProj k) p ≤ 1 / 8 := by
    have := arenaObs_siteProj_le_one_sub hjk p
    linarith
  refine ⟨?_, fun t ht0 ht => ?_⟩
  · rw [hκ₁]
    exact isRecordWrite_of_occupancy hUc hU (norm_siteProj_le j)
      (arenaObs_siteProj_nonneg j) (arenaObs_siteProj_le_one j) hp₁ hN₁ p hq hθ
      (echoFstShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ)
  · refine not_shown_of_occupancy hUc hU (norm_siteProj_le k) (arenaObs_siteProj_nonneg k) hp₂
      hN₂ p hqk hψ (echoSiteShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ)
      ht0 (ht.trans ?_)
    rw [hκ₁, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

/-- ★★★ **The same with the detectors exchanged.** A carrier with at least `7/8` of its
occupancy on the second detector's site `k`: the second readout's history is an `IsRecordWrite`
of `true` with write interval `[1/(6κ₂), 1/(2κ₂)]` and window `1/(6κ₂)`, and the first readout is
not `true` at any flow time up to `1/(2κ₂)`. -/
theorem diracTwoPointerFlow_record_snd_only (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hjk : j ≠ k) {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ twoSiteRecordFibres M J μ g₁ g₂ hf hh) {κ₂ : ℝ}
    (hκ₂ : κ₂ = rateAt g₂ 1 hh ψ.2) (p : GenArena (ZMod (M + 1) × Fin 2))
    (hq : 7 / 8 ≤ arenaObs (siteProj k) p) :
    IsRecordWrite
        (fun t => echoSiteShown (2 * M + 1)
          (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)))
        0 (1 / (6 * κ₂)) (1 / (2 * κ₂)) (1 / (6 * κ₂)) true
      ∧ ∀ t, 0 ≤ t → t ≤ 1 / (2 * κ₂) →
          ¬ echoFstShown (2 * M + 1)
            (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
              ((diracArenaEquiv M p, θ), ψ)) = true := by
  obtain ⟨hp₁, hp₂, hN₁, hN₂, -, h43⟩ := twoSiteRecordFibres_bounds J μ g₁ g₂ hf hh hx j k
  have hUc := continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2
  have hU := norm_diracTwoCarrierU_sub_one_le J μ g₁ g₂ j k hf hh θ.2 ψ.2
  have hqj : arenaObs (siteProj j) p ≤ 1 / 8 := by
    have := arenaObs_siteProj_le_one_sub hjk.symm p
    linarith
  refine ⟨?_, fun t ht0 ht => ?_⟩
  · rw [hκ₂]
    exact isRecordWrite_of_occupancy hUc hU (norm_siteProj_le k)
      (arenaObs_siteProj_nonneg k) (arenaObs_siteProj_le_one k) hp₂ hN₂ p hq hψ
      (echoSiteShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ)
  · refine not_shown_of_occupancy hUc hU (norm_siteProj_le j) (arenaObs_siteProj_nonneg j) hp₁
      hN₁ p hqj hθ (echoFstShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ)
      ht0 (ht.trans ?_)
    rw [hκ₂, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

end OneRun

end CSD.RecordLayer

end
