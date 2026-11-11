/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTwoPointer
public import CsdLean4.RecordLayer.UnifiedDiracClockTicks

/-!
# A tick record and a position record in one run of one flow

**Category:** 7-SigmaLayer (the record layer). BACKLOG #360 — the author's programme "From `Σ` to
physical spacetime", milestone M4, condition (d) of UO-14. M4's acceptance asks that clock
readings and measurement records come from the same dynamics. #358 read tick records off the
flow of the clock extension, which has no position detector. #359 put the clock's pointer and a
site pointer under one joint energy on `ℂℙ^{4M+3} × T² × T²` and solved its flow `clockSiteFlow`,
and read no record. This module puts a readout on each torus and reads both records off that one
flow.

**The readouts are apparatus input.** `echoTickShown` reads the clock's pointer angle `θ₁` against
the displayed arc `(1/3, 5/6]`, and `echoSiteShown` reads the site pointer's angle `ψ₁` against the
same arc. The ready sets `echoTickReady` and `echoSiteReady` are the arc `(0, 1/6]` on each
pointer. These are the arcs of #352 and #358, placed on the two-pointer arena by hand. Nothing
derives them (UA-4 of `specs/unified-record-spacetime-plan.md`).

**The clock's pointer, with the detector coupled.** The clock pointer's displacement under
`clockSiteFlow` is within

  `clockSwingErr + 2 |f'(θ₂)| |g₁| |h(ψ₂)| |g₂| T²`

of the swing `A (1 − cos R t)` up to the horizon `T` (`abs_clockSiteShiftFst_sub_swing_le`): the
error of #358 plus the cross-talk of #359 (`clockSiteCrossErr`). Under the four inequalities of
#358 with this larger error the history is a swing (`isSwing_clockSiteFlow`), so every statement
of #358 about swings holds for it: the count (`IsSwing.abs_tickCount_sub_le`), the tick as a
write (`IsSwing.isRecordWrite`) and the operational time
(`IsSwing.abs_clockOpTime_sub_dilated_le`). On a fibre where the detector's profile vanishes the
swings of #358 carry over with no added error (`isSwing_clockSiteFlow_of_lift_eq_zero`). Tick `n`
is an `ActualOccurrence` of `clockSiteFlow` (`clockSiteTickRecord`).

**The site pointer, with the clock coupled.** The occupancy of site `k` on both levels is a sum
of four moment coordinates (`arenaObs_deviceSiteProj`), so it lies in `[0, 1]`. On a fibre with a
nonnegative rate the site pointer's displacement is therefore monotone in time for every carrier
and every clock coupling (`clockSiteShiftSnd_mono`), and it is at most the rate times the time
(`clockSiteShiftSnd_le`). Monotonicity needs no cross-talk term. From a ready pointer, if the
displacement is at most `1/6` at `τ₀`, at least `1/3` at `τ₁` and at most `2/3` at `τ₂`, the
readout history writes `true` (`isRecordWrite_clockSiteFlow_site`), and the write is an
`ActualOccurrence` of `clockSiteFlow` (`clockSitePositionRecord`). The three values can be read
off the device alone with the cross-talk of #359 as a margin
(`isRecordWrite_clockSiteFlow_site_of_alone`).

**One run.** Both records evolve by `clockSiteEvolve` (`clockSiteTickRecord_evolve`,
`clockSitePositionRecord_evolve`). The tick record's preparation is the position record's start
state carried by that propagator to the start of the turn (`clockSiteTickRecord_prep`). Their
histories are the two readouts along `t ↦ clockSiteFlow t x₀` from the one start `x₀`
(`clockSiteTickRecord_history`, `clockSitePositionRecord_history`).

**An exact instance.** For a device in one momentum mode, prepared a quarter turn ahead, both
profiles `trainF`, on the fibres `θ₂ = 0` and `ψ₂ = 0`, with `g₂ > 0`: the clock's pointer is a
swing at the level splitting `R` on every horizon, and the site pointer's readout writes `true`
between the flow times `(M+1)/(12 g₂)` and `(M+1)/(6 g₂)` and holds it for `(M+1)/(6 g₂)`
(`clockSite_records_train`). Tick `n` and the position write are writes along one history.

## Exact scope

* **Conditional in general.** `isSwing_clockSiteFlow` has the four inequalities as hypotheses,
  with an error that grows as `T²`. `isRecordWrite_clockSiteFlow_site` has the three displacement
  values as hypotheses. The instance meets both sets at once only on the fibres where both
  profiles vanish, a null set of the arena's measure, and for one mode. No instance on a set of
  fibres of positive measure is given.
* **In the instance neither pointer acts on the device.** On the fibres where both profiles
  vanish the device moves freely (`arenaKick_clockSiteCarrierU_devicePacket`) and both pointers
  are driven by it. The cross-talk term is zero there. The two records are two readings of one
  orbit of one flow; an action of one record's apparatus on the other is not exhibited.
* **The position record does not single out the site.** For one momentum mode the occupancy of
  every site is `1/(M+1)` at all times (`arenaObs_deviceSiteProj_of_uniform`), so the write time
  in the instance is the same for every `k`. The record says that the accumulated occupancy of
  site `k` crossed the threshold. It is a definite fact of the one trajectory. It is not a
  statistical statement, and no weight of quantum mechanics is derived from it. A carrier mostly
  on one site, whose record is written only by a detector at that site, is in
  `RecordLayer/UnifiedSiteRecord.lean` (#363).
* **Tick records are erased, the position record is held for a window.** Each tick is held for
  less than a turn (#358). The position write is held for `τ₂ − τ₁`. Nothing here holds either
  for all later times.
* **All times are flow times** (UA-7). The start, the write interval and the window of each
  record are values of the flow parameter. The count of ticks at the position write is not taken:
  that needs the event of the write as a record, which is condition (c) of UO-14.
* **No register holds the count** (condition (b) of UO-14), **and the clock's coupling is not at
  a site** (condition (e)). Neither is changed here.
* **Exact and approximate.** The occupancy formula, the monotonicity, the reduction on the
  fibres where a profile vanishes and the instance are exact. The swing with the detector coupled
  is within stated upper bounds, not shown attained.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-13, UO-14, UD-72 onward); `RecordLayer/UnifiedTwoPointer.lean` (`clockSiteFlow`,
`clockSiteFlow_apply`, `clockSiteFlow_fst_of_lift_eq_zero`, `abs_clockSiteShiftFst_sub_le`,
`abs_clockSiteShiftSnd_sub_le`, `deviceSiteProj`); `RecordLayer/UnifiedDiracClockTicks.lean`
(`IsSwing`, `isSwing_of_abs_shift_sub_le`, `abs_clockPointerShift_sub_swing_le`,
`isSwing_clockPointerFlow_train`, `clockTickRecord`); `RecordLayer/DiracPointerRecord.lean`
(`isRecordWrite_diracPointerFlow`, `diracPointerRecord`, `pshift_notMem_displayArc_of_le`);
`RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`, `ActualOccurrence`);
`LF4/EchoVolume.lean` (`continuous_twoCoupledFlow`, `measurable_twoCoupledFlow`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A swing read through a map -/

/-- A history whose image under `π` is a swing between `rest` and `disp` is a swing between
their preimages. -/
theorem IsSwing.preimage {X Y : Type*} {rest disp : Set X} {γ : ℝ → Y} {π : Y → X}
    {R c d T : ℝ} (h : IsSwing rest disp (fun t => π (γ t)) R c d T) :
    IsSwing (π ⁻¹' rest) (π ⁻¹' disp) γ R c d T where
  rate_pos := h.rate_pos
  neg_one_lt := h.neg_one_lt
  thresh_le := h.thresh_le
  rest_of_cos := h.rest_of_cos
  disp_of_cos := h.disp_of_cos
  le_cos_of_rest := h.le_cos_of_rest
  cos_lt_of_disp := h.cos_lt_of_disp

/-! ### The expectation of a diagonal matrix -/

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The expectation of a real combination of basis projectors is the same combination of the
ray's moment coordinates. -/
theorem arenaObs_sum_smul_single (s : Finset ι) (d : ι → ℝ) (p : GenArena ι) :
    arenaObs (∑ x ∈ s, ((d x : ℝ) : ℂ) • Matrix.single x x (1 : ℂ)) p
      = ∑ x ∈ s, d x * momentMap p x := by
  induction s using Finset.induction_on with
  | empty => simp [arenaObs]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, arenaObs_add, arenaObs_real_smul,
      arenaObs_single_eq_momentMap, ih]

/-- ★ **The expectation of a real diagonal matrix at a ray** is the average of its entries by
the ray's moment coordinates. -/
theorem arenaObs_diagonal_ofReal (d : ι → ℝ) (p : GenArena ι) :
    arenaObs (Matrix.diagonal fun x => ((d x : ℝ) : ℂ)) p = ∑ x, d x * momentMap p x := by
  have hD : (Matrix.diagonal fun x => ((d x : ℝ) : ℂ))
      = ∑ x, ((d x : ℝ) : ℂ) • Matrix.single x x (1 : ℂ) := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.single_apply]
    · rw [Matrix.diagonal_apply_ne _ hij]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      have hc : ¬(c = i ∧ c = j) := fun hc => hij (hc.1.symm.trans hc.2)
      simp [hc]
  rw [hD, arenaObs_sum_smul_single]

end Diagonal

/-! ### The occupancy of a site on both levels -/

section Occupancy

variable {M : ℕ}

/-- ★ **The occupancy of site `k` of the device at a ray** is the sum of its four moment
coordinates: two spinor components on each of the two levels. -/
theorem arenaObs_deviceSiteProj (k : ZMod (M + 1))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (deviceSiteProj k) p = ∑ a : Fin 2, ∑ l : Fin 2, momentMap p ((k, a), l) := by
  have hc : (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => if x.1.1 = k then (1 : ℂ) else 0)
      = fun x => (((if x.1.1 = k then (1 : ℝ) else 0 : ℝ)) : ℂ) := by
    funext x
    split_ifs <;> simp
  rw [deviceSiteProj_eq_diagonal, hc, arenaObs_diagonal_ofReal, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp
  · intro y _ hy
    simp [hy]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem arenaObs_deviceSiteProj_nonneg (k : ZMod (M + 1))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) : 0 ≤ arenaObs (deviceSiteProj k) p := by
  rw [arenaObs_deviceSiteProj]
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun l _ => momentMap_nonneg p _

/-- The occupancies of the sites add up to one. -/
theorem sum_arenaObs_deviceSiteProj (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    ∑ k : ZMod (M + 1), arenaObs (deviceSiteProj k) p = 1 := by
  have h := momentMap_sum_eq_one p
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => arenaObs_deviceSiteProj k p

theorem arenaObs_deviceSiteProj_le_one (k : ZMod (M + 1))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) : arenaObs (deviceSiteProj k) p ≤ 1 := by
  rw [← sum_arenaObs_deviceSiteProj p]
  exact Finset.single_le_sum (f := fun y : ZMod (M + 1) => arenaObs (deviceSiteProj y) p)
    (fun y _ => arenaObs_deviceSiteProj_nonneg y p) (Finset.mem_univ k)

/-- ★ **A ray spread evenly over the ring occupies every site equally**: if each moment
coordinate does not depend on the site, the occupancy of site `k` is `1/(M+1)`. -/
theorem arenaObs_deviceSiteProj_of_uniform (k : ZMod (M + 1))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (hu : ∀ (y : ZMod (M + 1)) (a l : Fin 2),
      momentMap p ((y, a), l) = momentMap p ((k, a), l)) :
    arenaObs (deviceSiteProj k) p = 1 / ((M : ℝ) + 1) := by
  have h1 := sum_arenaObs_deviceSiteProj p
  have h2 : ∀ y : ZMod (M + 1), arenaObs (deviceSiteProj y) p = arenaObs (deviceSiteProj k) p :=
    fun y => by
      rw [arenaObs_deviceSiteProj, arenaObs_deviceSiteProj]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => by
        rw [hu y a l]
  rw [Finset.sum_congr rfl fun y _ => h2 y, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at h1
  rw [eq_div_iff (by positivity), mul_comm]
  exact_mod_cast h1

/-- The moment coordinates of the ray of a device amplitude. -/
theorem momentMap_deviceRay (Ψ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ) (hΨ : Ψ ≠ 0)
    (x : (ZMod (M + 1) × Fin 2) × Fin 2) :
    momentMap (deviceRay Ψ hΨ) x = ‖Ψ x‖ ^ 2 / (deviceNorm Ψ).re := by
  rw [deviceRay, momentMap_mk, norm_sq_toLp_device]

/-- A device in one momentum mode has the same modulus at every site. -/
theorem norm_devicePacket_single (J μ₀ μ₁ : ℝ) (m : ℤ) (β : ℤ → ℂ) (t : ℝ)
    (y y' : ZMod (M + 1)) (a l : Fin 2) :
    ‖devicePacket (L := M + 1) J μ₀ μ₁ {m} β t ((y, a), l)‖
      = ‖devicePacket (L := M + 1) J μ₀ μ₁ {m} β t ((y', a), l)‖ := by
  simp only [devicePacket, packet, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, diracMode,
    planeWave, norm_mul, Circle.norm_coe]

/-- ★ **A device in one momentum mode occupies every site equally**, at every time of its
packet. -/
theorem arenaObs_deviceSiteProj_single {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ℤ)
    {β : ℤ → ℂ} (hβ : β m ≠ 0) (k : ZMod (M + 1)) (t : ℝ) :
    arenaObs (deviceSiteProj k)
        (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β t)
          (devicePacket_single_ne_zero h0 h1 m hβ t))
      = 1 / ((M : ℝ) + 1) :=
  arenaObs_deviceSiteProj_of_uniform k _ fun y a l => by
    rw [momentMap_deviceRay, momentMap_deviceRay, norm_devicePacket_single J μ₀ μ₁ m β t y k]

end Occupancy

/-! ### The readouts on the two-pointer arena -/

section Readout

variable (M : ℕ)

/-- **The clock pointer's ready region** on the two-pointer arena: `θ₁` in the arc `(0, 1/6]`.
The region `tickReady` of #358, read on the clock's part of the state. Apparatus input. -/
noncomputable def echoTickReady : Set (EchoSigma (4 * M + 3)) := Prod.fst ⁻¹' tickReady M

theorem measurableSet_echoTickReady : MeasurableSet (echoTickReady M) :=
  measurable_fst (measurableSet_tickReady M)

/-- **The clock pointer's displayed region** on the two-pointer arena: `θ₁` in the arc
`(1/3, 5/6]`. Apparatus input. -/
noncomputable def echoTickDisplay : Set (EchoSigma (4 * M + 3)) := Prod.fst ⁻¹' tickDisplay M

theorem measurableSet_echoTickDisplay : MeasurableSet (echoTickDisplay M) :=
  measurable_fst (measurableSet_tickDisplay M)

/-- **The tick readout** on the two-pointer arena: `tickShown` of #358 on the clock's part of the
state. It reads the clock pointer's angle `θ₁` only. -/
noncomputable def echoTickShown (x : EchoSigma (4 * M + 3)) : Bool := tickShown M x.1

theorem measurable_echoTickShown : Measurable (echoTickShown M) :=
  (measurable_tickShown M).comp measurable_fst

theorem echoTickShown_eq_true_iff (x : EchoSigma (4 * M + 3)) :
    echoTickShown M x = true ↔ x ∈ echoTickDisplay M :=
  tickShown_eq_true_iff M x.1

variable (N : ℕ)

/-- **The site pointer's ready region**: `ψ₁` in the arc `(0, 1/6]`. Apparatus input. -/
noncomputable def echoSiteReady : Set (EchoSigma N) := {x | x.2 ∈ readyArc 2}

theorem measurableSet_echoSiteReady : MeasurableSet (echoSiteReady N) :=
  measurable_snd (measurableSet_readyArc (K := 2))

/-- **The site pointer's displayed region**: `ψ₁` in the arc `(1/3, 5/6]`. Apparatus input. -/
noncomputable def echoSiteDisplay : Set (EchoSigma N) := {x | x.2 ∈ displayArc}

theorem measurableSet_echoSiteDisplay : MeasurableSet (echoSiteDisplay N) :=
  measurable_snd measurableSet_displayArc

open Classical in
/-- **The site pointer's readout**: is `ψ₁` in the displayed arc? It reads the second pointer's
angle only. -/
noncomputable def echoSiteShown (x : EchoSigma N) : Bool :=
  if x.2 ∈ displayArc then true else false

theorem measurable_echoSiteShown : Measurable (echoSiteShown N) := by
  unfold echoSiteShown
  exact Measurable.ite (measurable_snd measurableSet_displayArc) measurable_const measurable_const

theorem echoSiteShown_eq_true_iff (x : EchoSigma N) :
    echoSiteShown N x = true ↔ x ∈ echoSiteDisplay N := by
  unfold echoSiteShown echoSiteDisplay
  simp

end Readout

/-! ### The joint flow as a two-time evolution -/

section Flow

variable {M : ℕ}

variable {f h : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ : ℝ) (k : ZMod (M + 1)) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1)

theorem continuous_clockSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    Continuous (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t) :=
  continuous_twoCoupledFlow _ _ _ hf hh hc hch t

set_option synthInstance.maxSize 512 in
theorem measurable_clockSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    Measurable (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t) :=
  measurable_twoCoupledFlow _ _ _ hf hh hc hch t

/-- **The two-time propagator** of the joint dynamics of the device, the clock's pointer and the
site pointer: autonomous, so only the elapsed time enters. It is `clockSiteFlow` and nothing
else. -/
noncomputable def clockSiteEvolve (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (s t : ℝ) :
    EchoSigma (4 * M + 3) → EchoSigma (4 * M + 3) :=
  clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (t - s)

theorem clockSiteEvolve_self (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch t t = id := by
  funext x
  rw [clockSiteEvolve, sub_self, clockSiteFlow_zero]
  rfl

/-- **The two-time law.** -/
theorem clockSiteEvolve_comp (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (s t u : ℝ) :
    clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch t u
        ∘ clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch s t
      = clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch s u := by
  funext x
  show clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (u - t)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (t - s) x)
    = clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (u - s) x
  rw [← clockSiteFlow_add, sub_add_sub_cancel]

theorem measurable_clockSiteEvolve (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (s t : ℝ) :
    Measurable (clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch s t) :=
  measurable_clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (t - s)

/-- The clock's pointer under the joint flow: turned by its displacement. -/
theorem clockSiteFlow_clock_pointer (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) :
    (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).1.2
      = pshift (clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p t) θ := by
  rw [clockSiteFlow_apply]
  rfl

/-- The site pointer under the joint flow: turned by its displacement. -/
theorem clockSiteFlow_site_pointer (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) :
    (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).2
      = pshift (clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p t) ψ := by
  rw [clockSiteFlow_apply]
  rfl

/-! ### The site pointer does not turn back -/

theorem continuous_clockSiteOccupancy (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    Continuous fun s : ℝ => arenaObs (deviceSiteProj k)
      (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p) :=
  (continuous_arenaObs (deviceSiteProj k)).comp
    ((continuous_idxTwoCarrierU _ _ _ hf hh φ χ).arenaKick continuous_const)

/-- The site pointer's displacement is its fibre's rate times the accumulated occupancy of the
site, along the carrier's orbit with both pointers coupled. -/
theorem clockSiteShiftSnd_eq_rateAt (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) :
    clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t
      = rateAt g₂ 1 hh χ * ∫ s in (0 : ℝ)..t, arenaObs (deviceSiteProj k)
          (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p) := by
  rw [clockSiteShiftSnd, rateAt, div_one]

/-- ★★ **On a fibre with a nonnegative rate the site pointer's displacement is monotone in
time**, for every carrier, every fibre of the clock's pointer and every clock coupling: it is the
rate times an integral of an occupancy, which is nonnegative. The clock's pointer changes the
orbit the occupancy is taken along, and cannot change its sign. -/
theorem clockSiteShiftSnd_mono (φ : AddCircle (1 : ℝ)) {χ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ rateAt g₂ 1 hh χ) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {s t : ℝ}
    (hst : s ≤ t) :
    clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p s
      ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t := by
  rw [clockSiteShiftSnd_eq_rateAt, clockSiteShiftSnd_eq_rateAt]
  refine mul_le_mul_of_nonneg_left ?_ hκ
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun u => arenaObs (deviceSiteProj k)
      (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ u) p)) volume a b :=
    fun a b => (continuous_clockSiteOccupancy J μ₀ μ₁ g₁ g₂ k hf hh φ χ p).intervalIntegrable a b
  have hsub := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s)
  have hn : 0 ≤ ∫ u in s..t, arenaObs (deviceSiteProj k)
      (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ u) p) :=
    intervalIntegral.integral_nonneg hst fun u _ => arenaObs_deviceSiteProj_nonneg k _
  linarith

theorem clockSiteShiftSnd_zero (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p 0 = 0 := by
  rw [clockSiteShiftSnd, intervalIntegral.integral_same, mul_zero]

theorem clockSiteShiftSnd_nonneg (φ : AddCircle (1 : ℝ)) {χ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ rateAt g₂ 1 hh χ) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t := by
  have h1 := clockSiteShiftSnd_mono J μ₀ μ₁ g₁ g₂ k hf hh φ hκ p ht
  rwa [clockSiteShiftSnd_zero] at h1

/-- ★ **The site pointer turns no faster than its fibre's rate**: the occupancy is at most one,
so the displacement up to `t` is at most the rate times `t`, on every fibre of the clock's
pointer. A ready pointer therefore stays outside the displayed arc up to the time `1/(6κ)`. -/
theorem clockSiteShiftSnd_le (φ : AddCircle (1 : ℝ)) {χ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ rateAt g₂ 1 hh χ) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ}
    (ht : 0 ≤ t) :
    clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t ≤ rateAt g₂ 1 hh χ * t := by
  rw [clockSiteShiftSnd_eq_rateAt]
  refine mul_le_mul_of_nonneg_left ?_ hκ
  have h1 := intervalIntegral.integral_mono_on ht
    ((continuous_clockSiteOccupancy J μ₀ μ₁ g₁ g₂ k hf hh φ χ p).intervalIntegrable 0 t)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t)
    (fun u _ => arenaObs_deviceSiteProj_le_one k _)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
  exact h1

/-! ### The position write -/

/-- ★★★ **The site pointer's readout history under the joint flow writes `true`.** On a fibre
of the site pointer with rate `κ ≥ 0`, from a ready site pointer, for every carrier and every
state of the clock's pointer: if the site pointer's displacement is at most `1/6` at `τ₀`, at
least `1/3` at `τ₁` and at most `2/3` at `τ₂`, the history of `echoSiteShown` along
`clockSiteFlow` is not `true` on `[0, τ₀)` and is `true` on `[τ₁, τ₂]`. The three values are
hypotheses about the joint orbit. -/
theorem isRecordWrite_clockSiteFlow_site (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {ψ : KTorus} (hψ : ψ ∈ readyArc 2) (θ : KTorus) (hκ : 0 ≤ rateAt g₂ 1 hh ψ.2)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₁)
    (h₂ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₂ ≤ 2 / 3) :
    IsRecordWrite
      (fun t => echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)))
      0 τ₀ τ₁ (τ₂ - τ₁) true where
  start_le := hτ₀
  interval := hτ₁
  window_nonneg := sub_nonneg.2 hτ₂
  before := fun t ht0 ht => by
    show ¬ echoSiteShown (4 * M + 3)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)) = true
    rw [echoSiteShown_eq_true_iff]
    show (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).2
      ∉ displayArc
    rw [clockSiteFlow_site_pointer]
    exact pshift_notMem_displayArc_of_le hψ
      (clockSiteShiftSnd_nonneg J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ p ht0)
      ((clockSiteShiftSnd_mono J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ p ht.le).trans h₀)
  holds := fun t ht₁ ht₂ => by
    show echoSiteShown (4 * M + 3)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)) = true
    rw [echoSiteShown_eq_true_iff]
    show (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).2
      ∈ displayArc
    rw [clockSiteFlow_site_pointer]
    exact pshift_mem_displayArc hψ
      (h₁.trans (clockSiteShiftSnd_mono J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ p ht₁))
      ((clockSiteShiftSnd_mono J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ p (by linarith)).trans h₂)

/-- ★★ **The position write from the device alone, with the cross-talk as a margin.** If the
site pointer's displacement on the device with no clock pointer clears the three thresholds by
the cross-talk bound `2 |h'(ψ₂)| |g₂| |f(θ₂)| |g₁| τ²` of #359 at each of the three times, the
joint flow writes. -/
theorem isRecordWrite_clockSiteFlow_site_of_alone (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) {ψ : KTorus} (hψ : ψ ∈ readyArc 2) (θ : KTorus)
    (hκ : 0 ≤ rateAt g₂ 1 hh ψ.2) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    {τ₀ τ₁ τ₂ : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : idxPointerShift (deviceHam_isHermitian J μ₀ μ₁) (deviceSiteProj_smul_isHermitian g₂ k)
        hh ψ.2 p τ₀
      + 2 * |hh.deriv_periodic.lift ψ.2| * (|g₂| * (|hf.lift θ.2| * |g₁|) * τ₀ ^ 2) ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ idxPointerShift (deviceHam_isHermitian J μ₀ μ₁)
        (deviceSiteProj_smul_isHermitian g₂ k) hh ψ.2 p τ₁
      - 2 * |hh.deriv_periodic.lift ψ.2| * (|g₂| * (|hf.lift θ.2| * |g₁|) * τ₁ ^ 2))
    (h₂ : idxPointerShift (deviceHam_isHermitian J μ₀ μ₁) (deviceSiteProj_smul_isHermitian g₂ k)
        hh ψ.2 p τ₂
      + 2 * |hh.deriv_periodic.lift ψ.2| * (|g₂| * (|hf.lift θ.2| * |g₁|) * τ₂ ^ 2) ≤ 2 / 3) :
    IsRecordWrite
      (fun t => echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)))
      0 τ₀ τ₁ (τ₂ - τ₁) true := by
  have e₀ := abs_le.1 (abs_clockSiteShiftSnd_sub_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p hτ₀)
  have e₁ := abs_le.1
    (abs_clockSiteShiftSnd_sub_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p (hτ₀.trans hτ₁))
  have e₂ := abs_le.1
    (abs_clockSiteShiftSnd_sub_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p
      ((hτ₀.trans hτ₁).trans hτ₂))
  exact isRecordWrite_clockSiteFlow_site J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ hκ p hτ₀ hτ₁ hτ₂
    (by linarith [e₀.2]) (by linarith [e₁.1]) (by linarith [e₂.2])

/-- ★★★ **The position write as an actual occurrence of the joint flow.** Its `evolve` is
`clockSiteFlow` over the elapsed time, its readout is `echoSiteShown`, its preparation is the
carrier `p` with any clock pointer and a ready site pointer, its site is `k`, and its `isWrite`
field is `isRecordWrite_clockSiteFlow_site`. The start, the write interval and the window are
flow times (UA-7). -/
noncomputable def clockSitePositionRecord (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {ψ : KTorus} (hψ : ψ ∈ readyArc 2) (θ : KTorus) (hκ : 0 ≤ rateAt g₂ 1 hh ψ.2)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₁)
    (h₂ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₂ ≤ 2 / 3) :
    ActualOccurrence (EchoSigma (4 * M + 3)) Bool (M + 1) where
  evolve := clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  evolve_self := clockSiteEvolve_self J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  evolve_comp := clockSiteEvolve_comp J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  measurable_evolve := measurable_clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  readout := echoSiteShown (4 * M + 3)
  measurable_readout := measurable_echoSiteShown (4 * M + 3)
  ready := echoSiteReady (4 * M + 3)
  measurableSet_ready := measurableSet_echoSiteReady (4 * M + 3)
  prep := ((clockArenaEquiv M p, θ), ψ)
  prep_mem := hψ
  site := {siteFin k}
  start := 0
  value := true
  writeStart := τ₀
  writeEnd := τ₁
  window := τ₂ - τ₁
  isWrite := by
    have key := isRecordWrite_clockSiteFlow_site J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ hκ p
      hτ₀ hτ₁ hτ₂ h₀ h₁ h₂
    have e : (fun t : ℝ => echoSiteShown (4 * M + 3)
          (clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch 0 t ((clockArenaEquiv M p, θ), ψ)))
        = fun t => echoSiteShown (4 * M + 3)
          (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)) := by
      funext t
      rw [clockSiteEvolve, sub_zero]
    rw [e]
    exact key

/-- The position record's history is the site readout along the joint flow from its
preparation. -/
theorem clockSitePositionRecord_history (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {ψ : KTorus} (hψ : ψ ∈ readyArc 2) (θ : KTorus) (hκ : 0 ≤ rateAt g₂ 1 hh ψ.2)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₁)
    (h₂ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₂ ≤ 2 / 3) (t : ℝ) :
    (clockSitePositionRecord J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ hκ p hτ₀ hτ₁ hτ₂ h₀ h₁
        h₂).history t
      = echoSiteShown (4 * M + 3)
          (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)) := by
  show echoSiteShown (4 * M + 3)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (t - 0) ((clockArenaEquiv M p, θ), ψ))
    = echoSiteShown (4 * M + 3)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ))
  rw [sub_zero]

theorem clockSitePositionRecord_evolve (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {ψ : KTorus} (hψ : ψ ∈ readyArc 2) (θ : KTorus) (hκ : 0 ≤ rateAt g₂ 1 hh ψ.2)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₁)
    (h₂ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₂ ≤ 2 / 3) :
    (clockSitePositionRecord J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ hκ p hτ₀ hτ₁ hτ₂ h₀ h₁
        h₂).evolve
      = clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch :=
  rfl

/-! ### The clock's pointer with the detector coupled -/

/-- **The cross-talk term in the swing's error**: the bound of #359 on what the site detector
does to the clock pointer's displacement up to the horizon `T`,
`2 |f'(θ₂)| |g₁| |h(ψ₂)| |g₂| T²`. It vanishes on the fibres where the detector's profile
does. -/
noncomputable def clockSiteCrossErr (φ χ : AddCircle (1 : ℝ)) (T : ℝ) : ℝ :=
  2 * |hf.deriv_periodic.lift φ| * (|g₁| * (|hh.lift χ| * |g₂|) * T ^ 2)

theorem clockSiteCrossErr_nonneg (φ χ : AddCircle (1 : ℝ)) (T : ℝ) :
    0 ≤ clockSiteCrossErr g₁ g₂ hf hh φ χ T := by
  unfold clockSiteCrossErr
  positivity

/-- ★★ **The clock's pointer against the swing, with the detector coupled.** On every pair of
fibres, for a device whose coherence stays within `|s| ε` of `e^{−iRs} C₀`: up to the horizon `T`
the clock pointer's displacement under the joint flow is within `clockSwingErr` plus
`clockSiteCrossErr` of `clockSwingAmp` times `1 − cos R t`. An upper bound. -/
theorem abs_clockSiteShiftFst_sub_swing_le (φ χ : AddCircle (1 : ℝ))
    {Ψ₀ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ₀ ≠ 0) {R : ℝ} (hR : 0 < R) {C₀ : ℂ}
    {ε : ℝ}
    (hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀)
        - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s)) * C₀‖ ≤ |s| * ε)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh φ χ (deviceRay Ψ₀ hΨ) t
        - clockSwingAmp g₁ hf φ R (deviceNorm Ψ₀).re C₀ * (1 - Real.cos (R * t))|
      ≤ clockSwingErr g₁ hf φ R (deviceNorm Ψ₀).re C₀ ε T
        + clockSiteCrossErr g₁ g₂ hf hh φ χ T := by
  have e1 := abs_clockSiteShiftFst_sub_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ (deviceRay Ψ₀ hΨ) ht
  have e2 := abs_clockPointerShift_sub_swing_le J μ₀ μ₁ g₁ hf φ hΨ hR hdrift ht htT
  have e3 : 2 * |hf.deriv_periodic.lift φ| * (|g₁| * (|hh.lift χ| * |g₂|) * t ^ 2)
      ≤ clockSiteCrossErr g₁ g₂ hf hh φ χ T := by
    unfold clockSiteCrossErr
    have ht2 : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht htT 2
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht2 (by positivity))
      (by positivity)
  have e4 := abs_sub_le (clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh φ χ (deviceRay Ψ₀ hΨ) t)
    (clockPointerShift J μ₀ μ₁ g₁ hf φ (deviceRay Ψ₀ hΨ) t)
    (clockSwingAmp g₁ hf φ R (deviceNorm Ψ₀).re C₀ * (1 - Real.cos (R * t)))
  linarith

/-- ★★★ **The clock's pointer is a swing history of the joint flow, with the detector
coupled**, under the four inequalities of #358 with the cross-talk added to the error. The four
inequalities are hypotheses. The error `δ` grows as `T²`, so they bound the horizon. -/
theorem isSwing_clockSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {Ψ₀ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ₀ ≠ 0) {R : ℝ} (hR : 0 < R) {C₀ : ℂ}
    {ε : ℝ}
    (hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀)
        - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s)) * C₀‖ ≤ |s| * ε)
    (θ ψ : KTorus) {T A δ : ℝ}
    (hAe : A = clockSwingAmp g₁ hf θ.2 R (deviceNorm Ψ₀).re C₀)
    (hδe : δ = clockSwingErr g₁ hf θ.2 R (deviceNorm Ψ₀).re C₀ ε T
      + clockSiteCrossErr g₁ g₂ hf hh θ.2 ψ.2 T)
    (hA : 0 < A) (h₁ : δ < rep θ.1) (h₂ : rep θ.1 + δ ≤ 1 / 6)
    (h₃ : 1 / 3 < rep θ.1 + 2 * A - δ) (h₄ : rep θ.1 + 2 * A + δ ≤ 5 / 6) :
    IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t
        ((clockArenaEquiv M (deviceRay Ψ₀ hΨ), θ), ψ))
      R (1 - (1 / 3 - rep θ.1 - δ) / A) (1 - (1 / 3 - rep θ.1 + δ) / A) T := by
  have hε : 0 ≤ ε := by
    have e1 := (norm_nonneg _).trans (hdrift 1)
    rwa [abs_one, one_mul] at e1
  have hδ : 0 ≤ δ := by
    rw [hδe]
    exact add_nonneg (clockSwingErr_nonneg g₁ hf θ.2 hR (deviceNorm_re_pos hΨ) C₀ hε T)
      (clockSiteCrossErr_nonneg g₁ g₂ hf hh θ.2 ψ.2 T)
  have key : IsSwing (tickReady M) (tickDisplay M)
      (fun t => (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t
        ((clockArenaEquiv M (deviceRay Ψ₀ hΨ), θ), ψ)).1)
      R (1 - (1 / 3 - rep θ.1 - δ) / A) (1 - (1 / 3 - rep θ.1 + δ) / A) T := by
    refine isSwing_of_abs_shift_sub_le hR hA hδ
      (σ := fun t => clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 (deviceRay Ψ₀ hΨ) t)
      (fun t _ _ => clockSiteFlow_clock_pointer J μ₀ μ₁ g₁ g₂ k hf hh hc hch t _ θ ψ)
      (fun t ht htT => ?_) h₁ h₂ h₃ h₄
    rw [hAe, hδe]
    exact abs_clockSiteShiftFst_sub_swing_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 hΨ hR hdrift ht htT
  exact IsSwing.preimage (π := Prod.fst)
    (γ := fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t
      ((clockArenaEquiv M (deviceRay Ψ₀ hΨ), θ), ψ)) key

/-- ★★ **On a fibre where the detector's profile vanishes, every swing of #358 is a swing of
the joint flow**, with the same rate, thresholds and horizon and no added error: there the joint
flow moves the clock's part of the state by `clockPointerFlow` exactly. -/
theorem isSwing_clockSiteFlow_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (x : CPN (4 * M + 3 + 1)) (θ : KTorus) {ψ : KTorus} (hz : hh.lift ψ.2 = 0) {R c d T : ℝ}
    (hs : IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g₁ hf hc t (x, θ)) R c d T) :
    IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)) R c d T := by
  have e : (fun t => (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)).1)
      = fun t => clockPointerFlow M J μ₀ μ₁ g₁ hf hc t (x, θ) :=
    funext fun t => clockSiteFlow_fst_of_lift_eq_zero J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x θ hz
  have key : IsSwing (tickReady M) (tickDisplay M)
      (fun t => (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)).1) R c d T := by
    rw [e]
    exact hs
  exact IsSwing.preimage (π := Prod.fst)
    (γ := fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)) key

/-! ### The tick record on the two-pointer arena -/

/-- ★★★ **Tick `n` as an actual occurrence of the joint flow.** Given that the clock pointer's
history from `x₀` under `clockSiteFlow` is a swing: the `evolve` is `clockSiteFlow` over the
elapsed time, the readout is `echoTickShown`, the preparation is `x₀` carried to the start of
turn `n`, where the clock's pointer is at rest, and the write is the tick of #358
(`IsSwing.isRecordWrite`). The swing is a hypothesis: `isSwing_clockSiteFlow` and
`isSwing_clockSiteFlow_of_lift_eq_zero` supply it. The record is held for less than a turn. -/
noncomputable def clockSiteTickRecord (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {x₀ : EchoSigma (4 * M + 3)} {R c d T : ℝ}
    (hs : IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀) R c d T)
    (n : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hn : ((n : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) :
    ActualOccurrence (EchoSigma (4 * M + 3)) Bool (M + 1) where
  evolve := clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  evolve_self := clockSiteEvolve_self J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  evolve_comp := clockSiteEvolve_comp J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  measurable_evolve := measurable_clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch
  readout := echoTickShown M
  measurable_readout := measurable_echoTickShown M
  ready := echoTickReady M
  measurableSet_ready := measurableSet_echoTickReady M
  prep := clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch ((n : ℝ) * (2 * Real.pi) / R) x₀
  prep_mem := hs.mem_rest_turn n ((div_le_div_of_nonneg_right
    (by linarith [Real.arccos_le_pi d', Real.pi_pos]) hs.rate_pos.le).trans hn)
  site := Finset.univ
  start := (n : ℝ) * (2 * Real.pi) / R
  value := true
  writeStart := ((n : ℝ) * (2 * Real.pi) + Real.arccos c) / R
  writeEnd := ((n : ℝ) * (2 * Real.pi) + Real.arccos d') / R
  window := 2 * (Real.pi - Real.arccos d') / R
  isWrite := hs.isRecordWrite (fun t => by
    show echoTickShown M (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch
        (t - (n : ℝ) * (2 * Real.pi) / R)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch ((n : ℝ) * (2 * Real.pi) / R) x₀)) = true
      ↔ clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀ ∈ echoTickDisplay M
    rw [← clockSiteFlow_add J μ₀ μ₁ g₁ g₂ k hf hh hc hch, sub_add_cancel]
    exact echoTickShown_eq_true_iff M _) n hd'1 hd' hn

/-- The tick record's history is the tick readout along the joint flow from `x₀`. -/
theorem clockSiteTickRecord_history (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {x₀ : EchoSigma (4 * M + 3)} {R c d T : ℝ}
    (hs : IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀) R c d T)
    (n : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hn : ((n : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) (t : ℝ) :
    (clockSiteTickRecord J μ₀ μ₁ g₁ g₂ k hf hh hc hch hs n hd'1 hd' hn).history t
      = echoTickShown M (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀) := by
  show echoTickShown M (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch
      (t - (n : ℝ) * (2 * Real.pi) / R)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch ((n : ℝ) * (2 * Real.pi) / R) x₀))
    = echoTickShown M (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀)
  rw [← clockSiteFlow_add J μ₀ μ₁ g₁ g₂ k hf hh hc hch, sub_add_cancel]

/-- ★ **One run: the same propagator.** The tick record evolves by `clockSiteEvolve`, as the
position record does (`clockSitePositionRecord_evolve`). -/
theorem clockSiteTickRecord_evolve (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {x₀ : EchoSigma (4 * M + 3)} {R c d T : ℝ}
    (hs : IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀) R c d T)
    (n : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hn : ((n : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) :
    (clockSiteTickRecord J μ₀ μ₁ g₁ g₂ k hf hh hc hch hs n hd'1 hd' hn).evolve
      = clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch :=
  rfl

/-- ★ **One run: the same start.** The tick record's preparation is `x₀`, the state the
position record is prepared in, carried by the one propagator from time `0` to the start of
turn `n`. -/
theorem clockSiteTickRecord_prep (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {x₀ : EchoSigma (4 * M + 3)} {R c d T : ℝ}
    (hs : IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x₀) R c d T)
    (n : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hn : ((n : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) :
    (clockSiteTickRecord J μ₀ μ₁ g₁ g₂ k hf hh hc hch hs n hd'1 hd' hn).prep
      = clockSiteEvolve J μ₀ μ₁ g₁ g₂ k hf hh hc hch 0 ((n : ℝ) * (2 * Real.pi) / R) x₀ := by
  show clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch ((n : ℝ) * (2 * Real.pi) / R) x₀
    = clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch ((n : ℝ) * (2 * Real.pi) / R - 0) x₀
  rw [sub_zero]

/-! ### One momentum mode on the fibres where both profiles vanish -/

/-- On the fibres where both profiles vanish the carrier moves freely, so a packet of the device
is carried to the packet at the later time. -/
theorem arenaKick_clockSiteCarrierU_devicePacket {φ χ : AddCircle (1 : ℝ)}
    (hz1 : hf.lift φ = 0) (hz2 : hh.lift χ = 0) (W : Finset ℤ) (β : ℤ → ℂ) (τ s : ℝ)
    (hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β τ ≠ 0)
    (hΨ' : devicePacket (L := M + 1) J μ₀ μ₁ W β (τ + s) ≠ 0) :
    arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s)
        (deviceRay (devicePacket J μ₀ μ₁ W β τ) hΨ)
      = deviceRay (devicePacket J μ₀ μ₁ W β (τ + s)) hΨ' := by
  unfold deviceRay
  rw [clockSiteCarrierU, idxTwoCarrierU_of_snd_lift_eq_zero _ _ _ hf hh φ hz2,
    idxCarrierU_of_lift_eq_zero _ _ hf hz1, arenaKick_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul]
  ext x
  rw [toEuclideanLin_coord, idxFreeU_deviceHam_val]
  exact (congrFun (deviceProp_devicePacket_shift J μ₀ μ₁ W β τ s) x).symm

/-- ★★ **The site pointer's displacement for one momentum mode**, on the fibres where both
profiles vanish: the rate times `t/(M+1)`, exactly, for every site `k`. -/
theorem clockSiteShiftSnd_single {φ χ : AddCircle (1 : ℝ)} (hz1 : hf.lift φ = 0)
    (hz2 : hh.lift χ = 0) (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0)
    (τ t : ℝ) :
    clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ
        (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β τ)
          (devicePacket_single_ne_zero h0 h1 m hβ τ)) t
      = rateAt g₂ 1 hh χ * (t / ((M : ℝ) + 1)) := by
  rw [clockSiteShiftSnd_eq_rateAt]
  have hI : ∀ s : ℝ, arenaObs (deviceSiteProj k)
      (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s)
        (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β τ)
          (devicePacket_single_ne_zero h0 h1 m hβ τ))) = 1 / ((M : ℝ) + 1) := fun s => by
    rw [arenaKick_clockSiteCarrierU_devicePacket J μ₀ μ₁ g₁ g₂ k hf hh hz1 hz2 {m} β τ s _
      (devicePacket_single_ne_zero h0 h1 m hβ (τ + s))]
    exact arenaObs_deviceSiteProj_single h0 h1 m hβ k (τ + s)
  simp only [hI]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div]

/-- ★★★ **The position write for one momentum mode**, on the fibres where both profiles
vanish, with the site pointer's rate `κ > 0`, from a ready site pointer: the readout history
writes `true` between the flow times `(M+1)/(6κ)` and `(M+1)/(3κ)` and holds it for
`(M+1)/(3κ)`. Exact, and the same for every site `k`. -/
theorem isRecordWrite_clockSiteFlow_site_single (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hψ : ψ ∈ readyArc 2) (hz1 : hf.lift θ.2 = 0) (hz2 : hh.lift ψ.2 = 0)
    {κ : ℝ} (hκe : κ = rateAt g₂ 1 hh ψ.2) (hκ : 0 < κ) (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ℤ)
    {β : ℤ → ℂ} (hβ : β m ≠ 0) (τ : ℝ) :
    IsRecordWrite
      (fun t => echoSiteShown (4 * M + 3) (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t
        ((clockArenaEquiv M (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β τ)
          (devicePacket_single_ne_zero h0 h1 m hβ τ)), θ), ψ)))
      0 (((M : ℝ) + 1) / (6 * κ)) (((M : ℝ) + 1) / (3 * κ)) (((M : ℝ) + 1) / (3 * κ))
      true := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hM0 : ((M : ℝ) + 1) ≠ 0 := hM.ne'
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hMκ := mul_pos hM hκ
  have hs : ∀ t : ℝ, clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2
      (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β τ)
        (devicePacket_single_ne_zero h0 h1 m hβ τ)) t = κ * (t / ((M : ℝ) + 1)) := fun t => by
    rw [hκe]
    exact clockSiteShiftSnd_single J μ₀ μ₁ g₁ g₂ k hf hh hz1 hz2 h0 h1 m hβ τ t
  have v₀ : κ * (((M : ℝ) + 1) / (6 * κ) / ((M : ℝ) + 1)) = 1 / 6 := by
    field_simp
  have v₁ : κ * (((M : ℝ) + 1) / (3 * κ) / ((M : ℝ) + 1)) = 1 / 3 := by
    field_simp
  have v₂ : κ * (2 * ((M : ℝ) + 1) / (3 * κ) / ((M : ℝ) + 1)) = 2 / 3 := by
    field_simp
  have key := isRecordWrite_clockSiteFlow_site J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ
    (by rw [← hκe]; exact hκ.le) (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β τ)
      (devicePacket_single_ne_zero h0 h1 m hβ τ))
    (τ₀ := ((M : ℝ) + 1) / (6 * κ)) (τ₁ := ((M : ℝ) + 1) / (3 * κ))
    (τ₂ := 2 * ((M : ℝ) + 1) / (3 * κ)) (by positivity)
    (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    (by rw [hs, v₀]) (by rw [hs, v₁]) (by rw [hs, v₂])
  have e : 2 * ((M : ℝ) + 1) / (3 * κ) - ((M : ℝ) + 1) / (3 * κ) = ((M : ℝ) + 1) / (3 * κ) := by
    ring
  rw [e] at key
  exact key

end Flow

/-! ### An exact instance: one mode, both profiles `trainF` -/

section Train

variable {M : ℕ}

/-- **The start state of the exact instance**: the device in one momentum mode `m`, prepared a
quarter turn of the level splitting `R` ahead; both pointers at the angle `1/12` on the fibres
`θ₂ = 0` and `ψ₂ = 0`. -/
noncomputable def clockSiteTrainStart (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ℤ)
    {β : ℤ → ℂ} (hβ : β m ≠ 0) (R : ℝ) : EchoSigma (4 * M + 3) :=
  ((clockArenaEquiv M (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β
      (-(Real.pi / (2 * R)))) (devicePacket_single_ne_zero h0 h1 m hβ _)),
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))),
   ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

/-- ★★ **The clock's pointer in the exact instance is a swing of the joint flow** at the level
splitting `R`, for every horizon and every coupling `g₂` of the site detector: the swing of
`isSwing_clockPointerFlow_train`, carried over on the fibre `ψ₂ = 0` where the detector's
profile vanishes. It displays exactly while `cos R t < 0`. -/
theorem isSwing_clockSiteFlow_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (k : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g₁ : ℝ}
    (hg : g₁ = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re)) (g₂ T : ℝ) :
    IsSwing (echoTickReady M) (echoTickDisplay M)
      (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
        contDiff_trainF t (clockSiteTrainStart J h0 (h0.trans h01) m hβ R))
      R 0 0 T := by
  unfold clockSiteTrainStart
  exact isSwing_clockSiteFlow_of_lift_eq_zero J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic
    contDiff_trainF contDiff_trainF _ _ trainF_lift_zero
    (isSwing_clockPointerFlow_train J h0 h01 h10 m hβ hRe hg T)

/-- ★★ **The position write in the exact instance**: with `g₂ > 0` the site pointer's rate on
the fibre `ψ₂ = 0` is `2 g₂`, and its readout history writes `true` between the flow times
`(M+1)/(12 g₂)` and `(M+1)/(6 g₂)` and holds it for `(M+1)/(6 g₂)`. The same for every
site. -/
theorem isRecordWrite_clockSiteFlow_site_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀)
    (h1 : 0 < μ₁) (k : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) (R g₁ : ℝ) {g₂ : ℝ}
    (hg₂ : 0 < g₂) :
    IsRecordWrite
      (fun t => echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
          contDiff_trainF t (clockSiteTrainStart J h0 h1 m hβ R)))
      0 (((M : ℝ) + 1) / (12 * g₂)) (((M : ℝ) + 1) / (6 * g₂)) (((M : ℝ) + 1) / (6 * g₂))
      true := by
  unfold clockSiteTrainStart
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hψ : (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) : KTorus)
      ∈ readyArc 2 := by
    show rep (((1 / 12 : ℝ) : CircleFibre)) ∈ Ioc (0 : ℝ) (shearWidth 2)
    rw [hrep, shearWidth_two]
    constructor <;> norm_num
  have key := isRecordWrite_clockSiteFlow_site_single J μ₀ μ₁ g₁ g₂ k trainF_periodic
    trainF_periodic contDiff_trainF contDiff_trainF
    (θ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) hψ trainF_lift_zero
    trainF_lift_zero (κ := 2 * g₂) (rateAt_trainF_zero g₂).symm (by positivity) h0 h1 m hβ
    (-(Real.pi / (2 * R)))
  have e0 : ((M : ℝ) + 1) / (6 * (2 * g₂)) = ((M : ℝ) + 1) / (12 * g₂) := by ring
  have e1 : ((M : ℝ) + 1) / (3 * (2 * g₂)) = ((M : ℝ) + 1) / (6 * g₂) := by ring
  rw [e0, e1] at key
  exact key

/-- ★★★ **A tick record and a position record in one run.** One start state
(`clockSiteTrainStart`), one flow (`clockSiteFlow`), two readouts. For every tick index `n` the
tick readout's history is a write of `true` begun at the turn's quarter and held while
`cos R t ≤ d'`, and the site readout's history is a write of `true` begun at `(M+1)/(12 g₂)`
and held for `(M+1)/(6 g₂)`. Exact, for one momentum mode, on the fibres where both profiles
vanish; all times are flow times. -/
theorem clockSite_records_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (k : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g₁ : ℝ}
    (hg : g₁ = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re)) {g₂ : ℝ}
    (hg₂ : 0 < g₂) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < 0) (n : ℕ) :
    IsRecordWrite
        (fun t => echoTickShown M
          (clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
            contDiff_trainF t (clockSiteTrainStart J h0 (h0.trans h01) m hβ R)))
        ((n : ℝ) * (2 * Real.pi) / R) (((n : ℝ) * (2 * Real.pi) + Real.arccos 0) / R)
        (((n : ℝ) * (2 * Real.pi) + Real.arccos d') / R) (2 * (Real.pi - Real.arccos d') / R)
        true
      ∧ IsRecordWrite
        (fun t => echoSiteShown (4 * M + 3)
          (clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
            contDiff_trainF t (clockSiteTrainStart J h0 (h0.trans h01) m hβ R)))
        0 (((M : ℝ) + 1) / (12 * g₂)) (((M : ℝ) + 1) / (6 * g₂)) (((M : ℝ) + 1) / (6 * g₂))
        true :=
  ⟨(isSwing_clockSiteFlow_train J h0 h01 h10 k m hβ hRe hg g₂
      (((n : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R)).isRecordWrite
      (fun _ => echoTickShown_eq_true_iff M _) n hd'1 hd' le_rfl,
    isRecordWrite_clockSiteFlow_site_train J h0 (h0.trans h01) k m hβ R g₁ hg₂⟩

end Train

end CSD.RecordLayer

end
