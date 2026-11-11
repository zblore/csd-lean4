/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.TriCoupledFlow
public import CsdLean4.RecordLayer.UnifiedCountAtWrite

/-!
# A clock and two site detectors under one flow

**Category:** 7-SigmaLayer (the record layer). BACKLOG #369 — the author's programme "From `Σ` to
physical spacetime", towards milestone M6; Remainder (a) of #368. `LF4/TriCoupledFlow.lean` built
the arena with three pointer tori and put nothing on it. This module couples the three tori to
the two-level device of #357: the first to the exchange of its levels (the clock's pointer), the
second and third to the occupancies of two sites (two detectors). It reads a record on each, in
one run, and takes the clock's count at each detector's record.

**The arena.** `clockTwoSiteFlow` is the flow, on `ℂℙ^{4M+3} × T² × T² × T²`, of

  `−2⟨H_dev⟩ − 2 g₁ f(θ₂)⟨X⟩ − 2 g₂ h(ψ₂)⟨Q_{k₂}⟩ − 2 g₃ k(χ₂)⟨Q_{k₃}⟩`.

It is a one-parameter group and preserves `triMuL` (`clockTwoSiteFlow_add`,
`triMuL_map_clockTwoSiteFlow`). On a fibre where the third profile vanishes, the device, the
clock's pointer and the first detector move exactly by `clockSiteFlow` of #359
(`clockTwoSiteFlow_fst_of_lift_eq_zero`), and the third pointer is turned by its rate times the
accumulated occupancy of its site along that orbit
(`clockTwoSiteFlow_thd_pointer_of_lift_eq_zero`). The third torus has the readout `triThdShown`
and the ready and displayed arcs of the other two (apparatus input, UA-4).

**Three readout histories in one run** (`clockTwoSite_records_train`). The start is that of #360
with a third ready pointer: the device in one momentum mode, the three pointers at `1/12`, all three
profiles `trainF`, the three conserved angles `0`, `g₂, g₃ > 0`, with `μ₀ < μ₁ < 2μ₀`, `R` the
mode's level splitting and the clock strength `g₁` fixed as in #360. Along the one orbit:

* the clock's pointer is a swing at the level splitting `R` on every horizon
  (`isSwing_clockTwoSiteFlow_train`), so by `IsSwing.isRecordWrite` (#358) each tick is a record
  write, and by `IsSwing.exists_tickCount` it has a count at every flow time `T ≥ 0`;
* the first detector's readout is `true` exactly after `t₂ = (M+1)/(8 g₂)`, on `0 ≤ t ≤ 3 t₂`
  (`echoSiteShown_clockTwoSiteFlow_train_iff`);
* the second detector's readout is `true` exactly after `t₃ = (M+1)/(8 g₃)`, on `0 ≤ t ≤ 3 t₃`
  (`triThdShown_clockTwoSiteFlow_train_iff`); nothing is stated later, and the two windows need
  not overlap;
* the tick history has counts `N₂` at `t₂` and `N₃` at `t₃`, each within one tick period
  `2π/R` of its time, and the interval between the two records read in ticks,
  `(N₃ − N₂) · 2π/R`, is within two periods of `t₃ − t₂`.

## Exact scope

* **No signal travels.** The carrier is one momentum mode, spread evenly over the ring. Each
  detector's pointer turns at its own rate, and the two records are separated in time because
  the strengths `g₂`, `g₃` differ, not because the sites are apart. The interval read in ticks
  is `(M+1)(1/g₃ − 1/g₂)/8` up to two ticks. It is not a transit time, and no distance or speed
  is read off it. A travelling packet with a clock in the same run is not here (see below).
* **A null set of fibres.** The instance is on the fibres where all three profiles vanish, where
  the device moves freely and drives the three pointers. Off them only the reduction to
  `clockSiteFlow` on the fibres of the third profile's zeros is proved.
* **The counts are taken at flow times.** Each count is the count of the tick history up to the
  flow time at which a detector's readout switches (UA-7). No degree of freedom holds a count.
* **"Record" here means a readout's switching instant**: `false` on `[0, t_i]`, `true` on
  `(t_i, 3 t_i]`. No `IsRecordWrite` or `ActualOccurrence` with propagator `clockTwoSiteFlow` is
  constructed, and no lemma places the start in `triThdReady`. The clock's ticks are records by
  `IsSwing.isRecordWrite` (#358) applied to this swing, which is not instantiated here.
* **The clock is the carrier's own.** The clock's pointer is coupled to the level swap of the
  device, and the device is the one particle on the ring. If that carrier travelled, its count
  between two detections would be the messenger's own tick count, not an observer's clock
  reading at emission and reception.
* **What is still missing for a one-way signal in this arena:** the clock's swing for a
  travelling packet in place of one mode (UO-14 (a)); the crossing bounds of #265 for the
  two-level device, whose levels have different rest energies and so different speeds; and
  with them the records of #367 with the clock's count at each. A radar exchange needs more:
  see UO-16 in the contract.
* **Definite facts, not statistics.** No weight of quantum mechanics is derived.
* **All times are flow times** (UA-7).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UA-15, UO-14, UO-16, UD-97, UD-98); `LF4/TriCoupledFlow.lean`
(`threeCoupledFlow`, `threeCoupledFlow_apply`, `triMuL_map_threeCoupledFlow`);
`RecordLayer/UnifiedTwoPointer.lean` (`clockSiteFlow`, `clockSiteFlow_apply`,
`clockSiteCarrierU`); `RecordLayer/UnifiedClockSiteRecords.lean` (`clockSiteTrainStart`,
`isSwing_clockSiteFlow_train`, `arenaKick_clockSiteCarrierU_devicePacket`,
`arenaObs_deviceSiteProj_single`, `IsSwing.preimage`); `RecordLayer/UnifiedCountAtWrite.lean`
(`echoSiteShown_clockSiteFlow_train_iff`, `IsSwing.abs_tickTime_sub_le`,
`IsSwing.abs_tickTime_sub_sub_le`); `RecordLayer/UnifiedDiracClock.lean`
(`schrodingerHamiltonian_reindex`, `clockArenaEquiv`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The third torus's readout, and the slice of the three-torus flow -/

section Readout

variable (N : ℕ)

/-- **The third pointer's ready region**: `χ₁` in the arc `(0, 1/6]`. Apparatus input. -/
noncomputable def triThdReady : Set (TriSigma N) := {x | x.2 ∈ readyArc 2}

theorem measurableSet_triThdReady : MeasurableSet (triThdReady N) :=
  measurable_snd (measurableSet_readyArc (K := 2))

/-- **The third pointer's displayed region**: `χ₁` in the arc `(1/3, 5/6]`. Apparatus input. -/
noncomputable def triThdDisplay : Set (TriSigma N) := {x | x.2 ∈ displayArc}

theorem measurableSet_triThdDisplay : MeasurableSet (triThdDisplay N) :=
  measurable_snd measurableSet_displayArc

open Classical in
/-- **The third pointer's readout**: is `χ₁` in the displayed arc? -/
noncomputable def triThdShown (x : TriSigma N) : Bool :=
  if x.2 ∈ displayArc then true else false

theorem measurable_triThdShown : Measurable (triThdShown N) := by
  unfold triThdShown
  exact Measurable.ite (measurable_snd measurableSet_displayArc) measurable_const
    measurable_const

theorem triThdShown_eq_true_iff (x : TriSigma N) :
    triThdShown N x = true ↔ x ∈ triThdDisplay N := by
  unfold triThdShown triThdDisplay
  simp

end Readout

section Slice

variable {N : ℕ} {f g k : ℝ → ℝ} (A BA BB BC : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
  (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)

/-- ★★ **On a fibre where the third profile vanishes the first two pointers move as on the
two-pointer arena.** -/
theorem threeCoupledFlow_fst_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (q : EchoSigma N) {χ : KTorus} (hz : hk.lift χ.2 = 0) :
    (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (q, χ)).1
      = twoCoupledFlow A BA BB hf hg hc hcg t q := by
  rw [threeCoupledFlow_apply]
  simp only [hz, Complex.ofReal_zero, zero_smul, add_zero]

/-- **The third pointer on a fibre where its profile vanishes**: turned by `k'(χ₂)` times the
accumulated `−2⟨B_C⟩` along the two-pointer orbit. -/
theorem threeCoupledFlow_snd_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (q : EchoSigma N) {χ : KTorus} (hz : hk.lift χ.2 = 0) :
    (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (q, χ)).2
      = pshift (hk.deriv_periodic.lift χ.2 * ∫ u in (0 : ℝ)..t,
          schrodingerHamiltonian BC (twoCoupledFlow A BA BB hf hg hc hcg u q).1.1) χ := by
  rw [threeCoupledFlow_apply]
  simp only [hz, Complex.ofReal_zero, zero_smul, add_zero]
  rfl

end Slice

/-! ### The arena: the device, the clock's pointer and two site detectors -/

section Arena

variable {M : ℕ} {f h k : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ g₃ : ℝ) (k₂ k₃ : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)

/-- **The joint flow of the two-level device, the clock's pointer and two site pointers**: the
flow, for the form of `ℂℙ^{4M+3} × T² × T² × T²`, of
`−2⟨H_dev⟩ − 2 g₁ f(θ₂)⟨X⟩ − 2 g₂ h(ψ₂)⟨Q_{k₂}⟩ − 2 g₃ k(χ₂)⟨Q_{k₃}⟩`. -/
noncomputable def clockTwoSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) : TriSigma (4 * M + 3) → TriSigma (4 * M + 3) :=
  threeCoupledFlow (Matrix.reindex (clockIdx M) (clockIdx M) (deviceHam J μ₀ μ₁))
    (Matrix.reindex (clockIdx M) (clockIdx M) (clockB M g₁))
    (Matrix.reindex (clockIdx M) (clockIdx M) ((g₂ : ℂ) • deviceSiteProj k₂))
    (Matrix.reindex (clockIdx M) (clockIdx M) ((g₃ : ℂ) • deviceSiteProj k₃)) hf hh hk hc hch
    hck t

theorem clockTwoSiteFlow_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (x : TriSigma (4 * M + 3)) :
    clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck 0 x = x :=
  threeCoupledFlow_zero _ _ _ _ hf hh hk hc hch hck x

/-- The flow is a one-parameter group. -/
theorem clockTwoSiteFlow_add (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (s t : ℝ) (x : TriSigma (4 * M + 3)) :
    clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck (s + t) x
      = clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck s
          (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck t x) :=
  threeCoupledFlow_add _ _ _ _ hf hh hk hc hch hck s t x

/-- ★★ **The joint flow preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²} ⊗ vol_{T²}`.** -/
theorem triMuL_map_clockTwoSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (p₀ : CPN (4 * M + 3 + 1)) (t : ℝ) :
    Measure.map (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck t) (triMuL p₀)
      = triMuL p₀ :=
  triMuL_map_threeCoupledFlow ((deviceHam_isHermitian J μ₀ μ₁).reindex (clockIdx M))
    ((clockB_isHermitian g₁).reindex (clockIdx M))
    ((deviceSiteProj_smul_isHermitian g₂ k₂).reindex (clockIdx M))
    ((deviceSiteProj_smul_isHermitian g₃ k₃).reindex (clockIdx M)) hf hh hk hc hch hck p₀ t

/-- ★★ **On a fibre where the third profile vanishes, the device, the clock's pointer and the
first detector move exactly by `clockSiteFlow`.** -/
theorem clockTwoSiteFlow_fst_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (q : EchoSigma (4 * M + 3)) {χ : KTorus}
    (hz : hk.lift χ.2 = 0) :
    (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck t (q, χ)).1
      = clockSiteFlow J μ₀ μ₁ g₁ g₂ k₂ hf hh hc hch t q :=
  threeCoupledFlow_fst_of_lift_eq_zero _ _ _ _ hf hh hk hc hch hck t q hz

/-- ★★ **The third pointer on a fibre where its profile vanishes**: turned by its rate times the
accumulated occupancy of its site along the orbit of `clockSiteFlow`. -/
theorem clockTwoSiteFlow_thd_pointer_of_lift_eq_zero (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (hck : ContDiff ℝ ∞ k) (t : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) {χ : KTorus}
    (hz : hk.lift χ.2 = 0) :
    (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ hf hh hk hc hch hck t
        (((clockArenaEquiv M p, θ), ψ), χ)).2
      = pshift (rateAt g₃ 1 hk χ.2 * ∫ u in (0 : ℝ)..t, arenaObs (deviceSiteProj k₃)
          (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k₂ hf hh θ.2 ψ.2 u) p)) χ := by
  have hint : ∀ u : ℝ,
      schrodingerHamiltonian
          (Matrix.reindex (clockIdx M) (clockIdx M) ((g₃ : ℂ) • deviceSiteProj k₃))
          (twoCoupledFlow (Matrix.reindex (clockIdx M) (clockIdx M) (deviceHam J μ₀ μ₁))
            (Matrix.reindex (clockIdx M) (clockIdx M) (clockB M g₁))
            (Matrix.reindex (clockIdx M) (clockIdx M) ((g₂ : ℂ) • deviceSiteProj k₂)) hf hh hc
            hch u ((clockArenaEquiv M p, θ), ψ)).1.1
        = -2 * (g₃ * arenaObs (deviceSiteProj k₃)
            (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k₂ hf hh θ.2 ψ.2 u) p)) := by
    intro u
    have hflow := clockSiteFlow_apply J μ₀ μ₁ g₁ g₂ k₂ hf hh hc hch u p θ ψ
    have h1 : (twoCoupledFlow (Matrix.reindex (clockIdx M) (clockIdx M) (deviceHam J μ₀ μ₁))
          (Matrix.reindex (clockIdx M) (clockIdx M) (clockB M g₁))
          (Matrix.reindex (clockIdx M) (clockIdx M) ((g₂ : ℂ) • deviceSiteProj k₂)) hf hh hc
          hch u ((clockArenaEquiv M p, θ), ψ)).1.1
        = clockArenaEquiv M
            (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k₂ hf hh θ.2 ψ.2 u) p) :=
      congrArg (fun z : EchoSigma (4 * M + 3) => z.1.1) hflow
    rw [h1]
    exact (schrodingerHamiltonian_reindex (clockIdx M) _ _).trans
      (by rw [arenaObs_real_smul])
  rw [clockTwoSiteFlow, threeCoupledFlow_snd_of_lift_eq_zero _ _ _ _ hf hh hk hc hch hck t _ hz]
  simp only [hint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, rateAt, div_one]
  congr 1
  ring

end Arena

/-! ### Three records in one run -/

section Train

variable {M : ℕ}

/-- A pointer at `1/12`, turned by `t c` with `c > 0`, is in the displayed arc exactly after
`1/(4c)`, for `0 ≤ t ≤ 3/(4c)`. -/
theorem pshift_twelfth_mem_displayArc_iff {c t : ℝ} (hc : 0 < c) (ht0 : 0 ≤ t)
    (ht : t ≤ 3 / 4 / c) :
    pshift (t * c) (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) : KTorus)
        ∈ displayArc ↔ 1 / 4 / c < t := by
  rw [le_div_iff₀ hc] at ht
  rw [div_lt_iff₀ hc]
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hnn : 0 ≤ t * c := mul_nonneg ht0 hc.le
  have key := pshift_mem_displayArc_iff
    (q := (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) : KTorus)) (a := t * c)
    (by show 0 < rep (((1 / 12 : ℝ) : CircleFibre)) + _; rw [hrep]; linarith)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ 5 / 6; rw [hrep]; linarith)
  rw [key]
  show 1 / 3 < rep (((1 / 12 : ℝ) : CircleFibre)) + _ ↔ _
  rw [hrep]
  constructor <;> intro h <;> linarith

/-- **The start state of the three-record run**: the start of #360 with a third pointer at the
angle `1/12` on the fibre `χ₂ = 0`. -/
noncomputable def clockTwoSiteTrainStart (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁)
    (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) (R : ℝ) : TriSigma (4 * M + 3) :=
  (clockSiteTrainStart J h0 h1 m hβ R,
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

/-- Along the three-record run the device, the clock's pointer and the first detector move by
the orbit of #360. -/
theorem clockTwoSiteFlow_train_fst (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁)
    (k₂ k₃ : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) (R g₁ g₂ g₃ t : ℝ) :
    (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic trainF_periodic
        contDiff_trainF contDiff_trainF contDiff_trainF t
        (clockTwoSiteTrainStart J h0 h1 m hβ R)).1
      = clockSiteFlow J μ₀ μ₁ g₁ g₂ k₂ trainF_periodic trainF_periodic contDiff_trainF
          contDiff_trainF t (clockSiteTrainStart J h0 h1 m hβ R) :=
  clockTwoSiteFlow_fst_of_lift_eq_zero J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
    trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t _ trainF_lift_zero

/-- ★★ **The clock's pointer is a swing along the three-record run**, at the level splitting
`R`, on every horizon and for every strength of the two detectors. -/
theorem isSwing_clockTwoSiteFlow_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (k₂ k₃ : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g₁ : ℝ}
    (hg : g₁ = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re))
    (g₂ g₃ T : ℝ) :
    IsSwing (Prod.fst ⁻¹' echoTickReady M) (Prod.fst ⁻¹' echoTickDisplay M)
      (fun t => clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
        trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t
        (clockTwoSiteTrainStart J h0 (h0.trans h01) m hβ R))
      R 0 0 T := by
  refine IsSwing.preimage (π := Prod.fst) ?_
  have e : (fun t => (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
        trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t
        (clockTwoSiteTrainStart J h0 (h0.trans h01) m hβ R)).1)
      = fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k₂ trainF_periodic trainF_periodic contDiff_trainF
          contDiff_trainF t (clockSiteTrainStart J h0 (h0.trans h01) m hβ R) :=
    funext fun t => clockTwoSiteFlow_train_fst J h0 (h0.trans h01) k₂ k₃ m hβ R g₁ g₂ g₃ t
  rw [e]
  exact isSwing_clockSiteFlow_train J h0 h01 h10 k₂ m hβ hRe hg g₂ T

/-- ★★ **The first detector's readout along the three-record run** is `true` exactly after the
flow time `(M+1)/(8 g₂)`, up to `3 (M+1)/(8 g₂)`. -/
theorem echoSiteShown_clockTwoSiteFlow_train_iff (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀)
    (h1 : 0 < μ₁) (k₂ k₃ : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) (R g₁ g₃ : ℝ)
    {g₂ : ℝ} (hg₂ : 0 < g₂) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 * ((M : ℝ) + 1) / (8 * g₂)) :
    echoSiteShown (4 * M + 3)
        (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic trainF_periodic
          contDiff_trainF contDiff_trainF contDiff_trainF t
          (clockTwoSiteTrainStart J h0 h1 m hβ R)).1 = true
      ↔ ((M : ℝ) + 1) / (8 * g₂) < t := by
  rw [clockTwoSiteFlow_train_fst]
  exact echoSiteShown_clockSiteFlow_train_iff J h0 h1 k₂ m hβ R g₁ hg₂ ht0 ht

/-- ★★ **The second detector's readout along the three-record run** is `true` exactly after the
flow time `(M+1)/(8 g₃)`, up to `3 (M+1)/(8 g₃)`. -/
theorem triThdShown_clockTwoSiteFlow_train_iff (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀)
    (h1 : 0 < μ₁) (k₂ k₃ : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) (R g₁ g₂ : ℝ)
    {g₃ : ℝ} (hg₃ : 0 < g₃) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 * ((M : ℝ) + 1) / (8 * g₃)) :
    triThdShown (4 * M + 3)
        (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic trainF_periodic
          contDiff_trainF contDiff_trainF contDiff_trainF t
          (clockTwoSiteTrainStart J h0 h1 m hβ R)) = true
      ↔ ((M : ℝ) + 1) / (8 * g₃) < t := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hc : 0 < 2 * g₃ / ((M : ℝ) + 1) := by positivity
  have e₁ : ((M : ℝ) + 1) / (8 * g₃) = 1 / 4 / (2 * g₃ / ((M : ℝ) + 1)) := by
    field_simp
    ring
  have e₃ : 3 * ((M : ℝ) + 1) / (8 * g₃) = 3 / 4 / (2 * g₃ / ((M : ℝ) + 1)) := by
    field_simp
    ring
  rw [e₃] at ht
  rw [e₁, ← pshift_twelfth_mem_displayArc_iff hc ht0 ht, triThdShown_eq_true_iff]
  have hI : ∀ u : ℝ, arenaObs (deviceSiteProj k₃)
      (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k₂ trainF_periodic trainF_periodic
        (0 : AddCircle (1 : ℝ)) (0 : AddCircle (1 : ℝ)) u)
        (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
          (devicePacket_single_ne_zero h0 h1 m hβ _))) = 1 / ((M : ℝ) + 1) := fun u => by
    rw [arenaKick_clockSiteCarrierU_devicePacket J μ₀ μ₁ g₁ g₂ k₂ trainF_periodic
      trainF_periodic trainF_lift_zero trainF_lift_zero {m} β _ u _
      (devicePacket_single_ne_zero h0 h1 m hβ (-(Real.pi / (2 * R)) + u))]
    exact arenaObs_deviceSiteProj_single h0 h1 m hβ k₃ _
  unfold clockTwoSiteTrainStart clockSiteTrainStart
  show (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic trainF_periodic
    contDiff_trainF contDiff_trainF contDiff_trainF t _).2 ∈ displayArc ↔ _
  rw [clockTwoSiteFlow_thd_pointer_of_lift_eq_zero J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic
    trainF_periodic trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t _ _ _
    trainF_lift_zero]
  simp only [hI]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, rateAt_trainF_zero]
  have e : 2 * g₃ * (t * (1 / ((M : ℝ) + 1))) = t * (2 * g₃ / ((M : ℝ) + 1)) := by ring
  rw [e]

/-- ★★★ **A clock record and two detector records in one run, with the clock's count at each.**
From `clockTwoSiteTrainStart`, along the one orbit of `clockTwoSiteFlow`, with `g₂, g₃ > 0`: the
first detector's readout switches to `true` at the flow time `t₂ = (M+1)/(8 g₂)` and the second
detector's at `t₃ = (M+1)/(8 g₃)`; the clock's tick history has counts `N₂` at `t₂` and `N₃` at
`t₃`, each within one tick period `2π/R` of its time; and the interval between the two records
read in ticks, `(N₃ − N₂) · 2π/R`, is within two periods of `t₃ − t₂`. The counts are taken at
flow times (UA-7). The carrier is one momentum mode: no signal travels between the sites. -/
theorem clockTwoSite_records_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (k₂ k₃ : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g₁ : ℝ}
    (hg : g₁ = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re))
    {g₂ g₃ : ℝ} (hg₂ : 0 < g₂) (hg₃ : 0 < g₃) :
    (∀ t, 0 ≤ t → t ≤ 3 * ((M : ℝ) + 1) / (8 * g₂) →
        (echoSiteShown (4 * M + 3)
            (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
              trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t
              (clockTwoSiteTrainStart J h0 (h0.trans h01) m hβ R)).1 = true
          ↔ ((M : ℝ) + 1) / (8 * g₂) < t))
      ∧ (∀ t, 0 ≤ t → t ≤ 3 * ((M : ℝ) + 1) / (8 * g₃) →
        (triThdShown (4 * M + 3)
            (clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
              trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t
              (clockTwoSiteTrainStart J h0 (h0.trans h01) m hβ R)) = true
          ↔ ((M : ℝ) + 1) / (8 * g₃) < t))
      ∧ ∃ N₂ N₃ : ℕ,
        IsTickCount (Prod.fst ⁻¹' echoTickReady M) (Prod.fst ⁻¹' echoTickDisplay M)
            (fun t => clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
              trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t
              (clockTwoSiteTrainStart J h0 (h0.trans h01) m hβ R))
            (((M : ℝ) + 1) / (8 * g₂)) N₂
          ∧ IsTickCount (Prod.fst ⁻¹' echoTickReady M) (Prod.fst ⁻¹' echoTickDisplay M)
            (fun t => clockTwoSiteFlow J μ₀ μ₁ g₁ g₂ g₃ k₂ k₃ trainF_periodic trainF_periodic
              trainF_periodic contDiff_trainF contDiff_trainF contDiff_trainF t
              (clockTwoSiteTrainStart J h0 (h0.trans h01) m hβ R))
            (((M : ℝ) + 1) / (8 * g₃)) N₃
          ∧ |(N₂ : ℝ) * (2 * Real.pi / R) - ((M : ℝ) + 1) / (8 * g₂)| ≤ 2 * Real.pi / R
          ∧ |(N₃ : ℝ) * (2 * Real.pi / R) - ((M : ℝ) + 1) / (8 * g₃)| ≤ 2 * Real.pi / R
          ∧ |((N₃ : ℝ) - N₂) * (2 * Real.pi / R)
              - (((M : ℝ) + 1) / (8 * g₃) - ((M : ℝ) + 1) / (8 * g₂))| ≤ 4 * Real.pi / R := by
  have hT₂ : (0 : ℝ) ≤ ((M : ℝ) + 1) / (8 * g₂) := by positivity
  have hT₃ : (0 : ℝ) ≤ ((M : ℝ) + 1) / (8 * g₃) := by positivity
  have s₂ := isSwing_clockTwoSiteFlow_train J h0 h01 h10 k₂ k₃ m hβ hRe hg g₂ g₃
    (((M : ℝ) + 1) / (8 * g₂))
  have s₃ := isSwing_clockTwoSiteFlow_train J h0 h01 h10 k₂ k₃ m hβ hRe hg g₂ g₃
    (((M : ℝ) + 1) / (8 * g₃))
  obtain ⟨N₂, hN₂⟩ := s₂.exists_tickCount hT₂
  obtain ⟨N₃, hN₃⟩ := s₃.exists_tickCount hT₃
  exact ⟨fun t ht0 ht => echoSiteShown_clockTwoSiteFlow_train_iff J h0 (h0.trans h01) k₂ k₃ m
      hβ R g₁ g₃ hg₂ ht0 ht,
    fun t ht0 ht => triThdShown_clockTwoSiteFlow_train_iff J h0 (h0.trans h01) k₂ k₃ m hβ R g₁
      g₂ hg₃ ht0 ht,
    N₂, N₃, hN₂, hN₃, s₂.abs_tickTime_sub_le hT₂ hN₂, s₃.abs_tickTime_sub_le hT₃ hN₃,
    s₂.abs_tickTime_sub_sub_le s₃ hT₂ hT₃ hN₂ hN₃⟩

end Train

end CSD.RecordLayer

end
