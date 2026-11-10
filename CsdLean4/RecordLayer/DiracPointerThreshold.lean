/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ActivatedWrite
public import CsdLean4.RecordLayer.DiracPointerWrite

/-!
# The pointer crossing an outcome threshold

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #352 — milestone **M2, part B** of the
author's programme "From `Σ` to physical spacetime" (2026-11-09): the second of the four statements
M2 keeps apart, *a pointer displacement crossing an outcome threshold*.

`RecordLayer/DiracPointerWrite.lean` (#351) bounded the displacement of the pointer of
`Σ_* = ℂℙ^{2M+1} × T²`. This module adds the two regions of the pointer circle that displacement is
read against — the ready arc `(0, 1/6]` of `RecordLayer/ShearWitness.lean` and the displayed arc
`(1/3, 5/6]` of `RecordLayer/ActivatedWrite.lean`, here as a set and a `Bool` on `Σ_*` — and proves
when `diracPointerFlow` takes the first into the second and when it does not.

Three cases are kept apart, by the conserved angle `θ₂` and by the carrier:

* on a **write fibre** a carrier prepared on the detector's site is displayed at the readout time
  `T`, and a carrier prepared on any other site is not, at any time up to `T`;
* on a **slow fibre** nothing is displayed up to `T`, whatever the carrier;
* on a fibre in neither set nothing is proved.

Both sets are open and they do not meet. The slow fibres have positive measure for every `C¹`
profile; the write fibres have positive measure for the profile `trainF`. The write is therefore not
universal, and no statement here says it is.

The estimate behind the first case is a short-time one. The coupled propagator is within `|t| ‖H‖`
of the identity (`Matrix.norm_exp_smul_neg_I_sub_le` against the zero matrix), so over a time short
on the scale `1/‖H‖` a carrier has neither left the site it started on nor reached another. The free
chain is not used as a comparison: the bound is on the carrier that feels the site potential, with
`‖H‖ ≤ ‖H_D‖ + |g f(θ₂)|`.

## The two arcs, and the regions on `Σ_*`

* `pshift_mem_displayArc` — a ready pointer turned by between `1/3` and `2/3` of a turn is in the
  displayed arc; `pshift_notMem_displayArc` — turned by less than `1/6` either way, it is not;
* `diracReady` — **the ready state** on `Σ_*` (`measurableSet_diracReady`,
  `mem_diracReady_congr`); `diracDisplayed` — **the readout** (`measurable_diracDisplayed`,
  `diracDisplayed_eq_true_iff`, `diracDisplayed_eq_false_iff`);
* ★ `diracDisplayed_congr` — **the readout is a function of the pointer angle `θ₁` alone.**

## The carrier over a short time

* `diracOccupancy_zero`; ★ `norm_diracCarrierU_sub_one_le` — the coupled propagator is within
  `|t| ‖H‖` of the identity; `norm_diracPointerH_le` — `‖H‖ ≤ ‖H_D‖ + |g f(θ₂)|`;
* ★ `abs_diracOccupancy_sub_zero_le`, ★★ `abs_integral_diracOccupancy_sub_mul_le` — the occupancy
  stays within `2 |s| ‖H‖` of its starting value, and its integral within `‖H‖ t²` of `t` times it.

## The displacement in terms of the rate `κ = −2 g f'(θ₂)`

* `rateAt_one`, `diracPointerShift_eq_rateAt` — the displacement is `rateAt g 1` times the
  accumulated occupancy; `diracPointerShift_nonneg`, `diracPointerShift_le_rateAt_mul`,
  `abs_diracPointerShift_le_rateAt`;
* ★★ `abs_diracPointerShift_sub_init_le` — **the displacement over a short time** is within
  `|κ| ‖H‖ t²` of `κ t` times the occupancy the carrier started with;
* ★★ `le_diracPointerShift_siteRay` — **the signal**: from the detector's site, at least
  `κ (t − ‖H‖ t²)`; ★★ `abs_diracPointerShift_siteRay_of_ne_le` — **the control**: from another
  site, at most `|κ| ‖H‖ t²`.

## The threshold, along the Hamiltonian flow

* `diracPointerFlow_snd` — the pointer pair of the flow is `pshift` by the displacement;
* ★★ `diracPointerFlow_displayed`, `diracPointerFlow_not_displayed` — **the two crossing
  criteria**, exact, in terms of the displacement;
* ★★★ `diracPointerFlow_siteRay_displayed` — **a carrier on the detector's site crosses**, when
  `1/3 ≤ κ (T − ‖H‖ T²)` and `κ T ≤ 2/3`;
* ★★★ `diracPointerFlow_siteRay_of_ne_not_displayed` — **a carrier on another site does not**, at
  any time up to `T`, when `|κ| ‖H‖ T² < 1/6`.

## The slow fibres and the write fibres

* `slowFibres` — `|κ(θ₂)| T < 1/6`; `isOpen_slowFibres`; ★★ `volume_slowFibres_pos` — **positive
  measure for every `C¹` profile and every horizon** (Rolle's zero of `f'`);
* ★★★ `diracPointerFlow_not_displayed_of_mem_slowFibres` — **on a slow fibre nothing is displayed
  up to `T`, whatever the carrier**;
* `writeFibres` — `κ > 0`, `1/3 < κ (T − h T²)`, `κ T < 2/3`, `κ h T² < 1/6` with
  `h = ‖H_D‖ + |g f(θ₂)|`; `isOpen_writeFibres`;
* ★★★ `diracPointerFlow_displayed_of_mem_writeFibres`,
  `diracPointerFlow_not_displayed_of_mem_writeFibres` — **on a write fibre the carrier on the
  detector's site is displayed at `T` and the carrier on another site is not, up to `T`**;
* `disjoint_writeFibres_slowFibres`;
* ★★ `zero_mem_writeFibres_trainF`, ★★★ `volume_writeFibres_trainF_pos` — **profile `trainF`,
  coupling `g = 1/(4T)`, any readout time with `‖H_D‖ T ≤ 1/4`: the write fibres contain `θ₂ = 0`
  and have positive measure**; `exists_volume_writeFibres_pos` — such `g` and `T` exist for every
  ring and every `J`, `μ`.

## Honest scope

* **Exact versus approximate.** The two crossing criteria are exact statements about the flow,
  given the size of the displacement. Everything that supplies the size is a bound, and the bound
  `‖H‖ t²` is the first-order estimate, not sharp. `writeFibres` is a set on which the write is
  *proved*, cut out by that bound. The set of fibres on which the carrier is in fact displayed at
  `T` contains it and is not determined here.
* **The signal carrier starts on the detector's site; it does not arrive.** The write here is
  complete in a time short on the scale `1/‖H‖`, before the carrier has moved. A packet with no
  weight at the detector that travels to it is not treated, here or in #351.
* **The control is bounded only up to `T`.** The chain carries a carrier that starts elsewhere to
  the detector's site, and the pointer then turns. Nothing is said about it after `T`.
* **Not universal.** On the slow fibres there is no write by `T`, for any carrier
  (`diracPointerFlow_not_displayed_of_mem_slowFibres`). The measures of the two sets are shown to
  be positive and are not computed. A fibre in neither set, and every fibre with a negative rate
  (the pointer turns the other way, and can enter the displayed arc from that side), is left
  without a statement.
* **A threshold, not a record.** No outcome is said to be selected, no `ActualOccurrence` is built,
  and the time the pointer stays in the displayed arc is not bounded. The signal theorems are
  statements at the one time `T`.
* **The regions are definitions.** The two arcs are apparatus parameters, chosen, and
  `diracDisplayed_congr` and `mem_diracReady_congr` check that they read the pointer angle alone.
  What is derived is that the flow carries one into the other.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1), the
  coupling `−2 g f(θ₂) ⟨P_j⟩` (UA-5) and the Dirac propagation law (UA-8) are the definitions every
  statement here is about. The ready arc, the displayed arc, the site, the profile, the coupling,
  the readout time, the carrier's initial ray and the fibre `θ₂` a statement holds on are
  preparation input (UA-4). Haar measure on the `θ₂` circle is used only to say that the two sets
  of fibres are not null: no law for `θ₂` is used, and no probability of a write is stated. Nothing
  here is a statement about Born weights, clocks or spacetime.

References: `specs/BACKLOG.md` #352, #351, #349, #350, #194; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UO-1, UO-3; UD-35 to UD-39);
`RecordLayer/DiracPointerWrite.lean` (`diracOccupancy`, `continuous_diracOccupancy`,
`integral_diracOccupancy_nonneg`, `integral_diracOccupancy_le`, `abs_arenaObs_arenaKick_sub_le`,
`norm_siteProj_le`); `RecordLayer/DiracPointerHamiltonian.lean` (`diracPointerFlow`,
`diracPointerFlow_apply`, `diracPointerShift`, `diracCarrierU_val`, `diracPointerH_isHermitian`,
`siteRay`, `arenaObs_siteProj_siteRay`, `arenaObs_siteProj_siteRay_of_ne`, `trainF_lift_zero`,
`trainF_deriv_lift_zero`); `RecordLayer/ActivatedWrite.lean` (`rateAt`, `continuous_rateAt`,
`exists_rateAt_eq_zero`, `displayArc`, `transition_region`, `rep_pshift_of_mem_neg`);
`RecordLayer/ShearWitness.lean` (`readyArc`, `pshift`, `rep_pshift_of_mem`);
`Mathlib/Analysis/Matrix/DuhamelBound.lean` (`Matrix.norm_exp_smul_neg_I_sub_le`);
`CV/DiracClockChain.lean` (`diracHam`); `CV/ArenaBridge.lean` (`arenaObs_kick_conj`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The two arcs under a turn of the pointer -/

/-- A ready pointer turned by between a third and two thirds of a turn is in the displayed arc. -/
theorem pshift_mem_displayArc {q : KTorus} (hq : q ∈ readyArc 2) {a : ℝ} (h₁ : 1 / 3 ≤ a)
    (h₂ : a ≤ 2 / 3) : pshift a q ∈ displayArc := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  change rep (pshift a q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)
  rw [shearWidth_two, rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩]
  constructor <;> linarith [hr.1, hr.2]

/-- A ready pointer turned by less than a sixth of a turn, either way, is not in the displayed
arc. -/
theorem pshift_notMem_displayArc {q : KTorus} (hq : q ∈ readyArc 2) {a : ℝ} (h : |a| < 1 / 6) :
    pshift a q ∉ displayArc := by
  intro hd
  change rep (pshift a q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) at hd
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hd hr
  obtain ⟨ha1, ha2⟩ := abs_lt.mp h
  by_cases hpos : 0 < rep q.1 + a
  · rw [rep_pshift_of_mem _ _ ⟨hpos, by linarith [hr.2]⟩] at hd
    linarith [hd.1, hr.2]
  · rw [rep_pshift_of_mem_neg _ ⟨by linarith [hr.1], not_lt.mp hpos⟩] at hd
    linarith [hd.2, hr.1]

/-! ### The ready state and the readout on `Σ_*` -/

section Readout

variable (M : ℕ)

/-- **The ready state** of the pointer of `Σ_*`: `θ₁` in the ready arc `(0, 1/6]`. It reads the
pointer angle only. -/
noncomputable def diracReady : Set (KSigma (2 * M + 1 + 1)) := {x | x.2 ∈ readyArc 2}

theorem measurableSet_diracReady : MeasurableSet (diracReady M) :=
  measurable_snd (measurableSet_readyArc (K := 2))

open Classical in
/-- **The readout** of the pointer of `Σ_*`: is `θ₁` in the displayed arc `(1/3, 5/6]`? It reads
the pointer angle only. -/
noncomputable def diracDisplayed (x : KSigma (2 * M + 1 + 1)) : Bool :=
  if x.2 ∈ displayArc then true else false

theorem measurable_diracDisplayed : Measurable (diracDisplayed M) := by
  unfold diracDisplayed
  exact Measurable.ite (measurable_snd measurableSet_displayArc) measurable_const measurable_const

variable {M}

theorem diracDisplayed_eq_true_iff {x : KSigma (2 * M + 1 + 1)} :
    diracDisplayed M x = true ↔ x.2 ∈ displayArc := by
  unfold diracDisplayed
  simp

theorem diracDisplayed_eq_false_iff {x : KSigma (2 * M + 1 + 1)} :
    diracDisplayed M x = false ↔ x.2 ∉ displayArc := by
  unfold diracDisplayed
  simp

/-- **The readout is a function of the pointer angle `θ₁` alone**: it does not read the carrier's
ray or the conserved angle `θ₂`. -/
theorem diracDisplayed_congr {x y : KSigma (2 * M + 1 + 1)} (h : x.2.1 = y.2.1) :
    diracDisplayed M x = diracDisplayed M y := by
  have hiff : x.2 ∈ displayArc ↔ y.2 ∈ displayArc := by
    show rep x.2.1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)
      ↔ rep y.2.1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)
    rw [h]
  by_cases hy : y.2 ∈ displayArc
  · rw [diracDisplayed_eq_true_iff.2 hy, diracDisplayed_eq_true_iff.2 (hiff.2 hy)]
  · rw [diracDisplayed_eq_false_iff.2 hy, diracDisplayed_eq_false_iff.2 (mt hiff.1 hy)]

/-- **The ready state is a condition on the pointer angle `θ₁` alone.** -/
theorem mem_diracReady_congr {x y : KSigma (2 * M + 1 + 1)} (h : x.2.1 = y.2.1) :
    x ∈ diracReady M ↔ y ∈ diracReady M := by
  show rep x.2.1 ∈ Ioc (0 : ℝ) (shearWidth 2) ↔ rep y.2.1 ∈ Ioc (0 : ℝ) (shearWidth 2)
  rw [h]

end Readout

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-! ### The carrier over a short time -/

/-- At time `0` the occupancy is the carrier's own. -/
theorem diracOccupancy_zero (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracOccupancy J μ g j hf φ p 0 = arenaObs (siteProj j) p := by
  rw [diracOccupancy, diracCarrierU_zero, arenaObs_kick_conj]
  simp

/-- **The coupled propagator is within `|t| ‖H_D + g f(θ₂) P_j‖` of the identity.** -/
theorem norm_diracCarrierU_sub_one_le (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(diracCarrierU J μ g j hf φ t).val - 1‖ ≤ |t| * ‖diracPointerH J μ g j hf φ‖ := by
  have h := Matrix.norm_exp_smul_neg_I_sub_le (diracPointerH J μ g j hf φ) 0
    (diracPointerH_isHermitian J μ g j hf φ) Matrix.isHermitian_zero t
  rw [smul_zero, smul_zero, NormedSpace.exp_zero, sub_zero] at h
  rwa [diracCarrierU_val]

/-- The carrier's Hamiltonian is no larger than the free chain's plus the site potential. -/
theorem norm_diracPointerH_le (φ : AddCircle (1 : ℝ)) :
    ‖diracPointerH J μ g j hf φ‖ ≤ ‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ| := by
  rw [diracPointerH]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_siteProj_le j)

/-- ★ **The occupancy stays within `2 |s| ‖H‖` of its starting value.** -/
theorem abs_diracOccupancy_sub_zero_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (s : ℝ) :
    |diracOccupancy J μ g j hf φ p s - arenaObs (siteProj j) p|
      ≤ 2 * |s| * ‖diracPointerH J μ g j hf φ‖ := by
  rw [← diracOccupancy_zero J μ g j hf φ p]
  refine (abs_arenaObs_arenaKick_sub_le _ _ (siteProj j) p).trans ?_
  have hU : ‖(diracCarrierU J μ g j hf φ s).val - (diracCarrierU J μ g j hf φ 0).val‖
      ≤ |s| * ‖diracPointerH J μ g j hf φ‖ := by
    rw [diracCarrierU_zero]
    exact norm_diracCarrierU_sub_one_le J μ g j hf φ s
  calc 2 * ‖siteProj j‖ * ‖(diracCarrierU J μ g j hf φ s).val - (diracCarrierU J μ g j hf φ 0).val‖
      ≤ 2 * 1 * (|s| * ‖diracPointerH J μ g j hf φ‖) := by
        gcongr
        exact norm_siteProj_le j
    _ = 2 * |s| * ‖diracPointerH J μ g j hf φ‖ := by ring

/-- ★★ **The accumulated occupancy is within `‖H‖ t²` of `t` times the starting occupancy.** -/
theorem abs_integral_diracOccupancy_sub_mul_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s) - t * arenaObs (siteProj j) p|
      ≤ ‖diracPointerH J μ g j hf φ‖ * t ^ 2 := by
  have hi : IntervalIntegrable (fun s => diracOccupancy J μ g j hf φ p s) volume 0 t :=
    (continuous_diracOccupancy J μ g j hf φ p).intervalIntegrable 0 t
  have hconst : (∫ _ in (0 : ℝ)..t, arenaObs (siteProj j) p) = t * arenaObs (siteProj j) p := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← hconst, ← intervalIntegral.integral_sub hi intervalIntegrable_const]
  have hc : Continuous fun s : ℝ => 2 * s * ‖diracPointerH J μ g j hf φ‖ := by fun_prop
  have hab : Continuous fun s =>
      |diracOccupancy J μ g j hf φ p s - arenaObs (siteProj j) p| :=
    ((continuous_diracOccupancy J μ g j hf φ p).sub continuous_const).abs
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine (intervalIntegral.integral_mono_on ht (hab.intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 t) fun s hs => ?_).trans_eq ?_
  · have h := abs_diracOccupancy_sub_zero_le J μ g j hf φ p s
    rwa [abs_of_nonneg hs.1] at h
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring

/-! ### The displacement in terms of the pointer's rate -/

/-- The pointer's rate per unit occupancy is `ActivatedWrite.lean`'s `rateAt` at `ħ = 1`:
`−2 g f'(θ₂)`. -/
theorem rateAt_one (φ : AddCircle (1 : ℝ)) :
    rateAt g 1 hf φ = -(2 * g) * hf.deriv_periodic.lift φ := by
  rw [rateAt, div_one]

/-- The displacement is the rate times the accumulated occupancy. -/
theorem diracPointerShift_eq_rateAt (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracPointerShift J μ g j hf φ p t
      = rateAt g 1 hf φ * ∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s := by
  rw [rateAt_one]
  rfl

/-- On a fibre with a nonnegative rate the pointer does not turn back. -/
theorem diracPointerShift_nonneg {φ : AddCircle (1 : ℝ)} (hκ : 0 ≤ rateAt g 1 hf φ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ diracPointerShift J μ g j hf φ p t := by
  rw [diracPointerShift_eq_rateAt]
  exact mul_nonneg hκ (integral_diracOccupancy_nonneg J μ g j hf φ p ht)

/-- On a fibre with a nonnegative rate `κ` the pointer has turned by at most `κ t`. -/
theorem diracPointerShift_le_rateAt_mul {φ : AddCircle (1 : ℝ)} (hκ : 0 ≤ rateAt g 1 hf φ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    diracPointerShift J μ g j hf φ p t ≤ rateAt g 1 hf φ * t := by
  rw [diracPointerShift_eq_rateAt]
  exact mul_le_mul_of_nonneg_left (integral_diracOccupancy_le J μ g j hf φ p ht) hκ

/-- On every fibre the pointer has turned by at most `|κ| t`, either way. -/
theorem abs_diracPointerShift_le_rateAt (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ p t| ≤ |rateAt g 1 hf φ| * t := by
  rw [diracPointerShift_eq_rateAt, abs_mul,
    abs_of_nonneg (integral_diracOccupancy_nonneg J μ g j hf φ p ht)]
  exact mul_le_mul_of_nonneg_left (integral_diracOccupancy_le J μ g j hf φ p ht) (abs_nonneg _)

/-- ★★ **The displacement over a short time.** It is within `|κ| ‖H‖ t²` of `κ t` times the
occupancy the carrier started with: a carrier has not had time to leave, or to reach, the
detector's site. -/
theorem abs_diracPointerShift_sub_init_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ p t - rateAt g 1 hf φ * (t * arenaObs (siteProj j) p)|
      ≤ |rateAt g 1 hf φ| * (‖diracPointerH J μ g j hf φ‖ * t ^ 2) := by
  rw [diracPointerShift_eq_rateAt, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_diracOccupancy_sub_mul_le J μ g j hf φ p ht) (abs_nonneg _)

/-- ★★ **The signal.** A carrier prepared on the detector's site turns the pointer by at least
`κ (t − ‖H‖ t²)`. -/
theorem le_diracPointerShift_siteRay {φ : AddCircle (1 : ℝ)} (hκ : 0 ≤ rateAt g 1 hf φ) {t : ℝ}
    (ht : 0 ≤ t) :
    rateAt g 1 hf φ * (t - ‖diracPointerH J μ g j hf φ‖ * t ^ 2)
      ≤ diracPointerShift J μ g j hf φ (siteRay j) t := by
  have h := abs_diracPointerShift_sub_init_le J μ g j hf φ (siteRay j) ht
  rw [arenaObs_siteProj_siteRay, mul_one, abs_of_nonneg hκ] at h
  linarith [(abs_le.mp h).1]

/-- ★★ **The control.** A carrier prepared on another site turns the pointer by at most
`|κ| ‖H‖ t²`. -/
theorem abs_diracPointerShift_siteRay_of_ne_le {k : ZMod (M + 1)} (hk : j ≠ k)
    (φ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ (siteRay k) t|
      ≤ |rateAt g 1 hf φ| * (‖diracPointerH J μ g j hf φ‖ * t ^ 2) := by
  have h := abs_diracPointerShift_sub_init_le J μ g j hf φ (siteRay k) ht
  rwa [arenaObs_siteProj_siteRay_of_ne hk, mul_zero, mul_zero, sub_zero] at h

/-! ### The threshold, along the Hamiltonian flow -/

/-- The pointer pair of the joint flow is the starting pair turned by the displacement. -/
theorem diracPointerFlow_snd (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : KTorus) :
    (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)).2
      = pshift (diracPointerShift J μ g j hf q.2 p t) q := by
  rw [diracPointerFlow_apply]
  rfl

/-- ★★ **Crossing the threshold.** From a ready pointer, a displacement between a third and two
thirds of a turn puts the flow in the displayed region. -/
theorem diracPointerFlow_displayed (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ}
    (h₁ : 1 / 3 ≤ diracPointerShift J μ g j hf q.2 p t)
    (h₂ : diracPointerShift J μ g j hf q.2 p t ≤ 2 / 3) :
    diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) = true := by
  rw [diracDisplayed_eq_true_iff, diracPointerFlow_snd]
  exact pshift_mem_displayArc hq h₁ h₂

/-- ★★ **Staying below the threshold.** From a ready pointer, a displacement of less than a sixth of
a turn leaves the flow outside the displayed region. -/
theorem diracPointerFlow_not_displayed (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ}
    (h : |diracPointerShift J μ g j hf q.2 p t| < 1 / 6) :
    diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) = false := by
  rw [diracDisplayed_eq_false_iff, diracPointerFlow_snd]
  exact pshift_notMem_displayArc hq h

/-- ★★★ **A carrier on the detector's site crosses the threshold.** On a fibre with rate `κ ≥ 0`,
at a time `T` with `1/3 ≤ κ (T − ‖H‖ T²)` and `κ T ≤ 2/3`, the flow from a ready pointer is in the
displayed region. -/
theorem diracPointerFlow_siteRay_displayed (hc : ContDiff ℝ ∞ f) {q : KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 ≤ rateAt g 1 hf q.2) {T : ℝ} (hT : 0 ≤ T)
    (h₁ : 1 / 3 ≤ rateAt g 1 hf q.2 * (T - ‖diracPointerH J μ g j hf q.2‖ * T ^ 2))
    (h₂ : rateAt g 1 hf q.2 * T ≤ 2 / 3) :
    diracDisplayed M
      (diracPointerFlow J μ g j hf hc T (diracArenaEquiv M (siteRay j), q)) = true :=
  diracPointerFlow_displayed J μ g j hf hc hq _
    (h₁.trans (le_diracPointerShift_siteRay J μ g j hf hκ hT))
    ((diracPointerShift_le_rateAt_mul J μ g j hf hκ _ hT).trans h₂)

/-- ★★★ **A carrier on another site does not**, up to the same time: if `|κ| ‖H‖ T² < 1/6` the
flow from a ready pointer is outside the displayed region throughout `[0, T]`. -/
theorem diracPointerFlow_siteRay_of_ne_not_displayed (hc : ContDiff ℝ ∞ f) {k : ZMod (M + 1)}
    (hk : j ≠ k) {q : KTorus} (hq : q ∈ readyArc 2) {T : ℝ}
    (h : |rateAt g 1 hf q.2| * (‖diracPointerH J μ g j hf q.2‖ * T ^ 2) < 1 / 6) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    diracDisplayed M
      (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay k), q)) = false := by
  refine diracPointerFlow_not_displayed J μ g j hf hc hq _ ?_
  refine ((abs_diracPointerShift_siteRay_of_ne_le J μ g j hf hk q.2 ht0).trans ?_).trans_lt h
  have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 htT 2
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (norm_nonneg _)) (abs_nonneg _)

/-! ### The fibres on which the pointer is too slow -/

/-- **The slow fibres** for the horizon `T`: the angles `θ₂` at which the pointer's rate is below a
sixth of a turn per `T`. -/
def slowFibres (T : ℝ) : Set (AddCircle (1 : ℝ)) := {φ | |rateAt g 1 hf φ| * T < 1 / 6}

theorem isOpen_slowFibres (hf1 : ContDiff ℝ 1 f) (T : ℝ) : IsOpen (slowFibres g hf T) :=
  isOpen_lt ((continuous_rateAt g 1 hf hf1).abs.mul continuous_const) continuous_const

/-- ★★ **The slow fibres have positive measure, for every profile and every horizon**: they are
open and contain Rolle's zero of `f'`. -/
theorem volume_slowFibres_pos (hf1 : ContDiff ℝ 1 f) (T : ℝ) :
    0 < volume (slowFibres g hf T) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_rateAt_eq_zero g 1 hf hf1
  refine (isOpen_slowFibres g hf hf1 T).measure_pos volume ⟨φ₀, ?_⟩
  show |rateAt g 1 hf φ₀| * T < 1 / 6
  rw [hφ₀, abs_zero, zero_mul]
  norm_num

/-- ★★★ **On a slow fibre nothing is displayed, whatever the carrier**: from a ready pointer the
flow is outside the displayed region throughout `[0, T]`. -/
theorem diracPointerFlow_not_displayed_of_mem_slowFibres (hc : ContDiff ℝ ∞ f) {T : ℝ}
    {q : KTorus} (hq : q ∈ readyArc 2) (hφ : q.2 ∈ slowFibres g hf T)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) = false := by
  refine diracPointerFlow_not_displayed J μ g j hf hc hq p ?_
  have hφ' : |rateAt g 1 hf q.2| * T < 1 / 6 := hφ
  exact ((abs_diracPointerShift_le_rateAt J μ g j hf q.2 p ht0).trans
    (mul_le_mul_of_nonneg_left htT (abs_nonneg _))).trans_lt hφ'

/-! ### The fibres on which the write is proved -/

variable (M) in
/-- **The write fibres** for the readout time `T`: the angles `θ₂` at which the rate `κ = −2 g f'`
is positive, `1/3 < κ (T − h T²)`, `κ T < 2/3` and `κ h T² < 1/6`, with
`h = ‖H_D‖ + |g f(θ₂)|` bounding the carrier's Hamiltonian. -/
def writeFibres (T : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {φ | 0 < rateAt g 1 hf φ
    ∧ 1 / 3 < rateAt g 1 hf φ * (T - (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) * T ^ 2)
    ∧ rateAt g 1 hf φ * T < 2 / 3
    ∧ rateAt g 1 hf φ * ((‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) * T ^ 2) < 1 / 6}

theorem isOpen_writeFibres (hf1 : ContDiff ℝ 1 f) (T : ℝ) :
    IsOpen (writeFibres M J μ g hf T) := by
  have hκ := continuous_rateAt g 1 hf hf1
  have hh : Continuous fun φ : AddCircle (1 : ℝ) =>
      ‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ| :=
    continuous_const.add (continuous_const.mul (continuous_periodicLift hf hf1.continuous)).abs
  exact (isOpen_lt continuous_const hκ).and
    ((isOpen_lt continuous_const
        (hκ.mul (continuous_const.sub (hh.mul continuous_const)))).and
      ((isOpen_lt (hκ.mul continuous_const) continuous_const).and
        (isOpen_lt (hκ.mul (hh.mul continuous_const)) continuous_const)))

/-- ★★★ **On a write fibre the carrier on the detector's site is displayed at `T`.** -/
theorem diracPointerFlow_displayed_of_mem_writeFibres (hc : ContDiff ℝ ∞ f) {T : ℝ}
    (hT : 0 ≤ T) {q : KTorus} (hq : q ∈ readyArc 2) (hφ : q.2 ∈ writeFibres M J μ g hf T) :
    diracDisplayed M
      (diracPointerFlow J μ g j hf hc T (diracArenaEquiv M (siteRay j), q)) = true := by
  obtain ⟨hκ, h₁, h₂, -⟩ := hφ
  refine diracPointerFlow_siteRay_displayed J μ g j hf hc hq hκ.le hT (h₁.le.trans ?_) h₂.le
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left
    (mul_le_mul_of_nonneg_right (norm_diracPointerH_le J μ g j hf q.2) (sq_nonneg T)) T) hκ.le

/-- ★★★ **On a write fibre the carrier on another site is not displayed** throughout `[0, T]`. -/
theorem diracPointerFlow_not_displayed_of_mem_writeFibres (hc : ContDiff ℝ ∞ f)
    {k : ZMod (M + 1)} (hk : j ≠ k) {T : ℝ} {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ writeFibres M J μ g hf T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    diracDisplayed M
      (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay k), q)) = false := by
  obtain ⟨hκ, -, -, h₃⟩ := hφ
  refine diracPointerFlow_siteRay_of_ne_not_displayed J μ g j hf hc hk hq
    (lt_of_le_of_lt ?_ h₃) ht0 htT
  rw [abs_of_pos hκ]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (norm_diracPointerH_le J μ g j hf q.2) (sq_nonneg T)) hκ.le

/-- The write fibres and the slow fibres of the same horizon do not meet. -/
theorem disjoint_writeFibres_slowFibres (T : ℝ) :
    Disjoint (writeFibres M J μ g hf T) (slowFibres g hf T) := by
  rw [Set.disjoint_left]
  rintro φ ⟨hκ, h₁, -, -⟩ hs
  have hs' : |rateAt g 1 hf φ| * T < 1 / 6 := hs
  rw [abs_of_pos hκ] at hs'
  have hh : 0 ≤ (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) * T ^ 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left (sub_le_self T hh) hκ.le]

end Arena

/-! ### The write fibres are not empty: the profile `trainF` -/

section Check

variable (M : ℕ) (J μ : ℝ)

/-- **The fibre `θ₂ = 0` of the profile `trainF` is a write fibre** at coupling `g = 1/(4T)`, for
every readout time `T` short on the chain's scale: `‖H_D‖ T ≤ 1/4`. -/
theorem zero_mem_writeFibres_trainF {T : ℝ} (hT : 0 < T)
    (hJT : ‖diracHam (L := M + 1) J μ‖ * T ≤ 1 / 4) :
    (0 : AddCircle (1 : ℝ)) ∈ writeFibres M J μ (1 / (4 * T)) trainF_periodic T := by
  have hT' : T ≠ 0 := hT.ne'
  have hκ : rateAt (1 / (4 * T)) 1 trainF_periodic (0 : AddCircle (1 : ℝ)) = 1 / (2 * T) := by
    rw [rateAt_one, trainF_deriv_lift_zero]
    field_simp
    ring
  show _ ∧ _ ∧ _ ∧ _
  rw [hκ, trainF_lift_zero, mul_zero, abs_zero, add_zero]
  set h := ‖diracHam (L := M + 1) J μ‖ with hh
  have e₁ : 1 / (2 * T) * (T - h * T ^ 2) = 1 / 2 - h * T / 2 := by
    field_simp
  have e₂ : 1 / (2 * T) * T = 1 / 2 := by
    field_simp
  have e₃ : 1 / (2 * T) * (h * T ^ 2) = h * T / 2 := by
    field_simp
  rw [e₁, e₂, e₃]
  refine ⟨by positivity, by linarith, by norm_num, by linarith⟩

/-- ★★★ **The write fibres have positive measure** for the profile `trainF`: they are open and
contain `θ₂ = 0`. -/
theorem volume_writeFibres_trainF_pos {T : ℝ} (hT : 0 < T)
    (hJT : ‖diracHam (L := M + 1) J μ‖ * T ≤ 1 / 4) :
    0 < volume (writeFibres M J μ (1 / (4 * T)) trainF_periodic T) :=
  (isOpen_writeFibres J μ (1 / (4 * T)) trainF_periodic
    (contDiff_trainF.of_le (by simp)) T).measure_pos volume
    ⟨0, zero_mem_writeFibres_trainF M J μ hT hJT⟩

/-- ★★ **For every ring and every `J`, `μ` there are a coupling and a readout time** at which the
write fibres have positive measure. -/
theorem exists_volume_writeFibres_pos :
    ∃ g T : ℝ, 0 < T ∧ 0 < volume (writeFibres M J μ g trainF_periodic T) := by
  have hn : 0 ≤ ‖diracHam (L := M + 1) J μ‖ := norm_nonneg _
  set h := ‖diracHam (L := M + 1) J μ‖ with hh
  refine ⟨1 / (4 * (1 / (8 * (h + 1)))), 1 / (8 * (h + 1)), by positivity,
    volume_writeFibres_trainF_pos M J μ (by positivity) ?_⟩
  rw [← hh, mul_one_div, div_le_iff₀ (by positivity)]
  linarith

end Check

end CSD.RecordLayer

end
