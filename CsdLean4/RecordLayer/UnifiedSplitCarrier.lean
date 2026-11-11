/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTwoSiteRecords

/-!
# A carrier split between two detectors: both display

**Category:** 7-SigmaLayer (the record layer). BACKLOG #370 — the author's programme "From `Σ` to
physical spacetime", obligation UO-10; Remainder (a) of #364.
`RecordLayer/UnifiedTwoSiteRecords.lean` put two site detectors in one run and showed that for a
carrier on one detector's site that detector writes and the other is not displayed until then. It
left open the carrier that is split between the two sites, which is the case "one trial, one
outcome" is about. This module settles it for this arena: both detectors display.

**A pointer driven by a half-occupied site** (any finite index). In the setting of #364 (a
continuous family of unitaries within `|s| N` of the identity, an observable with `‖D‖ ≤ 1`, a
ready pointer at `pshift (κ ∫₀ᵗ⟨D⟩)`, `κ > 0`): if `96 N ≤ κ` and the starting expectation `q`
is in `[3/8, 5/8]`, the readout is `true` at every time in `[23/(25κ), 26/(25κ)]`
(`shown_of_half_occupancy`). If the expectation is in `[0, 1]`, the readout is not `true` at any
time up to `1/(6κ)`, whatever `q` is (`not_shown_of_le_sixth`).

**The split fibres** (`splitFibres`): the pairs of conserved angles `(θ₂, ψ₂)` with
`96 B < κ₁`, `96 B < κ₂`, `23 κ₁ < 25 κ₂` and `25 κ₂ < 26 κ₁`, where
`B = ‖H_D‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|`. The set is open, and for both profiles `trainF` and equal
strengths `g` with `96 ‖H_D‖ < 2 g` it contains `(0, 0)` and has positive Haar measure
(`volume_splitFibres_trainF_pos`).

**Both display.** On a split fibre, from two ready pointers, for detectors at two different sites
`j ≠ k` and a carrier with at least `3/8` of its occupancy on each: at the flow time `1/κ₁` the
first readout is `true` and the second readout is `true`, along the one orbit of
`diracTwoPointerFlow` (`diracTwoPointerFlow_double_display`). Neither readout is `true` up to
`1/(6κ)` of its own rate (`diracTwoPointerFlow_split_not_shown_early`), so both switch on. The
equal superposition of a state on `j` and a state on `k` is such a carrier, with occupancy `1/2`
on each (`splitRay`, `arenaObs_siteProj_splitRay_fst`, `arenaObs_siteProj_splitRay_snd`,
`diracTwoPointerFlow_splitRay_double_display`).

## Exact scope

* **This is a statement about this coupling.** Each pointer is driven by the occupancy of its
  site (UA-5): its displacement is the rate times the accumulated occupancy. A carrier with half
  its occupancy on each site turns both pointers at half rate, and both cross the threshold. No
  step of the flow selects one site. So on this arena, with this coupling and these readouts,
  "one trial, one outcome" does not hold for a split carrier. It is the same obstruction as
  gate A's (#355): the pointer reads an occupancy, not an outcome.
* **Not a prediction about detectors.** The statement is about the model of UA-5 and UA-13 on
  the split fibres. The weights of quantum mechanics for one click or the other are not derived
  here and are not contradicted here: in the contract they stay conditional on the cell law
  (UA-6, Posit 1), which this arena does not use. A selection of one outcome would need a
  mechanism that is not in this joint energy. The selection by the cell of the ontic point,
  and why no readout local to its site can replace it, is `RecordLayer/UnifiedCellSelection.lean`
  (#371).
* **Fast detectors, comparable rates.** `96 ‖H‖ < κ` for both, and the rates within about
  thirteen per cent of each other, so that one flow time serves both. Nothing is said for slow
  detectors or for very different rates.
* **A class of carriers**: at least `3/8` of the occupancy on each of the two sites. The equal
  superposition is exhibited. Carriers between this class and that of #364 (occupancy between
  `1/8` and `3/8` on one site) are not covered.
* **One flow time.** Both readouts are shown `true` at `1/κ₁`, and each through an interval of
  its own. No `IsRecordWrite` with a window is built for the split carrier.
* **Positive measure is Haar measure on the pair of conserved angles**, for two `trainF`
  detectors of equal strength. No `echoMuL` measure of the set of start points is stated.
* **Definite facts, not statistics.** All times are flow times (UA-7). The readouts and ready
  arcs are apparatus input (UA-4).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-6, UA-7, UA-13, UO-10, UD-99, UD-100); `RecordLayer/UnifiedTwoSiteRecords.lean`
(`abs_integral_arenaObs_sub_mul_le`, `integral_arenaObs_mono`, `integral_arenaObs_le`,
`echoFstShown_diracTwoPointerFlow_iff`, `echoSiteShown_diracTwoPointerFlow_iff`,
`norm_diracTwoCarrierU_sub_one_le`, `norm_diracTwoH_le`, `arenaObs_siteProj_le_one_sub`,
`diracTwoPointerFlow_record_fst_only`); `RecordLayer/DiracPointerClick.lean` (`pairRay`,
`arenaObs_siteProj_pairRay`; gate A's obstruction); `RecordLayer/DiracPointerThreshold.lean`
(`pshift_mem_displayArc`); `RecordLayer/DiracPointerRecord.lean`
(`pshift_notMem_displayArc_of_le`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A pointer driven by a half-occupied site -/

section Driven

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {U : ℝ → Matrix.unitaryGroup ι ℂ} {D : Matrix ι ι ℂ}

/-- ★★★ **A fast pointer on a half-occupied site displays.** With `κ > 0`, `96 N ≤ κ` and a
starting expectation in `[3/8, 5/8]`, the readout of a ready pointer at `pshift (κ ∫₀ᵗ⟨D⟩)` is
`true` at every time in `[23/(25κ), 26/(25κ)]`. -/
theorem shown_of_half_occupancy (hUc : Continuous U) {N : ℝ}
    (hU : ∀ s, ‖(U s).val - 1‖ ≤ |s| * N) (hD : ‖D‖ ≤ 1) {κ : ℝ} (hκ : 0 < κ)
    (hN : 96 * N ≤ κ) (p : GenArena ι) (hq₁ : 3 / 8 ≤ arenaObs D p)
    (hq₂ : arenaObs D p ≤ 5 / 8) {a : KTorus} (ha : a ∈ readyArc 2) {hist : ℝ → Bool}
    (hhist : ∀ t, hist t = true
      ↔ pshift (κ * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) a ∈ displayArc)
    {t : ℝ} (ht₁ : 23 / (25 * κ) ≤ t) (ht₂ : t ≤ 26 / (25 * κ)) : hist t = true := by
  have hκne : κ ≠ 0 := hκ.ne'
  have ht0 : 0 ≤ t := le_trans (by positivity) ht₁
  have key := abs_le.1 (abs_integral_arenaObs_sub_mul_le hUc hU hD p ht0)
  -- the dimensionless time `u = κ t`
  have hu₁ : 23 / 25 ≤ κ * t := by
    have h := mul_le_mul_of_nonneg_left ht₁ hκ.le
    have e : κ * (23 / (25 * κ)) = 23 / 25 := by field_simp
    rwa [e] at h
  have hu₂ : κ * t ≤ 26 / 25 := by
    have h := mul_le_mul_of_nonneg_left ht₂ hκ.le
    have e : κ * (26 / (25 * κ)) = 26 / 25 := by field_simp
    rwa [e] at h
  -- the error `κ N t² ≤ (κ t)² / 96`
  have herr : κ * (N * t ^ 2) ≤ (κ * t) ^ 2 / 96 := by
    have h1 : N ≤ κ / 96 := by linarith
    have h2 : 0 ≤ κ * t ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have e : κ / 96 * (κ * t ^ 2) = (κ * t) ^ 2 / 96 := by ring
    rw [e] at h3
    linarith
  have hsq : (κ * t) ^ 2 ≤ 49 / 25 * (κ * t) - 598 / 625 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu₁) (sub_nonneg.2 hu₂)]
  have hlo := mul_le_mul_of_nonneg_left key.1 hκ.le
  have hhi := mul_le_mul_of_nonneg_left key.2 hκ.le
  have hq₁' : κ * t * (3 / 8) ≤ κ * (t * arenaObs D p) := by
    have := mul_le_mul_of_nonneg_left hq₁ (mul_nonneg hκ.le ht0)
    linarith
  have hq₂' : κ * (t * arenaObs D p) ≤ κ * t * (5 / 8) := by
    have := mul_le_mul_of_nonneg_left hq₂ (mul_nonneg hκ.le ht0)
    linarith
  refine (hhist t).2 (pshift_mem_displayArc ha ?_ ?_)
  · have e : κ * -(N * t ^ 2) = -(κ * (N * t ^ 2)) := by ring
    have e2 : κ * ((∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) - t * arenaObs D p)
        = κ * (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
          - κ * (t * arenaObs D p) := by ring
    rw [e, e2] at hlo
    linarith
  · have e2 : κ * ((∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) - t * arenaObs D p)
        = κ * (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
          - κ * (t * arenaObs D p) := by ring
    rw [e2] at hhi
    linarith

omit [Nonempty ι] in
/-- ★ **No pointer displays before a sixth of a turn at full rate.** For an observable with
expectation in `[0, 1]` and `κ > 0`, the readout is not `true` at any time in `[0, 1/(6κ)]`. -/
theorem not_shown_of_le_sixth (hUc : Continuous U) (hpos : ∀ q, 0 ≤ arenaObs D q)
    (hle : ∀ q, arenaObs D q ≤ 1) {κ : ℝ} (hκ : 0 < κ) (p : GenArena ι) {a : KTorus}
    (ha : a ∈ readyArc 2) {hist : ℝ → Bool}
    (hhist : ∀ t, hist t = true
      ↔ pshift (κ * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) a ∈ displayArc)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / (6 * κ)) : ¬ hist t = true := by
  have hκne : κ ≠ 0 := hκ.ne'
  intro hshown
  refine pshift_notMem_displayArc_of_le ha ?_ ?_ ((hhist t).1 hshown)
  · have h := mul_le_mul_of_nonneg_left (integral_arenaObs_mono hUc hpos p ht0) hκ.le
    rwa [intervalIntegral.integral_same, mul_zero] at h
  · have h1 := mul_le_mul_of_nonneg_left (integral_arenaObs_le hUc hle p ht0) hκ.le
    have h2 := mul_le_mul_of_nonneg_left ht hκ.le
    have e : κ * (1 / (6 * κ)) = 1 / 6 := by field_simp
    rw [e] at h2
    linarith

end Driven

/-! ### The split fibres -/

section Fibres

variable (M : ℕ) {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ)
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- **The split fibres**: the pairs of conserved angles `(θ₂, ψ₂)` at which both detectors are
fast, `96 (‖H_D‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|) < κ₁` and `< κ₂`, and their rates are close,
`23 κ₁ < 25 κ₂` and `25 κ₂ < 26 κ₁`. -/
def splitFibres : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 96 * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|)
        < rateAt g₁ 1 hf x.1
    ∧ 96 * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|)
        < rateAt g₂ 1 hh x.2
    ∧ 23 * rateAt g₁ 1 hf x.1 < 25 * rateAt g₂ 1 hh x.2
    ∧ 25 * rateAt g₂ 1 hh x.2 < 26 * rateAt g₁ 1 hf x.1}

/-- The split fibres are open. -/
theorem isOpen_splitFibres (hf1 : ContDiff ℝ 1 f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (splitFibres M J μ g₁ g₂ hf hh) := by
  have hκ₁ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₁ 1 hf x.1 :=
    (continuous_rateAt g₁ 1 hf hf1).comp continuous_fst
  have hκ₂ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₂ 1 hh x.2 :=
    (continuous_rateAt g₂ 1 hh hh1).comp continuous_snd
  have hB : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      96 * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) :=
    continuous_const.mul ((continuous_const.add
      (continuous_const.mul
        ((continuous_periodicLift hf hf1.continuous).comp continuous_fst)).abs).add
      (continuous_const.mul
        ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs)
  exact (isOpen_lt hB hκ₁).inter
    ((isOpen_lt hB hκ₂).inter
      ((isOpen_lt (continuous_const.mul hκ₁) (continuous_const.mul hκ₂)).inter
        (isOpen_lt (continuous_const.mul hκ₂) (continuous_const.mul hκ₁))))

variable {M}

/-- On a split fibre both rates are positive, `96 ‖H‖ ≤ κ` for each, and the rates are close,
for detectors at any two sites. -/
theorem splitFibres_bounds {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ splitFibres M J μ g₁ g₂ hf hh) (j k : ZMod (M + 1)) :
    0 < rateAt g₁ 1 hf φ ∧ 0 < rateAt g₂ 1 hh χ
      ∧ 96 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ≤ rateAt g₁ 1 hf φ
      ∧ 96 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ≤ rateAt g₂ 1 hh χ
      ∧ 23 * rateAt g₁ 1 hf φ ≤ 25 * rateAt g₂ 1 hh χ
      ∧ 25 * rateAt g₂ 1 hh χ ≤ 26 * rateAt g₁ 1 hf φ := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hH := mul_le_mul_of_nonneg_left (norm_diracTwoH_le J μ g₁ g₂ j k hf hh φ χ)
    (by norm_num : (0 : ℝ) ≤ 96)
  have h0 : 0 ≤ 96 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ := by positivity
  have h1' : (96 : ℝ) * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift φ| + |g₂ * hh.lift χ|)
      < rateAt g₁ 1 hf φ := h1
  have h2' : (96 : ℝ) * (‖diracHam (L := M + 1) J μ‖ + |g₁ * hf.lift φ| + |g₂ * hh.lift χ|)
      < rateAt g₂ 1 hh χ := h2
  have h3' : 23 * rateAt g₁ 1 hf φ < 25 * rateAt g₂ 1 hh χ := h3
  have h4' : 25 * rateAt g₂ 1 hh χ < 26 * rateAt g₁ 1 hf φ := h4
  exact ⟨by linarith, by linarith, by linarith, by linarith, h3'.le, h4'.le⟩

variable (M)

/-- **With both profiles `trainF` and equal strengths `g`, the pair `(0, 0)` is a split fibre**
once `96 ‖H_D‖ < 2 g`. -/
theorem zero_mem_splitFibres_trainF {g : ℝ} (hg : 96 * ‖diracHam (L := M + 1) J μ‖ < 2 * g) :
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ∈ splitFibres M J μ g g trainF_periodic trainF_periodic := by
  have h0 : 0 ≤ ‖diracHam (L := M + 1) J μ‖ := norm_nonneg _
  show _ ∧ _ ∧ _ ∧ _
  rw [rateAt_trainF_zero, trainF_lift_zero, mul_zero, abs_zero, add_zero, add_zero]
  exact ⟨hg, hg, by linarith, by linarith⟩

/-- ★★ **The split fibres have positive measure** for two detectors with the profile `trainF`
and equal strengths `g`, `96 ‖H_D‖ < 2 g`. -/
theorem volume_splitFibres_trainF_pos {g : ℝ}
    (hg : 96 * ‖diracHam (L := M + 1) J μ‖ < 2 * g) :
    0 < volume (splitFibres M J μ g g trainF_periodic trainF_periodic) :=
  (isOpen_splitFibres M J μ g g trainF_periodic trainF_periodic
    (contDiff_trainF.of_le (by simp)) (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(0, 0), zero_mem_splitFibres_trainF M J μ hg⟩

end Fibres

/-! ### Both detectors display -/

section Double

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (j k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- ★★★ **A split carrier makes both detectors display.** On a split fibre, from two ready
pointers, for detectors at two different sites and a carrier with at least `3/8` of its occupancy
on each: at the flow time `1/κ₁` the first readout is `true` and the second readout is `true`,
along the one orbit of `diracTwoPointerFlow`. So for this coupling one run does not have one
outcome. The time is a flow time (UA-7). -/
theorem diracTwoPointerFlow_double_display (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hjk : j ≠ k) {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ splitFibres M J μ g₁ g₂ hf hh) {κ₁ : ℝ}
    (hκ₁ : κ₁ = rateAt g₁ 1 hf θ.2) (p : GenArena (ZMod (M + 1) × Fin 2))
    (hqj : 3 / 8 ≤ arenaObs (siteProj j) p) (hqk : 3 / 8 ≤ arenaObs (siteProj k) p) :
    echoFstShown (2 * M + 1)
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch (1 / κ₁)
          ((diracArenaEquiv M p, θ), ψ)) = true
      ∧ echoSiteShown (2 * M + 1)
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch (1 / κ₁)
          ((diracArenaEquiv M p, θ), ψ)) = true := by
  obtain ⟨hp₁, hp₂, hN₁, hN₂, h23, h26⟩ := splitFibres_bounds J μ g₁ g₂ hf hh hx j k
  have hUc := continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2
  have hU := norm_diracTwoCarrierU_sub_one_le J μ g₁ g₂ j k hf hh θ.2 ψ.2
  have hqj' : arenaObs (siteProj j) p ≤ 5 / 8 := by
    have := arenaObs_siteProj_le_one_sub hjk.symm p
    linarith
  have hqk' : arenaObs (siteProj k) p ≤ 5 / 8 := by
    have := arenaObs_siteProj_le_one_sub hjk p
    linarith
  rw [hκ₁]
  set κ := rateAt g₁ 1 hf θ.2 with hκdef
  set κ' := rateAt g₂ 1 hh ψ.2 with hκ'def
  refine ⟨?_, ?_⟩
  · refine shown_of_half_occupancy hUc hU (norm_siteProj_le j) hp₁ hN₁ p hqj hqj' hθ
      (echoFstShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ) ?_ ?_
    · rw [div_le_div_iff₀ (by positivity) hp₁]
      linarith
    · rw [div_le_div_iff₀ hp₁ (by positivity)]
      linarith
  · refine shown_of_half_occupancy hUc hU (norm_siteProj_le k) hp₂ hN₂ p hqk hqk' hψ
      (echoSiteShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ) ?_ ?_
    · rw [div_le_div_iff₀ (by positivity) hp₁]
      linarith
    · rw [div_le_div_iff₀ hp₁ (by positivity)]
      linarith

/-- ★★ **Neither readout is `true` early**: the first up to `1/(6κ₁)` and the second up to
`1/(6κ₂)`, for every carrier. With `diracTwoPointerFlow_double_display`, both switch on. -/
theorem diracTwoPointerFlow_split_not_shown_early (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ splitFibres M J μ g₁ g₂ hf hh)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht0 : 0 ≤ t) :
    (t ≤ 1 / (6 * rateAt g₁ 1 hf θ.2) →
        ¬ echoFstShown (2 * M + 1)
          (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
            ((diracArenaEquiv M p, θ), ψ)) = true)
      ∧ (t ≤ 1 / (6 * rateAt g₂ 1 hh ψ.2) →
        ¬ echoSiteShown (2 * M + 1)
          (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
            ((diracArenaEquiv M p, θ), ψ)) = true) := by
  obtain ⟨hp₁, hp₂, -, -, -, -⟩ := splitFibres_bounds J μ g₁ g₂ hf hh hx j k
  have hUc := continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2
  exact ⟨fun ht => not_shown_of_le_sixth hUc (arenaObs_siteProj_nonneg j)
      (arenaObs_siteProj_le_one j) hp₁ p hθ
      (echoFstShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ) ht0 ht,
    fun ht => not_shown_of_le_sixth hUc (arenaObs_siteProj_nonneg k)
      (arenaObs_siteProj_le_one k) hp₂ p hψ
      (echoSiteShown_diracTwoPointerFlow_iff J μ g₁ g₂ j k hf hh hc hch p θ ψ) ht0 ht⟩

/-! ### The equal superposition over the two sites -/

/-- The two indices of the split carrier are different when the sites are. -/
theorem split_ne {j k : ZMod (M + 1)} (hjk : j ≠ k) :
    ((k, 0) : ZMod (M + 1) × Fin 2) ≠ (j, 0) := fun e => hjk (congrArg Prod.fst e).symm

/-- **The split carrier**: the ray of `e_(k,0) + e_(j,0)`, an equal superposition over the two
detectors' sites. -/
noncomputable def splitRay {j k : ZMod (M + 1)} (hjk : j ≠ k) :
    GenArena (ZMod (M + 1) × Fin 2) :=
  pairRay (split_ne hjk) 1

/-- The split carrier has half its occupancy on the first detector's site. -/
theorem arenaObs_siteProj_splitRay_fst {j k : ZMod (M + 1)} (hjk : j ≠ k) :
    arenaObs (siteProj j) (splitRay hjk) = 1 / 2 := by
  rw [splitRay, arenaObs_siteProj_pairRay]
  norm_num

/-- The split carrier has half its occupancy on the second detector's site. -/
theorem arenaObs_siteProj_splitRay_snd {j k : ZMod (M + 1)} (hjk : j ≠ k) :
    arenaObs (siteProj k) (splitRay hjk) = 1 / 2 := by
  have hk : k ≠ j := fun e => hjk e.symm
  rw [splitRay, pairRay, arenaObs_siteProj_mk, norm_pairVec_sq (split_ne hjk)]
  simp [siteWeight, pairVec, hk]
  norm_num

/-- ★★★ **The equal superposition over two detectors' sites makes both display.** On a split
fibre, from two ready pointers: at the flow time `1/κ₁` both readouts are `true`. -/
theorem diracTwoPointerFlow_splitRay_double_display (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (hjk : j ≠ k) {θ ψ : KTorus} (hθ : θ ∈ readyArc 2)
    (hψ : ψ ∈ readyArc 2) (hx : (θ.2, ψ.2) ∈ splitFibres M J μ g₁ g₂ hf hh) {κ₁ : ℝ}
    (hκ₁ : κ₁ = rateAt g₁ 1 hf θ.2) :
    echoFstShown (2 * M + 1)
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch (1 / κ₁)
          ((diracArenaEquiv M (splitRay hjk), θ), ψ)) = true
      ∧ echoSiteShown (2 * M + 1)
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch (1 / κ₁)
          ((diracArenaEquiv M (splitRay hjk), θ), ψ)) = true :=
  diracTwoPointerFlow_double_display J μ g₁ g₂ j k hf hh hc hch hjk hθ hψ hx hκ₁
    (splitRay hjk) (by rw [arenaObs_siteProj_splitRay_fst]; norm_num)
    (by rw [arenaObs_siteProj_splitRay_snd]; norm_num)

end Double

end CSD.RecordLayer

end
