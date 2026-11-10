/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormDiagonal
public import CsdLean4.RecordLayer.DiracArrival
public import CsdLean4.RecordLayer.DiracPointerHamiltonian

/-!
# The pointer displacement a chain packet creates

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #351 — milestone **M2, part A** of the
author's programme "From `Σ` to physical spacetime" (2026-11-09): the first of the four statements
M2 keeps apart, *an interaction creating a pointer displacement*.

`RecordLayer/DiracPointerHamiltonian.lean` (#349) put a Dirac ring and a torus pointer on the arena
`Σ_* = ℂℙ^{2M+1} × T²` under one energy, and showed the pointer's rate at one point. It gave no
size and no time. This module bounds the displacement `diracPointerShift` over an interval, **along
the coupled carrier**, and identifies it with the registers of `RecordLayer/DiracDetector.lean`.

The difficulty is that the pointer integrates the occupancy of a carrier that feels the static site
potential `g f(θ₂) P_j`, which has no closed form on the ring. The Duhamel bound of
`Mathlib/Analysis/Matrix/DuhamelBound.lean` controls the difference from the free chain:

  `| shift(t) − (−2 g f'(θ₂)) ∫₀ᵗ ⟨P_j⟩_free | ≤ 2 |g| |f'(θ₂)| · |g f(θ₂)| t²`.

On a fibre with `f(θ₂) = 0` the potential is absent and the displacement is exact.

## The comparison with the free chain

* `abs_arenaObs_arenaKick_sub_le` — an arena observable read after two kicks differs by at most
  `2 ‖A‖ ‖U − V‖`; `norm_siteProj_le`;
* `diracCarrierU_zero_coupling_val` — at `g = 0` the carrier's propagator is `chainProp`;
  `diracCarrierU_of_lift_eq_zero` — and so it is on every fibre with `f(θ₂) = 0`;
* ★★ `norm_diracCarrierU_sub_le` — **the coupled propagator is within `|t| |g f(θ₂)|` of the free
  one**; `continuous_diracCarrierU`.

## The occupancy and the displacement

* `diracOccupancy` — the occupancy of site `j` along the carrier's orbit (`diracOccupancy_nonneg`,
  `diracOccupancy_le_one`, `continuous_diracOccupancy`, `integral_diracOccupancy_nonneg`,
  `integral_diracOccupancy_le`); `diracPointerShift_eq_integral`;
* ★★ `abs_diracOccupancy_sub_le`, `abs_integral_diracOccupancy_sub_le` — the coupled occupancy is
  within `2 |s| |g f(θ₂)|` of the free one, and its integral within `|g f(θ₂)| t²`;
* `abs_diracPointerShift`; ★ `abs_diracPointerShift_le` — **the pointer moves at most
  `2 |g| |f'(θ₂)| t`**; `diracPointerShift_of_deriv_eq_zero` — **at a zero of `f'` it does not
  move**;
* ★★★ `abs_diracPointerShift_sub_le` — **the displacement created**, the two-sided bound above;
  ★★★ `le_abs_diracPointerShift` — the lower bound;
* ★★ `diracPointerShift_of_lift_eq_zero` — **exact on a fibre with `f(θ₂) = 0`**;
* `diracPointerFlow_snd_fst` — the pointer coordinate of `diracPointerFlow` is the starting value
  plus the displacement.

## The registers of `DiracDetector.lean`

* `chainRay`, `norm_sq_toLp_chain`; ★ `diracOccupancy_zero_coupling_mk`,
  `diracOccupancy_zero_coupling_chainRay`, `diracOccupancy_zero_coupling_packet` — the free
  occupancy is `siteWeight` of the evolved state over the norm;
* ★★★ `diracPointerShift_eq_register` — **on a fibre with `f(θ₂) = 0` the displacement is the
  register of `detFlow`** (gain `g`, same site, prepared at zero) times `−2 f'(θ₂) / ⟨ψ, ψ⟩`;
* ★★ `abs_diracPointerShift_sub_register_le` — on every other fibre the two differ by at most
  `2 |g| |f'(θ₂)| · |g f(θ₂)| t²`.

## The two-mode packet (`twoMode`, the 12-site ring, `J = 4`, `μ = 3`)

* `twoMode_ne_zero`, `twoModeRay`; ★ `diracOccupancy_twoMode` — the free occupancy of site `k` is
  `(116 + 96 Re beat k s) / 1392`; `integral_diracOccupancy_twoMode`;
* ★★★ `diracPointerShift_twoMode_zero` — **profile `trainF`, fibre `θ₂ = 0`, detector at site `0`:
  the displacement is `g (116 t + 48 sin 2t) / 696`**, exactly;
  ★★ `diracPointerShift_twoMode_six` — at the opposite site `g (116 t − 48 sin 2t) / 696`;
* ★★★ `diracPointerFlow_twoMode` — **the same as a statement about `diracPointerFlow`**;
* ★★★ `le_abs_diracPointerShift_twoMode`, `abs_diracPointerShift_twoMode_sub_le` — **every profile,
  every fibre**: the displacement is within `2 |g| |f'(θ₂)| · |g f(θ₂)| t²` of
  `−2 g f'(θ₂) (116 t + 48 sin 2t)/1392`;
* ★★★ `le_abs_diracPointerShift_twoMode_quarter` — at `t = π/4`, on every fibre with
  `|g f(θ₂)| ≤ 1/10`, the pointer has moved at least `|g| |f'(θ₂)| / 14`.

## Honest scope

* **Exact versus approximate.** Exact: the displacement on fibres with `f(θ₂) = 0`, the register
  identification there, and the two closed forms. Bounds: everything on the other fibres. The
  error term `|g f(θ₂)| t²` is the first-order Duhamel estimate. It is not sharp, and it is
  quadratic in `t` where the signal is linear, so the lower bounds say something only up to a time
  of order the mean occupancy over `|g f(θ₂)|`, and nothing after it.
* **A displacement, not a record.** No readout region, ready state, threshold, outcome,
  persistence or `ActualOccurrence` is stated here. They are the other three statements of M2;
  the regions and the threshold are in `RecordLayer/DiracPointerThreshold.lean` (#352).
* **The pointer does not always move.** Every periodic `C¹` profile has a zero of `f'`
  (`exists_rateAt_eq_zero`); there `diracPointerShift_of_deriv_eq_zero` gives no displacement, and
  near it `abs_diracPointerShift_le` makes the pointer slow. No lower bound here is uniform in
  `θ₂`.
* **`twoMode` is a beating two-mode state, not a packet arriving from far away.** Its occupancy
  of site `k` is `(116 + 96 Re beat k s)/1392` with `beat` a unit phase (`norm_beat`), so it lies
  between `20/1392` and `212/1392` and never vanishes: a detector at any site is displaced, and
  the sites differ in how much (`0` against `6`). A carrier that starts with no weight at the
  detector and arrives later is not treated.
* **The identification with `detFlow` is of one coordinate.** A register of `DetArena` is a real
  number at each site, driven by the free packet's unnormalised weight; the pointer is one angle at
  one site, and what is identified is its lifted displacement before it is reduced to the circle.
  The `ActualOccurrence` structures of `DiracDetector.lean` (`packetDetector`, `twoModeDetector`)
  are not transported.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1), the
  coupling `−2 g f(θ₂) ⟨P_j⟩` (UA-5) and the Dirac propagation law (UA-8) are the definitions every
  statement here is about. The fibre `θ₂` on which a statement holds, the profile, the site and the
  carrier's initial ray are preparation input (UA-4); no law for `θ₂` is used and no measure
  appears. Nothing here is a statement about probabilities, Born weights, clocks or spacetime.

References: `specs/BACKLOG.md` #351, #349, #350, #252, #195; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UO-2, UO-6; UD-31 to UD-34);
`RecordLayer/DiracPointerHamiltonian.lean` (`diracPointerFlow_apply`, `diracPointerShift`,
`diracCarrierU`, `diracPointerH_isHermitian`, `hasDerivAt_diracCarrierU`, `arenaObs_siteProj_mk`,
`trainF_lift_zero`, `trainF_deriv_lift_zero`); `RecordLayer/DiracDetector.lean` (`siteWeight`,
`detFlow`, `register_detFlow`, `twoMode`, `siteWeight_twoMode`, `integral_twoMode`,
`chainInner_twoMode`, `beat_zero`, `beat_six`, `norm_beat`); `RecordLayer/DiracArrival.lean`
(`chainProp`, `chainProp_packet`); `RecordLayer/ActivatedWrite.lean` (`exists_rateAt_eq_zero`,
`transition_region`); `Mathlib/Analysis/Matrix/DuhamelBound.lean`
(`Matrix.norm_exp_smul_neg_I_sub_le`); `Mathlib/Analysis/Matrix/L2OpNormDiagonal.lean`
(`Matrix.l2_opNorm_diagonal_le`); `CV/ArenaBridge.lean` (`arenaObs_sub_le`, `arenaObs_kick_conj`,
`arenaKick_mk`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Two nearby unitaries give nearby readings -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **An arena observable read after two kicks** differs by at most `2 ‖A‖ ‖U − V‖`. -/
theorem abs_arenaObs_arenaKick_sub_le (U V : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ)
    (p : GenArena ι) :
    |arenaObs A (arenaKick U p) - arenaObs A (arenaKick V p)| ≤ 2 * ‖A‖ * ‖U.val - V.val‖ := by
  have hU : ‖U.val‖ = 1 := CStarRing.norm_of_mem_unitary U.property
  have hV : ‖V.val‖ = 1 := CStarRing.norm_of_mem_unitary V.property
  rw [arenaObs_kick_conj, arenaObs_kick_conj]
  refine (arenaObs_sub_le _ _ p).trans ?_
  have hsplit : star U.val * A * U.val - star V.val * A * V.val
      = star U.val * A * (U.val - V.val) + star (U.val - V.val) * A * V.val := by
    rw [star_sub]
    noncomm_ring
  rw [hsplit]
  calc ‖star U.val * A * (U.val - V.val) + star (U.val - V.val) * A * V.val‖
      ≤ ‖star U.val * A * (U.val - V.val)‖ + ‖star (U.val - V.val) * A * V.val‖ :=
        norm_add_le _ _
    _ ≤ ‖star U.val‖ * ‖A‖ * ‖U.val - V.val‖ + ‖star (U.val - V.val)‖ * ‖A‖ * ‖V.val‖ :=
        add_le_add (norm_mul₃_le) (norm_mul₃_le)
    _ = 2 * ‖A‖ * ‖U.val - V.val‖ := by
        rw [norm_star, norm_star, hU, hV]
        ring

end Generic

/-! ### The site projector and the free chain -/

section Site

variable {L : ℕ} [NeZero L]

/-- The site projector has operator norm at most `1`. -/
theorem norm_siteProj_le (j : ZMod L) : ‖siteProj j‖ ≤ 1 := by
  rw [siteProj]
  exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp

end Site

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-- With the coupling off, the carrier's propagator is the free chain's `e^{−itH_D}`. -/
theorem diracCarrierU_zero_coupling_val (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    (diracCarrierU J μ 0 j hf φ t).val = chainProp J μ t := by
  rw [diracCarrierU_val, chainProp, diracPointerH, zero_mul, Complex.ofReal_zero, zero_smul,
    add_zero]
  congr 1
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- On a fibre where the profile vanishes the carrier does not see the pointer: its propagator is
the uncoupled one. -/
theorem diracCarrierU_of_lift_eq_zero {φ : AddCircle (1 : ℝ)} (h : hf.lift φ = 0) (t : ℝ) :
    diracCarrierU J μ g j hf φ t = diracCarrierU J μ 0 j hf φ t := by
  apply Subtype.ext
  rw [diracCarrierU_val, diracCarrierU_val, diracPointerH, diracPointerH, h, mul_zero, zero_mul]

/-- ★★ **The coupled carrier stays within `|t| |g f(θ₂)|` of the free chain**, in operator norm:
the Duhamel bound for the static site potential `g f(θ₂) P_j`. -/
theorem norm_diracCarrierU_sub_le (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(diracCarrierU J μ g j hf φ t).val - (diracCarrierU J μ 0 j hf φ t).val‖
      ≤ |t| * |g * hf.lift φ| := by
  rw [diracCarrierU_val, diracCarrierU_val]
  refine (Matrix.norm_exp_smul_neg_I_sub_le _ _ (diracPointerH_isHermitian J μ g j hf φ)
    (diracPointerH_isHermitian J μ 0 j hf φ) t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
  have hd : diracPointerH J μ g j hf φ - diracPointerH J μ 0 j hf φ
      = ((g * hf.lift φ : ℝ) : ℂ) • siteProj j := by
    simp [diracPointerH]
  rw [hd, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_siteProj_le j)

/-- The carrier's propagator is continuous in time. -/
theorem continuous_diracCarrierU (φ : AddCircle (1 : ℝ)) :
    Continuous fun t : ℝ => diracCarrierU J μ g j hf φ t := by
  refine continuous_induced_rng.2 ?_
  exact continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_diracCarrierU J μ g j hf φ t).continuousAt

/-! ### The occupancy along the carrier's orbit -/

/-- **The occupancy of site `j` along the carrier's orbit** on the fibre `θ₂ = φ`: the coefficient
of the pointer's equation `θ̇₁ = −2 g f'(θ₂) ⟨P_j⟩`. At `g = 0` it is the free chain's. -/
noncomputable def diracOccupancy (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    (s : ℝ) : ℝ :=
  arenaObs (siteProj j) (arenaKick (diracCarrierU J μ g j hf φ s) p)

theorem diracOccupancy_nonneg (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    (s : ℝ) : 0 ≤ diracOccupancy J μ g j hf φ p s :=
  arenaObs_siteProj_nonneg j _

theorem diracOccupancy_le_one (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    (s : ℝ) : diracOccupancy J μ g j hf φ p s ≤ 1 :=
  arenaObs_siteProj_le_one j _

theorem continuous_diracOccupancy (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    Continuous fun s => diracOccupancy J μ g j hf φ p s :=
  (continuous_arenaObs (siteProj j)).comp
    ((continuous_diracCarrierU J μ g j hf φ).arenaKick continuous_const)

/-- The pointer's displacement is `−2 g f'(θ₂)` times the accumulated occupancy. -/
theorem diracPointerShift_eq_integral (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracPointerShift J μ g j hf φ p t
      = -(2 * g) * hf.deriv_periodic.lift φ * ∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s :=
  rfl

theorem integral_diracOccupancy_nonneg (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s :=
  intervalIntegral.integral_nonneg ht fun s _ => diracOccupancy_nonneg J μ g j hf φ p s

theorem integral_diracOccupancy_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s ≤ t := by
  have h := intervalIntegral.integral_mono_on ht
    ((continuous_diracOccupancy J μ g j hf φ p).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
    fun s _ => diracOccupancy_le_one J μ g j hf φ p s
  simpa using h

/-- ★★ **The coupled carrier's occupancy is within `2 |s| |g f(θ₂)|` of the free chain's.** -/
theorem abs_diracOccupancy_sub_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (s : ℝ) :
    |diracOccupancy J μ g j hf φ p s - diracOccupancy J μ 0 j hf φ p s|
      ≤ 2 * |s| * |g * hf.lift φ| := by
  refine (abs_arenaObs_arenaKick_sub_le _ _ (siteProj j) p).trans ?_
  calc 2 * ‖siteProj j‖ * ‖(diracCarrierU J μ g j hf φ s).val - (diracCarrierU J μ 0 j hf φ s).val‖
      ≤ 2 * 1 * (|s| * |g * hf.lift φ|) := by
        gcongr
        · exact norm_siteProj_le j
        · exact norm_diracCarrierU_sub_le J μ g j hf φ s
    _ = 2 * |s| * |g * hf.lift φ| := by ring

/-- ★★ **The accumulated occupancy is within `|g f(θ₂)| t²` of the free chain's.** -/
theorem abs_integral_diracOccupancy_sub_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s)
        - ∫ s in (0 : ℝ)..t, diracOccupancy J μ 0 j hf φ p s| ≤ |g * hf.lift φ| * t ^ 2 := by
  have hi : ∀ g' : ℝ, IntervalIntegrable (fun s => diracOccupancy J μ g' j hf φ p s) volume 0 t :=
    fun g' => (continuous_diracOccupancy J μ g' j hf φ p).intervalIntegrable 0 t
  rw [← intervalIntegral.integral_sub (hi g) (hi 0)]
  have hc : Continuous fun s : ℝ => 2 * s * |g * hf.lift φ| := by fun_prop
  have hab : Continuous fun s =>
      |diracOccupancy J μ g j hf φ p s - diracOccupancy J μ 0 j hf φ p s| :=
    ((continuous_diracOccupancy J μ g j hf φ p).sub
      (continuous_diracOccupancy J μ 0 j hf φ p)).abs
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine (intervalIntegral.integral_mono_on ht (hab.intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 t) fun s hs => ?_).trans_eq ?_
  · have h := abs_diracOccupancy_sub_le J μ g j hf φ p s
    rwa [abs_of_nonneg hs.1] at h
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring

/-! ### The displacement -/

/-- **A pointer on a fibre where `f'` vanishes does not move**, whatever the carrier does. -/
theorem diracPointerShift_of_deriv_eq_zero {φ : AddCircle (1 : ℝ)}
    (h : hf.deriv_periodic.lift φ = 0) (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracPointerShift J μ g j hf φ p t = 0 := by
  rw [diracPointerShift, h, mul_zero, zero_mul]

/-- The size of the displacement: `2 |g| |f'(θ₂)|` times the accumulated occupancy. -/
theorem abs_diracPointerShift (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ p t|
      = 2 * |g| * |hf.deriv_periodic.lift φ|
        * ∫ s in (0 : ℝ)..t, diracOccupancy J μ g j hf φ p s := by
  rw [diracPointerShift_eq_integral, abs_mul, abs_mul, abs_neg, abs_mul, abs_two,
    abs_of_nonneg (integral_diracOccupancy_nonneg J μ g j hf φ p ht)]

/-- ★ **The pointer moves at most `2 |g| |f'(θ₂)| t`**: the occupancy is at most `1`. Fibres with
small `|f'(θ₂)|` are slow. -/
theorem abs_diracPointerShift_le (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ p t| ≤ 2 * |g| * |hf.deriv_periodic.lift φ| * t := by
  rw [abs_diracPointerShift J μ g j hf φ p ht]
  exact mul_le_mul_of_nonneg_left (integral_diracOccupancy_le J μ g j hf φ p ht) (by positivity)

/-- ★★★ **The displacement created, along the coupled carrier.** On every fibre `θ₂ = φ` the
pointer's displacement is within `2 |g| |f'(φ)| · |g f(φ)| t²` of `−2 g f'(φ)` times the occupancy
accumulated by the **free** chain. The error is the price of the static site potential the carrier
sees. -/
theorem abs_diracPointerShift_sub_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ p t
        - -(2 * g) * hf.deriv_periodic.lift φ * ∫ s in (0 : ℝ)..t, diracOccupancy J μ 0 j hf φ p s|
      ≤ 2 * |g| * |hf.deriv_periodic.lift φ| * (|g * hf.lift φ| * t ^ 2) := by
  rw [diracPointerShift_eq_integral, ← mul_sub, abs_mul, abs_mul, abs_neg, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (abs_integral_diracOccupancy_sub_le J μ g j hf φ p ht)
    (by positivity)

/-- ★★★ **A lower bound on the displacement**, for every fibre: the free chain's accumulated
occupancy, less `|g f(θ₂)| t²`, at the rate `2 |g| |f'(θ₂)|`. -/
theorem le_abs_diracPointerShift (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    {t : ℝ} (ht : 0 ≤ t) :
    2 * |g| * |hf.deriv_periodic.lift φ|
        * ((∫ s in (0 : ℝ)..t, diracOccupancy J μ 0 j hf φ p s) - |g * hf.lift φ| * t ^ 2)
      ≤ |diracPointerShift J μ g j hf φ p t| := by
  rw [abs_diracPointerShift J μ g j hf φ p ht]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := (abs_le.1 (abs_integral_diracOccupancy_sub_le J μ g j hf φ p ht)).1
  linarith

/-- ★★ **On a fibre where the profile vanishes the displacement is exact**: `−2 g f'(θ₂)` times
the free chain's accumulated occupancy. -/
theorem diracPointerShift_of_lift_eq_zero {φ : AddCircle (1 : ℝ)} (h : hf.lift φ = 0)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracPointerShift J μ g j hf φ p t
      = -(2 * g) * hf.deriv_periodic.lift φ
        * ∫ s in (0 : ℝ)..t, diracOccupancy J μ 0 j hf φ p s := by
  rw [diracPointerShift_eq_integral]
  congr 2
  funext s
  rw [diracOccupancy, diracOccupancy, diracCarrierU_of_lift_eq_zero J μ g j hf h]

/-! ### The free occupancy is the site weight of `DiracDetector.lean` -/

/-- ★ **The free occupancy at the ray of `ψ`** is the weight of `e^{−isH_D} ψ` on site `j`, over
`‖ψ‖²`. -/
theorem diracOccupancy_zero_coupling_mk (φ : AddCircle (1 : ℝ))
    {ψ : EuclideanSpace ℂ (ZMod (M + 1) × Fin 2)} (hψ : ψ ≠ 0) (s : ℝ) :
    diracOccupancy J μ 0 j hf φ (Projectivization.mk ℂ ψ hψ) s
      = siteWeight (chainProp J μ s *ᵥ ⇑ψ) j / ‖ψ‖ ^ 2 := by
  have hU : ((diracCarrierU J μ 0 j hf φ s).val)ᴴ * (diracCarrierU J μ 0 j hf φ s).val = 1 := by
    have hmem := (diracCarrierU J μ 0 j hf φ s).property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  rw [diracOccupancy, arenaKick_mk _ hψ, arenaObs_siteProj_mk,
    Matrix.norm_toEuclideanLin_of_isom hU ψ]
  congr 2
  rw [← diracCarrierU_zero_coupling_val J μ j hf φ s]
  rfl

/-- The pointer coordinate of the joint flow: the ready value plus the displacement. -/
theorem diracPointerFlow_snd_fst (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) :
    (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, θ)).2.1
      = θ.1 + ((diracPointerShift J μ g j hf θ.2 p t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [diracPointerFlow_apply]

/-! ### Chain states, packets, and the registers of `DiracDetector.lean` -/

/-- **The ray of a chain state** `ψ ≠ 0`, a point of the Dirac arena. -/
noncomputable def chainRay (ψ : ZMod (M + 1) × Fin 2 → ℂ) (hψ : ψ ≠ 0) :
    GenArena (ZMod (M + 1) × Fin 2) :=
  Projectivization.mk ℂ (WithLp.toLp 2 ψ) (by simpa using hψ)

theorem norm_sq_toLp_chain (ψ : ZMod (M + 1) × Fin 2 → ℂ) :
    ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (ZMod (M + 1) × Fin 2))‖ ^ 2 = (chainInner ψ ψ).re := by
  rw [EuclideanSpace.norm_sq_eq, re_chainInner_self]

/-- ★ **The free occupancy at a chain state** is the site weight of the evolved state over the
norm. -/
theorem diracOccupancy_zero_coupling_chainRay (φ : AddCircle (1 : ℝ))
    {ψ : ZMod (M + 1) × Fin 2 → ℂ} (hψ : ψ ≠ 0) (s : ℝ) :
    diracOccupancy J μ 0 j hf φ (chainRay ψ hψ) s
      = siteWeight (chainProp J μ s *ᵥ ψ) j / (chainInner ψ ψ).re := by
  rw [chainRay, diracOccupancy_zero_coupling_mk, norm_sq_toLp_chain]

/-- ★ **Along a packet the free occupancy is the packet's site weight over its norm.** -/
theorem diracOccupancy_zero_coupling_packet (φ : AddCircle (1 : ℝ)) (W : Finset ℤ) (a : ℤ → ℂ)
    (hp : packet (L := M + 1) J μ W a 0 ≠ 0) (s : ℝ) :
    diracOccupancy J μ 0 j hf φ (chainRay (packet (L := M + 1) J μ W a 0) hp) s
      = siteWeight (packet (L := M + 1) J μ W a s) j
        / (chainInner (packet (L := M + 1) J μ W a 0) (packet (L := M + 1) J μ W a 0)).re := by
  rw [diracOccupancy_zero_coupling_chainRay, chainProp_packet]

/-- ★★★ **The registers of `DiracDetector.lean` are this flow's pointer** on a fibre where the
profile vanishes: there the pointer's displacement is the register of gain `g` at the same site,
prepared at zero, times the constant `−2 f'(θ₂) / ⟨ψ, ψ⟩`. -/
theorem diracPointerShift_eq_register {φ : AddCircle (1 : ℝ)} (h : hf.lift φ = 0) (W : Finset ℤ)
    (a : ℤ → ℂ) (hp : packet (L := M + 1) J μ W a 0 ≠ 0) (t : ℝ) :
    diracPointerShift J μ g j hf φ (chainRay (packet (L := M + 1) J μ W a 0) hp) t
      = -(2 * hf.deriv_periodic.lift φ)
        / (chainInner (packet (L := M + 1) J μ W a 0) (packet (L := M + 1) J μ W a 0)).re
        * (detFlow (L := M + 1) J μ g W t (a, 0)).2 j := by
  rw [diracPointerShift_of_lift_eq_zero J μ g j hf h, register_detFlow]
  simp_rw [diracOccupancy_zero_coupling_packet]
  rw [intervalIntegral.integral_div, Pi.zero_apply, zero_add]
  ring

/-- ★★ **Off those fibres, how the pointer and the register differ**: on every fibre the
displacement is within `2 |g| |f'(θ₂)| · |g f(θ₂)| t²` of the same multiple of the register. The
register integrates the free packet; the pointer integrates the carrier that feels the site
potential. -/
theorem abs_diracPointerShift_sub_register_le (φ : AddCircle (1 : ℝ)) (W : Finset ℤ)
    (a : ℤ → ℂ) (hp : packet (L := M + 1) J μ W a 0 ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ (chainRay (packet (L := M + 1) J μ W a 0) hp) t
        - -(2 * hf.deriv_periodic.lift φ)
          / (chainInner (packet (L := M + 1) J μ W a 0) (packet (L := M + 1) J μ W a 0)).re
          * (detFlow (L := M + 1) J μ g W t (a, 0)).2 j|
      ≤ 2 * |g| * |hf.deriv_periodic.lift φ| * (|g * hf.lift φ| * t ^ 2) := by
  have h := abs_diracPointerShift_sub_le J μ g j hf φ
    (chainRay (packet (L := M + 1) J μ W a 0) hp) ht
  simp_rw [diracOccupancy_zero_coupling_packet] at h
  rw [intervalIntegral.integral_div] at h
  rw [register_detFlow]
  dsimp only
  rw [Pi.zero_apply, zero_add]
  convert h using 3
  ring

end Arena

/-! ### The two-mode packet at the pointer -/

section TwoMode

theorem twoMode_ne_zero : twoMode 0 ≠ 0 := fun h => by
  have h0 := chainInner_twoMode 0
  rw [h] at h0
  simp [chainInner] at h0

/-- **The two-mode packet's initial ray** on the arena of the `12`-site ring, `ℂℙ²³ × T²`. -/
noncomputable def twoModeRay : GenArena (ZMod (11 + 1) × Fin 2) :=
  chainRay (M := 11) (twoMode 0) twoMode_ne_zero

variable {f : ℝ → ℝ} (hf : Function.Periodic f 1)

/-- ★ **The free occupancy of site `k` along the two-mode packet**:
`(116 + 96 cos(πk/6 − 2s)) / 1392`. -/
theorem diracOccupancy_twoMode (k : ZMod 12) (φ : AddCircle (1 : ℝ)) (s : ℝ) :
    diracOccupancy (M := 11) 4 3 0 k hf φ twoModeRay s = (116 + 96 * (beat k s).re) / 1392 := by
  have h := diracOccupancy_zero_coupling_packet (M := 11) 4 3 k hf φ {0, 1} 1 twoMode_ne_zero s
  have hN : (chainInner (packet (L := 11 + 1) 4 3 {0, 1} 1 0)
      (packet (L := 11 + 1) 4 3 {0, 1} 1 0)).re = 1392 := by
    have := chainInner_twoMode 0
    exact (congrArg Complex.re this).trans (by norm_num)
  rw [hN] at h
  exact h.trans (congrArg (· / 1392) (siteWeight_twoMode s k))

theorem integral_diracOccupancy_twoMode (c : ℝ) (k : ZMod 12)
    (hk : ∀ s, (beat k s).re = c * Real.cos (2 * s)) (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, diracOccupancy (M := 11) 4 3 0 k hf φ twoModeRay s
      = (116 * t + c * 48 * Real.sin (2 * t)) / 1392 := by
  simp_rw [diracOccupancy_twoMode hf k φ]
  rw [intervalIntegral.integral_div]
  congr 1
  have h := integral_twoMode c k hk t
  simp_rw [siteWeight_twoMode] at h
  exact h

/-- ★★★ **The displacement the two-mode packet creates, in closed form.** With the profile
`trainF` on the fibre `θ₂ = 0`, the pointer at site `0` (where the packet's weight starts at its
peak) has moved `g (116 t + 48 sin 2t) / 696` at time `t`. -/
theorem diracPointerShift_twoMode_zero (g t : ℝ) :
    diracPointerShift (M := 11) 4 3 g 0 trainF_periodic 0 twoModeRay t
      = g * (116 * t + 48 * Real.sin (2 * t)) / 696 := by
  rw [diracPointerShift_of_lift_eq_zero 4 3 g 0 trainF_periodic trainF_lift_zero,
    trainF_deriv_lift_zero, integral_diracOccupancy_twoMode trainF_periodic 1 0
      (fun s => by rw [beat_zero, one_mul])]
  ring

/-- ★★ **The same packet at the opposite site**: a pointer coupled to site `6` has moved
`g (116 t − 48 sin 2t) / 696`. -/
theorem diracPointerShift_twoMode_six (g t : ℝ) :
    diracPointerShift (M := 11) 4 3 g 6 trainF_periodic 0 twoModeRay t
      = g * (116 * t - 48 * Real.sin (2 * t)) / 696 := by
  rw [diracPointerShift_of_lift_eq_zero 4 3 g 6 trainF_periodic trainF_lift_zero,
    trainF_deriv_lift_zero, integral_diracOccupancy_twoMode trainF_periodic (-1) 6
      (fun s => by rw [beat_six]; ring)]
  ring

/-- ★★★ **The displacement is a statement about the Hamiltonian flow**: from the two-mode packet
and the pointer at `(0, 0)`, the pointer coordinate of `diracPointerFlow` at time `t` is
`g (116 t + 48 sin 2t) / 696`, on the circle. -/
theorem diracPointerFlow_twoMode (g t : ℝ) :
    (diracPointerFlow (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF t
        (diracArenaEquiv 11 twoModeRay, ((0, 0) : KTorus))).2.1
      = ((g * (116 * t + 48 * Real.sin (2 * t)) / 696 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [diracPointerFlow_snd_fst, diracPointerShift_twoMode_zero, zero_add]

/-- ★★★ **Off the exact fibre: a lower bound for every profile and every `θ₂`.** The two-mode
packet moves the pointer at site `0` by at least
`2 |g| |f'(θ₂)| ((116 t + 48 sin 2t)/1392 − |g f(θ₂)| t²)`. -/
theorem le_abs_diracPointerShift_twoMode (g : ℝ) (φ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    2 * |g| * |hf.deriv_periodic.lift φ|
        * ((116 * t + 48 * Real.sin (2 * t)) / 1392 - |g * hf.lift φ| * t ^ 2)
      ≤ |diracPointerShift (M := 11) 4 3 g 0 hf φ twoModeRay t| := by
  have h := le_abs_diracPointerShift (M := 11) 4 3 g 0 hf φ twoModeRay ht
  rwa [integral_diracOccupancy_twoMode hf 1 0 (fun s => by rw [beat_zero, one_mul]),
    one_mul] at h

/-- ★★ **The two-sided form**: the displacement is within `2 |g| |f'(θ₂)| · |g f(θ₂)| t²` of
`−2 g f'(θ₂) (116 t + 48 sin 2t)/1392`. -/
theorem abs_diracPointerShift_twoMode_sub_le (g : ℝ) (φ : AddCircle (1 : ℝ)) {t : ℝ}
    (ht : 0 ≤ t) :
    |diracPointerShift (M := 11) 4 3 g 0 hf φ twoModeRay t
        - -(2 * g) * hf.deriv_periodic.lift φ * ((116 * t + 48 * Real.sin (2 * t)) / 1392)|
      ≤ 2 * |g| * |hf.deriv_periodic.lift φ| * (|g * hf.lift φ| * t ^ 2) := by
  have h := abs_diracPointerShift_sub_le (M := 11) 4 3 g 0 hf φ twoModeRay ht
  rwa [integral_diracOccupancy_twoMode hf 1 0 (fun s => by rw [beat_zero, one_mul]),
    one_mul] at h

/-- ★★★ **A displacement of definite size by `t = π/4`, on every fibre with `|g f(θ₂)| ≤ 1/10`**:
at least `|g| |f'(θ₂)| / 14`. -/
theorem le_abs_diracPointerShift_twoMode_quarter (g : ℝ) (φ : AddCircle (1 : ℝ))
    (h : |g * hf.lift φ| ≤ 1 / 10) :
    |g| * |hf.deriv_periodic.lift φ| / 14
      ≤ |diracPointerShift (M := 11) 4 3 g 0 hf φ twoModeRay (Real.pi / 4)| := by
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  refine le_trans ?_ (le_abs_diracPointerShift_twoMode hf g φ (by positivity))
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have hsq : |g * hf.lift φ| * (Real.pi / 4) ^ 2 ≤ 1 / 10 * (Real.pi / 4) ^ 2 :=
    mul_le_mul_of_nonneg_right h (sq_nonneg _)
  have hb : (1 : ℝ) / 28
      ≤ (116 * (Real.pi / 4) + 48 * 1) / 1392 - |g * hf.lift φ| * (Real.pi / 4) ^ 2 := by
    nlinarith [Real.pi_pos]
  calc |g| * |hf.deriv_periodic.lift φ| / 14
      = 2 * |g| * |hf.deriv_periodic.lift φ| * (1 / 28) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

end TwoMode

end CSD.RecordLayer

end
