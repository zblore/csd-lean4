/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracReturn

/-!
# The Doppler factor of the Dirac chain, read off the records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #256, re-scoped to one way (the two-way radar
version needs a return from a moving observer, #274).

Two messengers pass the observer at rest `A` (#253) on their way to an observer `B` approaching at
`3/5`. Each passage is recorded at `A`, each arrival at `B`, and both observers keep time with their own
Dirac clocks (~~#272~~). Between the two arrivals `B`'s clock counts **21 to 26** ticks; between the two
passages `A`'s counts **49 to 53**. The ratio lies in `[21/53, 26/49]`, which contains the
relativistic factor `v√(1 − β²)/(v + β) = 16/35` for messengers of speed `v = 4/5` — the kinematic
compression times `B`'s slow clock — and excludes the Galilean `v/(v + β) = 4/7`.

## Generic pieces

* `chainProp_ringPacket`, `deviceProp_devicePacket_shift` (evolving from any time);
  `norm_sum_shift_le`, ★★ `levelCoherence_shift_sharp` — **the device's clock drifts from any start
  at the sharp rate**;
* `devSiteWeight_levelLift`, `devRegionWeight_levelLift` (a messenger as a one-level device);
  `offset_mem_of_near_at`, `offset_not_mem_of_far_at` (encounter windows about moving centres).

## The approaching observer

* `approachObserver` (momentum `9/4`, velocity `3/5`), `approach_spread`, `vRel_approach`,
  `omega_approach`, `approach_win`; ★★ `approach_tail`, `image_tail_any` (each within chord `1/50` of its
  prediction at any time `|s| ≤ 8·10¹³`, but for `6·10⁻³`); `approach_total`, `image_total`;
* ★★ `approach_rate` — **its splitting is in `[8·10⁻¹², 8.002·10⁻¹²]`**, four fifths of the rest
  splitting; `approach_drift`, `approach_coherence_ge`, `approachTick` — **its ticks, counted from its
  preparation `5·10¹³` before it reaches `A`**.

## The weights along the way

* `star_exp_I_mul`, `rel_offset`; ★ `emission_near`, ★ `emission_far` (a messenger at `A` and away);
  ★ `reception_near`, ★ `reception_far` (a messenger at `B` and away); `rel_approach_le_one`,
  `image_le_one`.

## The arena and the records

* `DopArena`, `dopFlow`, `dopEm₁`, `dopEm₂`, `dopRc₁`, `dopRc₂`, `dopWeight`, `dopFlow_zero`,
  `dopFlow_add`, `measurable_dopFlow`, `continuous_levelLift_zero`, `continuous_dopWeight`, `dopPrep`,
  `dopFlow_prep_messenger₁`, `dopFlow_prep_messenger₂`, `dopFlow_prep_approach`, `dopFlow_prep_rest`,
  `continuous_dopWeight_prep`, `dopWeight_prep_em₁`, `dopWeight_prep_em₂`, `dopWeight_prep_rc₁`,
  `dopWeight_prep_rc₂`;
* `dop_emission_before`, `dop_emission_after`, `dop_reception_before`, `dop_reception_after`;
  ★★★ `dopEmission₁`, `dopEmission₂`, `dopReception₁`, `dopReception₂`; `restTickDop`,
  `approachTickDop`; the `_fields` lemmas.

## The factor

* ★★★ `dirac_doppler` — **one evolution carrying both clocks and both messengers; the emissions and
  receptions written in explicit windows; `A`'s ticks at `n · 2π·10¹¹`, `B`'s at `2πn/R`; the
  emissions between `A`'s ticks `4`–`6` and `55`–`57`, the receptions between `B`'s ticks `29`–`31` and
  `52`–`55`; the tick-count ratio in `[21/53, 26/49] ∋ 16/35`, excluding the Galilean `4/7`.**

## The finding

**The Doppler factor read off the records is the relativistic one.** The ratio of the receiver's
ticks between arrivals to the sender's ticks between emissions is `16/35 = (v/(v + β)) · √(1 − β²)`:
the kinematic compression of the arrivals times the receiver's dilated clock. Without the dilation it
would be `4/7`, which the records exclude. With messengers at the chain's `c` the factor would be
`√((1 − β)/(1 + β)) = 1/2`, which the bracket also contains; the messengers here are slower than `c`.

## Honest scope

⚠️ **One way.** The two-way (radar) factor needs the messenger returned by the moving observer, and
an actual occurrence needs reversible dynamics, so a relay at a moving observer is a hybrid flow with
a transversal switching surface (#274).

⚠️ **The emissions are prepared**: the messengers are set on their way upstream and `A` records their
passage, as in ~~#244~~ (launching is #254).

⚠️ **The messengers move at `4/5`, below the chain's `c`**, so the factor measured is
`v√(1 − β²)/(v + β)`; its `v → c` limit is `√((1 − β)/(1 + β))`, not reached on the chain (~~#246~~).

⚠️ **The detectors are calibrated test detectors** of a stated law (#251, #266, #273); the clocks
are #262's devices with #272's drifting ticks.

References: `specs/BACKLOG.md` #256, #253, #272, #270, #274, #244, #246, #254, #251, #266, #273, #39;
`RecordLayer/DiracTwin.lean` (`restObserver`, `twinRestTick`, `twin_budget`, `twin_rest_rate`);
`RecordLayer/DiracReturn.lean` (`imagePacket`, `chordArc_subset`, `integral_le_three`);
`RecordLayer/DiracDeviceTicks.lean` (`driftTickDetector`, `deviceTick_facts`, `deviceDrift`);
`RecordLayer/DiracObservers.lean` (`relWeight`, `regDetector`); `CV/DiracDevice.lean`
(`levelCoherence_rate_sharp`, `abs_levelClockRate_sub_le`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### Evolving from any time -/

theorem chainProp_ringPacket (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (s t : ℝ) :
    chainProp (L := L) (scaledHop c (ℓ / L)) μ t *ᵥ ringPacket c μ ℓ W β s
      = ringPacket c μ ℓ W β (s + t) := by
  rw [ringPacket, ringPacket, ← chainProp_packet _ _ _ _ s, ← chainProp_packet _ _ _ _ (s + t),
    Matrix.mulVec_mulVec, chainProp_add]

theorem deviceProp_devicePacket_shift (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (s t : ℝ) :
    deviceProp (L := L) J μ₀ μ₁ t *ᵥ devicePacket J μ₀ μ₁ W β s = devicePacket J μ₀ μ₁ W β (s + t) := by
  rw [← deviceProp_devicePacket _ _ _ _ _ s, ← deviceProp_devicePacket _ _ _ _ _ (s + t),
    Matrix.mulVec_mulVec, deviceProp_add]

/-- **Phases from any start**: `‖Σ w_m e^{iΔ_m(t₁+s)} − e^{iΩs} Σ w_m e^{iΔ_m t₁}‖ ≤ |s| Σ |w_m| |Δ_m − Ω|`. -/
theorem norm_sum_shift_le (W : Finset ℤ) (w : ℤ → ℂ) (Δ : ℤ → ℝ) (Ω t₁ s : ℝ) :
    ‖∑ m ∈ W, w m * exp (I * ((Δ m : ℂ) * ((t₁ + s : ℝ) : ℂ)))
        - exp (I * ((Ω : ℂ) * (s : ℂ))) * ∑ m ∈ W, w m * exp (I * ((Δ m : ℂ) * (t₁ : ℂ)))‖
      ≤ |s| * ∑ m ∈ W, ‖w m‖ * |Δ m - Ω| := by
  have e : ∑ m ∈ W, w m * exp (I * ((Δ m : ℂ) * ((t₁ + s : ℝ) : ℂ)))
      = ∑ m ∈ W, (w m * exp (I * ((Δ m : ℂ) * (t₁ : ℂ)))) * exp (I * ((Δ m : ℂ) * (s : ℂ))) :=
    Finset.sum_congr rfl fun m _ => by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  rw [e]
  refine (norm_sum_phase_sub_le W _ Δ Ω s).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [norm_mul, show I * ((Δ m : ℂ) * (t₁ : ℂ)) = ((Δ m * t₁ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- ★★ **The device's clock from any start**: the coherence at `t₁ + s` is within `|s|` times the
sharp drift of the coherence at `t₁` turned through `−Rs`. -/
theorem levelCoherence_shift_sharp {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (hℓ : 0 < ℓ) {W : Finset ℤ} (hD : Distinct L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₁ s : ℝ) :
    ‖levelCoherence (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W
          (unitAmp L (scaledHop c (ℓ / L)) μ₀ β) (unitAmp L (scaledHop c (ℓ / L)) μ₁ β) (t₁ + s)
        - exp (I * (((-levelClockRate μ₀ μ₁ (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) : ℝ)
            : ℂ) * s))
          * levelCoherence (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W
            (unitAmp L (scaledHop c (ℓ / L)) μ₀ β) (unitAmp L (scaledHop c (ℓ / L)) μ₁ β) t₁‖
      ≤ |s| * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2)) := by
  set J := scaledHop c (ℓ / L)
  rw [levelCoherence_eq J μ₀ μ₁ hD _ _ (t₁ + s), levelCoherence_eq J μ₀ μ₁ hD _ _ t₁]
  refine (norm_sum_shift_le W _ _ _ t₁ s).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
  set K := c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2)
  calc ∑ m ∈ W, ‖levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m‖
        * |(bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m))
          - -levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))|
      ≤ ∑ m ∈ W, ‖β m‖ ^ 2 * K := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hw := (levelWeight_unitAmp_bounds (L := L) (J := J) h0 h01 β m).2
        have hR : |(bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m))
            - -levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))|
            = |levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))
              - levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))| := by
          rw [← abs_neg]
          congr 1
          rw [levelClockRate, levelClockRate, bandE, bandE]
          ring
        have hK : |levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))
            - levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))| ≤ K := by
          refine (abs_levelClockRate_sub_le h0 h01 _ _).trans ?_
          have hΔ : 0 ≤ μ₁ - μ₀ := by linarith
          have hX := abs_sq_sub_sq_scaled_le (L := L) hc hℓ (hWD m hm)
          simp only [K]
          gcongr
        rw [hR]
        exact mul_le_mul hw hK (abs_nonneg _) (sq_nonneg _)
    _ = K := by rw [← Finset.sum_mul, hβ, one_mul]

/-! ### A messenger as a device of one level -/

omit [NeZero L] in
theorem devSiteWeight_levelLift (ψ : ZMod L × Fin 2 → ℂ) (k : ZMod L) :
    devSiteWeight (levelLift 0 ψ) k = siteWeight ψ k := by
  simp [devSiteWeight, levelLift, siteWeight, Fin.sum_univ_two]

omit [NeZero L] in
theorem devRegionWeight_levelLift (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    devRegionWeight (levelLift 0 ψ) A = regionWeight ψ A := by
  simp only [devRegionWeight, devSiteWeight_levelLift, regionWeight]

/-- **Offsets near the window, about moving centres**: if `A`'s site is within `ρA` of `uA`, `B`'s
within `ρB` of `uB`, and `|uB ūA − w| + ρA + ρB ≤ ρ`, the offset is in the window. -/
theorem offset_mem_of_near_at {j k : ZMod L} {uA uB w : ℂ} {ρA ρB ρ : ℝ} (huB : ‖uB‖ = 1) (hj : ‖(ZMod.toCircle j : ℂ) - uA‖ ≤ ρA)
    (hk : ‖(ZMod.toCircle k : ℂ) - uB‖ ≤ ρB) (h : ‖uB * star uA - w‖ + ρA + ρB ≤ ρ) :
    ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ := by
  have e : (ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w
      = ((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ)
        + uB * star ((ZMod.toCircle j : ℂ) - uA) + (uB * star uA - w) := by
    rw [star_sub]
    ring
  have h1 : ‖((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ)‖
      = ‖(ZMod.toCircle k : ℂ) - uB‖ := by
    rw [norm_mul, norm_star_of_norm (Circle.norm_coe _), mul_one]
  have h2 : ‖uB * star ((ZMod.toCircle j : ℂ) - uA)‖ = ‖(ZMod.toCircle j : ℂ) - uA‖ := by
    rw [norm_mul, huB, one_mul, Complex.star_def, Complex.norm_conj]
  rw [e]
  have := norm_add₃_le (a := ((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ))
    (b := uB * star ((ZMod.toCircle j : ℂ) - uA)) (c := uB * star uA - w)
  linarith

/-- **Offsets far from the window, about moving centres**: if `ρ + ρA + ρB < |uB ūA − w|`, the
offset is out of it. -/
theorem offset_not_mem_of_far_at {j k : ZMod L} {uA uB w : ℂ} {ρA ρB ρ : ℝ} (huB : ‖uB‖ = 1) (hj : ‖(ZMod.toCircle j : ℂ) - uA‖ ≤ ρA)
    (hk : ‖(ZMod.toCircle k : ℂ) - uB‖ ≤ ρB) (h : ρ + ρA + ρB < ‖uB * star uA - w‖) :
    ρ < ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ := by
  have e : uB * star uA - w = ((ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w)
      - ((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ)
      - uB * star ((ZMod.toCircle j : ℂ) - uA) := by
    rw [star_sub]
    ring
  have h1 : ‖((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ)‖
      = ‖(ZMod.toCircle k : ℂ) - uB‖ := by
    rw [norm_mul, norm_star_of_norm (Circle.norm_coe _), mul_one]
  have h2 : ‖uB * star ((ZMod.toCircle j : ℂ) - uA)‖ = ‖(ZMod.toCircle j : ℂ) - uA‖ := by
    rw [norm_mul, huB, one_mul, Complex.star_def, Complex.norm_conj]
  rw [e] at h
  have t1 := norm_sub_le ((ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w
      - ((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ))
    (uB * star ((ZMod.toCircle j : ℂ) - uA))
  have t2 := norm_sub_le ((ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w)
    (((ZMod.toCircle k : ℂ) - uB) * star (ZMod.toCircle j : ℂ))
  linarith

/-! ### The approaching observer -/

/-- **The approaching observer**: #262's device, rest energies `3` and `3 + 10⁻¹¹`, modes
`[2.25·10¹³, 2.25·10¹³ + 2·10⁶)` about momentum `9/4` — velocity `3/5`. -/
noncomputable def approachObserver (t : ℝ) : (ZMod L × Fin 2) × Fin 2 → ℂ :=
  devicePacket (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11)
    (Finset.Ico (225 * 10 ^ 11 : ℤ) (225 * 10 ^ 11 + (2000000 : ℕ))) twinAmp t

omit [NeZero L] in
theorem approach_spread : ∀ m ∈ Finset.Ico (225 * 10 ^ 11 : ℤ) (225 * 10 ^ 11 + (2000000 : ℕ)),
    |2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) - 9 / 4| ≤ 2 / 10 ^ 7 := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have hm' : (225 * 10 ^ 11 : ℝ) ≤ m ∧ (m : ℝ) ≤ 225 * 10 ^ 11 + 1999999 := by
    constructor <;> exact_mod_cast (by omega)
  rw [show 2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) = m / 10 ^ 13 by field_simp, abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    nlinarith [hm'.1]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]
    nlinarith [hm'.2]

omit [NeZero L] in
theorem vRel_approach : vRel 1 3 (1 * (9 / 4)) = 3 / 5 := by
  rw [vRel, dispE, show (3 : ℝ) ^ 2 + (1 * (9 / 4)) ^ 2 = (15 / 4) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

omit [NeZero L] in
theorem omega_approach :
    2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 3 (1 * (9 / 4)) = 6 / 10 ^ 14 := by
  rw [vRel_approach]
  field_simp
  norm_num

section Approach

variable (hL : 10 ^ 19 ≤ L)
include hL

omit [NeZero L] in
theorem approach_win : ∀ m ∈ Finset.Ico (225 * 10 ^ 11 : ℤ) (225 * 10 ^ 11 + (2000000 : ℕ)),
    225 * 10 ^ 11 ≤ m ∧ m + 1 < 225 * 10 ^ 11 + L := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  constructor <;> omega

/-- **Where the approaching observer is**, at any time `|s| ≤ 8·10¹³`: within chord `1/50` of
`e^{iΩs}`, `Ω = 6·10⁻¹⁴`, but for `6·10⁻³` of its weight. -/
theorem approach_tail {s : ℝ} (hs : |s| ≤ 8 * 10 ^ 13) :
    devRegionWeight (approachObserver (L := L) s)
        (chordArc (exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))) (1 / 50))ᶜ ≤ 6 / 1000 := by
  have hz₀ : ‖exp (I * ((2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 3 (1 * (9 / 4)) * s : ℝ)
      : ℂ)) - exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))‖ ≤ 1 / 10 ^ 9 := by
    rw [omega_approach, sub_self, norm_zero]
    positivity
  have hz₁ : ‖exp (I * ((2 * Real.pi / (2 * Real.pi * 10 ^ 13)
      * vRel 1 (3 + 1 / 10 ^ 11) (1 * (9 / 4)) * s : ℝ) : ℂ))
      - exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))‖ ≤ 1 / 10 ^ 9 := by
    refine (norm_exp_sub_exp_le _ _).trans ?_
    have hv := abs_vRel_sub_le (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11) (by norm_num)
      (by norm_num) (by norm_num) (1 * (9 / 4))
    rw [vRel_approach] at hv
    have hk : 2 * Real.pi / (2 * Real.pi * 10 ^ 13) = 1 / 10 ^ 13 := by field_simp
    rw [hk, show 1 / 10 ^ 13 * vRel 1 (3 + 1 / 10 ^ 11) (1 * (9 / 4)) * s - 6 / 10 ^ 14 * s
        = 1 / 10 ^ 13 * s * (vRel 1 (3 + 1 / 10 ^ 11) (1 * (9 / 4)) - 3 / 5) by ring, abs_mul,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10 ^ 13)]
    calc 1 / 10 ^ 13 * |s| * |vRel 1 (3 + 1 / 10 ^ 11) (1 * (9 / 4)) - 3 / 5|
        ≤ 1 / 10 ^ 13 * (8 * 10 ^ 13) * (1 * (3 + 1 / 10 ^ 11 - 3) / 3) := by gcongr
      _ ≤ 1 / 10 ^ 9 := by norm_num
  have h := devRegionWeight_compl_chordArc_le (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (P := 9 / 4) (D := 2 / 10 ^ 7) (p₀ := 9 / 4) one_pos (by norm_num)
    (by norm_num) (by positivity) (by norm_num) (by positivity) (approach_win hL) approach_spread
    twinAmp (twin_norm hL _) (z := exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))) (ρ := 1 / 50)
    (η := 1 / 10 ^ 9) (by norm_num) s hz₀ hz₁
  have b0 := twin_budget (L := L) hL (μ := 3) le_rfl (225 * 10 ^ 11) (D := 2 / 10 ^ 7) (P := 9 / 4)
    (by positivity) le_rfl (by norm_num) (by norm_num) (abs_nonneg s) hs
  have b1 := twin_budget (L := L) hL (μ := 3 + 1 / 10 ^ 11) (by norm_num) (225 * 10 ^ 11)
    (D := 2 / 10 ^ 7) (P := 9 / 4) (by positivity) le_rfl (by norm_num) (by norm_num)
    (abs_nonneg s) hs
  rw [abs_abs] at b0 b1
  have hnn := devRegionWeight_nonneg (approachObserver (L := L) s)
    (chordArc (exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))) (1 / 50))ᶜ
  unfold approachObserver at hnn ⊢
  nlinarith

/-- **Where a messenger is**, at any time `|s| ≤ 8·10¹³`: within chord `1/50` of `e^{−iΩs}`,
`Ω = 8·10⁻¹⁴`, but for `6·10⁻³` of its weight. -/
theorem image_tail_any {s : ℝ} (hs : |s| ≤ 8 * 10 ^ 13) :
    regionWeight (imagePacket (L := L) s)
      (chordArc (exp (I * ((-(8 / 10 ^ 14 * s) : ℝ) : ℂ))) (1 / 50))ᶜ ≤ 6 / 1000 := by
  have h := regionWeight_compl_chordArc_le (L := L) (c := 1) (μ := 3) (P := 4) (D := 2 / 10 ^ 7)
    (p₀ := -4) one_pos (by norm_num) (by positivity) (by norm_num) (by positivity) (image_win hL)
    image_spread twinAmp (twin_norm hL _) (z := exp (I * ((-(8 / 10 ^ 14 * s) : ℝ) : ℂ)))
    (ρ := 1 / 50) (η := 0) (by norm_num) s (by rw [omega_image, neg_mul, sub_self, norm_zero])
  have b := twin_budget (L := L) hL (μ := 3) le_rfl (-(4 * 10 ^ 13) - 1999999) (D := 2 / 10 ^ 7)
    (P := 4) (by positivity) le_rfl (by norm_num) le_rfl (abs_nonneg s) hs
  rw [abs_abs] at b
  have hnn := regionWeight_nonneg (imagePacket (L := L) s)
    (chordArc (exp (I * ((-(8 / 10 ^ 14 * s) : ℝ) : ℂ))) (1 / 50))ᶜ
  unfold imagePacket imageWin at hnn ⊢
  unfold imageWin at h
  rw [sub_zero] at h
  nlinarith

theorem approach_total (t : ℝ) :
    devRegionWeight (approachObserver (L := L) t) Finset.univ = 1 :=
  devRegionWeight_univ (L := L) (c := 1) (P := 9 / 4) (D := 2 / 10 ^ 7) (p₀ := 9 / 4) one_pos
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity) (approach_win hL)
    approach_spread twinAmp (twin_norm hL _) t

theorem image_total (t : ℝ) : regionWeight (imagePacket (L := L) t) Finset.univ = 1 := by
  rw [regionWeight, sum_siteWeight, imagePacket_norm hL, Complex.one_re]

omit [NeZero L] in
/-- ★★ **The approaching clock turns at `4/5` of the rest rate**: its splitting lies in
`[8·10⁻¹², 8.002·10⁻¹²]` — the dilation `√(1 − (3/5)²) = 4/5`, to the lattice's precision. -/
theorem approach_rate :
    8 / 10 ^ 12 ≤ levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
    ∧ levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
      ≤ 8002 / 10 ^ 15 := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  set a := 2 * Real.pi * 10 ^ 13 / L
  have ha0 : 0 < a := by positivity
  have ha : a ≤ 63 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hs : 2 * scaledHop 1 a * Real.sin (a * (9 / 4)) = Real.sin (9 / 4 * a) / a := by
    rw [scaledHop, mul_comm a (9 / 4)]
    field_simp
  set s := 2 * scaledHop 1 a * Real.sin (a * (9 / 4))
  have hs_le : |s| ≤ 9 / 4 := by
    rw [hs, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    have := Real.abs_sin_sub_sin_le (9 / 4 * a) 0
    rw [Real.sin_zero, sub_zero, sub_zero, abs_of_pos (show (0 : ℝ) < 9 / 4 * a by positivity)]
      at this
    linarith
  have hs_ge : 2249 / 1000 ≤ s := by
    rw [hs, le_div_iff₀ ha0]
    have := Real.sin_gt_sub_cube (x := 9 / 4 * a) (by positivity)
    have ha2 : a ^ 2 ≤ (63 / 10 ^ 7) ^ 2 := pow_le_pow_left₀ ha0.le ha 2
    nlinarith
  obtain ⟨hlo, hhi⟩ := clockRate_mem (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11) (by norm_num) (by norm_num) s
  have hE0 : dispE 3 s ≤ 15 / 4 := by
    rw [dispE, Real.sqrt_le_left (by norm_num)]
    have := sq_abs s
    nlinarith [abs_nonneg s]
  have hE1 : 37494 / 10000 ≤ dispE (3 + 1 / 10 ^ 11) s := by
    rw [dispE]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hE0p := dispE_pos (μ := 3) (by norm_num) s
  constructor
  · refine le_trans ?_ hlo
    rw [show (3 + 1 / 10 ^ 11 - 3 : ℝ) = 1 / 10 ^ 11 by ring]
    have : (3 : ℝ) / (15 / 4) ≤ 3 / dispE 3 s := div_le_div_of_nonneg_left (by norm_num) hE0p hE0
    nlinarith
  · refine hhi.trans ?_
    rw [show (3 + 1 / 10 ^ 11 - 3 : ℝ) = 1 / 10 ^ 11 by ring]
    have : (3 + 1 / 10 ^ 11 : ℝ) / dispE (3 + 1 / 10 ^ 11) s
        ≤ (3 + 1 / 10 ^ 11) / (37494 / 10000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hE1
    have hnum : (1 / 10 ^ 11 : ℝ) * ((3 + 1 / 10 ^ 11) / (37494 / 10000)) ≤ 8002 / 10 ^ 15 := by
      norm_num
    nlinarith

/-- **The approaching clock's coherence drifts from its start**: from `approachObserver (−5·10¹³)`,
within `|s|` times the sharp drift. -/
theorem approach_drift (s : ℝ) :
    ‖deviceCoherence (deviceProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3
          (3 + 1 / 10 ^ 11) s *ᵥ approachObserver (-(5 * 10 ^ 13)))
        - exp (I * (((-levelClockRate 3 (3 + 1 / 10 ^ 11) (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
            * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) : ℝ) : ℂ) * s))
          * deviceCoherence (approachObserver (L := L) (-(5 * 10 ^ 13)))‖
      ≤ |s| * deviceDrift 1 3 (3 + 1 / 10 ^ 11) (2 / 10 ^ 7) (9 / 4) := by
  obtain ⟨-, hD⟩ := noWrap_distinct_of_window (L := L) (approach_win hL)
  rw [approachObserver, deviceProp_devicePacket_shift,
    (device_observables _ _ _ _ _ (-(5 * 10 ^ 13) + s)).2.2,
    (device_observables _ _ _ _ _ (-(5 * 10 ^ 13))).2.2]
  have h := levelCoherence_shift_sharp (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (D := 2 / 10 ^ 7) (p₀ := 9 / 4) one_pos (by norm_num) (by norm_num)
    (by positivity) hD approach_spread twinAmp (twin_norm hL _) (-(5 * 10 ^ 13)) s
  have e2 : ∀ X Y e : ℂ, (1 / 2 : ℂ) * X - e * ((1 / 2 : ℂ) * Y) = (1 / 2 : ℂ) * (X - e * Y) :=
    fun X Y e => by ring
  rw [e2, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖_‖ ≤ 1 / 2 * (|s| * (1 * (2 / 10 ^ 7) * (2 * 1 * |(9 / 4 : ℝ)| + 1 * (2 / 10 ^ 7))
        * (3 + 1 / 10 ^ 11 - 3) / (2 * 3 ^ 2))) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = |s| * deviceDrift 1 3 (3 + 1 / 10 ^ 11) (2 / 10 ^ 7) (9 / 4) := by
        rw [deviceDrift]
        ring

end Approach

/-! ### The approaching clock's ticks -/

theorem star_exp_I_mul (b : ℝ) : star (exp (I * (b : ℂ))) = exp (I * ((-b : ℝ) : ℂ)) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

theorem rel_offset (a b : ℝ) :
    exp (I * (a : ℂ)) * star (exp (I * (b : ℂ))) = exp (I * ((a - b : ℝ) : ℂ)) := by
  rw [star_exp_I_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

section Ticks

variable (hL : 10 ^ 19 ≤ L)
include hL

/-- **The approaching clock keeps a reading at its start**: `|C| ≥ κ₀ − 5·10¹³ · drift`. -/
theorem approach_coherence_ge :
    (1 - ((3 + 1 / 10 ^ 11 - 3) / 3) ^ 2) / 2
        - 5 * 10 ^ 13 * deviceDrift 1 3 (3 + 1 / 10 ^ 11) (2 / 10 ^ 7) (9 / 4)
      ≤ ‖deviceCoherence (approachObserver (L := L) (-(5 * 10 ^ 13)))‖ := by
  have hf := deviceTick_facts (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (P := 9 / 4) (D := 2 / 10 ^ 7) (p₀ := 9 / 4) one_pos (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity) (approach_win hL)
    approach_spread twinAmp (twin_norm hL _)
  have h := approach_drift (L := L) hL (5 * 10 ^ 13)
  rw [approachObserver, deviceProp_devicePacket_shift, show -(5 * 10 ^ 13 : ℝ) + 5 * 10 ^ 13 = 0 by
    ring] at h
  have h0 := hf.2.1
  have hn : ‖exp (I * (((-levelClockRate 3 (3 + 1 / 10 ^ 11) (2 * scaledHop 1
      (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) : ℝ) : ℂ)
        * ((5 * 10 ^ 13 : ℝ) : ℂ)))
      * deviceCoherence (approachObserver (L := L) (-(5 * 10 ^ 13)))‖
      = ‖deviceCoherence (approachObserver (L := L) (-(5 * 10 ^ 13)))‖ := by
    rw [norm_mul, norm_exp_I_mul_ofReal_mul, one_mul]
  have tri := norm_sub_norm_le (deviceCoherence (devicePacket (L := L)
    (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11)
    (Finset.Ico (225 * 10 ^ 11 : ℤ) (225 * 10 ^ 11 + (2000000 : ℕ))) twinAmp 0))
    (exp (I * (((-levelClockRate 3 (3 + 1 / 10 ^ 11) (2 * scaledHop 1
      (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) : ℝ) : ℂ)
        * ((5 * 10 ^ 13 : ℝ) : ℂ)))
      * deviceCoherence (approachObserver (L := L) (-(5 * 10 ^ 13))))
  rw [hn] at tri
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 * 10 ^ 13)] at h
  unfold approachObserver at tri ⊢
  linarith

/-- **Tick `n` of the approaching clock** (`n ≤ 60`): written within `1.2·10¹¹` of `2πn/R`, its
splitting `R ∈ [8·10⁻¹², 8.002·10⁻¹²]`, counted from the preparation. -/
noncomputable def approachTick (n : ℕ) (hn : n ≤ 60) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  have hR := approach_rate (L := L) hL
  have hC := approach_coherence_ge (L := L) hL
  have hd : deviceDrift 1 3 (3 + 1 / 10 ^ 11) (2 / 10 ^ 7) (9 / 4)
      = 2 / 10 ^ 7 * (2 * 1 * (9 / 4) + 1 * (2 / 10 ^ 7)) * (1 / 10 ^ 11) / 36 := by
    simp only [deviceDrift, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 4)]
    norm_num
  driftTickDetector (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) 1 _
    (deviceDrift 1 3 (3 + 1 / 10 ^ 11) (2 / 10 ^ 7) (9 / 4)) one_pos (by linarith [hR.1])
    (approachObserver (-(5 * 10 ^ 13))) (approach_drift hL)
    (norm_pos_iff.1 (lt_of_lt_of_le (by rw [hd]; norm_num) hC)) n (δ := 12 * 10 ^ 10)
    (by positivity)
    (by
      rw [le_div_iff₀ (by linarith [hR.1])]
      nlinarith [hR.2])
    (by
      set R := levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
      have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR.1
      have hπ2 := pi_lt_sixty_three_div_twenty
      have hπ := Real.pi_pos
      have hn' : (n : ℝ) ≤ 60 := by exact_mod_cast hn
      have hx0 : 0 ≤ 2 * Real.pi * n / R + 12 * 10 ^ 10 := by positivity
      have hdiv : 2 * Real.pi * n / R ≤ 2 * Real.pi * n / (8 / 10 ^ 12) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hR.1
      have hx1 : 2 * Real.pi * n / R + 12 * 10 ^ 10 ≤ 5 * 10 ^ 13 := by
        rw [show 2 * Real.pi * n / (8 / 10 ^ 12) = 2 * Real.pi * n * (10 ^ 12 / 8) by
          field_simp] at hdiv
        nlinarith [mul_le_mul hπ2.le hn' (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 63 / 20)]
      have hsq := pow_le_pow_left₀ hx0 hx1 2
      have hC' : (49 / 100 : ℝ) ≤ ‖deviceCoherence (approachObserver (L := L) (-(5 * 10 ^ 13)))‖ :=
        le_trans (by rw [hd]; norm_num) hC
      rw [hd]
      calc 2 / 10 ^ 7 * (2 * 1 * (9 / 4) + 1 * (2 / 10 ^ 7)) * (1 / 10 ^ 11) / 36
            * (2 * Real.pi * n / R + 12 * 10 ^ 10) ^ 2
          ≤ 2 / 10 ^ 7 * (2 * 1 * (9 / 4) + 1 * (2 / 10 ^ 7)) * (1 / 10 ^ 11) / 36
            * (5 * 10 ^ 13) ^ 2 := by gcongr
        _ < 49 / 100 * (12 * 10 ^ 10) := by norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right hC' (by positivity))
    hw

/-! ### The weights along the way -/

/-- **A messenger at `A`**: within `10¹²` of its passage `e`, it has at least `1 − 6·10⁻³` on the
chord-`1/10` arc at `A`. -/
theorem emission_near {e t : ℝ} (h0 : |t - e| ≤ 10 ^ 12) :
    1 - 6 / 1000 ≤ regionWeight (imagePacket (L := L) (t - e)) (chordArc 1 (1 / 10)) := by
  have hs : |t - e| ≤ 8 * 10 ^ 13 := h0.trans (by norm_num)
  have ht := image_tail_any (L := L) hL hs
  have hu : ‖exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ)) - 1‖ ≤ 8 / 100 := by
    have := norm_exp_sub_exp_le (-(8 / 10 ^ 14 * (t - e))) 0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 8 / 10 ^ 14)] at this
    nlinarith
  have hsub := regionWeight_mono (imagePacket (L := L) (t - e)) (Finset.compl_subset_compl.2
    (chordArc_subset (z := exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))) (w := 1) (ρ := 1 / 50)
      (σ := 1 / 10) (by linarith)))
  have hsum := regionWeight_add_compl (imagePacket (L := L) (t - e)) (chordArc 1 (1 / 10))
  rw [imagePacket_norm hL, Complex.one_re] at hsum
  linarith

/-- **A messenger away from `A`**: while its angle `8·10⁻¹⁴ (e − t)` is at least `0.121` from every
multiple of `2π`, it has at most `6·10⁻³` at `A`. -/
theorem emission_far {e t : ℝ} (hs : |t - e| ≤ 8 * 10 ^ 13)
    (h1 : 121 / 1000 ≤ |8 / 10 ^ 14 * (t - e)|)
    (h2 : |8 / 10 ^ 14 * (t - e)| ≤ 2 * Real.pi - 121 / 1000) :
    regionWeight (imagePacket (L := L) (t - e)) (chordArc 1 (1 / 10)) ≤ 6 / 1000 := by
  have ht := image_tail_any (L := L) hL hs
  have hsin := Real.sin_gt_sub_cube (x := 121 / 1000 / 2) (by norm_num)
  have hfar := two_sin_le_norm_exp_sub_one (y := 121 / 1000) (z := -(8 / 10 ^ 14 * (t - e)))
    (by norm_num) (by rwa [abs_neg]) (by rwa [abs_neg])
  have : (12 / 100 : ℝ) < 2 * (121 / 1000 / 2 - (121 / 1000 / 2) ^ 3 / 6) := by norm_num
  exact (regionWeight_mono _ (chordArc_subset_compl
    (z := exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))) (w := 1) (ρ := 1 / 50) (σ := 1 / 10)
    (by linarith))).trans ht

/-- **The messenger at the approaching observer**: if their relative angle is within `6/100`, the
encounter weight is at least `(1 − 6·10⁻³)²`. -/
theorem reception_near {e t : ℝ} (hs1 : |t - e| ≤ 8 * 10 ^ 13)
    (hs2 : |t - 5 * 10 ^ 13| ≤ 8 * 10 ^ 13)
    (h : |-(8 / 10 ^ 14 * (t - e)) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)| ≤ 6 / 100) :
    (1 - 6 / 1000) ^ 2 ≤ relWeight 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (levelLift 0 (imagePacket (L := L) (t - e))) := by
  have tB := approach_tail (L := L) hL hs2
  have tm := image_tail_any (L := L) hL hs1
  have hX := devRegionWeight_add_compl (approachObserver (L := L) (t - 5 * 10 ^ 13))
    (chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50))
  rw [approach_total hL] at hX
  have hY := regionWeight_add_compl (imagePacket (L := L) (t - e))
    (chordArc (exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))) (1 / 50))
  rw [imagePacket_norm hL, Complex.one_re] at hY
  have hoff : ‖exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))
      * star (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) - 1‖ ≤ 6 / 100 := by
    rw [rel_offset]
    have := norm_exp_sub_exp_le (-(8 / 10 ^ 14 * (t - e)) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)) 0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero] at this
    exact this.trans h
  have hle := le_relWeight (w := 1) (ρ := 1 / 10)
    (ΨA := approachObserver (L := L) (t - 5 * 10 ^ 13))
    (ΨB := levelLift 0 (imagePacket (L := L) (t - e)))
    (X := chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50))
    (Y := chordArc (exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))) (1 / 50)) fun j hj k hk =>
      offset_mem_of_near_at (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj) (mem_chordArc.1 hk)
        (by linarith)
  rw [devRegionWeight_levelLift] at hle
  have hA : 1 - 6 / 1000 ≤ devRegionWeight (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50)) := by linarith
  have hB : 1 - 6 / 1000 ≤ regionWeight (imagePacket (L := L) (t - e))
      (chordArc (exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))) (1 / 50)) := by linarith
  calc (1 - 6 / 1000 : ℝ) ^ 2 = (1 - 6 / 1000) * (1 - 6 / 1000) := sq _
    _ ≤ _ := mul_le_mul hA hB (by norm_num) (devRegionWeight_nonneg _ _)
    _ ≤ _ := hle

/-- **The messenger away from the approaching observer**: if their relative angle is at least
`0.141` from every multiple of `2π`, the encounter weight is at most `1.2·10⁻²`. -/
theorem reception_far {e t : ℝ} (hs1 : |t - e| ≤ 8 * 10 ^ 13)
    (hs2 : |t - 5 * 10 ^ 13| ≤ 8 * 10 ^ 13)
    (h1 : 141 / 1000 ≤ |-(8 / 10 ^ 14 * (t - e)) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)|)
    (h2 : |-(8 / 10 ^ 14 * (t - e)) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)| ≤ 2 * Real.pi - 141 / 1000) :
    relWeight 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (levelLift 0 (imagePacket (L := L) (t - e))) ≤ 12 / 1000 := by
  have tB := approach_tail (L := L) hL hs2
  have tm := image_tail_any (L := L) hL hs1
  have hsin := Real.sin_gt_sub_cube (x := 141 / 1000 / 2) (by norm_num)
  have hfar := two_sin_le_norm_exp_sub_one (y := 141 / 1000)
    (z := -(8 / 10 ^ 14 * (t - e)) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)) (by norm_num) h1 h2
  have : (14 / 100 : ℝ) < 2 * (141 / 1000 / 2 - (141 / 1000 / 2) ^ 3 / 6) := by norm_num
  have hoff : 14 / 100 < ‖exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))
      * star (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) - 1‖ := by
    rw [rel_offset]
    linarith
  have hle := relWeight_le (w := 1) (ρ := 1 / 10)
    (ΨA := approachObserver (L := L) (t - 5 * 10 ^ 13))
    (ΨB := levelLift 0 (imagePacket (L := L) (t - e)))
    (X := chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50))
    (Y := chordArc (exp (I * ((-(8 / 10 ^ 14 * (t - e)) : ℝ) : ℂ))) (1 / 50)) fun j hj k hk =>
      offset_not_mem_of_far_at (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj)
        (mem_chordArc.1 hk) (by linarith)
  rw [devRegionWeight_levelLift, devRegionWeight_levelLift, approach_total hL, one_mul] at hle
  have hm1 : regionWeight (imagePacket (L := L) (t - e)) Finset.univ = 1 := image_total hL _
  rw [hm1, mul_one] at hle
  linarith

theorem rel_approach_le_one (e t : ℝ) :
    relWeight 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (levelLift 0 (imagePacket (L := L) (t - e))) ≤ 1 := by
  have h := relWeight_le_mul 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13))
    (levelLift 0 (imagePacket (L := L) (t - e)))
  rwa [approach_total hL, devRegionWeight_levelLift, image_total hL, one_mul] at h

theorem image_le_one (A : Finset (ZMod L)) (s : ℝ) : regionWeight (imagePacket (L := L) s) A ≤ 1 := by
  have h := regionWeight_add_compl (imagePacket (L := L) s) A
  rw [imagePacket_norm hL, Complex.one_re] at h
  linarith [regionWeight_nonneg (imagePacket (L := L) s) Aᶜ]

end Ticks

/-! ### The arena: two clocks, two messengers -/

/-- **The arena**: the observer at rest with its tick register, the approaching observer with its,
and two messengers. -/
abbrev DopArena (L : ℕ) : Type :=
  TickArena L × TickArena L × (ZMod L × Fin 2 → ℂ) × (ZMod L × Fin 2 → ℂ)

/-- **Its flow**: each clock by `e^{−itH_dev}` with its tick register, each messenger by `e^{−itH}`. -/
noncomputable def dopFlow (t : ℝ) (x : DopArena L) : DopArena L :=
  (tickFlow (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) 1
      (tickMark (restObserver (L := L) 0)) t x.1,
    tickFlow (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) 1
      (tickMark (approachObserver (L := L) (-(5 * 10 ^ 13)))) t x.2.1,
    chainProp (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 t *ᵥ x.2.2.1,
    chainProp (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 t *ᵥ x.2.2.2)

/-- The first messenger's weight at `A`. -/
noncomputable def dopEm₁ (x : DopArena L) : ℝ := regionWeight x.2.2.1 (chordArc 1 (1 / 10))

/-- The second messenger's weight at `A`. -/
noncomputable def dopEm₂ (x : DopArena L) : ℝ := regionWeight x.2.2.2 (chordArc 1 (1 / 10))

/-- The first messenger's encounter weight with the approaching observer. -/
noncomputable def dopRc₁ (x : DopArena L) : ℝ := relWeight 1 (1 / 10) x.2.1.1 (levelLift 0 x.2.2.1)

/-- The second messenger's encounter weight with the approaching observer. -/
noncomputable def dopRc₂ (x : DopArena L) : ℝ := relWeight 1 (1 / 10) x.2.1.1 (levelLift 0 x.2.2.2)

/-- **The four registers**: the two emissions at `A`, the two receptions at the approaching
observer. -/
noncomputable def dopWeight : Fin 4 → DopArena L → ℝ := ![dopEm₁, dopEm₂, dopRc₁, dopRc₂]

theorem dopFlow_zero (x : DopArena L) : dopFlow 0 x = x := by
  refine Prod.ext (tickFlow_zero _ _ _ _ _ _) (Prod.ext (tickFlow_zero _ _ _ _ _ _) (Prod.ext ?_ ?_))
  · show chainProp _ _ 0 *ᵥ x.2.2.1 = x.2.2.1
    rw [chainProp_zero, Matrix.one_mulVec]
  · show chainProp _ _ 0 *ᵥ x.2.2.2 = x.2.2.2
    rw [chainProp_zero, Matrix.one_mulVec]

theorem dopFlow_add (s t : ℝ) (x : DopArena L) : dopFlow (s + t) x = dopFlow t (dopFlow s x) := by
  refine Prod.ext (tickFlow_add _ _ _ _ _ _ _ _)
    (Prod.ext (tickFlow_add _ _ _ _ _ _ _ _) (Prod.ext ?_ ?_))
  · show chainProp _ _ (s + t) *ᵥ x.2.2.1 = chainProp _ _ t *ᵥ (chainProp _ _ s *ᵥ x.2.2.1)
    rw [Matrix.mulVec_mulVec, chainProp_add]
  · show chainProp _ _ (s + t) *ᵥ x.2.2.2 = chainProp _ _ t *ᵥ (chainProp _ _ s *ᵥ x.2.2.2)
    rw [Matrix.mulVec_mulVec, chainProp_add]

theorem measurable_dopFlow (t : ℝ) : Measurable (dopFlow (L := L) t) := by
  refine ((measurable_tickFlow _ _ _ _ _ t).comp measurable_fst).prodMk
    (((measurable_tickFlow _ _ _ _ _ t).comp measurable_snd.fst).prodMk ?_)
  have hc := (continuous_chainProp_mulVec (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3)
  refine (hc.comp (continuous_id.prodMk continuous_const)).measurable.comp measurable_snd.snd.fst
    |>.prodMk ?_
  exact (hc.comp (continuous_id.prodMk continuous_const)).measurable.comp measurable_snd.snd.snd

omit [NeZero L] in
theorem continuous_levelLift_zero :
    Continuous fun v : ZMod L × Fin 2 → ℂ => levelLift 0 v :=
  continuous_pi fun _ => continuous_if_const _ (fun _ => continuous_apply _)
    fun _ => continuous_const

theorem continuous_dopWeight (i : Fin 4) :
    Continuous fun p : DopArena L × ℝ => dopWeight i (dopFlow p.2 p.1) := by
  have hm₁ : Continuous fun p : DopArena L × ℝ =>
      chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 p.2 *ᵥ p.1.2.2.1 :=
    (continuous_chainProp_mulVec _ _).comp (continuous_fst.snd.snd.fst.prodMk continuous_snd)
  have hm₂ : Continuous fun p : DopArena L × ℝ =>
      chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 p.2 *ᵥ p.1.2.2.2 :=
    (continuous_chainProp_mulVec _ _).comp (continuous_fst.snd.snd.snd.prodMk continuous_snd)
  have hB : Continuous fun p : DopArena L × ℝ =>
      deviceProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) p.2
        *ᵥ p.1.2.1.1 :=
    (continuous_deviceProp_mulVec _ _ _).comp (continuous_fst.snd.fst.fst.prodMk continuous_snd)
  fin_cases i
  · have h := (continuous_regionWeight (L := L) (chordArc 1 (1 / 10))).comp hm₁
    exact h
  · have h := (continuous_regionWeight (L := L) (chordArc 1 (1 / 10))).comp hm₂
    exact h
  · have h := continuous_relWeight_comp hB (continuous_levelLift_zero.comp hm₁) 1 (1 / 10)
    exact h
  · have h := continuous_relWeight_comp hB (continuous_levelLift_zero.comp hm₂) 1 (1 / 10)
    exact h

/-- **The preparation**: both clocks at their starts — the approaching one `5·10¹³` before it reaches
`A` — every register at `0`, and the two messengers on their way to `A`, passing it at `4·10¹²` and
at `3.6·10¹³`. -/
noncomputable def dopPrep : DopArena L :=
  ((restObserver (L := L) 0, 0), (approachObserver (L := L) (-(5 * 10 ^ 13)), 0),
    imagePacket (L := L) (-(4 * 10 ^ 12)), imagePacket (L := L) (-(36 * 10 ^ 12)))

theorem dopFlow_prep_messenger₁ (s : ℝ) :
    (dopFlow s (dopPrep (L := L))).2.2.1 = imagePacket (s - 4 * 10 ^ 12) := by
  simp only [dopFlow, dopPrep]
  rw [imagePacket, chainProp_ringPacket, imagePacket]
  congr 1
  ring

theorem dopFlow_prep_messenger₂ (s : ℝ) :
    (dopFlow s (dopPrep (L := L))).2.2.2 = imagePacket (s - 36 * 10 ^ 12) := by
  simp only [dopFlow, dopPrep]
  rw [imagePacket, chainProp_ringPacket, imagePacket]
  congr 1
  ring

theorem dopFlow_prep_approach (s : ℝ) :
    (dopFlow s (dopPrep (L := L))).2.1.1 = approachObserver (s - 5 * 10 ^ 13) := by
  simp only [dopFlow, dopPrep, state_tickFlow]
  rw [approachObserver, deviceProp_devicePacket_shift, approachObserver]
  congr 1
  ring

theorem dopFlow_prep_rest (s : ℝ) :
    (dopFlow s (dopPrep (L := L))).1.1 = restObserver s := by
  simp only [dopFlow, dopPrep, state_tickFlow]
  rw [restObserver, deviceProp_devicePacket, restObserver]

theorem continuous_dopWeight_prep (i : Fin 4) :
    Continuous fun s => dopWeight i (dopFlow s (dopPrep (L := L))) := by
  have h := (continuous_dopWeight (L := L) i).comp
    (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (dopPrep (L := L), s))
  exact h

theorem dopWeight_prep_em₁ (s : ℝ) :
    dopWeight 0 (dopFlow s (dopPrep (L := L)))
      = regionWeight (imagePacket (L := L) (s - 4 * 10 ^ 12)) (chordArc 1 (1 / 10)) := by
  simp only [dopWeight, Matrix.cons_val_zero, dopEm₁]
  rw [dopFlow_prep_messenger₁]

theorem dopWeight_prep_em₂ (s : ℝ) :
    dopWeight 1 (dopFlow s (dopPrep (L := L)))
      = regionWeight (imagePacket (L := L) (s - 36 * 10 ^ 12)) (chordArc 1 (1 / 10)) := by
  simp only [dopWeight, Matrix.cons_val_one, Matrix.cons_val_zero, dopEm₂]
  rw [dopFlow_prep_messenger₂]

theorem dopWeight_prep_rc₁ (s : ℝ) :
    dopWeight 2 (dopFlow s (dopPrep (L := L)))
      = relWeight 1 (1 / 10) (approachObserver (L := L) (s - 5 * 10 ^ 13))
        (levelLift 0 (imagePacket (L := L) (s - 4 * 10 ^ 12))) := by
  have e : dopWeight (L := L) 2 = dopRc₁ := rfl
  rw [e, dopRc₁, dopFlow_prep_approach, dopFlow_prep_messenger₁]

theorem dopWeight_prep_rc₂ (s : ℝ) :
    dopWeight 3 (dopFlow s (dopPrep (L := L)))
      = relWeight 1 (1 / 10) (approachObserver (L := L) (s - 5 * 10 ^ 13))
        (levelLift 0 (imagePacket (L := L) (s - 36 * 10 ^ 12))) := by
  have e : dopWeight (L := L) 3 = dopRc₂ := rfl
  rw [e, dopRc₂, dopFlow_prep_approach, dopFlow_prep_messenger₂]

section Records

variable (hL : 10 ^ 19 ≤ L)
include hL

theorem dop_emission_before {e t : ℝ} (he0 : 15125 * 10 ^ 8 ≤ e) (he : e ≤ 36 * 10 ^ 12) (ht0 : 0 ≤ t)
    (ht : t < e - 113 * 10 ^ 10)
    (F : ℝ → ℝ) (hF : Continuous F) (hFe : ∀ s, F s = regionWeight (imagePacket (L := L) (s - e))
      (chordArc 1 (1 / 10))) :
    ∫ s in (0 : ℝ)..t, F s < 6 * 10 ^ 11 := by
  have hπ := Real.pi_pos
  have hπ1 : (314 / 100 : ℝ) < Real.pi := by
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  have hfar : ∀ s, 0 ≤ s → s ≤ e - 15125 * 10 ^ 8 → F s ≤ 6 / 1000 := fun s hs0 hs => by
    rw [hFe]
    have hneg : s - e < 0 := by linarith
    refine emission_far hL (by rw [abs_le]; constructor <;> linarith) ?_ ?_
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 10 ^ 14), abs_of_neg hneg]
      nlinarith
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 10 ^ 14), abs_of_neg hneg]
      nlinarith
  rcases le_total t (e - 15125 * 10 ^ 8) with h | h
  · have h1 := integral_le_of_le_on hF ht0 h hfar
    nlinarith
  · have h1 := integral_le_of_le_on_then_one hF (by linarith) h hfar fun s => by
      rw [hFe]
      exact image_le_one hL _ _
    nlinarith

theorem dop_emission_after {e : ℝ} (he0 : 10 ^ 12 ≤ e)
    (F : ℝ → ℝ) (hF : Continuous F) (hFe : ∀ s, F s = regionWeight (imagePacket (L := L) (s - e))
      (chordArc 1 (1 / 10))) :
    6 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..e - 39 * 10 ^ 10, F s := by
  have h := le_integral_of_ge_on hF (κ := 1 - 6 / 1000) (tn := e - 10 ^ 12) (te := e + 10 ^ 12)
    (t := e - 39 * 10 ^ 10) (by linarith) (by linarith) (by linarith)
    (fun s _ => by rw [hFe]; exact regionWeight_nonneg _ _)
    fun s hs1 hs2 => by
      rw [hFe]
      exact emission_near hL (by rw [abs_le]; constructor <;> linarith)
  have : (6 * 10 ^ 11 : ℝ) ≤ (1 - 6 / 1000) * (e - 39 * 10 ^ 10 - (e - 10 ^ 12)) := by
    ring_nf
    norm_num
  exact this.trans h

theorem dop_reception_before {e tk t : ℝ} (he0 : 0 ≤ e) (he : e ≤ 36 * 10 ^ 12)
    (htk : 14 / 10 ^ 14 * tk = 8 / 10 ^ 14 * e + 3) (ht0 : 0 ≤ t) (ht : t < tk - 75 * 10 ^ 10)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hFe : ∀ s, F s = relWeight 1 (1 / 10) (approachObserver (L := L) (s - 5 * 10 ^ 13))
      (levelLift 0 (imagePacket (L := L) (s - e)))) :
    ∫ s in (0 : ℝ)..t, F s < 8 * 10 ^ 11 := by
  have hπ := Real.pi_pos
  have hπ1 : (314 / 100 : ℝ) < Real.pi := by
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  have htk' : tk ≤ 42 * 10 ^ 12 := by nlinarith
  have hfar : ∀ s, 0 ≤ s → s ≤ tk - 1008 * 10 ^ 9 → F s ≤ 12 / 1000 := fun s hs0 hs => by
    rw [hFe]
    have hψ : 141 / 1000 ≤ -(8 / 10 ^ 14 * (s - e)) - 6 / 10 ^ 14 * (s - 5 * 10 ^ 13) := by
      nlinarith
    refine reception_far hL (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith) ?_ ?_
    · rw [abs_of_pos (by linarith)]; exact hψ
    · rw [abs_of_pos (by linarith)]; nlinarith
  rcases le_total t (tk - 1008 * 10 ^ 9) with h | h
  · have h1 := integral_le_of_le_on hF ht0 h hfar
    nlinarith
  · have h1 := integral_le_of_le_on_then_one hF (by nlinarith) h hfar fun s => by
      rw [hFe]
      exact rel_approach_le_one hL _ _
    nlinarith

theorem dop_reception_after {e tk : ℝ} (he0 : 0 ≤ e) (he : e ≤ 36 * 10 ^ 12)
    (htk : 14 / 10 ^ 14 * tk = 8 / 10 ^ 14 * e + 3)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hFe : ∀ s, F s = relWeight 1 (1 / 10) (approachObserver (L := L) (s - 5 * 10 ^ 13))
      (levelLift 0 (imagePacket (L := L) (s - e)))) :
    8 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..tk + 385 * 10 ^ 9, F s := by
  have htk1 : 21 * 10 ^ 12 ≤ tk := by nlinarith
  have htk2 : tk ≤ 42 * 10 ^ 12 := by nlinarith
  have h := le_integral_of_ge_on hF (κ := (1 - 6 / 1000) ^ 2) (tn := tk - 428 * 10 ^ 9)
    (te := tk + 428 * 10 ^ 9) (t := tk + 385 * 10 ^ 9) (by linarith) (by linarith) (by linarith)
    (fun s _ => by rw [hFe]; exact relWeight_nonneg _ _ _ _)
    fun s hs1 hs2 => by
      rw [hFe]
      refine reception_near hL (by rw [abs_le]; constructor <;> nlinarith)
        (by rw [abs_le]; constructor <;> nlinarith) ?_
      rw [abs_le]
      constructor <;> nlinarith
  have : (8 * 10 ^ 11 : ℝ) ≤ (1 - 6 / 1000) ^ 2 * (tk + 385 * 10 ^ 9 - (tk - 428 * 10 ^ 9)) := by
    ring_nf
    norm_num
  exact this.trans h

/-- ★★★ **The first emission, recorded at `A`**: the register of the first messenger's weight at `A`
reaches `6·10¹¹` within `[4·10¹² − 1.13·10¹², 4·10¹² − 3.9·10¹¹]`. -/
noncomputable def dopEmission₁ {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DopArena L × (Fin 4 → ℝ)) ℕ L :=
  regDetector dopFlow dopWeight dopFlow_zero dopFlow_add continuous_dopWeight measurable_dopFlow 0
    (6 * 10 ^ 11) dopPrep Finset.univ (τ₀ := 4 * 10 ^ 12 - 113 * 10 ^ 10)
    (τ₁ := 4 * 10 ^ 12 - 39 * 10 ^ 10) (by norm_num) (by norm_num) hw
    (fun s _ => regionWeight_nonneg _ _)
    (fun t ht0 ht => dop_emission_before hL (by norm_num) (by norm_num) ht0 ht _
      (continuous_dopWeight_prep 0) (dopWeight_prep_em₁))
    (dop_emission_after hL (by norm_num) _
      (continuous_dopWeight_prep 0) (dopWeight_prep_em₁))

/-- ★★★ **The second emission, recorded at `A`**: within
`[3.6·10¹³ − 1.13·10¹², 3.6·10¹³ − 3.9·10¹¹]`. -/
noncomputable def dopEmission₂ {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DopArena L × (Fin 4 → ℝ)) ℕ L :=
  regDetector dopFlow dopWeight dopFlow_zero dopFlow_add continuous_dopWeight measurable_dopFlow 1
    (6 * 10 ^ 11) dopPrep Finset.univ (τ₀ := 36 * 10 ^ 12 - 113 * 10 ^ 10)
    (τ₁ := 36 * 10 ^ 12 - 39 * 10 ^ 10) (by norm_num) (by norm_num) hw
    (fun s _ => regionWeight_nonneg _ _)
    (fun t ht0 ht => dop_emission_before hL (by norm_num) le_rfl ht0 ht _
      (continuous_dopWeight_prep 1) (dopWeight_prep_em₂))
    (dop_emission_after hL (by norm_num) _
      (continuous_dopWeight_prep 1) (dopWeight_prep_em₂))

/-- ★★★ **The first reception, recorded by the approaching observer**: the encounter register reaches
`8·10¹¹` within `[t₁ − 7.5·10¹¹, t₁ + 3.85·10¹¹]`, `t₁ = 1.66·10¹⁴/7`. -/
noncomputable def dopReception₁ {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DopArena L × (Fin 4 → ℝ)) ℕ L :=
  regDetector dopFlow dopWeight dopFlow_zero dopFlow_add continuous_dopWeight measurable_dopFlow 2
    (8 * 10 ^ 11) dopPrep Finset.univ (τ₀ := 166 * 10 ^ 12 / 7 - 75 * 10 ^ 10)
    (τ₁ := 166 * 10 ^ 12 / 7 + 385 * 10 ^ 9) (by norm_num) (by norm_num) hw
    (fun s _ => relWeight_nonneg _ _ _ _)
    (fun t ht0 ht => dop_reception_before hL (e := 4 * 10 ^ 12) (by norm_num) (by norm_num)
      (by norm_num) ht0 ht _
      (continuous_dopWeight_prep 2) (dopWeight_prep_rc₁))
    (dop_reception_after hL (e := 4 * 10 ^ 12) (by norm_num) (by norm_num) (by norm_num) _
      (continuous_dopWeight_prep 2) (dopWeight_prep_rc₁))

/-- ★★★ **The second reception, recorded by the approaching observer**: within
`[4.2·10¹³ − 7.5·10¹¹, 4.2·10¹³ + 3.85·10¹¹]`. -/
noncomputable def dopReception₂ {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DopArena L × (Fin 4 → ℝ)) ℕ L :=
  regDetector dopFlow dopWeight dopFlow_zero dopFlow_add continuous_dopWeight measurable_dopFlow 3
    (8 * 10 ^ 11) dopPrep Finset.univ (τ₀ := 42 * 10 ^ 12 - 75 * 10 ^ 10)
    (τ₁ := 42 * 10 ^ 12 + 385 * 10 ^ 9) (by norm_num) (by norm_num) hw
    (fun s _ => relWeight_nonneg _ _ _ _)
    (fun t ht0 ht => dop_reception_before hL (e := 36 * 10 ^ 12) (by norm_num) le_rfl (by norm_num)
      ht0 ht _ (continuous_dopWeight_prep 3) (dopWeight_prep_rc₂))
    (dop_reception_after hL (e := 36 * 10 ^ 12) (by norm_num) le_rfl (by norm_num) _
      (continuous_dopWeight_prep 3) (dopWeight_prep_rc₂))

/-- **Tick `n` of the clock at rest, in the arena.** -/
noncomputable def restTickDop (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DopArena L × (Fin 4 → ℝ)) ℕ L :=
  (twinRestTick hL n hn hw).pullback (regEvolve dopFlow dopWeight)
    (regEvolve_self dopFlow dopWeight dopFlow_zero)
    (regEvolve_comp dopFlow dopWeight dopFlow_add continuous_dopWeight)
    (fun s t => measurable_regFlow dopFlow dopWeight measurable_dopFlow continuous_dopWeight (t - s))
    (fun y => y.1.1) measurable_fst.fst (fun _ _ _ => rfl) (dopPrep, 0) rfl

/-- **Tick `n` of the approaching clock, in the arena.** -/
noncomputable def approachTickDop (n : ℕ) (hn : n ≤ 60) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DopArena L × (Fin 4 → ℝ)) ℕ L :=
  (approachTick hL n hn hw).pullback (regEvolve dopFlow dopWeight)
    (regEvolve_self dopFlow dopWeight dopFlow_zero)
    (regEvolve_comp dopFlow dopWeight dopFlow_add continuous_dopWeight)
    (fun s t => measurable_regFlow dopFlow dopWeight measurable_dopFlow continuous_dopWeight (t - s))
    (fun y => y.1.2.1) measurable_fst.snd.fst (fun _ _ _ => rfl) (dopPrep, 0) rfl

end Records

/-! ### The Doppler factor -/

section Factor

variable (hL : 10 ^ 19 ≤ L)
include hL

theorem dopEmission₁_fields {w : ℝ} (hw : 0 ≤ w) :
    (dopEmission₁ (L := L) hL hw).evolve = regEvolve dopFlow dopWeight
    ∧ (dopEmission₁ (L := L) hL hw).prep = (dopPrep, 0)
    ∧ (dopEmission₁ (L := L) hL hw).writeStart = 4 * 10 ^ 12 - 113 * 10 ^ 10
    ∧ (dopEmission₁ (L := L) hL hw).writeEnd = 4 * 10 ^ 12 - 39 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dopEmission₂_fields {w : ℝ} (hw : 0 ≤ w) :
    (dopEmission₂ (L := L) hL hw).evolve = regEvolve dopFlow dopWeight
    ∧ (dopEmission₂ (L := L) hL hw).prep = (dopPrep, 0)
    ∧ (dopEmission₂ (L := L) hL hw).writeStart = 36 * 10 ^ 12 - 113 * 10 ^ 10
    ∧ (dopEmission₂ (L := L) hL hw).writeEnd = 36 * 10 ^ 12 - 39 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dopReception₁_fields {w : ℝ} (hw : 0 ≤ w) :
    (dopReception₁ (L := L) hL hw).evolve = regEvolve dopFlow dopWeight
    ∧ (dopReception₁ (L := L) hL hw).prep = (dopPrep, 0)
    ∧ (dopReception₁ (L := L) hL hw).writeStart = 166 * 10 ^ 12 / 7 - 75 * 10 ^ 10
    ∧ (dopReception₁ (L := L) hL hw).writeEnd = 166 * 10 ^ 12 / 7 + 385 * 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dopReception₂_fields {w : ℝ} (hw : 0 ≤ w) :
    (dopReception₂ (L := L) hL hw).evolve = regEvolve dopFlow dopWeight
    ∧ (dopReception₂ (L := L) hL hw).prep = (dopPrep, 0)
    ∧ (dopReception₂ (L := L) hL hw).writeStart = 42 * 10 ^ 12 - 75 * 10 ^ 10
    ∧ (dopReception₂ (L := L) hL hw).writeEnd = 42 * 10 ^ 12 + 385 * 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem restTickDop_fields (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    (restTickDop (L := L) hL n hn hw).evolve = regEvolve dopFlow dopWeight
    ∧ (restTickDop (L := L) hL n hn hw).prep = (dopPrep, 0)
    ∧ (restTickDop (L := L) hL n hn hw).writeStart = max 0 (n * (2 * Real.pi * 10 ^ 11) - 10 ^ 11)
    ∧ (restTickDop (L := L) hL n hn hw).writeEnd = n * (2 * Real.pi * 10 ^ 11) + 10 ^ 11 := by
  have e : 2 * Real.pi * (n : ℝ) / (1 / 10 ^ 11) = n * (2 * Real.pi * 10 ^ 11) := by field_simp
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show max 0 (2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
        - 10 ^ 11) = _
    rw [twin_rest_rate, e]
  · show 2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
        + 10 ^ 11 = _
    rw [twin_rest_rate, e]

theorem approachTickDop_fields (n : ℕ) (hn : n ≤ 60) {w : ℝ} (hw : 0 ≤ w) :
    (approachTickDop (L := L) hL n hn hw).evolve = regEvolve dopFlow dopWeight
    ∧ (approachTickDop (L := L) hL n hn hw).prep = (dopPrep, 0)
    ∧ (approachTickDop (L := L) hL n hn hw).writeStart
      = max 0 (2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
          - 12 * 10 ^ 10)
    ∧ (approachTickDop (L := L) hL n hn hw).writeEnd
      = 2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
          + 12 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★★★ **The Doppler factor of the Dirac chain, read off the records** (BACKLOG #256, one way). On a
ring of length `2π·10¹³` (`c = 1`): the observer at rest `A` (#253) with its clock, the observer `B`
approaching it at `3/5` with its own, and two messengers at `4/5` passing `A` on their way to `B`:

* **one evolution**: the two emissions at `A`, the two receptions at `B` and the ticks of both clocks
  are actual occurrences of the same evolution from the same preparation, which carries all four;
* **the records**: the emissions written within `[e − 1.13·10¹², e − 3.9·10¹¹]`, `e = 4·10¹²` and
  `3.6·10¹³`; the receptions within `[t − 7.5·10¹¹, t + 3.85·10¹¹]`, `t = 1.66·10¹⁴/7` and `4.2·10¹³`;
* **the clocks**: `A` ticks within `10¹¹` of `n · 2π·10¹¹`; `B` within `1.2·10¹¹` of `2πn/R`, its
  splitting `R ∈ [8·10⁻¹², 8.002·10⁻¹²]`, four fifths of the rest splitting;
* **between the ticks**: the emissions between `A`'s ticks `4`–`6` and `55`–`57`, the receptions
  between `B`'s ticks `29`–`31` and `52`–`55`;
* **the factor**: `B` counts `21` to `26` ticks between the receptions while `A` counts `49` to `53`
  between the emissions; the ratio lies in `[21/53, 26/49]`, which contains the relativistic
  `v√(1 − β²)/(v + β) = 16/35` for messengers of speed `v = 4/5` and excludes the Galilean
  `v/(v + β) = 4/7`. -/
theorem dirac_doppler {w : ℝ} (hw : 0 ≤ w) :
    let em₁ := dopEmission₁ (L := L) hL hw
    let em₂ := dopEmission₂ (L := L) hL hw
    let rc₁ := dopReception₁ (L := L) hL hw
    let rc₂ := dopReception₂ (L := L) hL hw
    let a := fun (n : ℕ) (hn : n ≤ 130) => restTickDop (L := L) hL n hn hw
    let b := fun (n : ℕ) (hn : n ≤ 60) => approachTickDop (L := L) hL n hn hw
    let R := levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
    let T : ℝ := 2 * Real.pi * 10 ^ 11
    (em₂.evolve = em₁.evolve ∧ em₂.prep = em₁.prep ∧ rc₁.evolve = em₁.evolve
      ∧ rc₁.prep = em₁.prep ∧ rc₂.evolve = em₁.evolve ∧ rc₂.prep = em₁.prep
      ∧ (∀ n hn, (a n hn).evolve = em₁.evolve ∧ (a n hn).prep = em₁.prep)
      ∧ (∀ n hn, (b n hn).evolve = em₁.evolve ∧ (b n hn).prep = em₁.prep))
    ∧ (∀ t, (em₁.evolve 0 t em₁.prep).1.1.1 = restObserver t
      ∧ (em₁.evolve 0 t em₁.prep).1.2.1.1 = approachObserver (t - 5 * 10 ^ 13)
      ∧ (em₁.evolve 0 t em₁.prep).1.2.2.1 = imagePacket (t - 4 * 10 ^ 12)
      ∧ (em₁.evolve 0 t em₁.prep).1.2.2.2 = imagePacket (t - 36 * 10 ^ 12))
    ∧ (em₁.writeStart = 4 * 10 ^ 12 - 113 * 10 ^ 10 ∧ em₁.writeEnd = 4 * 10 ^ 12 - 39 * 10 ^ 10
      ∧ em₂.writeStart = 36 * 10 ^ 12 - 113 * 10 ^ 10 ∧ em₂.writeEnd = 36 * 10 ^ 12 - 39 * 10 ^ 10
      ∧ rc₁.writeStart = 166 * 10 ^ 12 / 7 - 75 * 10 ^ 10
      ∧ rc₁.writeEnd = 166 * 10 ^ 12 / 7 + 385 * 10 ^ 9
      ∧ rc₂.writeStart = 42 * 10 ^ 12 - 75 * 10 ^ 10 ∧ rc₂.writeEnd = 42 * 10 ^ 12 + 385 * 10 ^ 9)
    ∧ (∀ n hn, (a n hn).writeStart = max 0 ((n : ℝ) * T - 10 ^ 11)
      ∧ (a n hn).writeEnd = (n : ℝ) * T + 10 ^ 11)
    ∧ (8 / 10 ^ 12 ≤ R ∧ R ≤ 8002 / 10 ^ 15
      ∧ ∀ n hn, (b n hn).writeStart = max 0 (2 * Real.pi * (n : ℝ) / R - 12 * 10 ^ 10)
        ∧ (b n hn).writeEnd = 2 * Real.pi * (n : ℝ) / R + 12 * 10 ^ 10)
    ∧ ((a 4 (by norm_num)).writeEnd ≤ em₁.writeStart ∧ em₁.writeEnd ≤ (a 6 (by norm_num)).writeStart
      ∧ (a 55 (by norm_num)).writeEnd ≤ em₂.writeStart
      ∧ em₂.writeEnd ≤ (a 57 (by norm_num)).writeStart)
    ∧ ((b 29 (by norm_num)).writeEnd ≤ rc₁.writeStart
      ∧ rc₁.writeEnd ≤ (b 31 (by norm_num)).writeStart
      ∧ (b 52 (by norm_num)).writeEnd ≤ rc₂.writeStart
      ∧ rc₂.writeEnd ≤ (b 55 (by norm_num)).writeStart)
    ∧ ((52 - 31 : ℝ) / (57 - 4) ≤ 16 / 35 ∧ (16 / 35 : ℝ) ≤ (55 - 29) / (55 - 6)
      ∧ (55 - 29 : ℝ) / (55 - 6) < 4 / 7
      ∧ (16 / 35 : ℝ) = 4 / 5 * Real.sqrt (1 - (3 / 5) ^ 2) / (4 / 5 + 3 / 5)
      ∧ (4 / 7 : ℝ) = 4 / 5 / (4 / 5 + 3 / 5)) := by
  intro em₁ em₂ rc₁ rc₂ a b R T
  have hπ := Real.pi_pos
  have hπ1 : (314 / 100 : ℝ) < Real.pi := by
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  have hπ2 := pi_lt_sixty_three_div_twenty
  obtain ⟨hR1, hR2⟩ := approach_rate (L := L) hL
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  obtain ⟨e1e, e1p, e1s, e1t⟩ := dopEmission₁_fields (L := L) hL hw
  obtain ⟨e2e, e2p, e2s, e2t⟩ := dopEmission₂_fields (L := L) hL hw
  obtain ⟨r1e, r1p, r1s, r1t⟩ := dopReception₁_fields (L := L) hL hw
  obtain ⟨r2e, r2p, r2s, r2t⟩ := dopReception₂_fields (L := L) hL hw
  have hA := fun n hn => restTickDop_fields (L := L) hL n hn hw
  have hB := fun n hn => approachTickDop_fields (L := L) hL n hn hw
  have hdivlo : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
        ≤ 2 * Real.pi * k / (8 / 10 ^ 12) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) (by norm_num) hR1
  have hdivhi : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / (8002 / 10 ^ 15)
      ≤ 2 * Real.pi * k / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) hR0 hR2
  refine ⟨⟨e2e.trans e1e.symm, e2p.trans e1p.symm, r1e.trans e1e.symm, r1p.trans e1p.symm,
      r2e.trans e1e.symm, r2p.trans e1p.symm,
      fun n hn => ⟨(hA n hn).1.trans e1e.symm, (hA n hn).2.1.trans e1p.symm⟩,
      fun n hn => ⟨(hB n hn).1.trans e1e.symm, (hB n hn).2.1.trans e1p.symm⟩⟩,
    fun t => ?_, ⟨e1s, e1t, e2s, e2t, r1s, r1t, r2s, r2t⟩,
    fun n hn => ⟨(hA n hn).2.2.1, (hA n hn).2.2.2⟩,
    ⟨hR1, hR2, fun n hn => ⟨(hB n hn).2.2.1, (hB n hn).2.2.2⟩⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩⟩
  · rw [e1e, e1p]
    show ((dopFlow (t - 0) dopPrep).1.1 = _ ∧ (dopFlow (t - 0) dopPrep).2.1.1 = _
      ∧ (dopFlow (t - 0) dopPrep).2.2.1 = _ ∧ (dopFlow (t - 0) dopPrep).2.2.2 = _)
    rw [sub_zero]
    exact ⟨dopFlow_prep_rest t, dopFlow_prep_approach t, dopFlow_prep_messenger₁ t,
      dopFlow_prep_messenger₂ t⟩
  · rw [(hA 4 (by norm_num)).2.2.2, e1s]
    push_cast
    nlinarith
  · rw [(hA 6 (by norm_num)).2.2.1, e1t]
    refine le_max_of_le_right ?_
    push_cast
    nlinarith
  · rw [(hA 55 (by norm_num)).2.2.2, e2s]
    push_cast
    nlinarith
  · rw [(hA 57 (by norm_num)).2.2.1, e2t]
    refine le_max_of_le_right ?_
    push_cast
    nlinarith
  · rw [(hB 29 (by norm_num)).2.2.2, r1s]
    have h := hdivlo ((29 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 29 / (8 / 10 ^ 12) = Real.pi * (58 * 10 ^ 12 / 8) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 31 (by norm_num)).2.2.1, r1t]
    refine le_max_of_le_right ?_
    have h := hdivhi ((31 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 31 / (8002 / 10 ^ 15) = Real.pi * (62 * 10 ^ 15 / 8002) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 52 (by norm_num)).2.2.2, r2s]
    have h := hdivlo ((52 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 52 / (8 / 10 ^ 12) = Real.pi * (104 * 10 ^ 12 / 8) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 55 (by norm_num)).2.2.1, r2t]
    refine le_max_of_le_right ?_
    have h := hdivhi ((55 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 55 / (8002 / 10 ^ 15) = Real.pi * (110 * 10 ^ 15 / 8002) by ring] at h
    push_cast
    linarith
  · rw [show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

end Factor

end CSD.RecordLayer

end
