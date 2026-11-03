/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracRelayA

/-!
# The moving observer's radar: where `B` and its messenger meet

**Category:** 7-SigmaLayer (the record layer). BACKLOG #278, second landing, third part (first
stage).

`B` sends its massless messenger at `t = 0` and `A` returns it (`DiracRelayA.lean`). `B`'s records —
the emission and the return — will be one register integrating `B`'s encounter weight with the
messenger, clipped at `1/2`, read at two thresholds. This stage proves what that register sees: the
devices of the relay flow run free from every start, `B` and the messenger are sharply located, and
`B`'s encounter weight with the messenger — the free one at departure, the echo at the return — is
high when their relative angle is within `0.18` and low beyond `0.23`. The encounter window is
`B`'s relational window of chord `1/5`, wide enough that the return's gain outruns the departure's
uncertainty.

## The devices from every start

* ★★ `devA_aRelayFlow_any`, ★★ `devB_aRelayFlow_any` — **`A`'s and `B`'s devices run by
  `e^{−itH_dev}` from every start of the relay flow at `A`**.

## Where `B` is, sharply

* ★ `approach_tail_fine` (`B` off its chord-`1/100` arc: `≤ 2.3·10⁻²`), `bMess_univ`.

## `B` and the messenger

* `relWeight_levelLift_echo` — **the echo's encounter weight is the free messenger's** (the band
  flip does not change site weights);
* ★★ `bEncounter_near` — **if the messenger's predicted angle at its own time `t'` is within `0.18`
  of `B`'s at time `t`, the encounter weight is at least `0.977 · 0.989`**; ★★ `bEncounter_far` —
  **beyond `0.23` it is at most `3.4·10⁻²`** (for the free messenger `t' = t`; for the echo
  `t' = 2s₀ + 3·10⁻³ − t`).

## `B`'s register along the flow

* `bEnc` (`B`'s clipped encounter weight, window chord `1/5`), `continuous_bEnc`, `bEnc_nonneg`,
  `bRate` (its value along the relay flow at `A`), `continuous_bRate`, `bRate_nonneg`, `bRate_eq`,
  `bRate_le_half`, `abs_relWeight_B_sub_le` (close messengers, close encounter weights);
* for the crossing time `s₀` of `dirac_relay_at_rest`: `s₀_bounds`, `bRate_eq_free`,
  ★ `bRate_ge_depart` (**at departure, `t ≤ 4.5·10¹²`, the rate is at least `0.4662`**),
  ★ `bRate_eq_zero_depart` (zero from `5.75·10¹²` to `s₀`), ★ `bRate_eq_zero_pulse` (zero during
  the pulse — the rotation is invisible), `echo_eq`, `abs_relWeight_return_sub_le` (the echo's
  encounter weight to `0.0252`), ★ `bRate_eq_zero_return` (zero until
  `(2s₀ + 3·10⁻³)/1.6 − 1.4375·10¹²`), ★★ `bRate_ge_return` (**within `1.125·10¹²` of
  `(2s₀ + 3·10⁻³)/1.6` the rate is at least `0.441`**).

## The register and the records

* `integral_bRate_le_half`, ★ `integral_bRate_flight` (**flat at `≤ 2.875·10¹²` through the
  flight**), ★★ `integral_bRate_return` (**`≥ 3·10¹²` once the echo has passed `B`**: departure plus
  the return's window);
* `bRadarWeight` (four registers: `B`'s encounter with the messenger, `A`'s and `B`'s clocks'
  rates, `B`'s encounter with `A`), `bRadarWeight_zero`, `bRadarWeight_one`, `bRadarWeight_two`,
  `bRadarWeight_three`, `continuous_bRadarWeight`,
  `bRadarEvolve`, `bRadarEvolve_self`, `bRadarEvolve_comp`, `measurable_bRadarEvolve`, `bRadarPrep`,
  `bRadarEvolve_prep_fst`;
* ★★★ `bEmission` (**`B`'s register reaches `10¹²` within `[2·10¹², 2.15·10¹²]`**), `aRelayRead`,
  `measurable_aRelayRead`, ★★★ `aReception` (**`A`'s relay register reaches `3·10¹¹` within
  `[3·10¹³ − 8·10¹¹, 3·10¹³]`** — the relay's firing is the record), ★★★ `bReturn` (**the same
  register of `B` reaches `3·10¹²` within `[3.5·10¹³, 3.87·10¹³]`** — the echo back at `B`).

## The clocks and the bundle

* `meetRaw_aRelayFlow` (the encounter of `A` and `B` reads only the devices, alike in both relay
  arenas), `integral_bRadarWeight_three`, ★★★ `bMeeting` (**the meeting, `dirac_radar`'s window**),
  `bMeeting_fields`;
* `bRestTick`, `bApproachTick` (both clocks' ticks, pulled back into `B`'s radar arena along the
  devices and the tick registers it carries); `bEmission_fields`, `aReception_fields`,
  `bReturn_fields`, `bRestTick_fields`, `bApproachTick_fields`;
* ★★★ `dirac_b_radar` (**`B`'s radar, one evolution**: emission, `A`'s relay firing, return and
  both clocks' ticks; the record windows in order; `B`'s emission between its ticks `2`–`3`, its
  return between `44`–`50`, the meeting between `61`–`65`; `A`'s reception between `A`'s ticks
  `46`–`48`, the meeting between `76`–`81`).

References: `specs/BACKLOG.md` #278, #274; `RecordLayer/DiracRelayA.lean` (`aRelayFlow`,
`bMess_tail_fine`, `rest_tail_fine`, `dirac_relay_at_rest`); `RecordLayer/DiracRadar.lean`
(`devA_relayFlow_any`, `regionWeight_echo`, `siteWeight_neg_I_smul`);
`RecordLayer/DiracDoppler.lean` (`approach_tail`, `rel_offset`, `offset_mem_of_near_at`,
`offset_not_mem_of_far_at`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV CSD.SigmaLayer
open scoped Matrix NNReal

namespace CSD.RecordLayer

variable {L : ℕ} [NeZero L]

/-! ### The devices from every start -/

/-- ★★ **`A`'s device runs by `e^{−itH_dev}` from every start of the relay flow at `A`.** -/
theorem devA_aRelayFlow_any (x : GateArena (RelayIdx L)) (t : ℝ) :
    devA (aRelayFlow t x).1 = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devA x.1 := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (aRelayFlow t x).1 0 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devA x.1) (q, 0)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devA x.1) 0
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 0 = aRelayMass 0 by
      simp [levelMass, aRelayMass_zero]] at h
    refine congrFun (gatedFlow_block_eq aRelayLipschitz x (k := 0) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl
  · show blockOf (aRelayFlow t x).1 1 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devA x.1) (q, 1)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devA x.1) 1
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 1 = aRelayMass 1 by
      simp [levelMass, aRelayMass_one]] at h
    refine congrFun (gatedFlow_block_eq aRelayLipschitz x (k := 1) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl

/-- ★★ **`B`'s device runs by `e^{−itH_dev}` from every start of the relay flow at `A`.** -/
theorem devB_aRelayFlow_any (x : GateArena (RelayIdx L)) (t : ℝ) :
    devB (aRelayFlow t x).1 = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devB x.1 := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (aRelayFlow t x).1 2 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devB x.1) (q, 0)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devB x.1) 0
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 0 = aRelayMass 2 by
      simp [levelMass, aRelayMass_two]] at h
    refine congrFun (gatedFlow_block_eq aRelayLipschitz x (k := 2) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl
  · show blockOf (aRelayFlow t x).1 3 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devB x.1) (q, 1)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devB x.1) 1
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 1 = aRelayMass 3 by
      simp [levelMass, aRelayMass_three]] at h
    refine congrFun (gatedFlow_block_eq aRelayLipschitz x (k := 3) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl

/-! ### `B` and the messenger -/

/-- **The echo's encounter weight is the free messenger's**: `−i σ_y` does not change site
weights. -/
theorem relWeight_levelLift_echo (w : ℂ) (ρ : ℝ) (ΨA : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (v : ZMod L × Fin 2 → ℂ) :
    relWeight w ρ ΨA (levelLift 0 ((-I) • (spinY *ᵥ v))) = relWeight w ρ ΨA (levelLift 0 v) := by
  simp only [relWeight, devSiteWeight_levelLift, siteWeight_neg_I_smul, siteWeight_spinY]

section WithL

variable (hL : 10 ^ 19 ≤ L)
include hL

/-- ★ **`B` off its chord-`1/100` arc**: at most `2.3·10⁻²` of its weight. -/
theorem approach_tail_fine {s : ℝ} (hs : |s| ≤ 8 * 10 ^ 13) :
    devRegionWeight (approachObserver (L := L) s)
        (chordArc (exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))) (1 / 100))ᶜ ≤ 23 / 1000 := by
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
    twinAmp (twin_norm hL _) (z := exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))) (ρ := 1 / 100)
    (η := 1 / 10 ^ 9) (by norm_num) s hz₀ hz₁
  have b0 := twin_budget (L := L) hL (μ := 3) le_rfl (225 * 10 ^ 11) (D := 2 / 10 ^ 7) (P := 9 / 4)
    (by positivity) le_rfl (by norm_num) (by norm_num) (abs_nonneg s) hs
  have b1 := twin_budget (L := L) hL (μ := 3 + 1 / 10 ^ 11) (by norm_num) (225 * 10 ^ 11)
    (D := 2 / 10 ^ 7) (P := 9 / 4) (by positivity) le_rfl (by norm_num) (by norm_num)
    (abs_nonneg s) hs
  rw [abs_abs] at b0 b1
  have hnn := devRegionWeight_nonneg (approachObserver (L := L) s)
    (chordArc (exp (I * ((6 / 10 ^ 14 * s : ℝ) : ℂ))) (1 / 100))ᶜ
  unfold approachObserver at hnn ⊢
  nlinarith

/-- The messenger's total weight. -/
theorem bMess_univ (t : ℝ) : regionWeight (bMess (L := L) t) Finset.univ = 1 := by
  have := regionWeight_add_compl (bMess (L := L) t) Finset.univ
  rw [bMess_norm hL, Complex.one_re, Finset.compl_univ] at this
  simpa [regionWeight] using this

/-- ★★ **`B` meets the messenger**: if the messenger's predicted angle at its own time `t'` is
within `0.18` of `B`'s at time `t`, `B`'s encounter weight with it (window chord `1/5`) is at least
`(1 − 0.023)(1 − 0.011)`. -/
theorem bEncounter_near {t t' : ℝ} (ht0 : 0 ≤ t) (ht8 : t ≤ 8 * 10 ^ 13) (ht'0 : 0 ≤ t')
    (ht'8 : t' ≤ 8 * 10 ^ 13)
    (h : |1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)| ≤ 18 / 100) :
    (1 - 23 / 1000) * (1 - 11 / 1000) ≤ relWeight 1 (1 / 5)
      (approachObserver (L := L) (t - 5 * 10 ^ 13)) (levelLift 0 (bMess (L := L) t')) := by
  have tB := approach_tail_fine hL (s := t - 5 * 10 ^ 13)
    (by rw [abs_le]; constructor <;> linarith)
  have tm := bMess_tail_fine hL ht'0 ht'8
  have hX := devRegionWeight_add_compl (approachObserver (L := L) (t - 5 * 10 ^ 13))
    (chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
  rw [approach_total hL] at hX
  have hY := regionWeight_add_compl (bMess (L := L) t')
    (chordArc (exp (I * ((1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
  rw [bMess_norm hL, Complex.one_re] at hY
  have hoff : ‖exp (I * ((1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) : ℝ) : ℂ))
      * star (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) - 1‖ ≤ 18 / 100 := by
    rw [rel_offset]
    have := norm_exp_sub_exp_le
      (1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)) 0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero] at this
    exact this.trans h
  have hle := le_relWeight (w := 1) (ρ := 1 / 5)
    (ΨA := approachObserver (L := L) (t - 5 * 10 ^ 13)) (ΨB := levelLift 0 (bMess (L := L) t'))
    (X := chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
    (Y := chordArc (exp (I * ((1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
    fun j hj k hk =>
      offset_mem_of_near_at (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj)
        (mem_chordArc.1 hk) (by linarith)
  rw [devRegionWeight_levelLift] at hle
  have hA : 1 - 23 / 1000 ≤ devRegionWeight (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100)) := by linarith
  have hB : 1 - 11 / 1000 ≤ regionWeight (bMess (L := L) t')
      (chordArc (exp (I * ((1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100)) := by linarith
  calc (1 - 23 / 1000) * (1 - 11 / 1000)
      ≤ _ := mul_le_mul hA hB (by norm_num) (devRegionWeight_nonneg _ _)
    _ ≤ _ := hle

/-- ★★ **`B` away from the messenger**: while their relative angle is at least `0.23` from every
multiple of `2π`, the encounter weight is at most `3.4·10⁻²`. -/
theorem bEncounter_far {t t' : ℝ} (ht0 : 0 ≤ t) (ht8 : t ≤ 8 * 10 ^ 13) (ht'0 : 0 ≤ t')
    (ht'8 : t' ≤ 8 * 10 ^ 13)
    (h1 : 23 / 100 ≤ |1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)|)
    (h2 : |1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)|
      ≤ 2 * Real.pi - 23 / 100) :
    relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (levelLift 0 (bMess (L := L) t')) ≤ 34 / 1000 := by
  have tB := approach_tail_fine hL (s := t - 5 * 10 ^ 13)
    (by rw [abs_le]; constructor <;> linarith)
  have tm := bMess_tail_fine hL ht'0 ht'8
  have hsin := Real.sin_gt_sub_cube (x := 23 / 100 / 2) (by norm_num)
  have hfar := two_sin_le_norm_exp_sub_one (y := 23 / 100)
    (z := 1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)) (by norm_num) h1 h2
  have : (22 / 100 : ℝ) < 2 * (23 / 100 / 2 - (23 / 100 / 2) ^ 3 / 6) := by norm_num
  have hoff : 22 / 100 < ‖exp (I * ((1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) : ℝ) : ℂ))
      * star (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) - 1‖ := by
    rw [rel_offset]
    linarith
  have hle := relWeight_le (w := 1) (ρ := 1 / 5)
    (ΨA := approachObserver (L := L) (t - 5 * 10 ^ 13)) (ΨB := levelLift 0 (bMess (L := L) t'))
    (X := chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
    (Y := chordArc (exp (I * ((1 / 10 ^ 13 * (t' - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
    fun j hj k hk =>
      offset_not_mem_of_far_at (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj)
        (mem_chordArc.1 hk) (by linarith)
  rw [devRegionWeight_levelLift, devRegionWeight_levelLift, approach_total hL,
    bMess_univ hL, mul_one, one_mul] at hle
  linarith

/-! ### `B`'s register along the flow -/

/-- **`B`'s clipped encounter weight with the messenger** (window chord `1/5`). -/
noncomputable def bEnc (Ψ : RelayIdx L → ℂ) : ℝ :=
  max (relWeight 1 (1 / 5) (devB Ψ) (levelLift 0 (mess Ψ)) - 1 / 2) 0

omit hL in
theorem continuous_bEnc : Continuous (bEnc (L := L)) :=
  ((continuous_relWeight_comp continuous_devB (continuous_levelLift_zero.comp continuous_mess) 1
    (1 / 5)).sub continuous_const).max continuous_const

omit hL in
theorem bEnc_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ bEnc Ψ := le_max_right _ _

/-- **`B`'s register rate along the flow.** -/
noncomputable def bRate (L : ℕ) [NeZero L] (t : ℝ) : ℝ := bEnc (aRelayFlow t (aRelayPrep L)).1

omit hL in
theorem continuous_bRate : Continuous (bRate L) :=
  continuous_bEnc.comp (continuous_fst.comp (continuous_gatedFlow_time _ _))

omit hL in
theorem bRate_nonneg (t : ℝ) : 0 ≤ bRate L t := bEnc_nonneg _

omit hL in
theorem bRate_eq (t : ℝ) :
    bRate L t = max (relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (levelLift 0 (mess (aRelayFlow t (aRelayPrep L)).1)) - 1 / 2) 0 := by
  rw [bRate, bEnc, devB_aRelayFlow]

/-- The rate never exceeds `1/2`. -/
theorem bRate_le_half (t : ℝ) : bRate L t ≤ 1 / 2 := by
  rw [bRate_eq]
  have h := relWeight_le_mul 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
    (levelLift 0 (mess (aRelayFlow t (aRelayPrep L)).1))
  have hm : devRegionWeight (levelLift 0 (mess (aRelayFlow t (aRelayPrep L)).1)) Finset.univ
      = 1 := by
    rw [devRegionWeight_levelLift, regionWeight, ← sqNorm_eq_sum_siteWeight]
    exact sqNorm_mess_aRelayFlow hL t
  rw [approach_total hL, hm, one_mul] at h
  exact max_le (by linarith) (by norm_num)

/-- **Two close messengers have close encounter weights with `B`.** -/
theorem abs_relWeight_B_sub_le (t : ℝ) {ψ χ : ZMod L × Fin 2 → ℂ} (hψ : sqNorm ψ = 1)
    (hχ : sqNorm χ = 1) {d : ℝ} (hd : sqNorm (ψ - χ) ≤ d) {ε : ℝ} (hε : Real.sqrt d ≤ ε) :
    |relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13)) (levelLift 0 ψ)
      - relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13)) (levelLift 0 χ)|
      ≤ 2 * ε := by
  have e1 := abs_relWeight_levelLift_sub_le 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
    ψ χ
  have e1' := sum_abs_norm_sq_sub_le ψ χ
  have hsqrt4 : Real.sqrt (2 * 1 + 2 * 1) = 2 := by
    rw [show (2 : ℝ) * 1 + 2 * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hψ, hχ, hsqrt4] at e1'
  rw [approach_total hL, one_mul] at e1
  have hs : Real.sqrt (sqNorm (ψ - χ)) ≤ ε := (Real.sqrt_le_sqrt hd).trans hε
  linarith

variable {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk)
  (hfreeOn : ∀ t ∈ Icc (0 : ℝ) s₀, aRelayFlow t (aRelayPrep L) = (aRelayState t, aRelayReg L t))
include hs₀ hfreeOn

omit [NeZero L] hL hfreeOn in
theorem s₀_bounds : 29 * 10 ^ 12 ≤ s₀ ∧ s₀ ≤ 3 * 10 ^ 13 := by
  have htk : aRelayTk = 3 * 10 ^ 13 := rfl
  obtain ⟨h1, h2⟩ := hs₀
  rw [htk] at h1 h2
  constructor <;> linarith

omit hL hs₀ in
/-- **Before the flip the messenger is the free one.** -/
theorem bRate_eq_free {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s₀) :
    bRate L t = max (relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (levelLift 0 (bMess (L := L) t)) - 1 / 2) 0 := by
  rw [bRate_eq, hfreeOn t ⟨ht0, ht⟩, mess_aRelayState]

/-- **At departure the rate is at least `0.977 · 0.989 − 1/2`.** -/
theorem bRate_ge_depart {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 45 * 10 ^ 11) :
    (1 - 23 / 1000) * (1 - 11 / 1000) - 1 / 2 ≤ bRate L t := by
  have hb := s₀_bounds hs₀
  rw [bRate_eq_free hfreeOn ht0 (by linarith)]
  have hnear := bEncounter_near hL (t := t) (t' := t) ht0 (by linarith) ht0 (by linarith)
    (by rw [abs_le]; constructor <;> nlinarith)
  exact le_max_of_le_left (by linarith)

/-- **After departure, until the flip, the rate is zero.** -/
theorem bRate_eq_zero_depart {t : ℝ} (ht0 : 575 * 10 ^ 10 ≤ t) (ht : t ≤ s₀) : bRate L t = 0 := by
  have hb := s₀_bounds hs₀
  have hπ := pi_gt_314
  rw [bRate_eq_free hfreeOn (by linarith) ht]
  have e : 1 / 10 ^ 13 * (t - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13) = 4 / 10 ^ 14 * t := by
    ring
  have hfar := bEncounter_far hL (t := t) (t' := t) (by linarith) (by linarith) (by linarith)
    (by linarith) (by rw [e, abs_of_nonneg (by positivity)]; linarith)
    (by rw [e, abs_of_nonneg (by positivity)]; nlinarith)
  exact max_eq_right (by linarith)

omit hfreeOn in
/-- **During the pulse the rate is zero**: the messenger is at `A`, and the rotation is
invisible. -/
theorem bRate_eq_zero_pulse (hfree' : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo))
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 3 / 1000) : bRate L (s₀ + u) = 0 := by
  have hb := s₀_bounds hs₀
  have hπ := pi_gt_314
  set θ := ∫ s in (0 : ℝ)..u, relayGate relayLo relayHi aRelayWeight
    (aRelayFlow (s₀ + s) (aRelayPrep L)).1 (aRelayFlow (s₀ + s) (aRelayPrep L)).2
  have h1 := sqNorm_mess_aRelayFlow_sub_le hL hfree' hu0
  have hrot : sqNorm (gateRot spinY θ *ᵥ bMess (L := L) s₀) = 1 := by
    rw [sqNorm_gateRot_mulVec spinY_isHermitian spinY_mulVec_spinY, sqNorm_bMess hL]
  have hd := abs_relWeight_B_sub_le hL (s₀ + u) (sqNorm_mess_aRelayFlow hL _) hrot h1
    (ε := 3 / 1000 * (42 / 10)) (by
      rw [Real.sqrt_le_left (by norm_num)]
      calc u ^ 2 * 17 ≤ (3 / 1000) ^ 2 * 17 := by gcongr
        _ ≤ (3 / 1000 * (42 / 10)) ^ 2 := by norm_num)
  rw [relWeight_levelLift_gateRot_spinY] at hd
  have e : 1 / 10 ^ 13 * (s₀ - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (s₀ + u - 5 * 10 ^ 13)
      = 4 / 10 ^ 14 * s₀ - 6 / 10 ^ 14 * u := by ring
  have hfar := bEncounter_far hL (t := s₀ + u) (t' := s₀) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (by rw [e, abs_of_nonneg (by nlinarith)]; nlinarith)
    (by rw [e, abs_of_nonneg (by nlinarith)]; nlinarith)
  rw [bRate_eq]
  exact max_eq_right (by linarith [(abs_le.1 hd).2])

omit hL hs₀ hfreeOn in
/-- The echo at time `t`, as the free messenger at its reflected time. -/
theorem echo_eq (t : ℝ) :
    ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp
        (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - t)
      = bMess (2 * s₀ + 3 / 1000 - t) := by
  rw [bMess]
  congr 1
  ring

omit hfreeOn in
/-- **After the pulse the encounter weight is the echo's to `0.0252`.** -/
theorem abs_relWeight_return_sub_le
    (hfree' : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo))
    {t : ℝ} (ht : s₀ + 3 / 1000 ≤ t) :
    |relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
        (levelLift 0 (mess (aRelayFlow t (aRelayPrep L)).1))
      - relWeight 1 (1 / 5) (approachObserver (L := L) (t - 5 * 10 ^ 13))
        (levelLift 0 (bMess (L := L) (2 * s₀ + 3 / 1000 - t)))| ≤ 2 * (3 / 1000 * (42 / 10)) := by
  have h := sqNorm_mess_aReturn_le hL hs₀ hfree' ht
  rw [echo_eq] at h
  have hecho : sqNorm ((-I) • (spinY *ᵥ bMess (L := L) (2 * s₀ + 3 / 1000 - t))) = 1 := by
    rw [sqNorm_echo, sqNorm_bMess hL]
  have hd := abs_relWeight_B_sub_le hL t (sqNorm_mess_aRelayFlow hL _) hecho h
    (ε := 3 / 1000 * (42 / 10)) (by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num)
  rwa [relWeight_levelLift_echo] at hd

omit hfreeOn in
/-- **On the way back, while the echo is far from `B`, the rate is zero.** -/
theorem bRate_eq_zero_return (hfree' : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo))
    {t : ℝ} (ht : s₀ + 3 / 1000 ≤ t)
    (hfar : t ≤ (2 * s₀ + 3 / 1000) / (16 / 10) - 14375 * 10 ^ 8) : bRate L t = 0 := by
  have hb := s₀_bounds hs₀
  have hπ := pi_gt_314
  have hd := abs_relWeight_return_sub_le hL hs₀ hfree' ht
  have e : 1 / 10 ^ 13 * ((2 * s₀ + 3 / 1000 - t) - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)
      = 1 / 10 ^ 13 * (2 * s₀ + 3 / 1000) - 16 / 10 ^ 14 * t := by ring
  have hpos : 0 ≤ 1 / 10 ^ 13 * (2 * s₀ + 3 / 1000) - 16 / 10 ^ 14 * t := by
    have := hfar
    nlinarith
  have hfarB := bEncounter_far hL (t := t) (t' := 2 * s₀ + 3 / 1000 - t) (by linarith)
    (by nlinarith) (by nlinarith) (by linarith)
    (by rw [e, abs_of_nonneg hpos]; nlinarith) (by rw [e, abs_of_nonneg hpos]; nlinarith)
  rw [bRate_eq]
  exact max_eq_right (by linarith [(abs_le.1 hd).1, (abs_le.1 hd).2])

omit hfreeOn in
/-- **When the echo reaches `B` the rate is at least `0.977 · 0.989 − 0.0252 − 1/2`.** -/
theorem bRate_ge_return (hfree' : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo))
    {t : ℝ} (hnear : |t - (2 * s₀ + 3 / 1000) / (16 / 10)| ≤ 1125 * 10 ^ 9) :
    (1 - 23 / 1000) * (1 - 11 / 1000) - 2 * (3 / 1000 * (42 / 10)) - 1 / 2 ≤ bRate L t := by
  have hb := s₀_bounds hs₀
  rw [abs_le] at hnear
  have ht : s₀ + 3 / 1000 ≤ t := by nlinarith
  have hd := abs_relWeight_return_sub_le hL hs₀ hfree' ht
  have e : 1 / 10 ^ 13 * ((2 * s₀ + 3 / 1000 - t) - 3 * 10 ^ 13) - 6 / 10 ^ 14 * (t - 5 * 10 ^ 13)
      = 1 / 10 ^ 13 * (2 * s₀ + 3 / 1000) - 16 / 10 ^ 14 * t := by ring
  have hnearB := bEncounter_near hL (t := t) (t' := 2 * s₀ + 3 / 1000 - t) (by linarith)
    (by nlinarith) (by nlinarith) (by linarith)
    (by rw [e, abs_le]; constructor <;> nlinarith)
  rw [bRate_eq]
  exact le_max_of_le_left (by linarith [(abs_le.1 hd).1, (abs_le.1 hd).2])

/-! ### `B`'s register: the integral -/

omit hs₀ hfreeOn in
/-- The register never exceeds half the elapsed time. -/
theorem integral_bRate_le_half {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, bRate L s ≤ t / 2 := by
  have h := intervalIntegral.integral_mono_on ht
    ((continuous_bRate (L := L)).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ))) fun s _ => bRate_le_half hL s
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

omit hfreeOn in
/-- **Through the flight the register is flat**: from `5.75·10¹²` until the echo approaches, the
rate is zero, so the register stays at most `2.875·10¹²`. -/
theorem integral_bRate_flight
    (hfree' : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo))
    (hfreeOn' : ∀ t ∈ Icc (0 : ℝ) s₀,
      aRelayFlow t (aRelayPrep L) = (aRelayState t, aRelayReg L t))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (2 * s₀ + 3 / 1000) / (16 / 10) - 14375 * 10 ^ 8) :
    ∫ s in (0 : ℝ)..t, bRate L s ≤ 2875 * 10 ^ 9 := by
  have hb := s₀_bounds hs₀
  rcases le_total t (575 * 10 ^ 10) with h | h
  · exact (integral_bRate_le_half hL ht0).trans (by linarith)
  have hi : ∀ x y : ℝ, IntervalIntegrable (bRate L) volume x y :=
    fun x y => (continuous_bRate (L := L)).intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (575 * 10 ^ 10))
    (hi (575 * 10 ^ 10) t)]
  have hzero : ∫ s in (575 * 10 ^ 10 : ℝ)..t, bRate L s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · exact intervalIntegral.integral_zero
    · rw [Set.uIcc_of_le h] at hs
      show bRate L s = 0
      rcases le_total s s₀ with h1 | h1
      · exact bRate_eq_zero_depart hL hs₀ hfreeOn' hs.1 h1
      rcases le_total s (s₀ + 3 / 1000) with h2 | h2
      · have := bRate_eq_zero_pulse hL hs₀ hfree' (u := s - s₀) (by linarith) (by linarith)
        rwa [add_sub_cancel] at this
      · exact bRate_eq_zero_return hL hs₀ hfree' h2 (hs.2.trans ht)
  rw [hzero, add_zero]
  exact (integral_bRate_le_half hL (by norm_num)).trans (by norm_num)

omit hfreeOn in
/-- **After the echo has passed `B` the register is at least `3·10¹²`.** -/
theorem integral_bRate_return
    (hfree' : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo))
    (hfreeOn' : ∀ t ∈ Icc (0 : ℝ) s₀,
      aRelayFlow t (aRelayPrep L) = (aRelayState t, aRelayReg L t))
    {t : ℝ} (ht : (2 * s₀ + 3 / 1000) / (16 / 10) + 1125 * 10 ^ 9 ≤ t) :
    3 * 10 ^ 12 ≤ ∫ s in (0 : ℝ)..t, bRate L s := by
  have hb := s₀_bounds hs₀
  set c := (2 * s₀ + 3 / 1000) / (16 / 10) with hc
  have hc1 : 45 * 10 ^ 11 ≤ c - 1125 * 10 ^ 9 := by rw [hc]; nlinarith
  have h := le_integral_two_windows (continuous_bRate (L := L))
    (κ₁ := (1 - 23 / 1000) * (1 - 11 / 1000) - 1 / 2)
    (κ₂ := (1 - 23 / 1000) * (1 - 11 / 1000) - 2 * (3 / 1000 * (42 / 10)) - 1 / 2)
    (a := 0) (b := 45 * 10 ^ 11) (c := c - 1125 * 10 ^ 9) (d := c + 1125 * 10 ^ 9) (t := t)
    le_rfl (by norm_num) hc1 (by linarith) ht (fun s _ => bRate_nonneg s)
    (fun s hs1 hs2 => bRate_ge_depart hL hs₀ hfreeOn' hs1.le hs2.le)
    (fun s hs1 hs2 => bRate_ge_return hL hs₀ hfree' (by rw [abs_le]; constructor <;> linarith))
  refine le_trans ?_ h
  norm_num

/-! ### The record arena -/

omit hL hs₀ hfreeOn in
/-- **The rates of `B`'s radar arena's four registers**: `B`'s clipped encounter weight with the
messenger, `A`'s clock's rate, `B`'s clock's rate, `B`'s clipped encounter weight with `A`. -/
noncomputable def bRadarWeight : Fin 4 → GateArena (RelayIdx L) → ℝ :=
  ![fun x => bEnc x.1,
    fun x => rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) (tickMark (restObserver (L := L) 0))
      (devA x.1),
    fun x => rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
      (tickMark (approachObserver (L := L) (-(5 * 10 ^ 13)))) (devB x.1),
    fun x => meetRaw x.1]

omit hL hs₀ hfreeOn in
theorem bRadarWeight_zero : bRadarWeight (L := L) 0 = fun x => bEnc x.1 := by
  simp [bRadarWeight]

omit hL hs₀ hfreeOn in
theorem bRadarWeight_one : bRadarWeight (L := L) 1 = fun x =>
    rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) (tickMark (restObserver (L := L) 0))
      (devA x.1) := by
  simp [bRadarWeight]

omit hL hs₀ hfreeOn in
theorem bRadarWeight_two : bRadarWeight (L := L) 2 = fun x =>
    rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
      (tickMark (approachObserver (L := L) (-(5 * 10 ^ 13)))) (devB x.1) := by
  simp [bRadarWeight]

omit hL hs₀ hfreeOn in
theorem bRadarWeight_three : bRadarWeight (L := L) 3 = fun x => meetRaw x.1 := by
  simp [bRadarWeight]

omit hL hs₀ hfreeOn in
theorem continuous_bRadarWeight (i : Fin 4) :
    Continuous fun p : GateArena (RelayIdx L) × ℝ => bRadarWeight i (aRelayFlow p.2 p.1) := by
  have hflow : Continuous fun p : GateArena (RelayIdx L) × ℝ => (aRelayFlow p.2 p.1).1 :=
    continuous_fst.comp
      ((continuous_gatedFlow aRelayLipschitz).comp (continuous_snd.prodMk continuous_fst))
  fin_cases i
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => bRadarWeight 0 (aRelayFlow p.2 p.1)
    rw [bRadarWeight_zero]
    exact continuous_bEnc.comp hflow
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => bRadarWeight 1 (aRelayFlow p.2 p.1)
    rw [bRadarWeight_one]
    exact (continuous_rateWeight _ _ _ _).comp (continuous_devA.comp hflow)
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => bRadarWeight 2 (aRelayFlow p.2 p.1)
    rw [bRadarWeight_two]
    exact (continuous_rateWeight _ _ _ _).comp (continuous_devB.comp hflow)
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => bRadarWeight 3 (aRelayFlow p.2 p.1)
    rw [bRadarWeight_three]
    exact continuous_meetRaw.comp hflow

omit hL hs₀ hfreeOn in
/-- **`B`'s radar arena**: the relay flow at `A` with four registers. -/
noncomputable def bRadarEvolve :
    OnticTime → OnticTime → GateArena (RelayIdx L) × (Fin 4 → ℝ)
      → GateArena (RelayIdx L) × (Fin 4 → ℝ) :=
  regEvolve aRelayFlow bRadarWeight

omit hL hs₀ hfreeOn in
theorem bRadarEvolve_self (t : OnticTime) : bRadarEvolve (L := L) t t = id :=
  regEvolve_self aRelayFlow bRadarWeight (fun x => gatedFlow_zero aRelayLipschitz x) t

omit hL hs₀ hfreeOn in
theorem bRadarEvolve_comp (s t u : OnticTime) :
    bRadarEvolve t u ∘ bRadarEvolve s t = bRadarEvolve (L := L) s u :=
  regEvolve_comp aRelayFlow bRadarWeight (fun s t x => gatedFlow_add aRelayLipschitz s t x)
    continuous_bRadarWeight s t u

omit hL hs₀ hfreeOn in
theorem measurable_bRadarEvolve (s t : OnticTime) : Measurable (bRadarEvolve (L := L) s t) :=
  measurable_regFlow aRelayFlow bRadarWeight (fun t => measurable_gatedFlow aRelayLipschitz t)
    continuous_bRadarWeight (t - s)

omit hL hs₀ hfreeOn in
/-- **The preparation**: the relay flow's, every register at `0`. -/
noncomputable def bRadarPrep (L : ℕ) [NeZero L] : GateArena (RelayIdx L) × (Fin 4 → ℝ) :=
  (aRelayPrep L, 0)

omit hL hs₀ hfreeOn in
theorem bRadarEvolve_prep_fst (t : ℝ) :
    (bRadarEvolve (L := L) 0 t (bRadarPrep L)).1 = aRelayFlow t (aRelayPrep L) := by
  show aRelayFlow (t - 0) (aRelayPrep L) = _
  rw [sub_zero]

end WithL

/-! ### The records -/

section Records

variable (hL : 10 ^ 19 ≤ L)
include hL

/-- ★★★ **`B`'s emission**: `B`'s register reaches `10¹²` within `[2·10¹², 2.15·10¹²]` — the
messenger leaving `B`. -/
noncomputable def bEmission {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (GateArena (RelayIdx L) × (Fin 4 → ℝ)) ℕ L :=
  regDetector aRelayFlow bRadarWeight (fun x => gatedFlow_zero aRelayLipschitz x)
    (fun s t x => gatedFlow_add aRelayLipschitz s t x) continuous_bRadarWeight
    (fun t => measurable_gatedFlow aRelayLipschitz t) 0 (10 ^ 12) (aRelayPrep L) Finset.univ
    (τ₀ := 2 * 10 ^ 12) (τ₁ := 215 * 10 ^ 10) (by norm_num) (by norm_num) hw
    (fun s _ => by rw [bRadarWeight_zero]; exact bEnc_nonneg _)
    (fun t ht0 ht => by
      rw [bRadarWeight_zero]
      exact (integral_bRate_le_half hL ht0).trans_lt (by linarith))
    (by
      rw [bRadarWeight_zero]
      obtain ⟨s₀, hs₀, h₀⟩ := exists_aRelayCross hL
      have hfreeOn := aRelayFlow_eq_free hL h₀.le
      have h := le_integral_of_ge_on (continuous_bRate (L := L))
        (κ := (1 - 23 / 1000) * (1 - 11 / 1000) - 1 / 2) (tn := 0) (te := 45 * 10 ^ 11)
        (t := 215 * 10 ^ 10) le_rfl (by norm_num) (by norm_num) (fun s _ => bRate_nonneg s)
        fun s hs1 hs2 => bRate_ge_depart hL hs₀ hfreeOn hs1 hs2
      exact le_trans (by norm_num) h)

/-- **`A`'s relay register, read.** -/
noncomputable def aRelayRead (y : GateArena (RelayIdx L) × (Fin 4 → ℝ)) : ℕ :=
  if relayLo ≤ y.1.2 then 1 else 0

omit hL [NeZero L] in
theorem measurable_aRelayRead : Measurable (aRelayRead (L := L)) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_snd.comp measurable_fst))
    measurable_const measurable_const

/-- ★★★ **`A`'s relay firing — the reception**: `A`'s relay register reaches `3·10¹¹` within
`[3·10¹³ − 8·10¹¹, 3·10¹³]`. -/
noncomputable def aReception {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (GateArena (RelayIdx L) × (Fin 4 → ℝ)) ℕ L where
  evolve := bRadarEvolve
  evolve_self := bRadarEvolve_self
  evolve_comp := bRadarEvolve_comp
  measurable_evolve := measurable_bRadarEvolve
  readout := aRelayRead
  measurable_readout := measurable_aRelayRead
  ready := {y | y.1.2 = 0}
  measurableSet_ready := measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  prep := bRadarPrep L
  prep_mem := rfl
  site := Finset.univ
  start := 0
  value := 1
  writeStart := aRelayTk - 8 * 10 ^ 11
  writeEnd := aRelayTk
  window := w
  isWrite :=
    have htk : aRelayTk = 3 * 10 ^ 13 := rfl
    { start_le := by rw [htk]; norm_num
      interval := by linarith
      window_nonneg := hw
      before := fun t ht0 ht => by
        show aRelayRead (bRadarEvolve 0 t (bRadarPrep L)) ≠ 1
        rw [aRelayRead, bRadarEvolve_prep_fst]
        have hr : aRelayReg L (aRelayTk - 8 * 10 ^ 11) ≤ relayLo :=
          (aRelayReg_start_le hL).trans (by unfold relayLo; norm_num)
        rw [aRelayFlow_eq_free hL hr t ⟨ht0, ht.le⟩]
        have hmono : aRelayReg L t ≤ aRelayReg L (aRelayTk - 8 * 10 ^ 11) := aRelayReg_mono ht.le
        have hlt : aRelayReg L t < relayLo := by
          have := aRelayReg_start_le hL
          have h25 : (25 * 10 ^ 10 : ℝ) < relayLo := by unfold relayLo; norm_num
          linarith
        show (if relayLo ≤ aRelayReg L t then (1 : ℕ) else 0) ≠ 1
        split_ifs with h
        · exact absurd h (not_le.2 hlt)
        · decide
      holds := fun t ht _ => by
        show aRelayRead (bRadarEvolve 0 t (bRadarPrep L)) = 1
        rw [aRelayRead, bRadarEvolve_prep_fst]
        obtain ⟨s₀, hs₀, h₀⟩ := exists_aRelayCross hL
        have hs₀0 : 0 ≤ s₀ := by rw [htk] at hs₀; linarith [hs₀.1]
        have hfree := aRelayFlow_eq_free hL h₀.le s₀ ⟨hs₀0, le_rfl⟩
        have h1 : relayLo ≤ (aRelayFlow t (aRelayPrep L)).2 := by
          calc relayLo = (aRelayFlow s₀ (aRelayPrep L)).2 := by rw [hfree, h₀]
            _ ≤ _ := aRelayFlow_register_mono (hs₀.2.trans ht)
        simp [h1] }

/-- ★★★ **`B`'s return**: the same register reaches `3·10¹²` within `[3.5·10¹³, 3.87·10¹³]` —
the echo back at `B`. -/
noncomputable def bReturn {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (GateArena (RelayIdx L) × (Fin 4 → ℝ)) ℕ L :=
  regDetector aRelayFlow bRadarWeight (fun x => gatedFlow_zero aRelayLipschitz x)
    (fun s t x => gatedFlow_add aRelayLipschitz s t x) continuous_bRadarWeight
    (fun t => measurable_gatedFlow aRelayLipschitz t) 0 (3 * 10 ^ 12) (aRelayPrep L) Finset.univ
    (τ₀ := 35 * 10 ^ 12) (τ₁ := 387 * 10 ^ 11) (by norm_num) (by norm_num) hw
    (fun s _ => by rw [bRadarWeight_zero]; exact bEnc_nonneg _)
    (fun t ht0 ht => by
      rw [bRadarWeight_zero]
      obtain ⟨s₀, hs₀, h₀⟩ := exists_aRelayCross hL
      have hfreeOn := aRelayFlow_eq_free hL h₀.le
      have hs₀0 : 0 ≤ s₀ := by
        have htk : aRelayTk = 3 * 10 ^ 13 := rfl
        rw [htk] at hs₀; linarith [hs₀.1]
      have hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo) := by
        rw [hfreeOn s₀ ⟨hs₀0, le_rfl⟩, h₀]
      have h1 : 3 * 10 ^ 13 - 8 * 10 ^ 11 ≤ s₀ := hs₀.1
      exact (integral_bRate_flight hL hs₀ hfree hfreeOn ht0 (by linarith)).trans_lt
        (by norm_num))
    (by
      rw [bRadarWeight_zero]
      obtain ⟨s₀, hs₀, h₀⟩ := exists_aRelayCross hL
      have hfreeOn := aRelayFlow_eq_free hL h₀.le
      have hs₀0 : 0 ≤ s₀ := by
        have htk : aRelayTk = 3 * 10 ^ 13 := rfl
        rw [htk] at hs₀; linarith [hs₀.1]
      have hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo) := by
        rw [hfreeOn s₀ ⟨hs₀0, le_rfl⟩, h₀]
      have hb := s₀_bounds hs₀
      exact integral_bRate_return hL hs₀ hfree hfreeOn (by nlinarith))

omit hL in
/-- **The encounter of `A` and `B` is the same in both relay arenas**: it reads only the two
devices, which run alike in both. -/
theorem meetRaw_aRelayFlow (t : ℝ) :
    meetRaw (aRelayFlow t (aRelayPrep L)).1 = meetRaw (relayFlow t (relayPrep L)).1 := by
  simp only [meetRaw, devA_aRelayFlow, devB_aRelayFlow, devA_relayFlow, devB_relayFlow]

omit hL in
theorem integral_bRadarWeight_three (t : ℝ) :
    ∫ s in (0 : ℝ)..t, bRadarWeight 3 (aRelayFlow s (aRelayPrep L))
      = ∫ s in (0 : ℝ)..t, radarWeight 3 (relayFlow s (relayPrep L)) := by
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [bRadarWeight_three, radarWeight_three, meetRaw_aRelayFlow]

/-- ★★★ **The meeting, recorded by `B`** in its radar arena: the clipped encounter register of `B`
with `A` reaches `6·10¹¹` within `[5·10¹³ − 1.65·10¹², 5·10¹³ + 5.7·10¹¹]` — `dirac_radar`'s
meeting window, since the register reads only the devices. -/
noncomputable def bMeeting {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (GateArena (RelayIdx L) × (Fin 4 → ℝ)) ℕ L :=
  regDetector aRelayFlow bRadarWeight (fun x => gatedFlow_zero aRelayLipschitz x)
    (fun s t x => gatedFlow_add aRelayLipschitz s t x) continuous_bRadarWeight
    (fun t => measurable_gatedFlow aRelayLipschitz t) 3 (6 * 10 ^ 11) (aRelayPrep L) Finset.univ
    (τ₀ := 5 * 10 ^ 13 - 165 * 10 ^ 10) (τ₁ := 5 * 10 ^ 13 + 57 * 10 ^ 10) (by norm_num)
    (by norm_num) hw (fun s _ => by rw [bRadarWeight_three]; exact meetRaw_nonneg _)
    (fun t ht0 ht => by rw [integral_bRadarWeight_three]; exact radar_meeting_before hL ht0 ht)
    (by rw [integral_bRadarWeight_three]; exact radar_meeting_after hL)

/-- **Tick `n` of `A`'s clock, in `B`'s radar arena** (pulled back along `A`'s device and its tick
register, which the arena carries). -/
noncomputable def bRestTick (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (GateArena (RelayIdx L) × (Fin 4 → ℝ)) ℕ L :=
  (twinRestTick hL n hn hw).pullback bRadarEvolve bRadarEvolve_self bRadarEvolve_comp
    measurable_bRadarEvolve (fun y => (devA y.1.1, y.2 1))
    ((continuous_devA.measurable.comp measurable_fst.fst).prodMk
      ((measurable_pi_apply 1).comp measurable_snd))
    (fun s t y => by
      refine Prod.ext ?_ ?_
      · show devA (aRelayFlow (t - s) y.1).1
          = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) (t - s) *ᵥ devA y.1.1
        exact devA_aRelayFlow_any y.1 (t - s)
      · show y.2 1 + ∫ u in (0 : ℝ)..(t - s), bRadarWeight 1 (aRelayFlow u y.1)
          = y.2 1 + 1 * ∫ u in (0 : ℝ)..(t - s), rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
              (tickMark (restObserver 0))
              (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) u *ᵥ devA y.1.1)
        rw [one_mul]
        congr 1
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [bRadarWeight_one, devA_aRelayFlow_any])
    (bRadarPrep L) (by
      show (devA (aRelayState 0), (0 : Fin 4 → ℝ) 1) = (restObserver 0, 0)
      rw [devA_aRelayState]
      rfl)

/-- **Tick `n` of `B`'s clock, in `B`'s radar arena.** -/
noncomputable def bApproachTick (n : ℕ) (hn : n ≤ 100) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (GateArena (RelayIdx L) × (Fin 4 → ℝ)) ℕ L :=
  (approachTick hL n hn hw).pullback bRadarEvolve bRadarEvolve_self bRadarEvolve_comp
    measurable_bRadarEvolve (fun y => (devB y.1.1, y.2 2))
    ((continuous_devB.measurable.comp measurable_fst.fst).prodMk
      ((measurable_pi_apply 2).comp measurable_snd))
    (fun s t y => by
      refine Prod.ext ?_ ?_
      · show devB (aRelayFlow (t - s) y.1).1
          = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) (t - s) *ᵥ devB y.1.1
        exact devB_aRelayFlow_any y.1 (t - s)
      · show y.2 2 + ∫ u in (0 : ℝ)..(t - s), bRadarWeight 2 (aRelayFlow u y.1)
          = y.2 2 + 1 * ∫ u in (0 : ℝ)..(t - s), rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
              (tickMark (approachObserver (-(5 * 10 ^ 13))))
              (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) u *ᵥ devB y.1.1)
        rw [one_mul]
        congr 1
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [bRadarWeight_two, devB_aRelayFlow_any])
    (bRadarPrep L) (by
      show (devB (aRelayState 0), (0 : Fin 4 → ℝ) 2) = (approachObserver (-(5 * 10 ^ 13)), 0)
      rw [devB_aRelayState, zero_sub]
      rfl)

/-! ### The fields -/

theorem bEmission_fields {w : ℝ} (hw : 0 ≤ w) :
    (bEmission (L := L) hL hw).evolve = bRadarEvolve
    ∧ (bEmission (L := L) hL hw).prep = bRadarPrep L
    ∧ (bEmission (L := L) hL hw).writeStart = 2 * 10 ^ 12
    ∧ (bEmission (L := L) hL hw).writeEnd = 215 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem aReception_fields {w : ℝ} (hw : 0 ≤ w) :
    (aReception (L := L) hL hw).evolve = bRadarEvolve
    ∧ (aReception (L := L) hL hw).prep = bRadarPrep L
    ∧ (aReception (L := L) hL hw).writeStart = 3 * 10 ^ 13 - 8 * 10 ^ 11
    ∧ (aReception (L := L) hL hw).writeEnd = 3 * 10 ^ 13 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem bReturn_fields {w : ℝ} (hw : 0 ≤ w) :
    (bReturn (L := L) hL hw).evolve = bRadarEvolve
    ∧ (bReturn (L := L) hL hw).prep = bRadarPrep L
    ∧ (bReturn (L := L) hL hw).writeStart = 35 * 10 ^ 12
    ∧ (bReturn (L := L) hL hw).writeEnd = 387 * 10 ^ 11 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem bMeeting_fields {w : ℝ} (hw : 0 ≤ w) :
    (bMeeting (L := L) hL hw).evolve = bRadarEvolve
    ∧ (bMeeting (L := L) hL hw).prep = bRadarPrep L
    ∧ (bMeeting (L := L) hL hw).writeStart = 5 * 10 ^ 13 - 165 * 10 ^ 10
    ∧ (bMeeting (L := L) hL hw).writeEnd = 5 * 10 ^ 13 + 57 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem bRestTick_fields (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    (bRestTick (L := L) hL n hn hw).evolve = bRadarEvolve
    ∧ (bRestTick (L := L) hL n hn hw).prep = bRadarPrep L
    ∧ (bRestTick (L := L) hL n hn hw).writeStart
      = max 0 (n * (2 * Real.pi * 10 ^ 11) - 10 ^ 11)
    ∧ (bRestTick (L := L) hL n hn hw).writeEnd = n * (2 * Real.pi * 10 ^ 11) + 10 ^ 11 := by
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

theorem bApproachTick_fields (n : ℕ) (hn : n ≤ 100) {w : ℝ} (hw : 0 ≤ w) :
    (bApproachTick (L := L) hL n hn hw).evolve = bRadarEvolve
    ∧ (bApproachTick (L := L) hL n hn hw).prep = bRadarPrep L
    ∧ (bApproachTick (L := L) hL n hn hw).writeStart
      = max 0 (2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
          * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) - 12 * 10 ^ 10)
    ∧ (bApproachTick (L := L) hL n hn hw).writeEnd
      = 2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
          * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) + 12 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The bundle -/

/-- ★★★ **`B`'s radar on the Dirac chain** (BACKLOG #278, second landing). On the relay arena at
`A` — `A` at rest with its clock and its relay (massless block), `B` approaching at `3/5` with its
clock, the massless messenger launched toward `A` at `c = 1` from `B`'s side — read through the
three registers the arena carries (`B`'s encounter with the messenger, `A`'s and `B`'s clocks):

* **one evolution**: `B`'s emission, `A`'s reception (the firing of its relay), `B`'s return, and
  the ticks of both clocks are actual occurrences of the same evolution from the same preparation;
* **the orbit**: `A` is `restObserver t`, `B` is `approachObserver (t − 5·10¹³)`, the weight is `3`;
  the relay fires at some `s₀ ∈ [3·10¹³ − 8·10¹¹, 3·10¹³]`, and from `s₀ + 3·10⁻³` on the
  messenger is within `‖·‖² ≤ 1.53·10⁻⁴` of the echo `−iσ_y ψ_free(2s₀ + 3·10⁻³ − t)`;
* **the records**: `B`'s emission within `[2·10¹², 2.15·10¹²]`, `A`'s reception within
  `[3·10¹³ − 8·10¹¹, 3·10¹³]`, `B`'s return within `[3.5·10¹³, 3.87·10¹³]`, in this order;
* **the clocks**: `A` ticks within `10¹¹` of `n · 2π·10¹¹`; `B` within `1.2·10¹¹` of `2πn/R`, its
  splitting `R ∈ [8·10⁻¹², 8.002·10⁻¹²]`;
* **between the ticks**: `B`'s emission between `B`'s ticks `2`–`3`, its return between `44`–`50`;
  `A`'s reception between `A`'s ticks `46`–`48`.

What this does **not** yet say: the radar coordinates `B` assigns to `A`'s relay event, and their
comparison with `A`'s chart (landings 3 and 4 of #278). -/
theorem dirac_b_radar {w : ℝ} (hw : 0 ≤ w) :
    let em := bEmission (L := L) hL hw
    let rc := aReception (L := L) hL hw
    let ret := bReturn (L := L) hL hw
    let meet := bMeeting (L := L) hL hw
    let a := fun (n : ℕ) (hn : n ≤ 130) => bRestTick (L := L) hL n hn hw
    let b := fun (n : ℕ) (hn : n ≤ 100) => bApproachTick (L := L) hL n hn hw
    let R := levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
    let T : ℝ := 2 * Real.pi * 10 ^ 11
    (rc.evolve = em.evolve ∧ rc.prep = em.prep ∧ ret.evolve = em.evolve ∧ ret.prep = em.prep
      ∧ meet.evolve = em.evolve ∧ meet.prep = em.prep
      ∧ (∀ n hn, (a n hn).evolve = em.evolve ∧ (a n hn).prep = em.prep)
      ∧ (∀ n hn, (b n hn).evolve = em.evolve ∧ (b n hn).prep = em.prep))
    ∧ (∀ t, devA (em.evolve 0 t em.prep).1.1 = restObserver t
      ∧ devB (em.evolve 0 t em.prep).1.1 = approachObserver (t - 5 * 10 ^ 13)
      ∧ sqNorm (em.evolve 0 t em.prep).1.1 = 3)
    ∧ (∃ s₀ ∈ Icc (3 * 10 ^ 13 - 8 * 10 ^ 11) (3 * 10 ^ 13),
        (em.evolve 0 s₀ em.prep).1.2 = relayLo
        ∧ ∀ t, s₀ + 3 / 1000 ≤ t →
          sqNorm (mess (em.evolve 0 t em.prep).1.1
              - (-I) • (spinY *ᵥ bMess (L := L) (2 * s₀ + 3 / 1000 - t)))
            ≤ (3 / 1000) ^ 2 * 17)
    ∧ (em.writeStart = 2 * 10 ^ 12 ∧ em.writeEnd = 215 * 10 ^ 10
      ∧ rc.writeStart = 3 * 10 ^ 13 - 8 * 10 ^ 11 ∧ rc.writeEnd = 3 * 10 ^ 13
      ∧ ret.writeStart = 35 * 10 ^ 12 ∧ ret.writeEnd = 387 * 10 ^ 11
      ∧ meet.writeStart = 5 * 10 ^ 13 - 165 * 10 ^ 10 ∧ meet.writeEnd = 5 * 10 ^ 13 + 57 * 10 ^ 10)
    ∧ (∀ n hn, (a n hn).writeStart = max 0 ((n : ℝ) * T - 10 ^ 11)
      ∧ (a n hn).writeEnd = (n : ℝ) * T + 10 ^ 11)
    ∧ (8 / 10 ^ 12 ≤ R ∧ R ≤ 8002 / 10 ^ 15
      ∧ ∀ n hn, (b n hn).writeStart = max 0 (2 * Real.pi * (n : ℝ) / R - 12 * 10 ^ 10)
        ∧ (b n hn).writeEnd = 2 * Real.pi * (n : ℝ) / R + 12 * 10 ^ 10)
    ∧ (em.writeEnd < rc.writeStart ∧ rc.writeEnd < ret.writeStart
      ∧ ret.writeEnd < meet.writeStart)
    ∧ ((b 2 (by norm_num)).writeEnd ≤ em.writeStart ∧ em.writeEnd ≤ (b 3 (by norm_num)).writeStart
      ∧ (b 44 (by norm_num)).writeEnd ≤ ret.writeStart
      ∧ ret.writeEnd ≤ (b 50 (by norm_num)).writeStart
      ∧ (b 61 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (b 65 (by norm_num)).writeStart)
    ∧ ((a 46 (by norm_num)).writeEnd ≤ rc.writeStart
      ∧ rc.writeEnd ≤ (a 48 (by norm_num)).writeStart
      ∧ (a 76 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (a 81 (by norm_num)).writeStart) := by
  intro em rc ret meet a b R T
  have hπ := Real.pi_pos
  have hπ1 := pi_gt_314
  have hπ2 := pi_lt_31416
  obtain ⟨hR1, hR2⟩ := approach_rate (L := L) hL
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  obtain ⟨e1e, e1p, e1s, e1t⟩ := bEmission_fields (L := L) hL hw
  obtain ⟨r1e, r1p, r1s, r1t⟩ := aReception_fields (L := L) hL hw
  obtain ⟨t1e, t1p, t1s, t1t⟩ := bReturn_fields (L := L) hL hw
  obtain ⟨m1e, m1p, m1s, m1t⟩ := bMeeting_fields (L := L) hL hw
  have hA := fun n hn => bRestTick_fields (L := L) hL n hn hw
  have hB := fun n hn => bApproachTick_fields (L := L) hL n hn hw
  have hdivlo : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
        ≤ 2 * Real.pi * k / (8 / 10 ^ 12) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) (by norm_num) hR1
  have hdivhi : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / (8002 / 10 ^ 15)
      ≤ 2 * Real.pi * k / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
          * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) hR0 hR2
  refine ⟨⟨r1e.trans e1e.symm, r1p.trans e1p.symm, t1e.trans e1e.symm, t1p.trans e1p.symm,
      m1e.trans e1e.symm, m1p.trans e1p.symm,
      fun n hn => ⟨(hA n hn).1.trans e1e.symm, (hA n hn).2.1.trans e1p.symm⟩,
      fun n hn => ⟨(hB n hn).1.trans e1e.symm, (hB n hn).2.1.trans e1p.symm⟩⟩,
    fun t => ?_, ?_, ⟨e1s, e1t, r1s, r1t, t1s, t1t, m1s, m1t⟩,
    fun n hn => ⟨(hA n hn).2.2.1, (hA n hn).2.2.2⟩,
    ⟨hR1, hR2, fun n hn => ⟨(hB n hn).2.2.1, (hB n hn).2.2.2⟩⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [e1e, e1p, bRadarEvolve_prep_fst]
    exact ⟨devA_aRelayFlow t, devB_aRelayFlow t, sqNorm_aRelayFlow hL t⟩
  · obtain ⟨-, -, -, -, -, s₀, hs₀, -, hreg, -, hret⟩ := dirac_relay_at_rest (L := L) hL
    refine ⟨s₀, hs₀, ?_, fun t ht => ?_⟩
    · rw [e1e, e1p, bRadarEvolve_prep_fst]
      exact hreg
    · rw [e1e, e1p, bRadarEvolve_prep_fst, ← echo_eq]
      exact hret t ht
  · rw [e1t, r1s]
    norm_num
  · rw [r1t, t1s]
    norm_num
  · rw [t1t, m1s]
    norm_num
  · rw [(hB 2 (by norm_num)).2.2.2, e1s]
    have h := hdivlo ((2 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 2 / (8 / 10 ^ 12) = Real.pi * (4 * 10 ^ 12 / 8) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 3 (by norm_num)).2.2.1, e1t]
    refine le_max_of_le_right ?_
    have h := hdivhi ((3 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 3 / (8002 / 10 ^ 15) = Real.pi * (6 * 10 ^ 15 / 8002) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 44 (by norm_num)).2.2.2, t1s]
    have h := hdivlo ((44 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 44 / (8 / 10 ^ 12) = Real.pi * (88 * 10 ^ 12 / 8) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 50 (by norm_num)).2.2.1, t1t]
    refine le_max_of_le_right ?_
    have h := hdivhi ((50 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 50 / (8002 / 10 ^ 15) = Real.pi * (100 * 10 ^ 15 / 8002) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 61 (by norm_num)).2.2.2, m1s]
    have h := hdivlo ((61 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 61 / (8 / 10 ^ 12) = Real.pi * (122 * 10 ^ 12 / 8) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 65 (by norm_num)).2.2.1, m1t]
    refine le_max_of_le_right ?_
    have h := hdivhi ((65 : ℕ) : ℝ) (by norm_num)
    push_cast at h
    rw [show 2 * Real.pi * 65 / (8002 / 10 ^ 15) = Real.pi * (130 * 10 ^ 15 / 8002) by ring] at h
    push_cast
    nlinarith
  · rw [(hA 46 (by norm_num)).2.2.2, r1s]
    push_cast
    nlinarith
  · rw [(hA 48 (by norm_num)).2.2.1, r1t]
    refine le_max_of_le_right ?_
    push_cast
    nlinarith
  · rw [(hA 76 (by norm_num)).2.2.2, m1s]
    push_cast
    nlinarith
  · rw [(hA 81 (by norm_num)).2.2.1, m1t]
    refine le_max_of_le_right ?_
    push_cast
    nlinarith

end Records


end CSD.RecordLayer

end
