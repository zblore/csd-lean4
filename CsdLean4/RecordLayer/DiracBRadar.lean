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

* ★ `approach_tail_fine` (`B` off its chord-`1/100` arc: `≤ 2.3·10⁻²`).

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

end WithL

end CSD.RecordLayer

end
