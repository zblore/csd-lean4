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

end WithL

end CSD.RecordLayer

end
