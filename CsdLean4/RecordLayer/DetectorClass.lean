/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.EchoRadar

/-!
# Detector-class stability: which measurements are properties of geometry

**Category:** 7-SigmaLayer (the record layer). BACKLOG #204 (out of #39; the author's third
operational-geometry brief, §4: *determine which measurements are properties of geometry*).

A detector perturbs the carrier (its back-reaction detunes the exchange) and contributes its own
delay (its write completes after the arrival). Two detectors measuring the same arrangement — the
same exchange `J, ħ` between the same two sites — therefore read different raw timestamps. This file
says exactly what is the detector's and what is the arrangement's. The **correction** subtracts from
each raw timestamp the detector's derived response: the emission write's completion from the emission
reading, the return write's response from the return reading. After the correction the inferred
separation is within a residual of the arrangement's hop time, and two detectors' corrected separations
agree up to the sum of their residuals. The residual is #196's loss (the two transfer errors, quadratic
in each detector's detuning), the clock resolution and the retention window — nothing of the detector's
response survives in it.

* `emitCorrection`, `returnCorrection` — **the derived responses** a detector subtracts;
  `correctedSep` — the corrected radar separation from two raw timestamps; `correctedBudget` —
  `T + senderWindow + 2 transferError`: clock resolution, retention window (input), the two transfers;
* ★★ `abs_correctedEmit_le`, `abs_correctedRet_sub_roundTrip_le`, ★★ `abs_correctedSep_sub_hopTime_le`
  — **the corrected separation is within the corrected budget of the hop time**: the detector's
  responses are gone from the residual;
* `rawSep_eq_correctedSep_add` — **what the correction removes**: the raw separation is the corrected
  one plus half the detector's net delay, so raw separations of two detectors differ by a
  detector-dependent amount even on one arrangement;
* ★★★ `detector_class_stability` — **two detectors on one arrangement agree in corrected separation
  up to the sum of their corrected budgets**;
* `transferError_mono`, ★★ `stable_regime` — **the regime**: for the class of detectors with detuning
  at most `δ`, retention window at most `w`, on clocks of resolution at most `T₀`, any two corrected
  separations are within `2T₀ + 2w + 4 transferError J ħ δ` of each other, and each is within
  `T₀ + w + 2 transferError J ħ δ` of the hop time. The hop time is the property of the arrangement;
  the class is stated.

## Honest scope

* The correction uses each detector's *derived* response, which is known from the detector's own
  preparation (`r_A`, `λ`, `ω`). It is not a fit.
* The residual is not zero: the loss `λ < 1` of a detuned detector shifts the arrival itself, by
  `transferError`, and no correction removes it without knowing the detuning. The regime statement
  makes this quantitative in `δ`.
* The clock is #185's scheduled device, as in #200; with #201's hand clock in its place the
  resolution term is `τ_tick + 1/(2ω_c)` (#202) and nothing else changes.

References: `specs/BACKLOG.md` #204, #200, #196, #197, #199, #39; `RecordLayer/EchoRadar.lean`
(`echoReadings`, `echoReturnDelay`, `abs_detunedRoundTrip_sub_roundTrip_le`),
`RecordLayer/RadarDetector.lean` (`transferError`), `RecordLayer/EchoArena.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The corrections and the corrected budget -/

section Corrections

variable {J ħ : ℝ} (A B : PointerCoupling) {qA qB : LF4.KTorus} {K : ℕ}

/-- **The emission correction**: the emission write's completion, derived from the preparation. -/
noncomputable def emitCorrection (J ħ : ℝ) (qA qB : LF4.KTorus) : ℝ :=
  emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)

/-- **The return correction**: the return write's response, derived from the preparation. -/
noncomputable def returnCorrection (J ħ : ℝ) (qA qB : LF4.KTorus) : ℝ :=
  echoReturnDelay A B J ħ qA qB

/-- The corrected radar separation from two raw timestamps and the two corrections. -/
noncomputable def correctedSep (eE eR raw₁ raw₂ : ℝ) : ℝ := ((raw₂ - eR) - (raw₁ - eE)) / 2

/-- **The corrected budget**: clock resolution, retention window, the two transfers — and nothing of
the detector's response. -/
noncomputable def correctedBudget (J ħ : ℝ) (qA qB : LF4.KTorus) (T : ℝ) : ℝ :=
  T + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    + 2 * transferError J ħ (echoDetuning A B qA qB)

theorem correctedBudget_nonneg (hJ : 0 < J) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) {T : ℝ}
    (hT : 0 ≤ T) : 0 ≤ correctedBudget A B J ħ qA qB T := by
  unfold correctedBudget
  have h1 := senderWindow_nonneg hr (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB)
    hslow
  have h2 := transferError_nonneg hJ hħ (echoDetuning A B qA qB)
  linarith

/-- ★★ **The corrected emission timestamp is within `T + senderWindow` of `0`**: the emission
write's completion is gone. -/
theorem abs_correctedEmit_le (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂) (ht₁K : t₁ ≤ K * T)
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hE : 0 ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |(echoReadings hK hT hc h₁₂).emit - emitCorrection A B J ħ qA qB|
      ≤ T + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) := by
  rw [echoReadings_emit, emitCorrection]
  have h1 := abs_tickReading_sub_lt hK hT hc (by linarith [hemit.1]) ht₁K
  have h2 : |t₁ - emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)|
      ≤ senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) := by
    rw [abs_le]
    constructor <;> linarith [hemit.1, hemit.2]
  calc |tickReading T (clockEvolve T 0 t₁ c)
        - emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)|
      ≤ |tickReading T (clockEvolve T 0 t₁ c) - t₁|
        + |t₁ - emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith [h1.le, h2]

/-- ★★ **The corrected return timestamp is within the corrected budget of `2τ_hop`**: the return
write's response is gone, and what remains is the clock, the window and the two transfers. -/
theorem abs_correctedRet_sub_roundTrip_le (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) {T : ℝ}
    (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂)
    (ht₂K : t₂ ≤ K * T)
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hR : 0 ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |(echoReadings hK hT hc h₁₂).ret - returnCorrection A B J ħ qA qB - roundTrip J ħ|
      ≤ correctedBudget A B J ħ qA qB T := by
  rw [echoReadings_ret, returnCorrection, correctedBudget]
  set r := senderRate A ħ qA
  set l := echoLoss A B J qA qB
  set ω := echoRate A B J ħ qA qB
  set Δ := echoDetuning A B qA qB
  have h1 := abs_tickReading_sub_lt hK hT hc (by linarith [hret.1]) ht₂K
  have h2 : |t₂ - returnEnd r l ω| ≤ senderWindow r l ω := by
    rw [abs_le]
    constructor <;> linarith [hret.1, hret.2]
  have h3 : returnEnd r l ω - echoReturnDelay A B J ħ qA qB = detunedRoundTrip J ħ Δ := by
    unfold echoReturnDelay
    ring
  have h4 := abs_detunedRoundTrip_sub_roundTrip_le hJ hħ Δ
  have e : tickReading T (clockEvolve T 0 t₂ c) - echoReturnDelay A B J ħ qA qB - roundTrip J ħ
      = (tickReading T (clockEvolve T 0 t₂ c) - t₂) + (t₂ - returnEnd r l ω)
        + (detunedRoundTrip J ħ Δ - roundTrip J ħ) := by
    rw [← h3]
    ring
  rw [e]
  calc |(tickReading T (clockEvolve T 0 t₂ c) - t₂) + (t₂ - returnEnd r l ω)
        + (detunedRoundTrip J ħ Δ - roundTrip J ħ)|
      ≤ |(tickReading T (clockEvolve T 0 t₂ c) - t₂) + (t₂ - returnEnd r l ω)|
        + |detunedRoundTrip J ħ Δ - roundTrip J ħ| := abs_add_le _ _
    _ ≤ (|tickReading T (clockEvolve T 0 t₂ c) - t₂| + |t₂ - returnEnd r l ω|)
        + |detunedRoundTrip J ħ Δ - roundTrip J ħ| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith [h1.le, h2, h4]

end Corrections

/-! ### The corrected separation -/

/-- The corrected separation is within `max` of the two endpoint residuals of the hop time: the
arithmetic of `correctedSep` against `roundTrip = 2 hopTime`. -/
theorem abs_correctedSep_sub_hopTime_le_of {J ħ : ℝ} {eE eR raw₁ raw₂ B₁ B₂ : ℝ}
    (h₁ : |raw₁ - eE| ≤ B₁) (h₂ : |raw₂ - eR - roundTrip J ħ| ≤ B₂) (h₁₂ : B₁ ≤ B₂) :
    |correctedSep eE eR raw₁ raw₂ - hopTime J ħ| ≤ B₂ := by
  have e : correctedSep eE eR raw₁ raw₂ - hopTime J ħ
      = ((raw₂ - eR - roundTrip J ħ) - (raw₁ - eE)) / 2 := by
    unfold correctedSep roundTrip
    ring
  rw [e, abs_div, abs_two, div_le_iff₀ (by norm_num)]
  calc |(raw₂ - eR - roundTrip J ħ) - (raw₁ - eE)|
      ≤ |raw₂ - eR - roundTrip J ħ| + |raw₁ - eE| := abs_sub _ _
    _ ≤ B₂ * 2 := by linarith

/-- **What the correction removes**: the raw separation is the corrected one plus half the
detector's net delay `eR − eE`. Two detectors on one arrangement differ in raw separation by a
detector-dependent amount; the correction is what makes them comparable. -/
theorem rawSep_eq_correctedSep_add (eE eR raw₁ raw₂ : ℝ) :
    (raw₂ - raw₁) / 2 = correctedSep eE eR raw₁ raw₂ + (eR - eE) / 2 := by
  unfold correctedSep
  ring

section Stability

variable {J ħ : ℝ} (A B : PointerCoupling) {qA qB : LF4.KTorus} {K : ℕ}

/-- ★★ **The corrected separation is within the corrected budget of the hop time.** The detector's
responses do not appear in the residual. -/
theorem abs_correctedSep_sub_hopTime_le (hJ : 0 < J) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ}
    (h₁₂ : t₁ ≤ t₂) (ht₁K : t₁ ≤ K * T) (ht₂K : t₂ ≤ K * T)
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |correctedSep (emitCorrection A B J ħ qA qB) (returnCorrection A B J ħ qA qB)
        (echoReadings hK hT hc h₁₂).emit (echoReadings hK hT hc h₁₂).ret - hopTime J ħ|
      ≤ correctedBudget A B J ħ qA qB T := by
  have hl0 := (echoLoss_pos A B hJ qA qB).le
  have hl1 := echoLoss_le_one A B hJ qA qB
  have hω := echoRate_pos A B hJ hħ qA qB
  have hE := emitEnd_nonneg hr hl0 hl1 hω
  have hR := returnEnd_nonneg hr hl0 hl1 hω
  have h1 := abs_correctedEmit_le A B hK hT hc h₁₂ ht₁K hemit hE
  have h2 := abs_correctedRet_sub_roundTrip_le A B hJ hħ hK hT hc h₁₂ ht₂K hret hR
  refine abs_correctedSep_sub_hopTime_le_of h1 h2 ?_
  unfold correctedBudget
  linarith [transferError_nonneg hJ hħ (echoDetuning A B qA qB)]

end Stability

/-! ### Two detectors on one arrangement -/

/-- ★★★ **Detector-class stability.** Two detectors — two pointer couplings and two preparations,
on two clocks — measuring the same arrangement `J, ħ` agree in corrected separation up to the sum of
their corrected budgets. Nothing of either detector's response survives: the residual is the two
clocks, the two retention windows and the four transfers. -/
theorem detector_class_stability {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ)
    -- detector 1
    (A B : PointerCoupling) {qA qB : LF4.KTorus} (hr : 0 < senderRate A ħ qA) {K : ℕ} (hK : 0 < K)
    {T : ℝ} (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂)
    (ht₁K : t₁ ≤ K * T) (ht₂K : t₂ ≤ K * T)
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    -- detector 2
    (A' B' : PointerCoupling) {qA' qB' : LF4.KTorus} (hr' : 0 < senderRate A' ħ qA') {K' : ℕ}
    (hK' : 0 < K') {T' : ℝ} (hT' : 0 < T') {c' : ClockArena K'} (hc' : c' ∈ ClockReady K')
    {t₁' t₂' : ℝ} (h₁₂' : t₁' ≤ t₂') (ht₁K' : t₁' ≤ K' * T') (ht₂K' : t₂' ≤ K' * T')
    (hemit' : emitEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        ≤ t₁'
      ∧ t₁' ≤ emitEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        + senderWindow (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB'))
    (hret' : returnEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        ≤ t₂'
      ∧ t₂' ≤ returnEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        + senderWindow (senderRate A' ħ qA') (echoLoss A' B' J qA' qB')
          (echoRate A' B' J ħ qA' qB')) :
    |correctedSep (emitCorrection A B J ħ qA qB) (returnCorrection A B J ħ qA qB)
        (echoReadings hK hT hc h₁₂).emit (echoReadings hK hT hc h₁₂).ret
      - correctedSep (emitCorrection A' B' J ħ qA' qB') (returnCorrection A' B' J ħ qA' qB')
        (echoReadings hK' hT' hc' h₁₂').emit (echoReadings hK' hT' hc' h₁₂').ret|
      ≤ correctedBudget A B J ħ qA qB T + correctedBudget A' B' J ħ qA' qB' T' := by
  have h1 := abs_correctedSep_sub_hopTime_le A B hJ hħ hr hK hT hc h₁₂ ht₁K ht₂K hemit hret
  have h2 := abs_correctedSep_sub_hopTime_le A' B' hJ hħ hr' hK' hT' hc' h₁₂' ht₁K' ht₂K' hemit'
    hret'
  calc |correctedSep (emitCorrection A B J ħ qA qB) (returnCorrection A B J ħ qA qB)
        (echoReadings hK hT hc h₁₂).emit (echoReadings hK hT hc h₁₂).ret
      - correctedSep (emitCorrection A' B' J ħ qA' qB') (returnCorrection A' B' J ħ qA' qB')
        (echoReadings hK' hT' hc' h₁₂').emit (echoReadings hK' hT' hc' h₁₂').ret|
      ≤ |correctedSep (emitCorrection A B J ħ qA qB) (returnCorrection A B J ħ qA qB)
          (echoReadings hK hT hc h₁₂).emit (echoReadings hK hT hc h₁₂).ret - hopTime J ħ|
        + |correctedSep (emitCorrection A' B' J ħ qA' qB') (returnCorrection A' B' J ħ qA' qB')
          (echoReadings hK' hT' hc' h₁₂').emit (echoReadings hK' hT' hc' h₁₂').ret - hopTime J ħ| :=
        abs_sub_le_abs_sub_add_abs_sub _ _ _
    _ ≤ _ := add_le_add h1 h2

/-! ### The regime -/

/-- The transfer error is monotone in the size of the detuning. -/
theorem transferError_mono {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {Δ δ : ℝ} (h : |Δ| ≤ δ) :
    transferError J ħ Δ ≤ transferError J ħ δ := by
  unfold transferError
  have hδ : 0 ≤ δ := (abs_nonneg Δ).trans h
  have h2 : Δ ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs Δ]
    exact pow_le_pow_left₀ (abs_nonneg Δ) h 2
  have hpi := Real.pi_pos
  exact div_le_div_of_nonneg_right (by nlinarith [mul_pos hpi hħ]) (by positivity)

/-- The corrected budget of a detector of the class `|Δ| ≤ δ`, window `≤ w`, clock `≤ T₀`. -/
theorem correctedBudget_le_of_class {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (A B : PointerCoupling)
    {qA qB : LF4.KTorus} {T T₀ w δ : ℝ} (hT : T ≤ T₀)
    (hw : senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ w)
    (hδ : |echoDetuning A B qA qB| ≤ δ) :
    correctedBudget A B J ħ qA qB T ≤ T₀ + w + 2 * transferError J ħ δ := by
  unfold correctedBudget
  have := transferError_mono hJ hħ hδ
  linarith

/-- ★★ **The regime in which the inferred separation is a property of the arrangement.** For the
class of detectors whose detuning is at most `δ` and whose retention window is at most `w`, read on
clocks of resolution at most `T₀`: every corrected separation is within `T₀ + w + 2 transferError J ħ δ`
of the hop time, and any two are within twice that of each other. The hop time belongs to the
arrangement; the detector enters only through the class parameters. -/
theorem stable_regime {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {T₀ w δ : ℝ}
    (A B : PointerCoupling) {qA qB : LF4.KTorus} (hr : 0 < senderRate A ħ qA) {K : ℕ} (hK : 0 < K)
    {T : ℝ} (hT : 0 < T) (hT₀ : T ≤ T₀) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ}
    (h₁₂ : t₁ ≤ t₂) (ht₁K : t₁ ≤ K * T) (ht₂K : t₂ ≤ K * T)
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hw : senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ w)
    (hδ : |echoDetuning A B qA qB| ≤ δ)
    (A' B' : PointerCoupling) {qA' qB' : LF4.KTorus} (hr' : 0 < senderRate A' ħ qA') {K' : ℕ}
    (hK' : 0 < K') {T' : ℝ} (hT' : 0 < T') (hT₀' : T' ≤ T₀) {c' : ClockArena K'}
    (hc' : c' ∈ ClockReady K') {t₁' t₂' : ℝ} (h₁₂' : t₁' ≤ t₂') (ht₁K' : t₁' ≤ K' * T')
    (ht₂K' : t₂' ≤ K' * T')
    (hemit' : emitEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        ≤ t₁'
      ∧ t₁' ≤ emitEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        + senderWindow (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB'))
    (hret' : returnEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        ≤ t₂'
      ∧ t₂' ≤ returnEnd (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
        + senderWindow (senderRate A' ħ qA') (echoLoss A' B' J qA' qB')
          (echoRate A' B' J ħ qA' qB'))
    (hw' : senderWindow (senderRate A' ħ qA') (echoLoss A' B' J qA' qB') (echoRate A' B' J ħ qA' qB')
      ≤ w)
    (hδ' : |echoDetuning A' B' qA' qB'| ≤ δ) :
    |correctedSep (emitCorrection A B J ħ qA qB) (returnCorrection A B J ħ qA qB)
        (echoReadings hK hT hc h₁₂).emit (echoReadings hK hT hc h₁₂).ret - hopTime J ħ|
      ≤ T₀ + w + 2 * transferError J ħ δ
    ∧ |correctedSep (emitCorrection A B J ħ qA qB) (returnCorrection A B J ħ qA qB)
        (echoReadings hK hT hc h₁₂).emit (echoReadings hK hT hc h₁₂).ret
      - correctedSep (emitCorrection A' B' J ħ qA' qB') (returnCorrection A' B' J ħ qA' qB')
        (echoReadings hK' hT' hc' h₁₂').emit (echoReadings hK' hT' hc' h₁₂').ret|
      ≤ 2 * (T₀ + w + 2 * transferError J ħ δ) := by
  have h1 := abs_correctedSep_sub_hopTime_le A B hJ hħ hr hK hT hc h₁₂ ht₁K ht₂K hemit hret
  have hb1 := correctedBudget_le_of_class hJ hħ A B hT₀ hw hδ
  have hb2 := correctedBudget_le_of_class hJ hħ A' B' hT₀' hw' hδ'
  have h12 := detector_class_stability hJ hħ A B hr hK hT hc h₁₂ ht₁K ht₂K hemit hret A' B' hr' hK'
    hT' hc' h₁₂' ht₁K' ht₂K' hemit' hret'
  exact ⟨h1.trans hb1, h12.trans (by linarith)⟩

end CSD.RecordLayer

end
