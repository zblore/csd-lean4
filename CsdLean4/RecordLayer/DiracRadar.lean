/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracRelay

/-!
# The radar: emission, relay, return and meeting as records of one evolution

**Category:** 7-SigmaLayer (the record layer). BACKLOG #274, fourth landing (the records and the
two-way factor; closes the row).

The relay arena of `DiracRelay` — `A` at rest, `B` approaching at `3/5`, the messenger launched
from `A` at `4/5` and flipped by `B`'s relay — with four registers integrated along the one gated
flow: the **clipped weight of the messenger at `A`** (the emission, and later the return), the
**tick rates of both clocks**, and the **clipped encounter weight of `B` with `A`** (the meeting).
The reception is the relay register itself crossing its threshold. All of them are actual
occurrences (`ActualOccurrence`) of **one evolution** from **one preparation**, and the two-way
(radar) factor is read off the ticks.

## Integrals over windows (generic)

* `integral_le_integral_of_nonneg`, `integral_le_two_bumps` (an integrand at most `M` on two open
  windows and at most `0` off them), `le_integral_two_windows` (at least `κ₁`, `κ₂` on two open
  windows).

## The propagator on every start (generic)

* ★ `hasDerivAt_expProp_mulVec` — **`t ↦ e^{−itH} v` solves `Ψ' = −iHΨ` for every `v`**;
  `hasDerivAt_deviceProp_mulVec`, `hasDerivAt_deviceProp_level`; ★★ `devA_relayFlow_any`,
  `devB_relayFlow_any` — **the devices of the relay arena run by `e^{−itH_dev}` from every start**,
  not only from the preparation (what a pullback of their tick records needs).

## The radar arena

* `RadarArena` (the relay arena with four registers), `atA` (the clipped weight of the messenger at
  `A`), `meetRaw` (the clipped encounter weight of `B` with `A`), `radarWeight`, `radarEvolve`,
  `radarPrep`; `regionWeight_le_sqNorm`, `atA_le_half`, `meetRaw_le_half`.

## The messenger at `A`, out and back

* `atA_free_far`, `atA_free_near` (the free phase); `regionWeight_echo`, `sqNorm_echo`,
  `abs_regionWeight_sub_le`, ★ `abs_regionWeight_mess_sub_echo_le` — **after the pulse the
  messenger's weight on any region is within `0.031` of its echo's**; `atA_after_far`,
  `atA_after_near`.

## The meeting

* ★ `meeting_near`, ★ `meeting_far` — the encounter weight of the approaching observer with the
  observer at rest, near (`≥ 0.99` within `6.6·10¹¹` of `5·10¹³`) and far (`≤ 0.008` beyond
  `2.84·10¹²`).

## The records

* ★★★ `radarEmission` — the clipped register at `A` reaches `5·10¹¹` within
  `[4·10¹² − 5.3·10¹¹, 4·10¹² + 3·10¹⁰]`;
* ★★★ `radarReception` — **the relay register reaches `3·10¹¹`** within `t_k ± 4.28·10¹¹`,
  `t_k = 1.66·10¹⁴/7` (the reception is the firing of the relay);
* ★★★ `radarReturn` — the same clipped register at `A` reaches `1.7·10¹²` within
  `[2t_k − 4·10¹² − 2.37·10¹², 2t_k − 4·10¹² + 1.86·10¹²]`: **the echo is back at `A`**;
* ★★★ `radarMeeting` — the clipped encounter register of `B` with `A` reaches `6·10¹¹` within
  `[5·10¹³ − 1.65·10¹², 5·10¹³ + 5.7·10¹¹]`;
* `restTickRadar`, `approachTickRadar` — the ticks of both clocks, pulled back to the arena.

## The bundle

* ★★★ `dirac_radar` — one evolution; the records ordered; emission between `A`'s ticks `5`–`7`,
  reception between `B`'s `29`–`31`, return between `A`'s `65`–`73`, meeting between `A`'s
  `76`–`81` and `B`'s `61`–`65`; **the round trip within `2.5·10¹²` of `2ℓ_AB(t_k)/v`**; **the
  two-way factor off `A`'s clock** — the time from the return to the meeting over the time from
  the emission to the meeting lies in `[3/76, 16/69]`, which contains `(v − β)/(v + β) = 1/7` and
  excludes `0` (a return at `B`'s speed would arrive with `B`); with `B`'s clock the factor splits
  as `k₁ k₂ = (16/35)(5/16)`, `k₁ ∈ [30/76, 36/69]` containing the relativistic `16/35` and
  excluding the Galilean `4/7`.

## Findings

* **The reception is the relay's firing**: no separate reception register is needed — the register
  that drives the gate is the record, and its write interval is the sure window of the crossing.
* **Clipping removes the tails from the records too**: the clipped weight at `A` is exactly zero
  while the messenger is away (out, at `B`, and on the way back), so one register with two
  thresholds carries both the emission and the return, as in #270 — and the pulse error only
  enters through the near window (`0.031` against a weight near `1`).
* **The two-way factor is kinematic**: `(t_m − t_ret)/(t_m − e) = (v − β)/(v + β)` holds in
  Galilean and Lorentzian kinematics alike; the Lorentz content is in the one-way factor `k₁`
  (#256), which the same records recover.

## Honest scope

⚠️ **Bounds, not equalities**: every write interval is a sure window; the factors are intervals of
tick ratios containing the predicted values. The `k₂` interval `[3/36, 16/30]` contains both the
relativistic `5/16` and the Galilean `1/4`: the return is not located sharply enough to separate
them; `k₁` is.

⚠️ **The ticks are pulled back**, not re-derived: the devices evolve freely in the arena
(`devA_relayFlow_any`), so the tick records of `DiracTwin`/`DiracDoppler` are records of this
evolution by `ActualOccurrence.pullback`.

References: `specs/BACKLOG.md` #274, #256, #270, #253, #39; `RecordLayer/DiracRelay.lean`
(`relayFlow`, `dirac_relay`, `sqNorm_mess_return_le`); `RecordLayer/DiracDoppler.lean`
(`emission_near`, `emission_far`, `approachTick`, `offset_mem_of_near_at`);
`RecordLayer/DiracTwin.lean` (`twinRestTick`, `rest_tail`); `RecordLayer/DiracObservers.lean`
(`regFlow`, `regDetector`, `le_relWeight`, `relWeight_le`); `RecordLayer/MovingRadarPair.lean`
(`ActualOccurrence.pullback`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV CSD.SigmaLayer
open scoped Matrix NNReal

namespace CSD.RecordLayer

/-! ### Integrals over windows -/

section Integrals

/-- A nonnegative integrand integrates to no less over a longer interval. -/
theorem integral_le_integral_of_nonneg {F : ℝ → ℝ} (hF : Continuous F) {t t' : ℝ} (ht : 0 ≤ t)
    (htt' : t ≤ t') (hpos : ∀ s, 0 ≤ s → 0 ≤ F s) :
    ∫ s in (0 : ℝ)..t, F s ≤ ∫ s in (0 : ℝ)..t', F s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable 0 t)
    (hF.intervalIntegrable t t')]
  have := intervalIntegral.integral_nonneg (μ := volume) htt' fun s hs => hpos s (ht.trans hs.1)
  linarith

/-- An integrand at most `M` on the open windows `(a, b)` and `(c, d)` and at most `0` off them
integrates over `[0, t]` to at most `M` times the windows' length. -/
theorem integral_le_two_bumps {F : ℝ → ℝ} (hF : Continuous F) {M a b c d t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdt : d ≤ t)
    (h0 : ∀ s, 0 < s → s < a → F s ≤ 0) (h1 : ∀ s, a < s → s < b → F s ≤ M)
    (h2 : ∀ s, b < s → s < c → F s ≤ 0) (h3 : ∀ s, c < s → s < d → F s ≤ M)
    (h4 : ∀ s, d < s → s < t → F s ≤ 0) :
    ∫ s in (0 : ℝ)..t, F s ≤ M * (b - a) + M * (d - c) := by
  have hi : ∀ x y : ℝ, IntervalIntegrable F volume x y := fun x y => hF.intervalIntegrable x y
  have bump : ∀ x y K : ℝ, x ≤ y → (∀ s, x < s → s < y → F s ≤ K) →
      ∫ s in x..y, F s ≤ K * (y - x) := fun x y K hxy h => by
    have := intervalIntegral.integral_mono_on_of_le_Ioo hxy (hi x y)
      (intervalIntegrable_const (μ := volume) (c := K)) fun s hs => h s hs.1 hs.2
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi b c) (hi c t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi c d) (hi d t)]
  have e0 := bump 0 a 0 ha h0
  have e1 := bump a b M hab h1
  have e2 := bump b c 0 hbc h2
  have e3 := bump c d M hcd h3
  have e4 := bump d t 0 hdt h4
  linarith

/-- A nonnegative integrand at least `κ₁` on the open window `(a, b)` and at least `κ₂` on `(c, d)`
integrates over `[0, t]` to at least `κ₁ (b − a) + κ₂ (d − c)`. -/
theorem le_integral_two_windows {F : ℝ → ℝ} (hF : Continuous F) {κ₁ κ₂ a b c d t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdt : d ≤ t)
    (hpos : ∀ s, 0 ≤ s → 0 ≤ F s) (h1 : ∀ s, a < s → s < b → κ₁ ≤ F s)
    (h2 : ∀ s, c < s → s < d → κ₂ ≤ F s) :
    κ₁ * (b - a) + κ₂ * (d - c) ≤ ∫ s in (0 : ℝ)..t, F s := by
  have hi : ∀ x y : ℝ, IntervalIntegrable F volume x y := fun x y => hF.intervalIntegrable x y
  have window : ∀ x y K : ℝ, x ≤ y → (∀ s, x < s → s < y → K ≤ F s) →
      K * (y - x) ≤ ∫ s in x..y, F s := fun x y K hxy h => by
    have := intervalIntegral.integral_mono_on_of_le_Ioo hxy
      (intervalIntegrable_const (μ := volume) (c := K)) (hi x y) fun s hs => h s hs.1 hs.2
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
  have nn : ∀ x y : ℝ, 0 ≤ x → x ≤ y → 0 ≤ ∫ s in x..y, F s := fun x y hx hxy =>
    intervalIntegral.integral_nonneg (μ := volume) hxy fun s hs => hpos s (hx.trans hs.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi b c) (hi c t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi c d) (hi d t)]
  have e0 := nn 0 a le_rfl ha
  have e1 := window a b κ₁ hab h1
  have e2 := nn b c (ha.trans hab) hbc
  have e3 := window c d κ₂ hcd h2
  have e4 := nn d t ((ha.trans hab).trans (hbc.trans hcd)) hdt
  linarith

end Integrals

/-! ### The propagator on every start -/

section Propagator

open scoped Matrix.Norms.L2Operator in
/-- ★ **`t ↦ e^{−itH} v` solves `Ψ' = −iHΨ`** for every vector `v`. -/
theorem hasDerivAt_expProp_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (v : ι → ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((-(I * t)) • H) *ᵥ v)
      ((-I) • (H *ᵥ (NormedSpace.exp ((-(I * t)) • H) *ᵥ v))) t := by
  have hM := hasDerivAt_exp_smul_const' (𝕂 := ℂ) ((-I) • H) (t : ℂ)
  let Lv : Matrix ι ι ℂ →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }
  have hg := (LinearMap.toContinuousLinearMap Lv).hasFDerivAt.comp_hasDerivAt (t : ℂ) hM
  have h := hg.scomp t Complex.ofRealCLM.hasDerivAt
  have e1 : ∀ s : ℝ, ((s : ℂ)) • ((-I) • H) = (-(I * s)) • H := fun s => by
    rw [smul_smul]
    congr 1
    ring
  have hfun : ∀ s : ℝ, ((LinearMap.toContinuousLinearMap Lv)
      ∘ (fun u : ℂ => NormedSpace.exp (u • ((-I) • H)))) (s : ℂ)
      = NormedSpace.exp ((-(I * s)) • H) *ᵥ v := fun s => by
    simp only [Function.comp, LinearMap.coe_toContinuousLinearMap', e1]
    rfl
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => (hfun s).symm)).congr_deriv ?_
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    LinearMap.coe_toContinuousLinearMap', e1]
  show ((-I) • H * NormedSpace.exp ((-(I * t)) • H)) *ᵥ v = _
  rw [Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

variable {L : ℕ} [NeZero L]

/-- The device's propagator applied to any state solves the device's equation. -/
theorem hasDerivAt_deviceProp_mulVec (J μ₀ μ₁ : ℝ) (v : (ZMod L × Fin 2) × Fin 2 → ℂ) (t : ℝ) :
    HasDerivAt (fun t => deviceProp (L := L) J μ₀ μ₁ t *ᵥ v)
      ((-I) • (deviceHam J μ₀ μ₁ *ᵥ (deviceProp J μ₀ μ₁ t *ᵥ v))) t :=
  hasDerivAt_expProp_mulVec (deviceHam J μ₀ μ₁) v t

/-- Level `i` of the propagated state solves the chain equation at the level's mass. -/
theorem hasDerivAt_deviceProp_level (J μ₀ μ₁ : ℝ) (v : (ZMod L × Fin 2) × Fin 2 → ℂ) (i : Fin 2)
    (t : ℝ) :
    HasDerivAt (fun t => fun q => (deviceProp (L := L) J μ₀ μ₁ t *ᵥ v) (q, i))
      ((-I) • (diracHam J (levelMass μ₀ μ₁ i) *ᵥ fun q => (deviceProp J μ₀ μ₁ t *ᵥ v) (q, i)))
      t := by
  rw [hasDerivAt_pi]
  intro q
  refine (hasDerivAt_pi.1 (hasDerivAt_deviceProp_mulVec J μ₀ μ₁ v t) (q, i)).congr_deriv ?_
  simp only [Pi.smul_apply, smul_eq_mul, deviceHam_mulVec_apply]

/-- ★★ **`A`'s device runs by `e^{−itH_dev}` from every start of the relay arena.** -/
theorem devA_relayFlow_any (x : GateArena (RelayIdx L)) (t : ℝ) :
    devA (relayFlow t x).1 = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devA x.1 := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (relayFlow t x).1 0 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devA x.1) (q, 0)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devA x.1) 0
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 0 = relayMass 0 by simp [levelMass, relayMass_zero]] at h
    refine congrFun (gatedFlow_block_eq relayLipschitz x (k := 0) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl
  · show blockOf (relayFlow t x).1 1 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devA x.1) (q, 1)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devA x.1) 1
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 1 = relayMass 1 by simp [levelMass, relayMass_one]] at h
    refine congrFun (gatedFlow_block_eq relayLipschitz x (k := 1) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl

/-- ★★ **`B`'s device runs by `e^{−itH_dev}` from every start of the relay arena.** -/
theorem devB_relayFlow_any (x : GateArena (RelayIdx L)) (t : ℝ) :
    devB (relayFlow t x).1 = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devB x.1 := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (relayFlow t x).1 2 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devB x.1) (q, 0)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devB x.1) 0
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 0 = relayMass 2 by simp [levelMass, relayMass_two]] at h
    refine congrFun (gatedFlow_block_eq relayLipschitz x (k := 2) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl
  · show blockOf (relayFlow t x).1 3 q
      = (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ devB x.1) (q, 1)
    have h := hasDerivAt_deviceProp_level (relayHop L) 3 (3 + 1 / 10 ^ 11) (devB x.1) 1
    rw [show levelMass 3 (3 + 1 / 10 ^ 11) 1 = relayMass 3 by
      simp [levelMass, relayMass_three]] at h
    refine congrFun (gatedFlow_block_eq relayLipschitz x (k := 3) (by decide) h ?_ t) q
    funext q
    simp only [deviceProp_zero, Matrix.one_mulVec]
    rfl

end Propagator

/-! ### The radar arena -/

section Arena

variable {L : ℕ} [NeZero L]

/-- **The radar arena**: the relay arena with four registers — the clipped weight of the messenger
at `A`, the tick rates of `A`'s and `B`'s clocks, the clipped encounter weight of `B` with `A`. -/
abbrev RadarArena (L : ℕ) : Type := GateArena (RelayIdx L) × (Fin 4 → ℝ)

/-- **The clipped weight of the messenger at `A`**: `max (w_A − 1/2) 0`, `w_A` its weight on the
chord-`1/10` arc at `A`. -/
noncomputable def atA (Ψ : RelayIdx L → ℂ) : ℝ :=
  max (regionWeight (mess Ψ) (chordArc 1 (1 / 10)) - 1 / 2) 0

/-- **The clipped encounter weight of `B` with `A`**: `max (relWeight − 1/2) 0`. -/
noncomputable def meetRaw (Ψ : RelayIdx L → ℂ) : ℝ :=
  max (relWeight 1 (1 / 10) (devB Ψ) (devA Ψ) - 1 / 2) 0

/-- **The four registers' rates**, as functions of the relay arena's state. -/
noncomputable def radarWeight : Fin 4 → GateArena (RelayIdx L) → ℝ :=
  ![fun x => atA x.1,
    fun x => rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) (tickMark (restObserver (L := L) 0))
      (devA x.1),
    fun x => rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
      (tickMark (approachObserver (L := L) (-(5 * 10 ^ 13)))) (devB x.1),
    fun x => meetRaw x.1]

theorem radarWeight_zero : radarWeight (L := L) 0 = fun x => atA x.1 := by simp [radarWeight]

theorem radarWeight_one : radarWeight (L := L) 1 = fun x =>
    rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) (tickMark (restObserver (L := L) 0))
      (devA x.1) := by
  simp [radarWeight]

theorem radarWeight_two : radarWeight (L := L) 2 = fun x =>
    rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
      (tickMark (approachObserver (L := L) (-(5 * 10 ^ 13)))) (devB x.1) := by
  simp [radarWeight]

theorem radarWeight_three : radarWeight (L := L) 3 = fun x => meetRaw x.1 := by simp [radarWeight]

omit [NeZero L] in
theorem continuous_devA : Continuous (devA (L := L)) := continuous_pi fun _ => continuous_apply _

theorem continuous_atA : Continuous (atA (L := L)) :=
  (((continuous_regionWeight _).comp continuous_mess).sub continuous_const).max continuous_const

theorem continuous_meetRaw : Continuous (meetRaw (L := L)) :=
  ((continuous_relWeight_comp continuous_devB continuous_devA 1 (1 / 10)).sub
    continuous_const).max continuous_const

theorem continuous_radarWeight (i : Fin 4) :
    Continuous fun p : GateArena (RelayIdx L) × ℝ => radarWeight i (relayFlow p.2 p.1) := by
  have hflow : Continuous fun p : GateArena (RelayIdx L) × ℝ => (relayFlow p.2 p.1).1 :=
    continuous_fst.comp
      ((continuous_gatedFlow relayLipschitz).comp (continuous_snd.prodMk continuous_fst))
  fin_cases i
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => radarWeight 0 (relayFlow p.2 p.1)
    rw [radarWeight_zero]
    exact continuous_atA.comp hflow
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => radarWeight 1 (relayFlow p.2 p.1)
    rw [radarWeight_one]
    exact (continuous_rateWeight _ _ _ _).comp (continuous_devA.comp hflow)
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => radarWeight 2 (relayFlow p.2 p.1)
    rw [radarWeight_two]
    exact (continuous_rateWeight _ _ _ _).comp (continuous_devB.comp hflow)
  · show Continuous fun p : GateArena (RelayIdx L) × ℝ => radarWeight 3 (relayFlow p.2 p.1)
    rw [radarWeight_three]
    exact continuous_meetRaw.comp hflow

/-- **The evolution of the radar arena**: the relay flow with its four registers. -/
noncomputable def radarEvolve : OnticTime → OnticTime → RadarArena L → RadarArena L :=
  regEvolve relayFlow radarWeight

theorem radarEvolve_self (t : OnticTime) : radarEvolve (L := L) t t = id :=
  regEvolve_self relayFlow radarWeight (fun x => gatedFlow_zero relayLipschitz x) t

theorem radarEvolve_comp (s t u : OnticTime) :
    radarEvolve t u ∘ radarEvolve s t = radarEvolve (L := L) s u :=
  regEvolve_comp relayFlow radarWeight (fun s t x => gatedFlow_add relayLipschitz s t x)
    continuous_radarWeight s t u

theorem measurable_radarEvolve (s t : OnticTime) : Measurable (radarEvolve (L := L) s t) :=
  measurable_regFlow relayFlow radarWeight (fun t => measurable_gatedFlow relayLipschitz t)
    continuous_radarWeight (t - s)

/-- **The preparation**: the relay arena's, every register at `0`. -/
noncomputable def radarPrep (L : ℕ) [NeZero L] : RadarArena L := (relayPrep L, 0)

theorem radarEvolve_prep_fst (t : ℝ) :
    (radarEvolve (L := L) 0 t (radarPrep L)).1 = relayFlow t (relayPrep L) := by
  show relayFlow (t - 0) (relayPrep L) = _
  rw [sub_zero]

theorem radarEvolve_prep_snd (t : ℝ) (i : Fin 4) :
    (radarEvolve (L := L) 0 t (radarPrep L)).2 i
      = ∫ s in (0 : ℝ)..t, radarWeight i (relayFlow s (relayPrep L)) := by
  show (0 : Fin 4 → ℝ) i + ∫ s in (0 : ℝ)..(t - 0), radarWeight i (relayFlow s (relayPrep L)) = _
  rw [sub_zero, Pi.zero_apply, zero_add]

/-! #### Small facts about the weights -/

theorem sqNorm_eq_sum_siteWeight (ψ : ZMod L × Fin 2 → ℂ) : sqNorm ψ = ∑ k, siteWeight ψ k := by
  rw [sqNorm, Fintype.sum_prod_type]
  rfl

theorem regionWeight_le_sqNorm (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight ψ A ≤ sqNorm ψ := by
  rw [sqNorm_eq_sum_siteWeight, regionWeight]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun k _ _ => siteWeight_nonneg _ _

theorem atA_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ atA Ψ := le_max_right _ _

theorem atA_le_half {Ψ : RelayIdx L → ℂ} (h : sqNorm (mess Ψ) ≤ 1) : atA Ψ ≤ 1 / 2 :=
  max_le (by linarith [regionWeight_le_sqNorm (mess Ψ) (chordArc 1 (1 / 10))]) (by norm_num)

theorem meetRaw_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ meetRaw Ψ := le_max_right _ _

theorem meetRaw_le_half {Ψ : RelayIdx L → ℂ} (hB : devRegionWeight (devB Ψ) Finset.univ = 1)
    (hA : devRegionWeight (devA Ψ) Finset.univ = 1) : meetRaw Ψ ≤ 1 / 2 := by
  have h := relWeight_le_mul 1 (1 / 10) (devB Ψ) (devA Ψ)
  rw [hB, hA, one_mul] at h
  exact max_le (by linarith) (by norm_num)

omit [NeZero L] in
theorem siteWeight_neg_I_smul (v : ZMod L × Fin 2 → ℂ) (k : ZMod L) :
    siteWeight ((-I) • v) k = siteWeight v k := by
  simp only [siteWeight, Pi.smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- The echo `−iσ_y v` has the weight of `v` on every region. -/
theorem regionWeight_echo (v : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight ((-I) • (spinY *ᵥ v)) A = regionWeight v A := by
  simp only [regionWeight, siteWeight_neg_I_smul, siteWeight_spinY]

theorem sqNorm_echo (v : ZMod L × Fin 2 → ℂ) : sqNorm ((-I) • (spinY *ᵥ v)) = sqNorm v := by
  rw [sqNorm_eq_sum_siteWeight, sqNorm_eq_sum_siteWeight]
  simp only [siteWeight_neg_I_smul, siteWeight_spinY]

/-- The weight on a region moves by at most the total site-density change. -/
theorem abs_regionWeight_sub_le (ψ χ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    |regionWeight ψ A - regionWeight χ A| ≤ ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| := by
  simp only [regionWeight, siteWeight, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ A, |∑ c : Fin 2, (‖ψ (k, c)‖ ^ 2 - ‖χ (k, c)‖ ^ 2)|
      ≤ ∑ k ∈ A, ∑ c : Fin 2, |‖ψ (k, c)‖ ^ 2 - ‖χ (k, c)‖ ^ 2| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ c : Fin 2, |‖ψ (k, c)‖ ^ 2 - ‖χ (k, c)‖ ^ 2| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _
    _ = ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| :=
        (Fintype.sum_prod_type fun p : ZMod L × Fin 2 => |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2|).symm

/-! ### The relay register's readout, and the orbit's rates -/

/-- **The relay register's readout**: `1` once it has reached `relayLo`. -/
noncomputable def relayRead (y : RadarArena L) : ℕ := if relayLo ≤ y.1.2 then 1 else 0

omit [NeZero L] in
theorem measurable_relayRead : Measurable (relayRead (L := L)) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_snd.comp measurable_fst))
    measurable_const measurable_const

theorem continuous_radarOrbit (i : Fin 4) :
    Continuous fun s => radarWeight i (relayFlow s (relayPrep L)) :=
  (continuous_radarWeight i).comp (continuous_const.prodMk continuous_id)

theorem pi_lt_31416 : Real.pi < 31416 / 10000 := by
  have := Real.pi_lt_d4
  norm_num at this ⊢
  linarith

/-! ### The messenger at `A`, out and back -/

section WithL

variable (hL : 10 ^ 19 ≤ L)
include hL

omit hL in
/-- The messenger's angle `8·10⁻¹⁴ s` is at least `0.121` from `0` once `|s| ≥ 1.5125·10¹²`. -/
theorem angle_far_of_le {x : ℝ} (h : 15125 * 10 ^ 8 ≤ |x|) : 121 / 1000 ≤ |8 / 10 ^ 14 * x| := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 10 ^ 14)]
  calc (121 / 1000 : ℝ) = 8 / 10 ^ 14 * (15125 * 10 ^ 8) := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

omit hL in
/-- The messenger's angle stays below `2π − 0.121` while `|s| ≤ 2.5·10¹³`. -/
theorem angle_le_of_le {x : ℝ} (h : |x| ≤ 25 * 10 ^ 12) :
    |8 / 10 ^ 14 * x| ≤ 2 * Real.pi - 121 / 1000 := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 10 ^ 14)]
  have hπ := pi_gt_314
  calc 8 / 10 ^ 14 * |x| ≤ 8 / 10 ^ 14 * (25 * 10 ^ 12) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 := by norm_num
    _ ≤ 2 * Real.pi - 121 / 1000 := by linarith

/-- Before the crossing, the clipped weight at `A` is that of the free messenger. -/
theorem atA_free {s₀ s : ℝ} (hr : relayReg L s₀ ≤ relayLo) (hs : s ∈ Icc (0 : ℝ) s₀) :
    atA (relayFlow s (relayPrep L)).1
      = max (regionWeight (imagePacket (L := L) (s - 4 * 10 ^ 12)) (chordArc 1 (1 / 10)) - 1 / 2)
          0 := by
  rw [atA, relayFlow_eq_free hL hr s hs]
  simp only [mess_relayState]

/-- **The free messenger away from `A`**: at least `1.5125·10¹²` from its passage (and within
`2.5·10¹³` of it), its clipped weight at `A` is `0`. -/
theorem atA_free_far {s₀ s : ℝ} (hr : relayReg L s₀ ≤ relayLo) (hs : s ∈ Icc (0 : ℝ) s₀)
    (hfar : 15125 * 10 ^ 8 ≤ |s - 4 * 10 ^ 12|) (h25 : |s - 4 * 10 ^ 12| ≤ 25 * 10 ^ 12) :
    atA (relayFlow s (relayPrep L)).1 = 0 := by
  rw [atA_free hL hr hs]
  have h := emission_far hL (e := 4 * 10 ^ 12) (t := s) (h25.trans (by norm_num))
    (angle_far_of_le hfar) (angle_le_of_le h25)
  exact max_eq_right (by linarith)

/-- **The free messenger at `A`**: within `10¹²` of its passage, its clipped weight at `A` is at
least `0.494`. -/
theorem atA_free_near {s₀ s : ℝ} (hr : relayReg L s₀ ≤ relayLo) (hs : s ∈ Icc (0 : ℝ) s₀)
    (hnear : |s - 4 * 10 ^ 12| ≤ 10 ^ 12) :
    494 / 1000 ≤ atA (relayFlow s (relayPrep L)).1 := by
  rw [atA_free hL hr hs]
  have h := emission_near hL (e := 4 * 10 ^ 12) (t := s) hnear
  exact le_max_of_le_left (by linarith)

theorem atA_orbit_le_half (s : ℝ) : atA (relayFlow s (relayPrep L)).1 ≤ 1 / 2 :=
  atA_le_half (sqNorm_mess_relayFlow hL s).le

/-- ★ **After the pulse, the messenger's weight on any region is within `0.031` of its echo's**
`ψ_free(2s₀ + 3·10⁻³ − e − t)`. -/
theorem abs_regionWeight_mess_sub_echo_le {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) {t : ℝ}
    (ht : s₀ + 3 / 1000 ≤ t) (A : Finset (ZMod L)) :
    |regionWeight (mess (relayFlow t (relayPrep L)).1) A
        - regionWeight (imagePacket (L := L) (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)) A|
      ≤ 31 / 1000 := by
  set ψ := mess (relayFlow t (relayPrep L)).1 with hψdef
  set χ := (-I) • (spinY *ᵥ imagePacket (L := L) (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)) with hχdef
  have h1 := abs_regionWeight_sub_le ψ χ A
  have h2 := sum_abs_norm_sq_sub_le ψ χ
  have hψ : sqNorm ψ = 1 := sqNorm_mess_relayFlow hL t
  have hχ : sqNorm χ = 1 := by rw [hχdef, sqNorm_echo, sqNorm_imagePacket hL]
  have hd := sqNorm_mess_return_le hL hs₀ hfree ht
  rw [hχdef, regionWeight_echo] at h1
  have h3 : Real.sqrt (2 * sqNorm ψ + 2 * sqNorm χ) = 2 := by
    rw [hψ, hχ, show (2 : ℝ) * 1 + 2 * 1 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h4 : Real.sqrt (sqNorm (ψ - χ)) ≤ 153 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    exact hd.trans (by norm_num)
  calc |regionWeight ψ A - regionWeight (imagePacket (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)) A|
      ≤ ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| := h1
    _ ≤ Real.sqrt (2 * sqNorm ψ + 2 * sqNorm χ) * Real.sqrt (sqNorm (ψ - χ)) := h2
    _ = 2 * Real.sqrt (sqNorm (ψ - χ)) := by rw [h3]
    _ ≤ 2 * (153 / 10000) := by linarith
    _ ≤ 31 / 1000 := by norm_num

/-- **The echo away from `A`**: its clipped weight at `A` is `0`. -/
theorem atA_after_far {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) {t : ℝ}
    (ht : s₀ + 3 / 1000 ≤ t) (hfar : 15125 * 10 ^ 8 ≤ |2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t|)
    (h25 : |2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t| ≤ 25 * 10 ^ 12) :
    atA (relayFlow t (relayPrep L)).1 = 0 := by
  have hw := abs_regionWeight_mess_sub_echo_le hL hs₀ hfree ht (chordArc 1 (1 / 10))
  have h := emission_far hL (e := 0) (t := 2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)
    (by rw [sub_zero]; exact h25.trans (by norm_num))
    (by rw [sub_zero]; exact angle_far_of_le hfar) (by rw [sub_zero]; exact angle_le_of_le h25)
  rw [sub_zero] at h
  rw [abs_le] at hw
  exact max_eq_right (by linarith [hw.2])

/-- **The echo at `A`**: within `10¹²` of its return, its clipped weight at `A` is at least
`0.463`. -/
theorem atA_after_near {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) {t : ℝ}
    (ht : s₀ + 3 / 1000 ≤ t) (hnear : |2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t| ≤ 10 ^ 12) :
    463 / 1000 ≤ atA (relayFlow t (relayPrep L)).1 := by
  have hw := abs_regionWeight_mess_sub_echo_le hL hs₀ hfree ht (chordArc 1 (1 / 10))
  have h := emission_near hL (e := 0) (t := 2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)
    (by rw [sub_zero]; exact hnear)
  rw [sub_zero] at h
  rw [abs_le] at hw
  exact le_max_of_le_left (by linarith [hw.1])

/-! ### The meeting -/

/-- ★ **The approaching observer at the observer at rest**: within `6.6·10¹¹` of `5·10¹³`, their
encounter weight is at least `0.99`. -/
theorem meeting_near {t : ℝ} (ht0 : 0 ≤ t) (ht : |t - 5 * 10 ^ 13| ≤ 66 * 10 ^ 10) :
    99 / 100 ≤ relWeight 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (restObserver t) := by
  have ht' := abs_le.1 ht
  have tB := approach_tail hL (s := t - 5 * 10 ^ 13)
    (by rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2])
  have tA := rest_tail hL ht0 (by linarith [ht'.2])
  have hX := devRegionWeight_add_compl (approachObserver (L := L) (t - 5 * 10 ^ 13))
    (chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50))
  rw [approach_total hL] at hX
  have hY := devRegionWeight_add_compl (restObserver (L := L) t) (chordArc 1 (1 / 25))
  rw [rest_total hL] at hY
  have hoff : ‖(1 : ℂ) * star (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) - 1‖
      ≤ 4 / 100 := by
    rw [one_mul, star_exp_I_mul]
    have := norm_exp_sub_exp_le (-(6 / 10 ^ 14 * (t - 5 * 10 ^ 13))) 0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 6 / 10 ^ 14)] at this
    refine this.trans ?_
    calc 6 / 10 ^ 14 * |t - 5 * 10 ^ 13| ≤ 6 / 10 ^ 14 * (66 * 10 ^ 10) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ 4 / 100 := by norm_num
  have hle := le_relWeight (w := 1) (ρ := 1 / 10)
    (ΨA := approachObserver (L := L) (t - 5 * 10 ^ 13)) (ΨB := restObserver t)
    (X := chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50))
    (Y := chordArc 1 (1 / 25)) fun j hj k hk =>
      offset_mem_of_near_at norm_one (mem_chordArc.1 hj) (mem_chordArc.1 hk) (by linarith)
  have hA : 1 - 6 / 1000 ≤ devRegionWeight (approachObserver (L := L) (t - 5 * 10 ^ 13))
      (chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50)) := by
    linarith
  have hB : 1 - 14 / 10 ^ 4 ≤ devRegionWeight (restObserver (L := L) t) (chordArc 1 (1 / 25)) := by
    linarith
  calc (99 / 100 : ℝ) ≤ (1 - 6 / 1000) * (1 - 14 / 10 ^ 4) := by norm_num
    _ ≤ _ := mul_le_mul hA hB (by norm_num) (devRegionWeight_nonneg _ _)
    _ ≤ _ := hle

/-- ★ **The approaching observer away from the observer at rest**: while their relative angle
`6·10⁻¹⁴ (t − 5·10¹³)` is at least `0.17` from every multiple of `2π`, the encounter weight is at
most `8·10⁻³`. -/
theorem meeting_far {t : ℝ} (ht0 : 0 ≤ t) (ht8 : t ≤ 8 * 10 ^ 13)
    (h1 : 17 / 100 ≤ |6 / 10 ^ 14 * (t - 5 * 10 ^ 13)|)
    (h2 : |6 / 10 ^ 14 * (t - 5 * 10 ^ 13)| ≤ 2 * Real.pi - 17 / 100) :
    relWeight 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13)) (restObserver t)
      ≤ 8 / 1000 := by
  have tB := approach_tail hL (s := t - 5 * 10 ^ 13) (by rw [abs_le]; constructor <;> linarith)
  have tA := rest_tail hL ht0 ht8
  have hsin := Real.sin_gt_sub_cube (x := 17 / 100 / 2) (by norm_num)
  have hfar := two_sin_le_norm_exp_sub_one (y := 17 / 100)
    (z := -(6 / 10 ^ 14 * (t - 5 * 10 ^ 13))) (by norm_num) (by rwa [abs_neg]) (by rwa [abs_neg])
  have : (16 / 100 : ℝ) < 2 * (17 / 100 / 2 - (17 / 100 / 2) ^ 3 / 6) := by norm_num
  have hoff : 16 / 100
      < ‖(1 : ℂ) * star (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) - 1‖ := by
    rw [one_mul, star_exp_I_mul]
    linarith
  have hle := relWeight_le (w := 1) (ρ := 1 / 10)
    (ΨA := approachObserver (L := L) (t - 5 * 10 ^ 13)) (ΨB := restObserver t)
    (X := chordArc (exp (I * ((6 / 10 ^ 14 * (t - 5 * 10 ^ 13) : ℝ) : ℂ))) (1 / 50))
    (Y := chordArc 1 (1 / 25)) fun j hj k hk =>
      offset_not_mem_of_far_at norm_one (mem_chordArc.1 hj) (mem_chordArc.1 hk) (by linarith)
  rw [approach_total hL, rest_total hL, mul_one, one_mul] at hle
  linarith

omit hL in
theorem meetRaw_orbit (t : ℝ) :
    meetRaw (relayFlow t (relayPrep L)).1
      = max (relWeight 1 (1 / 10) (approachObserver (L := L) (t - 5 * 10 ^ 13)) (restObserver t)
          - 1 / 2) 0 := by
  rw [meetRaw, devB_relayFlow, devA_relayFlow]

theorem meetRaw_orbit_le_half (t : ℝ) : meetRaw (relayFlow t (relayPrep L)).1 ≤ 1 / 2 := by
  refine meetRaw_le_half ?_ ?_
  · rw [devB_relayFlow, approach_total hL]
  · rw [devA_relayFlow, rest_total hL]

/-- Near the meeting the clipped encounter rate is at least `0.49`. -/
theorem meetRaw_orbit_near {t : ℝ} (ht0 : 0 ≤ t) (ht : |t - 5 * 10 ^ 13| ≤ 66 * 10 ^ 10) :
    49 / 100 ≤ meetRaw (relayFlow t (relayPrep L)).1 := by
  rw [meetRaw_orbit]
  exact le_max_of_le_left (by linarith [meeting_near hL ht0 ht])

/-- Before `5·10¹³ − 2.84·10¹²` the clipped encounter rate is `0`. -/
theorem meetRaw_orbit_far {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 5 * 10 ^ 13 - 284 * 10 ^ 10) :
    meetRaw (relayFlow t (relayPrep L)).1 = 0 := by
  rw [meetRaw_orbit]
  have hπ := pi_gt_314
  have hx1 : 6 / 10 ^ 14 * (t - 5 * 10 ^ 13) ≤ 6 / 10 ^ 14 * (-(284 * 10 ^ 10)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have hx2 : 6 / 10 ^ 14 * (-(5 * 10 ^ 13)) ≤ 6 / 10 ^ 14 * (t - 5 * 10 ^ 13) :=
    mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  rw [show (6 / 10 ^ 14 : ℝ) * (-(284 * 10 ^ 10)) = -(1704 / 10000) by norm_num] at hx1
  rw [show (6 / 10 ^ 14 : ℝ) * (-(5 * 10 ^ 13)) = -3 by norm_num] at hx2
  have hneg : 6 / 10 ^ 14 * (t - 5 * 10 ^ 13) < 0 := by linarith
  have h := meeting_far hL ht0 (by linarith) (by rw [abs_of_neg hneg]; linarith)
    (by rw [abs_of_neg hneg]; linarith)
  exact max_eq_right (by linarith)

/-! ### The records -/

omit hL in
theorem radarWeight_zero_nonneg (s : ℝ) : 0 ≤ radarWeight 0 (relayFlow s (relayPrep L)) := by
  rw [radarWeight_zero]
  exact atA_nonneg _

omit hL in
theorem radarWeight_three_nonneg (s : ℝ) : 0 ≤ radarWeight 3 (relayFlow s (relayPrep L)) := by
  rw [radarWeight_three]
  exact meetRaw_nonneg _

/-- Before `4·10¹² − 5.3·10¹¹` the clipped register at `A` is below `5·10¹¹`. -/
theorem radar_emission_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 4 * 10 ^ 12 - 53 * 10 ^ 10) :
    ∫ s in (0 : ℝ)..t, radarWeight 0 (relayFlow s (relayPrep L)) < 5 * 10 ^ 11 := by
  have hF := continuous_radarOrbit (L := L) 0
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  have hr : relayReg L (relayTk - 428 * 10 ^ 9) ≤ relayLo :=
    (relayReg_start_le hL).trans (by unfold relayLo; norm_num)
  refine lt_of_le_of_lt (integral_le_integral_of_nonneg hF ht0 ht.le
    fun s _ => radarWeight_zero_nonneg s) ?_
  have h := integral_le_two_bumps hF (M := 1 / 2) (a := 4 * 10 ^ 12 - 15125 * 10 ^ 8)
    (b := 4 * 10 ^ 12 - 53 * 10 ^ 10) (c := 4 * 10 ^ 12 - 53 * 10 ^ 10)
    (d := 4 * 10 ^ 12 - 53 * 10 ^ 10) (t := 4 * 10 ^ 12 - 53 * 10 ^ 10) (by norm_num) (by norm_num)
    le_rfl le_rfl le_rfl
    (fun s hs0 hs => by
      rw [radarWeight_zero]
      exact (atA_free_far hL hr ⟨hs0.le, by linarith⟩ (le_abs.2 (Or.inr (by linarith)))
        (abs_le.2 ⟨by linarith, by linarith⟩)).le)
    (fun s _ _ => by rw [radarWeight_zero]; exact atA_orbit_le_half hL s)
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
  exact h.trans_lt (by norm_num)

/-- By `4·10¹² + 3·10¹⁰` the clipped register at `A` has reached `5·10¹¹`. -/
theorem radar_emission_after :
    5 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..(4 * 10 ^ 12 + 3 * 10 ^ 10),
      radarWeight 0 (relayFlow s (relayPrep L)) := by
  have hF := continuous_radarOrbit (L := L) 0
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  have hr : relayReg L (relayTk - 428 * 10 ^ 9) ≤ relayLo :=
    (relayReg_start_le hL).trans (by unfold relayLo; norm_num)
  have h := le_integral_two_windows hF (κ₁ := 494 / 1000) (κ₂ := 0) (a := 4 * 10 ^ 12 - 10 ^ 12)
    (b := 4 * 10 ^ 12 + 3 * 10 ^ 10) (c := 4 * 10 ^ 12 + 3 * 10 ^ 10)
    (d := 4 * 10 ^ 12 + 3 * 10 ^ 10) (t := 4 * 10 ^ 12 + 3 * 10 ^ 10) (by norm_num) (by norm_num)
    le_rfl le_rfl le_rfl (fun s _ => radarWeight_zero_nonneg s)
    (fun s h1 h2 => by
      rw [radarWeight_zero]
      exact atA_free_near hL hr ⟨by linarith, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩))
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
  exact le_trans (by norm_num) h

/-- ★★★ **The emission, recorded at `A`**: the clipped register of the messenger's weight at `A`
reaches `5·10¹¹` within `[4·10¹² − 5.3·10¹¹, 4·10¹² + 3·10¹⁰]`. -/
noncomputable def radarEmission {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (RadarArena L) ℕ L :=
  regDetector relayFlow radarWeight (fun x => gatedFlow_zero relayLipschitz x)
    (fun s t x => gatedFlow_add relayLipschitz s t x) continuous_radarWeight
    (fun t => measurable_gatedFlow relayLipschitz t) 0 (5 * 10 ^ 11) (relayPrep L) Finset.univ
    (τ₀ := 4 * 10 ^ 12 - 53 * 10 ^ 10) (τ₁ := 4 * 10 ^ 12 + 3 * 10 ^ 10) (by norm_num) (by norm_num)
    hw (fun s _ => radarWeight_zero_nonneg s) (fun t ht0 ht => radar_emission_before hL ht0 ht)
    (radar_emission_after hL)

/-- ★★★ **The reception, recorded by the relay itself**: the relay register reaches `3·10¹¹`
within `t_k ± 4.28·10¹¹`, `t_k = 1.66·10¹⁴/7` — the firing of the relay is the record. -/
noncomputable def radarReception {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (RadarArena L) ℕ L where
  evolve := radarEvolve
  evolve_self := radarEvolve_self
  evolve_comp := radarEvolve_comp
  measurable_evolve := measurable_radarEvolve
  readout := relayRead
  measurable_readout := measurable_relayRead
  ready := {y | y.1.2 = 0}
  measurableSet_ready := measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  prep := radarPrep L
  prep_mem := rfl
  site := Finset.univ
  start := 0
  value := 1
  writeStart := relayTk - 428 * 10 ^ 9
  writeEnd := relayTk + 428 * 10 ^ 9
  window := w
  isWrite :=
    have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
    { start_le := by rw [htk]; norm_num
      interval := by linarith
      window_nonneg := hw
      before := fun t ht0 ht => by
        show relayRead (radarEvolve 0 t (radarPrep L)) ≠ 1
        rw [relayRead, radarEvolve_prep_fst]
        have hr : relayReg L (relayTk - 428 * 10 ^ 9) ≤ relayLo :=
          (relayReg_start_le hL).trans (by unfold relayLo; norm_num)
        rw [relayFlow_eq_free hL hr t ⟨ht0, ht.le⟩]
        have hmono : relayReg L t ≤ relayReg L (relayTk - 428 * 10 ^ 9) := relayReg_mono ht.le
        have hlt : relayReg L t < relayLo := by
          have := relayReg_start_le hL
          have h29 : (29 * 10 ^ 10 : ℝ) < relayLo := by unfold relayLo; norm_num
          linarith
        show (if relayLo ≤ relayReg L t then (1 : ℕ) else 0) ≠ 1
        split_ifs with h
        · exact absurd h (not_le.2 hlt)
        · decide
      holds := fun t ht _ => by
        show relayRead (radarEvolve 0 t (radarPrep L)) = 1
        rw [relayRead, radarEvolve_prep_fst]
        obtain ⟨s₀, hs₀, h₀⟩ := exists_relayCross hL
        have hs₀0 : 0 ≤ s₀ := by linarith [hs₀.1]
        have hfree := relayFlow_eq_free hL h₀.le s₀ ⟨hs₀0, le_rfl⟩
        have h1 : relayLo ≤ (relayFlow t (relayPrep L)).2 := by
          calc relayLo = (relayFlow s₀ (relayPrep L)).2 := by rw [hfree, h₀]
            _ ≤ _ := relayFlow_register_mono (hs₀.2.trans ht)
        simp [h1] }

/-- Before `2t_k − 4·10¹² − 2.37·10¹²` the clipped register at `A` is below `1.7·10¹²`: the
messenger is away — out, at `B`, and on the way back. -/
theorem radar_return_before {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < 304 * 10 ^ 12 / 7 - 23685 * 10 ^ 8) :
    ∫ s in (0 : ℝ)..t, radarWeight 0 (relayFlow s (relayPrep L)) < 17 * 10 ^ 11 := by
  have hF := continuous_radarOrbit (L := L) 0
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  obtain ⟨s₀, ⟨hs₀1, hs₀2⟩, h₀⟩ := exists_relayCross hL
  have habs : |s₀ - relayTk| ≤ 428 * 10 ^ 9 := by
    rw [abs_le]; constructor <;> linarith
  have hs₀0 : 0 ≤ s₀ := by linarith
  have hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo) := by
    rw [relayFlow_eq_free hL h₀.le s₀ ⟨hs₀0, le_rfl⟩, h₀]
  refine lt_of_le_of_lt (integral_le_integral_of_nonneg hF ht0 ht.le
    fun s _ => radarWeight_zero_nonneg s) ?_
  have h := integral_le_two_bumps hF (M := 1 / 2) (a := 4 * 10 ^ 12 - 15125 * 10 ^ 8)
    (b := 4 * 10 ^ 12 + 15125 * 10 ^ 8) (c := s₀) (d := s₀ + 3 / 1000)
    (t := 304 * 10 ^ 12 / 7 - 23685 * 10 ^ 8) (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith)
    (fun s hs0 hs => by
      rw [radarWeight_zero]
      exact (atA_free_far hL h₀.le ⟨hs0.le, by linarith⟩
        (le_abs.2 (Or.inr (by linarith))) (abs_le.2 ⟨by linarith, by linarith⟩)).le)
    (fun s _ _ => by rw [radarWeight_zero]; exact atA_orbit_le_half hL s)
    (fun s hs1 hs2 => by
      rw [radarWeight_zero]
      exact (atA_free_far hL h₀.le ⟨by linarith, hs2.le⟩ (le_abs.2 (Or.inl (by linarith)))
        (abs_le.2 ⟨by linarith, by linarith⟩)).le)
    (fun s _ _ => by rw [radarWeight_zero]; exact atA_orbit_le_half hL s)
    (fun s hs1 hs2 => by
      rw [radarWeight_zero]
      exact (atA_after_far hL habs hfree hs1.le (le_abs.2 (Or.inl (by linarith)))
        (abs_le.2 ⟨by linarith, by linarith⟩)).le)
  exact h.trans_lt (by linarith)

/-- By `2t_k − 4·10¹² + 1.86·10¹²` the clipped register at `A` has reached `1.7·10¹²`: the echo
is back. -/
theorem radar_return_after :
    17 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..(304 * 10 ^ 12 / 7 + 1856 * 10 ^ 9 + 3 / 1000),
      radarWeight 0 (relayFlow s (relayPrep L)) := by
  have hF := continuous_radarOrbit (L := L) 0
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  obtain ⟨s₀, ⟨hs₀1, hs₀2⟩, h₀⟩ := exists_relayCross hL
  have habs : |s₀ - relayTk| ≤ 428 * 10 ^ 9 := by
    rw [abs_le]; constructor <;> linarith
  have hs₀0 : 0 ≤ s₀ := by linarith
  have hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo) := by
    rw [relayFlow_eq_free hL h₀.le s₀ ⟨hs₀0, le_rfl⟩, h₀]
  have h := le_integral_two_windows hF (κ₁ := 494 / 1000) (κ₂ := 463 / 1000)
    (a := 4 * 10 ^ 12 - 10 ^ 12) (b := 4 * 10 ^ 12 + 10 ^ 12)
    (c := 2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - 10 ^ 12) (d := 2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 + 10 ^ 12)
    (t := 304 * 10 ^ 12 / 7 + 1856 * 10 ^ 9 + 3 / 1000) (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith)
    (fun s _ => radarWeight_zero_nonneg s)
    (fun s h1 h2 => by
      rw [radarWeight_zero]
      exact atA_free_near hL h₀.le ⟨by linarith, by linarith⟩
        (abs_le.2 ⟨by linarith, by linarith⟩))
    (fun s h1 h2 => by
      rw [radarWeight_zero]
      exact atA_after_near hL habs hfree (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩))
  exact le_trans (by linarith) h

/-- ★★★ **The return, recorded at `A`**: the same clipped register at `A` reaches `1.7·10¹²` within
`[2t_k − 4·10¹² − 2.37·10¹², 2t_k − 4·10¹² + 1.86·10¹²]`, `2t_k − 4·10¹² = 3.04·10¹⁴/7` — the echo
returned by the moving observer is back at `A`. -/
noncomputable def radarReturn {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (RadarArena L) ℕ L :=
  regDetector relayFlow radarWeight (fun x => gatedFlow_zero relayLipschitz x)
    (fun s t x => gatedFlow_add relayLipschitz s t x) continuous_radarWeight
    (fun t => measurable_gatedFlow relayLipschitz t) 0 (17 * 10 ^ 11) (relayPrep L) Finset.univ
    (τ₀ := 304 * 10 ^ 12 / 7 - 23685 * 10 ^ 8) (τ₁ := 304 * 10 ^ 12 / 7 + 1856 * 10 ^ 9 + 3 / 1000)
    (by norm_num) (by norm_num) hw (fun s _ => radarWeight_zero_nonneg s)
    (fun t ht0 ht => radar_return_before hL ht0 ht) (radar_return_after hL)

/-- Before `5·10¹³ − 1.65·10¹²` the clipped encounter register is below `6·10¹¹`. -/
theorem radar_meeting_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 5 * 10 ^ 13 - 165 * 10 ^ 10) :
    ∫ s in (0 : ℝ)..t, radarWeight 3 (relayFlow s (relayPrep L)) < 6 * 10 ^ 11 := by
  have hF := continuous_radarOrbit (L := L) 3
  refine lt_of_le_of_lt (integral_le_integral_of_nonneg hF ht0 ht.le
    fun s _ => radarWeight_three_nonneg s) ?_
  have h := integral_le_two_bumps hF (M := 1 / 2) (a := 5 * 10 ^ 13 - 284 * 10 ^ 10)
    (b := 5 * 10 ^ 13 - 165 * 10 ^ 10) (c := 5 * 10 ^ 13 - 165 * 10 ^ 10)
    (d := 5 * 10 ^ 13 - 165 * 10 ^ 10) (t := 5 * 10 ^ 13 - 165 * 10 ^ 10) (by norm_num) (by norm_num)
    le_rfl le_rfl le_rfl
    (fun s hs0 hs => by rw [radarWeight_three]; exact (meetRaw_orbit_far hL hs0.le hs.le).le)
    (fun s _ _ => by rw [radarWeight_three]; exact meetRaw_orbit_le_half hL s)
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
  exact h.trans_lt (by norm_num)

/-- By `5·10¹³ + 5.7·10¹¹` the clipped encounter register has reached `6·10¹¹`. -/
theorem radar_meeting_after :
    6 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..(5 * 10 ^ 13 + 57 * 10 ^ 10),
      radarWeight 3 (relayFlow s (relayPrep L)) := by
  have hF := continuous_radarOrbit (L := L) 3
  have h := le_integral_two_windows hF (κ₁ := 49 / 100) (κ₂ := 0) (a := 5 * 10 ^ 13 - 66 * 10 ^ 10)
    (b := 5 * 10 ^ 13 + 57 * 10 ^ 10) (c := 5 * 10 ^ 13 + 57 * 10 ^ 10)
    (d := 5 * 10 ^ 13 + 57 * 10 ^ 10) (t := 5 * 10 ^ 13 + 57 * 10 ^ 10) (by norm_num) (by norm_num)
    le_rfl le_rfl le_rfl (fun s _ => radarWeight_three_nonneg s)
    (fun s h1 h2 => by
      rw [radarWeight_three]
      exact meetRaw_orbit_near hL (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩))
    (fun s h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
  exact le_trans (by norm_num) h

/-- ★★★ **The meeting, recorded by `B`**: the clipped encounter register of `B` with `A` reaches
`6·10¹¹` within `[5·10¹³ − 1.65·10¹², 5·10¹³ + 5.7·10¹¹]` — `B` passes `A`. -/
noncomputable def radarMeeting {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (RadarArena L) ℕ L :=
  regDetector relayFlow radarWeight (fun x => gatedFlow_zero relayLipschitz x)
    (fun s t x => gatedFlow_add relayLipschitz s t x) continuous_radarWeight
    (fun t => measurable_gatedFlow relayLipschitz t) 3 (6 * 10 ^ 11) (relayPrep L) Finset.univ
    (τ₀ := 5 * 10 ^ 13 - 165 * 10 ^ 10) (τ₁ := 5 * 10 ^ 13 + 57 * 10 ^ 10) (by norm_num)
    (by norm_num) hw (fun s _ => radarWeight_three_nonneg s)
    (fun t ht0 ht => radar_meeting_before hL ht0 ht) (radar_meeting_after hL)

/-- **Tick `n` of `A`'s clock, in the radar arena** (pulled back along `A`'s device and its tick
register, which the arena carries). -/
noncomputable def restTickRadar (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (RadarArena L) ℕ L :=
  (twinRestTick hL n hn hw).pullback radarEvolve radarEvolve_self radarEvolve_comp
    measurable_radarEvolve (fun y => (devA y.1.1, y.2 1))
    ((continuous_devA.measurable.comp measurable_fst.fst).prodMk
      ((measurable_pi_apply 1).comp measurable_snd))
    (fun s t y => by
      refine Prod.ext ?_ ?_
      · show devA (relayFlow (t - s) y.1).1
          = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) (t - s) *ᵥ devA y.1.1
        exact devA_relayFlow_any y.1 (t - s)
      · show y.2 1 + ∫ u in (0 : ℝ)..(t - s), radarWeight 1 (relayFlow u y.1)
          = y.2 1 + 1 * ∫ u in (0 : ℝ)..(t - s), rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
              (tickMark (restObserver 0))
              (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) u *ᵥ devA y.1.1)
        rw [one_mul]
        congr 1
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [radarWeight_one, devA_relayFlow_any])
    (radarPrep L) (by
      show (devA (relayState 0), (0 : Fin 4 → ℝ) 1) = (restObserver 0, 0)
      rw [devA_relayState]
      rfl)

/-- **Tick `n` of `B`'s clock, in the radar arena.** -/
noncomputable def approachTickRadar (n : ℕ) (hn : n ≤ 100) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (RadarArena L) ℕ L :=
  (approachTick hL n hn hw).pullback radarEvolve radarEvolve_self radarEvolve_comp
    measurable_radarEvolve (fun y => (devB y.1.1, y.2 2))
    ((continuous_devB.measurable.comp measurable_fst.fst).prodMk
      ((measurable_pi_apply 2).comp measurable_snd))
    (fun s t y => by
      refine Prod.ext ?_ ?_
      · show devB (relayFlow (t - s) y.1).1
          = deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) (t - s) *ᵥ devB y.1.1
        exact devB_relayFlow_any y.1 (t - s)
      · show y.2 2 + ∫ u in (0 : ℝ)..(t - s), radarWeight 2 (relayFlow u y.1)
          = y.2 2 + 1 * ∫ u in (0 : ℝ)..(t - s), rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
              (tickMark (approachObserver (-(5 * 10 ^ 13))))
              (deviceProp (relayHop L) 3 (3 + 1 / 10 ^ 11) u *ᵥ devB y.1.1)
        rw [one_mul]
        congr 1
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [radarWeight_two, devB_relayFlow_any])
    (radarPrep L) (by
      show (devB (relayState 0), (0 : Fin 4 → ℝ) 2) = (approachObserver (-(5 * 10 ^ 13)), 0)
      rw [devB_relayState, zero_sub]
      rfl)

/-! ### The fields -/

theorem radarEmission_fields {w : ℝ} (hw : 0 ≤ w) :
    (radarEmission (L := L) hL hw).evolve = radarEvolve
    ∧ (radarEmission (L := L) hL hw).prep = radarPrep L
    ∧ (radarEmission (L := L) hL hw).writeStart = 4 * 10 ^ 12 - 53 * 10 ^ 10
    ∧ (radarEmission (L := L) hL hw).writeEnd = 4 * 10 ^ 12 + 3 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem radarReception_fields {w : ℝ} (hw : 0 ≤ w) :
    (radarReception (L := L) hL hw).evolve = radarEvolve
    ∧ (radarReception (L := L) hL hw).prep = radarPrep L
    ∧ (radarReception (L := L) hL hw).writeStart = 166 * 10 ^ 12 / 7 - 428 * 10 ^ 9
    ∧ (radarReception (L := L) hL hw).writeEnd = 166 * 10 ^ 12 / 7 + 428 * 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem radarReturn_fields {w : ℝ} (hw : 0 ≤ w) :
    (radarReturn (L := L) hL hw).evolve = radarEvolve
    ∧ (radarReturn (L := L) hL hw).prep = radarPrep L
    ∧ (radarReturn (L := L) hL hw).writeStart = 304 * 10 ^ 12 / 7 - 23685 * 10 ^ 8
    ∧ (radarReturn (L := L) hL hw).writeEnd = 304 * 10 ^ 12 / 7 + 1856 * 10 ^ 9 + 3 / 1000 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem radarMeeting_fields {w : ℝ} (hw : 0 ≤ w) :
    (radarMeeting (L := L) hL hw).evolve = radarEvolve
    ∧ (radarMeeting (L := L) hL hw).prep = radarPrep L
    ∧ (radarMeeting (L := L) hL hw).writeStart = 5 * 10 ^ 13 - 165 * 10 ^ 10
    ∧ (radarMeeting (L := L) hL hw).writeEnd = 5 * 10 ^ 13 + 57 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem restTickRadar_fields (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    (restTickRadar (L := L) hL n hn hw).evolve = radarEvolve
    ∧ (restTickRadar (L := L) hL n hn hw).prep = radarPrep L
    ∧ (restTickRadar (L := L) hL n hn hw).writeStart
      = max 0 (n * (2 * Real.pi * 10 ^ 11) - 10 ^ 11)
    ∧ (restTickRadar (L := L) hL n hn hw).writeEnd = n * (2 * Real.pi * 10 ^ 11) + 10 ^ 11 := by
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

theorem approachTickRadar_fields (n : ℕ) (hn : n ≤ 100) {w : ℝ} (hw : 0 ≤ w) :
    (approachTickRadar (L := L) hL n hn hw).evolve = radarEvolve
    ∧ (approachTickRadar (L := L) hL n hn hw).prep = radarPrep L
    ∧ (approachTickRadar (L := L) hL n hn hw).writeStart
      = max 0 (2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
          - 12 * 10 ^ 10)
    ∧ (approachTickRadar (L := L) hL n hn hw).writeEnd
      = 2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
          + 12 * 10 ^ 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The bundle -/

/-- ★★★ **The radar on the Dirac chain** (BACKLOG #274, fourth landing; the row closes). On the
relay arena of #274 — `A` at rest with its clock, `B` approaching at `3/5` with its clock and its
relay, the messenger launched from `A` at `4/5` — read through the registers the arena carries:

* **one evolution**: the emission at `A`, the reception by `B` (the firing of its relay), the return
  at `A`, the meeting of `B` with `A`, and the ticks of both clocks are actual occurrences of the
  same evolution from the same preparation, which carries all of them;
* **the orbit**: `A` is `restObserver t`, `B` is `approachObserver (t − 5·10¹³)`, the weight is
  `3`; the relay fires at some `s₀` within `4.28·10¹¹` of `t_k = 1.66·10¹⁴/7`, and from
  `s₀ + 3·10⁻³` on the messenger is within `‖·‖² ≤ 2.34·10⁻⁴` of the echo
  `−iσ_y ψ_free(2s₀ + 3·10⁻³ − 4·10¹² − t)`;
* **the records**: the emission within `[4·10¹² − 5.3·10¹¹, 4·10¹² + 3·10¹⁰]`, the reception within
  `t_k ± 4.28·10¹¹`, the return within `[2t_k − 4·10¹² − 2.37·10¹², 2t_k − 4·10¹² + 1.86·10¹²]`, the
  meeting within `[5·10¹³ − 1.65·10¹², 5·10¹³ + 5.7·10¹¹]`, in this order;
* **the clocks**: `A` ticks within `10¹¹` of `n · 2π·10¹¹`; `B` within `1.2·10¹¹` of `2πn/R`, its
  splitting `R ∈ [8·10⁻¹², 8.002·10⁻¹²]`;
* **between the ticks**: the emission between `A`'s ticks `5`–`7`, the return between `65`–`73`, the
  meeting between `76`–`81`; the reception between `B`'s ticks `29`–`31`, the meeting between
  `61`–`65`;
* **the round trip** lies within `2.5·10¹²` of `2 ℓ_AB(t_k)/v`, `ℓ_AB(t_k) = β (5·10¹³ − t_k)` the
  separation at the reception, `v = 4/5` both ways;
* **the two-way factor off `A`'s clock**: the ticks from the return to the meeting over the ticks
  from the emission to the meeting lie in `[3/76, 16/69]`, which contains `(v − β)/(v + β) = 1/7`
  and excludes `0`; **with `B`'s clock** the one-way factor `k₁` (ticks of `B` from reception to
  meeting over ticks of `A` from emission to meeting) lies in `[30/76, 36/69]`, containing the
  relativistic `v√(1 − β²)/(v + β) = 16/35` and excluding the Galilean `4/7`; the echo's factor
  `k₂` lies in `[3/36, 16/30]`, containing `(v − β)/(v√(1 − β²)) = 5/16`; and
  `k₁ k₂ = (16/35)(5/16) = 1/7`. -/
theorem dirac_radar {w : ℝ} (hw : 0 ≤ w) :
    let em := radarEmission (L := L) hL hw
    let rc := radarReception (L := L) hL hw
    let ret := radarReturn (L := L) hL hw
    let meet := radarMeeting (L := L) hL hw
    let a := fun (n : ℕ) (hn : n ≤ 130) => restTickRadar (L := L) hL n hn hw
    let b := fun (n : ℕ) (hn : n ≤ 100) => approachTickRadar (L := L) hL n hn hw
    let R := levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
    let T : ℝ := 2 * Real.pi * 10 ^ 11
    let tk : ℝ := 166 * 10 ^ 12 / 7
    (rc.evolve = em.evolve ∧ rc.prep = em.prep ∧ ret.evolve = em.evolve ∧ ret.prep = em.prep
      ∧ meet.evolve = em.evolve ∧ meet.prep = em.prep
      ∧ (∀ n hn, (a n hn).evolve = em.evolve ∧ (a n hn).prep = em.prep)
      ∧ (∀ n hn, (b n hn).evolve = em.evolve ∧ (b n hn).prep = em.prep))
    ∧ (∀ t, devA (em.evolve 0 t em.prep).1.1 = restObserver t
      ∧ devB (em.evolve 0 t em.prep).1.1 = approachObserver (t - 5 * 10 ^ 13)
      ∧ sqNorm (em.evolve 0 t em.prep).1.1 = 3)
    ∧ (∃ s₀ ∈ Icc (tk - 428 * 10 ^ 9) (tk + 428 * 10 ^ 9),
        (em.evolve 0 s₀ em.prep).1.2 = relayLo
        ∧ ∀ t, s₀ + 3 / 1000 ≤ t →
          sqNorm (mess (em.evolve 0 t em.prep).1.1
              - (-I) • (spinY *ᵥ imagePacket (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)))
            ≤ (3 / 1000) ^ 2 * 26)
    ∧ (em.writeStart = 4 * 10 ^ 12 - 53 * 10 ^ 10 ∧ em.writeEnd = 4 * 10 ^ 12 + 3 * 10 ^ 10
      ∧ rc.writeStart = tk - 428 * 10 ^ 9 ∧ rc.writeEnd = tk + 428 * 10 ^ 9
      ∧ ret.writeStart = 304 * 10 ^ 12 / 7 - 23685 * 10 ^ 8
      ∧ ret.writeEnd = 304 * 10 ^ 12 / 7 + 1856 * 10 ^ 9 + 3 / 1000
      ∧ meet.writeStart = 5 * 10 ^ 13 - 165 * 10 ^ 10 ∧ meet.writeEnd = 5 * 10 ^ 13 + 57 * 10 ^ 10)
    ∧ (∀ n hn, (a n hn).writeStart = max 0 ((n : ℝ) * T - 10 ^ 11)
      ∧ (a n hn).writeEnd = (n : ℝ) * T + 10 ^ 11)
    ∧ (8 / 10 ^ 12 ≤ R ∧ R ≤ 8002 / 10 ^ 15
      ∧ ∀ n hn, (b n hn).writeStart = max 0 (2 * Real.pi * (n : ℝ) / R - 12 * 10 ^ 10)
        ∧ (b n hn).writeEnd = 2 * Real.pi * (n : ℝ) / R + 12 * 10 ^ 10)
    ∧ (em.writeEnd < rc.writeStart ∧ rc.writeEnd < ret.writeStart
      ∧ ret.writeEnd < meet.writeStart)
    ∧ ((a 5 (by norm_num)).writeEnd ≤ em.writeStart ∧ em.writeEnd ≤ (a 7 (by norm_num)).writeStart
      ∧ (a 65 (by norm_num)).writeEnd ≤ ret.writeStart
      ∧ ret.writeEnd ≤ (a 73 (by norm_num)).writeStart
      ∧ (a 76 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (a 81 (by norm_num)).writeStart)
    ∧ ((b 29 (by norm_num)).writeEnd ≤ rc.writeStart
      ∧ rc.writeEnd ≤ (b 31 (by norm_num)).writeStart
      ∧ (b 61 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (b 65 (by norm_num)).writeStart)
    ∧ (2 * (3 / 5 * (5 * 10 ^ 13 - tk)) / (4 / 5) - 25 * 10 ^ 11 ≤ ret.writeStart - em.writeEnd
      ∧ ret.writeEnd - em.writeStart ≤ 2 * (3 / 5 * (5 * 10 ^ 13 - tk)) / (4 / 5) + 25 * 10 ^ 11)
    ∧ ((76 - 73 : ℝ) / (81 - 5) ≤ 1 / 7 ∧ (1 / 7 : ℝ) ≤ (81 - 65) / (76 - 7)
      ∧ (1 / 7 : ℝ) = (4 / 5 - 3 / 5) / (4 / 5 + 3 / 5) ∧ (0 : ℝ) < (76 - 73) / (81 - 5)
      ∧ (61 - 31 : ℝ) / (81 - 5) ≤ 16 / 35 ∧ (16 / 35 : ℝ) ≤ (65 - 29) / (76 - 7)
      ∧ (65 - 29 : ℝ) / (76 - 7) < 4 / 7
      ∧ (16 / 35 : ℝ) = 4 / 5 * Real.sqrt (1 - (3 / 5) ^ 2) / (4 / 5 + 3 / 5)
      ∧ (76 - 73 : ℝ) / (65 - 29) ≤ 5 / 16 ∧ (5 / 16 : ℝ) ≤ (81 - 65) / (61 - 31)
      ∧ (5 / 16 : ℝ) = (4 / 5 - 3 / 5) / (4 / 5 * Real.sqrt (1 - (3 / 5) ^ 2))
      ∧ (16 / 35 : ℝ) * (5 / 16) = 1 / 7) := by
  intro em rc ret meet a b R T tk
  have hπ := Real.pi_pos
  have hπ1 := pi_gt_314
  have hπ2 := pi_lt_31416
  have hsq : Real.sqrt (1 - (3 / 5 : ℝ) ^ 2) = 4 / 5 := by
    rw [show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨hR1, hR2⟩ := approach_rate (L := L) hL
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  obtain ⟨e1e, e1p, e1s, e1t⟩ := radarEmission_fields (L := L) hL hw
  obtain ⟨r1e, r1p, r1s, r1t⟩ := radarReception_fields (L := L) hL hw
  obtain ⟨t1e, t1p, t1s, t1t⟩ := radarReturn_fields (L := L) hL hw
  obtain ⟨m1e, m1p, m1s, m1t⟩ := radarMeeting_fields (L := L) hL hw
  have hA := fun n hn => restTickRadar_fields (L := L) hL n hn hw
  have hB := fun n hn => approachTickRadar_fields (L := L) hL n hn hw
  have hdivlo : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
        ≤ 2 * Real.pi * k / (8 / 10 ^ 12) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) (by norm_num) hR1
  have hdivhi : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / (8002 / 10 ^ 15)
      ≤ 2 * Real.pi * k / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4))) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) hR0 hR2
  refine ⟨⟨r1e.trans e1e.symm, r1p.trans e1p.symm, t1e.trans e1e.symm, t1p.trans e1p.symm,
      m1e.trans e1e.symm, m1p.trans e1p.symm,
      fun n hn => ⟨(hA n hn).1.trans e1e.symm, (hA n hn).2.1.trans e1p.symm⟩,
      fun n hn => ⟨(hB n hn).1.trans e1e.symm, (hB n hn).2.1.trans e1p.symm⟩⟩,
    fun t => ?_, ?_, ⟨e1s, e1t, r1s, r1t, t1s, t1t, m1s, m1t⟩,
    fun n hn => ⟨(hA n hn).2.2.1, (hA n hn).2.2.2⟩,
    ⟨hR1, hR2, fun n hn => ⟨(hB n hn).2.2.1, (hB n hn).2.2.2⟩⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by rw [hsq]; norm_num, by norm_num, by norm_num, by rw [hsq]; norm_num, by norm_num⟩⟩
  · rw [e1e, e1p, radarEvolve_prep_fst]
    exact ⟨devA_relayFlow t, devB_relayFlow t, sqNorm_relayFlow hL t⟩
  · obtain ⟨-, -, -, -, -, s₀, hs₀, -, hreg, -, hret⟩ := dirac_relay (L := L) hL
    refine ⟨s₀, hs₀, ?_, fun t ht => ?_⟩
    · rw [e1e, e1p, radarEvolve_prep_fst]
      exact hreg
    · rw [e1e, e1p, radarEvolve_prep_fst]
      exact hret t ht
  · rw [e1t, r1s]
    norm_num
  · rw [r1t, t1s]
    norm_num
  · rw [t1t, m1s]
    norm_num
  · rw [(hA 5 (by norm_num)).2.2.2, e1s]
    push_cast
    nlinarith
  · rw [(hA 7 (by norm_num)).2.2.1, e1t]
    refine le_max_of_le_right ?_
    push_cast
    nlinarith
  · rw [(hA 65 (by norm_num)).2.2.2, t1s]
    push_cast
    nlinarith
  · rw [(hA 73 (by norm_num)).2.2.1, t1t]
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
  · rw [t1s, e1t]
    norm_num
  · rw [t1t, e1s]
    norm_num

end WithL

end Arena

end CSD.RecordLayer
