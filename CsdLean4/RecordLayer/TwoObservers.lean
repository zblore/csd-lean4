/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransportedClock

/-!
# A stationary and a moving observer in one model

**Category:** 7-SigmaLayer (the record layer). BACKLOG #243 (the author's fourth operational-geometry
brief, step 3), for the control candidate (A).

~~#242~~ moved one clock through a network. Here there are **two observers in one arena**, each with
its own hand clock (#201), position and momentum, and memory, and each with an **encounter register**
that its detector advances while the other is within half a cell. Observer `0` may be at rest and
observer `1` moving; the flow is the same for any pair of momenta. Relative motion is then read from
the records and compared with the transport observable.

## The arena and its flow

* `ObsArena`, `PairArena`, `obsOf`, `measurable_obsOf`; `observerFlow` (one observer alone), `observerFlow_zero`,
  `observerFlow_add`, `measurable_observerFlow`; `relPos`, `relVel`;
* ★★ `pairFlow` — **the pair's flow**: each observer by its own flow, each register advanced at rate
  `g_d` while `x₁ − x₀ ∈ [−½, ½)` — the same set as `x₀ − x₁ ∈ (−½, ½]`, so both detectors respond to
  one co-location; `pairFlow_zero`, ★★ `pairFlow_add` (the group law), `pairEvolve`,
  `pairEvolve_self`, `pairEvolve_comp`, ★ `measurable_pairFlow`;
* ★★ `obsOf_pairFlow` — **no mutual disturbance**: each observer evolves exactly as alone;
  `relPos_pairFlow`, `relVel_pairFlow`, `reg_pairFlow`.

## The encounter

* ★★ `reg_pairFlow_encounter` — **both registers see the encounter**: unchanged until the two are
  within half a cell, advanced by exactly `g_d / v` once they are half a cell apart on the other side;
* ★★★ `relSpeed_of_register` — **relative speed from the records**: each observer reads `g_d / Δη` off
  its own register, and it is the transport observable `p₁/m − p₀/m` — both read the same;
* `encounterRead`, `measurable_encounterRead`; ★★★ `encounterWrite` — **the encounter as an
  `ActualOccurrence`** for either observer.

## The clocks and the budget

* `handClockErr`, `obsReading`; ★★ `abs_obsReading_sub_le` — **each observer keeps time in the pair**;
  `observerTick` — **each observer's tick `n` as an `ActualOccurrence`** of the pair's evolution;
* `pairBudget` — observer `0`'s clock error + observer `1`'s + `|v|` × observer `0`'s (the transport
  error); ★★ `abs_relPos_sub_le` — **the transport error**: the relative position predicted on observer
  `0`'s clock; ★★ `abs_obsReading_sub_obsReading_le` — **the clocks agree when read together**;
  ★★ `pair_within_budget` — the composed bound;
* ★★★ `two_observers` — the package; ★★ `two_observers_instance` — **a concrete instance**: observer `0`
  at rest at `2`, observer `1` from `0` at momentum `1`, the encounter written over `[3/2, 5/2]`,
  relative speed `1` read by both.

## Honest scope

⚠️ **The disturbance term is zero because the detectors are test detectors.** The budget has the shape
of #212's `coupledBudget` — a sum of terms — and a detector that pushes back adds one (#251).

⚠️ **The relative speed is read from one encounter because the window's width is microscopic input**
(one cell, as the site index is in ~~#241~~). Reading it from signals exchanged at a distance — the
radar data — is #244.

⚠️ **This is the control (A)**, Galilean: the two clocks agree whatever the relative motion (as
`clock_movingFlow_indep` in ~~#241~~). The test candidate (B), two Dirac packets on one chain, is #253.

References: `specs/BACKLOG.md` #243, #242, #241, #244, #251, #253, #212, #39;
`RecordLayer/MovingClock.lean` (`occTime`, `occTime_add`, `occTime_eq_inv_of_crossed`);
`RecordLayer/TransportedClock.lean` (`measurable_occTime`, `movingTick`);
`RecordLayer/HandClock.lean`; `RecordLayer/ClockEchoCoupling.lean` (`coupledBudget`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The arena -/

/-- **One observer**: its hand clock, its position and momentum, and its memory. -/
abbrev ObsArena : Type := ActiveArena × (ℝ × ℝ) × LF4.KTorus

/-- **Two observers and their encounter registers**: observer `0`, observer `1`, and one register per
observer. -/
abbrev PairArena : Type := ObsArena × ObsArena × (Fin 2 → ℝ)

/-- Observer `i` of the pair. -/
def obsOf (i : Fin 2) (x : PairArena) : ObsArena := if i = 0 then x.1 else x.2.1

theorem measurable_obsOf (i : Fin 2) : Measurable (obsOf i) := by
  by_cases h : i = 0
  · rw [show obsOf i = fun x => x.1 from funext fun x => by simp [obsOf, h]]
    exact measurable_fst
  · rw [show obsOf i = fun x => x.2.1 from funext fun x => by simp [obsOf, h]]
    exact measurable_fst.comp measurable_snd

section Flow

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- **One observer's flow alone**: its hand clock by #194's activated flow, its position by the free
flow of `p²/(2m)`, its memory kept. -/
noncomputable def observerFlow (t : ℝ) (o : ObsArena) : ObsArena :=
  (activeFlow J ħ g hf t o.1, (o.2.1.1 + o.2.1.2 / m * t, o.2.1.2), o.2.2)

/-- The position of observer `1` relative to observer `0`. -/
def relPos (x : PairArena) : ℝ := x.2.1.2.1.1 - x.1.2.1.1

/-- The velocity of observer `1` relative to observer `0`. -/
noncomputable def relVel (x : PairArena) : ℝ := x.2.1.2.1.2 / m - x.1.2.1.2 / m

/-- ★★ **The pair's flow**: each observer by its own flow, and each encounter register advanced at
rate `g_d` while the two are within half a cell — `x₁ − x₀ ∈ [−½, ½)`, which is the same set as
`x₀ − x₁ ∈ (−½, ½]`: both detectors respond to one co-location. -/
noncomputable def pairFlow (t : ℝ) (x : PairArena) : PairArena :=
  (observerFlow J ħ g hf m t x.1, observerFlow J ħ g hf m t x.2.1,
    fun i => x.2.2 i + gd * occTime 0 (relPos x + 1 / 2) (relVel m x) t)

theorem observerFlow_zero : observerFlow J ħ g hf m 0 = id := by
  funext o
  simp [observerFlow, activeFlow_zero]

theorem observerFlow_add (s t : ℝ) :
    observerFlow J ħ g hf m (s + t) = observerFlow J ħ g hf m t ∘ observerFlow J ħ g hf m s := by
  funext o
  simp only [observerFlow, Function.comp, activeFlow_add]
  refine Prod.ext rfl (Prod.ext (Prod.ext ?_ rfl) rfl)
  ring

theorem pairFlow_zero : pairFlow J ħ g hf m gd 0 = id := by
  funext x
  simp only [pairFlow, observerFlow_zero, occTime, intervalIntegral.integral_same, mul_zero, add_zero,
    id]

/-- ★★ **The group law**: one autonomous evolution of the pair. -/
theorem pairFlow_add (s t : ℝ) :
    pairFlow J ħ g hf m gd (s + t) = pairFlow J ħ g hf m gd t ∘ pairFlow J ħ g hf m gd s := by
  funext x
  simp only [pairFlow, Function.comp, observerFlow_add]
  refine Prod.ext rfl (Prod.ext rfl (funext fun i => ?_))
  simp only [occTime_add, relPos, relVel, observerFlow]
  rw [mul_add, ← add_assoc]
  congr 3
  ring

/-- The two-time evolution. -/
noncomputable def pairEvolve (s t : OnticTime) : PairArena → PairArena := pairFlow J ħ g hf m gd (t - s)

theorem pairEvolve_self (t : OnticTime) : pairEvolve J ħ g hf m gd t t = id := by
  rw [pairEvolve, sub_self, pairFlow_zero]

theorem pairEvolve_comp (s t u : OnticTime) :
    pairEvolve J ħ g hf m gd t u ∘ pairEvolve J ħ g hf m gd s t = pairEvolve J ħ g hf m gd s u := by
  rw [pairEvolve, pairEvolve, pairEvolve, ← pairFlow_add]
  congr 1
  ring

theorem measurable_observerFlow (hf1 : ContDiff ℝ 1 f) (t : ℝ) : Measurable (observerFlow J ħ g hf m t) :=
  ((continuous_activeFlow J ħ g hf hf1 t).measurable.comp measurable_fst).prodMk
    ((by fun_prop : Measurable fun o : ObsArena => (o.2.1.1 + o.2.1.2 / m * t, o.2.1.2)).prodMk
      (measurable_snd.comp measurable_snd))

/-- ★ **Each step of the pair's evolution is measurable.** -/
theorem measurable_pairFlow (hf1 : ContDiff ℝ 1 f) (t : ℝ) : Measurable (pairFlow J ħ g hf m gd t) := by
  have hr : Measurable fun x : PairArena => (relPos x + 1 / 2, relVel m x) := by
    unfold relPos relVel
    fun_prop
  have ho := (measurable_occTime 0 t).comp hr
  refine ((measurable_observerFlow J ħ g hf m hf1 t).comp measurable_fst).prodMk
    (((measurable_observerFlow J ħ g hf m hf1 t).comp (measurable_fst.comp measurable_snd)).prodMk ?_)
  refine measurable_pi_iff.2 fun i => ?_
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).add (ho.const_mul gd)

/-! ### Each observer as if alone -/

/-- ★★ **No mutual disturbance**: each observer of the pair evolves exactly as it would alone. -/
theorem obsOf_pairFlow (i : Fin 2) (t : ℝ) (x : PairArena) :
    obsOf i (pairFlow J ħ g hf m gd t x) = observerFlow J ħ g hf m t (obsOf i x) := by
  by_cases h : i = 0 <;> simp [obsOf, h, pairFlow]

theorem relPos_pairFlow (t : ℝ) (x : PairArena) :
    relPos (pairFlow J ħ g hf m gd t x) = relPos x + relVel m x * t := by
  simp only [relPos, relVel, pairFlow, observerFlow]
  ring

theorem relVel_pairFlow (t : ℝ) (x : PairArena) :
    relVel m (pairFlow J ħ g hf m gd t x) = relVel m x := rfl

theorem reg_pairFlow (i : Fin 2) (t : ℝ) (x : PairArena) :
    (pairFlow J ħ g hf m gd t x).2.2 i = x.2.2 i + gd * occTime 0 (relPos x + 1 / 2) (relVel m x) t :=
  rfl

/-! ### The encounter -/

/-- ★★ **The encounter, as both registers see it**: while observer `1` is more than half a cell short
of observer `0` the registers are unchanged; once it has passed half a cell beyond, each has advanced
by exactly `g_d / v` — the relative speed. -/
theorem reg_pairFlow_encounter {x : PairArena} (hv : 0 < relVel m x) (i : Fin 2) {t : ℝ}
    (ht : 0 ≤ t) :
    (relPos x + relVel m x * t < -(1 / 2) → (pairFlow J ħ g hf m gd t x).2.2 i = x.2.2 i)
      ∧ (relPos x < -(1 / 2) → 1 / 2 ≤ relPos x + relVel m x * t →
          (pairFlow J ħ g hf m gd t x).2.2 i = x.2.2 i + gd * (relVel m x)⁻¹) := by
  refine ⟨fun hb => ?_, fun hx hc => ?_⟩
  · rw [reg_pairFlow, occTime_eq_zero_of_before hv.le ht (by push_cast; linarith), mul_zero,
      add_zero]
  · rw [reg_pairFlow, occTime_eq_inv_of_crossed hv (by push_cast; linarith) (by push_cast; linarith)]

/-- ★★★ **Relative speed, read from the records**: after the encounter, both observers read the same
relative speed `g_d / Δη` off their own registers, and it is the transport observable
`p₁/m − p₀/m`. -/
theorem relSpeed_of_register {x : PairArena} (hv : 0 < relVel m x) (hgd : gd ≠ 0) (i : Fin 2)
    {t : ℝ} (ht : 0 ≤ t) (hx : relPos x < -(1 / 2)) (hc : 1 / 2 ≤ relPos x + relVel m x * t) :
    gd / ((pairFlow J ħ g hf m gd t x).2.2 i - x.2.2 i) = relVel m x := by
  rw [((reg_pairFlow_encounter J ħ g hf m gd hv i ht).2 hx hc), add_sub_cancel_left, div_mul_eq_div_div,
    div_self hgd, one_div, inv_inv]

/-- **An encounter register's readout**: whether it has reached the threshold `θ`. -/
noncomputable def encounterRead (θ : ℝ) (i : Fin 2) (x : PairArena) : ℕ :=
  if θ ≤ x.2.2 i then 1 else 0

theorem measurable_encounterRead (θ : ℝ) (i : Fin 2) : Measurable (encounterRead θ i) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))

/-- ★★★ **The encounter as an actual occurrence, for either observer**: observer `i`'s register,
prepared at zero with threshold `0 < θ ≤ g_d / v`, is written while the two pass — not before they
come within half a cell, and from the time they are half a cell apart on the other side. -/
noncomputable def encounterWrite (hf1 : ContDiff ℝ 1 f) {K : ℕ} (site : Finset (Fin K)) (θ : ℝ)
    (hθ0 : 0 < θ) (i : Fin 2) (x₀ : PairArena) (hreg : x₀.2.2 i = 0) (hv : 0 < relVel m x₀)
    (hx : relPos x₀ < -(1 / 2)) (hθ : θ ≤ gd * (relVel m x₀)⁻¹) :
    ActualOccurrence PairArena ℕ K where
  evolve := pairEvolve J ħ g hf m gd
  evolve_self := pairEvolve_self J ħ g hf m gd
  evolve_comp := pairEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_pairFlow J ħ g hf m gd hf1 (t - s)
  readout := encounterRead θ i
  measurable_readout := measurable_encounterRead θ i
  ready := {x | x.2.2 i = 0}
  measurableSet_ready := measurableSet_eq_fun
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) measurable_const
  prep := x₀
  prep_mem := hreg
  site := site
  start := 0
  value := 1
  writeStart := (-(1 / 2) - relPos x₀) / relVel m x₀
  writeEnd := (1 / 2 - relPos x₀) / relVel m x₀
  window := 1 / relVel m x₀
  isWrite :=
    { start_le := div_nonneg (by linarith) hv.le
      interval := div_le_div_of_nonneg_right (by linarith) hv.le
      window_nonneg := by positivity
      before := fun t ht0 ht => by
        have hb : relPos x₀ + relVel m x₀ * t < -(1 / 2) := by
          rw [lt_div_iff₀ hv] at ht
          linarith
        show encounterRead θ i (pairFlow J ħ g hf m gd (t - 0) x₀) ≠ 1
        rw [sub_zero, encounterRead, (reg_pairFlow_encounter J ħ g hf m gd hv i ht0).1 hb, hreg,
          ite_eq_right (by linarith)]
        decide
      holds := fun t ht₁ _ => by
        have hc : 1 / 2 ≤ relPos x₀ + relVel m x₀ * t := by
          rw [div_le_iff₀ hv] at ht₁
          linarith
        have ht0 : 0 ≤ t := (div_nonneg (by linarith) hv.le).trans ht₁
        show encounterRead θ i (pairFlow J ħ g hf m gd (t - 0) x₀) = 1
        rw [sub_zero, encounterRead, (reg_pairFlow_encounter J ħ g hf m gd hv i ht0).2 hx hc, hreg,
          zero_add, ite_eq_left hθ] }

/-! ### The clocks -/

/-- **An observer's clock error** over its horizon: #201's `τ_tick + 1/(2ω)`. -/
noncomputable def handClockErr (K : ℕ) (q : LF4.KTorus) : ℝ :=
  tickTime K (handRate J ħ g hf q) + 1 / (2 * handFreq J ħ g hf q)

/-- The reading of observer `i`'s clock. -/
noncomputable def obsReading (K : ℕ) (q : LF4.KTorus) (i : Fin 2) (x : PairArena) : ℝ :=
  handReading K (tickTime K (handRate J ħ g hf q)) (obsOf i x).1.2

/-- ★★ **Each observer keeps time in the pair**, within its own clock error over its horizon. -/
theorem abs_obsReading_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {i : Fin 2} {x : PairArena}
    (hx : (obsOf i x).1 = (msgPoint 1, q)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |obsReading J ħ g hf K q i (pairFlow J ħ g hf m gd t x) - t| ≤ handClockErr J ħ g hf K q := by
  rw [obsReading, obsOf_pairFlow, observerFlow, hx]
  exact abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht

/-- **Tick `n` of observer `i`'s clock as an actual occurrence** of the pair's evolution. -/
noncomputable def observerTick (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K)
    (i : Fin 2) (x₀ : PairArena) (hx : (obsOf i x₀).1 = (msgPoint 1, q)) {L : ℕ}
    (site : Finset (Fin L)) : ActualOccurrence PairArena ℕ L where
  evolve := pairEvolve J ħ g hf m gd
  evolve_self := pairEvolve_self J ħ g hf m gd
  evolve_comp := pairEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_pairFlow J ħ g hf m gd hf1 (t - s)
  readout := fun x => handCount K (obsOf i x).1.2
  measurable_readout :=
    (measurable_handCount K).comp (measurable_snd.comp (measurable_fst.comp (measurable_obsOf i)))
  ready := {x | (obsOf i x).1 = (msgPoint 1, q)}
  measurableSet_ready := (measurable_fst.comp (measurable_obsOf i)) (measurableSet_singleton _)
  prep := x₀
  prep_mem := hx
  site := site
  start := 0
  value := n
  writeStart := tickStart K (handRate J ħ g hf q) n
  writeEnd := tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n
  window := tickWindow K (handRate J ħ g hf q) (handFreq J ħ g hf q)
  isWrite :=
    { start_le := tickStart_nonneg hK hκ hn1
      interval := tickStart_le_tickEnd hK hκ (handFreq_pos J ħ g hf hJ hħ q) n
      window_nonneg := tickWindow_nonneg hK hκ hslow
      before := fun t ht0 ht => by
        show handCount K (obsOf i (pairFlow J ħ g hf m gd (t - 0) x₀)).1.2 ≠ n
        rw [sub_zero, obsOf_pairFlow, observerFlow, hx]
        exact (hand_before_tick J ħ g hf hJ hħ hK hq hκ hn1 hnK ht0 ht).ne
      holds := fun t ht₁ ht₂ => by
        show handCount K (obsOf i (pairFlow J ħ g hf m gd (t - 0) x₀)).1.2 = n
        rw [sub_zero, obsOf_pairFlow, observerFlow, hx]
        exact hand_at_tick J ħ g hf hJ hħ hK hq hκ hnK ht₁ ht₂ }

/-! ### The budget -/

/-- **The pair's budget**: observer `0`'s clock error, observer `1`'s, and the transport error —
observer `1`'s relative position predicted on observer `0`'s clock, off by `|v|` times that clock's
error. The mutual disturbance contributes no term: each observer evolves as alone
(`obsOf_pairFlow`); a detector that pushes back adds one (#251). -/
noncomputable def pairBudget (K : ℕ) (q₀ q₁ : LF4.KTorus) (v : ℝ) : ℝ :=
  handClockErr J ħ g hf K q₀ + handClockErr J ħ g hf K q₁ + |v| * handClockErr J ħ g hf K q₀

/-- ★★ **The transport error**: observer `1`'s position relative to observer `0`, predicted from its
relative velocity on observer `0`'s clock, is off by at most `|v|` times that clock's error. -/
theorem abs_relPos_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {x : PairArena}
    (hx : (obsOf 0 x).1 = (msgPoint 1, q)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |relPos (pairFlow J ħ g hf m gd t x)
        - (relPos x + relVel m x * obsReading J ħ g hf K q 0 (pairFlow J ħ g hf m gd t x))|
      ≤ |relVel m x| * handClockErr J ħ g hf K q := by
  have h := abs_obsReading_sub_le J ħ g hf m gd hJ hħ hK hq hκ hx ht0 ht
  rw [relPos_pairFlow, show relPos x + relVel m x * t
      - (relPos x + relVel m x * obsReading J ħ g hf K q 0 (pairFlow J ħ g hf m gd t x))
      = -(relVel m x * (obsReading J ħ g hf K q 0 (pairFlow J ħ g hf m gd t x) - t)) by ring,
    abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- ★★ **The two clocks agree when read together**, within the sum of their errors — the control is
Galilean: no relative motion shows in their readings. -/
theorem abs_obsReading_sub_obsReading_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K)
    {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁) {x : PairArena}
    (hx₀ : (obsOf 0 x).1 = (msgPoint 1, q₀)) (hx₁ : (obsOf 1 x).1 = (msgPoint 1, q₁)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht₀ : t ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (ht₁ : t ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁)) :
    |obsReading J ħ g hf K q₀ 0 (pairFlow J ħ g hf m gd t x)
        - obsReading J ħ g hf K q₁ 1 (pairFlow J ħ g hf m gd t x)|
      ≤ handClockErr J ħ g hf K q₀ + handClockErr J ħ g hf K q₁ := by
  have h₀ := abs_obsReading_sub_le J ħ g hf m gd hJ hħ hK hq₀ hκ₀ hx₀ ht0 ht₀
  have h₁ := abs_obsReading_sub_le J ħ g hf m gd hJ hħ hK hq₁ hκ₁ hx₁ ht0 ht₁
  calc _ = |(obsReading J ħ g hf K q₀ 0 (pairFlow J ħ g hf m gd t x) - t)
          - (obsReading J ħ g hf K q₁ 1 (pairFlow J ħ g hf m gd t x) - t)| := by ring_nf
    _ ≤ _ := (abs_sub _ _).trans (add_le_add h₀ h₁)

/-- ★★ **The pair's budget composes the bounds**: over the shared horizon, the clock disagreement plus
the transport error stay within `pairBudget`. -/
theorem pair_within_budget (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K)
    {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁) {x : PairArena}
    (hx₀ : (obsOf 0 x).1 = (msgPoint 1, q₀)) (hx₁ : (obsOf 1 x).1 = (msgPoint 1, q₁)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht₀ : t ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (ht₁ : t ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁)) :
    |obsReading J ħ g hf K q₀ 0 (pairFlow J ħ g hf m gd t x)
        - obsReading J ħ g hf K q₁ 1 (pairFlow J ħ g hf m gd t x)|
      + |relPos (pairFlow J ħ g hf m gd t x)
          - (relPos x + relVel m x * obsReading J ħ g hf K q₀ 0 (pairFlow J ħ g hf m gd t x))|
      ≤ pairBudget J ħ g hf K q₀ q₁ (relVel m x) :=
  add_le_add (abs_obsReading_sub_obsReading_le J ħ g hf m gd hJ hħ hK hq₀ hq₁ hκ₀ hκ₁ hx₀ hx₁ ht0 ht₀ ht₁)
    (abs_relPos_sub_le J ħ g hf m gd hJ hħ hK hq₀ hκ₀ hx₀ ht0 ht₀)

/-- ★★★ **A stationary and a moving observer in one model (#243).** Two observers, each with its own
hand clock and memory, and an encounter register each, under one measurable autonomous evolution in
which each observer evolves exactly as alone (no mutual disturbance); once they have passed, both read
the same relative speed off their own registers and it is the transport observable; and over the
shared horizon their clocks agree and the relative position is predicted on observer `0`'s clock
within `pairBudget`. -/
theorem two_observers (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁) (hgd : gd ≠ 0) {x : PairArena}
    (hx₀ : (obsOf 0 x).1 = (msgPoint 1, q₀)) (hx₁ : (obsOf 1 x).1 = (msgPoint 1, q₁))
    (hv : 0 < relVel m x) (hfar : relPos x < -(1 / 2)) :
    (∀ s t, pairFlow J ħ g hf m gd (s + t) = pairFlow J ħ g hf m gd t ∘ pairFlow J ħ g hf m gd s)
    ∧ (∀ t, Measurable (pairFlow J ħ g hf m gd t))
    ∧ (∀ i t x', obsOf i (pairFlow J ħ g hf m gd t x') = observerFlow J ħ g hf m t (obsOf i x'))
    ∧ (∀ i t, 0 ≤ t → 1 / 2 ≤ relPos x + relVel m x * t →
        gd / ((pairFlow J ħ g hf m gd t x).2.2 i - x.2.2 i) = relVel m x)
    ∧ (∀ t, 0 ≤ t → t ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀) →
        t ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁) →
        |obsReading J ħ g hf K q₀ 0 (pairFlow J ħ g hf m gd t x)
            - obsReading J ħ g hf K q₁ 1 (pairFlow J ħ g hf m gd t x)|
          + |relPos (pairFlow J ħ g hf m gd t x)
              - (relPos x + relVel m x * obsReading J ħ g hf K q₀ 0 (pairFlow J ħ g hf m gd t x))|
          ≤ pairBudget J ħ g hf K q₀ q₁ (relVel m x)) :=
  ⟨pairFlow_add J ħ g hf m gd, measurable_pairFlow J ħ g hf m gd hf1,
    obsOf_pairFlow J ħ g hf m gd,
    fun i _ ht hc => relSpeed_of_register J ħ g hf m gd hv hgd i ht hfar hc,
    fun _ ht0 ht₀ ht₁ => pair_within_budget J ħ g hf m gd hJ hħ hK hq₀ hq₁ hκ₀ hκ₁ hx₀ hx₁ ht0 ht₀ ht₁⟩

/-- ★★ **A concrete instance in motion**: mass `1`; observer `0` at rest at `2`, observer `1` at `0`
with momentum `1`. The relative position is `−2`, the relative velocity `1`; each observer's encounter
record is written over `[3/2, 5/2]` (threshold `g_d > 0`), and at time `3` each reads relative
speed `1`. -/
theorem two_observers_instance (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) (q₀ q₁ mem₀ mem₁ : LF4.KTorus)
    {K : ℕ} (site : Finset (Fin K)) (i : Fin 2) :
    let x : PairArena := (((msgPoint 1, q₀), (2, 0), mem₀), ((msgPoint 1, q₁), (0, 1), mem₁), 0)
    relPos x = -2 ∧ relVel 1 x = 1
    ∧ (encounterWrite J ħ g hf 1 gd hf1 site gd hgd i x rfl (by norm_num [relVel])
        (by norm_num [relPos]) (by norm_num [relVel])).writeStart = 3 / 2
    ∧ (encounterWrite J ħ g hf 1 gd hf1 site gd hgd i x rfl (by norm_num [relVel])
        (by norm_num [relPos]) (by norm_num [relVel])).writeEnd = 5 / 2
    ∧ gd / ((pairFlow J ħ g hf 1 gd 3 x).2.2 i - x.2.2 i) = 1 := by
  intro x
  have hp : relPos x = -2 := by norm_num [x, relPos]
  have hv : relVel 1 x = 1 := by norm_num [x, relVel]
  refine ⟨hp, hv, by simp only [encounterWrite, hp, hv]; norm_num,
    by simp only [encounterWrite, hp, hv]; norm_num, ?_⟩
  rw [relSpeed_of_register J ħ g hf 1 gd (by rw [hv]; norm_num) hgd.ne' i (by norm_num)
    (by rw [hp]; norm_num) (by rw [hp, hv]; norm_num), hv]

end Flow

end CSD.RecordLayer

end
