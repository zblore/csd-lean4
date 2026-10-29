/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ClockAndEcho

/-!
# The clock coupled to the echo

**Category:** 7-SigmaLayer (the record layer). BACKLOG #212, the dynamics half (residue of #202).

In #202 the hand clock and the echo sit on one arena and do not interact; the clock is colocated with
`A` by a shared site label. Here they are coupled: **the clock's carrier is detuned at `A` by the
echo's pointer**, one more back-reaction term `g_c f_c(θ₂ᴬ) n_{A,c}` in the joint energy. Hamilton's
equations then make the clock's carrier a two-site detuned exchange, detuned at `A` by `θ₂ᴬ` and at
`B` by the hand, and make **the echo's pointer `A` turn while the clock's carrier is at `A`** —
reading the clock disturbs the echo's register.

* `clockView`, `clockUnview` — the clock's coordinates (its carrier, the echo's pointer `A`, the hand)
  arranged as an echo arena whose pointer `A` is the echo's own; `echoStep`, `clockStep` — #199's echo
  flow on the echo's coordinates and on the clock's view; ★ `coupledFlow` — the clock's step after
  the echo's;
* ★★ `echoStep_comm_clockStep` — **the two steps commute** (they share only pointer `A`, and each
  translates its first angle by an amount read from coordinates the other does not move);
  ★★ `coupledFlow_add` — the group law; `coupledFlow_angles` — **the three conserved angles stay
  conserved**; `coupledEvolve`, `coupledEvolve_comp`, ★ `coupledEvolve_shift` — two-time and
  autonomous;
* `clockShuffle`, `clockShuffle_measurePreserving` — the rearrangement that puts the clock's view
  first; ★★ `coupledEvolve_measurePreserving` — **Liouville**; ★★ `coupledEnergy_coupledFlow` —
  **the joint energy, cross term included, is conserved**;
* `bandEmitEnd`, `bandReturnEnd`, `bandWindow`, `mem_emit_of_band`, `mem_return_of_band` — #199's
  window arithmetic for any displacement in a band `[m t − b, m t + b]`;
  ★ `pointerDrift_monotone`, `rep_driftHand`, `driftHand_count_mono`, `abs_driftHand_reading_sub_le`,
  `driftHand_before_tick`, `driftHand_at_tick` — #201's hand clock for any mean rate `κ` and Rabi rate
  `ω` (the coupled clock's constants depend on `θ₂ᴬ`);
* `coupledRate`, `coupledMean`, `coupledBand`, `clockRate`, `clockFreq` — the coupled constants;
  ★★ `coupledFlow_pointerA` — **pointer `A` turns by the echo's drift plus the clock carrier's**;
  `coupledFlow_pointerB`, ★ `coupledFlow_hand`;
* ★★ `coupledEmission`, `coupledReception`, `coupledReturn`, `coupledTick` — **the three echo writes
  and the ticks are still `ActualOccurrence`s**, with the coupled windows (the reception's are #199's,
  pointer `B` being the echo's alone);
* `coupledReadingAt`, `coupledReadings`, `couplingTerm`, `coupledBudget` — **the budget acquires a
  term for the coupling**: the shift of the return record's completion; ★★ `couplingTerm_le` — it is
  `(b_c − m_c · returnEnd)/m`, so at most `(b_c + m_c · returnEnd)/m`;
  ★★ `abs_coupledReadings_emit_sub_le`, `abs_coupledReadings_ret_sub_le`;
* ★ `abs_clockFreq_sub_handFreq_le`, ★ `abs_clockRate_sub_handRate_le` — **the coupling's effect on
  the clock's constants**: `|ω_c − ω| ≤ |g_c f_c(θ₂ᴬ)|/(2ħ)` and
  `|κ_c − κ| ≤ |r_h| |g_c f_c(θ₂ᴬ)|/(2J_c)`, from `abs_rabiFreq_sub_le` and `abs_loss_sub_le`;
  ★★ `coupledBudget_of_g_eq_zero` — **at zero coupling the budget is #202's exactly**;
* ★★★ `coupled_clock_and_echo` — the package.

## Honest scope

* **Generation is in `RecordLayer/ClockEchoHamiltonian.lean`** (BACKLOG ~~#225~~): read on
  `(ℂℙ³ × T² × T²) × (ℂℙ³ × T²)`, `coupledFlow` is the Hamiltonian flow of `−(2/ħ)` times
  `coupledEnergy` (`hamiltonianFlow_coupledFlow`), the cross term's field computed in
  `LF4/CrossCoupledFlow.lean`. This file builds the dynamics and proves it is a two-time,
  measure-preserving, energy-conserving flow with the stated equations of motion.
* The tick windows are #201's formulas evaluated at the coupled constants; the coupling moves those
  constants by the stated bounds, and the clock remains self-calibrated (`τ_tick = 2/(Kκ_c)`), so
  its resolution in the budget is the coupled one.
* The clock carrier's rate at `A` is taken non-negative (`0 ≤ senderRate Cc ħ q_A`), so that it adds
  to pointer `A`'s staircase rather than unwinding it; the coupled slowness is
  `coupledBand ≤ 1/12`.
* **No universal `c`, no Lorentz invariance**; the #187 and #190 headers stand.

References: `specs/BACKLOG.md` #212, #202, #199, #201, #194, #195, #39; `RecordLayer/ClockAndEcho.lean`
(the uncoupled device), `RecordLayer/EchoArena.lean` (`echoFlow`, `senderDrift`, the window
arithmetic this generalises), `RecordLayer/HandClock.lean` (the hand clock this generalises),
`RecordLayer/EchoRadar.lean`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The clock's view of the arena -/

/-- **The clock's view**: its carrier, the echo's pointer at `A`, and the hand — the coordinates the
coupled clock reads and moves, arranged as an echo arena whose pointer `A` is the echo's own. -/
def clockView (x : ClockEchoArena) : EchoArena := (x.2.1, (x.1.2.1, x.2.2))

/-- Writing the clock's view back into the arena. -/
def clockUnview (x : ClockEchoArena) (y : EchoArena) : ClockEchoArena :=
  ((x.1.1, (y.2.1, x.1.2.2)), (y.1, y.2.2))

@[simp] theorem clockView_clockUnview (x : ClockEchoArena) (y : EchoArena) :
    clockView (clockUnview x y) = y := rfl

@[simp] theorem clockUnview_clockUnview (x : ClockEchoArena) (y z : EchoArena) :
    clockUnview (clockUnview x y) z = clockUnview x z := rfl

@[simp] theorem clockUnview_clockView (x : ClockEchoArena) : clockUnview x (clockView x) = x := rfl

theorem continuous_clockView : Continuous clockView :=
  continuous_snd.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd.snd)

/-! ### The two steps and the coupled flow -/

/-- **The echo's step**: #199's flow on the echo's coordinates, the clock untouched. -/
noncomputable def echoStep (J ħ : ℝ) (A B : PointerCoupling) (t : ℝ) (x : ClockEchoArena) :
    ClockEchoArena :=
  (echoFlow J ħ A B t x.1, x.2)

/-- **The clock's step**: the clock's carrier is a two-site detuned exchange, detuned at `A` by the
echo's pointer (`g_c f_c(θ₂ᴬ)`, coupling `Cc`) and at `B` by the hand (`g f(θ₂ʰ)`, coupling `C`); it
turns the hand while it is at `B` and **the echo's pointer `A` while it is at `A`**. As data this is
#199's echo flow run on the clock's view. -/
noncomputable def clockStep (Jc ħ : ℝ) (Cc C : PointerCoupling) (t : ℝ) (x : ClockEchoArena) :
    ClockEchoArena :=
  clockUnview x (echoFlow Jc ħ Cc C t (clockView x))

/-- ★ **The coupled flow**: the clock's step after the echo's. -/
noncomputable def coupledFlow (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (Cc C : PointerCoupling)
    (t : ℝ) : ClockEchoArena → ClockEchoArena :=
  clockStep Jc ħ Cc C t ∘ echoStep J ħ A B t

section Dynamics

variable (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (Cc C : PointerCoupling)

theorem echoStep_zero : echoStep J ħ A B 0 = id := by
  funext x
  simp [echoStep, echoFlow_zero]

theorem clockStep_zero : clockStep Jc ħ Cc C 0 = id := by
  funext x
  simp [clockStep, echoFlow_zero]

theorem echoStep_add (s t : ℝ) : echoStep J ħ A B (s + t) = echoStep J ħ A B t ∘ echoStep J ħ A B s := by
  funext x
  simp [echoStep, echoFlow_add]

theorem clockStep_add (s t : ℝ) :
    clockStep Jc ħ Cc C (s + t) = clockStep Jc ħ Cc C t ∘ clockStep Jc ħ Cc C s := by
  funext x
  simp [clockStep, echoFlow_add]

/-- ★★ **The two steps commute**: they share only the echo's pointer `A`, and each translates its
first angle by an amount read from coordinates the other does not move. -/
theorem echoStep_comm_clockStep (s t : ℝ) :
    echoStep J ħ A B s ∘ clockStep Jc ħ Cc C t = clockStep Jc ħ Cc C t ∘ echoStep J ħ A B s := by
  funext x
  refine Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) rfl
  show pshift (echoAmountA J ħ A B s x.1) (pshift (echoAmountA Jc ħ Cc C t (clockView x)) x.1.2.1)
    = pshift (echoAmountA Jc ħ Cc C t (clockView x)) (pshift (echoAmountA J ħ A B s x.1) x.1.2.1)
  rw [pshift_add, pshift_add, add_comm]

theorem coupledFlow_zero : coupledFlow J ħ A B Jc Cc C 0 = id := by
  rw [coupledFlow, echoStep_zero, clockStep_zero]
  rfl

/-- ★★ **The group law.** -/
theorem coupledFlow_add (s t : ℝ) :
    coupledFlow J ħ A B Jc Cc C (s + t) = coupledFlow J ħ A B Jc Cc C t ∘ coupledFlow J ħ A B Jc Cc C s := by
  funext x
  simp only [coupledFlow, clockStep_add, echoStep_add, Function.comp_apply]
  exact congrArg (clockStep Jc ħ Cc C t)
    (congrFun (echoStep_comm_clockStep J ħ A B Jc Cc C t s) (echoStep J ħ A B s x)).symm

/-- The coupled flow in components. -/
theorem coupledFlow_apply (t : ℝ) (x : ClockEchoArena) :
    coupledFlow J ħ A B Jc Cc C t x
      = (((echoFlow J ħ A B t x.1).1,
          (pshift (echoAmountA Jc ħ Cc C t (clockView x)) (echoFlow J ħ A B t x.1).2.1,
            (echoFlow J ħ A B t x.1).2.2)),
        ((echoFlow Jc ħ Cc C t (clockView x)).1, (echoFlow Jc ħ Cc C t (clockView x)).2.2)) :=
  rfl

/-- **The conserved angles stay conserved**: `θ₂ᴬ`, `θ₂ᴮ` and `θ₂ʰ`. -/
theorem coupledFlow_angles (t : ℝ) (x : ClockEchoArena) :
    (coupledFlow J ħ A B Jc Cc C t x).1.2.1.2 = x.1.2.1.2
      ∧ (coupledFlow J ħ A B Jc Cc C t x).1.2.2.2 = x.1.2.2.2
      ∧ (coupledFlow J ħ A B Jc Cc C t x).2.2.2 = x.2.2.2 :=
  ⟨rfl, rfl, rfl⟩

/-- **The two-time propagator**. -/
noncomputable def coupledEvolve (s t : OnticTime) : ClockEchoArena → ClockEchoArena :=
  coupledFlow J ħ A B Jc Cc C (t - s)

theorem coupledEvolve_self (t : OnticTime) : coupledEvolve J ħ A B Jc Cc C t t = id := by
  rw [coupledEvolve, sub_self, coupledFlow_zero]

/-- The two-time law. -/
theorem coupledEvolve_comp (s t u : OnticTime) :
    coupledEvolve J ħ A B Jc Cc C t u ∘ coupledEvolve J ħ A B Jc Cc C s t
      = coupledEvolve J ħ A B Jc Cc C s u := by
  unfold coupledEvolve
  rw [← coupledFlow_add]
  congr 1
  ring

/-- ★ **Autonomy**: no test of `t_Σ`. -/
theorem coupledEvolve_shift (s t a : OnticTime) :
    coupledEvolve J ħ A B Jc Cc C (s + a) (t + a) = coupledEvolve J ħ A B Jc Cc C s t := by
  unfold coupledEvolve
  congr 1
  ring

theorem continuous_echoStep (t : ℝ) : Continuous (echoStep J ħ A B t) :=
  ((continuous_echoFlow J ħ A B t).comp continuous_fst).prodMk continuous_snd

theorem continuous_clockStep (t : ℝ) : Continuous (clockStep Jc ħ Cc C t) := by
  have h : Continuous fun x : ClockEchoArena => echoFlow Jc ħ Cc C t (clockView x) :=
    (continuous_echoFlow Jc ħ Cc C t).comp continuous_clockView
  exact (continuous_fst.fst.prodMk (h.snd.fst.prodMk continuous_fst.snd.snd)).prodMk
    (h.fst.prodMk h.snd.snd)

theorem measurable_coupledEvolve (s t : OnticTime) :
    Measurable (coupledEvolve J ħ A B Jc Cc C s t) := by
  unfold coupledEvolve coupledFlow
  exact ((continuous_clockStep ħ Jc Cc C _).comp (continuous_echoStep J ħ A B _)).measurable

/-! ### Liouville -/

/-- The rearrangement `((a, (b, c)), (d, e)) ↦ ((d, (b, e)), (a, c))` that puts the clock's view
first. -/
noncomputable def clockShuffle : ClockEchoArena ≃ᵐ EchoArena × (FieldArena 2 2 × LF4.KTorus) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      MeasurableEquiv.prodComm) (MeasurableEquiv.refl _)).trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.refl _)).trans
      (MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.prodAssoc.symm.trans
          ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _)).trans
            MeasurableEquiv.prodAssoc)) (MeasurableEquiv.refl _)))))

theorem clockShuffle_apply (x : ClockEchoArena) : clockShuffle x = (clockView x, (x.1.1, x.1.2.2)) := by
  simp only [clockShuffle, MeasurableEquiv.trans_apply]
  rfl

set_option synthInstance.maxSize 512 in
theorem clockShuffle_measurePreserving (p₀ p₁ : FieldArena 2 2) :
    MeasurePreserving clockShuffle
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
      (((fsMeasure p₁).prod volume).prod ((fsMeasure p₀).prod volume)) := by
  have v := (volume : Measure LF4.KTorus)
  have s1 := ((MeasurePreserving.id (fsMeasure p₀)).prod
      (Measure.measurePreserving_swap (μ := (volume : Measure LF4.KTorus))
        (ν := (volume : Measure LF4.KTorus)))).prod
      (MeasurePreserving.id ((fsMeasure p₁).prod (volume : Measure LF4.KTorus)))
  have s2 := ((measurePreserving_prodAssoc (fsMeasure p₀) (volume : Measure LF4.KTorus)
      (volume : Measure LF4.KTorus)).symm MeasurableEquiv.prodAssoc).prod
      (MeasurePreserving.id ((fsMeasure p₁).prod (volume : Measure LF4.KTorus)))
  have s3 := measurePreserving_prodAssoc ((fsMeasure p₀).prod (volume : Measure LF4.KTorus))
      (volume : Measure LF4.KTorus) ((fsMeasure p₁).prod (volume : Measure LF4.KTorus))
  have s4 := Measure.measurePreserving_swap (μ := (fsMeasure p₀).prod (volume : Measure LF4.KTorus))
      (ν := (volume : Measure LF4.KTorus).prod ((fsMeasure p₁).prod (volume : Measure LF4.KTorus)))
  have g1 := (measurePreserving_prodAssoc (volume : Measure LF4.KTorus) (fsMeasure p₁)
      (volume : Measure LF4.KTorus)).symm MeasurableEquiv.prodAssoc
  have g2 := (Measure.measurePreserving_swap (μ := (volume : Measure LF4.KTorus))
      (ν := fsMeasure p₁)).prod (MeasurePreserving.id (volume : Measure LF4.KTorus))
  have g3 := measurePreserving_prodAssoc (fsMeasure p₁) (volume : Measure LF4.KTorus)
      (volume : Measure LF4.KTorus)
  have s5 := (g3.comp (g2.comp g1)).prod
      (MeasurePreserving.id ((fsMeasure p₀).prod (volume : Measure LF4.KTorus)))
  exact s5.comp (s4.comp (s3.comp (s2.comp s1)))

theorem clockStep_eq (t : ℝ) :
    clockStep Jc ħ Cc C t
      = clockShuffle.symm ∘ Prod.map (echoFlow Jc ħ Cc C t) id ∘ clockShuffle := by
  funext x
  refine ((MeasurableEquiv.symm_apply_eq clockShuffle).2 ?_).symm
  rw [Function.comp_apply, clockShuffle_apply, clockShuffle_apply]
  rfl

theorem echoStep_measurePreserving (t : ℝ) (p₀ p₁ : FieldArena 2 2) :
    MeasurePreserving (echoStep J ħ A B t)
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)) :=
  (echoFlow_measurePreserving J ħ A B t p₀).prod (MeasurePreserving.id _)

theorem clockStep_measurePreserving (t : ℝ) (p₀ p₁ : FieldArena 2 2) :
    MeasurePreserving (clockStep Jc ħ Cc C t)
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)) := by
  rw [clockStep_eq]
  have h := clockShuffle_measurePreserving p₀ p₁
  exact (h.symm clockShuffle).comp
    (((echoFlow_measurePreserving Jc ħ Cc C t p₁).prod (MeasurePreserving.id _)).comp h)

/-- ★★ **Liouville** for the coupled flow. -/
theorem coupledEvolve_measurePreserving (s t : OnticTime) (p₀ p₁ : FieldArena 2 2) :
    MeasurePreserving (coupledEvolve J ħ A B Jc Cc C s t)
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)) := by
  unfold coupledEvolve coupledFlow
  exact (clockStep_measurePreserving ħ Jc Cc C _ p₀ p₁).comp (echoStep_measurePreserving J ħ A B _ p₀ p₁)

/-- **The joint energy** of the coupled device: the echo's and the clock's, the clock's including
the cross term `g_c f_c(θ₂ᴬ) n_{A,c}`. -/
noncomputable def coupledEnergy (x : ClockEchoArena) : ℝ :=
  echoEnergy J A B x.1 + echoEnergy Jc Cc C (clockView x)

/-- ★★ **Energy conservation.** -/
theorem coupledEnergy_coupledFlow (t : ℝ) (x : ClockEchoArena) :
    coupledEnergy J A B Jc Cc C (coupledFlow J ħ A B Jc Cc C t x) = coupledEnergy J A B Jc Cc C x := by
  unfold coupledEnergy
  have h1 : echoEnergy J A B (coupledFlow J ħ A B Jc Cc C t x).1 = echoEnergy J A B (echoFlow J ħ A B t x.1) :=
    rfl
  have h2 : echoEnergy Jc Cc C (clockView (coupledFlow J ħ A B Jc Cc C t x))
      = echoEnergy Jc Cc C (echoFlow Jc ħ Cc C t (clockView x)) := rfl
  rw [h1, h2, echoEnergy_echoFlow, echoEnergy_echoFlow]

end Dynamics

/-! ### Window arithmetic for a displacement in a band -/

/-- The write of value `1` ends: the mean growth `m t` reaches `1/3` plus the band `b`. -/
noncomputable def bandEmitEnd (m b : ℝ) : ℝ := (1 / 3 + b) / m

/-- The write of value `2` ends: the mean growth reaches `2/3` plus the band. -/
noncomputable def bandReturnEnd (m b : ℝ) : ℝ := (2 / 3 + b) / m

/-- The retention window: `(1/6 − 2b)/m`. -/
noncomputable def bandWindow (m b : ℝ) : ℝ := (1 / 6 - 2 * b) / m

theorem emitEnd_eq_bandEmitEnd (r l ω : ℝ) : emitEnd r l ω = bandEmitEnd (meanRate r l) (band r l ω) :=
  rfl

theorem returnEnd_eq_bandReturnEnd (r l ω : ℝ) :
    returnEnd r l ω = bandReturnEnd (meanRate r l) (band r l ω) := rfl

theorem senderWindow_eq_bandWindow (r l ω : ℝ) :
    senderWindow r l ω = bandWindow (meanRate r l) (band r l ω) := rfl

theorem bandWindow_nonneg {m b : ℝ} (hm : 0 < m) (hb : b ≤ 1 / 12) : 0 ≤ bandWindow m b :=
  div_nonneg (by linarith) hm.le

theorem bandEmitEnd_nonneg {m b : ℝ} (hm : 0 < m) (hb : 0 ≤ b) : 0 ≤ bandEmitEnd m b :=
  div_nonneg (by linarith) hm.le

theorem bandEmitEnd_add_window_lt {m b : ℝ} (hm : 0 < m) (hb : 0 ≤ b) :
    bandEmitEnd m b + bandWindow m b < bandReturnEnd m b := by
  unfold bandEmitEnd bandWindow bandReturnEnd
  rw [← add_div]
  exact div_lt_div_of_pos_right (by linarith) hm

theorem emitStart_le_bandEmitEnd {R m b : ℝ} (hR : 0 < R) (hm : 0 < m) (hmR : m ≤ R) (hb : 0 ≤ b) :
    emitStart R ≤ bandEmitEnd m b := by
  unfold emitStart bandEmitEnd
  rw [div_le_div_iff₀ (by positivity) hm]
  nlinarith

theorem returnStart_le_bandReturnEnd {R m b : ℝ} (hR : 0 < R) (hm : 0 < m) (hmR : m ≤ R)
    (hb : 0 ≤ b) : returnStart R ≤ bandReturnEnd m b := by
  unfold returnStart bandReturnEnd
  rw [div_le_div_iff₀ (by positivity) hm]
  nlinarith

/-- Through the first window a displacement in the band lies in `[1/3, 1/2]`. -/
theorem mem_emit_of_band {m b D t : ℝ} (hm : 0 < m) (hlow : m * t - b ≤ D) (hup : D ≤ m * t + b)
    (ht₁ : bandEmitEnd m b ≤ t) (ht₂ : t ≤ bandEmitEnd m b + bandWindow m b) :
    1 / 3 ≤ D ∧ D ≤ 1 / 2 := by
  have h1 := mul_le_mul_of_nonneg_left ht₁ hm.le
  have h2 := mul_le_mul_of_nonneg_left ht₂ hm.le
  have e1 : m * bandEmitEnd m b = 1 / 3 + b := by unfold bandEmitEnd; field_simp
  have e2 : m * bandWindow m b = 1 / 6 - 2 * b := by unfold bandWindow; field_simp
  rw [e1] at h1
  rw [mul_add, e1, e2] at h2
  constructor <;> linarith

/-- Through the second window a displacement in the band lies in `[2/3, 5/6]`. -/
theorem mem_return_of_band {m b D t : ℝ} (hm : 0 < m) (hlow : m * t - b ≤ D) (hup : D ≤ m * t + b)
    (ht₁ : bandReturnEnd m b ≤ t) (ht₂ : t ≤ bandReturnEnd m b + bandWindow m b) :
    2 / 3 ≤ D ∧ D ≤ 5 / 6 := by
  have h1 := mul_le_mul_of_nonneg_left ht₁ hm.le
  have h2 := mul_le_mul_of_nonneg_left ht₂ hm.le
  have e1 : m * bandReturnEnd m b = 2 / 3 + b := by unfold bandReturnEnd; field_simp
  have e2 : m * bandWindow m b = 1 / 6 - 2 * b := by unfold bandWindow; field_simp
  rw [e1] at h1
  rw [mul_add, e1, e2] at h2
  constructor <;> linarith

/-- The sender's drift sits in its band about the mean growth. -/
theorem senderDrift_mem_band {r l ω : ℝ} (hr : 0 ≤ r) (hl0 : 0 ≤ l) (hω : 0 < ω) (t : ℝ) :
    meanRate r l * t - band r l ω ≤ senderDrift r l ω t
      ∧ senderDrift r l ω t ≤ meanRate r l * t + band r l ω := by
  have hlow := senderDrift_lower hr hl0 hω t
  have hup := senderDrift_upper hr hl0 hω t
  have e1 : r * (t * (1 - l / 2) - l / (4 * ω)) = meanRate r l * t - band r l ω := by
    unfold meanRate band
    ring
  have e2 : r * (t * (1 - l / 2) + l / (4 * ω)) = meanRate r l * t + band r l ω := by
    unfold meanRate band
    ring
  exact ⟨e1 ▸ hlow, e2 ▸ hup⟩

theorem meanRate_nonneg {r l : ℝ} (hr : 0 ≤ r) (hl : l ≤ 1) : 0 ≤ meanRate r l := by
  unfold meanRate
  nlinarith

/-! ### The drift hand, for any mean rate and Rabi rate -/

/-- ★ **The drift never turns back**, for any `κ ≥ 0`: `x − sin x cos x` is non-decreasing. -/
theorem pointerDrift_monotone {κ ω : ℝ} (hκ : 0 ≤ κ) (hω : 0 < ω) : Monotone (pointerDrift κ ω) := by
  intro s t hst
  unfold pointerDrift
  have hsin := (abs_le.mp (Real.abs_sin_sub_sin_le (2 * (ω * t)) (2 * (ω * s)))).1
  have e1 : Real.sin (ω * t) * Real.cos (ω * t) = Real.sin (2 * (ω * t)) / 2 := by
    rw [Real.sin_two_mul]; ring
  have e2 : Real.sin (ω * s) * Real.cos (ω * s) = Real.sin (2 * (ω * s)) / 2 := by
    rw [Real.sin_two_mul]; ring
  have key : ω * s - Real.sin (ω * s) * Real.cos (ω * s)
      ≤ ω * t - Real.sin (ω * t) * Real.cos (ω * t) := by
    rw [e1, e2]
    have : |2 * (ω * t) - 2 * (ω * s)| = 2 * (ω * t) - 2 * (ω * s) :=
      abs_of_nonneg (by nlinarith)
    nlinarith [Real.abs_sin_sub_sin_le (2 * (ω * t)) (2 * (ω * s)),
      abs_le.mp (Real.abs_sin_sub_sin_le (2 * (ω * t)) (2 * (ω * s)))]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key hκ) (by positivity)

section DriftHand

variable {K : ℕ} {κ ω : ℝ} {q : LF4.KTorus}

/-- Over the horizon a hand prepared in the first half-arc has not wrapped. -/
theorem rep_driftHand (hK : 0 < K) (hq : q ∈ handReady K) (hκ : 0 < κ) (hω : 0 < ω) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ handHorizon K κ ω) :
    rep (pshift (pointerDrift κ ω t) q).1 = rep q.1 + pointerDrift κ ω t := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hhalf : 1 / (2 * (K : ℝ)) ≤ 1 / K := by
    rw [div_le_div_iff₀ (by positivity) hKr]
    linarith
  have hu := pointerDrift_upper hκ.le hω t
  have hb := band_at_handHorizon (K := K) hκ hω
  have hD : pointerDrift κ ω t ≤ 1 - 1 / K := by
    rw [← hb]
    exact hu.trans (mul_le_mul_of_nonneg_left (by linarith) hκ.le)
  have hD0 := pointerDrift_nonneg hκ.le hω ht0
  exact rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- ★★ **Ticks persist**, for any drift hand. -/
theorem driftHand_count_mono (hK : 0 < K) (hq : q ∈ handReady K) (hκ : 0 < κ) (hω : 0 < ω)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ handHorizon K κ ω) :
    handCount K (pshift (pointerDrift κ ω s) q) ≤ handCount K (pshift (pointerDrift κ ω t) q) := by
  unfold handCount
  rw [rep_driftHand hK hq hκ hω hs (by linarith), rep_driftHand hK hq hκ hω (by linarith) ht]
  exact Nat.sub_le_sub_right (Nat.ceil_mono (mul_le_mul_of_nonneg_left
    (by linarith [pointerDrift_monotone hκ.le hω hst]) (Nat.cast_nonneg K))) 1

/-- ★★ **The resolution bound**, for any drift hand: `|reading − t| ≤ τ_tick + 1/(2ω)`. -/
theorem abs_driftHand_reading_sub_le (hK : 0 < K) (hq : q ∈ handReady K) (hκ : 0 < κ) (hω : 0 < ω)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ handHorizon K κ ω) :
    |handReading K (tickTime K κ) (pshift (pointerDrift κ ω t) q) - t|
      ≤ tickTime K κ + 1 / (2 * ω) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set τ := tickTime K κ with hτ
  have hτ0 : 0 < τ := tickTime_pos hK hκ
  set D := pointerDrift κ ω t with hD
  set c := (handCount K (pshift D q) : ℝ) with hc
  have h1 : |c - K * D| ≤ 1 := by
    have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
    have hKhalf : (K : ℝ) * rep q.1 ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hr.2 hKr.le
      rwa [show (K : ℝ) * (1 / (2 * K)) = 1 / 2 by field_simp] at this
    have hD0 : 0 ≤ D := pointerDrift_nonneg hκ.le hω ht0
    rw [hc]
    unfold handCount
    rw [rep_driftHand hK hq hκ hω ht0 ht]
    set y := (K : ℝ) * (rep q.1 + D) with hy
    have hy0 : 0 < y := by rw [hy]; exact mul_pos hKr (by linarith [hr.1])
    have h1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_ceil_iff.2 hy0
    have hle := Nat.le_ceil y
    have hlt := Nat.ceil_lt_add_one hy0.le
    rw [Nat.cast_sub h1, Nat.cast_one, abs_le]
    have hyD : y = K * rep q.1 + K * D := by rw [hy]; ring
    constructor <;> nlinarith [mul_pos hKr hr.1]
  have h2 : |D - κ * t / 2| ≤ κ / (4 * ω) := by
    have hl := pointerDrift_lower hκ.le hω t
    have hu := pointerDrift_upper hκ.le hω t
    rw [← hD] at hl hu
    have e1 : κ * (t / 2 - 1 / (4 * ω)) = κ * t / 2 - κ / (4 * ω) := by ring
    have e2 : κ * (t / 2 + 1 / (4 * ω)) = κ * t / 2 + κ / (4 * ω) := by ring
    rw [e1] at hl
    rw [e2] at hu
    rw [abs_le]
    constructor <;> linarith
  have hτK : τ * K * κ = 2 := by rw [hτ, ← mul_tickTime hK hκ]; ring
  have e : handReading K τ (pshift D q) - t = τ * (c - K * D) + τ * K * (D - κ * t / 2) := by
    unfold handReading
    rw [← hc]
    linear_combination (t / 2) * hτK
  rw [e]
  calc |τ * (c - K * D) + τ * K * (D - κ * t / 2)|
      ≤ |τ * (c - K * D)| + |τ * K * (D - κ * t / 2)| := abs_add_le _ _
    _ = τ * |c - K * D| + τ * K * |D - κ * t / 2| := by
        rw [abs_mul, abs_mul, abs_of_pos hτ0, abs_of_pos (mul_pos hτ0 hKr)]
    _ ≤ τ * 1 + τ * K * (κ / (4 * ω)) := by gcongr
    _ = τ + 1 / (2 * ω) := by
        rw [mul_one]
        congr 1
        rw [hτ]
        unfold tickTime
        field_simp
        ring

/-- ★★ **Before its start, tick `n` has not been written**, for any drift hand. -/
theorem driftHand_before_tick (hK : 0 < K) (hq : q ∈ handReady K) (hκ : 0 < κ) (hω : 0 < ω)
    {n : ℕ} (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < tickStart K κ n) :
    handCount K (pshift (pointerDrift κ ω t) q) < n := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hnK' : (n : ℝ) + 1 ≤ K := by exact_mod_cast hnK
  have hD0 := pointerDrift_nonneg hκ.le hω ht0
  have hD : pointerDrift κ ω t < (n : ℝ) / K - 1 / (2 * K) := by
    calc pointerDrift κ ω t ≤ κ * t := pointerDrift_le hκ.le hω ht0
      _ < κ * tickStart K κ n := mul_lt_mul_of_pos_left ht hκ
      _ = (n : ℝ) / K - 1 / (2 * K) := by unfold tickStart; field_simp
  have hsum : rep q.1 + pointerDrift κ ω t < (n : ℝ) / K := by linarith [hr.2]
  have hnK2 : (n : ℝ) / K ≤ 1 := by
    rw [div_le_one hKr]
    linarith
  have hrep : rep (pshift (pointerDrift κ ω t) q).1 = rep q.1 + pointerDrift κ ω t :=
    rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith⟩
  unfold handCount
  rw [hrep]
  have hceil : ⌈(K : ℝ) * (rep q.1 + pointerDrift κ ω t)⌉₊ ≤ n := by
    rw [Nat.ceil_le]
    have := mul_lt_mul_of_pos_left hsum hKr
    rw [mul_div_cancel₀ _ hKr.ne'] at this
    exact this.le
  omega

/-- ★★ **Through its window, tick `n` displays**, for any drift hand. -/
theorem driftHand_at_tick (hK : 0 < K) (hq : q ∈ handReady K) (hκ : 0 < κ) (hω : 0 < ω) {n : ℕ}
    (hnK : n + 1 ≤ K) {t : ℝ} (ht₁ : tickEnd K κ ω n ≤ t)
    (ht₂ : t ≤ tickEnd K κ ω n + tickWindow K κ ω) :
    handCount K (pshift (pointerDrift κ ω t) q) = n := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hnK' : (n : ℝ) + 1 ≤ K := by exact_mod_cast hnK
  have hl := pointerDrift_lower hκ.le hω t
  have hu := pointerDrift_upper hκ.le hω t
  have hDl : (n : ℝ) / K ≤ pointerDrift κ ω t := by
    rw [← band_at_tickEnd hK hκ hω n]
    exact (mul_le_mul_of_nonneg_left (by linarith) hκ.le).trans hl
  have hDu : pointerDrift κ ω t ≤ (n : ℝ) / K + 1 / (2 * K) := by
    rw [← band_at_tickWindow_end hK hκ hω n]
    exact hu.trans (mul_le_mul_of_nonneg_left (by linarith) hκ.le)
  have hD0 : 0 ≤ pointerDrift κ ω t := le_trans (by positivity) hDl
  have hwrap : rep q.1 + pointerDrift κ ω t ≤ 1 := by
    have : (n : ℝ) / K + 1 / K ≤ 1 := by
      rw [← add_div, div_le_one hKr]
      exact hnK'
    have hhalf : 1 / (2 * (K : ℝ)) + 1 / (2 * K) = 1 / K := by field_simp; ring
    linarith [hr.2]
  rw [handCount_eq_iff hK, rep_pshift_of_mem _ _ ⟨by linarith [hr.1], hwrap⟩, mem_Ioc]
  have hhalf : 1 / (2 * (K : ℝ)) + 1 / (2 * K) = 1 / K := by field_simp; ring
  constructor
  · linarith [hr.1]
  · rw [show ((n : ℝ) + 1) / K = n / K + 1 / K by ring]
    linarith [hr.2]

end DriftHand

/-! ### The coupled constants -/

section Constants

variable (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (Cc C : PointerCoupling)

/-- Pointer `A`'s top rate under the coupling: both carriers turn it. -/
noncomputable def coupledRate (qA : LF4.KTorus) : ℝ := senderRate A ħ qA + senderRate Cc ħ qA

/-- Pointer `A`'s mean rate under the coupling: the echo's `r_A(1 − λ/2)` plus the clock's. -/
noncomputable def coupledMean (qA qB qh : LF4.KTorus) : ℝ :=
  meanRate (senderRate A ħ qA) (echoLoss A B J qA qB)
    + meanRate (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh)

/-- Pointer `A`'s band under the coupling: the echo's plus the clock's. -/
noncomputable def coupledBand (qA qB qh : LF4.KTorus) : ℝ :=
  band (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    + band (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh)

/-- The coupled clock's mean rate `κ_c = r λ_c`: the hand of a two-site carrier detuned at `A` by
the echo's pointer. -/
noncomputable def clockRate (qA qh : LF4.KTorus) : ℝ := receiverDrift Cc C Jc ħ qA qh

/-- The coupled clock's Rabi rate. -/
noncomputable def clockFreq (qA qh : LF4.KTorus) : ℝ := echoRate Cc C Jc ħ qA qh

end Constants

/-! ### The coupled device read at its preparation -/

section Prepared

variable {J ħ : ℝ} (A B : PointerCoupling) {Jc : ℝ} (Cc C : PointerCoupling)

/-- The preparation: both carriers as message `1`, the pointers at `q_A`, `q_B`, the hand at
`q_h`. -/
noncomputable def coupledPrep (qA qB qh : LF4.KTorus) : ClockEchoArena :=
  ((msgPoint 1, (qA, qB)), (msgPoint 1, qh))

/-- ★★ **Pointer `A` under the coupling**: the echo's drift plus the clock's — reading the clock
moves the echo's register. -/
theorem coupledFlow_pointerA (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (qA qB qh : LF4.KTorus)
    (t : ℝ) :
    (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1.2.1
      = pshift (senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t
          + senderDrift (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh) t)
          qA := by
  show pshift (echoAmountA Jc ħ Cc C t (msgPoint 1, (qA, qh)))
      (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.1 = _
  rw [echoFlow_msgPoint_one_pointerA A B hJ hħ, echoAmountA_msgPoint_one Cc C hJc hħ, pshift_add,
    add_comm]

/-- Pointer `B` is the echo's alone. -/
theorem coupledFlow_pointerB (t : ℝ) (qA qB qh : LF4.KTorus) :
    (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1.2.2
      = (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.2 := rfl

/-- ★ **The hand under the coupling**: a drift hand with the coupled constants. -/
theorem coupledFlow_hand (hJc : 0 < Jc) (hħ : 0 < ħ) (qA qB qh : LF4.KTorus) (t : ℝ) :
    (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).2.2
      = pshift (pointerDrift (clockRate ħ Jc Cc C qA qh) (clockFreq ħ Jc Cc C qA qh) t) qh :=
  echoFlow_msgPoint_one_pointerB Cc C hJc hħ qA qh t

variable {qA qB qh : LF4.KTorus}

/-- The coupled sender's displacement is in the coupled band, at most the top rate times `t`, and
non-negative. -/
theorem coupledDrift_bounds (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) {t : ℝ} (ht : 0 ≤ t) :
    let D := senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t
      + senderDrift (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh) t
    coupledMean J ħ A B Jc Cc C qA qB qh * t - coupledBand J ħ A B Jc Cc C qA qB qh ≤ D
      ∧ D ≤ coupledMean J ħ A B Jc Cc C qA qB qh * t + coupledBand J ħ A B Jc Cc C qA qB qh
      ∧ 0 ≤ D ∧ D ≤ coupledRate ħ A Cc qA * t := by
  intro D
  have hl0 := (echoLoss_pos A B hJ qA qB).le
  have hl1 := echoLoss_le_one A B hJ qA qB
  have hω := echoRate_pos A B hJ hħ qA qB
  have hl0c := (echoLoss_pos Cc C hJc qA qh).le
  have hl1c := echoLoss_le_one Cc C hJc qA qh
  have hωc := echoRate_pos Cc C hJc hħ qA qh
  have he := senderDrift_mem_band hr.le hl0 hω t
  have hc := senderDrift_mem_band hrc hl0c hωc t
  have he0 := senderDrift_nonneg hr.le hl0 hl1 hω ht
  have hc0 := senderDrift_nonneg hrc hl0c hl1c hωc ht
  have he1 := senderDrift_le hr.le hl0 hω ht
  have hc1 := senderDrift_le hrc hl0c hωc ht
  unfold coupledMean coupledBand coupledRate
  refine ⟨by linarith [he.1, hc.1], by linarith [he.2, hc.2], by linarith, by linarith⟩

theorem coupledMean_pos (hJ : 0 < J) (hJc : 0 < Jc) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) : 0 < coupledMean J ħ A B Jc Cc C qA qB qh := by
  unfold coupledMean
  have := meanRate_pos hr (echoLoss_le_one A B hJ qA qB)
  have := meanRate_nonneg hrc (echoLoss_le_one Cc C hJc qA qh)
  linarith

theorem coupledMean_le (hJ : 0 < J) (hJc : 0 < Jc) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) : coupledMean J ħ A B Jc Cc C qA qB qh ≤ coupledRate ħ A Cc qA := by
  unfold coupledMean coupledRate
  have := meanRate_le hr.le (echoLoss_pos A B hJ qA qB).le
  have := meanRate_le hrc (echoLoss_pos Cc C hJc qA qh).le
  linarith

theorem coupledBand_nonneg (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) : 0 ≤ coupledBand J ħ A B Jc Cc C qA qB qh := by
  unfold coupledBand
  have := band_nonneg hr.le (echoLoss_pos A B hJ qA qB).le (echoRate_pos A B hJ hħ qA qB)
  have := band_nonneg hrc (echoLoss_pos Cc C hJc qA qh).le (echoRate_pos Cc C hJc hħ qA qh)
  linarith

/-- Before the coupled emission start pointer `A` reads `0`. -/
theorem coupled_before_emit (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < emitStart (coupledRate ħ A Cc qA)) :
    senderRead (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1 = 0 := by
  unfold senderRead
  rw [coupledFlow_pointerA A B Cc C hJ hJc hħ]
  obtain ⟨-, -, h0, h1⟩ := coupledDrift_bounds (qB := qB) (qh := qh) A B Cc C hJ hJc hħ hr hrc ht0
  have hR : 0 < coupledRate ħ A Cc qA := by unfold coupledRate; linarith
  have hE : coupledRate ħ A Cc qA * emitStart (coupledRate ħ A Cc qA) = 1 / 6 := by
    unfold emitStart; field_simp
  have := mul_lt_mul_of_pos_left ht hR
  exact thirds_pshift_ready_zero hqA h0 (by linarith)

/-- Through the coupled emission window pointer `A` reads `1`. -/
theorem coupled_emitted (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA) {t : ℝ}
    (ht₁ : bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh) ≤ t)
    (ht₂ : t ≤ bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
      + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)) :
    senderRead (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1 = 1 := by
  unfold senderRead
  rw [coupledFlow_pointerA A B Cc C hJ hJc hħ]
  have hm := coupledMean_pos A B Cc C (qB := qB) (qh := qh) hJ hJc hr hrc
  have ht0 : 0 ≤ t := (bandEmitEnd_nonneg hm (coupledBand_nonneg A B Cc C hJ hJc hħ hr hrc)).trans ht₁
  obtain ⟨hl, hu, -, -⟩ := coupledDrift_bounds (qB := qB) (qh := qh) A B Cc C hJ hJc hħ hr hrc ht0
  obtain ⟨h0, h1⟩ := mem_emit_of_band hm hl hu ht₁ ht₂
  exact thirds_pshift_ready_one hqA h0 h1

/-- Before the coupled return start pointer `A` does not read `2`. -/
theorem coupled_before_return (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < returnStart (coupledRate ħ A Cc qA)) :
    senderRead (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1 ≠ 2 := by
  unfold senderRead
  rw [coupledFlow_pointerA A B Cc C hJ hJc hħ]
  obtain ⟨-, -, h0, h1⟩ := coupledDrift_bounds (qB := qB) (qh := qh) A B Cc C hJ hJc hħ hr hrc ht0
  have hR : 0 < coupledRate ħ A Cc qA := by unfold coupledRate; linarith
  have hE : coupledRate ħ A Cc qA * returnStart (coupledRate ħ A Cc qA) = 1 / 2 := by
    unfold returnStart; field_simp
  have := mul_lt_mul_of_pos_left ht hR
  exact thirds_pshift_ready_ne_two hqA h0 (by linarith)

/-- Through the coupled return window pointer `A` reads `2`. -/
theorem coupled_returned (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA) {t : ℝ}
    (ht₁ : bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh) ≤ t)
    (ht₂ : t ≤ bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
      + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)) :
    senderRead (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1 = 2 := by
  unfold senderRead
  rw [coupledFlow_pointerA A B Cc C hJ hJc hħ]
  have hm := coupledMean_pos A B Cc C (qB := qB) (qh := qh) hJ hJc hr hrc
  have hb := coupledBand_nonneg A B Cc C (qB := qB) (qh := qh) hJ hJc hħ hr hrc
  have ht0 : 0 ≤ t := by
    have : 0 ≤ bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh)
        (coupledBand J ħ A B Jc Cc C qA qB qh) := div_nonneg (by linarith) hm.le
    linarith
  obtain ⟨hl, hu, -, -⟩ := coupledDrift_bounds (qB := qB) (qh := qh) A B Cc C hJ hJc hħ hr hrc ht0
  obtain ⟨h0, h1⟩ := mem_return_of_band hm hl hu ht₁ ht₂
  exact thirds_pshift_ready_two hqA h0 h1

theorem coupledRate_pos (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA) :
    0 < coupledRate ħ A Cc qA := by
  unfold coupledRate
  linarith

end Prepared

/-! ### The writes on the coupled arena -/

section Records

variable {J ħ : ℝ} (A B : PointerCoupling) {Jc : ℝ} (Cc C : PointerCoupling)
  {qA qB qh : LF4.KTorus} {K : ℕ}

/-- ★★ **The emission record under the coupling**: `A`'s first arc, now written by the echo's
carrier and the clock's together, with the coupled windows. -/
noncomputable def coupledEmission (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hqh : qh ∈ handReady K) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) (hslow : coupledBand J ħ A B Jc Cc C qA qB qh ≤ 1 / 12) :
    ActualOccurrence ClockEchoArena (Fin 3) 2 where
  evolve := coupledEvolve J ħ A B Jc Cc C
  evolve_self := coupledEvolve_self J ħ A B Jc Cc C
  evolve_comp := coupledEvolve_comp J ħ A B Jc Cc C
  measurable_evolve := measurable_coupledEvolve J ħ A B Jc Cc C
  readout := fun x => senderRead x.1
  measurable_readout := measurable_senderRead.comp measurable_fst
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := coupledPrep qA qB qh
  prep_mem := ⟨⟨hqA, hqB⟩, hqh⟩
  site := {0}
  start := 0
  value := 1
  writeStart := emitStart (coupledRate ħ A Cc qA)
  writeEnd := bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
  window := bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
  isWrite :=
    { start_le := emitStart_nonneg (coupledRate_pos A Cc hr hrc)
      interval := emitStart_le_bandEmitEnd (coupledRate_pos A Cc hr hrc)
        (coupledMean_pos A B Cc C hJ hJc hr hrc) (coupledMean_le A B Cc C hJ hJc hr hrc)
        (coupledBand_nonneg A B Cc C hJ hJc hħ hr hrc)
      window_nonneg := bandWindow_nonneg (coupledMean_pos A B Cc C hJ hJc hr hrc) hslow
      before := fun t ht0 ht => by
        show senderRead (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).1 ≠ 1
        rw [sub_zero, coupled_before_emit A B Cc C hJ hJc hħ hqA hr hrc ht0 ht]
        decide
      holds := fun t ht₁ ht₂ => by
        show senderRead (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).1 = 1
        rw [sub_zero]
        exact coupled_emitted A B Cc C hJ hJc hħ hqA hr hrc ht₁ ht₂ }

/-- ★★ **The return record under the coupling**: `A`'s second arc, with the coupled windows. -/
noncomputable def coupledReturn (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hqh : qh ∈ handReady K) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) (hslow : coupledBand J ħ A B Jc Cc C qA qB qh ≤ 1 / 12) :
    ActualOccurrence ClockEchoArena (Fin 3) 2 where
  evolve := coupledEvolve J ħ A B Jc Cc C
  evolve_self := coupledEvolve_self J ħ A B Jc Cc C
  evolve_comp := coupledEvolve_comp J ħ A B Jc Cc C
  measurable_evolve := measurable_coupledEvolve J ħ A B Jc Cc C
  readout := fun x => senderRead x.1
  measurable_readout := measurable_senderRead.comp measurable_fst
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := coupledPrep qA qB qh
  prep_mem := ⟨⟨hqA, hqB⟩, hqh⟩
  site := {0}
  start := 0
  value := 2
  writeStart := returnStart (coupledRate ħ A Cc qA)
  writeEnd := bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
  window := bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
  isWrite :=
    { start_le := returnStart_nonneg (coupledRate_pos A Cc hr hrc)
      interval := returnStart_le_bandReturnEnd (coupledRate_pos A Cc hr hrc)
        (coupledMean_pos A B Cc C hJ hJc hr hrc) (coupledMean_le A B Cc C hJ hJc hr hrc)
        (coupledBand_nonneg A B Cc C hJ hJc hħ hr hrc)
      window_nonneg := bandWindow_nonneg (coupledMean_pos A B Cc C hJ hJc hr hrc) hslow
      before := fun t ht0 ht => by
        show senderRead (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).1 ≠ 2
        rw [sub_zero]
        exact coupled_before_return A B Cc C hJ hJc hħ hqA hr hrc ht0 ht
      holds := fun t ht₁ ht₂ => by
        show senderRead (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).1 = 2
        rw [sub_zero]
        exact coupled_returned A B Cc C hJ hJc hħ hqA hr hrc ht₁ ht₂ }

/-- ★★ **The reception record under the coupling**: pointer `B` is the echo's alone, so #199's
windows stand unchanged. -/
noncomputable def coupledReception (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hqh : qh ∈ handReady K) (hκ : 0 < receiverDrift A B J ħ qA qB)
    (hslow : 3 * receiverDrift A B J ħ qA qB ≤ 2 * echoRate A B J ħ qA qB) :
    ActualOccurrence ClockEchoArena Bool 2 where
  evolve := coupledEvolve J ħ A B Jc Cc C
  evolve_self := coupledEvolve_self J ħ A B Jc Cc C
  evolve_comp := coupledEvolve_comp J ħ A B Jc Cc C
  measurable_evolve := measurable_coupledEvolve J ħ A B Jc Cc C
  readout := fun x => receiverRead x.1
  measurable_readout := measurable_receiverRead.comp measurable_fst
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := coupledPrep qA qB qh
  prep_mem := ⟨⟨hqA, hqB⟩, hqh⟩
  site := {1}
  start := 0
  value := true
  writeStart := writeStart (receiverDrift A B J ħ qA qB)
  writeEnd := writeEnd (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
  window := retention (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
  isWrite :=
    { start_le := (receptionRecord A B hJ hħ hqA hqB hκ hslow).isWrite.start_le
      interval := (receptionRecord A B hJ hħ hqA hqB hκ hslow).isWrite.interval
      window_nonneg := (receptionRecord A B hJ hħ hqA hqB hκ hslow).isWrite.window_nonneg
      before := fun t ht0 ht => by
        show receiverRead (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).1 ≠ true
        rw [sub_zero]
        have h := receiver_before A B hJ hħ qA hqB hκ ht0 ht
        unfold receiverRead at h ⊢
        rw [coupledFlow_pointerB, h]
        decide
      holds := fun t ht₁ ht₂ => by
        show receiverRead (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).1 = true
        rw [sub_zero]
        have h := receiver_received A B hJ hħ qA hqB hκ ht₁ ht₂
        unfold receiverRead at h ⊢
        rw [coupledFlow_pointerB, h] }

/-- ★★ **Tick `n` of the coupled clock**: a write by the clock's carrier, with the coupled
constants — the clock's rate now depends on the echo's conserved angle `θ₂ᴬ`. -/
noncomputable def coupledTick (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hK : 0 < K) (hqh : qh ∈ handReady K)
    (hκc : 0 < clockRate ħ Jc Cc C qA qh)
    (hslowc : K * clockRate ħ Jc Cc C qA qh ≤ clockFreq ħ Jc Cc C qA qh) {n : ℕ} (hn1 : 1 ≤ n)
    (hnK : n + 1 ≤ K) : ActualOccurrence ClockEchoArena ℕ 2 where
  evolve := coupledEvolve J ħ A B Jc Cc C
  evolve_self := coupledEvolve_self J ħ A B Jc Cc C
  evolve_comp := coupledEvolve_comp J ħ A B Jc Cc C
  measurable_evolve := measurable_coupledEvolve J ħ A B Jc Cc C
  readout := clockEchoLabel K
  measurable_readout := (measurable_handCount K).comp measurable_snd.snd
  ready := clockEchoReady K
  measurableSet_ready := measurableSet_clockEchoReady K
  prep := coupledPrep qA qB qh
  prep_mem := ⟨⟨hqA, hqB⟩, hqh⟩
  site := {0}
  start := 0
  value := n
  writeStart := tickStart K (clockRate ħ Jc Cc C qA qh) n
  writeEnd := tickEnd K (clockRate ħ Jc Cc C qA qh) (clockFreq ħ Jc Cc C qA qh) n
  window := tickWindow K (clockRate ħ Jc Cc C qA qh) (clockFreq ħ Jc Cc C qA qh)
  isWrite :=
    { start_le := tickStart_nonneg hK hκc hn1
      interval := tickStart_le_tickEnd hK hκc (echoRate_pos Cc C hJc hħ qA qh) n
      window_nonneg := tickWindow_nonneg hK hκc hslowc
      before := fun t ht0 ht => by
        show handCount K (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).2.2 ≠ n
        rw [sub_zero, coupledFlow_hand A B Cc C hJc hħ]
        exact (driftHand_before_tick hK hqh hκc (echoRate_pos Cc C hJc hħ qA qh) hn1 hnK ht0
          ht).ne
      holds := fun t ht₁ ht₂ => by
        show handCount K (coupledFlow J ħ A B Jc Cc C (t - 0) (coupledPrep qA qB qh)).2.2 = n
        rw [sub_zero, coupledFlow_hand A B Cc C hJc hħ]
        exact driftHand_at_tick hK hqh hκc (echoRate_pos Cc C hJc hħ qA qh) hnK ht₁ ht₂ }

end Records

/-! ### The readings, the budget and the coupling's term -/

section Radar

variable {J ħ : ℝ} (A B : PointerCoupling) {Jc : ℝ} (Cc C : PointerCoupling)
  {qA qB qh : LF4.KTorus} {K : ℕ}

/-- **The coupled clock's reading at time `t`**: the hand's count times the derived calibration
`τ_tick = 2/(Kκ_c)`. -/
noncomputable def coupledReadingAt (ħ Jc : ℝ) (Cc C : PointerCoupling) (K : ℕ)
    (qA qh : LF4.KTorus) (t : ℝ) : ℝ :=
  handReading K (tickTime K (clockRate ħ Jc Cc C qA qh))
    (pshift (pointerDrift (clockRate ħ Jc Cc C qA qh) (clockFreq ħ Jc Cc C qA qh) t) qh)

/-- The coupled clock's resolution `τ_tick + 1/(2ω_c)`. -/
noncomputable def coupledResolution (ħ Jc : ℝ) (Cc C : PointerCoupling) (K : ℕ)
    (qA qh : LF4.KTorus) : ℝ :=
  tickTime K (clockRate ħ Jc Cc C qA qh) + 1 / (2 * clockFreq ħ Jc Cc C qA qh)

/-- The coupled clock's horizon. -/
noncomputable def coupledHorizon (ħ Jc : ℝ) (Cc C : PointerCoupling) (K : ℕ)
    (qA qh : LF4.KTorus) : ℝ :=
  handHorizon K (clockRate ħ Jc Cc C qA qh) (clockFreq ħ Jc Cc C qA qh)

theorem coupledReadingAt_mono (hJc : 0 < Jc) (hħ : 0 < ħ) (hK : 0 < K) (hqh : qh ∈ handReady K)
    (hκc : 0 < clockRate ħ Jc Cc C qA qh) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ coupledHorizon ħ Jc Cc C K qA qh) :
    coupledReadingAt ħ Jc Cc C K qA qh s ≤ coupledReadingAt ħ Jc Cc C K qA qh t :=
  mul_le_mul_of_nonneg_right
    (Nat.cast_le.2 (driftHand_count_mono hK hqh hκc (echoRate_pos Cc C hJc hħ qA qh) hs hst ht))
    (tickTime_pos hK hκc).le

/-- **The measured readings** of the coupled clock at `t₁ ≤ t₂` within its horizon. -/
noncomputable def coupledReadings (hJc : 0 < Jc) (hħ : 0 < ħ) (hK : 0 < K) (hqh : qh ∈ handReady K)
    (hκc : 0 < clockRate ħ Jc Cc C qA qh) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ coupledHorizon ħ Jc Cc C K qA qh) : RadarReadings :=
  ⟨coupledReadingAt ħ Jc Cc C K qA qh t₁, coupledReadingAt ħ Jc Cc C K qA qh t₂,
    coupledReadingAt_mono Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂⟩

/-- **The coupling's term**: how far the coupling moves the return record's completion,
`|returnEnd_coupled − returnEnd_echo|`. -/
noncomputable def couplingTerm (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (Cc C : PointerCoupling)
    (qA qB qh : LF4.KTorus) : ℝ :=
  |bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
    - returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)|

/-- **The coupled round-trip budget**: #202's budget with the coupled clock's resolution, the
coupled emission window, and one more term — the coupling's shift of the return record. -/
noncomputable def coupledBudget (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (Cc C : PointerCoupling)
    (K : ℕ) (qA qB qh : LF4.KTorus) : ℝ :=
  coupledResolution ħ Jc Cc C K qA qh
    + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
    + bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
    + couplingTerm J ħ A B Jc Cc C qA qB qh
    + |echoReturnDelay A B J ħ qA qB| + 2 * transferError J ħ (echoDetuning A B qA qB)

/-- ★★ **The coupling's term, explicitly**: the return record's completion moves by
`(b_c − m_c · returnEnd)/m`, where `m_c`, `b_c` are the clock carrier's mean rate and band at `A`
and `m` the coupled mean rate — so it is bounded by `(b_c + m_c · returnEnd)/m`. -/
theorem couplingTerm_le (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hrc : 0 ≤ senderRate Cc ħ qA) :
    couplingTerm J ħ A B Jc Cc C qA qB qh
      ≤ (band (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh)
          + meanRate (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh)
            * returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
        / coupledMean J ħ A B Jc Cc C qA qB qh := by
  have hm := coupledMean_pos A B Cc C (qB := qB) (qh := qh) hJ hJc hr hrc
  have hμ := meanRate_pos hr (echoLoss_le_one A B hJ qA qB)
  have he := meanRate_mul_returnEnd (ω := echoRate A B J ħ qA qB) hr (echoLoss_le_one A B hJ qA qB)
  have hbc := band_nonneg hrc (echoLoss_pos Cc C hJc qA qh).le (echoRate_pos Cc C hJc hħ qA qh)
  have hmc := meanRate_nonneg hrc (echoLoss_le_one Cc C hJc qA qh)
  have hR := (returnStart_nonneg hr).trans (returnStart_le_returnEnd hr
    (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB))
  set m := coupledMean J ħ A B Jc Cc C qA qB qh with hmdef
  set R := returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  set mc := meanRate (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh)
  set bc := band (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh)
  have hshift : bandReturnEnd m (coupledBand J ħ A B Jc Cc C qA qB qh) - R = (bc - mc * R) / m := by
    have hmR : m * R = 2 / 3 + band (senderRate A ħ qA) (echoLoss A B J qA qB)
        (echoRate A B J ħ qA qB) + mc * R := by
      rw [hmdef]
      unfold coupledMean
      rw [add_mul, he]
    unfold bandReturnEnd coupledBand
    field_simp
    linarith
  unfold couplingTerm
  rw [hshift, abs_div, abs_of_pos hm]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by
    rw [abs_of_nonneg hbc, abs_of_nonneg (mul_nonneg hmc hR)])) hm.le

/-- ★★ **The emission timestamp is within the coupled budget of `0`.** -/
theorem abs_coupledReadings_emit_sub_le (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hK : 0 < K)
    (hqh : qh ∈ handReady K) (hκc : 0 < clockRate ħ Jc Cc C qA qh) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ coupledHorizon ħ Jc Cc C K qA qh)
    (hemit : t₁ ≤ bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)) :
    |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).emit - 0|
      ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh := by
  show |coupledReadingAt ħ Jc Cc C K qA qh t₁ - 0| ≤ _
  rw [sub_zero]
  have h1 : |coupledReadingAt ħ Jc Cc C K qA qh t₁ - t₁| ≤ coupledResolution ħ Jc Cc C K qA qh :=
    abs_driftHand_reading_sub_le hK hqh hκc (echoRate_pos Cc C hJc hħ qA qh) h₁ (h₁₂.trans h₂)
  have h2 : |t₁| ≤ bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh)
      (coupledBand J ħ A B Jc Cc C qA qB qh)
      + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh) := by
    rw [abs_of_nonneg h₁]
    exact hemit
  have h3 := abs_nonneg (echoReturnDelay A B J ħ qA qB)
  have h4 := transferError_nonneg hJ hħ (echoDetuning A B qA qB)
  have h5 : 0 ≤ couplingTerm J ħ A B Jc Cc C qA qB qh := abs_nonneg _
  calc |coupledReadingAt ħ Jc Cc C K qA qh t₁|
      = |(coupledReadingAt ħ Jc Cc C K qA qh t₁ - t₁) + t₁| := by rw [sub_add_cancel]
    _ ≤ |coupledReadingAt ħ Jc Cc C K qA qh t₁ - t₁| + |t₁| := abs_add_le _ _
    _ ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh := by
        unfold coupledBudget
        linarith

/-- ★★ **The return timestamp is within the coupled budget of `2τ_hop`.** -/
theorem abs_coupledReadings_ret_sub_le (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hK : 0 < K)
    (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA) (hqh : qh ∈ handReady K) (hκc : 0 < clockRate ħ Jc Cc C qA qh) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ coupledHorizon ħ Jc Cc C K qA qh)
    (hret : bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        ≤ t₂
      ∧ t₂ ≤ bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)) :
    |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).ret - roundTrip J ħ|
      ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh := by
  show |coupledReadingAt ħ Jc Cc C K qA qh t₂ - roundTrip J ħ| ≤ _
  set m := coupledMean J ħ A B Jc Cc C qA qB qh
  set b := coupledBand J ħ A B Jc Cc C qA qB qh
  set R := returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  set Δ := echoDetuning A B qA qB
  have h1 : |coupledReadingAt ħ Jc Cc C K qA qh t₂ - t₂| ≤ coupledResolution ħ Jc Cc C K qA qh :=
    abs_driftHand_reading_sub_le hK hqh hκc (echoRate_pos Cc C hJc hħ qA qh) (by linarith) h₂
  have h2 : |t₂ - bandReturnEnd m b| ≤ bandWindow m b := by
    rw [abs_le]
    constructor <;> linarith [hret.1, hret.2]
  have h3 : |R - detunedRoundTrip J ħ Δ| = |echoReturnDelay A B J ħ qA qB| := rfl
  have h4 := abs_detunedRoundTrip_sub_roundTrip_le hJ hħ Δ
  have h5 : |bandReturnEnd m b - R| = couplingTerm J ħ A B Jc Cc C qA qB qh := rfl
  have hE : 0 ≤ bandEmitEnd m b :=
    bandEmitEnd_nonneg (coupledMean_pos A B Cc C hJ hJc hr hrc)
      (coupledBand_nonneg A B Cc C hJ hJc hħ hr hrc)
  calc |coupledReadingAt ħ Jc Cc C K qA qh t₂ - roundTrip J ħ|
      ≤ |coupledReadingAt ħ Jc Cc C K qA qh t₂ - t₂| + |t₂ - roundTrip J ħ| := abs_sub_le _ _ _
    _ ≤ |coupledReadingAt ħ Jc Cc C K qA qh t₂ - t₂|
        + (|t₂ - bandReturnEnd m b| + |bandReturnEnd m b - roundTrip J ħ|) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ |coupledReadingAt ħ Jc Cc C K qA qh t₂ - t₂|
        + (|t₂ - bandReturnEnd m b| + (|bandReturnEnd m b - R| + |R - roundTrip J ħ|)) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ |coupledReadingAt ħ Jc Cc C K qA qh t₂ - t₂|
        + (|t₂ - bandReturnEnd m b| + (|bandReturnEnd m b - R|
          + (|R - detunedRoundTrip J ħ Δ| + |detunedRoundTrip J ħ Δ - roundTrip J ħ|))) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh := by
        rw [h3, h5]
        unfold coupledBudget
        linarith

/-! ### The decoupled limit -/

theorem senderRate_eq_zero_of_g {P : PointerCoupling} (hg : P.g = 0) (ħ : ℝ) (q : LF4.KTorus) :
    senderRate P ħ q = 0 := by
  unfold senderRate rateAt
  rw [hg]
  ring

theorem detuningAt_eq_zero_of_g {P : PointerCoupling} (hg : P.g = 0) (φ : AddCircle (1 : ℝ)) :
    detuningAt P.g P.periodic φ = 0 := by
  unfold detuningAt
  rw [hg, zero_mul]

/-- At zero coupling the coupled clock's mean rate is #201's. -/
theorem clockRate_of_g_eq_zero (hg : Cc.g = 0) :
    clockRate ħ Jc Cc C qA qh = handRate Jc ħ C.g C.periodic qh := by
  unfold clockRate receiverDrift echoLoss echoDetuning handRate driftRate
  rw [detuningAt_eq_zero_of_g hg, sub_zero]

/-- At zero coupling the coupled clock's Rabi rate is #201's. -/
theorem clockFreq_of_g_eq_zero (hg : Cc.g = 0) :
    clockFreq ħ Jc Cc C qA qh = handFreq Jc ħ C.g C.periodic qh := by
  unfold clockFreq echoRate echoDetuning handFreq
  rw [detuningAt_eq_zero_of_g hg, sub_zero]

/-- ★★ **The decoupled limit**: at zero coupling the coupled budget is #202's budget exactly — the
coupling term vanishes and every window is #199's and #201's. -/
theorem coupledBudget_of_g_eq_zero (hg : Cc.g = 0) :
    coupledBudget J ħ A B Jc Cc C K qA qB qh = clockEchoBudget A B J ħ qA qB Jc C K qh := by
  have hs := senderRate_eq_zero_of_g hg ħ qA
  have hm : coupledMean J ħ A B Jc Cc C qA qB qh
      = meanRate (senderRate A ħ qA) (echoLoss A B J qA qB) := by
    unfold coupledMean
    rw [hs]
    unfold meanRate
    ring
  have hb : coupledBand J ħ A B Jc Cc C qA qB qh
      = band (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) := by
    unfold coupledBand
    rw [hs]
    unfold band
    ring
  unfold coupledBudget couplingTerm coupledResolution clockEchoBudget clockResolution
  rw [hm, hb, clockRate_of_g_eq_zero Cc C hg, clockFreq_of_g_eq_zero Cc C hg,
    ← returnEnd_eq_bandReturnEnd, sub_self, abs_zero, add_zero]
  rfl

/-! ### The coupling's effect on the clock's constants -/

/-- The Rabi frequency is `1/2`-Lipschitz in the detuning. -/
theorem abs_rabiFreq_sub_le (J x y : ℝ) : |rabiFreq J x - rabiFreq J y| ≤ |x - y| / 2 := by
  set a := rabiFreq J x with ha
  set b := rabiFreq J y with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = J ^ 2 + (x / 2) ^ 2 := rabiFreq_sq J x
  have hb2 : b ^ 2 = J ^ 2 + (y / 2) ^ 2 := rabiFreq_sq J y
  have hxa : |x| ≤ 2 * a := by
    have : |x / 2| ≤ a := Real.abs_le_sqrt (by nlinarith [sq_nonneg J])
    rw [abs_div, abs_two] at this
    linarith
  have hyb : |y| ≤ 2 * b := by
    have : |y / 2| ≤ b := Real.abs_le_sqrt (by nlinarith [sq_nonneg J])
    rw [abs_div, abs_two] at this
    linarith
  have key : |a - b| * (a + b) ≤ |x - y| / 2 * (a + b) := by
    have e : |a - b| * (a + b) = |x - y| * |x + y| / 4 := by
      rw [← abs_of_nonneg (by linarith : 0 ≤ a + b), ← abs_mul, ← abs_mul,
        show (a - b) * (a + b) = (x - y) * (x + y) / 4 by nlinarith [ha2, hb2], abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_mul]
    rw [e]
    have hxy : |x + y| ≤ 2 * (a + b) := (abs_add_le x y).trans (by linarith)
    have := mul_le_mul_of_nonneg_left hxy (abs_nonneg (x - y))
    linarith
  rcases (add_nonneg ha0 hb0).lt_or_eq with hpos | hzero
  · exact le_of_mul_le_mul_right key hpos
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    rw [ha', hb', sub_zero, abs_zero]
    positivity

/-- The transfer factor `(J/Ω)² = 1/(1 + (Δ/2J)²)` is `1/(2J)`-Lipschitz in the detuning. -/
theorem abs_loss_sub_le {J : ℝ} (hJ : 0 < J) (x y : ℝ) :
    |(J / rabiFreq J x) ^ 2 - (J / rabiFreq J y) ^ 2| ≤ |x - y| / (2 * J) := by
  set u := x / (2 * J) with hu
  set v := y / (2 * J) with hv
  have hx : (J / rabiFreq J x) ^ 2 = 1 / (1 + u ^ 2) := by
    rw [div_pow, rabiFreq_sq, hu]
    field_simp
  have hy : (J / rabiFreq J y) ^ 2 = 1 / (1 + v ^ 2) := by
    rw [div_pow, rabiFreq_sq, hv]
    field_simp
  have huv : |x - y| / (2 * J) = |u - v| := by
    rw [show u - v = (x - y) / (2 * J) by ring, abs_div, abs_of_pos (by positivity : 0 < 2 * J)]
  rw [hx, hy, huv]
  have hP : 0 < 1 + u ^ 2 := by positivity
  have hQ : 0 < 1 + v ^ 2 := by positivity
  have e : 1 / (1 + u ^ 2) - 1 / (1 + v ^ 2) = (v - u) * (v + u) / ((1 + u ^ 2) * (1 + v ^ 2)) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (mul_pos hP hQ), abs_mul, div_le_iff₀ (mul_pos hP hQ), abs_sub_comm v u]
  have hu : |u| ≤ (1 + u ^ 2) / 2 := by nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
  have hv : |v| ≤ (1 + v ^ 2) / 2 := by nlinarith [sq_abs v, sq_nonneg (|v| - 1)]
  have hsum : |v + u| ≤ (1 + u ^ 2) * (1 + v ^ 2) := by
    have h1 : (1 + u ^ 2) / 2 ≤ (1 + u ^ 2) * (1 + v ^ 2) / 2 := by nlinarith [sq_nonneg v]
    have h2 : (1 + v ^ 2) / 2 ≤ (1 + u ^ 2) * (1 + v ^ 2) / 2 := by nlinarith [sq_nonneg u]
    linarith [abs_add_le v u]
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- ★ **The coupling's effect on the clock's Rabi rate**: `|ω_c − ω| ≤ |g_c f_c(θ₂ᴬ)|/(2ħ)`. -/
theorem abs_clockFreq_sub_handFreq_le (hħ : 0 < ħ) :
    |clockFreq ħ Jc Cc C qA qh - handFreq Jc ħ C.g C.periodic qh|
      ≤ |detuningAt Cc.g Cc.periodic qA.2| / (2 * ħ) := by
  unfold clockFreq echoRate echoDetuning handFreq rabiRate
  rw [← sub_div, abs_div, abs_of_pos hħ]
  have h := abs_rabiFreq_sub_le Jc (detuningAt C.g C.periodic qh.2 - detuningAt Cc.g Cc.periodic qA.2)
    (detuningAt C.g C.periodic qh.2)
  rw [sub_sub_cancel_left, abs_neg] at h
  calc _ ≤ (|detuningAt Cc.g Cc.periodic qA.2| / 2) / ħ := div_le_div_of_nonneg_right h hħ.le
    _ = |detuningAt Cc.g Cc.periodic qA.2| / (2 * ħ) := by ring

/-- ★ **The coupling's effect on the clock's mean rate**:
`|κ_c − κ| ≤ |r_h| · |g_c f_c(θ₂ᴬ)|/(2J_c)`. -/
theorem abs_clockRate_sub_handRate_le (hJc : 0 < Jc) :
    |clockRate ħ Jc Cc C qA qh - handRate Jc ħ C.g C.periodic qh|
      ≤ |rateAt C.g ħ C.periodic qh.2| * (|detuningAt Cc.g Cc.periodic qA.2| / (2 * Jc)) := by
  unfold clockRate receiverDrift echoLoss echoDetuning handRate driftRate
  rw [← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_loss_sub_le hJc (detuningAt C.g C.periodic qh.2 - detuningAt Cc.g Cc.periodic qA.2)
    (detuningAt C.g C.periodic qh.2)
  rwa [sub_sub_cancel_left, abs_neg] at this

/-! ### The package -/

/-- ★★★ **The clock coupled to the echo.** On the one arena `(ℂℙ³ × T² × T²) × (ℂℙ³ × T²)` with
the clock's carrier detuned at `A` by the echo's pointer (`g_c f_c(θ₂ᴬ) n_{A,c}`):

* the coupled dynamics is a two-time, autonomous, measure-preserving flow that conserves the joint
  energy (and the three angles `θ₂`);
* **reading the clock disturbs the echo's register**: pointer `A` turns by the echo's drift plus the
  clock carrier's;
* the emission, reception and return and the clock's ticks are still `ActualOccurrence`s, with the
  coupled windows;
* the radar timestamps, read on the coupled clock while `A`'s two records display, are within the
  coupled budget of the ideal round trip — #202's budget with the coupled constants and **one more
  term, the coupling's shift of the return record**, bounded by `(b_c + m_c · returnEnd)/m`;
* the coupling moves the clock's mean rate and Rabi rate by at most `|r_h| |g_c f_c(θ₂ᴬ)|/(2J_c)` and
  `|g_c f_c(θ₂ᴬ)|/(2ħ)`;
* at zero coupling the budget is #202's exactly. -/
theorem coupled_clock_and_echo (hJ : 0 < J) (hJc : 0 < Jc) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA) (hrc : 0 ≤ senderRate Cc ħ qA)
    (hslow : coupledBand J ħ A B Jc Cc C qA qB qh ≤ 1 / 12)
    (hκ : 0 < receiverDrift A B J ħ qA qB)
    (hslowB : 3 * receiverDrift A B J ħ qA qB ≤ 2 * echoRate A B J ħ qA qB) (hK : 0 < K)
    (hqh : qh ∈ handReady K) (hκc : 0 < clockRate ħ Jc Cc C qA qh)
    (hslowc : K * clockRate ħ Jc Cc C qA qh ≤ clockFreq ħ Jc Cc C qA qh) {t₁ t₂ : ℝ}
    (h₂ : t₂ ≤ coupledHorizon ħ Jc Cc C K qA qh)
    (hemit : bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        ≤ t₁
      ∧ t₁ ≤ bandEmitEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh))
    (hret : bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        ≤ t₂
      ∧ t₂ ≤ bandReturnEnd (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh)
        + bandWindow (coupledMean J ħ A B Jc Cc C qA qB qh) (coupledBand J ħ A B Jc Cc C qA qB qh))
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    (∀ s t u : OnticTime, coupledEvolve J ħ A B Jc Cc C t u ∘ coupledEvolve J ħ A B Jc Cc C s t
        = coupledEvolve J ħ A B Jc Cc C s u)
      ∧ (∀ s t a : OnticTime,
          coupledEvolve J ħ A B Jc Cc C (s + a) (t + a) = coupledEvolve J ħ A B Jc Cc C s t)
      ∧ (∀ (s t : OnticTime) (p₀ p₁ : FieldArena 2 2),
          MeasurePreserving (coupledEvolve J ħ A B Jc Cc C s t)
            (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
            (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)))
      ∧ (∀ (t : ℝ) (x : ClockEchoArena),
          coupledEnergy J A B Jc Cc C (coupledFlow J ħ A B Jc Cc C t x) = coupledEnergy J A B Jc Cc C x)
      ∧ (∀ t : ℝ, (coupledFlow J ħ A B Jc Cc C t (coupledPrep qA qB qh)).1.2.1
          = pshift (senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t
            + senderDrift (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh) t)
            qA)
      ∧ (coupledEmission A B Cc C hJ hJc hħ hqA hqB hqh hr hrc hslow).site = {0}
      ∧ (coupledReception A B Cc C (Jc := Jc) hJ hħ hqA hqB hqh hκ hslowB).site = {1}
      ∧ (coupledReturn A B Cc C hJ hJc hħ hqA hqB hqh hr hrc hslow).site = {0}
      ∧ (∀ (n : ℕ) (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K),
          (coupledTick (J := J) A B Cc C hJc hħ hqA hqB hK hqh hκc hslowc hn1 hnK).site = {0}
            ∧ (coupledTick (J := J) A B Cc C hJc hħ hqA hqB hK hqh hκc hslowc hn1 hnK).value = n)
      ∧ (∃ (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂),
          senderRead (coupledFlow J ħ A B Jc Cc C t₁ (coupledPrep qA qB qh)).1 = 1
          ∧ senderRead (coupledFlow J ħ A B Jc Cc C t₂ (coupledPrep qA qB qh)).1 = 2
          ∧ |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).radarTime
              - (idealEchoReadings hJ hħ).radarTime| ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh
          ∧ |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).radarSep
              - (idealEchoReadings hJ hħ).radarSep| ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh
          ∧ |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).radarDist c₀
              - (idealEchoReadings hJ hħ).radarDist c₀|
            ≤ c₀ * coupledBudget J ħ A B Jc Cc C K qA qB qh)
      ∧ couplingTerm J ħ A B Jc Cc C qA qB qh
          ≤ (band (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh) (echoRate Cc C Jc ħ qA qh)
              + meanRate (senderRate Cc ħ qA) (echoLoss Cc C Jc qA qh)
                * returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
            / coupledMean J ħ A B Jc Cc C qA qB qh
      ∧ |clockRate ħ Jc Cc C qA qh - handRate Jc ħ C.g C.periodic qh|
          ≤ |rateAt C.g ħ C.periodic qh.2| * (|detuningAt Cc.g Cc.periodic qA.2| / (2 * Jc))
      ∧ |clockFreq ħ Jc Cc C qA qh - handFreq Jc ħ C.g C.periodic qh|
          ≤ |detuningAt Cc.g Cc.periodic qA.2| / (2 * ħ)
      ∧ (Cc.g = 0 → coupledBudget J ħ A B Jc Cc C K qA qB qh = clockEchoBudget A B J ħ qA qB Jc C K qh) := by
  have hm := coupledMean_pos A B Cc C (qB := qB) (qh := qh) hJ hJc hr hrc
  have hb := coupledBand_nonneg A B Cc C (qB := qB) (qh := qh) hJ hJc hħ hr hrc
  have h₁ : 0 ≤ t₁ := (bandEmitEnd_nonneg hm hb).trans hemit.1
  have h₁₂ : t₁ ≤ t₂ := by
    have := bandEmitEnd_add_window_lt hm hb
    linarith [hemit.2, hret.1]
  refine ⟨coupledEvolve_comp J ħ A B Jc Cc C, coupledEvolve_shift J ħ A B Jc Cc C,
    fun s t p₀ p₁ => coupledEvolve_measurePreserving J ħ A B Jc Cc C s t p₀ p₁,
    coupledEnergy_coupledFlow J ħ A B Jc Cc C, fun t => coupledFlow_pointerA A B Cc C hJ hJc hħ qA qB qh t,
    rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩, ⟨h₁, h₁₂,
      coupled_emitted A B Cc C hJ hJc hħ hqA hr hrc hemit.1 hemit.2,
      coupled_returned A B Cc C hJ hJc hħ hqA hr hrc hret.1 hret.2, ?_, ?_, ?_⟩,
    couplingTerm_le A B Cc C hJ hJc hħ hr hrc, abs_clockRate_sub_handRate_le Cc C hJc,
    abs_clockFreq_sub_handFreq_le Cc C hħ, coupledBudget_of_g_eq_zero A B Cc C⟩
  all_goals
    have he : |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).emit - (idealEchoReadings hJ hħ).emit|
        ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh := by
      rw [idealEchoReadings_emit]
      exact abs_coupledReadings_emit_sub_le A B Cc C hJ hJc hħ hK hqh hκc h₁ h₁₂ h₂ hemit.2
    have hre : |(coupledReadings Cc C hJc hħ hK hqh hκc h₁ h₁₂ h₂).ret - (idealEchoReadings hJ hħ).ret|
        ≤ coupledBudget J ħ A B Jc Cc C K qA qB qh := by
      rw [idealEchoReadings_ret]
      exact abs_coupledReadings_ret_sub_le A B Cc C hJ hJc hħ hK hr hrc hqh hκc h₁ h₁₂ h₂ hret
  · exact RadarReadings.abs_radarTime_sub_le he hre
  · exact RadarReadings.abs_radarSep_sub_le he hre
  · exact RadarReadings.abs_radarDist_sub_le hc₀ he hre

end Radar

end CSD.RecordLayer

end
