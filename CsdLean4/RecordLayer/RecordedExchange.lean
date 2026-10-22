/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.SignalExchange
public import CsdLean4.CV.RecordCausalOrder
public import CsdLean4.RecordLayer.RecordClock
public import CsdLean4.RecordLayer.MacroProjection
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MomentMap

/-!
# The recorded exchange: clock, signal and three records on one arena, with one evolution

**Category:** 7-SigmaLayer (the record layer — the common arena of the clock-and-echo programme).
BACKLOG #186 (out of #39; the fourth of #183–#189, the price driver).

#183 built the signal (a two-site hop on `FieldArena 2 2`), #185 the clock (`ClockArena K`). This
file puts them on **one arena with one evolution** and adds the three record registers the
experiment needs — emission at `A`, reception at `B`, return at `A` — each written by the record
mechanism of `ShearWitness.lean`: a pointer translated by `shearAmt 2 b` from the ready arc into the
pointer arc of the bit `b` it reads. A register is written on the crossing of its readout time, by
the bit read off the **exchange state at that time**; the hop is switched on at `t = 0`, the
apparatus is prepared at `t = −1`.

* `XArena K = FieldArena 2 2 × ClockArena K × (Fin 3 → KTorus)`; `hopOn`, `arrived`, `readTime`,
  `readSite`, `readBit` (the occupancy weight of a site, thresholded at `1/2`, measurable by
  `measurable_momentMap`); `xEvolve J ħ T s t` — **the joint two-time propagator**;
* `xEvolve_self`, ★★ `xEvolve_comp` — **the two-time law holds on the common arena**: the bit a
  register reads is the exchange state at its readout time, which the group law of the hop makes
  independent of where the propagator is cut; `measurable_xEvolve`; ★ `xEvolve_measurePreserving`
  — Liouville (Fubini–Study × Haar × Haar) is preserved: **it is a dynamics**;
* `XReady`, `xPrep b c r` — the ready preparation with message `b`; `register_before`,
  ★★ `register_written` — **each register is written with the message**, emission at `0`, reception
  at `τ_hop`, return at `2 τ_hop`, from the actual transfer (`arenaFlow_hopTime`,
  `arenaFlow_roundTrip`) and nothing else; `register_frozen`;
* `recordProtocol i` — **each register is a `MeasurementProtocol`**, `recordProtocol_pointerInvariant`,
  ★ `record_persists` through the corpus's `record_persists_on_interval`;
* ★★ `reception_depends_on_message`, `return_depends_on_message` — **demonstrated influence**: two
  preparations differing only in the message (`msgConfig_siteB`) leave the reception register, and
  the return register, in disjoint pointer arcs;
* `Occurrence`, `emission`, `reception`, `returnOcc`, `eventOf` — **occurrences with their register,
  site, time and message, and the forgetful map to `CV.RecordEvent`**, whose period label is the
  tick count of the physical clock in the arena at the occurrence time (`eventOf_emission`,
  `eventOf_reception`, `eventOf_return` under the stated calibration `T = τ_hop`);
* ★★ `causal_chain` — **`emission ⪯ reception ⪯ return` under `CausalPrecedes`** on the coupling
  graph `{(A, B)}`, and `emission ⪯ return` by the corpus's transitivity;
* `recordEvents`, `recordPattern`, ★ `factorsThrough_recordEvents` — **the record predicates factor
  through a macroscopic projection**, the pattern projection of `MacroProjection.lean`;
* ★★★ `recorded_exchange` — the package.

## The two clocks, identified explicitly

`RecordEvent.time` is a period index; the clock reads a tick count. They coincide here by a
**stated modelling choice**: the clock period is the hop time, `T = τ_hop`, so emission, reception
and return fall at ticks `0`, `1`, `2` (`tickCount_at_period`). With another period the same
occurrences carry other labels; nothing identifies the two clocks dynamically.

## Honest scope

* ⚠️ The readout times and the switch-on are a schedule, a modelling input indexed by `t_Σ`, as in
  #185. The writes are triggered by the schedule reading the exchange state; a dynamical trigger is
  not built.
* ⚠️ `CausalPrecedes` is *permitted* influence on an assumed graph; the demonstrated influence is
  `reception_depends_on_message`. Both are proved; neither is inferred from the other.
* The bit is read by thresholding an occupancy weight at `1/2`. At the readout times the exchange
  state is a basis ray, so the weight is `0` or `1` and the threshold is never close; between them
  it is not read.
* No metric, no volume element on the event order, no universal `c`: the scoping note's §8 stands.

References: `specs/BACKLOG.md` #186, #183, #185, #187, #39; `CV/SignalExchange.lean`,
`RecordLayer/RecordClock.lean`, `CV/RecordCausalOrder.lean` (`RecordEvent`, `CausalPrecedes`),
`RecordLayer/MacroProjection.lean` (`patternProjection`, `factorsThrough_patternMap`),
`RecordLayer/ShearWitness.lean` (the arcs and `shearAmt`), `RecordLayer/RecordPersistence.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K : ℕ}

/-! ### The common arena -/

/-- **The experiment's arena**: the exchange, the clock, and three record registers
(`0` emission at `A`, `1` reception at `B`, `2` return at `A`). -/
abbrev XArena (K : ℕ) := FieldArena 2 2 × ClockArena K × (Fin 3 → LF4.KTorus)

/-- The hop coupling is switched on at `t = 0`: the exchange has run for `hopOn u` by time `u`. -/
noncomputable def hopOn (u : ℝ) : ℝ := max u 0

theorem hopOn_of_nonneg {u : ℝ} (hu : 0 ≤ u) : hopOn u = u := max_eq_left hu

theorem hopOn_of_nonpos {u : ℝ} (hu : u ≤ 0) : hopOn u = 0 := max_eq_right hu

/-- `1` once the readout time `τ` has arrived, `0` before. -/
noncomputable def arrived (τ t : ℝ) : ℝ := if τ ≤ t then 1 else 0

theorem arrived_of_le {τ t : ℝ} (h : τ ≤ t) : arrived τ t = 1 := by simp [arrived, h]

theorem arrived_of_lt {τ t : ℝ} (h : t < τ) : arrived τ t = 0 := by simp [arrived, not_le.mpr h]

/-- The readout times: emission at `0`, reception at `τ_hop`, return at `2 τ_hop`. -/
noncomputable def readTime (J ħ : ℝ) : Fin 3 → ℝ := ![0, hopTime J ħ, roundTrip J ħ]

/-- The site each register reads: `A`, `B`, `A`. -/
def readSite : Fin 3 → Fin 2 := ![0, 1, 0]

/-- The one-excitation configuration of a site. -/
def siteConfig : Fin 2 → HopConfig := ![excA, excB]

theorem readTime_zero (J ħ : ℝ) : readTime J ħ 0 = 0 := rfl
theorem readTime_one (J ħ : ℝ) : readTime J ħ 1 = hopTime J ħ := rfl
theorem readTime_two (J ħ : ℝ) : readTime J ħ 2 = roundTrip J ħ := rfl

theorem readTime_nonneg {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (i : Fin 3) : 0 ≤ readTime J ħ i := by
  fin_cases i
  · exact le_rfl
  · exact (hopTime_pos hJ hħ).le
  · exact (roundTrip_pos hJ hħ).le

/-- The bit read off a ray at a configuration: its occupancy weight thresholded at `1/2`. -/
noncomputable def readBit (c : HopConfig) (p : FieldArena 2 2) : Fin 2 :=
  if 1 / 2 ≤ momentMap p c then 1 else 0

theorem measurable_readBit (c : HopConfig) : Measurable (readBit c) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_momentMap c)) measurable_const
    measurable_const

/-! ### The arena kick is the unitary action -/

theorem arenaKick_eq_smul (U : Matrix.unitaryGroup HopConfig ℂ) (p : FieldArena 2 2) :
    arenaKick U p = U • p := by
  conv_rhs => rw [← p.mk_rep]
  rw [smul_mk_eq_mk_toEuclideanLin]
  rfl

theorem measurable_arenaKick (U : Matrix.unitaryGroup HopConfig ℂ) :
    Measurable (arenaKick U : FieldArena 2 2 → FieldArena 2 2) := by
  have h : (arenaKick U : FieldArena 2 2 → FieldArena 2 2) = fun p => U • p :=
    funext (arenaKick_eq_smul U)
  rw [h]
  exact (continuous_const_smul U).measurable

theorem hopFlow_zero (J ħ : ℝ) : (hopFlow J ħ).flow 0 = 1 := by
  apply Subtype.ext
  rw [FieldStructuredFlow.flow_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem arenaFlow_zero (J ħ : ℝ) (p : FieldArena 2 2) : (hopFlow J ħ).arenaFlow 0 p = p := by
  rw [FieldStructuredFlow.arenaFlow, hopFlow_zero, arenaKick_eq_smul, one_smul]

theorem measurable_arenaFlow (J ħ t : ℝ) : Measurable ((hopFlow J ħ).arenaFlow t) :=
  measurable_arenaKick _

/-! ### The joint propagator -/

/-- The bit register `i` reads: the occupancy of its site in the exchange state at its readout
time, when the propagator starts at `s`. -/
noncomputable def readAt (J ħ : ℝ) (i : Fin 3) (s : OnticTime) (p : FieldArena 2 2) : Fin 2 :=
  readBit (siteConfig (readSite i))
    ((hopFlow J ħ).arenaFlow (hopOn (readTime J ħ i) - hopOn s) p)

/-- **The joint two-time propagator**: the hop runs from switch-on, the clock runs on its schedule,
and register `i` is translated by `shearAmt 2 (bit)` on the crossing of its readout time, the bit
being read off the exchange state at that time. -/
noncomputable def xEvolve (J ħ T : ℝ) (s t : OnticTime) : XArena K → XArena K := fun x =>
  ((hopFlow J ħ).arenaFlow (hopOn t - hopOn s) x.1,
    clockEvolve T s t x.2.1,
    fun i => pshift ((arrived (readTime J ħ i) t - arrived (readTime J ħ i) s)
      * shearAmt 2 (readAt J ħ i s x.1)) (x.2.2 i))

theorem xEvolve_exchange (J ħ T : ℝ) (s t : OnticTime) (x : XArena K) :
    (xEvolve J ħ T s t x).1 = (hopFlow J ħ).arenaFlow (hopOn t - hopOn s) x.1 := rfl

theorem xEvolve_clock (J ħ T : ℝ) (s t : OnticTime) (x : XArena K) :
    (xEvolve J ħ T s t x).2.1 = clockEvolve T s t x.2.1 := rfl

theorem xEvolve_register (J ħ T : ℝ) (s t : OnticTime) (x : XArena K) (i : Fin 3) :
    (xEvolve J ħ T s t x).2.2 i
      = pshift ((arrived (readTime J ħ i) t - arrived (readTime J ħ i) s)
          * shearAmt 2 (readAt J ħ i s x.1)) (x.2.2 i) := rfl

theorem xEvolve_self (J ħ T : ℝ) (t : OnticTime) : xEvolve (K := K) J ħ T t t = id := by
  funext x
  simp [xEvolve, arenaFlow_zero, clockEvolve_self]

/-- The bit read at the readout time does not depend on where the propagator is cut. -/
theorem readAt_arenaFlow (J ħ : ℝ) (i : Fin 3) (s t : OnticTime) (p : FieldArena 2 2) :
    readAt J ħ i t ((hopFlow J ħ).arenaFlow (hopOn t - hopOn s) p) = readAt J ħ i s p := by
  unfold readAt
  rw [← FieldStructuredFlow.arenaFlow_add]
  congr 2
  ring

/-- ★★ **The two-time composition law on the common arena.** -/
theorem xEvolve_comp (J ħ T : ℝ) (s t u : OnticTime) :
    xEvolve (K := K) J ħ T t u ∘ xEvolve J ħ T s t = xEvolve J ħ T s u := by
  funext x
  simp only [Function.comp_apply, xEvolve]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    rw [← FieldStructuredFlow.arenaFlow_add]
    congr 1
    ring
  · simp only
    exact congrFun (clockEvolve_comp T s t u) x.2.1
  · funext i
    simp only
    rw [readAt_arenaFlow, pshift_add]
    congr 1
    ring

theorem measurable_xEvolve (J ħ T : ℝ) (s t : OnticTime) :
    Measurable (xEvolve (K := K) J ħ T s t) := by
  refine Measurable.prodMk ((measurable_arenaFlow J ħ _).comp measurable_fst)
    (Measurable.prodMk ((measurable_clockEvolve T s t).comp (measurable_fst.comp measurable_snd))
      (measurable_pi_iff.mpr fun i => ?_))
  have hcoef : Measurable fun x : XArena K =>
      (arrived (readTime J ħ i) t - arrived (readTime J ħ i) s) * shearAmt 2 (readAt J ħ i s x.1) :=
    measurable_const.mul ((Measurable.of_discrete (f := shearAmt 2)).comp
      (((measurable_readBit _).comp (measurable_arenaFlow J ħ _)).comp measurable_fst))
  exact continuous_pshift_uncurry.measurable.comp
    (hcoef.prodMk ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))

/-- The exchange factor preserves the Fubini–Study measure at every reference point. -/
theorem arenaFlow_measurePreserving (J ħ t : ℝ) (p₀ : FieldArena 2 2) :
    MeasurePreserving ((hopFlow J ħ).arenaFlow t) (fsMeasure p₀) (fsMeasure p₀) := by
  have h : (hopFlow J ħ).arenaFlow t = fun p => (hopFlow J ħ).flow t • p :=
    funext fun p => arenaKick_eq_smul _ p
  rw [h]
  exact ⟨(continuous_const_smul _).measurable, fsMeasure_smul_invariant _ p₀⟩

/-- ★ **The joint propagator preserves Liouville measure** — Fubini–Study on the exchange, Haar on
the clock and the registers — for every reference point of the Fubini–Study measure: it is a
dynamics. The register shifts depend on the exchange state, so this is a skew product. -/
theorem xEvolve_measurePreserving (J ħ T : ℝ) (s t : OnticTime) (p₀ : FieldArena 2 2) :
    MeasurePreserving (xEvolve (K := K) J ħ T s t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  have hfib : ∀ p : FieldArena 2 2, MeasurePreserving
      (fun y : ClockArena K × (Fin 3 → LF4.KTorus) =>
        (clockEvolve T s t y.1, fun i => pshift ((arrived (readTime J ħ i) t
          - arrived (readTime J ħ i) s) * shearAmt 2 (readAt J ħ i s p)) (y.2 i)))
      volume volume := by
    intro p
    have h : (fun y : ClockArena K × (Fin 3 → LF4.KTorus) =>
        (clockEvolve T s t y.1, fun i => pshift ((arrived (readTime J ħ i) t
          - arrived (readTime J ħ i) s) * shearAmt 2 (readAt J ħ i s p)) (y.2 i)))
        = Prod.map (clockEvolve T s t) (fun r : Fin 3 → LF4.KTorus => fun i : Fin 3 =>
            pshift ((arrived (readTime J ħ i) t - arrived (readTime J ħ i) s)
              * shearAmt 2 (readAt J ħ i s p)) (r i)) := rfl
    rw [h, Measure.volume_eq_prod, volume_pi]
    exact (clockEvolve_measurePreserving T s t).prod
      (measurePreserving_pi _ _ fun i => measurePreserving_pshift _)
  have hgm : Measurable (Function.uncurry fun (p : FieldArena 2 2)
      (y : ClockArena K × (Fin 3 → LF4.KTorus)) =>
        (clockEvolve T s t y.1, fun i => pshift ((arrived (readTime J ħ i) t
          - arrived (readTime J ħ i) s) * shearAmt 2 (readAt J ħ i s p)) (y.2 i))) := by
    refine Measurable.prodMk ((measurable_clockEvolve T s t).comp (measurable_fst.comp measurable_snd))
      (measurable_pi_iff.mpr fun i => ?_)
    have hcoef : Measurable fun x : FieldArena 2 2 × (ClockArena K × (Fin 3 → LF4.KTorus)) =>
        (arrived (readTime J ħ i) t - arrived (readTime J ħ i) s) * shearAmt 2 (readAt J ħ i s x.1) :=
      measurable_const.mul ((Measurable.of_discrete (f := shearAmt 2)).comp
        (((measurable_readBit _).comp (measurable_arenaFlow J ħ _)).comp measurable_fst))
    exact continuous_pshift_uncurry.measurable.comp
      (hcoef.prodMk ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))
  exact (arenaFlow_measurePreserving J ħ _ p₀).skew_product hgm
    (Filter.Eventually.of_forall fun p => (hfib p).map_eq)

/-! ### The ready preparation and what the registers read -/

/-- **The ready preparation**: clock ready, all three registers in the ready arc. -/
def XReady (K : ℕ) : Set (XArena K) :=
  {x | x.2.1 ∈ ClockReady K ∧ ∀ i, x.2.2 i ∈ readyArc 2}

/-- The preparation with message `b`: the exchange at the message point, clock and registers as
given. -/
noncomputable def xPrep (b : Fin 2) (c : ClockArena K) (r : Fin 3 → LF4.KTorus) : XArena K :=
  (msgPoint b, c, r)

/-- The occupancy weight of a configuration at a message point is `1` at the message's
configuration and `0` elsewhere. -/
theorem momentMap_msgPoint (b : Fin 2) (c : HopConfig) :
    momentMap (msgPoint b) c = if c = msgConfig b then 1 else 0 := by
  rw [msgPoint, momentMap_mk, basisVec, PiLp.norm_single, norm_one, one_pow, div_one]
  by_cases h : c = msgConfig b
  · subst h
    simp
  · simp [h]

theorem momentMap_mk_basisVec (c c' : HopConfig) :
    momentMap (Projectivization.mk ℂ (basisVec c) (basisVec_ne_zero c)) c'
      = if c' = c then 1 else 0 := by
  rw [momentMap_mk, basisVec, PiLp.norm_single, norm_one, one_pow, div_one]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h]

/-- The vacuum does not move: message `0`'s exchange point is fixed by the hop. -/
theorem arenaFlow_msgPoint_zero (J ħ t : ℝ) : (hopFlow J ħ).arenaFlow t (msgPoint 0) = msgPoint 0 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_zero, arenaKick_mk]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by
    rw [one_smul, toEuclideanLin_hopFlow_vacC]⟩

/-- At `A`, the message point reads its message. -/
theorem readBit_msgPoint_excA (b : Fin 2) : readBit excA (msgPoint b) = b := by
  unfold readBit
  rw [momentMap_msgPoint]
  fin_cases b
  · simp [msgConfig_zero, vacC_ne_excA.symm]
  · norm_num [msgConfig_one]

theorem readAt_xPrep_zero (J ħ : ℝ) (b : Fin 2) : readAt J ħ 0 (-1) (msgPoint b) = b := by
  show readBit excA ((hopFlow J ħ).arenaFlow (hopOn 0 - hopOn (-1)) (msgPoint b)) = b
  rw [hopOn_of_nonneg le_rfl, hopOn_of_nonpos (by norm_num), sub_zero, arenaFlow_zero]
  exact readBit_msgPoint_excA b

theorem readAt_xPrep_one {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2) :
    readAt J ħ 1 (-1) (msgPoint b) = b := by
  show readBit excB ((hopFlow J ħ).arenaFlow (hopOn (hopTime J ħ) - hopOn (-1)) (msgPoint b)) = b
  rw [hopOn_of_nonneg (hopTime_pos hJ hħ).le, hopOn_of_nonpos (by norm_num), sub_zero]
  fin_cases b
  · show readBit excB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 0)) = 0
    rw [arenaFlow_msgPoint_zero]
    unfold readBit
    rw [momentMap_msgPoint]
    norm_num [msgConfig_zero, vacC_ne_excB.symm]
  · show readBit excB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 1)) = 1
    rw [arenaFlow_hopTime hJ hħ]
    unfold readBit
    rw [momentMap_mk_basisVec]
    norm_num

theorem readAt_xPrep_two {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2) :
    readAt J ħ 2 (-1) (msgPoint b) = b := by
  show readBit excA ((hopFlow J ħ).arenaFlow (hopOn (roundTrip J ħ) - hopOn (-1)) (msgPoint b)) = b
  rw [hopOn_of_nonneg (roundTrip_pos hJ hħ).le, hopOn_of_nonpos (by norm_num), sub_zero]
  fin_cases b
  · show readBit excA ((hopFlow J ħ).arenaFlow (roundTrip J ħ) (msgPoint 0)) = 0
    rw [arenaFlow_msgPoint_zero]
    exact readBit_msgPoint_excA 0
  · show readBit excA ((hopFlow J ħ).arenaFlow (roundTrip J ħ) (msgPoint 1)) = 1
    rw [arenaFlow_roundTrip hJ hħ]
    exact readBit_msgPoint_excA 1

/-- ★ **Each register reads the message at its readout time**: emission reads `A` at `0`,
reception reads `B` at `τ_hop` (the transfer), return reads `A` at `2 τ_hop` (the Rabi return). -/
theorem readAt_xPrep {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (i : Fin 3) (b : Fin 2) :
    readAt J ħ i (-1) (msgPoint b) = b := by
  fin_cases i
  · exact readAt_xPrep_zero J ħ b
  · exact readAt_xPrep_one hJ hħ b
  · exact readAt_xPrep_two hJ hħ b

/-! ### The records -/

/-- A ready pointer shifted by `shearAmt K i` displays outcome `i`. -/
theorem pshift_shearAmt_mem_pointerArc {K' : ℕ} (i : Fin K') {q : LF4.KTorus}
    (hq : q ∈ readyArc K') : pshift (shearAmt K' i) q ∈ pointerArc K' i := by
  change rep q.1 ∈ Ioc (0 : ℝ) (shearWidth K') at hq
  change rep (pshift (shearAmt K' i) q).1 ∈ Ioc (shearAmt K' i) (shearAmt K' i + shearWidth K')
  have hle := shearAmt_add_width_le_one (K := K') i
  have hpos := shearAmt_pos (K := K') i
  rw [rep_pshift_of_mem _ _ ⟨by linarith [hq.1], by linarith [hq.2]⟩]
  constructor <;> linarith [hq.1, hq.2]

theorem readyArc_disjoint_pointerArc {K' : ℕ} (i : Fin K') :
    Disjoint (readyArc K') (pointerArc K' i) := by
  refine Set.disjoint_left.mpr fun q hr hp => ?_
  change rep q.1 ∈ Ioc (0 : ℝ) (shearWidth K') at hr
  change rep q.1 ∈ Ioc (shearAmt K' i) (shearAmt K' i + shearWidth K') at hp
  have h1 : shearWidth K' < shearAmt K' i := by
    have := shearWidth_lt_gap (K := K')
    have hg := shearGap_pos (K := K')
    have hi : (1 : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    unfold shearAmt
    nlinarith
  linarith [hr.2, hp.1]

/-- Before its readout time a register is still ready. -/
theorem register_before {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {x : XArena K} (hx : x ∈ XReady K)
    (i : Fin 3) {t : OnticTime} (ht : t < readTime J ħ i) :
    (xEvolve J ħ T (-1) t x).2.2 i ∈ readyArc 2 := by
  rw [xEvolve_register, arrived_of_lt ht,
    arrived_of_lt (show (-1 : ℝ) < readTime J ħ i by linarith [readTime_nonneg hJ hħ i]),
    sub_self, zero_mul, pshift_zero]
  exact hx.2 i

/-- ★★ **Each register is written with the message** from its readout time on: emission at `0`,
reception at `τ_hop`, return at `2 τ_hop`. -/
theorem register_written {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) (i : Fin 3) {t : OnticTime}
    (ht : readTime J ħ i ≤ t) :
    (xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i ∈ pointerArc 2 b := by
  rw [xEvolve_register, arrived_of_le ht,
    arrived_of_lt (show (-1 : ℝ) < readTime J ħ i by linarith [readTime_nonneg hJ hħ i]),
    sub_zero, one_mul]
  change pshift (shearAmt 2 (readAt J ħ i (-1) (msgPoint b))) (r i) ∈ pointerArc 2 b
  rw [readAt_xPrep hJ hħ i b]
  exact pshift_shearAmt_mem_pointerArc b (hr i)

/-- After its readout time a register is frozen. -/
theorem register_frozen (J ħ T : ℝ) {s t : OnticTime} (i : Fin 3) (hs : readTime J ħ i ≤ s)
    (hst : s ≤ t) (x : XArena K) : (xEvolve J ħ T s t x).2.2 i = x.2.2 i := by
  rw [xEvolve_register, arrived_of_le hs, arrived_of_le (hs.trans hst), sub_self, zero_mul,
    pshift_zero]

/-! ### Each register is a measurement protocol; the records persist -/

/-- **Register `i` as a `MeasurementProtocol`** with two outcomes (the bit), prepared at `−1`, read
out at its readout time, with record lifetime `τR`. -/
noncomputable def recordProtocol (J ħ T : ℝ) (i : Fin 3) (τR : ℝ) :
    MeasurementProtocol (XArena K) 2 where
  evolve := xEvolve J ħ T
  evolve_self := xEvolve_self J ħ T
  evolve_comp := xEvolve_comp J ħ T
  measurable_evolve := measurable_xEvolve J ħ T
  startTime := -1
  readoutTime := readTime J ħ i
  recordDuration := τR
  readyRegion := {x | x.2.2 i ∈ readyArc 2}
  pointerRegion := fun j => {x | x.2.2 i ∈ pointerArc 2 j}
  measurableSet_ready :=
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) measurableSet_readyArc
  measurableSet_pointer := fun j =>
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) (measurableSet_pointerArc j)
  pointer_pairwiseDisjoint := fun _ _ hjj' =>
    (pointerArc_pairwiseDisjoint hjj').preimage _
  ready_disjoint_pointer := fun j => (readyArc_disjoint_pointerArc j).preimage _

theorem recordProtocol_pointerInvariant (J ħ T : ℝ) (i : Fin 3) (τR : ℝ) :
    (recordProtocol (K := K) J ħ T i τR).PointerInvariantOn := by
  intro _ s t hs hst _ x hx
  have hs' : readTime J ħ i ≤ s := hs
  change (xEvolve J ħ T s t x).2.2 i ∈ pointerArc 2 _
  rw [register_frozen J ħ T i hs' hst]
  exact hx

/-- ★ **The records persist** from the readout time through the record lifetime — by the corpus's
`record_persists_on_interval`, applied to `recordProtocol i`. -/
theorem record_persists {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) (i : Fin 3) {τR t : ℝ}
    (ht₁ : readTime J ħ i ≤ t) (ht₂ : t ≤ readTime J ħ i + τR) :
    (xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i ∈ pointerArc 2 b := by
  have hsec : xPrep b c r ∈ (recordProtocol (K := K) J ħ T i τR).outcomeSector b :=
    register_written hJ hħ hr b i le_rfl
  exact (recordProtocol J ħ T i τR).record_persists_on_interval
    (recordProtocol_pointerInvariant J ħ T i τR) hsec ht₁ ht₂

/-! ### Demonstrated influence: the records depend on the message -/

/-- ★★ **The reception record depends on the message**: two preparations identical except for the
occupancy of `A` (`msgConfig_siteB`) leave the reception register in disjoint pointer arcs. -/
theorem reception_depends_on_message {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {t : OnticTime} (ht : hopTime J ħ ≤ t) :
    (xEvolve J ħ T (-1) t (xPrep 1 c r)).2.2 1 ∈ pointerArc 2 1
      ∧ (xEvolve J ħ T (-1) t (xPrep 0 c r)).2.2 1 ∈ pointerArc 2 0
      ∧ (xEvolve J ħ T (-1) t (xPrep 1 c r)).2.2 1 ≠ (xEvolve J ħ T (-1) t (xPrep 0 c r)).2.2 1 := by
  have h1 := register_written (T := T) (c := c) hJ hħ hr 1 1 ht
  have h0 := register_written (T := T) (c := c) hJ hħ hr 0 1 ht
  refine ⟨h1, h0, fun h => ?_⟩
  rw [h] at h1
  exact Set.disjoint_left.mp (pointerArc_pairwiseDisjoint (by decide : (1 : Fin 2) ≠ 0)) h1 h0

/-- The return record depends on the message in the same way. -/
theorem return_depends_on_message {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) {t : OnticTime}
    (ht : roundTrip J ħ ≤ t) :
    (xEvolve J ħ T (-1) t (xPrep 1 c r)).2.2 2 ≠ (xEvolve J ħ T (-1) t (xPrep 0 c r)).2.2 2 := by
  have h1 := register_written (T := T) (c := c) hJ hħ hr 1 2 ht
  have h0 := register_written (T := T) (c := c) hJ hħ hr 0 2 ht
  intro h
  rw [h] at h1
  exact Set.disjoint_left.mp (pointerArc_pairwiseDisjoint (by decide : (1 : Fin 2) ≠ 0)) h1 h0

/-! ### Occurrences and the forgetful map to record events -/

/-- **An occurrence** along the constructed evolution: which register writes, at which site, at
which time, recording which message. Richer than `CV.RecordEvent`, which keeps region and period
only. -/
structure Occurrence where
  /-- The register that writes. -/
  register : Fin 3
  /-- The site of the write. -/
  site : Fin 2
  /-- The ontic time of the write. -/
  time : ℝ
  /-- The message the write records. -/
  message : Fin 2

/-- The emission of message `b` at `A`, time `0`. -/
def emission (b : Fin 2) : Occurrence := ⟨0, 0, 0, b⟩

/-- The reception of message `b` at `B`, time `τ_hop`. -/
noncomputable def reception (J ħ : ℝ) (b : Fin 2) : Occurrence := ⟨1, 1, hopTime J ħ, b⟩

/-- The return of message `b` at `A`, time `2 τ_hop`. -/
noncomputable def returnOcc (J ħ : ℝ) (b : Fin 2) : Occurrence := ⟨2, 0, roundTrip J ħ, b⟩

/-- **The forgetful map to `CV.RecordEvent`**: the region is the site, and the period label is the
tick count of the physical clock in the arena at the occurrence time. -/
noncomputable def eventOf (J ħ T : ℝ) (x : XArena K) (o : Occurrence) : RecordEvent 2 :=
  ⟨{o.site}, tickCount (xEvolve J ħ T (-1) o.time x).2.1⟩

/-- The clock in the arena, run from `−1`, has the slots of the clock run from `0`. -/
theorem tickCount_clock_neg_one {T : ℝ} (hT : 0 < T) (t : OnticTime) (c : ClockArena K) :
    tickCount (clockEvolve T (-1) t c) = tickCount (clockEvolve T 0 t c) := by
  have h : (clockEvolve T (-1) t c).2 = (clockEvolve T 0 t c).2 := by
    funext n
    rw [clockEvolve_slot, clockEvolve_slot,
      winElapsed_of_le hT (n := n) (u := -1)
        (by linarith [mul_nonneg (Nat.cast_nonneg (n : ℕ)) hT.le]),
      winElapsed_of_le hT (n := n) (u := 0) (by positivity)]
  unfold tickCount
  rw [h]

/-- Under the calibration `T = τ_hop`, emission is at period `0`. -/
theorem eventOf_emission {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    eventOf J ħ T x (emission b) = ⟨{0}, 0⟩ := by
  have hTpos : 0 < T := hT ▸ hopTime_pos hJ hħ
  unfold eventOf emission
  rw [xEvolve_clock, tickCount_clock_neg_one hTpos]
  congr 1
  have h := tickCount_at_period hK hTpos hx.1 (m := 0) (Nat.zero_le _)
  rw [Nat.cast_zero, zero_mul] at h
  exact h

/-- Under the calibration `T = τ_hop`, reception is at period `1`. -/
theorem eventOf_reception {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 1 ≤ K)
    {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    eventOf J ħ T x (reception J ħ b) = ⟨{1}, 1⟩ := by
  have hTpos : 0 < T := hT ▸ hopTime_pos hJ hħ
  unfold eventOf reception
  rw [xEvolve_clock, tickCount_clock_neg_one hTpos]
  congr 1
  have h := tickCount_at_period (Nat.lt_of_lt_of_le Nat.zero_lt_one hK) hTpos hx.1 (m := 1) hK
  show tickCount (clockEvolve T 0 (hopTime J ħ) x.2.1) = 1
  rw [← hT]
  rw [Nat.cast_one, one_mul] at h
  exact h

/-- Under the calibration `T = τ_hop`, the return is at period `2`. -/
theorem eventOf_return {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 2 ≤ K)
    {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    eventOf J ħ T x (returnOcc J ħ b) = ⟨{0}, 2⟩ := by
  have hTpos : 0 < T := hT ▸ hopTime_pos hJ hħ
  unfold eventOf returnOcc
  rw [xEvolve_clock, tickCount_clock_neg_one hTpos]
  congr 1
  have h := tickCount_at_period (Nat.lt_of_lt_of_le Nat.zero_lt_two hK) hTpos hx.1 (m := 2) hK
  show tickCount (clockEvolve T 0 (roundTrip J ħ) x.2.1) = 2
  rw [roundTrip, ← hT]
  push_cast at h
  exact h

/-- The coupling graph of the experiment: the one hop edge `(A, B)`. -/
def hopGraph : Finset (Fin 2 × Fin 2) := {(0, 1)}

/-- ★★ **The causal chain**: `emission ⪯ reception ⪯ return` under `CausalPrecedes` on the hop
graph, and `emission ⪯ return` by the corpus's transitivity. -/
theorem causal_chain {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 2 ≤ K)
    {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    CausalPrecedes hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (reception J ħ b))
      ∧ CausalPrecedes hopGraph (eventOf J ħ T x (reception J ħ b))
          (eventOf J ħ T x (returnOcc J ħ b))
      ∧ CausalPrecedes hopGraph (eventOf J ħ T x (emission b))
          (eventOf J ħ T x (returnOcc J ħ b)) := by
  have hK0 : 0 < K := by omega
  have hK1 : 1 ≤ K := by omega
  rw [eventOf_emission hJ hħ hT hK0 hx b, eventOf_reception hJ hħ hT hK1 hx b,
    eventOf_return hJ hħ hT hK hx b]
  have h01 : CausalPrecedes hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{1}, 1⟩ := by
    refine ⟨Nat.zero_le _, ?_⟩
    show ({1} : Finset (Fin 2)) ⊆ graphBall hopGraph {0} (1 - 0)
    decide
  have h12 : CausalPrecedes hopGraph (⟨{1}, 1⟩ : RecordEvent 2) ⟨{0}, 2⟩ := by
    refine ⟨by norm_num, ?_⟩
    show ({0} : Finset (Fin 2)) ⊆ graphBall hopGraph {1} (2 - 1)
    decide
  exact ⟨h01, h12, causalPrecedes_trans h01 h12⟩

/-! ### The record predicates factor through a macroscopic projection -/

/-- The record events: register `i` displays bit `j`. -/
def recordEvents (j : Fin 2) : Fin 3 → Set (XArena K) := fun i => {x | x.2.2 i ∈ pointerArc 2 j}

theorem measurableSet_recordEvents (j : Fin 2) (i : Fin 3) :
    MeasurableSet (recordEvents (K := K) j i) :=
  ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) (measurableSet_pointerArc j)

/-- **The macroscopic coordinate of the experiment's records**: the pattern projection of the three
"register `i` displays `j`" events. -/
noncomputable def recordPattern (j : Fin 2) : MacroProjection (XArena K) (Fin 3 → Bool) :=
  patternProjection (recordEvents j) (measurableSet_recordEvents j)

/-- ★ **Every record predicate factors through the macroscopic projection.** -/
theorem factorsThrough_recordEvents (j : Fin 2) (i : Fin 3) :
    FactorsThrough (recordPattern (K := K) j) (recordEvents j i) :=
  factorsThrough_patternMap (recordEvents j) i

/-! ### The package -/

/-- ★★★ **The recorded exchange.** On the common arena with its one two-time, measure-preserving
evolution: from the ready preparation with message `b`, the three registers are written with `b`
at `0`, `τ_hop`, `2 τ_hop` and persist; the reception register distinguishes the two messages;
under the calibration `T = τ_hop` the occurrences map to record events at periods `0, 1, 2` that
form the chain `emission ⪯ reception ⪯ return` on the hop graph; and the record predicates factor
through the pattern projection. -/
theorem recorded_exchange {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 2 ≤ K)
    {c : ClockArena K} (hc : c ∈ ClockReady K) {r : Fin 3 → LF4.KTorus}
    (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) :
    (∀ s t u : OnticTime, xEvolve (K := K) J ħ T t u ∘ xEvolve J ħ T s t = xEvolve J ħ T s u)
      ∧ (∀ (s t : OnticTime) (p₀ : FieldArena 2 2), MeasurePreserving (xEvolve (K := K) J ħ T s t)
          ((fsMeasure p₀).prod volume) ((fsMeasure p₀).prod volume))
      ∧ (∀ (i : Fin 3) (t : OnticTime), readTime J ħ i ≤ t →
          (xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i ∈ pointerArc 2 b)
      ∧ (∀ t : OnticTime, hopTime J ħ ≤ t →
          (xEvolve J ħ T (-1) t (xPrep 1 c r)).2.2 1 ≠ (xEvolve J ħ T (-1) t (xPrep 0 c r)).2.2 1)
      ∧ eventOf J ħ T (xPrep b c r) (emission b) = ⟨{0}, 0⟩
      ∧ eventOf J ħ T (xPrep b c r) (reception J ħ b) = ⟨{1}, 1⟩
      ∧ eventOf J ħ T (xPrep b c r) (returnOcc J ħ b) = ⟨{0}, 2⟩
      ∧ CausalPrecedes hopGraph (eventOf J ħ T (xPrep b c r) (emission b))
          (eventOf J ħ T (xPrep b c r) (reception J ħ b))
      ∧ CausalPrecedes hopGraph (eventOf J ħ T (xPrep b c r) (reception J ħ b))
          (eventOf J ħ T (xPrep b c r) (returnOcc J ħ b))
      ∧ (∀ (j : Fin 2) (i : Fin 3), FactorsThrough (recordPattern (K := K) j) (recordEvents j i)) := by
  have hx : xPrep b c r ∈ XReady K := ⟨hc, hr⟩
  have hK0 : 0 < K := by omega
  have hK1 : 1 ≤ K := by omega
  refine ⟨xEvolve_comp J ħ T, fun s t p₀ => xEvolve_measurePreserving J ħ T s t p₀,
    fun i t ht => register_written hJ hħ hr b i ht,
    fun t ht => (reception_depends_on_message hJ hħ hr ht).2.2,
    eventOf_emission hJ hħ hT hK0 hx b, eventOf_reception hJ hħ hT hK1 hx b,
    eventOf_return hJ hħ hT hK hx b, (causal_chain hJ hħ hT hK hx b).1,
    (causal_chain hJ hħ hT hK hx b).2.1, fun j i => factorsThrough_recordEvents j i⟩

end CSD.RecordLayer

end
