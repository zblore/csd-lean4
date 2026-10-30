/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MovingClock
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# One transported clock, its ticks and passages as record writes

**Category:** 7-SigmaLayer (the record layer). BACKLOG #242 (the author's fourth operational-geometry
brief, step 2), for the control candidate (A).

~~#241~~ built the control candidate: a free massive device on sites as unit cells, carrying #201's
hand clock and a memory, with test detectors integrating its occupancy. Here the acceptance of the
brief's step 2 is met for it: **one measurable two-time evolution of one arena moves the device and
writes its ticks and its passages, as actual record occurrences** (#191), with a concrete instance in
motion.

## The arena

* ★ `measurable_occTime` — the occupancy time is measurable in the device's start and velocity;
* `TransportArena` (clock × phase space × memory × registers, as a product), `toArena`, `ofArena`;
* `transportFlow`, `transportEvolve`, `transportEvolve_self`, `transportEvolve_comp` — #241's
  `movingFlow` as two-time dynamics; ★ `measurable_transportFlow` — **each step is measurable**;
  `clock_transportFlow`, `pos_transportFlow`, `det_transportFlow`.

## The writes

* ★★★ `movingTick` — **tick `n` of the transported clock as an `ActualOccurrence`** of that evolution,
  at the site the device occupies when it completes;
* `passageRead`, `measurable_passageRead`; ★★★ `passageWrite` — **the passage through site `k` as an
  `ActualOccurrence`**: a detector with threshold `0 < θ ≤ g_d m/p` is not written before the device
  arrives and is written from its departure on;
* ★★★ `transported_clock` — **the concrete instance**: mass and momentum `1`, start `1/2`; the passage
  at site `1` is written over `[1/2, 3/2]`, every tick `1 ≤ n ≤ K − 1` is written, the position is
  `1/2 + t`, the clock and the motion do not depend on the registers, the memory is kept, and the clock
  reads within `τ_tick + 1/(2ω)`.

## Honest scope

⚠️ **The disturbance is zero because the detectors are test detectors.** They integrate the occupancy
and are never read back; generating them by a coupling, with the back-reaction it implies on the
device, is #251.

⚠️ **The tick's site is supplied.** `movingTick` takes the site at which the write completes as data;
`siteOf` (#241) computes it from the position, which is exact here.

⚠️ **This is the control (A).** The test candidate (B), the Dirac packet (~~#249~~, ~~#250~~), has its
detector readout in #252.

References: `specs/BACKLOG.md` #242, #241, #251, #252, #243, #191, #201, #39;
`RecordLayer/MovingClock.lean` (`movingFlow`, `det_movingFlow_passage`, `abs_handReading_sub_le`);
`RecordLayer/HandClock.lean` (`hand_before_tick`, `hand_at_tick`); `RecordLayer/RecordOccurrence.lean`
(`ActualOccurrence`, `IsRecordWrite`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Occupancy is measurable in the device's state -/

/-- ★ **The occupancy time is a measurable function of the start and the velocity.** -/
theorem measurable_occTime (k : ℤ) (t : ℝ) :
    Measurable fun w : ℝ × ℝ => occTime k w.1 w.2 t := by
  have hF : StronglyMeasurable (Function.uncurry fun (w : ℝ × ℝ) (s : ℝ) => siteInd k (w.1 + w.2 * s)) := by
    refine Measurable.stronglyMeasurable ?_
    have h : Measurable fun p : (ℝ × ℝ) × ℝ => p.1.1 + p.1.2 * p.2 := by fun_prop
    exact (measurable_const.indicator measurableSet_Ico).comp h
  have h1 := (hF.integral_prod_right (ν := volume.restrict (Ioc 0 t))).measurable
  have h2 := (hF.integral_prod_right (ν := volume.restrict (Ioc t 0))).measurable
  have : (fun w : ℝ × ℝ => occTime k w.1 w.2 t)
      = fun w => (∫ s in Ioc 0 t, siteInd k (w.1 + w.2 * s)) - ∫ s in Ioc t 0, siteInd k (w.1 + w.2 * s) := by
    funext w
    rfl
  rw [this]
  exact h1.sub h2

/-! ### The arena -/

/-- **The transport arena**: the carried clock, the device's position and momentum, the carried
memory, the detectors' registers — `MovingState` as a product, so that it is a measurable space. -/
abbrev TransportArena (L : ℕ) : Type := ActiveArena × (ℝ × ℝ) × LF4.KTorus × (Fin L → ℝ)

variable {L : ℕ}

/-- The state read as a point of the arena. -/
def toArena (z : MovingState L) : TransportArena L := (z.clock, (z.pos, z.mom), z.mem, z.det)

/-- The point read as a state. -/
def ofArena (x : TransportArena L) : MovingState L :=
  ⟨x.1, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2⟩

theorem toArena_ofArena (x : TransportArena L) : toArena (ofArena x) = x := rfl

theorem ofArena_toArena (z : MovingState L) : ofArena (toArena z) = z := rfl

section Flow

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- **The moving clock's flow on the arena**: #241's `movingFlow`, read on the product. -/
noncomputable def transportFlow (t : ℝ) (x : TransportArena L) : TransportArena L :=
  toArena (movingFlow J ħ g hf m gd t (ofArena x))

/-- The two-time evolution. -/
noncomputable def transportEvolve (s t : OnticTime) : TransportArena L → TransportArena L :=
  transportFlow J ħ g hf m gd (t - s)

theorem transportEvolve_self (t : OnticTime) :
    transportEvolve J ħ g hf m gd t t = (id : TransportArena L → TransportArena L) := by
  funext x
  simp only [transportEvolve, transportFlow, sub_self, movingFlow_zero, id, toArena_ofArena]

theorem transportEvolve_comp (s t u : OnticTime) :
    transportEvolve J ħ g hf m gd t u ∘ transportEvolve J ħ g hf m gd s t
      = (transportEvolve J ħ g hf m gd s u : TransportArena L → TransportArena L) := by
  funext x
  simp only [transportEvolve, transportFlow, Function.comp, ofArena_toArena]
  rw [show u - s = (t - s) + (u - t) by ring, movingFlow_add]
  rfl

/-- ★ **Each step of the evolution is measurable.** -/
theorem measurable_transportFlow (hf1 : ContDiff ℝ 1 f) (t : ℝ) :
    Measurable (transportFlow (L := L) J ħ g hf m gd t) := by
  have hc : Measurable fun x : TransportArena L => activeFlow J ħ g hf t x.1 :=
    (continuous_activeFlow J ħ g hf hf1 t).measurable.comp measurable_fst
  have hp : Measurable fun x : TransportArena L => (x.2.1.1 + x.2.1.2 / m * t, x.2.1.2) := by
    fun_prop
  have hdet : Measurable fun x : TransportArena L =>
      fun k : Fin L => x.2.2.2 k + gd * occTime ((k : ℕ) : ℤ) x.2.1.1 (x.2.1.2 / m) t := by
    refine measurable_pi_iff.2 fun k => ?_
    have ho := (measurable_occTime ((k : ℕ) : ℤ) t).comp
      (by fun_prop : Measurable fun x : TransportArena L => (x.2.1.1, x.2.1.2 / m))
    have hd : Measurable fun x : TransportArena L => x.2.2.2 k :=
      (measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact hd.add (ho.const_mul gd)
  exact hc.prodMk (hp.prodMk ((by fun_prop : Measurable fun x : TransportArena L => x.2.2.1).prodMk
    hdet))

theorem clock_transportFlow (t : ℝ) (x : TransportArena L) :
    (transportFlow J ħ g hf m gd t x).1 = activeFlow J ħ g hf t x.1 := rfl

theorem pos_transportFlow (t : ℝ) (x : TransportArena L) :
    (transportFlow J ħ g hf m gd t x).2.1.1 = x.2.1.1 + x.2.1.2 / m * t := rfl

theorem det_transportFlow (t : ℝ) (x : TransportArena L) (k : Fin L) :
    (transportFlow J ħ g hf m gd t x).2.2.2 k
      = (movingFlow J ħ g hf m gd t (ofArena x)).det k := rfl

/-! ### The ticks as record writes -/

/-- ★★★ **Tick `n` of the transported clock as an actual occurrence**: the same evolution that moves
the device writes its hand's `n`-th arc, at the site the device occupies when the write completes
(`hsite`: inside the network). -/
noncomputable def movingTick (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K)
    (x₀ p₀ : ℝ) (mem₀ : LF4.KTorus) (det₀ : Fin L → ℝ) (site : Fin L) :
    ActualOccurrence (TransportArena L) ℕ L where
  evolve := transportEvolve J ħ g hf m gd
  evolve_self := transportEvolve_self J ħ g hf m gd
  evolve_comp := transportEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_transportFlow J ħ g hf m gd hf1 (t - s)
  readout := fun x => handCount K x.1.2
  measurable_readout := (measurable_handCount K).comp (measurable_snd.comp measurable_fst)
  ready := {x | x.1.2 ∈ handReady K}
  measurableSet_ready := (measurable_snd.comp measurable_fst) (measurableSet_handReady K)
  prep := ((msgPoint 1, q), (x₀, p₀), mem₀, det₀)
  prep_mem := hq
  site := {site}
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
        show handCount K (transportFlow J ħ g hf m gd (t - 0) _).1.2 ≠ n
        rw [sub_zero, clock_transportFlow]
        exact (hand_before_tick J ħ g hf hJ hħ hK hq hκ hn1 hnK ht0 ht).ne
      holds := fun t ht₁ ht₂ => by
        show handCount K (transportFlow J ħ g hf m gd (t - 0) _).1.2 = n
        rw [sub_zero, clock_transportFlow]
        exact hand_at_tick J ħ g hf hJ hħ hK hq hκ hnK ht₁ ht₂ }

/-! ### The passages as record writes -/

/-- **A detector's readout**: whether its register has reached the threshold `θ`. -/
noncomputable def passageRead (θ : ℝ) (k : Fin L) (x : TransportArena L) : ℕ :=
  if θ ≤ x.2.2.2 k then 1 else 0

theorem measurable_passageRead (θ : ℝ) (k : Fin L) : Measurable (passageRead (L := L) θ k) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const
    ((measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

/-- ★★★ **The device's passage through site `k` as an actual occurrence**: the detector at `k`,
prepared at zero with a threshold `0 < θ ≤ g_d m / p`, is written while the device crosses the
site — not before it arrives, and from its departure on. -/
noncomputable def passageWrite (hf1 : ContDiff ℝ 1 f) (θ : ℝ) (hθ0 : 0 < θ) (k : Fin L)
    (c₀ : ActiveArena) (x₀ p₀ : ℝ) (mem₀ : LF4.KTorus) (det₀ : Fin L → ℝ) (hdet : det₀ k = 0)
    (hv : 0 < p₀ / m) (hx : x₀ < (k : ℕ)) (hθ : θ ≤ gd * (p₀ / m)⁻¹) :
    ActualOccurrence (TransportArena L) ℕ L where
  evolve := transportEvolve J ħ g hf m gd
  evolve_self := transportEvolve_self J ħ g hf m gd
  evolve_comp := transportEvolve_comp J ħ g hf m gd
  measurable_evolve := fun s t => measurable_transportFlow J ħ g hf m gd hf1 (t - s)
  readout := passageRead θ k
  measurable_readout := measurable_passageRead θ k
  ready := {x | x.2.2.2 k = 0}
  measurableSet_ready := measurableSet_eq_fun
    ((measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    measurable_const
  prep := (c₀, (x₀, p₀), mem₀, det₀)
  prep_mem := hdet
  site := {k}
  start := 0
  value := 1
  writeStart := (((k : ℕ) : ℝ) - x₀) / (p₀ / m)
  writeEnd := (((k : ℕ) : ℝ) + 1 - x₀) / (p₀ / m)
  window := 1 / (p₀ / m)
  isWrite :=
    { start_le := div_nonneg (by linarith) hv.le
      interval := div_le_div_of_nonneg_right (by linarith) hv.le
      window_nonneg := by positivity
      before := fun t ht0 ht => by
        have hb : x₀ + p₀ / m * t < (k : ℕ) := by
          rw [lt_div_iff₀ hv] at ht
          linarith
        have hpass := (det_movingFlow_passage J ħ g hf m gd
          (z := ofArena (c₀, (x₀, p₀), mem₀, det₀)) hv k ht0).1 hb
        show passageRead θ k (transportFlow J ħ g hf m gd (t - 0) _) ≠ 1
        rw [sub_zero, passageRead, det_transportFlow, hpass]
        show (if θ ≤ det₀ k then 1 else 0) ≠ 1
        rw [hdet, ite_eq_right (by linarith)]
        decide
      holds := fun t ht₁ _ => by
        have hc : ((k : ℕ) : ℝ) + 1 ≤ x₀ + p₀ / m * t := by
          rw [div_le_iff₀ hv] at ht₁
          linarith
        have ht0 : 0 ≤ t := (div_nonneg (by linarith) hv.le).trans ht₁
        have hpass := (det_movingFlow_passage J ħ g hf m gd
          (z := ofArena (c₀, (x₀, p₀), mem₀, det₀)) hv k ht0).2 hx hc
        show passageRead θ k (transportFlow J ħ g hf m gd (t - 0) _) = 1
        rw [sub_zero, passageRead, det_transportFlow, hpass]
        show (if θ ≤ det₀ k + gd * (p₀ / m)⁻¹ then 1 else 0) = 1
        rw [hdet, zero_add, ite_eq_left hθ] }

/-- ★★★ **One transported clock (#242), with a concrete moving instance.** Mass `1`, momentum `1`,
starting in the middle of site `0` on a network of at least two sites, the device carrying #201's hand
clock: one measurable two-time evolution of the arena moves it and

* writes the passage record at site `1` from its arrival at `1/2` to its departure at `3/2`, held
  thereafter (a detector of gain `g_d > 0` and threshold `g_d`);
* writes its hand's tick `n` for every `1 ≤ n ≤ K − 1`, with the values distinct;
* moves at velocity `1` (its position `1/2 + t`), its clock and motion undisturbed by the detectors'
  registers (they are written, never read back — the model's disturbance is zero);
* keeps its memory, and reads its clock within `τ_tick + 1/(2ω)` throughout (#241). -/
theorem transported_clock (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) (hL : 2 ≤ L) (hgd : 0 < gd)
    (mem₀ : LF4.KTorus) :
    let k : Fin L := ⟨1, by omega⟩
    let o := passageWrite J ħ g hf 1 gd hf1 gd hgd k (msgPoint 1, q) (1 / 2) 1 mem₀ 0 rfl
      (by norm_num) (by norm_num [k]) (by norm_num)
    o.writeStart = 1 / 2 ∧ o.writeEnd = 3 / 2 ∧ o.value = 1 ∧ o.site = {k}
    ∧ (∀ n (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K),
        (movingTick J ħ g hf 1 gd hJ hħ hf1 hK hq hκ hslow hn1 hnK (1 / 2) 1 mem₀ 0 k).value = n)
    ∧ (∀ t, (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, 0)).2.1.1
        = 1 / 2 + t)
    ∧ (∀ t (det₁ : Fin L → ℝ),
        (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, det₁)).1
          = (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, 0)).1
        ∧ (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, det₁)).2.1
          = (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, 0)).2.1)
    ∧ (∀ t, (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, 0)).2.2.1 = mem₀)
    ∧ (∀ t, 0 ≤ t → t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q) →
        |handReading K (tickTime K (handRate J ħ g hf q))
          (transportFlow (L := L) J ħ g hf 1 gd t ((msgPoint 1, q), (1 / 2, 1), mem₀, 0)).1.2 - t|
          ≤ tickTime K (handRate J ħ g hf q) + 1 / (2 * handFreq J ħ g hf q)) := by
  intro k o
  refine ⟨by simp [o, passageWrite, k]; norm_num, by simp [o, passageWrite, k]; norm_num, rfl, rfl,
    fun n _ _ => rfl, fun t => by simp [pos_transportFlow], fun t _ => ⟨rfl, rfl⟩, fun t => rfl,
    fun t ht0 ht => ?_⟩
  rw [clock_transportFlow]
  exact abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht

end Flow

end CSD.RecordLayer

end
