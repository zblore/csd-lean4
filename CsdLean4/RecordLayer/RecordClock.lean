/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ShearWitness
public import CsdLean4.RecordLayer.RecordPersistence

/-!
# The record clock: a periodic register plus fresh slots, read as a tick count

**Category:** 7-SigmaLayer (the record layer — the first physical clock in the corpus).
BACKLOG #185 (out of #39; the third of #183–#189).

A periodic subsystem does not count its cycles: after one period it is back where it was
(`osc_period`). A clock is a periodic register **together with fresh record slots**, one written per
cycle, and its reading is the number of written slots. This file builds that clock on one arena,
with the record machinery of `ShearWitness.lean` (the arcs, `pshift`, `rep`) and presents each slot
as a `MeasurementProtocol`, so that the corpus's own persistence theorem applies to every tick.

**The arena.** `ClockArena K = KTorus × (Fin K → KTorus)`: the oscillator register and `K` slot
registers, each a copy of the pointer torus. `K` is the **observation horizon**: the apparatus
memory, one slot per tick.

**The dynamics.** `clockEvolve T s t`: the oscillator turns at rate `1/T`; slot `n` is translated
by the gap `δ = shearGap K` during its own window `[n T, (n+1) T]` (`winElapsed`), from the ready
arc `(0, ε]` into the written arc `(δ, δ + ε]`, and is frozen outside its window. It is a two-time
propagator (`clockEvolve_self`, `clockEvolve_comp`), measurable, and preserves Liouville measure
on the arena (`clockEvolve_measurePreserving`). ⚠️ **The window schedule is a modelling input
indexed by ontic time `t_Σ`**, stated as such: it is the switching of the slot couplings, exactly
as `elapsed` is the switching of the shear coupling in `ShearWitness.lean`. It is not emergent
time, and this file does not call it that.

**The readout.** `tickCount x` is the number of slots in the written arc; `tickReading τ_tick x =
tickCount x · τ_tick` is the calibrated reading, with the **physical count** and the **unit**
`τ_tick > 0` kept apart.

* `ClockArena`, `winElapsed`, `clockEvolve`; `clockEvolve_self`, ★ `clockEvolve_comp`,
  `measurable_clockEvolve`, ★ `clockEvolve_measurePreserving` — **a dynamics**;
* `osc_period` — **the oscillator alone cannot count**: its state after one period is its state;
* `writtenArc`, `writtenArc_eq_pointerArc_zero`, `readyArc_disjoint_writtenArc`;
* ★ `slot_ready_before`, ★ `slot_written_after`, ★ `slot_written_mono` — **a concrete evolution
  writes tick `n` from the ready preparation**, during window `n`, once and for all;
* `tickCount`, ★ `measurable_tickCount` — **the readout is well defined and measurable**;
  `tickCount_le_horizon`;
* ★★ `tickCount_mono` — **the tick count is nondecreasing**;
* ★★ `tickCount_ge`, `tickCount_le`, `tickCount_at_period` — **the relation between tick count and
  the evolution parameter**: after `n + 1` full periods at least `n + 1` ticks, before `n` periods at
  most `n`, and exactly `m` at time `m T`;
* ★ `successive_ticks_distinguishable` — successive ticks occupy distinct register states;
* `tickProtocol n` — **each slot is a `MeasurementProtocol`**, with `tickProtocol_pointerInvariant`
  and ★ `tick_persists` — tick `n` persists through the window, by the corpus's
  `record_persists_on_interval`, not by a fresh argument;
* `tickReading`, ★★ `abs_tickReading_sub_lt` — **calibrated with `τ_tick = T`, the clock reads
  within one tick of `t_Σ`** over the horizon; ★★★ `record_clock` — the package.

## Honest scope

* ⚠️ The writes are *scheduled*, not triggered by the oscillator's phase: slot `n` moves during the
  `n`-th period because the schedule says so, and the oscillator's role is to define the period.
  A counter whose next slot is armed by the previous slot's record (a ripple counter) would make
  the trigger dynamical; it is not built here.
* During its window a slot is in transit and may or may not read as written; the theorems about
  the count are stated at the window boundaries (`tickCount_ge`, `tickCount_le`) and the count is
  monotone throughout (`tickCount_mono`). Within one tick of `t_Σ` is the honest resolution.
* The Hamiltonian generation of `clockEvolve` is not formalised, exactly as for `shearEvolve` and
  `swapEvolve` (`R-016′`); the propagator is given and shown to be a measure-preserving two-time
  dynamics.
* `K ≥ 1` is needed wherever a slot is written (`gap_add_width_le_one`); with `K = 0` there is no
  memory and nothing is claimed.

References: `specs/BACKLOG.md` #185, #183, #186, #39; `RecordLayer/ShearWitness.lean` (`pshift`,
`readyArc`, `pointerArc`, `shearGap`, `shearWidth`, `rep_pshift_of_mem`, `measurePreserving_pshift`);
`RecordLayer/SwapWitness.lean` (the slot bank); `RecordLayer/MeasurementProtocol.lean`;
`RecordLayer/RecordPersistence.lean` (`record_persists_on_interval`).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K : ℕ}

/-! ### The arena and the window schedule -/

/-- **The clock arena**: the oscillator register and `K` slot registers. `K` is the horizon. -/
abbrev ClockArena (K : ℕ) := LF4.KTorus × (Fin K → LF4.KTorus)

/-- The fraction of slot `n`'s window `[n T, (n+1) T]` elapsed by time `u`. -/
noncomputable def winElapsed (T : ℝ) (n : ℕ) (u : ℝ) : ℝ := max 0 (min ((u - n * T) / T) 1)

theorem winElapsed_nonneg (T : ℝ) (n : ℕ) (u : ℝ) : 0 ≤ winElapsed T n u := le_max_left _ _

theorem winElapsed_le_one (T : ℝ) (n : ℕ) (u : ℝ) : winElapsed T n u ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem winElapsed_of_le {T : ℝ} (hT : 0 < T) {n : ℕ} {u : ℝ} (hu : u ≤ n * T) :
    winElapsed T n u = 0 := by
  unfold winElapsed
  have h : (u - n * T) / T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
  rw [min_eq_left (h.trans zero_le_one), max_eq_left h]

theorem winElapsed_of_ge {T : ℝ} (hT : 0 < T) {n : ℕ} {u : ℝ} (hu : (n + 1) * T ≤ u) :
    winElapsed T n u = 1 := by
  unfold winElapsed
  have h : 1 ≤ (u - n * T) / T := by
    rw [le_div_iff₀ hT]
    linarith
  rw [min_eq_right h, max_eq_right zero_le_one]

theorem winElapsed_mono {T : ℝ} (hT : 0 < T) (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    winElapsed T n s ≤ winElapsed T n t := by
  unfold winElapsed
  apply max_le_max le_rfl
  apply min_le_min _ le_rfl
  rw [div_le_div_iff_of_pos_right hT]
  linarith

/-! ### The propagator -/

/-- **The clock propagator** over `[s, t]`: the oscillator turns by `(t − s)/T`; slot `n` is
translated by the gap `δ` times the fraction of its window that elapsed. -/
noncomputable def clockEvolve (T : ℝ) (s t : OnticTime) : ClockArena K → ClockArena K :=
  fun x => (pshift ((t - s) / T) x.1,
    fun n => pshift ((winElapsed T n t - winElapsed T n s) * shearGap K) (x.2 n))

theorem clockEvolve_osc (T : ℝ) (s t : OnticTime) (x : ClockArena K) :
    (clockEvolve T s t x).1 = pshift ((t - s) / T) x.1 := rfl

theorem clockEvolve_slot (T : ℝ) (s t : OnticTime) (x : ClockArena K) (n : Fin K) :
    (clockEvolve T s t x).2 n
      = pshift ((winElapsed T n t - winElapsed T n s) * shearGap K) (x.2 n) := rfl

theorem clockEvolve_self (T : ℝ) (t : OnticTime) : clockEvolve (K := K) T t t = id := by
  funext x
  simp [clockEvolve]

/-- ★ **The two-time composition law.** -/
theorem clockEvolve_comp (T : ℝ) (s t u : OnticTime) :
    clockEvolve (K := K) T t u ∘ clockEvolve T s t = clockEvolve T s u := by
  funext x
  simp only [Function.comp_apply, clockEvolve, pshift_add]
  refine Prod.ext ?_ ?_
  · simp only
    congr 1
    ring
  · funext n
    simp only
    congr 1
    ring

theorem measurable_pshift (a : ℝ) : Measurable (pshift a) :=
  (continuous_pshift_uncurry.comp (Continuous.prodMk continuous_const continuous_id)).measurable

theorem measurable_clockEvolve (T : ℝ) (s t : OnticTime) :
    Measurable (clockEvolve (K := K) T s t) := by
  refine Measurable.prodMk ((measurable_pshift _).comp measurable_fst) ?_
  exact measurable_pi_iff.mpr fun n =>
    (measurable_pshift _).comp ((measurable_pi_apply n).comp measurable_snd)

/-- ★ **The clock propagator preserves Liouville measure on the arena**: it is a dynamics. -/
theorem clockEvolve_measurePreserving (T : ℝ) (s t : OnticTime) :
    MeasurePreserving (clockEvolve (K := K) T s t) volume volume := by
  have h : clockEvolve (K := K) T s t
      = Prod.map (pshift ((t - s) / T))
          (fun v : Fin K → LF4.KTorus => fun n : Fin K =>
            pshift ((winElapsed T n t - winElapsed T n s) * shearGap K) (v n)) := rfl
  rw [h, Measure.volume_eq_prod, volume_pi]
  exact (measurePreserving_pshift _).prod
    (measurePreserving_pi _ _ fun n => measurePreserving_pshift _)

/-! ### The oscillator alone cannot count -/

/-- **After one period the oscillator is back where it was**: a periodic subsystem does not count
its cycles. This is why the slots are there. -/
theorem osc_period {T : ℝ} (hT : 0 < T) (t : ℝ) (q : LF4.KTorus) :
    pshift ((t + T) / T) q = pshift (t / T) q := by
  have h : (t + T) / T = t / T + 1 := by
    field_simp
  rw [h]
  simp only [pshift]
  rw [AddCircle.coe_add_period]

/-! ### The written arc -/

/-- The arc a slot occupies once its tick is written: `rep ∈ (δ, δ + ε]`. -/
noncomputable def writtenArc (K : ℕ) : Set LF4.KTorus :=
  {x | rep x.1 ∈ Ioc (shearGap K) (shearGap K + shearWidth K)}

theorem measurableSet_writtenArc : MeasurableSet (writtenArc K) :=
  (measurable_rep.comp measurable_fst) measurableSet_Ioc

/-- The written arc is the pointer arc of the first outcome. -/
theorem writtenArc_eq_pointerArc_zero (hK : 0 < K) : writtenArc K = pointerArc K ⟨0, hK⟩ := by
  ext x
  simp [writtenArc, pointerArc, shearAmt]

theorem readyArc_disjoint_writtenArc : Disjoint (readyArc K) (writtenArc K) := by
  refine Set.disjoint_left.mpr fun q hr hw => ?_
  change rep q.1 ∈ Ioc (0 : ℝ) (shearWidth K) at hr
  change rep q.1 ∈ Ioc (shearGap K) (shearGap K + shearWidth K) at hw
  have := shearWidth_lt_gap (K := K)
  linarith [hr.2, hw.1]

theorem gap_add_width_le_one (hK : 0 < K) : shearGap K + shearWidth K ≤ 1 := by
  have := shearAmt_add_width_le_one (K := K) ⟨0, hK⟩
  simpa [shearAmt] using this

/-! ### Writing one slot -/

/-- A ready slot shifted by a fraction `f ∈ [0, 1]` of the gap does not wrap: `rep` is additive. -/
theorem rep_pshift_ready (hK : 0 < K) {q : LF4.KTorus} (hq : q ∈ readyArc K) {f : ℝ}
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    rep (pshift (f * shearGap K) q).1 = rep q.1 + f * shearGap K := by
  apply rep_pshift_of_mem
  change rep q.1 ∈ Ioc (0 : ℝ) (shearWidth K) at hq
  have hg := shearGap_pos (K := K)
  have h1 := gap_add_width_le_one hK
  constructor
  · nlinarith [hq.1]
  · nlinarith [hq.2]

/-- ★ A ready slot shifted by the full gap is written. -/
theorem written_of_ready (hK : 0 < K) {q : LF4.KTorus} (hq : q ∈ readyArc K) :
    pshift (1 * shearGap K) q ∈ writtenArc K := by
  change rep (pshift (1 * shearGap K) q).1 ∈ Ioc (shearGap K) (shearGap K + shearWidth K)
  rw [rep_pshift_ready hK hq zero_le_one le_rfl]
  have hq' : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth K) := hq
  constructor <;> linarith [hq'.1, hq'.2]

/-- ★ Once a ready slot reads as written, it reads as written at every later fraction: the write
is monotone through the window. -/
theorem written_mono (hK : 0 < K) {q : LF4.KTorus} (hq : q ∈ readyArc K) {f g : ℝ} (hf0 : 0 ≤ f)
    (hfg : f ≤ g) (hg1 : g ≤ 1) (hw : pshift (f * shearGap K) q ∈ writtenArc K) :
    pshift (g * shearGap K) q ∈ writtenArc K := by
  change rep (pshift (f * shearGap K) q).1 ∈ Ioc (shearGap K) (shearGap K + shearWidth K) at hw
  change rep (pshift (g * shearGap K) q).1 ∈ Ioc (shearGap K) (shearGap K + shearWidth K)
  rw [rep_pshift_ready hK hq hf0 (hfg.trans hg1)] at hw
  rw [rep_pshift_ready hK hq (hf0.trans hfg) hg1]
  have hq' : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth K) := hq
  have hg := shearGap_pos (K := K)
  constructor
  · nlinarith [hw.1]
  · nlinarith [hq'.2]

/-! ### The ready preparation and the slots along the evolution -/

/-- **The ready preparation**: every slot in the ready arc. -/
def ClockReady (K : ℕ) : Set (ClockArena K) := {x | ∀ n, x.2 n ∈ readyArc K}

theorem measurableSet_clockReady : MeasurableSet (ClockReady K) := by
  have h : ClockReady K = Prod.snd ⁻¹' (Set.pi univ fun _ : Fin K => readyArc K) := by
    ext x
    simp [ClockReady]
  rw [h]
  exact measurable_snd (MeasurableSet.pi countable_univ fun _ _ => measurableSet_readyArc)

/-- Slot `n` along the evolution from time `0`. -/
theorem clockEvolve_slot_zero {T : ℝ} (hT : 0 < T) (t : OnticTime) (x : ClockArena K)
    (n : Fin K) :
    (clockEvolve T 0 t x).2 n = pshift (winElapsed T n t * shearGap K) (x.2 n) := by
  rw [clockEvolve_slot, winElapsed_of_le hT (n := n) (u := 0) (by positivity), sub_zero]

/-- ★ **Before its window, slot `n` is still ready.** -/
theorem slot_ready_before {T : ℝ} (hT : 0 < T) {x : ClockArena K} (hx : x ∈ ClockReady K)
    (n : Fin K) {t : OnticTime} (ht : t ≤ (n : ℕ) * T) :
    (clockEvolve T 0 t x).2 n ∈ readyArc K := by
  rw [clockEvolve_slot_zero hT, winElapsed_of_le hT ht, zero_mul, pshift_zero]
  exact hx n

/-- ★ **After its window, slot `n` is written**: the concrete evolution writes tick `n` from the
ready preparation. -/
theorem slot_written_after (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) (n : Fin K) {t : OnticTime} (ht : ((n : ℕ) + 1) * T ≤ t) :
    (clockEvolve T 0 t x).2 n ∈ writtenArc K := by
  rw [clockEvolve_slot_zero hT, winElapsed_of_ge hT ht]
  exact written_of_ready hK (hx n)

/-- ★ **A written tick stays written**: slot membership in the written arc is monotone in time. -/
theorem slot_written_mono (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) (n : Fin K) {s t : OnticTime} (hst : s ≤ t)
    (hw : (clockEvolve T 0 s x).2 n ∈ writtenArc K) :
    (clockEvolve T 0 t x).2 n ∈ writtenArc K := by
  rw [clockEvolve_slot_zero hT] at hw ⊢
  exact written_mono hK (hx n) (winElapsed_nonneg _ _ _) (winElapsed_mono hT n hst)
    (winElapsed_le_one _ _ _) hw

/-! ### The tick count -/

open Classical in
/-- **The tick count**: the number of slots in the written arc. -/
noncomputable def tickCount (x : ClockArena K) : ℕ :=
  (Finset.univ.filter fun n : Fin K => x.2 n ∈ writtenArc K).card

open Classical in
theorem tickCount_eq_sum (x : ClockArena K) :
    tickCount x = ∑ n : Fin K, if x.2 n ∈ writtenArc K then 1 else 0 := by
  classical
  unfold tickCount
  rw [Finset.card_filter]

/-- ★ **The readout is measurable.** -/
theorem measurable_tickCount : Measurable (tickCount (K := K)) := by
  classical
  have h : tickCount (K := K)
      = fun x => ∑ n : Fin K, if x.2 n ∈ writtenArc K then 1 else 0 := funext tickCount_eq_sum
  rw [h]
  refine Finset.measurable_sum _ fun n _ => ?_
  exact Measurable.ite (((measurable_pi_apply n).comp measurable_snd) measurableSet_writtenArc)
    measurable_const measurable_const

/-- The count never exceeds the horizon: finite memory. -/
theorem tickCount_le_horizon (x : ClockArena K) : tickCount x ≤ K := by
  classical
  unfold tickCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- ★★ **The tick count is nondecreasing** along the evolution from the ready preparation. -/
theorem tickCount_mono (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) {s t : OnticTime} (hst : s ≤ t) :
    tickCount (clockEvolve T 0 s x) ≤ tickCount (clockEvolve T 0 t x) := by
  classical
  unfold tickCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, slot_written_mono hK hT hx n hst hn.2⟩

/-- ★★ **After `n + 1` full periods, at least `n + 1` ticks.** -/
theorem tickCount_ge (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K} (hx : x ∈ ClockReady K)
    (n : Fin K) {t : OnticTime} (ht : ((n : ℕ) + 1) * T ≤ t) :
    (n : ℕ) + 1 ≤ tickCount (clockEvolve T 0 t x) := by
  classical
  unfold tickCount
  rw [← Fin.card_Iic n]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_Iic] at hk
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, slot_written_after hK hT hx k ?_⟩
  have hk' : ((k : ℕ) : ℝ) ≤ (n : ℕ) := by exact_mod_cast hk
  nlinarith

/-- ★★ **Before `n` periods, at most `n` ticks.** -/
theorem tickCount_le {T : ℝ} (hT : 0 < T) {x : ClockArena K} (hx : x ∈ ClockReady K) (n : ℕ)
    {t : OnticTime} (ht : t ≤ n * T) : tickCount (clockEvolve T 0 t x) ≤ n := by
  classical
  unfold tickCount
  rw [← Finset.card_range n]
  refine Finset.card_le_card_of_injOn (fun k : Fin K => (k : ℕ)) ?_ Fin.val_injective.injOn
  intro k hk
  rw [Finset.mem_coe, Finset.mem_filter] at hk
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra! hkn
  have hkn' : (n : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hkn
  have hready : (clockEvolve T 0 t x).2 k ∈ readyArc K :=
    slot_ready_before hT hx k (ht.trans (by nlinarith))
  exact Set.disjoint_left.mp readyArc_disjoint_writtenArc hready hk.2

/-- ★★ **Exactly `m` ticks at time `m T`**, for `m` up to the horizon. -/
theorem tickCount_at_period (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) {m : ℕ} (hm : m ≤ K) :
    tickCount (clockEvolve T 0 (m * T) x) = m := by
  apply le_antisymm (tickCount_le hT hx m le_rfl)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · simp [hm0]
  · have hlt : m - 1 < K := by omega
    have h := tickCount_ge hK hT hx ⟨m - 1, hlt⟩ (t := m * T) (by
      simp only
      have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub hmpos]
        push_cast
        ring
      rw [this])
    simp only at h
    omega

/-- ★ **Successive ticks occupy distinguishable register states.** -/
theorem successive_ticks_distinguishable (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) {m : ℕ} (hm : m + 1 ≤ K) :
    clockEvolve T 0 ((m + 1 : ℕ) * T) x ≠ clockEvolve T 0 (m * T) x := by
  intro h
  have h1 := tickCount_at_period hK hT hx hm
  have h2 := tickCount_at_period hK hT hx (Nat.le_of_succ_le hm)
  rw [h] at h1
  omega

/-! ### Each slot is a measurement protocol; ticks persist -/

/-- **Slot `n` as a `MeasurementProtocol`** with one outcome ("the tick is written"): start at
`n T`, readout at `(n+1) T`, record lifetime `τR`. -/
noncomputable def tickProtocol (T : ℝ) (n : Fin K) (τR : ℝ) :
    MeasurementProtocol (ClockArena K) 1 where
  evolve := clockEvolve T
  evolve_self := clockEvolve_self T
  evolve_comp := clockEvolve_comp T
  measurable_evolve := measurable_clockEvolve T
  startTime := (n : ℕ) * T
  readoutTime := ((n : ℕ) + 1) * T
  recordDuration := τR
  readyRegion := {x | x.2 n ∈ readyArc K}
  pointerRegion := fun _ => {x | x.2 n ∈ writtenArc K}
  measurableSet_ready := ((measurable_pi_apply n).comp measurable_snd) measurableSet_readyArc
  measurableSet_pointer := fun _ =>
    ((measurable_pi_apply n).comp measurable_snd) measurableSet_writtenArc
  pointer_pairwiseDisjoint := Subsingleton.pairwise
  ready_disjoint_pointer := fun _ => readyArc_disjoint_writtenArc.preimage _

/-- After its readout the slot is frozen, so the written arc is invariant: the hypothesis the
persistence theorem asks for, discharged by the dynamics. -/
theorem tickProtocol_pointerInvariant {T : ℝ} (hT : 0 < T) (n : Fin K) (τR : ℝ) :
    (tickProtocol T n τR).PointerInvariantOn := by
  intro _ s t hs hst _ x hx
  have hs' : (((n : ℕ) : ℝ) + 1) * T ≤ s := hs
  change (clockEvolve T s t x).2 n ∈ writtenArc K
  change x.2 n ∈ writtenArc K at hx
  rw [clockEvolve_slot, winElapsed_of_ge hT hs', winElapsed_of_ge hT (hs'.trans hst), sub_self,
    zero_mul, pshift_zero]
  exact hx

/-- ★ **Tick `n` persists** from its readout through the record lifetime — by the corpus's
`record_persists_on_interval`, applied to `tickProtocol n` from the state at the start of its
window. -/
theorem tick_persists (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) (n : Fin K) {τR t : ℝ} (ht₁ : (((n : ℕ) : ℝ) + 1) * T ≤ t)
    (ht₂ : t ≤ (((n : ℕ) : ℝ) + 1) * T + τR) :
    (clockEvolve T 0 t x).2 n ∈ writtenArc K := by
  have hsplit : clockEvolve T 0 t x
      = clockEvolve T ((n : ℕ) * T) t (clockEvolve T 0 ((n : ℕ) * T) x) := by
    rw [← Function.comp_apply (f := clockEvolve T ((n : ℕ) * T) t), clockEvolve_comp]
  rw [hsplit]
  have hsec : clockEvolve T 0 ((n : ℕ) * T) x ∈ (tickProtocol T n τR).outcomeSector 0 := by
    change (clockEvolve T ((n : ℕ) * T) (((n : ℕ) + 1) * T)
      (clockEvolve T 0 ((n : ℕ) * T) x)).2 n ∈ writtenArc K
    rw [← Function.comp_apply (f := clockEvolve T ((n : ℕ) * T) _), clockEvolve_comp]
    exact slot_written_after hK hT hx n le_rfl
  exact (tickProtocol T n τR).record_persists_on_interval (tickProtocol_pointerInvariant hT n τR)
    hsec ht₁ ht₂

/-! ### The calibrated reading -/

/-- **The calibrated reading** `τ_A = tickCount · τ_tick`: the physical count times the unit. -/
noncomputable def tickReading (τtick : ℝ) (x : ClockArena K) : ℝ := (tickCount x : ℝ) * τtick

theorem tickReading_nonneg {τtick : ℝ} (h : 0 ≤ τtick) (x : ClockArena K) :
    0 ≤ tickReading τtick x :=
  mul_nonneg (Nat.cast_nonneg _) h

/-- ★★ **Calibrated with the period, the clock reads within one tick of `t_Σ`** over the horizon:
`|tickCount · T − t| < T` for `0 ≤ t ≤ K T`. The reading is a record count; `t` is the ontic
parameter of the schedule; they agree to within the resolution of one tick, and that is the whole
relation between them. -/
theorem abs_tickReading_sub_lt (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K}
    (hx : x ∈ ClockReady K) {t : OnticTime} (ht0 : 0 ≤ t) (htK : t ≤ K * T) :
    |tickReading T (clockEvolve T 0 t x) - t| < T := by
  set m := tickCount (clockEvolve T 0 t x) with hm
  rw [abs_sub_lt_iff]
  unfold tickReading
  rw [← hm]
  constructor
  · -- m T − t < T, i.e. (m − 1) T < t
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]
      simp only [Nat.cast_zero, zero_mul]
      linarith
    · by_contra! hcon
      have hle : t ≤ ((m - 1 : ℕ) : ℝ) * T := by
        rw [Nat.cast_sub hmpos]
        push_cast
        linarith
      have := tickCount_le hT hx (m - 1) hle
      omega
  · -- t − m T < T, i.e. t < (m + 1) T
    by_contra! hcon
    rcases lt_or_ge m K with hmK | hmK
    · have := tickCount_ge hK hT hx ⟨m, hmK⟩ (t := t) (by
        simp only
        linarith)
      simp only at this
      omega
    · have hmK' : (K : ℝ) ≤ m := by exact_mod_cast hmK
      nlinarith

/-! ### The package -/

/-- ★★★ **The record clock.** From the ready preparation on a horizon of `K ≥ 1` slots, with period
`T > 0`: the propagator is a measure-preserving two-time dynamics; the tick count is measurable,
nondecreasing, never above `K`, exactly `m` at time `m T`; each tick, once written, persists; and
calibrated with the period the reading is within one tick of `t_Σ`. -/
theorem record_clock (hK : 0 < K) {T : ℝ} (hT : 0 < T) {x : ClockArena K} (hx : x ∈ ClockReady K) :
    (∀ s t : OnticTime, MeasurePreserving (clockEvolve (K := K) T s t) volume volume)
      ∧ Measurable (tickCount (K := K))
      ∧ (∀ s t : OnticTime, s ≤ t →
          tickCount (clockEvolve T 0 s x) ≤ tickCount (clockEvolve T 0 t x))
      ∧ (∀ t : OnticTime, tickCount (clockEvolve T 0 t x) ≤ K)
      ∧ (∀ m : ℕ, m ≤ K → tickCount (clockEvolve T 0 (m * T) x) = m)
      ∧ (∀ (n : Fin K) (s t : OnticTime), (((n : ℕ) : ℝ) + 1) * T ≤ s → s ≤ t →
          (clockEvolve T 0 t x).2 n ∈ writtenArc K)
      ∧ (∀ t : OnticTime, 0 ≤ t → t ≤ K * T →
          |tickReading T (clockEvolve T 0 t x) - t| < T) :=
  ⟨fun s t => clockEvolve_measurePreserving T s t, measurable_tickCount,
    fun _ _ hst => tickCount_mono hK hT hx hst, fun _ => tickCount_le_horizon _,
    fun _ hm => tickCount_at_period hK hT hx hm,
    fun n _ _ hs hst => slot_written_mono hK hT hx n hst (slot_written_after hK hT hx n hs),
    fun _ ht0 htK => abs_tickReading_sub_lt hK hT hx ht0 htK⟩

end CSD.RecordLayer

end
