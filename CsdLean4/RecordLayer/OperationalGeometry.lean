/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.RecordedExchange
public import CsdLean4.CV.RadarCoordinates

/-!
# Operational geometry of the clock-and-echo witness: the capstone

**Category:** 7-SigmaLayer (the record layer — the terminal statement of the clock-and-echo
programme). BACKLOG #187 (out of #39; the fifth of #183–#189).

On the explicit finite arena of #186, from the stated ready preparation with message `b`, the one
constructed evolution produces persistent clock records (#185) and persistent exchange records
(#186) from the actual transfer (#183); the clock's readings at emission and return define radar
coordinates (#184) that every repeated exchange reproduces; the represented events respect the
causal order; and bounded readout errors give bounded coordinate errors.

* `arenaFlow_cycles` — **the exchange returns to the message point after every round trip**, so the
  stationary witness repeats itself: cycle `m` emits at `2m τ_hop`, is received at `(2m+1) τ_hop`
  (`receiver_cycle`), returns at `(2m+2) τ_hop`;
* `clockReading` — the physical clock's calibrated reading in the arena at an ontic time;
  `cycleReadings m` — **the radar readings of cycle `m` are the clock's readings at its emission
  and return**, a `RadarReadings` whose domain condition is the monotonicity of the tick count;
* ★★ `radarSep_cycle`, `radarTime_cycle` — under the calibration `T = τ_hop`, cycle `m` has radar
  separation `τ_tick` and radar time `(2m+1) τ_tick`: **repeated exchanges reproduce the same
  separation**;
* ★★★ `operational_geometry` — the capstone, twelve conjuncts, every one consumed from
  #183–#186 and #184 and none carried by a structure field.

## Capstone discipline (`CONVENTIONS.md` §8.3b)

The corpus's records→spacetime capstone, `record_influence_le_of_separated` (`CV/TwoCones.lean`,
#98), is a statement about **cone containment**: a record cannot be steered from outside the
Lieb–Robinson cone. This theorem is a statement about **operational coordinates**: what two clock
readings of one experiment define, and how they transform and err. The two are different claim
surfaces, so this stands as its own terminal statement rather than as a conjunct on #98 — the
decision #187 asked to be confirmed against the rule, confirmed here: adding these conjuncts to #98
would fragment neither surface into the other but merge two unrelated citations.

## What is not claimed

No metric and no volume element on the event order (`specs/records-to-spacetime-scoping.md` §8).
No universal signal speed: `c₀` is a calibration constant, and `radarDist_rescale_eq` says it absorbs
the clock unit. The cone of the corpus moves one edge per period in a preferred frame (#98). The
schedule — switch-on, readout times, clock windows — is a modelling input indexed by `t_Σ`, and the
identification of the clock's tick count with the record event's period index is the stated choice
`T = τ_hop`, not a dynamical fact. Hamiltonian generation of the propagator is not formalised.

References: `specs/BACKLOG.md` #187, #183–#186, #39; `CONVENTIONS.md` §8.3b;
`RecordLayer/RecordedExchange.lean`, `RecordLayer/RecordClock.lean`, `CV/SignalExchange.lean`,
`CV/RadarCoordinates.lean`, `CV/TwoCones.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K : ℕ}

/-! ### The stationary witness repeats itself -/

/-- **After every round trip the exchange is back at the message point.** -/
theorem arenaFlow_cycles {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (m : ℕ) :
    (hopFlow J ħ).arenaFlow (m * roundTrip J ħ) (msgPoint 1) = msgPoint 1 := by
  induction m with
  | zero =>
      rw [Nat.cast_zero, zero_mul]
      exact arenaFlow_zero J ħ _
  | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, FieldStructuredFlow.arenaFlow_add,
        arenaFlow_roundTrip hJ hħ, ih]

/-- At the reception time of cycle `m` the exchange is the excitation at `B`. -/
theorem arenaFlow_cycle_reception {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (m : ℕ) :
    (hopFlow J ħ).arenaFlow (m * roundTrip J ħ + hopTime J ħ) (msgPoint 1)
      = Projectivization.mk ℂ (basisVec excB) (basisVec_ne_zero _) := by
  rw [add_comm, FieldStructuredFlow.arenaFlow_add, arenaFlow_cycles hJ hħ, arenaFlow_hopTime hJ hħ]

/-- **The receiver responds in every cycle**: the readout at `B` is `1` at every reception time. -/
theorem receiver_cycle {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (m : ℕ) :
    arenaObs occB ((hopFlow J ħ).arenaFlow (m * roundTrip J ħ + hopTime J ħ) (msgPoint 1)) = 1 := by
  rw [arenaFlow_cycle_reception hJ hħ, occB, arenaObs_single_mk, basisVec_apply, Pi.single_eq_same,
    norm_one, one_pow, basisVec, PiLp.norm_single, norm_one, one_pow, div_one]

/-- The exchange factor of the arena at a nonnegative time is the hop run for that time. -/
theorem xEvolve_exchange_of_nonneg (J ħ T : ℝ) {t : OnticTime} (ht : 0 ≤ t) (x : XArena K) :
    (xEvolve J ħ T (-1) t x).1 = (hopFlow J ħ).arenaFlow t x.1 := by
  rw [xEvolve_exchange, hopOn_of_nonneg ht, hopOn_of_nonpos (by norm_num), sub_zero]

/-! ### The clock's readings as radar readings -/

/-- **The physical clock's calibrated reading** in the arena at ontic time `t`, unit `τ_tick`. -/
noncomputable def clockReading (J ħ T τtick : ℝ) (x : XArena K) (t : OnticTime) : ℝ :=
  tickReading τtick (xEvolve J ħ T (-1) t x).2.1

theorem clockReading_eq {J ħ T : ℝ} (hT : 0 < T) (τtick : ℝ) (x : XArena K) (t : OnticTime) :
    clockReading J ħ T τtick x t = (tickCount (clockEvolve T 0 t x.2.1) : ℝ) * τtick := by
  rw [clockReading, xEvolve_clock, tickReading, tickCount_clock_neg_one hT]

/-- The clock's reading is nondecreasing in ontic time. -/
theorem clockReading_mono {J ħ T τtick : ℝ} (hK : 0 < K) (hT : 0 < T) (hτ : 0 ≤ τtick)
    {x : XArena K} (hx : x ∈ XReady K) {s t : OnticTime} (hst : s ≤ t) :
    clockReading J ħ T τtick x s ≤ clockReading J ħ T τtick x t := by
  rw [clockReading_eq hT, clockReading_eq hT]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (tickCount_mono hK hT hx.1 hst)) hτ

/-- At a tick boundary within the horizon the clock reads the tick. -/
theorem clockReading_at_period {J ħ T τtick : ℝ} (hK : 0 < K) (hT : 0 < T) {x : XArena K}
    (hx : x ∈ XReady K) {m : ℕ} (hm : m ≤ K) :
    clockReading J ħ T τtick x (m * T) = m * τtick := by
  rw [clockReading_eq hT, tickCount_at_period hK hT hx.1 hm]

/-- **The radar readings of cycle `m`**: the clock's readings at the cycle's emission `2m τ_hop`
and return `(2m+2) τ_hop`. The domain condition `τ₋ ≤ τ₊` is the monotonicity of the tick count. -/
noncomputable def cycleReadings {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K)
    (hT : 0 < T) (hτ : 0 ≤ τtick) {x : XArena K} (hx : x ∈ XReady K) (m : ℕ) : RadarReadings :=
  ⟨clockReading J ħ T τtick x (((2 * m : ℕ) : ℝ) * hopTime J ħ),
    clockReading J ħ T τtick x (((2 * m + 2 : ℕ) : ℝ) * hopTime J ħ),
    clockReading_mono hK hT hτ hx (by
      have := hopTime_pos hJ hħ
      have h2 : ((2 * m : ℕ) : ℝ) ≤ ((2 * m + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
      nlinarith)⟩

theorem cycleReadings_emit {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) (hT : 0 < T)
    (hτ : 0 ≤ τtick) {x : XArena K} (hx : x ∈ XReady K) (m : ℕ) :
    (cycleReadings hJ hħ hK hT hτ hx m).emit
      = clockReading J ħ T τtick x (((2 * m : ℕ) : ℝ) * hopTime J ħ) := rfl

theorem cycleReadings_ret {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) (hT : 0 < T)
    (hτ : 0 ≤ τtick) {x : XArena K} (hx : x ∈ XReady K) (m : ℕ) :
    (cycleReadings hJ hħ hK hT hτ hx m).ret
      = clockReading J ħ T τtick x (((2 * m + 2 : ℕ) : ℝ) * hopTime J ħ) := rfl

/-- ★★ **Under the calibration `T = τ_hop`, every cycle has radar separation `τ_tick`**: repeated
exchanges reproduce the same separation. -/
theorem radarSep_cycle {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) (hT : 0 < T)
    (hTcal : T = hopTime J ħ) (hτ : 0 ≤ τtick) {x : XArena K} (hx : x ∈ XReady K) {m : ℕ}
    (hm : 2 * m + 2 ≤ K) :
    (cycleReadings hJ hħ hK hT hτ hx m).radarSep = τtick := by
  rw [RadarReadings.radarSep, cycleReadings_emit, cycleReadings_ret, ← hTcal,
    clockReading_at_period hK hT hx hm, clockReading_at_period hK hT hx (by omega)]
  push_cast
  ring

/-- Under the calibration, cycle `m` has radar time `(2m+1) τ_tick`. -/
theorem radarTime_cycle {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) (hT : 0 < T)
    (hTcal : T = hopTime J ħ) (hτ : 0 ≤ τtick) {x : XArena K} (hx : x ∈ XReady K) {m : ℕ}
    (hm : 2 * m + 2 ≤ K) :
    (cycleReadings hJ hħ hK hT hτ hx m).radarTime = (2 * m + 1) * τtick := by
  rw [RadarReadings.radarTime, cycleReadings_emit, cycleReadings_ret, ← hTcal,
    clockReading_at_period hK hT hx hm, clockReading_at_period hK hT hx (by omega)]
  push_cast
  ring

/-! ### The capstone -/

/-- ★★★ **Operational geometry of the clock-and-echo witness.** With `J, ħ > 0`, clock period
calibrated to the hop time, a horizon of at least two ticks, the ready preparation with message `b`,
and a clock unit `τ_tick > 0`:

1. the joint evolution obeys the two-time law and
2. preserves Liouville measure (Fubini–Study × Haar × Haar) — one dynamics on one arena;
3. the clock's records persist: a tick once written stays written through the horizon;
4. the exchange records persist: each register displays the message from its readout time on;
5. the two messages are distinguishable at the receiver's record;
6. the receiver responds: readout `1` for message `1` and `0` for message `0` at `τ_hop`;
7. the round trip is nonzero;
8. the clock's readings at emission and return define radar coordinates with separation `τ_tick`
   and time `τ_tick`;
9. every repeated cycle within the horizon reproduces the separation `τ_tick`, returns the exchange
   to the message point, and is received with readout `1`;
10. the represented events satisfy `emission ⪯ reception ⪯ return` on the hop graph;
11. readings with endpoint errors `≤ δ` give coordinate errors `≤ δ` and a distance error `≤ c₀ δ`;
12. memory is finite: the tick count never exceeds the horizon. -/
theorem operational_geometry {J ħ T τtick : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hTcal : T = hopTime J ħ)
    (hK : 2 ≤ K) {c : ClockArena K} (hc : c ∈ ClockReady K) {r : Fin 3 → LF4.KTorus}
    (hr : ∀ i, r i ∈ readyArc 2) (hτ : 0 < τtick) (b : Fin 2) :
    let hT : 0 < T := hTcal ▸ hopTime_pos hJ hħ
    let hK0 : 0 < K := by omega
    let hx : xPrep b c r ∈ XReady K := ⟨hc, hr⟩
    let x := xPrep b c r
    (∀ s t u : OnticTime, xEvolve (K := K) J ħ T t u ∘ xEvolve J ħ T s t = xEvolve J ħ T s u)
      ∧ (∀ (s t : OnticTime) (p₀ : FieldArena 2 2), MeasurePreserving (xEvolve (K := K) J ħ T s t)
          ((Matrix.UnitaryGroup.fsMeasure p₀).prod volume)
          ((Matrix.UnitaryGroup.fsMeasure p₀).prod volume))
      ∧ (∀ (n : Fin K) (s t : OnticTime), (((n : ℕ) : ℝ) + 1) * T ≤ s → s ≤ t →
          (xEvolve J ħ T (-1) t x).2.1.2 n ∈ writtenArc K)
      ∧ (∀ (i : Fin 3) (t : OnticTime), readTime J ħ i ≤ t →
          (xEvolve J ħ T (-1) t x).2.2 i ∈ pointerArc 2 b)
      ∧ (∀ t : OnticTime, hopTime J ħ ≤ t →
          (xEvolve J ħ T (-1) t (xPrep 1 c r)).2.2 1 ≠ (xEvolve J ħ T (-1) t (xPrep 0 c r)).2.2 1)
      ∧ (arenaObs occB (xEvolve J ħ T (-1) (hopTime J ħ) (xPrep 1 c r)).1 = 1
          ∧ arenaObs occB (xEvolve J ħ T (-1) (hopTime J ħ) (xPrep 0 c r)).1 = 0)
      ∧ 0 < roundTrip J ħ
      ∧ ((cycleReadings hJ hħ hK0 hT hτ.le hx 0).radarSep = τtick
          ∧ (cycleReadings hJ hħ hK0 hT hτ.le hx 0).radarTime = τtick)
      ∧ (∀ m : ℕ, 2 * m + 2 ≤ K →
          (cycleReadings hJ hħ hK0 hT hτ.le hx m).radarSep = τtick
            ∧ (hopFlow J ħ).arenaFlow (m * roundTrip J ħ) (msgPoint 1) = msgPoint 1
            ∧ arenaObs occB ((hopFlow J ħ).arenaFlow (m * roundTrip J ħ + hopTime J ħ) (msgPoint 1))
                = 1)
      ∧ (CausalPrecedes hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (reception J ħ b))
          ∧ CausalPrecedes hopGraph (eventOf J ħ T x (reception J ħ b))
              (eventOf J ħ T x (returnOcc J ħ b))
          ∧ CausalPrecedes hopGraph (eventOf J ħ T x (emission b))
              (eventOf J ħ T x (returnOcc J ħ b)))
      ∧ (∀ (r' : RadarReadings) (δ c₀ : ℝ), 0 ≤ c₀ →
          |r'.emit - (cycleReadings hJ hħ hK0 hT hτ.le hx 0).emit| ≤ δ →
          |r'.ret - (cycleReadings hJ hħ hK0 hT hτ.le hx 0).ret| ≤ δ →
            |r'.radarTime - (cycleReadings hJ hħ hK0 hT hτ.le hx 0).radarTime| ≤ δ
              ∧ |r'.radarSep - (cycleReadings hJ hħ hK0 hT hτ.le hx 0).radarSep| ≤ δ
              ∧ |r'.radarDist c₀ - (cycleReadings hJ hħ hK0 hT hτ.le hx 0).radarDist c₀| ≤ c₀ * δ)
      ∧ (∀ t : OnticTime, tickCount (xEvolve J ħ T (-1) t x).2.1 ≤ K) := by
  intro hT hK0 hx x
  have hK1 : 1 ≤ K := by omega
  have hrt : 0 ≤ hopTime J ħ := (hopTime_pos hJ hħ).le
  refine ⟨xEvolve_comp J ħ T, fun s t p₀ => xEvolve_measurePreserving J ħ T s t p₀, ?_,
    fun i t ht => register_written hJ hħ hr b i ht,
    fun t ht => (reception_depends_on_message hJ hħ hr ht).2.2, ?_, roundTrip_pos hJ hħ,
    ⟨radarSep_cycle hJ hħ hK0 hT hTcal hτ.le hx (by omega), ?_⟩, ?_,
    causal_chain hJ hħ hTcal hK hx b, ?_, fun t => tickCount_le_horizon _⟩
  · -- clock records persist
    intro n s t hs hst
    rw [xEvolve_clock]
    have hsplit : clockEvolve T (-1) t x.2.1 = clockEvolve T 0 t (clockEvolve T (-1) 0 x.2.1) := by
      rw [← Function.comp_apply (f := clockEvolve T 0 t), clockEvolve_comp]
    have hready : clockEvolve T (-1) 0 x.2.1 ∈ ClockReady K := by
      intro k
      rw [clockEvolve_slot, winElapsed_of_le hT (n := k) (u := 0) (by positivity),
        winElapsed_of_le hT (n := k) (u := -1) (by linarith [mul_nonneg (Nat.cast_nonneg (k : ℕ)) hT.le]),
        sub_self, zero_mul, pshift_zero]
      exact hx.1 k
    rw [hsplit]
    exact slot_written_mono hK0 hT hready n hst (slot_written_after hK0 hT hready n hs)
  · -- the receiver responds
    rw [xEvolve_exchange_of_nonneg J ħ T hrt, xEvolve_exchange_of_nonneg J ħ T hrt]
    exact receiver_distinguishes hJ hħ
  · -- radar time of cycle 0
    rw [radarTime_cycle hJ hħ hK0 hT hTcal hτ.le hx (by omega)]
    push_cast
    ring
  · -- every cycle reproduces
    intro m hm
    exact ⟨radarSep_cycle hJ hħ hK0 hT hTcal hτ.le hx hm, arenaFlow_cycles hJ hħ m,
      receiver_cycle hJ hħ m⟩
  · -- error bounds
    intro r' δ c₀ hc₀ he hret
    exact ⟨RadarReadings.abs_radarTime_sub_le he hret, RadarReadings.abs_radarSep_sub_le he hret,
      RadarReadings.abs_radarDist_sub_le hc₀ he hret⟩

end CSD.RecordLayer

end
