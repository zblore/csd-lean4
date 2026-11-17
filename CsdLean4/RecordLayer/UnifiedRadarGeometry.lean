/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarRun

/-!
# The family's run on an open set of pointer angles

**Category:** 7-SigmaLayer (the record layer). BACKLOG #431, #432, #433 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Tasks 9 and 10 of the research
delivery plan of 2026-11-16. No new assumption beyond UA-18.

`radar_family_lorentz` (#426, strengthened in #431) gives the five counts and the Lorentz
statement for the family's run from every five pointer angles within a radius of the start
`(1/12, 0)`. This module states it for an open set of the ten angles and under the plan's
name.

* `isOpen_nearStart` — the pointer angles within `ρ` of the start are an open set of the
  torus;
* `restEvent`, `movingEvent`, `radarInterval` (#432) — the rest observer's coordinates of the
  relay event from its two counts, the moving observer's radar coordinates of it from its
  three counts, and the interval `t² − x²`;
* `lorentzBoost_interval`, ★★ `WallRadarLorentz.geometry`, `WallRadarGeometry` (#432) — the
  boost preserves the interval, so the Lorentz statement gives the comparison of the two
  observers' intervals, with the error `E₁ (2 |b₁| + E₁) + E₂ (2 |b₂| + E₂)`;
* `isOpenPosMeasure_volume_prod`, `sFinite_volume_prod` (#432) — for the measure of the open
  set;
* ★★★ `csd_operational_lorentz_from_records` — for every `k ≥ 100` and every even ring with
  `M ≥ 210000 N³`: there are strengths and an open set `U` of the five pointers' angles,
  containing the start of every pointer at `(1/12, 0)` and of positive measure, such that
  from every point of `U` the five pointers of the walled chain's run have counts at every
  choice of flow times in the five reading windows, the boost by `v = vRel 1 1 (1/2)` of the
  rest observer's coordinates is within `151 K/k` of the moving observer's radar coordinates
  in both components, and the two intervals differ by at most the error above;
* `radar_error_relative`, `tendsto_radar_error_relative` — `151 K/k` is `151/(π k)` of the
  distance `π K`, and that ratio tends to `0`.

## Exact scope

* **No hypothesis on histories, on the speed of the messenger, on a dilation law or on radar
  relations.** The hypotheses are `k ≥ 100`, the size of the ring and its parity.
* **The open set is not explicit**: a product of intervals of an unnamed radius `ρ > 0`,
  which depends on `k`, on the ring and on the operator norms of the five gates. Its measure
  is positive; no lower bound on it is given, and nothing says the radius does not shrink as
  `k` grows.
* **The interval's error is a number (#433)**: `E (2B/√(1 − v²) + E)` twice, with
  `E = 151 K/k` and the size `B = 6K` of the rest observer's time, which the chain now
  exports. It is at most `4600 K²/k` (`radar_interval_error_le`), that is `4600/(π² k)` of
  the square of the distance. No lower bound on the interval itself is stated, so the
  comparison scale is the distance, not the interval.
* **One family, one velocity, one distance**: the messenger of rest energy `1/k` at momentum
  `1/2`, the clock at rest at the far wall, the moving clock at momentum `1/2`, on the walled
  chain (the mirror-odd sector of the ring) of UA-18's arena. `v = vRel 1 1 (1/2)` is the
  band velocity of the moving clock's lower level; the distance is the whole chain.
* **The Lorentz statement is that of #402**: two components of the boost of the rest clock's
  counts compared with the moving clock's counts, in the unit `2π/R₀` of the rest clock. It
  is a statement about five tick counts read in flow-time windows, not about a metric.
* **The error is absolute, `151 K/k` in the flow time**; relative to the distance `π K` it is
  `151/(π k)`. The reading windows are stated in the flow time.
* **The strengths `g_A`, `g_B` exist** (#411, #417); they are not given by a formula.
* **1 + 1 dimensions.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-193, UD-196, UD-200, UD-201, UD-202, UD-203); `RecordLayer/UnifiedRadarRun.lean`
(#426, #431: `radar_family_lorentz`); `RecordLayer/UnifiedWallOpen.lean` (#430: `wallRunAt`,
`tri_wall_radar_lorentz_open`); `RecordLayer/UnifiedTriFibre.lean` (#430: `NearStart`,
`nearStart_start`, `tri_radar_lorentz_open`); `RecordLayer/UnifiedWallRadar.lean` (#423:
`WallRadarLorentz`); `RecordLayer/UnifiedRadarSkeleton.lean` (#402:
`radar_lorentz_of_histories`); `RecordLayer/UnifiedWallValues.lean` (#415: `wallN`, `wallK`,
`wallGap`, `wallDelta`, `wallMu`); `RecordLayer/UnifiedRadarFamily.lean` (#425: the times
`famTb`, …).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Filter
open scoped Topology

namespace CSD.RecordLayer

/-- The pointer angles within `ρ` of the start `(1/12, 0)` are an open set of the torus. -/
theorem isOpen_nearStart (ρ : ℝ) : IsOpen {θ : KTorus | NearStart ρ θ} := by
  have hc : IsOpenMap (fun y : ℝ => (y : AddCircle (1 : ℝ))) := QuotientAddGroup.isOpenMap_coe
  have e : {θ : KTorus | NearStart ρ θ}
      = ((fun y : ℝ => (y : AddCircle (1 : ℝ))) '' {y : ℝ | |y - 1 / 12| < ρ})
        ×ˢ ((fun y : ℝ => (y : AddCircle (1 : ℝ))) '' {x : ℝ | |x| < ρ}) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_image, NearStart]
    constructor
    · rintro ⟨η, x, hη, hx, h1, h2⟩
      exact ⟨⟨1 / 12 + η, by rwa [add_sub_cancel_left], h1.symm⟩, ⟨x, hx, h2.symm⟩⟩
    · rintro ⟨⟨y, hy, h1⟩, ⟨x, hx, h2⟩⟩
      refine ⟨y - 1 / 12, x, hy, hx, ?_, h2.symm⟩
      rw [← h1, add_sub_cancel]
  rw [e]
  exact (hc _ (isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const)).prod
    (hc _ (isOpen_lt continuous_abs continuous_const))

/-! ### Radar coordinates and the interval -/

/-- **The rest observer's coordinates of the relay event**, from its two counts: the time
between the relay and the meeting on its own clock, in the unit `2π/R₀`, at its own place. -/
def restEvent (R₀ : ℝ) (Nρ Nm : ℕ) : ℝ × ℝ :=
  ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)

/-- **The moving observer's radar coordinates of the relay event**, from its three counts:
the radar time (the mean of the emission and return readings) less the meeting reading, and
the radar distance (half their difference), on the side the signal was sent. -/
def movingEvent (R₀ : ℝ) (Ne Nr Nμ : ℕ) : ℝ × ℝ :=
  (((Ne : ℝ) * (2 * Real.pi) / R₀
        + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
      - (Nμ : ℝ) * (2 * Real.pi) / R₀,
    -((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
        - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))

/-- **The interval** of a pair (time, place), with the limiting speed `1`. -/
def radarInterval (p : ℝ × ℝ) : ℝ := p.1 ^ 2 - p.2 ^ 2

/-- A boost with the limiting speed `1` preserves the interval. -/
theorem lorentzBoost_interval {v : ℝ} (hv : |v| < 1) (p : ℝ × ℝ) :
    (lorentzBoost 1 v p).1 ^ 2 - (lorentzBoost 1 v p).2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
  have hv2 : v ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one v).2 hv
  have h2 : Real.sqrt (1 - v ^ 2 / 1 ^ 2) ^ 2 = 1 - v ^ 2 := by
    rw [one_pow, div_one, Real.sq_sqrt (by linarith only [hv2])]
  have h1 : (1 : ℝ) - v ^ 2 ≠ 0 := by linarith only [hv2]
  simp only [lorentzBoost]
  rw [div_pow, div_pow, h2]
  field_simp
  ring

/-- Squares of two numbers within `E` of each other. -/
theorem abs_sq_sub_sq_le_of_abs_sub_le {a τ E : ℝ} (h : |a - τ| ≤ E) :
    |τ ^ 2 - a ^ 2| ≤ E * (2 * |a| + E) := by
  have e : τ ^ 2 - a ^ 2 = (τ - a) * (τ + a) := by ring
  have h1 : |τ - a| ≤ E := by rwa [abs_sub_comm]
  have h2 : |τ + a| ≤ 2 * |a| + E := by
    have e2 : τ + a = (τ - a) + 2 * a := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two]
    linarith only [h1]
  rw [e, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- **The operational geometry of a run on the walled chain.** For every labelling of the
carrier's basis and every choice of flow times in the five reading windows, the five pointers
of `run` have counts such that: the boost by `v` of the rest observer's coordinates of the
relay event (`restEvent`) is within `E₁`, `E₂` of the moving observer's radar coordinates of
it (`movingEvent`), component by component; the rest observer's time is at most `B` in
size; and the two observers' intervals of the event differ by at most
`E₁ (2B/√(1 − v²) + E₁) + E₂ (2B/√(1 − v²) + E₂)`. -/
def WallRadarGeometry (M : ℕ)
    (run : ∀ {D : ℕ}, ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) → ℝ → PentaSigma D)
    (R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ B : ℝ) : Prop :=
  ∀ (D : ℕ) (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)),
    ∀ se, tb ≤ se → se ≤ t3 → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbM ≤ sμ → sμ ≤ tcM →
    ∀ sρ, tbR ≤ sρ → sρ ≤ tcR → ∀ sm, tbM ≤ sm → sm ≤ tcM →
    ∃ Ne Nr Nμ Nρ Nm : ℕ,
      IsTickCount {x : PentaSigma D | x.1.1.1.1.2 ∈ readyArc 2}
          {x : PentaSigma D | x.1.1.1.1.2 ∈ displayArc} (run e) se Ne
      ∧ IsTickCount {x : PentaSigma D | x.1.1.1.2 ∈ readyArc 2}
          {x : PentaSigma D | x.1.1.1.2 ∈ displayArc} (run e) sr Nr
      ∧ IsTickCount {x : PentaSigma D | x.1.1.2 ∈ readyArc 2}
          {x : PentaSigma D | x.1.1.2 ∈ displayArc} (run e) sμ Nμ
      ∧ IsTickCount {x : PentaSigma D | x.1.2 ∈ readyArc 2}
          {x : PentaSigma D | x.1.2 ∈ displayArc} (run e) sρ Nρ
      ∧ IsTickCount {x : PentaSigma D | x.2 ∈ readyArc 2}
          {x : PentaSigma D | x.2 ∈ displayArc} (run e) sm Nm
      ∧ |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1 - (movingEvent R₀ Ne Nr Nμ).1| ≤ E₁
      ∧ |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2 - (movingEvent R₀ Ne Nr Nμ).2| ≤ E₂
      ∧ |(restEvent R₀ Nρ Nm).1| ≤ B
      ∧ |radarInterval (movingEvent R₀ Ne Nr Nμ) - radarInterval (restEvent R₀ Nρ Nm)|
          ≤ E₁ * (2 * (B / Real.sqrt (1 - v ^ 2)) + E₁)
            + E₂ * (2 * (B / Real.sqrt (1 - v ^ 2)) + E₂)

/-- ★★ **From the Lorentz statement to the common interval.** The Lorentz statement of #423
for a velocity `|v| < 1` is the comparison of the two observers' coordinates of the relay
event, and it gives the comparison of their intervals. -/
theorem WallRadarLorentz.geometry {M : ℕ}
    {run : ∀ {D : ℕ}, ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) → ℝ → PentaSigma D}
    {R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ B : ℝ}
    (H : WallRadarLorentz M run R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ B) (hv : |v| < 1) :
    WallRadarGeometry M run R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ B := by
  intro D e se a1 a2 sr a3 a4 sμ a5 a6 sρ a7 a8 sm a9 a10
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    H D e se a1 a2 sr a3 a4 sμ a5 a6 sρ a7 a8 sm a9 a10
  have d6 : |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1 - (movingEvent R₀ Ne Nr Nμ).1|
      ≤ E₁ := c6
  have d7 : |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2 - (movingEvent R₀ Ne Nr Nμ).2|
      ≤ E₂ := c7
  have d8 : |(restEvent R₀ Nρ Nm).1| ≤ B := c8
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, d6, d7, d8, ?_⟩
  have hv2 : v ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one v).2 hv
  have hσ : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by linarith only [hv2])
  have eb1 : (lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1
      = (restEvent R₀ Nρ Nm).1 / Real.sqrt (1 - v ^ 2) := by
    simp only [lorentzBoost, restEvent]
    rw [show (1 : ℝ) - (-v) ^ 2 / 1 ^ 2 = 1 - v ^ 2 by ring]
    ring
  have eb2 : (lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2
      = v * (restEvent R₀ Nρ Nm).1 / Real.sqrt (1 - v ^ 2) := by
    simp only [lorentzBoost, restEvent]
    rw [show (1 : ℝ) - (-v) ^ 2 / 1 ^ 2 = 1 - v ^ 2 by ring]
    ring
  have hb1 : |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1| ≤ B / Real.sqrt (1 - v ^ 2) := by
    rw [eb1, abs_div, abs_of_pos hσ]
    exact div_le_div_of_nonneg_right d8 hσ.le
  have hb2 : |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2| ≤ B / Real.sqrt (1 - v ^ 2) := by
    rw [eb2, abs_div, abs_of_pos hσ, abs_mul]
    refine div_le_div_of_nonneg_right ?_ hσ.le
    calc |v| * |(restEvent R₀ Nρ Nm).1| ≤ 1 * |(restEvent R₀ Nρ Nm).1| :=
          mul_le_mul_of_nonneg_right hv.le (abs_nonneg _)
      _ ≤ B := by rw [one_mul]; exact d8
  have hE1 : 0 ≤ E₁ := (abs_nonneg _).trans d6
  have hE2 : 0 ≤ E₂ := (abs_nonneg _).trans d7
  have hb := lorentzBoost_interval (v := -v) (by rwa [abs_neg]) (restEvent R₀ Nρ Nm)
  have i1 := abs_sq_sub_sq_le_of_abs_sub_le d6
  have i2 := abs_sq_sub_sq_le_of_abs_sub_le d7
  unfold radarInterval
  rw [← hb]
  have e' : (movingEvent R₀ Ne Nr Nμ).1 ^ 2 - (movingEvent R₀ Ne Nr Nμ).2 ^ 2
        - ((lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1 ^ 2
          - (lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2 ^ 2)
      = ((movingEvent R₀ Ne Nr Nμ).1 ^ 2 - (lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1 ^ 2)
        - ((movingEvent R₀ Ne Nr Nμ).2 ^ 2
          - (lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2 ^ 2) := by ring
  rw [e']
  exact ((abs_sub _ _).trans (add_le_add i1 i2)).trans
    (add_le_add (mul_le_mul_of_nonneg_left (by linarith only [hb1]) hE1)
      (mul_le_mul_of_nonneg_left (by linarith only [hb2]) hE2))

/-- The volume of a product is positive on open sets when the factors' volumes are. -/
theorem isOpenPosMeasure_volume_prod {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasureTheory.MeasureSpace α] [MeasureTheory.MeasureSpace β]
    [(MeasureTheory.volume : MeasureTheory.Measure α).IsOpenPosMeasure]
    [(MeasureTheory.volume : MeasureTheory.Measure β).IsOpenPosMeasure]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure β)] :
    (MeasureTheory.volume : MeasureTheory.Measure (α × β)).IsOpenPosMeasure := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  infer_instance

/-- The volume of a product of two s-finite volumes is s-finite. -/
theorem sFinite_volume_prod {α β : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.MeasureSpace β]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure β)] :
    MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure (α × β)) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  infer_instance

/-- ★★★ **Five counts and the Lorentz statement from records, on an open set of pointer
angles.** For every `k ≥ 100` and every ring with an even number `M + 1 = 2H` of sites,
`M ≥ 210000 N³`, `N = 10¹⁶ k⁴`: take the light messenger's wall state (rest energy `1/k`),
the clock at rest translated to the far wall and the moving clock (gap `Δ = k/K`), both
clocks prepared a quarter turn early, and the five wall gates of width `3δ`,
`δ = 1/(10⁵ k)`. Then there are strengths `0 < g_A ≤ R₀/5`, `0 < g_B ≤ R_B/5` and an open set
`U` of the five pointers' angles, containing the start `(1/12, 0)` of every pointer, such
that from every point of `U`: at every choice of flow times in the five reading windows the
five pointers of `wallRunAt` have counts, and the counts satisfy both components of the
Lorentz statement of #402 for the velocity `v = vRel 1 1 (1/2)` within `151 K/k`.

The run lasts about `7K` in the flow time over the distance `πK`; the error is `151/(π k)`
of that distance (`radar_error_relative`), which tends to `0` along the family while the
distance (the whole chain) and the velocity do not change. -/
theorem csd_operational_lorentz_from_records {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ (hψ : oddWall (L := M + 1) 1 (wallMu k) (ringLen (1200 * wallN k * wallN k))
          (Finset.Ico (600 * (wallN k : ℤ) * wallN k) (600 * (wallN k : ℤ) * wallN k + wallN k))
          (flatAmpN (wallN k)) (radarRateB k * radarTau k M / radarRateA k) ≠ 0)
      (gA gB : ℝ)
      (hΨA : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (wallWindow (wallN k) ∪ negWin (wallWindow (wallN k)))
        (oddExt (wallWindow (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)))) ≠ 0)
      (hΨB : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (flatWindow (wallN k) (wallN k) ∪ negWin (flatWindow (wallN k) (wallN k)))
        (oddExt (flatWindow (wallN k) (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)))) ≠ 0)
      (U : Set (KTorus × KTorus × KTorus × KTorus × KTorus)),
      0 < gA ∧ gA ≤ ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) / 5
      ∧ 0 < gB ∧ gB ≤ ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5
      ∧ IsOpen U ∧ 0 < MeasureTheory.volume U
      ∧ (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) ∈ U
      ∧ ∀ Θ ∈ U, WallRadarGeometry M
          (fun e => wallRunAt (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
            gA gB e (chainRay _ hψ)
            (deviceRay (deviceShift (H : ZMod (M + 1)) _)
              (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB)
            Θ.1 Θ.2.1 Θ.2.2.1 Θ.2.2.2.1 Θ.2.2.2.2)
          (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) (vRel 1 1 (1 / 2))
          (famTb k) (famT3 k) (famT4 k) (famT5 k) (famTbM k M) (famTcM k M) (famTbR k M)
          (famTcR k M) (151 * (wallK k / k)) (151 * (wallK k / k)) (6 * wallK k) := by
  obtain ⟨hψ, gA, gB, hΨA, hΨB, a1, a2, a3, a4, -, ρ, hρ0, Hop⟩ :=
    radar_family_lorentz hk hM hH
  have hU : IsOpen {Θ : KTorus × KTorus × KTorus × KTorus × KTorus | NearStart ρ Θ.1 ∧ NearStart ρ
      Θ.2.1
      ∧ NearStart ρ Θ.2.2.1 ∧ NearStart ρ Θ.2.2.2.1 ∧ NearStart ρ Θ.2.2.2.2} := by
    have o := isOpen_nearStart ρ
    exact (o.preimage (by fun_prop : Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus
        => Θ.1)).and
      ((o.preimage (by fun_prop : Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus =>
          Θ.2.1)).and
        ((o.preimage (by fun_prop : Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus
            => Θ.2.2.1)).and
          ((o.preimage (by fun_prop : Continuous fun Θ : KTorus × KTorus × KTorus × KTorus ×
              KTorus => Θ.2.2.2.1)).and
            (o.preimage (by fun_prop : Continuous fun Θ : KTorus × KTorus × KTorus × KTorus ×
                KTorus => Θ.2.2.2.2)))))
  have hmem : ((((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) : KTorus × KTorus × KTorus ×
          KTorus × KTorus)
      ∈ {Θ : KTorus × KTorus × KTorus × KTorus × KTorus | NearStart ρ Θ.1 ∧ NearStart ρ Θ.2.1
      ∧ NearStart ρ Θ.2.2.1 ∧ NearStart ρ Θ.2.2.2.1 ∧ NearStart ρ Θ.2.2.2.2} :=
    ⟨nearStart_start hρ0, nearStart_start hρ0, nearStart_start hρ0, nearStart_start hρ0,
      nearStart_start hρ0⟩
  have hv := vRel_half_one
  have p1 : (MeasureTheory.volume : MeasureTheory.Measure KTorus).IsOpenPosMeasure :=
    isOpenPosMeasure_volume_prod
  have f1 : MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure KTorus) :=
    sFinite_volume_prod
  have p2 : (MeasureTheory.volume : MeasureTheory.Measure (KTorus × KTorus)).IsOpenPosMeasure :=
    isOpenPosMeasure_volume_prod
  have f2 : MeasureTheory.SFinite
      (MeasureTheory.volume : MeasureTheory.Measure (KTorus × KTorus)) := sFinite_volume_prod
  have p3 : (MeasureTheory.volume :
      MeasureTheory.Measure (KTorus × KTorus × KTorus)).IsOpenPosMeasure :=
    isOpenPosMeasure_volume_prod
  have f3 : MeasureTheory.SFinite
      (MeasureTheory.volume : MeasureTheory.Measure (KTorus × KTorus × KTorus)) :=
    sFinite_volume_prod
  have p4 : (MeasureTheory.volume :
      MeasureTheory.Measure (KTorus × KTorus × KTorus × KTorus)).IsOpenPosMeasure :=
    isOpenPosMeasure_volume_prod
  have f4 : MeasureTheory.SFinite
      (MeasureTheory.volume : MeasureTheory.Measure (KTorus × KTorus × KTorus × KTorus)) :=
    sFinite_volume_prod
  have p5 : (MeasureTheory.volume :
      MeasureTheory.Measure (KTorus × KTorus × KTorus × KTorus × KTorus)).IsOpenPosMeasure :=
    isOpenPosMeasure_volume_prod
  exact ⟨hψ, gA, gB, hΨA, hΨB, _, a1, a2, a3, a4, hU,
    hU.measure_pos MeasureTheory.volume ⟨_, hmem⟩, hmem, fun Θ hΘ =>
      (Hop _ _ _ _ _ hΘ.1 hΘ.2.1 hΘ.2.2.1 hΘ.2.2.2.1 hΘ.2.2.2.2).geometry
        (by rw [abs_of_pos hv.1]; linarith only [hv.2])⟩

/-- The error `151 K/k` is `151/(π k)` of the distance `π K`. -/
theorem radar_error_relative {k : ℕ} (hk : 1 ≤ k) :
    151 * (wallK k / k) = 151 / (Real.pi * k) * (Real.pi * wallK k) := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [this]
  have hπ := Real.pi_ne_zero
  field_simp

/-- The relative error `151/(π k)` tends to `0` along the family. -/
theorem tendsto_radar_error_relative :
    Tendsto (fun k : ℕ => 151 / (Real.pi * (k : ℝ))) atTop (𝓝 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat (151 / Real.pi)).congr fun k => by rw [div_div]

/-- **The interval's error for the family, as a number.** With the errors `151 K/k` and the
size `6K` of `csd_operational_lorentz_from_records`, the bound on the difference of the two
observers' intervals is at most `4600 K²/k`. -/
theorem radar_interval_error_le {k : ℕ} (hk : 100 ≤ k) :
    151 * (wallK k / k)
          * (2 * (6 * wallK k / Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2)) + 151 * (wallK k / k))
        + 151 * (wallK k / k)
          * (2 * (6 * wallK k / Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2)) + 151 * (wallK k / k))
      ≤ 4600 * (wallK k ^ 2 / k) := by
  have hK0 : 0 < wallK k := (radar_family_rates hk 0).1
  have hX : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hX0 : (0 : ℝ) < k := by linarith only [hX]
  have hv := vRel_half_one
  have hs : 89 / 100 ≤ Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hv.1, hv.2])
  have hq0 : 0 < wallK k / k := div_pos hK0 hX0
  have hq : wallK k / k ≤ wallK k / 100 := div_le_div_of_nonneg_left hK0.le (by norm_num) hX
  have h1 : 6 * wallK k / Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2) ≤ 6 * wallK k / (89 / 100) :=
    div_le_div_of_nonneg_left (by linarith only [hK0]) (by norm_num) hs
  have h2 : 2 * (6 * wallK k / Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2)) + 151 * (wallK k / k)
      ≤ 15 * wallK k := by
    have e : 6 * wallK k / (89 / 100) = 600 / 89 * wallK k := by ring
    rw [e] at h1
    linarith only [h1, hq, hK0]
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith only [hq0] : 0 ≤ 151 * (wallK k / k))
  have e2 : 151 * (wallK k / k) * (15 * wallK k) = 2265 * (wallK k ^ 2 / k) := by
    field_simp
    ring
  rw [e2] at h3
  have hp : 0 ≤ wallK k ^ 2 / k := by positivity
  linarith only [h3, hp]

/-- `4600 K²/k` is `4600/(π² k)` of the square of the distance `π K`. -/
theorem radar_interval_error_relative {k : ℕ} (hk : 1 ≤ k) :
    4600 * (wallK k ^ 2 / k) = 4600 / (Real.pi ^ 2 * k) * (Real.pi * wallK k) ^ 2 := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [this]
  have hπ := Real.pi_ne_zero
  field_simp

/-- The interval's relative error `4600/(π² k)` tends to `0` along the family. -/
theorem tendsto_radar_interval_error_relative :
    Tendsto (fun k : ℕ => 4600 / (Real.pi ^ 2 * (k : ℝ))) atTop (𝓝 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat (4600 / Real.pi ^ 2)).congr fun k => by rw [div_div]

end CSD.RecordLayer

end
