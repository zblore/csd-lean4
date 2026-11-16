/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallMeeting
public import CsdLean4.RecordLayer.UnifiedTriCarrier
public import CsdLean4.RecordLayer.UnifiedReturnReading

/-!
# The walled chain's run: five counts and the Lorentz statement, from where the carriers are

**Category:** 7-SigmaLayer (the record layer). BACKLOG #423 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Tasks 6 and 10 of the research
delivery plan of 2026-11-16 (one prepared state for the five histories, and the first
application of the top-down theorem). No new assumption beyond UA-18.

#420 to #422 proved the five histories that `tri_radar_lorentz` (#405) asks for, one theorem
each. This module joins them for **one prepared state and one run**: the light messenger, the
clock at rest translated to its place and the moving clock, with one strength for the three
pointers on the moving clock and one for the two on the clock at rest, and it applies #405.

* `wallRun` — the run: the five-pointer flow of UA-18's arena on the ring, for the three wall
  states, the five wall gates and the profiles `g_B · trainF` (three) and `g_A · trainF`
  (two), every pointer started at `(1/12, 0)`;
* `WallRadarLorentz`, `WallRadarLorentz.mono` — the conclusion as one statement about a run
  (the five counts in the five windows and the two components of the Lorentz statement within
  two errors), and its monotonicity in the errors;
* ★★★ `tri_wall_radar_lorentz` — if the three gates' angle conditions hold on their intervals
  and the sizes hold, then for some strengths `0 < g_A ≤ R₀/5`, `0 < g_B ≤ R_B/5` the five
  pointers of `wallRun` have counts at every choice of flow times in the five reading
  windows, and the counts satisfy the Lorentz statement of #402 with velocity
  `v = vRel 1 1 (1/2)` and explicit errors.

## Exact scope

* **Conditions on predicted angles over the intervals are hypotheses**, as are the sizes
  (the budget, the swing horizons, the closing conditions and the band). They are those of
  #420 to #422, with one budget hypothesis for the three carriers. Nothing here shows that
  they can be met together.
* **The errors are not shown to be small.** The bound contains `|t − T|` for each of the five
  gate times against the kinematic times of #412 for a distance `d` that the statement
  leaves free; it is small only when the gate times are close to those times, which is not
  proved here.
* **The fibres where the five profiles vanish**: every pointer starts at `(1/12, 0)`. The
  carriers then move freely. An open set of starts (R7) is outside this module.
* **Strengths exist; they are not chosen**: they are the ones the two swing theorems provide
  for the index `j`.
* **The labelling `e` of the carrier's basis is arbitrary.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-163, UD-164, UD-170, UD-181, UD-188, UD-190, UD-191, UD-192, UD-193);
`RecordLayer/UnifiedTriCarrier.lean` (#405: `triRun`, `tri_radar_lorentz`);
`RecordLayer/UnifiedWallObserver.lean` (#420: `wall_observer_radar_histories`);
`RecordLayer/UnifiedWallRelay.lean` (#421: `wall_relay_history`);
`RecordLayer/UnifiedWallMeeting.lean` (#422: `wall_meeting_history_moving`,
`wall_meeting_history_rest`); `RecordLayer/UnifiedWallOrbits.lean` (#411:
`wall_moving_clock_swing_fine`); `RecordLayer/UnifiedRingShift.lean` (#417:
`far_wall_clock_swing_fine`); `RecordLayer/UnifiedEventTimes.lean` (#418:
`wall_observer_clock_rate_relation`); `RecordLayer/UnifiedRadarTimes.lean` (#412:
`radar_times_relay`, `radar_times_return`); `RecordLayer/UnifiedEmissionValues.lean` (#397:
`vRel_half_one`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-- **The walled chain's run.** The five-pointer flow of UA-18's arena on the ring of `M + 1`
sites, for a messenger `p`, a clock `qa` and a clock `qb`: pointers 1 and 2 gated by "the
messenger is near `qb`" and its complement, pointer 3 by "the clocks are not near", all three
coupled to `qb`'s level swap with the profile `g_B · trainF`; pointer 4 gated by "the
messenger is not near `qa`" and pointer 5 by "the clocks are not near", coupled to `qa`'s
level swap with the profile `g_A · trainF`. Every pointer starts at `(1/12, 0)`. -/
def wallRun (n N M : ℕ) (μ Δ w gA gB : ℝ) {D : ℕ}
    (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1))
    (p : GenArena (ZMod (M + 1) × Fin 2))
    (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) : ℝ → PentaSigma D :=
  triRun e (diracHam (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (deviceHam (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (wallNear (M + 1) w) (fun k k' => ¬ wallNear (M + 1) w k k')
    (fun k k' => ¬ wallNear (M + 1) w k k') (fun k k' => ¬ wallNear (M + 1) w k k')
    (fun k k' => ¬ wallNear (M + 1) w k k')
    (levelSwap (ZMod (M + 1) × Fin 2)) (levelSwap (ZMod (M + 1) × Fin 2))
    (scaledTrainF_periodic gB) (scaledTrainF_periodic gB) (scaledTrainF_periodic gB)
    (scaledTrainF_periodic gA) (scaledTrainF_periodic gA)
    (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB)
    (contDiff_scaledTrainF gA) (contDiff_scaledTrainF gA) p qa qb
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))

/-- **The Lorentz statement for a run on the walled chain.** For every labelling of the
carrier's basis and every choice of flow times in the five reading windows, the five pointers
of `run` have counts, and the counts, as times in the unit `2π/R₀`, satisfy the two
components of the Lorentz statement of #402 for the velocity `v` within `E₁` and `E₂`. -/
def WallRadarLorentz (M : ℕ)
    (run : ∀ {D : ℕ}, ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) → ℝ → PentaSigma D)
    (R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ : ℝ) : Prop :=
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
      ∧ |(lorentzBoost 1 (-v)
              ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
            - (((Ne : ℝ) * (2 * Real.pi) / R₀
                  + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                - (Nμ : ℝ) * (2 * Real.pi) / R₀)| ≤ E₁
      ∧ |(lorentzBoost 1 (-v)
              ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
            - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                  - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))| ≤ E₂

/-- The Lorentz statement for a run holds with any larger errors. -/
theorem WallRadarLorentz.mono {M : ℕ}
    {run : ∀ {D : ℕ}, ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) → ℝ → PentaSigma D}
    {R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ E₁' E₂' : ℝ}
    (H : WallRadarLorentz M run R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂) (h1 : E₁ ≤ E₁')
    (h2 : E₂ ≤ E₂') : WallRadarLorentz M run R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁' E₂' := by
  intro D e se a1 a2 sr a3 a4 sμ a5 a6 sρ a7 a8 sm a9 a10
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6, c7⟩ :=
    H D e se a1 a2 sr a3 a4 sμ a5 a6 sρ a7 a8 sm a9 a10
  exact ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6.trans h1, c7.trans h2⟩

section Radar

variable {n N M : ℕ} {Δ : ℝ}

local notation "RB" => ringRate (1200 * n * N) M (1 / 2) Δ

local notation "RA" => ringRate (1200 * n * N) M 0 Δ

local notation "vB" => vRel 1 1 (1 / 2)

local notation "κB" => Δ + (ringLen (1200 * n * N) / (M + 1 : ℕ)) ^ 2 * (1 / 2) ^ 3 / 6

local notation "φA" h => 0 + 2 * Real.pi * (ZMod.val h) / (M + 1 : ℕ)

/-- ★★★ **Five counts and the Lorentz statement on the walled chain, from where the carriers
are.** A light messenger wall state (rest energy `0 < μ ≤ 1`, packet time `t₀`), the clock
at rest translated by `h` and the moving clock (momentum `1/2`), both clocks prepared a
quarter turn early, `1 ≤ j ≤ n`. Suppose, for one `w`, `δ`, `ε`:

* each carrier's bound is at most `ε (1 − cos δ)/2` up to a flow time `T` after the last
  reading window;
* the messenger is near the moving clock's mirror image on `[0, t_E]` (the clock is prepared
  before the wall and moving into it), away from the clock and its mirror image on
  `[t_b, t₃]`, near its mirror image on `[t₄, t₅]` (#420);
* the messenger is away from the clock at rest on `[0, t_R]` and near it on `[t_bR, t_cR]`
  (#421);
* the clock at rest is away from the moving clock on `[0, t_M]` and near it on
  `[t_bM, t_cM]` (#422);
* the sizes of #420 to #422 hold.

Then for some strengths `0 < g_A ≤ R₀/5` and `0 < g_B ≤ R_B/5`, at every choice of flow
times in the five reading windows the five pointers of `wallRun` have counts, and the counts
satisfy the Lorentz statement of #402 for the velocity `v = vRel 1 1 (1/2)`, with the gate
times compared with the kinematic times of #412 for any distance `d`. -/
theorem tri_wall_radar_lorentz {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M)
    {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ : ℝ)
    (h : ZMod (M + 1))
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0) {w δ ε T d : ℝ} (hδ0 : 0 ≤ δ) (hδ : Real.cos δ < 1)
    (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi) (hε : 0 ≤ ε)
    (hbud : ∀ s, 0 ≤ s → s ≤ T →
      4 * lightBudget n N μ (t₀ + s) ≤ ε * (1 - Real.cos δ) / 2
        ∧ 4 * lightBudget n N 1 (-(Real.pi / (2 * RA)) + s) ≤ ε * (1 - Real.cos δ) / 2
        ∧ 4 * lightBudget n N 1 (-(Real.pi / (2 * RB)) + s) ≤ ε * (1 - Real.cos δ) / 2)
    -- the messenger and the moving clock
    {tE tb t3 t4 t5 : ℝ} (htE : 0 ≤ tE) (hEb : tE ≤ tb) (hb3 : tb ≤ t3) (h34 : t3 ≤ t4)
    (h45 : t4 ≤ t5) (h5T : t5 ≤ T) (hT3 : t3 ≤ 2 * Real.pi * n / (j * RB))
    (hnear : ∀ s, 0 ≤ s → s ≤ tE →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s)))
    (hapart : ∀ s, tb ≤ s → s ≤ t3 →
      Real.cos (wallAngle n N μ p₀ (t₀ + s)
            - wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s)
            + wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s)
            - wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s)
            + wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s))
          < Real.cos (w + 2 * δ))
    (hback : ∀ s, t4 ≤ s → s ≤ t5 →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s)))
    (hcl3 : 2 * (RB / 5) * ε * (t3 - tb) ≤ 1 / 6)
    (hcl5 : 2 * (RB / 5) * ε * (t5 - t4) ≤ 1 / 6)
    (hband : 1 / 4 * (1 - Real.cos (RB * tE)) + 1 / (24 * (j : ℝ)) + 2 * (RB / 5) * ε * tE
        + 2 * (RB / 5) * (tb - tE) + (1 / (24 * (j : ℝ)) + 2 * (RB / 5) * ε * (t3 - tb))
      < 1 / 12)
    -- the messenger and the clock at rest
    {tR tbR tcR : ℝ} (htR : 0 ≤ tR) (hRb : tR ≤ tbR) (hRc : tbR ≤ tcR) (hRT : tcR ≤ T)
    (hTR : tR ≤ 2 * Real.pi * n / (j * RA))
    (hapartR : ∀ s, 0 ≤ s → s ≤ tR →
      Real.cos (wallAngle n N μ p₀ (t₀ + s) - (φA h)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + (φA h)) < Real.cos (w + 2 * δ))
    (hnearR : ∀ s, tbR ≤ s → s ≤ tcR →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s) - (φA h)))
    (hER : 1 / (24 * (j : ℝ)) + 2 * (RA / 5) * ε * tR < 1 / 12)
    (hclR : 2 * (RA / 5) * ε * (tcR - tbR) ≤ 1 / 6)
    -- the two clocks
    {tM tbM tcM : ℝ} (htM : 0 ≤ tM) (hMb : tM ≤ tbM) (hMc : tbM ≤ tcM) (hMT : tcM ≤ T)
    (hTMB : tM ≤ 2 * Real.pi * n / (j * RB)) (hTMA : tM ≤ 2 * Real.pi * n / (j * RA))
    (hapartM : ∀ s, 0 ≤ s → s ≤ tM →
      Real.cos ((φA h) - wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((φA h) + wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((φA h) - wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((φA h) + wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s))
          < Real.cos (w + 2 * δ))
    (hnearM : ∀ s, tbM ≤ s → s ≤ tcM →
      Real.cos (w - 2 * δ)
          ≤ Real.cos ((φA h) - wallAngle n N 1 (1 / 2) (-(Real.pi / (2 * RB)) + s))
        ∧ Real.cos (w - 2 * δ)
          ≤ Real.cos ((φA h) - wallAngle n N (1 + Δ) (1 / 2) (-(Real.pi / (2 * RB)) + s)))
    (hEMB : 1 / (24 * (j : ℝ)) + 2 * (RB / 5) * ε * tM < 1 / 12)
    (hclMB : 2 * (RB / 5) * ε * (tcM - tbM) ≤ 1 / 6)
    (hEMA : 1 / (24 * (j : ℝ)) + 2 * (RA / 5) * ε * tM < 1 / 12)
    (hclMA : 2 * (RA / 5) * ε * (tcM - tbM) ≤ 1 / 6) :
    ∃ (gA gB : ℝ)
      (hΨA : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
        (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N))
        (-(Real.pi / (2 * RA))) ≠ 0)
      (hΨB : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
        (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
        (-(Real.pi / (2 * RB))) ≠ 0),
      0 < gA ∧ gA ≤ RA / 5 ∧ 0 < gB ∧ gB ≤ RB / 5
      ∧ WallRadarLorentz M
          (fun e => wallRun n N M μ Δ w gA gB e (chainRay _ hψ)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB))
          RA vB tb t3 t4 t5 tbM tcM tbR tcR
          (((gatedErr (2 * gB) tE tb / RA + (κB) * tE + |tE - 0|)
                  + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4
                        + RB * (tb - tE)) / RA
                      + (κB) * t3 + |t3 - radarTRet d vB|)) / 2
                + (gatedErr (2 * gB) tM tbM / RA + (κB) * tM + |tM - radarTM d vB|)
                + ((gatedErr (2 * gA) tR tbR / RA + |tR - radarTR d|)
                    + (gatedErr (2 * gA) tM tbM / RA + |tM - radarTM d vB|))
                  / Real.sqrt (1 - vB ^ 2))
          (((gatedErr (2 * gB) tE tb / RA + (κB) * tE + |tE - 0|)
                  + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4
                        + RB * (tb - tE)) / RA
                      + (κB) * t3 + |t3 - radarTRet d vB|)) / 2
                + vB * ((gatedErr (2 * gA) tR tbR / RA + |tR - radarTR d|)
                    + (gatedErr (2 * gA) tM tbM / RA + |tM - radarTM d vB|))
                  / Real.sqrt (1 - vB ^ 2)) := by
  have hn : 0 < n := hj.trans_le hjn
  have hK : 0 < 1200 * n * N := by positivity
  have hRA : 0 < RA := by
    rw [ringRate_zero _ _ hΔ0.le]
    exact hΔ0
  obtain ⟨gB, hΨB, hgB0, hgB5, hswB⟩ :=
    wall_moving_clock_swing_fine (M := M) hj hjn hN hM hΔ0 hΔ
  obtain ⟨gA, hΨA, hgA0, hgA5, hswA⟩ :=
    far_wall_clock_swing_fine (M := M) hj hjn hN hM hΔ0 hΔ h
  obtain ⟨He, Hr⟩ := wall_observer_radar_histories hn hN hM hμ0 hμ1 hΔ0 hlo hhi hp₀ hWD t₀
    hψ hδ0 hδ hw hwπ hε htE hEb hb3 h34 h45 hT3
    (fun s h0 h1 => by
      obtain ⟨a, -, c⟩ := hbud s h0 (h1.trans h5T)
      linarith only [a, c])
    hnear hapart hback hcl3 hcl5 hband hgB0 hgB5 hΨB hswB
  have Hμ := wall_meeting_history_moving hn hN hM hΔ0 h (-(Real.pi / (2 * RA))) hΨA hδ0 hδ
    hw hwπ hε htM hMb hMc hTMB
    (fun s h0 h1 => by
      obtain ⟨-, b, c⟩ := hbud s h0 (h1.trans hMT)
      linarith only [b, c])
    hapartM hnearM hEMB hclMB hgB0 hgB5 hΨB hswB
  have Hρ := wall_relay_history hn hN hM hμ0 hμ1 hΔ0 hlo hhi hp₀ hWD t₀ h hψ hδ0 hδ hw hwπ
    hε htR hRb hRc hTR
    (fun s h0 h1 => by
      obtain ⟨a, b, -⟩ := hbud s h0 (h1.trans hRT)
      linarith only [a, b])
    hapartR hnearR hER hclR hgA0 hgA5 hΨA hswA
  have Hm := wall_meeting_history_rest hn hN hM hΔ0 h (-(Real.pi / (2 * RB))) hΨB hδ0 hδ
    hw hwπ hε htM hMb hMc hTMA
    (fun s h0 h1 => by
      obtain ⟨-, b, c⟩ := hbud s h0 (h1.trans hMT)
      linarith only [b, c])
    hapartM hnearM hEMA hclMA hgA0 hgA5 hΨA hswA
  refine ⟨gA, gB, hΨA, hΨB, hgA0, hgA5, hgB0, hgB5, ?_⟩
  unfold WallRadarLorentz
  intro D e
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hv := vRel_half_one
  rw [← scaledTrainF_deriv_lift_zero gB] at He Hr Hμ
  rw [← scaledTrainF_deriv_lift_zero gA] at Hρ Hm
  unfold wallRun
  exact tri_radar_lorentz (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
    (scaledTrainF_periodic gB) (scaledTrainF_periodic gB) (scaledTrainF_periodic gB)
    (scaledTrainF_periodic gA) (scaledTrainF_periodic gA)
    (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB)
    (contDiff_scaledTrainF gA) (contDiff_scaledTrainF gA) (chainRay _ hψ)
    (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB)
    (scaledTrainF_lift_zero gB) (scaledTrainF_lift_zero gB) (scaledTrainF_lift_zero gB)
    (scaledTrainF_lift_zero gA) (scaledTrainF_lift_zero gA) hrep hrep hrep hrep hrep
    hv.1.le (by linarith only [hv.2]) hRA
    (wall_observer_clock_rate_relation hK M hΔ0 (p := 1 / 2) (by norm_num))
    (radar_times_relay d hv.1) (radar_times_return d hv.1) le_rfl le_rfl le_rfl le_rfl
    le_rfl He Hr Hμ Hρ Hm

end Radar

end CSD.RecordLayer

end
