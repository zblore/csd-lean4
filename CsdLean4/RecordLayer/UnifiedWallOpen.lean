/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallRadar
public import CsdLean4.RecordLayer.UnifiedTriFibre

/-!
# The walled chain's run from an open set of pointer angles

**Category:** 7-SigmaLayer (the record layer). BACKLOG #430 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 9 of the research delivery
plan of 2026-11-16 (an open set of pointer angles), sixth part. No new assumption beyond
UA-18.

`tri_wall_radar_lorentz` (#423) is stated for the five pointers started at `(1/12, 0)`, a
set of measure zero. This module states it on a neighbourhood of that start.

* `wallRunAt` — the walled chain's run from any five pointer angles; `wallRun_eq_wallRunAt`;
* ★★★ `tri_wall_radar_lorentz_open` — under the hypotheses of #423 with the five closing
  sizes strict: the statement of #423, and for every `ϵ > 0` a radius `ρ > 0` such that from
  every five pointer angles within `ρ` of `(1/12, 0)` the five pointers have counts in the
  same reading windows and the counts satisfy the Lorentz statement with the errors of #423
  enlarged by `ϵ`.

## Exact scope

* **The radius is not explicit.** It exists for each `ϵ`; it depends on the strengths, the
  flow times, the slack in the sizes and the operator norms of the five gates. It does not
  depend on the labelling of the carrier's basis.
* **The hypotheses of #423 remain**: the bounds on where the carriers are, the seven angle
  conditions and the sizes. `UnifiedRadarRun.lean` (#426, #431) discharges them for the
  family.
* **The strengths are not chosen here**; they are those of #411 and #417.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-193, UD-197, UD-198, UD-199, UD-200); `RecordLayer/UnifiedWallRadar.lean`
(#423: `wallRun`, `WallRadarLorentz`, `tri_wall_radar_lorentz`);
`RecordLayer/UnifiedTriFibre.lean` (#430: `tri_radar_lorentz_open`, `NearStart`,
`coincShift_closed_le`); `RecordLayer/UnifiedWallObserver.lean` (#420:
`wall_observer_gate_weights`, `wall_observer_radar_histories`);
`RecordLayer/UnifiedWallRelay.lean` (#421: `wall_relay_gate_weights`, `wall_relay_history`);
`RecordLayer/UnifiedWallMeeting.lean` (#422: `wall_meeting_gate_weights`,
`wall_meeting_history_moving`, `wall_meeting_history_rest`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-- **The walled chain's run from any pointer angles**: `wallRun` (#423) with the five
pointers started at `θ, ψ, χ, ξ, ζ`. -/
def wallRunAt (n N M : ℕ) (μ Δ w gA gB : ℝ) {D : ℕ}
    (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1))
    (p : GenArena (ZMod (M + 1) × Fin 2))
    (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ χ ξ ζ : KTorus) :
    ℝ → PentaSigma D :=
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
    (contDiff_scaledTrainF gA) (contDiff_scaledTrainF gA) p qa qb θ ψ χ ξ ζ

/-- The run of #423 is the run from the start `(1/12, 0)` of every pointer. -/
theorem wallRun_eq_wallRunAt (n N M : ℕ) (μ Δ w gA gB : ℝ) {D : ℕ}
    (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1))
    (p : GenArena (ZMod (M + 1) × Fin 2))
    (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    wallRun n N M μ Δ w gA gB e p qa qb
      = wallRunAt n N M μ Δ w gA gB e p qa qb
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) :=
  rfl

section Radar

variable {n N M : ℕ} {Δ : ℝ}

local notation "RB" => ringRate (1200 * n * N) M (1 / 2) Δ

local notation "RA" => ringRate (1200 * n * N) M 0 Δ

local notation "vB" => vRel 1 1 (1 / 2)

local notation "κB" => Δ + (ringLen (1200 * n * N) / (M + 1 : ℕ)) ^ 2 * (1 / 2) ^ 3 / 6

local notation "φA" h => 0 + 2 * Real.pi * (ZMod.val h) / (M + 1 : ℕ)

/-- ★★★ **Five counts and the Lorentz statement on the walled chain, from an open set of
pointer angles.** Under the hypotheses of `tri_wall_radar_lorentz` (#423), with the five
closing sizes strict: for some strengths `0 < g_A ≤ R₀/5` and `0 < g_B ≤ R_B/5`,

* the statement of #423 holds for the pointers started at `(1/12, 0)`; and
* for every `ϵ > 0` there is a radius `ρ > 0` such that from every five pointer angles
  within `ρ` of `(1/12, 0)`, at every choice of flow times in the same five reading windows,
  the five pointers of `wallRunAt` have counts, and the counts satisfy the Lorentz statement
  with the errors of #423 enlarged by `ϵ`; and
* every `ρ > 0` is such a radius which, for a slack `s > 0` below every margin of the sizes
  and a bound `γ` on `R₀/5` and `R_B/5`, satisfies `ρ ≤ s/4`, `ρ C T ≤ s/4` and
  `ρ C (K₁ + K₂) ≤ ϵ` with `C = 20 γ² T + 14 γ` (the five gates have norm at most `1`). -/
theorem tri_wall_radar_lorentz_open {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
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
    (hcl3 : 2 * (RB / 5) * ε * (t3 - tb) < 1 / 6)
    (hcl5 : 2 * (RB / 5) * ε * (t5 - t4) < 1 / 6)
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
    (hclR : 2 * (RA / 5) * ε * (tcR - tbR) < 1 / 6)
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
    (hclMB : 2 * (RB / 5) * ε * (tcM - tbM) < 1 / 6)
    (hEMA : 1 / (24 * (j : ℝ)) + 2 * (RA / 5) * ε * tM < 1 / 12)
    (hclMA : 2 * (RA / 5) * ε * (tcM - tbM) < 1 / 6) :
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
                  / Real.sqrt (1 - vB ^ 2))
          (tR - tM) ((gatedErr (2 * gA) tR tbR + gatedErr (2 * gA) tM tbM) / RA)
      ∧ (∀ ϵ : ℝ, 0 < ϵ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ ψ χ ξ ζ : KTorus, NearStart ρ θ →
        NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
        WallRadarLorentz M
          (fun e => wallRunAt n N M μ Δ w gA gB e (chainRay _ hψ)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB)
            θ ψ χ ξ ζ)
          RA vB tb t3 t4 t5 tbM tcM tbR tcR
          ((((gatedErr (2 * gB) tE tb / RA + (κB) * tE + |tE - 0|)
                  + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4
                        + RB * (tb - tE)) / RA
                      + (κB) * t3 + |t3 - radarTRet d vB|)) / 2
                + (gatedErr (2 * gB) tM tbM / RA + (κB) * tM + |tM - radarTM d vB|)
                + ((gatedErr (2 * gA) tR tbR / RA + |tR - radarTR d|)
                    + (gatedErr (2 * gA) tM tbM / RA + |tM - radarTM d vB|))
                  / Real.sqrt (1 - vB ^ 2))
            + ϵ)
          ((((gatedErr (2 * gB) tE tb / RA + (κB) * tE + |tE - 0|)
                  + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4
                        + RB * (tb - tE)) / RA
                      + (κB) * t3 + |t3 - radarTRet d vB|)) / 2
                + vB * ((gatedErr (2 * gA) tR tbR / RA + |tR - radarTR d|)
                    + (gatedErr (2 * gA) tM tbM / RA + |tM - radarTM d vB|))
                  / Real.sqrt (1 - vB ^ 2))
            + ϵ)
          (tR - tM) ((gatedErr (2 * gA) tR tbR + gatedErr (2 * gA) tM tbM) / RA + ϵ))
      ∧ ∀ ϵ s γ ρ : ℝ, RA / 5 ≤ γ → RB / 5 ≤ γ → 0 < s →
        1 / 4 * (1 - Real.cos (RB * tE)) + 1 / (24 * (j : ℝ)) + 2 * (RB / 5) * ε * tE
            + 2 * (RB / 5) * (tb - tE)
            + (1 / (24 * (j : ℝ)) + 2 * (RB / 5) * ε * (t3 - tb)) ≤ 1 / 12 - s →
        1 / (24 * (j : ℝ)) + 2 * (RB / 5) * ε * tM ≤ 1 / 12 - s →
        1 / (24 * (j : ℝ)) + 2 * (RA / 5) * ε * tR ≤ 1 / 12 - s →
        1 / (24 * (j : ℝ)) + 2 * (RA / 5) * ε * tM ≤ 1 / 12 - s →
        2 * (RB / 5) * ε * (t3 - tb) ≤ 1 / 6 - s → 2 * (RB / 5) * ε * (t5 - t4) ≤ 1 / 6 - s →
        2 * (RB / 5) * ε * (tcM - tbM) ≤ 1 / 6 - s → 2 * (RA / 5) * ε * (tcR - tbR) ≤ 1 / 6 - s →
        2 * (RA / 5) * ε * (tcM - tbM) ≤ 1 / 6 - s →
        0 < ρ → ρ ≤ s / 4 → ρ * ((20 * γ ^ 2 * 1 ^ 2 * T + 14 * γ * 1) * T) ≤ s / 4 →
        ρ * ((20 * γ ^ 2 * 1 ^ 2 * T + 14 * γ * 1)
          * ((6 * Real.pi * (((tb - tE) / RA + ((tb - tE) + ((tb - tE) + (t4 - t3))) / RA) / 2
            + (tbM - tM) / RA + ((tbR - tR) / RA + (tbM - tM) / RA) / Real.sqrt (1 - vB ^ 2)))
            + (6 * Real.pi * (((tb - tE) / RA + ((tb - tE) + ((tb - tE) + (t4 - t3))) / RA) / 2
            + vB * ((tbR - tR) / RA + (tbM - tM) / RA) / Real.sqrt (1 - vB ^ 2))))) ≤ ϵ →
        ∀ θ ψ χ ξ ζ : KTorus, NearStart ρ θ →
        NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
        WallRadarLorentz M
          (fun e => wallRunAt n N M μ Δ w gA gB e (chainRay _ hψ)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB)
            θ ψ χ ξ ζ)
          RA vB tb t3 t4 t5 tbM tcM tbR tcR
          ((((gatedErr (2 * gB) tE tb / RA + (κB) * tE + |tE - 0|)
                  + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4
                        + RB * (tb - tE)) / RA
                      + (κB) * t3 + |t3 - radarTRet d vB|)) / 2
                + (gatedErr (2 * gB) tM tbM / RA + (κB) * tM + |tM - radarTM d vB|)
                + ((gatedErr (2 * gA) tR tbR / RA + |tR - radarTR d|)
                    + (gatedErr (2 * gA) tM tbM / RA + |tM - radarTM d vB|))
                  / Real.sqrt (1 - vB ^ 2))
            + ϵ)
          ((((gatedErr (2 * gB) tE tb / RA + (κB) * tE + |tE - 0|)
                  + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4
                        + RB * (tb - tE)) / RA
                      + (κB) * t3 + |t3 - radarTRet d vB|)) / 2
                + vB * ((gatedErr (2 * gA) tR tbR / RA + |tR - radarTR d|)
                    + (gatedErr (2 * gA) tM tbM / RA + |tM - radarTM d vB|))
                  / Real.sqrt (1 - vB ^ 2))
            + ϵ)
          (tR - tM) ((gatedErr (2 * gA) tR tbR + gatedErr (2 * gA) tM tbM) / RA + ϵ) := by
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
    hnear hapart hback hcl3.le hcl5.le hband hgB0 hgB5 hΨB hswB
  have Hμ := wall_meeting_history_moving hn hN hM hΔ0 h (-(Real.pi / (2 * RA))) hΨA hδ0 hδ
    hw hwπ hε htM hMb hMc hTMB
    (fun s h0 h1 => by
      obtain ⟨-, b, c⟩ := hbud s h0 (h1.trans hMT)
      linarith only [b, c])
    hapartM hnearM hEMB hclMB.le hgB0 hgB5 hΨB hswB
  have Hρ := wall_relay_history hn hN hM hμ0 hμ1 hΔ0 hlo hhi hp₀ hWD t₀ h hψ hδ0 hδ hw hwπ
    hε htR hRb hRc hTR
    (fun s h0 h1 => by
      obtain ⟨a, b, -⟩ := hbud s h0 (h1.trans hRT)
      linarith only [a, b])
    hapartR hnearR hER hclR.le hgA0 hgA5 hΨA hswA
  have Hm := wall_meeting_history_rest hn hN hM hΔ0 h (-(Real.pi / (2 * RB))) hΨB hδ0 hδ
    hw hwπ hε htM hMb hMc hTMA
    (fun s h0 h1 => by
      obtain ⟨-, b, c⟩ := hbud s h0 (h1.trans hMT)
      linarith only [b, c])
    hapartM hnearM hEMA hclMA.le hgA0 hgA5 hΨA hswA
  -- the weights while the gates are closed
  have hRB0 : 0 < RB := by
    have hR : Δ / 2 ≤ RB :=
      half_le_levelClockRate hΔ0.le
        (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
    linarith only [hR, hΔ0]
  obtain ⟨-, wAway, wBack⟩ := wall_observer_gate_weights (ε := ε) hn hN hM hμ0 hμ1 hΔ0 hlo hhi hp₀
      hWD
    t₀ (-(Real.pi / (2 * RB))) hψ hΨB hδ0 hδ hw hwπ htE hEb hb3 h34 h45
    (fun s h0 h1 => by
      obtain ⟨a, -, c⟩ := hbud s h0 (h1.trans h5T)
      linarith only [a, c])
    hnear hapart hback
  obtain ⟨-, wR⟩ := wall_relay_gate_weights (ε := ε) hn hN hM hμ0 hμ1 hΔ0 hlo hhi hp₀ hWD t₀
    (-(Real.pi / (2 * RA))) h hψ hΨA hδ0 hδ hw hwπ htR hRb hRc
    (fun s h0 h1 => by
      obtain ⟨a, b, -⟩ := hbud s h0 (h1.trans hRT)
      linarith only [a, b])
    hapartR hnearR
  obtain ⟨-, wM⟩ := wall_meeting_gate_weights (ε := ε) hn hN hM hΔ0 h (-(Real.pi / (2 * RA)))
    (-(Real.pi / (2 * RB))) hΨA hΨB hδ0 hδ hw hwπ htM hMb hMc
    (fun s h0 h1 => by
      obtain ⟨-, b, c⟩ := hbud s h0 (h1.trans hMT)
      linarith only [b, c])
    hapartM hnearM
  have hY : ∀ s' (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)),
      |arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) s'
          * levelSwap (ZMod (M + 1) × Fin 2)) q|
        ≤ arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) s') q :=
    fun s' q => abs_arenaObs_siteSel_mul_levelSwap_le
      (fun x : ZMod (M + 1) × Fin 2 => x.1) s' q
  have ce := coincShift_closed_le (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-gB)
    (chainRay _ hψ) (deviceRay _ hΨB) hε wAway
  have cr := coincShift_closed_le (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k k')
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-gB)
    (chainRay _ hψ) (deviceRay _ hΨB) hε wBack
  have cμ := coincShift_closed_le (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k k')
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-gB)
    (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB) hε wM
  have cρ := coincShift_closed_le (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k k')
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-gA)
    (chainRay _ hψ) (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) hε wR
  have cm := coincShift_closed_le (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k' k)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-gA)
    (deviceRay _ hΨB) (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) hε
    (fun s hbs hs => by
      have h1 := wM s hbs hs
      rw [← arenaObs_coincProj_prodRay_swap (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k k')]
            at h1
      exact h1)
  refine ⟨gA, gB, hΨA, hΨB, hgA0, hgA5, hgB0, hgB5, ?_, ?_, ?_⟩
  · unfold WallRadarLorentz
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
  · intro ϵ hϵ
    have hv := vRel_half_one
    have hzB : |(-gB : ℝ)| = gB := by rw [abs_neg, abs_of_pos hgB0]
    have hzA : |(-gA : ℝ)| = gA := by rw [abs_neg, abs_of_pos hgA0]
    have k1 : 2 * gB * ε * tE ≤ 2 * (RB / 5) * ε * tE := by
      have : 0 ≤ ε * tE := mul_nonneg hε htE
      nlinarith only [this, hgB5]
    have k2 : 2 * gB * ε * (t3 - tb) ≤ 2 * (RB / 5) * ε * (t3 - tb) := by
      have : 0 ≤ ε * (t3 - tb) := mul_nonneg hε (sub_nonneg.2 hb3)
      nlinarith only [this, hgB5]
    have k3 : 2 * gB * ε * (t5 - t4) ≤ 2 * (RB / 5) * ε * (t5 - t4) := by
      have : 0 ≤ ε * (t5 - t4) := mul_nonneg hε (sub_nonneg.2 h45)
      nlinarith only [this, hgB5]
    have k4 : 2 * gB * (tb - tE) ≤ 2 * (RB / 5) * (tb - tE) := by
      have : 0 ≤ tb - tE := sub_nonneg.2 hEb
      nlinarith only [this, hgB5]
    have k5 : 2 * gB * ε * (tcM - tbM) ≤ 2 * (RB / 5) * ε * (tcM - tbM) := by
      have : 0 ≤ ε * (tcM - tbM) := mul_nonneg hε (sub_nonneg.2 hMc)
      nlinarith only [this, hgB5]
    have k6 : 2 * gA * ε * (tcR - tbR) ≤ 2 * (RA / 5) * ε * (tcR - tbR) := by
      have : 0 ≤ ε * (tcR - tbR) := mul_nonneg hε (sub_nonneg.2 hRc)
      nlinarith only [this, hgA5]
    have k7 : 2 * gA * ε * (tcM - tbM) ≤ 2 * (RA / 5) * ε * (tcM - tbM) := by
      have : 0 ≤ ε * (tcM - tbM) := mul_nonneg hε (sub_nonneg.2 hMc)
      nlinarith only [this, hgA5]
    have hcosR : 0 ≤ 1 / 4 * (1 - Real.cos (RB * tE)) := by
      have := Real.cos_le_one (RB * tE)
      linarith only [this]
    have he0 : (0 : ℝ) ≤ 1 / (24 * (j : ℝ)) := by positivity
    have hGa : 0 ≤ 2 * (RB / 5) * ε * tE := by positivity
    have hG3 : 0 ≤ 2 * (RB / 5) * ε * (t3 - tb) :=
      mul_nonneg (by positivity) (sub_nonneg.2 hb3)
    have hGab : 0 ≤ 2 * (RB / 5) * (tb - tE) :=
      mul_nonneg (by positivity) (sub_nonneg.2 hEb)
    have hga : 0 ≤ 2 * gB * ε * tE := by positivity
    have hg3 : 0 ≤ 2 * gB * ε * (t3 - tb) := mul_nonneg (by positivity) (sub_nonneg.2 hb3)
    have hgab : 0 ≤ 2 * gB * (tb - tE) := mul_nonneg (by positivity) (sub_nonneg.2 hEb)
    have hsa := He.swing tE htE le_rfl
    have hmid := He.mid tE tb le_rfl hEb le_rfl
    rw [abs_le] at hsa hmid
    obtain ⟨ρ, hρ0, Hop⟩ := tri_radar_lorentz_open
      (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
      (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
      (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
      gB gB gB gA gA (chainRay _ hψ)
      (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB)
      hv.1.le (by linarith only [hv.2]) hRA
      (wall_observer_clock_rate_relation hK M hΔ0 (p := 1 / 2) (by norm_num))
      (radar_times_relay d hv.1) (radar_times_return d hv.1) le_rfl le_rfl le_rfl le_rfl
      le_rfl He Hr Hμ Hρ Hm ce cr cμ cρ cm
      (by rw [hzB]; linarith only [hcl3, k2]) (by rw [hzB]; linarith only [hcl5, k3])
      (by rw [hzB]; linarith only [hclMB, k5]) (by rw [hzA]; linarith only [hclR, k6])
      (by rw [hzA]; linarith only [hclMA, k7])
      ⟨by
        linarith only [hsa.1, hsa.2, hmid.1, hmid.2, hband, k1, k2, k4, hcosR, hga, hg3,
          hgab, he0, hGa, hG3, hGab],
       by
        linarith only [hsa.1, hsa.2, hmid.1, hmid.2, hband, k1, k2, k4, hcosR, hga, hg3,
          hgab, he0, hGa, hG3, hGab]⟩ hϵ
    refine ⟨ρ, hρ0, fun θ ψ χ ξ ζ hθ hψ' hχ hξ hζ => ?_⟩
    unfold WallRadarLorentz
    intro D e
    exact Hop D e θ ψ χ ξ ζ hθ hψ' hχ hξ hζ
  · intro ϵ s γ ρ hγA hγB hs hsb hsμ hsρ hsm hc3 hc5 hcMB hcR hcMA hρ0 hρs hρA hρB
      θ ψ χ ξ ζ hθ hψ' hχ hξ hζ
    have hv := vRel_half_one
    have hzB : |(-gB : ℝ)| = gB := by rw [abs_neg, abs_of_pos hgB0]
    have hzA : |(-gA : ℝ)| = gA := by rw [abs_neg, abs_of_pos hgA0]
    have k1 : 2 * gB * ε * tE ≤ 2 * (RB / 5) * ε * tE := by
      have : 0 ≤ ε * tE := mul_nonneg hε htE
      nlinarith only [this, hgB5]
    have k2 : 2 * gB * ε * (t3 - tb) ≤ 2 * (RB / 5) * ε * (t3 - tb) := by
      have : 0 ≤ ε * (t3 - tb) := mul_nonneg hε (sub_nonneg.2 hb3)
      nlinarith only [this, hgB5]
    have k3 : 2 * gB * ε * (t5 - t4) ≤ 2 * (RB / 5) * ε * (t5 - t4) := by
      have : 0 ≤ ε * (t5 - t4) := mul_nonneg hε (sub_nonneg.2 h45)
      nlinarith only [this, hgB5]
    have k4 : 2 * gB * (tb - tE) ≤ 2 * (RB / 5) * (tb - tE) := by
      have : 0 ≤ tb - tE := sub_nonneg.2 hEb
      nlinarith only [this, hgB5]
    have k5 : 2 * gB * ε * (tcM - tbM) ≤ 2 * (RB / 5) * ε * (tcM - tbM) := by
      have : 0 ≤ ε * (tcM - tbM) := mul_nonneg hε (sub_nonneg.2 hMc)
      nlinarith only [this, hgB5]
    have k6 : 2 * gA * ε * (tcR - tbR) ≤ 2 * (RA / 5) * ε * (tcR - tbR) := by
      have : 0 ≤ ε * (tcR - tbR) := mul_nonneg hε (sub_nonneg.2 hRc)
      nlinarith only [this, hgA5]
    have k7 : 2 * gA * ε * (tcM - tbM) ≤ 2 * (RA / 5) * ε * (tcM - tbM) := by
      have : 0 ≤ ε * (tcM - tbM) := mul_nonneg hε (sub_nonneg.2 hMc)
      nlinarith only [this, hgA5]
    have hcosR : 0 ≤ 1 / 4 * (1 - Real.cos (RB * tE)) := by
      have := Real.cos_le_one (RB * tE)
      linarith only [this]
    have he0 : (0 : ℝ) ≤ 1 / (24 * (j : ℝ)) := by positivity
    have hGa : 0 ≤ 2 * (RB / 5) * ε * tE := by positivity
    have hG3 : 0 ≤ 2 * (RB / 5) * ε * (t3 - tb) :=
      mul_nonneg (by positivity) (sub_nonneg.2 hb3)
    have hGab : 0 ≤ 2 * (RB / 5) * (tb - tE) :=
      mul_nonneg (by positivity) (sub_nonneg.2 hEb)
    have hga : 0 ≤ 2 * gB * ε * tE := by positivity
    have hg3 : 0 ≤ 2 * gB * ε * (t3 - tb) := mul_nonneg (by positivity) (sub_nonneg.2 hb3)
    have hgab : 0 ≤ 2 * gB * (tb - tE) := mul_nonneg (by positivity) (sub_nonneg.2 hEb)
    have hsa := He.swing tE htE le_rfl
    have hmid := He.mid tE tb le_rfl hEb le_rfl
    rw [abs_le] at hsa hmid
    have k8 : 2 * gB * ε * tM ≤ 2 * (RB / 5) * ε * tM := by
      have : 0 ≤ ε * tM := mul_nonneg hε htM
      nlinarith only [this, hgB5]
    have k9 : 2 * gA * ε * tR ≤ 2 * (RA / 5) * ε * tR := by
      have : 0 ≤ ε * tR := mul_nonneg hε htR
      nlinarith only [this, hgA5]
    have k10 : 2 * gA * ε * tM ≤ 2 * (RA / 5) * ε * tM := by
      have : 0 ≤ ε * tM := mul_nonneg hε htM
      nlinarith only [this, hgA5]
    have hYY := levelSwap_mul_self (n := ZMod (M + 1) × Fin 2)
    obtain ⟨n1, n2, n3, n4, n5⟩ := tri_gate_norms_le_one
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
      (wallNear (M + 1) w) (fun k k' => ¬ wallNear (M + 1) w k k')
      (fun k k' => ¬ wallNear (M + 1) w k k') (fun k k' => ¬ wallNear (M + 1) w k k')
      (fun k k' => ¬ wallNear (M + 1) w k k')
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) hYY
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) hYY
    have gB' : |gB| ≤ γ := by
      rw [abs_of_pos hgB0]
      linarith only [hgB5, hγB]
    have gA' : |gA| ≤ γ := by
      rw [abs_of_pos hgA0]
      linarith only [hgA5, hγA]
    have Hnear := tri_radar_lorentz_near
      (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
      (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
      (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
      gB gB gB gA gA (chainRay _ hψ)
      (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB)
      hv.1.le (by linarith only [hv.2]) hRA
      (wall_observer_clock_rate_relation hK M hΔ0 (p := 1 / 2) (by norm_num))
      (radar_times_relay d hv.1) (radar_times_return d hv.1) le_rfl le_rfl le_rfl le_rfl
      le_rfl He Hr Hμ Hρ Hm ce cr cμ cρ cm n1 n2 n3 n4 n5 gB' gB' gB' gA' gA'
      (h34.trans (h45.trans h5T)) h5T hMT hRT hMT hs
      (by linarith only [hsb, k1, hcosR, hGab, he0, hG3])
      (by linarith only [hsb, k1, hcosR, hGab, he0, hG3])
      (by linarith only [hsb, k2, hcosR, hGab, he0, hGa])
      (by
        linarith only [hsa.1, hsa.2, hmid.1, hmid.2, hsb, k1, k2, k4, hcosR, hga, hg3,
          hgab, he0, hGa, hG3, hGab, hs])
      (by
        linarith only [hsa.1, hsa.2, hmid.1, hmid.2, hsb, k1, k2, k4, hcosR, hga, hg3,
          hgab, he0, hGa, hG3, hGab, hs])
      (by linarith only [hsμ, k8]) (by linarith only [hsρ, k9]) (by linarith only [hsm, k10])
      (by rw [hzB]; linarith only [hc3, k2]) (by rw [hzB]; linarith only [hc5, k3])
      (by rw [hzB]; linarith only [hcMB, k5]) (by rw [hzA]; linarith only [hcR, k6])
      (by rw [hzA]; linarith only [hcMA, k7]) hρ0 hρs hρA hρB
    unfold WallRadarLorentz
    intro D e
    exact Hnear D e θ ψ χ ξ ζ hθ hψ' hχ hξ hζ

end Radar

end CSD.RecordLayer

end
