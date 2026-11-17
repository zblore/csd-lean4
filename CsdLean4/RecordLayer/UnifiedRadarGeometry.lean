/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarRun

/-!
# The family's run on an open set of pointer angles

**Category:** 7-SigmaLayer (the record layer). BACKLOG #431 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Tasks 9 and 10 of the research
delivery plan of 2026-11-16. No new assumption beyond UA-18.

`radar_family_lorentz` (#426, strengthened in #431) gives the five counts and the Lorentz
statement for the family's run from every five pointer angles within a radius of the start
`(1/12, 0)`. This module states it for an open set of the ten angles and under the plan's
name.

* `isOpen_nearStart` — the pointer angles within `ρ` of the start are an open set of the
  torus;
* ★★★ `csd_operational_lorentz_from_records` — for every `k ≥ 100` and every even ring with
  `M ≥ 210000 N³`: there are strengths and an open set `U` of the five pointers' angles,
  containing the start of every pointer at `(1/12, 0)`, such that from every point of `U` the
  five pointers of the walled chain's run have counts at every choice of flow times in the
  five reading windows, and the counts satisfy both components of the Lorentz statement of
  #402 for `v = vRel 1 1 (1/2)` within `151 K/k`;
* `radar_error_relative`, `tendsto_radar_error_relative` — `151 K/k` is `151/(π k)` of the
  distance `π K`, and that ratio tends to `0`.

## Exact scope

* **No hypothesis on histories, on the speed of the messenger, on a dilation law or on radar
  relations.** The hypotheses are `k ≥ 100`, the size of the ring and its parity.
* **The open set is not explicit**: a product of intervals of an unnamed radius `ρ > 0`,
  which depends on `k`, on the ring and on the operator norms of the five gates. Nothing is
  said about its measure, and nothing says the radius does not shrink as `k` grows.
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
(UA-18, UO-16, UD-164, UD-193, UD-196, UD-200, UD-201); `RecordLayer/UnifiedRadarRun.lean`
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
      ∧ IsOpen U
      ∧ (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) ∈ U
      ∧ ∀ Θ ∈ U, WallRadarLorentz M
          (fun e => wallRunAt (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
            gA gB e (chainRay _ hψ)
            (deviceRay (deviceShift (H : ZMod (M + 1)) _)
              (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB)
            Θ.1 Θ.2.1 Θ.2.2.1 Θ.2.2.2.1 Θ.2.2.2.2)
          (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) (vRel 1 1 (1 / 2))
          (famTb k) (famT3 k) (famT4 k) (famT5 k) (famTbM k M) (famTcM k M) (famTbR k M)
          (famTcR k M) (151 * (wallK k / k)) (151 * (wallK k / k)) := by
  obtain ⟨hψ, gA, gB, hΨA, hΨB, a1, a2, a3, a4, -, ρ, hρ0, Hop⟩ :=
    radar_family_lorentz hk hM hH
  refine ⟨hψ, gA, gB, hΨA, hΨB,
    {Θ | NearStart ρ Θ.1 ∧ NearStart ρ Θ.2.1 ∧ NearStart ρ Θ.2.2.1 ∧ NearStart ρ Θ.2.2.2.1
      ∧ NearStart ρ Θ.2.2.2.2}, a1, a2, a3, a4, ?_, ?_, ?_⟩
  · have o := isOpen_nearStart ρ
    exact (o.preimage
        (by fun_prop : Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus => Θ.1)).and
      ((o.preimage (by fun_prop :
          Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus => Θ.2.1)).and
        ((o.preimage (by fun_prop :
            Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus => Θ.2.2.1)).and
          ((o.preimage (by fun_prop :
              Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus => Θ.2.2.2.1)).and
            (o.preimage (by fun_prop :
              Continuous fun Θ : KTorus × KTorus × KTorus × KTorus × KTorus => Θ.2.2.2.2)))))
  · exact ⟨nearStart_start hρ0, nearStart_start hρ0, nearStart_start hρ0, nearStart_start hρ0,
      nearStart_start hρ0⟩
  · rintro Θ ⟨h1, h2, h3, h4, h5⟩
    exact Hop _ _ _ _ _ h1 h2 h3 h4 h5

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

end CSD.RecordLayer

end
