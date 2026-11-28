/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedInstance
public import CsdLean4.RecordLayer.UnifiedFineTransit

/-!
# The released return: the time of the detector's count, located

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4, condition
R5; route (γ6) of the task plans).

In `released_arrival_instance` (UD-282) the detector counts `0` at `40M` and `1` at `320M`:
the two times differ by a factor of eight, because the return carrier is a wide packet with a
tail of `1/10`. Here the return carrier is the fine packet of index `n` on a ring (#375): its
weight on the far half of the ring is at most `1/(100k)` until its predicted position is
within the angle `1/k` of that half, and at least `1 − 1/(100k)` once it is `1/k` inside. The
packet's velocity is `4/5` and the far half begins a quarter of the ring away, so the
predicted transit time is `625π n²`.

* `two_fifths_sq_le_one_sub_cos` — `(2/5) x² ≤ 1 − cos x` on `[0, 1]`;
* ★★ `arenaObs_farHalf_finePacket_le`, `le_arenaObs_farHalf_finePacket` — the fine packet's
  free occupancy of the far half, at the margin `1/k`, for `n ≥ 100 k³`;
* ★★★ `released_located_instance` — **the count is located.** The event carrier, its region
  and the fibres are those of UD-282; the return carrier is the fine packet with the detector
  on the far half; `c = 1`. For `k ≥ 2`, `n ≥ 100 k³` and `M k ≤ n²` the detector counts `0`
  at the flow time `1250 n² (π/2 − 1/k)` and `1` at `2M + 1250 n² (π/2 + 4/k)`;
* ★★★ `released_located_idle_instance` — **its control.** With the event pointer coupled to
  nothing the detector counts `0` at the later of those two times;
* ★★ `releasedLocated_window` — **the stated `δ`.** Both times are within the relative
  distance `13/(5k)` of `625π n²`, the first reading is later than `2M`, the end of the
  event's own window, and `2M` is itself at most `(13/(5k)) · 625π n²`.

## Honest scope

⚠️ **The event's time is inside the error.** The event carrier reaches its region between
the flow times `M/4` and `2M`, and `2M ≤ 2n²/k`. So the count is at "the event's time plus
`625π n²`" only in the sense that the event's time is smaller than `δ`. No run here has a
late event, and that the count's time moves with the event's time is not shown.

⚠️ **The prediction `625π n²` uses supplied numbers.** The velocity `4/5` is the band
velocity of the packet's prepared momentum (UA-8), the distance is a quarter of a ring of
physical length `2000π n²`, and `c = 1` is the constant of the release term (UA-22). With
another `c` the delay is divided by `c`. By the test of UO-32 this is the arena's parameter
restated and not a limiting speed.

⚠️ **A family of arenas, not one system.** The ring has at least `640000 n³` sites with
`n ≥ 100 k³`, its hop changes with `n`, and the rates of the two pointers and the window are
fitted to `M`, `n` and `k`.

⚠️ **`δ` holds the reading time.** The detector's rate is `k/(10000 n²)`, so it needs the
flow time `3750 n²/k` at full occupancy to count; that is three fifths of the gap between the
two readings.

⚠️ **One fibre** (both second angles `0`, a null set), a product ray, the event's pointer a
gate that is not read, the event the arrival of UD-245 and not the meeting of UD-261. All
times are flow times (UA-7): no clock at the receiver reads them (R7).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-8, UA-20,
UA-22, UO-26, UO-32, UD-108, UD-245, UD-282, UD-283; §9.4, R5);
`specs/unified-records-spacetime-task-plans.md` (§9, route (γ6));
`RecordLayer/UnifiedReleasedInstance.lean` (`released_detector_records_of_occupancy`,
`released_detector_idle_record_of_occupancy`); `RecordLayer/UnifiedFineTransit.lean`
(`finePacket`, `regionWeight_fine_far`, `regionWeight_fine_near`,
`arenaObs_farHalf_free_finePacket`); `RecordLayer/PacketOccupancy.lean`
(`arenaObs_arrivalBox_le`, `le_arenaObs_arrivalBox`); `RecordLayer/ArcWindow.lean`
(`gateWindow`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Projectivization Matrix.UnitaryGroup MeasureTheory
open NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The fine packet's occupancy of the far half, at the margin `1/k` -/

/-- `(2/5) x² ≤ 1 − cos x` for `0 ≤ x ≤ 1`. -/
theorem two_fifths_sq_le_one_sub_cos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    2 / 5 * x ^ 2 ≤ 1 - Real.cos x := by
  have hb := Real.cos_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at hb
  have h2 := (abs_le.1 hb).2
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have h4 : x ^ 4 ≤ x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]
  linarith [sq_nonneg x]

/-- The arithmetic of the tail: a weight `w ≥ 0` with `w · c ≤ 1/(6ν)`, where
`c ≥ (2/5)(1/κ)²` and `ν ≥ 100 κ³`, is at most `1/(100κ)`. -/
theorem fineTail_le {w c κ ν : ℝ} (hκ : 1 ≤ κ) (hν : 100 * κ ^ 3 ≤ ν) (hw : 0 ≤ w)
    (hc : 2 / 5 * (1 / κ) ^ 2 ≤ c) (h : w * c ≤ 1 / (6 * ν)) : w ≤ 1 / (100 * κ) := by
  have hκ0 : 0 < κ := by linarith
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hν
  have h1 : w * (2 / 5 * (1 / κ) ^ 2) ≤ 1 / (6 * ν) :=
    (mul_le_mul_of_nonneg_left hc hw).trans h
  have h2 : 1 / (6 * ν) ≤ 1 / (600 * κ ^ 3) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h3 : w * (2 / 5 * (1 / κ) ^ 2) * (600 * κ ^ 3) ≤ 1 := by
    rw [← le_div_iff₀ (by positivity)]
    exact h1.trans h2
  have e : w * (2 / 5 * (1 / κ) ^ 2) * (600 * κ ^ 3) = 240 * (w * κ) := by
    field_simp
    ring
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hw hκ0.le]

section Fine

variable {K n k : ℕ}

/-- ★★ **Before the fine packet is within the angle `1/k` of the far half, its free occupancy
of the far half is at most `1/(100k)`**: for `n ≥ 100 k³`, at its own times in
`[0, 1250 n² (π/2 − 1/k)]`. -/
theorem arenaObs_farHalf_finePacket_le (hn : 0 < n) (hK : 640000 * n ^ 3 ≤ K + 1)
    (hk : 1 ≤ k) (hnk : 100 * k ^ 3 ≤ n) {τ : ℝ} (h0 : 0 ≤ τ)
    (h1 : τ ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ))) :
    arenaObs (regionProj (farHalf (K + 1)))
        (arenaKick (idxFreeU (diracHam_isHermitian (L := K + 1) (fineHop n (K + 1)) 3) τ)
          (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK)))
      ≤ 1 / (100 * (k : ℝ)) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnr : (100 : ℝ) * (k : ℝ) ^ 3 ≤ n := by exact_mod_cast hnk
  have hx0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hkr
  have hw0 := arenaObs_regionProj_nonneg (farHalf (K + 1))
    (arenaKick (idxFreeU (diracHam_isHermitian (L := K + 1) (fineHop n (K + 1)) 3) τ)
      (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK)))
  rw [arenaObs_farHalf_free_finePacket hn hK τ] at hw0 ⊢
  exact fineTail_le hkr hnr hw0 (two_fifths_sq_le_one_sub_cos hx0 hx1)
    (regionWeight_fine_far (L := K + 1) hn hK hx0 h0 h1)

/-- ★★ **Once the fine packet is the angle `1/k` inside the far half, its free occupancy of
the far half is at least `1 − 1/(100k)`**: for `n ≥ 100 k³`, at its own times in
`[1250 n² (π/2 + 1/k), 1250 n² (3π/2 − 1/k)]`. -/
theorem le_arenaObs_farHalf_finePacket (hn : 0 < n) (hK : 640000 * n ^ 3 ≤ K + 1)
    (hk : 1 ≤ k) (hnk : 100 * k ^ 3 ≤ n) {τ : ℝ}
    (h0 : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 1 / (k : ℝ)) ≤ τ)
    (h1 : τ ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - 1 / (k : ℝ))) :
    1 - 1 / (100 * (k : ℝ))
      ≤ arenaObs (regionProj (farHalf (K + 1)))
        (arenaKick (idxFreeU (diracHam_isHermitian (L := K + 1) (fineHop n (K + 1)) 3) τ)
          (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK))) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnr : (100 : ℝ) * (k : ℝ) ^ 3 ≤ n := by exact_mod_cast hnk
  have hx0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hkr
  have hw1 := arenaObs_regionProj_le_one (farHalf (K + 1))
    (arenaKick (idxFreeU (diracHam_isHermitian (L := K + 1) (fineHop n (K + 1)) 3) τ)
      (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK)))
  rw [arenaObs_farHalf_free_finePacket hn hK τ] at hw1 ⊢
  have key := fineTail_le hkr hnr (sub_nonneg.2 hw1) (two_fifths_sq_le_one_sub_cos hx0 hx1)
    (regionWeight_fine_near (L := K + 1) hn hK hx0 h0 h1)
  linarith

end Fine

/-! ### The located count -/

section Located

variable {L : ℕ} [NeZero L] {N : ℕ}

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The released return, with the detector's count located.** The event carrier is the
flat packet of UD-245 on its torus (`L = 8M`, `M ≥ 4·10⁶`), read on `arrivalBox`; its pointer
has the profile `(1/(12000 n²)) · trainF` and starts at the angle `1/6` on the fibre `0`. The
window is `gateWindow (1/6) (M/(240000 n²)) (3M/(20000 n²)) (4/5)` and `c = 1`. The return
carrier is the fine packet of index `n` on a ring of `K + 1 ≥ 640000 n³` sites, with the
detector on the far half; the detector's profile is `(k/(20000 n²)) · trainF` and it starts
at `(1/6, 0)`. For `k ≥ 2`, `n ≥ 100 k³` and `M k ≤ n²` the start of the run is in the
compatible region of "the detector has counted `0` at the flow time `1250 n² (π/2 − 1/k)`"
and "the detector has counted `1` at `2M + 1250 n² (π/2 + 4/k)`". -/
theorem released_located_instance {M K n k : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (hk : 2 ≤ k) (hn : 0 < n) (hnk : 100 * k ^ 3 ≤ n) (hMk : M * k ≤ n ^ 2)
    (hK : 640000 * n ^ 3 ≤ K + 1)
    (e : ((Fin 2 → ZMod L) × Fin 2) × (ZMod (K + 1) × Fin 2) ≃ Fin (N + 1))
    (p₀ : CPN (N + 1)) :
    (((idxArenaEquiv e (prodRay (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))
          (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK))),
        ((((1 / 6 : ℝ) : ℝ) : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))), arrivalFibre) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e
          (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
          (siteSetProj Prod.fst (arrivalBox L : Set (Fin 2 → ZMod L)))
          (diracHam (L := K + 1) (fineHop n (K + 1)) 3)
          (scaledTrainF_periodic (1 / (12000 * (n : ℝ) ^ 2)))
          (gateWindow_periodic (1 / 6) ((M : ℝ) / (240000 * (n : ℝ) ^ 2))
            (3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2)) (4 / 5))
          (scaledTrainF_periodic ((k : ℝ) / (20000 * (n : ℝ) ^ 2)))
          (contDiff_scaledTrainF (1 / (12000 * (n : ℝ) ^ 2)))
          (contDiff_gateWindow (1 / 6) ((M : ℝ) / (240000 * (n : ℝ) ^ 2))
            (3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2)) (4 / 5))
          (contDiff_scaledTrainF ((k : ℝ) / (20000 * (n : ℝ) ^ 2))) 1
          (regionProj (farHalf (K + 1)))
          (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK)) p₀).semantics
        [TickReadout.startFact true (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ))) 0,
          TickReadout.startFact true
            (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))) 1] := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hMkr : (M : ℝ) * k ≤ (n : ℝ) ^ 2 := by exact_mod_cast hMk
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have hx0 : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hkr
  have h4ν : (n : ℝ) ^ 2 * (4 / (k : ℝ)) = 4 * ((n : ℝ) ^ 2 * (1 / (k : ℝ))) := by ring
  have ha1 : 3.14 * (n : ℝ) ^ 2 < (n : ℝ) ^ 2 * Real.pi := by nlinarith
  have ha2 : (n : ℝ) ^ 2 * Real.pi < 3.15 * (n : ℝ) ^ 2 := by nlinarith
  have hb0 : 0 < (n : ℝ) ^ 2 * (1 / (k : ℝ)) := mul_pos hν hx0
  have hb1 : (n : ℝ) ^ 2 * (1 / (k : ℝ)) ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
  have hmx : (M : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (k : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hk0]
    exact hMkr
  have hy0 : 0 < (M : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hy1 : (M : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hν]
    linarith
  have hyk : (M : ℝ) * k / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one hν]
    exact hMkr
  have hk100 : 1 / (100 * (k : ℝ)) ≤ 1 / 200 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hk100' : 0 < 1 / (100 * (k : ℝ)) := by positivity
  have hH := latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1
  have hHR := diracHam_isHermitian (L := K + 1) (fineHop n (K + 1)) 3
  have hPh : (siteSetProj (Prod.fst : (Fin 2 → ZMod L) × Fin 2 → Fin 2 → ZMod L)
      (arrivalBox L : Set (Fin 2 → ZMod L))).IsHermitian := siteSetProj_isHermitian _ _
  have hκe : -2 * (scaledTrainF_periodic (1 / (12000 * (n : ℝ) ^ 2))).deriv_periodic.lift
      (0 : AddCircle (1 : ℝ)) = 1 / (6000 * (n : ℝ) ^ 2) := by
    rw [scaledTrainF_deriv_lift_zero]
    ring
  have hρe : -2 * (scaledTrainF_periodic ((k : ℝ) / (20000 * (n : ℝ) ^ 2))).deriv_periodic.lift
      arrivalFibre.2 = (k : ℝ) / (10000 * (n : ℝ) ^ 2) := by
    show -2 * (scaledTrainF_periodic ((k : ℝ) / (20000 * (n : ℝ) ^ 2))).deriv_periodic.lift
      (0 : AddCircle (1 : ℝ)) = _
    rw [scaledTrainF_deriv_lift_zero]
    ring
  have hfree : ∀ s : ℝ, idxCarrierU hH hPh (scaledTrainF_periodic (1 / (12000 * (n : ℝ) ^ 2)))
      (0 : AddCircle (1 : ℝ)) s = idxFreeU hH s :=
    idxCarrierU_of_lift_eq_zero hH hPh _ (scaledTrainF_lift_zero _)
  -- the window
  have w0 : 0 ≤ (M : ℝ) / (240000 * (n : ℝ) ^ 2) := by positivity
  have ew1 : (M : ℝ) / (240000 * (n : ℝ) ^ 2) = (M : ℝ) / (n : ℝ) ^ 2 / 240000 := by
    field_simp
  have ew2 : 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) = 3 * ((M : ℝ) / (n : ℝ) ^ 2) / 20000 := by
    field_simp
  have w1 : (M : ℝ) / (240000 * (n : ℝ) ^ 2) < 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) := by
    rw [ew1, ew2]
    linarith
  have w2 : 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) ≤ 4 / 5 := by
    rw [ew2]
    linarith
  have w3 : 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) + 4 / 5 ≤ 1 := by
    rw [ew2]
    linarith
  -- the event pointer
  have g1 : 1 / (6000 * (n : ℝ) ^ 2) * (1 / 10 * ((M : ℝ) / 4))
      = (M : ℝ) / (240000 * (n : ℝ) ^ 2) := by
    field_simp
    ring
  have g2 : 1 / (6000 * (n : ℝ) ^ 2) * (9 / 10 * (2 * (M : ℝ) - M))
      = 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) := by
    field_simp
    ring
  have g3 : 1 / (6000 * (n : ℝ) ^ 2)
      * (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))) ≤ 4 / 5 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  -- the detector
  have d1 : (k : ℝ) / (10000 * (n : ℝ) ^ 2) * (1 / (100 * (k : ℝ))
      * (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ))))
      = (Real.pi / 2 - 1 / (k : ℝ)) / 800 := by
    field_simp
    ring
  have d2 : (k : ℝ) / (10000 * (n : ℝ) ^ 2) * ((1 - 1 / (100 * (k : ℝ)))
      * (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))
        - (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 1 / (k : ℝ)))))
      = 3 / 8 * (1 - 1 / (100 * (k : ℝ))) := by
    field_simp
    ring
  have d3 : (k : ℝ) / (10000 * (n : ℝ) ^ 2) * (1 / (100 * (k : ℝ))
      * (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ)))
      + (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))
        - 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ))))
      = (Real.pi / 2 - 1 / (k : ℝ)) / 800 + (M : ℝ) * k / (n : ℝ) ^ 2 / 5000 + 5 / 8 := by
    field_simp
    ring
  refine released_detector_records_of_occupancy e hH hPh hHR _ _ _ _ _ _ p₀
    (c := 1) (by norm_num) (arenaObs_regionProj_nonneg _) (arenaObs_regionProj_le_one _) _ _
    (a₀ := 1 / 6) (δ := (M : ℝ) / (240000 * (n : ℝ) ^ 2))
    (lo := 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2)) (hi := 4 / 5)
    (gateWindow_nonneg _ _ _ _) (gateWindow_le_one _ _ _ _)
    (fun x h1 h2 => gateWindow_eq_zero w0 w1 w2 w3 h1 h2)
    (fun x h1 h2 => gateWindow_eq_one w0 w1 w2 w3 h1 h2)
    (by rw [hκe]; positivity) arrivalFibre_mem_readyArc (scaledTrainF_lift_zero _)
    (by rw [hρe]; positivity)
    (s₁ := (M : ℝ) / 4) (s₂ := (M : ℝ)) (s₃ := 2 * (M : ℝ))
    (t₁ := 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ)))
    (u₂ := 2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 1 / (k : ℝ)))
    (t := 2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ)))
    (τ₁ := 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ)))
    (τ₂ := 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 1 / (k : ℝ)))
    (τ₃ := 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - 1 / (k : ℝ)))
    (ε := 1 / 10) (q := 9 / 10) (ε' := 1 / (100 * (k : ℝ))) (q' := 1 - 1 / (100 * (k : ℝ)))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (fun s _ _ => arenaObs_siteSetProj_nonneg _ _ _)
    (fun s _ _ => arenaObs_siteSetProj_le_one _ _ _)
    (fun s hs hs1 => by rw [hfree]; exact arenaObs_arrivalBox_le hL hM hs hs1)
    (fun s hs hs1 => by rw [hfree]; exact le_arenaObs_arrivalBox hL hM hs hs1)
    (by rw [hκe, g1]) (by rw [hκe, g2]) (by rw [hκe]; exact g3)
    (fun τ hτ hτ1 => arenaObs_farHalf_finePacket_le hn hK (by omega) hnk hτ hτ1)
    (fun τ hτ hτ1 => le_arenaObs_farHalf_finePacket hn hK (by omega) hnk hτ hτ1)
    (by linarith) (by linarith) (by linarith)
    (by rw [hρe, d1]; linarith) (by rw [hρe, d2]; linarith) (by rw [hρe, d3]; linarith)

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The control of `released_located_instance`.** The same carriers, window, constant
and profiles, with the event pointer coupled to nothing (`P = 0`). Then the start of the run
is in the compatible region of "the detector has counted `0` at the flow time
`2M + 1250 n² (π/2 + 4/k)`". -/
theorem released_located_idle_instance {M K n k : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (hk : 2 ≤ k) (hn : 0 < n) (hnk : 100 * k ^ 3 ≤ n) (hMk : M * k ≤ n ^ 2)
    (hK : 640000 * n ^ 3 ≤ K + 1)
    (e : ((Fin 2 → ZMod L) × Fin 2) × (ZMod (K + 1) × Fin 2) ≃ Fin (N + 1))
    (p₀ : CPN (N + 1)) :
    (((idxArenaEquiv e (prodRay (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))
          (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK))),
        ((((1 / 6 : ℝ) : ℝ) : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))), arrivalFibre) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e
          (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
          (0 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
          (diracHam (L := K + 1) (fineHop n (K + 1)) 3)
          (scaledTrainF_periodic (1 / (12000 * (n : ℝ) ^ 2)))
          (gateWindow_periodic (1 / 6) ((M : ℝ) / (240000 * (n : ℝ) ^ 2))
            (3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2)) (4 / 5))
          (scaledTrainF_periodic ((k : ℝ) / (20000 * (n : ℝ) ^ 2)))
          (contDiff_scaledTrainF (1 / (12000 * (n : ℝ) ^ 2)))
          (contDiff_gateWindow (1 / 6) ((M : ℝ) / (240000 * (n : ℝ) ^ 2))
            (3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2)) (4 / 5))
          (contDiff_scaledTrainF ((k : ℝ) / (20000 * (n : ℝ) ^ 2))) 1
          (regionProj (farHalf (K + 1)))
          (chainRay (finePacket (L := K + 1) n 0) (finePacket_ne_zero hn hK)) p₀).semantics
        [TickReadout.startFact true
          (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))) 0] := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hMkr : (M : ℝ) * k ≤ (n : ℝ) ^ 2 := by exact_mod_cast hMk
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have hx0 : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hkr
  have h4x : (4 : ℝ) / (k : ℝ) = 4 * (1 / (k : ℝ)) := by ring
  have h4ν : (n : ℝ) ^ 2 * (4 / (k : ℝ)) = 4 * ((n : ℝ) ^ 2 * (1 / (k : ℝ))) := by ring
  have ha1 : 3.14 * (n : ℝ) ^ 2 < (n : ℝ) ^ 2 * Real.pi := by nlinarith
  have hb0 : 0 < (n : ℝ) ^ 2 * (1 / (k : ℝ)) := mul_pos hν hx0
  have hy0 : 0 < (M : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hy1 : (M : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hν]
    nlinarith
  have hH := latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1
  have hHR := diracHam_isHermitian (L := K + 1) (fineHop n (K + 1)) 3
  have hκe : -2 * (scaledTrainF_periodic (1 / (12000 * (n : ℝ) ^ 2))).deriv_periodic.lift
      (0 : AddCircle (1 : ℝ)) = 1 / (6000 * (n : ℝ) ^ 2) := by
    rw [scaledTrainF_deriv_lift_zero]
    ring
  have hρe : -2 * (scaledTrainF_periodic ((k : ℝ) / (20000 * (n : ℝ) ^ 2))).deriv_periodic.lift
      arrivalFibre.2 = (k : ℝ) / (10000 * (n : ℝ) ^ 2) := by
    show -2 * (scaledTrainF_periodic ((k : ℝ) / (20000 * (n : ℝ) ^ 2))).deriv_periodic.lift
      (0 : AddCircle (1 : ℝ)) = _
    rw [scaledTrainF_deriv_lift_zero]
    ring
  have w0 : 0 ≤ (M : ℝ) / (240000 * (n : ℝ) ^ 2) := by positivity
  have ew1 : (M : ℝ) / (240000 * (n : ℝ) ^ 2) = (M : ℝ) / (n : ℝ) ^ 2 / 240000 := by
    field_simp
  have ew2 : 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) = 3 * ((M : ℝ) / (n : ℝ) ^ 2) / 20000 := by
    field_simp
  have w1 : (M : ℝ) / (240000 * (n : ℝ) ^ 2) < 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) := by
    rw [ew1, ew2]
    linarith
  have w2 : 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) ≤ 4 / 5 := by
    rw [ew2]
    linarith
  have w3 : 3 * (M : ℝ) / (20000 * (n : ℝ) ^ 2) + 4 / 5 ≤ 1 := by
    rw [ew2]
    linarith
  have i1 : (k : ℝ) / (10000 * (n : ℝ) ^ 2) * (1 / (100 * (k : ℝ))
      * (2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))))
      = (M : ℝ) / (n : ℝ) ^ 2 / 500000 + (Real.pi / 2 + 4 / (k : ℝ)) / 800 := by
    field_simp
    ring
  refine released_detector_idle_record_of_occupancy e hH Matrix.isHermitian_zero hHR _ _ _ _ _
    _ p₀ (c := 1) (by norm_num) (arenaObs_regionProj_nonneg _)
    (arenaObs_regionProj_le_one _) _ _ (a₀ := 1 / 6) (gateWindow_nonneg _ _ _ _)
    (gateWindow_le_one _ _ _ _) (gateWindow_eq_zero w0 w1 w2 w3 le_rfl (by linarith))
    (by rw [hκe]; positivity) arrivalFibre_mem_readyArc (scaledTrainF_lift_zero _)
    (by rw [hρe]; positivity)
    (t := 2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ)))
    (ε' := 1 / (100 * (k : ℝ))) (by nlinarith)
    (fun s _ _ => arenaObs_zero' _)
    (arenaObs_farHalf_finePacket_le hn hK (by omega) hnk le_rfl (by nlinarith))
    (by rw [hρe, i1]; linarith)

end Located

/-! ### The stated `δ` -/

/-- ★★ **Both reading times are within the relative distance `13/(5k)` of the predicted
transit time `625π n²`**, the first is later than `2M`, the end of the event's own window,
and `2M` is at most `(13/(5k)) · 625π n²`. -/
theorem releasedLocated_window {M n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (hMk : M * k ≤ n ^ 2) :
    625 * Real.pi * (n : ℝ) ^ 2 * (1 - 13 / 5 * (1 / (k : ℝ)))
        ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ))
      ∧ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ)) ≤ 625 * Real.pi * (n : ℝ) ^ 2
      ∧ 625 * Real.pi * (n : ℝ) ^ 2
        ≤ 2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))
      ∧ 2 * (M : ℝ) + 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 4 / (k : ℝ))
        ≤ 625 * Real.pi * (n : ℝ) ^ 2 * (1 + 13 / 5 * (1 / (k : ℝ)))
      ∧ 2 * (M : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - 1 / (k : ℝ))
      ∧ 2 * (M : ℝ) ≤ 13 / 5 * (1 / (k : ℝ)) * (625 * Real.pi * (n : ℝ) ^ 2) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hMkr : (M : ℝ) * k ≤ (n : ℝ) ^ 2 := by exact_mod_cast hMk
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have hx0 : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hkr
  have h4x : (4 : ℝ) / (k : ℝ) = 4 * (1 / (k : ℝ)) := by ring
  have hmx : (M : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (k : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hk0]
    exact hMkr
  rw [h4x]
  generalize (1 : ℝ) / (k : ℝ) = x at hx0 hx1 hmx ⊢
  generalize (n : ℝ) ^ 2 = ν at hν hmx ⊢
  generalize (M : ℝ) = m at hM0 hmx ⊢
  have hb0 : 0 < ν * x := mul_pos hν hx0
  have hb1 : ν * x ≤ ν / 2 := by nlinarith
  have ha1 : 3.14 * ν < ν * Real.pi := by nlinarith
  have hc1 : 3.14 * (ν * x) < ν * x * Real.pi := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end CSD.RecordLayer

end
