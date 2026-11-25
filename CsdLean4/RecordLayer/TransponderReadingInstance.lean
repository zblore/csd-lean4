/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderReading
public import CsdLean4.RecordLayer.TransponderInstance

/-!
# The meeting writes a record: an instance with numbers

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (3) in part: a geometry,
a strength and a pointer for which the hypotheses of UD-260 hold).

`transponder_meeting_record` asks three inequalities that the geometry of UD-257 does not
meet: there the packet's box is wholly in contact for the time `M` and partly in contact for
`3M/4`. Here the contact region is wider, the first coordinate on the arc `Re z < 3/5` seen
from the transponder's antipode, so that the box is apart up to `M/12`, wholly in contact
from `4M/5` to `11M/5`, and the three inequalities close.

## The contact region with a threshold

* `arrivalBoxAt`, `contactBoxAt`, `contactRelAt` — the regions of UD-245 and UD-257 with the
  threshold of the first coordinate a parameter; `arrivalBox_eq_arrivalBoxAt`,
  `contactBox_eq_contactBoxAt`;
* `contactRelAt_contactSite_iff`.

## The geometry

* `cos_dwellAngle_ge`, `cos_dwellAngle_le`;
* ★★ `arrivalBoxAt_disjoint_movedBoxD` — up to `M/12` the packet's box misses the region;
* ★★ `movedBoxD_subset_arrivalBoxAt` — from `4M/5` to `11M/5` it lies in the region;
* `flatTailD_instance_le_long` — the packet's tail is at most `41/2000` up to `3M`.

## The two runs

* `meetingState_ne_zero`;
* ★★★ `transponder_meeting_record_instance` — **`L = 8M`, `M ≥ 10⁹`, strength `3/(5M)`,
  profile `(500/M) · trainF`, start `(1/6, 0)`: the pointer coupled to the transponder's
  second level is not displayed up to the flow time `M/12`, and the counts `0` at `M/12` and
  some `c ≥ 1` at `11M/5` are a record history of the run's start**;
* ★★★ `transponder_reading_control_instance` — **the same preparation, profile and start
  without the contact term: the count is `0` at `11M/5`**.

## Honest scope

⚠️ **The signal is weak and read slowly.** The amplitude in the second level is shown to be
at least `1/20` on `[2M, 11M/5]`; the pointer's rate `1000/M` is chosen so that an occupancy
of `1/400` held for `M/5` carries it a half turn. The rate is fitted: the inequalities leave
it a window of about `[667/M, 39000/M]` (hand arithmetic).

⚠️ **The contact region is most of the ring** along the first axis: the arc `Re z < 3/5`
about the transponder's antipode, in the transponder's frame the arc `Re z > −3/5`. The
packet starts just outside it.

⚠️ **One fibre**, `θ₂ = 0`, where the profile vanishes: a null set. The control holds on
every fibre; it is stated here on the same one.

⚠️ **The count at `11M/5` is at least one and is not computed.** The pointer reads the
transponder where it rests; nothing is shown to travel. One energy for both levels. The
labelling `e` is a parameter. Flow times. No probability is derived or used.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-245, UD-257, UD-260, UD-261); `RecordLayer/TransponderReading.lean`
(`transponder_meeting_record`, `transponder_reading_control`,
`toLp_ne_zero_of_sum_norm_sq_eq_one`); `RecordLayer/TransponderInstance.lean` (`contactSite`,
`toCircle_four_mul`, `contactRel_contactSite_iff`); `RecordLayer/TorusArrivalBox.lean`
(`arrivalBox`, `arrivalAngle_eq`, `re_star_mul_gt_of_re_gt_of_re_ge`,
`abs_angleZD_arrival_le`); `RecordLayer/TorusArrivalExhibit.lean` (`arrivalFibre`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix NormedSpace Set MeasureTheory
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The contact region with a threshold -/

section Region

variable {L : ℕ} [NeZero L]

/-- **The region of `arrivalBox` with a threshold `p`**: the sites whose first coordinate is
on the arc `Re z < −p` and whose second is on the arc `Re z > 3/4`. -/
def arrivalBoxAt (L : ℕ) [NeZero L] (p : ℝ) : Finset (Fin 2 → ZMod L) :=
  arcBoxD (![-1, 1] : Fin 2 → ℂ) (![p, 3 / 4] : Fin 2 → ℝ)

/-- **The contact region with a threshold `p`**, as a box of displacements about the origin:
the first coordinate on the arc `Re z > p`, the second on the arc `Re z > 3/4`. -/
def contactBoxAt (L : ℕ) [NeZero L] (p : ℝ) : Finset (Fin 2 → ZMod L) :=
  arcBoxD (![1, 1] : Fin 2 → ℂ) (![p, 3 / 4] : Fin 2 → ℝ)

/-- **In contact, with a threshold `p`**: the messenger's displacement from the transponder
is in `contactBoxAt`. -/
def contactRelAt (L : ℕ) [NeZero L] (p : ℝ) (a b : Fin 2 → ZMod L) : Prop :=
  a - b ∈ contactBoxAt L p

instance contactRelAt.instDecidableRel (L : ℕ) [NeZero L] (p : ℝ) :
    DecidableRel (contactRelAt L p) :=
  fun a b => inferInstanceAs (Decidable (a - b ∈ contactBoxAt L p))

/-- The detector of UD-245 is the region with the threshold `−1/4`. -/
theorem arrivalBox_eq_arrivalBoxAt : arrivalBox L = arrivalBoxAt L (-1 / 4) := rfl

/-- The contact region of UD-257 is the one with the threshold `−1/4`. -/
theorem contactBox_eq_contactBoxAt : contactBox L = contactBoxAt L (-1 / 4) := rfl

/-- The messenger is in contact with the transponder exactly when it is on `arrivalBoxAt`. -/
theorem contactRelAt_contactSite_iff (p : ℝ) {M : ℕ} (hL : L = 8 * M) (hM : 0 < M)
    (a : Fin 2 → ZMod L) :
    contactRelAt L p a (contactSite L M) ↔ a ∈ arrivalBoxAt L p := by
  have hz : (ZMod.toCircle ((a - contactSite L M) 0) : ℂ) = -(ZMod.toCircle (a 0) : ℂ) := by
    have e : a 0 = (a - contactSite L M) 0 + ((4 * M : ℕ) : ZMod L) := by
      simp [contactSite]
    have h : (ZMod.toCircle (a 0) : ℂ)
        = (ZMod.toCircle ((a - contactSite L M) 0 + ((4 * M : ℕ) : ZMod L)) : ℂ) := by
      rw [← e]
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, toCircle_four_mul hL hM, mul_neg_one] at h
    rw [h, neg_neg]
  have h1 : (a - contactSite L M) 1 = a 1 := by
    simp [contactSite]
  constructor
  · intro h
    have hc : a - contactSite L M
        ∈ arcBoxD (![1, 1] : Fin 2 → ℂ) (![p, 3 / 4] : Fin 2 → ℝ) := h
    show a ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![p, 3 / 4] : Fin 2 → ℝ)
    refine mem_arcBoxD.2 fun i => ?_
    fin_cases i
    · have h0 : p < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 0) : ℂ)).re :=
        mem_arcBoxD.1 hc 0
      rw [hz] at h0
      show p < (star (-1 : ℂ) * (ZMod.toCircle (a 0) : ℂ)).re
      simpa using h0
    · have h0 : (3 / 4 : ℝ)
          < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 1) : ℂ)).re :=
        mem_arcBoxD.1 hc 1
      rw [h1] at h0
      exact h0
  · intro h
    have hc : a ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![p, 3 / 4] : Fin 2 → ℝ) := h
    show a - contactSite L M
      ∈ arcBoxD (![1, 1] : Fin 2 → ℂ) (![p, 3 / 4] : Fin 2 → ℝ)
    refine mem_arcBoxD.2 fun i => ?_
    fin_cases i
    · have h0 : p < (star (-1 : ℂ) * (ZMod.toCircle (a 0) : ℂ)).re :=
        mem_arcBoxD.1 hc 0
      show p < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 0) : ℂ)).re
      rw [hz]
      simpa using h0
    · have h0 : (3 / 4 : ℝ) < (star (1 : ℂ) * (ZMod.toCircle (a 1) : ℂ)).re :=
        mem_arcBoxD.1 hc 1
      show (3 / 4 : ℝ)
        < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 1) : ℂ)).re
      rw [h1]
      exact h0

/-! ### The geometry -/

omit [NeZero L] in
/-- Up to the flow time `M/12` the drift angle is at most `π/18`: its cosine is at least
`49/50`. -/
theorem cos_dwellAngle_ge {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ M / 12) :
    (49 / 50 : ℝ)
      ≤ Real.cos (2 * Real.pi / L * groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 * s) := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [arrivalAngle_eq hL hM]
  have hc0 : 0 ≤ 2 * Real.pi / (3 * (M : ℝ)) := by positivity
  have e1 : 2 * Real.pi / (3 * (M : ℝ)) * (M / 12) = Real.pi / 18 := by
    field_simp
    ring
  have hup := mul_le_mul_of_nonneg_left h1 hc0
  rw [e1] at hup
  have hlo := mul_nonneg hc0 h0
  generalize 2 * Real.pi / (3 * (M : ℝ)) * s = a at hup hlo ⊢
  have hπ := Real.pi_lt_d2
  have ha : a ≤ 7 / 40 := by linarith
  have ha2 : a ^ 2 ≤ (7 / 40) ^ 2 := pow_le_pow_left₀ hlo ha 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := a)
  norm_num at ha2
  linarith

omit [NeZero L] in
/-- From `4M/5` to `11M/5` the drift angle is between `8π/15` and `22π/15`: its cosine is at
most `−1/10`. -/
theorem cos_dwellAngle_le {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h1 : 4 * (M : ℝ) / 5 ≤ s) (h2 : s ≤ 11 * (M : ℝ) / 5) :
    Real.cos (2 * Real.pi / L * groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 * s)
      ≤ -1 / 10 := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [arrivalAngle_eq hL hM]
  have hc0 : 0 ≤ 2 * Real.pi / (3 * (M : ℝ)) := by positivity
  have e2 : 2 * Real.pi / (3 * (M : ℝ)) * (4 * M / 5) = 8 * Real.pi / 15 := by
    field_simp
    ring
  have e3 : 2 * Real.pi / (3 * (M : ℝ)) * (11 * M / 5) = 22 * Real.pi / 15 := by
    field_simp
    ring
  have hlow := mul_le_mul_of_nonneg_left h1 hc0
  have hupp := mul_le_mul_of_nonneg_left h2 hc0
  rw [e2] at hlow
  rw [e3] at hupp
  generalize 2 * Real.pi / (3 * (M : ℝ)) * s = a at hlow hupp ⊢
  have hπ0 := Real.pi_pos
  have hb : |a - Real.pi| ≤ 7 * Real.pi / 15 := abs_le.2 ⟨by linarith, by linarith⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (a - Real.pi))
    (by linarith) hb
  rw [Real.cos_abs, Real.cos_sub_pi] at hcos
  have hs : Real.cos (7 * Real.pi / 15) = Real.sin (Real.pi / 30) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  have hsin := Real.sin_gt_sub_cube (x := Real.pi / 30) (by positivity)
  have hy1 : (1046 / 10000 : ℝ) < Real.pi / 30 := by linarith [Real.pi_gt_d2]
  have hy2 : Real.pi / 30 ≤ 105 / 1000 := by linarith [Real.pi_lt_d2]
  have hy3 : (Real.pi / 30) ^ 3 ≤ (105 / 1000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hy2 3
  norm_num at hy3
  rw [hs] at hcos
  linarith

/-- ★★ **Up to the flow time `M/12` the packet's moving box misses the region** with the
threshold `−3/5`. -/
theorem arrivalBoxAt_disjoint_movedBoxD {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ M / 12) :
    Disjoint (arrivalBoxAt L (-3 / 5))
      (movedBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 1) (fun _ => 3 / 4) s) := by
  rw [Finset.disjoint_left]
  intro x hxX hx
  have hx1 : x ∈ arcBoxD (fun i => movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) i 1 s)
      (fun _ => 3 / 4) := hx
  have hx2 : x ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-3 / 5, 3 / 4] : Fin 2 → ℝ) := hxX
  have ha : (3 / 4 : ℝ) < (star (movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s)
      * (ZMod.toCircle (x 0) : ℂ)).re := mem_arcBoxD.1 hx1 0
  have hX : (-3 / 5 : ℝ) < (star (-1 : ℂ) * (ZMod.toCircle (x 0) : ℂ)).re :=
    mem_arcBoxD.1 hx2 0
  have hneg : ∀ w : ℂ, (star (-1 : ℂ) * w).re = -w.re := fun w => by simp
  have hone : ∀ w : ℂ, (star (1 : ℂ) * w).re = w.re := fun w => by simp
  have hone' : ∀ w : ℂ, (star w * 1).re = w.re := fun w => by simp
  have hQ : (49 / 50 : ℝ)
      ≤ (star (1 : ℂ) * movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s).re := by
    rw [hone, re_movedDirD_one]
    exact cos_dwellAngle_ge hL hM h0 h1
  have key := re_star_mul_gt_of_re_gt_of_re_ge (u := (ZMod.toCircle (x 0) : ℂ)) (u' := 1)
    (Circle.norm_coe _) norm_one
    (norm_movedDirD (L := L) 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 norm_one s)
    (p := 3 / 4) (q := 49 / 50) (r := 3 / 5) (by norm_num) (by norm_num)
    (by rw [re_star_mul_comm]; exact ha) hQ (by norm_num) (by norm_num)
  rw [hone'] at key
  rw [hneg] at hX
  linarith

/-- ★★ **From `4M/5` to `11M/5` the packet's moving box lies in the region** with the
threshold `−3/5`. -/
theorem movedBoxD_subset_arrivalBoxAt {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h1 : 4 * (M : ℝ) / 5 ≤ s) (h2 : s ≤ 11 * (M : ℝ) / 5) :
    movedBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 1) (fun _ => 3 / 4) s
      ⊆ arrivalBoxAt L (-3 / 5) := by
  intro x hx
  have hx1 : x ∈ arcBoxD (fun i => movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) i 1 s)
      (fun _ => 3 / 4) := hx
  have ha : (3 / 4 : ℝ) < (star (movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s)
      * (ZMod.toCircle (x 0) : ℂ)).re := mem_arcBoxD.1 hx1 0
  have hb : (3 / 4 : ℝ) < (star (movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 1 1 s)
      * (ZMod.toCircle (x 1) : ℂ)).re := mem_arcBoxD.1 hx1 1
  rw [movedDirD_instance_one] at hb
  have hneg : ∀ w : ℂ, (star (-1 : ℂ) * w).re = -w.re := fun w => by simp
  have hQ : (1 / 10 : ℝ)
      ≤ (star (-1 : ℂ) * movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s).re := by
    rw [hneg, re_movedDirD_one]
    have := cos_dwellAngle_le hL hM h1 h2
    linarith
  have key := re_star_mul_gt_of_re_gt_of_re_ge (u := (ZMod.toCircle (x 0) : ℂ)) (u' := -1)
    (Circle.norm_coe _) (by simp)
    (norm_movedDirD (L := L) 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 norm_one s)
    (p := 3 / 4) (q := 1 / 10) (r := -3 / 5) (by norm_num) (by norm_num)
    (by rw [re_star_mul_comm]; exact ha) hQ (by norm_num) (by norm_num)
  rw [re_star_mul_comm] at key
  show x ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-3 / 5, 3 / 4] : Fin 2 → ℝ)
  refine mem_arcBoxD.2 fun i => ?_
  fin_cases i
  · exact key
  · exact hb

/-- With `L = 8M` and `M ≥ 10⁹` the packet's tail is at most `41/2000` up to the flow time
`3M`. -/
theorem flatTailD_instance_le_long {M : ℕ} (hL : L = 8 * M) (hM : 1000000000 ≤ M) {τ : ℝ}
    (hτ : τ ≤ 3 * M) :
    flatTailD L 2 1 (fun _ : Fin 2 => 400) (fun _ => 400 * (2 * Real.pi / L))
        (fun _ => 3 / 4) τ ≤ 41 / 2000 := by
  have hMr : (1000000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hLr : (L : ℝ) = 8 * M := by rw [hL, Nat.cast_mul]; norm_num
  have hh : 2 * Real.pi / (L : ℝ) * M = Real.pi / 4 := by
    rw [hLr]
    field_simp
    ring
  rw [flatTailD_fin_two]
  generalize 2 * Real.pi / (L : ℝ) = x at hh ⊢
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hpos : 0 < x := by
    by_contra hx
    rw [not_lt] at hx
    nlinarith
  have h5 : x * 1000000000 ≤ x * M := mul_le_mul_of_nonneg_left hMr hpos.le
  have hs : x ≤ 8 / 10 ^ 10 := by linarith
  have h6 : τ * x ^ 2 ≤ 3 * Real.pi / 4 * x := by
    calc τ * x ^ 2 ≤ 3 * M * x ^ 2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg x)
      _ = 3 * (x * M) * x := by ring
      _ = 3 * Real.pi / 4 * x := by rw [hh]; ring
  have h7 : 3 * Real.pi / 4 * x ≤ 3 * 3.15 / 4 * (8 / 10 ^ 10) :=
    mul_le_mul (by linarith) hs hpos.le (by norm_num)
  have h8 : x ^ 2 ≤ x := by nlinarith
  linarith

end Region

/-! ### The two runs -/

section Runs

variable {L : ℕ} [NeZero L] {N : ℕ}

/-- The state of the instance, the flat packet with the transponder in its first level, is
not zero. -/
theorem meetingState_ne_zero {M : ℕ} (hL : L = 8 * M) (hM : 1000000000 ≤ M) :
    (WithLp.toLp 2 (fun y : ((Fin 2 → ZMod L) × Fin 2) × (Unit × Fin 2) =>
        packetD (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1
            (![1, 0] : Fin 2 → ℂ) (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
            (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0 y.1
          * (if y.2.2 = 0 then 1 else 0)) :
      EuclideanSpace ℂ (((Fin 2 → ZMod L) × Fin 2) × (Unit × Fin 2))) ≠ 0 := by
  refine toLp_ne_zero_of_sum_norm_sq_eq_one ?_
  have h := sum_norm_sq_prod
    (packetD (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1
      (![1, 0] : Fin 2 → ℂ) (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
      (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0)
    (fun q : Unit × Fin 2 => if q.2 = 0 then (1 : ℂ) else 0)
  rw [sum_norm_sq_flatPacketD cliffordTwo pauli_two_mulVec_spinUp star_spinUp_dotProduct
    one_pos _ (fun _ => by norm_num) (fun _ => by omega) 0, one_mul] at h
  have h2 : ∑ q : Unit × Fin 2, ‖(if q.2 = 0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
  exact h.trans h2

/-- ★★★ **The meeting writes a record, with numbers.** Two dimensions, `L = 8M` sites per
axis with `M ≥ 10⁹`, `J = 2`, `μ = 1`, the Clifford family `σ_x`, `σ_y` with `σ_z`, the
spinor `(1, 0)`, the flat packet of `400` momenta per axis starting at `(M, 0)`. One
transponder at rest with the energy `E` for both levels, at `contactSite`, in its first
level. The contact term has the relation `contactRelAt` with the threshold `−3/5` and the
strength `3/(5M)`. A pointer with the profile `(500/M) · trainF`, starting at `(1/6, 0)`, is
coupled to the projector on the transponder's second level. Then the pointer is not displayed
at any flow time up to `M/12`, and for some `c ≥ 1` the counts `0` at `M/12` and `c` at
`11M/5` are a record history of the run's start. -/
theorem transponder_meeting_record_instance {M : ℕ} (hL : L = 8 * M) (hM : 1000000000 ≤ M)
    (E : ℝ) (e : ((Fin 2 → ZMod L) × Fin 2) × (Unit × Fin 2) ≃ Fin (N + 1))
    (p₀ : CPN (N + 1)) :
    (∀ u, 0 ≤ u → u ≤ (M : ℝ) / 12 →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e (compositeH
              (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
              (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ))
            + ((3 / (5 * (M : ℝ)) : ℝ) : ℂ) • gateOp Prod.fst
                (fun _ : Unit × Fin 2 => contactSite L M) (contactRelAt L (-3 / 5))
                (levelSwap Unit)))
          (Matrix.reindex e e
            ((1 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
              ⊗ₖ levelProj Unit 1))
          (scaledTrainF_periodic (500 / (M : ℝ))) (contDiff_scaledTrainF (500 / (M : ℝ)))) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ (meetingState_ne_zero hL hM)),
          arrivalFibre)).2 ∉ displayArc)
      ∧ ∃ c : ℕ, 0 < c
        ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ (meetingState_ne_zero hL hM)),
            arrivalFibre) : KSigma (N + 1))
          ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
              (Matrix.reindex e e (compositeH
                  (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
                  (Matrix.blockDiagonal
                    fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ))
                + ((3 / (5 * (M : ℝ)) : ℝ) : ℂ) • gateOp Prod.fst
                    (fun _ : Unit × Fin 2 => contactSite L M) (contactRelAt L (-3 / 5))
                    (levelSwap Unit)))
              (Matrix.reindex e e
                ((1 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
                  ⊗ₖ levelProj Unit 1))
              (scaledTrainF_periodic (500 / (M : ℝ)))
              (contDiff_scaledTrainF (500 / (M : ℝ)))) p₀).semantics
            [TickReadout.startFact () ((M : ℝ) / 12) 0,
              TickReadout.startFact () (11 * (M : ℝ) / 5) c] := by
  have hM0 : 0 < M := by omega
  have hM4 : 4000000 ≤ M := by omega
  have hMr : (1000000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hrate : -2 * (scaledTrainF_periodic (500 / (M : ℝ))).deriv_periodic.lift
      arrivalFibre.2 = 1000 / M := by
    show -2 * (scaledTrainF_periodic (500 / (M : ℝ))).deriv_periodic.lift
      (0 : AddCircle (1 : ℝ)) = 1000 / M
    rw [scaledTrainF_deriv_lift_zero]
    ring
  have hg : |3 / (5 * (M : ℝ))| = 3 / (5 * M) := abs_of_pos (by positivity)
  have hT1 := flatTailD_instance_le_long (L := L) hL hM (τ := (M : ℝ) / 12) (by linarith)
  have hT2 := flatTailD_instance_le_long (L := L) hL hM (τ := 11 * (M : ℝ) / 5)
    (by linarith)
  have hs1 : Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 12)) ≤ 1432 / 10000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have hs2 : Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) (11 * (M : ℝ) / 5))
        ≤ 1432 / 10000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have hn1 := Real.sqrt_nonneg (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 12))
  have hn2 := Real.sqrt_nonneg (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) (11 * (M : ℝ) / 5))
  refine transponder_meeting_record e (fun _ : Unit × Fin 2 => contactSite L M)
    (contactRelAt L (-3 / 5)) (fun i j hij => absurd rfl hij) cliffordTwo
    pauli_two_mulVec_spinUp star_spinUp_dotProduct one_pos E (3 / (5 * (M : ℝ)))
    (scaledTrainF_periodic _) (contDiff_scaledTrainF _) p₀
    (![(M : ℤ), 0] : Fin 2 → ℤ) (Nw := fun _ => 400) (fun _ => by norm_num)
    (fun _ => by omega) (![Real.pi / 4, 0] : Fin 2 → ℝ)
    (w := fun _ => 400 * (2 * Real.pi / L)) (fun _ => by positivity)
    (abs_angleZD_arrival_le hL hM4) (γ := fun _ => 3 / 4) (fun _ => by norm_num)
    (fun q : Unit × Fin 2 => if q.2 = 0 then (1 : ℂ) else 0)
    (fun q hq => by simp [hq])
    (by simp [Fintype.sum_prod_type, Fin.sum_univ_two])
    ({contactSite L M} : Finset (Fin 2 → ZMod L))
    (fun q hq => absurd (Finset.mem_singleton_self _) hq)
    (meetingState_ne_zero hL hM) arrivalFibre_mem_readyArc (scaledTrainF_lift_zero _)
    (by rw [hrate]; positivity)
    (t₁ := (M : ℝ) / 12) (t₂ := 4 * (M : ℝ) / 5) (t₃ := 2 * (M : ℝ))
    (t := 11 * (M : ℝ) / 5) (ρ := 1 / 20) (by positivity) (by linarith) (by linarith)
    (by linarith) (by norm_num)
    (fun s hs hs1 a ha b hb hab => by
      rw [Finset.mem_singleton.1 hb] at hab
      exact Finset.disjoint_left.1 (arrivalBoxAt_disjoint_movedBoxD hL hM4 hs hs1)
        ((contactRelAt_contactSite_iff _ hL hM0 a).1 hab) ha)
    (fun s hs hst a ha b hb => by
      rw [Finset.mem_singleton.1 hb]
      exact (contactRelAt_contactSite_iff _ hL hM0 a).2
        (movedBoxD_subset_arrivalBoxAt hL hM4 hs hst ha))
    (fun s hs hst => ?_) ?_ ?_
  · -- the amplitude on the reading window
    rw [hg]
    generalize Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
        (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 12)) = a
      at hs1 hn1 ⊢
    generalize Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
        (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) (11 * (M : ℝ) / 5)) = b
      at hs2 hn2 ⊢
    have hc0 : 0 ≤ 3 / (5 * (M : ℝ)) := by positivity
    have e1 : 3 / (5 * (M : ℝ)) * (a * ((M : ℝ) / 12) + (4 * (M : ℝ) / 5 - M / 12))
        = a / 20 + 43 / 100 := by
      field_simp
      ring
    have e2 : 3 / (5 * (M : ℝ)) * (b * (11 * (M : ℝ) / 5 - 4 * M / 5)) = 21 / 25 * b := by
      field_simp
      ring
    have elo : 3 / (5 * (M : ℝ)) * (2 * (M : ℝ) - 4 * M / 5) = 18 / 25 := by
      field_simp
      ring
    have ehi : 3 / (5 * (M : ℝ)) * (11 * (M : ℝ) / 5 - 4 * M / 5) = 21 / 25 := by
      field_simp
      ring
    have hlo' := mul_le_mul_of_nonneg_left (sub_le_sub_right hs (4 * (M : ℝ) / 5)) hc0
    have hhi' := mul_le_mul_of_nonneg_left (sub_le_sub_right hst (4 * (M : ℝ) / 5)) hc0
    rw [elo] at hlo'
    rw [ehi] at hhi'
    rw [e1, e2]
    generalize 3 / (5 * (M : ℝ)) * (s - 4 * (M : ℝ) / 5) = θ at hlo' hhi' ⊢
    have hπ := Real.pi_gt_d2
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two (x := 18 / 25) (y := θ)
      (by linarith) (by linarith) hlo'
    have hsin := Real.sin_gt_sub_cube (x := (18 / 25 : ℝ)) (by norm_num)
    have habs := le_abs_self (Real.sin θ)
    norm_num at hsin
    linarith
  · -- the leakage before the meeting
    rw [hrate, hg]
    generalize Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
        (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 12)) = a
      at hs1 hn1 ⊢
    have e : 1000 / (M : ℝ) * ((3 / (5 * (M : ℝ)) * (a * ((M : ℝ) / 12))) ^ 2 * ((M : ℝ) / 12))
        = 5 / 24 * a ^ 2 := by
      field_simp
      ring
    have ha2 : a ^ 2 ≤ (1432 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hn1 hs1 2
    rw [e]
    norm_num at ha2
    linarith
  · -- the reading
    rw [hrate]
    have e : 1000 / (M : ℝ) * ((1 / 20 : ℝ) ^ 2 * (11 * (M : ℝ) / 5 - 2 * M)) = 1 / 2 := by
      field_simp
      ring
    rw [e]
    norm_num

/-- ★★★ **The same preparation without the contact term: the pointer counts `0`.** The
packet, the transponder, the pointer's profile and its start are those of
`transponder_meeting_record_instance`; the carriers' energy has no contact term. Then the
pointer is not displayed at any flow time up to `11M/5`, and "the pointer has counted `0` at
`11M/5`" is a recorded fact of the run's start. -/
theorem transponder_reading_control_instance {M : ℕ} (hL : L = 8 * M)
    (hM : 1000000000 ≤ M) (E : ℝ)
    (e : ((Fin 2 → ZMod L) × Fin 2) × (Unit × Fin 2) ≃ Fin (N + 1)) (p₀ : CPN (N + 1)) :
    (∀ u, 0 ≤ u → u ≤ 11 * (M : ℝ) / 5 →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e (compositeH
            (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
            (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ))))
          (Matrix.reindex e e
            ((1 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
              ⊗ₖ levelProj Unit 1))
          (scaledTrainF_periodic (500 / (M : ℝ))) (contDiff_scaledTrainF (500 / (M : ℝ)))) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ (meetingState_ne_zero hL hM)),
          arrivalFibre)).2 ∉ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ (meetingState_ne_zero hL hM)),
          arrivalFibre) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (compositeH
              (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
              (Matrix.blockDiagonal
                fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ))))
            (Matrix.reindex e e
              ((1 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
                ⊗ₖ levelProj Unit 1))
            (scaledTrainF_periodic (500 / (M : ℝ)))
            (contDiff_scaledTrainF (500 / (M : ℝ)))) p₀).semantics
          [TickReadout.startFact () (11 * (M : ℝ) / 5) 0] := by
  have hMr : (1000000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hT : ∀ _ : Fin 2, (((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hΨ : ((1 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
        ⊗ₖ levelProj Unit 1)
      *ᵥ (fun y : ((Fin 2 → ZMod L) × Fin 2) × (Unit × Fin 2) =>
        packetD (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1
            (![1, 0] : Fin 2 → ℂ) (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
            (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0 y.1
          * (if y.2.2 = 0 then 1 else 0)) = 0 :=
    one_kronecker_levelProj_one_mulVec_prod
      (packetD (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1
        (![1, 0] : Fin 2 → ℂ) (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
        (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0)
      (φ := fun q : Unit × Fin 2 => if q.2 = 0 then (1 : ℂ) else 0)
      (fun q hq => by simp [hq])
  exact transponder_reading_control e
    (M₀ := latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
    (latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1)
    (T := fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) hT
    (scaledTrainF_periodic (500 / (M : ℝ))) (contDiff_scaledTrainF (500 / (M : ℝ))) p₀ hΨ
    (meetingState_ne_zero hL hM) arrivalFibre_mem_readyArc (by linarith)

end Runs

end CSD.RecordLayer

end
