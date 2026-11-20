/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusArrivalExhibit

/-!
# Arrival and display on the torus: a detector given in advance

**Category:** 7-SigmaLayer. BACKLOG #297, seventh brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

In `RecordLayer/TorusArrivalInstance.lean` the detector sits on the sites the packet's moving
box sweeps, so the detector is defined from the packet's own motion. Here the detector is a
fixed box of arcs, written down with no reference to the packet.

## The geometry

* `lt_mul_add_mul_of_lt_of_le`, `re_star_mul_gt_of_re_gt_of_re_ge` — two unit points that see
  a third within `p` and `q` see each other within `r`, when
  `(1 − p²)(1 − q²) ≤ (p q − r)²`;
* `re_movedDirD_one` — the real part of the moved direction is the cosine of the drift;
* `arrivalBox` — **the detector**: the sites whose first coordinate is on the arc
  `Re z < 1/4` and whose second is on the arc `Re z > 3/4`;
* ★★ `arrivalBox_disjoint_movedBoxD` — up to the flow time `M/4` the packet's moving box
  misses the detector;
* ★★ `movedBoxD_subset_arrivalBox` — from `M` to `2M` the moving box lies in the detector.

## The run

* ★★★ `torusDetector_arrival_box` — **two dimensions, `L = 8M` sites per axis with
  `M ≥ 4·10⁶`, `J = 2`, `μ = 1`, `σ_x`, `σ_y` with `σ_z`, the spinor `(1, 0)`, the flat
  packet of `400` momenta per axis starting at `(M, 0)`, the detector `arrivalBox`, the
  profile `(3/(16M)) · trainF`, the pointer's start `(1/6, 0)`: the pointer is not displayed
  up to the flow time `M/4`, it is displayed at `2M`, and the counts `0` at `M/4` and `1` at
  `2M` are a record history of the start.**

## Honest scope

⚠️ **One fibre.** The pointer's conserved angle is `θ₂ = 0`, where the profile vanishes. This
is one point of the circle, a null set.

⚠️ **The detector is wide.** Its first side is the arc `Re z < 1/4`; its number of sites is
not computed. The packet's box has sides `3/4`, and the detector must hold it for the dwell
`[M, 2M]`.

⚠️ **The rate `3/(8M)` is fitted to the three inequalities**: with the tail bounded by
`1/10` they leave it the window `[10/27, 80/213] · 1/M`.

⚠️ **The labelling `e` is a parameter.** None is chosen.

⚠️ **Between `M/4` and `M` nothing is said about the display.** No time of arrival.

⚠️ **Not composed with the bound against the graph distance** (`torusDetector_not_displayed`).

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297; `specs/unified-record-spacetime-plan.md` (UD-242,
UD-244, UD-245); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/TorusArrival.lean` (`torusDetector_arrival_flatPacket`);
`RecordLayer/TorusArrivalInstance.lean` (`groupVelD_instance`, `flatTailD_instance_le`,
`re_star_mul_gt_of_re_gt`); `RecordLayer/TorusArrivalExhibit.lean` (`arrivalFibre`,
`arrivalPacket_ne_zero`); `CV/DiracPacketArcD.lean` (`arcBoxD`, `movedBoxD`);
`CV/DiracPacketBoxD.lean` (`movedDirD`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The geometry -/

/-- The real inequality behind `re_star_mul_gt_of_re_gt_of_re_ge`. -/
theorem lt_mul_add_mul_of_lt_of_le {P Q P' Q' p q r : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (h1 : p < P) (h2 : q ≤ Q) (hP : P ^ 2 + P' ^ 2 = 1) (hQ : Q ^ 2 + Q' ^ 2 = 1)
    (hr : r ≤ p * q) (hpqr : (1 - p ^ 2) * (1 - q ^ 2) ≤ (p * q - r) ^ 2) :
    r < P * Q + P' * Q' := by
  have hPQ : p * q < P * Q :=
    (mul_lt_mul_of_pos_right h1 hq).trans_le (mul_le_mul_of_nonneg_left h2 (hp.trans h1.le))
  have hp0 : 0 ≤ 1 - P ^ 2 := by nlinarith [sq_nonneg P']
  have hq0 : 0 ≤ 1 - Q ^ 2 := by nlinarith [sq_nonneg Q']
  have hp2 : 1 - P ^ 2 ≤ 1 - p ^ 2 := by
    have := pow_le_pow_left₀ hp h1.le 2
    linarith
  have hq2 : 1 - Q ^ 2 ≤ 1 - q ^ 2 := by
    have := pow_le_pow_left₀ hq.le h2 2
    linarith
  have hle : (1 - P ^ 2) * (1 - Q ^ 2) ≤ (1 - p ^ 2) * (1 - q ^ 2) :=
    mul_le_mul hp2 hq2 hq0 (hp0.trans hp2)
  have hsq : (P' * Q') ^ 2 = (1 - P ^ 2) * (1 - Q ^ 2) := by
    rw [mul_pow, show P' ^ 2 = 1 - P ^ 2 by linarith, show Q' ^ 2 = 1 - Q ^ 2 by linarith]
  by_contra hn
  rw [not_lt] at hn
  have h3 : p * q - r < -(P' * Q') := by linarith
  have h4 : (p * q - r) ^ 2 < (-(P' * Q')) ^ 2 :=
    pow_lt_pow_left₀ h3 (by linarith) two_ne_zero
  rw [neg_sq] at h4
  linarith

/-- Two unit points `u`, `u'` that see a unit point `z` within `p` and within `q` see each
other within `r`, when `(1 − p²)(1 − q²) ≤ (p q − r)²`. -/
theorem re_star_mul_gt_of_re_gt_of_re_ge {u u' z : ℂ} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hz : ‖z‖ = 1) {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (h1 : p < (star u * z).re)
    (h2 : q ≤ (star u' * z).re) (hr : r ≤ p * q)
    (hpqr : (1 - p ^ 2) * (1 - q ^ 2) ≤ (p * q - r) ^ 2) : r < (star u * u').re := by
  have nsq : ∀ w : ℂ, ‖w‖ = 1 → w.re * w.re + w.im * w.im = 1 := fun w hw => by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hw, one_pow]
  have ha := nsq u hu
  have hc := nsq u' hu'
  have hx := nsq z hz
  have e : ∀ v w : ℂ, (star v * w).re = v.re * w.re + v.im * w.im := fun v w => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [e] at h1 h2 ⊢
  have hP : (u.re * z.re + u.im * z.im) ^ 2 + (u.re * z.im - u.im * z.re) ^ 2 = 1 := by
    have : (u.re * z.re + u.im * z.im) ^ 2 + (u.re * z.im - u.im * z.re) ^ 2
        = (u.re * u.re + u.im * u.im) * (z.re * z.re + z.im * z.im) := by ring
    rw [this, ha, hx, mul_one]
  have hQ : (u'.re * z.re + u'.im * z.im) ^ 2 + (u'.re * z.im - u'.im * z.re) ^ 2 = 1 := by
    have : (u'.re * z.re + u'.im * z.im) ^ 2 + (u'.re * z.im - u'.im * z.re) ^ 2
        = (u'.re * u'.re + u'.im * u'.im) * (z.re * z.re + z.im * z.im) := by ring
    rw [this, hc, hx, mul_one]
  have key := lt_mul_add_mul_of_lt_of_le hp hq h1 h2 hP hQ hr hpqr
  have hid : (u.re * z.re + u.im * z.im) * (u'.re * z.re + u'.im * z.im)
        + (u.re * z.im - u.im * z.re) * (u'.re * z.im - u'.im * z.re)
      = u.re * u'.re + u.im * u'.im := by
    have : (u.re * z.re + u.im * z.im) * (u'.re * z.re + u'.im * z.im)
          + (u.re * z.im - u.im * z.re) * (u'.re * z.im - u'.im * z.re)
        = (u.re * u'.re + u.im * u'.im) * (z.re * z.re + z.im * z.im) := by ring
    rw [this, hx, mul_one]
  linarith

/-- `Re(ā b) = Re(b̄ a)`. -/
theorem re_star_mul_comm (a b : ℂ) : (star a * b).re = (star b * a).re := by
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The real part of the moved direction is the cosine of the drift. -/
theorem re_movedDirD_one {κ : Type*} [Fintype κ] (L : ℕ) (J μ : ℝ) (k₀ : κ → ℝ) (i : κ)
    (s : ℝ) :
    (movedDirD L J μ k₀ i 1 s).re = Real.cos (2 * Real.pi / L * groupVelD J μ k₀ i * s) := by
  rw [movedDirD, mul_one]
  have hh : Complex.I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * s)
      = ((2 * Real.pi / L * groupVelD J μ k₀ i * s : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hh, Complex.exp_ofReal_mul_I_re]

/-! ### The numbers of the instance -/

/-- For `J = 2`, `μ = 1` and the central momentum `(π/4, 0)` the group velocity along the
second axis is zero. -/
theorem groupVelD_instance_one :
    groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 1 = 0 := by
  show 2 * 2 * (2 * 2 * Real.sin 0) * Real.cos 0
      / latticeED 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) = 0
  rw [Real.sin_zero]
  simp

/-- Along the second axis the direction does not move. -/
theorem movedDirD_instance_one (L : ℕ) (s : ℝ) :
    movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 1 1 s = 1 := by
  rw [movedDirD, groupVelD_instance_one]
  simp

section Box

variable {L : ℕ} [NeZero L] {N : ℕ}

omit [NeZero L] in
/-- With `L = 8M` the drift angle along the first axis at the flow time `s` is
`2π s / (3M)`. -/
theorem arrivalAngle_eq {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) (s : ℝ) :
    2 * Real.pi / L * groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 * s
      = 2 * Real.pi / (3 * M) * s := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hLr : (L : ℝ) = 8 * M := by rw [hL, Nat.cast_mul]; norm_num
  rw [groupVelD_instance, hLr]
  field_simp

omit [NeZero L] in
/-- Up to the flow time `M/4` the drift angle is at most `π/6`: its cosine is at least
`43/50`. -/
theorem cos_arrivalAngle_ge {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ M / 4) :
    (43 / 50 : ℝ)
      ≤ Real.cos (2 * Real.pi / L * groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 * s) := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [arrivalAngle_eq hL hM]
  have hc0 : 0 ≤ 2 * Real.pi / (3 * (M : ℝ)) := by positivity
  have e1 : 2 * Real.pi / (3 * (M : ℝ)) * (M / 4) = Real.pi / 6 := by
    field_simp
    ring
  have hup := mul_le_mul_of_nonneg_left h1 hc0
  rw [e1] at hup
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hc0 h0)
    (by linarith [Real.pi_pos]) hup
  rw [Real.cos_pi_div_six] at hcos
  have h3 : (1.72 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1.72 : ℝ) = Real.sqrt (1.72 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

omit [NeZero L] in
/-- From `M` to `2M` the drift angle is between `2π/3` and `4π/3`: its cosine is at most
`−1/2`. -/
theorem cos_arrivalAngle_le {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h1 : (M : ℝ) ≤ s) (h2 : s ≤ 2 * M) :
    Real.cos (2 * Real.pi / L * groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 * s)
      ≤ -1 / 2 := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [arrivalAngle_eq hL hM]
  have hc0 : 0 ≤ 2 * Real.pi / (3 * (M : ℝ)) := by positivity
  have e2 : 2 * Real.pi / (3 * (M : ℝ)) * M = 2 * Real.pi / 3 := by
    field_simp
  have e3 : 2 * Real.pi / (3 * (M : ℝ)) * (2 * M) = 4 * Real.pi / 3 := by
    field_simp
    ring
  have hlow := mul_le_mul_of_nonneg_left h1 hc0
  have hupp := mul_le_mul_of_nonneg_left h2 hc0
  rw [e2] at hlow
  rw [e3] at hupp
  generalize 2 * Real.pi / (3 * (M : ℝ)) * s = a at hlow hupp ⊢
  have hb : |a - Real.pi| ≤ Real.pi / 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (a - Real.pi))
    (by linarith [Real.pi_pos]) hb
  rw [Real.cos_abs, Real.cos_sub_pi, Real.cos_pi_div_three] at hcos
  linarith

/-- **The detector**: the sites whose first coordinate is on the arc `Re z < 1/4` and whose
second coordinate is on the arc `Re z > 3/4`. -/
def arrivalBox (L : ℕ) [NeZero L] : Finset (Fin 2 → ZMod L) :=
  arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ)

/-- ★★ **Up to the flow time `M/4` the packet's moving box misses the detector.** -/
theorem arrivalBox_disjoint_movedBoxD {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ M / 4) :
    Disjoint (arrivalBox L)
      (movedBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 1) (fun _ => 3 / 4) s) := by
  rw [Finset.disjoint_left]
  intro x hxX hx
  have hx1 : x ∈ arcBoxD (fun i => movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) i 1 s)
      (fun _ => 3 / 4) := hx
  have hx2 : x ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ) := hxX
  have ha : (3 / 4 : ℝ) < (star (movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s)
      * (ZMod.toCircle (x 0) : ℂ)).re := mem_arcBoxD.1 hx1 0
  have hX : (-1 / 4 : ℝ) < (star (-1 : ℂ) * (ZMod.toCircle (x 0) : ℂ)).re :=
    mem_arcBoxD.1 hx2 0
  have hneg : ∀ w : ℂ, (star (-1 : ℂ) * w).re = -w.re := fun w => by simp
  have hone : ∀ w : ℂ, (star (1 : ℂ) * w).re = w.re := fun w => by simp
  have hone' : ∀ w : ℂ, (star w * 1).re = w.re := fun w => by simp
  have hQ : (43 / 50 : ℝ)
      ≤ (star (1 : ℂ) * movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s).re := by
    rw [hone, re_movedDirD_one]
    exact cos_arrivalAngle_ge hL hM h0 h1
  have key := re_star_mul_gt_of_re_gt_of_re_ge (u := (ZMod.toCircle (x 0) : ℂ)) (u' := 1)
    (Circle.norm_coe _) norm_one
    (norm_movedDirD (L := L) 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 norm_one s)
    (p := 3 / 4) (q := 43 / 50) (r := 1 / 4) (by norm_num) (by norm_num)
    (by rw [re_star_mul_comm]; exact ha) hQ (by norm_num) (by norm_num)
  rw [hone'] at key
  rw [hneg] at hX
  linarith

/-- ★★ **From `M` to `2M` the packet's moving box lies in the detector.** -/
theorem movedBoxD_subset_arrivalBox {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h1 : (M : ℝ) ≤ s) (h2 : s ≤ 2 * M) :
    movedBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 1) (fun _ => 3 / 4) s
      ⊆ arrivalBox L := by
  intro x hx
  have hx1 : x ∈ arcBoxD (fun i => movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) i 1 s)
      (fun _ => 3 / 4) := hx
  have ha : (3 / 4 : ℝ) < (star (movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s)
      * (ZMod.toCircle (x 0) : ℂ)).re := mem_arcBoxD.1 hx1 0
  have hb : (3 / 4 : ℝ) < (star (movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 1 1 s)
      * (ZMod.toCircle (x 1) : ℂ)).re := mem_arcBoxD.1 hx1 1
  rw [movedDirD_instance_one] at hb
  have hneg : ∀ w : ℂ, (star (-1 : ℂ) * w).re = -w.re := fun w => by simp
  have hQ : (1 / 2 : ℝ)
      ≤ (star (-1 : ℂ) * movedDirD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 1 s).re := by
    rw [hneg, re_movedDirD_one]
    have := cos_arrivalAngle_le hL hM h1 h2
    linarith
  have key := re_star_mul_gt_of_re_gt_of_re_ge (u := (ZMod.toCircle (x 0) : ℂ)) (u' := -1)
    (Circle.norm_coe _) (by simp)
    (norm_movedDirD (L := L) 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 norm_one s)
    (p := 3 / 4) (q := 1 / 2) (r := -1 / 4) (by norm_num) (by norm_num)
    (by rw [re_star_mul_comm]; exact ha) hQ (by norm_num) (by norm_num)
  rw [re_star_mul_comm] at key
  show x ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ)
  refine mem_arcBoxD.2 fun i => ?_
  fin_cases i
  · exact key
  · exact hb

/-! ### The run -/

omit [NeZero L] in
/-- The momenta of the instance's window are within `400 · 2π/L` of `(π/4, 0)`. -/
theorem abs_angleZD_arrival_le {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) :
    ∀ m ∈ boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) (fun _ => 400), ∀ j,
      |angleZD L m j - (![Real.pi / 4, 0] : Fin 2 → ℝ) j| ≤ 400 * (2 * Real.pi / L) := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hLr : (L : ℝ) = 8 * M := by rw [hL, Nat.cast_mul]; norm_num
  intro m hm j
  have hmj := Fintype.mem_piFinset.1 hm j
  simp only [Finset.mem_Ico] at hmj
  have hk : (![Real.pi / 4, 0] : Fin 2 → ℝ) j
      = 2 * Real.pi * (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) / L := by
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Int.cast_natCast]
      rw [hLr]
      field_simp
      ring
    · simp
  have hd0 : (0 : ℝ) ≤ (m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) :=
    sub_nonneg.2 (by exact_mod_cast hmj.1)
  have hd1 : (m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) ≤ 400 := by
    have h' : (m j : ℝ) < (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) + 400 := by
      exact_mod_cast hmj.2
    linarith
  have hc0 : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  show |2 * Real.pi * (m j : ℝ) / L - (![Real.pi / 4, 0] : Fin 2 → ℝ) j| ≤ _
  rw [hk, ← sub_div, ← mul_sub, abs_of_nonneg (by positivity)]
  calc 2 * Real.pi * ((m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ)) / L
      = 2 * Real.pi / L * ((m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ)) := by
        ring
    _ ≤ 2 * Real.pi / L * 400 := mul_le_mul_of_nonneg_left hd1 hc0
    _ = 400 * (2 * Real.pi / L) := by ring

/-- For the profile `g · trainF` with `g = 3/(16M)`, on the fibre `θ₂ = 0`, the rate is
`−2 f'(0) = 3/(8M)`. -/
theorem arrivalBoxRate_scaledTrainF (M : ℕ) :
    -2 * (scaledTrainF_periodic (3 / (16 * (M : ℝ)))).deriv_periodic.lift
        (0 : AddCircle (1 : ℝ)) = 3 / (8 * M) := by
  rw [scaledTrainF_deriv_lift_zero]
  ring

/-- ★★★ **Arrival and display on the torus for a detector given in advance.** Two
dimensions, `L = 8M` sites per axis with `M ≥ 4·10⁶`, `J = 2`, `μ = 1`, the Clifford family
`σ_x`, `σ_y` with `σ_z`, the spinor `(1, 0)`. The flat packet has `400` momenta per axis
starting at `(M, 0)`. The detector is `arrivalBox`: the sites whose first coordinate is on
the arc `Re z < 1/4` and whose second is on the arc `Re z > 3/4`. The pointer's profile is
`(3/(16M)) · trainF` and it starts at `(1/6, 0)`. Then the pointer is not displayed at any
flow time up to `M/4`, it is displayed at `2M`, and the counts `0` at `M/4` and `1` at `2M`
are a record history of the run's start. -/
theorem torusDetector_arrival_box {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (e : (Fin 2 → ZMod L) × Fin 2 ≃ Fin (N + 1)) (p₀ : CPN (N + 1)) :
    ((∀ u, 0 ≤ u → u ≤ (M : ℝ) / 4 →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e
            (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (arrivalBox L : Set (Fin 2 → ZMod L))))
          (scaledTrainF_periodic (3 / (16 * (M : ℝ))))
          (contDiff_scaledTrainF (3 / (16 * (M : ℝ))))) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)),
          arrivalFibre)).2 ∉ displayArc)
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e
            (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (arrivalBox L : Set (Fin 2 → ZMod L))))
          (scaledTrainF_periodic (3 / (16 * (M : ℝ))))
          (contDiff_scaledTrainF (3 / (16 * (M : ℝ)))))
        (2 * (M : ℝ))
        (idxArenaEquiv e (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)),
          arrivalFibre)).2 ∈ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)),
          arrivalFibre) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e
              (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
            (Matrix.reindex e e (siteSetProj Prod.fst
              (arrivalBox L : Set (Fin 2 → ZMod L))))
            (scaledTrainF_periodic (3 / (16 * (M : ℝ))))
            (contDiff_scaledTrainF (3 / (16 * (M : ℝ)))))
            p₀).semantics
          [TickReadout.startFact () ((M : ℝ) / 4) 0,
            TickReadout.startFact () (2 * (M : ℝ)) 1] := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hT := flatTailD_instance_le (L := L) hL hM (τ := 2 * (M : ℝ)) (by linarith)
  have hε := flatTailD_instance_le (L := L) hL hM (τ := (M : ℝ) / 4) (by linarith)
  have hrate : -2 * (scaledTrainF_periodic (3 / (16 * (M : ℝ)))).deriv_periodic.lift
      arrivalFibre.2 = 3 / (8 * M) := arrivalBoxRate_scaledTrainF M
  have r1 : ∀ ε : ℝ, 3 / (8 * (M : ℝ)) * (ε * (M / 4)) = 3 / 32 * ε := fun ε => by
    field_simp
    ring
  have r2 : ∀ q : ℝ, 3 / (8 * (M : ℝ)) * (q * (2 * M - M)) = 3 / 8 * q := fun q => by
    field_simp
    ring
  have r3 : ∀ ε : ℝ, 3 / (8 * (M : ℝ)) * (ε * (M / 4) + (2 * M - M / 4))
      = 3 / 32 * ε + 21 / 32 := fun ε => by
    field_simp
    ring
  refine torusDetector_arrival_flatPacket e cliffordTwo pauli_two_mulVec_spinUp
    star_spinUp_dotProduct one_pos (scaledTrainF_periodic _) (contDiff_scaledTrainF _) p₀
    (![(M : ℤ), 0] : Fin 2 → ℤ) (fun _ => by norm_num) (fun _ => by omega)
    (![Real.pi / 4, 0] : Fin 2 → ℝ) (w := fun _ => 400 * (2 * Real.pi / L))
    (fun _ => by positivity) (abs_angleZD_arrival_le hL hM) (γ := fun _ => 3 / 4)
    (fun _ => by norm_num) (arrivalPacket_ne_zero hL hM) (arrivalBox L)
    arrivalFibre_mem_readyArc (scaledTrainF_lift_zero _) (by rw [hrate]; positivity)
    (by positivity) (by linarith) (by linarith)
    (fun s hs hs1 => arrivalBox_disjoint_movedBoxD hL hM hs hs1)
    (fun s hs hs1 => movedBoxD_subset_arrivalBox hL hM hs hs1) ?_ ?_ ?_
  · rw [hrate, r1]
    linarith
  · rw [hrate, r2]
    linarith
  · rw [hrate, r3]
    linarith

end Box

end CSD.RecordLayer

end
