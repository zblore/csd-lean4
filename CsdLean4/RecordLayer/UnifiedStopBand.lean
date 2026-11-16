/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReturnReading

/-!
# Where the emission pointer stops: the band as a condition on the clock's phase

**Category:** 7-SigmaLayer (the record layer). BACKLOG #400 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, tenth brick: the band condition of #398 and #399. No new assumption beyond UA-18.

The return reading of #399 holds for the runs in which the emission pointer stopped in one of
the two bands of #398. This module bounds where that pointer stops, when its gate closes
quickly, and so replaces the band by a condition on the clock's phase at the flow time the
gate begins to close.

* `narrow_clock_packet_swing_fine`, `flat_clock_swing_fine` — over the `j`-th part of its
  horizon the narrow clock packet of #391 (the flat packet of #392) swings within `1/(24 j)`
  of `(1/4)(1 − cos R t)`, for `j ≤ n`;
* ★★ `coincShift_stop_le` — the displacement at `t_b` of a pointer coupled to the gate `r`
  is within `δ₀ + 2|z| ε t_a + 2|z| (t_b − t_a)` of `(1/4)(1 − cos R t_a)`, when the two
  carriers have weight at most `ε` outside the relation up to `t_a`;
* ★★★ `coincFlow_return_reading_of_phase` — the return reading of #399 with the band
  replaced by `4 σ < |cos R t_a|` and `σ < 1/12`, where
  `σ = 2 δ₀ + 2|z| (ε t_a + (t_b − t_a) + ε (t₃ − t_b))`;
* ★★★ `flat_clock_return_reading_of_phase` — on the ring, for any messenger packet and the
  flat clock packet with `n ≥ 4`, over a quarter of the clock's horizon: for some strength
  `0 < g ≤ R/5`, if `2 (R/5) (ε t_a + (t_b − t_a) + ε (t₃ − t_b)) ≤ 1/48` and
  `1/6 < |cos R t_a|`, the complementary pointer has at every flow time of `[t₄, t₅]` a count
  `N'` with `|2π N' − R (t₃ − t_b)| ≤ 2π (6 g ((t_b − t_a) + (t₄ − t₃)) + 7)`.

## Exact scope

* **Only a gate that closes quickly.** The bound on where the pointer stops carries the term
  `2|z| (t_b − t_a)`: while the gate closes, only the pointer's speed is used. The ring
  theorem asks `2 (R/5) (t_b − t_a) ≤ 1/48`, a closing that lasts a small part of one tick.
  In the family of #397 the closing lasts many ticks, so that family does not meet this
  condition. For a gate that closes slowly nothing is shown about where the pointer stops.
* **The band is replaced, not removed.** The condition `1/6 < |cos R t_a|` is on the clock's
  phase `R t_a` at the flow time `t_a`, the last at which the two carriers are certified
  together. Runs with `|cos R t_a| ≤ 1/6` are not covered, and #398 shows that near
  `cos R t_a = 0` the pointer's count need not follow the clock.
* **`R t_a` is a number of the arena, not a reading.** `R` is the clock's rate `ringRate` and
  `t_a` a flow time; the condition is an inequality between real numbers like the others.
  No pointer reads this phase.
* **Inequalities between real numbers, no values.** As #399: no values are shown to meet the
  hypotheses together, and no run is exhibited in which the messenger comes back.
* **A quarter of the horizon.** The finer swing `1/96` is proved up to `2π n/(4R)` for the
  packet of parameter `n ≥ 4`; the time away must fit in that.
* **How the messenger comes back is not said, and the radar time and distance are not
  formed**, as #399. Only the fibres where both profiles vanish and only product starts, as
  #393; for some strength, as #396; a ring and two carriers.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-18, UO-16, UD-155, UD-156, UD-157, UD-158, UD-159, UD-160);
`RecordLayer/UnifiedReturnReading.lean` (#399: `coincFlow_return_reading`, `ringReturnRun`,
`packetAngleGap`, `levelSwap_apply_eq_zero_of_site_ne`);
`RecordLayer/UnifiedWindowSwing.lean` (#398: `offset_swing_count`, the bands);
`RecordLayer/UnifiedEmissionReading.lean` (#396: `clock_packet_shift_le`,
`narrow_clock_packet_swing`, `clockPointerShift_trainF_eq`, `outside_arcs_flat_clock_le`);
`RecordLayer/UnifiedGateRegions.lean` (#395: `ringGate_not_le`, `ringGate_le`);
`RecordLayer/UnifiedGatedReading.lean` (#394: `abs_coincShift_sub_le`,
`abs_arenaObs_gateOp_prodRay_le`, `arenaObs_coincProj_add_not`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincShift_gateOp_add_not`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### A finer swing over part of the horizon -/

section Swing

variable {M : ℕ}

/-- **A narrow clock packet swings more closely over part of its horizon.** For the clock of
`narrow_clock_packet_swing` (#396) and `0 < j ≤ n`: for some strength `0 < g ≤ R/5`, up to
`2π n/(j R)` the clock pointer's displacement is within `1/(24 j)` of `(1/4)(1 − cos R t)`. -/
theorem narrow_clock_packet_swing_fine {n K j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hK : 0 < K)
    {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hp1 : p₀ ≤ 9 / 10)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |(m : ℝ) / K - p₀| ≤ 1 / (600 * n) ∨ |(m : ℝ) / K + p₀| ≤ 1 / (600 * n))
    (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop K M) 1 (1 + Δ) W β
          (-(Real.pi / (2 * ringRate K M p₀ Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate K M p₀ Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / (j * ringRate K M p₀ Δ) →
        |clockPointerShift (ringHop K M) 1 (1 + Δ) g trainF_periodic (0 : AddCircle (1 : ℝ))
              (deviceRay _ hΨ) t - 1 / 4 * (1 - Real.cos (ringRate K M p₀ Δ * t))|
          ≤ 1 / (24 * j) := by
  have hn : 0 < n := hj.trans_le hjn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hσsq : ringSigma K M p₀ ^ 2 ≤ 3 :=
    ringSigma_sq_le hK M (by rw [abs_of_nonneg hp0]; linarith)
  have hRlo : Δ / 2 ≤ ringRate K M p₀ Δ := half_le_levelClockRate hΔ0.le hσsq
  have hRhi : ringRate K M p₀ Δ ≤ Δ := levelClockRate_le_gap hΔ0.le _
  have hR0 : 0 < ringRate K M p₀ Δ := by linarith
  set R := ringRate K M p₀ Δ with hRd
  have hWD' : ∀ m ∈ W, |2 * Real.pi * m / ringLen K - p₀| ≤ 1 / (600 * n)
      ∨ |2 * Real.pi * m / ringLen K + p₀| ≤ 1 / (600 * n) := by
    intro m hm
    have e : 2 * Real.pi * (m : ℝ) / ringLen K = (m : ℝ) / K := by
      rw [ringLen]
      field_simp
    rw [e]
    exact hWD m hm
  have hD1 : (1 : ℝ) / (600 * n) ≤ 1 / 600 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hD0 : (0 : ℝ) < 1 / (600 * n) := by positivity
  have hρm : ∀ m ∈ W, Δ / 2 ≤ modeRate M (ringHop K M) 1 (1 + Δ) m := by
    intro m hm
    have hm1 : |(m : ℝ) / K| ≤ 1 := by
      rcases hWD m hm with h | h
      · have h := abs_le.1 h
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
      · have h := abs_le.1 h
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
    rw [modeRate, two_ringHop_mul_sin_angleZ hK]
    exact half_le_levelClockRate hΔ0.le (ringSigma_sq_le hK M hm1)
  set u := 1 / (600 * (n : ℝ)) * (2 * p₀ + 1 / (600 * n)) / 4 with hud
  have hεeq : deviceDrift 1 1 (1 + Δ) (1 / (600 * n)) p₀ = Δ * u := by
    rw [hud, deviceDrift, abs_of_nonneg hp0]
    ring
  have hu0 : 0 ≤ u := by
    rw [hud]
    positivity
  have hun : u * n ≤ 1 / 800 := by
    have hb : 2 * p₀ + 1 / (600 * n) ≤ 3 := by linarith
    have hDn : 1 / (600 * (n : ℝ)) * n = 1 / 600 := by field_simp
    calc u * n = 1 / (600 * n) * n * (2 * p₀ + 1 / (600 * n)) / 4 := by
          rw [hud]; ring
      _ = 1 / 600 * (2 * p₀ + 1 / (600 * n)) / 4 := by rw [hDn]
      _ ≤ 1 / 600 * 3 / 4 := by linarith
      _ = 1 / 800 := by norm_num
  have huj : u * j ≤ 1 / 800 := (mul_le_mul_of_nonneg_left hjn' hu0).trans hun
  have hule : u ≤ 1 / 800 := by nlinarith
  have hinv : Real.pi / (2 * R) * Δ ≤ Real.pi := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hprod : Real.pi / (2 * R) * (Δ * u) ≤ 1 / 100 := by
    calc Real.pi / (2 * R) * (Δ * u) = Real.pi / (2 * R) * Δ * u := by ring
      _ ≤ Real.pi * (1 / 800) := mul_le_mul hinv hule hu0 hπ.le
      _ ≤ 1 / 100 := by linarith
  have hΔe : ((1 + Δ - 1) / 1 : ℝ) = Δ := by ring
  have hΔsq : Δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hκ : (9 / 25 : ℝ) ≤ (1 - ((1 + Δ - 1) / 1) ^ 2) / 2 - Real.pi / (2 * R) * (Δ * u) := by
    rw [hΔe]
    linarith
  set T := 2 * Real.pi * n / (j * R) with hTd
  have hT0 : 0 ≤ T := by positivity
  have hX : R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
      ≤ 3 / 50 / j := by
    have e : R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
        = (8 * Real.pi * (u * n) + 12 * (R / Δ) * (u * j)
            + Real.pi / (2 * R) * Δ * (u * j)) / j := by
      rw [hTd]
      field_simp
      ring
    have hrΔ : R / Δ ≤ 1 := (div_le_one hΔ0).2 hRhi
    have hrΔ0 : 0 ≤ R / Δ := by positivity
    have huj0 : 0 ≤ u * j := mul_nonneg hu0 hj'.le
    have t1 : 8 * Real.pi * (u * n) ≤ 8 * 3.15 * (1 / 800) :=
      mul_le_mul (by linarith) hun (mul_nonneg hu0 hn'.le) (by norm_num)
    have t2 : 12 * (R / Δ) * (u * j) ≤ 12 * 1 * (1 / 800) :=
      mul_le_mul (by linarith) huj huj0 (by norm_num)
    have t3 : Real.pi / (2 * R) * Δ * (u * j) ≤ 3.15 * (1 / 800) :=
      mul_le_mul (by linarith) huj huj0 (by norm_num)
    rw [e]
    norm_num at t1 t2 t3
    exact div_le_div_of_nonneg_right (by linarith) hj'.le
  obtain ⟨hΨ, hg0, hgle, hsw⟩ := clock_packet_shift_le (M := M) (c := 1) (μ₀ := 1)
    (μ₁ := 1 + Δ) (ℓ := ringLen K) (D := 1 / (600 * n)) (p₀ := p₀) one_pos one_pos
    (by linarith) (ringLen_pos hK) hWin hWD' β hβ (J := ringHop K M)
    (σ := ringSigma K M p₀) (R := R) (ε := Δ * u) rfl rfl rfl hεeq.symm (ρ := Δ / 2)
    (by positivity) hRlo hρm rfl (κ := 9 / 25) (by norm_num) hκ hT0
  refine ⟨_, hΨ, hg0, ?_, fun t ht htT => (hsw t ht htT).trans ?_⟩
  · have e : R / (16 * (9 / 25)) = R * (25 / 144) := by ring
    rw [e] at hgle
    linarith
  · calc R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
            / (4 * (9 / 25))
        ≤ 3 / 50 / j / (4 * (9 / 25)) := div_le_div_of_nonneg_right hX (by norm_num)
      _ = 1 / (24 * j) := by
        field_simp
        norm_num

/-- **The flat clock packet swings more closely over part of its horizon**: the instance of
`narrow_clock_packet_swing_fine` on the flat window of #392. -/
theorem flat_clock_swing_fine {n N j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M (1 / 2) Δ) →
        |clockPointerShift (ringHop (1200 * n * N) M) 1 (1 + Δ) g trainF_periodic
              (0 : AddCircle (1 : ℝ)) (deviceRay _ hΨ) t
            - 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M (1 / 2) Δ * t))|
          ≤ 1 / (24 * j) := by
  have hn : 0 < n := hj.trans_le hjn
  exact narrow_clock_packet_swing_fine (lo := 0) hj hjn (by positivity) (by norm_num)
    (by norm_num) (flatWindow_mem_range hn hM)
    (fun m hm => Or.inl (flatWindow_width hn hN m hm)) (flatAmpN N)
    (sum_norm_flatAmpN n hN) hΔ0 hΔ

end Swing

/-! ### Where the pointer of a closing gate stops -/

section Stop

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] {a b : ℕ} (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h : ℝ → ℝ}
  (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {G₁ : Matrix (ι × κ) (ι × κ) ℂ} {Y : Matrix κ κ ℂ}

/-- ★★ **Where the pointer of a closing gate stops.** On a product ray, a pointer coupled to
the gate `gateOp r Y` with profile derivative `z`. If the two carriers have weight at most `ε`
outside the relation up to `t_a`, and the second carrier's own displacement at `t_a` is within
`δ₀` of `(1/4)(1 − cos R t_a)`, then at any later `t_b` the pointer's displacement is within
`δ₀ + 2|z| ε t_a + 2|z| (t_b − t_a)` of `(1/4)(1 − cos R t_a)`. -/
theorem coincShift_stop_le (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (z : ℝ) (p : GenArena ι) (q : GenArena κ) {R δ₀ ε ta tb : ℝ} (hta : 0 ≤ ta)
    (hab : ta ≤ tb)
    (hclock : |-2 * z * (∫ s in (0 : ℝ)..ta, arenaObs Y (arenaKick (idxFreeU hC s) q))
        - 1 / 4 * (1 - Real.cos (R * ta))| ≤ δ₀)
    (hnear0 : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε) :
    |coincShift hA hC (gateOp σ τ r Y) z p q tb - 1 / 4 * (1 - Real.cos (R * ta))|
      ≤ δ₀ + 2 * |z| * ε * ta + 2 * |z| * (tb - ta) := by
  have e := coincShift_gateOp_add_not σ τ r hA hC Y z p q ta
  have hD0 : coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q 0 = 0 := by
    rw [coincShift, intervalIntegral.integral_same, mul_zero]
  have hcl := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
    (ε := ε) hta (fun u hu0 hut =>
      (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans (hnear0 u hu0 hut))
  rw [hD0, sub_zero, sub_zero] at hcl
  have hW1 : ∀ u, arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)) ≤ 1 := fun u => by
    have h1 := arenaObs_coincProj_add_not σ τ r
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q))
    have h2 := arenaObs_coincProj_prodRay_nonneg σ τ (fun x y => ¬ r x y)
      (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)
    linarith
  have hmid := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := 1) hab
    (fun u _ _ => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans (hW1 u))
  have h1 := abs_le.1 hclock
  have h2 := abs_le.1 hcl
  have h3 := abs_le.1 hmid
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- ★★★ **The return reading from the clock's phase when the gate closes.** The return
reading of #399 with its band replaced: write
`σ = 2 δ₀ + 2|z| (ε t_a + (t_b − t_a) + ε (t₃ − t_b))`. If `σ < 1/12` and
`4 σ < |cos R t_a|`, then at every flow time of `[t₄, t₅]` the pointer coupled to the
complementary gate has a count `N` with
`|2π N − R (t₃ − t_b)| ≤ 2π (6|z| ((t_b − t_a) + (t₄ − t₃)) + 7)`. -/
theorem coincFlow_return_reading_of_phase (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hG₁ : G₁.IsHermitian) (hYh : Y.IsHermitian) (hYs : ∀ i j, τ i ≠ τ j → Y i j = 0)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (p : GenArena ι) (q : GenArena κ) {θ ψ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hh.lift ψ.2 = 0) (hψ1 : rep ψ.1 = 1 / 12)
    {R δ₀ ε ta tb t3 t4 t5 : ℝ} (hR : 0 < R) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hta : 0 ≤ ta)
    (hab : ta ≤ tb) (hb3 : tb ≤ t3) (h34 : t3 ≤ t4) (h45 : t4 ≤ t5)
    (hclock : ∀ t, 0 ≤ t → t ≤ t3 →
      |-2 * hh.deriv_periodic.lift ψ.2
            * (∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q))
          - 1 / 4 * (1 - Real.cos (R * t))| ≤ δ₀)
    (hnear0 : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hapart : ∀ s, tb ≤ s → s ≤ t3 →
      arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hnear1 : ∀ s, t4 ≤ s → s ≤ t5 →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hσ : 2 * δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * (ε * ta + (tb - ta) + ε * (t3 - tb))
      < 1 / 12)
    (hphase :
      4 * (2 * δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * (ε * ta + (tb - ta) + ε * (t3 - tb)))
        < |Real.cos (R * ta)|)
    (h4 : 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t5 - t4) ≤ 1 / 6) :
    ∀ t, t4 ≤ t → t ≤ t5 →
      ∃ N : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
          {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
          (fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ (fun x y => ¬ r x y) Y) hf hh hc hch t
            ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) t N
        ∧ |(N : ℝ) * (2 * Real.pi) - R * (t3 - tb)|
            ≤ 2 * Real.pi
              * (6 * |hh.deriv_periodic.lift ψ.2| * ((tb - ta) + (t4 - t3)) + 7) := by
  have hstop := abs_le.1 (coincShift_stop_le σ τ r hA hC hY (hh.deriv_periodic.lift ψ.2) p q
    (R := R) hta hab (hclock ta hta (hab.trans hb3)) hnear0)
  set z := hh.deriv_periodic.lift ψ.2 with hz
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have n1 : 0 ≤ 2 * |z| * ε * ta := by positivity
  have n2 : 0 ≤ 2 * |z| * (tb - ta) := mul_nonneg (by positivity) (sub_nonneg.2 hab)
  have n3 : 0 ≤ 2 * |z| * ε * (t3 - tb) := mul_nonneg (by positivity) (sub_nonneg.2 hb3)
  have e : 2 * |z| * (ε * ta + (tb - ta) + ε * (t3 - tb))
      = 2 * |z| * ε * ta + 2 * |z| * (tb - ta) + 2 * |z| * ε * (t3 - tb) := by ring
  rw [e] at hσ hphase
  have hcos1 := Real.cos_le_one (R * ta)
  have hcos2 := Real.neg_one_le_cos (R * ta)
  refine coincFlow_return_reading e₁ e₂ σ τ r hA hC hG₁ hYh hYs hY hf hh hc hch p q hθ hψ hψ1
    hR hδ₀ hε hta hab hb3 h34 h45 hclock hnear0 hapart hnear1 ?_ ?_ h4 ?_
  · linarith
  · linarith
  · rcases le_total 0 (Real.cos (R * ta)) with h0 | h0
    · rw [abs_of_nonneg h0] at hphase
      left
      constructor <;> linarith [hstop.1, hstop.2]
    · rw [abs_of_nonpos h0] at hphase
      right
      constructor <;> linarith [hstop.1, hstop.2]

end Stop

/-! ### A messenger packet and the flat clock packet on the ring -/

section Ring

variable {n N M : ℕ}

/-- ★★★ **The return reading on the ring from the clock's phase when the gate closes.** On one
ring, with both gates of "within the angle `w`" in one run, the flat clock packet with
`n ≥ 4`; `R` the clock's rate. Suppose that at every flow time up to `t₅` the two budgets add
up to at most `ε (1 − cos δ)`; that the messenger's predicted angle is within `w − 2δ` of both
levels' predicted angles up to `t_a` and again on `[t₄, t₅]`, and more than `w + 2δ` from both
on `[t_b, t₃]`, with `t₃ ≤ 2π n/(4R)`; that
`2 (R/5) (ε t_a + (t_b − t_a) + ε (t₃ − t_b)) ≤ 1/48` and `2 (R/5) ε (t₅ − t₄) ≤ 1/6`; and
that `1/6 < |cos R t_a|`. Then for some strength `0 < g ≤ R/5` the complementary pointer has
at every flow time of `[t₄, t₅]` a count `N'` with
`|2π N' − R (t₃ − t_b)| ≤ 2π (6 g ((t_b − t_a) + (t₄ − t₃)) + 7)`. -/
theorem flat_clock_return_reading_of_phase (hn : 4 ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {a b : ℕ}
    (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1)) {μ P D p₀ : ℝ} (hμ : 0 < μ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₀ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β t₀ ≠ 0)
    {w δ ε ta tb t3 t4 t5 : ℝ} (hδ : 0 < δ) (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hb3 : tb ≤ t3) (h34 : t3 ≤ t4)
    (h45 : t4 ≤ t5)
    (ht3T : t3 ≤ 2 * Real.pi * n / (4 * ringRate (1200 * n * N) M (1 / 2) Δ))
    (hbudget : ∀ s, 0 ≤ s → s ≤ t5 →
      (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) D P
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)
      ≤ ε * (1 - Real.cos δ))
    (hnear0 : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s)
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s))
    (hapart : ∀ s, tb ≤ s → s ≤ t3 →
      Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s) < Real.cos (w + 2 * δ)
        ∧ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s) < Real.cos (w + 2 * δ))
    (hnear1 : ∀ s, t4 ≤ s → s ≤ t5 →
      Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s)
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s))
    (hS : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5)
        * (ε * ta + (tb - ta) + ε * (t3 - tb)) ≤ 1 / 48)
    (hphase : 1 / 6 < |Real.cos (ringRate (1200 * n * N) M (1 / 2) Δ * ta)|)
    (hS4 : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (t5 - t4) ≤ 1 / 6) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ ∀ t, t4 ≤ t → t ≤ t5 →
          ∃ N' : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
              {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
              (ringReturnRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                (chainRay _ hψ) (deviceRay _ hΨ)) t N'
            ∧ |(N' : ℝ) * (2 * Real.pi)
                  - ringRate (1200 * n * N) M (1 / 2) Δ * (t3 - tb)|
                ≤ 2 * Real.pi * (6 * g * ((tb - ta) + (t4 - t3)) + 7) := by
  have hπ := Real.pi_pos
  have hn0 : 0 < n := by omega
  have hK : 0 < 1200 * n * N := by positivity
  have hR : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hR0 : 0 < ringRate (1200 * n * N) M (1 / 2) Δ := by linarith
  obtain ⟨g, hΨ, hg0, hg5, hsw⟩ := flat_clock_swing_fine (M := M) (j := 4) (by norm_num) hn hN
    hM hΔ0 hΔ
  simp only [Nat.cast_ofNat] at hsw
  refine ⟨g, hΨ, hg0, hg5, ?_⟩
  set R := ringRate (1200 * n * N) M (1 / 2) Δ with hRd
  have hcos : 0 < 1 - Real.cos δ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith : δ ≤ Real.pi) hδ
    rw [Real.cos_zero] at h
    linarith
  have hz : (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g :=
    scaledTrainF_deriv_lift_zero g
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have h03 : 0 ≤ t3 := (hta.trans hab).trans hb3
  have hX0 : 0 ≤ ε * ta + (tb - ta) + ε * (t3 - tb) :=
    add_nonneg (add_nonneg (mul_nonneg hε hta) (sub_nonneg.2 hab))
      (mul_nonneg hε (sub_nonneg.2 hb3))
  have hgX : 2 * g * (ε * ta + (tb - ta) + ε * (t3 - tb)) ≤ 1 / 48 :=
    (mul_le_mul_of_nonneg_right (by linarith : 2 * g ≤ 2 * (R / 5)) hX0).trans hS
  have key_near : ∀ s, 0 ≤ s → s ≤ t5 →
      Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s)
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s) →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ ringNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε :=
    fun s hs0 hs hc => le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (ringGate_not_le hδ.le hw (by linarith) hc.1 hc.2 _ _) hcos.le).trans
        ((outside_arcs_flat_clock_le hn0 hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
          (hbudget s hs0 hs))) hcos
  have key_apart : ∀ s, 0 ≤ s → s ≤ t5 →
      Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s) < Real.cos (w + 2 * δ)
        ∧ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s) < Real.cos (w + 2 * δ) →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε :=
    fun s hs0 hs hc => le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (ringGate_le hδ.le (by linarith) hwπ hc.1 hc.2 _ _) hcos.le).trans
        ((outside_arcs_flat_clock_le hn0 hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
          (hbudget s hs0 hs))) hcos
  have H := coincFlow_return_reading_of_phase e₁ e₂
    (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (G₁ := gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
      (levelSwap (ZMod (M + 1) × Fin 2)))
    (gateOp_isHermitian _ _ _ (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne)
    (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
    (fun s' q => abs_arenaObs_siteSel_mul_levelSwap_le
      (fun x : ZMod (M + 1) × Fin 2 => x.1) s' q)
    (scaledTrainF_periodic g) (scaledTrainF_periodic g) (contDiff_scaledTrainF g)
    (contDiff_scaledTrainF g) (chainRay _ hψ) (deviceRay _ hΨ)
    (θ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))
    (ψ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))
    (scaledTrainF_lift_zero g) (scaledTrainF_lift_zero g) hrep (R := R) (δ₀ := 1 / 96)
    (ε := ε) (ta := ta) (tb := tb) (t3 := t3) (t4 := t4) (t5 := t5) hR0 (by norm_num) hε hta
    hab hb3 h34 h45
  simp only [hz, abs_neg, abs_of_pos hg0] at H
  refine H ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht0 ht3
    have h := hsw t ht0 (ht3.trans ht3T)
    rw [clockPointerShift_trainF_eq, hz] at h
    exact h.trans (by norm_num)
  · exact fun s hs0 hs =>
      key_near s hs0 (hs.trans (hab.trans (hb3.trans (h34.trans h45)))) (hnear0 s hs0 hs)
  · exact fun s hbs hs =>
      key_apart s ((hta.trans hab).trans hbs) (hs.trans (h34.trans h45)) (hapart s hbs hs)
  · exact fun s h4s hs => key_near s ((h03.trans h34).trans h4s) hs (hnear1 s h4s hs)
  · linarith
  · linarith
  · have h := mul_le_mul_of_nonneg_right (by linarith : 2 * g ≤ 2 * (R / 5))
      (mul_nonneg hε (sub_nonneg.2 h45))
    calc 2 * g * ε * (t5 - t4) = 2 * g * (ε * (t5 - t4)) := by ring
      _ ≤ 2 * (R / 5) * (ε * (t5 - t4)) := h
      _ = 2 * (R / 5) * ε * (t5 - t4) := by ring
      _ ≤ 1 / 6 := hS4

end Ring

end CSD.RecordLayer

end
