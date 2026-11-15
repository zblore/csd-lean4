/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedStopBand

/-!
# The radar reading: the emission count and the return count of one run

**Category:** 7-SigmaLayer (the record layer). BACKLOG #401 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, eleventh brick: Remainder (a) of #400, the radar time and distance. No new
assumption beyond UA-18.

In the run with both gates the first pointer is coupled to "the messenger is with the clock"
and the last to its complement. This module reads both in that one run and forms the radar
time and the radar distance, in ticks, from the two counts.

* ★★ `coincFlow_first_gated_reading` — the emission reading of #394 for the *first* pointer
  of the flow of #393: at every flow time of `[t_b, t_c]` a count `N` with
  `|2π N − R t_a| ≤ 2π (6|z| (t_b − t_a) + 7/2)`;
* ★★★ `coincFlow_radar_reading` — both pointers of one run, started at `1/12` with the same
  profile derivative, under the hypotheses of #400: at every flow time `s` of `[t_b, t₃]` the
  first pointer has a count `N_e` and at every flow time `t` of `[t₄, t₅]` the last has a
  count `N_r`, with the two bounds of #394 and #399, and with `e = N_e`, `r = N_e + N_r`:
  `|2π (e + r)/2 − R (t_a + (t₃ − t_b)/2)| ≤ 2π (9|z| (t_b − t_a) + 3|z| (t₄ − t₃) + 7)` and
  `|2π (r − e)/2 − R (t₃ − t_b)/2| ≤ 2π (3|z| ((t_b − t_a) + (t₄ − t₃)) + 7/2)`;
* `flat_ring_not_near_le`, `flat_ring_near_le` — the weight outside, and inside, "within the
  angle `w`" for a messenger packet and the flat clock packet, from the budgets at one flow
  time;
* ★★★ `flat_clock_radar_reading` — the same on the ring for any messenger packet and the flat
  clock packet with `n ≥ 4`, in `ringReturnRun`, for some strength `0 < g ≤ R/5`.

## Exact scope

* **Two counts at two flow times.** The emission count is the first pointer's count at a
  flow time of `[t_b, t₃]`, while the messenger is away. After `t₄` that pointer's gate is
  open again and it ticks on, so at the flow times of `[t₄, t₅]` at which the return count
  is read it no longer shows the emission count. UA-18 (d) takes a reading to be the number
  of tick records of the pointer's first open period; no pointer here holds that number
  after the period ends, and nothing here says the two counts are read together.
* **The radar time and distance are arithmetic on the two counts.** `e = N_e` and
  `r = N_e + N_r` are the two readings of `radar_lorentz_error` in ticks; `(e + r)/2` and
  `(r − e)/2` are formed in the statement, by no pointer. They are compared with flow times:
  `t_a + (t₃ − t_b)/2` and `(t₃ − t_b)/2`, times the clock's rate `R`. Neither count sees
  the closing `[t_a, t_b]` or the reopening `[t₃, t₄]`; those are the error terms.
* **No distance in sites.** `(r − e)/2` is half the time away in ticks. That it is the
  distance to where the messenger turned, at its speed, is not stated: how the messenger
  comes back is not said (a lap of the ring, or a wall), and its speed enters no hypothesis.
* **Conditional as #400**: a gate that closes within a small part of a tick, and
  `1/6 < |cos R t_a|`; inequalities between real numbers with no values exhibited; no run
  with a return exhibited.
* **Only the fibres where both profiles vanish, and only product starts**, as #393; for some
  strength, as #396; a ring and two carriers; one observer.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-18, UO-16, UD-146, UD-148, UD-157, UD-159, UD-160, UD-161, UD-162);
`RecordLayer/UnifiedStopBand.lean` (#400: `coincFlow_return_reading_of_phase`,
`flat_clock_swing_fine`); `RecordLayer/UnifiedReturnReading.lean` (#399: `ringReturnRun`,
`packetAngleGap`); `RecordLayer/UnifiedEmissionReading.lean` (#396:
`outside_arcs_flat_clock_le`, `clockPointerShift_trainF_eq`);
`RecordLayer/UnifiedGateRegions.lean` (#395: `ringGate_not_le`, `ringGate_le`);
`RecordLayer/UnifiedGatedReading.lean` (#394: `gated_pointer_count`,
`coincFlow_gated_reading`, `abs_coincShift_sub_le`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincFlow_prodRay`);
`RecordLayer/DiracTwoCharts.lean` (`radar_lorentz_error`, whose readings `e`, `r` these are
for one observer).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The first pointer's count, and both counts of one run -/

section Reading

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] {a b : ℕ} (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h : ℝ → ℝ}
  (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {G₂ : Matrix (ι × κ) (ι × κ) ℂ} {Y : Matrix κ κ ℂ}

/-- ★★ **The emission reading of the first pointer.** For the flow of #393 with its *first*
pointer coupled to the gate `gateOp r Y`, from a product ray on a fibre where both profiles
vanish, `z` the derivative of the first pointer's profile. Under the hypotheses of
`coincFlow_gated_reading` (#394) read for the first pointer, at every flow time of
`[t_b, t_c]` it has a count `N` with `|2π N − R t_a| ≤ 2π (6|z| (t_b − t_a) + 7/2)`. -/
theorem coincFlow_first_gated_reading (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hYh : Y.IsHermitian) (hYs : ∀ i j, τ i ≠ τ j → Y i j = 0) (hG₂ : G₂.IsHermitian)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (p : GenArena ι) (q : GenArena κ) {θ ψ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hh.lift ψ.2 = 0) {R A δ₀ ε ta tb tc : ℝ} (hR : 0 < R)
    (hA' : 0 < A) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hclock : ∀ t, 0 ≤ t → t ≤ ta →
      |-2 * hf.deriv_periodic.lift θ.2
            * (∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q))
          - A * (1 - Real.cos (R * t))| ≤ δ₀)
    (hopen : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hclosed : ∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * ε * (tc - tb) ≤ 1 / 6)
    (h₁ : δ₀ + 2 * |hf.deriv_periodic.lift θ.2| * ε * ta < rep θ.1)
    (h₂ : rep θ.1 + (δ₀ + 2 * |hf.deriv_periodic.lift θ.2| * ε * ta) ≤ 1 / 6)
    (h₃ : 1 / 3 < rep θ.1 + 2 * A - (δ₀ + 2 * |hf.deriv_periodic.lift θ.2| * ε * ta))
    (h₄ : rep θ.1 + 2 * A + (δ₀ + 2 * |hf.deriv_periodic.lift θ.2| * ε * ta) ≤ 5 / 6) :
    ∀ t, tb ≤ t → t ≤ tc →
      ∃ N : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ readyArc 2}
          {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ displayArc}
          (fun t => coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y) G₂ hf hh hc hch t
            ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) t N
        ∧ |(N : ℝ) * (2 * Real.pi) - R * ta|
            ≤ 2 * Real.pi * (6 * |hf.deriv_periodic.lift θ.2| * (tb - ta) + 7 / 2) := by
  set z := hf.deriv_periodic.lift θ.2 with hz
  have hπ := Real.pi_pos
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hW1 : ∀ u, arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)) ≤ 1 := fun u => by
    have h1 := arenaObs_coincProj_add_not σ τ r
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q))
    have h2 := arenaObs_coincProj_prodRay_nonneg σ τ (fun x y => ¬ r x y)
      (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)
    linarith
  have hopen' : ∀ t, 0 ≤ t → t ≤ ta →
      |coincShift hA hC (gateOp σ τ r Y) z p q t - A * (1 - Real.cos (R * t))|
        ≤ δ₀ + 2 * |z| * ε * ta := by
    intro t ht0 htta
    have e := coincShift_gateOp_add_not σ τ r hA hC Y z p q t
    have hnot := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
      (ε := ε) ht0 (fun u hu0 hut =>
        (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
          (hopen u hu0 (hut.trans htta)))
    have h0 : coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q 0 = 0 := by
      rw [coincShift, intervalIntegral.integral_same, mul_zero]
    rw [h0, sub_zero, sub_zero] at hnot
    have hcl := hclock t ht0 htta
    have hmono : 2 * |z| * ε * t ≤ 2 * |z| * ε * ta :=
      mul_le_mul_of_nonneg_left htta (by positivity)
    rw [abs_le] at hnot hcl ⊢
    constructor <;> linarith [hnot.1, hnot.2, hcl.1, hcl.2]
  obtain ⟨Na, Nb, -, hNa', -, hNab, hNb', hwin⟩ := gated_pointer_count
    (Y := KSigma (a * (b + 1) + b + 1))
    (γ := fun t =>
      (((coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y) G₂ hf hh hc hch t
            ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)).1.1,
          (coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y) G₂ hf hh hc hch t
            ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)).2),
        (coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y) G₂ hf hh hc hch t
          ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)).1.2))
    (q := θ) (D := fun t => coincShift hA hC (gateOp σ τ r Y) z p q t) (v := 2 * |z|)
    hR hA' (add_nonneg hδ₀ (by positivity)) hta hab hbc
    (fun t _ _ => by
      show (coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y) G₂ hf hh hc hch t
        ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)).1.2 = _
      rw [coincFlow_prodRay e₁ e₂ hA hC (gateOp_isHermitian σ τ r hYh hYs) hG₂ hf hh hc hch t
        p q hθ hψ]
      rfl)
    hopen' h₁ h₂ h₃ h₄
    (fun s t _ hst _ => by
      have h := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := 1) hst
        (fun u _ _ => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans (hW1 u))
      linarith)
    (fun s t hbs hst htc => by
      have h := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := ε) hst
        (fun u hsu hut => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans
          (hclosed u (hbs.trans hsu) (hut.trans htc)))
      have hmono : 2 * |z| * ε * (t - s) ≤ 2 * |z| * ε * (tc - tb) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith)
  intro t hbt htc
  obtain ⟨N, hN, h1, h2⟩ := hwin t hbt htc
  refine ⟨N, hN, ?_⟩
  have hNa1 : (Na : ℝ) ≤ N := by exact_mod_cast hNab.trans h1
  have hN1 : (N : ℝ) ≤ Nb + 1 := by exact_mod_cast h2
  have htr : 0 ≤ 6 * |z| * (tb - ta) := by
    have : 0 ≤ tb - ta := sub_nonneg.2 hab
    positivity
  rw [abs_le] at hNa' ⊢
  constructor
  · nlinarith [hNa'.1, hNa'.2]
  · nlinarith [hNa'.1, hNa'.2]

/-- ★★★ **The radar reading: both counts of one run.** For the flow of #393 with its first
pointer coupled to the gate `gateOp r Y` and its last to the complementary gate, both started
at `1/12` with the same profile derivative `z`, under the hypotheses of
`coincFlow_return_reading_of_phase` (#400). At every flow time `s` of `[t_b, t₃]` the first
pointer has a count `N_e`, and at every flow time `t` of `[t₄, t₅]` the last has a count
`N_r`, with `|2π N_e − R t_a| ≤ 2π (6|z| (t_b − t_a) + 7/2)`,
`|2π N_r − R (t₃ − t_b)| ≤ 2π (6|z| ((t_b − t_a) + (t₄ − t₃)) + 7)`, and for `e = N_e`,
`r = N_e + N_r`: `(e + r)/2` within `9|z| (t_b − t_a) + 3|z| (t₄ − t₃) + 7` ticks of
`R (t_a + (t₃ − t_b)/2)/2π` and `(r − e)/2` within `3|z| ((t_b − t_a) + (t₄ − t₃)) + 7/2`
ticks of `R (t₃ − t_b)/(4π)`. -/
theorem coincFlow_radar_reading (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hYh : Y.IsHermitian) (hYs : ∀ i j, τ i ≠ τ j → Y i j = 0)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (p : GenArena ι) (q : GenArena κ) {θ ψ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hh.lift ψ.2 = 0) (hθ1 : rep θ.1 = 1 / 12)
    (hψ1 : rep ψ.1 = 1 / 12)
    (hzz : hf.deriv_periodic.lift θ.2 = hh.deriv_periodic.lift ψ.2)
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
    ∀ s, tb ≤ s → s ≤ t3 → ∀ t, t4 ≤ t → t ≤ t5 →
      ∃ Ne Nr : ℕ,
        IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ readyArc 2}
            {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ displayArc}
            (fun t => coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y)
              (gateOp σ τ (fun x y => ¬ r x y) Y) hf hh hc hch t
              ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) s Ne
          ∧ IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
              {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
              (fun t => coincFlow e₁ e₂ A₀ C₀ (gateOp σ τ r Y)
                (gateOp σ τ (fun x y => ¬ r x y) Y) hf hh hc hch t
                ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) t Nr
          ∧ |(Ne : ℝ) * (2 * Real.pi) - R * ta|
              ≤ 2 * Real.pi * (6 * |hh.deriv_periodic.lift ψ.2| * (tb - ta) + 7 / 2)
          ∧ |(Nr : ℝ) * (2 * Real.pi) - R * (t3 - tb)|
              ≤ 2 * Real.pi
                * (6 * |hh.deriv_periodic.lift ψ.2| * ((tb - ta) + (t4 - t3)) + 7)
          ∧ |((Ne : ℝ) + (Ne + Nr)) / 2 * (2 * Real.pi) - R * (ta + (t3 - tb) / 2)|
              ≤ 2 * Real.pi
                * (9 * |hh.deriv_periodic.lift ψ.2| * (tb - ta)
                  + 3 * |hh.deriv_periodic.lift ψ.2| * (t4 - t3) + 7)
          ∧ |(((Ne : ℝ) + Nr) - Ne) / 2 * (2 * Real.pi) - R * ((t3 - tb) / 2)|
              ≤ 2 * Real.pi
                * (3 * |hh.deriv_periodic.lift ψ.2| * ((tb - ta) + (t4 - t3)) + 7 / 2) := by
  have H2 := coincFlow_return_reading_of_phase e₁ e₂ σ τ r hA hC
    (G₁ := gateOp σ τ r Y) (gateOp_isHermitian σ τ r hYh hYs) hYh hYs hY hf hh hc hch p q hθ hψ
    hψ1 hR hδ₀ hε hta hab hb3 h34 h45 hclock hnear0 hapart hnear1 hσ hphase h4
  have H1 := coincFlow_first_gated_reading e₁ e₂ σ τ r hA hC hYh hYs
    (G₂ := gateOp σ τ (fun x y => ¬ r x y) Y)
    (gateOp_isHermitian σ τ (fun x y => ¬ r x y) hYh hYs) hY hf hh hc hch p q hθ hψ
    (R := R) (A := 1 / 4) (δ₀ := δ₀) (ε := ε) (ta := ta) (tb := tb) (tc := t3) hR
    (by norm_num) hδ₀ hε hta hab hb3
    (fun t h0 h1 => by
      rw [hzz]
      exact hclock t h0 (h1.trans (hab.trans hb3)))
    hnear0 hapart
  rw [hzz, hθ1] at H1
  have hz0 : 0 ≤ |hh.deriv_periodic.lift ψ.2| := abs_nonneg _
  have n1 : 0 ≤ 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta := by positivity
  have n2 : 0 ≤ 2 * |hh.deriv_periodic.lift ψ.2| * (tb - ta) :=
    mul_nonneg (by positivity) (sub_nonneg.2 hab)
  have n3 : 0 ≤ 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb) :=
    mul_nonneg (by positivity) (sub_nonneg.2 hb3)
  have e : 2 * |hh.deriv_periodic.lift ψ.2| * (ε * ta + (tb - ta) + ε * (t3 - tb))
      = 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta + 2 * |hh.deriv_periodic.lift ψ.2| * (tb - ta)
        + 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb) := by ring
  rw [e] at hσ
  have H1' := H1 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  intro s hs1 hs2 t ht1 ht2
  obtain ⟨Ne, hNe, be⟩ := H1' s hs1 hs2
  obtain ⟨Nr, hNr, br⟩ := H2 t ht1 ht2
  refine ⟨Ne, Nr, hNe, hNr, be, br, ?_, ?_⟩
  · have b1 := abs_le.1 be
    have b2 := abs_le.1 br
    rw [abs_le]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  · have b2 := abs_le.1 br
    rw [abs_le]
    constructor <;> linarith [b2.1, b2.2]

end Reading

/-! ### A messenger packet and the flat clock packet on the ring -/

section Ring

variable {n N M : ℕ}

/-- **The weight outside "within the angle `w`"** of a messenger packet and the flat clock
packet at the flow time `s`, when the two budgets add up to at most `ε (1 − cos δ)` and the
messenger's predicted angle is within `w − 2δ` of both levels' predicted angles. -/
theorem flat_ring_not_near_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {Δ : ℝ} (hΔ0 : 0 < Δ) {μ P D p₀ : ℝ} (hμ : 0 < μ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₀ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ) (flatWindow n N)
      (flatAmpN N) (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0)
    {w δ ε s : ℝ} (hδ : 0 < δ) (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (hb : (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) D P
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)
      ≤ ε * (1 - Real.cos δ))
    (hc : Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s)
      ∧ Real.cos (w - 2 * δ) ≤ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        fun k k' => ¬ ringNear (M + 1) w k k')
      (prodRay
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
          (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
        (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
          (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε := by
  have hcos : 0 < 1 - Real.cos δ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith : δ ≤ Real.pi) hδ
    rw [Real.cos_zero] at h
    linarith
  exact le_of_mul_le_mul_right
    ((mul_le_mul_of_nonneg_right
      (ringGate_not_le hδ.le hw (by linarith) hc.1 hc.2 _ _) hcos.le).trans
      ((outside_arcs_flat_clock_le hn hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
        hb)) hcos

/-- **The weight inside "within the angle `w`"** of a messenger packet and the flat clock
packet at the flow time `s`, when the two budgets add up to at most `ε (1 − cos δ)` and the
messenger's predicted angle is more than `w + 2δ` from both levels' predicted angles. -/
theorem flat_ring_near_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {Δ : ℝ} (hΔ0 : 0 < Δ) {μ P D p₀ : ℝ} (hμ : 0 < μ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₀ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ) (flatWindow n N)
      (flatAmpN N) (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0)
    {w δ ε s : ℝ} (hδ : 0 < δ) (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (hb : (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) D P
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)
      ≤ ε * (1 - Real.cos δ))
    (hc : Real.cos (packetAngleGap n N M Δ μ p₀ t₀ 1 s) < Real.cos (w + 2 * δ)
      ∧ Real.cos (packetAngleGap n N M Δ μ p₀ t₀ (1 + Δ) s) < Real.cos (w + 2 * δ)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w))
      (prodRay
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
          (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
        (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
          (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε := by
  have hcos : 0 < 1 - Real.cos δ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith : δ ≤ Real.pi) hδ
    rw [Real.cos_zero] at h
    linarith
  exact le_of_mul_le_mul_right
    ((mul_le_mul_of_nonneg_right
      (ringGate_le hδ.le (by linarith) hwπ hc.1 hc.2 _ _) hcos.le).trans
      ((outside_arcs_flat_clock_le hn hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
        hb)) hcos

/-- ★★★ **The radar reading on the ring.** On one ring, with both gates of "within the angle
`w`" in one run (`ringReturnRun`), the flat clock packet with `n ≥ 4`; `R` the clock's rate.
Under the hypotheses of `flat_clock_return_reading_of_phase` (#400), for some strength
`0 < g ≤ R/5`: at every flow time `s` of `[t_b, t₃]` the first pointer has a count `N_e`, and
at every flow time `t` of `[t₄, t₅]` the last has a count `N_r`, with
`|2π N_e − R t_a| ≤ 2π (6 g (t_b − t_a) + 7/2)`,
`|2π N_r − R (t₃ − t_b)| ≤ 2π (6 g ((t_b − t_a) + (t₄ − t₃)) + 7)`, and for `e = N_e`,
`r = N_e + N_r`:
`|2π (e + r)/2 − R (t_a + (t₃ − t_b)/2)| ≤ 2π (9 g (t_b − t_a) + 3 g (t₄ − t₃) + 7)` and
`|2π (r − e)/2 − R (t₃ − t_b)/2| ≤ 2π (3 g ((t_b − t_a) + (t₄ − t₃)) + 7/2)`. -/
theorem flat_clock_radar_reading (hn : 4 ≤ n) (hN : 0 < N)
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
      ∧ ∀ s, tb ≤ s → s ≤ t3 → ∀ t, t4 ≤ t → t ≤ t5 →
          ∃ Ne Nr : ℕ,
            IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ readyArc 2}
                {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ displayArc}
                (ringReturnRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                  (chainRay _ hψ) (deviceRay _ hΨ)) s Ne
              ∧ IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
                  {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
                  (ringReturnRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                    (chainRay _ hψ) (deviceRay _ hΨ)) t Nr
              ∧ |(Ne : ℝ) * (2 * Real.pi) - ringRate (1200 * n * N) M (1 / 2) Δ * ta|
                  ≤ 2 * Real.pi * (6 * g * (tb - ta) + 7 / 2)
              ∧ |(Nr : ℝ) * (2 * Real.pi)
                    - ringRate (1200 * n * N) M (1 / 2) Δ * (t3 - tb)|
                  ≤ 2 * Real.pi * (6 * g * ((tb - ta) + (t4 - t3)) + 7)
              ∧ |((Ne : ℝ) + (Ne + Nr)) / 2 * (2 * Real.pi)
                    - ringRate (1200 * n * N) M (1 / 2) Δ * (ta + (t3 - tb) / 2)|
                  ≤ 2 * Real.pi * (9 * g * (tb - ta) + 3 * g * (t4 - t3) + 7)
              ∧ |(((Ne : ℝ) + Nr) - Ne) / 2 * (2 * Real.pi)
                    - ringRate (1200 * n * N) M (1 / 2) Δ * ((t3 - tb) / 2)|
                  ≤ 2 * Real.pi * (3 * g * ((tb - ta) + (t4 - t3)) + 7 / 2) := by
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
  have H := coincFlow_radar_reading e₁ e₂
    (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
    (fun s' q => abs_arenaObs_siteSel_mul_levelSwap_le
      (fun x : ZMod (M + 1) × Fin 2 => x.1) s' q)
    (scaledTrainF_periodic g) (scaledTrainF_periodic g) (contDiff_scaledTrainF g)
    (contDiff_scaledTrainF g) (chainRay _ hψ) (deviceRay _ hΨ)
    (θ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))
    (ψ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))
    (scaledTrainF_lift_zero g) (scaledTrainF_lift_zero g) hrep hrep rfl (R := R)
    (δ₀ := 1 / 96) (ε := ε) (ta := ta) (tb := tb) (t3 := t3) (t4 := t4) (t5 := t5) hR0
    (by norm_num) hε hta hab hb3 h34 h45
  simp only [hz, abs_neg, abs_of_pos hg0] at H
  refine H ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht0 ht3
    have h := hsw t ht0 (ht3.trans ht3T)
    rw [clockPointerShift_trainF_eq, hz] at h
    exact h.trans (by norm_num)
  · exact fun s hs0 hs => flat_ring_not_near_le hn0 hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ hψ hΨ
      hδ hw hwπ (hbudget s hs0 (hs.trans (hab.trans (hb3.trans (h34.trans h45)))))
      (hnear0 s hs0 hs)
  · exact fun s hbs hs => flat_ring_near_le hn0 hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ hψ hΨ
      hδ hw hwπ (hbudget s ((hta.trans hab).trans hbs) (hs.trans (h34.trans h45)))
      (hapart s hbs hs)
  · exact fun s h4s hs => flat_ring_not_near_le hn0 hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ hψ
      hΨ hδ hw hwπ (hbudget s ((h03.trans h34).trans h4s) hs) (hnear1 s h4s hs)
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
