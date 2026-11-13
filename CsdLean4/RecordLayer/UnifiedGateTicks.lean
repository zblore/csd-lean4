/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCompositeCarrier

/-!
# The gated pointer ticks while the messenger is in the region; no tick in a short interval after

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #377 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #376.

On the composite carrier of #376 (assumption UA-17) the clock's pointer is coupled to the
product of the messenger's projector on the near half of its ring and the clock's level swap.
#376 bounded the pointer's real displacement. Here the pointer is read through the ready arc
and the displayed arc of #358.

* `pshift_notMem_displayArc_of_mem_readyArc` — a pointer in the ready arc, turned by at most a
  sixth of a turn either way, is not in the displayed arc;
* `isSwing_thd_of_abs_shift_sub_le` — the swing criterion of #358 for the third pointer of a
  three-pointer arena;
* ★ `clockPointerShift_train` — the displacement of the clock's own pointer in the exact
  instance of #358 is `(1/4)(1 − cos R t)`;
* `gateTrainStart`, `gateClockFlow_train_thd`, ★ `abs_gateClockShift_train_sub_le` — from that
  clock and the packet of index `n` of #375, the gated pointer's displacement is within
  `|g_c| t/n` of `(1/4)(1 − cos R t)` up to `(625π/3) n²`;
* ★★ `isSwing_gateClock_before` — **up to a flow time `0 ≤ T ≤ (625π/3) n²` with
  `|g_c| T/n < 1/12` the gated pointer is a swing at the clock's rate `R`**, with thresholds
  `±4|g_c| T/n`;
* ★ `gateClock_tickCount_before` — **it has a tick count at `T`, and the count times the
  period `2π/R` is within one period of `T`** (the count may be zero);
  ★ `gateClock_tick_isRecordWrite` — **each tick whose displayed window ends by `T` is a
  record write** of the third pointer's readout;
* ★★ `gateClock_no_tick_after` — **between two flow times `a ≤ b` of
  `[(3125π/3) n², (4375π/3) n²]` with `|k'(χ₂)||g_c| (b − a)/n ≤ 1/6`, a gated pointer that is
  ready at `a` is not displayed at `b`**: no tick is begun and completed in that interval.

## Exact scope

* **The arena and its limits are those of #376 (UA-17).** A fibre where the gated pointer's
  profile vanishes; a product start; the fine fibres of #375 for the two region pointers. The
  first is a null set of fibres and the second a null set of the base (two calculations, not in
  Lean).
* **The clock is the exact instance of #358**: one momentum mode, a quarter turn early, the
  profile `trainF` on the fibre `χ₂ = 0`, the pointer at `1/12`, the strength `g_c` fixed by
  the rate `R`. That is one point of the clock's state space. `gateClock_no_tick_after` does not
  need it: it holds for every clock ray and every profile on a fibre where the profile
  vanishes.
* **The hypothesis `|g_c| T/n < 1/12` bounds the rate from above.** `g_c` is `R` times a factor
  fixed by the clock's parameters (`hg`; the amplitude `1/4` is tuned by it, as in #358), so at
  `T = (625π/3) n²` it asks for `n R` small. The clock needs `μ₀ < μ₁ < 2μ₀`. The count is within
  one of `R T/2π`, which is large only when `n² R` is large. That both hold, with at least one
  tick, for some clock is not a theorem of this module; it is `gateClock_hasTicks_before` of
  `RecordLayer/UnifiedGateCount.lean` (#378), for every large `n`. For `T` small the swing
  theorem holds with a count of zero.
* **Gated by an occupancy, not by a record.** The pointer swings because the messenger's
  expectation of the near half's projector is close to `1`. No readout of the departure pointer
  enters. The gated pointer is a cyclic coordinate (the generic statement of #374; not
  instantiated for `gateFlow`).
* **"The count stops" is not proved.** What is proved after the transit is that no passage from
  ready to displayed lies inside a sub-interval `[a, b]` short enough for the hypothesis
  `|k'||g_c| (b − a)/n ≤ 1/6`. For the whole interval that needs `|k'||g_c| n ≤ 1/(2500π)`, which
  no theorem here assumes. Nothing is stated for the flow times between `(625π/3) n²` and
  `(3125π/3) n²`, where the pointer may tick, or after `(4375π/3) n²`. A tick begun before
  `(3125π/3) n²` may complete inside the interval. No theorem gives the count at a time after
  departure, and no degree of freedom holds the count (UO-14 (b)).
* **The clock's own pointer is not on this arena.** That it goes on ticking is #358's
  statement on the clock's arena (`isSwing_clockPointerFlow_train`), not a statement here.
* **The tick records last less than one turn** (`IsSwing.notMem_disp_of_cos_eq_one`), as in
  #358. They are `IsRecordWrite`s of the readout history; they are not packaged as
  `ActualOccurrence`s of `gateClockFlow`.
* **Flow times throughout (UA-7).** No distance, no speed, no second observer.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UA-17, UO-14, UO-16, UD-61, UD-62, UD-92, UD-113, UD-114);
`RecordLayer/UnifiedCompositeCarrier.lean` (#376: `gateClockFlow`, `gateClockFlow_apply`,
`gateClockShift`, `fine_gateClock_before`, `fine_gateClock_after`);
`RecordLayer/UnifiedDiracClockTicks.lean` (#358: `IsSwing`, `IsTickCount`,
`isSwing_of_abs_shift_sub_le`, `abs_clockPointerShift_sub_swing_le`, `IsSwing.isRecordWrite`,
`isSwing_clockPointerFlow_train`); `RecordLayer/UnifiedCountAtWrite.lean`
(`IsSwing.abs_tickTime_sub_le`); `RecordLayer/UnifiedClockTwoSites.lean` (`triThdReady`,
`triThdDisplay`, `triThdShown`); `RecordLayer/UnifiedClockSiteRecords.lean`
(`IsSwing.preimage`); `RecordLayer/UnifiedFineTransit.lean` (#375: `finePacket`, `fineFibres`);
`RecordLayer/UnifiedRecordInert.lean` (#374).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The two arcs, and the swing criterion for a third pointer -/

/-- A pointer in the ready arc, turned by at most a sixth of a turn either way, is not in the
displayed arc. The two arcs are a sixth of a turn apart on both sides. -/
theorem pshift_notMem_displayArc_of_mem_readyArc {q : KTorus} {d : ℝ} (hd : |d| ≤ 1 / 6)
    (hq : q ∈ readyArc 2) : pshift d q ∉ displayArc := by
  have hq' : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hq'
  obtain ⟨hd1, hd2⟩ := abs_le.1 hd
  intro hdisp
  have hdisp' : rep (pshift d q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) := hdisp
  rw [shearWidth_two] at hdisp'
  rcases lt_or_ge 0 (rep q.1 + d) with h | h
  · rw [rep_pshift_of_mem q d ⟨h, by linarith [hq'.2]⟩] at hdisp'
    linarith [hdisp'.1, hq'.2]
  · rw [rep_pshift_of_mem_neg q ⟨by linarith [hq'.1], h⟩] at hdisp'
    linarith [hdisp'.2, hq'.1]

/-- **The swing criterion of #358 for the third pointer of a three-pointer arena.** A history
whose third pointer pair is the start `q` turned by `σ t`, with `σ` within `δ` of
`A (1 − cos R t)` up to `T`, is a swing at the rate `R` under the hypotheses of
`isSwing_of_abs_shift_sub_le`. -/
theorem isSwing_thd_of_abs_shift_sub_le {N : ℕ} {γ : ℝ → TriSigma N} {q : KTorus} {σ : ℝ → ℝ}
    {R A δ T : ℝ} (hR : 0 < R) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hγ : ∀ t, 0 ≤ t → t ≤ T → (γ t).2 = pshift (σ t) q)
    (hσ : ∀ t, 0 ≤ t → t ≤ T → |σ t - A * (1 - Real.cos (R * t))| ≤ δ)
    (h₁ : δ < rep q.1) (h₂ : rep q.1 + δ ≤ 1 / 6) (h₃ : 1 / 3 < rep q.1 + 2 * A - δ)
    (h₄ : rep q.1 + 2 * A + δ ≤ 5 / 6) :
    IsSwing (triThdReady N) (triThdDisplay N) γ R (1 - (1 / 3 - rep q.1 - δ) / A)
      (1 - (1 / 3 - rep q.1 + δ) / A) T := by
  obtain ⟨p₀⟩ : Nonempty (CPN (4 * 0 + 3 + 1)) := inferInstance
  exact IsSwing.preimage (π := fun x : TriSigma N => ((p₀, x.2) : KSigma (4 * 0 + 3 + 1)))
    (isSwing_of_abs_shift_sub_le (M := 0) hR hA hδ (fun t ht0 htT => hγ t ht0 htT) hσ h₁ h₂
      h₃ h₄)

/-! ### The clock's own pointer in the exact instance of #358 -/

section Train

variable {M : ℕ}

/-- ★ **The displacement of the clock's own pointer in the exact instance of #358** is
`(1/4)(1 − cos R t)`: one mode, prepared a quarter turn early, the profile `trainF` on the
fibre `θ₂ = 0`, the strength fixed by the rate. -/
theorem clockPointerShift_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g : ℝ}
    (hg : g = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re))
    {t : ℝ} (ht : 0 ≤ t) :
    clockPointerShift J μ₀ μ₁ g trainF_periodic (0 : AddCircle (1 : ℝ))
        (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
          (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t
      = 1 / 4 * (1 - Real.cos (R * t)) := by
  have h1 : 0 < μ₁ := h0.trans h01
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hC := deviceCoherence_single_re_pos (L := M + 1) (J := J) h0 h01.le h10 m hβ
  have hb : 0 < ‖β m‖ ^ 2 := by positivity
  have hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s
        *ᵥ devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s))
        * (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0))‖
      ≤ |s| * 0 := by
    intro s
    rw [deviceCoherence_single_quarter J μ₀ μ₁ m β hRe hR.ne' s, sub_self, norm_zero, mul_zero]
  have hn : (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))).re
      = ‖β m‖ ^ 2 := by
    rw [deviceNorm_devicePacket h0 h1 (distinct_singleton m), Finset.sum_singleton,
      Complex.ofReal_re]
  have hre : (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re
      = 0 := by
    rw [Complex.I_mul_re, deviceCoherence_single_im h0 h1, neg_zero]
  have hAe : (1 / 4 : ℝ) = -(4 * g) * trainF_periodic.deriv_periodic.lift (0 : AddCircle (1 : ℝ))
      * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re / (R * ‖β m‖ ^ 2) := by
    rw [trainF_deriv_lift_zero, hg]
    field_simp
    ring
  have hamp : clockSwingAmp g trainF_periodic (0 : AddCircle (1 : ℝ)) R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))).re
      (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)) = 1 / 4 := by
    rw [clockSwingAmp, hn, Complex.I_mul_im]
    exact hAe.symm
  have herr : clockSwingErr g trainF_periodic (0 : AddCircle (1 : ℝ)) R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))).re
      (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)) 0 t = 0 := by
    unfold clockSwingErr
    rw [trainF_lift_zero, hre]
    simp
  have key := abs_clockPointerShift_sub_swing_le J μ₀ μ₁ g trainF_periodic
    (0 : AddCircle (1 : ℝ)) (devicePacket_single_ne_zero h0 h1 m hβ _) hR hdrift ht le_rfl
  rw [hamp, herr] at key
  exact sub_eq_zero.1 (abs_nonpos_iff.1 key)

end Train

/-! ### The gated pointer before the messenger leaves -/

section Before

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
  (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ}
  (hβ : β m ≠ 0) {R : ℝ}

/-- **The start of the gated run**: the messenger on the fine packet of index `n`, the clock
on the one-mode start of #358 at the rate `R`, as one product ray; the two region pointers at
`θ` and `ψ`; the gated pointer at the angle `1/12` on the fibre `χ₂ = 0`. -/
noncomputable def gateTrainStart (R : ℝ) (θ ψ : KTorus) :
    TriSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc))
      (prodRay (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
        (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
          (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _))), θ), ψ),
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

/-- Along the gated run the third pointer pair is its start turned by `gateClockShift`. -/
theorem gateClockFlow_train_thd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc : ℝ)
    (θ ψ : KTorus) (t : ℝ) :
    (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
        μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)).2
      = pshift (gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
          (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic θ.2 ψ.2 (0 : AddCircle (1 : ℝ))
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
          (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
            (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t)
        ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) := by
  rw [gateTrainStart, gateClockFlow_apply (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t _ _ θ ψ
    (χ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) trainF_lift_zero]

variable (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {gc : ℝ}
  (hg : gc = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- ★ **Before the transit the gated pointer's displacement is within `|g_c| t/n` of
`(1/4)(1 − cos R t)`**, on a fine fibre of the two region pointers, for
`0 ≤ t ≤ (625π/3) n²`. -/
theorem abs_gateClockShift_train_sub_le {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ fineFibres g₁ g₂ hf hh n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀ μ₁
          gc hf hh trainF_periodic φ χ (0 : AddCircle (1 : ℝ))
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
          (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
            (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t
        - 1 / 4 * (1 - Real.cos (R * t))|
      ≤ |gc| * t / n := by
  have key := fine_gateClock_before g₁ g₂ Jc μ₀ μ₁ gc hf hh trainF_periodic hn hL hx
    trainF_lift_zero
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) ht0 ht
  rw [idxPointerShift_clock, clockPointerShift_train Jc h0 h01 h10 m hβ hRe hg ht0,
    trainF_deriv_lift_zero, abs_neg, abs_one, one_mul] at key
  exact key

/-- ★★ **While the messenger is in the near half the gated pointer is a swing at the clock's
rate.** On the composite carrier, from `gateTrainStart`, on a fine fibre of the two region
pointers: up to any flow time `T ≤ (625π/3) n²` with `|g_c| T/n < 1/12` the history of
`gateClockFlow`, read through the third pointer's ready and displayed arcs, is a swing at the
rate `R`, resting only where `cos R t ≥ 4|g_c| T/n` and displaying wherever
`cos R t < −4|g_c| T/n`. -/
theorem isSwing_gateClock_before (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) {θ ψ : KTorus}
    (hx : (θ.2, ψ.2) ∈ fineFibres g₁ g₂ hf hh n) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : T ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) (hδ : |gc| * T / n < 1 / 12) :
    IsSwing (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ))
      R (4 * (|gc| * T / n)) (-(4 * (|gc| * T / n))) T := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hδ0 : 0 ≤ |gc| * T / n := by positivity
  have hsw := isSwing_thd_of_abs_shift_sub_le (A := 1 / 4) (δ := |gc| * T / n) hR
    (by norm_num) hδ0
    (fun t _ _ => gateClockFlow_train_thd g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc θ ψ t)
    (fun t ht0 htT => (abs_gateClockShift_train_sub_le g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ
      hRe hg hx ht0 (htT.trans hT)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htT (abs_nonneg gc)) hr.le))
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)); rw [hrep]; exact hδ)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ _; rw [hrep]; linarith)
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)) + _ - _; rw [hrep]; linarith)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ + _ ≤ _; rw [hrep]; linarith)
  have e₁ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) - |gc| * T / n) / (1 / 4)
      = 4 * (|gc| * T / n) := by
    rw [hrep]
    ring
  have e₂ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) + |gc| * T / n) / (1 / 4)
      = -(4 * (|gc| * T / n)) := by
    rw [hrep]
    ring
  rw [e₁, e₂] at hsw
  exact hsw

/-- ★ **The gated pointer has a tick count while the messenger is in the near half, and the
count times the period is within one period of the flow time.** The count may be zero. Under
the hypotheses of
`isSwing_gateClock_before` there is `N` with `N` ticks by `T` and not `N + 1`, and
`|N · 2π/R − T| ≤ 2π/R`. -/
theorem gateClock_tickCount_before (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hx : (θ.2, ψ.2) ∈ fineFibres g₁ g₂ hf hh n) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : T ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) (hδ : |gc| * T / n < 1 / 12) :
    ∃ N : ℕ, IsTickCount (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
        (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
        (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
          (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
          (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)) T N
      ∧ |(N : ℝ) * (2 * Real.pi / R) - T| ≤ 2 * Real.pi / R := by
  have hsw := isSwing_gateClock_before g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch hx
    hT0 hT hδ
  obtain ⟨N, hN⟩ := hsw.exists_tickCount hT0
  exact ⟨N, hN, hsw.abs_tickTime_sub_le hT0 hN⟩

/-- ★ **Each tick of the gated pointer whose displayed window ends by `T` is a record
write.** Under the hypotheses of
`isSwing_gateClock_before`, in turn `k` the third pointer's readout does not display from the
whole turn until the phase `arccos (4|g_c| T/n)`, and displays through the window of phases
`[arccos d', 2π − arccos d']` for every `d' < −4|g_c| T/n`, when that window ends by `T`. -/
theorem gateClock_tick_isRecordWrite (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hx : (θ.2, ψ.2) ∈ fineFibres g₁ g₂ hf hh n) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : T ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) (hδ : |gc| * T / n < 1 / 12) (k : ℕ) {d' : ℝ}
    (hd'1 : -1 ≤ d') (hd' : d' < -(4 * (|gc| * T / n)))
    (hk : ((k : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) :
    IsRecordWrite
      (fun t => triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
          μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
          (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)))
      ((k : ℝ) * (2 * Real.pi) / R)
      (((k : ℝ) * (2 * Real.pi) + Real.arccos (4 * (|gc| * T / n))) / R)
      (((k : ℝ) * (2 * Real.pi) + Real.arccos d') / R)
      (2 * (Real.pi - Real.arccos d') / R) true :=
  (isSwing_gateClock_before g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch hx hT0 hT
    hδ).isRecordWrite (fun _ => triThdShown_eq_true_iff _ _) k hd'1 hd' hk

end Before

/-! ### The gated pointer after the messenger has arrived -/

section After

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ : ℝ) (Jc μ₀ μ₁ gc : ℝ)
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
  {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)

/-- ★★ **After the transit no tick is begun and completed inside a short interval.** On the
composite carrier, from a
product ray of the fine packet of index `n` and any clock ray, on a fine fibre of the two
region pointers and a fibre where the gated pointer's profile vanishes: for flow times
`a ≤ b` of `[(3125π/3) n², (4375π/3) n²]` with `|k'(χ₂)||g_c| (b − a)/n ≤ 1/6`, if the gated
pointer is in its ready arc at `a` it is not in its displayed arc at `b`. -/
theorem gateClock_no_tick_after (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ : KTorus} (hx : (θ.2, ψ.2) ∈ fineFibres g₁ g₂ hf hh n)
    {χ : KTorus} (hz : hk.lift χ.2 = 0) (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2))
    {a b : ℝ} (ha : 3125 * Real.pi / 3 * (n : ℝ) ^ 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 4375 * Real.pi / 3 * (n : ℝ) ^ 2)
    (hsmall : |hk.deriv_periodic.lift χ.2| * |gc| * (b - a) / n ≤ 1 / 6)
    (hready : gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh hk hc hch hck a
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc))
          (prodRay (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q), θ),
          ψ), χ)
      ∈ triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))) :
    gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
        μ₁ gc hf hh hk hc hch hck b
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc))
          (prodRay (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q), θ),
          ψ), χ)
      ∉ triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) := by
  have hthd : ∀ t : ℝ, (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc))
          (prodRay (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q), θ),
          ψ), χ)).2
      = pshift (gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
          (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh hk θ.2 ψ.2 χ.2
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t) χ := by
    intro t
    rw [gateClockFlow_apply (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
      Jc μ₀ μ₁ gc hf hh hk hc hch hck t _ q θ ψ hz]
  have hmove := (fine_gateClock_after g₁ g₂ Jc μ₀ μ₁ gc hf hh hk hn hL hx χ.2 q ha hab
    hb).trans hsmall
  have hr' : pshift (gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
      (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh hk θ.2 ψ.2 χ.2
      (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q a) χ
      ∈ readyArc 2 := by
    rw [← hthd a]
    exact hready
  have hnd := pshift_notMem_displayArc_of_mem_readyArc hmove hr'
  rw [pshift_add, sub_add_cancel] at hnd
  show (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
    μ₀ μ₁ gc hf hh hk hc hch hck b _).2 ∉ displayArc
  rw [hthd b]
  exact hnd

end After

end CSD.RecordLayer

end
