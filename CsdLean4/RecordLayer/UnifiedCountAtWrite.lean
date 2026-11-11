/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedClockSiteRecords

/-!
# The clock's count at a position write

**Category:** 7-SigmaLayer (the record layer). BACKLOG #366 — the author's programme "From `Σ` to
physical spacetime", milestone M4, condition (c) of obligation UO-14 and Remainder (c) of #360.
`RecordLayer/UnifiedClockSiteRecords.lean` has a tick record and a position record in one run
and does not take the count of ticks at the position write. A radar coordinate is such a count:
the reading of a clock at an emission or a reception. This module takes the count at a position
write. It is not a radar coordinate: no signal is emitted or received.

**The count at a time** (any history). A swing at the rate `R` has a count `N` at every time
`T ≥ 0`, and `|2πN − R T| ≤ 2π` (`IsSwing.exists_tickCount_abs_sub_le`, from #358). In the
clock's own unit: `|N · 2π/R − T| ≤ 2π/R`, one tick period (`IsSwing.abs_tickTime_sub_le`). For
two times `T₀ ≤ T₁` with counts `N₀`, `N₁`, the number of ticks between them is within two
periods of the elapsed time: `|(N₁ − N₀) · 2π/R − (T₁ − T₀)| ≤ 4π/R`
(`IsSwing.abs_tickTime_sub_sub_le`).

**The count at the position write.** In the exact instance of #360 (one momentum mode, both
profiles `trainF`, the fibres `θ₂ = ψ₂ = 0`, `g₂ > 0`) the site readout's history is a write of
`true` begun at the flow time `τ₀ = (M+1)/(12 g₂)` and complete at `τ₁ = (M+1)/(6 g₂)`. Along the
same orbit the clock's pointer is a swing at the level splitting `R` on every horizon. So:

* the tick history has a count `N₁` at `τ₁`, and `N₁ · 2π/R` is within one tick period of `τ₁`;
* it has a count `N₀` at `τ₀`, and the write interval measured in ticks,
  `(N₁ − N₀) · 2π/R`, is within two tick periods of `τ₁ − τ₀ = (M+1)/(12 g₂)`

(`clockSite_count_at_write_train`). Both counts and the write are read along the one orbit of
`clockSiteFlow` from the one start state.

**An instant fixed by the record.** The write interval of an `IsRecordWrite` is not unique for a
history. The history does fix one instant: the site readout is `true` exactly after the flow
time `t* = (M+1)/(8 g₂)`, up to `3 (M+1)/(8 g₂)` (`echoSiteShown_clockSiteFlow_train_iff`). The
tick history has a count `N` at `t*`, with `N · 2π/R` within one tick period of `t*`
(`clockSite_count_at_display_train`).

## Exact scope

* **The count is taken at a flow time.** "The count at the write" is the count of the tick
  history up to the flow time at which the site readout's write is complete. The two histories
  are compared at equal values of the flow parameter (UA-7). Nothing in the arena compares
  them: no register for the count is built on this arena, and no register is stamped by the
  write. On the one-pointer clock arena no real function of the state holds the count (#358,
  `not_ae_count_advances_clockPointerFlow`); that statement is not restated for `clockSiteFlow`.
* **Within one tick.** The count fixes the write's flow time up to one period `2π/R`, and an
  interval up to two. It is a clock of finite resolution, and the bound is not improved here.
* **The instance of #360.** One momentum mode on the fibres where both profiles vanish, a null
  set, where the device moves freely and the position record does not single out its site.
  Elsewhere the swing is a hypothesis; the count bound then holds for any swing
  (`IsSwing.exists_tickCount_abs_sub_le`), with the error of #360 inside the swing.
* **Ticks are not held.** Each tick record is erased within its turn (#358). The count at `τ₁`
  is a property of the tick history on `[0, τ₁]`, not of the arena's state at `τ₁`.
* **The clock is at rest in the count's statement.** `R` is the level splitting of the mode.
  Its relation to the rest splitting is #357's dilation clause and is not used here.
* **All times are flow times** (UA-7).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-12, UA-13, UO-14 (c), UO-16, UD-92); `RecordLayer/UnifiedDiracClockTicks.lean` (`IsSwing`,
`IsTickCount`, `IsSwing.exists_tickCount`, `IsSwing.abs_tickCount_sub_le`);
`RecordLayer/UnifiedClockSiteRecords.lean` (`isSwing_clockSiteFlow_train`,
`isRecordWrite_clockSiteFlow_site_train`, `clockSiteTrainStart`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The count at a time -/

section Count

variable {X : Type*} {rest disp : Set X} {γ : ℝ → X}

/-- ★ **A swing has a count at every time, within one turn of the phase.** -/
theorem IsSwing.exists_tickCount_abs_sub_le {R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    (hT : 0 ≤ T) :
    ∃ N : ℕ, IsTickCount rest disp γ T N ∧ |(N : ℝ) * (2 * Real.pi) - R * T| ≤ 2 * Real.pi := by
  obtain ⟨N, hN⟩ := h.exists_tickCount hT
  exact ⟨N, hN, h.abs_tickCount_sub_le hT hN⟩

/-- ★★ **The count times the period is within one period of the time.** -/
theorem IsSwing.abs_tickTime_sub_le {R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    (hT : 0 ≤ T) {N : ℕ} (hN : IsTickCount rest disp γ T N) :
    |(N : ℝ) * (2 * Real.pi / R) - T| ≤ 2 * Real.pi / R := by
  have hR := h.rate_pos
  have key := h.abs_tickCount_sub_le hT hN
  have e : (N : ℝ) * (2 * Real.pi / R) - T = ((N : ℝ) * (2 * Real.pi) - R * T) / R := by
    field_simp
  rw [e, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right key hR.le

/-- ★★ **The ticks between two times are within two periods of the elapsed time.** -/
theorem IsSwing.abs_tickTime_sub_sub_le {R c d c' d' T₀ T₁ : ℝ}
    (h₀ : IsSwing rest disp γ R c d T₀) (h₁ : IsSwing rest disp γ R c' d' T₁) (hT₀ : 0 ≤ T₀)
    (hT₁ : 0 ≤ T₁) {N₀ N₁ : ℕ} (hN₀ : IsTickCount rest disp γ T₀ N₀)
    (hN₁ : IsTickCount rest disp γ T₁ N₁) :
    |((N₁ : ℝ) - N₀) * (2 * Real.pi / R) - (T₁ - T₀)| ≤ 4 * Real.pi / R := by
  have k₀ := abs_le.1 (h₀.abs_tickTime_sub_le hT₀ hN₀)
  have k₁ := abs_le.1 (h₁.abs_tickTime_sub_le hT₁ hN₁)
  have e : 4 * Real.pi / R = 2 * Real.pi / R + 2 * Real.pi / R := by ring
  rw [abs_le, e]
  constructor <;> nlinarith [k₀.1, k₀.2, k₁.1, k₁.2]

end Count

/-! ### The count at the position write -/

section Train

variable {M : ℕ}

/-- ★★★ **The clock's count at the position write.** In the exact instance of #360, along the
one orbit of `clockSiteFlow` from `clockSiteTrainStart`: the site readout's history is a write of
`true` begun at `τ₀ = (M+1)/(12 g₂)` and complete at `τ₁ = (M+1)/(6 g₂)`; the tick history has a
count `N₀` at `τ₀` and a count `N₁` at `τ₁`; `N₁ · 2π/R` is within one tick period of `τ₁`; and
the write interval in ticks, `(N₁ − N₀) · 2π/R`, is within two tick periods of `τ₁ − τ₀`. The
counts are taken at flow times (UA-7), and no register for them is built on this arena. -/
theorem clockSite_count_at_write_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (k : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g₁ : ℝ}
    (hg : g₁ = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re)) {g₂ : ℝ}
    (hg₂ : 0 < g₂) :
    IsRecordWrite
        (fun t => echoSiteShown (4 * M + 3)
          (clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
            contDiff_trainF t (clockSiteTrainStart J h0 (h0.trans h01) m hβ R)))
        0 (((M : ℝ) + 1) / (12 * g₂)) (((M : ℝ) + 1) / (6 * g₂)) (((M : ℝ) + 1) / (6 * g₂))
        true
      ∧ ∃ N₀ N₁ : ℕ,
        IsTickCount (echoTickReady M) (echoTickDisplay M)
            (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic
              contDiff_trainF contDiff_trainF t
              (clockSiteTrainStart J h0 (h0.trans h01) m hβ R))
            (((M : ℝ) + 1) / (12 * g₂)) N₀
          ∧ IsTickCount (echoTickReady M) (echoTickDisplay M)
            (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic
              contDiff_trainF contDiff_trainF t
              (clockSiteTrainStart J h0 (h0.trans h01) m hβ R))
            (((M : ℝ) + 1) / (6 * g₂)) N₁
          ∧ |(N₁ : ℝ) * (2 * Real.pi / R) - ((M : ℝ) + 1) / (6 * g₂)| ≤ 2 * Real.pi / R
          ∧ |((N₁ : ℝ) - N₀) * (2 * Real.pi / R)
              - (((M : ℝ) + 1) / (6 * g₂) - ((M : ℝ) + 1) / (12 * g₂))| ≤ 4 * Real.pi / R := by
  have hT₀ : (0 : ℝ) ≤ ((M : ℝ) + 1) / (12 * g₂) := by positivity
  have hT₁ : (0 : ℝ) ≤ ((M : ℝ) + 1) / (6 * g₂) := by positivity
  have s₀ := isSwing_clockSiteFlow_train J h0 h01 h10 k m hβ hRe hg g₂
    (((M : ℝ) + 1) / (12 * g₂))
  have s₁ := isSwing_clockSiteFlow_train J h0 h01 h10 k m hβ hRe hg g₂
    (((M : ℝ) + 1) / (6 * g₂))
  obtain ⟨N₀, hN₀⟩ := s₀.exists_tickCount hT₀
  obtain ⟨N₁, hN₁⟩ := s₁.exists_tickCount hT₁
  exact ⟨isRecordWrite_clockSiteFlow_site_train J h0 (h0.trans h01) k m hβ R g₁ hg₂,
    N₀, N₁, hN₀, hN₁, s₁.abs_tickTime_sub_le hT₁ hN₁,
    s₀.abs_tickTime_sub_sub_le s₁ hT₀ hT₁ hN₀ hN₁⟩

/-- ★★ **The instant the site readout switches.** In the exact instance of #360 the site
readout along the orbit is `true` exactly after the flow time `(M+1)/(8 g₂)`, up to
`3 (M+1)/(8 g₂)`. So the history itself fixes an instant: the one at which it turns to `true`. -/
theorem echoSiteShown_clockSiteFlow_train_iff (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁)
    (k : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) (R g₁ : ℝ) {g₂ : ℝ} (hg₂ : 0 < g₂)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 * ((M : ℝ) + 1) / (8 * g₂)) :
    echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
          contDiff_trainF t (clockSiteTrainStart J h0 h1 m hβ R)) = true
      ↔ ((M : ℝ) + 1) / (8 * g₂) < t := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hc : 0 < 2 * g₂ / ((M : ℝ) + 1) := by positivity
  have e₁ : ((M : ℝ) + 1) / (8 * g₂) = 1 / 4 / (2 * g₂ / ((M : ℝ) + 1)) := by
    field_simp
    ring
  have e₃ : 3 * ((M : ℝ) + 1) / (8 * g₂) = 3 / 4 / (2 * g₂ / ((M : ℝ) + 1)) := by
    field_simp
    ring
  rw [e₃, le_div_iff₀ hc] at ht
  rw [e₁, div_lt_iff₀ hc]
  have hshift : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic
      (0 : AddCircle (1 : ℝ)) (0 : AddCircle (1 : ℝ))
      (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
        (devicePacket_single_ne_zero h0 h1 m hβ _)) t = t * (2 * g₂ / ((M : ℝ) + 1)) := by
    rw [clockSiteShiftSnd_single J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic
      trainF_lift_zero trainF_lift_zero h0 h1 m hβ _ t, rateAt_trainF_zero]
    ring
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hnn : 0 ≤ t * (2 * g₂ / ((M : ℝ) + 1)) := mul_nonneg ht0 hc.le
  unfold clockSiteTrainStart
  rw [echoSiteShown_eq_true_iff]
  show (clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic contDiff_trainF
    contDiff_trainF t _).2 ∈ displayArc ↔ _
  rw [clockSiteFlow_site_pointer, hshift]
  have key := pshift_mem_displayArc_iff
    (q := (((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) : KTorus))
    (a := t * (2 * g₂ / ((M : ℝ) + 1)))
    (by show 0 < rep (((1 / 12 : ℝ) : CircleFibre)) + _; rw [hrep]; linarith)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ 5 / 6; rw [hrep]; linarith)
  rw [key]
  show 1 / 3 < rep (((1 / 12 : ℝ) : CircleFibre)) + _ ↔ _
  rw [hrep]
  constructor <;> intro h <;> linarith

/-- ★★★ **The clock's count at the instant the position readout switches.** In the exact
instance of #360, along the one orbit: the site readout turns to `true` at the flow time
`t* = (M+1)/(8 g₂)` (`echoSiteShown_clockSiteFlow_train_iff`), the tick history has a count `N`
at `t*`, and `N · 2π/R` is within one tick period of `t*`. The instant is fixed by the position
record's own history; the two histories are compared at that flow time (UA-7). -/
theorem clockSite_count_at_display_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (k : ZMod (M + 1)) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g₁ : ℝ}
    (hg : g₁ = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re)) {g₂ : ℝ}
    (hg₂ : 0 < g₂) :
    ∃ N : ℕ,
      IsTickCount (echoTickReady M) (echoTickDisplay M)
          (fun t => clockSiteFlow J μ₀ μ₁ g₁ g₂ k trainF_periodic trainF_periodic
            contDiff_trainF contDiff_trainF t
            (clockSiteTrainStart J h0 (h0.trans h01) m hβ R))
          (((M : ℝ) + 1) / (8 * g₂)) N
        ∧ |(N : ℝ) * (2 * Real.pi / R) - ((M : ℝ) + 1) / (8 * g₂)| ≤ 2 * Real.pi / R := by
  have hT : (0 : ℝ) ≤ ((M : ℝ) + 1) / (8 * g₂) := by positivity
  have s := isSwing_clockSiteFlow_train J h0 h01 h10 k m hβ hRe hg g₂
    (((M : ℝ) + 1) / (8 * g₂))
  obtain ⟨N, hN⟩ := s.exists_tickCount hT
  exact ⟨N, hN, s.abs_tickTime_sub_le hT hN⟩

end Train

end CSD.RecordLayer

end
