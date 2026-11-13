/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateTicks

/-!
# The gated count: as many ticks before departure as wanted, and a bound at any later time

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #378 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainders (a) and (b) of #377.

#377 showed that the gated pointer of the composite carrier (UA-17) is a swing while the
messenger is in the near half, under a hypothesis that bounds the clock's rate from above, and
left two things open: whether that hypothesis is compatible with any tick at all, and any
statement about the count at a later time.

* `pshift_notMem_readyArc_of_mem_displayArc`;
* ★ `hasTicks_le_of_travel` — **ticks need travel**: for a history whose third pointer is a
  start turned by `D t`, with `|D b − D a| ≤ W b − W a` on `[s, T]`, the number of ticks by `T`
  is at most the count at `s` plus `3 (W T − W s) + 3/2`;
* ★ `gateClock_hasTicks_le` — **on the composite carrier the gated count at `T` is at most
  the count at `s` plus `6|k'(χ₂)||g_c| (T − s) + 3/2`**, from any product ray on a fibre
  where the gated pointer's profile vanishes;
* `gateClock_coupling_le` — in the exact instance of #358 the strength satisfies
  `8 κ g_c ≤ R` with `κ = 1 − ((μ₁ − μ₀)/μ₀)²`, and `g_c > 0`;
* ★ `gateClock_hasTicks_before` — **as many ticks before departure as wanted**: for every
  `K`, every index `n` with `3πK < κ n` and `6K ≤ 625 n² R`, the gated pointer has `K` ticks
  by the flow time `2πK/R`, which is at most `(625π/3) n²`.

## Exact scope

* **The arena and its limits are those of #376 (UA-17)**, and for
  `gateClock_hasTicks_before` those of #377: a null set of fibres for the gated pointer and a
  product start (null sets by calculations not in Lean), the fine fibres of #375, the
  one-point clock start of #358.
* **`gateClock_hasTicks_before` removes the vacuity left open in #377.** Its two hypotheses
  are lower bounds on `n` for a given clock and a given `K`, so they hold for every large `n`.
  The system grows with `n` as in #375.
* **At least `K`, early.** `HasTicks` is a lower bound, not a count. `K < κ n/(3π)`, so more
  ticks need a larger ring. For a given clock the flow time `2πK/R` is a vanishing fraction of
  `[0, (625π/3) n²]` as `n` grows, and no theorem gives the count at `(625π/3) n²` unless
  `|g_c| n < 1/(2500π)` (#377).
* **The bound at a later time is weak.** It is the bound for a pointer moving at its largest
  rate `2|k'||g_c|` the whole time. With `8 κ g_c ≤ R` and `|k'| = 1` it is at most
  `3R(T − s)/(4κ) + 3/2` ticks, where the clock itself makes about `R(T − s)/(2π)`; that it
  is not much smaller needs a lower bound on `g_c`, which is a calculation and not in Lean. Over the
  transit window of #375, which is four times as long as the interval before it, it does not
  give the count at arrival to within the count at departure. A sharper statement needs the
  transit window narrowed for the coupled carrier (Remainder (a) of #375).
* **No lower bound beyond monotonicity.** The count does not decrease (`HasTicks.mono_time`).
* **"The count stops at departure" is still not proved.** No degree of freedom holds the count
  (UO-14 (b)); the gate is an occupancy, not a record. The ticks are `HasTicks` passages of
  the readout history, not `ActualOccurrence`s.
* **Flow times throughout (UA-7).**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UA-15, UA-17, UO-14, UO-16, UD-113 to UD-116); `RecordLayer/UnifiedGateTicks.lean`
(#377: `isSwing_gateClock_before`, `pshift_notMem_displayArc_of_mem_readyArc`, `gateTrainStart`);
`RecordLayer/UnifiedCompositeCarrier.lean` (#376: `gateClockFlow_apply`,
`abs_gateShift_sub_le_of_le`); `RecordLayer/UnifiedDiracClockTicks.lean` (#358: `HasTicks`,
`IsSwing.hasTicks`, `le_deviceCoherence_devicePacket_zero_re`);
`RecordLayer/UnifiedFineTransit.lean` (#375).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Ticks need travel -/

/-- A pointer in the displayed arc, turned by at most a sixth of a turn either way, is not in
the ready arc. -/
theorem pshift_notMem_readyArc_of_mem_displayArc {q : KTorus} {d : ℝ} (hd : |d| ≤ 1 / 6)
    (hq : q ∈ displayArc) : pshift d q ∉ readyArc 2 := fun hr => by
  have h := pshift_notMem_displayArc_of_mem_readyArc (d := -d) (by rwa [abs_neg]) hr
  rw [pshift_add, neg_add_cancel, pshift_zero] at h
  exact h hq

/-- ★ **Ticks need travel.** For a history on a three-pointer arena whose third pointer pair
is a start `q` turned by `D t` on `[s, T]`, with `|D b − D a| ≤ W b − W a` there: if the
history does not have `N₀ + 1` ticks by `s`, it has at most `N₀ + 3 (W T − W s) + 3/2` ticks by
`T`. Each tick after the first one that ends after `s` needs a passage from the ready arc to
the displayed arc and one back, a sixth of a turn each. -/
theorem hasTicks_le_of_travel {N : ℕ} {γ : ℝ → TriSigma N} {q : KTorus} {D W : ℝ → ℝ}
    {s T : ℝ} (hsT : s ≤ T) (hγ : ∀ t, s ≤ t → t ≤ T → (γ t).2 = pshift (D t) q)
    (hW : ∀ a b, s ≤ a → a ≤ b → b ≤ T → |D b - D a| ≤ W b - W a) {m N₀ : ℕ}
    (hm : HasTicks (triThdReady N) (triThdDisplay N) γ T m)
    (hN : ¬ HasTicks (triThdReady N) (triThdDisplay N) γ s (N₀ + 1)) :
    (m : ℝ) ≤ N₀ + 3 * (W T - W s) + 3 / 2 := by
  obtain ⟨a, b, h1, h2⟩ := hm
  have hmono : ∀ x y, s ≤ x → x ≤ y → y ≤ T → W x ≤ W y := fun x y hx hxy hy => by
    have h := hW x y hx hxy hy
    linarith [abs_nonneg (D y - D x)]
  have hWsT := hmono s T le_rfl hsT le_rfl
  by_cases hle : m ≤ N₀ + 1
  · have hc : (m : ℝ) ≤ (N₀ : ℝ) + 1 := by exact_mod_cast hle
    linarith
  obtain ⟨d, rfl⟩ : ∃ d, m = N₀ + 2 + d := ⟨m - N₀ - 2, by omega⟩
  -- the ends of the ticks increase
  have hb : ∀ j, j < N₀ + 2 + d → ∀ i, i ≤ j → b i ≤ b j := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      rw [Nat.le_zero.1 hi]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact ((ih (by omega) i (by omega)).trans (h2 j hj).le).trans (h1 (j + 1) hj).2.1.le
      · rw [le_antisymm hi hge]
  -- the tick `N₀` ends after `s`
  have hbN : s < b N₀ := by
    by_contra hc
    rw [not_lt] at hc
    exact hN ⟨a, b, fun i hi =>
      ⟨(h1 i (by omega)).1, (h1 i (by omega)).2.1, (hb N₀ (by omega) i (by omega)).trans hc,
        (h1 i (by omega)).2.2.2.1, (h1 i (by omega)).2.2.2.2⟩, fun i hi => h2 i (by omega)⟩
  -- the later ticks begin after `s`
  have hsa : ∀ e, N₀ + 1 + e < N₀ + 2 + d → s ≤ a (N₀ + 1 + e) := by
    intro e he
    have h3 := h2 (N₀ + e) (by omega)
    have e1 : N₀ + e + 1 = N₀ + 1 + e := by omega
    rw [e1] at h3
    exact (hbN.le.trans (hb (N₀ + e) (by omega) N₀ (by omega))).trans h3.le
  -- a passage from ready to displayed
  have hup : ∀ i, i < N₀ + 2 + d → s ≤ a i → 1 / 6 < W (b i) - W (a i) := by
    intro i hi hs
    obtain ⟨_, hab, hbT, hr, hd⟩ := h1 i hi
    by_contra hc
    rw [not_lt] at hc
    have habs := (hW (a i) (b i) hs hab.le hbT).trans hc
    have hr' : pshift (D (a i)) q ∈ readyArc 2 := by
      rw [← hγ (a i) hs (hab.le.trans hbT)]
      exact hr
    have hnd := pshift_notMem_displayArc_of_mem_readyArc habs hr'
    rw [pshift_add, sub_add_cancel] at hnd
    apply hnd
    rw [← hγ (b i) (hs.trans hab.le) hbT]
    exact hd
  -- a passage from displayed back to ready
  have hdown : ∀ i, i + 1 < N₀ + 2 + d → s ≤ a i → 1 / 6 < W (a (i + 1)) - W (b i) := by
    intro i hi hs
    obtain ⟨_, hab, _, _, hd⟩ := h1 i (by omega)
    obtain ⟨_, hab', hbT', hr', _⟩ := h1 (i + 1) hi
    have hba := h2 i hi
    have haT : a (i + 1) ≤ T := hab'.le.trans hbT'
    have hsb : s ≤ b i := hs.trans hab.le
    by_contra hc
    rw [not_lt] at hc
    have habs := (hW (b i) (a (i + 1)) hsb hba.le haT).trans hc
    have hd' : pshift (D (b i)) q ∈ displayArc := by
      rw [← hγ (b i) hsb (hba.le.trans haT)]
      exact hd
    have hnr := pshift_notMem_readyArc_of_mem_displayArc habs hd'
    rw [pshift_add, sub_add_cancel] at hnr
    apply hnr
    rw [← hγ (a (i + 1)) (hsb.trans hba.le) haT]
    exact hr'
  -- the travel adds up
  have key : ∀ e, N₀ + 1 + e < N₀ + 2 + d →
      (2 * (e : ℝ) + 1) / 6 ≤ W (b (N₀ + 1 + e)) - W (a (N₀ + 1)) := by
    intro e
    induction e with
    | zero =>
      intro he
      have h := hup (N₀ + 1) (by omega) (hsa 0 (by omega))
      simp only [Nat.cast_zero, mul_zero, zero_add, Nat.add_zero] at h ⊢
      linarith
    | succ e ih =>
      intro he
      have h3 := ih (by omega)
      have h4 := hdown (N₀ + 1 + e) (by omega) (hsa e (by omega))
      have h5 := hup (N₀ + 1 + (e + 1)) he (hsa (e + 1) he)
      have e1 : N₀ + 1 + e + 1 = N₀ + 1 + (e + 1) := by omega
      rw [e1] at h4
      push_cast
      linarith
  have hk := key d (by omega)
  have h6 := hmono s (a (N₀ + 1)) le_rfl (hsa 0 (by omega))
    ((h1 (N₀ + 1) (by omega)).2.1.le.trans (h1 (N₀ + 1) (by omega)).2.2.1)
  have h7 := hmono (b (N₀ + 1 + d)) T
    ((hsa d (by omega)).trans (h1 (N₀ + 1 + d) (by omega)).2.1.le)
    (h1 (N₀ + 1 + d) (by omega)).2.2.1 le_rfl
  push_cast
  linarith

/-! ### The gated count at a later time -/

section Later

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (Jc μ₀ μ₁ gc : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
  (hk : Function.Periodic k 1)

/-- ★ **The gated count at a later time.** On the composite carrier, from any product ray, on
a fibre where the gated pointer's profile vanishes: if the gated pointer does not have
`N₀ + 1` ticks by the flow time `s`, it has at most `N₀ + 6|k'(χ₂)||g_c| (T − s) + 3/2` ticks
by `T ≥ s`. -/
theorem gateClock_hasTicks_le (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (p : GenArena (ZMod (M + 1) × Fin 2))
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) {χ : KTorus}
    (hz : hk.lift χ.2 = 0) {s T : ℝ} (hsT : s ≤ T) {m N₀ : ℕ}
    (hm : HasTicks (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateClockFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc)) (prodRay p q), θ), ψ), χ)) T m)
    (hN : ¬ HasTicks (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateClockFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc)) (prodRay p q), θ), ψ), χ)) s
      (N₀ + 1)) :
    (m : ℝ) ≤ N₀ + 6 * |hk.deriv_periodic.lift χ.2| * |gc| * (T - s) + 3 / 2 := by
  have key := hasTicks_le_of_travel (q := χ)
    (D := fun t => gateClockShift J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk θ.2 ψ.2 χ.2 p q t)
    (W := fun t => 2 * |hk.deriv_periodic.lift χ.2| * |gc| * t) hsT
    (fun t _ _ => by
      rw [gateClockFlow_apply J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t p q θ ψ hz])
    (fun a b _ hab _ => by
      have h := abs_gateShift_sub_le_of_le (diracHam_isHermitian J μ)
        (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B)
        (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk θ.2 ψ.2 χ.2 p q
        (fun r => arenaObs_regionProj_nonneg A r) (abs_nonneg gc) (norm_clockB_le gc) hab
        (η := 1) (fun u _ => arenaObs_regionProj_le_one A _)
      refine h.trans_eq ?_
      ring) hm hN
  refine key.trans_eq ?_
  ring

end Later

/-! ### As many ticks before departure as wanted -/

section Many

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
  (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ}
  (hβ : β m ≠ 0) {R : ℝ}
  (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {gc : ℝ}
  (hg : gc = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))

include h0 h01 h10 hβ hg in
/-- In the exact instance of #358 the strength is positive and at most `R/(8κ)`, with
`κ = 1 − ((μ₁ − μ₀)/μ₀)²`. -/
theorem gateClock_coupling_le (hR : 0 < R) :
    0 < gc ∧ gc * (8 * (1 - ((μ₁ - μ₀) / μ₀) ^ 2)) ≤ R := by
  have hC := deviceCoherence_single_re_pos (L := Mc + 1) (J := Jc) h0 h01.le h10 m hβ
  have hb : 0 < ‖β m‖ ^ 2 := by positivity
  have hw := le_deviceCoherence_devicePacket_zero_re (L := Mc + 1) (J := Jc) h0 h01.le
    (distinct_singleton m) β
  rw [Finset.sum_singleton] at hw
  have hgc : 0 < gc := by
    rw [hg]
    positivity
  have e : gc * (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re)
      = R * ‖β m‖ ^ 2 := by
    rw [hg]
    field_simp
  refine ⟨hgc, ?_⟩
  have h1 : gc * (8 * (1 - ((μ₁ - μ₀) / μ₀) ^ 2)) * ‖β m‖ ^ 2 ≤ R * ‖β m‖ ^ 2 := by
    rw [← e]
    have h2 := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 16 * gc)
    linarith
  exact le_of_mul_le_mul_right h1 hb

include h10 hRe hg in
/-- ★ **As many ticks before departure as wanted.** On the composite carrier, from
`gateTrainStart`, on a fine fibre of the two region pointers: for every `K` and every index
`n` with `3πK < κ n` and `6K ≤ 625 n² R`, where `κ = 1 − ((μ₁ − μ₀)/μ₀)²`, the gated pointer
has `K` ticks by the flow time `2πK/R`, and that time is at most `(625π/3) n²`. For a given
clock and a given `K` both hypotheses hold for every large `n`. -/
theorem gateClock_hasTicks_before (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) {θ ψ : KTorus}
    (hx : (θ.2, ψ.2) ∈ fineFibres g₁ g₂ hf hh n) (K : ℕ)
    (hκ : 3 * Real.pi * K < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) * n)
    (hRn : 6 * (K : ℝ) ≤ 625 * (n : ℝ) ^ 2 * R) :
    2 * Real.pi * K / R ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2
      ∧ HasTicks (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
        (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
        (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
          (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
          (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)) (2 * Real.pi * K / R) K := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  obtain ⟨hgc, hgR⟩ := gateClock_coupling_le Jc h0 h01 h10 m hβ hg hR
  have hT0 : 0 ≤ 2 * Real.pi * K / R := by positivity
  have hT : 2 * Real.pi * K / R ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hR]
    nlinarith [mul_le_mul_of_nonneg_left hRn hπ.le]
  have hδ : |gc| * (2 * Real.pi * K / R) / n < 1 / 12 := by
    rw [abs_of_pos hgc, div_lt_iff₀ hr]
    have e : gc * (2 * Real.pi * K / R) = gc * (2 * Real.pi * K) / R := by ring
    rw [e, div_lt_iff₀ hR]
    have h1 := mul_lt_mul_of_pos_left hκ (by positivity : (0 : ℝ) < 8 * gc)
    have h2 := mul_le_mul_of_nonneg_right hgR hr.le
    nlinarith
  refine ⟨hT, ?_⟩
  refine (isSwing_gateClock_before g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch hx hT0
    hT hδ).hasTicks ?_
  have e : R * (2 * Real.pi * K / R) = 2 * Real.pi * K := by field_simp
  rw [e]
  linarith

end Many

end CSD.RecordLayer

end
