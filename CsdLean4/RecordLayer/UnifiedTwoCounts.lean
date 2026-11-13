/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.QuadCoupledFlow
public import CsdLean4.RecordLayer.UnifiedGateReturn

/-!
# Two counts in one run: the clock's own pointer beside the gated one

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #381 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #380. The arena
is assumption UA-17 with its amendment (e): the clock keeps a pointer of its own.

#380 showed that the gated pointer's swing comes back from an absence with an offset, and
gave no count across the absence. Here the composite carrier has a fourth pointer, coupled to
`1 ⊗ X`: the clock's level swap alone. On the fibres where neither the gated pointer nor this
one acts back, from a product ray, its displacement is exactly that of the pointer of #357
on the clock's own arena (an equality of real displacement functions, `clockPointerShift`,
across arenas), so it is the swing of #358 for every horizon, in the same run as the gated
pointer and the two region pointers. The clock's count and the gated count are then two counts
of one history.

* `isSwing_snd_of_abs_shift_sub_le` — the swing criterion of #358 for the last pointer of any
  arena with a last torus;
* `gateFreeFlow`, `quadMuL_map_gateFreeFlow`, `gateFreeFlow_fst` (**on a fibre where the
  fourth profile vanishes the first three pointers and the carrier move by `gateFlow`**),
  ★ `gateFreeFlow_snd_prodRay` (**from a product ray, where neither profile acts back, the
  fourth pointer advances by the displacement of a pointer coupled to the clock alone**);
* `gateFreeClockFlow`, `quadFreeReady`, `quadFreeDisplay`, `twoCountStart`,
  `gateFreeClockFlow_twoCount_fst`, `gateFreeClockFlow_twoCount_snd`;
* ★ `isSwing_free_twoCount` — **the clock's own pointer is a swing at the rate `R` for every
  horizon**, in the run that also carries the gated pointer;
* `hasTicks_le_succ_of_no_passage`, `exists_tickCount_of_bdd`, `exists_gate_tickCount`,
  `IsTickCount.le_succ_of_no_passage`;
* ★ `twoCounts_away` — **on the interval of #375 on which the far half's occupancy is at
  least `1 − 1/(2n)`, the clock's count advances with the flow time and the gated count by at
  most one**: for flow times `a ≤ b` of
  `[(3125π/3) n², (4375π/3) n²]` with `|g_c| (b − a)/n ≤ 1/6`, the difference of the two
  advances, times the period `2π/R`, is within `6π/R` of `b − a`.

## Exact scope

* **A record written on the return leg, with the clock's count at a flow time by which it is
  complete,** is in `RecordLayer/UnifiedRoundTrip.lean` (#382).
* **A sub-interval of the absence, between two flow times.** `a` and `b` are flow times inside
  the interval on which the messenger is in the far half. They are not a departure and a
  return, and no record marks them. Over the two transit windows the gated count is bounded
  only by #378, too weakly. So this is not a radar time: on a stretch of the absence the
  clock's count advances with the flow time and the gated count by at most one.
* **The time content is the clock's alone.**
  `|(N_b^f − N_a^f)·2π/R − (b − a)| ≤ 4π/R` holds for any two non-negative flow times (#366).
  The gated count contributes only that its advance is 0 or 1 on the stretch, which is why the
  difference is within three periods and not two. No hypothesis relates `2π/R` to `b − a`; the
  advances of all four counts may be zero. The clock's two counts exist
  (`IsSwing.exists_tickCount`); the gated ones by `exists_gate_tickCount`.
* **`g_c` is free here; only `g₀` is tuned.** The gated pointer is the swing of #377 only when
  `g_c` also has the tuned value, and that swing is not restated on this arena. For `g_c` far
  below the tuned value the gated pointer is not shown to tick at all, and the gated count may
  be zero throughout. With `g_c` tuned, `|g_c| (b − a)/n ≤ 1/6` allows a number of periods of
  order `n`. A calculation, not in Lean.
* **Not new on other arenas.** A clock pointer that swings at every horizon beside other
  pointers in one run is #369 (the same clock carrier with two site detectors) and #372 (the
  uncoupled product arena, with the same two-time bound). What is new here is the arena: the
  clock is a tensor factor of the composite carrier, in the run that also carries the pointer
  coupled to `P ⊗ X`.
* **A new pointer is an amendment of UA-17.** The fourth pointer, its coupling to `1 ⊗ g₀ X`
  and its profile are chosen. On this arena the clock again has a pointer of its own.
* **Only where neither clock pointer acts back, and only product starts.** Both profiles must
  vanish on the fibre; both sets of fibres and the product rays are null sets (calculations,
  not in Lean). The two region pointers are on a fine fibre of #375.
* **The counts are read at flow times** (UA-7). No degree of freedom holds either count, and
  no record reads one (UO-14 (b)). The ticks are `IsSwing`, `HasTicks` and `IsTickCount`
  statements about readout histories, not `ActualOccurrence`s.
* **Gated by an occupancy, not by a record.** As in #376.
* **One clock start.** The one-mode clock of #358, a quarter turn early.
* **No distance, no speed, no second observer.** Nothing here is evidence about Lorentz
  kinematics.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UA-15, UA-17, UO-14, UO-16, UD-113, UD-114, UD-115, UD-122 to UD-124);
`LF4/QuadCoupledFlow.lean` (`fourCoupledFlow`, `fourCoupledFlow_fst_of_lift_eq_zero`,
`fourCoupledFlow_snd_of_lift_eq_zero`, `quadMuL_map_fourCoupledFlow`);
`RecordLayer/UnifiedCompositeCarrier.lean` (#376: `gateFlow`, `gateFlow_prodRay`,
`gateClockFlow`); `RecordLayer/UnifiedGateTicks.lean` (#377: `gateTrainStart`,
`clockPointerShift_train`, `gateClock_no_tick_after`); `RecordLayer/UnifiedGateCount.lean` (#378:
`gateClock_hasTicks_le`); `RecordLayer/UnifiedGateReturn.lean` (#380: the obstruction);
`RecordLayer/UnifiedDiracClockTicks.lean` (#358: `IsSwing`, `HasTicks`, `IsTickCount`,
`isSwing_of_abs_shift_sub_le`); `RecordLayer/UnifiedClockTwoSites.lean` (#369:
`isSwing_clockTwoSiteFlow_train`); `RecordLayer/UnifiedClockMessenger.lean` (#372);
`RecordLayer/UnifiedCountAtWrite.lean` (`IsSwing.abs_tickTime_sub_sub_le`);
`RecordLayer/UnifiedClockSiteRecords.lean` (`IsSwing.preimage`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The swing criterion for a last pointer, and counts under a no-passage condition -/

/-- **The swing criterion of #358 for the last pointer of an arena with a last torus.** -/
theorem isSwing_snd_of_abs_shift_sub_le {Y : Type*} {γ : ℝ → Y × KTorus} {q : KTorus}
    {σ : ℝ → ℝ} {R A δ T : ℝ} (hR : 0 < R) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hγ : ∀ t, 0 ≤ t → t ≤ T → (γ t).2 = pshift (σ t) q)
    (hσ : ∀ t, 0 ≤ t → t ≤ T → |σ t - A * (1 - Real.cos (R * t))| ≤ δ)
    (h₁ : δ < rep q.1) (h₂ : rep q.1 + δ ≤ 1 / 6) (h₃ : 1 / 3 < rep q.1 + 2 * A - δ)
    (h₄ : rep q.1 + 2 * A + δ ≤ 5 / 6) :
    IsSwing {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc} γ R
      (1 - (1 / 3 - rep q.1 - δ) / A) (1 - (1 / 3 - rep q.1 + δ) / A) T := by
  obtain ⟨p₀⟩ : Nonempty (CPN (4 * 0 + 3 + 1)) := inferInstance
  exact IsSwing.preimage (π := fun x : Y × KTorus => ((p₀, x.2) : KSigma (4 * 0 + 3 + 1)))
    (isSwing_of_abs_shift_sub_le (M := 0) hR hA hδ (fun t ht0 htT => hγ t ht0 htT) hσ h₁ h₂
      h₃ h₄)

section Counts

variable {X : Type*} {rest disp : Set X} {γ : ℝ → X}

/-- **If no passage from the resting set to the displaying set lies inside `[s, T]`, the count
advances by at most one there.** A history without `N₀ + 1` ticks by `s` has at most `N₀ + 1`
ticks by `T`. -/
theorem hasTicks_le_succ_of_no_passage {s T : ℝ}
    (hno : ∀ a b, s ≤ a → a ≤ b → b ≤ T → γ a ∈ rest → γ b ∉ disp) {m N₀ : ℕ}
    (hm : HasTicks rest disp γ T m) (hN : ¬ HasTicks rest disp γ s (N₀ + 1)) :
    m ≤ N₀ + 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, b, h1, h2⟩ := hm
  have hb : ∀ j, j < m → ∀ i, i ≤ j → b i ≤ b j := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      rw [Nat.le_zero.1 hi]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with hlt' | hge
      · exact ((ih (by omega) i (by omega)).trans (h2 j hj).le).trans (h1 (j + 1) hj).2.1.le
      · rw [le_antisymm hi hge]
  have hbN : s < b N₀ := by
    by_contra hc
    rw [not_lt] at hc
    exact hN ⟨a, b, fun i hi =>
      ⟨(h1 i (by omega)).1, (h1 i (by omega)).2.1, (hb N₀ (by omega) i (by omega)).trans hc,
        (h1 i (by omega)).2.2.2.1, (h1 i (by omega)).2.2.2.2⟩, fun i hi => h2 i (by omega)⟩
  obtain ⟨_, hab, hbT, hr, hd⟩ := h1 (N₀ + 1) (by omega)
  have hsa : s ≤ a (N₀ + 1) := (hbN.trans (h2 N₀ (by omega))).le
  exact hno _ _ hsa hab.le hbT hr hd

/-- **A history whose number of ticks by `T` is bounded has a count at `T`.** -/
theorem exists_tickCount_of_bdd {T : ℝ} {B : ℕ}
    (hB : ∀ m, HasTicks rest disp γ T m → m ≤ B) : ∃ N, IsTickCount rest disp γ T N := by
  classical
  have hex : ∃ N, ¬ HasTicks rest disp γ T (N + 1) := ⟨B, fun h => by
    have := hB _ h
    omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    exact hasTicks_zero rest disp γ T
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_not] at hmin
    have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [e] at hmin

/-- A count does not decrease, and under the no-passage condition it advances by at most
one. -/
theorem IsTickCount.le_succ_of_no_passage {s T : ℝ} (hsT : s ≤ T)
    (hno : ∀ a b, s ≤ a → a ≤ b → b ≤ T → γ a ∈ rest → γ b ∉ disp) {Ns NT : ℕ}
    (hs : IsTickCount rest disp γ s Ns) (hT : IsTickCount rest disp γ T NT) :
    Ns ≤ NT ∧ NT ≤ Ns + 1 := by
  refine ⟨?_, hasTicks_le_succ_of_no_passage hno hT.1 hs.2⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hT.2 ((hs.1.mono_time hsT).mono_count (by omega))

end Counts

/-! ### The composite carrier with a fourth pointer coupled to the clock alone -/

section Composite

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {a b : ℕ}
  (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h k l : ℝ → ℝ}
  {A₀ B₁ B₂ P : Matrix ι ι ℂ} {C₀ X Y : Matrix κ κ ℂ}

/-- **The joint flow of a composite carrier with four pointers**: two coupled to the messenger
observables `B₁ ⊗ 1`, `B₂ ⊗ 1`, the third to the product `P ⊗ X`, and the fourth to the clock
observable `1 ⊗ Y` (UA-17, amended). -/
noncomputable def gateFreeFlow (A₀ B₁ B₂ P : Matrix ι ι ℂ) (C₀ X Y : Matrix κ κ ℂ)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ) :
    QuadSigma (a * (b + 1) + b) → QuadSigma (a * (b + 1) + b) :=
  fourCoupledFlow
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (compositeH A₀ C₀))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₁ ⊗ₖ (1 : Matrix κ κ ℂ)))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₂ ⊗ₖ (1 : Matrix κ κ ℂ)))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (P ⊗ₖ X))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) ((1 : Matrix ι ι ℂ) ⊗ₖ Y)) hf hh hk hl hc
    hch hck hcl t

omit [Fintype ι] [Fintype κ] in
/-- **The flow with the fourth pointer preserves `μ_FS ⊗ vol ⊗ vol ⊗ vol ⊗ vol`.** -/
theorem quadMuL_map_gateFreeFlow (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hP : P.IsHermitian) (hC : C₀.IsHermitian) (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (p₀ : CPN (a * (b + 1) + b + 1)) (t : ℝ) :
    Measure.map (gateFreeFlow e₁ e₂ A₀ B₁ B₂ P C₀ X Y hf hh hk hl hc hch hck hcl t)
        (quadMuL p₀) = quadMuL p₀ :=
  quadMuL_map_fourCoupledFlow ((compositeH_isHermitian hA hC).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian hB₁ Matrix.isHermitian_one).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian hB₂ Matrix.isHermitian_one).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian hP hX).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian Matrix.isHermitian_one hY).reindex (prodIdx e₁ e₂)) hf hh hk hl hc
    hch hck hcl p₀ t

omit [Fintype ι] [Fintype κ] in
/-- **On a fibre where the fourth profile vanishes, the carrier and the first three pointers
move by `gateFlow`.** -/
theorem gateFreeFlow_fst (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ)
    (x : TriSigma (a * (b + 1) + b)) {ξ : KTorus} (hz : hl.lift ξ.2 = 0) :
    (gateFreeFlow e₁ e₂ A₀ B₁ B₂ P C₀ X Y hf hh hk hl hc hch hck hcl t (x, ξ)).1
      = gateFlow e₁ e₂ A₀ B₁ B₂ P C₀ X hf hh hk hc hch hck t x :=
  fourCoupledFlow_fst_of_lift_eq_zero _ _ _ _ _ hf hh hk hl hc hch hck hcl t x hz

/-- ★ **From a product ray, where neither clock pointer acts back, the fourth pointer advances
by the displacement of a pointer coupled to the clock alone**: `−2 l'(ξ₂)` times the clock's
accumulated free reading of `Y`. -/
theorem gateFreeFlow_snd_prodRay (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hP : P.IsHermitian) (hC : C₀.IsHermitian) (hY : Y.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ) (p : GenArena ι) (q : GenArena κ)
    (θ ψ : KTorus) {χ ξ : KTorus} (hzk : hk.lift χ.2 = 0) (hz : hl.lift ξ.2 = 0) :
    (gateFreeFlow e₁ e₂ A₀ B₁ B₂ P C₀ X Y hf hh hk hl hc hch hck hcl t
        ((((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ), χ), ξ)).2
      = pshift (idxPointerShift hC hY hl ξ.2 q t) ξ := by
  have hint : ∀ u : ℝ, triRayEnergy
        (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) ((1 : Matrix ι ι ℂ) ⊗ₖ Y))
        (gateFlow e₁ e₂ A₀ B₁ B₂ P C₀ X hf hh hk hc hch hck u
          (((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ), χ))
      = -2 * arenaObs Y (arenaKick (idxFreeU hC u) q) := by
    intro u
    rw [gateFlow_prodRay e₁ e₂ hA hB₁ hB₂ hP hC hf hh hk hc hch hck u p q θ ψ hzk]
    show schrodingerHamiltonian _ (idxArenaEquiv (prodIdx e₁ e₂) _) = _
    rw [schrodingerHamiltonian_reindex, arenaObs_one_kronecker]
  have h := fourCoupledFlow_snd_of_lift_eq_zero
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (compositeH A₀ C₀))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₁ ⊗ₖ (1 : Matrix κ κ ℂ)))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₂ ⊗ₖ (1 : Matrix κ κ ℂ)))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (P ⊗ₖ X))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) ((1 : Matrix ι ι ℂ) ⊗ₖ Y)) hf hh hk hl hc
    hch hck hcl t (((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ), χ) hz
  rw [gateFreeFlow, h, idxPointerShift_of_lift_eq_zero hC hY hl hz q t]
  have hint' : ∀ u : ℝ, triRayEnergy
        (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) ((1 : Matrix ι ι ℂ) ⊗ₖ Y))
        (threeCoupledFlow
          (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (compositeH A₀ C₀))
          (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₁ ⊗ₖ (1 : Matrix κ κ ℂ)))
          (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₂ ⊗ₖ (1 : Matrix κ κ ℂ)))
          (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (P ⊗ₖ X)) hf hh hk hc hch hck u
          (((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ), χ))
      = -2 * arenaObs Y (arenaKick (idxFreeU hC u) q) := hint
  simp only [hint']
  rw [intervalIntegral.integral_const_mul, pshift]
  congr 2
  ring_nf

end Composite

/-! ### The messenger, the clock, the gated pointer and the clock's own pointer -/

section Clock

variable {M Mc : ℕ} {f h k l : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (Jc μ₀ μ₁ gc g₀ : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
  (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)

variable (Mc) in
/-- **The joint flow of the messenger-and-clock composite with four pointers**: the flow
`gateClockFlow` of #376 with one more pointer, coupled to the clock's level swap alone with the
strength `g₀`. The energy has the further term `− 2 g₀ l(ξ₂)⟨1 ⊗ X⟩`. -/
noncomputable def gateFreeClockFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ) :
    QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      → QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  gateFreeFlow (diracIdx M) (clockIdx Mc) (diracHam J μ) ((g₁ : ℂ) • regionProj A)
    ((g₂ : ℂ) • regionProj B) (regionProj A) (deviceHam Jc μ₀ μ₁) (clockB Mc gc)
    (clockB Mc g₀) hf hh hk hl hc hch hck hcl t

/-- The clock's own pointer's ready region on the four-pointer arena. Apparatus input. -/
noncomputable def quadFreeReady (N : ℕ) : Set (QuadSigma N) := {x | x.2 ∈ readyArc 2}

/-- The clock's own pointer's displayed region on the four-pointer arena. Apparatus input. -/
noncomputable def quadFreeDisplay (N : ℕ) : Set (QuadSigma N) := {x | x.2 ∈ displayArc}

end Clock

section Run

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
  (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ}
  (hβ : β m ≠ 0) {R : ℝ}

/-- **The start of the two-count run**: the start of #377 with the clock's own pointer at the
angle `1/12` on the fibre `ξ₂ = 0`. -/
noncomputable def twoCountStart (R : ℝ) (θ ψ : KTorus) :
    QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ,
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

/-- Along the two-count run the carrier and the first three pointers move by `gateClockFlow`
from the start of #377. -/
theorem gateFreeClockFlow_twoCount_fst (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (gc g₀ : ℝ) (θ ψ : KTorus) (t : ℝ) :
    (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
        μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
        contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1
      = gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
          μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
          (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ) :=
  gateFreeFlow_fst (diracIdx M) (clockIdx Mc) hf hh trainF_periodic trainF_periodic hc hch
    contDiff_trainF contDiff_trainF t _ trainF_lift_zero

/-- Along the two-count run the clock's own pointer is its start turned by the displacement of
the pointer of #357 on the clock's own arena. -/
theorem gateFreeClockFlow_twoCount_snd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (gc g₀ : ℝ) (θ ψ : KTorus) (t : ℝ) :
    (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
        μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
        contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).2
      = pshift (clockPointerShift Jc μ₀ μ₁ g₀ trainF_periodic (0 : AddCircle (1 : ℝ))
          (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
            (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t)
        ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) := by
  rw [← idxPointerShift_clock]
  exact gateFreeFlow_snd_prodRay (diracIdx M) (clockIdx Mc) (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (regionProj_isHermitian _) (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian g₀) hf hh
    trainF_periodic trainF_periodic hc hch contDiff_trainF contDiff_trainF t _ _ θ ψ
    (χ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))
    (ξ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) trainF_lift_zero
    trainF_lift_zero

variable (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))

include h10 hRe hg in
/-- ★ **The clock's own pointer is a swing at the rate `R`, for every horizon, in the run that
also carries the gated pointer.** From `twoCountStart` (both clock pointers' profiles `trainF`
on the fibre `0`, a product ray), for every strength `g_c` of the gated pointer and every pair
of region pointers: the history of `gateFreeClockFlow`, read through the fourth pointer's
arcs, rests only where `cos R t ≥ 0` (and at every whole turn) and displays exactly where
`cos R t < 0`. -/
theorem isSwing_free_twoCount (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc : ℝ)
    (θ ψ : KTorus) (T : ℝ) :
    IsSwing (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ))
      R 0 0 T := by
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hsw := isSwing_snd_of_abs_shift_sub_le (A := 1 / 4) (δ := 0) (T := T) hR (by norm_num)
    le_rfl
    (fun t _ _ => gateFreeClockFlow_twoCount_snd (R := R) g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc
      hch gc g₀ θ ψ t)
    (fun t ht0 _ => by
      rw [clockPointerShift_train Jc h0 h01 h10 m hβ hRe hg ht0, sub_self, abs_zero])
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)); rw [hrep]; norm_num)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ _; rw [hrep]; norm_num)
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)) + _ - _; rw [hrep]; norm_num)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ + _ ≤ _; rw [hrep]; norm_num)
  have e₁ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) - 0) / (1 / 4) = 0 := by
    rw [hrep]
    norm_num
  have e₂ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) + 0) / (1 / 4) = 0 := by
    rw [hrep]
    norm_num
  rw [e₁, e₂] at hsw
  exact hsw

/-- **The gated pointer has a count at every flow time of the two-count run.** -/
theorem exists_gate_tickCount (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc g₀ : ℝ)
    (θ ψ : KTorus) {T : ℝ} (hT : 0 ≤ T) :
    ∃ N, IsTickCount
      (Prod.fst ⁻¹' triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (Prod.fst ⁻¹' triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) T N := by
  obtain ⟨B, hB⟩ := exists_nat_ge (6 * |trainF_periodic.deriv_periodic.lift
    (0 : AddCircle (1 : ℝ))| * |gc| * (T - 0) + 3 / 2)
  refine exists_tickCount_of_bdd (B := B) fun k hk => ?_
  have hk' : HasTicks (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)) T k := by
    obtain ⟨a, b, h1, h2⟩ := hk
    refine ⟨a, b, fun i hi => ?_, h2⟩
    obtain ⟨ha, hab, hb, hr, hd⟩ := h1 i hi
    have e := fun t : ℝ => gateFreeClockFlow_twoCount_fst (Mc := Mc) (R := R) g₁ g₂ hf hh hn hL
      Jc h0 h01 m hβ hc hch gc g₀ θ ψ t
    refine ⟨ha, hab, hb, ?_, ?_⟩
    · show gateClockFlow Mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a i) _ ∈ _
      rw [← e (a i)]
      exact hr
    · show gateClockFlow Mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b i) _ ∈ _
      rw [← e (b i)]
      exact hd
  have hno : ¬ HasTicks (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)) 0 (0 + 1) := by
    rintro ⟨a, b, h1, -⟩
    obtain ⟨ha, hab, hb, -, -⟩ := h1 0 (by omega)
    linarith
  have key := gateClock_hasTicks_le (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) θ ψ
    (χ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) trainF_lift_zero hT hk'
    hno
  have hc0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
  rw [hc0, zero_add] at key
  exact_mod_cast key.trans hB

include h10 hRe hg in
/-- ★ **Two counts on a stretch of the absence.** From `twoCountStart`, on a fine fibre of the
two region pointers, for flow times `a ≤ b` of `[(3125π/3) n², (4375π/3) n²]` with
`|g_c| (b − a)/n ≤ 1/6`: for the counts `N_a^f`, `N_b^f` of the clock's own pointer and
`N_a^g`, `N_b^g` of the gated pointer at `a` and `b`, the gated count advances by at most one,
and the difference of the two advances times the period `2π/R` is within `6π/R` of
`b − a`. -/
theorem twoCounts_away (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc : ℝ) {θ ψ : KTorus}
    (hx : (θ.2, ψ.2) ∈ fineFibres g₁ g₂ hf hh n) {a b : ℝ}
    (ha : 3125 * Real.pi / 3 * (n : ℝ) ^ 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 4375 * Real.pi / 3 * (n : ℝ) ^ 2) (hsmall : |gc| * (b - a) / n ≤ 1 / 6)
    {Nfa Nfb Nga Ngb : ℕ}
    (hfa : IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) a Nfa)
    (hfb : IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) b Nfb)
    (hga : IsTickCount
      (Prod.fst ⁻¹' triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (Prod.fst ⁻¹' triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) a Nga)
    (hgb : IsTickCount
      (Prod.fst ⁻¹' triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (Prod.fst ⁻¹' triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) b Ngb) :
    (Nga ≤ Ngb ∧ Ngb ≤ Nga + 1)
      ∧ |(((Nfb : ℝ) - Nfa) - ((Ngb : ℝ) - Nga)) * (2 * Real.pi / R) - (b - a)|
          ≤ 6 * Real.pi / R := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hb0 : 0 ≤ b := ha0.trans hab
  -- the clock's own count
  have hfree := (isSwing_free_twoCount g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch gc θ
    ψ a).abs_tickTime_sub_sub_le
    (isSwing_free_twoCount g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch gc θ ψ b) ha0
    hb0 hfa hfb
  -- the gated count
  have hno : ∀ a' b', a ≤ a' → a' ≤ b' → b' ≤ b →
      gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
          Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
          contDiff_trainF a' (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)
        ∈ Prod.fst ⁻¹' triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) →
      gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
          Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
          contDiff_trainF b' (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)
        ∉ Prod.fst ⁻¹' triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) := by
    intro a' b' haa hab' hbb hready hdisp
    have hr' : (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF a' (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1
        ∈ triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) := hready
    have hd' : (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
        contDiff_trainF contDiff_trainF b' (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1
        ∈ triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) := hdisp
    rw [gateFreeClockFlow_twoCount_fst g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc g₀ θ ψ]
      at hr' hd'
    have hs' : |trainF_periodic.deriv_periodic.lift (0 : AddCircle (1 : ℝ))| * |gc|
        * (b' - a') / n ≤ 1 / 6 := by
      rw [trainF_deriv_lift_zero, abs_neg, abs_one, one_mul]
      refine le_trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg gc)) hr.le) hsmall
    exact gateClock_no_tick_after g₁ g₂ Jc μ₀ μ₁ gc hf hh trainF_periodic hn hL hc hch
      contDiff_trainF hx (χ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))
      trainF_lift_zero
      (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
        (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) (ha.trans haa) hab'
      (hbb.trans hb) hs' hr' hd'
  have hgate := IsTickCount.le_succ_of_no_passage hab hno hga hgb
  refine ⟨hgate, ?_⟩
  obtain ⟨hf1, hf2⟩ := abs_le.1 hfree
  have hg1 : (0 : ℝ) ≤ (Ngb : ℝ) - Nga := by
    have : (Nga : ℝ) ≤ Ngb := by exact_mod_cast hgate.1
    linarith
  have hg2 : (Ngb : ℝ) - Nga ≤ 1 := by
    have : (Ngb : ℝ) ≤ (Nga : ℝ) + 1 := by exact_mod_cast hgate.2
    linarith
  have hp : 0 < 2 * Real.pi / R := by positivity
  have e4 : 4 * Real.pi / R = 2 * (2 * Real.pi / R) := by ring
  have e6 : 6 * Real.pi / R = 3 * (2 * Real.pi / R) := by ring
  rw [e4] at hf1 hf2
  rw [abs_le, e6]
  constructor <;> nlinarith

end Run

end CSD.RecordLayer

end
