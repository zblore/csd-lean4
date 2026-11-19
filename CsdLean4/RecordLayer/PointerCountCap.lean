/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TickCountBound
public import CsdLean4.RecordLayer.UnifiedRecordHistoryBridge
public import CsdLean4.RecordLayer.UnifiedCausalArrival
public import CsdLean4.RecordLayer.UnifiedRadarMacrostate

/-!
# The cap of a pointer's count, as a number

**Category:** 7-SigmaLayer. BACKLOG #439, fourth brick (Task 3 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (3); plan `specs/unified-records-spacetime-task-plans.md` §1).

`RecordLayer/TickCountBound.lean` bounds a count by `K T / d` for a history of speed `K`
between two sets at distance `d`. This module supplies `d` and `K` for a pointer of the
arena, so that the cap of the macroscopic projection is a number.

* ★★ `one_sixth_le_dist_of_mem_readyArc_of_mem_displayArc` — the ready arc and the
  displaying arc are at distance at least `1/6`;
* `dist_pshift_pshift_le`;
* ★★ `HasTicks.pointer_mul_le` — a pointer turned by a displacement that changes at rate at
  most `K` has `n/6 ≤ K T` for `n` ticks by `T`;
* `abs_freeShift_sub_le` — a pointer's displacement along a carrier's orbit changes at rate
  at most `2 |z| ‖G‖`;
* ★★★ `pentaCount_le` — **on the five-pointer arena, from every start and for every
  pointer, a count at `T` is at most `12 Z Γ T`**, `Z` a bound for the profiles' derivatives
  and `Γ` for the observables' norms;
* `abs_scaledTrainF_deriv_lift_le`;
* ★★★ `wallCount_le` — **for the radar's walled chain the count of every pointer at `T`, from
  every start, is at most `12 max(|g_A|, |g_B|) T`**;
* `exists_isTickCount_of_cap` — a capped history has a count;
* `exists_le_card_mul_measure_inter_preimage` — one value of a map into a finite type carries
  a share of a set's measure;
* ★★★ `TickReadout.exists_history_measure_ge` — for a finite family of `k` readings capped at
  `B` and any set `S` of starts, one record history's compatible region holds at least
  `1 / (B + 1)^k` of the measure of `S`;
* ★★★ `wall_exists_history_measure_ge` — the same for five readings of the walled chain, with
  `B ≥ 12 max(|g_A|, |g_B|) τ_j`.

## Honest scope

⚠️ **An upper bound from the speed, not the count.** It holds from every start, including
those that are in no radar history. It is far above the counts of the family's runs.

⚠️ **`T` is a flow time.**

⚠️ **Which history is not said.** `wall_exists_history_measure_ge` gives some five counts
at most `B`. It does not say they satisfy the comparisons of `RadarCountBounds`; for the start
set of `csd_radar_history_preparation` that takes the covering of that theorem, which is not
joined to this one here. The fraction `1 / (B + 1)^5` is a pigeonhole bound, not the size of
a cell.

References: `specs/BACKLOG.md` #439; `specs/unified-record-spacetime-plan.md` (UO-25, UD-223,
UD-228, UD-232); `specs/unified-records-spacetime-task-plans.md` (§1);
`RecordLayer/TickCountBound.lean` (`HasTicks.mul_le`); `RecordLayer/UnifiedFibreRun.lean`
(`pentaRun_fibre`); `RecordLayer/UnifiedRecordHistoryBridge.lean` (`pentaPointer`,
`wallReadout`, `wallDynamics`); `RecordLayer/UnifiedTriFibre.lean`
(`tri_gate_norms_le_one`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix Set
open scoped Matrix.Norms.L2Operator ContDiff Kronecker

namespace CSD.RecordLayer

/-! ### The two arcs and the pointer's speed -/

/-- ★★ **The ready arc and the displaying arc are at distance at least `1/6`.** -/
theorem one_sixth_le_dist_of_mem_readyArc_of_mem_displayArc {x y : KTorus}
    (hx : x ∈ readyArc 2) (hy : y ∈ displayArc) : 1 / 6 ≤ dist x y := by
  have hx' : rep x.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hx
  have hy' : rep y.1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) := hy
  rw [shearWidth_two] at hx' hy'
  rw [Prod.dist_eq]
  refine le_trans ?_ (le_max_left _ _)
  have hu1 : -(5 / 6) ≤ rep x.1 - rep y.1 := by linarith [hx'.1, hy'.2]
  have hu2 : rep x.1 - rep y.1 ≤ -(1 / 6) := by linarith [hx'.2, hy'.1]
  have hd : dist x.1 y.1 = |rep x.1 - rep y.1 - round (rep x.1 - rep y.1)| := by
    conv_lhs => rw [← coe_rep x.1, ← coe_rep y.1]
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact UnitAddCircle.norm_eq
  rw [hd]
  rcases le_or_gt 0 (round (rep x.1 - rep y.1)) with h | h
  · have h0 : (0 : ℝ) ≤ round (rep x.1 - rep y.1) := by exact_mod_cast h
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  · have h0 : (round (rep x.1 - rep y.1) : ℝ) ≤ -1 := by
      exact_mod_cast Int.le_sub_one_of_lt h
    exact le_trans (by linarith) (le_abs_self _)

/-- Two turns of one pointer are no further apart than the turns differ. -/
theorem dist_pshift_pshift_le (a b : ℝ) (q : KTorus) :
    dist (pshift a q) (pshift b q) ≤ |a - b| := by
  rw [Prod.dist_eq]
  refine max_le ?_ (by simp [pshift])
  change dist (q.1 + (a : AddCircle (1 : ℝ))) (q.1 + (b : AddCircle (1 : ℝ))) ≤ |a - b|
  rw [dist_add_left, dist_eq_norm, ← AddCircle.coe_sub]
  have h := round_le (a - b) 0
  rw [Int.cast_zero, sub_zero] at h
  exact (UnitAddCircle.norm_eq (x := a - b)).le.trans h

/-- ★★ **A pointer's ticks take time.** A pointer turned from `q` by a displacement `D` that
changes at rate at most `K` up to `T` has `n/6 ≤ K T` for `n` ticks by `T`. -/
theorem HasTicks.pointer_mul_le {γ : ℝ → KTorus} {q : KTorus} {D : ℝ → ℝ} {K T : ℝ} {n : ℕ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hγ : ∀ t, 0 ≤ t → t ≤ T → γ t = pshift (D t) q)
    (hD : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → |D s - D t| ≤ K * (t - s))
    (h : HasTicks (readyArc 2) displayArc γ T n) : (n : ℝ) * (1 / 6) ≤ K * T :=
  HasTicks.mul_le hK hT
    (fun s t hs hst ht => by
      rw [hγ s hs (hst.trans ht), hγ t (hs.trans hst) ht]
      exact (dist_pshift_pshift_le _ _ q).trans (hD s t hs hst ht))
    (fun _ hx _ hy => one_sixth_le_dist_of_mem_readyArc_of_mem_displayArc hx hy) h

section Shift

variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] {H : Matrix ν ν ℂ}

/-- A pointer's displacement along a carrier's orbit changes at rate at most `2 |z| ‖G‖`. -/
theorem abs_freeShift_sub_le (hH : H.IsHermitian) (G : Matrix ν ν ℂ) (z : ℝ) (p : GenArena ν)
    {s t : ℝ} (hst : s ≤ t) :
    |freeShift hH G z p s - freeShift hH G z p t| ≤ 2 * |z| * ‖G‖ * (t - s) := by
  unfold freeShift
  have hcont : Continuous fun u : ℝ => arenaObs G (arenaKick (idxFreeU hH u) p) :=
    (continuous_arenaObs G).comp ((continuous_idxFreeU hH).arenaKick continuous_const)
  rw [← mul_sub, intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable 0 s)
    (hcont.intervalIntegrable 0 t)]
  have key : ‖∫ u in t..s, arenaObs G (arenaKick (idxFreeU hH u) p)‖ ≤ ‖G‖ * |s - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => abs_arenaObs_le G _
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)] at key
  rw [abs_mul, abs_mul, abs_neg, abs_two]
  calc 2 * |z| * |∫ u in t..s, arenaObs G (arenaKick (idxFreeU hH u) p)|
      ≤ 2 * |z| * (‖G‖ * (t - s)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg zero_le_two (abs_nonneg _))
    _ = _ := by ring

end Shift

/-! ### A cap gives a count, and one cell carries a share of the measure -/

section Cells

open CSD.SigmaLayer

universe u w

/-- **A capped history has a count.** If every number of ticks by `T` is at most `B`, the
history has a count at `T`, and it is at most `B`. -/
theorem exists_isTickCount_of_cap {X : Type*} {rest disp : Set X} {γ : ℝ → X} {T : ℝ} {B : ℕ}
    (hcap : ∀ n, HasTicks rest disp γ T n → n ≤ B) :
    ∃ N, N ≤ B ∧ IsTickCount rest disp γ T N := by
  classical
  have hex : ∃ n, ¬ HasTicks rest disp γ T (n + 1) :=
    ⟨B, fun h => absurd (hcap _ h) (Nat.not_succ_le_self B)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun h =>
    absurd (hcap _ h) (Nat.not_succ_le_self B), ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    exact hasTicks_zero rest disp γ T
  · have hmin := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
    rw [not_not, Nat.sub_add_cancel hpos] at hmin
    exact hmin

/-- **One value of a map into a finite type carries a share of a set's measure.** No
measurability is needed. -/
theorem exists_le_card_mul_measure_inter_preimage {X F : Type*} [MeasurableSpace X]
    [Fintype F] [Nonempty F] (ν : MeasureTheory.Measure X) (m : X → F) (S : Set X) :
    ∃ v, ν S ≤ Fintype.card F * ν (S ∩ m ⁻¹' {v}) := by
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image Finset.univ (fun v => ν (S ∩ m ⁻¹' {v}))
    Finset.univ_nonempty
  refine ⟨v, ?_⟩
  have hcov : S ⊆ ⋃ w ∈ (Finset.univ : Finset F), S ∩ m ⁻¹' {w} := fun x hx => by
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_singleton_iff]
    exact ⟨m x, hx, rfl⟩
  calc ν S ≤ ν (⋃ w ∈ (Finset.univ : Finset F), S ∩ m ⁻¹' {w}) := MeasureTheory.measure_mono hcov
    _ ≤ ∑ w ∈ (Finset.univ : Finset F), ν (S ∩ m ⁻¹' {w}) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ (Finset.univ : Finset F), ν (S ∩ m ⁻¹' {v}) :=
        Finset.sum_le_sum fun w _ => hv w (Finset.mem_univ w)
    _ = Fintype.card F * ν (S ∩ m ⁻¹' {v}) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable {X : Type w} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {D : ConstraintDynamics X} {ι : Type u} (A : TickReadout D ι)

/-- ★★★ **One record history carries a share of any set of starts.** For a finite family of
readings whose counts are capped at `B` from every start, and any set `S` of starts: there
are counts `c j ≤ B` such that the compatible region of the history that records `c j` at
every reading holds at least the fraction `1 / (B + 1)^k` of the measure of `S`. -/
theorem TickReadout.exists_history_measure_ge {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ)
    (hcap : ∀ j x n, HasTicks (A.rest (ctx j).1) (A.disp (ctx j).1) (fun s => D.flow s x)
      (ctx j).2 n → n ≤ B) (S : Set X) :
    ∃ c : Fin k → Fin (B + 1),
      (D.muL : MeasureTheory.Measure X) S
        ≤ ((B + 1 : ℕ) : ENNReal) ^ k * (D.muL : MeasureTheory.Measure X)
            (S ∩ compatibleSet A.semantics
              (List.ofFn fun j => TickReadout.startFact (ctx j).1 (ctx j).2 (c j))) := by
  have hex : ∀ x j, ∃ N : Fin (B + 1), x ∈ A.countEvent (ctx j).1 (ctx j).2 N := fun x j => by
    obtain ⟨N, hN, hc⟩ := exists_isTickCount_of_cap (hcap j x)
    exact ⟨⟨N, Nat.lt_succ_of_le hN⟩, hc⟩
  choose m hm using hex
  obtain ⟨c, hc⟩ := exists_le_card_mul_measure_inter_preimage
    (D.muL : MeasureTheory.Measure X) m S
  refine ⟨c, hc.trans ?_⟩
  have hcard : Fintype.card (Fin k → Fin (B + 1)) = (B + 1) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [hcard, Nat.cast_pow]
  refine mul_le_mul' le_rfl (MeasureTheory.measure_mono (inter_subset_inter_right S ?_))
  rintro x rfl
  rw [A.compatibleSet_eq_preimage_singleton ctx B]
  funext j
  exact (A.tickCode_eq_castSucc_iff B (ctx j).1 (ctx j).2 x (m x j)).2 (hm x j)

end Cells

/-! ### The five-pointer arena -/

section Penta

variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] {N : ℕ} (e : ν ≃ Fin (N + 1))
  {H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ} {f g k l r : ℝ → ℝ}

/-- ★★★ **The cap of a count on the five-pointer arena.** For a carrier with any index and
five Hermitian observables of norm at most `Γ`, and five profiles whose derivatives are at
most `Z` in size: from every start and for every pointer, a count at the flow time `T ≥ 0`
is at most `12 Z Γ T`. -/
theorem pentaCount_le (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian) (hG₂ : G₂.IsHermitian)
    (hG₃ : G₃.IsHermitian) (hG₄ : G₄.IsHermitian) (hG₅ : G₅.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (hcr : ContDiff ℝ ∞ r) {Z Γ : ℝ}
    (hZ₁ : ∀ φ, |hf.deriv_periodic.lift φ| ≤ Z) (hZ₂ : ∀ φ, |hg.deriv_periodic.lift φ| ≤ Z)
    (hZ₃ : ∀ φ, |hk.deriv_periodic.lift φ| ≤ Z) (hZ₄ : ∀ φ, |hl.deriv_periodic.lift φ| ≤ Z)
    (hZ₅ : ∀ φ, |hr.deriv_periodic.lift φ| ≤ Z) (hΓ₁ : ‖G₁‖ ≤ Γ) (hΓ₂ : ‖G₂‖ ≤ Γ)
    (hΓ₃ : ‖G₃‖ ≤ Γ) (hΓ₄ : ‖G₄‖ ≤ Γ) (hΓ₅ : ‖G₅‖ ≤ Γ) (i : Fin 5) (x : PentaSigma N)
    {T : ℝ} (hT : 0 ≤ T) {Nc : ℕ}
    (h : HasTicks (pentaPointer i ⁻¹' readyArc 2) (pentaPointer i ⁻¹' displayArc)
      (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
        (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
        (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t x) T Nc) :
    (Nc : ℝ) ≤ 12 * Z * Γ * T := by
  obtain ⟨⟨⟨⟨⟨P, θ⟩, ψ⟩, χ⟩, ξ⟩, ζ⟩ := x
  obtain ⟨p, rfl⟩ := (idxArenaEquiv e).surjective P
  have hF := fibreH_isHermitian hH hG₁ hG₂ hG₃ hG₄ hG₅ (hf.lift θ.2) (hg.lift ψ.2)
    (hk.lift χ.2) (hl.lift ξ.2) (hr.lift ζ.2)
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ₁ 0)
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans hΓ₁
  have key : ∀ (G : Matrix ν ν ℂ) (z : ℝ) (q : KTorus), |z| ≤ Z → ‖G‖ ≤ Γ →
      HasTicks (readyArc 2) displayArc (fun t => pshift (freeShift hF G z p t) q) T Nc →
      (Nc : ℝ) ≤ 12 * Z * Γ * T := by
    intro G z q hz hG hticks
    have h1 := HasTicks.pointer_mul_le (K := 2 * Z * Γ) (q := q)
      (D := fun t => freeShift hF G z p t)
      (mul_nonneg (mul_nonneg zero_le_two hZ0) hΓ0) hT (fun t _ _ => rfl)
      (fun s t _ hst _ => (abs_freeShift_sub_le hF G z p hst).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hz zero_le_two) hG (norm_nonneg _)
            (mul_nonneg zero_le_two hZ0)) (sub_nonneg.2 hst))) hticks
    linarith
  have hrun := fun t => pentaRun_fibre e hH hG₁ hG₂ hG₃ hG₄ hG₅ hf hg hk hl hr hc hcg hck hcl
    hcr p θ ψ χ ξ ζ hF t
  simp only [hrun] at h
  fin_cases i
  · exact key G₁ _ θ (hZ₁ _) hΓ₁ h
  · exact key G₂ _ ψ (hZ₂ _) hΓ₂ h
  · exact key G₃ _ χ (hZ₃ _) hΓ₃ h
  · exact key G₄ _ ξ (hZ₄ _) hΓ₄ h
  · exact key G₅ _ ζ (hZ₅ _) hΓ₅ h

end Penta

/-! ### The radar's walled chain -/

/-- The derivative of the scaled profile is at most `|g|` in size. -/
theorem abs_scaledTrainF_deriv_lift_le (g : ℝ) (φ : AddCircle (1 : ℝ)) :
    |(scaledTrainF_periodic g).deriv_periodic.lift φ| ≤ |g| := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective φ
  rw [scaledTrainF_deriv_lift_coe, abs_neg, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg g) (Real.abs_cos_le_one _)

section Wall

variable (n N M : ℕ) (μ Δ w gA gB : ℝ) {D : ℕ}
  (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
    × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1))

/-- ★★★ **The cap of the radar's counts.** On the walled chain of the radar, from every
start and for every one of the five pointers, a count at the flow time `T ≥ 0` is at most
`12 max(|g_A|, |g_B|) T`. -/
theorem wallCount_le (i : Fin 5) (x : PentaSigma D) {T : ℝ} (hT : 0 ≤ T) {Nc : ℕ}
    (h : HasTicks ((wallReadout n N M μ Δ w gA gB e p₀).rest i)
      ((wallReadout n N M μ Δ w gA gB e p₀).disp i)
      (fun t => (wallDynamics n N M μ Δ w gA gB e p₀).flow t x) T Nc) :
    (Nc : ℝ) ≤ 12 * max |gA| |gB| * T := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := tri_gate_norms_le_one
    (ι := ZMod (M + 1) × Fin 2) (κa := (ZMod (M + 1) × Fin 2) × Fin 2)
    (κb := (ZMod (M + 1) × Fin 2) × Fin 2)
    (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (wallNear (M + 1) w) (fun a b => ¬ wallNear (M + 1) w a b)
    (fun a b => ¬ wallNear (M + 1) w a b) (fun a b => ¬ wallNear (M + 1) w a b)
    (fun a b => ¬ wallNear (M + 1) w a b)
    (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_mul_self
    (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_mul_self
  have hB : ∀ φ, |(scaledTrainF_periodic gB).deriv_periodic.lift φ| ≤ max |gA| |gB| :=
    fun φ => (abs_scaledTrainF_deriv_lift_le gB φ).trans (le_max_right _ _)
  have hA : ∀ φ, |(scaledTrainF_periodic gA).deriv_periodic.lift φ| ≤ max |gA| |gB| :=
    fun φ => (abs_scaledTrainF_deriv_lift_le gA φ).trans (le_max_left _ _)
  have key := pentaCount_le e
    (compositeH_isHermitian
      (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
      (compositeH_isHermitian
        (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
        (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))))
    (gateOp_snd_isHermitian (κa := (ZMod (M + 1) × Fin 2) × Fin 2)
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne)
    (gateOp_snd_isHermitian (κa := (ZMod (M + 1) × Fin 2) × Fin 2)
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
      (fun a b => ¬ wallNear (M + 1) w a b)
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne)
    (kronecker_isHermitian (Matrix.isHermitian_one (n := ZMod (M + 1) × Fin 2))
      (gateOp_isHermitian (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun a b => ¬ wallNear (M + 1) w a b)
        (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
        levelSwap_apply_eq_zero_of_site_ne))
    (gateOp_fst_isHermitian (κb := (ZMod (M + 1) × Fin 2) × Fin 2)
      (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
      (fun a b => ¬ wallNear (M + 1) w a b)
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
      levelSwap_apply_eq_zero_of_site_ne)
    (kronecker_isHermitian (Matrix.isHermitian_one (n := ZMod (M + 1) × Fin 2))
      (gateOpL_isHermitian (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun a b => ¬ wallNear (M + 1) w a b)
        (levelSwap_isHermitian (ZMod (M + 1) × Fin 2))
        levelSwap_apply_eq_zero_of_site_ne))
    (scaledTrainF_periodic gB) (scaledTrainF_periodic gB) (scaledTrainF_periodic gB)
    (scaledTrainF_periodic gA) (scaledTrainF_periodic gA)
    (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB)
    (contDiff_scaledTrainF gA) (contDiff_scaledTrainF gA)
    hB hB hB hA hA n1 n2 n3 n4 n5 i x hT h
  linarith

set_option synthInstance.maxSize 4096 in
open CSD.SigmaLayer in
/-- ★★★ **One radar history carries a share of any set of starts.** For five readings of
the walled chain at flow times `τ j ≥ 0` and a cap `B` with `12 max(|g_A|, |g_B|) τ j ≤ B`:
for every set `S` of starts there are five counts at most `B` whose history's compatible
region holds at least `1 / (B + 1)^5` of the measure of `S`. -/
theorem wall_exists_history_measure_ge (τ : Fin 5 → ℝ) (hτ : ∀ j, 0 ≤ τ j) (B : ℕ)
    (hB : ∀ j, 12 * max |gA| |gB| * τ j ≤ B) (S : Set (PentaSigma D)) :
    ∃ c : Fin 5 → Fin (B + 1),
      ((wallDynamics n N M μ Δ w gA gB e p₀).muL : MeasureTheory.Measure (PentaSigma D)) S
        ≤ ((B + 1 : ℕ) : ENNReal) ^ 5
          * ((wallDynamics n N M μ Δ w gA gB e p₀).muL : MeasureTheory.Measure (PentaSigma D))
            (S ∩ compatibleSet (wallReadout n N M μ Δ w gA gB e p₀).semantics
              (List.ofFn fun j : Fin 5 => TickReadout.startFact j (τ j) (c j))) :=
  (wallReadout n N M μ Δ w gA gB e p₀).exists_history_measure_ge
    (fun j : Fin 5 => (j, τ j)) B
    (fun j x m h => by
      have h1 := wallCount_le n N M μ Δ w gA gB e p₀ j x (hτ j) h
      exact_mod_cast h1.trans (hB j)) S

end Wall

end CSD.RecordLayer

end
