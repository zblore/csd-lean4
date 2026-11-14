/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCoincidenceFlow
public import CsdLean4.RecordLayer.UnifiedTwoCounts

/-!
# A gated reading: the number of tick records fixed after the gate closes

**Category:** 7-SigmaLayer (the record layer). BACKLOG #394 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, fourth brick: the reading of UA-18 (e) as a theorem with hypotheses on where the
two carriers are. No new assumption beyond UA-18.

UA-18 (e) says a reading is the number of tick records a gated pointer wrote in its first open
period. This module proves the statement every one of the five readings is to be obtained
from. It has two layers.

*The pointer.* `gated_pointer_count`: a last pointer whose displacement follows a swing up to
`t_a`, moves at speed at most `v` on `[t_a, t_b]`, and moves by at most a sixth of a turn
inside `[t_b, t_c]`, has a count `N_a` at `t_a` with `|2π N_a − R t_a| ≤ 2π`; a count `N_b` at
`t_b` with `N_a ≤ N_b ≤ N_a + 3 v (t_b − t_a) + 3/2`; and at every flow time of `[t_b, t_c]` a
count that is `N_b` or `N_b + 1`.

*The carriers.* `coincFlow_gated_reading`: for the flow of #393, from a product ray on a fibre
where both profiles vanish, with the last pointer coupled to `gateOp r Y`: if the two carriers
have weight at most `ε` outside the relation `r` up to `t_a` (gate open), weight at most `ε`
inside it on `[t_b, t_c]` (gate closed), and the second carrier's own accumulated reading of
`Y` follows a swing up to `t_a`, then the pointer has those counts, with `v = 2|z|`, and every
count `N` in `[t_b, t_c]` has `|2π N − R t_a| ≤ 2π (6|z| (t_b − t_a) + 7/2)`.

* `hasTicks_snd_le_of_travel` — #378's "ticks need travel" for a last pointer;
* ★★ `gated_pointer_count`;
* `arenaObs_siteSel`, `arenaObs_siteSel_nonneg`, `sum_arenaObs_siteSel`;
* `arenaObs_coincProj_prodRay_nonneg`, `arenaObs_coincProj_add_not`;
* ★ `arenaObs_coincProj_prodRay_le_of_disjoint` — if no site of `I` is related to a site of
  `J`, the weight inside the relation is at most the first carrier's weight outside `I` plus
  the second carrier's weight outside `J`;
* ★ `abs_arenaObs_siteSel_mul_levelSwap_le` — the level swap of UA-12 meets the hypothesis on
  `Y` used below;
* ★★ `abs_arenaObs_gateOp_prodRay_le`, `abs_arenaObs_gateOp_prodRay_sub_le` — on a product
  ray a gated reading is at most the weight inside the relation, and differs from the ungated
  reading by at most the weight outside it;
* `abs_coincShift_sub_le` — a displacement over `[s, t]` from a bound of the expectation;
* ★★★ `coincFlow_gated_reading`.

## Exact scope

* **Conditional on where the carriers are and on the clock.** The three hypotheses (weight
  outside the relation small up to `t_a`; weight inside it small on `[t_b, t_c]`; the second
  carrier's ungated displacement within `δ₀` of a swing) are hypotheses. No carrier, relation
  or packet is put in here, and the hypotheses are not shown to hold for any. That is the
  next brick of step (4).
* **What is fixed, and when.** The count is `N_b` or `N_b + 1` at every flow time of
  `[t_b, t_c]`, and nothing is said after `t_c`. Between `t_a` and `t_b` the gate is neither
  open nor closed and the count may advance by up to `6|z| (t_b − t_a) + 3/2`: that term is
  the reading's error from the closing of the gate, and it is not small unless the closing is
  short against the pointer's speed.
* **Counts of passages.** `IsTickCount` counts passages from the ready arc to the displayed
  arc (#358). That each such tick is a record write is #358's `IsSwing.isRecordWrite` up to
  `t_a`; it is not restated here, and no record write is shown for a tick completed after
  `t_a`.
* **Flow times.** `t_a`, `t_b`, `t_c` and the rate `R` are in flow time. Nothing here is a
  speed, a distance or a second observer.
* **Only the fibres where both profiles vanish, and only product starts**, as #393: a null
  set of fibres and of starts.
* **Two carriers.** UA-18 has three, and walls.
* **Earlier.** #377 and #381 have the same three phases for one region projector on the ring
  with one-mode clocks (`isSwing_gateClock_before`, `gateClock_no_tick_after`,
  `twoCounts_away`); this module is the form with a coincidence relation, a general clock
  operator and hypotheses in place of the packet family.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-12,
UA-18, UO-16, UD-147, UD-148); `RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincFlow`,
`coincFlow_prodRay`, `coincShift`, `coincShift_gateOp_add_not`);
`RecordLayer/UnifiedCoincidence.lean` (#390: `coincProj`, `gateOp`, `siteSel`);
`RecordLayer/UnifiedTwoCounts.lean` (#381: `isSwing_snd_of_abs_shift_sub_le`,
`hasTicks_le_succ_of_no_passage`, `exists_tickCount_of_bdd`);
`RecordLayer/UnifiedGateCount.lean` (#378: `hasTicks_le_of_travel`);
`RecordLayer/UnifiedDiracClockTicks.lean` (#358: `IsSwing`, `IsTickCount`);
`RecordLayer/UnifiedDiracClock.lean` (`levelSwap`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The pointer: a count while the drive is a swing, and after it stops -/

section Pointer

variable {Y : Type*}

/-- **Ticks need travel, for a last pointer** (#378's `hasTicks_le_of_travel`). -/
theorem hasTicks_snd_le_of_travel {γ : ℝ → Y × KTorus} {q : KTorus} {D W : ℝ → ℝ} {s T : ℝ}
    (hsT : s ≤ T) (hγ : ∀ t, s ≤ t → t ≤ T → (γ t).2 = pshift (D t) q)
    (hW : ∀ a b, s ≤ a → a ≤ b → b ≤ T → |D b - D a| ≤ W b - W a) {m N₀ : ℕ}
    (hm : HasTicks {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc}
      γ T m)
    (hN : ¬ HasTicks {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc}
      γ s (N₀ + 1)) :
    (m : ℝ) ≤ N₀ + 3 * (W T - W s) + 3 / 2 := by
  obtain ⟨p₀⟩ : Nonempty (CPN (0 + 1)) := inferInstance
  exact hasTicks_le_of_travel (N := 0)
    (γ := fun t => ((((p₀, q), q), (γ t).2) : TriSigma 0)) hsT hγ hW hm hN

/-- ★★ **The count of a pointer whose drive is a swing and then stops.** A last pointer whose
displacement `D` is within `δ` of `A (1 − cos R t)` up to `t_a`, changes by at most
`v (t − s)` between flow times of `[t_a, t_b]`, and changes by at most a sixth of a turn
between flow times of `[t_b, t_c]`: it has a count `N_a` at `t_a` with
`|2π N_a − R t_a| ≤ 2π`, a count `N_b` at `t_b` with `N_a ≤ N_b ≤ N_a + 3 v (t_b − t_a) + 3/2`,
and at every flow time of `[t_b, t_c]` a count that is `N_b` or `N_b + 1`. -/
theorem gated_pointer_count {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ}
    {R A δ v ta tb tc : ℝ} (hR : 0 < R) (hA : 0 < A) (hδ : 0 ≤ δ) (hta : 0 ≤ ta)
    (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hγ : ∀ t, 0 ≤ t → t ≤ tc → (γ t).2 = pshift (D t) q)
    (hopen : ∀ t, 0 ≤ t → t ≤ ta → |D t - A * (1 - Real.cos (R * t))| ≤ δ)
    (h₁ : δ < rep q.1) (h₂ : rep q.1 + δ ≤ 1 / 6) (h₃ : 1 / 3 < rep q.1 + 2 * A - δ)
    (h₄ : rep q.1 + 2 * A + δ ≤ 5 / 6)
    (hmid : ∀ s t, ta ≤ s → s ≤ t → t ≤ tb → |D t - D s| ≤ v * (t - s))
    (hclosed : ∀ s t, tb ≤ s → s ≤ t → t ≤ tc → |D t - D s| ≤ 1 / 6) :
    ∃ Na Nb : ℕ,
      IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc}
          γ ta Na
        ∧ |(Na : ℝ) * (2 * Real.pi) - R * ta| ≤ 2 * Real.pi
        ∧ IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
            {x : Y × KTorus | x.2 ∈ displayArc} γ tb Nb
        ∧ Na ≤ Nb ∧ (Nb : ℝ) ≤ Na + 3 * v * (tb - ta) + 3 / 2
        ∧ ∀ t, tb ≤ t → t ≤ tc →
            ∃ N, IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
                {x : Y × KTorus | x.2 ∈ displayArc} γ t N ∧ Nb ≤ N ∧ N ≤ Nb + 1 := by
  have hsw := isSwing_snd_of_abs_shift_sub_le (Y := Y) (γ := γ) hR hA hδ
    (fun t h0 hT => hγ t h0 (hT.trans (hab.trans hbc))) hopen h₁ h₂ h₃ h₄
  obtain ⟨Na, hNa⟩ := hsw.exists_tickCount hta
  have hB : ∀ m, HasTicks {x : Y × KTorus | x.2 ∈ readyArc 2}
      {x : Y × KTorus | x.2 ∈ displayArc} γ tb m → (m : ℝ) ≤ Na + 3 * v * (tb - ta) + 3 / 2 := by
    intro m hm
    have h := hasTicks_snd_le_of_travel (W := fun t => v * t) hab
      (fun t h1 h2 => hγ t (hta.trans h1) (h2.trans hbc))
      (fun s t h1 h2 h3 => by
        show |D t - D s| ≤ v * t - v * s
        rw [← mul_sub]
        exact hmid s t h1 h2 h3) hm hNa.2
    have e : (fun t => v * t) tb - (fun t => v * t) ta = v * (tb - ta) := by
      show v * tb - v * ta = v * (tb - ta)
      ring
    rw [e] at h
    linarith
  obtain ⟨B, hBn⟩ := exists_nat_ge ((Na : ℝ) + 3 * v * (tb - ta) + 3 / 2)
  obtain ⟨Nb, hNb⟩ := exists_tickCount_of_bdd (B := B)
    (fun m hm => by exact_mod_cast (hB m hm).trans hBn)
  have hNab : Na ≤ Nb := by
    by_contra hlt
    rw [not_le] at hlt
    exact hNb.2 ((hNa.1.mono_time hab).mono_count (by omega))
  refine ⟨Na, Nb, hNa, hsw.abs_tickCount_sub_le hta hNa, hNb, hNab, hB Nb hNb.1, ?_⟩
  intro t hbt htc
  have hno : ∀ a' b', tb ≤ a' → a' ≤ b' → b' ≤ t →
      γ a' ∈ {x : Y × KTorus | x.2 ∈ readyArc 2} →
      γ b' ∉ {x : Y × KTorus | x.2 ∈ displayArc} := by
    intro a' b' h1 h2 h3 hr hd
    have h0a : 0 ≤ a' := (hta.trans hab).trans h1
    have habs := hclosed a' b' h1 h2 (h3.trans htc)
    have hr' : pshift (D a') q ∈ readyArc 2 := by
      rw [← hγ a' h0a ((h2.trans h3).trans htc)]
      exact hr
    have hnd := pshift_notMem_displayArc_of_mem_readyArc habs hr'
    rw [pshift_add, sub_add_cancel] at hnd
    apply hnd
    rw [← hγ b' (h0a.trans h2) (h3.trans htc)]
    exact hd
  obtain ⟨N, hN⟩ := exists_tickCount_of_bdd (B := Nb + 1)
    (fun m hm => hasTicks_le_succ_of_no_passage hno hm hNb.2)
  exact ⟨N, hN, hNb.le_succ_of_no_passage hbt hno hN⟩

end Pointer

/-! ### Weights inside and outside a relation -/

section Weights

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]

omit [Fintype S] in
/-- The occupancy of a site is the sum of the moment coordinates of the indices at it. -/
theorem arenaObs_siteSel (s : S) (p : GenArena ι) :
    arenaObs (siteSel σ s) p = ∑ i, if σ i = s then momentMap p i else 0 := by
  have hc : (fun i : ι => if σ i = s then (1 : ℂ) else 0)
      = fun i => (((if σ i = s then (1 : ℝ) else 0 : ℝ)) : ℂ) := by
    funext i
    split_ifs <;> simp
  rw [siteSel, hc, arenaObs_diagonal_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

omit [Fintype S] in
theorem arenaObs_siteSel_nonneg (s : S) (p : GenArena ι) : 0 ≤ arenaObs (siteSel σ s) p := by
  rw [arenaObs_siteSel]
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact momentMap_nonneg p i
  · exact le_rfl

/-- The occupancies of the sites add up to one. -/
theorem sum_arenaObs_siteSel (p : GenArena ι) : ∑ s, arenaObs (siteSel σ s) p = 1 := by
  simp only [arenaObs_siteSel]
  rw [Finset.sum_comm, ← momentMap_sum_eq_one p]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The weight of a product ray inside a relation is not negative. -/
theorem arenaObs_coincProj_prodRay_nonneg (p : GenArena ι) (q : GenArena κ) :
    0 ≤ arenaObs (coincProj σ τ r) (prodRay p q) := by
  rw [arenaObs_coincProj_prodRay]
  refine Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ => ?_
  split_ifs
  · exact mul_nonneg (arenaObs_siteSel_nonneg σ s p) (arenaObs_siteSel_nonneg τ s' q)
  · exact le_rfl

omit [Fintype S] [DecidableEq S] in
/-- The weight inside a relation and the weight outside it add up to one, at every ray. -/
theorem arenaObs_coincProj_add_not (P : GenArena (ι × κ)) :
    arenaObs (coincProj σ τ r) P + arenaObs (coincProj σ τ fun x y => ¬ r x y) P = 1 := by
  rw [← one_sub_coincProj, ← arenaObs_add, add_sub_cancel, arenaObs_one]

private theorem sum_ite_notMem (I : Finset S) (a : S → ℝ) (h1 : ∑ s, a s = 1) :
    ∑ s, (if s ∈ I then 0 else a s) = 1 - ∑ s ∈ I, a s := by
  have h : ∑ s, a s = ∑ s, ((if s ∈ I then a s else 0) + (if s ∈ I then 0 else a s)) :=
    Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at h
  linarith

/-- ★ **Apart regions give a small weight inside the relation.** If no site of `I` is related
to a site of `J`, the weight of a product ray inside the relation is at most the first
carrier's weight outside `I` plus the second carrier's weight outside `J`. -/
theorem arenaObs_coincProj_prodRay_le_of_disjoint (I J : Finset S)
    (hIJ : ∀ s ∈ I, ∀ s' ∈ J, ¬ r s s') (p : GenArena ι) (q : GenArena κ) :
    arenaObs (coincProj σ τ r) (prodRay p q)
      ≤ (1 - ∑ s ∈ I, arenaObs (siteSel σ s) p)
        + (1 - ∑ s' ∈ J, arenaObs (siteSel τ s') q) := by
  have ha := fun s => arenaObs_siteSel_nonneg σ s p
  have hb := fun s' => arenaObs_siteSel_nonneg τ s' q
  have hI := sum_ite_notMem I _ (sum_arenaObs_siteSel σ p)
  have hJ := sum_ite_notMem J _ (sum_arenaObs_siteSel τ q)
  rw [arenaObs_coincProj_prodRay, ← hI, ← hJ]
  have e1 : ∑ s, (if s ∈ I then 0 else arenaObs (siteSel σ s) p)
      = ∑ s, ∑ s', (if s ∈ I then 0 else arenaObs (siteSel σ s) p)
          * arenaObs (siteSel τ s') q := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, sum_arenaObs_siteSel τ q, mul_one]
  have e2 : ∑ s', (if s' ∈ J then 0 else arenaObs (siteSel τ s') q)
      = ∑ s, ∑ s', arenaObs (siteSel σ s) p
          * (if s' ∈ J then 0 else arenaObs (siteSel τ s') q) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [← Finset.sum_mul, sum_arenaObs_siteSel σ p, one_mul]
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s' _ => ?_
  have hab := mul_nonneg (ha s) (hb s')
  by_cases hs : s ∈ I
  · by_cases hs' : s' ∈ J
    · simp [hs, hs', hIJ s hs s' hs']
    · simp only [hs, hs', ↓reduceIte, zero_mul, zero_add]
      split_ifs
      · exact le_rfl
      · exact hab
  · simp only [hs, ↓reduceIte]
    have h2 : 0 ≤ arenaObs (siteSel σ s) p
        * (if s' ∈ J then 0 else arenaObs (siteSel τ s') q) := by
      split_ifs
      · simp
      · exact hab
    split_ifs <;> linarith

omit [Fintype S] in
/-- ★ **The level swap is bounded site by site**: restricted to a site, the level swap's
expectation is at most that site's occupancy, when the two levels sit at the same site. -/
theorem abs_arenaObs_siteSel_mul_levelSwap_le {n : Type*} [Fintype n] [DecidableEq n]
    (τ₀ : n → S) (s : S) (q : GenArena (n × Fin 2)) :
    |arenaObs (siteSel (fun x : n × Fin 2 => τ₀ x.1) s * levelSwap n) q|
      ≤ arenaObs (siteSel (fun x : n × Fin 2 => τ₀ x.1) s) q := by
  obtain ⟨v, hv, rfl⟩ : ∃ v, ∃ hv : v ≠ 0, q = Projectivization.mk ℂ v hv :=
    ⟨q.rep, q.rep_nonzero, (Projectivization.mk_rep q).symm⟩
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  rw [arenaObs_siteSel, arenaObs_mk_eq_inner _ hv]
  simp only [momentMap_mk]
  have key : (inner ℂ v (Matrix.toEuclideanLin
        (siteSel (fun x : n × Fin 2 => τ₀ x.1) s * levelSwap n) v)).re
      = ∑ a : n, if τ₀ a = s then 2 * (v (a, 1) * star (v (a, 0))).re else 0 := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    simp only [toEuclideanLin_coord, RCLike.inner_apply, ← Matrix.mulVec_mulVec, siteSel,
      Matrix.mulVec_diagonal, levelSwap_mulVec_zero, levelSwap_mulVec_one]
    split_ifs
    · simp only [one_mul, Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
        Complex.conj_im]
      ring
    · simp
  rw [key, abs_div, abs_of_pos hn, Fintype.sum_prod_type]
  have e : ∑ a : n, ∑ c : Fin 2, (if τ₀ (a, c).1 = s then ‖v (a, c)‖ ^ 2 / ‖v‖ ^ 2 else 0)
      = (∑ a : n, if τ₀ a = s then ‖v (a, 0)‖ ^ 2 + ‖v (a, 1)‖ ^ 2 else 0) / ‖v‖ ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    split_ifs <;> simp [add_div]
  rw [e]
  refine div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun a _ => ?_)) hn.le
  split_ifs
  · have h1 : |(v (a, 1) * star (v (a, 0))).re| ≤ ‖v (a, 1)‖ * ‖v (a, 0)‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_star]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_nonneg (‖v (a, 1)‖ - ‖v (a, 0)‖)]
  · simp

variable {Y : Matrix κ κ ℂ}

/-- ★★ **On a product ray a gated reading is at most the weight inside the relation**, for an
operator `Y` bounded site by site. -/
theorem abs_arenaObs_gateOp_prodRay_le
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (p : GenArena ι) (q : GenArena κ) :
    |arenaObs (gateOp σ τ r Y) (prodRay p q)| ≤ arenaObs (coincProj σ τ r) (prodRay p q) := by
  rw [arenaObs_gateOp_prodRay, arenaObs_coincProj_prodRay]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => ?_)
  split_ifs
  · rw [abs_mul, abs_of_nonneg (arenaObs_siteSel_nonneg σ s p)]
    exact mul_le_mul_of_nonneg_left (hY s' q) (arenaObs_siteSel_nonneg σ s p)
  · simp

/-- ★★ **On a product ray a gated reading differs from the ungated reading by at most the
weight outside the relation.** -/
theorem abs_arenaObs_gateOp_prodRay_sub_le
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (p : GenArena ι) (q : GenArena κ) :
    |arenaObs (gateOp σ τ r Y) (prodRay p q) - arenaObs Y q|
      ≤ arenaObs (coincProj σ τ fun x y => ¬ r x y) (prodRay p q) := by
  have h := abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY p q
  have e : arenaObs (gateOp σ τ r Y) (prodRay p q) - arenaObs Y q
      = -arenaObs (gateOp σ τ (fun x y => ¬ r x y) Y) (prodRay p q) := by
    have h1 := arenaObs_one_kronecker (ι := ι) Y p q
    rw [← gateOp_add_gateOp_not σ τ r Y, arenaObs_add] at h1
    linarith
  rw [e, abs_neg]
  exact h

end Weights

/-! ### The carriers: the reading of a gated pointer -/

section Reading

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] {a b : ℕ} (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h : ℝ → ℝ}
  (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {G₁ : Matrix (ι × κ) (ι × κ) ℂ} {Y : Matrix κ κ ℂ}

omit [Fintype S] [DecidableEq S] in
/-- **A displacement over `[s, t]` from a bound of the expectation.** -/
theorem abs_coincShift_sub_le (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (G : Matrix (ι × κ) (ι × κ) ℂ) (z : ℝ) (p : GenArena ι) (q : GenArena κ) {ε s t : ℝ}
    (hst : s ≤ t)
    (hε : ∀ u, s ≤ u → u ≤ t →
      |arenaObs G (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q))| ≤ ε) :
    |coincShift hA hC G z p q t - coincShift hA hC G z p q s| ≤ 2 * |z| * ε * (t - s) := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun u : ℝ =>
      arenaObs G (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)))
      volume x y := fun x y => (continuous_arenaObs_prodRay_free hA hC G p q).intervalIntegrable _ _
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := ε)
    (f := fun u : ℝ =>
      arenaObs G (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)))
    (fun u hu => by
      rw [Set.uIoc_of_le hst] at hu
      rw [Real.norm_eq_abs]
      exact hε u hu.1.le hu.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] at hI
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  unfold coincShift
  rw [← mul_sub, intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s), abs_mul,
    abs_mul, h2]
  calc 2 * |z| * |∫ u in s..t,
          arenaObs G (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q))|
      ≤ 2 * |z| * (ε * (t - s)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 2 * |z| * ε * (t - s) := by ring

/-- ★★★ **The reading of a gated pointer.** For the flow of #393 with its last pointer coupled
to `gateOp r Y`, from a product ray on a fibre where both profiles vanish, `z` the derivative
of the last pointer's profile at its conserved angle. Suppose that up to `t_a` the two carriers
have weight at most `ε` outside the relation, that on `[t_b, t_c]` they have weight at most
`ε` inside it with `2|z| ε (t_c − t_b) ≤ 1/6`, and that up to `t_a` the second carrier's own
accumulated reading of `Y`, times `−2z`, is within `δ₀` of `A (1 − cos R t)`. Then the pointer
has a count `N_a` at `t_a` with `|2π N_a − R t_a| ≤ 2π`; a count `N_b` at `t_b` with
`N_a ≤ N_b ≤ N_a + 6|z| (t_b − t_a) + 3/2`; and at every flow time of `[t_b, t_c]` a count
`N` that is `N_b` or `N_b + 1`, with `|2π N − R t_a| ≤ 2π (6|z| (t_b − t_a) + 7/2)`. -/
theorem coincFlow_gated_reading (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hG₁ : G₁.IsHermitian) (hYh : Y.IsHermitian) (hYs : ∀ i j, τ i ≠ τ j → Y i j = 0)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) (p : GenArena ι) (q : GenArena κ) {θ ψ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hh.lift ψ.2 = 0) {R A δ₀ ε ta tb tc : ℝ} (hR : 0 < R)
    (hA' : 0 < A) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hclock : ∀ t, 0 ≤ t → t ≤ ta →
      |-2 * hh.deriv_periodic.lift ψ.2
            * (∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q))
          - A * (1 - Real.cos (R * t))| ≤ δ₀)
    (hopen : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hclosed : ∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hsmall : 2 * |hh.deriv_periodic.lift ψ.2| * ε * (tc - tb) ≤ 1 / 6)
    (h₁ : δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta < rep ψ.1)
    (h₂ : rep ψ.1 + (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta) ≤ 1 / 6)
    (h₃ : 1 / 3 < rep ψ.1 + 2 * A - (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta))
    (h₄ : rep ψ.1 + 2 * A + (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta) ≤ 5 / 6) :
    ∃ Na Nb : ℕ,
      IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
          {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
          (fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ r Y) hf hh hc hch t
            ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) ta Na
        ∧ |(Na : ℝ) * (2 * Real.pi) - R * ta| ≤ 2 * Real.pi
        ∧ IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
            {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
            (fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ r Y) hf hh hc hch t
              ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) tb Nb
        ∧ Na ≤ Nb
        ∧ (Nb : ℝ) ≤ Na + 6 * |hh.deriv_periodic.lift ψ.2| * (tb - ta) + 3 / 2
        ∧ ∀ t, tb ≤ t → t ≤ tc →
            ∃ N, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
                {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
                (fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ r Y) hf hh hc hch t
                  ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) t N
              ∧ Nb ≤ N ∧ N ≤ Nb + 1
              ∧ |(N : ℝ) * (2 * Real.pi) - R * ta|
                  ≤ 2 * Real.pi * (6 * |hh.deriv_periodic.lift ψ.2| * (tb - ta) + 7 / 2) := by
  set z := hh.deriv_periodic.lift ψ.2 with hz
  have hπ := Real.pi_pos
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hW1 : ∀ u, arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)) ≤ 1 := fun u => by
    have h1 := arenaObs_coincProj_add_not σ τ r
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q))
    have h2 := arenaObs_coincProj_prodRay_nonneg σ τ (fun x y => ¬ r x y)
      (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)
    linarith
  -- the displacement while the gate is open
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
  obtain ⟨Na, Nb, hNa, hNa', hNb, hNab, hNb', hwin⟩ := gated_pointer_count
    (Y := KSigma (a * (b + 1) + b + 1))
    (γ := fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ r Y) hf hh hc hch t
      ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ))
    (q := ψ) (D := fun t => coincShift hA hC (gateOp σ τ r Y) z p q t) (v := 2 * |z|)
    hR hA' (add_nonneg hδ₀ (by positivity)) hta hab hbc
    (fun t _ _ => by
      rw [coincFlow_prodRay e₁ e₂ hA hC hG₁ (gateOp_isHermitian σ τ r hYh hYs) hf hh hc hch t
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
  have hNb'' : (Nb : ℝ) ≤ Na + 6 * |z| * (tb - ta) + 3 / 2 := by linarith
  refine ⟨Na, Nb, hNa, hNa', hNb, hNab, hNb'', fun t hbt htc => ?_⟩
  obtain ⟨N, hN, h1, h2⟩ := hwin t hbt htc
  refine ⟨N, hN, h1, h2, ?_⟩
  have hNa1 : (Na : ℝ) ≤ N := by exact_mod_cast hNab.trans h1
  have hN1 : (N : ℝ) ≤ Nb + 1 := by exact_mod_cast h2
  have htr : 0 ≤ 6 * |z| * (tb - ta) := by
    have : 0 ≤ tb - ta := sub_nonneg.2 hab
    positivity
  rw [abs_le] at hNa' ⊢
  constructor
  · nlinarith [hNa'.1, hNa'.2]
  · nlinarith [hNa'.1, hNa'.2]

end Reading

end CSD.RecordLayer
