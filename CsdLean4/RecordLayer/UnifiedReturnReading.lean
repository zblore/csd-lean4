/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWindowSwing
public import CsdLean4.RecordLayer.UnifiedEmissionReading

/-!
# The return reading: the count of the gate that is open while the messenger is away

**Category:** 7-SigmaLayer (the record layer). BACKLOG #399 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, ninth brick: Remainder (a) of #398, the return reading assembled. No new
assumption beyond UA-18.

The moving observer's return reading is the number of ticks of the pointer coupled to the
complementary gate, "the messenger is not with the clock". That gate is closed while the two
are together, open while the messenger is away and closed again when it is back. This module
reads that pointer.

* `count_after_transition` — a count carried through an interval of bounded speed and an
  interval in which the pointer hardly moves (the last two phases of #394, from any count);
* ★★ `away_pointer_count` — one pointer's history: within `η₀` of its start up to `t_a`,
  speed at most `v` on `[t_a, t_b]` and `[t₃, t₄]`, an offset swing in one of the bands of
  #398 on `[t_b, t₃]`, at most a sixth of a turn inside `[t₄, t₅]` ⇒ at every flow time of
  `[t₄, t₅]` a count `N` with `|2π N − R (t₃ − t_b)| ≤ 2π (3 v ((t_b − t_a) + (t₄ − t₃)) + 7)`;
* ★★★ `coincFlow_return_reading` — the same for the flow of #393 with its last pointer
  coupled to `gateOp (¬r) Y`, from where the two carriers are: little weight outside the
  relation up to `t_a` and on `[t₄, t₅]`, little weight inside it on `[t_b, t₃]`, the clock's
  swing up to `t₃`, and the offset in a band;
* `packetAngleGap`, `ringEmissionShift`, `ringReturnRun`, `levelSwap_apply_eq_zero_of_site_ne`;
* ★★★ `flat_clock_return_reading` — for any messenger packet and the flat clock packet of
  #392 on one ring, both gates in one run: for some strength `0 < g ≤ R/5`, if the emission
  pointer's displacement at `t_b` is in a band, the complementary pointer has at every flow
  time of `[t₄, t₅]` a count `N'` with
  `|2π N' − R (t₃ − t_b)| ≤ 2π (6 g ((t_b − t_a) + (t₄ − t₃)) + 7)`.

## Exact scope

* **Conditional on the band.** The conclusion holds for the runs in which the emission
  pointer's displacement `c` at `t_b` puts `1/12 − c` in one of the two bands of #398, with
  `η = 1/24 + 2 g ε (t₃ − t_b)`. Where `c` lies is not shown. Outside the bands #398 has a
  band in which the pointer does not tick at all, and edges at which nothing is proved.
* **The count is the time away, in ticks.** It is compared with `R (t₃ − t_b)`: `t_b` is the
  first flow time at which the two are certified apart and `t₃` the last. The two terms in
  `t_b − t_a` and `t₄ − t₃` are the closing and reopening of the emission gate. Nothing is
  recorded at any of these flow times (UA-7).
* **Inequalities between real numbers, no values.** As #396: the budgets, the predicted
  angles near, apart and near again, `t₃ ≤ 2π n/R`, and three size conditions. No values are
  shown to meet them together; #397 did that for the emission reading only. In particular
  no run is exhibited in which the messenger comes back, and `t₃ ≤ 2π n/R` asks the clock's
  horizon to cover the time away.
* **How the messenger comes back is not said.** The hypotheses are on predicted angles. On
  the ring a faster messenger laps the clock; with a wall it would be reflected. Neither is
  used here, and no wall is built.
* **`c` is the first pointer's displacement, by #393**: `ringEmissionShift` is
  `coincShift` of the gate with the same profile derivative, which `coincFlow_prodRay`
  identifies with the first pointer's lifted displacement in `ringReturnRun`. That
  identification is not restated as a theorem here.
* **The radar time and distance are not formed.** The emission reading (#396) and this one
  are two counts of two pointers of one run; no statement here adds or halves them.
* **Only the fibres where both profiles vanish, and only product starts**, as #393; for some
  strength, as #396; a ring and two carriers.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-18, UO-16, UD-146, UD-148, UD-151, UD-152, UD-155, UD-156, UD-157, UD-158);
`RecordLayer/UnifiedWindowSwing.lean` (#398: `offset_swing_count`);
`RecordLayer/UnifiedEmissionReading.lean` (#396: `flat_clock_swing`,
`clockPointerShift_trainF_eq`, `outside_arcs_flat_clock_le`, `scaledTrainF`);
`RecordLayer/UnifiedGateRegions.lean` (#395: `ringGate_not_le`, `ringGate_le`, `ringNear`,
`flatBudget`); `RecordLayer/UnifiedGatedReading.lean` (#394: `gated_pointer_count`,
`hasTicks_snd_le_of_travel`, `abs_coincShift_sub_le`, `abs_arenaObs_gateOp_prodRay_le`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincFlow_prodRay`,
`coincShift_gateOp_add_not`); `RecordLayer/UnifiedTwoCounts.lean` (#381:
`hasTicks_le_succ_of_no_passage`, `exists_tickCount_of_bdd`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The pointer: closed, open, closed -/

section Pointer

variable {Y : Type*}

/-- **A count through a transition and a stop.** A last pointer with a count `N_s` at `s`
whose displacement changes by at most `v (b − a)` between flow times of `[s, u]` and by at
most a sixth of a turn between flow times of `[u, w]`: it has a count `N_u` at `u` with
`N_s ≤ N_u ≤ N_s + 3 v (u − s) + 3/2`, and at every flow time of `[u, w]` a count that is
`N_u` or `N_u + 1`. -/
theorem count_after_transition {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ} {v s u w : ℝ}
    (hsu : s ≤ u) (huw : u ≤ w) (hγ : ∀ t, s ≤ t → t ≤ w → (γ t).2 = pshift (D t) q)
    (hmid : ∀ a b, s ≤ a → a ≤ b → b ≤ u → |D b - D a| ≤ v * (b - a))
    (hclosed : ∀ a b, u ≤ a → a ≤ b → b ≤ w → |D b - D a| ≤ 1 / 6) {Ns : ℕ}
    (hNs : IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
      {x : Y × KTorus | x.2 ∈ displayArc} γ s Ns) :
    ∃ Nu : ℕ,
      IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc}
          γ u Nu
        ∧ Ns ≤ Nu ∧ (Nu : ℝ) ≤ Ns + 3 * v * (u - s) + 3 / 2
        ∧ ∀ t, u ≤ t → t ≤ w →
            ∃ N, IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
                {x : Y × KTorus | x.2 ∈ displayArc} γ t N ∧ Nu ≤ N ∧ N ≤ Nu + 1 := by
  have hB : ∀ m, HasTicks {x : Y × KTorus | x.2 ∈ readyArc 2}
      {x : Y × KTorus | x.2 ∈ displayArc} γ u m → (m : ℝ) ≤ Ns + 3 * v * (u - s) + 3 / 2 := by
    intro m hm
    have h := hasTicks_snd_le_of_travel (W := fun t => v * t) hsu
      (fun t h1 h2 => hγ t h1 (h2.trans huw))
      (fun a b h1 h2 h3 => by
        show |D b - D a| ≤ v * b - v * a
        rw [← mul_sub]
        exact hmid a b h1 h2 h3) hm hNs.2
    have e : (fun t => v * t) u - (fun t => v * t) s = v * (u - s) := by
      show v * u - v * s = v * (u - s)
      ring
    rw [e] at h
    linarith
  obtain ⟨B, hBn⟩ := exists_nat_ge ((Ns : ℝ) + 3 * v * (u - s) + 3 / 2)
  obtain ⟨Nu, hNu⟩ := exists_tickCount_of_bdd (B := B)
    (fun m hm => by exact_mod_cast (hB m hm).trans hBn)
  have hNsu : Ns ≤ Nu := by
    by_contra hlt
    rw [not_le] at hlt
    exact hNu.2 ((hNs.1.mono_time hsu).mono_count (by omega))
  refine ⟨Nu, hNu, hNsu, hB Nu hNu.1, ?_⟩
  intro t hut htw
  have hno : ∀ a' b', u ≤ a' → a' ≤ b' → b' ≤ t →
      γ a' ∈ {x : Y × KTorus | x.2 ∈ readyArc 2} →
      γ b' ∉ {x : Y × KTorus | x.2 ∈ displayArc} := by
    intro a' b' h1 h2 h3 hr hd
    have hsa : s ≤ a' := hsu.trans h1
    have habs := hclosed a' b' h1 h2 (h3.trans htw)
    have hr' : pshift (D a') q ∈ readyArc 2 := by
      rw [← hγ a' hsa ((h2.trans h3).trans htw)]
      exact hr
    have hnd := pshift_notMem_displayArc_of_mem_readyArc habs hr'
    rw [pshift_add, sub_add_cancel] at hnd
    apply hnd
    rw [← hγ b' (hsa.trans h2) (h3.trans htw)]
    exact hd
  obtain ⟨N, hN⟩ := exists_tickCount_of_bdd (B := Nu + 1)
    (fun m hm => hasTicks_le_succ_of_no_passage hno hm hNu.2)
  exact ⟨N, hN, hNu.le_succ_of_no_passage hut hno hN⟩

/-- ★★ **The count of a pointer whose gate is closed, then open, then closed.** A last pointer
started at `1/12` whose displacement stays within `η₀ < 1/12` of zero up to `t_a`; changes at
speed at most `v` on `[t_a, t_b]` and on `[t₃, t₄]`; is within `η < 1/12` of
`(1/4)(1 − cos R t) − c` on `[t_b, t₃]`, with the lower turning point `1/12 − c` in one of
the two bands of #398; and changes by at most a sixth of a turn inside `[t₄, t₅]`. At every
flow time of `[t₄, t₅]` it has a count `N` with
`|2π N − R (t₃ − t_b)| ≤ 2π (3 v ((t_b − t_a) + (t₄ − t₃)) + 7)`. -/
theorem away_pointer_count {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ}
    {R c v η₀ η ta tb t3 t4 t5 : ℝ} (hR : 0 < R) (hta : 0 ≤ ta) (hab : ta ≤ tb)
    (hb3 : tb ≤ t3) (h34 : t3 ≤ t4) (h45 : t4 ≤ t5) (hq : rep q.1 = 1 / 12)
    (hγ : ∀ t, 0 ≤ t → t ≤ t5 → (γ t).2 = pshift (D t) q) (hη₀ : η₀ < 1 / 12)
    (hclosed0 : ∀ t, 0 ≤ t → t ≤ ta → |D t| ≤ η₀)
    (hmid1 : ∀ a b, ta ≤ a → a ≤ b → b ≤ tb → |D b - D a| ≤ v * (b - a)) (hη : 0 ≤ η)
    (hη1 : η < 1 / 12)
    (hopen : ∀ t, tb ≤ t → t ≤ t3 → |D t - (1 / 4 * (1 - Real.cos (R * t)) - c)| ≤ η)
    (hband : (-1 / 6 + η < 1 / 12 - c ∧ 1 / 12 - c ≤ 1 / 6 - η)
      ∨ (-1 / 2 + η < 1 / 12 - c ∧ 1 / 12 - c < -1 / 6 - η))
    (hmid2 : ∀ a b, t3 ≤ a → a ≤ b → b ≤ t4 → |D b - D a| ≤ v * (b - a))
    (hclosed1 : ∀ a b, t4 ≤ a → a ≤ b → b ≤ t5 → |D b - D a| ≤ 1 / 6) :
    ∀ t, t4 ≤ t → t ≤ t5 →
      ∃ N : ℕ, IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
          {x : Y × KTorus | x.2 ∈ displayArc} γ t N
        ∧ |(N : ℝ) * (2 * Real.pi) - R * (t3 - tb)|
            ≤ 2 * Real.pi * (3 * v * ((tb - ta) + (t4 - t3)) + 7) := by
  have hπ := Real.pi_pos
  have h0b : 0 ≤ tb := hta.trans hab
  have h03 : 0 ≤ t3 := h0b.trans hb3
  -- no tick before `t_a`
  have hNa : IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
      {x : Y × KTorus | x.2 ∈ displayArc} γ ta 0 := by
    refine ⟨hasTicks_zero _ _ _ _, ?_⟩
    rintro ⟨a, b, h1, -⟩
    obtain ⟨ha, hab', hb, -, hd⟩ := h1 0 (by norm_num)
    have hb0 : 0 ≤ b 0 := ha.trans hab'.le
    have hd' : (γ (b 0)).2 ∈ displayArc := hd
    have hs := abs_le.1 (hclosed0 (b 0) hb0 hb)
    rw [hγ (b 0) hb0 (hb.trans (hab.trans (hb3.trans (h34.trans h45)))),
      pshift_mem_displayArc_iff (by rw [hq]; linarith [hs.1]) (by rw [hq]; linarith [hs.2]),
      hq] at hd'
    linarith [hs.2]
  -- the count at `t_b`
  obtain ⟨Nb, hNb, -, hNb', -⟩ := count_after_transition (γ := γ) (D := D) (v := v) hab
    (le_refl tb) (fun t h1 h2 => hγ t (hta.trans h1) (h2.trans (hb3.trans (h34.trans h45))))
    hmid1 (fun a b h1 h2 h3 => by
      have e : b = a := le_antisymm (h3.trans h1) h2
      rw [e, sub_self, abs_zero]
      norm_num) hNa
  -- the count at `t₃`
  obtain ⟨N3, hN3, hN3'⟩ := offset_swing_count (γ := γ) (D := D) hR hη hη1 h0b hb3
    (fun t h1 h2 => hγ t (h0b.trans h1) (h2.trans (h34.trans h45))) hopen
    (by rw [hq]; exact hband) hNb
  -- the counts after `t₃`
  obtain ⟨N4, hN4, hN34, hN4', hwin⟩ := count_after_transition (γ := γ) (D := D) (v := v) h34
    h45 (fun t h1 h2 => hγ t (h03.trans h1) h2) hmid2 hclosed1 hN3
  intro t h4t ht5
  obtain ⟨N, hN, hN4N, hNN4⟩ := hwin t h4t ht5
  refine ⟨N, hN, ?_⟩
  have c1 : (N4 : ℝ) ≤ N := by exact_mod_cast hN4N
  have c2 : (N : ℝ) ≤ N4 + 1 := by exact_mod_cast hNN4
  have c3 : (N3 : ℝ) ≤ N4 := by exact_mod_cast hN34
  have c4 : (0 : ℝ) ≤ Nb := Nat.cast_nonneg Nb
  have c5 : (Nb : ℝ) ≤ 3 * v * (tb - ta) + 3 / 2 := by
    have := hNb'
    push_cast at this
    linarith
  have hs := abs_le.1 hN3'
  rw [abs_le]
  constructor
  · nlinarith [hs.1]
  · nlinarith [hs.2]

end Pointer

/-! ### The carriers: the count of the complementary gate -/

section Reading

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] {a b : ℕ} (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h : ℝ → ℝ}
  (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {G₁ : Matrix (ι × κ) (ι × κ) ℂ} {Y : Matrix κ κ ℂ}

/-- ★★★ **The return reading.** For the flow of #393 with its last pointer, started at `1/12`,
coupled to the complementary gate `gateOp (¬r) Y`, from a product ray on a fibre where both
profiles vanish, `z` the derivative of the last pointer's profile. Suppose the two carriers
have weight at most `ε` outside the relation up to `t_a` and again on `[t₄, t₅]`, and weight
at most `ε` inside it on `[t_b, t₃]`; that up to `t₃` the second carrier's own displacement is
within `δ₀` of `(1/4)(1 − cos R t)`; and that the displacement `c` at `t_b` of a pointer
coupled to the gate `r` with the same `z` puts `1/12 − c` in one of the two bands of #398,
with `η = δ₀ + 2|z| ε (t₃ − t_b)`. Then at every flow time of `[t₄, t₅]` the pointer has a
count `N` with `|2π N − R (t₃ − t_b)| ≤ 2π (6|z| ((t_b − t_a) + (t₄ − t₃)) + 7)`. -/
theorem coincFlow_return_reading (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
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
    (h0 : 2 * |hh.deriv_periodic.lift ψ.2| * ε * ta < 1 / 12)
    (h2 : δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb) < 1 / 12)
    (h4 : 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t5 - t4) ≤ 1 / 6)
    (hband :
      (-1 / 6 + (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb))
            < 1 / 12 - coincShift hA hC (gateOp σ τ r Y) (hh.deriv_periodic.lift ψ.2) p q tb
          ∧ 1 / 12 - coincShift hA hC (gateOp σ τ r Y) (hh.deriv_periodic.lift ψ.2) p q tb
            ≤ 1 / 6 - (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb)))
      ∨ (-1 / 2 + (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb))
            < 1 / 12 - coincShift hA hC (gateOp σ τ r Y) (hh.deriv_periodic.lift ψ.2) p q tb
          ∧ 1 / 12 - coincShift hA hC (gateOp σ τ r Y) (hh.deriv_periodic.lift ψ.2) p q tb
            < -1 / 6 - (δ₀ + 2 * |hh.deriv_periodic.lift ψ.2| * ε * (t3 - tb)))) :
    ∀ t, t4 ≤ t → t ≤ t5 →
      ∃ N : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
          {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
          (fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ (fun x y => ¬ r x y) Y) hf hh hc hch t
            ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)) t N
        ∧ |(N : ℝ) * (2 * Real.pi) - R * (t3 - tb)|
            ≤ 2 * Real.pi
              * (6 * |hh.deriv_periodic.lift ψ.2| * ((tb - ta) + (t4 - t3)) + 7) := by
  set z := hh.deriv_periodic.lift ψ.2 with hz
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have h0b : 0 ≤ tb := hta.trans hab
  have h03 : 0 ≤ t3 := h0b.trans hb3
  have h04 : 0 ≤ t4 := h03.trans h34
  -- the weight outside the relation is at most one
  have hW1 : ∀ u, arenaObs (coincProj σ τ fun x y => ¬ r x y)
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)) ≤ 1 := fun u => by
    have h1 := arenaObs_coincProj_add_not σ τ r
      (prodRay (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q))
    have h2 := arenaObs_coincProj_prodRay_nonneg σ τ r
      (arenaKick (idxFreeU hA u) p) (arenaKick (idxFreeU hC u) q)
    linarith
  have hD0 : coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q 0 = 0 := by
    rw [coincShift, intervalIntegral.integral_same, mul_zero]
  have hres := away_pointer_count (Y := KSigma (a * (b + 1) + b + 1))
    (γ := fun t => coincFlow e₁ e₂ A₀ C₀ G₁ (gateOp σ τ (fun x y => ¬ r x y) Y) hf hh hc hch t
      ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ))
    (q := ψ) (D := fun t => coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q t)
    (c := coincShift hA hC (gateOp σ τ r Y) z p q tb) (v := 2 * |z|)
    (η₀ := 2 * |z| * ε * ta) (η := δ₀ + 2 * |z| * ε * (t3 - tb)) hR hta hab hb3 h34 h45 hψ1
    (fun t _ _ => by
      rw [coincFlow_prodRay e₁ e₂ hA hC hG₁
        (gateOp_isHermitian σ τ (fun x y => ¬ r x y) hYh hYs) hf hh hc hch t p q hθ hψ]
      rfl)
    h0
    (fun t ht0 hta' => by
      have hb := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
        (ε := ε) ht0 (fun u hu0 hut =>
          (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
            (hnear0 u hu0 (hut.trans hta')))
      rw [hD0, sub_zero, sub_zero] at hb
      have hmono : 2 * |z| * ε * t ≤ 2 * |z| * ε * ta :=
        mul_le_mul_of_nonneg_left hta' (by positivity)
      exact hb.trans hmono)
    (fun s t _ hst _ => by
      have hb := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
        (ε := 1) hst (fun u _ _ =>
          (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans (hW1 u))
      linarith)
    (add_nonneg hδ₀ (mul_nonneg (by positivity) (sub_nonneg.2 hb3))) h2
    (fun t hbt ht3 => by
      have e := coincShift_gateOp_add_not σ τ r hA hC Y z p q t
      have hcl := abs_le.1 (hclock t (h0b.trans hbt) ht3)
      have hfr := abs_le.1 (abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := ε) hbt
        (fun u hbu hut => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans
          (hapart u hbu (hut.trans ht3))))
      have hmono : 2 * |z| * ε * (t - tb) ≤ 2 * |z| * ε * (t3 - tb) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [abs_le]
      constructor <;> linarith [hcl.1, hcl.2, hfr.1, hfr.2])
    hband
    (fun s t _ hst _ => by
      have hb := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
        (ε := 1) hst (fun u _ _ =>
          (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans (hW1 u))
      linarith)
    (fun s t h4s hst ht5 => by
      have hb := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
        (ε := ε) hst (fun u hsu hut =>
          (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
            (hnear1 u (h4s.trans hsu) (hut.trans ht5)))
      have hmono : 2 * |z| * ε * (t - s) ≤ 2 * |z| * ε * (t5 - t4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith)
  intro t h4t ht5
  obtain ⟨N, hN, hb⟩ := hres t h4t ht5
  refine ⟨N, hN, hb.trans (le_of_eq ?_)⟩
  ring

end Reading

/-! ### A messenger packet and the flat clock packet on the ring -/

section Ring

variable {n N M : ℕ}

/-- **The difference of the predicted angles** of a messenger packet (rest energy `μ`,
reference momentum `p₀`, packet time `t₀ + s`) and of the level of rest energy `lvl` of the
flat clock packet (packet time `−π/(2R) + s`), at the flow time `s`. -/
def packetAngleGap (n N M : ℕ) (Δ μ p₀ t₀ lvl s : ℝ) : ℝ :=
  2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ p₀ * (t₀ + s)
    - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 lvl (1 / 2)
      * (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)

/-- **The emission pointer's displacement**: that of a pointer of profile `g · trainF`, on
the fibre `0`, coupled to "within the angle `w`" times the clock's level swap. -/
noncomputable def ringEmissionShift (J μ μ₀ μ₁ w g : ℝ) (p : GenArena (ZMod (M + 1) × Fin 2))
    (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) : ℝ :=
  coincShift (diracHam_isHermitian (L := M + 1) J μ)
    (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁)
    (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
      (levelSwap (ZMod (M + 1) × Fin 2))) (-g) p q t

/-- **The run with both gates**: the flow of #393 with the first pointer coupled to "the
messenger is within the angle `w` of the clock" and the last to its complement, each times
the clock's level swap, both of profile `g · trainF` and started at `1/12` on the fibre `0`,
from the product of a messenger ray `p` and a clock ray `q`. -/
noncomputable def ringReturnRun {a b : ℕ} (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1)) (J μ μ₀ μ₁ w g : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (t : ℝ) : EchoSigma (a * (b + 1) + b) :=
  coincFlow e₁ e₂ (diracHam (L := M + 1) J μ) (deviceHam (L := M + 1) J μ₀ μ₁)
    (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
      (levelSwap (ZMod (M + 1) × Fin 2)))
    (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ ringNear (M + 1) w k k')
      (levelSwap (ZMod (M + 1) × Fin 2)))
    (scaledTrainF_periodic g) (scaledTrainF_periodic g) (contDiff_scaledTrainF g)
    (contDiff_scaledTrainF g) t
    ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q),
        ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))),
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

/-- The level swap does not move the clock carrier between sites. -/
theorem levelSwap_apply_eq_zero_of_site_ne (i j : (ZMod (M + 1) × Fin 2) × Fin 2)
    (hij : i.1.1 ≠ j.1.1) : levelSwap (ZMod (M + 1) × Fin 2) i j = 0 := by
  simp only [levelSwap, Matrix.of_apply]
  split_ifs with h
  · exact absurd (by rw [h.1]) hij
  · rfl

/-- ★★★ **The return reading for a messenger packet and the flat clock packet.** On one ring,
with both gates of "within the angle `w`" in one run; `R` the clock's rate. Suppose that at
every flow time up to `t₅` the two budgets add up to at most `ε (1 − cos δ)`; that the
messenger's predicted angle is within `w − 2δ` of both levels' predicted angles up to `t_a`
and again on `[t₄, t₅]`, and more than `w + 2δ` from both on `[t_b, t₃]`, with
`t₃ ≤ 2π n/R`; and that `2 (R/5) ε t_a < 1/12`, `2 (R/5) ε (t₃ − t_b) < 1/24` and
`2 (R/5) ε (t₅ − t₄) ≤ 1/6`. Then for some strength `0 < g ≤ R/5`: if the emission pointer's
displacement `c` at `t_b` puts `1/12 − c` in one of the two bands of #398 with
`η = 1/24 + 2 g ε (t₃ − t_b)`, the complementary pointer has at every flow time of
`[t₄, t₅]` a count `N'` with
`|2π N' − R (t₃ − t_b)| ≤ 2π (6 g ((t_b − t_a) + (t₄ − t₃)) + 7)`. -/
theorem flat_clock_return_reading (hn : 0 < n) (hN : 0 < N)
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
    (h45 : t4 ≤ t5) (ht3T : t3 ≤ 2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ)
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
    (hS0 : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * ta < 1 / 12)
    (hS2 : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (t3 - tb) < 1 / 24)
    (hS4 : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (t5 - t4) ≤ 1 / 6) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ (((-1 / 6 + (1 / 24 + 2 * g * ε * (t3 - tb))
              < 1 / 12 - ringEmissionShift (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                  (chainRay _ hψ) (deviceRay _ hΨ) tb
            ∧ 1 / 12 - ringEmissionShift (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                  (chainRay _ hψ) (deviceRay _ hΨ) tb
              ≤ 1 / 6 - (1 / 24 + 2 * g * ε * (t3 - tb)))
          ∨ (-1 / 2 + (1 / 24 + 2 * g * ε * (t3 - tb))
              < 1 / 12 - ringEmissionShift (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                  (chainRay _ hψ) (deviceRay _ hΨ) tb
            ∧ 1 / 12 - ringEmissionShift (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                  (chainRay _ hψ) (deviceRay _ hΨ) tb
              < -1 / 6 - (1 / 24 + 2 * g * ε * (t3 - tb)))) →
        ∀ t, t4 ≤ t → t ≤ t5 →
          ∃ N' : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
              {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
              (ringReturnRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) w g
                (chainRay _ hψ) (deviceRay _ hΨ)) t N'
            ∧ |(N' : ℝ) * (2 * Real.pi)
                  - ringRate (1200 * n * N) M (1 / 2) Δ * (t3 - tb)|
                ≤ 2 * Real.pi * (6 * g * ((tb - ta) + (t4 - t3)) + 7)) := by
  have hπ := Real.pi_pos
  have hK : 0 < 1200 * n * N := by positivity
  have hR : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hR0 : 0 < ringRate (1200 * n * N) M (1 / 2) Δ := by linarith
  obtain ⟨g, hΨ, hg0, hg5, hsw⟩ := flat_clock_swing (M := M) hn hN hM hΔ0 hΔ
  refine ⟨g, hΨ, hg0, hg5, fun hband => ?_⟩
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
  have hgε : ∀ x : ℝ, 0 ≤ x → 2 * g * ε * x ≤ 2 * (R / 5) * ε * x := by
    intro x hx
    have : 0 ≤ ε * x := mul_nonneg hε hx
    nlinarith
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
        ((outside_arcs_flat_clock_le hn hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
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
        ((outside_arcs_flat_clock_le hn hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
          (hbudget s hs0 hs))) hcos
  have H := coincFlow_return_reading e₁ e₂
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
    (scaledTrainF_lift_zero g) (scaledTrainF_lift_zero g) hrep (R := R) (δ₀ := 1 / 24)
    (ε := ε) (ta := ta) (tb := tb) (t3 := t3) (t4 := t4) (t5 := t5) hR0 (by norm_num) hε hta
    hab hb3 h34 h45
  simp only [hz, abs_neg, abs_of_pos hg0] at H
  refine H ?_ ?_ ?_ ?_ ?_ ?_ ?_ hband
  · intro t ht0 ht3
    have h := hsw t ht0 (ht3.trans ht3T)
    rw [clockPointerShift_trainF_eq, hz] at h
    exact h
  · exact fun s hs0 hs =>
      key_near s hs0 (hs.trans (hab.trans (hb3.trans (h34.trans h45)))) (hnear0 s hs0 hs)
  · exact fun s hbs hs =>
      key_apart s ((hta.trans hab).trans hbs) (hs.trans (h34.trans h45)) (hapart s hbs hs)
  · exact fun s h4s hs => key_near s ((h03.trans h34).trans h4s) hs (hnear1 s h4s hs)
  · exact (hgε ta hta).trans_lt hS0
  · have := hgε (t3 - tb) (sub_nonneg.2 hb3)
    linarith
  · exact (hgε (t5 - t4) (sub_nonneg.2 h45)).trans hS4

end Ring

end CSD.RecordLayer

end
