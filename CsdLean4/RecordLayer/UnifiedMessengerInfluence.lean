/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCoincidenceFlow
public import CsdLean4.RecordLayer.DiracPointerClick

/-!
# What a messenger does to a gated pointer

**Category:** 7-SigmaLayer. BACKLOG #442, fourth brick (Task 4 of the author's plan "Unified
records, quantum measurement and emergent spacetime", the causal bridge;
`specs/unified-records-spacetime-task-plans.md` §2, item 2, "demonstrated under a non-zero
coupling").

The relay pointer of the radar is coupled to a clock's operator `Y` through the gate "the
messenger is not near the clock". `RecordLayer/UnifiedCoincidenceFlow.lean` shows the
displacement while apart plus the displacement while together is the ungated clock's. This
module states what follows for two runs that differ only in the messenger.

* ★★ `abs_arenaObs_conj_le` — for a Hermitian idempotent `Q`: `|⟨Q Z Q⟩| ≤ ‖Z‖ ⟨Q⟩`;
* `gateOp_eq_conj`, `abs_arenaObs_gateOp_le` — a gated operator reads at most `‖1 ⊗ Y‖` times
  the weight of its gate;
* ★★ `abs_coincShift_gateOp_sub_le` — between two flow times a gated pointer moves by at most
  `2 |z| ‖1 ⊗ Y‖` times the accumulated weight of its gate;
* ★★ `coincShift_not_sub_messenger` — **two runs that differ only in the messenger differ, at
  the pointer gated by "apart", by exactly the difference of their displacements while
  together**;
* `coincShift_gateOp_eq_zero_of_never`, `coincShift_not_eq_free_of_never` — a messenger that
  is never near leaves the pointer to follow the clock alone;
* ★★★ `messenger_influence_eq` — **against a messenger that is never near, the messenger's
  whole effect on the pointer is minus its displacement while together**;
* ★★★ `messenger_influence_dwell` — **the effect over a dwell.** If over `[s₁, s₂]` the
  messenger is apart with weight at most `ε`, then over that interval the pointer falls
  behind the pointer of the run with the absent messenger by the clock's own swing over the
  interval, within `2 |z| ‖1 ⊗ Y‖ ε (s₂ − s₁)`.

## Honest scope

⚠️ **A difference of displacements, not of counts.** The plan's §2 asked for the relay
reading's count to differ with the messenger removed. That is not proved, and for the
family of UD-196 it is not expected in the relay's window: the dwell is about `6δK`, the
pointer's rate is at most `R₀/5`, so the effect is at most about `2.4 · 10⁻⁵` of a turn,
far below a tick. This estimate is arithmetic done by hand, not a Lean statement.

⚠️ **"Removed" is not available in the arena.** The messenger is a factor of the product
ray and cannot be absent. The comparison run has a messenger that is never near the clock up
to the time considered. No such messenger is exhibited.

⚠️ **Conditional on the weights of the gate along the two orbits.** They are hypotheses; the
family's messenger is not put in.

⚠️ **On the fibre where the profiles vanish**: `coincShift` is the displacement along the
uncoupled orbits of a product ray. The influence is of the messenger on a pointer, through
the gate; it is local to the encounter and is not carried along the chain by this theorem.

⚠️ **`Y` does not move the clock between sites** (the level swap does not).

References: `specs/BACKLOG.md` #442; `specs/unified-record-spacetime-plan.md` (UD-145,
UD-146, UD-196, UD-250); `specs/unified-records-spacetime-task-plans.md` (§2);
`RecordLayer/UnifiedCoincidence.lean` (`coincProj`, `gateOp`, `coincProj_mul_one_kronecker`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (`coincShift`, `coincShift_gateOp_add_not`,
`continuous_arenaObs_prodRay_free`); `RecordLayer/UnifiedTriCarrier.lean` (`triRun`,
`coincShift_gate_fst`); `RecordLayer/DiracPointerClick.lean` (`arenaObs_mk_eq_inner`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization Kronecker

namespace CSD.RecordLayer

/-! ### An operator between two copies of a projector -/

section Proj

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- ★★ **An operator read through a projector.** For a Hermitian idempotent `Q`:
`|⟨Q Z Q⟩| ≤ ‖Z‖ ⟨Q⟩` at every ray. -/
theorem abs_arenaObs_conj_le {Z Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (p : GenArena n) : |arenaObs (Q * Z * Q) p| ≤ ‖Z‖ * arenaObs Q p := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 : Matrix.toEuclideanLin (Q * Z * Q) v
        = Matrix.toEuclideanLin (Q * Z) (Matrix.toEuclideanLin Q v) :=
      DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 (Q * Z) Q) v
    have h2 : ∀ x : EuclideanSpace ℂ n, Matrix.toEuclideanLin (Q * Z) x
        = Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Z x) := fun x =>
      DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 Q Z) x
    have hmulQ : Matrix.toEuclideanLin (Q * Q) v
        = Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q v) :=
      DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 Q Q) v
    have hadj : LinearMap.adjoint (Matrix.toEuclideanLin Q) = Matrix.toEuclideanLin Q := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hQ.eq]
    have hsw : ∀ y : EuclideanSpace ℂ n, inner ℂ v (Matrix.toEuclideanLin Q y)
        = inner ℂ (Matrix.toEuclideanLin Q v) y := fun y => by
      have := LinearMap.adjoint_inner_left (Matrix.toEuclideanLin Q) y v
      rw [hadj] at this
      exact this.symm
    have hQw : (inner ℂ v (Matrix.toEuclideanLin Q v)).re
        = ‖Matrix.toEuclideanLin Q v‖ ^ 2 := by
      have h3 : inner ℂ v (Matrix.toEuclideanLin Q v)
          = inner ℂ (Matrix.toEuclideanLin Q v) (Matrix.toEuclideanLin Q v) := by
        rw [← hsw, ← hmulQ, hQQ]
      rw [h3, inner_self_eq_norm_sq_to_K]
      norm_cast
    have hZ : ‖Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v)‖
        ≤ ‖Z‖ * ‖Matrix.toEuclideanLin Q v‖ := by
      have hh : Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v)
          = (EuclideanSpace.equiv n ℂ).symm (Z *ᵥ (Matrix.toEuclideanLin Q v).ofLp) := rfl
      rw [hh]
      exact Matrix.l2_opNorm_mulVec Z _
    have hin : |(inner ℂ (Matrix.toEuclideanLin Q v)
        (Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v))).re|
        ≤ ‖Matrix.toEuclideanLin Q v‖ * (‖Z‖ * ‖Matrix.toEuclideanLin Q v‖) :=
      (Complex.abs_re_le_norm _).trans
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hZ (norm_nonneg _)))
    rw [arenaObs_mk_eq_inner, arenaObs_mk_eq_inner, h1, h2, hsw, hQw, abs_div,
      abs_of_pos (pow_pos hv0 2), div_le_iff₀ (pow_pos hv0 2), mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero 2 hv0.ne')]
    calc |(inner ℂ (Matrix.toEuclideanLin Q v)
          (Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v))).re|
        ≤ ‖Matrix.toEuclideanLin Q v‖ * (‖Z‖ * ‖Matrix.toEuclideanLin Q v‖) := hin
      _ = ‖Z‖ * ‖Matrix.toEuclideanLin Q v‖ ^ 2 := by ring

end Proj

/-! ### A gated pointer and its gate's weight -/

section Gates

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ}

/-- A gated operator is its operator between two copies of the gate's projector, when the
operator does not move the second carrier between sites. -/
theorem gateOp_eq_conj {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) :
    gateOp σ τ r Y
      = coincProj σ τ r * ((1 : Matrix ι ι ℂ) ⊗ₖ Y) * coincProj σ τ r := by
  rw [gateOp, Matrix.mul_assoc, ← coincProj_mul_one_kronecker σ τ r hY, ← Matrix.mul_assoc,
    coincProj_mul_self]

/-- A gated operator reads at most `‖1 ⊗ Y‖` times the weight of its gate. -/
theorem abs_arenaObs_gateOp_le {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0)
    (x : GenArena (ι × κ)) :
    |arenaObs (gateOp σ τ r Y) x|
      ≤ ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖ * arenaObs (coincProj σ τ r) x := by
  rw [gateOp_eq_conj σ τ r hY]
  exact abs_arenaObs_conj_le (coincProj_isHermitian σ τ r) (coincProj_mul_self σ τ r) x

/-- ★★ **A gated pointer moves at most as its gate's weight allows.** Between the flow times
`s₁ ≤ s₂` the displacement of the pointer coupled to `gateOp r Y` changes by at most
`2 |z| ‖1 ⊗ Y‖` times the accumulated weight of the gate. -/
theorem abs_coincShift_gateOp_sub_le (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (z : ℝ) (p : GenArena ι)
    (q : GenArena κ) {s₁ s₂ : ℝ} (h12 : s₁ ≤ s₂) :
    |coincShift hA hC (gateOp σ τ r Y) z p q s₂ - coincShift hA hC (gateOp σ τ r Y) z p q s₁|
      ≤ 2 * |z| * ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖
        * ∫ s in s₁..s₂, arenaObs (coincProj σ τ r)
            (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) := by
  unfold coincShift
  have hF := continuous_arenaObs_prodRay_free hA hC (gateOp σ τ r Y) p q
  have hW := continuous_arenaObs_prodRay_free hA hC (coincProj σ τ r) p q
  rw [← mul_sub, intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable _ _)
    (hF.intervalIntegrable _ _), abs_mul, abs_mul, abs_neg, abs_two]
  have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun s : ℝ => arenaObs (gateOp σ τ r Y)
      (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q))) h12
  have h2 : ∫ s in s₁..s₂, |arenaObs (gateOp σ τ r Y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q))|
      ≤ ∫ s in s₁..s₂, ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖ * arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) :=
    intervalIntegral.integral_mono_on h12 (hF.abs.intervalIntegrable _ _)
      ((continuous_const.mul hW).intervalIntegrable _ _)
      fun s _ => abs_arenaObs_gateOp_le σ τ r hY _
  rw [intervalIntegral.integral_const_mul] at h2
  calc 2 * |z| * |∫ s in s₁..s₂, arenaObs (gateOp σ τ r Y)
          (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q))|
      ≤ 2 * |z| * (‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖ * ∫ s in s₁..s₂, arenaObs (coincProj σ τ r)
          (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg zero_le_two (abs_nonneg z))
    _ = _ := by ring

/-- ★★ **Two runs that differ only in the messenger.** At the pointer gated by "apart" their
displacements differ by exactly the difference of the displacements while together, taken in
the other order. -/
theorem coincShift_not_sub_messenger (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (Y : Matrix κ κ ℂ) (z : ℝ) (p p' : GenArena ι) (q : GenArena κ) (t : ℝ) :
    coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q t
        - coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p' q t
      = coincShift hA hC (gateOp σ τ r Y) z p' q t
        - coincShift hA hC (gateOp σ τ r Y) z p q t := by
  have h1 := coincShift_gateOp_add_not σ τ r hA hC Y z p q t
  have h2 := coincShift_gateOp_add_not σ τ r hA hC Y z p' q t
  linarith

/-- A messenger that is never together with the clock up to `t` does not move the pointer
gated by "together". -/
theorem coincShift_gateOp_eq_zero_of_never (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (z : ℝ) (p : GenArena ι)
    (q : GenArena κ) {t : ℝ} (ht : 0 ≤ t)
    (hnever : ∀ s, 0 ≤ s → s ≤ t → arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) = 0) :
    coincShift hA hC (gateOp σ τ r Y) z p q t = 0 := by
  have h := abs_coincShift_gateOp_sub_le σ τ r hA hC hY z p q ht
  have h0 : coincShift hA hC (gateOp σ τ r Y) z p q 0 = 0 := by
    simp [coincShift]
  have hint : ∫ s in (0 : ℝ)..t, arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => by
      rw [Set.uIcc_of_le ht] at hs
      exact hnever s hs.1 hs.2]
    simp
  rw [h0, sub_zero, hint, mul_zero] at h
  exact abs_nonpos_iff.1 h

/-- With such a messenger the pointer gated by "apart" follows the clock alone. -/
theorem coincShift_not_eq_free_of_never (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (z : ℝ) (p : GenArena ι)
    (q : GenArena κ) {t : ℝ} (ht : 0 ≤ t)
    (hnever : ∀ s, 0 ≤ s → s ≤ t → arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) = 0) :
    coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q t
      = -2 * z * ∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q) := by
  have h1 := coincShift_gateOp_add_not σ τ r hA hC Y z p q t
  rw [coincShift_gateOp_eq_zero_of_never σ τ r hA hC hY z p q ht hnever, zero_add] at h1
  exact h1

/-- ★★★ **The messenger's whole effect on the pointer.** Against a run whose messenger `p'` is
never together with the clock up to `t`, the pointer gated by "apart" of the run with the
messenger `p` is behind by exactly its displacement while together. -/
theorem messenger_influence_eq (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (z : ℝ) (p p' : GenArena ι)
    (q : GenArena κ) {t : ℝ} (ht : 0 ≤ t)
    (hnever : ∀ s, 0 ≤ s → s ≤ t → arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA s) p') (arenaKick (idxFreeU hC s) q)) = 0) :
    coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p' q t
        - coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q t
      = coincShift hA hC (gateOp σ τ r Y) z p q t := by
  rw [coincShift_not_sub_messenger σ τ r hA hC Y z p' p q t,
    coincShift_gateOp_eq_zero_of_never σ τ r hA hC hY z p' q ht hnever, sub_zero]

/-- ★★★ **The effect over a dwell.** Over `[s₁, s₂]` the messenger `p` is apart from the clock
with weight at most `ε`; the messenger `p'` is never together with it up to `s₂`. Then over
that interval the pointer gated by "apart" of the run with `p` falls behind the pointer of
the run with `p'` by the clock's own swing `−2 z ∫ ⟨Y⟩` over the interval, within
`2 |z| ‖1 ⊗ Y‖ ε (s₂ − s₁)`. -/
theorem messenger_influence_dwell (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (z : ℝ) (p p' : GenArena ι)
    (q : GenArena κ) {s₁ s₂ ε : ℝ} (h01 : 0 ≤ s₁) (h12 : s₁ ≤ s₂)
    (hnear : ∀ s, s₁ ≤ s → s ≤ s₂ → arenaObs (coincProj σ τ (fun s s' => ¬ r s s'))
      (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hnever : ∀ s, 0 ≤ s → s ≤ s₂ → arenaObs (coincProj σ τ r)
      (prodRay (arenaKick (idxFreeU hA s) p') (arenaKick (idxFreeU hC s) q)) = 0) :
    |(coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p' q s₂
          - coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p' q s₁)
        - (coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q s₂
          - coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q s₁)
        - -2 * z * ∫ s in s₁..s₂, arenaObs Y (arenaKick (idxFreeU hC s) q)|
      ≤ 2 * |z| * ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖ * ε * (s₂ - s₁) := by
  have hcY := continuous_arenaObs_idxFreeU hC Y q
  have f2 := coincShift_not_eq_free_of_never σ τ r hA hC hY z p' q (h01.trans h12) hnever
  have f1 := coincShift_not_eq_free_of_never σ τ r hA hC hY z p' q h01
    fun s hs hs1 => hnever s hs (hs1.trans h12)
  have hfree : coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p' q s₂
        - coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p' q s₁
      = -2 * z * ∫ s in s₁..s₂, arenaObs Y (arenaKick (idxFreeU hC s) q) := by
    rw [f2, f1, ← mul_sub, intervalIntegral.integral_interval_sub_left
      (hcY.intervalIntegrable _ _) (hcY.intervalIntegrable _ _)]
  have hW := continuous_arenaObs_prodRay_free hA hC
    (coincProj σ τ (fun s s' => ¬ r s s')) p q
  have hb := abs_coincShift_gateOp_sub_le σ τ (fun s s' => ¬ r s s') hA hC hY z p q h12
  have hint : ∫ s in s₁..s₂, arenaObs (coincProj σ τ (fun s s' => ¬ r s s'))
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q))
      ≤ ε * (s₂ - s₁) := by
    have := intervalIntegral.integral_mono_on h12 (hW.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := ε)) fun s hs => hnear s hs.1 hs.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  rw [hfree, sub_sub_cancel_left, abs_neg]
  calc |coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q s₂
          - coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q s₁|
      ≤ 2 * |z| * ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖
        * ∫ s in s₁..s₂, arenaObs (coincProj σ τ (fun s s' => ¬ r s s'))
            (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) := hb
    _ ≤ 2 * |z| * ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖ * (ε * (s₂ - s₁)) :=
        mul_le_mul_of_nonneg_left hint
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg z)) (norm_nonneg _))
    _ = _ := by ring

end Gates

end CSD.RecordLayer

end
