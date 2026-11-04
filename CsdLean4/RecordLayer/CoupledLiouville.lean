/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CoupledDetector
public import CsdLean4.Mathlib.Analysis.ODE.FlowDerivative
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The coupled detector flow preserves Lebesgue measure

**Category:** 7-SigmaLayer (the record layer). BACKLOG #291, residue of ~~#251~~.

~~#251~~ generated the detectors by `H = p²/(2m) + g Σ_j χ(x − j) η_j` (`CoupledDetector.lean`)
and bounded the back-reaction. Here its flow on the arena `(x, p, ζ)` is shown to preserve Lebesgue
measure (Liouville).

## The proof

* **The flow splits.** The field does not read the registers, so the flow is a skew product: the
  device moves by the planar flow `φ_t` of `(p/m, F(x))`, and each register shifts by an amount
  fixed by the device's start (`detFlow_eq_shift`).
* **The planar flow preserves area.** The field is `C¹` for a `C²` profile, so `φ_t` is
  differentiable in the start with derivative the variational solution `Y`
  (`hasFDerivAt_flow_of_variational`). The field is trace-free (`ẋ` does not read `x`, `ṗ` does not
  read `p`), so `det Y` is constant, equal to `1`. Mathlib's change of variables
  (`lintegral_abs_det_fderiv_eq_addHaar_image`) then gives `vol (φ_t '' A) = vol A`.
* **The shear preserves volume** (a translation in `ζ` depending on `(x, p)`), so the skew product
  does (`MeasurePreserving.skew_product`).

## What is proved

* `detFlow_eq_shift`, `planarFlow`, `regShift`, ★★ `detFlow_eq_skew` (**the coupled flow is a skew
  product**); `planarFlow_zero`, `planarFlow_add`, `planarFlow_neg`, `planarFlow_neg_inv`;
  `planarField`, `hasDerivAt_planarFlow`, `continuous_planarFlow_time`, `lipschitz_planarFlow`,
  `continuous_planarFlow`, `continuous_regShift`;
* for a `C²` profile (`χ'` differentiable with continuous derivative `d2`): `forceDeriv`,
  `hasDerivAt_force`, `continuous_forceDeriv`, `planarDeriv`, `planarDeriv_apply`,
  `hasFDerivAt_planarField`, `continuous_planarDeriv`, ★ `contDiff_planarField`;
  `det_eq_entries`; ★★★ `exists_hasFDerivAt_planarFlow` (**the planar flow is differentiable in the
  start with determinant one**, forward in time);
* ★★ `volume_image_planarFlow`, ★★★ `measurePreserving_planarFlow` (**area preserved at every
  time**); ★★★ `measurePreserving_detFlow`, ★★★ `measurePreserving_coupledEvolve` (**the coupled
  detector flow preserves Lebesgue measure on `(x, p, ζ)`, at every time**).

## Honest scope

* **`C²` profile.** `DetProfile` asks for `C¹` with a Lipschitz derivative; Liouville here takes a
  second derivative `d2`, continuous, as a hypothesis. A smooth bump satisfies both.
* **`η` stays a parameter** (`CoupledDetector.lean`): the measure is Lebesgue on `(x, p, ζ)` for
  each preparation's `η`. On the full arena `(x, p, ζ, η)` the flow fixes `η`, so Fubini over `η`
  gives the same statement; that gluing is not written out.

## References

`CoupledDetector.lean` (`detFlow`, `detField`, `force`); `Mathlib/Analysis/ODE/FlowDerivative.lean`
(`hasFDerivAt_flow_of_variational`, `exists_linearODE_solution_Icc`);
`Mathlib/MeasureTheory/Function/Jacobian.lean` (`lintegral_abs_det_fderiv_eq_addHaar_image`);
`Mathlib/MeasureTheory/Measure/Prod.lean` (`MeasurePreserving.skew_product`,
`measurePreserving_prodAssoc`); `specs/BACKLOG.md` #291, #251; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer.Coupled

variable {L : ℕ} (P : DetProfile) {m g : ℝ} (η : Fin L → ℝ) (hm : 0 < m) (hg : 0 ≤ g)

/-! ### The flow splits -/

/-- **The registers are shifted, not read**: the flow from `(x, p, ζ)` is the flow from
`(x, p, 0)` with `ζ` added to the registers. -/
theorem detFlow_eq_shift (t x p : ℝ) (ζ : Fin L → ℝ) :
    detFlow P η hm hg t (x, p, ζ) = detFlow P η hm hg t (x, p, 0) + (0, 0, ζ) := by
  have hv := lipschitz_detField P η hm hg
  have h := hv.odeFlow_eq_of_hasDerivAt
    (γ := fun s => detFlow P η hm hg s (x, p, 0) + ((0 : ℝ), (0 : ℝ), ζ))
    (fun s => by
      have := (hasDerivAt_detFlow P η hm hg (x, p, 0) s).add_const ((0 : ℝ), (0 : ℝ), ζ)
      convert this using 1
      simp [detField])
    (x := (x, p, ζ)) (by simp [detFlow_zero])
  exact (congrFun h t).symm

/-- **The planar flow**: the device's position and momentum. -/
def planarFlow (t : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  ((detFlow P η hm hg t (u.1, u.2, 0)).1, (detFlow P η hm hg t (u.1, u.2, 0)).2.1)

/-- **The registers' shift** from a device start. -/
def regShift (t : ℝ) (u : ℝ × ℝ) : Fin L → ℝ := (detFlow P η hm hg t (u.1, u.2, 0)).2.2

/-- **The coupled flow as a skew product.** -/
theorem detFlow_eq_skew (t : ℝ) (z : DetState L) :
    detFlow P η hm hg t z = ((planarFlow P η hm hg t (z.1, z.2.1)).1,
      (planarFlow P η hm hg t (z.1, z.2.1)).2, z.2.2 + regShift P η hm hg t (z.1, z.2.1)) := by
  obtain ⟨x, p, ζ⟩ := z
  rw [detFlow_eq_shift]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [planarFlow, regShift, add_comm]

theorem planarFlow_zero (u : ℝ × ℝ) : planarFlow P η hm hg 0 u = u := by
  simp [planarFlow, detFlow_zero]

/-- **The group law of the planar flow.** -/
theorem planarFlow_add (s t : ℝ) (u : ℝ × ℝ) :
    planarFlow P η hm hg (s + t) u = planarFlow P η hm hg t (planarFlow P η hm hg s u) := by
  have h1 := detFlow_add P η hm hg s t (u.1, u.2, 0)
  have h2 := detFlow_eq_skew P η hm hg t (detFlow P η hm hg s (u.1, u.2, 0))
  show ((detFlow P η hm hg (s + t) (u.1, u.2, 0)).1, (detFlow P η hm hg (s + t) (u.1, u.2, 0)).2.1)
    = planarFlow P η hm hg t (planarFlow P η hm hg s u)
  rw [h1, h2]
  rfl

theorem planarFlow_neg (t : ℝ) (u : ℝ × ℝ) :
    planarFlow P η hm hg (-t) (planarFlow P η hm hg t u) = u := by
  rw [← planarFlow_add, add_neg_cancel, planarFlow_zero]

/-- **The planar field**: `(p/m, F(x))`. -/
def planarField (P : DetProfile) (m g : ℝ) (η : Fin L → ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (m⁻¹ * u.2, force P g η u.1)

theorem hasDerivAt_planarFlow (u : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun t => planarFlow P η hm hg t u)
      (planarField P m g η (planarFlow P η hm hg t u)) t := by
  have h := (hasDerivAt_pos P η hm hg (u.1, u.2, 0) t).prodMk
    (hasDerivAt_mom P η hm hg (u.1, u.2, 0) t)
  convert h using 1
  · rfl
  · rw [div_eq_inv_mul]
    rfl

theorem continuous_planarFlow_time (u : ℝ × ℝ) : Continuous fun t => planarFlow P η hm hg t u :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_planarFlow P η hm hg u t).continuousAt

/-- **The planar flow is Lipschitz in the start**, with the coupled flow's constant. -/
theorem lipschitz_planarFlow (t : ℝ) :
    LipschitzWith ⟨Real.exp ((Real.toNNReal (1 / m + g * (∑ j, |η j|) * P.Kd + g * P.Kχ) : ℝ)
      * |t|), (Real.exp_pos _).le⟩ (planarFlow P η hm hg t) := by
  have hv := (lipschitz_detField P η hm hg).lipschitzWith_odeFlow t
  refine LipschitzWith.of_dist_le_mul fun u w => ?_
  have h1 : dist (planarFlow P η hm hg t u) (planarFlow P η hm hg t w)
      ≤ dist (detFlow P η hm hg t (u.1, u.2, 0)) (detFlow P η hm hg t (w.1, w.2, 0)) := by
    show dist ((detFlow P η hm hg t (u.1, u.2, 0)).1, (detFlow P η hm hg t (u.1, u.2, 0)).2.1)
      ((detFlow P η hm hg t (w.1, w.2, 0)).1, (detFlow P η hm hg t (w.1, w.2, 0)).2.1) ≤ _
    rw [Prod.dist_eq, Prod.dist_eq (x := detFlow P η hm hg t (u.1, u.2, 0)),
      Prod.dist_eq (x := (detFlow P η hm hg t (u.1, u.2, 0)).2)]
    exact max_le_max le_rfl (le_max_left _ _)
  have h2 := hv.dist_le_mul (u.1, u.2, (0 : Fin L → ℝ)) (w.1, w.2, 0)
  have h3 : dist ((u.1, u.2, (0 : Fin L → ℝ)) : DetState L) (w.1, w.2, 0) = dist u w := by
    rw [Prod.dist_eq, Prod.dist_eq (x := (u.2, (0 : Fin L → ℝ))), dist_self,
      max_eq_left dist_nonneg, Prod.dist_eq (x := u)]
  rw [h3] at h2
  exact h1.trans h2

theorem continuous_planarFlow (t : ℝ) : Continuous (planarFlow P η hm hg t) :=
  (lipschitz_planarFlow P η hm hg t).continuous

/-! ### The planar field is `C¹` for a `C²` profile -/

variable {d2 : ℝ → ℝ}

/-- `F'(x) = −g Σ_j χ''(x − j) η_j`. -/
def forceDeriv (d2 : ℝ → ℝ) (x : ℝ) : ℝ := -(g * ∑ j : Fin L, d2 (x - (j : ℕ)) * η j)

theorem hasDerivAt_force (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x) (x : ℝ) :
    HasDerivAt (force P g η) (forceDeriv η (g := g) d2 x) x := by
  have hs : HasDerivAt (fun y => ∑ j : Fin L, P.dχ (y - (j : ℕ)) * η j)
      (∑ j : Fin L, d2 (x - (j : ℕ)) * η j) x :=
    HasDerivAt.fun_sum fun j _ => (((hd2 _).comp x
      ((hasDerivAt_id x).sub_const _)).mul_const (η j)).congr_deriv (by simp)
  exact (hs.const_mul g).neg

theorem continuous_forceDeriv (hc2 : Continuous d2) : Continuous (forceDeriv η (g := g) d2) :=
  (continuous_const.mul (continuous_finsetSum _ fun _ _ =>
    (hc2.comp (continuous_id.sub continuous_const)).mul continuous_const)).neg

/-- **The planar field's derivative**: `(a, b) ↦ (b/m, F'(x) a)`. -/
def planarDeriv (d2 : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (m⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (forceDeriv η (g := g) d2 z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem planarDeriv_apply (z w : ℝ × ℝ) :
    planarDeriv η (m := m) (g := g) d2 z w = (m⁻¹ * w.2, forceDeriv η (g := g) d2 z.1 * w.1) :=
  rfl

theorem hasFDerivAt_planarField (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x) (z : ℝ × ℝ) :
    HasFDerivAt (planarField P m g η) (planarDeriv η (m := m) (g := g) d2 z) z := by
  have h1 : HasFDerivAt (fun u : ℝ × ℝ => m⁻¹ * u.2) (m⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    (hasFDerivAt_snd).const_mul m⁻¹
  have h2 : HasFDerivAt (fun u : ℝ × ℝ => force P g η u.1)
      (forceDeriv η (g := g) d2 z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    (hasDerivAt_force P η hd2 z.1).comp_hasFDerivAt z hasFDerivAt_fst
  exact h1.prodMk h2

theorem continuous_planarDeriv (hc2 : Continuous d2) :
    Continuous (planarDeriv η (m := m) (g := g) d2) := by
  have he : planarDeriv η (m := m) (g := g) d2 = fun z =>
      (m⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0
        + forceDeriv η (g := g) d2 z.1
          • (0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    funext z
    ext <;> simp [planarDeriv]
  rw [he]
  exact continuous_const.add
    (((continuous_forceDeriv η hc2).comp continuous_fst).smul continuous_const)

theorem contDiff_planarField (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x) (hc2 : Continuous d2) :
    ContDiff ℝ 1 (planarField P m g η) :=
  contDiff_one_iff_hasFDerivAt.2
    ⟨_, continuous_planarDeriv η hc2, hasFDerivAt_planarField P η hd2⟩

/-! ### The planar flow's derivative has determinant one -/

theorem det_eq_entries (A : ℝ × ℝ →L[ℝ] ℝ × ℝ) :
    A.det = (A (1, 0)).1 * (A (0, 1)).2 - (A (1, 0)).2 * (A (0, 1)).1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one]
  ring

/-- ★★★ **The planar flow is differentiable in the start, with determinant one** (forward time):
the derivative is the variational solution along the orbit, and the field is trace-free. -/
theorem exists_hasFDerivAt_planarFlow (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x)
    (hc2 : Continuous d2) (u : ℝ × ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ × ℝ, HasFDerivAt (planarFlow P η hm hg t) D u ∧ D.det = 1 := by
  set T : ℝ := t + 1 with hTdef
  have hT : 0 < T := by linarith
  have htT : t ∈ Icc 0 T := ⟨ht, by linarith⟩
  set f := planarField P m g η with hfdef
  have hf : ContDiff ℝ 1 f := contDiff_planarField P η hd2 hc2
  set Kc : ℝ := ((Real.toNNReal (1 / m + g * (∑ j, |η j|) * P.Kd + g * P.Kχ) : ℝ)) with hKc
  set Λ : ℝ := Real.exp (Kc * T) with hΛ
  have hΛ0 : 0 ≤ Λ := (Real.exp_pos _).le
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_planarFlow_time P η hm hg u).continuousOn
  have hlipT : ∀ s ∈ Icc 0 T, LipschitzWith ⟨Λ, hΛ0⟩ (planarFlow P η hm hg s) := fun s hs =>
    (lipschitz_planarFlow P η hm hg s).weaken (by
      show Real.exp (Kc * |s|) ≤ Λ
      rw [abs_of_nonneg hs.1]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 (by positivity)))
  have hαK : ∀ y ∈ Metric.closedBall u 1, ∀ s ∈ Icc 0 T,
      planarFlow P η hm hg s y ∈ Metric.closedBall (0 : ℝ × ℝ) (B + Λ) := by
    intro y hy s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (hlipT s hs).dist_le_mul y u
    have h2 : dist y u ≤ 1 := hy
    calc ‖planarFlow P η hm hg s y‖
        ≤ ‖planarFlow P η hm hg s u‖
          + dist (planarFlow P η hm hg s y) (planarFlow P η hm hg s u) := by
          rw [dist_eq_norm]
          exact (norm_le_insert' _ _).trans (by rw [add_comm])
      _ ≤ B + Λ * 1 := add_le_add (hB s hs) (h1.trans (mul_le_mul_of_nonneg_left h2 hΛ0))
      _ = B + Λ := by ring
  -- the variational solution
  set A : ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ) →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ × ℝ) := fun s =>
    ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)
      (planarDeriv η (m := m) (g := g) d2 (planarFlow P η hm hg s u)) with hAdef
  have hAc : Continuous A :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)).continuous.comp
      ((continuous_planarDeriv η hc2).comp (continuous_planarFlow_time P η hm hg u))
  have hDc : Continuous fun s =>
      planarDeriv η (m := m) (g := g) d2 (planarFlow P η hm hg s u) :=
    (continuous_planarDeriv η hc2).comp (continuous_planarFlow_time P η hm hg u)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hDc.continuousOn
  have hM : ∀ s ∈ Icc 0 T, ‖A s‖
      ≤ ‖ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)‖ * max M₀ 0 := fun s hs =>
    ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hM₀ s hs).trans (le_max_left _ _))
        (ContinuousLinearMap.opNorm_nonneg _))
  have hC0 : 0 ≤ ‖ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)‖ * max M₀ 0 :=
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (le_max_right M₀ 0)
  obtain ⟨Y, hY0, hYd⟩ := exists_linearODE_solution_Icc A hT hC0
    (fun Z => (hAc.clm_apply continuous_const).continuousOn) hM (1 : ℝ × ℝ →L[ℝ] ℝ × ℝ)
  have hfd : ∀ z, fderiv ℝ f z = planarDeriv η (m := m) (g := g) d2 z := fun z =>
    (hasFDerivAt_planarField P η hd2 z).fderiv
  have hYd' : ∀ s ∈ Icc 0 T, HasDerivWithinAt Y
      (fderiv ℝ f (planarFlow P η hm hg s u) ∘L Y s) (Icc 0 T) s := fun s hs => by
    rw [hfd]
    exact hYd s hs
  have hder := hasFDerivAt_flow_of_variational (f := f) isOpen_univ hf.contDiffOn
    (isCompact_closedBall (0 : ℝ × ℝ) (B + Λ)) (subset_univ _)
    (α := fun y s => planarFlow P η hm hg s y) (x := u) one_pos hT
    (fun y _ => planarFlow_zero P η hm hg y)
    (fun y _ s _ => (hasDerivAt_planarFlow P η hm hg y s).hasDerivWithinAt)
    hαK (fun s hs => (hlipT s hs).lipschitzOnWith) hY0 hYd' t htT
  refine ⟨Y t, hder, ?_⟩
  -- the determinant is constant along the orbit
  set Dt : ℝ → ℝ := fun s => (Y s (1, 0)).1 * (Y s (0, 1)).2 - (Y s (1, 0)).2 * (Y s (0, 1)).1
    with hDt
  have hYe : ∀ e : ℝ × ℝ, ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun r => Y r e)
      (planarDeriv η (m := m) (g := g) d2 (planarFlow P η hm hg s u) (Y s e)) (Icc 0 T) s := by
    intro e s hs
    have := (hYd s hs).clm_apply (hasDerivWithinAt_const s _ e)
    simpa [hAdef] using this
  have hDd : ∀ s ∈ Icc 0 T, HasDerivWithinAt Dt 0 (Icc 0 T) s := by
    intro s hs
    have hfst : ∀ {φ : ℝ → ℝ × ℝ} {φ' : ℝ × ℝ}, HasDerivWithinAt φ φ' (Icc 0 T) s →
        HasDerivWithinAt (fun r => (φ r).1) φ'.1 (Icc 0 T) s := fun h =>
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt s h
    have hsnd : ∀ {φ : ℝ → ℝ × ℝ} {φ' : ℝ × ℝ}, HasDerivWithinAt φ φ' (Icc 0 T) s →
        HasDerivWithinAt (fun r => (φ r).2) φ'.2 (Icc 0 T) s := fun h =>
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt s h
    have h10 := hYe (1, 0) s hs
    have h01 := hYe (0, 1) s hs
    have h := (((hfst h10).mul (hsnd h01)).sub ((hsnd h10).mul (hfst h01)))
    convert h using 1
    simp only [planarDeriv_apply]
    ring
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := T)
    (fun s hs => (hDd s hs).continuousWithinAt)
    (fun s hs => (hDd s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2⟩)) t htT
  rw [det_eq_entries]
  show Dt t = 1
  rw [hconst]
  simp [hDt, hY0]

/-! ### Area and volume preservation -/

theorem planarFlow_neg_inv (t : ℝ) (w : ℝ × ℝ) :
    planarFlow P η hm hg t (planarFlow P η hm hg (-t) w) = w := by
  have h := planarFlow_neg P η hm hg (-t) w
  rwa [neg_neg] at h

/-- **Forward in time, the planar flow carries every measurable set to one of the same area.** -/
theorem volume_image_planarFlow (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x) (hc2 : Continuous d2)
    {t : ℝ} (ht : 0 ≤ t) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    volume (planarFlow P η hm hg t '' A) = volume A := by
  choose D hD hdet using fun u => exists_hasFDerivAt_planarFlow P η hm hg hd2 hc2 u ht
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hA (fun x _ => (hD x).hasFDerivWithinAt)
    (fun x _ y _ hxy => by
      have := congrArg (planarFlow P η hm hg (-t)) hxy
      rwa [planarFlow_neg, planarFlow_neg] at this)]
  simp [hdet]

/-- ★★★ **The planar flow preserves area**, at every time. -/
theorem measurePreserving_planarFlow (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x)
    (hc2 : Continuous d2) (t : ℝ) :
    MeasurePreserving (planarFlow P η hm hg t) volume volume := by
  have hmeas := (continuous_planarFlow P η hm hg t).measurable
  refine ⟨hmeas, ?_⟩
  ext B hB
  rw [Measure.map_apply hmeas hB]
  rcases le_total 0 t with ht | ht
  · have hsurj : Function.Surjective (planarFlow P η hm hg t) := fun w =>
      ⟨planarFlow P η hm hg (-t) w, planarFlow_neg_inv P η hm hg t w⟩
    rw [← volume_image_planarFlow P η hm hg hd2 hc2 ht (hmeas hB),
      Set.image_preimage_eq B hsurj]
  · have hpre : planarFlow P η hm hg t ⁻¹' B = planarFlow P η hm hg (-t) '' B := by
      ext v
      constructor
      · intro hv
        exact ⟨planarFlow P η hm hg t v, hv, planarFlow_neg P η hm hg t v⟩
      · rintro ⟨w, hw, rfl⟩
        show planarFlow P η hm hg t (planarFlow P η hm hg (-t) w) ∈ B
        rw [planarFlow_neg_inv]
        exact hw
    rw [hpre]
    exact volume_image_planarFlow P η hm hg hd2 hc2 (neg_nonneg.2 ht) hB

theorem continuous_regShift (t : ℝ) : Continuous (regShift P η hm hg t) := by
  have hc := (lipschitz_detField P η hm hg).continuous_odeFlow_point t
  have hemb : Continuous fun u : ℝ × ℝ => ((u.1, u.2, (0 : Fin L → ℝ)) : DetState L) := by
    fun_prop
  exact (hc.comp hemb).snd.snd

/-- ★★★ **Liouville for the coupled detector flow**: for a `C²` profile, the flow of
`H = p²/(2m) + g Σ_j χ(x − j) η_j` on the arena `(x, p, ζ)` preserves Lebesgue measure, at every
time. -/
theorem measurePreserving_detFlow (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x) (hc2 : Continuous d2)
    (t : ℝ) : MeasurePreserving (detFlow P η hm hg t) volume volume := by
  have hS : MeasurePreserving (fun q : (ℝ × ℝ) × (Fin L → ℝ) =>
      (planarFlow P η hm hg t q.1, q.2 + regShift P η hm hg t q.1))
      ((volume : Measure (ℝ × ℝ)).prod volume) ((volume : Measure (ℝ × ℝ)).prod volume) :=
    (measurePreserving_planarFlow P η hm hg hd2 hc2 t).skew_product
      (g := fun a ζ => ζ + regShift P η hm hg t a)
      (measurable_snd.add ((continuous_regShift P η hm hg t).measurable.comp measurable_fst))
      (ae_of_all _ fun a => map_add_right_eq_self volume (regShift P η hm hg t a))
  have he : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin L → ℝ) ≃ᵐ _)
      (((volume : Measure ℝ).prod volume).prod volume)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) :=
    measurePreserving_prodAssoc _ _ _
  have h := he.comp (hS.comp (MeasurePreserving.symm _ he))
  have hfun : detFlow P η hm hg t = (MeasurableEquiv.prodAssoc ∘ (fun q : (ℝ × ℝ) × (Fin L → ℝ) =>
      (planarFlow P η hm hg t q.1, q.2 + regShift P η hm hg t q.1)) ∘
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin L → ℝ) ≃ᵐ _).symm) := by
    funext z
    rw [detFlow_eq_skew]
    rfl
  rw [hfun]
  exact h

/-- ★★★ **The coupled two-time evolution preserves Lebesgue measure.** -/
theorem measurePreserving_coupledEvolve (hd2 : ∀ x, HasDerivAt P.dχ (d2 x) x)
    (hc2 : Continuous d2) (s t : ℝ) :
    MeasurePreserving (coupledEvolve (P := P) (η := η) (hm := hm) (hg := hg) s t) volume volume :=
  measurePreserving_detFlow P η hm hg hd2 hc2 (t - s)

end CSD.RecordLayer.Coupled
