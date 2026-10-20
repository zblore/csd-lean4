/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SingletSkewTables
public import CsdLean4.Empirical.QM.ColbeckRenner

/-!
# The blind B-wing primitive is unsatisfiable at the I3 record basins for the singlet

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #156 (out of ~~#137~~): the finding, as a theorem.

`LF3.RemoteSettingLocalityB` asks for **one** relabelling `reroute a a'` that carries B's reading in
context `⟨a, b⟩` to its reading in `⟨a', b⟩` for **every** `b`. ~~#137~~ observed that this is more
than the derivation uses and that the record layer cannot supply it. This file proves the second
half.

* ★ `LF3.measure_counterfactual_eq_of_remoteSettingLocalityB`: **a blind reroute equates the
  counterfactual joint laws** — `μ {l | wingB ⟨a,b⟩ l = t ∧ wingB ⟨a,b'⟩ l = t'}` is the same at `a`
  and at `a'`, because the one relabelling carries the intersection at `a'` back to the intersection
  at `a`, and it preserves `μ`. Pure measure theory, any `Σ`.
* `counterfactual_eq_iUnion`, ★ `volume_counterfactual`: at the I3 skew cells of two tables with
  the same A-marginal, the counterfactual set is `⋃ₛ A_s × (B_{s,t} ∩ B'_{s,t'})`, with measure
  `∑ₛ |A_s| · |B_{s,t} ∩ B'_{s,t'}|`.
* ★★ `volume_counterfactual_singlet`: for the singlet, `vol {wingB ⟨a,b⟩ = + ∧ wingB ⟨a,b'⟩ = +}
  = ½ min((1−d)/2, (1−d')/2) + ½ min((1+d)/2, (1+d')/2)` with `d = a·b`, `d' = a·b'` (`cfJoint`).
* ★★★ `not_nonempty_remoteSettingLocalityB_singlet`: **no blind B-reroute exists for the singlet
  on the I3 record basins.** At the circle settings `a = 0`, `a' = π/2`, `b = π/4`, `b' = −π/4`
  the counterfactual law is `1/2` at `a` and `(1 − √2/2)/2` at `a'`; `√2 ≠ 0`.

## What this says

The record layer satisfies the primitive the derivation consumes (`LocalSettingLocalityB`,
`SkewReroute.lean`, `SingletSkewTables.lean`) and **cannot** satisfy the blind one. The obstruction
is not a feature of the rectangle exchange but of any `b`-blind map whatsoever: the counterfactual
joint law of B's two readings is an invariant of such a map, and the singlet's tables make it
depend on `a`. A sharper reading: the blind primitive would force a joint distribution of B's
counterfactual readings under two settings that is independent of A's setting, which Bell-violating
tables refuse.

## Honest scope

* The obstruction is stated at the I3 skew cells with A's cells shared across `b` (the geometry the
  record layer has). The paragraph in `SettingLocalityLocal.lean` argues the same for any geometry
  with shared A-cells via the Fréchet bounds; that generalisation is not formalised.
* Four specific circle settings; the general contrast criterion
  (`|a·b − a·b'| ≠ |a'·b − a'·b'|`) is visible in `cfJoint` but stated only through this instance.

References: `LF3/SettingLocality.lean` (`RemoteSettingLocalityB`), `LF3/SettingLocalityLocal.lean`
(the restated primitive and the prose argument), `SkewReroute.lean` (`skewIdx`, `skewOutcomeMaps`),
`SingletSkewTables.lean` (`singletTables`), `Empirical/QM/ColbeckRenner.lean` (`circleSetting`,
`dotR_circleSetting`); `specs/BACKLOG.md` #156, ~~#137~~.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.LF3

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace]

/-- ★ **A blind B-reroute equates the counterfactual joint laws of B's two readings** at `a` and at
`a'`: the one relabelling carries the intersection at `a'` back to the intersection at `a`. -/
theorem measure_counterfactual_eq_of_remoteSettingLocalityB {μ : Measure SigmaSpace}
    {S : SharedContextOutcomeMaps SigmaSpace} (hS : MeasurableSharedContextOutcomeMaps S)
    (H : RemoteSettingLocalityB μ S) (a a' b b' : DetectorSetting) (t t' : Sign) :
    μ {l | S.wingB ⟨a, b⟩ l = t ∧ S.wingB ⟨a, b'⟩ l = t'}
      = μ {l | S.wingB ⟨a', b⟩ l = t ∧ S.wingB ⟨a', b'⟩ l = t'} := by
  have h1 : MeasurableSet {l | S.wingB ⟨a', b⟩ l = t} :=
    (S.measurable_wingB hS ⟨a', b⟩) (measurableSet_singleton t)
  have h2 : MeasurableSet {l | S.wingB ⟨a', b'⟩ l = t'} :=
    (S.measurable_wingB hS ⟨a', b'⟩) (measurableSet_singleton t')
  have hset : MeasurableSet {l | S.wingB ⟨a', b⟩ l = t ∧ S.wingB ⟨a', b'⟩ l = t'} := h1.inter h2
  have hpre : (H.reroute a a') ⁻¹' {l | S.wingB ⟨a', b⟩ l = t ∧ S.wingB ⟨a', b'⟩ l = t'}
      = {l | S.wingB ⟨a, b⟩ l = t ∧ S.wingB ⟨a, b'⟩ l = t'} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [H.wingB_invariant a a' b l, H.wingB_invariant a a' b' l]
  rw [← hpre]
  exact (H.measurePreserving a a').measure_preimage hset.nullMeasurableSet

end CSD.LF3

namespace CSD.RecordLayer

open LF3 Empirical.QM.ColbeckRenner

variable {m n : ℕ}

/-! ### The counterfactual set at the skew cells -/

/-- With the same A-marginal, the counterfactual set is a union over A's cells of rectangles. -/
theorem counterfactual_eq_iUnion {q q' : JointRates m n} (hrow : q.rowSum = q'.rowSum)
    (t t' : Fin n) :
    {θ : LF4.KTorus | (skewIdx q θ).2 = t ∧ (skewIdx q' θ).2 = t'}
      = ⋃ s, circleCell q.rowSum s ×ˢ (circleCell (q.condRate s) t ∩ circleCell (q'.condRate s) t') := by
  ext θ
  simp only [Set.mem_ofPred_eq, mem_iUnion, mem_prod, mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hm : θ ∈ skewCell q (skewIdx q θ).1 t := by
      have := mem_skewCell_skewIdx q θ
      rwa [h1] at this
    have hm' : θ ∈ skewCell q' (skewIdx q' θ).1 t' := by
      have := mem_skewCell_skewIdx q' θ
      rwa [h2] at this
    have hA : θ.1 ∈ circleCell q.rowSum (skewIdx q' θ).1 := by
      rw [hrow]; exact hm'.1
    have heq : (skewIdx q θ).1 = (skewIdx q' θ).1 := by
      by_contra hne
      exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint _ q.rowSum_nonneg hne) hm.1 hA
    refine ⟨(skewIdx q θ).1, hm.1, hm.2, ?_⟩
    rw [heq]
    exact hm'.2
  · rintro ⟨s, h1, h2, h3⟩
    have hq : θ ∈ skewCell q s t := ⟨h1, h2⟩
    have hq' : θ ∈ skewCell q' s t' := ⟨by rw [← hrow]; exact h1, h3⟩
    exact ⟨by rw [skewIdx_eq_of_mem q hq], by rw [skewIdx_eq_of_mem q' hq']⟩

/-- ★ **The counterfactual law at the skew cells**: `∑ₛ |A_s| · |B_{s,t} ∩ B'_{s,t'}|`. -/
theorem volume_counterfactual {q q' : JointRates m n} (hrow : q.rowSum = q'.rowSum) (t t' : Fin n) :
    (volume : Measure LF4.KTorus) {θ | (skewIdx q θ).2 = t ∧ (skewIdx q' θ).2 = t'}
      = ∑ s, (volume : Measure CircleFibre) (circleCell q.rowSum s)
          * (volume : Measure CircleFibre)
              (circleCell (q.condRate s) t ∩ circleCell (q'.condRate s) t') := by
  have hdisj : Pairwise (Function.onFun Disjoint fun s : Fin m =>
      circleCell q.rowSum s ×ˢ (circleCell (q.condRate s) t ∩ circleCell (q'.condRate s) t')) := by
    intro s s' hne
    refine Set.disjoint_left.mpr fun θ h h' => ?_
    exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint _ q.rowSum_nonneg hne) h.1 h'.1
  have hmeas : ∀ s : Fin m, MeasurableSet
      (circleCell q.rowSum s ×ˢ (circleCell (q.condRate s) t ∩ circleCell (q'.condRate s) t')) :=
    fun s => (measurableSet_circleCell _ s).prod
      ((measurableSet_circleCell _ t).inter (measurableSet_circleCell _ t'))
  rw [counterfactual_eq_iUnion hrow t t', measure_iUnion hdisj hmeas, tsum_fintype]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod]

/-! ### The singlet's counterfactual law -/

/-- The counterfactual joint law of B's `+` readings under `b` and `b'`, as a function of the two
correlations `d = a·b`, `d' = a·b'`. -/
def cfJoint (d d' : ℝ) : ℝ :=
  1 / 2 * min ((1 - d) / 2) ((1 - d') / 2) + 1 / 2 * min ((1 + d) / 2) ((1 + d') / 2)

theorem signOfFin_eq_plus_iff (x : Fin 2) : signOfFin x = Sign.plus ↔ x = 0 := by
  fin_cases x <;> simp

/-- The conditional probability of B's `+` given A's `s`, for the singlet. -/
theorem singletJointRates_condRate_zero (a b : DetectorSetting) (s : Fin 2) :
    (singletJointRates a b).condRate s 0 = 2 * P_st a b (signOfFin s) Sign.plus := by
  unfold JointRates.condRate
  rw [singletJointRates_rate, singletJointRates_rowSum, signOfFin_zero]
  ring

/-- Two initial arcs intersect in the initial arc of the smaller length. -/
theorem circleCell_condRate_zero_inter [NeZero n] (q q' : JointRates m n) (s : Fin m) :
    circleCell (q.condRate s) 0 ∩ circleCell (q'.condRate s) 0
      = rep ⁻¹' Ioc 0 (min (q.condRate s 0) (q'.condRate s 0)) := by
  have h0 : loSum (q.condRate s) 0 = 0 := loSum_zero_val _ rfl
  have h0' : loSum (q'.condRate s) 0 = 0 := loSum_zero_val _ rfl
  ext θ
  simp only [circleCell, h0, h0', zero_add, mem_inter_iff, mem_preimage, mem_Ioc, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, ⟨h1, h3⟩⟩

/-- ★★ **The singlet's counterfactual law of B's `+` readings** under `b` and `b'`, at the I3 skew
cells. -/
theorem volume_counterfactual_singlet (a b b' : DetectorSetting) :
    (volume : Measure LF4.KTorus)
        {θ | (skewOutcomeMaps singletTables).wingB ⟨a, b⟩ θ = Sign.plus
          ∧ (skewOutcomeMaps singletTables).wingB ⟨a, b'⟩ θ = Sign.plus}
      = ENNReal.ofReal (cfJoint (dotR a b) (dotR a b')) := by
  have hrow : (singletJointRates a b).rowSum = (singletJointRates a b').rowSum := by
    funext s
    rw [singletJointRates_rowSum, singletJointRates_rowSum]
  have hset : {θ : LF4.KTorus | (skewOutcomeMaps singletTables).wingB ⟨a, b⟩ θ = Sign.plus
      ∧ (skewOutcomeMaps singletTables).wingB ⟨a, b'⟩ θ = Sign.plus}
      = {θ | (skewIdx (singletJointRates a b) θ).2 = 0
          ∧ (skewIdx (singletJointRates a b') θ).2 = 0} := by
    ext θ
    simp only [Set.mem_ofPred_eq]
    show signOfFin _ = Sign.plus ∧ signOfFin _ = Sign.plus ↔ _
    rw [signOfFin_eq_plus_iff, signOfFin_eq_plus_iff]
    exact Iff.rfl
  rw [hset, volume_counterfactual hrow 0 0, Fin.sum_univ_two]
  -- the A-cells
  have hA : ∀ s : Fin 2, (volume : Measure CircleFibre) (circleCell (singletJointRates a b).rowSum s)
      = ENNReal.ofReal (1 / 2) := fun s => by
    rw [volume_circleCell _ (singletJointRates a b).rowSum_nonneg
      (singletJointRates a b).loSum_rowSum_le_one s, singletJointRates_rowSum]
  -- the B-arcs
  have hd := abs_le.1 (abs_dotR_le_one a b)
  have hd' := abs_le.1 (abs_dotR_le_one a b')
  have hB : ∀ s : Fin 2, (volume : Measure CircleFibre)
      (circleCell ((singletJointRates a b).condRate s) 0
        ∩ circleCell ((singletJointRates a b').condRate s) 0)
      = ENNReal.ofReal (min ((singletJointRates a b).condRate s 0)
          ((singletJointRates a b').condRate s 0)) := fun s => by
    rw [circleCell_condRate_zero_inter, volume_rep_preimage_Ioc le_rfl, sub_zero]
    have h1 := (singletJointRates a b).loSum_condRate_le_one s 0
    rw [loSum_zero_val _ rfl, zero_add] at h1
    exact le_trans (min_le_left _ _) h1
  rw [hA, hA, hB, hB, singletJointRates_condRate_zero, singletJointRates_condRate_zero,
    singletJointRates_condRate_zero, singletJointRates_condRate_zero, signOfFin_zero, signOfFin_one]
  simp only [P_st, Sign.val_plus, Sign.val_minus]
  have hn1 : 0 ≤ min (2 * ((1 - 1 * 1 * dotR a b) / 4)) (2 * ((1 - 1 * 1 * dotR a b') / 4)) :=
    le_min (by linarith [hd.2]) (by linarith [hd'.2])
  have hn2 : 0 ≤ min (2 * ((1 - -1 * 1 * dotR a b) / 4)) (2 * ((1 - -1 * 1 * dotR a b') / 4)) :=
    le_min (by linarith [hd.1]) (by linarith [hd'.1])
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hn1) (mul_nonneg (by norm_num) hn2)]
  congr 1
  unfold cfJoint
  congr 2 <;> congr 1 <;> ring

/-! ### ★★★ The obstruction -/

/-- ★★★ **No blind B-wing reroute exists for the singlet on the I3 record basins.** A blind reroute
would equate the counterfactual joint laws at `a = 0` and `a' = π/2` (settings on the great circle,
with `b = π/4`, `b' = −π/4`); they are `1/2` and `(1 − √2/2)/2`. -/
theorem not_nonempty_remoteSettingLocalityB_singlet :
    ¬ Nonempty (RemoteSettingLocalityB (volume : Measure LF4.KTorus)
      (skewOutcomeMaps singletTables)) := by
  rintro ⟨H⟩
  have h := measure_counterfactual_eq_of_remoteSettingLocalityB
    (measurable_skewOutcomeMaps singletTables) H (circleSetting 0) (circleSetting (Real.pi / 2))
    (circleSetting (Real.pi / 4)) (circleSetting (-(Real.pi / 4))) Sign.plus Sign.plus
  rw [volume_counterfactual_singlet, volume_counterfactual_singlet, dotR_circleSetting,
    dotR_circleSetting, dotR_circleSetting, dotR_circleSetting] at h
  -- the four correlations
  have c1 : Real.cos (0 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [zero_sub, Real.cos_neg, Real.cos_pi_div_four]
  have c2 : Real.cos (0 - -(Real.pi / 4)) = Real.sqrt 2 / 2 := by
    rw [zero_sub, neg_neg, Real.cos_pi_div_four]
  have c3 : Real.cos (Real.pi / 2 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have c4 : Real.cos (Real.pi / 2 - -(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
    rw [show Real.pi / 2 - -(Real.pi / 4) = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_four]
  rw [c1, c2, c3, c4] at h
  -- the two values of the counterfactual law
  have hs : 0 < Real.sqrt 2 / 2 := by positivity
  have hs1 : Real.sqrt 2 / 2 < 1 := by
    have : Real.sqrt 2 < 2 := (Real.sqrt_lt' two_pos).2 (by norm_num)
    linarith
  have hv1 : cfJoint (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) = 1 / 2 := by
    unfold cfJoint
    rw [min_self, min_self]
    ring
  have hv2 : cfJoint (Real.sqrt 2 / 2) (-(Real.sqrt 2 / 2)) = (1 - Real.sqrt 2 / 2) / 2 := by
    unfold cfJoint
    rw [min_eq_left (by linarith), min_eq_right (by linarith)]
    ring
  rw [hv1, hv2] at h
  have h' := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by linarith)).1 h
  linarith

end CSD.RecordLayer

end

end
