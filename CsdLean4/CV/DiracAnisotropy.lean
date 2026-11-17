/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracLatticeD
public import CsdLean4.CV.DiracContinuum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The lattice's preferred directions

**Category:** 3-Local (CV). BACKLOG #295 (split of #289; milestone M7 of the author's programme
"From `Σ` to physical spacetime", obligation UO-17; `specs/beyond-1p1-scoping.md` §2.6, §3.4).

On the lattice of [`DiracLatticeD.lean`](DiracLatticeD.lean) (~~#294~~) the energy at the
angles `k : ι → ℝ` is `E(k) = √(μ² + Σ_i (2J sin k_i)²)`. In one dimension the lattice showed as
a preferred frame: the group velocity is the relativistic velocity times `cos k`
(`lattice_dilation_defect`). With more than one axis it also shows as preferred **directions**.

## The group velocity (exact)

* `sNorm_sq`, `sNorm_nonneg`, `abs_le_sNorm`, `sNorm_le_sum_abs`, `abs_le_dispE_sNorm`;
* `sinS` (`s_i = 2J sin k_i`), `latticeED`, `latticeED_sq`, `modeSD_eq_sinS` (the momentum terms
  of ~~#294~~'s mode `n` are `sinS` at its angles), `groupVelD`
  (`v_i = 2J s_i cos k_i / E`);
* ★ `hasDerivAt_latticeED` — **`groupVelD` is the gradient of the energy**, one axis at a time;
* ★ `sum_groupVelD_sq_le`, `sNorm_groupVelD_le` — **`|v_g| ≤ c = 2|J|`**;
* `sq_vRel_sNorm_div`, ★★ `lattice_dilation_defect_d` — **the defect of the squared dilation
  factor** read from the group velocity against the one read from the relativistic speed is
  `Σ_i s_i² sin² k_i / E²`, exactly;
* ★★ `massless_groupSpeed_defect` — **for a massless carrier `1 − |v_g|²/c² = Σ_i sin⁴ k_i /
  Σ_i sin² k_i`**, exactly.

## The direction dependence (bounds)

* `sq_sub_le_sin_sq` (`y² − y⁴/3 ≤ sin² y`), `abs_sin_pow_four_sub_le`
  (`|sin⁴ y − y⁴| ≤ (2/3) y⁶`), for `|y| ≤ 1`;
* ★★ `abs_sin_ratio_sub_le` — along a unit direction `n`, at `k = x n` with `0 < x ≤ 1`:
  `|Σ sin⁴ k_i / Σ sin² k_i − x² Σ_i n_i⁴| ≤ (3/2) x⁴`;
* ★★★ `massless_anisotropy` — **a massless carrier's group speed along the unit direction `n`
  at `x = a p` satisfies `|1 − |v_g|²/c² − (a p)² Σ_i n_i⁴| ≤ (3/2) (a p)⁴`.** `Σ_i n_i⁴` is `1`
  along an axis and `1/d` along the diagonal.

## The rotation residue (bounds)

* `abs_dispE_sNorm_sub_le`, `abs_div_dispE_sNorm_sub_le` — the energy and the unit-speed
  vector `s/E` are Lipschitz in `s`, coordinate by coordinate;
* `scaledVelD` (the group velocity in physical units at spacing `a`, `J = c/(2a)`,
  `k = a p`), `contVelD` (`c² p / √(μ² + c² |p|²)`);
* ★★ `abs_scaledVelD_sub_le` — **each component of the lattice velocity is within
  `c a² (P²/2 + c P³ (1 + d)/(6μ))` of the continuum velocity**, for `|p_i| ≤ P`;
* `contVelD_map` — the continuum velocity commutes with every linear map that preserves
  `sNorm`;
* ★★★ `rotation_residue` — **a rotated preparation's lattice velocity is within `(1 + d)`
  times that bound of the rotated lattice velocity**, in each component: the rotational
  counterpart of `lattice_frame_residue`. It vanishes as `a → 0` at fixed `P`.

## Honest scope

⚠️ **Dispersion, not records.** Every statement is about the function `E(k)` and its gradient.
That a packet's centre moves at `groupVelD` is #296; no detector or count is read (#297).

⚠️ **`massless_anisotropy` is for `μ = 0`.** With `μ > 0` the exact defect is
`lattice_dilation_defect_d`; its expansion in `a p` is not stated.

⚠️ **The rotation bound is not sharp**, is componentwise, and grows with the number of axes.
`R` is any linear map preserving `sNorm`; that such maps are the orthogonal group is not used.

⚠️ **Whether the anisotropy is a prediction or an artefact of the regulator** is M8's question
(UO-18): it is a prediction only if a nonzero physical spacing is independently justified.

References: `specs/beyond-1p1-scoping.md`; `specs/BACKLOG.md` #295, ~~#294~~, #296, #297, #298,
~~#285~~, ~~#249~~; `specs/unified-record-spacetime-plan.md` (UO-17, UO-18, UD-207);
`CV/DiracLatticeD.lean` (`latticeDiracHam_mulVec_diracModeD`, `sNorm`, `modeSD`);
`CV/DiracClockChain.lean` (`hasDerivAt_dispE_lattice`, `lattice_dilation_defect`,
`abs_groupVel_le`); `CV/DiracContinuum.lean` (`abs_scaledMom_sub_le`, `abs_cos_sub_one_le`);
`RecordLayer/FrameCovariance.lean` (`lattice_frame_residue`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

namespace CSD.CV

variable {ι : Type*} [Fintype ι]

/-! ### `sNorm` -/

theorem sNorm_sq (s : ι → ℝ) : sNorm s ^ 2 = ∑ i, s i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (s i))

theorem sNorm_nonneg (s : ι → ℝ) : 0 ≤ sNorm s := Real.sqrt_nonneg _

theorem abs_le_sNorm (s : ι → ℝ) (i : ι) : |s i| ≤ sNorm s := by
  rw [sNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => s j ^ 2)
    (fun j _ => sq_nonneg (s j)) (Finset.mem_univ i))

theorem sNorm_le_sum_abs (s : ι → ℝ) : sNorm s ≤ ∑ i, |s i| := by
  rw [sNorm]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  calc ∑ i, s i ^ 2 = ∑ i, |s i| * |s i| :=
        Finset.sum_congr rfl fun i _ => by rw [← sq, sq_abs]
    _ ≤ ∑ i, |s i| * ∑ j, |s j| := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => |s j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
    _ = (∑ i, |s i|) ^ 2 := by rw [← Finset.sum_mul, sq]

theorem abs_le_dispE_sNorm (μ : ℝ) (s : ι → ℝ) (i : ι) : |s i| ≤ dispE μ (sNorm s) :=
  (abs_le_sNorm s i).trans ((le_abs_self _).trans (abs_le_dispE μ _))

/-- **The energy is Lipschitz in the momentum terms**, in the sum of the coordinates'
differences. -/
theorem abs_dispE_sNorm_sub_le {μ : ℝ} (hμ : 0 < μ) (s t : ι → ℝ) :
    |dispE μ (sNorm s) - dispE μ (sNorm t)| ≤ ∑ j, |s j - t j| := by
  have hs := dispE_pos hμ (sNorm s)
  have ht := dispE_pos hμ (sNorm t)
  have hprod : (dispE μ (sNorm s) - dispE μ (sNorm t)) * (dispE μ (sNorm s) + dispE μ (sNorm t))
      = ∑ j, (s j - t j) * (s j + t j) := by
    have e1 := dispE_sNorm_sq μ s
    have e2 := dispE_sNorm_sq μ t
    have e3 : ∑ j, (s j - t j) * (s j + t j) = ∑ j, s j ^ 2 - ∑ j, t j ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e3]
    linear_combination e1 - e2
  have hle : |dispE μ (sNorm s) - dispE μ (sNorm t)| * (dispE μ (sNorm s) + dispE μ (sNorm t))
      ≤ (∑ j, |s j - t j|) * (dispE μ (sNorm s) + dispE μ (sNorm t)) := by
    calc |dispE μ (sNorm s) - dispE μ (sNorm t)| * (dispE μ (sNorm s) + dispE μ (sNorm t))
        = |(dispE μ (sNorm s) - dispE μ (sNorm t))
            * (dispE μ (sNorm s) + dispE μ (sNorm t))| := by
          rw [abs_mul, abs_of_pos (add_pos hs ht)]
      _ = |∑ j, (s j - t j) * (s j + t j)| := by rw [hprod]
      _ ≤ ∑ j, |(s j - t j) * (s j + t j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |s j - t j| * (dispE μ (sNorm s) + dispE μ (sNorm t)) :=
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
              (add_le_add (abs_le_dispE_sNorm μ s j) (abs_le_dispE_sNorm μ t j))) (abs_nonneg _)
      _ = (∑ j, |s j - t j|) * (dispE μ (sNorm s) + dispE μ (sNorm t)) := by
          rw [Finset.sum_mul]
  exact le_of_mul_le_mul_right hle (add_pos hs ht)

/-- **The unit-speed vector `s / E` is Lipschitz in `s`**, coordinate by coordinate. -/
theorem abs_div_dispE_sNorm_sub_le {μ : ℝ} (hμ : 0 < μ) (s t : ι → ℝ) (i : ι) :
    |s i / dispE μ (sNorm s) - t i / dispE μ (sNorm t)|
      ≤ (|s i - t i| + ∑ j, |s j - t j|) / μ := by
  have hs := dispE_pos hμ (sNorm s)
  have ht := dispE_pos hμ (sNorm t)
  have hsμ : μ ≤ dispE μ (sNorm s) := le_dispE μ _
  have key : s i / dispE μ (sNorm s) - t i / dispE μ (sNorm t)
      = (s i - t i) / dispE μ (sNorm s)
        + t i / dispE μ (sNorm t)
          * ((dispE μ (sNorm t) - dispE μ (sNorm s)) / dispE μ (sNorm s)) := by
    field_simp
    ring
  have h1 : |(s i - t i) / dispE μ (sNorm s)| ≤ |s i - t i| / μ := by
    rw [abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hμ hsμ
  have h2 : |t i / dispE μ (sNorm t)| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    exact (div_le_one ht).2 (abs_le_dispE_sNorm μ t i)
  have h3 : |(dispE μ (sNorm t) - dispE μ (sNorm s)) / dispE μ (sNorm s)|
      ≤ (∑ j, |s j - t j|) / μ := by
    rw [abs_div, abs_of_pos hs, abs_sub_comm]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hμ hsμ).trans
      (div_le_div_of_nonneg_right (abs_dispE_sNorm_sub_le hμ s t) hμ.le)
  rw [key]
  calc |(s i - t i) / dispE μ (sNorm s)
        + t i / dispE μ (sNorm t)
          * ((dispE μ (sNorm t) - dispE μ (sNorm s)) / dispE μ (sNorm s))|
      ≤ |(s i - t i) / dispE μ (sNorm s)|
        + |t i / dispE μ (sNorm t)
          * ((dispE μ (sNorm t) - dispE μ (sNorm s)) / dispE μ (sNorm s))| := abs_add_le _ _
    _ ≤ |s i - t i| / μ + 1 * ((∑ j, |s j - t j|) / μ) := by
        refine add_le_add h1 ?_
        rw [abs_mul]
        exact mul_le_mul h2 h3 (abs_nonneg _) zero_le_one
    _ = (|s i - t i| + ∑ j, |s j - t j|) / μ := by ring

/-! ### The group velocity -/

/-- The lattice momentum terms at the angles `k`: `s_i = 2J sin k_i`. -/
def sinS (J : ℝ) (k : ι → ℝ) : ι → ℝ := fun i => 2 * J * Real.sin (k i)

/-- The lattice energy at the angles `k`. -/
def latticeED (J μ : ℝ) (k : ι → ℝ) : ℝ := dispE μ (sNorm (sinS J k))

/-- **The group velocity**: `v_i = 2J s_i cos k_i / E`. -/
def groupVelD (J μ : ℝ) (k : ι → ℝ) : ι → ℝ := fun i =>
  2 * J * sinS J k i * Real.cos (k i) / latticeED J μ k

theorem latticeED_sq (J μ : ℝ) (k : ι → ℝ) :
    latticeED J μ k ^ 2 = μ ^ 2 + ∑ i, (2 * J * Real.sin (k i)) ^ 2 :=
  dispE_sNorm_sq μ _

theorem latticeED_nonneg (J μ : ℝ) (k : ι → ℝ) : 0 ≤ latticeED J μ k :=
  (abs_nonneg _).trans (abs_le_dispE μ _)

omit [Fintype ι] in
/-- The momentum terms of the mode `n` of `DiracLatticeD.lean` are `sinS` at its angles. -/
theorem modeSD_eq_sinS {L : ℕ} (J : ℝ) (n : ι → ZMod L) :
    modeSD J n = sinS J (fun i => latticeAngle (n i)) := rfl

/-- ★ **`groupVelD` is the gradient of the energy**, one axis at a time. -/
theorem hasDerivAt_latticeED [DecidableEq ι] {J μ : ℝ} {k : ι → ℝ}
    (hE : 0 < latticeED J μ k) (i : ι) :
    HasDerivAt (fun x => latticeED J μ (Function.update k i x)) (groupVelD J μ k i) (k i) := by
  have hfun : ∀ x : ℝ, latticeED J μ (Function.update k i x)
      = Real.sqrt (μ ^ 2 + ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2
          + (2 * J * Real.sin x) ^ 2) := by
    intro x
    have h1 : sinS J (Function.update k i x) i = 2 * J * Real.sin x := by simp [sinS]
    have h2 : ∑ j ∈ Finset.univ.erase i, sinS J (Function.update k i x) j ^ 2
        = ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2 :=
      Finset.sum_congr rfl fun j hj => by
        simp [sinS, Finset.ne_of_mem_erase hj]
    unfold latticeED dispE
    congr 1
    rw [sNorm_sq, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), h1, h2]
    ring
  have hk : latticeED J μ k
      = Real.sqrt (μ ^ 2 + ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2
          + (2 * J * Real.sin (k i)) ^ 2) := by
    have := hfun (k i)
    rwa [Function.update_eq_self] at this
  have hin : HasDerivAt (fun x => μ ^ 2 + ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2
      + (2 * J * Real.sin x) ^ 2)
      (2 * (2 * J * Real.sin (k i)) * (2 * J * Real.cos (k i))) (k i) := by
    have := ((Real.hasDerivAt_sin (k i)).const_mul (2 * J)).pow 2
    simpa using this.const_add
      (μ ^ 2 + ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2)
  have hpos : μ ^ 2 + ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2
      + (2 * J * Real.sin (k i)) ^ 2 ≠ 0 := by
    intro h0
    rw [hk, h0, Real.sqrt_zero] at hE
    exact lt_irrefl _ hE
  have h := hin.sqrt hpos
  rw [funext hfun]
  convert h using 1
  simp only [groupVelD, sinS]
  rw [hk]
  have hne : Real.sqrt (μ ^ 2 + ∑ j ∈ Finset.univ.erase i, (2 * J * Real.sin (k j)) ^ 2
      + (2 * J * Real.sin (k i)) ^ 2) ≠ 0 := by
    rw [← hk]
    exact hE.ne'
  field_simp

/-- ★ **No mode outruns `c = 2J`**: `|v_g|² ≤ c²`. -/
theorem sum_groupVelD_sq_le {J μ : ℝ} {k : ι → ℝ} (hE : 0 < latticeED J μ k) :
    ∑ i, groupVelD J μ k i ^ 2 ≤ (2 * J) ^ 2 := by
  have hE2 := latticeED_sq J μ k
  have hterm : ∀ i, groupVelD J μ k i ^ 2
      ≤ (2 * J) ^ 2 * ((2 * J * Real.sin (k i)) ^ 2 / latticeED J μ k ^ 2) := by
    intro i
    have e : groupVelD J μ k i ^ 2
        = (2 * J) ^ 2 * ((2 * J * Real.sin (k i)) ^ 2 / latticeED J μ k ^ 2)
          * Real.cos (k i) ^ 2 := by
      simp only [groupVelD, sinS]
      ring
    rw [e]
    exact mul_le_of_le_one_right (by positivity) (Real.cos_sq_le_one _)
  calc ∑ i, groupVelD J μ k i ^ 2
      ≤ ∑ i, (2 * J) ^ 2 * ((2 * J * Real.sin (k i)) ^ 2 / latticeED J μ k ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (2 * J) ^ 2 * ((∑ i, (2 * J * Real.sin (k i)) ^ 2) / latticeED J μ k ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_div]
    _ ≤ (2 * J) ^ 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [div_le_one (by positivity), hE2]
        nlinarith [sq_nonneg μ]
    _ = (2 * J) ^ 2 := mul_one _

theorem sNorm_groupVelD_le {J μ : ℝ} {k : ι → ℝ} (hE : 0 < latticeED J μ k) :
    sNorm (groupVelD J μ k) ≤ |2 * J| := by
  rw [sNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sum_groupVelD_sq_le hE)

theorem sq_vRel_sNorm_div {J : ℝ} (hJ : J ≠ 0) (μ : ℝ) (k : ι → ℝ) :
    (vRel (2 * J) μ (sNorm (sinS J k)) / (2 * J)) ^ 2
      = (∑ i, (2 * J * Real.sin (k i)) ^ 2) / latticeED J μ k ^ 2 := by
  have hc : (2 * J) ≠ 0 := mul_ne_zero two_ne_zero hJ
  have e : vRel (2 * J) μ (sNorm (sinS J k)) / (2 * J)
      = sNorm (sinS J k) / latticeED J μ k := by
    unfold vRel latticeED
    field_simp
  rw [e, div_pow, sNorm_sq]
  rfl

/-- ★★ **The lattice's preferred frame and directions, exactly**: the squared dilation factor
read from the group velocity exceeds the one read from the relativistic speed by
`Σ_i s_i² sin² k_i / E²`. -/
theorem lattice_dilation_defect_d {J μ : ℝ} {k : ι → ℝ} (hJ : J ≠ 0)
    (hE : 0 < latticeED J μ k) :
    (1 - (∑ i, groupVelD J μ k i ^ 2) / (2 * J) ^ 2)
        - (1 - (vRel (2 * J) μ (sNorm (sinS J k)) / (2 * J)) ^ 2)
      = (∑ i, (2 * J * Real.sin (k i)) ^ 2 * Real.sin (k i) ^ 2) / latticeED J μ k ^ 2 := by
  have hc : (2 * J) ≠ 0 := mul_ne_zero two_ne_zero hJ
  have hE' := hE.ne'
  have hg : (∑ i, groupVelD J μ k i ^ 2) / (2 * J) ^ 2
      = (∑ i, (2 * J * Real.sin (k i)) ^ 2 * Real.cos (k i) ^ 2) / latticeED J μ k ^ 2 := by
    rw [Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [groupVelD, sinS]
    field_simp
  rw [sq_vRel_sNorm_div hJ, hg, sub_sub_sub_cancel_left, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (-(2 * J * Real.sin (k i)) ^ 2) * Real.sin_sq_add_cos_sq (k i)

/-- ★★ **A massless carrier's group speed, exactly**:
`1 − |v_g|²/c² = Σ_i sin⁴ k_i / Σ_i sin² k_i`. -/
theorem massless_groupSpeed_defect {J : ℝ} {k : ι → ℝ} (hJ : J ≠ 0)
    (hB : 0 < ∑ i, Real.sin (k i) ^ 2) :
    1 - (∑ i, groupVelD J 0 k i ^ 2) / (2 * J) ^ 2
      = (∑ i, Real.sin (k i) ^ 4) / (∑ i, Real.sin (k i) ^ 2) := by
  have hc : (2 * J) ≠ 0 := mul_ne_zero two_ne_zero hJ
  have hsum : ∑ i, (2 * J * Real.sin (k i)) ^ 2 = (2 * J) ^ 2 * ∑ i, Real.sin (k i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hE2 : latticeED J 0 k ^ 2 = (2 * J) ^ 2 * ∑ i, Real.sin (k i) ^ 2 := by
    rw [latticeED_sq, hsum]
    ring
  have hE2pos : 0 < latticeED J 0 k ^ 2 := by
    rw [hE2]
    positivity
  have hEpos : 0 < latticeED J 0 k :=
    lt_of_le_of_ne (latticeED_nonneg J 0 k) fun h => by
      rw [← h] at hE2pos
      simp at hE2pos
  have hd := lattice_dilation_defect_d hJ hEpos
  have hv1 : (vRel (2 * J) 0 (sNorm (sinS J k)) / (2 * J)) ^ 2 = 1 := by
    rw [sq_vRel_sNorm_div hJ, hsum, ← hE2]
    exact div_self hE2pos.ne'
  have h4 : ∑ i, (2 * J * Real.sin (k i)) ^ 2 * Real.sin (k i) ^ 2
      = (2 * J) ^ 2 * ∑ i, Real.sin (k i) ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hv1, sub_self, sub_zero] at hd
  rw [hd, hE2, h4, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-! ### The direction dependence -/

/-- `y² − y⁴/3 ≤ sin² y` for `|y| ≤ 1`. -/
theorem sq_sub_le_sin_sq {y : ℝ} (hy : |y| ≤ 1) : y ^ 2 - y ^ 4 / 3 ≤ Real.sin y ^ 2 := by
  have hs : Real.sin y ^ 2 = Real.sin |y| ^ 2 := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    rw [Real.sin_neg, neg_sq]
  have h0 := abs_nonneg y
  have h1 := Real.sin_ge_sub_cube h0
  have hsq : |y| ^ 2 ≤ 1 := pow_le_one₀ h0 hy
  have h2 : 0 ≤ |y| - |y| ^ 3 / 6 := by
    have e : |y| - |y| ^ 3 / 6 = |y| * (1 - |y| ^ 2 / 6) := by ring
    rw [e]
    exact mul_nonneg h0 (by linarith)
  have h3 := pow_le_pow_left₀ h2 h1 2
  have e2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have e4 : y ^ 4 = |y| ^ 4 := by
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, e2]
    ring
  have e6 : (|y| - |y| ^ 3 / 6) ^ 2 = |y| ^ 2 - |y| ^ 4 / 3 + |y| ^ 6 / 36 := by ring
  rw [hs, e2, e4]
  linarith [pow_nonneg h0 6]

/-- `|sin⁴ y − y⁴| ≤ (2/3) y⁶` for `|y| ≤ 1`. -/
theorem abs_sin_pow_four_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    |Real.sin y ^ 4 - y ^ 4| ≤ 2 / 3 * y ^ 6 := by
  have hl := sq_sub_le_sin_sq hy
  have hu := Real.sin_sq_le_sq (x := y)
  have e : Real.sin y ^ 4 - y ^ 4
      = -((y ^ 2 - Real.sin y ^ 2) * (Real.sin y ^ 2 + y ^ 2)) := by ring
  have hprod : (y ^ 2 - Real.sin y ^ 2) * (Real.sin y ^ 2 + y ^ 2)
      ≤ y ^ 4 / 3 * (2 * y ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hnn : 0 ≤ (y ^ 2 - Real.sin y ^ 2) * (Real.sin y ^ 2 + y ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  rw [e, abs_neg, abs_of_nonneg hnn]
  calc (y ^ 2 - Real.sin y ^ 2) * (Real.sin y ^ 2 + y ^ 2) ≤ y ^ 4 / 3 * (2 * y ^ 2) := hprod
    _ = 2 / 3 * y ^ 6 := by ring

/-- ★★ **The direction term**: along a unit direction `n`, at the angles `x n` with
`0 < x ≤ 1`, `Σ sin⁴ / Σ sin²` is `x² Σ_i n_i⁴` within `(3/2) x⁴`. -/
theorem abs_sin_ratio_sub_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ι → ℝ}
    (hn : ∑ i, n i ^ 2 = 1) :
    0 < ∑ i, Real.sin (x * n i) ^ 2
    ∧ |(∑ i, Real.sin (x * n i) ^ 4) / (∑ i, Real.sin (x * n i) ^ 2) - x ^ 2 * ∑ i, n i ^ 4|
        ≤ 3 / 2 * x ^ 4 := by
  have hn1 : ∀ i, n i ^ 2 ≤ 1 := fun i => by
    rw [← hn]
    exact Finset.single_le_sum (f := fun j => n j ^ 2) (fun j _ => sq_nonneg (n j))
      (Finset.mem_univ i)
  have hni : ∀ i, |x * n i| ≤ 1 := fun i => by
    rw [abs_mul, abs_of_pos hx0]
    calc x * |n i| ≤ 1 * 1 :=
          mul_le_mul hx1 ((sq_le_one_iff_abs_le_one _).1 (hn1 i)) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hq0 : 0 ≤ ∑ i, n i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  have hq1 : ∑ i, n i ^ 4 ≤ 1 := by
    rw [← hn]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hn1 i
    nlinarith [sq_nonneg (n i)]
  have hr1 : ∑ i, n i ^ 6 ≤ 1 := by
    rw [← hn]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hn1 i
    have h4 : n i ^ 4 ≤ 1 := by nlinarith [sq_nonneg (n i)]
    nlinarith [sq_nonneg (n i)]
  have hx2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1
  have hx4 : x ^ 4 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
  have hsumsq : ∑ i, (x * n i) ^ 2 = x ^ 2 := by
    rw [← mul_one (x ^ 2), ← hn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hBu : ∑ i, Real.sin (x * n i) ^ 2 ≤ x ^ 2 := by
    rw [← hsumsq]
    exact Finset.sum_le_sum fun i _ => Real.sin_sq_le_sq
  have hBl : x ^ 2 - x ^ 4 * (∑ i, n i ^ 4) / 3 ≤ ∑ i, Real.sin (x * n i) ^ 2 := by
    have e : x ^ 2 - x ^ 4 * (∑ i, n i ^ 4) / 3 = ∑ i, ((x * n i) ^ 2 - (x * n i) ^ 4 / 3) := by
      rw [Finset.sum_sub_distrib, hsumsq, ← Finset.sum_div, Finset.mul_sum]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Finset.sum_le_sum fun i _ => sq_sub_le_sin_sq (hni i)
  have hA : |∑ i, Real.sin (x * n i) ^ 4 - x ^ 4 * ∑ i, n i ^ 4| ≤ 2 / 3 * x ^ 6 := by
    have e : ∑ i, Real.sin (x * n i) ^ 4 - x ^ 4 * ∑ i, n i ^ 4
        = ∑ i, (Real.sin (x * n i) ^ 4 - (x * n i) ^ 4) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc |∑ i, (Real.sin (x * n i) ^ 4 - (x * n i) ^ 4)|
        ≤ ∑ i, |Real.sin (x * n i) ^ 4 - (x * n i) ^ 4| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 / 3 * (x * n i) ^ 6 :=
          Finset.sum_le_sum fun i _ => abs_sin_pow_four_sub_le (hni i)
      _ = 2 / 3 * x ^ 6 * ∑ i, n i ^ 6 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 2 / 3 * x ^ 6 * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = 2 / 3 * x ^ 6 := mul_one _
  generalize (∑ i, Real.sin (x * n i) ^ 4) = A at hA ⊢
  generalize (∑ i, Real.sin (x * n i) ^ 2) = B at hBu hBl ⊢
  generalize (∑ i, n i ^ 4) = q at hq0 hq1 hBl hA ⊢
  have hxq : x ^ 4 * q ≤ x ^ 4 := mul_le_of_le_one_right (by positivity) hq1
  have hB23 : 2 / 3 * x ^ 2 ≤ B := by linarith
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hB23
  refine ⟨hBpos, ?_⟩
  have hD0 : 0 ≤ x ^ 2 * q * (x ^ 2 - B) :=
    mul_nonneg (mul_nonneg (sq_nonneg x) hq0) (by linarith)
  have hD1 : x ^ 2 * q * (x ^ 2 - B) ≤ x ^ 2 * (x ^ 4 / 3) :=
    mul_le_mul (mul_le_of_le_one_right (sq_nonneg x) hq1) (by linarith) (by linarith)
      (sq_nonneg x)
  have hA' := abs_le.1 hA
  have hnum : |A - x ^ 2 * q * B| ≤ x ^ 6 := by
    have e : A - x ^ 2 * q * B = (A - x ^ 4 * q) + x ^ 2 * q * (x ^ 2 - B) := by ring
    rw [e, abs_le]
    constructor
    · nlinarith [pow_nonneg hx0.le 6]
    · have e6 : x ^ 2 * (x ^ 4 / 3) = x ^ 6 / 3 := by ring
      linarith [pow_nonneg hx0.le 6]
  have hdiv : A / B - x ^ 2 * q = (A - x ^ 2 * q * B) / B := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
  refine hnum.trans ?_
  have e : x ^ 6 = 3 / 2 * x ^ 4 * (2 / 3 * x ^ 2) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hB23 (by positivity)

/-- ★★★ **The lattice's preferred directions (#295).** A massless carrier moving along the unit
direction `n` at `x = a p ∈ (0, 1]` has group speed with
`|1 − |v_g|²/c² − x² Σ_i n_i⁴| ≤ (3/2) x⁴`, `c = 2J`. -/
theorem massless_anisotropy {J x : ℝ} (hJ : J ≠ 0) (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ι → ℝ}
    (hn : ∑ i, n i ^ 2 = 1) :
    |1 - (∑ i, groupVelD J 0 (fun j => x * n j) i ^ 2) / (2 * J) ^ 2 - x ^ 2 * ∑ i, n i ^ 4|
      ≤ 3 / 2 * x ^ 4 := by
  obtain ⟨hB, h⟩ := abs_sin_ratio_sub_le hx0 hx1 hn
  have e := massless_groupSpeed_defect (k := fun j => x * n j) hJ hB
  rw [e]
  exact h

/-! ### The rotation residue -/

/-- **The group velocity in physical units** at spacing `a`: hop `J = c/(2a)`, angles `a p`. -/
def scaledVelD (c μ a : ℝ) (p : ι → ℝ) : ι → ℝ := fun i =>
  a * groupVelD (scaledHop c a) μ (fun j => a * p j) i

/-- **The continuum velocity** `c² p / √(μ² + c² |p|²)`. -/
def contVelD (c μ : ℝ) (p : ι → ℝ) : ι → ℝ := fun i =>
  c * (c * p i) / dispE μ (sNorm (fun j => c * p j))

/-- ★★ **The lattice velocity converges to the continuum velocity**, each component within
`c a² (P²/2 + c P³ (1 + d)/(6μ))` for `|p_i| ≤ P`. -/
theorem abs_scaledVelD_sub_le {c μ a P : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ha : 0 < a)
    {p : ι → ℝ} (hp : ∀ j, |p j| ≤ P) (i : ι) :
    |scaledVelD c μ a p i - contVelD c μ p i|
      ≤ c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ)) := by
  have hP : 0 ≤ P := (abs_nonneg _).trans (hp i)
  have h2 := two_mul_scaledHop (c := c) ha.ne'
  have aux : ∀ s cosv E t E' : ℝ,
      a * (2 * scaledHop c a * s * cosv / E) - c * t / E'
        = c * (s / E * (cosv - 1) + (s / E - t / E')) := by
    intro s cosv E t E'
    linear_combination (s * cosv / E) * h2
  have hδ : ∀ j, |sinS (scaledHop c a) (fun j => a * p j) j - c * p j|
      ≤ c * a ^ 2 * P ^ 3 / 6 := fun j => by
    refine (abs_scaledMom_sub_le hc ha (p j)).trans ?_
    have h3 := pow_le_pow_left₀ (abs_nonneg (p j)) (hp j) 3
    have hca : 0 ≤ c * a ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h3 hca
    linarith
  have hE0 : 0 < dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j))) := dispE_pos hμ _
  have h1 : |sinS (scaledHop c a) (fun j => a * p j) i
      / dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))| ≤ 1 := by
    rw [abs_div, abs_of_pos hE0]
    exact (div_le_one hE0).2 (abs_le_dispE_sNorm μ _ i)
  have hpi : (p i) ^ 2 ≤ P ^ 2 := sq_le_sq' (neg_le_of_abs_le (hp i)) (le_of_abs_le (hp i))
  have hcos : |Real.cos (a * p i) - 1| ≤ a ^ 2 * P ^ 2 / 2 := by
    refine (abs_cos_sub_one_le _).trans ?_
    have := mul_le_mul_of_nonneg_left hpi (sq_nonneg a)
    rw [mul_pow]
    linarith
  have hsum : ∑ j, |sinS (scaledHop c a) (fun j => a * p j) j - c * p j|
      ≤ Fintype.card ι * (c * a ^ 2 * P ^ 3 / 6) := by
    calc ∑ j, |sinS (scaledHop c a) (fun j => a * p j) j - c * p j|
        ≤ ∑ _j : ι, c * a ^ 2 * P ^ 3 / 6 := Finset.sum_le_sum fun j _ => hδ j
      _ = Fintype.card ι * (c * a ^ 2 * P ^ 3 / 6) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h3 : |sinS (scaledHop c a) (fun j => a * p j) i
        / dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))
      - c * p i / dispE μ (sNorm (fun j => c * p j))|
      ≤ (c * a ^ 2 * P ^ 3 / 6 + Fintype.card ι * (c * a ^ 2 * P ^ 3 / 6)) / μ :=
    (abs_div_dispE_sNorm_sub_le hμ _ (fun j => c * p j) i).trans
      (div_le_div_of_nonneg_right (add_le_add (hδ i) hsum) hμ.le)
  have e : scaledVelD c μ a p i - contVelD c μ p i
      = c * (sinS (scaledHop c a) (fun j => a * p j) i
            / dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))
          * (Real.cos (a * p i) - 1)
        + (sinS (scaledHop c a) (fun j => a * p j) i
            / dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))
          - c * p i / dispE μ (sNorm (fun j => c * p j)))) :=
    aux (sinS (scaledHop c a) (fun j => a * p j) i) (Real.cos (a * p i))
      (dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))) (c * p i)
      (dispE μ (sNorm (fun j => c * p j)))
  rw [e, abs_mul, abs_of_nonneg hc]
  have hin : |sinS (scaledHop c a) (fun j => a * p j) i
          / dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))
        * (Real.cos (a * p i) - 1)
      + (sinS (scaledHop c a) (fun j => a * p j) i
          / dispE μ (sNorm (sinS (scaledHop c a) (fun j => a * p j)))
        - c * p i / dispE μ (sNorm (fun j => c * p j)))|
      ≤ 1 * (a ^ 2 * P ^ 2 / 2)
        + (c * a ^ 2 * P ^ 3 / 6 + Fintype.card ι * (c * a ^ 2 * P ^ 3 / 6)) / μ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ h3)
    rw [abs_mul]
    exact mul_le_mul h1 hcos (abs_nonneg _) zero_le_one
  calc c * _ ≤ c * (1 * (a ^ 2 * P ^ 2 / 2)
        + (c * a ^ 2 * P ^ 3 / 6 + Fintype.card ι * (c * a ^ 2 * P ^ 3 / 6)) / μ) :=
        mul_le_mul_of_nonneg_left hin hc
    _ = c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ)) := by
        field_simp

/-- The continuum velocity commutes with every linear map that preserves `sNorm`. -/
theorem contVelD_map (c μ : ℝ) (R : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hR : ∀ w, sNorm (R w) = sNorm w) (p : ι → ℝ) :
    contVelD c μ (R p) = R (contVelD c μ p) := by
  have hD : sNorm (fun j => c * R p j) = sNorm (fun j => c * p j) := by
    have e : (fun j => c * R p j) = R (fun j => c * p j) := by
      change c • R p = R (c • p)
      rw [map_smul]
    rw [e, hR]
  have e : ∀ q : ι → ℝ, contVelD c μ q = (c * c / dispE μ (sNorm (fun j => c * q j))) • q :=
    fun q => by
      funext i
      simp only [contVelD, Pi.smul_apply, smul_eq_mul]
      ring
  rw [e, e, hD, map_smul]

/-- ★★★ **The rotation residue (#295).** For a linear map `R` preserving `sNorm` and a
preparation with `|p| ≤ P`: the lattice velocity of the rotated preparation is, in each
component, within `(1 + d)` times the bound of `abs_scaledVelD_sub_le` of the rotated lattice
velocity. -/
theorem rotation_residue {c μ a P : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ha : 0 < a)
    (R : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hR : ∀ w, sNorm (R w) = sNorm w) {p : ι → ℝ}
    (hp : sNorm p ≤ P) (i : ι) :
    |scaledVelD c μ a (R p) i - R (scaledVelD c μ a p) i|
      ≤ (1 + Fintype.card ι)
        * (c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ))) := by
  have hp1 : ∀ j, |p j| ≤ P := fun j => (abs_le_sNorm p j).trans hp
  have hp2 : ∀ j, |R p j| ≤ P := fun j => (abs_le_sNorm _ j).trans ((hR p).le.trans hp)
  have h1 := abs_scaledVelD_sub_le hc hμ ha hp2 i
  have hw : ∀ j, |(contVelD c μ p - scaledVelD c μ a p) j|
      ≤ c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ)) := fun j => by
    rw [Pi.sub_apply, abs_sub_comm]
    exact abs_scaledVelD_sub_le hc hμ ha hp1 j
  have h2 : |R (contVelD c μ p - scaledVelD c μ a p) i|
      ≤ Fintype.card ι
        * (c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ))) := by
    refine (abs_le_sNorm _ i).trans ?_
    rw [hR]
    refine (sNorm_le_sum_abs _).trans ?_
    calc ∑ j, |(contVelD c μ p - scaledVelD c μ a p) j|
        ≤ ∑ _j : ι, c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ)) :=
          Finset.sum_le_sum fun j _ => hw j
      _ = Fintype.card ι
          * (c * a ^ 2 * (P ^ 2 / 2 + c * P ^ 3 * (1 + Fintype.card ι) / (6 * μ))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hRw : R (contVelD c μ p - scaledVelD c μ a p) i
      = contVelD c μ (R p) i - R (scaledVelD c μ a p) i := by
    rw [map_sub, contVelD_map c μ R hR, Pi.sub_apply]
  have e : scaledVelD c μ a (R p) i - R (scaledVelD c μ a p) i
      = (scaledVelD c μ a (R p) i - contVelD c μ (R p) i)
        + R (contVelD c μ p - scaledVelD c μ a p) i := by
    rw [hRw]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith

end CSD.CV

end
