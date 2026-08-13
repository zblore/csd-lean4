/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerWeights
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Group.AddCircle

/-!
# SigmaLayer/NullSeamWitness: the third horn — continuous, exact Born, null seam

**Category:** dynamical measurement — the "Cantor-horn" candidate brick recorded against
the fourth external review (2026-08-03), delivered — and *simpler than the
devil's-staircase sketch that motivated it*.

## The idea

`no_everywhere_correlation` kills {continuity + **everywhere**-exact records}. The two
formalised horns paid for that with seams (piecewise) or with an `ε`-corridor of Born
error (smooth witness). The reviewer observed a third option was not excluded: continuous
dynamics with records exact off a **null** seam and **exact** Born. This module exhibits
it — and the mechanism is not a Cantor function. The transition between two record
regions dodges the record gap by crossing **where the record regions kiss**: the moment
regions `{m₁ > ½}` and `{m₂ > ½}` share the boundary state `m₁ = m₂ = ½`, and a rotation
in the `(f₁, f₂)`-plane travels from one region to the other touching the complement at
exactly **one** projective point. Sweeping that crossing angle continuously in the
register coordinate `θ` — crossing `π/4` exactly at the two cell-boundary points — gives:

- ★★ `nullSeamClosure` — a **continuous** (`continuous_nullSeamEvolve`),
  **measure-preserving** (`nullSeamEvolve_measurePreserving`) skew-unitary propagator
  on `S¹ × ℂℙ²` whose landing from the calibrated ready state is in the **correct record
  region for every `θ` off a two-point seam** (`nullSeam_landing_neg/pos`,
  `nullSeam_seam_null`), with **exact** Born weights `r` and `1 − r`
  (`nullSeam_born_left/right`) — no `ε`.

The seam profile is `nullSeamSign θ = infDist θ I₁ − infDist θ I₂` (the two closed cell
arcs): continuous, negative exactly on the open first cell, positive exactly on the open
second, zero exactly at the two boundary points — circle-intrinsic, no fundamental-domain
lift, no case analysis at the wrap point.

⚠️ *Naming corrected 2026-08-03 (fifth external review, and the reviewer is right).* The
invariant measure here was originally called `nullSeamLiouville`. (*Corrected 2026-08-04 (independent Opus review of HEAD).* — the global rename
rewrote this sentence too, so the correction read as a no-op: it named the *new* name as the
old one. Exactly the class of defect it was describing.) **`S¹ × ℂℙ²` has real
dimension 5 — odd — so it carries no symplectic structure and the word "Liouville" was
unearned.** The measure (Haar ⊗ Fubini–Study) is genuinely invariant and every theorem below
stands unchanged; only the name and the surrounding prose overclaimed. It is now
`nullSeamMeasure`, and invariance is stated as measure-preservation. Earning the symplectic
word means lifting the register `S¹` to the full `T²` and working on `T² × ℂℙ²` (even
dimension) — recorded in `BACKLOG.md`, not done here. *(This is the corpus's second
odd-dimension slip; the first is recorded in the fibred-Σ correction.)*

⚠️ *Scope note 2026-08-04:* "Born" here is carried by the **cell split** `r`, a free
parameter of the construction. Unlike every other horn (`pointer_born_lower` reads
`c.rate p j`; `join_sector_born` reads `∑ ‖⟨eⱼ,ψ⟩‖²`), this module contains no preparation,
no ray and no moment map. That is adequate for what the horn claims — an *existence* result
against a no-go (`no_everywhere_correlation`) that is itself preparation-free, and every
`r ∈ (0,1)` is some preparation's Born weight — but the identification of `r` with a Born
weight is stated here, not formalised.

## The price — and the trilemma

⚠️ **Honest scope.** The exactness statements are at the **Dirac-calibrated ready point**
`q = [f₀]` — this is the third horn's price, and it is real: with a positive-width ready
region `{m₀ > 1 − δ}`, states near the crossing angle land near the kissing state, and
because the stroke is a homeomorphism their image is an **open** neighbourhood of it —
which necessarily meets the interior of the no-record set, giving that set **positive
measure** (`posMeasure_noRecord_of_isOpenMap`, `SigmaLayer/SharpenedNoGo.lean`). A Dirac
calibration escapes precisely because a point has no neighbourhood to spare, which is how
this witness threads the kissing state exactly. ⚠️ *Corrected 2026-08-04:* this note
previously said the seam fattens "to a positive-measure set **of order the calibration
width**". The *order* is a quantitative claim that the topological argument does not give
and that is not proved anywhere; it needed an estimate on how far the landing moments move
with the ready state. Positive measure stands; `O(δ)` was an over-assertion. The corpus already prices Dirac calibration:
`collapse_accuracy_bound`. The honest classification is therefore a **trilemma** — each
horn pays exactly one of: **seams** (piecewise witness, discontinuous propagator),
**ε-Born** (smooth witness, positive-measure ready state), **Dirac calibration** (this
witness, exact records a.e. and exact Born). ~~Whether a fourth combination
(continuous + positive-width ready + exact-Born-and-a.e.-records) is impossible is a
candidate *sharpened no-go*, recorded, not claimed.~~ *Updated 2026-08-05:* on the
pointer's moment-region geometry this is now a **theorem** — `posMeasure_noRecord_pointer`
(`SigmaLayer/NoRecordGeometry.lean`): continuity + open-map + open preconnected
positive-width ready + two-outcome correlation force a positive-measure no-record set, so
exact-a.e. records force Dirac calibration. General exhaustiveness over *all* arenas
remains research, not claimed. Further scope: two cells and a
`ℂℙ²` pointer (the horn is an existence claim; **general `N` DONE 2026-08-12** —
`NullSeamGeneralN.lean`, `nullSeamGenClosure`: every `N ≥ 2` and every weight vector,
via plateau tents and a single amplitude-polynomial rotation); the terminal stroke is exhibited as a continuous
skew-unitary map (time-ramping through `pointerRamp`/`smoothPointerRamp` is the same
mechanical wrapping as brick 4 and is not duplicated); no protocol packaging.

## References

`specs/BACKLOG.md` (the Cantor-horn row — this discharges it; fourth external review
2026-08-03); `docs/TOUR.md` §"Which horn is the right one?" (updated to the trilemma);
`SigmaLayer/PointerArena.lean` (`Pointer`, `recordRegion`, `readyState`,
`momentMap_add_le_one` — the kissing geometry), `SigmaLayer/PointerWeights.lean` (the
continuity-descent and skew-product idioms this reuses), `SigmaLayer/ShearDiscontinuity.
lean` (`shearEvolve_not_continuous` — what the first horn pays),
`SigmaLayer/PointerBorn.lean` (the `ε` the second horn pays),
`SigmaLayer/Measurement.lean` (`collapse_accuracy_bound` — the price tag on the third).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup Metric
open scoped LinearAlgebra.Projectivization

/-! ### Circle toolkit: lifts, half-diameter, coe-distance -/

/-- Round is the nearest integer: subtracting it can only shrink the absolute value. -/
lemma abs_sub_round_le_abs (c : ℝ) : |c - round c| ≤ |c| := by
  rcases le_or_gt (1 / 2) |c| with h | h
  · exact (abs_sub_round c).trans h
  · have h0 : round c = 0 := by
      rw [round_eq]
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast
        linarith [(abs_lt.mp h).1]
      · push_cast
        linarith [(abs_lt.mp h).2]
    rw [h0]
    simp

/-- Every point of the unit circle has a lift realising its norm, of size at most `½`. -/
lemma exists_norm_lift (z : CircleFibre) :
    ∃ c : ℝ, (c : CircleFibre) = z ∧ |c| = ‖z‖ ∧ |c| ≤ 1 / 2 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  refine ⟨x - round x, ?_, ?_, ?_⟩
  · rw [AddCircle.coe_sub,
      show (((round x : ℝ)) : CircleFibre) = 0 from
        (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x, by simp⟩,
      sub_zero]
  · rw [show ‖(QuotientAddGroup.mk x : CircleFibre)‖ = |x - round x| from
      UnitAddCircle.norm_eq]
  · exact abs_sub_round x

/-- The unit circle has diameter `½`. -/
lemma circle_dist_le_half (z w : CircleFibre) : dist z w ≤ 1 / 2 := by
  obtain ⟨c, _, hnorm, hle⟩ := exists_norm_lift (z - w)
  rw [dist_eq_norm, ← hnorm]
  exact hle

/-- Distance on the circle is dominated by the distance of any pair of lifts. -/
lemma circle_dist_coe_le (a b : ℝ) : dist ((a : ℝ) : CircleFibre) ((b : ℝ) : CircleFibre)
    ≤ |a - b| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  exact abs_sub_round_le_abs _

/-! ### The two cell arcs and the seam profile -/

/-- The first closed cell arc: the image of `[0, r]`. -/
def seamArcL (r : ℝ) : Set CircleFibre :=
  (fun s : ℝ => (s : CircleFibre)) '' Set.Icc 0 r

/-- The second closed cell arc: the image of `[r, 1]`. -/
def seamArcR (r : ℝ) : Set CircleFibre :=
  (fun s : ℝ => (s : CircleFibre)) '' Set.Icc r 1

lemma isClosed_seamArcL (r : ℝ) : IsClosed (seamArcL r) :=
  (isCompact_Icc.image (AddCircle.continuous_mk' (p := (1 : ℝ)))).isClosed

lemma isClosed_seamArcR (r : ℝ) : IsClosed (seamArcR r) :=
  (isCompact_Icc.image (AddCircle.continuous_mk' (p := (1 : ℝ)))).isClosed

lemma seamArc_union (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    seamArcL r ∪ seamArcR r = Set.univ := by
  rw [seamArcL, seamArcR, ← Set.image_union, Set.Icc_union_Icc_eq_Icc hr0 hr1]
  have := AddCircle.coe_image_Icc_eq (p := (1 : ℝ)) (a := (0 : ℝ))
  rw [zero_add] at this
  exact this

/-- The two closed arcs meet exactly at the two boundary points. -/
lemma seamArc_inter (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    seamArcL r ∩ seamArcR r = {((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)} := by
  ext θ
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
    have hst' : ((t : ℝ) : CircleFibre) = ((s : ℝ) : CircleFibre) := hst
    have hz : ((t - s : ℝ) : CircleFibre) = 0 := by
      rw [AddCircle.coe_sub, hst', sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    have hn' : (n : ℝ) = t - s := by
      rw [← hn]
      simp
    have hb1 : (0 : ℝ) ≤ t - s := by linarith [hs.2, ht.1]
    have hb2 : t - s ≤ 1 := by linarith [hs.1, ht.2]
    have hncases : n = 0 ∨ n = 1 := by
      have h1 : (0 : ℝ) ≤ (n : ℝ) := hn' ▸ hb1
      have h2 : (n : ℝ) ≤ 1 := hn' ▸ hb2
      have h1' : (0 : ℤ) ≤ n := by exact_mod_cast h1
      have h2' : n ≤ (1 : ℤ) := by exact_mod_cast h2
      omega
    rcases hncases with hn0 | hn1
    · -- `t = s`: the lifts agree, so both constraints force `s = r`.
      have hts : t = s := by
        rw [hn0] at hn'
        push_cast at hn'
        linarith
      have hsr : s = r := le_antisymm hs.2 (hts ▸ ht.1)
      subst hsr
      exact Or.inr rfl
    · -- `t = s + 1`: forces `s = 0`.
      have hts : t = s + 1 := by
        rw [hn1] at hn'
        push_cast at hn'
        linarith
      have hs0 : s = 0 := le_antisymm (by linarith [ht.2]) hs.1
      subst hs0
      exact Or.inl rfl
  · have hone : ((1 : ℝ) : CircleFibre) = ((0 : ℝ) : CircleFibre) := by
      have h1 : ((1 : ℝ) : CircleFibre) = 0 := AddCircle.coe_period (1 : ℝ)
      rw [h1]
      simp
    rintro (rfl | rfl)
    · exact ⟨⟨0, ⟨le_refl 0, hr0.le⟩, rfl⟩, ⟨1, ⟨hr1.le, le_refl 1⟩, hone⟩⟩
    · exact ⟨⟨r, ⟨hr0.le, le_refl r⟩, rfl⟩, ⟨r, ⟨le_refl r, hr1.le⟩, rfl⟩⟩

/-- **The seam profile**: signed by which closed arc is nearer. Continuous,
circle-intrinsic, negative exactly on the open first cell, positive exactly on the open
second, zero exactly at the two boundary points. -/
noncomputable def nullSeamSign (r : ℝ) (θ : CircleFibre) : ℝ :=
  infDist θ (seamArcL r) - infDist θ (seamArcR r)

lemma continuous_nullSeamSign (r : ℝ) : Continuous (nullSeamSign r) :=
  (continuous_infDist_pt _).sub (continuous_infDist_pt _)

lemma seamArcL_nonempty (r : ℝ) (hr0 : 0 < r) : (seamArcL r).Nonempty :=
  ⟨_, ⟨0, ⟨le_refl 0, hr0.le⟩, rfl⟩⟩

lemma seamArcR_nonempty (r : ℝ) (hr1 : r < 1) : (seamArcR r).Nonempty :=
  ⟨_, ⟨r, ⟨le_refl r, hr1.le⟩, rfl⟩⟩

/-- Negativity region: exactly the first arc minus the seam points. -/
lemma nullSeamSign_neg_iff (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre) :
    nullSeamSign r θ < 0 ↔ θ ∈ seamArcL r \ seamArcR r := by
  constructor
  · intro h
    have hL : θ ∈ seamArcL r := by
      by_contra hnot
      have h2 : 0 < infDist θ (seamArcL r) :=
        ((isClosed_seamArcL r).notMem_iff_infDist_pos (seamArcL_nonempty r hr0)).mp hnot
      have h3 : 0 ≤ infDist θ (seamArcR r) := infDist_nonneg
      rw [nullSeamSign] at h
      -- both distances nonneg; if θ ∈ R the sign is ≥ 0, if θ ∉ R it is in NEITHER arc,
      -- contradicting the cover
      by_cases hR : θ ∈ seamArcR r
      · rw [infDist_zero_of_mem hR] at h
        linarith
      · have := seamArc_union r hr0.le hr1.le
        have : θ ∈ seamArcL r ∪ seamArcR r := this ▸ Set.mem_univ θ
        exact absurd this (by simp [hnot, hR])
    have hR : θ ∉ seamArcR r := by
      intro hR
      rw [nullSeamSign, infDist_zero_of_mem hR] at h
      linarith [infDist_nonneg (s := seamArcL r) (x := θ)]
    exact ⟨hL, hR⟩
  · rintro ⟨hL, hR⟩
    rw [nullSeamSign, infDist_zero_of_mem hL]
    have := ((isClosed_seamArcR r).notMem_iff_infDist_pos (seamArcR_nonempty r hr1)).mp hR
    linarith

/-- Positivity region: exactly the second arc minus the seam points. -/
lemma nullSeamSign_pos_iff (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre) :
    0 < nullSeamSign r θ ↔ θ ∈ seamArcR r \ seamArcL r := by
  constructor
  · intro h
    have hR : θ ∈ seamArcR r := by
      by_contra hnot
      by_cases hL : θ ∈ seamArcL r
      · rw [nullSeamSign, infDist_zero_of_mem hL] at h
        have := ((isClosed_seamArcR r).notMem_iff_infDist_pos
          (seamArcR_nonempty r hr1)).mp hnot
        linarith
      · have hcov := seamArc_union r hr0.le hr1.le
        have : θ ∈ seamArcL r ∪ seamArcR r := hcov ▸ Set.mem_univ θ
        exact absurd this (by simp [hnot, hL])
    have hL : θ ∉ seamArcL r := by
      intro hL
      rw [nullSeamSign, infDist_zero_of_mem hL] at h
      linarith [infDist_nonneg (s := seamArcR r) (x := θ)]
    exact ⟨hR, hL⟩
  · rintro ⟨hR, hL⟩
    rw [nullSeamSign, infDist_zero_of_mem hR]
    have := ((isClosed_seamArcL r).notMem_iff_infDist_pos (seamArcL_nonempty r hr0)).mp hL
    linarith

/-- **The seam is exactly the two boundary points.** -/
lemma nullSeamSign_eq_zero_iff (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre) :
    nullSeamSign r θ = 0
      ↔ θ = ((0 : ℝ) : CircleFibre) ∨ θ = ((r : ℝ) : CircleFibre) := by
  constructor
  · intro h
    have hL : θ ∈ seamArcL r := by
      by_contra hnot
      rcases (nullSeamSign_pos_iff r hr0 hr1 θ).mpr
        ⟨(by
          have hcov := seamArc_union r hr0.le hr1.le
          have hmem : θ ∈ seamArcL r ∪ seamArcR r := hcov ▸ Set.mem_univ θ
          rcases hmem with h1 | h2
          · exact absurd h1 hnot
          · exact h2), hnot⟩ |>.ne' h
    have hR : θ ∈ seamArcR r := by
      by_contra hnot
      exact ((nullSeamSign_neg_iff r hr0 hr1 θ).mpr ⟨hL, hnot⟩).ne h
    have := seamArc_inter r hr0 hr1 ▸ Set.mem_inter hL hR
    simpa using this
  · intro h
    have hmem : θ ∈ seamArcL r ∩ seamArcR r := by
      rw [seamArc_inter r hr0 hr1]
      simpa using h
    rw [nullSeamSign, infDist_zero_of_mem hmem.1, infDist_zero_of_mem hmem.2, sub_zero]

/-- The seam profile is bounded by the circle's half-diameter. -/
lemma abs_nullSeamSign_le (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre) :
    |nullSeamSign r θ| ≤ 1 / 2 := by
  have hL : infDist θ (seamArcL r) ≤ 1 / 2 := by
    refine (infDist_le_dist_of_mem (seamArcL_nonempty r hr0).choose_spec).trans ?_
    exact circle_dist_le_half _ _
  have hR : infDist θ (seamArcR r) ≤ 1 / 2 := by
    refine (infDist_le_dist_of_mem (seamArcR_nonempty r hr1).choose_spec).trans ?_
    exact circle_dist_le_half _ _
  have h0L : 0 ≤ infDist θ (seamArcL r) := infDist_nonneg
  have h0R : 0 ≤ infDist θ (seamArcR r) := infDist_nonneg
  rw [nullSeamSign, abs_le]
  constructor <;> linarith

/-! ### The crossing angle and the record criterion -/

/-- The crossing angle: `π/4` exactly on the seam, `< π/4` in the first cell, `> π/4` in
the second — always inside `(0, π/2)`. -/
noncomputable def nullSeamAngle (r : ℝ) (θ : CircleFibre) : ℝ :=
  Real.pi / 4 + nullSeamSign r θ

lemma nullSeamAngle_mem (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre) :
    nullSeamAngle r θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hb := abs_le.mp (abs_nullSeamSign_le r hr0 hr1 θ)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  constructor
  · rw [nullSeamAngle]
    linarith [hb.1]
  · rw [nullSeamAngle]
    linarith [hb.2]

/-- The record criterion at the crossing angle: `cos²χ > ½ ↔ χ < π/4` inside the
window. -/
lemma cos_sq_gt_half_iff {χ : ℝ} (hχ : χ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 / 2 < Real.cos χ ^ 2 ↔ χ < Real.pi / 4 := by
  rw [Real.cos_sq]
  constructor
  · intro h
    have hcos : 0 < Real.cos (2 * χ) := by linarith
    by_contra hge
    push Not at hge
    have : Real.cos (2 * χ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith)
        (by nlinarith [hχ.2, Real.pi_pos])
    linarith
  · intro h
    have : 0 < Real.cos (2 * χ) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hχ.1, Real.pi_pos], by linarith⟩
    linarith

/-- The complementary criterion: `sin²χ > ½ ↔ χ > π/4` inside the window. -/
lemma sin_sq_gt_half_iff {χ : ℝ} (hχ : χ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 / 2 < Real.sin χ ^ 2 ↔ Real.pi / 4 < χ := by
  have hsin : Real.sin χ ^ 2 = 1 - Real.cos χ ^ 2 := by
    have := Real.sin_sq_add_cos_sq χ
    linarith
  rw [hsin, Real.cos_sq]
  constructor
  · intro h
    have hcos : Real.cos (2 * χ) < 0 := by linarith
    by_contra hge
    push Not at hge
    have : 0 ≤ Real.cos (2 * χ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hχ.1, Real.pi_pos], by linarith⟩
    linarith
  · intro h
    have : Real.cos (2 * χ) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith)
        (by nlinarith [hχ.2, Real.pi_pos])
    linarith

/-! ### The witness unitary -/

/-- The witness matrix at crossing angle `χ`: sends the ready direction `f₀` to
`cos χ · f₁ + sin χ · f₂` — the record-to-record crossing through the kissing state. -/
noncomputable def nullSeamMat (χ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of
    ![![0, 0, 1],
      ![(Real.cos χ : ℂ), -(Real.sin χ : ℂ), 0],
      ![(Real.sin χ : ℂ), (Real.cos χ : ℂ), 0]]

lemma nullSeamMat_mem (χ : ℝ) : nullSeamMat χ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nullSeamMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.conj_ofReal,
       ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_neg,
       ← Complex.ofReal_one, ← Complex.ofReal_zero]
     exact Complex.ofReal_inj.mpr
       (by nlinarith [Real.sin_sq_add_cos_sq χ, Real.cos_sq_add_sin_sq χ]))

/-- The witness unitary family over the register circle. -/
noncomputable def nullSeamUU (r : ℝ) (θ : CircleFibre) :
    Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨nullSeamMat (nullSeamAngle r θ), nullSeamMat_mem _⟩

/-- **The null-seam propagator**: register conserved, pointer rotated by the crossing
unitary at the register's crossing angle. -/
noncomputable def nullSeamEvolve (r : ℝ) :
    CircleFibre × Pointer 2 → CircleFibre × Pointer 2 :=
  fun y => (y.1, nullSeamUU r y.1 • y.2)

/-! ### Landing at the calibrated ready point -/

/-- The landing vector: `cos χ · f₁ + sin χ · f₂`. -/
noncomputable def nullSeamVec (χ : ℝ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![0, (Real.cos χ : ℂ), (Real.sin χ : ℂ)]

lemma nullSeamVec_ne_zero {χ : ℝ} (hχ : χ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    nullSeamVec χ ≠ 0 := by
  intro h
  have h1 : (nullSeamVec χ) 1 = 0 := by rw [h]; rfl
  have h2 : (nullSeamVec χ) 1 = (Real.cos χ : ℂ) := rfl
  rw [h2] at h1
  have : Real.cos χ = 0 :=
    Complex.ofReal_injective (by rw [Complex.ofReal_zero]; exact h1)
  have hpos : 0 < Real.cos χ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hχ.1, Real.pi_pos], by linarith [hχ.2]⟩
  linarith

lemma norm_nullSeamVec (χ : ℝ) : ‖nullSeamVec χ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ i : Fin 3, ‖(nullSeamVec χ) i‖ ^ 2 = 1 := by
    rw [Fin.sum_univ_three]
    show ‖(0 : ℂ)‖ ^ 2 + ‖((Real.cos χ : ℝ) : ℂ)‖ ^ 2 + ‖((Real.sin χ : ℝ) : ℂ)‖ ^ 2 = 1
    rw [norm_zero, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs]
    have := Real.sin_sq_add_cos_sq χ
    linarith
  rw [this, Real.sqrt_one]

/-- The witness matrix sends the ready vertex vector to the landing vector. -/
lemma nullSeamMat_mulVec (χ : ℝ) :
    Matrix.toEuclideanLin (nullSeamMat χ) (EuclideanSpace.single 0 (1 : ℂ))
      = nullSeamVec χ := by
  rw [Matrix.toLpLin_apply]
  apply PiLp.ext
  intro i
  show (nullSeamMat χ *ᵥ WithLp.ofLp (EuclideanSpace.single 0 (1 : ℂ))) i = _
  rw [PiLp.ofLp_single, Matrix.mulVec_single]
  fin_cases i <;> simp [nullSeamMat, nullSeamVec]

/-- **The landing identity**: the propagator sends the calibrated ready state to the
crossing ray. -/
lemma nullSeamEvolve_ready (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre) :
    (nullSeamEvolve r (θ, readyState)).2
      = Projectivization.mk ℂ (nullSeamVec (nullSeamAngle r θ))
          (nullSeamVec_ne_zero (nullSeamAngle_mem r hr0 hr1 θ)) := by
  show nullSeamUU r θ • readyState = _
  rw [readyState, vertexPoint,
    Projectivization.smul_mk_eq_mk_toEuclideanLin _ (single_ne_zero' 0)]
  congr 1
  exact nullSeamMat_mulVec _

/-- The landing moments: `m₁ = cos²χ`, `m₂ = sin²χ`. -/
lemma momentMap_nullSeamVec (χ : ℝ) (hχ : χ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (i : Fin 3) :
    LF4.momentMap (Projectivization.mk ℂ (nullSeamVec χ) (nullSeamVec_ne_zero hχ)) i
      = ‖(nullSeamVec χ) i‖ ^ 2 := by
  rw [LF4.momentMap_mk_eq_inner_sq _ _ (norm_nullSeamVec χ) i,
    EuclideanSpace.inner_single_left]
  simp

/-! ### ★ Records off the seam, both outcomes, exactly -/

/-- ★ In the open first cell, the landing carries record `0` — exactly. -/
theorem nullSeam_landing_neg (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre)
    (hθ : nullSeamSign r θ < 0) :
    (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 0 := by
  rw [nullSeamEvolve_ready r hr0 hr1 θ]
  show (1 : ℝ) / 2 < LF4.momentMap _ (Fin.succ 0)
  rw [show Fin.succ (0 : Fin 2) = (1 : Fin 3) from rfl,
    momentMap_nullSeamVec _ (nullSeamAngle_mem r hr0 hr1 θ)]
  show (1 : ℝ) / 2 < ‖((Real.cos (nullSeamAngle r θ) : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (cos_sq_gt_half_iff (nullSeamAngle_mem r hr0 hr1 θ)).mpr
    (by rw [nullSeamAngle]; linarith)

/-- ★ In the open second cell, the landing carries record `1` — exactly. -/
theorem nullSeam_landing_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : CircleFibre)
    (hθ : 0 < nullSeamSign r θ) :
    (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 1 := by
  rw [nullSeamEvolve_ready r hr0 hr1 θ]
  show (1 : ℝ) / 2 < LF4.momentMap _ (Fin.succ 1)
  rw [show Fin.succ (1 : Fin 2) = (2 : Fin 3) from rfl,
    momentMap_nullSeamVec _ (nullSeamAngle_mem r hr0 hr1 θ)]
  show (1 : ℝ) / 2 < ‖((Real.sin (nullSeamAngle r θ) : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (sin_sq_gt_half_iff (nullSeamAngle_mem r hr0 hr1 θ)).mpr
    (by rw [nullSeamAngle]; linarith)

/-- ★ **The seam is null** — indeed two points. -/
theorem nullSeam_seam_null (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (volume : Measure CircleFibre) {θ | nullSeamSign r θ = 0} = 0 := by
  have hset : {θ | nullSeamSign r θ = 0}
      = {((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)} := by
    ext θ
    exact nullSeamSign_eq_zero_iff r hr0 hr1 θ
  have hpt : ∀ c : ℝ, (volume : Measure CircleFibre) {((c : ℝ) : CircleFibre)} = 0 := by
    intro c
    refine le_zero_iff.mp ?_
    calc (volume : Measure CircleFibre) {((c : ℝ) : CircleFibre)}
        ≤ volume (Metric.closedBall (((c : ℝ) : CircleFibre)) 0) :=
          measure_mono (by
            intro x hx
            rw [Set.mem_singleton_iff] at hx
            subst hx
            exact Metric.mem_closedBall_self le_rfl)
      _ = 0 := by
          rw [AddCircle.volume_closedBall]
          norm_num
  rw [hset, Set.insert_eq]
  refine le_zero_iff.mp ((measure_union_le _ _).trans ?_)
  rw [hpt 0, hpt r, add_zero]

/-! ### ★ Exact Born -/

/-- The record-`0` outcome set is exactly the negativity region. -/
lemma nullSeam_outcome_left (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    {θ | (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 0}
      = {θ | nullSeamSign r θ < 0} := by
  ext θ
  constructor
  · intro h
    by_contra hge
    have hge' : ¬ nullSeamSign r θ < 0 := hge
    rcases eq_or_lt_of_le (not_lt.mp hge') with heq | hpos
    · -- on the seam: the landing is the kissing state, in no record region
      have hmem := h
      rw [Set.mem_ofPred_eq, nullSeamEvolve_ready r hr0 hr1 θ] at hmem
      have : (1 : ℝ) / 2 < ‖((Real.cos (nullSeamAngle r θ) : ℝ) : ℂ)‖ ^ 2 := by
        have := hmem
        rw [recordRegion, Set.mem_ofPred_eq,
          show Fin.succ (0 : Fin 2) = (1 : Fin 3) from rfl,
          momentMap_nullSeamVec _ (nullSeamAngle_mem r hr0 hr1 θ)] at this
        exact this
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
      have hlt := (cos_sq_gt_half_iff (nullSeamAngle_mem r hr0 hr1 θ)).mp this
      rw [nullSeamAngle] at hlt
      linarith
    · -- in the positivity region: record 1 excludes record 0
      have h1 := nullSeam_landing_pos r hr0 hr1 θ hpos
      have hdisj := recordRegion_pairwiseDisjoint (K := 2) (by norm_num : (0 : Fin 2) ≠ 1)
      exact Set.disjoint_left.mp hdisj h h1
  · exact nullSeam_landing_neg r hr0 hr1 θ

/-- ★ **Exact Born, left cell**: the record-`0` outcome set has measure exactly `r`. -/
theorem nullSeam_born_left (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (volume : Measure CircleFibre)
        {θ | (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 0}
      = ENNReal.ofReal r := by
  rw [nullSeam_outcome_left r hr0 hr1]
  -- sandwich the negativity region between the open and closed balls of radius r/2
  have hmid : ∀ u : ℝ, |u| ≤ r / 2 →
      (((r / 2 + u : ℝ)) : CircleFibre) ∈ seamArcL r := by
    intro u hu
    exact ⟨r / 2 + u, ⟨by linarith [abs_le.mp hu |>.1], by linarith [abs_le.mp hu |>.2]⟩,
      rfl⟩
  have hsub₂ : {θ | nullSeamSign r θ < 0}
      ⊆ Metric.closedBall (((r / 2 : ℝ)) : CircleFibre) (r / 2) := by
    intro θ hθ
    obtain ⟨⟨s, hs, rfl⟩, -⟩ := (nullSeamSign_neg_iff r hr0 hr1 θ).mp hθ
    rw [Metric.mem_closedBall]
    refine (circle_dist_coe_le s (r / 2)).trans ?_
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hsub₁ : Metric.closedBall (((r / 2 : ℝ)) : CircleFibre) (r / 2)
      ⊆ {θ | nullSeamSign r θ < 0}
        ∪ {((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)} := by
    intro θ hθ
    obtain ⟨u, hu, hnorm, -⟩ := exists_norm_lift (θ - (((r / 2 : ℝ)) : CircleFibre))
    have hdist : |u| ≤ r / 2 := by
      rw [hnorm, ← dist_eq_norm]
      exact Metric.mem_closedBall.mp hθ
    have hrep : θ = (((r / 2 + u : ℝ)) : CircleFibre) := by
      rw [AddCircle.coe_add, hu, add_sub_cancel]
    have hL : θ ∈ seamArcL r := hrep ▸ hmid u hdist
    by_cases hR : θ ∈ seamArcR r
    · right
      have := seamArc_inter r hr0 hr1 ▸ Set.mem_inter hL hR
      simpa using this
    · left
      exact (nullSeamSign_neg_iff r hr0 hr1 θ).mpr ⟨hL, hR⟩
  have hpair : (volume : Measure CircleFibre)
      {((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)} = 0 := by
    have h := nullSeam_seam_null r hr0 hr1
    rw [show {θ | nullSeamSign r θ = 0}
        = ({((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)} : Set CircleFibre) from
      Set.ext fun θ => nullSeamSign_eq_zero_iff r hr0 hr1 θ] at h
    exact h
  have hball : (volume : Measure CircleFibre)
      (Metric.closedBall (((r / 2 : ℝ)) : CircleFibre) (r / 2)) = ENNReal.ofReal r := by
    rw [AddCircle.volume_closedBall]
    congr 1
    rw [min_eq_right (by linarith)]
    ring
  refine le_antisymm ?_ ?_
  · calc (volume : Measure CircleFibre) {θ | nullSeamSign r θ < 0}
        ≤ volume (Metric.closedBall (((r / 2 : ℝ)) : CircleFibre) (r / 2)) :=
          measure_mono hsub₂
      _ = ENNReal.ofReal r := hball
  · calc ENNReal.ofReal r
        = volume (Metric.closedBall (((r / 2 : ℝ)) : CircleFibre) (r / 2)) := hball.symm
      _ ≤ volume ({θ | nullSeamSign r θ < 0}
            ∪ {((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)}) := measure_mono hsub₁
      _ ≤ volume {θ | nullSeamSign r θ < 0} + volume
            ({((0 : ℝ) : CircleFibre), ((r : ℝ) : CircleFibre)} : Set CircleFibre) :=
          measure_union_le _ _
      _ = volume {θ | nullSeamSign r θ < 0} := by rw [hpair, add_zero]

/-- The record-`1` outcome set is exactly the positivity region. -/
lemma nullSeam_outcome_right (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    {θ | (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 1}
      = {θ | 0 < nullSeamSign r θ} := by
  ext θ
  constructor
  · intro h
    by_contra hge
    have hge' : ¬ 0 < nullSeamSign r θ := hge
    rcases eq_or_lt_of_le (not_lt.mp hge') with heq | hneg
    · have hmem := h
      rw [Set.mem_ofPred_eq, nullSeamEvolve_ready r hr0 hr1 θ] at hmem
      have : (1 : ℝ) / 2 < ‖((Real.sin (nullSeamAngle r θ) : ℝ) : ℂ)‖ ^ 2 := by
        have := hmem
        rw [recordRegion, Set.mem_ofPred_eq,
          show Fin.succ (1 : Fin 2) = (2 : Fin 3) from rfl,
          momentMap_nullSeamVec _ (nullSeamAngle_mem r hr0 hr1 θ)] at this
        exact this
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
      have hlt := (sin_sq_gt_half_iff (nullSeamAngle_mem r hr0 hr1 θ)).mp this
      rw [nullSeamAngle] at hlt
      linarith
    · have h0 := nullSeam_landing_neg r hr0 hr1 θ hneg
      have hdisj := recordRegion_pairwiseDisjoint (K := 2) (by norm_num : (0 : Fin 2) ≠ 1)
      exact Set.disjoint_right.mp hdisj h h0
  · exact nullSeam_landing_pos r hr0 hr1 θ

/-- ★ **Exact Born, right cell**: the record-`1` outcome set has measure exactly
`1 − r`. -/
theorem nullSeam_born_right (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (volume : Measure CircleFibre)
        {θ | (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 1}
      = ENNReal.ofReal (1 - r) := by
  rw [nullSeam_outcome_right r hr0 hr1]
  have hmeas_neg : MeasurableSet {θ | nullSeamSign r θ < 0} :=
    measurableSet_lt (continuous_nullSeamSign r).measurable measurable_const
  have hmeas_pos : MeasurableSet {θ | 0 < nullSeamSign r θ} :=
    measurableSet_lt measurable_const (continuous_nullSeamSign r).measurable
  -- complement decomposition: {¬(0 < ψ)} = {ψ < 0} ∪ {ψ = 0}
  have hcompl : {θ | 0 < nullSeamSign r θ}ᶜ
      = {θ | nullSeamSign r θ < 0} ∪ {θ | nullSeamSign r θ = 0} := by
    ext θ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, not_lt]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h)
      · exact h.le
      · exact h.le
  have htotal := measure_add_measure_compl (μ := (volume : Measure CircleFibre)) hmeas_pos
  rw [hcompl] at htotal
  have hzero := nullSeam_seam_null r hr0 hr1
  have hunion : (volume : Measure CircleFibre)
      ({θ | nullSeamSign r θ < 0} ∪ {θ | nullSeamSign r θ = 0})
      = ENNReal.ofReal r := by
    refine le_antisymm ?_ ?_
    · refine (measure_union_le _ _).trans ?_
      rw [show (volume : Measure CircleFibre) {θ | nullSeamSign r θ < 0}
          = ENNReal.ofReal r from by
        have := nullSeam_born_left r hr0 hr1
        rw [nullSeam_outcome_left r hr0 hr1] at this
        exact this, hzero, add_zero]
    · rw [show ENNReal.ofReal r
          = (volume : Measure CircleFibre) {θ | nullSeamSign r θ < 0} from by
        have := nullSeam_born_left r hr0 hr1
        rw [nullSeam_outcome_left r hr0 hr1] at this
        exact this.symm]
      exact measure_mono Set.subset_union_left
  rw [hunion] at htotal
  rw [measure_univ] at htotal
  have hsolve : (volume : Measure CircleFibre) {θ | 0 < nullSeamSign r θ}
      = 1 - ENNReal.ofReal r :=
    ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top htotal
  rw [hsolve, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ r)]

/-! ### ★★ Continuity and measure invariance -/

/-- Entrywise continuity of the witness family over the register. -/
lemma continuous_nullSeamMat_entry (r : ℝ) (a b : Fin 3) :
    Continuous fun θ : CircleFibre => nullSeamMat (nullSeamAngle r θ) a b := by
  have hχ : Continuous (nullSeamAngle r) :=
    continuous_const.add (continuous_nullSeamSign r)
  have hcos : Continuous fun θ : CircleFibre =>
      ((Real.cos (nullSeamAngle r θ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp hχ)
  have hsin : Continuous fun θ : CircleFibre =>
      ((Real.sin (nullSeamAngle r θ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp hχ)
  fin_cases a <;> fin_cases b <;>
    simp only [nullSeamMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one,
      Matrix.empty_val'] <;>
    first
      | exact continuous_const
      | exact hcos
      | exact hsin
      | exact hcos.neg
      | exact hsin.neg

/-- The pointer component of the null-seam propagator is continuous. -/
theorem continuous_nullSeamEvolve_snd (r : ℝ) :
    Continuous fun y : CircleFibre × Pointer 2 => nullSeamUU r y.1 • y.2 := by
  have hQ : IsOpenQuotientMap
      (Prod.map (id : CircleFibre → CircleFibre)
        (Projectivization.mk' ℂ :
          {v : EuclideanSpace ℂ (Fin 3) // v ≠ 0} → Pointer 2)) :=
    IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'
  rw [hQ.isQuotientMap.continuous_iff]
  have hvec : Continuous fun z : CircleFibre × {v : EuclideanSpace ℂ (Fin 3) // v ≠ 0} =>
      (Matrix.toEuclideanLin (nullSeamMat (nullSeamAngle r z.1)) z.2.val
        : EuclideanSpace ℂ (Fin 3)) := by
    show Continuous fun z : CircleFibre × {v : EuclideanSpace ℂ (Fin 3) // v ≠ 0} =>
      (WithLp.toLp 2 ((nullSeamMat (nullSeamAngle r z.1)) *ᵥ (WithLp.ofLp z.2.val))
        : EuclideanSpace ℂ (Fin 3))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · refine continuous_matrix fun a b => ?_
      exact (continuous_nullSeamMat_entry r a b).comp continuous_fst
    · exact (PiLp.continuous_ofLp _ _).comp (continuous_subtype_val.comp continuous_snd)
  have hkey : ((fun y : CircleFibre × Pointer 2 => nullSeamUU r y.1 • y.2)
      ∘ (Prod.map id (Projectivization.mk' ℂ)))
      = fun z : CircleFibre × {v : EuclideanSpace ℂ (Fin 3) // v ≠ 0} =>
          Projectivization.mk' ℂ
            ⟨Matrix.toEuclideanLin (nullSeamMat (nullSeamAngle r z.1)) z.2.val,
              toEuclideanLin_unitary_apply_ne_zero (nullSeamUU r z.1) z.2.2⟩ := by
    funext z
    show nullSeamUU r z.1 • (Projectivization.mk' ℂ z.2) = _
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk]
    exact Projectivization.smul_mk_eq_mk_toEuclideanLin _ z.2.2
  rw [hkey]
  exact Projectivization.continuous_mk'.comp (hvec.subtype_mk _)

/-- ★★ **The null-seam propagator is continuous on the whole arena** — the property the
piecewise horn provably cannot have. -/
theorem continuous_nullSeamEvolve (r : ℝ) : Continuous (nullSeamEvolve r) :=
  continuous_fst.prodMk (continuous_nullSeamEvolve_snd r)

/-- The null-seam arena's invariant measure: Haar on the register, Fubini–Study on the
pointer. **Not** called Liouville: `S¹ × ℂℙ²` is odd-dimensional, hence not symplectic
(naming corrected 2026-08-03, fifth review). -/
noncomputable def nullSeamMeasure (q₀ : Pointer 2) : Measure (CircleFibre × Pointer 2) :=
  (volume : Measure CircleFibre).prod (fubiniStudyMeasure q₀)

instance (q₀ : Pointer 2) : IsProbabilityMeasure (nullSeamMeasure q₀) := by
  unfold nullSeamMeasure
  infer_instance

/-- ★★ **Measure invariance** — a skew product: register conserved, every register slice
acts by an FS-preserving unitary. -/
theorem nullSeamEvolve_measurePreserving (r : ℝ) (q₀ : Pointer 2) :
    MeasurePreserving (nullSeamEvolve r) (nullSeamMeasure q₀) (nullSeamMeasure q₀) := by
  unfold nullSeamEvolve nullSeamMeasure
  exact (MeasurePreserving.id (volume : Measure CircleFibre)).skew_product
    (continuous_nullSeamEvolve_snd r).measurable
    (Filter.Eventually.of_forall fun θ =>
      fubiniStudyMeasure_smul_invariant (nullSeamUU r θ) q₀)

/-! ### ★★ The third horn, bundled -/

/-- **The third horn**: continuous, measure-preserving dynamics whose records from the
calibrated ready state are exact and correct off a two-point seam, with exact Born
weights. The price is the Dirac calibration — see the module docstring's trilemma. -/
structure NullSeamClosure (r : ℝ) : Prop where
  /-- The propagator is continuous on the whole arena. -/
  continuity : Continuous (nullSeamEvolve r)
  /-- Measure invariance at every Fubini–Study base point. -/
  invariant : ∀ q₀ : Pointer 2,
    MeasurePreserving (nullSeamEvolve r) (nullSeamMeasure q₀) (nullSeamMeasure q₀)
  /-- Correct record in the open first cell — exactly. -/
  landing_left : ∀ θ, nullSeamSign r θ < 0 →
    (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 0
  /-- Correct record in the open second cell — exactly. -/
  landing_right : ∀ θ, 0 < nullSeamSign r θ →
    (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 1
  /-- The seam is null. -/
  seam_null : (volume : Measure CircleFibre) {θ | nullSeamSign r θ = 0} = 0
  /-- Exact Born, first outcome. -/
  born_left : (volume : Measure CircleFibre)
      {θ | (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 0}
    = ENNReal.ofReal r
  /-- Exact Born, second outcome. -/
  born_right : (volume : Measure CircleFibre)
      {θ | (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) 1}
    = ENNReal.ofReal (1 - r)

/-- ★★ **The third horn exists** — for every cell split `r ∈ (0, 1)`. -/
theorem nullSeamClosure (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : NullSeamClosure r where
  continuity := continuous_nullSeamEvolve r
  invariant := nullSeamEvolve_measurePreserving r
  landing_left := nullSeam_landing_neg r hr0 hr1
  landing_right := nullSeam_landing_pos r hr0 hr1
  seam_null := nullSeam_seam_null r hr0 hr1
  born_left := nullSeam_born_left r hr0 hr1
  born_right := nullSeam_born_right r hr0 hr1

end CSD.RecordLayer
