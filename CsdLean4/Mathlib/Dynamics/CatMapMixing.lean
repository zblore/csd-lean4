/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapWitness
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.PSeries

/-!
# Exponential decay of correlations for rectangles under Arnold's cat map

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #118(i); consumed by `SigmaLayer/FibreCellDecay.lean` and `Mathlib/Dynamics/CatMapStrongMixing.lean`.

`CatMapWitness.lean` proved that the cat map `(x, y) ↦ (2x + y, x + y)` on `T²` decorrelates the
single trigonometric observable `Re e^{2πix}`, with correlations exactly zero at every nonzero lag.
That is a witness. This file proves the statement a coarse-graining actually needs: **the indicator
of any rectangle `(a, b) × (c, d)` of arcs has correlations decaying like `4 · 2^{-⌊(n−2)/3⌋}`**,
a summable envelope, and the same for the pair correlation of two different rectangles.

## The argument

Four stages, each a section below.

1. **The frequency orbit grows.** `catZ (m, n) = (2m + n, m + n)` is the transpose action on
   character indices. The integer quadratic form `m² − mn − n²` is `catZ`-invariant and never
   vanishes on a nonzero integer vector (its discriminant `5` is not a square: a zero would make
   the golden ratio rational, `goldenRatio_irrational`), while the expanding linear form is
   multiplied by `φ²` at each step. Hence ★ `goldenRatio_pow_le_supNormZ_catZ_iterate`,
   `φ^{2n} ≤ φ³ ‖catZ^[n] v‖ ‖v‖`, and ★ `catCutoff_lt_supNormZ_catZ_iterate`: for `n ≥ 2` every
   nonzero frequency in the box of half-width `catCutoff n = 4^{⌊(n−2)/3⌋}` is carried strictly
   outside it. No eigenvector is ever written down; `φ² = φ + 1` does all the work.
2. **Arcs.** The indicator of an arc of the unit circle, read through the representative in
   `(0, 1]`, has Fourier coefficients `(e^{-2πinb} − e^{-2πina}) / (−2πin)`
   (`fourierCoeff_arcInd`), hence ★ `norm_fourierCoeff_arcInd_le`: `‖â(n)‖ ≤ 1/(π|n|)`.
3. **Truncation.** `trunc R u` keeps `|n| ≤ R`. Mathlib's Parseval (`tsum_sq_fourierCoeff`)
   identifies the `L²` truncation error with the tail of the series
   (`integral_normSq_sub_trunc`), Bessel bounds the truncation's energy
   (`integral_normSq_trunc_le`), and `∑_{|n|>R} n⁻² ≤ 4/R` (`tsum_tail_inv_sq_le`) give
   ★★ `integral_normSq_arcInd_sub_trunc_le`: the error of truncating an arc is at most `1/R`.
4. **Rectangles and the main term.** A rectangle is `u(x) v(y)`; its truncation is the product of
   the truncations, a trigonometric polynomial on the frequency box, with `L²` error at most `4/R`
   (`integral_normSq_rect_sub_trunc_le`, Fubini). Under `cat^[n]` the box is carried off itself,
   so by character orthogonality the integral of one truncated rectangle after `n` steps against
   another collapses to the product of the means, ★ `integral_rect_trunc_mul_rect_trunc`. Two
   Cauchy–Schwarz estimates (`normSq_integral_mul_le`) control the error terms, and
   ★★ `norm_integral_rect_iterate_mul_sub_le` is the bound at lags `n ≥ 2`; at lags `0, 1` the
   trivial bound `1` applies.

## The results

* ★★ `abs_integral_rectIndR_iterate_mul_sub_le_env`: for any two rectangles of arcs,
  `|∫ 1_A(cat^n p) 1_B(p) − |A||B|| ≤ catRectEnv n`, where `catRectEnv n = 1` for `n < 2` and
  `4 / 2^{⌊(n−2)/3⌋}` afterwards. This is the pair (mixing) statement.
* ★★★ `cat_hasCorrelationDecay_rectIndR`: the corpus's `HasCorrelationDecay` for the indicator
  of any rectangle of arcs, with ★ `summable_catRectEnv` (`catRectEnv n ≤ 13 (4/5)^n`).

## Honest scope

* **Rectangles of arcs only, with a rate.** Indicators of products of arcs, and by linearity their
  finite combinations. The statement for a general `L²` observable — convergence of the correlation
  with no rate — is `CatMapStrongMixing.lean` (★★★ `tendsto_integral_comp_cat_iterate_mul`, by the
  density of trigonometric polynomials and an `ε/3` argument); the rate is what this file adds,
  and it is for rectangles only.
* **The concrete matrix only**, as in `CatMapWitness.lean`: `[[2,1],[1,1]]`. The argument uses
  nothing about it beyond `φ² = φ + 1` and the invariant form, so a general hyperbolic element of
  `SL₂(ℤ)` would go the same way with its own quadratic form; not attempted.
* **The constants are not sharp.** The true rate is `φ^{-2n}` up to polynomial factors; the cutoff
  `4^{⌊(n−2)/3⌋}` was chosen to keep the envelope's square root a natural number, and the trivial
  bound covers lags `0` and `1`. Nothing downstream is sensitive to this.
* The arc indicator is read through the representative in `(0, 1]`, so its value at the two
  endpoints is a convention; everything here is insensitive to it.

References: Arnold–Avez, *Ergodic Problems of Classical Mechanics* (1968), §1.16; the Fourier
proof of mixing for hyperbolic toral automorphisms is standard (Katok–Hasselblatt, *Introduction to
the Modern Theory of Dynamical Systems*, §4.2). In-corpus: `Mathlib/Dynamics/CatMapWitness.lean`
(the map, the characters, the orthogonality), `Mathlib/Dynamics/CorrelationDecay.lean` (the
predicate and its consumers), `specs/BACKLOG.md` #118, `specs/residues.tsv` `R-019`.
-/

@[expose] public section

open MeasureTheory AddCircle Complex Real
open scoped goldenRatio

namespace MeasureTheory

/-! ### Stage 1: the frequency orbit of `catZ` grows geometrically

`catZ (m, n) = (2m + n, m + n)` is the transpose action of the cat map on character indices
(`chi_cat`). Its eigenvalues are `φ²` and `φ⁻²`, with `φ` the golden ratio, and the integer
quadratic form `m² − mn − n²` is invariant and never vanishes on a nonzero integer vector (its
discriminant `5` is not a square, i.e. `φ` is irrational). The expanding component of a nonzero
integer vector is therefore bounded below by `1 / (φ² ‖v‖)`, and the orbit grows like `φ^{2n}`. -/

/-- The sup norm of an integer vector, as a real number. -/
def supNormZ (v : ℤ × ℤ) : ℝ := max |(v.1 : ℝ)| |(v.2 : ℝ)|

lemma supNormZ_nonneg (v : ℤ × ℤ) : 0 ≤ supNormZ v := le_max_of_le_left (abs_nonneg _)

lemma abs_fst_le_supNormZ (v : ℤ × ℤ) : |(v.1 : ℝ)| ≤ supNormZ v := le_max_left _ _

lemma abs_snd_le_supNormZ (v : ℤ × ℤ) : |(v.2 : ℝ)| ≤ supNormZ v := le_max_right _ _

/-- The sup norm is bounded by `R` exactly when both coordinates lie in `[-R, R]`. -/
lemma supNormZ_le_iff (v : ℤ × ℤ) (R : ℕ) :
    supNormZ v ≤ R ↔ v.1 ∈ Finset.Icc (-(R : ℤ)) R ∧ v.2 ∈ Finset.Icc (-(R : ℤ)) R := by
  simp only [supNormZ, max_le_iff, Finset.mem_Icc, ← abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The linear form along the expanding eigendirection of `catZ`: scaled by `φ²`. -/
noncomputable def ellU (v : ℤ × ℤ) : ℝ := (v.1 : ℝ) + (φ - 1) * v.2

/-- The linear form along the contracting eigendirection of `catZ`: scaled by `φ⁻²`. -/
noncomputable def ellS (v : ℤ × ℤ) : ℝ := (v.1 : ℝ) - φ * v.2

lemma ellU_catZ (v : ℤ × ℤ) : ellU (catZ v) = φ ^ 2 * ellU v := by
  simp only [ellU, catZ, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  linear_combination (-((v.1 : ℝ) + φ * v.2)) * goldenRatio_sq

lemma ellU_catZ_iterate (v : ℤ × ℤ) (n : ℕ) :
    ellU (catZ^[n] v) = φ ^ (2 * n) * ellU v := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ellU_catZ, ih]
      ring

/-- The product of the two forms is the integer quadratic form `m² − mn − n²`. -/
lemma ellU_mul_ellS (v : ℤ × ℤ) :
    ellU v * ellS v = ((v.1 ^ 2 - v.1 * v.2 - v.2 ^ 2 : ℤ) : ℝ) := by
  simp only [ellU, ellS, Int.cast_sub, Int.cast_mul, Int.cast_pow]
  linear_combination (-((v.2 : ℝ) ^ 2)) * goldenRatio_sq

/-- The quadratic form has no nonzero integer zero: a zero would make `φ` rational. -/
lemma quadForm_ne_zero {v : ℤ × ℤ} (hv : v ≠ 0) : v.1 ^ 2 - v.1 * v.2 - v.2 ^ 2 ≠ 0 := by
  intro h
  have h' : ellU v * ellS v = 0 := by rw [ellU_mul_ellS, h]; simp
  have hirr := (irrational_iff_ne_rational φ).mp goldenRatio_irrational
  by_cases h2 : v.2 = 0
  · have h1 : v.1 = 0 := by
      rcases mul_eq_zero.mp h' with h0 | h0 <;> simp [ellU, ellS, h2] at h0 <;> exact_mod_cast h0
    exact hv (Prod.ext h1 h2)
  · have h2r : (v.2 : ℝ) ≠ 0 := by exact_mod_cast h2
    rcases mul_eq_zero.mp h' with h0 | h0
    · apply hirr (v.2 - v.1) v.2 h2
      simp only [ellU] at h0
      push_cast
      rw [eq_div_iff h2r]
      linear_combination h0
    · apply hirr v.1 v.2 h2
      simp only [ellS] at h0
      rw [eq_div_iff h2r]
      linear_combination (-1 : ℝ) * h0

/-- On a nonzero integer vector the invariant form has absolute value at least `1`. -/
lemma one_le_abs_ellU_mul_ellS {v : ℤ × ℤ} (hv : v ≠ 0) : 1 ≤ |ellU v * ellS v| := by
  rw [ellU_mul_ellS]
  exact_mod_cast Int.one_le_abs (quadForm_ne_zero hv)

lemma abs_ellS_le (v : ℤ × ℤ) : |ellS v| ≤ φ ^ 2 * supNormZ v := by
  have hφ : 0 < φ := goldenRatio_pos
  calc |ellS v| ≤ |(v.1 : ℝ)| + φ * |(v.2 : ℝ)| := by
        rw [ellS]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ supNormZ v + φ * supNormZ v := by
        have := abs_fst_le_supNormZ v
        have := abs_snd_le_supNormZ v
        nlinarith
    _ = φ ^ 2 * supNormZ v := by rw [goldenRatio_sq]; ring

lemma abs_ellU_le (v : ℤ × ℤ) : |ellU v| ≤ φ * supNormZ v := by
  have hφ : 0 ≤ φ - 1 := by linarith [one_lt_goldenRatio]
  calc |ellU v| ≤ |(v.1 : ℝ)| + (φ - 1) * |(v.2 : ℝ)| := by
        rw [ellU]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hφ]
    _ ≤ supNormZ v + (φ - 1) * supNormZ v := by
        have := abs_fst_le_supNormZ v
        have := abs_snd_le_supNormZ v
        nlinarith
    _ = φ * supNormZ v := by ring

/-- ★ **The frequency orbit grows geometrically.** For a nonzero integer vector `v`,
`φ^{2n} ≤ φ³ · ‖catZ^[n] v‖ · ‖v‖`: the orbit cannot stay small, because the invariant form is a
nonzero integer and the expanding component is multiplied by `φ²` at every step. -/
theorem goldenRatio_pow_le_supNormZ_catZ_iterate {v : ℤ × ℤ} (hv : v ≠ 0) (n : ℕ) :
    φ ^ (2 * n) ≤ φ ^ 3 * (supNormZ (catZ^[n] v) * supNormZ v) := by
  have hφ : 0 < φ := goldenRatio_pos
  have h1 : 1 ≤ |ellU v| * |ellS v| := by rw [← abs_mul]; exact one_le_abs_ellU_mul_ellS hv
  have h2 : |ellS v| ≤ φ ^ 2 * supNormZ v := abs_ellS_le v
  have h3 : |ellU (catZ^[n] v)| ≤ φ * supNormZ (catZ^[n] v) := abs_ellU_le _
  have h4 : |ellU (catZ^[n] v)| = φ ^ (2 * n) * |ellU v| := by
    rw [ellU_catZ_iterate, abs_mul, abs_of_pos (pow_pos hφ _)]
  have hU0 : 0 ≤ |ellU v| := abs_nonneg _
  have hp : 0 < φ ^ (2 * n) := pow_pos hφ _
  have hs : 0 ≤ φ ^ 2 * supNormZ v := mul_nonneg (pow_nonneg hφ.le _) (supNormZ_nonneg v)
  calc φ ^ (2 * n) = φ ^ (2 * n) * 1 := by ring
    _ ≤ φ ^ (2 * n) * (|ellU v| * |ellS v|) := by gcongr
    _ ≤ φ ^ (2 * n) * (|ellU v| * (φ ^ 2 * supNormZ v)) := by gcongr
    _ = |ellU (catZ^[n] v)| * (φ ^ 2 * supNormZ v) := by rw [h4]; ring
    _ ≤ (φ * supNormZ (catZ^[n] v)) * (φ ^ 2 * supNormZ v) := by gcongr
    _ = φ ^ 3 * (supNormZ (catZ^[n] v) * supNormZ v) := by ring

/-! ### The lag-dependent frequency cutoff -/

/-- `3/2 < φ`, since `2 < √5`. -/
lemma three_halves_lt_goldenRatio : (3 / 2 : ℝ) < φ := by
  have h : (2 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold goldenRatio
  linarith

/-- `φ⁶ = 8φ + 5`, so in particular `16 < φ⁶`. -/
lemma goldenRatio_pow_six : φ ^ 6 = 8 * φ + 5 := by
  linear_combination (φ ^ 4 + φ ^ 3 + 2 * φ ^ 2 + 3 * φ + 5) * goldenRatio_sq

lemma sixteen_le_goldenRatio_pow_six : (16 : ℝ) ≤ φ ^ 6 := by
  rw [goldenRatio_pow_six]; linarith [three_halves_lt_goldenRatio]

/-- The frequency cutoff at lag `n`: a perfect square `4^{⌊(n−2)/3⌋}`, chosen so that its square
stays below `φ^{2n-3}` (the orbit growth) for `n ≥ 2`, and so that its square root `2^{⌊(n−2)/3⌋}`
is a natural number. -/
def catCutoff (n : ℕ) : ℕ := 4 ^ ((n - 2) / 3)

lemma catCutoff_pos (n : ℕ) : 0 < catCutoff n := by unfold catCutoff; positivity

lemma catCutoff_eq_sq (n : ℕ) : catCutoff n = (2 ^ ((n - 2) / 3)) ^ 2 := by
  unfold catCutoff; rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- `R(n)² · φ³ < φ^{2n}` for `n ≥ 2`: the cutoff is small enough for the orbit growth to beat
it. -/
theorem catCutoff_sq_mul_lt {n : ℕ} (hn : 2 ≤ n) :
    ((catCutoff n : ℕ) : ℝ) ^ 2 * φ ^ 3 < φ ^ (2 * n) := by
  have hφ : 1 < φ := one_lt_goldenRatio
  have hφ0 : 0 < φ := goldenRatio_pos
  have h16 : ((catCutoff n : ℕ) : ℝ) ^ 2 = (16 : ℝ) ^ ((n - 2) / 3) := by
    unfold catCutoff; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h16]
  calc (16 : ℝ) ^ ((n - 2) / 3) * φ ^ 3 ≤ (φ ^ 6) ^ ((n - 2) / 3) * φ ^ 3 := by
        gcongr; exact sixteen_le_goldenRatio_pow_six
    _ = φ ^ (6 * ((n - 2) / 3) + 3) := by rw [← pow_mul, ← pow_add]
    _ ≤ φ ^ (2 * n - 1) := by
        apply pow_le_pow_right₀ hφ.le; omega
    _ < φ ^ (2 * n) := by
        apply pow_lt_pow_right₀ hφ; omega

/-- ★ **Separation.** For `n ≥ 2`, a nonzero frequency inside the cutoff box at lag `n` is
carried strictly outside it by `catZ^[n]`. This is the one fact the main-term computation uses. -/
theorem catCutoff_lt_supNormZ_catZ_iterate {n : ℕ} (hn : 2 ≤ n) {v : ℤ × ℤ} (hv : v ≠ 0)
    (hR : supNormZ v ≤ catCutoff n) : ((catCutoff n : ℕ) : ℝ) < supNormZ (catZ^[n] v) := by
  have h := goldenRatio_pow_le_supNormZ_catZ_iterate hv n
  have hc := catCutoff_sq_mul_lt hn
  have hRpos : (0 : ℝ) < catCutoff n := by exact_mod_cast catCutoff_pos n
  have hφ3 : 0 < φ ^ 3 := pow_pos goldenRatio_pos 3
  by_contra hcon
  replace hcon : supNormZ (catZ^[n] v) ≤ ((catCutoff n : ℕ) : ℝ) := not_lt.mp hcon
  have hv0 := supNormZ_nonneg v
  have hw0 := supNormZ_nonneg (catZ^[n] v)
  have hprod : supNormZ (catZ^[n] v) * supNormZ v
      ≤ ((catCutoff n : ℕ) : ℝ) * ((catCutoff n : ℕ) : ℝ) :=
    mul_le_mul hcon hR hv0 hRpos.le
  have : φ ^ (2 * n) ≤ φ ^ 3 * (((catCutoff n : ℕ) : ℝ) * ((catCutoff n : ℕ) : ℝ)) :=
    h.trans (by gcongr)
  nlinarith

/-! ### Stage 2: arcs of the circle and their Fourier coefficients

An arc is read through the representative in `(0, 1]`. Its Fourier coefficients are the usual
`(e^{-2πinb} − e^{-2πina}) / (−2πin)`, of modulus at most `1/(π|n|)`. -/

/-- The representative of a point of the unit circle in `(0, 1]`. -/
noncomputable def unitRep (x : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIoc (1 : ℝ) 0 x : ℝ)

lemma measurable_unitRep : Measurable unitRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

lemma unitRep_mem_Ioc (x : AddCircle (1 : ℝ)) : unitRep x ∈ Set.Ioc (0 : ℝ) 1 := by
  have h := (AddCircle.equivIoc (1 : ℝ) 0 x).2
  unfold unitRep
  simpa using h

/-- `haarAddCircle` on the unit circle is `volume`. -/
lemma haarAddCircle_one_eq_volume :
    (haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]; simp

/-- The indicator of the arc `{x | unitRep x ∈ (a, b)}`, as a complex observable. -/
noncomputable def arcInd (a b : ℝ) : AddCircle (1 : ℝ) → ℂ :=
  fun x => Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ)) (unitRep x)

lemma arcInd_eq_liftIoc (a b : ℝ) :
    arcInd a b = AddCircle.liftIoc 1 0 (Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ))) := rfl

lemma measurable_arcInd (a b : ℝ) : Measurable (arcInd a b) :=
  (measurable_const.indicator measurableSet_Ioo).comp measurable_unitRep

lemma arcInd_apply (a b : ℝ) (x : AddCircle (1 : ℝ)) :
    arcInd a b x = if unitRep x ∈ Set.Ioo a b then 1 else 0 :=
  Set.indicator_apply _ _ _

lemma norm_arcInd_le (a b : ℝ) (x : AddCircle (1 : ℝ)) : ‖arcInd a b x‖ ≤ 1 := by
  rw [arcInd_apply]; split_ifs <;> simp

/-- The zeroth coefficient of any integrable observable is its mean. -/
lemma fourierCoeff_zero_eq_integral (u : AddCircle (1 : ℝ) → ℂ) :
    fourierCoeff u 0 = ∫ x, u x ∂(volume : Measure (AddCircle (1 : ℝ))) := by
  simp [fourierCoeff, haarAddCircle_one_eq_volume]

/-- ★ The Fourier coefficients of an arc, as an interval integral. -/
theorem fourierCoeff_arcInd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (n : ℤ) :
    fourierCoeff (arcInd a b) n = ∫ x in a..b, Complex.exp (-(2 * π * I * n) * x) := by
  rw [arcInd_eq_liftIoc, fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, zero_add, sub_zero, Complex.ofReal_one, div_one, one_smul,
    smul_eq_mul, Int.cast_neg]
  have hsub : Set.Ioo a b ⊆ Set.Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨lt_of_le_of_lt ha hx.1, le_trans hx.2.le hb⟩
  have hpt : ∀ x : ℝ, Complex.exp (2 * π * I * (-(n : ℂ)) * x)
      * Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ)) x
      = Set.indicator (Set.Ioo a b) (fun x : ℝ => Complex.exp (-(2 * π * I * n) * x)) x := by
    intro x
    simp only [Set.indicator_apply]
    split_ifs <;> simp only [mul_one, mul_zero]
    congr 1; ring
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hab.le,
    integral_congr_ae (ae_of_all _ hpt), setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_right.mpr hsub, integral_Ioc_eq_integral_Ioo]

/-- The mean of an arc is its length. -/
theorem fourierCoeff_arcInd_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    fourierCoeff (arcInd a b) 0 = ((b - a : ℝ) : ℂ) := by
  rw [fourierCoeff_arcInd ha hab hb]
  simp

/-- ★ **The coefficient bound** `‖â(n)‖ ≤ 1 / (π |n|)` for `n ≠ 0`. -/
theorem norm_fourierCoeff_arcInd_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {n : ℤ} (hn : n ≠ 0) : ‖fourierCoeff (arcInd a b) n‖ ≤ 1 / (π * |(n : ℝ)|) := by
  rw [fourierCoeff_arcInd ha hab hb]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : (-(2 * π * I * n) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, hn']
  rw [integral_exp_mul_complex hc, norm_div]
  have h1 : ∀ t : ℝ, ‖Complex.exp (-(2 * π * I * n) * t)‖ = 1 := fun t => by
    have : (-(2 * π * I * n) : ℂ) * t = ((-(2 * π * n * t) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hnum : ‖Complex.exp (-(2 * π * I * n) * b) - Complex.exp (-(2 * π * I * n) * a)‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (-(2 * π * I * n) * b)‖ + ‖Complex.exp (-(2 * π * I * n) * a)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [h1, h1]; norm_num
  have hden : ‖(-(2 * π * I * n) : ℂ)‖ = 2 * π * |(n : ℝ)| := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast,
      Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hden]
  have hpos : 0 < 2 * π * |(n : ℝ)| := by
    have : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    positivity
  calc _ ≤ 2 / (2 * π * |(n : ℝ)|) := div_le_div_of_nonneg_right hnum hpos.le
    _ = 1 / (π * |(n : ℝ)|) := by field_simp

/-! ### Stage 3: truncation, Parseval, and the tail of an arc's Fourier series

`trunc R u` keeps the frequencies `|n| ≤ R`. Parseval (Mathlib's `tsum_sq_fourierCoeff`) turns the
`L²` error of the truncation into the tail `∑_{|n|>R} ‖û(n)‖²`, which for an arc is at most `1/R`
by the coefficient bound of Stage 2 and `∑_{|n|>R} n⁻² ≤ 4/R`. -/

/-- The frequency box `[-R, R]`. -/
abbrev freqBox (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) R

lemma zero_mem_freqBox (R : ℕ) : (0 : ℤ) ∈ freqBox R := by
  simp [freqBox]

/-- The truncation of `u` to the frequencies `|n| ≤ R`. -/
noncomputable def trunc (R : ℕ) (u : AddCircle (1 : ℝ) → ℂ) : AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑ n ∈ freqBox R, fourierCoeff u n * fourier n x

lemma norm_fourier_eq_one (n : ℤ) (x : AddCircle (1 : ℝ)) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply, Circle.norm_coe]

lemma integrable_of_bounded {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u) {C : ℝ}
    (hub : ∀ x, ‖u x‖ ≤ C) : Integrable u haarAddCircle :=
  Integrable.of_bound hu.aestronglyMeasurable C (ae_of_all _ hub)

lemma memLp_two_of_bounded {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u) {C : ℝ}
    (hub : ∀ x, ‖u x‖ ≤ C) : MemLp u 2 haarAddCircle :=
  MemLp.of_bound hu.aestronglyMeasurable C (ae_of_all _ hub)

lemma integrable_const_mul_fourier (c : ℂ) (n : ℤ) :
    Integrable (fun x : AddCircle (1 : ℝ) => c * fourier n x) haarAddCircle :=
  integrable_of_bounded (measurable_const.mul (fourier (T := (1 : ℝ)) n).continuous.measurable) (C := ‖c‖)
    (fun x => by rw [norm_mul, norm_fourier_eq_one, mul_one])

/-- A coefficient of an observable bounded by `1` is bounded by `1`. -/
lemma norm_fourierCoeff_le_one {u : AddCircle (1 : ℝ) → ℂ}
    (hub : ∀ x, ‖u x‖ ≤ 1) (n : ℤ) : ‖fourierCoeff u n‖ ≤ 1 := by
  unfold fourierCoeff
  refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun x => ?_)).trans ?_
  · rw [smul_eq_mul, norm_mul, norm_fourier_eq_one, one_mul]; exact hub x
  · simp

lemma continuous_trunc (R : ℕ) (u : AddCircle (1 : ℝ) → ℂ) : Continuous (trunc R u) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (fourier (T := (1 : ℝ)) n).continuous

lemma norm_trunc_le (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ}
    (hub : ∀ x, ‖u x‖ ≤ 1) (x : AddCircle (1 : ℝ)) :
    ‖trunc R u x‖ ≤ (freqBox R).card := by
  unfold trunc
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ freqBox R, ‖fourierCoeff u n * fourier n x‖
      ≤ ∑ _n ∈ freqBox R, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, norm_fourier_eq_one, mul_one]
        exact norm_fourierCoeff_le_one hub n
    _ = (freqBox R).card := by simp

lemma memLp_two_trunc (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ}
    (hub : ∀ x, ‖u x‖ ≤ 1) : MemLp (trunc R u) 2 haarAddCircle :=
  memLp_two_of_bounded (continuous_trunc R u).measurable (norm_trunc_le R hub)

/-- The coefficients of the truncation: those of `u` inside the box, `0` outside. -/
theorem fourierCoeff_trunc (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ} (m : ℤ) :
    fourierCoeff (trunc R u) m = if m ∈ freqBox R then fourierCoeff u m else 0 := by
  have h : trunc R u = ∑ n ∈ freqBox R, (fun x => fourierCoeff u n * fourier n x) := by
    ext x; simp [trunc, Finset.sum_apply]
  rw [h, fourierCoeff.sum _ _ (fun n _ => integrable_const_mul_fourier _ _), Finset.sum_apply]
  simp only [fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]

theorem fourierCoeff_sub_trunc (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u)
    (hub : ∀ x, ‖u x‖ ≤ 1) (m : ℤ) :
    fourierCoeff (u - trunc R u) m = if m ∈ freqBox R then 0 else fourierCoeff u m := by
  have hrw : u - trunc R u = u + (fun x => (-1 : ℂ) * trunc R u x) := by
    ext x; simp [sub_eq_add_neg]
  have hadd := congrFun (fourierCoeff.add (integrable_of_bounded hu hub)
    (integrable_of_bounded ((continuous_trunc R u).measurable.const_mul (-1 : ℂ))
      (C := (freqBox R).card) (fun x => by
        rw [norm_mul, norm_neg, norm_one, one_mul]; exact norm_trunc_le R hub x))) m
  rw [hrw, hadd, Pi.add_apply, fourierCoeff.const_mul, fourierCoeff_trunc R m]
  split_ifs <;> ring

/-- **Parseval**, for a bounded measurable observable: `∫ ‖g‖² = ∑ ‖ĝ(n)‖²`. -/
theorem integral_normSq_eq_tsum_of_memLp {g : AddCircle (1 : ℝ) → ℂ}
    (hg : MemLp g 2 haarAddCircle) :
    ∫ x, ‖g x‖ ^ 2 ∂haarAddCircle = ∑' n : ℤ, ‖fourierCoeff g n‖ ^ 2 := by
  have h := tsum_sq_fourierCoeff (hg.toLp g)
  rw [fourierCoeff_congr_ae hg.coeFn_toLp] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem summable_sq_fourierCoeff_of_memLp {g : AddCircle (1 : ℝ) → ℂ}
    (hg : MemLp g 2 haarAddCircle) : Summable (fun n : ℤ => ‖fourierCoeff g n‖ ^ 2) := by
  have h := (hasSum_sq_fourierCoeff (hg.toLp g)).summable
  rwa [fourierCoeff_congr_ae hg.coeFn_toLp] at h

/-- The `L²` error of the truncation is the tail of the series. -/
theorem integral_normSq_sub_trunc (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u)
    (hub : ∀ x, ‖u x‖ ≤ 1) :
    ∫ x, ‖u x - trunc R u x‖ ^ 2 ∂haarAddCircle
      = ∑' n : ℤ, ‖if n ∈ freqBox R then (0 : ℂ) else fourierCoeff u n‖ ^ 2 := by
  have hmem : MemLp (u - trunc R u) 2 haarAddCircle :=
    (memLp_two_of_bounded hu hub).sub (memLp_two_trunc R hub)
  have h := integral_normSq_eq_tsum_of_memLp hmem
  simp only [Pi.sub_apply] at h
  rw [h]
  congr 1
  ext n
  rw [fourierCoeff_sub_trunc R hu hub]

/-- **Bessel**: the truncation has no more energy than the observable. -/
theorem integral_normSq_trunc_le (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u)
    (hub : ∀ x, ‖u x‖ ≤ 1) :
    ∫ x, ‖trunc R u x‖ ^ 2 ∂haarAddCircle ≤ ∫ x, ‖u x‖ ^ 2 ∂haarAddCircle := by
  rw [integral_normSq_eq_tsum_of_memLp (memLp_two_trunc R hub),
    integral_normSq_eq_tsum_of_memLp (memLp_two_of_bounded hu hub)]
  have hfin : ∀ n ∉ freqBox R, ‖fourierCoeff (trunc R u) n‖ ^ 2 = 0 := fun n hn => by
    rw [fourierCoeff_trunc R n, ite_eq_right hn]; simp
  rw [tsum_eq_sum hfin]
  calc ∑ n ∈ freqBox R, ‖fourierCoeff (trunc R u) n‖ ^ 2
      = ∑ n ∈ freqBox R, ‖fourierCoeff u n‖ ^ 2 :=
        Finset.sum_congr rfl fun n hn => by rw [fourierCoeff_trunc R n, ite_eq_left hn]
    _ ≤ ∑' n : ℤ, ‖fourierCoeff u n‖ ^ 2 :=
        Summable.sum_le_tsum _ (fun n _ => by positivity)
          (summable_sq_fourierCoeff_of_memLp (memLp_two_of_bounded hu hub))

/-! #### The tail of `∑ n⁻²` over `|n| > R` -/

/-- The finite tail bound: a finite set of integers outside the box contributes at most `4/R`. -/
lemma sum_tail_inv_sq_le (R : ℕ) (hR : 1 ≤ R) (s : Finset ℤ) :
    ∑ n ∈ s, (if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2) ≤ 4 / R := by
  classical
  set M : ℕ := s.sup Int.natAbs + 1 with hM
  set t : Finset ℤ := s.filter (fun n => n ∉ freqBox R) with ht
  have h1 : ∑ n ∈ s, (if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2)
      = ∑ n ∈ t, 1 / (n : ℝ) ^ 2 := by
    rw [ht, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> rfl
  have hsub : t ⊆ (Finset.Ioo R M).biUnion (fun k : ℕ => {(k : ℤ), -(k : ℤ)}) := by
    intro n hn
    rw [ht, Finset.mem_filter] at hn
    obtain ⟨hns, hnb⟩ := hn
    rw [Finset.mem_biUnion]
    refine ⟨n.natAbs, ?_, ?_⟩
    · rw [Finset.mem_Ioo]
      constructor
      · by_contra hle
        apply hnb
        simp only [freqBox, Finset.mem_Icc]
        omega
      · have : n.natAbs ≤ s.sup Int.natAbs := Finset.le_sup hns
        omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  have hdisj : ((Finset.Ioo R M : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k : ℕ => ({(k : ℤ), -(k : ℤ)} : Finset ℤ)) := by
    intro k hk k' hk' hkk'
    simp only [Finset.coe_Ioo, Set.mem_Ioo] at hk hk'
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    omega
  have hnonneg : ∀ n : ℤ, 0 ≤ 1 / (n : ℝ) ^ 2 := fun n => by positivity
  calc ∑ n ∈ s, (if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2)
      = ∑ n ∈ t, 1 / (n : ℝ) ^ 2 := h1
    _ ≤ ∑ n ∈ (Finset.Ioo R M).biUnion (fun k : ℕ => {(k : ℤ), -(k : ℤ)}), 1 / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnonneg n)
    _ = ∑ k ∈ Finset.Ioo R M, ∑ n ∈ ({(k : ℤ), -(k : ℤ)} : Finset ℤ), 1 / (n : ℝ) ^ 2 :=
        Finset.sum_biUnion hdisj
    _ = ∑ k ∈ Finset.Ioo R M, 2 * ((k : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Ioo] at hk
        have hk0 : (k : ℤ) ≠ -(k : ℤ) := by omega
        rw [Finset.sum_pair hk0]
        push_cast
        ring
    _ = 2 * ∑ k ∈ Finset.Ioo R M, ((k : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 / ((R : ℝ) + 1)) := by gcongr; exact sum_Ioo_inv_sq_le R M
    _ ≤ 4 / R := by
        have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
        rw [show (2 : ℝ) * (2 / ((R : ℝ) + 1)) = 4 / ((R : ℝ) + 1) by ring]
        exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma summable_tail_inv_sq (R : ℕ) :
    Summable (fun n : ℤ => if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_one_div_int_pow.mpr one_lt_two)
  · split_ifs <;> positivity
  · split_ifs
    · positivity
    · exact le_rfl

/-- ★ `∑_{|n|>R} n⁻² ≤ 4/R`. -/
theorem tsum_tail_inv_sq_le (R : ℕ) (hR : 1 ≤ R) :
    ∑' n : ℤ, (if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2) ≤ 4 / R :=
  (summable_tail_inv_sq R).tsum_le_of_sum_le (sum_tail_inv_sq_le R hR)

/-- ★★ **The `L²` error of truncating an arc is at most `1/R`.** -/
theorem integral_normSq_arcInd_sub_trunc_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (R : ℕ) (hR : 1 ≤ R) :
    ∫ x, ‖arcInd a b x - trunc R (arcInd a b) x‖ ^ 2 ∂haarAddCircle ≤ 1 / R := by
  rw [integral_normSq_sub_trunc R (measurable_arcInd a b) (norm_arcInd_le a b)]
  have hsum1 : Summable (fun n : ℤ =>
      ‖if n ∈ freqBox R then (0 : ℂ) else fourierCoeff (arcInd a b) n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_sq_fourierCoeff_of_memLp
        (memLp_two_of_bounded (measurable_arcInd a b) (norm_arcInd_le a b)))
    split_ifs <;> simp
  have hπ : (0 : ℝ) < π := Real.pi_pos
  calc ∑' n : ℤ, ‖if n ∈ freqBox R then (0 : ℂ) else fourierCoeff (arcInd a b) n‖ ^ 2
      ≤ ∑' n : ℤ, (1 / π ^ 2) * (if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsum1 ((summable_tail_inv_sq R).mul_left _)
        split_ifs with hn
        · simp
        · have hn0 : n ≠ 0 := fun h => hn (h ▸ zero_mem_freqBox R)
          have hcoef := norm_fourierCoeff_arcInd_le ha hab hb hn0
          have hn0r : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn0)
          calc ‖fourierCoeff (arcInd a b) n‖ ^ 2 ≤ (1 / (π * |(n : ℝ)|)) ^ 2 := by
                gcongr
            _ = (1 / π ^ 2) * (1 / (n : ℝ) ^ 2) := by
                rw [div_pow, mul_pow, sq_abs]; ring
    _ = (1 / π ^ 2) * ∑' n : ℤ, (if n ∈ freqBox R then (0 : ℝ) else 1 / (n : ℝ) ^ 2) :=
        tsum_mul_left
    _ ≤ (1 / π ^ 2) * (4 / R) := by gcongr; exact tsum_tail_inv_sq_le R hR
    _ ≤ 1 / R := by
        have h4 : (4 : ℝ) ≤ π ^ 2 := by nlinarith [Real.two_le_pi]
        have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
        rw [show (1 / π ^ 2) * (4 / (R : ℝ)) = (4 / π ^ 2) / R by ring]
        refine div_le_div_of_nonneg_right ?_ hRpos.le
        rw [div_le_one (by positivity)]
        exact h4

/-! ### Stage 4: rectangles on the torus, and the main term

A rectangle observable is a product `u(x) v(y)` of two circle observables. Its truncation at the
cutoff `R` is the product of the two truncations, a trigonometric polynomial supported on the
frequency box; under `cat^[n]` that box is carried off itself (Stage 1), so the integral of the
truncated product against another truncated rectangle collapses to the product of the means.
The truncation errors are controlled by Stage 3 through Cauchy–Schwarz. -/

/-- Bounded measurable observables on the circle, the class everything below lives in. -/
structure BddC (u : AddCircle (1 : ℝ) → ℂ) : Prop where
  measurable : Measurable u
  bound : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C

/-- Bounded measurable observables on the torus. -/
structure BddT (F : Torus2 → ℂ) : Prop where
  measurable : Measurable F
  bound : ∃ C : ℝ, ∀ p, ‖F p‖ ≤ C

lemma BddC.arcInd (a b : ℝ) : BddC (arcInd a b) :=
  ⟨measurable_arcInd a b, 1, norm_arcInd_le a b⟩

lemma BddC.trunc (R : ℕ) {u : AddCircle (1 : ℝ) → ℂ} (hub : ∀ x, ‖u x‖ ≤ 1) : BddC (trunc R u) :=
  ⟨(continuous_trunc R u).measurable, _, norm_trunc_le R hub⟩

lemma BddC.sub {u v : AddCircle (1 : ℝ) → ℂ} (hu : BddC u) (hv : BddC v) : BddC (u - v) := by
  obtain ⟨C, hC⟩ := hu.bound
  obtain ⟨D, hD⟩ := hv.bound
  exact ⟨hu.measurable.sub hv.measurable, C + D, fun x =>
    (norm_sub_le _ _).trans (add_le_add (hC x) (hD x))⟩

lemma BddC.integrable {u : AddCircle (1 : ℝ) → ℂ} (hu : BddC u) :
    Integrable u (volume : Measure (AddCircle (1 : ℝ))) := by
  obtain ⟨C, hC⟩ := hu.bound
  exact Integrable.of_bound hu.measurable.aestronglyMeasurable C (ae_of_all _ hC)

lemma BddC.integrable_normSq {u : AddCircle (1 : ℝ) → ℂ} (hu : BddC u) :
    Integrable (fun x => ‖u x‖ ^ 2) (volume : Measure (AddCircle (1 : ℝ))) := by
  obtain ⟨C, hC⟩ := hu.bound
  refine Integrable.of_bound (hu.measurable.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2

/-- The energy of an observable bounded by `1` is at most `1`. -/
lemma BddC.integral_normSq_le_one {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u)
    (hub : ∀ x, ‖u x‖ ≤ 1) :
    ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))) ≤ 1 := by
  have hb : BddC u := ⟨hu, 1, hub⟩
  calc ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ)))
      ≤ ∫ _x, (1 : ℝ) ∂(volume : Measure (AddCircle (1 : ℝ))) :=
        integral_mono hb.integrable_normSq (integrable_const 1)
          (fun x => pow_le_one₀ (norm_nonneg _) (hub x))
    _ = 1 := by simp

/-- A rectangle observable: the product of two circle observables. -/
def rect (u v : AddCircle (1 : ℝ) → ℂ) : Torus2 → ℂ := fun p => u p.1 * v p.2

lemma BddT.rect {u v : AddCircle (1 : ℝ) → ℂ} (hu : BddC u) (hv : BddC v) : BddT (rect u v) := by
  obtain ⟨C, hC⟩ := hu.bound
  obtain ⟨D, hD⟩ := hv.bound
  refine ⟨(hu.measurable.comp measurable_fst).mul (hv.measurable.comp measurable_snd), C * D,
    fun p => ?_⟩
  show ‖u p.1 * v p.2‖ ≤ C * D
  rw [norm_mul]
  exact mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC p.1))

lemma BddT.sub {F G : Torus2 → ℂ} (hF : BddT F) (hG : BddT G) : BddT (F - G) := by
  obtain ⟨C, hC⟩ := hF.bound
  obtain ⟨D, hD⟩ := hG.bound
  exact ⟨hF.measurable.sub hG.measurable, C + D, fun p =>
    (norm_sub_le _ _).trans (add_le_add (hC p) (hD p))⟩

lemma BddT.mul {F G : Torus2 → ℂ} (hF : BddT F) (hG : BddT G) : BddT (fun p => F p * G p) := by
  obtain ⟨C, hC⟩ := hF.bound
  obtain ⟨D, hD⟩ := hG.bound
  exact ⟨hF.measurable.mul hG.measurable, C * D, fun p => by
    rw [norm_mul]
    exact mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC p))⟩

lemma BddT.comp_cat_iterate {F : Torus2 → ℂ} (hF : BddT F) (n : ℕ) :
    BddT (fun p => F (cat^[n] p)) := by
  obtain ⟨C, hC⟩ := hF.bound
  exact ⟨hF.measurable.comp (measurable_cat.iterate n), C, fun p => hC _⟩

lemma BddT.integrable {F : Torus2 → ℂ} (hF : BddT F) : Integrable F (volume : Measure Torus2) := by
  obtain ⟨C, hC⟩ := hF.bound
  exact Integrable.of_bound hF.measurable.aestronglyMeasurable C (ae_of_all _ hC)

lemma BddT.integrable_normSq {F : Torus2 → ℂ} (hF : BddT F) :
    Integrable (fun p => ‖F p‖ ^ 2) (volume : Measure Torus2) := by
  obtain ⟨C, hC⟩ := hF.bound
  refine Integrable.of_bound (hF.measurable.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC p) 2

lemma BddT.memLp_two {F : Torus2 → ℂ} (hF : BddT F) : MemLp F 2 (volume : Measure Torus2) := by
  obtain ⟨C, hC⟩ := hF.bound
  exact MemLp.of_bound hF.measurable.aestronglyMeasurable C (ae_of_all _ hC)

/-- The mean of a rectangle is the product of the means (Fubini). -/
lemma integral_rect (u v : AddCircle (1 : ℝ) → ℂ) :
    ∫ p, rect u v p ∂(volume : Measure Torus2)
      = (∫ x, u x ∂(volume : Measure (AddCircle (1 : ℝ))))
        * ∫ y, v y ∂(volume : Measure (AddCircle (1 : ℝ))) := by
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul u v

/-- The energy of a rectangle is the product of the energies. -/
lemma integral_normSq_rect (u v : AddCircle (1 : ℝ) → ℂ) :
    ∫ p, ‖rect u v p‖ ^ 2 ∂(volume : Measure Torus2)
      = (∫ x, ‖u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))))
        * ∫ y, ‖v y‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))) := by
  have h : ∀ p : Torus2, ‖rect u v p‖ ^ 2 = ‖u p.1‖ ^ 2 * ‖v p.2‖ ^ 2 := fun p => by
    rw [rect, norm_mul, mul_pow]
  simp_rw [h]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => ‖u x‖ ^ 2) (fun y => ‖v y‖ ^ 2)

/-- Composition with the cat map preserves integrals of real observables. -/
lemma integral_comp_cat_iterate (g : Torus2 → ℝ) (hg : Measurable g) (n : ℕ) :
    ∫ p, g (cat^[n] p) ∂(volume : Measure Torus2) = ∫ p, g p ∂(volume : Measure Torus2) :=
  integral_iterate_of_measurePreserving measurePreserving_cat hg.aestronglyMeasurable n

/-- **Cauchy–Schwarz** on the torus, in squared form, for two `L²` observables. -/
theorem normSq_integral_mul_le {F G : Torus2 → ℂ} (hF : MemLp F 2 (volume : Measure Torus2))
    (hG : MemLp G 2 (volume : Measure Torus2)) :
    ‖∫ p, F p * G p ∂(volume : Measure Torus2)‖ ^ 2
      ≤ (∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2))
        * ∫ p, ‖G p‖ ^ 2 ∂(volume : Measure Torus2) := by
  have h1 : ‖∫ p, F p * G p ∂(volume : Measure Torus2)‖
      ≤ ∫ p, ‖F p‖ * ‖G p‖ ∂(volume : Measure Torus2) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (ae_of_all _ fun p => norm_mul _ _)
  have hF2 : MemLp (fun p => ‖F p‖) (ENNReal.ofReal 2) (volume : Measure Torus2) := by
    rw [ENNReal.ofReal_ofNat]; exact hF.norm
  have hG2 : MemLp (fun p => ‖G p‖) (ENNReal.ofReal 2) (volume : Measure Torus2) := by
    rw [ENNReal.ofReal_ofNat]; exact hG.norm
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun p => norm_nonneg (F p)) (ae_of_all _ fun p => norm_nonneg (G p)) hF2 hG2
  simp only [Real.rpow_two] at h2
  have hA : 0 ≤ ∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2) := integral_nonneg fun p => by positivity
  have hB : 0 ≤ ∫ p, ‖G p‖ ^ 2 ∂(volume : Measure Torus2) := integral_nonneg fun p => by positivity
  have hI : 0 ≤ ∫ p, ‖F p‖ * ‖G p‖ ∂(volume : Measure Torus2) :=
    integral_nonneg fun p => by positivity
  calc ‖∫ p, F p * G p ∂(volume : Measure Torus2)‖ ^ 2
      ≤ (∫ p, ‖F p‖ * ‖G p‖ ∂(volume : Measure Torus2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ((∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2)) ^ (1 / (2 : ℝ))
          * (∫ p, ‖G p‖ ^ 2 ∂(volume : Measure Torus2)) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hI h2 2
    _ = (∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2)) * ∫ p, ‖G p‖ ^ 2 ∂(volume : Measure Torus2) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-! #### The truncation error of a rectangle of arcs -/

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
lemma normSq_add_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  calc ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- ★ **The `L²` error of truncating a rectangle of arcs is at most `4/R`.** -/
theorem integral_normSq_rect_sub_trunc_le {a b c d : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1) (R : ℕ) (hR : 1 ≤ R) :
    ∫ p, ‖rect (arcInd a b) (arcInd c d) p
        - rect (trunc R (arcInd a b)) (trunc R (arcInd c d)) p‖ ^ 2 ∂(volume : Measure Torus2)
      ≤ 4 / R := by
  set u := arcInd a b with hu
  set v := arcInd c d with hv
  have hub : ∀ x, ‖u x‖ ≤ 1 := norm_arcInd_le a b
  have hvb : ∀ x, ‖v x‖ ≤ 1 := norm_arcInd_le c d
  have hum : Measurable u := measurable_arcInd a b
  have hvm : Measurable v := measurable_arcInd c d
  have hBu : BddC u := BddC.arcInd a b
  have hBv : BddC v := BddC.arcInd c d
  have hBSu : BddC (trunc R u) := BddC.trunc R hub
  have hBSv : BddC (trunc R v) := BddC.trunc R hvb
  -- the pointwise decomposition
  have hpt : ∀ p : Torus2, rect u v p - rect (trunc R u) (trunc R v) p
      = rect (u - trunc R u) v p + rect (trunc R u) (v - trunc R v) p := fun p => by
    simp only [rect, Pi.sub_apply]; ring
  have hbound : ∀ p : Torus2, ‖rect u v p - rect (trunc R u) (trunc R v) p‖ ^ 2
      ≤ 2 * ‖rect (u - trunc R u) v p‖ ^ 2 + 2 * ‖rect (trunc R u) (v - trunc R v) p‖ ^ 2 :=
    fun p => by rw [hpt p]; exact normSq_add_le _ _
  have hI1 : Integrable (fun p => ‖rect u v p - rect (trunc R u) (trunc R v) p‖ ^ 2)
      (volume : Measure Torus2) :=
    ((BddT.rect hBu hBv).sub (BddT.rect hBSu hBSv)).integrable_normSq
  have hI2 : Integrable (fun p => ‖rect (u - trunc R u) v p‖ ^ 2) (volume : Measure Torus2) :=
    (BddT.rect (hBu.sub hBSu) hBv).integrable_normSq
  have hI3 : Integrable (fun p => ‖rect (trunc R u) (v - trunc R v) p‖ ^ 2)
      (volume : Measure Torus2) :=
    (BddT.rect hBSu (hBv.sub hBSv)).integrable_normSq
  -- the four one-dimensional ingredients, transported from `haarAddCircle` to `volume`
  have e1 := integral_normSq_arcInd_sub_trunc_le ha hab hb R hR
  have e2 := integral_normSq_arcInd_sub_trunc_le hc hcd hd R hR
  have e3 := integral_normSq_trunc_le R hum hub
  rw [haarAddCircle_one_eq_volume] at e1 e2 e3
  have e4 := BddC.integral_normSq_le_one hum hub
  have e5 := BddC.integral_normSq_le_one hvm hvb
  have n1 : 0 ≤ ∫ x, ‖u x - trunc R u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))) :=
    integral_nonneg fun x => by positivity
  have n2 : 0 ≤ ∫ x, ‖v x - trunc R v x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))) :=
    integral_nonneg fun x => by positivity
  have n3 : 0 ≤ ∫ x, ‖trunc R u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))) :=
    integral_nonneg fun x => by positivity
  have n5 : 0 ≤ ∫ x, ‖v x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))) :=
    integral_nonneg fun x => by positivity
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  calc ∫ p, ‖rect u v p - rect (trunc R u) (trunc R v) p‖ ^ 2 ∂(volume : Measure Torus2)
      ≤ ∫ p, (2 * ‖rect (u - trunc R u) v p‖ ^ 2
          + 2 * ‖rect (trunc R u) (v - trunc R v) p‖ ^ 2) ∂(volume : Measure Torus2) :=
        integral_mono hI1 ((hI2.const_mul 2).add (hI3.const_mul 2)) hbound
    _ = 2 * ∫ p, ‖rect (u - trunc R u) v p‖ ^ 2 ∂(volume : Measure Torus2)
          + 2 * ∫ p, ‖rect (trunc R u) (v - trunc R v) p‖ ^ 2 ∂(volume : Measure Torus2) := by
        rw [integral_add (hI2.const_mul 2) (hI3.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ = 2 * ((∫ x, ‖u x - trunc R u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))))
            * ∫ y, ‖v y‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))))
          + 2 * ((∫ x, ‖trunc R u x‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ))))
            * ∫ y, ‖v y - trunc R v y‖ ^ 2 ∂(volume : Measure (AddCircle (1 : ℝ)))) := by
        rw [integral_normSq_rect, integral_normSq_rect]
        rfl
    _ ≤ 2 * ((1 / R) * 1) + 2 * (1 * (1 / R)) := by
        gcongr
        · exact e3.trans e4
    _ = 4 / R := by ring

/-! #### The main term -/

lemma BddT.chi (a : ℤ × ℤ) : BddT (chi a) :=
  ⟨(continuous_chi a).measurable, 1, fun p => (norm_chi a p).le⟩

lemma BddT.const_mul (c : ℂ) {F : Torus2 → ℂ} (hF : BddT F) : BddT (fun p => c * F p) := by
  obtain ⟨C, hC⟩ := hF.bound
  exact ⟨hF.measurable.const_mul c, ‖c‖ * C, fun p => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg c)⟩

/-- A truncated rectangle is a trigonometric polynomial on the product frequency box. -/
lemma rect_trunc_eq_sum (R : ℕ) (u v : AddCircle (1 : ℝ) → ℂ) (p : Torus2) :
    rect (trunc R u) (trunc R v) p
      = ∑ k ∈ freqBox R ×ˢ freqBox R, (fourierCoeff u k.1 * fourierCoeff v k.2) * chi k p := by
  rw [Finset.sum_product]
  simp only [rect, trunc, Finset.sum_mul_sum, chi]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma rect_trunc_comp_cat_iterate (R : ℕ) (u v : AddCircle (1 : ℝ) → ℂ) (n : ℕ) (p : Torus2) :
    rect (trunc R u) (trunc R v) (cat^[n] p)
      = ∑ k ∈ freqBox R ×ˢ freqBox R,
          (fourierCoeff u k.1 * fourierCoeff v k.2) * chi (catZ^[n] k) p := by
  rw [rect_trunc_eq_sum]
  simp only [chi_cat_iterate]

lemma catZ_zero : catZ 0 = 0 := by simp [catZ]

lemma catZ_iterate_zero (n : ℕ) : catZ^[n] 0 = 0 :=
  Function.iterate_fixed catZ_zero n

lemma supNormZ_neg (v : ℤ × ℤ) : supNormZ (-v) = supNormZ v := by
  simp [supNormZ, abs_neg]

lemma zero_mem_freqBox_prod (R : ℕ) : (0 : ℤ × ℤ) ∈ freqBox R ×ˢ freqBox R :=
  Finset.mem_product.mpr ⟨by simp [freqBox], by simp [freqBox]⟩

/-- The integral of a product of two characters is `1` when the indices cancel and `0`
otherwise. -/
lemma integral_chi_mul_chi (a b : ℤ × ℤ) :
    ∫ p, chi a p * chi b p ∂(volume : Measure Torus2) = if a + b = 0 then 1 else 0 := by
  simp_rw [← chi_index_add]
  split_ifs with h
  · rw [h]; simp [chi_zero]
  · exact integral_chi_eq_zero h

/-- ★ **The main term.** For `n ≥ 2` the truncated rectangles at the cutoff `catCutoff n` have,
after `n` steps of the cat map, no frequency in common except `0`, so the integral of their product
is the product of their means. -/
theorem integral_rect_trunc_mul_rect_trunc {n : ℕ} (hn : 2 ≤ n)
    (u v u' v' : AddCircle (1 : ℝ) → ℂ) :
    ∫ p, rect (trunc (catCutoff n) u) (trunc (catCutoff n) v) (cat^[n] p)
        * rect (trunc (catCutoff n) u') (trunc (catCutoff n) v') p ∂(volume : Measure Torus2)
      = (fourierCoeff u 0 * fourierCoeff v 0) * (fourierCoeff u' 0 * fourierCoeff v' 0) := by
  set R := catCutoff n with hR
  set B := freqBox R ×ˢ freqBox R with hB
  set c : ℤ × ℤ → ℂ := fun k => fourierCoeff u k.1 * fourierCoeff v k.2 with hc
  set c' : ℤ × ℤ → ℂ := fun k => fourierCoeff u' k.1 * fourierCoeff v' k.2 with hc'
  have hT : ∀ p, rect (trunc R u) (trunc R v) (cat^[n] p)
      = ∑ k ∈ B, c k * chi (catZ^[n] k) p := fun p => rect_trunc_comp_cat_iterate R u v n p
  have hT' : ∀ p, rect (trunc R u') (trunc R v') p = ∑ j ∈ B, c' j * chi j p :=
    fun p => rect_trunc_eq_sum R u' v' p
  simp_rw [hT, hT', Finset.sum_mul_sum]
  have hint : ∀ (k j : ℤ × ℤ),
      Integrable (fun p => c k * chi (catZ^[n] k) p * (c' j * chi j p)) (volume : Measure Torus2) :=
    fun k j => (((BddT.chi _).const_mul (c k)).mul ((BddT.chi j).const_mul (c' j))).integrable
  have hterm : ∀ k j : ℤ × ℤ,
      ∫ p, c k * chi (catZ^[n] k) p * (c' j * chi j p) ∂(volume : Measure Torus2)
        = (c k * c' j) * (if catZ^[n] k + j = 0 then 1 else 0) := by
    intro k j
    rw [← integral_chi_mul_chi, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun p => by ring)
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => hint k j))]
  have hinner : ∀ k ∈ B, ∫ p, ∑ j ∈ B, c k * chi (catZ^[n] k) p * (c' j * chi j p)
      ∂(volume : Measure Torus2) = ∑ j ∈ B, (c k * c' j) * (if catZ^[n] k + j = 0 then 1 else 0) :=
    fun k _ => by
      rw [integral_finsetSum _ (fun j _ => hint k j)]
      exact Finset.sum_congr rfl fun j _ => hterm k j
  rw [Finset.sum_congr rfl hinner]
  have h00 : (0 : ℤ × ℤ) ∈ B := zero_mem_freqBox_prod R
  rw [Finset.sum_eq_single_of_mem (0 : ℤ × ℤ) h00 (fun k hk hk0 => ?_)]
  · rw [Finset.sum_eq_single_of_mem (0 : ℤ × ℤ) h00 (fun j hj hj0 => ?_)]
    · rw [catZ_iterate_zero, add_zero, ite_eq_left rfl, mul_one]
      rfl
    · rw [catZ_iterate_zero, zero_add, ite_eq_right hj0, mul_zero]
  · refine Finset.sum_eq_zero fun j hj => ?_
    have hne : catZ^[n] k + j ≠ 0 := by
      intro h
      have hk' : supNormZ k ≤ R := (supNormZ_le_iff k R).mpr (Finset.mem_product.mp hk)
      have hj' : supNormZ j ≤ R := (supNormZ_le_iff j R).mpr (Finset.mem_product.mp hj)
      have hsep := catCutoff_lt_supNormZ_catZ_iterate hn hk0 hk'
      rw [eq_neg_of_add_eq_zero_left h, supNormZ_neg] at hsep
      linarith
    rw [ite_eq_right hne, mul_zero]

/-! ### Stage 5: the correlation bound, and `HasCorrelationDecay` for rectangles

Write `f = T + D` with `T` the truncation at the lag-dependent cutoff and `D` the error. Then
`∫ f∘catⁿ · f' = ∫ T∘catⁿ · T' + ∫ T∘catⁿ · D' + ∫ D∘catⁿ · f'`: the first term is the product of
the means (Stage 4), and the other two are at most `2 / 2^{⌊(n−2)/3⌋}` each by Cauchy–Schwarz and
the truncation error `4 / R`. -/

/-- `a ≤ 1`, `0 ≤ b ≤ 1` give `a * b ≤ 1` (the deprecated `mul_le_one_of_le_one`, spelled out). -/
lemma mul_le_one_of_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  calc a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha hb0
    _ = b := one_mul b
    _ ≤ 1 := hb

/-- The decay envelope for rectangles of arcs: `1` at lags `0` and `1` (the trivial bound), and
`4 / 2^{⌊(n−2)/3⌋}` afterwards. -/
noncomputable def catRectEnv (n : ℕ) : ℝ := if n < 2 then 1 else 4 / 2 ^ ((n - 2) / 3)

/-- ★★ **Exponential decay of correlations for rectangles of arcs under the cat map**, complex
form, at lags `n ≥ 2`. -/
theorem norm_integral_rect_iterate_mul_sub_le {a b c d a' b' c' d' : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1)
    (ha' : 0 ≤ a') (hab' : a' < b') (hb' : b' ≤ 1) (hc' : 0 ≤ c') (hcd' : c' < d') (hd' : d' ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖(∫ p, rect (arcInd a b) (arcInd c d) (cat^[n] p) * rect (arcInd a' b') (arcInd c' d') p
          ∂(volume : Measure Torus2))
        - (∫ p, rect (arcInd a b) (arcInd c d) p ∂(volume : Measure Torus2))
          * ∫ p, rect (arcInd a' b') (arcInd c' d') p ∂(volume : Measure Torus2)‖
      ≤ 4 / 2 ^ ((n - 2) / 3) := by
  set R := catCutoff n with hR
  have hR1 : 1 ≤ R := catCutoff_pos n
  set u := arcInd a b with hu
  set v := arcInd c d with hv
  set u' := arcInd a' b' with hu'
  set v' := arcInd c' d' with hv'
  set f := rect u v with hf
  set f' := rect u' v' with hf'
  set T := rect (trunc R u) (trunc R v) with hT
  set T' := rect (trunc R u') (trunc R v') with hT'
  have hBu : BddC u := BddC.arcInd a b
  have hBv : BddC v := BddC.arcInd c d
  have hBu' : BddC u' := BddC.arcInd a' b'
  have hBv' : BddC v' := BddC.arcInd c' d'
  have hBf : BddT f := BddT.rect hBu hBv
  have hBf' : BddT f' := BddT.rect hBu' hBv'
  have hBT : BddT T := BddT.rect (BddC.trunc R (norm_arcInd_le a b)) (BddC.trunc R (norm_arcInd_le c d))
  have hBT' : BddT T' :=
    BddT.rect (BddC.trunc R (norm_arcInd_le a' b')) (BddC.trunc R (norm_arcInd_le c' d'))
  have hBD : BddT (f - T) := hBf.sub hBT
  have hBD' : BddT (f' - T') := hBf'.sub hBT'
  -- the decomposition of the integrand
  have hdecomp : ∀ p, f (cat^[n] p) * f' p
      = T (cat^[n] p) * T' p + T (cat^[n] p) * (f' - T') p + (f - T) (cat^[n] p) * f' p := by
    intro p; simp only [Pi.sub_apply]; ring
  have int1 : Integrable (fun p => T (cat^[n] p) * T' p) (volume : Measure Torus2) :=
    ((hBT.comp_cat_iterate n).mul hBT').integrable
  have int2 : Integrable (fun p => T (cat^[n] p) * (f' - T') p) (volume : Measure Torus2) :=
    ((hBT.comp_cat_iterate n).mul hBD').integrable
  have int3 : Integrable (fun p => (f - T) (cat^[n] p) * f' p) (volume : Measure Torus2) :=
    ((hBD.comp_cat_iterate n).mul hBf').integrable
  have hI : ∫ p, f (cat^[n] p) * f' p ∂(volume : Measure Torus2)
      = (∫ p, T (cat^[n] p) * T' p ∂(volume : Measure Torus2))
        + (∫ p, T (cat^[n] p) * (f' - T') p ∂(volume : Measure Torus2))
        + ∫ p, (f - T) (cat^[n] p) * f' p ∂(volume : Measure Torus2) := by
    have e1 := integral_add (int1.add int2) int3
    have e2 := integral_add int1 int2
    simp only [Pi.add_apply] at e1 e2
    rw [integral_congr_ae (ae_of_all _ hdecomp), e1, e2]
  -- the main term
  have hmain : ∫ p, T (cat^[n] p) * T' p ∂(volume : Measure Torus2)
      = (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, f' p ∂(volume : Measure Torus2) := by
    rw [hT, hT', hf, hf', integral_rect_trunc_mul_rect_trunc hn, integral_rect, integral_rect]
    simp only [fourierCoeff_zero_eq_integral]
  -- energies
  have hTe : ∫ p, ‖T p‖ ^ 2 ∂(volume : Measure Torus2) ≤ 1 := by
    rw [hT, integral_normSq_rect]
    have e1 := integral_normSq_trunc_le R (measurable_arcInd a b) (norm_arcInd_le a b)
    have e2 := integral_normSq_trunc_le R (measurable_arcInd c d) (norm_arcInd_le c d)
    rw [haarAddCircle_one_eq_volume] at e1 e2
    have e3 := BddC.integral_normSq_le_one (measurable_arcInd a b) (norm_arcInd_le a b)
    have e4 := BddC.integral_normSq_le_one (measurable_arcInd c d) (norm_arcInd_le c d)
    exact mul_le_one_of_le_one (e1.trans e3) (integral_nonneg fun x => by positivity) (e2.trans e4)
  have hfe' : ∫ p, ‖f' p‖ ^ 2 ∂(volume : Measure Torus2) ≤ 1 := by
    rw [hf', integral_normSq_rect]
    have e3 := BddC.integral_normSq_le_one (measurable_arcInd a' b') (norm_arcInd_le a' b')
    have e4 := BddC.integral_normSq_le_one (measurable_arcInd c' d') (norm_arcInd_le c' d')
    exact mul_le_one_of_le_one e3 (integral_nonneg fun x => by positivity) e4
  have hDe : ∫ p, ‖(f - T) p‖ ^ 2 ∂(volume : Measure Torus2) ≤ 4 / R := by
    simp only [Pi.sub_apply]
    exact integral_normSq_rect_sub_trunc_le ha hab hb hc hcd hd R hR1
  have hDe' : ∫ p, ‖(f' - T') p‖ ^ 2 ∂(volume : Measure Torus2) ≤ 4 / R := by
    simp only [Pi.sub_apply]
    exact integral_normSq_rect_sub_trunc_le ha' hab' hb' hc' hcd' hd' R hR1
  -- the two error terms, squared
  have hE1 : ‖∫ p, T (cat^[n] p) * (f' - T') p ∂(volume : Measure Torus2)‖ ^ 2 ≤ 4 / R := by
    refine (normSq_integral_mul_le (hBT.comp_cat_iterate n).memLp_two hBD'.memLp_two).trans ?_
    rw [integral_comp_cat_iterate (fun p => ‖T p‖ ^ 2) (hBT.measurable.norm.pow_const 2) n]
    calc _ ≤ (1 : ℝ) * (4 / (R : ℝ)) :=
          mul_le_mul hTe hDe' (integral_nonneg fun p => by positivity) zero_le_one
      _ = 4 / (R : ℝ) := one_mul _
  have hE2 : ‖∫ p, (f - T) (cat^[n] p) * f' p ∂(volume : Measure Torus2)‖ ^ 2 ≤ 4 / R := by
    refine (normSq_integral_mul_le (hBD.comp_cat_iterate n).memLp_two hBf'.memLp_two).trans ?_
    rw [integral_comp_cat_iterate (fun p => ‖(f - T) p‖ ^ 2) (hBD.measurable.norm.pow_const 2) n]
    calc _ ≤ (4 / (R : ℝ)) * (1 : ℝ) :=
          mul_le_mul hDe hfe' (integral_nonneg fun p => by positivity) (by positivity)
      _ = 4 / (R : ℝ) := mul_one _
  -- from squares to norms: `4 / R = (2 / 2^j)^2`
  have hsq : (4 : ℝ) / R = (2 / 2 ^ ((n - 2) / 3)) ^ 2 := by
    rw [hR, catCutoff_eq_sq]; push_cast; field_simp; norm_num
  have hpos : (0 : ℝ) ≤ 2 / 2 ^ ((n - 2) / 3) := by positivity
  rw [hsq] at hE1 hE2
  have hE1' := (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).mp hE1
  have hE2' := (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).mp hE2
  calc ‖(∫ p, f (cat^[n] p) * f' p ∂(volume : Measure Torus2))
        - (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, f' p ∂(volume : Measure Torus2)‖
      = ‖(∫ p, T (cat^[n] p) * (f' - T') p ∂(volume : Measure Torus2))
          + ∫ p, (f - T) (cat^[n] p) * f' p ∂(volume : Measure Torus2)‖ := by
        rw [hI, hmain]; congr 1; ring
    _ ≤ ‖∫ p, T (cat^[n] p) * (f' - T') p ∂(volume : Measure Torus2)‖
          + ‖∫ p, (f - T) (cat^[n] p) * f' p ∂(volume : Measure Torus2)‖ := norm_add_le _ _
    _ ≤ 2 / 2 ^ ((n - 2) / 3) + 2 / 2 ^ ((n - 2) / 3) := add_le_add hE1' hE2'
    _ = 4 / 2 ^ ((n - 2) / 3) := by ring

/-! #### The real form -/

/-- The real indicator of the arc `(a, b)`. -/
noncomputable def arcIndR (a b : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  fun x => Set.indicator (Set.Ioo a b) (fun _ => (1 : ℝ)) (unitRep x)

lemma arcInd_eq_ofReal (a b : ℝ) (x : AddCircle (1 : ℝ)) : arcInd a b x = (arcIndR a b x : ℂ) := by
  unfold arcInd arcIndR
  simp only [Set.indicator_apply]
  split_ifs <;> simp

lemma measurable_arcIndR (a b : ℝ) : Measurable (arcIndR a b) :=
  (measurable_const.indicator measurableSet_Ioo).comp measurable_unitRep

lemma arcIndR_nonneg (a b : ℝ) (x : AddCircle (1 : ℝ)) : 0 ≤ arcIndR a b x := by
  unfold arcIndR; rw [Set.indicator_apply]; split_ifs <;> norm_num

lemma arcIndR_le_one (a b : ℝ) (x : AddCircle (1 : ℝ)) : arcIndR a b x ≤ 1 := by
  unfold arcIndR; rw [Set.indicator_apply]; split_ifs <;> norm_num

/-- The real indicator of the rectangle `(a, b) × (c, d)` of the torus. -/
noncomputable def rectIndR (a b c d : ℝ) : Torus2 → ℝ := fun p => arcIndR a b p.1 * arcIndR c d p.2

lemma rect_arcInd_eq_ofReal (a b c d : ℝ) (p : Torus2) :
    rect (arcInd a b) (arcInd c d) p = (rectIndR a b c d p : ℂ) := by
  simp [rect, rectIndR, arcInd_eq_ofReal]

lemma measurable_rectIndR (a b c d : ℝ) : Measurable (rectIndR a b c d) :=
  ((measurable_arcIndR a b).comp measurable_fst).mul ((measurable_arcIndR c d).comp measurable_snd)

lemma rectIndR_nonneg (a b c d : ℝ) (p : Torus2) : 0 ≤ rectIndR a b c d p :=
  mul_nonneg (arcIndR_nonneg _ _ _) (arcIndR_nonneg _ _ _)

lemma rectIndR_le_one (a b c d : ℝ) (p : Torus2) : rectIndR a b c d p ≤ 1 :=
  mul_le_one_of_le_one (arcIndR_le_one _ _ _) (arcIndR_nonneg _ _ _) (arcIndR_le_one _ _ _)

/-- ★★ **The real form at lags `n ≥ 2`.** -/
theorem abs_integral_rectIndR_iterate_mul_sub_le {a b c d a' b' c' d' : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1)
    (ha' : 0 ≤ a') (hab' : a' < b') (hb' : b' ≤ 1) (hc' : 0 ≤ c') (hcd' : c' < d') (hd' : d' ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    |(∫ p, rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p ∂(volume : Measure Torus2))
        - (∫ p, rectIndR a b c d p ∂(volume : Measure Torus2))
          * ∫ p, rectIndR a' b' c' d' p ∂(volume : Measure Torus2)|
      ≤ 4 / 2 ^ ((n - 2) / 3) := by
  have h := norm_integral_rect_iterate_mul_sub_le ha hab hb hc hcd hd ha' hab' hb' hc' hcd' hd' hn
  have e1 : ∫ p, rect (arcInd a b) (arcInd c d) (cat^[n] p) * rect (arcInd a' b') (arcInd c' d') p
        ∂(volume : Measure Torus2)
      = ((∫ p, rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p
          ∂(volume : Measure Torus2) : ℝ) : ℂ) :=
    calc _ = ∫ p, ((rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p : ℝ) : ℂ)
            ∂(volume : Measure Torus2) :=
          integral_congr_ae (ae_of_all _ fun p => by simp [rect_arcInd_eq_ofReal])
      _ = _ := integral_ofReal
  have e2 : ∫ p, rect (arcInd a b) (arcInd c d) p ∂(volume : Measure Torus2)
      = ((∫ p, rectIndR a b c d p ∂(volume : Measure Torus2) : ℝ) : ℂ) :=
    calc _ = ∫ p, ((rectIndR a b c d p : ℝ) : ℂ) ∂(volume : Measure Torus2) :=
          integral_congr_ae (ae_of_all _ fun p => rect_arcInd_eq_ofReal a b c d p)
      _ = _ := integral_ofReal
  have e3 : ∫ p, rect (arcInd a' b') (arcInd c' d') p ∂(volume : Measure Torus2)
      = ((∫ p, rectIndR a' b' c' d' p ∂(volume : Measure Torus2) : ℝ) : ℂ) :=
    calc _ = ∫ p, ((rectIndR a' b' c' d' p : ℝ) : ℂ) ∂(volume : Measure Torus2) :=
          integral_congr_ae (ae_of_all _ fun p => rect_arcInd_eq_ofReal a' b' c' d' p)
      _ = _ := integral_ofReal
  rw [e1, e2, e3, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

/-- Both integrals of a `[0,1]`-valued rectangle pair lie in `[0, 1]`, so the trivial bound is `1`. -/
theorem abs_integral_rectIndR_iterate_mul_sub_le_one (a b c d a' b' c' d' : ℝ) (n : ℕ) :
    |(∫ p, rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p ∂(volume : Measure Torus2))
        - (∫ p, rectIndR a b c d p ∂(volume : Measure Torus2))
          * ∫ p, rectIndR a' b' c' d' p ∂(volume : Measure Torus2)| ≤ 1 := by
  have hm1 : Measurable (fun p => rectIndR a b c d (cat^[n] p)) :=
    (measurable_rectIndR a b c d).comp (measurable_cat.iterate n)
  have hI1 : Integrable (fun p => rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p)
      (volume : Measure Torus2) :=
    Integrable.of_bound (hm1.mul (measurable_rectIndR _ _ _ _)).aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rectIndR_nonneg _ _ _ _ _)
          (rectIndR_nonneg _ _ _ _ _))]
        exact mul_le_one_of_le_one (rectIndR_le_one _ _ _ _ _) (rectIndR_nonneg _ _ _ _ _)
          (rectIndR_le_one _ _ _ _ _))
  have hI2 : Integrable (rectIndR a b c d) (volume : Measure Torus2) :=
    Integrable.of_bound (measurable_rectIndR _ _ _ _).aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (rectIndR_nonneg _ _ _ _ _)]
        exact rectIndR_le_one _ _ _ _ _)
  have hI3 : Integrable (rectIndR a' b' c' d') (volume : Measure Torus2) :=
    Integrable.of_bound (measurable_rectIndR _ _ _ _).aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (rectIndR_nonneg _ _ _ _ _)]
        exact rectIndR_le_one _ _ _ _ _)
  have h1 : 0 ≤ ∫ p, rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p
      ∂(volume : Measure Torus2) :=
    integral_nonneg fun p => mul_nonneg (rectIndR_nonneg _ _ _ _ _) (rectIndR_nonneg _ _ _ _ _)
  have h2 : ∫ p, rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p
      ∂(volume : Measure Torus2) ≤ 1 := by
    calc _ ≤ ∫ _p, (1 : ℝ) ∂(volume : Measure Torus2) :=
          integral_mono hI1 (integrable_const 1) fun p =>
            mul_le_one_of_le_one (rectIndR_le_one _ _ _ _ _) (rectIndR_nonneg _ _ _ _ _)
              (rectIndR_le_one _ _ _ _ _)
      _ = 1 := by simp
  have h3 : 0 ≤ ∫ p, rectIndR a b c d p ∂(volume : Measure Torus2) :=
    integral_nonneg fun p => rectIndR_nonneg _ _ _ _ _
  have h4 : ∫ p, rectIndR a b c d p ∂(volume : Measure Torus2) ≤ 1 := by
    calc _ ≤ ∫ _p, (1 : ℝ) ∂(volume : Measure Torus2) :=
          integral_mono hI2 (integrable_const 1) fun p => rectIndR_le_one _ _ _ _ _
      _ = 1 := by simp
  have h5 : 0 ≤ ∫ p, rectIndR a' b' c' d' p ∂(volume : Measure Torus2) :=
    integral_nonneg fun p => rectIndR_nonneg _ _ _ _ _
  have h6 : ∫ p, rectIndR a' b' c' d' p ∂(volume : Measure Torus2) ≤ 1 := by
    calc _ ≤ ∫ _p, (1 : ℝ) ∂(volume : Measure Torus2) :=
          integral_mono hI3 (integrable_const 1) fun p => rectIndR_le_one _ _ _ _ _
      _ = 1 := by simp
  rw [abs_le]
  constructor <;> nlinarith

/-- ★★ **The pair correlation of two rectangles of arcs decays with the envelope `catRectEnv`.** -/
theorem abs_integral_rectIndR_iterate_mul_sub_le_env {a b c d a' b' c' d' : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1)
    (ha' : 0 ≤ a') (hab' : a' < b') (hb' : b' ≤ 1) (hc' : 0 ≤ c') (hcd' : c' < d') (hd' : d' ≤ 1)
    (n : ℕ) :
    |(∫ p, rectIndR a b c d (cat^[n] p) * rectIndR a' b' c' d' p ∂(volume : Measure Torus2))
        - (∫ p, rectIndR a b c d p ∂(volume : Measure Torus2))
          * ∫ p, rectIndR a' b' c' d' p ∂(volume : Measure Torus2)|
      ≤ catRectEnv n := by
  unfold catRectEnv
  split_ifs with hn
  · exact abs_integral_rectIndR_iterate_mul_sub_le_one a b c d a' b' c' d' n
  · exact abs_integral_rectIndR_iterate_mul_sub_le ha hab hb hc hcd hd ha' hab' hb' hc' hcd' hd'
      (not_lt.mp hn)

/-! #### The envelope is summable -/

/-- `(5/4)^m ≤ 2 · 2^{⌊m/3⌋}`, because `(5/4)³ < 2` and `(5/4)² < 2`. -/
lemma five_fourth_pow_le_two_mul_two_pow (m : ℕ) : (5 / 4 : ℝ) ^ m ≤ 2 * 2 ^ (m / 3) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 3 ∧ m = 3 * q + r :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
  have hq : (3 * q + r) / 3 = q := by omega
  rw [hq, pow_add, pow_mul]
  have h1 : ((5 / 4 : ℝ) ^ 3) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h2 : (5 / 4 : ℝ) ^ r ≤ 2 := by interval_cases r <;> norm_num
  calc ((5 / 4 : ℝ) ^ 3) ^ q * (5 / 4 : ℝ) ^ r ≤ 2 ^ q * 2 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 2 * 2 ^ q := by ring

lemma catRectEnv_nonneg (n : ℕ) : 0 ≤ catRectEnv n := by
  unfold catRectEnv; split_ifs <;> positivity

/-- The envelope is dominated by the geometric sequence `13 · (4/5)^n`. -/
lemma catRectEnv_le_geometric (n : ℕ) : catRectEnv n ≤ 13 * (4 / 5 : ℝ) ^ n := by
  unfold catRectEnv
  split_ifs with hn
  · interval_cases n <;> norm_num
  · have hn2 : 2 ≤ n := not_lt.mp hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h := five_fourth_pow_le_two_mul_two_pow m
    have hpow : (0 : ℝ) < 2 ^ (m / 3) := by positivity
    have h54 : (0 : ℝ) < (5 / 4 : ℝ) ^ m := by positivity
    have hgeom : (4 / 5 : ℝ) ^ (m + 2) = (16 / 25) * ((5 / 4 : ℝ) ^ m)⁻¹ := by
      rw [pow_add, ← inv_pow, show ((5 / 4 : ℝ))⁻¹ = 4 / 5 by norm_num]; ring
    rw [hgeom, div_le_iff₀ hpow]
    rw [show (13 : ℝ) * (16 / 25 * ((5 / 4 : ℝ) ^ m)⁻¹) * 2 ^ (m / 3)
        = (13 * (16 / 25) * 2 ^ (m / 3)) / (5 / 4 : ℝ) ^ m by ring, le_div_iff₀ h54]
    linarith

/-- ★ The envelope is summable. -/
theorem summable_catRectEnv : Summable catRectEnv :=
  Summable.of_nonneg_of_le catRectEnv_nonneg catRectEnv_le_geometric
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 13)

/-- ★★★ **A rectangle of arcs has exponentially decaying correlations under the cat map**, in the
corpus's `HasCorrelationDecay` form. -/
theorem cat_hasCorrelationDecay_rectIndR {a b c d : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1) :
    HasCorrelationDecay (volume : Measure Torus2) cat (rectIndR a b c d) catRectEnv := by
  refine HasCorrelationDecay.of_measurePreserving measurePreserving_cat (measurable_rectIndR a b c d)
    fun n => ?_
  have h := abs_integral_rectIndR_iterate_mul_sub_le_env ha hab hb hc hcd hd ha hab hb hc hcd hd n
  rw [integral_congr_ae (ae_of_all _ fun p => mul_comm (rectIndR a b c d (cat^[n] p))
    (rectIndR a b c d p))] at h
  rw [sq]
  exact h

end MeasureTheory
