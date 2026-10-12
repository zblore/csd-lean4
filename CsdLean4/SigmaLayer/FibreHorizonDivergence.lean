/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreFiniteHorizon
public import CsdLean4.Mathlib.InformationTheory.ChiSquare

/-!
# The finite-horizon bound in relative-entropy form

**Category:** 7-SigmaLayer.
BACKLOG #130, out of #118(ii).

[`FibreFiniteHorizon.lean`](FibreFiniteHorizon.lean) (#118(ii)) proved the `L²` statement: at
horizon `T` the mean-square deviation of a cell's time-averaged occupation from its Haar value is at
most `(2/T)·∑_{u<T} ε u`, and summed over the `(m+1)²` cells it costs one factor `(m+1)²`.
`R-019`'s second clause is phrased in **relative entropy**, and this file says the same thing in
that vocabulary.

Two pieces, exactly as #130 priced them.

* **The occupation law.** `horizonLaw m T p` is the time-averaged occupation of the cells along the
  orbit of `p` out to `T`, as a `Measure` on the cells rather than a family of real numbers: the
  uniform average of the `T` Dirac masses at the cells visited. ★★ `horizonLaw_real_apply`
  identifies its mass at `c` with #118(ii)'s Birkhoff average, so the two files are talking about
  the same object; ★ `isProbabilityMeasure_horizonLaw` for `T > 0`, and ★ `measurable_horizonLaw`
  is the measurability in the base point #130 asked for.
* **The divergence bound.** ★★★ `klDiv_horizonLaw_le_chiSq`: the divergence of the occupation law
  from the uniform cell law is at most `(m+1)²` times the mean-square deviation of the occupations
  from `1/(m+1)²`, pointwise in the base point. With #118(ii) that is the relative-entropy reading
  of the finite-horizon bound, at the cost of one more factor `(m+1)²`.

## Honest scope

⚠️ **The reference is the uniform cell law, and #118(ii)'s is the Haar cell law.** The chi-squared
inequality is proved against `uniformOn univ`
([`ChiSquare.lean`](../Mathlib/InformationTheory/ChiSquare.lean)), so the deviation below is measured
from `1/(m+1)²`, while #118(ii) measures it from `coarseLaw (kMuL p₀) (fibreCell m)`. **These agree
only if the Haar cell law is uniform, and nothing in this corpus proves that.** It is true — the
cells of `circCell` have equal width by construction — but the proof is a floor-and-endpoint
computation on `AddCircle 1` with the `min m` clamp and the `(0, 1]` representative to handle, and it
is **BACKLOG #144**. Combining the bound below with #118(ii) therefore needs that identification,
which is why no such combination is stated here: #130's own phrasing assumed it silently, and naming
it is the honest form. What *is* proved below needs no such hypothesis.

⚠️ **Still time-averaged, so still not `R-019`.** Everything inherits #118(ii)'s scope: what
equilibrates is a cell's *time-averaged* occupation, not the law at step `n`. The entropy vocabulary
changes nothing about that, exactly as the row that wanted it recorded.

⚠️ **`(m+1)²` on top of #118(ii)'s `(m+1)²`.** The chi-squared conversion costs one factor of the
cell count, so in this vocabulary the bound degrades *quartically* in the fineness of the
coarse-graining. `R-019`'s "rate set by the cell size" is further away here than in the `L²` reading,
not closer.

⚠️ **The occupation law is not a limit object.** `horizonLaw m T p` is a finite average over
`[0, T)`; nothing says it converges as `T → ∞`, and the `T = 0` value is the zero measure.

References: [`FibreFiniteHorizon.lean`](FibreFiniteHorizon.lean) (#118(ii), `fibreCellInd`,
`integral_sum_birkhoffAverage_fibreCellInd_sub_sq_le`),
[`FibreCoarseArrow.lean`](FibreCoarseArrow.lean) (`fibreCell`, `fibreStroke`, `circCell`),
[`ChiSquare.lean`](../Mathlib/InformationTheory/ChiSquare.lean) (`klDiv_uniformOn_univ_le_chiSq`);
`specs/BACKLOG.md` #130, #118, #144; `specs/residues.tsv` `R-019`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set InformationTheory

open scoped ENNReal

namespace CSD.SigmaLayer

open LF4

/-! ### The cell indicator as a test for one cell -/

/-- The cell indicator, as the test `fibreCell p = c`. -/
theorem fibreCellInd_eq_ite {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (q : KSigma N) :
    fibreCellInd m c q = if fibreCell (N := N) m q = c then (1 : ℝ) else 0 := by
  classical
  rw [fibreCellInd, Set.indicator_apply]
  simp [Set.mem_preimage]

theorem fibreCellInd_nonneg {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (q : KSigma N) :
    0 ≤ fibreCellInd m c q := by
  rw [fibreCellInd_eq_ite]
  split <;> norm_num

/-! ### The time-averaged occupation law of the cells -/

/-- **The occupation law at horizon `T`**: the uniform average of the Dirac masses at the cells the
orbit of `p` visits over `[0, T)`. This is #118(ii)'s family of Birkhoff averages assembled into a
single measure on the cells, which is the form a divergence takes its argument in. -/
noncomputable def horizonLaw {N : ℕ} (m : ℕ) (T : ℕ) (p : KSigma N) :
    Measure (Fin (m + 1) × Fin (m + 1)) :=
  (T : ℝ≥0∞)⁻¹ • ∑ u ∈ Finset.range T, Measure.dirac (fibreCell (N := N) m (fibreStroke^[u] p))

/-- ★★ **Its mass at a cell is #118(ii)'s Birkhoff average**, so the two files are about one
object. -/
theorem horizonLaw_real_apply {N : ℕ} (m T : ℕ) (p : KSigma N)
    (c : Fin (m + 1) × Fin (m + 1)) :
    (horizonLaw m T p).real {c}
      = birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p := by
  have hone : ∀ u : ℕ,
      (Measure.dirac (fibreCell (N := N) m (fibreStroke^[u] p))) ({c} : Set _)
        = ENNReal.ofReal (fibreCellInd (N := N) m c (fibreStroke^[u] p)) := by
    intro u
    rw [Measure.dirac_apply, fibreCellInd_eq_ite]
    by_cases h : fibreCell (N := N) m (fibreStroke^[u] p) = c <;> simp [h]
  rw [horizonLaw, measureReal_def, Measure.smul_apply, smul_eq_mul]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, hone]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => fibreCellInd_nonneg m c _),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun u _ => fibreCellInd_nonneg m c _),
    birkhoffAverage, birkhoffSum, smul_eq_mul]

/-- ★ **It is a probability measure at a positive horizon.** -/
theorem isProbabilityMeasure_horizonLaw {N : ℕ} (m T : ℕ) (p : KSigma N) (hT : 0 < T) :
    IsProbabilityMeasure (horizonLaw (N := N) m T p) := by
  constructor
  rw [horizonLaw, Measure.smul_apply, smul_eq_mul]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.dirac_apply_of_mem (mem_univ _),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hT.ne') (ENNReal.natCast_ne_top T)]

/-- ★ **Measurable in the base point**, which is what makes the divergence below a function of `p`
that can be integrated. -/
theorem measurable_horizonLaw {N : ℕ} (m T : ℕ) :
    Measurable fun p : KSigma N => horizonLaw (N := N) m T p := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [horizonLaw, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply]
  refine Measurable.const_mul (Finset.measurable_sum _ fun u _ => ?_) _
  simpa only [Measure.dirac_apply' _ hs, Function.comp_def] using
    (measurable_one.indicator hs).comp
      ((measurable_fibreCell m).comp (measurable_fibreStroke.iterate u))

/-! ### The divergence bound -/

/-- ★★★ **The finite-horizon bound in relative-entropy form.**

The divergence of the time-averaged occupation law from the uniform cell law is at most `(m+1)²`
times the mean-square deviation of the occupations from `1/(m+1)²`. This is the chi-squared
inequality of [`ChiSquare.lean`](../Mathlib/InformationTheory/ChiSquare.lean) at the occupation law,
and it is the conversion `R-019`'s second clause asks for: an `L²` estimate on the occupations
becomes an estimate on the divergence, at the cost of one factor of the cell count. -/
theorem klDiv_horizonLaw_le_chiSq {N : ℕ} (m T : ℕ) (p : KSigma N) (hT : 0 < T) :
    klDiv (horizonLaw (N := N) m T p) (uniformOn (univ : Set (Fin (m + 1) × Fin (m + 1))))
      ≤ ENNReal.ofReal (((m : ℝ) + 1) ^ 2 *
          ∑ c : Fin (m + 1) × Fin (m + 1),
            (birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p
              - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2) := by
  have := isProbabilityMeasure_horizonLaw (N := N) m T p hT
  have hcard : (Fintype.card (Fin (m + 1) × Fin (m + 1)) : ℝ) = ((m : ℝ) + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have h := klDiv_uniformOn_univ_le_chiSq (horizonLaw (N := N) m T p)
  rwa [hcard, Finset.sum_congr rfl
    (fun c (_ : c ∈ (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1)))) =>
      by rw [horizonLaw_real_apply])] at h

end CSD.SigmaLayer

end
