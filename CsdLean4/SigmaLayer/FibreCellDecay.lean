/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreHorizonDivergence
public import CsdLean4.SigmaLayer.FibreCellUniform
public import CsdLean4.Mathlib.Dynamics.CatMapMixing

/-!
# The fibre cells decorrelate under the hyperbolic stroke

**Category:** 7-SigmaLayer.
BACKLOG #118(i), the hypothesis #118(ii), #130 and #144 consumed; `R-019`.

Every finite-horizon theorem of [`FibreFiniteHorizon.lean`](FibreFiniteHorizon.lean),
[`FibreHorizonDivergence.lean`](FibreHorizonDivergence.lean) and
[`FibreCellUniform.lean`](FibreCellUniform.lean) took **finite-horizon correlation decay of the
cell indicators** as a hypothesis, #118(i), recorded as a genuine mathematical question about the
cat map on indicator functions. This file proves it, and then states what the corpus's rate
theorems become once their hypothesis is a theorem.

## The identification

A fibre cell `fibreCell m ⁻¹' {(k, l)}` is a product of two circle cells, and a circle cell is the
open grid arc `(k/(m+1), (k+1)/(m+1))` up to its two endpoints
(★ `circCell_ind_ae_eq_arcIndR`, from `FibreCellUniform.lean`'s sandwich). So on `Σ`, almost
everywhere for `μL`, ★★ `fibreCellInd_ae_eq_rectIndR`: the cell indicator is the indicator of a
rectangle of arcs on the fibre, exactly the observable
[`Mathlib/Dynamics/CatMapMixing.lean`](../Mathlib/Dynamics/CatMapMixing.lean) decorrelates. Decay
transfers across almost-everywhere equality of the observable
(`HasCorrelationDecay.congr_ae`, through measure preservation of the stroke) and lifts from the
fibre to `Σ` along the second projection (`HasCorrelationDecay.liftSnd`, the base carrying mass `1`).

## The results

* ★★★ `fibreStroke_hasCorrelationDecay_fibreCellInd`: **every fibre cell's indicator has
  exponentially decaying correlations under the hyperbolic stroke**, with the explicit summable
  envelope `catRectEnv` (`4 · 2^{-⌊(n−2)/3⌋}` from lag `2`). #118(i), discharged for the corpus's
  hyperbolic fibre map.
* ★★★ `integral_birkhoffAverage_fibreCellInd_sub_sq_le_hyperbolic`: the finite-horizon
  equilibration of a cell, **unconditionally**: the mean-square deviation of its time-averaged
  occupation from `1/(m+1)²` is at most `130/T` at horizon `T`; and
  ★★★ `tendsto_integral_birkhoffAverage_fibreCellInd_sub_sq_hyperbolic`, the `L²` convergence of
  the time averages with no hypothesis.
* ★★★ `abs_integral_fibreCellInd_iterate_mul_sub_le`: **two cells decorrelate at step `n`**:
  the joint occupation of `c'` after `n` strokes and of `c` now is within `catRectEnv n` of
  `1/(m+1)⁴`. This is instantaneous (mixing), not a time average.
* ★★★ `abs_stepWeight_sub_le` and ★★★ `klDiv_stepLaw_le`: **the law at step `n` of a
  coarse-grained initial density approaches the uniform cell law, in relative entropy, at the rate
  of the envelope.** For a density `∑ w_c 1_c` constant on the cells, nonnegative and normalised,
  the cell law after `n` strokes (`stepLaw`, a probability measure on the cells) satisfies
  `klDiv (stepLaw n) (uniform) ≤ (m+1)⁸ · catRectEnv n²`, through the chi-squared bound of
  `ChiSquare.lean`. This is `R-019`'s second clause, *the distribution approaches Haar*, stated at
  step `n` in `klDiv`, with a rate in the cell count, for the hyperbolic fibre map and every initial
  distribution coarse-grained on the same grid. Together with the monotone clause of
  `FibreCoarseArrow.lean` (#18) it is the relaxation statement Track B asked for, on this map.

## Honest scope

* **The map is the available hyperbolic witness, not a derived de-isolation dynamics.**
  `catStroke` is `MovingFibreWitness.lean`'s cat map on the fibre, offered there as an available
  hyperbolic fibre map and not wired into a `ConstraintDynamics`. That the physical de-isolation
  flow acts on the fibre by a hyperbolic map is the A5/D1 residue (Posit 1, BACKLOG #19); nothing
  here derives it. What is proved is: *given* that map, the fibre relaxes, with these rates.
* **Initial densities coarse-grained on the grid.** `cellDensity` is constant on the `(m+1)²`
  cells. A density that is a finite combination of indicators of arbitrary rectangles of arcs is
  covered by the same Category-1 pair bound; a general `L²` density is not formalised (the step
  functions are dense, which is the one missing step, BACKLOG #147).
  The relaxation H-theorem for the fibre stays on the map identification and on general initial densities. RESIDUE(R-019)
* **The constants are polynomial in the cell count**, `(m+1)⁸` in the divergence bound, from
  `(m+1)²` cells each deviating by at most `(m+1)² · catRectEnv n`, and the envelope is not sharp
  (see the Category-1 file). The exponential rate in `n` is what matters, and the first-passage
  question #118(iii) was not needed for it.
* **Unchanged:** nothing here is about the translation `kFlow`, which
  `relaxation_requires_hyperbolic_fibre` shows cannot decorrelate; the typicality posits are
  untouched.

References: `specs/BACKLOG.md` #118, #18, #130, #144, #147; `specs/residues.tsv` `R-019`;
`Mathlib/Dynamics/CatMapMixing.lean`; `SigmaLayer/FibreFiniteHorizon.lean`;
`SigmaLayer/FibreHorizonDivergence.lean`; `SigmaLayer/FibreCellUniform.lean`;
`SigmaLayer/MovingFibreWitness.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal

namespace CSD.SigmaLayer

open LF4 Matrix.UnitaryGroup

/-! ### A fibre cell is a rectangle of arcs, almost everywhere -/

/-- The representative used by the Category-1 arcs is the record layer's `rep`. -/
theorem unitRep_eq_rep : MeasureTheory.unitRep = RecordLayer.rep := rfl

/-- The left endpoint of the `k`-th grid arc. -/
noncomputable abbrev gridLo (m : ℕ) (k : Fin (m + 1)) : ℝ := ((k : ℕ) : ℝ) / ((m : ℝ) + 1)

/-- The right endpoint of the `k`-th grid arc. -/
noncomputable abbrev gridHi (m : ℕ) (k : Fin (m + 1)) : ℝ := (((k : ℕ) : ℝ) + 1) / ((m : ℝ) + 1)

lemma gridLo_nonneg (m : ℕ) (k : Fin (m + 1)) : 0 ≤ gridLo m k := by
  unfold gridLo; positivity

lemma gridLo_lt_gridHi (m : ℕ) (k : Fin (m + 1)) : gridLo m k < gridHi m k := by
  unfold gridLo gridHi
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [div_lt_div_iff_of_pos_right hM]
  linarith

lemma gridHi_le_one (m : ℕ) (k : Fin (m + 1)) : gridHi m k ≤ 1 := by
  unfold gridHi
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [div_le_one hM]
  have : (k : ℕ) ≤ m := Nat.lt_succ_iff.mp k.2
  exact_mod_cast Nat.succ_le_succ this

/-- The `rep`-preimage of a single point of the circle is null. -/
lemma volume_rep_preimage_singleton (t : ℝ) :
    (volume : Measure (AddCircle (1 : ℝ))) (RecordLayer.rep ⁻¹' {t}) = 0 := by
  rw [RecordLayer.volume_rep_preimage (measurableSet_singleton t)]
  exact measure_mono_null inter_subset_left Real.volume_singleton

/-- ★ **A circle cell is its open grid arc up to a null set**: the two indicators differ only at
the two endpoints of the arc. -/
theorem circCell_ind_ae_eq_arcIndR (m : ℕ) (k : Fin (m + 1)) :
    (fun x : AddCircle (1 : ℝ) => if circCell m x = k then (1 : ℝ) else 0)
      =ᵐ[(volume : Measure (AddCircle (1 : ℝ)))] MeasureTheory.arcIndR (gridLo m k) (gridHi m k) := by
  have hsub : {x : AddCircle (1 : ℝ) |
      ¬ ((if circCell m x = k then (1 : ℝ) else 0) = MeasureTheory.arcIndR (gridLo m k) (gridHi m k) x)}
      ⊆ RecordLayer.rep ⁻¹' {gridLo m k} ∪ RecordLayer.rep ⁻¹' {gridHi m k} := by
    intro x hx
    simp only [mem_ofPred_eq, MeasureTheory.arcIndR, unitRep_eq_rep, Set.indicator_apply] at hx
    have hcell : circCell m x = k ↔ RecordLayer.rep x ∈ cellSet m (k : ℕ) := by
      have := congrArg (fun S => x ∈ S) (circCell_preimage m k)
      simpa using this
    have hrep := RecordLayer.rep_mem_Ioc x
    by_cases hmem : RecordLayer.rep x ∈ Ioo (gridLo m k) (gridHi m k)
    · exfalso
      have hk : circCell m x = k := hcell.mpr (Ioo_subset_cellSet_inter m k hmem).1
      simp [hk, hmem] at hx
    · by_cases hk : circCell m x = k
      · have hIcc : RecordLayer.rep x ∈ Icc (gridLo m k) (gridHi m k) :=
          cellSet_inter_subset_Icc m k ⟨hcell.mp hk, hrep⟩
        simp only [mem_Ioo, not_and_or, not_lt] at hmem
        simp only [mem_Icc] at hIcc
        rcases hmem with h | h
        · exact Or.inl (by simp only [mem_preimage, mem_singleton_iff]; linarith)
        · exact Or.inr (by simp only [mem_preimage, mem_singleton_iff]; linarith)
      · exfalso
        simp [hk, hmem] at hx
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null hsub (measure_union_null (volume_rep_preimage_singleton _)
    (volume_rep_preimage_singleton _))

/-- The cell indicator on `Σ` factors through the fibre as a product of two circle tests. -/
lemma fibreCellInd_eq_mul_ite {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (p : KSigma N) :
    fibreCellInd (N := N) m c p
      = (if circCell m p.2.1 = c.1 then (1 : ℝ) else 0)
        * (if circCell m p.2.2 = c.2 then (1 : ℝ) else 0) := by
  rw [fibreCellInd_eq_ite]
  simp only [fibreCell, torusCell, Prod.ext_iff]
  split_ifs <;> simp_all

/-- ★★ **A fibre cell is a rectangle of grid arcs on the fibre, almost everywhere for `μL`.** -/
theorem fibreCellInd_ae_eq_rectIndR {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) :
    fibreCellInd (N := N) m c =ᵐ[kMuL p₀]
      fun p => MeasureTheory.rectIndR (gridLo m c.1) (gridHi m c.1) (gridLo m c.2) (gridHi m c.2) p.2 := by
  have h1 := circCell_ind_ae_eq_arcIndR m c.1
  have h2 := circCell_ind_ae_eq_arcIndR m c.2
  have e1 := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (AddCircle (1 : ℝ))))
    (ν := (volume : Measure (AddCircle (1 : ℝ))))).ae_eq_comp h1
  have e2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (AddCircle (1 : ℝ))))
    (ν := (volume : Measure (AddCircle (1 : ℝ))))).ae_eq_comp h2
  have hT : (fun y : KTorus => (if circCell m y.1 = c.1 then (1 : ℝ) else 0)
        * (if circCell m y.2 = c.2 then (1 : ℝ) else 0))
      =ᵐ[(volume : Measure KTorus)]
        fun y => MeasureTheory.rectIndR (gridLo m c.1) (gridHi m c.1) (gridLo m c.2) (gridHi m c.2) y := by
    have := e1.mul e2
    rw [Measure.volume_eq_prod]
    exact this
  have hS := (Measure.quasiMeasurePreserving_snd (μ := fsMeasure p₀)
    (ν := (volume : Measure KTorus))).ae_eq_comp hT
  have hfun : fibreCellInd (N := N) m c
      = (fun y : KTorus => (if circCell m y.1 = c.1 then (1 : ℝ) else 0)
          * (if circCell m y.2 = c.2 then (1 : ℝ) else 0)) ∘ Prod.snd := by
    funext p; exact fibreCellInd_eq_mul_ite m c p
  rw [hfun, kMuL]
  exact hS

/-! ### Transport from the fibre to `Σ` -/

lemma fsMeasure_univ_eq_one {N : ℕ} (p₀ : CPN N) : fsMeasure p₀ univ = 1 := measure_univ

/-- Integrating a function of the fibre coordinate against `μL` integrates it against Haar on the
fibre: the base carries total mass `1`. -/
lemma integral_snd_kMuL {N : ℕ} (p₀ : CPN N) (h : KTorus → ℝ) :
    ∫ p, h p.2 ∂(kMuL p₀) = ∫ y, h y ∂(volume : Measure KTorus) := by
  rw [kMuL]
  have := integral_prod_mul (μ := fsMeasure p₀) (ν := (volume : Measure KTorus))
    (fun _ : CPN N => (1 : ℝ)) h
  simp only [one_mul] at this
  rw [this, integral_const, measureReal_def, fsMeasure_univ_eq_one]
  simp

lemma fibreStroke_iterate {N : ℕ} (u : ℕ) (p : KSigma N) :
    fibreStroke^[u] p = (p.1, catStroke^[u] p.2) := by
  rw [fibreStroke, Prod.map_iterate, Function.iterate_id]
  rfl

/-- Decay of a fibre observable lifts to `Σ` along the second projection. -/
theorem HasCorrelationDecay.liftSnd {N : ℕ} (p₀ : CPN N) {g : KTorus → ℝ} {ε : ℕ → ℝ}
    (hg : HasCorrelationDecay (volume : Measure KTorus) catStroke g ε) :
    HasCorrelationDecay (kMuL p₀) fibreStroke (fun p => g p.2) ε := by
  intro s t
  simp only [fibreStroke_iterate]
  rw [integral_snd_kMuL p₀ (fun y => g (catStroke^[s] y) * g (catStroke^[t] y)),
    integral_snd_kMuL p₀ g]
  exact hg s t

/-- Decay transfers across almost-everywhere equality of the observable. -/
theorem HasCorrelationDecay.congr_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} {Φ : X → X}
    {f g : X → ℝ} {ε : ℕ → ℝ} (hΦ : MeasurePreserving Φ μ μ) (hfg : f =ᵐ[μ] g)
    (hg : HasCorrelationDecay μ Φ g ε) : HasCorrelationDecay μ Φ f ε := by
  intro s t
  have hs := (hΦ.iterate s).quasiMeasurePreserving.ae_eq_comp hfg
  have ht := (hΦ.iterate t).quasiMeasurePreserving.ae_eq_comp hfg
  have hprod : (fun x => f (Φ^[s] x) * f (Φ^[t] x)) =ᵐ[μ] fun x => g (Φ^[s] x) * g (Φ^[t] x) := by
    filter_upwards [hs, ht] with x hx hx'
    simp only [Function.comp] at hx hx'
    rw [hx, hx']
  rw [integral_congr_ae hprod, integral_congr_ae hfg]
  exact hg s t

/-- ★★★ **The fibre cells decorrelate exponentially under the hyperbolic stroke.** This is the
hypothesis every finite-horizon theorem of `FibreFiniteHorizon.lean` consumed, now proved for the
corpus's hyperbolic fibre map. -/
theorem fibreStroke_hasCorrelationDecay_fibreCellInd {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) :
    HasCorrelationDecay (kMuL p₀) fibreStroke (fibreCellInd (N := N) m c)
      MeasureTheory.catRectEnv :=
  HasCorrelationDecay.congr_ae (fibreStroke_measurePreserving p₀)
    (fibreCellInd_ae_eq_rectIndR p₀ m c)
    (HasCorrelationDecay.liftSnd p₀
      (MeasureTheory.cat_hasCorrelationDecay_rectIndR (gridLo_nonneg m c.1)
        (gridLo_lt_gridHi m c.1) (gridHi_le_one m c.1) (gridLo_nonneg m c.2)
        (gridLo_lt_gridHi m c.2) (gridHi_le_one m c.2)))

/-! ### The finite-horizon theorems, unconditional -/

/-- The envelope's partial sums are bounded by `65`. -/
lemma sum_range_catRectEnv_le (T : ℕ) :
    ∑ u ∈ Finset.range T, MeasureTheory.catRectEnv u ≤ 65 := by
  have hsum : Summable (fun u : ℕ => 13 * (4 / 5 : ℝ) ^ u) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 13
  calc ∑ u ∈ Finset.range T, MeasureTheory.catRectEnv u
      ≤ ∑ u ∈ Finset.range T, 13 * (4 / 5 : ℝ) ^ u :=
        Finset.sum_le_sum fun u _ => MeasureTheory.catRectEnv_le_geometric u
    _ ≤ ∑' u : ℕ, 13 * (4 / 5 : ℝ) ^ u :=
        Summable.sum_le_tsum _ (fun u _ => by positivity) hsum
    _ = 13 * (1 - 4 / 5 : ℝ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 65 := by norm_num

/-- ★★★ **Finite-horizon equilibration of a fibre cell, unconditionally**: at horizon `T` the
mean-square deviation of the cell's time-averaged occupation from `1/(m+1)²` is at most
`130 / T`. -/
theorem integral_birkhoffAverage_fibreCellInd_sub_sq_le_hyperbolic {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) {T : ℕ} (hT : 0 < T) :
    ∫ p, (birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p
        - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2 ∂(kMuL p₀) ≤ 130 / (T : ℝ) := by
  have h := integral_birkhoffAverage_fibreCellInd_sub_sq_le p₀ m c
    ((fibreStroke_hasCorrelationDecay_fibreCellInd p₀ m c).upTo T) hT
  rw [coarseLaw_fibreCell_toReal] at h
  calc _ ≤ 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, MeasureTheory.catRectEnv u := h
    _ ≤ 2 * (T : ℝ)⁻¹ * 65 := by gcongr; exact sum_range_catRectEnv_le T
    _ = 130 / (T : ℝ) := by ring

/-- ★★★ **The time-averaged occupation of every fibre cell converges in `L²` to its Haar value**,
with no hypothesis. -/
theorem tendsto_integral_birkhoffAverage_fibreCellInd_sub_sq_hyperbolic {N : ℕ} (p₀ : CPN N)
    (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    Tendsto (fun T : ℕ => ∫ p, (birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p
        - (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal) ^ 2 ∂(kMuL p₀))
      atTop (nhds 0) :=
  tendsto_integral_birkhoffAverage_fibreCellInd_sub_sq p₀ m c
    (fibreStroke_hasCorrelationDecay_fibreCellInd p₀ m c) MeasureTheory.summable_catRectEnv

/-! ### The law at step `n`: two cells, then a coarse-grained density -/

/-- The mean of a grid rectangle on the fibre is `1/(m+1)²`. -/
lemma integral_rectIndR_grid {N : ℕ} (p₀ : CPN N) (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    ∫ y, MeasureTheory.rectIndR (gridLo m c.1) (gridHi m c.1) (gridLo m c.2) (gridHi m c.2) y
        ∂(volume : Measure KTorus)
      = (((m : ℝ) + 1) ^ 2)⁻¹ := by
  rw [← integral_snd_kMuL p₀, ← integral_congr_ae (fibreCellInd_ae_eq_rectIndR p₀ m c),
    integral_fibreCellInd, coarseLaw_fibreCell_toReal]

/-- ★★★ **Two fibre cells decorrelate at step `n`**: the joint occupation of `c'` after `n` strokes
and `c` now is within `catRectEnv n` of the product `1/(m+1)⁴`. This is the instantaneous (mixing)
statement, not a time average. -/
theorem abs_integral_fibreCellInd_iterate_mul_sub_le {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c c' : Fin (m + 1) × Fin (m + 1)) (n : ℕ) :
    |(∫ p, fibreCellInd (N := N) m c' (fibreStroke^[n] p) * fibreCellInd (N := N) m c p ∂(kMuL p₀))
        - (((m : ℝ) + 1) ^ 2)⁻¹ * (((m : ℝ) + 1) ^ 2)⁻¹|
      ≤ MeasureTheory.catRectEnv n := by
  have hΦ := (fibreStroke_measurePreserving p₀).iterate n
  have hc' := hΦ.quasiMeasurePreserving.ae_eq_comp (fibreCellInd_ae_eq_rectIndR p₀ m c')
  have hc := fibreCellInd_ae_eq_rectIndR p₀ m c
  have hprod : (fun p => fibreCellInd (N := N) m c' (fibreStroke^[n] p) * fibreCellInd (N := N) m c p)
      =ᵐ[kMuL p₀] fun p =>
        MeasureTheory.rectIndR (gridLo m c'.1) (gridHi m c'.1) (gridLo m c'.2) (gridHi m c'.2)
            (catStroke^[n] p.2)
          * MeasureTheory.rectIndR (gridLo m c.1) (gridHi m c.1) (gridLo m c.2) (gridHi m c.2) p.2 := by
    filter_upwards [hc', hc] with p hp' hp
    simp only [Function.comp, fibreStroke_iterate] at hp'
    rw [fibreStroke_iterate, hp', hp]
  rw [integral_congr_ae hprod, integral_snd_kMuL p₀ (fun y =>
      MeasureTheory.rectIndR (gridLo m c'.1) (gridHi m c'.1) (gridLo m c'.2) (gridHi m c'.2)
          (catStroke^[n] y)
        * MeasureTheory.rectIndR (gridLo m c.1) (gridHi m c.1) (gridLo m c.2) (gridHi m c.2) y)]
  have h := MeasureTheory.abs_integral_rectIndR_iterate_mul_sub_le_env (gridLo_nonneg m c'.1)
    (gridLo_lt_gridHi m c'.1) (gridHi_le_one m c'.1) (gridLo_nonneg m c'.2)
    (gridLo_lt_gridHi m c'.2) (gridHi_le_one m c'.2) (gridLo_nonneg m c.1)
    (gridLo_lt_gridHi m c.1) (gridHi_le_one m c.1) (gridLo_nonneg m c.2)
    (gridLo_lt_gridHi m c.2) (gridHi_le_one m c.2) n
  rw [integral_rectIndR_grid p₀ m c', integral_rectIndR_grid p₀ m c] at h
  exact h

/-- A density on `Σ` that is constant on the fibre cells: the coarse-grained initial distributions
of Track B. -/
noncomputable def cellDensity {N : ℕ} (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ) (p : KSigma N) :
    ℝ :=
  ∑ c, w c * fibreCellInd (N := N) m c p

lemma measurable_cellDensity {N : ℕ} (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ) :
    Measurable (cellDensity (N := N) m w) :=
  Finset.measurable_sum _ fun c _ => (measurable_fibreCellInd m c).const_mul (w c)

lemma abs_cellDensity_le {N : ℕ} (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ) (p : KSigma N) :
    |cellDensity (N := N) m w p| ≤ ∑ c, |w c| := by
  unfold cellDensity
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_fibreCellInd_le m c p)

/-- The mass the coarse-grained density puts on the cell `c'` after `n` strokes. -/
noncomputable def stepWeight {N : ℕ} (p₀ : CPN N) (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ)
    (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) : ℝ :=
  ∫ p, fibreCellInd (N := N) m c' (fibreStroke^[n] p) * cellDensity m w p ∂(kMuL p₀)

lemma integrable_fibreCellInd_iterate_mul {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c c' : Fin (m + 1) × Fin (m + 1)) (n : ℕ) :
    Integrable (fun p => fibreCellInd (N := N) m c' (fibreStroke^[n] p) * fibreCellInd (N := N) m c p)
      (kMuL p₀) := by
  refine Integrable.of_bound (((measurable_fibreCellInd m c').comp
    (measurable_fibreStroke.iterate n)).mul (measurable_fibreCellInd m c)).aestronglyMeasurable 1
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_one_of_le_one' (abs_fibreCellInd_le m c' _) (abs_nonneg _) (abs_fibreCellInd_le m c p)
  where mul_le_one_of_le_one' {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
    MeasureTheory.mul_le_one_of_le_one ha hb0 hb

/-- The step weight is the `w`-combination of the pair occupations. -/
lemma stepWeight_eq_sum {N : ℕ} (p₀ : CPN N) (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ) (n : ℕ)
    (c' : Fin (m + 1) × Fin (m + 1)) :
    stepWeight p₀ m w n c'
      = ∑ c, w c * ∫ p, fibreCellInd (N := N) m c' (fibreStroke^[n] p) * fibreCellInd (N := N) m c p
          ∂(kMuL p₀) := by
  unfold stepWeight cellDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun c _ => ((integrable_fibreCellInd_iterate_mul p₀ m c c' n).const_mul
    (w c)).congr (ae_of_all _ fun p => by ring))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun p => by ring)

/-- ★★★ **The law at step `n` of a coarse-grained density approaches the uniform cell law at the
rate of the envelope**: each cell's mass is within `(∑|w|) · catRectEnv n` of its limit
`(∑ w) / (m+1)⁴`. -/
theorem abs_stepWeight_sub_le {N : ℕ} (p₀ : CPN N) (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ)
    (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) :
    |stepWeight p₀ m w n c' - (∑ c, w c) * ((((m : ℝ) + 1) ^ 2)⁻¹ * (((m : ℝ) + 1) ^ 2)⁻¹)|
      ≤ (∑ c, |w c|) * MeasureTheory.catRectEnv n := by
  rw [stepWeight_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_integral_fibreCellInd_iterate_mul_sub_le p₀ m c c' n)
    (abs_nonneg _)

/-! ### The step-`n` law as a measure on the cells, and its divergence from uniform -/

/-- Exactly one cell contains any point: the cell indicators sum to `1`. -/
lemma sum_fibreCellInd {N : ℕ} (m : ℕ) (q : KSigma N) :
    ∑ c : Fin (m + 1) × Fin (m + 1), fibreCellInd (N := N) m c q = 1 := by
  simp [fibreCellInd_eq_ite]

lemma integrable_fibreCellInd {N : ℕ} (p₀ : CPN N) (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    Integrable (fibreCellInd (N := N) m c) (kMuL p₀) :=
  Integrable.of_bound (measurable_fibreCellInd m c).aestronglyMeasurable 1
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact abs_fibreCellInd_le m c p)

lemma integrable_fibreCellInd_iterate_mul_cellDensity {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (w : Fin (m + 1) × Fin (m + 1) → ℝ) (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) :
    Integrable (fun p => fibreCellInd (N := N) m c' (fibreStroke^[n] p) * cellDensity m w p)
      (kMuL p₀) := by
  refine Integrable.of_bound (((measurable_fibreCellInd m c').comp
    (measurable_fibreStroke.iterate n)).mul (measurable_cellDensity m w)).aestronglyMeasurable
    (∑ c, |w c|) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |fibreCellInd (N := N) m c' (fibreStroke^[n] p)| * |cellDensity m w p|
      ≤ 1 * ∑ c, |w c| :=
        mul_le_mul (abs_fibreCellInd_le m c' _) (abs_cellDensity_le m w p) (abs_nonneg _)
          zero_le_one
    _ = ∑ c, |w c| := one_mul _

lemma stepWeight_nonneg {N : ℕ} (p₀ : CPN N) (m : ℕ) {w : Fin (m + 1) × Fin (m + 1) → ℝ}
    (hw : ∀ c, 0 ≤ w c) (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) :
    0 ≤ stepWeight p₀ m w n c' :=
  integral_nonneg fun p => mul_nonneg (fibreCellInd_nonneg m c' _)
    (Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (fibreCellInd_nonneg m c p))

/-- The step weights sum to the mass of the density. -/
lemma sum_stepWeight {N : ℕ} (p₀ : CPN N) (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ) (n : ℕ) :
    ∑ c', stepWeight p₀ m w n c' = ∫ p, cellDensity (N := N) m w p ∂(kMuL p₀) := by
  unfold stepWeight
  rw [← integral_finsetSum _ (fun c' _ => integrable_fibreCellInd_iterate_mul_cellDensity p₀ m w n c')]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  beta_reduce
  rw [← Finset.sum_mul, sum_fibreCellInd, one_mul]

/-- The mass of a coarse-grained density is `(∑ w) / (m+1)²`. -/
lemma integral_cellDensity {N : ℕ} (p₀ : CPN N) (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ) :
    ∫ p, cellDensity (N := N) m w p ∂(kMuL p₀) = (∑ c, w c) * (((m : ℝ) + 1) ^ 2)⁻¹ := by
  unfold cellDensity
  rw [integral_finsetSum _ (fun c _ => (integrable_fibreCellInd p₀ m c).const_mul (w c))]
  simp_rw [integral_const_mul, integral_fibreCellInd, coarseLaw_fibreCell_toReal]
  rw [← Finset.sum_mul]

/-- The law at step `n` of the coarse-grained density, as a measure on the cells: the step weights
placed at the cells. -/
noncomputable def stepLaw {N : ℕ} (p₀ : CPN N) (m : ℕ) (w : Fin (m + 1) × Fin (m + 1) → ℝ)
    (n : ℕ) : Measure (Fin (m + 1) × Fin (m + 1)) :=
  ∑ c', ENNReal.ofReal (stepWeight p₀ m w n c') • Measure.dirac c'

theorem stepLaw_real_apply {N : ℕ} (p₀ : CPN N) (m : ℕ) {w : Fin (m + 1) × Fin (m + 1) → ℝ}
    (hw : ∀ c, 0 ≤ w c) (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) :
    (stepLaw p₀ m w n).real {c'} = stepWeight p₀ m w n c' := by
  rw [measureReal_def, stepLaw]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, mem_singleton_iff, Pi.one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact ENNReal.toReal_ofReal (stepWeight_nonneg p₀ m hw n c')

/-- The step law of a normalised nonnegative density is a probability measure. -/
theorem isProbabilityMeasure_stepLaw {N : ℕ} (p₀ : CPN N) (m : ℕ)
    {w : Fin (m + 1) × Fin (m + 1) → ℝ} (hw : ∀ c, 0 ≤ w c)
    (hnorm : ∑ c, w c = ((m : ℝ) + 1) ^ 2) (n : ℕ) :
    IsProbabilityMeasure (stepLaw p₀ m w n) := by
  constructor
  rw [stepLaw]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c' _ => stepWeight_nonneg p₀ m hw n c'), sum_stepWeight,
    integral_cellDensity, hnorm, mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]

/-- ★★★ **The divergence of the step-`n` law from the uniform cell law decays exponentially**:
for a nonnegative density constant on the cells and normalised to mass `1`,
`klDiv (stepLaw n) (uniform) ≤ (m+1)⁸ · catRectEnv n²`. This is `R-019`'s second clause at step
`n` — the instantaneous, relative-entropy statement, not a time average — for the hyperbolic fibre
map and every initial distribution coarse-grained on the same grid. -/
theorem klDiv_stepLaw_le {N : ℕ} (p₀ : CPN N) (m : ℕ) {w : Fin (m + 1) × Fin (m + 1) → ℝ}
    (hw : ∀ c, 0 ≤ w c) (hnorm : ∑ c, w c = ((m : ℝ) + 1) ^ 2) (n : ℕ) :
    klDiv (stepLaw p₀ m w n) (uniformOn (univ : Set (Fin (m + 1) × Fin (m + 1))))
      ≤ ENNReal.ofReal (((m : ℝ) + 1) ^ 8 * MeasureTheory.catRectEnv n ^ 2) := by
  have := isProbabilityMeasure_stepLaw p₀ m hw hnorm n
  have hcard : (Fintype.card (Fin (m + 1) × Fin (m + 1)) : ℝ) = ((m : ℝ) + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have h := klDiv_uniformOn_univ_le_chiSq (stepLaw p₀ m w n)
  rw [hcard] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hK : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
  have hdev : ∀ c', |(stepLaw p₀ m w n).real {c'} - (((m : ℝ) + 1) ^ 2)⁻¹|
      ≤ ((m : ℝ) + 1) ^ 2 * MeasureTheory.catRectEnv n := by
    intro c'
    rw [stepLaw_real_apply p₀ m hw n c']
    have hb := abs_stepWeight_sub_le p₀ m w n c'
    have habs : ∑ c, |w c| = ((m : ℝ) + 1) ^ 2 := by
      rw [← hnorm]; exact Finset.sum_congr rfl fun c _ => abs_of_nonneg (hw c)
    rw [hnorm, habs, show ((m : ℝ) + 1) ^ 2 * ((((m : ℝ) + 1) ^ 2)⁻¹ * (((m : ℝ) + 1) ^ 2)⁻¹)
        = (((m : ℝ) + 1) ^ 2)⁻¹ by field_simp] at hb
    exact hb
  calc ((m : ℝ) + 1) ^ 2 * ∑ c', ((stepLaw p₀ m w n).real {c'} - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2
      ≤ ((m : ℝ) + 1) ^ 2 * ∑ _c' : Fin (m + 1) × Fin (m + 1),
          (((m : ℝ) + 1) ^ 2 * MeasureTheory.catRectEnv n) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c' _ => ?_) hK.le
        calc ((stepLaw p₀ m w n).real {c'} - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2
            = |(stepLaw p₀ m w n).real {c'} - (((m : ℝ) + 1) ^ 2)⁻¹| ^ 2 := (sq_abs _).symm
          _ ≤ (((m : ℝ) + 1) ^ 2 * MeasureTheory.catRectEnv n) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hdev c') 2
    _ = ((m : ℝ) + 1) ^ 8 * MeasureTheory.catRectEnv n ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end CSD.SigmaLayer

end
