/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreCellDecay
public import CsdLean4.Mathlib.Dynamics.CatMapStrongMixing

/-!
# Relaxation of a general `L²` fibre density

**Category:** 7-SigmaLayer.
BACKLOG #147 (out of #118); `R-019`.

[`FibreCellDecay.lean`](FibreCellDecay.lean) proved `R-019`'s convergence clause — the cell law
after `n` strokes approaches the uniform cell law in relative entropy — for initial densities
constant on the fibre cells, with a rate. This file removes the restriction on the density: for
**every** `L²` density on the fibre, nonnegative and normalised, the cell law after `n` strokes
converges to uniform, in relative entropy, ★★★ `tendsto_klDiv_fibreStepLaw`. No rate: the rate
of a general density depends on the density, and the rate for coarse-grained densities is the
earlier file's business.

## The argument

Nothing is new on `Σ`: the stroke acts on the fibre with the base fixed (`fibreStroke_iterate`),
the base carries mass `1` (`integral_snd_kMuL`), and a fibre cell is a set on `T²`
(`fibreCellInd_eq_torusCellInd_snd`, definitional). So the weight a cell carries after `n` strokes
is the correlation `∫ 1_{c'}(cat^n y) ϱ(y) dy` on the torus (`fibreStepWeight_eq`), and
[`Mathlib/Dynamics/CatMapStrongMixing.lean`](../Mathlib/Dynamics/CatMapStrongMixing.lean) — the
cat map is strongly mixing on `L²(T²)` — sends it to `|c'| ∫ ϱ = (m+1)⁻²`
(★★★ `tendsto_fibreStepWeight`). Finitely many cells, so the chi-squared bound of `ChiSquare.lean`
sends the relative entropy to zero.

## The results

* ★★★ `tendsto_integral_fibreStroke_iterate_mul_snd`: **the hyperbolic stroke is mixing on `Σ`
  for fibre observables**: for `f, g ∈ L²(T²)`,
  `∫ f((fibreStroke^n p).2) g(p.2) dμL → (∫ f)(∫ g)`.
* ★★★ `tendsto_fibreStepWeight`: for every `ϱ ∈ L²(T²)`, the weight of every cell after `n`
  strokes tends to `(m+1)⁻² ∫ ϱ`.
* ★★★ `tendsto_klDiv_fibreStepLaw`: **the relaxation H-theorem for a general `L²` fibre
  density**: for `ϱ ≥ 0` with `∫ ϱ = 1`, the cell law after `n` strokes (`fibreStepLaw`, a
  probability measure on the cells, `isProbabilityMeasure_fibreStepLaw`) satisfies
  `klDiv (fibreStepLaw n) (uniform) → 0`. This is `R-019`'s convergence clause with no condition
  on the initial density, for the hyperbolic fibre map.

## Honest scope

* **The map is the available hyperbolic witness, not a derived de-isolation dynamics**, exactly
  as in `FibreCellDecay.lean`: `catStroke` is `MovingFibreWitness.lean`'s cat map. That the
  physical de-isolation flow acts on the fibre by a hyperbolic map is Posit 1 (BACKLOG #19), and
  it is now the only thing `R-019` is open on.
  The relaxation H-theorem for the fibre stays on the map identification. RESIDUE(R-019)
* **Densities on the fibre coordinate.** `ϱ` is a function of `p.2`. A density on `Σ` depending
  on the base coordinate too reduces to this by integrating out the base (its fibre marginal is in
  `L²` by Jensen, the base measure being a probability measure); that reduction is not written.
* **No rate**, by design. The rate for a general density depends on the decay of its Fourier
  coefficients; `klDiv_stepLaw_le` is the rate for the coarse-grained class.
* **Unchanged:** nothing here is about the translation `kFlow`, which
  `relaxation_requires_hyperbolic_fibre` shows cannot decorrelate; the typicality posits are
  untouched.

References: `specs/BACKLOG.md` #147, #118, #18, #19; `specs/residues.tsv` `R-019`;
`Mathlib/Dynamics/CatMapStrongMixing.lean`; `Mathlib/InformationTheory/ChiSquare.lean`;
`SigmaLayer/FibreCellDecay.lean`; `SigmaLayer/FibreCellUniform.lean`;
`SigmaLayer/MovingFibreWitness.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Set Topology
open scoped ENNReal

namespace CSD.SigmaLayer

open LF4 Matrix.UnitaryGroup

/-! ### The cell indicator, read on the fibre -/

/-- The indicator of the cell `c` of the `(m+1) × (m+1)` grid, as a function on the fibre `T²`. -/
noncomputable def torusCellInd (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (y : KTorus) : ℝ :=
  Set.indicator (torusCell m ⁻¹' {c}) (fun _ => (1 : ℝ)) y

/-- The fibre cell indicator is the torus cell indicator of the fibre coordinate (definitional). -/
lemma fibreCellInd_eq_torusCellInd_snd {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1))
    (p : KSigma N) : fibreCellInd m c p = torusCellInd m c p.2 := rfl

lemma measurable_torusCellInd (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    Measurable (torusCellInd m c) :=
  measurable_const.indicator ((measurable_torusCell m) (measurableSet_singleton c))

lemma torusCellInd_nonneg (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (y : KTorus) :
    0 ≤ torusCellInd m c y :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma norm_torusCellInd_le (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (y : KTorus) :
    ‖torusCellInd m c y‖ ≤ 1 :=
  (norm_indicator_le_norm_self _ _).trans (by simp)

lemma memLp_two_torusCellInd (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    MemLp (torusCellInd m c) 2 (volume : Measure KTorus) :=
  MemLp.of_bound (measurable_torusCellInd m c).aestronglyMeasurable 1
    (ae_of_all _ (norm_torusCellInd_le m c))

lemma torusCellInd_eq_ite (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (y : KTorus) :
    torusCellInd m c y = if torusCell m y = c then (1 : ℝ) else 0 := by
  classical
  rw [torusCellInd, Set.indicator_apply]
  simp [Set.mem_preimage]

/-- Exactly one cell contains any point of the fibre. -/
lemma sum_torusCellInd (m : ℕ) (y : KTorus) :
    ∑ c : Fin (m + 1) × Fin (m + 1), torusCellInd m c y = 1 := by
  simp [torusCellInd_eq_ite]

/-- A cell has volume `(m+1)⁻²` on the fibre: `#144`'s uniform coarse law, read on `T²` through
the base (which is why a base point `p₀` appears in a statement about the torus). -/
lemma integral_torusCellInd {N : ℕ} (p₀ : CPN N) (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    ∫ y, torusCellInd m c y ∂(volume : Measure KTorus) = (((m : ℝ) + 1) ^ 2)⁻¹ := by
  rw [← integral_snd_kMuL p₀ (torusCellInd m c)]
  change ∫ p, fibreCellInd m c p ∂(kMuL p₀) = _
  rw [integral_fibreCellInd, coarseLaw_fibreCell_toReal]

/-! ### The hyperbolic stroke is mixing on `Σ` for fibre observables -/

/-- ★★★ **Mixing of the hyperbolic stroke for fibre observables**: for `f, g ∈ L²(T²)`, the
correlation `∫ f((fibreStroke^n p).2) g(p.2) dμL` tends to the product of the means. -/
theorem tendsto_integral_fibreStroke_iterate_mul_snd {N : ℕ} (p₀ : CPN N) {f g : KTorus → ℝ}
    (hf : MemLp f 2 (volume : Measure KTorus)) (hg : MemLp g 2 (volume : Measure KTorus)) :
    Tendsto (fun n : ℕ => ∫ p, f (fibreStroke^[n] p).2 * g p.2 ∂(kMuL p₀)) atTop
      (𝓝 ((∫ p, f p.2 ∂(kMuL p₀)) * ∫ p, g p.2 ∂(kMuL p₀))) := by
  have e : ∀ n : ℕ, ∫ p, f (fibreStroke^[n] p).2 * g p.2 ∂(kMuL p₀)
      = ∫ y, f (MeasureTheory.cat^[n] y) * g y ∂(volume : Measure KTorus) := fun n => by
    rw [← integral_snd_kMuL p₀ (fun y => f (MeasureTheory.cat^[n] y) * g y)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [fibreStroke_iterate, catStroke]
  simp_rw [e, integral_snd_kMuL p₀ f, integral_snd_kMuL p₀ g]
  exact MeasureTheory.tendsto_integral_comp_cat_iterate_mul_real hf hg

/-! ### The step-`n` cell law of a general fibre density -/

/-- The weight the cell `c'` carries after `n` strokes, for an initial density `ϱ` on the fibre:
`∫ 1_{c'}(fibreStroke^n p) ϱ(p.2) dμL`. -/
noncomputable def fibreStepWeight {N : ℕ} (p₀ : CPN N) (m : ℕ) (ϱ : KTorus → ℝ) (n : ℕ)
    (c' : Fin (m + 1) × Fin (m + 1)) : ℝ :=
  ∫ p, fibreCellInd m c' (fibreStroke^[n] p) * ϱ p.2 ∂(kMuL p₀)

/-- The weight is a correlation on the fibre alone. -/
lemma fibreStepWeight_eq {N : ℕ} (p₀ : CPN N) (m : ℕ) (ϱ : KTorus → ℝ) (n : ℕ)
    (c' : Fin (m + 1) × Fin (m + 1)) :
    fibreStepWeight p₀ m ϱ n c'
      = ∫ y, torusCellInd m c' (MeasureTheory.cat^[n] y) * ϱ y ∂(volume : Measure KTorus) := by
  unfold fibreStepWeight
  rw [← integral_snd_kMuL p₀ (fun y => torusCellInd m c' (MeasureTheory.cat^[n] y) * ϱ y)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [fibreStroke_iterate, fibreCellInd_eq_torusCellInd_snd, catStroke]

/-- ★★★ **Relaxation of a general `L²` fibre density, cell by cell**: the weight of every cell
after `n` strokes tends to the uniform value `(m+1)⁻² ∫ ϱ`. -/
theorem tendsto_fibreStepWeight {N : ℕ} (p₀ : CPN N) (m : ℕ) {ϱ : KTorus → ℝ}
    (hϱ : MemLp ϱ 2 (volume : Measure KTorus)) (c' : Fin (m + 1) × Fin (m + 1)) :
    Tendsto (fun n : ℕ => fibreStepWeight p₀ m ϱ n c') atTop
      (𝓝 ((((m : ℝ) + 1) ^ 2)⁻¹ * ∫ y, ϱ y ∂(volume : Measure KTorus))) := by
  simp_rw [fibreStepWeight_eq]
  have h := MeasureTheory.tendsto_integral_comp_cat_iterate_mul_real
    (memLp_two_torusCellInd m c') hϱ
  rwa [integral_torusCellInd p₀] at h

lemma integrable_torusCellInd_iterate_mul (m : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) (n : ℕ)
    {ϱ : KTorus → ℝ} (hϱ : MemLp ϱ 2 (volume : Measure KTorus)) :
    Integrable (fun y => torusCellInd m c' (MeasureTheory.cat^[n] y) * ϱ y)
      (volume : Measure KTorus) :=
  ((memLp_two_torusCellInd m c').comp_measurePreserving
    (MeasureTheory.measurePreserving_cat.iterate n)).integrable_mul hϱ

lemma fibreStepWeight_nonneg {N : ℕ} (p₀ : CPN N) (m : ℕ) {ϱ : KTorus → ℝ}
    (h0 : 0 ≤ᵐ[(volume : Measure KTorus)] ϱ) (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) :
    0 ≤ fibreStepWeight p₀ m ϱ n c' := by
  rw [fibreStepWeight_eq]
  exact integral_nonneg_of_ae (h0.mono fun y hy => mul_nonneg (torusCellInd_nonneg m c' _) hy)

/-- The step weights sum to the mass of the density. -/
lemma sum_fibreStepWeight {N : ℕ} (p₀ : CPN N) (m : ℕ) {ϱ : KTorus → ℝ}
    (hϱ : MemLp ϱ 2 (volume : Measure KTorus)) (n : ℕ) :
    ∑ c', fibreStepWeight p₀ m ϱ n c' = ∫ y, ϱ y ∂(volume : Measure KTorus) := by
  simp_rw [fibreStepWeight_eq]
  rw [← integral_finsetSum _ (fun c' _ => integrable_torusCellInd_iterate_mul m c' n hϱ)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  beta_reduce
  rw [← Finset.sum_mul, sum_torusCellInd, one_mul]

/-- The law at step `n` of the fibre density `ϱ`, as a measure on the cells. -/
noncomputable def fibreStepLaw {N : ℕ} (p₀ : CPN N) (m : ℕ) (ϱ : KTorus → ℝ) (n : ℕ) :
    Measure (Fin (m + 1) × Fin (m + 1)) :=
  ∑ c', ENNReal.ofReal (fibreStepWeight p₀ m ϱ n c') • Measure.dirac c'

theorem fibreStepLaw_real_apply {N : ℕ} (p₀ : CPN N) (m : ℕ) {ϱ : KTorus → ℝ}
    (h0 : 0 ≤ᵐ[(volume : Measure KTorus)] ϱ) (n : ℕ) (c' : Fin (m + 1) × Fin (m + 1)) :
    (fibreStepLaw p₀ m ϱ n).real {c'} = fibreStepWeight p₀ m ϱ n c' := by
  rw [measureReal_def, fibreStepLaw]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, mem_singleton_iff, Pi.one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact ENNReal.toReal_ofReal (fibreStepWeight_nonneg p₀ m h0 n c')

/-- The step law of a nonnegative density of mass `1` is a probability measure. -/
theorem isProbabilityMeasure_fibreStepLaw {N : ℕ} (p₀ : CPN N) (m : ℕ) {ϱ : KTorus → ℝ}
    (hϱ : MemLp ϱ 2 (volume : Measure KTorus)) (h0 : 0 ≤ᵐ[(volume : Measure KTorus)] ϱ)
    (hnorm : ∫ y, ϱ y ∂(volume : Measure KTorus) = 1) (n : ℕ) :
    IsProbabilityMeasure (fibreStepLaw p₀ m ϱ n) := by
  constructor
  rw [fibreStepLaw]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c' _ => fibreStepWeight_nonneg p₀ m h0 n c'),
    sum_fibreStepWeight p₀ m hϱ n, hnorm, ENNReal.ofReal_one]

/-- ★★★ **The relaxation H-theorem for a general `L²` fibre density** (`R-019`'s convergence
clause, with no condition on the initial density): for `ϱ ∈ L²(T²)` nonnegative with `∫ ϱ = 1`,
the relative entropy of the step-`n` cell law with respect to the uniform cell law tends to zero.
-/
theorem tendsto_klDiv_fibreStepLaw {N : ℕ} (p₀ : CPN N) (m : ℕ) {ϱ : KTorus → ℝ}
    (hϱ : MemLp ϱ 2 (volume : Measure KTorus)) (h0 : 0 ≤ᵐ[(volume : Measure KTorus)] ϱ)
    (hnorm : ∫ y, ϱ y ∂(volume : Measure KTorus) = 1) :
    Tendsto (fun n : ℕ => klDiv (fibreStepLaw p₀ m ϱ n)
      (uniformOn (univ : Set (Fin (m + 1) × Fin (m + 1))))) atTop (𝓝 0) := by
  have hK : (Fintype.card (Fin (m + 1) × Fin (m + 1)) : ℝ) = ((m : ℝ) + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  -- the chi-squared bound at every step
  have hbound : ∀ n : ℕ, klDiv (fibreStepLaw p₀ m ϱ n)
      (uniformOn (univ : Set (Fin (m + 1) × Fin (m + 1))))
      ≤ ENNReal.ofReal (((m : ℝ) + 1) ^ 2
          * ∑ c', (fibreStepWeight p₀ m ϱ n c' - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2) := fun n => by
    have := isProbabilityMeasure_fibreStepLaw p₀ m hϱ h0 hnorm n
    have h := klDiv_uniformOn_univ_le_chiSq (fibreStepLaw p₀ m ϱ n)
    rw [hK] at h
    simp_rw [fibreStepLaw_real_apply p₀ m h0 n] at h
    exact h
  -- every weight tends to the uniform value, so the bound tends to zero
  have hw : ∀ c', Tendsto (fun n : ℕ => fibreStepWeight p₀ m ϱ n c') atTop
      (𝓝 ((((m : ℝ) + 1) ^ 2)⁻¹)) := fun c' => by
    have h := tendsto_fibreStepWeight p₀ m hϱ c'
    rwa [hnorm, mul_one] at h
  have hsum : Tendsto (fun n : ℕ => ((m : ℝ) + 1) ^ 2
      * ∑ c', (fibreStepWeight p₀ m ϱ n c' - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2) atTop
      (𝓝 (((m : ℝ) + 1) ^ 2 * ∑ _c' : Fin (m + 1) × Fin (m + 1),
        ((((m : ℝ) + 1) ^ 2)⁻¹ - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2)) :=
    tendsto_const_nhds.mul (tendsto_finsetSum _ fun c' _ => ((hw c').sub_const _).pow 2)
  simp only [sub_self, zero_pow two_ne_zero, Finset.sum_const_zero, mul_zero] at hsum
  have hup := ENNReal.tendsto_ofReal hsum
  rw [ENNReal.ofReal_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
    hbound

end CSD.SigmaLayer

end
