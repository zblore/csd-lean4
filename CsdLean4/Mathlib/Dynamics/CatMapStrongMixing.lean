/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapMixing
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Arnold's cat map is strongly mixing on `L²(T²)`

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #147; consumed by `SigmaLayer/FibreRelaxation.lean`.

`CatMapMixing.lean` proved decay of correlations, with a rate, for the indicators of rectangles of
arcs. This file proves the statement with no rate and no restriction on the observables: for every
`f, g ∈ L²(T²)`,

  `∫ f(cat^n p) g(p) dp  ⟶  (∫ f)(∫ g)`   as `n → ∞`,

★★★ `tendsto_integral_comp_cat_iterate_mul`. That is strong mixing in its textbook form, and it is
packaged as such: ★★★ `cat_mixing : Mixing cat volume`, where `Mixing` is the predicate
`μ (f^[n] ⁻¹' s ∩ t) → μ s · μ t` for all measurable `s, t`, shaped after Mathlib's `Ergodic`
(and implying it, `Mixing.ergodic`; hence `cat_ergodic`).

## The argument

The `ε/3` argument of every textbook, with the dense class chosen to make the exact statement
trivial.

1. **Trigonometric polynomials are dense in `L²(T²)`.** Mathlib has the Fourier basis of
   `L²(Fin 2 → T)` (`UnitAddTorus.hasSum_mFourier_series_L2`); the measurable equivalence
   `finTwoArrow : (Fin 2 → T) ≃ᵐ T × T` carries Haar to Haar and the monomial `mFourier n` to the
   character `chi (n 0, n 1)`, so every `g ∈ L²(T²)` is within any `δ > 0` in energy of a finite
   combination of characters, ★★ `exists_trigPoly_integral_normSq_sub_lt`.
2. **Characters decorrelate exactly after finitely many steps.** `∫ χ_v(cat^n p) χ_w(p)` is `1` if
   `catZ^n v + w = 0` and `0` otherwise (`integral_chi_iterate_mul_chi`); for `v ≠ 0` the orbit
   `catZ^n v` leaves every bounded set (`tendsto_supNormZ_catZ_iterate_atTop`, from the
   golden-ratio growth of `CatMapMixing.lean`), so for two trigonometric polynomials the correlation
   is *equal* to the product of the means from some lag on, ★★ `eventually_integral_trigPoly_iterate_mul`.
3. **Cauchy–Schwarz pays for the rest.** With `P, Q` the approximants of `f, g` at energy `η²`,
   `fg − PQ = (f−P)g + f(g−Q) − (f−P)(g−Q)` and each piece is bounded by the product of the
   `L²` norms (`norm_integral_mul_sub_integral_mul_le`); composition with `cat^n` preserves the
   energy. The same identity on the four means gives the other side, and the total error is
   `2η(‖f‖₂ + ‖g‖₂ + η)`.

## Honest scope

* **No rate.** The theorem is convergence; the rate for a general observable depends on the
  observable (on the decay of its Fourier coefficients), and the rate for rectangles is
  `CatMapMixing.lean`'s business.
* **The concrete matrix only**, as upstream: the argument uses the growth of the frequency orbit
  and nothing else, so a general hyperbolic element of `SL₂(ℤ)` would go the same way with its own
  growth lemma; not attempted.
* `Mixing` is the two-set (strong) mixing; weak mixing and mixing of higher order are not defined.

References: Walters, *An Introduction to Ergodic Theory* (1982), Def. 1.6 and Thm. 1.28 (the
approximation argument); Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical
Systems*, §4.2 (the Fourier proof for toral automorphisms). In-corpus:
`Mathlib/Dynamics/CatMapWitness.lean` (the map and the characters),
`Mathlib/Dynamics/CatMapMixing.lean` (the growth lemma, Cauchy–Schwarz, the rate for rectangles),
`specs/BACKLOG.md` #147, `specs/residues.tsv` `R-019`.
-/

@[expose] public section

open MeasureTheory AddCircle Filter Topology
open scoped goldenRatio

/-! ### Strong mixing, as a predicate -/

/-- A map `f : α → α` is **(strongly) mixing** with respect to `μ` if it preserves `μ` and
`μ (f^[n] ⁻¹' s ∩ t) → μ s * μ t` for all measurable `s`, `t`. Shaped after `Ergodic`. -/
structure Mixing {α : Type*} [MeasurableSpace α] (f : α → α) (μ : Measure α := by volume_tac) :
    Prop extends MeasurePreserving f μ μ where
  tendsto_measure_preimage_iterate_inter ⦃s t : Set α⦄ : MeasurableSet s → MeasurableSet t →
    Tendsto (fun n : ℕ => μ (f^[n] ⁻¹' s ∩ t)) atTop (𝓝 (μ s * μ t))

/-- The identity on a null-measurability proof. With `MeasurableSet.nullMeasurableSet` it makes
`hs.nullMeasurableSet` read the same whether `hs` proves `MeasurableSet s` or
`NullMeasurableSet s μ`: Mathlib master's `PreErgodic.aeconst_set` takes the second where the pin
takes the first, and `Mixing.ergodic` is written once for both (Compat canary, 2026-10-26). -/
theorem MeasureTheory.NullMeasurableSet.nullMeasurableSet {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (h : NullMeasurableSet s μ) : NullMeasurableSet s μ := h

/-- The identity on an eventual equality. With Mathlib's `Eq.eventuallyEq` it makes
`h.eventuallyEq` read the same whether `h` proves `f = g` or `f =ᶠ[l] g`; the companion of
`MeasureTheory.NullMeasurableSet.nullMeasurableSet` for the invariance hypothesis. -/
theorem Filter.EventuallyEq.eventuallyEq {α β : Type*} {l : Filter α} {f g : α → β}
    (h : f =ᶠ[l] g) : f =ᶠ[l] g := h

/-- **A mixing map is ergodic on strictly invariant measurable sets.** A strictly invariant set
`s` has `μ (f^[n] ⁻¹' s ∩ sᶜ) = 0` at every lag, so the limit `μ s * μ sᶜ` vanishes and one
factor is zero. -/
theorem Mixing.eventuallyEmptyOrUniv_of_preimage_eq {α : Type*} [MeasurableSpace α] {f : α → α}
    {μ : Measure α} (h : Mixing f μ) {s : Set α} (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) :
    EventuallyEmptyOrUniv s (ae μ) := by
  have hlim := h.tendsto_measure_preimage_iterate_inter hs hs.compl
  have hzero : ∀ n : ℕ, μ (f^[n] ⁻¹' s ∩ sᶜ) = 0 := fun n => by
    rw [Set.preimage_iterate_eq, Function.iterate_fixed hfs n, Set.inter_compl_self,
      measure_empty]
  have hlim' : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 (μ s * μ sᶜ)) := by
    simpa only [hzero] using hlim
  have hprod : μ s * μ sᶜ = 0 := tendsto_nhds_unique hlim' tendsto_const_nhds
  rw [eventuallyEmptyOrUniv_iff']
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact Or.inl (ae_eq_empty.2 h0)
  · exact Or.inr (ae_eq_univ.2 h0)

/-- **A mixing map is ergodic.** The ergodicity condition on any set the definition hands over is
reduced to a strictly invariant measurable set almost equal to it
(`QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae`), where
`Mixing.eventuallyEmptyOrUniv_of_preimage_eq` applies. Written so that it compiles against both
forms of `PreErgodic.aeconst_set`: measurable and strictly invariant at the pin, null-measurable
and almost invariant on Mathlib master. -/
theorem Mixing.ergodic {α : Type*} [MeasurableSpace α] {f : α → α} {μ : Measure α}
    (h : Mixing f μ) : Ergodic f μ := by
  refine ⟨h.toMeasurePreserving, ⟨fun s hs hfs => ?_⟩⟩
  obtain ⟨t, ht, hts, htf⟩ :=
    h.toMeasurePreserving.quasiMeasurePreserving.exists_preimage_eq_of_preimage_ae
      hs.nullMeasurableSet (hfs.eventuallyEq (l := ae μ))
  exact (h.eventuallyEmptyOrUniv_of_preimage_eq ht htf).congr hts

namespace MeasureTheory

/-! ### Trigonometric polynomials on `T²` -/

/-- A finite combination of characters on `T²`: `∑ i ∈ S, a i • χ_{v i}`. -/
noncomputable def trigPoly {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ℤ × ℤ) :
    Torus2 → ℂ :=
  fun p => ∑ i ∈ S, a i * chi (v i) p

lemma continuous_trigPoly {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ℤ × ℤ) :
    Continuous (trigPoly S a v) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_chi (v i))

lemma norm_trigPoly_le {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ℤ × ℤ) (p : Torus2) :
    ‖trigPoly S a v p‖ ≤ ∑ i ∈ S, ‖a i‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by rw [norm_mul, norm_chi, mul_one])

lemma memLp_two_trigPoly {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ℤ × ℤ) :
    MemLp (trigPoly S a v) 2 (volume : Measure Torus2) :=
  MemLp.of_bound (continuous_trigPoly S a v).aestronglyMeasurable _
    (ae_of_all _ (norm_trigPoly_le S a v))

/-- `∫ χ_v = [v = 0]`. -/
lemma integral_chi (v : ℤ × ℤ) :
    ∫ p, chi v p ∂(volume : Measure Torus2) = if v = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [chi_zero]
  · exact integral_chi_eq_zero h

/-- The mean of a trigonometric polynomial is its constant coefficient. -/
lemma integral_trigPoly {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ℤ × ℤ) :
    ∫ p, trigPoly S a v p ∂(volume : Measure Torus2) = ∑ i ∈ S, if v i = 0 then a i else 0 := by
  unfold trigPoly
  rw [integral_finsetSum _ (fun i _ => (integrable_chi (v i)).const_mul (a i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_chi]
  split_ifs <;> simp

/-! ### Density of trigonometric polynomials in `L²(T²)`

Mathlib's Fourier basis lives on `Fin 2 → T`; `finTwoArrow` carries it to `T × T`. -/

/-- Mathlib's monomial `mFourier n` on `Fin 2 → T` is the character `chi (n 0, n 1)` on `T²`. -/
lemma mFourier_eq_chi_finTwoArrow (n : Fin 2 → ℤ) (x : Fin 2 → AddCircle (1 : ℝ)) :
    UnitAddTorus.mFourier n x = chi (n 0, n 1) (MeasurableEquiv.finTwoArrow x) := by
  show ∏ i : Fin 2, fourier (n i) (x i) = _
  rw [Fin.prod_univ_two]
  simp [chi]

/-- `finTwoArrow` carries the product of Haar measures on `Fin 2 → T` to Haar on `T²`. -/
lemma measurePreserving_finTwoArrow_haar :
    MeasurePreserving (MeasurableEquiv.finTwoArrow (α := AddCircle (1 : ℝ)))
      (Measure.pi fun _ : Fin 2 => (haarAddCircle : Measure (AddCircle (1 : ℝ))))
      (volume : Measure Torus2) := by
  have e : (haarAddCircle : Measure (AddCircle (1 : ℝ))).prod haarAddCircle
      = (volume : Measure Torus2) := by
    rw [Measure.volume_eq_prod, haarAddCircle_one_eq_volume]
  rw [← e]
  exact measurePreserving_finTwoArrow (haarAddCircle : Measure (AddCircle (1 : ℝ)))

/-- ★★ **Trigonometric polynomials are dense in `L²(T²)`**: every `L²` function is within any
`δ > 0` in energy of a finite combination of characters. Mathlib's
`UnitAddTorus.hasSum_mFourier_series_L2` on `Fin 2 → T`, transported along `finTwoArrow`. -/
theorem exists_trigPoly_integral_normSq_sub_lt {g : Torus2 → ℂ}
    (hg : MemLp g 2 (volume : Measure Torus2)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset (Fin 2 → ℤ)) (a : (Fin 2 → ℤ) → ℂ),
      ∫ p, ‖g p - trigPoly S a (fun n => (n 0, n 1)) p‖ ^ 2 ∂(volume : Measure Torus2) < δ := by
  classical
  have hpres := measurePreserving_finTwoArrow_haar
  set e := MeasurableEquiv.finTwoArrow (α := AddCircle (1 : ℝ)) with he
  set μ₂ := Measure.pi fun _ : Fin 2 => (haarAddCircle : Measure (AddCircle (1 : ℝ))) with hμ₂
  have hg' : MemLp (g ∘ e) 2 μ₂ := hg.comp_measurePreserving hpres
  set F := hg'.toLp (g ∘ e) with hF
  have hsum : Tendsto (fun s : Finset (Fin 2 → ℤ) =>
      ∑ i ∈ s, UnitAddTorus.mFourierCoeff F i • UnitAddTorus.mFourierLp 2 i) atTop (𝓝 F) :=
    UnitAddTorus.hasSum_mFourier_series_L2 (d := Fin 2) F
  obtain ⟨S, hS⟩ := Metric.tendsto_atTop.1 hsum (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
  have hdist := hS S le_rfl
  set a : (Fin 2 → ℤ) → ℂ := fun n => UnitAddTorus.mFourierCoeff F n with ha
  refine ⟨S, a, ?_⟩
  set P := trigPoly S a (fun n => (n 0, n 1)) with hP
  -- the `Lp` partial sum is almost everywhere the trigonometric polynomial pulled back
  have hae : ⇑(∑ i ∈ S, a i • UnitAddTorus.mFourierLp (d := Fin 2) 2 i) =ᵐ[μ₂]
      fun x => P (e x) := by
    filter_upwards [Lp.coeFn_finsetSum S (fun i => a i • UnitAddTorus.mFourierLp (d := Fin 2) 2 i),
      (Finset.eventually_all S).2 fun i (_ : i ∈ S) =>
        Lp.coeFn_smul (a i) (UnitAddTorus.mFourierLp (d := Fin 2) 2 i),
      (Finset.eventually_all S).2 fun i (_ : i ∈ S) =>
        UnitAddTorus.coeFn_mFourierLp (d := Fin 2) 2 i] with x hx hx' hx''
    rw [hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hx' i hi, Pi.smul_apply, smul_eq_mul, hx'' i hi, mFourier_eq_chi_finTwoArrow]
  have hsub : ⇑(∑ i ∈ S, a i • UnitAddTorus.mFourierLp (d := Fin 2) 2 i) - ⇑F =ᵐ[μ₂]
      (fun x => P (e x)) - g ∘ e := by
    filter_upwards [hae, hg'.coeFn_toLp] with x hx hx'
    rw [← hF] at hx'
    simp only [Pi.sub_apply, hx, hx']
  have hmemP : MemLp (fun x => P (e x)) 2 μ₂ :=
    (memLp_two_trigPoly S a _).comp_measurePreserving hpres
  -- the distance in `L²` is the square root of the energy of the difference
  rw [Lp.dist_def] at hdist
  have hdist' : (eLpNorm ((fun x => P (e x)) - g ∘ e) 2 μ₂).toReal < Real.sqrt δ := by
    rw [eLpNorm_congr_ae hsub.symm]
    exact hdist
  rw [(hmemP.sub hg').eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hdist'
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply, Function.comp_apply] at hdist'
  rw [ENNReal.toReal_ofReal (by positivity), ← one_div, ← Real.sqrt_eq_rpow,
    Real.sqrt_lt_sqrt_iff (integral_nonneg fun x => by positivity)] at hdist'
  -- transport the energy to `T²`
  calc ∫ p, ‖g p - P p‖ ^ 2 ∂(volume : Measure Torus2)
      = ∫ x, ‖g (e x) - P (e x)‖ ^ 2 ∂μ₂ :=
        (hpres.integral_comp' (fun p => ‖g p - P p‖ ^ 2)).symm
    _ = ∫ x, ‖P (e x) - g (e x)‖ ^ 2 ∂μ₂ := by simp_rw [norm_sub_rev]
    _ < δ := hdist'

/-! ### Characters decorrelate exactly after finitely many steps -/

lemma one_le_supNormZ {v : ℤ × ℤ} (hv : v ≠ 0) : 1 ≤ supNormZ v := by
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    exact le_trans (by exact_mod_cast Int.one_le_abs h2) (abs_snd_le_supNormZ v)
  · exact le_trans (by exact_mod_cast Int.one_le_abs h1) (abs_fst_le_supNormZ v)

/-- **The frequency orbit of a nonzero index escapes to infinity**, from the golden-ratio growth
`φ^{2n} ≤ φ³ ‖catZ^[n] v‖ ‖v‖` of `CatMapMixing.lean`. -/
theorem tendsto_supNormZ_catZ_iterate_atTop {v : ℤ × ℤ} (hv : v ≠ 0) :
    Tendsto (fun n : ℕ => supNormZ (catZ^[n] v)) atTop atTop := by
  have hv1 := one_le_supNormZ hv
  have hφ := Real.goldenRatio_pos
  have hc : 0 < 1 / (φ ^ 3 * supNormZ v) := by positivity
  refine tendsto_atTop_mono (fun n => ?_)
    ((tendsto_pow_atTop_atTop_of_one_lt
      (one_lt_pow₀ Real.one_lt_goldenRatio two_ne_zero)).const_mul_atTop hc)
  have h := goldenRatio_pow_le_supNormZ_catZ_iterate hv n
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  calc (φ ^ 2) ^ n = φ ^ (2 * n) := by rw [pow_mul]
    _ ≤ φ ^ 3 * (supNormZ (catZ^[n] v) * supNormZ v) := h
    _ = supNormZ (catZ^[n] v) * (φ ^ 3 * supNormZ v) := by ring

lemma eventually_catZ_iterate_ne {v : ℤ × ℤ} (hv : v ≠ 0) (w : ℤ × ℤ) :
    ∀ᶠ n : ℕ in atTop, catZ^[n] v ≠ w := by
  filter_upwards [(tendsto_supNormZ_catZ_iterate_atTop hv).eventually_gt_atTop (supNormZ w)]
    with n hn
  rintro h
  rw [h] at hn
  exact lt_irrefl _ hn

lemma continuous_chi_iterate_mul_chi (v w : ℤ × ℤ) (n : ℕ) :
    Continuous fun p : Torus2 => chi v (cat^[n] p) * chi w p :=
  ((continuous_chi v).comp (continuous_cat.iterate n)).mul (continuous_chi w)

lemma integrable_chi_iterate_mul_chi (v w : ℤ × ℤ) (n : ℕ) :
    Integrable (fun p : Torus2 => chi v (cat^[n] p) * chi w p) (volume : Measure Torus2) :=
  Integrable.of_bound (continuous_chi_iterate_mul_chi v w n).aestronglyMeasurable 1
    (ae_of_all _ fun p => by rw [norm_mul, norm_chi, norm_chi, mul_one])

/-- `∫ χ_v(cat^n p) χ_w(p) = [catZ^n v + w = 0]`. -/
lemma integral_chi_iterate_mul_chi (v w : ℤ × ℤ) (n : ℕ) :
    ∫ p, chi v (cat^[n] p) * chi w p ∂(volume : Measure Torus2)
      = if catZ^[n] v + w = 0 then 1 else 0 := by
  simp_rw [chi_cat_iterate, ← chi_index_add]
  exact integral_chi _

/-- ★★ **Exact decorrelation of trigonometric polynomials**: from some lag on, the correlation of
two trigonometric polynomials under the cat map *equals* the product of their means. -/
theorem eventually_integral_trigPoly_iterate_mul {ι κ : Type*} (S : Finset ι) (a : ι → ℂ)
    (v : ι → ℤ × ℤ) (T : Finset κ) (b : κ → ℂ) (w : κ → ℤ × ℤ) :
    ∀ᶠ n : ℕ in atTop,
      ∫ p, trigPoly S a v (cat^[n] p) * trigPoly T b w p ∂(volume : Measure Torus2)
        = (∫ p, trigPoly S a v p ∂(volume : Measure Torus2))
          * ∫ p, trigPoly T b w p ∂(volume : Measure Torus2) := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop, ∀ i ∈ S, ∀ j ∈ T, v i ≠ 0 → catZ^[n] (v i) ≠ -(w j) := by
    rw [Finset.eventually_all]
    intro i _
    rw [Finset.eventually_all]
    intro j _
    by_cases hvi : v i = 0
    · exact Filter.Eventually.of_forall fun n h => absurd hvi h
    · exact (eventually_catZ_iterate_ne hvi (-(w j))).mono fun n hn _ => hn
  filter_upwards [hev] with n hn
  have hint : ∀ (i : ι) (j : κ), Integrable
      (fun p : Torus2 => a i * b j * (chi (v i) (cat^[n] p) * chi (w j) p))
      (volume : Measure Torus2) :=
    fun i j => (integrable_chi_iterate_mul_chi (v i) (w j) n).const_mul _
  have hexp : ∀ p : Torus2, trigPoly S a v (cat^[n] p) * trigPoly T b w p
      = ∑ i ∈ S, ∑ j ∈ T, a i * b j * (chi (v i) (cat^[n] p) * chi (w j) p) := fun p => by
    unfold trigPoly
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul,
    integral_chi_iterate_mul_chi, integral_trigPoly, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  by_cases hvi : v i = 0
  · rw [hvi, catZ_iterate_zero, zero_add]
    simp only [ite_true]
    split_ifs <;> ring
  · have hne : catZ^[n] (v i) + w j ≠ 0 := fun h => hn i hi j hj hvi (eq_neg_of_add_eq_zero_left h)
    simp [hne, hvi]

/-! ### The `ε/3` argument -/

lemma memLp_two_comp_cat_iterate {F : Torus2 → ℂ} (hF : MemLp F 2 (volume : Measure Torus2))
    (n : ℕ) : MemLp (fun p => F (cat^[n] p)) 2 (volume : Measure Torus2) :=
  hF.comp_measurePreserving (measurePreserving_cat.iterate n)

lemma integral_normSq_comp_cat_iterate {F : Torus2 → ℂ}
    (hF : AEStronglyMeasurable F (volume : Measure Torus2)) (n : ℕ) :
    ∫ p, ‖F (cat^[n] p)‖ ^ 2 ∂(volume : Measure Torus2)
      = ∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2) :=
  integral_iterate_of_measurePreserving measurePreserving_cat
    ((continuous_pow 2).comp_aestronglyMeasurable hF.norm) n

/-- **Cauchy–Schwarz**: `‖∫ F G‖ ≤ ‖F‖₂ ‖G‖₂`. -/
lemma norm_integral_mul_le_sqrt {F G : Torus2 → ℂ} (hF : MemLp F 2 (volume : Measure Torus2))
    (hG : MemLp G 2 (volume : Measure Torus2)) :
    ‖∫ p, F p * G p ∂(volume : Measure Torus2)‖
      ≤ Real.sqrt (∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2))
        * Real.sqrt (∫ p, ‖G p‖ ^ 2 ∂(volume : Measure Torus2)) := by
  rw [← Real.sqrt_mul (integral_nonneg fun p => by positivity)]
  calc ‖∫ p, F p * G p ∂(volume : Measure Torus2)‖
      = Real.sqrt (‖∫ p, F p * G p ∂(volume : Measure Torus2)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (normSq_integral_mul_le hF hG)

/-- `‖∫ F‖ ≤ ‖F‖₂` on a probability space. -/
lemma norm_integral_le_sqrt {F : Torus2 → ℂ} (hF : MemLp F 2 (volume : Measure Torus2)) :
    ‖∫ p, F p ∂(volume : Measure Torus2)‖
      ≤ Real.sqrt (∫ p, ‖F p‖ ^ 2 ∂(volume : Measure Torus2)) := by
  have h := norm_integral_mul_le_sqrt hF (memLp_const (1 : ℂ))
  simpa using h

/-- The bilinear error identity `fg − PQ = (f−P)g + f(g−Q) − (f−P)(g−Q)`, integrated and
bounded by Cauchy–Schwarz. -/
lemma norm_integral_mul_sub_integral_mul_le {f P g Q : Torus2 → ℂ}
    (hf : MemLp f 2 (volume : Measure Torus2)) (hP : MemLp P 2 (volume : Measure Torus2))
    (hg : MemLp g 2 (volume : Measure Torus2)) (hQ : MemLp Q 2 (volume : Measure Torus2)) :
    ‖(∫ p, f p * g p ∂(volume : Measure Torus2)) - ∫ p, P p * Q p ∂(volume : Measure Torus2)‖
      ≤ Real.sqrt (∫ p, ‖f p - P p‖ ^ 2 ∂(volume : Measure Torus2))
          * Real.sqrt (∫ p, ‖g p‖ ^ 2 ∂(volume : Measure Torus2))
        + Real.sqrt (∫ p, ‖f p‖ ^ 2 ∂(volume : Measure Torus2))
          * Real.sqrt (∫ p, ‖g p - Q p‖ ^ 2 ∂(volume : Measure Torus2))
        + Real.sqrt (∫ p, ‖f p - P p‖ ^ 2 ∂(volume : Measure Torus2))
          * Real.sqrt (∫ p, ‖g p - Q p‖ ^ 2 ∂(volume : Measure Torus2)) := by
  have hfP : MemLp (fun p => f p - P p) 2 (volume : Measure Torus2) := hf.sub hP
  have hgQ : MemLp (fun p => g p - Q p) 2 (volume : Measure Torus2) := hg.sub hQ
  have h1 : Integrable (fun p => (f p - P p) * g p) (volume : Measure Torus2) :=
    hfP.integrable_mul hg
  have h2 : Integrable (fun p => f p * (g p - Q p)) (volume : Measure Torus2) :=
    hf.integrable_mul hgQ
  have h3 : Integrable (fun p => (f p - P p) * (g p - Q p)) (volume : Measure Torus2) :=
    hfP.integrable_mul hgQ
  have h12 : Integrable (fun p => (f p - P p) * g p + f p * (g p - Q p))
      (volume : Measure Torus2) := h1.add h2
  have hfg : Integrable (fun p => f p * g p) (volume : Measure Torus2) := hf.integrable_mul hg
  have hPQ : Integrable (fun p => P p * Q p) (volume : Measure Torus2) := hP.integrable_mul hQ
  have key : (∫ p, f p * g p ∂(volume : Measure Torus2))
      - ∫ p, P p * Q p ∂(volume : Measure Torus2)
      = ((∫ p, (f p - P p) * g p ∂(volume : Measure Torus2))
          + ∫ p, f p * (g p - Q p) ∂(volume : Measure Torus2))
        - ∫ p, (f p - P p) * (g p - Q p) ∂(volume : Measure Torus2) := by
    calc (∫ p, f p * g p ∂(volume : Measure Torus2))
          - ∫ p, P p * Q p ∂(volume : Measure Torus2)
        = ∫ p, f p * g p - P p * Q p ∂(volume : Measure Torus2) := (integral_sub hfg hPQ).symm
      _ = ∫ p, ((f p - P p) * g p + f p * (g p - Q p)) - (f p - P p) * (g p - Q p)
            ∂(volume : Measure Torus2) := by
          congr 1; ext p; ring
      _ = (∫ p, (f p - P p) * g p + f p * (g p - Q p) ∂(volume : Measure Torus2))
            - ∫ p, (f p - P p) * (g p - Q p) ∂(volume : Measure Torus2) := integral_sub h12 h3
      _ = _ := by rw [integral_add h1 h2]
  rw [key]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact norm_integral_mul_le_sqrt hfP hg
  · exact norm_integral_mul_le_sqrt hf hgQ
  · exact norm_integral_mul_le_sqrt hfP hgQ

/-- ★★★ **The cat map is strongly mixing on `L²(T²)`**: for every `f, g ∈ L²`,
`∫ f(cat^n p) g(p) dp → (∫ f)(∫ g)`. The `ε/3` argument through trigonometric polynomials. -/
theorem tendsto_integral_comp_cat_iterate_mul {f g : Torus2 → ℂ}
    (hf : MemLp f 2 (volume : Measure Torus2)) (hg : MemLp g 2 (volume : Measure Torus2)) :
    Tendsto (fun n : ℕ => ∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2)) atTop
      (𝓝 ((∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.sqrt (∫ p, ‖f p‖ ^ 2 ∂(volume : Measure Torus2)) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Real.sqrt (∫ p, ‖g p‖ ^ 2 ∂(volume : Measure Torus2)) :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := hB ▸ Real.sqrt_nonneg _
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (ε / (4 * (A + B + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := hη ▸ min_le_left _ _
  have hηε : η * (A + B + 1) ≤ ε / 4 := by
    have h := hη ▸ min_le_right 1 (ε / (4 * (A + B + 1)))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨S, a, hP⟩ := exists_trigPoly_integral_normSq_sub_lt hf (pow_pos hη0 2)
  obtain ⟨T, b, hQ⟩ := exists_trigPoly_integral_normSq_sub_lt hg (pow_pos hη0 2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_integral_trigPoly_iterate_mul S a (fun n => (n 0, n 1)) T b (fun n => (n 0, n 1)))
  set P := trigPoly S a (fun n => (n 0, n 1)) with hPdef
  set Q := trigPoly T b (fun n => (n 0, n 1)) with hQdef
  have hPm : MemLp P 2 (volume : Measure Torus2) := memLp_two_trigPoly _ _ _
  have hQm : MemLp Q 2 (volume : Measure Torus2) := memLp_two_trigPoly _ _ _
  have hfP : Real.sqrt (∫ p, ‖f p - P p‖ ^ 2 ∂(volume : Measure Torus2)) ≤ η :=
    ((Real.sqrt_lt' hη0).2 hP).le
  have hgQ : Real.sqrt (∫ p, ‖g p - Q p‖ ^ 2 ∂(volume : Measure Torus2)) ≤ η :=
    ((Real.sqrt_lt' hη0).2 hQ).le
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  -- the dynamical piece: `∫ f∘catⁿ · g` against `∫ P∘catⁿ · Q`
  have hfn : MemLp (fun p => f (cat^[n] p)) 2 (volume : Measure Torus2) :=
    memLp_two_comp_cat_iterate hf n
  have hPn : MemLp (fun p => P (cat^[n] p)) 2 (volume : Measure Torus2) :=
    memLp_two_comp_cat_iterate hPm n
  have h1 := norm_integral_mul_sub_integral_mul_le hfn hPn hg hQm
  have e1 : ∫ p, ‖f (cat^[n] p) - P (cat^[n] p)‖ ^ 2 ∂(volume : Measure Torus2)
      = ∫ p, ‖f p - P p‖ ^ 2 ∂(volume : Measure Torus2) :=
    integral_normSq_comp_cat_iterate (F := fun p => f p - P p) (hf.sub hPm).aestronglyMeasurable n
  have e2 : ∫ p, ‖f (cat^[n] p)‖ ^ 2 ∂(volume : Measure Torus2)
      = ∫ p, ‖f p‖ ^ 2 ∂(volume : Measure Torus2) :=
    integral_normSq_comp_cat_iterate hf.aestronglyMeasurable n
  rw [e1, e2, ← hA, ← hB] at h1
  have h1' : ‖(∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2))
      - ∫ p, P (cat^[n] p) * Q p ∂(volume : Measure Torus2)‖ ≤ η * B + A * η + η * η :=
    h1.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hfP hB0)
      (mul_le_mul_of_nonneg_left hgQ hA0)) (mul_le_mul hfP hgQ (Real.sqrt_nonneg _) hη0.le))
  -- the exact piece
  have h2 := hN n hn
  -- the static piece: the four means
  have hIf : ‖(∫ p, f p ∂(volume : Measure Torus2)) - ∫ p, P p ∂(volume : Measure Torus2)‖ ≤ η := by
    rw [← integral_sub (hf.integrable one_le_two) (hPm.integrable one_le_two)]
    exact (norm_integral_le_sqrt (hf.sub hPm)).trans hfP
  have hIg : ‖(∫ p, g p ∂(volume : Measure Torus2)) - ∫ p, Q p ∂(volume : Measure Torus2)‖ ≤ η := by
    rw [← integral_sub (hg.integrable one_le_two) (hQm.integrable one_le_two)]
    exact (norm_integral_le_sqrt (hg.sub hQm)).trans hgQ
  have hIfA : ‖∫ p, f p ∂(volume : Measure Torus2)‖ ≤ A := hA ▸ norm_integral_le_sqrt hf
  have hIgB : ‖∫ p, g p ∂(volume : Measure Torus2)‖ ≤ B := hB ▸ norm_integral_le_sqrt hg
  have h3 : ‖(∫ p, P p ∂(volume : Measure Torus2)) * (∫ p, Q p ∂(volume : Measure Torus2))
      - (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2)‖
      ≤ η * B + A * η + η * η := by
    have hid : (∫ p, P p ∂(volume : Measure Torus2)) * (∫ p, Q p ∂(volume : Measure Torus2))
        - (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2)
        = -(((∫ p, f p ∂(volume : Measure Torus2)) - ∫ p, P p ∂(volume : Measure Torus2))
              * ∫ p, g p ∂(volume : Measure Torus2))
          - ((∫ p, f p ∂(volume : Measure Torus2))
              * ((∫ p, g p ∂(volume : Measure Torus2)) - ∫ p, Q p ∂(volume : Measure Torus2)))
          + ((∫ p, f p ∂(volume : Measure Torus2)) - ∫ p, P p ∂(volume : Measure Torus2))
              * ((∫ p, g p ∂(volume : Measure Torus2)) - ∫ p, Q p ∂(volume : Measure Torus2)) := by
      ring
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_neg, norm_mul]; exact mul_le_mul hIf hIgB (norm_nonneg _) hη0.le
    · rw [norm_mul]; exact mul_le_mul hIfA hIg (norm_nonneg _) hA0
    · rw [norm_mul]; exact mul_le_mul hIf hIg (norm_nonneg _) hη0.le
  -- assemble
  calc ‖(∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2))
        - (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2)‖
      = ‖((∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2))
            - ∫ p, P (cat^[n] p) * Q p ∂(volume : Measure Torus2))
          + ((∫ p, P p ∂(volume : Measure Torus2)) * (∫ p, Q p ∂(volume : Measure Torus2))
            - (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2))‖ := by
        rw [h2]; congr 1; ring
    _ ≤ ‖(∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2))
            - ∫ p, P (cat^[n] p) * Q p ∂(volume : Measure Torus2)‖
          + ‖(∫ p, P p ∂(volume : Measure Torus2)) * (∫ p, Q p ∂(volume : Measure Torus2))
            - (∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2)‖ :=
        norm_add_le _ _
    _ ≤ (η * B + A * η + η * η) + (η * B + A * η + η * η) := add_le_add h1' h3
    _ = 2 * (η * (A + B + η)) := by ring
    _ ≤ 2 * (η * (A + B + 1)) := by gcongr
    _ ≤ 2 * (ε / 4) := by gcongr
    _ < ε := by linarith

/-- ★★★ The real-valued form of `tendsto_integral_comp_cat_iterate_mul`. -/
theorem tendsto_integral_comp_cat_iterate_mul_real {f g : Torus2 → ℝ}
    (hf : MemLp f 2 (volume : Measure Torus2)) (hg : MemLp g 2 (volume : Measure Torus2)) :
    Tendsto (fun n : ℕ => ∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2)) atTop
      (𝓝 ((∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2))) := by
  have h : Tendsto (fun n : ℕ => ∫ p, (f (cat^[n] p) : ℂ) * (g p : ℂ) ∂(volume : Measure Torus2))
      atTop (𝓝 ((∫ p, (f p : ℂ) ∂(volume : Measure Torus2))
        * ∫ p, (g p : ℂ) ∂(volume : Measure Torus2))) :=
    tendsto_integral_comp_cat_iterate_mul (hf.ofReal (K := ℂ)) (hg.ofReal (K := ℂ))
  have e : ∀ n : ℕ, (∫ p, (f (cat^[n] p) : ℂ) * (g p : ℂ) ∂(volume : Measure Torus2))
      = ((∫ p, f (cat^[n] p) * g p ∂(volume : Measure Torus2) : ℝ) : ℂ) := fun n => by
    rw [← integral_complex_ofReal]; push_cast; rfl
  have e0 : (∫ p, (f p : ℂ) ∂(volume : Measure Torus2)) * ∫ p, (g p : ℂ) ∂(volume : Measure Torus2)
      = (((∫ p, f p ∂(volume : Measure Torus2)) * ∫ p, g p ∂(volume : Measure Torus2) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_complex_ofReal, Complex.ofReal_mul]
  simp_rw [e, e0] at h
  have h' := (Complex.continuous_re.tendsto _).comp h
  simpa [Function.comp_def] using h'

lemma memLp_two_indicator_one {s : Set Torus2} (hs : MeasurableSet s) :
    MemLp (s.indicator (1 : Torus2 → ℝ)) 2 (volume : Measure Torus2) :=
  MemLp.of_bound (measurable_const.indicator hs).aestronglyMeasurable 1
    (ae_of_all _ fun p => (norm_indicator_le_norm_self _ _).trans (by simp))

/-- ★★ The set form: `vol (cat^[n] ⁻¹' s ∩ t) → vol s · vol t`, in real numbers. -/
theorem tendsto_measureReal_preimage_cat_iterate_inter {s t : Set Torus2} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    Tendsto (fun n : ℕ => (volume : Measure Torus2).real (cat^[n] ⁻¹' s ∩ t)) atTop
      (𝓝 ((volume : Measure Torus2).real s * (volume : Measure Torus2).real t)) := by
  have h := tendsto_integral_comp_cat_iterate_mul_real (memLp_two_indicator_one hs)
    (memLp_two_indicator_one ht)
  have e : ∀ n : ℕ, ∫ p, s.indicator (1 : Torus2 → ℝ) (cat^[n] p) * t.indicator 1 p
      ∂(volume : Measure Torus2) = (volume : Measure Torus2).real (cat^[n] ⁻¹' s ∩ t) := fun n => by
    rw [← integral_indicator_one ((measurable_cat.iterate n hs).inter ht)]
    congr 1; ext p
    by_cases h1 : cat^[n] p ∈ s <;> by_cases h2 : p ∈ t <;> simp [Set.indicator, h1, h2]
  simp_rw [e, integral_indicator_one hs, integral_indicator_one ht] at h
  exact h

/-- ★★★ **Arnold's cat map is strongly mixing** for Haar measure on `T²`. -/
theorem cat_mixing : Mixing cat (volume : Measure Torus2) where
  toMeasurePreserving := measurePreserving_cat
  tendsto_measure_preimage_iterate_inter s t hs ht := by
    have h := ENNReal.tendsto_ofReal (tendsto_measureReal_preimage_cat_iterate_inter hs ht)
    rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal, ofReal_measureReal] at h
    exact h.congr fun n => ofReal_measureReal

/-- The cat map is ergodic, as a corollary of mixing. -/
theorem cat_ergodic : Ergodic cat (volume : Measure Torus2) := cat_mixing.ergodic

end MeasureTheory

end
