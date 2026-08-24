/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hausdorff moment determinacy on a compact interval

**Category:** 1-Mathlib. No CSD content.

On a *compact* interval the moment sequence determines the measure. Mathlib provisions both halves
— Weierstrass (`polynomialFunctions_closure_eq_top`) and
`ext_of_forall_integral_eq_of_IsFiniteMeasure` — but does not state the conclusion, so this file
assembles it.

The argument is the elementary one: equal moments give equal integrals of polynomials by
linearity; polynomials are uniformly dense; and on a finite measure the integral is
sup-norm-Lipschitz, so equality passes to every continuous function and then to the measures.
No functional-analytic packaging is needed — just a three-term triangle inequality.

Needed by `specs/q12c-exponential-characterisation-route.md`, where the race property is turned
into a moment sequence on `[0,1]` and determinacy is what converts it back into a distributional
identity.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {a b : ℝ}

/-- A continuous function on a compact space is integrable against a finite measure. -/
lemma integrable_continuousMap (ρ : Measure (Set.Icc a b)) [IsFiniteMeasure ρ]
    (f : C(Set.Icc a b, ℝ)) : Integrable (fun x => f x) ρ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (ae_of_all _ (fun x => f.norm_coe_le_norm x))

/-- Integrals against a finite measure on a compact space are sup-norm-Lipschitz. -/
lemma abs_integral_le_norm_mul (ρ : Measure (Set.Icc a b)) [IsFiniteMeasure ρ]
    (f : C(Set.Icc a b, ℝ)) :
    |∫ x, f x ∂ρ| ≤ ‖f‖ * (ρ Set.univ).toReal := by
  have h := norm_integral_le_of_norm_le_const (μ := ρ) (C := ‖f‖)
    (ae_of_all _ (fun x => f.norm_coe_le_norm x))
  rwa [Real.norm_eq_abs] at h

/-- Equal moments give equal integrals of every polynomial. -/
lemma integral_polynomial_eq_of_moments {μ ν : Measure (Set.Icc a b)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k : ℕ, ∫ x, (x : ℝ) ^ k ∂μ = ∫ x, (x : ℝ) ^ k ∂ν) (p : Polynomial ℝ) :
    ∫ x, p.eval (x : ℝ) ∂μ = ∫ x, p.eval (x : ℝ) ∂ν := by
  have hint : ∀ (ρ : Measure (Set.Icc a b)), IsFiniteMeasure ρ → ∀ k : ℕ,
      Integrable (fun x : Set.Icc a b => (x : ℝ) ^ k) ρ := by
    intro ρ hρ k
    have := hρ
    exact integrable_continuousMap ρ
      ⟨fun x => (x : ℝ) ^ k, continuous_subtype_val.pow k⟩
  have hsum : ∀ (ρ : Measure (Set.Icc a b)), IsFiniteMeasure ρ →
      ∫ x, p.eval (x : ℝ) ∂ρ
        = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * ∫ x, (x : ℝ) ^ k ∂ρ := by
    intro ρ hρ
    have := hρ
    have hpt : ∀ x : Set.Icc a b,
        p.eval (x : ℝ) = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (x : ℝ) ^ k :=
      fun x => by rw [Polynomial.eval_eq_sum_range]
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ (fun k _ => (hint ρ hρ k).const_mul _)]
    exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
  rw [hsum μ inferInstance, hsum ν inferInstance]
  exact Finset.sum_congr rfl (fun k _ => by rw [h k])

/-- ★★ **Hausdorff moment determinacy.** Two finite Borel measures on a compact interval with the
same moment sequence are equal. -/
theorem ext_of_forall_integral_pow_eq {μ ν : Measure (Set.Icc a b)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k : ℕ, ∫ x, (x : ℝ) ^ k ∂μ = ∫ x, (x : ℝ) ^ k ∂ν) : μ = ν := by
  have hcont : ∀ f : C(Set.Icc a b, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
    intro f
    by_contra hne
    set d : ℝ := |∫ x, f x ∂μ - ∫ x, f x ∂ν| with hd
    have hdpos : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
    set M : ℝ := (μ Set.univ).toReal + (ν Set.univ).toReal + 1 with hM
    have hμnn : (0 : ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
    have hνnn : (0 : ℝ) ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
    have hMpos : 0 < M := by rw [hM]; linarith
    have hclosure : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
      rw [polynomialFunctions_closure_eq_top]
      exact Algebra.mem_top
    obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.mp hclosure (d / M) (by positivity)
    obtain ⟨p, -, rfl⟩ := hg
    have hgint : ∫ x, (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b) p) x ∂μ
        = ∫ x, (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b) p) x ∂ν := by
      have hpg : ∀ x : Set.Icc a b,
          (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b) p) x = p.eval (x : ℝ) :=
        fun x => rfl
      rw [integral_congr_ae (ae_of_all _ hpg), integral_congr_ae (ae_of_all _ hpg)]
      exact integral_polynomial_eq_of_moments h p
    set g : C(Set.Icc a b, ℝ) := Polynomial.toContinuousMapOnAlgHom (Set.Icc a b) p with hgdef
    have hfg : ‖f - g‖ < d / M := by rwa [dist_eq_norm] at hgf
    have hnorm_nn : (0 : ℝ) ≤ ‖f - g‖ := norm_nonneg _
    have hbμ : |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ ‖f - g‖ * (μ Set.univ).toReal := by
      rw [← integral_sub (integrable_continuousMap μ f) (integrable_continuousMap μ g)]
      exact abs_integral_le_norm_mul μ (f - g)
    have hbν : |∫ x, f x ∂ν - ∫ x, g x ∂ν| ≤ ‖f - g‖ * (ν Set.univ).toReal := by
      rw [← integral_sub (integrable_continuousMap ν f) (integrable_continuousMap ν g)]
      exact abs_integral_le_norm_mul ν (f - g)
    have key : d ≤ ‖f - g‖ * (μ Set.univ).toReal + ‖f - g‖ * (ν Set.univ).toReal := by
      have htri : |∫ x, f x ∂μ - ∫ x, f x ∂ν|
          ≤ |∫ x, f x ∂μ - ∫ x, g x ∂μ| + |∫ x, f x ∂ν - ∫ x, g x ∂ν| := by
        have hrw : ∫ x, f x ∂μ - ∫ x, f x ∂ν
            = (∫ x, f x ∂μ - ∫ x, g x ∂μ) - (∫ x, f x ∂ν - ∫ x, g x ∂ν) := by
          rw [hgint]; ring
        rw [hrw]
        exact abs_sub _ _
      rw [hd]
      linarith [htri, hbμ, hbν]
    have hsum_lt : (μ Set.univ).toReal + (ν Set.univ).toReal < M := by rw [hM]; linarith
    have h1' : ‖f - g‖ * ((μ Set.univ).toReal + (ν Set.univ).toReal)
        ≤ (d / M) * ((μ Set.univ).toReal + (ν Set.univ).toReal) :=
      mul_le_mul_of_nonneg_right hfg.le (by linarith)
    have h2' : (d / M) * ((μ Set.univ).toReal + (ν Set.univ).toReal) < (d / M) * M :=
      mul_lt_mul_of_pos_left hsum_lt (by positivity)
    have h3' : (d / M) * M = d := div_mul_cancel₀ _ hMpos.ne'
    nlinarith [key, h1', h2', h3']
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  exact hcont f.toContinuousMap

/-! ### The form actually used: measures on `ℝ` concentrated on the interval

The subtype statement above is the natural one to prove but an awkward one to apply, since the
laws one meets in practice are laws of `[a,b]`-valued random variables and so live on `ℝ`. This
transfers it. -/

theorem ext_of_forall_integral_pow_eq_of_null_compl {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (hν : ν (Set.Icc a b)ᶜ = 0)
    (h : ∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) : μ = ν := by
  have hmeas : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have hemb : MeasurableEmbedding ((↑) : Set.Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe hmeas
  -- the comaps are finite
  have hfin : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ →
      IsFiniteMeasure (Measure.comap ((↑) : Set.Icc a b → ℝ) ρ) := by
    intro ρ hρ
    have := hρ
    refine ⟨?_⟩
    rw [hemb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top ρ _)
  have hfinμ := hfin μ inferInstance
  have hfinν := hfin ν inferInstance
  -- each measure is the pushforward of its comap
  have hback : ∀ ρ : Measure ℝ, ρ (Set.Icc a b)ᶜ = 0 →
      (Measure.comap ((↑) : Set.Icc a b → ℝ) ρ).map (↑) = ρ := by
    intro ρ hρ
    rw [map_comap_subtype_coe hmeas]
    exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hρ)
  -- moments transfer through the embedding
  have hmom : ∀ (ρ : Measure ℝ), ρ (Set.Icc a b)ᶜ = 0 → ∀ k : ℕ,
      ∫ x : Set.Icc a b, (x : ℝ) ^ k ∂(Measure.comap ((↑) : Set.Icc a b → ℝ) ρ)
        = ∫ x, x ^ k ∂ρ := by
    intro ρ hρ k
    rw [← hemb.integral_map (fun y : ℝ => y ^ k), hback ρ hρ]
  refine (hback μ hμ) ▸ (hback ν hν) ▸ ?_
  congr 1
  have := hfinμ
  have := hfinν
  exact ext_of_forall_integral_pow_eq (fun k => by
    rw [hmom μ hμ k, hmom ν hν k, h k])

/-! ### ★ Continuous functions determined by their moments against powers

The form the `Q12-c2` route actually needs, and the one that dissolves its step-3′ fork: no
monotone-rearrangement argument and no two-dimensional determinacy, just the same Weierstrass
density argument run against a *fixed* continuous weight. -/

/-- The `k`-th coordinate power, bundled. -/
def coordPow (k : ℕ) : C(Set.Icc a b, ℝ) :=
  ⟨fun x => (x : ℝ) ^ k, continuous_subtype_val.pow k⟩

@[simp] lemma coordPow_apply (k : ℕ) (x : Set.Icc a b) : coordPow k x = (x : ℝ) ^ k := rfl

lemma integrable_mul_continuousMap (ρ : Measure (Set.Icc a b)) [IsFiniteMeasure ρ]
    (f g : C(Set.Icc a b, ℝ)) : Integrable (fun x => f x * g x) ρ := by
  have h := integrable_continuousMap ρ (f * g)
  simpa using h

lemma integrable_mul_pow (ρ : Measure (Set.Icc a b)) [IsFiniteMeasure ρ]
    (f : C(Set.Icc a b, ℝ)) (k : ℕ) :
    Integrable (fun x : Set.Icc a b => f x * (x : ℝ) ^ k) ρ :=
  integrable_mul_continuousMap ρ f (coordPow k)

/-- A continuous function orthogonal to every power is orthogonal to every polynomial. -/
lemma integral_mul_polynomial_eq_zero {ρ : Measure (Set.Icc a b)} [IsFiniteMeasure ρ]
    {d : C(Set.Icc a b, ℝ)} (h : ∀ k : ℕ, ∫ x, d x * (x : ℝ) ^ k ∂ρ = 0) (p : Polynomial ℝ) :
    ∫ x, d x * p.eval (x : ℝ) ∂ρ = 0 := by
  have hpt : ∀ x : Set.Icc a b,
      d x * p.eval (x : ℝ)
        = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (d x * (x : ℝ) ^ k) := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_finsetSum _ (fun k _ => (integrable_mul_pow ρ d k).const_mul _)]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [integral_const_mul, h k, mul_zero]

/-- ★★ **Two continuous functions with the same moments against all powers are equal.**

`IsOpenPosMeasure` is what upgrades "equal almost everywhere" to "equal", and it is exactly what a
measure with full support on the interval provides. -/
theorem eq_of_forall_integral_mul_pow_eq {μ : Measure (Set.Icc a b)}
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {f g : C(Set.Icc a b, ℝ)}
    (h : ∀ k : ℕ, ∫ x, f x * (x : ℝ) ^ k ∂μ = ∫ x, g x * (x : ℝ) ^ k ∂μ) : f = g := by
  set d : C(Set.Icc a b, ℝ) := f - g with hddef
  have hdapp : ∀ x : Set.Icc a b, d x = f x - g x := fun x => rfl
  -- `d` is orthogonal to every power, hence to every polynomial
  have hpow : ∀ k : ℕ, ∫ x, d x * (x : ℝ) ^ k ∂μ = 0 := by
    intro k
    have hpt : ∀ x : Set.Icc a b,
        d x * (x : ℝ) ^ k = f x * (x : ℝ) ^ k - g x * (x : ℝ) ^ k := by
      intro x; rw [hdapp]; ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_sub (integrable_mul_pow μ f k) (integrable_mul_pow μ g k), h k, sub_self]
  -- hence `∫ d² = 0`, by uniform approximation
  have hsq : ∫ x, d x * d x ∂μ = 0 := by
    by_contra hne
    set e : ℝ := |∫ x, d x * d x ∂μ| with hedef
    have hepos : 0 < e := abs_pos.mpr hne
    have hμnn : (0 : ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
    set K : ℝ := ‖d‖ * (μ Set.univ).toReal + 1 with hKdef
    have hKpos : 0 < K := by
      have : (0 : ℝ) ≤ ‖d‖ * (μ Set.univ).toReal := mul_nonneg (norm_nonneg _) hμnn
      rw [hKdef]; linarith
    have hclosure : d ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
      rw [polynomialFunctions_closure_eq_top]; exact Algebra.mem_top
    obtain ⟨q, hq, hdq⟩ := Metric.mem_closure_iff.mp hclosure (e / K) (by positivity)
    obtain ⟨p, -, rfl⟩ := hq
    set q : C(Set.Icc a b, ℝ) := Polynomial.toContinuousMapOnAlgHom (Set.Icc a b) p with hqdef
    have hqp : ∀ x : Set.Icc a b, q x = p.eval (x : ℝ) := fun x => rfl
    have hdqn : ‖d - q‖ < e / K := by rwa [dist_eq_norm] at hdq
    -- split `d² = d·(d − q) + d·q`, the second term vanishing
    have hzero : ∫ x, d x * q x ∂μ = 0 := by
      rw [integral_congr_ae (ae_of_all _ (fun x => by rw [hqp]))]
      exact integral_mul_polynomial_eq_zero hpow p
    have hsplit : ∫ x, d x * d x ∂μ = ∫ x, d x * (d x - q x) ∂μ := by
      have hpt : ∀ x : Set.Icc a b, d x * d x = d x * (d x - q x) + d x * q x := by
        intro x; ring
      have hdq_int : Integrable (fun x : Set.Icc a b => d x * (d x - q x)) μ :=
        integrable_mul_continuousMap μ d (d - q)
      rw [integral_congr_ae (ae_of_all _ hpt),
        integral_add hdq_int (integrable_mul_continuousMap μ d q), hzero, add_zero]
    have hbd : |∫ x, d x * (d x - q x) ∂μ| ≤ (‖d‖ * ‖d - q‖) * (μ Set.univ).toReal := by
      have hpt : ∀ x : Set.Icc a b, ‖d x * (d x - q x)‖ ≤ ‖d‖ * ‖d - q‖ := by
        intro x
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact d.norm_coe_le_norm x)
          (by rw [← Real.norm_eq_abs]; exact (d - q).norm_coe_le_norm x)
          (abs_nonneg _) (norm_nonneg _)
      have := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hpt)
      rwa [Real.norm_eq_abs] at this
    rw [hsplit] at hedef
    have hlt : (‖d‖ * ‖d - q‖) * (μ Set.univ).toReal < e := by
      have h1 : ‖d‖ * ‖d - q‖ * (μ Set.univ).toReal
          ≤ ‖d‖ * (e / K) * (μ Set.univ).toReal := by
        have := mul_le_mul_of_nonneg_left hdqn.le (norm_nonneg d)
        exact mul_le_mul_of_nonneg_right this hμnn
      have h2 : ‖d‖ * (e / K) * (μ Set.univ).toReal = (e / K) * (‖d‖ * (μ Set.univ).toReal) := by
        ring
      have h3 : ‖d‖ * (μ Set.univ).toReal < K := by rw [hKdef]; linarith
      have h4 : (e / K) * (‖d‖ * (μ Set.univ).toReal) < (e / K) * K :=
        mul_lt_mul_of_pos_left h3 (by positivity)
      have h5 : (e / K) * K = e := div_mul_cancel₀ _ hKpos.ne'
      linarith [h1, h2 ▸ h1, h4, h5]
    rw [hedef] at hepos
    linarith [hbd, hlt, le_abs_self (∫ x, d x * (d x - q x) ∂μ)]
  -- a nonnegative continuous function with zero integral vanishes
  have hdz : d = 0 := by
    have hnn : (0 : Set.Icc a b → ℝ) ≤ fun x => d x * d x := fun x => mul_self_nonneg _
    have hae := (integral_eq_zero_iff_of_nonneg hnn
      (integrable_mul_continuousMap μ d d)).mp hsq
    have hcont : Continuous (fun x : Set.Icc a b => d x * d x) := d.continuous.mul d.continuous
    have heq : (fun x : Set.Icc a b => d x * d x) = fun _ => (0 : ℝ) :=
      (hcont.ae_eq_iff_eq μ continuous_const).mp hae
    ext x
    have := congrFun heq x
    simpa [mul_self_eq_zero] using this
  have : f - g = 0 := hdz
  rwa [sub_eq_zero] at this

/-! ### The carrier: Lebesgue measure on a compact interval

Mathlib has no `MeasureSpace` instance on the subtype `Set.Icc a b`, so the measure the results
above are stated against has to be built. It is the comap of `volume`, and it has the two
properties they need: finiteness, and full support (which is what turns "equal almost everywhere"
into "equal"). -/

/-- Lebesgue measure on a compact interval, as a measure on the subtype. -/
noncomputable def intervalMeasure (a b : ℝ) : Measure (Set.Icc a b) :=
  Measure.comap Subtype.val volume

instance instIsFiniteMeasureIntervalMeasure (a b : ℝ) : IsFiniteMeasure (intervalMeasure a b) := by
  refine ⟨?_⟩
  rw [intervalMeasure, (MeasurableEmbedding.subtype_coe (measurableSet_Icc (a := a) (b := b)))
    |>.comap_apply]
  exact lt_of_le_of_lt (measure_mono (by rintro y ⟨z, -, rfl⟩; exact z.2)) measure_Icc_lt_top

/-- On a **nondegenerate** interval the measure has full support, which is what upgrades
"equal almost everywhere" to "equal". -/
lemma isOpenPosMeasure_intervalMeasure {a b : ℝ} (hab : a < b) :
    (intervalMeasure a b).IsOpenPosMeasure := by
  refine ⟨fun U hU hne hzero => ?_⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hxV : (x : ℝ) ∈ V := by rw [← hVU] at hx; exact hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV _ hxV
  -- a nondegenerate subinterval of `Icc a b` inside the ball
  have hxab : (x : ℝ) ∈ Set.Icc a b := x.2
  obtain ⟨u, v, huv, hsub⟩ :
      ∃ u v : ℝ, u < v ∧ Set.Ioo u v ⊆ Metric.ball (x : ℝ) ε ∩ Set.Icc a b := by
    refine ⟨max a ((x : ℝ) - ε / 2), min b ((x : ℝ) + ε / 2), ?_, ?_⟩
    · refine max_lt (lt_min hab (by linarith [hxab.1])) (lt_min ?_ (by linarith))
      linarith [hxab.2]
    · rintro y ⟨hy1, hy2⟩
      have hya : a < y := lt_of_le_of_lt (le_max_left _ _) hy1
      have hyb : y < b := lt_of_lt_of_le hy2 (min_le_left _ _)
      have hy1' : (x : ℝ) - ε / 2 < y := lt_of_le_of_lt (le_max_right _ _) hy1
      have hy2' : y < (x : ℝ) + ε / 2 := lt_of_lt_of_le hy2 (min_le_right _ _)
      refine ⟨?_, ⟨hya.le, hyb.le⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
  -- that subinterval has positive Lebesgue measure, contradicting `hzero`
  have himg : Set.Ioo u v ⊆ Subtype.val '' U := by
    intro y hy
    obtain ⟨hyb, hyI⟩ := hsub hy
    refine ⟨⟨y, hyI⟩, ?_, rfl⟩
    rw [← hVU]
    exact hball hyb
  have hUimg : (intervalMeasure a b) U = volume (Subtype.val '' U) := by
    rw [intervalMeasure,
      (MeasurableEmbedding.subtype_coe (measurableSet_Icc (a := a) (b := b))).comap_apply]
  rw [hUimg] at hzero
  have : volume (Set.Ioo u v) = 0 := measure_mono_null himg hzero
  rw [Real.volume_Ioo] at this
  simp only [ENNReal.ofReal_eq_zero, tsub_le_iff_right, zero_add] at this
  linarith

end MeasureTheory
