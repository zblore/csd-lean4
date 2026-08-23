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

end MeasureTheory
