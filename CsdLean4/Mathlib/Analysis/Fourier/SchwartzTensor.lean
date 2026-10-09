/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The tensor product of Schwartz functions

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #126(i), out of #122.

★★ `SchwartzMap.tensorProd` — **`(p, q) ↦ f p · g q` is Schwartz on `D₁ × D₂`** when `f` and `g` are
Schwartz on the factors. Mathlib has no such lemma, and #126 needs it: a composite integral kernel
is built from a *product* of two kernels, one variable then integrated out.

## The two ingredients

* the **Leibniz bound** `norm_iteratedFDeriv_mul_le` expands the derivatives of the product, and
  ★ `norm_iteratedFDeriv_comp_clm_le` drops each factor's derivative from the product to its own
  variable — a derivative along a continuous linear map of norm at most one is no bigger than the
  derivative of the function it is composed with, which is what the two projections are;
* the **weight splits multiplicatively**: `‖(p, q)‖ ≤ (1 + ‖p‖)·(1 + ‖q‖)`, because the product norm
  is a max. So one weight on the pair becomes one weight on each factor, and
  `SchwartzMap.one_add_le_sup_seminorm_apply` bounds each side by a `Finset.sup` of that factor's
  seminorms. The same bound then serves *every* term of the Leibniz sum, which is what keeps the
  constant short.

## Honest scope

⚠️ **Not bilinear-continuous.** `tensorProd` is a function of two Schwartz functions, not a
continuous bilinear map `𝓢(D₁, ℂ) →L 𝓢(D₂, ℂ) →L 𝓢(D₁ × D₂, ℂ)`. The estimate here is *linear in
one `Finset.sup` of each factor's seminorms*, which is what continuity in each argument separately
would need, so the stronger statement is a packaging exercise — but nothing needs it, and
`SchwartzMap.decay'` asks only that a bound exist.

⚠️ **Scalar-valued.** Both factors are `ℂ`-valued and the product is multiplication. The version for
a general bounded bilinear map is the same proof with `norm_iteratedFDeriv_clm_apply_const_le` in
place of the Leibniz bound; it is not needed here.

References: [`SchwartzPartialIntegral.lean`](SchwartzPartialIntegral.lean) (#126(ii), which consumes
this), [`WeylComposition.lean`](WeylComposition.lean) (#126(iii)(iv));
`specs/BACKLOG.md` #126, #122.
-/

@[expose] public section

open SchwartzMap

noncomputable section

variable {D₁ : Type*} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
  {D₂ : Type*} [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ★ **A derivative along a short linear map is no bigger than the derivative itself.** The two
projections of a product are short, which is how the Leibniz expansion below returns each factor's
derivative to its own variable. -/
theorem norm_iteratedFDeriv_comp_clm_le {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1) {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ℕ) (x : D) :
    ‖iteratedFDeriv ℝ i (fun y => f (L y)) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ := by
  have hcomp : (fun y => f (L y)) = f ∘ L := rfl
  rw [hcomp, L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hprod : ∏ _i : Fin i, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hL
  calc ‖iteratedFDeriv ℝ i f (L x)‖ * ∏ _i : Fin i, ‖L‖
      ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i f (L x)‖ := mul_one _

/-- Both projections of a product are short. -/
theorem norm_fst_clm_le_one : ‖ContinuousLinearMap.fst ℝ D₁ D₂‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun r => ?_
  rw [one_mul, Prod.norm_def]
  exact le_max_left _ _

theorem norm_snd_clm_le_one : ‖ContinuousLinearMap.snd ℝ D₁ D₂‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun r => ?_
  rw [one_mul, Prod.norm_def]
  exact le_max_right _ _

omit [NormedSpace ℝ D₁] [NormedSpace ℝ D₂] in
/-- The weight on a pair splits multiplicatively, because the product norm is a max. -/
theorem norm_le_one_add_mul_one_add (r : D₁ × D₂) : ‖r‖ ≤ (1 + ‖r.1‖) * (1 + ‖r.2‖) := by
  have h1 : (0 : ℝ) ≤ ‖r.1‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖r.2‖ := norm_nonneg _
  have hmax : ‖r‖ = max ‖r.1‖ ‖r.2‖ := Prod.norm_def r
  rw [hmax]
  rcases le_total ‖r.1‖ ‖r.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

/-- ★★ **The tensor product of two Schwartz functions is Schwartz.** -/
noncomputable def SchwartzMap.tensorProd (f : 𝓢(D₁, ℂ)) (g : 𝓢(D₂, ℂ)) : 𝓢(D₁ × D₂, ℂ) where
  toFun r := f r.1 * g r.2
  smooth' := by
    have hf : ContDiff ℝ (⊤ : ℕ∞) fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1 :=
      (f.smooth' : ContDiff ℝ (⊤ : ℕ∞) (f : D₁ → ℂ)).comp contDiff_fst
    have hg : ContDiff ℝ (⊤ : ℕ∞) fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2 :=
      (g.smooth' : ContDiff ℝ (⊤ : ℕ∞) (g : D₂ → ℂ)).comp contDiff_snd
    exact (hf.mul hg).of_le (by exact_mod_cast le_top)
  decay' k n := by
    classical
    obtain ⟨Sf, hSf⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ D₁ ℂ) f :=
      ⟨_, rfl⟩
    obtain ⟨Sg, hSg⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ D₂ ℂ) g :=
      ⟨_, rfl⟩
    refine ⟨∑ _i ∈ Finset.range (n + 1),
      (n.choose _i : ℝ) * (2 ^ k * Sf) * (2 ^ k * Sg), fun r => ?_⟩
    have hf : ContDiff ℝ (⊤ : ℕ∞) fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1 :=
      (f.smooth' : ContDiff ℝ (⊤ : ℕ∞) (f : D₁ → ℂ)).comp contDiff_fst
    have hg : ContDiff ℝ (⊤ : ℕ∞) fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2 :=
      (g.smooth' : ContDiff ℝ (⊤ : ℕ∞) (g : D₂ → ℂ)).comp contDiff_snd
    -- the Leibniz expansion
    have hleib := norm_iteratedFDeriv_mul_le hf hg r (n := n) (by exact_mod_cast le_top)
    -- every term of it obeys the same bound
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖r‖ ^ k * ((n.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1) r‖
            * ‖iteratedFDeriv ℝ (n - i) (fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2) r‖)
          ≤ (n.choose i : ℝ) * (2 ^ k * Sf) * (2 ^ k * Sg) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hin : i ≤ n := by omega
      have hni : n - i ≤ n := by omega
      -- drop each derivative to its own variable
      have hfi : ‖iteratedFDeriv ℝ i (fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1) r‖
          ≤ ‖iteratedFDeriv ℝ i (f : D₁ → ℂ) r.1‖ :=
        norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.fst ℝ D₁ D₂) norm_fst_clm_le_one
          (f.smooth' : ContDiff ℝ (⊤ : ℕ∞) (f : D₁ → ℂ)) i r
      have hgi : ‖iteratedFDeriv ℝ (n - i) (fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2) r‖
          ≤ ‖iteratedFDeriv ℝ (n - i) (g : D₂ → ℂ) r.2‖ :=
        norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.snd ℝ D₁ D₂) norm_snd_clm_le_one
          (g.smooth' : ContDiff ℝ (⊤ : ℕ∞) (g : D₂ → ℂ)) (n - i) r
      -- the two seminorm bounds, one per factor
      have hfs : (1 + ‖r.1‖) ^ k * ‖iteratedFDeriv ℝ i (f : D₁ → ℂ) r.1‖ ≤ 2 ^ k * Sf := by
        rw [hSf]
        exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) (le_refl k) hin f r.1
      have hgs : (1 + ‖r.2‖) ^ k * ‖iteratedFDeriv ℝ (n - i) (g : D₂ → ℂ) r.2‖ ≤ 2 ^ k * Sg := by
        rw [hSg]
        exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) (le_refl k) hni g r.2
      -- the weight splits
      have hw : ‖r‖ ^ k ≤ (1 + ‖r.1‖) ^ k * (1 + ‖r.2‖) ^ k := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg r) (norm_le_one_add_mul_one_add r) k
      calc ‖r‖ ^ k * ((n.choose i : ℝ)
              * ‖iteratedFDeriv ℝ i (fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1) r‖
              * ‖iteratedFDeriv ℝ (n - i) (fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2) r‖)
          ≤ ((1 + ‖r.1‖) ^ k * (1 + ‖r.2‖) ^ k) * ((n.choose i : ℝ)
              * ‖iteratedFDeriv ℝ i (f : D₁ → ℂ) r.1‖
              * ‖iteratedFDeriv ℝ (n - i) (g : D₂ → ℂ) r.2‖) := by
            refine mul_le_mul hw ?_ (by positivity) (by positivity)
            gcongr
        _ = (n.choose i : ℝ)
              * ((1 + ‖r.1‖) ^ k * ‖iteratedFDeriv ℝ i (f : D₁ → ℂ) r.1‖)
              * ((1 + ‖r.2‖) ^ k * ‖iteratedFDeriv ℝ (n - i) (g : D₂ → ℂ) r.2‖) := by ring
        _ ≤ (n.choose i : ℝ) * (2 ^ k * Sf) * (2 ^ k * Sg) := by
            have hSf0 : (0 : ℝ) ≤ Sf := by rw [hSf]; exact apply_nonneg _ _
            have h1 : (n.choose i : ℝ)
                  * ((1 + ‖r.1‖) ^ k * ‖iteratedFDeriv ℝ i (f : D₁ → ℂ) r.1‖)
                ≤ (n.choose i : ℝ) * (2 ^ k * Sf) :=
              mul_le_mul_of_nonneg_left hfs (by positivity)
            refine mul_le_mul h1 hgs (by positivity) ?_
            exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hSf0)
    -- assemble
    calc ‖r‖ ^ k * ‖iteratedFDeriv ℝ n (fun r : D₁ × D₂ => f r.1 * g r.2) r‖
        ≤ ‖r‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1) r‖
            * ‖iteratedFDeriv ℝ (n - i) (fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2) r‖ := by
          exact mul_le_mul_of_nonneg_left hleib (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), ‖r‖ ^ k * ((n.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (fun r : D₁ × D₂ => (f : D₁ → ℂ) r.1) r‖
            * ‖iteratedFDeriv ℝ (n - i) (fun r : D₁ × D₂ => (g : D₂ → ℂ) r.2) r‖) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 ^ k * Sf) * (2 ^ k * Sg) :=
          Finset.sum_le_sum hterm

@[simp]
theorem SchwartzMap.tensorProd_apply (f : 𝓢(D₁, ℂ)) (g : 𝓢(D₂, ℂ)) (r : D₁ × D₂) :
    SchwartzMap.tensorProd f g r = f r.1 * g r.2 := rfl

end

end
