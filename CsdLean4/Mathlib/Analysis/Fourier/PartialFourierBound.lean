/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourierMul

/-!
# The joint Schwartz seminorm bounds of the partial Fourier transform

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #173 (out of #121(ii), brick 4 of 5: the partial Fourier transform on `𝓢(ℝ × ℝ, ℂ)`).

For every `k, n` there are a finite set `s` of seminorm indices and a constant `C` with

  `‖p‖ᵏ · ‖∂ⁿ 𝓕₂K(p)‖ ≤ C · (s.sup 𝓠) K`  for every kernel `K` and every `p ∈ ℝ × ℝ`,

which is the hypothesis `SchwartzMap.mkCLM` consumes (#174). The three previous bricks reduce it to
one fact about continuous linear maps of Schwartz space:

* #171: `∂ⁿ 𝓕₂K(p)(v) = 𝓕₂(dopFin n v K)(p)`, so a derivative of `𝓕₂K` is `𝓕₂` of a Schwartz
  function `G`;
* #172: `‖p‖ᵏ ‖𝓕₂G(p)‖ ≤ ‖𝓕₂(uᵏ G)(p)‖ + (2π)⁻ᵏ ‖𝓕₂(∂_wᵏ G)(p)‖`, the weight moved onto `G`;
* #170: `‖𝓕₂H(p)‖ ≤ 4π · 𝒮(H)` for one Schwartz seminorm `𝒮`.

**The one fact**: a continuous linear map `T` of `𝓢(ℝ × ℝ, ℂ)` to itself satisfies, for every finite
sup of seminorms `s.sup 𝓠`, a bound `(s.sup 𝓠)(T K) ≤ C · (s'.sup 𝓠) K` — Mathlib's
`Seminorm.bound_of_continuous` for the continuous seminorm `(s.sup 𝓠) ∘ T` on a space whose
topology is given by the family `𝓠` (`schwartz_withSeminorms`). Applied to `uᵏ ·`, `∂_wᵏ` and the
two operators `Dop` is built from, with `Dop h` linear in `h` so that `∏ ‖vᵢ‖` factors out of
`dopFin n v`, this is the whole proof.

* ★★ `SchwartzMap.exists_seminorm_bound_clm` — **the one fact**, for any continuous linear
  endomorphism of `𝓢(ℝ × ℝ, ℂ)`;
* ★ `SchwartzMap.exists_seminorm_bound_Dop` — `(s.sup 𝓠)(Dop h K) ≤ C ‖h‖ (s'.sup 𝓠) K`;
* ★★ `SchwartzMap.exists_seminorm_bound_dopFin` — `(s.sup 𝓠)(dopFin n v K) ≤ C (∏ ‖vᵢ‖) (s'.sup 𝓠) K`;
* ★★★ `SchwartzMap.exists_bound_partialFourier` — **the joint seminorm bounds**.

## Honest scope

* The constants are existential: `Seminorm.bound_of_continuous` produces them from continuity, so
  nothing here names a `C` in terms of `k`, `n` and the Leibniz constant of #170 (which it could,
  at the cost of exporting the bounds `mkCLM` was built from). `mkCLM` asks for existence.
* Nothing is yet a `SchwartzMap`; the packaging and the `weylSymbol` identification are #174.

References: [`PartialFourierSmooth.lean`](PartialFourierSmooth.lean) (#170),
[`PartialFourierDeriv.lean`](PartialFourierDeriv.lean) (#171), [`PartialFourierMul.lean`](PartialFourierMul.lean)
(#172); Mathlib `Analysis/LocallyConvex/WithSeminorms.lean` (`Seminorm.bound_of_continuous`),
`Analysis/Distribution/SchwartzSpace/Basic.lean` (`schwartz_withSeminorms`);
`specs/BACKLOG.md` #173, #121.
-/

@[expose] public section

open MeasureTheory Set Real LineDeriv
open scoped FourierTransform NNReal

namespace SchwartzMap

local notation "𝓠" => schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ

/-! ### The one fact: continuous linear maps of Schwartz space are seminorm-bounded -/

/-- A finite sup of the Schwartz seminorms is continuous (its balls are basis sets). -/
theorem continuous_finset_sup_schwartzSeminorm (s : Finset (ℕ × ℕ)) :
    Continuous ⇑(s.sup 𝓠 : Seminorm ℂ 𝓢(ℝ × ℝ, ℂ)) :=
  Seminorm.continuous_of_forall fun _ hr =>
    (schwartz_withSeminorms ℂ (ℝ × ℝ) ℂ).hasBasis.mem_of_mem
      (SeminormFamily.basisSets_mem (p := schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ) s hr)

/-- ★★ **A continuous linear map of Schwartz space is bounded, seminorm by seminorm**: for every
finite sup of seminorms there are a finite sup and a constant controlling its composite with `T`. -/
theorem exists_seminorm_bound_clm (T : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ)) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ K : 𝓢(ℝ × ℝ, ℂ), (s.sup 𝓠) (T K) ≤ C * (s'.sup 𝓠) K := by
  have hcomp : Continuous ⇑((s.sup 𝓠).comp (T : 𝓢(ℝ × ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ × ℝ, ℂ))) := by
    have : ⇑((s.sup 𝓠).comp (T : 𝓢(ℝ × ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ × ℝ, ℂ))) = fun K => (s.sup 𝓠) (T K) := by
      funext K
      simp [Seminorm.comp_apply]
    rw [this]
    exact (continuous_finset_sup_schwartzSeminorm s).comp T.continuous
  obtain ⟨s', C, -, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ℝ × ℝ) ℂ) _ hcomp
  refine ⟨s', C, C.coe_nonneg, fun K => ?_⟩
  have h := Seminorm.le_def.1 hle K
  rw [Seminorm.comp_apply, _root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h
  simpa using h

/-! ### The first-order operator, with the direction factored out -/

/-- ★ `(s.sup 𝓠)(Dop h K) ≤ C · ‖h‖ · (s'.sup 𝓠) K`: `Dop h` is linear in `h`. -/
theorem exists_seminorm_bound_Dop (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (h : ℝ × ℝ) (K : 𝓢(ℝ × ℝ, ℂ)), (s.sup 𝓠) (Dop h K) ≤ C * ‖h‖ * (s'.sup 𝓠) K := by
  obtain ⟨s₁, C₁, hC₁, h₁⟩ :=
    exists_seminorm_bound_clm (lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ))) s
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := exists_seminorm_bound_clm (smulLeftCLM ℂ wMul) s
  refine ⟨s₁ ∪ s₂, C₁ + C₂, by positivity, fun h K => ?_⟩
  have hm₁ : (s₁.sup 𝓠) K ≤ ((s₁ ∪ s₂).sup 𝓠) K :=
    (Seminorm.le_def.1 (Finset.sup_mono Finset.subset_union_left)) K
  have hm₂ : (s₂.sup 𝓠) K ≤ ((s₁ ∪ s₂).sup 𝓠) K :=
    (Seminorm.le_def.1 (Finset.sup_mono Finset.subset_union_right)) K
  have e1 : ‖(h.1 : ℂ)‖ ≤ ‖h‖ := by rw [Complex.norm_real]; exact norm_fst_le h
  have e2 : ‖(h.2 : ℂ)‖ ≤ ‖h‖ := by rw [Complex.norm_real]; exact norm_snd_le h
  have hD : Dop h K = (h.1 : ℂ) • lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) K
      + (h.2 : ℂ) • smulLeftCLM ℂ wMul K := rfl
  calc (s.sup 𝓠) (Dop h K)
      ≤ (s.sup 𝓠) ((h.1 : ℂ) • lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) K)
        + (s.sup 𝓠) ((h.2 : ℂ) • smulLeftCLM ℂ wMul K) := by
          rw [hD]; exact map_add_le_add _ _ _
    _ = ‖(h.1 : ℂ)‖ * (s.sup 𝓠) (lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) K)
        + ‖(h.2 : ℂ)‖ * (s.sup 𝓠) (smulLeftCLM ℂ wMul K) := by
          rw [map_smul_eq_mul, map_smul_eq_mul]
    _ ≤ ‖h‖ * (C₁ * ((s₁ ∪ s₂).sup 𝓠) K) + ‖h‖ * (C₂ * ((s₁ ∪ s₂).sup 𝓠) K) :=
          add_le_add
            (mul_le_mul e1 ((h₁ K).trans (mul_le_mul_of_nonneg_left hm₁ hC₁)) (apply_nonneg _ _)
              (norm_nonneg _))
            (mul_le_mul e2 ((h₂ K).trans (mul_le_mul_of_nonneg_left hm₂ hC₂)) (apply_nonneg _ _)
              (norm_nonneg _))
    _ = (C₁ + C₂) * ‖h‖ * ((s₁ ∪ s₂).sup 𝓠) K := by ring

/-- ★★ `(s.sup 𝓠)(dopFin n v K) ≤ C · (∏ ‖vᵢ‖) · (s'.sup 𝓠) K`. -/
theorem exists_seminorm_bound_dopFin (n : ℕ) :
    ∀ s : Finset (ℕ × ℕ), ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (v : Fin n → ℝ × ℝ) (K : 𝓢(ℝ × ℝ, ℂ)),
        (s.sup 𝓠) (dopFin n v K) ≤ C * (∏ i, ‖v i‖) * (s'.sup 𝓠) K := by
  induction n with
  | zero =>
      intro s
      exact ⟨s, 1, zero_le_one, fun v K => by simp⟩
  | succ n ih =>
      intro s
      obtain ⟨s₁, C₁, hC₁, h₁⟩ := ih s
      obtain ⟨s₂, C₂, hC₂, h₂⟩ := exists_seminorm_bound_Dop s₁
      refine ⟨s₂, C₁ * C₂, by positivity, fun v K => ?_⟩
      rw [dopFin_succ, ContinuousLinearMap.comp_apply, Fin.prod_univ_castSucc]
      have hinit : ∏ i : Fin n, ‖Fin.init v i‖ = ∏ i : Fin n, ‖v (Fin.castSucc i)‖ := rfl
      calc (s.sup 𝓠) (dopFin n (Fin.init v) (Dop (v (Fin.last n)) K))
          ≤ C₁ * (∏ i, ‖Fin.init v i‖) * (s₁.sup 𝓠) (Dop (v (Fin.last n)) K) := h₁ _ _
        _ ≤ C₁ * (∏ i, ‖Fin.init v i‖) * (C₂ * ‖v (Fin.last n)‖ * (s₂.sup 𝓠) K) := by
            gcongr
            exact h₂ _ _
        _ = C₁ * C₂ * ((∏ i : Fin n, ‖v (Fin.castSucc i)‖) * ‖v (Fin.last n)‖)
            * (s₂.sup 𝓠) K := by
            rw [hinit]; ring

/-! ### The joint seminorm bounds -/

/-- ★★★ **The joint Schwartz seminorm bounds of the partial Fourier transform**: for every `k, n`
there are a finite set of seminorm indices and a constant with
`‖p‖ᵏ · ‖∂ⁿ 𝓕₂K(p)‖ ≤ C · (s.sup 𝓠) K` for all `K` and `p` — the hypothesis `SchwartzMap.mkCLM`
consumes. -/
theorem exists_bound_partialFourier (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ),
        ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (partialFourier K) p‖ ≤ C * (s.sup 𝓠) K := by
  obtain ⟨sA, CA, hCA, hA⟩ := exists_seminorm_bound_clm (mulUPow k) (Finset.Iic (2, 0))
  obtain ⟨sB, CB, hCB, hB⟩ := exists_seminorm_bound_clm (derivWPow k) (Finset.Iic (2, 0))
  obtain ⟨sD, CD, hCD, hD⟩ := exists_seminorm_bound_dopFin n (sA ∪ sB)
  refine ⟨sD, 4 * π * (CA + (2 * π)⁻¹ ^ k * CB) * CD, by positivity, fun K p => ?_⟩
  have hS0 : 0 ≤ (sD.sup 𝓠) K := apply_nonneg _ _
  have key : ∀ v : Fin n → ℝ × ℝ,
      ‖p‖ ^ k * ‖(iteratedFDeriv ℝ n (partialFourier K) p : (Fin n → ℝ × ℝ) → ℂ) v‖
        ≤ (4 * π * (CA + (2 * π)⁻¹ ^ k * CB) * CD * (sD.sup 𝓠) K) * ∏ i, ‖v i‖ := by
    intro v
    rw [iteratedFDeriv_partialFourier_apply]
    have hmA : (sA.sup 𝓠) (dopFin n v K) ≤ ((sA ∪ sB).sup 𝓠) (dopFin n v K) :=
      (Seminorm.le_def.1 (Finset.sup_mono Finset.subset_union_left)) _
    have hmB : (sB.sup 𝓠) (dopFin n v K) ≤ ((sA ∪ sB).sup 𝓠) (dopFin n v K) :=
      (Seminorm.le_def.1 (Finset.sup_mono Finset.subset_union_right)) _
    have hG := hD v K
    calc ‖p‖ ^ k * ‖partialFourier (dopFin n v K) p‖
        ≤ ‖partialFourier (mulUPow k (dopFin n v K)) p‖
          + (2 * π)⁻¹ ^ k * ‖partialFourier (derivWPow k (dopFin n v K)) p‖ :=
            norm_pow_mul_norm_partialFourier_le _ k p
      _ ≤ 4 * π * kSup (mulUPow k (dopFin n v K)) 0
          + (2 * π)⁻¹ ^ k * (4 * π * kSup (derivWPow k (dopFin n v K)) 0) := by
            gcongr <;> exact norm_partialFourier_le _ _
      _ = 4 * π * ((Finset.Iic (2, 0)).sup 𝓠 (mulUPow k (dopFin n v K)))
          + (2 * π)⁻¹ ^ k * (4 * π * ((Finset.Iic (2, 0)).sup 𝓠 (derivWPow k (dopFin n v K)))) :=
            rfl
      _ ≤ 4 * π * (CA * ((sA ∪ sB).sup 𝓠) (dopFin n v K))
          + (2 * π)⁻¹ ^ k * (4 * π * (CB * ((sA ∪ sB).sup 𝓠) (dopFin n v K))) := by
            gcongr
            · exact (hA _).trans (mul_le_mul_of_nonneg_left hmA hCA)
            · exact (hB _).trans (mul_le_mul_of_nonneg_left hmB hCB)
      _ ≤ 4 * π * (CA * (CD * (∏ i, ‖v i‖) * (sD.sup 𝓠) K))
          + (2 * π)⁻¹ ^ k * (4 * π * (CB * (CD * (∏ i, ‖v i‖) * (sD.sup 𝓠) K))) := by
            gcongr
      _ = (4 * π * (CA + (2 * π)⁻¹ ^ k * CB) * CD * (sD.sup 𝓠) K) * ∏ i, ‖v i‖ := by ring
  have hM : 0 ≤ 4 * π * (CA + (2 * π)⁻¹ ^ k * CB) * CD * (sD.sup 𝓠) K := by positivity
  have h1 : ‖(‖p‖ ^ k) • iteratedFDeriv ℝ n (partialFourier K) p‖
      ≤ 4 * π * (CA + (2 * π)⁻¹ ^ k * CB) * CD * (sD.sup 𝓠) K := by
    refine ContinuousMultilinearMap.opNorm_le_bound hM fun v => ?_
    rw [_root_.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p‖ ^ k)]
    exact key v
  rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p‖ ^ k)] at h1

end SchwartzMap

end
