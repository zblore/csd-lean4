/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.ODE.FlowDerivative

/-!
# Smooth dependence of a flow on its initial point

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #60, the
`C^k` half of Darboux's theorem.

`FlowDerivative.lean` proves that the flow of a `C¹` time-dependent field is differentiable in
the initial point, with derivative the solution `Y` of the variational equation
`Y' = D(f t)(α x t) ∘ Y`. This file proves **`C^k` dependence for a `C^k` field**, by induction
on `k` through the **pair flow**: `(x, Z) ↦ (α x t, Y x t ∘ Z)` is the flow of the field
`G t (z, Z) = (f t z, D(f t)(z) ∘ Z)` on `E × (E →L E)`, which is `C^{k−1}` when `f` is `C^k`;
the induction hypothesis applied to it makes `x ↦ Y x t = D(α · t)(x)` of class `C^{k−1}`, so
`α · t` is `C^k`. The linear ODE solutions it needs on the whole time interval are
`exists_linearODE_solution_Icc`.

* `hasFDerivAt_of_contDiffOn_uncurry` — the partial derivative of a jointly `C¹` field,
  `D(f t)(z) = D(↿f)(t, z) ∘ inr`;
* `exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry` — an open neighbourhood of a compact on
  which a jointly `C¹` field has the differentiability and joint continuity of `D(f t)` that
  `hasFDerivAt_flow_of_variational_timeDependent` asks for (the tube lemma);
* ★ `exists_variational_of_lipschitz` — **`C¹` dependence in Lipschitz form**: a flow of a jointly
  `C¹` field on an open set of initial points, confined to a compact and Lipschitz in the initial
  point, is differentiable in the initial point with derivative the variational solution, and
  that derivative is continuous in the initial point;
* ★★ `contDiffOn_flow_of_contDiffOn` — **`C^n` dependence**: if the field is jointly `C^n` on an
  open set (`n ≤ ∞`) and the flow is confined to a compact convex set and Lipschitz in the
  initial point, the time-`t` map is `C^n` on the open set of initial points.

Mathlib at the pin has Picard–Lindelöf (existence, uniqueness, Lipschitz dependence) and no
differentiable or smooth dependence on the initial point. References: P. Hartman, *Ordinary
Differential Equations*, Ch. V (Thm 3.1, 4.1); S. Lang, *Real and Functional Analysis*, XIV §3;
`Analysis/ODE/FlowDerivative.lean`; `Geometry/Manifold/Darboux.lean`; `specs/BACKLOG.md` #60.
-/

@[expose] public section

open Set Metric Filter Topology
open scoped NNReal ContDiff

universe u

section Partial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative of a jointly `C¹` field: `D(f t)(z) = D(↿f)(t, z) ∘ inr`. -/
theorem hasFDerivAt_of_contDiffOn_uncurry {f : ℝ → E → E} {V : Set (ℝ × E)} (hV : IsOpen V)
    {n : WithTop ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n (Function.uncurry f) V) {t : ℝ} {z : E}
    (hp : (t, z) ∈ V) :
    HasFDerivAt (f t) (fderiv ℝ (Function.uncurry f) (t, z) ∘L ContinuousLinearMap.inr ℝ ℝ E) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (t, z) :=
    (hf.differentiableOn (lt_of_lt_of_le zero_lt_one hn).ne').differentiableAt (hV.mem_nhds hp)
  exact hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right t z)

/-- On an open neighbourhood `U` of a compact `K` with `[0, T] × K` inside the open set where the
field is jointly `C¹`, the field is differentiable in `z` with `(t, z) ↦ D(f t)(z)` continuous —
the hypotheses of `hasFDerivAt_flow_of_variational_timeDependent`. -/
theorem exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry {f : ℝ → E → E} {V : Set (ℝ × E)}
    (hV : IsOpen V) {n : WithTop ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n (Function.uncurry f) V)
    {T : ℝ} {K : Set E} (hK : IsCompact K) (hKV : Icc 0 T ×ˢ K ⊆ V) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ Icc 0 T ×ˢ U ⊆ V ∧
      (∀ t ∈ Icc 0 T, ∀ z ∈ U, HasFDerivAt (f t) (fderiv ℝ (f t) z) z) ∧
      ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Icc 0 T ×ˢ U) := by
  obtain ⟨u, U, -, hU, hIu, hKU, huV⟩ := generalized_tube_lemma isCompact_Icc hK hV hKV
  have hsub : Icc 0 T ×ˢ U ⊆ V := (prod_mono hIu subset_rfl).trans huV
  have hDc' : ContinuousOn (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry f) p ∘L ContinuousLinearMap.inr ℝ ℝ E) (Icc 0 T ×ˢ U) :=
    ((hf.continuousOn_fderiv_of_isOpen hV hn).mono hsub).clm_comp continuousOn_const
  refine ⟨U, hU, hKU, hsub, fun t ht z hz =>
    (hasFDerivAt_of_contDiffOn_uncurry hV hn hf (hsub ⟨ht, hz⟩)).differentiableAt.hasFDerivAt,
    hDc'.congr fun p hp => ?_⟩
  obtain ⟨t, z⟩ := p
  exact (hasFDerivAt_of_contDiffOn_uncurry hV hn hf (hsub hp)).fderiv

end Partial

section C1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- ★ **`C¹` dependence of a flow on the initial point, in Lipschitz form.** Let `f t` be
differentiable on an open `U` for `t ∈ [0, T]` with `(t, z) ↦ D(f t)(z)` continuous and bounded by
`M` on a compact `K ⊆ U`, and let `α` be a flow of `f` on an open set `S` of initial points,
confined to `K` and Lipschitz in the initial point uniformly in time. Then there is `Y` with
`Y x 0 = 1`, solving the variational equation along the curve of `x`, such that `α · t` is
differentiable at every `x ∈ S` with derivative `Y x t`, and `x ↦ Y x t` is continuous on `S`.
(The variational solution exists on all of `[0, T]` by `exists_linearODE_solution_Icc`; the
continuity is `dist_le_of_linearODE_coeff_close` with the uniform continuity of `D(f t)` on
`[0, T] × K` and the Lipschitz separation of trajectories.) -/
theorem exists_variational_of_lipschitz {f : ℝ → E → E} {U : Set E} (hU : IsOpen U) {T : ℝ}
    (hT : 0 < T) (hfd : ∀ t ∈ Icc 0 T, ∀ z ∈ U, HasFDerivAt (f t) (fderiv ℝ (f t) z) z)
    (hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Icc 0 T ×ˢ U))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {α : E → ℝ → E} {S : Set E} (hS : IsOpen S)
    (hα0 : ∀ x ∈ S, α x 0 = x)
    (hαd : ∀ x ∈ S, ∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f t (α x t)) (Icc 0 T) t)
    (hαK : ∀ x ∈ S, ∀ t ∈ Icc 0 T, α x t ∈ K) {L' : ℝ≥0}
    (hlip : ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) S) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Icc 0 T, ∀ z ∈ K, ‖fderiv ℝ (f t) z‖ ≤ M) :
    ∃ Y : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ S, Y x 0 = 1 ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (Y x) (fderiv ℝ (f t) (α x t) ∘L Y x t) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, HasFDerivAt (α · t) (Y x t) x) ∧
      ∀ t ∈ Icc 0 T, ContinuousOn (fun x => Y x t) S := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcontα : ∀ x ∈ S, ContinuousOn (α x) (Icc 0 T) := fun x hx t ht =>
    (hαd x hx t ht).continuousWithinAt
  -- the variational equation along each curve, on all of `[0, T]`
  have hlin : ∀ x ∈ S, ∃ Y : ℝ → E →L[ℝ] E, Y 0 = 1 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (fderiv ℝ (f t) (α x t) ∘L Y t) (Icc 0 T) t := by
    intro x hx
    have hA : ∀ Z : E →L[ℝ] E, ContinuousOn
        (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t)) Z) (Icc 0 T) := by
      intro Z
      simp only [ContinuousLinearMap.compL_apply]
      have hD : ContinuousOn (fun t => fderiv ℝ (f t) (α x t)) (Icc 0 T) :=
        hDc.comp (continuousOn_id.prodMk (hcontα x hx)) fun t ht => ⟨ht, hKU (hαK x hx t ht)⟩
      exact hD.clm_comp continuousOn_const
    have hAM : ∀ t ∈ Icc (0 : ℝ) T,
        ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t))‖ ≤ M := by
      intro t ht
      calc ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t))‖
          ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖fderiv ℝ (f t) (α x t)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * M := by
            gcongr
            · exact ContinuousLinearMap.norm_compL_le ℝ E E E
            · exact hM t ht _ (hαK x hx t ht)
        _ = M := one_mul M
    obtain ⟨Y, hY0, hY⟩ := exists_linearODE_solution_Icc
      (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t))) hT hM0 hA hAM 1
    exact ⟨Y, hY0, fun t ht => by simpa [ContinuousLinearMap.compL_apply] using hY t ht⟩
  choose Y hY using hlin
  set Y' : E → ℝ → E →L[ℝ] E := fun x => if hx : x ∈ S then Y x hx else fun _ => 1
  have hYx : ∀ x (hx : x ∈ S), Y' x = Y x hx := fun x hx => by simp only [Y', dif_pos hx]
  refine ⟨Y', fun x hx => ?_, ?_⟩
  · rw [hYx x hx]
    refine ⟨(hY x hx).1, (hY x hx).2, ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hx
    have hρ0 : 0 < ε / 2 := by positivity
    have hcb : closedBall x (ε / 2) ⊆ S := (closedBall_subset_ball (by linarith)).trans hball
    exact hasFDerivAt_flow_of_variational_timeDependent hU hT hfd hDc hK hKU hρ0
      (fun y hy => hα0 y (hcb hy)) (fun y hy t ht => hαd y (hcb hy) t ht)
      (fun y hy t ht => hαK y (hcb hy) t ht) (L' := L') (fun t ht => (hlip t ht).mono hcb)
      (hY x hx).1 (hY x hx).2
  · -- continuous dependence on the initial point
    have hunif : UniformContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
        (Icc (0 : ℝ) T ×ˢ K) :=
      (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous
        (hDc.mono (prod_mono subset_rfl hKU))
    have hAM : ∀ z ∈ S, ∀ s ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (f s) (α z s)‖ ≤ M :=
      fun z hz s hs => hM s hs _ (hαK z hz s hs)
    intro t ht
    rw [Metric.continuousOn_iff]
    intro x hx ε hε
    set C : ℝ := Real.exp (M * T) * (T * Real.exp (M * T)) with hC
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    set ε₁ : ℝ := ε / (2 * (C + 1)) with hε₁
    have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
    obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.uniformContinuousOn_iff.mp hunif ε₁ hε₁0
    refine ⟨δ₁ / ((L' : ℝ) + 1), by positivity, fun y hy hyx => ?_⟩
    have hAB : ∀ s ∈ Icc (0 : ℝ) T,
        ‖fderiv ℝ (f s) (α y s) - fderiv ℝ (f s) (α x s)‖ ≤ ε₁ := by
      intro s hs
      have h1 : dist (α y s) (α x s) < δ₁ :=
        calc dist (α y s) (α x s) ≤ (L' : ℝ) * dist y x := (hlip s hs).dist_le_mul y hy x hx
          _ ≤ ((L' : ℝ) + 1) * dist y x := by gcongr; linarith
          _ < ((L' : ℝ) + 1) * (δ₁ / ((L' : ℝ) + 1)) := by gcongr
          _ = δ₁ := by field_simp
      have := hδ₁c (s, α y s) ⟨hs, hαK y hy s hs⟩ (s, α x s) ⟨hs, hαK x hx s hs⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact h1)
      rw [dist_eq_norm] at this
      exact this.le
    show dist (Y' y t) (Y' x t) < ε
    rw [hYx y hy, hYx x hx, dist_comm]
    calc dist (Y x hx t) (Y y hy t)
        ≤ ε₁ * Real.exp (M * T) * (T * Real.exp (M * T)) :=
          dist_le_of_linearODE_coeff_close hM0 hε₁0.le (hAM x hx) (hAM y hy) hAB
            (hY x hx).1 (hY x hx).2 (hY y hy).1 (hY y hy).2 t ht
      _ = ε₁ * C := by rw [hC]; ring
      _ ≤ ε₁ * (C + 1) := by nlinarith [hε₁0.le, hC0]
      _ = ε / 2 := by rw [hε₁]; field_simp
      _ < ε := by linarith

end C1

section Ck

/-- The induction behind `contDiffOn_flow_of_contDiffOn`, on the order `k + 1`, generalised over
the space: the step passes from `(E, f, α)` to the pair flow `(x, Z) ↦ (α x t, Y x t ∘ Z)` of
the field `(z, Z) ↦ (f t z, D(f t)(z) ∘ Z)` on `E × (E →L E)`, which is one order less smooth. -/
theorem contDiffOn_flow_aux (k : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (f : ℝ → E → E) (V : Set (ℝ × E)), IsOpen V → ∀ (T : ℝ), 0 < T →
      ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry f) V →
      ∀ (α : E → ℝ → E) (S : Set E), IsOpen S → ∀ (K : Set E), IsCompact K → Convex ℝ K →
      Icc 0 T ×ˢ K ⊆ V → (∀ x ∈ S, α x 0 = x) →
      (∀ x ∈ S, ∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f t (α x t)) (Icc 0 T) t) →
      (∀ x ∈ S, ∀ t ∈ Icc 0 T, α x t ∈ K) →
      ∀ (L' : ℝ≥0), (∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) S) →
      ∀ t ∈ Icc 0 T, ContDiffOn ℝ (k + 1 : ℕ) (α · t) S := by
  induction k with
  | zero =>
    intro E _ _ _ f V hV T hT hf α S hS K hK _ hKV hα0 hαd hαK L' hlip t ht
    have hn : (1 : WithTop ℕ∞) ≤ ((0 + 1 : ℕ) : WithTop ℕ∞) := by simp
    obtain ⟨U, hU, hKU, -, hfd, hDc⟩ :=
      exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry hV hn hf hK hKV
    obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      (hDc.mono (prod_mono subset_rfl hKU))
    obtain ⟨Y, hY, hYc⟩ := exists_variational_of_lipschitz hU hT hfd hDc hK hKU hS hα0 hαd hαK
      hlip (M := max M₀ 0) (le_max_right _ _)
      (fun s hs z hz => (hM₀ (s, z) ⟨hs, hz⟩).trans (le_max_left _ _))
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun x hx => ((hY x hx).2.2 t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hYc t ht).congr fun x hx => ((hY x hx).2.2 t ht).fderiv
  | succ k ih =>
    intro E _ _ _ f V hV T hT hf α S hS K hK hKc hKV hα0 hαd hαK L' hlip t ht
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    have hn : (1 : WithTop ℕ∞) ≤ ((k + 1 + 1 : ℕ) : WithTop ℕ∞) := by norm_cast; omega
    have hn1 : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by norm_cast; omega
    obtain ⟨U, hU, hKU, -, hfd, hDc⟩ :=
      exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry hV hn hf hK hKV
    -- the bound on `Df` on the compact
    obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      (hDc.mono (prod_mono subset_rfl hKU))
    set M : ℝ := max M₀ 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hM : ∀ s ∈ Icc (0 : ℝ) T, ∀ z ∈ K, ‖fderiv ℝ (f s) z‖ ≤ M :=
      fun s hs z hz => (hM₀ (s, z) ⟨hs, hz⟩).trans (le_max_left _ _)
    -- the variational solution: the derivative in the initial point, continuous
    obtain ⟨Y, hY, -⟩ := exists_variational_of_lipschitz hU hT hfd hDc hK hKU hS hα0 hαd hαK
      hlip hM0 hM
    -- `Df` is Lipschitz on the convex compact `K`, uniformly in time
    have hf2 : ContDiffOn ℝ (k + 1 : ℕ) (fderiv ℝ (Function.uncurry f)) V :=
      hf.fderiv_of_isOpen hV (by push_cast; exact le_rfl)
    obtain ⟨M₂', hM₂'⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      ((hf2.continuousOn_fderiv_of_isOpen hV hn1).mono hKV)
    set M₂ : ℝ := max M₂' 0 with hM₂def
    have hM₂0 : 0 ≤ M₂ := le_max_right _ _
    have hinr : ‖ContinuousLinearMap.inr ℝ ℝ E‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
        simp only [ContinuousLinearMap.inr_apply, one_mul, Prod.norm_def, norm_zero]
        exact max_le (norm_nonneg _) le_rfl
    have hDlip : ∀ s ∈ Icc (0 : ℝ) T, ∀ z ∈ K, ∀ w ∈ K,
        ‖fderiv ℝ (f s) z - fderiv ℝ (f s) w‖ ≤ M₂ * ‖z - w‖ := by
      intro s hs z hz w hw
      have hd : ∀ y ∈ K, HasFDerivWithinAt (fun y => fderiv ℝ (Function.uncurry f) (s, y))
          (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (s, y) ∘L ContinuousLinearMap.inr ℝ ℝ E)
          K y := by
        intro y hy
        have hdiff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (s, y) :=
          (hf2.differentiableOn (lt_of_lt_of_le zero_lt_one hn1).ne').differentiableAt
            (hV.mem_nhds (hKV ⟨hs, hy⟩))
        exact (hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)).hasFDerivWithinAt
      have hbound : ∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ (Function.uncurry f)) (s, y) ∘L
          ContinuousLinearMap.inr ℝ ℝ E‖ ≤ M₂ := by
        intro y hy
        calc ‖fderiv ℝ (fderiv ℝ (Function.uncurry f)) (s, y) ∘L ContinuousLinearMap.inr ℝ ℝ E‖
            ≤ ‖fderiv ℝ (fderiv ℝ (Function.uncurry f)) (s, y)‖ *
              ‖ContinuousLinearMap.inr ℝ ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ M₂ * 1 :=
              mul_le_mul ((hM₂' (s, y) ⟨hs, hy⟩).trans (le_max_left _ _)) hinr (norm_nonneg _)
                hM₂0
          _ = M₂ := mul_one _
      have hmv := hKc.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbound hw hz
      rw [(hasFDerivAt_of_contDiffOn_uncurry hV hn hf (hKV ⟨hs, hz⟩)).fderiv,
        (hasFDerivAt_of_contDiffOn_uncurry hV hn hf (hKV ⟨hs, hw⟩)).fderiv,
        ← ContinuousLinearMap.sub_comp]
      calc ‖(fderiv ℝ (Function.uncurry f) (s, z) - fderiv ℝ (Function.uncurry f) (s, w)) ∘L
            ContinuousLinearMap.inr ℝ ℝ E‖
          ≤ ‖fderiv ℝ (Function.uncurry f) (s, z) - fderiv ℝ (Function.uncurry f) (s, w)‖ *
            ‖ContinuousLinearMap.inr ℝ ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M₂ * ‖z - w‖ * 1 := mul_le_mul hmv hinr (norm_nonneg _) (by positivity)
        _ = M₂ * ‖z - w‖ := mul_one _
    -- the variational solution is Lipschitz in the initial point, and bounded
    set LY : ℝ := M₂ * (L' : ℝ) * (Real.exp (M * T) * (T * Real.exp (M * T))) with hLY
    have hLY0 : 0 ≤ LY := by positivity
    have hYlip : ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ S, ∀ y ∈ S,
        dist (Y x s) (Y y s) ≤ LY * dist x y := by
      intro s hs x hx y hy
      have hAB : ∀ u ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (f u) (α y u) - fderiv ℝ (f u) (α x u)‖
          ≤ M₂ * ((L' : ℝ) * dist x y) := by
        intro u hu
        calc ‖fderiv ℝ (f u) (α y u) - fderiv ℝ (f u) (α x u)‖
            ≤ M₂ * ‖α y u - α x u‖ := hDlip u hu _ (hαK y hy u hu) _ (hαK x hx u hu)
          _ ≤ M₂ * ((L' : ℝ) * dist x y) := by
              gcongr
              rw [← dist_eq_norm, dist_comm]
              exact (hlip u hu).dist_le_mul x hx y hy
      have h := dist_le_of_linearODE_coeff_close hM0 (by positivity)
        (fun u hu => hM u hu _ (hαK x hx u hu)) (fun u hu => hM u hu _ (hαK y hy u hu)) hAB
        (hY x hx).1 (hY x hx).2.1 (hY y hy).1 (hY y hy).2.1 s hs
      calc dist (Y x s) (Y y s)
          ≤ M₂ * ((L' : ℝ) * dist x y) * Real.exp (M * T) * (T * Real.exp (M * T)) := h
        _ = LY * dist x y := by rw [hLY]; ring
    have hYn : ∀ x ∈ S, ∀ s ∈ Icc (0 : ℝ) T, ‖Y x s‖ ≤ Real.exp (M * T) := by
      intro x hx s hs
      refine (norm_le_exp_of_linearODE hM0 (fun u hu => hM u hu _ (hαK x hx u hu)) (hY x hx).1
        (hY x hx).2.1 s hs).trans ?_
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hM0)
    -- the pair field on `E × (E →L E)` and the pair flow
    set G : ℝ → E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
      fun s p => (f s p.1, fderiv ℝ (f s) p.1 ∘L p.2) with hG
    set V' : Set (ℝ × (E × (E →L[ℝ] E))) := {p | (p.1, p.2.1) ∈ V} with hV'
    have hV'o : IsOpen V' :=
      hV.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hG : ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry G) V' := by
      have hπ : ContDiff ℝ (k + 1 : ℕ) (fun p : ℝ × (E × (E →L[ℝ] E)) => (p.1, p.2.1)) :=
        contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
      have h1 : ContDiffOn ℝ (k + 1 : ℕ) (fun p : ℝ × (E × (E →L[ℝ] E)) => f p.1 p.2.1) V' :=
        (hf.of_le (by norm_cast; omega)).comp hπ.contDiffOn fun p hp => hp
      have h2 : ContDiffOn ℝ (k + 1 : ℕ) (fun p : ℝ × (E × (E →L[ℝ] E)) =>
          (fderiv ℝ (Function.uncurry f) (p.1, p.2.1) ∘L ContinuousLinearMap.inr ℝ ℝ E) ∘L
            p.2.2) V' :=
        ((hf2.comp hπ.contDiffOn fun p hp => hp).clm_comp contDiffOn_const).clm_comp
          contDiff_snd.snd.contDiffOn
      refine (h1.prodMk h2).congr fun p hp => ?_
      show (f p.1 p.2.1, fderiv ℝ (f p.1) p.2.1 ∘L p.2.2) = _
      rw [(hasFDerivAt_of_contDiffOn_uncurry hV hn hf hp).fderiv]
    set β : E × (E →L[ℝ] E) → ℝ → E × (E →L[ℝ] E) :=
      fun p s => (α p.1 s, Y p.1 s ∘L p.2) with hβ
    set S' : Set (E × (E →L[ℝ] E)) := S ×ˢ ball (0 : E →L[ℝ] E) 2 with hS'
    have hS'o : IsOpen S' := hS.prod isOpen_ball
    set K' : Set (E × (E →L[ℝ] E)) :=
      K ×ˢ closedBall (0 : E →L[ℝ] E) (2 * Real.exp (M * T)) with hK'
    have hK'c : IsCompact K' := hK.prod (isCompact_closedBall _ _)
    have hK'cv : Convex ℝ K' := hKc.prod (convex_closedBall _ _)
    have hK'V' : Icc 0 T ×ˢ K' ⊆ V' := fun p hp => hKV ⟨hp.1, hp.2.1⟩
    have hβ0 : ∀ p ∈ S', β p 0 = p := by
      rintro ⟨x, Z⟩ ⟨hx, -⟩
      show (α x 0, Y x 0 ∘L Z) = (x, Z)
      rw [hα0 x hx, (hY x hx).1, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    have hβd : ∀ p ∈ S', ∀ s ∈ Icc 0 T, HasDerivWithinAt (β p) (G s (β p s)) (Icc 0 T) s := by
      rintro ⟨x, Z⟩ ⟨hx, -⟩ s hs
      have h := (hαd x hx s hs).prodMk
        (((hY x hx).2.1 s hs).clm_comp (hasDerivWithinAt_const s (Icc (0 : ℝ) T) Z))
      refine h.congr_deriv ?_
      show _ = (f s (α x s), fderiv ℝ (f s) (α x s) ∘L (Y x s ∘L Z))
      simp [ContinuousLinearMap.comp_assoc]
    have hβK : ∀ p ∈ S', ∀ s ∈ Icc 0 T, β p s ∈ K' := by
      rintro ⟨x, Z⟩ ⟨hx, hZ⟩ s hs
      refine ⟨hαK x hx s hs, ?_⟩
      rw [mem_closedBall_zero_iff]
      calc ‖Y x s ∘L Z‖ ≤ ‖Y x s‖ * ‖Z‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ Real.exp (M * T) * 2 := by
            gcongr
            · exact hYn x hx s hs
            · exact (mem_ball_zero_iff.mp hZ).le
        _ = 2 * Real.exp (M * T) := mul_comm _ _
    set L'' : ℝ≥0 := ⟨max (L' : ℝ) (2 * LY + Real.exp (M * T)), le_max_of_le_left L'.2⟩ with hL''
    have hlip' : ∀ s ∈ Icc 0 T, LipschitzOnWith L'' (β · s) S' := by
      intro s hs
      refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
      obtain ⟨x, Z⟩ := p
      obtain ⟨y, W⟩ := q
      obtain ⟨hx, hZ⟩ := hp
      obtain ⟨hy, hW⟩ := hq
      have hZ2 : ‖Z‖ ≤ 2 := (mem_ball_zero_iff.mp hZ).le
      have hd1 : dist x y ≤ dist (x, Z) (y, W) := le_max_left _ _
      have hd2 : dist Z W ≤ dist (x, Z) (y, W) := le_max_right _ _
      show dist (α x s, Y x s ∘L Z) (α y s, Y y s ∘L W) ≤ (L'' : ℝ) * dist (x, Z) (y, W)
      rw [Prod.dist_eq]
      dsimp only
      refine max_le ?_ ?_
      · calc dist (α x s) (α y s) ≤ (L' : ℝ) * dist x y := (hlip s hs).dist_le_mul x hx y hy
          _ ≤ (L' : ℝ) * dist (x, Z) (y, W) := by gcongr
          _ ≤ (L'' : ℝ) * dist (x, Z) (y, W) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
      · calc dist (Y x s ∘L Z) (Y y s ∘L W)
            = ‖(Y x s - Y y s) ∘L Z + Y y s ∘L (Z - W)‖ := by
              rw [dist_eq_norm, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
              abel_nf
          _ ≤ ‖(Y x s - Y y s) ∘L Z‖ + ‖Y y s ∘L (Z - W)‖ := norm_add_le _ _
          _ ≤ ‖Y x s - Y y s‖ * ‖Z‖ + ‖Y y s‖ * ‖Z - W‖ :=
              add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
                (ContinuousLinearMap.opNorm_comp_le _ _)
          _ ≤ LY * dist x y * 2 + Real.exp (M * T) * dist Z W := by
              gcongr
              · rw [← dist_eq_norm]
                exact hYlip s hs x hx y hy
              · exact hYn y hy s hs
              · exact (dist_eq_norm Z W).ge
          _ ≤ (2 * LY + Real.exp (M * T)) * dist (x, Z) (y, W) := by
              have e1 := mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ 2 * LY)
              have e2 := mul_le_mul_of_nonneg_left hd2 (Real.exp_pos (M * T)).le
              linarith
          _ ≤ (L'' : ℝ) * dist (x, Z) (y, W) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
    -- the induction hypothesis on the pair flow
    have hβk := ih (E × (E →L[ℝ] E)) G V' hV'o T hT hG β S' hS'o K' hK'c hK'cv hK'V' hβ0 hβd hβK
      L'' hlip' t ht
    -- so `x ↦ Y x t` is `C^{k+1}`
    have hYk : ContDiffOn ℝ (k + 1 : ℕ) (fun x => Y x t) S := by
      have h1 : ContDiffOn ℝ (k + 1 : ℕ) (fun x => β (x, 1) t) S :=
        hβk.comp (contDiff_prodMk_left (1 : E →L[ℝ] E)).contDiffOn fun x hx =>
          ⟨hx, mem_ball_zero_iff.mpr (ContinuousLinearMap.norm_id_le.trans_lt one_lt_two)⟩
      refine h1.snd.congr fun x _ => ?_
      show Y x t ∘L 1 = Y x t
      rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    -- and `α · t` is `C^{k+2}`
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun x hx => ((hY x hx).2.2 t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hYk.congr fun x hx => ((hY x hx).2.2 t ht).fderiv

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- ★★ **`C^n` dependence of a flow on its initial point.** Let `f` be a time-dependent field,
jointly `C^n` (`1 ≤ n ≤ ∞`) on an open `V ⊆ ℝ × E`, and `α` a flow of `f` on an open set `S` of
initial points for times in `[0, T]`, confined to a compact convex `K` with `[0, T] × K ⊆ V` and
Lipschitz in the initial point uniformly in time. Then the time-`t` map `α · t` is `C^n` on `S`.
-/
theorem contDiffOn_flow_of_contDiffOn {f : ℝ → E → E} {V : Set (ℝ × E)} (hV : IsOpen V)
    {T : ℝ} (hT : 0 < T) {n : ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n (Function.uncurry f) V)
    {α : E → ℝ → E} {S : Set E} (hS : IsOpen S) {K : Set E} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKV : Icc 0 T ×ˢ K ⊆ V) (hα0 : ∀ x ∈ S, α x 0 = x)
    (hαd : ∀ x ∈ S, ∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f t (α x t)) (Icc 0 T) t)
    (hαK : ∀ x ∈ S, ∀ t ∈ Icc 0 T, α x t ∈ K) {L' : ℝ≥0}
    (hlip : ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) S) :
    ∀ t ∈ Icc 0 T, ContDiffOn ℝ n (α · t) S := by
  intro t ht
  induction n using ENat.recTopCoe with
  | top =>
    rw [contDiffOn_infty]
    intro m
    have hfm : ContDiffOn ℝ (m + 1 : ℕ) (Function.uncurry f) V := contDiffOn_infty.mp hf (m + 1)
    exact (contDiffOn_flow_aux m E f V hV T hT hfm α S hS K hK hKc hKV hα0 hαd hαK L' hlip t
      ht).of_le (by exact_mod_cast Nat.le_succ m)
  | coe m =>
    have hm : 1 ≤ m := by exact_mod_cast hn
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact contDiffOn_flow_aux k E f V hV T hT hf α S hS K hK hKc hKV hα0 hαd hαK L' hlip t ht

end Ck

end
