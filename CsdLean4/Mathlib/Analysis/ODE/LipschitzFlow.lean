/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Dynamics.Flow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import CsdLean4.Mathlib.Analysis.ODE.FlowDerivative

/-!
# The global flow of a Lipschitz vector field

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Mathlib's Picard–Lindelöf theorem (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`)
gives a solution of `x' = v x` on a short time interval whose length depends on the initial point,
and Grönwall's inequality gives uniqueness (`ODE_solution_unique_univ`). What Mathlib does not have
is the **global flow**: for a *globally* Lipschitz field the step length is uniform in the initial
point, so the short solutions concatenate to a solution on all of `ℝ` through every point, and
uniqueness makes the time-`t` maps a group. This file proves it.

* `LipschitzWith.exists_hasDerivWithinAt_Icc_step` — **the uniform step**: through every point a
  solution on `[−τ, τ]`, `τ = 1/(2(K + 1))` (Picard–Lindelöf on the ball of radius
  `(‖v x‖ + 1)/(K + 1)`, where the field is bounded by `2‖v x‖ + 1`);
* `LipschitzWith.exists_hasDerivWithinAt_Icc_forward`, `…_Icc_symm` — solutions on `[0, T]` and on
  `[−T, T]` for every `T` (concatenation by `hasDerivWithinAt_Icc_glue`; backward time by the
  reversed field `−v`);
* `LipschitzWith.eqOn_Icc_of_hasDerivWithinAt` — two solutions on `[−T, T]` with one initial point
  agree there;
* ★ `LipschitzWith.exists_global_solution` — **through every point a solution on all of `ℝ`**
  (the solutions on `[−(n + 1), n + 1]` patched by uniqueness);
* ★★ `LipschitzWith.odeFlow` — **the flow**, `odeFlow_zero`, `hasDerivAt_odeFlow`,
  `odeFlow_eq_of_hasDerivAt` (uniqueness: every global solution is an orbit), **`odeFlow_add`
  (the group law)**, `odeFlow_neg_odeFlow` (every time-`t` map is invertible), `odeFlow_neg`
  (backward time is the flow of `−v`);
* ★ `LipschitzWith.dist_odeFlow_le` — **Grönwall**: `dist (φ_t x) (φ_t y) ≤ dist x y · e^{K|t|}`;
  `lipschitzWith_odeFlow`, `continuous_odeFlow_point`, `measurable_odeFlow`;
* ★ `LipschitzWith.continuous_odeFlow` — **joint continuity** in `(t, x)`; `LipschitzWith.toFlow`,
  the flow as Mathlib's `Flow ℝ E`.

## Honest scope

The field is **globally** Lipschitz. A locally Lipschitz field with an a priori bound (a conserved
norm, say) is covered by a cutoff that leaves the field unchanged on the bounded region the
trajectories stay in; the cutoff is the consumer's. Differentiable dependence on the initial point
is `FlowDerivative.lean`; nothing here is a manifold statement (that is
`Geometry/Manifold/IntegralCurve/GlobalFlow.lean`, for compact manifolds).

References: `Mathlib/Analysis/ODE/PicardLindelof.lean` (`IsPicardLindelof.of_time_independent`),
`Mathlib/Analysis/ODE/ExistUnique.lean` (`ODE_solution_unique_univ`, `ODE_solution_unique_of_mem_Icc`),
`Mathlib/Analysis/ODE/Gronwall.lean` (`dist_le_of_trajectories_ODE`),
`CsdLean4/Mathlib/Analysis/ODE/FlowDerivative.lean` (`hasDerivWithinAt_Icc_glue`).
-/

@[expose] public section

open Set Metric Filter Topology
open scoped NNReal

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K : ℝ≥0}

/-! ### Existence on bounded intervals -/

/-- **The uniform step**: a `K`-Lipschitz field has a solution through every point on
`[−τ, τ]`, `τ = 1/(2(K + 1))`, whatever the point. -/
theorem exists_hasDerivWithinAt_Icc_step (hv : LipschitzWith K v) (x : E) :
    ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Icc (-(1 / (2 * ((K : ℝ) + 1)))) (1 / (2 * ((K : ℝ) + 1))),
      HasDerivWithinAt α (v (α t)) (Icc (-(1 / (2 * ((K : ℝ) + 1)))) (1 / (2 * ((K : ℝ) + 1)))) t := by
  set τ : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  have hvx := norm_nonneg (v x)
  set a : ℝ≥0 := ⟨(‖v x‖ + 1) / ((K : ℝ) + 1), by positivity⟩ with ha
  set L : ℝ≥0 := ⟨2 * ‖v x‖ + 1, by positivity⟩ with hL
  have hKa : (K : ℝ) * a ≤ ‖v x‖ + 1 := by
    show (K : ℝ) * ((‖v x‖ + 1) / ((K : ℝ) + 1)) ≤ ‖v x‖ + 1
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hb : ∀ y ∈ closedBall x (a : ℝ), ‖v y‖ ≤ (L : ℝ) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 : ‖v y - v x‖ ≤ K * ‖y - x‖ := hv.norm_sub_le y x
    have h2 : (K : ℝ) * ‖y - x‖ ≤ K * a := mul_le_mul_of_nonneg_left hy hK
    show ‖v y‖ ≤ 2 * ‖v x‖ + 1
    calc ‖v y‖ ≤ ‖v y - v x‖ + ‖v x‖ := norm_le_norm_sub_add _ _
      _ ≤ 2 * ‖v x‖ + 1 := by linarith
  have hm : (L : ℝ) * max (τ - ((⟨0, by constructor <;> linarith⟩ : Icc (-τ) τ) : ℝ))
      (((⟨0, by constructor <;> linarith⟩ : Icc (-τ) τ) : ℝ) - -τ) ≤ (a : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    show (2 * ‖v x‖ + 1) * max (τ - 0) (0 - -τ) ≤ (‖v x‖ + 1) / ((K : ℝ) + 1) - 0
    rw [sub_zero, zero_sub, neg_neg, max_self, sub_zero, hτ, mul_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpl : IsPicardLindelof (fun _ => v) (tmin := -τ) (tmax := τ) ⟨0, by constructor <;> linarith⟩
      x a 0 L K :=
    IsPicardLindelof.of_time_independent hb hv.lipschitzOnWith hm
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hαd⟩

omit [CompleteSpace E] in
/-- A solution shifted in time is a solution. -/
theorem hasDerivWithinAt_Icc_shift {α : ℝ → E} {a b s : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (v (α t)) (Icc a b) t) :
    ∀ t ∈ Icc (s + a) (s + b),
      HasDerivWithinAt (fun t => α (t - s)) (v (α (t - s))) (Icc (s + a) (s + b)) t := by
  intro t ht
  have h1 : HasDerivWithinAt (fun t : ℝ => t - s) 1 (Icc (s + a) (s + b)) t :=
    (hasDerivWithinAt_id t _).sub_const s
  have h2 := (hα (t - s) ⟨by linarith [ht.1], by linarith [ht.2]⟩).scomp t h1
    (show MapsTo (fun t : ℝ => t - s) (Icc (s + a) (s + b)) (Icc a b) from
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  simpa [Function.comp_def] using h2

/-- **Solutions on `[0, T]`** through every point, for every `T`: the uniform steps concatenated. -/
theorem exists_hasDerivWithinAt_Icc_forward (hv : LipschitzWith K v) (x : E) (T : ℝ) :
    ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt α (v (α t)) (Icc 0 T) t := by
  set τ : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have key : ∀ m : ℕ, ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Icc 0 (((m : ℝ) + 1) * τ),
      HasDerivWithinAt α (v (α t)) (Icc 0 (((m : ℝ) + 1) * τ)) t := by
    intro m
    induction m with
    | zero =>
      obtain ⟨α, hα0, hαd⟩ := hv.exists_hasDerivWithinAt_Icc_step x
      have hsub : Icc (0 : ℝ) ((((0 : ℕ) : ℝ) + 1) * τ) ⊆ Icc (-τ) τ := by
        rw [Nat.cast_zero, zero_add, one_mul]
        exact Icc_subset_Icc (by linarith) le_rfl
      exact ⟨α, hα0, fun t ht => (hαd t (hsub ht)).mono hsub⟩
    | succ m ih =>
      obtain ⟨α, hα0, hαd⟩ := ih
      set s : ℝ := ((m : ℝ) + 1) * τ with hs
      have hs0 : 0 ≤ s := by positivity
      obtain ⟨β, hβ0, hβd⟩ := hv.exists_hasDerivWithinAt_Icc_step (α s)
      have hβ' := hasDerivWithinAt_Icc_shift (s := s) hβd
      have hβ'' : ∀ t ∈ Icc s (s + τ), HasDerivWithinAt (fun t => β (t - s)) (v (β (t - s)))
          (Icc s (s + τ)) t := fun t ht =>
        (hβ' t ⟨by linarith [ht.1], ht.2⟩).mono (Icc_subset_Icc (by linarith) le_rfl)
      refine ⟨fun t => if t ≤ s then α t else β (t - s), by simp [hα0, hs0], ?_⟩
      have hj : α s = β (s - s) := by rw [sub_self, hβ0]
      have h := hasDerivWithinAt_Icc_glue (v := fun _ y => v y) hs0 (by linarith) hαd hβ'' hj
      push_cast
      rw [add_mul _ (1 : ℝ) τ, one_mul]
      exact h
  obtain ⟨m, hm⟩ := exists_nat_ge (T / τ)
  obtain ⟨α, hα0, hαd⟩ := key m
  have hTm : T ≤ ((m : ℝ) + 1) * τ := by
    calc T = T / τ * τ := by rw [div_mul_cancel₀ _ hτ0.ne']
      _ ≤ (m : ℝ) * τ := by gcongr
      _ ≤ ((m : ℝ) + 1) * τ := by nlinarith [hτ0.le]
  exact ⟨α, hα0, fun t ht => (hαd t (Icc_subset_Icc_right hTm ht)).mono
    (Icc_subset_Icc_right hTm)⟩

/-- **Solutions on `[−T, T]`** through every point, for every `T`: forward in time by the field,
backward by the reversed field `−v`, glued at `0`. -/
theorem exists_hasDerivWithinAt_Icc_symm (hv : LipschitzWith K v) (x : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Icc (-T) T, HasDerivWithinAt α (v (α t)) (Icc (-T) T) t := by
  obtain ⟨α, hα0, hαd⟩ := hv.exists_hasDerivWithinAt_Icc_forward x T
  obtain ⟨β, hβ0, hβd⟩ := hv.neg.exists_hasDerivWithinAt_Icc_forward x T
  have hβ' : ∀ t ∈ Icc (-T) 0, HasDerivWithinAt (fun t => β (-t)) (v (β (-t))) (Icc (-T) 0) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t : ℝ => -t) (-1) (Icc (-T) 0) t := (hasDerivAt_neg t).hasDerivWithinAt
    have h2 := (hβd (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).scomp t h1
      (show MapsTo (fun t : ℝ => -t) (Icc (-T) 0) (Icc 0 T) from
        fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    simpa [Function.comp_def, Pi.neg_apply] using h2
  refine ⟨fun t => if t ≤ 0 then β (-t) else α t, by simp [hβ0], ?_⟩
  have hj : β (-0) = α 0 := by rw [neg_zero, hβ0, hα0]
  exact hasDerivWithinAt_Icc_glue (v := fun _ y => v y) (by linarith) hT hβ' hαd hj

/-! ### Uniqueness and the global solution -/

omit [CompleteSpace E] in
/-- Two solutions on `[−T, T]` with the same initial point agree there. -/
theorem eqOn_Icc_of_hasDerivWithinAt (hv : LipschitzWith K v) {α β : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hα : ∀ t ∈ Icc (-T) T, HasDerivWithinAt α (v (α t)) (Icc (-T) T) t)
    (hβ : ∀ t ∈ Icc (-T) T, HasDerivWithinAt β (v (β t)) (Icc (-T) T) t) (h0 : α 0 = β 0) :
    EqOn α β (Icc (-T) T) :=
  ODE_solution_unique_of_mem_Icc (v := fun _ y => v y) (s := fun _ => univ) (K := K)
    (fun _ _ => hv.lipschitzOnWith) (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT⟩)
    (fun t ht => (hα t ht).continuousWithinAt)
    (fun t ht => (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => trivial) (fun t ht => (hβ t ht).continuousWithinAt)
    (fun t ht => (hβ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => trivial) h0

/-- ★ **Through every point a solution on all of `ℝ`.** -/
theorem exists_global_solution (hv : LipschitzWith K v) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  have hex : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivWithinAt α (v (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t :=
    fun n => hv.exists_hasDerivWithinAt_Icc_symm x (by positivity)
  choose α hα0 hαd using hex
  -- two of the solutions agree wherever both are defined
  have hagree : ∀ n m : ℕ, ∀ t : ℝ, |t| ≤ n → |t| ≤ m → α n t = α m t := by
    intro n m t hn hm
    set N : ℝ := min (n : ℝ) m + 1 with hN
    have hN0 : 0 < N := by positivity
    have hsub_n : Icc (-N) N ⊆ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
      Icc_subset_Icc (by linarith [min_le_left (n : ℝ) m]) (by linarith [min_le_left (n : ℝ) m])
    have hsub_m : Icc (-N) N ⊆ Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1) :=
      Icc_subset_Icc (by linarith [min_le_right (n : ℝ) m]) (by linarith [min_le_right (n : ℝ) m])
    have h := hv.eqOn_Icc_of_hasDerivWithinAt hN0
      (fun t ht => (hαd n t (hsub_n ht)).mono hsub_n)
      (fun t ht => (hαd m t (hsub_m ht)).mono hsub_m) (by rw [hα0, hα0])
    have ht : t ∈ Icc (-N) N := by
      rw [mem_Icc, ← abs_le]
      exact (le_min hn hm).trans (by linarith)
    exact h ht
  refine ⟨fun t => α ⌈|t|⌉₊ t, by simp [hα0], fun t => ?_⟩
  set n := ⌈|t|⌉₊ with hn
  have htn : |t| ≤ n := Nat.le_ceil _
  have hopen : IsOpen {u : ℝ | |u| < (n : ℝ) + 1} := isOpen_lt continuous_abs continuous_const
  have hmem : t ∈ {u : ℝ | |u| < (n : ℝ) + 1} := by
    show |t| < (n : ℝ) + 1
    linarith
  have heq : (fun u => α ⌈|u|⌉₊ u) =ᶠ[𝓝 t] α n := by
    refine eventuallyEq_of_mem (hopen.mem_nhds hmem) fun u hu => ?_
    have hu' : |u| < (n : ℝ) + 1 := hu
    by_cases h : |u| ≤ n
    · exact hagree _ _ u (Nat.le_ceil _) h
    · -- `u` is just beyond `n`; both solutions still live on `[−(n + 1), n + 1]`
      have hc : ⌈|u|⌉₊ = n + 1 := by
        rw [Nat.ceil_eq_iff (by positivity)]
        push_cast
        exact ⟨by linarith [not_le.1 h], hu'.le⟩
      rw [hc]
      have hN0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsub : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
          ⊆ Icc (-(((n + 1 : ℕ) : ℝ) + 1)) (((n + 1 : ℕ) : ℝ) + 1) :=
        Icc_subset_Icc (by push_cast; linarith) (by push_cast; linarith)
      have h := hv.eqOn_Icc_of_hasDerivWithinAt hN0
        (fun t ht => (hαd (n + 1) t (hsub ht)).mono hsub) (hαd n) (by rw [hα0, hα0])
      exact h ⟨by linarith [abs_lt.1 hu'], by linarith [abs_lt.1 hu']⟩
  have hd : HasDerivAt (α n) (v (α n t)) t :=
    (hαd n t ⟨by linarith [abs_le.1 htn], by linarith [abs_le.1 htn]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [abs_le.1 htn]) (by linarith [abs_le.1 htn]))
  exact hd.congr_of_eventuallyEq heq

/-! ### The flow -/

/-- ★★ **The flow of a Lipschitz field**: `odeFlow hv t x` is the solution through `x` at time
`t`. -/
noncomputable def odeFlow (hv : LipschitzWith K v) (t : ℝ) (x : E) : E :=
  Classical.choose (hv.exists_global_solution x) t

theorem odeFlow_zero (hv : LipschitzWith K v) (x : E) : hv.odeFlow 0 x = x :=
  (Classical.choose_spec (hv.exists_global_solution x)).1

theorem hasDerivAt_odeFlow (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (fun t => hv.odeFlow t x) (v (hv.odeFlow t x)) t :=
  (Classical.choose_spec (hv.exists_global_solution x)).2 t

/-- **Uniqueness**: every global solution is an orbit of the flow. -/
theorem odeFlow_eq_of_hasDerivAt (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) {x : E} (h0 : γ 0 = x) :
    γ = fun t => hv.odeFlow t x :=
  ODE_solution_unique_univ (v := fun _ y => v y) (s := fun _ => univ) (K := K) (t₀ := 0)
    (fun _ => hv.lipschitzOnWith) (fun t => ⟨hγ t, trivial⟩)
    (fun t => ⟨hv.hasDerivAt_odeFlow x t, trivial⟩) (by rw [h0, odeFlow_zero])

/-- ★★ **The group law.** -/
theorem odeFlow_add (hv : LipschitzWith K v) (s t : ℝ) (x : E) :
    hv.odeFlow (s + t) x = hv.odeFlow t (hv.odeFlow s x) := by
  have h := hv.odeFlow_eq_of_hasDerivAt (γ := fun u => hv.odeFlow (s + u) x)
    (fun u => (hv.hasDerivAt_odeFlow x (s + u)).comp_const_add s u) (x := hv.odeFlow s x)
    (by simp only [add_zero])
  exact congrFun h t

/-- Every time-`t` map is inverted by the time-`(−t)` map. -/
theorem odeFlow_neg_odeFlow (hv : LipschitzWith K v) (t : ℝ) (x : E) :
    hv.odeFlow (-t) (hv.odeFlow t x) = x := by
  rw [← odeFlow_add, add_neg_cancel, odeFlow_zero]

/-- Backward time is the flow of the reversed field. -/
theorem odeFlow_neg (hv : LipschitzWith K v) (t : ℝ) (x : E) :
    hv.odeFlow (-t) x = hv.neg.odeFlow t x := by
  have h := hv.neg.odeFlow_eq_of_hasDerivAt (γ := fun u => hv.odeFlow (-u) x) (fun u => ?_)
    (x := x) (by rw [neg_zero, odeFlow_zero])
  · exact congrFun h t
  · have h1 := (hv.hasDerivAt_odeFlow x (-u)).scomp u (hasDerivAt_neg u)
    simpa [Function.comp_def, Pi.neg_apply] using h1

/-! ### Dependence on the initial point -/

/-- **Grönwall, forward**: `dist (φ_t x) (φ_t y) ≤ dist x y · e^{K t}` for `t ≥ 0`. -/
theorem dist_odeFlow_le_of_nonneg (hv : LipschitzWith K v) {t : ℝ} (ht : 0 ≤ t) (x y : E) :
    dist (hv.odeFlow t x) (hv.odeFlow t y) ≤ dist x y * Real.exp (K * t) := by
  have h := dist_le_of_trajectories_ODE (v := fun _ y => v y) (K := K) (a := 0) (b := t)
    (f := fun u => hv.odeFlow u x) (g := fun u => hv.odeFlow u y) (δ := dist x y) (fun _ => hv)
    (fun u _ => (hv.hasDerivAt_odeFlow x u).continuousAt.continuousWithinAt)
    (fun u _ => (hv.hasDerivAt_odeFlow x u).hasDerivWithinAt)
    (fun u _ => (hv.hasDerivAt_odeFlow y u).continuousAt.continuousWithinAt)
    (fun u _ => (hv.hasDerivAt_odeFlow y u).hasDerivWithinAt)
    (by rw [odeFlow_zero, odeFlow_zero]) t ⟨ht, le_rfl⟩
  simpa using h

/-- ★ **Grönwall**: `dist (φ_t x) (φ_t y) ≤ dist x y · e^{K|t|}`. -/
theorem dist_odeFlow_le (hv : LipschitzWith K v) (t : ℝ) (x y : E) :
    dist (hv.odeFlow t x) (hv.odeFlow t y) ≤ dist x y * Real.exp (K * |t|) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact hv.dist_odeFlow_le_of_nonneg ht x y
  · rw [abs_of_neg ht]
    have h := hv.neg.dist_odeFlow_le_of_nonneg (show (0 : ℝ) ≤ -t by linarith) x y
    rw [← odeFlow_neg, ← odeFlow_neg, neg_neg] at h
    exact h

/-- The time-`t` map is Lipschitz with constant `e^{K|t|}`. -/
theorem lipschitzWith_odeFlow (hv : LipschitzWith K v) (t : ℝ) :
    LipschitzWith ⟨Real.exp (K * |t|), (Real.exp_pos _).le⟩ (hv.odeFlow t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    show dist _ _ ≤ Real.exp (K * |t|) * dist x y
    rw [mul_comm]
    exact hv.dist_odeFlow_le t x y

theorem continuous_odeFlow_point (hv : LipschitzWith K v) (t : ℝ) : Continuous (hv.odeFlow t) :=
  (hv.lipschitzWith_odeFlow t).continuous

theorem measurable_odeFlow [MeasurableSpace E] [BorelSpace E] (hv : LipschitzWith K v) (t : ℝ) :
    Measurable (hv.odeFlow t) :=
  (hv.continuous_odeFlow_point t).measurable

theorem continuous_odeFlow_time (hv : LipschitzWith K v) (x : E) :
    Continuous fun t => hv.odeFlow t x :=
  continuous_iff_continuousAt.2 fun t => (hv.hasDerivAt_odeFlow x t).continuousAt

/-- ★ **Joint continuity** of the flow in `(t, x)`. -/
theorem continuous_odeFlow (hv : LipschitzWith K v) :
    Continuous fun p : ℝ × E => hv.odeFlow p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  set T : ℝ := |p.1| + 1 with hT
  have hT0 : 0 < T := by positivity
  have hon : ContinuousOn (fun p : ℝ × E => hv.odeFlow p.1 p.2) (Icc (-T) T ×ˢ univ) := by
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith' (fun p : ℝ × E => hv.odeFlow p.1 p.2)
      ⟨Real.exp (K * T), (Real.exp_pos _).le⟩ (fun t ht => ?_) fun x _ => ?_
    · refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      show dist (hv.odeFlow t x) (hv.odeFlow t y) ≤ Real.exp (K * T) * dist x y
      rw [mul_comm]
      refine (hv.dist_odeFlow_le t x y).trans ?_
      gcongr
      exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    · exact (hv.continuous_odeFlow_time x).continuousOn
  refine hon.continuousAt (prod_mem_nhds (Icc_mem_nhds ?_ ?_) univ_mem)
  · linarith [neg_abs_le p.1]
  · linarith [le_abs_self p.1]

/-- The flow as Mathlib's `Flow ℝ E`. -/
noncomputable def toFlow (hv : LipschitzWith K v) : Flow ℝ E where
  toFun := hv.odeFlow
  cont' := hv.continuous_odeFlow
  map_add' := fun t₁ t₂ x => by rw [add_comm, odeFlow_add]
  map_zero' := hv.odeFlow_zero

theorem toFlow_apply (hv : LipschitzWith K v) (t : ℝ) (x : E) : hv.toFlow t x = hv.odeFlow t x :=
  rfl

end LipschitzWith
