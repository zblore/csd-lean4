/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Differentiation under the integral sign over a finite-dimensional parameter

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #124, out of #121(ii).

#120 did this for a **one-dimensional** parameter, deliberately: its scope note records that the
`fderiv` version "is the same induction with `ContinuousLinearMap` plumbing and is not done here".
#121(ii) is what wants the general case — the joint Schwartz claim needs differentiating in two
variables at once — so here it is, for a parameter in any normed space.

## The interface is directional, and that is the whole design

#124's row warned that the hypothesis-design question #120 flagged "returns in harder form: a
per-order, locally-uniform bound on a *multilinear* norm". It does not have to. Bounding
`iteratedFDeriv` means bounding a multilinear map, which drags currying equivalences through every
step; bounding **iterated directional derivatives** keeps every hypothesis valued in `E`, and the
recursion is then literally list-append:

* `dirDeriv F hs` — differentiate `F` in the directions `hs`, innermost last, by recursion on the
  list, with ★ `dirDeriv_append_singleton` the shift the induction runs on;
* ★★★ `contDiffOn_integral_of_dirBound` — **the theorem**: if each `x ↦ F x a` is `C^n`, each
  directional derivative of order `≤ n` is measurable in `a`, and the one along `hs` is bounded on an
  open `U` by `(∏ ‖hᵢ‖)·bound hs.length a` with each `bound k` integrable, then `x ↦ ∫ a, F x a` is
  `C^n` on `U`;
* ★★ `contDiff_integral_of_dirBound` — the global corollary, and ★★
  `contDiffOn_integral_of_dirBound_all` smoothness at every order;
* ★★ `norm_dirDeriv_le` and ★★ `contDiffOn_integral_of_iteratedFDeriv_bound` — **the multilinear
  interface, as a corollary of the directional one.** Added after #121(ii) tried to consume this file
  and could not: `SchwartzMap.decay` gives bounds on `iteratedFDeriv`, so without the bridge the
  directional hypotheses were not dischargeable from Schwartz data and the file was unusable by the
  row it was built for. The bridge also makes the header's claim honest — the directional form is
  easier to meet *and* strictly more general, since the multilinear form follows from it.

The product `∏ ‖hᵢ‖` is what makes the bound family shift cleanly: appending one direction `h`
multiplies it by `‖h‖` and raises the order by one, so the inner call runs with
`fun k a => ‖h‖ · bound (k + 1) a`, still integrable.

## Honest scope

⚠️ **One hypothesis is unavoidably operator-valued.** Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le` takes the derivative as a map into `H →L[ℝ] E`, so
strong measurability of `a ↦ fderiv ℝ (F · a) x` is required and cannot be reduced to directional
data. It appears as `hmeasD`, indexed the same way, and is closed under the recursion for the same
list-append reason.

⚠️ **The bound family must be nonnegative** (`hb0`). #120 needed no such hypothesis, because its
one-dimensional engine takes a bound on `‖F' x a‖` directly; here the directional bounds have to be
turned into an *operator*-norm bound through `opNorm_le_bound`, which is false for a negative constant
when `H` is trivial. It is one line to discharge for any bound family anyone builds.

⚠️ **No formula for the derivatives**, as in #120: each step produces
`fderiv (∫ a, F · a) x = ∫ a, fderiv (F · a) x` on `U` as a by-product and only the smoothness is
recorded.

⚠️ **The bound must be locally uniform in the parameter**, which is what `U` is for: a bound uniform
on a ball is what kernels actually supply, and `contDiff_integral_of_dirBound` is the `U = univ`
special case.

References: [`ContDiffParametricIntegral.lean`](ContDiffParametricIntegral.lean) (#120, the
one-dimensional case), [`ContDiffParametricIntervalIntegral.lean`](ContDiffParametricIntervalIntegral.lean)
(#60, whose directional recursion this follows), `Mathlib/Analysis/Calculus/ParametricIntegral.lean`;
`specs/BACKLOG.md` #124, #120, #121, #60.
-/

@[expose] public section

open MeasureTheory Set

variable {H : Type*} [NormedAddCommGroup H]

/-! ### The weight a list of directions carries -/

/-- The product of the directions' norms, the weight the bound family carries. -/
noncomputable def dirWeight (hs : List H) : ℝ := (hs.map fun h => ‖h‖).prod

@[simp] theorem dirWeight_nil : dirWeight ([] : List H) = 1 := by simp [dirWeight]

theorem dirWeight_nonneg (hs : List H) : 0 ≤ dirWeight hs := by
  rw [dirWeight]
  exact List.prod_nonneg fun x hx => by
    obtain ⟨h, _, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg h

theorem dirWeight_append_singleton (hs : List H) (h : H) :
    dirWeight (hs ++ [h]) = dirWeight hs * ‖h‖ := by
  simp [dirWeight, List.map_append]

variable [NormedSpace ℝ H] {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Iterated directional derivatives in the parameter -/

/-- `dirDeriv F hs` differentiates `F` in its parameter along the directions `hs`, the head of the
list being the outermost derivative. Every value is in `E`, which is what keeps the interface free of
multilinear maps. -/
noncomputable def dirDeriv (F : H → α → E) : List H → H → α → E
  | [] => F
  | h :: hs => fun x a => fderiv ℝ (fun y => dirDeriv F hs y a) x h

@[simp] theorem dirDeriv_nil (F : H → α → E) : dirDeriv F [] = F := rfl

theorem dirDeriv_cons (F : H → α → E) (h : H) (hs : List H) :
    dirDeriv F (h :: hs) = fun x a => fderiv ℝ (fun y => dirDeriv F hs y a) x h := rfl

/-- ★ **The shift the induction runs on.** Differentiating along `h` first and then along `hs` is
differentiating along `hs ++ [h]`. -/
theorem dirDeriv_append_singleton (F : H → α → E) (h : H) (hs : List H) :
    dirDeriv (dirDeriv F [h]) hs = dirDeriv F (hs ++ [h]) := by
  induction hs with
  | nil => rfl
  | cons g gs ih => rw [dirDeriv_cons, ih, List.cons_append, dirDeriv_cons]

variable [MeasurableSpace α] {μ : Measure α} [FiniteDimensional ℝ H]

/-! ### The theorem -/

/-- ★★★ **Differentiation under the integral sign to all orders, over a parameter in any normed
space.** The hypotheses are directional throughout, so nothing here is valued in a space of
multilinear maps except `hmeasD`, which Mathlib's first-derivative theorem forces. -/
theorem contDiffOn_integral_of_dirBound (n : ℕ) :
    ∀ (F : H → α → E) (U : Set H) (bound : ℕ → α → ℝ), IsOpen U →
      (∀ a, ContDiff ℝ (n : ℕ) fun x => F x a) →
      (∀ hs : List H, hs.length ≤ n → ∀ x,
        AEStronglyMeasurable (fun a => dirDeriv F hs x a) μ) →
      (∀ hs : List H, hs.length < n → ∀ x,
        AEStronglyMeasurable (fun a => fderiv ℝ (fun y => dirDeriv F hs y a) x) μ) →
      (∀ k, k ≤ n → Integrable (bound k) μ) →
      (∀ k, k ≤ n → ∀ a, 0 ≤ bound k a) →
      (∀ hs : List H, hs.length ≤ n → ∀ x ∈ U, ∀ a,
        ‖dirDeriv F hs x a‖ ≤ dirWeight hs * bound hs.length a) →
      ContDiffOn ℝ (n : ℕ) (fun x => ∫ a, F x a ∂μ) U := by
  induction n with
  | zero =>
      intro F U bound hU hsm hmeas _ hint _ hbd
      rw [Nat.cast_zero, contDiffOn_zero]
      intro x hx
      refine ContinuousAt.continuousWithinAt ?_
      refine continuousAt_of_dominated (bound := bound 0) ?_ ?_ (hint 0 le_rfl) ?_
      · filter_upwards with y using hmeas [] (by simp) y
      · filter_upwards [hU.mem_nhds hx] with y hy
        filter_upwards with a
        have h := hbd [] (by simp) y hy a
        simpa using h
      · filter_upwards with a
        exact ((hsm a).continuous).continuousAt
  | succ n ih =>
      intro F U bound hU hsm hmeas hmeasD hint hb0 hbd
      have hcast : (((n : ℕ) + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; ring
      -- each parameter slice is differentiable
      have hdiff : ∀ (a : α) (x : H), HasFDerivAt (fun y => F y a)
          (fderiv ℝ (fun y => F y a) x) x := by
        intro a x
        have h := hsm a
        rw [hcast] at h
        exact (h.differentiable (by simp) x).hasFDerivAt
      -- the operator-norm bound the first derivative satisfies on `U`
      have hopbd : ∀ x ∈ U, ∀ a, ‖fderiv ℝ (fun y => F y a) x‖ ≤ bound 1 a := by
        intro x hx a
        refine ContinuousLinearMap.opNorm_le_bound _ ?_ fun h => ?_
        · exact hb0 1 (by omega) a
        · have h1 := hbd [h] (by simp) x hx a
          rw [dirDeriv_cons] at h1
          calc ‖fderiv ℝ (fun y => F y a) x h‖
              ≤ dirWeight [h] * bound (List.length [h]) a := h1
            _ = bound 1 a * ‖h‖ := by simp [dirWeight]; ring
      -- differentiation under the integral, at each point of `U`
      have hderiv : ∀ x ∈ U, HasFDerivAt (fun x => ∫ a, F x a ∂μ)
          (∫ a, fderiv ℝ (fun y => F y a) x ∂μ) x := by
        intro x hx
        have hFint : Integrable (F x) μ := by
          refine (hint 0 (by omega)).mono' (hmeas [] (by simp) x) ?_
          filter_upwards with a using by simpa using hbd [] (by simp) x hx a
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := bound 1)
          (F' := fun x a => fderiv ℝ (fun y => F y a) x) (hU.mem_nhds hx) ?_ hFint
          (hmeasD [] (by simp) x) ?_ (hint 1 (by omega)) ?_
        · filter_upwards with y using hmeas [] (by simp) y
        · filter_upwards with a
          intro y hy
          exact hopbd y hy a
        · filter_upwards with a
          intro y _
          exact hdiff a y
      rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun x hx => ((hderiv x hx).differentiableAt).differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      -- the derivative is `C^n`, which is the inductive hypothesis in each direction
      have hdir : ∀ h : H, ContDiffOn ℝ (n : ℕ)
          (fun x => ∫ a, dirDeriv F [h] x a ∂μ) U := by
        intro h
        refine ih (dirDeriv F [h]) U (fun k a => ‖h‖ * bound (k + 1) a) hU ?_ ?_ ?_ ?_ ?_ ?_
        · intro a
          have hF := hsm a
          rw [hcast, contDiff_succ_iff_fderiv] at hF
          exact (hF.2.2).clm_apply contDiff_const
        · intro hs hlen x
          rw [dirDeriv_append_singleton] at *
          exact hmeas (hs ++ [h]) (by simp; omega) x
        · intro hs hlen x
          rw [dirDeriv_append_singleton] at *
          exact hmeasD (hs ++ [h]) (by simp; omega) x
        · intro k hk
          exact (hint (k + 1) (by omega)).const_mul ‖h‖
        · intro k hk a
          exact mul_nonneg (norm_nonneg h) (hb0 (k + 1) (by omega) a)
        · intro hs hlen x hx a
          rw [dirDeriv_append_singleton]
          have hb := hbd (hs ++ [h]) (by simp; omega) x hx a
          rw [dirWeight_append_singleton] at hb
          calc ‖dirDeriv F (hs ++ [h]) x a‖
              ≤ dirWeight hs * ‖h‖ * bound (hs ++ [h]).length a := hb
            _ = dirWeight hs * (‖h‖ * bound (hs.length + 1) a) := by simp; ring
      -- assemble the directional components into the operator-valued derivative
      have hFDint : ∀ x ∈ U, Integrable (fun a => fderiv ℝ (fun y => F y a) x) μ := by
        intro x hx
        refine (hint 1 (by omega)).mono' (hmeasD [] (by simp) x) ?_
        filter_upwards with a using hopbd x hx a
      have hfd : ContDiffOn ℝ (n : ℕ) (fun x => ∫ a, fderiv ℝ (fun y => F y a) x ∂μ) U := by
        rw [contDiffOn_clm_apply]
        intro h
        refine (hdir h).congr fun x hx => ?_
        rw [ContinuousLinearMap.integral_apply (hFDint x hx) h]
        rfl
      refine hfd.congr fun x hx => ?_
      exact (hderiv x hx).fderiv

/-- ★★ **The global corollary**, for bounds that hold at every parameter. -/
theorem contDiff_integral_of_dirBound {n : ℕ} {F : H → α → E} {bound : ℕ → α → ℝ}
    (hsm : ∀ a, ContDiff ℝ (n : ℕ) fun x => F x a)
    (hmeas : ∀ hs : List H, hs.length ≤ n → ∀ x,
      AEStronglyMeasurable (fun a => dirDeriv F hs x a) μ)
    (hmeasD : ∀ hs : List H, hs.length < n → ∀ x,
      AEStronglyMeasurable (fun a => fderiv ℝ (fun y => dirDeriv F hs y a) x) μ)
    (hint : ∀ k, k ≤ n → Integrable (bound k) μ)
    (hb0 : ∀ k, k ≤ n → ∀ a, 0 ≤ bound k a)
    (hbd : ∀ hs : List H, hs.length ≤ n → ∀ (x : H) (a : α),
      ‖dirDeriv F hs x a‖ ≤ dirWeight hs * bound hs.length a) :
    ContDiff ℝ (n : ℕ) fun x => ∫ a, F x a ∂μ := by
  rw [← contDiffOn_univ]
  exact contDiffOn_integral_of_dirBound n F univ bound isOpen_univ hsm hmeas hmeasD hint hb0
    fun hs hlen x _ a => hbd hs hlen x a

/-- ★★ **Smoothness at every order**, stated over `ℕ` so that no `∞`-coercion enters the interface. -/
theorem contDiffOn_integral_of_dirBound_all {F : H → α → E} {U : Set H} {bound : ℕ → α → ℝ}
    (hU : IsOpen U) (hsm : ∀ (m : ℕ) (a : α), ContDiff ℝ (m : ℕ) fun x => F x a)
    (hmeas : ∀ (hs : List H) (x : H), AEStronglyMeasurable (fun a => dirDeriv F hs x a) μ)
    (hmeasD : ∀ (hs : List H) (x : H),
      AEStronglyMeasurable (fun a => fderiv ℝ (fun y => dirDeriv F hs y a) x) μ)
    (hint : ∀ k : ℕ, Integrable (bound k) μ)
    (hb0 : ∀ (k : ℕ) (a : α), 0 ≤ bound k a)
    (hbd : ∀ hs : List H, ∀ x ∈ U, ∀ a, ‖dirDeriv F hs x a‖ ≤ dirWeight hs * bound hs.length a)
    (m : ℕ) :
    ContDiffOn ℝ (m : ℕ) (fun x => ∫ a, F x a ∂μ) U :=
  contDiffOn_integral_of_dirBound m F U bound hU (hsm m) (fun hs _ x => hmeas hs x)
    (fun hs _ x => hmeasD hs x) (fun k _ => hint k) (fun k _ a => hb0 k a)
    fun hs _ x hx a => hbd hs x hx a

/-! ### The multilinear interface, as a corollary of the directional one

This file's header claims the directional hypotheses are easier to meet than multilinear ones. That
is only worth claiming if the multilinear form *follows*, so here it does. The bridge is that an
iterated directional derivative is bounded by the iterated total derivative times the product of the
directions' norms — proved by peeling the **innermost** direction, which is what
`dirDeriv_append_singleton` is for. -/

omit [FiniteDimensional ℝ H] in
theorem norm_applyCLM_le (h : H) : ‖ContinuousLinearMap.apply ℝ E h‖ ≤ ‖h‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h) fun L => ?_
  rw [mul_comm]
  exact L.le_opNorm h

omit [MeasurableSpace α] [FiniteDimensional ℝ H] in
/-- ★★ **A directional derivative is bounded by the total one.** The induction peels the innermost
direction through `dirDeriv_append_singleton`, turns the evaluation into a left composition with
`ContinuousLinearMap.apply` (`ContinuousLinearMap.iteratedFDeriv_comp_left`), and puts the extra
order back with `norm_iteratedFDeriv_fderiv`. Smoothness is assumed outright, which is what removes
all order bookkeeping and is what a Schwartz integrand supplies. -/
theorem norm_dirDeriv_le :
    ∀ (hs : List H) (F : H → α → E), (∀ a, ContDiff ℝ (⊤ : ℕ∞) fun y => F y a) →
      ∀ (x : H) (a : α),
        ‖dirDeriv F hs x a‖
          ≤ ‖iteratedFDeriv ℝ hs.length (fun y => F y a) x‖ * dirWeight hs := by
  intro hs
  induction hs using List.reverseRecOn with
  | nil =>
      intro F _ x a
      simp [norm_iteratedFDeriv_zero]
  | append_singleton hs h ih =>
      intro F hsm x a
      -- the innermost derivative, as a left composition with evaluation at `h`
      have hfd : ∀ a, ContDiff ℝ (⊤ : ℕ∞) fun y => fderiv ℝ (fun z => F z a) y := fun a =>
        (hsm a).fderiv_right (by exact_mod_cast le_top)
      have hG : ∀ a, ContDiff ℝ (⊤ : ℕ∞) fun y => dirDeriv F [h] y a := fun a =>
        (hfd a).clm_apply contDiff_const
      have hcomp : (fun y => dirDeriv F [h] y a)
          = (ContinuousLinearMap.apply ℝ E h) ∘ fun y => fderiv ℝ (fun z => F z a) y := rfl
      have hiter : iteratedFDeriv ℝ hs.length (fun y => dirDeriv F [h] y a) x
          = (ContinuousLinearMap.apply ℝ E h).compContinuousMultilinearMap
              (iteratedFDeriv ℝ hs.length (fun y => fderiv ℝ (fun z => F z a) y) x) := by
        rw [hcomp]
        exact (ContinuousLinearMap.apply ℝ E h).iteratedFDeriv_comp_left
          ((hfd a).contDiffAt) (by exact_mod_cast le_top)
      have hnorm : ‖iteratedFDeriv ℝ hs.length (fun y => dirDeriv F [h] y a) x‖
          ≤ ‖h‖ * ‖iteratedFDeriv ℝ (hs.length + 1) (fun y => F y a) x‖ := by
        rw [hiter]
        calc ‖(ContinuousLinearMap.apply ℝ E h).compContinuousMultilinearMap
                (iteratedFDeriv ℝ hs.length (fun y => fderiv ℝ (fun z => F z a) y) x)‖
            ≤ ‖ContinuousLinearMap.apply ℝ E h‖
                * ‖iteratedFDeriv ℝ hs.length (fun y => fderiv ℝ (fun z => F z a) y) x‖ :=
              ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
          _ ≤ ‖h‖ * ‖iteratedFDeriv ℝ (hs.length + 1) (fun y => F y a) x‖ := by
              gcongr
              · exact norm_applyCLM_le h
              · rw [norm_iteratedFDeriv_fderiv]
      -- assemble
      have hIH := ih (dirDeriv F [h]) hG x a
      rw [dirDeriv_append_singleton] at hIH
      rw [dirWeight_append_singleton, List.length_append, List.length_cons, List.length_nil]
      calc ‖dirDeriv F (hs ++ [h]) x a‖
          ≤ ‖iteratedFDeriv ℝ hs.length (fun y => dirDeriv F [h] y a) x‖ * dirWeight hs := hIH
        _ ≤ ‖h‖ * ‖iteratedFDeriv ℝ (hs.length + 1) (fun y => F y a) x‖ * dirWeight hs := by
            gcongr
            exact dirWeight_nonneg hs
        _ = ‖iteratedFDeriv ℝ (hs.length + 0 + 1) (fun y => F y a) x‖ * (dirWeight hs * ‖h‖) := by
            simp; ring

/-- ★★ **The multilinear form of this file's theorem**, for a user whose bounds come from
`iteratedFDeriv` — which is what `SchwartzMap.decay` gives. It is a corollary of the directional form,
which is the claim the header makes. -/
theorem contDiffOn_integral_of_iteratedFDeriv_bound {F : H → α → E} {U : Set H}
    {bound : ℕ → α → ℝ} (hU : IsOpen U)
    (hsm : ∀ a, ContDiff ℝ (⊤ : ℕ∞) fun x => F x a)
    (hmeas : ∀ (hs : List H) (x : H), AEStronglyMeasurable (fun a => dirDeriv F hs x a) μ)
    (hmeasD : ∀ (hs : List H) (x : H),
      AEStronglyMeasurable (fun a => fderiv ℝ (fun y => dirDeriv F hs y a) x) μ)
    (hint : ∀ k : ℕ, Integrable (bound k) μ)
    (hb0 : ∀ (k : ℕ) (a : α), 0 ≤ bound k a)
    (hbd : ∀ (k : ℕ), ∀ x ∈ U, ∀ a, ‖iteratedFDeriv ℝ k (fun y => F y a) x‖ ≤ bound k a)
    (m : ℕ) :
    ContDiffOn ℝ (m : ℕ) (fun x => ∫ a, F x a ∂μ) U := by
  refine contDiffOn_integral_of_dirBound_all hU (fun k a => (hsm a).of_le (by exact_mod_cast le_top))
    hmeas hmeasD hint hb0 (fun hs x hx a => ?_) m
  calc ‖dirDeriv F hs x a‖
      ≤ ‖iteratedFDeriv ℝ hs.length (fun y => F y a) x‖ * dirWeight hs :=
        norm_dirDeriv_le hs F hsm x a
    _ ≤ bound hs.length a * dirWeight hs :=
        mul_le_mul_of_nonneg_right (hbd hs.length x hx a) (dirWeight_nonneg hs)
    _ = dirWeight hs * bound hs.length a := by ring

end
