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
* ★★★ `hasFDerivAt_integral_of_bound` and ★★ `fderiv_integral_apply_of_bound` — **the first-order
  identity**, which the induction proves and the smoothness statement discards. Exported for #126
  with the weakest hypotheses that give it — differentiability of each slice, not smoothness — and in
  directional form; the induction now *calls* it rather than rebuilding it;
* ★★★ `norm_iteratedFDeriv_integral_le` — **the bound at every order**: under the same hypotheses,
  `‖iteratedFDeriv ℝ n (∫ a, F · a) x‖ ≤ ∫ a, bound n a` on `U`, by an induction that peels the last
  direction (`iteratedFDeriv_apply_succ_last`) and substitutes the first-order identity under the
  remaining derivatives (`Filter.EventuallyEq.iteratedFDeriv_eq`, which Mathlib has only for
  `iteratedFDerivWithin`). This is the shape a Schwartz seminorm estimate asks for;
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

⚠️ ~~**No formula for the derivatives**, as in #120.~~ **Amended 2026-10-08 (#126).** The
first-order identity is now exported, and at higher order what is exported is the **bound** it
implies, not the identity. The identity at order `n` would need the iterated derivative of the
integral *as a multilinear map* — the plumbing this file exists to avoid — and no consumer has wanted
it: a Schwartz estimate wants a scalar bound.

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

/-! ### The first-order identity, which the induction needs and a consumer wants

The induction below proves `fderiv (∫ a, F · a) x = ∫ a, fderiv (F · a) x` at each step and then
keeps only the smoothness. #125 made that identity an exported theorem for #120's one-dimensional
parameter; here it is for a parameter in any normed space, stated with the weakest hypotheses that
give it — differentiability of each slice, not smoothness — so that the induction can call it instead
of rebuilding it. -/

omit [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace ℝ E] [FiniteDimensional ℝ H] in
/-- The integrand is integrable wherever the order-zero bound holds, which every statement here
needs. -/
theorem integrable_of_bound {F : H → α → E} {U : Set H} {b₀ : α → ℝ}
    (hmeas : ∀ x, AEStronglyMeasurable (fun a => F x a) μ) (hint₀ : Integrable b₀ μ)
    (hbd₀ : ∀ x ∈ U, ∀ a, ‖F x a‖ ≤ b₀ a) {x : H} (hx : x ∈ U) :
    Integrable (fun a => F x a) μ :=
  hint₀.mono' (hmeas x) (Filter.Eventually.of_forall (hbd₀ x hx))

omit [FiniteDimensional ℝ H] in
/-- ★★★ **Differentiation under the integral sign over a normed parameter, with the derivative
kept.** The identity `contDiffOn_integral_of_dirBound` proves and discards. -/
theorem hasFDerivAt_integral_of_bound {F : H → α → E} {U : Set H} {b₀ b₁ : α → ℝ}
    (hU : IsOpen U) (hdiff : ∀ a, Differentiable ℝ fun y => F y a)
    (hmeas : ∀ x, AEStronglyMeasurable (fun a => F x a) μ)
    (hmeasD : ∀ x, AEStronglyMeasurable (fun a => fderiv ℝ (fun y => F y a) x) μ)
    (hint₀ : Integrable b₀ μ) (hint₁ : Integrable b₁ μ)
    (hbd₀ : ∀ x ∈ U, ∀ a, ‖F x a‖ ≤ b₀ a)
    (hbd₁ : ∀ x ∈ U, ∀ a, ‖fderiv ℝ (fun y => F y a) x‖ ≤ b₁ a)
    {x : H} (hx : x ∈ U) :
    HasFDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, fderiv ℝ (fun y => F y a) x ∂μ) x := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b₁)
    (F' := fun x a => fderiv ℝ (fun y => F y a) x) (hU.mem_nhds hx) ?_
    (integrable_of_bound hmeas hint₀ hbd₀ hx) (hmeasD x) ?_ hint₁ ?_
  · filter_upwards with y using hmeas y
  · filter_upwards with a
    intro y hy
    exact hbd₁ y hy a
  · filter_upwards with a
    intro y _
    exact (hdiff a y).hasFDerivAt

omit [FiniteDimensional ℝ H] in
/-- The first derivative is integrable, which is what lets the identity above be evaluated at a
direction. -/
theorem integrable_fderiv_of_bound {F : H → α → E} {U : Set H} {b₁ : α → ℝ}
    (hmeasD : ∀ x, AEStronglyMeasurable (fun a => fderiv ℝ (fun y => F y a) x) μ)
    (hint₁ : Integrable b₁ μ)
    (hbd₁ : ∀ x ∈ U, ∀ a, ‖fderiv ℝ (fun y => F y a) x‖ ≤ b₁ a)
    {x : H} (hx : x ∈ U) : Integrable (fun a => fderiv ℝ (fun y => F y a) x) μ :=
  hint₁.mono' (hmeasD x) (Filter.Eventually.of_forall (hbd₁ x hx))

omit [FiniteDimensional ℝ H] in
/-- ★★ **The directional form of the identity**, in this file's own vocabulary: no operator-valued
integral survives in the statement. -/
theorem fderiv_integral_apply_of_bound {F : H → α → E} {U : Set H} {b₀ b₁ : α → ℝ}
    (hU : IsOpen U) (hdiff : ∀ a, Differentiable ℝ fun y => F y a)
    (hmeas : ∀ x, AEStronglyMeasurable (fun a => F x a) μ)
    (hmeasD : ∀ x, AEStronglyMeasurable (fun a => fderiv ℝ (fun y => F y a) x) μ)
    (hint₀ : Integrable b₀ μ) (hint₁ : Integrable b₁ μ)
    (hbd₀ : ∀ x ∈ U, ∀ a, ‖F x a‖ ≤ b₀ a)
    (hbd₁ : ∀ x ∈ U, ∀ a, ‖fderiv ℝ (fun y => F y a) x‖ ≤ b₁ a)
    {x : H} (hx : x ∈ U) (h : H) :
    fderiv ℝ (fun x => ∫ a, F x a ∂μ) x h = ∫ a, dirDeriv F [h] x a ∂μ := by
  rw [(hasFDerivAt_integral_of_bound hU hdiff hmeas hmeasD hint₀ hint₁ hbd₀ hbd₁ hx).fderiv,
    ContinuousLinearMap.integral_apply (integrable_fderiv_of_bound hmeasD hint₁ hbd₁ hx) h]
  rfl


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
      have hdiff : ∀ a, Differentiable ℝ fun y => F y a := by
        intro a
        have h := hsm a
        rw [hcast] at h
        exact h.differentiable (by simp)
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
          (∫ a, fderiv ℝ (fun y => F y a) x ∂μ) x := fun x hx =>
        hasFDerivAt_integral_of_bound hU hdiff (fun y => hmeas [] (by simp) y)
          (fun y => hmeasD [] (by simp) y) (hint 0 (by omega)) (hint 1 (by omega))
          (fun y hy a => by simpa using hbd [] (by simp) y hy a)
          (fun y hy a => hopbd y hy a) hx
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


/-! ### The bound at every order, which is what a Schwartz estimate asks for

The first-order identity above is not enough for a consumer: a Schwartz seminorm estimate needs
`‖iteratedFDeriv ℝ n (∫ a, F · a) x‖`, and *stating* the identity at order `n` would need the
iterated derivative of the integral as a multilinear map — exactly the plumbing this file exists to
avoid. The bound is scalar, follows from the first-order identity by the same list-append induction,
and is what #126 consumes.

The peel is `iteratedFDeriv_apply_succ_last`: Mathlib's `iteratedFDeriv_succ_apply_right` peels one
order into a function *valued* in `H →L[ℝ] E`, and composing with evaluation at the last direction
puts the value back in `E`. -/

omit [FiniteDimensional ℝ H] in
/-- Two functions that agree near a point have the same iterated derivatives there. Mathlib has the
`iteratedFDerivWithin` version only. -/
theorem Filter.EventuallyEq.iteratedFDeriv_eq {f g : H → E} {x : H} (h : f =ᶠ[nhds x] g) (n : ℕ) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
  refine Filter.EventuallyEq.iteratedFDerivWithin_eq ?_ h.self_of_nhds n
  rwa [nhdsWithin_univ]

omit [FiniteDimensional ℝ H] in
/-- One order of `iteratedFDeriv`, applied to a tuple, is the `iteratedFDeriv` of one order less of
the derivative along the tuple's **last** direction — the same innermost-first peeling
`dirDeriv_append_singleton` performs, and for the same reason: the head of a tuple is the outermost
derivative, which is not of this form. -/
theorem iteratedFDeriv_apply_succ_last {f : H → E} {x : H} {n : ℕ}
    (hf : ContDiffAt ℝ ((n : ℕ) + 1 : ℕ) f x) (v : Fin (n + 1) → H) :
    (iteratedFDeriv ℝ (n + 1) f x : (Fin (n + 1) → H) → E) v
      = (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (v (Fin.last n))) x : (Fin n → H) → E)
          (Fin.init v) := by
  have hfd : ContDiffAt ℝ (n : ℕ) (fun y => fderiv ℝ f y) x := hf.fderiv_right (by push_cast; rfl)
  have hcomp : (fun y => fderiv ℝ f y (v (Fin.last n)))
      = (ContinuousLinearMap.apply ℝ E (v (Fin.last n))) ∘ fun y => fderiv ℝ f y := rfl
  rw [iteratedFDeriv_succ_apply_right, hcomp,
    (ContinuousLinearMap.apply ℝ E (v (Fin.last n))).iteratedFDeriv_comp_left hfd le_rfl]
  rfl

/-- ★★★ **The iterated derivative of the integral obeys the bound family, at every order.** With
the same hypotheses that make the integral smooth, `‖iteratedFDeriv ℝ n (∫ a, F · a) x‖ ≤
∫ a, bound n a` on `U`. The induction peels the last direction, replaces the derivative of the
integral by the integral of the directional derivative (the identity above, valid on all of the open
`U`, hence substitutable under the remaining derivatives), and calls itself on `dirDeriv F [h]` with
the bound family shifted exactly as the smoothness proof shifts it. -/
theorem norm_iteratedFDeriv_integral_le (n : ℕ) :
    ∀ (F : H → α → E) (U : Set H) (bound : ℕ → α → ℝ), IsOpen U →
      (∀ (m : ℕ) (a : α), ContDiff ℝ (m : ℕ) fun x => F x a) →
      (∀ (hs : List H) (x : H), AEStronglyMeasurable (fun a => dirDeriv F hs x a) μ) →
      (∀ (hs : List H) (x : H),
        AEStronglyMeasurable (fun a => fderiv ℝ (fun y => dirDeriv F hs y a) x) μ) →
      (∀ k : ℕ, Integrable (bound k) μ) →
      (∀ (k : ℕ) (a : α), 0 ≤ bound k a) →
      (∀ hs : List H, ∀ x ∈ U, ∀ a, ‖dirDeriv F hs x a‖ ≤ dirWeight hs * bound hs.length a) →
      ∀ x ∈ U, ‖iteratedFDeriv ℝ n (fun x => ∫ a, F x a ∂μ) x‖ ≤ ∫ a, bound n a ∂μ := by
  induction n with
  | zero =>
      intro F U bound _ _ hmeas _ hint hb0 hbd x hx
      rw [norm_iteratedFDeriv_zero]
      refine norm_integral_le_of_norm_le (hint 0) (Filter.Eventually.of_forall fun a => ?_)
      simpa [dirWeight] using hbd [] x hx a
  | succ n ih =>
      intro F U bound hU hsm hmeas hmeasD hint hb0 hbd x hx
      refine ContinuousMultilinearMap.opNorm_le_bound
        (integral_nonneg fun a => hb0 (n + 1) a) fun v => ?_
      -- the hypotheses of the first-order identity, at order one
      have hdiff : ∀ a, Differentiable ℝ fun y => F y a := fun a =>
        (hsm 1 a).differentiable (by norm_num)
      have hbd₀ : ∀ y ∈ U, ∀ a, ‖F y a‖ ≤ bound 0 a := fun y hy a => by
        simpa [dirWeight] using hbd [] y hy a
      have hopbd : ∀ y ∈ U, ∀ a, ‖fderiv ℝ (fun z => F z a) y‖ ≤ bound 1 a := by
        intro y hy a
        refine ContinuousLinearMap.opNorm_le_bound _ (hb0 1 a) fun h => ?_
        have h1 := hbd [h] y hy a
        rw [dirDeriv_cons] at h1
        calc ‖fderiv ℝ (fun z => F z a) y h‖
            ≤ dirWeight [h] * bound (List.length [h]) a := h1
          _ = bound 1 a * ‖h‖ := by simp [dirWeight]; ring
      -- the first-order identity along the last direction, on all of `U`
      have hid : ∀ y ∈ U, fderiv ℝ (fun z => ∫ a, F z a ∂μ) y (v (Fin.last n))
          = ∫ a, dirDeriv F [v (Fin.last n)] y a ∂μ := fun y hy =>
        fderiv_integral_apply_of_bound hU hdiff (fun z => hmeas [] z) (fun z => hmeasD [] z)
          (hint 0) (hint 1) hbd₀ hopbd hy _
      -- peel the last direction off the tuple
      have hcd : ContDiffAt ℝ ((n : ℕ) + 1 : ℕ) (fun y => ∫ a, F y a ∂μ) x :=
        (contDiffOn_integral_of_dirBound_all hU hsm hmeas hmeasD hint hb0 hbd (n + 1)).contDiffAt
          (hU.mem_nhds hx)
      rw [iteratedFDeriv_apply_succ_last hcd v]
      -- and replace the derivative of the integral by the integral of the derivative
      have heq : (fun y => fderiv ℝ (fun z => ∫ a, F z a ∂μ) y (v (Fin.last n)))
          =ᶠ[nhds x] fun y => ∫ a, dirDeriv F [v (Fin.last n)] y a ∂μ := by
        filter_upwards [hU.mem_nhds hx] with y hy using hid y hy
      rw [heq.iteratedFDeriv_eq n]
      -- the inductive hypothesis, on the directional derivative
      have hGsm : ∀ (m : ℕ) (a : α),
          ContDiff ℝ (m : ℕ) fun y => dirDeriv F [v (Fin.last n)] y a := by
        intro m a
        have hcast : (((m : ℕ) + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; ring
        have hF := hsm (m + 1) a
        rw [hcast, contDiff_succ_iff_fderiv] at hF
        exact (hF.2.2).clm_apply contDiff_const
      have hGmeas : ∀ (hs : List H) (y : H),
          AEStronglyMeasurable (fun a => dirDeriv (dirDeriv F [v (Fin.last n)]) hs y a) μ := by
        intro hs y
        rw [dirDeriv_append_singleton]
        exact hmeas (hs ++ [v (Fin.last n)]) y
      have hGmeasD : ∀ (hs : List H) (y : H), AEStronglyMeasurable
          (fun a => fderiv ℝ (fun z => dirDeriv (dirDeriv F [v (Fin.last n)]) hs z a) y) μ := by
        intro hs y
        rw [dirDeriv_append_singleton]
        exact hmeasD (hs ++ [v (Fin.last n)]) y
      have hGbd : ∀ hs : List H, ∀ y ∈ U, ∀ a,
          ‖dirDeriv (dirDeriv F [v (Fin.last n)]) hs y a‖
            ≤ dirWeight hs * (‖v (Fin.last n)‖ * bound (hs.length + 1) a) := by
        intro hs y hy a
        rw [dirDeriv_append_singleton]
        have hb := hbd (hs ++ [v (Fin.last n)]) y hy a
        rw [dirWeight_append_singleton] at hb
        calc ‖dirDeriv F (hs ++ [v (Fin.last n)]) y a‖
            ≤ dirWeight hs * ‖v (Fin.last n)‖ * bound (hs ++ [v (Fin.last n)]).length a := hb
          _ = dirWeight hs * (‖v (Fin.last n)‖ * bound (hs.length + 1) a) := by simp; ring
      have hIH := ih (dirDeriv F [v (Fin.last n)]) U
        (fun k a => ‖v (Fin.last n)‖ * bound (k + 1) a) hU hGsm hGmeas hGmeasD
        (fun k => (hint (k + 1)).const_mul _)
        (fun k a => mul_nonneg (norm_nonneg _) (hb0 (k + 1) a)) hGbd x hx
      -- assemble
      calc ‖(iteratedFDeriv ℝ n (fun y => ∫ a, dirDeriv F [v (Fin.last n)] y a ∂μ) x :
                (Fin n → H) → E) (Fin.init v)‖
          ≤ ‖iteratedFDeriv ℝ n (fun y => ∫ a, dirDeriv F [v (Fin.last n)] y a ∂μ) x‖
              * ∏ i, ‖Fin.init v i‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ (∫ a, ‖v (Fin.last n)‖ * bound (n + 1) a ∂μ) * ∏ i, ‖Fin.init v i‖ := by
            gcongr
        _ = (∫ a, bound (n + 1) a ∂μ) * ∏ i, ‖v i‖ := by
            rw [integral_const_mul, Fin.prod_univ_castSucc]
            simp only [Fin.init]
            ring

end
