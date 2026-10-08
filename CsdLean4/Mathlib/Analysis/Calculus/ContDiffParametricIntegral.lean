/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Differentiation under the integral sign, to all orders

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #120, out of #92's split.

Mathlib differentiates a parametric integral **once** (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`
and its `fderiv` siblings). The corpus differentiates one to **all** orders, but only for an *interval*
integral on a compact interval
([`ContDiffParametricIntervalIntegral.lean`](ContDiffParametricIntervalIntegral.lean), #60), where the
bounds come free from continuity on a compact set. For an integral over a general measure space there
is no such shortcut and the bounds have to be hypotheses. This file supplies that.

* `partialDeriv F k` — the `k`-th derivative of `F` in its **parameter**, by recursion rather than
  through `iteratedDeriv`, so the induction below shifts the order with no API friction;
  ★ `partialDeriv_eq_iteratedDeriv` is the bridge for discharging bounds either way, and
  ★ `partialDeriv_succ_left` is the shift the induction runs on;
* ★★★ `contDiffOn_integral_of_bound` — **the theorem**: if each `x ↦ F x a` is `C^n`, each
  `partialDeriv F k x` is measurable, and each is bounded on an open `U` by an integrable function of
  `a` **uniformly in the parameter**, then `x ↦ ∫ a, F x a` is `C^n` on `U`;
* ★★ `contDiff_integral_of_bound` — the global corollary, and ★★
  `contDiffOn_integral_of_bound_all` smoothness at every order.

## The hypotheses are the statement

⚠️ The row that opened this warned that a version with hypotheses nobody can discharge would be
worse than none, so they are chosen to be checkable: the bound is **one integrable function per
order**, valid for every parameter in `U` — not a Lipschitz modulus, and not something per-point. The
`U` is there because that is how such bounds actually arise: for a kernel like `K ((x + y)/2, x − y)`
the majorant depends on where the parameter sits, so a bound uniform on a ball is available and a
globally uniform one is not. `ContDiffOn` on an open set is exactly what that buys, and
`contDiff_integral_of_bound` is the special case `U = univ` for the rarer situation where the bound
really is global.

▸ **The derivative formula is now exported too** (added 2026-10-08, #125). The original version of
this file recorded only the smoothness, with a scope note saying the identity was "a by-product of
each induction step" that "nothing here needs". #122's decay half and #121(ii) both needed it —
without a formula for `∂ᵏ(∫ F)` there is nothing to move a polynomial weight onto — so
★★★ `hasDerivAt_integral_of_bound` states the first-order identity and
★★★ `iteratedDeriv_integral_of_bound` iterates it: on an open `U`, the `n`-th derivative of the
integral is the integral of the `n`-th parameter derivative. `iteratedDeriv_integral_of_bound_le` is
the every-order-up-to-`n` form a consumer wants, and `integrable_partialDeriv` is the integrability
the formula is false without. The smoothness theorem now *calls* the first-order identity rather than
re-proving it inline.

⚠️ **Parameter in `ℝ`.** The integration variable ranges over an arbitrary measure space, but the
parameter is one-dimensional, which is what lets the proof use `deriv` throughout and keeps the
bounds scalar. The `fderiv` version over a finite-dimensional parameter is the same induction with
`ContinuousLinearMap` plumbing and is not done here.

References: `Mathlib/Analysis/Calculus/ParametricIntegral.lean` (the first derivative),
[`ContDiffParametricIntervalIntegral.lean`](ContDiffParametricIntervalIntegral.lean) (#60, the
compact-interval case at all orders); `specs/BACKLOG.md` #120, #92, #60, #88.
-/

@[expose] public section

open MeasureTheory Metric Set SchwartzMap

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The parameter's iterated derivative -/

/-- The `k`-th derivative of `F` in its first (parameter) slot. -/
noncomputable def partialDeriv (F : ℝ → α → E) : ℕ → ℝ → α → E
  | 0 => F
  | k + 1 => fun x a => deriv (fun x => partialDeriv F k x a) x

@[simp] theorem partialDeriv_zero (F : ℝ → α → E) : partialDeriv F 0 = F := rfl

theorem partialDeriv_succ (F : ℝ → α → E) (k : ℕ) :
    partialDeriv F (k + 1) = fun x a => deriv (fun x => partialDeriv F k x a) x := rfl

/-- ★ **The bridge to `iteratedDeriv`**, so a user can discharge the bounds with either vocabulary. -/
theorem partialDeriv_eq_iteratedDeriv (F : ℝ → α → E) (k : ℕ) (x : ℝ) (a : α) :
    partialDeriv F k x a = iteratedDeriv k (fun x => F x a) x := by
  induction k generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      rw [partialDeriv_succ, iteratedDeriv_succ]
      exact congrArg (fun f => deriv f x) (funext fun y => ih y)

/-- ★ **The shift the induction runs on**: differentiating once and then `k` times is differentiating
`k + 1` times. -/
theorem partialDeriv_succ_left (F : ℝ → α → E) (k : ℕ) :
    partialDeriv (partialDeriv F 1) k = partialDeriv F (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [partialDeriv_succ (partialDeriv F 1) k, ih, ← partialDeriv_succ]

/-- The parameter-smoothness of `F` passes to its parameter derivative. -/
theorem contDiff_partialDeriv_one {F : ℝ → α → E} {n : ℕ}
    (hF : ∀ a, ContDiff ℝ ((n : ℕ) + 1 : ℕ) fun x => F x a) (a : α) :
    ContDiff ℝ (n : ℕ) fun x => partialDeriv F 1 x a := by
  have h := hF a
  rw [show (((n : ℕ) + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 from by push_cast; ring,
    contDiff_succ_iff_deriv] at h
  exact h.2.2

variable [MeasurableSpace α] {μ : Measure α}

/-! ### The theorem -/

/-! ### One derivative, with the derivative

The first-order identity is proved here rather than inside the induction below, because #122's decay
half and #121(ii) need the *derivative*, not only the smoothness, and a statement that discards it
cannot be reused. The smoothness theorem then calls it. -/

/-- The parameter derivatives are integrable, which the formula below is false without. -/
theorem integrable_partialDeriv {F : ℝ → α → E} {U : Set ℝ} {bound : ℕ → α → ℝ} {n k : ℕ}
    (hk : k ≤ n)
    (hmeas : ∀ k, k ≤ n → ∀ x, AEStronglyMeasurable (partialDeriv F k x) μ)
    (hint : ∀ k, k ≤ n → Integrable (bound k) μ)
    (hbd : ∀ k, k ≤ n → ∀ x ∈ U, ∀ a, ‖partialDeriv F k x a‖ ≤ bound k a)
    {x : ℝ} (hx : x ∈ U) : Integrable (partialDeriv F k x) μ := by
  refine (hint k hk).mono' (hmeas k hk x) ?_
  filter_upwards with a using hbd k hk x hx a

/-- ★★★ **Differentiation under the integral sign, with the derivative.** The identity
`contDiffOn_integral_of_bound` proves and throws away. -/
theorem hasDerivAt_integral_of_bound {F : ℝ → α → E} {U : Set ℝ} {bound : ℕ → α → ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hU : IsOpen U)
    (hsm : ∀ a, ContDiff ℝ (n : ℕ) fun x => F x a)
    (hmeas : ∀ k, k ≤ n → ∀ x, AEStronglyMeasurable (partialDeriv F k x) μ)
    (hint : ∀ k, k ≤ n → Integrable (bound k) μ)
    (hbd : ∀ k, k ≤ n → ∀ x ∈ U, ∀ a, ‖partialDeriv F k x a‖ ≤ bound k a)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, partialDeriv F 1 x a ∂μ) x := by
  have hFdiff : ∀ (a : α) (y : ℝ), HasDerivAt (fun x => F x a) (partialDeriv F 1 y a) y := by
    intro a y
    have h1 : Differentiable ℝ fun x => F x a := by
      refine (hsm a).differentiable ?_
      exact_mod_cast Nat.one_le_iff_ne_zero.1 hn
    exact (h1 y).hasDerivAt
  have hF0 : Integrable (F x) μ :=
    integrable_partialDeriv (n := n) (k := 0) (by omega) hmeas hint hbd hx
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (bound := bound 1)
    (F' := fun x a => partialDeriv F 1 x a) (hU.mem_nhds hx) ?_ hF0
    (hmeas 1 hn x) ?_ (hint 1 hn) ?_).2
  · filter_upwards with y using hmeas 0 (by omega) y
  · filter_upwards with a
    intro y hy
    exact hbd 1 hn y hy a
  · filter_upwards with a
    intro y _
    exact hFdiff a y

/-- ★★★ **Differentiation under the integral sign, to all orders.** If each `x ↦ F x a` is `C^n` in
the parameter, each parameter derivative is measurable in `a`, and the `k`-th one is bounded on an
open `U` by an integrable `bound k` uniformly in the parameter, then the integral is `C^n` on `U`. -/
theorem contDiffOn_integral_of_bound (n : ℕ) :
    ∀ (F : ℝ → α → E) (U : Set ℝ) (bound : ℕ → α → ℝ), IsOpen U →
      (∀ a, ContDiff ℝ (n : ℕ) fun x => F x a) →
      (∀ k, k ≤ n → ∀ x, AEStronglyMeasurable (partialDeriv F k x) μ) →
      (∀ k, k ≤ n → Integrable (bound k) μ) →
      (∀ k, k ≤ n → ∀ x ∈ U, ∀ a, ‖partialDeriv F k x a‖ ≤ bound k a) →
      ContDiffOn ℝ (n : ℕ) (fun x => ∫ a, F x a ∂μ) U := by
  induction n with
  | zero =>
      intro F U bound hU hsm hmeas hint hbd
      rw [Nat.cast_zero, contDiffOn_zero]
      intro x hx
      refine ContinuousAt.continuousWithinAt ?_
      refine continuousAt_of_dominated (bound := bound 0) ?_ ?_ (hint 0 le_rfl) ?_
      · filter_upwards with y using hmeas 0 le_rfl y
      · filter_upwards [hU.mem_nhds hx] with y hy
        filter_upwards with a using hbd 0 le_rfl y hy a
      · filter_upwards with a
        exact ((hsm a).continuous).continuousAt
  | succ n ih =>
      intro F U bound hU hsm hmeas hint hbd
      have hcast : (((n : ℕ) + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; ring
      -- the parameter derivative, and its own hypotheses
      have hGsm : ∀ a, ContDiff ℝ (n : ℕ) fun x => partialDeriv F 1 x a :=
        contDiff_partialDeriv_one hsm
      -- the integral is differentiable on `U`, with the expected derivative
      have hderiv : ∀ x ∈ U, HasDerivAt (fun x => ∫ a, F x a ∂μ)
          (∫ a, partialDeriv F 1 x a ∂μ) x := fun x hx =>
        hasDerivAt_integral_of_bound (n := n + 1) (by omega) hU hsm hmeas hint hbd hx
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun x hx => ((hderiv x hx).differentiableAt).differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      -- the derivative is the integral of the parameter derivative, which the hypothesis covers
      have hGcd : ContDiffOn ℝ (n : ℕ) (fun x => ∫ a, partialDeriv F 1 x a ∂μ) U := by
        refine ih (partialDeriv F 1) U (fun k => bound (k + 1)) hU hGsm ?_ ?_ ?_
        · intro k hk x
          rw [partialDeriv_succ_left]
          exact hmeas (k + 1) (by omega) x
        · intro k hk
          exact hint (k + 1) (by omega)
        · intro k hk x hx a
          rw [partialDeriv_succ_left]
          exact hbd (k + 1) (by omega) x hx a
      refine hGcd.congr fun x hx => ?_
      exact (hderiv x hx).deriv

/-- ★★ **The global corollary**, for the rarer case where the bounds hold for every parameter. -/
theorem contDiff_integral_of_bound {n : ℕ} {F : ℝ → α → E} {bound : ℕ → α → ℝ}
    (hsm : ∀ a, ContDiff ℝ (n : ℕ) fun x => F x a)
    (hmeas : ∀ k, k ≤ n → ∀ x, AEStronglyMeasurable (partialDeriv F k x) μ)
    (hint : ∀ k, k ≤ n → Integrable (bound k) μ)
    (hbd : ∀ k, k ≤ n → ∀ (x : ℝ) (a : α), ‖partialDeriv F k x a‖ ≤ bound k a) :
    ContDiff ℝ (n : ℕ) fun x => ∫ a, F x a ∂μ := by
  rw [← contDiffOn_univ]
  exact contDiffOn_integral_of_bound n F univ bound isOpen_univ hsm hmeas hint
    fun k hk x _ a => hbd k hk x a

/-- ★★ **Smoothness at every order.** Bounds at every order give `C^m` on `U` for every `m`, stated
over `ℕ` so that no `∞`-coercion enters the interface. -/
theorem contDiffOn_integral_of_bound_all {F : ℝ → α → E} {U : Set ℝ} {bound : ℕ → α → ℝ}
    (hU : IsOpen U) (hsm : ∀ (m : ℕ) (a : α), ContDiff ℝ (m : ℕ) fun x => F x a)
    (hmeas : ∀ (k : ℕ) (x : ℝ), AEStronglyMeasurable (partialDeriv F k x) μ)
    (hint : ∀ k : ℕ, Integrable (bound k) μ)
    (hbd : ∀ (k : ℕ), ∀ x ∈ U, ∀ a, ‖partialDeriv F k x a‖ ≤ bound k a) (m : ℕ) :
    ContDiffOn ℝ (m : ℕ) (fun x => ∫ a, F x a ∂μ) U :=
  contDiffOn_integral_of_bound m F U bound hU (hsm m) (fun k _ x => hmeas k x)
    (fun k _ => hint k) fun k _ x hx a => hbd k x hx a

/-! ### The interface is dischargeable

The row that opened this warned that hypotheses nobody can discharge would be worse than none, so
here is a consumer that discharges all four of them, and is a theorem worth having on its own:
**convolution with a Schwartz function is smooth**, for any integrable weight. Each hypothesis is met
by one fact about Schwartz functions — the `k`-th derivative is bounded (`decay 0 k`) uniformly, which
is exactly the "uniformly in the parameter" the bound family asks for. -/

/-- The parameter derivatives of a translated Schwartz function against a weight. -/
theorem partialDeriv_sub_mul (f : 𝓢(ℝ, ℂ)) (g : ℝ → ℂ) (k : ℕ) (x t : ℝ) :
    partialDeriv (fun x t => f (x - t) * g t) k x t = iteratedDeriv k f (x - t) * g t := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [partialDeriv_succ]
      calc deriv (fun x => partialDeriv (fun x t => f (x - t) * g t) k x t) x
          = deriv (fun x => iteratedDeriv k f (x - t) * g t) x := by
            exact congrArg (fun h => deriv h x) (funext fun y => ih y)
        _ = deriv (fun x => iteratedDeriv k f (x - t)) x * g t := by
            exact deriv_mul_const_field (g t)
        _ = iteratedDeriv (k + 1) f (x - t) * g t := by
            rw [deriv_comp_sub_const, ← iteratedDeriv_succ]

/-- An iterated derivative of a Schwartz function is bounded. -/
theorem exists_bound_iteratedDeriv (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖iteratedDeriv k f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.decay 0 k
  refine ⟨C, hC.1.le, fun x => ?_⟩
  have h := hC.2 x
  rwa [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h

/-- ★★★ **Convolution with a Schwartz function is smooth to every order**, for any integrable weight
— and every hypothesis of `contDiffOn_integral_of_bound` is discharged along the way. -/
theorem contDiff_integral_schwartz_sub_mul (f : 𝓢(ℝ, ℂ)) {g : ℝ → ℂ}
    (hg : Integrable g) (m : ℕ) :
    ContDiff ℝ (m : ℕ) fun x => ∫ t, f (x - t) * g t := by
  classical
  -- one bound per order, uniform in the parameter
  choose C hC0 hC using fun k => exists_bound_iteratedDeriv f k
  refine contDiff_integral_of_bound (bound := fun k t => C k * ‖g t‖) ?_ ?_ ?_ ?_
  · intro t
    exact ((f.smooth'.of_le (by exact_mod_cast le_top)).comp
      (contDiff_id.sub contDiff_const)).mul contDiff_const
  · intro k _ x
    have heq : partialDeriv (fun x t => f (x - t) * g t) k x
        = fun t => iteratedDeriv k f (x - t) * g t :=
      funext fun t => partialDeriv_sub_mul f g k x t
    rw [heq]
    have hcont : Continuous fun t : ℝ => iteratedDeriv k f (x - t) :=
      (f.smooth'.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp
        (continuous_const.sub continuous_id)
    exact hcont.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · intro k _
    exact (hg.norm.const_mul (C k))
  · intro k _ x t
    rw [partialDeriv_sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC k (x - t)) (norm_nonneg _)

/-! ### The formula at every order -/

/-- ★★★ **The formula at every order.** On an open `U`, the `n`-th derivative of the integral is the
integral of the `n`-th parameter derivative. The induction is the same shift
(`partialDeriv_succ_left`) the smoothness proof runs on, with the identity kept instead of
discarded; locality of `iteratedDeriv` on the open set is what lets the first-order identity be
substituted under the remaining derivatives. -/
theorem iteratedDeriv_integral_of_bound (n : ℕ) :
    ∀ (F : ℝ → α → E) (U : Set ℝ) (bound : ℕ → α → ℝ), IsOpen U →
      (∀ a, ContDiff ℝ (n : ℕ) fun x => F x a) →
      (∀ k, k ≤ n → ∀ x, AEStronglyMeasurable (partialDeriv F k x) μ) →
      (∀ k, k ≤ n → Integrable (bound k) μ) →
      (∀ k, k ≤ n → ∀ x ∈ U, ∀ a, ‖partialDeriv F k x a‖ ≤ bound k a) →
      ∀ x ∈ U, iteratedDeriv n (fun x => ∫ a, F x a ∂μ) x = ∫ a, partialDeriv F n x a ∂μ := by
  induction n with
  | zero =>
      intro F U bound _ _ _ _ _ x _
      simp [iteratedDeriv_zero]
  | succ n ih =>
      intro F U bound hU hsm hmeas hint hbd x hx
      -- the first-order identity, on all of `U`
      have hd1 : ∀ y ∈ U, deriv (fun x => ∫ a, F x a ∂μ) y = ∫ a, partialDeriv F 1 y a ∂μ :=
        fun y hy =>
          (hasDerivAt_integral_of_bound (n := n + 1) (by omega) hU hsm hmeas hint hbd hy).deriv
      have heq : deriv (fun x => ∫ a, F x a ∂μ)
          =ᶠ[nhds x] fun y => ∫ a, partialDeriv F 1 y a ∂μ := by
        filter_upwards [hU.mem_nhds hx] with y hy using hd1 y hy
      -- the inner call, on the parameter derivative
      have hGsm : ∀ a, ContDiff ℝ (n : ℕ) fun y => partialDeriv F 1 y a :=
        contDiff_partialDeriv_one hsm
      have hmeas' : ∀ k, k ≤ n → ∀ y,
          AEStronglyMeasurable (partialDeriv (partialDeriv F 1) k y) μ := by
        intro k hk y
        rw [partialDeriv_succ_left]
        exact hmeas (k + 1) (by omega) y
      have hbd' : ∀ k, k ≤ n → ∀ y ∈ U, ∀ a,
          ‖partialDeriv (partialDeriv F 1) k y a‖ ≤ bound (k + 1) a := by
        intro k hk y hy a
        rw [partialDeriv_succ_left]
        exact hbd (k + 1) (by omega) y hy a
      have hIH := ih (partialDeriv F 1) U (fun k => bound (k + 1)) hU hGsm hmeas'
        (fun k hk => hint (k + 1) (by omega)) hbd' x hx
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq, hIH, partialDeriv_succ_left]

/-- ★★ The formula at every order up to `n`, which is the form a consumer wants. -/
theorem iteratedDeriv_integral_of_bound_le {F : ℝ → α → E} {U : Set ℝ} {bound : ℕ → α → ℝ} {n : ℕ}
    (hU : IsOpen U)
    (hsm : ∀ a, ContDiff ℝ (n : ℕ) fun x => F x a)
    (hmeas : ∀ k, k ≤ n → ∀ x, AEStronglyMeasurable (partialDeriv F k x) μ)
    (hint : ∀ k, k ≤ n → Integrable (bound k) μ)
    (hbd : ∀ k, k ≤ n → ∀ x ∈ U, ∀ a, ‖partialDeriv F k x a‖ ≤ bound k a)
    {k : ℕ} (hk : k ≤ n) {x : ℝ} (hx : x ∈ U) :
    iteratedDeriv k (fun x => ∫ a, F x a ∂μ) x = ∫ a, partialDeriv F k x a ∂μ :=
  iteratedDeriv_integral_of_bound k F U bound hU
    (fun a => (hsm a).of_le (by exact_mod_cast hk))
    (fun j hj => hmeas j (by omega)) (fun j hj => hint j (by omega))
    (fun j hj => hbd j (by omega)) x hx

end
