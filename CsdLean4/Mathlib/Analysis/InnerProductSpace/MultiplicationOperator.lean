/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.DiagonalOperator
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Multiplication operators on `L²`

**Category:** 1-Mathlib (CSD-free; staged for upstream).

[`DiagonalOperator.lean`](DiagonalOperator.lean) (BACKLOG #93(a)) builds the unbounded-operator layer
the pin lacks — `LinearPMap.IsResolventAt`, `resolventSet`, `spectrum` — and the one operator a
Hilbert basis supplies: the diagonal operator of a real weight family, self-adjoint with spectrum the
closure of the weights. That route needs a basis, so it reaches only operators with discrete
spectrum. This module is its **continuum companion**: multiplication by a real measurable function on
`L²(μ)`, where the spectrum is in general not discrete.

* **the bounded part first**: `mulCLM` is multiplication by a bounded measurable function, through
  Mathlib's Hölder pairing `L^∞ × L² → L²` (the function-indexed companion of
  [`HeatSemigroup.lean`](../Semigroup/HeatSemigroup.lean)'s `potential`), and `cutCLM`, `cutMulCLM`
  are the **cut-offs** `1_{|m| ≤ n}` and `m · 1_{|m| ≤ n}`;
* ★ `ae_eq_zero_of_ae_eq_zero_on_cutSet` — **the cut-offs exhaust `α`**, because `m` is real-valued:
  a function vanishing a.e. on every cut-off set vanishes a.e. This one lemma **replaces every
  limiting argument below** — no dominated convergence appears in this file;
* `mulDomain`, `mulOp` — the natural domain `{f ∈ L² : m f ∈ L²}` and the operator on it;
* ★★ `dense_mulDomain` — **the domain is dense**: a vector orthogonal to it is killed by every
  cut-off (the cut-offs are self-adjoint, `inner_cutCLM`), hence vanishes;
* ★★ `mulOp_isFormalAdjoint` — symmetry, the one place reality of `m` is used; and the content,
  ★★★ `isSelfAdjoint_mulOp` — **multiplication by a real measurable function is self-adjoint on its
  natural domain**. Maximality is `coeFn_adjoint_mulOp`: the adjoint's value agrees with `m · y` on
  every cut-off set, so a vector the adjoint is defined at already has `m · y ∈ L²`;
* ★★ `mem_resolventSet_mulOp` — **off the closure of the values the operator has a bounded inverse**,
  multiplication by `(m − z)⁻¹`; `m/(m − z)` is bounded too, which is what puts the inverse's values
  back in the domain;
* ★★ `mem_spectrum_mulOp` — **every essential value is in the spectrum**: the normalised indicators
  of `m⁻¹(ball λ ε)` are approximate eigenvectors, so a bounded inverse would have to stretch one of
  them by more than its own norm. Together with the previous item this pins the spectrum between the
  essential values and the closure of all values.

## Honest scope

⚠️ **`m` is real**, which is what makes the operator self-adjoint; a complex multiplier gives a
normal operator and nothing here is stated for that case.

⚠️ **No spectral theorem and no functional calculus.** The spectrum is characterised by the two
one-sided statements above, not computed in general: identifying it with the essential range needs
the measure, which is done for the free Hamiltonian in
[`../Semigroup/FreeHamiltonian.lean`](../Semigroup/FreeHamiltonian.lean) and not in general. There is
no projection-valued measure here (MATHLIB-ABSENT(LinearPMap.spectralMeasure)), and Mathlib has no
multiplication operator on `Lp` to build on (MATHLIB-ABSENT(MeasureTheory.multiplicationOperator)).

⚠️ **Nothing about generated groups.** Stone's theorem is absent from the pin
(MATHLIB-ABSENT(LinearPMap.stoneTheorem)), so no statement here connects a self-adjoint operator to a
one-parameter unitary group; the corpus's propagators are built directly as Fourier multipliers.

References: M. Reed, B. Simon, *Methods of Modern Mathematical Physics* I §VII.2 and §VIII.3 (the
multiplication operator and its spectrum); `DiagonalOperator.lean` (BACKLOG #93(a));
`specs/BACKLOG.md` #64; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal LinearPMap

noncomputable section

namespace MeasureTheory.L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : α → ℝ}

/-! ### Multiplication by a bounded function -/

/-- **Multiplication by a bounded measurable function** as an operator on `L²`, through Mathlib's
Hölder pairing `L^∞ × L² → L²`. This is the function-indexed companion of
`Analysis/Semigroup/HeatSemigroup.lean`'s `potential`, which takes an `L^∞` element; here the bound
is a hypothesis, which is what the cut-offs below need. -/
def mulCLM (g : α → ℂ) (hg : AEStronglyMeasurable g μ) {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 ((memLp_top_of_bound hg C hb).toLp g)

theorem coeFn_mulCLM (g : α → ℂ) (hg : AEStronglyMeasurable g μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp ℂ 2 μ) :
    mulCLM g hg hb f =ᵐ[μ] fun x => g x * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
      ((memLp_top_of_bound hg C hb).toLp g) f,
    (memLp_top_of_bound hg C hb).coeFn_toLp] with x h1 h2
  rw [mulCLM, ContinuousLinearMap.holderL_apply_apply, h1, h2]
  rfl

/-! ### The cut-offs -/

/-- The cut-off set `{|m| ≤ n}`. The cut-offs exhaust `α` because `m` is real-valued, and that is
the only property of them used below. -/
def cutSet (m : α → ℝ) (n : ℕ) : Set α := {x | |m x| ≤ n}

theorem measurableSet_cutSet (hm : Measurable m) (n : ℕ) : MeasurableSet (cutSet m n) :=
  measurableSet_le (continuous_abs.measurable.comp hm) measurable_const

omit [MeasurableSpace α] in
theorem exists_mem_cutSet (x : α) : ∃ n : ℕ, x ∈ cutSet m n := by
  obtain ⟨n, hn⟩ := exists_nat_ge |m x|
  exact ⟨n, hn⟩

theorem aestronglyMeasurable_indicator_cutSet (hm : Measurable m) (n : ℕ) :
    AEStronglyMeasurable (Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ))) μ :=
  (Measurable.indicator measurable_const (measurableSet_cutSet hm n)).aestronglyMeasurable

omit [MeasurableSpace α] in
theorem norm_indicator_cutSet_le (n : ℕ) (x : α) :
    ‖Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ cutSet m n
  · rw [Set.indicator_of_mem hx, norm_one]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    norm_num

theorem aestronglyMeasurable_indicator_cutSet_mul (hm : Measurable m) (n : ℕ) :
    AEStronglyMeasurable (Set.indicator (cutSet m n) (fun x : α => ((m x : ℂ)))) μ :=
  (Measurable.indicator (Complex.measurable_ofReal.comp hm)
    (measurableSet_cutSet hm n)).aestronglyMeasurable

omit [MeasurableSpace α] in
theorem norm_indicator_cutSet_mul_le (n : ℕ) (x : α) :
    ‖Set.indicator (cutSet m n) (fun x : α => ((m x : ℂ))) x‖ ≤ n := by
  by_cases hx : x ∈ cutSet m n
  · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  · rw [Set.indicator_of_notMem hx, norm_zero]
    positivity

/-- Multiplication by the cut-off indicator `1_{|m| ≤ n}`. -/
def cutCLM (hm : Measurable m) (n : ℕ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulCLM _ (aestronglyMeasurable_indicator_cutSet hm n) (C := 1)
    (Eventually.of_forall (norm_indicator_cutSet_le n))

theorem coeFn_cutCLM (hm : Measurable m) (n : ℕ) (f : Lp ℂ 2 μ) :
    cutCLM hm n f =ᵐ[μ] fun x => Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x * f x :=
  coeFn_mulCLM _ _ _ f

/-- Multiplication by `m` cut off at `n`: bounded, hence defined on all of `L²`. -/
def cutMulCLM (hm : Measurable m) (n : ℕ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulCLM _ (aestronglyMeasurable_indicator_cutSet_mul hm n) (C := n)
    (Eventually.of_forall (norm_indicator_cutSet_mul_le n))

theorem coeFn_cutMulCLM (hm : Measurable m) (n : ℕ) (f : Lp ℂ 2 μ) :
    cutMulCLM hm n f
      =ᵐ[μ] fun x => Set.indicator (cutSet m n) (fun x : α => ((m x : ℂ))) x * f x :=
  coeFn_mulCLM _ _ _ f

/-- **The cut-offs exhaust `α`**: a function vanishing a.e. on every cut-off set vanishes a.e. This
replaces a dominated-convergence argument everywhere below. -/
theorem ae_eq_zero_of_ae_eq_zero_on_cutSet {u : α → ℂ}
    (h : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ cutSet m n → u x = 0) : u =ᵐ[μ] 0 := by
  have hnull : ∀ n : ℕ, μ {x | x ∈ cutSet m n ∧ u x ≠ 0} = 0 := by
    intro n
    refine measure_mono_null (fun x hx => ?_) ((MeasureTheory.ae_iff).1 (h n))
    exact fun hc => hx.2 (hc hx.1)
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ (measure_iUnion_null hnull))
  intro x hx
  obtain ⟨n, hn⟩ := exists_mem_cutSet (m := m) x
  exact Set.mem_iUnion.2 ⟨n, hn, hx⟩

/-! ### The unbounded multiplication operator -/

/-- The natural domain of multiplication by `m`: those `f ∈ L²` whose product with `m` is in `L²`. -/
def mulDomain (m : α → ℝ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f : Lp ℂ 2 μ | MemLp (fun x => ((m x : ℂ)) * f x) 2 μ}
  add_mem' := by
    intro f g hf hg
    refine (MemLp.add hf hg).ae_eq ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx]
    ring
  zero_mem' := by
    refine (MemLp.zero (p := 2) (μ := μ) (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, mul_zero]
  smul_mem' := by
    intro c f hf
    refine (MemLp.const_mul hf c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    ring

theorem mem_mulDomain_iff {f : Lp ℂ 2 μ} :
    f ∈ mulDomain m ↔ MemLp (fun x => ((m x : ℂ)) * f x) 2 μ := Iff.rfl

/-- The value of the multiplication operator, as an `L²` element. Wrapping the `toLp` in a
definition keeps its `MemLp` proof opaque, so the rewriting below matches syntactically. -/
def mulVal (f : mulDomain (μ := μ) m) : Lp ℂ 2 μ := MemLp.toLp _ (mem_mulDomain_iff.1 f.2)

theorem coeFn_mulVal (f : mulDomain (μ := μ) m) :
    mulVal f =ᵐ[μ] fun x => ((m x : ℂ)) * (f : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp _

theorem mulVal_add (f g : mulDomain (μ := μ) m) : mulVal (f + g) = mulVal f + mulVal g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulVal (f + g), coeFn_mulVal f, coeFn_mulVal g,
    Lp.coeFn_add (mulVal f) (mulVal g),
    Lp.coeFn_add (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1, h4, h2, h3, Submodule.coe_add, h5]
  ring

theorem mulVal_smul (c : ℂ) (f : mulDomain (μ := μ) m) : mulVal (c • f) = c • mulVal f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulVal (c • f), coeFn_mulVal f, Lp.coeFn_smul c (mulVal f),
    Lp.coeFn_smul c (f : Lp ℂ 2 μ)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
  rw [h1, h3, h2, Submodule.coe_smul, h4]
  ring

/-- **Multiplication by a real measurable function as an unbounded operator on `L²`**, on its
natural domain. -/
def mulOp (m : α → ℝ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := mulDomain m
  toFun :=
    { toFun := mulVal
      map_add' := mulVal_add
      map_smul' := mulVal_smul }

@[simp]
theorem mulOp_domain : (mulOp (μ := μ) m).domain = mulDomain m := rfl

theorem mulOp_apply (f : (mulOp (μ := μ) m).domain) : mulOp m f = mulVal f := rfl

theorem coeFn_mulOp (f : (mulOp (μ := μ) m).domain) :
    mulOp m f =ᵐ[μ] fun x => ((m x : ℂ)) * (f : Lp ℂ 2 μ) x :=
  coeFn_mulVal f

/-- Every cut-off of every `L²` function lies in the domain: the cut-off makes `m` bounded. -/
theorem cutCLM_mem_mulDomain (hm : Measurable m) (n : ℕ) (k : Lp ℂ 2 μ) :
    cutCLM hm n k ∈ mulDomain (μ := μ) m := by
  refine MemLp.mono' (g := fun x => (n : ℝ) * ‖k x‖) (MemLp.const_mul (Lp.memLp k).norm n) ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hm).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _)
  · filter_upwards [coeFn_cutCLM hm n k] with x hx
    rw [hx]
    have hm' : ‖((m x : ℂ))‖ = |m x| := by rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hc : x ∈ cutSet m n
    · rw [Set.indicator_of_mem hc, one_mul, norm_mul, hm']
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    · rw [Set.indicator_of_notMem hc, zero_mul, mul_zero, norm_zero]
      positivity

/-! ### The cut-off is self-adjoint -/

omit [MeasurableSpace α] in
theorem conj_indicator_cutSet (n : ℕ) (x : α) :
    conj (Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x)
      = Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x := by
  by_cases hx : x ∈ cutSet m n
  · rw [Set.indicator_of_mem hx, map_one]
  · rw [Set.indicator_of_notMem hx, map_zero]

omit [MeasurableSpace α] in
theorem indicator_cutSet_mul (n : ℕ) (x : α) :
    Set.indicator (cutSet m n) (fun x : α => ((m x : ℂ))) x
      = Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x * ((m x : ℂ)) := by
  by_cases hx : x ∈ cutSet m n
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- The cut-off is a self-adjoint bounded operator: it moves across the inner product. -/
theorem inner_cutCLM (hm : Measurable m) (n : ℕ) (f g : Lp ℂ 2 μ) :
    inner ℂ (cutCLM hm n f) g = inner ℂ f (cutCLM hm n g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cutCLM hm n f, coeFn_cutCLM hm n g] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, conj_indicator_cutSet]
  ring

/-- ★★ **The domain is dense.** A vector orthogonal to it is killed by every cut-off, hence vanishes
a.e. on every cut-off set, and the cut-offs exhaust `α`: no approximation argument is needed. -/
theorem dense_mulDomain (hm : Measurable m) :
    Dense ((mulDomain (μ := μ) m : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  have hperp : (mulDomain (μ := μ) m)ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun g hg => ?_
    have hcut : ∀ n : ℕ, cutCLM hm n g = 0 := by
      intro n
      have h0 : ∀ k : Lp ℂ 2 μ, inner ℂ k (cutCLM hm n g) = (0 : ℂ) := by
        intro k
        rw [← inner_cutCLM hm n k g]
        exact (Submodule.mem_orthogonal _ g).1 hg _ (cutCLM_mem_mulDomain hm n k)
      exact inner_self_eq_zero.1 (h0 (cutCLM hm n g))
    have hgz : ⇑g =ᵐ[μ] (0 : α → ℂ) := by
      refine ae_eq_zero_of_ae_eq_zero_on_cutSet (m := m) fun n => ?_
      have h1 : (fun x => Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x * g x)
          =ᵐ[μ] (0 : α → ℂ) := by
        refine (coeFn_cutCLM hm n g).symm.trans ?_
        rw [hcut n]
        exact Lp.coeFn_zero ℂ 2 μ
      filter_upwards [h1] with x hx hxs
      simp only [Pi.zero_apply] at hx
      rwa [Set.indicator_of_mem hxs, one_mul] at hx
    exact Lp.ext (hgz.trans (Lp.coeFn_zero ℂ 2 μ).symm)
  have hclos := Submodule.orthogonal_orthogonal_eq_closure (K := mulDomain (μ := μ) m)
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 hclos.symm

/-! ### Symmetry and self-adjointness -/

/-- ★★ **Multiplication by a real function is symmetric**: the factor comes out of either slot
unchanged, which is the only place reality of `m` is used. -/
theorem mulOp_isFormalAdjoint (m : α → ℝ) :
    (mulOp (μ := μ) m).IsFormalAdjoint (mulOp (μ := μ) m) := by
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOp x, coeFn_mulOp y] with t h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- ★★ **Multiplication by a bounded real function is symmetric as a bounded operator** — the
hypothesis #64(ii)'s perturbation theorem consumes, discharged here for the only perturbation the
corpus needs. Reality of the function is the whole of it, exactly as for the unbounded `mulOp`. -/
theorem isSymmetric_mulCLM (g : α → ℝ) (hg : AEStronglyMeasurable (fun x => ((g x : ℂ))) μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖((g x : ℂ))‖ ≤ C) :
    LinearMap.IsSymmetric
      ((mulCLM (fun x => ((g x : ℂ))) hg hb : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) := by
  intro f h
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulCLM (fun x => ((g x : ℂ))) hg hb f,
    coeFn_mulCLM (fun x => ((g x : ℂ))) hg hb h] with x h1 h2
  rw [show ((mulCLM (fun x => ((g x : ℂ))) hg hb : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) f) = mulCLM _ hg hb f
      from rfl,
    show ((mulCLM (fun x => ((g x : ℂ))) hg hb : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) h) = mulCLM _ hg hb h
      from rfl, h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- Pairing the operator against a cut-off moves the cut-off `m` to the other slot. -/
theorem inner_cutMulCLM (hm : Measurable m) (n : ℕ) (k y : Lp ℂ 2 μ) :
    inner ℂ (cutMulCLM hm n y) k
      = inner ℂ y (mulOp m ⟨cutCLM hm n k, cutCLM_mem_mulDomain hm n k⟩) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cutMulCLM hm n y,
    coeFn_mulOp (⟨cutCLM hm n k, cutCLM_mem_mulDomain hm n k⟩ : (mulOp (μ := μ) m).domain),
    coeFn_cutCLM hm n k] with x h1 h2 h3
  rw [h1, h2, h3, RCLike.inner_apply', RCLike.inner_apply', map_mul, indicator_cutSet_mul,
    map_mul, conj_indicator_cutSet, Complex.conj_ofReal]
  ring

/-- **The adjoint multiplies by `m` too**: on every cut-off set its value agrees with `m · y`, and
the cut-offs exhaust `α`. This is the computation behind maximality. -/
theorem coeFn_adjoint_mulOp (hm : Measurable m) (y : ((mulOp (μ := μ) m)†).domain) :
    (((mulOp (μ := μ) m)† y : Lp ℂ 2 μ)) =ᵐ[μ] fun x => ((m x : ℂ)) * (y : Lp ℂ 2 μ) x := by
  have hT : Dense (((mulOp (μ := μ) m).domain : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
    dense_mulDomain hm
  have hpair : ∀ n : ℕ,
      cutCLM hm n ((mulOp (μ := μ) m)† y : Lp ℂ 2 μ) = cutMulCLM hm n (y : Lp ℂ 2 μ) := by
    intro n
    refine ext_inner_right ℂ fun k => ?_
    rw [inner_cutCLM hm n _ k, inner_cutMulCLM hm n k (y : Lp ℂ 2 μ)]
    exact LinearPMap.adjoint_isFormalAdjoint hT y ⟨cutCLM hm n k, cutCLM_mem_mulDomain hm n k⟩
  have hsub : (fun x => ((mulOp (μ := μ) m)† y : Lp ℂ 2 μ) x - ((m x : ℂ)) * (y : Lp ℂ 2 μ) x)
      =ᵐ[μ] (0 : α → ℂ) := by
    refine ae_eq_zero_of_ae_eq_zero_on_cutSet (m := m) fun n => ?_
    have h1 := coeFn_cutCLM hm n ((mulOp (μ := μ) m)† y : Lp ℂ 2 μ)
    have h2 := coeFn_cutMulCLM hm n (y : Lp ℂ 2 μ)
    have h3 : (fun x => Set.indicator (cutSet m n) (fun _ : α => (1 : ℂ)) x
          * ((mulOp (μ := μ) m)† y : Lp ℂ 2 μ) x)
        =ᵐ[μ] fun x => Set.indicator (cutSet m n) (fun x : α => ((m x : ℂ))) x
          * (y : Lp ℂ 2 μ) x := by
      refine h1.symm.trans ?_
      rw [hpair n]
      exact h2
    filter_upwards [h3] with x hx hxs
    rw [Set.indicator_of_mem hxs, one_mul] at hx
    rw [indicator_cutSet_mul, Set.indicator_of_mem hxs, one_mul] at hx
    rw [hx]
    ring
  filter_upwards [hsub] with x hx
  simp only [Pi.zero_apply] at hx
  linear_combination (norm := ring_nf) hx

/-- ★★★ **Multiplication by a real measurable function is self-adjoint on its natural domain.**
Symmetry is the easy half; the content is maximality — a vector the adjoint is defined at already
has `m · y ∈ L²`, because the adjoint's value is `m · y` on every cut-off set. -/
theorem isSelfAdjoint_mulOp (hm : Measurable m) : IsSelfAdjoint (mulOp (μ := μ) m) := by
  have hT : Dense (((mulOp (μ := μ) m).domain : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
    dense_mulDomain hm
  have hle : mulOp (μ := μ) m ≤ (mulOp (μ := μ) m)† := (mulOp_isFormalAdjoint m).le_adjoint hT
  have hdom : (mulOp (μ := μ) m).domain = ((mulOp (μ := μ) m)†).domain := by
    refine le_antisymm hle.1 fun y hy => ?_
    exact mem_mulDomain_iff.2
      ((Lp.memLp (((mulOp (μ := μ) m)† ⟨y, hy⟩ : Lp ℂ 2 μ))).ae_eq
        (coeFn_adjoint_mulOp hm ⟨y, hy⟩))
  exact LinearPMap.isSelfAdjoint_def.2 (LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

/-! ### The resolvent -/

/-- ★★ **Off the closure of the values, multiplication by `m` has a bounded inverse**, namely
multiplication by `(m − z)⁻¹`. The reciprocal is bounded there — that is what being off the closure
says — and `m/(m − z)` is bounded too, which is what puts the inverse's values back in the
domain. -/
theorem mem_resolventSet_mulOp (hm : Measurable m) {z : ℂ}
    (hz : z ∉ closure (Set.range fun x => ((m x : ℂ)))) :
    z ∈ LinearPMap.resolventSet (mulOp (μ := μ) m) := by
  obtain ⟨r, hr, hfar⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x, r ≤ ‖((m x : ℂ)) - z‖ := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z hz
    refine ⟨r, hr, fun x => ?_⟩
    by_contra hlt
    refine hball (?_ : ((m x : ℂ)) ∈ Metric.ball z r) (subset_closure ⟨x, rfl⟩)
    rw [Metric.mem_ball, dist_eq_norm]
    exact not_le.1 hlt
  have hne : ∀ x, ((m x : ℂ)) - z ≠ 0 := by
    intro x h
    have h' := hfar x
    rw [h, norm_zero] at h'
    linarith
  have hinv_le : ∀ x, ‖(((m x : ℂ)) - z)⁻¹‖ ≤ r⁻¹ := by
    intro x
    rw [norm_inv]
    have h := one_div_le_one_div_of_le hr (hfar x)
    rwa [one_div, one_div] at h
  have hu : ∀ x, ‖((m x : ℂ)) * (((m x : ℂ)) - z)⁻¹‖ ≤ 1 + ‖z‖ * r⁻¹ := by
    intro x
    have h1 : 0 < ‖((m x : ℂ)) - z‖ := lt_of_lt_of_le hr (hfar x)
    have h2 : ‖((m x : ℂ))‖ ≤ ‖((m x : ℂ)) - z‖ + ‖z‖ := by
      calc ‖((m x : ℂ))‖ = ‖(((m x : ℂ)) - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖((m x : ℂ)) - z‖ + ‖z‖ := norm_add_le _ _
    calc ‖((m x : ℂ)) * (((m x : ℂ)) - z)⁻¹‖ = ‖((m x : ℂ))‖ * ‖((m x : ℂ)) - z‖⁻¹ := by
          rw [norm_mul, norm_inv]
      _ ≤ (‖((m x : ℂ)) - z‖ + ‖z‖) * ‖((m x : ℂ)) - z‖⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 1 + ‖z‖ * ‖((m x : ℂ)) - z‖⁻¹ := by field_simp
      _ ≤ 1 + ‖z‖ * r⁻¹ := by
          have h3 : ‖((m x : ℂ)) - z‖⁻¹ ≤ r⁻¹ := by
            have := hinv_le x
            rwa [norm_inv] at this
          nlinarith [norm_nonneg z]
  have hmeas : AEStronglyMeasurable (fun x => (((m x : ℂ)) - z)⁻¹) μ :=
    (((Complex.measurable_ofReal.comp hm).sub measurable_const).inv).aestronglyMeasurable
  set S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    mulCLM (fun x => (((m x : ℂ)) - z)⁻¹) hmeas (C := r⁻¹) (Eventually.of_forall hinv_le)
    with hS_def
  have hScoe : ∀ y : Lp ℂ 2 μ, S y =ᵐ[μ] fun x => (((m x : ℂ)) - z)⁻¹ * y x := by
    intro y
    rw [hS_def]
    exact coeFn_mulCLM _ _ _ y
  have hmaps : ∀ y : Lp ℂ 2 μ, S y ∈ (mulOp (μ := μ) m).domain := by
    intro y
    refine mem_mulDomain_iff.2 (MemLp.mono' (g := fun x => (1 + ‖z‖ * r⁻¹) * ‖y x‖)
      (MemLp.const_mul (Lp.memLp y).norm _) ?_ ?_)
    · exact ((Complex.measurable_ofReal.comp hm).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable _)
    · filter_upwards [hScoe y] with x hx
      rw [hx, ← mul_assoc, norm_mul]
      exact mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
  refine ⟨S, { maps_mem := hmaps, right_inv := ?_, left_inv := ?_ }⟩
  · intro y
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_sub (mulOp m ⟨S y, hmaps y⟩) (z • S y),
      coeFn_mulOp (⟨S y, hmaps y⟩ : (mulOp (μ := μ) m).domain), Lp.coeFn_smul z (S y),
      hScoe y] with x e1 e2 e3 e4
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e3
    rw [e1, e2, e3, e4]
    have h := hne x
    field_simp
  · intro f
    refine Lp.ext ?_
    filter_upwards [hScoe (mulOp m f - z • (f : Lp ℂ 2 μ)),
      Lp.coeFn_sub (mulOp m f) (z • (f : Lp ℂ 2 μ)), coeFn_mulOp f,
      Lp.coeFn_smul z (f : Lp ℂ 2 μ)] with x e1 e2 e3 e4
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e4
    rw [e1, e2, e3, e4]
    have h := hne x
    field_simp

/-! ### The spectrum -/

/-- ★★ **Every value that `m` takes on sets of positive measure is in the spectrum.** The normalised
indicators of the preimages `m⁻¹(ball lam ε)` are approximate eigenvectors: `(M_m − lam)` shrinks
them by `ε`, so a bounded inverse would have to stretch one of them by more than its own norm. The
two hypotheses say exactly that `lam` is an *essential* value of `m`. -/
theorem mem_spectrum_mulOp (hm : Measurable m) {lam : ℝ}
    (hpos : ∀ ε : ℝ, 0 < ε → μ (m ⁻¹' Metric.ball lam ε) ≠ 0)
    (hfin : ∀ ε : ℝ, 0 < ε → μ (m ⁻¹' Metric.ball lam ε) ≠ ⊤) :
    ((lam : ℂ)) ∈ LinearPMap.spectrum (mulOp (μ := μ) m) := by
  rw [LinearPMap.mem_spectrum_iff]
  intro S hS
  have hS0 : (0 : ℝ) ≤ ‖S‖ := norm_nonneg _
  set ε : ℝ := 1 / (‖S‖ + 1) with hεdef
  have hεpos : 0 < ε := by positivity
  have hsm : MeasurableSet (m ⁻¹' Metric.ball lam ε) := hm Metric.isOpen_ball.measurableSet
  set f : Lp ℂ 2 μ := indicatorConstLp 2 hsm (hfin ε hεpos) (1 : ℂ) with hfdef
  have hfcoe : ⇑f =ᵐ[μ] (m ⁻¹' Metric.ball lam ε).indicator (fun _ : α => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have habs : ∀ x ∈ m ⁻¹' Metric.ball lam ε, |m x - lam| < ε := by
    intro x hx
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hx
    exact hx
  have hdom : f ∈ mulDomain (μ := μ) m := by
    refine mem_mulDomain_iff.2 (MemLp.mono' (g := fun x => (|lam| + ε) * ‖f x‖)
      (MemLp.const_mul (Lp.memLp f).norm _) ?_ ?_)
    · exact ((Complex.measurable_ofReal.comp hm).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable _)
    · filter_upwards [hfcoe] with x hx
      by_cases hxs : x ∈ m ⁻¹' Metric.ball lam ε
      · have h1 : |m x| ≤ |lam| + ε := by
          have h2 := habs x hxs
          have h3 : |m x| - |lam| ≤ |m x - lam| := abs_sub_abs_le_abs_sub (m x) lam
          linarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      · rw [hx, Set.indicator_of_notMem hxs]
        simp
  have hest : ‖mulOp m ⟨f, hdom⟩ - ((lam : ℂ)) • f‖ ≤ ε * ‖f‖ := by
    have h1 : ‖mulOp m ⟨f, hdom⟩ - ((lam : ℂ)) • f‖ ≤ ‖(ε : ℝ) • f‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [Lp.coeFn_sub (mulOp m ⟨f, hdom⟩) (((lam : ℂ)) • f),
        coeFn_mulOp (⟨f, hdom⟩ : (mulOp (μ := μ) m).domain),
        Lp.coeFn_smul ((lam : ℂ)) f, Lp.coeFn_smul (ε : ℝ) f, hfcoe] with x e1 e2 e3 e4 e5
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e3 e4
      rw [e1, e2, e3, e4]
      by_cases hxs : x ∈ m ⁻¹' Metric.ball lam ε
      · have h2 := habs x hxs
        have h3 : ((m x : ℂ)) * f x - ((lam : ℂ)) * f x = (((m x - lam : ℝ)) : ℂ) * f x := by
          push_cast
          ring
        rw [h3, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs,
          abs_of_pos hεpos]
        exact mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
      · rw [e5, Set.indicator_of_notMem hxs]
        simp
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos] at h1
    exact h1
  have hfpos : 0 < ‖f‖ := by
    rw [hfdef, norm_indicatorConstLp' (by norm_num) (hpos ε hεpos)]
    have h1 : 0 < μ.real (m ⁻¹' Metric.ball lam ε) := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_pos (hpos ε hεpos) (hfin ε hεpos)
    have h2 := Real.rpow_pos_of_pos h1 (1 / (2 : ℝ≥0∞).toReal)
    simpa using h2
  have hkey := hS.left_inv ⟨f, hdom⟩
  have hchain : ‖f‖ ≤ ‖S‖ * (ε * ‖f‖) := by
    calc ‖f‖ = ‖S (mulOp m ⟨f, hdom⟩ - ((lam : ℂ)) • (⟨f, hdom⟩ : (mulOp (μ := μ) m).domain))‖ := by
          rw [hkey]
      _ ≤ ‖S‖ * ‖mulOp m ⟨f, hdom⟩ - ((lam : ℂ)) • f‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (ε * ‖f‖) := by gcongr
  have hlt1 : ‖S‖ * ε < 1 := by
    rw [hεdef, mul_one_div]
    exact (div_lt_one (by positivity)).2 (by linarith)
  nlinarith [hfpos]

end MeasureTheory.L2

end

end
