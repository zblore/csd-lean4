/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DysonSeries

/-!
# The vertex bookkeeping of the Dyson series

**Category:** 1-Mathlib (CSD-free; staged for upstream).

`DysonSeries.lean` expands the propagator `exp (t (A + B))` in powers of the interaction `B`.
This module is the bookkeeping that turns the `n`-th term into a **sum over diagrams with `n`
vertices**: the interaction picture, the ordered vertex times, the labelling of the vertices when
the interaction is a sum of vertex types, and — in the eigenbasis of a diagonal free generator —
the old-fashioned (time-ordered) perturbation theory with intermediate states and its explicit
first- and second-order amplitudes.

* `interactionPicture A B s = exp (−s A) · B · exp (s A)` — the interaction-picture vertex;
  `dysonTermI A B n t = exp (−t A) · Dₙ(t)` — the term in the interaction picture, with
  `dysonTermI_zero` (`= 1`) and ★ `dysonTermI_succ`,
  `dysonTermI (n + 1) t = ∫₀ᵗ V_I(s) · dysonTermI n s ds`: unrolled, the `n`-th term is the
  **time-ordered product** `∫_{0 ≤ s₁ ≤ ⋯ ≤ sₙ ≤ t} V_I(sₙ) ⋯ V_I(s₁) ds` — the `n` vertices at
  ordered times, `dysonTerm_eq_exp_smul_mul_dysonTermI`;
* `dysonTermLabelled A B n f t` — the term with the vertex type `f i` at slot `i` (`f 0` the
  latest), and ★ `dysonTerm_sum_eq_sum_dysonTermLabelled` — **the sum over labellings**: for an
  interaction `∑ v, B v` (a sum of vertex types — local vertices at the sites of a lattice, the
  monomials of a polynomial interaction), the `n`-th term is the sum over all `f : Fin n → ι` of
  the labelled terms, one per assignment of a type to each of the `n` ordered vertices;
* `intervalIntegral_apply` — the entry of a matrix-valued interval integral is the interval
  integral of the entry;
* **Diagonal free generator** `A = diagonal a` (the eigenbasis; `a i = −i Eᵢ` for a Hamiltonian):
  `interactionPicture_diagonal_apply` — `V_I(s) i j = e^{s (aⱼ − aᵢ)} · B i j`, the vertex
  dressed with the free phases of its two legs; ★ `dysonTermI_succ_apply_diagonal` —
  **old-fashioned perturbation theory**, one vertex at a time:
  `dysonTermI (n + 1) t i j = ∫₀ᵗ ∑ₖ e^{s (aₖ − aᵢ)} B i k · dysonTermI n s k j ds`, the sum over
  the intermediate state `k` after the latest vertex;
  `dysonTermI_one_apply_diagonal`, ★ `dysonTerm_one_apply_diagonal_self`
  (`D₁(t) i i = e^{t aᵢ} · t · B i i`, the first-order diagonal amplitude — with `B` a
  polynomial in the field, the one-vertex vacuum diagram), ★ `dysonTerm_one_apply_diagonal_of_ne`
  (`D₁(t) i j = B i j · (e^{t aⱼ} − e^{t aᵢ}) / (aⱼ − aᵢ)`, **the first-order transition
  amplitude** of time-dependent perturbation theory), and ★ `dysonTermI_two_apply_diagonal` /
  `dysonTermI_two_apply_diagonal_self` — the two-vertex amplitude as the double integral over
  `0 ≤ s₁ ≤ s₂ ≤ t` of the sum over the intermediate state of the two vertex entries dressed with
  the free propagation between them.

## Honest scope

⚠️ **Bookkeeping only.** Nothing here evaluates a vacuum expectation: the reduction of
`⟨V_I(sₙ) ⋯ V_I(s₁)⟩` to a sum over pairings of propagators is Wick's theorem, which lives with
the field (the CSD lattice's `CV/Wick.lean`, `CV/WickGeneral.lean`) and is joined to these
identities in `CV/FeynmanVertex.lean`. The `1/n!` of the unordered-time form is not stated: the
terms are kept as ordered (simplex) integrals, which is what the recursion gives.

⚠️ **Finite dimension.** Matrix exponentials and Bochner integrals of matrices under the L2
operator norm, as in `DysonSeries.lean`; no unbounded generators.

References: F. J. Dyson, *The radiation theories of Tomonaga, Schwinger, and Feynman*, Phys. Rev.
75, 486 (1949) §III (the time-ordered expansion); `Analysis/Matrix/DysonSeries.lean`;
`specs/BACKLOG.md` #36(b)(iii); `specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix Nat Topology
open NormedSpace MeasureTheory intervalIntegral Filter

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-! ### Entries of matrix-valued integrals -/

omit [Nonempty m] in
/-- The `(i, j)` entry of a matrix-valued interval integral is the interval integral of the
entry. -/
theorem intervalIntegral_apply {f : ℝ → Matrix m m ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (i j : m) :
    (∫ s in a..b, f s) i j = ∫ s in a..b, f s i j := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (entryLinearMap ℂ ℂ i j)
  have h := L.intervalIntegral_comp_comm hf
  simpa [L] using h.symm

omit [Nonempty m] in
theorem exp_neg_smul_mul_exp_smul (A : Matrix m m ℂ) (t : ℝ) :
    exp ((-t) • A) * exp (t • A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left (-t)).smul_right t), ← add_smul,
    neg_add_cancel, zero_smul, exp_zero]

omit [Nonempty m] in
theorem exp_smul_mul_exp_neg_smul (A : Matrix m m ℂ) (t : ℝ) :
    exp (t • A) * exp ((-t) • A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left t).smul_right (-t)), ← add_smul,
    add_neg_cancel, zero_smul, exp_zero]

/-! ### The interaction picture -/

/-- **The interaction-picture vertex** `V_I(s) = exp (−s A) · B · exp (s A)`: the interaction
transported by the free evolution to time `s`. -/
noncomputable def interactionPicture (A B : Matrix m m ℂ) (s : ℝ) : Matrix m m ℂ :=
  exp ((-s) • A) * B * exp (s • A)

omit [Nonempty m] in
theorem continuous_interactionPicture (A B : Matrix m m ℂ) :
    Continuous (interactionPicture A B) :=
  ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_exp_smul A)

omit [Nonempty m] in
theorem interactionPicture_smul (A B : Matrix m m ℂ) (c : ℂ) (s : ℝ) :
    interactionPicture A (c • B) s = c • interactionPicture A B s := by
  simp only [interactionPicture, Matrix.mul_smul, Matrix.smul_mul]

/-- **The Dyson term in the interaction picture**, `exp (−t A) · Dₙ(t)`. -/
noncomputable def dysonTermI (A B : Matrix m m ℂ) (n : ℕ) (t : ℝ) : Matrix m m ℂ :=
  exp ((-t) • A) * dysonTerm A B n t

omit [Nonempty m] in
theorem dysonTerm_eq_exp_smul_mul_dysonTermI (A B : Matrix m m ℂ) (n : ℕ) (t : ℝ) :
    dysonTerm A B n t = exp (t • A) * dysonTermI A B n t := by
  rw [dysonTermI, ← Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, one_mul]

omit [Nonempty m] in
theorem dysonTermI_zero (A B : Matrix m m ℂ) (t : ℝ) : dysonTermI A B 0 t = 1 := by
  rw [dysonTermI, dysonTerm_zero, exp_neg_smul_mul_exp_smul]

omit [Nonempty m] in
/-- ★ **The time-ordered recursion**: `dysonTermI (n + 1) t = ∫₀ᵗ V_I(s) · dysonTermI n s ds`.
Unrolled, `dysonTermI n t = ∫_{0 ≤ s₁ ≤ ⋯ ≤ sₙ ≤ t} V_I(sₙ) ⋯ V_I(s₁) ds` — the `n` vertices at
ordered times, the latest on the left. -/
theorem dysonTermI_succ (A B : Matrix m m ℂ) (n : ℕ) (t : ℝ) :
    dysonTermI A B (n + 1) t
      = ∫ s in (0 : ℝ)..t, interactionPicture A B s * dysonTermI A B n s := by
  rw [dysonTermI, dysonTerm_succ, ← Matrix.mul_assoc, exp_neg_smul_mul_exp_smul, one_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [interactionPicture, dysonTermI, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (exp (s • A)), exp_smul_mul_exp_neg_smul, one_mul]

omit [Nonempty m] in
theorem continuous_dysonTermI (A B : Matrix m m ℂ) (n : ℕ) : Continuous (dysonTermI A B n) :=
  (continuous_exp_neg_smul A).mul (continuous_dysonTerm A B n)

omit [Nonempty m] in
/-- The one-vertex term: `dysonTermI 1 t = ∫₀ᵗ V_I(s) ds`. -/
theorem dysonTermI_one (A B : Matrix m m ℂ) (t : ℝ) :
    dysonTermI A B 1 t = ∫ s in (0 : ℝ)..t, interactionPicture A B s := by
  rw [dysonTermI_succ]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [dysonTermI_zero, mul_one]

/-! ### The sum over vertex labellings -/

/-- **The Dyson term with labelled vertices**: the interaction `B (f i)` at the `i`-th slot, `f 0`
the latest vertex, `Fin.tail f` the earlier ones. -/
noncomputable def dysonTermLabelled (A : Matrix m m ℂ) {ι : Type*} (B : ι → Matrix m m ℂ) :
    (n : ℕ) → (Fin n → ι) → ℝ → Matrix m m ℂ
  | 0, _ => fun t => exp (t • A)
  | n + 1, f => fun t =>
      exp (t • A) * ∫ s in (0 : ℝ)..t,
        exp ((-s) • A) * B (f 0) * dysonTermLabelled A B n (Fin.tail f) s

omit [Nonempty m] in
theorem dysonTermLabelled_zero (A : Matrix m m ℂ) {ι : Type*} (B : ι → Matrix m m ℂ)
    (f : Fin 0 → ι) (t : ℝ) : dysonTermLabelled A B 0 f t = exp (t • A) :=
  rfl

omit [Nonempty m] in
theorem dysonTermLabelled_succ (A : Matrix m m ℂ) {ι : Type*} (B : ι → Matrix m m ℂ) (n : ℕ)
    (f : Fin (n + 1) → ι) (t : ℝ) :
    dysonTermLabelled A B (n + 1) f t
      = exp (t • A) * ∫ s in (0 : ℝ)..t,
          exp ((-s) • A) * B (f 0) * dysonTermLabelled A B n (Fin.tail f) s :=
  rfl

omit [Nonempty m] in
theorem continuous_dysonTermLabelled (A : Matrix m m ℂ) {ι : Type*} (B : ι → Matrix m m ℂ) :
    ∀ (n : ℕ) (f : Fin n → ι), Continuous (dysonTermLabelled A B n f)
  | 0, _ => continuous_exp_smul A
  | n + 1, f => by
    rw [show dysonTermLabelled A B (n + 1) f = fun t => exp (t • A) * ∫ s in (0 : ℝ)..t,
        exp ((-s) • A) * B (f 0) * dysonTermLabelled A B n (Fin.tail f) s from rfl]
    refine (continuous_exp_smul A).mul ?_
    exact intervalIntegral.continuous_primitive
      (fun a b =>
        (((continuous_exp_neg_smul A).mul continuous_const).mul
          (continuous_dysonTermLabelled A B n (Fin.tail f))).intervalIntegrable a b) 0

omit [Nonempty m] in
/-- ★ **The sum over vertex labellings.** For an interaction that is a sum of vertex types,
`B = ∑ v, B v`, the `n`-th Dyson term is the sum over every assignment `f : Fin n → ι` of a type
to each of the `n` ordered vertices of the labelled term. -/
theorem dysonTerm_sum_eq_sum_dysonTermLabelled (A : Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (B : ι → Matrix m m ℂ) (n : ℕ) (t : ℝ) :
    dysonTerm A (∑ v, B v) n t = ∑ f : Fin n → ι, dysonTermLabelled A B n f t := by
  induction n generalizing t with
  | zero =>
    rw [dysonTerm_zero, Fintype.sum_unique]
    rfl
  | succ n ih =>
    rw [dysonTerm_succ]
    have hint : ∀ s : ℝ,
        exp ((-s) • A) * (∑ v, B v) * dysonTerm A (∑ v, B v) n s
          = ∑ p : ι × (Fin n → ι),
              exp ((-s) • A) * B p.1 * dysonTermLabelled A B n p.2 s := by
      intro s
      rw [ih s, Fintype.sum_prod_type]
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    simp_rw [hint]
    rw [intervalIntegral.integral_finsetSum fun p _ =>
        (((continuous_exp_neg_smul A).mul continuous_const).mul
          (continuous_dysonTermLabelled A B n p.2)).intervalIntegrable _ _,
      Finset.mul_sum,
      ← Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _ fun _ => rfl]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dysonTermLabelled_succ]
    simp [Fin.consEquiv, Fin.tail_cons]

/-! ### A diagonal free generator: old-fashioned perturbation theory -/

omit [Nonempty m] in
theorem exp_smul_diagonal (a : m → ℂ) (t : ℝ) :
    exp (t • diagonal a) = diagonal fun i => Complex.exp (t * a i) := by
  rw [← diagonal_smul, exp_diagonal]
  congr 1
  funext i
  rw [Pi.exp_def]
  show exp (t • a i) = Complex.exp (t * a i)
  rw [← Complex.exp_eq_exp_ℂ, Complex.real_smul]

omit [Nonempty m] in
/-- In the eigenbasis of the free generator the interaction-picture vertex is the bare vertex
dressed with the free phases of its two legs: `V_I(s) i j = e^{s (aⱼ − aᵢ)} · B i j`. -/
theorem interactionPicture_diagonal_apply (a : m → ℂ) (B : Matrix m m ℂ) (s : ℝ) (i j : m) :
    interactionPicture (diagonal a) B s i j = Complex.exp (s * (a j - a i)) * B i j := by
  rw [interactionPicture, exp_smul_diagonal, exp_smul_diagonal, mul_diagonal, diagonal_mul,
    mul_comm _ (B i j), mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  push_cast
  ring

omit [Nonempty m] in
/-- ★ **Old-fashioned perturbation theory**, one vertex at a time: in the eigenbasis of the free
generator, `dysonTermI (n + 1) t i j = ∫₀ᵗ ∑ₖ e^{s (aₖ − aᵢ)} B i k · dysonTermI n s k j ds` — the
sum over the intermediate state `k` between the latest vertex and the earlier ones. -/
theorem dysonTermI_succ_apply_diagonal (a : m → ℂ) (B : Matrix m m ℂ) (n : ℕ) (t : ℝ) (i j : m) :
    dysonTermI (diagonal a) B (n + 1) t i j
      = ∫ s in (0 : ℝ)..t,
          ∑ k, Complex.exp (s * (a k - a i)) * B i k * dysonTermI (diagonal a) B n s k j := by
  rw [dysonTermI_succ, intervalIntegral_apply
    (((continuous_interactionPicture _ _).mul (continuous_dysonTermI _ _ n)).intervalIntegrable
      _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [Matrix.mul_apply]
  simp_rw [interactionPicture_diagonal_apply]

omit [Nonempty m] in
theorem dysonTermI_one_apply_diagonal (a : m → ℂ) (B : Matrix m m ℂ) (t : ℝ) (i j : m) :
    dysonTermI (diagonal a) B 1 t i j
      = ∫ s in (0 : ℝ)..t, Complex.exp (s * (a j - a i)) * B i j := by
  rw [dysonTermI_succ_apply_diagonal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp [dysonTermI_zero, Matrix.one_apply]

omit [Nonempty m] in
theorem continuous_exp_mul_const (c : ℂ) : Continuous fun s : ℝ => Complex.exp (s * c) :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

omit [Nonempty m] in
/-- ★ **The first-order diagonal amplitude**: `D₁(t) i i = e^{t aᵢ} · t · B i i`. The free phase of
the state carries through and the vertex is inserted at every time `s ∈ [0, t]` with the same
weight — with `B` a polynomial in the field and `i` the vacuum, the one-vertex vacuum diagram. -/
theorem dysonTerm_one_apply_diagonal_self (a : m → ℂ) (B : Matrix m m ℂ) (t : ℝ) (i : m) :
    dysonTerm (diagonal a) B 1 t i i = Complex.exp (t * a i) * (t * B i i) := by
  rw [dysonTerm_eq_exp_smul_mul_dysonTermI, exp_smul_diagonal, diagonal_mul,
    dysonTermI_one_apply_diagonal]
  simp only [sub_self, mul_zero, Complex.exp_zero, one_mul, intervalIntegral.integral_const,
    sub_zero, Complex.real_smul]

omit [Nonempty m] in
/-- ★ **The first-order transition amplitude** between distinct free levels:
`D₁(t) i j = B i j · (e^{t aⱼ} − e^{t aᵢ}) / (aⱼ − aᵢ)` — for `a = −i E` the textbook
`⟨j∣U(t)∣i⟩ ≈ −i V_{ji} (e^{−i E_j t} − e^{−i E_i t}) / (−i (E_j − E_i))` of time-dependent
perturbation theory. -/
theorem dysonTerm_one_apply_diagonal_of_ne (a : m → ℂ) (B : Matrix m m ℂ) (t : ℝ) {i j : m}
    (h : a i ≠ a j) :
    dysonTerm (diagonal a) B 1 t i j
      = B i j * (Complex.exp (t * a j) - Complex.exp (t * a i)) / (a j - a i) := by
  have hc : a j - a i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [dysonTerm_eq_exp_smul_mul_dysonTermI, exp_smul_diagonal, diagonal_mul,
    dysonTermI_one_apply_diagonal]
  simp_rw [mul_comm (Complex.exp _) (B i j), mul_comm (_ : ℂ) (a j - a i)]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero]
  have key : Complex.exp (t * a i) * (Complex.exp ((a j - a i) * t) - 1)
      = Complex.exp (t * a j) - Complex.exp (t * a i) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [← key]
  ring

omit [Nonempty m] in
/-- ★ **The two-vertex amplitude**: the double integral over the ordered times `0 ≤ s₁ ≤ s₂ ≤ t`
of the sum over the intermediate state `k` of the two vertex entries dressed with the free phases
— the second-order term of old-fashioned perturbation theory. -/
theorem dysonTermI_two_apply_diagonal (a : m → ℂ) (B : Matrix m m ℂ) (t : ℝ) (i j : m) :
    dysonTermI (diagonal a) B 2 t i j
      = ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
          ∑ k, Complex.exp (s₂ * (a k - a i)) * Complex.exp (s₁ * (a j - a k))
            * (B i k * B k j) := by
  rw [dysonTermI_succ_apply_diagonal]
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  simp_rw [dysonTermI_one_apply_diagonal]
  rw [intervalIntegral.integral_finsetSum
    (f := fun k s₁ => Complex.exp (s₂ * (a k - a i)) * Complex.exp (s₁ * (a j - a k))
      * (B i k * B k j))
    fun k _ => ((continuous_const.mul (continuous_exp_mul_const _)).mul
      continuous_const).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  ring

omit [Nonempty m] in
/-- The two-vertex amplitude on the diagonal: only the time *difference* `s₂ − s₁` between the
vertices enters the free propagation, `e^{(s₂ − s₁) (aₖ − aᵢ)}`. -/
theorem dysonTermI_two_apply_diagonal_self (a : m → ℂ) (B : Matrix m m ℂ) (t : ℝ) (i : m) :
    dysonTermI (diagonal a) B 2 t i i
      = ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
          ∑ k, Complex.exp ((s₂ - s₁) * (a k - a i)) * (B i k * B k i) := by
  rw [dysonTermI_two_apply_diagonal]
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_add]
  congr 2
  ring

end Matrix
