/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The chained Bell walk: no-signalling plus chained correlations forces a uniform marginal

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #23.

A **two-party outcome law** is a function `P : X → Y → O → O → ℝ`, where `P x y i j` is the
probability that Alice reads `i` at setting `x` while Bob reads `j` at setting `y`. Two outcomes
`o`, `oc` are singled out, so the law is a two-outcome box (`huniv`, `hoc` below say that `O` is
exactly `{o, oc}`). **No-signalling** is marginal invariance: Alice's marginal does not depend on
Bob's setting, and conversely. That is the predicate `CSD.SigmaLayer.HasNoSignalling`, which lives
in a higher layer of this repository and cannot be imported here, so it appears below as its two
conjuncts `hA` and `hB` rather than as a second definition of the same thing.

The mathematics is one observation used twice. For a single pair of settings, two marginals of the
same joint distribution differ by at most the probability that the two outcomes disagree
(`abs_marginalA_sub_marginalB_le`), and they add to at most `1` plus the probability that the two
outcomes agree (`abs_marginalA_add_marginalB_sub_one_le`). No-signalling is what lets those
one-pair statements be chained across *different* pairs, because it makes each wing's marginal a
function of that wing's setting alone.

* `marginalA`, `marginalB`, `agree`, `disagree`, `chainCost`;
* ★ `abs_marginalA_sub_marginalB_le`, ★ `abs_marginalA_add_marginalB_sub_one_le` — the two
  one-pair links;
* ★★ `abs_marginalA_sub_marginalB_chain_le` — **the walk**: along the alternating chain
  `A 0, B 0, A 1, B 1, …, A n, B n` the two end marginals differ by at most the sum of the `2n + 1`
  link disagreements;
* ★★★ `abs_marginalA_sub_half_le` — **chained uniformity**: closing the walk with an
  *anticorrelated* link between `A 0` and `B n` forces Alice's marginal at `A 0` to within
  `(chainCost + agree (A 0) (B n)) / 2` of `1 / 2`. Correlations around a chain that close up with
  one reversal leave no room for a biased marginal;
* ★★★ `integral_abs_marginalA_sub_half_le` — **the same bound for every component of a mixture**:
  if each `q ξ` is a no-signalling law and the mixture over `ξ` reproduces `Q`, then the
  components' marginals are `1 / 2` up to the bound computed from `Q`, in mean over `ξ`. The
  functional is affine in the law, so the components inherit the bound the mixture satisfies;
* ★ `exists_signalling_of_sharp_integral` — the contrapositive: a mixture whose components sharpen
  the marginal past that bound has a component that signals.

## Honest scope

⚠️ Two outcomes and one distinguished pair of them. Nothing here is about more outcomes, more
parties, or the chained *inequality* of Braunstein and Caves (a bound on a sum of correlations for
local models), which is a neighbour of this walk and is not proved here.

⚠️ The bound is what it says: a bound. It is informative only when the chain's disagreements and
the closing agreement are small, which is a property of the law the theorem is applied to, and for
the quantum singlet that is `Empirical/QM/ColbeckRenner.lean`.

⚠️ `chainCost` counts the links of an alternating walk with `A` on one wing and `B` on the other.
The settings are arbitrary functions of `ℕ`; no geometry is assumed here.

References: S. L. Braunstein, C. M. Caves, *Wringing out better Bell inequalities*, Ann. Phys. 202
(1990) 22 (the chained family); J. Barrett, L. Hardy, A. Kent, PRL 95 (2005) 010503 (the chained
walk as a device-independent tool); R. Colbeck, R. Renner, *No extension of quantum theory can have
improved predictive power*, Nat. Commun. 2 (2011) 411 (the use made of it in
`Empirical/QM/ColbeckRenner.lean`); `specs/colbeck-renner-note.md`; `specs/BACKLOG.md` #23;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.ChainedBell

variable {X Y O : Type*} [Fintype O] [DecidableEq O]

/-! ### Marginals, agreement, and the two one-pair links -/

/-- Alice's marginal: the probability that she reads `i` at setting `x`, when Bob measures `y`. -/
def marginalA (P : X → Y → O → O → ℝ) (x : X) (y : Y) (i : O) : ℝ := ∑ j, P x y i j

/-- Bob's marginal: the probability that he reads `j` at setting `y`, when Alice measures `x`. -/
def marginalB (P : X → Y → O → O → ℝ) (x : X) (y : Y) (j : O) : ℝ := ∑ i, P x y i j

/-- The probability that the two wings read the same outcome. -/
def agree (P : X → Y → O → O → ℝ) (o oc : O) (x : X) (y : Y) : ℝ := P x y o o + P x y oc oc

/-- The probability that the two wings read different outcomes. -/
def disagree (P : X → Y → O → O → ℝ) (o oc : O) (x : X) (y : Y) : ℝ := P x y o oc + P x y oc o

section TwoOutcome

variable {P : X → Y → O → O → ℝ} {o oc : O} {x : X} {y : Y}

/-- A sum over a two-element outcome type is a two-term sum. -/
theorem sum_two {M : Type*} [AddCommMonoid M] (huniv : (Finset.univ : Finset O) = {o, oc})
    (hoc : oc ≠ o) (f : O → M) : ∑ i, f i = f o + f oc := by
  rw [huniv, Finset.sum_pair (Ne.symm hoc)]

/-- Alice's marginal, as a two-term sum. -/
theorem marginalA_eq (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o) (i : O) :
    marginalA P x y i = P x y i o + P x y i oc :=
  sum_two huniv hoc _

/-- Bob's marginal, as a two-term sum. -/
theorem marginalB_eq (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o) (j : O) :
    marginalB P x y j = P x y o j + P x y oc j :=
  sum_two huniv hoc _

/-- The normalisation of a two-outcome law, as a four-term identity. -/
theorem sum_eq_four (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o) :
    ∑ i, ∑ j, P x y i j = P x y o o + P x y o oc + (P x y oc o + P x y oc oc) := by
  rw [sum_two huniv hoc (fun i => ∑ j, P x y i j), sum_two huniv hoc (fun j => P x y o j),
    sum_two huniv hoc (fun j => P x y oc j)]

/-- Agreement and disagreement partition the normalisation. -/
theorem agree_add_disagree_eq_one (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o)
    (hsum : ∑ i, ∑ j, P x y i j = 1) : agree P o oc x y + disagree P o oc x y = 1 := by
  rw [sum_eq_four huniv hoc] at hsum
  rw [agree, disagree]
  linarith

/-- ★ **The correlated link.** Two marginals of one joint distribution differ by at most the
probability that the outcomes disagree. -/
theorem abs_marginalA_sub_marginalB_le (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o)
    (hnn : ∀ i j, 0 ≤ P x y i j) (i : O) :
    |marginalA P x y i - marginalB P x y i| ≤ disagree P o oc x y := by
  have hne : o ≠ oc := Ne.symm hoc
  have hmem : i = o ∨ i = oc := by
    have : i ∈ ({o, oc} : Finset O) := huniv ▸ Finset.mem_univ i
    simpa using this
  rw [marginalA_eq huniv hoc, marginalB_eq huniv hoc, disagree]
  rcases hmem with rfl | rfl
  · rw [abs_le]
    exact ⟨by linarith [hnn i oc, hnn oc i], by linarith [hnn i oc, hnn oc i]⟩
  · rw [abs_le]
    exact ⟨by linarith [hnn o i, hnn i o], by linarith [hnn o i, hnn i o]⟩

/-- ★ **The anticorrelated link.** Two marginals of one joint distribution add to `1` up to the
probability that the outcomes agree. -/
theorem abs_marginalA_add_marginalB_sub_one_le (huniv : (Finset.univ : Finset O) = {o, oc})
    (hoc : oc ≠ o) (hnn : ∀ i j, 0 ≤ P x y i j) (hsum : ∑ i, ∑ j, P x y i j = 1) (i : O) :
    |marginalA P x y i + marginalB P x y i - 1| ≤ agree P o oc x y := by
  have hmem : i = o ∨ i = oc := by
    have : i ∈ ({o, oc} : Finset O) := huniv ▸ Finset.mem_univ i
    simpa using this
  rw [sum_eq_four huniv hoc] at hsum
  rw [marginalA_eq huniv hoc, marginalB_eq huniv hoc, agree]
  rcases hmem with rfl | rfl
  · rw [abs_le]
    exact ⟨by linarith [hnn i i, hnn oc oc], by linarith [hnn i i, hnn oc oc]⟩
  · rw [abs_le]
    exact ⟨by linarith [hnn o o, hnn i i], by linarith [hnn o o, hnn i i]⟩

end TwoOutcome

/-! ### The chained walk -/

/-- The total disagreement along the alternating walk `A 0, B 0, A 1, B 1, …, A n, B n`: one term
for each of its `2n + 1` links. -/
def chainCost (P : X → Y → O → O → ℝ) (o oc : O) (A : ℕ → X) (B : ℕ → Y) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), disagree P o oc (A i) (B i)) +
    ∑ i ∈ Finset.range n, disagree P o oc (A (i + 1)) (B i)

omit [Fintype O] [DecidableEq O] in
/-- Extending the walk by one node pair adds its two links. -/
theorem chainCost_succ (P : X → Y → O → O → ℝ) (o oc : O) (A : ℕ → X) (B : ℕ → Y) (n : ℕ) :
    chainCost P o oc A B (n + 1)
      = chainCost P o oc A B n + disagree P o oc (A (n + 1)) (B n)
        + disagree P o oc (A (n + 1)) (B (n + 1)) := by
  simp only [chainCost, Finset.sum_range_succ]
  ring

section Walk

variable {P : X → Y → O → O → ℝ} {o oc : O}

/-- ★★ **The chained walk.** For a no-signalling law, the marginal at one end of the alternating
walk and the marginal at the other end differ by at most the walk's total disagreement. The
hypotheses `hA` and `hB` are no-signalling: each wing's marginal is a function of that wing's
setting alone, which is what allows one-pair links to be composed across different pairs. -/
theorem abs_marginalA_sub_marginalB_chain_le (huniv : (Finset.univ : Finset O) = {o, oc})
    (hoc : oc ≠ o) (hnn : ∀ x y i j, 0 ≤ P x y i j)
    (hA : ∀ x y y' i, marginalA P x y i = marginalA P x y' i)
    (hB : ∀ x x' y j, marginalB P x y j = marginalB P x' y j)
    (A : ℕ → X) (B : ℕ → Y) (i : O) (n : ℕ) :
    |marginalA P (A 0) (B 0) i - marginalB P (A n) (B n) i| ≤ chainCost P o oc A B n := by
  induction n with
  | zero =>
    have h := abs_marginalA_sub_marginalB_le huniv hoc (hnn (A 0) (B 0)) i
    simpa [chainCost] using h
  | succ n ih =>
    have hmid : |marginalB P (A n) (B n) i - marginalA P (A (n + 1)) (B (n + 1)) i|
        ≤ disagree P o oc (A (n + 1)) (B n) := by
      rw [hB (A n) (A (n + 1)) (B n) i, hA (A (n + 1)) (B (n + 1)) (B n) i, abs_sub_comm]
      exact abs_marginalA_sub_marginalB_le huniv hoc (hnn (A (n + 1)) (B n)) i
    have hlast : |marginalA P (A (n + 1)) (B (n + 1)) i - marginalB P (A (n + 1)) (B (n + 1)) i|
        ≤ disagree P o oc (A (n + 1)) (B (n + 1)) :=
      abs_marginalA_sub_marginalB_le huniv hoc (hnn (A (n + 1)) (B (n + 1))) i
    have hstep :
        |marginalA P (A 0) (B 0) i - marginalB P (A (n + 1)) (B (n + 1)) i|
          ≤ |marginalA P (A 0) (B 0) i - marginalB P (A n) (B n) i|
            + |marginalB P (A n) (B n) i - marginalA P (A (n + 1)) (B (n + 1)) i|
            + |marginalA P (A (n + 1)) (B (n + 1)) i
                - marginalB P (A (n + 1)) (B (n + 1)) i| := by
      refine (abs_sub_le _ (marginalA P (A (n + 1)) (B (n + 1)) i) _).trans ?_
      have := abs_sub_le (marginalA P (A 0) (B 0) i) (marginalB P (A n) (B n) i)
        (marginalA P (A (n + 1)) (B (n + 1)) i)
      linarith
    rw [chainCost_succ]
    linarith

/-- ★★★ **Chained uniformity.** Close the walk with an anticorrelated link between its two ends:
then Alice's marginal at `A 0` is within half the total of the walk's disagreements and the closing
agreement of `1 / 2`. A chain of correlations that closes up with one reversal leaves no room for a
biased marginal. -/
theorem abs_marginalA_sub_half_le (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o)
    (hnn : ∀ x y i j, 0 ≤ P x y i j) (hsum : ∀ x y, ∑ i, ∑ j, P x y i j = 1)
    (hA : ∀ x y y' i, marginalA P x y i = marginalA P x y' i)
    (hB : ∀ x x' y j, marginalB P x y j = marginalB P x' y j)
    (A : ℕ → X) (B : ℕ → Y) (i : O) (n : ℕ) :
    |marginalA P (A 0) (B 0) i - 1 / 2|
      ≤ (chainCost P o oc A B n + agree P o oc (A 0) (B n)) / 2 := by
  have hwalk := abs_marginalA_sub_marginalB_chain_le huniv hoc hnn hA hB A B i n
  have hclose : |marginalA P (A 0) (B 0) i + marginalB P (A n) (B n) i - 1|
      ≤ agree P o oc (A 0) (B n) := by
    rw [hB (A n) (A 0) (B n) i, hA (A 0) (B 0) (B n) i]
    exact abs_marginalA_add_marginalB_sub_one_le huniv hoc (hnn (A 0) (B n)) (hsum (A 0) (B n)) i
  rw [abs_le] at hwalk hclose ⊢
  constructor <;> [linarith [hwalk.1, hclose.1]; linarith [hwalk.2, hclose.2]]

end Walk

/-! ### Every component of a mixture inherits the bound -/

section Mixture

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
variable {q : Ξ → X → Y → O → O → ℝ} {Q : X → Y → O → O → ℝ} {o oc : O}

omit [DecidableEq O] in
/-- A marginal of a mixture component is integrable when the law's entries are. -/
theorem integrable_marginalA (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (x : X) (y : Y) (i : O) : Integrable (fun ξ => marginalA (q ξ) x y i) μ :=
  integrable_finsetSum _ fun j _ => hint x y i j

omit [DecidableEq O] in
/-- Mixing commutes with taking a marginal. -/
theorem integral_marginalA (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (hmix : ∀ x y i j, ∫ ξ, q ξ x y i j ∂μ = Q x y i j) (x : X) (y : Y) (i : O) :
    ∫ ξ, marginalA (q ξ) x y i ∂μ = marginalA Q x y i := by
  simp only [marginalA]
  rw [integral_finsetSum _ fun j _ => hint x y i j]
  exact Finset.sum_congr rfl fun j _ => hmix x y i j

omit [Fintype O] [DecidableEq O] in
/-- Disagreement of a mixture component is integrable when the law's entries are. -/
theorem integrable_disagree (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (x : X) (y : Y) : Integrable (fun ξ => disagree (q ξ) o oc x y) μ :=
  (hint x y o oc).add (hint x y oc o)

omit [Fintype O] [DecidableEq O] in
/-- Mixing commutes with disagreement. -/
theorem integral_disagree (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (hmix : ∀ x y i j, ∫ ξ, q ξ x y i j ∂μ = Q x y i j) (x : X) (y : Y) :
    ∫ ξ, disagree (q ξ) o oc x y ∂μ = disagree Q o oc x y := by
  rw [disagree, ← hmix x y o oc, ← hmix x y oc o]
  exact integral_add (hint x y o oc) (hint x y oc o)

omit [Fintype O] [DecidableEq O] in
/-- Agreement of a mixture component is integrable when the law's entries are. -/
theorem integrable_agree (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (x : X) (y : Y) : Integrable (fun ξ => agree (q ξ) o oc x y) μ :=
  (hint x y o o).add (hint x y oc oc)

omit [Fintype O] [DecidableEq O] in
/-- Mixing commutes with agreement. -/
theorem integral_agree (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (hmix : ∀ x y i j, ∫ ξ, q ξ x y i j ∂μ = Q x y i j) (x : X) (y : Y) :
    ∫ ξ, agree (q ξ) o oc x y ∂μ = agree Q o oc x y := by
  rw [agree, ← hmix x y o o, ← hmix x y oc oc]
  exact integral_add (hint x y o o) (hint x y oc oc)

omit [Fintype O] [DecidableEq O] in
/-- The walk's cost for a mixture component is integrable when the law's entries are. -/
theorem integrable_chainCost (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (A : ℕ → X) (B : ℕ → Y) (n : ℕ) :
    Integrable (fun ξ => chainCost (q ξ) o oc A B n) μ := by
  refine Integrable.add ?_ ?_
  · exact integrable_finsetSum _ fun i _ => integrable_disagree hint (A i) (B i)
  · exact integrable_finsetSum _ fun i _ => integrable_disagree hint (A (i + 1)) (B i)

omit [Fintype O] [DecidableEq O] in
/-- Mixing commutes with the walk's cost: the functional is affine in the law. -/
theorem integral_chainCost (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (hmix : ∀ x y i j, ∫ ξ, q ξ x y i j ∂μ = Q x y i j) (A : ℕ → X) (B : ℕ → Y) (n : ℕ) :
    ∫ ξ, chainCost (q ξ) o oc A B n ∂μ = chainCost Q o oc A B n := by
  have h₁ : ∫ ξ, (∑ i ∈ Finset.range (n + 1), disagree (q ξ) o oc (A i) (B i)) ∂μ
      = ∑ i ∈ Finset.range (n + 1), disagree Q o oc (A i) (B i) := by
    rw [integral_finsetSum _ fun i _ => integrable_disagree hint (A i) (B i)]
    exact Finset.sum_congr rfl fun i _ => integral_disagree hint hmix (A i) (B i)
  have h₂ : ∫ ξ, (∑ i ∈ Finset.range n, disagree (q ξ) o oc (A (i + 1)) (B i)) ∂μ
      = ∑ i ∈ Finset.range n, disagree Q o oc (A (i + 1)) (B i) := by
    rw [integral_finsetSum _ fun i _ => integrable_disagree hint (A (i + 1)) (B i)]
    exact Finset.sum_congr rfl fun i _ => integral_disagree hint hmix (A (i + 1)) (B i)
  rw [chainCost, ← h₁, ← h₂]
  exact integral_add
    (integrable_finsetSum _ fun i _ => integrable_disagree hint (A i) (B i))
    (integrable_finsetSum _ fun i _ => integrable_disagree hint (A (i + 1)) (B i))

/-- ★★★ **Every component of a mixture inherits the chained bound.** If each `q ξ` is a
no-signalling two-outcome law and the mixture over `ξ` reproduces `Q`, then in mean over `ξ` the
components' marginals at `A 0` sit within `1 / 2` up to the bound computed from `Q` alone. So a
chain on which `Q` is nearly perfectly correlated pins down not just `Q`'s own marginal but every
component's. -/
theorem integral_abs_marginalA_sub_half_le [IsProbabilityMeasure μ]
    (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o)
    (hnn : ∀ ξ x y i j, 0 ≤ q ξ x y i j) (hsum : ∀ ξ x y, ∑ i, ∑ j, q ξ x y i j = 1)
    (hA : ∀ ξ x y y' i, marginalA (q ξ) x y i = marginalA (q ξ) x y' i)
    (hB : ∀ ξ x x' y j, marginalB (q ξ) x y j = marginalB (q ξ) x' y j)
    (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (hmix : ∀ x y i j, ∫ ξ, q ξ x y i j ∂μ = Q x y i j)
    (A : ℕ → X) (B : ℕ → Y) (i : O) (n : ℕ) :
    ∫ ξ, |marginalA (q ξ) (A 0) (B 0) i - 1 / 2| ∂μ
      ≤ (chainCost Q o oc A B n + agree Q o oc (A 0) (B n)) / 2 := by
  have hle : ∀ ξ, |marginalA (q ξ) (A 0) (B 0) i - 1 / 2|
      ≤ (chainCost (q ξ) o oc A B n + agree (q ξ) o oc (A 0) (B n)) / 2 := fun ξ =>
    abs_marginalA_sub_half_le huniv hoc (hnn ξ) (hsum ξ) (hA ξ) (hB ξ) A B i n
  have hif : Integrable (fun ξ => |marginalA (q ξ) (A 0) (B 0) i - 1 / 2|) μ :=
    ((integrable_marginalA hint (A 0) (B 0) i).sub (integrable_const _)).abs
  have hig : Integrable
      (fun ξ => (chainCost (q ξ) o oc A B n + agree (q ξ) o oc (A 0) (B n)) / 2) μ :=
    (((integrable_chainCost hint A B n).add (integrable_agree hint (A 0) (B n)))).div_const 2
  have hmono := integral_mono hif hig hle
  rw [integral_div, integral_add (integrable_chainCost hint A B n)
    (integrable_agree hint (A 0) (B n)), integral_chainCost hint hmix A B n,
    integral_agree hint hmix (A 0) (B n)] at hmono
  exact hmono

/-- ★ **The contrapositive.** A mixture whose components sharpen the marginal past the chained
bound must contain a component that signals: no-signalling for every component is exactly what the
bound needs. -/
theorem exists_signalling_of_sharp_integral [IsProbabilityMeasure μ]
    (huniv : (Finset.univ : Finset O) = {o, oc}) (hoc : oc ≠ o)
    (hnn : ∀ ξ x y i j, 0 ≤ q ξ x y i j) (hsum : ∀ ξ x y, ∑ i, ∑ j, q ξ x y i j = 1)
    (hint : ∀ x y i j, Integrable (fun ξ => q ξ x y i j) μ)
    (hmix : ∀ x y i j, ∫ ξ, q ξ x y i j ∂μ = Q x y i j)
    (A : ℕ → X) (B : ℕ → Y) (i : O) (n : ℕ)
    (hsharp : (chainCost Q o oc A B n + agree Q o oc (A 0) (B n)) / 2
      < ∫ ξ, |marginalA (q ξ) (A 0) (B 0) i - 1 / 2| ∂μ) :
    ¬ ((∀ ξ x y y' i, marginalA (q ξ) x y i = marginalA (q ξ) x y' i) ∧
        ∀ ξ x x' y j, marginalB (q ξ) x y j = marginalB (q ξ) x' y j) := by
  intro h
  exact absurd (integral_abs_marginalA_sub_half_le huniv hoc hnn hsum h.1 h.2 hint hmix A B i n)
    (not_le.mpr hsharp)

end Mixture

end ProbabilityTheory.ChainedBell

end
