/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# The group-commutator contraction: Solovay–Kitaev's shrinking lemma

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #112, the first brick of #74's split.

Two gates near the identity have a group commutator **quadratically** nearer it. That quadratic
gain is the entire engine of the Solovay–Kitaev recursion: one level of commutators turns an
accuracy `δ` into an accuracy `2δ²`, and five words into one.

## What is proved

* ★ `norm_mul_sub_mul_comm_le` — in **any** normed ring, `‖VW − WV‖ ≤ 2‖V − 1‖·‖W − 1‖`. The whole
  content is the identity `VW − WV = (V−1)(W−1) − (W−1)(V−1)`: the commutator sees only how far the
  factors are from `1`, which is why being near the identity is what makes it small;
* ★★ `CStarRing.norm_groupCommutator_sub_one_le` — for **unitaries** in a C\*-algebra,
  `‖VWV⋆W⋆ − 1‖ ≤ 2‖V − 1‖·‖W − 1‖`. Unitarity enters exactly twice: to write
  `VWV⋆W⋆ − 1 = (VW − WV)(V⋆W⋆)`, and to drop the trailing unitary from the norm;
* ★★ `CStarRing.norm_groupCommutator_sub_one_le_two_mul_sq` — the shrinking lemma as the recursion
  uses it: both factors within `δ` of `1` gives `2δ²`, and
  ★★ `CStarRing.norm_groupCommutator_sub_one_lt` — **the contraction**: for `0 < δ < 1/2` the
  commutator is *strictly* closer to `1` than its factors were;
* ★ `CStarRing.norm_mul_sub_mul_le` — and the companion the recursion needs for its error budget:
  the product of unitaries is **stable**, `‖AB − A′B′‖ ≤ ‖A − A′‖ + ‖B − B′‖`, with
  ★★ `CStarRing.norm_groupCommutator_sub_groupCommutator_le` giving `4ε` for the commutator of two
  `ε`-approximations.

## Honest scope

⚠️ **No gate counts, and no algorithm.** This is the shrinking lemma alone. The recursion that
consumes it (#115), the `ε`-net it starts from (#113) and the decomposition that produces the
commutators in the first place (#114) are separate rows, and the `O(log^c(1/ε))` bound is #116.

⚠️ **Constants are the stated ones, not optimal.** `2` in the contraction and `4` in the
perturbation are what the telescoping gives; no attempt is made to sharpen either, and the
Solovay–Kitaev exponent does not depend on them.

⚠️ **The quadratic gain needs `δ < 1/2`.** Above that the bound is weaker than the input and says
nothing — which is why the algorithm needs a base accuracy from the net before it can recurse.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81,
Lemma 2 and §3; M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information*, Appendix 3;
`Mathlib.Analysis.CStarAlgebra.Basic` (`CStarRing.norm_mem_unitary_mul`,
`CStarRing.norm_mul_mem_unitary`); `specs/BACKLOG.md` #112, #74, #113, #114, #115, #116.
-/

@[expose] public section

variable {E : Type*}

/-! ### The commutator sees only the distance to the identity -/

/-- ★ **In any normed ring, the commutator is quadratic in the distance to the identity.**
`VW − WV = (V − 1)(W − 1) − (W − 1)(V − 1)`, so two elements near `1` barely fail to commute. -/
theorem norm_mul_sub_mul_comm_le [NormedRing E] (V W : E) :
    ‖V * W - W * V‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  have key : V * W - W * V = (V - 1) * (W - 1) - (W - 1) * (V - 1) := by noncomm_ring
  rw [key]
  calc ‖(V - 1) * (W - 1) - (W - 1) * (V - 1)‖
      ≤ ‖(V - 1) * (W - 1)‖ + ‖(W - 1) * (V - 1)‖ := norm_sub_le _ _
    _ ≤ ‖V - 1‖ * ‖W - 1‖ + ‖W - 1‖ * ‖V - 1‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖V - 1‖ * ‖W - 1‖ := by ring

namespace CStarRing

variable [NormedRing E] [StarRing E] [CStarRing E]

/-! ### The shrinking lemma -/

omit [CStarRing E] in
/-- The group commutator of two unitaries, written out. -/
theorem groupCommutator_sub_one_eq {V W : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E) :
    V * W * star V * star W - 1 = (V * W - W * V) * (star V * star W) := by
  have h1 : W * V * (star V * star W) = 1 := by
    rw [show W * V * (star V * star W) = W * (V * star V) * star W from by noncomm_ring,
      Unitary.mul_star_self_of_mem hV, mul_one, Unitary.mul_star_self_of_mem hW]
  rw [sub_mul, h1]
  noncomm_ring

/-- ★★ **The shrinking lemma.** Two unitaries within `‖V − 1‖` and `‖W − 1‖` of the identity have a
group commutator within `2‖V − 1‖·‖W − 1‖` of it.

Unitarity is used exactly twice: `VWV⋆W⋆ − 1 = (VW − WV)(V⋆W⋆)`, and the trailing unitary drops out
of the norm. -/
theorem norm_groupCommutator_sub_one_le {V W : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E) :
    ‖V * W * star V * star W - 1‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  rw [groupCommutator_sub_one_eq hV hW,
    norm_mul_mem_unitary _ (mul_mem (Unitary.star_mem hV) (Unitary.star_mem hW))]
  exact norm_mul_sub_mul_comm_le V W

/-- ★★ **The shrinking lemma as the recursion uses it**: both factors within `δ` of the identity
gives `2δ²`. -/
theorem norm_groupCommutator_sub_one_le_two_mul_sq {V W : E} (hV : V ∈ unitary E)
    (hW : W ∈ unitary E) {δ : ℝ} (hV' : ‖V - 1‖ ≤ δ) (hW' : ‖W - 1‖ ≤ δ) :
    ‖V * W * star V * star W - 1‖ ≤ 2 * δ ^ 2 := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hV'
  refine le_trans (norm_groupCommutator_sub_one_le hV hW) ?_
  calc 2 * ‖V - 1‖ * ‖W - 1‖ ≤ 2 * δ * δ := by gcongr
    _ = 2 * δ ^ 2 := by ring

/-- ★★ **The contraction.** Below `δ = 1/2` the commutator of two `δ`-close unitaries is *strictly*
closer to the identity than its factors were — the step that makes the Solovay–Kitaev iteration
converge, and the reason the algorithm needs a base accuracy before it can recurse. -/
theorem norm_groupCommutator_sub_one_lt {V W : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    {δ : ℝ} (hpos : 0 < δ) (hhalf : δ < 1 / 2) (hV' : ‖V - 1‖ ≤ δ) (hW' : ‖W - 1‖ ≤ δ) :
    ‖V * W * star V * star W - 1‖ < δ := by
  refine lt_of_le_of_lt (norm_groupCommutator_sub_one_le_two_mul_sq hV hW hV' hW') ?_
  nlinarith

/-! ### Stability: the error budget the recursion needs -/

/-- ★ **A product of unitaries is stable.** Replacing each factor by an approximation moves the
product by at most the sum of the two errors. -/
theorem norm_mul_sub_mul_le {A B A' B' : E} (hB : B ∈ unitary E) (hA' : A' ∈ unitary E) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ + ‖B - B'‖ := by
  have key : A * B - A' * B' = (A - A') * B + A' * (B - B') := by noncomm_ring
  rw [key]
  refine le_trans (norm_add_le _ _) (le_of_eq ?_)
  rw [norm_mul_mem_unitary _ hB, norm_mem_unitary_mul _ hA']

/-- ★★ **The commutator of two `ε`-approximations is a `4ε`-approximation of the commutator.** The
four factors each move by at most `ε` — the adjoints by `norm_star` — and the product is stable, so
the error budget the Solovay–Kitaev recursion carries is linear in the input error. -/
theorem norm_groupCommutator_sub_groupCommutator_le {V W V' W' : E} (hV : V ∈ unitary E)
    (hW : W ∈ unitary E) (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E) {ε : ℝ}
    (hVe : ‖V - V'‖ ≤ ε) (hWe : ‖W - W'‖ ≤ ε) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖ ≤ 4 * ε := by
  have hstarV : ‖star V - star V'‖ ≤ ε := by
    rw [← star_sub, norm_star]
    exact hVe
  have hstarW : ‖star W - star W'‖ ≤ ε := by
    rw [← star_sub, norm_star]
    exact hWe
  have h1 : ‖V * W - V' * W'‖ ≤ ε + ε := by
    refine le_trans (norm_mul_sub_mul_le hW hV') ?_
    exact add_le_add hVe hWe
  have h2 : ‖V * W * star V - V' * W' * star V'‖ ≤ ε + ε + ε := by
    refine le_trans (norm_mul_sub_mul_le (Unitary.star_mem hV) (mul_mem hV' hW')) ?_
    exact add_le_add h1 hstarV
  refine le_trans (norm_mul_sub_mul_le (Unitary.star_mem hW)
    (mul_mem (mul_mem hV' hW') (Unitary.star_mem hV'))) ?_
  calc ‖V * W * star V - V' * W' * star V'‖ + ‖star W - star W'‖
      ≤ (ε + ε + ε) + ε := add_le_add h2 hstarW
    _ = 4 * ε := by ring

end CStarRing

end
