import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Empirical: Hardy's paradox (nonlocality without inequalities)

**Category:** 3-Local. The combinatorial LHV impossibility is
QM-generic (no CSD ontology); promotion-ready to 2-Framework on demand.

## What Hardy says

Hardy 1992-1993: for almost all two-qubit entangled states, there
exists a choice of two binary measurements on each side
(Alice: `A`, `A'`; Bob: `B`, `B'`, outcomes `±1`) and a positive
joint probability `P(A=+1, B=+1) > 0` such that QM also predicts
three forbidden joint outcomes:

```
P(A=+1, B=+1) = α > 0     -- the "Hardy probability"
P(A=+1, B'=-1) = 0        -- forbidden: A=+1 implies B'=+1
P(A'=-1, B=+1) = 0        -- forbidden: B=+1 implies A'=+1
P(A'=+1, B'=+1) = 0       -- forbidden: A' and B' can't both be +1
```

Under any local hidden-variable model with a joint outcome
distribution over `(A, A', B, B') ∈ {±1}^4`, the four constraints
above are jointly unsatisfiable:

1. The positive Hardy probability forces some outcome quadruple `x`
   with `A(x)=+1, B(x)=+1, p(x) > 0`.
2. The constraint `P(A=+1, B'=-1) = 0` forces `B'(x)=+1` (else `x`
   would be a positive contribution to a zero-sum).
3. Similarly, `P(A'=-1, B=+1) = 0` forces `A'(x)=+1`.
4. But then `x` has `A'=+1, B'=+1`, so its probability contributes to
   `P(A'=+1, B'=+1)`, which is zero. Contradiction with `p(x) > 0`.

This is the structural signature of QM nonlocality "without
inequalities": a single-shot algebraic contradiction (like GHZ) but on
**two qubits** and for **almost all** entangled states (unlike GHZ
which requires the specific 3-qubit GHZ state, or CHSH which is a
statistical inequality violation).

## Distinction from CHSH, GHZ, KS, Mermin-Peres

- **CHSH (Bell.lean):** statistical inequality, 2-party.
- **GHZ (Multipartite/GHZ.lean):** algebraic single-shot, 3-party.
- **KS (Contextuality/KS18.lean):** combinatorial contextuality,
  single-system.
- **Mermin-Peres (Contextuality/MerminPeres.lean):** algebraic
  single-shot, 2-qubit, contextuality.
- **Hardy (this file):** algebraic single-shot, 2-party, nonlocality.
  Distinct from GHZ in that it works for almost any entangled 2-qubit
  state (with appropriate choice of measurements), not just the
  specific GHZ state.

## Experimental verification

- Hardy 1992: *Phys. Rev. Lett.* **68**, 2981 ("Quantum mechanics,
  local realistic theories, and Lorentz-invariant realistic theories").
- Hardy 1993: *Phys. Rev. Lett.* **71**, 1665 ("Nonlocality for two
  particles without inequalities for almost all entangled states").
- Lundeen, Steinberg 2009: *Phys. Rev. Lett.* **102**, 020404
  (experimental confirmation via weak measurements).

## What this file proves

`no_lhv_hardy`: there is no probability distribution
`p : (Fin 2)^4 → ℝ` (non-negative, marginal sums) satisfying the four
Hardy constraints simultaneously.

Combinatorial; cites only the foundational triple.

## What this file does *not* prove

The QM-side identities establishing that some specific 2-qubit state
and four observables actually realise the four Hardy constraints
predicted in the docstring. (Hardy 1993 gives the construction; a
Lean formalisation would parametrise by the entanglement parameter
and verify each probability via inner-product / Born computations.
Deferred to a follow-up tranche, in the same spirit as the
"QM-side operator identities deferred" reading in KS18.)

## Coding convention

We index outcome quadruples by `Outcome := Fin 2 × Fin 2 × Fin 2 × Fin 2`.
The coordinates are `(A, A', B, B')`, with `Fin 2`-value `1` meaning
QM-outcome `+1` and `Fin 2`-value `0` meaning QM-outcome `-1`.
-/

namespace CSD
namespace Empirical
namespace Hardy

open Finset

/-- An LHV outcome quadruple: `(A, A', B, B')` with each coordinate
in `Fin 2` (`1` = QM outcome `+1`, `0` = QM outcome `-1`). -/
abbrev Outcome := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- **No LHV distribution satisfies the four Hardy constraints.**

For any probability distribution `p : Outcome → ℝ` (non-negative)
satisfying:

- `∑ x with A(x)=+1, B(x)=+1, p(x) > 0` (positive Hardy probability),
- `∑ x with A(x)=+1, B'(x)=-1, p(x) = 0` (forbidden joint #1),
- `∑ x with A'(x)=-1, B(x)=+1, p(x) = 0` (forbidden joint #2),
- `∑ x with A'(x)=+1, B'(x)=+1, p(x) = 0` (forbidden joint #3),

a contradiction follows by the chain:

1. The positive sum forces some `x` with `A(x)=B(x)=+1, p(x) > 0`.
2. The first zero-sum forces `B'(x) = +1` (else `p(x) = 0`).
3. The second zero-sum forces `A'(x) = +1`.
4. The third zero-sum then forces `p(x) = 0`, contradicting `p(x) > 0`. -/
theorem no_lhv_hardy :
    ¬ ∃ p : Outcome → ℝ,
      (∀ x, 0 ≤ p x) ∧
      0 < (∑ x ∈ univ.filter (fun x : Outcome =>
              x.1 = 1 ∧ x.2.2.1 = 1), p x) ∧
      (∑ x ∈ univ.filter (fun x : Outcome =>
              x.1 = 1 ∧ x.2.2.2 = 0), p x) = 0 ∧
      (∑ x ∈ univ.filter (fun x : Outcome =>
              x.2.1 = 0 ∧ x.2.2.1 = 1), p x) = 0 ∧
      (∑ x ∈ univ.filter (fun x : Outcome =>
              x.2.1 = 1 ∧ x.2.2.2 = 1), p x) = 0 := by
  rintro ⟨p, hnn, hAB_pos, hAB'_zero, hA'B_zero, hA'B'_zero⟩
  -- Step 1: extract a positive-probability witness x with A=1, B=1.
  have hAB_zero_iff :=
    Finset.sum_eq_zero_iff_of_nonneg (s := univ.filter
        (fun x : Outcome => x.1 = 1 ∧ x.2.2.1 = 1))
        (f := p) (fun x _ => hnn x)
  -- The positive sum hAB_pos rules out the "all-zero" right side.
  have h_exists_pos : ∃ x ∈ univ.filter
      (fun x : Outcome => x.1 = 1 ∧ x.2.2.1 = 1), 0 < p x := by
    by_contra h_none
    push_neg at h_none
    have h_all_zero : ∀ x ∈ univ.filter
        (fun x : Outcome => x.1 = 1 ∧ x.2.2.1 = 1), p x = 0 := by
      intro x hx
      exact le_antisymm (h_none x hx) (hnn x)
    have h_sum_zero := hAB_zero_iff.mpr h_all_zero
    linarith
  obtain ⟨x, hx_in, hx_pos⟩ := h_exists_pos
  have hxAB := (mem_filter.mp hx_in).2
  have hxA : x.1 = 1 := hxAB.1
  have hxB : x.2.2.1 = 1 := hxAB.2
  -- Step 2: from hAB'_zero and p ≥ 0, every outcome with A=1, B'=0 has p = 0.
  -- So x.2.2.2 ≠ 0, i.e., x.2.2.2 = 1.
  have hAB'_all_zero : ∀ y ∈ univ.filter
      (fun y : Outcome => y.1 = 1 ∧ y.2.2.2 = 0), p y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn y)).mp hAB'_zero
  have hxB' : x.2.2.2 = 1 := by
    by_contra hne
    have h_eq_zero : x.2.2.2 = 0 := by
      have hlt := x.2.2.2.isLt
      have hne_val : x.2.2.2.val ≠ 1 := fun h => hne (Fin.eq_of_val_eq h)
      have hval : x.2.2.2.val = 0 := by omega
      exact Fin.eq_of_val_eq hval
    have hx_in_AB' : x ∈ univ.filter
        (fun y : Outcome => y.1 = 1 ∧ y.2.2.2 = 0) := by
      simp [mem_filter, hxA, h_eq_zero]
    have hpx_zero : p x = 0 := hAB'_all_zero x hx_in_AB'
    linarith
  -- Step 3: from hA'B_zero, every outcome with A'=0, B=1 has p = 0.
  -- So x.2.1 ≠ 0, i.e., x.2.1 = 1.
  have hA'B_all_zero : ∀ y ∈ univ.filter
      (fun y : Outcome => y.2.1 = 0 ∧ y.2.2.1 = 1), p y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn y)).mp hA'B_zero
  have hxA' : x.2.1 = 1 := by
    by_contra hne
    have h_eq_zero : x.2.1 = 0 := by
      have hlt := x.2.1.isLt
      have hne_val : x.2.1.val ≠ 1 := fun h => hne (Fin.eq_of_val_eq h)
      have hval : x.2.1.val = 0 := by omega
      exact Fin.eq_of_val_eq hval
    have hx_in_A'B : x ∈ univ.filter
        (fun y : Outcome => y.2.1 = 0 ∧ y.2.2.1 = 1) := by
      simp [mem_filter, h_eq_zero, hxB]
    have hpx_zero : p x = 0 := hA'B_all_zero x hx_in_A'B
    linarith
  -- Step 4: x has A'=1 AND B'=1, so x is in the (A'=1, B'=1) zero-sum set.
  -- Hence p x = 0, contradicting hx_pos.
  have hA'B'_all_zero : ∀ y ∈ univ.filter
      (fun y : Outcome => y.2.1 = 1 ∧ y.2.2.2 = 1), p y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn y)).mp hA'B'_zero
  have hx_in_A'B' : x ∈ univ.filter
      (fun y : Outcome => y.2.1 = 1 ∧ y.2.2.2 = 1) := by
    simp [mem_filter, hxA', hxB']
  have hpx_zero : p x = 0 := hA'B'_all_zero x hx_in_A'B'
  linarith

end Hardy
end Empirical
end CSD
