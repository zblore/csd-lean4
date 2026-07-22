/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Polyrith

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

@[expose] public section

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
    push Not at h_none
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

/-! ## QM-side Hardy realisation

A specific 2-qubit state and four observables (Pauli `Z` and `X` on each
side) realising the four Hardy probabilities predicted by QM.

**State** (unnormalised; the normalisation factor `1/√12` cancels in
"= 0" vs "≠ 0" reasoning):
```
|ψ⟩ ∝ |00⟩ + |01⟩ + |10⟩ - 3|11⟩
```

**Observables**: `A = B = Z` (computational basis, `+1` eigenstate `|0⟩`);
`A' = B' = X` (Hadamard basis, `+1` eigenstate `|+⟩ = |0⟩ + |1⟩`).

**Four amplitude identities** (squared moduli are the Hardy probabilities):
- `⟨0,0|ψ⟩ = 1` (proportional to `P(A=+1, B=+1) = 1/12 > 0`)
- `⟨0,−|ψ⟩ = 0` (`P(A=+1, B'=-1) = 0`)
- `⟨−,0|ψ⟩ = 0` (`P(A'=-1, B=+1) = 0`)
- `⟨+,+|ψ⟩ = 0` (`P(A'=+1, B'=+1) = 0`)

The fourth (load-bearing) identity reduces to the integer sum
`1 + 1 + 1 + (−3) = 0`. This is why the |11⟩-amplitude `δ = −3` is
load-bearing: the general Hardy algebraic condition
`α(α² + β² + γ²) + βγδ = 0` (derived from setting `⟨+,+|ψ⟩ = 0`)
becomes `3 + δ = 0` with `α = β = γ = 1`.

The construction here is not Hardy's maximum (≈ 9% from the golden-ratio
state); the integer-amplitude variant gives Hardy probability `1/12 ≈
8.3%`. The choice is for cleanest Lean algebra — no square-root
manipulation, all amplitudes ℤ.

Together with `no_lhv_hardy`, this closes the Hardy story: QM realises
the four constraints; no LHV distribution can.
-/

namespace HardyQM

open Finset

/-- The (unnormalised) Hardy state:
`|ψ⟩ = |00⟩ + |01⟩ + |10⟩ − 3|11⟩`. -/
def hardyVec : Fin 2 × Fin 2 → ℂ
  | (⟨0, _⟩, ⟨0, _⟩) => 1
  | (⟨0, _⟩, ⟨1, _⟩) => 1
  | (⟨1, _⟩, ⟨0, _⟩) => 1
  | (⟨1, _⟩, ⟨1, _⟩) => -3

/-- `|0⟩`: the `+1` eigenstate of `Z`. -/
def zPlus : Fin 2 → ℂ := ![1, 0]

/-- `|+⟩ = |0⟩ + |1⟩` (unnormalised): the `+1` eigenstate of `X`. -/
def xPlus : Fin 2 → ℂ := ![1, 1]

/-- `|−⟩ = −|0⟩ + |1⟩` (unnormalised): the `−1` eigenstate of `X`. -/
def xMinus : Fin 2 → ℂ := ![-1, 1]

/-- Joint amplitude `⟨a ⊗ b | ψ⟩` for `ψ : Fin 2 × Fin 2 → ℂ` and
single-qubit bras `a, b : Fin 2 → ℂ`. -/
noncomputable def jointAmplitude (a b : Fin 2 → ℂ) (ψ : Fin 2 × Fin 2 → ℂ) : ℂ :=
  ∑ p : Fin 2 × Fin 2, star (a p.1) * star (b p.2) * ψ p

/-- **Hardy amplitude 1**: `⟨0, 0 | ψ⟩ = 1` (proportional to the
positive Hardy probability `P(A=+1, B=+1) = 1/12`). -/
theorem hardyAmp_AB : jointAmplitude zPlus zPlus hardyVec = 1 := by
  simp [jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        zPlus, hardyVec]

/-- **Hardy amplitude 2**: `⟨0, − | ψ⟩ = 0` (`P(A=+1, B'=-1) = 0`).

The only contributing terms have `i = 0` (since `zPlus 1 = 0`):
`star(−1)·ψ(0,0) + star(1)·ψ(0,1) = −1·1 + 1·1 = 0`. -/
theorem hardyAmp_A_B'minus :
    jointAmplitude zPlus xMinus hardyVec = 0 := by
  simp [jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        zPlus, xMinus, hardyVec]

/-- **Hardy amplitude 3**: `⟨−, 0 | ψ⟩ = 0` (`P(A'=-1, B=+1) = 0`).

Symmetric to the previous: only `j = 0` contributes,
`star(−1)·ψ(0,0) + star(1)·ψ(1,0) = −1·1 + 1·1 = 0`. -/
theorem hardyAmp_A'minus_B :
    jointAmplitude xMinus zPlus hardyVec = 0 := by
  simp [jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        zPlus, xMinus, hardyVec]

/-- **Hardy amplitude 4** (load-bearing): `⟨+, + | ψ⟩ = 0`
(`P(A'=+1, B'=+1) = 0`).

All four `ψ` terms contribute: `1 + 1 + 1 + (−3) = 0`. This is the
specific reason `δ = −3` is the |11⟩-amplitude. -/
theorem hardyAmp_A'_B' :
    jointAmplitude xPlus xPlus hardyVec = 0 := by
  simp [jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        xPlus, hardyVec]
  ring

/-- **QM realises the Hardy constraints.** A specific 2-qubit state
and four observables exhibit the four Hardy probability identities,
demonstrating that the LHV-impossibility theorem `no_lhv_hardy` has
empirical content (QM violates LHV on this Hardy instance). -/
theorem exists_hardy_realisation :
    ∃ (ψ : Fin 2 × Fin 2 → ℂ) (a aPrime b bPrime aPrime_perp bPrime_perp : Fin 2 → ℂ),
      jointAmplitude a b ψ ≠ 0 ∧
      jointAmplitude a bPrime_perp ψ = 0 ∧
      jointAmplitude aPrime_perp b ψ = 0 ∧
      jointAmplitude aPrime bPrime ψ = 0 :=
  ⟨hardyVec, zPlus, xPlus, zPlus, xPlus, xMinus, xMinus,
   by rw [hardyAmp_AB]; norm_num,
   hardyAmp_A_B'minus,
   hardyAmp_A'minus_B,
   hardyAmp_A'_B'⟩

end HardyQM

/-! ## QM-side Hardy realisation at the golden-ratio maximum

The Hardy probability `1/12` from `HardyQM` is below Hardy's theoretical
maximum `(5√5 − 11)/2 ≈ 9.017%`. The maximum is achieved at the
**golden-ratio Hardy state**

```
|ψ_max⟩ ∝ |00⟩ + √φ |01⟩ + √φ |10⟩ − φ² |11⟩
```

where `φ = (1+√5)/2` is the golden ratio. This namespace exhibits the
golden-ratio state and verifies the four Hardy amplitude identities for
it, completing the "Hardy probability gap" by showing both
integer-amplitude (≈ 8.3%) and golden-ratio (≈ 9.017%) realisations.

The eigenstate vectors `aPrimeMax = (1, √φ)` and `bPrimeMinusMax = (-√φ, 1)`
are the unnormalised `+1` and `−1` eigenstates of the second-measurement
basis on each side (the basis whose `+1` eigenvector aligns with the
marginal `(α|0⟩ + γ|1⟩) ∝ (1|0⟩ + √φ |1⟩)` of the partially-traced
Hardy state).

**Load-bearing identity**: the fourth amplitude reduces to
`1 + 2φ − φ³`. The golden-ratio identity `φ³ = 2φ + 1` (proved below
from `φ² = φ + 1`) makes this zero.

The Hardy probability is `α² / ‖ψ_max‖² = 1 / (5φ + 3) = (5√5 − 11)/2`
after rationalisation. The numerical equality is left as a separate
follow-up; this namespace delivers the four amplitude identities
needed to satisfy the LHV-impossibility hypothesis.
-/

namespace HardyQMMax

open Finset

/-- The golden ratio `φ = (1 + √5)/2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  unfold phi
  have h5 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg _
  linarith

/-- The defining identity `φ² = φ + 1`. -/
lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  nlinarith [h]

/-- The cubic identity `φ³ = 2φ + 1` (the load-bearing fact for the
fourth Hardy amplitude at the golden-ratio maximum). Derived from
`φ² = φ + 1`: `φ³ = φ·φ² = φ(φ + 1) = φ² + φ = (φ + 1) + φ = 2φ + 1`. -/
lemma phi_cube : phi ^ 3 = 2 * phi + 1 := by
  have h := phi_sq
  nlinarith [h]

/-- `√φ` (positive square root of the golden ratio). -/
noncomputable def sqrtPhi : ℝ := Real.sqrt phi

lemma sqrtPhi_sq : sqrtPhi ^ 2 = phi := by
  unfold sqrtPhi
  exact Real.sq_sqrt phi_pos.le

/-- The golden-ratio Hardy state (unnormalised):
`|ψ_max⟩ = |00⟩ + √φ |01⟩ + √φ |10⟩ − φ² |11⟩`. -/
noncomputable def hardyMaxVec : Fin 2 × Fin 2 → ℂ
  | (⟨0, _⟩, ⟨0, _⟩) => 1
  | (⟨0, _⟩, ⟨1, _⟩) => (sqrtPhi : ℂ)
  | (⟨1, _⟩, ⟨0, _⟩) => (sqrtPhi : ℂ)
  | (⟨1, _⟩, ⟨1, _⟩) => -((phi ^ 2 : ℝ) : ℂ)

/-- `|a'⟩ = |0⟩ + √φ |1⟩` (unnormalised; the second-measurement
`+1` eigenstate aligned with the partially-traced Hardy state). -/
noncomputable def aPrimeMax : Fin 2 → ℂ := ![1, (sqrtPhi : ℂ)]

/-- `|a'_⊥⟩ = −√φ |0⟩ + |1⟩` (unnormalised; the orthogonal complement). -/
noncomputable def aPrimeMinusMax : Fin 2 → ℂ := ![-(sqrtPhi : ℂ), 1]

/-- **Max-Hardy amplitude 1**: `⟨0, 0 | ψ_max⟩ = 1` (positive). -/
theorem hardyMaxAmp_AB :
    HardyQM.jointAmplitude HardyQM.zPlus HardyQM.zPlus hardyMaxVec = 1 := by
  simp [HardyQM.jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        HardyQM.zPlus, hardyMaxVec]

/-- **Max-Hardy amplitude 2**: `⟨0, a'_⊥ | ψ_max⟩ = 0`.
Only `i = 0` contributes: `star(−√φ)·1 + star(1)·√φ = −√φ + √φ = 0`. -/
theorem hardyMaxAmp_A_B'minus :
    HardyQM.jointAmplitude HardyQM.zPlus aPrimeMinusMax hardyMaxVec = 0 := by
  simp [HardyQM.jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        HardyQM.zPlus, aPrimeMinusMax, hardyMaxVec]

/-- **Max-Hardy amplitude 3**: `⟨a'_⊥, 0 | ψ_max⟩ = 0`. Symmetric. -/
theorem hardyMaxAmp_A'minus_B :
    HardyQM.jointAmplitude aPrimeMinusMax HardyQM.zPlus hardyMaxVec = 0 := by
  simp [HardyQM.jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        HardyQM.zPlus, aPrimeMinusMax, hardyMaxVec]

/-- **Max-Hardy amplitude 4** (load-bearing): `⟨a', a' | ψ_max⟩ = 0`.

All four terms contribute:
`1·1·1 + 1·√φ·√φ + √φ·1·√φ + √φ·√φ·(−φ²)
   = 1 + φ + φ − φ·φ² = 1 + 2φ − φ³ = 1 + 2φ − (2φ + 1) = 0`,
using `sqrtPhi_sq : √φ · √φ = φ` and `phi_cube : φ³ = 2φ + 1`. -/
theorem hardyMaxAmp_A'_B' :
    HardyQM.jointAmplitude aPrimeMax aPrimeMax hardyMaxVec = 0 := by
  simp [HardyQM.jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two,
        aPrimeMax, hardyMaxVec]
  -- Goal: 1 + sqrtPhi·sqrtPhi + sqrtPhi·sqrtPhi - sqrtPhi·sqrtPhi·phi² = 0
  -- = 1 + 2φ - φ³ = 1 + 2φ - (2φ+1) = 0.
  have hsq : (sqrtPhi : ℂ) * (sqrtPhi : ℂ) = (phi : ℂ) := by
    have hsr : sqrtPhi ^ 2 = phi := sqrtPhi_sq
    have : (sqrtPhi : ℂ) * sqrtPhi = ((sqrtPhi ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, hsr]
  have hcube : (phi : ℂ) ^ 3 = 2 * (phi : ℂ) + 1 := by
    have hpc : phi ^ 3 = 2 * phi + 1 := phi_cube
    have : ((phi : ℂ)) ^ 3 = ((phi ^ 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, hpc]; push_cast; ring
  linear_combination (2 - (phi : ℂ)^2) * hsq - hcube

/-- **QM realises the Hardy constraints at the golden-ratio maximum.** -/
theorem exists_hardy_realisation_max :
    ∃ (ψ : Fin 2 × Fin 2 → ℂ) (a aPrime b bPrime aPrime_perp bPrime_perp : Fin 2 → ℂ),
      HardyQM.jointAmplitude a b ψ ≠ 0 ∧
      HardyQM.jointAmplitude a bPrime_perp ψ = 0 ∧
      HardyQM.jointAmplitude aPrime_perp b ψ = 0 ∧
      HardyQM.jointAmplitude aPrime bPrime ψ = 0 :=
  ⟨hardyMaxVec, HardyQM.zPlus, aPrimeMax, HardyQM.zPlus, aPrimeMax,
   aPrimeMinusMax, aPrimeMinusMax,
   by rw [hardyMaxAmp_AB]; norm_num,
   hardyMaxAmp_A_B'minus,
   hardyMaxAmp_A'minus_B,
   hardyMaxAmp_A'_B'⟩

/-! ### Hardy maximum probability value

The Hardy probability for the golden-ratio state evaluates to the
closed-form maximum `(5√5 − 11)/2 ≈ 9.017%`. Three steps:

1. `normSq_hardyMaxVec`: `‖ψ_max‖² = 5φ + 3` (uses `sqrtPhi_sq`, `phi_sq`).
2. `hardyMax_value`: `1/(5φ + 3) = (5√5 − 11)/2` (rationalisation
   identity, via `(5√5)² = 25·5 = 125` and `(5√5−11)(11+5√5) = 4`).
3. `hardyMax_probability_eq`: combines via `hardyMaxAmp_AB`.
-/

/-- The squared norm of a 2-qubit state vector. -/
noncomputable def normSq (ψ : Fin 2 × Fin 2 → ℂ) : ℝ := ∑ p, ‖ψ p‖ ^ 2

/-- `‖ψ_max‖² = 5φ + 3`. Expands the four-term sum:
`1 + (√φ)² + (√φ)² + (φ²)² = 1 + φ + φ + (3φ + 2) = 5φ + 3`. -/
lemma normSq_hardyMaxVec : normSq hardyMaxVec = 5 * phi + 3 := by
  have hsq : sqrtPhi ^ 2 = phi := sqrtPhi_sq
  have hpsq : phi ^ 2 = phi + 1 := phi_sq
  have hsqrtPhi_nn : 0 ≤ sqrtPhi := Real.sqrt_nonneg _
  have hphisq_nn : 0 ≤ phi ^ 2 := sq_nonneg _
  simp [normSq, hardyMaxVec, Fintype.sum_prod_type, Fin.sum_univ_two,
        Complex.norm_real, abs_of_nonneg hsqrtPhi_nn]
  nlinarith [hsq, hpsq]

/-- The rationalisation identity `1 / (5φ + 3) = (5√5 − 11)/2`.

The proof routes via the difference-of-squares
`(5√5 − 11)(11 + 5√5) = 25·(√5)² − 121 = 125 − 121 = 4` and the
substitution `5φ + 3 = (11 + 5√5)/2`. -/
lemma hardyMax_value :
    1 / (5 * phi + 3) = (5 * Real.sqrt 5 - 11) / 2 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have hsqrt_nn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hne : (5 * phi + 3 : ℝ) ≠ 0 := by
    unfold phi; nlinarith
  rw [div_eq_div_iff hne (by norm_num : (2 : ℝ) ≠ 0)]
  unfold phi
  nlinarith [h5, hsqrt_nn]

/-- **Hardy's maximum probability value**: the QM joint probability
`|⟨0, 0 | ψ_max⟩|² / ‖ψ_max‖²` for the golden-ratio Hardy state
equals the closed-form maximum `(5√5 − 11)/2 ≈ 9.017%`. -/
theorem hardyMax_probability_eq :
    ‖HardyQM.jointAmplitude HardyQM.zPlus HardyQM.zPlus hardyMaxVec‖ ^ 2
      / normSq hardyMaxVec = (5 * Real.sqrt 5 - 11) / 2 := by
  rw [hardyMaxAmp_AB, normSq_hardyMaxVec]
  rw [show (‖(1 : ℂ)‖ ^ 2 : ℝ) = 1 by simp]
  rw [show ((1 : ℝ) / (5 * phi + 3) = (1 : ℝ) / (5 * phi + 3)) from rfl]
  exact hardyMax_value

end HardyQMMax

end Hardy
end Empirical
end CSD
