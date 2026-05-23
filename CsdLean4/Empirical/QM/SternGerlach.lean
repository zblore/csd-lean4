import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Empirical: Stern-Gerlach Born probabilities (spin-1/2)

**Category:** 3-Local. Foundational Born-probability example for a
single spin-1/2 system; QM-generic, no CSD ontology;
promotion-ready to 2-Framework on demand.

## What this file proves

The four canonical Born identities for a spin-1/2 system prepared in
the +1 eigenstate of `Z` (`|+_z⟩ = |0⟩`) and measured in either the
`Z` or `X` basis:

```
P(+_z | +_z) = 1          P(+_x | +_z) = 1/2
P(-_z | +_z) = 0          P(-_x | +_z) = 1/2
```

Plus the two **basis completeness** identities: probabilities sum to 1
across the outcomes of any single basis (this is the spectral
decomposition of unity for a complete projective measurement).

## Why Stern-Gerlach matters

The Stern-Gerlach experiment (Stern, Gerlach 1922) was the first
direct measurement of spatial quantisation of angular momentum.
A beam of silver atoms passed through an inhomogeneous magnetic field
splits into exactly two discrete beams — not a continuous distribution
— demonstrating that the projection of spin angular momentum along
any axis takes only two values, `±ℏ/2`.

The Born identities here are the QM-side predictions for the
**relative populations** observed in a sequential SG experiment:
prepare along `+z`, measure along `z` (one beam, all `+`); prepare
along `+z`, measure along `x` (two equal beams, 50/50). These are the
foundational tests of QM's probabilistic structure.

## Experimental verification

- Stern, Gerlach 1922: *Z. Phys.* **9**, 349 (original silver-atom beam).
- Phipps, Taylor 1927: *Phys. Rev.* **29**, 309 (hydrogen confirmation).
- Sakurai 1985 / Modern QM textbooks: SG as the canonical pedagogical
  illustration of QM measurement and basis-change.

## Distinction from other empirical content

- **Bell.lean / CHSH:** statistical inequalities for 2-party correlations.
- **GHZ.lean / Mermin-Peres:** algebraic LHV / contextuality.
- **Hardy.lean:** algebraic LHV for 2-party (with QM realisation).
- **Stern-Gerlach (this file):** **foundational single-particle Born**
  probabilities. The most basic QM prediction. No nonlocality, no
  contextuality — just `|⟨state|prep⟩|²` for a 2-dim system.

## Coding convention

Spin states are stored unnormalised as `Fin 2 → ℂ` (consistent with
`Hardy.lean`'s convention). `bornProb` divides through by the
norm-squared product, so any consistent (un)normalisation gives the
same Born probability.
-/

namespace CSD
namespace Empirical
namespace SternGerlach

open Finset

/-! ### Spin states (unnormalised) -/

/-- `|+_z⟩ = |0⟩`: the `+1` eigenstate of `σ_z`. -/
def zPlus : Fin 2 → ℂ := ![1, 0]

/-- `|−_z⟩ = |1⟩`: the `−1` eigenstate of `σ_z`. -/
def zMinus : Fin 2 → ℂ := ![0, 1]

/-- `|+_x⟩ ∝ |0⟩ + |1⟩` (unnormalised): the `+1` eigenstate of `σ_x`. -/
def xPlus : Fin 2 → ℂ := ![1, 1]

/-- `|−_x⟩ ∝ |0⟩ − |1⟩` (unnormalised): the `−1` eigenstate of `σ_x`. -/
def xMinus : Fin 2 → ℂ := ![1, -1]

/-! ### Inner products, norms, and Born probability -/

/-- The Hermitian inner product `⟨a|b⟩ = ∑ star(a i) · b i`. -/
noncomputable def innerProd (a b : Fin 2 → ℂ) : ℂ := ∑ i, star (a i) * b i

/-- The squared norm `‖a‖² = ∑ ‖a i‖²`, returned as a real number. -/
noncomputable def normSq (a : Fin 2 → ℂ) : ℝ := ∑ i, ‖a i‖ ^ 2

/-- The Born probability for measurement outcome `state` (given as
its `+1` eigenstate) after preparation `prep`:
`P(state | prep) = |⟨state|prep⟩|² / (‖state‖² · ‖prep‖²)`. The
double normalisation makes the result invariant under independent
scaling of `state` and `prep`. -/
noncomputable def bornProb (state prep : Fin 2 → ℂ) : ℝ :=
  ‖innerProd state prep‖ ^ 2 / (normSq state * normSq prep)

/-! ### Auxiliary norm-squared values -/

@[simp] lemma normSq_zPlus : normSq zPlus = 1 := by
  simp [normSq, zPlus, Fin.sum_univ_two]

@[simp] lemma normSq_zMinus : normSq zMinus = 1 := by
  simp [normSq, zMinus, Fin.sum_univ_two]

@[simp] lemma normSq_xPlus : normSq xPlus = 2 := by
  simp [normSq, xPlus, Fin.sum_univ_two]; norm_num

@[simp] lemma normSq_xMinus : normSq xMinus = 2 := by
  simp [normSq, xMinus, Fin.sum_univ_two]; norm_num

/-! ### The four Born identities -/

/-- **Born `P(+_z | +_z) = 1`** (perfect correlation: preparing
along `+z` and measuring along `z` always yields `+1`). -/
theorem born_zPlus_zPlus : bornProb zPlus zPlus = 1 := by
  simp [bornProb, innerProd, normSq, zPlus, Fin.sum_univ_two]

/-- **Born `P(−_z | +_z) = 0`** (perfect anti-correlation: preparing
along `+z` and measuring `−_z` outcome has zero probability). -/
theorem born_zMinus_zPlus : bornProb zMinus zPlus = 0 := by
  simp [bornProb, innerProd, normSq, zMinus, zPlus, Fin.sum_univ_two]

/-- **Born `P(+_x | +_z) = 1/2`** (the canonical 50/50 split: a spin
prepared along `+z` measured along `x` has equal probability of
`+x` and `−x` outcomes). -/
theorem born_xPlus_zPlus : bornProb xPlus zPlus = 1 / 2 := by
  simp [bornProb, innerProd, normSq, xPlus, zPlus, Fin.sum_univ_two]
  norm_num

/-- **Born `P(−_x | +_z) = 1/2`** (the other half of the SG x-axis split). -/
theorem born_xMinus_zPlus : bornProb xMinus zPlus = 1 / 2 := by
  simp [bornProb, innerProd, normSq, xMinus, zPlus, Fin.sum_univ_two]
  norm_num

/-! ### Basis-completeness theorems

For any complete projective measurement, the Born probabilities sum
to 1 across all outcomes. These two theorems verify this for the
`Z` and `X` bases respectively, with preparation along `+z`. -/

/-- **Z-basis completeness** (preparation `+z`): the two `Z`-outcome
probabilities sum to 1. -/
theorem born_z_basis_complete :
    bornProb zPlus zPlus + bornProb zMinus zPlus = 1 := by
  rw [born_zPlus_zPlus, born_zMinus_zPlus]; norm_num

/-- **X-basis completeness** (preparation `+z`): the two `X`-outcome
probabilities sum to 1. -/
theorem born_x_basis_complete :
    bornProb xPlus zPlus + bornProb xMinus zPlus = 1 := by
  rw [born_xPlus_zPlus, born_xMinus_zPlus]; norm_num

end SternGerlach
end Empirical
end CSD
