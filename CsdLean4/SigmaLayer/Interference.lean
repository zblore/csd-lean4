import CsdLean4.SigmaLayer.CompositeInterface
import CsdLean4.Empirical.QM.Algorithms.HadamardTest

/-!
# SigmaLayer/Interference: quantum interference as a first-class target

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Interference is NOT a postulate and NOT a structure field: it is a consequence of two facts already in the
base, namely that the projective sector is a COMPLEX projective space (P7) and that outcome probabilities
are Born weights (T1/T2). Because amplitudes live in a complex Hilbert space and probabilities are
inner-product moduli, a two-path (superposition) outcome probability carries a phase-dependent cross
term, so it is not the phase-independent classical average of the branch probabilities.

This module records that consequence as a first-class ledger target (T16) and inhabits it by wiring the
existing Hadamard-test result: the ancilla-`0` marginal probability is `(1 + Re⟨ψ, Uψ⟩)/2`, a genuine
two-path interference formula whose value tracks the relative phase of the two branches (constructive at
`Uψ = ψ`, giving `1`; destructive at `Uψ = -ψ`, giving `0`). The same phenomenon appears in the swap
test (`(1 + ‖⟨ψ,φ⟩‖²)/2`) and the Ramsey fringe (`cos²(φ/2)`, Fubini-Study-volume derived); the Hadamard
form is used here because it exposes the phase (the real part of the overlap) directly.

We provide NO new mathematics: `HasBornInterference` is inhabited verbatim by `hadamard_test_prob`.
-/

open scoped ComplexConjugate

namespace CSD.SigmaLayer

/-- **T16: two-path Born interference.** The Born probability of the `|0⟩`-ancilla branch of an equal
superposition of two unit paths `a, b` is `(1 + Re⟨a, b⟩)/2`: it carries the phase-dependent cross term
`Re⟨a, b⟩`, so it deviates from the phase-independent classical value `1/2` unless the paths are
orthogonal. Generic over the paths and the measured probability. -/
def HasBornInterference {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E) (prob : ℝ) : Prop :=
  prob = (1 + (inner ℂ a b).re) / 2

/-- **T16 inhabited by the Hadamard test.** For a linear map `U` with `‖ψ‖ = ‖Uψ‖ = 1`, the Hadamard-test
ancilla-`0` probability exhibits Born interference between the paths `ψ` and `Uψ`: it equals
`(1 + Re⟨ψ, Uψ⟩)/2`. From `hadamard_test_prob`. -/
theorem hadamardTest_hasBornInterference {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (hU : ‖U ψ‖ = 1) :
    HasBornInterference ψ (U ψ)
      (CSD.Empirical.QM.HadamardTest.hadTestProb0 U ψ) :=
  CSD.Empirical.QM.HadamardTest.hadamard_test_prob U ψ hψ hU

end CSD.SigmaLayer
