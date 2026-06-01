import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/QM: No-communication theorem (E3a, marginal form)

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

The no-communication (no-signalling) theorem: a local operation performed by
Alice on her half of a shared bipartite state cannot change any measurement
statistic Bob computes on his half. This is the relativistic-causality guarantee
underlying entanglement — entanglement gives correlations but no faster-than-light
signalling.

We deliver the **marginal form** (E3a), which avoids the reduced-density /
partial-trace machinery (absent from Mathlib): for a bipartite state
`ψ ∈ ℂ^m ⊗ ℂ^n`, any **unitary** Alice-side operation `U` (`Uᴴ U = I`), and **any**
Bob-side operator `Q`,

```
⟨(U ⊗ I) ψ, (I ⊗ Q) (U ⊗ I) ψ⟩ = ⟨ψ, (I ⊗ Q) ψ⟩.
```

The left side is the expectation of Bob's observable `Q` *after* Alice applies
`U`; the right side is the expectation with Alice doing nothing. Taking `Q` a
projector gives Bob's outcome probabilities; taking `Q` Hermitian gives his
expectation values (`bob_expectation_invariant`). Either way Alice's choice of
`U` does not enter.

This is **strictly stronger** than the singlet-specific Bell-marginal
no-signalling already in `Empirical/QM/Bell.lean` (`no_signalling_alice/bob`,
which are about the fixed singlet and specific Pauli settings): it holds for an
*arbitrary* shared state `ψ`, an *arbitrary* unitary Alice operation, and an
*arbitrary* Bob observable.

## Scope (E3a vs E3b)

This is the **amplitude / marginal** form, needing only the Kronecker
mixed-product identity `(A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)`. The **reduced-density**
form (E3b) — "Alice's local CPTP map leaves `Tr_A(ρ)` invariant" — requires a
partial-trace construction not yet in Mathlib, and is deferred to a shared
partial-trace infrastructure tranche (jointly with E2 no-broadcasting). See
`specs/qm-empirical-tests.md` §3bis.1.

## Source

Standard; the relativistic no-signalling property of quantum mechanics
(Ghirardi-Rimini-Weber 1980; Eberhard 1978). Cf. the PR-box / no-signalling
literature (Popescu-Rohrlich 1994).
-/

open Matrix ComplexConjugate
open scoped Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace NoCommunication

variable {m n : ℕ}

/-- Alice's local operation `U ⊗ I` on the bipartite space `ℂ^m ⊗ ℂ^n`
(`Fin m × Fin n`-indexed). -/
noncomputable def aliceOp (U : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Bob's observable `I ⊗ Q` on the bipartite space. -/
noncomputable def bobOp (Q : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Q

/-- **Matrix core.** Conjugating Bob's operator by Alice's unitary leaves it
unchanged: `(U ⊗ I)ᴴ · (I ⊗ Q) · (U ⊗ I) = I ⊗ Q`, because the Alice factor
collapses through `Uᴴ U = I` and the Bob factor through `I·Q·I = Q`. -/
theorem aliceOp_conjugate (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) :
    (aliceOp U)ᴴ * (bobOp Q * aliceOp (n := n) U) = bobOp (m := m) Q := by
  unfold aliceOp bobOp
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, one_mul, hU]

/-- **No-communication theorem (marginal form).** For a bipartite state `ψ`, a
unitary Alice-side operation `U`, and any Bob-side operator `Q`, Bob's
expectation `⟨φ, (I ⊗ Q) φ⟩` is the same whether or not Alice applies `U`
(`φ = (U ⊗ I) ψ` vs `φ = ψ`). Alice cannot signal to Bob.

**Proof.** Move `U ⊗ I` across the inner product as an adjoint
(`adjoint_inner_right` + `toEuclideanLin_conjTranspose_eq_adjoint`), compose the
three matrices into one (`toLpLin_mul_same`), and collapse the conjugate by
`aliceOp_conjugate`. -/
theorem no_communication
    (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    inner ℂ (Matrix.toEuclideanLin (aliceOp U) ψ)
        (Matrix.toEuclideanLin (bobOp Q) (Matrix.toEuclideanLin (aliceOp U) ψ))
      = inner ℂ ψ (Matrix.toEuclideanLin (bobOp Q) ψ) := by
  rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (aliceOp U))]
  rw [show (Matrix.toEuclideanLin (aliceOp U)).adjoint
          = Matrix.toEuclideanLin (aliceOp U)ᴴ from
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (aliceOp U)).symm]
  rw [show Matrix.toEuclideanLin (aliceOp U)ᴴ
            (Matrix.toEuclideanLin (bobOp Q) (Matrix.toEuclideanLin (aliceOp U) ψ))
          = Matrix.toEuclideanLin ((aliceOp U)ᴴ * (bobOp Q * aliceOp U)) ψ from by
        rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same]; rfl]
  rw [aliceOp_conjugate U Q hU]

/-- **Bob's expectation/probability is invariant.** The real-valued form of
`no_communication`: Bob's measured expectation of `Q` (and, for `Q` a projector,
his outcome probability) does not depend on Alice's local unitary. -/
theorem bob_expectation_invariant
    (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    (inner ℂ (Matrix.toEuclideanLin (aliceOp U) ψ)
        (Matrix.toEuclideanLin (bobOp Q) (Matrix.toEuclideanLin (aliceOp U) ψ))).re
      = (inner ℂ ψ (Matrix.toEuclideanLin (bobOp Q) ψ)).re := by
  rw [no_communication U Q hU ψ]

end NoCommunication
end QM
end Empirical
end CSD
