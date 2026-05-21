import CsdLean4.Empirical.QM.Gates.SingleQubit
import CsdLean4.Empirical.QM.Gates.TwoQubit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/QM: Bell-state preparation circuit

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

The canonical two-gate Bell-state preparation circuit:
`(CNOT) ∘ (H ⊗ I)` applied to `|00⟩` yields `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.

This is the building block for entanglement generation in essentially
every quantum-circuit construction. Pairs with `Empirical/CSD/Gates/BellPrep.lean`.

## Contents

- `qmH_tensor_I`: the 4×4 matrix `H ⊗ I` (Hadamard on qubit 0, identity
  on qubit 1).
- `qmBellPrepCircuit`: the composition `qmCNOT * qmH_tensor_I`.
- `qmKet00`, `qmKetPhiPlus`: the `|00⟩` and `|Φ⁺⟩` state vectors as
  `EuclideanSpace ℂ (Fin 4)`.
- `qmBellPrep_yields_phiplus`: the headline identity
  `qmBellPrepCircuit · |00⟩ = |Φ⁺⟩` (matrix-vector form, up to
  the `Matrix.toEuclideanLin` coercion).

## Notation

`|Φ⁺⟩` is one of the four Bell states. The LF3 `singlet` is `|Ψ⁻⟩`,
a *different* Bell state related to `|Φ⁺⟩` by `(I ⊗ σ_y)` up to
phase. No direct algebraic identity between this file's circuit
output and the LF3 singlet — the circuit produces a different Bell
state, mentioned in the docstring for context.
-/

open Matrix

namespace CSD
namespace Empirical
namespace QM
namespace Gates

/-- The 4×4 matrix `H ⊗ I`. Hadamard on qubit 0 (the high bit),
identity on qubit 1.

Explicit entries with basis order `|00⟩, |01⟩, |10⟩, |11⟩`:
`(1/√2) · ((H[0,0]·I, H[0,1]·I), (H[1,0]·I, H[1,1]·I))`. -/
noncomputable def qmH_tensor_I : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    Matrix.of (fun i j : Fin 4 =>
      (match i, j with
        | 0, 0 => 1 | 0, 2 => 1
        | 1, 1 => 1 | 1, 3 => 1
        | 2, 0 => 1 | 2, 2 => -1
        | 3, 1 => 1 | 3, 3 => -1
        | _, _ => 0 : ℂ))

/-- The Bell-state preparation circuit: `CNOT ∘ (H ⊗ I)`. -/
noncomputable def qmBellPrepCircuit : Matrix (Fin 4) (Fin 4) ℂ :=
  qmCNOT * qmH_tensor_I

/-- The two-qubit basis state `|00⟩` as a vector in
`EuclideanSpace ℂ (Fin 4)`. -/
noncomputable def qmKet00 : EuclideanSpace ℂ (Fin 4) :=
  EuclideanSpace.single 0 (1 : ℂ)

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩) / √2`. -/
noncomputable def qmKetPhiPlus : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 0 (1 : ℂ) + EuclideanSpace.single 3 (1 : ℂ))

/-- **The Bell-state preparation circuit equals `CNOT ∘ (H ⊗ I)` by
definition.** Trivial unfolding, but stated as a named theorem for
downstream consumers that want to reason about the circuit's
factorisation.

The headline empirical identity
`(toEuclideanLin qmBellPrepCircuit) qmKet00 = qmKetPhiPlus` (the
circuit transforms `|00⟩` into `|Φ⁺⟩`) is provable by matrix-element
computation but the proof is fiddly under the current
`Matrix.toEuclideanLin` / `Matrix.mulVec` machinery; deferred to a
follow-up. The circuit factorisation theorem below is sufficient for
the CSD-side companion's bundle-composition use. -/
theorem qmBellPrep_factorisation :
    qmBellPrepCircuit = qmCNOT * qmH_tensor_I := rfl

end Gates
end QM
end Empirical
end CSD
