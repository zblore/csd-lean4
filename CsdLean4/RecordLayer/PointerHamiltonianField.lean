/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerCoupling
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.HamiltonianVectorField
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# SigmaLayer/PointerHamiltonianField: A4's arrow on the witness's own generator

**Category:** dynamical measurement — `specs/BACKLOG.md` **A4**, the formalisable
fragment instantiated on the smooth pointer witness.

## What this is

`HamiltonianVectorField.lean` proves `X_H = ω⁻¹ dH` at the linear level: the `ω`-dual of a
quadratic energy's differential is the Schrödinger vector field `-(i • A x)`. This module
feeds it the smooth witness's **actual generator**: the fixed-weight coupling `couplingH w`
is Hermitian (`couplingH_isHermitian`), so as an operator on the pointer model space it is
symmetric, and

★★ `coupling_hamiltonian_duality`: the Schrödinger vector field `-(i • H(w)ψ)` of the
pointer stroke pairs against the Fubini–Study fundamental form to give **exactly the
differential of the coupling energy** `½⟨ψ, H(w)ψ⟩` — the stroke's generator IS the
Hamiltonian vector field of its energy observable, `X_𝓗 = ω⁻¹d𝓗` with no inverse formed.

Together with `rampedU_schrodinger` (the stroke solves the Schrödinger ODE for this very
generator, `PointerGeneration.lean`) and `schrodinger_flow_kahler_symplectomorphism` (the
flow *preserves* `ω`, KG-2's invariance half), the fixed-weight loop is closed at the
formalisable level: the energy generates the field (here), the field generates the flow
(`rampedU_schrodinger`), the flow preserves the form (invariance half).

## ⚠️ Honest scope

**Fixed weights, flat model.** This is the fibrewise statement — `w` is held fixed, the
model space is the linear `ℂ^{K+1}`, and `ω` is the pointwise fundamental form. The
**joint-arena manifold** statement — `𝓗(x,q) = Σⱼ wⱼ(x)hⱼ(q)` as a scalar on the product
manifold, `X_𝓗` on the quotient, weight conservation along the true joint flow — remains
the §2a boundary (Mathlib has no manifold symplectic API; flat-space `extDeriv` landed
upstream but manifold forms are explicitly TODO there). The chart-level Poisson half of
that story is A3 (`ChartBracket.lean`); the measure-level transport is A1
(`JointFlowTransfer.lean`); this module is the third fragment, and the three together are
what the corpus can honestly say about A4 today.

## References

`specs/BACKLOG.md` A4, A3, A1; `Mathlib/Analysis/InnerProductSpace/`
`HamiltonianVectorField.lean` (`quadraticEnergy_hamiltonian_duality`, the linear-level
arrow); `RecordLayer/PointerCoupling.lean` (`couplingH`, `couplingH_isHermitian`);
`RecordLayer/PointerGeneration.lean` (`rampedU_schrodinger` — the same generator's ODE);
`LF4/SchrodingerKahlerInvariance.lean` (the invariance half);
`specs/reconstruction-status.md` §2a.
-/

@[expose] public section

namespace CSD.RecordLayer

open Kahler

variable {K : ℕ}

/-- The fixed-weight coupling as a continuous linear operator on the pointer model space. -/
noncomputable def couplingCLM (w : Fin K → ℝ) :
    EuclideanSpace ℂ (Fin (K + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (K + 1)) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (couplingH w))

/-- The coupling operator is symmetric — Hermiticity of `couplingH`, transported through
`toEuclideanLin`. -/
theorem couplingCLM_symmetric (w : Fin K → ℝ) (u v : EuclideanSpace ℂ (Fin (K + 1))) :
    inner ℂ (couplingCLM w u) v = inner ℂ u (couplingCLM w v) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr (couplingH_isHermitian w)) u v

/-- **The coupling energy**: the quantum expectation value `½⟨ψ, H(w)ψ⟩` of the
fixed-weight coupling — the observable whose Hamiltonian flow is the pointer stroke. -/
noncomputable def couplingEnergy (w : Fin K → ℝ) : EuclideanSpace ℂ (Fin (K + 1)) → ℝ :=
  quadraticEnergy (couplingCLM w)

/-- ★★ **A4's arrow on the witness's generator** (fixed weights, linear level): the
Schrödinger vector field `-(i • H(w)ψ)` of the pointer stroke is the Hamiltonian vector
field of the coupling energy — its `ω`-pairing against every direction is exactly the
energy's differential, `ι_{X_𝓗} ω = d𝓗`. The joint-arena manifold form of this statement
is the §2a boundary; see the module docstring. -/
theorem coupling_hamiltonian_duality (w : Fin K → ℝ)
    (ψ v : EuclideanSpace ℂ (Fin (K + 1))) :
    fundamentalForm (-(Complex.I • couplingCLM w ψ)) v
      = fderiv ℝ (couplingEnergy w) ψ v :=
  quadraticEnergy_hamiltonian_duality (couplingCLM w) (couplingCLM_symmetric w) ψ v

end CSD.RecordLayer
