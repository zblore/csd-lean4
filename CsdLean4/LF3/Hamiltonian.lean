import CsdLean4.LF3.Setup

/-!
# LF3 Hamiltonian: tensor-factor readout algebra and measurement unitary

**Category:** 3-Local (LF3 abstract structural interfaces for the impulsive-readout measurement model).

Paper §3 / §9.5. Abstract structural interfaces for the impulsive-readout
measurement model:

- `TensorFactorReadoutAlgebra` carries `hA`, `hB` and their commutation as a
  field. The local Hamiltonians are self-adjoint continuous linear maps.
- `MeasurementUnitary` carries a `LinearIsometryEquiv` triple `(u, uA, uB)`
  for the full and per-wing measurement unitaries (unitarity in the type),
  the factorisation law in pointwise form, and the eigenstate-action field
  encoding the impulsive-readout idealisation.

Per spec §9.5, the operator exponential is not constructed in v1.00; the
unitaries enter as structural data.
-/

open scoped ComplexConjugate

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]

/-- Abstract tensor-factor readout algebra on `H_SA`. `hA` acts on the A
    factor, `hB` on the B factor; commutation is recorded as a field per
    spec §9.11.

    Self-adjointness is stated via the inner-product equation directly,
    matching the convention used in `BinaryPointerProjectors` (avoids the
    `Star` typeclass synthesis on `H_SA →L[ℂ] H_SA`). -/
structure TensorFactorReadoutAlgebra (S : SystemApparatusSetup K_A K_B H_SA) where
  /-- Local readout Hamiltonian on the A wing. -/
  hA      : H_SA →L[ℂ] H_SA
  /-- Local readout Hamiltonian on the B wing. -/
  hB      : H_SA →L[ℂ] H_SA
  /-- `hA` is self-adjoint with respect to the inner product. -/
  hA_selfAdjoint : ∀ x y, inner ℂ (hA x) y = inner ℂ x (hA y)
  /-- `hB` is self-adjoint with respect to the inner product. -/
  hB_selfAdjoint : ∀ x y, inner ℂ (hB x) y = inner ℂ x (hB y)
  /-- The two readout Hamiltonians commute. -/
  commute : hA ∘L hB = hB ∘L hA

/-- Sum of the two local readout Hamiltonians. -/
noncomputable def hTotal {S : SystemApparatusSetup K_A K_B H_SA}
    (R : TensorFactorReadoutAlgebra S) : H_SA →L[ℂ] H_SA :=
  R.hA + R.hB

/-- `hA` and `hB` commute (field re-export, paper §3.5). -/
theorem hA_commute_hB {S : SystemApparatusSetup K_A K_B H_SA}
    (R : TensorFactorReadoutAlgebra S) :
    R.hA ∘L R.hB = R.hB ∘L R.hA :=
  R.commute

/-- A measurement unitary, its single-wing factors, the factorisation law,
    and the action on joint spin/pointer eigenstates.

    **D4 / G6 disclosure.** Per spec §9.5: `u` / `uA` / `uB` are **not**
    derived from `exp(-iHt)` in v1.00. They are supplied as a
    `LinearIsometryEquiv` triple (unitarity is part of the type) satisfying
    the factorisation and eigenstate-action laws (paper §3.6–§3.7) as
    structural fields rather than as theorems. Together with the abstract
    `ProjectorAlgebra` (`LF3/Projectors/Core.lean`), this carries the
    composite-tensor-structure debt D4 / G6 in Lean form.

    **v2 derivation status, partial discharge landed.** The factorisation
    field `factorises : ∀ x, u x = uA (uB x)` is now derivable via
    `MeasurementUnitary.ofUnitaryTensorEmbedding` in
    `LF3/Projectors/TensorModel.lean`. The constructor takes a
    `UnitaryTensorEmbedding K_A K_B H_SA` (per-wing unitary lifts with
    commuting images), per-wing unitaries `vA`, `vB`, the joint-eigenstate
    / pointer-translation data, and the action proof; it defines
    `u := (liftB_unitary vB).trans (liftA_unitary vA)` and discharges
    `factorises` by `rfl`. The eigenstate-action field `action`, encoding
    the impulsive-readout idealisation, requires `exp(-iHt)` machinery
    (operator exponential, Stone on bounded self-adjoint operators); spec
    §9.5 explicitly carves this out of v1.00 and LF4 or later is the
    natural home, gated on the operator-exponential pickup. The abstract
    `MeasurementUnitary` structure remains available for callers without a
    tensor model. -/
structure MeasurementUnitary (S : SystemApparatusSetup K_A K_B H_SA) where
  /-- The full measurement unitary on `H_SA`. -/
  u          : H_SA ≃ₗᵢ[ℂ] H_SA
  /-- The A-wing measurement unitary. -/
  uA         : H_SA ≃ₗᵢ[ℂ] H_SA
  /-- The B-wing measurement unitary. -/
  uB         : H_SA ≃ₗᵢ[ℂ] H_SA
  /-- Factorisation law in function-application form: `u` acts as `uA ∘ uB`
      pointwise. (Equivalent to `u = uB.trans uA`; the pointwise spelling is
      chosen because every downstream consumer applies `u` to a specific
      vector.) -/
  factorises : ∀ x, u x = uA (uB x)
  /-- Abstract joint spin / pointer eigenstate injection
      `|s_a, t_b⟩ ⊗ |φ_A⟩ ⊗ |φ_B⟩ ∈ H_SA`. -/
  jointEig   : Sign × Sign → K_A → K_B → H_SA
  /-- The A-wing pointer translation by the A-wing unitary, conditional on
      the spin label `s`. -/
  ptrTransA  : Sign → K_A → K_A
  /-- The B-wing pointer translation by the B-wing unitary, conditional on
      the spin label `t`. -/
  ptrTransB  : Sign → K_B → K_B
  /-- Action of `u` on a joint spin / pointer eigenstate. Each wing's
      unitary translates only its own pointer factor; spin labels are
      preserved. Encodes the impulsive-readout idealisation (paper §3.2). -/
  action     : ∀ s t φA φB,
                 u (jointEig (s, t) φA φB)
                   = jointEig (s, t) (ptrTransA s φA) (ptrTransB t φB)

/-- The total readout Hamiltonian is self-adjoint (paper §3.4). -/
theorem hTotal_isSelfAdjoint {S : SystemApparatusSetup K_A K_B H_SA}
    (R : TensorFactorReadoutAlgebra S) :
    ∀ x y, inner ℂ (hTotal R x) y = inner ℂ x (hTotal R y) := by
  intro x y
  unfold hTotal
  simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  rw [R.hA_selfAdjoint, R.hB_selfAdjoint]

/-- Factorisation of the measurement unitary (paper §3.6). Field re-export
    of `MeasurementUnitary.factorises`, applied at a specific vector. -/
theorem uMeasure_factorises {S : SystemApparatusSetup K_A K_B H_SA}
    (M : MeasurementUnitary S) (x : H_SA) :
    M.u x = M.uA (M.uB x) :=
  M.factorises x

/-- Action of the measurement unitary on a joint spin / pointer eigenstate
    (paper §3.7). Field re-export of `MeasurementUnitary.action`. -/
theorem uMeasure_on_joint_eigenstate {S : SystemApparatusSetup K_A K_B H_SA}
    (M : MeasurementUnitary S) (s t : Sign) (φA : K_A) (φB : K_B) :
    M.u (M.jointEig (s, t) φA φB)
      = M.jointEig (s, t) (M.ptrTransA s φA) (M.ptrTransB t φB) :=
  M.action s t φA φB

end LF3
end CSD
