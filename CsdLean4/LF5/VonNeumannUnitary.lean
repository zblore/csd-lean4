/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# LF5: the von Neumann measurement coupling unitary (LF5-A)

**Category:** 3-Local (the first LF5 layer; opens `CsdLean4/LF5/`, namespace
`CSD.LF5`).

This is **LF5-A** of `specs/lf5-plan.md`: the von Neumann measurement coupling
unitary, the generalized-CNOT / "copy" interaction

```
  eⱼ ⊗ a₀  ↦  eⱼ ⊗ aⱼ        (ground apparatus a₀ = 0)
```

realised as the **adder permutation** `σ(j,k) = (j, j + k)` on `Fin N × Fin N`
(system index × apparatus index, `Fin N`'s `Add` being mod-`N`). At the ground
apparatus state `k = 0` this is `σ(j,0) = (j,j)`: the system index is *copied*
into the apparatus. Building the coupling as a **permutation matrix** makes
unitarity manifest (`vnUnitaryᴴ * vnUnitary = 1`), sidestepping any
extend-a-partial-isometry problem.

## Index convention

The dilated index is `Fin N × Fin N`, matching `LF4/POVMDilation.lean`'s
`blockProj N i : Matrix (Fin N × ι) (Fin N × ι) ℂ` with apparatus `ι = Fin N`:
the first factor is the **system**, the second the **apparatus / pointer**.

## Downstream

LF5-A feeds:
- **LF5-B**: the measurement flow `Φ_vN := projMap vnUnitary` on `ℂℙ^{N·N−1}`
  (`vnUnitary_mem_unitaryGroup` is what the U(N)-action consumes);
- **LF5-C**: the dynamically-realised dilation `V = vnUnitary ∘ (· ⊗ a₀)`, whose
  pullback identity `Vᴴ (blockProj N i) V = |eᵢ⟩⟨eᵢ|` reuses the LF4 POVM volume /
  frequency engine.

`NeZero N` is assumed throughout: it gives `Fin N` its `AddCommGroup` structure,
required for the adder permutation's inverse `(j, m) ↦ (j, m − j)`. Every
downstream system dimension is `≥ 1`, so this costs nothing.

Reference: `specs/lf5-plan.md` (LF5-A).
-/

@[expose] public section

open Matrix

namespace CSD
namespace LF5

variable {N : ℕ} [NeZero N]

/-- The **adder bijection** `(j, k) ↦ (j, j + k)` on `Fin N × Fin N`, with
`Fin N`'s mod-`N` addition. The inverse is `(j, m) ↦ (j, m − j)`. This is the
von Neumann measurement coupling permutation: the system index `j` is unchanged,
the apparatus index is shifted by `j`, so at the ground apparatus `k = 0` the
system index is copied (`(j, 0) ↦ (j, j)`). -/
def vnPerm (N : ℕ) [NeZero N] : Equiv.Perm (Fin N × Fin N) where
  toFun := fun p => (p.1, p.1 + p.2)
  invFun := fun p => (p.1, p.2 - p.1)
  left_inv := by
    rintro ⟨j, k⟩
    simp only [Prod.mk.injEq, true_and]
    rw [add_comm, add_sub_cancel_right]
  right_inv := by
    rintro ⟨j, m⟩
    simp only [Prod.mk.injEq, true_and]
    rw [add_comm, sub_add_cancel]

@[simp]
lemma vnPerm_apply (j k : Fin N) : vnPerm N (j, k) = (j, j + k) := rfl

@[simp]
lemma vnPerm_symm_apply (j m : Fin N) : (vnPerm N).symm (j, m) = (j, m - j) := rfl

/-- **Ground-apparatus copy.** At the apparatus ground state `k = 0` the adder
permutation copies the system index into the apparatus: `σ(j, 0) = (j, j)`. -/
lemma vnPerm_ground (j : Fin N) : vnPerm N (j, 0) = (j, j) := by
  rw [vnPerm_apply, add_zero]

/-- The **von Neumann coupling unitary**: the permutation matrix of the *inverse*
adder permutation `(vnPerm N).symm` on the dilated index `Fin N × Fin N`.
Manifestly unitary (`vnUnitary_unitary`).

The inverse is taken because the permutation matrix realises a basis-index map by
its *symm*: `permMatrix σ *ᵥ e_a = e_{σ.symm a}` (see `vnUnitary_mulVec_single`).
Taking `σ = (vnPerm N).symm` makes the basis action equal `vnPerm N` itself, so
the ground-apparatus column action is the intended copy `e_{(j,0)} ↦ e_{(j,j)}`
(`vnUnitary_mulVec_ground`). -/
noncomputable def vnUnitary (N : ℕ) [NeZero N] :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Equiv.Perm.permMatrix ℂ (vnPerm N).symm

/-- **Entry formula.** `vnUnitary` is the permutation matrix of `(vnPerm N).symm`. -/
lemma vnUnitary_apply :
    vnUnitary N = Equiv.Perm.permMatrix ℂ (vnPerm N).symm := rfl

/-- **Unitarity (manifest).** A permutation matrix `P = permMatrix σ` satisfies
`Pᴴ = permMatrix σ⁻¹`, hence `Pᴴ P = permMatrix σ⁻¹ · permMatrix σ =
permMatrix (σ · σ⁻¹) = permMatrix 1 = 1` (note `permMatrix_mul` is contravariant). -/
theorem vnUnitary_unitary :
    (vnUnitary N)ᴴ * (vnUnitary N) = 1 := by
  rw [vnUnitary, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

/-- **Membership in the unitary group** `U(Fin N × Fin N)`. This is what the
LF5-B U(N)-action / `projMap` consumes. -/
theorem vnUnitary_mem_unitaryGroup :
    vnUnitary N ∈ Matrix.unitaryGroup (Fin N × Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact vnUnitary_unitary

/-- **Action on a computational basis vector.** The permutation matrix
`permMatrix σ` sends `e_a` to `e_{σ.symm a}`; with `σ = (vnPerm N).symm` this is
`e_a ↦ e_{vnPerm N a}`. So `vnUnitary` realises the adder bijection on the
computational basis. -/
lemma vnUnitary_mulVec_single (a : Fin N × Fin N) :
    vnUnitary N *ᵥ (Pi.single a (1 : ℂ)) = Pi.single (vnPerm N a) (1 : ℂ) := by
  rw [vnUnitary, Matrix.permMatrix_mulVec]
  ext x
  simp only [Function.comp_apply, Pi.single_apply]
  exact if_congr (Equiv.symm_apply_eq (vnPerm N)) rfl rfl

/-- **Ground-apparatus copy at the matrix level.** Acting on the basis vector
`e_{(j,0)}` (system `j`, apparatus ground), the coupling produces `e_{(j,j)}`:
the system index has been copied into the apparatus. This is the LF5-C input
`vnUnitary *ᵥ (eⱼ ⊗ a₀) = eⱼ ⊗ aⱼ`. -/
lemma vnUnitary_mulVec_ground (j : Fin N) :
    vnUnitary N *ᵥ (Pi.single (j, 0) (1 : ℂ)) = Pi.single (j, j) (1 : ℂ) := by
  rw [vnUnitary_mulVec_single, vnPerm_ground]

end LF5
end CSD
