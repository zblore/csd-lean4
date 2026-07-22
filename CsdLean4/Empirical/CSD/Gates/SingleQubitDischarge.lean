/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Gates.WignerDischarge
import CsdLean4.Empirical.CSD.Gates.SingleQubit

/-!
# Empirical/CSD/Gates: §13.2 discharge for the single-qubit gates (H, S, T)

**Category:** 3-Local (CSD-side concrete discharge of the LF4-§13.2 gate-realisability
obligation).

The three `*_realisable_for` Props in `Empirical/CSD/Gates/SingleQubit.lean` were
claim-shaped placeholders (`PLACEHOLDERS.md §1`: "no concrete `D` is constructed for
which any holds"). This module DISCHARGES them on the concrete Kähler sector
`cpSectorData p₀`: each gate's action is exhibited as a genuine `CSDUnitaryBundle`
whose `U` IS the gate's Hilbert action and whose `U_isometry` is a THEOREM, derived from
the gate lying in `U(2)` — the sector-symmetry membership — via
`Projectivization.inner_toEuclideanLin_unitary` (the same content `cpSectorActionBundle`
carries for a general sector element).

## Honest scope

* **Modulo A5.** `cpSectorData` is the *posited* Kähler sector; this discharges the Props
  *given* that sector, exactly as `WignerDischarge`/`cpSectorActionBundle` do. It does not
  derive the sector.
* **What the type carries.** Per `PLACEHOLDERS.md §7` the `CSDUnitaryBundle` type carries
  `U` + `U_isometry` + a `Context D`, NOT a Σ-flow / π-equivariance datum. So these theorems
  establish the Prop *as typed* (a `Context` plus a Hilbert isometry equal to the gate);
  the stronger prose reading (the gate as the projective lift of a deterministic Σ-flow) is
  the open **D1** gap and is NOT claimed here.
* **`U_isometry` is derived, not posited.** It comes from `qm{H,S,T} ∈ U(2)`
  (`inner_toEuclideanLin_unitary`), i.e. from the gate being a Fubini–Study isometry — the
  A5 sector datum — not from `μL`-measure-preservation (measure ≠ metric; see
  `WignerDischarge`).

Net effect: the three single-qubit gate placeholders (`PLACEHOLDERS.md §1`) become proved
theorems on the concrete instance. The two-qubit / multi-qubit / Bell-prep gates follow the
same pattern (each gate matrix is unitary) and are the mechanical continuation.

References: `Empirical/CSD/Gates/WignerDischarge.lean`, `Empirical/CSD/Gates/SingleQubit.lean`,
`Empirical/QM/Gates/SingleQubit.lean` (`qmH`, `qmS`, `qmT`), `specs/LF4-todo.md` §13.2,
`BRIDGE-OBLIGATIONS.md` §2.6, `PLACEHOLDERS.md` §1/§7.
-/

open Matrix
open CSD.Empirical.QM.Gates
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- `qmH ∈ U(2)`: Hadamard is Hermitian (real symmetric) and involutive, so
`qmH * star qmH = qmH * qmH = 1`. -/
theorem qmH_mem_unitaryGroup : qmH ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star qmH = qmH := by
    rw [Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qmH, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  rw [hstar, qmH_mul_self]

/-- `qmS ∈ U(2)`: `S = diag(1, i)`, `S · Sᴴ = diag(1, i·(-i)) = 1`. -/
theorem qmS_mem_unitaryGroup : qmS ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.conj_I, Complex.I_mul_I]

/-- `qmT ∈ U(2)`: `T = diag(1, e^{iπ/4})`, `T · Tᴴ = diag(1, e^{iπ/4}·e^{-iπ/4}) = 1`. -/
theorem qmT_mem_unitaryGroup : qmT ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hw : (starRingEnd ℂ) (Complex.I * (Real.pi / 4)) = -(Complex.I * (Real.pi / 4)) := by
    simp only [map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal, map_ofNat, neg_mul]
  have hce : (starRingEnd ℂ) (Complex.exp (Complex.I * (Real.pi / 4)))
      = Complex.exp (-(Complex.I * (Real.pi / 4))) := by
    rw [← Complex.exp_conj, hw]
  have hmod : Complex.exp (Complex.I * (Real.pi / 4))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (Real.pi / 4))) = 1 := by
    rw [hce, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, hmod]

/-- **§13.2 discharge (Hadamard).** `hadamard_realisable_for (cpSectorData p₀)` holds:
the bundle's `U` is the Hadamard action, `U_isometry` derived from `qmH ∈ U(2)`. -/
theorem hadamard_realisable_cpSector (p₀ : CPN 2) :
    CSD.Empirical.CSDBridge.Gates.SingleQubit.hadamard_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmH)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmH, qmH_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

/-- **§13.2 discharge (Phase S).** `phaseS_realisable_for (cpSectorData p₀)` holds. -/
theorem phaseS_realisable_cpSector (p₀ : CPN 2) :
    CSD.Empirical.CSDBridge.Gates.SingleQubit.phaseS_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmS)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmS, qmS_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

/-- **§13.2 discharge (Phase T).** `phaseT_realisable_for (cpSectorData p₀)` holds. -/
theorem phaseT_realisable_cpSector (p₀ : CPN 2) :
    CSD.Empirical.CSDBridge.Gates.SingleQubit.phaseT_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmT)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmT, qmT_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

end CSD.LF4
