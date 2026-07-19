/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CsdLean4.Empirical.CSD.Gates.TwoQubitDischarge
import CsdLean4.Empirical.CSD.Gates.BellPrep

/-!
# Empirical/CSD/Gates: §13.2 discharge for Bell-state preparation (H⊗I, CNOT)

**Category:** 3-Local (CSD-side concrete discharge of LF4-§13.2, composite tier).

Completes the gate `*_realisable_for` discharge (`PLACEHOLDERS.md §1`, the ninth and last
Prop). `bell_prep_realisable_for` asks for two `CSDUnitaryBundle`s realising `H ⊗ I` and
`CNOT`; both are discharged on `cpSectorData p₀` (`p₀ : CPN 4`). `qmCNOT ∈ U(4)` is reused
from `TwoQubitDischarge`; `qmH_tensor_I` (`= H ⊗ I`, real Hermitian, involutive) is shown
unitary here (`qmH_tensor_I_mem_unitaryGroup`). Each `U_isometry` is derived from `U(4)`
membership via `inner_toEuclideanLin_unitary`.

## Honest scope

As in the earlier tiers: **modulo A5**; the bundle type carries `U` + `U_isometry` + a
`Context`, not a Σ-flow (`PLACEHOLDERS.md §7`), so this discharges the Prop *as typed*, not
the Σ-flow-lift prose (open **D1** gap). With this file **all nine gate realisability Props
are discharged** on the concrete instance.

References: `Gates/{SingleQubit,TwoQubit,MultiQubit}Discharge.lean`,
`Empirical/QM/Gates/BellPrep.lean` (`qmH_tensor_I`), `PLACEHOLDERS.md` §1/§7.
-/

open Matrix
open CSD.Empirical.QM.Gates
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- `H ⊗ I` is Hermitian (real symmetric): `star (H⊗I) = H⊗I`. -/
theorem qmH_tensor_I_hermitian : star qmH_tensor_I = qmH_tensor_I := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmH_tensor_I, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.conj_ofReal]

/-- `H ⊗ I` is involutive: `(H⊗I)² = 1`. -/
theorem qmH_tensor_I_mul_self : qmH_tensor_I * qmH_tensor_I = 1 := by
  unfold qmH_tensor_I
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) from by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply] <;> ring

/-- `qmH_tensor_I ∈ U(4)` (Hermitian involution: `(H⊗I) · star(H⊗I) = (H⊗I)² = 1`). -/
theorem qmH_tensor_I_mem_unitaryGroup : qmH_tensor_I ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, qmH_tensor_I_hermitian, qmH_tensor_I_mul_self]

/-- **§13.2 discharge (Bell-state preparation).** `bell_prep_realisable_for (cpSectorData p₀)`
holds: bundles realising `H ⊗ I` and `CNOT`, each `U_isometry` derived from `U(4)` membership.
Modulo A5. The ninth and last gate realisability Prop. -/
theorem bell_prep_realisable_cpSector (p₀ : CPN 4) :
    CSD.Empirical.CSDBridge.Gates.BellPrep.bell_prep_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmH_tensor_I)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmH_tensor_I, qmH_tensor_I_mem_unitaryGroup⟩ x y },
   { toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmCNOT)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmCNOT, qmCNOT_mem_unitaryGroup⟩ x y },
   fun _ => rfl, fun _ => rfl⟩

end CSD.LF4
