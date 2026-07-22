/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Gates.WignerDischarge
public import CsdLean4.Empirical.CSD.Gates.TwoQubit

/-!
# Empirical/CSD/Gates: §13.2 discharge for the two-qubit gates (CNOT, SWAP, CZ)

**Category:** 3-Local (CSD-side concrete discharge of the LF4-§13.2 gate-realisability
obligation, two-qubit tier).

Companion to `Gates/SingleQubitDischarge.lean`. The three two-qubit gate
`*_realisable_for` Props (`Empirical/CSD/Gates/TwoQubit.lean`) were claim-shaped
placeholders (`PLACEHOLDERS.md §1`). This module DISCHARGES them on the concrete Kähler
sector `cpSectorData p₀` (`p₀ : CPN 4`): each gate's action is a genuine `CSDUnitaryBundle`
whose `U` IS the gate's Hilbert action and whose `U_isometry` is a THEOREM, derived from the
gate lying in `U(4)` (`inner_toEuclideanLin_unitary`). CNOT, SWAP, CZ are real Hermitian
permutation/diagonal involutions, so `Gᴴ * G = 1` (`qmG*_unitary`) gives membership directly.

## Honest scope

Identical to the single-qubit tier: **modulo A5** (the sector is posited), and per
`PLACEHOLDERS.md §7` the `CSDUnitaryBundle` type carries `U` + `U_isometry` + a `Context`,
not a Σ-flow — so these theorems establish the Prop *as typed*, not the stronger Σ-flow-lift
prose (the open **D1** gap). `U_isometry` is derived from `qm{CNOT,SWAP,CZ} ∈ U(4)` — the
sector-symmetry (Fubini–Study isometry) membership — not from `μL`-measure-preservation.

References: `Gates/SingleQubitDischarge.lean`, `Empirical/CSD/Gates/TwoQubit.lean`,
`Empirical/QM/Gates/TwoQubit.lean` (`qmCNOT`, `qmSWAP`, `qmCZ`, `qmG*_unitary`),
`specs/LF4-todo.md` §13.2, `PLACEHOLDERS.md` §1/§7.
-/

@[expose] public section

open Matrix
open CSD.Empirical.QM.Gates
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- `qmCNOT ∈ U(4)`: `CNOTᴴ * CNOT = 1` (Hermitian involution). -/
theorem qmCNOT_mem_unitaryGroup : qmCNOT ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact qmCNOT_unitary

/-- `qmSWAP ∈ U(4)`: `SWAPᴴ * SWAP = 1`. -/
theorem qmSWAP_mem_unitaryGroup : qmSWAP ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact qmSWAP_unitary

/-- `qmCZ ∈ U(4)`: `CZᴴ * CZ = 1`. -/
theorem qmCZ_mem_unitaryGroup : qmCZ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact qmCZ_unitary

/-- **§13.2 discharge (CNOT).** `cnot_realisable_for (cpSectorData p₀)` holds: the bundle's
`U` is the CNOT action, `U_isometry` derived from `qmCNOT ∈ U(4)`. Modulo A5. -/
theorem cnot_realisable_cpSector (p₀ : CPN 4) :
    CSD.Empirical.CSDBridge.Gates.TwoQubit.cnot_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmCNOT)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmCNOT, qmCNOT_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

/-- **§13.2 discharge (SWAP).** `swap_realisable_for (cpSectorData p₀)` holds. -/
theorem swap_realisable_cpSector (p₀ : CPN 4) :
    CSD.Empirical.CSDBridge.Gates.TwoQubit.swap_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmSWAP)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmSWAP, qmSWAP_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

/-- **§13.2 discharge (CZ).** `cz_realisable_for (cpSectorData p₀)` holds. -/
theorem cz_realisable_cpSector (p₀ : CPN 4) :
    CSD.Empirical.CSDBridge.Gates.TwoQubit.cz_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmCZ)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmCZ, qmCZ_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

end CSD.LF4
