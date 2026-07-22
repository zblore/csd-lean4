/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Gates.WignerDischarge
public import CsdLean4.Empirical.CSD.Gates.MultiQubit

/-!
# Empirical/CSD/Gates: §13.2 discharge for the multi-qubit gates (Toffoli, Fredkin)

**Category:** 3-Local (CSD-side concrete discharge of LF4-§13.2, multi-qubit tier).

Companion to `Gates/{SingleQubit,TwoQubit}Discharge.lean`. The two three-qubit gate
`*_realisable_for` Props (`Empirical/CSD/Gates/MultiQubit.lean`) were claim-shaped
placeholders (`PLACEHOLDERS.md §1`). This module DISCHARGES them on `cpSectorData p₀`
(`p₀ : CPN 8`): each gate's action is a genuine `CSDUnitaryBundle` whose `U` IS the gate
and whose `U_isometry` is derived from the gate lying in `U(8)` (`inner_toEuclideanLin_unitary`).
Toffoli and Fredkin are real Hermitian permutation involutions, so `Gᴴ * G = 1`
(`qmG_unitary`) gives membership directly.

## Honest scope

Identical to the earlier tiers: **modulo A5**; the bundle type carries `U` + `U_isometry`
+ a `Context`, not a Σ-flow (`PLACEHOLDERS.md §7`), so this discharges the Prop *as typed*,
not the Σ-flow-lift prose (open **D1** gap). `U_isometry` is derived from
`qm{Toffoli,Fredkin} ∈ U(8)` (sector-symmetry membership), not `μL`-measure-preservation.

References: `Gates/SingleQubitDischarge.lean`, `Empirical/QM/Gates/MultiQubit.lean`
(`qmToffoli`, `qmFredkin`, `qmG_unitary`), `PLACEHOLDERS.md` §1/§7.
-/

@[expose] public section

open Matrix
open CSD.Empirical.QM.Gates
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- `qmToffoli ∈ U(8)`: `Toffoliᴴ * Toffoli = 1` (Hermitian involution). -/
theorem qmToffoli_mem_unitaryGroup : qmToffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact qmToffoli_unitary

/-- `qmFredkin ∈ U(8)`: `Fredkinᴴ * Fredkin = 1`. -/
theorem qmFredkin_mem_unitaryGroup : qmFredkin ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact qmFredkin_unitary

/-- **§13.2 discharge (Toffoli).** `toffoli_realisable_for (cpSectorData p₀)` holds. -/
theorem toffoli_realisable_cpSector (p₀ : CPN 8) :
    CSD.Empirical.CSDBridge.Gates.MultiQubit.toffoli_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmToffoli)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmToffoli, qmToffoli_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

/-- **§13.2 discharge (Fredkin).** `fredkin_realisable_for (cpSectorData p₀)` holds. -/
theorem fredkin_realisable_cpSector (p₀ : CPN 8) :
    CSD.Empirical.CSDBridge.Gates.MultiQubit.fredkin_realisable_for (cpSectorData p₀) :=
  ⟨{ toContext := cpContext p₀
     U := ⇑(Matrix.toEuclideanLin qmFredkin)
     U_isometry := fun x y =>
       Projectivization.inner_toEuclideanLin_unitary ⟨qmFredkin, qmFredkin_mem_unitaryGroup⟩ x y },
   fun _ => rfl⟩

end CSD.LF4
