/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
# Ecdsafail axiom audit — the ecdsa.fail track's `#print axioms` pins

This is the axiom-audit for the **ecdsa.fail / ECDLP quantum-cryptanalysis track**
(`CsdLean4/Ecdsafail/`), separated out of the core `CsdLean4/Tests/AxiomAudit.lean` so
that the core QM test suite does not import or build the ecdsa track. Its `lean_lib`
target is `Ecdsafail` (see `lakefile.toml`); the core `CsdLeanTests` lib no longer
reaches ecdsa.

Contents: the `#print axioms` / `#guard_msgs` pins for the moved modules — the 4
ecdsa-specific circuit-assembly files (`Reversible.*` theorems, namespace kept on move)
and the 17 ECDLP-proper modules (`ECDLP.*`). The shared reversible-arithmetic DSL pins
(`Reversible.modMul_*`, `Cuccaro*`, `Gidney*`, …) stay in the core audit — those modules
stayed in `Reversible/`.
-/

import CsdLean4.Ecdsafail.ProgramRouter
import CsdLean4.Ecdsafail.ProgramRouterDoubling
import CsdLean4.Ecdsafail.DoublingAssembly
import CsdLean4.Ecdsafail.DoublingAssemblyOps
import CsdLean4.Ecdsafail.EllipticCurve
import CsdLean4.Ecdsafail.ScalarMul
import CsdLean4.Ecdsafail.Secp256k1
import CsdLean4.Ecdsafail.ResourceBounds
import CsdLean4.Ecdsafail.Inversion
import CsdLean4.Ecdsafail.PointDouble
import CsdLean4.Ecdsafail.PointAdd
import CsdLean4.Ecdsafail.PointAddBenchmark
import CsdLean4.Ecdsafail.SafegcdInversion
import CsdLean4.Ecdsafail.KaratsubaMul
import CsdLean4.Ecdsafail.HalfGcdInversion
import CsdLean4.Ecdsafail.TwoTrack
import CsdLean4.Ecdsafail.ThreeTrackScore
import CsdLean4.Ecdsafail.TrustedEstimate
import CsdLean4.Ecdsafail.SafegcdDivstep
import CsdLean4.Ecdsafail.SafegcdDivstepCircuit
import CsdLean4.Ecdsafail.SafegcdExecCost

/-! ### ECDLP SLP → circuit router STEP 1 (Ecdsafail/ProgramRouter.lean) -/

/-- info: 'Reversible.contigBlock_injOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.contigBlock_injOn

/-- info: 'Reversible.add_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.add_bridge

/-- info: 'Reversible.mul_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_bridge

/-- info: 'Reversible.nsmul_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.nsmul_bridge

/-- info: 'Reversible.neg_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.neg_bridge

/-- info: 'Reversible.sub_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sub_bridge

/-- info: 'Reversible.modSub_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_preserves_external

/-- info: 'Reversible.router_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.router_holds

/-- info: 'Reversible.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.compile_correct

/-- info: 'Reversible.worked_compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.worked_compile_correct

/-! ### ECDLP SLP → circuit dispatcher STEP 2 (Ecdsafail/ProgramRouterDoubling.lean) -/

/-- info: 'Reversible.mulLoop_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_preserves_external

/-- info: 'Reversible.modConstMul_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_preserves_external

/-- info: 'Reversible.addWrap_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.addWrap_correct

/-- info: 'Reversible.subWrap_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.subWrap_correct

/-- info: 'Reversible.compileInstr_emits_mulLoop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.compileInstr_emits_mulLoop

/-- info: 'Reversible.mulLoopEmissions_eq_mulCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoopEmissions_eq_mulCount

/-- info: 'Reversible.doubling_mulLoop_emissions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.doubling_mulLoop_emissions

/-- info: 'Reversible.doubling_mulLoop_emissions_eq_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.doubling_mulLoop_emissions_eq_8

/-- info: 'Reversible.worked_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.worked_value

/-! ### ECDLP SLP → circuit STEP 3: PROVEN gadget assembly (Ecdsafail/DoublingAssembly.lean) -/

/-- info: 'Reversible.hornerStep_preserves_ctrl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_preserves_ctrl

/-- info: 'Reversible.mulLoop_preserves_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_preserves_X

/-- info: 'Reversible.mulLoop_preserves_ctrl_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_preserves_ctrl_wire

/-- info: 'Reversible.nsmul_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.nsmul_step_assembly_correct

/-- info: 'Reversible.nsmul_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.nsmul_step_value

/-- info: 'Reversible.mul_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_step_assembly_correct

/-- info: 'Reversible.mul_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_step_value

/-- info: 'Reversible.doubling_field_mul_count_eq_8_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.doubling_field_mul_count_eq_8_verified

/-! ### ECDLP per-opcode fold closure STEP 4 (Ecdsafail/DoublingAssemblyOps.lean) -/

/-- info: 'Reversible.modAdd_preserves_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_preserves_block

/-- info: 'Reversible.modSub_preserves_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_preserves_block

/-- info: 'Reversible.sq_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sq_step_assembly_correct

/-- info: 'Reversible.sq_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sq_step_value

/-- info: 'Reversible.add_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.add_step_assembly_correct

/-- info: 'Reversible.add_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.add_step_value

/-- info: 'Reversible.sub_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sub_step_assembly_correct

/-- info: 'Reversible.sub_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sub_step_value

/-- info: 'Reversible.all_six_opcodes_through_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.all_six_opcodes_through_fold

/-! ### ECDLP elliptic-curve layer (ECDLP/EllipticCurve.lean, Tranche 5) -/

/-- info: 'ECDLP.scalarMul_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.scalarMul_add

/-- info: 'ECDLP.scalarMul_addOrderOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.scalarMul_addOrderOf

/-- info: 'ECDLP.isDLog_add_addOrderOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.isDLog_add_addOrderOf

/-! ### ECDLP double-and-add scalar multiplication (ECDLP/ScalarMul.lean, Tranche 6) -/

/-- info: 'ECDLP.doubleAndAdd_eq_nsmul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAdd_eq_nsmul

/-- info: 'ECDLP.doubleAndAdd_eq_scalarMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAdd_eq_scalarMul

/-- info: 'ECDLP.doubleAndAddCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAddCost_le

/-- info: 'ECDLP.doubleAndAddWeightedCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAddWeightedCost_le

/-! ### ECDLP secp256k1 capstone (Secp256k1.lean + ResourceBounds.lean, Tranche 7) -/

/-- info: 'ECDLP.Secp256k1.p_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.Secp256k1.p_lt_two_pow

/-- info: 'ECDLP.ResourceBounds.scalarMulToffoli_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.scalarMulToffoli_le

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_bound

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliBound_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliBound_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_concrete

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliRefined_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliRefined_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_refined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_refined

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliWindowed_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliWindowed_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliOptimized_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliOptimized_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1DepthSequential_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1DepthSequential_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1DepthOptimized_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1DepthOptimized_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1QubitsBaseline_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1QubitsBaseline_eq

/-- info: 'ECDLP.ResourceBounds.modMultToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.modMultToffoli_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliWithReduction_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliWithReduction_eq

/-! ### ECDLP H1 secp256k1 figure from the verified modular arithmetic (ResourceBounds.lean) -/

/-- info: 'ECDLP.ResourceBounds.verifiedModMulToffoli_eq_mulLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedModMulToffoli_eq_mulLoop

/-- info: 'ECDLP.ResourceBounds.verifiedModMulToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedModMulToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.verifiedDoublingToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedDoublingToffoli_eq

/-- info: 'ECDLP.ResourceBounds.verifiedDoublingToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedDoublingToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.verifiedAdditionToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedAdditionToffoli_eq

/-- info: 'ECDLP.ResourceBounds.verifiedAdditionToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedAdditionToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliVerifiedArith_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliVerifiedArith_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_verified_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_verified_arith

/-! ### ECDLP Stage 3 secp256k1 figure from the carry-clean modular arithmetic (ResourceBounds.lean) -/

/-- info: 'ECDLP.ResourceBounds.cleanModMulToffoli_eq_cuccaro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulToffoli_eq_cuccaro

/-- info: 'ECDLP.ResourceBounds.cleanModMulToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliCleanArith_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliCleanArith_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_clean_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_clean_arith

/-- info: 'ECDLP.ResourceBounds.cleanModMulQubits_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulQubits_secp256k1

/-- info: 'ECDLP.ResourceBounds.cleanModMulQubits_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulQubits_inhabited

/-! ### ECDLP Fermat modular inversion: algebra + cost fold-in (Inversion.lean + ResourceBounds.lean) -/

/-- info: 'ECDLP.fermatInv_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.fermatInv_eq_inv

/-- info: 'ECDLP.fermatInv_eq_modInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.fermatInv_eq_modInv

/-- info: 'ECDLP.modExpFieldMults_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.modExpFieldMults_le

/-- info: 'ECDLP.fermatInvFieldMults_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.fermatInvFieldMults_le

/-- info: 'ECDLP.ResourceBounds.fermatInvToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.fermatInvToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliCleanArithWithInversion_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliCleanArithWithInversion_eq

/-! ### ECDLP full quantum core (2nd scalar mult + QFT) + affine variant (ResourceBounds.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1EcdlpQftToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1EcdlpQftToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1EcdlpToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1EcdlpToffoli_eq

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliAffineWithInversion_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliAffineWithInversion_eq

/-! ### ECDSA.fail benchmark: one affine point addition (PointAddBenchmark.lean) -/

/-- info: 'ECDLP.ResourceBounds.classicalOffsetCoordToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.classicalOffsetCoordToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.classicalOffset_coord_lt_one_qq_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.classicalOffset_coord_lt_one_qq_mult

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_eq

/-- info: 'ECDLP.ResourceBounds.onePointAdd_toffoli_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAdd_toffoli_le

/-- info: 'ECDLP.ResourceBounds.onePointAddPeakQubits_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddPeakQubits_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_eq

/-! ### ECDLP L6 binary-GCD / Kaliski modular inversion (SafegcdInversion.lean) -/

/-- info: 'ECDLP.binGcdInv_mul_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.binGcdInv_mul_eq_one

/-- info: 'ECDLP.binGcdInv_eq_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.binGcdInv_eq_inv

/-- info: 'ECDLP.binGcdInv_eq_modInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.binGcdInv_eq_modInv

/-- info: 'ECDLP.ResourceBounds.divstepToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.divstepToffoli_eq

/-- info: 'ECDLP.ResourceBounds.divstepToffoli_eq_gadgets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.divstepToffoli_eq_gadgets

-- EC-2 (2026-07-09, cost side): the divstep gadget EXHIBITED as one concrete Circuit
-- (modSub ++ cuccaroCModAdd ++ cuccaroModDouble) whose Toffoli cost IS divstepToffoli n. So the cost is
-- the cost of a real in-DSL circuit, not a count over a hypothetical one. HONEST: this is the modular
-- PROXY circuit (denote ≠ integer divstep); the value-faithful divstepGadget (denote = divstep, with
-- garbage bits since divstep is not injective) is the deferred residue.
/-- info: 'ECDLP.ResourceBounds.divstepProxyGadget_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.divstepProxyGadget_toffoli

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_eq

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_safegcd_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_safegcd_secp256k1

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_lt_fermat_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_lt_fermat_secp256k1

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_le_fermat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_le_fermat

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_safegcd_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_safegcd_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_safegcd_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_safegcd_eq

/-- info: 'ECDLP.ResourceBounds.safegcd_score_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_score_improvement

/-- info: 'ECDLP.ResourceBounds.fermat_score_gap_vs_leaderboard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.fermat_score_gap_vs_leaderboard

/-- info: 'ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_upper

/-! ### ECDLP L2 windowed Fermat inversion — DOCUMENTED COMPARISON, off the critical path
(SafegcdInversion.lean). Cost-model only; safegcd wins even against windowed Fermat. -/

/-- info: 'ECDLP.ResourceBounds.windowedFermatInvToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.windowedFermatInvToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.windowedFermatInvToffoli_lt_fermat_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.windowedFermatInvToffoli_lt_fermat_secp256k1

/-- info: 'ECDLP.ResourceBounds.safegcd_beats_windowed_fermat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_beats_windowed_fermat

-- ECDLP L8 (2026-07-09): the sub-quadratic (half-GCD) inversion lever, quantified at 256. It BEATS
-- safegcd at 256 iff the recursion is tuned to ≤1 full Karatsuba multiply per level (k=1, ≤8 total);
-- at k≥2 it loses. So a genuine beat CANDIDATE at the ECDLP width — on the knife-edge — the honest
-- "can we beat, not just reproduce" answer. Documented op-count model over the verified Karatsuba mult.
/-- info: 'ECDLP.ResourceBounds.halfGcd_aggressive_beats_safegcd_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_aggressive_beats_safegcd_256

/-- info: 'ECDLP.ResourceBounds.halfGcd_beats_iff_k_one_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_beats_iff_k_one_256

-- ECDLP L8 faster-M(n) lever (2026-07-10): substitute the verified Toom-3 multiply (Θ(n^1.465)) into the
-- half-GCD model and characterise the beat threshold in the multiply cost. Toom-3 IMPROVES the k=1 margin
-- (12%→~24%) but does NOT flip the threshold at 256 (still beats iff k≤1); flipping to k=2 needs
-- M(256) ≤ 369311, below both Karatsuba (653388) and Toom-3 (596490) — an FFT-class multiply. The
-- knife-edge at the ECDLP width is structural (8 levels vs safegcd's tight ~90n²), not a Karatsuba artefact.
/-- info: 'ECDLP.ResourceBounds.halfGcdInvToffoli_eq_with' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcdInvToffoli_eq_with

/-- info: 'ECDLP.ResourceBounds.halfGcd_toom3_beats_iff_k_one_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_toom3_beats_iff_k_one_256

/-- info: 'ECDLP.ResourceBounds.halfGcd_toom3_improves_margin_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_toom3_improves_margin_256

/-- info: 'ECDLP.ResourceBounds.halfGcd_k2_beats_iff_mult_budget_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_k2_beats_iff_mult_budget_256

/-- info: 'ECDLP.ResourceBounds.karatsuba_toom3_miss_k2_budget_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_toom3_miss_k2_budget_256

/-- info: 'ECDLP.ResourceBounds.windowedFermatInvToffoli_ge_cubic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.windowedFermatInvToffoli_ge_cubic

/-! ### ECDLP L7 Karatsuba sub-quadratic modular multiply cost model (KaratsubaMul.lean) -/

/-- info: 'ECDLP.ResourceBounds.karatsuba_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_identity

/-- info: 'ECDLP.ResourceBounds.kCombineToffoli_eq_adders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.kCombineToffoli_eq_adders

/-- info: 'ECDLP.ResourceBounds.karatsubaToffoli_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsubaToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.karatsubaToffoli_lt_schoolbook_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsubaToffoli_lt_schoolbook_secp256k1

-- ECDLP L7-t Toom-3 modular multiply (Θ(n^{log₃5})=Θ(n^1.465)), same verified footing as Karatsuba
-- (base = verified schoolbook, combine = verified modular adders). toom3Toffoli 256 = 596490 < 653388.
/-- info: 'ECDLP.ResourceBounds.toom3_coeff_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3_coeff_identity

/-- info: 'ECDLP.ResourceBounds.toom3CombineToffoli_eq_adders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3CombineToffoli_eq_adders

/-- info: 'ECDLP.ResourceBounds.toom3Toffoli_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3Toffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.toom3Toffoli_lt_karatsuba_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3Toffoli_lt_karatsuba_secp256k1

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_karatsuba_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_karatsuba_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_karatsuba_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_karatsuba_eq

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_improvement

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_upper

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_karatsuba_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_karatsuba_secp256k1

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_improvement_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_improvement_quant

/-! ### ECDLP L3 dedicated modular squaring cost model + re-cost (KaratsubaMul.lean) -/

/-- info: 'ECDLP.ResourceBounds.karatsubaSquare_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsubaSquare_identity

/-- info: 'ECDLP.ResourceBounds.schoolbookSquareToffoli_two_mul' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.schoolbookSquareToffoli_two_mul

/-- info: 'ECDLP.ResourceBounds.squareToffoli_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squareToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.squareToffoli_lt_multiply_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squareToffoli_lt_multiply_secp256k1

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_squaring_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_squaring_secp256k1

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_squaring_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_squaring_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_squaring_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_squaring_eq

/-- info: 'ECDLP.ResourceBounds.squaring_score_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squaring_score_improvement

/-- info: 'ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_upper

/-! ### ECDLP two-track resource accounting: verified floor / trusted estimate / frontier (TwoTrack.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_verifiedFloor_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_verifiedFloor_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_eq

/-- info: 'ECDLP.ResourceBounds.verifiedFloor_no_trusted_leak' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedFloor_no_trusted_leak

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_uses_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_uses_trusted

/-- info: 'ECDLP.ResourceBounds.verificationFrontier_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verificationFrontier_length

/-- info: 'ECDLP.ResourceBounds.two_track_gap_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.two_track_gap_lower

/-- info: 'ECDLP.ResourceBounds.two_track_gap_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.two_track_gap_upper

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_lt_verifiedFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_lt_verifiedFloor

/-! ### ECDLP THREE-TRACK score ledger: Verified / Trusted / Leaderboard (ThreeTrackScore.lean, 2026-07-17)
The ecdsa.fail SCORE (peak × Toffoli) split three ways. Verified score = verifiedFloor × peak 2822 =
1.91e12; Trusted score = trustedEstimate × peak 2822 = 2.2e10; Leaderboard (competition convention) =
optimised peak 1156 × CALCULATED avg-executed 1,950,403 = 2,254,665,868 ≈ 2.25e9 -- ~1.44× the live best
(leaderboard_calculated_gap: ratio in (1.4,1.5); leaderboard_not_below_best: ABOVE it, NOT a win). The
avg-executed is COMPUTED (SafegcdExecCost.lean: competition's executed-Toffoli rule MEASURED on the
verified n=3 adder = 25% executed/emitted, × emitted worst-case 7,801,612), a grounded MODEL — not the
frontier's number. The exact figure needs the assembled op-stream + eval_circuit (#7). -/

/-- info: 'ECDLP.ResourceBounds.leaderboardConventionScore_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboardConventionScore_eq

/-- info: 'ECDLP.ResourceBounds.leaderboard_calculated_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboard_calculated_gap

/-- info: 'ECDLP.ResourceBounds.leaderboard_not_below_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboard_not_below_best

/-- info: 'ECDLP.ResourceBounds.three_tracks_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.three_tracks_ordered

/-! ### ECDLP Stage-1 trusted leaderboard estimate: measurement + windowing + qubit model + score (TrustedEstimate.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_measGidney_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_measGidney_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_v2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_v2_eq

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_v2_lt_trustedEstimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_v2_lt_trustedEstimate

/-- info: 'ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_eq

/-- info: 'ECDLP.ResourceBounds.qubits_trustedEstimate_lt_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_trustedEstimate_lt_anchor

/-- info: 'ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_eq

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_lt_squaring_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_lt_squaring_score

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_v2_uses_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_v2_uses_trusted

/-- info: 'ECDLP.ResourceBounds.leaderboardScoreExact_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboardScoreExact_eq

/-- info: 'ECDLP.ResourceBounds.toffoli_v2_reproduces_leaderboard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toffoli_v2_reproduces_leaderboard

/-- info: 'ECDLP.ResourceBounds.qubits_trustedEstimate_two_leaderboard' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_trustedEstimate_two_leaderboard

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_upper

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_vs_rounded_leaderboard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_vs_rounded_leaderboard

/-! ### ECDLP Stage-2 aggressive qubit layout: cited 4.5n = 1152, recomposed score, ~1.07x rank (TrustedEstimate.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_aggressive_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_aggressive_eq

/-- info: 'ECDLP.ResourceBounds.qubits_aggressive_matches_leaderboard_benchmark' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_aggressive_matches_leaderboard_benchmark

/-- info: 'ECDLP.ResourceBounds.qubits_aggressive_half_trustedEstimate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_aggressive_half_trustedEstimate

/-- info: 'ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_aggressive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_aggressive_eq

/-- info: 'ECDLP.ResourceBounds.score_aggressive_within_leaderboard_benchmark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_aggressive_within_leaderboard_benchmark

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_aggressive_uses_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_aggressive_uses_trusted

-- Stage-2b (2026-07-12): the aggressive 4.5n qubit layout given a register-role breakdown grounded in the
-- corpus's verified measurement-ancilla-recycling. secp256k1Qubits_aggressive_breakdown = 2n + 5n/2 = 9n/2
-- = 1152 (2n coords + 2.5n recycled scratch), = leaderboardQubits (aggressive_breakdown_closes_qubit_gap):
-- the 2x qubit gap (2304→1152) closed via the same discipline that halves the AND-adder Toffoli (EC-6/L5-d).
-- Documented layout model (trusted tier), not a verified circuit.
/-- info: 'ECDLP.ResourceBounds.secp256k1Qubits_aggressive_breakdown_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Qubits_aggressive_breakdown_eq

/-- info: 'ECDLP.ResourceBounds.aggressive_breakdown_closes_qubit_gap' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.aggressive_breakdown_closes_qubit_gap

/-! ### ECDLP S6.1 concrete EC doubling: derived field-mult count (PointDouble.lean) -/

/-- info: 'ECDLP.doublingProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doublingProgram_correct

/-- info: 'ECDLP.M_dbl_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.M_dbl_eq

/-- info: 'ECDLP.doubling_toffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubling_toffoli_eq

/-- info: 'ECDLP.doubling_toffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubling_toffoli_secp256k1

/-! ### ECDLP S6.2 concrete EC mixed addition: derived field-mult count (PointAdd.lean) -/

/-- info: 'ECDLP.additionProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.additionProgram_correct

/-- info: 'ECDLP.additionProgram_correct_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.additionProgram_correct_vector

/-- info: 'ECDLP.M_add_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.M_add_eq

/-- info: 'ECDLP.addition_toffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.addition_toffoli_eq

/-- info: 'ECDLP.addition_toffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.addition_toffoli_secp256k1


-- Safegcd (Bernstein-Yang) divstep: the GCD invariant as a GENUINE theorem
-- (divstep_gcd, not a ZMod.inv unfolding; Odd f load-bearing), the divstep
-- function, correctness-modulo-termination, and Bezout-up-to-2^k. Termination +
-- the reversible circuit + the 2^{-k} correction are named residuals (still
-- trusted). All foundational-triple.
/-- info: 'ECDLP.Safegcd.divstep_fst_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_fst_odd

/-- info: 'ECDLP.Safegcd.gcd_two_mul_right_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.gcd_two_mul_right_of_odd

/-- info: 'ECDLP.Safegcd.divstep_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_gcd

/-- info: 'ECDLP.Safegcd.divstepIter_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_gcd

/-- info: 'ECDLP.Safegcd.divstepIter_natAbs_of_g_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_natAbs_of_g_zero

/-- info: 'ECDLP.Safegcd.divstepIter_natAbs_one_of_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_natAbs_one_of_coprime

-- EC-1 (2026-07-09): termination STABILITY (the fixed-count-loop half). g=0 is absorbing
-- (divstep_snd_snd_zero); once g hits 0 the surviving |f| = gcd(f₀,g₀) and STAYS so for every further
-- step (divstepIter_natAbs_of_g_zero_stable) — so a fixed 3n-step loop reads the right answer on any
-- input that terminates within it. The termination-COUNT bound itself (g reaches 0 within ~2.88·bits,
-- Bernstein-Yang's computer-assisted argument) stays the external residual.
/-- info: 'ECDLP.Safegcd.divstep_snd_snd_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_snd_snd_zero

/-- info: 'ECDLP.Safegcd.divstepIter_zero_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_zero_stable

/-- info: 'ECDLP.Safegcd.divstepIter_natAbs_of_g_zero_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_natAbs_of_g_zero_stable

-- EC-2 value side (2026-07-09): the divstep is REVERSIBLE on the odd-f domain. Raw divstep is NOT
-- injective (divstep_not_injective: divstep 0 1 2 = divstep 0 1 1), so garbage is genuinely needed;
-- divstepRev keeps the minimal 2-bit branch selector (input sign-δ, parity-g), and divstepRev_injective
-- proves the extended transition injective for f odd — the mathematical basis for a denote=divstep
-- reversible circuit (2 garbage bits/step). The bit-level circuit itself is the deferred build.
/-- info: 'ECDLP.Safegcd.divstep_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_not_injective

/-- info: 'ECDLP.Safegcd.divstepRev_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepRev_injective

/-- info: 'ECDLP.Safegcd.divstepIter_bezout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_bezout

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 1 (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the value-faithful divstep bit-circuit (denote = divstep) opened at its exact-halving primitive.
-- shiftDown is a concrete `n`-swap Circuit; halve_correct proves it computes `÷2` on an EVEN register
-- at the `denote`/regValRange level (general n) -- the divstep's third register update, value-faithful
-- (the divstepProxyGadget above is only a modular COST proxy). shiftDown_toffoli: the halving is
-- Toffoli-FREE (pure wire permutation), refining divstepToffoli's `cuccaroModDouble` 6n+4 overcount.
-- Remaining tranches: signed subtraction (2), conditional swap + branch routing (3), assembly = divstepRev (4).
/-- info: 'ECDLP.Safegcd.Circuit.halve_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.halve_correct

/-- info: 'ECDLP.Safegcd.Circuit.shiftDown_apply_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.shiftDown_apply_lt

/-- info: 'ECDLP.Safegcd.Circuit.shiftDown_toffoli' depends on axioms: [propext] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.shiftDown_toffoli

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 2 (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the signed integer arithmetic for the divstep numerators g+f / g-f. signedRep is the two's-complement
-- balanced representative (signedRep_of_mem: fixes in-range values); regValZ the signed register value.
-- signedAdd_correct / signedSub_correct: under a no-overflow bound, the VERIFIED mod-2^n gadgets
-- (cuccaroAdd / rippleSub) realise signed ℤ addition / subtraction at the regValZ level -- the branch-B
-- `g+f` and branch-A `g-f` numerators on a value-faithful circuit (two's-complement +/- IS mod-2^n
-- arithmetic, exact whenever the true result fits the signed range).
/-- info: 'ECDLP.Safegcd.Circuit.signedAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedAdd_correct

/-- info: 'ECDLP.Safegcd.Circuit.signedSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedSub_correct

/-- info: 'ECDLP.Safegcd.Circuit.signedRep_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedRep_of_mem

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 3 (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the branch control. cswap (Fredkin) + condSwapReg: the value-faithful controlled register swap --
-- condSwapReg_swaps proves F,G exchange bitwise exactly when the control is set (divstep branch-A
-- `f ↔ g`), one Toffoli/bit (condSwapReg_toffoli). regValRange_odd_iff / regValZ_odd_iff: the `Odd g`
-- branch test IS a read of wire 0 (parity = low bit, interpretation-independent). Remaining: the `0<δ`
-- sign read + branch-bit ancilla synthesis + assembly = divstepRev (tranche 4).
/-- info: 'ECDLP.Safegcd.Circuit.cswap_correct_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cswap_correct_general

/-- info: 'ECDLP.Safegcd.Circuit.condSwapReg_swaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.condSwapReg_swaps

/-- info: 'ECDLP.Safegcd.Circuit.regValZ_odd_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_odd_iff

/-- info: 'ECDLP.Safegcd.Circuit.condSwapReg_toffoli' depends on axioms: [propext] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.condSwapReg_toffoli

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4a (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the SIGNED halving. Building the assembly exposed that tranche 1's shiftDown halves the UNSIGNED
-- magnitude (fills the vacated top with 0), but the divstep halves SIGNED numerators (g±f)/2 (g,f go
-- negative) -> needs a sign-EXTENDING right shift. signedHalve = shiftDown + one sign-copy CNOT;
-- signedHalve_correct: regValZ ÷2 for an even register (still Toffoli-free). Supporting two's-complement
-- lemmas: signedRep_high (high-half value = v - 2^W), regValZ_signBit (signed = lowbits - sign·2^n).
-- Remaining tranche-4 residual: g-update composition (signedSub;signedHalve), the δ-counter arithmetic
-- layer + `0<δ` read, branch-bit synthesis + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.signedHalve_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedHalve_correct

/-- info: 'ECDLP.Safegcd.Circuit.regValZ_signBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_signBit

/-- info: 'ECDLP.Safegcd.Circuit.signedRep_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedRep_high

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4b (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the g-register update, COMPOSING the tranches. gUpdateSub_correct: the composite rippleSub;signedHalve
-- computes g ↦ (g-f)/2 (branch-A numerator) at the signed regValZ level; gUpdateAdd_correct: cuccaroAdd;
-- signedHalve computes g ↦ (g+f)/2 (branch-B). Composes T2 (signed ±) with T4a (signed halve); f,g odd
-- makes the numerator even (Odd.sub_odd/add_odd), discharging the halving's bottom-bit hypothesis. So the
-- divstep g-update is now a single value-faithful circuit. Remaining: δ-counter arithmetic + branch
-- synthesis + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.gUpdateSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.gUpdateSub_correct

/-- info: 'ECDLP.Safegcd.Circuit.gUpdateAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.gUpdateAdd_correct

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4c (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the `0 < δ` control read (the branch discriminant). regValZ_nonneg_iff: 0 ≤ δ iff the sign bit (wire n)
-- is clear; regValZ_pos_iff: 0 < δ iff sign bit clear AND low bits nonzero -- the divstep branch-A test
-- `0<δ` as a bit read, via regValZ_signBit. (The `Odd g` half is regValZ_odd_iff, T3.) Remaining: the
-- δ-counter arithmetic δ ↦ 1±δ, branch-bit synthesis + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.regValZ_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_pos_iff

/-- info: 'ECDLP.Safegcd.Circuit.regValZ_nonneg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_nonneg_iff

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4d (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the δ-counter update δ ↦ 1±δ, a tranche-2 corollary (signed ± against constant 1, no new circuit).
-- deltaInc_correct: cuccaroAdd gives δ↦1+δ (branches B,C); deltaDec_correct: rippleSub gives δ↦1-δ
-- (branch A), each with a register holding the value 1. So every divstep sub-operation (swap, signed ±,
-- signed halve, g-update, δ-update, the 0<δ / Odd g reads) is now circuit-backed. Remaining: branch-bit
-- synthesis (needs a reversible nonzero/OR gadget) + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.deltaInc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.deltaInc_correct

/-- info: 'ECDLP.Safegcd.Circuit.deltaDec_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.deltaDec_correct

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4e (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the reversible nonzero/OR gadget (branch-synthesis prerequisite). orBlock: De Morgan `a ← c ∨ w` into
-- a fresh ancilla (1 Toffoli), c/w restored; orAccum: the ancilla-ladder fold, orAccum_correct proves the
-- top ancilla is `true` iff some low input wire is set -- a reversible nonzero test (the "low bits ≠ 0"
-- half of the 0<δ read, T4c). Preserves the input wires.
/-- info: 'ECDLP.Safegcd.Circuit.orBlock_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.orBlock_correct

/-- info: 'ECDLP.Safegcd.Circuit.orAccum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.orAccum_correct

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4f (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the branch-A f-recovery. addTwice_correct: two cuccaroAdds give f ← f + 2·g at the signed regValZ level
-- (the in-place resolution of f'=g: run the g-update first, then f_old + 2·(g-f)/2 = g_old recovers f'=g
-- with no swap, no value destroyed). branchA_recovers: the ℤ identity f + 2·((g-f)/2) = g (f,g odd)
-- confirming gUpdateSub (g-update, T4b) + addTwice compose to divstep branch A (f,g) ↦ (g,(g-f)/2).
/-- info: 'ECDLP.Safegcd.Circuit.addTwice_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.addTwice_correct

/-- info: 'ECDLP.Safegcd.Circuit.branchA_recovers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.branchA_recovers

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4g (2026-07-17, SafegcdDivstepCircuit.lean, #36c-2/#3):
-- lane-0 cswap elision (a real frontier Toffoli lever). cswap_noop_of_eq: a controlled swap of two wires
-- holding EQUAL values is the identity. cswap_lane0_noop: when the branch-A f↔g swap fires, f,g are both
-- odd so wire 0 is true for both -- the lane-0 swap is a no-op, eliminable (the field's `divstep 0..n →
-- 1..n`), here a proved value-exact identity.
/-- info: 'ECDLP.Safegcd.Circuit.cswap_noop_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cswap_noop_of_eq

/-- info: 'ECDLP.Safegcd.Circuit.cswap_lane0_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cswap_lane0_noop

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4h (2026-07-17, SafegcdDivstepCircuit.lean, #36c-2/#1):
-- the branch-control-bit synthesis. and3_correct: [CCX a b u, CCX u c t, CCX a b u] sets t = a∧b∧c and
-- restores scratch u (compute-copy-uncompute, 2 Toffoli) -- synthesises the branch-A control
-- bA = sign_clear ∧ nonzero_δ ∧ odd_g into a clean ancilla, the input the conditional gadgets consume.
/-- info: 'ECDLP.Safegcd.Circuit.and3_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.and3_correct

-- ECDLP TRANCHE 5 prerequisites (2026-07-18): frame/preservation lemmas for the branch-A end-to-end
-- assembly. shiftDown_apply_of_ne / signedHalve_apply_of_ne: a wire disjoint from the register family is
-- untouched by the shift / signed-halve (needed to show the g-update does not disturb the f register).
-- gUpdateSub_preserves_Sub: the g-update `rippleSub ; signedHalve` leaves regValZ of the f (Sub) register
-- unchanged (rippleSub keeps Sub read-only via rippleSub_invariant P2; signedHalve acts only on B=g) --
-- the glue that lets branch A recover f' = g by adding 2·g back into an intact f register afterwards.
/-- info: 'ECDLP.Safegcd.Circuit.shiftDown_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.shiftDown_apply_of_ne

/-- info: 'ECDLP.Safegcd.Circuit.signedHalve_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedHalve_apply_of_ne

/-- info: 'ECDLP.Safegcd.Circuit.gUpdateSub_preserves_Sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.gUpdateSub_preserves_Sub

-- ECDLP TRANCHE 5 (2026-07-18): the branch-A transformation assembled END-TO-END -- the first COMPLETE
-- divstep branch verified at the circuit level. rippleSub_apply_of_ne / addTwice_preserves_B: the extra
-- frames (borrow-chain leaves a disjoint carry ancilla alone; the f-recovery's two adders leave g intact).
-- branchA_transformation: on the shared BranchALayout (SubLayout view B=g,Sub=f + CuccaroLayout view
-- A=f,B=g), branchACircuit = (rippleSub;signedHalve);(cuccaroAdd;cuccaroAdd) realises divstep branch A
-- (f,g) ↦ (g,(g-f)/2) at the signed-ℤ level: f-reg ends = old g, g-reg ends = (g-f)/2. Composes
-- gUpdateSub_correct + gUpdateSub_preserves_Sub + addTwice_correct + branchA_recovers + addTwice_preserves_B.
/-- info: 'ECDLP.Safegcd.Circuit.rippleSub_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.rippleSub_apply_of_ne

/-- info: 'ECDLP.Safegcd.Circuit.addTwice_preserves_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.addTwice_preserves_B

/-- info: 'ECDLP.Safegcd.Circuit.branchA_transformation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.branchA_transformation

-- ECDLP EXECUTED-COST CERTIFICATION (2026-07-18, SafegcdExecCost.lean): the measured executed/emitted
-- ratio, now PROVED. executedToffoli_le_toffoli: on every input, Toffolis that FIRE ≤ Toffolis EMITTED --
-- so the competition's scored avg-executed quantity is a certified LOWER bound on the verified emitted
-- floor (the three-track direction, a theorem not a #eval). totalExecuted_le: total (hence average)
-- executed ≤ emitted × #inputs. inertToffoli_executed_zero: a CCX with a control clear contributes 0
-- executed but 1 emitted -- the certified data-dependence mechanism that puts average-executed below
-- worst-case. Axiom set [propext, Quot.sound] (constructive, no Classical.choice).
/-- info: 'ECDLP.Safegcd.Circuit.executedToffoli_le_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.executedToffoli_le_toffoli

/-- info: 'ECDLP.Safegcd.Circuit.totalExecuted_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.totalExecuted_le

/-- info: 'ECDLP.Safegcd.Circuit.inertToffoli_executed_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.inertToffoli_executed_zero

-- ECDLP EXECUTED-COST COMPOSITIONALITY (2026-07-18): toward a per-branch executed count.
-- executedToffoli_append: the executed count is additive over ++ (executed(c₁++c₂) a = executed c₁ a +
-- executed c₂ (runArr c₁ a)) -- the compositional backbone. signedHalve_executed_zero /
-- executedToffoli_eq_zero_of_toffoli_zero: Toffoli-free stages (the sign-extending halving) execute 0.
-- branchA_executed_decomp: executed(branchACircuit) = executed(rippleSub) + executed(2 adders) -- the
-- branch-A executed cost lives entirely in the subtractor + two adders; the halving contributes nothing.
/-- info: 'ECDLP.Safegcd.Circuit.executedToffoli_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.executedToffoli_append

/-- info: 'ECDLP.Safegcd.Circuit.signedHalve_executed_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedHalve_executed_zero

/-- info: 'ECDLP.Safegcd.Circuit.branchA_executed_decomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.branchA_executed_decomp

-- ECDLP PER-BRANCH INERTNESS (2026-07-18): the certified per-branch executed-count mechanism.
-- executedToffoli_cons: executed(g::gs) a = gateFires g a + executed gs (applyGate g a) (head peel).
-- applyGate_getElem!_of_not_writesTo: a gate not writing w preserves w's value (Array frame).
-- executedToffoli_ctrl_clear: a block where every CCX has control w, w never written and clear on input,
-- executes 0 Toffolis -- so a non-taken divstep branch (its select wire clear) costs nothing. With
-- executedToffoli_append this yields executed(divstep|branch X) = executed(unconditional)+executed(gadget X).
/-- info: 'ECDLP.Safegcd.Circuit.executedToffoli_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.executedToffoli_cons

/-- info: 'ECDLP.Safegcd.Circuit.applyGate_getElem!_of_not_writesTo' depends on axioms: [propext] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.applyGate_getElem!_of_not_writesTo

/-- info: 'ECDLP.Safegcd.Circuit.executedToffoli_ctrl_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.executedToffoli_ctrl_clear

-- ECDLP TAKEN-GADGET EXECUTED COUNT (2026-07-18, step 5): the adder's Toffoli cells' executed count as an
-- explicit boolean function of the data. uma_executed: the un-majority-add cell executes its Toffoli iff
-- both controls c,b are set (⟦arr c ∧ arr b⟧). maj_executed: the majority cell executes iff the two
-- CX-updated controls c⊕a, b⊕a are both set (⟦(arr a ⊕ arr c) ∧ (arr a ⊕ arr b)⟧, distinct wires) -- the
-- majority predicate. The adder's total executed count is the sum of these over its cells (via _append).
/-- info: 'ECDLP.Safegcd.Circuit.uma_executed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.uma_executed

/-- info: 'ECDLP.Safegcd.Circuit.maj_executed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.maj_executed

-- ECDLP CELL COMPOSITION THROUGH THE CARRY RECURSION (2026-07-18, step 6). cuccaroRec_executed_succ: the
-- executed count peels one Cuccaro bit -- executed(len+1-bit adder) = maj's + (len-bit remainder)'s +
-- uma's, each on the running array (composition through the recursion, via executedToffoli_append twice +
-- runArr_append). cuccaroAdd_one_executed: the base case as a CLOSED FORM -- the 1-bit adder executes 2
-- Toffolis iff the carry-generate predicate (B₀⊕Z)∧(A₀⊕B₀) holds, else 0 (maj and uma fire together). Over
-- uniform inputs the predicate is true 1/4 the time: avg-executed = 2·¼ = ½ of 2 emitted = the 25% ratio,
-- now certified from the closed form rather than #eval-measured.
/-- info: 'ECDLP.Safegcd.Circuit.cuccaroRec_executed_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cuccaroRec_executed_succ

/-- info: 'ECDLP.Safegcd.Circuit.cuccaroAdd_one_executed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cuccaroAdd_one_executed

