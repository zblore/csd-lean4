import CsdLean4.LF1.MainTheorem
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.Interface
import CsdLean4.LF2.Preparation
import CsdLean4.LF3.Interface
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF3.Projectors.TensorModel
import CsdLean4.Empirical.Bell
import CsdLean4.Empirical.NoCloning
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace

/-!
# Axiom regression suite

**Category:** Special (cross-layer axiom-posture regression for all headline theorems).

`#guard_msgs` + `#print axioms` for every theorem in `AXIOMS.md §5`. Build
fails on regression: if any theorem acquires (or sheds) an axiom, the
expected `info:` string no longer matches `#print axioms`'s output, and
this module fails to compile.

The intent is **not** to forbid axiom changes; legitimate changes are
welcome and require updating both this module and `AXIOMS.md §5` in the
same commit. The intent is to make axiom drift impossible without an
explicit, visible diff.

## How to update

When discharging an axiom (e.g., LF4 proves `rankOneDensity_unique_of_certainty`)
or introducing a new one, update the `/-- info: ... -/` line above the
corresponding `#print axioms` to match the new output, in lockstep with
the corresponding `AXIOMS.md §5` row.
-/

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3

/-! ### LF1 -/

/-- info: 'CSD.LF1.OnticSetup.LF1_main_theorem_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF1_main_theorem_ae

/-! ### LF2 -/

/-- info: 'CSD.LF2.LF1_main_theorem_projective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF1_main_theorem_projective

/-- info: 'CSD.LF2.lf1_weight_eq_projective_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lf1_weight_eq_projective_weight

/-- info: 'CSD.LF2.SectorData.outcomeOfProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SectorData.outcomeOfProjective

/-- info: 'CSD.LF2.SectorData.outcomeOfProjective_preEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SectorData.outcomeOfProjective_preEvent

/--
info: 'CSD.LF2.SectorData.outcomeOfProjective_weight_eq_projectiveWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms SectorData.outcomeOfProjective_weight_eq_projectiveWeight

/-- info: 'CSD.LF2.measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound, invariant_measure_uniqueness] -/
#guard_msgs in #print axioms measure_bridge

/-- info: 'CSD.LF2.born_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms born_quadratic

/-- info: 'CSD.LF2.pure_state_born_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pure_state_born_weights

/--
info: 'CSD.LF2.pure_state_born_weights_of_certainty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms pure_state_born_weights_of_certainty

/-- info: 'CSD.LF2.PurePreparation.OP_certain_at_ψ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.OP_certain_at_ψ

/-- info: 'CSD.LF2.PurePreparation.born_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one

/-- info: 'CSD.LF2.PurePreparation.born_rank_one_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one_direct

/-! ### LF3 -/

/-- info: 'CSD.LF3.LF3_main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_main_theorem

/-- info: 'CSD.LF3.LF3_finite_leakage_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_finite_leakage_theorem

/--
info: 'CSD.LF3.LF3_singlet_frequency_convergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence

/--
info: 'CSD.LF3.LF3_singlet_frequency_convergence_born' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born

/--
info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_inner

/--
info: 'CSD.LF3.LF3_singlet_frequency_convergence_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_joint

/--
info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_joint

/--
info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_inner_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_inner_joint

/-- info: 'CSD.LF3.PureSingletPreparation.ofHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PureSingletPreparation.ofHypothesis

/--
info: 'CSD.LF3.PureSingletPreparation.weight_eq_P_st' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms PureSingletPreparation.weight_eq_P_st

/-- info: 'CSD.LF3.ProjectorAlgebra.ofTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProjectorAlgebra.ofTensorEmbedding

/--
info: 'CSD.LF3.MeasurementJointEig.singletProjectiveOutcome_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms MeasurementJointEig.singletProjectiveOutcome_measurable

/--
info: 'CSD.LF3.MeasurementJointEig.singletProjectiveOutcome_disjoint_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms MeasurementJointEig.singletProjectiveOutcome_disjoint_distinct

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st_direct

/-- info: 'CSD.LF3.MeasurementUnitary.ofUnitaryTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasurementUnitary.ofUnitaryTensorEmbedding

/-! ### Empirical predictions (Bell family, Phase A1-A5)

All Phase A1-A5 predictions cite only the foundational triple: the LF3
content they re-export does too (LF3 algebraic core in `Singlet/Kernel.lean`
is axiom-clean), and the new CHSH-at-Tsirelson computation is pure
arithmetic. -/

/-- info: 'CSD.Empirical.Bell.correlation_eq_neg_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.correlation_eq_neg_dot

/-- info: 'CSD.Empirical.Bell.no_signalling_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_alice

/-- info: 'CSD.Empirical.Bell.no_signalling_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_bob

/-- info: 'CSD.Empirical.Bell.singlet_marginal_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_alice

/-- info: 'CSD.Empirical.Bell.singlet_marginal_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_bob

/-- info: 'CSD.Empirical.Bell.chsh_classical_bound_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_classical_bound_violated

/-- info: 'CSD.Empirical.Bell.chsh_singlet_at_optimal_angles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_at_optimal_angles

/-- info: 'CSD.Empirical.Bell.chsh_singlet_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_tsirelson_bound

/-- info: 'CSD.Empirical.Bell.chsh_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_inner_bound

/-- info: 'CSD.Empirical.Bell.chsh_qm_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_qm_tsirelson_bound

/-! ### Empirical predictions (no-cloning, Phase B2) -/

/-- info: 'CSD.Empirical.NoCloning.no_cloning_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_cloning_two_state

/-- info: 'CSD.Empirical.NoCloning.no_universal_cloner_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_universal_cloner_of_witness

/-! ### Mathlib upstream candidates (Projectivization, §12)

These are CSD-free Mathlib-track lemmas staged under
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/`. They cite the
foundational triple only — any axiom acquisition would be an upstream
regression and a blocker for the eventual Mathlib PR. -/

/-- info: 'Projectivization.continuous_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_mk'

/-- info: 'Projectivization.isOpenMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isOpenMap_mk'

/-- info: 'Projectivization.isOpenQuotientMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isOpenQuotientMap_mk'

/-- info: 'Projectivization.instT2Space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instT2Space

/-- info: 'Projectivization.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instCompactSpace

/-- info: 'Projectivization.instMeasurableSingletonClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instMeasurableSingletonClass

/-- info: 'Projectivization.borel_eq_map_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.borel_eq_map_mk'

/-- info: 'Projectivization.lift_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.lift_measurable

/-- info: 'Projectivization.measurable_iff_measurable_comp_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.measurable_iff_measurable_comp_mk'

end CSD.Tests.AxiomAudit
