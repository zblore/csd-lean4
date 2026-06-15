# Spec → Lean cross-reference

Maps spec section numbers (Paper A / B / D) to the Lean theorem or definition that formalises them. The inverse mapping (Lean → file path) is in [`README.md`](../README.md) under "Theorem inventory" and in [`AXIOMS.md`](../AXIOMS.md) §5.

**Scope.** This table records the explicit `paper §X` / `spec §X` references that appear in Lean module docstrings as of `v0.3.2-lf3`. It is not a comprehensive audit of every spec sentence — only the sections that have a stable Lean counterpart. Sections without a Lean entry (e.g. paper §1, §2.1, §10.5 below) are present in the spec but consumed as background, not formalised individually.

**Maintenance.** When spec sections renumber, update both this file and the corresponding docstring `paper §X` references. The docstrings are the authoritative source; this file aggregates them.

## Paper A — LF1 (deterministic repeated-trial frequency theorem)

| Spec section | Lean reference | File |
|---|---|---|
| §4.2 (conditional measure) | `prepMeasure_apply` | `CsdLean4/LF1/Preparation.lean` |
| (frequency theorem) | `LF1_main_theorem_ae` | `CsdLean4/LF1/MainTheorem.lean` |

## Paper B — LF2 (measure bridge + Born-weight wrapper)

| Spec section | Lean reference | File |
|---|---|---|
| §3.3 Lemma 1 (preimage / action) | `preimage_action_eq` | `CsdLean4/LF2/MeasureBridge.lean` |
| §3.3 Lemma 2 (pushforward `G`-invariance) | `pushforward_epAction_invariant` | `CsdLean4/LF2/MeasureBridge.lean` |
| §3.3 Theorem 1 (measure bridge) | `measure_bridge` | `CsdLean4/LF2/MeasureBridge.lean` |
| §4.1 (measurable partition) | `MeasurablePartition` | `CsdLean4/LF2/Weights.lean` |
| §4.2 (projective weight) | `projectiveWeight` | `CsdLean4/LF2/Weights.lean` |
| §4.3 (normalisation) | `weights_sum_eq_one` | `CsdLean4/LF2/Weights.lean` |
| §5.2 / §7.4 (Busch effect-Gleason) | `busch_effect_gleason` (axiom) | `CsdLean4/LF2/BornWrapper.lean` |
| §5.4 (Born quadratic form) | `born_quadratic` | `CsdLean4/LF2/BornWrapper.lean` |
| §5.4 wrapper | `born_form_of_package` | `CsdLean4/LF2/BornWrapper.lean` |
| §5.4 pure-state weights | `pure_state_born_weights`, `pure_state_born_weights_of_certainty` | `CsdLean4/LF2/BornWrapper.lean` |
| §6 (LF1 ↔ LF2 identity) | `lf1_weight_eq_projective_weight` | `CsdLean4/LF2/Interface.lean` |
| §6 (combined headline) | `LF1_main_theorem_projective` | `CsdLean4/LF2/Interface.lean` |
| §7.4 (invariant-measure uniqueness) | ~~`invariant_measure_uniqueness`~~ REMOVED 2026-06-04; concrete content is the proved theorem `Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn` | `CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean` |
| §7.4 (rank-1 density uniqueness) | `rankOneDensity_unique_of_certainty` (theorem; discharged 2026-05-18) | `CsdLean4/LF2/BornWrapper.lean` |

## Paper D — LF3 (singlet kernel + LF1↔LF2↔LF3 empirical chain)

| Spec section | Lean reference | File |
|---|---|---|
| §2.5 (detector setting) | `DetectorSetting` | `CsdLean4/LF3/Setup.lean` |
| §2.7 (binary pointer projectors) | `BinaryPointerProjectors` | `CsdLean4/LF3/Setup.lean` |
| §2.7 (system-apparatus container) | `SystemApparatusSetup` | `CsdLean4/LF3/Setup.lean` |
| §2.8 (Pauli-layer identities) | `pauliDot_isHermitian`, `pauliDot_sq`, `spinProj_idem`, `spinProj_isHermitian`, `spinProj_complete` | `CsdLean4/LF3/Setup.lean` |
| §3.2 (impulsive readout) | `MeasurementUnitary.action` field | `CsdLean4/LF3/Hamiltonian.lean` |
| §3.4 (self-adjoint readout Hamiltonian) | `TensorFactorReadoutAlgebra` fields | `CsdLean4/LF3/Hamiltonian.lean` |
| §3.5 (Hamiltonian commutation) | `TensorFactorReadoutAlgebra.hAB_commute` | `CsdLean4/LF3/Hamiltonian.lean` |
| §3.6 (unitary factorisation) | `MeasurementUnitary.factorises` | `CsdLean4/LF3/Hamiltonian.lean` |
| §3.7 (eigenstate action) | `MeasurementUnitary.action` | `CsdLean4/LF3/Hamiltonian.lean` |
| §4.5 (branch decomposition) | `finalState_decomposition` (definitional) | `CsdLean4/LF3/BranchSeparation.lean` |
| §4.7 (per-side leakage bounds) | `PointerLeakageBounds` | `CsdLean4/LF3/BranchSeparation.lean` |
| §4.11 (geometric leakage bound) | `branch_separation_leakage_bound` (standalone; see disclosure note) | `CsdLean4/LF3/BranchSeparation.lean` |
| §5.10 (branchWeight, strong readout) | `branchWeight_strong_readout` | `CsdLean4/LF3/Projectors/BranchWeight.lean` |
| §5.10 (branchWeight, finite leakage) | `branchWeight_finite_leakage` | `CsdLean4/LF3/Projectors/BranchWeight.lean` |
| §5.11 (leakage compatibility) | `LeakageCompat` (structure; deviation bound is a field, not a theorem — see `AXIOMS.md §6.1`) | `CsdLean4/LF3/Projectors/BranchWeight.lean` |
| §5.14 (projector-algebra theorems) | `ProjectorAlgebra.idem_re_export` and field re-exports | `CsdLean4/LF3/Projectors/Core.lean` |
| §5.14 (LF3 → LF2 Born form) | `branchWeight_eq_LF2_Born` | `CsdLean4/LF3/Projectors/LF2Interface.lean` |
| §6 (Bell singlet) | `singlet`, `singlet_norm` | `CsdLean4/LF3/Singlet/State.lean` |
| §6.7 / §6.8 (Pauli expectations) | `singlet_left_pauli_expectation_zero`, `singlet_right_pauli_expectation_zero`, `singlet_pauli_correlation` | `CsdLean4/LF3/Singlet/Expectations.lean` |
| §6.9 (algebraic core) | `cst_squared_eq` | `CsdLean4/LF3/Singlet/Kernel.lean` |
| §6.10 (correlation, marginals) | `correlation_eq_neg_dot`, `marginal_a_eq_half`, `marginal_b_eq_half` | `CsdLean4/LF3/Singlet/Kernel.lean` |
| §6.11 (Born-form equivalence) | `cAmp_norm_sq_eq_inner_norm_sq`, `abstract_branchWeight_eq_P_st_at_singlet` | `CsdLean4/LF3/Singlet/Kernel.lean` |
| §7 (finite-leakage variants) | `singlet_pointer_probability_finite_leakage`, `correlation_finite_leakage_bound`, `marginal_a_finite_leakage_bound`, `marginal_b_finite_leakage_bound` | `CsdLean4/LF3/Singlet/Leakage.lean` |
| §7.10 (no-signalling) | `no_signalling_strong_readout_a`, `no_signalling_strong_readout_b` | `CsdLean4/LF3/Singlet/Kernel.lean` |
| §8 (measurement contexts) | `MeasurementContext`, `ContextIndexedOutcomeMaps`, `GlobalCHSHAssignment` | `CsdLean4/LF3/ContextMap.lean` |
| §8.7 (global CHSH assignment) | `GlobalCHSHAssignment` | `CsdLean4/LF3/ContextMap.lean` |
| §8.12 (context-form re-statements) | six context theorems (kernel, correlation, A/B marginals, A/B no-signalling) | `CsdLean4/LF3/ContextMap.lean` |
| §9.4 (Sign type) | `Sign`, `Sign.val` | `CsdLean4/LF3/Setup.lean` |
| §9.5 (operator exponential carve-out) | not formalised; field-level disclosure in `MeasurementUnitary.action` | `CsdLean4/LF3/Hamiltonian.lean` |
| §9.6 (branch decomposition) | `finalState_decomposition` (definitional) | `CsdLean4/LF3/BranchSeparation.lean` |
| §9.7 (ProjectorAlgebra / LeakageCompat as data) | `ProjectorAlgebra`, `LeakageCompat` (v1.00 carve-out; v2 derivation via `ProjectorAlgebra.ofTensorEmbedding`) | `CsdLean4/LF3/Projectors/{Core,BranchWeight,TensorModel}.lean` |
| §9.8 (algebraic core) | `P_st`, `cst_squared_eq` | `CsdLean4/LF3/Singlet/Kernel.lean` |
| §9.11 (self-adjointness convention) | inner-product-equation spelling throughout LF3 (see CONVENTIONS) | various |
| §9.13 (strong-readout main theorem) | `LF3_main_theorem` (8-conjunct) | `CsdLean4/LF3/Interface.lean` |
| §9.13 + §7 (finite-leakage theorem) | `LF3_finite_leakage_theorem` (4-conjunct) | `CsdLean4/LF3/Interface.lean` |
| §10.5 (LF1↔LF2↔LF3 empirical chain) | `LF3_singlet_frequency_convergence`, `LF3_singlet_frequency_convergence_born`, `LF3_singlet_frequency_convergence_born_inner` | `CsdLean4/LF3/Interface.lean` |

## Gaps and clarifications

**Spec sections without a Lean entry.** Paper §1 (motivation), §2.1 (programme background), and similar prose-only sections are not formalised individually. They are background for the formalised content rather than independent claims.

**Lean entries without a clean spec section.** A handful of helper lemmas (e.g. `outerProduct_isHermitian`, `outerProduct_posSemidef`) have no explicit spec reference because they are routine matrix-algebra facts the spec takes for granted. The README inventory and per-file docstrings remain authoritative for these.

**Conditional content.** The LF3 chain capstones (§10.5) consume `PureSingletPreparation.weight_eq_P_st` as a bundled hypothesis until LF4 supplies a structural constructor. The spec → Lean mapping records the headline theorem; the conditional-on-LF4 status is documented in `AXIOMS.md §6.2`.
