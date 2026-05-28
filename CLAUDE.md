# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the library (CsdLean4 target — LF1/LF2/LF3/LF4/Empirical/Mathlib, no tests)
lake build

# Build the test target (AxiomAudit + Examples; required to fire #guard_msgs)
lake build CsdLeanTests

# Check a single file
lake env lean CsdLean4/LF1/MainTheorem.lean

# Update dependencies (after editing lakefile.toml)
lake update
```

The build configuration lives in `lakefile.toml` (not `lakefile.lean`); Mathlib
is pinned by `rev` there, bumped in lockstep with `lean-toolchain`.

The project uses **Lean 4.29.0-rc8** (see `lean-toolchain`) and depends on **Mathlib4**. There is no separate test runner — the Lean typechecker is the verification mechanism. A clean `lake build` plus a clean `lake build CsdLeanTests` with no errors and no `sorry`s constitutes a verified proof plus a green regression suite.

CI (`.github/workflows/ci.yml`) builds both targets on push to `main`/`master` and on all PRs. The library target uses `leanprover/lean-action@v1`; the test target is built with a direct `lake build CsdLeanTests` step.

## Architecture

This project formalizes **Constraint-Surface Dynamics (CSD)** as a linear stack
of layers. **LF1** (deterministic repeated-trial frequency theorem), **LF2**
(sector-conditional measure bridge + Born-weight wrapper), **LF3** (singlet
kernel + the LF1↔LF2↔LF3 empirical chain), and **LF4 §14.2** (observable
correspondence + Robertson uncertainty on a concrete compact-Kähler instance)
are all merged and machine-verified, alongside an **Empirical** QM-validity
regression suite. The LF1 core claim: empirical frequencies of outcomes in
deterministic repeated-trial experiments converge almost surely to ontic volume
weights. Each higher layer instantiates / consumes the previous (LF2's
`SectorData.toOntic` produces an LF1 `OnticSetup`; LF4 instantiates `SectorData`
on `ℂℙ^{M-1} × T²`).

The detailed per-layer architecture for LF1, LF2, and LF3 follows; LF4 and
Empirical are summarised at the end. The README is the current authoritative
status overview; this file is the working-with-the-code guide.

### Key design choice: determinism

Probability enters only through **repeated-preparation sampling** — each trial draws a new initial microstate from a conditional measure on a preparation region Ω₀. The ontic evolution Φ is a deterministic measure-preserving flow. There is no intrinsic randomness at the ontic level.

### Module dependency chain (linear, each imports the previous)

```
Setup.lean          — OnticSetup: measurable space Σ, Liouville measure μL,
                      deterministic flow Φ, preparation region Ω₀
Preparation.lean    — prepMeasure: conditional measure μprep(A) = μL(A ∩ Ω₀) / μL(Ω₀)
Outcomes.lean       — OutcomeRegion: measurable subsets, preEvent pullbacks, weight
Trials.lean         — TrialModel: i.i.d. preparation sampling, repeated-trial space
Indicators.lean     — indicatorRV, empiricalFreq (Bernoulli 0/1 per trial)
Expectation.lean    — Bridge: E[indicatorRV O n] = O.weightReal
Convergence.lean    — Applies Mathlib's strong law of large numbers
MainTheorem.lean    — LF1_main_theorem_ae and corollaries
```

`CsdLean4.lean` (the root file) is the canonical top-level import — it lists every module explicitly. `CsdLean4/Basic.lean` is the conventional `Pkg.Basic` convenience re-export that transitively pulls in the chain via `MainTheorem`. Downstream layers and external consumers should `import CsdLean4.Basic`; edits inside the package should modify the explicit list in `CsdLean4.lean`.

Higher layers are sibling directories (`CsdLean4/LF2/`, `LF3/`, `LF4/`, `Empirical/`, `Mathlib/`), each instantiating or consuming the previous. New top-level modules must be added explicitly to `CsdLean4.lean` — that file is not glob-based.

All definitions live under the `CSD.LF1` namespace, with sub-namespaces `OnticSetup` and `OnticSetup.TrialModel`. New lemmas should follow this pattern.

### Main theorem signature

```lean
theorem LF1_main_theorem_ae
    (T : S.TrialModel Ω)
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g T.trialMeasure)
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto (T.empiricalFreq O · ω) atTop (nhds O.weightReal)
```

The only hypothesis the caller must supply is pairwise independence of trial indicators (`hindep`). Integrability and identical distribution are proved internally. The `Function.onFun` wrapping is the standard Mathlib spelling for `Pairwise` applied to a binary relation `IndepFun · · μ` lifted along the indexing `n ↦ T.indicatorRV O n`; no CSD-namespace abbreviation is introduced.

The theorem is deliberately stated for a **single** `O : OutcomeRegion` rather than a formalised partition family. The joint almost-sure statement for a finite measurable outcome partition `{Ω_i^Σ}` follows by applying the theorem once per element and intersecting the resulting full-measure sets. Do not refactor this into a partition type at the LF1 layer — the single-outcome form is intentional (see the docstring of `MainTheorem.lean`). A partition type may become necessary at LF2/LF4 for POVM completeness.

### Key infrastructure lemmas (used by future layers)

- `prepMeasure_apply` — explicit rewriting formula for the conditional measure (consumed by LF2/LF4)
- `weight_eq_prepEvent_div` — volume interpretation of weights
- `trialEvent_eq_comp_preimage` — makes deterministic structure explicit
- `indicatorRV_integrable`, `indicatorRV_identDistrib` — prerequisites for the strong law

### LF2: measure bridge and Born-weight wrapper

LF2 sits directly on top of LF1 and delivers:

- the sector-conditional **measure bridge** `π*μL = c • μFS` connecting ontic
  Liouville volume to an abstract projective reference measure;
- the **Born-weight wrapper** packaging finite-dimensional probability under
  an explicit operational consistency package (spec Definition 5.1);
- the **proved Born quadratic form** `wᵢ = ‖⟨ψ, φᵢ⟩‖²` for rank-1 outcomes on
  pure preparations;
- the **LF1 ↔ LF2 weight identity** linking `μprep(π⁻¹(O))` to
  `(π*μprep)(O)`, so `LF1_main_theorem_ae` consumers can reinterpret the
  limiting ontic weight as a projective weight.

LF2 module chain (under `CsdLean4/LF2/`, namespace `CSD.LF2`):

```
Setup.lean         — SectorData: LF1 OnticSetup + measurable π : Σ → P +
                     G-action with μL-invariance and π-equivariance
MeasureBridge.lean — π*μL, preimage_action_eq (Lemma 1),
                     pushforward_epAction_invariant (Lemma 2),
                     invariant_measure_uniqueness AXIOM, measure_bridge
Weights.lean       — MeasurablePartition, projectiveWeight,
                     weights_sum_eq_one (normalisation)
BornWrapper.lean   — concrete Effect / DensityOperator (N×N complex matrices),
                     traceForm, Effect.one / .zero / .add helpers,
                     outerProduct + all projection lemmas,
                     rankOneEffect / rankOneDensity, OperationalPackage,
                     busch_effect_gleason AXIOM, born_form_of_package,
                     born_quadratic (proved), pure_state_born_weights
PhaseInvariance.lean — outerProduct_phase_invariant, rankOneEffect /
                     rankOneDensity phase invariance under unit-modulus
                     scalar action (pre-LF4 Phase 1)
EffectFn.lean      — effectProjFn (volume-ratio projective effect function:
                     RCLike.re (star v ⬝ᵥ E.M *ᵥ v) where v = (rep p).ofLp),
                     measurability + integrability + Born rank-1 identity
                     effectProjFn_rankOne (pre-LF4 Phase 2)
Preparation.lean   — MeasureBridgeData structure + ofSectorData constructor
                     citing invariant_measure_uniqueness;
                     OperationalPackage.fromPreparation (volume-ratio Born
                     wrapper from a preparation measure);
                     PurePreparation structure (ψ + rep + Dirac
                     concentration) + OP_certain_at_ψ + born_rank_one
                     (Busch-mediated) + born_rank_one_direct (volume-ratio
                     auxiliary, no Busch) (pre-LF4 Phases 3-4)
Interface.lean     — lf1_weight_eq_projective_weight, LF1_main_theorem_projective,
                     SectorData.outcomeOfProjective (Phase 5)
```

**LF2 is the first layer with `axiom` declarations.** LF1 is
axiom-and-sorry-free; LF2 has exactly two axioms:

- `invariant_measure_uniqueness` — invariant-measure uniqueness on the
  abstract projective target (concretely: SU(N)-invariant Borel probability
  measure on CP^{N-1} is unique). Spec-mandated (§7.4). Not in Mathlib.
- `busch_effect_gleason` — effect-additive probability on finite-dim
  operational packages admits a unique trace-form density operator.
  Spec-mandated (§7.4). Not in Mathlib.

Both are imported per the spec's explicit directive.

`rankOneDensity_unique_of_certainty` was carried as a third axiom in earlier
revisions (a density operator that assigns probability one to `|ψ⟩⟨ψ|` is
`|ψ⟩⟨ψ|` itself); it is now a proved theorem (discharged 2026-05-18). The
proof routes through `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: the
sandwich `(I−P) ρ (I−P)` is PSD with trace zero (by trace cyclicity and the
certainty hypothesis), hence zero; so `ρ · (I−P) = 0` and thus `ρ = P ρ P`.
The rank-1 sandwich identity `P · M · P = Tr(M · P) • P` then collapses ρ
to `1 • P = P`. Used to strengthen `pure_state_born_weights` so that the "OP
is certain at ψ" hypothesis suffices to conclude `|⟨ψ|φ⟩|²` — without it,
the pure-state endpoint requires the caller to already know `OP.p E =
traceForm (rankOneDensity ψ) E` for every effect, which is almost the
conclusion.

Everything else is proved. Notably, `born_quadratic` is a genuine Lean proof
(trace-of-outer-product identity + conjugate symmetry + `RCLike.mul_conj`),
not a narrative corollary.

**LF2 design choices:**

- `SectorData` is parametric in an abstract `(SigmaSpace, P, G)`. The projective
  target `P` is **not** specialised to Mathlib's `Projectivization`; no
  Fubini–Study measure is constructed. Concrete instantiation is deferred to
  LF4+.
- `SectorData` carries **group-action coherence fields**
  (`onticAction_one`, `onticAction_mul`, `epAction_one`, `epAction_mul`)
  expressing the left-action laws for `onticAction` and `epAction`. LF2's
  own theorems don't consume them, but LF4 will when it uses
  transitivity / orbits / Haar measure.
- The reference measure `μFS` is **not** a field of `SectorData`; it enters
  `measure_bridge` as an explicit argument, keeping `SectorData`
  `μFS`-agnostic.
- `Effect` and `DensityOperator` are concrete `Matrix (Fin N) (Fin N) ℂ`
  structures (not opaque stubs). This gives real Lean content to the Born
  quadratic form.
- `Effect.add` takes the `le_one` hypothesis (`1 - (E.M + F.M)).PosSemidef`)
  as an explicit argument — no `Option`-valued addition, no
  `Decidable (PosSemidef _)` required.
- `Effect.conjugateBy (U : Matrix.unitaryGroup (Fin N) ℂ)` returns `U† E U`
  as an `Effect`. This is the structural helper for spec Def 5.1 clause 3
  (unitary covariance), but the clause itself is **not** a field on
  `OperationalPackage` — both natural readings have issues (invariance
  over-constrains; covariance is type-heavy). Deferred to LF4; see
  `specs/LF4-todo.md` §1.
- `ComplexOrder` is opened scoped in `BornWrapper.lean` so that `ℂ` has the
  `PartialOrder` / `StarOrderedRing` instances required by `Matrix.PosSemidef`.

**Key infrastructure lemmas exported by LF2** (consumed by LF4+):

- `measure_bridge` — the central bridge theorem
- `lf1_weight_eq_projective_weight` — the LF1 ↔ LF2 hinge (measure identity)
- `LF1_main_theorem_projective` — the LF1 ↔ LF2 headline theorem: LF1
  frequency convergence, stated natively in projective form. This is the
  theorem-level consumption of LF1 by LF2 (not just structural)
- `outerProduct_posSemidef`, `one_sub_outerProduct_posSemidef` — projection
  lemmas useful wherever rank-1 effects appear downstream
- `born_quadratic` — the quadratic form in Lean; any LF4+ Born-weight
  consumer can cite it
- `pure_state_born_weights_of_certainty` — derives `|⟨ψ,φ⟩|²` from a
  purity hypothesis (`OP.p` is certain at `ψ`), routing through the
  Busch axiom + matrix uniqueness

### LF3: singlet kernel and the LF1↔LF2↔LF3 empirical chain

LF3 sits on top of LF2 and delivers:

- the **singlet kernel** `P_{st}(a, b) = (1 − st·a·b)/4` and its operational
  consequences (correlation `−a·b`, marginals `1/2`, no-signalling on each
  side, pointer-completeness);
- the **finite-leakage stability** of all four quantities, parameterised by
  per-side leakage parameters `εA`, `εB`;
- the **LF1↔LF2↔LF3 empirical chain capstones**, three per-sector +
  three joint-partition variants (Phase 8):
  `LF3_singlet_frequency_convergence` (pre-Born, landing on `(1 − st a·b)/4`),
  `LF3_singlet_frequency_convergence_born` (closed-form Born, `‖cAmp‖²`),
  `LF3_singlet_frequency_convergence_born_inner` (bra-ket Born), plus
  `..._joint`, `..._born_joint`, `..._born_inner_joint` (joint AE over
  the Sign × Sign partition).

LF3 module chain (under `CsdLean4/LF3/`, namespace `CSD.LF3`):

```
Setup.lean              — Sign, DetectorSetting, BinaryPointerProjectors,
                          SystemApparatusSetup, pauliDot, sigmaDotLeft/Right/Joint,
                          spinProj, jointSpinProj
Hamiltonian.lean        — TensorFactorReadoutAlgebra, MeasurementUnitary
                          (abstract factorisation + eigenstate-action fields)
SectorSeparation.lean   — sectorState, finalState, pointerOverlapA/B,
                          crossSectorReadoutMass, PointerLeakageBounds,
                          sector_separation_leakage_bound
Projectors/
  Core.lean             — ProjectorAlgebra, mHat, four field re-exports
  SectorVolume.lean     — sectorVolume, StrongReadoutCompat, LeakageCompat,
                          sectorVolume_strong_readout, sectorVolume_finite_leakage
  LF2Interface.lean     — BasisIso, rankOneStateOfΨ, effectOfM,
                          trace_outerProduct_mul_eq_inner,
                          sectorVolume_eq_LF2_Born
Singlet/
  State.lean            — singlet, singlet_norm, expectation
  Expectations.lean     — singlet_left/right_pauli_expectation_zero,
                          singlet_pauli_correlation,
                          expectation_formula (helper, fully proved)
  Kernel.lean           — dotR, P_st, cAmp (closed-form sqrt definition),
                          cst_squared_eq (algebraic core, derived from
                          closed-form cAmp), correlation_eq_neg_dot,
                          marginal_a/b_eq_half, no_signalling_strong_readout_a/b,
                          abstract_sectorVolume_eq_P_st_at_singlet
  Leakage.lean          — singlet_pointer_probability_finite_leakage,
                          correlation_finite_leakage_bound,
                          marginal_a/b_finite_leakage_bound
ContextMap.lean         — MeasurementContext, ContextIndexedOutcomeMaps,
                          GlobalCHSHAssignment (definitional separation,
                          no Fine axiom), six context-form theorems
SingletProjective.lean  — MeasurementJointEig (joint spin eigenstate
                          bundle with Born identity), SingletProjectiveOutcome
                          (rep-preimage projective region), measurability,
                          disjointness, OP_p_at_jointEig_eq_P_st
                          (Busch-mediated) + _direct variant (Phase 6)
PurePreparation.lean    — PureSingletPreparation bundle (option (B),
                          posited-fibre-measure form 2026-05-25):
                          μψ (posited fibre trial law) + μFS + bridge +
                          PP (over μψ) + jed + O_region + bridge_op_p
                          (LF4 discharge target), weight_eq_P_st convenience
                          theorem (Phase 7)
Interface.lean          — LF3_main_theorem (8-conjunct),
                          LF3_finite_leakage_theorem (4-conjunct),
                          three per-sector chain capstones
                          (LF3_singlet_frequency_convergence /
                          _born / _born_inner) plus three joint-partition
                          variants (Phase 8 _joint suffixes)
```

**LF3 axiom inheritance (post Phase 7 rewrite, 2026-05-18).**
`LF3_main_theorem` and `LF3_finite_leakage_theorem` are fully axiom-clean
(only the Mathlib foundational triple). The six chain capstones (three
per-sector + three joint variants) cite the foundational triple **plus**
`busch_effect_gleason`: the chain bridge now routes via OP.p (option (B)
chain design — see `specs/pre-LF4-plan.md`), and the OP.p Born identity
extensionally invokes `LF2.pure_state_born_weights_of_certainty` which
cites Busch. `invariant_measure_uniqueness` enters at LF4 instantiation
sites that build `MeasureBridgeData` via `MeasureBridgeData.ofSectorData`
(option (b) structural propagation) — not extensionally on the chain
capstones themselves. This is the spec §5.4 four-ingredient
combinatorial framing realised at the Lean level.

**LF3 design choices:**

- `Sign` is a two-element inductive `| plus | minus` (spec §9.4).
- The two-qubit factor `HAB` is `EuclideanSpace ℂ (Fin 2 × Fin 2)`
  (matching the `Fin 2 × Fin 2` indexing on `pauliDot ⊗ pauliDot`).
- `MeasurementUnitary` carries the full and per-wing unitaries as
  `LinearIsometryEquiv` (Mathlib idiom); unitarity is encoded in the type.
- Self-adjointness on continuous linear maps is stated via the inner-product
  equation `∀ x y, inner ℂ (T x) y = inner ℂ x (T y)` to avoid `Star`
  typeclass synthesis on `H_SA →L[ℂ] H_SA`.
- `cAmp` is defined in **closed form** as `(Real.sqrt (P_st a b s t) : ℂ)`.
  This sidesteps the explicit construction of joint spin eigenstates;
  downstream theorems consume only `‖cAmp‖²`, so a future swap to
  `cAmp := inner ℂ jointSpinEig singlet` is transparent. The bra-ket
  equivalence is exposed via `cAmp_norm_sq_eq_inner_norm_sq` (under a
  rank-1 projector hypothesis) and via the
  `LF3_singlet_frequency_convergence_born_inner` capstone variant.
- The `LF1↔LF2↔LF3` chain capstones consume a `PureSingletPreparation D ctx N`
  bundle whose load-bearing hypotheses are the option (B) split:
  `MeasurementJointEig.born_eq_P_st : ‖⟨ψ, eig s t⟩‖² = P_st` (the Born
  identity for the joint spin eigenstate, LF4-todo §3 discharge target)
  and `PureSingletPreparation.bridge_op_p : μψ(preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (eig s t)))`
  (the ontic-weight ↔ OP.p bridge, LF4-todo §2 + §7 discharge target).
  The bundle's `weight_eq_P_st` theorem composes the two via
  `LF3.OP_p_at_jointEig_eq_P_st` (Phase 6) which cites
  `LF2.PurePreparation.born_rank_one` (which cites Busch). **The
  preparation primitive is a posited fibre trial law `μψ`, not the ambient
  `μL`-conditional `prepMeasure`** (posited-fibre-measure migration,
  2026-05-25): under the continuous measure bridge `π∗μL = c·μFS` every
  state's fibre is `μL`-null, so a `μL`-conditional pure preparation is
  uninhabitable. The capstones take i.i.d. trials with common law `μψ` and
  route through `LF1.freq_tendsto_of_iid` (not `LF1_main_theorem_ae`). See
  `LF4-todo §8`.

**LF3 is sorry-free.** All capstone exports and supporting lemmas are
sorry-free. The chain capstones cite `propext, Classical.choice,
Quot.sound, busch_effect_gleason` per the post-Phase-7 option (B) form;
`LF3_main_theorem` and `LF3_finite_leakage_theorem` remain axiom-clean.

**LF3 self-adjointness convention.** `BinaryPointerProjectors`,
`TensorFactorReadoutAlgebra`, `ProjectorAlgebra`, and `mHat_isSelfAdjoint`
state self-adjointness via the inner-product equation
`∀ x y, inner ℂ (T x) y = inner ℂ x (T y)` rather than Mathlib's
`IsSelfAdjoint T` predicate. This deviates from idiom but is forced: the
`Star (H →L[ℂ] H)` typeclass synthesis on a finite-dim complex inner-product
space fails even with `Mathlib.Analysis.InnerProductSpace.Adjoint` imported
(the adjoint construction needs full completeness boilerplate Mathlib
doesn't synthesise for our `[NormedAddCommGroup H] [InnerProductSpace ℂ H]
[FiniteDimensional ℂ H]` setup). The inner-product spelling is
mathematically equivalent and avoids the synthesis dead-end.

### LF4: concrete compact-Kähler instance and §14.2 observable correspondence

LF4 is the layer where the abstract `SectorData` framework acquires a concrete
inhabitant and projective objects acquire ontic content. It instantiates
`SectorData` on a genuinely compact-Kähler `Σ` and discharges the
observable-correspondence target (spec §14.2).

LF4 module chain (under `CsdLean4/LF4/`, namespace `CSD.LF4`):

```
Instance.lean          — cpSectorData: first concrete SectorData (Σ = P =
                         ℂℙ^{N-1}, G = U(N), π = id, μL = fubiniStudyMeasure);
                         cp_measure_bridge (axiom-free for the instance).
                         Honest scope: π = id ⇒ point fibres, c = 1, no Born
                         prediction reproduced (base case proving the framework
                         is inhabited)
KahlerInstance.lean    — kSectorData on KSigma M = ℂℙ^{M-1} × T² with
                         kMuL = fubiniStudyMeasure ⊗ vol_T²; k_measure_bridge
                         (c = 1, axiom-free marginal bridge). First
                         non-trivial-fibre, genuinely compact-Kähler SectorData
SingletKahler.lean     — ofKählerPreparation: concrete LF3 PureSingletPreparation
                         for the singlet on KSigma; bridge_op_p proved Busch-free
                         via fibre-arc carving (see Tier-2 note below)
SingleQubitKahler.lean — Stern-Gerlach single-qubit carving + capstone;
                         zPlus_expectation and Pauli-on-|0⟩ shortcuts
SingletObservables,
HardyKahler           — N=4 two-qubit Pauli correspondences; Hardy lift
SpectralExpansion.lean — hermitian_inner_spectral_expansion:
                         ⟨ψ,Aψ⟩ = ∑ᵢ λᵢ‖⟨uᵢ,ψ⟩‖² for any Hermitian N×N (Hilbert
                         side; genuine Parseval + spectral content)
SpectralCarving.lean   — fibreShiftedArc, cumWeights, spectralRegion (genuinely
                         disjoint N-arc fibre partition) + integral headline
                         ∫ spectralOntic dμψ = re⟨ψ,Aψ⟩ (ontic side)
SpectralVariance.lean  — spectralVariance + ∫ spectralOnticCentered = ‖Aψ‖²−⟨A⟩²
UncertaintyKahler.lean — kahler_robertson_ontic_variance (ontic-side LHS Robertson)
PauliRobertson.lean    — pauli_xy_robertson_saturation (σx,σy on |0⟩, both = 1)
PauliDotRobertson.lean — pauliDot_robertson_zPlus (parametric over unit axes)
OnticBorn.lean         — ontic_born_frequency (general pure-state ontic Born
                         capstone via freq_tendsto_of_iid + Busch)
```

**§14.2 is closed.** The observable-correspondence chain (six commits,
`eeec1e8`→`c5eed61`) is fully verified, foundational-triple-only on every pin,
with two concrete Robertson witnesses.

**Tier-2 honesty (load-bearing).** Every LF4 result that lands on a specific
Born weight does so on a fibre partition **carved by construction** to that
value: `kMuPsi_kRegion` makes `fibreArc (P_st)` have volume `P_st`;
`spectralRegion` is cut to length `‖⟨uᵢ,ψ⟩‖²`. So `bridge_op_p` and
`diracProd_spectralRegion` are *proved* but realise the Born value rather than
*derive* it. The genuine content is (a) the partition is genuinely disjoint, and
(b) the ontic Lebesgue-integral route and the Hilbert Parseval route meet at the
same number through structurally distinct machinery. **`Φ := id` in every
concrete `SectorData`** — no dynamics is exercised (structural debt D1, wide
open). LF4 is a faithful *realisation* on a compact-Kähler Σ, not a *derivation*
of quantum weights from deterministic dynamics. Say which side of that line any
new result sits on.

### Empirical: QM-validity regression suite

Under `CsdLean4/Empirical/`, namespace `Empirical`. Two branches:

- `Empirical/QM/` — pure QM-validity content (inner-product geometry, no CSD
  ontology). Bell/CHSH at Tsirelson, no-cloning (Wootters-Zurek + Dieks),
  no-deleting (Pati-Braunstein), superdense coding, quantum money, Stern-Gerlach,
  uncertainty, Kochen-Specker (Cabello-18), Mermin-Peres, GHZ, Hardy, and
  single/two/multi-qubit gates. Every theorem foundational-triple-only and
  AxiomAudit-pinned.
- `Empirical/CSD/` — CSD volume-ratio readings: transport each QM-validity
  statement through a `CSDBridge.Context D` bundle carrying the LF2 `SectorData`
  + measure-bridge data, providing the structural slot for the CSD-ontic
  interpretation. Several bundles carry load-bearing undischarged realisability
  fields (`bridge_isometry`, observable-correspondence; LF4-todo §13/§14) marked
  with `Status: load-bearing, externally supplied, undischarged`.

### `Mathlib/` staging tree

`CsdLean4/Mathlib/` holds Cat-1 (CSD-free) helpers staged as Mathlib upstream
candidates — `Projectivization` topology/measure/lift API and the
`UnitaryGroup` / Fubini-Study uniqueness chain (which gives the axiom-free
concrete realisation `invariant_measure_uniqueness_cpn`). These files keep the
**natural Mathlib namespace** (`namespace Projectivization`, `namespace Matrix`),
not a CSD wrapper; the `CsdLean4/Mathlib/<path>/` location is the only staging
signal (CONVENTIONS.md §1 Cat-1).

**LF4 TODO list:** items deferred from LF2 / LF3 to LF4 are recorded in
`specs/LF4-todo.md` (§14.2 now closed; §13 isometry realisability, §8 additional
preparation classes, §1-§11 remaining). The LF3 chain bundle hypotheses
(`MeasurementJointEig.born_eq_P_st`, `PureSingletPreparation.bridge_op_p`)
discharge through items §2, §3, §7. Read that file before starting LF4 work; the
pre-LF4 plan and execution log live at `specs/pre-LF4-plan.md`.

## Lean / Mathlib conventions

- `sorry`-free proofs are required; `lake build` failing or any `sorry` means the formalization is incomplete.
- Mathlib's `MeasureTheory` namespace is used throughout. Lean elaboration order matters — structure field order in `OnticSetup` and `TrialModel` is load-bearing.
- When adding new lemmas, place them in the module where their primary definition lives; keep the dependency chain linear (no circular imports).
- `hΩ0_nonzero : (μL : Measure SigmaSpace) Ω0 ≠ 0` is a hypothesis threaded through many definitions — it prevents division-by-zero in `prepMeasure` and is required wherever conditional measure values are rewritten.
- `hΦ_pres : MeasurePreserving Φ μL μL` (Liouville's theorem) is structural ontic input on `OnticSetup`, but inside LF1, LF2, and LF3 **only its measurability content is used** (extracted via `measurable_Φ`). Grep confirms no current proof in the corpus invokes the preservation content. The full property is carried for physical admissibility of the ontic model and becomes load-bearing only when LF4 derives `μL` from a concrete symplectic / Kähler volume form. Until then `hΦ_pres` is structural payload; the LF1 proof is strictly more general than the physical reading suggests. See the `OnticSetup` module docstring in `LF1/Setup.lean` for the honest disclosure.
- `SigmaSpace` in `OnticSetup` is an abstract `MeasurableSpace` — it is **not** specialised to `ℝ^{2n}`, a symplectic manifold, or any concrete phase space. Do not add assumptions that implicitly assume one; concrete instantiation is LF4's job (LF2 keeps `SigmaSpace`/`P`/`G` abstract; `LF4/KahlerInstance.lean` provides the concrete `ℂℙ^{M-1} × T²`).
