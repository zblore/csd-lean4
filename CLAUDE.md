# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the library (CsdLean4 target — LF1/LF2/LF3, no tests)
lake build

# Build the test target (AxiomAudit + Examples; required to fire #guard_msgs)
lake build CsdLeanTests

# Check a single file
lake env lean CsdLean4/LF1/MainTheorem.lean

# Update dependencies (after editing lakefile.lean)
lake update
```

The project uses **Lean 4.29.0-rc8** (see `lean-toolchain`) and depends on **Mathlib4**. There is no separate test runner — the Lean typechecker is the verification mechanism. A clean `lake build` plus a clean `lake build CsdLeanTests` with no errors and no `sorry`s constitutes a verified proof plus a green regression suite.

CI (`.github/workflows/ci.yml`) builds both targets on push to `main`/`master` and on all PRs. The library target uses `leanprover/lean-action@v1`; the test target is built with a direct `lake build CsdLeanTests` step.

## Architecture

This project formalizes **LF1: a deterministic repeated-trial frequency theorem** (Constraint-Surface Dynamics, Layer 1). The core claim: empirical frequencies of outcomes in deterministic repeated-trial experiments converge almost surely to ontic volume weights.

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

Future layers (LF2, LF4, …) become sibling directories `CsdLean4/LF2/`, each instantiating `OnticSetup`. New top-level modules must be added explicitly to `CsdLean4.lean` — that file is not glob-based.

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
Interface.lean     — lf1_weight_eq_projective_weight and its specialisation
                     to LF1's S.prepMeasure
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
- the **LF1↔LF2↔LF3 empirical chain capstones**
  `LF3_singlet_frequency_convergence` (pre-Born, landing on `(1 − st a·b)/4`)
  and `LF3_singlet_frequency_convergence_born` (Born-mediated, landing on
  `‖cAmp s t (a, b)‖²`).

LF3 module chain (under `CsdLean4/LF3/`, namespace `CSD.LF3`):

```
Setup.lean              — Sign, DetectorSetting, BinaryPointerProjectors,
                          SystemApparatusSetup, pauliDot, sigmaDotLeft/Right/Joint,
                          spinProj, jointSpinProj
Hamiltonian.lean        — TensorFactorReadoutAlgebra, MeasurementUnitary
                          (abstract factorisation + eigenstate-action fields)
BranchSeparation.lean   — branchState, finalState, pointerOverlapA/B,
                          wrongPointerReadoutMass, PointerLeakageBounds,
                          branch_separation_leakage_bound
Projectors/
  Core.lean             — ProjectorAlgebra, mHat, four field re-exports
  BranchWeight.lean     — branchWeight, StrongReadoutCompat, LeakageCompat,
                          branchWeight_strong_readout, branchWeight_finite_leakage
  LF2Interface.lean     — BasisIso, rankOneStateOfΨ, effectOfM,
                          trace_outerProduct_mul_eq_inner,
                          branchWeight_eq_LF2_Born
Singlet/
  State.lean            — singlet, singlet_norm, expectation
  Expectations.lean     — singlet_left/right_pauli_expectation_zero,
                          singlet_pauli_correlation,
                          expectation_formula (helper, fully proved)
  Kernel.lean           — dotR, P_st, cAmp (closed-form sqrt definition),
                          cst_squared_eq (algebraic core, derived from
                          closed-form cAmp), correlation_eq_neg_dot,
                          marginal_a/b_eq_half, no_signalling_strong_readout_a/b,
                          abstract_branchWeight_eq_P_st_at_singlet
  Leakage.lean          — singlet_pointer_probability_finite_leakage,
                          correlation_finite_leakage_bound,
                          marginal_a/b_finite_leakage_bound
ContextMap.lean         — MeasurementContext, ContextIndexedOutcomeMaps,
                          GlobalCHSHAssignment (definitional separation,
                          no Fine axiom), six context-form theorems
Interface.lean          — LF3_main_theorem (8-conjunct),
                          LF3_finite_leakage_theorem (4-conjunct),
                          LF3_singlet_frequency_convergence (pre-Born),
                          LF3_singlet_frequency_convergence_born (closed form),
                          LF3_singlet_frequency_convergence_born_inner
                            (genuine bra-ket form, takes eigenstate parameter)
```

**LF3 axiom inheritance.** `LF3_main_theorem` is fully axiom-clean (only
Mathlib foundational `propext`, `Classical.choice`, `Quot.sound`). The four
exported theorems do **not** invoke `busch_effect_gleason` or
`invariant_measure_uniqueness` — LF2's two axioms enter only through
`LF2.pure_state_born_weights_of_certainty`, which LF3 does not consume (the
singlet is concretely given as a Hilbert vector, not extracted from a Busch
package).

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
- The `LF1↔LF2↔LF3` chain capstone takes an external `hLF2` hypothesis
  relating `projectiveWeight (O_st s t) = ENNReal.ofReal (P_st ctx.a ctx.b s t)`.
  This is the LF4-todo §2 + §7 boundary (preparation ↔ Hilbert + projective-
  first outcomes); the LF3 capstone records the structural shape of the
  chain under that external hypothesis.

**LF3 is sorry-free.** All four capstone exports and every supporting lemma
are fully axiom-clean — `#print axioms` returns only `propext`,
`Classical.choice`, `Quot.sound` (the Mathlib foundational set). None of
LF2's two axioms (`busch_effect_gleason`, `invariant_measure_uniqueness`)
appear anywhere in the LF3 export.

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

### Planned future layers

LF1, LF2, and LF3 are in place. The README outlines LF4 (mixed states,
POVMs, reduction) and LF5 (outcome-conditioned update and sequential
circuits). Each future layer will instantiate `OnticSetup` (via
`SectorData.toOntic`) and consume `prepMeasure_apply` from LF1 plus
`measure_bridge` / `lf1_weight_eq_projective_weight` from LF2.

**LF4 TODO list:** concrete items deferred from LF2 (and now LF3) are
recorded in `specs/LF4-todo.md`. The hLF2 hypothesis on the LF3 empirical
chain capstone (preparation-to-Hilbert correspondence + projective-first
outcomes) discharges through items §2 and §7 there. Read that file before
starting LF4 work.

## Lean / Mathlib conventions

- `sorry`-free proofs are required; `lake build` failing or any `sorry` means the formalization is incomplete.
- Mathlib's `MeasureTheory` namespace is used throughout. Lean elaboration order matters — structure field order in `OnticSetup` and `TrialModel` is load-bearing.
- When adding new lemmas, place them in the module where their primary definition lives; keep the dependency chain linear (no circular imports).
- `hΩ0_nonzero : (μL : Measure SigmaSpace) Ω0 ≠ 0` is a hypothesis threaded through many definitions — it prevents division-by-zero in `prepMeasure` and is required wherever conditional measure values are rewritten.
- `hΦ_pres : MeasurePreserving Φ μL μL` (Liouville's theorem) is structural ontic input on `OnticSetup`, but inside LF1, LF2, and LF3 **only its measurability content is used** (extracted via `measurable_Φ`). Grep confirms no current proof in the corpus invokes the preservation content. The full property is carried for physical admissibility of the ontic model and becomes load-bearing only when LF4 derives `μL` from a concrete symplectic / Kähler volume form. Until then `hΦ_pres` is structural payload; the LF1 proof is strictly more general than the physical reading suggests. See the `OnticSetup` module docstring in `LF1/Setup.lean` for the honest disclosure.
- `SigmaSpace` in `OnticSetup` is an abstract `MeasurableSpace` — it is **not** specialised to `ℝ^{2n}`, a symplectic manifold, or any concrete phase space. Do not add assumptions that implicitly assume one; concrete instantiation is LF2's job.
