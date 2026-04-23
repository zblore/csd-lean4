# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the full project
lake build

# Check a single file
lake env lean CsdLean4/LF1/MainTheorem.lean

# Update dependencies (after editing lakefile.lean)
lake update
```

The project uses **Lean 4.29.0-rc8** (see `lean-toolchain`) and depends on **Mathlib4**. There is no separate test runner — the Lean typechecker is the verification mechanism. A clean `lake build` with no errors and no `sorry`s constitutes a verified proof.

CI (`.github/workflows/ci.yml`) runs `leanprover/lean-action@v1` with `build: true` on push to `main`/`master` and on all PRs.

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

Future layers (LF2, LF3, …) become sibling directories `CsdLean4/LF2/`, each instantiating `OnticSetup`. New top-level modules must be added explicitly to `CsdLean4.lean` — that file is not glob-based.

All definitions live under the `CSD.LF1` namespace, with sub-namespaces `OnticSetup` and `OnticSetup.TrialModel`. New lemmas should follow this pattern.

### Main theorem signature

```lean
theorem LF1_main_theorem_ae
    (T : S.TrialModel Ω)
    (O : S.OutcomeRegion)
    (hindep : Pairwise (IndepFun on (T.indicatorRV O ·))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto (T.empiricalFreq O · ω) atTop (nhds O.weightReal)
```

The only hypothesis the caller must supply is pairwise independence of trial indicators (`hindep`). Integrability and identical distribution are proved internally.

The theorem is deliberately stated for a **single** `O : OutcomeRegion` rather than a formalised partition family. The joint almost-sure statement for a finite measurable outcome partition `{Ω_i^Σ}` follows by applying the theorem once per element and intersecting the resulting full-measure sets. Do not refactor this into a partition type at the LF1 layer — the single-outcome form is intentional (see the docstring of `MainTheorem.lean`). A partition type may become necessary at LF2/LF3 for POVM completeness.

### Key infrastructure lemmas (used by future layers)

- `prepMeasure_apply` — explicit rewriting formula for the conditional measure (consumed by LF2/LF3)
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
axiom-and-sorry-free; LF2 has exactly three axioms:

- `invariant_measure_uniqueness` — invariant-measure uniqueness on the
  abstract projective target (concretely: SU(N)-invariant Borel probability
  measure on CP^{N-1} is unique). Spec-mandated (§7.4). Not in Mathlib.
- `busch_effect_gleason` — effect-additive probability on finite-dim
  operational packages admits a unique trace-form density operator.
  Spec-mandated (§7.4). Not in Mathlib.
- `rankOneDensity_unique_of_certainty` — a density operator that assigns
  probability one to a rank-1 projector `|ψ⟩⟨ψ|` is necessarily `|ψ⟩⟨ψ|`
  itself. Standard corollary of the spectral theorem; used to strengthen
  `pure_state_born_weights` so that the "OP is certain at ψ" hypothesis
  suffices to conclude `|⟨ψ|φ⟩|²`. Imported as an axiom pending Mathlib
  spectral-theorem integration (an LF3-scope task); the proof sketch is
  in the module docstring.

The first two are imported per the spec's explicit directive. The third is
an auxiliary matrix fact that makes `pure_state_born_weights_of_certainty`
work from a weaker purity hypothesis — without it, the pure-state endpoint
requires the caller to already know `OP.p E = traceForm (rankOneDensity ψ) E`
for every effect, which is almost the conclusion.

Everything else is proved. Notably, `born_quadratic` is a genuine Lean proof
(trace-of-outer-product identity + conjugate symmetry + `RCLike.mul_conj`),
not a narrative corollary.

**LF2 design choices:**

- `SectorData` is parametric in an abstract `(Sigma, P, G)`. The projective
  target `P` is **not** specialised to Mathlib's `Projectivization`; no
  Fubini–Study measure is constructed. Concrete instantiation is deferred to
  LF3+.
- `SectorData` carries **group-action coherence fields**
  (`onticAction_one`, `onticAction_mul`, `epAction_one`, `epAction_mul`)
  expressing the left-action laws for `onticAction` and `epAction`. LF2's
  own theorems don't consume them, but LF3 will when it uses
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
  over-constrains; covariance is type-heavy). Deferred to LF3; see
  `specs/LF3-todo.md` §1.
- `ComplexOrder` is opened scoped in `BornWrapper.lean` so that `ℂ` has the
  `PartialOrder` / `StarOrderedRing` instances required by `Matrix.PosSemidef`.

**Key infrastructure lemmas exported by LF2** (consumed by LF3+):

- `measure_bridge` — the central bridge theorem
- `lf1_weight_eq_projective_weight` — the LF1 ↔ LF2 hinge (measure identity)
- `LF1_main_theorem_projective` — the LF1 ↔ LF2 headline theorem: LF1
  frequency convergence, stated natively in projective form. This is the
  theorem-level consumption of LF1 by LF2 (not just structural)
- `outerProduct_posSemidef`, `one_sub_outerProduct_posSemidef` — projection
  lemmas useful wherever rank-1 effects appear downstream
- `born_quadratic` — the quadratic form in Lean; any LF3+ Born-weight
  consumer can cite it
- `pure_state_born_weights_of_certainty` — derives `|⟨ψ,φ⟩|²` from a
  purity hypothesis (`OP.p` is certain at `ψ`), routing through the
  Busch axiom + matrix uniqueness

### Planned future layers

LF1 and LF2 are in place. The README outlines LF3 (mixed states, POVMs,
reduction), LF4 (control Hamiltonians), and LF5 (outcome-conditioned update
and sequential circuits). Each future layer will instantiate `OnticSetup`
(via `SectorData.toOntic`) and consume `prepMeasure_apply` from LF1 plus
`measure_bridge` / `lf1_weight_eq_projective_weight` from LF2.

**LF3 TODO list:** concrete items deferred from LF2 are recorded in
`specs/LF3-todo.md` — unitary covariance clause, preparation-to-Hilbert
correspondence, rank-1 effects from projective points,
`rankOneDensity_unique_of_certainty` axiom discharge, σ-additivity check,
concrete `(Sigma, P, G)` instantiation, etc.  Read that file before
starting LF3 work.

## Lean / Mathlib conventions

- `sorry`-free proofs are required; `lake build` failing or any `sorry` means the formalization is incomplete.
- Mathlib's `MeasureTheory` namespace is used throughout. Lean elaboration order matters — structure field order in `OnticSetup` and `TrialModel` is load-bearing.
- When adding new lemmas, place them in the module where their primary definition lives; keep the dependency chain linear (no circular imports).
- `hΩ0_nonzero : (μL : Measure Sigma) Ω0 ≠ 0` is a hypothesis threaded through many definitions — it prevents division-by-zero in `prepMeasure` and is required wherever conditional measure values are rewritten.
- `hΦ_pres : MeasurePreserving Φ μL μL` (Liouville's theorem) is structural ontic input on `OnticSetup`, but inside LF1 **only its measurability content is used** (extracted via `measurable_Φ`). The full measure-preservation property is carried for physical admissibility and will be exercised in LF2+. Do not be surprised that LF1 proofs never invoke the preservation part directly.
- `Sigma` in `OnticSetup` is an abstract `MeasurableSpace` — it is **not** specialised to `ℝ^{2n}`, a symplectic manifold, or any concrete phase space. Do not add assumptions that implicitly assume one; concrete instantiation is LF2's job.
