# csd-lean4

[![CI](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml)

Lean 4 formalisation of Constraint-Surface Dynamics. **LF1**, **LF2**, **LF3**, and **LF4 §14.2** (the observable-correspondence layer — Hilbert spectral expansion, ontic-side multi-region carving, ontic ↔ Hilbert variance correspondence, and Robertson uncertainty at the ontic-integration level, including two concrete witnesses) are merged and machine-verified. An **Empirical** module provides the QM-validity regression suite (Bell family, no-cloning, no-deleting, Uncertainty, Stern-Gerlach, superdense coding, quantum money, contextuality, Hardy, GHZ, gates).

**Notable result (the Born rule as a Kähler volume ratio).** A new LF4 module cluster derives the Born weight `‖⟨eᵢ, ψ⟩‖²` from the Fubini–Study Kähler geometry — as the **torus moment-map coordinate** (`momentMap_mk_eq_inner_sq`), as a **barycentric Lebesgue-volume ratio** (`born_eq_volume_ratio`, general `N`), and for the qubit as a **genuine `fubiniStudyMeasure` volume ratio on the ontic `Σ = ℂℙ¹`** (`fs_born_volume_ratio_qubit`). This yields a **Busch-free empirical chain** `qubit_born_frequency_convergence`: deterministic repeated-trial typicality (LF1) + Born = Fubini–Study volume ratio ⟹ frequencies converge a.s. to the Born weight, with the Born value *derived from the Kähler volume* rather than imported via Gleason/Busch. This is a foundational strengthening (where the Born numbers come from), upstream of the Empirical suite; it is **not** an empirical-parity result. Conditional on one explicit, classically-true hypothesis `h_uniform` (the `N=2` Duistermaat–Heckman fact, deferred — see [`specs/carve-out-plan.md`](specs/carve-out-plan.md)).

The repo is sorry-free and `lake build CsdLeanTests` green (3044 jobs at this writing). Axiom posture is the foundational Lean triple + two spec-mandated Mathlib-external axioms (`invariant_measure_uniqueness`, `busch_effect_gleason`). See [`AXIOMS.md`](AXIOMS.md) for the per-theorem ledger and [`specs/LF4-todo.md`](specs/LF4-todo.md) for the LF4 backlog.

## What's machine-verified

| Layer | Headline | Carving | Axioms beyond foundational triple |
|---|---|---|---|
| **LF4 Born-from-volume** | Born weight `‖⟨eᵢ,ψ⟩‖²` = torus moment-map coordinate (`momentMap_mk_eq_inner_sq`) = barycentric volume ratio (`born_eq_volume_ratio`, general `N`) = genuine FS-volume ratio on `Σ=ℂℙ¹` (`fs_born_volume_ratio_qubit`); Busch-free empirical chain `qubit_born_frequency_convergence` (frequencies → Born via the Kähler volume) | **No carving** — geometric regions (moment sublevel / barycentric sub-simplex); Born value derived, not cut to fit. Qubit on-`Σ` + empirical chain conditional on `h_uniform` (`N=2` Duistermaat–Heckman, deferred plan B) | none (`h_uniform` is a hypothesis, **not** `busch_effect_gleason`) |
| **LF4 §14.2** | `kahler_robertson_ontic_variance` — Robertson bound on ontic-side integrals for any Hermitian observables on `EuclideanSpace ℂ (Fin N)`, with concrete witnesses `pauli_xy_robertson_saturation` (saturation at \|0⟩) and `pauliDot_robertson_zPlus` (parametric over axes) | Compact Kähler `KSigma M = ℂℙ^{M-1} × T²`; N-arc fibre partition via `spectralRegion`; integration headline `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²` | none |
| **LF3** | Singlet kernel `P_st = (1 − st a·b)/4`; LF1↔LF2↔LF3 chain capstones (6 variants); finite-leakage stability | Posited fibre law `μψ` (option (B) chain design, post-Phase-7) | `busch_effect_gleason` (chain capstones only) |
| **LF2** | `measure_bridge` (`π∗μL = c·μFS`); `born_quadratic` (`Tr(\|ψ⟩⟨ψ\|·\|φ⟩⟨φ\|) = ‖⟨ψ,φ⟩‖²`); `pure_state_born_weights_of_certainty`; `LF1_main_theorem_projective` | Abstract projective target `P` (concrete instantiation deferred to LF4 §8) | `invariant_measure_uniqueness`; `busch_effect_gleason` (purity-form Born only) |
| **LF1** | `LF1_main_theorem_ae` — empirical frequencies converge a.s. to ontic weight under deterministic flow + pairwise-independent i.i.d. preparation | Abstract measurable `SigmaSpace` (no symplectic / Kähler structure assumed) | none |
| **Empirical** | Bell + No-cloning + No-deleting + Uncertainty + Stern-Gerlach + Superdense coding + Quantum money + Mermin-Peres + Hardy + GHZ + Single/Two/Multi-qubit gates (Phases A1-A6, B1-B5, C1-C3, D-gates) | Two-layer: QM-validity (inner-product geometry) + CSD-side (transport bundles for the same predictions) | foundational triple only on every Empirical pin |

Every theorem listed is AxiomAudit-pinned via `#guard_msgs` in `CsdLean4/Tests/AxiomAudit.lean`; the build fails on axiom drift.

## Quick start

```bash
# Library (LF1+LF2+LF3+LF4+Empirical, no tests):
lake build

# Tests target (AxiomAudit pins + Examples):
lake build CsdLeanTests

# Type-check a single file:
lake env lean CsdLean4/LF4/PauliDotRobertson.lean
```

Toolchain: Lean 4.29.0-rc8 (see `lean-toolchain`); Mathlib4. CI builds both targets on every push to `main` and on PRs.

The canonical top-level import is `CsdLean4` (explicit module list — not glob). For downstream consumers `import CsdLean4.Basic` transitively pulls in the LF1 → LF2 → LF3 → LF4 → Empirical chain.

---

## LF4 — observable correspondence and Robertson uncertainty (§14.2)

LF4 is the layer where projective objects acquire ontic content via a concrete Kähler instance. The §14.2 sub-target — the **observable-correspondence theorem**, lifting self-adjoint Hilbert operators to measurable Σ-valued functions whose integral against the preparation measure matches the Hilbert expectation — is fully discharged on the existing compact Kähler instance, with concrete witnesses.

### The §14.2 chain (six commits)

| Commit | Module | Headline |
|---|---|---|
| `eeec1e8` | `LF4/SpectralExpansion.lean` | `hermitian_inner_spectral_expansion` — `⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²` for any Hermitian `A : Matrix (Fin N) (Fin N) ℂ`. Proof: Parseval (`OrthonormalBasis.sum_inner_mul_inner`) + self-adjointness (`Matrix.isHermitian_iff_isSymmetric`) + eigenvalue equation (`LinearMap.IsSymmetric.apply_eigenvectorBasis`, bridged to the Matrix-level reindexed basis as Mathlib's `Matrix.Spectrum` does internally) |
| `dec11e5` | `LF4/SpectralCarving.lean` | Multi-region carving infrastructure (`fibreShiftedArc`, `cumWeights`, `spectralRegion`) + integration headline `integral_spectralOntic_eq_inner_re` — `∫ spectralOntic dμψ = re ⟨ψ, A ψ⟩`. The pre-existing `fibreArc ℓ = (0, ℓ]` is anchored at 0, so distinct arcs are nested; the shifted-anchor primitive gives genuinely disjoint N-arc partitions |
| `fe717ed` | `LF4/SpectralVariance.lean` | `spectralVariance := ∑ᵢ (λᵢ − ⟨A⟩)² · bornWeights i` and the composite headline `integral_spectralOnticCentered_eq_hilbert_norm_sq_diff` — `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²` (the standard QM variance form for self-adjoint A) |
| `63fe1b0` | `LF4/UncertaintyKahler.lean` | `kahler_robertson_ontic_variance` — Robertson bound with **ontic-side LHS**: `(∫ spectralOnticCentered hA ψ dμψ) · (∫ spectralOnticCentered hB ψ dμψ) ≥ ¼ ‖⟨ψ, [A, B] ψ⟩‖²`. Bridges QM-side `variance` (norm-sub-sq form) to spectral form via `variance_eq_norm_sq_sub_expectation_sq` and composes with `Empirical.Uncertainty.robertson_uncertainty` |
| `59eba66` | `LF4/PauliRobertson.lean` | First concrete witness: `pauli_xy_robertson_saturation` — `σ_x, σ_y` on `|0⟩` saturates Robertson with both sides equal to 1. The canonical textbook example, machine-verified |
| `c5eed61` | `LF4/PauliDotRobertson.lean` | Parametric generalisation: `pauliDot_robertson_zPlus â b̂ p₀` — `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²` for arbitrary unit-vector axes (the `DetectorSetting` constraint). Both sides explicit polynomials in the axis components |

The Kähler instance is `KSigma M = CPN M × KTorus = ℂℙ^{M-1} × (AddCircle 1 × AddCircle 1)` with `kMuL = fubiniStudyMeasure p₀ ⊗ vol_T²`. The preparation measure for §14.2 is `(Measure.dirac p₀) ⊗ vol_T²` (Dirac on the base ray × Haar on the fibre).

### What §14.2 unlocks

- **Uncertainty bundle's ontic-variance match**: pre-LF4 `csd_robertson_uncertainty` was a transport theorem (any Hilbert state satisfies Robertson). With `kahler_robertson_ontic_variance`, the physical content — ontic variances satisfy Robertson, not just Hilbert variances — is realisable for any concrete pair of bounded Hermitian observables.
- **Any multi-eigenvalue observable**: spin-1 components, GHZ stabiliser generators, generic Hermitian operators. The spectral pattern works beyond ±1 / projector cases.
- **Variance identity in spectral form**: `Var_ψ(A) = ∑ᵢ (λᵢ − ⟨A⟩)² · ‖⟨uᵢ, ψ⟩‖²`, with `bornWeights ψ A i = ‖⟨uᵢ, ψ⟩‖²` summing to `‖ψ‖²` via `OrthonormalBasis.sum_sq_norm_inner_right`.

### LF4 design choices (post-§14.2)

- `SectorData` (LF2) is the abstract layer; the compact Kähler instance is `KSigma M` defined in `LF4/KahlerInstance.lean`, with `fubiniStudyMeasure p₀` (Dirac at `p₀ : CPN M`) and `vol_T²` (Haar on the flat torus). Fibre arcs are subsets of `AddCircle 1` carved via `equivIoc 1 0`.
- The `fibreShiftedArc c ℓ := (equivIoc 1 0)⁻¹' (Ioc c (c+ℓ))` primitive replaces the nested `fibreArc ℓ = (0, ℓ]` from `SingletKahler.lean` for genuinely-disjoint N-arc partitions. Volume = `ENNReal.ofReal ℓ` for `[c, c+ℓ] ⊆ [0,1]`; disjoint when underlying intervals are disjoint.
- `cumWeights w : Fin (N+1) → ℝ` is defined via `Finset.filter` (not `Nat.rec`) for clean `Finset.sum_insert` proofs of the succ-castSucc step and `cumWeights_last = ∑ w`.
- The variance bridge `variance_eq_norm_sq_sub_expectation_sq` uses `norm_sub_sq` + `Complex.mul_conj` + `Complex.normSq_apply` to derive `Var = ‖Aψ‖² − (re ⟨A⟩)²` from the standard QM `Var = ‖Aψ − ⟨A⟩ψ‖²` definition for symmetric `T` and unit `ψ`.
- Robertson on ontic variances is `kahler_robertson_ontic_variance`; its proof composes `QM_variance_eq_integral_spectralOnticCentered` (the spectral bridge applied twice) with the existing QM-side `Empirical.Uncertainty.robertson_uncertainty` (Cauchy-Schwarz + commutator algebra).

### LF4 backlog (`specs/LF4-todo.md`)

§14.2 is **closed**. Remaining LF4 work:

- **§13** — isometry realisability (cloning / deletion / N-qubit unitaries as Σ-flows). Partial; cloning + deletion bundles in place.
- **§8** — concrete `SectorData` constructions for additional preparation classes (mixed-state, multi-particle).
- **§1-§11** — see `specs/LF4-todo.md` for the full backlog (preparation-to-Hilbert correspondence, projective-first outcome specification, etc.).

---

## LF3 — singlet kernel and the LF1↔LF2↔LF3 empirical chain

LF3 sits on top of LF2 and delivers the **first concrete CSD-ontic prediction** beyond the abstract `SectorData` layer: the singlet kernel `P_st(a, b) = (1 − s·t·a·b)/4` and its four operational consequences (correlation `−a·b`, marginals `1/2`, no-signalling on each side, pointer-completeness), with finite-leakage stability of all four.

### Headline deliverables

1. **Singlet kernel algebraic core** — `cst_squared_eq : ‖cAmp s t (a, b)‖² = (1 − st·a·b)/4`, with `cAmp := (Real.sqrt P_st : ℂ)` as the v1.00 closed-form representative.
2. **Eight-conjunct strong-readout package** — `LF3_main_theorem`. Kernel + correlation + marginals + no-signalling + pointer-completeness in one statement.
3. **Finite-leakage four-conjunct package** — `LF3_finite_leakage_theorem`. Each quantity deviates from its strong-readout value by at most `εA + εB + εA·εB` (with explicit prefactors). Stability-from-assumption (the deviation bound enters as a field of `LeakageCompat`, not a first-principles derivation).
4. **Six chain capstones** — three per-sector + three joint-partition Phase 8 variants:
   - `LF3_singlet_frequency_convergence` (pre-Born, lands on `P_st`),
   - `LF3_singlet_frequency_convergence_born` (closed-form Born, lands on `‖cAmp‖²`),
   - `LF3_singlet_frequency_convergence_born_inner` (bra-ket form, lands on `‖⟨v, ψ⁻⟩‖²` for caller-supplied joint spin eigenstate `v`),
   - plus `..._joint`, `..._born_joint`, `..._born_inner_joint` (joint AE over `Sign × Sign`).

All six chain capstones consume a `PureSingletPreparation D ctx N` bundle (option (B) form, post-Phase 7), whose load-bearing hypotheses are `MeasurementJointEig.born_eq_P_st` (Born identity for joint spin eigenstates) and `PureSingletPreparation.bridge_op_p` (ontic-weight ↔ OP.p bridge). The bundle's `weight_eq_P_st` theorem composes the two.

### LF3 axiom posture (post Phase 7, 2026-05-18)

- `LF3_main_theorem` and `LF3_finite_leakage_theorem` cite **only** the foundational triple.
- The six chain capstones cite the foundational triple **plus** `busch_effect_gleason`: the chain bridge routes via OP.p (option (B) chain design), which extensionally invokes `pure_state_born_weights_of_certainty`. See `specs/pre-LF4-plan.md` for the design rationale.
- `invariant_measure_uniqueness` does **not** appear extensionally on the chain capstone definitions — it enters at LF4 instantiation sites via `MeasureBridgeData.ofSectorData` (option (b) structural propagation).

The full per-theorem audit is in [`AXIOMS.md`](AXIOMS.md) §3.6 and §5. Regression-protection via `CsdLean4/Tests/AxiomAudit.lean`'s `#guard_msgs` against `#print axioms`.

### Posted-fibre-measure migration (2026-05-25)

The preparation primitive at LF3 is a posited fibre trial law `μψ` (option (B)), not the ambient `μL`-conditional `prepMeasure`: under the continuous measure bridge `π∗μL = c·μFS`, every state's fibre is μL-null, so a μL-conditional pure preparation is uninhabitable. The capstones take i.i.d. trials with common law `μψ` and route through `LF1.freq_tendsto_of_iid` (not `LF1_main_theorem_ae`). See `LF4-todo §8`.

---

## LF2 — sector-conditional measure bridge and Born-weight wrapper

LF2 connects LF1's ontic volume weights to projective Born-form probabilities under explicit symmetry and operational hypotheses.

### What LF2 delivers

1. **Measure bridge** — `π∗ μL = c · μFS` for some `c : ENNReal`, under symmetry-compatible `SectorData`. Internal proof of `G`-invariance of `π∗ μL`, then invocation of `invariant_measure_uniqueness`.
2. **LF1 ↔ LF2 weight identity** — `μprep(π⁻¹(O_ep)) = projectiveWeight D μprep O_ep`. The structural hinge.
3. **Combined LF1 + LF2 theorem** — `LF1_main_theorem_projective`. LF1 empirical frequency converges almost surely to the real-valued projective weight under the outcome correspondence `O.preEvent = π⁻¹(O_ep)`.
4. **Born quadratic form** — `born_quadratic`. For unit `ψ, φ : EuclideanSpace ℂ (Fin N)`, `Tr(|ψ⟩⟨ψ| · |φ⟩⟨φ|) = ‖⟨ψ, φ⟩‖²`. Genuine Lean proof via trace-of-outer-product + `Complex.mul_conj`.
5. **Pure-state Born weights from certainty** — `pure_state_born_weights_of_certainty`. Given an `OP` that is "certain" at `|ψ⟩`, for every unit `φ` the probability is `‖⟨ψ, φ⟩‖²`. Composes `busch_effect_gleason` + `rankOneDensity_unique_of_certainty` (now proved, no longer axiomatic) + `born_quadratic`.

### LF2 axiom posture

| Axiom | Role | Source |
|---|---|---|
| `invariant_measure_uniqueness` | `G`-invariant probability measure on `P` is unique (Fubini–Study in the concrete CSD model) | Spec-mandated (§7.4); not in Mathlib |
| `busch_effect_gleason` | Effect-additive probability on finite-dim `N ≥ 2` admits a unique trace-form density | Spec-mandated (§7.4); not in Mathlib |

`rankOneDensity_unique_of_certainty` was carried as a third axiom in earlier revisions; **now a proved theorem** (discharged 2026-05-18) via `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` — `(I − P) ρ (I − P) = 0` from the certainty hypothesis, then `ρ = P ρ P = Tr(M·P) • P` via the rank-1 sandwich identity. Proof in `CsdLean4/LF2/BornWrapper.lean`.

LF1 theorems remain axiom-free beyond Lean's standard triple. Several LF2 theorems — including `born_quadratic` and `LF1_main_theorem_projective` — depend on **neither** of the two LF2 axioms.

### Design choices in LF2

- `SectorData` is parametric in `(SigmaSpace, P, G)`. The projective target is kept abstract — no `Projectivization`, no Fubini–Study measure constructed. Concrete instantiation is LF4 §8's job.
- `μFS` is **not** a field of `SectorData`; it enters `measure_bridge` as an explicit argument, keeping `SectorData` `μFS`-agnostic.
- `Effect` and `DensityOperator` are concrete `Matrix (Fin N) (Fin N) ℂ` structures (not opaque stubs). This gives `born_quadratic` real Lean content.
- `Effect.add` takes the `le_one` hypothesis explicitly; avoids `Option`-valued addition.
- Spec Def 5.1 clause 3 (unitary covariance) is **not** a field on `OperationalPackage` — the literal invariance over-constrains, the covariant reading is type-heavy. Deferred to LF4.

---

## LF1 — deterministic repeated-trial typicality theorem

For a finite-measure ontic state space `(Σ, μL)`, measurable preparation region `Ω0 ⊂ Σ`, measurable outcome partition `{Ω_i^Σ}`, and deterministic `μL`-preserving flow `Φ_t`: LF1 studies repeated trials whose initial microstates are sampled independently from the conditional preparation measure on `Ω0`.

### Headline theorem

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

Empirical frequencies converge `μ`-almost surely to the real-valued ontic weight under repeated preparation with **pairwise-independent trial indicators**. Pairwise independence is the only non-trivial repeated-trial hypothesis; integrability and identical distribution are automatic from the `TrialModel` structure.

### Deterministic content

LF1 is not merely a law-of-large-numbers on an abstract probability space. The physical content is **deterministic at the ontic level**:

- Each single trial is generated by a deterministic measurable flow `Φ_t : Σ → Σ`.
- The outcome of a single trial is determined by the initial microstate `x ∈ Σ`.
- The outcome event is `x ∈ Φ_t⁻¹(Ω_i^Σ)`.

No stochastic evolution at the ontic level. The only probabilistic ingredient is the repeated-trial preparation model. LF1 is a **deterministic typicality theorem with a probabilistic preparation model**, not an intrinsic-randomness theorem.

### Scope and limitations

`OnticSetup` takes an abstract `SigmaSpace : Type*` — **not** specialised to `ℝ^{2n}`, a symplectic manifold, or any concrete phase space. Physical meanings:

| Field | Physical meaning | Status in v1.00 |
|---|---|---|
| `μL` | Liouville measure | *assumed* as a finite measure |
| `Φ` | Hamiltonian flow | *assumed* as a measurable map |
| `hΦ_pres` | Liouville's theorem | *assumed*; structurally inert through LF3 (see `LF1/Setup.lean`) |
| `Ω0` | Preparation region | *assumed* as a measurable set |

**Structural debt D1** (preparation-measure origin): `μL` is asserted as a finite measure; the flow `Φ` is asserted to preserve it; neither is derived from a symplectic / Kähler volume form in v1.00. The LF1 frequency theorem is correspondingly more general than the physical reading suggests. D1 discharges at the Lean level when LF4 instantiates `SigmaSpace` as a compact Kähler manifold and constructs `μL` from `ω^n / n!` — **partially done** by `LF4/KahlerInstance.lean`, which provides `KSigma M = ℂℙ^{M-1} × T²` with `fubiniStudyMeasure` and `vol_T²` as the concrete instance for §14.2.

---

## Empirical — QM-validity regression suite

The Empirical module is a **QM-validity layer** regression suite. Each theorem proves that the standard QM formalisation produces the predicted experimental number; the proofs are linear algebra and inner-product geometry, with no ontic substrate at the proof level. CSD's foundational claim — that QM emerges from volume ratios on Σ — is verified at the **CSD-ontic layer** by the LF3 chain capstones and (now) the LF4 §14.2 carving / variance / Robertson chain.

### Current Empirical phases

| Phase | Predictions | Files |
|---|---|---|
| **A** (Bell) | CHSH at Tsirelson bound, classical-violation gap, no-signalling, marginals, Khalfin-Tsirelson upper bound | `Empirical/QM/Bell.lean`, `Empirical/CSD/Bell.lean` |
| **B** (Resources) | No-cloning (Wootters-Zurek + Dieks 1982), no-deleting (Pati-Braunstein 2000), superdense coding, quantum money, Stern-Gerlach | `Empirical/QM/{NoCloning,NoDeleting,Resources/SuperdenseCoding,Crypto/QuantumMoney,SternGerlach,Uncertainty}.lean` |
| **C** (Contextuality / Paradoxes) | Kochen-Specker 18-vector (Cabello 1996), Mermin-Peres magic square, GHZ all-or-nothing (Mermin form), Hardy non-locality | `Empirical/QM/{Contextuality/KS18,Contextuality/MerminPeres,Multipartite/GHZ,Hardy}.lean` |
| **D** (Gates) | Single-qubit gates, two-qubit gates, Bell preparation, multi-qubit gate semantics | `Empirical/QM/Gates/*.lean` |

Every Empirical theorem is **foundational-triple-only** and AxiomAudit-pinned. The CSD-side companions in `Empirical/CSD/` transport each QM-validity statement through a `CSDBridge.Context D` bundle, carrying the LF2 `SectorData` + measure-bridge data, providing the structural slot for the CSD-ontic interpretation that LF4 will eventually instantiate via `kahler_robertson_ontic_variance` and similar §14.2 mechanisms.

### Two-layer model: QM-validity vs CSD-ontic

The QM-validity layer is **prerequisite** to the CSD-ontic layer. LF4 §14.2's spectral expansion + carving + integration headline + Robertson chain provides the **lifting mechanism**: any QM-validity statement about expectations and variances of bounded Hermitian observables on `EuclideanSpace ℂ (Fin N)` has a corresponding CSD-ontic statement on `KSigma M`, with the same numerical prediction realised via spectral indicator sums integrated against the preparation measure.

See `specs/qm-empirical-tests.md` §0.1 for the full two-layer correspondence statement, and `specs/empirical-csd-bridge-plan.md` for the CSDBridge architecture.

---

## Genealogy

The LLN-based typicality framing used in LF1 and the geometric quantum mechanics structure on `CP^{N-1}` consumed by LF2 match structures developed independently in the Dürr / Goldstein / Zanghì typicality line and the Kibble / Heslot / Anandan / Ashtekar-Schilling geometric quantum mechanics line. The CSD corpus uses the standard mathematical machinery shared with those programmes (measure theory, finite-dim inner-product geometry, the symplectic-Kähler structure on `CP^{N-1}`), and the Lean tree imports Mathlib accordingly. What is independently rediscovered is the **structural choice of objects**: typicality measures on the ontic phase space for LF1, the Born quadratic form on projective Hilbert space for LF2, and (as of §14.2) the eigenvalue-weighted indicator sum integrated against the fibre measure as the ontic counterpart of Hilbert expectation values. The corpus arrives at those choices from its own internal logic; convergence is offered as a credibility signal rather than a claim of priority.

---

## Theorem inventory

Exported theorems and their dependencies. The "Axioms" column lists CSD-specific axioms beyond Lean's foundational triple (`propext`, `Classical.choice`, `Quot.sound`); these are always present via Mathlib and not separately listed. For the full audit see [`AXIOMS.md`](AXIOMS.md).

### LF4 §14.2 (observable correspondence + Robertson on Kähler instance)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `hermitian_inner_spectral_expansion` | `LF4/SpectralExpansion.lean` | `⟨ψ, A ψ⟩ = ∑ᵢ (λᵢ : ℂ) · ‖⟨uᵢ, ψ⟩‖²` for Hermitian `A : Matrix (Fin N) (Fin N) ℂ`. | none |
| `hermitian_inner_spectral_expansion_re` | `LF4/SpectralExpansion.lean` | Real-valued form: `re ⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²`. | none |
| `fibreShiftedArc_volume` | `LF4/SpectralCarving.lean` | Shifted-anchor primitive: `vol (fibreShiftedArc c ℓ) = ofReal ℓ` for `[c, c+ℓ] ⊆ [0,1]`. | none |
| `diracProd_spectralRegion` | `LF4/SpectralCarving.lean` | Per-region carving identity: `(Dirac p₀ ⊗ vol_T²)(spectralRegion w i) = ofReal (w i)` for nonneg `w` with `∑ w ≤ 1`. | none |
| `integral_spectralOntic_eq_inner_re` | `LF4/SpectralCarving.lean` | Integration headline: `∫ spectralOntic dμψ = re ⟨ψ, A ψ⟩` for unit `ψ`. | none |
| `hilbert_norm_sq_apply_hermitian` | `LF4/SpectralVariance.lean` | `‖A ψ‖² = ∑ᵢ λᵢ² · bornWeights i` for Hermitian `A`. | none |
| `spectralVariance_eq_hilbert_norm_sq_diff` | `LF4/SpectralVariance.lean` | `spectralVariance = ‖A ψ‖² − (re ⟨A⟩)²` under unit `ψ`. | none |
| `integral_spectralOnticCentered_eq_variance` | `LF4/SpectralVariance.lean` | `∫ spectralOnticCentered dμψ = spectralVariance` under unit `ψ`. | none |
| `integral_spectralOnticCentered_eq_hilbert_norm_sq_diff` | `LF4/SpectralVariance.lean` | Composite: `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²`. | none |
| `QM_variance_eq_spectralVariance` | `LF4/UncertaintyKahler.lean` | Bridge: `Empirical.Uncertainty.variance A.toEuclideanLin ψ = spectralVariance hA ψ`. | none |
| `kahler_robertson_ontic_variance` | `LF4/UncertaintyKahler.lean` | **Robertson on ontic variances**: `(∫ spectralOnticCentered hA ψ dμψ) · (∫ spectralOnticCentered hB ψ dμψ) ≥ ¼ ‖⟨ψ, [A, B] ψ⟩‖²`. | none |
| `pauli_xy_robertson_saturation` | `LF4/PauliRobertson.lean` | First concrete witness: `σ_x, σ_y` on `|0⟩` saturates Robertson; both sides equal 1. | none |
| `pauliDot_robertson_zPlus` | `LF4/PauliDotRobertson.lean` | Parametric: `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²` for unit-vector axes `â, b̂`. | none |

### LF4 Born-from-Kähler-volume (the moment-map cluster)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `kFlow_measurePreserving`, `kFlow_frequency_convergence` | `LF4/KahlerFlow.lean` | First non-trivial measure-preserving flow `Φ≠id` (fibre translation); LF1 typicality non-vacuous, `hΦ_pres` load-bearing. | none |
| `momentMap_mk_eq_inner_sq` | `LF4/MomentMap.lean` | Born weight = torus moment-map coordinate `Φ([ψ])ᵢ = ‖⟨eᵢ,ψ⟩‖²` (forced symplectic invariant). | none |
| `born_eq_volume_ratio` | `LF4/BornVolume.lean` | Born weight = barycentric Lebesgue-volume ratio of the vertex-replacement image (general `N`). | none |
| `momentMap_orbit` | `LF4/MomentPushforward.lean` | Reduces `Φ∗μ_FS = uniform_Δ` to the Haar marginal (μ_FS = Haar-on-`U(N)` pushforward). | none |
| `fs_born_volume_ratio_qubit` | `LF4/BornFS.lean` | Born weight = genuine `fubiniStudyMeasure` volume ratio on `Σ=ℂℙ¹`, modulo `h_uniform`. | none |
| `qubit_born_frequency_convergence` | `LF4/QubitBornFrequency.lean` | **Busch-free** empirical chain: frequencies → `‖⟨e₀,ψ⟩‖²` via the FS volume, modulo `h_uniform`. | none |

`h_uniform` (the `N=2` Duistermaat–Heckman fact) is an explicit theorem **hypothesis**, not an axiom; the pins above are foundational-triple-only. Discharging it is the deferred plan B (`specs/carve-out-plan.md`).

### LF3 (singlet kernel, pointer-sector decomposition, empirical chain)

`LF3_main_theorem` and `LF3_finite_leakage_theorem` cite **only** the foundational triple. The six chain capstones cite **`busch_effect_gleason`** (option (B) chain bridge routes via OP.p Born identity, post Phase 7).

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `singlet_pauli_correlation` | `LF3/Singlet/Expectations.lean` | `⟨ψ⁻ \| σ·a ⊗ σ·b \| ψ⁻⟩ = −a·b`. | none |
| `cst_squared_eq` | `LF3/Singlet/Kernel.lean` | `‖cAmp s t (a, b)‖² = (1 − s·t·a·b) / 4`. | none |
| `correlation_eq_neg_dot` | `LF3/Singlet/Kernel.lean` | `∑ s t, s·t · P_st(a, b) = −a·b`. | none |
| `marginal_a_eq_half`, `marginal_b_eq_half` | `LF3/Singlet/Kernel.lean` | Both wing marginals equal `1/2`. | none |
| `no_signalling_strong_readout_a`, `..._b` | `LF3/Singlet/Kernel.lean` | Each wing's marginal independent of the other wing's setting. | none |
| `sectorVolume_eq_LF2_Born` | `LF3/Projectors/LF2Interface.lean` | LF3 operator-form sector volume = LF2 Born weight on rank-1 effects. | none |
| `LF3_main_theorem` | `LF3/Interface.lean` | Eight-conjunct strong-readout package. | none |
| `LF3_finite_leakage_theorem` | `LF3/Interface.lean` | Finite-leakage stability of all four kernel quantities. | none |
| `LF3_singlet_frequency_convergence` | `LF3/Interface.lean` | Pre-Born chain capstone (per-sector). | `busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born` | `LF3/Interface.lean` | Closed-form Born variant. | `busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born_inner` | `LF3/Interface.lean` | Bra-ket variant. | `busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_joint` | `LF3/Interface.lean` | Phase 8 joint-partition variant of pre-Born capstone. | `busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born_joint` | `LF3/Interface.lean` | Joint variant of closed-form Born capstone. | `busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born_inner_joint` | `LF3/Interface.lean` | Joint variant of bra-ket Born capstone. | `busch_effect_gleason` |
| `PureSingletPreparation.weight_eq_P_st` | `LF3/PurePreparation.lean` | Composes `bridge_op_p` + `OP_p_at_jointEig_eq_P_st`. | `busch_effect_gleason` |

### LF2 (sector-conditional measure bridge and Born-weight wrapper)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `measure_bridge` | `LF2/MeasureBridge.lean` | `π_* μL = c · μFS` for some `c : ENNReal`. | `invariant_measure_uniqueness` |
| `pushforward_epAction_invariant` | `LF2/MeasureBridge.lean` | `π_* μL` is `G`-invariant under the epistemic action. | none |
| `weights_sum_eq_one` | `LF2/Weights.lean` | Projective weights of a measurable partition sum to 1. | none |
| `born_quadratic` | `LF2/BornWrapper.lean` | `Tr(\|ψ⟩⟨ψ\| · \|φ⟩⟨φ\|) = ‖⟨ψ, φ⟩‖²`. | none |
| `pure_state_born_weights` | `LF2/BornWrapper.lean` | Density-form purity → `‖⟨ψ, φ⟩‖²`. | none |
| `pure_state_born_weights_of_certainty` | `LF2/BornWrapper.lean` | Strengthening from a purity (certainty) hypothesis. | `busch_effect_gleason` |
| `lf1_weight_eq_projective_weight` | `LF2/Interface.lean` | LF1 ↔ LF2 measure-identity hinge. | none |
| `LF1_main_theorem_projective` | `LF2/Interface.lean` | LF1 frequency convergence on projective weight. | none |
| `effectProjFn_rankOne` | `LF2/EffectFn.lean` | Volume-ratio Born identity on the foundational effect function. | none |
| `MeasureBridgeData.ofSectorData` | `LF2/Preparation.lean` | Primary `MeasureBridgeData` constructor. | `invariant_measure_uniqueness` |
| `LF2.PurePreparation.born_rank_one` | `LF2/Preparation.lean` | `OP.p (rankOneEffect φ) = ‖⟨ψ, φ⟩‖²` (chain critical path). | `busch_effect_gleason` |
| `LF2.PurePreparation.born_rank_one_direct` | `LF2/Preparation.lean` | Same conclusion via direct Dirac integration; no Busch. | none |

### LF1 (deterministic repeated-trial frequency theorem)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `LF1_main_theorem_ae` | `LF1/MainTheorem.lean` | Empirical frequencies converge `μ`-almost surely to ontic weight under pairwise-independent trials. | none |
| `expectation_eq_weight` | `LF1/MainTheorem.lean` | `E[𝟙_O(X_n)] = O.weightReal`. | none |
| `prepMeasure_apply` | `LF1/Preparation.lean` | `μprep(A) = μL(A ∩ Ω0) / μL(Ω0)`. | none |
| `weight_eq_prepEvent_div` | `LF1/Outcomes.lean` | `O.weight = μL(O.prepEvent) / μL(Ω0)`. | none |
| `trialEvent_eq_comp_preimage` | `LF1/Trials.lean` | Deterministic structure: `T.trialEvent O n = (Φ ∘ X n)⁻¹(O.Ω)`. | none |

---

## Repository structure

```text
CsdLean4/
  LF1/                 -- ontic setup, preparation measure, outcomes, trials,
                       --   indicators, expectation bridge, LLN application,
                       --   LF1 main theorem and corollaries
  LF2/                 -- SectorData, measure bridge, weights, BornWrapper,
                       --   PhaseInvariance, EffectFn, Preparation, Interface
  LF3/                 -- Sign, DetectorSetting, pauliDot, Hamiltonian,
                       --   SectorSeparation, Projectors/, Singlet/,
                       --   ContextMap, SingletProjective, PurePreparation,
                       --   Interface
  LF4/                 -- Instance, KahlerInstance, SingletKahler,
                       --   SingleQubitKahler, SingletObservables, HardyKahler,
                       --   SpectralExpansion, SpectralCarving, SpectralVariance,
                       --   UncertaintyKahler, PauliRobertson, PauliDotRobertson,
                       --   OnticBorn
  Empirical/
    QM/                -- Pure QM-validity content (no CSD ontology)
    CSD/               -- CSD volume-ratio readings (transport bundles)
  Tests/
    AxiomAudit.lean    -- #guard_msgs regression suite (build-fails on drift)
    Examples.lean      -- LF1 coin-toss, LF2 Born-form edge cases, LF3 chain smoke
  Mathlib/             -- Cat-1: CSD-free helpers staged as Mathlib upstream candidates
  Basic.lean           -- Pkg.Basic convenience re-export
CsdLean4.lean          -- canonical top-level import (explicit module list)
specs/
  LF1-v1.01.{pdf,txt,plan.md}
  LF2-v1.00.{pdf,txt,plan.md}
  LF3-v1.00.{pdf,txt,plan.md}
  LF4-todo.md          -- twelve+ items deferred from LF2 / LF3 to LF4
                       --   (§14.2 now closed; §13, §8, §1-§11 remain)
  pre-LF4-plan.md      -- pre-LF4 execution log
  qm-empirical-tests.md -- QM empirical regression suite plan
  empirical-csd-bridge-plan.md -- CSDBridge architecture
AXIOMS.md              -- per-theorem axiom audit
CONVENTIONS.md         -- three-category framing (Cat-1 / Cat-2 / Cat-3)
BRIDGE-OBLIGATIONS.md  -- per-Empirical-CSD-bundle obligations ledger
PLACEHOLDERS.md        -- schema-mismatch acknowledgements
```
