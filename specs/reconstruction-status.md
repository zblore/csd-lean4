# Reconstruction status — a thorough review of what is machine-verified (2026-07-15)

**Purpose.** A single honest review of what the `csd-lean4` corpus actually proves, at commit `HEAD`
(after the FND "Choice A" layer and FND-T5). It supersedes scattered claims; where it and an older
document disagree, this file and [`connectivity-manifest.md`](connectivity-manifest.md) win. Everything
below is `sorry`-free, `lake build CsdLeanTests` green, and AxiomAudit-pinned to the foundational triple
(`propext`, `Classical.choice`, `Quot.sound`) unless explicitly noted otherwise.

## 1. One-paragraph verdict

The corpus is a **rigorous, forward finite-dimensional QM reconstruction from one posited Choice A ontic
model.** A single genuine `Φ ≠ id` Kähler sector yields BOTH pillars (Born + Schrödinger) at general `N`
with arbitrary Hermitian `H` (`manyToOneSchrodingerSetup_both_pillars`), and ONE ontic model
`(Σ = ℂℙ^{M}×T², μL = μFS⊗vol, Φ, π = Prod.fst)` carries isolated Hamiltonian dynamics and de-isolating
measurement together. `unified_choiceA_capstone` BUNDLES the dynamics + measurement core (six proved
properties: isolated measure-preservation, projectability, FS pushforward, measurement-interaction
preservation, a.e. pointer readout, record establishment). Time-indexed record semantics (now INSTANTIATED on the model:
`unifiedFlowedSemantics` / `unified_records_persistence`, records time-physical under the isolated flow),
Born-frequency convergence (now stated on the model: `unified_born_frequency`, for EVERY unit `ψ` — the `hpos` full-support genericity hypothesis was retired via the `_uncond` engine, so vanishing amplitudes are covered too), and the conditioning = Lüders correspondence (`ConditioningLuders.lean`,
`conditioning_luders_effect_equivalence` — now genuinely proved: the ontic record-conditioning and the
Lüders update give the same conditional prediction for every pointer-basis effect) are now ASSEMBLED into
one tiered record: **`FiniteQMClosure`** / `unifiedFiniteQMClosure` (`FND/FiniteQMClosure.lean`) collects all
eleven proved-on-the-model facts as fields (the sixth-through-eleventh: records #5, Born-frequency #2, conditioning=Lüders #3/#4, mixed-state Born weight #8 C, mixed-state Born FREQUENCY #8 C), each discharged by its source lemma, and states honestly in the
module header what is a theorem here vs. a Choice-A posit vs. a QM adapter vs. still open (no field is
`sorry`). So L9 is now a single unified closure (Tier 1), not a scattered multi-theorem partial. The **one
deep gap** — outside the closure's Tier 1 — is A5 / FND-1: the
sector itself is **posited**, not derived from the deterministic flow (the Born trials SAMPLE `μL`
i.i.d.). This is FORWARD throughout — it does not derive the sector — and that scope matches Paper C's
own (§1.4 assumes `Σ`, `π`, the A5 sector).

## 2. The FND Choice A postulate ledger (P1–P9 / B1–B7 / T1–T16)

The anti-circularity ontology layer (`CsdLean4/FND/`, namespace `CSD.FND`). Full ledger in
[`../CsdLean4/FND/Adapters.lean`](../CsdLean4/FND/Adapters.lean) and [`../AXIOMS.md`](../AXIOMS.md) §3.7.
NONE of these is an `axiom`: postulates are structure fields, bridges are named assumptions discharged
per model, targets are `Prop` predicates inhabited by proved theorems.

**Core postulates (fields).** P1 `ConstraintSurface`; P2 `ConstraintDynamics.muL`; P3 `flow`/`flow_zero`/
`flow_add`; P4 `flow_preserves`; P5 `RecordSemantics` (time-indexed via `flowedSemantics`); P6
`HistoryPreparation` (isolation = conditioning); P7 `ProjectiveState = CP^{N-1}`; P8 `ChoiceASector.pi`;
P9 many-to-one `π`.

**Bridges (discharged for the product model).** B1 `π_*μL = μFS` (`productSector_hasFubiniStudyPushforward`);
B2 `ProjectiveDynamicsBridge.projectable`; B3 `HasUnitaryRealisation`/`HasHamiltonianRealisation`; B4/B5
`DeisolationModel` + `vnDeisolationModel_records`; B6 `CompositeSector.tensor_dimension` (P3 "why ⊗" — now
DISCHARGEABLE via `CompositeSector.ofReconstruction` / `composite_dim_eq`, no longer necessarily posited);
B7 `TrialWitness` / `IsErgodicForOutcomeRegions`.

**Theorem targets (each inhabited).**

| # | Target | Key theorem | Status |
|---|---|---|---|
| T1 | Born from volume | `BornFromVolume`, LF4 `fs_born_volume_ratio_N` | proved |
| T2 | Born from i.i.d. frequencies | `born_frequency_convergence_N` | proved |
| T3 | Born from deterministic-flow frequencies | `BornFromFlow` predicate | OPEN (= A5 face) — ergodic side sharpened: `UniquelyErgodic` defined + `⇒ Ergodic ⇒ IsErgodicForOutcomeRegions` (`FND/UniqueErgodicity.lean`); residual gap is the Mathlib-absent pointwise Birkhoff theorem, and the unitary no-gos exclude the hypothesis (candidate flow must be non-unitary) |
| T4 | Unitary projected dynamics | `HasUnitaryRealisation` | proved (product model) |
| T5 | Schrödinger evolution | `HasHamiltonianRealisation`, `productProjectedFlow_hasHamiltonianRealisation` | proved (product model) |
| T6 | Unique contextual outcome a.e. | `vnDeisolationModel_ae_total` | proved |
| T7 | General conditional update | `conditionalUpdate_capstone` | proved |
| T8 | Lüders update | `luders_capstone` (sharp special case of T7) | proved |
| T9 | Mixed states | `mixedState_capstone`, `isPure_iff_trace_sq_one`; ensemble #8 A+B: `traceForm_ensemble`, `density_isPureEnsemble`, `mixedEnsemble_capstone`; ontic-side #8 C: `mixed_ontic_born_weight` (= `FiniteQMClosure.mixed_born`) | proved (mixed-freq LLN open) |
| T10 | POVM by dilation | `POVMWeightsProbability`, `LF4.povm_born_frequency_volume_canonical` | proved |
| T11 | Composite probabilities | joint Born-frequency capstones | per-instance (P3-gated for sector-intrinsic) |
| T12 | Entangled predictions | = T14 | per-instance |
| T13 | Contextuality | `NoNonContextualValuation`: Cabello-18 / Mermin-Peres / GHZ; `general_ks_noNonContextualValuation` | proved (+ general KS) |
| T14 | Bell correlations | `NoLocalHiddenVariableTable` (CGLMP), `HasTsirelsonSeparation`, `bell_general_separation`, `lhv_chsh_le_two`, `qm_chsh_le_tsirelson` | proved (+ universal bounds) |
| T15 | No-signalling | `HasNoSignalling` (singlet), `tensorSector_no_signalling` (operator) | proved |
| T16 | Two-path interference | `HasBornInterference` (Hadamard test) | proved (derived, not postulated) |

## 3. The connectivity chain (L1–L9)

See [`connectivity-manifest.md`](connectivity-manifest.md) for full evidence.

| Link | Claim | Status |
|---|---|---|
| L1 | Kähler geometry ⇒ sector fields | PARTIAL — volume forced; 2-form's **pointwise** compatibility core now genuine & consumed (`IsKahlerSector := IsFubiniStudyKahler`, proved via `fubiniStudy_pointwise_kahler_compatibility`); only manifold closedness `dω=0` / `ω^{∧n}/n!=μ_FS` unformalizable (no Mathlib API) |
| L2 | Σ+Φ+π ⇒ projected flow | CONNECTED |
| L3 | projected flow ⇒ Schrödinger | CONNECTED — general `N`, arbitrary `H`; C¹-Stone derivation EXERCISED on the real nonzero generator (`manyToOneSchrodingerSetup_schrodinger_derived`), not only the `A = 0` witness |
| L4 | genuine `Φ ≠ id` inhabitant | CONNECTED — `rotationSetup`, `manyToOneSetup`, `unitaryFlowSetup` (4 total) |
| L5 | sector ⇒ Born frequencies | CONNECTED (structural) |
| L6/L8 | ONE object, both pillars, many-to-one `π` | CONNECTED — `manyToOneSchrodingerSetup_both_pillars` |
| **L9** | ONE model: dynamics + measurement + records + Born + update | CONNECTED — **`FiniteQMClosure` / `unifiedFiniteQMClosure`** (`FND/FiniteQMClosure.lean`) assembles all 11 proved-on-model facts (the 6 core `unified_choiceA_capstone` properties + records-time-physical #5 + Born-frequency #2 + conditioning=Lüders #3/#4 + mixed-state Born weight #8 C `mixed_born` + mixed-state Born FREQUENCY #8 C `mixed_born_frequency`) into ONE tiered record, each field discharged by its source lemma; Choice-A posit / QM adapters / open residue documented, not encoded as fields |
| **L7** ★ | Born weights derived FROM the flow | **OPEN (boundary proved; ergodic face sharpened)** — the sector is posited (A5/FND-1); a single flow provably cannot pin `μ_FS` (`flow_admits_invariant_ne_fubiniStudy`, `obsFlow_not_uniquely_ergodic`). `UniquelyErgodic` now defined with `⇒ Ergodic ⇒ IsErgodicForOutcomeRegions` (`FND/UniqueErgodicity.lean`); the gap to `BornFromFlow` is exactly the Mathlib-absent pointwise Birkhoff theorem, and the current unitary flows provably fail the hypothesis. Typicality itself is forced by the LLN, not this route (Papers A/B) |

## 4. The forward reconstruction — what each pillar delivers

* **Born rule** (LF1–LF4): the Born weight `‖⟨eᵢ,ψ⟩‖²` is a Fubini–Study typicality volume; i.i.d.
  FS-typical trial frequencies converge a.s. to it, Gleason-free, general `N`, including **general POVMs**
  (`povm_born_frequency_volume`, canonical Naimark dilation from CFC `√Eᵢ`).
* **Schrödinger dynamics** (the W-series, LF4): given the Kähler sector interface, Wigner rigidity +
  Bargmann branch selection + phase lift + a C¹ finite-dim Stone theorem force the projected flow to be
  `exp(-itH)` on rays. Instantiated non-trivially at general `N` (`manyToOneSchrodingerSetup`); the
  C¹-Stone derivation is now EXERCISED on the real object at general `N` with arbitrary Hermitian `H` —
  `manyToOneSchrodingerSetup_schrodinger_derived` exhibits the skew generator `A = -iH`, DISCHARGES the
  smoothness datum `U' t = U t·A`, and runs `CSD.StoneC1.eq_exp_of_hasDeriv` — so the ray-level `rfl`
  form is backed by an actual derivation, not standing alone.
* **Measurement** (LF5 + FND): a measure-preserving von Neumann de-isolation flow realises the Naimark
  dilation; the per-microstate pointer outcome is defined a.e.; frequencies are Born. In FND this is a
  `DeisolationModel` over the *nontrivial* isolated dynamics (`unifiedDeisolationModel`).
* **Records / state update** (FND): records are time-indexed measurable events (`flowedSemantics`), with
  probability conserved and flow-covariant under isolation; the post-outcome preparation has proven
  nonzero measure (`PostMeasurement.appendFact`); the record conditioning equals the Lüders update as an
  OPERATIONAL EQUIVALENCE — `ConditioningLuders.conditioning_luders_effect_equivalence`: on the product
  model the ontic record-conditioning and the Lüders update give the same conditional prediction for every
  pointer-basis effect, resting on the proved weight agreement `onticRegion_measure_eq_born`
  (`μL(π⁻¹ bornRegion i) = ‖⟨eᵢ,ψ⟩‖²`, via B1 + Born-from-volume). (The earlier
  `luders_record_conditioning_correspondence` only conjoined the two Bayesian halves; it did not prove the
  weights agree.)
* **Entanglement / non-locality** (LF6): Bell-forced non-factorisation in the Σ-engine at full
  generality — CGLMP for every `d`, GHZ/Mermin for every party count `n`, no-signalling; the universal
  bounds (`lhv_chsh_le_two`, `qm_chsh_le_tsirelson`, `cglmp_lhv_le_two`, `bell_general_separation`).
* **Open-system dynamics** (LF6-2): the two canonical qubit dissipators as continuous quantum dynamical
  semigroups — T2 dephasing (`dephasingChannel`) and T1 amplitude damping (`dampingChannel`), each with
  the semigroup law, trace preservation and relaxation limits.

## 5. Adjacent arms (honest scope)

* **Empirical / CSD arm** — thermodynamics (TH1–TH4), CV track (finite position/momentum, approximate
  CCR, oscillator spectrum), algorithms (Deutsch–Jozsa, Simon, BV, Grover, QFT, full Shor), metrology
  (Ramsey, Heisenberg, quantum Fisher), QEC, contextuality, channels/decoherence. These share the same
  complex-sector + Born + unitary primitives but are independent theorems consuming them, not a formal
  cascade from the FND ledger.
* **ecdsa.fail / ECDLP arm** — quantum resource estimation for Shor-on-ECDLP (elliptic-curve arithmetic,
  Karatsuba/Toom-3, safegcd/half-GCD inversion, Toffoli/qubit counting, a verified-floor / trusted-estimate
  two-track). It presupposes the unitary-evolution pillar but its theorems are number theory + circuit
  costs, NOT a QM reconstruction. See [`ecdsafail-two-track.md`](ecdsa/ecdsafail-two-track.md).

## 6. Axiom hygiene

* Foundational triple only on every FND/LF headline pin.
* One imported mathematical result remains: `busch_effect_gleason` — library debt confined to the
  operational stratum, **not** in the ontic Born derivation (which is Gleason-free). See
  [`../AXIOMS.md`](../AXIOMS.md) §2.2.
* No global `axiom` declarations in the FND layer; no `sorry`/`admit`.
* Three static guards (connectivity, sector-linkage, axiom-imports) pass and are run in CI.

## 7. The honest frontier — what is NOT claimed

*(Actionable open items — including the research-tier ones below — are tracked in the
canonical [`BACKLOG.md`](BACKLOG.md).)*

* **A5 / FND-1 ★** — deriving the sector `(π, G)` and its Born weights FROM the deterministic flow. The
  sector is posited; the trials sample `μL`. This is the one deep gap and is research-grade. It now has
  **both a proved boundary and a localized partial**:
  * **No-go (why the gap is real, not a formalisation debt)** (`FND/A5NoGo.lean`): a single projective
    unitary flow does NOT uniquely determine an invariant measure — a flow with two distinct fixed rays
    admits (at least) two distinct invariant probability measures, so at least one is not `μ_FS`
    (`flow_admits_invariant_ne_fubiniStudy`), exhibited on the concrete nontrivial phase-flip
    `diag(1,-1)` on `ℂℙ¹` (`phaseFlip_admits_invariant_ne_fubiniStudy`). So "A5 is posited" is a proved
    statement about the limit: the deterministic flow underdetermines the sector's typicality measure.
  * **Localized partial (what DOES pin it)** (`FND/LocalisedTypicality.lean`): A5 is discharged AT sectors
    carrying the full `U(N)` symmetry — the typicality measure and Born weights are symmetry-forced there
    (`localised_A5_capstone`, `region_measure_symmetry_forced`) — so A5 need only hold "in the appropriate
    places". Residual: the bare flow is one one-parameter subgroup, not all of `U(N)`; the symmetry is
    still construction data. Together: a single flow is provably insufficient; the full symmetry is
    provably sufficient — the frontier is exactly the gap between them.
* **P3 "why ⊗" — SUFFICIENCY + NECESSITY both proved** (2 files): SUFFICIENCY
  (`FND/TensorSolved.lean` `composite_is_tensor_product`) — the standard Kronecker model REALIZES the
  composition principles: `compositeTensorEquiv` is a bijective linear iso `M_{NA} ⊗ M_{NB} ≃ M_{NA·NB}`
  in which locality (`aliceOp_bobOp_commute`) and local tomography (`joint_mem_span_local`, proved for the
  quantum case) both hold. NECESSITY / uniqueness (`FND/TensorReconstruction.lean`
  `compositeAlgReconstruction`) — an ARBITRARY composite `𝒜` with commuting, generating local embeddings
  is FORCED to be the tensor product (`𝒜 ≃ₐ M_NA ⊗ M_NB`: injective because `M_NA ⊗ M_NB` is simple,
  surjective from generation), and `composite_dim_eq` derives `dim = NA·NB`, DISCHARGING bridge B6
  (`CompositeSector.ofReconstruction` fills the `tensor_dimension` field from the reconstruction). So both
  halves are now theorems. Residual: local tomography itself is the one operational axiom that cannot be
  derived from nothing (it singles out quantum `⊗`); and the sector interface uses the discharge
  constructor only where the local-algebra data is on hand.
* **KG-1** — the Kähler closed 2-form `dω = 0` and the global volume identity, blocked on missing Mathlib
  manifold exterior calculus (the volume is forced; the pointwise form is proved).
* **LF6-9** — the general Lindblad generator + complete positivity (the two bounded dissipators are done).
* **IP-1** — identical particles / spin-statistics, not in the corpus.

### 7a. Settled non-goals — do NOT re-litigate these

Two positions are **decided** and recorded here so they are not re-argued. Both are backed by
machine-checked facts in the corpus.

* **NG1 — "derive Born from a single deterministic flow" (the Birkhoff / single-trajectory ergodic
  route) is a PROVED DEAD-END that CSD deliberately does not take.** CSD forces typicality by the **law
  of large numbers over fresh i.i.d. preparations**, NOT by time-averaging one trajectory
  (`specs/active-todo.md`, framing correction 2026-06-29, Papers A & B). The single-flow route is
  provably impossible: `flow_admits_invariant_ne_fubiniStudy` (`FND/A5NoGo.lean`),
  `obsFlow_not_ergodic` / `obsFlow_not_uniquely_ergodic` (`LF4/TypicalityForcing.lean`) — a unitary flow
  is not even ergodic w.r.t. `μ_FS`. The ergodic scaffolding (`FND/UniqueErgodicity.lean`,
  `IsErgodicForOutcomeRegions`, `BornFromFlow`) is **boundary-marking only** — it precisely locates why
  the route fails; it is NOT the reconstruction path and building it out further is not progress on the
  reconstruction. The genuine open ★ residue is narrower: the sector/symmetry ORIGIN (NG-adjacent, see
  A5 above), not "Born from flow".
* **NG2 — the Busch effect-Gleason axiom is NOT needed for CSD's core claim; discharging it is
  cosmetic.** CSD's ontic Born rule is **Gleason-free**: it is a Fubini–Study / Duistermaat–Heckman
  *volume* (`bornRegion_fs_measure`, `born_frequency_convergence_N`), with no Gleason or Busch input.
  The single imported axiom `busch_effect_gleason` (`LF2/BornWrapper.lean`) enters only the
  **operational effect/POVM stratum**, off the reconstruction path (`AXIOMS.md` §2.2). Proving it in-repo
  would take the imported-axiom count to zero — an **audit-posture** improvement (the "three axioms, zero
  imported" headline), NOT a strengthening of the CSD reconstruction. Do not describe it as required for
  the result.

## 8. Bottom line

Under Choice A, the finite-dimensional QM reconstruction is **structurally closed forward**: one posited
ontic model, one measurement/record/update loop, the full T1–T16 target ledger inhabited, axiom-clean.
The remaining depth is the *origin* of the posited sector (A5) and the *derivation* of composition (P3) —
genuine open problems, honestly flagged, not papered over.

References: [`connectivity-manifest.md`](connectivity-manifest.md), [`future-work.md`](future-work.md),
[`../AXIOMS.md`](../AXIOMS.md), [`../CsdLean4/FND/Adapters.lean`](../CsdLean4/FND/Adapters.lean).
