# QM empirical-test plan: validating CSD against quantum experiment

Plan for an empirical-prediction regression suite. Goal: when LF4 lands
the concrete ontic instantiation, the predictions delivered by CSD
should match QM, and should match laboratory experiment where QM has
been verified. The Lean module is the live regression target; this
document is the roadmap.

This work is independent of the TN4 / Sigma1 / LF4 paper sequence (per
the 2026-05-19 paper-sequencing decision, see `[[project-lf4-decisions]]`):
unblocked Lean thread parallel to `specs/projectivization-plan.md`.

## 0. Goal and scope

**Goal.** Build a Lean-checkable empirical-prediction suite covering:

1. Landmark QM experiments (Bell/Aspect, Stern-Gerlach, Mach-Zehnder, GHZ, Hardy).
2. Foundational QM theorems with empirical content (Tsirelson bound, no-cloning, no-signalling).
3. Quantum algorithms in the CSD reading (Deutsch-Jozsa, Grover, QFT, Shor).

## 0.1 Two-layer model: QM-validity vs CSD-ontic

Every empirical prediction in this suite admits two Lean formulations.
The distinction is load-bearing and easy to confuse.

**QM-validity layer.** A pure theorem about specific Hilbert spaces,
vectors, and operators. Inputs are abstract: `EuclideanSpace ℂ (Fin n)`,
unit vectors, Pauli matrices, isometries. Proofs are linear algebra
and inner-product geometry. **No ontic substrate appears at the proof
level.** This layer answers: "Does the standard QM formalisation
produce the predicted number?"

**CSD-ontic layer.** The same numerical prediction wrapped in the
LF1↔LF2↔LF3 chain so that the QM expectation is *derived from*
empirical frequencies via volume ratios on Σ. Inputs include
`OnticSetup`, `SectorData`, `MeasureBridgeData`, `PurePreparation`. The
proof routes through `LF1_main_theorem_ae` + `measure_bridge` + Born
wrapper. This layer answers: "Does CSD's ontic account produce the same
number that QM does?"

**Current state.** Only one prediction has a CSD-ontic-layer
formalisation: the singlet kernel `P_st(a, b) = (1 − st·a·b)/4`, via
the six `LF3_singlet_frequency_convergence*` capstones. Everything
else in this document — Bell A1–A6, NoCloning B2, Stern-Gerlach,
Mach-Zehnder, GHZ, Hardy, Mermin, KS, algorithms — is QM-validity
layer only at any "actionable now" status.

**Why the QM-validity layer is still load-bearing pre-LF4.**

1. **Prerequisite for LF4 lift.** The LF3 singlet capstones exist
   because the QM-validity `P_st` content existed first. LF4 §8 wraps
   the QM-validity statement; it does not replace it. Any
   `LF4_<prediction>_frequency_convergence` capstone will instantiate
   the same chain pattern over a corresponding QM-validity theorem.
2. **Verification that the projective side is correctly formalised.**
   CSD's foundational claim is `QM = volume ratios on Σ`. The
   QM-validity layer in Lean verifies the LHS independently — without
   it, an LF4 derivation could land at a numerically wrong target
   while passing internal consistency checks.
3. **Cross-reference against published QM and laboratory experiment.**
   Every QM-validity theorem is checkable against textbook QM and
   experimental papers. If the Lean version of CHSH disagrees with
   Aspect's `S ≈ 2√2`, the bug is in the Lean. The CSD-ontic side is
   downstream of that check.

**What "tractable now" means in this document.** It means *QM-validity
layer only*. The CSD-ontic lift for any "tractable now" item is the
same LF4 §8 obligation that the singlet capstones already carry. When
LF4 §8 lands, the lift mechanism is the same wrapping pattern as the
existing `LF3_singlet_frequency_convergence_born_inner` — one capstone
per prediction, consuming a `PurePreparation` bundle and outputting a
QM-validity statement composed with the LF1 SLLN.

**Status tags below.** Each prediction below has *two* statuses
implicitly: a QM-validity-layer status and a CSD-ontic-layer status.
The tables show the QM-validity status; the CSD-ontic status for every
item except the existing LF3 capstones is "LF4-blocked" (specifically,
blocked on §8 Kähler instantiation + chain wrapping).

## 0.2 Scope rule

**Scope rule.** Each prediction is a Lean `theorem` whose statement
expresses the experimental quantity (a probability, expectation, or
constraint) at the appropriate Hilbert-space level. The proof routes
through whichever combination of LF1 + LF2 + LF3 + Bell/NoCloning
infrastructure is available; the proof body does not need to invoke the
ontic chain unless the theorem is explicitly CSD-ontic-layer.

**Layered status.** Predictions are tagged:

- **PROVED** — QM-validity-layer Lean theorem in place, AxiomAudit-pinned.
- **PROVED-LF3** — content exists inside LF3 but not yet named as
  an empirical-test export.
- **READY** — actionable now at QM-validity layer, no new structural debt.
- **LF4-blocked** — even the QM-validity layer requires concrete LF4
  setup (single-qubit `SectorData`, two-mode infrastructure, etc.).
- **INFRA-blocked** — requires new mathematical infrastructure beyond
  LF4 (weak-measurement formalism, n-qubit chains, QFT, etc.).

The CSD-ontic-layer status for every item except the existing LF3
singlet capstones is implicitly "blocked on LF4 §8" and will not be
repeated in each row.
- **INFRA-blocked** — requires new infrastructure (multi-qubit, QFT,
  modular arithmetic, etc.) beyond LF4.

## 1. Phase A — Bell family (actionable now, no LF4 dependency)

All Phase A content lives in `CsdLean4/Empirical/QM/Bell.lean` (Cat-3
unless promoted to Framework Cat-2, see per-item notes), with the
CSD-ontic bridge reading in `CsdLean4/Empirical/CSD/Bell.lean`. Consumes
LF3's `correlation_eq_neg_dot`, `marginal_a_eq_half`,
`marginal_b_eq_half`, `no_signalling_strong_readout_a/b`. The new work
is Tsirelson (A6); A1–A5 are packaging.

| # | Prediction | Statement | Status | Source / verification |
|---|---|---|---|---|
| A1 | CHSH at Tsirelson bound | `∃ a a' b b' : DetectorSetting, |S(a,a',b,b')| = 2√2` on the singlet | **DONE 2026-05-19** (`chsh_singlet_tsirelson_bound`) | Bell 1964 (bound), Tsirelson 1980 (saturation), Aspect 1982 (experimental) |
| A2 | CHSH classical bound violated | `2√2 > 2`, named as the empirical violation gap | **DONE 2026-05-19** (`chsh_classical_bound_violated`) | Bell 1964 |
| A3 | No-signalling, side A | Marginal of A independent of B's setting | **DONE 2026-05-19** (`no_signalling_alice`) | Aspect 1982; loophole-free: Hensen 2015, Giustina 2015, Shalm 2015 |
| A4 | No-signalling, side B | Symmetric | **DONE 2026-05-19** (`no_signalling_bob`) | same |
| A5 | Singlet marginal uniform | `P(A = +|a) = 1/2` for any unit `a` | **DONE 2026-05-19** (`singlet_marginal_alice`, `singlet_marginal_bob`) | Textbook |
| A6 | Tsirelson upper bound (algebraic form) | For any 4 unit vectors `α, α', β, β'` in a complex inner product space, `|Re⟨α,β⟩ − Re⟨α,β'⟩ + Re⟨α',β⟩ + Re⟨α',β'⟩| ≤ 2√2` | **DONE 2026-05-19** (`chsh_inner_bound`); QM-application lift pending (see below) | Tsirelson 1980 |

A6 routes through the operator identity `(σ_a + σ_{a'})² + (σ_a − σ_{a'})² ≤ 4`
plus Cauchy-Schwarz on `⟨ψ | · | ψ⟩`. It is QM-generic (no CSD
content), so Framework Cat-2 promotion is on the table; defer the
classification call until the proof is in place.

**Exit criterion for Phase A.** `Bell.lean` builds; all six items are
named, docstringed with experimental provenance (year + reference),
and pinned in AxiomAudit. The Bell paragraph in `README.md` is
updated.

**Phase A1-A5 landed 2026-05-19** in commit `b8c31da`. A1-A5 are
foundational-triple-only (eight AxiomAudit `#guard_msgs` regressions
added under `### Empirical predictions (Bell family, Phase A1-A5)`
in `Tests/AxiomAudit.lean`).

**Phase A6 (algebraic form) landed 2026-05-19** in a follow-up commit.
`chsh_inner_bound` proves the pure-Hilbert-space Khalfin-Tsirelson
inequality `|Re⟨α,β⟩ − Re⟨α,β'⟩ + Re⟨α',β⟩ + Re⟨α',β'⟩| ≤ 2√2` for
any four unit vectors in a complex inner product space. Foundational
triple only.

**A6 QM-application lift (DONE 2026-05-19).** `chsh_qm_tsirelson_bound`
delivers the QM form: for any unit `ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)`
and any unit detector settings,
```
|Re⟨ψ, (σ·a ⊗ σ·b)ψ⟩ − Re⟨ψ, (σ·a ⊗ σ·b')ψ⟩
   + Re⟨ψ, (σ·a' ⊗ σ·b)ψ⟩ + Re⟨ψ, (σ·a' ⊗ σ·b')ψ⟩| ≤ 2√2.
```
Proved by the Tsirelson construction (`alphaVec a ψ := (σ·a ⊗ I)ψ`,
`betaVec b ψ := (I ⊗ σ·b)ψ`) reducing to `chsh_inner_bound`. Norm
preservation `‖alphaVec a ψ‖ = ‖ψ‖` follows from
`(σ·a ⊗ I)² = I` (Hermitian involution); the inner-product identity
`⟨alphaVec a ψ, betaVec b ψ⟩ = ⟨ψ, (σ·a ⊗ σ·b) ψ⟩` follows from the
Hermitian-adjoint property of `σ·a ⊗ I` plus the Kronecker product
identity `(σ·a ⊗ I)·(I ⊗ σ·b) = σ·a ⊗ σ·b`. Foundational-triple only;
AxiomAudit pinned.

## 2. Phase B — single-experiment Born predictions (LF4-blocked)

These become meaningful once LF4 §8 supplies the concrete
(`SigmaSpace`, `μL`, `Φ`, `π`) for the relevant Hilbert dimension.
Until then, they can be stated as conditional theorems over an
abstract `SectorData` matching the relevant N, but the *physical*
content is sealed behind the LF4 discharge.

### 2.1 `SingleQubit.lean` — N = 2

| # | Prediction | LF4 prerequisite |
|---|---|---|
| B1 | Stern-Gerlach: `P(↑|ẑ, |+ẑ⟩) = 1`, `P(↓|ẑ, |+ẑ⟩) = 0`, `P(↑|x̂, |+ẑ⟩) = 1/2` | N=2 `SectorData` instantiation |
| B3 | Malus's law (operational form): `P(↑|θ, |+ẑ⟩) = cos²(θ/2)` | N=2 `SectorData` + angle parameterisation |

### 2.2 `Interference.lean` — single-photon two-mode

| # | Prediction | LF4 prerequisite |
|---|---|---|
| B4 | Mach-Zehnder visibility = 1 for pure single-photon | N=2 `SectorData` instantiated as two-mode bosonic, beam-splitter unitary |

### 2.3 `NoCloning.lean` — general QM theorem

| # | Prediction | Status |
|---|---|---|
| B2 | No-cloning (two-state form): if isometry `U` clones `ψ, φ` from a unit blank, then `⟨ψ, φ⟩ ∈ {0, 1}` | **DONE 2026-05-19** (`no_cloning_two_state`); Cat-2 (QM-generic) |
| B2 (corollary) | No universal cloner: no isometry can clone every unit state | **DONE 2026-05-19** (`no_universal_cloner_of_witness`); Cat-2 |

**Source:** Wootters-Zurek 1982, *Nature* **299**, 802; Dieks 1982,
*Phys. Lett. A* **92**, 271.

The theorem is stated abstractly over the tensor structure: `tensor :
H → H → Htensor` with the inner-product factorisation `⟨tensor a b,
tensor c d⟩ = ⟨a, c⟩ · ⟨b, d⟩` as a hypothesis. Concrete instances
(Kronecker on `EuclideanSpace ℂ (Fin n × Fin n)`, Mathlib's
`TensorProduct ℂ H H` once equipped with the standard inner product)
discharge the hypothesis. The QM no-cloning content is then immediate.

Foundational-triple-only; AxiomAudit pinned.

### 2.4 `BornNumerical.lean` — Born rule for named 2-qubit states

| # | Prediction | LF4 prerequisite |
|---|---|---|
| B5a | Bell-basis Born numerics: explicit probability tables for |Φ±⟩, |Ψ±⟩ under standard projective measurements | LF4 §8 + LF3 → LF2 chain wiring |
| B5b | Werner state predictions: depolarising-noise spectrum `p|ψ⟩⟨ψ| + (1−p)I/4` | LF4 §8 |

## 3. Phase C — QM paradoxes (mixed INFRA-blocked / LF4-blocked)

QM has a substantial catalogue of paradoxes — statements that look
inconsistent but are predicted by QM and have been empirically verified.
They complement the Bell family: where Bell-type inequalities falsify
local realism *statistically*, paradoxes typically falsify it
*structurally* (single-shot impossibility statements).

Paradoxes are housed by topic under `CsdLean4/Empirical/QM/` (and their
`CSD/` counterparts): `Multipartite/GHZ.lean`, `Contextuality/KS18.lean`
and `Contextuality/MerminPeres.lean`, `Hardy.lean`. (The original plan
proposed a flat `Empirical/Paradoxes/` subdirectory; the by-topic layout
under the `QM/`÷`CSD/` split was adopted instead.)

### 3.1 Single-system paradoxes (mostly LF4-blocked, some QM-generic)

| # | Paradox | Lean target | Status | Experimental verification |
|---|---|---|---|---|
| D1 | Quantum Zeno effect | Frequent measurement of a slowly evolving state freezes the survival probability; `lim_{N→∞} P_survive(N measurements over [0, T]) = 1` | LF4-blocked (needs single-qubit evolution + sequential projective measurement) | Itano et al. 1990, *Phys. Rev. A* **41**, 2295 |
| D2 | Quantum eraser | Marking which-path destroys interference; erasing the mark recovers it | LF4-blocked (single-photon, two-mode, plus environment) | Scully, Englert, Walther 1991; Kim et al. 2000 |
| D3 | Three-box paradox (Aharonov-Vaidman) | Pre/post-selected particle "in box A with probability 1 AND in box B with probability 1" | LF4-blocked (3-state system, weak/strong measurement) | Resch et al. 2004 |
| D4 | Quantum Cheshire Cat | Property (spin) detected without bearer (particle) | INFRA-blocked (weak-measurement formalism) | Denkmayr et al. 2014 |
| D5 | Schrödinger's cat (mesoscopic regime) | Macroscopic superposition observable | INFRA-blocked (open-quantum-system, decoherence model) | NIST 1996 (Be⁺ ion); Arndt et al. (C60 molecules) |

### 3.2 Multipartite paradoxes (`Empirical/Multipartite/`)

| # | Paradox | Lean target | Status | Experimental verification |
|---|---|---|---|---|
| D6 | GHZ paradox (Mermin form) | 3-qubit `(|000⟩ + |111⟩)/√2`: classical local-realism cannot reproduce `⟨σ_x σ_x σ_x⟩ = +1` and the three permutations `⟨σ_x σ_y σ_y⟩ = ⟨σ_y σ_x σ_y⟩ = ⟨σ_y σ_y σ_x⟩ = −1` simultaneously | **DONE 2026-05-20** (`Empirical/Multipartite/GHZ.lean`: `ghz_expectation_xxx`, `_xyy`, `_yxy`, `_yyx`, `no_lhv_assignment_for_ghz`) | Pan et al. 2000, *Nature* **403**, 515 |
| D7 | Hardy's 9% paradox | Non-maximally entangled 2-qubit state; specific outcome combination occurs ~9% of the time though classically impossible | LF4-blocked + LF3 extension | Lundeen, Steinberg 2009 |
| D8 | Mermin's pentagram (KS contextuality) | Five mutually compatible measurements forming a KS configuration cannot all be assigned values consistently | INFRA-blocked (5-context infrastructure) | Bartosik et al. 2009 (neutrons); Kirchmair et al. 2009 (trapped ions) |
| D9 | Kochen-Specker theorem | No non-contextual hidden-variable assignment consistent with QM on projection observables in dim ≥ 3 | **DONE 2026-05-20** (full, `Empirical/Contextuality/KS18.lean`: `no_value_assignment_18_9` + `ks_no_value_assignment_cabello18` for the combinatorial impossibility, plus `cabello_pairwise_orthogonal_in_basis` for the geometric content on the 18 ℝ⁴ vectors); QM-generic, Cat-2 candidate | Cabello 1996 (theoretical); experimental: Kirchmair 2009, others |

### 3.3 Observer-dependence paradoxes (foundational, post-LF4)

| # | Paradox | Lean target | Status | Experimental verification |
|---|---|---|---|---|
| D10 | Wigner's friend | Observer and friend assign different states; QM gives different predictions | post-LF4 (consciousness/measurement-cut question; CSD-relevant since CSD claims an ontic state independent of observer) | Conceptual; some experimental tests (Massimiliano Proietti 2019) |
| D11 | Frauchiger-Renner | Extended Wigner's friend: contradiction from assuming all observers' QM reasoning is consistent | post-LF4 (CSD's ontic foundation may give a sharper answer than QM here) | Theoretical 2018; no decisive experimental test |

These two are the most philosophically loaded and most directly engage
CSD's ontic claim. A CSD-perspective paper on Wigner's friend /
Frauchiger-Renner is a natural late-stage deliverable; the Lean
formalisation tracks behind the paper.

### 3.4 Paradox / CSD-prediction divergence (placeholder)

Some paradoxes may be *resolved* by CSD's ontic account in a way that
makes them no-longer-paradoxical. The structural-debt items
(`[[project-structural-debts]]`: V ≈ 1 − I, G3b) are candidates: their
resolution under the Kähler ontic instantiation may sharpen or relax
specific paradox statements. Watch for these as LF4 → TN4 + Sigma1 +
LF4-paper drafting proceeds.

## 4. Phase D — quantum algorithms (INFRA-blocked + LF4-blocked, long-term)

### 4.1 `Multipartite/GHZ.lean` (now subsumed under §3.2 D6)

The original Phase C GHZ and Hardy items now live under Phase C
paradoxes (§3.2 D6, D7). They are retained as `Empirical/Multipartite/`
files since the bipartite/tripartite split is also useful as a structural
organisation. See §3.2 for the paradox-framed statements.

### 4.2 `Algorithms/`

| # | Prediction | Status |
|---|---|---|
| C5 | GHZ paradox: 3-qubit `(|000⟩ + |111⟩)/√2` shows Mermin's all-or-nothing correlation inconsistent with any local-realistic assignment | INFRA-blocked (3-qubit Hilbert space + multi-Pauli observables) |

### 3.2 `Multipartite/Hardy.lean`

| # | Prediction | Status |
|---|---|---|
| C6 | Hardy's 9% paradox: specific non-maximally-entangled 2-qubit state exhibits a 9% paradoxical outcome under local-realism | LF4 + named 2-qubit state setup |

### 3.3 `Algorithms/` subdirectory

The goal here is *not* to reproduce textbook QM derivations but to express the algorithmic predictions in CSD-foundational form. The interesting question: how does the textbook story (amplitude interference) translate to the volume-ratio account?

| # | Algorithm | Lean target | Status |
|---|---|---|---|
| C1 | Deutsch-Jozsa | `f` balanced vs constant: 1-query discrimination probability | INFRA-blocked (n-qubit + oracle) |
| C2 | Grover | `O(√N)` query complexity to find marked element | INFRA-blocked (controlled gates + amplitude analysis) |
| C3 | Quantum Fourier Transform | `|x⟩ ↦ (1/√N) Σ_y e^{2πi xy/N} |y⟩` | INFRA-blocked (many-qubit + roots of unity) |
| C4 | Shor order-finding | Success probability `Ω(1/log N)` for period extraction from `f(x) = a^x mod N` | INFRA-blocked (QFT + modular arithmetic + continued fractions) |

Each of these will likely become its own paper-and-Lean track. Listed here so the LF4 infrastructure choices don't accidentally close off the natural multi-qubit + circuit-model extensions.

## 3bis. Phase E — quantum information & cryptography

The original plan stopped at Bell, single-experiment Born, paradoxes,
and algorithms. This section adds the quantum-information-resource and
cryptography track. **Most of it composes theorems already in the
corpus** rather than requiring new infrastructure: no-cloning
(`no_cloning_two_state`) is the security root of the prepare-and-measure
(BB84) family, and CHSH at the Tsirelson bound (`chsh_qm_tsirelson_bound`)
is the security root of the device-independent (E91) family.

### 3bis.1 No-go cluster (`Empirical/QM/`)

These are the impossibility theorems. They are QM-generic (Cat-3,
promotion-ready to Cat-2) and stated in the same abstract-tensor /
inner-product style as `NoCloning.lean`.

| # | Theorem | Statement | Status | Source |
|---|---|---|---|---|
| E1 | No-deleting (two-state) | isometry `ψ⊗ψ ↦ ψ⊗e0` for two states forces `⟨ψ,φ⟩ ∈ {0,1}` | **DONE 2026-05-24** (`Empirical/QM/NoDeleting.lean`: `no_deleting_two_state`, `no_universal_deleter_of_witness`) | Pati-Braunstein 2000, *Nature* **404**, 164 |
| E2 | No-broadcasting (pure-marginal core) | a bipartite PSD operator with a pure first-factor marginal `|ψ⟩⟨ψ|` is confined to that pure sector: `(P⊗I)·ρ·(P⊗I) = ρ` | **DONE 2026-06-01** (`Empirical/QM/NoBroadcasting.lean`: `pure_marginal_confinement`, `traceForm_complement_block_zero`). The structural squeeze behind "broadcasting a pure state = cloning it"; via the partial-trace module laws + PSD block-vanishing (mirrors `LF2.rankOneDensity_unique_of_certainty`). The **full BCFJS** commuting-states iff is fidelity / channel-monotonicity content — Mathlib has none; deferred to the QI-infra tranche with E7/E91. | Barnum-Caves-Fuchs-Jozsa-Schumacher 1996 |
| E3a | No-communication (marginal form) | Alice's local unitary `U⊗I` leaves every Bob-side expectation `⟨φ,(I⊗Q)φ⟩` invariant | **DONE 2026-06-01** (`Empirical/QM/NoCommunication.lean`: `aliceOp_conjugate`, `no_communication`, `bob_expectation_invariant`). Via the Kronecker mixed-product collapse `(U⊗I)ᴴ(I⊗Q)(U⊗I)=I⊗Q`; **no partial trace**. Strictly stronger than the singlet-only `no_signalling_alice/bob` (arbitrary state, arbitrary unitary, arbitrary observable). | Ghirardi-Rimini-Weber 1980; Eberhard 1978 |
| E3b | No-communication (reduced-density form, **unitary**) | Alice's local unitary `U⊗I` leaves Bob's reduced state `Tr_A(ρ) = traceLeft ρ` invariant | **DONE 2026-06-01** (`Empirical/QM/NoCommunication.lean`: `no_communication_reduced`, `reducedLeft_aliceConj_eq`). Built on the new partial-trace infra (`CsdLean4/Mathlib/.../PartialTrace.lean`, `traceLeft_conjTranspose_kronecker_one`) + LF2 `DensityOperatorIx.reducedLeft`. The general **CPTP-map** form (not just unitary) is the remaining piece, sharing the no-broadcasting (E2) tranche. | Standard |

**CSD-specific angle (load-bearing, not packaging).** The no-go cluster
is the sharpest test of CSD's ontic claim. An ontic theory naively
looks like it should permit cloning — just copy the microstate. CSD
must explain why copying a sampled microstate does not clone the
quantum state; the answer is structural: the quantum state is a
volume/measure on Σ, not a microstate, so no microstate-copy reproduces
the measure. Each no-go bundle is where a real Σ-side field (`flow`,
`π`-equivariance, measure-preservation) would first earn its keep
instead of living in docstring prose (cf. `PLACEHOLDERS.md §7`
schema-mismatch bundles).

### 3bis.2 Entanglement-as-resource (`Empirical/QM/Resources/`)

| # | Theorem | Statement | Status | Source |
|---|---|---|---|---|
| E4 | Superdense coding | the four local-Pauli images of `|Φ⁺⟩` are the four Bell states (2 classical bits via 1 qubit + shared entanglement) | **DONE 2026-05-24** (`Empirical/QM/Resources/SuperdenseCoding.lean`: `encode_I/X/Z/XZ` image identities + `bell_basis_orthonormal`) | Bennett-Wiesner 1992 |
| E5 | Teleportation | post-Bell-measurement-and-correction state equals the input; 3-qubit identity | **DONE 2026-05-31** (`Empirical/QM/Resources/Teleportation.lean`: `teleState_factorises` (input = \|ψ⟩⊗\|Φ⁺⟩), `teleportation_bell_expansion` (Bell-basis expansion → Pauli image per branch), `teleportation_branch_recovers_input` (four corrections {I,Z,X,ZX} recover ψ); branch-conditional QM-validity layer). The measurement-collapse step + no-signalling marginal need LF5 / partial trace; documented in-file. | Bennett et al. 1993 |
| E6 | Robertson uncertainty | `Var(A)·Var(B) ≥ ¼|⟨[A,B]⟩|²` | **DONE 2026-05-24** (`Empirical/QM/Uncertainty.lean`: `robertson_uncertainty`, over `Module.End ℂ H` with `IsSymmetric`; `robertson_core` is the Cauchy-Schwarz heart) | Robertson 1929 |

### 3bis.3 Cryptography (`Empirical/QM/Crypto/`)

| # | Item | Statement | Status | Source |
|---|---|---|---|---|
| E7 | E91 security witness | CHSH > 2 ⟹ no LHV ⟹ eavesdropper detectable | **NOT cheap (reclassified 2026-05-24)**: the LHV bound `|S| ≤ 2` is deliberately *un-formalised* in `Empirical/QM/Bell.lean` (`bellClassicalBoundValue` is a named constant `2`, not a theorem about local-hidden-variable models — see its docstring). A genuine "no LHV" witness needs an LHV factorisable-correlation model + the `≤ 2` proof, i.e. an infra build; writing it without that would be a thin repackage of `chsh_classical_bound_violated`. Deferred to an LHV-model tranche. | Ekert 1991 |
| E8 | Quantum money unforgeability | forgery ⟹ cloning, contradiction | **DONE 2026-05-24** (`Empirical/QM/Crypto/QuantumMoney.lean`: `quantum_money_unforgeable` via `no_universal_cloner_of_witness`, with concrete Wiesner states `|0⟩,|+⟩` and the proved witness `wiesner_nonorthogonal : ⟨0|+⟩ = 1/√2 ∉ {0,1}`) | Wiesner 1983 |
| E9 | BB84 / B92 protocols | basis-choice / encode / measure / sift structures; security reduction to no-cloning + measurement disturbance | **structure-now** (the disturbance half needs the LF5 measurement-update notion; scaffold the type, carry the security theorem as the obligation) | Bennett-Brassard 1984 |

### 3bis.4 INFRA-blocked (new mathematics)

- **Holevo bound, Schumacher compression** — need von Neumann entropy
  of density operators (concavity, subadditivity). Check Mathlib
  matrix-entropy coverage first.
- **Schmidt decomposition, purification** — need SVD / spectral theorem
  on the bipartite split; purification is the more tractable.
- **Strong subadditivity (Lieb-Ruskai), monogamy (CKW)** — far out.
- **No-bit-commitment (Mayers-Lo-Chau)** — needs purification + fidelity
  machinery.

**Note on the second axiom.** Gleason's theorem is itself a QI result.
The Busch–Gleason statement axiomatised in LF2 (`busch_effect_gleason`)
would have its concrete-content thread here: a finite-dimensional
Gleason/Busch formalisation is the analogue, for the *second* LF2 axiom,
of the projectivization thread that produced
`invariant_measure_uniqueness_cpn` for the first. Heavy; INFRA-blocked.

### 3bis.5 Execution order for Phase E

1. **No-deleting (E1)** — DONE; cheapest, mirrors no-cloning.
2. **Superdense coding (E4)** — DONE; Bell-state Pauli identities + orthonormality.
3. **Quantum money (E8)** — DONE; composes no-cloning with a concrete Wiesner witness.
4. **No-broadcasting (E2), no-communication (E3)** — need a partial-trace infra build first (not in Mathlib); promote to an infra tranche.
5. **E91 witness (E7)** — needs an LHV-model build (the `≤ 2` bound is un-formalised); LHV tranche, not a composition.
6. **Robertson (E6)** — DONE; QM-generic operator inequality.
7. **Teleportation (E5)** — DONE 2026-05-31; branch-conditional form (dual of E4).
8. **Pause for LF5** on BB84/B92 security (measurement update).

## 4. Recommended execution order

1. **Spec doc landed (this file).**
2. **`Bell.lean` Phase A packaging commit.** A1–A5 (re-export PROVED-LF3 content with empirical provenance docstrings, AxiomAudit pinning). A2 is a `theorem` carrying the numerical gap. ~2h focused.
3. **`Bell.lean` A6 (Tsirelson upper bound).** New theorem; the load-bearing one in Phase A. ~1 day focused.
4. **`NoCloning.lean` B2.** No-cloning is QM-generic and doesn't need LF4. ~1 day focused.
5. **Pause for LF4.** Phases B (rest) and C are queued behind LF4 §8 (`SectorData` instantiation) and per-experiment infrastructure.

After step 4, the immediately-actionable empirical work is exhausted
until LF4 progresses. The pre-LF4 deliverable is: Bell-family fully
proved, Tsirelson upper bound proved, no-cloning proved. That is a
substantial empirical-status milestone: the Bell experiments are the
canonical foundational benchmarks for QM, and CSD passing them is the
first hard test the framework needs to clear.

## 5. Long-term: EFT and CSD-specific predictions

CSD claims to be a finite EFT of an ontic structure. Standard QM is
recovered in the appropriate limit. The empirical tests above are the
"CSD reduces to QM in regime X" checks. Two additional categories
worth listing for completeness:

### 5.1 EFT-level CSD predictions matching QM

These are the QM-equivalence checks above. The empirical content is
identical to QM; the CSD-specific content is the volume-ratio account
of where the numbers come from.

### 5.2 Potential CSD departures from QM

The structural debts (`[[project-structural-debts]]`) include V ≈ 1 − I
and G3b: regimes where CSD may not exactly reproduce QM. If any of
these become numerically pinned, they would become **predictions
distinguishing CSD from QM** rather than empirical-verification checks.
This is post-LF4 paper-track territory (TN0 §9.3 forwarding remark);
not yet scope here, but noted so the test infrastructure is structured
not to assume CSD = QM identically.

## 6. Naming conventions

- Each theorem carries an experimental-source docstring: `**Experimental verification:** Aspect 1982, Phys. Rev. Lett. 49, 91`.
- Top-of-file `Category:` declaration per `CONVENTIONS.md`.
- AxiomAudit `#guard_msgs` entries grouped under `/-! ### Empirical predictions -/`.

## 7. Files index

**Layout (updated 2026-05-31).** The tree splits into two parallel branches:
`Empirical/QM/` (pure QM-validity theorems, §0.1) and `Empirical/CSD/` (the
volume-ratio bridge readings — each `QM/` file has a `CSD/` counterpart carrying
a `CSDBridge.Context D` bundle). Both branches are imported explicitly in
`CsdLean4.lean` (lines 70–100); there is no `Empirical.lean` aggregator.

```
specs/qm-empirical-tests.md                            -- this file (the roadmap)

# QM-validity branch (Empirical/QM/)
CsdLean4/Empirical/QM/Bell.lean                        -- Phase A: A1-A6 (CHSH, Tsirelson, no-signalling)
CsdLean4/Empirical/QM/NoCloning.lean                   -- Phase B: B2  (namespace CSD.Empirical.NoCloning)
CsdLean4/Empirical/QM/NoDeleting.lean                  -- Phase E: E1
CsdLean4/Empirical/QM/Uncertainty.lean                 -- Phase E: E6 (Robertson)
CsdLean4/Empirical/QM/SternGerlach.lean                -- Phase B: B1
CsdLean4/Empirical/QM/Hardy.lean                       -- Phase C: D7 (QM-validity layer)
CsdLean4/Empirical/QM/Multipartite/GHZ.lean            -- Phase C: D6
CsdLean4/Empirical/QM/Contextuality/KS18.lean          -- Phase C: D9 (Kochen-Specker, Cabello-18)
CsdLean4/Empirical/QM/Contextuality/MerminPeres.lean   -- Phase C: Mermin-Peres square
CsdLean4/Empirical/QM/Resources/SuperdenseCoding.lean  -- Phase E: E4
CsdLean4/Empirical/QM/Crypto/QuantumMoney.lean         -- Phase E: E8 (Wiesner, via no-cloning)
CsdLean4/Empirical/QM/Gates/{SingleQubit,TwoQubit,MultiQubit,BellPrep}.lean
                                                       -- gate library (Hadamard/Pauli/phase, CNOT/SWAP/CZ, Toffoli; Bell prep)

# CSD-ontic bridge branch (Empirical/CSD/) — one file per QM/ counterpart
CsdLean4/Empirical/CSD/Framework.lean                  -- CSDBridge.Context D bundle + transport scaffolding
CsdLean4/Empirical/CSD/{Bell,NoCloning,NoDeleting,Uncertainty,SternGerlach,Hardy}.lean
CsdLean4/Empirical/CSD/Multipartite/GHZ.lean
CsdLean4/Empirical/CSD/Contextuality/{KS18,MerminPeres}.lean
CsdLean4/Empirical/CSD/Resources/SuperdenseCoding.lean
CsdLean4/Empirical/CSD/Crypto/QuantumMoney.lean
CsdLean4/Empirical/CSD/Gates/{Framework,SingleQubit,TwoQubit,MultiQubit,BellPrep}.lean

CsdLean4/Empirical/QM/Resources/Teleportation.lean    -- Phase E: E5 (DONE 2026-05-31)

# Planned but not yet created (see phase tables above)
#   QM/NoCommunication.lean            -- Phase E: E3 (split: E3a marginal-form READY; E3b needs partial-trace infra)
#   QM/Crypto/E91.lean                 -- Phase E: E7 (deferred, needs LHV-model build)
#   Interference.lean / BornNumerical.lean / Algorithms/*  -- LF4/INFRA-blocked
```

**Namespace note.** Most `QM/` files use `CSD.Empirical.QM.<Topic>`, but the two
earliest (`NoCloning`, and the `NoDeleting` it seeded) use `CSD.Empirical.<Topic>`
(no `QM` segment) for historical reasons — check the file before referencing a
fully-qualified name.

`Tests/AxiomAudit.lean` carries the `#guard_msgs` pins; empirical entries are
grouped under `### Empirical predictions`.
