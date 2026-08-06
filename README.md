# csd-lean4

[![CI](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalisation of **Constraint-Surface Dynamics (CSD)** — a reconstruction
of finite-dimensional quantum mechanics from one deterministic ontic *surface* `Σ`, carrying a
family of explicit volume-preserving witnesses.

## What this is, in plain terms

CSD starts from one posited object: an ontic surface `Σ` (concretely `ℂℙ^{N-1} × T²` — a
complex projective space of rays carrying a small torus of extra ontic coordinates), a natural
volume measure on it, and a deterministic, volume-preserving flow. Probability is read as
**typicality**: the fraction of ontic volume, nothing more. Everything else is supposed to be
a *theorem*.

This repository machine-verifies that programme for finite-dimensional QM. From that one
model, with no further axioms, the corpus derives:

- **Schrödinger evolution** — the flow, projected to rays, *is* `exp(-itH)`;
- **the Born rule** — outcome probabilities are volumes of regions of `Σ`, for every
  dimension and for general (POVM) measurements, with observed frequencies converging to them;
- **measurement as a physical process** — an explicit volume-preserving interaction creates a
  record from an apparatus-ready state, the record persists, distinct outcomes exclude each
  other, and the outcome statistics are exactly Born. A single capstone theorem
  (`projectiveMeasurementCapstone`) indexes the layer — rank-one measurements, every
  apparatus basis, degenerate blocks, the smooth horn, and its Schrödinger generation
  (distinct witnesses per horn, by design) — with mixed preparations reproducing `Tr(ρE)` through the same
  dynamics, no-signalling holding *dynamically* (a distant measurement — outcome or basis
  choice — cannot move the local marginal), and the quantum eraser realised as a process:
  erasure restores fringes only before a record exists, never after. POVMs ride the same
  machinery via Naimark dilation — their **instrument** (the state update) is delivered
  dynamically, and their Born statistics are proven at the protocol-**sector** level for
  every POVM (`povm_sector_born_canonical`; the selector-level-only boundary this line
  recorded until 2026-08-04 was discharged that day, and this sentence caught up on
  2026-08-06 — an *under*claim outliving its fact, the mirror image of the drift the
  guards police). Mixed preparations also update correctly on an outcome: the conditioned
  ensemble is the Bayes posterior; at rank one **the record, not the pedigree, fixes the
  post-state**, and on a degenerate outcome the conditioned mixture is the Bayes mixture
  of the block posts — the density-operator update `ρ ↦ ΠᵢρΠᵢ/Tr(ρΠᵢ)` realised
  dynamically at every rank (`mixed_join_luders`, 2026-08-06);
- **wavefunction collapse as a theorem** — the post-measurement state update (the Lüders
  rule) falls out as a pushforward of the dynamics rather than being postulated; the harder
  *degenerate* case is realised on a companion projective-join witness, now packaged as one
  closure on one protocol (records, exclusivity, persistence, Liouville, coarse Born, and the
  ψ-dependent update together), and the **smooth horn carries the update too**
  (2026-08-05): the record stroke composed with a record-triggered relocation on one arena,
  the whole composite measure-preserving, with the conditioned post-measurement marginal
  **exact** — the `ε` lives only in *which* outcome occurs. The apparatus never destroys
  information: what looks like collapse is provably *relocation with storage*;
- **measurement dynamics from every side of a proven trade-off** — a machine-checked no-go
  shows that continuity and records that are exact **everywhere** cannot both hold. The corpus
  holds three witness families, and each pays exactly one price — a **trilemma**: *seams*
  (exact-record witnesses, provably not continuous flows); *`ε`-Born* (a smooth witness — a
  projective pointer whose propagator is continuous in time and state and satisfies the
  Schrödinger equation with an explicit Hermitian coupling — whose records and Born weights are
  exact up to a stated, tunable `ε`); and *Dirac calibration* (a continuous witness with exact
  Born and records exact off a two-point seam, at a point-calibrated ready state — with the
  caveat that in that witness "Born" is carried by a free cell-split parameter rather than
  by a preparation's moment map). No horn is
  canonical — and on the pointer's own record geometry the fourth combination is now
  **provably impossible** (`posMeasure_noRecord_pointer`, 2026-08-05: continuity, an open
  positive-width ready region, and two-outcome correlation force a positive-measure
  no-record set, so exact-a.e. records force Dirac calibration); whether that
  exhaustiveness extends to *every* conceivable arena remains research, not a claim
  (the tour has the comparison every measuring science meets);
- **the standard quantum canon** — entanglement and Bell/CGLMP/GHZ non-locality with
  no-signalling, contextuality, uncertainty, mixed states, quantum information theory,
  cryptographic protocols, Shor's algorithm, and quantum thermodynamics through Landauer's
  bound — each with its experimental face indexed in [`EMPIRICAL.md`](EMPIRICAL.md).

Two properties frame everything. First, the formalisation imports **zero axioms**: every
theorem reports exactly Lean's foundational triple (`propext`, `Classical.choice`,
`Quot.sound`) under `#print axioms`, and this is enforced *per theorem* by pinned checks in
CI. Second, the repository is aggressively honest about its boundaries — module headers carry
⚠️ honest-scope blocks, errors are corrected in place with dates, and automated guards scan
the prose for overclaims.

## Operational finite-QM closure (declared at `v1.1.0-finite-qm-closed`, 2026-08-06)

Fix the definition first, so the goalposts cannot move:

> **Operational finite QM** is the theory of density-operator preparations,
> finite-dimensional transformations and composites, finite-outcome measurements, Born
> probabilities, conditional updates and sequential statistics.

Every requirement of that definition is carried by named, axiom-pinned theorems already in
the corpus — **no additional capstone module exists or is needed**; the table below is the
role map:

| Requirement | Carried by |
|---|---|
| Pure and mixed states | `LF2` density operators; `mixedSwapPrep`/`eigRay` (spectral two-stage sampling) |
| Schrödinger dynamics and channels | `manyToOneSchrodingerSetup_both_pillars`, `rampedU_schrodinger`; `LF2/QuantumChannel` (Kraus/CPTP) |
| Composites and reduced states | `LF2/ReducedDensity`, the join/local arenas (`OnticComposite`, `LocalLuders*`) |
| Projective measurement, incl. degeneracy | `projectiveMeasurementCapstone` (rank-one + every basis + degenerate + smooth, one theorem) |
| POVMs and instruments | `naimarkInstrumentClosureCanonical` (dilation-relative, stated as physics not defect) |
| Born probabilities and frequencies | `join_sector_born`, `povm_sector_born_canonical`, `mixed_swap_sector_born`; LLN layers (`freq_tendsto_of_iid`, `pointer_born_frequency`) |
| Conditional and sequential update | `swap_luders_born`, `joinWitness_blockLuders`, `mixed_post_bayes`/`mixed_luders_followup`, `mixed_join_luders`, `csd_sequential_born`, `sequential_no_revival` |
| Marginal stability / no-signalling | `reduceA_localLudersOn_mixture` (every basis, dynamically) |

The closure is exactly as strong as its stated boundaries, which survive it unchanged: the
sector is posited (previous section); instruments are dilation-relative; the measurement
witnesses pay the trilemma's prices; the symplectic-manifold reading stays prose. What
remains in the repository is deliberately **outside** this definition: the CSD-foundations
frontier ([`specs/CSD-CHARTER.md`](specs/CSD-CHARTER.md) — the record-layer residue and the
fibre-mechanism question), which adds or removes no operational finite-QM theorem.
(Mathlib upstreaming and paper–corpus alignment were both moved off this repository's
queue 2026-08-06 — neither is a need of the repository; see `CONVENTIONS.md` §7 and
`BACKLOG` §B6/§C. The staging discipline, and the corpus's role as the source of truth
for what the papers owe it, both remain.)

## What is honestly assumed

The reconstruction is **conditional**: the sector itself is posited, never derived — CSD's
substrate, projection, and typicality reading enter as hypotheses on the types, and the
trials sample the ontic measure (see [`AXIOMS.md`](AXIOMS.md) §3 and the
[connectivity manifest](specs/connectivity-manifest.md), which governs every end-to-end
claim). The apparatus calibration of the exact-record witnesses is a named posit (the smooth witness
needs none — its preparation conditions on a ready region of positive measure). Each
measurement witness states what it gives up: the piecewise witnesses keep exact records but
are provably not continuous flows (the torus-flux correction of 2026-08-02); the smooth
pointer witness is Schrödinger-generated and continuous but carries records and Born only up
to its stated `ε`. That split is a proven trade-off, not a defect of either construction.
"Kähler" names the standard geometric reading of the measures; no
symplectic *manifold* is constructed in Lean (Mathlib has no manifold-forms API — though the
pointwise Kähler triple and the linear-level `X_H = ω⁻¹dH` duality, with the Schrödinger
field exhibited, are proved; see [`MATHLIB-GAPS.md`](MATHLIB-GAPS.md)). The full non-claims
list opens [`docs/TOUR.md`](docs/TOUR.md).

## Where to go next

| If you want… | Read |
|---|---|
| The precise claims, theorem names, results table, and the measurement story | [`docs/TOUR.md`](docs/TOUR.md) |
| A reading path through one sector — foundations, dynamics, measurement, entanglement, quantum information, crypto, algorithms, thermodynamics | [`docs/PATHS.md`](docs/PATHS.md) |
| Every experiment, in both branches (QM proof + CSD ontic twin) | [`EMPIRICAL.md`](EMPIRICAL.md) |
| What is assumed vs. proved; the per-theorem axiom ledger | [`AXIOMS.md`](AXIOMS.md) |
| The A1–A7 axiom-level audit of the reconstruction | [`specs/reconstruction-status.md`](specs/reconstruction-status.md) |
| Mathlib gaps this project hit, and what's staged for upstream | [`MATHLIB-GAPS.md`](MATHLIB-GAPS.md) |
| What is open, with effort grades | [`specs/BACKLOG.md`](specs/BACKLOG.md) |
| How the code is organised and disciplined | [`CONVENTIONS.md`](CONVENTIONS.md), [`specs/INDEX.md`](specs/INDEX.md) |

## Verify it yourself

```bash
lake exe cache get       # fetch Mathlib build cache
lake build               # the corpus (root target)
lake build CsdLeanTests  # the axiom audit — REQUIRED: the root target does NOT run it
./scripts/check-claims.sh  # the epistemic-overclaim guard
```

Both build targets must be green; the second executes every `#print axioms` pin. CI runs all
of the above on every push.

## Layout

| Path | Contents |
|---|---|
| `CsdLean4/LF1/`–`LF6/` | The layered build-up: typicality, operational layer, the singlet chain, the Born-from-volume engine + dynamics spine, measurement dynamics, entangled de-isolation |
| `CsdLean4/SigmaLayer/` | The projective-sector ontology: record layer, the dynamical measurement arc, the unified and join arenas, the capstones |
| `CsdLean4/Empirical/` | `QM/` (validity regression suite) and `CSD/` (ontic twins) |
| `CsdLean4/Thermo/` | Thermodynamics TH1–TH4 |
| `CsdLean4/Mathlib/` | CSD-free staging for upstream |
| `CsdLean4/Tests/` | `AxiomAudit.lean` — the pin ledger |
| `docs/`, `specs/` | The tour and sector paths; charter, status maps, plans, backlog, archives |

## History

| Tag | Milestone |
|---|---|
| `v0.6.0-context-fixed-a7` | Context-fixed basins; the fibred A7 realisation |
| `v0.7.0-dynamical-measurement` | The dynamical arc through rank-one Lüders |
| `v1.0.0-finite-qm-closure` | The combining capstone (`CsdFiniteQMClosure`) |
| `v1.0.1-luders-covariance` | Unified arena; degenerate Lüders closed on the join; the covariance law |
| `v1.0.2-smooth-witness` | The compact Kähler pointer witness: Schrödinger-generated measurement dynamics, continuous in time and state, Born up to `ε` |
| `v1.0.3-measurement-capstone` | The projective-measurement capstone (four closures, one theorem); dynamical no-signalling in every basis; the eraser as a process with statistical irreversibility; mixed preparations |
| `v1.0.5-trilemma` | POVM/instrument dynamics by Naimark dilation; the degenerate one-protocol package; the outcome-conditioned mixed update; `C^∞` transition profiles (Schrödinger at every time); and **the third measurement horn** — continuous, two-point seam, exact Born — turning the measurement fork into a **trilemma**: seams, `ε`-Born, or Dirac calibration |
| `v1.0.6-audited` | The audited corpus: 15 verified claim-level corrections (no false theorem among them), the guard family extended |
| `v1.1.0-finite-qm-closed` | **Operational finite-QM closure declared** (the section above). The week that earned the minor bump: the trilemma's third leg closed (`posMeasure_noRecord_pointer`); the smooth-witness Lüders composition (`pointer_luders_marginal`); degenerate-on-mixed (`mixed_join_luders`); sector-level POVM Born (`povm_sector_born_canonical`, from `v1.0.6`'s window); A4's linear fragment (`X_H = ω⁻¹dH` with the Schrödinger field exhibited); the library-grade standard (`CONVENTIONS` §9) with the review-surface auditor and the `Reversible/` API pass; two guard blind spots closed (scope-expiry ledger, instantiation-parity inventory) |

Versioning: patch increments for review-driven corrections, minor increments for closure
declarations. The project develops in dated, review-driven increments; superseded documents
are archived, not rewritten — the previous README lives at
[`specs/archive/README-2026-07.md`](specs/archive/README-2026-07.md).
