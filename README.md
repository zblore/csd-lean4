# csd-lean4

[![CI](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalisation of **Constraint-Surface Dynamics (CSD)** — a reconstruction
of finite-dimensional quantum mechanics from a single deterministic ontic model.

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
  other, and the outcome statistics are exactly Born;
- **wavefunction collapse as a theorem** — the post-measurement state update (the Lüders
  rule) falls out as a pushforward of the dynamics rather than being postulated; the harder
  *degenerate* case is realised on a companion projective-join witness. The apparatus never destroys information: what looks like
  collapse is provably *relocation with storage*;
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

## What is honestly assumed

The reconstruction is **conditional**: the sector itself is posited, never derived — CSD's
substrate, projection, and typicality reading enter as hypotheses on the types, and the
trials sample the ontic measure (see [`AXIOMS.md`](AXIOMS.md) §3 and the
[connectivity manifest](specs/connectivity-manifest.md), which governs every end-to-end
claim). The apparatus calibration is likewise a named posit, and the current measurement witness is a
*piecewise rigid symplectic translation* — measure-preserving and machine-classified, but not
a globally Hamiltonian flow (the torus-flux correction of 2026-08-02); building the genuinely
Hamiltonian compact-pointer witness is the reopened row at the top of the backlog. "Kähler" names the standard geometric reading of the measures; no
symplectic manifold is constructed in Lean (Mathlib has no such API — see
[`MATHLIB-GAPS.md`](MATHLIB-GAPS.md)). The full non-claims list opens
[`docs/TOUR.md`](docs/TOUR.md).

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

Versioning proceeds in patch increments. The project develops in dated, review-driven
increments; superseded documents are archived, not rewritten — the previous README lives at
[`specs/archive/README-2026-07.md`](specs/archive/README-2026-07.md).
