# csd-lean4

[![CI](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalisation of **Constraint-Surface Dynamics (CSD)**: finite-dimensional
quantum mechanics reconstructed as theorems about one ontic model.

*(This README was rewritten from a clean snapshot on 2026-08-02, after the dynamical-measurement
arc; the previous version is archived verbatim at
[`specs/archive/README-2026-07.md`](specs/archive/README-2026-07.md) per the repo's
dated-corrections convention.)*

## The claim

On the ontic surface `Σ = ℂℙ^{N-1} × T²` with its Liouville measure `μL = μ_FS ⊗ vol` and the
projection `π` to rays, the corpus machine-verifies — for every dimension `N`, every unit
preparation, and arbitrary Hermitian `H` — that:

- **isolated dynamics** projects to Schrödinger evolution `exp(-itH)` on rays
  (`projectedFlow_schrodinger_form`, instantiated non-trivially on `manyToOneSchrodingerSetup`);
- **the Born rule is a theorem**: the weight `‖⟨eᵢ,ψ⟩‖²` is a Fubini–Study typicality volume,
  Gleason-free, POVMs included (`fs_born_volume_ratio_N`, `povm_born_frequency_volume`), with
  i.i.d. frequencies converging to it almost surely;
- **measurement is a process**: an explicit measure-preserving propagator carries a
  positive-measure apparatus-ready state into created, persistent, mutually exclusive records
  whose outcome sectors carry exactly the Born weights (`SwapMeasurementClosure`,
  `swap_sector_born`);
- **the state update is a pushforward theorem**, not a postulate: rank-one Lüders
  (`swap_luders_born`), and — via the projective join `ℙ(ℂ^{N+N})` — **degenerate** Lüders
  (`joinWitness_blockLuders` inhabits `BlockLudersObligation`), each through
  Liouville-preserving dynamics;
- **the apparatus basis is not preferred structure**: the full measurement closure holds for
  every orthonormal basis (`measurement_covariance`);
- **one arena carries all of it** (`unifiedArenaClosure`): the isolated flow and the
  record-creating propagator preserve the *same* Liouville measure, and the
  isolate → measure → isolate round trip is a theorem (`arena_round_trip` — the record is a
  conserved coordinate of the isolated flow).

The formalisation imports **zero axioms**: every theorem in the corpus reports exactly
`[propext, Classical.choice, Quot.sound]` under `#print axioms`, enforced per-theorem by
`#guard_msgs` pins in `CsdLean4/Tests/AxiomAudit.lean` and by CI. The tree is `sorry`-free.

## What is NOT claimed

Read this before the results; it is what makes them meaningful.

1. **The sector itself is posited.** CSD's postulates — the substrate `(Σ, μL)` with a
   deterministic measure-preserving flow, the projection `π`, and probability read as
   typicality volume — are carried as hypotheses on the types, and every reconstruction
   theorem is conditional on them; the trials *sample* `μL` — the sector itself is posited,
   never derived from the flow. Σ is the floor: deriving it is a
   non-question (Paper C is a reconstruction, not a derivation). See
   [`AXIOMS.md`](AXIOMS.md) §3 and the SO-1 row of the
   [connectivity manifest](specs/connectivity-manifest.md).
2. **The apparatus calibration is a posit** (`AXIOMS.md` §3.8): the swap witness's bank starts
   at the outcome vertices, the join witness's slot starts block-supported. It is kept honest
   by two theorems: `collapse_accuracy_bound` (approximate calibration is *priced*), and
   `swap_not_blockLuders` (no fixed ray-level calibration can serve degenerate blocks — which
   is *why* the join arena exists).
3. **The measurement dynamics is piecewise Hamiltonian, not smooth.** The propagator is
   provably not continuous (`shearEvolve_not_continuous`), and this is *forced*: no continuous
   map can correlate a connected ready region with disjoint pointer regions
   (`no_everywhere_correlation`). The honest classification — continuous rigid-translation
   pieces on the basin cylinders, null seam set — is itself machine-checked
   (`shear_piecewise_hamiltonian`).
4. **"Kähler" is the mathematical reading, not a formalised manifold.** In Lean the measures
   are `fubiniStudyMeasure` and Haar products; no symplectic form or Kähler metric is
   constructed (Mathlib has no such API). The identification with Kähler/Liouville volume
   forms is standard differential geometry carried as prose (`AXIOMS.md` §3.1).
5. **Open items are named, not hidden.** The single canonical list is
   [`specs/BACKLOG.md`](specs/BACKLOG.md); headlines: mixed preparations and POVM/instrument
   dynamics in the dynamical model, Shor-9 concatenation, composable finite-key QKD, the
   Lindblad tier, and the foundations frontier
   ([`specs/sigma-fibre-contextuality.md`](specs/sigma-fibre-contextuality.md)).

## The results, by pillar

| Reconstructed pillar | Headline theorem | Module |
|---|---|---|
| Schrödinger evolution from the sector flow | `projectedFlow_schrodinger_form`, `manyToOneSchrodingerSetup_both_pillars` | `LF4/PhaseLift`, `LF4/…` |
| Born rule as FS typicality volume (all `N`, POVMs) | `fs_born_volume_ratio_N`, `povm_born_frequency_volume` | `LF4/…` |
| Fubini–Study bridge `π_*μL = μ_FS` | `productSector_hasFubiniStudyPushforward`, `arenaRay_pushforward` | `SigmaLayer/MeasureBridge`, `UnifiedArena` |
| Context-fixed measurement partitions (Paper C A7) | `globalBasin_born`, `globalBasin_prob` | `SigmaLayer/GlobalBasin` |
| Records created, persistent, exclusive — dynamically | `SwapMeasurementClosure` / `swapMeasurementClosure` | `SigmaLayer/SwapClosure` |
| Dynamical Born (outcome-sector measure = Born weight) | `swap_sector_born`, `sector_born_ctx` | `SigmaLayer/SwapClosure`, `RotatedSwap` |
| Rank-one Lüders as pushforward | `swap_luders_born` | `SigmaLayer/SwapLuders` |
| Degenerate Lüders (the projective join) | `joinWitness_blockLuders`, `join_block_luders`, `joinSwap_measurePreserving` | `SigmaLayer/JoinLuders`, `JoinArena` |
| Unitary covariance of measurement | `measurement_covariance` | `SigmaLayer/RotatedSwap` |
| One arena, one Liouville measure family | `unifiedArenaClosure`, `arena_round_trip` | `SigmaLayer/UnifiedArena` |
| Repeatability & sequential statistics | `csd_repeatability`, `csd_sequential_born` | `Empirical/CSD/SequentialMeasurement` |
| Mixed states, weights and frequencies | `mixed_ontic_born_weight`, `arena_mixed_born_frequency` | `SigmaLayer/MixedOntic`, `UnifiedArena` |
| Entanglement / non-locality / no-signalling | `no_product_partition_realises_singlet`, CGLMP ∀`d`, GHZ ∀`n` | `LF6/…` |
| Contextuality, Bell, Tsirelson, uncertainty, thermodynamics TH1–TH4 | see [`EMPIRICAL.md`](EMPIRICAL.md) and the module headers | `Empirical/…`, `Thermo/…` |

Historical capstones (`FiniteQMClosure`, `unified_projectiveSector_capstone`,
`measurement_flow_born_frequency`) stand unchanged; `unifiedArenaClosure` is their one-arena
successor, with an explicit field-by-field mapping table in `SigmaLayer/UnifiedArena.lean`.

## The story of measurement

The dynamical arc is the corpus's most instructive chain, because every negative result became
load-bearing:

1. **Constraints before construction.** `no_everywhere_correlation`: continuous propagators
   cannot make exact records — seams are forced. `no_exact_collapse`: measure-preserving
   dynamics cannot contract; collapse must be *relocation with storage*.
   `collapse_accuracy_bound`: approximate collapse is priced in ready-state improbability,
   forcing Dirac calibration.
2. **The shear** (`ShearWitness`) creates Born-weighted, persistent records from a ready
   state — and provably *cannot* collapse (`shear_base_marginal_unchanged`).
3. **The calibrated swap** (`SwapWitness`, `SwapLuders`) adds the record-triggered bank
   exchange: collapse as relocation, rank-one Lüders as a pushforward. Its own boundary:
   `swap_not_blockLuders` — no fixed calibration serves degenerate blocks, because the
   demanded post-state depends on the preparation.
4. **The wall, diagnosed** (`BlockCollapse`): the degenerate mechanism exists at the vector
   level (`componentSwap` — collapse with the residual stored), but its ray-pair descent
   loses the *relative phase*.
5. **The join** (`PhaseSlot`, `JoinArena`): keep the phase — the pair arena *is* the
   projective join `ℙ(ℂ^{N+N})`, the swap becomes a permutation unitary, Liouville
   preservation becomes FS unitary invariance, and the update is pointwise deterministic
   (`join_block_luders`).
6. **The protocol and the obligation** (`JoinProtocol`, `JoinLuders`): the join update runs in
   the standard record architecture, and `joinWitness_blockLuders` inhabits the very
   obligation the no-go had closed off — from a fixed calibration.
7. **Covariance** (`RotatedSwap`): all of it, in every orthonormal basis
   (`measurement_covariance`).
8. **Classification** (`ShearDiscontinuity`, `PiecewiseHamiltonian`): what kind of dynamics
   this is — piecewise Hamiltonian with a provably-forced null seam set. Stated, not hidden.

## Three reading pathways

**For the physicist** — what does CSD claim and what is actually proved?
1. [`specs/CSD-CHARTER.md`](specs/CSD-CHARTER.md) — the ontology and the anti-drift frame.
2. [`specs/reconstruction-status.md`](specs/reconstruction-status.md) §2a — the A1–A7 axiom
   audit; as of 2026-08-02 it has **no unscoped open rows**.
3. `CsdLean4/SigmaLayer/GlobalBasin.lean` — measurement partitions fixed by the apparatus.
4. `CsdLean4/SigmaLayer/SwapLuders.lean` → `UnifiedArena.lean` → `JoinLuders.lean` — the
   measurement story above, in code.
5. [`EMPIRICAL.md`](EMPIRICAL.md) — every flagship experiment, QM proof + CSD ontic twin.

**For the Lean/Mathlib reader** — how is it built and enforced?
1. [`CONVENTIONS.md`](CONVENTIONS.md) — the three-category discipline (Mathlib-staging / QM /
   CSD) and naming rules.
2. [`AXIOMS.md`](AXIOMS.md) §0 — axioms vs. structural posits vs. foundational triple.
3. `CsdLean4/Tests/AxiomAudit.lean` + `scripts/check-claims.sh` — the enforcement: per-theorem
   `#print axioms` pins as `#guard_msgs`, and an epistemic-overclaim scanner over the docs.
4. `CsdLean4/Mathlib/` — the staged upstream candidates: `Projectivization`
   topology/measure/Fubini–Study, the C¹ Stone theorem, the Duhamel bound, piecewise
   measure-preservation, quantum-information infrastructure (entropy, SSA scaffold, channels,
   trace distance).

**For the skeptic** — where are the boundaries, and does the repo respect them?
1. [`AXIOMS.md`](AXIOMS.md) — start with what is assumed.
2. The five no-gos, in order: `no_everywhere_correlation`, `no_exact_collapse`,
   `shearEvolve_not_continuous`, `shear_base_marginal_unchanged`, `swap_not_blockLuders`
   (plus `SectorPostulateNoGo` for the sector-origin question). Each is load-bearing.
3. The ⚠️ **Honest scope** blocks in every module header — the corpus's standing convention.
4. [`specs/BACKLOG.md`](specs/BACKLOG.md) — the canonical open-items list, with effort grades.
5. The dated-corrections convention: errors are corrected *in place with dates*, never
   silently (see `specs/archive/` and the correction notes throughout the docs).

## Verify it yourself

```bash
lake exe cache get       # fetch Mathlib build cache
lake build               # the corpus (root target)
lake build CsdLeanTests  # the axiom audit — REQUIRED: the root target does NOT run it
./scripts/check-claims.sh  # the epistemic-overclaim guard
```

Both build targets must be green; the second executes every `#print axioms` pin. CI runs all
of the above on every push.

## Map of the repository

| Path | Contents |
|---|---|
| `CsdLean4/LF1/`–`LF3/` | Typicality/trials layer; operational layer (effect algebras, the de-axiomatised Busch–Gleason); the singlet chain |
| `CsdLean4/LF4/` | The Born-from-volume engine (moment map, Duistermaat–Heckman, POVM/Naimark), the W-series dynamics spine, qubit A7 |
| `CsdLean4/LF5/`, `LF6/` | Measurement dynamics (von Neumann tier); entangled/non-local de-isolation (CGLMP, GHZ) |
| `CsdLean4/SigmaLayer/` | The projective-sector ontology (Paper C): record layer, dynamical measurement arc, unified arena, join arena, capstones |
| `CsdLean4/Empirical/` | Two branches: `QM/` (validity regression suite) and `CSD/` (ontic twins — Born values as volumes, sequential/dynamical entries) |
| `CsdLean4/Thermo/` | TH1–TH4: canonical typicality, second law, Gibbs, Landauer |
| `CsdLean4/Mathlib/` | CSD-free staging for upstream (Category 1) |
| `CsdLean4/Tests/` | `AxiomAudit.lean` — the pin ledger |
| `specs/` | Charter, status maps, plans, `BACKLOG.md`, archives — see [`specs/INDEX.md`](specs/INDEX.md) |

## Status, open work, history

**Status.** The A1–A7 reconstruction map has no unscoped open rows
([`specs/reconstruction-status.md`](specs/reconstruction-status.md) §2a). The dynamical
measurement layer is complete through degenerate Lüders and unitary covariance; its two
recorded extensions are mixed preparations and POVM/instrument dynamics. The empirical suite
covers every flagship test on both branches. Connectivity claims are governed by
[`specs/connectivity-manifest.md`](specs/connectivity-manifest.md) — nothing here may be read
as stronger than a CONNECTED row there.

**Open work.** [`specs/BACKLOG.md`](specs/BACKLOG.md) is the single canonical list. The
foundations frontier — where measurement contextuality lives in Σ's fibre for `N ≥ 3`, and
deriving the fibre mechanism from de-isolation dynamics — is mapped in
[`specs/sigma-fibre-contextuality.md`](specs/sigma-fibre-contextuality.md).

**Tags.**

| Tag | Milestone |
|---|---|
| `v0.6.0-context-fixed-a7` | Context-fixed basins; the fibred A7 realisation |
| `v0.7.0-dynamical-measurement` | The dynamical arc through rank-one Lüders |
| `v1.0.0-finite-qm-closure` | The combining capstone (`CsdFiniteQMClosure`) |
| `v1.0.1-luders-covariance` | Unified arena; degenerate Lüders closed on the join; the covariance law |

The project develops in dated, review-driven increments; external reviews and their
corrections are folded in with in-place dated notes. Version numbering proceeds in patch
increments (`1.0.1`, `1.0.2`, …).
