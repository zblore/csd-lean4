# The detailed tour — claims, theorems, and the measurement story

*(The bridge page between the introductory [`README`](../README.md) and the modules. Everything
here names its theorem. Sector-by-sector reading paths: [`PATHS.md`](PATHS.md). The A1–A7
axiom-level audit: [`specs/reconstruction-status.md`](../specs/reconstruction-status.md).)*

## The claim, precisely

On the ontic surface `Σ = ℂℙ^{N-1} × T²` with its Liouville measure `μL = μ_FS ⊗ vol` and the
projection `π` to rays, the corpus machine-verifies — for every dimension `N`, every unit
preparation, and arbitrary Hermitian `H`:

- **isolated dynamics** projects to Schrödinger evolution `exp(-itH)` on rays
  (`projectedFlow_schrodinger_form`, instantiated non-trivially on `manyToOneSchrodingerSetup`);
- **the Born rule is a theorem**: `‖⟨eᵢ,ψ⟩‖²` is a Fubini–Study typicality volume,
  Gleason-free, POVMs included (`fs_born_volume_ratio_N`, `povm_born_frequency_volume`), with
  i.i.d. frequencies converging to it almost surely;
- **measurement is a process**: an explicit measure-preserving propagator carries a
  positive-measure apparatus-ready state into created, persistent, mutually exclusive records
  whose outcome sectors carry exactly the Born weights (`SwapMeasurementClosure`,
  `swap_sector_born`);
- **the state update is a pushforward theorem**: rank-one Lüders (`swap_luders_born`), and —
  via the projective join `ℙ(ℂ^{N+N})` — **degenerate** Lüders (`joinWitness_blockLuders`
  inhabits `BlockLudersObligation`), each through Liouville-preserving dynamics;
- **the apparatus basis is not preferred structure**: the full measurement closure holds for
  every orthonormal basis (`measurement_covariance`);
- **one arena carries all of it** (`unifiedArenaClosure`): the isolated flow and the
  record-creating propagator preserve the *same* Liouville measure, and the
  isolate → measure → isolate round trip is a theorem (`arena_round_trip`).

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
| Contextuality, Bell, Tsirelson, uncertainty, thermodynamics TH1–TH4 | see [`EMPIRICAL.md`](../EMPIRICAL.md) and the module headers | `Empirical/…`, `Thermo/…` |

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

## Three reading pathways, by reader

**For the physicist** — what does CSD claim and what is actually proved?
1. [`specs/CSD-CHARTER.md`](../specs/CSD-CHARTER.md) — the ontology and the anti-drift frame.
2. [`specs/reconstruction-status.md`](../specs/reconstruction-status.md) §2a — the A1–A7
   audit; as of 2026-08-02 it has **no unscoped open rows**.
3. `CsdLean4/SigmaLayer/GlobalBasin.lean` — measurement partitions fixed by the apparatus.
4. `CsdLean4/SigmaLayer/SwapLuders.lean` → `UnifiedArena.lean` → `JoinLuders.lean` — the
   measurement story above, in code.
5. [`EMPIRICAL.md`](../EMPIRICAL.md) — every flagship experiment, QM proof + CSD ontic twin.

**For the Lean/Mathlib reader** — how is it built and enforced?
1. [`CONVENTIONS.md`](../CONVENTIONS.md) — the three-category discipline and naming rules.
2. [`AXIOMS.md`](../AXIOMS.md) §0 — axioms vs. structural posits vs. foundational triple.
3. `CsdLean4/Tests/AxiomAudit.lean` + `scripts/check-claims.sh` — the enforcement: per-theorem
   `#print axioms` pins as `#guard_msgs`, and an epistemic-overclaim scanner over the docs.
4. `CsdLean4/Mathlib/` + [`MATHLIB-GAPS.md`](../MATHLIB-GAPS.md) — the staged upstream
   candidates and the library gaps they answer.

**For the skeptic** — where are the boundaries, and does the repo respect them?
1. [`AXIOMS.md`](../AXIOMS.md) — start with what is assumed.
2. The five no-gos, in order: `no_everywhere_correlation`, `no_exact_collapse`,
   `shearEvolve_not_continuous`, `shear_base_marginal_unchanged`, `swap_not_blockLuders`
   (plus `SectorPostulateNoGo` for the sector-origin question). Each is load-bearing.
3. The ⚠️ **Honest scope** blocks in every module header — the corpus's standing convention.
4. [`specs/BACKLOG.md`](../specs/BACKLOG.md) — the canonical open-items list, with effort
   grades.
5. The dated-corrections convention: errors are corrected *in place with dates*, never
   silently (see `specs/archive/` and the correction notes throughout the docs).

## Status and open work

The A1–A7 reconstruction map has no unscoped open rows
([`specs/reconstruction-status.md`](../specs/reconstruction-status.md) §2a). The dynamical
measurement layer is complete through degenerate Lüders and unitary covariance; its two
recorded extensions are mixed preparations and POVM/instrument dynamics. The empirical suite
covers every flagship test on both branches. Connectivity claims are governed by
[`specs/connectivity-manifest.md`](../specs/connectivity-manifest.md) — nothing here may be
read as stronger than a CONNECTED row there. Open work:
[`specs/BACKLOG.md`](../specs/BACKLOG.md) (canonical), with the foundations frontier mapped in
[`specs/sigma-fibre-contextuality.md`](../specs/sigma-fibre-contextuality.md).
