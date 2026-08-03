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
  Gleason-free, POVMs included (`fs_born_volume_ratio_N_uncond` — every unit preparation,
  vanishing weights included — and `povm_born_frequency_volume`), with
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
- **one arena carries isolated dynamics plus the complete rank-one measurement
  reconstruction** (`unifiedArenaClosure`): the isolated flow and the record-creating
  propagator preserve the *same* Liouville measure, and the isolate → measure → isolate round
  trip is a theorem (`arena_round_trip`). The degenerate update runs on the companion
  projective-join witness; a single capstone bundling rank-one, all bases, and degenerate is a
  recorded open item.
- ★★★ **one theorem now carries the whole projective-measurement layer**
  (`projectiveMeasurementCapstone`, `SigmaLayer/MeasurementCapstone.lean`): for every
  Hermitian generator, base point, and unit preparation — rank-one on the unified arena,
  the six-fact closure in **every** apparatus basis, the **complete degenerate package on
  one protocol** for every block structure (records, exclusivity, persistence, Liouville,
  the coarse Born mass, ψ-dependent Lüders — `DegenerateMeasurementClosure`, upgraded
  2026-08-03), the smooth `ε`-horn, and its Schrödinger generation. The fields quantify
  over different witnesses by design (the two-horn framing); new prose cites this theorem
  and the constituent closures remain as the construction record;
- **no-signalling holds dynamically, in every basis** (`reduceA_localLudersOn_mixture`,
  with the local-measurement-is-block-measurement bridge `toComposite_blockProj` and the
  join witness supplying the post-states): the Born-weighted mixture of local marginals
  after a distant measurement equals the marginal before — the distant party's outcome
  *and basis choice* are invisible. **Mixed preparations** run through the same dynamics:
  `mixedSwapPrep ρ (outcomeSector i) = Tr(ρ|eᵢ⟩⟨eᵢ|)` (`mixed_swap_sector_born`), and the
  outcome-conditioned update is delivered too: the post-ensemble is the Bayes-posterior
  mixture (`mixed_post_bayes`), and at rank one **the record erases the classical
  ignorance** — follow-up statistics equal the pure Lüders update's
  (`mixed_luders_followup`);
- **the quantum eraser is a process, and records are irreversible**: the mark stroke
  produces which-path states with flat statistics at every phase (`marked_no_fringe`);
  the erase stroke on the *coherent* state produces exactly the conditioned fringe states
  (`erased_amp` — the dynamical post-states are `√2·eraserOut`, dark zero included);
  and erasing **after** the mark record revives nothing (`sequential_no_revival`) —
  interference is recoverable only before a record exists;
- **POVMs and instruments are dynamical too** (`povm_selector_born`, `povm_instrument`,
  `naimarkInstrumentClosureCanonical`, `SigmaLayer/PovmDynamics.lean`): Naimark-dilate and
  run the *existing* degenerate record protocol on the dilated arena — the ancilla block
  structure IS `localBlock`, so no new dynamics or sectors are needed. Outcome sectors
  carry `⟨ψ, Eᵢ ψ⟩` exactly, and the post-states the join witness delivers are the
  Naimark–Lüders instrument posts `Πᵢ(Vψ)`. Every POVM, via the canonical dilation
  (the instrument is dilation-relative — a POVM does not determine its instrument);
- **measurement dynamics has a smooth horn** (`smoothWitnessClosure`,
  `SigmaLayer/PointerBorn.lean`): on the pointer arena `ℂℙ^{N-1} × T² × ℂℙ^N`, one witness
  simultaneously carries a measurement protocol whose two-time law is the exponential group
  property, a propagator **jointly continuous in time and state**
  (`continuous_pointerRampedEvolve`), Liouville preservation, a positive-measure ready state
  with no Dirac calibration posit, record creation with the ontic sector selecting the
  outcome, structural persistence, and the Born sandwich
  `rⱼ − 2ε ≤ sector ≤ rⱼ + 2(N−1)ε`. On the interaction window the propagator satisfies the
  **Schrödinger equation** with the explicit Hermitian coupling `H_eff`
  (`rampedU_schrodinger`) — the Hamiltonian-generation statement at the formalisable level.
  *Precision (2026-08-03, fourth external review): the generation is **fibrewise** — the
  joint-arena flow's register back-reaction is suppressed by design
  (`pointerEvolve_base_marginal_unchanged` is the fingerprint; `ι_Vω ≠ d𝓗` on the
  ε-collars, genuinely Hamiltonian off them), and the original trapezoid weight/ramp
  ingredients are proved `Continuous`, not `C^∞` — *discharged same day at the ingredient
  level*: `PointerSmoothProfile.lean` provides `Real.smoothTransition` profiles with the
  identical plateau interface, a `C^∞` weight lift (`contDiff_smoothArcWeight_lift`), and
  the Schrödinger equation at **every** time (`smoothRampedU_schrodinger`). The fibrewise
  (not joint-arena Hamiltonian) character is unchanged; see `PointerGeneration.lean`'s
  honest-scope block.*

## The results, by pillar

| Reconstructed pillar | Headline theorem | Module |
|---|---|---|
| Schrödinger evolution from the sector flow | `projectedFlow_schrodinger_form`, `manyToOneSchrodingerSetup_both_pillars` | `LF4/PhaseLift`, `LF4/…` |
| Born rule as FS typicality volume (all `N`, POVMs, zero weights included) | `fs_born_volume_ratio_N_uncond`, `povm_born_frequency_volume` | `LF4/…` |
| Fubini–Study bridge `π_*μL = μ_FS` | `productSector_hasFubiniStudyPushforward`, `arenaRay_pushforward` | `SigmaLayer/MeasureBridge`, `UnifiedArena` |
| Context-fixed measurement partitions (Paper C A7) | `globalBasin_born`, `globalBasin_prob` | `SigmaLayer/GlobalBasin` |
| Records created, persistent, exclusive — dynamically | `SwapMeasurementClosure` / `swapMeasurementClosure` | `SigmaLayer/SwapClosure` |
| Dynamical Born (outcome-sector measure = Born weight) | `swap_sector_born`, `sector_born_ctx` | `SigmaLayer/SwapClosure`, `RotatedSwap` |
| Rank-one Lüders as pushforward | `swap_luders_born` | `SigmaLayer/SwapLuders` |
| Degenerate Lüders (the projective join) | `joinWitness_blockLuders`, `join_block_luders`, `joinSwap_measurePreserving` | `SigmaLayer/JoinLuders`, `JoinArena` |
| Unitary covariance of measurement | `measurement_covariance` | `SigmaLayer/RotatedSwap` |
| One arena, one Liouville measure family (rank-one tier) | `unifiedArenaClosure`, `arena_round_trip` | `SigmaLayer/UnifiedArena` |
| Smooth measurement dynamics: Schrödinger-generated, jointly continuous | `rampedU_schrodinger`, `continuous_pointerRampedEvolve` | `SigmaLayer/PointerGeneration`, `PointerProtocol` |
| The ε-Born sandwich and the smooth-horn closure | `pointer_born_lower`/`pointer_born_upper`, `smoothWitnessClosure` | `SigmaLayer/PointerBorn` |
| ★★★ The projective-measurement capstone (five fields, one theorem) | `projectiveMeasurementCapstone` | `SigmaLayer/MeasurementCapstone` |
| The degenerate one-protocol package; the coarse dynamical Born mass | `degenerateMeasurementClosure`, `join_sector_born` | `SigmaLayer/JoinClosure` |
| Dynamical no-signalling, every basis; local = block-degenerate | `reduceA_localLudersOn_mixture`, `toComposite_blockProj` | `SigmaLayer/LocalLudersBasis`, `LocalBlockBridge` |
| The eraser as a process; statistical irreversibility of records | `erased_amp`, `erased_rate`, `sequential_no_revival` | `Empirical/CSD/EraserDynamics`, `EraserSequential` |
| Mixed preparations: the mixed dynamical Born rule | `mixed_swap_sector_born` | `SigmaLayer/MixedSwap` |
| The outcome-conditioned mixed update: Bayes posterior + rank-one collapse of ignorance | `mixed_post_bayes`, `mixed_luders_followup` | `SigmaLayer/MixedLuders` |
| The dynamical POVM Born rule; the Naimark–Lüders instrument | `povm_selector_born`, `povm_instrument`, `naimarkInstrumentClosureCanonical` | `SigmaLayer/PovmDynamics` |
| `C^∞` transition profiles: smooth weights (universal-cover `C^∞`) and Schrödinger at every time | `contDiff_smoothArcWeight_lift`, `smoothRampedU_schrodinger` | `SigmaLayer/PointerSmoothProfile` |
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

1. **Constraints before construction.** `no_everywhere_correlation`: a continuous propagator
   cannot correlate everywhere — an exceptional set is forced (though not, as first over-read,
   discontinuity itself). `no_exact_collapse`: measure-preserving
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
8. **Classification** (`ShearDiscontinuity`, `PiecewiseHamiltonian`): what the exact-record
   witness's dynamics provably is — a piecewise rigid **symplectic** translation with null
   seam set (*not* globally Hamiltonian: the torus-flux correction of 2026-08-02). That
   raised the question the final step answers.
9. **The smooth horn** (`PointerArena` → `PointerGeneration`, eight modules): replace the
   torus register with a projective pointer `ℂℙ^N`, and the seam-jumping readout with a
   continuously modulated Hermitian coupling. The propagator becomes a ramped exponential —
   jointly continuous in time and state, Liouville-preserving, Schrödinger-generated
   (`rampedU_schrodinger`) — that lands ready states in the record regions with the ontic
   sector selecting the outcome, at the price of a stated `ε` in records and Born
   (`smoothWitnessClosure`). The trade-off forced by `no_everywhere_correlation` is now held
   from **both ends**, each machine-checked: exact records with seams, or seamless dynamics
   with `ε`. *(Precision, 2026-08-03: the no-go rules out **everywhere**-exact records
   under continuity; it does not exclude a third option — continuous dynamics with records
   exact off a* **null** *seam, devil's-staircase style, with exact Born. That is a
   recorded candidate brick, not a proved impossibility.)*

### Which horn is the right one?

Neither — and that is a settled framing (author decision, 2026-08-03), not an open question.
`no_everywhere_correlation` rules out **everywhere**-exact records for any continuous
dynamics on a connected state space, and every measuring science has met that constraint.
(*Precision added 2026-08-03, fourth external review: the two horns below are the two
answers the corpus has formalised, not a proven exhaustive dichotomy — a continuous witness
with records exact off a **null** seam is not excluded and is a recorded candidate brick.*) Digital
electronics keeps continuous dynamics and engineers the `ε`: flip-flop *metastability* is an
unresolved needle between the marks, its probability driven down exponentially with settling
time — the classical twin of our no-go is Lamport's *Buridan's Principle* (1984), found by
people building arbiter circuits. Thermodynamics keeps the exact jump and admits it is the
infinite-size idealisation of a steep continuous crossover — bubble chambers and Geiger
counters "jump" by phase transitions that are sharp only in the thermodynamic limit. Control
engineering trades single-valued readout for hysteresis (Schmitt triggers); neurons near
firing threshold do the same. Textbook QM alone promoted the jump to an *axiom* — collapse —
instead of modelling the apparatus. The corpus's two witness families are these two universal
answers, formalised: reach for the exact-record witnesses when the analysis needs sharp
records (the operational closures do), and for the smooth witness when it needs honest
Hamiltonian dynamics (the papers' architecture does). Neither is "the" CSD measurement; the
trade-off theorem is.

## Three reading pathways, by reader

**For the physicist** — what does CSD claim and what is actually proved?
1. [`specs/CSD-CHARTER.md`](../specs/CSD-CHARTER.md) — the ontology and the anti-drift frame.
2. [`specs/reconstruction-status.md`](../specs/reconstruction-status.md) §2a — the A1–A7
   audit. A2's **Hamiltonian-generation** sub-question — reopened 2026-08-02 on the
   torus-flux correction — was closed 2026-08-03 by the smooth pointer witness, at the
   formalisable level; §2a carries the full audit trail and the scoped residue.
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

The A1–A7 reconstruction map's last genuinely open row — A2's Hamiltonian-generation
sub-question — was closed 2026-08-03 at the formalisable level by the smooth pointer witness
([`specs/reconstruction-status.md`](../specs/reconstruction-status.md) §2a; the
symplectic/moment-map *reading* of the generator remains the same scoped prose boundary as
A1/A3). The dynamical measurement layer is complete through the capstone — rank-one, every basis,
degenerate blocks, the smooth horn, mixed preparations, dynamical no-signalling, the
eraser process with its irreversibility theorem, and POVM/instrument dynamics via Naimark
dilation; its recorded extensions are the smooth-witness Lüders composition and the
ε-Born frequency layer. The empirical suite
covers every flagship test on both branches. Connectivity claims are governed by
[`specs/connectivity-manifest.md`](../specs/connectivity-manifest.md) — nothing here may be
read as stronger than a CONNECTED row there. Open work:
[`specs/BACKLOG.md`](../specs/BACKLOG.md) (canonical), with the foundations frontier mapped in
[`specs/sigma-fibre-contextuality.md`](../specs/sigma-fibre-contextuality.md).
