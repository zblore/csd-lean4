# LF6 — the entangled de-isolation tier (D1 frontier) — plan

**Status: A.1 DONE 2026-06-28.** LF6 is the first concrete attack on the entangled / non-local
stratum of D1 (measurement dynamics), the deepest open debt. LF5 closed the single-system projective
measurement-dynamics tier (`Φ_vN ≠ id` de-isolation flow on the dilated projective space). LF6
extends de-isolation to the entangled case, where Bell forces non-locality. Target: a deterministic,
FS-measure-preserving de-isolation account that reproduces the LF3 singlet kernel `P_st`, with the
non-locality located honestly and no-signalling proven.

## The conceptual frame (settled in design, 2026-06-28)

- **The non-factorisation is in the Σ-volume engine, derived, not posited.** The moment-map /
  `BornRegion` engine reads the global entangled vector and returns joint weights `P_st(i,j)` that do
  not factor (`engine_joint_nonfactorises`), while its marginals do factor (`engine_marginal_factorises`,
  = no-signalling). The same engine that derives Born (the DH cluster) produces the entangled
  correlations; Born and non-locality are two outputs of one engine.
- **Contextuality is forced by Bell, not chosen.** A product (setting-local, non-contextual)
  outcome-partition of Σ is a deterministic LHV model; by `lhvCHSH_abs_le_two` it cannot reproduce the
  singlet's `2√2`. So any partition realising `P_st` must be jointly contextual. This is `LF6-A.1`'s
  `no_product_partition_realises_singlet`.
- **Mechanism: factorisation = measurement.** A product outcome-partition asserts setting-local
  definite values, which is a completed de-isolation. So factorisation cannot pre-exist the carve.
- **Nudge ≠ carve.** Pre-measurement unitary `Φ_U` volume reshaping (axis rotation, gates, the A1
  Ramsey phase flow) is available and reversible and produces no outcomes; the de-isolation carve is
  what produces pointer-definite outcomes. The context is set by a pre-measurement nudge; the carve
  follows it.
- **Residue = A5.** The entangled sector / the singlet's `Ω₀` is posited, not derived. LF6 threads
  dynamics through the entangled instance; it does not derive the entangled sector. A5 reduces to the
  deeper D1 strata.

## Stages

### LF6-A.1 — the forced-contextuality crux (DONE 2026-06-28)
`CsdLean4/LF6/ForcedContextuality.lean` (namespace `CSD.LF6`), auditor-SOUND, foundational-triple-only.
- `no_product_partition_realises_singlet` — no setting-local ±1 product partition of a shared
  probability space reproduces the singlet correlations (routes `ReproducesSinglet` → singlet CHSH
  `2√2` via `Bell.chsh_singlet_at_optimal_angles`, vs `E91.lhvCHSH_abs_le_two` ≤ 2). Both hypotheses
  proved load-bearing (auditor: `ReproducesSinglet` is satisfiable standalone by a non-±1 model, so
  the contradiction is genuinely the ±1/locality structure, not a trivial impossibility).
- `productPartition_nonvacuous` — product partitions exist (all-+1 reproduces a constant correlation),
  so the no-go is non-vacuous.
- `engine_joint_nonfactorises` — `P_st(i,j) ≠ P_A(i)·P_B(j)` (aligned axes: `P_st = 0 ≠ 1/4`).
- `engine_marginal_factorises` — marginals `= 1/2` both ways + no-signalling A/B (LF3 reuse).
Reuses `E91.lhvCHSH_abs_le_two`, `Bell.chsh_singlet_at_optimal_angles`, `LF3.P_st`/marginals; no Bell
re-proof, no kernel reinvention. 4 AxiomAudit pins.

### LF6-A.2 — the full singlet de-isolation flow (NEXT, planned)
The dynamical realisation on `Σ' = ℂℙ¹⁵ = ℙ(ℂ²⊗ℂ²⊗ℂ²⊗ℂ²)` (two qubits + two pointer ancillae):
1. Define the joint von Neumann de-isolation unitary (a `vnUnitary`-style adder on the 16-dim register)
   and lift `LF5.measurementFlow` to it; FS-measure-preserving, `≠ id`.
2. Pointer-block FS volume `= P_st`, by composing `LF5.vnDilation_pointer_volume` with
   `LF3.MeasurementJointEig.born_eq_P_st`.
3. a.s. pointer-block frequency convergence to `P_st` via `BornRegionUncond`.

**OPEN DESIGN QUESTION for A.2 (flagged by the A.1 expert + auditor, must resolve before building).**
Does the de-isolation flow factor as `Φ = Φ_A ⊗ Φ_B`?
- Design position (carve-out reading): the FLOW can be local (`Φ_A ⊗ Φ_B`, each wing's de-isolation a
  local process), with ALL the non-locality in the jointly-contextual outcome PARTITION (the carve),
  per A.1. No non-local interaction is needed; the correlations come from the engine reading the
  entangled state.
- Tension: the A.1 expert suggested A.2 should *exhibit that the flow does NOT factor* as the
  dynamical counterpart of the no-go. The auditor's safety check: confirm the A.2 partition realising
  `P_st` is genuinely contextual (entangled `Σ'`) and that the `vnDilation_pointer_volume ∘ born_eq_P_st`
  composition does NOT assume the product structure A.1 forbids — that is where a vacuity could re-enter.
- Resolution to settle first: a local flow `Φ_A ⊗ Φ_B` acting on the entangled preparation, followed by
  a jointly-contextual carve, is consistent with A.1 (the no-go is about the carve/partition, not the
  flow). The thing to PROVE in A.2 is that the carve realising `P_st` is the contextual one (its A-marginal
  region depends on the far setting while its volume does not), NOT a product partition. Build that
  contextuality witness before/with the pointer-volume composition, so A.2 cannot silently assume the
  forbidden factorisation. This is the genuinely new physics content of A.2.

### LF6-B and beyond (not started)
General-N entangled tier; the decoherence / partial-trace (open-system) stratum (D1b, system→environment
volume loss); threading `Φ` through the concrete entangled `SectorData` (D1c). A5 emergence (deriving the
entangled sector from the dynamics) is the downstream target that would retire the residue.

## Honest posture (carried into each file)
LF6 realises the singlet on a deterministic substrate and locates the non-locality precisely (in the
engine / contextual carve, derived; forced by Bell). It is a global-beable, jointly-contextual,
no-signalling account, the standard escape made measure-theoretic — NOT a Bell-local model and NOT a
Bell violation. The entangled sector (`Ω₀`, A5) is posited; LF6 supplies dynamics modulo A5, exactly as
Born is derived modulo A5.
