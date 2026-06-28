# LF6 — the entangled de-isolation tier (D1 frontier) — plan

**Status: A.1 + A.2 + A.3 DONE 2026-06-28 (the entangled-tier A-stage is complete).** LF6 is the first concrete attack on the entangled / non-local
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

### LF6-A.2 — the full singlet de-isolation flow (DONE 2026-06-28)
`CsdLean4/LF6/SingletDeisolationFlow.lean` (namespace `CSD.LF6`), foundational-triple-only, 5
AxiomAudit pins. The dynamical realisation on `Σ' = ℂℙ¹⁵ = ℙ(EuclideanSpace ℂ (Fin 16))`
(`16 = 4·4`), built on the clean construction path (LF5 @ N=4 + LF3 + A.1), NOT a from-scratch
ℂℙ¹⁵ build:
- `singletDeisolationFlow := measurementFlow 4 finProdFinEquiv` with `singletDeisolation_measurePreserving`
  / `singletDeisolation_ne_id` (inherited from LF5-B); the flow is LOCAL (the LF5 de-isolation at N=4).
- `nudgedSinglet a b` — the prepared state `φ = (U_A^x⊗U_B^y)† ψ⁻`, the singlet in the rotated
  axis-context basis, in coordinates `φ_{stIdx(s,t)} = ⟨ψ⁻, singletJointEig s t a b⟩`; `nudgedSinglet_norm`
  (unit, `∑ P_st = 1`), `nudgedSinglet_born` (`‖⟨e_{stIdx(s,t)}, φ⟩‖² = P_st`, the unitary-invariance +
  LF3 `singletJointEig_born` step).
- `singletDeisolation_pointer_volume` (the headline) — joint `BornRegion` pointer-block `(s,t)` FS
  volume `= P_st a b s t`, COMPOSING `LF5.vnDilation_pointer_volume` @ N=4 with `nudgedSinglet_born`
  (which behind `singletJointEig_born` is `MeasurementJointEig.born_eq_P_st`). Born = volume IMPORTED
  from the DH/FS-volume engine, not re-derived.
- `singletDeisolation_frequency` — a.s. pointer-block frequency → `P_st` (`LF5.vnDilation_pointer_frequency`
  @ N=4 on `BornRegionUncond`).
- `singletDeisolation_blockVolume_correlation` — the carve's block-volume correlation is the singlet's
  `−a·b`; `singletDeisolation_carve_contextual` — ROUTES THROUGH A.1 `no_product_partition_realises_singlet`:
  no setting-local ±1 product partition reproduces it, so the carve is contextual (safety anchor).
- `singletDeisolation_flow_capstone` — 6-conjunct (≠ id ∧ FS-preserving ∧ pointer volume = P_st ∧
  block correlation = −a·b ∧ a.s. freq → P_st ∧ carve contextual via A.1).
The carve is the joint moment subdivision, never a setting-local `{ptr_A=i}∩{ptr_B=j}` product region.
Generic context (`hgen : P_st > 0`, every Bell setting). Flow factorisation `Φ = Φ_A ⊗ Φ_B` DEFERRED to
LF6-A.3 (the heavy tensor reindex; A.1 already shows local-flow ⊕ contextual-carve is consistent, so
A.2 is not blocked on it). Residue A5 (entangled sector posited).

**Auditor faithfulness note (A.2, recorded 2026-06-28, honest not a defect).** The capstone's
contextuality conjunct (`singletDeisolation_carve_contextual`) carries A.1's content (no setting-local
±1 product partition achieves the `−a·b` correlation); the A.2-specific increment is the separate
conjunct that the exhibited carve *achieves* `−a·b` (`singletDeisolation_blockVolume_correlation`). The
bridge "the exhibited carve is therefore not a product partition" is a juxtaposition of the two
conjuncts, not one composed theorem — because the carve (a `BornRegion` subdivision of `ℂℙ¹⁵` under FS
measure) and product partitions (LHV models on an abstract `Λ`) live in genuinely disjoint types. That
disjointness IS the contextuality (a contextual carve cannot be written as `IsProductPartition RA RB`),
so the informality is the honest content, not a gap. Optional future strengthening: a corollary feeding
the carve's correlation into A.1 under a formal `Λ`-realisation, if/when the carve is realised as a
`Λ`-measure.

**OPEN DESIGN QUESTION for A.2 — RESOLVED 2026-06-28 (user: "measurement is contextual, continue").**
Does the de-isolation flow factor as `Φ = Φ_A ⊗ Φ_B`? Resolution: the FLOW is local (LF5 de-isolation
at N=4); the CARVE (joint `BornRegion` moment-subdivision) is contextual. A.2 built the local flow +
contextual carve; the explicit flow-factorisation `Φ = Φ_A ⊗ Φ_B` (the tensor reindexing) is DEFERRED
to LF6-A.3. Original framing retained below.
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

### LF6-A.3 — the local product de-isolation flow (DONE 2026-06-28)
`CsdLean4/LF6/LocalDeisolationFlow.lean` (namespace `CSD.LF6`), auditor-SOUND, foundational-triple-only,
4 AxiomAudit pins. Exhibits a genuinely LOCAL product de-isolation `V_loc = V_A ⊗ V_B` (each wing an
N=2 LF5 `vnDilationV`) realising the SAME joint singlet measurement, so the de-isolation needs NO
non-local interaction; the non-locality is entirely in the contextual carve (A.2) and the entangled
preparation (A5).
- `localDeisolation_factorises` — `V_loc` is a genuine Kronecker product of the two wing de-isolations
  (verified `rfl`; the reindex equivs are genuine bijections).
- `localDeisolation_pullback` — `(V_loc)ᴴ Π_{(i,j)} V_loc = |e_{(i,j)}⟩⟨e_{(i,j)}|`, GENUINELY composing
  the two per-wing LF5 `vnDilationV_pullback` via `conjTranspose_kronecker`/`mul_kronecker_mul`/
  `single_kronecker_single` (no `decide`/brute-force).
- `localNaimark : NaimarkDilation (basisPOVM 4)` (+ `localDeisolation_isom`) — the product dilation is a
  valid Naimark dilation, so the LF4 POVM-volume engine applies.
- `localDeisolation_pointer_volume` — the local product flow's pointer-block `(i,j)` FS volume `= P_st`,
  routing `povm_born_eq_dilated_volume_uncond` + `nudgedSinglet_born` (LF3). Same `hgen` (generic Bell
  setting) as A.2.
- `localDeisolationFlow_measurePreserving` / `_ne_id` — the projectivized product flow `U_A⊗U_B` is
  FS-measure-preserving and `≠ id`.
- `localDeisolation_capstone` — 5-conjunct (factorises ∧ ≠ id ∧ measure-preserving ∧ pointer volume =
  P_st ∧ valid Naimark).
HONEST framing honored: A.3 does NOT claim the A.2 `ℤ/4`-adder flow factors (it does not — `ℤ/4 ≠
ℤ/2×ℤ/2`); it builds a SEPARATE manifestly-local product flow. Born = FS volume imported (LF5/DH/
POVM-Naimark), not re-derived.
**Auditor Minor (completeness, not soundness; follow-up):** the capstone bundles the local flow
`Φ_loc` (≠id, measure-preserving) and the local dilation `V_loc` (the volumes), but has NO lemma tying
them (`Φ_loc[ψ⊗a₀] = [V_loc ψ]`), unlike LF5's `measurement_flow_realises_dilation` conjunct. The link
is true and routine (`vnDilationV = vnUnitary ∘ embedGround`); add `localDeisolationFlow_realises_localNaimark`
as a 6th conjunct (lift LF5 `measurement_flow_realises_dilation` through `kronecker` + `jointFlowEquiv`)
to make "the LOCAL flow realises the singlet" fully a theorem.

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
