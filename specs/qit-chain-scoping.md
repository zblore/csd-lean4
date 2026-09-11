# From CSD's posits to the end of the QIT layer: scoping note

**Status:** SCOPED 2026-09-11, after a full anchoring survey of `CsdLean4/Mathlib/QuantumInfo/` (24 modules),
`Empirical/CSD/` (the QIT-touching twins), and the `LF2`/`SigmaLayer`/`RecordLayer` bridge modules. Every claim
below was read from theorem *types*, not headers. Nothing here is built yet; §5 prices what would be.

## 1. The question

Can a reader start from CSD's posits (an ontic sector `Σ = ℂℙⁿ × T²` with its Liouville measure and flow,
`specs/POSITS.md`) and, following only Lean theorems, arrive at the quantum-information results the corpus
proves — von Neumann entropy, trace distance and the data-processing inequality, subadditivity, strong
subadditivity, Holevo, Stinespring, the three-qubit code, the algorithms? Today: **no**, and the reason is
not that the bridge is missing. It is that the bridge exists as two theorems that are never composed, and
the QIT layer is stated on bare matrices that nothing CSD-side ever instantiates.

## 2. What the QIT layer is anchored on

Every module in `Mathlib/QuantumInfo/` is Category 1-Mathlib, imports nothing from `LF*`/`SigmaLayer`/
`RecordLayer`/`Empirical` (verified), and takes as input a bare `ρ : Matrix n n ℂ` with `PosSemidef` and
`trace = 1` hypotheses (or a bare `EuclideanSpace ℂ ι` vector, or a `Channel` as a Kraus family). That is
correct for a Mathlib-staging layer, and none of it should change. The question is what *feeds* it.

| What feeds it today | Where | Verdict |
|---|---|---|
| `LF6.decohereReduced ψ` — the partial trace of the LF5 von Neumann isometry applied to `ψ`, with each diagonal entry proved equal to an ontic typicality volume (`decoherence_diagonal_eq_pointer_volume`), fed to `vonNeumannEntropy_eq_zero_of_pure` (`decoherence_vonNeumann_irreversibility_capstone`, `LF6/Decoherence.lean:560`) | one theorem | **The one genuine CSD → QIT consequence in the corpus.** Its input is a Hilbert-space isometry, not a Σ-flow; its output entries are Σ-volumes. |
| `ledgerState` in `Empirical/CSD/QuantumChaos/EntropyLedger.lean` — `diag(1−e, e)` from a set's measure, `vonNeumannEntropy_ledgerState` | one theorem | A CSD-derived density matrix reaching a QIT theorem; special-purpose. |
| `CV/ChannelRG.lean` — consumes `channel_traceDist_le`, `traceDist_conj_sub_le` | on the CV field model's bare matrices | Not a Σ object. |
| Every other QIT theorem | — | **No CSD-side instantiation.** |

The `Empirical/CSD/` twins that touch QIT (`NoCloning`, `NoBroadcasting`, `NoCommunication`, `NoDeleting`,
`QEC/ThreeQubit`, `QECDecoherence`, `Resources/*`, `Crypto/QuantumMoney`, `Contextuality/KS18`,
`MerminPeres`) each take a `CSDBridge.Context D` bundle and prove the QM statement. In `QEC/ThreeQubit.lean:116`
and `QECDecoherence.lean:350` the bundle is bound as `_b` / `_bundle` — an **unused binder**. Their own
tags say TRANSPORT-ONLY and SCHEMA-MISMATCH; `EMPIRICAL.md` calls the bundle "the structural slot for the
ontic interpretation". A slot, not a derivation. `ChannelCapacity.lean` and `Einselection.lean` carry the
Category tag "6-Local" while every theorem type is a bare `Matrix (Fin N)` statement; their headers admit
it in prose, the tag overstates it.

The genuinely CSD-anchored empirical twins — the sequential-measurement crypto (`BB84Sequential`, `B92`,
`Wiesner`: calibrated-swap dynamics on Σ), the contextuality volumes (`KCBSVolume`, `KS18Volume`,
`MerminPeresVolume`: basin frequencies on `ℂℙᴹ × T²`), `Darwinism` (record strokes), and
`MixedStateBornVolume` — produce **no QIT object** (no density operator, channel, or entropy). They stop
at Born numbers.

## 3. The bridge as it exists

The chain `CSD posit → sector → preparation → density operator` is two proved theorems:

1. **Preparation → operational package.** `CSD.LF2.OperationalPackage.fromPreparation`
   (`LF2/Preparation.lean:155`): from `SectorData`, a `MeasureBridgeData`, a probability measure `μprep`
   on Σ and a representation `rep : P → ℂᴺ`, an `OperationalPackage N` whose effect probabilities are
   `∫ effectProjFn rep E ∂(π_* μprep)`.
2. **Operational package → density operator.** `CSD.LF2.OperationalPackage.effect_gleason_representation`
   (`LF2/EffectGleason.lean:1409`): `∃! ρ : DensityOperator N, ∀ E, OP.p E = traceForm ρ E`, witness
   `OP.qdensity`. Foundational triple, pinned.

**2 ∘ 1 is never stated as a theorem**, and `(fromPreparation …).qdensity` is consumed nowhere outside
`LF2/EffectGleason.lean` and `Headlines.lean`. The pure special case is composed (`born_rank_one`); the mixed
case is not. The region-preparation density `ρ_ep` (`SigmaLayer/PreparationDensity.lean`) is a function on
`ℂℙⁿ⁻¹`, and its identification with `qdensity` as a barycentre `∫ |ψ⟩⟨ψ| ρ_ep dμ_FS` is **absent** (no
declaration of that shape anywhere).

The next link, `density operator → channel`, has one witness: `LF6.decohereReduced`, whose Kraus form is the
partial trace of the vN isometry. The general-N version `decohereReducedN` is **posited**
(`Einselection.lean:414`, a `Matrix.diagonal` map). "A channel is the environment-marginal of a
measure-preserving flow on `Σ_sys × Σ_env`" (`Stinespring.lean` header, `channels-plan.md §3`) is prose: no
declaration takes a Σ-flow and returns a `QuantumInfo.Channel`. And the corpus carries **two parallel
Kraus types** — `CSD.LF2.QuantumChannel ι N M` and `QuantumInfo.Channel n m ι` — with no bridge lemma.

## 4. Link-by-link

| Link | Status |
|---|---|
| posit → sector | (iii) posited as structure fields; (ii) inhabited by a witness (`kMuL`, `fubiniStudyMeasure`); the sector's *geometry* proved by the G series (`generator-layer-scoping.md` §10) |
| sector → preparation | (i) proved for pure and region preparations; mixed preparations (ii) defined only from a given `ρ` (`mixedSwapPrep`) |
| preparation → density operator | (i) proved as two theorems, **never composed, never consumed by QIT**; barycentre identification (iv) absent |
| density operator → channel | (ii) one witness (`decohereReduced`); Σ-flow ⇒ `Channel` (iii) prose; `LF2.QuantumChannel` ↔ `QuantumInfo.Channel` bridge (iv) absent |
| channel → entropy, trace distance, DPI, subadditivity | (i) proved on bare matrices |
| strong subadditivity | (iii) conditional on an explicit `hDPI` hypothesis (`StrongSubadditivity.lean:374`); `lieb-dpi-scoping.md` recommends leaving it |
| Holevo / capacity | (iv) absent beyond one single-shot example; entropy concavity not in the corpus |
| QEC | (i) on `(Fin 2)³` matrices; CSD twins are transports with unused binders |
| algorithms | (i) on `QReg`; a CSD reading of circuits (iv) absent by design (`nqubit-register-plan.md §4`) |

## 5. What would be needed, priced

The programme, in order. Each row is a brick; the author decides. `P` is P(success); `V` is value for the
question in §1.

| # | Brick | Cx | P | V | What it lands |
|---|---|---|---|---|---|
| ~~**W2**~~ **DONE 2026-09-11** (10 pins, `LF2/PreparationQdensity.lean`; took S as priced; entropy of a preparation and DPI for two preparations are the first consumers) | **Compose the bridge.** `preparation_qdensity : ∀ (D bridge μprep rep …), ∃! ρ : DensityOperator N, ∀ E, (fromPreparation D bridge μprep rep).p E = traceForm ρ E` — literally `effect_gleason_representation` applied to `fromPreparation`, named and pinned, with `qdensity_fromPreparation` exposing the witness. Then the **instantiation lemmas**: for that `ρ`, `ρ.M.PosSemidef` and `ρ.M.trace = 1` in the exact form `Entropy.lean` / `Subadditivity.lean` / `TraceDistance.lean` take. | **S** | High | **High** — this is the missing spine; after it every K1/K3 theorem applies to a CSD preparation by one `exact` |
| ~~**W3**~~ **DONE 2026-09-11** (11 pins, `LF2/PreparationBarycenter.lean`; took M as priced; `preparationDensity_eq_barycenter`, entrywise `preparationDensity_apply`, the `ρ_ep` form `preparationDensity_apply_rnDeriv` under `π_* μprep ≪ μFS` — a hypothesis in the `LF2` interface, a theorem in the `SigmaLayer` one, the two interfaces not yet identified) | **The barycentre.** For a region preparation with projective law `μ_FS.withDensity ρ_ep`, `qdensity = ∫ |ψ⟩⟨ψ| ρ_ep(ψ) dμ_FS(ψ)` (a Bochner integral of rank-one projectors). This is what makes the density operator *the* ontic object rather than a Gleason witness. Needs integration of matrix-valued functions over `ℂℙⁿ` against `μ_FS` — `MeasureTheory.integral` on `Matrix` is present; the identification is `traceForm` linearity + `effectProjFn` = `Tr(|ψ⟩⟨ψ| E)`. | **M** | High | High |
| ~~**W4**~~ **DONE 2026-09-11** (coarse-graining half via W8: `preparationEntropy_mixture_ge`, `LF2/PreparationCoarseGraining.lean`; `= 0 ↔ pure` half: `LF2/PreparationPurity.lean` ★★ `preparationEntropy_eq_zero_iff` — a preparation has zero entropy iff its projective law is a Dirac mass at one ray, with `Projectivization.unitSection` as representative; matrix level `vonNeumannEntropy_eq_zero_iff` in Cat-1 `Mathlib/QuantumInfo/PureState.lean`; 9 pins, took S. **Remaining: monotonicity under coarse-graining of regions, needs W8**) | **Entropy of a preparation.** `vonNeumannEntropy_fromPreparation`, `= 0 ↔ pure` (`SigmaLayer/PreparationDensity` has purity), monotone under coarse-graining of regions (needs W3 + concavity, see W8). | **S–M** after W2 | High | Medium — the first QIT quantity *of a Σ-region* |
| ~~**W5**~~ **DONE 2026-09-11** (witness half: `LF6/DecoherenceChannel.lean`, `deisolationChannel_apply_outerProduct : (deisolationChannel N).apply ∣ψ⟩⟨ψ∣ = decohereReduced ψ`, 4 pins; bridge half: `LF2/ChannelBridge.lean`, `channelEquiv : QuantumChannel ι N M ≃ Channel (Fin N) (Fin M) ι` with actions / dilations / unitary channels / compositions agreeing (`Channel.comp` added to `Mathlib/QuantumInfo/ChannelComp.lean`) and `traceDist_channelApply_le`, DPI for LF2 channels; `QuantumChannel` marked an **interface** kept for its Choi layer, 11 pins; took S) | **Channels from flows, the witness first.** State `LF6.decohereReduced` as a `QuantumInfo.Channel` (Kraus = partial-trace-of-isometry, `Stinespring.ofIsometry` is present) and prove `Channel.apply = decohereReduced`; then the bridge `LF2.QuantumChannel ↔ QuantumInfo.Channel` (both are Kraus families; a `toChannel` + `apply_eq`). Retire the parallel type or mark it an interface. | **S–M** | High | Medium |
| ~~**W6**~~ **DONE 2026-09-11** (22 pins, `LF2/FlowChannel.lean`; took L as priced. ⚠️ *This row's gloss of the corpus was wrong and is corrected here:* `RecordLayer.IsJointLift` is the pointer-arena stroke predicate — pointer agreement plus conserved rates and register — **not** "the lift of a unitary on `ℂᴺ ⊗ ℂᴱ`"; the corpus's flows lifting unitaries are the projective actions `π (Φ x) = U • π x` of `KahlerOnticSetup.projectable` / LF5's `measurementFlow`. Built on those and on the abstract `SectorData` interface: `IsUnitaryLift` (projector level, phase-free; a theorem for the projective action with any unit section, `isUnitaryLift_of_smul`), ★★ `barycenter_flow` (closed system, `U ρ Uᴴ`), ★★ `traceRight_barycenter_flow` (open system, ready environment `e₀`: the reduced flowed state is `stinespringChannel U e₀` applied to the system's density operator), ★★ `traceRight_barycenter_flow_prod` (product preparation on a product sector: the mixed-environment channel `stinespringChannelMixed`, environment state = the barycentre of the environment preparation, spectral Kraus family). Residue **W6′** below.) | **Channels from flows, general.** For a measure-preserving flow `Φ_t` on `Σ_sys × Σ_env` that is the lift of a unitary `U_t` on `ℂᴺ ⊗ ℂᴱ` (~~the corpus's `IsJointLift`~~ — see the correction), the map `ρ ↦ Tr_env (U_t (ρ ⊗ σ_env) U_tᴴ)` is a `QuantumInfo.Channel` whose action on `qdensity` of a preparation is `qdensity` of the *flowed* preparation. This is the theorem the `Stinespring.lean` header calls the "CSD reading"; it needs W2, W5, and the joint-lift API. | **L** | Medium | **High** — the CSD origin of every channel the QIT layer then reasons about |
| ~~**W6′**~~ **DONE 2026-09-11** (6 pins, `LF6/MeasurementFlowChannel.lean` + `isUnitaryLift_of_reindex` in `LF2/FlowChannel.lean`; took S. ★★ `measurementFlow_traceRight_barycenter`: the de-isolation channel IS the environment marginal of LF5's `measurementFlow`; `measurementFlow_vonNeumannEntropy_le`. Unit section of the ray map and product form are hypotheses.) | **The joint-index instance.** `isUnitaryLift_of_smul` is at `Fin N` because the projective unitary action (`Projectivization/Unitary.lean`) is `Fin N`-indexed; feeding a joint `Fin N × Fin E` sector through it needs the reindexing `Fin N × Fin E ≃ Fin m` LF5 already uses (`vnUnitaryReindexed`, `measurementFlow`), i.e. `IsUnitaryLift` for `measurementFlow N e` with `rep` transported along `piLpCongrLeft`. Then LF5's flow on the dilated sector is literally an instance of `traceRight_barycenter_flow` with `U = vnUnitary N`, `e₀ = a₀`. | **S–M** | High | Medium — closes the loop from LF5's ontic flow to `deisolationChannel` |
| ~~**W7**~~ **DONE 2026-09-11** (9 pins, `Thermo/SigmaSecondLaw.lean`; took S as priced. `deisolationChannel_apply_eq_pinch`: TH2's `pinch` IS the de-isolation channel's action, so the second law's coarse-graining is the environment marginal of the de-isolation flow, not a separate postulate; ★★ `vonNeumannEntropy_le_pinching_flow` (the second law on Σ: entropy conserved along the flow, produced by pinching), ★★ `vonNeumannEntropy_le_deisolation` (entropy after de-isolation ≥ before), ★★ `traceDist_traceRight_flow_le` (DPI on Σ), ★★ `landauer_flow` (Landauer for a product preparation whose bath preparation has the Gibbs barycentre). Hypotheses inherited from TH2/TH4: full support / full rank.) | **DPI and the second law on Σ.** With W6: `channel_traceDist_le` and `vonNeumannEntropy_le_pinching` instantiated on flowed preparations — the corpus's `Thermo/SecondLaw.lean` and `Landauer.lean` become statements about Σ-regions under de-isolation. | **S** after W6 | High | High |
| ~~**W6″**~~ **DONE 2026-09-11** (12 pins; `Mathlib/LinearAlgebra/Projectivization/UnitSection.lean`, Cat-1: `Projectivization.unitSection`, unit-norm with first non-zero coordinate real and positive, `mk_unitSection`, ★ `measurable_unitSection` via `lift_measurable`; consumers `isUnitaryLift_unitSection` and `measurementFlow_traceRight_barycenter_unitSection` — no section hypothesis left between LF5's flow and the de-isolation channel. Took M.) | **A measurable unit section of the ray map.** `isUnitaryLift_of_smul` and W6′ take a unit-norm measurable `rep'` with `mk (rep' p) = p` as a hypothesis; the corpus's concrete consumers use constant representatives (Dirac preparations). Construct one: normalise the first non-zero coordinate to be real and positive (a Borel selection on `ℙ ℂ (ℂᵐ)`); measurability needs the quotient Borel structure of `ℙ` against the sphere, cf. Q26's `StandardBorelSpace` probe. Then every projective-action lift is unconditional. | **M** | Medium | Medium — removes the last hypothesis between LF5's flow and the channel |
| ~~**W8**~~ **DONE 2026-09-11** (Cat-1 `Mathlib/QuantumInfo/Concavity.lean`: ★ `vonNeumannEntropy_mixture_ge` via `S(σ) − ∑ pᵢ S(ρᵢ) = ∑ pᵢ D(ρᵢ‖σ) ≥ 0` (Klein), `holevoChi` + ★ `holevoChi_nonneg`; applied in `LF2/PreparationCoarseGraining.lean`: ★★ `preparationEntropy_mixture_ge`, W4's coarse-graining half — 11 pins, took S. Klein's full-support condition on the mixture is inherited; removing it is a separate step) | **Concavity of von Neumann entropy** (`S(∑ pᵢ ρᵢ) ≥ ∑ pᵢ S(ρᵢ)`): needed for Holevo ≥ 0, for W4's coarse-graining, and for any capacity statement. The corpus has `matrix_log_concave`/`matrix_rpow_concave` (`OperatorConvexBridge.lean`) but not `S`; Mathlib has `CFC.concaveOn_log` since 2026-08-30. Route: `S(ρ) = −Tr(ρ log ρ)` and operator concavity of `x log x`'s negative via the CFC. | **M** | Medium–high | Medium |
| **W9** | **SSA unconditional** — the `hDPI` hypothesis of `strong_subadditivity_of_relEntropy_monotone`. `lieb-dpi-scoping.md` (2026-09-01) found physlib's `Sᵥₙ_strong_subadditivity` sorry-free on identical pins and recommends *leave `hDPI` honest, or bridge*; its Gate 0 (`#print axioms`) is unrun. Do that gate before pricing further. | **L–XL** (build) / **S** (bridge if Gate 0 passes) | Low / High | Medium |
| **W10** | **Holevo χ and one capacity.** With W8: `holevo_nonneg`, `holevo_le_log_dim`, and the single-letter classical capacity of the dephasing witness as a *theorem* rather than an example (`ChannelCapacity.lean` has the arithmetic). Regularised capacity not in scope. | **M** after W8 | Medium | Low–medium |
| **W11** | **QEC on Σ.** `three_qubit_corrects_single_bitflip` with the bit-flip channel produced by W6 from a Σ-flow, and the code space read as a Σ-region (`RecordLayer` basins). Removes the unused `_bundle` binders honestly. | **M** after W6 | Medium | Medium |
| ~~**W12**~~ **DONE 2026-09-11** (both mis-tags re-tagged 3-Local — "6-Local" is not a CONVENTIONS §1 category; the three stale notes corrected; `EMPIRICAL.md`'s QEC row now says its bundle is unused) | **Ledger fixes now, no Lean:** re-tag `ChannelCapacity.lean` and `Einselection.lean` from "6-Local" to what they are; mark the unused-binder twins as such in `EMPIRICAL.md`; the three stale notes the survey found (`StrongSubadditivity.lean:80` — the fork is no longer build-vs-axiom; `Pauli.lean:28` and `Clifford.lean:37` say stabiliser measurement is "not attempted" while `Stabilizer.lean` proves it; `channels-plan.md:104` lists DPI as deferred, it landed 2026-06-09). | **S** | High | Site accuracy |

**The critical path is W2 → W3 → W6 → W7; all four built 2026-09-11.** From CSD's posited sector and a flow lifting a unitary, the density operator of a preparation, its evolution, the channels it passes through, and the second law, data processing and Landauer bounds on it are now one chain of theorems. After W2 (an afternoon) every entropy, distance, and DPI theorem
in the corpus is *available* to a CSD preparation; after W6 (L) the channels those theorems talk about
*come from* Σ-flows. That is the point at which "from the base posit to the end of the QIT" is a chain of
theorems rather than a chain of headers. W8–W11 extend the reach; W9 is a Mathlib-depth fork the author
has already been asked to rule on.

**What this does not change.** The posits stay posits (`POSITS.md`): the sector is selected, not derived,
and the flow's Liouville property for the constraint dynamics is Posit 3. Every QIT statement reached by
this programme is of the form "given CSD's posited sector and flow, the following quantum-information
quantities of its preparations obey these theorems". That is a consequence of the posits, which is what §1
asks; it is not a derivation of the posits, which the CHARTER says is a non-question.

## References

`EMPIRICAL.md` (the two layers; "structural slot"); `specs/channels-plan.md`, `specs/lieb-dpi-scoping.md`,
`specs/nqubit-register-plan.md`; `LF2/Preparation.lean`, `LF2/EffectGleason.lean`, `LF6/Decoherence.lean`,
`SigmaLayer/PreparationDensity.lean`, `RecordLayer/JointFlowTransfer.lean`, `RecordLayer/JointLift.lean`, `Empirical/CSD/Framework.lean`;
`Mathlib/QuantumInfo/*`; `specs/generator-layer-scoping.md` §10 (the geometry side of the same question).
