> ⚠️ HISTORICAL — layer complete; frozen execution log. Open items live in [BACKLOG.md](BACKLOG.md).
# TN4 — the measurement-theory architecture

**Orientation map for the measurement stack.** This document is the single
architectural view of how the corpus's measurement machinery fits together,
before diving into the per-layer code. It is descriptive, not a plan: every
object named here already exists and is machine-verified. For the working
guide see [`CLAUDE.md`](../CLAUDE.md); for the axiom posture see
[`AXIOMS.md`](../AXIOMS.md); for the per-test index see
[`EMPIRICAL.md`](../EMPIRICAL.md).

## The one question

TN4 answers: **how does a general measurement arise in CSD?** Everything below
is support for that single question. The CSD answer, in one line: a general
(POVM) measurement is a deterministic, measure-preserving de-isolation flow that
realises a Naimark dilation, and its pointer-block typicality volumes are the
Born weights. The single-system projective tier of that answer is closed (LF5);
the entangled tier is the open frontier (D1, below).

## The stack

```
            QM layer (inner-product geometry)        CSD-ontic layer (typicality volume on Σ)
            ----------------------------------        ----------------------------------------
  pure states                ψ : QReg / EuclideanSpace ℂ ι           microstate σ ∈ Σ,  μ_L
        │                    Register.lean, prob = ‖·‖²              LF1/Setup.lean (OnticSetup)
        ▼
  density operators          DensityOperator, rankOneDensity         conditional law μ_prep on Ω₀
        │                    LF2/BornWrapper, LF2/ReducedDensity      LF1/Preparation.lean
        ▼
  channels / dilation        Channel (Kraus/Stinespring/canonical)   measure-preserving flow Φ
        │                    Mathlib/QuantumInfo/{Channel,            LF1 OnticSetup.Φ
        │                    Stinespring,CanonicalChannels,PartialTrace}
        ▼
  measurements        ┌───────────────────────┬───────────────────────┐
                      │  projective (context) │   POVM (general)       │
                      │  MeasurementContext    │   POVM, Effect         │
                      │  LF3/ContextMap        │   LF2/{POVM,BornWrapper}│
                      └───────────┬───────────┴───────────┬───────────┘
                                  │                       │
                                  ▼      Naimark dilation ▼
                            canonicalNaimark : NaimarkDilation P     (from CFC √Eᵢ)
                            LF4/{POVMNaimark,POVMDilation}  —  born_transfer
                                  │
                                  ▼
  Born rule           ‖⟨eᵢ,ψ⟩‖²  /  ⟨ψ,Eᵢψ⟩                 = a Fubini–Study volume ratio on Σ
                      (taken as inner product)               momentMap_mk_eq_inner_sq,
                                  │                          fs_born_volume_ratio_N,
                                  ▼                          born_frequency_convergence_N (DH cluster)
  CSD volume          LF1 typicality: a.s. frequencies → ontic volume weights
                      LF1_main_theorem_ae  →  LF1_main_theorem_projective
                                  │
                                  ▼
  measurement         a deterministic FS-measure-preserving flow Φ_vN ≠ id realises the
  dynamics (LF5)      Naimark dilation; pointer-block volumes / a.s. frequencies = Born
                      measurement_flow_born_frequency  (LF5/Capstone)
```

## Per-layer reference

| Layer | What it is | Key Lean objects | File(s) |
|---|---|---|---|
| Pure states | finite-dim state vectors; `prob = ‖·‖²` | `QReg`, `basisState`, `prob` | `Mathlib/QuantumInfo/Register.lean` |
| Ontic substrate | the deterministic measure space `(Σ, μ_L, Φ, Ω₀)` | `OnticSetup` | `LF1/Setup.lean` |
| Density operators | concrete `N×N` density / reduced states | `DensityOperator`, `rankOneDensity`, reduced density | `LF2/BornWrapper.lean`, `LF2/ReducedDensity.lean` |
| Effects / POVM | finite-dim effect algebra; the POVM type + completeness | `Effect`, `POVM` | `LF2/BornWrapper.lean`, `LF2/POVM.lean` |
| Channels | CPTP maps: Kraus / Stinespring / canonical; partial trace | `Channel`, `PartialTrace` | `Mathlib/QuantumInfo/{Channel,Stinespring,CanonicalChannels,PartialTrace}.lean` |
| Projective measurement | an orthonormal measurement context; rank-1 and degenerate | `MeasurementContext`, `context_born_frequency_volume`, `block_born_frequency_volume` | `LF3/ContextMap.lean`, `Empirical/CSD/ContextVolume.lean` |
| Naimark dilation | the canonical isometry `V` with `Vᴴ Πᵢ V = Eᵢ`, from CFC `√Eᵢ` | `NaimarkDilation`, `canonicalNaimark`, `born_transfer` | `LF4/POVMNaimark.lean`, `LF4/POVMDilation.lean` |
| Born = FS volume | the Born weight as a Fubini–Study typicality volume ratio, general `N`, unconditional | `momentMap_mk_eq_inner_sq`, `fs_born_volume_ratio_N`, `born_frequency_convergence_N`, `povm_born_frequency_volume(_uncond)` | `LF4/{MomentMap,MomentBornN,BornFrequencyN,POVMVolume,BornRegionUncond}.lean` |
| CSD typicality | a.s. empirical frequencies converge to ontic volume weights | `LF1_main_theorem_ae`, `LF1_main_theorem_projective` | `LF1/MainTheorem.lean`, `LF2/Interface.lean` |
| Measurement dynamics | the von Neumann de-isolation flow `Φ_vN ≠ id` realising the dilation dynamically | `measurement_flow_born_frequency`, `measurement_flow_outcome_frequency` | `LF5/Capstone.lean`, `LF5/{MeasurementFlow,DilationFromFlow,PointerOutcome}.lean` |

## The two readings (horizontal axes)

Every row of the stack is read two ways, and separately sits in one of two
axiom strata. Keeping these straight is the whole point of the architecture.

**Axis 1 — QM-validity vs CSD-ontic.** The left column (`Empirical/QM/`) is pure
inner-product geometry: Born numbers are taken as `‖⟨·,·⟩‖²`. The right column
(`Empirical/CSD/`, LF1–LF5) reads the same numbers as Fubini–Study typicality
volumes on the ontic `Σ`. The two meet at the Born value: the QM side asserts it,
the CSD side **derives** it from the Kähler volume (the Duistermaat–Heckman
cluster, `fs_born_volume_ratio_N` / `born_frequency_convergence_N`).

**Axis 2 — operational stratum vs ontic stratum.** The *operational* reading of
the Born rule (effect-additive probability ⟹ trace-form density) uses the one
imported library axiom `busch_effect_gleason`. The *ontic* reading (Born = FS
volume) is **Gleason-free**: it never touches `busch_effect_gleason`, for
projective *and* POVM measurements. The corpus deliberately keeps both; the
ontic stratum is the one that carries CSD's claim. See `AXIOMS.md §2`.

## Where Born comes from (not postulated)

The Born weight is not an input to the CSD layer. It is derived one level down,
in the moment-map / Duistermaat–Heckman cluster, as a Fubini–Study volume ratio:
`momentMap_mk_eq_inner_sq` (Born = torus moment coordinate), `fs_born_volume_ratio_N`
(Born = barycentric FS-volume ratio, all `N`, unconditional), and
`born_frequency_convergence_N` (i.i.d. FS trials ⟹ frequencies → the full Born
vector a.s.). The POVM case is reduced to this via `canonicalNaimark` +
`born_transfer` + `povm_born_frequency_volume`. LF5 *imports* this; it does not
re-derive it. This is a relocation of the primitive, not its elimination: Born
becomes a theorem of the posited sector geometry on `Σ` (the **A5** datum), which
in turn rests on the deterministic dynamics (**D1**).

## The dynamical realisation (LF5) — the answer to the one question

The review's desired narrative

```
projective measurement → ancilla → unitary interaction → projective measurement → POVM → Born volume
```

is realised, dynamically, as LF5. A deterministic, FS-measure-preserving von
Neumann de-isolation flow `Φ_vN ≠ id` on the dilated projective ontic space
carries `[ψ ⊗ a₀] ↦ [Vψ]` (the Naimark isometry applied), and its context-fixed
pointer-block volumes and a.s. empirical frequencies are the Born weights, for
every unit preparation (`measurement_flow_born_frequency`). The per-microstate
outcome map is `vnPointerOutcome` (`measurement_flow_outcome_frequency`). So a
general measurement is not an extra postulate on top of unitary dynamics; it is
unitary de-isolation of an ancilla followed by typicality, read on `Σ`.

## Honest residue (what is NOT yet done)

The architecture is complete for the **single-system projective** tier. Marked
honestly, the open parts are mathematics, not integration:

- **D1 — entangled / non-local de-isolation.** Bell forces a *non-local*
  de-isolation map given the corpus CHSH `= 2√2`. LF5's flow is single-system;
  the entangled tier is unbuilt. This is the deepest open debt.
- **A5 — the sector origin.** The projection-and-symmetry data `(π, G)` is
  *posited* (a `SectorData` field), not derived. A5 reduces to D1.
- **Φ = id in the concrete instances.** `cpSectorData` / `kSectorData` carry
  `Φ = id`; LF5's `Φ_vN ≠ id` lives only on the dilated `Σ'`, not threaded into
  the concrete `SectorData`. So the volume readings are faithful *realisations*,
  not *derivations from dynamics*.
- **Operational-stratum library debt.** `busch_effect_gleason` (the Busch
  effect-Gleason theorem, not yet in Mathlib) survives on the operational route
  only; it is off the ontic Born path.

## Reading order

1. This file (the map).
2. [`AXIOMS.md`](../AXIOMS.md) §2 — the two strata, the one imported axiom.
3. [`specs/lf5-plan.md`](lf5-plan.md) — the measurement-dynamics tier and its honesty ledger.
4. [`specs/povm-plan.md`](povm-plan.md) — the general-measurement (Naimark) tranche.
5. [`specs/carve-out-plan.md`](carve-out-plan.md) §6 — the D1 de-isolation reading and the open frontier.
