# POVM tranche plan — extend the ontic Born derivation to general POVMs

Status: planning doc, opened 2026-06-02. This is the **starting point for the next
session**. Read `specs/INDEX.md` first for orientation; read this for the tranche.

## Goal and why it matters

The ontic Born derivation (Born = Fubini–Study typicality volume on `Σ = ℂℙ^{N-1}`)
is, as of 2026-06-02, complete for **rank-1 projective (von Neumann) measurements** at
general `N`, Gleason-free (`fs_born_volume_ratio_N` / `_apex`,
`born_frequency_convergence_N`; see `general-n-dh-plan.md`). The LF3 empirical chain was
re-routed onto it (`weight_eq_P_st` → `OP_p_at_jointEig_eq_P_st_direct`).

`busch_effect_gleason` now survives **only** as the operational-stratum statement, cited
by `pure_state_born_weights_of_certainty`, `born_rank_one`, `OP_p_at_jointEig_eq_P_st`,
`ontic_born_frequency`. The **one thing keeping it genuinely load-bearing** is that the
volume route covers projective measurements only; Busch's representation theorem covers
**arbitrary effects / POVMs**. Closing that is this tranche: make the ontic stratum cover
general POVMs, so the Gleason import becomes dispensable for the ontic reading even for
non-projective effects.

This is **consolidation of the achieved result**, not a new frontier (the frontier is D1,
the physical-faithfulness question of exercising real measurement dynamics on `Σ`; see
`carve-out-plan.md`). It completes the ontic stratum; it does not, by itself, derive
anything new about nature.

## The approach: Naimark dilation + partial trace

A POVM `{Eᵢ}` on `ℂ^N` (effects `0 ≤ Eᵢ`, `∑ Eᵢ = I`) is the compression of a
**projective** measurement `{Πᵢ}` on a dilated space `ℂ^N ⊗ ℂ^K` (Naimark):
there is an isometry `V : ℂ^N → ℂ^N ⊗ ℂ^K` with `Eᵢ = V† Πᵢ V`. Then the Born weight

```
⟨ψ, Eᵢ ψ⟩ = ⟨V ψ, Πᵢ (V ψ)⟩
```

is the **projective** Born weight of the dilated state `V ψ` against the projector `Πᵢ`,
which the achieved result (`fs_born_volume_ratio_N` on `ℂℙ^{NK-1}`) gives as a
**Fubini–Study volume ratio** on the dilated `Σ' = ℂℙ^{NK-1}`. Reducing back (partial
trace) gives the POVM Born weight as an ontic volume on the dilated configuration space.

So the POVM Born value is: *project the preparation into a larger ontic configuration
space (system + ancilla), read the projective volume there.* The honest reading is that
the ontic stratum handles POVMs by **dilation onto a larger constraint surface** — which
is physically natural (the ancilla is the measurement apparatus / environment), exactly
the CSD picture.

## Tooling already in place

- `CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` — `traceRight`/`traceLeft`,
  `traceRight_kronecker` (`Tr_n(A⊗B)=Tr(B)·A`), `PosSemidef.traceRight`, the bimodule
  laws, `trace_traceRight`. The reduction tool.
- `CsdLean4/LF2/ReducedDensity.lean` — `DensityOperatorIx ι`, `.reduced`/`.reducedLeft`.
- `CsdLean4/LF4/MomentBornN.lean`, `BornFrequencyN.lean` — the projective Born = FS-volume
  result on `ℂℙ^{N-1}` (apply on the dilated space).
- `CsdLean4/LF2/BornWrapper.lean` — the `Effect` type (PSD matrix `≤ 1`), `Effect.add`,
  `rankOneEffect`; the starting point for a POVM type.

## Mathlib-gap recon needed first (the session's first action)

The main unknown is how much dilation infrastructure Mathlib has. Likely thin. Probe:

- Naimark / Stinespring dilation: search Mathlib for `Naimark`, `Stinespring`,
  `isometry` + `POVM`, `CPMap`, completely-positive maps. **Expect this to be absent** —
  if so, the dilation isometry must be constructed by hand (the standard block
  construction: `V` built from the `√Eᵢ` so that `Πᵢ = |i⟩⟨i| ⊗ I` pulls back to `Eᵢ`).
- The matrix square root `√E` for a PSD effect (needed for the canonical Naimark
  isometry `Vψ = ∑ᵢ √Eᵢ ψ ⊗ |i⟩`): Mathlib has `Matrix.PosSemidef.sqrt` —
  confirm and use.
- Whether to dilate via tensor with `ℂ^K` (`Fin N × Fin K` indexing, matches
  `traceRight`) or a direct sum. Tensor matches the partial-trace tooling.

## Proposed DAG (revise after recon)

- **P.0 — recon** Mathlib for dilation / CP-map / sqrt infrastructure; decide hand-built
  vs library. Output: a concrete construction choice.
- **P.1 — POVM type.** A finite family `E : ι → Effect N` with `∑ᵢ (E i).M = 1`
  (a `POVM N ι` structure). Cat-3 or Cat-2.
- **P.2 — Naimark isometry.** `naimarkIsometry : ℂ^N → ℂ^N ⊗ ℂ^ι`,
  `Vψ = ∑ᵢ (√Eᵢ ψ) ⊗ |i⟩`; prove it is an isometry (`V† V = I`, uses `∑ Eᵢ = I`), and
  the pullback identity `V† (|i⟩⟨i| ⊗ I) V = Eᵢ` (the defining Naimark property).
- **P.3 — Born transfer.** `⟨ψ, Eᵢ ψ⟩ = ‖((mk (Vψ)) projected onto the i-th block)‖²`
  = projective Born weight on `ℂℙ^{Nι-1}`; compose with `fs_born_volume_ratio_N` to read
  it as an FS-volume ratio on the dilated `Σ'`.
- **P.4 — (optional) empirical capstone.** A POVM analogue of
  `born_frequency_convergence_N`: i.i.d. trials, frequencies → `⟨ψ, Eᵢ ψ⟩` via the
  dilated volume. May reuse `born_frequency_convergence_partition` with the dilated
  regions.

## Honest scope to preserve

- The Naimark dilation isometry `V` is a **choice** (dilations are non-unique). The result
  will be "given a Naimark dilation, the POVM Born weight is the dilated projective
  volume." Whether a canonical/forced dilation exists is a separate question — flag it,
  do not claim the dilation is forced.
- This relocates POVM Born onto a **larger** posited configuration space (`Σ'`), so the A5
  ontology now includes the ancilla. Honest: the apparatus/environment is part of the
  ontic story (CSD-consistent), but it is an enlargement of the posited structure.
- `busch_effect_gleason` stays in the corpus as the operational stratum regardless; this
  tranche makes it dispensable for the *ontic* POVM reading, not removable.

## Entry points (files to open first)

`CsdLean4/LF2/BornWrapper.lean` (Effect type), `PartialTrace.lean` (reduction),
`CsdLean4/LF4/MomentBornN.lean` (`fs_born_volume_ratio_N`), and probe Mathlib for
`PosSemidef.sqrt` / dilation. AxiomAudit-pin every new export to the foundational triple.
