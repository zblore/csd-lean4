# POVM tranche plan — extend the ontic Born derivation to general POVMs

Status: **CLOSED 2026-06-03.** P.1–P.5 done (POVM type, Naimark dilation + Born transfer,
volume reading, frequency capstone, canonical-dilation existence), P.6 (docs) done — all
foundational-triple-only, Gleason-free. The ontic Born = Kähler-volume derivation now
covers general (non-projective) measurements. See the Progress section below. The open
frontier is now **D1's deeper strata** (`specs/carve-out-plan.md`): the single-system
projective tier was exercised by LF5 (`Φ_vN ≠ id`, complete 2026-06-15), but the concrete
`SectorData` instances still carry `Φ = id`, and entanglement / the A5 sector origin remain.

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

## Recon findings (DONE 2026-06-03)

Read-only sweep of the pinned Mathlib (`Analysis/Matrix/*`, `LinearAlgebra/Matrix/*`,
`Analysis/CStarAlgebra/*`). Verdicts:

- **PSD square root: OBTAINABLE via CFC (not absent).** There is no
  `Matrix.PosSemidef.sqrt`, but `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`
  provides `Matrix.IsHermitian.cfc : (ℝ → ℝ) → Matrix n n 𝕜` (a real continuous functional
  calculus for Hermitian matrices; **not** deprecated), built on `IsHermitian.spectral_theorem`.
  So `√E := hE.isHermitian.cfc Real.sqrt`. Fallback if its API is thin: the general
  `cfc`/`CFC.sqrt` on `Matrix n n ℂ` as a C⋆-algebra, or a hand build from
  `IsHermitian.eigenvalues` + `eigenvectorBasis` (`Analysis/Matrix/Spectrum.lean`).
- **PSD preservation under conjugation: PRESENT.**
  `Matrix.PosSemidef.conjTranspose_mul_mul_same` (`Bᴴ A B`) and `mul_mul_conjTranspose_same`
  (`B A Bᴴ`) — already used in `LF2/BornWrapper.lean` `Effect.conjugateBy`. Gives `Eᵢ = Vᴴ Πᵢ V`
  PSD for free.
- **Matrix↔operator bridge: PRESENT.** `Matrix.toEuclideanLin` +
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` (the adjoint bridge) +
  `LinearMap.isometryOfInner` / the `Vᴴ V = 1` characterisation — the isometry idiom is
  exactly the one `Bell.lean`'s Tsirelson construction already uses.
- **Kronecker + reindex: PRESENT.** `mul_kronecker_mul`, `one_kronecker_one`,
  `trace_kronecker`, `kronecker_assoc'`; `finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)` and
  `OrthonormalBasis.reindex` for transporting the dilated space to `Fin (N·K)`.
- **Naimark / Stinespring / POVM / CPTP / quantum channel: ABSENT.** Confirmed zero hits.
  `CompletelyPositiveMap` + GNS exist but are infinite-dim / `CStarMatrix`-level, **not**
  usable for our finite `Matrix (Fin N) ℂ`. **Everything POVM-specific is hand-built.**

**Net effect on the plan.** The dilation must be hand-built (as expected), but the sqrt is a
CFC wrapper rather than a from-scratch spectral build, so the *existence* half (P.5) is
moderate, not heavy. The recon also confirms the clean decomposition below: a **conditional
core** (P.1–P.4, sqrt-free, ships first) and an **existence half** (P.5, the CFC sqrt +
canonical isometry) that makes the core unconditional.

## Progress (2026-06-03)

**Phase 1 P.1–P.3 DONE** (commits `fc2e7af`, `a58e41e`, + P.3b), all foundational
triple only, AxiomAudit-pinned:
- P.1 `LF2/POVM.lean` — `POVM` type, `weight`, `weights_sum_eq_normSq/_one`.
- P.2 `LF4/POVMDilation.lean` — `blockProj`, `NaimarkDilation`, `born_transfer`.
- P.3a `LF4/POVMVolume.lean` — `blockProj_mulVec`, `blockProj_born_eq_block_sum`,
  `povm_born_eq_block_sum` (POVM Born = ∑ dilated rank-1 cells).
- P.3b `LF4/POVMVolume.lean` — `povm_born_eq_dilated_volume`: `pᵢ(ψ) = ∑ₙ μ_FS(bornRegion ψ' (e(n,i)))`,
  the POVM Born weight as a sum of genuine FS volumes on `Σ' = ℂℙ^{N·|ι|−1}`, via the
  `piLpCongrLeft` reindex isometry + `bornRegion_fs_measure`. Carving-free, Gleason-free.
  Takes the reindex `e : Fin N × ι ≃ Fin(M+1)`, unit `ψ'`, and genericity (`hpos`) as
  supplied (honest scope: dilation supplied, ancilla enlarges `Σ`).

**Phase 1 COMPLETE — P.4 DONE** (`LF4/POVMVolume.lean` `povm_born_frequency_volume`):
i.i.d. Fubini–Study trials on the dilated `Σ'` ⟹ the `i`-th POVM outcome's empirical
frequency (the block sum of dilated cell frequencies) converges a.s. to `pᵢ(ψ)`. The
empirical → Born chain for a general (non-projective) POVM, carving-free and
Gleason-free. Composes `born_frequency_convergence_N` (joint per-cell a.s.) with the
P.3a block sum via `tendsto_finset_sum`. The block frequency is taken as the sum of the
cells' frequencies (Option A — no disjointness lemma needed; the cells are disjoint so
this is the honest block count). Foundational triple only; AxiomAudit-pinned.

**Phase 2 COMPLETE — P.5 DONE** (`LF4/POVMNaimark.lean`): the canonical Naimark
dilation `canonicalNaimark P : NaimarkDilation P` exists for **every** POVM, built from
`√Eᵢ = cfc Real.sqrt Eᵢ` (the unital Hermitian CFC on `Matrix n n ℂ` — P.5a is a library
call: `√Eᵢ √Eᵢ = Eᵢ` via `cfc_mul` + `√x·√x = x` on the nonneg spectrum
(`spectrum_nonneg_of_nonneg`) + `cfc_id`; no hand-built spectral construction). The
isometry `naimarkV_isom` (`Vᴴ V = ∑Eᵢ = I`) and pullback `naimarkV_pullback`
(`Vᴴ Πᵢ V = Eᵢ`) both reduce to `∑ₙ conj(√Eᵢ)_{n,m}(√Eᵢ)_{n,m'} = (Eᵢ)_{m,m'}`. This makes
the Phase-1 ontic POVM Born = Kähler-volume results **unconditional** — every POVM has a
dilation. Foundational triple only; AxiomAudit-pinned.

Note (impl): the non-unital `CFC.sqrt` is NOT wired for `Matrix` (no registered
`CStarAlgebra` instance), so the unital `cfc Real.sqrt` is used instead — same result,
slightly more plumbing (`spectrum ℝ`-nonneg via `spectrum_nonneg_of_nonneg`).

**Phase 3 — P.6 DONE** (docs): README headline + machine-verified table + theorem
inventory updated to sell the POVM achievement; `INDEX.md`, `CLAUDE.md` (where-to-start +
LF2/LF4 module chains), `AXIOMS.md` §2.4 (the open-POVM-step note rewritten — POVMs now
covered, Busch off the ontic path) all refreshed. **Tranche complete.** The
conditional-dilation caveat is discharged; what remains posited is the enlarged sector
structure on `Σ'` (A5 on the ancilla) and the dynamics (D1, the open frontier).

## Detailed DAG (recon-grounded 2026-06-03)

Two phases. **Phase 1 (P.1–P.4)** is a complete, shippable, foundational-triple-only result
that is *conditional on a supplied Naimark dilation* — matching the honest-scope note
(dilations are non-unique / supplied, not forced). **Phase 2 (P.5)** discharges existence,
making Phase 1 hold for every POVM. **Phase 3 (P.6)** is audit + docs. Pure-state `ψ`
throughout (matches `born_frequency_convergence_N`); mixed `ρ` is a later extension.

### Phase 1 — conditional core (sqrt-free, foundational triple)

- **P.1 — POVM type.** New `CsdLean4/LF2/POVM.lean` (sits on `BornWrapper.lean`). Cat-3.
  `structure POVM (N : ℕ) (ι : Type*) [Fintype ι]` = `E : ι → Effect N` with
  `complete : ∑ i, (E i).M = 1`. Define `povmWeight (ψ) (i) := re ⟨ψ, (E i).M *ᵥ ψ⟩`
  (or via `traceForm` of the pure density), and `povmWeights_sum_eq_one`
  (`∑ i, povmWeight ψ i = ‖ψ‖²`, from `complete`). Small.

- **P.2 — abstract Naimark data + Born transfer.** New `CsdLean4/LF4/POVMDilation.lean`.
  `structure NaimarkDilation (P : POVM N ι)` carrying ancilla dim (use `ι` as the ancilla
  index, dilated index `Fin N × ι`), isometry `V : Matrix (Fin N × ι) (Fin N) ℂ` with
  `isom : Vᴴ * V = 1`, and the pullback field
  `pullback : ∀ i, Vᴴ * blockProj i * V = (P.E i).M`, where
  `blockProj i := (1 : Matrix (Fin N) (Fin N) ℂ) ⊗ₖ (single i i 1)` is the rank-`N`
  ancilla-`i` projector `I_N ⊗ |i⟩⟨i|`.
  - `born_transfer : povmWeight ψ i = re ⟨Vψ, blockProj i (Vψ)⟩` via the
    `toEuclideanLin`/adjoint bridge (`⟨Vψ, Π Vψ⟩ = ⟨ψ, Vᴴ Π V ψ⟩ = ⟨ψ, Eᵢ ψ⟩`).
    Foundational triple.

- **P.3 — volume reading.** Same file (or `POVMVolume.lean`).
  - `blockProj i` in the computational basis is `∑_{n} |e_{(n,i)}⟩⟨e_{(n,i)}|`, so
    `⟨Vψ, blockProj i Vψ⟩ = ∑_{n} ‖⟨e_{(n,i)}, Vψ⟩‖²` (a coarse, rank-`N` outcome = a
    *union* of rank-1 cells).
  - Reindex `Fin N × ι ≃ Fin (N·K)` (`finProdFinEquiv`, `K = card ι`); transport `Vψ` to
    `EuclideanSpace ℂ (Fin (N·K))`; each `‖⟨e_{(n,i)}, Vψ⟩‖²` is a rank-1 FS volume
    (`fs_born_volume_ratio_N`). Sum over the block ⇒
    `povm_born_eq_dilated_volume : povmWeight ψ i = FS-volume(ancilla-block i)` on
    `Σ' = ℂℙ^{N·K−1}`. Foundational triple; **the headline conditional result.**

- **P.4 — empirical capstone.** `povm_born_frequency_volume`: i.i.d. FS trials on `Σ'`,
  frequency of landing in ancilla-block `i` → `povmWeight ψ i`. Compose
  `born_frequency_convergence_N` (full rank-1 vector jointly a.s.) with a finite
  block-sum (the block frequency is the sum of its cells' frequencies → sum of weights).
  **Main design risk (investigate first):** `born_frequency_convergence_N` needs `hpos`
  (*all* `N·K` dilated coordinates strictly positive). A POVM/ψ with a zero amplitude in
  some cell violates it. Two outs: (a) restrict to generic `(P, ψ)` with `Vψ` interior and
  carry a genericity caveat (cf. GHZ boundary); (b) prove a **block-coarsening** lemma over
  the lower `born_frequency_convergence_partition` layer that needs only *block-sum*
  positivity, not per-cell — check whether the partition layer tolerates zero-measure cells.
  Prefer (b) if the partition theorem allows it; else ship (a) and note (b) as follow-up.

### Phase 2 — existence (the CFC-sqrt half, makes Phase 1 unconditional)

- **P.5a — PSD matrix square root.** New `CsdLean4/Mathlib/LinearAlgebra/Matrix/PosSemidefSqrt.lean`
  (Cat-1, natural `namespace Matrix`). `PosSemidef.sqrt := hM.isHermitian.cfc Real.sqrt`; prove
  `sqrt_posSemidef`, `sqrt_isHermitian`, and the load-bearing `sqrt_mul_self : √M * √M = M`
  (CFC multiplicativity `cfc(f)·cfc(g)=cfc(fg)` + `Real.sqrt`-squared-on-`[0,∞)` = id on the
  spectrum). **Decision point:** if `IsHermitian.cfc`'s API lacks a usable `cfc_mul`, switch
  to the general `cfc`/`CFC.sqrt` (needs the `Matrix n n ℂ` C⋆-CFC instance) or the
  `eigenvectorBasis` hand build. Probe the three options in this order at P.5a start.

- **P.5b — canonical Naimark isometry.** `CsdLean4/LF4/POVMNaimark.lean`.
  `naimarkV (P) : Matrix (Fin N × ι) (Fin N) ℂ` with column action
  `(V ψ)_{(n,i)} = (√(E i) ψ)_n`, i.e. `V (n,i) m = (√(E i)) n m`. Prove
  `Vᴴ V = ∑_i √Eᵢ √Eᵢ = ∑_i Eᵢ = 1` (isometry, uses `sqrt_mul_self` + `P.complete`) and
  `Vᴴ (blockProj i) V = Eᵢ` (the pullback, `√Eᵢ I √Eᵢ = Eᵢ`). Output:
  `canonicalNaimark (P) : NaimarkDilation P`, inhabiting P.2's structure for **every** POVM.
  Then P.3/P.4 specialise to unconditional statements (modulo the P.4 genericity choice).

### Phase 3 — close-out

- **P.6 — audit + docs.** AxiomAudit-pin every export (`born_transfer`,
  `povm_born_eq_dilated_volume`, `povm_born_frequency_volume`, `canonicalNaimark`,
  `sqrt_mul_self`) to the foundational triple. Update `README.md` (POVM line under the
  moment-map cluster), `specs/INDEX.md`, and this file's status. If `PosSemidefSqrt.lean` is
  clean Cat-1, note it as a Mathlib upstream candidate alongside `PartialTrace.lean`.

### Suggested commit slicing

1. P.1 (POVM type + weights).  2. P.2 (NaimarkDilation + born_transfer).
3. P.3 (volume reading) — **Phase-1 headline, shippable here.**  4. P.4 (empirical capstone).
5. P.5a (CFC sqrt, Cat-1).  6. P.5b (canonical dilation) — **Phase-2 headline.**
7. P.6 (audit + docs). Each commit builds + `lake build CsdLeanTests` green, pins to the
triple. Phase 1 alone is a legitimate stopping point if Phase 2's sqrt API fights back.

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
