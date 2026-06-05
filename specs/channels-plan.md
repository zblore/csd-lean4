# K2 — CPTP channel infrastructure plan

The channels keystone (K2 of [`qi-qec-roadmap.md`](qi-qec-roadmap.md)). A finite-dimensional
quantum-channel framework, built on the corpus's existing Stinespring (`canonicalNaimark`)
and partial-trace (`Matrix.traceRight`) primitives. Created 2026-06-05.

## 0. Why

Three drivers:
1. **QEC errors are channels.** The honest ontic error model is decoherence (system→
   environment volume flow), not a coherent flow on `Σ_sys`; the error model *is* a CPTP
   channel and the "volume loss" *is* the partial-trace step (see `Empirical/CSD/QEC/`).
2. **No-communication CPTP form** (completes E3 in `qm-empirical-tests.md`): Alice's general
   *channel* — not just a unitary — leaves Bob's reduced state invariant.
3. **The structural on-ramp to `Φ ≠ id`.** A channel's Stinespring dilation is a
   measure-preserving flow on `Σ_sys × Σ_env`; channels are the first place the corpus
   exhibits a non-trivial flow with operational meaning.

## 1. Representation choice and location

**Kraus** as the working definition (concrete, CP-by-construction), **Stinespring** as the
dilation theorem (the ontic flow form) plus the Kraus↔Stinespring bridge. `apply` acts on
general matrices (a linear map); density-operator preservation (Hermitian + PSD + trace) is
a theorem.

**Cat-1** (CSD-free, Mathlib-upstreamable) → `CsdLean4/Mathlib/QuantumInfo/Channel.lean`,
namespace `QuantumInfo` (not `Matrix` — a channel is a quantum-info object, the directory is
`QuantumInfo/`, and `namespace Matrix` is fragile here once `ℂ`/`ComplexOrder` instances are
in play; upstream a channel would plausibly live under a `QuantumInfo` root too).
Consumers (no-comm CPTP, QEC error channel) and the CSD reading land in `Empirical/`.

## 2. Phases

### C1 — the type + trace-preserving / positive core — **DONE 2026-06-05**
- `QuantumInfo.Channel n m ι`: `kraus : ι → Matrix m n ℂ` with the TP constraint
  `∑ᵢ (kraus i)ᴴ * (kraus i) = 1`.
- `Channel.apply ρ := ∑ᵢ kraus i * ρ * (kraus i)ᴴ`; `apply_add`, `apply_smul` (linear).
- `apply_trace` (`Tr(Φ ρ) = Tr ρ`, via TP + trace cyclicity), `apply_posSemidef`
  (PSD-preserving), `apply_isHermitian`.
- `Channel.id` (identity channel) as the inhabiting instance.
- *Difficulty: low.* Pure matrix algebra reusing `PosSemidef.mul_mul_conjTranspose_same`,
  `trace_mul_cycle`. **Built green; `apply_trace`/`apply_posSemidef`/`apply_isHermitian`
  AxiomAudit-pinned (foundational triple).** Next: C3 unitary/trace-out, then C4 no-comm CPTP.

### C2 — Stinespring dilation (the ontic flow form; reuse `PartialTrace`) — **DONE 2026-06-05**
- `Channel.ofIsometry (V) (hV : Vᴴ V = 1)`: `ρ ↦ traceRight (V * ρ * Vᴴ)` — isometry into
  system⊗environment, then trace the environment. TP from the isometry (`ofIsometry_apply`).
- `dilation_exists` = `stinespringIsom` + `stinespringIsom_isom`
  (`(stinespringIsom Φ)ᴴ (stinespringIsom Φ) = 1`) + `apply_eq_traceRight_stinespring`
  (Kraus ⇒ Stinespring isometry, stacking the Kraus operators); `kraus_of_isometry` =
  `ofIsometry` (the converse, Kraus = the env-blocks of `V`).
- The whole bridge rests on one block identity for a general `V`: `krausBlock`,
  `sum_krausBlock_conjTranspose_mul` (`∑ᵢ (krausBlock V i)ᴴ (krausBlock V i) = Vᴴ V`, so
  isometry ⟺ TP) and `traceRight_conj_eq_sum_krausBlock` (env-averaged conjugation = Kraus
  action). `canonicalNaimark` not needed (it specialises to the measurement-channel case).
- File `CsdLean4/Mathlib/QuantumInfo/Stinespring.lean`, all foundational-triple-only
  (`stinespringIsom_isom` / `apply_eq_traceRight_stinespring` / `ofIsometry_apply`
  AxiomAudit-pinned). This module realises "channel = env-averaged joint flow".
  *Difficulty was: medium* (reindex/block algebra; partial trace already built).

### C3 — the canonical channels — **DONE 2026-06-05**
- `unitaryChannel U hU` (single Kraus, `apply ρ = U ρ Uᴴ`; generalises `Channel.id`);
  `traceOutChannel s env` (`apply ρ = traceRight ρ` — the literal volume-loss-to-environment,
  obtained for free as C2's `ofIsometry 1`); `mixedUnitaryChannel U hU p hp0 hp`
  (`apply ρ = ∑ᵢ pᵢ • Uᵢ ρ Uᵢᴴ`, Kraus `√pᵢ • Uᵢ`).
- **Deviation from plan:** instead of bespoke `dephasingChannel` / `depolarizingChannel`
  (which would import a specific Pauli family), C3 ships the general **mixed-unitary**
  channel — dephasing / depolarizing / bit-flip are its instances with a concrete Pauli
  `U`, assembled by the consumer (the QEC files already carry Paulis). This keeps the Cat-1
  staging file **Pauli-free**.
- File `CsdLean4/Mathlib/QuantumInfo/CanonicalChannels.lean`; `unitaryChannel_apply` /
  `traceOutChannel_apply` / `mixedUnitaryChannel_apply` AxiomAudit-pinned (foundational
  triple). *Difficulty was: low–medium* (the √p scalar bookkeeping in mixed-unitary TP).

### C4 — the first payoffs
- **No-communication CPTP form** — **DONE 2026-06-05.**
  (`Empirical/QM/NoCommunication.lean`: `channel_no_communication`):
  `traceLeft((Φ_A ⊗ id) ρ) = traceLeft ρ` for *any* channel `Φ_A` — generalises the unitary
  `no_communication_reduced`; the TP property `∑ᵢ Kᵢᴴ Kᵢ = 1` is the key. **Retires E3's CPTP
  gap.** Built on two new pieces: the Cat-1 Kraus-summed partial-trace lemma
  `Matrix.traceLeft_sum_conjTranspose_kronecker_one` (generalises the single-unitary
  `traceLeft_conjTranspose_kronecker_one`) and the local channel
  `QuantumInfo.Channel.tensorRight` (`Φ ⊗ id`). Foundational-triple-only, AxiomAudit-pinned.
- **The QEC error channel** — *remaining C4 sub-item.* The bit-flip error as a
  `mixedUnitaryChannel {I, X}` instance applied to a codeword — the honest "error =
  decoherence" statement. (Full *correction* still needs the syndrome measurement-update =
  LF5.)
- *Difficulty was: medium* (the 4-sum reorder in the Kraus-summed partial-trace lemma).

### C5 — deferred / Mathlib-scale (later, some need K3)
- Full complete-positivity characterisation (Choi-PSD ⟺ CP). *Note:* Kraus channels are CP
  by construction, so CP is available for everything in C1–C4 without this; only the abstract
  equivalence is hard.
- Data-processing inequality (channels contract trace distance) — needs **K3**.
- Composition, identity, capacities.

## 3. The CSD reading (`Empirical/CSD/`)

A channel **is** the environment-averaged image of a measure-preserving flow on
`Σ_sys × Σ_env`: the Stinespring isometry (C2) is the joint flow — a genuine `Φ ≠ id` on the
enlarged `Σ` — and `traceRight` is the environment average. So C2 is the structural on-ramp
to the dynamics frontier, and the QEC decoherence reading (error channel = the joint flow's
environment-marginal; "volume loss" = the partial trace) becomes a real statement.

## 4. Dependency graph and ordering

```
C1 (Kraus core) ──► C2 (Stinespring; reuses PartialTrace + canonicalNaimark)
                      ├─► C3 (unitary / trace-out / dephasing channels)
                      │     ├─► C4 no-comm CPTP (completes E3)  ← first real payoff
                      │     └─► C4 QEC error channel
                      └─► CSD reading (channel = env-averaged Φ on Σ_sys×Σ_env)
C5 (full CP, data-processing) ── needs K3 (trace distance)
```

C1–C3 are tractable now (matrix algebra reusing existing primitives). C4 is the first genuine
theorem and retires a standing gap (E3 CPTP). C5 is the Mathlib-scale residue, off the
critical path. Recommended order: **C1 → (C3 unitary/trace-out) → C4 no-comm CPTP**.
