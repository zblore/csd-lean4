# External-library map — who owns what (Mathlib / Physlib / Lean-QIT / csd-lean4)

Created 2026-08-06 (author decision, recorded from the integration-strategy review).
**Read together with [`CSD-CHARTER.md`](CSD-CHARTER.md) §"Repository architecture".**
Open work driven by this map lives in [`BACKLOG.md`](BACKLOG.md) §H; the long-horizon
items are cross-referenced in [`future-work.md`](future-work.md).

## The architecture decision (2026-08-06)

**One repository.** `csd-lean4` is the unified formal repository for the complete CSD
quantum programme — foundations, measurement, records, composites, quantum information,
computation, cryptography, error correction, chaos, thermodynamics, classical emergence,
and later EFT/spacetime interfaces. There will be **no** satellite CSD repositories
(`csd-qit`, `csd-chaos`, …): splitting the theorem graph would break end-to-end claims
(the connectivity-manifest discipline depends on one graph).

**External libraries sit underneath, as dependencies — never as places where the
programme fragments.** The external library owns the *generic object*; `csd-lean4` owns
the *CSD theorem about that object* (ontic lifts, Σ-volume statements, record semantics,
de-isolation, information relocation on Σ).

```
Mathlib
   ├── Physlib            (physical systems, Hamiltonians, dynamics, chaos models)
   ├── Lean-QIT / Physlib-QuantumInfo   (states, channels, entropy, coding)
   ▼
csd-lean4                 (the complete CSD quantum programme)
```

**No external dependency is added today.** Toolchains (verified 2026-08-07):
`csd-lean4` Lean 4.33.0-rc1 (Mathlib `c732b96`); Physlib Lean 4.32.0 (Mathlib
`81a5d25`); Lean-QIT Lean **4.30.0** (Mathlib `c5ea003`). **Alignment target:
Physlib** — one minor version behind, community-maintained, active (commits daily as
of 2026-08-05; no 4.33-bump PR open yet); the convergence event is Lean 4.33.0
stable + Physlib's bump (our move is rc→stable, trivial). **Downgrading csd-lean4 is
FEASIBLE but not worth it** (measured 2026-08-07, correcting an earlier overstatement):
their Mathlib pin is only ONE WEEK older than ours (2026-07-13 vs 07-20) and carries
`extDeriv`/`alternatizeUncurryFin`/`skew_product`; the cost is a half-day of
rename-chasing (`mem_ofPred_eq` and kin, concentrated in the newest modules) plus a
full rebuild — but the benefit is nil: Physlib currently has NO theorem the corpus
would import (FiniteTarget is a thin wrapper over our native carrier; no
Floquet/chaos), so alignment today buys an unused dependency and chains our Mathlib
cadence to theirs. For the CONTRIBUTION direction (upstreaming Incubator generics to
PhyslibAlpha), develop the PR against THEIR toolchain in a separate worktree — no pin
change in csd-lean4 needed. Lean-QIT at three minor
versions behind validates the cited-not-imported posture on their DPI; if
SSA-unconditional becomes load-bearing first, the E2 ladder beats waiting. Until
versions align and a *specific theorem or API* is needed, external libraries are
studied, not imported.

## The four-way classification rule

Before implementing any generic quantum definition or theorem, check Mathlib, Physlib,
and Lean-QIT, and classify the addition:

1. **Already exists externally** → import it (once a dependency exists) and build the
   CSD theorem on top.
2. **Exists externally, incompatible types** → write an adapter in `CsdLean4/Interop/`;
   do not re-prove the external theory.
3. **Missing externally but required** → implement locally behind a generic interface;
   mark `upstream-candidate(physlib)` / `upstream-candidate(mathlib)`. If later
   upstreamed, the local generic implementation is replaced by an import; the CSD
   results stay (dependency consolidation, not fragmentation).
4. **Intrinsically CSD-specific** → permanent `csd-lean4` content.

**Single-provider rule.** Never two competing state/channel types through the corpus.
When an external QIT provider is eventually chosen, it is chosen capability-by-capability
(required theorem, cleaner API, compatible versions, conversion overhead, maintenance) —
but each capability layer gets ONE provider, connected through the canonical internal
interface (`CsdLean4/Interop/`), so the corpus can change providers without rewriting
theorems.

## Ownership table

Statuses: **ext-available** (exists externally, verified), **ext-claimed** (exists
externally per their docs, APIs not yet studied in detail), **local** (implemented in
csd-lean4; not seeking an upstream), **local-upstream-candidate** (implemented locally,
generic, may migrate), **missing** (nowhere yet), **CSD-permanent**.

| Capability | Intended owner | Status | Notes |
|---|---|---|---|
| Basic mathematics (measure, spectral, matrix exp) | Mathlib | ext-available | The pin carries `NormedSpace.exp`, cfc, `extDeriv` (flat), manifolds without symplectic forms |
| Finite quantum system abstraction | Physlib | ext-available (verified 2026-08-07) | `Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/` — `FiniteHilbertSpace d` is a structure **wrapping `EuclideanSpace ℂ d`**, the corpus's native carrier, so adapters are `.val`-thin. Their QM layer: FiniteTarget, HarmonicOscillator (1D ladder/TISE), FreeParticle. No generic time-evolution module found |
| Floquet systems, kicked models | Physlib (target) | **missing (verified 2026-08-07: 0 matches in their 690-module tree)** | Class 3 confirmed → implemented locally behind the H2 `FloquetEvolution` interface (`Incubator/QuantumChaos/FloquetInterface.lean`), `upstream-candidate(physlib)` |
| Chaos diagnostics (spectral form factor, Loschmidt echo, OTOC) | Physlib (target) | missing (verified 2026-08-07) | Will follow the same class-3 route when the §H thread reaches them |
| Density states, channels, POVMs, partial trace | csd-lean4 today; Lean-QIT or Physlib-QuantumInfo later | local | Our `Mathlib/QuantumInfo` tree — audit-validated 2026-08-06 (CL-022/023 chain). The chaos pilot CONSUMES this; it does not expand it |
| Entropy, subadditivity, Araki–Lieb, trace distance, DPI-conditional SSA | csd-lean4 today | local | Same tree; `Tests/EntropyWitness.lean` carries the committed witnesses |
| **Unconditional SSA / DPI** | Lean-QIT **or** local E2 ladder | ext-available (Lean-QIT) | **The first concrete Lean-QIT decision point**, already named in `StrongSubadditivity.lean`: their `relativeEntropy_dataProcessing_channel_ge` is cited-not-imported; the alternative is the E2 operator-convexity ladder (BACKLOG §E). Decide when SSA-unconditional is actually consumed |
| Coding theorems, one-shot information, recovery maps, capacities | Lean-QIT | ext-claimed | Evaluate against Physlib-QuantumInfo per capability when reached |
| Reversible-circuit arithmetic (adders, modular arithmetic) | csd-lean4 | local | Live corpus (measurement-adder consumers); B6 Mathlib upstreaming retired 2026-08-06 |
| Projectivization topology/measure, Wigner rigidity + uniqueness, FS uniqueness, Kähler pointwise + flat dω = 0 | csd-lean4 | local-upstream-candidate(mathlib) | The `CsdLean4/Mathlib/` staging tree; staging discipline stands even with B6 retired |
| CSD ontic lift (Σ, π, μL), Born-from-volume, typicality | csd-lean4 | CSD-permanent | LF1–LF4 + SigmaLayer |
| Records, de-isolation, Lüders/calibration, measurement dynamics | csd-lean4 | CSD-permanent | SigmaLayer/RecordLayer + LF5/LF6 |
| Scrambling / chaos interpreted on Σ; record persistence under Floquet | csd-lean4 | CSD-permanent (**pilot landed 2026-08-07**: `Empirical/CSD/QuantumChaos/` — ontic lift, sure record persistence, `floquetPilotClosure`) | Coupled driving PRICED and WITNESSED 2026-08-07 (`RecordDegradation.lean` + `CouplingWitness.lean`: half-life bound `≤ n·ε`, bitten at `ε = 1/2` by the fibre-triggered kick); Loschmidt echo landed (`Diagnostics.lean`). Continuation: attainment, SFF/OTOC |
| CSD empirical corrections / departures | csd-lean4 | CSD-permanent | `csd-departures-eft.md` |

## Interop and interface policy

- `CsdLean4/Interop/` holds adapters between external providers and the canonical
  internal interfaces. Created 2026-08-06 (documentation only until the first
  dependency lands).
- New generic objects the CSD layer consumes are declared as small abstract interfaces
  — the first is LIVE (H2, 2026-08-07): `QuantumChaos.FloquetEvolution` with
  `step : H ≃ₗᵢ[ℂ] H` (an *equivalence*: reversibility is load-bearing for the CSD
  reading), `Incubator/QuantumChaos/FloquetInterface.lean`, with iteration,
  information-preservation, induced ray dynamics, and the `ofUnitary` matrix adapter
  seam. CSD theorems never bind to a locally-invented concrete model. Adapters later instantiate the interface from
  Physlib dynamics, Lean-QIT channels, or the existing local matrix dynamics.
- **Consistency note (B6).** Upstreaming generic files to Physlib is NOT a reversal of
  the 2026-08-06 B6 retirement: B6 retired *Mathlib* PRs as a non-need. Physlib
  upstreaming is the strategic-positioning step-4 channel (consume upward, contribute
  downward, provenance) and is decided per file when toolchains align.

## Target internal topology (consolidation-release target — do NOT migrate now)

The long-term knowledge-area layout (Foundations / QuantumMechanics /
QuantumInformation / QuantumComputation / QuantumChaos / Thermodynamics /
ClassicalEmergence / Spacetime / EFT / Interop / Empirical / Mathlib / SigmaLayer) is
adopted as the **target** topology. Per the G10 decision, the existing 440+-module tree
is NOT re-homed mid-programme (moves churn imports, pins, and docs); the target applies
to **new workstreams immediately** (QuantumChaos starts under
`CsdLean4/Incubator/QuantumChaos/` while exploratory) and to the existing tree only at
a deliberate consolidation release when the record-layer tranche stabilizes.

## First chaos deliverable (the §H pilot)

One vertical CSD result, not a generic chaos framework: *a repeated
finite-dimensional unitary evolution preserves global information, changes restricted
accessibility, induces projective dynamics, admits an ontic lift under stated
conditions, and preserves a formed record when the record sector is invariant.*
Consumes the existing local QIT machinery; generic pieces go behind the
`FloquetEvolution` interface with `upstream-candidate(physlib)` marks.
