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
`csd-lean4` Lean **4.33.0 stable** (Mathlib tag `v4.33.0` = `db584cd6`; **bumped
2026-08-10**, the day 4.33.0 released — the planned single rc1→stable jump, skipping
rc2; cost: 2 call sites for a generalised `integrableOn_rpow_mul_exp_neg_mul_rpow`
hypothesis, 2 for the `LinearEquiv.ofLinear`→`ofLinearMap` rename, and 60 sites of the
new `have`-over-`haveI` / `let`-over-`letI` style linter; **every axiom pin passed
unchanged**). Physlib Lean 4.32.0 (Mathlib
`81a5d25`); Lean-QIT Lean **4.30.0** (Mathlib `c5ea003`). **Alignment target:
Physlib** — one minor version behind, community-maintained, active (commits daily as
of 2026-08-05; no 4.33-bump PR open yet); the convergence event is Lean 4.33.0
stable + Physlib's bump (our move is rc→stable, trivial). Cadence, measured
2026-08-07: Lean 4.33.0-rc2 is out (08-03; rc1→stable took ~4 weeks last cycle, so
stable ≈ mid/late August); Physlib bumps stable-only, ~8 days after release (their
toolchain history back to 4.29). Forecast alignment window: late August / early
September. Do NOT bump to rc2 meanwhile — one jump rc1→stable, skipping rc2, is the
plan.

> **⚡ ALIGNMENT VERIFIED 2026-08-17 — and the full rescan ran the same day.** Physlib
> took 4.33.0 stable on cadence: toolchain `leanprover/lean4:v4.33.0`, Mathlib
> `db584cd6…` — **byte-identical to our pins**, two weeks ahead of the forecast window.
> The contribution direction is now frictionless (their environment IS ours; the
> separate-worktree precaution below is moot while alignment holds).
>
> **Rescan of their tree (707 modules, was 690 on 2026-08-07).** Still absent:
> Floquet/kicked/stroboscopic (0 hits), chaos diagnostics (SFF/OTOC/Loschmidt: 0 hits) — the
> `upstream-candidate(physlib)` marks stand and are STILL new content for them;
> symplectic/Kähler manifold API (their Kähler hits are SUSY prose; no help for Q8/KG-1).
>
> ⛔ **RETRACTED 2026-09-01 — this rescan recorded a VERIFIED FALSE NEGATIVE, and it is the
> most consequential error in this file.** It reported "density matrices, channels, POVMs,
> partial trace, entropy, measurement theory, Lindblad (**0 hits**) — no external provider for
> our `QuantumInfo` tree". All of that is present and was present on the very commit the rescan
> read. Re-verified at physlib `b651a4af`, searching **their** vocabulary rather than ours:
> `MState` 25 files, `CPTPMap` 16, `HermitianMat` 44, `traceLeft`/`traceRight` 11 each, `POVM` 3,
> `Sᵥₙ` 4, `qRelativeEnt` 6, across an **84-module `QuantumInfo` Lake target**.
>
> **Cause, worth naming because it will recur:** the scan grepped OUR names (`PosSemidef`,
> `partialTrace`, `vonNeumannEntropy`, `relEntropy`) against a library that spells them
> `HermitianMat`/`nonneg`, `traceLeft`/`traceRight`, `Sᵥₙ`, `qRelativeEnt`. The module *count*
> in the note is right (576 + 47 + 84 = 707), so the scan enumerated these files and the search
> missed them. **A vocabulary-blind grep is not a consumption verdict.**
>
> ★ **What is actually there**, and it bears directly on the DPI/SSA row of `BACKLOG.md`:
> `QuantumInfo/Entropy/SSA.lean` proves `Sᵥₙ_strong_subadditivity` **unconditionally**, and
> `Entropy/DPI.lean` proves `qRelativeEnt_joint_convexity` — the deep input our `hDPI` encodes.
> `ForMathlib/HayataGroup/TraceInequality/` carries the whole operator-convexity stratum
> (`OperatorConvexOn`, `JensenOperatorInequality`, `LownerHeinzTheorem`,
> `GeneralizedPerspectiveFunction`, `LiebAndoTrace`), ported from
> `Hayata-Yamasaki-Group/lean-quantum` (arXiv:2607.05492). ⚠️ And **the toolchain objection that
> ruled out Lean-QIT does not apply here**: physlib pins `leanprover/lean4:v4.33.0` and resolves
> mathlib to `db584cd6d46c92f209a44c0f1c829460d327499d` — **byte-identical to ours** (verified in
> their `lake-manifest.json`). The SSA import cone is 56 `QuantumInfo` modules and is
> `sorry`-free (static check; the `#print axioms` gate is still required before relying on it).
> What they DID add since the baseline, none of it consumable: `FiniteTarget.timeEvolution
> = NormedSpace.exp(-(it/ℏ)•Ham)` (supersedes the "no generic time-evolution" note below —
> but a thin wrapper; ours carries the C¹-Stone derivation and Kähler invariance), a
> continuum `Operators/` tree (unbounded operators, spectral measures `SpectralTheory/`,
> completed tensor products — the infinite-dim rung our scope ladder defers), Wirtinger
> calculus with Schwarz's theorem (`Mathematics/Calculus/Wirtinger/` — adjacent to the
> KG-3 holomorphic route at best), and pedagogical potentials (Hydrogen, Pöschl–Teller,
> square wells).
>
> **Two coordination signals, both watch-items not work-items.** (i) A top-level
> `QuantumInfo/` tree now EXISTS in their repo — `States/Pure/{Braket, BlochSphere,
> BargmannInvariant}.lean`, the latter two not yet imported into their build — and the
> Qubit API-map's roadmap explicitly plans density matrices "with their evolution,
> measurements and distinguishability measures" as a separate API map. **Physlib-QuantumInfo
> (this map's named "later" provider) is visibly under construction**: when their
> density-matrix layer lands, the four-way check starts hitting it. (ii) **Bargmann
> collision surface**: their unbuilt `bargmannInvariantThree` (117 lines, Ket-level)
> overlaps our proved, projective, branch-separating `Projectivization.bargmann` stack
> (load-bearing in W3 unitary selection). When upstreaming resumes, our Bargmann +
> WignerRigidity staging is the natural PR into exactly this lane — offer ours before
> they rebuild it.

**Downgrading csd-lean4 is
FEASIBLE but not worth it** (measured 2026-08-07, correcting an earlier overstatement — and MOOT since the 2026-08-17 alignment):
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
| Finite quantum system abstraction | Physlib | ext-available (verified 2026-08-07; re-scanned 2026-08-17) | `Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/` — `FiniteHilbertSpace d` is a structure **wrapping `EuclideanSpace ℂ d`**, the corpus's native carrier, so adapters are `.val`-thin. Their QM layer: FiniteTarget, HarmonicOscillator (1D ladder/TISE), FreeParticle. ~~No generic time-evolution module found~~ *Superseded 2026-08-17:* `FiniteTarget.timeEvolution = exp(-(it/ℏ)•Ham)` now exists — a thin `NormedSpace.exp` wrapper with matrix forms; ours keeps the C¹-Stone derivation and Kähler invariance, so consumption value stays nil |
| Floquet systems, kicked models | Physlib (target) | **missing (verified 2026-08-07; re-verified 2026-08-17: 0 matches in 707 modules)** | Class 3 confirmed → implemented locally behind the H2 `FloquetEvolution` interface (`Incubator/QuantumChaos/FloquetInterface.lean`), `upstream-candidate(physlib)` — with pins now byte-aligned, the PR costs no toolchain work |
| Chaos diagnostics (spectral form factor, Loschmidt echo, OTOC) | Physlib (target) | missing (verified 2026-08-07; re-verified 2026-08-17) | Class 3 — ALL THREE implemented locally 2026-08-07/08 behind the interface (`Diagnostics`, `SpectralFormFactor`, `Otoc`, `EchoBound`), `upstream-candidate(physlib)` |
| Density states, channels, POVMs, partial trace | csd-lean4 today; Lean-QIT or Physlib-QuantumInfo later | local | Our `Mathlib/QuantumInfo` tree — audit-validated 2026-08-06 (CL-022/023 chain). The chaos pilot CONSUMES this; it does not expand it |
| Entropy, subadditivity, Araki–Lieb, trace distance, DPI-conditional SSA | csd-lean4 today | local | Same tree; `Tests/EntropyWitness.lean` carries the committed witnesses |
| **Unconditional SSA / DPI** | Lean-QIT **or** local E2 ladder | ext-available (Lean-QIT) | **The first concrete Lean-QIT decision point**, already named in `StrongSubadditivity.lean`: their `relativeEntropy_dataProcessing_channel_ge` is cited-not-imported; the alternative is the E2 operator-convexity ladder (BACKLOG §E). Decide when SSA-unconditional is actually consumed |
| Coding theorems, one-shot information, recovery maps, capacities | Lean-QIT | ext-claimed | Evaluate against Physlib-QuantumInfo per capability when reached |
| Reversible-circuit arithmetic (adders, modular arithmetic) | csd-lean4 | local | Live corpus (measurement-adder consumers); B6 Mathlib upstreaming retired 2026-08-06 |
| Projectivization topology/measure, Wigner rigidity + uniqueness, FS uniqueness, Kähler pointwise + flat dω = 0 | csd-lean4 | local-upstream-candidate(mathlib) | The `CsdLean4/Mathlib/` staging tree; staging discipline stands even with B6 retired |
| CSD ontic lift (Σ, π, μL), Born-from-volume, typicality | csd-lean4 | CSD-permanent | LF1–LF4 + SigmaLayer |
| Records, de-isolation, Lüders/calibration, measurement dynamics | csd-lean4 | CSD-permanent | SigmaLayer/RecordLayer + LF5/LF6 |
| Scrambling / chaos interpreted on Σ; record persistence under Floquet | csd-lean4 | CSD-permanent (**pilot landed 2026-08-07**: `Empirical/CSD/QuantumChaos/` — ontic lift, sure record persistence, `floquetPilotClosure`) | Coupled driving PRICED and WITNESSED 2026-08-07 (`RecordDegradation.lean` + `CouplingWitness.lean`: half-life bound `≤ n·ε`, bitten at `ε = 1/2` by the fibre-triggered kick); Loschmidt echo landed (`Diagnostics.lean`). CV pillar joined 2026-08-07: free + interacting diagonal drives reach the same pilot closure (`FreeFieldClosure.lean`); free dynamics preserves mode support (`CV/DynamicalLocality.lean`) and interacting dynamics is confined to the coupling-graph light cone (`CV/SupportSpreading.lean`, one edge per period) with the locality violation priced linearly in the coupling (`CV/InteractionPrice.lean`, Duhamel route) and the price's cutoff scaling graded by operator content (`CV/PowerCounting.lean` — Stage 3 complete). Continuation DISCHARGED 2026-08-08: SFF/OTOC/echo-bound landed (with the OTOC light-cone gate and the echo price on the Stage-3 drives, `CV/ChaosBounds.lean`) and the half-life bound proved SHARP (`HalfLifeAttainment.lean`, cyclic kick attains `n·ε` exactly on the window). Remaining continuation (recorded, unqueued): growth rates / level statistics (RMT) |
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
