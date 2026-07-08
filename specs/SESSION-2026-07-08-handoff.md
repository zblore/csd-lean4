# Session handoff — 2026-07-08 (connectivity fixes C1–C5, Paper-C cross-check)

Single-page state so the next session can resume without re-deriving. The
authoritative per-link ledger is [`connectivity-manifest.md`](connectivity-manifest.md);
the todo backlog is [`future-work.md`](future-work.md). This file is the narrative.

## What was done this session (all committed + pushed to `origin/main`)

The 2026-07-07 provenance audit found the "one Kähler object → both pillars"
claim was **not realized in code** (individual theorems real, but unconnected).
The fix course C1–C6 was defined; this session landed C1–C5.

| Commit | Fix | Result |
|---|---|---|
| `23c0338` | **C3** | Retracted the README overclaim; wrote the connectivity manifest; added `scripts/check-connectivity.sh` (self-tested guard). |
| `74a1ac4` | **C1** | `rotationSetup` — a genuine `Φ ≠ id` `KahlerOnticSetup` (ℂℙ¹ rotation flow), `projectedFlow ≠ id`. Link L4 CONNECTED. |
| `1620386` | **C2** | `rotationSetup_schrodinger_form` — W-series capstone fired on the non-trivial flow, recovers `H = σ_y ≠ 0`. Link L3 CONNECTED. (`LF4/RotationSchrodinger.lean`) |
| `6436c22` | **C4** | `rotationSetup_both_pillars` — Born ∧ Schrödinger on ONE object; Born law stated with sampling measure = the sector's own `liouvilleMeasure`. Links L5/L6 CONNECTED. (`LF4/BothPillars.lean`) |
| `f3e4b19` | **C5** | `IsLiouvilleKahlerVolume` made load-bearing (normalized-volume core, consumed by `unitaryFlowSetup_liouville_isProbability`); `IsKahlerSector` honestly demoted (no Mathlib Kähler API). README top restored (structural claim, guarded). Link L1 PARTIAL. |
| `324c8bf` | Paper-C cross-check | Recorded the `π = id` degeneracy caveat; added C7 + KG-1/2/3 to the backlog. |

Build discipline held throughout: `lake build` + `lake build CsdLeanTests`
(AxiomAudit `#print axioms` pins, foundational triple only) green; all three
static guards (`check-axiom-imports`, `check-sector-linkage`,
`check-connectivity`) green.

## Connectivity ledger now: L2–L6 CONNECTED

A single genuine `Φ ≠ id` object (`rotationSetup`) supports both pillars.
**Two gaps remain**, of very different character:

- **L1 (Kähler geometry)** — the differential-geometric content (2-form ω,
  complex structure J) is unformalizable today (no Mathlib API). Only its
  normalized-volume core is formalized. *Formalization-depth, not correctness*:
  μ_FS is provably the unique invariant measure (`fubiniStudyMeasure_unique`),
  so the object is already the right one.
- **L7 / FND-1 (Born from the flow)** ★ — the deep frontier. Born trials still
  *sample* μ_FS i.i.d.; they are not *evolved by* the deterministic flow, and
  the weights are not *derived from* the dynamics. The A5→D1 sector-origin
  problem. Research-grade; may not close. Paper C itself defers this.

## Three architectural findings from the Paper-C cross-check

Paper C = *A Deterministic Reconstruction of Finite-Dimensional QM*
(`Paper_C___1_05.txt`). The theorems we have are **valid**, and our
posited-sector scope **matches Paper C's own** (§1.4: Σ, π, and the A5 sector
are *assumed, not derived*). Three clarifications worth keeping:

### (a) Two Schrödinger routes — the Lean corpus uses Wigner, NOT Paper C's Ashtekar–Schilling
There is **no Ashtekar–Schilling anywhere in the corpus** (grep-confirmed). Every
Schrödinger derivation (`sigmaFlow_schrodinger_form`, `rotationSetup_schrodinger_form`)
runs: FS-isometry → **Wigner rigidity** → Bargmann branch → phase-lift → Stone →
`exp(-itH)`. Paper C §3.4 uses **Ashtekar–Schilling** (projected holomorphic
vector field → Schrödinger). Same endpoint, different theorem. The corpus chose
Wigner **because it is the formalizable route**: Wigner needs only the FS metric's
isometry structure (in Mathlib today); Ashtekar–Schilling needs the Kähler
symplectic form + Hamiltonian vector fields (the KG-blocked API).

### (b) The π mapping is a two-track split
| Track | Structure | π | Σ | Status |
|---|---|---|---|---|
| **Born / measurement** | `SectorData` (LF2) | `Prod.fst` | `KSigma = ℂℙ^{N-1} × T²` | **genuine many-to-one**, fibres = T², real pushforward `π∗μL = μ_FS` (`k_measure_bridge`) |
| **Schrödinger** | `KahlerOnticSetup` (LF4) | `id` (all instances) | `ℂℙ^{N-1}` | **trivial projection** |

Born has the projection but trivial ray dynamics (`kFlow` moves only the torus);
Schrödinger has the dynamics but `π = id`. Different structure types — the reason
C4's one-object had to be the `π = id` one. Paper C's A3 requires a smooth
many-to-one π with non-trivial fibres, so `rotationSetup` runs the degenerate
limit of Paper C's architecture.

### (c) KG (Kähler geometry) is what would reunify everything with the papers
Formalizing KG-1 (ω, `μ_FS = ω^n/n!`) → KG-2 (Hamiltonian vector field) → KG-3
(Ashtekar–Schilling) would: (1) put the corpus back on Paper C's actual argument;
(2) give a **second, independent** Schrödinger proof (geometric) provably agreeing
with the Wigner one; (3) provide one geometric language for π/μ/flow/dynamics,
knitting the Born and Schrödinger tracks onto one Σ. **But**: XL and *blocked* on
Mathlib's missing Kähler API (greenfield, plausibly larger than all work so far);
does NOT close FND-1 (sector origin stays open — Paper C posits it too).

## Recommended next step

Two open, non-overlapping directions:
- **C7** (`future-work.md`, Foundations, **M**, unblocked) — build a genuine
  many-to-one-π object (Σ = ℂℙ^{N-1} × T², π = Prod.fst) whose flow projects to a
  *non-trivial* ray rotation, and fire both pillars on it. Removes the `π = id`
  degeneracy; the cheap structural win. **User was asked whether to do this next;
  no answer given before session close.**
- **KG-1/2/3** (`future-work.md`, blocked) — the deep geometric reunification with
  Paper C. Large; gated on Mathlib.
- **FND-1** ★ — the actual thesis gap (Born from the flow). Unchanged.

Everything is honest and guarded: `check-connectivity.sh` fails the build if the
retracted overclaim phrases reappear, and the manifest is the single source of
truth for what "connected" means per link.
