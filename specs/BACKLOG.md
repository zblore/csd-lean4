# BACKLOG — the single canonical open-items list

> **This is the ONE place open work lives.** Do not add TODO / future-work / "next
> steps" / open items to any other `.md`. The per-phase plans (`LF*-plan`, `shor-plan`,
> `povm-plan`, …) are **historical execution logs** — frozen; read them for how a
> completed layer was built, not for what is open. The status/claims docs
> (`reconstruction-status`, `connectivity-manifest`, `PLACEHOLDERS`, `AXIOMS`,
> `BRIDGE-OBLIGATIONS`) describe *what is proved*; they point here for *what is next*.
>
> Effort key: **S** hrs–day · **M** days–2wk · **L** weeks · **XL** Mathlib-scale.
> Last updated 2026-07-19.

---

## M — genuinely closeable, real content

| Item | Status / what's needed | Former source |
|---|---|---|
| **Choi converse** (PSD Choi ⇒ Kraus) | **Sketched, not started.** Needs the missing piece: a vectorization / reshape iso (eigenvector → Kraus operator). Have: `choiMatrix` forward, Kraus→CPTP, Stinespring. | `qi-qec-roadmap.md` |
| **Gisin's theorem** (pure entangled ⇒ CHSH violation) | **Sketched, not started.** Needs the missing piece: a Schmidt decomposition of a general pure bipartite state (not in repo). Have: CHSH / Tsirelson machinery for the singlet. Unblocks LF6-6. | `lf6-plan.md` (LF6-8) |
| **Busch–Gleason** (effect-Gleason, finite-dim) | Deletes the one imported axiom `busch_effect_gleason` → "three axioms, zero imported". **Cosmetic** (NG2): not needed for CSD — ontic Born is Gleason-free. Do only for audit-posture. | `AXIOMS.md §2.2` |
| **Separate the ecdsa.fail track** | Real carve, not zero-coupling (see the dedicated section below). | `ecdsafail-two-track.md` |

## L — weeks

| Item | Status / what's needed | Former source |
|---|---|---|
| **Operator convexity → unconditional SSA** | **Parked on an instance wall.** Detailed ladder (steps 0→7) in `operator-convexity-plan.md`; the immediate blocker is step 0 (ℂ-smul Löwner monotonicity + spectrum-restricted `affine_output`; the `PartialOrder ℂ` cascade). Endpoint: discharge `hDPI` in `strong_subadditivity_of_relEntropy_monotone`. | `operator-convexity-plan.md` |
| **GKSL / Lindblad open-systems tier** (LF6-9) | General `Φ_t = e^{tℒ}` + complete positivity. Buildable in-repo on the existing Kraus/Choi/Stinespring infra. Unblocks LF6-2 full + Metrology A4. | `lf6-plan.md` |
| **§14 *states* obligation** | NoBroadcasting / SuperdenseCoding / Teleportation cite §14 for **state/projector** realisation (distinct from the observable-correspondence, which is now connected for SG/Uncertainty/Hardy). No LF4 content to cite → needs genuine new state-realisation content. | `BRIDGE-OBLIGATIONS.md` |
| **Lévy / spherical isoperimetry** (TH-1) | Canonical-typicality concentration (single-state typicality). Mathlib lacks spherical isoperimetry; the mean is proved. Optional strengthening. | `thermo-plan.md` |
| **Continuity-only Stone** | The non-C¹ Stone strengthening (drop the smoothness hypothesis). The C¹ case is done. | `future-work.md` (W5-S2) |

## XL — Mathlib-scale (depth, not correctness)

| Item | Status | Former source |
|---|---|---|
| **Manifold exterior calculus** (Kähler `dω=0`, symplectic gradient — KG-1/2/3) | Genuine upstream gap; the volume is forced and the pointwise Kähler core is proved, so this is formalization-depth, not a correctness gap. | `future-work.md` (KG-1/2/3) |
| ~~Pointwise Birkhoff ergodic theorem~~ | **Do not pursue** — the single-flow route is a proved dead-end CSD does not take (NG1). | — |

## Research — physics-first, not formalization tasks

| Item | Note | Source |
|---|---|---|
| **A5 sector origin** (derive `(Σ, π, G)` from primitive ontology) | The one genuine ★ open frontier. `flow_admits_invariant_ne_fubiniStudy` proves a single flow can't do it. | `reconstruction-status.md §7` |
| **Track B — quantum relaxation** (Valentini H-theorem) | The only route to *new predictions* past the "empirically identical" ceiling. | `project` note |
| **CV chain** — continuous spectra | Extend Born-as-volume past finite `ℂℙⁿ`. Foundations begun (`CsdLean4/CV/`). | `project` note |

---

## ecdsa.fail separation

**Folder move DONE 2026-07-19.** The non-QM-core code now lives in one folder,
`CsdLean4/Ecdsafail/` (21 files): the ECDLP tree (17 — elliptic curves, secp256k1,
point add/double, scalar mul, safegcd) plus the 4 ecdsa-specific circuit-assembly files
(`ProgramRouter`, `ProgramRouterDoubling`, `DoublingAssembly`, `DoublingAssemblyOps`).
The generic reversible-arithmetic DSL (`CuccaroAdd`, `ModMul`, `ModInv`, …) stayed in
`Reversible/` — it is shared with core-QM (Shor + `MeasurementGidneyAdder`/`Uncompute*`).
The core aggregator `CsdLean4.lean` has **zero** ecdsa references; `check-claims`'s
exclude path updated to `CsdLean4/Ecdsafail`.

**Lake-lib split + audit split DONE 2026-07-19.** `Ecdsafail` is now its own `lean_lib`
target (`lakefile.toml`, root `CsdLean4.Ecdsafail.AxiomAudit`); the ecdsa `#print axioms`
pins moved out of the core `Tests/AxiomAudit.lean` into `CsdLean4/Ecdsafail/AxiomAudit.lean`
(3 blocks: the 4 assembly `Reversible.*` pins, the ECDLP-proper `ECDLP.*` pins, and the
`ECDLP.Safegcd.*` divstep pins). `lake build CsdLean4` and `lake build CsdLeanTests` no
longer reach ecdsa; `lake build Ecdsafail` builds + audits the track on its own.

**Only genuinely-remaining split item (S, optional):** relocate the 6 `specs/ecd*` /
`specs/ecdsafail-*` doc files into an `ecdsa/` subtree, and (if ever wanted) a fully
separate repo sharing the `Reversible/` arithmetic DSL as a base. The code and build are
already fully separated.

---

## Done this session (2026-07-19)

Honesty guard (`check-claims.sh`) · Track A#1 Schrödinger derivation · Track A#2 Kähler de-vacuum · A5/L7 ergodic bracket · §13.2 all 9 gates · §14 measurement connections (SG/Uncertainty/Hardy) · Mach–Zehnder · Double-slit + complementarity · **composite mixed-Born on `DensityOperatorIx`** (FND-T3 T9).

## Settled non-goals — do not re-litigate (see `reconstruction-status.md §7a`)

- **NG1** — single-flow / Birkhoff / ergodic route to Born: proved dead-end; CSD forces typicality by the LLN.
- **NG2** — Busch–Gleason "needed for CSD": no; the ontic Born rule is Gleason-free.
