# Future work — priorities, dependencies, complexity

**Living planning doc (created 2026-07-04).** Every open work item with a stable reference number,
dependencies, and complexity, so priorities can be evaluated and items cited by id ("do EC-1").

**Legend.** Complexity: **S** = bounded (hours), **M** = one tranche, **L** = multi-tranche / genuinely
hard, **XL** = research-grade / multi-session. **★** = actually reduces the deep A5/D1 residue
(thesis-critical); everything else is breadth, consolidation, or tooling. Status: OPEN unless noted.

## Foundations / the deep frontier

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **FND-1** ★ | A5 → D1: derive the sector `(π,G)` + FS typicality from the deterministic dynamics | none (hard) | **XL** | The deepest residue under all of LF6/Wigner/thermo. The only work that closes the thesis gap. No clean on-ramp yet (onramps: `TypicalityForcing`, D1c). |
| **FND-2** ★ | D1c-entangled: thread a genuine `Φ≠id` through a concrete *entangled* SectorData | LF6 tier | **M** | Most tractable genuine A5 attack; mirrors D1c-1/-2. |
| **FND-3** ★ | §13.2 ontic lift: thread `Φ` + prove `TransProbPreserving f_Φ` on `kSectorData` | Wigner (done) | **M** | Makes the A5→Wigner→U_isometry chain explicit on the non-trivial-fibre instance. Caveat C-1: sector-action-carries-isometry, so partly consolidation. |

## LF6 entangled tier (remaining)

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **LF6-1** | Flow-capstone d-intrinsic reroute: route `maxEntangledDeisolation_flow_capstone` conjunct-7 through the general-d CGLMP force (not the Φ⁺ sector) | CGLMP general-d (done) | **S** | Cheap cleanup; the CGLMP expert's named follow-on. |
| **LF6-2** | Lindblad / continuous-time open-system de-isolation (T1/T2 semigroup) | LF6-B | **L** | Subsumes Metrology A4; the dynamics half of decoherence. |
| **LF6-3** | Marginal volume-drift geometry (symplectic drift of the reduced state) | LF6-B, LF5 | **M** | |
| **LF6-4** | Metrology A4: decoherence as open symplectic drift | LF6-2 (Lindblad) | **M** | D1-gated. |

## Thermodynamics track (`thermo-plan.md`)

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **TH-1** | Canonical typicality: `E_{μFS}[ρ_S] = I/d_S` (avg) + Levy stretch | μ_FS + partial trace | **M** | Flagship; IN PROGRESS 2026-07-04. |
| **TH-2** | Second law: coarse-grained vN entropy monotone under the de-isolation flow | TH-1 / LF6-B.3 | **M** | Generalises the single-step entropy witness. |
| **TH-3** | Temperature / free energy: Gibbs max-entropy state, `T=∂S/∂E`, `F=E−TS`, variational principle | vN entropy (K1) | **M** | |
| **TH-4** | Landauer erasure bound `≥ kT ln2` | TH-3, QEC tier | **M** | Info-thermodynamics. |
| **TH-5** | ETH / fluctuation theorem (Jarzynski/Crooks) | TH-1..3 | **L** | Stretch. |

## CV / continuous-variable track

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| ~~W4~~ | ApproxCCR finite-dim CCR obstruction | — | — | DONE (committed). |
| **CV-1** | Finite position observable on a lattice | W4 | **S/M** | NEXT after TH-1. |
| **CV-2** | Finite momentum: conjugate basis via finite Fourier | CV-1 | **M** | |
| **CV-3** | Approximate CCR: `‖[Q_N,P_N]−iℏ·1‖ ≤ ε` on a low-energy sector | CV-1, CV-2 | **M/L** | The quantitative finite-sector-recovers-continuum claim; highest-value CV item. |
| **CV-4** | Oscillator truncation recovers finite-energy predictions | CV-1..3 | **M** | |

## W-series (CSD dynamics spine — needs specs)

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **W-2** | KählerOnticSetup (user #1 priority) | spec needed | **L** | Needs the spec (as given for W4). |
| **W-3** | UnitarySelection | spec needed, Wigner | **M/L** | |
| **W-5** | ProjectedDynamics | spec needed | **L** | |

## ecdsa.fail / ECDLP

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **EC-1** | Safegcd termination: `g→0` within `2n` (potential-function argument) | safegcd divstep (done) | **L** | The load-bearing residual keeping inversion trusted; self-contained integer combinatorics. |
| **EC-2** | Safegcd reversible circuit: `divstepGadget` with `denote = divstep`, cost over a proven circuit | divstep + Reversible DSL | **M/L** | Promotes the cost-side from documented to circuit-backed. |
| **EC-3** | Gidney measurement adder as a verified circuit (task #36) | measurement-discipline DSL ext (EC-6) | **M/L** | The other score lever. |
| **EC-4** | Run their Rust harness for a leaderboard entry (task #7) | competitive Rust circuit | **—** | User machine action; out of Lean scope. |
| **EC-5** | Full doubling layout assembly (~1200 wires) | router (done) | **M** | Declared low-payoff mechanical residue. |
| **EC-6** | Measurement-discipline DSL extension decision (task #22) | — | **M** | Gates EC-3; a posture/architecture decision. |

## Hygiene / audits

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **HY-1** | kSectorData inhabitation + bridge audit (first non-trivial-fibre instance) | — | **S/M** | Older-code auditor's recommended next. |
| **HY-2** | Vacuity re-audit of the earliest Empirical files | — | **M** | Completes the older-code health pass. |
| **HY-3** | Doc-currency sweep: CLAUDE.md `SectorData` field drift (MulAction migration) + stale plan rows | — | **S** | Audit-flagged. |
| **HY-4** | Deprecation sweep (`EuclideanSpace.single_apply → PiLp.single_apply` etc.) | — | **S** | Keeps the build warning-clean. |

## Priority read (recommendation, 2026-07-04)

- **Thesis goal:** only the ★ rows move it. **FND-2** (D1c-entangled, M) is the most tractable genuine A5
  attack; **FND-1** (A5→D1, XL) is the prize but has no clean on-ramp. Everything else is breadth or
  consolidation, however valuable.
- **Manuscript breadth:** finish the thermodynamics track (**TH-1→TH-4**) and the CV track
  (**CV-1→CV-3**) — strong, well-supported, land clean "CSD covers ordinary QM / stat-mech / CV" claims.
- **ecdsa.fail artifact:** **EC-1** (safegcd termination, L) is the one piece that would make the inversion
  genuinely VERIFIED end-to-end.
- **Cheap wins, clear anytime:** **LF6-1** (S), **HY-3** + **HY-4** (S).
