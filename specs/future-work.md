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
| **LF6-5** | General-`d` CGLMP LHV bound `I_d ≤ 2` for all `d` (the counting argument) -- currently `decide`-proved only for `d ≤ 4`; would make LF6-D's non-factorisation d-INTRINSIC (not routed through the 2×2 `Φ⁺` CHSH sector) | CGLMP infra (done) | **M/L** | The general-N entangled tier's non-factorisation refinement. |
| **LF6-6** | Arbitrary (partial-Schmidt) entangled states general-`d` -- LF6-D covers only the maximally-entangled family | LF6-D | **M/L** | Extends the tier beyond maximal entanglement. |
| **LF6-7** | Symmetric-sector `Φ⁺↔ψ⁻` transport recompute (not yet done in LF6-D) | LF6-D | **S/M** | Small consolidation. |

**LF6 general-N entangled tier status:** the CORE is DONE (LF6-D: general `d×d` maximally-entangled
de-isolation + Born-from-volume + forced non-factorisation; CGLMP general-`d` violation; GHZ_n general-`n`
Mermin). LF6-5/6/7 + LF6-2 (Lindblad) are the named residuals.

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

## W-series (CSD dynamics spine — the prize: finite-dim Schrödinger dynamics as projected CSD flow)

**Spec received 2026-07-04. SPINE COMPLETE 2026-07-05 (W-2/W-3/W-5 all DONE).** The chain built:
`Σ-flow → projected ℂℙ^{N-1} flow → FS-isometry / transition-probability-preserving flow → unitary
dynamics`. W1 (Wigner) + W4 (CCR obstruction) done; W-2/W-3/W-5 assemble the bridge, all auditor-SOUND,
foundational-triple, no global axioms. **W-5-S2 finite-dim Stone: DONE** (C^1 form,
`Mathlib/Analysis/Matrix/StoneC1.lean`, commit 23b2a36 -- differentiable one-parameter unitary group =
`exp(t.A)`, generator recovered; the CompleteSpace instance-diamond blocker resolved via the C^*-algebra
norm; full-continuity Stone is the named sub-residual). **W-5-S1 phase lift: DONE 2026-07-07**
(`LF4/PhaseLift.lean` + `Mathlib/LinearAlgebra/Projectivization/PhaseRigidity.lean`): phase rigidity
(ker `U(N)→PU(N)` = the circle, via `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`)
extracts the `U(1)` cocycle of the projected-flow family (`projectedFlow_phase_cocycle`, the named
obstruction), the 2-cocycle law is proved (`phase_cocycle_identity`), and the coboundary datum `b`
(the honest cohomological input -- `H²(ℝ,U(1)) ≠ 0` algebraically, so some input is genuinely required)
yields the GENUINE vector-level one-parameter unitary group realising the same flow
(`projectedFlow_phase_lift`). Wired to S2 this closes the **W5 capstone**
`projectedFlow_schrodinger_form`: projected CSD flow = `exp(-itH)`-conjugation on rays, `H` Hermitian
recovered. Non-vacuity end-to-end on the trivial witness. Named follow-ons: Bargmann (continuity ⇒
coboundary datum, kills S1's input for continuous flows) and full-continuity Stone (S2's input).
**W-3 clopen datum: CLOSED 2026-07-07** (`LF4/BargmannSelection.lean` +
`Mathlib/LinearAlgebra/Projectivization/Bargmann.lean`): the Bargmann invariant (normalised triple
product on `ℙ³`, preserved by unitaries, CONJUGATED by `conjProj`) separates the Wigner branches at
the distinct values `Δ` vs `conj Δ` on a probe triple with `Im Δ = 1/4 ≠ 0` (exists ∀ `N ≥ 2`) --
(ii) (PU(N) disconnected in the FS-isometry group) is thereby PROVED (incl. exclusivity of the
Wigner disjunction, `not_projUnitary_and_projAntiunitary`), and (i) is REDUCED to the scalar datum
"the Bargmann observable `t ↦ Δ(Φ_t p,Φ_t q,Φ_t r)` is continuous", from which the clopen set is
DERIVED (`projUnitary_isClopen_of_bargmann_continuous`) and the selection fires
(`projectedFlow_unitary_of_bargmann_continuous`); `N ≤ 1` needs no datum. Named follow-ons:
continuity of the Bargmann function on `ℙ³` (local sections of `mk`; would derive the scalar datum
from raw flow continuity) and inhabiting the continuity datum on a non-trivial (`Φ≠id`)
`KahlerOnticSetup`. **ALL THREE W-RESIDUES ARE NOW CLOSED** (S1, S2, W-3 clopen); EC-6 unblocks.
Leave the P3 tensor derivation alone until there is a paper proof.

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **W-2** | `LF4/KahlerOnticSetup.lean`: the `structure KahlerOnticSetup N` interface (8 genuine fields + 2 honest Kähler-geometry placeholders, NO global axioms; `trivialKahlerOnticSetup` witness; projective target = Wigner's). | none (interface) | **M** | **DONE 2026-07-05** (`53ad012`). |
| **W-3** | `LF4/UnitarySelection.lean`: transProb-preservation (a HYPOTHESIS, not derived from Liouville) ⇒ unitary ∨ antiunitary via `wigner_rigidity_unitaryGroup`; continuous-from-id ⇒ unitary branch, STAGED on the clopen datum (connectedness on `PreconnectedSpace ℝ` proved). | W-2, Wigner | **M/L** | **DONE 2026-07-05** (`c119ffc`). Residue (clopen datum) CLOSED 2026-07-07 via the Bargmann discriminator (`LF4/BargmannSelection.lean`). |
| **W-5** | `LF4/ProjectedDynamics.lean`: `projectedFlow_eq_unitary_family` (projected flow = projective action of a one-parameter unitary family) + ray-level group law under explicit hypotheses + `expNegITH_unitary_group` (converse: `exp(-itH)` a genuine unitary group from Hermitian H). `U_t=exp(-itH)`-for-the-flow STAGED. | W-2, W-3 | **L** | **DONE 2026-07-05** (`ff97830`). Residues S2 (finite-dim Stone) DONE 2026-07-05 + S1 (phase lift) DONE 2026-07-07 (`LF4/PhaseLift.lean`, capstone `projectedFlow_schrodinger_form`). |

**Follow-on (auditor-recommended, S):** inhabit the W-3 continuity datum (now the Bargmann-observable
continuity, after the 2026-07-07 closure) on a non-trivial (`Φ≠id`, e.g. `kFlow`) `KahlerOnticSetup`,
not only the identity witness, so the unitary-branch selection is non-vacuous beyond the base case.

**Honest posture of the W-series (load-bearing):** this is the FORWARD direction -- GIVEN the Kähler sector
(as hypotheses/fields), it derives the unitary Schrödinger dynamics (via Wigner). It CONSUMES the sector
(A5-level structure); it does NOT derive the sector from the dynamics (that reverse is D1/FND-1, untouched).
So the W-series completes "QM dynamics from the posited sector", not the deep residue. Not ★.

## ecdsa.fail / ECDLP

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **EC-1** | Safegcd termination: `g→0` within `2n` (potential-function argument) | safegcd divstep (done) | **L** | The load-bearing residual keeping inversion trusted; self-contained integer combinatorics. |
| **EC-2** | Safegcd reversible circuit: `divstepGadget` with `denote = divstep`, cost over a proven circuit | divstep + Reversible DSL | **M/L** | Promotes the cost-side from documented to circuit-backed. |
| **EC-3** | Gidney measurement adder as a verified circuit (task #36) | measurement-discipline DSL ext (EC-6) | **M/L** | The other score lever. |
| **EC-4** | Run their Rust harness for a leaderboard entry (task #7) | competitive Rust circuit | **—** | User machine action; out of Lean scope. |
| **EC-5** | Full doubling layout assembly (~1200 wires) | router (done) | **M** | Declared low-payoff mechanical residue. |
| **EC-6** | Measurement-discipline DSL extension for Gidney (task #22) | W-residues first | **L** (multi-tranche) | **DECIDED 2026-07-05: opted IN, sequenced after the W-residues.** Gates EC-3. First tranche = an AND-based adder (the Cuccaro adder is carry-restoring, no AND to uncompute); then the Boolean→amplitude bridge (`denote↔toEuclideanLin`); then the net-channel theorem (measure+correct = identity-on-data ⊗ ancilla-reset) via the QuantumInfo CPTP/measurement machinery. Genuine verified theorem; larger trusted base. L5-a..d proved the amplitude MODEL of the primitive already. |

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
