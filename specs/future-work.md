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
| ~~FND-2~~ ★ | D1c-entangled: thread a genuine `Φ≠id` through a concrete *entangled* SectorData | LF6 tier | **M** | **DONE 2026-07-09** (`LF4/SingletKahlerFlow.lean`): the singlet preparation rebuilt over `kSectorDataFlow p₀ sh` (`Φ = kFlow ≠ id`) — `ofKählerPreparationFlow`, `ofKählerPreparationFlow_phi_ne_id`. Since LF1's `preEvent = Φ⁻¹'Ω`, the capstone `ofKählerPreparationFlow_flow_frequency_convergence` scores the flow-EVOLVED trials `(kFlow∘X)⁻¹'kRegion` → `P_st`, with `kFlow`'s `μψ`-preservation (`kFlow_measurePreserving_muPsi`) load-bearing. AxiomAudit-pinned. Mirrors D1c-1 on the entangled sector. **Does NOT reduce A5** (the entangled sector still posited; `kFlow` dynamically trivial) — the deep residue stays **FND-1**. |
| **FND-3** ★ | §13.2 ontic lift: thread `Φ` + prove `TransProbPreserving f_Φ` on `kSectorData` | Wigner (done) | **M** | Makes the A5→Wigner→U_isometry chain explicit on the non-trivial-fibre instance. Caveat C-1: sector-action-carries-isometry, so partly consolidation. |
| **C7** (Paper-C A3) — **DONE 2026-07-08** | **Genuine many-to-one `π` both-pillars object.** ✅ `LF4/ManyToOnePillars.lean`: `manyToOneSetup U p₀` is a `KahlerOnticSetup` on `Σ = ℂℙ^{N-1} × T²`, `π = Prod.fst` (many-to-one, fibres `= T²`, `manyToOneSetup_pi_not_injective`), flow rotates the base ray by `U t`; `manyToOneRotationSetup_both_pillars` fires BOTH pillars on the `N=2` witness (Schrödinger from `rotationSetup_schrodinger_form`, Born via `manyToOneSetup_born_frequency` on the fibred region `π⁻¹'(bornRegion)`). AxiomAudit-pinned, connectivity link **L8**. | C1–C5, `KSigma` | **M** | Removed the `π = id` degeneracy and matched Paper C's A3 fibred-projection shape. Did NOT touch the deep A5 origin / weights-from-flow (that stays **FND-1**); the fibre flow here is trivial (dynamics move only the base ray). |

## Kähler / symplectic differential geometry (blocked on Mathlib API)

These formalize Paper C's geometric substrate — currently carried as honest
interpretive prose (connectivity-manifest link L1) because Mathlib has no
Kähler / symplectic-form API on projective space. Each is unblocked only when
that API lands; the objects we use are already the correct ones (μ_FS is *the*
unique invariant measure, `fubiniStudyMeasure_unique`), so this is
formalization-DEPTH, not a correctness gap.

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **KG-1** | Construct the Fubini–Study Kähler 2-form `ω` on `ℂℙ^{N-1}`, prove it closed and compatible with the complex structure `J`; identify `μ_FS = ω^{∧(N-1)}/(N-1)!`. Discharges the `IsKahlerSector` / full `IsLiouvilleKahlerVolume` posits (L1). | **Mathlib Kähler-form API (does not exist)** | **XL / blocked** | Flagged 2026-07-08. The interpretive core of "Σ is a Kähler manifold with Kähler volume μ_FS." Today only the *normalized-volume* core is formalized (C5). |
| **KG-2** | Derive the Σ-flow from an explicit Hamiltonian vector field `X_H` (symplectic gradient of `H` w.r.t. `ω`), matching Paper C's A2, rather than positing a unitary/rotation flow. | KG-1, symplectic-gradient API | **L / blocked** | The flows we use are measure-preserving but not presented as `X_H = ω^{-1}dH`. |
| **KG-3** | Ashtekar–Schilling route to Schrödinger: projected quantum-effective Hamiltonian ⇒ holomorphic vector field on `ℂℙ^{N-1}` ⇒ `iψ̇ = Ĥψ`, matching Paper C §3.4 (we currently reach the same endpoint via Wigner-rigidity + phase-lift + Stone). | KG-1 | **L / blocked** | Alternative/complementary derivation; not required (endpoint already proved). |

## LF6 entangled tier (remaining)

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| ~~LF6-1~~ | Flow-capstone d-intrinsic reroute: route `maxEntangledDeisolation_flow_capstone` conjunct-7 through the general-d CGLMP force (not the Φ⁺ sector) | CGLMP general-d (done) | **S** | **DONE 2026-07-09** (`LF6/MaxEntangledCGLMPCapstone.lean`): `maxEntangledDeisolation_flow_capstone_cglmp` inherits conjuncts 1–6 and reroutes conjunct 7 to `no_lhv_realises_maxEntangled_cglmp_d` (no LHV table reproduces `pQM d`, since `cglmp d pQM > 2` in dimension `d`) — no 2×2 `Φ⁺`/CHSH reduction. New downstream file (CGLMPQudit imports the capstone, so an in-place edit would cycle). AxiomAudit-pinned. |
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
| ~~TH-1~~ | Canonical typicality: `E_{μFS}[ρ_S] = I/d_S` (avg) + Levy stretch | μ_FS + partial trace | **M** | **DONE (expectation core) 2026-07-07** (`Thermo/CanonicalTypicality.lean`): `E_{μFS}[ρ_S] = I/d_S`, thermal equilibrium from FS volume. Optional residue: the **Levy-concentration** stretch (needs spherical isoperimetry, not in Mathlib). |
| ~~TH-2~~ | Second law: coarse-grained vN entropy monotone under the de-isolation flow | TH-1 / LF6-B.3 | **M** | **DONE 2026-07-07** (`Thermo/SecondLaw.lean`): the H-theorem `vonNeumannEntropy_le_pinching` (`S(ρ) ≤ S(pinch ρ)`) + `entropy_reversible_then_coarsegrain` + `entropy_production_nonneg`, via Klein. |
| ~~TH-3~~ | Temperature / free energy: Gibbs max-entropy state, `T=∂S/∂E`, `F=E−TS`, variational principle | vN entropy (K1) | **M** | **DONE 2026-07-07** (`Thermo/FreeEnergy.lean`): `gibbs_free_energy_min` (`F(ρ_β) ≤ F(ρ)`) + `gibbs_free_energy_eq` (`F(ρ_β) = −T log Z`) + the Gibbs state (`gibbsState`, `cfc_log_gibbsState`), via Klein. |
| ~~TH-4~~ | Landauer erasure bound `≥ kT ln2` | TH-3, QEC tier | **M** | **DONE 2026-07-07** (`Thermo/Landauer.lean`): the Reeb–Wolf bound `landauer_bound` (`S(ρ_S)−S(ρ_S') ≤ β·ΔQ`) via entropy conservation + subadditivity + `bath_clausius`; one-bit corollary `landauer_one_bit` (`ΔQ ≥ T log 2`). |
| **TH-5** | ETH / fluctuation theorem (Jarzynski/Crooks) | TH-1..3 | **L** | Stretch. |

## CV / continuous-variable track

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| ~~W4~~ | ApproxCCR finite-dim CCR obstruction | — | — | DONE (committed). |
| ~~CV-1~~ | Finite position observable on a lattice | W4 | **S/M** | **DONE 2026-07-09** (`CV/Position.lean`): `positionOp = diag(x_j)` on the symmetric lattice — Hermitian, eigenvalues = lattice points (`positionOp_mulVec_single`), distinct (`latticePoint_injective`), bounded, centered. AxiomAudit-pinned. |
| ~~CV-2~~ / ~~CV-3~~ | Finite conjugate pair + approximate CCR on a low-energy sector | CV-1 / W4 | **M/L** | **DONE 2026-07-09** (`CV/Oscillator.lean`): took the truncated-oscillator route (cleaner + provable, and the sharp complement to W4) rather than lattice+DFT. `a`, `a†`, number op `a†a = diag(n)`; truncated CCR `[a,a†] = 1 − N·|N−1⟩⟨N−1|`; `Q,P` Hermitian; `[Q,P] = i·[a,a†]`; **`ccr_exact_on_bulk`**: `[Q,P]·eₙ = i·eₙ` exactly for every `n ≠ N−1` — the exact CCR on the low-energy sector, W4-forced defect confined to the top level. AxiomAudit-pinned. NB: the "‖·‖ ≤ ε" is realised as *exact on the bulk* (defect rank-one at the ceiling), stronger than a norm bound; the lattice+DFT semiclassical form is left as a harder alternative. |
| ~~CV-4~~ | Oscillator truncation recovers finite-energy predictions | CV-1..3 | **M** | **DONE 2026-07-09** (`CV/OscillatorSpectrum.lean`): `H = a†a + ½ = diag(n+½)`, Hermitian, with the Fock states as energy eigenstates (`hamiltonian_mulVec_single`: `H·eₙ = (n+½)·eₙ`). The energy `Eₙ = n+½` (`oscEnergy`) is manifestly **cutoff-independent** — no `N` — so the zero-point `½` (`hamiltonian_groundEnergy`), the uniform gap `1` (`oscEnergy_gap`), and every level below the ceiling are recovered exactly. AxiomAudit-pinned. **CV track (CV-1..CV-4) complete.** |

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
**Substrate-linkage fix (2026-07-07):** a provenance audit found the W-series theorems consumed only
`d.projectedFlow` — the `KahlerOnticSetup` substrate fields (`flow`, `pi`, the descent equation
`projectable`) were inert, so the "Schrödinger from the ontic sector" reading was carried-but-unused
scaffolding. Fixed by `sigmaFlow_schrodinger_form` (`LF4/PhaseLift.lean`), which consumes
`d.projectable`/`d.flow`/`d.pi` to land `d.pi (d.flow t x) = exp(-itH) • d.pi x` — the deterministic
Σ-flow, projected, IS Schrödinger evolution. Enforced by `scripts/check-sector-linkage.sh`. (The Born
pillar has the analogous gap — its general-`N` frequency capstones run on abstract `CPN` + `μ_FS`, not
an `OnticSetup` with a deterministic Σ-flow; wiring that through is the D1/FND-1 frontier, HY-5 below.)
Leave the P3 tensor derivation alone until there is a paper proof.

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **W-2** | `LF4/KahlerOnticSetup.lean`: the `structure KahlerOnticSetup N` interface (8 genuine fields + 2 honest Kähler-geometry placeholders, NO global axioms; `trivialKahlerOnticSetup` witness; projective target = Wigner's). | none (interface) | **M** | **DONE 2026-07-05** (`53ad012`). |
| **W-3** | `LF4/UnitarySelection.lean`: transProb-preservation (a HYPOTHESIS, not derived from Liouville) ⇒ unitary ∨ antiunitary via `wigner_rigidity_unitaryGroup`; continuous-from-id ⇒ unitary branch, STAGED on the clopen datum (connectedness on `PreconnectedSpace ℝ` proved). | W-2, Wigner | **M/L** | **DONE 2026-07-05** (`c119ffc`). Residue (clopen datum) CLOSED 2026-07-07 via the Bargmann discriminator (`LF4/BargmannSelection.lean`). |
| **W-5** | `LF4/ProjectedDynamics.lean`: `projectedFlow_eq_unitary_family` (projected flow = projective action of a one-parameter unitary family) + ray-level group law under explicit hypotheses + `expNegITH_unitary_group` (converse: `exp(-itH)` a genuine unitary group from Hermitian H). `U_t=exp(-itH)`-for-the-flow STAGED. | W-2, W-3 | **L** | **DONE 2026-07-05** (`ff97830`). Residues S2 (finite-dim Stone) DONE 2026-07-05 + S1 (phase lift) DONE 2026-07-07 (`LF4/PhaseLift.lean`, capstone `projectedFlow_schrodinger_form`). |

**Follow-on (auditor-recommended, S):** inhabit the W-3 continuity datum (now the Bargmann-observable
continuity, after the 2026-07-07 closure) on a non-trivial (`Φ≠id`) `KahlerOnticSetup`, not only the
identity witness, so the unitary-branch selection is non-vacuous beyond the base case. **A genuine
`Φ≠id` inhabitant now EXISTS** (`rotationSetup`, `LF4/NonTrivialSetup.lean`, connectivity fix C1
2026-07-07); firing the W3/W5/S1/S2 chain on it is fix **C2** (the next connectivity step). NB: `kFlow`
is NOT usable here — it acts trivially on rays (`projectedFlow=id`); the C1 witness uses a projective
unitary flow. See [`specs/connectivity-manifest.md`](connectivity-manifest.md).

**Honest posture of the W-series (load-bearing):** this is the FORWARD direction -- GIVEN the Kähler sector
(as hypotheses/fields), it derives the unitary Schrödinger dynamics (via Wigner). It CONSUMES the sector
(A5-level structure); it does NOT derive the sector from the dynamics (that reverse is D1/FND-1, untouched).
So the W-series completes "QM dynamics from the posited sector", not the deep residue. Not ★.

## ecdsa.fail / ECDLP

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| EC-1 — **PARTIAL 2026-07-09** | Safegcd termination: `g→0` within the Bernstein–Yang bound (potential-function argument) | safegcd divstep (done) | **L** | **Done: the termination-STABILITY half** (`SafegcdDivstep.lean`): `divstep_snd_snd_zero` (g=0 absorbing), `divstepIter_natAbs_of_g_zero_stable` (the surviving `|f|=gcd` is stable for every step count ≥ termination — so a fixed-count loop reads the right answer). **Numbers revised (EC-1)**: corrected the divstep count from the optimistic `2n` to the honest Bernstein–Yang worst-case `3n ≥ ⌊(49n+80)/17⌋≈2.88n` across `SafegcdInversion`/`KaratsubaMul`/`TwoTrack`/`TrustedEstimate` (score win ~86×→~69×; trusted estimate now ~1.43× the leaders' Toffoli band, not ~1.07×). **Residual**: the termination-COUNT bound itself (that `g` reaches 0 within the bound) — Bernstein–Yang's proof is computer-assisted (transition-matrix search), not formalised. |
| EC-2 — **cost side DONE + value-side reversibility DONE 2026-07-09** (bit-circuit deferred) | Safegcd reversible circuit: `divstepGadget` with `denote = divstep`, cost over a proven circuit | divstep + Reversible DSL | **M/L** | **Cost side done** (`SafegcdInversion.lean`): `divstepProxyGadget` EXHIBITS the divstep gadget as one concrete `Circuit` (`modSub ++ cuccaroCModAdd ++ cuccaroModDouble`), and `divstepProxyGadget_toffoli` proves its Toffoli cost IS `divstepToffoli n` — cost of a real in-DSL circuit, not a count over a hypothetical one. **Value-side reversibility done** (`SafegcdDivstep.lean`): `divstep_not_injective` proves raw divstep is NOT injective (`divstep 0 1 2 = divstep 0 1 1 = (1,1,0)`), so garbage is genuinely necessary; `divstepRev` adjoins the MINIMAL 2-bit branch selector (`decide (0<d)`, `decide (Odd g)`), and `divstepRev_injective` proves the extended transition injective on the `f`-odd invariant domain — the exact mathematical basis for a value-faithful reversible divstep (denote=divstep, 2 garbage bits/step), and it certifies 2 bits is minimal-in-kind. All AxiomAudit-pinned. **Residual (bit-level build):** turning `divstepRev` into a concrete signed-register `Circuit` over the Reversible DSL whose `denote` equals it — a mechanical multi-session assembly, now with the reversibility invariant nailed down. |
| EC-7 (beat lever) — **DONE 2026-07-09; faster-M(n) analysis DONE 2026-07-10** | Sub-quadratic (half-GCD) inversion: does it BEAT safegcd at 256? | Karatsuba mult | **S** | **`HalfGcdInversion.lean`**: modelled the recursive/half-GCD inversion `halfGcdInvToffoli k n = (log₂n)·k·karatsubaToffoli n = O(n^{1.585} log n)` (sub-quadratic exponent). **Quantified honestly**: at 256 it beats safegcd **iff `k ≤ 1`** (`halfGcd_beats_iff_k_one_256`) — an aggressively-tuned recursion (≤8 total full multiplies) BEATS by ~12% (`halfGcd_aggressive_beats_safegcd_256`), a standard `k≥2` LOSES (`halfGcd_standard_loses_safegcd_256`). **Faster-M(n) lever (2026-07-10):** added a verified **Toom-3** multiply model (`KaratsubaMul.lean` `toom3Toffoli`, `Θ(n^{log₃5})=Θ(n^1.465)`, base = verified schoolbook, combine = verified modular adders; `toom3Toffoli 256 = 596 490 < 653 388 = karatsuba`, `toom3Toffoli_lt_karatsuba_secp256k1`), and a **multiply-parameterised** half-GCD `halfGcdInvToffoliWith`. Finding, quantified: Toom-3 IMPROVES the k=1 margin (12%→~24%, `halfGcd_toom3_improves_margin_256`) but does NOT flip the threshold at 256 (still beats iff k≤1, `halfGcd_toom3_beats_iff_k_one_256`); flipping to a standard k=2 recursion needs `M(256) ≤ 369 311` (`halfGcd_k2_beats_iff_mult_budget_256`), below BOTH Karatsuba and Toom-3 (`karatsuba_toom3_miss_k2_budget_256`) — an FFT-class multiply whose crossover is far above 256. **So the knife-edge at the ECDLP width is STRUCTURAL** (8 log-levels vs safegcd's tight ~90n² constant), not a Karatsuba artefact: a genuine beat needs a tuned k≤1 half-GCD; a faster multiply alone won't do it at 256. AxiomAudit-pinned. |
| EC-3 — **DONE 2026-07-09** (channel residual shared w/ EC-6) | Gidney measurement adder as a verified circuit (task #36) | measurement-discipline DSL ext (EC-6) | **M/L** | The verified Gidney adder (`GidneyAdder.lean`, `gidneyAdd_correct`, 2n) + its measurement re-cost to `n` (`MeasurementGidneyAdder.lean`, `gidneyMeasAddToffoli_eq`, `gidney_beats_cuccaro`: n < 2n Cuccaro < 6n AND) were already built + pinned. Added the **capstone** (`MeasurementAdderHierarchy.lean`): the full ordering `measurement_adder_hierarchy` (meas-Gidney n < unitary-Gidney 2n < meas-AND 3n < unitary-AND 6n, each a proven circuit cost) and `gidneyMeas_cheapest` — the measurement Gidney adder is the corpus's least-Toffoli reversible adder, unifying EC-3 with EC-6/L5-d. AxiomAudit-pinned. **Residual (shared w/ EC-6):** the channel-level composition over all n cells. |
| **EC-4** | Run their Rust harness for a leaderboard entry (task #7) | competitive Rust circuit | **—** | User machine action; out of Lean scope. |
| **EC-5** | Full doubling layout assembly (~1200 wires) | router (done) | **M** | Declared low-payoff mechanical residue. |
| EC-6 — **L5-a..d DONE 2026-07-09** (channel-level residual remains) | Measurement-discipline DSL extension for Gidney (task #22) | TH + CV tracks (done) | **L** (multi-tranche) | **Tranches proved:** AND-based adder (`Reversible/AndAdd.lean`, 6n; `andAdd_correct`/`_ancilla_clean`/`_toffoli`); Gidney adder (`GidneyAdder.lean`, 2n); the Boolean→amplitude bridge `andUncompMat_lifts_denote` + the per-AND net-channel equivalence `andUncompute_measureUncompute_same_data` + 0-vs-1 Toffoli `andUncompute_measurement_saving` (`Empirical/QM/MeasurementUncompute*.lean`); **L5-d** the circuit-level saving threaded through the whole adder (`andAdd_measurement_toffoli`: 3n; `andAdd_measurement_halves`: 2×3n = 6n = unitary adder). All AxiomAudit-pinned. **Residual:** the CHANNEL-level proof that the `n` measurement gadgets composed reproduce the unitary uncompute's data effect on the WHOLE register (tensor composition over all cells with mid-circuit measurement) — the per-cell equivalence is proved; the n-fold channel composition is the standing gap. Gates EC-3. |

## Hygiene / audits

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **HY-1** | kSectorData inhabitation + bridge audit (first non-trivial-fibre instance) | — | **S/M** | Older-code auditor's recommended next. |
| **HY-2** | Vacuity re-audit of the earliest Empirical files | — | **M** | Completes the older-code health pass. |
| **HY-3** | Doc-currency sweep: CLAUDE.md `SectorData` field drift (MulAction migration) + stale plan rows | — | **S** | Audit-flagged. |
| **HY-4** | Deprecation sweep (`EuclideanSpace.single_apply → PiLp.single_apply` etc.) | — | **S** | Keeps the build warning-clean. |
| ~~HY-5~~ ★ | Born-pillar Σ-linkage: route the general-`N` Born-frequency capstones through a Σ with a DETERMINISTIC flow, not the abstract i.i.d. SLLN engine on bare `CPN`+`μ_FS`. The provenance-audit analogue of the W-series `sigmaFlow` fix, on the Born side. | `unitaryFlowSetup` flow | **L** | **DONE 2026-07-09** (`LF4/BornFlowLinkage.lean`): `unitaryFlowSetup_born_frequency_evolved` + `povm_born_frequency_volume_evolved` — the general-`N` Born / POVM capstones now score trials EVOLVED by the sector's own flow `Φ_t = (unitaryFlowSetup …).flow t`, with `flow_preserves_volume` (= `U(N)`-invariance of `μ_FS`) load-bearing (pins the evolved law). The substrate `flow`/`flow_preserves_volume` fields are now consumed on the Born side. AxiomAudit-pinned. Does NOT derive weights-from-flow (that stays **FND-1**); trials are still an i.i.d. posit before evolution. |

## Pillar completeness (named deferrals)

The pillar map of ordinary QM, for manuscript honesty (see the README pillar ledger). Two textbook
pillars are deliberately NOT in the work programme; they are recorded here so their absence is a
decision, not an oversight.

| Ref | Item | Depends on | Cx | Notes |
|---|---|---|---|---|
| **P3** | Tensor-product / composite-system derivation (why `⊗`) | a paper proof first | **XL** | PARKED by standing instruction; composite structure is currently POSITED per instance (the LF6 entangled setups are built by hand at fixed `N`). |
| **IP-1** | Identical particles / spin-statistics (symmetrisation postulate, boson/fermion sectors) | P3 | **XL** | NOT in the corpus or plans (recorded 2026-07-07 for pillar-map completeness). Out of current scope; any "CSD covers ordinary QM" claim should name this deferral. |

## Priority read (user-set sequencing, 2026-07-07; supersedes the 2026-07-04 recommendation)

- **THERMO TRACK COMPLETE (TH-1..TH-4, all DONE 2026-07-07):** canonical typicality (expectation),
  the second law / H-theorem, the Gibbs free-energy variational principle, and Landauer's `kT ln 2`
  bound. Remaining thermo residues are optional: the **TH-1 Levy-concentration** upgrade (needs
  spherical isoperimetry, not in Mathlib) and the **TH-5 stretch** (ETH / Jarzynski–Crooks
  fluctuation theorem). **NEXT PER SEQUENCING: the CV track (CV-1 onwards)** — the continuous-variables
  pillar.
- **THEN — the CV track, CV-1 onwards:** finite position observable → finite momentum (finite
  Fourier) → approximate CCR `‖[Q_N,P_N]−iℏ·1‖ ≤ ε` → oscillator truncation. The
  continuous-variables pillar.
- **DEPRIORITISED — EC-6 / the ecdsa.fail Tier-X fork:** still opted in, but sequenced BEHIND the TH
  and CV tracks (previously "after the W-residues"; the W-residues are now all closed, 2026-07-07).
  Same for the other EC rows.
- **Thesis goal (unchanged):** only the ★ rows move it. **FND-2** (D1c-entangled, M) is the most
  tractable genuine A5 attack; **FND-1** (A5→D1, XL) is the prize but has no clean on-ramp.
- **Cheap wins, clear anytime:** **LF6-1** (S), **HY-3** + **HY-4** (S).
