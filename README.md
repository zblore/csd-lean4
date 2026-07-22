# csd-lean4

[![CI](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml)

**Scope, stated honestly (read [`specs/connectivity-manifest.md`](specs/connectivity-manifest.md) first).** This Lean 4 formalisation of Constraint-Surface Dynamics machine-verifies the major structural theorems of finite-dimensional quantum mechanics and — as of the 2026-07 connectivity work (fixes C1–C7) and the SigmaLayer (the projective-sector ontology, Paper C) (`CsdLean4/SigmaLayer/`) — **connects them end-to-end on genuine objects.** A single posited Kähler sector yields BOTH pillars together at **general `N`** with **arbitrary Hermitian `H`**: `manyToOneSchrodingerSetup_both_pillars` proves (A) its projected flow is Schrödinger evolution `exp(-itH)` on rays, AND (B) sampling its own Liouville/typicality measure gives the Born frequencies `‖⟨eᵢ,ψ⟩‖²`, on `Σ = ℂℙ^{N-1} × T²` with a genuine **many-to-one** `π = Prod.fst` (Paper-C A3 shape). The Σ-layer then puts isolated Hamiltonian dynamics **AND** de-isolating measurement **AND** time-indexed records **AND** Born **AND** the conditional/Lüders state update on **ONE** ontic model `(Σ, μL, Φ, π)` — the unified capstone `unified_projectiveSector_capstone`. Connectivity-manifest links **L2–L9 are CONNECTED**.

**The one deep gap: the sector itself is posited (A5 / SL-1).** Everything above is FORWARD — it consumes the posited Kähler sector. The Born trials *sample* the sector's measure i.i.d.; they are **not** *evolved by the deterministic flow*, and the Born weights are **not** *derived from the dynamics*. Closing this — deriving the sector and its typicality from `Φ` itself — is the A5→D1 sector-origin problem (manifest link **L7**), research-grade and open. Until then the result reads "given the posited Kähler sector, both pillars and the full measurement/record chain follow," **not** "both follow from deterministic dynamics." (Paper C §1.4 likewise assumes `Σ`, `π` and the A5 sector rather than deriving them, so this posited-sector scope matches the paper's own.)
- **Kähler geometry (L1).** The differential-geometric content (a closed 2-form compatible with a complex structure) is **unformalizable in current Mathlib** — no Kähler API — so the `IsKahlerSector` field is an honestly-labelled interpretive posit consumed by no theorem. Its formalizable core (the Liouville measure is a *normalized* volume) is now genuine, consumed content (fix C5). "Kähler" elsewhere names the *mathematical reading*, not a formalized manifold.

Nothing below may be read as a stronger connection than a **CONNECTED** row in the [manifest](specs/connectivity-manifest.md), enforced by `scripts/check-connectivity.sh`. For a full, current review of what is machine-verified, see [`specs/reconstruction-status.md`](specs/reconstruction-status.md).

**What is proved** (each a real theorem):

- **the Born rule as a Fubini–Study typicality volume** — for every dimension, every unit preparation, and *general* (POVM) measurements, empirical frequencies of i.i.d. FS draws converge a.s. to FS volumes = the Born weights, Gleason-free (LF1–LF4); and, for `rotationSetup`, those draws are from the sector object's own `liouvilleMeasure` (fix C4).
- **Schrödinger dynamics from the sector** — for the genuine `Φ ≠ id` sector, the projected deterministic flow is `exp(-itH)`-conjugation on rays, at **general `N` with arbitrary Hermitian `H`** (`manyToOneSchrodingerSetup`, fixes C1/C2/C7). The general form `sigmaFlow_schrodinger_form` takes any `KahlerOnticSetup` with FS-isometry / coboundary / C¹ regularity as explicit hypotheses.
- **measurement as a process, unified with the dynamics** — a `Φ ≠ id` von Neumann de-isolation flow realises the Naimark dilation dynamically, with per-microstate outcomes (LF5); and the Σ-layer puts that measurement AND the isolated Hamiltonian dynamics AND time-indexed records AND the Born frequencies AND the conditional/Lüders state update on ONE ontic model (`unified_projectiveSector_capstone`);
- **the finite-QM reconstruction targets** — the SigmaLayer projective-sector ledger (P1–P9 / B1–B7 / **T1–T16**): Born, unitary/Schrödinger dynamics, unique measurement outcome, general conditional + Lüders update, mixed states, POVMs, contextuality, Bell/CGLMP/Tsirelson (universal bounds), no-signalling, interference — each a `Prop` target inhabited by a proved theorem (`CsdLean4/SigmaLayer/`, `AXIOMS.md §3.7`);
- **entanglement, non-locality, no-signalling** — Bell-forced non-factorisation in the `Σ`-engine at full generality: CGLMP for *every* `d`, GHZ/Mermin for *every* `n` (LF6);
- **uncertainty** (Robertson, LF4 §14.2) and the **thermodynamics track TH1–TH4** (canonical typicality, the second law, the Gibbs free-energy principle, Landauer's `kT ln 2`).

**The connectivity ledger** (see the [manifest](specs/connectivity-manifest.md) for the per-link evidence L1–L9):

| Intended link | Status |
|---|---|
| Kähler geometry ⇒ the sector's fields (L1) | **PARTIAL** — volume-normalization core consumed (C5); the differential geometry is unformalizable (no Mathlib API), honestly demoted |
| Σ + `Φ` + `π` ⇒ projected flow (L2) | **CONNECTED** — the descent field `projectable` is consumed (`sigmaFlow_schrodinger_form`) |
| projected flow ⇒ Schrödinger form (L3) | **CONNECTED** — general `N`, arbitrary `H` (`manyToOneSchrodingerSetup_schrodinger_form`, C1/C2/C7) |
| a genuine `Φ ≠ id` sector instance exists (L4) | **CONNECTED** — `rotationSetup` / `manyToOneSetup`, `projectedFlow ≠ id` (C1/C7) |
| sector ⇒ Born frequencies (L5) | **CONNECTED (structural)** — Born law stated with sampling measure = the sector's `liouvilleMeasure`; trials still sampled, not flow-evolved |
| ONE object underlies both pillars (L6/L8) | **CONNECTED** — `manyToOneSchrodingerSetup_both_pillars`, both pillars on one object with a genuine many-to-one `π`, general `N` (C4/C7) |
| ONE model carries dynamics + measurement + records + Born + update (L9) | **CONNECTED** — `unified_projectiveSector_capstone` (SL-T5) |
| Born weights derived FROM the flow (L7) | **OPEN ★** — the thesis frontier (A5→D1, SL-1); the sector itself is posited |

**Current work programme:** the forward reconstruction (L2–L9) and the SigmaLayer T1–T16 ledger are landed; remaining work is documentation/CI hygiene, breadth, and the deep frontier (A5/SL-1, the general Lindblad tier, the Kähler 2-form). Details: [`specs/future-work.md`](specs/future-work.md) and the [connectivity manifest](specs/connectivity-manifest.md).

---

Lean 4 formalisation of Constraint-Surface Dynamics. **LF1**, **LF2**, **LF3**, and **LF4 §14.2** (the observable-correspondence layer — Hilbert spectral expansion, ontic-side multi-region carving, ontic ↔ Hilbert variance correspondence, and Robertson uncertainty at the ontic-integration level, including two concrete witnesses) are merged and machine-verified, along with a **general-`N` Born-from-Kähler-volume cluster** (the moment-map / Duistermaat–Heckman programme) and its **extension to general POVMs via Naimark dilation**. An **Empirical** module provides the QM-validity regression suite (Bell family + Tsirelson, no-cloning / -deleting / -broadcasting / -communication, E91 device-independent security, Robertson uncertainty, Stern-Gerlach, unambiguous state discrimination, superdense coding, teleportation, quantum money, contextuality, Hardy, GHZ, gates) plus a carving-free, Gleason-free **CSD volume-frequency series** (Stern-Gerlach, Malus, Bell, GHZ, Hardy projective; trine, USD, SIC non-projective POVMs — each Born value *derived* as a Fubini–Study volume). **[`EMPIRICAL.md`](EMPIRICAL.md) is the per-test index** for both branches.

**The Born-rule theorems — the Born rule as a Fubini–Study typicality volume, for *general quantum measurements*.** (Connectivity caveat: the raw general-`N` Born capstones are theorems about the FS measure on `ℂℙ^{N-1}` reached via an i.i.d. strong law; a sector-object version now exists — `manyToOneSetup_born_frequency` samples the sector field `liouvilleMeasure`, and `manyToOneSchrodingerSetup_both_pillars` puts Born and Schrödinger on ONE object (manifest L5/L6/L8) — but the trials still SAMPLE the measure rather than being evolved by the flow (A5, L7). Formalisation boundary, stated once: "Kähler" names the *mathematical reading* of the formal objects — in Lean the ontic spaces are types, the measures are `fubiniStudyMeasure` (the Haar-on-`U(N)` pushforward) and product/Haar measures, and no manifold, symplectic form, or Kähler metric is constructed; Mathlib has no Kähler API. The volume, pushforward, and frequency theorems below are machine-verified about *those measures*; their identification with Kähler/Liouville volume forms is standard differential geometry carried as prose. See `AXIOMS.md §3.1` and the module docstrings of `LF4/KahlerInstance.lean` / `LF4/MomentMap.lean`.) The Born weight `‖⟨eᵢ, ψ⟩‖²` is derived from the Fubini–Study Kähler geometry of the ontic `Σ = ℂℙ^{N-1}` — as the **torus moment-map coordinate** (`momentMap_mk_eq_inner_sq`), as a **barycentric Lebesgue-volume ratio** (`born_eq_volume_ratio`), and, **for every `N`, unconditionally**, as a **genuine `fubiniStudyMeasure` volume ratio** (`fs_born_volume_ratio_N`) carrying a **Gleason-free empirical chain** `born_frequency_convergence_N`: deterministic repeated-trial typicality (LF1) + Born = Fubini–Study volume ⟹ frequencies converge a.s. to the Born weight, the Born value *derived from the Kähler volume* rather than imported via Gleason/Busch. **This now covers non-projective measurements:** every **POVM** `{Eᵢ}` acquires a canonical Naimark dilation `canonicalNaimark P` (built from the CFC square roots `√Eᵢ`), and `povm_born_frequency_volume` lands the POVM Born weight `⟨ψ, Eᵢ ψ⟩` as a sum of Fubini–Study volumes on the dilated `Σ' = ℂℙ^{N·|ι|−1}` — empirical frequencies converging to it, **carving-free, Gleason-free, and unconditional**. So the Born rule for *arbitrary* quantum measurements is a **theorem about the Fubini–Study measure**, not of operational effect-additivity (Busch). Honest residue (the connectivity gap, manifest L5): this is a theorem about `μ_FS` on `ℂℙ^{N-1}` reached via an i.i.d. strong law — it is **NOT** derived from a deterministic `Σ`-flow, and the general-`N` capstones consume no `OnticSetup`/`KahlerOnticSetup` at all. Deriving the Born weights *from* the deterministic flow is the open sector-origin problem (A5→D1, SL-1). **Measurement dynamics is now exercised at the single-system projective tier** (LF5, complete 2026-06-11; layer headline `measurement_flow_born_frequency`): a deterministic, Fubini–Study measure-preserving von Neumann de-isolation flow `Φ_vN ≠ id` realises the Naimark dilation dynamically, and its context-fixed pointer-block volumes and a.s. empirical frequencies are the Born weights, for every unit preparation. The **per-microstate outcome map** is now realised too (LF5-F, 2026-06-14): `bornRegion_pairwiseDisjoint` makes the moment-subdivision a genuine partition, `vnPointerOutcome` is the resulting deterministic outcome function, and `measurement_flow_outcome_frequency` upgrades the capstone to a single union event per pointer. The **entangled / non-local de-isolation tier** opened at LF6-A/B (2026-06-28: the singlet's non-factorisation Bell-forced in the `Σ`-engine, realised by a genuine `ℂℙ¹⁵` de-isolation flow, with a decoherence / purity-drop witness) and its **general-`N` core is now CLOSED** (2026-07-04, LF6-C/D/E: general `d×d` maximally-entangled de-isolation with Born-from-volume and forced non-factorisation, the CGLMP violation for *every* dimension `d`, and GHZ/Mermin for *every* party number `n`; no-signalling proven; LF6-5 (general-d CGLMP bound + tightness) now DONE; named residuals LF6-6/7 + Lindblad). What remains of the dynamics debt: the dynamical origin of the sector itself (A5 — first onramp results 2026-06-29 single out `μFS` by symmetry and rule out the single-flow ergodic route, but do not yet derive the sector from the dynamics); and the Born-from-volume `SectorData` instances, which still carry `Φ = id` (the D1c variants `kSectorDataFlow` / `cpSectorDataFlow` thread a genuine `Φ ≠ id` into concrete instances but do not yet discharge A5).

**The Schrödinger-dynamics theorems — Schrödinger evolution as the projected sector flow (the W-series, complete 2026-07-07, but see the instantiation caveat).** Given the W2 sector interface (`LF4/KahlerOnticSetup.lean`: compact `Σ`, Liouville measure, deterministic measure-preserving flow, projection with descent to `ℂℙ^{N-1}` — sector-level hypotheses as structure fields, no global axioms), the chain forces the projected dynamics to be finite-dimensional Schrödinger evolution. Transition-probability preservation (the FS-isometry posit, an explicit hypothesis — **not** derived from Liouville preservation; measure ≠ metric) puts each time-`t` map on the Wigner unitary-or-antiunitary dichotomy (`wigner_rigidity_unitaryGroup`, W1, proved in-tree). The **Bargmann invariant** separates the two branches — it is preserved by unitaries and conjugated by antiunitaries, and a probe triple with `Im Δ = 1/4 ≠ 0` exists for every `N ≥ 2` — so the Wigner disjunction is **exclusive**, and continuity of that one scalar observable of the flow makes the unitary-time set clopen; connectedness of `ℝ` then selects the unitary branch at every time (`projectedFlow_unitary_of_bargmann_continuous`, the W3 clopen datum CLOSED). Choice assembles the unitary family and the flow group law descends to a ray-level projective representation (W5); **phase rigidity** (the kernel of `U(N) → PU(N)` is the circle) extracts its genuine `U(1)` 2-cocycle, which a coboundary datum kills — an honest cohomological input, since `H²(ℝ, U(1)) ≠ 0` algebraically — yielding a true vector-level one-parameter unitary group (`projectedFlow_phase_lift`, S1). The **C¹ finite-dimensional Stone theorem** (`StoneC1.lean` — Mathlib has no Stone theorem) recovers the generator, landing the capstone **`projectedFlow_schrodinger_form`**: `d.projectedFlow t p = exp(-itH) • p` with `H` Hermitian — `iψ̇ = Hψ` read on rays. Every physical input is a named explicit hypothesis (FS-isometry, flow group law, Bargmann-observable continuity, coboundary, C¹), each non-vacuously inhabited; named follow-ons: Bargmann's theorem (continuity ⇒ coboundary), full-continuity Stone, `Δ`-continuity on `ℙ³`, a `Φ ≠ id` inhabitant. **Honest posture: this is the forward direction — it consumes the posited sector and outputs quantum dynamics as a *conditional* theorem; it does not derive the sector (that reverse is A5→D1/SL-1).** As of fixes C1/C2/C7 it is instantiated **non-trivially**: the FS-isometry / coboundary / C¹ hypotheses are discharged for **arbitrary Hermitian `H`** on `manyToOneSchrodingerSetup` (a genuine `Φ ≠ id` `KahlerOnticSetup` on `Σ = ℂℙ^{N-1} × T²` with a many-to-one `π = Prod.fst`), so the fully-instantiated Schrödinger statement is now `exp(-itH)` for any `H`, not the trivial `exp(0) = 1`. And the Born-rule and Schrödinger theorems now **share that one sector object** — `manyToOneSchrodingerSetup_both_pillars` proves both pillars on it (manifest L6/L8), and `unified_projectiveSector_capstone` adds the measurement/record chain on the same model (L9). The remaining gap is A5 (deriving the sector from `Φ`), not the instantiation. (The `trivialKahlerOnticSetup` witness is retained only as the datum-free base case.)

The repo is sorry-free and `lake build CsdLeanTests` green. **What CSD commits you to is a physical posture, not an axiom count.** The theory's postulates are: an ontic substrate `(Σ, μL)` carrying a deterministic, measure-preserving flow; a posited projection onto the quantum-effective sector together with its symmetry; and the reading of probability as a typicality volume. From these the **Born rule is derived as a theorem** — Gleason-free, general dimension, including general POVMs — rather than assumed. These postulates are carried as hypotheses on the types (CSD's claims are conditional on the substrate existing), so they do not appear in `#print axioms`; the deepest open one is the *dynamical origin of the sector* (the LF5 measurement flow `Φ_vN ≠ id` is now exercised at the single-system projective tier, but the concrete `SectorData` instances still carry `Φ = id`, and the sector itself remains posited). Separately, the **formalisation** rests on the foundational Lean triple (`propext`, `Classical.choice`, `Quot.sound`) and — as of 2026-07-21 — **zero imported axioms**. The last one, `busch_effect_gleason` (the Busch effect-Gleason theorem), was **proved and de-axiomatised** (now `OperationalPackage.effect_gleason_representation` in `LF2/EffectGleason.lean`); the earlier import, invariant-measure uniqueness, was **removed 2026-06-04**. Every corpus theorem now reports only the foundational triple under `#print axioms`. See [`AXIOMS.md`](AXIOMS.md) §0 for this three-category distinction and the per-theorem ledger, and [`specs/povm-plan.md`](specs/povm-plan.md) / [`specs/LF4-todo.md`](specs/LF4-todo.md) for the POVM tranche and LF4 backlog.

## What's machine-verified

| Layer | Headline | Carving | Axioms beyond foundational triple |
|---|---|---|---|
| **W-series dynamics spine (COMPLETE 2026-07-07) — the Schrödinger pillar** | Capstone **`projectedFlow_schrodinger_form`** (`LF4/PhaseLift.lean`): GIVEN the W2 `KahlerOnticSetup` sector interface plus named regularity data, the projected flow IS `exp(-itH)`-conjugation on rays with Hermitian `H` recovered. Links: **W1** Wigner / FS rigidity (`wigner_rigidity_unitaryGroup`, both branches genuine); **W3** unitary selection — the staged clopen datum **CLOSED** via the Bargmann discriminator (`Bargmann.lean` + `LF4/BargmannSelection.lean`: the invariant is preserved by unitaries, conjugated by antiunitaries; probe with `Im Δ = 1/4` ∀ `N ≥ 2`; branch separation PROVED incl. exclusivity `not_projUnitary_and_projAntiunitary`; continuity reduced to ONE scalar observable; `N ≤ 1` datum-free); **W5** the projective one-parameter representation; **S1** the phase lift (`PhaseRigidity.lean`: ker `U(N)→PU(N)` = the circle; the `U(1)` cocycle extracted, 2-cocycle law proved, killed on the coboundary datum — genuinely required, `H²(ℝ,U(1)) ≠ 0`); **S2** the C¹ finite-dim Stone theorem (`StoneC1.lean`; Mathlib has none) | **No carving** — the unitary structure enters through the FS-isometry HYPOTHESIS (measure ≠ metric discipline), never from the Liouville field; every physical input an explicit named hypothesis, each discharged on the genuine `Φ ≠ id` `manyToOneSchrodingerSetup` for arbitrary Hermitian `H` (C1/C2/C7) | none |
| **Thermodynamics TH1 (2026-07-05)** | `canonical_typicality_expectation` (`Thermo/CanonicalTypicality.lean`): `E_{μFS}[Tr_E ρ] = I_S/d_S` — thermal equilibrium from Fubini–Study typicality volume, via the genuine twirl integral `fs_first_moment` (`∫ \|ψ⟩⟨ψ\| dμ_FS = I/N`) | Honest scope: EXPECTATION (average) only — Levy concentration is the named residual; not dynamical thermalisation | none |
| **Thermodynamics TH2 — the second law (2026-07-07)** | `vonNeumannEntropy_le_pinching` (`Thermo/SecondLaw.lean`): the H-theorem `S(ρ) ≤ S(pinch ρ)` — pinching (dephasing to the pointer-basis diagonal) never decreases von Neumann entropy, via Klein's inequality; `entropy_reversible_then_coarsegrain` — the fine-grained unitary step conserves entropy, the coarse-graining produces it (`S(ρ) = S(UρUᴴ) ≤ S(pinch(UρUᴴ))`); `entropy_production_nonneg` (pure-state instance = LF6-B.3) | Honest scope: the Klein support hypothesis; the H-theorem for the SPECIFIC pointer-basis coarse-graining, not a universal second law; not dynamical thermalisation | none |
| **Thermodynamics TH3 — free energy / Gibbs variational principle (2026-07-07)** | `gibbs_free_energy_min` (`Thermo/FreeEnergy.lean`): the Gibbs state `ρ_β = exp(-βH)/Z` minimises the free energy `F(ρ) = Re Tr(ρH) − T·S(ρ)`, `F(ρ_β) ≤ F(ρ)`, via Klein `β(F(ρ)−F(ρ_β)) = D(ρ‖ρ_β) ≥ 0`; `gibbs_free_energy_eq` — `F(ρ_β) = −T log Z` (equilibrium free energy); the crux `cfc_log_gibbsState` — `log ρ_β = −βH − (log Z)·1` | Honest scope: the inequality (not the equality-iff-Gibbs strict case); `[Nonempty n]`; QM stat-mech with a CSD reading | none |
| **Thermodynamics TH4 — Landauer's principle (2026-07-07)** | `landauer_bound` (`Thermo/Landauer.lean`): the Reeb–Wolf bound — a system coupled by a global unitary to a bath in the Gibbs state obeys `S(ρ_S) − S(ρ_S') ≤ β·ΔQ` (entropy removed ≤ β × heat dumped); chain = entropy conservation (`conj_unitary` + `kronecker`) + `subadditive` + `bath_clausius` (`D(ρ_B'‖τ_B) ≥ 0` through the TH3 Gibbs log identity). `landauer_one_bit` — erasing a maximally-mixed bit costs `ΔQ ≥ T log 2 = kT ln 2` | Honest scope: full-rank final marginals + initial system state; the standard finite-dim Reeb–Wolf setting; QM stat-mech with a CSD reading | none |
| **LF6 entangled de-isolation tier (first results 2026-06-28)** | The non-local strata of D1. **LF6-A:** `no_product_partition_realises_singlet` — the singlet's correlations cannot come from a product/factorised partition of the `Σ`-engine (non-factorisation is **Bell-forced**, derived not posited; factorisation would itself be a measurement), with the contextuality corollary; `singletDeisolationFlow` — a genuine `Φ ≠ id` de-isolation flow on the dilated `ℂℙ¹⁵` realising the singlet dilation. **LF6-B:** the decoherence / partial-trace tier (D1b) — a purity-drop / irreversibility witness on the reduced state, upgraded to the von Neumann entropy jump 0→S>0 (B.3, 2026-07-01). **General-`N` core CLOSED 2026-07-04 (LF6-C/D/E):** GHZ forced contextuality + carve + manifestly-local product flow; general `d×d` maximally-entangled de-isolation with Born-from-volume and forced non-factorisation; the CGLMP violation `I_d > 2` for EVERY `d ≥ 2`; GHZ_n Mermin for EVERY `n`. Named residuals: LF6-6/7 + Lindblad (LF6-2); LF6-5 (general-d CGLMP bound) DONE | **No carving** — the non-factorisation is derived from the engine structure; the flow realises (not carves) the dilation | none |
| **LF5 measurement dynamics (single-system projective tier COMPLETE 2026-06-11; outcome map LF5-F 2026-06-14)** | Layer headline **`measurement_flow_born_frequency`** (`LF5/Capstone.lean`): the five-conjunct chain — `Φ_vN ≠ id` (genuine measurement dynamics), FS measure-preserving (Liouville content), the flow realises the Naimark dilation for **every** preparation (context-fixedness), pointer-block FS volume = Born `‖⟨eᵢ,ψ⟩‖²`, and a.s. pointer-block frequencies → Born — for every unit `ψ`. Built from: LF5-A `vnUnitary` (vN coupling permutation, copy `eⱼ⊗a₀ ↦ eⱼ⊗aⱼ`); LF5-B `measurementFlow` (`Φ_vN ≠ id` on the dilated `ℂℙ^{N·N−1}`, FS-preserving); LF5-C `vnNaimark` (the **dynamically-realised dilation** `V = U_vN ∘ (·⊗a₀)`, pullback `Vᴴ Πᵢ V = \|eᵢ⟩⟨eᵢ\|`, flow carries `[ψ⊗a₀] ↦ [Vψ]`); LF5-D the **unconditional engine** (`LF4/BornRegionUncond.lean`, retires the `hpos` genericity of the general-`N` + POVM engines additively) + `vnDilation_pointer_volume` / `vnDilation_pointer_frequency`. **LF5-F (2026-06-14): the per-microstate outcome map** — `bornRegion_pairwiseDisjoint` (the moment-subdivision is a genuine partition, `LF4/BornRegionDisjoint.lean`) → `vnPointerOutcome` (deterministic, total off an FS-null set, measurable fibres) → `measurement_flow_outcome_frequency` (`LF5/PointerOutcome.lean`, the conjunct-(5) upgrade to a single union event per pointer); closes the outcome-function caveat owed since `aeece86`. Remaining D1: entangled/non-local tier, A5 sector origin | **No carving** — pointer regions are the context-fixed `blockProj` apparatus blocks, the outcome assignment `c ↦ (e.symm c).2` is ψ-independent; the Born number is reused from the FS-volume engine (not re-derived), per the de-isolation reading (carve-out-plan §6); the unconditional zero-weight branch *derives* FS-measure 0 from the `det = 0` geometry | none |
| **LF4 Born-from-volume** | Born weight `‖⟨eᵢ,ψ⟩‖²` = torus moment-map coordinate (`momentMap_mk_eq_inner_sq`) = barycentric volume ratio (`born_eq_volume_ratio`, general `N`) = genuine FS-volume ratio on `Σ=ℂℙ¹` (`fs_born_volume_ratio_qubit`); Busch-free empirical chain (`qubit_born_frequency_convergence`; general-`N` joint form `born_frequency_convergence_partition`) — frequencies → Born via the Kähler volume; unconditional qubit forms `*_uncond` | **No carving** — geometric regions (moment sublevel / barycentric sub-simplex); Born value derived, not cut to fit | none (the `N=2` DH fact `fs_moment_pushforward_uniform` is a discharged **theorem**, plan B closed; the general-`N` extension `fs_moment_joint_dirichlet_N` / `fs_born_volume_ratio_N` / `born_frequency_convergence_N` is likewise foundational-triple-only) |
| **LF4 POVM (Naimark)** | General (non-projective) measurements: every POVM has a canonical Naimark dilation `canonicalNaimark P` (from CFC square roots `√Eᵢ`); `povm_born_eq_dilated_volume` lands the POVM Born weight `⟨ψ,Eᵢψ⟩` as a sum of FS volumes on the dilated `Σ'=ℂℙ^{N·\|ι\|−1}`; `povm_born_frequency_volume` — empirical frequencies → POVM Born weight | **No carving** — dilated barycentric block regions; Born value derived. Honest scope: dilation enlarges the posited `Σ` by the ancilla; the original forms assume genericity `hpos`, **retired by the `_uncond` variants** (`BornRegionUncond.lean`, 2026-06-11 — every unit state, vanishing amplitudes included) | none (Gleason-free; `busch_effect_gleason` no longer on the ontic POVM path) |
| **LF4 §14.2** | `kahler_robertson_ontic_variance` — Robertson bound on ontic-side integrals for any Hermitian observables on `EuclideanSpace ℂ (Fin N)`, with concrete witnesses `pauli_xy_robertson_saturation` (saturation at \|0⟩) and `pauliDot_robertson_zPlus` (parametric over axes) | Compact Kähler `KSigma M = ℂℙ^{M-1} × T²`; N-arc fibre partition via `spectralRegion`; integration headline `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²` | none |
| **LF3** | Singlet kernel `P_st = (1 − st a·b)/4`; LF1↔LF2↔LF3 chain capstones (6 variants); finite-leakage stability | Posited fibre law `μψ` (option (B) chain design, post-Phase-7) | none (chain re-routed off Busch 2026-06-02; the operational-stratum statements are now foundational-triple too — `busch_effect_gleason` proved 2026-07-21) |
| **LF2** | measure bridge `π∗μL = c·μFS` (axiom-free on the concrete instances, `cp_measure_bridge` / `k_measure_bridge`); `born_quadratic` (`Tr(\|ψ⟩⟨ψ\|·\|φ⟩⟨φ\|) = ‖⟨ψ,φ⟩‖²`); `pure_state_born_weights_of_certainty`; `LF1_main_theorem_projective` | Abstract projective target `P` (concrete instantiation deferred to LF4 §8) | none (`busch_effect_gleason` proved 2026-07-21; the abstract-bridge `invariant_measure_uniqueness` was removed 2026-06-04) |
| **LF1** | `LF1_main_theorem_ae` — empirical frequencies converge a.s. to ontic weight under deterministic flow + pairwise-independent i.i.d. preparation | Abstract measurable `SigmaSpace` (no symplectic / Kähler structure assumed) | none |
| **Empirical** | Bell + Tsirelson + No-cloning/-deleting/-broadcasting/-communication + **E91 device-independent security** (the LHV CHSH `\|S\|≤2` bound) + Robertson + Stern-Gerlach + USD + Superdense coding + Teleportation + Quantum money + Mermin-Peres + KS18 + Hardy + GHZ + gates; plus the **CSD volume-frequency series** (SG, Malus, Bell, GHZ, Hardy projective; trine, USD, SIC POVMs — Born values *derived* as FS volumes). Per-test index: [`EMPIRICAL.md`](EMPIRICAL.md) | Two-layer: QM-validity (inner-product geometry) + CSD-side (volume-ratio readings / transport bundles) | foundational triple only on every Empirical pin |
| **Empirical: open-system / decoherence (15-series, 2026-06-30)** | The decoherence stratum (`Empirical/CSD/`): **15a** einselection / pointer-basis selection + degeneracy boundary (`einselection_degenerate_boundary`, `einselectionN`); **15b** QEC-as-decoherence (error = bit-flip channel with Stinespring origin, in-code correction `qec_corrects_decoherence`); **15c** weak / unsharp measurement (`weak_born_unsharp_interpolation`, FS-volume reading `weak_born_frequency_volume`); **15d** quantum Zeno (`zeno_survival_quadratic`, `zeno_freezing`); **15e** channel capacities (`dephasing_classical_vs_quantum`, `holevo_classical_eq_log_two`). Per-test index: [`EMPIRICAL.md`](EMPIRICAL.md) | QM-operational content discharged; the ontic Σ-volume / partial-trace-loss origin uniformly D1-gated (`Φ = id` in concrete `SectorData`) | foundational triple only on every pin |
| **Empirical: metrology / quantum sensing (A1–A3)** | The metrology branch (`Empirical/Metrology/`): Ramsey interferometry, quantum Fisher information, the Heisenberg scaling limit | QM-validity (inner-product / estimator geometry) | foundational triple only on every pin |
| **Algorithms** | n-qubit register + **Deutsch-Jozsa** (1-query constant/balanced), **Simon** (`simon_orthogonal`/`simon_uniform` — the period-promise: every outcome `⊥ s`), **Bernstein-Vazirani** (`bv_certain`/`bv_zero` — one query recovers the hidden linear string, `prob = δ_{y,a}`), **swap test** (`swap_test_prob` — overlap estimator, ancilla-`0` prob `(1+|⟨ψ,φ⟩|²)/2`), **Hadamard test** (`hadamard_test_prob` — `Re⟨ψ,Uψ⟩` estimator, its parent: the swap test is the `U=SWAP` case, `swap_test_via_hadamard`), **Grover** (`sin²((2k+1)θ)` amplitude amplification), **QFT** (`qft_unitary`, finite unitary via roots-of-unity orthogonality), and the **full Shor's algorithm** end to end: order-finding by phase estimation (ideal `r∣T` + Dirichlet `≥4/π²` bound), period recovery, factoring from a nontrivial `√1`, and random-`a` success `≥ 1/2` for *arbitrary odd composite `N`* (`shor_factor_prob_ge`). Per-test index: [`EMPIRICAL.md`](EMPIRICAL.md) | QM-validity (inner-product geometry; `prob = ‖·‖²`). Finite-dimensional throughout — no field theory | foundational triple only on every pin; Tier-A adversarially audited SOUND |

Every theorem listed is AxiomAudit-pinned via `#guard_msgs` in `CsdLean4/Tests/AxiomAudit.lean`; the build fails on axiom drift.

## Quick start

```bash
# Library (LF1+LF2+LF3+LF4+Empirical, no tests):
lake build

# Tests target (AxiomAudit pins + Examples):
lake build CsdLeanTests

# Type-check a single file:
lake env lean CsdLean4/LF4/PauliDotRobertson.lean
```

Toolchain: Lean 4.29.0-rc8 (see `lean-toolchain`); Mathlib4. CI builds both targets on every push to `main` and on PRs.

The canonical top-level import is `CsdLean4` (explicit module list — not glob). For downstream consumers `import CsdLean4.Basic` transitively pulls in the LF1 → LF2 → LF3 → LF4 → Empirical chain.

---

## LF4 — observable correspondence and Robertson uncertainty (§14.2)

LF4 is the layer where projective objects acquire ontic content via a concrete Kähler instance. The §14.2 sub-target — the **observable-correspondence theorem**, lifting self-adjoint Hilbert operators to measurable Σ-valued functions whose integral against the preparation measure matches the Hilbert expectation — is fully discharged on the existing compact Kähler instance, with concrete witnesses.

### The §14.2 chain (six commits)

| Commit | Module | Headline |
|---|---|---|
| `eeec1e8` | `LF4/SpectralExpansion.lean` | `hermitian_inner_spectral_expansion` — `⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²` for any Hermitian `A : Matrix (Fin N) (Fin N) ℂ`. Proof: Parseval (`OrthonormalBasis.sum_inner_mul_inner`) + self-adjointness (`Matrix.isHermitian_iff_isSymmetric`) + eigenvalue equation (`LinearMap.IsSymmetric.apply_eigenvectorBasis`, bridged to the Matrix-level reindexed basis as Mathlib's `Matrix.Spectrum` does internally) |
| `dec11e5` | `LF4/SpectralCarving.lean` | Multi-region carving infrastructure (`fibreShiftedArc`, `cumWeights`, `spectralRegion`) + integration headline `integral_spectralOntic_eq_inner_re` — `∫ spectralOntic dμψ = re ⟨ψ, A ψ⟩`. The pre-existing `fibreArc ℓ = (0, ℓ]` is anchored at 0, so distinct arcs are nested; the shifted-anchor primitive gives genuinely disjoint N-arc partitions |
| `fe717ed` | `LF4/SpectralVariance.lean` | `spectralVariance := ∑ᵢ (λᵢ − ⟨A⟩)² · bornWeights i` and the composite headline `integral_spectralOnticCentered_eq_hilbert_norm_sq_diff` — `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²` (the standard QM variance form for self-adjoint A) |
| `63fe1b0` | `LF4/UncertaintyKahler.lean` | `kahler_robertson_ontic_variance` — Robertson bound with **ontic-side LHS**: `(∫ spectralOnticCentered hA ψ dμψ) · (∫ spectralOnticCentered hB ψ dμψ) ≥ ¼ ‖⟨ψ, [A, B] ψ⟩‖²`. Bridges QM-side `variance` (norm-sub-sq form) to spectral form via `variance_eq_norm_sq_sub_expectation_sq` and composes with `Empirical.Uncertainty.robertson_uncertainty` |
| `59eba66` | `LF4/PauliRobertson.lean` | First concrete witness: `pauli_xy_robertson_saturation` — `σ_x, σ_y` on `|0⟩` saturates Robertson with both sides equal to 1. The canonical textbook example, machine-verified |
| `c5eed61` | `LF4/PauliDotRobertson.lean` | Parametric generalisation: `pauliDot_robertson_zPlus â b̂ p₀` — `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²` for arbitrary unit-vector axes (the `DetectorSetting` constraint). Both sides explicit polynomials in the axis components |

The Kähler instance is `KSigma M = CPN M × KTorus = ℂℙ^{M-1} × (AddCircle 1 × AddCircle 1)` with `kMuL = fubiniStudyMeasure p₀ ⊗ vol_T²`. The preparation measure for §14.2 is `(Measure.dirac p₀) ⊗ vol_T²` (Dirac on the base ray × Haar on the fibre).

### What §14.2 unlocks

- **Uncertainty bundle's ontic-variance match**: pre-LF4 `csd_robertson_uncertainty` was a transport theorem (any Hilbert state satisfies Robertson). With `kahler_robertson_ontic_variance`, the physical content — ontic variances satisfy Robertson, not just Hilbert variances — is realisable for any concrete pair of bounded Hermitian observables.
- **Any multi-eigenvalue observable**: spin-1 components, GHZ stabiliser generators, generic Hermitian operators. The spectral pattern works beyond ±1 / projector cases.
- **Variance identity in spectral form**: `Var_ψ(A) = ∑ᵢ (λᵢ − ⟨A⟩)² · ‖⟨uᵢ, ψ⟩‖²`, with `bornWeights ψ A i = ‖⟨uᵢ, ψ⟩‖²` summing to `‖ψ‖²` via `OrthonormalBasis.sum_sq_norm_inner_right`.

### LF4 design choices (post-§14.2)

- `SectorData` (LF2) is the abstract layer; the compact Kähler instance is `KSigma M` defined in `LF4/KahlerInstance.lean`, with `fubiniStudyMeasure p₀` (Dirac at `p₀ : CPN M`) and `vol_T²` (Haar on the flat torus). Fibre arcs are subsets of `AddCircle 1` carved via `equivIoc 1 0`.
- The `fibreShiftedArc c ℓ := (equivIoc 1 0)⁻¹' (Ioc c (c+ℓ))` primitive replaces the nested `fibreArc ℓ = (0, ℓ]` from `SingletKahler.lean` for genuinely-disjoint N-arc partitions. Volume = `ENNReal.ofReal ℓ` for `[c, c+ℓ] ⊆ [0,1]`; disjoint when underlying intervals are disjoint.
- `cumWeights w : Fin (N+1) → ℝ` is defined via `Finset.filter` (not `Nat.rec`) for clean `Finset.sum_insert` proofs of the succ-castSucc step and `cumWeights_last = ∑ w`.
- The variance bridge `variance_eq_norm_sq_sub_expectation_sq` uses `norm_sub_sq` + `Complex.mul_conj` + `Complex.normSq_apply` to derive `Var = ‖Aψ‖² − (re ⟨A⟩)²` from the standard QM `Var = ‖Aψ − ⟨A⟩ψ‖²` definition for symmetric `T` and unit `ψ`.
- Robertson on ontic variances is `kahler_robertson_ontic_variance`; its proof composes `QM_variance_eq_integral_spectralOnticCentered` (the spectral bridge applied twice) with the existing QM-side `Empirical.Uncertainty.robertson_uncertainty` (Cauchy-Schwarz + commutator algebra).

### LF4 backlog (`specs/LF4-todo.md`)

§14.2 is **closed**. Remaining LF4 work:

- **§13** — isometry realisability (cloning / deletion / N-qubit unitaries as Σ-flows). Partial; cloning + deletion bundles in place.
- **§8** — concrete `SectorData` constructions for additional preparation classes (mixed-state, multi-particle).
- **§1-§11** — see `specs/LF4-todo.md` for the full backlog (preparation-to-Hilbert correspondence, projective-first outcome specification, etc.).

---

## LF3 — singlet kernel and the LF1↔LF2↔LF3 empirical chain

LF3 sits on top of LF2 and delivers the **first concrete CSD-ontic prediction** beyond the abstract `SectorData` layer: the singlet kernel `P_st(a, b) = (1 − s·t·a·b)/4` and its four operational consequences (correlation `−a·b`, marginals `1/2`, no-signalling on each side, pointer-completeness), with finite-leakage stability of all four.

### Headline deliverables

1. **Singlet kernel algebraic core** — `cst_squared_eq : ‖cAmp s t (a, b)‖² = (1 − st·a·b)/4`, with `cAmp := (Real.sqrt P_st : ℂ)` as the v1.00 closed-form representative.
2. **Eight-conjunct strong-readout package** — `LF3_main_theorem`. Kernel + correlation + marginals + no-signalling + pointer-completeness in one statement.
3. **Finite-leakage four-conjunct package** — `LF3_finite_leakage_theorem`. Each quantity deviates from its strong-readout value by at most `εA + εB + εA·εB` (with explicit prefactors). Stability-from-assumption (the deviation bound enters as a field of `LeakageCompat`, not a first-principles derivation).
4. **Six chain capstones** — three per-sector + three joint-partition Phase 8 variants:
   - `LF3_singlet_frequency_convergence` (pre-Born, lands on `P_st`),
   - `LF3_singlet_frequency_convergence_born` (closed-form Born, lands on `‖cAmp‖²`),
   - `LF3_singlet_frequency_convergence_born_inner` (bra-ket form, lands on `‖⟨v, ψ⁻⟩‖²` for caller-supplied joint spin eigenstate `v`),
   - plus `..._joint`, `..._born_joint`, `..._born_inner_joint` (joint AE over `Sign × Sign`).

All six chain capstones consume a `PureSingletPreparation D ctx N` bundle (option (B) form, post-Phase 7), whose load-bearing hypotheses are `MeasurementJointEig.born_eq_P_st` (Born identity for joint spin eigenstates) and `PureSingletPreparation.bridge_op_p` (ontic-weight ↔ OP.p bridge). The bundle's `weight_eq_P_st` theorem composes the two.

### LF3 axiom posture (post Phase 7, 2026-05-18)

- `LF3_main_theorem` and `LF3_finite_leakage_theorem` cite **only** the foundational triple.
- The six chain capstones are now **foundational-triple-only** (re-routed off Busch, 2026-06-02): `weight_eq_P_st` routes the chain bridge through the Busch-free `OP_p_at_jointEig_eq_P_st_direct` (the ontic-stratum, direct volume-ratio Born step). The Busch-mediated twin `OP_p_at_jointEig_eq_P_st` remains as the operational-stratum statement. So the LF3 empirical chain is Gleason-free. The operational-stratum statements (`pure_state_born_weights_of_certainty`, `born_rank_one`, `OP_p_at_jointEig_eq_P_st`, `ontic_born_frequency`) that once cited `busch_effect_gleason` are now foundational-triple too, since that axiom was **proved** 2026-07-21 (`effect_gleason_representation`). See [`AXIOMS.md`](AXIOMS.md) §2.2, §2.4.
- The measure bridge carries **no axiom** on the chain capstones: the concrete instances supply it axiom-free (`cp_measure_bridge` / `k_measure_bridge`). The abstract `measure_bridge` and the `invariant_measure_uniqueness` axiom it required were removed 2026-06-04.

The full per-theorem audit is in [`AXIOMS.md`](AXIOMS.md) §3.6 and §5. Regression-protection via `CsdLean4/Tests/AxiomAudit.lean`'s `#guard_msgs` against `#print axioms`.

### Posted-fibre-measure migration (2026-05-25)

The preparation primitive at LF3 is a posited fibre trial law `μψ` (option (B)), not the ambient `μL`-conditional `prepMeasure`: under the continuous measure bridge `π∗μL = c·μFS`, every state's fibre is μL-null, so a μL-conditional pure preparation is uninhabitable. The capstones take i.i.d. trials with common law `μψ` and route through `LF1.freq_tendsto_of_iid` (not `LF1_main_theorem_ae`). See `LF4-todo §8`.

---

## LF2 — sector-conditional measure bridge and Born-weight wrapper

LF2 connects LF1's ontic volume weights to projective Born-form probabilities under explicit symmetry and operational hypotheses.

### What LF2 delivers

1. **Measure bridge** — `π∗ μL = c · μFS` for some `c : ENNReal`, under symmetry-compatible `SectorData`. Internal proof of `G`-invariance of `π∗ μL`, then uniqueness of the invariant measure. On the concrete instances the bridge holds **axiom-free** (`cp_measure_bridge` / `k_measure_bridge`, `c = 1`); the abstract over-general statement and its `invariant_measure_uniqueness` import were removed 2026-06-04 (the `ℂℙ^{N-1}` uniqueness is itself a proved axiom-free theorem).
2. **LF1 ↔ LF2 weight identity** — `μprep(π⁻¹(O_ep)) = projectiveWeight D μprep O_ep`. The structural hinge.
3. **Combined LF1 + LF2 theorem** — `LF1_main_theorem_projective`. LF1 empirical frequency converges almost surely to the real-valued projective weight under the outcome correspondence `O.preEvent = π⁻¹(O_ep)`.
4. **Born quadratic form** — `born_quadratic`. For unit `ψ, φ : EuclideanSpace ℂ (Fin N)`, `Tr(|ψ⟩⟨ψ| · |φ⟩⟨φ|) = ‖⟨ψ, φ⟩‖²`. Genuine Lean proof via trace-of-outer-product + `Complex.mul_conj`.
5. **Pure-state Born weights from certainty** — `pure_state_born_weights_of_certainty` (in `LF2/EffectGleason.lean` since 2026-07-21). Given an `OP` that is "certain" at `|ψ⟩`, for every unit `φ` the probability is `‖⟨ψ, φ⟩‖²`. Composes the now-**proved** `effect_gleason_representation` + `rankOneDensity_unique_of_certainty` + `born_quadratic` — foundational-triple only.

### LF2 axiom posture — zero imported axioms (since 2026-07-21)

The corpus imports **no** axioms beyond Lean's foundational triple. The former imports:

| Former axiom | Role | Status |
|---|---|---|
| `busch_effect_gleason` | Effect-additive probability admits a unique trace-form density | **Proved 2026-07-21** — now `OperationalPackage.effect_gleason_representation` (`LF2/EffectGleason.lean`), foundational-triple, AxiomAudit-pinned. |
| `invariant_measure_uniqueness` | `ℂℙ^{N-1}` FS-measure uniqueness | **Removed 2026-06-04** — abstract bridge unused; concrete uniqueness is a proved theorem. |
| `rankOneDensity_unique_of_certainty` | Certainty ⇒ pure-state density | **Proved 2026-05-18** — via `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` (`LF2/BornWrapper.lean`). |

LF1 theorems, `born_quadratic`, and `LF1_main_theorem_projective` were always axiom-free beyond the triple; with `busch_effect_gleason` discharged, so is everything else — including the operational-stratum `pure_state_born_weights_of_certainty` chain.

### Design choices in LF2

- `SectorData` is parametric in `(SigmaSpace, P, G)`. The projective target is kept abstract — no `Projectivization`, no Fubini–Study measure constructed. Concrete instantiation is LF4 §8's job.
- `μFS` is **not** a field of `SectorData`; it enters via the `MeasureBridgeData` bundle as an explicit argument, keeping `SectorData` `μFS`-agnostic.
- `Effect` and `DensityOperator` are concrete `Matrix (Fin N) (Fin N) ℂ` structures (not opaque stubs). This gives `born_quadratic` real Lean content.
- `Effect.add` takes the `le_one` hypothesis explicitly; avoids `Option`-valued addition.
- Spec Def 5.1 clause 3 (unitary covariance) is **not** a field on `OperationalPackage` — the literal invariance over-constrains, the covariant reading is type-heavy. Deferred to LF4.

---

## LF1 — deterministic repeated-trial typicality theorem

For a finite-measure ontic state space `(Σ, μL)`, measurable preparation region `Ω0 ⊂ Σ`, measurable outcome partition `{Ω_i^Σ}`, and deterministic `μL`-preserving flow `Φ_t`: LF1 studies repeated trials whose initial microstates are sampled independently from the conditional preparation measure on `Ω0`.

### Headline theorem

```lean
theorem LF1_main_theorem_ae
    (T : S.TrialModel Ω)
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g T.trialMeasure)
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto (T.empiricalFreq O · ω) atTop (nhds O.weightReal)
```

Empirical frequencies converge `μ`-almost surely to the real-valued ontic weight under repeated preparation with **pairwise-independent trial indicators**. Pairwise independence is the only non-trivial repeated-trial hypothesis; integrability and identical distribution are automatic from the `TrialModel` structure.

### Deterministic content

LF1 is not merely a law-of-large-numbers on an abstract probability space. The physical content is **deterministic at the ontic level**:

- Each single trial is generated by a deterministic measurable flow `Φ_t : Σ → Σ`.
- The outcome of a single trial is determined by the initial microstate `x ∈ Σ`.
- The outcome event is `x ∈ Φ_t⁻¹(Ω_i^Σ)`.

No stochastic evolution at the ontic level. The only probabilistic ingredient is the repeated-trial preparation model. LF1 is a **deterministic typicality theorem with a probabilistic preparation model**, not an intrinsic-randomness theorem.

### Scope and limitations

`OnticSetup` takes an abstract `SigmaSpace : Type*` — **not** specialised to `ℝ^{2n}`, a symplectic manifold, or any concrete phase space. Physical meanings:

| Field | Physical meaning | Status in v1.00 |
|---|---|---|
| `μL` | Liouville measure | *assumed* as a finite measure |
| `Φ` | Hamiltonian flow | *assumed* as a measurable map |
| `hΦ_pres` | Liouville's theorem | *assumed*; structurally inert through LF3 (see `LF1/Setup.lean`) |
| `Ω0` | Preparation region | *assumed* as a measurable set |

**Structural assumption** (preparation-measure origin): `μL` is asserted as a finite measure; the flow `Φ` is asserted to preserve it; neither is derived from a symplectic / Kähler volume form in v1.00. The LF1 frequency theorem is correspondingly more general than the physical reading suggests. This assumption discharges at the Lean level when LF4 instantiates `SigmaSpace` as a compact Kähler manifold and constructs `μL` from `ω^n / n!` — **partially done** by `LF4/KahlerInstance.lean`, which provides `KSigma M = ℂℙ^{M-1} × T²` with `fubiniStudyMeasure` and `vol_T²` as the concrete instance for §14.2. Deriving the flow itself (rather than asserting it) is a deeper, theory-level question.

---

## Empirical — QM-validity regression suite

The Empirical module is a **QM-validity layer** regression suite. Each theorem proves that the standard QM formalisation produces the predicted experimental number; the proofs are linear algebra and inner-product geometry, with no ontic substrate at the proof level. CSD's foundational claim — that QM emerges from volume ratios on Σ — is verified at the **CSD-ontic layer** by the LF3 chain capstones and (now) the LF4 §14.2 carving / variance / Robertson chain.

**[`EMPIRICAL.md`](EMPIRICAL.md) is the per-test index** — every validation in both branches with its file, headline theorem, claim, and physics source. The phase table below is the abridged map; `EMPIRICAL.md` is the full enumeration.

### Current Empirical phases

| Phase | Predictions | Files |
|---|---|---|
| **A** (Bell) | CHSH at Tsirelson bound, classical-violation gap, no-signalling, marginals, Khalfin-Tsirelson upper bound | `Empirical/QM/Bell.lean`, `Empirical/CSD/Bell.lean` |
| **B** (Resources) | No-cloning (Wootters-Zurek + Dieks 1982), no-deleting (Pati-Braunstein 2000), superdense coding, quantum money, Stern-Gerlach | `Empirical/QM/{NoCloning,NoDeleting,Resources/SuperdenseCoding,Crypto/QuantumMoney,SternGerlach,Uncertainty}.lean` |
| **C** (Contextuality / Paradoxes) | Kochen-Specker 18-vector (Cabello 1996), Mermin-Peres magic square, GHZ all-or-nothing (Mermin form), Hardy non-locality | `Empirical/QM/{Contextuality/KS18,Contextuality/MerminPeres,Multipartite/GHZ,Hardy}.lean` |
| **D** (Gates) | Single-qubit gates, two-qubit gates, Bell preparation, multi-qubit gate semantics | `Empirical/QM/Gates/*.lean` |
| **E** (QI / crypto) | No-broadcasting, no-communication, teleportation, Robertson uncertainty, E91 device-independent security, unambiguous discrimination (USD) | `Empirical/QM/{NoBroadcasting,NoCommunication,Resources/Teleportation,Uncertainty,Crypto/E91,USD}.lean` |
| **V** (volume series) | Born numbers *derived* (not transported) as Fubini-Study volumes: Stern-Gerlach, Malus, Bell, GHZ, Hardy, the **uncertainty** variance as a product of typicality volumes (`Var = 4·vol₊·vol₋`), the trine / USD / SIC / qutrit / Hesse / MUB POVMs, and **any projective measurement context**, rank-1 *and* degenerate (`context_born_frequency_volume` / `block_born_frequency_volume` — the general contextuality grounding, Kochen-Specker + Mermin-Peres rank-2 eigenspaces as block sums of FS volumes), with the **Cabello-18 Kochen-Specker** context (`ks18_context_born_frequency_volume`) and the **full 9-observable Mermin-Peres square** (`mp_{xx,xi,ix,zi,iz,xz,zx,yy}_born_frequency_volume`, each cell's frame machine-checked as the genuine `σ_a⊗σ_b` eigenbasis and its block as the `+1` eigenspace) as concrete instances. Genericity-free since the 2026-06-11 hpos migration (`BornRegionUncond.lean`): boundary preparations — context eigenstates, the Mermin GHZ points `Φ = 0, π`, aligned Bell analysers — covered | `Empirical/CSD/{SternGerlach,Malus,Bell,GHZ,Hardy,Trine,USD,SIC,…}Volume.lean`, `Empirical/CSD/ContextVolume.lean`, `Empirical/CSD/Contextuality/{KS18Volume,MerminPeresVolume}.lean` |
| **Alg** (algorithms) | n-qubit register; Deutsch-Jozsa; Simon (period-promise, outcomes `⊥ s`); Bernstein-Vazirani (1-query hidden string, `prob = δ_{y,a}`); swap test (overlap estimator, `(1+|⟨ψ,φ⟩|²)/2`); Hadamard test (`Re⟨ψ,Uψ⟩` estimator, swap test = `U=SWAP` case); Grover `sin²((2k+1)θ)`; QFT unitarity; full Shor (quantum core + recovery + factoring + random-`a` ≥ 1/2 for arbitrary odd composite `N` + capstone) | `Mathlib/QuantumInfo/{Register,Hadamard,Fourier}.lean`, `Empirical/QM/Algorithms/{DeutschJozsa,Simon,BernsteinVazirani,SwapTest,HadamardTest,Grover,ShorCore,ShorRecovery,ShorRandomA,ShorCapstone}.lean` |

Every Empirical theorem is **foundational-triple-only** and AxiomAudit-pinned. The CSD-side companions in `Empirical/CSD/` transport each QM-validity statement through a `CSDBridge.Context D` bundle, carrying the LF2 `SectorData` + measure-bridge data, providing the structural slot for the CSD-ontic interpretation that LF4 will eventually instantiate via `kahler_robertson_ontic_variance` and similar §14.2 mechanisms.

### Two-layer model: QM-validity vs CSD-ontic

The QM-validity layer is **prerequisite** to the CSD-ontic layer. LF4 §14.2's spectral expansion + carving + integration headline + Robertson chain provides the **lifting mechanism**: any QM-validity statement about expectations and variances of bounded Hermitian observables on `EuclideanSpace ℂ (Fin N)` has a corresponding CSD-ontic statement on `KSigma M`, with the same numerical prediction realised via spectral indicator sums integrated against the preparation measure.

See [`EMPIRICAL.md`](EMPIRICAL.md) for the per-test index, `specs/qm-empirical-tests.md` §0.1 for the full two-layer correspondence statement, and `specs/empirical-csd-bridge-plan.md` for the CSDBridge architecture.

---

## Genealogy

The LLN-based typicality framing used in LF1 and the geometric quantum mechanics structure on `CP^{N-1}` consumed by LF2 match structures developed independently in the Dürr / Goldstein / Zanghì typicality line and the Kibble / Heslot / Anandan / Ashtekar-Schilling geometric quantum mechanics line. The CSD corpus uses the standard mathematical machinery shared with those programmes (measure theory, finite-dim inner-product geometry, the symplectic-Kähler structure on `CP^{N-1}`), and the Lean tree imports Mathlib accordingly. What is independently rediscovered is the **structural choice of objects**: typicality measures on the ontic phase space for LF1, the Born quadratic form on projective Hilbert space for LF2, and (as of §14.2) the eigenvalue-weighted indicator sum integrated against the fibre measure as the ontic counterpart of Hilbert expectation values. The corpus arrives at those choices from its own internal logic; convergence is offered as a credibility signal rather than a claim of priority.

---

## Theorem inventory

Exported theorems and their dependencies. The "Axioms" column lists CSD-specific axioms beyond Lean's foundational triple (`propext`, `Classical.choice`, `Quot.sound`); these are always present via Mathlib and not separately listed. For the full audit see [`AXIOMS.md`](AXIOMS.md).

### LF4 §14.2 (observable correspondence + Robertson on Kähler instance)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `hermitian_inner_spectral_expansion` | `LF4/SpectralExpansion.lean` | `⟨ψ, A ψ⟩ = ∑ᵢ (λᵢ : ℂ) · ‖⟨uᵢ, ψ⟩‖²` for Hermitian `A : Matrix (Fin N) (Fin N) ℂ`. | none |
| `hermitian_inner_spectral_expansion_re` | `LF4/SpectralExpansion.lean` | Real-valued form: `re ⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²`. | none |
| `fibreShiftedArc_volume` | `LF4/SpectralCarving.lean` | Shifted-anchor primitive: `vol (fibreShiftedArc c ℓ) = ofReal ℓ` for `[c, c+ℓ] ⊆ [0,1]`. | none |
| `diracProd_spectralRegion` | `LF4/SpectralCarving.lean` | Per-region carving identity: `(Dirac p₀ ⊗ vol_T²)(spectralRegion w i) = ofReal (w i)` for nonneg `w` with `∑ w ≤ 1`. | none |
| `integral_spectralOntic_eq_inner_re` | `LF4/SpectralCarving.lean` | Integration headline: `∫ spectralOntic dμψ = re ⟨ψ, A ψ⟩` for unit `ψ`. | none |
| `hilbert_norm_sq_apply_hermitian` | `LF4/SpectralVariance.lean` | `‖A ψ‖² = ∑ᵢ λᵢ² · bornWeights i` for Hermitian `A`. | none |
| `spectralVariance_eq_hilbert_norm_sq_diff` | `LF4/SpectralVariance.lean` | `spectralVariance = ‖A ψ‖² − (re ⟨A⟩)²` under unit `ψ`. | none |
| `integral_spectralOnticCentered_eq_variance` | `LF4/SpectralVariance.lean` | `∫ spectralOnticCentered dμψ = spectralVariance` under unit `ψ`. | none |
| `integral_spectralOnticCentered_eq_hilbert_norm_sq_diff` | `LF4/SpectralVariance.lean` | Composite: `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²`. | none |
| `QM_variance_eq_spectralVariance` | `LF4/UncertaintyKahler.lean` | Bridge: `Empirical.Uncertainty.variance A.toEuclideanLin ψ = spectralVariance hA ψ`. | none |
| `kahler_robertson_ontic_variance` | `LF4/UncertaintyKahler.lean` | **Robertson on ontic variances**: `(∫ spectralOnticCentered hA ψ dμψ) · (∫ spectralOnticCentered hB ψ dμψ) ≥ ¼ ‖⟨ψ, [A, B] ψ⟩‖²`. | none |
| `pauli_xy_robertson_saturation` | `LF4/PauliRobertson.lean` | First concrete witness: `σ_x, σ_y` on `|0⟩` saturates Robertson; both sides equal 1. | none |
| `pauliDot_robertson_zPlus` | `LF4/PauliDotRobertson.lean` | Parametric: `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²` for unit-vector axes `â, b̂`. | none |

### LF4 Born-from-Kähler-volume (the moment-map cluster)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `kFlow_measurePreserving`, `kFlow_frequency_convergence` | `LF4/KahlerFlow.lean` | First non-trivial measure-preserving flow `Φ≠id` (fibre translation); LF1 typicality non-vacuous, `hΦ_pres` load-bearing. | none |
| `momentMap_mk_eq_inner_sq` | `LF4/MomentMap.lean` | Born weight = torus moment-map coordinate `Φ([ψ])ᵢ = ‖⟨eᵢ,ψ⟩‖²` (forced symplectic invariant). | none |
| `born_eq_volume_ratio` | `LF4/BornVolume.lean` | Born weight = barycentric Lebesgue-volume ratio of the vertex-replacement image (general `N`). | none |
| `momentMap_orbit` | `LF4/MomentPushforward.lean` | Reduces `Φ∗μ_FS = uniform_Δ` to the Haar marginal (μ_FS = Haar-on-`U(N)` pushforward). | none |
| `fs_born_volume_ratio_qubit` | `LF4/BornFS.lean` | Born weight = genuine `fubiniStudyMeasure` volume ratio on `Σ=ℂℙ¹`, modulo `h_uniform`. | none |
| `qubit_born_frequency_convergence` | `LF4/QubitBornFrequency.lean` | **Busch-free** empirical chain: frequencies → `‖⟨e₀,ψ⟩‖²` via the FS volume, modulo `h_uniform`. | none |
| `born_frequency_convergence_partition` | `LF4/BornFrequencyPartition.lean` | General-`N` joint Busch-free chain: frequencies → Born weights over a finite outcome family (Born = ontic volume as hypothesis). Closes LF4-todo §9. | none |
| `momentMap_pushforward_eq_haar_marginal` | `LF4/MomentMarginal.lean` | Plan B step 1: the moment marginal = the Haar law of `‖(U·rep)ᵢ‖²/‖U·rep‖²`. | none |
| `fs_moment_pushforward_uniform` | `LF4/MomentUniform.lean` | The `N=2` Duistermaat–Heckman fact `Φ₀∗μ_FS = uniform[0,1]`, **discharged to a theorem** (plan B, Gaussian + FS-uniqueness route). | none |
| `fs_born_volume_ratio_qubit_uncond` | `LF4/MomentUniform.lean` | **Unconditional** qubit Born = FS-volume ratio on `ℂℙ¹`. | none |
| `qubit_born_frequency_convergence_uncond` | `LF4/MomentUniform.lean` | **Unconditional** Busch-free qubit Born frequency convergence. | none |

**General-`N` Duistermaat–Heckman / Born-from-Kähler-volume (the qubit result extended to all `N`, 2026-06-02):**

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `fs_moment_joint_dirichlet_N` | `LF4/MomentDirichletN.lean` | **Joint Duistermaat–Heckman law, general `N`**: `(ratioN ∘ momentMap)∗ μ_FS = M!·vol\|_{simplex}` on `ℂℙ^M` (the Dirichlet(1,…,1) law). The qubit scalar marginal is only `Beta(1,N−1)` for `N≥3`; the joint simplex law is what feeds Born. | none |
| `fs_volume_eq_dirichlet`, `volume_openSimplexFree` | `LF4/MomentBornN.lean` | The DH volume law on `Σ` (`μ_FS` of a moment region `= M!·`its Lebesgue volume); the free simplex has volume `(M!)⁻¹`. | none |
| `fs_born_volume_ratio_N`, `fs_born_volume_ratio_N_apex` | `LF4/MomentBornN.lean` | **Unconditional** Born = FS-volume ratio of the `i`-th barycentric region, **all `N` coordinates** (free coords + the affine apex). | none |
| `born_frequency_convergence_N` | `LF4/BornFrequencyN.lean` | **Unconditional Busch-free general-`N` empirical chain**: i.i.d. trials from `μ_FS` on `ℂℙ^M` ⟹ frequencies → the full Born vector `‖⟨eᵢ,ψ⟩‖²` jointly a.s. The i.i.d. trial law is now **witnessed by a canonical in-tree process** (`Measure.infinitePi` of `μ_FS`, `LF4/TrialWitness.lean`): `born_frequency_convergence_N_canonical` and the LF5 `measurement_flow_born_frequency_canonical` (`LF5/CapstoneCanonical.lean`) discharge the whole trial bundle, conclusions verbatim. | none |
| `measurePreserving_piCurry`, `map_curryProd_pi` | `Mathlib/MeasureTheory/PiCurry.lean` | Cat-1 Mathlib-gap: currying a sigma/product index preserves `Measure.pi`. | none |
| `fs_moment_pushforward_uniform_of_joint_dirichlet` | `LF4/QubitConsistency.lean` | **N=2 consistency cross-check**: the qubit `fs_moment_pushforward_uniform` is kernel-derived from `fs_moment_joint_dirichlet_N (M:=1)` (via the `(Fin 1 → ℝ) ≃ᵐ ℝ` eval iso + `Ioo`/`Icc` null-set bridge), machine-confirming the general-`N` law faithfully generalises the independently-proved qubit result. | none |

The qubit's former `h_uniform` hypothesis is now the **theorem** `fs_moment_joint_dirichlet_N`, so the general-`N` Born-from-volume chain is **unconditional and foundational-triple-only — no `busch_effect_gleason`**. The CSD thesis is realised end-to-end for general `N`: deterministic LF1 typicality + Born = Kähler volume ⟹ frequencies → Born, with Born *derived* from the symplectic geometry rather than imported via Gleason. Plan and honesty ledger: `specs/general-n-dh-plan.md`. Genericity hypothesis on the Born-region forms: `ψ` has no vanishing amplitude.

**Foundational reading (two strata).** The corpus reaches Born by two derivations, kept deliberately separate. The *operational* stratum (the Gleason-class argument, the **proved** theorem `effect_gleason_representation` — formerly the import `busch_effect_gleason`, discharged 2026-07-21) forces Born from effect-additivity given the formalism, with no configuration space, covering arbitrary effects. The *ontic* stratum (LF2 → LF4) derives Born as the Fubini–Study volume ratio, with the U(N) symmetry fixing the volume; this is foundational-triple-only and Gleason-free. The shift to the ontic derivation is a **relocation of the primitive, not its elimination**: Born becomes a theorem of the posited quantum-effective sector structure (`SectorData.(π, G)` — the projection onto the sector and its U(N) symmetry; see [`AXIOMS.md`](AXIOMS.md) §3.3) rather than an independent probability postulate. Honest hierarchy: Born-as-a-volume-ratio is dischargeable now for projective measurements *modulo* that sector posit, which in turn rests on the deterministic dynamics — and in every concrete instance the flow is currently the identity, so the dynamics layer is not yet exercised (the deepest open question, calling for further theoretical development). **General POVMs are now covered geometrically too** (the Naimark-dilation route, see the POVM table below): the (non-projective) POVM Born weight is a sum of Fubini–Study volumes on a dilated `Σ' = ℂℙ^{N·|ι|−1}`, unconditionally and Gleason-free, with `canonicalNaimark` supplying the dilation for every POVM — at the cost of enlarging the posited sector structure by the ancilla.

**POVM extension (Naimark dilation — the ontic Born derivation for general measurements, 2026-06-03):**

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `POVM`, `weights_sum_eq_normSq` | `LF2/POVM.lean` | The POVM type (effects summing to `I`); the Born weights `pᵢ(ψ)=⟨ψ,Eᵢψ⟩` sum to `‖ψ‖²`. | none |
| `NaimarkDilation`, `born_transfer` | `LF4/POVMDilation.lean` | The dilation data (isometry `V`, `Vᴴ Πᵢ V = Eᵢ`); the Born transfer `⟨ψ,Eᵢψ⟩ = ⟨Vψ, Πᵢ Vψ⟩` onto the projective surface. | none |
| `povm_born_eq_block_sum` | `LF4/POVMVolume.lean` | POVM weight = `∑ₙ` dilated computational-basis (rank-1) Born weights over the `i`-th ancilla block. | none |
| `povm_born_eq_dilated_volume` | `LF4/POVMVolume.lean` | **POVM Born weight = a sum of Fubini–Study volumes** of the dilated barycentric cells on `Σ'=ℂℙ^{N·\|ι\|−1}` (via the `piLpCongrLeft` reindex + `bornRegion_fs_measure`). | none |
| `povm_born_frequency_volume` | `LF4/POVMVolume.lean` | **The observable capstone**: i.i.d. FS trials on `Σ'` ⟹ the `i`-th POVM outcome's empirical frequency → `⟨ψ,Eᵢψ⟩`. Carving-free, Gleason-free. | none |
| `canonicalNaimark`, `naimarkV_isom`, `naimarkV_pullback` | `LF4/POVMNaimark.lean` | **Existence**: the canonical Naimark dilation from the CFC square roots `√Eᵢ = cfc Real.sqrt Eᵢ` inhabits `NaimarkDilation P` for **every** POVM — making the volume/frequency results unconditional. | none |

This makes the ontic Born derivation cover **arbitrary quantum measurements**, not just projective (von Neumann) ones, with effect-Gleason fully off the ontic path — it serves only as the operational-stratum closure (and, since 2026-07-21, is itself a proved theorem, not an axiom). Plan and honesty ledger: `specs/povm-plan.md`. The genericity hypothesis (`hpos`: the dilated state `ψ'` has no vanishing amplitude) carried by the original forms is **retired** by the hpos-free `_uncond` variants (`povm_born_eq_dilated_volume_uncond` / `povm_born_frequency_volume_uncond`, `LF4/BornRegionUncond.lean`); since the 2026-06-11 call-site migration all Empirical/CSD POVM witnesses route through them.

### LF3 (singlet kernel, pointer-sector decomposition, empirical chain)

`LF3_main_theorem` and `LF3_finite_leakage_theorem` cite **only** the foundational triple. The six chain capstones are now **foundational-triple-only** too (re-routed off Busch, 2026-06-02): `weight_eq_P_st` routes the chain bridge through the Busch-free `OP_p_at_jointEig_eq_P_st_direct`. The operational-stratum statements are now foundational-triple too — `busch_effect_gleason` was proved 2026-07-21.

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `singlet_pauli_correlation` | `LF3/Singlet/Expectations.lean` | `⟨ψ⁻ \| σ·a ⊗ σ·b \| ψ⁻⟩ = −a·b`. | none |
| `cst_squared_eq` | `LF3/Singlet/Kernel.lean` | `‖cAmp s t (a, b)‖² = (1 − s·t·a·b) / 4`. | none |
| `correlation_eq_neg_dot` | `LF3/Singlet/Kernel.lean` | `∑ s t, s·t · P_st(a, b) = −a·b`. | none |
| `marginal_a_eq_half`, `marginal_b_eq_half` | `LF3/Singlet/Kernel.lean` | Both wing marginals equal `1/2`. | none |
| `no_signalling_strong_readout_a`, `..._b` | `LF3/Singlet/Kernel.lean` | Each wing's marginal independent of the other wing's setting. | none |
| `sectorVolume_eq_LF2_Born` | `LF3/Projectors/LF2Interface.lean` | LF3 operator-form sector volume = LF2 Born weight on rank-1 effects. | none |
| `LF3_main_theorem` | `LF3/Interface.lean` | Eight-conjunct strong-readout package. | none |
| `LF3_finite_leakage_theorem` | `LF3/Interface.lean` | Finite-leakage stability of all four kernel quantities. | none |
| `LF3_singlet_frequency_convergence` | `LF3/Interface.lean` | Pre-Born chain capstone (per-sector). | none |
| `LF3_singlet_frequency_convergence_born` | `LF3/Interface.lean` | Closed-form Born variant. | none |
| `LF3_singlet_frequency_convergence_born_inner` | `LF3/Interface.lean` | Bra-ket variant. | none |
| `LF3_singlet_frequency_convergence_joint` | `LF3/Interface.lean` | Phase 8 joint-partition variant of pre-Born capstone. | none |
| `LF3_singlet_frequency_convergence_born_joint` | `LF3/Interface.lean` | Joint variant of closed-form Born capstone. | none |
| `LF3_singlet_frequency_convergence_born_inner_joint` | `LF3/Interface.lean` | Joint variant of bra-ket Born capstone. | none |
| `PureSingletPreparation.weight_eq_P_st` | `LF3/PurePreparation.lean` | Composes `bridge_op_p` + the Busch-free `OP_p_at_jointEig_eq_P_st_direct`. | none |
| `OP_p_at_jointEig_eq_P_st` | `LF3/SingletProjective.lean` | Operational-stratum Born step (retained). | none (proved 2026-07-21) |

### LF2 (sector-conditional measure bridge and Born-weight wrapper)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `pushforward_epAction_invariant` | `LF2/MeasureBridge.lean` | `π_* μL` is `G`-invariant under the epistemic action. | none |
| `cp_measure_bridge` / `k_measure_bridge` | `LF4/Instance.lean` / `KahlerInstance.lean` | `π_* μL = c · μFS` (`c = 1`) on the concrete instances — the measure bridge, **axiom-free**. (The abstract `measure_bridge` + `invariant_measure_uniqueness` were removed 2026-06-04.) | none |
| `weights_sum_eq_one` | `LF2/Weights.lean` | Projective weights of a measurable partition sum to 1. | none |
| `born_quadratic` | `LF2/BornWrapper.lean` | `Tr(\|ψ⟩⟨ψ\| · \|φ⟩⟨φ\|) = ‖⟨ψ, φ⟩‖²`. | none |
| `pure_state_born_weights` | `LF2/BornWrapper.lean` | Density-form purity → `‖⟨ψ, φ⟩‖²`. | none |
| `pure_state_born_weights_of_certainty` | `LF2/EffectGleason.lean` | Strengthening from a purity (certainty) hypothesis. | none (proved 2026-07-21) |
| `lf1_weight_eq_projective_weight` | `LF2/Interface.lean` | LF1 ↔ LF2 measure-identity hinge. | none |
| `LF1_main_theorem_projective` | `LF2/Interface.lean` | LF1 frequency convergence on projective weight. | none |
| `effectProjFn_rankOne` | `LF2/EffectFn.lean` | Volume-ratio Born identity on the foundational effect function. | none |
| `LF2.PurePreparation.born_rank_one` | `LF2/Preparation.lean` | `OP.p (rankOneEffect φ) = ‖⟨ψ, φ⟩‖²` (chain critical path). | none (proved 2026-07-21) |
| `LF2.PurePreparation.born_rank_one_direct` | `LF2/Preparation.lean` | Same conclusion via direct Dirac integration; no Busch. | none |

### LF1 (deterministic repeated-trial frequency theorem)

| Theorem | File | Mathematical meaning | Axioms |
|---|---|---|---|
| `LF1_main_theorem_ae` | `LF1/MainTheorem.lean` | Empirical frequencies converge `μ`-almost surely to ontic weight under pairwise-independent trials. | none |
| `expectation_eq_weight` | `LF1/MainTheorem.lean` | `E[𝟙_O(X_n)] = O.weightReal`. | none |
| `prepMeasure_apply` | `LF1/Preparation.lean` | `μprep(A) = μL(A ∩ Ω0) / μL(Ω0)`. | none |
| `weight_eq_prepEvent_div` | `LF1/Outcomes.lean` | `O.weight = μL(O.prepEvent) / μL(Ω0)`. | none |
| `trialEvent_eq_comp_preimage` | `LF1/Trials.lean` | Deterministic structure: `T.trialEvent O n = (Φ ∘ X n)⁻¹(O.Ω)`. | none |

---

## Repository structure

```text
CsdLean4/
  LF1/                 -- ontic setup, preparation measure, outcomes, trials,
                       --   indicators, expectation bridge, LLN application,
                       --   LF1 main theorem and corollaries
  LF2/                 -- SectorData, measure bridge, weights, BornWrapper,
                       --   PhaseInvariance, EffectFn, Preparation, Interface
  LF3/                 -- Sign, DetectorSetting, pauliDot, Hamiltonian,
                       --   SectorSeparation, Projectors/, Singlet/,
                       --   ContextMap, SingletProjective, PurePreparation,
                       --   Interface
  LF4/                 -- Instance, KahlerInstance, SingletKahler,
                       --   SingleQubitKahler, SingletObservables, HardyKahler,
                       --   SpectralExpansion, SpectralCarving, SpectralVariance,
                       --   UncertaintyKahler, PauliRobertson, PauliDotRobertson,
                       --   OnticBorn, KahlerFlow, MomentMap/MomentMarginal/MomentRatio/
                       --   MomentBridge/MomentDirichlet/MomentBorn/MomentPushforward,
                       --   BornVolume, BornFS, BornFrequency(N), QubitBornFrequency,
                       --   POVMDilation/POVMVolume/POVMNaimark, BornRegionUncond,
                       --   BornRegionDisjoint, TypicalityForcing, ObservableFlow
  LF5/                 -- VonNeumannUnitary, MeasurementFlow, DilationFromFlow,
                       --   FlowBornFrequency, Capstone(Canonical), PointerOutcome,
                       --   SyndromeFlow, SyndromeOutcome (measurement dynamics)
  LF6/                 -- ForcedContextuality, SingletDeisolationFlow,
                       --   LocalDeisolationFlow, Decoherence (entangled de-isolation tier)
  Empirical/
    QM/                -- Pure QM-validity content (no CSD ontology)
      Algorithms/      -- Deutsch-Jozsa, Simon, Bernstein-Vazirani, swap test,
                       --   Hadamard test, Grover, Shor (core + recovery + factoring + random-a + capstone)
    CSD/               -- CSD volume-ratio readings (transport bundles) +
                       --   open-system 15-series (Einselection, QECDecoherence,
                       --   WeakMeasurement, QuantumZeno, ChannelCapacity)
    Metrology/         -- quantum sensing: Ramsey, QuantumFisher, Heisenberg
  Tests/
    AxiomAudit.lean    -- #guard_msgs regression suite (build-fails on drift)
    Examples.lean      -- LF1 coin-toss, LF2 Born-form edge cases, LF3 chain smoke
  Mathlib/             -- Cat-1: CSD-free helpers staged as Mathlib upstream candidates
                       --   (incl. QuantumInfo/ -- n-qubit register, Hadamard, QFT,
                       --   channels, trace distance; QEC/ codes;
                       --   Reversible/ -- reversible-arithmetic gate DSL + cost model,
                       --   ModAdd/ModMul/ModInv + Cuccaro stack, used by Shor)
  Basic.lean           -- Pkg.Basic convenience re-export
CsdLean4.lean          -- canonical top-level import (explicit module list)
specs/
  LF1-v1.01.{pdf,txt,plan.md}
  LF2-v1.00.{pdf,txt,plan.md}
  LF3-v1.00.{pdf,txt,plan.md}
  LF4-todo.md          -- items deferred from LF2 / LF3 to LF4
                       --   (observable correspondence closed; others remain)
  pre-LF4-plan.md      -- pre-LF4 execution log
  qm-empirical-tests.md -- QM empirical regression suite plan
  empirical-csd-bridge-plan.md -- CSDBridge architecture
AXIOMS.md              -- per-theorem axiom audit
CONVENTIONS.md         -- three-category framing (Cat-1 / Cat-2 / Cat-3)
BRIDGE-OBLIGATIONS.md  -- per-Empirical-CSD-bundle obligations ledger
PLACEHOLDERS.md        -- schema-mismatch acknowledgements
```
