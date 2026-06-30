# Active TODO — CSD session work queue (persistent)

**Purpose.** Durable copy of the session task list so it survives session loss. If the
in-memory task list is gone, re-seed from the table below (each row → a task; keep the
Category / Complexity / Blocked-by columns). Last updated 2026-06-30.

**Complexity key:** S = single step · M = one expert tranche · L = multi-tranche · XL =
research-frontier / infrastructure gap.

## Task table

| # | Task | Category | Cx | Status | Blocked by |
|---|---|---|---|---|---|
| 1 | LF6-A.3 local product de-isolation flow | LF6 | M | DONE | |
| 3 | LF6-B.1 decoherence / partial-trace (D1b) | LF6 | M | DONE | |
| 6 | LF6-A.2 contextuality corollary | LF6 | S | DONE | |
| 8 | LF6-A.3 flow-realises-dilation lemma | LF6 | S | DONE | |
| 9 | LF6-B.2 purity-drop witness | LF6 | M | DONE | |
| 11 | ECDSA L6 safegcd inversion (dominant) | ECDSA | L | DONE | |
| 12 | ECDSA L1 Karatsuba multiply | ECDSA | M | DONE | |
| 13 | ECDSA L2 windowed Fermat (comparison) | ECDSA | S | DONE | |
| 10 | ECDSA L3 shared-partial-product squaring | ECDSA | M | DONE | |
| 2 | ECDSA L1–L6 (umbrella) | ECDSA | — | open | #14 |
| 18 | L5-a measure-and-correct primitive (amplitude model) — GREEN LIGHT: measurement-based uncompute IS verifiable in Lean | ECDSA | M | DONE | |
| 19 | L5-b ~2× cost accounting + operator↔list link | ECDSA | S–M | DONE | |
| 20 | L5-c Boolean↔amplitude bridge — SCOPING DONE, verdict WALL (see below) | ECDSA | L–XL | scoped (wall) | |
| 30 | AND-based adder primitive (Boolean DSL; fresh per-carry AND temporary) — DONE (the L5-d attachment point) | ECDSA | L | DONE | |
| 31 | Localized amplitude lift of the AND-uncompute block (denote↔toEuclideanLin, restricted) — DONE: L5-c wall closed at CELL granularity (MeasurementUncomputeLift.lean) | ECDSA | L–XL | DONE | #30 |
| 21 | L5-d measurement-based adder re-cost — DONE: adder Toffolis 6n→3n (n=256: 1536→768), aggregated from 3n #31-proven-equivalent blocks (MeasurementAdder.lean); n-fold amplitude correctness WALLED (gadget non-permutation; QReg 3⊗QReg(m−3) tensor factor); SCORE still gated on adder-swap-through-point-addition + #7 | ECDSA | M | DONE | #7 |
| 22 | L5-e DSL-extension posture decision | ECDSA | M | open | #18 |
| 35 | Minimal 1-AND-per-carry Gidney adder (~n Toffoli, free measurement uncompute) — the REAL Tier-X score-lever prerequisite; #30/#21 are a proof-of-concept attachment point, not competitive (6n→3n > 2n Cuccaro) | ECDSA | L | open | |
| 14 | ECDSA L5 Gidney measurement adders (Tier-X umbrella) — score lever ONLY after #35 + pervasive O(n²) mult/inverter application | ECDSA | XL | open | #35,#7,#22 |
| 7 | ECDSA step 2: run their Rust harness (USER action) | ECDSA (user) | S | open | |
| 16 | Debt D1c-1: structural Φ≠id into kSectorData (kFlow) | Foundations-debt | M | DONE | |
| 28 | D1c-2: physically-meaningful Φ (obsFlow Hamiltonian) into cpSectorData | Foundations-debt | S | DONE | |
| 29 | A5 onramp: typicality forced by symmetry + single-flow obstruction (DONE) | Foundations-debt | L | DONE | |
| 32 | A5 onramp follow-up: conserved-quantity CONTINUUM of invariant measures (DONE) | Foundations-debt | M | DONE | |
| 33 | A5: obsFlow_not_ergodic — momentMap·i is a non-constant conserved observable (closes the obstruction story) | Foundations-debt | S–M | DONE | |
| 17 | A5: derive sector (π,G) + FS typicality from dynamics | Foundations-debt | XL | open | #29 |
| 5 | LF6 general-N entangled tier | LF6 | L | open | |
| 15 | Open-system / decoherence empirical (umbrella; 15a einselection DONE) | Empirical | L | 15a, 15b, 15c DONE; 15d–e open | |
| 25 | 15c weak/unsharp measurement — DONE: unsharp POVM weakEffect±(η)=½(I±ησ), no-meas(η=0)↔projective(η=1) interpolation, partial-info witness, FULL FS-volume reading on ℂℙ³ Naimark dilation (Gleason-free uncond engine); continuous-measurement flow D1-gated (WeakMeasurement.lean) | Empirical | M | DONE | |
| 24 | 15b QEC-as-decoherence — DONE: error = K2 bit-flip CHANNEL + Stinespring origin + in-code correction (recoverⱼ∘errorⱼ=id on encoded density, one space); ontic Σ-volume origin gated to D1 (QECDecoherence.lean) | Empirical | M | DONE | |
| 34 | 15a follow-up — DONE: degeneracy boundary (p₀=p₁ ⇒ ½I basis-invariant, einselection FAILS; iff `decohere_hadamard_offDiag_ne_zero_iff`) + general-N einselection (`einselectionN`, `decohereReducedN_acts_nontrivial`); ontic origin D1-gated (Einselection.lean) | Empirical | M | DONE | |
| 4 | Metrology A4: decoherence (Lindblad) | Metrology | XL | open | |

Per-area plans: [`lf6-plan.md`](lf6-plan.md), [`ecdsafail-optimization-plan.md`](ecdsafail-optimization-plan.md),
[`metrology-plan.md`](metrology-plan.md), [`INDEX.md`](INDEX.md).

## ECDSA.fail score ledger (point addition, qubit×Toffoli, lower wins)

| stage | Toffoli | score | leaderboard gap |
|---|---|---|---|
| step 3 (Fermat) | 676,880,936 | 1,910,158,001,392 | ~1217× |
| + L6 safegcd | 7,896,616 | 22,284,250,352 | ~14× |
| + L1 Karatsuba | 5,913,868 | 16,688,935,496 | ~10.6× |
| + L3 squaring | 5,831,948 | 16,457,757,256 | ~10.5× |
| leaderboard best | ~1,360,000 | ~1,566,720,000 | 1× |

Per-field-op constant levers (L6/L1/L3) exhausted. Current ~5.83M Toffoli/point-add is
**inversion-dominated**: safegcd `60n²+28n` ≈ 3.94M at n=256 (~67%); mults/squarings/adds the
rest. Standalone adders are an O(n) sliver of an O(n²) total — which is why the L5-d adder
re-cost barely moves the score.

**HONESTY CORRECTION (2026-06-30): L5-d as built is NOT a score lever.** The #30 AND-based
adder is `6n` Toffoli (`andCarryCell` = 3 CCX/carry, fresh-ancilla majority cell), ~3× a
Cuccaro adder (~2n ≈ 512 at n=256). After the measurement re-cost it is `3n` = 768, STILL
larger than Cuccaro's ~2n. So swapping #30 into the point-addition RAISES the score. #30/#21
are the measurement-path proof-of-concept (the `andInput`-shaped uncompute attachment point),
not a competitive adder. The genuine Tier-X score lever needs (i) a MINIMAL 1-AND-per-carry
Gidney adder (~n Toffoli, free uncompute → beats Cuccaro), then (ii) pervasive application
inside the O(n²) multiplier/inverter (where the measurement uncompute halves the dominant
cost). The earlier "gap → ~5×" was aspirational (assumed that minimal-adder programme), NOT
what #30/#21 deliver. Parity still gated on that unbuilt programme + step #7 (user harness).

## #16 — D1c plan (thread genuine Φ through concrete SectorData)

**Debt.** The concrete instances hard-code `Φ := id`: `kSectorData` (`LF4/KahlerInstance.lean:107`),
`cpSectorData` (`LF4/Instance.lean:64`). The flow lives in `SectorData.toOntic.Φ` (the LF1
`OnticSetup.Φ`); the load-bearing law is `hΦ_pres : MeasurePreserving Φ μL μL` (carried as
structural payload — LF1/LF2/LF3 proofs only use `measurable_Φ`).

**Asset (ready).** `LF4/KahlerFlow.lean` already has `kFlow sh : (p,t) ↦ (p, sh+t)` on
`KSigma N = ℂℙ^{N-1} × T²`, with `kFlow_measurePreserving`, `kFlow_ne_id` (sh≠0),
`kFlow_preserves_rays` (`π∘kFlow = π`), and `kFlow_frequency_convergence` (LF1 typicality
non-vacuous on the **evolved** states). But `kFlow` is NOT wired as any SectorData's `Φ`.

**D1c-1 (tractable, M — recommended first).** Build `kSectorData'` / a `kOnticSetup` variant
with `Φ := kFlow sh` (sh≠0) instead of `id`. Proof obligations, nearly all already proven:
- `Φ` measurable — `kFlow` is `id × (sh + ·)`, measurable.
- `hΦ_pres` = `kFlow_measurePreserving` (exists verbatim).
- SectorData G-action coherence (`hμL_inv`, equivariance `π∘onticAction = epAction∘π`) is
  about `onticAction`, NOT `Φ`, so it is unaffected; `kFlow_preserves_rays` confirms `Φ`
  commutes with the base/π structure.
- Non-vacuity: lift `kFlow_frequency_convergence` so the LF1/LF2 chain on `kSectorData'` is
  genuinely about a moving flow (`kFlow_ne_id`).
Result: a concrete SectorData carrying a genuine measure-preserving `Φ ≠ id`, discharging the
headline "every concrete instance has Φ=id" caveat for the Kähler instance.

**D1c-1 honest scope.** `kFlow` is a FREE T²-fibre translation — a genuine measure-preserving
`Φ≠id`, but trivial dynamics: not a measurement/de-isolation flow, not a symplectic/Hamiltonian
flow derived from the Kähler form. So D1c-1 discharges the STRUCTURAL debt (the instance carries
non-trivial dynamics), not the physical content.

**D1c-1 DONE 2026-06-29** (`LF4/KahlerFlow.lean`, self-verified, foundational-triple): `kOnticSetupFlow`
(= `kOnticSetup` with `Φ := kFlow sh`, `hΦ_pres := kFlow_measurePreserving`) + `kSectorDataFlow` (G-action
fields reused verbatim — none touch `Φ`) + `kSectorDataFlow_phi_ne_id` (instance's `Φ ≠ id`),
`_phi_measurePreserving`, `kSectorDataFlow_frequency_convergence` (LF1 typicality through the instance's
own `Φ ∘ sample` → `kMuL` volume, non-vacuous). Structural `Φ=id` debt discharged for the Kähler instance.
3 AxiomAudit pins. `cpSectorData` still `Φ=id`.

**D1c-2 DONE 2026-06-29** (`LF4/ObservableFlow.lean`, self-verified, foundational-triple): `cpSectorDataFlow`
= `cpSectorData` with `Φ := obsFlow lam t` (a diagonal-phase `e^{itÂ}` observable/Hamiltonian flow on the
actual Fubini–Study Kähler base ℂℙ^{N-1}, MOVING superposition rays — strictly stronger than D1c-1's
ray-fixing fibre translation), `hΦ_pres := obsFlow_measurePreserving`; `cpSectorDataFlow_phi_ne_id`,
`_phi_measurePreserving`, `cpSectorDataFlow_frequency_convergence` (LF1 via `freq_tendsto_of_iid`). 3 pins.
Honest: a single observable's PERIODIC phase flow — NOT ergodic/mixing, so A5 still untouched.

**A5 onramp (#29) DONE 2026-06-29** (`LF4/TypicalityForcing.lean`, auditor-SOUND, foundational-triple).
The naive "single ergodic flow forcing μFS" is MATHEMATICALLY OBSTRUCTED (a one-parameter unitary flow on
ℂℙ^{N-1} has torus orbit-closures + fixed basis rays). The honest content instead:
- (A) `fubiniStudy_forced_by_symmetry`: any U(N)-invariant probability (typicality) law on the sector IS
  μFS (one-line reuse of the axiom-free `invariant_measure_uniqueness_cpn`). So Born = FS-volume is DERIVED
  from the sector symmetry G, CONDITIONAL on positing G-invariance of the typicality law.
- (B) `obsFlow_not_uniquely_ergodic` (the honest negative, genuine new content): `obsFlow` fixes the
  eigenstate rays, so `δ_{[e₀]}` is invariant and ≠ μFS (distinctness via a swap-unitary + FS's
  U(N)-invariance) — TWO distinct invariant probability measures, so a single ontic flow does NOT force
  μFS. This is WHY D1c-1/2's single-flow instances do not discharge A5.
- `a5_onramp` capstone conjoins (A)+(B). HONEST: A5 is NOT closed; typicality is forced by the SYMMETRY
  (not a flow); the residual A5 primitive is G=U(N) ITSELF, reducing to D1 (deriving the U(N)-symmetry of
  the ontic dynamics from the substrate — the deepest open content). Nothing claimed about deriving G.
Follow-up #32: strengthen (B) to a continuum of invariant measures via the moment-fibre conserved
quantities (`momentMap ∘ obsFlow = momentMap`). The genuine A5/D1 frontier beyond: the entangled
de-isolation tier (Bell-forced non-locality), where G could begin to be derived rather than posited.

(superseded:) The fuller D1c-2 is threading the LF5/LF6 de-isolation/measurement `Φ_vN`
(needs the SectorData on the dilated space).

**Relation to A5 (#17).** D1c (Φ≠id) is necessary-but-not-sufficient for A5 (deriving (π,G) +
FS typicality from the dynamics). A5 additionally needs the flow to be ergodic/mixing so the FS
measure is FORCED (the quantum Liouville/equal-a-priori justification). D1c-1 is the structural
foothold; the flow choice in D1c-2 is what an A5 ergodicity argument would build on.

## #15 — open-system empirical targets: next-tranche scoping

LF6-B gives `decohereReduced` (the dephasing channel), `Channel`, `PartialTrace`,
`decoherence_dephases` (→ Born diagonal mixture), `_offdiagonal_vanish`, the purity drop (B.2).
Candidate first tranches, by tractability:

1. **Einselection / pointer-basis (M, DONE 2026-06-29 — `Empirical/CSD/Einselection.lean`).** Witness:
   `(qmH · decohereReduced ψ · qmH) 0 1 = (p₀−p₁)/2` (computed); `decohere_not_diagonal_in_rotated_basis`
   (off-diag ≠ 0 for `p₀≠p₁`); `einselection` capstone (diagonal in `{e_j}`, off-diag `3/2` in the
   Hadamard rotation). Decoherence is basis-SELECTIVE; the pointer basis is the de-isolation's context
   basis, contrasted honestly with #29's basis-covariant FS typicality. Follow-up #34: degeneracy boundary
   (`p₀=p₁ ⇒ scalar·I`, every basis diagonal) + general-N. (original scoping:) `decohereReduced` already yields the
   diagonal Born mixture IN THE MEASUREMENT BASIS — the pointer basis IS the einselected basis.
   Tranche: prove decoherence selects that basis as the preferred one — coherences vanish in the
   `e_j` basis (have B.1) but PERSIST in a generic rotated basis (the new content: the reduced
   state is NOT diagonal in a rotated frame, so the basis is genuinely selected, not arbitrary).
   Directly on the B.1/B.2 machinery, no new infra. Zurek einselection, the "why a preferred
   basis" foundational content.
2. **QEC-as-decoherence (M–L).** Connect LF5-G's syndrome readout to the error channel
   (`bitFlipChannel` / `Channel` + `PartialTrace`): the error channel as system→environment
   decoherence, syndrome extraction as partial de-isolation. Reuses LF5-G + the Channel branch.
3. **Weak / continuous measurement (M–L).** Partial de-isolation (a coupling-strength parameter),
   gradual decoherence interpolating identity↔full dephasing. New infra: parameterised weak
   coupling.
4. **Quantum Zeno (M–L).** Repeated de-isolation freezing evolution — needs the weak/partial
   coupling from (3) plus iteration.
5. **Channel capacities (L).** The de-isolation channel's classical/quantum capacity — needs the
   K1 entropy machinery + capacity definitions.

Recommended order: 1 (einselection, cheapest + most foundational) → 2 (QEC-as-decoherence) →
3/4 (weak/Zeno) → 5 (capacities).

## FRAMING CORRECTION (2026-06-29, per user / papers A & B): typicality is forced by the LLN, NOT ergodicity

CSD forces **typicality** (frequencies → ontic volume weights) by the **law of large numbers** (LF1,
`LF1_main_theorem_ae` / `freq_tendsto_of_iid`, over repeated i.i.d. preparations) — papers A & B. There is
NO time-average / Birkhoff / single-flow-ergodicity hypothesis in the forcing. Earlier A5-onramp docs
(below, #29/#32/#33) used an ergodicity framing imported from stat mech; that is the WRONG mechanism.
Re-classification of the onramp results (the theorems are correct; only the framing was off):
- **#29 `fubiniStudy_forced_by_symmetry` is a MEASURE-CHARACTERISATION, not a forcing.** FS is the unique
  U(N)-invariant measure → it is the symmetry-CANONICAL measure to sample from on the sector. It bears on
  the measure CHOICE; the LLN then forces frequencies to its volume ratios. NOT "typicality forced by
  symmetry."
- **#32/#33 are honest NEGATIVES about the single-flow Birkhoff (time-average) route — which CSD does NOT
  use.** They show you cannot shortcut typicality via one flow's ergodicity (conserved Born coordinates
  block it), which REINFORCES that the LLN/i.i.d. route is the right one. They are not an obstruction to
  CSD's typicality (there is none — the LLN does the forcing).
Net: typicality-forcing is SETTLED (LLN, A&B). Measure-choice is symmetry-canonical (#29). The A5 residue
is just the SECTOR/SYMMETRY origin = G-from-D1; typicality-forcing is NOT part of the residue.

### Byproducts of the (mis-framed) ergodicity exploration — KEEP (they were net-positive)

The ergodicity framing was wrong, but the WORK yielded three durable things:
1. **The negative results JUSTIFY the LLN route (not just decline ergodicity).** #32/#33 prove a single
   one-parameter unitary flow CANNOT be μFS-ergodic (the Born coordinates are constants of motion; orbit
   closures are tori, real-dim ≤ N−1 inside the 2(N−1)-dim sector). So CSD's LLN/ensemble route is FORCED,
   not a stylistic choice.
2. **Individual-vs-ensemble typicality — a genuine D1 constraint.** The LLN gives ENSEMBLE typicality
   (many fresh preparations). An ergodic flow would give the stronger SINGLE-TRAJECTORY / individual-system
   account (one system's time-average self-averages to Born, Boltzmann's actual ergodic hypothesis). #33
   shows the single-trajectory account is BLOCKED under unitary dynamics. CONSTRAINT FOR D1: any
   individual-system Born account must come from genuinely mixing — i.e. NON-UNITARY / open-system or
   entangled de-isolation — dynamics, never unitary time-evolution. (Paper-worthy: A/B/D — flag for the
   user; do not touch preprints.)
3. **Reusable framing-independent lemmas** (in `LF4/TypicalityForcing.lean`): `map_withDensity_of_conserved`
   (reweighting an invariant measure by a conserved quantity preserves invariance — general Mathlib-grade)
   and `fubiniStudyMeasure_pos_of_isOpen` (FS has FULL SUPPORT: every nonempty open set has positive
   measure — directly useful for any "generic ψ" / open-dense genericity argument across the corpus).

## L5-c wall CLOSED at cell granularity (2026-06-30, #31)

`CsdLean4/Empirical/QM/MeasurementUncomputeLift.lean` (auditor-SOUND, foundational-triple, no busch).
The L5-c "no gate-lift" obstruction (1, below) is closed FOR THE SINGLE AND-uncompute block by staying
in L5-a's `B3 = Fin 3 → Fin 2` permutation-matrix representation — NO `Fin 8`/`qmToffoli` reindex (that
ill-typing was exactly the wall). Headlines, all computed not asserted:
- `andUncompMat_lifts_denote` — the `B3` unitary acts on basis states exactly as the Boolean Toffoli
  `denote (andUncompute 0 1 2)` (modulo an explicit, round-tripping `Bool↔Fin 2` recast). The localized
  gate-lift.
- `andUncompMat_uncomputes` — the unitary deterministically uncomputes the AND on the `andInput` subspace
  (`toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0`).
- `andUncompute_measureUncompute_agree_on_block` / `..._same_data` — the unitary block and the L5-a
  measurement gadget land in the SAME `uncomputedData c ·` family (same data amplitudes `c`; ancilla `0`
  deterministic vs `m` measured; the `_same_data` form clears the `(√2)⁻¹` so `c` is literal in both).
  So `measureUncompute` is a PROVEN-equivalent replacement on this block.
- `andUncompute_measurement_saving` — 1 vs 0 Toffoli, on the proven-equivalent block (not a count over an
  unverified swap; the auditor confirmed this is the real saving, not 0-vs-0/miscount).

Honest scope: CELL granularity. Trusted base grows by this localized lift. NO circuit-level re-cost and
NO ECDSA score change here. DEFERRED: #21 (L5-d) threads the block-replacement through the AND-based
adder's `n` AND-uncomputes for the circuit re-cost (gap ~10.5×→~5×); the watch-point (auditor) is whether
the per-block "same data modulo ancilla/scalar" composes coherently across the `n`-fold tensor embedding
(stay in the per-block `B3` factor, identity elsewhere — the analogous sidestep). Also gated on #7 (harness).

## L5-c scoping probe verdict (2026-06-29) — WALL [superseded at cell granularity by #31 above]

The measurement-based AND-uncompute (L5-a/b, verified as an amplitude gadget, `measureUncompute_cost`:
0 vs 1 Toffoli per AND) is currently STRANDED in the amplitude model with no attachment point to corpus
arithmetic. Two obstructions:
1. **No gate-lift.** `denote : (Fin n → Bool) → (Fin n → Bool)` (Boolean permutation) and the amplitude
   unitaries (`qmToffoli : Matrix (Fin 8)`) are ill-typed against each other: bridging needs a `Bool≃Fin 2`
   recast, per-gate `Equiv.Perm (Fin n → Fin 2)` packaging, and a general amplitude-lift `denote c ↔
   toEuclideanLin (∏ permMatrix)` (a real 2ⁿ-dim isometry, foundational but a nontrivial induction over
   the gate list). The clean `Equiv.Perm.permMatrix` pattern exists (LF5 `vnUnitary_mulVec_single`) but is
   generic — it touches neither `qmToffoli` nor `denoteGate`.
2. **Decisive: no AND-ancilla to discharge.** The corpus Cuccaro adder is IN-PLACE carry-restoring (`uma`
   uncomputes the carry UNITARILY); there is no fresh `|0⟩`-initialised AND temporary. Gidney's gadget
   needs an AND-based adder (one fresh AND ancilla per carry, later measured away). So even with a perfect
   gate-lift, `measureUncompute` has nothing to attach to.

**Consequence: L5-d is NOT a re-cost.** The Tier-X parity path requires NEW INFRASTRUCTURE:
- **#30** an AND-based adder primitive in the reversible DSL (a Boolean task, no amplitude bridge: allocate
  + compute + later uncompute a per-carry AND temporary, so an `andInput`-shaped state appears at an
  uncompute point);
- **#31** a LOCALIZED amplitude lift of just that AND-uncompute block (not a full general-circuit `denote`
  lift), bridging the single block via the `permMatrix` pattern;
- then **#21 (L5-d)** re-costs the AND-based adder with `measureUncompute` replacing the AND-uncompute Toffoli.

Honest L5 status: measurement-based uncompute is VERIFIED as an amplitude gadget (L5-a/b done) with a real
per-gadget Toffoli saving; APPLYING it to corpus arithmetic for a score is gated on #30 + #31 — genuine new
construction (the trusted base grows), NOT a wrapper. This is the user-gated fork's true cost, now known.
