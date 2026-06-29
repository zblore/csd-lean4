# Active TODO — CSD session work queue (persistent)

**Purpose.** Durable copy of the session task list so it survives session loss. If the
in-memory task list is gone, re-seed from the table below (each row → a task; keep the
Category / Complexity / Blocked-by columns). Last updated 2026-06-29.

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
| 30 | AND-based adder primitive (Boolean DSL; fresh per-carry AND temporary) — prereq for measurement re-cost | ECDSA | L | open | |
| 31 | Localized amplitude lift of the AND-uncompute block (denote↔toEuclideanLin, restricted) | ECDSA | L–XL | open | #30 |
| 21 | L5-d measurement-based adder + re-cost (gap ~10.5×→~5×) — DEFERRED pending #30+#31 | ECDSA | M | open | #30,#31,#7 |
| 22 | L5-e DSL-extension posture decision | ECDSA | M | open | #18 |
| 14 | ECDSA L5 Gidney measurement adders (Tier-X umbrella) | ECDSA | XL | open | #7,#18–#22 |
| 7 | ECDSA step 2: run their Rust harness (USER action) | ECDSA (user) | S | open | |
| 16 | Debt D1c-1: structural Φ≠id into kSectorData (kFlow) | Foundations-debt | M | DONE | |
| 28 | D1c-2: physically-meaningful Φ (obsFlow Hamiltonian) into cpSectorData | Foundations-debt | S | DONE | |
| 29 | A5 onramp: typicality forced by symmetry + single-flow obstruction (DONE) | Foundations-debt | L | DONE | |
| 32 | A5 onramp follow-up: conserved-quantity CONTINUUM of invariant measures (DONE) | Foundations-debt | M | DONE | |
| 33 | A5: obsFlow_not_ergodic — momentMap·i is a non-constant conserved observable (closes the obstruction story) | Foundations-debt | S–M | open | |
| 17 | A5: derive sector (π,G) + FS typicality from dynamics | Foundations-debt | XL | open | #29 |
| 5 | LF6 general-N entangled tier | LF6 | L | open | |
| 15 | Open-system / decoherence empirical targets | Empirical | L | open | |
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

Per-field-op constant levers (L6/L1/L3) exhausted. Remaining: carry-clean adder (the
`30n²→~2n²` dirty-carry gap) and the Tier-X L5 measurement fork (#14, gap → ~5× but needs
amplitude semantics). Parity gated on L5 + step #7 (user harness).

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

1. **Einselection / pointer-basis (M, RECOMMENDED first).** `decohereReduced` already yields the
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

## L5-c scoping probe verdict (2026-06-29) — WALL

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
