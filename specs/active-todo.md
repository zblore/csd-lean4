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
| 18 | L5-a measure-and-correct primitive (amplitude model) | ECDSA | M | open (startable) | |
| 19 | L5-b ~2× cost accounting (Cost.meas) | ECDSA | S–M | open | #18 |
| 20 | L5-c Boolean↔amplitude bridge (THE wall) | ECDSA | L–XL | open | #18 |
| 21 | L5-d measurement-based adder + re-cost (gap ~10.5×→~5×) | ECDSA | M | open | #19,#20,#7 |
| 22 | L5-e DSL-extension posture decision | ECDSA | M | open | #18 |
| 14 | ECDSA L5 Gidney measurement adders (Tier-X umbrella) | ECDSA | XL | open | #7,#18–#22 |
| 7 | ECDSA step 2: run their Rust harness (USER action) | ECDSA (user) | S | open | |
| 16 | Debt D1c-1: structural Φ≠id into kSectorData (kFlow) | Foundations-debt | M | DONE | |
| 28 | D1c-2: physically-meaningful Φ (obsFlow Hamiltonian) into cpSectorData | Foundations-debt | S | DONE | |
| 29 | D1c-3 / A5-onramp: ergodic/mixing Φ whose unique invariant measure is μFS | Foundations-debt | L–XL | open | |
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

**D1c-3 / A5 onramp (#29).** The A5 gap is precisely that `obsFlow`/`kFlow` are periodic/non-mixing, so they
do not FORCE `μFS`. The onramp: an ERGODIC / MIXING `Φ` on ℂℙ^{N-1} (e.g. an irrational-rotation phase flow)
whose UNIQUE invariant measure is `μFS` — that is what makes typicality *derived* (the quantum
Liouville/equal-a-priori justification) rather than posited, and is where A5 (#17) actually starts. Also
proper D1c-3: `obsFlow` on the non-trivial-fibre `kSectorData` base (moves `π`).

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
