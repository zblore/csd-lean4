# Headline claim validation ledger

Review date: 2026-08-06; sign-off session S1 2026-08-20 (see below)  
Machine-readable source: `specs/validation-claims.tsv`

## Purpose

Lean checks that a proof term has its declared type. This ledger checks the separate question: whether
the declared type, definitions, hypotheses, and public description support the intended mathematical
or physical claim.

Statuses:

- `validated`: statement and intended claim align at the present review depth.
- `qualified`: correct under important scope or interpretation qualifications.
- `needs-change`: the public claim/API should be narrowed or strengthened.
- `specialist-review`: mathematically deep proof requiring independent domain proof review.

The TSV is canonical for automation. It records 58 headline claims, their defining modules, exact Lean
constants, load-bearing assumptions, an independent validation route, and any linked review finding.

## Admission criteria (defined 2026-08-13, Q17 — the census is now criteria-driven)

The original 30 rows were a hand-curated selection by the 2026-08-06 codex external-review
session — a defensible register, but with no stated admission rule, so "the 30" was an
artifact of one session's reading. A constant is now admitted as a headline claim when
**all four** hold:

1. **Terminal** — it is the strongest statement of its result chain in the corpus (the
   capstone, closure, or sharpest bound; never a lemma feeding a stronger landed statement).
2. **Claim-bearing** — the corpus cites it as delivering a named result (a ★★/★★★ BACKLOG
   strike, README/TOUR headline, or paper claim): something the programme would defend to an
   external reviewer as a *result*, not infrastructure.
3. **Pinned** — axiom-audited (foundational triple, or the deviation explicitly disclosed).
4. **Distinct** — not propositionally subsumed by an existing row; when a stronger form
   lands, the row is *replaced*, not duplicated (precedent: CL-031).

Census sources: the Headlines facade, ★★/★★★ markers in BACKLOG strikes and module
docstrings, and the necessity audit's named omissions. The ledger remains a curated
register, not an exhaustive census of the corpus's ~4,100 statements — but admission is
now a rule, and `check-validation-ledger.sh`'s known blind spot (it enforces consistency
of listed rows, not completeness of the list) is mitigated by re-running this census when
a tranche closes with starred headliners.

**Extension 2026-08-13 (CL-032 … CL-051, 20 rows, all `qualified`):** the necessity
audit's named strongest-direction omissions (`stone_continuous`, `no_exact_finite_ccr`,
the three `MeasurementConstraints` no-gos, `compositeAlgReconstruction`,
`posMeasure_noRecord_pointer`), the A7-faithful `qubitBorn`, the 2026-08-12/13 tranche's
starred headliners (derived coupling, DH-exact rate, entropy ledger, Shor-9 degeneracy,
the Lindblad master equation, LR velocity, vacuum clustering, the general-`N` third horn),
the Q18 conditioner conversions (`recordKernel_eq_transProb`,
`measure_eq_fubiniStudy_of_record_statistics_invariant`), and the two record-layer ★★
results that discharge earlier rows' known boundaries (`povm_sector_born` vs CL-026,
`pointer_luders_born_prep`). All entered as `qualified` with load-bearing posits named —
promotion to `validated` stays claim-by-claim sign-off, per the rules below. Necessity
classification of the extended set: `necessity-audit.md`, addendum 2026-08-13.

**CL-052 added 2026-08-13** (`c1_singlet_contextual_capstone`, qualified; Q19, author
sign-off same day): the **positive half** of the C1 separation — an explicit measurable
shared-context family on `(KSigma 4, kMuPsi)` reproduces the singlet (the full `P_st`
table at **every** context, hence the CHSH correlations) and no global CHSH assignment
is compatible with it. Until Q19 CL-031's reproduction hypothesis had no inhabitant;
this row supplies it, making the separation two-sided. The table-level reproduction is
deliberate: a correlation-only witness could carry degenerate marginals, and
"reproduces the singlet" would over-read it (the E-1 lesson applied in advance). CL-031
is retained as the general obstruction; the two rows are read together, existence +
no-go. Classification: INSTANTIATION (`necessity-audit.md` addendum).

**CL-058 added 2026-08-24** (`hasRaceProperty_iff_exists_expMeasure`, qualified; Q12-c2). The
classical competing-risks characterisation, absent from Mathlib: first-to-fire proportional to the
rate **iff** the waiting-time law is exponential. It closes `record-layer-plan.md` §3c, which until
now cited the literature. Admitted as terminal (the `iff` subsumes both directions), claim-bearing
(★★★ BACKLOG strike), pinned, and distinct.

`qualified`, on two counts that must travel with any statement of it. (i) `HasRaceProperty`
quantifies over the **number of clocks**; at a fixed number of outcomes `n` the race supplies only
`n−1` moments and finitely many moments determine nothing, so the exponential is forced *given that
one clock law serves every `n`* — the measurement-independence `sigma-fibre-contextuality.md`
commits to. (ii) It is **a posit removed, not a mechanism supplied**: the fibre law is no longer a
choice, but no dynamics carves the race cells, `Q12-d` stays blocked by `W1`, and neither
`DeIsolationInteraction` witness is dynamical.

## Current result

| Status | Count | Meaning |
|---|---:|---|
| Validated | 26 | No material claim mismatch found at current depth. |
| Qualified | 25 | Formally coherent, but assumptions or construction scope must accompany the claim. |
| Needs change | 1 | Concrete semantic/API mismatch recorded in the main review ledger. |
| Specialist review | 0 | All three commissioned audits (CL-005/CL-022+CL-023/CL-024) completed 2026-08-06. |

## Sign-off session S1 (2026-08-20, author-directed)

Authorised by the author in-session and executed claim by claim against the
promotion rules below; every touched row carries an `S1-2026-08-20` tag in the
TSV `finding` column naming its evidence or its remaining gap. Outcomes:

- **12 promotions to `validated`**, each on a named in-corpus artifact
  completing criteria 5–6: CL-003 (G1 transport theorems), CL-007
  (`ChoiConverse` as the independent CP characterisation), CL-020 (the
  CL-031 assumption-comparison work), CL-025 (`swap_luders_iff_calibrated`),
  CL-026 (boundary discharged by CL-050), CL-033 (two independently pinned
  trace facts + textbook comparison), CL-037 (the P2 instantiation
  `compositeArenaForced` freshly exercises the premises), CL-041 (the DH
  exact-coupling oracle), CL-043 (exhaustive blocks + structural lift),
  CL-048 (consumer chain), CL-049 (G4-uniqueness consistency), CL-052 (the
  table equality is itself an exhaustive finite check).
- **CL-027 needs-change → qualified**: the G5 decision (2026-08-06) had
  already resolved the API question; the status was stale.
- **17 rows confirmed `qualified`-by-design**: their qualification is the
  claim's permanent honest scope (e.g. CL-002's pairwise-not-full-iid,
  CL-028's cutoff scope, CL-044's CP gap), so `qualified` is their correct
  terminal status and the sign-off records exactly that.
- **12 rows left `qualified` pending real work**, each gap named in the TSV
  (CL-024's is the author hand-pass, G11); CL-011 stands `needs-change` as
  the MD-1 frontier (Q12).

The earlier in-session estimate "28 one-sign-off-away" was optimistic: it
counted the by-design rows as promotable. This pass does not — a permanent
scope qualification is not a missing signature.

**CL-011 REPLACED 2026-08-24** (author sign-off) — `CSD.LF4.born_frequency_convergence_N`
→ `CSD.RecordLayer.globalRecordClosure_born`, `needs-change` → `qualified`. **The ledger's only
`needs-change` row is now cleared, and it was cleared by a theorem that had been in the corpus since
July.**

CL-011 stood `needs-change` from finding F-03 because its outcome regions were
**preparation-indexed** (`bornRegion ψ'`), and S1 (2026-08-20) left it standing with the reason
"the MD-1 frontier, Q12". That reason was already wrong twice over. Q12 was the **dynamics** half of
MD-1, not the preparation-indexing half; and the preparation-indexing half had been closed on
2026-07-31 by `GlobalBasin`/`GlobalRecordClosure`. The ledger simply had not caught up, and Q12's
closure on 2026-08-24 made the stale pin visible.

`globalRecordClosure_born` discharges the defect **by construction rather than by argument**: the
record event `globalBasin (momentContext N) i` is literally the same set for every `ψ`, and only the
epistemic measure moves. Its own docstring names it *"`RecordLayerClosure.born_typicality`'s
successor, with the preparation-indexing removed"*. Replacement rather than a new row is admission
criterion 4 — *when a stronger form lands, the row is replaced, not duplicated* (precedent CL-031).

⚠️ `qualified`, **not** `validated`: the theorem's own docstring keeps the honest caveat, *"Still
kinematic: no `H_int(M)` produces these basins."* The preparation-indexing defect is fixed; the
kinematic scope is not, and that is the permanent honest scope of the claim. The necessity
classification is unchanged (SUFFICIENCY).

**S3 (2026-08-24) — two of the seven named-gap rows cleared, and one of the gaps was itself wrong.**

* **CL-030** (`landauer_bound`), sign/temperature convention check: **clean.** The statement matches
  Reeb–Wolf 2014 exactly (`ΔS ≤ βΔQ`, system entropy *decrease* against heat *absorbed by the
  bath*); `gibbsWeight = exp(−βx)/Z` is the standard convention and is cross-checked internally by
  `re_trace_mul_log_gibbs`; the signs are consistent on both sides. ★ **Finding:** the docstring says
  "at inverse temperature `β > 0`" while the signature carries **no positivity hypothesis** — and
  that is correct, because the inequality descends from `D(ρ_B'‖τ_B) ≥ 0`, which holds for any real
  `β`. The `β > 0` is a physical gloss, not a hypothesis. **Do not "fix" it by adding `0 < β`**; that
  would strictly weaken a correct theorem.
* **CL-029** (`vonNeumannEntropy_le_pinching`): ★ **the audit's own suggested check was circular.**
  It asked for an "independent relative-entropy derivation", but Klein's inequality
  `tr[ρ log ρ] ≥ tr[ρ log σ]` **is** nonnegativity of quantum relative entropy, and the corpus proof
  already runs on it — so a relative-entropy derivation would restate the proof rather than check it.
  Replaced with a genuinely independent route: pinching is the uniform mixture
  `P(ρ) = (1/N) Σₘ Zᵐ ρ Zᵐ*` over diagonal phase unitaries, so **concavity of `S` plus unitary
  invariance** gives the inequality with no Klein and no relative entropy.

* **CL-032** (`stone_continuous`), criterion 6: **done, by specialist proof review of the
  statement — which found a redundant hypothesis.** `hU0 : U 0 = 1` follows from `hgroup` and
  `hunit` alone (`U 0 = U 0 * U 0` by the group law at `(0,0)`; `U 0` is left-invertible by
  unitarity; cancel). The finding is *verified in Lean*, not asserted:
  `Matrix.StoneC1.apply_zero_eq_one`. So the statement carries four hypotheses where three suffice.
  ⚠️ `hU0` is **deliberately retained** — it is free at every call site (nothing outside its own file
  passes it) and keeps the hypothesis list reading as the standard four-part Stone statement. The
  redundancy is now in the theorem's own docstring so it cannot be mistaken for an oversight.

All three rows stay `qualified` — their load-bearing scope is unchanged; what was missing was the
recorded independent check, and that is what these supply.

**Follow-up S2 (same day):** the two S-sized outcomes executed. CL-006's named
API test landed as `POVM.weight_nonneg` and the row promoted; the four rows
left unconfirmed at S1 depth were read to promotion standard and all four
promoted — CL-034/035/036 on their textbook mechanisms with CL-047's seam
witness as the sharpness companion (and consumers for CL-035), CL-046 on the
exact propagator tables in its own module. Validated 21 → 26.

**CL-031 added 2026-08-10** (`no_compatible_global_chsh_assignment_realises_singlet`,
validated — hence Validated 8 → 9). It arrived through the C1 correction and
**replaces** a false claim: `LF3/ContextMap.lean` previously asserted that type
separation between `ContextIndexedOutcomeMaps` and `GlobalCHSHAssignment`
"carries the Bell-consistency content". Different structures give definitional
separation only, and the per-context domains in fact *prevented* the no-go from
being stated. CL-031 is the theorem that states it, on the shared domain C1
posits. Scope: four CHSH settings only, so it does **not** subsume CL-020.
See `specs/publication-errata.md` E-1 and `docs/C1-FORMAL-SUPPORT.md`.

(Counts updated 2026-08-06 after same-day resolution of CL-003 (G1 discharge, -> qualified) and the
three specialist audits with author sign-off: CL-005 -> validated; CL-022, CL-023, CL-024 ->
qualified. Audit payloads summarized in `audit-sweep-plan.md`; residue rows in `BACKLOG.md` SG.)

## Highest-priority validations

(Original five priorities, status as of 2026-08-06:)

1. `CL-003` — DONE (G1 discharge: transport theorems consume `bridge_eq`; mutation guard requires them).
2. `CL-011` — standing: the preparation-indexed vs context-fixed distinction is the MD-1 frontier
   (qubit done; general-`N` per `sigma-fibre-contextuality.md`).
3. `CL-023` — DONE (audit verified the reduction + repo-wide wording sweep; hDPI discharge itself
   stays the E2 backlog row).
4. `CL-027` — DECIDED (G5: index-style capstone names kept, rename on-touch; docstrings carry the
   framing).
5. `CL-024`/`CL-005`/`CL-022` — audits completed 2026-08-06 and signed off. Remaining residue:
   the human hand pass on the five named Wigner tactic blocks + optional uniqueness formalization
   (BACKLOG G11).

## Required evidence for promotion to validated

A claim may move to `validated` only when:

1. its Lean module and constant still exist and compile;
2. `#print axioms` has only the accepted foundational footprint;
3. every load-bearing assumption is identified;
4. non-vacuity is established by an inhabitant or consistency witness;
5. the statement is compared with an authoritative mathematical reference;
6. at least one independent check is completed (alternative proof, exhaustive finite model, numerical
   oracle, or specialist proof review);
7. the README/spec wording is no stronger than the exact Lean statement.

## Control boundary

The automated checker validates ledger structure and declaration linkage. It cannot certify the human
judgments in the `status`, `load_bearing`, or `independent_check` columns. Those remain review evidence
and must be signed off claim by claim.
