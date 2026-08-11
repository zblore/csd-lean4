# C1 correction: formal closure report

Work-order item 36. Written 2026-08-10.

**Starting HEAD** `f5384515724754d4035d9feb2326e11e1ce8afb9`
**Ending HEAD** `612d9ecd4f640e59ce6ea1ef1bf35a4eb8fd9414`

Ten commits, in three gated phases with a stop for review after each.

> *Closed* means a theorem exists where one was required, or a claim was
> explicitly corrected to record that no theorem establishes it. Documentation
> edits alone close nothing.

## The two headline findings

**Item 7 was FALSE, not merely unproved.** `nudgedSinglet a b` is the vector
`(√P_st)_{s,t}` — real, non-negative, every relative phase discarded. Local
unitaries preserve Schmidt spectra and `ψ⁻` is maximally entangled; at `a ⊥ b`
all four `P_st = ¼`, so the object is `½(1,1,1,1)`, a **product state**. It is a
local-unitary image of the singlet only at `a·b = ±1` — exactly the endpoint set
`hgen` excluded. Cause: `singletJointEig` divides by the real `√P_st`, fixing
each basis vector's phase by projecting `ψ⁻` itself, giving four independent
phases where a product unitary supplies only separable ones.

**Item 12 dissolved rather than being solved.** The same division was the sole
source of `hgen`. Removing it to repair locality removed the genericity
restriction at the same time; the two problems had one cause. The volume engine
was never implicated (`povm_born_eq_dilated_volume_uncond` is hpos-free).

## Items

| # | Outcome |
|---|---|
| 1 | **Closed.** Landed early, forced by the new guard. |
| 2–5 | **Closed.** Shared-domain interface, compatibility, obstruction, non-vacuity. |
| 6 | **Closed by not needing an adapter** — reduced directly to `lhvCHSH_abs_le_two`, per fidelity-over-reuse. |
| 7 | **Closed as a CORRECTION.** The claim was false; `localNudge` is the repair. |
| 8 | **Closed.** `localMeasurementChain_factorises`. |
| 9 | **Closed.** Capstone conjunct 3 qualified; three-way locality distinction added. |
| 10 | **Closed.** `hgen` scope stated wherever the claim appears. |
| 11 | **Superseded.** The local route has no `hgen` to discharge. |
| 12 | **Closed.** `a·b = ±1` now covered. |
| 13–15 | **Closed.** Measure-level predicate, kernel theorem, marginal-volume lift. |
| 16 | **Recorded OPEN.** BACKLOG row; no axiom added. |
| 17–19 | **Closed.** Stale A.2/A.3 status; the false claim in two further places. |
| 20 | **Closed.** SO-1 preserved as an upstream input throughout. |
| 21 | **Closed, swept clean.** No ℂℙ¹ used for the joint two-qubit space. |
| 22 | **Closed.** Locality scoped to the finite dilated construction. |
| 23–24 | **Closed in Phase 0.** See below. |
| 25 | **Recorded as erratum E-1**; the manuscript is not editable from here. |
| 26–28 | **Closed.** Spec sync, claim status, `docs/C1-FORMAL-SUPPORT.md`. |
| 29 | **Closed.** `CITATION.cff` extended; **no tag created** — author decision. |
| 30 | **Closed, swept clean.** No LF3 → LF6 cycle; new modules in the root. |
| 31 | **Closed.** Sweep found one residual the guard missed; pattern extended. |
| 32, 33, 34 | **Honoured throughout** (constraints, not tasks). |
| 35 | **Closed.** Both targets clean, zero warnings, nine guards green. |

## Files

**Added (9):** `LF3/{Spinor,SharedContextMap,OperationalNoSignalling}.lean`,
`LF6/{NudgeLocality,C1BellConsistency}.lean`, `docs/C1-FORMAL-SUPPORT.md`,
`specs/{c1-correction-plan,publication-errata}.md`,
`scripts/check-claim-provenance.sh`. **Modified:** 12.

## Theorems added

Signatures verbatim from Lean; every one reports exactly
`[propext, Classical.choice, Quot.sound]`.

* `CSD.LF3.spinProj_eq_outer` — `spinProj s a i j = spinor s a i * star (spinor s a j)`
* `CSD.LF3.wingBasisUnitary_mem_unitaryGroup`
* `CSD.LF3.jointSpinProj_eq_outer`, `spinor_normSq`, `two_mul_spinProj_eq_raw_outer`
* `CSD.LF6.localNudge_born` — `‖(localNudge a b) (k,l)‖ ^ 2 = P_st a b (signOfFin k) (signOfFin l)`
* `CSD.LF6.localMeasurementChain_factorises` —
  `(V_A ⊗ V_B) * (wingPairUnitary a b)ᴴ = (V_A * U_Aᴴ) ⊗ (V_B * U_Bᴴ)`
* `CSD.LF6.localDeisolation_pointer_volume_local` — **no `hgen`**
* `CSD.LF6.no_compatible_global_chsh_assignment_realises_singlet` —
  `Measurable S → Compatible S G → ReproducesSingletAtCHSH μ S → False`
* `CSD.LF6.compatibleGlobalCHSH_nonvacuous`
* `CSD.LF3.singlet_operational_no_signalling`, `singlet_marginals_eq_half`
* `CSD.LF6.localDeisolation_{A,B}_marginal_volume_eq_half`,
  `localDeisolation_no_signalling_{A,B}`
* `CSD.LF6.localNudgeVec_{coord_normSq,born,norm,ne_zero}`

## Status of each obligation

* **Endpoint `a·b = ±1`** — **CLOSED** on the local route; retained on the
  original `localDeisolation_pointer_volume`.
* **Nudge locality** — **CLOSED as a correction.**
* **Full-chain locality** — **CLOSED**, scoped to the finite dilated
  construction. Not a subsystem decomposition of arbitrary `Σ`.
* **C1 Bell adapter** — **CLOSED**, four CHSH settings only, reduced to E91.
* **Kernel no-signalling** — **CLOSED.**
* **LF6 pointer-volume no-signalling** — **CLOSED**, marginal *volumes*.
* **SO-1** — **assumed/open**, preserved as an upstream input.
* **General non-factorising-`Σ` no-signalling** — **OPEN**, BACKLOG row.
* **Bell-local outcome factorisation** — **impossible**, unchanged.

## Axiom results

All C1 support theorems, old and new: `[propext, Classical.choice, Quot.sound]`.

Item 24 specifically: the Born-volume chain is clean, and stronger than clean —
`EffectGleason` is **not in the 53-module transitive import closure** of
`LF6/LocalDeisolationFlow.lean`. It never reaches Busch, so this is a fact about
the dependency graph rather than about axiom bookkeeping.

**No `Tests/AxiomAudit/C1.lean` was created**, deviating from the work order:
nine of its ten listed theorems were *already* pinned in the namespace-matched
parts the G9 split mandates, so a dedicated part meant nine duplicate pins. The
one genuinely missing pin was added to `Dynamics.lean`.

## Build and guards

`lake build` and `lake build CsdLeanTests`: **0 errors, 0 warnings**.
**Nine guards green**, including the new `check-claim-provenance`.

## Remaining debts

1. **Erratum E-1** (type separation) and **E-2** (the nudge) — the manuscript
   is not editable from here. Close only when the *text* is amended.
2. **General no-signalling over non-factorising `Σ`** — open research.
3. **SO-1** — the entangled sector posited, never derived.
4. **`hgen` on the original `localDeisolation_pointer_volume`** — retained
   deliberately; the local route supersedes it.
5. **Promotion to CL-031+** — author decision, see below.

## Recommended release action

A tag is **prepared but not created**: `CITATION.cff` now records the
theorem-citation quadruple (repository, tag or SHA, module path, theorem name)
and the rule that "LF5"/"LF6" must never be cited as documents. Creating and
pushing a tag is an author decision.

Recommendation: tag after the CL-031 decision, so the ledger surface is stable
at the tagged commit.

## On promoting the C1 theorems to CL-031 onward

**Recommendation: promote exactly one —
`no_compatible_global_chsh_assignment_realises_singlet`.**

It is a genuinely new no-go, and a direct sibling of CL-020
(`no_product_partition_realises_singlet`) and CL-021 (the GHZ analogue), which
*are* headlines. A new no-go of that family belongs beside them.

Leave the locality results sub-headline. `localDeisolation_factorises`,
`localDeisolation_pointer_volume` and the rest of the local-de-isolation tier
are **not** CL rows today, so promoting their successors while their
predecessors stay unlisted would make the ledger less coherent, not more.

Cost of promoting, concretely: a `public import` plus a drift-guard
`example := @…` line in `Headlines.lean`; a row in `validation-claims.tsv` and
`VALIDATION-LEDGER.md`; and the "30 headline claims" count updated in
`Headlines.lean` (twice), `CsdLean4.lean`, `specs/INDEX.md` and
`specs/audit-sweep-plan.md`. That last one touches the landing surface, which
`CONVENTIONS.md` §10 permits only when a headline claim actually changes —
which this would be.

Benefit beyond what already exists: the axiom pins already give rename and
deletion protection, since a renamed constant fails to elaborate. What a CL row
adds is the **review surface** — `status`, `load_bearing`, `independent_check`
and `finding` columns. For this theorem the `finding` column is the valuable
part: it can record that the C1 tier arrived via a correction of a false claim,
which is exactly the context a later reviewer needs and which no pin carries.

## Post-closure update (2026-08-10)

The report above is the record **as of `612d9ec`**, and is preserved unedited.
Two things happened after it:

1. **CL-031 promoted at `7347e62`.**
   `no_compatible_global_chsh_assignment_realises_singlet` is now a headline
   claim; the corpus carries **31**, not 30. `Headlines.lean` (facade import,
   layer entry, drift-guard line), `validation-claims.tsv`,
   `VALIDATION-LEDGER.md` (Validated 8 → 9) and the count in `CsdLean4.lean`,
   `specs/INDEX.md` and `specs/audit-sweep-plan.md` were all updated. The
   locality and no-signalling results were deliberately **not** promoted — see
   the recommendation in this report, which was followed.

   ⚠️ So this report's "recommended release action" and the
   `docs/C1-FORMAL-SUPPORT.md` note about promotion being a pending author
   decision were both **superseded within the same session**; the support map has
   been corrected, and this note records the sequence.

2. **Tag `v1.2.0-c1-correction` created and pushed at `7347e62`.**

**Residual hygiene pass (2026-08-11).** An external verification of `7347e62`
found five documentation defects that the item-31 sweep missed, all now fixed:
the `SingletDeisolationFlow` module introduction still carried the false
local-unitary reading of `nudgedSinglet` and an "A.3 deferred" bullet, so the
file contradicted its own corrected docstring; over-broad "every Bell-test"
wording
attached to `hgen` survived in `JointEig.lean`, `SingletDeisolationFlow.lean` and
`specs/LF4-todo.md`; and `Tests/AxiomAudit/Dynamics.lean` still described the GHZ
Mermin carve and local product flow as deferred, though both landed as C.3 and
C.4. The lesson is the same one this correction kept re-learning: a lexical sweep
narrows the surface and does not close it.

**On item 35 — CORRECTED 2026-08-11.** An earlier revision of this note said
remote CI confirmation was "not independently established". **That was wrong**,
and it was wrong because both the external reviewer and I checked the legacy
commit-*status* endpoint, which GitHub Actions does not populate: Actions
reports through **check runs**, not statuses.

CI has in fact run on every push throughout this correction and **passed every
time**. Run `31500132916` covers `b0d94b2` (this pass) and completed `success`
in 5m13s, executing the full guard suite including the new
`check-claim-provenance`.

Two guards ran in CI that were **never run locally** in the correction session,
and both passed:

* `check-axiom-imports` — OK, every locatable pinned constant is in AxiomAudit's
  import closure (this is the ~10-minute guard);
* `check-module-coverage` — OK, 495 modules reachable.

`check-validation-ledger` also reports **OK (31 linked headline claims)**,
independently confirming the CL-031 wiring.

So item 35 is **CI-confirmed**, not merely locally reported — and CI verified
strictly more than the local runs did. The lesson is the same one this
correction kept producing: check the endpoint before recording an absence.

## Post-R1 history (added 2026-08-11 — this section was itself behind)

An external review found that this report had **again** fallen behind the
repository, recording only up to the CI correction. That is an audit-trail
defect in a document whose only job is the audit trail, so the remaining
history is recorded here and this section is to be extended with every C1 tag.

3. **R2 correction** (`6771214`, tagged `v1.2.2-c1-R2` at `b38c110`). The
   endpoint treatment in `JointEig.lean` was corrected: at `a·b = ±1` two
   sectors vanish and the other two carry probability `1/2`, giving perfect
   correlation or anticorrelation. The legacy restriction comes from division
   by `√P_st`, **not** from any absence of physical information — the earlier
   text said the collinear settings "carry no Born information", which was
   false. `b38c110` then repaired a dangling clause the R2 edit left stranded.

4. **R3, this pass** (tagged `v1.2.3-c1-R3`). A second external review found
   four live-documentation residuals and one hardening opportunity; all five
   are closed:

   * `SingletDeisolationFlow.lean` — the section heading still read "the
     prepared state `φ = (U_A ⊗ U_B)† ψ⁻`" **directly above** the docstring
     saying that identification is false. Retitled "The legacy singlet-moduli
     representative". Historical "deferred" prose removed from the live A.3
     description (it belongs in this report, not in a module specification).
   * **"A.3 factorises A.2" was wrong wording in two places.** A.3 does *not*
     factorise the A.2 flow: A.2 gives a joint `N = 4` realisation that is not
     wing-factorised, and A.3 *independently* supplies a factorised local
     realisation of the same joint measurement. Corrected in the module header
     and the capstone.
   * `ContextMap.lean` — the **category line** still read "Bell-consistency
     boundary via definitional separation, no Fine axiom", contradicting the
     body, which correctly says type separation proves nothing. This is the
     precise phrase that caused the original defect, surviving in the one place
     nobody re-read.
   * `CITATION.cff` pointed at `v1.2.1-c1-R1`, whose prose R2 had superseded.
     Now points at `v1.2.3-c1-R3`, with the tag history and an explicit warning
     that the line is not self-maintaining — it has now gone stale twice.
   * **Hardening:** `wingPairUnitary` was called a "product unitary" in prose
     while only its *factors* carried an exported unitarity theorem.
     `wingPairUnitary_mem_unitary` / `_mem_unitaryGroup` now export it
     (via `Matrix.kronecker_mem_unitary`), pinned in `AxiomAudit/Dynamics.lean`.

   Old tags were **not** moved. They are audit history.

**No theorem-level C1 defect was found by either review.** The reviews have
converged from mathematical defects, through conceptual documentation defects,
to release hygiene — which is the expected shape of convergence, and the reason
to stop iterating on the repository for C1 after this tag.

## References

`specs/c1-correction-plan.md`; `docs/C1-FORMAL-SUPPORT.md`;
`specs/publication-errata.md`; `scripts/check-claim-provenance.sh`;
`specs/prose-audit.md` (the standing audit whose mode-4 rule came out of this).
