# The CR queue — external review, execution order

**Status:** recorded 2026-09-05. **Why this file exists:** the queue lived only in a chat
transcript. Two items had been executed and the remaining fourteen existed nowhere in the
repository, so a lost session would have lost the plan. The titles, sizes, dependencies and
execution order below were recovered from the session log; ⚠️ **the per-item bodies were not fully
recoverable**. ⚠️ Where an item's body is not recovered the detail must be re-supplied by the
author before it is worked: **do not infer the scope from the title** (author instruction,
2026-09-05).

## Execution order (as set by the author)

> **CR-1 + CR-15 together** → **CR-2** → **CR-3, CR-6, CR-8, CR-12** → **CR-13** → **CR-16** →
> **CR-7** → **CR-5** → **CR-11** → **CR-4** → CR-9 (background) → CR-14-as-fallback → **CR-10**

## The items

| # | Item | Size | Status |
|---|------|------|--------|
| CR-1 | Governance layer: posit-plus-characterisation wording | days | **DONE 2026-09-05** (`edb34d1`) |
| CR-2 | Posit register | days | **DONE 2026-09-05** — `specs/POSITS.md`, the frontier trichotomy, this file |
| CR-3 | The three priced witnesses as a first-class statement | days | **DONE 2026-09-05** — TOUR section, the horn named in `FiniteQMClosure.lean` (**seams**), the everywhere-only scope recorded at `no_everywhere_correlation`, the Q12-d retirement in `KahlerFibreMixing.lean`, A2 pointer |
| CR-4 | BELL-MIGRATE (28 files, mechanical) | 1–2 weeks | open |
| CR-5 | Promote the calibrated bank to a named posit **in code** | days | open — registered as Posit 5, code half outstanding |
| CR-6 | Unitary-class posit recorded | days | **DONE 2026-09-05** — TOUR (both halves), `LF4/ProjectedDynamics.lean` header, reconstruction-status A5, Posit 6, Gisin1990 registered |
| CR-7 | Label-space and infrastructure hygiene | days | **DONE 2026-09-05** — CONVENTIONS §12 (not §10, which was taken), `scripts/check-labels.sh` + baseline + 2 probes + CI. ⚠️ The five collisions are **grandfathered, not renamed**; reasons in §12 |
| CR-8 | Naming and residue paragraphs in CV and Empirical | hours | open — ⚠️ *body not recovered; the author will supply it. Do NOT infer the scope from the title.* |
| CR-9 | Mathlib upstream batch | weeks, background | open — ⚠️ *body not recovered; the author will supply it. Do NOT infer the scope from the title.* |
| CR-10 | *Optional:* unitarity from no-signalling | 4–8 weeks | open — would upgrade the review's Posit 4 to a theorem |
| CR-11 | Moving-fibre witness | 1–2 weeks | open |
| CR-12 | Recurrence and persistence scope | days | **DONE 2026-09-05** (incl. the E5 spike retained-not-required annotation) — two new theorems making register-freezing checkable (`unifiedDeisolationModel_interaction_register`, `…_readout_register_irrelevant`, 2 pins), plus FiniteQMClosure header and TOUR |
| CR-13 | Name the equivariance theorem | days | **DONE 2026-09-05** — new `SigmaLayer/Equivariance.lean` (`epistemicMeasure_equivariant`, ★★ `csd_equivariance`, 2 pins, CL-069), POSITS Posit 9, TOUR, Headlines. ⚠️ Corrects the item's premise: µL-preservation is **proved** on the concrete arena, not posited |
| CR-14 | Exploration only: relaxation H-theorem | — | blocked on hitting-time asymptotics; after CR-11 |
| CR-15 | *Optional:* characterise the cell law | weeks | **DONE 2026-09-04** (`aa7c3cb`, `e6ba209`) |
| CR-16 | *Optional:* the n-step chain theorem | weeks | open |

## What CR-15 and CR-1 settled, for anyone reading the later items

CR-15 was executed first on the author's instruction, being the only item that could convert the
programme's weakest posit into a theorem. It did, by a route the queue did not anticipate — torus
**generation**, not the `T^N`-equivariance-plus-normalisation package Part II proposed (which is
false; see the numbering warning below) and not the frame-function route, which was declined. Consequences the
remaining items should not re-litigate:

* The Gleason/frame-function route is **declined, not refuted** (`specs/cell-law-scoping.md`).
* Posit 1 is **restated, not discharged** — the posit count is unchanged.
* "Gleason-free" is a **provenance** claim only (`specs/CSD-CHARTER.md`, drift red flags).

⚠️ **CR-1's literal acceptance test was not met, deliberately.** It asked that a grep for
"gleason-free" return only historical lines, but the same item says to keep the phrase where it
means provenance — which is what ~130 of the uses mean, across 59 module headers, backed by two
guards. Deleting them would have orphaned machine-checked claims. The *meaning* was narrowed at the
governance sites instead. Do not re-raise the grep as an outstanding acceptance failure.

## Numbering warning

The review's own "Part II" numbers posits 1–6; `specs/POSITS.md` numbers the repository's. They
agree at Posit 1 (the cell law) and **diverge after**: review 2 (calibrated bank) = repo 5, review 3
(preparation measure) = repo 9, review 4 (unitary class) = repo 6, review 5 (composite structure) =
repo 7, review 6 (measurement independence) = repo 8; repo 3 (Liouville preservation) and repo 4
(typicality reading) have no review counterpart. When an item below says "Posit N", check which
register is meant. The review's Part II was supplied by the author on 2026-09-05 and the
correspondence is now recorded in `specs/POSITS.md` ("Correspondence with the external review's
Part II").

⚠️ **One Part II claim is refuted, not merely superseded.** Its Posit 1 proposed that
`T^N`-equivariance plus normalisation forces the rate field to be `momentMap`, calling this "a
bounded, plausible theorem worth attempting (see CR-15)". CR-15 showed it **false** —
`rate_field_not_forced_by_torus_symmetry` is a counterexample to exactly that package. The rate
field is forced by torus *generation* instead. Do not re-queue the proposed theorem.

## References

`specs/POSITS.md` (the register, and what "frontier" means);
`specs/cell-law-scoping.md` (CR-15's route, and the declined one); `AXIOMS.md` §3 (the postulate
ledger); `specs/residues.tsv` + `specs/BACKLOG.md` (unfinished work, distinct from posits);
`specs/future-work.md`.
