# The CR queue — external review, execution order

**Status:** recorded 2026-09-05. **Why this file exists:** the queue lived only in a chat
transcript. Two items had been executed and the remaining fourteen existed nowhere in the
repository, so a lost session would have lost the plan. The titles, sizes, dependencies and
execution order below were recovered from the session log; ⚠️ **the per-item bodies were not fully
recoverable** — where an item is marked *(body not recovered)* the detail must be re-supplied
before it is worked.

## Execution order (as set by the author)

> **CR-1 + CR-15 together** → **CR-2** → **CR-3, CR-6, CR-8, CR-12** → **CR-13** → **CR-16** →
> **CR-7** → **CR-5** → **CR-11** → **CR-4** → CR-9 (background) → CR-14-as-fallback → **CR-10**

## The items

| # | Item | Size | Status |
|---|------|------|--------|
| CR-1 | Governance layer: posit-plus-characterisation wording | days | **DONE 2026-09-05** (`edb34d1`) |
| CR-2 | Posit register | days | **DONE 2026-09-05** — `specs/POSITS.md`, the frontier trichotomy, this file |
| CR-3 | The three priced witnesses as a first-class statement | days | open |
| CR-4 | BELL-MIGRATE (28 files, mechanical) | 1–2 weeks | open |
| CR-5 | Promote the calibrated bank to a named posit **in code** | days | open — registered as Posit 5, code half outstanding |
| CR-6 | Unitary-class posit recorded | days | open |
| CR-7 | Label-space and infrastructure hygiene | days | open *(body not recovered)* |
| CR-8 | Naming and residue paragraphs in CV and Empirical | hours | open *(body not recovered)* |
| CR-9 | Mathlib upstream batch | weeks, background | open *(body not recovered)* |
| CR-10 | *Optional:* unitarity from no-signalling | 4–8 weeks | open — would upgrade the review's Posit 4 to a theorem |
| CR-11 | Moving-fibre witness | 1–2 weeks | open |
| CR-12 | Recurrence and persistence scope | days | open |
| CR-13 | Name the equivariance theorem | days | open — first item with real mathematical content after the wording batch |
| CR-14 | Exploration only: relaxation H-theorem | — | blocked on hitting-time asymptotics; after CR-11 |
| CR-15 | *Optional:* characterise the cell law | weeks | **DONE 2026-09-04** (`aa7c3cb`, `e6ba209`) |
| CR-16 | *Optional:* the n-step chain theorem | weeks | open |

## What CR-15 and CR-1 settled, for anyone reading the later items

CR-15 was executed first on the author's instruction, being the only item that could convert the
programme's weakest posit into a theorem. It did, by a route the queue did not anticipate — torus
**generation** rather than the frame-function characterisation CR-15 proposed. Consequences the
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
agree at Posit 1 (the cell law) and **diverge after** — the review's Posit 2 concerns n-bank chain
depth and its Posit 4 is unitarity, neither of which is the repository's Posit 2 or 4. When an item
below says "Posit N", check which register is meant. The review's Part II enumeration is **not**
recorded here because it was not recoverable from the session log; re-supply it if exact
correspondence is needed.

## References

`specs/POSITS.md` (the register, and what "frontier" means);
`specs/cell-law-scoping.md` (CR-15's route, and the declined one); `AXIOMS.md` §3 (the postulate
ledger); `specs/residues.tsv` + `specs/BACKLOG.md` (unfinished work, distinct from posits);
`specs/future-work.md`.
