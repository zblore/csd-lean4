# The curated key set — terms the corpus cannot name for itself

`scripts/extract-eponyms.sh` decides one half of the glossary: the eponyms that appear
in declaration and module names. That half is derived, not chosen, which is its whole
virtue — the corpus says what needs explaining and taste does not get a vote.

It is also structurally blind. It can only surface names that someone is named after.
A reader arriving at this programme is at least as likely to be searching for
**contextuality**, **the measurement problem**, or **ψ-epistemic** — terms that name
what the programme is *about*, that every rival account also claims, and that no
extractor will ever find because no declaration is called `contextuality`.

So this file is the other source: **hand-maintained, deliberately editorial, and
justified per entry.** It exists to be argued with. `docs/glossary.yaml` consumes both
lists; nothing distinguishes the resulting entries except that these ones were chosen.

## The admission test

An eponym earns an entry by appearing in the corpus. A concept has no such evidence, so
it needs a reason. One of:

1. **CSD takes a position on it**, and a reader comparing accounts needs to know what
   that position is (ψ-epistemic, collapse, determinism).
2. **It is a rival account** a reader will inevitably want CSD placed against
   (Copenhagen, Many-Worlds, Bohmian, GRW, QBism).
3. **It is an obstruction the programme must survive**, whether or not it is named after
   anyone (contextuality, hidden variables, the measurement problem).

A term that fails all three is a dictionary definition and belongs in `refs:` as an
outward link, not as a page.

## The standing risk, stated once

These entries are the only ones where the `in_csd` register makes a *positional* claim —
"CSD is ψ-epistemic about states", "CSD is not Many-Worlds" — rather than reporting a
theorem. Positional claims cannot be guarded: `check-glossary` verifies that anchors
resolve and links are symmetric, and nothing anywhere can verify that a sentence
describes the programme correctly. Two consequences, both deliberate:

* Where a positional claim is **backed by a theorem**, the entry carries the anchor and
  says which theorem. Contextuality and hidden variables do; Copenhagen does not.
* Where it is **not**, the entry says so plainly rather than borrowing authority from
  the anchored ones. An interpretation page that reads like a proved result is worse
  than no page.

## The list

Status column is the intended `status:` in `glossary.yaml`.

| Term | Test | Status | Notes |
|---|---|---|---|
| contextuality | 3 | proved-in-corpus | Anchored: the singlet obstruction. CSD is contextual by construction, so this is a commitment, not a concession |
| hidden variables | 3 | proved-in-corpus | Anchored. The substrate IS a hidden-variable theory in the technical sense; the entry must say which kind and why the no-gos do not kill it |
| measurement problem | 3 | proved-in-corpus | Anchored to the trilemma no-gos — the sharpest thing the corpus has to say about it |
| psi-epistemic | 1 | definition | The programme's central positional claim. No theorem states it; it is the reading OF the theorems |
| collapse | 1 | proved-in-corpus | Anchored: no measure-preserving map implements exact collapse |
| determinism | 1 | definition | Substrate is deterministic; outcomes are typicality. Positional |
| typicality | 1 | proved-in-corpus | The mechanism the whole account runs on |
| Kochen-Specker | 3 | standard-mathematics | Eponym, but the extractor never sees it: no declaration carries the name. Exactly the blind spot this file exists for |
| Copenhagen | 2 | definition | Positional, unanchored |
| Many-Worlds | 2 | definition | Positional. Must record that CSD is single-trajectory — a settled non-goal, not an open question |
| Bohmian mechanics | 2 | definition | The closest rival in spirit: deterministic, ψ-epistemic-adjacent, explicitly non-local |
| GRW / spontaneous collapse | 2 | definition | The rival that CHANGES the predictions; CSD does not |
| QBism | 2 | definition | The rival that is epistemic all the way down, where CSD keeps an ontic floor |

## Candidates considered and rejected

* **Superposition, entanglement, decoherence, wavefunction** — standard vocabulary any
  encyclopaedia covers, and the corpus does nothing distinctive with the *terms* even
  where it proves things about the phenomena. `refs:`, not entries.
* **Everett branching** — the content is Many-Worlds; a separate page would split one
  position across two.
* **Non-locality** — genuinely tempting, and the reason it is held back is that saying
  it properly requires the part of the programme that is not public. Revisit when it is.

## References

`docs/glossary.yaml` (the entries themselves); `scripts/extract-eponyms.sh` (the derived
half); `scripts/check-glossary.sh` (what is and is not guarded);
`specs/CSD-CHARTER.md` (the vocabulary discipline these positional claims must respect).
