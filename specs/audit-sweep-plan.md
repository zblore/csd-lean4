# Audit sweep — extend the adversarial audit below the Tier-A headlines

Added 2026-06-10. **Status: planned, not started.**

## Motivation

The standing verification discipline audits each tranche's **Tier-A headlines** (the
named capstone theorems) via the independent referee pass (csd-lean-auditor):
vacuity, hallucinated/weakened statements, axiom drift, coverage gaps. That pass
reads supporting material only as far as the headline's soundness requires. The
**Tier-B-and-below strata** — supporting lemmas, infrastructure modules, the Cat-1
`Mathlib/` staging tree, bridge bundles, definitional packaging — have never had a
*dedicated* adversarial pass of their own. Risks living there:

- a supporting lemma whose name/docstring claims more than its statement (latent
  over-claim that a future tranche cites at face value);
- definitional packaging that does not mean what it is named (the auditor's
  "definition drift" class), invisible while only headlines are checked;
- Cat-1 staging files diverging from Mathlib standards before upstreaming;
- structure-field hypotheses that are satisfiable-but-never-instantiated
  (vacuity one level below the pinned theorems);
- docstring honesty drift in modules last touched several tranches ago.

## Scope and method

Run csd-lean-auditor as a **per-module gap sweep** (its second designed use), not
per-theorem. Sweep order by downstream load:

1. `CsdLean4/Mathlib/` staging tree (highest reuse; upstream-facing standards);
2. `LF2/` + `LF3/` supporting strata (oldest, most cited by later layers);
3. `LF4/` non-headline modules (the moment-map cluster's helper lemmas);
4. `Empirical/` non-headline support + the `CSD/` bridge bundles (cross-check
   against `BRIDGE-OBLIGATIONS.md`);
5. `LF1/` (smallest risk; audited implicitly by every chain consumer).

Each sweep produces a findings report (severity-tagged, exact locations); repairs
land via the standard expert→auditor→commit loop, doc-currency rule applies.
Findings that are honest-scope notes (not defects) get docstring fixes only.

## Definition of done

Every module under `CsdLean4/` has either (a) a Tier-A audit on its headlines from
its landing tranche **and** a module-level sweep entry here, or (b) an explicit
skip rationale recorded here. This file carries the running ledger:

| Sweep | Modules | Status |
|---|---|---|
| 1. Mathlib staging | `CsdLean4/Mathlib/**` | not started |
| 2. LF2/LF3 support | `LF2/**`, `LF3/**` | not started |
| 3. LF4 non-headline | `LF4/**` (non-capstone) | not started |
| 4. Empirical support + bridges | `Empirical/**` | not started |
| 5. LF1 | `LF1/**` | not started |
