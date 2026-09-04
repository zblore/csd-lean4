# Colbeck–Renner and CSD: which premise the programme denies

**Status:** spec note, written 2026-09-04 (expert-review row D of `BACKLOG.md`). Positioning,
not a Lean obligation — the Lean form is scoped at the end and is **not** queued.

## The theorem

Colbeck and Renner 2011 (`[ColbeckRenner2011]`, doi:10.1038/ncomms1416): **no extension of
quantum theory can have improved predictive power**. An "extension" supplies additional
information `Ξ` beyond the quantum state; the conclusion is that conditioning on `Ξ` cannot
sharpen the quantum predictions. Read as a referee reads it, it says: a theory that posits
underlying states which fix outcomes is either predictively equivalent to quantum mechanics, or
it violates one of the premises.

CSD posits exactly such underlying states — a point of `Σ` fixes the outcome — so the referee's
question is the right one to answer directly, and this note answers it.

## Which premise CSD denies

**Parameter independence, at the `Σ` level.** This is the same escape the corpus already takes
from Bell, and it is a theorem there, not a stance: `CSD.LF6.no_product_partition_realises_singlet`
(`LF6/ForcedContextuality.lean`, CL-020) shows that **no** product partition of any probability
space reproduces the singlet correlations. The response maps cannot each depend only on the local
setting; the ontic response is irreducibly joint. Note the theorem's own scope, recorded in
`necessity-audit.md`: it is stated over an arbitrary measurable space with no CSD-specific
hypothesis, so it constrains rival theories of the same shape too.

## ⚠️ Not by denying free choice — the unbundling

The escape is **not** "CSD denies free choice", and saying so would misdescribe the corpus.
Colbeck–Renner's "free choice" (their FR condition) **bundles two distinct assumptions**:

1. **parameter independence** — the distant setting does not affect the local ontic response;
2. **measurement independence** — the settings are uncorrelated with the ontic state.

The analyses that separated them are Ghirardi–Romano 2013 (`[GhirardiRomano2013]`) and Leegwater
2016 (`[Leegwater2016]`): what the argument actually needs is parameter independence, and a
theory may deny that while keeping measurement independence in full.

**The corpus keeps measurement independence, as a premise, and says so in the module that uses
it.** `LF3/OperationalNoSignalling.lean` states it outright — one shared measure across the four
contexts *is* measurement independence, "a premise, not a consequence". So the CSD position is:

> parameter independence — denied, and the denial is a theorem
> (`no_product_partition_realises_singlet`);
> measurement independence — retained, as an explicit premise.

Anything that reads CSD as superdeterministic or as retrocausal has collapsed the bundle. The
glossary entry `is-csd-superdeterministic` makes the same point for a general reader; this note
is the referee-facing version with the citation trail.

## What is NOT claimed here

* **No Lean theorem states the Colbeck–Renner escape.** This note is positioning prose. Recording
  it as a named theorem would need the chained-Bell family the CR argument runs on — rated M–L in
  `BACKLOG.md` row D, and deliberately **not queued** ("Lean only if asked"). Do not cite this
  note as a formal result.
* **Satisfying or escaping a no-go is not evidence for the programme.** It removes an objection;
  it does not support a claim. The same discipline as the `excess-baggage` glossary entry.
* **The escape is inherited, not independent.** It is the Bell escape, in the CR setting. If
  `no_product_partition_realises_singlet` were ever weakened, this note weakens with it.

## References

`[ColbeckRenner2011]`, `[GhirardiRomano2013]`, `[Leegwater2016]` in `REFERENCES.json`;
`CsdLean4/LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`, CL-020);
`CsdLean4/LF3/OperationalNoSignalling.lean` (measurement independence as a stated premise);
`CsdLean4/LF3/SettingLocality.lean` (`operationalNoSignalling_of_settingLocality`, Q10-a/b);
`specs/necessity-audit.md` (the theorem's transferable force); `specs/BACKLOG.md` row D;
`docs/glossary.yaml` (`is-csd-superdeterministic`, `excess-baggage`).
