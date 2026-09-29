# Colbeck–Renner and CSD: which premise the programme denies

**Status:** spec note, written 2026-09-04 (expert-review row D of `BACKLOG.md`); the Lean form
landed 2026-09-29 and is described in "The Lean form" below. The positioning is still positioning:
what the Lean theorems add is that the premise the escape uses is now a *hypothesis of a theorem*
rather than a sentence in this note.

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

## The Lean form (landed 2026-09-29, BACKLOG row 23)

Two modules. [`Mathlib/Probability/ChainedBell.lean`](../CsdLean4/Mathlib/Probability/ChainedBell.lean)
is the CSD-free half: for a two-outcome outcome law, two marginals of one joint distribution differ
by at most the probability that the outcomes disagree, and add to `1` up to the probability that
they agree. **No-signalling is exactly what allows those one-pair statements to be chained across
different pairs**, because it makes each wing's marginal a function of that wing's setting alone.
Closing the chain with one reversed link gives `abs_marginalA_sub_half_le`: the marginal is `1/2` up
to half the chain's total cost. `integral_abs_marginalA_sub_half_le` transfers the same bound to
every component of a mixture, since the functional is affine in the law.

[`Empirical/QM/ColbeckRenner.lean`](../CsdLean4/Empirical/QM/ColbeckRenner.lean) instantiates it at
the singlet, with `2n + 2` settings placed around a great circle in steps of `π − π/(2n+1)` so that
the chain closes exactly (`dotR_crA_zero_crB_last`, because `(2n+1)` steps come to `2nπ`). The bound
is `π²/(8(2n+1))`, and `no_improved_predictive_power` is the limit form: for every `δ > 0` there are
settings at which no parameter-independent extension predicts Alice's outcome better than `1/2` by
more than `δ`, in mean over the extension variable.

**The unbundling is in the hypotheses, which is the point of doing it in Lean.** Parameter
independence is the pair `hA`, `hB` (each component is no-signalling); measurement independence is
the single shared `μ`, fixed before the settings and used for every setting pair in `hmix`. A reader
can see which one the theorem consumes without taking this note's word for it, and
`exists_signalling_of_sharp` states the contrapositive: an extension that does sharpen the outcome
has a component that signals.

## What is NOT claimed here

* **Not the general-state theorem.** Colbeck and Renner extend from maximally entangled states to
  all states by an embedding argument, which is not formalised. What is proved is their statement
  for the singlet, which is where the chained-Bell machinery does its work. "Improved predictive
  power" is formalised as sharpening the *outcome marginal* of one measurement, in mean over the
  extension variable, not as the full conditional distribution.
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
