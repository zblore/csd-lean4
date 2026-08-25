# Q10 — no-signalling from primitives over a non-factorising Σ

**Status: a scoping doc. No theorem here, and nothing below is a corpus claim.** Written 2026-08-25
against `specs/BACKLOG.md` row Q10 / C1 item 16, which asks for *scoping-first* and is right to.

⚠️ **Framing not yet anti-drift checked.** `CLAUDE.md` requires the `csd-foundations` agent before
scoping new work; the session that wrote this could not spawn agents. Run it over §3 and §4 before
any of this is quoted as programme direction.

---

## 1. What Q10 asks

> Determine sufficient **primitive** conditions on setting-dependent, measure-preserving CSD dynamics
> over a **non-factorising** ontic `Σ` that **imply** operational remote marginal invariance —
> *without* assuming Bell-local pointwise response independence.

Non-factorising is the whole point: C1 needs `Σ` **not** to split as a product across the wings, or
the singlet is unreachable. So the no-signalling has to come from somewhere other than a product
form.

---

## 2. ★ Wall-check, done before any theorems

The Q12 arc cost three separate walls that each turned out narrower than first stated, every one of
them discovered *after* work had started. This section is the correction: the walls are checked
first, and each is tied to a constant.

### W1 — the response-side primitive is not merely too strong, it is **FALSE** here

The obvious primitive is pointwise response independence: `F_A(a,b,x) = F_A(a,b',x)` on both wings.
Imposing it makes `(R_A, R_B)` a **product partition**, and
`CSD.LF6.no_product_partition_realises_singlet` says no product partition reproduces the singlet.

⚠️ That theorem is **fully general** — an arbitrary measurable space with a probability measure,
no CSD hypothesis anywhere (its own docstring names the binder as Bell's `Λ`). So this is not a
limitation of the corpus's sector; the response-side route is closed by a theorem, for any theory of
this shape. **Do not spend effort here.**

### W2 — the predicate currently in the corpus is a restatement, not a premise

`LF3.OperationalNoSignalling μ S := RemoteMarginalInvariantA μ S ∧ RemoteMarginalInvariantB μ S`,
and `RemoteMarginalInvariantA` is literally `μ {l | wingA ⟨a,b⟩ l = s} = μ {l | wingA ⟨a,b'⟩ l = s}`
— the conclusion. Any theorem taking it as a hypothesis is a **verification in the constructed
sector, not a derivation**, and the BACKLOG row already requires C1 §4.2 to say so in those words.
This is the gap Q10 exists to close, not a defect to be repaired in place.

### W3 — the hidden premise is measurement independence, and it is already named

`OperationalNoSignalling` fixes **one `μ` across all four contexts**. That fixture *is* measurement
independence — a genuine Bell premise. ✅ It is disclosed in the definition's own docstring
(`LF3/OperationalNoSignalling.lean`), so no drift here; but any Q10 statement inherits it and must
say so.

### W4 — ★ the corpus **already derives** no-signalling from a primitive, just not here

`CSD.CV.composite_no_signalling` (`CV/CompositeArena.lean`): a kick built from a right-sector unitary
leaves **every** left-sector arena observable invariant, at **every** point, entangled points
included. Its own docstring: *"not a consequence of the join, which is why it needs no product form
on the state."*

That is a genuine derivation from a primitive — **disjoint mode support** — and it needs no product
state, which is exactly Q10's constraint. What it is not: it is pointwise on the arena rather than
measure-level on `Σ`, and it constrains *observables under a kick* rather than *outcome maps under a
setting change*.

---

## 3. ★ What the wall-check reshapes

Put W1 and W4 side by side and the design question answers itself:

> **W1 kills primitives phrased on the response functions. W4 shows a primitive phrased on the
> support/generator side derives the same conclusion and never touches the responses at all.**

`composite_no_signalling` evades W1 not by being cleverer but by living somewhere else: disjoint
support is a condition on *which modes the operators touch*, and it says nothing about how an outcome
depends on a remote setting. The product-partition obstruction has nothing to bite on.

**So Q10's search space is not "which response condition is weak enough". It is "what is the
`Σ`-level analogue of disjoint support".** That reframing is the main output of this doc, and it
should be checked before it is relied on.

---

## 4. ★ Q10 and Q12 exit at the same place, and the board did not know it

The BACKLOG says Q10 "pairs naturally with Q12 (both ask for primitive conditions on Σ-dynamics)".
That was written before Q12 finished, and the pairing is now much tighter than "both are about
dynamics":

* **Q12's exit question** (2026-08-24, after the mixing formulation was retired): *what structure
  supplies the **independence** of the outcome clocks?* — established as a question about `Σ`'s
  structure, not its dynamics, because one deterministic trajectory cannot supply independence.
* **Q10's hidden premise** (W3): fixing one `μ` across contexts **is measurement independence**.

Both bottom out in **independence as a primitive on `Σ`**. And Q12 produced a positive result about
where independence lives: the **fibre** carries independence the base cannot
(`specs/CSD-CHARTER.md`, restated 2026-08-24).

**Conjecture worth scoping (not a claim):** the fibre is also where Q10's primitive lives. If the
fibre factorises across the wings while the **base** does not, then remote marginal invariance could
follow by a Fubini argument over the fibre, leaving base non-factorisation — the thing C1 needs —
completely untouched.

⚠️ **This must be gated against W1 before any Lean.** The question to answer first is whether
fibre-factorisation collapses into a product partition. It plausibly does not, because the wing
readouts would still depend on the *shared, non-factorising base*, so `R_A` still moves with `b`
through the base — but "plausibly" is exactly the word that cost the Q12 arc three restatements.
**Settle it on paper, with an explicit candidate `(R_A, R_B)`, before opening a file.**

---

## 5. Candidate primitives, and the gate each must pass

| # | Candidate | Shape | Gate (all must pass W1) |
|---|---|---|---|
| (a) | **Fibre factorisation** — `Σ = base × (F_A × F_B)`, wing readout depends on the base and its own fibre factor | the §4 conjecture | Does an explicit `(R_A, R_B)` of this shape form a product partition? If yes, dead by W1 |
| (b) | **Σ-level disjoint support** — the setting change acts by a measure-preserving map supported away from the remote readout | the W4 analogue | Is "support" definable on `Σ` without a product structure? This is the real design question |
| (c) | **Conditional independence given the base** | weakening of (a) | Weaker than (a), so if (a) fails, check whether (c) still yields invariance |

★ **(b) is the one to scope first.** It is the shape the corpus has already made work once, and the
whole content is whether `Σ` admits a notion of localisation that does not presuppose a product.

---

## 6. Bricks, in order, with gates

1. **Q10-w — settle the §4 gate on paper (S).** Write an explicit candidate `(R_A, R_B)` of
   fibre-factorised shape and check by hand whether `IsProductPartition` holds. **Gate: if it does,
   route (a) is dead and this doc's §4 conjecture is retracted, in writing.**
2. **Q10-a — define `Σ`-level localisation (M, design).** The actual work of the row. Candidate (b):
   what does "the setting acts away from the remote readout" mean on a non-factorising `Σ`? The
   `CV/ModeLocality` `SupportedOn` machinery is the model to imitate, not to import.
3. **Q10-b — the derivation (S–M, if 2 lands).** With a localisation primitive in hand the proof is
   expected short — this is the row's own "the proofs after are likely short". Deliverable: a theorem
   whose *hypothesis* is the primitive and whose *conclusion* is `OperationalNoSignalling`, replacing
   the current verification-shaped statement.
4. **Q10-c — C1 §4.2 wording (S, author).** Whatever lands, the paper text must distinguish
   verification from derivation, per the BACKLOG row.

---

## 7. Non-goals

* **Not** re-deriving C1. The obstruction results stand; Q10 is about the no-signalling side only.
* **Not** adding an axiom. The row says so explicitly, and W3's measurement-independence premise is
  disclosed rather than assumed away.
* **Not** repairing `OperationalNoSignalling` in place. W2 is the point of the row: the predicate is
  the conclusion, and the deliverable is a *premise* upstream of it.
* **Not** claiming derivation where verification is what was achieved. This is the specific failure
  the row was opened to prevent.

---

## 8. Recommendation

Do **Q10-w first, and let it kill §4 if it wants to.** It is an afternoon on paper and it decides
whether the Q12 connection is real or a pleasing coincidence. Only then open Q10-a.

The honest headline for the queue: **Q10's response-side route is closed by a theorem the corpus
owns, and its support-side route has a working precedent in the corpus. That is a much better
starting position than "research", and it is the direct benefit of checking the walls first.**

## References

`specs/BACKLOG.md` row Q10 and the C1 item 16 row; `docs/C1-FORMAL-SUPPORT.md`;
`specs/c1-correction-plan.md` §1; `LF3/OperationalNoSignalling.lean` (W2, W3);
`LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`, W1);
`CV/CompositeArena.lean` (`composite_no_signalling`, W4); `CV/ModeLocality.lean` (the `SupportedOn`
model); `specs/q12-fibre-mechanism-scoping.md` (the exit question, §4);
`specs/CSD-CHARTER.md`; `specs/future-work.md`.
