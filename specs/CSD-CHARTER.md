# CSD Charter — the north star (read before framing claims or scoping work)

> **Purpose.** One page stating what this project is *for*, so work does not drift
> into "just reproducing QM." This is the anchor the `csd-foundations` agent enforces
> and the frame every status doc / claim must respect. It states the mission and the
> guardrails; it does **not** hold open items (those live in [`BACKLOG.md`](BACKLOG.md))
> or the detailed status (that is [`reconstruction-status.md`](reconstruction-status.md)).

## The mission

**Deliver CSD from its foundations.** CSD (Constraint-Surface Dynamics) is the
foundation: a **deterministic, measure-preserving flow** on an **ontic constraint
surface** `(Σ, μL)`, an **epistemic projection** `π : Σ → ℂℙ^{N-1}`, and **probability
as a typicality volume** forced by the **law of large numbers over i.i.d.
preparations** (Papers A/B) — never by time-averaging one trajectory.

**QM is the forward output, not the goal.** The Born rule, Schrödinger evolution,
measurement, entanglement are what the CSD ontic model looks like *from the inside*.
Proving a QM fact matters only insofar as it is delivered from — or honestly labelled
as a forward consequence of — the CSD substrate. "We reproduced QM result X" is not,
by itself, progress here.

## The two endpoints — never conflate

1. **Operational finite-QM closure on a concrete projective product witness.**
   Largely done. A *consequence*, not the point. The witness bakes in
   `μL = μFS ⊗ vol` and `Φ_t = (e^{-itH}·[p], θ)`, so its `π_*μL = μFS` and
   `exp(-itH)` facts are *compatibility facts about the witness* — **not** derivations
   of the Fubini–Study measure, projective geometry, or unitary dynamics from anything
   more primitive.
2. **A faithful derivation of the Paper C/D architecture from CSD's primitive
   deterministic ontology.** This is the **GOAL**, and it is open.

A witness is not a derivation. Never present endpoint (1) as endpoint (2), or as "the
achievement."

## Where CSD-foundational progress actually happens

- **SO-1 — the sector-origin problem (the central open goal).** Derive the sector
  `(Σ, π, μL)` + FS typicality from CSD's primitive ontology / deterministic dynamics.
  Partial: the typicality measure is symmetry-forced *given* full `U(N)`
  (`LocalisedTypicality.lean`); the prize is a genuine **dynamical origin of the `U(N)`
  symmetry** from the substrate. **Distinct from Paper C Axiom A5** (which is
  *projectability* — the quantum-effective condition that *selects* the sector, not its
  origin; §3.6 leaves the origin "for later work").
- **MD-1 — the measurement account.** Replace preparation-indexed cells
  (`vnPointerOutcome` via `bornRegion ψ'`) with **context-fixed apparatus partitions**
  `Ωᵢ(M)` (Paper C A7), then derive outcome probabilities by integrating the
  preparation law over those fixed regions.
- **A6 / A1** — derive composition (`⊗`) and the Kähler structure from more primitive
  data rather than positing them.
- **Track B** — a genuine CSD-vs-QM departure past the "empirically identical to QM"
  ceiling (the only route to *new predictions*).

Adding gates, algorithms, or empirical QM tests is **breadth** — legitimate, but only
when *labelled as breadth*, never when it masquerades as foundational depth or crowds
out SO-1 / MD-1.

## Vocabulary discipline (guarded by `check-claims.sh`)

- **A5** = Paper C's projectability / quantum-effective condition. **Never** "sector
  origin."
- **SO-1** = the sector-origin goal. (The retired "SL-1" label and the mislabels that
  attach A5 to the sector's origin are forbidden on the forward-claim doc surface, per
  `check-claims.sh`.)
- **MD-1** = the A7 measurement-partition gap.
- The finite-QM closure is *operational closure on a witness*, not "QM derived from CSD."

## Settled non-goals (do not reopen; do not misuse)

- **NG1** — deriving Born from a single deterministic trajectory (Birkhoff / single-flow
  ergodic route) is a **proved dead-end** (`SectorPostulateNoGo.lean`,
  `TypicalityForcing.lean`). CSD forces typicality by the LLN. *But* NG1 being dead does
  **not** make SO-1 unreachable — the live route is the origin of the full `U(N)`
  symmetry, not single-trajectory ergodicity. Do not round "the flow route is dead" up
  to "SO-1 is hopeless / already handled."
- **NG2** — discharging the Busch effect-Gleason axiom was audit-posture (zero imported
  axioms), **not** a strengthening of the reconstruction (CSD's Born rule is
  Gleason-free). Do not describe it as required for the result.

## Drift red flags

- "We prove/reproduce QM" as the headline, without the CSD ontic anchor or the
  forward-consequence caveat.
- "CSD derives QM" / "the sector is derived" / "Born weights derived from the flow" —
  the sector is **posited** (SO-1 open).
- The product-model closure called a "derivation from CSD."
- SO-1 or MD-1 demoted to a footnote or dropped from a status doc while QM breadth grows.
- A5 reconflated with the sector origin.
- A measurement claim omitting the MD-1 preparation-indexed caveat.
- A tranche that is pure QM breadth presented as advancing the thesis.
- "Finite-dimensional QM is derived" — it is *reconstructed forward on a witness*, SO-1
  and MD-1 open.

## How to use this

Before landing framing/prose/claims, or scoping new work, run the **`csd-foundations`**
agent (`.claude/agents/csd-foundations.md`) against the change or plan, or check it
against this charter yourself. When in doubt about a claim's framing,
[`reconstruction-status.md`](reconstruction-status.md) §1–§2 is the canonical honest
statement, and [`BACKLOG.md`](BACKLOG.md) holds the SO-1 / MD-1 rows.
