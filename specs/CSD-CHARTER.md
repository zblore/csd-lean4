# CSD Charter — the north star (read before framing claims or scoping work)

> **Purpose.** One page stating what this project is *for*, so work does not drift
> into "just reproducing QM." Reproducing QM is the **calculation-engine floor**, not
> the thesis. This is the anchor the `csd-foundations` agent enforces and the frame
> every status doc / claim must respect. It states the mission and the guardrails; it
> does **not** hold open items (those live in [`BACKLOG.md`](BACKLOG.md)) or the
> detailed status (that is [`reconstruction-status.md`](reconstruction-status.md)).

## The ontology (the whole point)

**Σ is the floor, and Σ is everything.** The ontic surface Σ is the total, fixed,
**local** space of everything that exists. There is nothing beneath it and nothing
outside it; it does not grow. Physical reality is a **single deterministic trajectory
ω(t)** on Σ under a Liouville-preserving flow. All indeterminacy is epistemic —
ignorance of exactly *where* in a prepared region Ω₀ ⊂ Σ the microstate is.

From this one posit, the stack is:

1. **Σ — the floor.** Posited as the complete local reality. **Deriving Σ is a
   non-question** — there is nothing beneath it. (This retires the old "SO-1 / derive
   the sector" framing entirely; see *Corrections* below.)
2. **Ω-regions → QM as a calculation engine.** A measurement context partitions the
   prepared region into outcome basins {Ωᵢ}; the invariant volume ratios
   μ(Ωᵢ)/μ(Ω₀) are the outcome weights, and via typicality over repeated preparations
   (classical-statistical-mechanics-style ignorance of the microstate in Ω₀; Paper A)
   plus the SU(n)-fixed measure μFS (Paper B) they become the Born weights |⟨i|ψ⟩|².
   **QM is the instrumental calculation engine born from the Ω-region structure — not
   ontology, not the goal.** Reproducing it is the consistency floor.
3. **Measurement = de-isolation = record *selection*.** When a system is measured it
   loses isolation (couples to apparatus/environment). This **selects a record** — it
   picks out which basin the single trajectory occupies. The record is a **selection
   of structure already present in Σ**; nothing is created, Σ does not grow.
4. **Records → spacetime (projection).** The selected records in Σ **project** to make
   spacetime. Spacetime is emergent, downstream of records — not fundamental.
5. **The payoff — entanglement dissolved.** Σ is **local**; the record→spacetime
   projection is **non-local**. So entanglement-at-a-distance is *locality in Σ* seen
   through a non-local projection — there is no fundamental action at a distance. This
   is the deliverable the whole programme is for.

**The thesis is layers 3→5 (records in Σ, their projection to spacetime, and the
locality resolution). Layer 2 — reproducing QM — is the engine floor beneath it.**

## Where progress actually happens

- **The record layer (MD-1).** Make measurement genuine **record selection via
  context-fixed Ω-basins on Σ** — a partition of Ω₀ determined by the apparatus, with
  the preparation entering only through Ω₀ — instead of the corpus's current epistemic,
  preparation-indexed `bornRegion ψ'` on ℂℙⁿ⁻¹. The records this produces are the raw
  material for layer 4.
- **The projection layer (the thesis).** Records in Σ → spacetime, and the **locality
  theorem**: correlations local in Σ, non-local only in the spacetime projection. Not
  started in Lean. This is the real frontier.

Adding gates / algorithms / more empirical QM tests is **calculation-engine breadth** —
legitimate only when labelled as such, never as thesis progress.

## Corrections (do not re-inject these errors)

- **Σ is not to be derived.** "Derive the sector / origin of Σ" (the retired "SO-1"/
  "SL-1" framing) is a **non-question** — Σ is the floor and is everything.
- **QM is not the goal.** It is the calculation engine; proving it (even fully) is the
  floor, not the thesis. "We reproduced QM result X" is not, by itself, progress.
- **CSD *is* a single-trajectory theory.** Do not call the single-trajectory /
  deterministic-flow account a "dead-end CSD rejects." What fails is *time-averaging one
  infinite epistemic unitary trajectory* (`obsFlow_not_ergodic`) — a narrow technical
  fact on ℂℙ, not CSD's mechanism. CSD's typicality is repeated-preparation ignorance
  over Ω₀ on Σ (Paper D). Do not round the narrow no-go up to a rejection of the
  ontology.
- **μFS is settled.** It is the unique SU(n)-compatible measure (Paper B); it is not an
  open "derive the measure from a flow" problem.
- **Paper C is explicitly "a reconstruction, not a derivation"** — it assumes Σ, π, μFS
  and shows closure. That is by design, not a debt.

## Vocabulary discipline (guarded by `check-claims.sh`)

- **A5** = Paper C's projectability / quantum-effective condition on Hamiltonians (it
  *selects* the sector's dynamics). It is **never** "the origin of Σ." Keep it distinct
  from any origin talk; the retired "SL-1" / A5-as-origin mislabels stay forbidden.
- **QM = calculation engine** (from Ω-regions), never "the achievement."
- The finite-QM closure is *the engine demonstrated on a witness*, never "QM derived
  from CSD as the result."

## Drift red flags

- "We prove/reproduce QM" as the headline achievement, rather than as the engine floor.
- Any attempt to "derive Σ" / "explain where Σ comes from" — a non-question.
- Measurement left on the epistemic ℂℙ side (preparation-indexed `bornRegion ψ'`)
  instead of record selection via Ω-basins on Σ.
- The **records → spacetime** projection and the **Σ-local / spacetime-non-local**
  locality resolution dropped, forgotten, or demoted — that IS the thesis.
- QM breadth (gates/algorithms/tests) presented as advancing the thesis.
- "Finite-dimensional QM is derived from CSD" — it is the engine, run on a witness.

## How to use this

Before landing framing/prose/claims, or scoping new work, run the **`csd-foundations`**
agent (`.claude/agents/csd-foundations.md`) against the change or plan, or check it
against this charter yourself. The immediate research frontier is the record layer
(MD-1: Ω-basins + records on Σ) as the substrate for the projection layer
(records → spacetime + the locality theorem) — the actual deliverable.
