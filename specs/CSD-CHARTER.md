# CSD Charter — the north star (read before framing claims or scoping work)

> **Purpose.** One page stating what this project is *for* right now, so work does not
> drift into "just reproducing QM." The current goal is to **complete the reconstruction
> of QM from Σ and Ω-regions** — genuinely, on the ontic surface — not to accumulate more
> QM results on the epistemic side. This is the anchor the `csd-foundations` agent
> enforces. It states the mission and the guardrails; it does **not** hold open items
> (those live in [`BACKLOG.md`](BACKLOG.md)) or the detailed status (that is
> [`reconstruction-status.md`](reconstruction-status.md)).

## The picture

**Σ is the floor, and Σ is everything.** The ontic surface Σ is the total, fixed,
**local** space of everything that exists — nothing beneath it, nothing outside it, it
does not grow. Physical reality is a **single deterministic trajectory** ω(t) on Σ under
a Liouville-preserving flow. All indeterminacy is epistemic — ignorance of exactly
*where* in a prepared region Ω₀ ⊂ Σ the microstate is. **Deriving Σ is a non-question**
(the retired "SO-1 / derive the sector" framing); Σ is posited as complete local reality.

**But constrain Σ ≠ derive Σ.** Σ is not directly seen (we observe only the epistemic
projection), so it must *not* be treated as a free, arbitrary posit: **constraining Σ as
tightly as possible — from above, from what it must do (give QM via Ω-regions, support the
records) — is legitimate, valuable work.** The more forced / less arbitrary the hidden Σ,
the stronger the theory. Deriving Σ (from beneath) is the non-question; *constraining* it
(from the requirements) is not. The structure-forcing results — μ_FS the **unique**
SU(n)-compatible measure, the U(N) symmetry, the Kähler structure, minimality — are exactly
this constraint work (not a frontier *like the record layer*, but not to be dismissed).

**QM arises from Ω-regions on Σ.** A measurement context partitions the prepared region
into outcome basins {Ωᵢ}; the invariant volume ratios μ(Ωᵢ)/μ(Ω₀) are the outcome
weights, and — via typicality over repeated preparations (classical-statistical-mechanics
ignorance of the microstate in Ω₀; Paper A) together with the SU(n)-fixed measure μ_FS
(Paper B) — they are the Born weights |⟨i|ψ⟩|². The rest of QM (Schrödinger dynamics,
composite structure, contextuality) follows on the same footing. **QM is the calculation
engine born from the Ω-region structure — reproducing it is the point, but only when it
genuinely arises from Σ and Ω.**

## The goal now — complete the Σ+Ω reconstruction of QM

The immediate deliverable is to make **the whole of finite-dimensional QM arise from Σ and
Ω-regions**, on the ontic surface, with no epistemic shortcuts. The corpus has the
calculation engine running on a projective *witness*, but two things are not yet genuine:

- **Measurement must be a record on Σ — the near frontier.** Measurement = de-isolation =
  **record selection via context-fixed Ω-basins on Σ**: a partition of Ω₀ determined by
  the apparatus (not the preparation), the record being *which basin the single trajectory
  occupies* — a **selection of structure already in Σ** (Σ does not grow). The corpus
  currently does measurement on the *epistemic* side — `vnPointerOutcome` via
  `bornRegion ψ'` on ℂℙⁿ⁻¹, preparation-indexed — which is the wrong side. Completing the
  reconstruction means moving measurement onto Σ as genuine Ω-basins + records.
  > Separate preparation laws from context-fixed outcome partitions, then derive the
  > outcome probabilities by integrating the preparation law over those fixed regions.
- **The engine currently runs on a witness with μ_FS and `exp(-itH)` built in.** That
  demonstrates closure; it is not yet QM *arising from* a more primitive Σ+Ω account
  (Paper C is explicitly "a reconstruction, not a derivation" — that is by design, but the
  ontic Ω-region account is what we are completing).

## What is NOT the current goal

- **Adding QM breadth** — more gates, algorithms, empirical tests on the epistemic side —
  is *not* completing the reconstruction. It is legitimate only when labelled as breadth.
- **"Deriving Σ."** A non-question; Σ is the floor.
- **The deeper research direction beyond the QM reconstruction is intentionally kept out
  of the public docs for now.** First complete QM from Σ + Ω.

## Corrections (do not re-inject these errors)

- **Σ is not to be derived.** "Derive the sector / origin of Σ" (retired "SO-1" / "SL-1")
  is a non-question.
- **CSD *is* a single-trajectory theory.** Do not call the single-trajectory /
  deterministic-flow account a "dead-end CSD rejects." What fails is time-averaging one
  infinite epistemic unitary trajectory (`obsFlow_not_ergodic`) — a narrow ℂℙ fact, not
  CSD's mechanism. CSD's typicality is repeated-preparation ignorance over Ω₀ on Σ.
- **μ_FS is settled** (unique SU(n)-compatible measure, Paper B) — not an open "derive the
  measure from a flow" problem.
- **A5** = projectability (Paper C), never "the origin of Σ."

## Vocabulary discipline (guarded by `check-claims.sh`)

- **A5** = Paper C's projectability / quantum-effective condition — never "the origin of Σ."
- The finite-QM closure is *the calculation engine demonstrated on a witness*, never "QM
  derived from CSD as the result."
- The retired "SL-1" / A5-as-origin mislabels stay forbidden.

## Drift red flags

- Reproducing QM on the *epistemic* side (more results, gates, algorithms) presented as
  completing the reconstruction.
- Any attempt to "derive Σ" / explain Σ's origin — a non-question.
- Measurement left on the epistemic ℂℙ side (preparation-indexed `bornRegion ψ'`) instead
  of record selection via Ω-basins on Σ — the near frontier.
- The witness closure called "QM derived from CSD."

## How to use this

Before landing framing/prose/claims, or scoping new work, run the **`csd-foundations`**
agent (`.claude/agents/csd-foundations.md`) against the change or plan, or check it
against this charter yourself. The immediate frontier is **the record layer** — measurement
as record selection via Ω-basins on Σ — as the step that makes QM genuinely arise from Σ
and Ω.
