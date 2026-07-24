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

**QM arises from the (epistemic) Ω-region partition + the ontic typicality volume — two
levels, kept distinct.** A measurement context M fixes an **epistemic** outcome partition
**{Ωᵢ(M)} ⊂ ℂℙⁿ⁻¹** — context-defined, μ_FS-null boundaries (Paper C A7). **The Ω-regions
are EPISTEMIC, not ontic.** The outcome weight is the **ontic typicality volume ratio**
`μL(π⁻¹Ωᵢ(M) ∩ Ω₀) / μL(Ω₀)` on Σ (equivalently `∫_{Ωᵢ(M)} ρ_ep dμ_FS`), which — via
typicality over repeated preparations (ignorance of the microstate in Ω₀; Paper A) + the
SU(n)-fixed μ_FS (Paper B) — is the Born weight |⟨i|ψ⟩|². So: **the regions are epistemic (on
ℂℙ); the measure/typicality that weights them is ontic (μL over Ω₀ ⊂ Σ).** QM is the
calculation engine born from this structure.

## The goal now — complete the Σ+Ω reconstruction of QM

The immediate deliverable is to make **the whole of finite-dimensional QM arise from Σ and
Ω-regions**, on the ontic surface, with no epistemic shortcuts. The corpus has the
calculation engine running on a projective *witness*, but two things are not yet genuine:

- **The record — the near frontier.** Measurement = de-isolation. The apparatus context M
  fixes the **epistemic** partition {Ωᵢ(M)} ⊂ ℂℙⁿ⁻¹; the single trajectory's projection lands
  in one region, and **the record is the ontic selection in Σ** of which one — equivalently
  which `π⁻¹(Ωᵢ(M))` basin ω(t) occupies (a **selection of structure already in Σ**; Σ does
  not grow). Born = the prepared density integrated over the fixed epistemic regions. **The
  corpus's gap is two things, neither of them "move the regions onto Σ":** (1) `bornRegion ψ'`
  is **preparation-indexed** (defined from the state ψ'), not **context-fixed** {Ωᵢ(M)}
  (defined from the apparatus M) — *both are epistemic*; and (2) the record is not yet realized
  as the ontic selection in Σ. **The Ω-regions stay epistemic (on ℂℙ) — do NOT relocate them to Σ.**
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
- Measurement outcome regions **preparation-indexed** (`bornRegion ψ'`) instead of
  **context-fixed** {Ωᵢ(M)} — both epistemic; and the record not realized as the ontic
  selection in Σ. (The Ω-regions are epistemic; do not "relocate them to Σ".)
- The witness closure called "QM derived from CSD."

## How to use this

Before landing framing/prose/claims, or scoping new work, run the **`csd-foundations`**
agent (`.claude/agents/csd-foundations.md`) against the change or plan, or check it
against this charter yourself. The immediate frontier is **the record layer** — context-fixed
**epistemic** outcome regions {Ωᵢ(M)} on ℂℙ, with the **record the ontic selection in Σ** of
which region the trajectory realizes — the step that makes QM's measurement genuinely arise
from Σ + Ω.
