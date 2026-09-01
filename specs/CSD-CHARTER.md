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
calculation engine running on a projective *witness*, with two honest status notes (the first now
resolved in Lean, the second the standing posit):

- **The record — the KINEMATIC interface is BUILT (2026-07-25).** *Addendum 2026-08-02 — the
  DYNAMICAL layer now exists and most of what this bullet listed as open has closed:* records are
  **dynamically created** from a positive-measure ready state by an explicit measure-preserving
  propagator, persist, and carry the Born weights (`SwapClosure`); A7 is **discharged** at every
  `N` (fibred reading canonical, `GlobalBasin` + the dynamical realisation); the Lüders update is
  a pushforward theorem, rank-one (`swap_luders_born`) **and** degenerate (on the projective join,
  `join_block_luders`, Liouville-preserving); the `H_int` question resolved as the
  **piecewise-Hamiltonian classification** (seams provably forced + null). Still open: the
  join-arena protocol plumbing and the items in `BACKLOG.md`. The original bullet follows,
  unedited, as the historical record. **(Original:) MD-1 was NOT discharged at that date.**
  ⚠️ *Scope corrected 2026-07-28 (external review): general-`N` A7 (`Ωᵢ(M)` from the apparatus
  alone) is proved only at `N=2`, the partition here being preparation-indexed; the de-isolation
  `H_int` is not constructed; and the fibred Σ is a measurable record model, not a proven A1
  sector. See `record-layer-plan.md` and `BACKLOG.md`.* Measurement = de-isolation, formalized
  end-to-end
  (`record-layer-plan.md §4`). The model space is **Σ = base × fibre** (`FibredSigma`): the base
  `ℂℙⁿ⁻¹` is the *epistemic* projective point (pinned to `[ψ]` for a sharp prep), the fibre the
  *ontic* record coordinate. A measurement is **`context + unknown microstate → record`**
  (`Measurement`): the context fixes the basin partition, the unknown microstate selects the basin
  it occupies, and the combined result is a genuine postulate-P5 `RecordSemantics` record. The
  outcome probabilities are the **Kähler torus moment map** (`MomentMapRace` — forced, not injected),
  and Born is nothing but the **law of large numbers over the unknown initial microstate**
  (`Measurement.bornMeasurement_frequency`; randomness = ignorance of the initial condition). The
  Ω-regions stay epistemic (on ℂℙ) — they were *not* relocated to Σ; the record is the ontic
  selection in the fibre. Realized on the corpus's actual Σ (`KSigmaRecord`,
  `born_frequency_region_eq_record`).
  > Done: preparation laws (the base/epistemic point) separated from the context-fixed outcome
  > partition (the fibre), with the outcome probabilities the LLN over the unknown microstate.
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
- Re-proposing **base-only context-fixed regions for `N ≥ 3`**, or attributing that wall to Gleason.
  **Structural lesson ([`sigma-fibre-contextuality.md`](sigma-fibre-contextuality.md)):** Born =
  typicality volume for all `N` (theorem), but measurement contextuality lives on the base only at
  `N = 2` (`CP¹ = S²` accident) and, at `N ≥ 3`, **in the fibre by author decision against a tight
  but unclosed constraint chain** — ⚠️ base-only at `N ≥ 3` is **open in both directions**, and
  "necessarily in the fibre" was retracted 2026-07-28 (this line still carried it until
  2026-08-25). This is a *constraint on Σ's structure* (the fibre is load-bearing), not a defect — and it is **not** Gleason (CSD is
  contextual). ⚠️ **Frontier restated 2026-08-24.** This line previously read "deriving the fibre
  mechanism from a de-isolation dynamics is the open frontier". That formulation — derive the
  first-passage race from a **mixing** de-isolation flow — was **retired as mis-specified**, not
  merely hard: the hitting-time limit theorems need vanishingly rare sets while a Born partition's
  cells sum to one; an asymptotic law would deliver the Born weights only in a limit, weaker than the
  corpus already proves exactly; and the race needs **independent** clocks, which one deterministic
  trajectory cannot supply. ⚠️ **SUCCESSOR QUESTION CORRECTED 2026-08-26 (author call). This line
  previously read: "the fibre carries the independence the base cannot … the open question is now
  what structure supplies the independence." That framing is WITHDRAWN — it was over-fitted to the
  very race picture the retirement discarded, and it pointed work at a property the corpus does not
  use.**

  Three things settle it. **(1) Time in Σ is single and shared.** `ConstraintDynamics.flow :
  OnticTime → Σ → Σ` (`OnticTime := ℝ`) is ONE one-parameter group acting on all of Σ (P3). There
  are no per-outcome clocks in the ontology; there is one flow and one microstate, so the "clocks"
  are Σ-aligned deterministic readings, maximally dependent, not independent processes. **(2) The
  proved Born construction never used a race.** `RecordLayer/CircleFibre.lean`'s `circleCell` cuts
  the fibre circle into consecutive ARCS at the running sums of the rates, and ★ `volume_circleCell`
  gives the Born weight as the ARC LENGTH under Haar. One uniformly-distributed fibre coordinate,
  partitioned. No independence anywhere, because there is only one variable. **(3) So there is
  nothing to supply.** The question presupposed independent stochastic processes; CSD has none, wants
  none, and derives Born without them.

  ★ **Keep two senses of "independence" apart, permanently.** *Dynamical* independence — separate
  processes running in time — CSD does not have and does not need. *Measure factorisation* — the
  typicality measure on the fibre factorising — is a property of the ignorance distribution over
  starting points, is legitimate, and is what the Gumbel construction and the Q10 conjecture actually
  use. Conflating them is what produced the withdrawn framing.

  **⚠️ RESOLVED 2026-08-31/09-01 — read this before quoting the paragraph below.** This section
  and §"How to use this" answered the same question opposite ways; the author's MD-1 closure
  settles it, and the split is between two things this paragraph ran together. **Which physical
  interaction an apparatus realises** is a modelling input, outside the Lean claim by design and
  permanently (`R-015`) — the same input Bohm and Everett take, and not a debt. **The chart→arena
  transport of Hamiltonian generation** is mathematics and stays open (`R-016`); chart-level
  generation was proved 2026-09-01 (`SigmaLayer/ChartIntegralCurve.lean`), and globalising is
  obstructed by the flux theorem, not by tooling. So "no `H_int(M)` produces the basins" is
  **withdrawn as a statement of open work** and retained only as the boundary it names. The
  paragraph is kept below because the *scoping* in it (the two partitions) is still exactly right.

  **The question as it was originally framed:** the mechanism is still underived — no
  `H_int(M)` produces the basins — and the successor question is **what physical de-isolation interaction generates a READOUT whose level sets carry the Born measures? (⚠️ scope carefully -- there are TWO partitions. The Omega-regions on the projective BASE are EPISTEMIC, a calculation space (Paper C A7); nothing sculpts them and they match volume because mu_FS is forced by symmetry and the weights are the moment map. The FIBRE cells are a different object: BornFibrePartition.lean places them on the ONTIC fibre and calls the outcome the ontic selection of which cell the fibre point occupies -- while adding that the CDF family is ONE concrete realisation, the content being the interface plus the measure identity. So the cell SHAPES are bookkeeping; the fibre, the rates and the selection are not. The obligation is DeIsolationFlow.lean's: exhibit a pointer p = readout . flow(H_int(M)) whose basins are cdfCell(moment map).)** That is the `H_int` question, and it is about Σ's dynamics, not
  about supplying a probabilistic structure. Retiring the mixing route was right; the successor
  question was mis-stated.
- The witness closure called "QM derived from CSD."

## Repository architecture (decided 2026-08-06)

**`csd-lean4` is the unified formal repository for the complete CSD quantum
programme. External Lean libraries provide generic mathematical and physical
infrastructure through explicit interoperability layers.** One repository, one theorem
graph — no satellite CSD repos (they would break end-to-end claims). External libraries
(Mathlib now; Physlib / a QIT provider when toolchains align and a concrete need
exists) sit *underneath* as dependencies: they own generic objects, `csd-lean4` owns
the CSD theorems about them. Rules, ownership table, and the four-way
check-before-implementing classification: [`external-library-map.md`](external-library-map.md);
adapters live in `CsdLean4/Interop/`.

## How to use this

Before landing framing/prose/claims, or scoping new work, run the **`csd-foundations`**
agent (`.claude/agents/csd-foundations.md`) against the change or plan, or check it
against this charter yourself. The record layer — the step that makes QM's measurement genuinely
arise from Σ + Ω — is now **built** (2026-07-25, `record-layer-plan.md §4`; MD-1 closed 2026-08-31,
residuals `R-015` boundary and `R-016` open — this is the half of the former contradiction that
was right): measurement =
`context + unknown microstate → record` on the base×fibre Σ, outcome probabilities = the Kähler
moment map, Born = the law of large numbers over the unknown microstate. What remains is optional
(a mechanical field naming in the pinned closure, no new theorem) or unrelated open tiers (Lindblad,
the Kähler 2-form) — not a foundational frontier.
