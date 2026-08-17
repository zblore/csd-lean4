# EFT Stage 7 plan: the Wick closure and the thermal tier

Status: **SCOPED 2026-08-17** (BACKLOG row **Q21**; rows CV-23..CV-25 in
[`future-work.md`](future-work.md)). Deliverable of this document: the stage's
brick queue with gates and abort criteria, feasibility checked up front — no
theorems claimed here.

## Where Stage 6 left the chain

Stage 6 closed same-day (velocity, clustering, the four-point table) with three
residues recorded and unqueued: the packaged single-formula `δ`-sum, the
time-separated four-point, and higher `2n`-point Wick. Two postures stand
untouched and Stage 7 does not reopen them: **no continuum limit**
(`ApproxCCR.no_exact_finite_ccr`) and **RG-as-theorems unqueued** (the Stage-4
`exists_unitary_compress_not_unitary` no-go re-scoped it to channel level).
Separately: the Thermo track (TH1–TH4) has been COMPLETE since 2026-07-07 and
has never been joined to the CV vertical — the corpus has Gibbs states and a
free field but no thermal field statement, and **no KMS anywhere** (verified
2026-08-17, zero hits).

## Feasibility, checked before scoping (the check-impossible-first record)

* **Walk-collapse scales with explicit thresholds.** The four-point table's
  truncation honesty (`eqFourPoint_same` needs `2 < N`; at `N = 2` the value is
  `1/4`, not the Gaussian `3/4`) generalises: the `2n`-point all-equal pattern
  needs the tridiagonal `Q` entry lemmas through level `n` and holds only above
  an explicit cutoff threshold (`n < N` shaped). The entry-lemma ladder exists
  through level 2 (`Q_zero_one`, `Q_one_two`, symmetric halves); each new level
  is one lemma in the same shape. No wall — but combinatorial growth is real,
  hence the CV-23c gate.
* **`gibbsState` is index-generic** (`{n : Type*} [Fintype n] [DecidableEq n]`,
  `Thermo/FreeEnergy.lean`), so it applies to `FieldConfig K N` verbatim; and
  `fieldHamiltonian` is **diagonal** in the configuration basis, so the Gibbs
  state is the explicit diagonal Boltzmann matrix with finite-geometric-sum
  normalisation — closed forms available, no spectral machinery needed.
* **Finite-dimensional KMS is algebra, not analysis.** For diagonal `H` the
  complex-time Heisenberg evolution is entrywise `e^{iz(E_c − E_d)}`, total and
  well-defined at every `z : ℂ`; the KMS identity
  `⟨A(t)B⟩_β = ⟨B A(t+iβ)⟩_β` is an entrywise exponential shuffle. No analytic
  continuation apparatus, no operator-algebraic KMS theory required at the
  cutoff. This is why CV-24 is M/L and not research.
* **Import direction clean:** Thermo imports nothing from CV, so
  `CV/ThermalPropagator.lean` importing both `CV/Propagator` and
  `Thermo/FreeEnergy` is cycle-free.

## Rows

| # | Item | Deps | Size | Status |
|---|---|---|---|---|
| CV-23 | **The Wick closure** — the Stage-6 residues, in three parts. **(a)** the packaged single-formula `δ`-sum over pairings (assembly of the existing `eqFourPoint` table into `Σ_pairings ∏ ½δ` form — per `CONVENTIONS.md` §8.3b this strengthens the existing Propagator table, no new capstone); **(b)** the **time-separated four-point** `⟨vac∣Q_{k₁}(n₁)Q_{k₂}(n₂)Q_{k₃}(n₃)Q_{k₄}∣vac⟩` — Heisenberg factors at distinct periods; the phase bookkeeping rides `heisenberg_phaseDiagU_apply` + `phaseDiagU_pow` exactly as the two-point did; **(c)** the **`2n`-point Wick theorem at the cutoff**, pattern-resolved with the truncation threshold explicit (`n < N` shaped — the honesty that made `eqFourPoint_same` state its `2 < N`). | CV-22 | (a) S, (b) M, (c) **L, GATED** | queued |
| CV-24 | **The thermal tier at the cutoff** (`CV/ThermalPropagator.lean`): `thermalFieldState β := gibbsState fieldHamiltonian _ β` with its closed-form diagonal Boltzmann weights; ★ the **thermal two-point function** `⟨Q_k(n) Q_l⟩_β` in closed form, with the vacuum recovered in the `β → ∞` limit (`freeTwoPoint` as a theorem-level limit, not a remark); ★★ **exact KMS at the cutoff** — the first KMS statement in the corpus, and the first join of the two complete verticals (Thermo TH1–TH4 ↔ CV). Relativistic reading by the same substitution as CV-13 (`relFieldHamiltonian`, spacing `ω(m,p)`), recorded not restated. | CV-13, TH3 | M/L | queued |
| CV-25 | **Channel-level RG — the scoping session ONLY** (Q11 mold: a doc, not theorems). Map the CPTP coarse-graining candidates (partial trace over decimated modes vs `compressCfg`-conjugation Kraus), fix the norm, and determine whether the existing Duhamel/price ladder already supplies the error budget `ε(λ, τ, distance)`; name the first brick or return the row to unqueued. The Stage-4 no-go is the floor any statement must respect: exact unitary matching is impossible for support-spreading drives, so the target is approximate channel matching with a priced defect. | Stage 4 record, K2 channels | **Research, GATED** | queued |

## Gates and abort criteria (agreed in advance, per the Stage-5 precedent)

* **CV-23c gate:** the six-point all-equal pattern (`3 < N`) plus one mixed
  pattern must land with the walk-collapse idiom `fin_cases`-free and the
  threshold explicit. If the idiom blows up combinatorially, **abort to
  (a)+(b) only** — the four-point table remains the headline and the `2n`-point
  residue returns to the recorded-not-queued state. No shame recorded either
  way.
* **CV-25 gate:** one focused scoping pass. If no statement with a *provable*
  error budget emerges, the row returns to unqueued research and says so —
  the Stage-4 record is not to be re-litigated by optimism.

## Non-goals (Stage 7)

- **No continuum limit** — the `ApproxCCR.no_exact_finite_ccr` posture stands.
- **No RG theorems** — CV-25 is a scoping session; theorems are a Stage-8+
  decision gated on its outcome.
- **No velocity optimality, no price attainment** — both stay ledger notes.
- **The departures tower** (`csd-departures-eft.md`) stays theory-gated on the
  papers pinning the correction form — it is the horizon this stage walks
  toward, not a row.

## Labelling (charter)

Stage 7 is **breadth, honestly labelled**: the CV/EFT chain is the
isolated-piece image of Σ's operating rules, not the Σ+Ω reconstruction
frontier (that remains Q10/Q12/Q13). It is where empirical contact lives, which
is its justification; it is not sold as reconstruction progress.

## References

`specs/BACKLOG.md` (row Q21; the §CV chain row);
[`eft-stage6-plan.md`](eft-stage6-plan.md) (the residues this stage takes up);
[`future-work.md`](future-work.md) (rows CV-23..CV-25);
`CV/Propagator.lean` (the walk-collapse idiom, `Q` entry ladder, `eqFourPoint`
table); `Thermo/FreeEnergy.lean` (`gibbsState`, index-generic);
`CV/DynamicalLocality.lean` (`heisenberg_phaseDiagU_apply`);
`CONVENTIONS.md` §8.3b (capstone discipline — CV-23a strengthens in place).
