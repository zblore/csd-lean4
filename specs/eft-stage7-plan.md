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
| CV-23 | **The Wick closure** — the Stage-6 residues, in three parts. **(a)** the packaged single-formula `δ`-sum over pairings (assembly of the existing `eqFourPoint` table into `Σ_pairings ∏ ½δ` form — per `CONVENTIONS.md` §8.3b this strengthens the existing Propagator table, no new capstone); **(b)** the **time-separated four-point** `⟨vac∣Q_{k₁}(n₁)Q_{k₂}(n₂)Q_{k₃}(n₃)Q_{k₄}∣vac⟩` — Heisenberg factors at distinct periods; the phase bookkeeping rides `heisenberg_phaseDiagU_apply` + `phaseDiagU_pow` exactly as the two-point did; **(c)** the **`2n`-point Wick theorem at the cutoff**, pattern-resolved with the truncation threshold explicit (`n < N` shaped — the honesty that made `eqFourPoint_same` state its `2 < N`). | CV-22 | (a) S, (b) M, (c) **L, GATED** | **(a) DONE 2026-08-17** (`eqFourPoint_wick`); (b) open (clean-context session); (c) gate not yet run |
| CV-24 | **The thermal tier at the cutoff** (`CV/ThermalPropagator.lean`): `thermalFieldState β := gibbsState fieldHamiltonian _ β` with its closed-form diagonal Boltzmann weights; ★ the **thermal two-point function** `⟨Q_k(n) Q_l⟩_β` in closed form, with the vacuum recovered in the `β → ∞` limit (`freeTwoPoint` as a theorem-level limit, not a remark); ★★ **exact KMS at the cutoff** — the first KMS statement in the corpus, and the first join of the two complete verticals (Thermo TH1–TH4 ↔ CV). Relativistic reading by the same substitution as CV-13 (`relFieldHamiltonian`, spacing `ω(m,p)`), recorded not restated. | CV-13, TH3 | M/L | **DONE 2026-08-17** — all landed incl. the `β → ∞` vacuum limit; no residue. See the `future-work.md` CV-24 strike for the full record |
| CV-25 | **Channel-level RG — the scoping session ONLY** (Q11 mold: a doc, not theorems). Map the CPTP coarse-graining candidates (partial trace over decimated modes vs `compressCfg`-conjugation Kraus), fix the norm, and determine whether the existing Duhamel/price ladder already supplies the error budget `ε(λ, τ, distance)`; name the first brick or return the row to unqueued. The Stage-4 no-go is the floor any statement must respect: exact unitary matching is impossible for support-spreading drives, so the target is approximate channel matching with a priced defect. | Stage 4 record, K2 channels | **Research, GATED** | queued |

## CV-23b / CV-23c construction notes (recorded 2026-08-17, so the next session starts warm)

Written at the close of the CV-23a/CV-24 session, in the D3b spirit: nothing below is
proved; it is the worked design so the clean-context session re-derives nothing.

**CV-23b — the time-separated four-point.**

* **Kernel:** define the stroboscopic two-point kernel
  `twoPointKernel τ (n m : ℕ) : ℂ := 2⁻¹ · e^{-i·nτ} · e^{+i·mτ}` (= `½e^{-i(n−m)τ}`,
  kept in two-factor form so ℕ-subtraction never appears). `freeTwoPoint` is
  `twoPointKernel τ n 0`.
* **Target statement (the clean one, `2 < N`):**
  `⟨Q_{k₁}(n₁)Q_{k₂}(n₂)Q_{k₃}(n₃)Q_{k₄}⟩ = δ₁₂δ₃₄·K₁₂K₃₄ + δ₁₃δ₂₄·K₁₃K₂₄ + δ₁₄δ₂₃·K₁₄K₂₃`
  with `K_{ij}` the kernel at the two times — the `eqFourPoint_wick` shape with phases;
  equal times recover CV-23a.
* **The load-bearing identity (worked by hand, checks out):** the level-2 walk
  `0→1→2→1→0` has amplitude `½·e^{-i(t₁+t₂−t₃−t₄)}`, and the two cross-pairings share
  exactly that exponent — `K₁₃K₂₄` and `K₁₄K₂₃` are **each** `¼e^{-i(t₁+t₂−t₃−t₄)}` —
  so their sum equals the walk term. **This is why Wick survives truncation exactly**
  (above threshold), and it is the whole content of the all-equal case. At `N = 2` the
  walk dies and only `K₁₂K₃₄` survives — same honesty as CV-23a.
* **Reusable bricks, all landed:** `heisenberg_freeFieldU_pow_apply` (phase-decorated
  entries, `ThermalPropagator`), `sum_collapse_of_support` + `fieldEnergy_update` +
  `Q_mul_Q_apply` (the single-mode collapse battery, `ThermalPropagator`),
  `diag_entry_mul_of_disjointSupport` + `commute_modeOp` (cross-mode factorisation,
  `Propagator`), and the `eqFourPoint_wick` case-tree skeleton (the mode-pattern
  analysis transfers verbatim; only the values gain phases).
* **Route:** distinct-mode patterns factorise by clustering into evolved two-points
  (each mode walks only to level 1 — no threshold); the all-equal pattern is one
  three-intermediate collapse with the identity above. Expected size M.

**CV-23c — the gate, not yet run.**

* Gate content: the six-point all-equal pattern (`3 < N`) plus one mixed pattern,
  `fin_cases`-free. Target value: `⟨Q⁶⟩ = 15/8` for `3 < N` (Gaussian `5!!·(½)³`).
* Cheapest verification route for the all-equal value: `Q` Hermitian gives
  `⟨0|Q⁶|0⟩ = ‖Q³e₀‖²`, and `Q³e₀ = (3/(2√2))·e₁ + (√3/2)·e₃` for `N > 3`
  (worked by hand: `9/8 + 3/4 = 15/8` ✓). The field-level statement still wants the
  walk-collapse idiom (that is what the gate tests); the vector computation is the
  sanity anchor, not the landing shape.
* At `N = 3` the level-3 path dies; the truncated value differs — state it or guard it,
  per the CV-23a/CV-24 honesty pattern.
* Abort criterion unchanged: if the idiom blows up combinatorially, abort to (a)+(b)
  and return the `2n`-point residue to recorded-not-queued. No shame either way.

**Session snag ledger (also in the Extensions pin block):** `Pi.div` hits the
module-system defeq wall (`Complex.mulAux` unexposed) — bridge via `Pi.div_apply`;
unannotated `∑ m, … oscEnergy m` binders default to ℕ — always annotate `∑ m : Fin N`;
Fin-literal `if_pos`/`if_neg` conditions need show-ascriptions stating the goal's exact
syntactic condition (the B5-geom idiom family).

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
