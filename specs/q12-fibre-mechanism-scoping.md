# Q12 — the fibre mechanism from de-isolation dynamics: scoping note

**Status:** scoping only. No Lean written. Gates and abort criteria below are to be agreed
*before* any brick starts, on the Q11 mold.

**Charter position.** Q12 is a *constrain-Σ-from-above* item, which is legitimate: it does not
attempt to derive Σ (Σ is the floor, and "derive Σ / SO-1" is retired). It asks whether the
**fibre mechanism** — currently posited — can be forced by dynamics already available.

---

## 1. What Q12 asks

`specs/sigma-fibre-contextuality.md` establishes that for `N ≥ 3` the contextual, record-forming
content must live in the **fibre** of `Σ = base × fibre`, and that a Born-reproducing fibre
partition **exists** (Phase-2b, the Gumbel race, numerically verified at `N = 3`). What is missing
is that the partition is *posited* rather than carved by a flow.

`specs/record-layer-plan.md` §3c narrows this to a two-part factorisation:

* **(B) the rates are the moment map** — `bornRate ψ i = ‖ψ i‖² = momentMap([ψ])ᵢ`.
  **DONE in Lean**: `RecordLayer/MomentMapRace.lean` (`bornRate_eq_momentMap`,
  `bornRate_eq_inner_sq`, `fibreTypicality_bornCell_eq_momentMap`). The Born *square* is
  Kähler-geometric, not injected.
* **(A) the exponential first-passage structure** — for a **mixing** de-isolation flow with
  disjoint environment targets `Aᵢ`, the first target entered is `i` with probability
  `∝ μ(Aᵢ)` (the exponential law for competing hitting sets; Galves–Schmitt / Abadi / Hirata).
  **OPEN.**

Everything funnels into one hypothesis field:

```
structure DeIsolationInteraction (ψ) where
  pointer            : ℝ → Fin n
  measurable_pointer : Measurable pointer
  basin_rate         : ∀ i, fibreTypicality (pointer ⁻¹' {i}) = ENNReal.ofReal (bornRate ψ i)
```

`DeIsolationInteraction.born` is a theorem *given* that field. Q12 is the job of earning it.

---

## 2. ★ Wall-check record — and one finding that reshapes the item

### W1 — **No flow currently in the corpus can supply (A)'s mixing hypothesis.** (New, decisive.)

This was an impression before today; it is now a consequence of machinery the corpus owns.

`MeasureTheory.HasCorrelationDecay.integral_mul_self_eq_of_recurrent` (E6) says: if the
correlation function returns near its lag-zero value at arbitrarily large lags, then summable
correlation decay forces an **a.e. constant observable**. `exists_le_pow_mem_of_compactSpace`
says the powers of any element of a **compact topological group** do exactly that return.

Every flow the corpus has is of that form:

* the base action `p ↦ U • p` for `U : Matrix.unitaryGroup` — `Matrix.unitaryGroup` is a compact
  group (`UnitaryGroup.instCompactSpace`), and this case is already proved:
  `CSD.Thermo.not_hasCorrelationDecay_blockPop_of_unitary`;
* the Kähler fibre flow `LF4.KahlerFlow.kFlow sh p = (p.1, sh + p.2)` — a **shift on `T²`**, i.e.
  translation in a compact group, so the identical argument applies;
* `kProjectedFlow` is literally `id`.

**Consequence.** (A) as stated is not merely unproved in the corpus — its antecedent is
**unsatisfiable by any dynamics the corpus currently defines**. A mixing de-isolation flow cannot
be a unitary base action, cannot be a torus shift, and cannot be built from them by composition
inside a compact group.

This is a limitation on the *route*, not on CSD: mixing environments certainly exist (E5's
doubling-map witness is one). But they are **non-atomic and non-compact-group**, and nothing of
that kind is currently in the corpus's Σ vocabulary.

### W2 — Mathlib provisions the elementary route, not the deep one

* ✅ `Mathlib/Probability/Distributions/Exponential.lean` — the exponential distribution.
* ✅ `Mathlib/Probability/Process/HittingTime.lean` — `hittingBtwn`, `hittingAfter`.
* ❌ **No** exponential law for competing hitting sets; **no** memoryless characterisation
  (`grep` for `memoryless` returns nothing). Galves–Schmitt is not upstream and formalising it
  would be a research-grade project in its own right, not a brick.

### W3 — `DeIsolationInteraction` had **no witness instance** (✅ closed same day by Q12-a)

*As found:* `grep` found only documentation references and the audit pin; no term of the structure
was ever constructed. **Fixed 2026-08-23** — see the Q12-a record below. That is precisely the defect E5 fixed for E4: an interface whose antecedent is never
shown to be satisfiable. Here it plainly *is* satisfiable — `RecordLayer/BornFibrePartition.lean`
already proves `volume_bornCell`, `cdfCell_pairwiseDisjoint` and `fibreOutcome_eq_some_iff` on the
compact fibre `fibreTypicality = volume.restrict (Ico 0 1)` — but nobody has assembled them.

---

## 3. What the wall-check reshapes

Q12 splits cleanly into a **cheap certain part**, a **real but bounded part**, and a **blocked
part**. Before today the third was thought to be the whole item.

---

## 4. Bricks, in order, with gates

### Q12-a — the missing witness (S, certain)

Assemble `fibreOutcome` + `volume_bornCell` into an actual `DeIsolationInteraction ψ`, so the
interface is populated rather than hypothetical.

* **Gate:** none. Either the existing lemmas suffice or they are weaker than they read, and
  finding *that* out is worth the hour.
* **Value:** removes a live non-vacuity hole of exactly the kind E5 just closed elsewhere.
* **Honest caveat to record in the module:** the CDF-stacking pointer imposes an **outcome
  order**, so it is a witness of satisfiability, *not* the canonical symmetric mechanism.

> ### ✅ Q12-a EXECUTED 2026-08-23
>
> ★★ `RecordLayer.cdfDeIsolationInteraction` — every unit state admits a `DeIsolationInteraction`,
> so `DeIsolationInteraction.born` now has a **populated** antecedent. `cdfPointer` makes
> `fibreOutcome` total by sending the leftover to a default outcome; `cdfPointer_preimage` gives the
> basin exactly (cell, plus the leftover only at the default), `measurable_cdfPointer` follows via
> `measurable_to_countable'`, and `fibreTypicality_compl_iUnion_bornCell` shows the leftover is null.
>
> **The gate did its job in an unexpected direction.** Every containment lemma I started to write —
> `cdfCell_subset_Ico`, `bornCell_subset_Ico01`, `fibreTypicality_bornCell`,
> `fibreTypicality_iUnion_bornCell` — **already existed** in `RecordLayer/DeIsolationFlow.lean`. I
> duplicated four of them before the name clash surfaced, and reverted. The witness needed no new
> analysis at all: only `cdfPointer`, its preimage, and the null-leftover step. **Grep the
> neighbouring module before adding lemmas to a mature area**, which is the same
> probe-don't-assume lesson as E6's rotted wall label, one layer down.
>
> Caveats are recorded at the section, in the module header, and on the audit pin: it witnesses
> **satisfiability only** — arbitrary outcome order, and no dynamics carves the cells.

### Q12-b — the symmetric race (M)

Replace order-dependent CDF stacking with **competing exponential clocks**: `n` clocks, clock `i`
at rate `bᵢ`, outcome = first to fire, `P(first = i) = bᵢ` since `Σbᵢ = 1`. This is the canonical
order-free partition §3b asks for, and it is the first genuinely *race*-shaped object in Lean.

* **Probe gate (do first, ~1h):** does Mathlib's exponential API support an independent family and
  a minimum cheaply? Specifically: `expMeasure`/`exponentialPDF` + a product measure + `Finset.inf`
  argmin. If the answer is "hand-roll the density", the brick is still M but the route changes.
* **Abort criterion:** if the independence plumbing exceeds the estimate, stop and record —
  Q12-a already delivers non-vacuity, and Q12-b is an elegance upgrade, not a new claim.

> ### ✅ Q12-b EXECUTED 2026-08-23
>
> **Probe outcome: the gate's premise was wrong in a useful way.** Mathlib *does* have the density
> (`exponentialPDF`), the measure (`expMeasure`), the CDF (`cdf_expMeasure_eq`), boxes
> (`Measure.pi_pi`) and the coordinate split (`measurePreserving_piFinSuccAbove`). Hand-rolling was
> never needed. The cost driver was the **product-measure plumbing**, which the gate had not named,
> and it came in at M–L rather than M. Not aborted: no step was blocked, and one shortcut collapsed
> the worst of it.
>
> `Mathlib/Probability/CompetingExponentials.lean` (Cat-1, 3 pins):
> `raceCell i` (fires strictly first — no index order anywhere in the definition),
> `raceCell_pairwiseDisjoint` (partition content, no hypothesis on the rates),
> ★★ `measure_raceCell` (`P(i wins) = bᵢ/Σⱼbⱼ`) and
> ★★ `measure_raceCell_of_sum_eq_one` (`= bᵢ` for a probability vector).
>
> **The shortcut worth keeping.** `lintegral_exp_neg_expMeasure` evaluates *no* improper integral:
> `e^{-St}` times the `Exp r` density is exactly `r/(r+S)` times the `Exp (r+S)` density, whose mass
> is one by `lintegral_exponentialPDF_eq_one`. Recognising a rescaled density beats integrating it.
>
> **⚠️ Two findings, and the first is decision-relevant for Q12.**
>
> 1. **The race does not fit the corpus's record-layer interface.** `DeIsolationInteraction` takes
>    `pointer : ℝ → Fin n` — a **one-dimensional** fibre — while the race needs `Fin (n+1) → ℝ`.
>    That is not incidental: `record-layer-plan.md` §3b states the minimal fibre dimension is
>    `n − 1`. So **the existing interface is committed to the ordered CDF construction**, and
>    admitting the symmetric mechanism §3b actually asks for would mean generalising it.
>    `cdfDeIsolationInteraction` (Q12-a) remains the only instance. *This is the next natural
>    record-layer question, and it is cheaper than Q12-c.*
> 2. **Strictly positive rates only.** An exponential clock needs `r > 0`, so the theorem covers
>    states with every amplitude nonzero. A zero amplitude is a clock that never fires — right
>    physics, outside `expMeasure`'s domain.
>
> Snags: `Finset.prod_congr` inline in a `rw` leaves metavariables (state it as a `have`);
> `MeasurableSet.nullMeasurableSet` inside a `rw` argument leaves the measure a metavariable (bind
> it first); `lintegral_withDensity_eq_lintegral_mul` produces a **Pi-level** product, so the
> pointwise lemma must be stated in that shape and in the density-first order.

> ### ✅ Q12-b′ EXECUTED 2026-08-23 — finding 1 acted on the same day
>
> The interface mismatch is gone. `DeIsolationInteraction` now takes an **arbitrary fibre**
> `(F, ν)` instead of the hard-wired `ℝ`, so the race instantiates it:
> ★★ `raceDeIsolationInteraction` — for a unit state with every amplitude nonzero, the
> competing-clock race is a `DeIsolationInteraction` on `Fin (n+1) → ℝ`. There are now **two**
> witnesses: the ordered CDF one and the symmetric race one.
>
> Generalising was a strict widening — `map_pointer_apply`'s proof was already fibre-agnostic, and
> the only consumers were inside the module plus the audit pins.
>
> **Extracted at the second consumer** (`CONVENTIONS.md` §9, rule of two):
> `Mathlib/MeasureTheory/CellPointer.lean` — `cellPointer` turns a disjoint measurable cell family
> into a **total** readout by sending the leftover to a default index, and
> ★ `measure_cellPointer_preimage` shows the leftover is null whenever the cell weights already
> exhaust the probability. Q12-a's bespoke `cdfPointer` machinery was deleted and re-derived from
> it, so the argument now exists once rather than twice.
>
> ⚠️ **Neither witness is the dynamical result.** The CDF cells are stacked in index order; the race
> cells are symmetric but their clock law is *posited*; and **no flow carves either family**. That
> remains `Q12-c` and `Q12-d`.

### Q12-c — the characterisation: is the exponential law *forced*? (M–L)

§3c asserts that first-to-fire `∝ bᵢ` for independent linear clocks holds **iff** the waiting
times are exponential. If provable, the fibre law stops being a free choice and becomes a
*derived constraint* — the largest honest step Q12 can take without a mixing flow.

* **Gate:** the memoryless characterisation runs through a Cauchy functional equation. Confirm
  Mathlib has enough (`Analysis/SpecialFunctions`) before starting; if not, this is research.
* **Abort criterion:** if the functional-equation half is not upstream, stop. Do **not** formalise
  Cauchy's equation as a side quest.

> ### ⛔ Q12-c PROBED 2026-08-23 — **not started; the gate fires, though not where it expected to**
>
> **The gate's own question came back "mostly yes".** `AddMonoidHom.toRealLinearMap` solves Cauchy
> for *continuous additive maps on a group*, which is enough for a memorylessness characterisation
> modulo two gaps: the survival function lives on `[0,∞)` and would need extending to `ℝ` to be a
> group hom, and **monotone ⇒ linear is not upstream**, so continuity has to be *assumed* rather
> than derived from monotonicity.
>
> **But the functional equation was not the blocker.** This scoping note wrote "is the exponential
> law *forced*?" as one question. It is two, and §3c states the harder one:
>
> * **(c1) memorylessness ⇒ exponential.** `G(s+t) = G(s)G(t)` with `G` continuous forces
>   `G(t) = e^{-rt}`. Tractable — **M** — via the extension plus `toRealLinearMap`.
> * **(c2) §3c's actual claim:** *first-to-fire `= bᵢ` holds **iff** the waiting times are
>   exponential*. The forward direction is an **integral equation in the unknown law**:
>   `∫ G(x/b) dF(x) = b/(b+1)` for every `b > 0`. Classically this is solved by Laplace-transform /
>   Choquet–Deny methods. That is **research-grade, not a brick**, and the abort criterion applies.
>
> ⚠️ **Correction to `record-layer-plan.md` §3c — of status, not of truth.** The "iff" is classically
> true under mild regularity; nothing here disputes it. What the plan understates is its *cost*: it
> reads as a step one takes in passing, and it is a research formalisation. The phrase "the
> exponential fibre measure is **FORCED**" should be read as *forced in the literature*, not *forced
> in the corpus*.
>
> **What (c1) would and would not buy.** It would narrow the posit from "some memoryless clock law"
> to "the exponential, given the rate" — a family down to a point, which is real. It would **not**
> establish §3c's claim, and a module proving (c1) would sit one careless sentence away from being
> read as if it had. Given how much of this corpus's discipline is about that exact gap, (c1) is a
> **decision for the author**, not a default.
>
> **Recommendation:** leave Q12-c unstarted. Record (c2) as research alongside `Q12-d`; take (c1)
> only if the narrowing is wanted for its own sake, with the labelling agreed in advance.

### Q12-d — the genuine frontier: derive the race from a deterministic flow (**BLOCKED**, foundations)

Exhibit a de-isolation coupling whose environment target-measures are `∝ the moment map`, with the
first-passage structure coming from *mixing* rather than from an assumed clock law.

**W1 says this is blocked in the corpus's current scope, and now says so with a theorem.** The
escape routes, in the order I would rate them:

1. **A genuinely infinite-dimensional environment.** Mixing is available there; but this leaves the
   scope ladder's finite-`N` tier and the corpus has no such object.
2. **Weaken "mixing" to finite-time / approximate decorrelation.** Physically the honest move — real
   environments decorrelate on a timescale, they do not mix asymptotically. E4's engine is already
   *quantitative* (`ε` is an explicit envelope), so a finite-horizon variant is the natural fit.
   **This is the route I would pursue**, and it is the one E4's shape was built for.
3. **Fibre-intrinsic dynamics.** Let the fibre carry the non-compact-group dynamics. Note the
   corpus's fibre is `T²` (compact) while §3c's race wants `ℝⁿ` — the successor question at the
   end of `sigma-fibre-contextuality.md` is exactly this tension, and it is unresolved.

**Do not open Q12-d as a Lean brick.** It is a foundations question, and the memory note saying so
was right.

> ### ✅ Q12-d ROUTE 2 EXECUTED 2026-08-23 — the original stays blocked; the escape is taken
>
> **Q12-d as scoped is untouched**: no de-isolation coupling is exhibited, and `W1` still blocks the
> mixing route. What is now done is **route 2**, which `W1` never blocked.
>
> `MeasureTheory.HasCorrelationDecayUpTo μ Φ f ε T` bounds the correlations only on lags **below
> `T`**, and the two Cesàro estimates now take it. ★★
> `CSD.Thermo.blockPop_timeAverage_le_of_finiteHorizon`: the time average at horizon `T` sits within
> `(2/T) Σ_{u<T} ε u` of the maximally-mixed value. No summability, no limit.
>
> **Why E6 does not reach it.** E6 kills the asymptotic antecedent for every unitary flow — the
> powers recur, so the correlations recur — but that argument needs the bound at *arbitrarily large*
> lags. Over a bounded window it says nothing, and a unitary flow on a large space decorrelates for
> a very long time before recurring. **So E4's conclusion is not lost for finite-dimensional unitary
> Σ-dynamics; its asymptotic form is.** That is the substantive correction to how `W1` should be
> read.
>
> **The weakening was nearly free** — `hdec` was only ever applied at `s, t ∈ Finset.range T`, so
> binding the two membership hypotheses (previously discarded as `_`) sufficed.
> `HasCorrelationDecay.upTo` makes the asymptotic theorems corollaries, so nothing downstream moved.
> Worth noting for its own sake: the original proof had been *finite-horizon all along*, and only
> the hypothesis was stated asymptotically.
>
> ⚠️ **Still conditional, and still not exhibited.** Nothing shows any particular Σ-flow has small
> `ε` on lags below `T`; that is a quantitative estimate about specific dynamics and it remains
> open. What changed is that the hypothesis is no longer *provably unsatisfiable*, which is what E6
> established for the asymptotic version.

### Q12-w — optional, cheap: record W1 as a theorem (S)

One-shot application of `integral_mul_self_eq_of_recurrent` + `exists_le_pow_mem_of_compactSpace`
to `kFlow`, giving "the Kähler fibre flow cannot have decaying correlations either". Worth doing
only if Q12-d is ever written up, since it is the precise statement of why the route is blocked.

---

## 5. Non-goals (charter)

* **Not** deriving Σ. Q12 constrains Σ from above; that distinction is `[[project-a5-so1-distinction]]`
  and must not blur in any module docstring.
* **Not** re-deriving the `N ≥ 3` base-only failure as a Gleason/KS result. It is covariance +
  nonnegativity killing one radial ansatz. `sigma-fibre-contextuality.md` §"This is NOT Gleason".
* **Not** resuming the base-only general-`N` route (parked 2026-07-29, and still parked).
* **Not** claiming any de-isolation Hamiltonian exists. `D1` is untouched by every brick above.

---

## 6. Recommendation

~~Run **Q12-a**~~ **done 2026-08-23**. ~~Next: probe Q12-b~~ **Q12-b done 2026-08-23**. ~~Next candidate: generalise the record-layer interface~~ **done 2026-08-23 (Q12-b′)**. Remaining: **Q12-c2** (§3c's iff) is **research**, alongside **Q12-d** (blocked, W1). **Q12-c1** (memorylessness ⇒ exponential, M) is available but weaker than the row promises — an author decision, not a default.
Treat Q12-c as the stretch. Leave Q12-d closed with W1 recorded as the reason.

The honest headline for the queue: **Q12's frontier half is blocked by a theorem the corpus now
owns, and its remaining half is smaller and more certain than the row's "research" rating
suggests.**

---

## References

`specs/record-layer-plan.md` §3b/§3c; `specs/sigma-fibre-contextuality.md`;
`specs/equilibration-arc-plan.md` (E4/E6, the source of W1); `specs/BACKLOG.md` row Q12;
`RecordLayer/MomentMapRace.lean`, `RecordLayer/BornFibrePartition.lean`,
`RecordLayer/DeIsolationFlow.lean`, `LF4/KahlerFlow.lean`;
`Mathlib/Dynamics/CorrelationDecay.lean`, `Mathlib/Topology/Algebra/CompactRecurrence.lean`;
`specs/future-work.md`.
