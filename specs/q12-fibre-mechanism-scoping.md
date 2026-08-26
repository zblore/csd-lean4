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

> ### ✅ **COMPLETED 2026-08-24 — W1 is now a theorem, and a structural one**
>
> As written below, W1 was **half a theorem**: the unitary base action was proved, the `T²` fibre
> shift was asserted by analogy ("the identical argument applies"), and only `kProjectedFlow = id`
> was otherwise covered. Both gaps are closed, and the fix generalised the wall rather than
> enumerating it.
>
> * ★★ `MeasureTheory.not_hasCorrelationDecay_of_compactGroup`
>   (`Mathlib/Dynamics/CompactGroupNoMixing.lean`, Cat-1) — **for any flow `Ψ U` with `U` in a
>   compact group, no observable of nonzero variance has a summable decay envelope**, given only
>   that `V ↦ ∫ f(x)·f(Ψ V x)` is continuous at `1`. So W1 is no longer a list of the three flows
>   the corpus happens to have today; it covers any compact-group flow added later.
> * ★ It is stated with a **bare `Ψ` and `hpow : (Ψ U)^[n] = Ψ (U ^ n)`, not a `MulAction`**,
>   because the two consumers are a multiplicative group action and an **additive** torus shift.
>   `to_additive` then makes one proof serve both; `exists_le_pow_mem_of_compactSpace` gained
>   `@[to_additive]` for the same reason.
> * `not_hasCorrelationDecay_blockPop_of_unitary` was **refactored into a corollary** rather than
>   left as a parallel proof (CONVENTIONS §8.3b), which is what gives the general lemma its second
>   consumer.
> * ★★ `CSD.LF4.not_hasCorrelationDecay_kFlow` (`LF4/KahlerFlowNoMixing.lean`) is the missing half
>   — the `Q12-w` brick below. It came cheap because **the exact correlation is never needed**:
>   shifting the fibre replaces the character `e(x)` by `e(v)·e(x)`, so the observable moves by
>   `Re((e(v) − 1)·e(x))` and the correlation by at most `‖e(v) − 1‖`, a continuous modulus
>   vanishing at `0`. Every Fubini argument is dodged; only the *variance* needs the product
>   structure. The observable reuses `MeasureTheory.circObs`, built as E5's mixing **witness** for
>   the doubling map — here the same function certifies that the fibre flow **cannot** mix, the
>   difference being entirely the map.
>
> ⚠️ **This strengthens the wall; it does not move the frontier.** Mixing systems exist and are
> exactly the ones that are not compact-group translations. What is ruled out is deriving the race
> from **asymptotic** mixing of any dynamics the corpus currently has. `Q12-d` route 2
> (`HasCorrelationDecayUpTo`, finite horizon) is untouched and remains the recommended escape — the
> theorem kills the asymptotic antecedent only.

This was an impression before 2026-08-23; it is now a consequence of machinery the corpus owns.

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
>
> ### ⚠️ The "(c2) is research" verdict above is SUPERSEDED (same day)
>
> It was reached by looking only at the **two-clock** condition, where it is correct — the Mellin
> transform there constrains only the even part of `log E[e^{s log ξ}]`, which is genuinely a
> moment-problem shape. **With the `k`-clock family the problem collapses**: instantiating the race
> at rates `(1, c, c, …, c)` gives `E[G(cξ)^k] = 1/(1+kc)`, turning the integral equation into a
> moment sequence on `[0,1]`, where moments determine the law. Four elementary steps then finish,
> with no Cauchy equation and no Laplace inversion.
>
> Written up in **`specs/q12c-exponential-characterisation-route.md`**: a proof on paper plus a
> mapped Lean project at **L**, needing no mathematics Mathlib lacks (Weierstrass +
> `ext_of_forall_integral_eq_of_IsFiniteMeasure` give the determinacy step). One real caveat: it
> needs races with arbitrarily many clocks, so what is forced is *the exponential law given that a
> single clock law serves every `n`* — which is the measurement-independence CSD has already
> committed to in `sigma-fibre-contextuality.md`.

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

> ### ★ **BRICK (i) DONE 2026-08-24 — and it corrects how W1 should be read**
>
> ⚠️ **`W1` does not say "Σ cannot mix".** It rules out flows whose iterates are the **powers of an
> element of a compact group**. `kFlow` is one, because translations are `T²` acting on itself. An
> **endomorphism** of the same torus is not, because its iterates are powers in a *discrete,
> non-compact* monoid.
>
> ★★ `CSD.LF4.torusDouble_hasCorrelationDecay` (`LF4/KahlerFibreMixing.lean`): the doubling map
> `y ↦ 2y` on the corpus's **own** fibre `KTorus` has correlations that are **exactly zero at every
> nonzero lag**. Same fibre, same observable as `not_hasCorrelationDecay_kFlow`, opposite verdict.
> **So the obstruction is the choice of map, not the ontic space** — Σ is untouched, and route 3
> does not require leaving `T²` after all.
>
> The proof is free: the observable reads one angle, the map acts coordinatewise, so every
> correlation collapses to E5's circle witness.
>
> ⚠️ **Three things it does not settle.** (1) It does not replace `kFlow` — that is the *phase*
> translation, and a phase should translate; `torusDouble` is a candidate for the **de-isolation**
> map. (2) It is **not invertible**, so it is not yet a physically admissible Σ-flow; the invertible
> case is a hyperbolic toral automorphism (cat map), same character argument, extra cost being
> Haar-invariance of a toral automorphism, which Mathlib lacks. (3) ★ **Mixing is not the race** —
> `Q12-d` still needs first-passage times *exponential at moment-map rates*, and that link
> (Galves–Schmitt/Abadi) is `W2`'s research-grade item. **That, not Σ's vocabulary, is the real
> blocker**, which is the correction this brick makes to the reading of `W1`.

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
>
> ### ⚠️ **ROUTE 2 IS CLOSED FOR `kFlow` — 2026-08-24**
>
> The caveat above turned out to be answerable, and the answer is negative for the corpus's own
> fibre flow. ★★ `CSD.LF4.exists_lag_le_envelope` (`LF4/KahlerFlowFiniteHorizon.lean`): for every
> `δ > 0` there is a lag bound `n` such that on **any** horizon `T > n`, a finite-horizon envelope
> for `kFlow sh` must already exceed `1/2 − δ` at some lag in `[1, n]`.
>
> The mechanism is **quantitative recurrence**. Dirichlet's approximation theorem
> (`AddCircle.exists_norm_nsmul_le`, in Mathlib) returns `j • sh` to within `1/(n+1)` of the
> identity at some lag `j ≤ n`, **for every shift**. So the correlation is back near its lag-zero
> value `1/2` at a lag bounded by a number depending only on how close you want to get.
>
> ★ **What is uniform is the whole point.** The bound `n` depends on `δ` **alone** — not on the
> shift, not on the base point, and *not on the horizon*. Route 2's physical picture is a system
> that wanders long enough to decorrelate before recurring; a torus shift has no such room, and the
> bound is blind to every parameter one might hope to tune. Enlarging `T` buys nothing, because the
> return has already happened inside it.
>
> **Non-vacuous**: `ε = 1` does satisfy `HasCorrelationDecayUpTo` (the observable is bounded by
> one), so the hypothesis is satisfiable and "the envelope is `≥ 1/2 − δ` at a small lag" is a real
> constraint rather than an empty one. `exists_lag_envelope_ge_quarter` states it with a number.
>
> ⚠️ **Scope.** This is about `kFlow`, *not* about finite-horizon decorrelation in general. Route
> 2's engine (`blockPop_timeAverage_le_of_finiteHorizon`) is untouched and still correct; what is
> ruled out is **instantiating its antecedent on the Kähler fibre shift**. Nothing here says CSD
> cannot have a de-isolation flow with finite-horizon decorrelation — it says no flow currently in
> the corpus is one. **With `W1`, `Q12-d` now has no route the corpus's present Σ-vocabulary can
> supply**, and the open question is a Σ-vocabulary question, not a proof-technique one.

### ✅ Q12-d — **MIXING FORMULATION RETIRED 2026-08-24** (author decision taken)

**Recommendation: retire `Q12-d`'s *mixing* formulation.** Not because it is hard, but because it
cannot deliver what it promises. Three independent reasons, none about formalisation effort:

1. **Regime mismatch.** Galves–Schmitt/Abadi is a theorem about **rare** sets: `μ A → 0`, with the
   conclusion about `μ(A)·τ_A`. A Born partition has cells of measure `bᵢ` with `Σbᵢ = 1` — order
   one, not vanishing. The theorem's hypothesis is the opposite of the regime `§3c` lives in, so it
   cannot be instantiated where the record layer needs it.
2. **Exact versus asymptotic — this is `Q12-c2` talking.** `hasRaceProperty_iff_exists_expMeasure`
   says the race gives *exactly* `bᵢ/Σb` **iff** the clock law is *exactly* exponential. A
   hitting-time limit theorem gives exponential only in a limit, so the "derived" construction would
   yield Born asymptotically — **strictly weaker than `measure_raceCell`, which already proves it
   exactly.** The derivation would trade an exact result for an approximate one.
3. **Independence.** The race needs `n` **independent** clocks. A single deterministic trajectory on
   Σ is one process, and hitting times of the `n` cells along one orbit are strongly dependent — the
   same orbit. ★ **The fibre is not scaffolding standing in for work not yet done: it is carrying the
   independence that base dynamics cannot supply.** That is why it is there.

**So `Q12-d` is not one theorem away — it is mis-specified**, and closing it honestly means retiring
the target rather than proving it. A correct successor question would ask what structure supplies
the *independence*, which is where the content actually sits.

✅ **Executed 2026-08-24.** `Q12-d`'s mixing formulation is **retired**. It is not "blocked" and not
"open" — it is **withdrawn as mis-specified**, and should not be reopened in that form.

**The successor question, for whoever picks this up:** ⚠️ **CORRECTED 2026-08-26 — this read "what
structure supplies the independence of the outcome clocks?" and that is WITHDRAWN** (`CSD-CHARTER.md`
carries the reasoning). Time in Σ is a single shared parameter (`flow : ℝ → Σ → Σ`, P3), so the
"clocks" are Σ-aligned deterministic readings, not independent processes; and the proved Born
construction never raced anything — `volume_circleCell` gives the weights as ARC LENGTHS of a
partition of ONE uniformly-distributed fibre coordinate. Nothing needs supplying.

*The successor question is: **what physical de-isolation interaction generates a READOUT whose level sets carry the Born measures? (⚠️ scope carefully -- there are TWO partitions. The Omega-regions on the projective BASE are EPISTEMIC, a calculation space (Paper C A7); nothing sculpts them and they match volume because mu_FS is forced by symmetry and the weights are the moment map. The FIBRE cells are a different object: BornFibrePartition.lean places them on the ONTIC fibre and calls the outcome the ontic selection of which cell the fibre point occupies -- while adding that the CDF family is ONE concrete realisation, the content being the interface plus the measure identity. So the cell SHAPES are bookkeeping; the fibre, the rates and the selection are not. The obligation is DeIsolationFlow.lean's: exhibit a pointer p = readout . flow(H_int(M)) whose basins are cdfCell(moment map).)*** That is
the `H_int` question, and unlike the withdrawn version it IS about Σ's dynamics. Retiring the mixing
route was right; the successor question was mis-stated.

**What was salvaged instead** — ★★ `MeasureTheory.tsum_measure_lt_returnTime` (Kac's formula,
`Mathlib/Dynamics/Kac.lean`, Cat-1, absent from Mathlib). Kac is the one piece that is
**regime-correct**: it needs no rarity hypothesis, holding for *any* cell of positive measure. It
gives mean return time `= 1/μ A`, so a cell of Born weight `bᵢ` is returned to on average every
`1/bᵢ` steps — **feature (B) of `§3c`, the rates, derived from the dynamics instead of posited.**
`CSD.LF4.kac_doubling` instantiates it on brick (i)'s map, which is also the non-vacuity check.
⚠️ It gives the **rates**, not the **law**; by reason 2 above, nothing regime-correct gives the law.

---

### Q12-w — ✅ **DONE 2026-08-24** (was: optional, cheap: record W1 as a theorem (S))

Scoped as a one-shot application of `integral_mul_self_eq_of_recurrent` +
`exists_le_pow_mem_of_compactSpace` to `kFlow`. Executed as something better: the argument was
**extracted into a general theorem about compact-group flows** first
(`not_hasCorrelationDecay_of_compactGroup`), and `kFlow` and the unitary action are both now
corollaries of it. See the W1 box above.

★ Worth carrying: the scoping note said this was worth doing "only if Q12-d is ever written up".
That undersold it. Doing it turned W1 from an enumeration of the corpus's current flows into a
statement about a *class* of flows — which is the form in which a wall is actually useful, because
it says what an escape must avoid rather than what happens to be present.

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
