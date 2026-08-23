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

### W3 — `DeIsolationInteraction` has **no witness instance**

`grep` finds only documentation references and the audit pin; no term of the structure is ever
constructed. That is precisely the defect E5 fixed for E4: an interface whose antecedent is never
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

### Q12-b — the symmetric race (M)

Replace order-dependent CDF stacking with **competing exponential clocks**: `n` clocks, clock `i`
at rate `bᵢ`, outcome = first to fire, `P(first = i) = bᵢ` since `Σbᵢ = 1`. This is the canonical
order-free partition §3b asks for, and it is the first genuinely *race*-shaped object in Lean.

* **Probe gate (do first, ~1h):** does Mathlib's exponential API support an independent family and
  a minimum cheaply? Specifically: `expMeasure`/`exponentialPDF` + a product measure + `Finset.inf`
  argmin. If the answer is "hand-roll the density", the brick is still M but the route changes.
* **Abort criterion:** if the independence plumbing exceeds the estimate, stop and record —
  Q12-a already delivers non-vacuity, and Q12-b is an elegance upgrade, not a new claim.

### Q12-c — the characterisation: is the exponential law *forced*? (M–L)

§3c asserts that first-to-fire `∝ bᵢ` for independent linear clocks holds **iff** the waiting
times are exponential. If provable, the fibre law stops being a free choice and becomes a
*derived constraint* — the largest honest step Q12 can take without a mixing flow.

* **Gate:** the memoryless characterisation runs through a Cauchy functional equation. Confirm
  Mathlib has enough (`Analysis/SpecialFunctions`) before starting; if not, this is research.
* **Abort criterion:** if the functional-equation half is not upstream, stop. Do **not** formalise
  Cauchy's equation as a side quest.

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

Run **Q12-a** (certain, closes a real non-vacuity hole), then **probe** Q12-b before committing.
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
