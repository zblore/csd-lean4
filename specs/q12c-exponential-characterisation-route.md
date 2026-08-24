# Q12-c2 — a route to "the exponential clock law is forced"

**Status: ✅ DONE 2026-08-24. `record-layer-plan.md` §3c is a corpus theorem** —
`ProbabilityTheory.hasRaceProperty_iff_exists_expMeasure` in
`Mathlib/Probability/IidClockRace.lean`, `sorry`-free, five pins.

⚠️ **Read §5a before reusing this memo.** The route below is *not* the route that closed it. Steps
1 and 2 landed as written (step 2 stronger than written); steps 3 and 3′ — the Hausdorff-determinacy
work in `MomentDeterminacy.lean` — turned out **not to be needed for this result at all**. §5a
records what replaced them and why, because the lesson generalises.

**Supersedes my own assessment of 2026-08-23**, recorded in `q12-fibre-mechanism-scoping.md`, that
c2 is "research-grade, not a brick". That verdict came from looking only at the **two-clock**
condition, where it is correct. With the **`k`-clock family** the problem collapses.

---

## 1. What c2 asks

`record-layer-plan.md` §3c: *for iid linear clocks, first-to-fire `= bᵢ` holds **iff** the waiting
times are exponential.* The `⇐` direction is `Q12-b`
(`ProbabilityTheory.measure_raceCell_of_sum_eq_one`). This memo is about `⇒`.

Setup: `ξ₁, ξ₂, …` iid on `(0, ∞)` with survival function `G(t) = P(ξ > t)`; clock `i` has rate
`bᵢ` and fires at `ξᵢ / bᵢ`; the race property is `P(argminⱼ ξⱼ/bⱼ = i) = bᵢ / Σⱼ bⱼ` for every
rate vector.

**Why two clocks is the wrong place to look.** With `n = 2` and ratio `c = b₂/b₁` the condition is
`E[G(cξ)] = 1/(1+c)`, an integral equation in the unknown law. Taking Mellin transforms turns it
into `E[ξˢ]·E[ξ⁻ˢ] = Γ(1+s)Γ(1−s)`, which constrains only the **even part** of `log E[e^{sY}]`,
`Y = log ξ`. That is a moment-problem shape, and it is why the two-clock version looks like
Choquet–Deny territory.

---

## 2. ★ The insight: use `k` identical clocks

Instantiate the race property at the rate vector `(1, c, c, …, c)` — one clock at rate `1` and `k`
clocks at rate `c`. Clock 1 wins iff `ξⱼ > c·ξ₁` for all `j`, so by independence

> **(1)  `E[G(cξ)ᵏ] = 1/(1 + kc)`  for every `k ≥ 1` and `c > 0`.**

The integral equation has become a **moment sequence**, and the variable `G(cξ)` takes values in
`[0,1]`, where moments determine the law.

---

## 3. The proof, in four steps

Regularity assumed: `G` continuous and strictly decreasing, `G(0) = 1`, `G(t) → 0`. Equivalently,
`ξ` has a continuous strictly increasing CDF with support `(0, ∞)`. The exponential satisfies this,
so the characterisation is not hollowed out by its own hypotheses.

**Step 1.** (1), as above.

**Step 2.** `U := G(ξ)` is `Uniform[0,1]` — the probability integral transform. Write
`H_c(u) := G(c·G⁻¹(u))`, so `G(cξ) = H_c(U)`. Since `G` is decreasing, `H_c` is *increasing*.
Now `E[(U^c)^k] = E[U^{ck}] = 1/(ck+1)`, so by (1)

> **(2)  `E[H_c(U)ᵏ] = E[(U^c)ᵏ]` for every `k ≥ 1`.**

**Step 3.** Both `H_c(U)` and `U^c` are `[0,1]`-valued with the same moments, so they have the same
law (Hausdorff determinacy). Both are *increasing* functions of the same `U`, so they agree
pointwise:

> **(3)  `H_c(u) = u^c`, i.e. `G(ct) = G(t)^c` for all `c, t > 0`.**

**Step 4.** Put `t = 1`:

> **(4)  `G(c) = G(1)^c = e^{−λc}` with `λ = −log G(1) > 0`.  ∎**

No Cauchy functional equation, no Laplace inversion, no Choquet–Deny. Step 4 is a substitution.

---

## 4. The one real caveat, and why CSD is entitled to it

The argument needs the `k`-th moment for **every** `k`, hence races with **arbitrarily many
clocks**. For a *fixed* number of outcomes `n` it yields only `n−1` moments, and finitely many
moments do not determine a law — so at fixed `n` the exponential is **not** forced. State it as:

> the exponential law is forced *provided the same clock law serves every `n`*.

CSD is entitled to exactly that hypothesis, and has already committed to it:
`sigma-fibre-contextuality.md` argues the fibre model is legitimate precisely because "the fibre law
`ξ` is fixed, prep- and measurement-independent". A law that changed with the number of outcomes
would be measurement-dependent, which is the thing that section rules out. So the hypothesis is not
a convenience — **it is the corpus's own stated posture, and this argument is where it earns its
keep.**

---

## 5. Lean cost — a project, not research

| Step | Ingredient | Status |
|---|---|---|
| 1 | the `k`-clock race probability for *general* iid clocks | ✅ **DONE 2026-08-24** — `ProbabilityTheory.HasRaceProperty.lintegral_measure_Ioi_pow` and `…_pow_mul_pow` (`Mathlib/Probability/IidClockRace.lean`). Not the fiddliest part after all: see §6a |
| 2 | probability integral transform | ✅ **DONE 2026-08-24** — `HasRaceProperty.map_survival`, and it needs **no regularity hypothesis on `μ` whatsoever** |
| 3 | Hausdorff determinacy on `[0,1]` | ✅ **DONE 2026-08-23** — `MeasureTheory.ext_of_forall_integral_pow_eq` (`Mathlib/MeasureTheory/MomentDeterminacy.lean`). Consumed by step 2 |
| 3′ | ✅ built 2026-08-24 — `eq_of_forall_integral_mul_pow_eq`. ⚠️ **Not used**: the route that closed c2 needs no comparison of `H_c` with `u^c` at all (§5a). Cat-1 and reusable; left in place |
| 4 | substitution | ✅ **DONE 2026-08-24**, but not as a substitution — `survival_natMul_ae` + `raceRate_le` + `map_survival`, per §5a |

**Estimate: L** — and the estimate was right about the size, wrong about *where it sits*. See §5a.

---

## 5a. ★ What actually closed it, and why the mapped assemblies were all unnecessary

Steps 3 and 3′ exist to compare `H_c(u) = G(c·G⁻¹(u))` against `u^c`. Every one of them needs `H_c`
as a *continuous function on a closed interval*, hence the quantile `G⁻¹`, which Mathlib does not
provide. Halfway through the build this looked like the remaining cost, and three routes past it
were mapped: build the quantile; or push weighted measures forward and prove `G_*` injective on
densities; or do determinacy in two variables on `[0,1]²` via Stone–Weierstrass.

**All three were unnecessary.** The observation that dissolves them:

> Restrict the ratio to a **natural number** `m`. Then `G(t)^m` is *itself a product of `m` survival
> factors at rate `1`*, so it lives inside the race family — and every term of the expansion of
> `∫ (G(mt) − G(t)ᵐ)² dμ` is an instance of that one family:
>
> * `∫ G(mt)² dμ = 1/(1+2m)` at rates `(1, m, m)`;
> * `∫ G(mt)·G(t)ᵐ dμ = 1/(1+2m)` at rates `(1, m, 1ᵐ)`;
> * `∫ G(t)²ᵐ dμ = 1/(1+2m)` at rates `(1, 1²ᵐ)`.
>
> They cancel. A nonnegative function with zero integral vanishes almost everywhere, so
> `G(mt) = G(t)ᵐ` a.e. (`HasRaceProperty.survival_natMul_ae`).

The cross term is the whole difficulty, and it is computable *exactly when the ratio is an integer*.
That is why the real ratios the four-step sketch reaches for are never needed.

**And the integers are enough, because antitonicity supplies what they leave out.** The functional
equation ties `G` together only along the lattice `{mt}`, and a priori nothing connects the lattices
of two different readings. Monotonicity connects them (`raceRate_le`): `mt ≤ nt'` forces
`G(t)ᵐ = G(mt) ≥ G(nt') = G(t')ⁿ`, hence `m·λ(t)·t ≤ n·λ(t')·t'`; let the integer ratio `m/n` climb
to `t'/t` and `λ(t) ≤ λ(t')`, with symmetry giving equality. **One `λ` serves every good reading**,
and no density of the support is needed anywhere.

The finish reads the law off through step 2 rather than through a functional equation: on the good
set `t > s ↔ G t < e^{−λs}`, so `μ (Ioi s) = (μ.map G) (Iio e^{−λs}) = e^{−λs}`, and
`Measure.ext_of_Iic` closes it. Two further hypotheses of §3 also came out **derived, not assumed**:
atomlessness (§6a, step 2) and support in `(0,∞)` — for `t ≤ 0` one has `2t ≤ t`, so
`G(t) ≤ G(2t) = G(t)²`, false for `G(t) ∈ (0,1)`; the `m = 2` case alone.

★ **The lesson, and it is the same one twice.** §6a already records: *when a step looks like it
needs a stronger determinacy theorem, check whether it needs only the same theorem against a
different object.* The stronger version is: **check whether it needs a determinacy theorem at all.**
Both times the fix was to ask what the race family can already compute, and to shape the question to
fit that, rather than to build machinery that would answer the question as first posed. The
`k`-clock family paid for four separate steps here (the moment sequence, the transform, the
functional equation, and positivity of the support); the two-clock framing that made this look like
research could pay for none of them.

**What `MomentDeterminacy.lean` is still for.** It is not wasted: `map_survival` (step 2) uses
`ext_of_forall_integral_pow_eq_of_null_compl`, and it is Cat-1 and reusable. But
`eq_of_forall_integral_mul_pow_eq` and the `intervalMeasure` carrier are **currently unconsumed** —
built for a step this route no longer takes. Leave them; do not build `H_c` to justify them.

---

## 6. Alternatives considered

* **Memorylessness first** (race ⇒ restart-invariance ⇒ memoryless ⇒ exponential). Rejected: the
  restart-invariance hypothesis is close enough to memorylessness to make the argument feel
  circular, and it needs a process formulation the corpus does not have.
* **Ferguson-type characterisation** (min independent of argmin ⇒ exponential). A different
  hypothesis; would need the independence version derived from the race property first. No cheaper.
* **Characterise within a parametric family** (say, Weibull). Cheap, but proves far less — "not an
  arbitrary choice *within a family we chose*" is close to vacuous.
* **Two-clock + Mellin.** The route that made this look like research. Strictly harder; skip.

---

## 6a. Progress

* ✅ **Step 3 landed 2026-08-23** — `MeasureTheory.ext_of_forall_integral_pow_eq`, exactly the
  assembly this memo predicted (Weierstrass + `ext_of_forall_integral_eq_of_IsFiniteMeasure`, an
  elementary three-term triangle inequality). It is Cat-1 and reusable well beyond this route.
* ✅ **The `ℝ`-supported restatement landed too** —
  `ext_of_forall_integral_pow_eq_of_null_compl`, transferring through `Subtype.val` with
  `map_comap_subtype_coe`. This is the form the route actually consumes.
* ✅ **The fork is dissolved — step 3′ is done, by a third route neither branch anticipated.**
  `eq_of_forall_integral_mul_pow_eq`: *two continuous functions on a compact interval with the same
  moments against all powers are equal.* Applied to `H_c` and `u ↦ u^c` — both continuous, because
  `G` is continuous and strictly decreasing — this gives `H_c = u^c` directly.

  The route works because the `k`-clock family delivers more than the marginal moments: with `j`
  clocks at rate `c` and `k` at rate `1` it gives `E[H_c(U)^j U^k] = 1/(1 + jc + k)`, and taking
  `j = 1` leaves `∫ H_c(u)·u^k du = ∫ u^c·u^k du` for every `k` — a *fixed continuous weight*
  against all powers, which is exactly the hypothesis above. No rearrangement theory, no joint
  law, no `[0,1]²`.

  `IsOpenPosMeasure` is what upgrades "a.e. equal" to "equal", and full support on the interval
  supplies it.

* ~~**A fork discovered while building, which the four-step sketch hid.**~~ *(Retired — kept for the
  record.)* Step 3′ looked like it needed one of two branches:
  * **(i) the monotone route** — two antitone functions of the same variable with equal laws are
    equal a.e. This is decreasing-rearrangement uniqueness; Mathlib has no quantile machinery for
    it, so it would be built from scratch (order + topology fiddling, no deep analysis).
  * **(ii) the two-dimensional route** — use the *joint* moments. The `k`-clock family also gives
    `E[G(c₁ξ)^{k₁} G(c₂ξ)^{k₂}] = 1/(1 + k₁c₁ + k₂c₂)`, so the joint law of `(G(cξ), G(ξ))` matches
    that of `(U^c, U)`, which is **supported on a graph** — giving `G(cξ) = G(ξ)^c` a.s. directly,
    with no monotonicity argument at all. The cost is 2-D determinacy on `[0,1]²`, i.e. redoing the
    assembly above with general Stone–Weierstrass (the coordinate algebra separates points) instead
    of Weierstrass.
  Route (ii) was the better of the two, but **route (iii) above beat both** — it reuses the
  Weierstrass argument already written, against a fixed weight instead of between two measures.
  Worth remembering: when a step looks like it needs a *stronger determinacy theorem*, check first
  whether it needs only the *same* theorem against a different object.
* ✅ **The carrier is built** (2026-08-24). Mathlib has no `MeasureSpace` instance on the subtype
  `Set.Icc a b`, so `intervalMeasure` (the comap of `volume`) and its two needed properties had to
  be supplied: finiteness, and `isOpenPosMeasure_intervalMeasure` (needs `a < b`), which is what
  upgrades a.e.-equality to equality. The analytic half of the route is now complete infrastructure.
* ✅ **Step 1 landed 2026-08-24** — `Mathlib/Probability/IidClockRace.lean`. It was billed as "the
  fiddliest part" and was not, because of a **change of framing** the memo had not spelled out.
  `CompetingExponentials` gave each clock its own law `Exp bⱼ` and raced them unscaled; that is
  unusable when the law is the unknown. `scaledRaceCell` instead puts one iid law on every clock and
  carries the rate as a **scaling of the reading** — clock `j` fires at `ξⱼ / bⱼ`. The proof is then
  the *same* `measurePreserving_piFinSuccAbove` split and `Measure.pi_pi` box, but strictly cleaner:
  because the rate scales the reading rather than the law, each slice is a box at **every** `t`, and
  the almost-everywhere step of the exponential case disappears.
  `hasRaceProperty_expMeasure` is the non-vacuity witness — every exponential law has the property,
  which is the `⇐` direction restated in the iid framing, and it is where the two framings visibly
  agree (the rate `r` cancels out of `r/(r + r·S/bᵢ)`).
  `HasRaceProperty` quantifies over the number of clocks, so §4's caveat is now **encoded in the
  Lean statement** rather than only in prose. Good.
* ✅ **Step 2 landed 2026-08-24, and is stronger than this memo predicted.**
  `HasRaceProperty.map_survival` — `G(ξ)` is uniform on `[0,1]` — holds with **no regularity
  hypothesis on `μ` at all**. §3's "regularity assumed: `G` continuous and strictly decreasing" is
  not needed for this step: the `c = 1` moments are exactly the uniform moments, and step 3 closes
  it. ★ So atomlessness of `μ` is **derived from the race property, not assumed of it** — as it
  must be, since the `(k+1)`-clock race at equal rates says the smallest of `k+1` iid readings is
  *strictly* smallest with probability `1/(k+1)`, and ties would cost. That is the second time the
  `k`-clock family has paid for a step the two-clock framing made look expensive.
* ✅ **Steps 3 and 4 landed 2026-08-24 — by a route this memo did not contain.** See §5a. The
  headline is `hasRaceProperty_iff_exists_expMeasure`; the `⇒` half is
  `HasRaceProperty.exists_eq_expMeasure`, resting on `survival_natMul_ae` (the integer-ratio L²
  cancellation) and `raceRate_le` (antitonicity across lattices).
* ⚠️ **Two things this does NOT say**, and both are easy to overstate:
  * `map_survival` alone is not "the fibre law is pinned down" — it says the survival function is a
    uniform variable, which *every* atomless law satisfies. The pinning is `exists_eq_expMeasure`.
  * The characterisation is **a posit removed, not a mechanism supplied.** §3c's exponential fibre
    measure is no longer a choice; **no dynamics carves the race cells.** `Q12-d`'s frontier half
    stays blocked by `W1`, and neither `DeIsolationInteraction` witness is dynamical. The
    reconstruction frontier has not moved.

## 7. Recommendation

*(Historical — the recommendation as written before the build.)* The route above is the one to take
if c2 is wanted. It is **L**, it is fully mapped, and it needs no upstream mathematics that Mathlib
lacks.

**Executed 2026-08-24, in one session, and the estimate was right about the size while being wrong
about the shape**: steps 1 and 2 as written, steps 3/4 by the integer-ratio argument of §5a instead
of by the determinacy comparison this memo built for. Keep §5a; it is the part worth rereading. It is *not* recommended ahead of frontier work: c2
would tighten a posit that is already narrow, and `Q12-d`'s original form stays blocked either way.

If it is built, the honest headline is: **the exponential fibre law is forced by the race property
together with measurement-independence of the fibre law** — and the second conjunct must travel
with the first.

## References

`specs/record-layer-plan.md` §3c; `specs/sigma-fibre-contextuality.md` (the fixed,
measurement-independent fibre law); `specs/q12-fibre-mechanism-scoping.md` (`Q12-c`, and the
assessment this supersedes); `Mathlib/Probability/CompetingExponentials.lean` (the `⇐` direction);
`specs/future-work.md`.
