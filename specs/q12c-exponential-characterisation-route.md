# Q12-c2 — a route to "the exponential clock law is forced"

**Status: a proof on paper, and a mapped Lean project. Step 3 is now Lean; the rest is not.** Everything below is a
route memo. Nothing here is a corpus theorem, and the `record-layer-plan.md` §3c claim it targets
stays unproved until it is.

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
| 1 | the `k`-clock race probability for *general* iid clocks | needs the product-measure setup of `Q12-b` redone without the exponential assumption — the fiddliest part |
| 2 | probability integral transform | standard; check Mathlib coverage |
| 3 | Hausdorff determinacy on `[0,1]` | ✅ **DONE 2026-08-23** — `MeasureTheory.ext_of_forall_integral_pow_eq` (`Mathlib/MeasureTheory/MomentDeterminacy.lean`). Assembled from Weierstrass + `ext_of_forall_integral_eq_of_IsFiniteMeasure`, as predicted |
| 3′ | ✅ **DONE 2026-08-24** — `eq_of_forall_integral_mul_pow_eq`. Not the quantile argument: continuous functions with equal moments against all powers, via the same Weierstrass density argument |
| 4 | substitution | trivial |

**Estimate: L.** The analytic content is light; the cost is step 1's plumbing plus assembling
determinacy, which Mathlib provisions but does not state.

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
* ⏳ **Next: step 2**, the probability integral transform — `μ.map G = Uniform[0,1]`, which is what
  converts the `μ`-integrals of the race into Lebesgue integrals on `[0,1]`. Note it comes *free
  from the hypothesis at `c = 1`* rather than needing a separate PIT theorem: the `c = 1` moments
  are exactly the moments of the uniform law, so `ext_of_forall_integral_pow_eq_of_null_compl`
  delivers it. Step 4 is then a substitution.
* ⏳ **Then step 1**, the expensive half: the `k`-clock race for *general* iid clocks, i.e. Q12-b's
  product-measure setup without the exponential assumption. This is the only remaining piece that
  is plumbing rather than mathematics, and it is what ties the result to §3c.

⚠️ Until step 1 lands, the corpus has the *characterisation*, not §3c's claim.

## 7. Recommendation

The route above is the one to take if c2 is wanted. It is **L**, it is fully mapped, and it needs
no upstream mathematics that Mathlib lacks. It is *not* recommended ahead of frontier work: c2
would tighten a posit that is already narrow, and `Q12-d`'s original form stays blocked either way.

If it is built, the honest headline is: **the exponential fibre law is forced by the race property
together with measurement-independence of the fibre law** — and the second conjunct must travel
with the first.

## References

`specs/record-layer-plan.md` §3c; `specs/sigma-fibre-contextuality.md` (the fixed,
measurement-independent fibre law); `specs/q12-fibre-mechanism-scoping.md` (`Q12-c`, and the
assessment this supersedes); `Mathlib/Probability/CompetingExponentials.lean` (the `⇐` direction);
`specs/future-work.md`.
