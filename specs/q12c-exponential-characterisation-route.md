# Q12-c2 — a route to "the exponential clock law is forced"

**Status: steps 1, 2, 3 and 3′ are Lean; the ASSEMBLY is not.** The probabilistic half and the
analytic half are both built and neither is joined to the other, because joining them needs an
object nothing yet constructs — `H_c` — see §5a. Everything below is a route memo. The
`record-layer-plan.md` §3c claim it targets **stays unproved until the assembly lands**.

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
| 3 | Hausdorff determinacy on `[0,1]` | ✅ **DONE 2026-08-23** — `MeasureTheory.ext_of_forall_integral_pow_eq` (`Mathlib/MeasureTheory/MomentDeterminacy.lean`). Assembled from Weierstrass + `ext_of_forall_integral_eq_of_IsFiniteMeasure`, as predicted |
| 3′ | ✅ **DONE 2026-08-24** — `eq_of_forall_integral_mul_pow_eq`. Not the quantile argument: continuous functions with equal moments against all powers, via the same Weierstrass density argument |
| 4 | substitution | trivial |

**Estimate: L** — and the estimate was right about the size, wrong about *where it sits*. See §5a.

---

## 5a. ⚠️ Where the remaining cost actually is: `H_c`

The four-step table above hides its own hardest item, and this is the finding of the 2026-08-24
session. Steps 3 and 3′ are theorems **about** `H_c`; step 4 is a substitution **into** the
conclusion about `H_c`. Nothing anywhere **constructs** `H_c(u) = G(c·G⁻¹(u))`, and
`eq_of_forall_integral_mul_pow_eq` wants it as an element of `C(Icc 0 1, ℝ)`. That needs:

* the **quantile** `G⁻¹`, i.e. the inverse of a continuous strictly antitone surjection
  `(0,∞) → (0,1)`, which Mathlib does not hand over (this is the same wall route (i) hit, arriving
  from a different direction — dissolving the *fork* did not dissolve the *inverse*); and
* the **endpoints**: `G⁻¹` lives on the open interval, `H_c` has to be continuous on the closed
  one, extended by `H_c(0) = 0`, `H_c(1) = 1`.

There is a second route to the same place which trades the quantile for a measure-theoretic
statement, and it may be the cheaper one:

* Push the *weighted* measures forward instead of changing variables. `ν₁ := G_*(G(c·) dμ)` and
  `ν₂ := G_*(G(·)ᶜ dμ)` have the same moments by the mixed-moment identity plus step 2, so
  `ν₁ = ν₂` by `ext_of_forall_integral_pow_eq_of_null_compl` — provable **today**, with no `H_c`.
  What it gives is `𝔼[G(cξ) ∣ G(ξ)] = G(ξ)ᶜ`, a *conditional* statement; upgrading it to the
  pointwise identity needs `G_*` injective on densities.
* That injectivity is within reach and does not need step 2: `G` is antitone, so for `s < t` with
  `G s = G t` one has `μ (Ioc s t) = 0`; hence `Ioi a ▵ G⁻¹(Iio (G a))` is contained in
  `{t > a ∣ G t = G a}`, an interval of zero `μ`-measure. So `σ(G)` contains the Borel sets mod
  `μ`-null, and a π-λ argument finishes. **Written down here because it was worked out and not
  built — do not re-derive it.**

Neither route is research. Both are a day's build. Until one of them lands, the corpus has the
*ingredients*, not the characterisation.

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
* ⏳ **What is left is the assembly, and it is not step 4.** See §5a: `H_c` is used by steps 3, 3′
  and 4 and constructed by none of them. Two routes are mapped there, both a day's build, neither
  research.

⚠️ Until the assembly lands, the corpus has the *ingredients*, not §3c's claim. In particular do
not read `map_survival` as "the fibre law is pinned down": it says the survival function is a
uniform variable, which every atomless law satisfies.

## 7. Recommendation

The route above is the one to take if c2 is wanted. It is **L**, it is fully mapped, and it needs
no upstream mathematics that Mathlib lacks. As of 2026-08-24 four of its five pieces are built and
the fifth (§5a) is the only one outstanding. It is *not* recommended ahead of frontier work: c2
would tighten a posit that is already narrow, and `Q12-d`'s original form stays blocked either way.

If it is built, the honest headline is: **the exponential fibre law is forced by the race property
together with measurement-independence of the fibre law** — and the second conjunct must travel
with the first.

## References

`specs/record-layer-plan.md` §3c; `specs/sigma-fibre-contextuality.md` (the fixed,
measurement-independent fibre law); `specs/q12-fibre-mechanism-scoping.md` (`Q12-c`, and the
assessment this supersedes); `Mathlib/Probability/CompetingExponentials.lean` (the `⇐` direction);
`specs/future-work.md`.
