# Feynman's formulation, the continuum rung: scoping note (BACKLOG #36(c))

**Status:** SCOPED 2026-09-20; **FC-0 probes pass, FC-1 to FC-4 LANDED the same day — the Euclidean deliverable, Feynman–Kac, is a theorem** (`Mathlib/Analysis/Semigroup/{BoundedPerturbation,HeatSemigroup}.lean`, `Mathlib/Probability/{TimeSlicedWiener,FeynmanKac}.lean`, §7), after rungs (a) and (b) of row 36 landed (2026-09-19/20) and a survey of the
Mathlib pin `db584cd6d` for path-space measures, semigroups and the Fourier transform. Every claim below
about the corpus or the pin was read from theorem *types*. Nothing here is built; §4 and §5 price what could
be, §8 says what needs the author's decision, and §9 says what is not claimed.

## 1. The question

Rung (c) asks for the **continuum path integral**: Feynman's

    ⟨x_f | e^{−iTH} | x_i⟩ = ∫ 𝒟x e^{iS[x]},   H = −½Δ + V on L²(ℝᵈ),

as a theorem. The obstruction is not Lean's: the symbol `𝒟x e^{iS}` is not a countably additive complex
measure on paths (Cameron 1960), so there is no measure-theoretic statement to prove in real time as written.
Mathematics has two honest forms, and each is a theorem that can be stated:

* **(E) Euclidean — the Feynman–Kac formula.** Replace `e^{−iTH}` by `e^{−TH}`; then the path "measure" is
  Wiener measure, an honest probability measure, and

      (e^{−tH} f)(x) = E[ f(x + B_t) · exp(−∫₀ᵗ V(x + B_s) ds) ],

  `B` a Brownian motion. This is Kac's theorem (1949): the Euclidean path integral *is* a Wiener integral.
* **(R) Real time — Nelson's theorem.** Define the real-time path integral as the limit of the time-sliced
  products,

      e^{−itH} ψ = lim_n (e^{−itH₀/n} e^{−itV/n})ⁿ ψ,

  the Trotter product formula for the unbounded pair `(H₀, V)` (Nelson 1964). The `n`-slice product is a
  finite iterated integral against the free kernel; the limit exists as a strong operator limit; the "measure"
  never appears.

Rung (a) already proved the finite-dimensional shadow of (R) (`exp_add_apply_tendsto_sum_pathWeight`,
`Mathlib/Analysis/Matrix/SumOverPaths.lean`). Rung (c) is (E) and (R) on `L²(ℝ)` with the free generator
unbounded. "Done" means: **(E) proved as stated**, conditional on a Brownian motion, with `e^{−tH}` given by an
operator-theoretic definition that needs no unbounded-operator theory; **(R) proved in operator form**, with
the free Schrödinger group defined through the L² Fourier transform. The kernel form of (R), with the
oscillatory free kernel `(2πit)^{−1/2} e^{i(x−y)²/2t}` written out, is priced separately and honestly (§5).

## 2. What the corpus has

| Rung | Module | What it gives the continuum |
|---|---|---|
| (a) | `Mathlib/Analysis/Matrix/SumOverPaths.lean` | the time-sliced product as a sum over discrete paths, and its limit, at finite dimension |
| (b)(ii) | `Mathlib/Analysis/Matrix/DysonSeries.lean` | the Dyson series as Bochner integrals, the Duhamel identity, the truncation error `(‖B‖t)ⁿ/n!` — the template for the vector-valued series of FC-1 |
| (b)(iii) | `Mathlib/Analysis/Matrix/DysonVertex.lean` | the interaction picture and the time-ordered recursion — carries over verbatim to a semigroup |
| — | `Mathlib/Analysis/NormedSpace/TrotterGeneral.lean` | ★★ `trotter_product` for **bounded** `A, B` in a Banach algebra, with the rate `n⁻¹ s²(3+s)e^{2s}` — the telescoping proof pattern, but the free generator of (c) is not bounded |
| (b)(iv) | `CV/WickTime.lean` | Wick at the cutoff — the lattice side of the same physics; not used by (c) |

Everything is at finite dimension or with bounded generators. What the continuum needs and the corpus lacks is
exactly three things: an **unbounded free generator** (the Laplacian, or the heat/Schrödinger group it
generates), a **path-space measure** (Wiener), and **continuous paths** (to make `∫₀ᵗ V(x + B_s) ds` a
Riemann integral). §3 says which of these the pin supplies.

## 3. What the pin has (Mathlib `db584cd6d`)

| Ingredient | At the pin | Consequence for (c) |
|---|---|---|
| L² Fourier transform | ✓ `MeasureTheory.Lp.fourierTransformₗᵢ : Lp F 2 ≃ₗᵢ[ℂ] Lp F 2`, agreeing with the Schwartz transform (`Analysis/Fourier/LpSpace.lean`) | the free Schrödinger group `e^{−itH₀} = 𝓕⁻¹ ∘ (e^{−itξ²/2} ·) ∘ 𝓕` is **definable** on `L²(ℝ)` as an operator, no unbounded operator needed |
| multiplication by `L^∞` on `L²` | ✓ bundled: `(ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 : Lp ℂ ∞ μ →L Lp ℂ 2 μ →L Lp ℂ 2 μ` (`MeasureTheory/Function/Holder.lean`; probe P1 confirmed it, §7) | the multiplier `M_V` and the Fourier multiplier come for free, with `‖M_g‖ ≤ ‖g‖_∞` |
| Gaussian measures | ✓ `gaussianReal`, `multivariateGaussian`, ✓ `gaussianReal_conv_gaussianReal` (1-d) | the heat semigroup on `L²(ℝ)` as Gaussian convolution, with its semigroup law, is buildable in one dimension |
| Brownian motion | ✓ predicates `IsPreBrownianReal` / `IsBrownianReal` (real-valued, `ℝ≥0 → Ω → ℝ`), finite-dimensional laws `projectiveFamily` as a multivariate Gaussian, ✓ independent increments `hasIndepIncrements`, ✓ the weak Markov property `indepFun_shift`; ✗ **existence** (Kolmogorov–Chentsov: only `IsKolmogorovProcess` and the pair-reduction groundwork are at the pin) | every theorem of (E) is stated **conditionally on `hB : IsBrownianReal B P`**, as Mathlib's own Brownian file states its theorems; when Mathlib lands existence the hypothesis is discharged by a name |
| Wiener measure on `C([0,T])` | ✗ | not needed: the Wiener *integral* is `E[·]` under `P` for a Brownian process on any `Ω` |
| Riemann sums of a continuous function | ✗ as a ready lemma (`BoxIntegral` proves Riemann integrability, heavier than needed) | probe P3 (§7): uniform continuity on `[0, t]` gives the lemma in ~70 lines |
| `C₀`-semigroups, Hille–Yosida, Stone | ✗ | **do not define `e^{−tH}` as "the semigroup generated by `H`"**; define it by the Dyson series around the free semigroup (FC-1) — that is an honest operator-theoretic definition and coincides with the generated semigroup whenever the latter exists |
| unbounded self-adjoint operators | ✗ | same: the free generator is never written; only the group/semigroup it generates |
| Feynman–Kac, Trotter–Kato (unbounded) | ✗ | the deliverables of this note |
| oscillatory integrals (Fresnel) | ✗ | the kernel form of (R) is out of the pin's L¹-based Fourier framework; priced XL in §5 |

The pin's Brownian motion is one-dimensional. Dimension `d` is a separate brick (FC-2′) once the
one-dimensional arc stands; nothing in the arc depends on `d = 1` except the availability of the objects.

## 4. The Euclidean arc, priced

`Cx` is the size scale (S, M, L, XL), `P` is P(success) at the pin, `V` is value for the question in §1.

| # | Brick | Cx | P | V | What it lands |
|---|---|---|---|---|---|
| **FC-0** | **Three probes** (§7): P1 the `L^∞`-multiplier as a CLM on `L²`; P2 `E[F(B_{t₁}, …, B_{tₙ})]` as an iterated Gaussian integral from independent increments; P3 Riemann sums of a continuous function on `[0, t]`. | **S** | high | gates FC-2/3/4 |
| ~~**FC-1**~~ **DONE 2026-09-20** | **A bounded perturbation of a contraction semigroup** (Category 1). For `S : ℝ≥0 → H →L[ℂ] H` a strongly continuous contraction semigroup (a predicate `IsContractionSemigroup S`, no generator named) and `V` bounded: the vector-valued Dyson series `𝒮(t)ψ = ∑ₙ Dₙ(t)ψ`, `Dₙ₊₁(t)ψ = ∫₀ᵗ S(t−s) V Dₙ(s)ψ ds` (Bochner in `H`; the integrand is continuous in `s` because `S` is strongly continuous), its convergence with the bound `(‖V‖t)ⁿ/n!`, `𝒮` a strongly continuous semigroup, the Duhamel identity, and ★★ **the Trotter product formula** `(S(t/n) e^{−(t/n)V})ⁿ ψ → 𝒮(t) ψ`. The unitary-group case (real time) is the same statement on `t ≥ 0`. | **M–L** | high: the Dyson half is `DysonSeries.lean` with `exp(tA)` replaced by `S(t)` and matrices by vectors; the Trotter half is the classical argument (Reed–Simon VIII.31) — telescoping plus uniformity on the compact orbit `{𝒮(s)ψ : s ∈ [0,t]}` | high: the abstract engine of both (E) and (R); Mathlib has none of it |
| ~~**FC-2**~~ **DONE 2026-09-20** | **The heat semigroup on `L²(ℝ)`** (Category 1). `P_t f = γ_t * f` (Gaussian convolution, `gaussianReal 0 t`): contraction, semigroup law (`gaussianReal_conv_gaussianReal`), strong continuity, and the identification `P_t f x = E[f(x + B_t)]` for a pre-Brownian `B` (`hasLaw_eval`). | **M** | high | the free Euclidean propagator, the `S` of FC-1 |
| ~~**FC-3**~~ **DONE 2026-09-20** | **The time-sliced Wiener functional** (Category 1). For a pre-Brownian `B` and bounded measurable `V`: `E[f(x + B_t) ∏_{k=1}^{n} e^{−(t/n) V(x + B_{kt/n})}] = ((P_{t/n} M_{e^{−(t/n)V}})ⁿ f)(x)` a.e. in `x` — Feynman's finite-slice formula in the Euclidean continuum, the sum over paths become an iterated Gaussian integral over the `n` intermediate positions. Induction on `n` through the weak Markov property (`indepFun_shift`, `hasIndepIncrements`). The direct analogue of rung (a)'s `pow_succ_apply_eq_sum_pathWeight`. | **M** | high: the pin has the Markov ingredient | high: the identity that joins Wiener to the operator product |
| ~~**FC-4**~~ **DONE 2026-09-20** | ★★ **Feynman–Kac** (Category 1). For `hB : IsBrownianReal B P` (a.s. continuous paths), `V` bounded continuous, `f ∈ L²(ℝ)`: (i) `(t/n) ∑_k V(x + B_{kt/n}) → ∫₀ᵗ V(x + B_s) ds` a.s. (P3 along the continuous path) and dominated convergence for the Wiener side; (ii) FC-1's Trotter formula with `S = P` for the operator side; hence `𝒮(t) f =ᵃᵉ x ↦ E[f(x + B_t) exp(−∫₀ᵗ V(x + B_s) ds)]`. Corollary for bounded continuous `f`: the pointwise form. | **M–L** | high once FC-1–3 stand | **the deliverable of (E)**: the Euclidean path integral as a theorem at the level Kac stated it, conditional on the existence Mathlib is building |
| **FC-2′** | **Dimension `d`.** The heat semigroup on `L²(ℝᵈ)` through `multivariateGaussian` (or the product of one-dimensional kernels), a `d`-dimensional Brownian motion as `d` independent real ones, FC-3/4 restated. | **S–M** after FC-4 | medium: the pin's Brownian API is one-dimensional, so the `d`-dimensional process is assembled by hand | medium: physics wants `d = 3`, the mathematics is unchanged |

The design decision that makes the arc honest and buildable at the pin: **`e^{−tH}` is *defined* by the Dyson
series around the heat semigroup** (FC-1 applied to FC-2). No Laplacian is written, no domain, no
self-adjointness, no Hille–Yosida. The definition is canonical — it is the unique strongly continuous
semigroup satisfying the Duhamel identity with `P` and `V` — and coincides with the semigroup generated by
`−½Δ + V` whenever Mathlib acquires the theory to say so. The theorem "FC-1's `𝒮` is generated by `−½Δ + V`"
is Mathlib-future and is **not claimed** here.

## 5. Real time, priced

| # | Brick | Cx | P | V | What it lands |
|---|---|---|---|---|---|
| **FC-5** | ★★ **Nelson's theorem in operator form** (Category 1). The free Schrödinger group `U₀(t) := 𝓕⁻¹ ∘ M_{e^{−itξ²/2}} ∘ 𝓕` on `L²(ℝ)` (P1 for the multiplier): unitary, a group, strongly continuous (dominated convergence on the Fourier side). FC-1 for the unitary case gives the interacting group `U(t)` (Dyson) and `(U₀(t/n) e^{−itV/n})ⁿ ψ → U(t) ψ` — **the real-time path integral as the strong limit of time-sliced products**, which is what the symbol `∫𝒟x e^{iS}` means in Nelson's definition. Also its action on Gaussians/Schwartz functions explicitly, so the free propagator's kernel is visible where it is absolutely convergent. | **L** | medium–high: the Fourier side is at the pin; the delicate part is only P1 and the group's strong continuity | high: (R) as a theorem; the `𝒟x` heuristic replaced by its definition |
| **FC-5′** | **The kernel form.** `(U₀(t)ψ)(x) = (2πit)^{−1/2} ∫ e^{i(x−y)²/2t} ψ(y) dy` for `ψ ∈ L¹ ∩ L²` (as an improper Fresnel integral) and hence the `n`-slice iterated kernel integral with `e^{i S_n(x₀, …, xₙ)}` in the integrand — Feynman's formula with the action visible. | **XL** | low at the pin: the kernel is not absolutely integrable, so it is outside Mathlib's L¹-based Fourier theory; needs oscillatory-integral technology (Fresnel, or the `ε ↓ 0` limit of `e^{−(ε+it)H₀}` through FC-2's Gaussian kernel with complex variance) | medium: the same theorem as FC-5 in different clothes; the physics reader wants to see `e^{iS}`, the mathematics does not need it |

FC-5′ is the only piece of rung (c) that is XL, and it is XL for a reason that is not Lean's: real-time
kernels are oscillatory. The honest route to the action `S[x]` in the integrand is the analytic continuation
from FC-4 (`t ↦ it`), which is again a theorem about where the Gaussian kernel with complex variance is
absolutely convergent; it is recorded here as the route, not priced as a brick.

## 6. The CSD reading (FC-6, documentation, S)

Rung (c) is Category-1 mathematics about standard quantum mechanics on `L²(ℝᵈ)` and its Euclidean shadow. On
the programme's scope ladder (`specs/CSD-CHARTER.md`, the scope ladder note) the continuum is the EFT rung:
the reconstruction of quantum mechanics from the arena is complete at finite dimension, the CV modules are
the isolated-piece image with continuous spectra, and infinite-dimensional field theory is not required for
the programme's claims. Rung (c) therefore adds **no CSD claim**. Its value is twofold: Feynman's formulation
becomes a theorem at the level physicists state it (Kac's formula, Nelson's limit), completing row 36's
answer to "have we got Feynman integrals?"; and every brick is staged-for-Mathlib content Mathlib does not
have (a bounded-perturbation Trotter formula for semigroups, the heat semigroup as an operator, the
time-sliced Wiener functional, Feynman–Kac).

FC-6 landed with FC-4 (2026-09-20): the narrative document now cites Feynman–Kac for the continuum, and FP-1 records the Euclidean rung as done; Nelson's form (FC-5) is still open.

## 7. Order, sizes, gates

1. **FC-0** (S): the three probes, each a scratch file against the pin.
   * **P1** — a bundled multiplier: for `g` bounded measurable, `f ↦ g · f` as `Lp ℂ 2 →L[ℂ] Lp ℂ 2` with norm `≤ ‖g‖_∞`, from `MemLp.mul` and `eLpNorm_mul_le`-type bounds. Gate: the CLM exists in under 60 lines.
   * **P2** — for a pre-Brownian `B` and `0 < t₁ < t₂`: `E[F(B_{t₁}, B_{t₂})] = ∫∫ F(y₁, y₁ + y₂) dγ_{t₁}(y₁) dγ_{t₂−t₁}(y₂)`, from `hasIndepIncrements` and `hasLaw_sub`. Gate: the two-point case closes; the `n`-point case is the same induction.
   * **P3** — for `g` continuous on `[0, t]`: `(t/n) ∑_{k=1}^{n} g(kt/n) → ∫₀ᵗ g`. Gate: under 60 lines from uniform continuity and `intervalIntegral.sum_integral_adjacent_intervals`.
   **FC-0 outcome (2026-09-20): all three probes pass at the pin**, as local scratch files (not committed; they become the first lemmas of FC-2, FC-3 and FC-4).
   * **P1 — passes, 29 lines.** The pin already has the operator: `(ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 g` is the multiplier `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` for `g : Lp ℂ ∞ μ` (`MeasureTheory/Function/Holder.lean`, the `HolderTriple ∞ 2 2` instance), with `‖·‖ ≤ ‖g‖` from `norm_holderL_le` and `opNorm_mul_le`, and the pointwise formula `coeFn_holder`. Nothing to build.
   * **P2 — passes, 50 lines.** `IndepFun (B t₁) (B t₂ − B t₁) P` from `indepFun_shift t₁` composed with two evaluations (`IndepFun.comp`, `measurable_pi_apply`); the increment's law from `hasLaw_sub` (with `nndist ↑t₂ ↑t₁ = t₂ − t₁` for `t₁ ≤ t₂`); the joint law `(gaussianReal 0 t₁).prod (gaussianReal 0 (t₂ − t₁))` from `IndepFun.map_prod_eq_prod_map_map` and `HasLaw.map_eq`; then `integral_map` and `integral_prod`. `∫ F(B t₁, B t₂) dP = ∫∫ F(y₁, y₁ + y₂) dγ_{t₂−t₁} dγ_{t₁}` for bounded continuous `F`. The `n`-point case is the same induction.
   * **P3 — passes, ~70 lines** (the gate said 60; the excess is cast bookkeeping). Uniform continuity on `[0, t]` (`IsCompact.uniformContinuousOn_of_continuous`, `Metric.uniformContinuousOn_iff_le`), the partition `sum_integral_adjacent_intervals`, the constant integral on each piece, `norm_integral_le_of_norm_le_const` with `C = ε/(2t)`.
   Gate verdict: the arc's ingredients are at the pin; FC-1 can start.
   **FC-1 outcome (2026-09-20): landed as `Mathlib/Analysis/Semigroup/BoundedPerturbation.lean`, 833 lines, 16 pins, M–L took L.** Everything in the row's cell is proved: the Dyson series and its bounds, the Duhamel equation, uniqueness, the semigroup law, the bundled operator, the Trotter product formula, and `of_group` for the unitary case. Design as predicted: the semigroup is extended by the identity to `t ≤ 0` so every integrand is globally continuous (`continuous_parametric_intervalIntegral_of_continuous` then applies); joint continuity of `(t, ψ) ↦ S t ψ` comes from strong continuity plus the uniform bound; the Dyson sum is continuous in `t` by uniform convergence on `Iic T`; the sum-integral interchange in Duhamel is `intervalIntegral.hasSum_integral_of_dominated_convergence`; the Trotter proof needs `[Nontrivial E]` for `‖1‖ = 1` in the operator algebra. The one item not done is the *test* named below — the matrix `DysonSeries.lean` as an instance — priced as FC-1′ (S–M) in the BACKLOG row.
2. **FC-1** (M–L), the abstract engine; test it against the corpus's own `DysonSeries.lean` by instantiating `H = Fin m → ℂ`, `S(t) = exp(tA)`: the matrix theorems must come back as corollaries (the rule of two).
   **FC-2 outcome (2026-09-20): landed as `Mathlib/Analysis/Semigroup/HeatSemigroup.lean`, 17 pins, M took M.** The design that avoided every kernel estimate: `P_t f` is the `L²`-valued Bochner integral of the translates `τ_y f` against `γ_t`, so contraction is `‖∫‖ ≤ ∫‖·‖` on a probability measure, the semigroup law is `γ_s ∗ γ_t = γ_{s+t}` plus `translate_translate`, and strong continuity is the continuity of `y ↦ τ_y f` (Mathlib's `Continuous.compMeasurePreservingLp`) plus `γ_t = γ_1 ∘ (√t ·)⁻¹` and dominated convergence. The pointwise formula `(P_t f)(x) = ∫ f(x + y) dγ_t(y)` a.e. is the one place Fubini enters (pairing with indicators of finite-measure sets and `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`; the local integrability of the Wiener functional by the AM–GM bound `‖g‖ ≤ (1 + ‖g‖²)/2`, no Hölder). FC-1 then gives `perturbedHeat V t = e^{−t(H₀+V)}` for `V ∈ L^∞` with its Duhamel equation and ★★ the Trotter product formula. `Nontrivial L²` had to be supplied by hand (the indicator of `[0,1]`).
   **FC-3 outcome (2026-09-20): landed as `Mathlib/Probability/TimeSlicedWiener.lean`, 8 pins, M took M.** Stated for a general bounded weight `g` (so `g = e^{−hV}` is a special case and the exponential of the multiplication operator is deferred to FC-4). The Markov step is the weak Markov property exactly as the pin states it: the shifted process `B' = B(h + ·) − B(h)` is pre-Brownian and independent of `B_h`, and a freezing lemma for independent variables (joint law = product of marginals, `integral_prod`) turns `E[Ψ(B_h, B')]` into `∫ E[Ψ(y, B')] dγ_h(y)`. The induction quantifies over all pre-Brownian motions because the shifted process is a different one. Bounded data throughout; the extension to `f ∈ L²` is FC-4's, by continuity.
3. **FC-3** (M).
   **FC-4 outcome (2026-09-20): landed as `Mathlib/Probability/FeynmanKac.lean`, 6 pins, M–L took L.** Exactly the route of §4: the multiplier exponential `exp(−h M_V) = M_{e^{−hV}}` by the operator series applied to `f` (partial sums pointwise, `L²` limit and pointwise limit identified on finite-measure sets), the Wiener-side limit by dominated convergence with the Riemann sums of probe P3 along the continuous path, the operator side by FC-2's Trotter formula, and the two limits identified on every finite-measure set. Bounded `f`; the `L²` extension by continuity is FC-4′ (S). Conditional on `hB : IsBrownianReal B P`. Snag: `rw` could not match `exp (h • −M_V)` across the two modules' instance paths for the ℝ-action on operators; `congr 1; exact` did.
4. **FC-4** (M–L): Feynman–Kac. The Euclidean deliverable.
5. **FC-5** (L): Nelson. The real-time deliverable.
6. **FC-2′** (S–M) and **FC-6** (S) as the author wants.

Total for the arc through FC-5: **L**, in six bricks none larger than M–L. FC-5′ stays XL and is not in the
plan unless the author asks for the action in the integrand.

## 8. Decisions for the author

* **D1 — dimension.** One dimension first (the pin's Brownian motion is real-valued); `d` as FC-2′. The
  recommendation is one dimension: nothing in the mathematics changes, and the pin's API is one-dimensional.
* **D2 — the function space.** `L²(ℝ)` with almost-everywhere statements, because the heat semigroup is
  strongly continuous there and FC-1 needs strong continuity; pointwise corollaries for bounded continuous
  `f`, `V` afterwards. Bounded continuous functions with the sup norm would make the statements pointwise
  from the start but break FC-1 (the heat semigroup is not strongly continuous in sup norm without uniform
  continuity). The recommendation is `L²`.
* **D3 — wait for Mathlib's Brownian motion?** No: state everything conditionally on `hB : IsBrownianReal B P`,
  exactly as Mathlib's own Brownian file does today; existence is Mathlib's Kolmogorov–Chentsov programme and
  discharges the hypothesis by a name when it lands. The recommendation is to build now.
* **D4 — the action in the integrand (FC-5′)?** The recommendation is no: FC-4 and FC-5 are Feynman's
  formulation as theorems; FC-5′ is the same theorem with an oscillatory kernel written out, and its cost is
  a piece of analysis Mathlib does not have.

## 9. What is not claimed

* That `∫𝒟x e^{iS}` is a measure. It is not (Cameron 1960); the real-time statement is Nelson's limit.
* That FC-1's `𝒮(t)` is "the semigroup generated by `−½Δ + V`". At the pin there are no generators; the
  identification is Mathlib-future. `𝒮` is defined by the Duhamel series and is the object Kac's formula is
  about.
* That a Brownian motion exists at the pin. Every theorem of (E) carries `hB : IsBrownianReal B P`.
* Anything about CSD. Rung (c) is standard quantum mechanics and its Euclidean form, staged for Mathlib.
* The relativistic or field-theoretic path integral. That is the EFT rung of the scope ladder, not row 36.

## References

* R. P. Feynman, *Space-time approach to non-relativistic quantum mechanics*, Rev. Mod. Phys. 20, 367 (1948).
* M. Kac, *On distributions of certain Wiener functionals*, Trans. AMS 65, 1 (1949).
* R. H. Cameron, *A family of integrals serving to connect the Wiener and Feynman integrals*, J. Math. Phys.
  39, 126 (1960) — no countably additive complex path measure.
* E. Nelson, *Feynman integrals and the Schrödinger equation*, J. Math. Phys. 5, 332 (1964) — the Trotter
  definition of the real-time path integral.
* H. F. Trotter, *On the product of semi-groups of operators*, Proc. AMS 10, 545 (1959).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Thm VIII.30–31 (Trotter for bounded
  perturbations); B. Simon, *Functional Integration and Quantum Physics* (Feynman–Kac).
* Corpus: `Mathlib/Analysis/Matrix/{SumOverPaths,DysonSeries,DysonVertex}.lean`,
  `Mathlib/Analysis/NormedSpace/TrotterGeneral.lean`, `CV/WickTime.lean`; `specs/BACKLOG.md` #36;
  `specs/future-work.md` (FP-1).
* Mathlib pin: `Probability/BrownianMotion/{Basic,GaussianProjectiveFamily}.lean`,
  `Probability/Process/Kolmogorov.lean`, `Probability/Distributions/Gaussian/{Real,Multivariate}.lean`,
  `Analysis/Fourier/LpSpace.lean`, `MeasureTheory/Function/LpSeminorm/CompareExp.lean` (`MemLp.mul`).
