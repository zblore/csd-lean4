# The top-power identity `ωⁿ/n! = μ_FS` (step 3): scoping note

**Status:** SCOPED 2026-09-07 (late evening, after `c35b090`); **M1 and M3 BUILT 2026-09-08**
(`Mathlib/Analysis/Normed/Module/Alternating/TopForm.lean`;
`Mathlib/Geometry/Manifold/TopFormMeasure.lean` — `chartMeasure`, ★★ `chartMeasure_congr`,
`ChartCover`, ★★ `topFormMeasure`, `topFormMeasure_apply_of_subset_source` for *any* chart, ★
`topFormMeasure_congr_cover`; and `Instances/ProjectiveSpaceChartCover.lean`, the affine atlas of
`ℂℙⁿ` as a cover). The §6 stop condition held: chart-independence was
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` + the Jacobian rule through
`localRep_transition`, no new measure-theoretic lemma; the one lemma that had to be written was
`MeasurableSet.inter_preimage_of_continuousOn`. Cost: one sitting. **M2 BUILT 2026-09-08 as well** (`Alternating/WedgeCLM.lean`: the wedge is a bounded
bilinear map, ★ pullback commutes with it, reindexing is a continuous linear map;
`Geometry/Manifold/WedgeForm.lean`: ★★ `DifferentialForm.wedge`, `domDomCongr`, `constZero`, ★★
`wedgePow`; and `Projectivization.fsTopForm n := wedgePow fsForm n` in
`ProjectiveSpaceFubiniStudyForm.lean`). **M4, M5 and M6(a),(c) BUILT 2026-09-08 too**
(`Instances/ProjectiveSpaceUnitaryAction.lean`: the action in charts is the linear-fractional
`uTrans U i j`, ★★ `fsChartForm_uTransE` / `fsModelForm_uTrans` — the chart form is `U(n+1)`-invariant,
via `ddcForm_log_norm_eq_zero_of_holomorphic`; `TopFormMeasure.lean`: ★★ `topFormMeasure_map_eq`, a
form-preserving homeomorphism preserves the measure, and `isFiniteMeasure_topFormMeasure`, finite on a
compact manifold by local finiteness — **no decay estimate was needed, compactness replaced the
Japanese bracket**; `Instances/ProjectiveSpaceFubiniStudyVolume.lean`: `fsVolume n`, ★★
`fsVolume_map_smul`, ★ `isFiniteMeasure_fsVolume`, and ★★★ `fsVolumeNormalized_eq_fubiniStudyMeasure`
— **the normalised volume of the top power of the Fubini–Study form is `fubiniStudyMeasure p₀`, under the
premise `fsVolume n ≠ 0`**). **M6(b) BUILT 2026-09-08, later the same day** — the §6 fallback (the
premise in the statement) lived for one commit and was then retired. Generic half,
`TopFormMeasure.lean`: ★ `topFormMeasure_ne_zero_of_localRep_ne_zero` — one nonzero chart coefficient
at one point makes the measure nonzero (continuous density, a ball, Haar). Flat half,
`Alternating/WedgeShuffle.lean`: the shuffle sum of `α ∧ β` (`β` a 2-form) on a **pair family** — only
the `k + 1` classes sending the two `β`-slots into one pair survive, and each has a representative made
of **two disjoint transpositions**, sign `+1`, so no sign is ever computed — ★★ `wedge_mul_apply_pairs`,
`(α ∧ β) u = ∑ⱼ α (u ∘ pairRep j ∘ inl)`; then in the Volume module ★★ `wedgePow_stdForm_pairFamily`
by induction — **the `k`-th power of the standard symplectic form on `k` distinct standard pairs is
`k!`** — hence ★★ `wedgePow_fsModelForm_zero_stdBasis` `= (-4)ⁿ n!` (`fsModelForm_zero`), ★★
`fsVolume_ne_zero`, and **★★★ `fsVolumeNormalized_eq_fubiniStudyMeasure` with NO premise** (the
premise forms survive as `_of_ne_zero`). Neither of the two tools named in §2 for M6(b) was used: the
quotient `Perm.ModSumCongr` was handled class by class (`Quotient.out`, and Mathlib's
`mem_sumCongrHom_range_of_perm_mapsTo_inl` to identify a class by where it sends the `inr` slots), and
`domCoprod_alternization_eq` was not needed. **M7 BUILT 2026-09-08 as well — every milestone of this
note is built.** `Analysis/SpecialFunctions/JapaneseBracketIntegral.lean`: the radial integral by the
fundamental theorem of calculus on `[0, ∞)`, the planar one by polar coordinates, and ★★
`lintegral_pi_pow_inv_one_add_sum_norm_sq`, `∫_{ℂⁿ} (1 + ‖w‖²)^{-(n+1)} = πⁿ/n!`, by splitting one
coordinate off (`measurePreserving_piFinSuccAbove`) and induction — the "Gaussian-type integral not on the
shelf" of the M7 row was a one-factor Fubini induction. `Instances/ProjectiveSpaceFubiniStudyMass.lean`:
the density **everywhere** — rotate `w` to the first axis by a unitary matrix (§5's `|det_ℂ|²` identity
was on the shelf as `LinearMap.det_restrictScalars`, so a unitary has Jacobian `1`), where the model form
is the diagonal pullback of the form at the origin (`fsModelForm_single`), hence ★★
`wedgePow_fsModelForm_stdBasis` `= (-4)ⁿ n! (1 + ‖w‖²)^{-(n+1)}`; the hyperplane `z₀ = 0` is null
(`addHaar_submodule` in every other chart), so the mass is one chart integral; ★★ `fsVolume_univ = (4π)ⁿ`;
and **★★★ `fsVolume_eq_smul_fubiniStudyMeasure : fsVolume n = (4π)ⁿ • fubiniStudyMeasure p₀`** — the
top power of the Fubini–Study form IS the Fubini–Study measure, with its constant (the `(4π)ⁿ` is
convention-bound: the chart form carries the potential's `-4`, the wedge its own normalisation; every
factor is in the statement). Deviation from §4 worth
recording: no general pullback of forms was built (M4(a)); the invariance is consumed directly in chart
form, which is all Route U needs.
Step (3) of the
manifold exterior-calculus plan ([`BACKLOG.md`](BACKLOG.md) XL, [`MATHLIB-GAPS.md`](../MATHLIB-GAPS.md)),
the "top forms → measures" step, scoped against what `c35b090` left standing: `ℂℙⁿ` is an analytic
manifold, `fsForm` is a global `C^∞` 2-form on it, `mextDeriv` exists with `d ∘ d = 0`, and
`fsForm_isSymplectic` says the form is closed and non-degenerate.

⚠️ **Every shelf item below was probed at the pin on 2026-09-07 before being written down**, per
the lesson of [`exterior-derivative-scoping.md`](exterior-derivative-scoping.md) §3a: price by what
is *missing*, and confirm each "missing" by grep. Two things are missing, and they are named in §2.

---

## 1. What is being added

The identity the corpus has priced as its last exterior-calculus item since `MATHLIB-GAPS.md` was
written: **the Liouville measure of the Fubini–Study form is the Fubini–Study measure**,

    |fsForm^{∧n}| (normalised) = fubiniStudyMeasure p₀   on ℂℙⁿ,

where the left side is the measure a top-degree form induces (its chart density is the absolute
value of its coefficient against the standard volume form) and the right side is the corpus's
`fubiniStudyMeasure`, the pushforward of Haar on `U(n+1)` under an orbit map
(`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`).

Why it matters, and what it does *not* touch:

* it is the manifold half of `specs/TERMS.md`'s **Liouville** entry ("that this measure **is** the
  Kähler top-power volume `ω^{∧n}/n!`") — the corpus's flow-invariant measure is pinned by
  symmetry, and this identity is what lets it be *called* a symplectic volume;
* it closes residue (iii) of the `MATHLIB-GAPS.md` row (the row's (i) fell with `fsForm_mextDeriv`);
* ⚠️ **nothing downstream waits on it.** `μ_FS` is forced by `fubiniStudyMeasure_unique`, every
  consumer uses the measure, and `R-016` is a generator statement, not a volume statement.

## 2. Shelf and gaps, as probed

**On the shelf (upstream, at the pin):**

* `AlternatingMap.eq_smul_basis_det : f = f e • e.det` — a top-degree alternating map is a scalar
  multiple of the determinant of any basis (`LinearAlgebra/Determinant.lean`);
* `Basis.det_comp : e.det (f ∘ v) = LinearMap.det f * e.det v` — pullback of the top form scales by
  the determinant;
* ★ `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` (`MeasureTheory/Function/Jacobian.lean`):
  change of variables for Lebesgue measure under a map that is injective and differentiable on a
  measurable set, with the factor `|det f'|` — **exactly the shape a chart transition has**;
* `integrable_rpow_neg_one_add_norm_sq (hnr : finrank ℝ E < r) : Integrable (fun x ↦ (1 + ‖x‖²)^(-r/2))`
  (`Analysis/SpecialFunctions/JapaneseBracket.lean`) — finiteness of the Fubini–Study volume in a
  chart is this lemma with `r = 2n + 2 > 2n`;
* `ContMDiff.contMDiff_tangentMap` — smoothness of the tangent map, for the pullback of forms;
* the `MulAction (V ≃ₗ[K] V) (ℙ K V)` and, through it, `U(N)` acting on `ℙ ℂ (EuclideanSpace ℂ (Fin N))`
  by `U • p`, with `MulAction.exists_smul_eq` — transitivity (corpus,
  `Projectivization/{Topology,Unitary,UnitaryTransitive}.lean`).

**On the shelf (this repository):**

* `fubiniStudyMeasure p₀ := Measure.map (orbitMap p₀) unitaryHaarProb`, a probability measure,
  and ★★ `fubiniStudyMeasure_unique (μ) [IsProbabilityMeasure μ] (hμ : ∀ U, map (U • ·) μ = μ) :
  μ = fubiniStudyMeasure p₀` (`FubiniStudyUnique.lean`). **This is the endgame:** the identity is
  proved by exhibiting the top-form measure as a `U(N)`-invariant probability measure, never by
  computing either side;
* `ContinuousAlternatingMap.wedge` (`Alternating/Wedge.lean`) with `wedge_apply` (the shuffle sum)
  and `domDomCongr`; ⚠️ continuity is proved in the *vector family* only, not in the pair `(a, b)`;
* `fsForm`, `localRep_fsSection` (the local representative in every chart is the flat chart form),
  `fsChartForm_apply` (explicit components), `mextDeriv`, `IsSymplectic`, `fsForm_isSymplectic`;
* `MeasurableSpace (ℙ K V) = borel`, `BorelSpace`, `CompactSpace` (`Projectivization/{MeasureSpace,Topology}.lean`).

**Missing (grep-confirmed absent at the pin):**

* ⛔ **Measures or integration on manifolds.** `Geometry/Manifold/Riemannian/Basic.lean` is the only
  file under `Geometry/Manifold` that imports measure theory, and it uses it for path lengths. There
  is no "top form → measure", no manifold volume, no integration of forms. **This is the step's
  genuine Mathlib gap (M3 below).**
* the wedge of *sections* (M2), the pullback of forms along maps of manifolds (M4), and any
  smoothness statement for the `U(N)` action on `ℂℙⁿ` as a manifold map (M4).

## 3. Route: uniqueness, not computation

Three routes exist. **Take the first.**

* **Route U (uniqueness).** Build `|fsForm^{∧n}|` as a measure; prove it is finite, nonzero and
  `U(N)`-invariant; normalise; conclude by `fubiniStudyMeasure_unique`. Every ingredient is a
  general lemma or a computation at *one* point (the chart origin), because transitivity moves
  the origin everywhere. ✅
* **Route D (direct density).** Show the chart density of `fsForm^{∧n}` is `c · (1+‖z‖²)^{-(n+1)}`
  and that `fubiniStudyMeasure` has the same chart density. ⛔ The second half is not available:
  `fubiniStudyMeasure` is *defined* as a pushforward of Haar and its chart density has never been
  computed; that computation is harder than the whole of Route U.
* **Route O (orientation + integration of forms).** Define `∫_M τ` for top forms on an oriented
  manifold. ⛔ Needs orientations on manifolds, absent upstream, and buys nothing here: a measure
  from `|density|` needs no orientation.

## 4. Milestones, in build order

Each milestone is landable on its own, with pins, and is worth landing even if the next stalls.

| # | Milestone | Size | Depends on | What it lands |
|---|---|---|---|---|
| **M1** | **Top-degree flat forms.** For `E` finite-dimensional real with a basis `e : Basis (Fin d) ℝ E`, the coefficient map `E [⋀^Fin d]→L[ℝ] ℝ → ℝ`, `α ↦ α e`, with `α = (α e) • det` (`eq_smul_basis_det` through `toAlternatingMap`) and `(α.compContinuousLinearMap L) e = det L * α e` (`Basis.det_comp`). | S | — | `Mathlib/Analysis/Normed/Module/Alternating/TopForm.lean` |
| **M2** | **Wedge of sections.** (a) the wedge as a bounded bilinear map in `(a, b)` (norm bound from `wedge_apply`), hence `C^∞`; (b) the flat identity `(a ∧ b).compCLM L = (a.compCLM L) ∧ (b.compCLM L)`; (c) `DifferentialForm.wedge` with the local representative of the wedge being the wedge of the local representatives (the `localRep_transition` plumbing again); (d) the iterated power re-indexed to `Fin (2n)`: `fsTopForm : DifferentialForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n)) ∞ (Fin (2n)) ℝ`. ⚠️ Name it `fsTopForm`, not `liouvilleForm`, until M6 earns the word (vocabulary registry, §5). | M | — | `Mathlib/Geometry/Manifold/WedgeForm.lean` |
| **M3** | ★★ **The measure of a top form** on a manifold with a **finite atlas given as data** (a `Fintype ι`-indexed family of charts covering `M`; for `ℂℙⁿ` the `n+1` affine charts `chartAtIdx`). Definition: on the measurable partition `Sᵢ := sourceᵢ \ ⋃_{j<i} sourceⱼ`, the measure `Measure.sum i, map (chartᵢ.symm) ((Lebesgue.restrict (chartᵢ '' Sᵢ)).withDensity (ofReal |coefficient of localRep τ in chart i|))`. Theorems: (a) **chart-independence** — on an overlap the two chart expressions agree, by M1's `det` scaling of the coefficient plus `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the transition (injective, differentiable on the open overlap); (b) hence the value is independent of the ordering of the atlas and equals, on any single chart source, the pushforward of the chart density; (c) **naturality**: for a diffeomorphism `g` of `M` (smooth, smooth inverse) `measureOf (pullback g τ) = map g⁻¹ (measureOf τ)` — the same change-of-variables lemma, applied to the chart expression of `g`. | **M–L** (the gap) | M1 | `Mathlib/Geometry/Manifold/TopFormMeasure.lean` |
| **M4** | **`U(N)` acts smoothly; `fsForm` is invariant.** (a) `pullback f α` for a `C^∞` map `f : M → M'` (fibre: `(α (f x)).compCLM (mfderiv f x)`), smooth by `contMDiff_tangentMap` and the local-representative plumbing; (b) `U • ·` is `C^∞` on `ℂℙⁿ` — in the affine atlas it is a linear-fractional map, `ContDiffOn.div` as in step (0); (c) `pullback (U • ·) fsForm = fsForm`: in charts the potential shifts by `-2 log ‖L z‖` with `L` **affine** (the `0`-th coordinate of `U (1, z)`), so `ddcForm_log_norm_eq_zero` must be generalised from linear `L` to affine / non-vanishing holomorphic `f` (its proof already goes through a local holomorphic logarithm, so this is a restatement), then the argument of `fsChartForm_transE` verbatim. | M | — | `Mathlib/Geometry/Manifold/Pullback.lean`; `Instances/ProjectiveSpaceUnitaryAction.lean` |
| **M5** | **Invariance of the volume.** `measureOf fsTopForm` is `U(N)`-invariant: M3(c) with M4(c), plus "pullback commutes with the wedge power" (M2(b) at section level). | S–M | M2, M3, M4 | in `Instances/ProjectiveSpaceFubiniStudyVolume.lean` |
| **M6** | ★★★ **The identity.** (a) **finite**: in the chart at the origin the coefficient is continuous and bounded by `C (1+‖z‖²)^{-(n+1)}`, integrable by the Japanese bracket with `2n+2 > 2n`; ⚠️ finiteness needs the bound in *every* chart of the partition — the same bound holds in each affine chart by symmetry, or use M5 to move a neighbourhood of the origin around (compactness: finitely many translates cover); (b) **nonzero**: the coefficient at the origin is nonzero — `fsChartForm 0 = -4 • fundamentalFormAlt` (`fsChartForm_zero`), so this is the **flat** statement `fundamentalFormAlt^{∧n} ≠ 0`, which is the evaluation of the `n`-fold wedge of the standard symplectic form on the standard basis `(e₁, i e₁, …, eₙ, i eₙ)` through `wedge_apply` — by induction on `n` splitting `ℂⁿ = ℂ ⊕ ℂⁿ⁻¹`, or directly as a shuffle count; ⚠️ **this is the one computation with no shelf besides M3**, and it is where the wedge's normalisation convention enters (only `≠ 0` is needed here; the constant is M7); (c) normalise `μ := (μ univ)⁻¹ • μ`, invariance survives scaling, apply `fubiniStudyMeasure_unique`. | M | M2–M5 | `Instances/ProjectiveSpaceFubiniStudyVolume.lean`: ★★★ `fsTopForm_measure_eq_fubiniStudy` |
| M7 | *(optional)* **The constant.** `measureOf fsTopForm univ = (4π)ⁿ · (normalisation of the wedge)` via `∫_{ℂⁿ} (1+‖z‖²)^{-(n+1)} = πⁿ/n!` — needs the Gaussian-type integral, which is not on the shelf in that form. State the identity as "`= c • μ_FS` with `0 < c < ∞`" in M6 and land the value separately. | M | M6 | same file |

**Build order:** M1 → M3 in one sitting (M3 is the gap and should be attempted first, while the
chart plumbing of `c35b090` is fresh); M2 and M4 are independent of it and of each other; M5–M6
assemble. If only one thing lands, let it be **M3**: it is the upstream-shaped piece, it is what
"integration on manifolds" is missing, and it is reusable for every later volume statement.

## 5. Traps, all known in advance

* **Vocabulary ratchets and registries.** `check-terms` pins unmarked uses of `top-power volume`,
  `ω^{∧n}/n!` (Liouville) and `top-power identity` (Kahler) in Lean files: every module here carries
  `**TERM-SCOPE(Liouville)**` and `**TERM-SCOPE(Kahler)**`. `check-claims` requires every
  declaration *named* with `Liouville`/`symplectic`/`Kahler` to be in `DECLARED_SYMPLECTIC_VOCAB`
  (or the theorem-level list) with a parity justification. **Name the top form `fsTopForm` and the
  measure `fsTopForm.measure` until M6 is proved; then, and only then, add a `liouville`-named
  alias with its ledger line (`ℂℙⁿ`, real dimension `2n`, even).**
* **Two spellings of the same type.** `fubiniStudyMeasure` lives on `ℙ ℂ (EuclideanSpace ℂ (Fin N))`;
  the manifold structure is on `ℙ ℂ (Ambient n)` with `Ambient n = EuclideanSpace ℂ (Fin (n+1))`.
  Same type when `N = n + 1`; state M5–M6 with `N := n + 1` and never with a subtraction.
* **Real determinants of complex-linear maps.** The change-of-variables factor is the *real*
  determinant of the transition's derivative on `Fin n → ℂ` viewed over `ℝ`; for a `ℂ`-linear map
  it is `|det_ℂ|²`. M3 never needs this identity (it uses `|det|` abstractly), but M7 does; probe
  `LinearMap.det_restrictScalars` before relying on it.
* **No orientation.** The measure uses `|coefficient|`; do not reach for `Orientation` or
  `Basis.det` sign conventions. (Route O is rejected for exactly this reason.)
* **Partition, not partition of unity.** M3's definition sums over a measurable partition of the
  finite atlas, so no bump functions and no paracompactness enter. The price is a finite atlas
  given as data, which `ℂℙⁿ` has and which is the right generality for a first upstream PR.
* **Wedge normalisation.** Mathlib's flat `extDeriv` docstring warns its normalisation "differs
  from other definitions by a factor"; the corpus's `wedge` has its own. M6 needs only `≠ 0`; keep
  every constant out of M6's statement and let M7 own them.
* **`TangentSpace`-vs-model instance path.** Every identity in M2–M4 is stated on the model via a
  `toFlat`-style cast and finished pointwise, exactly as `localRep_mextDeriv` was. Do not `rw` a
  CLM equality across the path; it will not work and it is not a wall.

## 6. Deliverables and stop condition

**Deliverables** (each with pins in `Tests/AxiomAudit/MathlibStaging.lean`, each root-imported):
`Mathlib/Analysis/Normed/Module/Alternating/TopForm.lean` (M1);
`Mathlib/Geometry/Manifold/WedgeForm.lean` (M2); `Mathlib/Geometry/Manifold/TopFormMeasure.lean`
(M3); `Mathlib/Geometry/Manifold/Pullback.lean` and
`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceUnitaryAction.lean` (M4);
`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyVolume.lean` (M5–M7). These are
registered in `scripts/check-doc-promises.sh` as promised-not-yet-built; remove each entry when
its brick lands.

**⛔ Stop condition.** If M3's chart-independence (§4, M3(a)) is not a direct application of
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` plus `Basis.det_comp` — if it needs a new
measure-theoretic lemma rather than a rewrite — **stop and re-scope the definition**: the measure is
being built on the wrong side of the chart. And if M6(b), the flat non-vanishing, resists the
induction, land M1–M5 and the identity *up to the hypothesis* `fsTopForm ≠ 0` stated as an explicit
premise; a premise a `#print axioms` reader can see is worth more than a hidden `sorry`, and it is
the one place in this plan where the mathematics, not the plumbing, is the work.

## 7. Rating

**L** overall: M3 is **M–L** and is a genuine gap; M6(b) is **M** and is genuine mathematics (a
shuffle count); everything else is the chart plumbing that `c35b090` has now made routine. P(success)
for the identity up to a constant: **medium–high** *by Route U*; for the constant (M7): medium.
Nothing here has been "attempted and walled": the §3a discipline applies — a failed tactic is
evidence about the tactic, and every claimed absence above was a grep.

## References

* `Mathlib/LinearAlgebra/Determinant.lean` — `AlternatingMap.eq_smul_basis_det`, `Basis.det_comp`.
* `Mathlib/MeasureTheory/Function/Jacobian.lean` — ★ `lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
  `map_withDensity_abs_det_fderiv_eq_addHaar`.
* `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean` — `integrable_rpow_neg_one_add_norm_sq`.
* `Mathlib/Geometry/Manifold/ContMDiffMFDeriv.lean` — `ContMDiff.contMDiff_tangentMap`.
* `CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`, `FubiniStudyUnique.lean` —
  `fubiniStudyMeasure`, ★★ `fubiniStudyMeasure_unique`, `fubiniStudyMeasure_smul_invariant`.
* `CsdLean4/Mathlib/Analysis/Normed/Module/Alternating/Wedge.lean` — `wedge`, `wedge_apply`, `domDomCongr`.
* `CsdLean4/Mathlib/Geometry/Manifold/{DifferentialForm,ExteriorDerivative,SymplecticForm}.lean`,
  `Instances/ProjectiveSpaceFubiniStudy{,Form,Symplectic}.lean` — what step (3) stands on.
* `specs/exterior-derivative-scoping.md` §3a — the pricing discipline this note follows.
* `specs/TERMS.md` (Liouville, Kähler, symplectic / manifold), `specs/future-work.md`.
