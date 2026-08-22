# C2 support: the entangled-positive-measure arc — scoping note

**EXECUTED 2026-08-21, same day as the scoping — items 1–4 all landed** (see
the BACKLOG Q28 row for the full landing record and snag ledger). ~~item 5 stays
research-gated as scoped~~ **ITEM 5 LANDED 2026-08-22** via the MG-2 arc
(`specs/mathlib-gaps-plan.md`): `compositeFubiniStudy_range_segre_null` and
`ae_not_mem_range_segre` — *almost every composite state is entangled*. The
research gate dissolved because the general polynomial-zero-set lemma was never
needed: the Segre cone lies in the zero set of ONE coordinate quadratic (the
`segre_minor_eq` corner minor through the index bijection), which is null by
Fubini slicing, and Fubini–Study is a Lebesgue-absolutely-continuous
pushforward (`fubiniStudyMeasure_null_of_cone`). One route improvement over the plan below: item 2b's
perturbation is a single standard-basis vector `e_{(j₁,k₁)}`, not `a' ⊗ b'` —
no orthogonal complements anywhere — and the reusable minor criterion
`not_mem_range_segre` replaces the bespoke rank argument.

Created 2026-08-21, from the external C2 review brief ("what the paper needs, and
what it does not"), verified claim-by-claim against the corpus the same day. The
Q11 mold: routes checked before scoping, gates and abort criteria fixed in
advance. Companion to `RecordLayer/OnticComposite.lean` (the Segre layer this
extends), `SigmaLayer/IsolationPreparation.lean` (the preparation interface),
and `specs/BACKLOG.md` (Q28).

## Verification record (2026-08-21)

Checked and CONFIRMED, against the tree at `1c5ea8b`:

* `LF4/KahlerInstance.lean:36`-region does say FS-atomlessness "is itself a
  Haar-of-subgroup argument" — the caveat Item 1's pigeonhole route retires.
* `fubiniStudyMeasure_pos_of_isOpen` (`LF4/TypicalityForcing.lean:425`) and the
  `MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ)` transitivity idiom
  (`:429`) exist exactly as the brief cites them.
* `fubiniStudyMeasure_smul_invariant` and `orbit_map_continuous` exist
  (`Mathlib/LinearAlgebra/Projectivization/FubiniStudy*.lean`); the FS measure
  carries an `IsProbabilityMeasure` instance.
* `RecordLayer/OnticComposite.lean` carries `prodVec`, `segre`, `segre_mk`,
  `segre_not_surjective`, and the scope caveat "Measure statements … are not
  attempted; the strict inclusion carries the axiom's weight" — the exact
  sentence 2c retracts (in weak form) and Item 5 would retract in full.
* `CSD.SigmaLayer.Preparation` (`IsolationPreparation.lean:40`) has `region`,
  `measurable_region`, `nonzero_region`, `conditionalMeasure`
  (a `ProbabilityMeasure` reusing LF1's `prepMeasure`), and
  `conditionalMeasure_apply` — Item 3/4's interface, as briefed.
* `kBridge` (`LF4/SingletKahler.lean:279`) and `kBridgeData`
  (`LF4/KahlerWignerLift.lean:118`) exist; the concrete bridge is `c = 1`.
* BONUS the brief did not know: `Projectivization.instCompactSpace` already
  exists (`Mathlib/LinearAlgebra/Projectivization/Topology.lean:392`), so 2a's
  compact-image route is fully stocked; and Item 3's pushforward object already
  has a name — `ProjectiveSector.projectivePreparationLaw`
  (`SigmaLayer/ProjectiveSector.lean:83`). Item 3 is "prove a property of an
  existing definition", not "introduce ρ_ep".

CORRECTED — the brief's one soft spot: **no `MetricSpace`/`Dist` instance on
`ℙ ℂ (EuclideanSpace ℂ _)` exists anywhere in the corpus or in Mathlib.** The
statements written with `Metric.ball` / `dist` (2b, 2c, and Item 4's
`dist [ψ] [φ] < 2ε` instance) are not statable today. The fix below is
topological and strictly cheaper; the Fubini–Study metric itself is recorded as
a separate Mathlib-gap item (it would also serve Item 5 and the quantified
ψ-epistemic prose).

## What C2 needs (and the one selected form)

One fact: near a product ray, the CSD preparation weight charges rays outside
the Segre image. A PBR-style product law is supported on the Segre image, so it
gives that set measure zero; the two measures differ, and no reshuffling repairs
a discrepancy on a coordinate-free set. The **positive form** (every
neighbourhood of a product ray meets the complement in positive μ_FS measure)
is enough; the **null form** (Segre image is μ_FS-null) is Item 5, later.

## Item 2 — entangled rays have positive measure near every product ray
**C2-BLOCKING. Do first. Home: `RecordLayer/OnticComposite.lean`, extending in
place per §8.3b (the scope caveat is superseded at source when 2c lands).**

* **2a `segre_range_isClosed`** — `IsClosed (Set.range segre)`.
  Route: the domain `ℙ × ℙ` is compact (`instCompactSpace` on both factors,
  `Prod` instance), `segre` is continuous, compact image is closed.
  Continuity of `segre`: the brief's route (via `Projectivization.continuous_mk'`
  composed with continuity of `prodVec` on representatives) has the same shape
  as `orbit_map_continuous`; the rep-dependence of `segre`'s definition means
  continuity should go through the mk-descended form (`segre_mk`) — expect the
  quotient-topology descent lemma (`Projectivization` continuity API in the
  staged `Topology.lean`) to carry it. GATE: if continuity of `segre` as
  defined through `.rep` walls (rep is not continuous), restate via the
  descended map on the sphere product — the image is the same set, and only
  the image is used downstream. Size M.
* **2b′ `exists_entangled_mem_nhds`** (metric-corrected form) — for
  `2 ≤ nA`, `2 ≤ nB`, every `p ∈ Set.range segre`, and every open `U ∋ p`:
  `∃ q ∈ U, q ∉ Set.range segre`.
  Route: for `p = [a ⊗ b]` pick `a' ⊥ a`, `b' ⊥ b` (dimensions ≥ 2; Gram
  witnesses as in the ONB machinery), set `w t = a ⊗ b + t • (a' ⊗ b')`, prove
  `t ↦ [w t]` continuous at `0` (continuous into the vector space, then
  `continuous_mk'` off the nonzero locus) and `[w t] ∉ range segre` for
  `t ≠ 0` by the diag(1, t) rank-2 obstruction — the coordinate-comparison
  technique already written inside `segre_not_surjective`'s proof. Size M.
* **2c′ `fubiniStudy_entangled_pos`** (metric-corrected form) — for every open
  `U` with `U ∩ Set.range segre ≠ ∅` (in particular every open neighbourhood
  of a product ray) and every basepoint:
  `fubiniStudyMeasure p₀ (U \ Set.range segre) ≠ 0`.
  Route: `U \ range segre = U ∩ (range segre)ᶜ` is open by 2a, nonempty by
  2b′, positive by `fubiniStudyMeasure_pos_of_isOpen`. Size S given 2a+2b′.
* **2c₀ (freebie, land with 2a)** — the GLOBAL weakest form needs no 2b′ at
  all: `(range segre)ᶜ` is open (2a) and nonempty (`segre_not_surjective`,
  already proved), hence `fubiniStudyMeasure p₀ (Set.range segre)ᶜ ≠ 0`.
  Worth landing immediately: it is already the sentence "entangled rays carry
  positive preparation weight", and C2 can cite it while 2b′ is in flight.

## Item 4 — distinct preparations are not mutually singular (the ψ-epistemic claim)
**Home: `SigmaLayer/IsolationPreparation.lean` (the general lemma) +
`SigmaLayer/Adapters.lean` or a small new witness section (the instance).**

* **4a `conditional_not_mutuallySingular`** — metric-free, exactly as briefed:
  `(D.muL) (P.region ∩ Q.region) ≠ 0 →
  ¬ (P.conditionalMeasure ⊥ₘ Q.conditionalMeasure)`.
  The route is the brief's density argument and it is right that shared
  support alone would NOT suffice: from a singularity witness `S` with
  `μ_Q(S) = 0`, `conditionalMeasure_apply` gives
  `μL(S ∩ Ω_Q) = 0` ⟹ `μL(S ∩ Ω_P ∩ Ω_Q) = 0` ⟹
  `μ_P(S ∩ Ω_P ∩ Ω_Q) = 0`, so `μ_P(Sᶜ) ≥ μ_P(Ω_P ∩ Ω_Q) > 0`,
  contradicting `μ_P(Sᶜ) = 0`. ENNReal division care at the normalisation
  (region measures are ≠ 0 and finite: `muL` is a probability measure on the
  concrete arena; in the abstract statement add finiteness or use
  `≠ 0 ∧ ≠ ⊤` as `prepMeasure_apply` requires). Size S.
* **4b the witness instance** — CORRECTED from the brief's ε-ball form (no
  metric): for `[ψ] ≠ [φ]` there exist preparations `P, Q` with
  `P.region = Q.pi ⁻¹' Uψ`, `Q.region = Q.pi ⁻¹' Uφ`, `Uψ ∋ [ψ]`, `Uφ ∋ [φ]`
  open, and `μL(P.region ∩ Q.region) ≠ 0` — via `Uψ ∩ Uφ ⊇ W` for a chosen
  nonempty open `W` (e.g. `Uψ := U₀ ∪ W`), positivity by the bridge +
  `fubiniStudyMeasure_pos_of_isOpen`. Honest scope note to carry: the
  quantified "any two states closer than 2ε with ε-balls" form NEEDS the
  Fubini–Study metric (Mathlib gap, recorded below); the existence form is
  the ψ-epistemic content and is metric-free. Size S–M.
* **Doc-currency rider:** when 4a lands, the glossary's `psi-epistemic` and
  `does-csd-conflict-with-pbr` pages should cite it — the pages currently
  carry the disjoint-support story of the idealised `δ_p ⊗ Haar` states; 4a
  is the overlapping-support story of PHYSICAL (region) preparations. Both
  are true of different objects; after 4a the pages can and should say both,
  with the theorem name.

## Item 3 — the preparation pushforward has a projective density (ρ_ep)
**Home: `SigmaLayer/ProjectiveSector.lean` or a small
`SigmaLayer/PreparationDensity.lean` beside it — NOT LF2 (see the seam note).**

The object exists: `Q.projectivePreparationLaw P`. To prove, over a bridge
hypothesis `hbridge : Q.projectiveLaw (D.muL) = c • μFS`, `c ≠ 0`:

* `prep_pushforward_absolutelyContinuous`:
  `Q.projectivePreparationLaw P ≪ μFS`. Route exactly as briefed:
  `P.conditionalMeasure ≪ D.muL` from `conditionalMeasure_apply` (a null set's
  intersection is null; division of `0`); `Measure.AbsolutelyContinuous.map`
  pushes it to `≪ Q.projectiveLaw (D.muL) = c • μFS ≪ μFS` (`c ≠ 0`).
* `prep_pushforward_withDensity`:
  `Q.projectivePreparationLaw P = μFS.withDensity ρ_ep` with
  `ρ_ep := (Q.projectivePreparationLaw P).rnDeriv μFS`, by
  `Measure.withDensity_rnDeriv_eq` (both sides probability ⟹ σ-finite,
  Lebesgue decomposition instance free in finite dimension).
* **The seam, healed where C2 v1.01 tore:** add the one corollary that
  mentions both interfaces — on the Kähler arena, the adapter's sector
  (`kahlerProjectiveSector`) discharges `hbridge` at `c = 1` (the
  `k_measure_bridge` marginal identity), so ρ_ep exists concretely for every
  region preparation on `KSigma`. That corollary is the first statement in
  the corpus connecting `SigmaLayer.Preparation` to the LF2/LF4 bridge data,
  which is exactly what the brief asks the seam to carry. Size S–M.

## Item 1 — Fubini–Study atomlessness
**Home: `Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`, beside the
invariance lemmas. Genuine Mathlib-upstream candidate.**

`fubiniStudyMeasure_singleton` : for `2 ≤ N`, `fubiniStudyMeasure p₀ {q} = 0`.
The brief's pigeonhole route is verified ingredient-by-ingredient: transitivity
(`MulAction.exists_smul_eq`, the `TypicalityForcing:429` idiom) + invariance
(`fubiniStudyMeasure_smul_invariant`) give all singletons equal measure `a`;
the probability instance bounds `k·a ≤ 1` for `k` distinct points; only the
supply of arbitrarily many distinct points is new — `t ↦ [e₀ + t • e₁]`
injective (via `Projectivization.mk_eq_mk_iff` + coordinate comparison; mind
the WithLp one-field-structure snags), giving `Infinite (CPN N)` or a direct
`∀ k, ∃ k distinct points`. Then `a = 0`. Corollaries to land with it:
fibres of the Kähler projection are `kMuL`-null (the "Dirac wrapper is
unreachable" step), and the `KahlerInstance` "Haar-of-subgroup" caveat is
superseded at source. Size S.

## Item 5 — the Segre image is null (RESEARCH-GATED, not C2 work)

`segre_range_null` licenses "almost every composite state is entangled". Both
routes run through machinery Mathlib lacks (multivariate polynomial zero sets
are null; or the analytic identity theorem on the connected group). Recorded in
`MATHLIB-GAPS.md` alongside the **Fubini–Study metric on `ℙ`** (which the
corrected 2b/4b forms route around, and which would also upgrade the
ψ-epistemic instance to the quantified ε-ball form). Neither blocks anything
above. Do not schedule without a feasibility pass.

## Order, sizes, gates

| Step | Blocks C2? | Size | Gate / abort |
|---|---|---|---|
| 2a + 2c₀ (closed image + global positive) | yes | M | continuity of `segre` via descended form; abort to sphere-level image restatement if rep-continuity walls |
| 2b′ + 2c′ (local form) | yes | M | the rank-2 obstruction reuse; if the `segre_not_surjective` technique does not lift to parametrised `t`, fall back to 2c₀ for C2 and record 2b′ as a named residue |
| 4a + 4b (non-singularity + witness) | no (ψ-epistemic claim) | S + S–M | none foreseen; ENNReal normalisation care |
| 3 (ρ_ep + the seam corollary) | no | S–M | none — all Mathlib pieces exist |
| 1 (atomlessness + null fibres) | no | S | WithLp injectivity snags only |
| 5 (Segre null) + FS metric | no | research | separate feasibility pass first |

With 2, 4, 3, 1 done, every claim in C2 is machine-checked except the
interpretive framing — the position C1 shipped in. Per the no-manuscript-edits
rule, all of this is repo-side; the paper cites the theorem names.
