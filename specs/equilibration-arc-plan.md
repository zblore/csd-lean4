# Equilibration arc (E1–E5) — plan

Created 2026-08-22 from the author's five-item brief. Horizon: ~5–10 h/week, a two-to-three
month arc, not a sprint. The Q11 mold: **walls checked before scoping**, gates and abort
criteria fixed in advance. Companions: `specs/th1-concentration-scoping.md` (Q24, the
second-moment machinery this builds on), `specs/thermo-plan.md` (TH-1),
`specs/VALIDATION-LEDGER.md` + `specs/validation-claims.tsv` (the claims register),
`MATHLIB-GAPS.md` (Birkhoff row).

## Three corrections to the brief's premises (checked at the pin, 2026-08-22)

The brief is right about the shape of the arc and about which item is dangerous. Three of its
factual premises have moved, and the corrections change cost and ordering:

1. **Item 1 is substantially already provisioned, not "the actual work".**
   * The *first* moment is **landed**: `Thermo.canonical_typicality_expectation`
     (TH-1, 2026-07-05) is exactly `E_{μ_FS}[Tr_B |ψ⟩⟨ψ|] = I_A/d_A`. It already takes the
     tensor decomposition as an **explicit reindex argument** `e` — so the H-TENSOR discipline
     the brief demands is the *existing* convention there, not a new one to invent.
   * The *second* moments are **landed** as of yesterday (Q24): `fs_x_sq_moment`
     (`2/(N(N+1))`), `fs_x_cross_moment` (`1/(N(N+1))`), `fs_linear_sq_moment`,
     `fs_chebyshev_concentration` — obtained by twirl algebra, no integrals.
   * What actually remains of item 1 is Q24's own **gated bricks B4 and B5**, already scoped
     with routes in `th1-concentration-scoping.md`: B4 = general Hermitian observable (via
     diagonalisation transport), B5 = the reduced-state capstone (union bound over `2·d_A²`
     real observables ⇒ trace-norm concentration at polynomial rate). **E1 below is B4+B5
     with the H-TENSOR discipline made explicit**, not a fresh development.

2. **Item 3's premise is partly outdated — but its *worry* is correct and sharpens.**
   * The unrestricted pushforward is **not** merely existential. `∃ c, μ = c • μ_FS`
     (`invariant_finiteMeasure_eq_smul_fubiniStudy`) is a general-invariant-measure statement,
     but on the Kähler arena the constant is **computed and exact**:
     `kahlerFstSector_projectiveLaw` proves `π_*(μ_L) = 1 • μ_FS` (Q28, 2026-08-21).
   * **Why the worry still stands, sharpened.** That `c = 1` proof is a *product-measure
     computation*: `μ_L = μ_FS ⊗ vol_{T²}` and `π = Prod.fst`, so `π_*` is
     `Measure.prod_prod` + `measure_univ`. It transfers to a constraint surface **only if the
     surface is a `π`-cylinder** (`S = π⁻¹(base) `, i.e. fibre-saturated). A generic
     energy-shell constraint is *not* fibre-saturated, and then neither the product
     computation nor `fubiniStudyMeasure_unique` applies — the latter needs `U(N)`-invariance
     of a probability measure on **all** of `ℂℙ^{N−1}`, whereas the restricted object lives on
     `ℙ(H_R)` with only `U(d_R)`-invariance available.
   * So the real question is not "is `c` computed" but **"is the constraint surface
     fibre-saturated, and is the restricted measure `U(d_R)`-invariant on `ℙ(H_R)`?"** That is
     the spike, and the brief's instruction to run it first is correct.

3. **There is no `claims.yaml`.** The corpus register is `specs/validation-claims.tsv`
   (canonical, machine-readable: id, module, constant, status, claim_kind, load_bearing,
   independent_check, finding) with `VALIDATION-LEDGER.md` as its prose face. Item 5's
   registration targets those. The "visibility" mechanism the brief wants already exists in
   three layers and should be used rather than replaced: `scripts/check-claims.sh` guard
   phrases (they fail CI on unqualified prose), the glossary entry `status:` field, and the
   ledger's `status` + `load_bearing` columns.

**Unresolved referent.** The brief says "cross-reference D4/G6". In this repo `D4` is the
audit record about `born_*`-name blindness and `G6` is the root-repair infra item — neither is
about tensor decomposition. These are presumably the author's paper/vault IDs. **Action: the
docstrings will cite the corpus's own composite obligations and leave a marked `TODO(author):
confirm D4/G6 referent` rather than cross-reference the wrong thing.**

## Ordering (the brief's own instruction, adopted)

Dependency order reads E1 → E2 → E3 → E4 → E5. **Execution order is E3 first**, as a spike,
because it is the item most likely to fail and failure is more valuable early. If E3 fails,
E2 and E4 lose their Σ-level content and the arc must be re-scoped (see the abort clause).

---

## E3 (SPIKE, run first) — the restricted pushforward `π_*(μ_L|_S) = μ_FS^{H_R}`

**Goal.** Decide, constructively, whether the base pushforward of the Liouville measure
*restricted to a constraint surface* is the Fubini–Study measure of the restricted sector —
and if so with which constant.

**Shape.**
```
theorem restricted_projectiveLaw
    (R : Submodule ℂ (EuclideanSpace ℂ (Fin N)))      -- the spectral sector H_R
    (S : Set (KSigma N)) (hS : IsFibreSaturated S)     -- ← the load-bearing hypothesis
    (hbase : S = Prod.fst ⁻¹' (raysIn R)) :
    π_* ((μ_L).restrict S) = (μ_L S) • fubiniStudyMeasure_on (raysIn R)
```
**Route.** (i) Define `raysIn R : Set (CPN N)` and the sector's own FS measure — the cleanest
construction is the MG-1/MG-2 machinery: `ℙ(H_R)` is itself a projectivization, so
`fubiniStudyMeasure` applies to it directly, and `fubiniStudyMeasure_null_of_cone` + the
`ballMeasure` presentation (`FubiniStudyLebesgue.lean`, landed 2026-08-22) give the
Lebesgue-side handle on the restriction. (ii) Prove the fibre-saturated case by the same
product computation as `kahlerFstSector_projectiveLaw`. (iii) **Then attack the non-saturated
case honestly** — either exhibit the obstruction or find the invariance that saves it.

**Gates / abort criteria (fixed in advance).**
* **PASS** = the saturated case is a theorem *and* the physically intended constraint surfaces
  (energy shells of a Σ-flow) are shown to be saturated, or a stated restriction class is.
* **PARTIAL** = saturated case proved, general case exhibited as *false or open* with a
  witness. Then E2 proceeds **with the saturation hypothesis carried explicitly in every
  signature**, and the arc's honest scope narrows to saturated constraints. This is an
  acceptable outcome and must be recorded, not smoothed over.
* **FAIL** = the restricted object is provably not FS on `ℙ(H_R)` for any constant. Then E2/E4
  are re-scoped to statements about `μ_FS` alone with the Σ-level relation demoted to a named
  **posit** — and the brief's own warning applies: say plainly that the segment is then
  ordinary quantum statistical mechanics with extra notation, and decide whether it is worth
  landing at all.

**Charter note.** Whichever way it goes, the *decision itself* (theorem vs posit) is the
deliverable the brief asks for. It gets stated in the module header and the ledger, never left
implicit.

> ### ★★ E3 EXECUTED 2026-08-22 — verdict: **FAIL on the naive statement**, with diagnosis
>
> `Thermo/SectorRestriction.lean` (new) + `fubiniStudyMeasure_subspaceRays` in the staged
> `FubiniStudyLebesgue.lean`; 4 pins. The spike did its job on the first attempt: **the naive
> E3 statement is false, and the reason is sharper than "the constant does not compute".**
>
> **What is true** — `projectiveLaw_restrict_saturated`: for a **fibre-saturated** surface
> `S = π⁻¹B` (constraining only the base), `π_*(μ_L|_S) = μ_FS|_B` exactly. This is the honest
> generalisation of the unrestricted `c = 1`, and it needs saturation because the proof is the
> product computation `Prod.fst ⁻¹' B = B ×ˢ univ`.
>
> **What is false** — ★★ `projectiveLaw_restrict_sector_eq_zero`: for a **proper** spectral
> sector `R ⊊ H`, `π_*(μ_L|_{π⁻¹(rays in R)}) = 0`. **The constraint set is Fubini–Study-null**
> (`fubiniStudyMeasure_subspaceRays`: the rays of a proper subspace have the subspace as their
> cone, and a proper subspace is Lebesgue-null by `Measure.addHaar_submodule`). So there is
> nothing to condition on and no normalisation repairs it. `kMuL_sector_eq_zero` says the same
> at the surface level: the constraint surface carries **zero Liouville weight**.
>
> **Why this is the useful outcome.** The brief anticipated a possible failure of the form "the
> pushforward does not restrict cleanly". The actual failure is more specific and more
> actionable: *exact spectral sectors are measure-zero in the ambient arena*, which is a fact
> about the geometry, not about our proof technique. It kills one route decisively and names
> the only two survivors:
>
> 1. **Positive-measure energy windows** (`{p | ⟨H⟩_p ∈ [E, E+Δ]}`). Conditioning is then well
>    defined, but the conditioned law is **not** `μ_FS` on any `ℙ(H_R)` — it is a distinct shell
>    measure. Σ-level content survives; this is a **theorem route**, and it is the recommended
>    one.
> 2. **The sector as its own arena** (`Σ_R = ℙ(H_R) × T²`). Then the pushforward is the existing
>    `c = 1` theorem at dimension `d_R` — but about a *different* `Σ`, so "the constrained
>    dynamics is described by the sector arena" becomes a **posit**.
>
> **Gate outcome: PARTIAL, not FAIL-and-abort.** The arc proceeds, with these consequences:
> * **E2 must be re-scoped to route 1** (energy windows), and its signature must carry the
>   window and its positivity — *not* an eigenspace. Cost likely rises (a positive-measure
>   window needs `⟨H⟩` measurability and a non-degeneracy hypothesis).
> * **E2/E4 must never say "μ_FS on the sector"** — these theorems refute it. The phrase is a
>   candidate `check-claims.sh` guard entry in E5.
> * **E1 is untouched** (it is about the unrestricted `μ_FS`, which is fine).
>
> **The brief's own warning, discharged:** it said item 3 was the thing that could sink the arc
> and that finding out early beats the other four succeeding. It did not sink it, but it *did*
> invalidate the intended formulation of item 2 — which is exactly the value of running it
> first, and would have been expensive to discover after building E1 and E2 on top.

---

## E1 — FS second moment for reduced states (= Q24-B4 + B5, with H-TENSOR explicit)

**Goal.** `E_{μ_FS}‖Tr_B|ψ⟩⟨ψ| − I_A/d_A‖₁²` bounded by an explicit function of `d_A/d_B`.

**Route (already scoped).** B4: general Hermitian observable via diagonalisation transport
(μ_FS unitary invariance + `fs_integral_unitary`, both landed). B5: union bound over a real
observable basis of the `A`-block; `fs_chebyshev_concentration` supplies the per-observable
tail; `‖·‖₁ ≤ √(d_A)·‖·‖₂` converts to trace norm.

**H-TENSOR discipline (the brief's non-negotiable, and it is right).** The bipartition enters
as a **named hypothesis in the theorem signature** — the reindex `e : Fin N ≃ Fin d_A × Fin d_B`
plus `N = d_A * d_B` — exactly as `canonical_typicality_expectation` already does. ⚠️ Now that
`regTensorEquiv` exists (MG-5, 2026-08-22) there is a live temptation to let the decomposition
enter *silently* through the tensor API; the plan forbids it. Rationale to record in the
docstring: a silently-chosen factorisation is a second `D1` — an unstated structural posit
doing load-bearing work.

**Cost.** M (both bricks pre-routed). This is the cheapest item in the arc.

---

## E2 — the constrained microcanonical statement

**Goal.** E1 with `μ_FS` on the unit sphere of a spectral sector `H_R`.

**Required explicit hypotheses (the brief's list, adopted verbatim as signature obligations):**
which restriction; why it is dynamically preserved (an invariance hypothesis on the Σ-flow, not
an assertion); what "effective dimension" means (`d_R = finrank ℂ R`, and its role in the bound).

**Depends on E3's verdict** for the `μ_L ↔ μ_FS^{H_R}` relation, and inherits its status
(theorem / hypothesis-carried / posit). Cost M–L.

---

## E4 — equilibration as a conditional mixing theorem

**Goal.** "If the Σ-flow restricted to the constraint surface has decaying correlations w.r.t.
`μ_L`, then time-averaged reduced states converge to the `μ_FS` average, at a rate controlled
by that decay." **Explicitly conditional; mixing is never proved.**

**Wall check — and a route decision that matters.** Mathlib has `Ergodic` as a structure but
**no mixing definition, no mean ergodic theorem, and no pointwise Birkhoff** (the Birkhoff row
in `MATHLIB-GAPS.md`, re-verified standing 2026-08-22). Therefore:
* **Do not** state the antecedent as abstract mixing and route through ergodic theory — that
  path hits the recorded Birkhoff wall immediately.
* **Do** state the antecedent as **quantitative correlation decay**
  (`|⟨(f∘Φ_t)·g⟩ − ⟨f⟩⟨g⟩| ≤ ε(t)` with `ε` summable/decaying), from which the Cesàro estimate
  on time averages is elementary and needs no upstream ergodic theorem.
This is the difference between a feasible M–L brick and a blocked one.

**Contribution claim, stated carefully.** The value is converting equilibration from a
dephasing statement into an ergodic-theoretic one with an available toolkit — *not* proving
that any particular Σ mixes. Prose must carry the hypothesis every time (see E5).

---

## E5 — non-vacuity witness + register the arc

**Goal (a).** Exhibit at least one concrete `Σ` and Hamiltonian satisfying E2's and E4's
hypotheses **nontrivially** — otherwise E4 is a conditional with an unpopulated antecedent,
which a referee should attack. Corpus precedent for witnesses of exactly this kind:
`Empirical/CSD` witness modules and the `PriceAttainment` sandwich. Candidate: a finite-mode
CV drive where correlation decay is computable in closed form.

**Goal (b).** Register E1–E4 in `specs/validation-claims.tsv` with honest `status`
(`validated` / `qualified` / `conditional`) and `load_bearing` filled in — E4's row must name
its antecedent. Add the guard so E4 cannot appear in external prose without its hypothesis:
a `check-claims.sh` phrase entry (the mechanism that already blocks unqualified Born/typicality
prose), plus the glossary `status:` field if a page is created.

---

## Cut (adopted from the brief)

**Lévy/exponential concentration is dropped from this arc.** Severable, gates nothing above,
and is a Mathlib-PR candidate rather than a CSD result. The `MATHLIB-GAPS.md` row stands
unchanged; Q24's polynomial tier is what the arc consumes.

## Risk register

| Risk | Item | Mitigation |
|---|---|---|
| Restricted pushforward does not transfer | **E3** | Run first as a spike; three-way gate above; PARTIAL is an acceptable, recordable outcome |
| Tensor decomposition enters silently | E1/E2 | H-TENSOR named in every signature; docstring rationale; a check-claims phrase if it recurs |
| E4 read as unconditional | E4/E5 | Antecedent in the statement name, the ledger `load_bearing` column, and a guard phrase |
| Antecedent unpopulated | E4 | E5(a) is a gate on E4's public claim, not optional garnish |
| Birkhoff wall | E4 | Quantitative-decay antecedent, never abstract mixing (see E4 wall check) |
