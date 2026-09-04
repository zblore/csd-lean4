# Record layer (MD-1) — plan: measurement as context-fixed regions + the ontic record

> **Status: the KINEMATIC record interface is BUILT 2026-07-25 (see §4).** *Addendum 2026-08-02:*
> **the dynamical layer is now COMPLETE through the join arena** — of the three items the
> correction below listed as open, general-`N` A7 is **discharged** (fibred reading canonical,
> `GlobalBasin`), the de-isolation dynamics is **constructed** (shear/swap witnesses, with the
> piecewise-Hamiltonian classification replacing the `H_int`-as-smooth-flow expectation), and the
> fibred Σ's A1 status was resolved by the parity correction (`KSigma = ℂℙ^{N-1} × T²`). See
> `reconstruction-status.md` §2a and `BACKLOG.md`. The original status and correction follow as
> the historical record. **(Original:) MD-1 is NOT discharged.**
> Formalized in Lean end-to-end: measurement as `context + unknown microstate → record` on the
> base×fibre Σ, Born = the LLN over the unknown microstate, probabilities = the Kähler moment map.
>
> ⚠️ **Scope corrected 2026-07-28 after an external review.** Earlier wording here ("the record
> layer is BUILT", the staging table's "feature (A) DISSOLVED") overstated it. What is proved is:
> *given* a basin partition, an unknown microstate selects one definite record, and repeated i.i.d.
> preparations obey the LLN. What is **not** proved:
> 1. **General-`N` A7** — the partition is constructed from the preparation (`bornContext ψ`,
>    `cdfCell (bornRate ψ)`), so Paper C's `Ωᵢ(M)`, fixed by the apparatus alone, is established
>    only at `N = 2` (§2, `LF4/QubitBorn.lean`). `N ≥ 3` is **open in both directions** — the
>    earlier "provably dead" verdict rested on numerics plus an informal argument and is retracted
>    (`BACKLOG.md`).
>    ⚠️ **UPDATED 2026-07-31 — this item is now split.** A **fibred** context-fixed partition exists
>    at every `N`: `RecordLayer/GlobalBasin.lean`'s `globalBasin c i` reads a `ContextField`'s rate
>    **at the ontic point**, so its events mention no preparation, and `globalBasin_born` still
>    returns `‖⟨eᵢ,ψ⟩‖²`; `RecordLayer/GlobalRecordClosure.lean` carries the five record-layer facts on
>    it. So the **preparation-indexing** half is closed. What remains open is the **base-only** half —
>    whether `Ωᵢ(M)` can live on `ℂℙⁿ⁻¹` itself, which is the ⏸ parked `ContextFixedA7` chain, and
>    which of the two Paper C actually intends is a question about the axiom, not about the Lean.
> 2. **The de-isolation dynamics** — `DeIsolationInteraction.basin_rate` is a *hypothesis field*;
>    no `H_int` generating those basins is constructed. `DeIsolationFlow.lean` states this
>    correctly; §3c's staging row did not.
>    ⚠️ **UPDATED 2026-08-02 — the dynamical layer now EXISTS** (v0.7.0, `MeasurementProtocol` /
>    `ShearWitness` / `SwapWitness` / `SwapLuders`): records are created from a ready state by an
>    explicit measure-preserving propagator, persist, carry Born weights, and implement the
>    rank-one Lüders update. The *Hamiltonian origin* of those propagators is **permanently
>    scoped** (user decision 2026-08-02; no manifold Hamiltonian-flow API in Mathlib — verified a
>    tooling gap, not a falsity). `basin_rate` remains a hypothesis field in the OLD
>    `DeIsolationInteraction` interface only.
> 3. **That the fibred Σ is an A1 sector** — `ℂℙⁿ⁻¹ × ℝ` with Lebesgue restricted to `[0,1)` is a
>    measurable record model: non-compact fibre, no Kähler structure, measure not shown to be
>    Liouville. It is not the completed Paper C ontic surface.
>
> This doc is retained as the record of the build and of those three open items.
>
> **★ UPDATE 2026-07-26: the qubit context-fixed Born rule is now formalized END-TO-END in Lean**
> ([`LF4/QubitBorn.lean`](../CsdLean4/LF4/QubitBorn.lean) `qubitBorn`, foundational-triple, pinned —
> see §2 and §4). The epistemic hemisphere partition `{H±(n)}` is provably **context-fixed**
> (prep-independent) and the Born weight `|⟨n|ψ⟩|²` is *derived* from the ontic Fubini–Study
> typicality measure via the CSD spread density — for the **qubit**. Residual: the general-`N`
> context-fixed partition, then the **extensions** (continuous spectra, relativistic locality,
> identical particles). Historical planning notes (qubit crux, N≥3) follow.
>
> **★ STRUCTURAL LESSON (2026-07-27) — [`sigma-fibre-contextuality.md`](sigma-fibre-contextuality.md).**
> The general-`N` residual taught us a fact about Σ: a base-only, `U(N)`-covariant, nonnegative
> context-fixed density is **conjectured not to** reproduce Born for `N ≥ 3` — numerics plus an
> informal operator argument, **not a proof** (corrected 2026-07-28; the general-`N` item is OPEN,
> `BACKLOG.md`). The `CP¹=S²` antipode has no `N ≥ 3` analogue, and this is **not** Gleason. On that
> conjecture measurement contextuality
> lives on the projective **base** only at `N = 2` and necessarily in the **fibre** for `N ≥ 3`. The
> fibre is load-bearing, not decorative — a *constraint on Σ's structure*, not a defect (existence of
> a Born fibre-partition is proven, Phase-2b). Read that doc before touching general-`N` context-fixing. Open-item row:
> [`BACKLOG.md`](BACKLOG.md) "record layer (MD-1)". This doc holds the detail; BACKLOG
> holds the one-line status.

## 1. The correct basis (do not blur these)

- **Ω-outcome-regions {Ωᵢ(M)} are EPISTEMIC** — on `ℂℙⁿ⁻¹`, determined by the apparatus
  context M (Paper C **A7**: "epistemic outcome regions {Ωᵢ(M)} ⊂ CPⁿ⁻¹"). They are NOT
  on Σ; do not "move them onto Σ".
- **The record is ONTIC** — the selection in Σ of *which* region the single trajectory
  realizes (equivalently which `π⁻¹(Ωᵢ(M)) ⊂ Σ` basin `ω(t)` occupies).
- **Born is the ontic typicality volume:** `P(i|M) = μL(π⁻¹Ωᵢ(M) ∩ Ω₀)/μL(Ω₀)` on Σ
  (= `∫_{Ωᵢ(M)} ρ_ep dμ_FS`), via typicality over the prepared region `Ω₀` (Paper A) + the
  SU(n)-fixed μ_FS (Paper B).
- **The ψ-dependence lives in the PREPARATION, not the region.** A context-fixed region has
  fixed volume, so it cannot equal a ψ-varying Born weight; the state must enter through the
  prepared region `Ω₀(ψ)` / the epistemic density `ρ_ep,ψ`. This is the crux, and the point
  of departure from the corpus's `bornRegion ψ` (which bakes ψ into the region geometry so
  its volume = |⟨eᵢ|ψ⟩|² — a preparation-indexed shortcut).

## 2. The qubit crux — SOLVED analytically AND FORMALIZED IN LEAN (2026-07-26)

> **★ Now machine-checked.** The analytic argument below is fully formalized: see the "Qubit identity
> (§2) — COMPLETE END-TO-END" entry in §4 for the 7-module chain and `qubitBorn`. What follows is the
> original analytic derivation (retained for exposition).

Setup: `ℂℙ¹` = Bloch sphere `S²`, μ_FS = uniform normalized area. Measurement context M
along axis `n` gives the **context-fixed** outcome regions = hemispheres
`H±(n) = {λ : ±λ·n > 0}` (boundary = equator, μ_FS-null). A prepared state ψ has Bloch
vector `m`, with `|⟨n₊|ψ⟩|² = (1 + m·n)/2`.

**Result.** The preparation is *not* a Dirac at [ψ]; it is the spread density
$$\rho_m(\lambda) = 4\,(m\cdot\lambda)_+ = 4\max(m\cdot\lambda,\,0)$$
(non-negative, `∫ρ_m dμ_FS = 1`, cos-weighted on the hemisphere around m). Then for
**every** context axis `n`:
$$\int_{H_+(n)} \rho_m \, d\mu_{FS} = \frac{1+m\cdot n}{2} = |\langle n_+|\psi\rangle|^2 .$$

**Proof (analytic).** `4(m·λ)₊ = 2(m·λ) + 2|m·λ|`. Its odd part is the pure dipole
`2(m·λ)` (ℓ=1 only). `∫_{H₊(n)} ρ_m = ½∫ρ_m + ½∫sign(λ·n)ρ_m = ½ + ½·(m·n)`, using
`∫sign(λ·n)ρ_m = 2∫sign(λ·n)(m·λ)dμ = 2·½(m·n)` (the `|m·λ|` term is odd·even ⟹ 0), and
`∫sign(λ·n)(m·λ)dμ = ½(m·n)` from rotational covariance + `∫|λ·n|dμ = ½` (Archimedes'
hat-box: λ·n ~ Uniform[−1,1]). ∎ Spot-checked n = m, n ⊥ m, n = −m.

**What it reveals.**
- **"Preparing ψ" = the spread ρ_m of ontic states around ψ**, not the microstate landing
  on [ψ]. This makes "typicality over repeated preparations" concrete: repeated preps
  scatter the epistemic point as ρ_m; the measurement counts hemisphere fractions.
- **The record is clean:** `λ ↦ which hemisphere H±(n)` — context-fixed, prep-independent,
  the ontic selection. A genuine `RecordedFact`, strictly better than `vnPointerOutcome`.

## 3. The N≥3 problem — OPEN (NOT a Gleason no-go)

**Correction (2026-07-25).** An earlier version claimed Gleason forbids the base-only route
for N≥3. **That is wrong.** The outcome regions {Ωᵢ(M)} are *context-fixed* — they **depend
on the apparatus context M** (the Voronoi cell of eᵢ is defined relative to the *whole*
basis). So `P(i|M) = ∫_{Ωᵢ(M)} ρ_ψ` depends on the projector eᵢ **and** the basis M → it is a
measurement-**contextual** model, which Gleason/KS do **not** forbid (KS forbids
noncontextual *deterministic value* assignments; this is a contextual *probabilistic* model).
So N≥3 is **open**, not closed, and whether the fibre is even needed is the question.

**The real question (decisive):**
> Does a **base-only** preparation density reproduce Born for N≥3, or is the fibre needed?
> By unitary covariance, any base-only prep is `ρ_ψ(φ) = g(|⟨ψ|φ⟩|²)` for a *single* function
> `g:[0,1]→ℝ≥0`. Is there a `g` with `∫_{Ωᵢ(M)} g(|⟨ψ|φ⟩|²) dμ_FS = |⟨eᵢ|ψ⟩|²` for **all**
> contexts M and states ψ?

Partial evidence (basis-vector prep, ψ = eⱼ): taking `g` supported on `(½,1]` — the
"unambiguous cap" where φ is closest to eⱼ for *every* basis containing eⱼ — gives
`∫_{Ωⱼ(M)}g = 1`, `∫_{i≠j}g = 0`, **M-independently**. So the base-only route is not
obviously dead; the open case is **generic ψ** (where the cap around ψ overlaps the eᵢ-cells).

**Two outcomes, both informative:**
- **(A) g exists** ⟹ base-only reproduces Born, **no measurement-fibre needed**; the qubit
  route (i) generalizes. (The many-to-one fibre would then be motivated by other structure —
  records, dynamics — not by measurement.)
- **(B) no g** ⟹ the base is insufficient; the many-to-one **fibre of Σ** must carry the
  extra structure — *here* "constrain Σ" fuses with MD-1:
  > Design the Σ-fibre + prepared region `Ω₀(ψ) ⊂ Σ` so that
  > `μL(Ω₀(ψ) ∩ B_i(M)) / μL(Ω₀(ψ)) = |⟨eᵢ|ψ⟩|²` for all contexts M, the fibre supplying the
  > context-dependence — where the ontic outcome basins `B_i(M) ⊂ Σ` use the fibre (they need
  > NOT be plain π-pullbacks; if the outcome depended only on `π(ω)` the fibre would be inert).

**Settling A vs B is the decisive next step** (Phase 1 below).

### Phase 1 RESULT (2026-07-25): Outcome B — base-only fails at N=3

Decisive numerical test done (`scripts/experiments/record_layer_base_only_test.py`,
Monte-Carlo on ℂℙ² + non-negative least-squares feasibility, `nnls`). The Born condition is
linear in `g`; the diagnostic is the non-negative residual `r_nn` vs the noise floor `r_unc`
(the signed-`g` residual):

- **Qubit control (d=2, base-only KNOWN to work):** `r_nn ≈ r_unc ≈` MC noise (0.0008) — a
  non-negative `g` exists. **Validates the test.**
- **Qutrit (d=3):** `r_unc → 0` with more samples (a *signed* `g` fits Born), but `r_nn`
  **plateaus at ~0.008 (~10× the noise floor) and does not shrink with 4× samples** — a genuine
  model-misfit floor. **No non-negative base density fits.**

So a covariant base-only density on `ℂℙ²` reproducing Born over FS-Voronoi regions **is forced
to go negative** — the honest N=3 analog of the qubit's `c=2`, with no rescue. **Outcome B: the
fibre is needed** — now *earned numerically* (this replaces the retracted Gleason argument;
the impossibility is real but it is a forced-negativity result for the contextual Voronoi base
model, established empirically and validated by the qubit control). (Diagnostic caveat learned:
`min(g_unc)<0` is a red herring — `lstsq` returns the min-norm solution, negative even for the
qubit where a non-negative `g` exists; rely on `r_nn`.)

**Honest caveats:** (i) tested for **FS-Voronoi** regions (Paper C's canonical choice) — but
note Voronoi = *sharp regions on the base* ℂℙⁿ⁻¹, i.e. exactly the base-only structure, so this
is not a real limitation: the resolution abandons base-sharp regions entirely (see §3b);
(ii) numerical, not yet a proof (the robust plateau + forced negativity suggest a clean "no
covariant base density reproduces Born via base-sharp regions for N≥3" theorem).

### §3b. Phase 2b — the fibre model (Outcome B resolved: a working construction, N≥3)

**Correct structure (drop Voronoi / base-sharp regions).** For a *sharp* prep the epistemic
state is definite, `π(ω)=[ψ]`, so the prepared region sits **in the fibre over [ψ]**:
`μL|Ω₀ = δ_{[ψ]} ⊗ ν` (this is already the corpus's `push_dirac`, `π_*μ_ψ = δ_ray`). The
measurement carves the **fibre**, and the whole problem is one object:

> **Born partition of the fibre.** For each base point `φ` and context `M`, a partition
> `{Fᵢ(M,φ)}` of `(F,ν)` with `ν(Fᵢ(M,φ)) = |⟨eᵢ|φ⟩|²`. Outcome `ω=(φ,ξ)↦i` iff `ξ∈Fᵢ(M,φ)`;
> Born = fibre volume. Probabilities depend only on `(eᵢ,φ)` (measurement-noncontextual, as QM
> demands); regions may depend on the full `M` (contextual). Base-only failed precisely because
> it forces this partition onto ℂℙⁿ⁻¹ itself (§3).

**Existence + canonical instance (VERIFIED, N=3).** The Born partition always exists; the
canonical symmetric one (no outcome ordering) is a noisy-argmax:
`F=ℝⁿ, ν=iid Gumbel, Fᵢ(M,φ)={ξ : i=argmaxⱼ(log|⟨eⱼ|φ⟩|²+ξⱼ)}` ⟹ `ν(Fᵢ)=softmaxᵢ(log b)=bᵢ`
**exactly** (Gumbel–max). Numerically confirmed at N=3 to MC precision, incl. the KS-relevant
check that two bases sharing a vector give the same outcome probability (context-independent
prob, context-dependent regions). Minimal fibre dim `= n−1`; `n=2` → a single logistic threshold
(recovers the qubit `ρ_m`). Script: `scripts/experiments/record_layer_fibre_gumbel.py`.

**Honest boundary — existence ≠ CSD-native.** The Gumbel model reproduces Born by *injected
iid noise*; it is a valid ontological model that **settles the architecture** (the fibre can
carry the contextuality), but it is NOT yet the CSD mechanism, which needs the fibre randomness
from **typicality** (a fixed geometric fibre measure) resolved by a **deterministic de-isolation
flow**. The genuine remaining research:
1. **Canonical geometric fibre** `(F,ν)` — compact, natural Born partition, `μ_FS`-null
   boundaries, continuous in `(M,φ)` (is `T²` rich enough? a simplex? `ℂℙⁿ⁻¹` self-similar?).
2. **The deterministic de-isolation flow** `Φ_M:Σ→Σ` whose basins `Bᵢ(M)=Φ_M⁻¹(pointer_i)` ARE
   the Born partition — Born as a typicality volume of a *flow-carved* basin, not injected noise
   (the corpus's LF5 pointer-flow, generalized to be N≥3-contextual). **← the real next target;
   where typicality + Kähler dynamics enter.**
3. Sequential/Lüders + POVM via the same fibre.

### §3c. The dynamical picture (2026-07-25) — first-passage race at moment-map rates

A CSD-native shape for the fibre model, verified
(`scripts/experiments/record_layer_race_moment.py`), that is a *flow* and grounds the Born
square in the corpus's own geometry:

- **Measurement = a first-passage race.** `Σ = ℂℙⁿ⁻¹ × F`, base pinned to `[ψ]`, fibre carries
  `n` clocks; clock `i` runs at speed `bᵢ` and fires at `ξᵢ/bᵢ`; **outcome = first to fire**.
  `P(first=j)=bⱼ` exactly. The outcome is the *first jump* — the de-isolation completion, not a
  static sample.
- **The Born SQUARE = the torus moment map.** The rates `bᵢ = |⟨eᵢ|ψ⟩|²` **are** `momentMap([ψ])ᵢ`
  of the `Tⁿ` action `z↦|zᵢ|²` (corpus `momentMap_mk_eq_inner_sq`). So the square is Kähler-geometric,
  not injected.
- **The exponential fibre measure is FORCED** — ✅ **now a corpus theorem (2026-08-24)**, not a
  citation: `ProbabilityTheory.hasRaceProperty_iff_exists_expMeasure`
  (`Mathlib/Probability/IidClockRace.lean`, Q12-c2). For iid linear clocks, first-to-fire `= bᵢ`
  holds **iff** the waiting times are exponential (memoryless/Poisson), so the fibre typicality is
  pinned by the first-passage structure rather than chosen. This is exactly the **quantum-jump /
  continuous-measurement** form (jumps at exponential times, rates `∝|amplitude|²`) — a developed
  formalism to anchor to.
  - ⚠️ **State the second conjunct with it.** `HasRaceProperty` quantifies over the **number of
    clocks**; at a fixed number of outcomes `n` the race supplies only `n−1` moments, and finitely
    many moments determine nothing. What is forced is the exponential law *given that one clock law
    serves every `n`* — the measurement-independence `specs/sigma-fibre-contextuality.md` already
    commits to. This is where that commitment earns its keep.
  - ⚠️ **A posit removed, not a mechanism supplied.** The *law* is no longer a choice; **no dynamics
    carves the race cells**. The frontier half (`Q12-d`) stays blocked by `W1`, and neither
    `DeIsolationInteraction` witness is dynamical.

**The decomposition (2026-07-25) — two grounded parts.** The measurement factorises as
*(moment map sets the rates) × (mixing de-isolation gives the exponential first-passage)*:

- **(A) exponential first-passage — DERIVABLE (not injected).** For a **mixing** de-isolation flow
  with disjoint environment targets `Aᵢ`, the first target entered is `i` with probability
  `→ μ(Aᵢ)/Σⱼμ(Aⱼ)` — the **exponential law for competing hitting sets** (Galves–Schmitt / Abadi /
  Hirata). So a deterministic mixing environment + typicality *produces* the exponential-clock /
  first-jump structure; no injected noise. (Do not simulate — it is a theorem; naive chaotic-map
  sims also hit float precision walls.)
- **(B) rates = the moment map.** Winner probabilities `∝ μ(Aᵢ)`, so Born needs
  `μ(Aᵢ) ∝ bᵢ = |⟨eᵢ|φ⟩|² = momentMap([ψ])ᵢ` — the torus moment map (`momentMap_mk_eq_inner_sq`),
  Papers A/B territory.

**The one remaining crux (narrowed, precise):** exhibit a **de-isolation coupling** whose environment
target-measures are `∝ the moment map` — tying `|⟨eᵢ|φ⟩|²` to the environment geometry. That is the
last "Born from the dynamics" step; LF5's `measurementFlow` + the moment-map engine + the
exponential-law theorem are the scaffolding.

**Feature (B) rates = moment map — GROUNDED IN LEAN 2026-07-25:**
[`RecordLayer/MomentMapRace.lean`](../CsdLean4/RecordLayer/MomentMapRace.lean). For a unit `ψ` the
fibre-partition rate `bornRate ψ i = ‖ψ i‖²` **is** the `i`-th Fubini–Study torus moment-map
coordinate `momentMap([ψ])ᵢ` (`bornRate_eq_momentMap`, via corpus `LF4/MomentMap.momentMap_mk`) —
hence `= ‖⟨eᵢ,ψ⟩‖²`, the `FiniteQMClosure.born_frequency` target (`bornRate_eq_inner_sq`). So the
race rates are the Kähler moment map, read off the context rather than injected (that the moment map
is the forced *choice* of rate field is a posit — `specs/POSITS.md` Posit 1). The residual is sharpened to one
statement: `DeIsolationInteraction` (a measurable pointer whose basins carry the moment-map rates)
⟹ Born (`DeIsolationInteraction.born`); the open part is realising it from a Hamiltonian `H_int(M)`,
i.e. feature (A) (the exponential first-passage from a mixing flow) tied to these rates. Kinematics
done, dynamics open.

## 4. Lean status

- **The fibre-partition factor — LANDED 2026-07-25:**
  [`RecordLayer/BornFibrePartition.lean`](../CsdLean4/RecordLayer/BornFibrePartition.lean). The
  fibre `F = ℝ` is carved into cumulative (CDF) cells `cdfCell r i = [∑_{j<i}rⱼ, ∑_{j≤i}rⱼ)`
  with **`volume (cdfCell r i) = ENNReal.ofReal (rᵢ)`** (`volume_cdfCell`), the cells are
  **pairwise disjoint** for `r ≥ 0` (`cdfCell_pairwiseDisjoint`, via
  `loSum_add_le_loSum` + `Set.Ico_disjoint_Ico`) — a genuine partition. Fed the **Born rates**
  `rᵢ = ‖ψ i‖² = |⟨eᵢ,ψ⟩|²` (`bornRate`, `sum_bornRate_unit`), the fibre measure of outcome `i`
  is the Born weight (`volume_bornCell`), and for a unit state the cells cover a set of measure
  **exactly `1`** (`volume_iUnion_bornCell_unit`, via `measure_iUnion`). Foundational-triple, no
  `sorry`; pinned in `Tests/AxiomAudit.lean`; exported from `CsdLean4.lean`. This discharges the
  **measure content** of the record layer's fibre-partition factor — the "(A) mechanism" of the
  §3c decomposition. What remains open is *not* this factor but the **dynamical realisation**
  (§3c / step 2b′): a de-isolation flow whose basins reproduce `cdfCell (moment map)`.
- **The outcome distribution + the flow ⟹ Born bridge — LANDED 2026-07-25 (step 2b′, partial):**
  [`RecordLayer/DeIsolationFlow.lean`](../CsdLean4/RecordLayer/DeIsolationFlow.lean). On the canonical
  **fibre typicality measure** `fibreTypicality = vol|[0,1)` (a probability measure,
  `instIsProbabilityMeasure`): the Born cell `i` has fibre typicality **exactly `‖ψ i‖²`**
  (`fibreTypicality_bornCell` = the outcome probability of `i`); the cells **cover the fibre up to a
  null set** (`fibreTypicality_uncovered` = the de-isolation pointer is a.e. defined — no
  positive-typicality "no outcome" set); and the **abstract bridge** `map_pointer_apply` proves
  *any* measurable pointer `p` whose basins carry the Born cell measures pushes `fibreTypicality`
  forward to the Born distribution (`(fibreTypicality.map p) {i} = ‖ψ i‖²`). This is the
  **flow-independent** content of 2b′ — Born as a *typicality volume of a basin*, not injected noise.
  **The wall that remains** is exactly `map_pointer_apply`'s `hbasin` hypothesis made physical:
  exhibit a pointer `p` generated by a de-isolation Hamiltonian `H_int(M)`
  (`p = readout ∘ flow(H_int(M))`) whose basins are `cdfCell (moment map)`. Foundational-triple, no
  `sorry`; pinned; exported.
- **★ Qubit identity (§2) — COMPLETE END-TO-END 2026-07-26:** the full **qubit context-fixed Born
  rule** is proven, foundational-triple (`[propext, Classical.choice, Quot.sound]`), no `sorry`, no
  extra axioms, pinned in `Tests/AxiomAudit.lean`, `check-claims.sh` passing. Headline
  [`LF4/QubitBorn.lean`](../CsdLean4/LF4/QubitBorn.lean) `qubitBorn`:
  `∫ ½(1 + rsign(2·blochProj n − 1))·4(2·blochProj ψ − 1)₊ dμ_FS = |⟨n|ψ⟩|²` — the CSD spread density
  from prep `ψ`, weighted by the **context-fixed** hemisphere indicator `H₊(n)` (function of the
  measurement axis `n` alone), integrated against the ontic Fubini–Study typicality measure, **equals
  the Born weight**. The 7-module chain (all foundational-triple, all pinned):
  1. [`LF4/HatBox.lean`](../CsdLean4/LF4/HatBox.lean) — Archimedes hat-box `∫|2·momentMap − 1| = ½`
     (`hatBox_moment`) + density normalisation, via `fs_moment_pushforward_uniform` + `∫_{[0,1]}|2t−1| = ½`.
  2. [`LF4/QubitReflection.lean`](../CsdLean4/LF4/QubitReflection.lean) — the reflection identity
     `‖⟨ψ,φ⟩‖² + ‖⟨ψ,R_nφ⟩‖² = 2cu + 2(1−c)(1−u)` (`reflect_sq_add`), pure `ℂ²` linear algebra.
  3. [`LF4/BlochProjection.lean`](../CsdLean4/LF4/BlochProjection.lean) — the general-axis Born weight
     `blochProj a p = |⟨a,rep p⟩|²/‖rep p‖²` + `U(2)`-equivariance + measurability.
  4. [`LF4/AxisBridge.lean`](../CsdLean4/LF4/AxisBridge.lean) — general-axis bridge
     `∫ f(blochProj n) dμ_FS = ∫ f(momentMap · 0) dμ_FS` → general-axis hat-box `hatBox_axis`.
  5. [`LF4/QubitDipole.lean`](../CsdLean4/LF4/QubitDipole.lean) — `R_n = 2|n⟩⟨n| − I` as a Hermitian
     **unitary** (so `μ_FS`-preserving via the *existing* `U(2)`-invariance — the earlier "anti-unitary"
     worry was unfounded); the **dipole** `∫ rsign(2u−1)(2s−1) dμ_FS = (2c−1)/2`.
  6. [`LF4/QubitCrossTerm.lean`](../CsdLean4/LF4/QubitCrossTerm.lean) — the antipode symmetry via Haar
     **right**-invariance (never needs the anti-unitary map on `Projectivization`); the **cross-term**
     `∫ rsign(2u−1)|2s−1| dμ_FS = 0`.
  7. [`LF4/QubitBorn.lean`](../CsdLean4/LF4/QubitBorn.lean) — assembles `0 + ½ + (2c−1)/2 + 0 = c`.

  **A7-faithfulness for the qubit is discharged:** the epistemic partition `{H±(n)}` is provably
  context-fixed (prep-independent) and the Born rule is *derived* from the ontic `μ_FS` volume, not
  postulated. Next natural target: the general-`N` context-fixed partition (the `blochProj`/bridge
  foundation is already `N`-agnostic; what remains `N`-specific is the `CP¹ = S²` reflection geometry).
- **The record — LANDED 2026-07-25 (step 3):**
  [`RecordLayer/FibreRecord.lean`](../CsdLean4/RecordLayer/FibreRecord.lean). The record-layer readout
  as a first-class postulate-P5 `RecordSemantics` on `Σ = ℝ` (reusing `RecordedFact.lean`):
  a **context** is a nonnegative rate vector `FibreContext`; the **record event** of "context `c`
  recorded outcome `i`" is `cdfCell c.rate i` (`fibreRecordSemantics`), measurable and **exclusive**
  within a context (distinct outcomes disjoint, from `cdfCell_pairwiseDisjoint`); the **ontic
  selection** `fibreOutcome` *is* the record (`fibreOutcome_eq_record`); the **compatible region** of
  one record is that cell (`compatibleSet_fibre_single` — isolation = conditioning on the outcome
  cell, the P6 story); and **Born meets the record** — the fibre typicality of the Born-context
  record event is exactly `‖ψ i‖²` (`fibreTypicality_bornRecord`). Foundational-triple, no `sorry`;
  pinned; exported. This is the intended replacement for the prep-indexed `vnPointerOutcome` readout.
- **The record-layer capstone bundle — LANDED 2026-07-25 (step 5):**
  [`RecordLayer/RecordLayerClosure.lean`](../CsdLean4/RecordLayer/RecordLayerClosure.lean). The analog
  of `FiniteQMClosure`: one `Prop` bundle `RecordLayerClosure`, discharged by `recordLayerClosure`
  for every unit `ψ`, collecting the proved record-layer facts — `exclusive` (P5),
  `selection_is_record`, `isolation_is_conditioning` (P6), `born_typicality` (fibre typicality of the
  record event `= ‖ψ i‖²`), `ae_total`. The **certified successor** to `vnPointerOutcome`: outcome
  probabilities are measurement-noncontextual. `FiniteQMClosure`'s MD-1 docstring now points at it.
  Foundational-triple, no `sorry`; pinned; exported. **Open:** migrating `FiniteQMClosure`'s *proved*
  fields off the `bornRegion`/`vnPointerOutcome` product-model engine onto this readout is
  research-scale (the born-frequency/records machinery redone on the fibre model), gated on step 2b′.
- **The rates are the Kähler moment map — LANDED 2026-07-25 (step 2b′ feature B):**
  [`RecordLayer/MomentMapRace.lean`](../CsdLean4/RecordLayer/MomentMapRace.lean). `bornRate_eq_momentMap`
  — for a unit `ψ` the fibre-partition rate `‖ψ i‖²` **is** the `i`-th Fubini–Study torus moment-map
  coordinate at `[ψ]` (corpus `LF4/MomentMap.momentMap_mk`) — read off the context, not injected; the
  choice of that rate field is a posit (`specs/POSITS.md` Posit 1). `bornRate_eq_inner_sq` — hence `= ‖⟨eᵢ,ψ⟩‖²`, the `FiniteQMClosure.born_frequency` target.
  `fibreTypicality_bornCell_eq_momentMap` — the record-layer Born rule in moment-map terms.
  `DeIsolationInteraction` — the sharpened residual: a measurable pointer whose basins carry the
  moment-map rates ⟹ Born (`.born`). Foundational-triple, no `sorry`; pinned; exported. **Open (the
  wall):** realise a `DeIsolationInteraction` from a physical Hamiltonian `H_int(M)` (feature A — the
  exponential first-passage of a mixing de-isolation flow). Kinematics grounded; the dynamics is open.
- **The measurement architecture in one object — LANDED 2026-07-25:**
  [`RecordLayer/Measurement.lean`](../CsdLean4/RecordLayer/Measurement.lean). `Measurement` = a
  **context** (the measurement type — fixes the basins, hence the probabilities) awaiting an
  **unknown microstate** `ξ`. `outcome_eq_some_iff` (the microstate selects the basin it occupies);
  `record_of_mem_basin` (the combined result *is* the record `⟨context, outcome, time⟩`);
  `bornMeasurement_prob` (the basins set the probabilities `= ‖ψ i‖²`) and
  `bornMeasurement_prob_momentMap` (`=` the Kähler moment map — read off the context, not
  injected; the choice is a posit, `specs/POSITS.md` Posit 1);
  `bornMeasurement_ae_total` (a.e. microstate yields a record). The whole record layer as one
  measurement event. Foundational-triple, no `sorry`; pinned; exported. Assembles the proven pieces —
  the physical flow `H_int(M)` behind the basins stays open (feature A).
- **The Born rule as LLN over the unknown microstate — LANDED 2026-07-25:**
  `Measurement.bornMeasurement_frequency` (in the file above). The whole probabilistic content, and
  *nothing special*: i.i.d. typical microstates (law `fibreTypicality`) give outcome-`i` frequency
  → the basin measure `‖ψ i‖²` = the moment map, by the strong law (`LF1.freq_tendsto_of_iid`).
  Randomness = ignorance of the initial condition. ⚠️ **Corrected 2026-07-28:** this dissolves only
  the *statistical* half of "feature A" — no extra probabilistic postulate is needed **once the
  basins are given**. It does **not** dissolve the dynamical half: the basins themselves enter as
  the hypothesis field `DeIsolationInteraction.basin_rate`, and constructing an `H_int` that
  generates them is open (`DeIsolationFlow.lean` "the open research obligation"). The earlier claim
  that there is "no separate flow to derive" was wrong. Foundational-triple.
- **The record layer on the ACTUAL projective Σ (migration) — LANDED 2026-07-25:**
  [`RecordLayer/ProjectiveRecord.lean`](../CsdLean4/RecordLayer/ProjectiveRecord.lean). No longer a
  fibre toy — the record layer instantiated on the corpus's real model `Σ = CPN(M+1)` with its own
  `bornRegion` (events), `bornOutcome` (outcome map), and `fubiniStudyMeasure`: `projRecordSemantics`
  (P5 `RecordSemantics`, measurable + exclusive via `bornRegion_measurable_uncond` /
  `bornRegion_pairwiseDisjoint`), `bornOutcome_eq_record` (the corpus outcome map *is* the record),
  `compatibleSet_proj_single` (isolation = conditioning on the region), `fubiniStudy_projRecord`
  (FS typicality of the record event `= ‖⟨eᵢ,ψ⟩‖²`), and `projRecord_frequency` (**Born = LLN over the
  unknown microstate on the real Σ** — the exact `FiniteQMClosure.born_frequency` conclusion, carried
  by the record semantics instead of `vnPointerOutcome`). `FiniteQMClosure`'s MD-1 docstring points at
  it. Only field re-plumbing (mechanical, no new theorem) is left. Foundational-triple, no `sorry`.
- **The base×fibre ontic space Σ — LANDED 2026-07-25:**
  [`RecordLayer/FibredSigma.lean`](../CsdLean4/RecordLayer/FibredSigma.lean). The ontic space assembled
  as a product `Σ = base × fibre = CPN n × ℝ`, realising the epistemic/ontic split literally: the
  **base** `CPN n` is the *epistemic* projective point, pinned to `[ψ]` for a sharp prep
  (`baseProj_sharpTypicality`: `π_* (δ_{[ψ]} ⊗ fibreTypicality) = δ_{[ψ]}`); the **fibre** `ℝ` is the
  *ontic* record coordinate carrying the Born partition. The sharp typicality
  `δ_{[ψ]} ⊗ fibreTypicality` gives Born as the fibre event's typicality
  (`sharpTypicality_fibredEvent = ‖ψ i‖²`, `sharpTypicality_fibredEvent_momentMap = ` the moment map).
  Ties `FibreRecord` to the projective base: ψ-dependence in the (epistemic) base, context-fixed
  partition in the (ontic) fibre — Papers C/D epistemic-base/ontic-fibre split made literal.
  Foundational-triple, no `sorry`.
- **The record layer on the closure's actual product Σ — LANDED 2026-07-25:**
  [`RecordLayer/KSigmaRecord.lean`](../CsdLean4/RecordLayer/KSigmaRecord.lean). The record layer lifted to
  `Σ = KSigma(M+1) = CPN × T²`, the exact space `FiniteQMClosure` lives on: `kSigmaRecordSemantics`
  (P5 `RecordSemantics`, events = `bornRegion` lifted through `π = Prod.fst`), and — the key wire-in —
  `born_frequency_region_eq_record`: the region `FiniteQMClosure.born_frequency` lands in
  (`π⁻¹'bornRegion ψ i`) is **definitionally** the record-layer event. So the pinned closure's Born
  frequencies already *are* record-layer frequencies; the literal field rewrite is unnecessary, not
  merely deferred. Foundational-triple, no `sorry`.
- **Arbitrary observable (general basis) — LANDED 2026-07-25:**
  [`RecordLayer/BasisMeasurement.lean`](../CsdLean4/RecordLayer/BasisMeasurement.lean). The record layer
  for any orthonormal basis `b`: `bornRateBasis_eq_inner_sq` (outcome probability `= ‖⟨bᵢ,ψ⟩‖²`),
  `sum_bornRateBasis_unit`, `bornMeasurementBasis_prob`. Change of basis via the isometry `b.repr`.
  Foundational-triple, no `sorry`.
- **Two-time Lüders on one arena (Q25) — LANDED 2026-08-21:**
  [`RecordLayer/TwoTimeLuders.lean`](../CsdLean4/RecordLayer/TwoTimeLuders.lean)
  (+ `swap_sector_born_ctx` in `SwapClosure.lean`; `specs/two-time-luders-scoping.md`). The
  post-outcome fate of the other `Ω_j`, composed: the swap arena extended with a fresh second
  apparatus, the first record persisting **structurally** through the second measurement, and the
  joint two-record law ★★ `two_time_born`
  `P(record i at t₁ ∧ record j at t₂) = momentMap p i · c₂.rate [eᵢ] j` for any second context —
  with ★ `two_time_repeat` (von Neumann repeatability composed) and ★ `two_time_other_fate` (the
  conditioned re-partition: the repeated context's other regions are null, a fresh context sees
  the collapsed weights). Foundational-triple, pinned. Gated residue: the clock-glued two-epoch
  protocol and the entangled/composite instantiation (Q27's mixed tier).
- **Corpus today:** `bornRegion ψ` (prep-indexed, state-shaped) + `vnPointerOutcome`
  (prep-indexed) — the LF5 readout. `FibreRecord` supplies the record-layer replacement; retiring
  `vnPointerOutcome` at the `FiniteQMClosure` wiring is staging step 5 (open).

## 5. Staging

| Step | What | Risk |
|---|---|---|
| ~~1 (Phase 1 — decisive)~~ | **DONE 2026-07-25 → Outcome B** (§3): base-only fails at N=3 for FS-Voronoi (density forced negative; qubit control validates). Fibre needed. | — |
| 1b (optional) | Quick check: does a *non-Voronoi* context-fixed region family rescue base-only? (bound the caveat before committing to the fibre) | low |
| 2b (existence) | **NUMERICALLY VERIFIED 2026-07-25 → §3b, not formalized.** A fibre model reproduces Born at N≥3 (Gumbel race; checked in `scripts/experiments/record_layer_fibre_gumbel.py`, no Lean theorem). Suggestive of where contextuality can live; it does **not** settle the architecture, and the Gumbel noise is injected rather than CSD-native. *(This row read "DONE … Architecture settled"; corrected 2026-07-28.)* | **open** |
| 2b′ (flow-independent half) | **DONE 2026-07-25 → §4:** `RecordLayer/DeIsolationFlow.lean` — canonical fibre typicality `fibreTypicality=vol\|[0,1)`; outcome prob = Born (`fibreTypicality_bornCell`); pointer a.e. defined (`fibreTypicality_uncovered`); **flow ⟹ Born bridge** `map_pointer_apply` (any pointer with Born basin measures → Born distribution). Born as a typicality volume of a basin. | — |
| 2b′ feature (B) rates=moment map | **DONE 2026-07-25 → §3c/§4:** `RecordLayer/MomentMapRace.lean` — `bornRate_eq_momentMap` (rate ‖ψ i‖² IS the torus moment-map coordinate; the choice of rate field is a posit, `specs/POSITS.md` Posit 1), `bornRate_eq_inner_sq` (= corpus Born weight), `DeIsolationInteraction` (moment-map basins ⟹ Born). Feature (2) grounded. | — |
| 2b′ feature (A) — "the wall" | **STATISTICAL half done; DYNAMICAL half OPEN.** ⚠️ This row previously read "DISSOLVED — not a research problem"; that was wrong and is retracted (2026-07-28). **Done:** once the basins are given, no extra probabilistic postulate is needed — each run is deterministic given its microstate, the microstate is typical (`fibreTypicality`), so the outcome frequency → the basin measure `‖ψ i‖²` = the moment map (`Measurement.bornMeasurement_frequency`, via `LF1.freq_tendsto_of_iid`). **Open:** the basins are *assumed*, not derived — `DeIsolationInteraction.basin_rate` is a hypothesis field, and no interaction Hamiltonian `H_int(M)` generating `cdfCell (moment map)` is constructed. Paper D additionally wants system–apparatus–environment coupling, interaction-generated outcome regions, stable macroscopic correlations, and persistence of the record: none of that is formalized. `DeIsolationFlow.lean` states the obligation correctly; this table did not. | **open** |
| ~~fibre-partition factor~~ | **DONE 2026-07-25 → §4:** `RecordLayer/BornFibrePartition.lean` — CDF cells, `volume_cdfCell = rᵢ`, pairwise-disjoint, Born rates → `volume_bornCell`, unit-state total measure `= 1`. Foundational-triple, pinned. The "(A) mechanism" of §3c. | — |
| ~~3 (the record)~~ | **DONE 2026-07-25 → §4:** `RecordLayer/FibreRecord.lean` — the readout as a first-class P5 `RecordSemantics` on `Σ=ℝ`: record event = `cdfCell c.rate i` (measurable + exclusive via `cdfCell_pairwiseDisjoint`); `fibreOutcome_eq_record` (selection = record); `compatibleSet_fibre_single` (isolation = conditioning on the cell); `fibreTypicality_bornRecord` (typicality of recording `i` = `‖ψ i‖²`). Replaces the prep-indexed `vnPointerOutcome` readout. | — |
| 4 | The context-fixed regions `{Ωᵢ(M)}` def + μ_FS-null boundaries (Voronoi) | low |
| 5 (successor bundle) | **DONE 2026-07-25 → §4:** `RecordLayer/RecordLayerClosure.lean` — the record-layer capstone `recordLayerClosure` (analog of `FiniteQMClosure`): exclusive, selection=record, isolation=conditioning, `born_typicality` (=‖ψ i‖²), `ae_total`. The certified successor to `vnPointerOutcome`; `FiniteQMClosure` docstring updated to point at it. | — |
| 5 (migration onto the real Σ) | **DONE 2026-07-25 → §4:** `RecordLayer/ProjectiveRecord.lean` — the record layer instantiated on the corpus's ACTUAL model `Σ = CPN(M+1)`, events = the corpus's own `bornRegion`, outcome map = `bornOutcome`, measure = `fubiniStudyMeasure`. `projRecordSemantics` (P5, measurable+exclusive), `bornOutcome_eq_record`, `fubiniStudy_projRecord` (FS typicality = `‖⟨eᵢ,ψ⟩‖²`), `projRecord_frequency` (Born = LLN over the unknown microstate on the real Σ = the `born_frequency` conclusion, carried by the record semantics). Not a parallel toy. | — |
| ~~5 (field re-plumbing)~~ | **UNNECESSARY 2026-07-25 → §4:** `RecordLayer/KSigmaRecord.lean` `born_frequency_region_eq_record` proves the closure's Born-frequency region `π⁻¹'bornRegion` is *definitionally* the record-layer event `kSigmaRecordSemantics` on the actual Σ=KSigma. So the closure's Born frequencies already ARE record-layer frequencies — no rewrite of the pinned field needed (and the field's coarse `vnPointerOutcome` is a block-sum of these events, `vnPointerOutcome_preimage_some`). | — |
| ~~arbitrary observable~~ | **DONE 2026-07-25 → §4:** `RecordLayer/BasisMeasurement.lean` — the record layer for any orthonormal basis `b`: `bornRateBasis_eq_inner_sq` (outcome prob `= ‖⟨bᵢ,ψ⟩‖²`), `sum_bornRateBasis_unit`, `bornMeasurementBasis_prob`. Change of basis via the isometry `b.repr`. | — |

## 6. References

[`CSD-CHARTER.md`](CSD-CHARTER.md) (the north star); [`reconstruction-status.md`](reconstruction-status.md)
§7 (the record layer, now built); [`BACKLOG.md`](BACKLOG.md) (record-layer row);
[`future-work.md`](future-work.md) (record-layer row). Papers: Paper C **A7** (epistemic
outcome regions {Ωᵢ(M)} ⊂ CPⁿ⁻¹), Paper A (typicality), Paper B (μ_FS unique by SU(n)),
Gleason (N≥3 impossibility) — `.tmp_extract/PaperC.txt`, `.tmp_extract/PaperD.txt`.
Corpus: `LF1/Outcomes.lean` (`OutcomeRegion`, `weight = μL(Ω₀ ∩ Φ⁻¹Ω)/μL(Ω₀)`),
`LF4/BornFrequencyN.lean` (`bornRegion`, the prep-indexed engine),
`LF5/PointerOutcome.lean` (`vnPointerOutcome`), `SigmaLayer/RecordedFact.lean`.

## Measurement, stated structurally (2026-08-26, author-approved framing)

Records are prior. The apparatus **is** a record history; isolation is conditioning Σ on
compatibility with that history (P6, `HistoryPreparation`); de-isolation extends the history with a
new fact (`appendFact`, `compatibleSet (h ++ [r]) = compatibleSet h ∩ event r`). Isolation is the
manufactured special condition, de-isolation the default — so there is no bootstrap problem about a
first record.

A measurement is reading the actual location of a point. Its probability is volume, and the volume
is epistemic — ignorance of which point. Two inputs fix the reading: **how the apparatus is
constructed**, which fixes the context field `c`, and **the unknowable microstate of Σ at the moment
of de-isolation**, which fixes where in the field the point sits.
`globalBasin c i = {x | x.2.1 ∈ circleCell (c.rate x.1) i}` is exactly this.

**Two partitions, kept apart.** The Ω-regions on the projective base are epistemic — a calculation
space (A7); nothing sculpts them, and they match volume because `μ_FS` is forced by symmetry and the
weights are the moment map. The fibre cells sit on the ontic fibre and the selection is ontic, though
the particular cell family is one realisation of an interface, so the cell *shapes* are bookkeeping.

**What this dissolves.** Not the Born weights — those are geometry, and `map_pointer_apply` makes
them flow-independent. It dissolves the demand for a carving Hamiltonian: if isolation is maintained
conditioning, de-isolation is its cessation, and nothing needs to carve. ⚠️ On that reading
`DeIsolationFlow.lean`'s "exhibit `p = readout ∘ flow(H_int(M))`" asks for the wrong object.
**FLAGGED, NOT DECIDED** — this obligation has been mis-stated repeatedly and needs `csd-foundations`
sign-off before the Lean-side docstring is amended.

**What remains.** The physical origin of the context field: why *this* apparatus has *that* rate
field. Pointer-basis / einselection territory; the corpus's general-`N` einselection is currently
definitional with the ontic origin gated to the entangled tier. ✅ Exclusivity is **not** in the
residue — `globalRecordSemantics.exclusive` is *derived* from `globalBasin_pairwiseDisjoint`.
