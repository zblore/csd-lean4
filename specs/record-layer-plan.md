# Record layer (MD-1) — plan: measurement as context-fixed regions + the ontic record

> **Status: LIVE plan (created 2026-07-25).** The near frontier for *completing the
> reconstruction of QM from Σ + Ω* (see [`CSD-CHARTER.md`](CSD-CHARTER.md)). The qubit
> crux is **solved analytically** (below); its Lean formalization is a scoped
> sphere-measure infra task; the N≥3 case is the genuine research core. Open-item row:
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

## 2. The qubit crux — SOLVED (analytically; route (i), epistemic density)

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
- **The exponential fibre measure is FORCED.** For iid linear clocks, first-to-fire `=bᵢ` holds
  **iff** the waiting times are exponential (memoryless/Poisson). So the fibre typicality is pinned
  by the first-passage structure. This is exactly the **quantum-jump / continuous-measurement** form
  (jumps at exponential times, rates `∝|amplitude|²`) — a developed formalism to anchor to.

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

## 4. Lean status

- **Qubit identity (§2):** an `S²` integral. Formalization is **Cat-1 sphere-measure
  infra** — Mathlib has `Measure.toSphere` but not (a) rotation/reflection invariance of
  it, (b) angular integration, or (c) Archimedes' hat-box (`∫|λ₃|dμ = ½`). A real focused
  build, not blocked on CSD. Not yet attempted; **no `sorry`/axiom stub landed** (repo rule).
- **The record (§2):** clean — reuse `SigmaLayer/RecordedFact.lean`, `RecordSemantics`,
  `compatibleSet`, `flowedSemantics`; the record event is the context-fixed `π⁻¹Ωᵢ(M)`.
- **Corpus today:** `bornRegion ψ` (prep-indexed, state-shaped) + `vnPointerOutcome`
  (prep-indexed) — to be replaced by context-fixed regions + the ontic record.

## 5. Staging

| Step | What | Risk |
|---|---|---|
| ~~1 (Phase 1 — decisive)~~ | **DONE 2026-07-25 → Outcome B** (§3): base-only fails at N=3 for FS-Voronoi (density forced negative; qubit control validates). Fibre needed. | — |
| 1b (optional) | Quick check: does a *non-Voronoi* context-fixed region family rescue base-only? (bound the caveat before committing to the fibre) | low |
| ~~2b (existence)~~ | **DONE 2026-07-25 → §3b:** the fibre model reproduces Born exactly at N≥3 (Gumbel race; verified, `scripts/experiments/record_layer_fibre_gumbel.py`). Architecture settled: the fibre carries the contextuality. | — |
| **2b′ (the real core)** | **CSD-native fibre model:** a *canonical geometric* fibre `(F,ν)` + a *deterministic de-isolation flow* `Φ_M` whose basins `B_i(M)=Φ_M⁻¹(pointer_i)` ARE the Born partition — Born as a typicality volume of a flow-carved basin, not injected noise. Where typicality + Kähler dynamics enter. | **high — research core** |
| 3 | The record: context-fixed `RecordedFact` + ontic selection `ω ↦ i` (reuse `RecordSemantics`) — independent of A/B | low |
| 4 | The context-fixed regions `{Ωᵢ(M)}` def + μ_FS-null boundaries (Voronoi) | low |
| 5 | Formalize (qutrit) + wire into `FiniteQMClosure`; retire the prep-indexed readout | med |

## 6. References

[`CSD-CHARTER.md`](CSD-CHARTER.md) (the north star); [`reconstruction-status.md`](reconstruction-status.md)
§7 (the record layer as near frontier); [`BACKLOG.md`](BACKLOG.md) (record-layer row);
[`future-work.md`](future-work.md) (record-layer row). Papers: Paper C **A7** (epistemic
outcome regions {Ωᵢ(M)} ⊂ CPⁿ⁻¹), Paper A (typicality), Paper B (μ_FS unique by SU(n)),
Gleason (N≥3 impossibility) — `.tmp_extract/PaperC.txt`, `.tmp_extract/PaperD.txt`.
Corpus: `LF1/Outcomes.lean` (`OutcomeRegion`, `weight = μL(Ω₀ ∩ Φ⁻¹Ω)/μL(Ω₀)`),
`LF4/BornFrequencyN.lean` (`bornRegion`, the prep-indexed engine),
`LF5/PointerOutcome.lean` (`vnPointerOutcome`), `SigmaLayer/RecordedFact.lean`.
