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

## 3. The N≥3 consequence — Gleason forces the fibre (why "constrain Σ" is now necessary)

Route (i) is a *non-negative density on `ℂℙⁿ⁻¹` reproducing Born over context-fixed regions
for all contexts*. For **N ≥ 3, Gleason's theorem forbids it** — no such density exists (it
would be a non-contextual hidden-variable model in dim ≥ 3). The qubit works *only because*
dim 2 escapes Gleason/KS.

**Consequence:** a fixed epistemic density on `ℂℙⁿ⁻¹` cannot carry Born past N=2. The
contextuality must live *below* ℂℙ — in the **fibre of the many-to-one π**. This is why Σ
must be genuinely many-to-one over ℂℙ (Paper C A3), and it turns *constraining Σ's fibre*
from optional into **necessary**: the fibre is not a spectator (contra the corpus's ad-hoc
`T²`) — it supplies exactly the contextuality Gleason says ℂℙ cannot. The record — which
ontic basin `π⁻¹Ωᵢ(M) ⊂ Σ` the trajectory realizes — depends on `ω` (fibre included), not on
[ψ] alone, and *that* is how KS is evaded. **MD-1 and "constrain Σ" fuse here.**

The N≥3 problem, sharply posed:
> Design the Σ-fibre and the prepared region `Ω₀(ψ) ⊂ Σ` so that
> `μL(Ω₀(ψ) ∩ π⁻¹Ωᵢ(M)) / μL(Ω₀(ψ)) = |⟨eᵢ|ψ⟩|²` for **all** contexts M — the fibre
> supplying the context-dependence Gleason forbids on ℂℙ alone.

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
| 1 | `MeasurementContext → {Ωᵢ(M)}` context-fixed **epistemic** partition on ℂℙ (Voronoi / moment-polytope), μ_FS-null boundaries | low |
| 2 | **Qubit crux (§2)** — analytic DONE; Lean = sphere-measure infra (reflection-invariance of `toSphere` + Archimedes `∫|λ₃|=½`) | med (infra) |
| 3 | The record as a context-fixed `RecordedFact` + ontic selection `ω ↦ i` (reuse `RecordSemantics`) | low |
| 4 | **N≥3 fibre construction (§3)** — the fibre supplies contextuality; `Ω₀(ψ)` + Born for all contexts | **high — the research core** |
| 5 | Wire into `FiniteQMClosure`; retire the prep-indexed readout | med |

## 6. References

[`CSD-CHARTER.md`](CSD-CHARTER.md) (the north star); [`reconstruction-status.md`](reconstruction-status.md)
§7 (the record layer as near frontier); [`BACKLOG.md`](BACKLOG.md) (record-layer row);
[`future-work.md`](future-work.md) (record-layer row). Papers: Paper C **A7** (epistemic
outcome regions {Ωᵢ(M)} ⊂ CPⁿ⁻¹), Paper A (typicality), Paper B (μ_FS unique by SU(n)),
Gleason (N≥3 impossibility) — `.tmp_extract/PaperC.txt`, `.tmp_extract/PaperD.txt`.
Corpus: `LF1/Outcomes.lean` (`OutcomeRegion`, `weight = μL(Ω₀ ∩ Φ⁻¹Ω)/μL(Ω₀)`),
`LF4/BornFrequencyN.lean` (`bornRegion`, the prep-indexed engine),
`LF5/PointerOutcome.lean` (`vnPointerOutcome`), `SigmaLayer/RecordedFact.lean`.
