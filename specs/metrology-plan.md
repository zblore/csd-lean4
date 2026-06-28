# Quantum sensing / metrology in CSD — program plan

**Status: planned (2026-06-27).** Validation target: shift from static-state validation
(Bell/GHZ) to **parameter estimation** — how cleanly an external classical parameter
`θ` (field, gradient, time interval) maps onto the ontic trajectory on `Σ` and onto the
resulting carving volume ratios. Four areas, ordered by infrastructure readiness below.

## The four areas

### A1 — Ramsey interferometry as a parameter-driven volume-preserving flow (DONE 2026-06-28)
**`Empirical/Metrology/Ramsey.lean`, auditor-SOUND.** `ramseyPhaseFlow` (the `diag(1,e^{iφ})`
free-precession flow on `Σ = ℂℙ¹`, reusing `LF4.obsFlow`) with `ramseyPhaseFlow_measurePreserving`
(the first parameter-driven FS-measure-preserving metrology flow) and `ramseyPhaseFlow_ne_id`
(`Φ ≠ id` at `φ = π`); `ramseyVec` proved equal to the genuine circuit `qmH · diag(1,e^{iφ}) · qmH · |0⟩`
(`ramseyVec_eq_circuit`, machine-checked, not asserted); `ramsey_fringe_volume` lands the `|0⟩`-outcome
FS volume on the fringe `cos²(φ/2)` via `qubit_born_frequency_convergence_uncond` (Gleason-free), with
extremes `r(0)=1`, `r(π)=0` and the sensitivity `dP/dφ = −sin(φ)/2` (`ramsey_fringe_hasDerivAt`, the QFI
precursor, maximal at quadrature `φ=π/2`). 7 pins. Honest: single-qubit; Born = FS volume imported; the
flow runs on the projective probe, concrete `SectorData` still `Φ = id`.

(original scope:)
Mechanise the Ramsey sequence: `[π/2] → [phase φ(θ)] → [π/2] → carve`, with the phase
accumulation a deterministic measure-preserving flow on `Σ` driven by `θ`, and prove the
end-of-sequence multi-region carving yields the FS volume ratio reproducing the standard
fringe `∝ cos²(φ/2)`.
- **Infrastructure: READY.** `Empirical/CSD/MalusVolume.lean` (`csd_malus_law`) already
  proves `cos²(θ/2)` as a genuine FS volume of the moment-sublevel region, via
  `context_born_frequency_volume` at `M=1`. The Ramsey fringe *is* this reading with `φ`
  the accumulated phase. New content: the protocol framing + the phase as a `θ`-driven
  flow + (optionally) the sensitivity `dP/dφ` as the fringe slope.
- **Validates:** CSD handles dynamic time-dependent phase tracking as cleanly as static
  entanglement. Low-risk foundational sensing protocol.

### A2 — Quantum Fisher Information = Fubini-Study metric
Formalize `F_Q(θ) = g_θθ` (the FS metric tensor along the trajectory `γ(θ)`), turning the
Quantum Cramér-Rao bound `Var(θ̂) ≥ 1/F_Q` into a statement about the differential geometry
of `Σ = ℂℙ^{N-1}`.
- **Infrastructure: GAP.** The corpus has `fubiniStudyMeasure` (a measure) and the moment
  map, but **no FS metric tensor** as a Riemannian/Kähler metric object, and Mathlib's
  manifold/metric API on `ℂℙ^{N-1}` is thin. This is a real new-infrastructure tranche:
  define the FS metric (e.g. via `g = ⟨∂ψ|∂ψ⟩ − |⟨ψ|∂ψ⟩|²` on the normalized vector, the
  pullback to the trajectory), then prove the QFI identity. Larger and riskier than A1.
- **Validates:** QFI as a literal property of the ontic manifold's geometry, not an
  operational bound on measurement operators.

### A3 — Heisenberg limit (1/N scaling) via dilated manifolds
Prove that `N`-particle correlation makes the trajectory on the dilated manifold
`Σ' = ℂℙ^{2^N−1}` hyper-sensitive to `θ`: the carved-region boundaries shift so an
infinitesimal `dθ` produces a macroscopic FS-volume-ratio change, giving `1/N` scaling
(vs the SQL `1/√N`).
- **Infrastructure: PARTIAL.** The dilated manifold `Σ'` and its FS-volume Born readings
  exist (the POVM Naimark dilation `LF4/POVM*`, LF5 `ℂℙ^{N·N−1}`). But the `1/N`-scaling
  argument needs A2's metric/sensitivity machinery (volume-ratio volatility vs `θ`). So A3
  depends on A2. The geometric reading (entanglement/squeezing = guiding the ontic point
  through tightly-constrained high-curvature regions, maximizing volume-ratio volatility)
  is the payoff.
- **Validates:** a purely geometric account of quantum enhancement.

### A4 — Decoherence as open symplectic drift
Formalize T1/T2 decoherence (Lindblad `dρ/dt`) at the ontic layer (no `ρ`) as an
unmonitored-environment interaction: a conservative flow on the *joint* `Σ` that, coarse-
grained over the environment, mimics diffusion/drift across the constraint surfaces, and
recover the Lindblad sensitivity degradation.
- **Infrastructure: GAP + tied to D1.** Requires open-system / partial-trace dynamics on
  `Σ` and a coarse-graining-to-diffusion argument. This is the entangled/non-local
  de-isolation tier (D1) wearing a metrology hat — the deepest open frontier. Hardest;
  do last.
- **Validates:** open quantum systems as deterministic geometric drift, not intrinsic
  stochasticity.

## Recommended order (by readiness, not by glamour)
**A1 (Ramsey) → A2 (QFI = FS metric) → A3 (Heisenberg, needs A2) → A4 (decoherence, = D1).**

A1 is nearly free (reuses `MalusVolume`/`context_born_frequency_volume`); it lands the
foundational sensing protocol and the dynamic-phase-tracking validation with low risk.
A2 is the first genuine new infrastructure (the FS metric tensor) and unblocks A3. A4 is
gated on the D1 entangled/open-system frontier and is the deepest.

## Honest posture (carried into each file)
Same as the rest of the volume series: these are **realisations** of the metrology numbers
as FS typicality volumes on `Σ` (Born = FS volume *derived* one layer down in the DH
cluster, imported here), not derivations from first-principles dynamics; the concrete
`SectorData` instances still carry `Φ = id` (A1's phase flow is the first metrology flow,
single-system). The QCRB/Lindblad statements themselves stay at the QM-validity layer
where they are operator/master-equation facts; the CSD increment is the geometric reading.

## Home
`CsdLean4/Empirical/Metrology/` (new), namespace `CSD.Empirical.Metrology`. A1 may also
reuse / sit beside `Empirical/CSD/MalusVolume.lean`.
