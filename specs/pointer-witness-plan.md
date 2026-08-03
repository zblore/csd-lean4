# Pointer-witness plan — the compact Kähler pointer `ℂℙ^K` (smooth measurement dynamics)

*Created 2026-08-03. Decision record: the author confirmed (2026-08-03) that the
**smooth-Hamiltonian architecture** of Paper C A2 / TN6 is **retained** — the papers stand as
written, and this witness is the formal obligation that must satisfy them. The landed piecewise
witnesses (`ShearWitness`, `SwapWitness`, the join arc) are NOT displaced: they remain the
exact-record horn of the `no_everywhere_correlation` trade-off. This plan builds the smooth
horn. Backlog row: the ★ L item in [`BACKLOG.md`](BACKLOG.md); broader programme:
[`future-work.md`](future-work.md).*

## Why this witness, in one paragraph

The second external review (2026-08-02) established two corrections that jointly fix the
route. **(flux)** Rigid translations on the torus register are symplectic but not globally
Hamiltonian (`ι_Xω = a·dp` is closed-not-exact; `∮dp ≠ 0`), so no witness built on register
*translations* can ever satisfy Paper C A2's smooth-Hamiltonian architecture. **(overread)**
`no_everywhere_correlation` forces an exceptional *non-correlating set*, not discontinuity —
so a continuous propagator that maps seam states to *transition states* outside `⋃Bⱼ` is not
excluded. The repair for both at once: replace the torus **register** with a projective
pointer `ℂℙ^K = ℙ(ℂ^{K+1})` — compact Kähler, `H¹ = 0`, where unitary one-parameter groups
**are** globally Hamiltonian flows (moment map `[ψ] ↦ ⟨ψ, Hψ⟩/‖ψ‖²`) — and replace the
seam-jumping selector readout with a **continuously modulated** coupling whose seam-corridor
images are partial rotations: legitimate transition states of the projective pointer.

## The trade-off, stated honestly up front

`no_everywhere_correlation` (`SigmaLayer/MeasurementConstraints.lean`) makes
{continuity, exact records everywhere, exact Born} jointly unattainable. The corpus will hold
**both horns**:

| Horn | Witness | Exact records/Born | Smooth, globally Hamiltonian |
|---|---|---|---|
| Exact-record | `ShearWitness`/`SwapWitness`/join arc (landed) | yes | no — piecewise rigid symplectic translation (`PiecewiseHamiltonian.lean`, flux correction 2026-08-02) |
| Smooth | `ℂℙ^K` pointer (this plan) | up to `ε`, `ε` arbitrary | yes (at the level formalisable — see Honest scope) |

The `ε`-price is not new mathematics for the corpus: `collapse_accuracy_bound` prices
approximate collapse, and `quantum_effective_shadowing` (A5) is already an `ε·T` tracking
statement. The pointer witness extends that idiom to record creation.

## Arena and dynamics design

- **Arena** `Σ_ptr = ℂℙ^{N-1} × T²_λ × ℂℙ^K` — base, the retained selector fibre (Born cells
  on the first torus coordinate, `torusCell` machinery), and the pointer. Product of compact
  Kähler manifolds, even-dimensional (parity checked: `2(N-1) + 2 + 2K`). Reference measure:
  `μ_FS ⊗ Haar ⊗ μ_FS`. `K = N` for the nondegenerate witness: pointer basis `f₀` (ready),
  `f₁ … f_N` (records).
- **Fixed-outcome rotation.** `hⱼ = |f₀⟩⟨fⱼ| + |fⱼ⟩⟨f₀|` (Hermitian); `exp(-i(π/2)hⱼ)` maps
  `[f₀] ↦ [fⱼ]` projectively. Each is a unitary one-parameter group on `ℂ^{K+1}`, hence a
  globally Hamiltonian flow on `ℂℙ^K` in the standard reading.
- **Continuous selector modulation.** Trapezoidal bump weights `wⱼ(p, θ)` equal to `1` on the
  `ε`-shrunk cell `j` of the context rate at the base point (the `ContextField` /
  `globalBasin` pattern — no `ψ` in the definition), `0` outside the unshrunk cell,
  continuous on the corridors. Coupling `H(p, θ) = Σⱼ wⱼ(p, θ) · hⱼ` — Hermitian for every
  `(p, θ)`, jointly continuous.
- **Propagator.** `Φₜ(p, θ, q) = (p, θ, exp(-i κ(t) (π/2) H(p, θ)) · q)` with `κ` a ramp
  frozen at `1` after `T_M`. Base and selector are conserved coordinates (the
  `readout_arenaIso` persistence pattern); the two-time law is the **group property** of the
  exponential — strictly easier than the swap's eight-case crossing proof.
- **Regions and readout.** `Bⱼ = {q : mⱼ(q) > 1/2}` via the pointer moment map — open,
  pairwise disjoint; ready region an open neighbourhood of `[f₀]` (positive measure, with a
  uniform landing margin by compactness). Corridor states land at partial rotations —
  transition states in `⋃Bⱼ`'s complement, exactly what the corrected no-go reading permits.
- **Born.** Sector `j` contains the shrunk-cell cylinder, so `volume_torusCell` gives sector
  measure in `[rⱼ − O(ε), rⱼ]` with `rⱼ` the context rate — Born up to `ε`, `ε` a parameter
  of the witness, not a hidden constant.

## Reuse map

| Need | Already in the corpus |
|---|---|
| FS measure invariance under the rotation | `fubiniStudyMeasure_smul_invariant` (one line, as in `joinSwap_measurePreserving`) |
| Pointer moment-map regularity | `continuous_momentMap` / `measurable_momentMap` + the `Projectivization` staging (`Mathlib/LinearAlgebra/Projectivization/Topology.lean`) |
| Context-fixed cells at the ontic point | `ContextField`, `globalBasin`, `volume_torusCell` |
| `exp` continuity in `t` and in the generator | `StoneC1`, matrix-exponential continuity (L2Operator norm scope — the Track-A lesson) |
| Protocol interface, persistence, sector accounting | `MeasurementProtocol`, `measure_outcomeSector_eq_of_correlates`, `RecordPersistence` |
| `ε`-statement idiom | `collapse_accuracy_bound`, `quantum_effective_shadowing` |

## Brick ladder (review steps 1–3 refined)

| Brick | Content | Effort |
|---|---|---|
| ~~0~~ | ~~Arena + pointer definitions; `mⱼ` regularity; `Bⱼ` open/disjoint; ready region~~ **DONE 2026-08-03** (`SigmaLayer/PointerArena.lean`, foundational-triple, 5 pins): `Pointer K = ℂℙ^K`, ready/record vertices via `vertexPoint`; `recordRegion`/`readyRegion` open + measurable + pairwise disjoint + positive FS measure (`fubiniStudyMeasure_pos_of_isOpen`); `PointerArena N K = KSigma N × ℂℙ^K`, `pointerLiouville` a probability measure; ★ `arenaReady_pos` — a positive-measure apparatus-ready state exists on this arena (contrast `globalBasin_ae_total`) | ~~S–M~~ S (one pass) |
| ~~1~~ | ~~Fixed-outcome rotation: `hⱼ` Hermitian, unitarity, `[f₀] ↦ [fⱼ]`, FS invariance, `t`-continuity~~ **DONE 2026-08-03** (`SigmaLayer/PointerRotation.lean`, foundational-triple, 6 pins): `pointerH` Hermitian; `pointerRot θ j = 1 + (cosθ−1)•Pⱼ − (i sinθ)•hⱼ` a **continuous one-parameter unitary group** (group law + `rotᴴ = rot(−θ)` unitarity + continuity into the group and through the projective action — the properties `shearEvolve_not_continuous` proves the torus witness lacks); quarter turn `[f₀] ↦ [f_{j+1}]` (`pointerRotU_pi_div_two_ready`); FS invariance one-line. The `exp(−iθhⱼ)` identification stays brick 5 as planned | ~~M~~ S–M (one session) |
| 2a | ~~Generator half: `couplingH w` Hermitian, `couplingU w = exp((π/2)•(−i•couplingH w))` unitary, entrywise continuity in the weights~~ **DONE 2026-08-03** (`SigmaLayer/PointerCoupling.lean`, foundational-triple, 6 pins): the `hⱼ` don't commute, so the propagator is the honest exponential; unitarity via `exp_smul_unitary`; ★ `pointerRot_eq_exp` — **the Hamiltonian-generation identification** (brick 5's single-plane half, pulled forward: the landing theorem reads pure cells through `couplingU_single`), by ODE uniqueness against `eq_exp_of_hasDeriv`; entrywise Lipschitz continuity via the Duhamel bound + the **new staged entry bound** `Matrix.norm_entry_le_l2_opNorm` (`L2OpNormEntry.lean`) — statements kept free of the scoped norm instances | ~~—~~ done |
| ~~2b~~ | ~~Weight field, arena propagator, joint continuity, measure preservation~~ **DONE 2026-08-03** (`SigmaLayer/PointerWeights.lean`, foundational-triple, 5 pins): weights are **circle-intrinsic** trapezoids `clamp((rⱼ/2 − dist(θ₁, mⱼ))/ε)` (no fundamental-domain lift, so joint continuity is a composition — the moving-endpoint problem dissolves); ★ `continuous_pointerEvolve` — **the full arena propagator is continuous** (contrast `shearEvolve_not_continuous`), via open-quotient descent through `id × mk'`; `pointerEvolve_measurePreserving` (skew product); `pointerEvolve_pure` — on shrunk cells the propagator is the brick-1 quarter rotation | ~~M~~ done |
| ~~3~~ | ~~Landing theorem on shrunk cells~~ **DONE 2026-08-03** (`SigmaLayer/PointerLanding.lean`, foundational-triple, 6 pins): midpoint separation `cellMid_dist_ge` (circle norm via `round`, `loSum` ordering) + triangle inequality discharge both `pointerEvolve_pure` hypotheses — no cell-inclusion geometry needed; `momentMap_pointerRot_smul` (`m_{j+1}(U•q) = m₀(q)` exactly) sends ready → record with margin; ★ `pointer_landing`; `volume_shrunkCell_slice` = `rⱼ − 2ε` exactly (the Born seed). *Two-time law + persistence + `MeasurementProtocol` instance moved to brick 4 (protocol packaging).* | ~~M~~ done |
| 4a | ~~Protocol packaging: two-time law, persistence, `MeasurementProtocol` instance, correlation~~ **DONE 2026-08-03** (`SigmaLayer/PointerProtocol.lean`, foundational-triple, 7 pins): `pointerProtocol` with evolve = ramped exponential; two-time law = **exponential group property** (`couplingUAt_mul`); persistence = **freezing** (`pointerProtocol_pointerInvariantOn` discharged outright, `record_persists_on_interval` applies verbatim); correlation = the landing theorem (`pointerProtocol_correlatesOn`); ★ **joint time–state continuity** (`continuous_pointerRampedEvolve`, two-sided Duhamel squeeze + generic open-quotient action descent `continuous_unitaryFamily_smul`) — neither piecewise witness is continuous in either variable | ~~—~~ done |
| ~~4b~~ | ~~`ε`-Born sector sandwich and the smooth-horn closure~~ **DONE 2026-08-03** (`SigmaLayer/PointerBorn.lean`, foundational-triple, 5 pins): `pointerPrep = epistemicMeasure ⊗ FS[\|ready]` (conditioning legitimate by `readyRegion_pos` — **no Dirac calibration posit**); sector measure `= rⱼ − 2ε` exactly; ★ the sandwich `rⱼ − 2ε ≤ μ(sector j) ≤ rⱼ + 2(N−1)ε` (upper bound from disjointness + the other lower bounds alone); ★★ `SmoothWitnessClosure`/`smoothWitnessClosure` — one witness: protocol + joint time–state continuity + Liouville + positive-measure ready + sector-selected record creation + structural persistence + ε-Born, instantiated on the canonical moment-map context | ~~M~~ done |
| 5 | Hamiltonian-generation statement at the formalisable level (explicit Hermitian generator family + the moment-map reading; see Honest scope); Lüders composition with the relocation machinery | L / recorded extension |

Ordering rule (inherited from the `H_int` row): build only the interface needed to *state*
the landing theorem, then prove it — no scaffold with a hypothesis at its heart.

## ⚠️ Honest scope

- **"Globally Hamiltonian" is delivered at the formalisable level**: an explicit continuous
  family of Hermitian generators whose exponential flow *is* the propagator on the pointer
  factor. Mathlib has no symplectic-manifold or moment-map API
  ([`MATHLIB-GAPS.md`](../MATHLIB-GAPS.md)), so the geometric statement "this flow is the
  Hamiltonian flow of the FS moment map" is the standard reading recorded in prose, not a
  Lean theorem. This is the *same* scope boundary A1/A3 carry, and unlike the torus case
  there is no flux obstruction hiding behind it.
- **Exact records and exact Born are not claimed** — the `ε`-corridor is forced by
  `no_everywhere_correlation` and is stated, parameterised, and priced.
- **Lüders on this witness is brick 5, not assumed**; until it lands, collapse remains on
  the piecewise horn (swap/join witnesses), and the closure statement must say so.

## References

Second external review 2026-08-02 (steps 1–3); [`BACKLOG.md`](BACKLOG.md) (the ★ L row and
the `H_int` ledger row); [`reconstruction-status.md`](reconstruction-status.md) §2a (A2);
[`future-work.md`](future-work.md); `SigmaLayer/PiecewiseHamiltonian.lean` (the flux
correction), `SigmaLayer/ShearDiscontinuity.lean` (`shearEvolve_not_continuous`),
`SigmaLayer/MeasurementConstraints.lean` (`no_everywhere_correlation`),
`SigmaLayer/GlobalBasin.lean` (`ContextField`), `SigmaLayer/TorusFibre.lean`
(`volume_torusCell`).
