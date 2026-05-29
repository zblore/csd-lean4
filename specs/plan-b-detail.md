# Plan B — detailed implementation spec

**Goal.** Discharge the axiom `CSD.LF4.fs_moment_pushforward_uniform`:
```
(fun p => momentMap p 0)∗ fubiniStudyMeasure p₀ = (volume : Measure ℝ).restrict (Set.Icc 0 1).
```
Once proved, the unconditional qubit results (`fs_born_volume_ratio_qubit_uncond`,
`qubit_born_frequency_convergence_uncond`) become foundational-triple-only, and
the axiom is retired from `AXIOMS.md §2.3`.

Everything is finite-dimensional (`ℂℙ¹`, `U(2)`). Multi-session build.

## Route (chosen): Gaussian-induced measure + Fubini–Study uniqueness

Two key Mathlib/project tools make this the cleanest route:

- **`Matrix.UnitaryGroup.fubiniStudyMeasure_unique`** (project,
  `Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean:181`, **proved,
  axiom-free**): any `U(N)`-invariant *probability* measure on `ℂℙ^{N-1}` equals
  `fubiniStudyMeasure p₀`.
- **`MeasureTheory.stdGaussian_map`** (Mathlib
  `Probability/Distributions/Gaussian/Multivariate.lean:129`): for a linear
  isometry equiv `f`, `(stdGaussian E).map f = stdGaussian F`. ⟹ `stdGaussian` is
  invariant under every linear isometry, in particular the `U(2)` action on `ℂ²`
  (unitaries are ℝ-linear isometries).

So we identify `fubiniStudyMeasure` with the Gaussian-induced measure on `ℂℙ¹`,
where the moment marginal is the classical `Beta(1,1)` computation.

## Part 1 — `gaussianCP = fubiniStudyMeasure` (B.2; tractable)

Let `H := EuclideanSpace ℂ (Fin 2)`, viewed as a real inner-product space.

- **L1 `gaussianProj`** — the map `H → ℂℙ¹` sending `v ↦ mk ℂ v hv` for `v ≠ 0`
  and a junk value at `0`. Measurable. (Or push the `stdGaussian` restriction to
  `{v ≠ 0}` and use `mk'`; `stdGaussian {0} = 0` so the junk value is irrelevant.)
- **L2 `gaussianCP := (stdGaussian H).map gaussianProj`** — a probability measure
  on `ℂℙ¹` (pushforward of a probability measure).
- **L3 invariance** — `∀ U : U(2), (gaussianCP).map (U • ·) = gaussianCP`. Proof:
  `(U • ·) ∘ gaussianProj = gaussianProj ∘ (U-as-ℝ-isometry)` (mk' equivariance,
  `U • mk v = mk (U v)`); push through `Measure.map_map`; kill the inner map by
  `stdGaussian_map` (the `U` action is a linear isometry equiv of `H`).
- **L4** — `gaussianCP = fubiniStudyMeasure p₀`, by `fubiniStudyMeasure_unique`
  (L2 gives the probability instance, L3 the invariance hypothesis).

**ℝ/ℂ friction (the one setup snag).** `stdGaussian` needs `[InnerProductSpace ℝ H]`.
`H` is a complex IPS; the real structure is `InnerProductSpace.rclikeToReal`,
which is **not** a global instance (diamond risk). Two ways:
  (a) work in `EuclideanSpace ℝ (Fin 4)` with a fixed `ℝ`-linear isometry
      `e : ℝ⁴ ≃ₗᵢ[ℝ] H` and carry `e` through; or
  (b) supply the `rclikeToReal` instance locally and check no diamond bites.
Prefer (a) if (b) causes instance clashes. The `U(2)` action becomes an `O(4)`
action on `ℝ⁴` under `e`; `stdGaussian (ℝ⁴)` is invariant under it.

Part 1 is a committable, foundational-triple increment on its own (identifies
`fubiniStudyMeasure` as the Gaussian-induced measure — reusable).

## Part 2 — the moment marginal is uniform (B.3; the hard gap)

- **L5** — `(fun v : H => ‖v 0‖²/‖v‖²)∗ stdGaussian H = (volume).restrict [0,1]`.
  Mathematically: for `z = (z₀,z₁)` iid complex standard Gaussian,
  `|z₀|², |z₁|²` are iid `Exp` (each a chi-squared on 2 real dof), and
  `|z₀|²/(|z₀|²+|z₁|²) ~ Beta(1,1) = Uniform[0,1]`.
  **Mathlib gap.** Building blocks: `Probability.Distributions.{Beta,Gamma,Exponential}`,
  `gaussianReal`. Missing: (i) `|z|² ~ Gamma/Exp` for complex Gaussian `z`
  (sum of two squared `gaussianReal`s); (ii) independence of the two coordinates'
  squared moduli; (iii) the ratio identity `Gamma(α)/(Gamma(α)+Gamma(β)) ~
  Beta(α,β)` at `α=β=1`; (iv) `Beta(1,1) = Uniform[0,1]`. Each is a real
  probability-theory construction. This is the bulk of the multi-session effort
  and the genuine Mathlib contribution.

## Part 3 — assemble (B.4)

- **L6** — `fs_moment_pushforward_uniform`:
  `(momentMap · 0)∗ fubiniStudyMeasure p₀ = (volume).restrict [0,1]`. Proof:
  rewrite `fubiniStudyMeasure` by L4 (`= gaussianCP`); `(momentMap·0)∗ gaussianCP
  = ((momentMap·0) ∘ gaussianProj)∗ stdGaussian` (`Measure.map_map`);
  `(momentMap·0)(gaussianProj v) = ‖v 0‖²/‖v‖²` (by `momentMap_mk`, a.e. on `v≠0`);
  conclude by L5.

## Status / sequencing

- B.1 (reduction `momentMap_pushforward_eq_haar_marginal`) — DONE (`MomentMarginal.lean`).
- Part 1 (L1–L4) — tractable; implement first. Lands `gaussianCP = fubiniStudyMeasure`.
- Part 2 (L5) — the hard `Beta(1,1)` gap; the multi-session core.
- Part 3 (L6) — trivial assembly once Parts 1–2 land; then retire the axiom.
