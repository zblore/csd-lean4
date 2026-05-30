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

## Progress (2026-05-30) — Part 1 CLOSED

**`gaussianCP p₀ = fubiniStudyMeasure p₀` is proved, foundational-triple-only.**
All of C1–C5 in `CsdLean4/LF4/GaussianCP.lean` compile clean (no `sorry`, no
warnings); `lake build CsdLean4.LF4.GaussianCP` and `lake build CsdLeanTests`
are green. AxiomAudit pins added for `coords` (C1), `conjR`, `gaussianH_map_unitary`,
`gaussianCP_smul_invariant`, `gaussianCP_eq_fubiniStudy`.

- **C1–C3 repaired.** The committed (`d5425f7`) file did not build against the
  pinned Mathlib. Fixes:
  - `coords.map_smul'`: the surviving `c • (z : ℂ)` on the RHS uses the
    `Module ℝ ℂ`/C*-algebra smul instance term, NOT `Complex.instSMulRealComplex`,
    so `Complex.real_smul` / `Algebra.smul_def` / `Complex.smul_re` all refuse to
    fire (simp and `rw` key on the instance term, defeq is not enough). The fix
    is `change _ = (c : ℂ) * _` (defeq-coerces the smul to multiplication) after
    pushing the smul through `WithLp.ofLp_smul` + `Pi.smul_apply`; then
    `push_cast; ring`.
  - `coords.norm_map'`: `(struct y).ofLp i` did not reduce under simp because the
    half-built `LinearIsometryEquiv` literal's FunLike coe has no construction-time
    simp lemma. Fixed with an explicit `show` exposing
    `(WithLp.equiv 2 _).symm ![…]`, then `WithLp.ofLp_toLp` + matrix `cons_val` +
    `Complex.normSq_apply` + `ring`.
  - `isProbabilityMeasure_map` → `Measure.isProbabilityMeasure_map` (namespace
    `MeasureTheory.Measure`).
  - `measurable_gaussianProj`: dropped `borelize` (EuclideanSpace ℂ already a
    BorelSpace; `borelize` clashed with `WithLp.measurableSpace`). The total
    `dite` junk-at-0 map is handled via `measurable_of_measurable_on_compl_singleton 0`
    + `Projectivization.measurable_mk'` on the `{v ≠ 0}` restriction (the note's
    "total `Projectivization.mk'`" does not exist; `mk'` is the subtype map).
- **C4 `conjR` route: by-hand, NOT `restrictScalars`.** Probed
  `(unitaryIsomC U).restrictScalars ℝ` in the full LF4 import context: it
  diamonds (synthInstance failure on `LinearMap.CompatibleSMul … ℝ ℂ`), exactly
  as flagged. `conjR U : ℝ⁴ ≃ₗᵢ[ℝ] ℝ⁴` is built by hand as
  `y ↦ coords.symm (toEuclideanLin U.val (coords y))`, inverse via `Uᴴ`; ℝ-linearity
  via a `toEuclideanLin_real_smul` helper (`mulVec` commutes with the ℝ-scalar
  through `WithLp.ofLp_smul` + `Matrix.mulVec_smul`); `norm_map'` from
  `coords.norm_map` + `unitary_norm_preserving`; inverses from `Uᴴ U = U Uᴴ = 1`.
  `gaussianH_map_unitary` then rewrites `toEuclideanLin U.val ∘ coords =
  coords ∘ conjR U` and kills the inner map by `stdGaussian_map (conjR U)`.
- **C4 invariance + singleton-null.** `gaussianCP_smul_invariant` uses the a.e.
  agreement of `(U • ·) ∘ gaussianProj` and `gaussianProj ∘ toEuclideanLin U.val`
  off `{0}`, via `smul_mk_eq_mk` + `toEuclideanLin_ne_zero`. The null-set fact
  `gaussianH {0} = 0` routes through `coords⁻¹'{0} = {0}` (linear-equiv,
  `map_eq_zero_iff`) and `stdGaussian (ℝ⁴) {0} = 0`; the latter via a one-off
  `NoAtoms (stdGaussian ℝ⁴)` instance from `ProbabilityTheory.IsGaussian.noAtoms`
  with the non-Dirac witness `Var[innerSL ℝ (single 0 1)] = ‖single 0 1‖² = 1 ≠ 0`
  (`variance_dual_stdGaussian` vs `variance_dirac`).
- **C5.** `gaussianCP_eq_fubiniStudy := fubiniStudyMeasure_unique p₀ (gaussianCP p₀)
  gaussianCP_smul_invariant` (the `IsProbabilityMeasure` instance and `[NeZero 2]`
  are inferred; `CPN 2 = ℙ ℂ (EuclideanSpace ℂ (Fin 2))` lines up definitionally).

Remaining for the axiom retirement: Part 2 (L5, the `Beta(1,1)` moment-marginal
gap) and Part 3 (L6 assembly).

## Progress (2026-05-29)

- **`unitary_norm_preserving`** (`CsdLean4/LF4/GaussianFS.lean`, done,
  AxiomAudit-pinned): a unitary matrix's `toEuclideanLin` preserves the Euclidean
  norm (`‖U v‖ = ‖v‖`), from `Uᴴ U = 1`. The matrix-analytic core for L3.
- **`unitaryIsomC`** (done): the `U(2)` action as a **complex** `≃ₗᵢ[ℂ]`.
- **Blocker on L3:** `(unitaryIsomC U).restrictScalars ℝ` (to feed
  `stdGaussian_map`) needs `LinearMap.CompatibleSMul … ℝ ℂ` /
  `IsScalarTower ℝ ℂ (EuclideanSpace ℂ (Fin 2))` + `FiniteDimensional ℝ (…)`.
  These **resolve in a minimal import context but fail inside the full LF4 import
  chain** (instance-resolution ambiguity from the large environment). Next:
  either supply the real-scalar instances explicitly, or take the `ℝ⁴`-isometry
  route (option (a) below) — a genuine real space, no ℝ-over-ℂ instances.

## Part 1 — explicit-coords route (Option 2, chosen; avoids the ℝ/ℂ diamond)

Keep `stdGaussian` on the clean real `EuclideanSpace ℝ (Fin 4)` (so no
`complexToReal` import → `IsScalarTower ℝ ℂ` stays available; no diamond). Lemma
list (`CsdLean4/LF4/GaussianCP.lean`):

- **C1 `coords`** : `EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2)`,
  hand-built: `y ↦ ![y0 + y1·I, y2 + y3·I]`, inverse `z ↦ ![re z0, im z0, re z1, im z1]`.
  Fields: `map_add'`, `map_smul'` (over ℝ), `left/right_inv`, `norm_map'`
  (`‖z‖² = |z0|²+|z1|² = y0²+y1²+y2²+y3² = ‖y‖²`).
- **C2 `gaussianH := (stdGaussian (EuclideanSpace ℝ (Fin 4))).map coords`** — a
  probability measure on `ℂ²`.
- **C3 `gaussianCP := gaussianH.map (projectivization)`** (`mk`, junk at 0;
  measurable) — a probability measure on `ℂℙ¹`.
- **C4 invariance** : `∀ U, gaussianCP.map (U • ·) = gaussianCP`. Reduce (mk
  equivariance + `gaussianH`-a.e.) to `gaussianH.map (toEuclideanLin U.val) =
  gaussianH`, i.e. `((coords.symm).trans ((unitary as fn).trans coords))` is an
  `ℝ⁴`-isometry preserving `stdGaussian ℝ⁴` (`stdGaussian_map`, clean). The
  unitary-as-`ℝ⁴`-isometry conjugate avoids `ℂ²`'s real-module diamond because the
  composite is built/typed on `ℝ⁴`; norm transfer uses `unitary_norm_preserving`
  + `coords.norm_map`.
- **C5 `gaussianCP = fubiniStudyMeasure p₀`** by `fubiniStudyMeasure_unique`.

Then Part 3 (L6) composes with B.1 + the (Part 2) Beta marginal.

## Part 1 — `gaussianCP = fubiniStudyMeasure` (B.2; original sketch)

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

**ℝ/ℂ friction — findings from probing (2026-05-29):**
- `stdGaussian (EuclideanSpace ℂ (Fin 2))` **elaborates directly** — both
  `InnerProductSpace ℝ` and `FiniteDimensional ℝ` resolve through the existing
  imports. So **no `ℝ⁴` bridge is needed**; work on `H = EuclideanSpace ℂ (Fin 2)`.
- The remaining snag is **L3**: `stdGaussian_map` needs the `U(2)` action as a
  `≃ₗᵢ[ℝ]`. `(toEuclideanLinearEquiv U).restrictScalars ℝ` fails — missing
  `LinearMap.CompatibleSMul H H ℝ ℂ` (i.e. `IsScalarTower ℝ ℂ H`). Fix: either
  supply that instance (`IsScalarTower ℝ ℂ H` should hold for the ℝ→ℂ→module
  tower; check no diamond), or build the `≃ₗᵢ[ℝ]` by hand — same `toFun` as
  `toEuclideanLinearEquiv U`, ℝ-linearity is free (ℂ-linear ⟹ ℝ-linear),
  `norm_map'` from `‖U v‖ = ‖v‖` (unitary preserves the norm). The latter is the
  safer route if the instance route diamonds.

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
