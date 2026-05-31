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

## Part 2 — the moment marginal is uniform (B.3) — DETAILED PLAN (2026-05-30)

**Headline (L5).** `T∗ stdGaussian(ℝ⁴) = volume.restrict (Ioo 0 1)`, where
`T : EuclideanSpace ℝ (Fin 4) → ℝ`, `T y = (y0²+y1²)/(y0²+y1²+y2²+y3²)`. (Via
`coords`, `T y = ‖(coords y) 0‖²/‖coords y‖² = momentMap (mk (coords y)) 0`, so
L5 on ℝ⁴ is exactly the moment marginal — see L6.) Target measure note:
`betaPDFReal 1 1 x = 1/beta(1,1) = 1` on `(0,1)`, so `betaMeasure 1 1 =
volume.restrict (Ioo 0 1)` is a one-screen computation; **we never need general
`Beta(α,β)` theory** — the analytic content is the two pushforwards below.

**Reconnaissance verdict (2026-05-30): NOT a blocked foundational gap.** Every
load-bearing Mathlib tool exists; Part 2 is the *assembly* (the upstreamable
contribution). Pillars, with exact names:
- `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`: `polarCoord`
  (`OpenPartialHomeomorph (ℝ×ℝ) (ℝ×ℝ)`), `hasFDerivAt_polarCoord_symm`,
  `lintegral_comp_polarCoord_symm (f : ℝ×ℝ → ℝ≥0∞)`,
  `integral_comp_polarCoord_symm`, `polarCoord_source_ae_eq_univ`.
- `Mathlib/MeasureTheory/Function/Jacobian.lean:1133`
  `map_withDensity_abs_det_fderiv_eq_addHaar (hs : NullMeasurableSet s μ)
   (hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
   Measure.map f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|)
     = μ.restrict (f '' s)` — and the integral form
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (Jacobian.lean:1189).
- `Mathlib/MeasureTheory/Integral/Gamma.lean`: `integral_rpow_mul_exp_neg_mul_rpow`
  / `integral_exp_neg_mul_rpow` for the 1-D radial integrals (the `∫ S e^{-S/2}=4`
  marginalisation constant).
- `map_pi_eq_stdGaussian` (already used in Part 1): `stdGaussian(EuclideanSpace ℝ ι)
  = (Measure.pi fun _ => gaussianReal 0 1).map (toLp 2)` — gives the product/block
  structure and per-coordinate density `gaussianReal 0 1 = volume.withDensity gaussianPDF`.

**Lemma DAG (`CsdLean4/LF4/MomentMarginalUniform.lean`, new file).**

- **L5.0 (base rewrite).** Reduce `T∗ stdGaussian(ℝ⁴)` to a Lebesgue-density
  pushforward on `Fin 4 → ℝ`: via `map_pi_eq_stdGaussian` + `Measure.map_map`,
  `T∗ stdGaussian(ℝ⁴) = (T ∘ toLp)∗ (Measure.pi (gaussianReal 0 1))`, and
  `Measure.pi (gaussianReal 0 1) = (volume : Measure (Fin 4 → ℝ)).withDensity
  (∏ i, gaussianPDF (x i))` (pi-of-withDensity). Risk: LOW-MED (the pi↔volume
  density identification; check `Measure.pi` of `withDensity` lemmas /
  `volume_pi`).

- **L5.1 (single-block law = Exp(1/2)).** `Lsq∗ stdGaussian(ℝ²) = expHalf`, where
  `Lsq p = ‖p‖²` and `expHalf := volume.withDensity (s ↦ ENNReal.ofReal
  (if 0<s then (1/2)·Real.exp (-s/2) else 0))`. **Proof via `polarCoord`:** for
  test `g ≥ 0`, `∫⁻ g d(Lsq∗ μ) = ∫⁻ p, g(‖p‖²) ∂stdGaussian(ℝ²)`; rewrite
  `stdGaussian(ℝ²)` to `volume.withDensity ((1/2π)e^{-‖p‖²/2})` and apply
  `lintegral_comp_polarCoord_symm` (Jacobian `r`): `= ∫⁻ r in Ioi 0, ∫⁻ θ in
  Ioo (-π) π, g(r²)·(1/2π)e^{-r²/2}·r dθ dr = ∫⁻ r in Ioi 0, g(r²)·e^{-r²/2}·r dr`
  (θ-integral kills 2π); substitute `s = r²` (1-D CoV, `ds = 2r dr`) to get
  `∫⁻ s in Ioi 0, g(s)·(1/2)e^{-s/2} ds = ∫⁻ g d expHalf`. Conclude by
  `Measure.ext`/`lintegral`-characterisation. Risk: **MED** (the θ-marginal and
  the 1-D `s=r²` substitution; the `stdGaussian(ℝ²) = volume.withDensity …`
  density form must be pinned — check `stdGaussian` density lemmas or build from
  `map_pi_eq_stdGaussian` + `gaussianReal` density).

- **L5.2 (block product).** `P∗ stdGaussian(ℝ⁴) = expHalf.prod expHalf`, where
  `P y = (y0²+y1², y2²+y3²)`. Factor `Measure.pi (Fin 4)` into the `{0,1}` and
  `{2,3}` block product (`Measure.pi` reindex / `MeasurePreserving` block split),
  then `(P)∗(block₁ × block₂) = (Lsq∗block₁).prod (Lsq∗block₂)` via
  `Measure.map_prod_map` (each factor = `expHalf` by L5.1). Risk: MED (the 4↦2×2
  block reindexing bookkeeping).

- **L5.3 (ratio → uniform; THE CRUX).** `R∗ (expHalf.prod expHalf) =
  volume.restrict (Ioo 0 1)`, where `R q = q.1/(q.1+q.2)`. **Proof:** for test
  `g ≥ 0`, `∫⁻ g d(R∗ μ) = ∫⁻_(Q) g(A/(A+B))·(1/4)e^{-(A+B)/2} dA dB`
  (`Q = Ioi 0 ×ˢ Ioi 0`). Apply the 2-D change of variables (the diffeo
  `Φ(A,B) = (A/(A+B), A+B)` on `Q`, onto `Ioo 0 1 ×ˢ Ioi 0`, inverse
  `(T,S)↦(T·S,(1-T)·S)`, `|det Φ⁻¹'| = S`) via
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (or `map_withDensity_…`):
  `= ∫⁻_(Ioo 0 1) ∫⁻_(Ioi 0) g(T)·(1/4)e^{-S/2}·S dS dT` (Tonelli)
  `= ∫⁻_(Ioo 0 1) g(T)·[(1/4)·∫_{S>0} S e^{-S/2} dS] dT = ∫⁻_(Ioo 0 1) g(T) dT`,
  using `∫_{S>0} S e^{-S/2} dS = 4` (`Integral/Gamma.lean`). Risk: **MED-HIGH**
  (set up `Φ`/`Φ⁻¹` as the diffeo, its `fderiv`/`det = S`, `InjOn`, image
  `= Ioo 0 1 ×ˢ Ioi 0`; this is the single hardest lemma).

- **L5 (assemble).** `T = R ∘ P` (off the null `{‖y‖=0}`); compose L5.2 + L5.3
  via `Measure.map_map`. Handle the `A+B=0` null set (= `{y=0}`, `stdGaussian`-null
  by the `instNoAtomsStdGaussian4` already built in Part 1) so `R∘P` agrees a.e.
  with `T`.

**Independence framing note.** L5.2 *is* the independence statement (joint law =
product), so no separate `IndepFun` lemma is needed — the product measure carries
it. If a cleaner path emerges via `iIndepFun` from `Measure.pi`
(`Mathlib/Probability/Independence/*`), it is interchangeable with L5.2.

## Part 3 — assemble (B.4)

- **L6** — `fs_moment_pushforward_uniform`:
  `(momentMap · 0)∗ fubiniStudyMeasure p₀ = (volume).restrict [0,1]`. Proof:
  rewrite `fubiniStudyMeasure` by L4 (`= gaussianCP`); `(momentMap·0)∗ gaussianCP
  = ((momentMap·0) ∘ gaussianProj)∗ stdGaussian` (`Measure.map_map`);
  `(momentMap·0)(gaussianProj v) = ‖v 0‖²/‖v‖²` (by `momentMap_mk`, a.e. on `v≠0`);
  conclude by L5.

### Slice 4 — CLOSED (2026-05-31, commit c2d6536). Axiom retired; LF4 axiom-free.

`fs_moment_pushforward_uniform` is now a foundational-triple **theorem**
(`CsdLean4/LF4/MomentUniform.lean`): `regroupPi_map` (bridge via
`finSumFinEquiv` + `measurePreserving_sumPiEquivProdPi` — which *does* exist; the
recon below missed it), `moment_marginal_uniform_pi` (L5), and L6 via
`gaussianCP_eq_fubiniStudy` + `Measure.map_congr` (moment-map = `Tpi` a.e. off
`{0}`) + `Ioo_ae_eq_Icc`. The two `_uncond` consumers moved to `MomentUniform.lean`
(`DuistermaatHeckman.lean` now axiom-free); AxiomAudit pins flipped to the
foundational triple; `AXIOMS.md §2.3` DISCHARGED. `lake build CsdLeanTests` green.
(`regroupPi_map`/L6 need `set_option maxHeartbeats 1000000` — heavy
`piCongrLeft`/`finSumFinEquiv` defeq.) The detailed plan below is historical.

### Slice 4 — DETAILED PLAN (2026-05-31) — the remaining work (historical)

**Status: NOT a clean assembly; the L5.2c bridge has no Mathlib MP shortcut.**
Slices 1–3 (L5.1, L5.2a/b, L5.3) are CLOSED and reusable. The remainder is three
sub-tasks, the first of which is genuine custom plumbing:

- **L5.2c (the bridge) — fiddliest, no library shortcut.**
  `regroup∗ stdGaussian(ℝ⁴) = gaussian2.prod gaussian2`, where
  `regroup y = ((y 0, y 1), (y 2, y 3)) : (ℝ×ℝ)×(ℝ×ℝ)`.
  Route: `map_pi_eq_stdGaussian` gives `stdGaussian(EuclideanSpace ℝ (Fin 4)) =
  (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)).map (toLp 2)`, so it reduces to
  `m∗ (pi (Fin 4) gaussianReal) = gaussian2.prod gaussian2` with
  `m y = ((y 0,y 1),(y 2,y 3))` and `gaussian2 = (gaussianReal 0 1).prod
  (gaussianReal 0 1)` (Slice 2 L5.2a). **Findings (reconnaissance):**
  - `measurePreserving_piEquivPiSubtypeProd (·<2)` splits `pi (Fin 4)` into a
    product over the 2-element *subtypes* `{i:Fin4 // i<2}` and `{i // ¬i<2}`;
    reindexing each subtype to `Fin 2` (`measurePreserving_piCongrLeft` +
    `Fintype.equivFin`/card-2 proof) then `measurePreserving_finTwoArrow` to `ℝ×ℝ`
    is available, but the *composite* equiv's concrete action is hard to pin to
    exactly `y ↦ ((y0,y1),(y2,y3))`, so proving `m = E` (composite) is itself painful.
  - There is **no** `measurePreserving_sumPiEquivProdPi` (only `Equiv`/`LinearEquiv`
    `sumPiEquivProdPi`), so the cleaner `Fin 2 ⊕ Fin 2 ≃ Fin 4` route needs a
    hand-built `MeasurableEquiv` + MP proof.
  - `Measure.prod_eq` rectangle route needs `pi{y | (y0,y1)∈C ∧ (y2,y3)∈D}` to
    factor for *general* measurable `C,D` — i.e. block-independence of the pi
    measure — which again routes back through the equiv split.
  Recommended: build the composite `MeasurableEquiv (Fin 4 → ℝ) ((ℝ×ℝ)×(ℝ×ℝ))` via
  `piEquivPiSubtypeProd` + per-block (`piCongrLeft` to `Fin 2`) + `finTwoArrow`,
  prove `MeasurePreserving` by `.comp`/`.prod`, then show `m` equals it on a
  `funext`/`Fin.cases`. ~50–80 lines.

- **L5 (compose).** `T∗ stdGaussian(ℝ⁴) = volume.restrict (Ioo 0 1)`,
  `T = (fun q => q.1/(q.1+q.2)) ∘ (Prod.map Lsq Lsq) ∘ regroup ∘ toLp`-ish:
  `map_pi_eq_stdGaussian` → `Measure.map_map` → L5.2c → L5.2b
  (`blockSqNorm_map_gaussian2_prod`) → L5.3 (`ratioSqNorm_map_expHalf_prod`).

- **L6 + retirement.** Chain L5 with `gaussianCP_eq_fubiniStudy` (Part 1),
  `Measure.map_map`, `momentMap_mk` (`(momentMap·0)(gaussianProj(coords y)) =
  ‖coords y 0‖²/‖coords y‖² = (y0²+y1²)/‖y‖²`, a.e. off the `stdGaussian`-null
  `{0}`), and `volume.restrict (Ioo 0 1) = volume.restrict (Icc 0 1)` (endpoints
  null: `Measure.restrict_congr_set` with `Ioo =ᵐ Icc`). **Import restructuring:**
  the axiom lives in `DuistermaatHeckman.lean` and is consumed by
  `fs_born_volume_ratio_qubit_uncond` / `qubit_born_frequency_convergence_uncond`
  there; to make it a *theorem*, add the L5-proving file's import to
  `DuistermaatHeckman.lean` and verify no cycle (`GaussianCP`,
  `MomentRatioUniform`, `MomentMarginalUniform`, `MomentMap` must not import
  `DuistermaatHeckman`). Then flip the two `_uncond` AxiomAudit pins from
  `[…, LF4.fs_moment_pushforward_uniform]` to `[propext, Classical.choice,
  Quot.sound]` and drop the axiom from `AXIOMS.md §2.3`.

## Status / sequencing

- B.1 (reduction `momentMap_pushforward_eq_haar_marginal`) — DONE (`MomentMarginal.lean`).
- Part 1 (C1–C5) — DONE (commit da8f9e0): `gaussianCP_eq_fubiniStudy`. Foundational
  triple, AxiomAudit-pinned.
- Part 2 (L5) — detailed DAG above; the multi-session core. **Tools all exist**
  (polarCoord, Jacobian CoV, Integral/Gamma); it is assembly, not a blocked gap.
- Part 3 (L6) — trivial assembly once L5 lands; then retire the axiom.

**Committable slices for Part 2 (each foundational-triple, AxiomAudit-pinned):**
1. **Slice 1 — L5.1 (single-block law = Exp(1/2)).** Self-contained, reusable,
   genuinely upstreamable (`‖·‖²∗ stdGaussian(ℝ²) = Exp(1/2)`). Best first target:
   exercises the polarCoord + 1-D substitution machinery in isolation. Includes
   L5.0 base rewrite as a prerequisite helper.
2. **Slice 2 — L5.2 (block product).** Depends on Slice 1; pure measure-algebra
   (pi block split + `map_prod_map`).
3. **Slice 3 — L5.3 (ratio → uniform).** The crux; independent of Slices 1–2 (can
   be developed in parallel against the abstract `expHalf.prod expHalf`). Highest
   risk; the diffeo `Φ` + its Jacobian determinant is the hard nut.
   **(DONE — 2026-05-31.)** `ratioSqNorm_map_expHalf_prod` in
   `CsdLean4/LF4/MomentRatioUniform.lean`, foundational-triple, AxiomAudit-pinned.
   Five ingredients + assembly:
   - `lintegral_radial_const`: `∫⁻_{S>0} (1/4)·S·e^{−S/2} = 1` (Gamma 2 = 1 via
     `integral_rpow_mul_exp_neg_mul_Ioi` + `ofReal_integral_eq_lintegral_ofReal`;
     integrability from `integrableOn_rpow_mul_exp_neg_mul_rpow`).
   - `Psi (T,S) = (T·S,(1−T)·S)`, `hasFDerivAt_Psi` (single `exact` from
     `HasFDerivAt.mul`/`.prodMk`; `psiFDeriv` shaped to match the produced deriv),
     `psiFDeriv_det = S` (via `Module.Basis.finTwoProd` + `LinearMap.det_toMatrix`
     + `Matrix.det_fin_two`; needs `open Module`).
   - `injOn_Psi` (`linear_combination` + `mul_right_cancel₀`), `image_Psi`
     (preimage `(A/(A+B), A+B)`).
   - Assembly: `Measure.ext_of_lintegral` → `lintegral_map` → `prod_withDensity`
     → restrict-to-quadrant via `lintegral_indicator` → `← image_Psi` +
     `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (μ = volume explicit) →
     `setLIntegral_prod` (Tonelli) → `lintegral_mul_const` + `lintegral_radial_const`.
   Key frictions resolved: `lintegral_withDensity_eq_lintegral_mul` fixes its
   test/density functions from the supplied measurability proofs, so those must be
   shaped to the goal (type-ascribed, not `∘`-composed); the post-density integrand
   is folded to `d`-form by a defeq `show`; pair projections `(T,y).1/.2` reduced
   by a defeq `show`.
4. **Slice 4 — L5 + L6 assembly.** Compose, discharge the `{0}` null set, rewrite
   `fubiniStudyMeasure` by `gaussianCP_eq_fubiniStudy`, retire
   `fs_moment_pushforward_uniform` from `AXIOMS.md §2.3`; flip
   `fs_born_volume_ratio_qubit_uncond` / `qubit_born_frequency_convergence_uncond`
   to foundational-triple-only in AxiomAudit.

**Recommended entry: Slice 1.** Smallest self-contained increment, lands a
reusable distributional fact, and de-risks the polarCoord route before the harder
Jacobian work in Slice 3. **(DONE — commit f7e1bdd.)**

### Slice 2 — DETAILED PLAN (2026-05-30)

**Recon verdict: the block-product (independence) content is CLEAN; the
`stdGaussian(EuclideanSpace ℝ (Fin 4))` regrouping is the only bookkeeping cost,
and is deferred to Slice 4.** All tools exist. Two lemmas, both in
`MomentMarginalUniform.lean` (extending Slice 1):

- **L5.2a (2-D bridge, reusable).**
  `gaussian2 = (gaussianReal 0 1).prod (gaussianReal 0 1)`.
  Proof: `gaussianReal_of_var_ne_zero` (Mathlib `Gaussian/Real.lean:203`,
  `gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1)`); then
  `MeasureTheory.prod_withDensity` (`WithDensity.lean:711`,
  `(μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity
   (p ↦ f p.1 * g p.2)`); `Measure.volume_eq_prod` to fold `volume.prod volume
   = volume` on `ℝ × ℝ`; then density algebra
  `gaussianPDF 0 1 x * gaussianPDF 0 1 y = ENNReal.ofReal ((1/2π) e^{-(x²+y²)/2})`
  via `ENNReal.ofReal_mul` and `(1/√(2π))·(1/√(2π)) = 1/(2π)`
  (`Real.sqrt`/`Real.mul_self_sqrt`, `2π ≥ 0`). Risk: **MED** (the `1/√(2π)`
  squaring + `ENNReal.ofReal` product bookkeeping; everything nonneg so clean).

- **L5.2b (block product = independence).**
  `Measure.map (Prod.map Lsq Lsq) (gaussian2.prod gaussian2) = expHalf.prod expHalf`,
  where `Lsq p = p.1² + p.2²` and
  `Prod.map Lsq Lsq : (ℝ×ℝ)×(ℝ×ℝ) → ℝ×ℝ`. Proof: `Measure.map_prod_map`
  (Mathlib `Measure/Prod.lean`,
  `map (Prod.map f g) (μ.prod ν) = (μ.map f).prod (ν.map g)`; needs the two
  factor maps measurable) + `sqNorm_map_gaussian2` (Slice 1) on each factor.
  ~10 lines. Risk: LOW. **This is the independence statement** — the joint law of
  the two block squared-norms is the product, no separate `IndepFun` needed.

**Deferred to Slice 4 (NOT Slice 2): L5.2c — the EuclideanSpace bridge.**
`stdGaussian(EuclideanSpace ℝ (Fin 4))` transported to `gaussian2.prod gaussian2`.
Route: `map_pi_eq_stdGaussian` (`stdGaussian = (Measure.pi (fun _ => gaussianReal
0 1)).map (toLp 2)`) + `measurePreserving_piEquivPiSubtypeProd` (`Pi.lean:727`,
splits `Measure.pi (Fin 4)` into the `{i<2}`/`{i≥2}` block product) +
`measurePreserving_piCongrLeft` reindex each `Fin 2` block + L5.2a per block. This
is index/reindex bookkeeping (`Fin 4 ↔ (Fin 2→ℝ)×(Fin 2→ℝ) ↔ (ℝ×ℝ)×(ℝ×ℝ)`,
through `toLp`/`ofLp`), more fiddly than deep — so it lives in Slice 4 alongside
the `coords`/`momentMap` composition, the `{0}`-null handling, and the axiom
retirement, where all the "connect to Part 1" plumbing is concentrated.

**Slice 2 scope = L5.2a + L5.2b only** (self-contained, no EuclideanSpace/`pi`
gymnastics; ~40-60 lines total). Foundational-triple, AxiomAudit-pinned.

**(DONE — 2026-05-31.)** Both lemmas land in `MomentMarginalUniform.lean`,
foundational-triple, AxiomAudit-pinned, `lake build CsdLeanTests` green:
- `gaussianPDFReal_zero_one` (helper): `gaussianPDFReal 0 1 x = (√(2π))⁻¹·e^{-x²/2}`.
- `gaussian2_eq_prod` (L5.2a): `gaussian2 = (gaussianReal 0 1).prod (gaussianReal 0 1)`,
  via `gaussianReal_of_var_ne_zero` + `prod_withDensity` + `Measure.volume_eq_prod`,
  closing on the density identity `(1/2π)e^{-(x²+y²)/2} = pdf(x)·pdf(y)`
  (`(√(2π))⁻¹·(√(2π))⁻¹ = 1/(2π)` via `Real.mul_self_sqrt`; `exp` factors kept atomic).
- `blockSqNorm_map_gaussian2_prod` (L5.2b): `(Prod.map ‖·‖² ‖·‖²)∗ (gaussian2 × gaussian2)
  = expHalf × expHalf`, via `← Measure.map_prod_map` + `sqNorm_map_gaussian2` (Slice 1);
  `SFinite gaussian2` discharged by `unfold gaussian2; infer_instance`
  (`Measure.withDensity.instSFinite`). This is the independence statement.

**Honesty note.** This route proves the axiom outright (no new axiom, no carving)
— `fs_moment_pushforward_uniform` becomes a theorem and the uncond qubit Born
results become foundational-triple-only. It does NOT touch the deeper structural
debts (D1 dynamics `Φ=id`; the metric/basis ontic primitive A5/G3b); it discharges
exactly the one geometry axiom on the qubit Born-from-volume chain.
