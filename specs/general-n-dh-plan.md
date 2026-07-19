> ⚠️ HISTORICAL — layer complete; frozen execution log. Open items live in [BACKLOG.md](BACKLOG.md).
# General-N Duistermaat–Heckman — plan + honest difficulty grading

Status: planning doc, 2026-06-01. Scope: extend the discharged qubit DH fact
(`fs_moment_pushforward_uniform`, N=2) to general N. Where the genuine target sits,
what is tractable, and where the real walls are.

## What N=2 gave us, and why N≥3 is not symmetric

The qubit discharge (`MomentUniform.lean`) proved
`(momentMap · 0)∗ μ_FS = Uniform[0,1]` — a **scalar marginal** of the first
squared-modulus of a Haar-random unit `ℂ²` vector. It fed
`fs_born_volume_ratio_qubit` via the **sublevel set** `{p | momentMap p 0 ≤ b₀(ψ)}`,
whose FS-measure is the coordinate-0 marginal CDF at `b₀`. For N=2 the moment
polytope is the 1-D segment `[0,1]`, the marginal is `Uniform`, so that CDF *is*
`b₀ = ‖⟨e₀,ψ⟩‖²`.

**This does NOT generalize.** For general N the coordinate-0 marginal of the Haar
squared-moduli is `Beta(1, N−1)`, CDF `1 − (1−x)^{N−1}`. So for N≥3 the sublevel-set
FS-measure is `1 − (1−b₀)^{N−1} ≠ b₀`. The single-coordinate marginal cannot give a
general-N Born result — **the genuine general-N DH must be the JOINT law** on the
moment simplex (the Dirichlet(1,…,1) distribution), which feeds `born_eq_volume_ratio`
(the barycentric Lebesgue-volume ratio, already proved general-N) rather than the
sublevel set.

## Already in place (reusable)

- `born_eq_volume_ratio` (`BornVolume.lean`, general N, foundational triple): Born
  weight = barycentric **Lebesgue**-volume ratio on the moment polytope. The missing
  step is lifting Lebesgue-polytope → FS-volume-on-Σ, which is exactly the joint DH.
- `momentMap_orbit` (`MomentPushforward.lean`): `Φ∗μ_FS = (U ↦ ‖(U·rep)ᵢ‖²)∗ Haar` —
  reduces DH to the Haar squared-moduli law.
- The N=2 Gaussian-route slices (`MomentMarginalUniform.lean`, `MomentRatioUniform.lean`,
  `MomentUniform.lean`): `coords`, `gaussian2`, `expHalf`, `sqNorm_map_gaussian2`
  (Slice 1), `blockSqNorm_map_gaussian2_prod` (Slice 2), `ratioSqNorm_map_expHalf_prod`
  (Slice 3, the diffeo `Ψ`), `regroupPi_map` + `fs_moment_pushforward_uniform` (Slice 4).

## Mathlib gaps (confirmed absent)

- **No uniform/Hausdorff measure on `stdSimplex`** (Mathlib has the set, not a measure).
- **No Dirichlet distribution.**
- Consequence: the *intrinsic* "`Φ∗μ_FS = uniform_Δ`" cannot even be **stated** without
  first building a simplex surface measure — a separate infra tranche on its own.

## The statable general-N target (avoids the simplex-measure gap)

Express the simplex in **free coordinates**: parametrise `Δ_{N−1}` by its first
`N−1` coordinates `(s_0,…,s_{N−2}) ∈ ℝ^{N−1}` (the last is `1 − ∑`). Then the joint
DH law is the **Dirichlet(1,…,1) density = constant `(N−1)!` w.r.t. Lebesgue on
ℝ^{N−1}**, restricted to the open simplex `{s | s_i > 0, ∑ s_i < 1}`. This uses only
`volume : Measure (Fin (N−1) → ℝ)` — no Hausdorff/simplex-surface measure. Target:

```
fs_moment_joint_dirichlet_N :
  (p ↦ (momentMap p 0, …, momentMap p (N-2)))∗ μ_FS,N
    = (Nat.factorial (N-1)) • volume.restrict (openSimplex (N-1))
```

This IS the genuine general-N DH, and it lifts `born_eq_volume_ratio` to the FS
volume on Σ (both live on Lebesgue coordinates).

## DAG (generalises the qubit slices)

- **Part 1 (Gaussian = FS), general N.** `coords_N : ℝ^{2N} ≃ₗᵢ[ℝ] ℂ^N` (generalise
  `coords`); `gaussianCP_N = μ_FS,N` by `fubiniStudyMeasure_unique`. **Risk: LOW-MED**
  — Part 1 was never deeply N-specific; the `coords` isometry + invariance argument
  generalise, mostly index bookkeeping (`Fin 4`→`Fin 2N`, `Fin 2`→`Fin N`).
- **Part 2a (block law), general N.** `stdGaussian(ℝ^{2N})` ≅ `expHalf^{⊗N}` on `ℝ^N`
  via `Measure.pi` reindexing + per-block `sqNorm_map_gaussian2` (Slice 1, reused
  verbatim). **Risk: MED** — the `Fin 2N ↔ (Fin N → ℝ²)` reindex (generalises
  `regroupPi_map`'s `finSumFinEquiv` to an N-fold `Measure.pi` split).
- **Part 2b (THE CRUX): Gamma → Dirichlet in free coordinates.**
  `R_N : ℝ^N_{>0} → ℝ^{N−1}`, `s ↦ (s_0/Σ, …, s_{N−2}/Σ)` pushes `expHalf^{⊗N}` to
  `(N−1)! · volume.restrict (openSimplex)`. Proof = the N-dim change of variables
  through the diffeo `Φ(s) = (s_0/Σ,…,s_{N−2}/Σ, Σ)`, inverse
  `(t,S) ↦ (t_0·S,…,t_{N−2}·S, (1−∑t)·S)`, **Jacobian det = `S^{N−1}`**; the
  `S`-integral `∫ S^{N−1}(1/2)^N e^{−S/2} = (N−1)!` (via
  `integral_rpow_mul_exp_neg_mul_Ioi` with `a = N`, generalising
  `lintegral_radial_const`). Tooling exists
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), but the **N-dimensional
  fderiv + `det = S^{N−1}` + `InjOn` + image** is the research-grade nut.
  **Risk: HIGH (multi-session).** The N=2 `Ψ` was already the single hardest slice;
  the N-dim determinant (a bordered/rank-one-update matrix det) is the real work.
- **Part 3 (assemble).** `momentMap (mk (coords_N y)) k = (y_{2k}²+y_{2k+1}²)/‖y‖²
  = R_N(blockLsq_N y) k` a.e. off `{0}`; compose with `gaussianCP_N = μ_FS,N`.
  **Risk: MED** — generalises `MomentUniform`'s assembly + `{0}`-null handling.

## Committable slices (each foundational-triple, AxiomAudit-pinned)

1. **Slice A — single-coordinate marginal `Beta(1, N−1)`** (warm-up, de-risks the
   Gaussian-route generalisation; reuses N=2 machinery). `(momentMap · 0)∗ μ_FS,N =
   Beta(1,N−1)` on `[0,1]`. Genuinely reusable distributional fact; does **NOT** close
   the carve-out (Beta-CDF ≠ identity for N≥3 — see above), so its value is the
   distributional content + correctness check, not a Born result. Risk: MED.
2. **Slice B — Part 1 general N** (`gaussianCP_N = μ_FS,N`). Standalone, reusable. MED.
3. **Slice C — Part 2a block law** (`expHalf^{⊗N}`). Depends on B-style reindex. MED.
4. **Slice D — Part 2b the crux** (Gamma→Dirichlet, N-dim Jacobian). HIGH, multi-session.
5. **Slice E — Part 3 assemble** → `fs_moment_joint_dirichlet_N`; lift
   `born_eq_volume_ratio` to FS volume on Σ for general N.

## Honest verdict

- **Genuinely tractable now:** Slices A, B, C (the Gaussian-route generalisation up to
  the crux). Each a clean, committable, foundational-triple increment.
- **The wall:** Slice D (the N-dim Gamma→Dirichlet Jacobian) is research-grade —
  the N=2 `Ψ` diffeo was already the hardest single proof in the qubit discharge, and
  the determinant `S^{N−1}` of the N-dim bordered map is a real linear-algebra +
  change-of-variables build. Plausibly upstreamable (it IS the Dirichlet distribution,
  a longstanding Mathlib gap).
- **NOT in scope even after D:** the intrinsic `uniform_Δ` on the simplex surface
  (needs a Hausdorff/simplex measure — separate infra), and the QI-entropy items.
- **NOT closed by any of this:** the deeper carve-out (outcome regions from
  deterministic dynamics, G3b) — this is a derivation-strengthening of *where the
  Born numbers come from given the Kähler structure*, exactly as the N=2 result was.

## Recommended entry

**Slice B (Part 1 general N)** — it is the cleanest standalone reusable increment
(`gaussianCP_N = μ_FS,N`), lowest risk, and unblocks everything downstream. Slice A
(the Beta marginal) is an optional warm-up/correctness-check but, being a marginal,
does not advance the Born result; skip it unless we want the distributional fact for
its own sake. The crux (Slice D) should be scoped as its own multi-session effort
once B+C land.

## Progress (2026-06-01) — Slice B DONE

`CsdLean4/LF4/GaussianCPN.lean`, `gaussianCPN_eq_fubiniStudy [NeZero N] (p₀ : CPN N)
: gaussianCPN p₀ = fubiniStudyMeasure p₀`. Foundational triple, AxiomAudit-pinned.
The general-N analogue of `gaussianCP_eq_fubiniStudy`, generalising every C1–C5
piece of `GaussianCP.lean`:
- `coordsN : ℝ^{N×2} ≃ₗᵢ[ℝ] ℂ^N` (real space indexed by `Fin N × Fin 2`, so coord
  `i` reads its re/im off `(i,0)`/`(i,1)` — no `2i`/`2i+1` arithmetic).
- `gaussianHN`/`gaussianProjN`/`gaussianCPN` + probability instances.
- `conjRN` real-conjugate isometry + `gaussianHN_map_unitary` (U(N)-invariance of
  the transported Gaussian, via `stdGaussian_map`).
- `stdGaussianN_ne_dirac` + `instNoAtomsStdGaussianN` (needs `[NeZero N]` for a
  nonempty index) ⟹ origin is `gaussianHN`-null.
- `gaussianCPN_smul_invariant` ⟹ `gaussianCPN_eq_fubiniStudy` via
  `fubiniStudyMeasure_unique`.
The discharged qubit `GaussianCP.lean` is left untouched (parallel development, not
a refactor — its `Fin 4` machinery is load-bearing for the retired axiom).
Dependencies (`unitary_norm_preserving`, `fubiniStudyMeasure_unique`,
`smul_mk_eq_mk`) were already general-N.

## Progress (2026-06-01) — Slice C DONE

`MomentMarginalUniform.lean`, `blockSqNorm_map_gaussianN_pi {N} :
(fun q i => (q i).1² + (q i).2²)∗ (pi (fun _ : Fin N => gaussian2))
= pi (fun _ : Fin N => expHalf)`. Foundational triple, AxiomAudit-pinned. The
N-fold analogue of `blockSqNorm_map_gaussian2_prod`: a clean `Measure.pi_map_pi`
application, each factor closed by Slice 1 (`sqNorm_map_gaussian2`). Added the
supporting `instProbGaussian2` / `instProbExpHalf` probability instances. Came in
~20 lines as planned (LOW risk; the only fix was the `Measure.isProbabilityMeasure_map`
name). The `EuclideanSpace ℝ (Fin N × Fin 2) ↔ pi (Fin N) gaussian2` reindex bridge
is deferred to assembly (Slice E), as the qubit deferred its bridge to Slice 4.

Next: Slice D (the crux — N-dim Gamma→Dirichlet, Jacobian `det = S^{N−1}`;
research-grade, its own multi-session effort).

## Slice D — DETAILED PLAN (the crux: Gamma → Dirichlet in free coordinates)

**Target.** The N-fold ratio map sends `expHalf^{⊗N}` to the Dirichlet(1,…,1) law,
expressed (to dodge the missing simplex surface measure) as the constant `(N−1)!`
density on the open simplex in free coordinates `ℝ^{N−1}`:

```
ratioSqNorm_map_expHalf_pi {N} :
  Measure.map R_N (Measure.pi (fun _ : Fin N => expHalf))
    = ((Nat.factorial (N-1) : ℝ≥0∞)) • volume.restrict (openSimplex)
  where  R_N (s : Fin N → ℝ) : Fin (N-1) → ℝ := fun k => s (castSucc k) / (∑ i, s i)
         openSimplex : Set (Fin (N-1) → ℝ) := {t | (∀ k, 0 < t k) ∧ ∑ k, t k < 1}
```

N=2 is exactly `ratioSqNorm_map_expHalf_prod` (`Beta(1,1)=Uniform[0,1]`, `(N−1)!=1`).
This is the genuine general-N DH content; everything else (Slices B, C, E) is bridge.

**Why this is the wall.** The N=2 proof (`MomentRatioUniform.lean`) was already the
hardest single piece of the qubit discharge — the 2-D diffeo `Ψ`, its `fderiv`,
`psiFDeriv_det = S`, `injOn_Psi`, `image_Psi`, and the radial collapse. Slice D is
the N-dimensional version of *every* one of those, and the determinant step is a
real linear-algebra theorem rather than a `Matrix.det_fin_two` one-liner.

### Lemma DAG (new file `CsdLean4/LF4/MomentRatioUniformN.lean`)

- **D.1 Radial moment, general N — DONE 2026-06-01** (`MomentRatioUniformN.lean`,
  `lintegral_radial_moment`). `∫⁻_{S>0} Sⁿ·e^{−S/2} = 2^{n+1}·n!` (the `n`-th
  moment base; with `n = N−1` it is the normalisation the post-substitution
  S-integral collapses to). Route as planned: `integral_rpow_mul_exp_neg_mul_Ioi`
  (`a = n+1`, `r = 1/2`) ⟹ `2^{n+1}·Γ(n+1)`, `Real.Gamma_nat_eq_factorial`,
  `ofReal`↔`lintegral` bridge — mirrors `lintegral_radial_const` (n=1). Foundational
  triple, AxiomAudit-pinned. (Stated as the moment `= 2^{n+1}·n!` rather than the
  normalised `= 1`, so the `(1/2)^N/(N−1)!` prefactor can be applied at assembly;
  cleaner than baking it in.) Friction: beta-redex blocking the integrand `rw`
  (fixed with explicit `show`), `-1 < ↑n` not a `positivity` goal (used
  `Nat.cast_nonneg` + `linarith`).

- **D.2 the diffeo `Ψ_N` + its `fderiv`/det — DONE 2026-06-01**
  (`MomentRatioUniformN.lean`, `PsiN`, `psiFDerivN`, `hasFDerivAt_PsiN`,
  `psiFDerivN_det`). `PsiN y = lastCases ((1−∑t)·S) (fun k => t k · S)` (`S = y last`,
  `t = y∘castSucc`). Candidate derivative `psiFDerivN y := (toLin' (psiMat S t)).toCLM`
  — so `psiFDerivN_det = (y last)^M` is *immediate* from D.3 via `LinearMap.det_toLin'`
  (the payoff of having isolated D.3 as a pure matrix lemma). `hasFDerivAt_PsiN`
  proved componentwise (`hasFDerivAt_pi`): each output coord is `.mul`/affine of
  `proj`s (`hasFDerivAt_apply`), and the produced derivative matches `(proj i).comp
  (psiFDerivN y)` (= `psiMat` row `i`) via `Matrix.toLin'_apply` + the row evaluation.
  Foundational triple, AxiomAudit-pinned. MED as planned; frictions: `proj` needs
  pinned `(R := ℝ)(φ := …)`, `.mul` derivative order, `HasFDerivAt.fun_sum` (not
  `.sum`) for the `fun x => ∑` form, `Finset.sum_neg_distrib` for the last-row algebra.
  Note D.4's `InjOn`/image is still owed (folded into D.2's plan slot but separate work).

- **D.2-orig The substitution diffeo `Ψ_N` and its inverse (original framing).**
  `Ψ_N : (Fin (N-1) → ℝ) × ℝ → (Fin N → ℝ)`,
  `(t, S) ↦ fun i => if h : i = last then (1 − ∑ t) · S else t (i.castPred) · S`
  (the "stick-breaking" parametrisation). Domain `openSimplex ×ˢ Ioi 0`, image the
  open quadrant `{s | ∀ i, 0 < s i}`. Inverse `s ↦ ((fun k => s (castSucc k) / ∑ s), ∑ s)`.
  **Decision to make at build time:** index management — whether to carry the
  `Fin (N-1)`/`Fin N` split via `Fin.lastCases`/`Fin.snoc` (clean recursion, the
  recommended route) or `Fin.castSucc`/`Fin.last` projections (more explicit, more
  `Fin` arithmetic). `Fin.snoc` is likely cleaner for both the map and its `fderiv`.
  **Risk: MED** — `Fin` bookkeeping, but no deep content.

- **D.3 the determinant `= S^M` — DONE 2026-06-01** (`MomentRatioUniformN.lean`,
  `psiMat` + `psiMat_col_sum` + `psiMat_det`). The gate is through. Encoded the
  Jacobian as an explicit `Matrix.of` bordered matrix `psiMat S t` (dim `M+1`,
  `N = M+1`) — `S·I` block, last col `t`/`1−∑t`, last row `−S`/`1−∑t` — using
  `Fin.lastCases` (which reduces cleanly under `simp`, verified). Proof exactly as
  planned: `psiMat_col_sum` (every column sums to `[j=last]`: `S+(−S)=0` on castSucc
  cols, `∑t+(1−∑t)=1` on the last) → row op via `Matrix.det_updateRow_sum` (coeff 1,
  det invariant) making the last row `e_last` → `twoBlockTriangular_det` (`p := ·≠last`)
  → corner block `1` (`det_eq_elem_of_subsingleton`) × big block `det (diagonal S)
  = S^M` (`Fintype.card_subtype_compl`). Foundational triple, AxiomAudit-pinned.
  **Came in cleaner than budgeted** (the planned-HIGH risk) by isolating it as a
  pure matrix lemma (no `fderiv`/CLM machinery) — that connection is now D.2's job
  (`LinearMap.det_toMatrix` linking `psiFDeriv_N` to `psiMat`). The original NUT
  framing follows.

- **D.3-orig `fderiv` and the determinant `= S^{N−1}` (THE NUT — original framing).**
  `HasFDerivAt Ψ_N (Ψ_N_fderiv (t,S)) (t,S)`, then `det = S^{N-1}`. The Jacobian (in
  the basis `(t_0,…,t_{N−2}, S)`) is the N×N matrix:
  - `∂(t_k S)/∂t_j = S·δ_{kj}`, `∂(t_k S)/∂S = t_k`   (rows `k < N−1`)
  - `∂((1−∑t)S)/∂t_j = −S`,     `∂((1−∑t)S)/∂S = 1−∑t` (last row)
  i.e. a **bordered matrix**: top-left `(N−1)×(N−1)` block `S·I`, last column
  `(t_0,…,t_{N−2}, 1−∑t)`, last row `(−S,…,−S, 1−∑t)`. Its determinant is `S^{N−1}`
  (add all first `N−1` rows scaled appropriately into the last, or cofactor on the
  last column; the `S·I` block gives `S^{N−1}` and the border contributes the
  `∑ t_k + (1−∑t) = 1` collapse). **This is the genuine theorem.** Options:
  (a) compute via `Matrix.det` of the explicit `updateRow`/`updateCol` form +
  `Matrix.det_succ_row_zero` cofactor expansion or a block-triangular argument;
  (b) recognise it as `S^{N−1}` times a rank-one update determinant
  (`Matrix.det_one_add_col_mul_row`-style). **Risk: HIGH** — this is the
  multi-session core; budget the bulk of Slice D here. No Mathlib lemma gives it
  directly; it is a genuine determinant computation.

- **D.4 `InjOn` + image — DONE 2026-06-01** (`MomentRatioUniformN.lean`, `domainN`,
  `posQuadrant`, `PsiN_sum`, `injOn_PsiN`, `image_PsiN`). `Ψ_N` is a bijection
  `domainN` (open simplex in free coords × `Ioi 0`) → `posQuadrant` (`∀ i, 0 < s i`).
  Crux `PsiN_sum : ∑ᵢ Ψ_N(y)ᵢ = y last` (the `(∑t)S + (1−∑t)S = S` cancel) drives
  both injectivity (sum recovers `S`, then `castSucc` coords cancel `S>0`) and the
  image inverse (`S := ∑ s`, `t_k := s(castSucc k)/S`; `∑ t < 1` because the omitted
  last term `s(last)/S > 0`). Foundational triple, AxiomAudit-pinned. **Built first
  try** (probe-first + close N=2 template). MED as planned.

- **D.5 Assemble — SCOPED, NOT YET BUILT (2026-06-01).** The recon for the
  assembly turned up **two missing Mathlib lemmas** that the qubit's `prod`-based
  D.5 got for free, so D.5 splits into three:
  - **D.5a — lintegral product over `Measure.pi` — DONE 2026-06-01**
    (`CsdLean4/Mathlib/MeasureTheory/LintegralFintypeProd.lean`, Cat-1):
    `lintegral_fin_nat_prod_eq_prod` (`Fin n`, by induction via
    `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`) and
    `lintegral_fintype_prod_eq_prod` (general index, transferred via `equivFin` +
    `measurePreserving_piCongrLeft.lintegral_comp_emb`). The `lintegral` analogue of
    the Bochner `integral_fintype_prod_eq_prod`, ported step-for-step. Foundational
    triple, AxiomAudit-pinned. Friction: `≥0∞` needs `open scoped ENNReal`;
    `lintegral_prod_mul` needed explicit `(μ:=)(ν:=)(f:=)(g:=)` + a beta-reduce
    (`simp only at hmul`) before matching; the recursion's `Fin.prod_univ_succ`
    binder alpha-equivalence closed via `exact hmul` (not `rw`).
  - **D.5b — the pi-withDensity bridge — DONE 2026-06-01**
    (`LintegralFintypeProd.lean`, `pi_withDensity`):
    `Measure.pi (fun i => (μ i).withDensity gᵢ) = (Measure.pi μ).withDensity
    (fun x => ∏ᵢ gᵢ(xᵢ))`, the pi analogue of `prod_withDensity` (absent from Mathlib).
    Proof: `Measure.pi_eq` on rectangles → `withDensity_apply` both sides → rewrite
    the rectangle set-integral as `∫⁻ ∏ᵢ (sᵢ.indicator gᵢ)` (the indicator-product
    identity) → factor by D.5a → match `∏ᵢ ∫_{sᵢ} gᵢ`. Foundational triple,
    AxiomAudit-pinned. Friction: `withDensity_apply` (not `Measure.`-prefixed),
    `pi_eq` orientation (no `.symm`), `classical` for the indicator `split_ifs`,
    `Set.mem_univ_pi` unfolding. Carries an explicit
    `[∀ i, SigmaFinite ((μ i).withDensity gᵢ)]` (withDensity isn't auto-σ-finite for
    general `ℝ≥0∞` densities — discharged at the D.5c callsite via `expHalf` finiteness).
    (Both D.5a/D.5b are genuine Cat-1 Mathlib-gap contributions.)
  - **D.5c — the assembly proper — DONE 2026-06-01** (`MomentRatioUniformN.lean`,
    `ratioSqNorm_map_expHalf_pi`). **Closes Slice D.** `Measure.ext_of_lintegral` →
    `lintegral_map` → expose joint density (D.5b `pi_withDensity`, σ-finite from
    `expHalf` prob) → restrict to `posQuadrant` (`image_PsiN`) →
    `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (`hasFDerivAt_PsiN` +
    `psiFDerivN_det = S^M` + `injOn_PsiN`) → reindex `domainN` as `e ⁻¹' (Ioi 0 ×ˢ
    openSimplexFree)` via `piFinSuccAbove (last M)` (the structurally-novel step; the
    qubit had `ℝ×ℝ` free) → `setLIntegral_comp_preimage_emb` + `setLIntegral_prod`
    (Tonelli) → pull the radial factor out of the inner simplex integral
    (`lintegral_const_mul`) → outer `S`-integral = `M!` via D.1
    (`lintegral_radial_moment`: `∫ S^M e^{-S/2} = 2^{M+1} M!`, times `(1/2)^{M+1}`)
    → `M! • vol.restrict` via `lintegral_smul_measure` + `smul_eq_mul`. Foundational
    triple, AxiomAudit-pinned. The longest proof in the slice (the assembly threads
    all seven D-ingredients); many small bookkeeping frictions (eta, `Decidable`,
    `Finset.sum_neg_distrib`, `Pi.mul` folding, `setLIntegral_comp_preimage_emb`
    direction) but no math unknowns — every sub-fact was probe-verified first.

  **SLICE D COMPLETE.** `ratioSqNorm_map_expHalf_pi` (the general-N Dirichlet law)
  is proved, foundational-triple, AxiomAudit-pinned. Remaining for the programme:
  Slice E (compose B+C+D → `fs_moment_joint_dirichlet_N`; lift `born_eq_volume_ratio`
  to FS-volume on Σ for general N).
  **Target:** `ratioSqNorm_map_expHalf_pi : Measure.map ratioN (Measure.pi (fun _ =>
  expHalf)) = (M.factorial : ℝ≥0∞) • volume.restrict (openSimplexFree)` where
  `ratioN s k = s(castSucc k)/∑s`, `openSimplexFree = {t : Fin M → ℝ | (∀ k, 0<t k)
  ∧ ∑ t < 1}`. (N=2 = `ratioSqNorm_map_expHalf_prod`, `M=1`, `1! = 1`, Uniform.)
  D.1–D.4 (incl. the research-grade gate D.3) are all banked; D.5 is the remaining
  measure-theoretic plumbing, gated on the two standard-but-missing pi lemmas above.

### Honest budget

D.3 (the determinant) is the research-grade theorem and the single largest risk —
plausibly a session by itself. D.1/D.2/D.4/D.5 are MED-risk generalisations of
existing N=2 lemmas (real work, but the shape is known). Recommended order:
D.1 (warm-up, near-mechanical) → D.3 (the determinant, the gate) → D.2/D.4 (diffeo
+ inj/image) → D.5 (assembly). If D.3 stalls, the whole slice stalls, so attack it
early and consider proving the determinant identity standalone first.

### Slice E (assembly to the Born result) — DONE (2026-06-02)

**Headline `fs_moment_joint_dirichlet_N`** (`MomentDirichletN.lean`):
`(ratioN ∘ momentMap)∗ μ_FS = M! · vol|_{openSimplexFree}` on `ℂℙ^M`, the joint
Dirichlet(1,…,1) law. Assembly: `gaussianCPN_eq_fubiniStudy` (Slice B) +
`map_pi_eq_stdGaussian` (Mathlib) + the product-index curry bridge
`blockSqNormCurry_map_pi` (`MomentBridgeN.lean`, E1/E2 — **bypasses Slice C**,
landing directly on `Exp(1/2)^{⊗N}` via `map_curryProd_pi` + `Measure.pi_map_pi`) +
Slice D `ratioSqNorm_map_expHalf_pi` + the a.e.-off-`{0}` normalised-vs-unnormalised
ratio identity.

**New Cat-1 gap** (`Mathlib/MeasureTheory/PiCurry.lean`): `measurePreserving_piCurry`
/ `map_curryProd_pi` — currying a sigma/product index preserves `Measure.pi`. Mathlib
proves `piCurry` measurable but had no measure-preserving statement. Proved via
`pi_eq_generateFrom` on the box-of-boxes π-system. Third Cat-1 gap of the programme
(after the D.5a/D.5b lintegral-Fubini lemmas). Upstream candidate.

**Born lift** (`MomentBornN.lean`), all **unconditional** (the qubit `h_uniform` is
now the proved headline):
- `fs_volume_eq_dirichlet` (E4a): the DH volume law on Σ — `μ_FS` of a measurable
  moment region `R ⊆ openSimplexFree` = `M! · vol(R)`.
- `volume_openSimplexFree` (E4b): the free simplex has volume `(M!)⁻¹` (forced by
  `μ_FS` being a probability measure).
- `fs_born_volume_ratio_N` (E4c): for each free coordinate `i : Fin M`, the FS measure
  of the `i`-th barycentric region (`replaceMap`, pulled back through the moment map)
  = the Born weight `‖⟨e_{castSucc i}, ψ⟩‖²`. Region is the homeomorphic image of the
  open simplex (`det = bᵢ ≠ 0 ⇒ open ⇒ measurable`) and stays inside (interior-point
  subdivision).

**Apex coordinate CLOSED (2026-06-02).** `fs_born_volume_ratio_N_apex`
(`MomentBornN.lean`) handles the dropped apex (index `M`) via the affine apex map
`A(x) = L(x) + b'`, `L(x) = x − (∑x)•b'`, with `det L = 1 − ∑b' = b_M`
(`apexLin_det` via `Matrix.det_one_sub_mul_comm`: `b` as a column, `𝟙` as a row).
Translation-invariance (`measure_preimage_add_right`) + `addHaar_image_linearMap` give
the region volume `b_M·(M!)⁻¹`, collapsing to the Born weight `‖⟨e_{last M},ψ⟩‖²`.
**Together with `fs_born_volume_ratio_N` this covers all `N` of `N` coordinates** (the
qubit gave 1 of 2). Genericity hypothesis: `ψ` has no vanishing amplitude.

All foundational-triple-only; AxiomAudit-pinned; both `lake build` targets green.
**The general-N Born-from-Kähler-volume programme is geometrically total.**

**Empirical capstone DONE (2026-06-02).** `born_frequency_convergence_N`
(`BornFrequencyN.lean`): i.i.d. trials from `μ_FS` on `ℂℙ^M`, the empirical frequencies
of the `N` barycentric Born regions (`bornRegion`, `Fin.lastCases` of the `replaceMap`
free regions + the affine apex region) converge **jointly** a.s. to the Born weights
`‖⟨eᵢ,ψ⟩‖²`. One-line application of `born_frequency_convergence_partition`
(`LF1.freq_tendsto_of_iid` per index), with `hborn` from `fs_born_volume_ratio_N`/`_apex`
and `hmeas` from the open-image lemmas. **Foundational-triple-only — NO
`busch_effect_gleason`** (contrast the LF3 chain capstones). The general-N analogue of
`qubit_born_frequency_convergence_uncond`; the headline empirical payoff: deterministic
LF1 typicality + Born = Kähler volume ⟹ frequencies → Born, Born derived from the
symplectic geometry, not imported via Gleason.
