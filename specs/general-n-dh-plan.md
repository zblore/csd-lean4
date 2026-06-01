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
