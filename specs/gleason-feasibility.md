# Gleason's theorem, finite-dimensional — feasibility pass (2026-09-21)

**Brief:** the one-week spec of 2026-09-21 (owner: Zayn Blore): state the finite-dimensional
projection form of Gleason's theorem in the Mathlib-only tree, prove the cheap layers (A:
reductions, C: descent), refactor Busch's proof through the shared lemma, size the core lemma on
`S²` against Cooke–Keane–Moran, and return a go/no-go with a sized plan.

**Status wording (binding until the last `sorry` is gone):** *finite-dimensional Gleason,
reductions and descent proved, core lemma open.* Nothing in code, docs or ledger claims the
theorem.

**Where things are.** The proved layers are on `main`, sorry-free and gated
(`CsdLean4/Mathlib/Analysis/InnerProductSpace/Gleason/`, 38 AxiomAudit pins, foundational triple
only). The one `sorry` lives on the branch `gleason-feasibility`
(`Gleason/Core.lean`), so that `main` keeps its no-`sorry` invariant and the guards; the
axiom sweep on that branch is in §5.

---

## 1. The statement

Projections are `IsStarProjection` matrices (Mathlib's self-adjoint idempotents); a package is
a total function on matrices constrained only on projections:

```lean
structure Gleason.ProjectionPackage (N : ℕ) where
  p : Matrix (Fin N) (Fin N) ℂ → ℝ
  nonneg : ∀ P, IsStarProjection P → 0 ≤ p P
  total_one : p 1 = 1
  additive : ∀ P Q, IsStarProjection P → IsStarProjection Q → P * Q = 0 → p (P + Q) = p P + p Q
```

Target (`Reduction.lean`, proved from the core lemma; `Core.lean` on the branch, with the
`sorry`):

```lean
theorem Gleason.ProjectionPackage.gleason_representation_of_core (hcore : CoreLemma) (hN : 3 ≤ N)
    (OP : ProjectionPackage N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re
```

**Why this representation.** The matrix form makes A1 twenty lines: `IsStarProjection.add`
(Mathlib) is exactly the closure the additivity axiom needs, rank-one projections are
`vecMulVec v (star v)` with Mathlib's `vecMulVec` calculus, and the spectral resolution of a
projection is `Matrix.IsHermitian.eigenvectorBasis` with eigenvalues in `{0, 1}`. The
`Submodule`/`orthogonalProjection` form would have needed the correspondence
`orthogonalProjection (span (range b)) = ∑ rankOne (b i)` and an additivity statement about
`⊔` of orthogonal submodules — both absent from Mathlib at the pin. The density matrix is a bare
matrix with `PosSemidef ∧ trace = 1` rather than a structure, so the file imports nothing from
the CSD layers; `LF2/BornWrapper.lean` can package it as a `DensityOperator` in one line.

## 2. What is proved (all on `main`, sorry-free)

| Layer | File | Content | Lines |
|---|---|---|---|
| engine | `Gleason/Polarization.lean` | The Jordan–von Neumann reconstruction, **extracted verbatim from `LF2/EffectGleason.lean`** §§I–L: `IsQuadraticLike q` (degree-2 homogeneous, parallelogram, `0 ≤ q ≤ ‖·‖²`) ⇒ `polarMatrix q` Hermitian with `q v = ⟨v, R v⟩` (`IsQuadraticLike.eq_dotProduct`); `additive_bounded_linear` (Cauchy with a local bound, no continuity); `matrix_eq_zero_of_quadForm_zero`, `trace_mul_isHermitian_real`, `trace_mul_vecMulVec` | 470 |
| A1, A2 | `Gleason/ProjectionPackage.lean` | `rankOne`, `isStarProjection_rankOne`, `sum_rankOne_orthonormalBasis`, `p_sum` (additivity over any finite pairwise-orthogonal family), `frame v = p |v⟩⟨v|` with `frame_nonneg`, `frame_le_one`, `frame_smul` (phases), `sum_frame_orthonormalBasis = 1` (**A1**, `isFrameFunction_frame`); `realRestrict OP e : ℝᵏ → ℝ` and `isFrameFunction_realRestrict` (**A2**: for a complex-orthonormal `e : Fin k → ℂᴺ` the restriction is a real frame function of weight `p (∑ |eᵢ⟩⟨eᵢ|)`, via the Gram identity `E Bᵀ B Eᴴ = E Eᴴ`) | 380 |
| C | `Gleason/Descent.lean` | `posSemidef_of_sphere_nonneg`, `trace_eq_sum_sphere`, `eq_of_sphere_quadForm_eq`, packaged as **`quadraticForm_on_sphere_to_density`** (the lemma the spec asked for; Busch's proof now consumes it, §4); `Matrix.IsHermitian.eq_sum_eigenvalues_smul_rankOne`, `eigenvalues_eq_zero_or_one` (projections), `p_eq_re_trace` (spectral descent), ★★ `existsUnique_density_of_frame_quadratic` | 265 |
| A3 | `Gleason/FrameFunction.lean` | `IsRealPlaneRegular f` (regular on every completely real plane); `frame_add_frame_eq` (weight of a plane is basis independent); **`crossTerm_phase`** — on the equator pair `w = (x+y)/√2, w' = i(x−y)/√2` regularity forces `crossTerm f x (e • y) = β₁ Re e + β₂ Im e`; `frame_plane_unit`, `ext_plane` (Hermitian form on every complex plane); `ext_parallelogram` (Gram–Schmidt, parallelogram law on all of `ℂᴺ`); ★ **`exists_isHermitian_of_isRealPlaneRegular`** (A3); `exists_orthonormal_triple`, **`isRealPlaneRegular_of_triples`** (the bridge from what the core lemma gives on completely real `3`-spaces, `N ≥ 3`) | 626 |
| assembly | `Gleason/Reduction.lean` | `CoreLemma : Prop`; ★★ `gleason_representation_of_core` | 73 |

**A3 was done differently from the spec's outline and from CKM §1.** Gleason's §3 patching and
CKM's §1 lemma ("a state on a two-dimensional complex space that is regular on every
completely real subspace is regular") both go through a maximiser on the sphere and a
compactness/subsequence argument. The Lean proof avoids all of that: for an orthonormal pair
`(x, y)` the values `f(αx + β e^{iφ} y)` are pinned by the completely real planes
`span_ℝ{x, e^{iφ}y}` (the "meridians"), and the single completely real plane
`span_ℝ{(x+y)/√2, i(x−y)/√2}` (the "equator" — its real unit circle is exactly
`{(x + e^{iφ}y)/√2}`) forces the cross term to be a first-degree trigonometric polynomial in
`φ`. That makes `f` a Hermitian form on every complex plane, hence the degree-2 extension obeys
the parallelogram law on `ℂᴺ`, and the Jordan–von Neumann engine already built for Busch
finishes. No compactness, no maximiser, no square roots except one unit square root
(`Complex.cpow_nat_inv_pow`). This is the reason the reductions took a day rather than the
spec's two.

**A4 (real `N ≥ 3` from real `3`) was not built and is not on the path.** The complex theorem
needs regularity on completely real *planes*, and every plane sits in a completely real
`3`-space (`exists_orthonormal_triple`), so the core lemma is consumed directly. A4 is the
reduction for a *real* Hilbert space corollary; priced S–M (the three-vector argument: any
`u, u', v` lie in a `3`-space, so the polarisation `B(u,v) = (F(u+v) − F(u−v))/4` is bilinear
without any Cauchy equation). BACKLOG #58.

## 3. Busch's proof re-routed (spec task 2)

`LF2/EffectGleason.lean` lost §§I–L (≈450 lines, moved unchanged to `Polarization.lean` as the
generic engine) and now reads `qform_isQuadraticLike`, `qmatrix := Gleason.polarMatrix qform`,
`qmatrix_isHermitian`/`qform_eq_dotProduct` from the engine; `qmatrix_posSemidef` goes through
`Gleason.posSemidef_of_sphere_nonneg` and `qdensity_unique` through
`Gleason.eq_of_sphere_quadForm_eq` (the sphere half of `quadraticForm_on_sphere_to_density`;
the trace-one half keeps its one-line proof from `p_eq_trace Effect.one`). Consumers
(`PreparationBarycenter`, `TensorTomography`) now name `Gleason.trace_mul_isHermitian_real`;
`trace_mul_outerProduct` stays in LF2 as the `outerProduct` wrapper.
`effect_gleason_representation` is unchanged in statement and still foundational-triple
(AxiomAudit, `check-gleason-free`, `check-import-negative` all green).

## 4. What is `sorry` (branch `gleason-feasibility` only)

`Gleason/Core.lean`:

```lean
theorem Gleason.frameFunction_regular_sphere (f : EuclideanSpace ℝ (Fin 3) → ℝ) {W : ℝ}
    (hf : IsFrameFunction ℝ f W) (h0 : ∀ x, ‖x‖ = 1 → 0 ≤ f x) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧ ∀ x, ‖x‖ = 1 → f x = ⇑x ⬝ᵥ (A *ᵥ ⇑x) := by
  sorry
theorem Gleason.coreLemma : CoreLemma := ...                      -- from the sorry
theorem Gleason.ProjectionPackage.gleason_representation ...      -- from coreLemma
```

Axiom sweep on the branch (`lake env lean`, `#print axioms`):

| Declaration | Axioms |
|---|---|
| `Gleason.frameFunction_regular_sphere` | `propext, sorryAx, Classical.choice, Quot.sound` |
| `Gleason.coreLemma` | `propext, sorryAx, Classical.choice, Quot.sound` |
| `Gleason.ProjectionPackage.gleason_representation` | `propext, sorryAx, Classical.choice, Quot.sound` |
| `Gleason.ProjectionPackage.gleason_representation_of_core` | foundational triple |
| `…exists_isHermitian_of_isRealPlaneRegular`, `…isRealPlaneRegular_of_triples`, `…existsUnique_density_of_frame_quadratic`, `…isFrameFunction_realRestrict`, `Gleason.quadraticForm_on_sphere_to_density`, `Gleason.IsQuadraticLike.eq_dotProduct` | foundational triple |

**Exactly one `sorry`**, the core lemma; the theorem depends on nothing else. (The corpus sweep
`scripts/check-axiom-sweep.sh` walks `CSD.*` declarations only, so it does not see the `Gleason`
namespace; on the branch the two `sorryAx` results are pinned explicitly in
`Tests/AxiomAudit/MathlibStaging.lean`, and on `main` all 38 Gleason pins are foundational-triple.)

## 5. Layer B, sized against Cooke–Keane–Moran (spec task 4)

Source: R. Cooke, M. Keane, W. Moran, *Math. Proc. Cambridge Philos. Soc.* **98** (1985)
117–128 — obtained from Cooke's site (a scan, read page by page; the copy is at
`export/fc5/ckm.pdf`, git-ignored). The spec's outline B1–B4 was **not** the paper's structure;
the table below is. CKM's own §1 (reduction to `ℝ³`) is superseded by §2 above.

Notation: `S` the unit sphere of `ℝ³`; a *frame* is an orthonormal triple; a *frame function*
has `f(p)+f(q)+f(r) = w(f)` on every frame (our `IsFrameFunction ℝ f W`); `p` the north pole,
`l(s) = ⟪p, s⟫²` the latitude, `E = p^⊥ ∩ S` the equator, `N` the northern hemisphere,
`s^⊥` the "coldest" unit vector orthogonal to `s` (`l(s) + l(s^⊥) = 1`, explicitly
`(p − ⟪p,s⟫ s)/‖·‖`), `D_s = {t ∈ N : t ⟂ s^⊥}` the *descent* through `s` (the great circle
with `s` as its northernmost point).

| # | CKM | Lean statement | Mathlib assets | Missing | Lines | Risk |
|---|---|---|---|---|---|---|
| B0 | §2 P1–P4: frame functions form a vector space, `f(−s) = f(s)`, the four-point identity on a great circle (`s ⟂ t, s' ⟂ t'` on one great circle ⇒ `f s + f t = f s' + f t'`), P4 (`f s > M − ξ` ⇒ ∃ `t ⟂ s`, `f t < m + ξ`); boundedness | `IsFrameFunction ℝ f W`; `frame_neg`; `four_point (w : unit normal) (hs : s ⟂ w) …`; `exists_orth_lt_inf_add`; `0 ≤ f ≤ W` from nonnegativity + the frame identity (so *bounded* is free for our `h0`) | `Orthonormal`, `OrthonormalBasis (Fin 3)`, `orthonormal_iff_ite`, `crossProduct` (`Mathlib.LinearAlgebra.CrossProduct`: `dot_self_cross`, `cross_dot_cross`, `norm` via `cross_dot_cross`) for completing a pair to a frame | a "complete an orthonormal pair of `ℝ³` to a frame" lemma (`![s, t, s ×₃ t]`), `sSup`/`sInf` of `f` on the sphere (`Real.sSup` with `BddAbove`) | 250 | low |
| B1 | §3 Warmup I: bounded `f : [0,1] → ℝ` with `f a + f b + f c` constant on `a+b+c = 1` is affine. Warmup II: `f` on `[0,1] \ C`, `C` countable, `f 0 = 0`, monotone, `f a + f b + f c = 1` on `a+b+c=1` ⇒ `f a = a` | `affine_of_sum_const_bounded`; `eq_id_of_monotone_sum_eq_one (hC : C.Countable)` | `additive_bounded_linear` (ours, Cauchy + local bound); `Set.Countable`, an uncountable interval (`Cardinal.not_countable_real` / `Set.Ioo` uncountable) to pick `a₀ ∉ C̃`; `Rat.denseRange_cast`, `exists_rat_btwn` | the "rational multiples of a countable set are countable" bookkeeping; the monotone squeeze | 350 | low |
| B2 | §4 Basic lemma: `f p = sup f`, `f` constant on `E` ⇒ `f s ≥ f s'` for `s' ∈ D_s`; approximate version (`f p > sup − ξ` ⇒ `f s > f s' − ξ`) | `descent_le (hp : IsMaxOn f S p) (hE : ∀ e ∈ E, f e = m) (hs' : s' ∈ D_s) : f s' ≤ f s`; `descent_lt_add` | `crossProduct` for the equator point `t ⟂ s, t ⟂ s^⊥` and `t' ⟂ s'` on `D_s`; `inner`, `real_inner_self_eq_norm_sq` | latitude/`s^⊥`/`D_s` definitions and their algebra (all elementary but coordinate-heavy) | 300 | medium |
| B3 | §5 Geometric lemma (Piron): `l s > l t` (both in `N \ {p}`) ⇒ finite chain `s = s₀, …, sₙ = t` with `sᵢ ∈ D_{sᵢ₋₁}`. Proof by gnomonic projection: descents become tangent lines to latitude circles; same ray: two steps; general: a spiral of `n` steps of angle `π/n` with radius ratio `(cos π/n)⁻ⁿ → 1` | `exists_descent_chain (hl : l t < l s) : ∃ n (c : Fin (n+1) → S), c 0 = s ∧ c n = t ∧ ∀ i, c (i+1) ∈ D_{c i}`; formalise the tangent plane as `ℂ` (`π s = (s − ⟪p,s⟫p)/⟪p,s⟫` read in an orthonormal basis of `p^⊥`), descent = `{z : Re (z · conj (π s)) = ‖π s‖²}`, the spiral explicitly `zₖ = π s · (cos φ/n)⁻ᵏ e^{ikφ/n}` | `Complex.exp`, `Complex.abs_exp_ofReal_mul_I`, `Real.one_sub_sq_div_two_le_cos`, `one_add_mul_le_pow` (Bernoulli), `Real.cos_pos_of_mem_Ioo`, `OrthonormalBasis` of `p^⊥` (`Submodule.orthogonal` + `stdOrthonormalBasis`) | the gnomonic dictionary (`t ∈ D_s ↔ Re (π t · conj (π s)) = ‖π s‖²`), the two-step same-ray construction, the limit `(cos φ/n)⁻ⁿ → 1` (from `cos x ≥ 1 − x²/2` and Bernoulli) | 600 | **medium-high** — the one step with no Mathlib support; the explicit spiral removes the geometry, leaving analysis of `cos` |
| B4 | §5 Theorem (simple frame functions): `f p = sup f`, `f = m` on `E` ⇒ `f s = m + (M−m) l(s)`. Proof: monotone in latitude (B2+B3); `f̄(l), f̲(l)` sup/inf on parallels; the exceptional set `C = {l : f̄ l > f̲ l}` is countable; frames with prescribed latitudes `l+l'+l'' = 1`; Warmup II; `C = ∅` | `eq_latitude_of_isMaxOn`; `exists_frame_of_latitudes (h : l + l' + l'' = 1) : ∃ frame, …`; `monotone_parallel_sup` | `Monotone.countable_not_continuousAt` (the countability of the jump set of a monotone function — exactly the "`∑ (f̄ − f̲) ≤ 1`" step), `sSup`/`sInf` on parallels (`Real.sSup_le`, `le_csSup`) | the frame-with-prescribed-latitudes construction (explicit: `q = (√l, √(1−l), 0)`-type vectors in a frame through `p`, then a rotation about `p`) | 500 | medium |
| B5 | §6 Extremal values: a bounded frame function attains `sup` and `inf`. Proof: `pₙ → p` with `f pₙ → M`; rigid motions `ρₙ` taking `p ↦ pₙ`; symmetrise `hₙ s = gₙ s + gₙ (p̂ s)` (`p̂` = 90° rotation about `p`) so each `hₙ` is constant on `E`; **Tychonoff**: `[2m, 2M]^S` compact in the product topology, an accumulation point `h` is a frame function with `h p = 2M = sup h`, constant on `E`, hence (B4) of the special form; the approximate basic lemma + the two-step geometric lemma give `f p > M − ε` | `exists_isMaxOn_sphere (hf) (hb : bounded)`; the symmetrisation `frame_add_rot`; `frameFunctions_isClosed`; a cluster point via `IsCompact.exists_clusterPt` (not sequences: the product is not sequentially compact) | `Pi.compactSpace`/`isCompact_univ_pi` (Tychonoff), `IsCompact.exists_clusterPt`, `isClosed_iInter`, `continuous_apply`, `Metric.sphere` compact (`isCompact_sphere`), `Matrix.specialOrthogonalGroup`/`Orientation.rotation` for `ρₙ` and `p̂` | rigid motions `ρₙ` with `ρₙ p = pₙ` and `ρₙ cₙ = p` (a rotation in the plane of `p, pₙ`: build it in `ℂ`-coordinates of that plane), the cluster-point extraction of the four properties | 550 | **medium-high** — filters and rotations; every ingredient exists but none is assembled |
| B6 | §7 General case: `f p = M`, `f r = m` (`r ⟂ p`), `q ⟂ p, r`, `f q = α`, `m < α < M`; `f + f∘p̂` is constant on `E` and attains `2M` at `p`, so B4 gives `f s + f (p̂ s) = g s + g (p̂ s)` for the target form `g = M x² + α y² + m z²`; likewise with `r̂`; the Claim `f = g` on the six great circles `x = ±y, x = ±z, y = ±z` (compose the 90° rotations); `h = g − f` is a frame function of weight `0` vanishing on those circles; if `h ≠ 0` apply B5/B4 to `h` at its own extremes `p', r'`, steps (i)–(iv): `M' = −m'`, `α' = 0`, `h(x',x',z') = M'(x'² − z'²)`, and a great circle through four of the zero points must be `y = z`, contradiction | `frameFunction_regular_sphere` itself; `rot_p, rot_q, rot_r` as explicit signed permutations in frame coordinates; `eq_on_six_circles`; `great_circle_through_four_points` | `EuclideanGeometry`/`Orientation` for the three 90° rotations (or explicit `!![…]` matrices), `Matrix.IsSymm`, `Finset` counting of intersection points | the intersection-counting of great circles ("a great circle meets another in exactly two points", "only one great circle through these four points") — elementary but nothing in Mathlib is phrased this way | 800 | medium |

**Total: ≈ 3,000 lines** (spec's estimate 3,000–6,000), of which the risk sits in B3 and B5.
The two places where Mathlib has nothing: (i) any spherical-geometry vocabulary — great
circles, latitude, descents, "a great circle through these points" (we would model the tangent
plane as `ℂ` and great circles as unit normals, and prove the handful of intersection facts by
coordinates); (ii) the assembly of Tychonoff + cluster point + closedness for a sequence of
functions on the sphere (each piece exists; the extraction is bespoke). A third near-gap:
frames with prescribed latitudes and rotations moving a given point to the pole (Mathlib has
`Orientation.rotation` in oriented `2`-spaces and `Matrix.specialOrthogonalGroup`, neither
with the "rotation taking `u` to `v`" API we need — we would build them in the complex
coordinates of the plane `span{u, v}`).

**Cheaper alternatives checked.** Gleason's own §2 (spherical harmonics: the continuity of a
frame function via the representation theory of `O(3)`) is out — Mathlib has no spherical
harmonics. Richman–Bridges (1999, constructive) is structurally CKM with the suprema replaced by
approximate suprema; it would remove B5's Tychonoff step at the cost of ε-management
throughout; not cheaper in Lean. Bell's / Piron's extreme-case proofs (`f` attains `1`) are B0–B4
only, and are exactly what the spec's "bank what is cheap" would land first.

## 6. Recommendation: **go, in stages** (spec task 7)

Not "no": every step is elementary, the paper is in hand, and the reductions took a day
instead of two. Not an unconditional "go": B3 and B5 are the two places the effort could double,
and both are early enough in the chain to be probes. The staged plan, each stage a numbered
queue row that lands green on `main` on its own:

| Stage (BACKLOG #57) | CKM steps | Content | Lands as | Price |
|---|---|---|---|---|
| 57(a) | B0 + B1 | frame-function basics on `S²`, the two warmup theorems | `Gleason/Sphere.lean`, `Gleason/Warmup.lean`, pins; nothing about Gleason claimed | **S–M** |
| 57(b) | B3 | Piron's geometric lemma with the explicit spiral — **the probe**: if it lands in ≤ 600 lines the rest is bookkeeping; the decision point | `Gleason/Descent.lean`'s sibling `Gleason/Piron.lean` | **M** |
| 57(c) | B2 + B4 | basic lemma, the simple-frame-function theorem (Bell/Piron's extreme case, a result in its own right: "a frame function attaining its supremum and constant on the equator is `m + (M−m) cos²θ`") | `Gleason/SimpleFrame.lean` | **M** |
| 57(d) | B5 | extremal values attained (Tychonoff) | `Gleason/Extremal.lean` | **M–L** |
| 57(e) | B6 | the general case; `frameFunction_regular_sphere` proved; `Core.lean` merges to `main` without its `sorry`; `gleason_representation` becomes a theorem | `Gleason/Core.lean` | **L** |

At the corpus's rate (the reductions: ≈1,800 lines in a day, but those were algebra) stage 1 is a
day, stage 2 two to three days, stages 3–5 a week to ten days together: **two and a half to
three weeks** for the whole of Layer B, with the decision point after 57(b). Real-space
corollary (A4) is a separate S–M row (#58) after stage 57(e).

## 7. Deviations from the brief, stated

* The spec asked for the `sorry`-carrying statement "with exactly the named gaps left as sorry
  at the end of the week". The repository's standing rules (no `sorry` on `main`, `--wfail`,
  the axiom sweep) would break on `main`, so the `sorry` file is on the branch
  `gleason-feasibility` and `main` carries the conditional theorem
  `gleason_representation_of_core` with `CoreLemma` as an explicit hypothesis. Same
  information, guards intact.
* The sizing table follows the paper's sections, not the brief's outline; where they differ
  (B1 is the warmup theorems, not boundedness; continuity is not a separate step — CKM never
  prove continuity of `f`, they prove monotonicity in latitude and use the countable exceptional
  set) the paper wins, as instructed.
* A3 was proved by a different, shorter argument than Gleason's (§2 above); the statement is
  Gleason's.
* Nothing external was done: no Zulip, no PR, no 1000-list entry, no push of the branch beyond
  the author's own repository.

## 8. References

Gleason 1957, *J. Math. Mech.* **6**, 885–893. Cooke, Keane, Moran 1985, *Math. Proc. Cambridge
Philos. Soc.* **98**, 117–128. Richman, Bridges 1999, *J. Funct. Anal.* **162**, 287–312.
Busch 2003, `quant-ph/9909073` (the effect version, `LF2/EffectGleason.lean`). Piron 1976,
*Foundations of Quantum Physics* (the geometric lemma). The 1000+ theorems list
(`leanprover-community/1000`, Wikidata Q5567394): no formalisation of Gleason's theorem in any
proof assistant as of 2026-09-21.
