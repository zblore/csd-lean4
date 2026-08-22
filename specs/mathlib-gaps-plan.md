# Mathlib-gaps review — triage and attack plan (MG arc)

Created 2026-08-22, on the Q16 lesson: **wall labels rot**. Every "genuine absence" row in
`MATHLIB-GAPS.md` was re-checked at the current pin before this plan was written. Companion:
`MATHLIB-GAPS.md` (the ledger this triages), `specs/BACKLOG.md` (the canonical queue; this
plan's rows are indexed there as MG-1..5).

## Wall-rot probe results (2026-08-22, at the pin)

| Row | Probe | Verdict |
|---|---|---|
| Birkhoff pointwise ergodic | `Dynamics/BirkhoffSum/` has the sums/averages ALGEBRA only; `Dynamics/Ergodic/` has no pointwise theorem | **Wall stands.** Leave (BornFromFlow keeps the strong-law route) |
| Lévy / spherical isoperimetry | `Probability/Moments/SubGaussian.lean` exists, but nothing supplies the isoperimetric/log-Sobolev input | **Wall stands.** Leave (Q24's Chebyshev tier is the delivered polynomial substitute) |
| `CStarAlgebra` on matrices | `instCStarAlgebra : CStarAlgebra (CStarMatrix n n A)` **EXISTS at the pin** (`CStarMatrix.lean:826`); the recorded failure is discrimination-tree RESOLUTION (repeated-index key blocks `Fintype`/`DecidableEq` synthesis — `OperatorConvexBridge.lean`'s B-notes) | **Soft wall — probe-first.** MG-3 below |
| Analytic/polynomial null sets | `Analysis/Analytic/{IsolatedZeros,Uniqueness}.lean` carry `eqOn` results only; no measure-zero statement anywhere | Wall stands upstream — **but the lemma is buildable in-corpus** (MG-2) |
| FS metric on `ℙ` | Mathlib has no `dist` on `Projectivization` — but nothing blocks US staging one on the already-staged topology | **Not a wall at all.** MG-1 |
| Kronecker spectral; invariant Gaussian | — | Already worked around / dissolved; ledger rows accurate |
| Stone general; Bargmann; Wigner §13; manifold-Kähler global half | — | Genuine / paused / XL — leave as recorded |

## The attack rows

### MG-3 (S probe, then L programme gated on it) — the CStarMatrix resolution probe → the DPI ladder

The single biggest payoff in the ledger. Probe (Q26-probe pattern, a scratch file at the
root): does the pin now resolve `CStarAlgebra (CStarMatrix n n ℂ)` + `NonnegSpectrumClass` +
`CFC.rpow` WITHOUT `OperatorConvexBridge.lean`'s local shim? If YES: resume the Löwner ladder
(`OperatorConvex.lean` rungs → `log`/`x^p` interior rungs → Lieb concavity → joint convexity
of relative entropy → **DPI** → **unconditional SSA**), retiring `StrongSubadditivity.lean`'s
explicit `hDPI` hypothesis and eventually the bridge file itself. If NO: record the probe
output in the gap row (upgrading "discrimination-key failures" to a dated, reproducible
witness — the shape an upstream instance-hygiene issue needs anyway) and stop.

> **PROBE EXECUTED 2026-08-22** (`scratch_mg3_probe.lean` at the root, five rounds — the
> resume seed until B.4 lands). Verdict, sharper than either branch anticipated:
>
> 1. `CStarAlgebra` / `PartialOrder` / `StarOrderedRing` on `CStarMatrix n n ℂ` all RESOLVE
>    at the pin (round-1 "failures" on these were noncomputable-compilation noise).
> 2. The wall is **exactly two non-firing generic instances**, each provable by a one-line
>    application of its own generic provider: `ContinuousFunctionalCalculus ℝ … IsSelfAdjoint`
>    (the bridge's existing shim) and `NonnegSpectrumClass ℝ …`
>    (`CStarAlgebra.instNonnegSpectrumClass` — the second shim the bridge does not yet have).
> 3. With BOTH shims registered, the **entire upstream monotonicity tier fires on
>    `CStarMatrix n n ℂ`**: `CFC.monotone_nnrpow` + `CFC.monotone_rpow` (operator
>    monotonicity of `x^p`, `p ∈ [0,1]` — which now EXISTS upstream,
>    `…/Rpow/Order.lean`, postdating the gap row), `CFC.monotone_sqrt`, `CFC.rpow`,
>    `CFC.log_le_log` (this last needs only shim 1).
> 4. The bare-`Matrix` side ℝ≥0-CFC fires already (scoped `MatrixOrder`), so `A ^ p`
>    (`p : ℝ≥0`) elaborates on the `Matrix` carrier — only the ORDER lemma needs transporting.
>
> **Re-rating.** The "rpow wall" of `OperatorConvexBridge.lean` is now an **M brick (B.4)**:
> register shim 2, prove the ℝ≥0-CFC naturality across `e` (the `map_cfc`/`map_cfcₙ` shape of
> B.1), transport `monotone_nnrpow` to `Matrix.rpow_le_rpow` on the Löwner order (+ sqrt as a
> corollary), supersede the honest-scope paragraph. The **DPI/SSA prize is NOT unlocked by
> instances alone**: operator CONVEXITY (Lieb) is still absent upstream (their own TODO list
> in `Rpow/Order.lean`), but upstream's new `Rpow/IntegralRepresentation.lean` supplies the
> integral-representation machinery the convexity rungs would consume — the L programme is
> better-provisioned than when the ladder was parked. Upstream note: the two-instance witness
> is the crisp reproduction an instance-hygiene issue/PR needs.
>
> **B.4 LANDED same day 2026-08-22** (`OperatorConvexBridge.lean` extended in place, first-try
> compile; 3 pins in the MathlibStaging part): `instCStarMatrixNonnegSpectrumClass` (shim 2),
> `cstar_cfcₙ_nnreal` (ℝ≥0-`cfcₙ` naturality across `e`, via
> `NonUnitalStarAlgHomClass.map_cfcₙ`), ★ `matrix_nnrpow_le_nnrpow` (`x^p` operator monotone,
> `p ∈ [0,1]`, Löwner order, on the BARE `Matrix` carrier's own `^` notation — the `p = 0`
> junk-value case branched, `p ≠ 0` zero-preserving pointwise), `matrix_sqrt_le_sqrt`. The
> rpow-wall paragraph superseded at source; `operator-convexity-plan.md` L.3 note updated.
> The probe file has served and is deleted; its content is reproduced by the shims + this
> record. MG-3's residue = the L.3a interior CONCAVITY assembly (Lieb direction), now with
> upstream's integral-representation machinery as input — still the ladder's open rung.

### MG-1 (M) — the Fubini–Study metric on `ℙ`, in-corpus

Kills a ledger row with no upstream dependency, and is a prime Mathlib candidate (there is no
metric on `Projectivization` anywhere). Route that makes every metric axiom free: embed
`p ↦ P_p` (the rank-one projection onto the line, well-defined and injective), set
`dist p q := ‖P_p − P_q‖`; symmetry/triangle/zero-iff come from the norm and injectivity. The
work is the TOPOLOGY AGREEMENT: `p ↦ P_p` is continuous off the staged quotient topology, `ℙ`
is compact (staged), the target is Hausdorff, so the map is a homeomorphism onto its image and
the induced metric topology IS the quotient topology (`MetricSpace` via the induced/replace
idiom). Unlocks: the quantified ε-ball forms of the C2 arc (Q28's "every ε-ball around a
product ray", "states closer than 2ε have overlapping ε-preparations"). Home:
`Mathlib/LinearAlgebra/Projectivization/Metric.lean` (staged, Cat-1).

> **EXECUTED 2026-08-22, same day** (`Projectivization/Metric.lean`, 4 pins; two build
> rounds — the only real error was `lift_mk`'s argument count; the notation open
> `LinearAlgebra.Projectivization` was the other). Delivered exactly as routed:
> `rankOneProj` (+ scale invariance via `RCLike.conj_mul` + `field_simp`, self-application,
> `normSq_coe_ne_zero`), `toProjCLM` by `Projectivization.lift`, continuity through the staged
> `continuous_lift` (the bounded-bilinear `smulRightL` + `innerSL` route), injectivity by
> applying equal projections to a representative (`mk_eq_mk_iff'`), ★
> `isClosedEmbedding_toProjCLM` (compact→Hausdorff), the `instMetricSpace` via
> `Topology.IsEmbedding.comapMetricSpace` (topology definitionally the staged quotient
> topology — no diamond), and `dist_eq`. `CPN N` inherits the instance with no further work.
> The C2 ε-ball corollaries are the recorded follow-up (a Q28 rider, not this brick). The
> ledger row is CLOSED in-corpus; the file joins the upstream first batch.

### MG-2 (M + S–M + M) — polynomial null sets → almost every composite state is entangled

Converts the research-gated Q28 item 5 into a bounded three-brick chain with no genuine wall:

1. **`polynomial_zeroSet_null`** (M, staged Cat-1): the zero set of a nonzero multivariate
   polynomial on `ℝⁿ` (then `ℂⁿ ≃ ℝ²ⁿ`) is Lebesgue-null. Classic missing Mathlib lemma.
   Route: induction on variables — Fubini slices, one-variable polynomials have finitely many
   roots (Mathlib has this), the leading-coefficient slice is null by induction.
2. **FS as an absolutely-continuous pushforward** (S–M): build the radial-density measure
   `(π^{-N} e^{−‖z‖²}) · vol` on `ℂᴺ` by hand (`withDensity`; no Gaussian API needed),
   restrict to `≠ 0`, push through `Projectivization.mk`. It is `U(N)`-invariant (unitaries
   preserve Lebesgue — linear isometries, real Jacobian 1 — and the density is norm-radial),
   so by the STAGED uniqueness theorem (`FubiniStudyUnique`) the pushforward **is**
   `fubiniStudyMeasure`. This gives FS a Lebesgue-a.c. source — the transport the c2 plan
   said was missing (no `U(N)`-chart work anywhere).
3. **`segre_range_null`** (M): the Segre minor is a polynomial on `ℂ^{nm}`, not identically
   zero (Q28's witness), its zero set is null (brick 1), the source measure is a.c. (brick 2),
   so the product rays are `compositeFubiniStudy`-null — ★★ **"almost every composite state is
   entangled"**, the C2 prose upgraded to a theorem. Closes the ledger's polynomial-zero-sets
   row AND Q28 item 5.

> **MG-2 SCOPING EXECUTED 2026-08-22** (feasibility probe `scratch_mg2_probe.lean` + corpus
> reads; the route SIMPLIFIED twice during the pass):
>
> 1. **The general `polynomial_zeroSet_null` is NOT needed** for the headline. The reindex
>    `rayReindexInv` computes on `mk` as a COORDINATE PERMUTATION (`tensorReindexL` is
>    `piLpCongrLeft` of `finProdFinEquiv`), so `segre_minor_eq`'s fixed corner minor pulls
>    back to the bare quadratic `v a · v b = v c · v d` at four DISTINCT indices of
>    `Fin (nA·nB)`. Its zero set is null by a two-step hand slicing (fix all but `v a`: the
>    `v b ≠ 0` slice is a singleton, null since `ℂ`'s volume has no atoms; the `v b = 0`
>    parameter set is a coordinate hyperplane, null by the same one-step slice), via
>    `measurePreserving_piEquivPiSubtypeProd` + `measure_prod_null` (both at pin ✓). The
>    general MvPolynomial lemma is RECORDED as a pure-optionality upstream candidate
>    (general-lift precedent): nothing in flight needs it once the specific quadratic lands.
> 2. **Probe results (round 1)**: `MeasureSpace (EuclideanSpace ℂ (Fin N))` FIRES (the
>    canonical inner-product-space volume), `IsAddHaarMeasure` ✓, `measure_ball_lt_top` ✓,
>    `LinearIsometryEquiv.measurePreserving` ✓ for ℝ-isometry equivs of `E`. Spelling
>    residue: `measure_ball_pos` needs its import; `LinearIsometryEquiv.restrictScalars`
>    doesn't exist (construct the ℝ-isometry by hand from the ℂ one); `NoAtoms` deprecated
>    → `NullSingletonClass`/`measure_singleton`; the pi-side lemmas return `Measure.pi`
>    form (bridge with `volume_pi`).
> 3. **The `E ↔ pi` volume bridge for ℂ components does NOT exist upstream**
>    (`PiLp.volume_preserving_ofLp` is ℝ-only). Not needed in full: NULL-transport suffices —
>    `map ofLp volume_E` is addHaar on the pi space (pushforward through
>    `PiLp.continuousLinearEquiv`), and two Haar measures are equal up to a positive scalar
>    (`Haar/Unique.lean`'s `…eq_smul_of_regular` family, spelling at build time), so null
>    sets coincide.
> 4. **Unitary norm-preservation on `E`** (`toEuclideanLin U` is an isometry) is not in the
>    corpus or upstream by that name — build it via the matrix-adjoint relation
>    (`U†U = 1` + the `toEuclideanLin`/adjoint bridge; spelling at build time).
> 5. **The action side is free**: `smul_mk_eq_mk` is `rfl` (UnitaryTransitive), the
>    uniqueness theorem `fubiniStudyMeasure_unique` takes exactly `[IsProbabilityMeasure] +
>    ∀ U, map (U • ·) μ = μ`, and `measurableSet_range_segre` is landed (Q28).
>
> **MG-2 EXECUTED 2026-08-22, same day as scoped.** All three bricks landed:
> `Mathlib/LinearAlgebra/Projectivization/FubiniStudyLebesgue.lean` (new, staged Cat-1: the
> Fubini slicing vehicle, `pi_coord_zero_null`, ★ `pi_quadratic_null`(`'`),
> `volume_ofLp_preimage_null` (Haar↔Haar null transport), `toEuclideanIsometry` (unitary as a
> `ℂ`-isometry via `toEuclideanCLM`), `ballMeasure`, `projOfVec`, ★
> `map_ballMeasure_eq_fubiniStudy`, ★★ `fubiniStudyMeasure_null_of_cone`) and the assembly in
> `RecordLayer/EntangledMeasure.lean` (extended in place): ★★
> `compositeFubiniStudy_range_segre_null` + ★★ `ae_not_mem_range_segre` — **almost every
> composite state is entangled**. The general polynomial lemma was never needed (route
> simplification 1 held). Snags: `Set.restrict` → `Set.domRestrict` and subtype binders need
> `show` to pin; `simpa using x.2` over-simplifies a subtype property to `True` (use `x.2`
> directly — membership in `{a}`/`{a}ᶜ` is definitional); `private` conflicts with the module
> system's public section; `EuclideanSpace` has no `NoAtoms` instance (route the origin's
> nullity through the pi space); the reindex's coordinate reading needs the coercion-normalising
> simp set (`LinearEquiv.coe_coe`, `LinearIsometryEquiv.coe_toLinearEquiv`) before
> `piLpCongrLeft_symm`/`_apply`; CLM `(f*g) x = f (g x)` and `1 x = x` are `rfl` (the
> deprecation replacements live in a different namespace).
>
> **Bricks**: **B-a** (S–M) the quadratic zero-set null lemma on the pi space + transport to
> `volume_E`; **B-b** (S–M) `fubiniStudyMeasure` as the `mk`-pushforward of the normalized
> ball measure (a.c. source; junk-totalised `mk`, invariance by isometry + ball, uniqueness)
> — the reusable API is `fubiniStudyMeasure_null_of_cone` (cone volume-null ⇒ FS-null);
> **B-c** (S) the assembly in `EntangledMeasure.lean` (extend in place): ★★
> `compositeFubiniStudy_range_segre_null` + the a.e.-entangled form. Home for B-a/B-b: new
> staged `Mathlib/LinearAlgebra/Projectivization/FubiniStudyLebesgue.lean` (upstream can
> split the pi-null lemma out later; noted in the header). GATE: if the Haar-uniqueness or
> adjoint spellings fight beyond a session, B-a falls back to a direct Fubini computation on
> the prod split and B-b to an explicit `withDensity` comparison; the physics target is
> unchanged.

### MG-4 (M, opportunistic) — chart-level Kähler closedness on `ℂℙ^{N−1}`

The flat half of the Kähler gap is gone upstream (`extDeriv` on normed spaces) and the corpus
already proved flat `dω = 0` for the constant form (`KahlerClosed.lean`). The next narrowing:
the genuine FS fundamental form **in an affine chart** (potential `K = log (1 + ‖z‖²)`,
`ω = i∂∂̄K` — non-constant now) is closed, via the upstream flat machinery. Leaves the Q8 gap
holding ONLY the quotient/manifold glue. Do when touching that area; not a session of its own.

### MG-5 (row only — gated) — the register tensor factorisation

`QReg m ≅ QReg 3 ⊗ QReg (m − 3)` (as Hilbert spaces, with the inner product carried) is a gap
this project has HIT (the measurement-gadget wall, `MeasurementAdder.lean`; also what the
general-lift optionality verdict cites) but never recorded in the ledger — added now. Attack
is GATED on a consumer, per the 2026-08-21 optionality decision; the route would be the
`Fin m ≃ Fin 3 ⊕ (m−3)` reindex + a `PiLp`-compatible tensor split.

## The upstream batch (user-gated)

The ledger's "suggested first upstream batch" (Projectivization `Topology` + `MeasureSpace`,
`StoneC1`, `DuhamelBound`, `PiecewisePreserving`, `PartialTrace`, `TraceDistance`) stands;
MG-1's metric file joins it when landed. Submission is an authorial act — queue by explicit
decision.

## Recommended order

MG-3 probe first (S — it gates the largest prize and its negative outcome is also valuable);
then MG-1 (self-contained, kills a row, feeds the upstream batch); then the MG-2 chain (the
headline strengthening); MG-4/MG-5 opportunistic/gated. Each M+ row goes scoping-first
(Q11 mold) at execution time — this plan is the triage, not the scoping.
