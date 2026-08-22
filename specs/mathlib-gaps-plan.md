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
