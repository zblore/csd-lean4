# TH1 concentration: Chebyshev-grade canonical typicality — scoping note (Q24)

> **EXECUTED 2026-08-21.** B1–B3 landed in `Thermo/CanonicalTypicality.lean`
> (extended in place): `phaseFlip` / `hadamardU` + coordinate actions +
> unitarity, the kill lemmas (`fs_cross_linear_zero`, `fs_re_sq_eq_im_sq` /
> `fs_re_sq_moment`), the per-pair engine ★ `fs_x_sq_eq_two_cross` (`a = 2b`),
> the moments ★ `fs_x_sq_moment` (`2/(N(N+1))`) and ★ `fs_x_cross_moment`
> (`1/(N(N+1))`), `fs_linear_expectation`, ★ `fs_linear_sq_moment`, and the
> capstone ★★ `fs_chebyshev_concentration` — polynomial-rate canonical
> typicality with no isoperimetry, exactly as scoped. The B1 gate never fired
> (the entrywise `U†U = I` fight was won by restricting each block row's sum to
> the pair `{i,j}` via `Finset.sum_subset` + `Finset.sum_pair`). **B4 (general
> Hermitian `A`) and B5 (reduced-state union-bound capstone) were NOT
> attempted**: they stay gated per this note's own brick list — B4 on a fresh
> session with the diagonalisation-transport route notes below, B5 on B4 plus a
> fresh go decision. The variance formula used downstream is
> `variance_eq_sub` (NOT `variance_def'` — wall-check correction).

Created 2026-08-21, the Q11 mold: feasibility checked before scoping, gates and
abort criteria fixed in advance. Companion to `Thermo/CanonicalTypicality.lean`
(TH-1, the module this extends in place per §8.3b), `specs/BACKLOG.md` (Q24,
queued 2026-08-20 after the external physicist review flagged TH-1's
expectation-level gap as load-bearing), and `MATHLIB-GAPS.md` (the Lévy row this
does NOT touch).

## The gap

TH-1 proves the Fubini–Study AVERAGE: `fs_first_moment` (the mean density matrix
is `I/N`) and `canonical_typicality_expectation` (the mean reduced state is
`I/d_S`). The reviewer's point: expectation alone does not say what a SINGLE
sampled state sees. The missing tier is concentration. Exponential (Lévy)
concentration needs spherical isoperimetry — a genuine Mathlib gap, recorded,
untouched here. The Chebyshev tier needs only a second moment, and this note
scopes that.

## The route discovery (why the rated hard part dissolves)

The brief rated "moment integrals" the known hard part — the second moment of
`⟨ψ|A|ψ⟩` over `μ_FS` via the Gaussian/Dirichlet machinery or the standard
`∫ ψᵢψ̄ⱼψₖψ̄ₗ` formula. The feasibility pass found the integrals are not needed:
**TH-1's own twirl style extends one moment higher and determines everything
algebraically.** With `x_i := momentMap · i` (= `rayDensity · i i`),
`a := E[x_i²]`, `b := E[x_i x_j]` (`i ≠ j`):

1. **Permutation invariance** (`permU`, `momentMap_permU` — landed) makes `a`
   and `b` well-defined (index-independent).
2. **Pointwise normalisation** `Σ_i x_i = 1` (landed) integrates to
   `a + (N−1)·b = 1/N`.
3. **A two-coordinate Hadamard rotation** `hadamardRot i j` (the `(1/√2)·
   [[1,1],[1,−1]]` block, a new unitary in the `signFlipMat` construction
   pattern) sends `x_i ↦ (x_i + x_j + 2·Re r)/2` with `r := rayDensity · i j`.
   Invariance of `E[x_i²]` expands to `4a = 2a + 4·E[(Re r)²] + 2b + 4·E[(x_i +
   x_j)·Re r]`. The last term dies by `signFlip` (`r ↦ −r`, `x` fixed — the
   landed kill idiom); `E[(Re r)²] = b/2` by a **quarter-phase flip**
   `phaseFlip i` (diagonal unitary with `Complex.I` at `i`, same construction
   pattern: `r ↦ i·r` swaps `Re r` with `−Im r` while `|r|² = x_i x_j`).
   Result: `a = 2b`.
4. Solve: `b = 1/(N(N+1))`, `a = 2/(N(N+1))` — the Dirichlet values, derived
   with **no simplex integrals, no Dirichlet-law moments, no Gaussian
   representation, no isoperimetry**. Pure twirl algebra, in the module's own
   idiom.

The same flips settle the general fourth-moment pattern: `E[r²] = 0`
(quarter-phase: `r² ↦ −r²`), unbalanced patterns die by `signFlip`, so for
Hermitian `A` the pattern expansion gives
`E[⟨A⟩²] = ((tr A)² + tr(A²)) / (N(N+1))` and
`Var = (N·tr(A²) − (tr A)²) / (N²(N+1)) ≤ ‖A‖² / (N+1)`.

## Bricks, in order

* **B1 (M)** — the new unitaries + kill lemmas + the two moments:
  `phaseFlip i` (+ membership + coordinate action), `hadamardRot i j` (+
  membership + coordinate action), `fs_x_sq_moment` (`a`) and
  `fs_x_cross_moment` (`b`). GATE: the Hadamard block's unitarity is a dense
  2×2-block computation — if the entrywise `U†U = I` fight exceeds the
  session, fall back to the rotation `[[cos,−sin],[sin,cos]]` at `π/4` or
  abort to the Dirichlet-integral route and re-scope.
* **B2 (S)** — the diagonal-observable variance: for `λ : Fin N → ℝ`,
  `E[Σ λ_i x_i] = (Σλ)/N` and
  `Var = (N·Σλ² − (Σλ)²)/(N²(N+1))`.
* **B3 (S) ★★** — `fs_chebyshev_concentration` (diagonal form): for `0 < ε`,
  `μ_FS {p | ε ≤ |Σ λ_i x_i − (Σλ)/N|} ≤ (N·Σλ² − (Σλ)²)/(N²(N+1)·ε²)`.
  Via `ProbabilityTheory.meas_ge_le_variance_div_sq` (wall-checked: exists at
  pin, needs `MemLp X 2` — bounded measurable on a probability space).
  **Polynomial-rate canonical typicality, with no isoperimetry.**
* **B4 (M, gated) ★★** — general Hermitian `A`: either the diagonalisation
  transport (`μ_FS` smul-invariance + `integral_map` + the spectral machinery,
  all landed — the law of `⟨ψ|A|ψ⟩` equals the law of `Σ eigenvalues·x`) or
  the direct pattern expansion. GATE: if the eigenbasis-transport plumbing
  fights, B1–B3 stand alone as the landed tier and B4 is recorded with the
  route notes.
* **B5 (M–L, gated, later)** — the reduced-state capstone: union-bound
  Chebyshev over `2·d_S²` real observables gives trace-norm concentration of
  `reducedRayDensity` around `I/d_S` at polynomial rate. Do NOT schedule with
  B1–B4; gate on B4 and a fresh go decision.

## Non-goals (unchanged)

Exponential Lévy concentration (the `MATHLIB-GAPS.md` row stands exactly as
written); dynamical thermalisation / ETH; deriving `μ_FS` from a flow (TH-1's
own scope note).

## Wall-check record

`meas_ge_le_variance_div_sq` ✓ (`Mathlib/Probability/Moments/Variance.lean`);
`momentMap_permU`, `signFlip` + kill idiom, `rayDensity` measurability /
boundedness / integrability ✓ (all in `CanonicalTypicality.lean`); the
normalisation `Σ x = 1` ✓ (`momentMap_sum_eq_one`); `MemLp` from boundedness ✓
(`MemLp.of_bound`-family). Home: `Thermo/CanonicalTypicality.lean` extended in
place; pins in the Extensions part (Thermo's home).
