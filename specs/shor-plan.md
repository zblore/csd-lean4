# Shor's algorithm — plan

The final item of the quantum-algorithm branch (`specs/nqubit-register-plan.md` R5+). Drafted
2026-06-06, building on the completed register (R1), Hadamard (R2/R3), Deutsch-Jozsa (R4),
QFT unitarity (R5), and Grover (R5+). Status: **planned, not started.**

Shor is **in scope**: it is finite-dimensional QM throughout (registers of dimension `2^t` and
`ZMod N`, both finite) plus finite number theory over `ℤ/Nℤ`. Nothing here is Quantum Field
Theory. But unlike the earlier algorithms, the bulk of the work and the largest Mathlib gaps
are in the **classical** number-theory tail, not the quantum core.

## 0. Structure of the algorithm

Factor an odd composite `N` that is not a prime power. Classical reduction: factoring reduces
to **order-finding**. Pick `a` coprime to `N`, let `r = orderOf (a : (ZMod N)ˣ)`. If `r` is even
and `a^(r/2) ≢ -1 (mod N)`, then `gcd(a^(r/2) ± 1, N)` are nontrivial factors. The quantum part
finds `r` via phase estimation of "multiply by `a`": prepare the counting register uniform,
apply the modular-exponentiation oracle, apply `QFT⁻¹`, measure `c ≈ s·T/r` (`T = 2^t`), then
recover `r` from `c/T` by continued fractions.

## 1. Tranches

Each is a self-contained, separately-verifiable unit. Tagged **[Q]** (finite QM, reuses our
infra) or **[NT]** (classical number theory).

### S1 — Modular-exponentiation oracle as a permutation unitary  **[Q]**, medium
- Work register `EuclideanSpace ℂ (ZMod N)` (or `Fin N`). `mulOracle a : |y⟩ ↦ |a·y⟩` is the
  permutation induced by multiplication by the unit `a` on `ZMod N`; a genuine permutation
  matrix, hence unitary. Then `|x⟩|y⟩ ↦ |x⟩|a^x · y⟩` on the joint register.
- Mathlib: `Equiv.mulLeft₀` / unit multiplication is a bijection; permutation matrices are
  unitary. Clean.

### S2 — Eigenstructure of "multiply by a"  **[Q]**, medium
- `u s := (1/√r) ∑_{j<r} ω_r^{-sj} |a^j⟩` is an eigenvector of `mulOracle a` with eigenvalue
  `ω_r^s = exp(2πi s/r)`; and `(1/√r) ∑_{s<r} u s = |1⟩`.
- Reuses `Fourier.qftω` and the roots-of-unity machinery from `Fourier.lean` (`qftω_primitive`,
  the geometric-sum orthogonality). This is the hinge that turns order-finding into phase
  estimation.

### S3 — Phase estimation, clean case `r ∣ T`  **[Q]**, medium  ← **recommended first milestone (M1)**
- With `T = 2^t` and `r ∣ T`: starting from uniform counting register, applying the oracle
  (controlled powers = modexp), then `QFT⁻¹`, the measured value `c` is uniform on the `r`
  multiples `{s·T/r : s < r}`; `prob(c = s·T/r) = 1/r` exactly.
- Proof is a finite geometric sum collapse, the same `∑_k ζ^k = T·[ζ=1]` orthogonality proved
  for `qft_unitary` (`Fourier.lean`). **No new hard analysis.** This is the genuine quantum
  core of Shor and the cleanest defensible "Shor's algorithm (ideal case)" deliverable.

### S4 — Phase estimation, general case `r ∤ T`  **[Q]**, medium-hard
- `prob(c = round(s·T/r)) ≥ 4/π²` for each `s`. Dirichlet-kernel lower bound on
  `|∑_{x<T} ω^{x(c - sT/r)}|²`; needs the real-analysis estimate `|sin(Tα)/sin(α)|` /
  `2/π ≤ sin(x)/x` type bounds. Mathlib has `Real.sin` bounds but the packaged Dirichlet
  estimate must be assembled.

### S5 — Continued-fraction recovery of `r`  **[NT]**, medium-hard — **Mathlib gap**
- From `|c/T - s/r| ≤ 1/(2T)` with `r < √T` (choose `t ≈ 2 log₂ N`, so `T > N²`), `s/r` is a
  convergent of `c/T`, recoverable by the CF algorithm.
- **Mathlib has the forward bound (`abs_sub_convergents_le'`) but NOT the Legendre converse**
  ("any `p/q` with `|x - p/q| < 1/(2q²)` is a convergent of `x`"). That converse must be built
  on Mathlib's `GenContFract` API. This is the "continued-fraction period recovery" the plan
  always flagged as a real cost.

### S6 — Factoring from order: nontrivial square root of unity  **[NT]**, medium — **Mathlib gap**
- `x² ≡ 1 (mod N)`, `x ≢ ±1` ⟹ `gcd(x-1, N)` is a nontrivial factor. Build on `ZMod`/`Nat.gcd`
  /CRT. The exact lemma is not in Mathlib (related pieces exist: `orderOf` API is rich,
  `ZMod.chineseRemainder`). Standalone and reusable.

### S7 — Random-`a` success probability ≥ 1/2  **[NT]**, hard — **largest build, Mathlib gap**
- For `N` odd with `m ≥ 2` distinct prime factors and `a` uniform in `(ZMod N)ˣ`:
  `P[r even ∧ a^(r/2) ≢ -1] ≥ 1 - 1/2^m ≥ 1/2`. Standard proof: CRT decomposition
  `(ZMod N)ˣ ≅ ∏ (ZMod p_i^{k_i})ˣ`, count via the 2-adic valuation of the per-factor orders.
  This is a known-hard finite-group-theory theorem and is almost certainly **not** in Mathlib.
  It is the real gate to a full factoring guarantee.

### Assembly — `shor_factors`
- Combine S6 + (S3/S4 + S5) + S7: the algorithm outputs a nontrivial factor of `N` with
  probability `≥ Ω(1/log N)` (the `1/log N` from `O(log N)` repetitions to amplify the
  per-run constant). Headline theorem; AxiomAudit-pinned.

## 2. Dependency graph

```
S1 oracle ─► S2 eigenstructure ─► S3 phase-est (r∣T)  ──┐  [M1: quantum core, ideal]
                                  └► S4 phase-est (r∤T) ─┤
                                       S5 CF recovery ───┤  [M2: order-finding, general]
S6 sqrt-of-unity factor ───────────────────────────────┤
S7 random-a ≥ 1/2 ─────────────────────────────────────┴► Assembly shor_factors  [M3: factoring]
```

## 3. Milestones and honest recommendation

- **M1 = S1+S2+S3 (quantum core, ideal `r ∣ T`).** Self-contained, reuses `Fourier.lean`'s
  roots-of-unity orthogonality directly, no new hard analysis. This is the in-character,
  finite-QM heart of Shor and the recommended first executable tranche.
- **M2 = +S4+S5 (order-finding for any `r`).** Adds the Dirichlet-kernel bound (real analysis)
  and the Legendre CF converse (Mathlib gap, must build).
- **M3 = +S6+S7 (full factoring, `Ω(1/log N)`).** S7 (random-`a` ≥ 1/2 via CRT counting) is the
  hardest piece and the most likely to stall; it is classical group theory, not physics.

Honest read: the QM-validity payoff is concentrated in **M1** (and the eigenstructure of S2 is
the conceptually interesting bridge). Past **M2**, the work is essentially a classical
number-theory library build (CF Legendre converse, the sqrt-of-unity factor lemma, the CRT
counting bound). Recommend executing **M1** first as a clean tranche, then re-deciding whether
to invest in the classical tail (M2/M3) versus returning to D1/LF5 thesis work. The branch
already demonstrates finite-QM coverage (DJ, QFT, Grover); M1 adds Shor's quantum essence
without committing to the large number-theory apparatus.

## 4. Mathlib-gap summary (build-debt, not theory)

- Legendre CF converse (S5): absent; forward direction present.
- Nontrivial-sqrt-of-unity factor lemma (S6): absent; `ZMod`/`orderOf`/CRT primitives present.
- Random-`a` ≥ 1/2 group-counting (S7): absent; the hardest, a genuine finite-group-theory
  theorem.
- Available and reused: `orderOf` API, `ZMod.chineseRemainder`, `Complex.isPrimitiveRoot_exp`
  + our `Fourier.qftω` orthogonality, `GenContFract` forward approximation.
