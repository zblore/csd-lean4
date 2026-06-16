# K1 — density-operator entropy `S(ρ) = −Tr ρ log ρ`, staged plan

**STATUS: K1-A DONE 2026-06-16 (incl. K1-A.2 unconditional tensor additivity 2026-06-16);
K1-B/C/D planned.** The QI/QEC-roadmap keystone K1
(`specs/qi-qec-roadmap.md` §1). Builds the entropy / information-measure stratum:
von Neumann entropy, subadditivity, strong subadditivity, data-processing, then downstream
Holevo / Schumacher / entanglement entropy / quantum thermodynamics.

## 0. Honest framing (read first)

**K1 is mostly Cat-1 Mathlib-adjacent infrastructure that sits BESIDE the CSD layers, not
downstream of them.** Von Neumann entropy is interpretation-free Hilbert-space mathematics; it
would compile identically in a repo with no CSD content. It lives in the `Mathlib/QuantumInfo/`
staging tree (natural Mathlib namespace `QuantumInfo`), parallel to LF1–LF5, upstreamable.

- **K1-A/B/D are coverage**, not thesis: standard quantum Shannon theory imported into Lean,
  low CSD-novelty per theorem. The detector being calibrated (2026-06-16), these will proceed
  clean and that tells us little about CSD specifically.
- **K1-C (strong subadditivity) is the hard core** and the genuine new-math risk: it rests on
  Lieb's concavity theorem / operator convexity, which Mathlib does **not** appear to have. This
  stage may stall or require multi-week operator-convexity infrastructure. It is the one stage
  capable of producing a real obstruction, hence the most informative.
- **The only thesis-relevant part is the CSD touchpoint**: `S(ρ_A)` read as the log-volume of
  the de-isolated spread when DOF are traced out, and Landauer tying entropy to the ontic measure
  `μ_L`. This is where K1 stops being import and becomes CSD content; it is also the same
  machinery (partial trace) the gated decoherence / entangled D1 tier needs.

Do not oversell K1 as "built on the CSD foundation"; only the Landauer / ontic-entropy touchpoint
is. The residual epistemic risk of the programme is in the deferred D1/A5 tier, not in K1.

## 1. The key reuse insight (why K1-A is immediate)

`CsdLean4/Mathlib/QuantumInfo/TraceDistance.lean` already stages the spectral machinery:
- `Matrix.IsHermitian.cfc f = U · diag(↑∘f∘λ) · Uᴴ` (continuous functional calculus, any `f`),
- `re_trace_cfc hA f : RCLike.re (trace (hA.cfc f)) = ∑ i, f (hA.eigenvalues i)`,
- `Matrix.IsHermitian.eigenvalues`, `traceNorm_of_posSemidef`, the Jordan/`posPart` layer.

So `vonNeumannEntropy hρ := ∑ i, Real.negMulLog (hρ.eigenvalues i)` (Mathlib has `Real.negMulLog`,
`negMulLog x = −x log x`), and `S(ρ) = RCLike.re (− trace (ρ * log ρ))` follows from `re_trace_cfc`
at `f = negMulLog` (since `negMulLog ∘ λ` is the spectrum of `−ρ log ρ`). Elementary properties
reduce to `negMulLog` facts + eigenvalue facts (PSD ⟹ `λᵢ ≥ 0`; `trace ρ = 1` ⟹ `∑ λᵢ = 1` ⟹
`λᵢ ∈ [0,1]`). No new analysis for K1-A.

## 2. Decomposition (stages, new-vs-reuse, risk)

### K1-A — spectral von Neumann entropy + elementary properties  [REUSE; low risk] — DONE 2026-06-16
File `CsdLean4/Mathlib/QuantumInfo/Entropy.lean`, namespace `QuantumInfo`, hypothesis style
(`IsHermitian`/`PosSemidef`/`trace = 1`, matching `TraceDistance.lean`). Delivered,
foundational-triple-only, AxiomAudit-pinned:
- `vonNeumannEntropy hρ := ∑ i, Real.negMulLog (hρ.eigenvalues i)`;
- operator-form identities `vonNeumannEntropy_eq_re_trace_cfc`
  (`S(ρ) = Re Tr(cfc negMulLog ρ)`) and `vonNeumannEntropy_eq_neg_re_trace_mul_log`
  (`S(ρ) = − Re Tr(cfc (x↦x log x) ρ)` = `−Tr(ρ log ρ)`, with `cfc_id_mul_log` confirming the
  cfc is genuinely `ρ log ρ`) via `re_trace_cfc`;
- `vonNeumannEntropy_nonneg`: `S ≥ 0` for a density operator (eigenvalues in `[0,1]` via
  `eigenvalues_mem_Icc_of_density` ⟹ `Real.negMulLog_nonneg`);
- `vonNeumannEntropy_eq_zero_of_projection` (`ρ·ρ = ρ` ⟹ spectrum `⊆ {0,1}` ⟹ `S = 0`, via the
  new `cfc_eq_iff_on_eigenvalues` spectral-injectivity helper) and the named pure-state corollary
  `vonNeumannEntropy_eq_zero_of_pure` (+ unit trace; non-vacuity noted in docstring);
- `vonNeumannEntropy_conj_unitary`: `S(U ρ Uᴴ) = S(ρ)` via `charpoly_conj_unitary`
  (two `charpoly_mul_comm`) + `IsHermitian.eigenvalues_eq_eigenvalues_iff`.
- **Additivity — UNCONDITIONAL (K1-A.2 DONE 2026-06-16).** `vonNeumannEntropy_kronecker`:
  `S(ρ⊗σ) = S(ρ)+S(σ)` for density operators (PSD + unit trace), **no spectral hypothesis**.
  The load-bearing new lemma is the **Kronecker spectrum** `spectral_sum_kronecker`:
  `∑_c g(λ(ρ⊗σ)_c) = ∑_{i,j} g(λρ(i)·λσ(j))` for every `g`. Route A (charpoly,
  permutation-invariant — sidesteps the eigenvalue-*sorting* trap): `ρ⊗σ` is unitarily similar to
  `diagonal(λρ·λσ)` (`kronecker_eq_conj_diagonal_eigenvalues`, via the two spectral theorems +
  `mul_kronecker_mul` + `diagonal_kronecker_diagonal`), so its charpoly is `∏_p (X−↑(λρ·λσ))`
  (`charpoly_conj_unitary` + `charpoly_diagonal`); the spectral sum is read off the charpoly root
  multiset by `spectral_sum_eq_of_charpoly_prod`. **No Kronecker spectral theorem assumed — this
  IS one** (spectral-sum form). Foundational-triple-only, AxiomAudit-pinned. The conditional
  `vonNeumannEntropy_kronecker_of_eigenvalues` is retained for callers holding a sorted
  eigenvalue-product witness.
- *Deferred:* `S ≤ log d` (concavity of `negMulLog` / Jensen — needs convexity infrastructure;
  not blocking K1-A).

### K1-B — subadditivity + Araki–Lieb  [partial trace + Klein; moderate]
`S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, `|S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB)`. Needs **partial trace** (built here;
shared prerequisite with the decoherence/entangled D1 tier) + the Klein / Gibbs inequality.

### K1-C — strong subadditivity (Lieb–Ruskai)  [HARD; the genuine new-math core]
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. Rests on Lieb's concavity / operator convexity of
`(A,B) ↦ Tr exp(log A + log B)`, **not believed to be in Mathlib**. **OPEN FORK (decision owed):**
(a) build the operator-convexity infrastructure (Lieb's concavity — multi-week, genuinely new,
upstreamable), or (b) state SSA as an honest hypothesis/`axiom` and proceed to K1-D. This choice
sets whether K1 is a ~2-stage or a much longer build. Flagged, not yet decided.

### K1-D — data-processing / monotonicity  [composes K1-C + K2 channels]
`S(Φρ) ≥ S(ρ)` under CPTP, composing K1-C with the K2 `Channel.lean` already built; downstream
Holevo / Schumacher.

### CSD touchpoint (the only thesis-relevant slice)
`S(ρ_A) = log-volume of the de-isolated spread`; Landauer ↔ `μ_L`. Connects to the
decoherence reading of QEC (`Empirical/CSD/QEC/ThreeQubit.lean`) and the entangled D1 tier.

## 3. Recommended order

K1-A → K1-B → (SSA fork decision) → K1-C → K1-D. K1-A is decision-independent and starts now.
Each stage via the expert → auditor → commit(+doc) loop (the auditor calibrated SOUND 2026-06-16,
7/7 on a blind planted-flaw battery), with doc-currency in the landing commit (this file + INDEX +
qi-qec-roadmap K-series status + AxiomAudit pins). The SSA fork is the one strategic decision; it
can be deferred until K1-B lands.

## 4. Honest non-goals

- Not a CSD result except the Landauer / ontic-entropy touchpoint (K1 is sibling infrastructure).
- No infinite-dimensional / continuous-variable entropy (finite-dim matrices only, per the corpus
  finite-EFT posture).
- SSA (K1-C) may be axiom-stated rather than derived, pending the §2 fork decision.
