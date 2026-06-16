# K1 — density-operator entropy `S(ρ) = −Tr ρ log ρ`, staged plan

**STATUS: K1-A DONE 2026-06-16 (incl. K1-A.2 unconditional tensor additivity);
K1-B.1 partial trace DONE 2026-06-16; K1-B.2 PARTIAL 2026-06-16 — Klein's inequality
(PD σ) + relative entropy + doubly-stochastic cross-term machinery + reduced-trace
identities LANDED; subadditivity headline + Araki–Lieb WALLED on the Kronecker-log
operator split (see K1-B.2 entry); K1-C/D planned.** The QI/QEC-roadmap keystone K1
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
- *Deferred (now UNBLOCKED, see K1-B note):* `S ≤ log d` — Mathlib HAS `convexOn_mul_log` /
  `strictConvexOn_mul_log` (`Analysis/SpecialFunctions/Log/NegMulLog.lean`), so this is a quick
  scalar-Jensen item; fold into K1-B or do standalone.

### K1-B — subadditivity + Araki–Lieb  [partial trace + Klein; moderate] — IN PROGRESS
`S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, `|S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB)`. **Convexity recon (2026-06-16):**
Mathlib HAS the *scalar* convexity `convexOn_mul_log` / `strictConvexOn_mul_log`; it does NOT have
matrix partial trace (the only `partialTrace` hits are category theory / probability kernels). Klein
/ subadditivity needs only the SCALAR convexity of `x log x` applied to the doubly-stochastic
overlap matrix `Dᵢⱼ = |⟨aᵢ|bⱼ⟩|²` between the two eigenbases (a Jensen / doubly-stochastic
averaging) — **NOT** the operator convexity (Lieb) that SSA (K1-C) needs. So K1-B is genuinely the
moderate middle, reachable now. Decomposed:

- **K1-B.1 — partial trace** [NEW infrastructure; low–moderate risk] — **DONE 2026-06-16**
  (`Mathlib/QuantumInfo/PartialTrace.lean`, namespace `QuantumInfo`, Cat-1). `partialTraceRight`
  (`Matrix (n×m) (n×m) ℂ → Matrix n n ℂ`, `(Tr_B M) i j = ∑ₖ M (i,k) (j,k)`) and `partialTraceLeft`;
  delivered: linearity (`_add`/`_smul` + bundled `partialTraceRightₗ`/`partialTraceLeftₗ` LinearMaps),
  trace preservation `trace (Tr_B M) = trace M` (`partialTraceRight_trace`, via `Fintype.sum_prod_type`),
  tensor reduction `Tr_B (ρ ⊗ₖ σ) = (trace σ) • ρ` / `Tr_A (ρ ⊗ₖ σ) = (trace ρ) • σ`
  (`partialTrace{Right,Left}_kronecker`; trace of the **traced-out** factor multiplies the surviving one —
  2×2⊗2×2 sanity-probed) + the `trace = 1` reductions (`partialTraceRight_kronecker_trace_one` ⟹
  `Tr_B (ρ_A ⊗ ρ_B) = ρ_A` when `Tr ρ_B = 1`, the K1-B.2 consumer), IsHermitian preservation,
  PSD preservation (`partialTrace{Right,Left}_posSemidef`, via the `v ⊗ eₖ` witness vectors
  `wₖ p = if p.2 = k then v p.1 else 0` and `star v ⬝ᵥ (Tr_B M) *ᵥ v = ∑ₖ star wₖ ⬝ᵥ M *ᵥ wₖ ≥ 0`),
  and density ↦ density (`partialTrace{Right,Left}_density`). Foundational-triple-only, AxiomAudit-pinned
  (trace/kronecker/posSemidef + density). **Dual-purpose: shared prerequisite with the gated
  decoherence / entangled D1 tier and the Landauer / ontic-entropy touchpoint** — the only
  CSD-load-bearing slice of K1. No convexity needed. Honesty: the PSD proof closed cleanly via the
  `v ⊗ eₖ` witness route (no alternative argument needed). Cleanly Mathlib-upstreamable (no Mathlib
  matrix partial trace exists).
- **K1-B.2 — Klein inequality → subadditivity + Araki–Lieb** [PARTIAL 2026-06-16,
  `Mathlib/QuantumInfo/Subadditivity.lean`].

  **LANDED (sorry-free, foundational-triple-only, AxiomAudit-pinned):**
  - `overlapV` (`V = U_ρᴴ U_σ`) + double stochasticity `overlapV_row_sum` / `overlapV_col_sum`
    (`∑ⱼ ‖Vᵢⱼ‖² = ∑ᵢ ‖Vᵢⱼ‖² = 1` from `Vᴴ V = V Vᴴ = 1`).
  - the **cross-term spectral expansion** `trace_mul_cfc_eq`:
    `Tr(ρ · cfc g σ) = ∑ᵢⱼ pᵢ · g(qⱼ) · ‖Vᵢⱼ‖²` (the trace of a product of two operators in
    DIFFERENT eigenbases; cyclic reduction `trace_mul_cfc_cyclic` + diagonal expansion
    `trace_diag_overlap_expand`, plus `re_trace_mul_cfc_eq`).
  - `relEntropy ρ σ := Re Tr(ρ log ρ) − Re Tr(ρ log σ)` + `re_trace_self_log`
    (`Re Tr(ρ log ρ) = ∑ pᵢ log pᵢ`).
  - **Klein's inequality** `relEntropy_nonneg` / `klein_inequality`: `D(ρ‖σ) ≥ 0` for `ρ` a
    density and **`σ` POSITIVE-DEFINITE**. Route: `D = ∑ᵢⱼ ‖Vᵢⱼ‖² pᵢ (log pᵢ − log qⱼ) ≥
    ∑ᵢⱼ ‖Vᵢⱼ‖² (pᵢ − qⱼ) = 1 − 1 = 0` via the **scalar** `Real.log_le_sub_one_of_pos`
    (`log(qⱼ/pᵢ) ≤ qⱼ/pᵢ − 1`) + BOTH row and column stochasticity. **No concave-Jensen step**
    (deliberate: Jensen `∑ w log x ≤ log(∑ w x)` over `Ici 0` is FALSE at the Mathlib junk
    `log 0 = 0`; the scalar route is robust at zero weights and `pᵢ = 0`).
  - reduced-trace identities `trace_mul_kronecker_one_right` / `trace_mul_one_kronecker_left`:
    `Tr(M · (X ⊗ I)) = Tr(Tr_B(M) · X)` (basis-free; the subadditivity bridge).

  **THE WALL (subadditivity headline + Araki–Lieb, NOT landed):** two genuine obstructions.
  1. **PD-`σ` is load-bearing, not cosmetic.** With Mathlib's junk `Real.log 0 = 0`, the
     *finite* expression `Tr(ρ log ρ) − Tr(ρ log σ)` can be NEGATIVE when `supp ρ ⊄ supp σ`
     (the true `D(ρ‖σ) = +∞` case); Klein's `≥ 0` is false without a support hypothesis.
     `σ` PD is the standard clean sufficient condition. Subadditivity via Klein at `σ = ρ_A⊗ρ_B`
     therefore needs either `ρ_A, ρ_B` PD or the support-projection argument
     (`supp ρ_AB ⊆ supp(ρ_A⊗ρ_B)` always, but proving it in Lean is itself a sub-development).
  2. **The Kronecker-log operator split** `cfc log (ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B`
     (item (e) of the route) is the predicted hard sub-problem and is NOT closed. Mathlib has
     no commuting-CFC-log-additivity and no direct cfc-conjugation-covariance lemma. The viable
     Lean route is `StarAlgHomClass.map_cfc` applied to the conjugation `*`-automorphism
     `Unitary.conjStarAlgAut` (covariance `cfc f (U A Uᴴ) = U (cfc f A) Uᴴ`), which drags three
     real obligations — continuity of the conjugation linear map
     (`LinearMap.continuous_of_finiteDimensional`, NOT `fun_prop`-provable as-is),
     `ContinuousOn Real.log (spectrum)` (needs PD), and `IsSelfAdjoint` predicate preservation —
     PLUS the W-basis diagonal identity `log(λ_a μ_b) = log λ_a + log μ_b` over `W = U_A ⊗ U_B`
     (the sorted-eigenvalue-vs-W-basis mismatch is the same subtlety `spectral_sum_kronecker`
     sidesteps for SUMS, but here the OPERATOR is needed). This is a multi-lemma development,
     correctly flagged in the route as item (e). Once (e) lands, subadditivity follows from
     Klein + `re_trace_self_log` + the reduced-trace identities (all already in the file).
     Araki–Lieb then follows from subadditivity on a purification.

  The doubly-stochastic two-eigenbasis cross-term — predicted as the place to audit hardest —
  is **closed** (`trace_mul_cfc_eq`); the actual residual wall is the operator-level
  Kronecker-log split, not the doubly-stochastic step.

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
