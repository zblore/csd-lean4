> ⚠️ HISTORICAL — layer complete; frozen execution log. Open items live in [BACKLOG.md](BACKLOG.md).
# K1 — density-operator entropy `S(ρ) = −Tr ρ log ρ`, staged plan

**STATUS: K1-A DONE 2026-06-16 (incl. K1-A.2 unconditional tensor additivity);
K1-B.1 partial trace DONE 2026-06-16; K1-B.2 DONE 2026-06-16 (subadditivity) + Araki–Lieb DONE
2026-06-17 (PD ρ_AB) — Klein's inequality
(PD σ) + relative entropy + doubly-stochastic cross-term machinery + reduced-trace identities +
the Kronecker-log operator split (`cfc_log_kronecker`, via the decomposition-independent
`cfc_eq_conj_diagonal` / Lagrange route) + the subadditivity headline `S(ρ_AB) ≤ S(ρ_A)+S(ρ_B)`
(marginals PD, ρ_AB only PSD) all LANDED; **`S ≤ log d` + Araki–Lieb `|S_A−S_B|≤S_AB` (ρ_AB PD)
DONE 2026-06-17** via the purification + Schmidt-symmetry route, so **K1-A and K1-B are COMPLETE**
(only the singular-marginal Araki–Lieb generalisation deferred). **K1-C SCAFFOLD + CONDITIONAL
REDUCTION LANDED 2026-06-17**: tripartite marginals + the mutual-information identity
`relEntropy_kronecker_eq_entropy_sub` (unconditional) + the conditional reduction
`strong_subadditivity_of_relEntropy_monotone` (SSA from DPI carried as explicit hypothesis `hDPI`),
`StrongSubadditivity.lean`, no axiom / no sorry, foundational-triple-only, AxiomAudit-pinned. The
deep operator-convexity input (Lieb / joint convexity / DPI) is ISOLATED as `hDPI` and confirmed
absent from Mathlib; FORK (build Lieb vs axiom-state DPI) open. K1-D planned.**
The QI/QEC-roadmap keystone K1
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
- **`S ≤ log d` DONE 2026-06-17** (`vonNeumannEntropy_le_log_card`, `Entropy.lean`): the
  maximum-entropy bound `S(ρ) ≤ Real.log (Fintype.card n)` via concave Jensen on `negMulLog`
  (uniform weights `1/d`, `∑λ = 1`); tight at the maximally mixed state (`S(I/d) = log d`).
  Foundational-triple-only, AxiomAudit-pinned.

### K1-B — subadditivity + Araki–Lieb  [partial trace + Klein; moderate] — DONE 2026-06-16/17 (subadditivity + Araki–Lieb for PD ρ_AB; singular-marginal A–L deferred)
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
- **K1-B.2 — Klein inequality → subadditivity + Araki–Lieb** [**DONE 2026-06-16/17** (subadditivity
  + Araki–Lieb for PD ρ_AB; singular-marginal A–L deferred). `Mathlib/QuantumInfo/Subadditivity.lean`].

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

  **THE WALL — NOW CLOSED 2026-06-16.** The Kronecker-log operator split landed, so subadditivity
  is a proved headline:
  - `cfc_eq_conj_diagonal`: if `M = U · diagonal d · Uᴴ` (`U` unitary, `d` real) then
    `hM.cfc f = U · diagonal (↑∘f∘d) · Uᴴ` — **decomposition-independent** (holds for ANY
    diagonalizing `U`, not just the canonical eigenvectorUnitary). Proof via **Lagrange
    interpolation**: `hM.cfc f = aeval M q` for `q` interpolating `f` on the spectrum, then `aeval`
    conjugates diagonally through `U` via `Unitary.conjStarAlgAut`. The `d c`-are-eigenvalues fact
    (`eigenvalue_of_conj_diagonal`) routes through the **charpoly root multiset**, sidestepping the
    eigenvalue-sorting subtlety entirely — this is the cleaner route than the `StarAlgHomClass.map_cfc`
    continuity yak-shave originally feared.
  - `cfc_log_kronecker` (PosDef `ρ_A, ρ_B`): `(ρ_A ⊗ₖ ρ_B).cfc log = (ρ_A.cfc log) ⊗ₖ 1 + 1 ⊗ₖ
    (ρ_B.cfc log)` — apply `cfc_eq_conj_diagonal` to `kronecker_eq_conj_diagonal_eigenvalues`
    (`ρ_A⊗ρ_B = W diag(λ_A·λ_B) Wᴴ`, `W = U_A⊗U_B`), per-eigenvalue `Real.log_mul` (PD ⟹ `λ>0`),
    `mul_kronecker_mul` distribution.
  - **`vonNeumannEntropy_subadditive`**: `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` under `ρ_AB.PosSemidef`,
    `ρ_AB.trace = 1`, and the **MARGINALS** `(partialTraceRight ρ_AB)`, `(partialTraceLeft ρ_AB)`
    **PosDef**. **Crucially does NOT assume `ρ_AB` PD** — pure entangled states (where `S(ρ_AB)=0`,
    marginals full-rank) ARE covered; audited non-vacuous at a correlated non-product state. Proof:
    Klein at `σ = ρ_A⊗ρ_B` (PD via `Matrix.PosDef.kronecker`) + `cfc_log_kronecker` +
    `trace_mul_kronecker_one_right`/`_left` + `re_trace_self_log`.

  The doubly-stochastic two-eigenbasis cross-term — predicted as the place to audit hardest —
  closed first (`trace_mul_cfc_eq`); the operator-level Kronecker-log split (the *actual* residual
  wall) then closed via the Lagrange-interpolation route above. **Araki–Lieb DONE 2026-06-17**
  (`vonNeumannEntropy_araki_lieb`, `araki_lieb_one_side`): `|S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB)` for
  **`ρ_AB` positive-definite** (full-rank global state; the pure-entangled saturating case
  `S_AB = 0` is excluded, by design — honestly documented). Built via the genuine **purification
  route**: `exists_purification` (unit Ψ on (AB)⊗R, R≅AB, with `Tr_R |Ψ⟩⟨Ψ| = ρ_AB`) +
  **`pure_marginal_entropy_eq`** (Schmidt symmetry: pure-state marginals have equal entropy, via
  `MMᴴ`/`MᴴM` cospectrum on nonzero eigenvalues, `negMulLog 0 = 0`) + `reshapeABR` (the A|BR vs
  AB|R reassociation) + subadditivity; the other side via a `Equiv.prodComm` swap-reindex
  (`posDef_of_charpoly_eq` on the reindexed state). Audited SOUND (Bell + asymmetric 2×3 + a
  correlated full-rank ρ_AB with `S_A ≠ S_B` probes; PD-scope honesty confirmed). Deferred only:
  the singular-marginal Araki–Lieb generalisation. Foundational-triple-only, AxiomAudit-pinned
  (`cfc_eq_conj_diagonal`, `cfc_log_kronecker`, `vonNeumannEntropy_subadditive`,
  `vonNeumannEntropy_le_log_card`, `pure_marginal_entropy_eq`, `exists_purification`,
  `araki_lieb_one_side`, `vonNeumannEntropy_araki_lieb`). **Provenance note:** the split + headline
  were written in a remote-control session and left UNCOMMITTED with a build-breaking typo
  (`_root_.PosDef.kronecker` → `Matrix.PosDef.kronecker` + missing `import
  Mathlib.Analysis.Matrix.Order`); recovered, fixed, independently audited SOUND, then committed.

### K1-C — strong subadditivity (Lieb–Ruskai)  [SCAFFOLD + CONDITIONAL REDUCTION LANDED 2026-06-17; deep input ISOLATED, FORK OPEN]
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. Module `CsdLean4/Mathlib/QuantumInfo/StrongSubadditivity.lean`
(namespace `QuantumInfo`, Cat-1). **No `axiom`, no `sorry`; foundational-triple-only on everything
that landed; AxiomAudit-pinned.**

**WHAT LANDED (the LF3-bundle pattern: everything proved except one named deep hypothesis).**

- **Tripartite marginals** on `Matrix (a × b × c) (a × b × c) ℂ` (Lean's `a × b × c = a × (b × c)`):
  `rhoBC := partialTraceLeft ρ` (trace `A`), `rhoAB := partialTraceRight (reassocABC ρ)` (regroup to
  `(a×b)×c`, trace `C`), `rhoA := partialTraceRight ρ`, `rhoB := partialTraceLeft (rhoAB ρ)`. The
  reassociation `assocE : (a×b×c) ≃ ((a×b)×c)` is `(Equiv.prodAssoc).symm`; trace/PSD transfer
  (`reassocABC_trace`, `reassocABC_posSemidef`). The reindexing identities the auditor probes are
  proved by direct index computation: `rhoAB_apply`, `rhoBC_apply`, `rhoA_apply`, `rhoB_consistency`
  (`rhoB = Tr_C ρ_BC`), `rhoA_eq_traceB_AB` (`Tr_BC ρ = Tr_B ρ_AB`), `rhoB_eq_traceC_BC`.
- **The mutual-information identity (the genuine unconditional algebraic content)**
  `relEntropy_kronecker_eq_entropy_sub`: for a bipartite density `ρ` on `x × y` with both marginals
  PD, `D(ρ ‖ ρ_X ⊗ ρ_Y) = S(ρ_X) + S(ρ_Y) − S(ρ)`. This is `cfc_log_kronecker` (the Kronecker-log
  split, already in `Subadditivity.lean`) + the reduced-trace identities
  `trace_mul_kronecker_one_right`/`_left`, extracted as a reusable *identity* (not the subadditivity
  *inequality*). **No deep input.**
- **The CONDITIONAL reduction (the real deliverable)** `strong_subadditivity_of_relEntropy_monotone`:
  SSA derived from the **data-processing inequality carried as an explicit hypothesis** `hDPI`:
  `D(ρ_AB ‖ ρ_A⊗ρ_B) ≤ D(ρ_ABC ‖ ρ_A⊗ρ_BC)` (relative entropy non-increasing under `Tr_C`, which
  sends `ρ_ABC ↦ ρ_AB` and `ρ_A⊗ρ_BC ↦ ρ_A⊗ρ_B`). The reduction is genuine: both relative entropies
  are rewritten by the MI identity into `I(A:BC) = S_A+S_BC−S_ABC` and `I(A:B) = S_A+S_B−S_AB`; the
  common `S_A` cancels and `hDPI` becomes `S_B−S_AB ≤ S_BC−S_ABC`, i.e. SSA. Correct direction
  (`I(A:BC) ≥ I(A:B)`, mutual information monotone under discarding `C`); non-vacuous on correlated
  `ρ_ABC` (equality iff a quantum Markov chain `A−B−C`). Global `ρ_ABC` only `PosSemidef`; the three
  sub-marginals PD is the standard Klein-style support condition (`relEntropy_nonneg` needs PD `σ`).

**THE PRECISE WALL (the deep input NOT discharged).** `hDPI` is the standard deep input —
data-processing inequality for quantum relative entropy = joint convexity of `(ρ,σ) ↦ D(ρ‖σ)` =
Lieb's concavity of `(A,B) ↦ Tr exp(log A + log B)`. **Scout of Mathlib HEAD (2026-06-17):**

- Operator MONOTONICITY (single-variable Löwner order) IS present: `CFC.log_monotoneOn` /
  `CFC.log_le_log` (log operator monotone), `CFC.monotone_rpow` / `monotone_nnrpow` /
  `sqrt_le_sqrt` (`x^p` operator monotone, `p∈[0,1]`), and the integral-representation scaffold
  `…/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean`.
- Operator CONVEXITY / CONCAVITY is **NOT** present. `…/ExpLog/Order.lean` carries explicit TODOs:
  "Show that the log is operator concave" and "Show that `x ↦ x log x` is operator convex". There is
  **no** `OperatorConvex`/`OperatorMonotone` predicate, **no** Lieb/Ando/Epstein/Wigner–Yanase,
  **no** joint convexity of any trace functional, **no** DPI / relative-entropy monotonicity.

So the minimal missing Mathlib lemma is **joint convexity of `D(·‖·)`** (or its DPI / Lieb form). A
realistic build is the operator-convexity stratum: an `OperatorConvexOn` predicate on the Löwner
order, the Löwner-matrix / integral route to operator convexity of `−log` and `x↦x log x`, the
perspective-function joint-convexity lift, and the partial-trace DPI corollary — a genuine
**multi-week** infrastructure build (the in-Mathlib `Rpow/IntegralRepresentation` scaffold is the
template but only covers `p∈(0,1)` *monotonicity*, not convexity and not the two-variable
perspective). **FORK (user's decision, owed):** (a) build the operator-convexity / Lieb infrastructure
(multi-week, upstreamable), or (b) discharge `hDPI` by stating DPI / joint convexity as a named
`axiom`. The axiom-vs-build choice is deliberately left open; this stage isolates the wall as `hDPI`
and does not paper it.

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
- SSA (K1-C): the conditional reduction (SSA from DPI) is LANDED unconditionally; the deep input
  `hDPI` (DPI / joint convexity / Lieb) may be axiom-stated rather than built, pending the fork.
