# Shor's algorithm — plan

The final item of the quantum-algorithm branch (`specs/nqubit-register-plan.md` R5+). Drafted
2026-06-06, building on the completed register (R1), Hadamard (R2/R3), Deutsch-Jozsa (R4),
QFT unitarity (R5), and Grover (R5+). Status: **M1 DONE 2026-06-06** (S1 + S2 + S3-core + the
S2↔S3 bridge); **M1.5 DONE 2026-06-07** (the full ideal-case `r ∣ T` order-finding output
distribution: the two-register joint state + uniform-`1/r` measurement marginal); **S4 DONE
2026-06-07** (the single-eigenvector / generic-`φ` Dirichlet-kernel `≥ 4/π²` phase-estimation lower
bound, `phase_estimation_lower_bound` + `shor_phase_estimation_lower_bound`). **S4 closes the last
*quantum* piece of order-finding.** What remains is the classical number-theory tail: S5 (CF Legendre
converse), S6 (sqrt-of-unity factor), S7 (random-`a` ≥ 1/2). M2 (= S4+S5) is now S5-only; M3 not
started.

**M1 landed (`CsdLean4/Empirical/QM/Algorithms/ShorCore.lean`, namespace `CSD.Empirical.QM.Shor`,
foundational-triple-only, AxiomAudit-pinned):**
- **S1.** `mulOracle a : EuclideanSpace ℂ (ZMod N) → ...`, the genuine permutation `|y⟩ ↦ |a·y⟩`
  for a unit `a : (ZMod N)ˣ` (coordinate pulled back along `a⁻¹·y`); `mulOracle_basisState`,
  plus linearity (`mulOracle_smul`, `mulOracle_sum`). Genuine `ZMod N` work register, not a toy
  `Fin r` shift.
- **S2.** `ord a = orderOf a`, `omega a = qftω (ord a)`, `orbit j = a^j`, the cyclic shift
  `cycShift` (`= +1 mod r`); eigenvector `eigU s = (1/√r) ∑_j conj(ω)^{sj} |a^j⟩`;
  `mulOracle_eigU : mulOracle a (eigU s) = ω^s • eigU s` (reindex by `cycShift` + `conj ω = ω⁻¹`,
  `ω^r = 1`); `sum_eigU : (1/√r) ∑_s eigU s = |1⟩` (roots-of-unity orthogonality, geom-sum collapse).
- **S3.** `applyQFT`/`applyQFTinv` on `EuclideanSpace ℂ (Fin T)`; `phaseColumn`,
  `phaseColumn_apply`; `applyQFTinv_phaseColumn` (inverse-QFT inverts QFT via `qft_unitary` +
  `toLpLin_mul_same`/`toLpLin_one`); capstone `phase_estimation_exact : prob = 1`.
- **Bridge.** `qftω_div : qftω r = qftω T ^ (T/r)` for `r ∣ T` (`Complex.exp_nat_mul`);
  `eigenPhase_eq_phaseColumn` (eigenvalue-`ω_r^s` phase state = QFT column `s·(T/r)`); headline
  `shor_order_readout : prob (applyQFTinv (eigenphase state)) ⟨s·(T/r), _⟩ = 1`.

**M1.5 landed (`ShorCore.lean`, same namespace, foundational-triple-only, AxiomAudit-pinned):**
the full two-register joint state and the ideal-case (`r ∣ T`) output distribution.
- **Joint register.** `tensorCN φ ψ` (coordinate `φ c * ψ y`) on `EuclideanSpace ℂ (Fin T × ZMod N)`,
  the counting-only inverse QFT `qftInvCount` with the key reduction
  `qftInvCount_tensorCN : qftInvCount (tensorCN φ ψ) = tensorCN (applyQFTinv T φ) ψ`, and the Born
  marginal `probCount Φ c = ∑_y ‖Φ (c, y)‖²`.
- **Faithful state.** `jointModexp a` (`|x⟩|y⟩ ↦ |x⟩|a^x·y⟩`, a genuine permutation) with
  `jointModexp_initial : jointModexp a (uniformCount ⊗ |1⟩) = postModexpState = (1/√T) ∑_x |x⟩|a^x⟩`.
- **Eigenbasis.** `orbit_injective`, `eigU_norm : ‖u_s‖ = 1`, the roots-of-unity inversion
  `basisState_apow_eq : |a^x⟩ = (1/√r) ∑_s ω^{sx} u_s` (dual to `sum_eigU`),
  `postModexp_eq_eigenbasis = (1/√r) ∑_s (phase column s·T/r) ⊗ u_s`, and after the inverse QFT
  `qftInvCount_postModexp = (1/√r) ∑_s |s·T/r⟩ ⊗ u_s`.
- **Headline `shor_order_distribution`:** `probCount (qftInvCount postModexpState) ⟨s·(T/r)⟩ = 1/r`
  for each `s < r` (via `eigU_norm` + `bridgeIndex_inj`), with `shor_order_distribution_zero`
  giving `0` off the `r` multiples. This is the **uniform-`1/r`** marginal M1 deferred.

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

### S1 — Modular-exponentiation oracle as a permutation unitary  **[Q]**, medium — **DONE 2026-06-06**
- Work register `EuclideanSpace ℂ (ZMod N)` (or `Fin N`). `mulOracle a : |y⟩ ↦ |a·y⟩` is the
  permutation induced by multiplication by the unit `a` on `ZMod N`; a genuine permutation
  matrix, hence unitary. Then `|x⟩|y⟩ ↦ |x⟩|a^x · y⟩` on the joint register.
- Mathlib: `Equiv.mulLeft₀` / unit multiplication is a bijection; permutation matrices are
  unitary. Clean.

### S2 — Eigenstructure of "multiply by a"  **[Q]**, medium — **DONE 2026-06-06**
- `u s := (1/√r) ∑_{j<r} ω_r^{-sj} |a^j⟩` is an eigenvector of `mulOracle a` with eigenvalue
  `ω_r^s = exp(2πi s/r)`; and `(1/√r) ∑_{s<r} u s = |1⟩`.
- Reuses `Fourier.qftω` and the roots-of-unity machinery from `Fourier.lean` (`qftω_primitive`,
  the geometric-sum orthogonality). This is the hinge that turns order-finding into phase
  estimation.

### S3 — Phase estimation, clean case `r ∣ T`  **[Q]**, medium — **DONE 2026-06-07 (full distribution)**
- With `T = 2^t` and `r ∣ T`: starting from uniform counting register, applying the oracle
  (controlled powers = modexp), then `QFT⁻¹`, the measured value `c` is uniform on the `r`
  multiples `{s·T/r : s < r}`; `prob(c = s·T/r) = 1/r` exactly.
- Proof is a finite geometric sum collapse, the same `∑_k ζ^k = T·[ζ=1]` orthogonality proved
  for `qft_unitary` (`Fourier.lean`). **No new hard analysis.** This is the genuine quantum
  core of Shor and the cleanest defensible "Shor's algorithm (ideal case)" deliverable.
- **Landed (S3-core + bridge, M1):** inverse-QFT exactness (`phase_estimation_exact`) and the
  eigenphase-to-column bridge (`shor_order_readout`): inverse-QFT of the eigenvalue-`ω_r^s`
  counting phase state yields the basis state `s·(T/r)` with `prob = 1`. This reads the order's
  phase `s/r` exactly off a **single** eigenvalue branch.
- **Landed (full distribution, M1.5 DONE 2026-06-07):** the **uniform-`1/r`** distribution over
  `{s·T/r : s < r}` on the genuine two-register modexp state. `shor_order_distribution`:
  `probCount (qftInvCount postModexpState) ⟨s·(T/r)⟩ = 1/r`; `shor_order_distribution_zero`: `0`
  off the `r` multiples. The joint register (`tensorCN`, `qftInvCount`), the faithful state
  (`jointModexp_initial`), the roots-of-unity inversion (`basisState_apow_eq`), and `‖u_s‖ = 1`
  (`eigU_norm`) are all in `ShorCore.lean`, foundational-triple-only.
- **S4 (general `r ∤ T`) DONE 2026-06-07:** the single-eigenvector Dirichlet-kernel `≥ 4/π²` lower
  bound is now landed; see §S4 below.

### S4 — Phase estimation, general case `r ∤ T`  **[Q]**, medium-hard — **DONE 2026-06-07**
- `prob(c) ≥ 4/π²` for `c` the closest integer to `φ·T` (single eigenvector, phase `φ`).
  Dirichlet-kernel lower bound. Landed in `ShorCore.lean` (namespace `CSD.Empirical.QM.Shor`,
  foundational-triple-only, AxiomAudit-pinned). Mathlib analytic support used exactly as scoped:
  `Complex.norm_exp_I_mul_ofReal_sub_one`, `Real.mul_abs_le_abs_sin` (Jordan), `Real.abs_sin_le_abs`
  (`|sin t| ≤ |t|`), `geom_sum_eq` (+ imports `Trigonometric/Bounds`, `Real/Pi/Bounds`).
- **Landed exports:**
  - `phaseStateR φ = (1/√T) ∑_x e^{2πi φ x} |x⟩` — the counting-register phase state for a real
    phase `φ` (general-`r` analogue of the `eigenPhase` state, no longer required to be an exact
    QFT column).
  - `applyQFTinv_phaseStateR_apply` — the Dirichlet amplitude
    `applyQFTinv (phaseStateR φ) c = (1/T) ∑_{x<T} e^{2πi(φ−c/T)x}` (the two `(√T)⁻¹` collapse to
    `T⁻¹`; `e^{2πiφx}·conj(ω_T)^{xc}` merges to `e^{2πi(φ−c/T)x}`).
  - `prob_phaseStateR_eq` — off-resonance closed form `prob = T⁻² · sin²(πδT)/sin²(πδ)` with
    `δ = φ−c/T` (geom-sum + `norm_exp_I_mul_ofReal_sub_one`); the `sin(πδ) ≠ 0` side-hypothesis is
    discharged inside the headline from `0 < |πδ| < π`.
  - `phase_estimation_lower_bound (φ : ℝ) (c : Fin T) : |φ − c/T| ≤ 1/(2T) → 4/π² ≤ prob …` — the
    HEADLINE. `δ=0` gives `prob=1 ≥ 4/π²` (via `Real.pi_gt_three`); else Jordan
    (`sin²(πδT) ≥ (2δT)²`) over `sin²(πδ) ≤ (πδ)²` yields `≥ 4/π²`.
  - `shor_phase_estimation_lower_bound {r} (hr : 0 < r) (s : Fin r) (c : Fin T)` — the Shor
    corollary at `φ = s/r`.
- **Honest scope (delivered as stated):** single-eigenvector / generic-`φ` bound. The full
  two-register `r∤T` measurement marginal — controlling the cross-terms across the `r` eigen-branches
  `u_s` to get the per-outcome probability of the *joint* state — is **beyond S4 and not done**. This
  closes the last *quantum* piece of order-finding; S5/S6/S7 (the classical number-theory tail)
  remain.

### S5 — Period recovery of `r`  **[NT]** — **DONE 2026-06-07 (uniqueness route)**
- The measured count `c` **determines** the order `r`. Landed in `ShorRecovery.lean` (new
  standalone file, namespace `CSD.Empirical.QM.Shor`, foundational-triple-only, AxiomAudit-pinned).
- **Route deviation (documented in-file):** rather than build the Legendre converse on Mathlib's
  `GenContFract` (Mathlib has only the forward `abs_sub_convergents_le'`), S5 proves the
  recovery-correctness content by the elementary **uniqueness** argument:
  - `abs_sub_rat_ge` — distinct fractions `a/b`, `c/d` (positive denominators) differ by at least
    `1/(b·d)` (the numerator `a·d − c·b` is a nonzero integer).
  - `approx_unique` — two fractions within `1/(2T)` of the same `x` with `b·d < T` coincide.
  - **`shor_period_determined` (headline):** the true `s/r` and any candidate `s'/r'`, both in
    lowest terms with `r·r' < T` and both within `1/(2T)` of `c/T`, satisfy `s = s'` and `r = r'`.
    So `r` is the unique denominator consistent with the measurement. For Shor `T ≥ N² > r²`
    gives `r, r' < √T`, so `r·r' < T` holds with slack and S4's `|s/r − c/T| ≤ 1/(2T)` feeds in.
- **Honest scope:** this is the information-theoretic *determination* of `r` (why recovery is
  possible: a unique consistent answer). It is NOT the constructive continued-fraction
  *computation* of `r` from `c/T`; the constructive Legendre-on-`GenContFract` extraction is a
  heavier, separately-scoped alternative, deferred.
- **Composition with S4:** S4 gives `prob ≥ 4/π²` for the closest-integer event
  `|c/T − s/r| ≤ 1/(2T)`; S5 shows that event determines `r`. So a single run determines `r` with
  probability `≥ 4/π²`. (The combined cross-file theorem is a trivial follow-up.)

### S6 — Factoring from order: nontrivial square root of unity  **[NT]** — **DONE 2026-06-07**
- `x² ≡ 1 (mod N)`, `x ≢ ±1` ⟹ `gcd(x-1, N)` is a proper nontrivial divisor. Landed in
  `ShorRecovery.lean` (`nontrivial_factor`: `1 < Int.gcd (x-1) N ∧ Int.gcd (x-1) N < N ∧
  Int.gcd (x-1) N ∣ N`), plus the existential corollary `N_has_nontrivial_factor`. Pure number
  theory over ℤ; route: `N ∣ (x-1)(x+1)`, `g=N ⟹ N∣x-1` (contra), `g=1 ⟹ N coprime (x-1) ⟹
  N∣x+1` (contra), via `Int.gcd_dvd_left/right`, `Int.isCoprime_iff_gcd_eq_one`,
  `IsCoprime.dvd_of_dvd_mul_left`. Both AxiomAudit-pinned, foundational-triple-only.
  Independently audited SOUND (non-vacuous at N=8→gcd 2, N=15→gcd 3; coprime-cancellation
  direction verified). This is the reduction "order-finding ⟹ factoring": for even order `r`
  of a unit `a` with `a^(r/2) ≢ ±1`, `x = a^(r/2)` satisfies the hypotheses.
- **Bridge DONE 2026-06-07** (`ShorRecovery.lean`): `even_order_sqrt_unity` (for a unit `a` of
  even order with `a^(r/2) ≢ ±1 mod N`, `x = a^(r/2)` satisfies S6's `hsq/hne1/hne2`, via
  `(a^(r/2))² = a^r = 1` + `ZMod.intCast_zmod_eq_zero_iff_dvd`) and `shor_factor_of_even_order`
  (composes the bridge with `nontrivial_factor`: even order ⟹ `gcd(a^(r/2)-1, N)` a proper
  nontrivial divisor). Both AxiomAudit-pinned, foundational-triple-only. Independently audited
  SOUND with the full `(ZMod 15)ˣ` witness (a=4, order 2, x=4 → gcd 3). This is the complete
  classical reduction **order-finding ⟹ factoring**.

### S7 — Random-`a` success probability ≥ 1/2  **[NT]**, hard — **PLANNED (decomposed) 2026-06-07**
For `N` odd composite and `a` uniform in `(ZMod N)ˣ`: `P[r even ∧ a^(r/2) ≢ -1] ≥ 1/2`. Framed by
**counting** (`2 · #GOOD ≥ #(ZMod N)ˣ`), no measure theory. The single largest tranche; pure
finite group theory.

**Mathlib coverage (grounded 2026-06-07):** the foundations exist —
`MulEquiv.prodUnits` (`(M×N)ˣ ≃* Mˣ × Nˣ`) + `ZMod.chineseRemainder` (CRT for units),
`ZMod.isCyclic_units` (`(ZMod pᵏ)ˣ` cyclic for odd prime `p`), `Nat.totient_even`,
`orderOf_eq_totient` (count of order-`d` elements in a cyclic group = `φ(d)`). The v₂-distribution
count and the `−1` characterisation are bespoke.

**Design pivot:** the per-factor bound `#{a : v₂(ord a) = k} ≤ |G|/2` holds ONLY for **cyclic**
`G` (it fails for `(Z/2)ⁿ`), so the proof needs the prime-power (cyclic) decomposition, not just any
two coprime factors. **Milestone `S7★`: `N = p^α · q^β`, two distinct odd prime powers** (the
RSA-semiprime case) — captures the full essence with exactly two cyclic factors, avoiding the
indexed-product-over-all-primes machinery. General `m ≥ 2` (indexed `∏ᵢ`, bound `1 − 1/2^{m−1}`)
is a generalisation flagged as stretch.

**Sub-tranches (execute bottom-up; each a scoped two-agent loop):**
- **S7b — per-cyclic-factor v₂-distribution bound — DONE 2026-06-08** (`ShorRandomA.lean`,
  `card_v2_orderOf_le`, foundational-triple-only, AxiomAudit-pinned). In a finite cyclic group `G`
  of even order, `2 · #{a ∈ G : v₂(orderOf a) = k} ≤ |G|` for every `k`. **Route taken: generator**
  (not totient) — the power map `t : Fin n ↦ g^t` is a bijection (`Equiv.ofBijective` via
  `pow_injOn_Iio_orderOf`), the `v₂=k` class transports to a parity class of `Fin n`: the `k = c`
  class (`c = v₂ n`) injects into the odd residues, every other class into the even residues, both
  of size `n/2` (`card_odd_fin`/`card_even_fin`); valuation fact `v2_orderOf_pow`
  (`v₂(orderOf g^t) = c − min(c, v₂ t)` via `orderOf_pow` + `Nat.factorization_div`/`_gcd`).
  Independently audited SOUND: contentful and TIGHT at `ℤ/6` (`2·3 = 6`), and `hev` proved
  load-bearing (theorem FALSE without it: `ℤ/3` gives `2·3 > 3`).
- **S7c — the `−1` characterisation (abstract cyclic core) — DONE 2026-06-08** (`ShorRandomA.lean`,
  `pow_half_eq_orderTwo_iff`, foundational-triple-only, AxiomAudit-pinned). In a finite cyclic group
  with order-2 element `z`, for `R` even (`≠0`) with `ord a ∣ R`: `a^(R/2) = z ⟺ v₂(ord a) = v₂(R)`.
  Route: `a^(R/2)` is a √1 (`a^R=1`), so `∈ {1,z}` (cyclic ⟹ order-2 singleton via
  `IsCyclic.card_orderOf_eq_totient`, `φ(2)=1`); `a^(R/2)=1 ⟺ ord a ∣ R/2 ⟺ v₂(ord a) < v₂(R)`
  (private ℕ-valuation helper `dvd_half_iff_v2_lt` via `Nat.factorization_le_iff_dvd` /
  `Nat.factorization_div`); so `=z ⟺ ≠1 ⟺ v₂ equal`. Independently audited SOUND with both-true
  (`C₄`: a=g,R=4) and both-false (a=z,R=4) witnesses (iff genuinely two-directional), reproduced on
  `C₈`; `hz`/`hdvd` proved load-bearing. The `z := −1`-in-each-cyclic-factor instantiation and the
  CRT `−1 ↔ (−1,−1)` split are deferred to S7a/S7d.
- **S7a — two-factor CRT framing — DONE 2026-06-08** (`ShorRandomA.lean`, foundational-triple-only,
  AxiomAudit-pinned; cyclicity-agnostic, any coprime `m n`). `unitsCRT h : (ZMod (m·n))ˣ ≃*
  (ZMod m)ˣ × (ZMod n)ˣ` (`Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv |>.trans
  MulEquiv.prodUnits`); `unitsCRT_orderOf` (`ord a = lcm(ord a₁, ord a₂)` via `MulEquiv.orderOf_eq`
  + `Prod.orderOf`); `unitsCRT_neg_one` (`-1 ↦ (-1,-1)`, via `Units.ext` + ring `map_neg`/`map_one`);
  `card_units_mul` (`#(ZMod(m·n))ˣ = #(ZMod m)ˣ · #(ZMod n)ˣ`). Independently audited SOUND: iso
  confirmed the genuine CRT map (witness `7 ↦ (1,2)` rules out identity/swap), `-1 ↦ (2,4)`, card
  `8=2·4`, `lcm(2,4)=4≠8`, coprimality load-bearing.
- **S7d — assembly + headline `S7★` (split into S7d-1 + S7d-2).**
  - **S7d-1 — diagonal count — DONE 2026-06-08** (`ShorRandomA.lean`, `two_mul_card_diag_le`,
    foundational-triple-only, AxiomAudit-pinned). Abstract: for `G₁ × G₂` (`G₂` cyclic even),
    `2 · #{p : v₂(ord p.1) = v₂(ord p.2)} ≤ |G₁|·|G₂|`. Route: `Fintype.sum_prod_type` +
    `Finset.card_filter` decompose the product-filter into `∑_{a₁} #{a₂ : v₂(ord a₂)=v₂(ord a₁)}`,
    each fiber bounded by S7b (`card_v2_orderOf_le` at `k = v₂(ord a₁)`), then `Finset.sum_const`.
    Only `G₂` needs cyclic+even. Audited SOUND: diagonal non-empty (`(1,1)`), bound tight at `ℤ/2`
    (`2·2 = 4`), `Even` hypothesis load-bearing (`ℤ/3` would give false `2·9 ≤ 9`).
  - **S7d-2a — the BAD characterisation (abstract) — DONE 2026-06-08** (`ShorRandomA.lean`,
    `bad_iff_v2_eq`, foundational-triple-only, AxiomAudit-pinned). For `p : G₁×G₂` (both cyclic, with
    order-2 `z₁,z₂`): `¬(Even (orderOf p) ∧ p^(orderOf p/2) ≠ (z₁,z₂)) ⟺ v₂(ord p.1) = v₂(ord p.2)`.
    Route: `Prod.orderOf` (= lcm), `Nat.factorization_lcm` (v₂(lcm)=max), per-factor S7c
    (`pow_half_eq_orderTwo_iff`), `omega` case split on `Even r`. Audited SOUND with both-true `(g,g)`
    and both-false `(g,z)` witnesses (iff genuinely separates BAD/GOOD).
  - **S7d-2b-i — abstract `2·#GOOD ≥ |G₁×G₂|` — DONE 2026-06-08** (`ShorRandomA.lean`,
    `two_mul_card_good_ge`, foundational-triple-only, AxiomAudit-pinned). `#BAD = #diagonal`
    (`Finset.filter_congr` on `bad_iff_v2_eq`) + S7d-1 (`two_mul_card_diag_le`) ⟹ `2·#BAD ≤ |G₁||G₂|`;
    `Finset.card_filter_add_card_filter_not` + `omega` ⟹ `|G₁||G₂| ≤ 2·#GOOD`. (`open Classical in`
    for the non-decidable filter; no axiom widening.) Audited SOUND: GOOD non-empty (`(g,1)`), bound
    bites (`16 ≤ 2·#GOOD`), direction + predicate genuine, `hz₁/hz₂` load-bearing.
  - **S7d-2b-ii — the `(ZMod N)ˣ` headline `S7★`.** Transport `two_mul_card_good_ge` across
    `unitsCRT` (GOOD over `(ZMod N)ˣ` ↔ product GOOD, `(z₁,z₂) = unitsCRT(−1)` via `unitsCRT_neg_one`
    + `MulEquiv` orderOf/pow preservation), instantiate `m=p^α, n=q^β` odd prime powers
    (`ZMod.isCyclic_units` + `Nat.totient_even`, `orderOf (−1) = 2`); conclude
    `#(ZMod N)ˣ ≤ 2·#{a : Even (ord a) ∧ a^(ord a/2) ≠ −1}`. The remaining piece (last one for `S7★`).

**Honest cost / recommendation:** even `S7★` is the largest single tranche of the Shor effort, pure
number theory (not physics). Shor's *correctness* is already morally complete (order ⟹ factor done;
per-run phase concentration done); S7 is the *success-amplification* guarantee. Recommend executing
**S7b first** (independent, reusable cyclic-group counting), then S7c, then S7a+S7d, each as a
scoped expert+auditor loop — and reassessing after S7b whether to push to the full `S7★`/general-`m`
or stop at a defensible milestone.

### Assembly — `shor_factors`
- Combine S6 + (S3/S4 + S5) + S7: the algorithm outputs a nontrivial factor of `N` with
  probability `≥ Ω(1/log N)` (the `1/log N` from `O(log N)` repetitions to amplify the
  per-run constant). Headline theorem; AxiomAudit-pinned.

## 2. Dependency graph

```
S1 oracle ─► S2 eigenstructure ─► S3 phase-est (r∣T)  ──┐  [M1: quantum core, ideal — DONE]
                                  └► S4 phase-est (r∤T) ─┤  [S4 DONE: quantum core, general]
                                       S5 CF recovery ───┤  [M2: order-finding, general — S5 open]
S6 sqrt-of-unity factor ───────────────────────────────┤
S7 random-a ≥ 1/2 ─────────────────────────────────────┴► Assembly shor_factors  [M3: factoring]
```

## 3. Milestones and honest recommendation

- **M1 = S1+S2+S3 (quantum core, ideal `r ∣ T`). DONE 2026-06-06; M1.5 DONE 2026-06-07.**
  Self-contained, reuses `Fourier.lean`'s roots-of-unity orthogonality directly, no new hard
  analysis. The in-character, finite-QM heart of Shor. Landed in `ShorCore.lean` as S1 (oracle) +
  S2 (eigenstructure) + S3-core/bridge (single-branch phase-estimation exactness) + **M1.5: the
  full ideal-case output distribution** (the `EuclideanSpace ℂ (Fin T × ZMod N)` joint register,
  the genuine modexp state, and the uniform-`1/r` measurement marginal `shor_order_distribution`).
  S3 is now fully closed for `r ∣ T`. **S4 (general `r ∤ T`, the Dirichlet-kernel `≥ 4/π²` bound)
  is the next open quantum piece.**
- **M2 = +S4+S5 (order-finding for any `r`). S4 DONE 2026-06-07; S5 open.** The Dirichlet-kernel
  `≥ 4/π²` lower bound (`phase_estimation_lower_bound`, the genuinely analytic real-analysis tranche)
  is landed; the only remaining M2 piece is the Legendre CF converse (Mathlib gap, must build).
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
