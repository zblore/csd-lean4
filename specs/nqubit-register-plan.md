# n-qubit register + quantum-algorithm branch — plan

The enabling infrastructure for the QM-validity algorithm tier (Deutsch–Jozsa, Simon, Bernstein–Vazirani,
QFT, Grover, Shor). Drafted 2026-06-05. Status: **COMPLETE 2026-06-08.** R1–R5 + Grover done 2026-06-06;
(Simon + Bernstein–Vazirani added 2026-06-26 — single-register Hadamard, reuse the R4 infra.)
the full **Shor's algorithm** (quantum core M1/M1.5/S4 + classical recovery S5 + factoring
S6 + random-`a` success S7/S7-gen + factoring capstone) done 2026-06-07/08. See
[`shor-plan.md`](shor-plan.md). This is deliberate coverage breadth (validity suite),
separate from the D1/LF5 thesis work.

## 0. Why / scope

The algorithms `C1–C4` in `qm-empirical-tests.md` are marked **INFRA-blocked**: there is no
n-qubit register in the corpus, only ad-hoc `Fin 2`, `Fin 2×Fin 2`, `Fin 2×Fin 2×Fin 2`
with `kron2`/`kron3`. Nothing is *conceptually* blocked — DJ/QFT/Grover are inner-product
linear algebra; Shor's tail is classical number theory. Build the register once and the
algorithms follow in sequence.

## 1. Design decisions

- **State space:** `QReg n := EuclideanSpace ℂ (Fin n → Fin 2)`. The index `Fin n → Fin 2`
  is the set of **bitstrings** (computational basis), `Fintype` + `DecidableEq` of
  cardinality `2^n`. Chosen over `Fin (2^n)` because the per-qubit / tensor structure
  (single-qubit gates, the Hadamard product `∏ᵢ`, the dot product `x·y`) is then
  first-class, which is exactly what the algorithms need. Inner product / norm come free
  from `EuclideanSpace`; Born prob `= ‖⟨basis z, ψ⟩‖² = ‖ψ z‖²`.
- **Gates:** `Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ` acting by `toEuclideanLin` / `*ᵥ`.
- **Location:** **Cat-1** (CSD-free) → `CsdLean4/Mathlib/QuantumInfo/Register.lean` (+ gates);
  algorithm theorems in `CsdLean4/Empirical/QM/Algorithms/` (matches the structure decision:
  infra → Mathlib staging, topics under QM). Namespace `QuantumInfo`.

## 2. Phases

### R1 — register + basis + Born probability (foundation, low) — **DONE 2026-06-05**
- `QReg n`, `basisState x := EuclideanSpace.single x 1`, `prob ψ z := ‖ψ z‖^2`.
- API: `prob_eq_inner_sq` (`prob ψ z = ‖⟨basisState z, ψ⟩‖²`), `normSq_eq_sum_prob`,
  `sum_prob_eq_one` for unit ψ, `basisState_apply` / `basisState_norm` / `prob_basisState`
  (a basis state is measured with certainty).
- File `CsdLean4/Mathlib/QuantumInfo/Register.lean`; `prob_eq_inner_sq` / `sum_prob_eq_one` /
  `prob_basisState` AxiomAudit-pinned (foundational triple). Both targets green.

### R2 — Hadamard^⊗n and its action on |0…0⟩ (medium) — **DONE 2026-06-05**
- `hadEntry a b : ℂ := (-1)^(a*b) / √2`; `Hn x y := ∏ i, hadEntry (x i) (y i)`;
  `applyHn ψ := toEuclideanLin Hn ψ`, `applyHn_apply` (coordinate sum form).
- **`Hn_apply_zero` (key):** `applyHn (basisState 0) y = (√2⁻¹)ⁿ` for every `y` — the uniform
  superposition. Via `Finset.sum_eq_single` collapse + `∏ᵢ hadEntry (yᵢ) 0 = ∏ᵢ (√2⁻¹)`.
  (Does *not* need unitarity.) File `Hadamard.lean`; `Hn_apply_zero` AxiomAudit-pinned. Green.

### R3 — character orthogonality ⟹ Hn unitary (the meaty lemma, medium–hard) — **DONE 2026-06-06**
- **`Hn_unitary` (`Hnᴴ * Hn = 1`):** the multi-qubit character orthogonality in matrix form;
  entrywise `∑_y H(x,y) H(y,x') = [x = x']`. So any Hadamard circuit's full output is a
  legitimate probability vector.
- **Route deviation (documented in the file):** proved via the *per-qubit factorisation*
  rather than a global XOR character sum — `Finset.prod_univ_sum` factors
  `∑_{y:Π} ∏ᵢ fᵢ(yᵢ) = ∏ᵢ ∑_{yᵢ} fᵢ(yᵢ)`, reducing to `n` copies of the single-qubit
  orthogonality `hadEntry_mul_sum : ∑_b H(b,a) H(b,a') = [a=a']`. This avoids defining
  bitwise ⊕ on bitstrings; the per-qubit sum *is* the character sum on `Fin 2`.
- Supporting: `hadEntry_comm` (symmetric), `hadEntry_conj` (real), `sqrt2_mul_self`,
  `Hn_conjTranspose` (`Hnᴴ = Hn`, Hermitian), and the free corollary `Hn_mul_self`
  (`Hn * Hn = 1`, `H^⊗n` is an involution). File `Hadamard.lean`; `Hn_unitary` +
  `Hn_mul_self` AxiomAudit-pinned (foundational triple). Both targets green.

### R4 — phase oracle + Deutsch–Jozsa (the first algorithm, medium)
- `phaseOracle (f : (Fin n → Fin 2) → Fin 2) := diagonal (fun x => (-1)^(f x))` (unitary,
  diagonal, easy).
- **`deutsch_jozsa`:** the measured amplitude of `0ⁿ` after `Hn ∘ phaseOracle f ∘ Hn` on
  `|0ⁿ⟩` is `(1/2^n) ∑_x (-1)^{f x}`; hence
  `prob (…) 0ⁿ = 1` if `f` constant, `= 0` if `f` balanced.
  Clean route: `⟨0ⁿ| Hn Uf Hn |0ⁿ⟩ = (1/2^n) ∑_{x,x'} ⟨x|Uf|x'⟩ = (1/2^n) ∑_x (-1)^{f x}`
  (Uf diagonal; uses `Hn_mulVec_zero` both sides — character orthogonality only needed for
  the *probability legitimacy* via `Hn_unitary`).

### R5 — Quantum Fourier transform, unitarity via roots-of-unity orthogonality — **DONE 2026-06-06**
- **`qft_unitary` (`Fᴴ * F = 1`):** `F j k = (1/√N) ω^{jk}`, `ω = exp(2πi/N)` a primitive
  `N`-th root of unity (`Complex.isPrimitiveRoot_exp`). Entrywise `(Fᴴ F) j j' = (1/N) ∑ₖ
  ω^{k(j'-j)} = [j=j']` is the **roots-of-unity orthogonality** `∑_{k<N} ζᵏ = N·[ζ=1]`
  (geometric series `geom_sum_eq`; `ζ^N=1` kills the `j≠j'` sum, `IsPrimitiveRoot.pow_inj`
  gives `ζ=1 ⟺ j=j'`). The ℂ-analogue of the R3 `±1`-character sum.
- Defined on a general level count `N` (not specialised to `2ⁿ`), so it is the discrete
  Fourier unitary directly; qubit case is `N=2ⁿ`. Supporting: `qftω_primitive`,
  `qftω_conj` (unimodular), `sqrtN_mul_self`, `qftMatrix_symm` (Fᵀ=F). File
  `Mathlib/QuantumInfo/Fourier.lean`; `qft_unitary` AxiomAudit-pinned (foundational triple).
  Both targets green. A finite `N×N` unitary throughout — EFT-regime, never field theory.

### R5+ — Grover's search algorithm — **DONE 2026-06-06**
- **Operators (genuine reflections on the `EuclideanSpace` inner-product structure):**
  `oracle w ψ = ψ - 2·(ψ w)·|w⟩` (`I - 2|w⟩⟨w|`), `diffusion ψ = 2·⟨s,ψ⟩·|s⟩ - ψ`
  (`2|s⟩⟨s| - I`, inversion about the mean), `groverStep = diffusion ∘ oracle`, with
  `uniformState |s⟩ = (1/√N)∑_z|z⟩`. Carried as `ℂ`-vectors; amplitudes real-valued throughout.
- **Symmetric-state plane:** `symState w a b = b·J + (a-b)·|w⟩` (`symState_apply`: amplitude `a`
  on `w`, `b` elsewhere). The operator action lemmas compute the step as a linear coefficient
  map: `oracle_symState` (`(a,b) ↦ (-a,b)`), `diffusion_symState` (mean inversion),
  `groverStep_symState` (`(a,b) ↦ ((N-2)/N·a + 2(N-1)/N·b, -2/N·a + (N-2)/N·b)`). The diffusion
  inner product is `⟨s, symState a b⟩ = (√N)⁻¹(a + (N-1)b)` (`inner_uniformState_symState`).
- **2D rotation single-step lemma (`groverStep_rotates`):** with `sin θ = 1/√N`,
  `cos θ = √(N-1)/√N`, one step is a rotation by `2θ`:
  `groverStep w (rotState w γ) = rotState w (γ + 2θ)`, where
  `rotState w γ = symState w (↑sin γ) (↑(cos γ/√(N-1)))`. Proved via the double-angle
  identities `cos 2θ = (N-2)/N` (`cos_two_theta`), `sin 2θ = 2√(N-1)/N` (`sin_two_theta`)
  and `sin/cos_add`. Iterate (`groverStep_iterate`) by induction:
  `(groverStep w)^[k] (rotState w θ) = rotState w ((2k+1)θ)`;
  `uniformState = rotState w θ` (`uniformState_eq_rotState`).
- **Headline `grover_success` (capstone):**
  `prob ((groverStep w)^[k] uniformState) w = sin²((2k+1)θ)` for `n ≥ 1`. AxiomAudit-pinned,
  **foundational-triple-only.** File `CsdLean4/Empirical/QM/Algorithms/Grover.lean`. Both
  targets green.
- **Consolidations (2026-06-06):** `uniformState_eq_hadamard` (`uniformState = applyHn
  (basisState 0)`, via `√(2ⁿ) = (√2)ⁿ` — ties the Grover entry point to the R2 Hadamard
  layer) and `grover_certain` (when `(2k+1)θ = π/2` the marked item is measured with
  probability `1`; the optimal `k ≈ (π/4)√N`). `grover_certain` AxiomAudit-pinned. The
  closest-integer rounding bound for general `N` remains downstream arithmetic, not formalised.
- **Honest scope.** QM-validity breadth on `QReg n = EuclideanSpace ℂ (Fin n → Fin 2)` (no
  `Fin (2^n)` fallback); `N = 2ⁿ` enters as the cardinality `∑_z (1:ℂ) = N`. Genuine Hilbert
  reflections, not degraded to plain `Fin _ → ℂ` functions.
- **Shor**: QFT + modular exponentiation oracle + **continued-fraction period recovery** +
  success bound `Ω(1/log N)`. The quantum core is reachable post-QFT; the classical
  post-processing (continued fractions, the order-recovery probability) is a **large
  number-theory build** and is the real cost of "all the way to Shor".

## 3. Dependency graph & estimate

```
R1 register ─► R2 Hn|0ⁿ⟩=uniform ─► R3 char-orthogonality ⟹ Hn unitary ─► R4 Deutsch–Jozsa
                                                                  └─► R5 QFT
R1 register ─► Grover (oracle + diffusion, sin²((2k+1)θ) capstone)  [DONE; QFT-independent]
                                                                          └─► Shor
```

R1–R4 (Deutsch–Jozsa, first algorithm with legitimate probabilities): **~2–3 sessions**,
the only fiddly piece being R3. QFT/Grover are comparable each. **Shor is a multi-tranche
build dominated by classical number theory, not QM.**

## 4. Honesty note

This is QM-validity breadth: it reproduces textbook quantum computing inside the formalism.
It advances *coverage*, not the CSD thesis (D1/LF5). The CSD-branch reading ("a circuit is a
composition of `Φ_U` volume-reshapings on `Σ`, ending in a context partition") could be
layered on later per `project_d1_measurement_reading`, which would make the algorithm work
double as dynamics content — but that is a separate, optional pass on top of the QM-branch
results here.
