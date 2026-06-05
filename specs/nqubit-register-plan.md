# n-qubit register + quantum-algorithm branch — plan

The enabling infrastructure for the QM-validity algorithm tier (Deutsch–Jozsa, QFT, Grover,
Shor). Drafted 2026-06-05. Status: **planned, not started.** This is deliberate coverage
breadth (validity suite), separate from the D1/LF5 thesis work.

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

### R1 — register + basis + Born probability (foundation, low)
- `QReg n`, `basisState x := EuclideanSpace.single x 1`, `prob ψ z := ‖ψ z‖^2`.
- API: `prob_eq_inner_sq` (`prob ψ z = ‖⟨basisState z, ψ⟩‖²`), `sum_prob_eq_one` for unit ψ,
  basis inner products (`EuclideanSpace.inner_single_*`).

### R2 — Hadamard^⊗n and its action on |0…0⟩ (medium)
- `hadEntry a b : ℂ := (-1)^(a*b) / √2`; `Hn x y := ∏ i, hadEntry (x i) (y i)`
  ( = `(-1)^(x·y)/√(2^n)` ).
- **`Hn_mulVec_zero` (key):** `(Hn *ᵥ basisState 0ⁿ) y = 1/√(2^n)` — the uniform
  superposition. Via `mulVec_single` + `∏ᵢ hadEntry (yᵢ) 0 = ∏ᵢ (1/√2)`. (Does *not* need
  unitarity.)

### R3 — character orthogonality ⟹ Hn unitary (the meaty lemma, medium–hard)
- **`hadamard_orthogonality`:** `∑ y : (Fin n → Fin 2), (-1)^((x ⊕ x')·y) = if x = x' then 2^n else 0`.
  Route: `Finset.prod_univ_sum` to factor `∑_{y:Π} ∏ᵢ fᵢ(yᵢ) = ∏ᵢ ∑_{yᵢ} fᵢ(yᵢ)`, then each
  qubit factor `∑_{b:Fin 2} (-1)^{(xᵢ⊕x'ᵢ)b} = 1 + (-1)^{xᵢ⊕x'ᵢ} = (2 if xᵢ=x'ᵢ else 0)`.
- `Hn_unitary` (`Hnᴴ * Hn = 1`) from it, so the circuit's probabilities are legitimate.
- *Risk:* the Pi-sum/product factoring + the `(-1)^…` bookkeeping over `Fin 2`. This is the
  one genuinely fiddly lemma; everything downstream is assembly.

### R4 — phase oracle + Deutsch–Jozsa (the first algorithm, medium)
- `phaseOracle (f : (Fin n → Fin 2) → Fin 2) := diagonal (fun x => (-1)^(f x))` (unitary,
  diagonal, easy).
- **`deutsch_jozsa`:** the measured amplitude of `0ⁿ` after `Hn ∘ phaseOracle f ∘ Hn` on
  `|0ⁿ⟩` is `(1/2^n) ∑_x (-1)^{f x}`; hence
  `prob (…) 0ⁿ = 1` if `f` constant, `= 0` if `f` balanced.
  Clean route: `⟨0ⁿ| Hn Uf Hn |0ⁿ⟩ = (1/2^n) ∑_{x,x'} ⟨x|Uf|x'⟩ = (1/2^n) ∑_x (-1)^{f x}`
  (Uf diagonal; uses `Hn_mulVec_zero` both sides — character orthogonality only needed for
  the *probability legitimacy* via `Hn_unitary`).

### R5+ — later (each a tranche)
- **QFT** (`ωⁿ` matrix, unitarity via roots-of-unity orthogonality — a ℂ-analogue of R3),
  then **Grover** (oracle + diffusion, amplitude `sin((2k+1)θ)` iteration). Medium–hard.
- **Shor**: QFT + modular exponentiation oracle + **continued-fraction period recovery** +
  success bound `Ω(1/log N)`. The quantum core is reachable post-QFT; the classical
  post-processing (continued fractions, the order-recovery probability) is a **large
  number-theory build** and is the real cost of "all the way to Shor".

## 3. Dependency graph & estimate

```
R1 register ─► R2 Hn|0ⁿ⟩=uniform ─► R3 char-orthogonality ⟹ Hn unitary ─► R4 Deutsch–Jozsa
                                                                  └─► R5 QFT ─► Grover ─► Shor
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
