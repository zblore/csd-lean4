# QM empirical-test plan: validating CSD against quantum experiment

Plan for an empirical-prediction regression suite. Goal: when LF4 lands
the concrete ontic instantiation, the predictions delivered by CSD
should match QM, and should match laboratory experiment where QM has
been verified. The Lean module is the live regression target; this
document is the roadmap.

This work is independent of the TN4 / Sigma1 / LF4 paper sequence (per
the 2026-05-19 paper-sequencing decision, see `[[project-lf4-decisions]]`):
unblocked Lean thread parallel to `specs/projectivization-plan.md`.

## 0. Goal and scope

**Goal.** Build a Lean-checkable empirical-prediction suite covering:

1. Landmark QM experiments (Bell/Aspect, Stern-Gerlach, Mach-Zehnder, GHZ, Hardy).
2. Foundational QM theorems with empirical content (Tsirelson bound, no-cloning, no-signalling).
3. Quantum algorithms in the CSD reading (Deutsch-Jozsa, Grover, QFT, Shor).

**Scope rule.** Each prediction is a Lean `theorem` whose statement
expresses the experimental quantity in CSD-foundational form (volume
ratios of effect functions against pushed-forward preparation measures,
per LF2's `effectProjFn` and `OperationalPackage.fromPreparation`),
*not* a textbook re-derivation in matrix QM. The CSD-specific question
is whether the volume-ratio account reproduces the QM numerics; the
empirical-test suite is the regression that answers it.

**Layered status.** Predictions are tagged:

- **PROVED** — Lean theorem in place, AxiomAudit-pinned.
- **PROVED-LF3** — content exists inside LF3 but not yet named as
  an empirical-test export.
- **READY** — actionable now without LF4, no new structural debt.
- **LF4-blocked** — requires concrete ontic instantiation per LF4 §8.
- **INFRA-blocked** — requires new infrastructure (multi-qubit, QFT,
  modular arithmetic, etc.) beyond LF4.

## 1. Phase A — Bell family (actionable now, no LF4 dependency)

All Phase A content lives in `CsdLean4/Empirical/Bell.lean` (Cat-3
unless promoted to Framework Cat-2, see per-item notes). Consumes
LF3's `correlation_eq_neg_dot`, `marginal_a_eq_half`,
`marginal_b_eq_half`, `no_signalling_strong_readout_a/b`. The new work
is Tsirelson (A6); A1–A5 are packaging.

| # | Prediction | Statement | Status | Source / verification |
|---|---|---|---|---|
| A1 | CHSH at Tsirelson bound | `∃ a a' b b' : DetectorSetting, |S(a,a',b,b')| = 2√2` on the singlet | **DONE 2026-05-19** (`chsh_singlet_tsirelson_bound`) | Bell 1964 (bound), Tsirelson 1980 (saturation), Aspect 1982 (experimental) |
| A2 | CHSH classical bound violated | `2√2 > 2`, named as the empirical violation gap | **DONE 2026-05-19** (`chsh_classical_bound_violated`) | Bell 1964 |
| A3 | No-signalling, side A | Marginal of A independent of B's setting | **DONE 2026-05-19** (`no_signalling_alice`) | Aspect 1982; loophole-free: Hensen 2015, Giustina 2015, Shalm 2015 |
| A4 | No-signalling, side B | Symmetric | **DONE 2026-05-19** (`no_signalling_bob`) | same |
| A5 | Singlet marginal uniform | `P(A = +|a) = 1/2` for any unit `a` | **DONE 2026-05-19** (`singlet_marginal_alice`, `singlet_marginal_bob`) | Textbook |
| A6 | Tsirelson upper bound | For any pure 2-qubit `|ψ⟩` and unit `a, a', b, b'`, `|S(a,a',b,b')| ≤ 2√2` | pending (~1 day; Cat-2 candidate) | Tsirelson 1980 |

A6 routes through the operator identity `(σ_a + σ_{a'})² + (σ_a − σ_{a'})² ≤ 4`
plus Cauchy-Schwarz on `⟨ψ | · | ψ⟩`. It is QM-generic (no CSD
content), so Framework Cat-2 promotion is on the table; defer the
classification call until the proof is in place.

**Exit criterion for Phase A.** `Bell.lean` builds; all six items are
named, docstringed with experimental provenance (year + reference),
and pinned in AxiomAudit. The Bell paragraph in `README.md` is
updated.

**Phase A1-A5 landed 2026-05-19** in commit `<filled at commit time>`.
A1-A5 are foundational-triple-only (eight AxiomAudit `#guard_msgs`
regressions added under `### Empirical predictions (Bell family,
Phase A1-A5)` in `Tests/AxiomAudit.lean`). Library build `lake build`
(2956 jobs) clean; test build `lake build CsdLeanTests` (2955 jobs)
clean. A6 (Tsirelson upper bound) remains as the only Phase A item
open.

## 2. Phase B — single-experiment Born predictions (LF4-blocked)

These become meaningful once LF4 §8 supplies the concrete
(`SigmaSpace`, `μL`, `Φ`, `π`) for the relevant Hilbert dimension.
Until then, they can be stated as conditional theorems over an
abstract `SectorData` matching the relevant N, but the *physical*
content is sealed behind the LF4 discharge.

### 2.1 `SingleQubit.lean` — N = 2

| # | Prediction | LF4 prerequisite |
|---|---|---|
| B1 | Stern-Gerlach: `P(↑|ẑ, |+ẑ⟩) = 1`, `P(↓|ẑ, |+ẑ⟩) = 0`, `P(↑|x̂, |+ẑ⟩) = 1/2` | N=2 `SectorData` instantiation |
| B3 | Malus's law (operational form): `P(↑|θ, |+ẑ⟩) = cos²(θ/2)` | N=2 `SectorData` + angle parameterisation |

### 2.2 `Interference.lean` — single-photon two-mode

| # | Prediction | LF4 prerequisite |
|---|---|---|
| B4 | Mach-Zehnder visibility = 1 for pure single-photon | N=2 `SectorData` instantiated as two-mode bosonic, beam-splitter unitary |

### 2.3 `NoCloning.lean` — general QM theorem

| # | Prediction | Status |
|---|---|---|
| B2 | No-cloning: no `U : H ⊗ H → H ⊗ H` unitary with `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for all `|ψ⟩` | READY (Cat-2 candidate; ~1 day) |

Proof: contradiction from linearity plus `‖|ψ⟩ ⊗ |0⟩‖ = ‖|ψ⟩ ⊗ |ψ⟩‖`
applied to two non-orthogonal states.

### 2.4 `BornNumerical.lean` — Born rule for named 2-qubit states

| # | Prediction | LF4 prerequisite |
|---|---|---|
| B5a | Bell-basis Born numerics: explicit probability tables for |Φ±⟩, |Ψ±⟩ under standard projective measurements | LF4 §8 + LF3 → LF2 chain wiring |
| B5b | Werner state predictions: depolarising-noise spectrum `p|ψ⟩⟨ψ| + (1−p)I/4` | LF4 §8 |

## 3. Phase C — multipartite and algorithms (INFRA-blocked + LF4-blocked)

### 3.1 `Multipartite/GHZ.lean`

| # | Prediction | Status |
|---|---|---|
| C5 | GHZ paradox: 3-qubit `(|000⟩ + |111⟩)/√2` shows Mermin's all-or-nothing correlation inconsistent with any local-realistic assignment | INFRA-blocked (3-qubit Hilbert space + multi-Pauli observables) |

### 3.2 `Multipartite/Hardy.lean`

| # | Prediction | Status |
|---|---|---|
| C6 | Hardy's 9% paradox: specific non-maximally-entangled 2-qubit state exhibits a 9% paradoxical outcome under local-realism | LF4 + named 2-qubit state setup |

### 3.3 `Algorithms/` subdirectory

The goal here is *not* to reproduce textbook QM derivations but to express the algorithmic predictions in CSD-foundational form. The interesting question: how does the textbook story (amplitude interference) translate to the volume-ratio account?

| # | Algorithm | Lean target | Status |
|---|---|---|---|
| C1 | Deutsch-Jozsa | `f` balanced vs constant: 1-query discrimination probability | INFRA-blocked (n-qubit + oracle) |
| C2 | Grover | `O(√N)` query complexity to find marked element | INFRA-blocked (controlled gates + amplitude analysis) |
| C3 | Quantum Fourier Transform | `|x⟩ ↦ (1/√N) Σ_y e^{2πi xy/N} |y⟩` | INFRA-blocked (many-qubit + roots of unity) |
| C4 | Shor order-finding | Success probability `Ω(1/log N)` for period extraction from `f(x) = a^x mod N` | INFRA-blocked (QFT + modular arithmetic + continued fractions) |

Each of these will likely become its own paper-and-Lean track. Listed here so the LF4 infrastructure choices don't accidentally close off the natural multi-qubit + circuit-model extensions.

## 4. Recommended execution order

1. **Spec doc landed (this file).**
2. **`Bell.lean` Phase A packaging commit.** A1–A5 (re-export PROVED-LF3 content with empirical provenance docstrings, AxiomAudit pinning). A2 is a `theorem` carrying the numerical gap. ~2h focused.
3. **`Bell.lean` A6 (Tsirelson upper bound).** New theorem; the load-bearing one in Phase A. ~1 day focused.
4. **`NoCloning.lean` B2.** No-cloning is QM-generic and doesn't need LF4. ~1 day focused.
5. **Pause for LF4.** Phases B (rest) and C are queued behind LF4 §8 (`SectorData` instantiation) and per-experiment infrastructure.

After step 4, the immediately-actionable empirical work is exhausted
until LF4 progresses. The pre-LF4 deliverable is: Bell-family fully
proved, Tsirelson upper bound proved, no-cloning proved. That is a
substantial empirical-status milestone: the Bell experiments are the
canonical foundational benchmarks for QM, and CSD passing them is the
first hard test the framework needs to clear.

## 5. Long-term: EFT and CSD-specific predictions

CSD claims to be a finite EFT of an ontic structure. Standard QM is
recovered in the appropriate limit. The empirical tests above are the
"CSD reduces to QM in regime X" checks. Two additional categories
worth listing for completeness:

### 5.1 EFT-level CSD predictions matching QM

These are the QM-equivalence checks above. The empirical content is
identical to QM; the CSD-specific content is the volume-ratio account
of where the numbers come from.

### 5.2 Potential CSD departures from QM

The structural debts (`[[project-structural-debts]]`) include V ≈ 1 − I
and G3b: regimes where CSD may not exactly reproduce QM. If any of
these become numerically pinned, they would become **predictions
distinguishing CSD from QM** rather than empirical-verification checks.
This is post-LF4 paper-track territory (TN0 §9.3 forwarding remark);
not yet scope here, but noted so the test infrastructure is structured
not to assume CSD = QM identically.

## 6. Naming conventions

- Each theorem carries an experimental-source docstring: `**Experimental verification:** Aspect 1982, Phys. Rev. Lett. 49, 91`.
- Top-of-file `Category:` declaration per `CONVENTIONS.md`.
- AxiomAudit `#guard_msgs` entries grouped under `/-! ### Empirical predictions -/`.

## 7. Files index

```
specs/qm-empirical-tests.md           -- this file
CsdLean4/Empirical/Bell.lean          -- Phase A: A1-A6
CsdLean4/Empirical/SingleQubit.lean   -- Phase B: B1, B3
CsdLean4/Empirical/Interference.lean  -- Phase B: B4
CsdLean4/Empirical/NoCloning.lean     -- Phase B: B2
CsdLean4/Empirical/BornNumerical.lean -- Phase B: B5
CsdLean4/Empirical/Multipartite/GHZ.lean
CsdLean4/Empirical/Multipartite/Hardy.lean
CsdLean4/Empirical/Algorithms/DeutschJozsa.lean
CsdLean4/Empirical/Algorithms/Grover.lean
CsdLean4/Empirical/Algorithms/QFT.lean
CsdLean4/Empirical/Algorithms/Shor.lean
```

`Tests/AxiomAudit.lean` gets a new `/-! ## Empirical predictions -/` section as items land.
