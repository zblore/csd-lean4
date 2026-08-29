# Steane seven-qubit code — scoping and execution

**Status:** scoped and **EXECUTED 2026-08-29, same session as GK-3** (author instruction:
"Do GK3 then 4").

**Provenance.** Candidate 4 of the five from the 2026-08-28 algorithms discussion. The
pitch, verbatim: *"Steane seven-qubit CSS code. You have the three-qubit codes and Shor-9 by
concatenation. Steane introduces the CSS construction properly, which generalises the QEC
layer instead of adding a fourth instance."* Executed as the **first genuine instance of the
GK-3 stabiliser layer** (`specs/gottesman-knill-plan.md`) — the generalisation and the
instance landed the same day, in that order.

## Design

`Empirical/QM/QEC/Steane.lean` (3-Local), consuming Cat-1 `Stabilizer.lean`. The classical
Hamming `[7,4]` parity-check rows (`hammingRow`, columns = binary 1..7) drive everything:

* The stabiliser family: `steaneA`/`steaneB` split `𝔽₂⁶` into three `X`-type and three
  `Z`-type row combinations; the **CSS condition** `H Hᵀ = 0` (all nine row pairs
  orthogonal, kernel-checked by `decide`) makes the trivial sign function coherent — so
  GK-3's absorption/idempotence/trace/existence instantiate wholesale.
* `steane_code_dimension`: trace `2⁷/2⁶ = 2` — one logical qubit, by `stabProjector_trace`.
* The logical states `steaneZero`/`steaneOne` (uniform superpositions over the row space
  `C₂` and its `1⃗`-coset), proved **stabilised by all 64 group elements**, **orthonormal**
  (`inner_steaneZero_steaneOne`, `inner_steaneZero_self`, `inner_steaneOne_self`) — the
  2-dimensional code space exhibited concretely, matching the trace.
* The logical operators `X̄ = X^{1⃗}`, `Z̄ = Z^{1⃗}`: `X̄` swaps the logical states, `Z̄`
  fixes `|0̄⟩` and negates `|1̄⟩` — a genuine encoded qubit (`1⃗` is a Hamming codeword
  outside the row space: `rowComb_ne_allOnes`, decide).
* The distance mechanism: `syndrome (unitErr j)` is **nonzero** and **injective** in `j`
  (the Hamming columns are nonzero and pairwise distinct, decide) — the distance-3 property;
  via `pauliOp_comm` this is exactly "every single-qubit error anticommutes with a generator
  identified by its syndrome", and CSS self-duality covers both error types with one matrix.

## Honest scope

The code space and the syndrome mechanism are exhibited; the full recovery map, the
Knill–Laflamme conditions, and any fault-tolerance claim are **not attempted** — the same
posture as the three-qubit modules. The `decide`-closed facts are finite computations on a
fixed `3 × 7` matrix — the right tool, not a shortcut.

## Execution record — 2026-08-29

GK-3 (`Stabilizer.lean`, ~180 lines) + Steane (~330 lines) together ≈ 80 minutes wall-clock
including build iterations. GK-3's design — the group indexed by `𝔽₂^m` with linear label
maps and the coherence law `σ(x+y) = σx + σy + B(x)·A(y)` (which IS "`−I ∉ S`", and which
*implies* commutativity) — made absorption a one-reindex proof and idempotence a three-liner;
the stabilised state came from `tr P ≠ 0` + idempotence with no spectral machinery. Steane
then instantiated it with all `𝔽₂` side conditions kernel-checked. Snag for the pile: `rw`
with an over-general `if_neg` lambda targets the FIRST `ite` in the goal — ascribe the
binder's type (`fun h : condition => …`) to aim it at the intended one.

**Named residues:** (i) GK-3 uniqueness/dimension (rank-equals-trace for self-adjoint
idempotents — spectral machinery); (ii) the stabiliser measurement-update rule; (iii)
Knill–Laflamme / recovery for Steane. Each is a scoped future brick, none is silently
claimed.

## References

Steane, "Error correcting codes in quantum theory" (PRL 77, 793 (1996));
Calderbank–Shor, "Good quantum error-correcting codes exist" (PRA 54, 1098 (1996));
Nielsen–Chuang §10.4.2 (the Steane code), §10.5 (stabiliser codes). In-corpus:
`Mathlib/QuantumInfo/Stabilizer.lean` (GK-3, the layer this instantiates),
`Empirical/QM/QEC/ThreeQubit.lean`/`ShorNine.lean` (the earlier instances the CSS
construction generalises).
