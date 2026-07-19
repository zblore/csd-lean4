# ECDSA.fail benchmark correlation layer

**Purpose.** Normalise the comparison target *before* any further optimisation. The repo's
ECDLP work is a secp256k1 *scalar-multiplication / resource-accounting scaffold* (explicitly
"not a verified fault-tolerant attack"); the ECDSA.fail benchmark scores *one reversible point
addition with a classical offset*. These count different objects. This file maps the two so we
never make a false comparison, then sequences the bridge work.

## What ECDSA.fail actually asks

One reversible circuit implementing, on a quantum target point with a **classical** offset:

```
(target_x, target_y)  ↦  (target_x, target_y) + (offset_x, offset_y)
```

- `target_x`, `target_y`: 256-qubit registers (quantum).
- `offset_x`, `offset_y`: classical constants (NOT quantum registers).
- Harness: builds the circuit, validates it (ancilla restored, phase clean, reverse identity),
  scores **average executed Toffoli count × peak live qubits**, appends to `results.tsv`, writes
  `score.json` (toffoli, clifford, peak qubits, score, correct/fail).

So the benchmark is **one point addition**, executable, scored on `Toffoli × peak-qubits`, with the
offset classical.

## Correlation table

| Dimension | ECDSA.fail | This repo (current) |
|---|---|---|
| Object counted | one point addition | scalar multiplication / modular-arithmetic layers |
| Inputs | quantum target point + **classical** offset | general modular arithmetic + EC scaffold (mostly quantum×quantum) |
| Circuit status | executable Rust circuit, validated | Lean theorem / cost scaffold (gate-list `denote`, not the Rust gate model) |
| Toffoli metric | average **executed** Toffolis | mostly upper bounds / derived formulas (`additionToffoli w = 136w²`, etc.) |
| Qubit metric | **peak live** qubits | layout/formula-level qubits (carry-clean multiply `cleanModMulQubits = 6n+6 = 1542`) |
| Cleanliness | ancilla + phase + reverse identity checked by harness | proven only for selected gadgets (`cuccaroAdd_ancilla_clean`, `cuccaroModMul_clean`, …) |
| Score | `avg Toffoli × peak qubits` | not computed (no `Toffoli × qubits` figure for a single point op) |

## What the repo has that maps onto a point addition

- `ECDLP/PointAdd.lean` (S6.2): the secp256k1 `a=0` Jacobian **mixed addition** SLP, `M_add = 17`
  field multiplies (DERIVED), and `additionToffoli w = M_add · fieldMulToffoli w = 136w²`
  (`additionToffoli 256 = 8,912,896`). **But:** this costs the field multiplies as quantum×quantum
  (`fieldMulToffoli = 8w²`, the controlled q×q adder), NOT the cheaper quantum×classical that a
  classical offset permits; and it is a *bound formula*, not a `Toffoli × peak-qubits` score, and not
  the affine convention the benchmark uses.
- Carry-clean stack (`CuccaroAdd`/`CuccaroModAdd`/`CuccaroModMul`): the `Θ(n)`-qubit reusable model
  (`1542` qubits for the 256-bit modular multiply working set) and `cuccaroModMul_clean` (ancilla
  restored). This is the right *peak-qubit* primitive, but it is the modular-multiply width, not yet
  lifted to a full point-addition circuit's peak.
- The verified / documented / conjectural tiering (keep it): the comparison must show which numbers
  are Lean-proved, which are documented cost-model assumptions, and which would be executable harness
  results.

## The gap (why the first missing bridge is alignment, not optimisation)

1. **Object mismatch.** The repo costs scalar mult (`O(n³)·ops`) and a generic q×q point op. The
   benchmark wants exactly one addition with a **classical** offset (cheaper: q×classical, ~`2n²`/mult
   not `8w²` or `20n²+14n`).
2. **Metric mismatch.** The repo has Toffoli *formulas*; the benchmark scores `avg-executed-Toffoli ×
   peak-live-qubits`. The repo has no single-point-op `Toffoli × qubits` figure.
3. **Convention/cleanliness mismatch.** Benchmark = affine in/out, harness-checked ancilla/phase/reverse
   identity; the repo proves cleanliness for selected gadgets only and uses Jacobian/projective coords.

## Sequenced plan (correlate → reproduce → comparable artefact → optimise)

**Step 1 — this file (correlation).** DONE: the map above, so no false comparisons.

**Step 2 — reproduce the ECDSA.fail public baseline locally.** Run their harness:
`cargo run --release -- --note "baseline reproduction"`, record `toffoli`, `clifford`, `peak qubits`,
`score`, `correct/fail`. **Status: BLOCKED in this repo** — the ECDSA.fail Rust source is not in this
tree, so the harness cannot be run from here. This step is a user action (`! cargo run …` in a checkout
of their repo) or requires cloning their repo alongside. Reproduce the **public baseline first** (the
benchmark warns memory/source may come from different agents; verify by rerunning), NOT the live
leaderboard best unless its source is available.

**Step 3 — build the comparable Lean artefact: a point-addition cost theorem. DONE 2026-06-28**
(`ECDLP/PointAddBenchmark.lean`, auditor-SOUND). The three comparable numbers for one affine
point addition with a classical offset at `n = 256`:
- `onePointAddToffoli = 676,880,936` (= `affinePointOpToffoli 256` `676,866,560` [3 carry-clean field
  multiplies + one Fermat inversion, the inversion is `99.4%`] + `classicalOffsetCoordToffoli 256`
  `14,376` [the four constant/register coordinate subtractions]),
- `onePointAddPeakQubits = 2,822` (= `2n` target `+ 3n` working coords `+ cleanModMulQubits n` `1542`
  multiply scratch, `≈ 11n`; a documented layout tally),
- `onePointAddScore = 1,910,158,001,392` (Toffoli × peak-qubits, the ECDSA.fail-convention score).
Anchored by `onePointAdd_toffoli_le : onePointAddToffoli ≤ 4·cleanModMulToffoli 256 + fermatInvToffoli 256`
(`678,180,864`) and the classical-offset saving `classicalOffset_coord_lt_one_qq_mult`
(the whole offset pass `14,376` < one q×q multiply `1,314,304`). Tiers: VERIFIED gadget costs
(`cleanModMulToffoli`/`cuccaroModMul`, `fermatInvToffoli`, `cleanModMulQubits`), DOCUMENTED assembly
(3-mult / 4-subtraction op counts, peak-qubit layout), CONJECTURAL/EXTERNAL map to the executed-average
harness score. This is the repo's comparable-OBJECT figure; it is **not** a validated ECDSA.fail score
until step 2 runs their harness. (Original requirements:)
New file `ECDLP/PointAddBenchmark.lean`, target shape `onePointAddCost ≤ B` (NOT `scalarMulCost ≤ B`), with:
- affine input/output convention,
- **classical** offset point (exploit it — q×classical, do not cost it as generic q×q),
- reversible cleanup (ancilla-clean, reusing the Cuccaro `_clean` lemmas),
- **peak-live-qubit** accounting (lift `cleanModMulQubits` to the full point-add peak),
- explicit Toffoli count for **one** addition (ignore scalar mult here),
- the `Toffoli × peak-qubits` score figure,
- translation notes to the ECDSA.fail Rust gate model,
- the verified / documented / conjectural tier labels per number.

**Step 4 — only then optimise.** Specialise to the benchmark (classical offset, one addition,
peak-qubit scoring). Do NOT chase Gidney-style / leaderboard improvements until the output is "one
ECDSA.fail point addition, with Toffoli, qubits, and score" — until then we cannot know which
enhancement actually matters.

## Honest status line
Step 3 is DONE: the repo now has a single-point-addition `Toffoli × peak-qubits` figure
(`onePointAddScore = 1,910,158,001,392`, from `onePointAddToffoli = 676,880,936` and
`onePointAddPeakQubits = 2,822`) in the verified/documented tiers. This is the comparable-OBJECT
figure (one affine point addition, classical offset). It is **not yet** a validated comparison to an
ECDSA.fail score: that needs step 2 (running their harness on the identical operation), which is
BLOCKED on the ECDSA.fail Rust source not being in this tree. The repo's *scalar-mult* numbers
(`secp256k1ToffoliCleanArith`, etc.) remain **not** comparable to an ECDSA.fail point-addition score —
they count a different object. Cite `onePointAddScore`, not the scalar-mult figures, for the benchmark.
