# ECDSA.fail — entry point (the reversible EC point-addition subroutine)

**This is the landing page for the ECDSA.fail resource work. Read it first.** ECDSA.fail is, at
bottom, a competition over ONE subroutine: the reversible elliptic-curve **point addition** on
secp256k1. The leaderboard scores exactly that circuit. Everything in this repo's ECDLP tree is
either (a) building that point-addition subroutine from machine-verified field arithmetic, or (b)
costing the optimised version against the leaderboard. This file ties the two together and points at
every relevant file.

Companion docs (all under `specs/`): `ecdsafail-correlation.md` (what the benchmark scores, the
object-correlation guard), `ecdsafail-two-track.md` (the verified-floor / trusted-estimate accounting),
`ecdsafail-optimization-plan.md` (the L1-L6 optimisation levers), `ecdlp-resource-plan.md` (the full
reversible-arithmetic programme). This README is the map over all four.

## 0. TL;DR

| | figure (secp256k1, one point addition) | basis |
| --- | --- | --- |
| **Verified floor** | Toffoli `676,880,936`, peak qubits `2,822`, score `1,910,158,001,392` | machine-verified circuits + anchored op-counts only |
| **Trusted estimate** | Toffoli `1,457,987`, peak qubits `1,152`, score `1,679,601,024` | composition of published, community-validated mechanisms |
| number-one benchmark | score `1,566,720,000` (`1,360,000 × 1,152`) | external Rust-circuit leaderboard entry |

The trusted estimate lands at about `1.07×` the number-one benchmark on both axes. The verified floor
is about `1,219×` above it. **The distance between the two tracks is the verification frontier: the
roadmap.** The verified floor is not a weakness; it is a first-of-kind artifact (a formally verified
quantum resource bound) on an axis no leaderboard entry occupies.

## 1. What ECDSA.fail scores

One reversible circuit implementing, on a quantum target point with a **classical** offset:

```
(target_x, target_y)  ↦  (target_x, target_y) + (offset_x, offset_y)
```

- `target_x, target_y`: 256-qubit registers (quantum). `offset_x, offset_y`: classical constants.
- Harness: builds the circuit, validates it (ancilla restored, phase clean, reverse identity), scores
  **average executed Toffoli × peak live qubits** (lower wins), appends to `results.tsv`.
- **The board scores a RUST-coded circuit.** A Lean cost figure is not a submission; getting on the
  board means writing the competitive Rust circuit and running the harness. Our Lean figures are a
  TARGET SPEC (what a good construction should hit) and a VERIFIED artifact, not entries. See
  `ecdsafail-correlation.md`.

## 2. The subroutine, decomposed

A point addition is field arithmetic. In affine coordinates (the isolated scored object) it is

```
one point addition  =  3 field multiplications  +  1 field inversion  +  classical-offset adders
```

and the **inversion dominates** (an isolated affine add pays one slope inversion `1/(offset_x −
target_x)`; there is no projective amortisation across a single op). In the windowed-projective form
used inside a full scalar multiplication, the per-op inversion is amortised away and each point
operation is a fixed count of field multiplications (verified SLP derivations: doubling `M_dbl = 8`,
mixed addition `M_add = 17` field multiplies; `ECDLP/PointDouble.lean`, `ECDLP/PointAdd.lean`).

Every field operation is a machine-verified reversible gadget (denote-level correct, `ZMod`-valued):

| gadget | Toffoli | file | status |
| --- | --- | --- | --- |
| modular multiply (carry-clean) | `20n² + 14n` | `Reversible/CuccaroModMul.lean` | VERIFIED (`cuccaroModMul_correct`) |
| modular multiply (schoolbook loop) | `30n²` | `Reversible/ModularMulLoop.lean` | VERIFIED (`mulLoop_correct`) |
| modular add / sub / double | `12n` / `10n` / `12n` | `Reversible/Modular{Add,Sub,Double}.lean` | VERIFIED |
| modular const-multiply / negate | `c·12n` / `10n` | `Reversible/ModularConst.lean` | VERIFIED |
| Fermat inversion (square-and-multiply) | `≈ 2n · (20n²+14n)` | `ECDLP/ResourceBounds.lean` | ANCHORED (verified mults, documented `2n` schedule) |

The point-addition Toffoli is these gadget costs assembled: `onePointAddToffoli ≤ 4·cleanModMulToffoli(256)
+ fermatInvToffoli(256) = 678,180,864`, with the exact affine assembly `676,880,936`
(`ECDLP/PointAddBenchmark.lean`). The `≈ 672,923,648` Fermat inversion is the whole floor.

## 3. The two tracks over the SAME subroutine

Both tracks cost the identical point-addition subroutine; they differ only in the trust basis of the
primitives plugged into it (`ecdsafail-two-track.md`, `ECDLP/TwoTrack.lean` + `ECDLP/TrustedEstimate.lean`).

- **Verified floor** (`secp256k1Toffoli_verifiedFloor = 676,880,936`). Only machine-verified circuits and
  anchored op-counts. The one inversion the corpus can machine-anchor is the `O(n³)` Fermat exponentiation,
  so the floor is the LARGER number, and the inversion dominates it. `verifiedFloor_no_trusted_leak`
  certifies no trusted primitive leaks in.
- **Trusted estimate** (`secp256k1Toffoli_trustedEstimate_v2 = 1,457,987`, score `1,679,601,024`). The same
  subroutine with each dominant primitive replaced by a published, community-validated mechanism:
  `O(n²)` safegcd inversion (Bernstein-Yang), Karatsuba sub-quadratic multiply, Gidney measurement-based
  uncomputation (`÷2`), windowed EC recoding (`÷2`), and Litinski's ancilla-recycling qubit layout
  (`≈ 4.5n`, `1,152` peak qubits). Every figure tags `trusted` (cited, not Lean-verified);
  `trustedEstimate_uses_trusted` certifies it.

**"Trusted" = trust the PUBLISHED MECHANISM, not any leaderboard entry.** The ecdsa.fail board is an
external benchmark we compare to; that a principled composition of published mechanisms lands near it is a
cross-check, not the justification. See `ecdsafail-two-track.md` for the citations and the trust ladder
(verified / anchored / trusted).

## 4. How the subroutine is being improved

Two directions, both real, on different axes.

**Verified, bottom-up (the floor).** Build the point-addition subroutine from machine-verified field
gadgets so its resource bound is a theorem, not an estimate. Done: the full modular field-op gadget set
`{modAdd, modSub, modDouble, mulLoop, modConstMul, modNeg}` (each denote-level correct); the carry-clean
Cuccaro multiply/adder; the Fermat-anchored inversion; the derived point-add / point-double SLP counts
(`M_add = 17`, `M_dbl = 8`); a strict Array circuit evaluator (`Reversible/Eval.lean`) and an SLP→circuit
router with per-opcode field-correctness (`Reversible/ProgramRouter*.lean`, `DoublingAssembly*.lean`). This
is the axis no leaderboard entry occupies: a **formally verified** quantum resource bound for a secp256k1
point addition.

**Trusted, optimisation (toward the leaderboard band).** Swap in the published mechanisms, tracked by the
L-series (`ecdsafail-optimization-plan.md`): L6 safegcd inversion (`O(n³) → O(n²)`, the dominant lever), L1
Karatsuba multiply, L3 shared-partial-product squaring, L5 Gidney measurement adders, windowing, and the
Litinski qubit layout. Trajectory on the score: verified floor `1,910,158,001,392` (`≈ 1,219×` #1) →
trusted estimate `1,679,601,024` (`≈ 1.07×` #1).

**The frontier = the roadmap.** Each verified tranche promotes one primitive `trusted → verified`, pulling
the verified floor down toward the trusted estimate. The four frontier items (`verificationFrontier`,
`TwoTrack.lean`):

1. the safegcd divstep circuit (Bernstein-Yang invariant + termination), the dominant lever;
2. a measurement-based (Gidney) adder / multiply as a verified circuit (needs a measurement-discipline
   extension of the CCX DSL);
3. a sub-quadratic Karatsuba multiply as a verified circuit (split + recombine proved);
4. windowed elliptic-curve scalar recoding as a verified circuit.

Verifying (1) alone converts the dominant inversion cost and collapses most of the gap.

## 5. File map (entry-point navigation)

### Specs (read in this order)
- `ecdsafail-README.md` — this file (the map).
- `ecdsafail-correlation.md` — what the benchmark scores; the object-correlation guard (do not compare
  different objects). Step 2 (running the Rust harness) is the user's machine action.
- `ecdsafail-two-track.md` — the verified-floor / trusted-estimate / frontier accounting; the trust ladder;
  citations.
- `ecdsafail-optimization-plan.md` — the L1-L6 optimisation levers, tiered by DSL-expressibility.
- `ecdlp-resource-plan.md` — the full 7-tranche reversible-arithmetic programme (T1-T7) the subroutine is
  built on.

### Lean — the point-addition subroutine (`CsdLean4/Mathlib/QuantumInfo/ECDLP/`)
- `PointAddBenchmark.lean` — THE scored object: one affine point addition, `onePointAddToffoli /
  _PeakQubits / _Score`, gadget-anchored bound.
- `PointAdd.lean`, `PointDouble.lean` — verified projective SLP point add / double (`M_add = 17`,
  `M_dbl = 8` derived).
- `ResourceBounds.lean` — `cleanModMulToffoli`, `fermatInvToffoli`, peak-qubit layout, the composition.
- `TwoTrack.lean` — verified floor, trust ladder, `verificationFrontier`, the gap theorems.
- `TrustedEstimate.lean` — the trusted leaderboard estimate (Stage-1 Gidney/windowing, Stage-2 Litinski
  qubit layout), the score, the leaderboard comparison.
- `EllipticCurve.lean`, `ScalarMul.lean`, `Secp256k1.lean` — the curve, `[k]P` scalar multiply, the
  secp256k1 instance and the end-to-end scalar-multiply bound.
- `SafegcdInversion.lean`, `KaratsubaMul.lean`, `Inversion.lean` — the trusted-track inversion / multiply
  primitives.

### Lean — the verified field-arithmetic stack (`CsdLean4/Mathlib/QuantumInfo/Reversible/`)
- `Circuit.lean`, `Cost.lean`, `Eval.lean` — the reversible-gate DSL, the derived cost model, the strict
  Array evaluator (`#eval` circuit outputs).
- `Modular{Add,Sub,Double,MulLoop,Const}.lean` — the verified modular field-op gadgets.
- `Cuccaro{Add,ModAdd,ModMul}.lean` — the carry-clean Cuccaro/Takahashi arithmetic (the verified-floor
  primitives).
- `ProgramRouter*.lean`, `DoublingAssembly*.lean` — the SLP→circuit router with per-opcode field
  correctness (every `Instr` is a verified bit-circuit computing its `ZMod p` op through the fold).
- `Gidney{Adder}.lean`, `AndAdd.lean`, `VerifiedAdder*.lean` — the measurement-based / AND-based adder
  work (the L5 / measurement-uncompute frontier).

### Axiom pins
- `CsdLean4/Tests/AxiomAudit.lean` — foundational-triple pins for every headline (TwoTrack, TrustedEstimate,
  the gadget correctness lemmas). CI gates the `#guard_msgs`.

## 6. Honest status

- **What is verified:** the field-arithmetic gadgets (denote-level circuit correctness), the point-add
  assembly bound, the Fermat-anchored inversion. A sorry-free, foundational-triple resource SCAFFOLD with
  `O(n³)` verified structure. NOT a verified fault-tolerant attack; residue = a concrete measurement-based
  EC-add circuit, `p`-primality, an on-curve point.
- **What is trusted:** the safegcd inversion, Karatsuba, Gidney, windowing, and the Litinski qubit layout
  (cited published mechanisms, not Lean-verified here).
- **What ECDSA.fail is not:** a venue for Lean proofs. The board scores Rust circuits. The profile-raising
  Lean-side move is the VERIFIED resource bound as its own artifact ("first formally verified quantum
  resource bound for a secp256k1 point addition"), and the trusted estimate as a target spec reaching the
  leaderboard band via published mechanisms.
- **Highest-value next tranche:** verify the safegcd divstep circuit (frontier item 1) — it is the dominant
  lever, and it pulls the verified floor from `O(n³)` toward the `O(n²)` trusted band.
