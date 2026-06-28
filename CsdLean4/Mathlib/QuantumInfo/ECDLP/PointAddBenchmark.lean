import CsdLean4.Mathlib.QuantumInfo.ECDLP.ResourceBounds

/-!
# ECDSA.fail benchmark-comparable artefact — one affine point addition

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This file builds the single comparable object the ECDSA.fail benchmark scores
(`specs/ecdsafail-correlation.md`, step 3): **one reversible affine elliptic-curve point
addition** with a QUANTUM target point and a CLASSICAL offset point,

```
(target_x, target_y)  ↦  (target_x, target_y) + (offset_x, offset_y)
```

scored on the benchmark convention `Toffoli × peak-live-qubits`. Every number reuses the
verified field-arithmetic gadget costs from `ResourceBounds.lean` — `cleanModMulToffoli`
(tied to the proved carry-clean `Reversible.cuccaroModMul_toffoli`), `fermatInvToffoli`
(square-and-multiply on it), and `cleanModMulQubits` (the proved `Θ(n)` carry-clean width).
Nothing here re-derives a field-arithmetic cost.

## The three comparable numbers (at `Secp256k1.bits = 256`)

* `onePointAddToffoli_eq      : onePointAddToffoli      = 676880936`
* `onePointAddPeakQubits_eq   : onePointAddPeakQubits   = 2822`
* `onePointAddScore_eq        : onePointAddScore        = 1910158001392`

and the gadget-anchored bound `onePointAdd_toffoli_le : onePointAddToffoli ≤ 678180864`
(`= 4·cleanModMulToffoli 256 + fermatInvToffoli 256`).

## Verified / documented / conjectural tiering (mandatory)

* **VERIFIED** (proved Lean circuit costs): the per-field-multiply Toffoli
  `cleanModMulToffoli n = 20n²+14n` (`cleanModMulToffoli_eq_cuccaro`, the carry-clean
  modular multiply `cuccaroModMul`); the per-inversion Fermat factor built on it
  (`fermatInvToffoli`, the `≤ 2n` square-and-multiply op count is the proved
  `fermatInvFieldMults_le`, each multiply the verified `cleanModMulToffoli`); the
  carry-clean `Θ(n)` width `cleanModMulQubits n = 6n+6` (`cleanModMulQubits_inhabited`,
  a layout genuinely exists for every `n ≥ 1`); the carry-clean per-modular-adder cost
  `14n+10` (the `cuccaroCModAdd` figure underlying `classicalOffsetCoordToffoli`).
* **DOCUMENTED** (op-count / layout models, not verified circuits): the affine op-count
  assembly `3 mults + 1 inversion` (`affinePointOpToffoli`, an EFD-ish count); the
  classical-offset coordinate term `classicalOffsetCoordToffoli` (the count `4` of O(n)
  constant-subtractions is documented, the per-op `14n+10` is the verified adder cost);
  the peak-qubit layout count `onePointAddPeakQubits` (a register-tally, NOT a peak read
  off an executed circuit).
* **CONJECTURAL / EXTERNAL** (not validated against ECDSA.fail): the map from our
  worst-case UPPER-bound Toffoli count to their average **executed** Toffoli count; their
  Rust gate model; and the live-harness score. Our `onePointAddScore` is the repo's
  comparable-OBJECT figure, NOT their score, until step 2 of the plan (running their
  harness on the same point operation) is done.

## Rust-gate translation notes (ECDSA.fail harness)

* **Toffoli = their Toffoli.** Our `circuitCost.toffoli` counts CCX gates in the
  measurement-free `CCX`-DSL; the benchmark counts Toffolis in its Rust gate model. Our
  count is a worst-case UPPER bound on an exhibited unoptimised circuit; theirs is the
  average **executed** Toffoli of a concrete run. These agree only after step 2.
* **Ancilla-clean = their reverse-identity / ancilla-restoration check.** The benchmark's
  validation (ancilla restored, phase clean, reverse identity) is the harness analogue of
  the corpus cleanliness lemmas `Reversible.cuccaroModMul_clean` (shared scratch bank
  restored) and `Reversible.cuccaroAdd_ancilla_clean` (Cuccaro ancilla `Z` returns to
  `false`), which the multiply/adder gadgets satisfy.
* **Affine in/out convention matches theirs.** `(target_x, target_y) ↦ (target_x,
  target_y) + (offset_x, offset_y)`, affine coordinates in and out — so an isolated
  addition MUST pay one slope inversion `1/(offset_x − target_x)` (no projective
  amortisation across a single op; that is why `fermatInvToffoli` dominates).
* **Offset classical matches theirs.** `offset_x`, `offset_y` are classical constants, so
  the coordinate combinations are subtract-by-classical-constant (O(n)), not q×q field
  operations; the offset is never loaded into a quantum register.

## Honest status line

Until step 2 (reproducing the ECDSA.fail harness on the same point operation) lands, this
score is the repo's comparable-OBJECT figure — one affine point addition, classical
offset, `Toffoli × peak-qubits` — but it is **NOT yet validated against a live ECDSA.fail
run**. It is a verified-gadget-anchored worst-case upper bound, not their executed average.
-/

namespace ECDLP.ResourceBounds

open ECDLP

/-! ### The classical-offset coordinate term (the benchmark-specific saving) -/

/-- **Classical-offset coordinate handling, `4·(14n+10)` (sub-dominant `O(n)`).** With a
CLASSICAL offset the four coordinate combinations of the affine addition —
`Δx = offset_x − x`, `Δy = offset_y − y`, `x₃ −= offset_x`, `y₃ −= y` — are
subtract-by-classical-constant / register-subtractions, each an `O(n)` modular adder
(`14n+10`, the carry-clean `Reversible.cuccaroCModAdd` cost), **not** a `q×q` field
multiply. The count `4` is a DOCUMENTED op-count; the per-op `14n+10` is the VERIFIED
carry-clean adder cost. This is the benchmark-specific saving the classical offset buys:
the coordinate work is `O(n)`, not the `q×q` `cleanModMulToffoli = 20n²+14n` of the
Jacobian generic mixed-addition figure `ECDLP.additionToffoli w = 136w²`. It does NOT
reduce the dominant slope inversion. -/
def classicalOffsetCoordToffoli (n : ℕ) : ℕ := 4 * (14 * n + 10)

theorem classicalOffsetCoordToffoli_secp256k1 :
    classicalOffsetCoordToffoli Secp256k1.bits = 14376 := by
  norm_num [classicalOffsetCoordToffoli, Secp256k1.bits]

/-- **The classical-offset saving, anchored.** The whole four-operation classical-offset
coordinate pass (`classicalOffsetCoordToffoli 256 = 14376`) costs strictly less than even
ONE generic `q×q` carry-clean field multiply (`cleanModMulToffoli 256 = 1314304`) — the
quantitative statement that handling the offset as a classical constant (`O(n)`
subtractions) is cheap against the `q×q` `O(n²)` field-multiply scale that the generic
Jacobian figure `ECDLP.additionToffoli = 136w²` uses for coordinate work. The dominant
cost (the slope inversion) is unaffected by this saving. -/
theorem classicalOffset_coord_lt_one_qq_mult :
    classicalOffsetCoordToffoli Secp256k1.bits < cleanModMulToffoli Secp256k1.bits := by
  norm_num [classicalOffsetCoordToffoli, cleanModMulToffoli, Secp256k1.bits]

/-! ### The Toffoli count for one affine point addition -/

/-- **Toffoli count for ONE affine point addition, classical offset.** The verified affine
point-op core (`affinePointOpToffoli Secp256k1.bits` — three carry-clean field multiplies
`λ = Δy·(1/Δx)`, `λ²`, `λ·(x−x₃)` plus the dominating Fermat slope inversion
`1/(offset_x − x)`) plus the sub-dominant classical-offset coordinate term
(`classicalOffsetCoordToffoli`). The inversion (`fermatInvToffoli 256 = 672923648`)
dominates: it is `~99.4%` of the total, the three multiplies `~0.6%`, the classical-offset
coordinate handling `~0.002%`.

**Tier:** the inversion + multiply core is VERIFIED-gadget-anchored (`cleanModMulToffoli`,
`fermatInvToffoli`); the `3`-mult op-count assembly and the `4`-subtraction classical-offset
count are DOCUMENTED. -/
def onePointAddToffoli : ℕ :=
  affinePointOpToffoli Secp256k1.bits + classicalOffsetCoordToffoli Secp256k1.bits

/-- One affine point addition with a classical offset costs `676880936` Toffolis: the
verified affine core `affinePointOpToffoli 256 = 676866560` (one Fermat inversion
`672923648` + three carry-clean multiplies `3 · 1314304 = 3942912`) plus the
classical-offset coordinate term `classicalOffsetCoordToffoli 256 = 14376`. -/
theorem onePointAddToffoli_eq : onePointAddToffoli = 676880936 := by
  norm_num [onePointAddToffoli, affinePointOpToffoli, classicalOffsetCoordToffoli,
    cleanModMulToffoli, fermatInvToffoli, Secp256k1.bits]

/-- **Gadget-anchored Toffoli bound.** One affine point addition costs at most
`4·cleanModMulToffoli 256 + fermatInvToffoli 256 = 678180864` — four carry-clean field
multiplies plus one Fermat inversion. The bound absorbs the `O(n)` classical-offset
coordinate term into a fourth multiply's budget (`classicalOffsetCoordToffoli 256 = 14376
< cleanModMulToffoli 256 = 1314304`, `classicalOffset_coord_lt_one_qq_mult`), tying the
benchmark figure to the proved field-arithmetic gadget costs rather than leaving it
free-floating. -/
theorem onePointAdd_toffoli_le :
    onePointAddToffoli ≤ 4 * cleanModMulToffoli Secp256k1.bits + fermatInvToffoli Secp256k1.bits := by
  rw [onePointAddToffoli_eq]
  norm_num [cleanModMulToffoli, fermatInvToffoli, Secp256k1.bits]

/-! ### Peak live qubits for one affine point addition -/

/-- **Peak-live-qubit count for one affine point addition: `2822` (`≈ 11n`).** A DOCUMENTED
layout count (a register tally, NOT a peak read off an executed circuit). Register
breakdown at the dominant operation (the slope inversion):

* `2n` — the quantum target `x, y` (preserved across the op); `x₃, y₃` overwrite in place;
* `3n` — the live working coordinates `Δx` (= inversion input), `Δy` (needed for `λ`), and
  the Fermat exponentiation accumulator for `a^{p-2}`;
* `cleanModMulQubits n = 6n+6` — the shared carry-clean modular-multiply / inversion
  scratch bank, the VERIFIED `Θ(n)` width (`cleanModMulQubits_inhabited`: a
  `Reversible.CuccaroMulLayout` exists on exactly `6n+6` wires for every `n ≥ 1`).

Total `2n + 3n + (6n+6) = 11n + 6 = 2822` at `n = 256`. The carry-clean bank is the
verified driver; the `5n` target+working tally is the documented layout.

**Tier:** DOCUMENTED layout count; its `cleanModMulQubits` component is VERIFIED. -/
def onePointAddPeakQubits : ℕ :=
  2 * Secp256k1.bits + 3 * Secp256k1.bits + cleanModMulQubits Secp256k1.bits

theorem onePointAddPeakQubits_eq : onePointAddPeakQubits = 2822 := by
  norm_num [onePointAddPeakQubits, cleanModMulQubits, Secp256k1.bits]

/-! ### The ECDSA.fail-convention score -/

/-- **The ECDSA.fail-convention score for one affine point addition.** The benchmark scores
`average-executed-Toffoli × peak-live-qubits`; this is the repo's comparable-OBJECT
analogue, `onePointAddToffoli × onePointAddPeakQubits`, the headline figure.

**Tier:** the factors are VERIFIED-gadget-anchored (Toffoli) / DOCUMENTED (peak qubits);
the product is **CONJECTURAL / EXTERNAL** as a comparison to the live ECDSA.fail score —
ours is a worst-case UPPER bound, theirs an executed average; not validated until the
harness is run on the same operation (see the honest status line in the module docstring). -/
def onePointAddScore : ℕ := onePointAddToffoli * onePointAddPeakQubits

/-- The ECDSA.fail-convention score for one affine point addition (classical offset) is
`1910158001392`: `onePointAddToffoli = 676880936` Toffolis times `onePointAddPeakQubits =
2822` peak live qubits. This is the repo's comparable-OBJECT figure, NOT a validated
ECDSA.fail harness score. -/
theorem onePointAddScore_eq : onePointAddScore = 1910158001392 := by
  rw [onePointAddScore, onePointAddToffoli_eq, onePointAddPeakQubits_eq]

end ECDLP.ResourceBounds
