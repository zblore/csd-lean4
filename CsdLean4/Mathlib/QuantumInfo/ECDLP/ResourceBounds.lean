import CsdLean4.Mathlib.QuantumInfo.ECDLP.ScalarMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduce
import CsdLean4.Mathlib.QuantumInfo.ECDLP.Secp256k1
import CsdLean4.Mathlib.QuantumInfo.ECDLP.PointAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModMul
import CsdLean4.Mathlib.QuantumInfo.ECDLP.Inversion

/-!
# ECDLP / secp256k1 resource estimate — the capstone  (ECDLP Tranche 7)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The capstone of the ECDLP resource-accounting programme (`specs/ecdlp-resource-plan.md`): it assembles
the end-to-end Toffoli-cost estimate for `[k]P` — the quantum core of Shor's attack on the
elliptic-curve discrete logarithm — by **composing the two derived cost factors** the programme built:

* the **`O(log k)` operation count** of double-and-add (Tranche 6, `doubleAndAddCost_le ≤ 2·Nat.size k`);
* the **modular-multiplier Toffoli count** (Tranche 3, `multiplier_ripple_toffoli = 2·n·(#partial products)`).

The headline `secp256k1_scalarMul_toffoli_bound` gives `[k]P ≤ 2·256·(M·(2·256·256)) = O(256³)·M`
Toffolis for a 256-bit scalar, where `M` is the number of field multiplications per elliptic-curve
point operation.

## Honest scope — this is a resource *scaffold*, not a verified attack

The two factors above are genuinely *derived* (from exhibited circuits / a proved algorithm). The
**single honest parameter** is `M` (field-mults per point op): pinning it down requires the concrete
reversible **EC point-addition circuit** — composing the Tranche-3/4 modular-arithmetic oracles into the
secant–tangent addition formula (in projective/Jacobian coordinates, to avoid per-op inversion). That
circuit is **not built here**; until it is, `M` (a small constant, ~10–20 in the standard analysis) is a
parameter, and the per-op multiplications are taken as the Tranche-3 multiplier (quantum × classical, the
"add a classical `2^i·P`" structure of `[k]P` with `k` the quantum register and `P` classical). So the
honest claim is: **a sorry-free semantic + abstract resource scaffold for ECDLP over secp256k1, giving
the `O(n³)` Toffoli structure** — NOT a verified fault-tolerant attack (that needs the exhibited EC-add
circuit fixing `M`, plus the `p`-primality and a concrete on-curve point, all named residue).
-/

namespace ECDLP.ResourceBounds

open ECDLP Reversible

/-- Toffoli-cost model for computing `[k]P`: the double-and-add operation count (Tranche 6) times the
Toffoli cost of one elliptic-curve point operation. -/
def scalarMulToffoli (pointOpCost k : ℕ) : ℕ := doubleAndAddCost k * pointOpCost

/-- **Scalar-multiplication resource bound.** `[k]P` costs at most `2·Nat.size k · pointOpCost`
Toffolis — the `O(log k)` factor is Tranche-6's derived `doubleAndAddCost_le`. -/
theorem scalarMulToffoli_le (pointOpCost k : ℕ) :
    scalarMulToffoli pointOpCost k ≤ 2 * Nat.size k * pointOpCost := by
  unfold scalarMulToffoli
  gcongr
  exact doubleAndAddCost_le k

/-- **Per-point-operation cost from the Tranche-3 multiplier.** A point operation using `M` modular
multiplications, each an `n`-bit shift-and-add multiplier of `Ls.length` partial products, costs
`M · (2·n·Ls.length)` Toffolis — the multiplier factor is Tranche-3's derived `multiplier_ripple_toffoli`. -/
theorem pointOpCost_eq {m n : ℕ} (M : ℕ) (Ls : List (RippleLayout m n)) :
    M * (circuitCost (multiplier (Ls.map rippleCirc))).toffoli = M * (2 * n * Ls.length) := by
  rw [multiplier_ripple_toffoli]

/-- **ECDLP / secp256k1 resource scaffold (the capstone).** Computing `[k]P` for a 256-bit scalar `k`,
with `M` modular multiplications per elliptic-curve point operation and the Tranche-3 256-bit multiplier
(256 partial products) per multiplication, costs at most `2·256·(M·(2·256·256))` Toffolis — i.e.
`O(256³)·M`. The two cost factors (`O(log k)` op count, `2·n²` multiplier) are derived (Tranches 6 and 3);
`M` is the field-mults-per-point-op parameter the concrete EC-addition circuit would fix (see module note). -/
theorem secp256k1_scalarMul_toffoli_bound {m : ℕ} (M k : ℕ) (hk : Nat.size k ≤ Secp256k1.bits)
    (Ls : List (RippleLayout m Secp256k1.bits)) (hLs : Ls.length = Secp256k1.bits) :
    scalarMulToffoli (M * (circuitCost (multiplier (Ls.map rippleCirc))).toffoli) k
      ≤ 2 * Secp256k1.bits * (M * (2 * Secp256k1.bits * Secp256k1.bits)) := by
  calc scalarMulToffoli (M * (circuitCost (multiplier (Ls.map rippleCirc))).toffoli) k
      ≤ 2 * Nat.size k * (M * (circuitCost (multiplier (Ls.map rippleCirc))).toffoli) :=
        scalarMulToffoli_le _ _
    _ = 2 * Nat.size k * (M * (2 * Secp256k1.bits * Secp256k1.bits)) := by
        rw [pointOpCost_eq, hLs]
    _ ≤ 2 * Secp256k1.bits * (M * (2 * Secp256k1.bits * Secp256k1.bits)) := by gcongr

/-! ### Fixing the parameter `M`: a concrete secp256k1 Toffoli figure (Pass 1)

The bound above is `O(256³)·M` with `M` (field multiplications per elliptic-curve point operation) a
free parameter. Here we *fix* `M` to a documented constant and collapse the estimate to a concrete
number. This is **Pass-1** discipline (the same cost-from-exhibited-structure / correctness-deferred
split the whole programme uses): `M` is the operation count of the *standard* point-addition/doubling
formulae, taken as an upper bound; the **correctness** of those formulae as a reversible circuit
(composing the Tranche-3/4 modular oracles) is the named Pass-2 residue and is NOT proved here. -/

/-- A conservative upper bound on the number of field **multiplications** (counting squarings as
multiplications) per elliptic-curve point operation, in projective / Jacobian coordinates for an
`a = 0` curve (secp256k1): mixed-Jacobian addition is `7M + 4S` and doubling `3M + 4S`, so `≤ 16`
covers both (Explicit-Formulas Database). Projective coordinates avoid a per-operation modular
inversion. **Documented count, not a verified-circuit count** — the addition formula's correctness is
the Pass-2 residue. -/
def pointOpMults : ℕ := 16

/-- The concrete secp256k1 scalar-multiplication Toffoli figure: `2·256 · (16 · (2·256·256))`. -/
def secp256k1ToffoliBound : ℕ :=
  2 * Secp256k1.bits * (pointOpMults * (2 * Secp256k1.bits * Secp256k1.bits))

/-- The figure evaluates to `2^30 = 1 073 741 824` Toffolis: `512` point ops (the `O(log k)` count, ≤
`2·256`) × `16` field mults/op × `2·256² = 131 072` Toffolis per `256`-bit schoolbook multiply. -/
theorem secp256k1ToffoliBound_eq : secp256k1ToffoliBound = 1073741824 := by
  simp only [secp256k1ToffoliBound, pointOpMults, Secp256k1.bits]

/-- **ECDLP / secp256k1 — the concrete Toffoli figure (Pass-1 scaffold).** With `M` fixed to the
documented `pointOpMults = 16`, computing `[k]P` for a 256-bit scalar costs at most
`secp256k1ToffoliBound = 2^30` Toffolis, under the stated accounting (projective `a=0` point ops, the
Tranche-3 256-bit schoolbook multiplier per field multiplication). This is an **upper-bound resource
figure**, NOT a verified attack cost: it omits the mod-`N` register-reduction overhead (ModMul Stage C
residue) and assumes the standard point-addition formulae whose reversible-circuit correctness — and
the quantum × quantum products / inversion inside them — is the named Pass-2 residue. -/
theorem secp256k1_scalarMul_toffoli_concrete {m : ℕ} (k : ℕ) (hk : Nat.size k ≤ Secp256k1.bits)
    (Ls : List (RippleLayout m Secp256k1.bits)) (hLs : Ls.length = Secp256k1.bits) :
    scalarMulToffoli (pointOpMults * (circuitCost (multiplier (Ls.map rippleCirc))).toffoli) k
      ≤ secp256k1ToffoliBound :=
  secp256k1_scalarMul_toffoli_bound pointOpMults k hk Ls hLs

/-! ### Refined figure: per-operation-type field-multiplication counts

The figure above applies a single conservative `pointOpMults = 16` to a worst-case `2·size(k)` operation
count, which over-counts (it bills every operation as an addition, and double-counts the bit loop). The
refinement here weights **doublings** and **additions** separately with their documented field-mult
counts, via `doubleAndAddWeightedCost`. This removes the conservative inflation (≈ 1.8×) and is the
honest tightening; the residual gap to the most-optimised literature is the *documented* optimisations
listed in the scope note below, which are not formalised here. -/

/-- Field multiplications per elliptic-curve **doubling**, `a = 0` projective/Jacobian coordinates:
`2M + 5S` (EFD `dbl-2009-l`), counted as `7` (squarings as multiplications). -/
def fieldMultsPerDoubling : ℕ := 7

/-- Field multiplications per **mixed** (Jacobian + affine) **addition**, `a = 0`: `7M + 4S` (EFD
`madd-2007-bl`), counted as `11`. The base point `2ⁱ·P` is classical, so mixed addition applies. -/
def fieldMultsPerAddition : ℕ := 11

/-- Total field multiplications to compute `[k]P` by double-and-add, doublings and additions weighted
separately (the honest count, vs the uniform `pointOpMults` bound). -/
def scalarMulFieldMults (k : ℕ) : ℕ :=
  doubleAndAddWeightedCost fieldMultsPerDoubling fieldMultsPerAddition k

theorem scalarMulFieldMults_le (k : ℕ) : scalarMulFieldMults k ≤ Nat.size k * 18 := by
  have h := doubleAndAddWeightedCost_le fieldMultsPerDoubling fieldMultsPerAddition k
  simpa [scalarMulFieldMults, fieldMultsPerDoubling, fieldMultsPerAddition] using h

/-- The refined secp256k1 figure: `256 · 18 · (2·256²)`. -/
def secp256k1ToffoliRefined : ℕ :=
  Secp256k1.bits * 18 * (2 * Secp256k1.bits * Secp256k1.bits)

/-- The refined figure evaluates to `603 979 776 ≈ 6.0 × 10⁸` Toffolis (`= 9·2²⁶`): `256` doublings at
`7` field mults plus `≤ 256` additions at `11`, each multiplication the `256`-bit schoolbook multiplier
at `2·256² = 131 072` Toffolis. About `1.8×` below the uniform-`M` figure. -/
theorem secp256k1ToffoliRefined_eq : secp256k1ToffoliRefined = 603979776 := by
  simp only [secp256k1ToffoliRefined, Secp256k1.bits]

/-- **ECDLP / secp256k1 — the refined Toffoli figure.** Computing `[k]P` for a 256-bit scalar, with
doublings and additions costed separately (`7` and `11` field mults, EFD `a=0`) and each field
multiplication the Tranche-3 256-bit schoolbook multiplier, costs at most `secp256k1ToffoliRefined =
603 979 776 ≈ 6.0×10⁸` Toffolis.

**Scope (what this figure counts, exactly), so it is not misread:** the field **multiplications** of one
scalar multiplication, via standard ripple-carry adders (`2` Toffoli/bit, the Cuccaro/Takahashi class)
and schoolbook `O(n²)` multiplication. **It OMITS**, as named residue: the modular **reduction** after
each multiply (ModMul Stage C; ≈ doubles the per-mult cost), modular **inversion** / the projective
coordinate-recovery multiplications beyond the `7`/`11` counts, the **second** scalar multiplication of
the discrete-log instance, the **QFT / phase-estimation** wrapper, and ancilla **uncomputation**. **The
gap to the most-optimised published estimates is the documented optimisations not formalised here:**
**windowing** of the scalar (precomputed `2ⁱ·P` tables, fewer additions), **Montgomery / Karatsuba**
multiplication (sub-`2n²`), and **measurement-based** adders (Gidney, ≈ `1` Toffoli/bit). This is a
**verified upper bound for the stated unoptimised circuit**, correct on its own terms; it should be
positioned against a published figure of the *same scope*, not cited as the cost of breaking secp256k1. -/
theorem secp256k1_scalarMul_toffoli_refined {m : ℕ} (k : ℕ) (hk : Nat.size k ≤ Secp256k1.bits)
    (Ls : List (RippleLayout m Secp256k1.bits)) (hLs : Ls.length = Secp256k1.bits) :
    scalarMulFieldMults k * (circuitCost (multiplier (Ls.map rippleCirc))).toffoli
      ≤ secp256k1ToffoliRefined := by
  rw [multiplier_ripple_toffoli, hLs]
  calc scalarMulFieldMults k * (2 * Secp256k1.bits * Secp256k1.bits)
      ≤ Nat.size k * 18 * (2 * Secp256k1.bits * Secp256k1.bits) := by
        gcongr; exact scalarMulFieldMults_le k
    _ ≤ Secp256k1.bits * 18 * (2 * Secp256k1.bits * Secp256k1.bits) := by gcongr
    _ = secp256k1ToffoliRefined := rfl

/-! ### Tiered cost model: reconciling the verified figure with the optimised literature

The figures above are **verified upper bounds** tied to the exhibited circuits (the schoolbook multiplier
of Tranche 3 and the verified `doubleAndAddWeightedCost`).

**Literature context (256-bit ECDLP, published Toffoli counts span ~3 orders).** The
Roetteler–Naehrig–Svore–Lauter 2017 baseline (eprint 2017/598) is `≈ 1.26×10¹¹` Toffolis at `2330`
logical qubits (general formula `448 n³ log₂ n + 4090 n³`); Häner et al. tighten the qubit count (to
`~1333`); and the most aggressively optimised estimate, Gidney 2023 ("50 million Toffoli", arXiv
2306.08585), reaches `≈ 5×10⁷` Toffolis via windowed arithmetic + measurement-based uncomputation. So the
"optimised literature" is a *range* `~5×10⁷ … ~1.3×10¹¹`, not a single number, and the corpus's `Optimized`
tier below sits at the aggressively-optimised end. **Honest caveat on the verified figures:** the verified
`secp256k1ToffoliRefined` / `…VerifiedArith` / `…CleanArith` (`6.0×10⁸ … 1.26×10¹⁰`) sit *below*
Roetteler's `~10¹¹` baseline because they **omit** the modular **inversion** and the full
projective-coordinate overhead that the published circuits cost in full — i.e. they are *optimistic* on
the point-op side (the `M = 7/11` field-mult counts, no inversion), which is the named Pass-2 residue, not
a tighter circuit.

The standard literature applies three further optimisations to the per-multiply / op-count; each is a
*documented, standard* technique, but of differing verification status in this development:

* **windowing** of the scalar (precomputed `2ⁱ·P` tables): cuts additions from `~n` to `~n/w`.
  Verifiable in this DSL (a windowed `doubleAndAdd` variant), but only its op-count is modelled here.
* **squaring at ~half a multiply** (`n²` vs `2n²`, diagonal symmetry): documented count; a verified
  squaring *circuit* is not exhibited (the general multiplier is, at `2n²`).
* **measurement-based adders** (Gidney, `~1` Toffoli/bit vs the `2`/bit Cuccaro/Takahashi class):
  **not expressible** in this measurement-free gate DSL; documented only.

The definitions below compose the **derived** per-multiply cost with these **documented** counts to give a
transparent reconciliation. They are a *cost model*, not verified bounds: the multiplier `2n²` is derived
(Tranche 3), but `sqrToffoli`, the EFD per-operation profile, windowing, and the measurement-adder halving
are documented constants. The point is the **factor-by-factor account** from the verified `6.0×10⁸` down to
the literature `~10⁸`, with each step's status explicit — not a single number to cite as "the cost". -/

/-- Toffoli cost of one `n`-bit modular multiplication, schoolbook, standard (`2`/bit) adders: `2n²`
(derived, Tranche 3 `multiplier_ripple_toffoli`). With measurement-based adders this halves to `n²`. -/
def multToffoli (n : ℕ) : ℕ := 2 * n * n

/-- Toffoli cost of one `n`-bit modular **squaring**: `~n²` (≈ half a multiply, diagonal symmetry;
documented count, no verified squaring circuit exhibited). -/
def sqrToffoli (n : ℕ) : ℕ := n * n

/-- One `a=0` elliptic-curve **doubling** = `2M + 5S` field ops (EFD `dbl-2009-l`). -/
def doublingToffoli (n : ℕ) : ℕ := 2 * multToffoli n + 5 * sqrToffoli n

/-- One `a=0` mixed (Jacobian+affine) **addition** = `7M + 4S` (EFD `madd-2007-bl`). -/
def additionToffoli (n : ℕ) : ℕ := 7 * multToffoli n + 4 * sqrToffoli n

/-- Windowed scalar multiplication `[k]P` over `n` bits, window `w`: `n` doublings and `n/w` additions
(the precomputed `2ⁱ·P` table is classical). -/
def windowedScalarMulToffoli (n w : ℕ) : ℕ :=
  n * doublingToffoli n + (n / w) * additionToffoli n

/-- **Tier 2 (windowing + squaring-aware, standard `2`/bit adders).** secp256k1, `w = 4`:
`226 492 416 ≈ 2.3×10⁸` Toffolis — squaring-aware costing and windowing applied to the *verified*
schoolbook multiplier; ~2.7× below the verified `6.0×10⁸`. -/
def secp256k1ToffoliWindowed : ℕ := windowedScalarMulToffoli 256 4

theorem secp256k1ToffoliWindowed_eq : secp256k1ToffoliWindowed = 226492416 := by
  simp only [secp256k1ToffoliWindowed, windowedScalarMulToffoli, doublingToffoli, additionToffoli,
    multToffoli, sqrToffoli]

/-- **Tier 3 (all standard optimisations, incl. measurement-based `1`/bit adders).** Same model with the
multiply/square costs halved (Gidney adders): secp256k1, `w = 4`: `113 246 208 ≈ 1.1×10⁸` Toffolis —
the **aggressively-optimised end** of the literature range, the same order as Gidney 2023's `≈ 5×10⁷`
("50 million Toffoli", arXiv 2306.08585), and `~3` orders below the Roetteler 2017 baseline `≈ 1.26×10¹¹`.
The measurement-adder halving is documented only (not formalisable in this measurement-free DSL); this
figure reconciles the verified scaffold with the *optimised* published estimates, factor by factor — it
is NOT the conservative baseline (which the verified figures already undercut by omitting inversion). -/
def secp256k1ToffoliOptimized : ℕ :=
  256 * (2 * (256 * 256) + 5 * (256 * 256 / 2)) + (256 / 4) * (7 * (256 * 256) + 4 * (256 * 256 / 2))

theorem secp256k1ToffoliOptimized_eq : secp256k1ToffoliOptimized = 113246208 := by
  simp only [secp256k1ToffoliOptimized]

/-! ### Modular-reduction completeness (S4)

The figures above cost *multiply-and-accumulate* but **omit the modular reduction** that keeps the
accumulator bounded after each step — a real completeness gap (`mulCircuit_correct_zmod` reduces only
*semantically*, by reading the register in `ZMod N`; no reduction circuit is costed). Each accumulate
step needs one reduction = **compare-and-conditional-subtract**:

* the **comparison** is the ripple adder's carry-out, **verified** by
  `Reversible.rippleCirc_carryout` (preset register `A := 2ⁿ − N`; carry-out `= decide (N ≤ x)`), and
  the reduce *value* for the `x ≥ N` branch is **verified** by `Reversible.rippleCirc_modReduce_ge`;
* the **conditional subtract** (flag-controlled adder, so the `x < N` branch is untouched) is
  **documented** — a controlled adder is control-heavier than the measurement-free DSL exhibits.

A reduction therefore costs ≈ one comparison adder + one (controlled) subtract adder ≈ `2` adders ≈
`4n` Toffoli; the schoolbook multiply does `n` accumulate steps, so reduction adds `n · 4n = 4n²`,
taking the modular multiply from `2n²` to `6n²` (≈ 3×, consistent with the standard
multiply-vs-modular-multiply ratio). Standard optimised modular-arithmetic costings (Roetteler et al.;
Häner et al.) fold the reduction into their per-multiply figure, so a like-for-like comparison with the
published `~10⁸` should use the reduction-inclusive baseline below rather than the un-reduced `6.0×10⁸`
(this is a modelling assumption about what the external figures count, not a verified fact). The
reduction-inclusive *baseline* below restores that apples-to-apples comparison. -/

/-- Toffoli cost of one `n`-bit modular **reduction** (compare-and-conditional-subtract): ≈ 2 adders =
`4n`. The comparison adder is verified (`Reversible.rippleCirc_carryout`); the conditional-subtract
adder is documented (flag-controlled, not exhibited in the control-light DSL). -/
def modReduceToffoli (n : ℕ) : ℕ := 4 * n

/-- Toffoli cost of one `n`-bit **modular multiply, reduction included**: schoolbook `2n²` (verified,
Tranche 3) plus `n` reductions at `4n` each = `2n² + 4n² = 6n²` (≈ 3× the un-reduced multiply). -/
def modMultToffoli (n : ℕ) : ℕ := multToffoli n + n * modReduceToffoli n

theorem modMultToffoli_eq (n : ℕ) : modMultToffoli n = 6 * n * n := by
  simp only [modMultToffoli, multToffoli, modReduceToffoli]; ring

/-- **Reduction-inclusive verified-class baseline.** The refined figure `6.0×10⁸` re-costed with the
modular multiply `6n²` (reduction included) in place of the un-reduced `2n²`, i.e. `3×`:
`secp256k1ToffoliRefined · 3 = 1 811 939 328 ≈ 1.8×10⁹`. This is the honest reduction-complete baseline
for the exhibited circuits + the documented reduction; the published optimised `~10⁸` reaches its figure
from *here* (not from `6.0×10⁸`) via windowing + sub-quadratic multiply + measurement adders. -/
def secp256k1ToffoliWithReduction : ℕ := 3 * secp256k1ToffoliRefined

theorem secp256k1ToffoliWithReduction_eq : secp256k1ToffoliWithReduction = 1811939328 := by
  simp only [secp256k1ToffoliWithReduction, secp256k1ToffoliRefined, Secp256k1.bits]

/-! ### The `(Toffoli, depth, qubits)` triple — the multi-metric resource profile (S1 close)

A resource estimate is a *triple*, not a single Toffoli count: gate count, **depth** (parallel time),
and **qubit width** (space). The Toffoli axis is tiered above (`6.0×10⁸` verified → `1.1×10⁸`
optimised). This section completes the triple for the two remaining axes, with each value's status
explicit — the same verified-anchor / documented-composition discipline.

**Depth.** The verified *principle* is `Reversible.sequential_depth : depth (sequential c) = c.length`
(a fully-sequentialised circuit has depth equal to its gate count), realised concretely for the ripple
adder by `rippleCirc_sequential_depth` (`depth = 4n`). The scalar-multiplication circuit is **not
assembled as a `Circuit` at this scale**, so we *apply that principle as a documented estimate*: its
sequential depth is of the same order as its gate count (the Toffoli figure `6.0×10⁸`, plus CNOTs), with
no parallelism — the honest baseline. The **optimised depth** exploits parallelism the framework
*demonstrates* at small scale (`reduceTree4`: a `LayerWF`-proven log-depth reduction tree): carry-lookahead
adders at `O(log n)` depth (the reduction tree is their carry-prefix core) and partial products summed in
a tree. The composition factors below (CLA-add depth `≈ 2·log₂n`, `log₂n` tree levels, the EFD field-mult
profile as the per-point-op sequential bound) are **documented**, not verified circuits; the figure is a
cost-model estimate placing the optimised depth at `~10⁵–10⁶ layers`, consistent with the published
256-bit ECC depth range.

**Qubits.** The exhibited circuits allocate a *fresh* carry chain per multiply step (no reuse), giving
`O(n²)` width — `~n² = 65 536` for `n=256` (the carry banks dominate). The **space-optimal** width
uncomputes/reuses ancilla, giving `O(n)` — the published figure is `~2330` logical qubits. The baseline
is structural to the exhibited circuit; the optimised value is documented (ancilla reuse is not modelled
in the allocate-only DSL).

The honest reading: the *verified* triple is `(6.0×10⁸ Toffoli, =gate-count depth, O(n²) qubits)` — a
correct profile for the exhibited unoptimised circuits. The *optimised* triple
`(1.1×10⁸, ~6×10⁵, ~2330)` is the documented reconciliation with the literature, factor by factor. -/

/-- **Sequential depth ≈ gate count** (documented estimate applying the verified *principle*
`Reversible.sequential_depth`, which is realised concretely only for the ripple adder,
`rippleCirc_sequential_depth`). With no parallelism, depth equals gate count; the secp256k1 scalar
multiply is not assembled as a `Circuit` at this scale, so we take its sequential depth as of the same
order as the Toffoli figure `6.0×10⁸` (plus CNOTs). The honest worst-case-time baseline. -/
def secp256k1DepthSequential : ℕ := secp256k1ToffoliRefined

theorem secp256k1DepthSequential_eq : secp256k1DepthSequential = 603979776 := by
  simp only [secp256k1DepthSequential, secp256k1ToffoliRefined, Secp256k1.bits]

/-- **Optimised depth** (documented cost model): `256` point-ops, each `≤18` sequential field-ops (EFD
profile), each a parallel multiply of depth `≈ log₂256` tree levels × `≈ 2·log₂256` carry-lookahead-add
depth = `8·16`. `256·18·8·16 = 589 824 ≈ 5.9×10⁵ layers` — in the published 256-bit ECC depth range.
The CLA/parallel circuits are documented, not exhibited; the log-depth *principle* is demonstrated at
4 wires by `reduceTree4` (this 256-bit figure does not consume it). -/
def secp256k1DepthOptimized : ℕ := 256 * 18 * 8 * 16

theorem secp256k1DepthOptimized_eq : secp256k1DepthOptimized = 589824 := by
  simp only [secp256k1DepthOptimized]

/-- **Baseline qubit width** (structural to the exhibited circuit): a fresh carry chain per multiply
step (no reuse) ⇒ `O(n²)`; the carry banks alone are `~n² = 65 536` for `n=256`. -/
def secp256k1QubitsBaseline : ℕ := 256 * 256

theorem secp256k1QubitsBaseline_eq : secp256k1QubitsBaseline = 65536 := by
  simp only [secp256k1QubitsBaseline]

/-- **Space-optimal qubit width** (documented, ancilla reuse not modelled in the allocate-only DSL):
`O(n)` ⇒ the published `~2330` logical qubits for 256-bit ECDLP. -/
def secp256k1QubitsOptimized : ℕ := 2330

/-! ### H1 — secp256k1 figure from the verified modular arithmetic

The figures above (`secp256k1ToffoliRefined`, `…WithReduction`, the tiered cost model) cost every field
multiplication with the **Tranche-3 schoolbook multiplier** `multToffoli n = 2n²` — a *quantum × classical*,
**reduction-free** count — and fix the per-point-op field-mult counts to the *documented* EFD `7`/`11`.
The S6.3 programme has since produced something stronger and value-correct: a **verified** modular field
multiply `X·Y mod N` (`Reversible.mulLoop_correct`) whose Toffoli cost is *derived*
(`Reversible.mulLoop_toffoli : (circuitCost (mulLoop L)).toffoli = 30·n²`), **reduction INCLUDED**
(Horner double-and-reduce: each of the `n` steps is `modDouble` `12n` + `cModAdd` `18n`), *quantum × quantum*;
and the per-point-op field-mult counts `M_dbl = 8` (`ECDLP.M_dbl_eq`, one `a=0` doubling) and `M_add = 17`
(`ECDLP.M_add_eq`, one mixed addition) are now *derived* off the verified SLP programs, not read from the EFD.

This section closes hole **H1** by rebuilding the secp256k1 figure from the corpus's OWN verified gadget
cost (`30n²`, reduction-included, q×q) and the DERIVED `M_dbl`/`M_add` (`8`/`17`), in place of the
schoolbook `2n²` and the documented `7`/`11`. The result (~`1.3×10¹⁰`) is ~21× the schoolbook
`secp256k1ToffoliRefined` (`6.0×10⁸`); the gap is named honestly in `secp256k1ToffoliVerifiedArith`'s
docstring. **Neither number is "the cost to break secp256k1":** the verified-arith figure is an honest
upper bound on the *exhibited unoptimised verified circuit*; the schoolbook figure is a thinner, more
optimistic accounting. -/

/-- **Per-field-multiply Toffoli cost, verified.** `30·n²` — the derived cost of the value-correct
general-`n` modular field multiply `X·Y mod N` (`Reversible.mulLoop_toffoli`), **reduction INCLUDED** (the
Horner double-and-reduce: each of the `n` steps is `modDouble` `12n` + `cModAdd` `18n`), *quantum × quantum*.
This replaces the schoolbook `multToffoli n = 2n²` (quantum × classical, reduction-free) used in the
figures above. The link to the verified circuit is the theorem `verifiedModMulToffoli_eq_mulLoop`. -/
def verifiedModMulToffoli (n : ℕ) : ℕ := 30 * n ^ 2

/-- **The verified-arithmetic link.** `verifiedModMulToffoli n` is exactly the derived Toffoli cost of the
value-correct modular field multiply, for any concrete `n`-bit multiply-loop layout
(`Reversible.mulLoop_toffoli`). This makes the citation in `verifiedModMulToffoli`'s docstring a theorem,
not a comment. -/
theorem verifiedModMulToffoli_eq_mulLoop {m n : ℕ} (L : MulLoopLayout m n) :
    verifiedModMulToffoli n = (circuitCost (mulLoop L)).toffoli :=
  (mulLoop_toffoli L).symm

theorem verifiedModMulToffoli_secp256k1 : verifiedModMulToffoli Secp256k1.bits = 1966080 := by
  norm_num [verifiedModMulToffoli, Secp256k1.bits]

/-- Verified-arithmetic cost of one `a=0` elliptic-curve **doubling**: `M_dbl` derived field multiplies
(`= 8`), each the verified `verifiedModMulToffoli` (`30w²`). Closed form `240·w²`. -/
def verifiedDoublingToffoli (w : ℕ) : ℕ := M_dbl * verifiedModMulToffoli w

theorem verifiedDoublingToffoli_eq (w : ℕ) : verifiedDoublingToffoli w = 240 * w ^ 2 := by
  simp only [verifiedDoublingToffoli, M_dbl_eq, verifiedModMulToffoli]; ring

theorem verifiedDoublingToffoli_secp256k1 : verifiedDoublingToffoli Secp256k1.bits = 15728640 := by
  rw [verifiedDoublingToffoli_eq]; norm_num [Secp256k1.bits]

/-- Verified-arithmetic cost of one **mixed** elliptic-curve **addition**: `M_add` derived field
multiplies (`= 17`), each the verified `verifiedModMulToffoli` (`30w²`). Closed form `510·w²`. -/
def verifiedAdditionToffoli (w : ℕ) : ℕ := M_add * verifiedModMulToffoli w

theorem verifiedAdditionToffoli_eq (w : ℕ) : verifiedAdditionToffoli w = 510 * w ^ 2 := by
  simp only [verifiedAdditionToffoli, M_add_eq, verifiedModMulToffoli]; ring

theorem verifiedAdditionToffoli_secp256k1 : verifiedAdditionToffoli Secp256k1.bits = 33423360 := by
  rw [verifiedAdditionToffoli_eq]; norm_num [Secp256k1.bits]

/-- **ECDLP / secp256k1 — the verified-arithmetic Toffoli figure (H1).** The worst-case double-and-add
operation count `≤ Secp256k1.bits · (M_dbl + M_add)` (one doubling and at most one addition per bit, the
derived counts `8`/`17`) times the verified per-field-multiply cost `verifiedModMulToffoli Secp256k1.bits`
(`30·256²`, reduction-included, q×q). The analogue of `secp256k1ToffoliRefined` with the corpus's OWN
verified gadget in place of the schoolbook `2n²` and the derived `M_dbl`/`M_add` in place of the EFD
`7`/`11`.

**Honest positioning vs `secp256k1ToffoliRefined` (`6.0×10⁸`).** This figure is `12 582 912 000 ≈
1.3×10¹⁰`, about **21× higher**, decomposing as `≈15× (per-multiply) × ≈1.4× (M-count)`:
**(a) per-multiply, ×15** — the schoolbook figure costs each multiply at `2n²` *quantum × classical* and
**reduction-free**, whereas `verifiedModMulToffoli` is `30n²` *quantum × quantum* with the **modular
reduction included** (the verified Horner double-and-reduce: `30/2 = 15`); the *cause* of the `30`-vs-`2`
constant is the absent **carry-clean adder** — the corpus's verified gadgets allocate fresh ancilla per
step (`Θ(n²)` qubits, the orthogonal `Θ(n²)→Θ(n)` residue), where an in-place Cuccaro/Takahashi-class
adder would bring the per-multiply count back toward the standard `2n²`. **(b) M-count, ×1.4** — the
derived per-op field-multiply counts rose to `M_dbl + M_add = 25` (8 + 17) from the EFD `7 + 11 = 18`
(`25/18 ≈ 1.39`). So this is an honest **upper bound on the exhibited unoptimised verified circuit**,
reduction-complete and value-correct; `secp256k1ToffoliRefined` is a thinner, more optimistic accounting.
Neither is "the cost to break secp256k1".

**Honesty on the width.** The per-multiply cost formula `mulLoop_toffoli = 30n²` is unconditional in `n`,
but the value-correctness witness (`mulLoop_correct` with its full hypothesis bundle jointly discharged)
is exhibited concretely only at `n = 3` (`wMulLoop`); the `n = 256` figure is the proven cost-formula
**extrapolation** of that verified gadget family, not a separately-exhibited 256-bit value-correct
circuit. (The `n`-general layout inhabitability is asserted in `ModularMulLoop.lean`, not formally
exhibited at 256.) -/
def secp256k1ToffoliVerifiedArith : ℕ :=
  Secp256k1.bits * (M_dbl + M_add) * verifiedModMulToffoli Secp256k1.bits

/-- The verified-arithmetic figure evaluates to `12 582 912 000 ≈ 1.3×10¹⁰` Toffolis: `256` bits ×
`(8 + 17) = 25` field mults/bit × `30·256² = 1 966 080` Toffolis per reduction-included field multiply. -/
theorem secp256k1ToffoliVerifiedArith_eq : secp256k1ToffoliVerifiedArith = 12582912000 := by
  norm_num [secp256k1ToffoliVerifiedArith, M_dbl_eq, M_add_eq, verifiedModMulToffoli, Secp256k1.bits]

/-- **ECDLP / secp256k1 — the verified-arithmetic scalar-multiplication bound (H1).** For a scalar `k`
with `Nat.size k ≤ Secp256k1.bits`, the double-and-add field-multiply count weighted by the DERIVED
per-op counts `M_dbl`/`M_add`, times the verified per-field-multiply cost
`verifiedModMulToffoli Secp256k1.bits`, is at most `secp256k1ToffoliVerifiedArith`. Mirrors
`secp256k1_scalarMul_toffoli_refined` with the verified `30n²` gadget and the derived `8`/`17` in place of
the schoolbook `2n²` and the EFD `7`/`11`. -/
theorem secp256k1_scalarMul_toffoli_verified_arith (k : ℕ) (hk : Nat.size k ≤ Secp256k1.bits) :
    doubleAndAddWeightedCost M_dbl M_add k * verifiedModMulToffoli Secp256k1.bits
      ≤ secp256k1ToffoliVerifiedArith := by
  calc doubleAndAddWeightedCost M_dbl M_add k * verifiedModMulToffoli Secp256k1.bits
      ≤ Nat.size k * (M_dbl + M_add) * verifiedModMulToffoli Secp256k1.bits := by
        gcongr; exact doubleAndAddWeightedCost_le M_dbl M_add k
    _ ≤ Secp256k1.bits * (M_dbl + M_add) * verifiedModMulToffoli Secp256k1.bits := by gcongr
    _ = secp256k1ToffoliVerifiedArith := rfl

/-! ### Stage 3 — secp256k1 figure from the carry-clean modular arithmetic

The H1 section above costs each field multiply with the **dirty** verified gadget
`verifiedModMulToffoli n = 30·n²` (`Reversible.mulLoop`), whose Horner double-and-reduce allocates a
**fresh ancilla bank per step** — `Θ(n²)` qubits. Stage 2b (`Reversible.cuccaroModMul`) produced a
**carry-clean** modular field multiply `X·Y mod N` that reuses **one shared scratch bank** across all
`n` Horner steps, restoring every scratch wire (`cuccaroModMul_clean`); its derived Toffoli cost is
`Reversible.cuccaroModMul_toffoli : (circuitCost (cuccaroModMul L)).toffoli = (20·n + 14)·n =
20·n² + 14·n`, **reduction included**, *quantum × quantum*.

This section rebuilds the secp256k1 figure from the carry-clean gadget. It captures **two** gains:

* **(modest) Toffoli improvement** — `20n² + 14n` vs the dirty `30n²` (≈ `1.5×` at `n = 256`); the
  modular reduction per step is irreducible in this measurement-free `CCX`-only DSL, so the constant
  cannot drop to the non-modular `~2n²`.
* **(real) qubit collapse Θ(n²) → Θ(n)** — the headline `cleanModMulQubits n = 6n + 6` (a single shared
  bank: `Acc, B/Mask2, Nreg, Mask` each `n+1` wires, `flag`, `Z`, plus the read-only `Y`, `X` registers
  each `n` wires), inhabited for every `n ≥ 1` by `cleanModMulQubits_inhabited`. The dirty `mulLoop`
  allocates `n` fresh banks, i.e. `Θ(n²)` wires (`secp256k1QubitsBaseline = n² = 65 536`); the clean
  route needs `6·256 + 6 = 1 542`.

## Three secp256k1 Toffoli figures, positioned honestly

| figure | per-multiply | reduction | width | value |
| --- | --- | --- | --- | --- |
| `secp256k1ToffoliRefined` | `2n²` schoolbook, q × classical | **omitted** | `Θ(n²)` | `6.0×10⁸` (optimistic) |
| `secp256k1ToffoliVerifiedArith` (H1) | `30n²` verified dirty | included | `Θ(n²)` | `1.26×10¹⁰` |
| `secp256k1ToffoliCleanArith` (here) | `20n² + 14n` verified clean | included | **`Θ(n)`** | `8.41×10⁹` |

The clean route's **Toffoli** gain over H1 is only ≈ `1.5×` (the reduction is irreducible in this DSL);
its genuine win is the **qubit** axis, `Θ(n²) → Θ(n)`. The literature `~10⁸` Toffoli for 256-bit ECDLP
remains out of reach: it needs Gidney measurement-based adders (`~1` Toffoli/bit), which this
measurement-free DSL cannot express. **None of these is "the cost to break secp256k1"**: each is a
verified upper bound on an exhibited unoptimised circuit (and `secp256k1ToffoliRefined` omits reduction
entirely), all costing one scalar multiplication only (no second scalar mult, no QFT/phase-estimation
wrapper, no uncomputation accounting). -/

/-- **Per-field-multiply Toffoli cost, carry-clean.** `20·n² + 14·n` — the derived cost of the
value-correct carry-clean modular field multiply `X·Y mod N` (`Reversible.cuccaroModMul_toffoli`),
**reduction INCLUDED** (the Horner double-and-reduce: each of the `n` steps is `cuccaroModDouble`
`6n + 4` + `cuccaroCModAdd` `14n + 10` = `20n + 14`), *quantum × quantum*, and running on **one shared
scratch bank** (`Θ(n)` qubits). This replaces both the schoolbook `multToffoli n = 2n²` and the dirty
verified `verifiedModMulToffoli n = 30n²`. The link to the verified circuit is the theorem
`cleanModMulToffoli_eq_cuccaro`. -/
def cleanModMulToffoli (n : ℕ) : ℕ := 20 * n ^ 2 + 14 * n

/-- **The carry-clean-arithmetic link.** `cleanModMulToffoli n` is exactly the derived Toffoli cost of
the value-correct carry-clean modular field multiply, for any concrete `n`-bit layout
(`Reversible.cuccaroModMul_toffoli`, which gives the factored `(20n + 14)·n`). This makes the citation
in `cleanModMulToffoli`'s docstring a theorem, not a comment. -/
theorem cleanModMulToffoli_eq_cuccaro {m n : ℕ} (L : CuccaroMulLayout m n) :
    cleanModMulToffoli n = (circuitCost (cuccaroModMul L)).toffoli := by
  rw [cleanModMulToffoli, cuccaroModMul_toffoli]; ring

theorem cleanModMulToffoli_secp256k1 : cleanModMulToffoli Secp256k1.bits = 1314304 := by
  norm_num [cleanModMulToffoli, Secp256k1.bits]

/-- **ECDLP / secp256k1 — the carry-clean-arithmetic Toffoli figure (Stage 3).** The worst-case
double-and-add operation count `≤ Secp256k1.bits · (M_dbl + M_add)` (the derived counts `8`/`17`) times
the carry-clean per-field-multiply cost `cleanModMulToffoli Secp256k1.bits` (`20·256² + 14·256`,
reduction-included, q × q, one shared bank). The analogue of `secp256k1ToffoliVerifiedArith` with the
carry-clean gadget in place of the dirty `30n²`.

**Honest positioning.** This figure is `8 411 545 600 ≈ 8.4×10⁹`, about `1.5×` below the dirty-arith
H1 figure `secp256k1ToffoliVerifiedArith` (`1.26×10¹⁰`) — the per-multiply ratio `(20n+14)/(30n) → 2/3`
as `n → ∞`. The reduction is included in both (the modular reduce per Horner step is irreducible in this
measurement-free `CCX`-only DSL), so the constant cannot fall to the reduction-free schoolbook `2n²` of
`secp256k1ToffoliRefined` (`6.0×10⁸`). The genuine win of the carry-clean route is **not** this `1.5×`
Toffoli factor but the **qubit collapse** `Θ(n²) → Θ(n)` (`cleanModMulQubits = 6n + 6 = 1 542` vs the
dirty `secp256k1QubitsBaseline = n² = 65 536`), a genuinely inhabited layout for every `n ≥ 1`
(`cleanModMulQubits_inhabited`). **Width convention (honest boundary):** these figures use the
programme-wide `Secp256k1.bits = 256` register width; `cuccaroModMul`'s value-correctness needs
`2N ≤ 2ⁿ`, so value-correctness *at the exact prime* `p ≈ 2²⁵⁶` is at `n = 257` (the standard +1-bit
modular-arithmetic headroom), marginally shifting `6n+6` / `20n²+14n`. The figures are arithmetic
identities on the `n = 256` register; they do not assert value-correctness at `p` with `n = 256`.
Neither figure is "the cost to break secp256k1". -/
def secp256k1ToffoliCleanArith : ℕ :=
  Secp256k1.bits * (M_dbl + M_add) * cleanModMulToffoli Secp256k1.bits

/-- The carry-clean-arithmetic figure evaluates to `8 411 545 600 ≈ 8.4×10⁹` Toffolis: `256` bits ×
`(8 + 17) = 25` field mults/bit × `20·256² + 14·256 = 1 314 304` Toffolis per reduction-included
carry-clean field multiply. -/
theorem secp256k1ToffoliCleanArith_eq : secp256k1ToffoliCleanArith = 8411545600 := by
  norm_num [secp256k1ToffoliCleanArith, M_dbl_eq, M_add_eq, cleanModMulToffoli, Secp256k1.bits]

/-- **ECDLP / secp256k1 — the carry-clean-arithmetic scalar-multiplication bound (Stage 3).** For a
scalar `k` with `Nat.size k ≤ Secp256k1.bits`, the double-and-add field-multiply count weighted by the
DERIVED per-op counts `M_dbl`/`M_add`, times the carry-clean per-field-multiply cost
`cleanModMulToffoli Secp256k1.bits`, is at most `secp256k1ToffoliCleanArith`. Mirrors
`secp256k1_scalarMul_toffoli_verified_arith` with the carry-clean `20n² + 14n` gadget. -/
theorem secp256k1_scalarMul_toffoli_clean_arith (k : ℕ) (hk : Nat.size k ≤ Secp256k1.bits) :
    doubleAndAddWeightedCost M_dbl M_add k * cleanModMulToffoli Secp256k1.bits
      ≤ secp256k1ToffoliCleanArith := by
  calc doubleAndAddWeightedCost M_dbl M_add k * cleanModMulToffoli Secp256k1.bits
      ≤ Nat.size k * (M_dbl + M_add) * cleanModMulToffoli Secp256k1.bits := by
        gcongr; exact doubleAndAddWeightedCost_le M_dbl M_add k
    _ ≤ Secp256k1.bits * (M_dbl + M_add) * cleanModMulToffoli Secp256k1.bits := by gcongr
    _ = secp256k1ToffoliCleanArith := rfl

/-! #### The qubit collapse — a verified `Θ(n)` per-field-multiply qubit count

The dirty `Reversible.mulLoop` allocates a *fresh* ancilla bank per Horner step, so its qubit width is
`Θ(n²)` (`secp256k1QubitsBaseline = n² = 65 536`). The carry-clean `Reversible.cuccaroModMul` runs on a
single shared bank reused across all `n` steps; its qubit width is the wire count of a
`Reversible.CuccaroMulLayout m n`, which is **linear** in `n`. Counting the wire families of the layout
(`CuccaroModLayout`'s `Acc`, `B = Mask2`, `Nreg`, `Mask` at `n+1` wires each, the singletons `flag`,
`Z`, and `CuccaroMulLayout`'s read-only `Y`, `X` at `n` wires each):

`4·(n+1) + 2 + 2·n = 6n + 6`.

This is the genuine structural payoff of the whole carry-clean tranche: `Θ(n²) → Θ(n)` qubits. -/

/-- **Per-field-multiply qubit count, carry-clean: `6n + 6` (`Θ(n)`).** The wire count of a
`Reversible.CuccaroMulLayout m n` — one shared scratch bank `Acc, B(=Mask2), Nreg, Mask` (`n+1` wires
each), the flag and Cuccaro ancilla `flag, Z` (`1` each), and the read-only operand registers `Y, X`
(`n` each): `4·(n+1) + 2 + 2·n = 6n + 6`. Contrast the dirty `Reversible.mulLoop`, which allocates `n`
fresh banks, i.e. `Θ(n²)` qubits (`secp256k1QubitsBaseline = n² = 65 536`). This is the headline
structural result of the carry-clean route: the qubit axis collapses from quadratic to linear. -/
def cleanModMulQubits (n : ℕ) : ℕ := 6 * n + 6

theorem cleanModMulQubits_secp256k1 : cleanModMulQubits Secp256k1.bits = 1542 := by
  norm_num [cleanModMulQubits, Secp256k1.bits]

/-- The shared carry-clean modular-adder bank on exactly `6n + 6` wires (`Acc → [0,n]`,
`B → [n+1, 2n+1]`, `Nreg → [2n+2, 3n+2]`, `Mask → [3n+3, 4n+3]`, `flag = 4n+4`, `Z = 4n+5`). The four
banks are placed in disjoint width-`(n+1)` blocks, indexed `i ↦ i % (n+1)` inside each block (injective
on `[0, n]`). -/
def cleanMulModLayout (n : ℕ) : CuccaroModLayout (6 * n + 6) n where
  Acc i := ⟨i % (n + 1), by have := Nat.mod_lt i (show 0 < n + 1 by omega); omega⟩
  B i := ⟨(n + 1) + i % (n + 1), by have := Nat.mod_lt i (show 0 < n + 1 by omega); omega⟩
  Nreg i := ⟨2 * (n + 1) + i % (n + 1), by have := Nat.mod_lt i (show 0 < n + 1 by omega); omega⟩
  Mask i := ⟨3 * (n + 1) + i % (n + 1), by have := Nat.mod_lt i (show 0 < n + 1 by omega); omega⟩
  flag := ⟨4 * (n + 1), by omega⟩
  Z := ⟨4 * (n + 1) + 1, by omega⟩
  hAccB i j := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [ne_eq, Fin.mk.injEq]; omega
  hAccN i j := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [ne_eq, Fin.mk.injEq]; omega
  hAccM i j := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [ne_eq, Fin.mk.injEq]; omega
  hBN i j := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [ne_eq, Fin.mk.injEq]; omega
  hBM i j := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [ne_eq, Fin.mk.injEq]; omega
  hNM i j := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [ne_eq, Fin.mk.injEq]; omega
  hAccflag i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hBflag i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hNflag i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hMflag i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hAccZ i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hBZ i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hNZ i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hMZ i := by
    have h1 := Nat.mod_lt i (show 0 < n + 1 by omega); simp only [ne_eq, Fin.mk.injEq]; omega
  hflagZ := by simp only [ne_eq, Fin.mk.injEq]; omega
  hAccinj i j hi hj h := by
    have hv : i % (n + 1) = j % (n + 1) := congrArg Fin.val h
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  hBinj i j hi hj h := by
    have hv : (n + 1) + i % (n + 1) = (n + 1) + j % (n + 1) := congrArg Fin.val h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv; omega
  hNinj i j hi hj h := by
    have hv : 2 * (n + 1) + i % (n + 1) = 2 * (n + 1) + j % (n + 1) := congrArg Fin.val h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv; omega
  hMinj i j hi hj h := by
    have hv : 3 * (n + 1) + i % (n + 1) = 3 * (n + 1) + j % (n + 1) := congrArg Fin.val h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv; omega

/-- The full carry-clean modular-multiply layout on exactly `6n + 6` wires (`n ≥ 1`): the shared bank
`cleanMulModLayout` plus the read-only operand registers `Y → [4n+6, 5n+5]` and `X → [5n+6, 6n+5]`,
each a disjoint width-`n` block (`i ↦ offset + i % n`). Witnesses that a `CuccaroMulLayout` exists on a
`Θ(n)` register, so the carry-clean modular multiply genuinely runs in `6n + 6` qubits. -/
def cleanMulLayout (n : ℕ) (hn : 1 ≤ n) : CuccaroMulLayout (6 * n + 6) n where
  mod := cleanMulModLayout n
  Y i := ⟨4 * (n + 1) + 2 + i % n, by have := Nat.mod_lt i (show 0 < n by omega); omega⟩
  X i := ⟨4 * (n + 1) + 2 + n + i % n, by have := Nat.mod_lt i (show 0 < n by omega); omega⟩
  hYAcc i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hYB i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hYN i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hYM i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hYflag i := by
    have h1 := Nat.mod_lt i (show 0 < n by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hYZ i := by
    have h1 := Nat.mod_lt i (show 0 < n by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hXAcc i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hXB i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hXN i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hXM i j := by
    have h1 := Nat.mod_lt i (show 0 < n by omega); have h2 := Nat.mod_lt j (show 0 < n + 1 by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hXflag i := by
    have h1 := Nat.mod_lt i (show 0 < n by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega
  hXZ i := by
    have h1 := Nat.mod_lt i (show 0 < n by omega)
    simp only [cleanMulModLayout, ne_eq, Fin.mk.injEq]; omega

/-- **The qubit collapse, verified (Stage 3 headline).** For every `n ≥ 1` there is a
`Reversible.CuccaroMulLayout` — the layout the carry-clean modular multiply `cuccaroModMul` runs on —
on exactly `cleanModMulQubits n = 6n + 6` wires. So the verified carry-clean modular field multiply
`X·Y mod N` uses `Θ(n)` qubits, against the dirty `mulLoop`'s `Θ(n²)` (fresh bank per step). This is the
genuine structural payoff of the carry-clean tranche; the Toffoli gain over the dirty figure is only
≈ `1.5×`, but the qubit axis collapses from quadratic to linear. -/
theorem cleanModMulQubits_inhabited (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (CuccaroMulLayout (cleanModMulQubits n) n) :=
  ⟨cleanMulLayout n hn⟩

/-! ### Fermat modular inversion — closing the inversion-omission gap

Every figure above (`secp256k1ToffoliRefined`, `…VerifiedArith`, `…CleanArith`) costs modular
**multiplication** in full but **omits modular inversion entirely**, so each undercounts. Projective /
Jacobian elliptic-curve coordinates legitimately avoid a *per-operation* inversion — that is exactly what
projective coordinates buy — but the scalar multiplication `[k]P` still needs **one** final inversion to
recover the affine result from projective `(X : Y : Z)` (the `Z⁻¹` of the coordinate normalisation). This
section costs that one inversion, conservatively, from the corpus's OWN verified gadget — **no new
circuit**.

The route is **Fermat** (`ECDLP.Inversion`): over the prime field `ZMod p`, `a⁻¹ = a^{p-2}`
(`fermatInv_eq_inv`, carrying `[Fact p.Prime]` — the named secp256k1 primality residue), a modular
exponentiation. Square-and-multiply costs `≤ 2·Nat.size (p-2) ≤ 2n` modular multiplies
(`fermatInvFieldMults_le`), each the verified carry-clean `cleanModMulToffoli n = 20n²+14n`. So one
inversion is `2n·(20n²+14n) = O(n³)` Toffoli — derived from the existing multiply, not annotated.

**Conservative, by design.** The optimal extended-Euclid / Kaliski inversion is `O(n²)`, cheaper, but
needs a separate verified inversion circuit (named residue). Fermat is what can be costed from what the
corpus already has. The heavier **affine** alternative — a per-operation inversion, `~2·Nat.size k`
inversions over the whole scalar multiply rather than one — is stated here for context but **not built**;
projective coordinates are precisely the standard way to avoid it. -/

/-- **Per-inversion Toffoli cost, Fermat route.** `(2n)·cleanModMulToffoli n = 2n·(20n²+14n)` — the
square-and-multiply op count `≤ 2n` (`ECDLP.fermatInvFieldMults_le`, `n = Nat.size (p-2)` width) times the
verified carry-clean modular multiply (`cleanModMulToffoli`, reduction-included, q × q). The conservative
`O(n³)` cost of one modular inversion `a⁻¹ = a^{p-2}`, built from the EXISTING verified multiply (no new
circuit). The optimal Euclid/Kaliski inversion is `O(n²)` but needs a separate verified circuit.

**Two levels of guarantee (honest line).** The inversion *value*-correctness is a PROVED theorem
(`ECDLP.fermatInv_eq_inv : a^{p-2} = a⁻¹` for prime `p`, via Fermat). The inversion *count* `2n` is a
derived op-count MODEL (`modExpFieldMults`, square-and-multiply, same status as `doubleAndAddCost`): there
is no separately-exhibited `a^{p-2}` exponentiation *circuit* whose denotation is `a⁻¹` and whose gate
tally is this product — only the per-multiply `cleanModMulToffoli` is a verified circuit cost. So "derived"
here means "op-count model × verified-per-multiply", not "verified exponentiation circuit". -/
def fermatInvToffoli (n : ℕ) : ℕ := (2 * n) * cleanModMulToffoli n

/-- **Op-count honesty.** The leading `2n` factor of `fermatInvToffoli` is the proved square-and-multiply
bound on the Fermat exponentiation's field multiplies (`ECDLP.fermatInvFieldMults_le`, valid at any
register width `n ≥ Nat.size (p-2)`): `fermatInvFieldMults p ≤ 2 · Nat.size (p-2) ≤ 2n`. So the inversion
cost is the *derived* op count times the verified per-multiply Toffoli. -/
theorem fermatInvToffoli_field_mult_bound (p n : ℕ) (hn : Nat.size (p - 2) ≤ n) :
    fermatInvFieldMults p ≤ 2 * n :=
  le_trans (fermatInvFieldMults_le p) (by gcongr)

/-- One secp256k1 modular inversion via Fermat costs `672 923 648 ≈ 6.7×10⁸` Toffolis:
`2·256 = 512` verified carry-clean multiplies, each `cleanModMulToffoli 256 = 1 314 304`. -/
theorem fermatInvToffoli_secp256k1 : fermatInvToffoli Secp256k1.bits = 672923648 := by
  norm_num [fermatInvToffoli, cleanModMulToffoli, Secp256k1.bits]

/-- **ECDLP / secp256k1 — the carry-clean figure WITH the final coordinate-recovery inversion.** The
carry-clean scalar-multiplication figure `secp256k1ToffoliCleanArith` (`8.41×10⁹`, which omits inversion)
plus the ONE final projective→affine inversion costed via Fermat (`fermatInvToffoli Secp256k1.bits`,
`6.7×10⁸`). This closes the "omits inversion" gap of the prior figures, conservatively.

**What this counts, exactly.** Projective `[k]P` does NOT pay a per-operation inversion (that is the point
of projective coordinates); it pays exactly one inversion at the end to normalise `(X:Y:Z) ↦ (X/Z, Y/Z)`.
That one inversion is costed here via Fermat (`a^{p-2}`, `≤ 2n` verified carry-clean multiplies, `O(n³)`).
The optimal extended-Euclid/Kaliski inversion is `O(n²)`, cheaper, but is a separate verified-circuit
residue. The heavier **affine** variant (a per-op inversion, `~2·Nat.size k` inversions) is not built —
projective coordinates avoid it. `p`-primality is the named residue carried by `fermatInv_eq_inv`'s
`[Fact p.Prime]`. Still one scalar multiplication only: no second scalar mult, no QFT/phase-estimation
wrapper, no uncomputation accounting. -/
def secp256k1ToffoliCleanArithWithInversion : ℕ :=
  secp256k1ToffoliCleanArith + fermatInvToffoli Secp256k1.bits

/-- The inversion-inclusive carry-clean figure evaluates to `9 084 469 248 ≈ 9.1×10⁹` Toffolis:
`secp256k1ToffoliCleanArith = 8 411 545 600` plus the one Fermat inversion `fermatInvToffoli 256 =
672 923 648`. -/
theorem secp256k1ToffoliCleanArithWithInversion_eq :
    secp256k1ToffoliCleanArithWithInversion = 9084469248 := by
  rw [secp256k1ToffoliCleanArithWithInversion, secp256k1ToffoliCleanArith_eq,
    fermatInvToffoli_secp256k1]

end ECDLP.ResourceBounds
