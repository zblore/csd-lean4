import CsdLean4.Mathlib.QuantumInfo.ECDLP.ScalarMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduce
import CsdLean4.Mathlib.QuantumInfo.ECDLP.Secp256k1

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
of Tranche 3 and the verified `doubleAndAddWeightedCost`). The standard literature applies three further
optimisations to reach `~10⁸` Toffolis for 256-bit ECDLP; each is a *documented, standard* technique, but
of differing verification status in this development:

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
**consistent with the optimised literature (`~10⁸`)**. The measurement-adder halving is documented only
(not formalisable in this measurement-free DSL); this figure reconciles the verified scaffold with the
published optimised estimates, factor by factor. -/
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

end ECDLP.ResourceBounds
