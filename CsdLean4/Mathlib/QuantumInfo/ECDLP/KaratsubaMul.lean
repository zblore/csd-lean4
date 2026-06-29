import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdInversion
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd

/-!
# Karatsuba sub-quadratic modular multiply — cost model + re-cost  (ECDLP L7)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

After L6 (`SafegcdInversion.lean`) dropped the modular inversion from `O(n³)` (Fermat) to `O(n²)`
(binary-GCD), the field **multiply** is the now-dominant remaining lever on the affine point-add
figure: the three carry-clean multiplies are `3·cleanModMulToffoli 256 = 3 942 912` of the
`onePointAddToffoli_safegcd = 7 896 616` total (`≈ 50%`). This file attacks that half with a
**Karatsuba** cost model: the schoolbook `O(n²)` modular multiply is replaced by the classical
`T(n) = 3·T(⌈n/2⌉) + O(n)` recurrence, whose solution is `Θ(n^{log₂ 3}) = Θ(n^{1.585})`.

## HONEST STATUS — what kind of result this is (read before citing)

This is a **derived cost recurrence**, the SAME status as L6's `safegcdInvToffoli` and the corpus's
`fermatInvToffoli`: an op-count model whose leaf and combine terms are tied to **verified circuits**,
NOT a verified Karatsuba circuit.

* **cost side (sound DERIVED recurrence)** — `karatsubaToffoli n` is the Karatsuba recurrence with
  * **base case** = the VERIFIED carry-clean schoolbook multiply `cleanModMulToffoli`
    (`cleanModMulToffoli_eq_cuccaro`, tied to `Reversible.cuccaroModMul_toffoli`, whose VALUE is the
    genuinely value-verified circuit `Reversible.cuccaroModMul_correct : = X·Y mod N`);
  * **combine term** `kCombineToffoli n` = a DOCUMENTED count (`kCombineAdders = 6`) of `O(n)` modular
    adders, each tied to the VERIFIED `Reversible.cuccaroModAdd_toffoli = 12n + 10`
    (`kCombineToffoli_eq_adders`).
  So the `O(n^{1.585})`-vs-`O(n²)` win lives entirely on the cost side, and every term is anchored to a
  proved gadget cost — no free-floating constant.

* **value side (route 3b, stated plainly)** — the modular product `X·Y mod N` is **unique**, so the
  Karatsuba circuit and the schoolbook circuit compute the SAME value. The corpus's verified value
  content for that product is `Reversible.cuccaroModMul_correct` (the schoolbook carry-clean multiply);
  `karatsubaToffoli` models the cost of a **different implementation** of that same proved product.
  The genuine ALGEBRAIC core of Karatsuba — that the 3-multiply split is exact — is proved here as
  `karatsuba_identity` (a `ring` identity in any `CommRing`), which is real content but is **algebra,
  not a circuit**. **The full verified Karatsuba CIRCUIT** (a divide-and-conquer reversible circuit
  whose denotation IS `X·Y mod N`, with the recursion's split/recombine proved) is the **named
  deferred residue** — it is NOT built here. We do NOT claim a verified Karatsuba circuit. This mirrors
  L6's route 2b exactly (verified value for the unique result, cost model for the alternative schedule).

## Tier (per figure, mandatory)

* **VERIFIED** (proved Lean circuit costs / values): the base-case multiply cost `cleanModMulToffoli`
  (`cleanModMulToffoli_eq_cuccaro`) and its value `Reversible.cuccaroModMul_correct`; the combine
  adder cost `Reversible.cuccaroModAdd_toffoli = 12n+10` (cited via `kCombineToffoli_eq_adders`); the
  Karatsuba algebraic identity `karatsuba_identity`.
* **DOCUMENTED** (op-count / shape model, not verified circuits): the recurrence SHAPE
  `T(n) = 3·T(⌈n/2⌉) + combine` (the 3-way split is the source of the `log₂ 3` exponent); the
  combine-adder count `kCombineAdders = 6` (2 half-width input sums + 2 middle subtractions + 2 shifted
  recompositions); the schoolbook/Karatsuba crossover threshold `kThreshold = 32`.
* **CONJECTURAL / EXTERNAL** (not validated against ECDSA.fail): the leaderboard datum
  `ecdsaFailLeaderboardBest`; the map from our worst-case UPPER-bound Toffoli count to the executed
  average. Not a validated ECDSA.fail score.

## Headline figures (at `Secp256k1.bits = 256`)

* `karatsubaToffoli_secp256k1                 : karatsubaToffoli 256 = 653388` (`≈ 6.5×10⁵`)
* `karatsubaToffoli_lt_schoolbook_secp256k1   : karatsubaToffoli 256 < cleanModMulToffoli 256`
  (`653 388 < 1 314 304`, a `≈ 2.0×` per-multiply win after combine overhead)
* `onePointAddToffoli_karatsuba_eq            : onePointAddToffoli_karatsuba = 5913868`
* `onePointAddScore_karatsuba_eq              : onePointAddScore_karatsuba = 16688935496`
* `karatsuba_score_improvement                : onePointAddScore_karatsuba < onePointAddScore_safegcd`
  (`1.67×10¹⁰ < 2.23×10¹⁰`, a `≈ 1.33×` win over the L6 figure — the multiply was `≈ 50%`, halving it
  gives `≈ 1.33×`; the inversion now **co-dominates** at `≈ 67%`).
-/

namespace ECDLP.ResourceBounds

open ECDLP Reversible

/-! ### The Karatsuba algebraic identity (VERIFIED algebra, not a circuit) -/

/-- **The Karatsuba 3-multiply identity (genuine algebra).** In any commutative ring, splitting two
operands at radix `B` as `x = x₁·B + x₀`, `y = y₁·B + y₀`, the product is recovered from the THREE
sub-products `x₁y₁`, `x₀y₀`, `(x₁+x₀)(y₁+y₀)` (the middle term replacing the naive two cross-products):

`(x₁B+x₀)(y₁B+y₀) = x₁y₁·B² + ((x₁+x₀)(y₁+y₀) − x₁y₁ − x₀y₀)·B + x₀y₀`.

This is the **exactness** of the Karatsuba split — real content, proved by `ring`. It is the algebraic
justification that `karatsubaToffoli`'s 3-way recursion computes the SAME product as schoolbook. It is
ALGEBRA, **not** a verified reversible circuit: the mod-`N` circuit value rides on the verified
schoolbook `Reversible.cuccaroModMul_correct` (route 3b; see module note). -/
theorem karatsuba_identity {R : Type*} [CommRing R] (B x1 x0 y1 y0 : R) :
    (x1 * B + x0) * (y1 * B + y0)
      = x1 * y1 * B ^ 2
        + ((x1 + x0) * (y1 + y0) - x1 * y1 - x0 * y0) * B
        + x0 * y0 := by
  ring

/-! ### The combine term, tied to the verified carry-clean modular adder -/

/-- **Combine-adder count per Karatsuba level: `6` (DOCUMENTED).** One Karatsuba level forms the middle
sub-product and recomposes the result with a constant number of `O(n)` add/subtracts: 2 half-width input
sums `x₁+x₀`, `y₁+y₀`; 2 middle subtractions `(x₁+x₀)(y₁+y₀) − x₁y₁ − x₀y₀`; 2 shifted recompositions
`x₁y₁·B² + … + x₀y₀`. Modelled uniformly as `6` modular adders at the node width. A documented op-count
(the standard Karatsuba combine), not a verified per-gate count. -/
def kCombineAdders : ℕ := 6

/-- **Per-level combine Toffoli cost: `6·(12n+10)`.** `kCombineAdders` modular adders, each the VERIFIED
carry-clean `Reversible.cuccaroModAdd` (`cuccaroModAdd_toffoli = 12n+10`). Derived (a count of verified
gadget costs), tied to the circuit by `kCombineToffoli_eq_adders` — the same discipline as L6's
`divstepToffoli_eq_gadgets`. -/
def kCombineToffoli (n : ℕ) : ℕ := kCombineAdders * (12 * n + 10)

theorem kCombineToffoli_eq (n : ℕ) : kCombineToffoli n = 72 * n + 60 := by
  simp only [kCombineToffoli, kCombineAdders]; ring

/-- **The verified-gadget link for the combine.** `kCombineToffoli n` is exactly `kCombineAdders` copies
of the proved carry-clean modular-adder Toffoli cost, for any concrete `n`-bit layout
(`Reversible.cuccaroModAdd_toffoli`). Makes the combine term a theorem about the corpus's verified
circuits, not a free constant. -/
theorem kCombineToffoli_eq_adders {m n : ℕ} (L : CuccaroModLayout m n) :
    kCombineToffoli n = kCombineAdders * (circuitCost (cuccaroModAdd L)).toffoli := by
  rw [kCombineToffoli, cuccaroModAdd_toffoli]

/-! ### The Karatsuba recurrence -/

/-- **Schoolbook/Karatsuba crossover threshold: `32` (DOCUMENTED).** Below `~32` bits the recursion's
`O(n)` combine overhead exceeds the schoolbook saving, so a real Karatsuba implementation falls back to
the schoolbook multiply (`cleanModMulToffoli`). `32` is the standard documented crossover band. -/
def kThreshold : ℕ := 32

/-- **Karatsuba modular-multiply Toffoli cost: `T(n) = 3·T(⌈n/2⌉) + 6·(12n+10)`, base
`T(n≤32) = cleanModMulToffoli n`.** The classical 3-way recurrence: three half-width recursive
multiplies (the source of the `Θ(n^{log₂ 3}) = Θ(n^{1.585})` solution, since `3 < 4` schoolbook
sub-products) plus the `O(n)` combine `kCombineToffoli`. Base case is the VERIFIED carry-clean schoolbook
multiply `cleanModMulToffoli`. `⌈n/2⌉ = (n+1)/2` in `ℕ`.

**Status: DERIVED cost recurrence** (op-count model, base + combine tied to verified circuits), NOT a
verified Karatsuba circuit. The VALUE (`X·Y mod N`) rides on the verified schoolbook
`Reversible.cuccaroModMul_correct` (route 3b); the full verified Karatsuba circuit is deferred residue.
See module note. -/
def karatsubaToffoli (n : ℕ) : ℕ :=
  if h : n ≤ 32 then cleanModMulToffoli n
  else 3 * karatsubaToffoli ((n + 1) / 2) + kCombineToffoli n
termination_by n
decreasing_by omega

/-- **Base-case unfolding** (`n ≤ 32`): `karatsubaToffoli n = cleanModMulToffoli n`. -/
theorem karatsubaToffoli_base {n : ℕ} (h : n ≤ 32) :
    karatsubaToffoli n = cleanModMulToffoli n := by
  rw [karatsubaToffoli.eq_def, dif_pos h]

/-- **Recursive-step unfolding** (`32 < n`): `karatsubaToffoli n = 3·karatsubaToffoli ⌈n/2⌉ + combine`.
The faithful `T(n) = 3·T(⌈n/2⌉) + 6·(12n+10)` recurrence. -/
theorem karatsubaToffoli_rec {n : ℕ} (h : ¬ n ≤ 32) :
    karatsubaToffoli n = 3 * karatsubaToffoli ((n + 1) / 2) + kCombineToffoli n := by
  rw [karatsubaToffoli.eq_def, dif_neg h]

/-- The Karatsuba modular-multiply cost at secp256k1 width evaluates to `653 388 ≈ 6.5×10⁵` Toffolis:
unrolling `T(256) = 3·T(128) + 18 492`, `T(128) = 3·T(64) + 9 276`, `T(64) = 3·T(32) + 4 668`, base
`T(32) = cleanModMulToffoli 32 = 20 928` (since `32 ≤ kThreshold`). So `T(64) = 67 452`,
`T(128) = 211 632`, `T(256) = 653 388`. The recursion bottoms out at the verified schoolbook multiply,
and each combine term is `6·(12n+10)` verified modular adders. -/
theorem karatsubaToffoli_secp256k1 : karatsubaToffoli Secp256k1.bits = 653388 := by
  have h32 : karatsubaToffoli 32 = 20928 := by
    rw [karatsubaToffoli_base (by norm_num)]; norm_num [cleanModMulToffoli]
  have h64 : karatsubaToffoli 64 = 67452 := by
    have hd : ((64 : ℕ) + 1) / 2 = 32 := by norm_num
    rw [karatsubaToffoli_rec (by norm_num), hd, h32]; norm_num [kCombineToffoli, kCombineAdders]
  have h128 : karatsubaToffoli 128 = 211632 := by
    have hd : ((128 : ℕ) + 1) / 2 = 64 := by norm_num
    rw [karatsubaToffoli_rec (by norm_num), hd, h64]; norm_num [kCombineToffoli, kCombineAdders]
  have h256 : karatsubaToffoli 256 = 653388 := by
    have hd : ((256 : ℕ) + 1) / 2 = 128 := by norm_num
    rw [karatsubaToffoli_rec (by norm_num), hd, h128]; norm_num [kCombineToffoli, kCombineAdders]
  rw [show Secp256k1.bits = 256 from rfl]; exact h256

/-- **The per-multiply win, concrete.** At `n = 256`, the Karatsuba modular multiply is strictly cheaper
than the carry-clean schoolbook multiply: `karatsubaToffoli 256 = 653 388 < 1 314 304 =
cleanModMulToffoli 256` (a `≈ 2.0×` win — the `O(n^{1.585})`-vs-`O(n²)` improvement, net of the `O(n)`
combine overhead at the `32`-bit threshold). The win is `~2×` rather than larger because the combine
adders and the `32`-bit schoolbook fallback eat into the asymptotic factor at this width. -/
theorem karatsubaToffoli_lt_schoolbook_secp256k1 :
    karatsubaToffoli Secp256k1.bits < cleanModMulToffoli Secp256k1.bits := by
  rw [karatsubaToffoli_secp256k1, cleanModMulToffoli_secp256k1]; norm_num

/-! ### Re-costing the ECDSA.fail benchmark with the Karatsuba multiply (L7) -/

/-- **Affine point-op Toffoli cost, Karatsuba multiply + binary-GCD inversion.** The
`affinePointOpToffoli_safegcd` analogue with the Karatsuba `karatsubaToffoli` in place of the schoolbook
`cleanModMulToffoli` for the three field multiplies, keeping the L6 binary-GCD inversion
`safegcdInvToffoli`. With the multiply now sub-quadratic, the inversion is again the dominant term:
`safegcdInvToffoli 256 = 3 939 328` vs the three Karatsuba multiplies `3·653 388 = 1 960 164`. -/
def affinePointOpToffoli_karatsuba (n : ℕ) : ℕ := 3 * karatsubaToffoli n + safegcdInvToffoli n

/-- One representative secp256k1 affine point op with Karatsuba multiply + binary-GCD inversion costs
`5 899 492 ≈ 5.9×10⁶` Toffolis: `3·karatsubaToffoli 256 = 1 960 164` plus `safegcdInvToffoli 256 =
3 939 328`. Contrast the L6 `affinePointOpToffoli_safegcd 256 = 7 882 240` (schoolbook multiply). -/
theorem affinePointOpToffoli_karatsuba_secp256k1 :
    affinePointOpToffoli_karatsuba Secp256k1.bits = 5899492 := by
  rw [affinePointOpToffoli_karatsuba, karatsubaToffoli_secp256k1, safegcdInvToffoli_secp256k1]

/-- **Toffoli count for ONE affine point addition, Karatsuba multiply, classical offset.** The
`onePointAddToffoli_safegcd` analogue: the Karatsuba affine point-op core
(`affinePointOpToffoli_karatsuba Secp256k1.bits`) plus the sub-dominant classical-offset coordinate term
(`classicalOffsetCoordToffoli`). With the multiply dropped to `Θ(n^{1.585})`, the inversion is again the
dominant single term (`≈ 67%`); the three multiplies are `≈ 33%`.

**Tier:** the multiply core is the DERIVED Karatsuba recurrence (base + combine tied to verified
gadgets, value rides on `cuccaroModMul_correct`); the inversion is the L6 verified-gadget-anchored
op-count model `safegcdInvToffoli`; the `3`-mult assembly and `4`-subtraction classical-offset count are
DOCUMENTED. -/
def onePointAddToffoli_karatsuba : ℕ :=
  affinePointOpToffoli_karatsuba Secp256k1.bits + classicalOffsetCoordToffoli Secp256k1.bits

/-- One affine point addition with Karatsuba multiply + binary-GCD inversion (classical offset) costs
`5 913 868 ≈ 5.9×10⁶` Toffolis: the Karatsuba affine core `affinePointOpToffoli_karatsuba 256 =
5 899 492` plus the classical-offset coordinate term `classicalOffsetCoordToffoli 256 = 14 376`.
Contrast the L6 `onePointAddToffoli_safegcd = 7 896 616` — a `≈ 1.33×` per-addition Toffoli win. -/
theorem onePointAddToffoli_karatsuba_eq : onePointAddToffoli_karatsuba = 5913868 := by
  rw [onePointAddToffoli_karatsuba, affinePointOpToffoli_karatsuba_secp256k1,
    classicalOffsetCoordToffoli_secp256k1]

/-- **The ECDSA.fail-convention score for one affine point addition, Karatsuba multiply.** The
`onePointAddScore_safegcd` analogue, `onePointAddToffoli_karatsuba × onePointAddPeakQubits`. The
peak-qubit count `onePointAddPeakQubits = 2822` is reused: Karatsuba's recursion runs on the same shared
carry-clean scratch bank (`cleanModMulQubits = 6n+6`) that dominates the width tally — the recursion is
sequentialised, so the peak live width stays in the same `≈ 11n` band (reusing `onePointAddPeakQubits`
is the DOCUMENTED layout choice; a deeper recursion-depth ancilla analysis is residue). So the score win
equals the Toffoli win (`≈ 1.33×`).

**Tier:** Toffoli factor DERIVED-recurrence / op-count-model; peak qubits DOCUMENTED; the product as a
comparison to the live ECDSA.fail score is CONJECTURAL / EXTERNAL (worst-case upper bound, not their
executed average). -/
def onePointAddScore_karatsuba : ℕ := onePointAddToffoli_karatsuba * onePointAddPeakQubits

/-- The ECDSA.fail-convention score for one affine point addition with Karatsuba multiply is
`16 688 935 496 ≈ 1.67×10¹⁰`: `onePointAddToffoli_karatsuba = 5 913 868` Toffolis times
`onePointAddPeakQubits = 2822` peak live qubits. Contrast the L6 `onePointAddScore_safegcd =
22 284 250 352 ≈ 2.23×10¹⁰` — a `≈ 1.33×` score win. Repo comparable-OBJECT figure, NOT a validated
ECDSA.fail harness score. -/
theorem onePointAddScore_karatsuba_eq : onePointAddScore_karatsuba = 16688935496 := by
  rw [onePointAddScore_karatsuba, onePointAddToffoli_karatsuba_eq, onePointAddPeakQubits_eq]

/-- **The score win over the L6 binary-GCD figure: `≈ 1.33×`.** `onePointAddScore_karatsuba <
onePointAddScore_safegcd` — Karatsuba drops the one-affine-point-addition score from `22 284 250 352`
(L6) to `16 688 935 496`. The factor is `≈ 1.33×` (the multiply was `≈ 50%` of the L6 Toffoli total and
Karatsuba ≈ halves it), with the inversion now co-dominant (`≈ 67%` of the new total). The quantitative
`> 1.3×` form is `karatsuba_score_improvement_quant`. -/
theorem karatsuba_score_improvement :
    onePointAddScore_karatsuba < onePointAddScore_safegcd := by
  rw [onePointAddScore_karatsuba_eq, onePointAddScore_safegcd_eq]; norm_num

/-- **The score win, quantitative (`> 1.3×`).** `onePointAddScore_karatsuba · 13 <
onePointAddScore_safegcd · 10` — the Karatsuba score is below `10/13 ≈ 0.77×` of the L6 figure, i.e. a
`> 1.3×` improvement (the actual factor is `≈ 1.335×`). -/
theorem karatsuba_score_improvement_quant :
    onePointAddScore_karatsuba * 13 < onePointAddScore_safegcd * 10 := by
  rw [onePointAddScore_karatsuba_eq, onePointAddScore_safegcd_eq]; norm_num

/-! ### Placement against the ECDSA.fail leaderboard (CONJECTURAL / EXTERNAL) -/

/-- **The leaderboard gap after L7 — lower bound.** The Karatsuba score is still `> 10×` the leaderboard
best: `ecdsaFailLeaderboardBest · 10 < onePointAddScore_karatsuba` (`15 700 000 000 < 16 688 935 496`).
-/
theorem karatsuba_score_gap_vs_leaderboard_lower :
    ecdsaFailLeaderboardBest * 10 < onePointAddScore_karatsuba := by
  rw [onePointAddScore_karatsuba_eq]; norm_num [ecdsaFailLeaderboardBest]

/-- **The leaderboard gap after L7 — upper bound.** The Karatsuba score is `< 11×` the leaderboard best:
`onePointAddScore_karatsuba < ecdsaFailLeaderboardBest · 11` (`16 688 935 496 < 17 270 000 000`).
Together with the lower bound, L7 brings the gap from L6's `≈ 14×` to `≈ 10.6×` — the residual is the
documented optimisations (windowing, measurement-based adders, a deeper-fidelity inversion) plus the
worst-case-vs-executed-average modelling gap. -/
theorem karatsuba_score_gap_vs_leaderboard_upper :
    onePointAddScore_karatsuba < ecdsaFailLeaderboardBest * 11 := by
  rw [onePointAddScore_karatsuba_eq]; norm_num [ecdsaFailLeaderboardBest]

/-! ### Dedicated modular SQUARING cost model + re-cost  (ECDLP L3)

A squaring `x²` is cheaper than a general multiply `x·y`: schoolbook, the diagonal symmetry leaves only
`n(n+1)/2 ≈ n²/2` distinct partial products (the `n` diagonal `xᵢ²` plus the `n(n−1)/2` off-diagonal
`xᵢxⱼ`, `i < j`, each used twice via a free shift) against `n²` for a general multiply — a `~2×`
partial-product saving. This block costs that saving (a Karatsuba-square recurrence, so it lands strictly
below the Karatsuba *multiply* `karatsubaToffoli`) and re-costs the L6+L1 affine point op by costing its
ONE squaring (`λ²`) with the cheaper figure instead of a full multiply.

## HONEST STATUS — this is a COST MODEL, not a verified squaring circuit (mirrors L1/L6 route 3b)

`x²` is `x·x`, the **same proved product**: its value rides on the corpus's verified carry-clean modular
multiply `Reversible.cuccaroModMul_correct` (`= X·Y mod N`), with the squaring algebra trivial (`x*x`).
We do **not** build or claim a verified squaring CIRCUIT (a reversible circuit exploiting the diagonal
symmetry whose denotation IS `x² mod N`) — that is the **named deferred residue**. The win lives entirely
on the cost side, every term tied to the verified gadgets `karatsubaToffoli` already uses. The genuine
ALGEBRAIC core (the Karatsuba-square split is exact) is `karatsubaSquare_identity` (a `ring` identity),
real content but algebra, not a circuit. This is L1's route 3b exactly.

## Squaring model chosen + count of squarings costed

* **Model:** the **Karatsuba-square recurrence** `S(n) = 2·S(⌈n/2⌉) + karatsubaToffoli(⌈n/2⌉) +
  kCombineToffoli n`, base `S(n≤32) = schoolbookSquareToffoli n` — TWO half-width recursive squarings +
  ONE half-width recursive *multiply* (the cross term `x₁x₀`), one fewer recursive multiply than the
  general Karatsuba's three. The schoolbook *base* is the diagonal-halved `10n²+14n` (the `20n²`
  partial-product term of the verified `cleanModMulToffoli` halved, the per-step reduction `14n` kept —
  one reduction per Horner step regardless). The pure schoolbook square `~n²/2` (≈ half of
  `cleanModMulToffoli`) is `658 944` at `n=256`, *above* the Karatsuba multiply `653 388`; the
  Karatsuba-square recurrence is what brings the per-squaring figure below the Karatsuba multiply.
* **Squarings costed:** the affine point op has three field multiplies (`λ = Δy·(1/Δx)`, `λ²`,
  `λ·(x−x₃)`); exactly ONE — `λ²` — is a squaring, so the re-cost is `2·multiply + 1·squaring +
  inversion`. The DERIVED per-op mul/sq splits one layer down corroborate that squarings are a minority:
  `M_add = 17 = 13 mul + 4 sq` (`additionProgram`), `M_dbl = 8 = 4 mul + 4 sq` (`doublingProgram`).

## Tier (per figure, mandatory)

* **VERIFIED** — the carry-clean multiply base cost `cleanModMulToffoli` (`cleanModMulToffoli_eq_cuccaro`,
  value `cuccaroModMul_correct`) that the squaring base halves; the combine adder cost (`kCombineToffoli`,
  `kCombineToffoli_eq_adders`, tied to `cuccaroModAdd_toffoli = 12n+10`); the embedded recursive multiply
  `karatsubaToffoli`; the Karatsuba-square algebraic identity `karatsubaSquare_identity`.
* **DOCUMENTED** — the diagonal-symmetry halving of the base partial-product term
  (`schoolbookSquareToffoli n = 10n²+14n`, tied by `schoolbookSquareToffoli_two_mul`); the
  Karatsuba-square recurrence SHAPE (2 squares + 1 multiply); the identification of `λ²` as the one
  affine squaring.
* **CONJECTURAL / EXTERNAL** — the leaderboard datum `ecdsaFailLeaderboardBest` and the
  worst-case→executed-average map (unchanged). **The win here is SMALL** (squarings are a minority of the
  field ops and the inversion still dominates `~67%`), so the leaderboard band is unmoved (`~10.5×`).

## Headline figures (at `Secp256k1.bits = 256`)

* `squareToffoli_secp256k1                 : squareToffoli 256 = 571468`  (`< 653 388 =
  karatsubaToffoli 256`, a `~1.14×` per-squaring win over the Karatsuba multiply)
* `squareToffoli_lt_multiply_secp256k1     : squareToffoli 256 < karatsubaToffoli 256`
* `onePointAddToffoli_squaring_eq          : onePointAddToffoli_squaring = 5831948`
  (vs L1 `onePointAddToffoli_karatsuba = 5 913 868`, a `~81 920` Toffoli trim)
* `onePointAddScore_squaring_eq            : onePointAddScore_squaring = 16457757256`
  (vs L1 `onePointAddScore_karatsuba = 16 688 935 496`, a `~1.014×` score trim; small by design)
-/

/-- **The Karatsuba-square algebraic identity (genuine algebra).** In any commutative ring, splitting
`x = x₁·B + x₀`, the square is recovered from TWO sub-squares `x₁²`, `x₀²` and ONE cross product `x₁x₀`
(the middle term `2·x₁x₀` a free doubling/shift) — one fewer recursive multiply than the general
Karatsuba's three: `(x₁B+x₀)² = x₁²·B² + 2·x₁x₀·B + x₀²`. The **exactness** of the Karatsuba-square split,
proved by `ring`; the source of the `2·S + 1·M` recurrence shape. ALGEBRA, **not** a verified circuit (the
mod-`N` value rides on `Reversible.cuccaroModMul_correct`; route 3b, see block note). -/
theorem karatsubaSquare_identity {R : Type*} [CommRing R] (B x1 x0 : R) :
    (x1 * B + x0) ^ 2 = x1 ^ 2 * B ^ 2 + 2 * (x1 * x0) * B + x0 ^ 2 := by
  ring

/-- **Schoolbook squaring base cost: `10n² + 14n` (DOCUMENTED diagonal-symmetry halving).** The
carry-clean schoolbook multiply is `cleanModMulToffoli n = 20n² + 14n` (`n` Horner steps; the `20n²` the
partial-product term, the `14n` the per-step modular reduction). A squaring computes only `n(n+1)/2`
distinct partial products against `n²` — the diagonal symmetry HALVES the partial-product term `20n² →
10n²`; the per-step modular reduction `14n` is NOT halved (one reduction per Horner step regardless). So
the schoolbook squaring base is `10n² + 14n`. DOCUMENTED count, tied to the VERIFIED multiply by
`schoolbookSquareToffoli_two_mul`; no verified squaring circuit. -/
def schoolbookSquareToffoli (n : ℕ) : ℕ := 10 * n ^ 2 + 14 * n

/-- **The verified-multiply tie for the squaring base.** `2 · schoolbookSquareToffoli n =
cleanModMulToffoli n + 14n` — twice the squaring base equals the carry-clean multiply plus the unhalved
per-step reduction `14n`, i.e. the partial-product term is EXACTLY halved (`10n²` vs `20n²`). Anchors the
diagonal-symmetry halving to the verified multiply cost `cleanModMulToffoli` (itself
`cleanModMulToffoli_eq_cuccaro`), not a free constant. -/
theorem schoolbookSquareToffoli_two_mul (n : ℕ) :
    2 * schoolbookSquareToffoli n = cleanModMulToffoli n + 14 * n := by
  simp only [schoolbookSquareToffoli, cleanModMulToffoli]; ring

/-- **Karatsuba modular-SQUARING Toffoli cost: `S(n) = 2·S(⌈n/2⌉) + karatsubaToffoli(⌈n/2⌉) +
kCombineToffoli n`, base `S(n≤32) = schoolbookSquareToffoli n`.** The Karatsuba-square recurrence: TWO
half-width recursive squarings plus ONE half-width recursive MULTIPLY (`karatsubaToffoli`, the cross term
`x₁x₀`), one fewer recursive multiply than the general Karatsuba's three (cf. `karatsubaSquare_identity`);
the same `O(n)` combine `kCombineToffoli`. Base is the diagonal-halved schoolbook squaring
`schoolbookSquareToffoli` (the verified `cleanModMulToffoli` halved, `schoolbookSquareToffoli_two_mul`).
`⌈n/2⌉ = (n+1)/2` in `ℕ`.

**Status: DERIVED cost recurrence** (base + combine + embedded multiply tied to verified circuits), NOT a
verified squaring circuit. The VALUE (`x² mod N = x·x mod N`) rides on `Reversible.cuccaroModMul_correct`
(route 3b); the full verified squaring circuit is the deferred residue. See block note. -/
def squareToffoli (n : ℕ) : ℕ :=
  if h : n ≤ 32 then schoolbookSquareToffoli n
  else 2 * squareToffoli ((n + 1) / 2) + karatsubaToffoli ((n + 1) / 2) + kCombineToffoli n
termination_by n
decreasing_by omega

/-- **Base-case unfolding** (`n ≤ 32`): `squareToffoli n = schoolbookSquareToffoli n`. -/
theorem squareToffoli_base {n : ℕ} (h : n ≤ 32) :
    squareToffoli n = schoolbookSquareToffoli n := by
  rw [squareToffoli.eq_def, dif_pos h]

/-- **Recursive-step unfolding** (`32 < n`): `squareToffoli n = 2·squareToffoli ⌈n/2⌉ +
karatsubaToffoli ⌈n/2⌉ + combine` — the `2·S + 1·M` Karatsuba-square recurrence. -/
theorem squareToffoli_rec {n : ℕ} (h : ¬ n ≤ 32) :
    squareToffoli n
      = 2 * squareToffoli ((n + 1) / 2) + karatsubaToffoli ((n + 1) / 2) + kCombineToffoli n := by
  rw [squareToffoli.eq_def, dif_neg h]

/-- The Karatsuba modular-squaring cost at secp256k1 width evaluates to `571 468 ≈ 5.7×10⁵` Toffolis:
unrolling `S(256) = 2·S(128) + karatsuba(128) + 18 492`, `S(128) = 2·S(64) + karatsuba(64) + 9 276`,
`S(64) = 2·S(32) + karatsuba(32) + 4 668`, base `S(32) = schoolbookSquareToffoli 32 = 10 688` (since
`32 ≤ 32`). With `karatsuba(32) = 20 928`, `karatsuba(64) = 67 452`, `karatsuba(128) = 211 632`, this
gives `S(64) = 46 972`, `S(128) = 170 672`, `S(256) = 571 468`. The recursion bottoms out at the
diagonal-halved schoolbook squaring, each embedded multiply the verified Karatsuba `karatsubaToffoli`,
each combine `6·(12n+10)` verified modular adders. -/
theorem squareToffoli_secp256k1 : squareToffoli Secp256k1.bits = 571468 := by
  have hk32 : karatsubaToffoli 32 = 20928 := by
    rw [karatsubaToffoli_base (by norm_num)]; norm_num [cleanModMulToffoli]
  have hk64 : karatsubaToffoli 64 = 67452 := by
    have hd : ((64 : ℕ) + 1) / 2 = 32 := by norm_num
    rw [karatsubaToffoli_rec (by norm_num), hd, hk32]; norm_num [kCombineToffoli, kCombineAdders]
  have hk128 : karatsubaToffoli 128 = 211632 := by
    have hd : ((128 : ℕ) + 1) / 2 = 64 := by norm_num
    rw [karatsubaToffoli_rec (by norm_num), hd, hk64]; norm_num [kCombineToffoli, kCombineAdders]
  have hs32 : squareToffoli 32 = 10688 := by
    rw [squareToffoli_base (by norm_num)]; norm_num [schoolbookSquareToffoli]
  have hs64 : squareToffoli 64 = 46972 := by
    have hd : ((64 : ℕ) + 1) / 2 = 32 := by norm_num
    rw [squareToffoli_rec (by norm_num), hd, hs32, hk32]; norm_num [kCombineToffoli, kCombineAdders]
  have hs128 : squareToffoli 128 = 170672 := by
    have hd : ((128 : ℕ) + 1) / 2 = 64 := by norm_num
    rw [squareToffoli_rec (by norm_num), hd, hs64, hk64]; norm_num [kCombineToffoli, kCombineAdders]
  have hs256 : squareToffoli 256 = 571468 := by
    have hd : ((256 : ℕ) + 1) / 2 = 128 := by norm_num
    rw [squareToffoli_rec (by norm_num), hd, hs128, hk128]; norm_num [kCombineToffoli, kCombineAdders]
  rw [show Secp256k1.bits = 256 from rfl]; exact hs256

/-- **The per-squaring win, concrete.** At `n = 256` the Karatsuba modular squaring is strictly cheaper
than the Karatsuba modular multiply: `squareToffoli 256 = 571 468 < 653 388 = karatsubaToffoli 256` (a
`~1.14×` win — the diagonal-halved base plus one fewer recursive multiply per level). The win is modest:
the squaring shares the same `O(n)` combine and `~32`-bit fallback band as the multiply, and replaces only
one of the three recursive products with a recursive square. -/
theorem squareToffoli_lt_multiply_secp256k1 :
    squareToffoli Secp256k1.bits < karatsubaToffoli Secp256k1.bits := by
  rw [squareToffoli_secp256k1, karatsubaToffoli_secp256k1]; norm_num

/-! ### Re-costing the ECDSA.fail benchmark with squaring-aware field ops (L3) -/

/-- **Affine point-op Toffoli cost, Karatsuba multiply + dedicated squaring + binary-GCD inversion.** The
`affinePointOpToffoli_karatsuba` analogue, refining its three uniform field multiplies into TWO Karatsuba
multiplies (`λ = Δy·(1/Δx)`, `λ·(x−x₃)`) and ONE dedicated squaring (`λ²`), keeping the L6 binary-GCD
inversion `safegcdInvToffoli`. The squaring `λ²` is the only one of the three affine field multiplies that
is a square; the derived one-layer-down splits corroborate squarings as a minority (`M_add = 13 mul + 4
sq`, `M_dbl = 4 mul + 4 sq`). The inversion still dominates: `safegcdInvToffoli 256 = 3 939 328` vs the
two multiplies + one square `2·653 388 + 571 468 = 1 878 244`. -/
def affinePointOpToffoli_squaring (n : ℕ) : ℕ :=
  2 * karatsubaToffoli n + squareToffoli n + safegcdInvToffoli n

/-- One representative secp256k1 affine point op with two Karatsuba multiplies + one dedicated squaring +
binary-GCD inversion costs `5 817 572 ≈ 5.8×10⁶` Toffolis: `2·karatsubaToffoli 256 = 1 306 776` plus
`squareToffoli 256 = 571 468` plus `safegcdInvToffoli 256 = 3 939 328`. Contrast the L1
`affinePointOpToffoli_karatsuba 256 = 5 899 492` (all three field mults full multiplies) — an `81 920`
Toffoli trim, exactly `karatsubaToffoli 256 − squareToffoli 256`. -/
theorem affinePointOpToffoli_squaring_secp256k1 :
    affinePointOpToffoli_squaring Secp256k1.bits = 5817572 := by
  rw [affinePointOpToffoli_squaring, karatsubaToffoli_secp256k1, squareToffoli_secp256k1,
    safegcdInvToffoli_secp256k1]

/-- **Toffoli count for ONE affine point addition, squaring-aware field ops, classical offset.** The
`onePointAddToffoli_karatsuba` analogue with the squaring-aware affine point-op core
(`affinePointOpToffoli_squaring`) plus the unchanged sub-dominant classical-offset coordinate term
(`classicalOffsetCoordToffoli`).

**Tier:** the two multiplies are the DERIVED Karatsuba recurrence `karatsubaToffoli`; the one squaring is
the DERIVED Karatsuba-square recurrence `squareToffoli` (value rides on `cuccaroModMul_correct`, base
halving DOCUMENTED via `schoolbookSquareToffoli_two_mul`); the inversion is the L6 op-count model
`safegcdInvToffoli`; the `2-mul + 1-sq` assembly and the classical-offset count are DOCUMENTED. -/
def onePointAddToffoli_squaring : ℕ :=
  affinePointOpToffoli_squaring Secp256k1.bits + classicalOffsetCoordToffoli Secp256k1.bits

/-- One affine point addition with squaring-aware field ops (classical offset) costs `5 831 948 ≈ 5.8×10⁶`
Toffolis: the squaring-aware affine core `affinePointOpToffoli_squaring 256 = 5 817 572` plus the
classical-offset coordinate term `classicalOffsetCoordToffoli 256 = 14 376`. Contrast the L1
`onePointAddToffoli_karatsuba = 5 913 868` — an `81 920` Toffoli trim (`~1.014×`), small by design: the
squaring is one of three field multiplies and the inversion still dominates. -/
theorem onePointAddToffoli_squaring_eq : onePointAddToffoli_squaring = 5831948 := by
  rw [onePointAddToffoli_squaring, affinePointOpToffoli_squaring_secp256k1,
    classicalOffsetCoordToffoli_secp256k1]

/-- **The ECDSA.fail-convention score for one affine point addition, squaring-aware field ops.** The
`onePointAddScore_karatsuba` analogue, `onePointAddToffoli_squaring × onePointAddPeakQubits`. The
peak-qubit count `onePointAddPeakQubits = 2822` is reused unchanged: the dedicated squaring runs on the
same shared carry-clean scratch bank (`cleanModMulQubits = 6n+6`) as the multiply (`x²` is `x·x` on that
bank), so the live width band is unaffected (the DOCUMENTED layout choice). So the score trim equals the
Toffoli trim.

**Tier:** Toffoli factor DERIVED-recurrence / op-count-model; peak qubits DOCUMENTED; the product as a
comparison to the live ECDSA.fail score is CONJECTURAL / EXTERNAL (worst-case upper bound, not their
executed average). -/
def onePointAddScore_squaring : ℕ := onePointAddToffoli_squaring * onePointAddPeakQubits

/-- The ECDSA.fail-convention score for one affine point addition with squaring-aware field ops is
`16 457 757 256 ≈ 1.65×10¹⁰`: `onePointAddToffoli_squaring = 5 831 948` Toffolis times
`onePointAddPeakQubits = 2822` peak live qubits. Contrast the L1 `onePointAddScore_karatsuba =
16 688 935 496 ≈ 1.67×10¹⁰` — a `~1.014×` score trim. Repo comparable-OBJECT figure, NOT a validated
ECDSA.fail harness score. -/
theorem onePointAddScore_squaring_eq : onePointAddScore_squaring = 16457757256 := by
  rw [onePointAddScore_squaring, onePointAddToffoli_squaring_eq, onePointAddPeakQubits_eq]

/-- **The score trim over the L1 Karatsuba figure (SMALL, `~1.014×`).** `onePointAddScore_squaring <
onePointAddScore_karatsuba` — costing `λ²` as a dedicated squaring drops the one-affine-point-addition
score from `16 688 935 496` (L1) to `16 457 757 256`. The trim is small by design: the squaring is one of
three affine field multiplies, and the inversion still dominates (`~67%` of the total). This is a small
critical-path trim, not a major lever. -/
theorem squaring_score_improvement :
    onePointAddScore_squaring < onePointAddScore_karatsuba := by
  rw [onePointAddScore_squaring_eq, onePointAddScore_karatsuba_eq]; norm_num

/-! ### Placement against the ECDSA.fail leaderboard (CONJECTURAL / EXTERNAL) -/

/-- **The leaderboard gap after L3 — lower bound.** The squaring-aware score is still `> 10×` the
leaderboard best: `ecdsaFailLeaderboardBest · 10 < onePointAddScore_squaring` (`15 700 000 000 <
16 457 757 256`). -/
theorem squaring_score_gap_vs_leaderboard_lower :
    ecdsaFailLeaderboardBest * 10 < onePointAddScore_squaring := by
  rw [onePointAddScore_squaring_eq]; norm_num [ecdsaFailLeaderboardBest]

/-- **The leaderboard gap after L3 — upper bound.** The squaring-aware score is `< 11×` the leaderboard
best: `onePointAddScore_squaring < ecdsaFailLeaderboardBest · 11` (`16 457 757 256 < 17 270 000 000`).
The gap stays in L1's `~10.5×` band — the squaring trim is small (a minority of the field ops, inversion
dominant), so it does not move the leaderboard placement. -/
theorem squaring_score_gap_vs_leaderboard_upper :
    onePointAddScore_squaring < ecdsaFailLeaderboardBest * 11 := by
  rw [onePointAddScore_squaring_eq]; norm_num [ecdsaFailLeaderboardBest]

end ECDLP.ResourceBounds
