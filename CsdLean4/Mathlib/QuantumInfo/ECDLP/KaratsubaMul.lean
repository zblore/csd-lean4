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

end ECDLP.ResourceBounds
