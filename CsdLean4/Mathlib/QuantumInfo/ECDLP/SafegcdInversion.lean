import CsdLean4.Mathlib.QuantumInfo.ECDLP.PointAddBenchmark
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
import Mathlib.Data.Int.GCD

/-!
# Binary-GCD / Kaliski modular inversion — value-correct, `O(n²)` cost  (ECDLP L6)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The benchmark figures (`PointAddBenchmark.lean`) are dominated by **modular inversion**: the
slope `λ = 1/(offset_x − x)` of an isolated affine point addition is one field division, and the
corpus costed it via **Fermat** (`Inversion.lean`, `fermatInv p a = a^{p-2}`), an `O(n³)`
exponentiation (`fermatInvToffoli n = 2n·cleanModMulToffoli n`). The inversion is `~99.4%` of one
affine point addition's Toffoli cost, so it is the single highest-impact lever on the ECDSA.fail
point-add score.

This file builds the structural win: a **binary-GCD / Kaliski / Bernstein–Yang (safegcd)** modular
inversion, whose **divstep** structure costs `O(n²)` — an `~n`-fold asymptotic improvement over
Fermat. The two sides have DIFFERENT honesty status, stated plainly:

* **value side (honest about being an unfolding)** — `binGcdInv N a` is **definitionally** Mathlib's
  `ZMod.inv N a` (both are `↑(a.val.gcdA N)` at `NeZero N`; see `ZMod.inv`). So
  `binGcdInv_eq_inv : binGcdInv N a = a⁻¹` is an **unfolding to the `⁻¹` notation**, NOT an
  independent algorithm-correctness proof, and it carries NO hypothesis. The genuine,
  coprimality-load-bearing value content is
  `binGcdInv_mul_eq_one : Nat.Coprime a.val N → a * binGcdInv N a = 1` (the Bézout identity reduced
  mod `N`; without coprimality `a` has no inverse and the product is `gcd a.val N ≠ 1`). This is
  **weaker than `fermatInv`'s status**: `fermatInv = a^{p-2}` is a genuinely *distinct* term from
  `a⁻¹` whose equality needs load-bearing primality, whereas `binGcdInv` IS `a⁻¹` by definition.
* **cost side (sound DERIVED op-count model)** — `safegcdInvToffoli n = (2n)·(per-divstep gadget
  cost)`, the per-divstep cost tied to the corpus's VERIFIED `O(n)` modular gadgets
  (`divstepToffoli_eq_gadgets`: one `modSub` + one `cuccaroCModAdd` + one `cuccaroModDouble`), not an
  asserted constant. Same status as `fermatInvToffoli`'s op-count model (`modExpFieldMults`).

**Value-side promotion (2026-07-04, `SafegcdDivstep.lean`).** The divstep transition is no longer
only a `ZMod.inv` unfolding: `ECDLP.Safegcd.divstep` exhibits the Bernstein-Yang divstep as a concrete
`ℤ³ → ℤ³` function, and `ECDLP.Safegcd.divstep_gcd` proves the GCD INVARIANT `Int.gcd f' g' =
Int.gcd f g` as a genuine theorem (parity + coprimality-with-2, not a `Nat.gcd`/`ZMod.inv` unfolding).
`divstepIter_gcd` iterates it; `divstepIter_natAbs_of_g_zero` gives correctness modulo termination
(when the running `g` hits `0`, the running `|f|` equals `gcd(f₀,g₀)`); `divstepIter_bezout` tracks the
cofactor up to the `2^k` scale. So the divstep recurrence now GENUINELY computes the gcd. The two
NAMED RESIDUALS that keep the full inversion trusted-not-verified: (i) TERMINATION (the `g → 0` within
`2·bits` bound, the potential-function argument), and (ii) the reversible BIT-CIRCUIT whose denotation
equals `divstep` (the `divstepToffoli` op-count model below is over this not-yet-exhibited circuit).

## Route taken for value-correctness (stated honestly)

**Route 2b** of the plan: the value-bearing algorithm is Mathlib's verified **xgcd** (`Nat.gcdA`,
which `ZMod.inv` is built on), while the cost-modelled algorithm is the **binary-GCD divsteps** — a
different schedule for the same extended GCD. Because the modular inverse is **unique**, both correct
inversions have the same value (`= a⁻¹`), so the cost model is allowed to reflect the binary-GCD
divstep structure (conditional swap + subtraction + halving, all `O(n)`) while the value rides on
`ZMod.inv`. The `O(n²)`-vs-`O(n³)` win lives entirely on the cost side. **The full per-divstep
bit-circuit whose denotation IS the inverse** (the gold-standard route 2a: a divstep recurrence with
a proved GCD/Bézout invariant + termination, exhibited as a reversible circuit) is the **deferred
residue** that would make the value genuinely circuit-backed; it is NOT built here — exactly as
`fermatInv` does not exhibit an `a^{p-2}` exponentiation circuit.

## What is proved / what is modelled (tier)

* **VERIFIED**: `binGcdInv_mul_eq_one` (the coprimality-load-bearing value content; `binGcdInv_eq_inv`
  is a definitional unfolding, not independent value content); the per-divstep gadget costs
  `modSub_toffoli = 10n`, `cuccaroCModAdd_toffoli = 14n+10`, `cuccaroModDouble_toffoli = 6n+4` (cited
  via `divstepToffoli_eq_gadgets`).
* **DOCUMENTED** (op-count model, same status as `fermatInv`'s `2n`): the divstep **count**
  `safegcdDivsteps n = 2n` (the standard binary-GCD / Kaliski / Bernstein–Yang worst-case iteration
  bound for `n`-bit inputs), and the `divstep = modSub + cModAdd + modDouble` assembly.
* **CONJECTURAL / EXTERNAL**: the leaderboard reference `ecdsaFailLeaderboardBest` and the mapping of
  our worst-case UPPER-bound Toffoli count to the executed-average harness.

## Headline figures (at `Secp256k1.bits = 256`)

* `safegcdInvToffoli_secp256k1            : safegcdInvToffoli 256 = 3939328`  (`≈ 3.9×10⁶`, vs Fermat
  `fermatInvToffoli 256 = 672923648 ≈ 6.7×10⁸`, a `~170×` per-inversion win)
* `onePointAddToffoli_safegcd_eq          : onePointAddToffoli_safegcd = 7896616`
* `onePointAddScore_safegcd_eq            : onePointAddScore_safegcd = 22284250352`
* `safegcd_score_improvement              : onePointAddScore_safegcd · 85 < onePointAddScore`
  (the `~86×` score win over the Fermat benchmark `onePointAddScore = 1910158001392`)
-/

namespace ECDLP

/-! ### Binary-GCD / Kaliski inversion: value-correctness via the Bézout coefficient -/

/-- **Binary-GCD / Kaliski modular inverse** (`binGcdInv N a`), defined via the extended-Euclid
**Bézout coefficient** `Nat.gcdA a.val N` cast into `ZMod N`. At `NeZero N` this is **definitionally**
Mathlib's `ZMod.inv N a` (`= a⁻¹`), so `binGcdInv_eq_inv` below is an unfolding; the genuine value
content is `binGcdInv_mul_eq_one`. The binary-GCD / safegcd divstep recurrence computes the same
Bézout coefficient (a different schedule for the same extended GCD), so it has the same value; the
`O(n²)` divstep COST model is `safegcdInvToffoli`. Route 2b: Mathlib's verified extended-Euclid for
the value, the binary-GCD divstep structure for the cost (see module note). -/
def binGcdInv (N : ℕ) (a : ZMod N) : ZMod N := (Nat.gcdA a.val N : ZMod N)

/-- **The genuine value content: `a * binGcdInv N a = 1` for `a` coprime to `N`.** Here the
coprimality hypothesis is **load-bearing**: the Bézout identity `1 = a.val·gcdA + N·gcdB`
(`Nat.gcd_eq_gcd_ab`, with `gcd a.val N = 1` from coprimality) reduces mod `N` (with `↑N = 0`,
`↑a.val = a`) to `a · binGcdInv N a = 1`. Without coprimality the product is `gcd a.val N ≠ 1` and
`a` has no inverse, so the statement genuinely fails — this is the honest analogue of Fermat's
content (cf. `binGcdInv_eq_inv`, which is a mere definitional unfolding). -/
theorem binGcdInv_mul_eq_one {N : ℕ} [NeZero N] {a : ZMod N} (hcop : Nat.Coprime a.val N) :
    a * binGcdInv N a = 1 := by
  have hg1 : Nat.gcd a.val N = 1 := hcop
  have hbez : ((Nat.gcd a.val N : ℕ) : ℤ)
      = (a.val : ℤ) * Nat.gcdA a.val N + (N : ℤ) * Nat.gcdB a.val N := Nat.gcd_eq_gcd_ab a.val N
  have hcast : ((Nat.gcd a.val N : ℤ) : ZMod N)
      = (((a.val : ℤ) * Nat.gcdA a.val N + (N : ℤ) * Nat.gcdB a.val N : ℤ) : ZMod N) := by
    rw [hbez]
  push_cast at hcast
  rw [hg1, Nat.cast_one, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_rightInverse a] at hcast
  -- hcast : (1 : ZMod N) = a * ↑(Nat.gcdA a.val N)
  show a * (Nat.gcdA a.val N : ZMod N) = 1
  exact hcast.symm

/-- **`binGcdInv N a = a⁻¹` — a definitional UNFOLDING, not independent algorithm-correctness.** At
`NeZero N` (`N = n+1`), `ZMod.inv (n+1) a := Nat.gcdA a.val (n+1)`, which is exactly `binGcdInv N a`;
so the equality holds by `rfl` after destructuring `N`, with NO coprimality hypothesis (it is not
load-bearing here). The coprimality-load-bearing value statement is `binGcdInv_mul_eq_one`. -/
theorem binGcdInv_eq_inv {N : ℕ} [NeZero N] (a : ZMod N) : binGcdInv N a = a⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rfl

/-- **Tie to the `Reversible.modInv` algebra.** `binGcdInv N a = modInv N a` (`= a⁻¹`) — both unfold to
the `⁻¹` notation (`Reversible.modInv N a := a⁻¹`), so this is again a definitional unfolding with no
load-bearing hypothesis. The reversibility layer (`ModInv.lean`) consumes the same oracle action. -/
theorem binGcdInv_eq_modInv {N : ℕ} [NeZero N] (a : ZMod N) :
    binGcdInv N a = Reversible.modInv N a := by
  rw [binGcdInv_eq_inv, Reversible.modInv]

end ECDLP

namespace ECDLP.ResourceBounds

open ECDLP Reversible

/-! ### The per-divstep cost, tied to the verified `O(n)` modular gadgets

A binary-GCD / safegcd **divstep** on the running `(f, g, u, v)` state does, per iteration: a
conditional **swap** (when `g` is "ahead"), a **subtraction** `g ← g − f` (or `f ← f − g`), and a
**halving / shift** of the trailing register, with the Bézout coefficients `(u, v)` tracked by a
**conditional modular add**. We cost one divstep by the corpus's VERIFIED `O(n)` modular gadgets it
reuses:

* the subtraction = `Reversible.modSub` (`modSub_toffoli = 10n`);
* the conditional Bézout-coefficient update = `Reversible.cuccaroCModAdd` (`cuccaroCModAdd_toffoli =
  14n + 10`);
* the halving / shift = `Reversible.cuccaroModDouble` (`cuccaroModDouble_toffoli = 6n + 4`,
  the double/halve gadget on the shared scratch bank).

So one divstep is `10n + (14n+10) + (6n+4) = 30n + 14` Toffolis, a **derived** count (each summand a
proved gadget cost), not an asserted `O(n)` constant. -/

/-- **Per-divstep Toffoli cost: `30n + 14`** — one `modSub` (`10n`) + one `cuccaroCModAdd` (`14n+10`)
+ one `cuccaroModDouble` (`6n+4`). A derived figure (sum of verified gadget costs), tied to the
circuits by `divstepToffoli_eq_gadgets`.

**Fidelity caveat (DOCUMENTED op-count model, not a faithful per-gate divstep count).** This is a
LOWER-FIDELITY proxy that, if anything, *undercounts*: a real safegcd divstep tracks TWO Bézout
coefficients `(u, v)` (two conditional adds), so the single `cuccaroCModAdd` here models the
coefficient track with the second coefficient's update folded/omitted; and `cuccaroModDouble` (a
DOUBLING gadget) stands in for the divstep's HALVING/shift (same `O(n)` class, opposite direction).
So the constant `30n+14` is the documented op-count-model tier, not a verified per-gate divstep cost;
the undercount means the reported win is, if anything, optimistic on the safegcd side. -/
def divstepToffoli (n : ℕ) : ℕ := (10 * n) + (14 * n + 10) + (6 * n + 4)

theorem divstepToffoli_eq (n : ℕ) : divstepToffoli n = 30 * n + 14 := by
  simp only [divstepToffoli]; ring

/-- **The verified-gadget link.** `divstepToffoli n` is exactly the sum of the three proved gadget
Toffoli costs (`modSub_toffoli`, `cuccaroCModAdd_toffoli`, `cuccaroModDouble_toffoli`), for any
concrete `n`-bit layouts. Makes the per-divstep cost a theorem about the corpus's verified circuits,
not a free-floating constant — the same discipline as `cleanModMulToffoli_eq_cuccaro`. -/
theorem divstepToffoli_eq_gadgets {m n : ℕ} (Ls : ModSubLayout m n)
    (Lc : CuccaroCModLayout m n) (Ld : CuccaroModLayout m n) :
    divstepToffoli n
      = (circuitCost (modSub Ls)).toffoli
        + (circuitCost (cuccaroCModAdd Lc)).toffoli
        + (circuitCost (cuccaroModDouble Ld)).toffoli := by
  unfold divstepToffoli
  rw [modSub_toffoli, cuccaroCModAdd_toffoli, cuccaroModDouble_toffoli]

/-! ### The divstep count and the `O(n²)` inversion cost -/

/-- **Divstep count, `2n` (DOCUMENTED model).** The binary-GCD / Kaliski almost-inverse / Bernstein–Yang
safegcd loop runs at most `~2n` divsteps for `n`-bit inputs (each divstep removes at least one bit from
the combined `(f, g)` length, total `2n`). This is the op-count model — the analogue of `fermatInv`'s
`modExpFieldMults_le ≤ 2·Nat.size e`; a *proved* `2n` bound would need the divstep recurrence + its
termination (route 2a, the named residue). -/
def safegcdDivsteps (n : ℕ) : ℕ := 2 * n

/-- **Binary-GCD inversion Toffoli cost: `(2n)·(30n+14) = 60n² + 28n` (`O(n²)`).** The DOCUMENTED
divstep count (`safegcdDivsteps = 2n`) times the verified-gadget-anchored per-divstep cost
(`divstepToffoli = 30n+14`). This is the `~n`-fold structural win over the `O(n³)` Fermat
`fermatInvToffoli n = 2n·cleanModMulToffoli n`. Same honesty status as `fermatInvToffoli`: a derived
op-count model (`divstep count × verified-per-divstep`), not a separately-exhibited inversion circuit;
the VALUE is the proved `binGcdInv_eq_inv`. -/
def safegcdInvToffoli (n : ℕ) : ℕ := safegcdDivsteps n * divstepToffoli n

theorem safegcdInvToffoli_eq (n : ℕ) : safegcdInvToffoli n = 60 * n ^ 2 + 28 * n := by
  simp only [safegcdInvToffoli, safegcdDivsteps, divstepToffoli]; ring

/-- One secp256k1 binary-GCD inversion costs `3 939 328 ≈ 3.9×10⁶` Toffolis: `2·256 = 512` divsteps,
each `30·256 + 14 = 7694` Toffolis (`= 60·256² + 28·256`). Contrast the Fermat
`fermatInvToffoli 256 = 672 923 648 ≈ 6.7×10⁸` — a `~170×` per-inversion win (`O(n²)` vs `O(n³)`). -/
theorem safegcdInvToffoli_secp256k1 : safegcdInvToffoli Secp256k1.bits = 3939328 := by
  rw [safegcdInvToffoli_eq]; norm_num [Secp256k1.bits]

/-- **The per-inversion win, concrete.** At `n = 256`, the binary-GCD inversion is strictly cheaper
than Fermat: `safegcdInvToffoli 256 = 3 939 328 < 672 923 648 = fermatInvToffoli 256` (a `~170×`
factor — the `O(n²)`-vs-`O(n³)` structural improvement). -/
theorem safegcdInvToffoli_lt_fermat_secp256k1 :
    safegcdInvToffoli Secp256k1.bits < fermatInvToffoli Secp256k1.bits := by
  rw [safegcdInvToffoli_secp256k1, fermatInvToffoli_secp256k1]; norm_num

/-- **The per-inversion win, structural (`O(n²) ≤ O(n³)`).** For every register width `n ≥ 2`, the
binary-GCD inversion cost `60n² + 28n` is at most the Fermat cost `40n³ + 28n²`. This is the
`O(n²)`-vs-`O(n³)` separation as a theorem, not just at `n = 256`. -/
theorem safegcdInvToffoli_le_fermat (n : ℕ) (hn : 2 ≤ n) :
    safegcdInvToffoli n ≤ fermatInvToffoli n := by
  have hf : fermatInvToffoli n = 40 * n ^ 3 + 28 * n ^ 2 := by
    simp only [fermatInvToffoli, cleanModMulToffoli]; ring
  rw [safegcdInvToffoli_eq, hf]
  have key : 2 * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_right' hn (n ^ 2)
  nlinarith [key, hn]

/-! ### Re-costing the ECDSA.fail benchmark with the binary-GCD inversion (L6) -/

/-- **Affine point-op Toffoli cost, binary-GCD inversion.** The `affinePointOpToffoli` analogue with
`safegcdInvToffoli` in place of the Fermat `fermatInvToffoli`: three carry-clean field multiplies
(`λ = Δy·(1/Δx)`, `λ²`, `λ·(x−x₃)`) plus the now-`O(n²)` slope inversion. The inversion no longer
dominates: `safegcdInvToffoli 256 = 3 939 328` vs the three multiplies `3·1 314 304 = 3 942 912`
(roughly equal), against Fermat's `~170×` domination. -/
def affinePointOpToffoli_safegcd (n : ℕ) : ℕ := 3 * cleanModMulToffoli n + safegcdInvToffoli n

/-- One representative secp256k1 affine point op with binary-GCD inversion costs `7 882 240 ≈ 7.9×10⁶`
Toffolis: `3·cleanModMulToffoli 256 = 3 942 912` plus `safegcdInvToffoli 256 = 3 939 328`. Contrast
the Fermat `affinePointOpToffoli 256 = 676 866 560` (the inversion `~170×` the three multiplies). -/
theorem affinePointOpToffoli_safegcd_secp256k1 :
    affinePointOpToffoli_safegcd Secp256k1.bits = 7882240 := by
  rw [affinePointOpToffoli_safegcd, safegcdInvToffoli_secp256k1, cleanModMulToffoli_secp256k1]

/-- **Toffoli count for ONE affine point addition, binary-GCD inversion, classical offset.** The
`onePointAddToffoli` analogue: the binary-GCD affine point-op core
(`affinePointOpToffoli_safegcd Secp256k1.bits`) plus the sub-dominant classical-offset coordinate term
(`classicalOffsetCoordToffoli`). With the inversion dropped from `O(n³)` to `O(n²)`, the field
multiplies and the inversion are now comparable, not inversion-dominated.

**Tier:** the multiply core is VERIFIED-gadget-anchored (`cleanModMulToffoli`); the inversion is the
verified-gadget-anchored op-count model `safegcdInvToffoli` (value `binGcdInv_eq_inv` proved); the
`3`-mult assembly and `4`-subtraction classical-offset count are DOCUMENTED. -/
def onePointAddToffoli_safegcd : ℕ :=
  affinePointOpToffoli_safegcd Secp256k1.bits + classicalOffsetCoordToffoli Secp256k1.bits

/-- One affine point addition with binary-GCD inversion (classical offset) costs `7 896 616 ≈ 7.9×10⁶`
Toffolis: the binary-GCD affine core `affinePointOpToffoli_safegcd 256 = 7 882 240` plus the
classical-offset coordinate term `classicalOffsetCoordToffoli 256 = 14 376`. Contrast the Fermat
`onePointAddToffoli = 676 880 936` — an `~86×` per-addition Toffoli win. -/
theorem onePointAddToffoli_safegcd_eq : onePointAddToffoli_safegcd = 7896616 := by
  rw [onePointAddToffoli_safegcd, affinePointOpToffoli_safegcd_secp256k1,
    classicalOffsetCoordToffoli_secp256k1]

/-- **The ECDSA.fail-convention score for one affine point addition, binary-GCD inversion.** The
`onePointAddScore` analogue, `onePointAddToffoli_safegcd × onePointAddPeakQubits`. The peak-qubit count
`onePointAddPeakQubits = 2822` is reused: the binary-GCD divstep state `(f, g, u, v)` is `O(n)` (four
`n`-bit working registers vs Fermat's `Δx, Δy, accumulator` three) and runs on the same shared
carry-clean scratch bank `cleanModMulQubits = 6n+6` that dominates the tally, so the width stays in the
same `~11n` band; reusing `onePointAddPeakQubits` is the DOCUMENTED layout choice (the inversion is no
longer the qubit driver either). So the score win equals the Toffoli win (`~86×`).

**Tier:** Toffoli factor VERIFIED-gadget-anchored / op-count-model; peak qubits DOCUMENTED; the product
as a comparison to the live ECDSA.fail score is CONJECTURAL / EXTERNAL (worst-case upper bound, not
their executed average). -/
def onePointAddScore_safegcd : ℕ := onePointAddToffoli_safegcd * onePointAddPeakQubits

/-- The ECDSA.fail-convention score for one affine point addition with binary-GCD inversion is
`22 284 250 352 ≈ 2.2×10¹⁰`: `onePointAddToffoli_safegcd = 7 896 616` Toffolis times
`onePointAddPeakQubits = 2822` peak live qubits. Contrast the Fermat
`onePointAddScore = 1 910 158 001 392 ≈ 1.9×10¹²` — an `~86×` score win. Repo comparable-OBJECT figure,
NOT a validated ECDSA.fail harness score. -/
theorem onePointAddScore_safegcd_eq : onePointAddScore_safegcd = 22284250352 := by
  rw [onePointAddScore_safegcd, onePointAddToffoli_safegcd_eq, onePointAddPeakQubits_eq]

/-- **The score win over the Fermat benchmark: `> 85×`.** `onePointAddScore_safegcd · 85 <
onePointAddScore` — binary-GCD inversion drops the one-affine-point-addition score from
`1 910 158 001 392` to `22 284 250 352`, an `~86×` improvement (the inversion was `~99.4%` of the cost,
and `O(n²)` replaces `O(n³)`). -/
theorem safegcd_score_improvement :
    onePointAddScore_safegcd * 85 < onePointAddScore := by
  rw [onePointAddScore_safegcd_eq, onePointAddScore_eq]; norm_num

/-! ### Placement against the ECDSA.fail leaderboard (CONJECTURAL / EXTERNAL) -/

/-- **ECDSA.fail leaderboard best (EXTERNAL reference).** `≈ 1.57×10⁹`, the leaderboard's best
`Toffoli × peak-qubits` score for one point operation (`~1152` qubits × `~1.36×10⁶` Toffoli). A
CONJECTURAL / EXTERNAL datum: it is *not* validated against our circuit model (their executed-average
Toffoli vs our worst-case upper bound), used only to position the figures. -/
def ecdsaFailLeaderboardBest : ℕ := 1570000000

/-- **The gap L6 closes — before.** The Fermat benchmark score is `> 1216×` the leaderboard best:
`ecdsaFailLeaderboardBest · 1216 < onePointAddScore` (`1.909×10¹² < 1.910×10¹²`). The full gap is
`~1217×`. -/
theorem fermat_score_gap_vs_leaderboard :
    ecdsaFailLeaderboardBest * 1216 < onePointAddScore := by
  rw [onePointAddScore_eq]; norm_num [ecdsaFailLeaderboardBest]

/-- **The gap L6 closes — after (lower bound).** The binary-GCD score is still `> 14×` the leaderboard
best: `ecdsaFailLeaderboardBest · 14 < onePointAddScore_safegcd`. -/
theorem safegcd_score_gap_vs_leaderboard_lower :
    ecdsaFailLeaderboardBest * 14 < onePointAddScore_safegcd := by
  rw [onePointAddScore_safegcd_eq]; norm_num [ecdsaFailLeaderboardBest]

/-- **The gap L6 closes — after (upper bound).** The binary-GCD score is `< 15×` the leaderboard best:
`onePointAddScore_safegcd < ecdsaFailLeaderboardBest · 15`. Together with the lower bound, L6 brings
the gap from `~1217×` (Fermat) to `~14×` (binary-GCD) — closing the dominant `~86×` of the
`~1220×` leaderboard gap; the residual `~14×` is the documented optimisations (windowing, sub-quadratic
multiply, measurement-based adders) plus the worst-case-vs-executed-average modelling gap. -/
theorem safegcd_score_gap_vs_leaderboard_upper :
    onePointAddScore_safegcd < ecdsaFailLeaderboardBest * 15 := by
  rw [onePointAddScore_safegcd_eq]; norm_num [ecdsaFailLeaderboardBest]

/-! ### Windowed Fermat inversion — a DOCUMENTED COMPARISON, off the critical path (L2)

**This block is a standalone cost-model comparison closing L2; it is NOT on the critical path.**
The point addition now inverts via **safegcd** (the L6 `safegcdInvToffoli` above), NOT via Fermat, so
nothing here feeds `onePointAddScore_safegcd` / `onePointAddToffoli_safegcd`: `windowedFermatInvToffoli`
is referenced by no point-op definition. It exists only to answer "does the standard *windowed*
(`2^k`-ary) refinement of Fermat exponentiation close the gap to safegcd?" — and the answer is no.

**The model.** Windowed (`2^k`-ary) modular exponentiation of `a^{p-2}` over an `~n`-bit exponent does
`~n` squarings, `~n/k` window-multiplies, and `~2^k` precomputed-power multiplies, each one a verified
carry-clean modular multiply `cleanModMulToffoli n`. So the multiply count is `n + n/k + 2^k` and
`windowedFermatInvToffoli n k = (n + n/k + 2^k)·cleanModMulToffoli n`. This is the `2^k`-ary refinement
of `fermatInvToffoli n = 2n·cleanModMulToffoli n` (`Inversion.modExpFieldMults`'s `≤ 2n`): at small
optimal `k` the multiply count is `~n·(1 + 1/k)` (vs naive `2n`), a constant `~1.4–1.7×` saving — but
STILL `O(n)` modular multiplies, i.e. `O(n³)` Toffoli.

**Tiers (honest, cost-model only — NO value-correctness claim beyond what already exists).**
* **DOCUMENTED**: the windowed op-count `n + n/k + 2^k` and the window parameter `k` (same status as
  `fermatInvToffoli`'s `2n` op-count model; an analogue of `modExpFieldMults`, no windowed-exponentiation
  *circuit* is exhibited).
* **VERIFIED**: the per-multiply base `cleanModMulToffoli` (the carry-clean modular multiply Toffoli cost,
  tied to `Reversible.cuccaroModMul_toffoli` by `cleanModMulToffoli_eq_cuccaro`).
* **CONJECTURAL / EXTERNAL**: n/a here — the inverse VALUE is unchanged (still `a⁻¹ = a^{p-2}`, the proved
  `ECDLP.fermatInv_eq_inv`); this block makes no new value claim, it only re-costs the same exponentiation.

The headline `safegcd_beats_windowed_fermat` confirms safegcd (`O(n²)`) wins by `~120×` even against
windowed Fermat: windowing buys a constant factor over naive Fermat but cannot overcome the structural
`O(n³)`-vs-`O(n²)` gap. -/

/-- **Windowed (`2^k`-ary) Fermat inversion Toffoli cost (DOCUMENTED op-count model).**
`(n + n/k + 2^k)·cleanModMulToffoli n` — `~n` squarings + `~n/k` window-multiplies + `~2^k`
precomputed-power multiplies, each the verified carry-clean modular multiply `cleanModMulToffoli n`. The
`2^k`-ary refinement of `fermatInvToffoli n = 2n·cleanModMulToffoli n`. Same honesty status as
`fermatInvToffoli`: a documented op-count model (analogue of `Inversion.modExpFieldMults`) times the
verified per-multiply cost; no separately-exhibited windowed-exponentiation circuit. **Off the critical
path:** no point-op definition references it (the point addition inverts via `safegcdInvToffoli`); this
is the standalone L2 comparison only. -/
def windowedFermatInvToffoli (n k : ℕ) : ℕ := (n + n / k + 2 ^ k) * cleanModMulToffoli n

/-- One secp256k1 windowed-Fermat inversion at window `k = 6` costs `475 778 048 ≈ 4.8×10⁸` Toffolis:
`256 + 256/6 + 2^6 = 256 + 42 + 64 = 362` verified carry-clean multiplies (note `256/6 = 42` in `ℕ`,
not the round-up `43`), each `cleanModMulToffoli 256 = 1 314 304`. Contrast naive Fermat
`fermatInvToffoli 256 = 672 923 648` — windowing saves the constant factor `~1.41×`
(`windowedFermatInvToffoli_lt_fermat_secp256k1`). -/
theorem windowedFermatInvToffoli_secp256k1 :
    windowedFermatInvToffoli Secp256k1.bits 6 = 475778048 := by
  norm_num [windowedFermatInvToffoli, cleanModMulToffoli, Secp256k1.bits]

/-- **Windowing beats naive Fermat by a constant factor.** At `n = 256`, `k = 6`:
`windowedFermatInvToffoli 256 6 = 475 778 048 < 672 923 648 = fermatInvToffoli 256` — the `~1.41×`
windowing saving (`362` window-multiplies vs the naive `512`). Still `O(n³)`. -/
theorem windowedFermatInvToffoli_lt_fermat_secp256k1 :
    windowedFermatInvToffoli Secp256k1.bits 6 < fermatInvToffoli Secp256k1.bits := by
  rw [windowedFermatInvToffoli_secp256k1, fermatInvToffoli_secp256k1]; norm_num

/-- **THE HEADLINE COMPARISON: safegcd wins even against windowed Fermat (`~120×`).**
`safegcdInvToffoli 256 = 3 939 328 < 475 778 048 = windowedFermatInvToffoli 256 6` — the `O(n²)`
binary-GCD inversion is `~120×` cheaper than the `2^6`-ary windowed Fermat exponentiation. Windowing
saves a constant `~1.4×` over naive Fermat but cannot overcome the structural `O(n³)`-vs-`O(n²)` gap.
This closes L2 as a documented comparison. -/
theorem safegcd_beats_windowed_fermat :
    safegcdInvToffoli Secp256k1.bits < windowedFermatInvToffoli Secp256k1.bits 6 := by
  rw [safegcdInvToffoli_secp256k1, windowedFermatInvToffoli_secp256k1]; norm_num

/-- **Windowed Fermat stays `O(n³)` for any fixed window `k`.** For every register width `n` and window
`k`, `windowedFermatInvToffoli n k ≥ n·cleanModMulToffoli n = 20n³ + 14n²` — the multiply count
`n + n/k + 2^k ≥ n` is `Ω(n)`, so windowing cannot drop the inversion below the cubic Toffoli class,
whatever `k`. Contrast safegcd's `O(n²)` (`safegcdInvToffoli_eq : 60n² + 28n`). The structural reason
the `~120×` gap at `n = 256` only widens with `n`. -/
theorem windowedFermatInvToffoli_ge_cubic (n k : ℕ) :
    n * cleanModMulToffoli n ≤ windowedFermatInvToffoli n k := by
  unfold windowedFermatInvToffoli
  gcongr
  exact le_trans (Nat.le_add_right n (n / k)) (Nat.le_add_right _ (2 ^ k))

end ECDLP.ResourceBounds
