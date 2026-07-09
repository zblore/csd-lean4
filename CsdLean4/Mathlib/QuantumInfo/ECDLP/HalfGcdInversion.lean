import CsdLean4.Mathlib.QuantumInfo.ECDLP.KaratsubaMul

/-!
# Half-GCD (recursive) modular inversion — the sub-quadratic lever, quantified  (ECDLP L8)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The safegcd inversion (`SafegcdInversion.lean`) is `O(n²)`; the ecdsa.fail leaders use it, and after the
honest Bernstein–Yang `3n` correction the corpus sits `~1.43×` above their Toffoli figure. Can we BEAT
them rather than reproduce? The only genuine *asymptotic* lever is a **quasi-linear** inversion: the
recursive / half-GCD algorithm (Schönhage; Stehlé–Yang–Zimmermann), which computes the extended GCD in
`O(M(n) · log n)` field multiplications — `O(n^{1.585} log n)` with Karatsuba `M(n)`, strictly below
safegcd's `O(n²)` in the exponent.

This file **models that lever and quantifies whether it wins at the ECDLP width `n = 256`.** The answer
is precise and on the boundary:

    halfGcdInvToffoli k 256 = (log₂ 256) · k · (karatsubaToffoli 256) = 8 · k · 653388,

so half-GCD is cheaper than `safegcdInvToffoli 256 = 5 908 992` **iff `k = 1`** (an aggressively-tuned
recursion averaging ≤ one full-width Karatsuba multiply per level, ≤ 8 total): `8 · 653388 = 5 227 104
< 5 908 992` — a `~12%` BEAT. At `k ≥ 2` (a standard recursion, several multiplies per level) it loses:
`5 908 992 < 8 · 2 · 653388 = 10 454 208`.

**Honest conclusion.** The sub-quadratic inversion is a *genuine beat candidate at 256* — not hopeless,
but on the knife-edge: it beats safegcd only if the recursion is tuned down to `~8` full multiplies
total (`k = 1`), which is more aggressive than a textbook half-GCD (`k ~ 2–9`). Because the exponent is
sub-quadratic, for ANY fixed `k` it beats safegcd for large enough `n` (the crossover moves *above* 256
as `k` grows); the `k = 1` model already crosses at 256. So the corpus's safegcd choice is right at 256
for a standard recursion, and the realistic path to a *beat* is a highly-tuned half-GCD (few multiplies
per level) plus a faster `M(n)` (Toom/FFT), pushing the crossover down to 256.

## HONEST STATUS (read before citing)

`halfGcdInvToffoli` is a **DOCUMENTED op-count model** — the same tier as `safegcdInvToffoli` and
`windowedFermatInvToffoli`: a recursion-shape count (`log n` levels × `k` multiplies) times the
**verified** Karatsuba multiply cost `karatsubaToffoli` (tied to `Reversible.cuccaroModMul_correct`). No
half-GCD circuit is exhibited and no value-correctness of a half-GCD *circuit* is claimed; the recursion
constant `k` is the documented modelling input, and the results are stated as a function of `k`. The
comparison to the leaderboard remains CONJECTURAL/EXTERNAL.

## Main results

- `halfGcd_aggressive_beats_safegcd_256` — at `k = 1`, half-GCD BEATS safegcd at 256.
- `halfGcd_standard_loses_safegcd_256` — at `k = 2`, half-GCD loses at 256.
- `halfGcd_beats_iff_k_one_256` — the exact threshold: it beats at 256 iff `k ≤ 1`.
-/

namespace ECDLP.ResourceBounds

open ECDLP

/-- **Half-GCD (recursive / Schönhage–Stehlé–Yang–Zimmermann) modular-inversion cost model.**
`multsPerLevel` full-width Karatsuba multiplies at each of the `~log₂ n` recursion levels:
`halfGcdInvToffoli k n = (log₂ n) · k · karatsubaToffoli n`. This is `O(M(n) · log n) =
O(n^{1.585} log n)` with the verified Karatsuba multiply `M(n) = karatsubaToffoli n` — SUB-QUADRATIC in
the exponent (below safegcd's `O(n²)`), at the price of a `log n` factor and the recursion constant `k`.
DOCUMENTED op-count model (like `safegcdInvToffoli`); no half-GCD circuit exhibited. -/
def halfGcdInvToffoli (multsPerLevel n : ℕ) : ℕ :=
  Nat.log2 n * multsPerLevel * karatsubaToffoli n

/-- `karatsubaToffoli 256 = 653388` (the verified Karatsuba multiply at the ECDLP width). -/
private theorem karatsubaToffoli_256 : karatsubaToffoli 256 = 653388 :=
  karatsubaToffoli_secp256k1

/-- `safegcdInvToffoli 256 = 5908992` (the honest Bernstein–Yang `3n` figure). -/
private theorem safegcdInvToffoli_256 : safegcdInvToffoli 256 = 5908992 :=
  safegcdInvToffoli_secp256k1

/-- `log₂ 256 = 8`. -/
private theorem log2_256 : Nat.log2 256 = 8 := by decide

/-- **An aggressively-tuned half-GCD BEATS safegcd at 256.** If the recursion averages at most one
full-width Karatsuba multiply per level (`k = 1`, i.e. `≤ log₂ 256 = 8` multiplies total), the half-GCD
inversion is strictly cheaper than safegcd at the ECDLP width:
`halfGcdInvToffoli 1 256 = 8 · 653388 = 5 227 104 < 5 908 992 = safegcdInvToffoli 256`. So the
sub-quadratic lever is a genuine beat candidate at 256 — a `~12%` win, on the boundary. -/
theorem halfGcd_aggressive_beats_safegcd_256 :
    halfGcdInvToffoli 1 256 < safegcdInvToffoli 256 := by
  rw [halfGcdInvToffoli, log2_256, karatsubaToffoli_256, safegcdInvToffoli_256]; norm_num

/-- **A standard half-GCD LOSES to safegcd at 256.** At `k = 2` (two full-width multiplies per level,
still optimistic for a real recursion) the half-GCD figure exceeds safegcd:
`safegcdInvToffoli 256 = 5 908 992 < 10 454 208 = halfGcdInvToffoli 2 256`. So a textbook half-GCD does
not beat at 256; safegcd is the right `O(n²)` choice at the ECDLP width. -/
theorem halfGcd_standard_loses_safegcd_256 :
    safegcdInvToffoli 256 < halfGcdInvToffoli 2 256 := by
  rw [halfGcdInvToffoli, log2_256, karatsubaToffoli_256, safegcdInvToffoli_256]; norm_num

/-- **The exact threshold at 256: half-GCD beats safegcd iff `k ≤ 1`.** The crossover in the recursion
constant is sharp — an aggressive `≤ 1` full-multiply-per-level recursion wins; anything at `≥ 2` loses.
This pins the sub-quadratic lever's viability at the ECDLP width to whether the half-GCD recursion can be
tuned to `~8` total full-width multiplies. -/
theorem halfGcd_beats_iff_k_one_256 (k : ℕ) :
    halfGcdInvToffoli k 256 < safegcdInvToffoli 256 ↔ k ≤ 1 := by
  rw [halfGcdInvToffoli, log2_256, karatsubaToffoli_256, safegcdInvToffoli_256]
  omega

end ECDLP.ResourceBounds

