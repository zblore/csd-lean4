import CsdLean4.Mathlib.QuantumInfo.Reversible.ModInv
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Size

/-!
# Fermat modular inversion — the algebra and its op count  (ECDLP, inversion-omission close)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The prior secp256k1 resource figures (`ResourceBounds.lean`) cost modular **multiplication** in full but
**omit modular inversion** entirely — a genuine undercount. The honest, no-new-circuit way to cost an
inversion from what the corpus already has is **Fermat's little theorem**: over a prime field `ZMod p`,
`a^{p-1} = 1` for `a ≠ 0`, so

  `a⁻¹ = a^{p-2}`  (`fermatInv`),

a modular exponentiation. Square-and-multiply computes `a^e` with `≈ size(e)` squarings + `≤ size(e)`
multiplications, i.e. `≤ 2·size(e)` modular multiplies (the same `O(log)` shape as
`ECDLP.doubleAndAddCost`, mirrored here as `modExpFieldMults`). At width `n = size(p)` this is `≤ 2n`
verified modular multiplies, each the corpus's `cleanModMulToffoli n = 20n² + 14n` — so one inversion is
`≈ 2n·(20n²+14n) = O(n³)` Toffoli, derived (not annotated) from the EXISTING verified multiply.

This is a **conservative** upper bound: the optimal extended-Euclid / Kaliski inversion is `O(n²)`,
cheaper, but needs a separate verified inversion circuit. Fermat is what the corpus can cost from what it
already has. The Toffoli fold-in lives in `ResourceBounds.lean §"Fermat modular inversion"`.

## What is proved here

* `fermatInv p a := a^{p-2}` and the correctness `fermatInv_eq_inv` (`= a⁻¹`, via Fermat,
  carrying `[Fact p.Prime]` — the named secp256k1 primality residue), plus `fermatInv_eq_modInv`
  tying it to the `Reversible.modInv` algebra.
* `modExpFieldMults e` (the square-and-multiply field-multiply count for `a^e`, mirroring
  `doubleAndAddCost`) with `modExpFieldMults_le : ≤ 2·Nat.size e`.
* `fermatInvFieldMults p := modExpFieldMults (p-2)` with `fermatInvFieldMults_le : ≤ 2·Nat.size (p-2)`.
-/

namespace ECDLP

/-! ### Fermat inversion: `a⁻¹ = a^{p-2}` over a prime field -/

/-- **Fermat modular inverse**: `fermatInv p a = a^{p-2}`. Over a prime field this equals `a⁻¹` for
`a ≠ 0` (`fermatInv_eq_inv`); the cost below counts modular multiplies that genuinely compute the
inverse. -/
def fermatInv (p : ℕ) (a : ZMod p) : ZMod p := a ^ (p - 2)

/-- **Fermat's little theorem ⇒ inversion.** Over `ZMod p` with `p` prime, `a^{p-2} = a⁻¹` for every
`a ≠ 0`: `a · a^{p-2} = a^{p-1} = 1` (`ZMod.pow_card_sub_one_eq_one`), so `a^{p-2}` is the inverse. The
`[Fact p.Prime]` hypothesis is what makes `ZMod p` a field; for secp256k1 it is the **named primality
residue** (`p`'s 256-bit primality is not reproved in Lean). -/
theorem fermatInv_eq_inv {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    fermatInv p a = a⁻¹ := by
  have hp : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hfl : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hsucc : p - 1 = (p - 2) + 1 := by omega
  rw [hsucc, pow_succ] at hfl
  exact eq_inv_of_mul_eq_one_left hfl

/-- **Tie to the `Reversible.modInv` algebra.** `fermatInv p a = modInv p a` (`= a⁻¹`) for `a ≠ 0` over a
prime field — the Fermat exponentiation realises the same oracle action the reversibility layer
(`ModInv.lean`) consumes. -/
theorem fermatInv_eq_modInv {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    fermatInv p a = Reversible.modInv p a := by
  rw [fermatInv_eq_inv ha, Reversible.modInv]

/-! ### Square-and-multiply op count (mirrors `ECDLP.doubleAndAddCost`)

`a^e` by square-and-multiply does one **squaring** per level and one **multiply** when the bit is set —
the same `size + popcount`, `≤ 2·size` shape as `doubleAndAddCost`. We count field multiplications
(squarings counted as multiplications). -/

/-- The number of field multiplications square-and-multiply performs for `a^e` — read off the recursion
(one squaring per level, plus one multiply when the bit is set). Mirrors `ECDLP.doubleAndAddCost`. -/
def modExpFieldMults (e : ℕ) : ℕ :=
  if e = 0 then 0
  else (1 + (if e % 2 = 1 then 1 else 0)) + modExpFieldMults (e / 2)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹e ≠ 0›) one_lt_two

/-- **Logarithmic cost**: square-and-multiply uses at most `2 · Nat.size e` field multiplications (a
squaring and at most one multiply per bit of `e`). Mirrors `ECDLP.doubleAndAddCost_le`. -/
theorem modExpFieldMults_le (e : ℕ) : modExpFieldMults e ≤ 2 * Nat.size e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [modExpFieldMults]
    split
    · rename_i he; subst he; simp
    · rename_i he
      have hpos : 0 < e := Nat.pos_of_ne_zero he
      have hsize : Nat.size e = Nat.size (e / 2) + 1 := by
        have hbne : Nat.bit (Nat.bodd e) (Nat.div2 e) ≠ 0 := by rw [Nat.bit_bodd_div2]; exact he
        rw [← Nat.div2_val, ← Nat.succ_eq_add_one, ← Nat.size_bit hbne, Nat.bit_bodd_div2]
      have hrec := ih (e / 2) (Nat.div_lt_self hpos one_lt_two)
      have hbit : (if e % 2 = 1 then 1 else 0) ≤ 1 := by split <;> omega
      omega

/-- Field multiplications to compute the Fermat inverse `a^{p-2}` by square-and-multiply. -/
def fermatInvFieldMults (p : ℕ) : ℕ := modExpFieldMults (p - 2)

/-- **Fermat inversion is `≤ 2·Nat.size (p-2)` field multiplications** — so `≤ 2n` at register width
`n = size(p)`. This is the op-count factor the Toffoli fold-in (`ResourceBounds.fermatInvToffoli`)
multiplies by the verified per-multiply cost. -/
theorem fermatInvFieldMults_le (p : ℕ) : fermatInvFieldMults p ≤ 2 * Nat.size (p - 2) :=
  modExpFieldMults_le (p - 2)

end ECDLP
