import CsdLean4.Mathlib.QuantumInfo.ECDLP.EllipticCurve
import Mathlib.Data.Nat.Size

/-!
# Double-and-add scalar multiplication  (ECDLP Tranche 6)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The efficient algorithm for elliptic-curve scalar multiplication `[k]P` (`specs/ecdlp-resource-plan.md`).
`doubleAndAdd P k` is the standard binary double-and-add — `[2m]P = 2([m]P)`, `[2m+1]P = 2([m]P) + P` —
stated for any `AddMonoid` (so it applies to the Mathlib elliptic-curve point group). Two deliverables:

* **Correctness** `doubleAndAdd_eq_nsmul : doubleAndAdd P k = k • P`, hence `doubleAndAdd_eq_scalarMul`
  (`= ECDLP.scalarMul P k`) — the algorithm computes the Tranche-5 discrete-log map `[k]P`, closing the
  loop from this algorithm to the EC math layer.
* **Cost** `doubleAndAddCost k` (the count of doublings + additions, read off the recursion — derived,
  not annotated) with the **logarithmic bound** `doubleAndAddCost_le : ≤ 2 · Nat.size k`. This is the
  resource content: `[k]P` is `O(log k)` point operations — each ultimately a fixed number of modular
  multiplications (the EC addition formula) costing the Tranche-3 multiplier's derived Toffolis.
-/

namespace ECDLP

variable {M : Type*} [AddMonoid M]

/-- **Double-and-add** for `[k]P`: `[2m]P = 2([m]P)`, `[2m+1]P = 2([m]P) + P`. The standard
logarithmic-time scalar-multiplication algorithm (general `AddMonoid`). -/
def doubleAndAdd (P : M) (k : ℕ) : M :=
  if k = 0 then 0
  else 2 • doubleAndAdd P (k / 2) + (if k % 2 = 1 then P else 0)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹k ≠ 0›) one_lt_two

/-- **Double-and-add correctness**: it computes `[k]P = k • P`. -/
theorem doubleAndAdd_eq_nsmul (P : M) (k : ℕ) : doubleAndAdd P k = k • P := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [doubleAndAdd]
    split
    · rename_i hk; subst hk; simp
    · rename_i hk
      rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hk) one_lt_two)]
      have h1 : (2 : ℕ) • ((k / 2) • P) = (2 * (k / 2)) • P := (mul_nsmul' P 2 (k / 2)).symm
      have h2 : (if k % 2 = 1 then P else 0) = (k % 2) • P := by
        rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]
      rw [h1, h2, ← add_nsmul, Nat.div_add_mod]

/-! ### Operation count and the logarithmic cost bound -/

/-- The number of point operations (doublings + additions) double-and-add performs for `[k]P` — read
off the recursion (one doubling per level, plus one addition when the bit is set). -/
def doubleAndAddCost (k : ℕ) : ℕ :=
  if k = 0 then 0
  else (1 + (if k % 2 = 1 then 1 else 0)) + doubleAndAddCost (k / 2)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹k ≠ 0›) one_lt_two

/-- **Logarithmic cost**: double-and-add uses at most `2 · Nat.size k` point operations (a doubling and
at most one addition per bit of `k`). This is the `O(log k)` that makes scalar multiplication efficient
— the first factor of the ECDLP resource estimate. -/
theorem doubleAndAddCost_le (k : ℕ) : doubleAndAddCost k ≤ 2 * Nat.size k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [doubleAndAddCost]
    split
    · rename_i hk; subst hk; simp
    · rename_i hk
      have hpos : 0 < k := Nat.pos_of_ne_zero hk
      have hsize : Nat.size k = Nat.size (k / 2) + 1 := by
        have hbne : Nat.bit (Nat.bodd k) (Nat.div2 k) ≠ 0 := by rw [Nat.bit_bodd_div2]; exact hk
        rw [← Nat.div2_val, ← Nat.succ_eq_add_one, ← Nat.size_bit hbne, Nat.bit_bodd_div2]
      have hrec := ih (k / 2) (Nat.div_lt_self hpos one_lt_two)
      have hbit : (if k % 2 = 1 then 1 else 0) ≤ 1 := by split <;> omega
      omega

/-! ### Per-operation-type weighted cost (doublings vs additions cost differently)

Double-and-add does one **doubling** per bit and one **addition** per set bit, and on an elliptic curve
these cost different numbers of field multiplications (a doubling is cheaper than a mixed addition). The
uniform `pointOpCost` bound over-counts; `doubleAndAddWeightedCost wDbl wAdd k` weights the two
separately, giving a tighter, more accurate field-multiplication count for the resource estimate. -/

/-- Per-operation-type cost of double-and-add: `wDbl` per doubling (one per bit) and `wAdd` per addition
(one per set bit). -/
def doubleAndAddWeightedCost (wDbl wAdd : ℕ) (k : ℕ) : ℕ :=
  if k = 0 then 0
  else (wDbl + (if k % 2 = 1 then wAdd else 0)) + doubleAndAddWeightedCost wDbl wAdd (k / 2)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹k ≠ 0›) one_lt_two

/-- **Weighted logarithmic cost**: at most `Nat.size k · (wDbl + wAdd)` — one doubling and at most one
addition per bit of `k`. Tighter than the uniform bound (`size k · (wDbl+wAdd)` vs `2·size k · max`). -/
theorem doubleAndAddWeightedCost_le (wDbl wAdd k : ℕ) :
    doubleAndAddWeightedCost wDbl wAdd k ≤ Nat.size k * (wDbl + wAdd) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [doubleAndAddWeightedCost]
    split
    · rename_i hk; subst hk; simp
    · rename_i hk
      have hpos : 0 < k := Nat.pos_of_ne_zero hk
      have hsize : Nat.size k = Nat.size (k / 2) + 1 := by
        have hbne : Nat.bit (Nat.bodd k) (Nat.div2 k) ≠ 0 := by rw [Nat.bit_bodd_div2]; exact hk
        rw [← Nat.div2_val, ← Nat.succ_eq_add_one, ← Nat.size_bit hbne, Nat.bit_bodd_div2]
      have hrec := ih (k / 2) (Nat.div_lt_self hpos one_lt_two)
      have hbit : (if k % 2 = 1 then wAdd else 0) ≤ wAdd := by split <;> omega
      rw [hsize, Nat.succ_mul]
      omega

/-! ### Loop closure to the Tranche-5 elliptic-curve scalar-multiplication map -/

open WeierstrassCurve

/-- **Loop closure**: double-and-add computes the Tranche-5 elliptic-curve discrete-log map
`[k]P = scalarMul P k`. So the efficient `O(log k)` algorithm and the `[k]P` map ECDLP inverts agree —
and the resource estimate (`doubleAndAddCost_le`) is a cost bound for computing `scalarMul`. -/
theorem doubleAndAdd_eq_scalarMul {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
    (P : W.Point) (k : ℕ) : doubleAndAdd P k = scalarMul P k :=
  doubleAndAdd_eq_nsmul P k

end ECDLP
