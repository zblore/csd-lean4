/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul

/-!
# Reversible modular inverse — the semantic layer  (ECDLP Tranche 4)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The modular-inverse layer of the reversible-arithmetic substrate (`specs/ecdlp-resource-plan.md`). The
semantic target is the oracle action `y ↦ y⁻¹` on `ZMod N` (modular inversion — the field division
underlying elliptic-curve slope computation). Per the investigation map this layer is **reuse**: the
arithmetic content is Mathlib's `ZMod` inverse (`ZMod.mul_inv_of_unit`, `inv_mul_of_unit`,
`isUnit_iff_coprime`, `unitOfCoprime`), so this module is the thin oracle + algebra on top, and — the
load-bearing increment — the **reversibility connection to the multiplication oracle** (Tranche 3):
multiplying by `a` is undone by multiplying by `a⁻¹`, so `mulConst a` is a reversible permutation whose
inverse is `mulConst a⁻¹`.

## What is proved here

* `modInv N a := a⁻¹` — the modular-inverse oracle action; `mul_modInv_of_unit` / `modInv_mul_of_unit`
  (`a · a⁻¹ = 1` for units), `isUnit_modInv`, `modInv_modInv` (involution on units).
* `modInv_isUnit_iff_coprime` — the unit ⇔ coprimality bridge (reuse `ZMod.isUnit_iff_coprime`).
* `mulConst_modInv_leftInverse` / `_rightInverse` — **the reversibility link**: `mulConst a⁻¹` is the
  two-sided inverse of `mulConst a` on a unit `a`; hence `mulConst_modInv_bijective`.

## Honest scope — no inversion circuit (and why that is the right call here)

This is the **semantic / algebraic** layer only. A *reversible circuit* for modular inversion (extended
Euclid) is large and is **not** built. This is deliberate and standard for ECDLP resource accounting:
elliptic-curve point arithmetic in **projective / Jacobian coordinates** avoids a per-operation field
inversion (one inversion at the very end, or via Fermat `a⁻¹ = a^{N-2}` = modular exponentiation built
from the Tranche-3 multiplier). So the dominant cost is multiplications (Tranche 3, with derived gate
counts), and the inversion-as-a-circuit is deferred to the EC layer's coordinate choice. What is
established here is the inversion *oracle* and the reversibility algebra that the EC group law consumes.
-/

@[expose] public section

namespace Reversible

variable {N : ℕ}

/-- The modular-inverse oracle action: `y ↦ y⁻¹` on `ZMod N` (Mathlib's `ZMod` inverse). -/
def modInv (N : ℕ) (a : ZMod N) : ZMod N := a⁻¹

/-- For a unit `a`, `a · a⁻¹ = 1` (reuse `ZMod.mul_inv_of_unit`). -/
theorem mul_modInv_of_unit {a : ZMod N} (h : IsUnit a) : a * modInv N a = 1 :=
  ZMod.mul_inv_of_unit a h

/-- For a unit `a`, `a⁻¹ · a = 1` (reuse `ZMod.inv_mul_of_unit`). -/
theorem modInv_mul_of_unit {a : ZMod N} (h : IsUnit a) : modInv N a * a = 1 :=
  ZMod.inv_mul_of_unit a h

/-- The modular inverse of a unit is a unit. -/
theorem isUnit_modInv {a : ZMod N} (h : IsUnit a) : IsUnit (modInv N a) :=
  IsUnit.of_mul_eq_one a (modInv_mul_of_unit h)

/-- **`modInv` is an involution on units**: `(a⁻¹)⁻¹ = a`. So as a permutation of the units, the
modular-inverse oracle is its own inverse. -/
theorem modInv_modInv {a : ZMod N} (h : IsUnit a) : modInv N (modInv N a) = a :=
  calc modInv N (modInv N a)
      = modInv N (modInv N a) * (modInv N a * a) := by rw [modInv_mul_of_unit h, mul_one]
    _ = modInv N (modInv N a) * modInv N a * a := by rw [mul_assoc]
    _ = 1 * a := by rw [modInv_mul_of_unit (isUnit_modInv h)]
    _ = a := one_mul a

/-- The unit ⇔ coprimality bridge: `(m : ZMod N)` is invertible iff `m` is coprime to `N` (reuse
`ZMod.isUnit_iff_coprime`). The admissibility condition for a modular inverse to exist. -/
theorem modInv_isUnit_iff_coprime (m : ℕ) : IsUnit (m : ZMod N) ↔ m.Coprime N :=
  ZMod.isUnit_iff_coprime m N

/-! ### Reversibility: the multiplication oracle is inverted by `mulConst` at the modular inverse -/

/-- **`mulConst a⁻¹` left-inverts `mulConst a`** (for a unit `a`): multiplying by `a` then by `a⁻¹`
recovers `y`. So the reversible circuit realising `mulConst a` (Tranche 3) is undone by the one for
`mulConst a⁻¹`. -/
theorem mulConst_modInv_leftInverse {a : ZMod N} (h : IsUnit a) (y : ZMod N) :
    mulConst N (modInv N a) (mulConst N a y) = y := by
  rw [mulConst, mulConst, modInv, ← mul_assoc, ZMod.inv_mul_of_unit a h, one_mul]

/-- **`mulConst a⁻¹` right-inverts `mulConst a`** (for a unit `a`). -/
theorem mulConst_modInv_rightInverse {a : ZMod N} (h : IsUnit a) (y : ZMod N) :
    mulConst N a (mulConst N (modInv N a) y) = y := by
  rw [mulConst, mulConst, modInv, ← mul_assoc, ZMod.mul_inv_of_unit a h, one_mul]

/-- The multiplication oracle `mulConst a` is a bijection for a unit `a`, with explicit inverse
`mulConst a⁻¹` — the reversibility witness underlying its reversible-circuit realisation. Strengthens
`ModMul.mulConst_bijective` (which proves bijectivity without exposing `modInv` as the inverse) by
threading `mulConst (modInv a)` as the two-sided inverse the EC layer consumes. -/
theorem mulConst_modInv_bijective {a : ZMod N} (h : IsUnit a) :
    Function.Bijective (mulConst N a) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨mulConst N (modInv N a), mulConst_modInv_leftInverse h, mulConst_modInv_rightInverse h⟩

end Reversible
