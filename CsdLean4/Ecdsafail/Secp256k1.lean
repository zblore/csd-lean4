import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.ZMod.Basic

/-!
# The secp256k1 elliptic curve  (ECDLP Tranche 7, parameters)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The concrete curve targeted by the ECDLP resource-accounting programme
(`specs/ecdlp-resource-plan.md`): **secp256k1**, `y² = x³ + 7` over `𝔽_p` with
`p = 2^256 − 2^32 − 977` (the Bitcoin / SEC curve). This module fixes the parameters and the
Weierstrass curve object; `ResourceBounds.lean` assembles the cost estimate.

**Honest scope.** The curve *definition* needs only `CommRing (ZMod p)` (always available), so no
primality proof is required here — and `p`'s 256-bit primality (a standard, citable fact) is **not**
reproved in Lean (infeasible at this size without an ECPP/Pratt certificate; it is library/number-theory
debt, not a theory commitment). The `Field 𝔽_p` and `AddCommGroup` point-group structure that genuine
point arithmetic uses are gated on `Fact p.Prime`, supplied as a hypothesis where needed. The resource
bounds downstream are driven by the **bit length** `bits = 256`, which needs none of this.
-/

namespace ECDLP.Secp256k1

/-- The secp256k1 base-field prime `p = 2^256 − 2^32 − 977`. -/
def p : ℕ := 2 ^ 256 - 2 ^ 32 - 977

/-- The curve constant: secp256k1 is `y² = x³ + 7`. -/
def b : ℕ := 7

/-- The bit length of the secp256k1 field and scalars — the size parameter of the resource estimate. -/
def bits : ℕ := 256

/-- The **secp256k1 Weierstrass curve** `y² = x³ + 7` over `𝔽_p` (`a₁=a₂=a₃=a₄=0`, `a₆=7`). The
definition needs only the `CommRing (ZMod p)` structure. -/
def curve : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := (b : ZMod p)

theorem p_pos : 0 < p := by
  have h1 : 2 ^ 32 + 977 < 2 ^ 256 := by norm_num
  rw [p]; omega

/-- `p` fits in 256 bits (`p < 2^256`) — it is `2^256` minus positive terms. -/
theorem p_lt_two_pow : p < 2 ^ 256 := by
  have h1 : (0 : ℕ) < 2 ^ 32 + 977 := by norm_num
  have h2 : 2 ^ 32 + 977 ≤ 2 ^ 256 := by norm_num
  rw [p]; omega

end ECDLP.Secp256k1
