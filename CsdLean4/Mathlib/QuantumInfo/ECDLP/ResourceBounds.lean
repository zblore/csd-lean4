import CsdLean4.Mathlib.QuantumInfo.ECDLP.ScalarMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
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

end ECDLP.ResourceBounds
