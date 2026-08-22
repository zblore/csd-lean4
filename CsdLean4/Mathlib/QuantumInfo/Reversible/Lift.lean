/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Register
public import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd

/-!
# The Boolean → amplitude lift of reversible circuits

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The bridge between the two layers this directory and `QuantumInfo/Register.lean` provide:
a reversible classical gate (`Reversible.Gate`, Boolean state `Fin n → Bool`) acts on the
quantum register `QReg n = EuclideanSpace ℂ (Fin n → Fin 2)` as a **permutation matrix on
computational basis states**, and the permutation is exactly the gate's Boolean `denote`
semantics, modulo the `Bool ↔ Fin 2` recast of the wires. This is the "later embedding
step" that `Circuit.lean`'s design note deliberately kept out of the classical layer —
delivered here, beside the DSL, for the CCX/Toffoli gate.

## What is proved

* `toEuclideanLin_basisState_m` — the column read: a register operator applied to a
  computational basis state reads off the corresponding matrix column. (The generic width
  form; everything below routes through it.)
* Fixed three-wire form (`Fin 3 → Fin 2`, wires `0,1,2`): `ccx` (the CCX permutation on
  indices), `andUncompMat` (its permutation matrix), the recasts `stateOfB3` / `b3OfState`,
  and `andUncompMat_lifts_denote` — the matrix acts on basis states exactly as the Boolean
  `denote (andUncompute 0 1 2)` permutation.
* Arbitrary wires, any width: `ccxAt` / `ccxAtMat` / `stateOfReg` / `regOfState` and
  `ccxAtMat_lifts_denote` — the same lift for a CCX at wires `(wa, wb, wg)` on `QReg m`,
  with `wg` distinct from the controls.

The permutation matrices are genuine unitaries on the full register (identity off the
target wire), so a single reversible gate embeds soundly as a local unitary; iterating
over a gate list lifts a whole permutation circuit basis-state by basis-state.

## What is deliberately NOT here

* **The general lift** — per-constructor lemmas for `X`, `CX` and `swap` (each easier than the
  CCX case done here) plus the gate-list fold (a nontrivial induction) — is a recorded
  **pure-optionality** item (decision 2026-08-21): nothing in flight needs it. The Boolean
  frontier (`denote = divstepRev`-style results) never touches amplitudes; the measurement-gadget
  strand needs amplitudes but is blocked on a *different* thing (the gadget is not a permutation,
  so it needs the tensor factorisation `QReg m ≅ QReg 3 ⊗ QReg (m − 3)` — supplied since
  2026-08-22 by `QuantumInfo.regTensorEquiv`, leaving the n-fold hybrid argument itself as the
  open work; the permutation lift would not unblock that either); and the
  documented-count QFT gap needs the *converse* direction on a non-permutation. Build it only
  when a consumer appears or as a Mathlib submission in its own right; if picked up, scope it
  fresh (prior sizing estimates oscillated and are not to be trusted).
* Nothing about non-permutation operations: a mid-circuit measurement gadget is not a basis
  permutation, and lifting one as a local tensor factor of `QReg m` needs the factorisation
  named above, out of scope for this file (see the consumers' scope notes).

## References

`QuantumInfo/Register.lean` (`QReg`, `basisState`); `Reversible/Circuit.lean` (the DSL and
its design note); `Reversible/AndAdd.lean` (`andUncompute`). Application consumers:
`Empirical/QM/MeasurementUncomputeLift.lean` and `Empirical/QM/MeasurementAdder.lean`
(measurement-gadget replacement cost accounting), where these lemmas were first built
(Builds `#31` and `#21`) before extraction here.
-/

@[expose] public section

open scoped Matrix
open QuantumInfo

namespace Reversible

variable {m : ℕ}

/-! ## The column read on `QReg m` -/

/-- A register operator applied to a computational basis state reads off the corresponding
matrix column. -/
lemma toEuclideanLin_basisState_m (A : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (w z : Fin m → Fin 2) :
    Matrix.toEuclideanLin A (basisState w) z = A z w := by
  rw [Matrix.toLpLin_apply]
  show (A *ᵥ (basisState w).ofLp) z = A z w
  simp only [basisState, show (EuclideanSpace.single w (1 : ℂ)).ofLp = Pi.single w 1 from rfl,
    Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul]

/-! ## The fixed three-wire CCX lift (wires `0, 1, 2`) -/

/-- The **CCX permutation on three wires** in the `Fin 2` representation: flip wire `2` iff
wires `0` and `1` are both `1`. On `Fin 2`, "flip by `a ∧ b`" is `+ (w 0 * w 1)`
(`(1 : Fin 2) + 1 = 0`, so a double flip is the identity — `ccx` is an involution). -/
def ccx (w : Fin 3 → Fin 2) : Fin 3 → Fin 2 := Function.update w 2 (w 2 + w 0 * w 1)

/-- **The three-wire CCX as an amplitude unitary**: the permutation matrix of `ccx`,
`andUncompMat z w = [z = ccx w]`. -/
noncomputable def andUncompMat : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  Matrix.of fun z w => if z = ccx w then 1 else 0

lemma andUncompMat_apply (z w : Fin 3 → Fin 2) :
    andUncompMat z w = if z = ccx w then 1 else 0 := rfl

/-- **The unitary permutes basis states by `ccx`**: `toEuclideanLin andUncompMat (basisState w)
= basisState (ccx w)`. Reads off the `w`-th column via `toEuclideanLin_basisState_m`. -/
lemma andUncompMat_apply_basisState (w : Fin 3 → Fin 2) :
    Matrix.toEuclideanLin andUncompMat (basisState w) = basisState (ccx w) := by
  ext z
  rw [toEuclideanLin_basisState_m, andUncompMat_apply, basisState_apply]

/-! ## The `Bool ↔ Fin 2` recast (three wires) -/

/-- Recast a three-wire index (`Fin 3 → Fin 2`) to a Boolean reversible state
(`Fin 3 → Bool`): `a ↦ (a = 1)`. -/
def stateOfB3 (w : Fin 3 → Fin 2) : State 3 := fun i => decide (w i = 1)

/-- Recast a Boolean reversible state back to a three-wire index: `b ↦ if b then 1 else 0`. -/
def b3OfState (s : State 3) : Fin 3 → Fin 2 := fun i => if s i then 1 else 0

/-- `b3OfState ∘ stateOfB3 = id` pointwise: the recast round-trips on a single `Fin 2`
value. -/
lemma b3OfState_decide (a : Fin 2) : (if decide (a = 1) then (1 : Fin 2) else 0) = a := by
  fin_cases a <;> decide

/-- The Boolean AND-uncompute on wires `0,1,2` is a single Toffoli flipping wire `2`:
`denote (andUncompute 0 1 2) s = update s 2 (s 2 ⊕ (s 0 ∧ s 1))`. -/
lemma denote_andUncompute_012 (s : State 3) :
    denote (andUncompute 0 1 2) s
      = Function.update s 2 (s 2 ^^ (s 0 && s 1)) := by
  show denoteGate (Gate.CCX 0 1 2) s = _
  simp only [denoteGate, if_neg (show ¬((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) by decide)]

/-- **The Boolean ↔ Fin 2 link.** `ccx` is exactly the recast of the Boolean
`denote (andUncompute 0 1 2)`: the `Fin 2` permutation and the Boolean Toffoli agree
wire-by-wire under `stateOfB3` / `b3OfState`. *Computed*, not asserted — the target wire is
the genuine `g + a*b = [decide g ⊕ (decide a ∧ decide b)]` content (`ccx_index2`), the other
wires round-trip (`b3OfState_decide`). -/
lemma ccx_eq_denote_recast (w : Fin 3 → Fin 2) :
    ccx w = b3OfState (denote (andUncompute 0 1 2) (stateOfB3 w)) := by
  have ccx_index2 : ∀ a b g : Fin 2,
      g + a * b
        = (if (decide (g = 1) ^^ (decide (a = 1) && decide (b = 1))) then (1 : Fin 2) else 0) := by
    intro a b g; fin_cases a <;> fin_cases b <;> fin_cases g <;> decide
  rw [denote_andUncompute_012]
  funext i
  simp only [ccx, b3OfState, stateOfB3, Function.update_apply]
  by_cases h : i = 2
  · subst h
    rw [if_pos (rfl : (2 : Fin 3) = 2), if_pos (rfl : (2 : Fin 3) = 2)]
    exact ccx_index2 (w 0) (w 1) (w 2)
  · simp only [if_neg h]
    exact (b3OfState_decide (w i)).symm

/-- **The three-wire gate lift.** The unitary `andUncompMat` acts on computational basis
states **exactly as the Boolean `denote (andUncompute 0 1 2)` permutation**, modulo the
explicit `Bool ↔ Fin 2` recast of the three wires:

  `toEuclideanLin andUncompMat (basisState w) = basisState (recast (denote (andUncompute 0 1 2)
  (recast w)))`.

It is *computed* (`andUncompMat_apply_basisState` + `ccx_eq_denote_recast`), not asserted. -/
theorem andUncompMat_lifts_denote (w : Fin 3 → Fin 2) :
    Matrix.toEuclideanLin andUncompMat (basisState w)
      = basisState (b3OfState (denote (andUncompute 0 1 2) (stateOfB3 w))) := by
  rw [andUncompMat_apply_basisState, ccx_eq_denote_recast]

/-! ## The arbitrary-wire CCX lift on `QReg m` -/

/-- **The full-register CCX permutation** at wires `(wa, wb, wg)`: flip wire `wg` by
`wa ∧ wb` (`+ w wa * w wb` on `Fin 2`). The width-`m`, arbitrary-wire generalization of
`ccx`. -/
def ccxAt (wa wb wg : Fin m) (w : Fin m → Fin 2) : Fin m → Fin 2 :=
  Function.update w wg (w wg + w wa * w wb)

/-- **The CCX amplitude unitary on `QReg m`**: the permutation matrix of `ccxAt`. A genuine
permutation matrix on the full register (identity off `wg`) — the local unitary of one CCX
at arbitrary wires. -/
noncomputable def ccxAtMat (wa wb wg : Fin m) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  Matrix.of fun z w => if z = ccxAt wa wb wg w then 1 else 0

lemma ccxAtMat_apply (wa wb wg : Fin m) (z w : Fin m → Fin 2) :
    ccxAtMat wa wb wg z w = if z = ccxAt wa wb wg w then 1 else 0 := rfl

/-- The unitary permutes basis states by `ccxAt`. -/
lemma ccxAtMat_apply_basisState (wa wb wg : Fin m) (w : Fin m → Fin 2) :
    Matrix.toEuclideanLin (ccxAtMat wa wb wg) (basisState w) = basisState (ccxAt wa wb wg w) := by
  ext z
  rw [toEuclideanLin_basisState_m, ccxAtMat_apply, basisState_apply]

/-- Recast a `QReg m` index to a Boolean reversible state (`a ↦ (a = 1)`). -/
def stateOfReg (w : Fin m → Fin 2) : State m := fun i => decide (w i = 1)

/-- Recast a Boolean reversible state back to a `QReg m` index (`b ↦ if b then 1 else 0`). -/
def regOfState (s : State m) : Fin m → Fin 2 := fun i => if s i then 1 else 0

/-- The Boolean AND-uncompute on wires `wa, wb, wg` (with `wg` distinct from the controls)
is a single Toffoli flipping wire `wg`. The arbitrary-wire generalization of
`denote_andUncompute_012`. -/
lemma denote_andUncompute (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb)
    (s : State m) :
    denote (andUncompute wa wb wg) s
      = Function.update s wg (s wg ^^ (s wa && s wb)) := by
  show denoteGate (Gate.CCX wa wb wg) s = _
  simp only [denoteGate, if_neg (not_or.mpr ⟨hga, hgb⟩)]

/-- **The Boolean ↔ `Fin 2` link, arbitrary wires.** `ccxAt` is the recast of the Boolean
`denote (andUncompute wa wb wg)`: the full-register `Fin 2` permutation and the Boolean
Toffoli agree wire-by-wire under `stateOfReg` / `regOfState`. *Computed*, not asserted (the
target wire is the genuine `g + a*b` content; the others round-trip via
`b3OfState_decide`). -/
lemma ccxAt_eq_denote_recast (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb)
    (w : Fin m → Fin 2) :
    ccxAt wa wb wg w
      = regOfState (denote (andUncompute wa wb wg) (stateOfReg w)) := by
  have hidx : ∀ a b g : Fin 2,
      g + a * b
        = (if (decide (g = 1) ^^ (decide (a = 1) && decide (b = 1))) then (1 : Fin 2) else 0) := by
    intro a b g; fin_cases a <;> fin_cases b <;> fin_cases g <;> decide
  rw [denote_andUncompute wa wb wg hga hgb]
  funext i
  simp only [ccxAt, regOfState, stateOfReg, Function.update_apply]
  by_cases h : i = wg
  · subst h
    rw [if_pos rfl, if_pos rfl]
    exact hidx (w wa) (w wb) (w i)
  · simp only [if_neg h]
    exact (b3OfState_decide (w i)).symm

/-- **The arbitrary-wire gate lift on `QReg m`.** The full-register unitary `ccxAtMat` acts
on computational basis states **exactly as the Boolean `denote (andUncompute wa wb wg)`
permutation**, modulo the `Bool ↔ Fin 2` recast — for arbitrary wires `wa, wb, wg` of any
width `m` (with `wg` distinct from the controls). Generalizes the fixed-wire
`andUncompMat_lifts_denote` off the `0,1,2` wires: the per-gate **unitary** embedding into
the full register is sound at any width. -/
theorem ccxAtMat_lifts_denote (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb)
    (w : Fin m → Fin 2) :
    Matrix.toEuclideanLin (ccxAtMat wa wb wg) (basisState w)
      = basisState
          (regOfState (denote (andUncompute wa wb wg) (stateOfReg w))) := by
  rw [ccxAtMat_apply_basisState, ccxAt_eq_denote_recast wa wb wg hga hgb]

end Reversible
