import CsdLean4.Empirical.QM.MeasurementUncomputeLift

/-!
# Measurement-based AND-adder re-cost  (Build #21, L5-d)

**Category:** 3-Local (QM-validity content; no CSD ontology).

This file delivers the **adder-level Toffoli re-count** of the AND-based ripple adder
(`Mathlib/QuantumInfo/Reversible/AndAdd.lean`, `#30`) obtained by replacing each of its reverse-pass
AND-uncompute CCX Toffolis with the **measurement gadget** (`gadgetGateList`,
`Empirical/QM/MeasurementUncompute.lean`, `0` Toffoli), whose per-block equivalence to the unitary
AND-uncompute is the **proven** content of `#31` (`Empirical/QM/MeasurementUncomputeLift.lean`,
`andUncompute_measureUncompute_same_data` / `andUncompute_measurement_saving`).

The CSD anti-hollow-cost ethos is binding: the saving is **not** a count over an unverified swap. It
aggregates `numUncomputeBlocks L` (= `3n`) per-block `#31` replacements, each a `1 → 0` Toffoli swap on
a block **proven** to have the same data effect (`andUncompute_measurement_saving`). The Part-1 closed
form is *derived* from those per-block lemmas (`measUncomputeGadgets_toffoli` routes through
`gadgetBlockToffoli_eq_zero`, which is literally `#31`'s second conjunct), not asserted independently.

## The exact pre-replacement count (decision-relevant finding)

The `#30` adder is `andForward L ++ andSumPass L ++ inverse (andForward L)`. Its reverse pass
`inverse (andForward L)` carries **`3n`** AND-uncompute CCX Toffolis, NOT `n`: each of the `n` carry
bits uses a 3-Toffoli *preserving-majority* cell (`andCarryCell`), so the reverse pass has `3`
AND-uncompute blocks per carry bit (`andAdd_uncompute_toffoli : … = 3 * n`). Each block is a single
`Reversible.andUncompute`-shaped CCX, so `#31`'s per-block lemma applies to every one.

## Part 1 — the Toffoli count (the deliverable)

* **before** (`#30`): `andAdd_toffoli_eq : (circuitCost (andAdd L)).toffoli = 6 * n`
  (`3n` compute + `3n` uncompute; sum pass CNOT-only).
* **after** (this file): `measAddToffoli_eq : measAddToffoli L = 3 * n`
  (forward kept; the `3n` AND-uncompute Toffolis become `3n` gadgets, each `0` Toffoli).
* **saving**: `measAdd_toffoli_savings_eq : (circuitCost (andAdd L)).toffoli - measAddToffoli L = 3 * n`
  and the first-class before/after form `measAdd_toffoli_saving : before = after + numUncomputeBlocks L`.
* **at `n = 256`** (`measAdd_toffoli_256`): before `1536`, after `768`, saving `768` (a 2× reduction).

## Part 2 — the correctness anchor (so the count is not hollow)

* MUST-HAVE: `measAdd_saving_aggregates` — the saving is `numUncomputeBlocks L` (= `3n`) times the
  per-block `#31` saving `(circuitCost (andUncompute a b g)).toffoli - gadgetBlockToffoli = 1`
  (`perBlock_saving`, from `andUncompute_measurement_saving`). The count provably aggregates `3n`
  proven-equivalent block replacements.
* STRETCH (single carry, unitary side done; gadget n-fold amplitude WALLED): `ccxAtMat_lifts_denote`
  lifts a **single** AND-uncompute CCX block into the full register `QReg m` as the permutation matrix
  `ccxAtMat`, generalizing `#31`'s fixed-wire (`0,1,2`) `B3` lift to arbitrary wires of any width.
  This shows the per-block **unitary** embedding into the full register is **not** the obstruction.

  **The wall (precise, decision-relevant).** The genuine gadget hybrid — replacing one AND-uncompute
  by the *measurement gadget* and proving the full-register data output on `S` unchanged — walls at
  the tensor factor. The gadget is **not** a permutation: `measureUncompute_uncomputes` sends the
  AND-shaped block state `Σ c_{xy}|x,y,x∧y⟩` to `(√2)⁻¹ • Σ c_{xy}|x,y,m⟩` (a `(√2)⁻¹` scalar plus
  an ancilla reset to the outcome `m`). So the clean "basis-state ↦ basis-state" induction that lifts
  unitary permutation circuits (and underlies `ccxAtMat_lifts_denote`) **breaks at the replaced
  block**: the post-gadget full-register state is no longer a basis-state permutation of the input.
  Applying the gadget as a *local tensor factor* `measureUncompute ⊗ I` to a general entangled
  full-register superposition requires the factorization `QReg m ≅ QReg 3 ⊗ QReg (m−3)`, which
  Mathlib's `EuclideanSpace` tensor API does not cleanly provide. The single-block unitary embedding
  is sound; the *non-permutation gadget* tensor-factor on a general superposition is the obstruction.

## Honest scope (Part 3)

This is an **adder-level** re-cost on proven-equivalent blocks. **No ECDSA score change is claimed.**
The ECDSA score requires (i) swapping the corpus point-addition's adders (Cuccaro, in-place) for
AND-based adders throughout the curve arithmetic, AND (ii) the harness step `#7` — **neither is done
here**. The Part-1 count is exact and the Part-2 anchor proves it aggregates `3n` `#31`-equivalent
blocks (so the count is *not* hollow); the full n-fold amplitude state-equality of the hybrid adder is
**WALLED** at the `QReg 3 ⊗ QReg (m−3)` tensor factor, as stated above and reported.
-/

open scoped Matrix
open QuantumInfo
open Reversible

namespace CSD.Empirical.QM

variable {m n : ℕ}

/-! ## Part 1 — the measurement-based re-cost -/

/-- **The per-block measurement-gadget Toffoli cost (`= 0`).** The Toffoli total of one
`gadgetGateList` (Hadamard + measurement + conditional CZ). It is `#31`'s second conjunct
(`andUncompute_measurement_saving`), the proven-equivalent Toffoli-free replacement. -/
def gadgetBlockToffoli : ℕ := (gadgetGateList.map (fun g => (gadgetGateCost g).toffoli)).sum

/-- `gadgetBlockToffoli = 0`, extracted from `#31`'s `andUncompute_measurement_saving` (the gadget
Toffoli count is wire-independent; any width witness gives it). -/
theorem gadgetBlockToffoli_eq_zero : gadgetBlockToffoli = 0 :=
  (andUncompute_measurement_saving (0 : Fin 1) 0 0).2

/-- **The number of AND-uncompute blocks in the `#30` reverse pass.** It is the Toffoli count of
`inverse (andForward L)`, namely `3n` (`3` per carry bit, `n` bits); each block is a single
`Reversible.andUncompute`-shaped CCX replaced by the measurement gadget. -/
def numUncomputeBlocks (L : AndAddLayout m n) : ℕ := (circuitCost (inverse (andForward L))).toffoli

/-- `numUncomputeBlocks L = 3 * n` (`#30` `andAdd_uncompute_toffoli`). -/
theorem numUncomputeBlocks_eq (L : AndAddLayout m n) : numUncomputeBlocks L = 3 * n :=
  andAdd_uncompute_toffoli L

/-- **Aggregating `k` gadget blocks.** The Toffoli total of `k` concatenated copies of any gate list
`l` is `k` times the per-copy total — the elementary accounting behind "replace each block by a
proven-equivalent gadget and sum". -/
lemma replicate_flatten_map_sum (k : ℕ) (l : List GadgetGate) (f : GadgetGate → ℕ) :
    (((List.replicate k l).flatten).map f).sum = k * (l.map f).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [List.flatten_cons, List.map_append, List.sum_append, ih]
    ring

/-- **The measurement-based uncompute pass is Toffoli-free.** Replacing every one of the
`numUncomputeBlocks L` reverse-pass AND-uncompute CCX Toffolis by the gadget (`gadgetGateList`)
gives `numUncomputeBlocks L` copies of a `0`-Toffoli block, total `0`. Derived: the `k`-fold
aggregation (`replicate_flatten_map_sum`) times the per-block `0` (`gadgetBlockToffoli_eq_zero`,
i.e. `#31`'s saving). -/
theorem measUncomputeGadgets_toffoli (L : AndAddLayout m n) :
    (((List.replicate (numUncomputeBlocks L) gadgetGateList).flatten).map
        (fun g => (gadgetGateCost g).toffoli)).sum = 0 := by
  rw [replicate_flatten_map_sum]
  show numUncomputeBlocks L * gadgetBlockToffoli = 0
  rw [gadgetBlockToffoli_eq_zero, mul_zero]

/-- **The measurement-based adder's Toffoli count.** The forward AND-compute pass keeps its Toffolis,
the sum pass is CNOT-only, and each of the `numUncomputeBlocks L` reverse-pass AND-uncompute Toffolis
becomes a measurement gadget (`gadgetGateList`, `0` Toffoli). The third summand is the Toffoli total of
those `numUncomputeBlocks L` gadget blocks — so the count is, by construction, the aggregate of the
per-block replacements. -/
def measAddToffoli (L : AndAddLayout m n) : ℕ :=
  (circuitCost (andForward L)).toffoli
  + (circuitCost (andSumPass L)).toffoli
  + (((List.replicate (numUncomputeBlocks L) gadgetGateList).flatten).map
      (fun g => (gadgetGateCost g).toffoli)).sum

/-- **Part-1 closed form (after): `measAddToffoli L = 3 * n`.** Forward `3n` (`andForwardPrefix_toffoli`)
`+` sum `0` (`andSumPrefix_toffoli`) `+` uncompute `0` (`measUncomputeGadgets_toffoli`). The uncompute
Toffolis vanish; the forward half survives. -/
theorem measAddToffoli_eq (L : AndAddLayout m n) : measAddToffoli L = 3 * n := by
  unfold measAddToffoli
  rw [measUncomputeGadgets_toffoli]
  simp only [andForward, andSumPass]
  rw [andForwardPrefix_toffoli, andSumPrefix_toffoli]
  omega

/-- **Part-1 closed form (before): `(circuitCost (andAdd L)).toffoli = 6 * n`** (re-export of `#30`
`andAdd_toffoli`: `3n` compute `+` `3n` uncompute). -/
theorem andAdd_toffoli_eq (L : AndAddLayout m n) : (circuitCost (andAdd L)).toffoli = 6 * n :=
  andAdd_toffoli L

/-- **The saving, before/after first-class form.** The `#30` total equals the measurement-based total
plus the saved Toffolis, which are exactly the `numUncomputeBlocks L` (= `3n`) uncompute Toffolis the
gadget eliminates: `before = after + numUncomputeBlocks L`. -/
theorem measAdd_toffoli_saving (L : AndAddLayout m n) :
    (circuitCost (andAdd L)).toffoli = measAddToffoli L + numUncomputeBlocks L := by
  rw [andAdd_toffoli, measAddToffoli_eq, numUncomputeBlocks_eq]; omega

/-- **The saving as a closed form: `before − after = 3 * n`.** -/
theorem measAdd_toffoli_savings_eq (L : AndAddLayout m n) :
    (circuitCost (andAdd L)).toffoli - measAddToffoli L = 3 * n := by
  rw [andAdd_toffoli, measAddToffoli_eq]; omega

/-- **Explicit numbers at `n = 256`.** Before `1536` (`6·256`), after `768` (`3·256`), saving `768`
(a 2× Toffoli reduction). -/
theorem measAdd_toffoli_256 (L : AndAddLayout m 256) :
    (circuitCost (andAdd L)).toffoli = 1536
      ∧ measAddToffoli L = 768
      ∧ (circuitCost (andAdd L)).toffoli - measAddToffoli L = 768 := by
  rw [andAdd_toffoli, measAddToffoli_eq]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ## Part 2 — the correctness anchor -/

/-- **The per-block `#31` saving.** Each reverse-pass AND-uncompute is one CCX (`1` Toffoli,
`andCell_uncompute_toffoli`); its measurement-gadget replacement is `0` Toffoli (`gadgetBlockToffoli`).
So the per-block saving is `1 − 0 = 1` Toffoli on a block **proven** to have the same data effect
(`andUncompute_measureUncompute_same_data`). This is `#31`'s `andUncompute_measurement_saving`, in
subtraction form. -/
theorem perBlock_saving {k : ℕ} (a b g : Fin k) :
    (circuitCost (Reversible.andUncompute a b g)).toffoli - gadgetBlockToffoli = 1 := by
  obtain ⟨h1, _⟩ := andUncompute_measurement_saving a b g
  rw [h1, gadgetBlockToffoli_eq_zero]

/-- **Compositional anchor (the count is not hollow).** The total Toffoli saving equals the number of
reverse-pass AND-uncompute blocks (`numUncomputeBlocks L = 3n`) times the per-block `#31` saving
(`perBlock_saving`, `1` Toffoli on a proven-equivalent block). So the re-cost is the *sum over the `3n`
carries' AND-uncompute blocks of the `#31` per-block replacement*, not a count over an unverified
swap. -/
theorem measAdd_saving_aggregates (L : AndAddLayout m n) (a b g : Fin m) :
    (circuitCost (andAdd L)).toffoli - measAddToffoli L
      = numUncomputeBlocks L
          * ((circuitCost (Reversible.andUncompute a b g)).toffoli - gadgetBlockToffoli) := by
  rw [measAdd_toffoli_savings_eq, perBlock_saving, mul_one, numUncomputeBlocks_eq]

/-! ## Part 2 (stretch) — the single-block unitary lift into the full register `QReg m`

The `#31` lift was done in `B3 = Fin 3 → Fin 2` on the fixed wires `0,1,2`. Here it is generalized to
**arbitrary wires of any width `m`** (`QReg m = EuclideanSpace ℂ (Fin m → Fin 2)`), showing the
per-block **unitary** embedding into the full register is not the obstruction. The wall is the
non-permutation *measurement gadget* tensor-factor, documented in the module header. -/

/-- General `toEuclideanLin` column read on `QReg m` (the `#31` `toEuclideanLin_basisState`, off `B3`):
a register operator applied to a basis state reads off the corresponding matrix column. -/
lemma toEuclideanLin_basisState_m (A : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (w z : Fin m → Fin 2) :
    Matrix.toEuclideanLin A (basisState w) z = A z w := by
  rw [Matrix.toLpLin_apply]
  show (A *ᵥ (basisState w).ofLp) z = A z w
  simp only [basisState, show (EuclideanSpace.single w (1 : ℂ)).ofLp = Pi.single w 1 from rfl,
    Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul]

/-- **The full-register CCX permutation** at wires `(wa, wb, wg)`: flip wire `wg` by `wa ∧ wb`
(`+ w wa * w wb` on `Fin 2`). The width-`m`, arbitrary-wire generalization of `#31`'s `ccx`. -/
def ccxAt (wa wb wg : Fin m) (w : Fin m → Fin 2) : Fin m → Fin 2 :=
  Function.update w wg (w wg + w wa * w wb)

/-- **The single-block amplitude unitary on `QReg m`**: the permutation matrix of `ccxAt`. A genuine
permutation matrix on the full register (identity off `wg`), the local tensor factor of one
AND-uncompute CCX — no `B3`, no `Fin 8` reindex. -/
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
def stateOfReg (w : Fin m → Fin 2) : Reversible.State m := fun i => decide (w i = 1)

/-- Recast a Boolean reversible state back to a `QReg m` index (`b ↦ if b then 1 else 0`). -/
def regOfState (s : Reversible.State m) : Fin m → Fin 2 := fun i => if s i then 1 else 0

/-- The Boolean AND-uncompute on wires `wa, wb, wg` (with `wg` distinct from the controls) is a single
Toffoli flipping wire `wg`. The arbitrary-wire generalization of `#31`'s `denote_andUncompute_012`. -/
lemma denote_andUncompute (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb)
    (s : Reversible.State m) :
    Reversible.denote (Reversible.andUncompute wa wb wg) s
      = Function.update s wg (s wg ^^ (s wa && s wb)) := by
  show Reversible.denoteGate (Reversible.Gate.CCX wa wb wg) s = _
  simp only [Reversible.denoteGate, if_neg (not_or.mpr ⟨hga, hgb⟩)]

/-- **The Boolean ↔ `Fin 2` link, arbitrary wires.** `ccxAt` is the recast of the Boolean
`denote (andUncompute wa wb wg)`: the full-register `Fin 2` permutation and the Boolean Toffoli agree
wire-by-wire under `stateOfReg` / `regOfState`. *Computed*, not asserted (the ancilla wire is the
genuine `g + a*b` content; the others round-trip via `b3OfState_decide`). -/
lemma ccxAt_eq_denote_recast (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb)
    (w : Fin m → Fin 2) :
    ccxAt wa wb wg w
      = regOfState (Reversible.denote (Reversible.andUncompute wa wb wg) (stateOfReg w)) := by
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

/-- **The single-block unitary amplitude lift into `QReg m` (the stretch deliverable).** The
full-register unitary `ccxAtMat` acts on computational basis states **exactly as the Boolean
`denote (andUncompute wa wb wg)` permutation**, modulo the `Bool ↔ Fin 2` recast — for arbitrary wires
`wa, wb, wg` of any width `m` (with `wg` distinct from the controls). This generalizes `#31`'s
fixed-wire `B3` lift `andUncompMat_lifts_denote` off the `0,1,2` wires and off `B3`, showing the
per-block **unitary** embedding into the full register is sound (NOT the obstruction).

The genuine gadget hybrid — the *measurement gadget* replacement and the full-register `S`-output
equality — walls at the `QReg m ≅ QReg 3 ⊗ QReg (m−3)` tensor factor, because the gadget is not a
permutation; see the module header. -/
theorem ccxAtMat_lifts_denote (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb)
    (w : Fin m → Fin 2) :
    Matrix.toEuclideanLin (ccxAtMat wa wb wg) (basisState w)
      = basisState
          (regOfState (Reversible.denote (Reversible.andUncompute wa wb wg) (stateOfReg w))) := by
  rw [ccxAtMat_apply_basisState, ccxAt_eq_denote_recast wa wb wg hga hgb]

/-! ## Non-vacuity witness -/

/-- The headlines are non-vacuous: on the concrete `#30` 2-bit layout (`Fin 9`) the before count is
`6·2 = 12`, the after count `3·2 = 6`, and the saving `6`. -/
example : (circuitCost (andAdd Reversible.andAddLayout2)).toffoli = 12
    ∧ measAddToffoli Reversible.andAddLayout2 = 6
    ∧ (circuitCost (andAdd Reversible.andAddLayout2)).toffoli
        - measAddToffoli Reversible.andAddLayout2 = 6 := by
  rw [andAdd_toffoli, measAddToffoli_eq]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

end CSD.Empirical.QM
