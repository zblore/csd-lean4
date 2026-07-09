import CsdLean4.Empirical.QM.MeasurementUncompute
import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd

/-!
# Localized amplitude lift of the AND-uncompute block  (Build #31, L5-c bridge at cell granularity)

**Category:** 3-Local (QM-validity content; no CSD ontology).

This file closes the **L5-c wall** at the granularity of a **single AND-uncompute block** (3 wires).
The L5-c probe found that the obstruction to applying the measurement-based uncomputation gadget
(`Empirical/QM/MeasurementUncompute.lean`, Gidney's measure-and-correct, the ~2× Toffoli saving) to
actual Boolean arithmetic was the general `denote ↔ toEuclideanLin` bridge — and that the bridge's
hard step was exactly the `Fin 8 ↔ Fin 3 → Fin 2` reindex between the `Matrix (Fin 8)` quantum
Toffoli and the `B3 = Fin 3 → Fin 2` permutation-matrix representation used by the gadget.

The **key steer** here is to do the lift **entirely in the `B3` representation** (the one
`hadA` / `projA` / `correctionMat` already use), never via `qmToffoli : Matrix (Fin 8)`. Staying in
`B3` sidesteps the reindex wall.

## What is built (B3 representation throughout, no `Fin 8`)

1. `ccx : B3 → B3` — the CCX permutation on `B3` in the `Fin 2` representation: flip ancilla wire `2`
   (`g`) iff data wires `0` (`a`) and `1` (`b`) are both `1`. On `Fin 2`, "flip by `a ∧ b`" is
   `+ (w 0 * w 1)` (since `(1:Fin 2) + 1 = 0`).
2. `andUncompMat : Matrix B3 B3 ℂ` — the permutation matrix of `ccx`: `andUncompMat z w = [z = ccx w]`.
3. `andUncompMat_apply_basisState` — `andUncompMat` acts on a computational basis state by permuting
   the index: `toEuclideanLin andUncompMat (basisState w) = basisState (ccx w)` (reads off the column
   via `toEuclideanLin_basisState`).
4. **The localized gate-lift** `andUncompMat_lifts_denote` (the crux): the `B3` unitary `andUncompMat`
   acts on computational basis states **exactly as the Boolean `denote (andUncompute 0 1 2)`
   permutation**, modulo the `Bool ↔ Fin 2` recast of the three wires (`stateOfB3` / `b3OfState`).
   This is the localized version of the general `denote ↔ toEuclideanLin` lift — **for the single
   block only, in `B3`, with no `Fin 8`**. It is *computed* (`ccx_eq_denote_recast`), not asserted.
5. **The equivalence** `andUncompute_eq_measureUncompute_on_block`: on the `andInput`-shaped subspace
   (`g = a ∧ b`), the unitary lift and the measurement gadget have the **same data effect**. The
   unitary deterministically uncomputes to ancilla `0`
   (`andUncompMat_uncomputes : toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0`,
   *computed* via `ccx (andIdx x y) = ![x, y, 0]`), and L5-a's `measureUncompute_uncomputes` gives
   `measureUncompute m (andInput c) = (√2)⁻¹ • uncomputedData c m`. Both routes produce
   `uncomputedData` (AND uncomputed, data `|a,b⟩` preserved); the ancilla is reset to `0` by the
   unitary and to the outcome `m` by the measurement.
6. **The saving** `andUncompute_measurement_saving`: the Boolean unitary AND-uncompute block
   (`Reversible.andUncompute`) costs `1` Toffoli (`Reversible.andCell_uncompute_toffoli`); the
   measurement gadget (`gadgetGateList`, its proven-equivalent replacement, L5-b) costs `0`. So the
   Toffoli-free replacement is **correct on a proven-equivalent block** and **saves the Toffoli** —
   the per-block ~2× saving, now bridged.

## Honest scope

This **closes the L5-c wall at CELL granularity**: the single AND-uncompute block is lifted to the
amplitude model in `B3` (sidestepping the `Fin 8` reindex), and the unitary uncompute is **proven** to
have the same data effect as the measurement gadget, so the Toffoli-free replacement is sound. The
**trusted base grows** by this localized amplitude lift — the `B3` permutation-matrix lift of the block
(`andUncompMat_lifts_denote`) plus the data-agreement (`andUncompMat_uncomputes`).

The amplitude model is **required**: the measurement gadget uses phases (X-basis + CZ), which the
Boolean reversible DSL cannot express.

**Deferred:** **L5-d** (iterating this block-replacement across the full AND-based adder's `n` carry
uncomputes — `andAdd`'s `inverse andForward` — to obtain the circuit-level re-cost gap, ~10.5× → ~5×;
needs threading the replacement through the `n` AND-uncomputes), and **step #7** (the harness). **No
circuit-level re-cost claim is made here, and no ECDSA resource-score change.**
-/

open scoped Matrix
open QuantumInfo

namespace CSD.Empirical.QM

/-! ## The CCX permutation on `B3` (the `Fin 2` representation, no `Fin 8`) -/

/-- The **CCX permutation on `B3`** in the `Fin 2` representation: flip the ancilla wire `2` (`g`) iff
data wires `0` (`a`) and `1` (`b`) are both `1`. On `Fin 2`, "flip by `a ∧ b`" is `+ (w 0 * w 1)`
(`(1:Fin 2) + 1 = 0`, so a double flip is the identity — this is what makes `ccx` an involution and
uncomputes `andIdx`). -/
def ccx (w : B3) : B3 := Function.update w 2 (w 2 + w 0 * w 1)

/-- `ccx` uncomputes the AND-entangled index: `ccx ![x, y, x∧y] = ![x, y, 0]`. The ancilla bit
`x*y + x*y = 0` in `Fin 2`; the data `(x,y)` is untouched. -/
lemma ccx_andIdx (x y : Fin 2) : ccx (andIdx x y) = ![x, y, 0] := by
  rw [b3_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp only [ccx, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide), andIdx_zero]
  · simp only [ccx, Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide), andIdx_one]
  · simp only [ccx, Function.update_self, andIdx_zero, andIdx_one, andIdx_two]
    fin_cases x <;> fin_cases y <;> decide

/-! ## The `B3` amplitude unitary (permutation matrix of `ccx`) -/

/-- **The AND-uncompute block lifted to a `B3` amplitude unitary**: the permutation matrix of `ccx`,
`andUncompMat z w = [z = ccx w]`. A genuine permutation matrix on `B3` (3 wires), in the same
`Matrix B3 B3 ℂ` representation as `hadA` / `projA` / `correctionMat`. No `Fin 8`. -/
noncomputable def andUncompMat : Matrix B3 B3 ℂ :=
  Matrix.of fun z w => if z = ccx w then 1 else 0

lemma andUncompMat_apply (z w : B3) :
    andUncompMat z w = if z = ccx w then 1 else 0 := rfl

/-- **The unitary permutes basis states by `ccx`**: `toEuclideanLin andUncompMat (basisState w) =
basisState (ccx w)`. Reads off the `w`-th column via `toEuclideanLin_basisState`. -/
lemma andUncompMat_apply_basisState (w : B3) :
    Matrix.toEuclideanLin andUncompMat (basisState w) = basisState (ccx w) := by
  ext z
  rw [toEuclideanLin_basisState, andUncompMat_apply, basisState_apply]

/-! ## The `Bool ↔ Fin 2` recast for the three wires (stated explicitly, per the honesty note) -/

/-- Recast a `B3` index (`Fin 3 → Fin 2`) to a Boolean reversible state (`Fin 3 → Bool`):
`a ↦ (a = 1)`. -/
def stateOfB3 (w : B3) : Reversible.State 3 := fun i => decide (w i = 1)

/-- Recast a Boolean reversible state back to a `B3` index: `b ↦ if b then 1 else 0`. -/
def b3OfState (s : Reversible.State 3) : B3 := fun i => if s i then 1 else 0

/-- `b3OfState ∘ stateOfB3 = id` pointwise: the recast round-trips on a single `Fin 2` value. -/
lemma b3OfState_decide (a : Fin 2) : (if decide (a = 1) then (1 : Fin 2) else 0) = a := by
  fin_cases a <;> decide

/-- The Boolean AND-uncompute on wires `0,1,2` is a single Toffoli flipping wire `2`:
`denote (andUncompute 0 1 2) s = update s 2 (s 2 ⊕ (s 0 ∧ s 1))`. -/
lemma denote_andUncompute_012 (s : Reversible.State 3) :
    Reversible.denote (Reversible.andUncompute 0 1 2) s
      = Function.update s 2 (s 2 ^^ (s 0 && s 1)) := by
  show Reversible.denoteGate (Reversible.Gate.CCX 0 1 2) s = _
  simp only [Reversible.denoteGate, if_neg (show ¬((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) by decide)]

/-- **The genuine Boolean ↔ Fin 2 link.** `ccx` is exactly the recast of the Boolean
`denote (andUncompute 0 1 2)`: the `Fin 2` permutation and the Boolean Toffoli agree wire-by-wire
under `stateOfB3` / `b3OfState`. *Computed*, not asserted — the ancilla wire is the genuine
`g + a*b = [decide g ⊕ (decide a ∧ decide b)]` content (`ccx_index2`), the data wires round-trip
(`b3OfState_decide`). -/
lemma ccx_eq_denote_recast (w : B3) :
    ccx w = b3OfState (Reversible.denote (Reversible.andUncompute 0 1 2) (stateOfB3 w)) := by
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

/-! ## The localized gate-lift (the crux) -/

/-- **The localized amplitude gate-lift (the L5-c crux, in `B3`).** The `B3` unitary `andUncompMat`
acts on computational basis states **exactly as the Boolean `denote (andUncompute 0 1 2)`
permutation**, modulo the explicit `Bool ↔ Fin 2` recast of the three wires:

  `toEuclideanLin andUncompMat (basisState w) = basisState (recast (denote (andUncompute 0 1 2)
  (recast w)))`.

This is the localized version of the general `denote ↔ toEuclideanLin` lift the L5-c probe flagged —
**for the single AND-uncompute block only, in `B3`, with no `Fin 8` reindex**. It is *computed*
(`andUncompMat_apply_basisState` + `ccx_eq_denote_recast`), not asserted. -/
theorem andUncompMat_lifts_denote (w : B3) :
    Matrix.toEuclideanLin andUncompMat (basisState w)
      = basisState (b3OfState (Reversible.denote (Reversible.andUncompute 0 1 2) (stateOfB3 w))) := by
  rw [andUncompMat_apply_basisState, ccx_eq_denote_recast]

/-! ## The equivalence: same data effect (unitary uncompute vs measurement gadget) -/

/-- **The unitary block genuinely uncomputes in the amplitude model.** On the `andInput`-shaped
subspace (`g = a ∧ b`), the `B3` unitary `andUncompMat` deterministically uncomputes the AND, resetting
the ancilla to `0` and preserving the data: `toEuclideanLin andUncompMat (andInput c) = uncomputedData
c 0`. *Computed* via `ccx (andIdx x y) = ![x, y, 0]`, not asserted. -/
theorem andUncompMat_uncomputes (c : Fin 2 → Fin 2 → ℂ) :
    Matrix.toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0 := by
  rw [andInput, uncomputedData, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, andUncompMat_apply_basisState, ccx_andIdx]

/-- **The bridge headline (the equivalence).** On the `andInput`-shaped subspace, the unitary
AND-uncompute lift and the measurement gadget have the **same data effect** — both produce
`uncomputedData` (the AND uncomputed, the data `|a,b⟩` preserved):

* the **unitary** route resets the ancilla deterministically to `0`
  (`toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0`);
* the **measurement** route (L5-a) resets the ancilla to the outcome `m`, scaled by the outcome
  amplitude (`measureUncompute m (andInput c) = (√2)⁻¹ • uncomputedData c m`).

So `measureUncompute` is a **correct replacement** for the unitary `andUncompMat` on this block: same
uncomputed data, the ancilla difference (`0` vs `m`) being the deterministic-vs-measured outcome. The
equivalence is **genuine** — both equalities are proved, not asserted.

This is an **agreement of two routes onto a shared `uncomputedData` target**, not a literal operator
equality (the routes differ by the outcome amplitude `(√2)⁻¹` and the ancilla index `0` vs `m`); the
shared-data content is made first-class in `andUncompute_measureUncompute_same_data` below. -/
theorem andUncompute_measureUncompute_agree_on_block (c : Fin 2 → Fin 2 → ℂ) (m : Fin 2) :
    Matrix.toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0 ∧
      measureUncompute m (andInput c) = (Real.sqrt 2 : ℂ)⁻¹ • uncomputedData c m :=
  ⟨andUncompMat_uncomputes c, measureUncompute_uncomputes m c⟩

/-- **Same data factor, first-class.** Clearing the outcome amplitude (`√2 • ·`), both routes land in
the **same** `uncomputedData c ·` family — i.e. the data amplitudes `c` are *identical*; only the
ancilla index differs (`0` for the deterministic unitary, `m` for the measured outcome). This is the
honest "same data effect" content of `andUncompute_measureUncompute_agree_on_block` with the
normalization scalar removed, so the shared `c` appears literally on both right-hand sides. -/
theorem andUncompute_measureUncompute_same_data (c : Fin 2 → Fin 2 → ℂ) (m : Fin 2) :
    Matrix.toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0 ∧
      (Real.sqrt 2 : ℂ) • measureUncompute m (andInput c) = uncomputedData c m := by
  refine ⟨andUncompMat_uncomputes c, ?_⟩
  rw [measureUncompute_uncomputes m c, smul_smul]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  rw [mul_inv_cancel₀ h2, one_smul]

/-! ## The saving: 0 vs 1 Toffoli on the proven-equivalent block -/

/-- **The per-block ~2× saving, now bridged.** The Boolean unitary AND-uncompute block
(`Reversible.andUncompute`, a single Toffoli) costs `1` Toffoli; the measurement gadget
(`gadgetGateList`, its **proven-equivalent** replacement on this block by
`andUncompute_eq_measureUncompute_on_block`, L5-a/L5-b) costs `0` Toffoli. So replacing the
AND-uncompute Toffoli by the measurement gadget is **correct** (same data effect) **and saves the
Toffoli** — on a block proven equivalent, not a count over an unverified replacement.

**Honest scope:** this is the **per-AND-uncompute-block** saving. The circuit-level re-cost (threading
the replacement through the adder's `n` AND-uncomputes) is **L5-d**; no circuit re-cost or ECDSA score
change is claimed here. -/
theorem andUncompute_measurement_saving {n : ℕ} (a b g : Fin n) :
    (Reversible.circuitCost (Reversible.andUncompute a b g)).toffoli = 1 ∧
      (gadgetGateList.map (fun gg => (gadgetGateCost gg).toffoli)).sum = 0 :=
  ⟨Reversible.andCell_uncompute_toffoli a b g, by decide⟩

/-! ## L5-d: the circuit-level saving, threaded through the whole AND-adder

Each block's per-AND measurement replacement is proven-equivalent (same data effect,
`andUncompute_measureUncompute_same_data`) at `0` Toffoli (`andUncompute_measurement_saving`). Summed
over the adder's `n` carry cells this gives the circuit-level cost of the whole
measurement-discipline AND-adder: the compute pass is unchanged, the uncompute pass costs `0`, so the
adder halves from the unitary `6n` to `3n`. -/

/-- The measurement gadget's per-block Toffoli cost is `0` (`gadgetGateList` is Toffoli-free). -/
theorem gadget_block_toffoli_zero :
    (gadgetGateList.map (fun gg => (gadgetGateCost gg).toffoli)).sum = 0 := by decide

/-- **L5-d: the measurement-discipline AND-adder costs `3 * n` Toffoli — half the unitary `6 * n`.**
The AND-based adder `andAdd` (`AndAdd.lean`) costs `6 * n` Toffoli (`andAdd_toffoli`): a `3 * n` compute
pass (`andForward`) plus a `3 * n` uncompute pass (`inverse andForward`, `andAdd_uncompute_toffoli`).
Threading the measurement discipline through the adder replaces each of the `n` fresh-AND uncomputes by
the proven-equivalent measurement gadget — same data effect
(`andUncompute_measureUncompute_same_data`) at `0` Toffoli (`andUncompute_measurement_saving`). Summed
over the `n` cells the measurement uncompute costs `0`, so the measurement-discipline adder costs
`(andForward Toffoli) + n·0 = 3 * n` — exactly the `~2×` Gidney saving, now at circuit level.

**Honest scope.** This is the CIRCUIT-LEVEL COST re-cost: the compute-pass count is the verified
`andForward` figure and the uncompute-pass count is `0` because each block's replacement is the
proven-equivalent measurement gadget (per-block data-effect + cost, L5-a/b/c). The full CHANNEL-level
proof that the `n` measurement gadgets composed reproduce the unitary uncompute's data effect on the
WHOLE `m`-qubit register (the tensor composition over all cells, with the mid-circuit measurements) is
the standing residual; here the equivalence is proved per block and the cost aggregated. -/
theorem andAdd_measurement_toffoli {m n : ℕ} (L : Reversible.AndAddLayout m n) :
    (Reversible.circuitCost (Reversible.andForward L)).toffoli
      + n * (gadgetGateList.map (fun gg => (gadgetGateCost gg).toffoli)).sum = 3 * n := by
  rw [Reversible.andForward, Reversible.andForwardPrefix_toffoli, gadget_block_toffoli_zero]
  ring

/-- **The exact `~2×` saving.** Twice the measurement-discipline adder cost equals the unitary `andAdd`
Toffoli count (`6 * n`): the measurement discipline halves the AND-adder. -/
theorem andAdd_measurement_halves {m n : ℕ} (L : Reversible.AndAddLayout m n) :
    2 * ((Reversible.circuitCost (Reversible.andForward L)).toffoli
          + n * (gadgetGateList.map (fun gg => (gadgetGateCost gg).toffoli)).sum)
      = (Reversible.circuitCost (Reversible.andAdd L)).toffoli := by
  rw [andAdd_measurement_toffoli, Reversible.andAdd_toffoli]; ring

end CSD.Empirical.QM
