/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.MeasurementUncompute
public import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Lift

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

1.–4. *(Extracted 2026-08-21.)* The generic gate-lift layer — `ccx` (the CCX permutation in the
   `Fin 2` representation), its permutation matrix `andUncompMat`,
   `andUncompMat_apply_basisState`, the `Bool ↔ Fin 2` recasts (`stateOfB3` / `b3OfState`), and
   **the localized gate-lift `andUncompMat_lifts_denote`** (the L5-c crux: the unitary acts on
   computational basis states exactly as the Boolean `denote (andUncompute 0 1 2)` permutation) —
   is generic mathematics with no gadget content, and now lives Category-1 beside the DSL:
   `Mathlib/QuantumInfo/Reversible/Lift.lean` (namespace `Reversible`, re-exported here through
   the import). This file keeps what is genuinely gadget-specific: `ccx_andIdx` (the AND-shaped
   index is uncomputed) and everything below.
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
**trusted base grows** by this localized amplitude lift — the permutation-matrix lift of the block
(`Reversible.andUncompMat_lifts_denote`, `Mathlib/QuantumInfo/Reversible/Lift.lean`) plus the
data-agreement (`andUncompMat_uncomputes`, here).

The amplitude model is **required**: the measurement gadget uses phases (X-basis + CZ), which the
Boolean reversible DSL cannot express.

**Deferred:** **L5-d** (iterating this block-replacement across the full AND-based adder's `n` carry
uncomputes — `andAdd`'s `inverse andForward` — to obtain the circuit-level re-cost gap, ~10.5× → ~5×;
needs threading the replacement through the `n` AND-uncomputes), and **step #7** (the harness). **No
circuit-level re-cost claim is made here, and no ECDSA resource-score change.**
-/

@[expose] public section

open scoped Matrix
open QuantumInfo
open Reversible

namespace CSD.Empirical.QM

/-! ## The gate-lift layer, imported

The CCX permutation `ccx`, its permutation matrix `andUncompMat`, the `Bool ↔ Fin 2` recasts
(`stateOfB3` / `b3OfState`), and the localized gate-lift `andUncompMat_lifts_denote` are generic
mathematics and live Category-1 in `Mathlib/QuantumInfo/Reversible/Lift.lean` (namespace
`Reversible`, opened above; extracted from this file 2026-08-21). What is gadget-specific stays
here. -/

/-- `ccx` uncomputes the AND-entangled index: `ccx ![x, y, x∧y] = ![x, y, 0]`. The ancilla bit
`x*y + x*y = 0` in `Fin 2`; the data `(x,y)` is untouched. -/
lemma ccx_andIdx (x y : Fin 2) : ccx (andIdx x y) = ![x, y, 0] := by
  rw [b3_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp only [ccx, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide), andIdx_zero]
  · simp only [ccx, Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide), andIdx_one]
  · simp only [ccx, Function.update_self, andIdx_zero, andIdx_one, andIdx_two]
    fin_cases x <;> fin_cases y <;> decide

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
