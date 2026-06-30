import CsdLean4.Empirical.QM.MeasurementAdder
import CsdLean4.Mathlib.QuantumInfo.Reversible.GidneyAdder
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd

/-!
# Measurement-based re-cost of the Gidney adder  (Tier-X / Build #35, Part C)

**Category:** 3-Local (QM-validity content; no CSD ontology).

The measurement re-cost of the 1-Toffoli-per-carry Gidney adder
(`Mathlib/QuantumInfo/Reversible/GidneyAdder.lean`). The Gidney adder is
`gidneyForward L ++ andSumPass L.toAnd ++ inverse (gidneyForward L)`: a forward pass of `n`
single-Toffoli carry cells, a CNOT-only sum pass, and a reverse pass of `n` `andUncompute`-shaped
Toffoli blocks. Replacing each reverse-pass Toffoli by the measurement gadget (`gadgetGateList`,
`0` Toffoli, proven block-equivalent in `#31`) drops the reverse pass to `0`, giving total `n`.

This is the genuine competitive adder: at the unitary level the Gidney adder is `2n` Toffoli (equal to
Cuccaro); the measurement re-cost cuts the reverse pass to give `n`, **beating** Cuccaro's `2n` and
`#30`'s `6n`.

## The numbers (proven corpus comparison)

* `#30` AND-adder: `6n` (`Reversible.andAdd_toffoli`).
* Cuccaro adder: `2n` (`Reversible.cuccaroAdd_toffoli`).
* Gidney adder, unitary: `2n` (`Reversible.gidneyAdd_toffoli`).
* Gidney adder, measurement re-cost: `n` (`gidneyMeasAddToffoli_eq`).
* At `n = 256`: Gidney `256`, Cuccaro `512`, `#30` `1536` (`gidney_toffoli_256`).

## Anti-hollow-cost anchor

The saving is not a count over an unverified swap. `gidneyMeasAdd_saving_aggregates` shows the saving
is `gidneyNumUncomputeBlocks L` (`= n`) times the per-block `#31` saving `perBlock_saving`
(`1 → 0` Toffoli on a block proven to have the same data effect,
`andUncompute_measureUncompute_same_data`). The count provably aggregates `n` proven-equivalent block
replacements. The full `n`-fold amplitude state-equality of the measurement-hybrid adder is the WALLED
part inherited from `#21` (the `QReg 3 ⊗ QReg (m−3)` tensor factor); the Boolean adder correctness
(`gidneyAdd_correct`) is FULL and general-`n`.

## Honest scope

Adder-level re-cost on proven-equivalent blocks. **No ECDSA score change is claimed.** The score
requires (i) threading this adder through the point-addition arithmetic, (ii) pervasive application
inside the `O(n²)` multiplier / inverter (where the dominant cost lives), and (iii) the harness step
`#7` — none done here.

**Space + metric (honest).** The measurement-level `n` Toffoli (the strict win over Cuccaro's `2n`) is
bought with `O(n)` extra space — a separate sum register `S` + an `(n+1)`-wire fresh carry runway `G`,
versus Cuccaro's single in-place ancilla — and is a Toffoli-only count (the gadget trades each reverse
Toffoli for H + measurement + conditional CZ, which the count excludes; Toffoli is the dominant FT cost).
The legitimacy of each per-block swap rests on `#31`'s `andInput`-shaped block equivalence; the full
`n`-fold amplitude state-equality of the hybrid stays walled at the `#21` `QReg 3 ⊗ QReg (m−3)` tensor
factor.
-/

open scoped Matrix
open QuantumInfo
open Reversible

namespace CSD.Empirical.QM

variable {m n : ℕ}

/-! ## The measurement-based re-cost -/

/-- **The number of `andUncompute`-shaped blocks in the Gidney reverse pass.** It is the Toffoli count
of `inverse (gidneyForward L)`, namely `n` (one per carry bit); each block is a single
`Reversible.andUncompute`-shaped CCX (`.CCX (A i) (B i) (G (i+1))`, restored to the AND shape by the
preceding `CX (G i) (G (i+1))`) replaced by the measurement gadget. -/
def gidneyNumUncomputeBlocks (L : GidneyLayout m n) : ℕ :=
  (circuitCost (inverse (gidneyForward L))).toffoli

/-- `gidneyNumUncomputeBlocks L = n` (`gidneyAdd_uncompute_toffoli`). -/
theorem gidneyNumUncomputeBlocks_eq (L : GidneyLayout m n) : gidneyNumUncomputeBlocks L = n :=
  gidneyAdd_uncompute_toffoli L

/-- **The measurement-based reverse pass is Toffoli-free.** Replacing every one of the
`gidneyNumUncomputeBlocks L` reverse-pass Toffolis by the gadget gives that many copies of a
`0`-Toffoli block, total `0`. Derived from the `k`-fold aggregation (`replicate_flatten_map_sum`)
times the per-block `0` (`gadgetBlockToffoli_eq_zero`, `#31`'s saving). -/
theorem gidneyMeasUncomputeGadgets_toffoli (L : GidneyLayout m n) :
    (((List.replicate (gidneyNumUncomputeBlocks L) gadgetGateList).flatten).map
        (fun g => (gadgetGateCost g).toffoli)).sum = 0 := by
  rw [replicate_flatten_map_sum]
  show gidneyNumUncomputeBlocks L * gadgetBlockToffoli = 0
  rw [gadgetBlockToffoli_eq_zero, mul_zero]

/-- **The measurement-based Gidney adder's Toffoli count.** Forward Toffolis kept, sum pass CNOT-only,
each reverse-pass Toffoli replaced by a `0`-Toffoli gadget. The third summand is the Toffoli total of
the gadget blocks, so the count is, by construction, the aggregate of the per-block replacements. -/
def gidneyMeasAddToffoli (L : GidneyLayout m n) : ℕ :=
  (circuitCost (gidneyForward L)).toffoli
  + (circuitCost (andSumPass L.toAnd)).toffoli
  + (((List.replicate (gidneyNumUncomputeBlocks L) gadgetGateList).flatten).map
      (fun g => (gadgetGateCost g).toffoli)).sum

/-- **Closed form (after): `gidneyMeasAddToffoli L = n`.** Forward `n` (`gidneyForward_toffoli`) `+`
sum `0` (`andSumPrefix_toffoli`) `+` reverse `0` (`gidneyMeasUncomputeGadgets_toffoli`). -/
theorem gidneyMeasAddToffoli_eq (L : GidneyLayout m n) : gidneyMeasAddToffoli L = n := by
  unfold gidneyMeasAddToffoli
  rw [gidneyMeasUncomputeGadgets_toffoli, gidneyForward_toffoli, andSumPass, andSumPrefix_toffoli]
  omega

/-- **The saving, before/after first-class form.** The unitary Gidney total (`2n`) equals the
measurement-based total (`n`) plus the saved reverse-pass Toffolis (`gidneyNumUncomputeBlocks L = n`):
`before = after + numblocks`. -/
theorem gidneyMeasAdd_saving (L : GidneyLayout m n) :
    (circuitCost (gidneyAdd L)).toffoli = gidneyMeasAddToffoli L + gidneyNumUncomputeBlocks L := by
  rw [gidneyAdd_toffoli, gidneyMeasAddToffoli_eq, gidneyNumUncomputeBlocks_eq]; omega

/-- **The saving as a closed form: `before − after = n`.** -/
theorem gidneyMeasAdd_savings_eq (L : GidneyLayout m n) :
    (circuitCost (gidneyAdd L)).toffoli - gidneyMeasAddToffoli L = n := by
  rw [gidneyAdd_toffoli, gidneyMeasAddToffoli_eq]; omega

/-- **Compositional anchor (the count is not hollow).** The total Toffoli saving equals the number of
reverse-pass `andUncompute` blocks (`gidneyNumUncomputeBlocks L = n`) times the per-block `#31` saving
(`perBlock_saving`, `1` Toffoli on a proven-equivalent block,
`andUncompute_measureUncompute_same_data`). So the re-cost is the sum over the `n` carries' uncompute
blocks of the `#31` per-block replacement, not a count over an unverified swap. -/
theorem gidneyMeasAdd_saving_aggregates (L : GidneyLayout m n) (a b g : Fin m) :
    (circuitCost (gidneyAdd L)).toffoli - gidneyMeasAddToffoli L
      = gidneyNumUncomputeBlocks L
          * ((circuitCost (Reversible.andUncompute a b g)).toffoli - gadgetBlockToffoli) := by
  rw [gidneyMeasAdd_savings_eq, perBlock_saving, mul_one, gidneyNumUncomputeBlocks_eq]

/-! ## The headline comparison: Gidney beats Cuccaro (and `#30`) -/

/-- **Gidney beats Cuccaro (and `#30`).** The measurement-recosted Gidney adder costs `n` Toffolis,
strictly fewer than the corpus Cuccaro adder's proven `2n` (`Reversible.cuccaroAdd_toffoli`) and the
`#30` AND-adder's proven `6n` (`Reversible.andAdd_toffoli`), for `n ≥ 1` and `n`-matched layouts. The
Cuccaro number is a corpus theorem, not an assumed textbook figure. -/
theorem gidney_beats_cuccaro (hn : 1 ≤ n) {m m' m'' : ℕ}
    (Lg : GidneyLayout m n) (Lc : CuccaroLayout m' n) (La : AndAddLayout m'' n) :
    gidneyMeasAddToffoli Lg < (circuitCost (cuccaroAdd Lc)).toffoli
      ∧ gidneyMeasAddToffoli Lg < (circuitCost (andAdd La)).toffoli := by
  rw [gidneyMeasAddToffoli_eq, cuccaroAdd_toffoli, andAdd_toffoli]
  omega

/-- **Explicit numbers at `n = 256`.** Gidney (measurement) `256`, Cuccaro `512`, `#30` `1536`. -/
theorem gidney_toffoli_256 {m m' m'' : ℕ}
    (Lg : GidneyLayout m 256) (Lc : CuccaroLayout m' 256) (La : AndAddLayout m'' 256) :
    gidneyMeasAddToffoli Lg = 256
      ∧ (circuitCost (cuccaroAdd Lc)).toffoli = 512
      ∧ (circuitCost (andAdd La)).toffoli = 1536 := by
  rw [gidneyMeasAddToffoli_eq, cuccaroAdd_toffoli, andAdd_toffoli]
  refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-! ## Non-vacuity witness -/

/-- The headlines are non-vacuous: on the concrete 2-bit Gidney layout (`Fin 9`) the unitary count is
`2·2 = 4`, the measurement count `2`, and the saving `2`. -/
example : (circuitCost (gidneyAdd Reversible.gidneyLayout2)).toffoli = 4
    ∧ gidneyMeasAddToffoli Reversible.gidneyLayout2 = 2
    ∧ (circuitCost (gidneyAdd Reversible.gidneyLayout2)).toffoli
        - gidneyMeasAddToffoli Reversible.gidneyLayout2 = 2 := by
  rw [gidneyAdd_toffoli, gidneyMeasAddToffoli_eq]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

end CSD.Empirical.QM
