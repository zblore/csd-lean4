/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.MeasurementGidneyAdder
public import CsdLean4.Empirical.QM.MeasurementUncomputeLift

/-!
# EC-3 capstone: the measurement-discipline adder hierarchy

**Category:** 3-Local (the measurement-discipline adder hierarchy).

Two adder families carry the safegcd / point-op cost model, and each has a unitary and a
measurement-discipline cost:

| adder | unitary | measurement-discipline |
|---|---|---|
| AND-based (`AndAdd.lean`, #30) | `6n` (`andAdd_toffoli`) | `3n` (`andAdd_measurement_toffoli`, EC-6/L5-d) |
| Gidney (`GidneyAdder.lean`, #35) | `2n` (`gidneyAdd_toffoli`) | `n`  (`gidneyMeasAddToffoli_eq`, EC-3) |

This module states the full ordering as one theorem, each entry a PROVEN circuit cost (not an assumed
figure): the measurement-discipline Gidney adder at `n` Toffoli is the cheapest of the four, strictly
below the unitary Gidney (`2n`), the measurement AND-adder (`3n`), and the unitary AND-adder (`6n`).

## Honest scope

Every cost here is a proven `Reversible.circuitCost … .toffoli` figure; the measurement-discipline
figures are cost re-costs whose per-AND-block replacement is proven-equivalent
(`andUncompute_measureUncompute_same_data`, data effect + `0` Toffoli). The CHANNEL-level proof that the
`n` measurement gadgets composed reproduce the unitary uncompute's data effect on the WHOLE register
(the tensor composition over all cells) is the standing residual shared by EC-3 and EC-6 — proved per
block, aggregated in cost. No amplitudes or ECDSA-score claim here; just the adder cost ordering.
-/

@[expose] public section

open QuantumInfo Reversible

namespace CSD.Empirical.QM

/-- **The measurement-discipline adder hierarchy (all four costs, each proven).** For `n`-matched
layouts: the measurement Gidney adder costs `n`, the unitary Gidney adder `2n`, the measurement
AND-adder `3n`, and the unitary AND-adder `6n`. -/
theorem measurement_adder_hierarchy {m m' n : ℕ}
    (Lg : GidneyLayout m n) (La : AndAddLayout m' n) :
    gidneyMeasAddToffoli Lg = n
    ∧ (circuitCost (gidneyAdd Lg)).toffoli = 2 * n
    ∧ (circuitCost (andForward La)).toffoli
        + n * (gadgetGateList.map (fun gg => (gadgetGateCost gg).toffoli)).sum = 3 * n
    ∧ (circuitCost (andAdd La)).toffoli = 6 * n :=
  ⟨gidneyMeasAddToffoli_eq Lg, gidneyAdd_toffoli Lg,
    andAdd_measurement_toffoli La, andAdd_toffoli La⟩

/-- **The measurement Gidney adder is the cheapest of the four** (for `n ≥ 1`): its `n` Toffoli beat the
unitary Gidney (`2n`), the measurement AND-adder (`3n`), and the unitary AND-adder (`6n`). The final
score lever on the adder side — the least-Toffoli reversible adder in the corpus, verified. -/
theorem gidneyMeas_cheapest {m m' n : ℕ} (hn : 1 ≤ n)
    (Lg : GidneyLayout m n) (La : AndAddLayout m' n) :
    gidneyMeasAddToffoli Lg < (circuitCost (gidneyAdd Lg)).toffoli
    ∧ gidneyMeasAddToffoli Lg
        < (circuitCost (andForward La)).toffoli
          + n * (gadgetGateList.map (fun gg => (gadgetGateCost gg).toffoli)).sum
    ∧ gidneyMeasAddToffoli Lg < (circuitCost (andAdd La)).toffoli := by
  obtain ⟨h1, h2, h3, h4⟩ := measurement_adder_hierarchy Lg La
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, h2]; omega
  · rw [h1, h3]; omega
  · rw [h1, h4]; omega

end CSD.Empirical.QM

