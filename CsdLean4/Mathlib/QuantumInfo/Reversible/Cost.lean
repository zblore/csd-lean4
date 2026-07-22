/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.Circuit
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Reversible-circuit resource cost — the derived gate-list cost model  (ECDLP Tranche 1b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The cost half of the reversible-circuit substrate (`Circuit.lean`). The design decision (locked in
`specs/ecdlp-resource-plan.md`): a circuit's resource cost is a **function of its gate list**, not a
number annotated onto an opaque `Equiv`. So "operation `op` costs `≤ B` Toffolis" is a *theorem* —
exhibit a circuit `c`, prove `denote c = op` and `(circuitCost c).toffoli ≤ B` — not a trusted
constant. This is what makes the downstream ECDLP resource accounting genuinely machine-checked.

`Cost` bundles the standard fault-tolerant resource fields (qubit width, ancilla, Toffoli count and
depth, CNOT count, T-count, measurements), all `ℕ`. `circuitCost` reads each additive field off the
gate list by `(c.map (gateCost · |>.field)).sum`, deliberately avoiding an `AddMonoid Cost` instance
(the width fields `qubits`/`ancilla` are NOT additive under composition — they combine by `max` /
accumulation — so a single monoid structure would be wrong for them). The composition lemmas below
make the additive/non-additive split explicit: Toffoli/CNOT counts add exactly; Toffoli depth is
`≤`-subadditive (here equality, since the model is sequential); width is `≤ max` (here trivial, since
`circuitCost` fixes `qubits := n` — genuine width/ancilla accounting is a Pass-2 refinement).
-/

namespace Reversible

variable {n : ℕ}

/-- Fault-tolerant resource cost of a reversible circuit: qubit width, ancilla count, Toffoli count
and depth, CNOT count, T-count, and measurement count. All `ℕ`. The count fields are additive under
sequential composition; `qubits`/`ancilla` are width fields (combine by `max`/accumulation, not `+`).
-/
structure Cost where
  /-- Number of (logical) qubits the circuit acts on. -/
  qubits : ℕ
  /-- Number of ancilla qubits used. -/
  ancilla : ℕ
  /-- Number of Toffoli (CCX) gates. -/
  toffoli : ℕ
  /-- Toffoli depth (longest chain of dependent Toffolis); for a sequential gate list, the count. -/
  toffoliDepth : ℕ
  /-- Number of CNOT (CX) gates. -/
  cnot : ℕ
  /-- T-gate count (Pass-2 refinement; `0` at the abstract Pass-1 model). -/
  tCount : ℕ
  /-- Number of measurements. -/
  meas : ℕ
  deriving DecidableEq, Repr

/-- Per-gate resource cost. `X` is free (a classical bit flip, no T/Toffoli); `CX` is one CNOT;
`CCX` is one Toffoli at depth one; `swap` is three CNOTs (the standard CNOT decomposition). The
width fields (`qubits`/`ancilla`) are `0` here — they are supplied at the circuit level by
`circuitCost`, since a single gate does not determine the register width.

Cost is **syntactic**: it is a function of the gate, not of the permutation it realises. A
degenerate gate (control = target, e.g. `CCX i j i`) acts as the identity under `denoteGate` yet is
still billed its full cost. This is the conservative (upper-bound) convention for resource
accounting — `circuitCost c` bounds the true cost of any realisation of `c` — so do NOT assume
`denoteGate g = id ⇒ gateCost g = 0`. A degenerate-gate–stripping `simplify` pass before costing is
a possible Pass-2 refinement. -/
def gateCost : Gate n → Cost
  | .X _ => { qubits := 0, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 0, tCount := 0, meas := 0 }
  | .CX _ _ => { qubits := 0, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 1, tCount := 0, meas := 0 }
  | .CCX _ _ _ => { qubits := 0, ancilla := 0, toffoli := 1, toffoliDepth := 1, cnot := 0, tCount := 0, meas := 0 }
  | .swap _ _ => { qubits := 0, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 3, tCount := 0, meas := 0 }

/-- The derived cost of a circuit: each additive field is the gate-list sum of that field of
`gateCost`; the width is `qubits := n` (the circuit acts on `n` wires) with `ancilla := 0` (the
classical reversible layer introduces no ancilla — ancilla accounting is a Pass-2 refinement). -/
def circuitCost (c : Circuit n) : Cost where
  qubits := n
  ancilla := 0
  toffoli := (c.map (fun g => (gateCost g).toffoli)).sum
  toffoliDepth := (c.map (fun g => (gateCost g).toffoliDepth)).sum
  cnot := (c.map (fun g => (gateCost g).cnot)).sum
  tCount := (c.map (fun g => (gateCost g).tCount)).sum
  meas := (c.map (fun g => (gateCost g).meas)).sum

@[simp] theorem circuitCost_nil : circuitCost ([] : Circuit n) =
    { qubits := n, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 0, tCount := 0, meas := 0 } := by
  simp [circuitCost]

@[simp] theorem circuitCost_qubits (c : Circuit n) : (circuitCost c).qubits = n := rfl

@[simp] theorem circuitCost_ancilla (c : Circuit n) : (circuitCost c).ancilla = 0 := rfl

/-- **Toffoli count is additive under composition.** Exact equality: the gate list of `c₁ ++ c₂` is
the concatenation, and the sum of a concatenation splits (`List.map_append` + `List.sum_append`). -/
theorem cost_comp_toffoli_count (c₁ c₂ : Circuit n) :
    (circuitCost (c₁ ++ c₂)).toffoli = (circuitCost c₁).toffoli + (circuitCost c₂).toffoli := by
  simp [circuitCost, List.map_append, List.sum_append]

/-- **CNOT count is additive under composition.** -/
theorem cost_comp_cnot_count (c₁ c₂ : Circuit n) :
    (circuitCost (c₁ ++ c₂)).cnot = (circuitCost c₁).cnot + (circuitCost c₂).cnot := by
  simp [circuitCost, List.map_append, List.sum_append]

/-- **Toffoli depth is `≤`-subadditive under composition.** For a sequential gate list this holds
with equality; stated as `≤` because depth is genuinely subadditive (parallel scheduling can only
lower it), which is the bound downstream resource accounting relies on. -/
theorem cost_comp_toffoli_depth_le (c₁ c₂ : Circuit n) :
    (circuitCost (c₁ ++ c₂)).toffoliDepth
      ≤ (circuitCost c₁).toffoliDepth + (circuitCost c₂).toffoliDepth := by
  simp [circuitCost, List.map_append, List.sum_append]

/-- **Width is `≤ max` under composition.** Composing two circuits on the same `n` wires does not
widen the register. (At the abstract Pass-1 model `circuitCost` fixes `qubits := n`, so this is
`n ≤ max n n`; genuine width/ancilla accounting is a Pass-2 refinement.) -/
theorem cost_comp_qubits_le (c₁ c₂ : Circuit n) :
    (circuitCost (c₁ ++ c₂)).qubits ≤ max (circuitCost c₁).qubits (circuitCost c₂).qubits := by
  simp [circuitCost]

/-- **The inverse circuit has the same cost.** `inverse = List.reverse` permutes the gate list, and
every additive field is a `List.sum` of a `List.map`, invariant under reversal
(`List.map_reverse` + `List.sum_reverse`); the width fields are constant. -/
theorem cost_inverse_toffoli (c : Circuit n) :
    (circuitCost (inverse c)).toffoli = (circuitCost c).toffoli := by
  simp [circuitCost, inverse, List.map_reverse, List.sum_reverse]

theorem cost_inverse_cnot (c : Circuit n) :
    (circuitCost (inverse c)).cnot = (circuitCost c).cnot := by
  simp [circuitCost, inverse, List.map_reverse, List.sum_reverse]

end Reversible
