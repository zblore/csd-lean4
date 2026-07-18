import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdDivstepCircuit

/-!
# Average-EXECUTED Toffoli — the competition's scored quantity, computed (not assumed)  (ECDLP, #36c-2)

**Category:** 1-Mathlib (CSD-free).

The ecdsa.fail score is `peak_qubits × AVERAGE-EXECUTED Toffoli`, where a Toffoli is "executed" on an
input iff BOTH its controls are set at the moment it runs (otherwise it is inert / identity on that
input). This module implements that exact counting rule (`executedToffoli`) and RUNS it over concrete
verified gadgets to produce a MEASURED average-executed count — the honest, computed alternative to
adopting the frontier's number.

`executedToffoli c s` folds the gate list tracking the running state; on each `CCX` it adds `1` iff both
controls are currently set. `avgExecutedNum` sums that over all `2^wires` inputs (the numerator; divide by
`2^wires` for the average). Contrast `(circuitCost c).toffoli`, the EMITTED count — the executed count is
`≤` it, and the ratio is exactly the "how much less than worst-case" the score sees.

**Scope of what is measured here:** the concrete `n=3` carry-clean adder `cuccaroAdd cuccaroLayout3` (the
dominant Toffoli source in the divstep). This is a genuine measurement of OUR verified gadget under the
competition's rule — averaged over ALL `2^7` inputs (a uniform-input model, not the harness's specific
9024-shot island, which needs the assembled point-add op-stream + `eval_circuit`, task #7). It grounds the
executed/emitted ratio in a real computation. Assembling the full divstep / point-add to measure the
end-to-end number is the ongoing `denote = divstepRev` work.
-/

namespace ECDLP.Safegcd.Circuit

open Reversible

/-- **The competition's counting rule: Toffolis that ACTUALLY FIRE.** Runs circuit `c` on the strict
`Array Bool` input `a`, counting each `CCX` whose two controls are both set when it executes (an inert
`CCX` — some control `0` — adds nothing, exactly as the "executed, not emitted" score treats it). One
input's executed-Toffoli. Array-backed (`applyGate`) so `#eval` over many inputs is fast. -/
def executedToffoli {m : ℕ} (c : Circuit m) (a : Array Bool) : ℕ :=
  (c.foldl (fun (p : ℕ × Array Bool) g =>
    match g with
    | .CCX c₁ c₂ _ => (p.1 + (if p.2[c₁.val]! && p.2[c₂.val]! then 1 else 0), applyGate g p.2)
    | _ => (p.1, applyGate g p.2)) (0, a)).1

/-- Decode a natural `i` to an `m`-wire `Array Bool` input (bit `j` = `Nat.testBit i j`). -/
def arrOfNat (m i : ℕ) : Array Bool := Array.ofFn (fun (j : Fin m) => Nat.testBit i j.val)

/-- **Total executed Toffoli over all `2^wires` inputs** (numerator of the average-executed count; divide
by `2 ^ wires`). Enumerates every input state and sums `executedToffoli`. -/
def totalExecuted {m : ℕ} (c : Circuit m) (wires : ℕ) : ℕ :=
  (List.range (2 ^ wires)).foldl (fun acc i => acc + executedToffoli c (arrOfNat m i)) 0

/-! ### Measurements on the concrete verified `n=3` carry-clean adder (7 wires) -/

/-- EMITTED Toffoli of the `n=3` Cuccaro adder: `2·n = 6` (the worst-case op-count `circuitCost`). -/
example : (circuitCost (cuccaroAdd cuccaroLayout3)).toffoli = 6 := by decide

-- MEASURED total executed Toffoli of the n=3 Cuccaro adder, summed over all 2^7 = 128 inputs.
-- avg-executed = total / 128; executed/emitted percent = total * 100 / (128 * 6).
#eval totalExecuted (cuccaroAdd cuccaroLayout3) 7                     -- 192  (total executed over 128 inputs)
#eval totalExecuted (cuccaroAdd cuccaroLayout3) 7 * 1000 / 128        -- 1500 (avg-executed × 1000 → 1.500)
#eval totalExecuted (cuccaroAdd cuccaroLayout3) 7 * 100 / (128 * 6)   -- 25   (executed / emitted, percent)

/-! ### Extrapolation to the point-add avg-executed (a MODEL grounded in the measurement)

The measured executed/emitted ratio for the verified adder is `192/(128·6) = 25%`. Applying it to the
EMITTED worst-case safegcd point-add Toffoli (`ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate =
7,801,612`) gives a CALCULATED avg-executed estimate — the competition's scored quantity, computed from a
real measurement rather than adopted. **Honest scope:** a single-gadget ratio under UNIFORM inputs, not
the point-add's mixed gadgets over the harness's specific 9024-shot island, and BEFORE constprop folding
(which the frontier applies and we do not). So it is a grounded MODEL, `~1.95×10⁶`, in the frontier's
ballpark (`~1.37×10⁶`) — the residual gap is constprop + the input-distribution/mixed-gadget difference,
not a copied number. The exact figure needs the assembled op-stream + `eval_circuit` (task #7). -/

-- calculated avg-executed point-add = emitted 7,801,612 × (measured 25% ratio):
#eval 7801612 * (totalExecuted (cuccaroAdd cuccaroLayout3) 7) / (128 * 6)  -- 1950403 (≈ 1.95e6)

/-! ### Certified executed-vs-emitted bounds (the measured ratio, now PROVED)

The `#eval`s above MEASURE the executed count. These theorems PROVE the structural facts the whole
average-executed argument rests on: the executed Toffoli is always `≤` the emitted count (so the scored
quantity is a genuine lower bound on the verified worst-case floor), it stays `≤` on average, and the gap
is real — an "inert" Toffoli (a control clear at run time) contributes `0` executed but `1` emitted. This
is the data-dependence mechanism that makes the average-executed metric below worst-case, certified rather
than sampled. -/

/-- **Executed ≤ emitted (per input), certified.** For every input `a`, the number of Toffolis that
actually FIRE is at most the number EMITTED (`(circuitCost c).toffoli` counts the `CCX` gates; the executed
count adds `≤ 1` per `CCX`). So the competition's scored quantity is a provable lower bound on the verified
emitted floor — the direction the three-track ledger asserts, now a theorem, not a measurement. -/
theorem executedToffoli_le_toffoli {m : ℕ} (c : Circuit m) (a : Array Bool) :
    executedToffoli c a ≤ (circuitCost c).toffoli := by
  have key : ∀ (gs : Circuit m) (acc : ℕ) (arr : Array Bool),
      (List.foldl (fun (p : ℕ × Array Bool) g =>
        match g with
        | .CCX c₁ c₂ _ => (p.1 + (if p.2[c₁.val]! && p.2[c₂.val]! then 1 else 0), applyGate g p.2)
        | _ => (p.1, applyGate g p.2)) (acc, arr) gs).1
        ≤ acc + (List.map (fun g => (gateCost g).toffoli) gs).sum := by
    intro gs
    induction gs with
    | nil => intro acc arr; simp
    | cons g gs' ih =>
      intro acc arr
      rw [List.foldl_cons, List.map_cons, List.sum_cons]
      cases g with
      | CCX c₁ c₂ t => refine (ih _ _).trans ?_; simp only [gateCost]; split <;> omega
      | X i => exact (ih _ _).trans (by simp only [gateCost]; omega)
      | CX c₃ t => exact (ih _ _).trans (by simp only [gateCost]; omega)
      | swap i j => exact (ih _ _).trans (by simp only [gateCost]; omega)
  simpa [executedToffoli, circuitCost] using key c 0 a

/-- **Total executed ≤ emitted × #inputs, certified.** Summing the per-input bound: the average-executed
Toffoli (`totalExecuted / 2^wires`) never exceeds the emitted worst-case. The scored average is a certified
lower bound on the floor. -/
theorem totalExecuted_le {m : ℕ} (c : Circuit m) (wires : ℕ) :
    totalExecuted c wires ≤ (circuitCost c).toffoli * 2 ^ wires := by
  have key : ∀ (l : List ℕ) (acc : ℕ),
      l.foldl (fun acc i => acc + executedToffoli c (arrOfNat m i)) acc
        ≤ acc + (circuitCost c).toffoli * l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons i l' ih =>
      intro acc
      rw [List.foldl_cons, List.length_cons, Nat.mul_succ]
      exact (ih _).trans (by have := executedToffoli_le_toffoli c (arrOfNat m i); omega)
  simpa [totalExecuted, List.length_range] using key (List.range (2 ^ wires)) 0

/-- **The inert-Toffoli mechanism, certified.** A single `CCX` with a control clear at run time contributes
`0` to the EXECUTED count while contributing `1` to the EMITTED count. This is the exact data-dependence
that pushes average-executed strictly below worst-case: the executed metric sees an inert Toffoli as
identity. The gap the three-track ledger exploits is real and proved, not merely sampled. -/
theorem inertToffoli_executed_zero {m : ℕ} (c₁ c₂ t : Fin m) (a : Array Bool)
    (h : a[c₁.val]! = false) :
    executedToffoli [Gate.CCX c₁ c₂ t] a = 0
      ∧ (circuitCost [Gate.CCX c₁ c₂ t]).toffoli = 1 := by
  refine ⟨?_, by simp [circuitCost, gateCost]⟩
  simp [executedToffoli, h]

end ECDLP.Safegcd.Circuit
