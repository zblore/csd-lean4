import CsdLean4.Mathlib.QuantumInfo.Reversible.Circuit
import CsdLean4.Mathlib.QuantumInfo.Reversible.Cost
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Reversible modular addition — register encoding, verified full adder, ripple cost  (ECDLP Tranche 2, Pass 1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The addition layer of the reversible-circuit substrate
(`Circuit.lean` / `Cost.lean`, `specs/ecdlp-resource-plan.md`). Pass 1 delivers a **sorry-free
semantic + derived-cost scaffold**: the register readout `regVal`, the **fully verified** four-gate
full-adder gadget, its derived cost, and the **linear** Toffoli / CNOT count of an `k`-slice ripple
adder (composed through the Tranche-1 `cost_comp_*` lemmas, not re-derived).

The locked design decision is respected throughout: every cost claim is about an *exhibited*
`Circuit` and is discharged through `circuitCost`. The full-adder correctness is genuine
all-inputs coverage (`decide` over `Fintype (Fin 4 → Bool)`), not a single example.

## What is proved here (Pass 1)

* `regVal` little-endian readout, `regVal_lt_two_pow`, and an `X`-flip round-trip lemma.
* `fullAdder` (four gates) with **full all-inputs correctness** on the concrete `State 4` layout:
  sum bit `b ← a ⊕ b ⊕ cin`, carry-out `cout ← majority(a, b, cin)` (with `cout` init `false`),
  `a` and `cin` preserved.
* `fullAdder_cost`: derived `toffoli = 2`, `cnot = 2` (and the full `Cost` record).
* `rippleAdder` (an `k`-slice concatenation of `fullAdder` gadgets) with **linear cost**:
  `(circuitCost (rippleAdder ...)).toffoli = 2 * k` and `.cnot = 2 * k`, composed through the
  Tranche-1 composition lemmas.

## Pass-2 target (NOT attempted here)

The general-`n` in-place carry-chain *correctness* over `regVal` — i.e. proving that the `k`-slice
`rippleAdder`, threaded through a concrete carry/sum wire layout, computes
`regVal (output) = (regVal a + regVal b) mod 2 ^ n` — is the **Pass-2** target. It is index-heavy
(per-slice carry propagation) and is deliberately deferred; nothing below claims it. Pass 1 proves
the *gadget* correct and the *cost* linear; Pass 2 wires the gadgets into the modular sum and proves
the arithmetic identity.
-/

namespace Reversible

variable {n : ℕ}

/-! ### Register encoding (little-endian) -/

/-- Little-endian binary readout of a wire state: wire `i` carries place value `2 ^ i`. -/
def regVal (s : State n) : ℕ := ∑ i : Fin n, if s i then 2 ^ (i : ℕ) else 0

@[simp] theorem regVal_zero (s : State 0) : regVal s = 0 := by
  simp [regVal]

/-- The register value is bounded by `2 ^ n` (an `n`-wire register holds an `n`-bit number). -/
theorem regVal_lt_two_pow (s : State n) : regVal s < 2 ^ n := by
  induction n with
  | zero => simp [regVal]
  | succ m ih =>
    -- Split the top wire off the sum.
    have hsplit : regVal s
        = (∑ i : Fin m, if s (i.castSucc) then 2 ^ (i : ℕ) else 0)
          + (if s (Fin.last m) then 2 ^ m else 0) := by
      simp only [regVal, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    -- The lower-`m` part is `< 2 ^ m` (it is `regVal` of the restricted state).
    have hlow : (∑ i : Fin m, if s (i.castSucc) then 2 ^ (i : ℕ) else 0) < 2 ^ m :=
      ih (fun i => s i.castSucc)
    rw [hsplit, pow_succ]
    have htop : (if s (Fin.last m) then 2 ^ m else 0) ≤ 2 ^ m := by
      split <;> simp
    omega

/-- The general place-value update law for `Function.update s i b`: replacing wire `i`'s bit by `b`
(for ANY prior bit `s i` and ANY new bit `b`) removes `i`'s old place-value contribution and adds the
new one. The reusable round-trip helper consumed by ModMul / ScalarMul. -/
theorem regVal_update_eq (s : State n) (i : Fin n) (b : Bool) :
    regVal (Function.update s i b)
      = (regVal s - (if s i then 2 ^ (i : ℕ) else 0)) + (if b then 2 ^ (i : ℕ) else 0) := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  -- Peel index `i` out of both sums.
  have hupd : regVal (Function.update s i b)
      = (if b then 2 ^ (i : ℕ) else 0)
        + ∑ j ∈ Finset.univ.erase i, if Function.update s i b j then 2 ^ (j : ℕ) else 0 := by
    rw [regVal, ← Finset.add_sum_erase _ _ hmem, Function.update_self]
  have horig : regVal s
      = (if s i then 2 ^ (i : ℕ) else 0)
        + ∑ j ∈ Finset.univ.erase i, if s j then 2 ^ (j : ℕ) else 0 := by
    rw [regVal, ← Finset.add_sum_erase _ _ hmem]
  -- Off-index terms agree.
  have hcongr : (∑ j ∈ Finset.univ.erase i, if Function.update s i b j then 2 ^ (j : ℕ) else 0)
      = ∑ j ∈ Finset.univ.erase i, if s j then 2 ^ (j : ℕ) else 0 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hupd, horig, hcongr]
  omega

/-! ### The full-adder gadget (the verified primitive) -/

/-- Boolean majority of three bits: at least two are set. -/
def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The four-gate full adder on wires `a b cin cout` (with `cout` initialised `false`):
`b ← a ⊕ b ⊕ cin` (sum bit), `cout ← majority(a, b, cin)` (carry-out), `a`/`cin` unchanged.

The gate order realises the standard in-place adder: write the partial carry into `cout` from
`(a,b)`, fold `a` into `b`, fold `(cin,b)` into `cout`, fold `cin` into `b`. Correctness on the
concrete layout is `fullAdder_correct`. -/
def fullAdder (a b cin cout : Fin n) : Circuit n :=
  [.CCX a b cout, .CX a b, .CCX cin b cout, .CX cin b]

/-- **Full-adder correctness — genuine all-inputs coverage.** On the concrete `State 4` layout
(wires `0,1,2,3 = a,b,cin,cout`), with `cout` initialised `false`, the gadget computes the sum bit
on wire `1`, the carry-out on wire `3`, and preserves `a` (wire `0`) and `cin` (wire `2`). Proved by
`decide` over the finite `State 4 = Fin 4 → Bool` (16 inputs, each input fixed `s 3 = false`). -/
theorem fullAdder_correct :
    ∀ s : State 4, s 3 = false →
      (denote (fullAdder 0 1 2 3) s 1 = (s 0 ^^ s 1 ^^ s 2))
        ∧ (denote (fullAdder 0 1 2 3) s 3 = majority (s 0) (s 1) (s 2))
        ∧ (denote (fullAdder 0 1 2 3) s 0 = s 0)
        ∧ (denote (fullAdder 0 1 2 3) s 2 = s 2) := by
  decide

/-- **Frame lemma for the gadget.** A wire distinct from all four of `a, b, cin, cout` is untouched
by `fullAdder` (every gate's wires lie in `{a, b, cin, cout}`). The payoff of the Circuit-level
`denote_apply_of_forall_not_mem`; lets the carry-chain (Pass 2) lift this slice over a register. -/
theorem fullAdder_apply_of_ne {a b cin cout w : Fin n}
    (ha : w ≠ a) (hb : w ≠ b) (hcin : w ≠ cin) (hcout : w ≠ cout) (s : State n) :
    denote (fullAdder a b cin cout) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [fullAdder, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp_all [gateWires]

/-- **Full-adder correctness, general `Fin n` wires.** For pairwise-distinct wires `a, b, cin, cout`
with `cout` initialised `false`, the gadget writes the sum bit to `b`, the carry-out to `cout`, and
preserves `a` and `cin` — over arbitrary `Fin n` (not just the concrete `State 4` of
`fullAdder_correct`). This is the slice the ripple carry-chain (Pass 2) iterates. -/
theorem fullAdder_correct_general {a b cin cout : Fin n}
    (hba : b ≠ a) (hbcin : b ≠ cin) (hcouta : cout ≠ a) (hcoutb : cout ≠ b)
    (hcoutcin : cout ≠ cin) (hacin : a ≠ cin) {s : State n} (hc0 : s cout = false) :
    denote (fullAdder a b cin cout) s b = (s a ^^ s b ^^ s cin)
      ∧ denote (fullAdder a b cin cout) s cout = majority (s a) (s b) (s cin)
      ∧ denote (fullAdder a b cin cout) s a = s a
      ∧ denote (fullAdder a b cin cout) s cin = s cin := by
  have hab : a ≠ b := hba.symm
  have hcinb : cin ≠ b := hbcin.symm
  have haco : a ≠ cout := hcouta.symm
  have hbco : b ≠ cout := hcoutb.symm
  have hcinco : cin ≠ cout := hcoutcin.symm
  have hcina : cin ≠ a := hacin.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fullAdder, denote_cons, denote_nil] <;>
    simp_all [denoteGate] <;>
    cases s a <;> cases s b <;> cases s cin <;> decide

/-! ### Derived cost of the gadget -/

/-- **Derived cost of the full adder** (from the gate list, via `circuitCost`): two Toffolis, two
CNOTs, Toffoli depth two, everything else zero. Not asserted — read off `[CCX, CX, CCX, CX]`. -/
theorem fullAdder_cost (a b cin cout : Fin n) :
    circuitCost (fullAdder a b cin cout)
      = { qubits := n, ancilla := 0, toffoli := 2, toffoliDepth := 2,
          cnot := 2, tCount := 0, meas := 0 } := by
  simp [circuitCost, fullAdder, gateCost]

@[simp] theorem fullAdder_toffoli (a b cin cout : Fin n) :
    (circuitCost (fullAdder a b cin cout)).toffoli = 2 := by
  rw [fullAdder_cost]

@[simp] theorem fullAdder_cnot (a b cin cout : Fin n) :
    (circuitCost (fullAdder a b cin cout)).cnot = 2 := by
  rw [fullAdder_cost]

/-! ### Ripple adder (general `n`): linear cost -/

/-- An `k`-slice ripple adder: the concatenation of `fullAdder` gadgets, one per quadruple of wires
in `slices`. A quadruple is `(a, b, cin, cout)`. The wire layout (which carries feed which sums) is a
Pass-2 concern; Pass 1 fixes only the *gate list* (hence the cost). -/
def rippleAdder (slices : List (Fin n × Fin n × Fin n × Fin n)) : Circuit n :=
  slices.flatMap (fun q => fullAdder q.1 q.2.1 q.2.2.1 q.2.2.2)

@[simp] theorem rippleAdder_nil : rippleAdder ([] : List (Fin n × Fin n × Fin n × Fin n)) = [] := rfl

/-- **Ripple-adder Toffoli count is linear in the number of slices.** Each slice contributes exactly
two Toffolis (`fullAdder_toffoli`); the count adds over the concatenation
(`cost_comp_toffoli_count`). Proved by induction over the slice list, composing the Tranche-1
lemma — not by re-deriving the sum. -/
theorem rippleAdder_toffoli (slices : List (Fin n × Fin n × Fin n × Fin n)) :
    (circuitCost (rippleAdder slices)).toffoli = 2 * slices.length := by
  induction slices with
  | nil => simp
  | cons q rest ih =>
    have hsplit : rippleAdder (q :: rest)
        = fullAdder q.1 q.2.1 q.2.2.1 q.2.2.2 ++ rippleAdder rest := by
      simp [rippleAdder, List.flatMap_cons]
    rw [hsplit, cost_comp_toffoli_count, fullAdder_toffoli, ih, List.length_cons]
    omega

/-- **Ripple-adder CNOT count is linear in the number of slices.** Same route via
`cost_comp_cnot_count` + `fullAdder_cnot`. -/
theorem rippleAdder_cnot (slices : List (Fin n × Fin n × Fin n × Fin n)) :
    (circuitCost (rippleAdder slices)).cnot = 2 * slices.length := by
  induction slices with
  | nil => simp
  | cons q rest ih =>
    have hsplit : rippleAdder (q :: rest)
        = fullAdder q.1 q.2.1 q.2.2.1 q.2.2.2 ++ rippleAdder rest := by
      simp [rippleAdder, List.flatMap_cons]
    rw [hsplit, cost_comp_cnot_count, fullAdder_cnot, ih, List.length_cons]
    omega

end Reversible
