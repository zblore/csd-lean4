import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd
import Mathlib.Data.ZMod.Basic

/-!
# Reversible modular multiplication — semantic target + shift-and-add multiplier cost  (ECDLP Tranche 3, Stage A)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The multiplication layer of the reversible-circuit substrate
(`Circuit.lean` / `Cost.lean` / `ModAdd.lean`, `specs/ecdlp-resource-plan.md`). The semantic target is
**Shor's modular-multiplication oracle** `mulOracle : |y⟩ ↦ |a·y⟩` on `ZMod N` (a permutation when `a`
is a unit), which the corpus's `Empirical/QM/Algorithms/ShorCore.lean` carries with no gate-level
content. This tranche builds the missing reversible circuit + *derived* cost.

## What is proved here (Stage A)

* `mulConst` — the semantic target: the `ZMod N` map `y ↦ a · y`, with `mulConst_bijective` (a unit
  acts as a permutation — the reversibility that lets a circuit realise it).
* `multiplier` — the shift-and-add multiplier as the concatenation of a list of partial-product adder
  circuits, with **derived cost** `multiplier_toffoli` / `_cnot` (the total count is the list-sum of the
  block counts, composed through the Tranche-1 `cost_comp_*` lemmas — not annotated).
* `rippleCirc_toffoli` / `_cnot` — a ripple adder block costs `2 * n` Toffolis / CNOTs (derived), so a
  multiplier built from `m` width-`n` adders costs `2 * n * m` (`multiplier_ripple_toffoli`).
* The per-partial-product correctness is `ModAdd.rippleCirc_correct` (one shifted add); the building
  block is in hand.

## Stage B target (NOT claimed here)

The end-to-end accumulation correctness — that the exhibited shift-and-add multiplier leaves the
accumulator holding `(a · Y) mod 2 ^ W` — is **Stage B**: an induction over partial products, each step
a widened ripple add (carry propagating through the full upper accumulator), reusing `rippleCirc_correct`
and `rippleCirc_invariant`'s preservation of the multiplicand. The mod-`N` reduction (vs mod-`2^W`) is a
further stage. Stage A exhibits the circuit and proves its cost + the per-step correctness; nothing below
claims the full `a · Y` identity.
-/

namespace Reversible

variable {m : ℕ}

/-! ### Semantic target: the `ZMod N` multiplication oracle -/

/-- The modular-multiplication oracle action: `y ↦ a · y` on `ZMod N`. This is the permutation Shor's
`mulOracle` realises (for `a` a unit); the circuit below is its reversible implementation. -/
def mulConst (N : ℕ) (a : ZMod N) : ZMod N → ZMod N := fun y => a * y

/-- For a unit `a`, `mulConst` is a bijection (the reversibility that admits a reversible circuit):
its inverse is multiplication by `a⁻¹`. -/
theorem mulConst_bijective {N : ℕ} {a : ZMod N} (ha : IsUnit a) :
    Function.Bijective (mulConst N a) := by
  obtain ⟨u, rfl⟩ := ha
  constructor
  · intro x y h
    simp only [mulConst] at h
    calc x = (↑u⁻¹ * ↑u) * x := by rw [Units.inv_mul, one_mul]
      _ = ↑u⁻¹ * (↑u * x) := by rw [mul_assoc]
      _ = ↑u⁻¹ * (↑u * y) := by rw [h]
      _ = (↑u⁻¹ * ↑u) * y := by rw [mul_assoc]
      _ = y := by rw [Units.inv_mul, one_mul]
  · intro y
    refine ⟨↑u⁻¹ * y, ?_⟩
    simp only [mulConst]
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-! ### The shift-and-add multiplier circuit and its derived cost -/

/-- The shift-and-add multiplier: the concatenation of a list of partial-product adder circuits. Each
entry is the circuit that adds one shifted copy of the multiplicand into the accumulator; the multiplier
is their composition. (Which adders appear is fixed by the classical constant `a` — its set bits — so no
quantum control is needed; the gate list, hence the cost, is determined.) -/
def multiplier (adders : List (Circuit m)) : Circuit m := adders.flatMap id

@[simp] theorem multiplier_nil : multiplier ([] : List (Circuit m)) = [] := rfl

/-- **Multiplier Toffoli count is the sum of the block counts** (derived, composed through the
Tranche-1 `cost_comp_toffoli_count`). Not annotated — read off the concatenated gate list. -/
theorem multiplier_toffoli (adders : List (Circuit m)) :
    (circuitCost (multiplier adders)).toffoli
      = (adders.map (fun c => (circuitCost c).toffoli)).sum := by
  induction adders with
  | nil => simp
  | cons c rest ih =>
    have hsplit : multiplier (c :: rest) = c ++ multiplier rest := by
      simp [multiplier, List.flatMap_cons]
    rw [hsplit, cost_comp_toffoli_count, ih, List.map_cons, List.sum_cons]

/-- **Multiplier CNOT count is the sum of the block counts** (derived). -/
theorem multiplier_cnot (adders : List (Circuit m)) :
    (circuitCost (multiplier adders)).cnot
      = (adders.map (fun c => (circuitCost c).cnot)).sum := by
  induction adders with
  | nil => simp
  | cons c rest ih =>
    have hsplit : multiplier (c :: rest) = c ++ multiplier rest := by
      simp [multiplier, List.flatMap_cons]
    rw [hsplit, cost_comp_cnot_count, ih, List.map_cons, List.sum_cons]

/-- The first `k` slices of a ripple adder cost `2 * k` Toffolis (derived, induction on `k` composing
`cost_comp_toffoli_count` + `fullAdder_toffoli`). -/
theorem ripplePrefix_toffoli (L : RippleLayout m n) (k : ℕ) :
    (circuitCost (ripplePrefix L k)).toffoli = 2 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    have hsplit : ripplePrefix L (k + 1) = ripplePrefix L k ++ rippleSlice L k := by
      simp [ripplePrefix, List.range_succ, List.flatMap_append]
    rw [hsplit, cost_comp_toffoli_count, ih]
    simp only [rippleSlice, fullAdder_toffoli]
    omega

/-- A ripple adder block (`n` slices) costs `2 * n` Toffolis (derived). -/
theorem rippleCirc_toffoli (L : RippleLayout m n) :
    (circuitCost (rippleCirc L)).toffoli = 2 * n := ripplePrefix_toffoli L n

/-- A multiplier built from `m'` width-`n` ripple-adder blocks costs `2 * n * m'` Toffolis (derived).
The count is independent of whether the layouts are *valid* (disjoint-wire) — cost is syntactic, so this
is a cost statement, not a correctness one; the multiplier's correctness is Stage B. -/
theorem multiplier_ripple_toffoli {n : ℕ} (Ls : List (RippleLayout m n)) :
    (circuitCost (multiplier (Ls.map rippleCirc))).toffoli = 2 * n * Ls.length := by
  rw [multiplier_toffoli, List.map_map]
  have hconst : Ls.map ((fun c => (circuitCost c).toffoli) ∘ rippleCirc)
      = Ls.map (fun _ => 2 * n) := by
    apply List.map_congr_left
    intro L _; simp [Function.comp, rippleCirc_toffoli]
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

end Reversible
