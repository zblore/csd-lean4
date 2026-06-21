import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

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

## Stage B.1 — the per-step accumulation correctness (landed below)

* `regValRange_split` — split a register readout at an offset (`low + 2^i · window`), the tool relating
  a windowed add to the full accumulator value with no division.
* `rippleCirc_preserves_external` — a ripple circuit preserves any wire disjoint from its layout (the
  frame lemma at circuit granularity).
* `accStep` — **THE per-step heart**: one full-remaining-width ripple add of the multiplicand (value
  `Yv`) into the accumulator window `Acc[i, W)` increases the full accumulator value by exactly
  `2^i · Yv` (carry propagating through the whole upper accumulator; low `i` bits preserved; no overflow).

## Stage B.2 target (NOT claimed yet)

The end-to-end `Acc = (a · Y)` identity — the fold of `accStep` over all set bits of `a` (a multi-step
induction threading `Y`-preservation and carry-freshness through the composition; each step has a
different width `W - i`, hence a dependent-width fold) — plus a concrete inhabited `MulLayout` witness,
and then the mod-`N` reduction. Stage B.1 proves the single shifted-add accumulation; nothing below
claims the full `a · Y` identity yet.
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

/-! ### Stage B: multiplication correctness — arithmetic tools -/

/-- **Split a register readout at an offset.** The low-`i` value plus `2^i` times the value of the
window starting at `i`. The key tool relating a windowed add to the full accumulator value (no
division). -/
theorem regValRange_split {m : ℕ} (f : ℕ → Fin m) (s : State m) (i k : ℕ) (h : i ≤ k) :
    regValRange f s k
      = regValRange f s i + 2 ^ i * regValRange (fun j => f (i + j)) s (k - i) := by
  simp only [regValRange]
  rw [← Finset.sum_range_add_sum_Ico (fun j => (s (f j)).toNat * 2 ^ j) h]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_add]
  exact mul_left_comm _ _ _

/-- **A ripple circuit preserves any wire external to its layout** (disjoint from all of `A`, `B`, `C`).
The frame lemma at circuit granularity, lifting `denote_apply_of_forall_not_mem`: every gate of
`rippleCirc L` has wires among `L.A`, `L.B`, `L.C`, so a wire avoiding all three is untouched. -/
theorem rippleCirc_preserves_external {w : ℕ} (L : RippleLayout m w) (s : State m) (x : Fin m)
    (hA : ∀ k, k < w → x ≠ L.A k) (hB : ∀ k, k < w → x ≠ L.B k)
    (hC : ∀ k, k < w + 1 → x ≠ L.C k) :
    denote (rippleCirc L) s x = s x := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, hk, hgk⟩ := hg
  rw [List.mem_range] at hk
  simp only [rippleSlice, fullAdder, List.mem_cons, List.not_mem_nil, or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl <;>
    simp [gateWires, hA k hk, hB k hk, hC k (by omega), hC (k + 1) (by omega)]

/-- **Single accumulation step.** One full-remaining-width ripple add of the multiplicand (value `Yv`,
read by `L.A`) into the accumulator window `Acc[i, W)` increases the full accumulator value by
`2^i · Yv` — provided the add does not overflow the window. The carry propagates through the whole
upper accumulator (width `w = W - i`), so nothing is dropped; the low `i` bits are preserved. -/
theorem accStep {w : ℕ} (L : RippleLayout m w) (Acc : ℕ → Fin m) (s : State m)
    (i W : ℕ) (hw : w = W - i) (hiW : i ≤ W)
    (hB : ∀ k, L.B k = Acc (i + k))
    (hAccinj : ∀ j k, j < W → k < W → Acc j = Acc k → j = k)
    (hAccA : ∀ j, j < i → ∀ k, Acc j ≠ L.A k)
    (hAccC : ∀ j, j < i → ∀ k, Acc j ≠ L.C k)
    (hcarry : ∀ j, s (L.C j) = false)
    (Yv : ℕ) (hYv : regValRange L.A s w = Yv)
    (hno : Yv + regValRange (fun k => Acc (i + k)) s w < 2 ^ w) :
    regValRange Acc (denote (rippleCirc L) s) W
      = regValRange Acc s W + 2 ^ i * Yv := by
  have hWi : W - i = w := hw.symm
  have hcorr := rippleCirc_correct L s hcarry
  have hBwin : L.B = fun k => Acc (i + k) := funext hB
  rw [hBwin, hYv, Nat.mod_eq_of_lt hno] at hcorr
  have hlow : regValRange Acc (denote (rippleCirc L) s) i = regValRange Acc s i := by
    simp only [regValRange]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [rippleCirc_preserves_external L s (Acc j) (fun k _ => hAccA j hj k) ?_
        (fun k _ => hAccC j hj k)]
    intro k hk
    rw [hB]
    exact fun h => absurd (hAccinj j (i + k) (by omega) (by omega) h) (by omega)
  rw [regValRange_split Acc (denote (rippleCirc L) s) i W hiW,
      regValRange_split Acc s i W hiW, hlow, hWi, hcorr]
  ring

end Reversible
