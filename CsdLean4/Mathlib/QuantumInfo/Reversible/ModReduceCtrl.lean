import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduce

/-!
# Reversible modular reduction — the complete single-step reduce circuit  (ECDLP Phase 2, Stage S6.3a)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

S4 (`ModReduce.lean`) verified the comparison-as-carry-out primitive and the `x ≥ N` reduce *value*
(`rippleCirc_modReduce_ge`), but left **the flag-controlled wrapper and the `x < N` branch** as
*documented* cost, not as an exhibited circuit (`ResourceBounds.modReduceToffoli` is a documented
estimate, not derived from a reduce circuit). This module **closes that residue**: it exhibits and
proves the complete single-step modular reduction circuit, **both branches**, from already-verified
primitives only.

## The circuit (`modReduce`)

For `x` in register `B` with `x < 2N` (and `x < 2ⁿ`, `N ≤ 2ⁿ`):

```
modReduce L = rippleCirc L1 ++ [Gate.X flag] ++ cRippleCirc L2
```

* **Step 1** `rippleCirc L1` (`A1` preset to `2ⁿ − N`, `B`, fresh carry chain `C1`): adds the
  complement constant, so `B ← (x + 2ⁿ − N) mod 2ⁿ`, and `flag := C1 n` (the carry-out) becomes
  `decide (N ≤ x)` (`rippleCirc_correct` + `rippleCirc_carryout`).
* **Step 2** `X flag`: flips the flag to `decide (x < N) = ¬ decide (N ≤ x)`.
* **Step 3** `cRippleCirc L2` (`A2` preset to `N`, same `B`, **second** fresh carry chain `C2`,
  `ctrl := flag`, fresh ancilla `anc`): controlled add-back of `N`, conditional on `x < N`
  (`cRippleCirc_correct`).

The arithmetic (verified in `modReduce_correct`):
* `x ≥ N`: flag clears, no add-back; step-1 value `(x + 2ⁿ − N) mod 2ⁿ = x − N = x mod N`
  (using `N ≤ x < 2ⁿ` and S4's `mod_eq_sub_of_le_of_lt_two_mul`).
* `x < N`: flag sets; step-1 value is `x + 2ⁿ − N` (no wrap, since `x < N ≤ 2ⁿ`), then
  `+ N mod 2ⁿ = (x + 2ⁿ) mod 2ⁿ = x = x mod N`.

## What is NEW vs S4

S4's `rippleCirc_modReduce_ge` handled only the `x ≥ N` branch and *no* control — the reduce was
the bare adder, correct only when a subtract was actually needed. This module does **both branches in
one reversible pass**, with the comparison flag *controlling* the conditional add-back via S2's
`cRippleCirc`. So: comparison VERIFIED (S4), `x ≥ N` reduce VERIFIED (S4), and now the
flag-controlled wrapper + the `x < N` identity branch are **exhibited circuits, VERIFIED** (S6.3a) —
the documented residue of S4 §"Documented residue" is closed.

## Honest cost

`modReduceCtrl_toffoli` derives `2n + 8n = 10n` Toffolis from the exhibited gate list (step-1 ripple
`2n`, the `X` flip `0`, step-3 controlled ripple `8n` via `cRippleCirc_toffoli`). This is **heavier**
than S4's *documented* estimate `modReduceToffoli n = 4n`: the controlled add-back is `8n` (the
quantum×quantum overhead of S2, `4×` the `2n` of an uncontrolled add), not the `~2n` an idealised
in-place subtract would suggest. That is the honest cost of a **verified** reduction (compare-and-
conditional-subtract, both branches, in the 2-control DSL) versus S4's documented uncontrolled-add
estimate.

## Remaining residue (named, not built)

1. **Cleanup / reversibility (S6.3b concern).** The comparison flag `C1 n` is left holding
   `decide (x < N)`, the step-1 carry chain `C1` holds garbage, and `C2`/`anc` are restored clean by
   `cRippleCirc` but `C1`/`flag` are not uncomputed. The *value* correctness of `B` holds regardless
   (`modReduce_correct`), but **in-place reuse inside a multiply** needs the standard
   recompute-and-uncompute of the flag and step-1 carries. Naming, not building, that uncompute pass
   here.
2. **Full product reduction.** A `2w`-bit product (`x` up to `~N²`) is reduced by the multi-step /
   interleaved schedule that keeps the accumulator `< 2N` and applies this primitive each step. This
   module is the **single-step (`x < 2N`) primitive** that schedule iterates; the full modular
   multiply is S6.3b.
-/

namespace Reversible

variable {m n : ℕ}

/-- A single-step modular-reduction layout on `Fin m` for `n`-bit registers. Bundles:
* `B` — the data register (holds `x`, overwritten with `x mod N`);
* `A1` — the step-1 constant register (preset to `2ⁿ − N`), with fresh carry chain `C1`
  (whose output wire `C1 n` is the comparison **flag**);
* `A2` — the step-3 constant register (preset to `N`), with a **second** fresh carry chain `C2`;
* `anc` — the shared clean ancilla for the controlled add-back.

The fields are pure wire geometry (pairwise disjointness + per-range bounded injectivity), mirroring
the `RippleLayout`/`CRippleLayout` discipline. The injectivity fields are **bounded** (`< n` for
registers, `< n + 1` for carry chains) exactly as `MulLayout`/`CMulLayout` — an unbounded `ℕ → Fin m`
injectivity field is uninhabitable and would make the theorem vacuous. -/
structure ModReduceLayout (m n : ℕ) where
  /-- Data register: holds `x`, overwritten with `x mod N`. -/
  B : ℕ → Fin m
  /-- Step-1 constant register (preset to `2ⁿ − N`). -/
  A1 : ℕ → Fin m
  /-- Step-1 carry chain; `C1 n` is the comparison flag (the control of step 3). -/
  C1 : ℕ → Fin m
  /-- Step-3 constant register (preset to `N`). -/
  A2 : ℕ → Fin m
  /-- Step-3 carry chain (distinct from `C1`). -/
  C2 : ℕ → Fin m
  /-- Shared clean ancilla for the controlled add-back. -/
  anc : Fin m
  -- step-1 register geometry (A1, B, C1 pairwise disjoint + injective)
  hBA1 : ∀ i j, B i ≠ A1 j
  hBC1 : ∀ i j, B i ≠ C1 j
  hA1C1 : ∀ i j, A1 i ≠ C1 j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hA1inj : ∀ i j, i < n → j < n → A1 i = A1 j → i = j
  hC1inj : ∀ i j, i < n + 1 → j < n + 1 → C1 i = C1 j → i = j
  -- step-3 register geometry (A2, B, C2 pairwise disjoint + injective)
  hBA2 : ∀ i j, B i ≠ A2 j
  hBC2 : ∀ i j, B i ≠ C2 j
  hA2C2 : ∀ i j, A2 i ≠ C2 j
  hA2inj : ∀ i j, i < n → j < n → A2 i = A2 j → i = j
  hC2inj : ∀ i j, i < n + 1 → j < n + 1 → C2 i = C2 j → i = j
  -- the flag (= C1 n) controls step 3; disjoint from step-3 registers
  hflagA2 : ∀ j, C1 n ≠ A2 j
  hflagB : ∀ j, C1 n ≠ B j
  hflagC2 : ∀ j, C1 n ≠ C2 j
  hflaganc : C1 n ≠ anc
  -- the ancilla is disjoint from step-3 registers
  hancA2 : ∀ j, anc ≠ A2 j
  hancB : ∀ j, anc ≠ B j
  hancC2 : ∀ j, anc ≠ C2 j
  -- cross-step disjointness: step-3 wires (A2, C2, anc) are untouched by step 1 (A1, C1)
  -- and step 2 (the X on C1 n). [B is shared between steps by design.]
  hA2A1 : ∀ i j, A2 i ≠ A1 j
  hA2C1 : ∀ i j, A2 i ≠ C1 j
  hC2A1 : ∀ i j, C2 i ≠ A1 j
  hC2C1 : ∀ i j, C2 i ≠ C1 j
  hancA1 : ∀ j, anc ≠ A1 j
  hancC1 : ∀ j, anc ≠ C1 j

variable {L : ModReduceLayout m n}

/-- Step 1 as a `RippleLayout`: register `A1` + data `B` + carry chain `C1`. -/
def ModReduceLayout.stepOne (L : ModReduceLayout m n) : RippleLayout m n where
  A := L.A1
  B := L.B
  C := L.C1
  hAB i j := (L.hBA1 j i).symm
  hAC := L.hA1C1
  hBC := L.hBC1
  hAinj := L.hA1inj
  hBinj := L.hBinj
  hCinj := L.hC1inj

/-- Step 3 as a `CRippleLayout`: register `A2` + data `B` + carry chain `C2`, controlled on the flag
`C1 n`, with the shared ancilla. -/
def ModReduceLayout.stepThree (L : ModReduceLayout m n) : CRippleLayout m n where
  A := L.A2
  B := L.B
  C := L.C2
  ctrl := L.C1 n
  anc := L.anc
  hAB i j := (L.hBA2 j i).symm
  hAC := L.hA2C2
  hBC := L.hBC2
  hAinj := L.hA2inj
  hBinj := L.hBinj
  hCinj := L.hC2inj
  hctrlA := L.hflagA2
  hctrlB := L.hflagB
  hctrlC := L.hflagC2
  hctrlanc := L.hflaganc
  hancA := L.hancA2
  hancB := L.hancB
  hancC := L.hancC2

/-- **The single-step modular-reduction circuit.** `rippleCirc` (add complement `2ⁿ − N`, produce the
comparison flag) `++ [X flag]` (flip flag to `x < N`) `++ cRippleCirc` (controlled add-back of `N`). -/
def modReduce (L : ModReduceLayout m n) : Circuit m :=
  rippleCirc L.stepOne ++ [Gate.X (L.C1 n)] ++ cRippleCirc L.stepThree

/-! ### Frame: step-3 inputs survive steps 1 and 2

Step 1 (`rippleCirc L.stepOne`) touches only `{A1 k, B k, C1 k}` and step 2 (`X (C1 n)`) only
`{C1 n}`. The step-3 carry chain `C2`, constant `A2`, and ancilla `anc` are disjoint from those, so
their values pass through steps 1 + 2 unchanged. -/

/-- The data-register window `B` is untouched by the flag flip (step 2): `C1 n ≠ B j`. -/
theorem modReduce_stepTwo_preserves_B (s : State m) (j : ℕ) :
    denoteGate (Gate.X (L.C1 n)) s (L.B j) = s (L.B j) := by
  apply denoteGate_apply_of_not_mem
  simp only [gateWires, Finset.mem_singleton]
  exact fun h => (L.hflagB j) h.symm

/-- Steps 1 + 2 leave the step-3 carry chain `C2 j` at its initial value. -/
theorem modReduce_steps12_preserves_C2 (s : State m) (j : ℕ) :
    denoteGate (Gate.X (L.C1 n)) (denote (rippleCirc L.stepOne) s) (L.C2 j) = s (L.C2 j) := by
  rw [denoteGate_apply_of_not_mem (by
    simp only [gateWires, Finset.mem_singleton]; exact fun h => (L.hC2C1 j n) h)]
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, hk, hgk⟩ := hg
  rw [List.mem_range] at hk
  simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, List.mem_cons, List.not_mem_nil,
    or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl <;>
    simp [gateWires, L.hC2A1 j k, L.hC2C1 j k, L.hC2C1 j (k + 1), (L.hBC2 k j).symm]

/-- Steps 1 + 2 leave the step-3 constant register `A2 j` at its initial value. -/
theorem modReduce_steps12_preserves_A2 (s : State m) (j : ℕ) :
    denoteGate (Gate.X (L.C1 n)) (denote (rippleCirc L.stepOne) s) (L.A2 j) = s (L.A2 j) := by
  rw [denoteGate_apply_of_not_mem (by
    simp only [gateWires, Finset.mem_singleton]; exact fun h => (L.hflagA2 j) h.symm)]
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, hk, hgk⟩ := hg
  rw [List.mem_range] at hk
  simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, List.mem_cons, List.not_mem_nil,
    or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl <;>
    simp [gateWires, L.hA2A1 j k, L.hA2C1 j k, L.hA2C1 j (k + 1), (L.hBA2 k j).symm]

/-- Steps 1 + 2 leave the shared ancilla `anc` at its initial value. -/
theorem modReduce_steps12_preserves_anc (s : State m) :
    denoteGate (Gate.X (L.C1 n)) (denote (rippleCirc L.stepOne) s) L.anc = s L.anc := by
  rw [denoteGate_apply_of_not_mem (by
    simp only [gateWires, Finset.mem_singleton]; exact fun h => L.hflaganc h.symm)]
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, hk, hgk⟩ := hg
  rw [List.mem_range] at hk
  simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, List.mem_cons, List.not_mem_nil,
    or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl <;>
    simp [gateWires, L.hancA1 k, L.hancC1 k, L.hancC1 (k + 1), L.hancB k]

/-! ### Value correctness, both branches -/

/-- **The complete single-step modular reduction — both branches, verified from the exhibited
circuit.** For a disjoint-wire `ModReduceLayout` with the step-1 carry chain `C1`, the step-3 carry
chain `C2`, and the ancilla `anc` all initialised `false`, register `A1` preset to `2ⁿ − N`, register
`A2` preset to `N`, and data `B` holding `x` with `N ≤ 2ⁿ`, `x < 2ⁿ`, `x < 2N`: the circuit
`modReduce L` leaves `B` holding `x mod N`.

Proof. Step 1 (`rippleCirc_correct`) writes `(x + 2ⁿ − N) mod 2ⁿ` to `B` and sets the flag
`C1 n = decide (N ≤ x)` (`rippleCirc_carryout`); step 2 flips it to `decide (x < N)`; step 3
(`cRippleCirc_correct`) adds `N` back iff the flag is set. The two branches:
* `x ≥ N` (flag clear): step-1 value `(x + 2ⁿ − N) mod 2ⁿ = x − N` (`N ≤ x < 2ⁿ`), and
  `x − N = x mod N` (`mod_eq_sub_of_le_of_lt_two_mul`); add-back skipped.
* `x < N` (flag set): step-1 value `x + 2ⁿ − N` (no wrap, `x < N ≤ 2ⁿ`), then `+ N mod 2ⁿ =
  (x + 2ⁿ) mod 2ⁿ = x = x mod N`.

This closes S4's documented residue: comparison + conditional-subtract + **both branches**, derived
from circuits, not documented. -/
theorem modReduce_correct (L : ModReduceLayout m n) (s : State m)
    (hC1 : ∀ j, s (L.C1 j) = false) (hC2 : ∀ j, s (L.C2 j) = false) (hanc : s L.anc = false)
    {N : ℕ} (hN : N ≤ 2 ^ n) (hA1 : regValRange L.A1 s n = 2 ^ n - N)
    (hA2 : regValRange L.A2 s n = N) (hx2N : regValRange L.B s n < 2 * N) :
    regValRange L.B (denote (modReduce L) s) n = regValRange L.B s n % N := by
  set x := regValRange L.B s n with hx
  have hxlt : x < 2 ^ n := regValRange_lt _ _ _
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with hN0 | hN0
    · subst hN0; omega
    · exact hN0
  -- abbreviations for the three stages
  set s1 := denote (rippleCirc L.stepOne) s with hs1def
  set s2 := denoteGate (Gate.X (L.C1 n)) s1 with hs2def
  -- the circuit decomposes as s ↦ s1 ↦ s2 ↦ final
  have hdenote : denote (modReduce L) s = denote (cRippleCirc L.stepThree) s2 := by
    rw [modReduce, denote_append, denote_append, denote_cons, denote_nil, ← hs1def, ← hs2def]
  -- STEP 1 value of B (= step-one register B = L.B)
  have hB1 : regValRange L.B s1 n = (regValRange L.A1 s n + x) % 2 ^ n := by
    have := rippleCirc_correct L.stepOne s (by intro j; exact hC1 j)
    simpa [ModReduceLayout.stepOne, hx] using this
  rw [hA1] at hB1
  -- STEP 1 flag (= carry-out C1 n) = decide (N ≤ x)
  have hflag1 : s1 (L.C1 n) = decide (N ≤ x) := by
    have hco := rippleCirc_carryout L.stepOne s (by intro j; exact hC1 j)
    simp only [ModReduceLayout.stepOne, hs1def] at hco ⊢
    rw [hco]
    apply decide_eq_decide.mpr
    rw [hA1]; omega
  -- STEP 2: flag flips to decide (x < N); B preserved
  have hflag2 : s2 (L.C1 n) = decide (x < N) := by
    rw [hs2def, denoteGate]
    simp only [Function.update_self, hflag1, ← decide_not]
    apply decide_eq_decide.mpr; omega
  have hB2 : regValRange L.B s2 n = regValRange L.B s1 n := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hs2def, modReduce_stepTwo_preserves_B]
  -- STEP 2: A2 register = N (preserved across steps 1,2)
  have hA2_2 : regValRange L.A2 s2 n = N := by
    rw [← hA2]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs2def, modReduce_steps12_preserves_A2]
  -- STEP 2: C2 carry chain still false
  have hC2_2 : ∀ j, s2 (L.C2 j) = false := by
    intro j
    rw [hs2def, modReduce_steps12_preserves_C2 s j]; exact hC2 j
  -- STEP 2: anc still false
  have hanc_2 : s2 L.anc = false := by
    rw [hs2def, modReduce_steps12_preserves_anc]; exact hanc
  -- STEP 3: controlled add-back of N, conditional on the flag
  have hstep3 := cRippleCirc_correct L.stepThree s2 hC2_2 hanc_2
  rw [hdenote]
  show regValRange L.stepThree.B (denote (cRippleCirc L.stepThree) s2) n = x % N
  rw [hstep3]
  show (if s2 (L.C1 n) then (regValRange L.A2 s2 n + regValRange L.B s2 n) % 2 ^ n
      else regValRange L.B s2 n) = x % N
  rw [hflag2, hA2_2, hB2, hB1]
  -- now branch on x < N
  by_cases hlt : x < N
  · -- x < N: ctrl set, add N back
    simp only [hlt, decide_true, if_true]
    -- step-1 value = (2ⁿ − N) + x, no wrap since x < N ≤ 2ⁿ
    have hnowrap : (2 ^ n - N + x) % 2 ^ n = 2 ^ n - N + x := Nat.mod_eq_of_lt (by omega)
    rw [hnowrap]
    -- N + (2ⁿ − N + x) = 2ⁿ + x ≡ x  (mod 2ⁿ)
    have hsum : N + (2 ^ n - N + x) = 2 ^ n + x := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt hxlt]
    exact (Nat.mod_eq_of_lt hlt).symm
  · -- x ≥ N: ctrl clear, no add-back; step-1 value is x − N = x mod N
    have hge : N ≤ x := by omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    -- (2ⁿ − N + x) % 2ⁿ = x − N
    have hsum : 2 ^ n - N + x = 2 ^ n + (x - N) := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    exact (mod_eq_sub_of_le_of_lt_two_mul hge hx2N).symm

/-- **The reducer output is a genuine residue in `[0, N)`.** A direct corollary of
`modReduce_correct` and `Nat.mod_lt`: the property a modular reducer must have. -/
theorem modReduce_in_range (L : ModReduceLayout m n) (s : State m)
    (hC1 : ∀ j, s (L.C1 j) = false) (hC2 : ∀ j, s (L.C2 j) = false) (hanc : s L.anc = false)
    {N : ℕ} (hNpos : 0 < N) (hN : N ≤ 2 ^ n) (hA1 : regValRange L.A1 s n = 2 ^ n - N)
    (hA2 : regValRange L.A2 s n = N) (hx2N : regValRange L.B s n < 2 * N) :
    regValRange L.B (denote (modReduce L) s) n < N := by
  rw [modReduce_correct L s hC1 hC2 hanc hN hA1 hA2 hx2N]
  exact Nat.mod_lt _ hNpos

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the single-step reduce circuit**: `10n` Toffolis, from the exhibited gate
list. Step 1 (`rippleCirc`) is `2n` (`rippleAdder_toffoli`-style, here read via the same ripple count),
the `X` flip is `0`, and step 3 (`cRippleCirc`) is `8n` (`cRippleCirc_toffoli`); composed through the
Tranche-1 additivity `cost_comp_toffoli_count`. This is heavier than S4's *documented*
`modReduceToffoli n = 4n`: the **verified** controlled add-back costs `8n` (the quantum×quantum
overhead of S2, `4×` an uncontrolled add), the honest price of an exhibited both-branch reduction. -/
theorem modReduceCtrl_toffoli (L : ModReduceLayout m n) :
    (circuitCost (modReduce L)).toffoli = 10 * n := by
  rw [modReduce, cost_comp_toffoli_count, cost_comp_toffoli_count, cRippleCirc_toffoli]
  -- step 1 ripple: 2n;  X flip: 0
  have hstep1 : (circuitCost (rippleCirc L.stepOne)).toffoli = 2 * n := by
    rw [rippleCirc, ripplePrefix]
    suffices h : ∀ k, (circuitCost ((List.range k).flatMap (rippleSlice L.stepOne))).toffoli = 2 * k
      from h n
    intro k
    induction k with
    | zero => simp [circuitCost]
    | succ k ih =>
      have hsplit : (List.range (k + 1)).flatMap (rippleSlice L.stepOne)
          = (List.range k).flatMap (rippleSlice L.stepOne) ++ rippleSlice L.stepOne k := by
        rw [List.range_succ, List.flatMap_append]; simp
      rw [hsplit, cost_comp_toffoli_count, ih, rippleSlice, fullAdder_toffoli]
      omega
  have hX : (circuitCost ([Gate.X (L.C1 n)] : Circuit m)).toffoli = 0 := by
    simp [circuitCost, gateCost]
  rw [hstep1, hX]
  omega

/-! ### Non-vacuity witness

A concrete 2-bit reduce layout on `Fin 13`:
* data `B → {0,1}`, step-1 constant `A1 → {2,3}`, step-1 carry chain `C1 → {4,5,6}`,
* step-3 constant `A2 → {7,8}`, step-3 carry chain `C2 → {9,10,11}`, ancilla `12`.

This exhibits that `ModReduceLayout` is inhabited (the bounded-injectivity bundle is satisfiable),
so the headlines are not vacuously quantified. The concrete computations below run the reducer on
`n = 2, N = 3` at two fully-specified input states, checking `x = 3 ↦ 0` (the `x ≥ N` subtract
branch) and `x = 2 ↦ 2` (the `x < N` identity branch). [The spec's illustrative `x = 5 ↦ 2` needs
`n = 3`: `5 < 2³ = 8`; at `n = 2`, `x < 2² = 4`, so `5` is not representable in two wires.] -/

/-- A concrete 2-bit reduce layout on `Fin 13`. -/
def modReduceLayout2 : ModReduceLayout 13 2 where
  B i := if i = 0 then 0 else 1
  A1 i := if i = 0 then 2 else 3
  C1 i := if i = 0 then 4 else if i = 1 then 5 else 6
  A2 i := if i = 0 then 7 else 8
  C2 i := if i = 0 then 9 else if i = 1 then 10 else 11
  anc := 12
  hBA1 i j := by split_ifs <;> decide
  hBC1 i j := by split_ifs <;> decide
  hA1C1 i j := by split_ifs <;> decide
  hBinj i j hi hj h := by split_ifs at h <;> omega
  hA1inj i j hi hj h := by split_ifs at h <;> omega
  hC1inj i j hi hj h := by split_ifs at h <;> omega
  hBA2 i j := by split_ifs <;> decide
  hBC2 i j := by split_ifs <;> decide
  hA2C2 i j := by split_ifs <;> decide
  hA2inj i j hi hj h := by split_ifs at h <;> omega
  hC2inj i j hi hj h := by split_ifs at h <;> omega
  hflagA2 j := by split_ifs <;> decide
  hflagB j := by split_ifs <;> decide
  hflagC2 j := by split_ifs <;> decide
  hflaganc := by decide
  hancA2 j := by split_ifs <;> decide
  hancB j := by split_ifs <;> decide
  hancC2 j := by split_ifs <;> decide
  hA2A1 i j := by split_ifs <;> decide
  hA2C1 i j := by split_ifs <;> decide
  hC2A1 i j := by split_ifs <;> decide
  hC2C1 i j := by split_ifs <;> decide
  hancA1 j := by split_ifs <;> decide
  hancC1 j := by split_ifs <;> decide

/-- The headline is non-vacuous: it applies to the concrete `modReduceLayout2`. -/
example (s : State 13) (hC1 : ∀ j, s (modReduceLayout2.C1 j) = false)
    (hC2 : ∀ j, s (modReduceLayout2.C2 j) = false) (hanc : s modReduceLayout2.anc = false)
    (hA1 : regValRange modReduceLayout2.A1 s 2 = 2 ^ 2 - 3)
    (hA2 : regValRange modReduceLayout2.A2 s 2 = 3)
    (hx2N : regValRange modReduceLayout2.B s 2 < 2 * 3) :
    regValRange modReduceLayout2.B (denote (modReduce modReduceLayout2) s) 2
      = regValRange modReduceLayout2.B s 2 % 3 := by
  have hN : (3 : ℕ) ≤ 2 ^ 2 := by decide
  exact modReduce_correct modReduceLayout2 s hC1 hC2 hanc hN hA1 hA2 hx2N

/-- Concrete input state for `n = 2, N = 3`: data `B = x` (wires `0,1`), `A1 = 1 = 2² − 3`
(wire `2`), `A2 = 3` (wires `7,8`), all carries / ancilla `false`. Parameterised by the two data
bits `b0, b1` of `x`. -/
def modReduceState2 (b0 b1 : Bool) : State 13 := fun w =>
  if w = 0 then b0 else if w = 1 then b1
  else if w = 2 then true                 -- A1 bit 0 (value 1 = 2² − 3)
  else if w = 7 then true else if w = 8 then true  -- A2 = 3
  else false

/-- The hypotheses of `modReduce_correct` hold at `modReduceState2 b0 b1` (carries/ancilla clear,
`A1 = 1`, `A2 = 3`), for any data bits. The `regValRange` register-value preconditions are concrete
sums, discharged by `decide`. -/
private theorem modReduceState2_pre (b0 b1 : Bool) :
    (∀ j, modReduceState2 b0 b1 (modReduceLayout2.C1 j) = false)
      ∧ (∀ j, modReduceState2 b0 b1 (modReduceLayout2.C2 j) = false)
      ∧ modReduceState2 b0 b1 modReduceLayout2.anc = false
      ∧ regValRange modReduceLayout2.A1 (modReduceState2 b0 b1) 2 = 2 ^ 2 - 3
      ∧ regValRange modReduceLayout2.A2 (modReduceState2 b0 b1) 2 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j; show modReduceState2 b0 b1 (modReduceLayout2.C1 j) = false
    simp only [modReduceLayout2]; split_ifs <;> rfl
  · intro j; show modReduceState2 b0 b1 (modReduceLayout2.C2 j) = false
    simp only [modReduceLayout2]; split_ifs <;> rfl
  · rfl
  · simp [regValRange, Finset.sum_range_succ, modReduceLayout2, modReduceState2]
  · simp [regValRange, Finset.sum_range_succ, modReduceLayout2, modReduceState2]

/-- **Concrete run, the `x ≥ N` subtract branch:** `x = 3 ↦ 3 mod 3 = 0`. The full reduce circuit
on the explicit 13-wire input leaves register `B` holding `0`. -/
example : regValRange modReduceLayout2.B (denote (modReduce modReduceLayout2)
    (modReduceState2 true true)) 2 = 0 := by
  obtain ⟨hC1, hC2, hanc, hA1, hA2⟩ := modReduceState2_pre true true
  have hx : regValRange modReduceLayout2.B (modReduceState2 true true) 2 = 3 := by
    simp [regValRange, Finset.sum_range_succ, modReduceLayout2, modReduceState2]
  have := modReduce_correct modReduceLayout2 (modReduceState2 true true) hC1 hC2 hanc
    (by decide) hA1 hA2 (by rw [hx]; decide)
  rw [this, hx]

/-- **Concrete run, the `x < N` identity branch:** `x = 2 ↦ 2 mod 3 = 2`. The add-back of `N` is
flag-suppressed, leaving register `B` holding `2`. -/
example : regValRange modReduceLayout2.B (denote (modReduce modReduceLayout2)
    (modReduceState2 false true)) 2 = 2 := by
  obtain ⟨hC1, hC2, hanc, hA1, hA2⟩ := modReduceState2_pre false true
  have hx : regValRange modReduceLayout2.B (modReduceState2 false true) 2 = 2 := by
    simp [regValRange, Finset.sum_range_succ, modReduceLayout2, modReduceState2]
  have := modReduce_correct modReduceLayout2 (modReduceState2 false true) hC1 hC2 hanc
    (by decide) hA1 hA2 (by rw [hx]; decide)
  rw [this, hx]

end Reversible
