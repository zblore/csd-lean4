/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd

/-!
# The minimal 1-Toffoli-per-carry (Gidney) reversible adder  (Tier-X / Build #35)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). **Pure Boolean-DSL
value-correctness**; the amplitude / measurement re-cost is `Empirical/QM/MeasurementGidneyAdder.lean`.

## Why this file exists

`#30` (`AndAdd.lean`) computes each carry into a fresh ancilla with a 3-Toffoli *preserving-majority*
cell (`andCarryCell`), so its adder costs `6n` Toffoli. The Cuccaro adder (`CuccaroAdd.lean`) restores
the carries in place with `2n` Toffoli but exposes **no fresh-AND attachment point** (its `uma` is a
unitary in-place restore), so the measurement-uncomputation gadget (`#31`) cannot drop its Toffolis.

This file supplies the **competitive** adder: the Gidney carry cell folds the carry into a fresh
ancilla with a **single Toffoli** (the addend bits are XOR-shifted by the carry-in and restored on the
reverse pass), and the reverse pass's per-carry Toffoli is a genuine `andUncompute`-shaped block — the
attachment point the measurement gadget eliminates. The unitary cost is `2n`; the measurement re-cost
(in `MeasurementGidneyAdder.lean`) drops the reverse pass to `0`, giving `n`.

## The carry cell (Gidney, one Toffoli)

`c_{i+1} = MAJ(a_i, b_i, c_i) = c_i ⊕ ((a_i ⊕ c_i) ∧ (b_i ⊕ c_i))`. The cell on `(a, b, cin, cout)`
(`cout` a fresh runway ancilla, init `false`) is
`majCell a b cin cout := [CX cin a, CX cin b, CCX a b cout, CX cin cout]`:

* `CX cin a` / `CX cin b` shift `a ← a ⊕ cin`, `b ← b ⊕ cin`;
* the **single** `CCX a b cout` writes `cout ← (a ⊕ cin) ∧ (b ⊕ cin)` (the fresh-AND temporary);
* `CX cin cout` adds the `cin` term, giving `cout = MAJ(a, b, cin)`.

`majCell_toffoli : … = 1` is the cost win. `majCell_correct` proves the Boolean semantics.

## The adder + correctness (the anti-hollow requirement)

`gidneyAdd L := gidneyForward L ++ andSumPass L.toAnd ++ inverse (gidneyForward L)` on a
`GidneyLayout` (addends `A`, `B`, sum register `S`, fresh carry chain `G`). The forward pass computes
every carry into `G` (XOR-shifting `A`, `B`); the sum pass writes `S i ← A i ⊕ B i ⊕ G i`
(`= a_i ⊕ b_i ⊕ c_i`, since the two `c_i` shifts cancel one); the reverse pass uncomputes the carries
and restores `A`, `B`, `G`.

* `gidneyAdd_correct : regValRange L.S (denote (gidneyAdd L) s) n = (A + B) % 2 ^ n` — **general `n`**.
* `gidneyAdd_ancilla_clean` / `gidneyAdd_preserves_A` / `_preserves_B` — the reverse pass restores the
  carry chain to `false` and the addends to their inputs.
* `gidneyAdd_toffoli : … = 2 * n` — `n` forward + `n` reverse, sum pass CNOT-only.

The sum-pass machinery, the carry arithmetic (`carryOf`, `adder_sum_identity`), and the circuit
locality lemmas (`denote_apply_of_forall_not_mem_target`, `denote_agree_on`) are **reused** from `#30`
via the projection `GidneyLayout.toAnd`.

## Honest scope

Value-correct + ancilla-clean over `regVal`, Boolean DSL only, general `n`. The Toffoli win over `#30`
(`6n`) is at the unitary level; the win over Cuccaro (`2n`) requires the measurement re-cost
(`MeasurementGidneyAdder.lean`), which inherits `#31`'s cell-granularity amplitude bridge. No
amplitudes, no measurement, no ECDSA resource claim here.

**Space tradeoff (honest).** The Toffoli parity (and the measurement-level advantage over Cuccaro) is
bought with `O(n)` extra space: a separate sum register `S` (`n` wires) and an `(n+1)`-wire fresh carry
runway `G`, against Cuccaro's single in-place ancilla. The win is on the Toffoli axis only. The count is
also Toffoli-only (the dominant fault-tolerant cost); Cliffords / measurements are not counted.
-/

namespace Reversible

variable {m n : ℕ}

/-! ### The Gidney carry cell (one Toffoli) -/

/-- **The Gidney carry cell** on `(a, b, cin, cout)` with `cout` a fresh runway ancilla:
`[CX cin a, CX cin b, CCX a b cout, CX cin cout]`. The single `CCX` folds the fresh-AND
`(a ⊕ cin) ∧ (b ⊕ cin)` into `cout`; the surrounding CNOTs shift `a`, `b` by `cin` and add the `cin`
term, giving `cout = MAJ(a, b, cin)`. Deviates from Cuccaro's 3-wire in-place `maj` by using a fresh
`cout` (the attachment point the measurement gadget needs). One Toffoli per carry. -/
def majCell (a b cin cout : Fin m) : Circuit m :=
  [.CX cin a, .CX cin b, .CCX a b cout, .CX cin cout]

/-- **Cell Toffoli cost = 1** (the single `CCX`; the other three gates are CNOTs). The key cost win
over `#30`'s 3-Toffoli `andCarryCell`. -/
theorem majCell_toffoli (a b cin cout : Fin m) :
    (circuitCost (majCell a b cin cout)).toffoli = 1 := by
  simp [circuitCost, majCell, gateCost]

set_option linter.unnecessarySeqFocus false in
/-- **Cell correctness.** For pairwise-distinct wires and a fresh `cout = false`, the cell writes
`cout = MAJ(a, b, cin)`, shifts `a ← a ⊕ cin` and `b ← b ⊕ cin`, and preserves `cin`. The fresh-AND
temporary `(a ⊕ cin) ∧ (b ⊕ cin)` is computed by the single Toffoli and completed to the majority by
the final CNOT. -/
theorem majCell_correct {a b cin cout : Fin m}
    (hab : a ≠ b) (hca : cin ≠ a) (hcb : cin ≠ b) (hcc : cin ≠ cout)
    (hoa : cout ≠ a) (hob : cout ≠ b) {s : State m} (h0 : s cout = false) :
    denote (majCell a b cin cout) s cout = majority (s a) (s b) (s cin)
      ∧ denote (majCell a b cin cout) s a = (s a ^^ s cin)
      ∧ denote (majCell a b cin cout) s b = (s b ^^ s cin)
      ∧ denote (majCell a b cin cout) s cin = s cin := by
  have hba : b ≠ a := hab.symm
  have hac : a ≠ cin := hca.symm
  have hbc : b ≠ cin := hcb.symm
  have hac' : cout ≠ cin := hcc.symm
  have hao : a ≠ cout := hoa.symm
  have hbo : b ≠ cout := hob.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [majCell, denote_cons, denote_nil, denoteGate] <;>
    simp_all <;>
    cases s a <;> cases s b <;> cases s cin <;> simp_all [majority]

/-! ### The Gidney adder layout (addend registers injective; `A`, `B` are modified and restored) -/

/-- The Gidney-adder wire geometry on `m` wires for `n`-bit registers: addends `A`, `B` (XOR-shifted
during the forward pass, restored by the reverse pass), a separate sum register `S`, and a fresh
per-carry ancilla chain `G` (`G 0` the input carry, `G (i+1)` the carry out of bit `i`, all init
`false`). Unlike `AndAddLayout`, `A` and `B` carry their own injectivity (`hAinj` / `hBinj`) because
the forward pass *writes* them. The four images are pairwise disjoint. -/
structure GidneyLayout (m n : ℕ) where
  /-- First addend (shifted then restored). -/
  A : ℕ → Fin m
  /-- Second addend (shifted then restored). -/
  B : ℕ → Fin m
  /-- Sum output register (`(A + B) mod 2 ^ n`). -/
  S : ℕ → Fin m
  /-- Fresh per-carry ancilla chain (`G i` = carry into bit `i`; init/returned `false`). -/
  G : ℕ → Fin m
  hAB : ∀ i j, A i ≠ B j
  hAS : ∀ i j, A i ≠ S j
  hAG : ∀ i j, A i ≠ G j
  hBS : ∀ i j, B i ≠ S j
  hBG : ∀ i j, B i ≠ G j
  hSG : ∀ i j, S i ≠ G j
  hAinj : ∀ i j, i < n → j < n → A i = A j → i = j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hSinj : ∀ i j, i < n → j < n → S i = S j → i = j
  hGinj : ∀ i j, i < n + 1 → j < n + 1 → G i = G j → i = j

/-- The `#30` `AndAddLayout` underlying a `GidneyLayout` (drops the addend injectivity). Lets the
Gidney adder reuse `#30`'s sum-pass machinery and carry arithmetic verbatim. -/
def GidneyLayout.toAnd (L : GidneyLayout m n) : AndAddLayout m n where
  A := L.A
  B := L.B
  S := L.S
  G := L.G
  hAB := L.hAB
  hAS := L.hAS
  hAG := L.hAG
  hBS := L.hBS
  hBG := L.hBG
  hSG := L.hSG
  hSinj := L.hSinj
  hGinj := L.hGinj

/-! ### Forward carry pass -/

/-- The carry compute for bit `i`: the Gidney cell on `(A i, B i, G i, G (i+1))`. -/
def gidneyForwardSlice (L : GidneyLayout m n) (i : ℕ) : Circuit m :=
  majCell (L.A i) (L.B i) (L.G i) (L.G (i + 1))

/-- The forward carry pass over the first `k` bits. -/
def gidneyForwardPrefix (L : GidneyLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).flatMap (gidneyForwardSlice L)

/-- The full forward carry pass (all `n` bits). -/
def gidneyForward (L : GidneyLayout m n) : Circuit m := gidneyForwardPrefix L n

/-- **The Gidney adder.** Compute all carries into `G` (`gidneyForward`, `n` Toffoli, XOR-shifting
`A`, `B`), write the sums into `S` (`andSumPass`, CNOT-only, reused from `#30`), then **uncompute**
every carry and restore `A`, `B`, `G` via the reverse pass `inverse (gidneyForward L)`. The reverse
pass's per-carry Toffoli is an `andUncompute`-shaped block — the measurement-gadget attachment point. -/
def gidneyAdd (L : GidneyLayout m n) : Circuit m :=
  gidneyForward L ++ andSumPass L.toAnd ++ inverse (gidneyForward L)

/-! ### Membership / wire / target characterisation -/

theorem mem_gidneyForwardPrefix {L : GidneyLayout m n} {k : ℕ} {g : Gate m}
    (hg : g ∈ gidneyForwardPrefix L k) : ∃ j, j < k ∧ g ∈ gidneyForwardSlice L j := by
  simp only [gidneyForwardPrefix, List.mem_flatMap, List.mem_range] at hg
  exact hg

theorem gidneyForwardSlice_wires {L : GidneyLayout m n} {j : ℕ} {g : Gate m}
    (hg : g ∈ gidneyForwardSlice L j) {w : Fin m} (hw : w ∈ gateWires g) :
    w = L.A j ∨ w = L.B j ∨ w = L.G j ∨ w = L.G (j + 1) := by
  simp only [gidneyForwardSlice, majCell, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp only [gateWires, Finset.mem_insert, Finset.mem_singleton] at hw <;> tauto

theorem gidneyForwardSlice_target {L : GidneyLayout m n} {j : ℕ} {g : Gate m}
    (hg : g ∈ gidneyForwardSlice L j) {w : Fin m} (hw : w ∈ gateTarget g) :
    w = L.A j ∨ w = L.B j ∨ w = L.G (j + 1) := by
  simp only [gidneyForwardSlice, majCell, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp only [gateTarget, Finset.mem_singleton] at hw <;> tauto

/-! ### Preservation lemmas (target-frame) -/

/-- The forward prefix preserves the sum register (`S` is never a target). -/
theorem gidneyForwardPrefix_preserves_S (L : GidneyLayout m n) (s : State m) (k i : ℕ) :
    denote (gidneyForwardPrefix L k) s (L.S i) = s (L.S i) := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  obtain ⟨j, _, hgj⟩ := mem_gidneyForwardPrefix hg
  rcases gidneyForwardSlice_target hgj hmem with h | h | h
  · exact L.hAS j i h.symm
  · exact L.hBS j i h.symm
  · exact L.hSG i (j + 1) h

/-- The forward slice for bit `k` preserves any wire outside `{A k, B k, G (k+1)}`. -/
theorem gidneyForwardSlice_preserves (L : GidneyLayout m n) (s : State m) (k : ℕ) {w : Fin m}
    (hA : w ≠ L.A k) (hB : w ≠ L.B k) (hG : w ≠ L.G (k + 1)) :
    denote (gidneyForwardSlice L k) s w = s w := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  rcases gidneyForwardSlice_target hg hmem with h | h | h
  · exact hA h
  · exact hB h
  · exact hG h

/-! ### The forward carry invariant -/

/-- **The forward carry invariant.** After the first `k` forward slices: every computed carry `G i`
(`i ≤ k`) holds the true carry `carryOf i`; the not-yet-computed ancillas (`k < i ≤ n`) are still
`false`; the processed addend bits (`i < k`) are XOR-shifted `A i = a_i ⊕ carryOf i`,
`B i = b_i ⊕ carryOf i`; and the unprocessed addend bits (`k ≤ i < n`) are still their inputs. By
induction on `k`, each step one Gidney cell on the fresh `G (k+1)`. -/
theorem gidneyForward_invariant (L : GidneyLayout m n) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) :
    ∀ k, k ≤ n →
      (∀ i, i ≤ k → denote (gidneyForwardPrefix L k) s (L.G i)
          = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) i)
      ∧ (∀ i, k < i → i ≤ n → denote (gidneyForwardPrefix L k) s (L.G i) = false)
      ∧ (∀ i, i < k → denote (gidneyForwardPrefix L k) s (L.A i)
          = (s (L.A i) ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) i))
      ∧ (∀ i, i < k → denote (gidneyForwardPrefix L k) s (L.B i)
          = (s (L.B i) ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) i))
      ∧ (∀ i, k ≤ i → i < n → denote (gidneyForwardPrefix L k) s (L.A i) = s (L.A i))
      ∧ (∀ i, k ≤ i → i < n → denote (gidneyForwardPrefix L k) s (L.B i) = s (L.B i)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have : i = 0 := Nat.le_zero.mp hi
      subst this; simp [gidneyForwardPrefix, carryOf, hG0]
    · intro i _ _; simp [gidneyForwardPrefix, hG0]
    · intro i hi; omega
    · intro i hi; omega
    · intro i _ _; simp [gidneyForwardPrefix]
    · intro i _ _; simp [gidneyForwardPrefix]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hG, hU, hA, hB, hAo, hBo⟩ := ih hkn
    have hsplit : gidneyForwardPrefix L (k + 1)
        = gidneyForwardPrefix L k ++ gidneyForwardSlice L k := by
      simp [gidneyForwardPrefix, List.range_succ, List.flatMap_append]
    set sk := denote (gidneyForwardPrefix L k) s with hskdef
    -- cell-wire distinctness
    have hab : L.A k ≠ L.B k := L.hAB k k
    have hca : L.G k ≠ L.A k := (L.hAG k k).symm
    have hcb : L.G k ≠ L.B k := (L.hBG k k).symm
    have hcc : L.G k ≠ L.G (k + 1) := fun h =>
      Nat.succ_ne_self k (L.hGinj (k + 1) k (by omega) (by omega) h.symm)
    have hoa : L.G (k + 1) ≠ L.A k := (L.hAG k (k + 1)).symm
    have hob : L.G (k + 1) ≠ L.B k := (L.hBG k (k + 1)).symm
    -- the slice's fresh target G (k+1) is still false
    have hfresh : sk (L.G (k + 1)) = false := hU (k + 1) (by omega) (by omega)
    -- input bits to the cell, in terms of original s
    have hskG : sk (L.G k) = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k := hG k (le_refl k)
    have hskA : sk (L.A k) = s (L.A k) := hAo k (le_refl k) hkltn
    have hskB : sk (L.B k) = s (L.B k) := hBo k (le_refl k) hkltn
    obtain ⟨hcMaj, hcA, hcB, hcG⟩ := majCell_correct hab hca hcb hcc hoa hob hfresh
    -- value of G (k+1) after the cell
    have hGkp1 : denote (gidneyForwardSlice L k) sk (L.G (k + 1))
        = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) (k + 1) := by
      simp only [gidneyForwardSlice] at hcMaj ⊢
      rw [hcMaj, hskA, hskB, hskG]; rfl
    have hAk : denote (gidneyForwardSlice L k) sk (L.A k)
        = (s (L.A k) ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k) := by
      simp only [gidneyForwardSlice] at hcA ⊢
      rw [hcA, hskA, hskG]
    have hBk : denote (gidneyForwardSlice L k) sk (L.B k)
        = (s (L.B k) ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k) := by
      simp only [gidneyForwardSlice] at hcB ⊢
      rw [hcB, hskB, hskG]
    have hGk : denote (gidneyForwardSlice L k) sk (L.G k)
        = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k := by
      simp only [gidneyForwardSlice] at hcG ⊢
      rw [hcG, hskG]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- G i = carryOf i, i ≤ k+1
      intro i hi
      rw [hsplit, denote_append, ← hskdef]
      by_cases hik : i = k + 1
      · subst hik; exact hGkp1
      · have hiAk : L.G i ≠ L.A k := L.hAG k i |>.symm
        have hiBk : L.G i ≠ L.B k := L.hBG k i |>.symm
        have hiGk : L.G i ≠ L.G (k + 1) := fun h =>
          hik (L.hGinj i (k + 1) (by omega) (by omega) h)
        rw [gidneyForwardSlice_preserves L sk k hiAk hiBk hiGk, hG i (by omega)]
    · -- G i = false, k+1 < i ≤ n
      intro i hik hin
      rw [hsplit, denote_append, ← hskdef]
      have hiAk : L.G i ≠ L.A k := L.hAG k i |>.symm
      have hiBk : L.G i ≠ L.B k := L.hBG k i |>.symm
      have hiGk : L.G i ≠ L.G (k + 1) := fun h =>
        (by omega : i ≠ k + 1) (L.hGinj i (k + 1) (by omega) (by omega) h)
      rw [gidneyForwardSlice_preserves L sk k hiAk hiBk hiGk, hU i (by omega) hin]
    · -- A i shifted, i < k+1
      intro i hi
      rw [hsplit, denote_append, ← hskdef]
      by_cases hik : i = k
      · subst hik; exact hAk
      · have hiAk : L.A i ≠ L.A k := fun h => hik (L.hAinj i k (by omega) hkltn h)
        have hiBk : L.A i ≠ L.B k := L.hAB i k
        have hiGk : L.A i ≠ L.G (k + 1) := L.hAG i (k + 1)
        rw [gidneyForwardSlice_preserves L sk k hiAk hiBk hiGk, hA i (by omega)]
    · -- B i shifted, i < k+1
      intro i hi
      rw [hsplit, denote_append, ← hskdef]
      by_cases hik : i = k
      · subst hik; exact hBk
      · have hiAk : L.B i ≠ L.A k := (L.hAB k i).symm
        have hiBk : L.B i ≠ L.B k := fun h => hik (L.hBinj i k (by omega) hkltn h)
        have hiGk : L.B i ≠ L.G (k + 1) := L.hBG i (k + 1)
        rw [gidneyForwardSlice_preserves L sk k hiAk hiBk hiGk, hB i (by omega)]
    · -- A i original, k+1 ≤ i < n
      intro i hik hin
      rw [hsplit, denote_append, ← hskdef]
      have hiAk : L.A i ≠ L.A k := fun h => (by omega : i ≠ k) (L.hAinj i k hin hkltn h)
      have hiBk : L.A i ≠ L.B k := L.hAB i k
      have hiGk : L.A i ≠ L.G (k + 1) := L.hAG i (k + 1)
      rw [gidneyForwardSlice_preserves L sk k hiAk hiBk hiGk, hAo i (by omega) hin]
    · -- B i original, k+1 ≤ i < n
      intro i hik hin
      rw [hsplit, denote_append, ← hskdef]
      have hiAk : L.B i ≠ L.A k := (L.hAB k i).symm
      have hiBk : L.B i ≠ L.B k := fun h => (by omega : i ≠ k) (L.hBinj i k hin hkltn h)
      have hiGk : L.B i ≠ L.G (k + 1) := L.hBG i (k + 1)
      rw [gidneyForwardSlice_preserves L sk k hiAk hiBk hiGk, hBo i (by omega) hin]

/-! ### Per-bit value of the full adder -/

/-- **Per-bit sum value.** Bit `k` of the sum register holds `A k ⊕ B k ⊕ carry k`. The forward pass
XOR-shifts the addends (`A k ⊕ c`, `B k ⊕ c`), the sum pass XORs them with `G k = c` (the two `c`
shifts cancel one), and the reverse pass only touches `A`, `B`, `G`, so `S k` survives. -/
theorem gidneyAdd_sum_bit (L : GidneyLayout m n) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (hS0 : ∀ i, s (L.S i) = false) (k : ℕ) (hk : k < n) :
    denote (gidneyAdd L) s (L.S k)
      = (s (L.A k) ^^ s (L.B k)
          ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k) := by
  rw [gidneyAdd, denote_append, denote_append]
  set t := denote (gidneyForward L) s with htdef
  -- the reverse pass preserves S k (it only writes A, B, G wires)
  have hinvS : denote (inverse (gidneyForward L)) (denote (andSumPass L.toAnd) t) (L.S k)
      = denote (andSumPass L.toAnd) t (L.S k) := by
    apply denote_apply_of_forall_not_mem_target
    intro g hg hmem
    rw [inverse, List.mem_reverse] at hg
    obtain ⟨j, _, hgj⟩ := mem_gidneyForwardPrefix hg
    rcases gidneyForwardSlice_target hgj hmem with h | h | h
    · exact L.hAS j k h.symm
    · exact L.hBS j k h.symm
    · exact L.hSG k (j + 1) h
  rw [hinvS]
  -- value of the sum pass at S k (reused from #30)
  obtain ⟨hSC, _⟩ := andSum_value L.toAnd t n (le_refl n)
  have hval : denote (andSumPass L.toAnd) t (L.S k)
      = (t (L.toAnd.S k) ^^ t (L.toAnd.A k) ^^ t (L.toAnd.B k) ^^ t (L.toAnd.G k)) := by
    rw [andSumPass]; exact hSC k hk
  rw [hval]
  -- t = forward of s: S preserved; A, B shifted; G k = carry k
  have htS : t (L.toAnd.S k) = false := by
    rw [htdef, gidneyForward]
    exact (gidneyForwardPrefix_preserves_S L s n k).trans (hS0 k)
  have htA : t (L.toAnd.A k)
      = (s (L.A k) ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k) := by
    rw [htdef, gidneyForward]; exact (gidneyForward_invariant L s hG0 n (le_refl n)).2.2.1 k hk
  have htB : t (L.toAnd.B k)
      = (s (L.B k) ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k) := by
    rw [htdef, gidneyForward]; exact (gidneyForward_invariant L s hG0 n (le_refl n)).2.2.2.1 k hk
  have htG : t (L.toAnd.G k) = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k := by
    rw [htdef, gidneyForward]; exact (gidneyForward_invariant L s hG0 n (le_refl n)).1 k (by omega)
  rw [htS, htA, htB, htG]
  cases s (L.A k) <;> cases s (L.B k) <;>
    cases carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k <;> decide

/-! ### Headline theorems -/

/-- **Gidney adder correctness.** For a disjoint-wire layout with the carry chain and the sum register
initialised `false`, the sum register ends holding `(A + B) mod 2 ^ n`. **General `n`.** The proof is
the `#30` arithmetic (`adder_sum_identity`) over the Gidney per-bit value `gidneyAdd_sum_bit`. -/
theorem gidneyAdd_correct (L : GidneyLayout m n) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (hS0 : ∀ i, s (L.S i) = false) :
    regValRange L.S (denote (gidneyAdd L) s) n
      = (regValRange L.A s n + regValRange L.B s n) % 2 ^ n := by
  have hbit : regValRange L.S (denote (gidneyAdd L) s) n
      = ∑ i ∈ Finset.range n,
          (s (L.A i) ^^ s (L.B i)
            ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) i).toNat * 2 ^ i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [gidneyAdd_sum_bit L s hG0 hS0 i hi]
  have hid := adder_sum_identity (fun i => s (L.A i)) (fun i => s (L.B i)) n
  have hcombine : regValRange L.S (denote (gidneyAdd L) s) n
      + (carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) n).toNat * 2 ^ n
      = regValRange L.A s n + regValRange L.B s n := by
    rw [hbit]; exact hid
  have hlt : regValRange L.S (denote (gidneyAdd L) s) n < 2 ^ n := regValRange_lt _ _ _
  set vS := regValRange L.S (denote (gidneyAdd L) s) n
  set vA := regValRange L.A s n
  set vB := regValRange L.B s n
  cases hc : carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) n
  · simp only [hc, Bool.toNat_false, zero_mul, add_zero] at hcombine
    rw [← hcombine, Nat.mod_eq_of_lt hlt]
  · simp only [hc, Bool.toNat_true, one_mul] at hcombine
    rw [← hcombine, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- **Non-`S` wires are restored.** Any wire that is not a (used) sum-register wire is returned to its
input: the sum pass leaves it untouched (`andSumPrefix_preserves_of_ne_S`), so the reverse pass
`inverse (gidneyForward L)` undoes the forward pass on it (`reversible_inverse_correct`). The frame
behind addend / carry restoration. -/
theorem gidneyAdd_preserves_nonS (L : GidneyLayout m n) (s : State m) (w : Fin m)
    (hw : ∀ i, i < n → w ≠ L.S i) : denote (gidneyAdd L) s w = s w := by
  rw [gidneyAdd, denote_append, denote_append]
  set t := denote (gidneyForward L) s with htdef
  have hagree : denote (inverse (gidneyForward L)) (denote (andSumPass L.toAnd) t) w
      = denote (inverse (gidneyForward L)) t w := by
    refine denote_agree_on (P := fun w => ∀ i, i < n → w ≠ L.S i) (inverse (gidneyForward L))
      ?_ ?_ w hw
    · intro g hg w' hw'
      rw [inverse, List.mem_reverse] at hg
      obtain ⟨jj, _, hgj⟩ := mem_gidneyForwardPrefix hg
      intro i _ heq
      rcases gidneyForwardSlice_wires hgj hw' with h | h | h | h
      · exact L.hAS jj i (h.symm.trans heq)
      · exact L.hBS jj i (h.symm.trans heq)
      · exact L.hSG i jj (heq.symm.trans h)
      · exact L.hSG i (jj + 1) (heq.symm.trans h)
    · intro w' hwP
      exact andSumPrefix_preserves_of_ne_S L.toAnd t n (fun i hi => hwP i hi)
  rw [hagree, htdef, reversible_inverse_correct]

/-- **Ancilla-clean: every carry ancilla returns to `false`.** -/
theorem gidneyAdd_ancilla_clean (L : GidneyLayout m n) (s : State m) (hG0 : ∀ j, s (L.G j) = false)
    (j : ℕ) : denote (gidneyAdd L) s (L.G j) = false := by
  rw [gidneyAdd_preserves_nonS L s (L.G j) (fun i _ => (L.hSG i j).symm)]; exact hG0 j

/-- **Addend `A` is restored.** The forward XOR-shift `A i ← A i ⊕ carry i` is undone by the reverse
pass. -/
theorem gidneyAdd_preserves_A (L : GidneyLayout m n) (s : State m) (k : ℕ) :
    denote (gidneyAdd L) s (L.A k) = s (L.A k) :=
  gidneyAdd_preserves_nonS L s (L.A k) (fun i _ => L.hAS k i)

/-- **Addend `B` is restored.** -/
theorem gidneyAdd_preserves_B (L : GidneyLayout m n) (s : State m) (k : ℕ) :
    denote (gidneyAdd L) s (L.B k) = s (L.B k) :=
  gidneyAdd_preserves_nonS L s (L.B k) (fun i _ => L.hBS k i)

/-! ### Derived cost: 2n Toffolis (n forward + n reverse) -/

theorem gidneyForwardPrefix_toffoli (L : GidneyLayout m n) (k : ℕ) :
    (circuitCost (gidneyForwardPrefix L k)).toffoli = k := by
  induction k with
  | zero => simp [gidneyForwardPrefix, circuitCost]
  | succ k ih =>
    have hsplit : gidneyForwardPrefix L (k + 1)
        = gidneyForwardPrefix L k ++ gidneyForwardSlice L k := by
      simp [gidneyForwardPrefix, List.range_succ, List.flatMap_append]
    rw [hsplit, cost_comp_toffoli_count, ih, gidneyForwardSlice, majCell_toffoli]

theorem gidneyForward_toffoli (L : GidneyLayout m n) :
    (circuitCost (gidneyForward L)).toffoli = n := by
  rw [gidneyForward, gidneyForwardPrefix_toffoli]

/-- **The reverse pass is `n` Toffolis** — the `andUncompute`-shaped blocks a measurement-based gadget
eliminates (the win over Cuccaro). It equals the forward pass (`gidneyForward`, `n`) by
`cost_inverse_toffoli`. -/
theorem gidneyAdd_uncompute_toffoli (L : GidneyLayout m n) :
    (circuitCost (inverse (gidneyForward L))).toffoli = n := by
  rw [cost_inverse_toffoli, gidneyForward_toffoli]

/-- **Derived Toffoli cost: `2 * n`.** `n` forward Gidney cells (one Toffoli each) `+` `n` reverse
uncompute Toffolis; the sum pass is CNOT-only. One third of `#30`'s `6n`; equal to Cuccaro's `2n` at
the unitary level (the win over Cuccaro is the measurement re-cost of the reverse `n`). -/
theorem gidneyAdd_toffoli (L : GidneyLayout m n) :
    (circuitCost (gidneyAdd L)).toffoli = 2 * n := by
  rw [gidneyAdd, cost_comp_toffoli_count, cost_comp_toffoli_count, gidneyForward_toffoli,
    andSumPass, andSumPrefix_toffoli, cost_inverse_toffoli, gidneyForward_toffoli]
  omega

/-! ### Non-vacuity witness + `#eval` cross-check

A concrete 2-bit Gidney layout on `Fin 9`: `A → {0,1}`, `B → {2,3}`, `S → {4,5}`, carry chain
`G → {6,7,8}`. The headline applies, and the strict `Array` evaluator `runArr` (bridge
`regValRangeArr_eq`) witnesses `2 + 3 = 5` (`= 1 mod 4`), every carry ancilla / addend restored. -/

/-- A concrete 2-bit Gidney layout on `Fin 9`. -/
def gidneyLayout2 : GidneyLayout 9 2 where
  A i := if i = 0 then 0 else 1
  B i := if i = 0 then 2 else 3
  S i := if i = 0 then 4 else 5
  G i := if i = 0 then 6 else if i = 1 then 7 else 8
  hAB i j := by split_ifs <;> decide
  hAS i j := by split_ifs <;> decide
  hAG i j := by split_ifs <;> decide
  hBS i j := by split_ifs <;> decide
  hBG i j := by split_ifs <;> decide
  hSG i j := by split_ifs <;> decide
  hAinj i j hi hj h := by split_ifs at h <;> omega
  hBinj i j hi hj h := by split_ifs at h <;> omega
  hSinj i j hi hj h := by split_ifs at h <;> omega
  hGinj i j hi hj h := by split_ifs at h <;> omega

/-- The headline is non-vacuous: it applies to `gidneyLayout2`. -/
example (s : State 9) (hG0 : ∀ j, s (gidneyLayout2.G j) = false)
    (hS0 : ∀ i, s (gidneyLayout2.S i) = false) :
    regValRange gidneyLayout2.S (denote (gidneyAdd gidneyLayout2) s) 2
      = (regValRange gidneyLayout2.A s 2 + regValRange gidneyLayout2.B s 2) % 2 ^ 2 :=
  gidneyAdd_correct gidneyLayout2 s hG0 hS0

/-- Witness: `A = 2` (wires `0,1 = 0,1`), `B = 3` (wires `2,3 = 1,1`), `S`/`G` init `false`. -/
def gidneyWitness2 : State 9 := ![false, true, true, true, false, false, false, false, false]

-- `S ← 2 + 3 = 5`; reads `1 = 5 mod 4` off register `S` (low 2 bits).
#eval regValRangeArr gidneyLayout2.S
  (runArr (gidneyAdd gidneyLayout2) (ofState gidneyWitness2)) 2
-- 1

-- Carry ancillas clean.
#eval (runArr (gidneyAdd gidneyLayout2) (ofState gidneyWitness2))[gidneyLayout2.G 1 |>.val]!
-- false

-- Addends restored: `A` reads `2`, `B` reads `3`.
#eval regValRangeArr gidneyLayout2.A
  (runArr (gidneyAdd gidneyLayout2) (ofState gidneyWitness2)) 2
-- 2
#eval regValRangeArr gidneyLayout2.B
  (runArr (gidneyAdd gidneyLayout2) (ofState gidneyWitness2)) 2
-- 3

-- Theorem-independent value check via the proven `runArr` bridge: `S` reads `1 = 5 mod 4`.
set_option maxRecDepth 4000 in
example : regValRangeArr gidneyLayout2.S
    (runArr (gidneyAdd gidneyLayout2) (ofState gidneyWitness2)) 2 = 1 := by
  decide

end Reversible
