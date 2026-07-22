/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval

/-!
# Reversible modular doubling — the verified value primitive `a ↦ 2a mod N`  (ECDLP Phase 2, Stage S6.3d-1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module **verifies the modular-doubling VALUE primitive** `a ↦ 2a mod N` over bit registers, the
`acc ← 2·acc mod N` step of the interleaved MSB-first modular multiply. It is realised as a copy
followed by the already-verified S6.3b modular adder:

```
modDouble L = copyReg L ++ modAdd L.addLayout
```

* **Copy step** `copyReg L` (the only genuinely new gadget): with `B` holding `a` and the operand
  register `Aop` initially `0` on `[0, n)`, `n` CNOTs `CX (B i) (Aop i)` copy `B` into `Aop`. Each
  `Aop i ← Aop i ⊕ B i = 0 ⊕ B i = B i`; `B` is the control, so it is preserved. After the copy:
  `Aop = a`, `B = a`.
* **Add step** `modAdd L.addLayout` (S6.3b, `modAdd_correct`): with `Aop = a`, `B = a` (both `< N`),
  presets `A1 = 2ⁿ − N`, `A2 = N`, carries / ancilla clean, `2N ≤ 2ⁿ`, leaves `B ← (a + a) mod N`,
  and `a + a = 2 * a` gives `2a mod N`.

The copy step touches only the wires `{B i, Aop i}`. So it WRITES `Aop` (from `0` to `a`, exactly the
operand the add step wants), PRESERVES `B` (control), and leaves the add step's presets / carries
(`A1, A2, Cadd, C1, C2, anc`) untouched — re-establishing `modAdd_correct`'s hypotheses with
`a := a`, `b := a`.

## Carve line (what this is, and is NOT)

This is `2a mod N` realised as `copy ++ modAdd`, **reusing wholesale the verified S6.3b `modAdd`**.
The only new verified content is the `copyReg` CNOT-copy gadget (`copyReg_correct`). This is `ℕ` /
`mod N` bit arithmetic; no group-law / field semantics are in play.

**Named residue (same fresh-ancilla model as S6.3b; do NOT read as a clean in-place primitive):**

1. **Operand copy left dirty.** After `modDouble`, the operand register `Aop` is left holding `a`
   (not restored to `0`), and — inherited from `modAdd` — the carry chains `Cadd`, `C1`, `C2` and the
   comparison flag are dirty. Correctness holds *because the layout supplies fresh wires per use*. In-
   place reuse across many doublings needs the carry-clean / ancilla-restoring adders the corpus does
   NOT yet provide (Cuccaro-style inline uncompute, or the self-cleaning high-bit modular adder).
2. **This is the doubling PRIMITIVE, not the multiply.** The full interleaved MSB-first modular
   MULTIPLY over `𝔽_p` (the Horner loop of `modDouble` + `cModAdd` with the running `acc < N`
   invariant) is the subsequent tranche (S6.3d-2). This module is the `acc ← 2·acc mod N` atom that
   loop iterates.

## Honest cost

`modDouble_toffoli` derives `12n` Toffolis: copy step `0` (`n` CNOTs, no Toffoli) + add step `12n`
(`modularAdd_toffoli`), composed through `cost_comp_toffoli_count`. The copy contributes `n` CNOTs
(`modDouble_cnot_copy`), which do not add Toffolis.
-/

namespace Reversible

variable {m n : ℕ}

/-- A modular-doubling layout on `Fin m` for `n`-bit registers. It is exactly a `ModAddLayout`: the
copy step reuses the same two registers the add step uses — `B` (holds `a`, the doubled accumulator)
and `Aop` (the operand, initially `0`, copied to `a`). No new wire families are needed. All
disjointness / bounded-injectivity facts come for free from the bundled `ModAddLayout`. -/
structure ModDoubleLayout (m n : ℕ) where
  /-- The bundled S6.3b modular-addition layout (supplies every register + geometry fact). -/
  addLayout : ModAddLayout m n

/-- The doubled accumulator register (`B` of the bundled add layout); holds `a`, overwritten with
`2a mod N`. -/
def ModDoubleLayout.B (L : ModDoubleLayout m n) : ℕ → Fin m := L.addLayout.B

/-- The operand register (`Aop` of the bundled add layout); initially `0`, copied to `a`. -/
def ModDoubleLayout.Aop (L : ModDoubleLayout m n) : ℕ → Fin m := L.addLayout.Aop

variable {L : ModDoubleLayout m n}

/-! ### The copy gadget -/

/-- **The copy circuit:** `n` CNOTs `CX (B i) (Aop i)`, copying register `B` into register `Aop`. -/
def copyReg (L : ModDoubleLayout m n) : Circuit m :=
  (List.range n).map (fun i => Gate.CX (L.B i) (L.Aop i))

/-- **The modular-doubling circuit.** Copy `B` into `Aop`, then add (`modAdd`): `2a = a + a`. -/
def modDouble (L : ModDoubleLayout m n) : Circuit m :=
  copyReg L ++ modAdd L.addLayout

/-! ### Copy-step frame: a wire disjoint from `{B i, Aop i}` survives

`copyReg L` touches only the wires `{B k, Aop k}` (the `k`-th gate is `CX (B k) (Aop k)`, whose
`gateWires` is `{B k, Aop k}`). Any wire distinct from all of those passes through unchanged. -/

/-- **Generic copy-step frame.** A wire `w` with `w ≠ B k`, `w ≠ Aop k` for all `k` is left unchanged
by `copyReg L`. -/
theorem copyReg_preserves (s : State m) (w : Fin m)
    (hB : ∀ k, w ≠ L.B k) (hA : ∀ k, w ≠ L.Aop k) :
    denote (copyReg L) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [copyReg, List.mem_map] at hg
  obtain ⟨k, _hk, rfl⟩ := hg
  simp [gateWires, hB k, hA k]

/-! ### Copy-step value correctness

The CNOTs have pairwise-disjoint targets (`Aop` injective on `[0, n)`) and never target a control
(`hAopB`), so each `Aop i` is touched by exactly its own CNOT, and `B` is never a target. We prove
the prefix invariant by induction: after the first `k` copies, `Aop i = B i` for `i < k`, `Aop i`
unchanged for `k ≤ i`, and `B` everywhere preserved. -/

/-- The circuit of the first `k` copies. -/
def copyPrefix (L : ModDoubleLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).map (fun i => Gate.CX (L.B i) (L.Aop i))

theorem copyReg_eq_prefix (L : ModDoubleLayout m n) : copyReg L = copyPrefix L n := rfl

theorem denote_copyPrefix_succ (L : ModDoubleLayout m n) (k : ℕ) (s : State m) :
    denote (copyPrefix L (k + 1)) s
      = denoteGate (Gate.CX (L.B k) (L.Aop k)) (denote (copyPrefix L k) s) := by
  simp only [copyPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    denote_append, denote_cons, denote_nil]

/-- A wire disjoint from `{B i, Aop i}` survives the first `k` copies (the prefix frame). -/
theorem copyPrefix_preserves (s : State m) (w : Fin m) (k : ℕ)
    (hB : ∀ j, w ≠ L.B j) (hA : ∀ j, w ≠ L.Aop j) :
    denote (copyPrefix L k) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [copyPrefix, List.mem_map] at hg
  obtain ⟨j, _hj, rfl⟩ := hg
  simp [gateWires, hB j, hA j]

/-- **The copy invariant.** Assuming `Aop` is initially `0` on `[0, n)`, after the first `k` copies:
`Aop i = B i` for `i < k`, `Aop i` is unchanged for `k ≤ i < n`, and `B j` is preserved for all `j`.
The `B` preservation holds because `B` is never a CNOT target (`hAopB`); the `Aop` clauses hold
because the targets are pairwise disjoint (`Aop` injective). -/
theorem copyReg_invariant (L : ModDoubleLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.Aop i) = false) :
    ∀ k, k ≤ n →
      (∀ i, i < k → denote (copyPrefix L k) s (L.Aop i) = s (L.B i))
      ∧ (∀ i, k ≤ i → i < n → denote (copyPrefix L k) s (L.Aop i) = s (L.Aop i))
      ∧ (∀ j, denote (copyPrefix L k) s (L.B j) = s (L.B j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; omega
    · intro i _ _; simp [copyPrefix]
    · intro j; simp [copyPrefix]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hLow, hHigh, hBpres⟩ := ih hkn
    set sk := denote (copyPrefix L k) s with hskdef
    -- the (k+1)-th gate is CX (B k) (Aop k); B k ≠ Aop k, so it updates Aop k
    have hBkAk : L.B k ≠ L.Aop k := (L.addLayout.hAopB k k).symm
    have hstep : denote (copyPrefix L (k + 1)) s
        = Function.update sk (L.Aop k) (sk (L.B k) ^^ sk (L.Aop k)) := by
      rw [denote_copyPrefix_succ, denoteGate, if_neg hBkAk]
    refine ⟨?_, ?_, ?_⟩
    · -- Aop i = B i for i < k+1
      intro i hi
      rw [hstep]
      by_cases hik : i = k
      · subst i
        rw [Function.update_self]
        -- sk (Aop k) = s (Aop k) = false  (k not yet copied)
        have hAk : sk (L.Aop k) = s (L.Aop k) := hHigh k (Nat.le_refl k) hkltn
        have hAk0 : sk (L.Aop k) = false := by rw [hAk]; exact hAop0 k hkltn
        rw [hAk0, Bool.xor_false]
        -- sk (B k) = s (B k)
        exact hBpres k
      · -- i < k: Aop i unchanged by this gate, value already B i
        have hineq : (L.Aop i) ≠ (L.Aop k) := by
          intro h
          exact hik (L.addLayout.hAopinj i k (by omega) hkltn h)
        rw [Function.update_of_ne hineq]
        -- value at Aop i from the prefix is B i; B i preserved at level k
        exact hLow i (by omega)
    · -- Aop i unchanged for k+1 ≤ i < n
      intro i hi hin
      rw [hstep]
      have hineq : (L.Aop i) ≠ (L.Aop k) := by
        intro h
        exact (show i ≠ k by omega) (L.addLayout.hAopinj i k hin hkltn h)
      rw [Function.update_of_ne hineq]
      exact hHigh i (by omega) hin
    · -- B j preserved
      intro j
      rw [hstep]
      have hineq : (L.B j) ≠ (L.Aop k) := L.addLayout.hAopB k j |>.symm
      rw [Function.update_of_ne hineq]
      exact hBpres j

/-- **Copy correctness — operand.** With `Aop` initially `0`, after the copy the operand register
reads the value `B` held: `regValRange Aop (denote (copyReg L) s) n = regValRange B s n`. -/
theorem copyReg_correct_operand (L : ModDoubleLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.Aop i) = false) :
    regValRange L.Aop (denote (copyReg L) s) n = regValRange L.B s n := by
  obtain ⟨hLow, -, -⟩ := copyReg_invariant L s hAop0 n (Nat.le_refl n)
  rw [copyReg_eq_prefix]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  show (denote (copyPrefix L n) s (L.Aop i)).toNat * 2 ^ i = (s (L.B i)).toNat * 2 ^ i
  rw [hLow i hi]

/-- **Copy correctness — accumulator preserved.** The copy leaves register `B` unchanged
(it is the control, never a CNOT target). Note `B` is NOT disjoint from the gate wires (each `B k`
is a control wire), so this is read off the invariant's `B`-preservation clause, not the generic
frame lemma. -/
theorem copyReg_correct_B (L : ModDoubleLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.Aop i) = false) :
    regValRange L.B (denote (copyReg L) s) n = regValRange L.B s n := by
  obtain ⟨-, -, hBpres⟩ := copyReg_invariant L s hAop0 n (Nat.le_refl n)
  apply Finset.sum_congr rfl
  intro j _
  show (denote (copyPrefix L n) s (L.B j)).toNat * 2 ^ j = (s (L.B j)).toNat * 2 ^ j
  rw [hBpres j]

/-! ### Copy-step frame for the add-step presets / carries

The add step (`modAdd L.addLayout`) reads `A1, A2, Cadd, C1, C2, anc`. Each is disjoint from both
`B` and `Aop` (the only wires `copyReg` touches), so all survive the copy and `modAdd`'s preset /
clean-carry hypotheses re-establish. The `hAop*` / `hB*` fields of `ModAddLayout` supply the
disjointness; the helper below packages the per-wire frame for each. -/

/-- After the copy, `A1` is unchanged on every wire. -/
theorem copyReg_preserves_A1 (s : State m) (j : ℕ) :
    denote (copyReg L) s (L.addLayout.A1 j) = s (L.addLayout.A1 j) :=
  copyReg_preserves s (L.addLayout.A1 j)
    (fun k => (L.addLayout.hBA1 k j).symm) (fun k => (L.addLayout.hAopA1 k j).symm)

/-- After the copy, `A2` is unchanged on every wire. -/
theorem copyReg_preserves_A2 (s : State m) (j : ℕ) :
    denote (copyReg L) s (L.addLayout.A2 j) = s (L.addLayout.A2 j) :=
  copyReg_preserves s (L.addLayout.A2 j)
    (fun k => (L.addLayout.hBA2 k j).symm) (fun k => (L.addLayout.hAopA2 k j).symm)

/-- After the copy, the add-carry chain `Cadd` is unchanged on every wire. -/
theorem copyReg_preserves_Cadd (s : State m) (j : ℕ) :
    denote (copyReg L) s (L.addLayout.Cadd j) = s (L.addLayout.Cadd j) :=
  copyReg_preserves s (L.addLayout.Cadd j)
    (fun k => (L.addLayout.hBCadd k j).symm) (fun k => (L.addLayout.hAopCadd k j).symm)

/-- After the copy, the reduce step-1 carry `C1` is unchanged on every wire. -/
theorem copyReg_preserves_C1 (s : State m) (j : ℕ) :
    denote (copyReg L) s (L.addLayout.C1 j) = s (L.addLayout.C1 j) :=
  copyReg_preserves s (L.addLayout.C1 j)
    (fun k => (L.addLayout.hBC1 k j).symm) (fun k => (L.addLayout.hAopC1 k j).symm)

/-- After the copy, the reduce step-3 carry `C2` is unchanged on every wire. -/
theorem copyReg_preserves_C2 (s : State m) (j : ℕ) :
    denote (copyReg L) s (L.addLayout.C2 j) = s (L.addLayout.C2 j) :=
  copyReg_preserves s (L.addLayout.C2 j)
    (fun k => (L.addLayout.hBC2 k j).symm) (fun k => (L.addLayout.hAopC2 k j).symm)

/-- After the copy, the shared ancilla `anc` is unchanged. -/
theorem copyReg_preserves_anc (s : State m) :
    denote (copyReg L) s L.addLayout.anc = s L.addLayout.anc :=
  copyReg_preserves s L.addLayout.anc
    (fun k => L.addLayout.hancB k) (fun k => (L.addLayout.hAopanc k).symm)

/-! ### Value correctness of the modular doubler -/

/-- **The verified modular-doubling value primitive.** For a `ModDoubleLayout` with operand register
`Aop` initially `0` on `[0, n)`, accumulator `B` holding `a < N`, with `2N ≤ 2ⁿ`, presets
`A1 = 2ⁿ − N`, `A2 = N`, and all carries (`Cadd`, `C1`, `C2`) and ancilla `anc` clean: `modDouble L`
leaves register `B` holding `(2 * a) mod N`.

Proof. The copy step (`copyReg_correct_operand` / `copyReg_correct_B`) writes `a` to `Aop` and
preserves `B = a`, and (`copyReg_preserves_*`) leaves the add step's presets `A1 = 2ⁿ − N`,
`A2 = N` and clean carries `Cadd = C1 = C2 = false`, `anc = false`. So `modAdd_correct` applies with
`a := a`, `b := a`, giving `B ← (a + a) mod N`; rewriting `a + a = 2 * a` finishes. -/
theorem modDouble_correct (L : ModDoubleLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.Aop i) = false)
    (hCadd : ∀ j, s (L.addLayout.Cadd j) = false) (hC1 : ∀ j, s (L.addLayout.C1 j) = false)
    (hC2 : ∀ j, s (L.addLayout.C2 j) = false) (hanc : s L.addLayout.anc = false)
    {N a : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1 : regValRange L.addLayout.A1 s n = 2 ^ n - N)
    (hA2 : regValRange L.addLayout.A2 s n = N)
    (hB : regValRange L.B s n = a) (haN : a < N) :
    regValRange L.B (denote (modDouble L) s) n = (2 * a) % N := by
  -- decompose at the copy step
  set scp := denote (copyReg L) s with hscpdef
  have hdenote : denote (modDouble L) s = denote (modAdd L.addLayout) scp := by
    rw [modDouble, denote_append, ← hscpdef]
  rw [hdenote]
  -- COPY STEP: Aop ← a, B preserved, presets / carries intact
  have hAopcp : regValRange L.addLayout.Aop scp n = a := by
    show regValRange L.Aop scp n = a
    rw [hscpdef, copyReg_correct_operand L s hAop0, hB]
  have hBcp : regValRange L.addLayout.B scp n = a := by
    show regValRange L.B scp n = a
    rw [hscpdef, copyReg_correct_B L s hAop0, hB]
  have hA1cp : regValRange L.addLayout.A1 scp n = 2 ^ n - N := by
    rw [← hA1]
    apply Finset.sum_congr rfl
    intro j _
    show (scp (L.addLayout.A1 j)).toNat * 2 ^ j = (s (L.addLayout.A1 j)).toNat * 2 ^ j
    rw [hscpdef, copyReg_preserves_A1]
  have hA2cp : regValRange L.addLayout.A2 scp n = N := by
    rw [← hA2]
    apply Finset.sum_congr rfl
    intro j _
    show (scp (L.addLayout.A2 j)).toNat * 2 ^ j = (s (L.addLayout.A2 j)).toNat * 2 ^ j
    rw [hscpdef, copyReg_preserves_A2]
  have hCaddcp : ∀ j, scp (L.addLayout.Cadd j) = false := by
    intro j; rw [hscpdef, copyReg_preserves_Cadd]; exact hCadd j
  have hC1cp : ∀ j, scp (L.addLayout.C1 j) = false := by
    intro j; rw [hscpdef, copyReg_preserves_C1]; exact hC1 j
  have hC2cp : ∀ j, scp (L.addLayout.C2 j) = false := by
    intro j; rw [hscpdef, copyReg_preserves_C2]; exact hC2 j
  have hanccp : scp L.addLayout.anc = false := by
    rw [hscpdef, copyReg_preserves_anc]; exact hanc
  -- ADD STEP: B ← (a + a) mod N
  have hred := modAdd_correct L.addLayout scp hCaddcp hC1cp hC2cp hanccp h2N hA1cp hA2cp
    hAopcp hBcp haN haN
  show regValRange L.addLayout.B (denote (modAdd L.addLayout) scp) n = (2 * a) % N
  rw [hred, two_mul]

/-- **The modular-doubling output is a genuine residue in `[0, N)`.** Corollary of `modDouble_correct`
and `Nat.mod_lt`. -/
theorem modDouble_in_range (L : ModDoubleLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.Aop i) = false)
    (hCadd : ∀ j, s (L.addLayout.Cadd j) = false) (hC1 : ∀ j, s (L.addLayout.C1 j) = false)
    (hC2 : ∀ j, s (L.addLayout.C2 j) = false) (hanc : s L.addLayout.anc = false)
    {N a : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1 : regValRange L.addLayout.A1 s n = 2 ^ n - N)
    (hA2 : regValRange L.addLayout.A2 s n = N)
    (hB : regValRange L.B s n = a) (haN : a < N) :
    regValRange L.B (denote (modDouble L) s) n < N := by
  rw [modDouble_correct L s hAop0 hCadd hC1 hC2 hanc h2N hA1 hA2 hB haN]
  exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) haN)

/-! ### Derived cost -/

/-- **Copy-step CNOT count:** `n` CNOTs (and zero Toffoli). The copy is `n` `CX` gates. -/
theorem copyReg_cnot (L : ModDoubleLayout m n) :
    (circuitCost (copyReg L)).cnot = n := by
  rw [copyReg]
  suffices h : ∀ (l : List ℕ),
      (circuitCost (l.map (fun i => Gate.CX (L.B i) (L.Aop i)))).cnot = l.length by
    rw [h (List.range n), List.length_range]
  intro l
  induction l with
  | nil => simp [circuitCost]
  | cons i rest ih =>
    have hsplit : (i :: rest).map (fun i => Gate.CX (L.B i) (L.Aop i))
        = [Gate.CX (L.B i) (L.Aop i)] ++ rest.map (fun i => Gate.CX (L.B i) (L.Aop i)) := by
      simp
    rw [hsplit, cost_comp_cnot_count, ih]
    simp only [circuitCost, gateCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons]
    omega

/-- **Copy-step Toffoli count:** zero — the copy is `n` CNOTs, no Toffoli. -/
theorem copyReg_toffoli (L : ModDoubleLayout m n) :
    (circuitCost (copyReg L)).toffoli = 0 := by
  rw [copyReg]
  suffices h : ∀ (l : List ℕ),
      (circuitCost (l.map (fun i => Gate.CX (L.B i) (L.Aop i)))).toffoli = 0 by
    rw [h (List.range n)]
  intro l
  induction l with
  | nil => simp [circuitCost]
  | cons i rest ih =>
    have hsplit : (i :: rest).map (fun i => Gate.CX (L.B i) (L.Aop i))
        = [Gate.CX (L.B i) (L.Aop i)] ++ rest.map (fun i => Gate.CX (L.B i) (L.Aop i)) := by
      simp
    rw [hsplit, cost_comp_toffoli_count, ih]
    simp [circuitCost, gateCost]

/-- **Derived Toffoli cost of the modular doubler**: `12n` Toffolis, from the exhibited gate list.
Copy step `0` (`copyReg_toffoli`, the `n` CNOTs carry no Toffoli) + add step `12n`
(`modularAdd_toffoli`), composed through `cost_comp_toffoli_count`. -/
theorem modDouble_toffoli (L : ModDoubleLayout m n) :
    (circuitCost (modDouble L)).toffoli = 12 * n := by
  rw [modDouble, cost_comp_toffoli_count, copyReg_toffoli, modularAdd_toffoli, Nat.zero_add]

/-- **Copy contributes `n` CNOTs to the doubler** (reported separately; they do not add Toffolis). -/
theorem modDouble_cnot_copy (L : ModDoubleLayout m n) :
    (circuitCost (modDouble L)).cnot = n + (circuitCost (modAdd L.addLayout)).cnot := by
  rw [modDouble, cost_comp_cnot_count, copyReg_cnot]

/-! ### Non-vacuity witness

A concrete 3-bit modular-doubling layout on `Fin 25`, reusing the S6.3b `modAddLayout2`
(operand `Aop → {0,1,2}`, accumulator `B → {3,4,5}`, add-carry `Cadd → {6..9}`, reduce presets /
carries `A1,C1,A2,C2,anc → {10..24}`). `n = 3` is needed (not `n = 2`): the modular adder requires
`2N ≤ 2ⁿ`, so for `N = 3` that forces `2ⁿ ≥ 6`, i.e. `n ≥ 3`.

The concrete runs double modulo `N = 3`: `a = 2 ↦ (2 * 2) mod 3 = 1` and `a = 1 ↦ (2 * 1) mod 3 = 2`,
with the operand `Aop` initialised `0` (so the copy seeds it from `B = a`). -/

/-- A concrete 3-bit modular-doubling layout on `Fin 25`, bundling `modAddLayout2`. -/
def modDoubleLayout2 : ModDoubleLayout 25 3 where
  addLayout := modAddLayout2

/-- The doubler headline is non-vacuous: it applies to the concrete `modDoubleLayout2`. -/
example (s : State 25)
    (hAop0 : ∀ i, i < 3 → s (modDoubleLayout2.Aop i) = false)
    (hCadd : ∀ j, s (modDoubleLayout2.addLayout.Cadd j) = false)
    (hC1 : ∀ j, s (modDoubleLayout2.addLayout.C1 j) = false)
    (hC2 : ∀ j, s (modDoubleLayout2.addLayout.C2 j) = false)
    (hanc : s modDoubleLayout2.addLayout.anc = false)
    (hA1 : regValRange modDoubleLayout2.addLayout.A1 s 3 = 2 ^ 3 - 3)
    (hA2 : regValRange modDoubleLayout2.addLayout.A2 s 3 = 3)
    (hB : regValRange modDoubleLayout2.B s 3 = 2) :
    regValRange modDoubleLayout2.B (denote (modDouble modDoubleLayout2) s) 3 = (2 * 2) % 3 := by
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  exact modDouble_correct modDoubleLayout2 s hAop0 hCadd hC1 hC2 hanc h2N hA1 hA2 hB
    (show (2 : ℕ) < 3 by decide)

/-- Concrete input state for `n = 3, N = 3`: accumulator `B = a` (wires `3,4,5`), operand `Aop = 0`
(wires `0,1,2`), `A1 = 5 = 2³ − 3` (wires `10,12`), `A2 = 3` (wires `17,18`), all carries / ancilla
`false`. Parameterised by the data bits of `a` (on the `B` wires `3,4,5`). -/
def modDoubleState2 (b0 b1 b2 : Bool) : State 25 := fun w =>
  if w = 3 then b0 else if w = 4 then b1 else if w = 5 then b2
  else if w = 10 then true else if w = 12 then true   -- A1 = 5 = 2³ − 3 (bits 0, 2)
  else if w = 17 then true else if w = 18 then true    -- A2 = 3 (bits 0, 1)
  else false

/-- The hypotheses of `modDouble_correct` hold at `modDoubleState2` (operand `0`, carries / ancilla
clear, `A1 = 5`, `A2 = 3`), for any data bits. -/
private theorem modDoubleState2_pre (b0 b1 b2 : Bool) :
    (∀ i, i < 3 → modDoubleState2 b0 b1 b2 (modDoubleLayout2.Aop i) = false)
      ∧ (∀ j, modDoubleState2 b0 b1 b2 (modDoubleLayout2.addLayout.Cadd j) = false)
      ∧ (∀ j, modDoubleState2 b0 b1 b2 (modDoubleLayout2.addLayout.C1 j) = false)
      ∧ (∀ j, modDoubleState2 b0 b1 b2 (modDoubleLayout2.addLayout.C2 j) = false)
      ∧ modDoubleState2 b0 b1 b2 modDoubleLayout2.addLayout.anc = false
      ∧ regValRange modDoubleLayout2.addLayout.A1 (modDoubleState2 b0 b1 b2) 3 = 2 ^ 3 - 3
      ∧ regValRange modDoubleLayout2.addLayout.A2 (modDoubleState2 b0 b1 b2) 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    show modDoubleState2 b0 b1 b2 (modAddLayout2.Aop i) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · intro j; show modDoubleState2 b0 b1 b2 (modAddLayout2.Cadd j) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · intro j; show modDoubleState2 b0 b1 b2 (modAddLayout2.C1 j) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · intro j; show modDoubleState2 b0 b1 b2 (modAddLayout2.C2 j) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · rfl
  · simp [regValRange, Finset.sum_range_succ, modDoubleLayout2, modAddLayout2, modDoubleState2]
  · simp [regValRange, Finset.sum_range_succ, modDoubleLayout2, modAddLayout2, modDoubleState2]

/-- **Concrete run:** `a = 2, N = 3 ↦ (2 * 2) mod 3 = 1`. The full modular doubler on the explicit
25-wire input (operand `0`, accumulator `2`) leaves register `B` holding `1`. -/
example : regValRange modDoubleLayout2.B
    (denote (modDouble modDoubleLayout2) (modDoubleState2 false true false)) 3 = 1 := by
  obtain ⟨hAop0, hCadd, hC1, hC2, hanc, hA1, hA2⟩ := modDoubleState2_pre false true false
  have hB : regValRange modDoubleLayout2.B (modDoubleState2 false true false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, ModDoubleLayout.B, modDoubleLayout2, modAddLayout2,
      modDoubleState2]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  rw [modDouble_correct modDoubleLayout2 (modDoubleState2 false true false) hAop0 hCadd hC1 hC2
    hanc h2N hA1 hA2 hB (show (2 : ℕ) < 3 by decide)]

/-- **Concrete run:** `a = 1, N = 3 ↦ (2 * 1) mod 3 = 2`. -/
example : regValRange modDoubleLayout2.B
    (denote (modDouble modDoubleLayout2) (modDoubleState2 true false false)) 3 = 2 := by
  obtain ⟨hAop0, hCadd, hC1, hC2, hanc, hA1, hA2⟩ := modDoubleState2_pre true false false
  have hB : regValRange modDoubleLayout2.B (modDoubleState2 true false false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, ModDoubleLayout.B, modDoubleLayout2, modAddLayout2,
      modDoubleState2]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  rw [modDouble_correct modDoubleLayout2 (modDoubleState2 true false false) hAop0 hCadd hC1 hC2
    hanc h2N hA1 hA2 hB (show (1 : ℕ) < 3 by decide)]

/-! ### Fast `#eval` cross-check (Eval harness)

`runArr` / `regValRangeArr` (`Eval.lean`) compute the *same* `denote` / `regValRange` value the
theorems are stated about (`regValRangeArr_eq`), but on a strict `Array Bool` — instant, no lazy
`Function.update` blowup. The `#eval`s below print `2a mod N` off register `B` for the two witnesses;
the `decide` `example`s confirm the printed numbers (kernel-reduced through the bridge). -/

-- `a = 2, N = 3 ↦ (2 * 2) mod 3 = 1`. Prints `1`, instantly.
#eval regValRangeArr modDoubleLayout2.B
  (runArr (modDouble modDoubleLayout2) (ofState (modDoubleState2 false true false))) 3
-- 1

-- `a = 1, N = 3 ↦ (2 * 1) mod 3 = 2`. Prints `2`, instantly.
#eval regValRangeArr modDoubleLayout2.B
  (runArr (modDouble modDoubleLayout2) (ofState (modDoubleState2 true false false))) 3
-- 2

-- Green, fast, theorem-independent value check: the `Array`-backed read is `1`, by `decide`.
set_option maxRecDepth 4000 in
example : regValRangeArr modDoubleLayout2.B
    (runArr (modDouble modDoubleLayout2) (ofState (modDoubleState2 false true false))) 3 = 1 := by
  decide

-- The `a = 1 ↦ 2` witness: the `Array`-backed read is `2`, by `decide`.
set_option maxRecDepth 4000 in
example : regValRangeArr modDoubleLayout2.B
    (runArr (modDouble modDoubleLayout2) (ofState (modDoubleState2 true false false))) 3 = 2 := by
  decide

/-- The cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`, the fast
`Array` value (`1`, above) *is* the `regValRange (denote …)` quantity `modDouble_correct` constrains. -/
example : regValRangeArr modDoubleLayout2.B
    (runArr (modDouble modDoubleLayout2) (ofState (modDoubleState2 false true false))) 3
      = regValRange modDoubleLayout2.B (denote (modDouble modDoubleLayout2)
        (modDoubleState2 false true false)) 3 :=
  regValRangeArr_eq modDoubleLayout2.B (modDouble modDoubleLayout2)
    (modDoubleState2 false true false) 3

end Reversible
