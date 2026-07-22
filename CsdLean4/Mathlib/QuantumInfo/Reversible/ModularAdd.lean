/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduceCtrl

/-!
# Reversible modular addition — the verified value primitive `(a, b) ↦ (a, (a+b) mod N)`  (ECDLP Phase 2, Stage S6.3b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module **verifies the modular-addition VALUE primitive** `(a, b) ↦ (a, (a + b) mod N)` over bit
registers, by chaining two already-verified blocks:

```
modAdd L = rippleCirc L.addStep ++ modReduce L.reduceStep
```

* **Add step** `rippleCirc L.addStep` (`Aop` = the operand `a`, read-only addend; `B` holds `b`; fresh
  carry chain `Cadd`): with `a, b < N` and `2N ≤ 2ⁿ` (so `a + b < 2N ≤ 2ⁿ`), `rippleCirc_correct`
  gives `B ← (a + b) mod 2ⁿ = a + b` (NO wrap, via `Nat.mod_eq_of_lt`).
* **Reduce step** `modReduce L.reduceStep` (S6.3a): now `B` holds `x = a + b < 2N`, so
  `modReduce_correct` applies and leaves `B ← x mod N = (a + b) mod N`.

The single load-bearing range fact is `a + b < 2N`: it is what makes the **single-step** S6.3a
reduction apply (a `2w`-bit product would need the iterated schedule). The add step's carry chain
`Cadd` is disjoint from everything the reduce step touches (`A1, A2, C1, C2, anc, B`), so after the
add: `A1/A2` are still at their presets and `C1/C2/anc` are still `false` (frame lemmas below). `B`
after the add is exactly `a + b`.

## Carve line (what this is, and is NOT)

This is the **value-correct modular-addition atom in the fresh-ancilla model**. Group-law / field
semantics are NOT in play here: this is `ℕ` / `mod N` bit arithmetic.

**Named residue (do NOT read this as a clean reusable in-place primitive):**

1. **Dirty carries / flag (the genuine S6.3b-cleanup residue).** The carry chains `Cadd`, `C1`, `C2`
   and the comparison flag `C1 n` are left **dirty** after `modAdd`. Correctness holds *because the
   layout supplies fresh wires per use* (`modAdd_correct` requires `C* / anc` initialised `false`). In-
   place reuse across many additions needs **carry-clean / ancilla-restoring** adders — which the
   corpus's `rippleCirc`/`cRippleCirc` do NOT provide. Closing this needs either Cuccaro-style inline
   carry-uncompute adders, or reversing the carry generation, or the high-bit self-cleaning modular-
   adder variant. That is the genuine remaining S6.3b-cleanup work, NOT built here.
2. **Uncontrolled only.** This is the UNCONTROLLED modular adder. The CONTROLLED version (S6.3b-2) and
   the interleaved MSB-first double-and-reduce modular MULTIPLY over `𝔽_p` (S6.3c) are the subsequent
   tranches. This module is the arithmetic core a modular multiply iterates.

So: a verified modular-addition *value* atom with dirty carries (fresh-ancilla model), NOT the modular
multiply and NOT a clean in-place adder.

## Honest cost

`modularAdd_toffoli` derives `12n` Toffolis from the exhibited gate list: add step `2n`
(`rippleCirc`, the `rippleAdder`-style ripple count) + reduce step `10n` (`modReduceCtrl_toffoli`),
composed through `cost_comp_toffoli_count`.
-/

@[expose] public section

namespace Reversible

variable {m n : ℕ}

/-- A modular-addition layout on `Fin m` for `n`-bit registers. Bundles the operand register `Aop`
(read-only addend `a`), the accumulator `B` (holds `b`, overwritten with `(a+b) mod N`), the add
step's own carry chain `Cadd`, and the reduce sub-data (`A1, A2, C1, C2`, `anc`).

The geometry fields give: (i) `addStep : RippleLayout` well-formed (`Aop`, `B`, `Cadd` pairwise
disjoint + bounded-injective), (ii) `reduceStep : ModReduceLayout` well-formed, and (iii) `Cadd` and
`Aop` disjoint from every reduce-step wire so the add step's carries are fresh and the operand
survives the whole circuit.

Injectivity fields are **bounded** (`< n` for registers, `< n + 1` for carry chains), exactly as
`ModReduceLayout` / `MulLayout`: an unbounded `ℕ → Fin m` injectivity field is uninhabitable and would
make the theorems vacuous. -/
structure ModAddLayout (m n : ℕ) where
  /-- Operand register: holds `a`, read-only addend (preserved by `modAdd`). -/
  Aop : ℕ → Fin m
  /-- Accumulator: holds `b`, overwritten with `(a + b) mod N`. -/
  B : ℕ → Fin m
  /-- Add-step carry chain (disjoint from the reduce step). -/
  Cadd : ℕ → Fin m
  /-- Reduce step-1 constant register (preset to `2ⁿ − N`). -/
  A1 : ℕ → Fin m
  /-- Reduce step-1 carry chain; `C1 n` is the comparison flag. -/
  C1 : ℕ → Fin m
  /-- Reduce step-3 constant register (preset to `N`). -/
  A2 : ℕ → Fin m
  /-- Reduce step-3 carry chain. -/
  C2 : ℕ → Fin m
  /-- Reduce shared clean ancilla. -/
  anc : Fin m
  -- add-step register geometry (Aop, B, Cadd pairwise disjoint + bounded injective)
  hAopB : ∀ i j, Aop i ≠ B j
  hAopCadd : ∀ i j, Aop i ≠ Cadd j
  hBCadd : ∀ i j, B i ≠ Cadd j
  hAopinj : ∀ i j, i < n → j < n → Aop i = Aop j → i = j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hCaddinj : ∀ i j, i < n + 1 → j < n + 1 → Cadd i = Cadd j → i = j
  -- reduce step-1 register geometry (A1, B, C1 pairwise disjoint + injective)
  hBA1 : ∀ i j, B i ≠ A1 j
  hBC1 : ∀ i j, B i ≠ C1 j
  hA1C1 : ∀ i j, A1 i ≠ C1 j
  hA1inj : ∀ i j, i < n → j < n → A1 i = A1 j → i = j
  hC1inj : ∀ i j, i < n + 1 → j < n + 1 → C1 i = C1 j → i = j
  -- reduce step-3 register geometry (A2, B, C2 pairwise disjoint + injective)
  hBA2 : ∀ i j, B i ≠ A2 j
  hBC2 : ∀ i j, B i ≠ C2 j
  hA2C2 : ∀ i j, A2 i ≠ C2 j
  hA2inj : ∀ i j, i < n → j < n → A2 i = A2 j → i = j
  hC2inj : ∀ i j, i < n + 1 → j < n + 1 → C2 i = C2 j → i = j
  -- the flag (= C1 n) controls reduce step 3; disjoint from step-3 registers
  hflagA2 : ∀ j, C1 n ≠ A2 j
  hflagB : ∀ j, C1 n ≠ B j
  hflagC2 : ∀ j, C1 n ≠ C2 j
  hflaganc : C1 n ≠ anc
  -- the ancilla is disjoint from step-3 registers
  hancA2 : ∀ j, anc ≠ A2 j
  hancB : ∀ j, anc ≠ B j
  hancC2 : ∀ j, anc ≠ C2 j
  -- reduce cross-step disjointness (step-3 wires untouched by step 1 + the X flip)
  hA2A1 : ∀ i j, A2 i ≠ A1 j
  hA2C1 : ∀ i j, A2 i ≠ C1 j
  hC2A1 : ∀ i j, C2 i ≠ A1 j
  hC2C1 : ∀ i j, C2 i ≠ C1 j
  hancA1 : ∀ j, anc ≠ A1 j
  hancC1 : ∀ j, anc ≠ C1 j
  -- the add-step carry chain `Cadd` is disjoint from every reduce-step wire
  hCaddA1 : ∀ i j, Cadd i ≠ A1 j
  hCaddC1 : ∀ i j, Cadd i ≠ C1 j
  hCaddA2 : ∀ i j, Cadd i ≠ A2 j
  hCaddC2 : ∀ i j, Cadd i ≠ C2 j
  hCaddanc : ∀ i, Cadd i ≠ anc
  -- the operand `Aop` is disjoint from every reduce-step wire (so it survives the reduce)
  hAopA1 : ∀ i j, Aop i ≠ A1 j
  hAopC1 : ∀ i j, Aop i ≠ C1 j
  hAopA2 : ∀ i j, Aop i ≠ A2 j
  hAopC2 : ∀ i j, Aop i ≠ C2 j
  hAopanc : ∀ i, Aop i ≠ anc

variable {L : ModAddLayout m n}

/-- The add step as a `RippleLayout`: operand `Aop` + accumulator `B` + add-carry chain `Cadd`. -/
def ModAddLayout.addStep (L : ModAddLayout m n) : RippleLayout m n where
  A := L.Aop
  B := L.B
  C := L.Cadd
  hAB := L.hAopB
  hAC := L.hAopCadd
  hBC := L.hBCadd
  hAinj := L.hAopinj
  hBinj := L.hBinj
  hCinj := L.hCaddinj

/-- The reduce step as a `ModReduceLayout` (S6.3a). -/
def ModAddLayout.reduceStep (L : ModAddLayout m n) : ModReduceLayout m n where
  B := L.B
  A1 := L.A1
  C1 := L.C1
  A2 := L.A2
  C2 := L.C2
  anc := L.anc
  hBA1 := L.hBA1
  hBC1 := L.hBC1
  hA1C1 := L.hA1C1
  hBinj := L.hBinj
  hA1inj := L.hA1inj
  hC1inj := L.hC1inj
  hBA2 := L.hBA2
  hBC2 := L.hBC2
  hA2C2 := L.hA2C2
  hA2inj := L.hA2inj
  hC2inj := L.hC2inj
  hflagA2 := L.hflagA2
  hflagB := L.hflagB
  hflagC2 := L.hflagC2
  hflaganc := L.hflaganc
  hancA2 := L.hancA2
  hancB := L.hancB
  hancC2 := L.hancC2
  hA2A1 := L.hA2A1
  hA2C1 := L.hA2C1
  hC2A1 := L.hC2A1
  hC2C1 := L.hC2C1
  hancA1 := L.hancA1
  hancC1 := L.hancC1

/-- **The modular-addition circuit.** Register add (`rippleCirc`) followed by the S6.3a single-step
modular reduction (`modReduce`). -/
def modAdd (L : ModAddLayout m n) : Circuit m :=
  rippleCirc L.addStep ++ modReduce L.reduceStep

/-! ### Frame: a wire disjoint from `addStep`'s registers survives the add step

`rippleCirc L.addStep` touches only the wires `{Aop k, B k, Cadd k}` (the slices are
`fullAdder (Aop k) (B k) (Cadd k) (Cadd (k+1))`). Any wire distinct from all of those passes through
unchanged. This is the generic frame lemma; the four corollaries below specialise it to the reduce
step's `A1 / A2 / C1 / C2 / anc` wires. -/

/-- **Generic add-step frame.** A wire `w` with `w ≠ Aop k`, `w ≠ B k`, `w ≠ Cadd k` for all `k` is
left unchanged by `rippleCirc L.addStep`. -/
theorem rippleCirc_addStep_preserves (s : State m) (w : Fin m)
    (hA : ∀ k, w ≠ L.Aop k) (hB : ∀ k, w ≠ L.B k) (hC : ∀ k, w ≠ L.Cadd k) :
    denote (rippleCirc L.addStep) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, _hk, hgk⟩ := hg
  simp only [rippleSlice, fullAdder, ModAddLayout.addStep, List.mem_cons, List.not_mem_nil,
    or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl <;>
    simp [gateWires, hA k, hB k, hC k, hC (k + 1)]

/-- After the add step, `A1` is unchanged on every wire (disjoint from the add step). -/
theorem modAdd_addStep_preserves_A1 (s : State m) (j : ℕ) :
    denote (rippleCirc L.addStep) s (L.A1 j) = s (L.A1 j) :=
  rippleCirc_addStep_preserves s (L.A1 j)
    (fun k => (L.hAopA1 k j).symm) (fun k => (L.hBA1 k j).symm) (fun k => (L.hCaddA1 k j).symm)

/-- After the add step, `A2` is unchanged on every wire. -/
theorem modAdd_addStep_preserves_A2 (s : State m) (j : ℕ) :
    denote (rippleCirc L.addStep) s (L.A2 j) = s (L.A2 j) :=
  rippleCirc_addStep_preserves s (L.A2 j)
    (fun k => (L.hAopA2 k j).symm) (fun k => (L.hBA2 k j).symm) (fun k => (L.hCaddA2 k j).symm)

/-- After the add step, `C1` is unchanged on every wire. -/
theorem modAdd_addStep_preserves_C1 (s : State m) (j : ℕ) :
    denote (rippleCirc L.addStep) s (L.C1 j) = s (L.C1 j) :=
  rippleCirc_addStep_preserves s (L.C1 j)
    (fun k => (L.hAopC1 k j).symm) (fun k => (L.hBC1 k j).symm) (fun k => (L.hCaddC1 k j).symm)

/-- After the add step, `C2` is unchanged on every wire. -/
theorem modAdd_addStep_preserves_C2 (s : State m) (j : ℕ) :
    denote (rippleCirc L.addStep) s (L.C2 j) = s (L.C2 j) :=
  rippleCirc_addStep_preserves s (L.C2 j)
    (fun k => (L.hAopC2 k j).symm) (fun k => (L.hBC2 k j).symm) (fun k => (L.hCaddC2 k j).symm)

/-- After the add step, `anc` is unchanged. -/
theorem modAdd_addStep_preserves_anc (s : State m) :
    denote (rippleCirc L.addStep) s L.anc = s L.anc :=
  rippleCirc_addStep_preserves s L.anc
    (fun k => (L.hAopanc k).symm) (fun k => L.hancB k)
    (fun k => (L.hCaddanc k).symm)

/-! ### Frame: the operand `Aop` survives the reduce step

`modReduce L.reduceStep` touches only `{A1, A2, C1, C2, anc, B}` (and the flag `C1 n`). Since `Aop`
is disjoint from all of these, the operand passes through the reduce step unchanged. -/

/-- **Operand frame through the reduce step.** `Aop j` is untouched by `modReduce L.reduceStep`. -/
theorem modReduce_reduceStep_preserves_Aop (s : State m) (j : ℕ) :
    denote (modReduce L.reduceStep) s (L.Aop j) = s (L.Aop j) := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [modReduce, List.append_assoc, List.mem_append] at hg
  rcases hg with hg | hg
  · -- step 1: rippleCirc L.reduceStep.stepOne, wires {A1, B, C1}
    rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
    obtain ⟨k, _hk, hgk⟩ := hg
    simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, ModAddLayout.reduceStep,
      List.mem_cons, List.not_mem_nil, or_false] at hgk
    rcases hgk with rfl | rfl | rfl | rfl <;>
      simp [gateWires, L.hAopA1 j k, L.hAopB j k, L.hAopC1 j k, L.hAopC1 j (k + 1)]
  · rw [List.mem_append] at hg
    rcases hg with hg | hg
    · -- step 2: [X (C1 n)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp [gateWires, ModAddLayout.reduceStep, L.hAopC1 j n]
    · -- step 3: cRippleCirc L.reduceStep.stepThree
      rw [cRippleCirc, cRipplePrefix, List.mem_flatMap] at hg
      obtain ⟨k, _hk, hgk⟩ := hg
      simp only [cRippleSlice, cfullAdder, ModReduceLayout.stepThree, ModAddLayout.reduceStep,
        List.mem_cons, List.not_mem_nil, or_false] at hgk
      rcases hgk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [gateWires, L.hAopA2 j k, L.hAopB j k, L.hAopC2 j k, L.hAopC2 j (k + 1),
          L.hAopanc j, L.hAopC1 j n]

/-! ### Value correctness -/

/-- **The verified modular-addition value primitive.** For a disjoint-wire `ModAddLayout` with all
carry chains (`Cadd`, `C1`, `C2`) and the ancilla `anc` initialised `false`, register `A1` preset to
`2ⁿ − N`, register `A2` preset to `N`, operand register `Aop` holding `a`, accumulator `B` holding
`b`, with `a < N`, `b < N`, `2N ≤ 2ⁿ` (so `a + b < 2N ≤ 2ⁿ`): `modAdd L` leaves register `B`
holding `(a + b) mod N`.

Proof. The add step (`rippleCirc_correct`) writes `(a + b) mod 2ⁿ = a + b` to `B` (no wrap, since
`a + b < 2N ≤ 2ⁿ`), preserving `Aop = a` (P2 of the ripple invariant) and — via the frame lemmas — the
reduce step's presets `A1 = 2ⁿ − N`, `A2 = N` and clean carries `C1 = C2 = false`, `anc = false`. The
reduce step (`modReduce_correct`, S6.3a) then maps `B = a + b < 2N` to `(a + b) mod N`.

The range hypothesis is taken as `2 * N ≤ 2 ^ n` directly (the honest load-bearing form; the gloss
`N ≤ 2^(n-1)` is only equivalent for `n ≥ 1` and diverges at `n = 0`, so it is avoided):
it forces both `a + b < 2ⁿ`, so the add does not wrap, and
`a + b < 2N`, so the single-step S6.3a reduction applies. -/
theorem modAdd_correct (L : ModAddLayout m n) (s : State m)
    (hCadd : ∀ j, s (L.Cadd j) = false) (hC1 : ∀ j, s (L.C1 j) = false)
    (hC2 : ∀ j, s (L.C2 j) = false) (hanc : s L.anc = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1 : regValRange L.A1 s n = 2 ^ n - N) (hA2 : regValRange L.A2 s n = N)
    (hAop : regValRange L.Aop s n = a) (hB : regValRange L.B s n = b)
    (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (modAdd L) s) n = (a + b) % N := by
  have hNpos : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le a) haN
  have hNle : N ≤ 2 ^ n := by omega
  -- decompose the circuit at the add step
  set sadd := denote (rippleCirc L.addStep) s with hsadddef
  have hdenote : denote (modAdd L) s = denote (modReduce L.reduceStep) sadd := by
    rw [modAdd, denote_append, ← hsadddef]
  rw [hdenote]
  -- ADD STEP value: B ← (a + b) mod 2ⁿ = a + b (no wrap)
  have habsum : a + b < 2 ^ n := by omega
  have hBadd : regValRange L.B sadd n = a + b := by
    have := rippleCirc_correct L.addStep s (by intro j; exact hCadd j)
    simp only [ModAddLayout.addStep, hAop, hB, hsadddef] at this ⊢
    rw [this, Nat.mod_eq_of_lt habsum]
  -- ADD STEP frame: reduce-step presets / clean carries survive
  have hA1add : regValRange L.reduceStep.A1 sadd n = 2 ^ n - N := by
    rw [← hA1]
    apply Finset.sum_congr rfl
    intro j _
    show (sadd (L.A1 j)).toNat * 2 ^ j = (s (L.A1 j)).toNat * 2 ^ j
    rw [hsadddef, modAdd_addStep_preserves_A1]
  have hA2add : regValRange L.reduceStep.A2 sadd n = N := by
    rw [← hA2]
    apply Finset.sum_congr rfl
    intro j _
    show (sadd (L.A2 j)).toNat * 2 ^ j = (s (L.A2 j)).toNat * 2 ^ j
    rw [hsadddef, modAdd_addStep_preserves_A2]
  have hC1add : ∀ j, sadd (L.reduceStep.C1 j) = false := by
    intro j; show sadd (L.C1 j) = false
    rw [hsadddef, modAdd_addStep_preserves_C1]; exact hC1 j
  have hC2add : ∀ j, sadd (L.reduceStep.C2 j) = false := by
    intro j; show sadd (L.C2 j) = false
    rw [hsadddef, modAdd_addStep_preserves_C2]; exact hC2 j
  have hancadd : sadd L.reduceStep.anc = false := by
    show sadd L.anc = false
    rw [hsadddef, modAdd_addStep_preserves_anc]; exact hanc
  have hBaddR : regValRange L.reduceStep.B sadd n = a + b := hBadd
  have hx2N : regValRange L.reduceStep.B sadd n < 2 * N := by rw [hBaddR]; omega
  -- REDUCE STEP: B ← (a + b) mod N
  have hred := modReduce_correct L.reduceStep sadd hC1add hC2add hancadd hNle hA1add hA2add hx2N
  rw [show L.reduceStep.B = L.B from rfl] at hred
  rw [hred, hBadd]

/-- **The operand register is intact.** `modAdd L` leaves `Aop` holding `a` (read-only addend). The
add step preserves `Aop` (P2 of the ripple invariant) and the reduce step is disjoint from `Aop`. -/
theorem modAdd_preserves_operand (L : ModAddLayout m n) (s : State m)
    (hCadd : ∀ j, s (L.Cadd j) = false) {a : ℕ} (hAop : regValRange L.Aop s n = a) :
    regValRange L.Aop (denote (modAdd L) s) n = a := by
  rw [← hAop]
  set sadd := denote (rippleCirc L.addStep) s with hsadddef
  have hdenote : denote (modAdd L) s = denote (modReduce L.reduceStep) sadd := by
    rw [modAdd, denote_append, ← hsadddef]
  rw [hdenote]
  -- add step preserves Aop (ripple invariant P2)
  obtain ⟨-, hP2, -, -⟩ := rippleCirc_invariant L.addStep s (by intro j; exact hCadd j) n (le_refl n)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  show (denote (modReduce L.reduceStep) sadd (L.Aop j)).toNat * 2 ^ j
      = (s (L.Aop j)).toNat * 2 ^ j
  rw [modReduce_reduceStep_preserves_Aop]
  have hAk : sadd (L.Aop j) = s (L.Aop j) := by
    rw [hsadddef, rippleCirc]
    exact hP2 j hj
  rw [hAk]

/-- **The modular-addition output is a genuine residue in `[0, N)`.** Corollary of `modAdd_correct`
and `Nat.mod_lt`. -/
theorem modAdd_in_range (L : ModAddLayout m n) (s : State m)
    (hCadd : ∀ j, s (L.Cadd j) = false) (hC1 : ∀ j, s (L.C1 j) = false)
    (hC2 : ∀ j, s (L.C2 j) = false) (hanc : s L.anc = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1 : regValRange L.A1 s n = 2 ^ n - N) (hA2 : regValRange L.A2 s n = N)
    (hAop : regValRange L.Aop s n = a) (hB : regValRange L.B s n = b)
    (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (modAdd L) s) n < N := by
  rw [modAdd_correct L s hCadd hC1 hC2 hanc h2N hA1 hA2 hAop hB haN hbN]
  exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) haN)

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the modular adder**: `12n` Toffolis, from the exhibited gate list. Add
step `2n` (`rippleCirc`, the same ripple count as `rippleAdder`) + reduce step `10n`
(`modReduceCtrl_toffoli`), composed through `cost_comp_toffoli_count`. -/
theorem modularAdd_toffoli (L : ModAddLayout m n) :
    (circuitCost (modAdd L)).toffoli = 12 * n := by
  rw [modAdd, cost_comp_toffoli_count, modReduceCtrl_toffoli]
  -- add step ripple: 2n (same induction as `modReduceCtrl_toffoli`'s step-1)
  have hadd : (circuitCost (rippleCirc L.addStep)).toffoli = 2 * n := by
    rw [rippleCirc, ripplePrefix]
    suffices h : ∀ k, (circuitCost ((List.range k).flatMap (rippleSlice L.addStep))).toffoli = 2 * k
      from h n
    intro k
    induction k with
    | zero => simp [circuitCost]
    | succ k ih =>
      have hsplit : (List.range (k + 1)).flatMap (rippleSlice L.addStep)
          = (List.range k).flatMap (rippleSlice L.addStep) ++ rippleSlice L.addStep k := by
        rw [List.range_succ, List.flatMap_append]; simp
      rw [hsplit, cost_comp_toffoli_count, ih, rippleSlice, fullAdder_toffoli]
      omega
  rw [hadd]
  omega

/-! ### Non-vacuity witness

A concrete 3-bit modular-addition layout on `Fin 25`:
* operand `Aop → {0,1,2}`, accumulator `B → {3,4,5}`, add-carry `Cadd → {6,7,8,9}`,
* reduce step-1 constant `A1 → {10,11,12}`, step-1 carry `C1 → {13,14,15,16}`,
* reduce step-3 constant `A2 → {17,18,19}`, step-3 carry `C2 → {20,21,22,23}`, ancilla `24`.

(`n = 3` is needed, not `n = 2`: the modular adder requires `2N ≤ 2ⁿ` so the add does not wrap; for
`N = 3` that forces `2ⁿ ≥ 6`, i.e. `n ≥ 3`. At `n = 2` the case `a = b = 2` gives `a + b = 4 = 2²`,
which would wrap.) This exhibits that `ModAddLayout` is inhabited, so the headlines are not vacuously
quantified. The concrete runs below add modulo `N = 3` at fully specified input states:
`a = 2, b = 2 ↦ (2 + 2) mod 3 = 1` and `a = 1, b = 1 ↦ (1 + 1) mod 3 = 2`. -/

/-- A concrete 3-bit modular-addition layout on `Fin 25`. -/
def modAddLayout2 : ModAddLayout 25 3 where
  Aop i := if i = 0 then 0 else if i = 1 then 1 else 2
  B i := if i = 0 then 3 else if i = 1 then 4 else 5
  Cadd i := if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else 9
  A1 i := if i = 0 then 10 else if i = 1 then 11 else 12
  C1 i := if i = 0 then 13 else if i = 1 then 14 else if i = 2 then 15 else 16
  A2 i := if i = 0 then 17 else if i = 1 then 18 else 19
  C2 i := if i = 0 then 20 else if i = 1 then 21 else if i = 2 then 22 else 23
  anc := 24
  hAopB i j := by split_ifs <;> decide
  hAopCadd i j := by split_ifs <;> decide
  hBCadd i j := by split_ifs <;> decide
  hAopinj i j hi hj h := by split_ifs at h <;> omega
  hBinj i j hi hj h := by split_ifs at h <;> omega
  hCaddinj i j hi hj h := by split_ifs at h <;> omega
  hBA1 i j := by split_ifs <;> decide
  hBC1 i j := by split_ifs <;> decide
  hA1C1 i j := by split_ifs <;> decide
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
  hCaddA1 i j := by split_ifs <;> decide
  hCaddC1 i j := by split_ifs <;> decide
  hCaddA2 i j := by split_ifs <;> decide
  hCaddC2 i j := by split_ifs <;> decide
  hCaddanc i := by split_ifs <;> decide
  hAopA1 i j := by split_ifs <;> decide
  hAopC1 i j := by split_ifs <;> decide
  hAopA2 i j := by split_ifs <;> decide
  hAopC2 i j := by split_ifs <;> decide
  hAopanc i := by split_ifs <;> decide

/-- The headline is non-vacuous: it applies to the concrete `modAddLayout2`. -/
example (s : State 25)
    (hCadd : ∀ j, s (modAddLayout2.Cadd j) = false) (hC1 : ∀ j, s (modAddLayout2.C1 j) = false)
    (hC2 : ∀ j, s (modAddLayout2.C2 j) = false) (hanc : s modAddLayout2.anc = false)
    (hA1 : regValRange modAddLayout2.A1 s 3 = 2 ^ 3 - 3)
    (hA2 : regValRange modAddLayout2.A2 s 3 = 3)
    (hAop : regValRange modAddLayout2.Aop s 3 = 2) (hB : regValRange modAddLayout2.B s 3 = 2) :
    regValRange modAddLayout2.B (denote (modAdd modAddLayout2) s) 3 = (2 + 2) % 3 := by
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  exact modAdd_correct modAddLayout2 s hCadd hC1 hC2 hanc h2N hA1 hA2 hAop hB
    (by decide) (by decide)

/-- Concrete input state for `n = 3, N = 3`: operand `Aop = a` (wires `0,1,2`), accumulator `B = b`
(wires `3,4,5`), `A1 = 5 = 2³ − 3` (wires `10,12`, bits `0` and `2`), `A2 = 3` (wires `17,18`), all
carries / ancilla `false`. Parameterised by the data bits of `a` (wires `0,1,2`) and `b` (wires
`3,4,5`). -/
def modAddState2 (a0 a1 a2 b0 b1 b2 : Bool) : State 25 := fun w =>
  if w = 0 then a0 else if w = 1 then a1 else if w = 2 then a2
  else if w = 3 then b0 else if w = 4 then b1 else if w = 5 then b2
  else if w = 10 then true else if w = 12 then true   -- A1 = 5 = 2³ − 3 (bits 0, 2)
  else if w = 17 then true else if w = 18 then true    -- A2 = 3 (bits 0, 1)
  else false

/-- The hypotheses of `modAdd_correct` hold at `modAddState2` (carries/ancilla clear, `A1 = 5`,
`A2 = 3`), for any data bits. The `regValRange` register-value preconditions are concrete sums,
discharged by `decide`. -/
theorem modAddState2_pre (a0 a1 a2 b0 b1 b2 : Bool) :
    (∀ j, modAddState2 a0 a1 a2 b0 b1 b2 (modAddLayout2.Cadd j) = false)
      ∧ (∀ j, modAddState2 a0 a1 a2 b0 b1 b2 (modAddLayout2.C1 j) = false)
      ∧ (∀ j, modAddState2 a0 a1 a2 b0 b1 b2 (modAddLayout2.C2 j) = false)
      ∧ modAddState2 a0 a1 a2 b0 b1 b2 modAddLayout2.anc = false
      ∧ regValRange modAddLayout2.A1 (modAddState2 a0 a1 a2 b0 b1 b2) 3 = 2 ^ 3 - 3
      ∧ regValRange modAddLayout2.A2 (modAddState2 a0 a1 a2 b0 b1 b2) 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; show modAddState2 a0 a1 a2 b0 b1 b2 (modAddLayout2.Cadd j) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · intro j; show modAddState2 a0 a1 a2 b0 b1 b2 (modAddLayout2.C1 j) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · intro j; show modAddState2 a0 a1 a2 b0 b1 b2 (modAddLayout2.C2 j) = false
    simp only [modAddLayout2]; split_ifs <;> rfl
  · rfl
  · simp [regValRange, Finset.sum_range_succ, modAddLayout2, modAddState2]
  · simp [regValRange, Finset.sum_range_succ, modAddLayout2, modAddState2]

/-- **Concrete run:** `a = 2, b = 2, N = 3 ↦ (2 + 2) mod 3 = 1`. The full modular adder on the
explicit 25-wire input leaves register `B` holding `1`. -/
example : regValRange modAddLayout2.B
    (denote (modAdd modAddLayout2) (modAddState2 false true false false true false)) 3 = 1 := by
  obtain ⟨hCadd, hC1, hC2, hanc, hA1, hA2⟩ := modAddState2_pre false true false false true false
  have hAop : regValRange modAddLayout2.Aop
      (modAddState2 false true false false true false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, modAddLayout2, modAddState2]
  have hB : regValRange modAddLayout2.B
      (modAddState2 false true false false true false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, modAddLayout2, modAddState2]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  rw [modAdd_correct modAddLayout2 (modAddState2 false true false false true false) hCadd hC1 hC2
    hanc h2N hA1 hA2 hAop hB (by decide) (by decide)]

/-- **Concrete run:** `a = 1, b = 1, N = 3 ↦ (1 + 1) mod 3 = 2`. -/
example : regValRange modAddLayout2.B
    (denote (modAdd modAddLayout2) (modAddState2 true false false true false false)) 3 = 2 := by
  obtain ⟨hCadd, hC1, hC2, hanc, hA1, hA2⟩ := modAddState2_pre true false false true false false
  have hAop : regValRange modAddLayout2.Aop
      (modAddState2 true false false true false false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, modAddLayout2, modAddState2]
  have hB : regValRange modAddLayout2.B
      (modAddState2 true false false true false false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, modAddLayout2, modAddState2]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  rw [modAdd_correct modAddLayout2 (modAddState2 true false false true false false) hCadd hC1 hC2
    hanc h2N hA1 hA2 hAop hB (by decide) (by decide)]

end Reversible
