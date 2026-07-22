/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAdd

/-!
# Reversible controlled modular addition — `(ctrl, a, b) ↦ if ctrl then (a+b) mod N else b`  (ECDLP Phase 2, Stage S6.3c)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module **verifies the controlled modular-addition VALUE primitive** — the controlled analogue of
S6.3b's `modAdd` — by chaining two already-verified blocks:

```
cModAdd L = cRippleCirc L.cAddStep ++ modReduce L.reduceStep
```

* **Controlled add step** `cRippleCirc L.cAddStep` (S2): addend `Aop` (= `a`, read-only), accumulator
  `B` (= `b`), control wire `ctrl`, the cRipple carry chain `Ccadd`, shared ancilla `ancC` (restored by
  `cRippleCirc_anc_restored`). With `a + b < 2N ≤ 2ⁿ`, `cRippleCirc_correct` gives
  `B ← if ctrl then (a + b) mod 2ⁿ else b = if ctrl then a + b else b` (no wrap). In **both** branches
  `B < 2N` (ctrl: `a + b < 2N`; ¬ctrl: `b < N < 2N`).
* **Reduce step** `modReduce L.reduceStep` (S6.3a) — **UNCONDITIONAL, it always runs**: since `B < 2N`
  in both branches, `modReduce_correct` maps `B ← B mod N`. In the ctrl branch that is `(a + b) mod N`;
  in the ¬ctrl branch it is `b mod N = b` (since `b < N`). **The reduce being unconditional is the whole
  trick:** `b` is already a valid reduced residue, so reducing it again is the identity.

So the headline value is `B ← if ctrl then (a + b) mod N else b`.

## Carve line (what this is, and is NOT)

This **VERIFIES the controlled modular-addition value primitive** `B ← if ctrl then (a+b) mod N else b`
by chaining the verified `cRippleCirc` (S2) with S6.3a's `modReduce`; the unconditional reduce is
correct in both branches because `b < N` is already a valid residue. This is `ℕ` / `mod N` bit
arithmetic — NO field / group semantics are in play.

This is the inner-loop primitive of the interleaved MSB-first modular MULTIPLY over `𝔽_p` (the next
stage, **S6.3d**), which also needs a modular DOUBLING gadget (`2·acc mod N`, the register-to-itself
add) and the Horner loop invariant. **This module is NOT the multiply.**

**Named residue (same as S6.3b; name it):** the carry chains `Ccadd`, `C1`, `C2` and the comparison
flag `C1 n` are left **DIRTY** after `cModAdd`. Correctness holds *because the layout supplies fresh
wires per use* (`cModAdd_correct` requires `C* / anc` initialised `false`). In-place reuse across the
many additions of a modular multiply needs **carry-clean / ancilla-restoring** adders (Cuccaro-style
inline carry-uncompute, or reversing carry generation) which the corpus's `rippleCirc` / `cRippleCirc`
do NOT provide. That carry-clean adder is the genuine orthogonal residue, NOT built here.

## Honest cost

`cModularAdd_toffoli` derives `18n` Toffolis from the exhibited gate list: controlled add step `8n`
(`cRippleCirc_toffoli`, the quantum×quantum overhead) + reduce step `10n` (`modReduceCtrl_toffoli`),
composed through `cost_comp_toffoli_count`. (Heavier than S6.3b's uncontrolled `12n` precisely by the
`4×` quantum×quantum cost of the controlled add, `8n` vs `2n`.)
-/

namespace Reversible

variable {m n : ℕ}

/-- A controlled-modular-addition layout on `Fin m` for `n`-bit registers. Like `ModAddLayout` but the
add step is a `CRippleLayout`: it bundles the operand register `Aop` (read-only addend `a`), the
accumulator `B` (holds `b`, overwritten with `if ctrl then (a+b) mod N else b`), the controlled-add
step's own carry chain `Ccadd`, the control wire `ctrl`, the cRipple shared ancilla `ancC`, and the
reduce sub-data (`A1, A2, C1, C2`, `anc`).

The geometry fields give: (i) `cAddStep : CRippleLayout` well-formed (`Aop`, `B`, `Ccadd`, `ctrl`,
`ancC` pairwise disjoint + bounded-injective), (ii) `reduceStep : ModReduceLayout` well-formed, and
(iii) `Ccadd`, `Aop`, `ctrl`, `ancC` all disjoint from every reduce-step wire so the controlled-add
step's carries / ancilla are fresh and the operand + control bit survive the whole circuit.

Injectivity fields are **bounded** (`< n` for registers, `< n + 1` for carry chains), exactly as
`ModAddLayout` / `ModReduceLayout` / `MulLayout`: an unbounded `ℕ → Fin m` injectivity field is
uninhabitable and would make the theorems vacuous. -/
structure CModAddLayout (m n : ℕ) where
  /-- Operand register: holds `a`, read-only addend (preserved by `cModAdd`). -/
  Aop : ℕ → Fin m
  /-- Accumulator: holds `b`, overwritten with `if ctrl then (a + b) mod N else b`. -/
  B : ℕ → Fin m
  /-- Controlled-add-step carry chain (disjoint from the reduce step). -/
  Ccadd : ℕ → Fin m
  /-- The control wire (set ⇒ add `a`; clear ⇒ leave `b`). Read, never written. -/
  ctrl : Fin m
  /-- The controlled-add-step shared clean ancilla (`CCCX` decomposition; restored `false`). -/
  ancC : Fin m
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
  -- controlled-add-step register geometry (Aop, B, Ccadd pairwise disjoint + bounded injective)
  hAopB : ∀ i j, Aop i ≠ B j
  hAopCcadd : ∀ i j, Aop i ≠ Ccadd j
  hBCcadd : ∀ i j, B i ≠ Ccadd j
  hAopinj : ∀ i j, i < n → j < n → Aop i = Aop j → i = j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hCcaddinj : ∀ i j, i < n + 1 → j < n + 1 → Ccadd i = Ccadd j → i = j
  -- control + cRipple ancilla disjoint from the cRipple registers/carries
  hctrlAop : ∀ i, ctrl ≠ Aop i
  hctrlB : ∀ i, ctrl ≠ B i
  hctrlCcadd : ∀ i, ctrl ≠ Ccadd i
  hctrlancC : ctrl ≠ ancC
  hancCAop : ∀ i, ancC ≠ Aop i
  hancCB : ∀ i, ancC ≠ B i
  hancCCcadd : ∀ i, ancC ≠ Ccadd i
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
  -- the reduce ancilla is disjoint from step-3 registers
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
  -- the controlled-add-step carry chain `Ccadd` is disjoint from every reduce-step wire
  hCcaddA1 : ∀ i j, Ccadd i ≠ A1 j
  hCcaddC1 : ∀ i j, Ccadd i ≠ C1 j
  hCcaddA2 : ∀ i j, Ccadd i ≠ A2 j
  hCcaddC2 : ∀ i j, Ccadd i ≠ C2 j
  hCcaddanc : ∀ i, Ccadd i ≠ anc
  -- the operand `Aop` is disjoint from every reduce-step wire (so it survives the reduce)
  hAopA1 : ∀ i j, Aop i ≠ A1 j
  hAopC1 : ∀ i j, Aop i ≠ C1 j
  hAopA2 : ∀ i j, Aop i ≠ A2 j
  hAopC2 : ∀ i j, Aop i ≠ C2 j
  hAopanc : ∀ i, Aop i ≠ anc
  -- the control wire `ctrl` is disjoint from every reduce-step wire (so it survives the reduce)
  hctrlA1 : ∀ j, ctrl ≠ A1 j
  hctrlC1 : ∀ j, ctrl ≠ C1 j
  hctrlA2 : ∀ j, ctrl ≠ A2 j
  hctrlC2 : ∀ j, ctrl ≠ C2 j
  hctrlanc : ctrl ≠ anc
  -- the cRipple ancilla `ancC` is disjoint from every reduce-step wire
  hancCA1 : ∀ j, ancC ≠ A1 j
  hancCC1 : ∀ j, ancC ≠ C1 j
  hancCA2 : ∀ j, ancC ≠ A2 j
  hancCC2 : ∀ j, ancC ≠ C2 j
  hancCanc : ancC ≠ anc

variable {L : CModAddLayout m n}

/-- The controlled add step as a `CRippleLayout`: operand `Aop` + accumulator `B` + add-carry chain
`Ccadd`, controlled on `ctrl`, with shared ancilla `ancC`. -/
def CModAddLayout.cAddStep (L : CModAddLayout m n) : CRippleLayout m n where
  A := L.Aop
  B := L.B
  C := L.Ccadd
  hAB := L.hAopB
  hAC := L.hAopCcadd
  hBC := L.hBCcadd
  hAinj := L.hAopinj
  hBinj := L.hBinj
  hCinj := L.hCcaddinj
  ctrl := L.ctrl
  anc := L.ancC
  hctrlA := L.hctrlAop
  hctrlB := L.hctrlB
  hctrlC := L.hctrlCcadd
  hctrlanc := L.hctrlancC
  hancA := L.hancCAop
  hancB := L.hancCB
  hancC := L.hancCCcadd

/-- The reduce step as a `ModReduceLayout` (S6.3a). -/
def CModAddLayout.reduceStep (L : CModAddLayout m n) : ModReduceLayout m n where
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

/-- **The controlled modular-addition circuit.** Controlled register add (`cRippleCirc`) followed by
the S6.3a single-step modular reduction (`modReduce`), the latter run **unconditionally**. -/
def cModAdd (L : CModAddLayout m n) : Circuit m :=
  cRippleCirc L.cAddStep ++ modReduce L.reduceStep

/-! ### Frame: a wire disjoint from `cAddStep`'s wires survives the controlled add step

`cRippleCirc L.cAddStep` touches only `{ctrl, ancC} ∪ {Aop k, B k, Ccadd k}`. Any wire distinct from all
of those passes through unchanged (`cRippleCirc_preserves_external`). The four corollaries below
specialise it to the reduce step's `A1 / A2 / C1 / C2 / anc` wires. -/

/-- After the controlled add step, `A1` is unchanged on every wire (disjoint from the add step). -/
theorem cModAdd_cAddStep_preserves_A1 (s : State m) (j : ℕ) :
    denote (cRippleCirc L.cAddStep) s (L.A1 j) = s (L.A1 j) :=
  cRippleCirc_preserves_external L.cAddStep s (L.A1 j)
    (fun h => (L.hctrlA1 j) h.symm) (fun h => (L.hancCA1 j) h.symm)
    (fun k _ => (L.hAopA1 k j).symm) (fun k _ => (L.hBA1 k j).symm)
    (fun k _ => (L.hCcaddA1 k j).symm)

/-- After the controlled add step, `A2` is unchanged on every wire. -/
theorem cModAdd_cAddStep_preserves_A2 (s : State m) (j : ℕ) :
    denote (cRippleCirc L.cAddStep) s (L.A2 j) = s (L.A2 j) :=
  cRippleCirc_preserves_external L.cAddStep s (L.A2 j)
    (fun h => (L.hctrlA2 j) h.symm) (fun h => (L.hancCA2 j) h.symm)
    (fun k _ => (L.hAopA2 k j).symm) (fun k _ => (L.hBA2 k j).symm)
    (fun k _ => (L.hCcaddA2 k j).symm)

/-- After the controlled add step, `C1` is unchanged on every wire. -/
theorem cModAdd_cAddStep_preserves_C1 (s : State m) (j : ℕ) :
    denote (cRippleCirc L.cAddStep) s (L.C1 j) = s (L.C1 j) :=
  cRippleCirc_preserves_external L.cAddStep s (L.C1 j)
    (fun h => (L.hctrlC1 j) h.symm) (fun h => (L.hancCC1 j) h.symm)
    (fun k _ => (L.hAopC1 k j).symm) (fun k _ => (L.hBC1 k j).symm)
    (fun k _ => (L.hCcaddC1 k j).symm)

/-- After the controlled add step, `C2` is unchanged on every wire. -/
theorem cModAdd_cAddStep_preserves_C2 (s : State m) (j : ℕ) :
    denote (cRippleCirc L.cAddStep) s (L.C2 j) = s (L.C2 j) :=
  cRippleCirc_preserves_external L.cAddStep s (L.C2 j)
    (fun h => (L.hctrlC2 j) h.symm) (fun h => (L.hancCC2 j) h.symm)
    (fun k _ => (L.hAopC2 k j).symm) (fun k _ => (L.hBC2 k j).symm)
    (fun k _ => (L.hCcaddC2 k j).symm)

/-- After the controlled add step, `anc` is unchanged. -/
theorem cModAdd_cAddStep_preserves_anc (s : State m) :
    denote (cRippleCirc L.cAddStep) s L.anc = s L.anc :=
  cRippleCirc_preserves_external L.cAddStep s L.anc
    (fun h => L.hctrlanc h.symm) (fun h => L.hancCanc h.symm)
    (fun k _ => (L.hAopanc k).symm) (fun k _ => L.hancB k)
    (fun k _ => (L.hCcaddanc k).symm)

/-! ### Frame: the operand `Aop` and the control bit `ctrl` survive the reduce step

`modReduce L.reduceStep` touches only `{A1, A2, C1, C2, anc, B}` (and the flag `C1 n`). Since `Aop` and
`ctrl` are disjoint from all of these, they pass through the reduce step unchanged. -/

/-- **Operand frame through the reduce step.** `Aop j` is untouched by `modReduce L.reduceStep`. -/
theorem cModAdd_reduceStep_preserves_Aop (s : State m) (j : ℕ) :
    denote (modReduce L.reduceStep) s (L.Aop j) = s (L.Aop j) := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [modReduce, List.append_assoc, List.mem_append] at hg
  rcases hg with hg | hg
  · -- step 1: rippleCirc L.reduceStep.stepOne, wires {A1, B, C1}
    rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
    obtain ⟨k, _hk, hgk⟩ := hg
    simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, CModAddLayout.reduceStep,
      List.mem_cons, List.not_mem_nil, or_false] at hgk
    rcases hgk with rfl | rfl | rfl | rfl <;>
      simp [gateWires, L.hAopA1 j k, L.hAopB j k, L.hAopC1 j k, L.hAopC1 j (k + 1)]
  · rw [List.mem_append] at hg
    rcases hg with hg | hg
    · -- step 2: [X (C1 n)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp [gateWires, CModAddLayout.reduceStep, L.hAopC1 j n]
    · -- step 3: cRippleCirc L.reduceStep.stepThree
      rw [cRippleCirc, cRipplePrefix, List.mem_flatMap] at hg
      obtain ⟨k, _hk, hgk⟩ := hg
      simp only [cRippleSlice, cfullAdder, ModReduceLayout.stepThree, CModAddLayout.reduceStep,
        List.mem_cons, List.not_mem_nil, or_false] at hgk
      rcases hgk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [gateWires, L.hAopA2 j k, L.hAopB j k, L.hAopC2 j k, L.hAopC2 j (k + 1),
          L.hAopanc j, L.hAopC1 j n]

/-- **Control frame through the reduce step.** `ctrl` is untouched by `modReduce L.reduceStep`. -/
theorem cModAdd_reduceStep_preserves_ctrl (s : State m) :
    denote (modReduce L.reduceStep) s L.ctrl = s L.ctrl := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [modReduce, List.append_assoc, List.mem_append] at hg
  rcases hg with hg | hg
  · -- step 1: rippleCirc L.reduceStep.stepOne, wires {A1, B, C1}
    rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
    obtain ⟨k, _hk, hgk⟩ := hg
    simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, CModAddLayout.reduceStep,
      List.mem_cons, List.not_mem_nil, or_false] at hgk
    rcases hgk with rfl | rfl | rfl | rfl <;>
      simp [gateWires, L.hctrlA1 k, L.hctrlB k, L.hctrlC1 k, L.hctrlC1 (k + 1)]
  · rw [List.mem_append] at hg
    rcases hg with hg | hg
    · -- step 2: [X (C1 n)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp [gateWires, CModAddLayout.reduceStep, L.hctrlC1 n]
    · -- step 3: cRippleCirc L.reduceStep.stepThree
      rw [cRippleCirc, cRipplePrefix, List.mem_flatMap] at hg
      obtain ⟨k, _hk, hgk⟩ := hg
      simp only [cRippleSlice, cfullAdder, ModReduceLayout.stepThree, CModAddLayout.reduceStep,
        List.mem_cons, List.not_mem_nil, or_false] at hgk
      rcases hgk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [gateWires, L.hctrlA2 k, L.hctrlB k, L.hctrlC2 k, L.hctrlC2 (k + 1),
          L.hctrlanc, L.hctrlC1 n]

/-! ### Value correctness -/

/-- **The verified controlled modular-addition value primitive.** For a disjoint-wire `CModAddLayout`
with all carry chains (`Ccadd`, `C1`, `C2`) and both ancillas (`ancC`, `anc`) initialised `false`,
register `A1` preset to `2ⁿ − N`, register `A2` preset to `N`, operand register `Aop` holding `a`,
accumulator `B` holding `b`, with `a < N`, `b < N`, `2N ≤ 2ⁿ`: `cModAdd L` leaves register `B` holding
`if ctrl then (a + b) mod N else b`.

Proof. The controlled add step (`cRippleCirc_correct`) writes
`if ctrl then (a + b) mod 2ⁿ else b = if ctrl then a + b else b` to `B` (no wrap, since
`a + b < 2N ≤ 2ⁿ`), preserving `Aop = a` and — via the frame lemmas — the reduce step's presets
`A1 = 2ⁿ − N`, `A2 = N` and clean carries `C1 = C2 = false`, `anc = false`. In **both** control
branches `B < 2N` (ctrl: `a + b < 2N`; ¬ctrl: `b < N < 2N`), so the **unconditional** reduce step
(`modReduce_correct`, S6.3a) maps `B` to `B mod N`: `(a + b) mod N` in the ctrl branch, and
`b mod N = b` in the ¬ctrl branch (`b < N`, `Nat.mod_eq_of_lt`). The reduce being unconditional is the
whole trick: `b` is already a valid residue. -/
theorem cModAdd_correct (L : CModAddLayout m n) (s : State m)
    (hCcadd : ∀ j, s (L.Ccadd j) = false) (hancC : s L.ancC = false)
    (hC1 : ∀ j, s (L.C1 j) = false) (hC2 : ∀ j, s (L.C2 j) = false) (hanc : s L.anc = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1 : regValRange L.A1 s n = 2 ^ n - N) (hA2 : regValRange L.A2 s n = N)
    (hAop : regValRange L.Aop s n = a) (hB : regValRange L.B s n = b)
    (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (cModAdd L) s) n = if s L.ctrl then (a + b) % N else b := by
  have hNle : N ≤ 2 ^ n := by omega
  -- decompose the circuit at the controlled add step
  set sadd := denote (cRippleCirc L.cAddStep) s with hsadddef
  have hdenote : denote (cModAdd L) s = denote (modReduce L.reduceStep) sadd := by
    rw [cModAdd, denote_append, ← hsadddef]
  rw [hdenote]
  -- CONTROLLED ADD STEP value: B ← if ctrl then (a+b) mod 2ⁿ = a+b else b  (no wrap)
  have habsum : a + b < 2 ^ n := by omega
  have hBadd : regValRange L.B sadd n = if s L.ctrl then a + b else b := by
    have := cRippleCirc_correct L.cAddStep s (fun j => hCcadd j) hancC
    simp only [CModAddLayout.cAddStep, hAop, hB, hsadddef] at this ⊢
    rw [this]
    cases s L.ctrl with
    | true => simp only [if_true]; rw [Nat.mod_eq_of_lt habsum]
    | false => simp only [Bool.false_eq_true, if_false]
  -- ADD STEP frame: reduce-step presets / clean carries survive
  have hA1add : regValRange L.reduceStep.A1 sadd n = 2 ^ n - N := by
    rw [← hA1]
    apply Finset.sum_congr rfl
    intro j _
    show (sadd (L.A1 j)).toNat * 2 ^ j = (s (L.A1 j)).toNat * 2 ^ j
    rw [hsadddef, cModAdd_cAddStep_preserves_A1]
  have hA2add : regValRange L.reduceStep.A2 sadd n = N := by
    rw [← hA2]
    apply Finset.sum_congr rfl
    intro j _
    show (sadd (L.A2 j)).toNat * 2 ^ j = (s (L.A2 j)).toNat * 2 ^ j
    rw [hsadddef, cModAdd_cAddStep_preserves_A2]
  have hC1add : ∀ j, sadd (L.reduceStep.C1 j) = false := by
    intro j; show sadd (L.C1 j) = false
    rw [hsadddef, cModAdd_cAddStep_preserves_C1]; exact hC1 j
  have hC2add : ∀ j, sadd (L.reduceStep.C2 j) = false := by
    intro j; show sadd (L.C2 j) = false
    rw [hsadddef, cModAdd_cAddStep_preserves_C2]; exact hC2 j
  have hancadd : sadd L.reduceStep.anc = false := by
    show sadd L.anc = false
    rw [hsadddef, cModAdd_cAddStep_preserves_anc]; exact hanc
  -- BOTH branches give B < 2N
  have hBaddR : regValRange L.reduceStep.B sadd n = if s L.ctrl then a + b else b := hBadd
  have hx2N : regValRange L.reduceStep.B sadd n < 2 * N := by
    rw [hBaddR]; cases s L.ctrl <;> simp <;> omega
  -- REDUCE STEP (unconditional): B ← B mod N
  have hred := modReduce_correct L.reduceStep sadd hC1add hC2add hancadd hNle hA1add hA2add hx2N
  rw [show L.reduceStep.B = L.B from rfl] at hred
  rw [hred, hBadd]
  -- evaluate the mod on each branch
  cases s L.ctrl with
  | true => simp only [if_true]
  | false => simp only [Bool.false_eq_true, if_false]; exact Nat.mod_eq_of_lt hbN

/-- **The operand register is intact.** `cModAdd L` leaves `Aop` holding `a` (read-only addend). The
controlled add step preserves `Aop` (P2 of the controlled-ripple invariant) and the reduce step is
disjoint from `Aop`. -/
theorem cModAdd_preserves_operand (L : CModAddLayout m n) (s : State m)
    (hCcadd : ∀ j, s (L.Ccadd j) = false) (hancC : s L.ancC = false) {a : ℕ}
    (hAop : regValRange L.Aop s n = a) :
    regValRange L.Aop (denote (cModAdd L) s) n = a := by
  rw [← hAop]
  set sadd := denote (cRippleCirc L.cAddStep) s with hsadddef
  have hdenote : denote (cModAdd L) s = denote (modReduce L.reduceStep) sadd := by
    rw [cModAdd, denote_append, ← hsadddef]
  rw [hdenote]
  -- controlled add step preserves Aop (controlled-ripple invariant P2)
  obtain ⟨-, hP2, -, -, -, -, -⟩ :=
    cRippleCirc_invariant L.cAddStep s (fun j => hCcadd j) hancC n (le_refl n)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  show (denote (modReduce L.reduceStep) sadd (L.Aop j)).toNat * 2 ^ j
      = (s (L.Aop j)).toNat * 2 ^ j
  rw [cModAdd_reduceStep_preserves_Aop]
  have hAk : sadd (L.Aop j) = s (L.Aop j) := by
    rw [hsadddef, cRippleCirc]
    exact hP2 j hj
  rw [hAk]

/-- **The control bit is preserved.** `cModAdd L` leaves `ctrl` at its initial value (it is read by the
controlled add step, never written, and the reduce step is disjoint from it). The interleaved modular
multiply needs this to keep each partial-product's control bit equal to the original register bit across
the accumulation loop. -/
theorem cModAdd_preserves_ctrl (L : CModAddLayout m n) (s : State m)
    (hCcadd : ∀ j, s (L.Ccadd j) = false) (hancC : s L.ancC = false) :
    denote (cModAdd L) s L.ctrl = s L.ctrl := by
  set sadd := denote (cRippleCirc L.cAddStep) s with hsadddef
  have hdenote : denote (cModAdd L) s = denote (modReduce L.reduceStep) sadd := by
    rw [cModAdd, denote_append, ← hsadddef]
  rw [hdenote, cModAdd_reduceStep_preserves_ctrl, hsadddef]
  -- ctrl = cAddStep.ctrl, preserved by the controlled ripple adder
  exact cRippleCirc_ctrl_preserved L.cAddStep s (fun j => hCcadd j) hancC

/-- **The controlled modular-addition output is a genuine residue in `[0, N)`.** In both branches:
`(a + b) % N < N` (ctrl set) and `b < N` (ctrl clear). Corollary of `cModAdd_correct`. -/
theorem cModAdd_in_range (L : CModAddLayout m n) (s : State m)
    (hCcadd : ∀ j, s (L.Ccadd j) = false) (hancC : s L.ancC = false)
    (hC1 : ∀ j, s (L.C1 j) = false) (hC2 : ∀ j, s (L.C2 j) = false) (hanc : s L.anc = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1 : regValRange L.A1 s n = 2 ^ n - N) (hA2 : regValRange L.A2 s n = N)
    (hAop : regValRange L.Aop s n = a) (hB : regValRange L.B s n = b)
    (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (cModAdd L) s) n < N := by
  rw [cModAdd_correct L s hCcadd hancC hC1 hC2 hanc h2N hA1 hA2 hAop hB haN hbN]
  cases s L.ctrl with
  | true => simp only [if_true]; exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) haN)
  | false => simp only [Bool.false_eq_true, if_false]; exact hbN

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the controlled modular adder**: `18n` Toffolis, from the exhibited gate
list. Controlled add step `8n` (`cRippleCirc_toffoli`, the quantum×quantum overhead) + reduce step `10n`
(`modReduceCtrl_toffoli`), composed through `cost_comp_toffoli_count`. Heavier than S6.3b's uncontrolled
`12n` precisely by the `4×` cost of the controlled add (`8n` vs `2n`). -/
theorem cModularAdd_toffoli (L : CModAddLayout m n) :
    (circuitCost (cModAdd L)).toffoli = 18 * n := by
  rw [cModAdd, cost_comp_toffoli_count, modReduceCtrl_toffoli, cRippleCirc_toffoli]
  omega

/-! ### Non-vacuity witness

A concrete 3-bit controlled-modular-addition layout on `Fin 27`:
* operand `Aop → {0,1,2}`, accumulator `B → {3,4,5}`, controlled-add carry `Ccadd → {6,7,8,9}`,
  control `25`, cRipple ancilla `26`,
* reduce step-1 constant `A1 → {10,11,12}`, step-1 carry `C1 → {13,14,15,16}`,
* reduce step-3 constant `A2 → {17,18,19}`, step-3 carry `C2 → {20,21,22,23}`, reduce ancilla `24`.

(`n = 3` is needed, as in S6.3b: the modular adder requires `2N ≤ 2ⁿ` so the controlled add does not
wrap; for `N = 3` that forces `2ⁿ ≥ 6`, i.e. `n ≥ 3`.) This exhibits that `CModAddLayout` is inhabited,
so the headlines are not vacuously quantified. The concrete runs below exercise **both** control
branches at fully-specified input states: `a = 2, b = 2, N = 3`, `ctrl = true ↦ (2+2) mod 3 = 1`, and
the same `a, b` with `ctrl = false ↦ B stays b = 2`. -/

/-- A concrete 3-bit controlled-modular-addition layout on `Fin 27`. -/
def cModAddLayout2 : CModAddLayout 27 3 where
  Aop i := if i = 0 then 0 else if i = 1 then 1 else 2
  B i := if i = 0 then 3 else if i = 1 then 4 else 5
  Ccadd i := if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else 9
  ctrl := 25
  ancC := 26
  A1 i := if i = 0 then 10 else if i = 1 then 11 else 12
  C1 i := if i = 0 then 13 else if i = 1 then 14 else if i = 2 then 15 else 16
  A2 i := if i = 0 then 17 else if i = 1 then 18 else 19
  C2 i := if i = 0 then 20 else if i = 1 then 21 else if i = 2 then 22 else 23
  anc := 24
  hAopB i j := by split_ifs <;> decide
  hAopCcadd i j := by split_ifs <;> decide
  hBCcadd i j := by split_ifs <;> decide
  hAopinj i j hi hj h := by split_ifs at h <;> omega
  hBinj i j hi hj h := by split_ifs at h <;> omega
  hCcaddinj i j hi hj h := by split_ifs at h <;> omega
  hctrlAop i := by split_ifs <;> decide
  hctrlB i := by split_ifs <;> decide
  hctrlCcadd i := by split_ifs <;> decide
  hctrlancC := by decide
  hancCAop i := by split_ifs <;> decide
  hancCB i := by split_ifs <;> decide
  hancCCcadd i := by split_ifs <;> decide
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
  hCcaddA1 i j := by split_ifs <;> decide
  hCcaddC1 i j := by split_ifs <;> decide
  hCcaddA2 i j := by split_ifs <;> decide
  hCcaddC2 i j := by split_ifs <;> decide
  hCcaddanc i := by split_ifs <;> decide
  hAopA1 i j := by split_ifs <;> decide
  hAopC1 i j := by split_ifs <;> decide
  hAopA2 i j := by split_ifs <;> decide
  hAopC2 i j := by split_ifs <;> decide
  hAopanc i := by split_ifs <;> decide
  hctrlA1 j := by split_ifs <;> decide
  hctrlC1 j := by split_ifs <;> decide
  hctrlA2 j := by split_ifs <;> decide
  hctrlC2 j := by split_ifs <;> decide
  hctrlanc := by decide
  hancCA1 j := by split_ifs <;> decide
  hancCC1 j := by split_ifs <;> decide
  hancCA2 j := by split_ifs <;> decide
  hancCC2 j := by split_ifs <;> decide
  hancCanc := by decide

/-- The headline is non-vacuous: it applies to the concrete `cModAddLayout2`. -/
example (s : State 27)
    (hCcadd : ∀ j, s (cModAddLayout2.Ccadd j) = false) (hancC : s cModAddLayout2.ancC = false)
    (hC1 : ∀ j, s (cModAddLayout2.C1 j) = false) (hC2 : ∀ j, s (cModAddLayout2.C2 j) = false)
    (hanc : s cModAddLayout2.anc = false)
    (hA1 : regValRange cModAddLayout2.A1 s 3 = 2 ^ 3 - 3)
    (hA2 : regValRange cModAddLayout2.A2 s 3 = 3)
    (hAop : regValRange cModAddLayout2.Aop s 3 = 2) (hB : regValRange cModAddLayout2.B s 3 = 2) :
    regValRange cModAddLayout2.B (denote (cModAdd cModAddLayout2) s) 3
      = if s cModAddLayout2.ctrl then (2 + 2) % 3 else 2 := by
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  exact cModAdd_correct cModAddLayout2 s hCcadd hancC hC1 hC2 hanc h2N hA1 hA2 hAop hB
    (by decide) (by decide)

/-- Concrete input state for `n = 3, N = 3`: operand `Aop = a` (wires `0,1,2`), accumulator `B = b`
(wires `3,4,5`), control wire `25 = ctrl`, `A1 = 5 = 2³ − 3` (wires `10,12`), `A2 = 3` (wires `17,18`),
all carries / ancillas `false`. Parameterised by the data bits of `a`, `b`, and the control bit. -/
def cModAddState2 (a0 a1 a2 b0 b1 b2 c : Bool) : State 27 := fun w =>
  if w = 0 then a0 else if w = 1 then a1 else if w = 2 then a2
  else if w = 3 then b0 else if w = 4 then b1 else if w = 5 then b2
  else if w = 10 then true else if w = 12 then true   -- A1 = 5 = 2³ − 3 (bits 0, 2)
  else if w = 17 then true else if w = 18 then true    -- A2 = 3 (bits 0, 1)
  else if w = 25 then c                                -- control
  else false

/-- The hypotheses of `cModAdd_correct` hold at `cModAddState2` (carries/ancillas clear, `A1 = 5`,
`A2 = 3`), for any data / control bits. The `regValRange` register-value preconditions are concrete
sums, discharged by `decide`. -/
private theorem cModAddState2_pre (a0 a1 a2 b0 b1 b2 c : Bool) :
    (∀ j, cModAddState2 a0 a1 a2 b0 b1 b2 c (cModAddLayout2.Ccadd j) = false)
      ∧ cModAddState2 a0 a1 a2 b0 b1 b2 c cModAddLayout2.ancC = false
      ∧ (∀ j, cModAddState2 a0 a1 a2 b0 b1 b2 c (cModAddLayout2.C1 j) = false)
      ∧ (∀ j, cModAddState2 a0 a1 a2 b0 b1 b2 c (cModAddLayout2.C2 j) = false)
      ∧ cModAddState2 a0 a1 a2 b0 b1 b2 c cModAddLayout2.anc = false
      ∧ regValRange cModAddLayout2.A1 (cModAddState2 a0 a1 a2 b0 b1 b2 c) 3 = 2 ^ 3 - 3
      ∧ regValRange cModAddLayout2.A2 (cModAddState2 a0 a1 a2 b0 b1 b2 c) 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; show cModAddState2 a0 a1 a2 b0 b1 b2 c (cModAddLayout2.Ccadd j) = false
    simp only [cModAddLayout2]; split_ifs <;> rfl
  · rfl
  · intro j; show cModAddState2 a0 a1 a2 b0 b1 b2 c (cModAddLayout2.C1 j) = false
    simp only [cModAddLayout2]; split_ifs <;> rfl
  · intro j; show cModAddState2 a0 a1 a2 b0 b1 b2 c (cModAddLayout2.C2 j) = false
    simp only [cModAddLayout2]; split_ifs <;> rfl
  · rfl
  · simp [regValRange, Finset.sum_range_succ, cModAddLayout2, cModAddState2]
  · simp [regValRange, Finset.sum_range_succ, cModAddLayout2, cModAddState2]

/-- **Concrete run, control set:** `a = 2, b = 2, N = 3, ctrl = true ↦ (2 + 2) mod 3 = 1`. The full
controlled modular adder on the explicit 27-wire input leaves register `B` holding `1`. -/
example : regValRange cModAddLayout2.B
    (denote (cModAdd cModAddLayout2) (cModAddState2 false true false false true false true)) 3 = 1 := by
  obtain ⟨hCcadd, hancC, hC1, hC2, hanc, hA1, hA2⟩ :=
    cModAddState2_pre false true false false true false true
  have hAop : regValRange cModAddLayout2.Aop
      (cModAddState2 false true false false true false true) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, cModAddLayout2, cModAddState2]
  have hB : regValRange cModAddLayout2.B
      (cModAddState2 false true false false true false true) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, cModAddLayout2, cModAddState2]
  have hctrl : (cModAddState2 false true false false true false true) cModAddLayout2.ctrl = true := by
    simp [cModAddLayout2, cModAddState2]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  rw [cModAdd_correct cModAddLayout2 (cModAddState2 false true false false true false true)
    hCcadd hancC hC1 hC2 hanc h2N hA1 hA2 hAop hB (by decide) (by decide), hctrl]
  decide

/-- **Concrete run, control clear:** same `a = 2, b = 2, N = 3` but `ctrl = false ↦ B stays b = 2`.
The controlled add is suppressed (so `B = b = 2 < N`), and the unconditional reduce is the identity on
the already-reduced residue `2`. -/
example : regValRange cModAddLayout2.B
    (denote (cModAdd cModAddLayout2) (cModAddState2 false true false false true false false)) 3 = 2 := by
  obtain ⟨hCcadd, hancC, hC1, hC2, hanc, hA1, hA2⟩ :=
    cModAddState2_pre false true false false true false false
  have hAop : regValRange cModAddLayout2.Aop
      (cModAddState2 false true false false true false false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, cModAddLayout2, cModAddState2]
  have hB : regValRange cModAddLayout2.B
      (cModAddState2 false true false false true false false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, cModAddLayout2, cModAddState2]
  have hctrl :
      (cModAddState2 false true false false true false false) cModAddLayout2.ctrl = false := by
    simp [cModAddLayout2, cModAddState2]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  rw [cModAdd_correct cModAddLayout2 (cModAddState2 false true false false true false false)
    hCcadd hancC hC1 hC2 hanc h2N hA1 hA2 hAop hB (by decide) (by decide), hctrl]
  decide

end Reversible
