import CsdLean4.Mathlib.QuantumInfo.Reversible.DoublingAssembly

/-!
# Per-opcode closure of the SLP → circuit fold: `sq` / `add` / `sub` (STEP 4)  (ECDLP Phase 2, S6.3e-2b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

STEP 3 (`DoublingAssembly.lean`) routed the genuine field-multiply (`mul`) and constant-multiply
(`nsmul`) gadgets through the verified SSA fold `compile_correct`, each landing on the
`(evalProgram inputs prog out).val` of the corresponding `ZMod p` field operation. STEP 4 (this file)
**closes the per-opcode infrastructure**: the remaining three field opcodes — `sq` (squaring),
`add`, `sub` — are routed through the *same* fold, so **all six `ECDLP.Instr` opcode kinds** now have a
`*_step_assembly_correct` theorem (mul / nsmul / mul from STEP 3, neg from STEP 1's
`worked_compile_correct`, and sq / add / sub here).

## What STEP 4 proves (this file)

* **`sq_step_assembly_correct`** (Part 2) — the faithful `sq` compilation. `compileInstr (.sq i)`
  emits `mulLoop`, but `mulLoop` needs its multiplier `X` and multiplicand `Y` on *disjoint* wires
  (`sq i` reading block `i` twice violates `hCtrlTouch`). So `sqStep` is `copyReg sqCopy ++ mulLoop
  wMulLoop`: copy the multiplicand block `Y` into the fresh multiplier block `X` (`copyReg`), then run
  the verified field-multiply. The one-step program `[Instr.sq 0]` over `ZMod 3` on input `2` lands the
  output block on `(evalProgram [2] [.sq 0] 1).val = (2·2).val = 1` through `compile_correct`. Reuses
  the STEP 3 `wMulLoop` / `Fin 135` multiply witness wholesale; only the small `copyReg` wrapper
  (`sqCopy`) is new.
* **`add_step_assembly_correct`** (Part 3) — the `add` fold. `addStep = copyReg addCopy ++ modAdd
  addOp` (= `compileInstr _ (.add 0 1)`). The one-step program `[Instr.add 0 1]` over `ZMod 3` on
  inputs `[2, 2]` lands the output block on `(evalProgram [2,2] [.add 0 1] 2).val = (2+2).val = 1`
  (via STEP 2's `addWrap_correct` + the `add_bridge`), with both source blocks preserved through the
  fold frame.
* **`sub_step_assembly_correct`** (Part 4) — the `sub` fold. `subStep = copyReg subCopy ++ modSub
  subOp`. The one-step program `[Instr.sub 0 1]` over `ZMod 3` on inputs `[1, 2]` lands the output
  block on `(evalProgram [1,2] [.sub 0 1] 2).val = (1-2).val = 2` (exercising the truncation-safe
  wraparound branch `(a + N − b) % N`, via `subWrap_correct` + `sub_bridge`).
* **`all_six_opcodes_through_fold`** (Part 5) — the closure headline: a conjunction recording that
  every one of the six `ECDLP.Instr` opcode kinds now has a `*_step_assembly_correct` landing on the
  `evalProgram`-`.val` field value through `compile_correct`.

## Carve line

STEP 4 closes the **per-opcode folds** (all six opcodes proven field-correct as one-step programs
through `compile_correct`). The full multi-step `doublingProgram` layout assembly (≈1200 wires, the
17-step heterogeneous `hstep`) remains **named mechanical residue** (the STEP 2/3 carve line, unchanged),
and secp256k1 width remains gated on the `regValRange`-of-binary-digits extraction helper. The orthogonal
carry-clean-adder qubit residue is unchanged.
-/

namespace Reversible

open ECDLP

/-! ## Part 0 — the two missing per-gadget register-block frame lemmas

`compile_correct`'s `hstep` frame obligation needs `modAdd` / `modSub` to preserve every *other*
register block. STEP 1/2 named the wire-level external frames (`modAdd_preserves_external`,
`modSub_preserves_external`); these are the register-block forms (fold over the low `q` bits). -/

variable {m n : ℕ}

/-- **`modAdd` register-block frame.** A register `f` whose every wire is disjoint from every
`modAdd`-touched family survives `modAdd L`. -/
theorem modAdd_preserves_block (L : ModAddLayout m n) (s : State m) (f : ℕ → Fin m) (q : ℕ)
    (hAop : ∀ i j, f i ≠ L.Aop j) (hB : ∀ i j, f i ≠ L.B j) (hCadd : ∀ i j, f i ≠ L.Cadd j)
    (hA1 : ∀ i j, f i ≠ L.A1 j) (hC1 : ∀ i j, f i ≠ L.C1 j) (hA2 : ∀ i j, f i ≠ L.A2 j)
    (hC2 : ∀ i j, f i ≠ L.C2 j) (hanc : ∀ i, f i ≠ L.anc) :
    regValRange f (denote (modAdd L) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (modAdd L) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [modAdd_preserves_external L s (f i) (hAop i) (hB i) (hCadd i) (hA1 i) (hC1 i) (hA2 i)
    (hC2 i) (hanc i)]

/-- **`modSub` register-block frame.** A register `f` whose every wire is disjoint from every
`modSub`-touched family survives `modSub L`. -/
theorem modSub_preserves_block (L : ModSubLayout m n) (s : State m) (f : ℕ → Fin m) (q : ℕ)
    (hB : ∀ i j, f i ≠ L.B j) (hSub : ∀ i j, f i ≠ L.Sub j) (hBor : ∀ i j, f i ≠ L.Bor j)
    (hNreg : ∀ i j, f i ≠ L.Nreg j) (hC : ∀ i j, f i ≠ L.C j) (hanc : ∀ i, f i ≠ L.anc) :
    regValRange f (denote (modSub L) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (modSub L) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [modSub_preserves_external L s (f i) (hB i) (hSub i) (hBor i) (hNreg i) (hC i) (hanc i)]

/-! ## Part 1 — the `sq` copy-wrapper layout

`sqCopy` is a `copyReg` layout on `Fin 135` whose source `B` is the STEP 3 multiplicand register
`wMulLoop.Y` (= wires `{3,4,5}`) and whose destination `Aop` is the multiplier register `wMulLoop.X`
(= wires `{6,7,8}`). The `copyReg` step copies `Y` into `X` (`X` initially `0`), so the subsequent
`mulLoop wMulLoop` computes `X · Y = a · a`. The filler `ModAddLayout` registers (`A1, A2, Cadd, …`,
never touched by `copyReg`) sit at wires `[9, 28)`; they overlap `wMulLoop`'s bank wires harmlessly
because `copyReg sqCopy` only touches `{3,…,8}` and `modDouble sqCopy` (the part that would use them) is
never run. -/

/-- The `sq` copy layout on `Fin 135`: `B = wMulLoop.Y` (`{3,4,5}`), `Aop = wMulLoop.X` (`{6,7,8}`),
filler registers in `[9, 28)`. -/
def sqCopy : ModDoubleLayout 135 3 where
  addLayout :=
    { Aop i := ⟨6 + min i 2, by omega⟩
      B i := ⟨3 + min i 2, by omega⟩
      Cadd i := ⟨9 + min i 3, by omega⟩
      A1 i := ⟨13 + min i 2, by omega⟩
      C1 i := ⟨16 + min i 3, by omega⟩
      A2 i := ⟨20 + min i 2, by omega⟩
      C2 i := ⟨23 + min i 3, by omega⟩
      anc := ⟨27, by omega⟩
      hAopB i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hCaddinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hC1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hC2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hflagA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflagB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflagC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflaganc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hC2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hC2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega }

/-- `sqCopy.Aop` is definitionally `wMulLoop.X`. -/
theorem sqCopy_Aop_eq : sqCopy.Aop = wMulLoop.X := rfl

/-- `sqCopy.B` is definitionally `wMulLoop.Y`. -/
theorem sqCopy_B_eq : sqCopy.B = wMulLoop.Y := rfl

/-! ## Part 2 — the `sq` opcode through `compile_correct` -/

/-- The register-block layout for the `sq` step: block `0` = the input/multiplicand `Y`, block `1` =
the accumulator/output `B`. (The multiplier `X` is internal scratch, not a program register.) -/
def sqReg : RegBlockLayout 135 3 where
  block r i := if r = 0 then wMulLoop.Y i else wMulLoop.B i

/-- The compiled `sq` step circuit: copy `Y` into `X`, then the field-multiply loop. -/
def sqStep : ℕ → Circuit 135 := fun _ => copyReg sqCopy ++ mulLoop wMulLoop

/-- The `sq` input state on `Fin 135`: `Y = 2` (wires `{3,4,5}`), `X = 0` (wires `{6,7,8}`), `B = 0`,
every bank's presets `A1 = 5`, `A2 = 3` set, all scratch / carries / ancilla clean. (Reuses the STEP 3
multiply witness state `wState` with the multiplier bits all `false`.) -/
def sqState : State 135 := wState false true false false false false

/-- Step `t`'s self-precondition: the STEP 3 `mulPre` (clean accumulator / carries / presets) plus the
multiplier register `X` clean (`sqCopy.Aop` initially `0`, required by `copyReg_correct_operand`). -/
def sqPre : ℕ → State 135 → Prop := fun t s =>
  mulPre t s ∧ (∀ i, i < 3 → s (sqCopy.Aop i) = false)

/-- The `ZMod 3` register file of `[.sq 0]` on input `2`: `[2, 2·2]` (i.e. `[2, 1]`). -/
theorem sqRun :
    runProgram [(2 : ZMod 3)] [Instr.sq 0] = [(2 : ZMod 3), (2 : ZMod 3) * (2 : ZMod 3)] := by
  simp only [runProgram, evalInstr, regGet, List.cons_append, List.nil_append]

set_option maxRecDepth 4000 in
/-- The `sq` self-preconditions hold at `sqState` (the `mulPre` part replicates the STEP 3 discharge;
the `X`-clean part is `decide` on the all-`false` multiplier bits). -/
theorem sqPre_at_state : sqPre 0 sqState := by
  refine ⟨⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j i hj hi; interval_cases j <;> interval_cases i <;> decide
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [sqState, wMulLoop, wBank, wDbl]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [sqState, wMulLoop, wBank, wDbl]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [sqState, wMulLoop, wBank, wDbl]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;> (dsimp only [sqState, wMulLoop, wBank, wDbl]; decide)
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [sqState, wMulLoop, wBank, wAdd]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;> (dsimp only [sqState, wMulLoop, wBank, wAdd]; decide)
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [sqState, wMulLoop, wBank, wAdd]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [sqState, wMulLoop, wBank, wAdd]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;> (dsimp only [sqState, wMulLoop, wBank, wAdd]; decide)
  · intro j hj; interval_cases j <;> decide
  · intro j hj; interval_cases j <;> decide
  · intro j hj; interval_cases j <;> decide
  · intro j hj; interval_cases j <;> decide
  · intro i hi; interval_cases i <;> decide

/-- A bank / accumulator wire of `wMulLoop` (val `< 3` or `≥ 9`) survives `copyReg sqCopy` (which only
touches `{3,…,8}`). -/
theorem copyReg_sqCopy_pres (s : State 135) (w : Fin 135) (hw : w.val < 3 ∨ 9 ≤ w.val) :
    denote (copyReg sqCopy) s w = s w :=
  copyReg_preserves (L := sqCopy) s w
    (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [ModDoubleLayout.B, sqCopy]; omega)
    (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [ModDoubleLayout.Aop, sqCopy]; omega)

/-- Register-block form of `copyReg_sqCopy_pres`. -/
theorem copyReg_sqCopy_pres_reg (s : State 135) (f : ℕ → Fin 135) (q : ℕ)
    (hf : ∀ i, (f i).val < 3 ∨ 9 ≤ (f i).val) :
    regValRange f (denote (copyReg sqCopy) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (copyReg sqCopy) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [copyReg_sqCopy_pres s (f i) (hf i)]

/-- `mulPre` survives `copyReg sqCopy`: every `mulPre` wire is the accumulator `B` (val `< 3`) or a bank
wire (val `≥ 9`), disjoint from the copy's `{3,…,8}`. -/
theorem mulPre_after_sqCopy {s : State 135} (h : mulPre 0 s) :
    mulPre 0 (denote (copyReg sqCopy) s) := by
  obtain ⟨hB0, hAop, hCadd, hdC1, hdC2, hdanc, hCcadd, hancC, hC1, hC2, hanc,
    hA1dbl, hA2dbl, hA1add, hA2add⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [copyReg_sqCopy_pres_reg s wMulLoop.B 3
      (fun i => Or.inl (by dsimp only [MulLoopLayout.B, wMulLoop, wBank, wAdd,
        HornerStepLayout.B]; omega))]
    exact hB0
  · intro j i hj hi
    rw [copyReg_sqCopy_pres s _
      (Or.inr (by dsimp only [wMulLoop, wBank, wDbl, ModDoubleLayout.Aop]; omega))]
    exact hAop j i hj hi
  · intro j i hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wDbl]; omega))]
    exact hCadd j i hj
  · intro j i hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wDbl]; omega))]
    exact hdC1 j i hj
  · intro j i hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wDbl]; omega))]
    exact hdC2 j i hj
  · intro j hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wDbl]; omega))]
    exact hdanc j hj
  · intro j i hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hCcadd j i hj
  · intro j hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hancC j hj
  · intro j i hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hC1 j i hj
  · intro j i hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hC2 j i hj
  · intro j hj
    rw [copyReg_sqCopy_pres s _ (Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hanc j hj
  · intro j hj
    rw [copyReg_sqCopy_pres_reg s _ 3
      (fun i => Or.inr (by dsimp only [wMulLoop, wBank, wDbl]; omega))]
    exact hA1dbl j hj
  · intro j hj
    rw [copyReg_sqCopy_pres_reg s _ 3
      (fun i => Or.inr (by dsimp only [wMulLoop, wBank, wDbl]; omega))]
    exact hA2dbl j hj
  · intro j hj
    rw [copyReg_sqCopy_pres_reg s _ 3
      (fun i => Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hA1add j hj
  · intro j hj
    rw [copyReg_sqCopy_pres_reg s _ 3
      (fun i => Or.inr (by dsimp only [wMulLoop, wBank, wAdd]; omega))]
    exact hA2add j hj

set_option maxRecDepth 4000 in
/-- **The `sq` opcode assembled through `compile_correct`.** The compiled one-step circuit for
`[.sq 0]` over `ZMod 3`, on `sqState` (input `2`), leaves the output block (register `1`) holding
`(evalProgram [2] [.sq 0] 1).val` — the bit circuit (copy `Y` into `X`, then the field-multiply loop)
computes `a · a` mod `3`, value-correct, via the verified SSA fold. -/
theorem sq_step_assembly_correct :
    sqReg.valOf (denote (compile sqStep [Instr.sq 0].length) sqState) 1
      = (evalProgram [(2 : ZMod 3)] [Instr.sq 0] 1).val := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  refine compile_correct sqReg [(2 : ZMod 3)] [Instr.sq 0] sqStep sqPre sqState ?_ ?_ ?_ ?_ 1
    (by decide)
  · -- hbase: input block holds its value
    intro r hr
    have : r = 0 := by simpa using hr
    subst this
    rw [sqRun]
    show regValRange wMulLoop.Y sqState 3 = ZMod.val (2 : ZMod 3)
    decide
  · -- hpre0
    intro t ht
    have : t = 0 := by simpa using ht
    subst this; exact sqPre_at_state
  · -- hpre_frame: vacuous (one-step)
    intro t t' ht't ht s hsp
    have : t < 1 := by simpa using ht
    omega
  · -- hstep
    intro t ht s hHolds hsp r hr
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    obtain ⟨hmul, hX0⟩ := hsp
    -- a = Y value from block 0
    have hYval : regValRange wMulLoop.Y s 3 = ZMod.val (2 : ZMod 3) := by
      have h0 := hHolds 0 (by simp); rw [sqRun] at h0; simpa using h0
    -- the post-copy state
    set s' := denote (copyReg sqCopy) s with hs'
    have hmul' : mulPre 0 s' := mulPre_after_sqCopy hmul
    obtain ⟨hB0', hAop', hCadd', hdC1', hdC2', hdanc', hCcadd', hancC', hC1', hC2', hanc',
      hA1dbl', hA2dbl', hA1add', hA2add'⟩ := hmul'
    -- X = a at s' (copyReg_correct_operand: Aop ← B)
    have hXa : regValRange wMulLoop.X s' 3 = ZMod.val (2 : ZMod 3) := by
      rw [hs', ← sqCopy_Aop_eq, copyReg_correct_operand sqCopy s hX0, sqCopy_B_eq, hYval]
    -- Y = a at s' (copyReg_correct_B: B preserved)
    have hYval' : regValRange wMulLoop.Y s' 3 = ZMod.val (2 : ZMod 3) := by
      rw [hs', ← sqCopy_B_eq, copyReg_correct_B sqCopy s hX0, sqCopy_B_eq, hYval]
    have hYN : ZMod.val (2 : ZMod 3) < 3 := by decide
    -- output value via mulLoop_correct at s'
    have hBval := mulLoop_correct wMulLoop s' (N := 3) (Yval := ZMod.val (2 : ZMod 3))
      (by decide) (by decide) hYN hB0' hYval' hAop' hCadd' hdC1' hdC2' hdanc' hCcadd' hancC'
      hC1' hC2' hanc' hA1dbl' hA2dbl' hA1add' hA2add'
    -- multiplicand preserved through mulLoop at s'
    have hYpres := (mulLoop_invariant wMulLoop s' (N := 3) (Yval := ZMod.val (2 : ZMod 3))
      (by decide) (by decide) hYN hB0' hYval' hAop' hCadd' hdC1' hdC2' hdanc' hCcadd' hancC'
      hC1' hC2' hanc' hA1dbl' hA2dbl' hA1add' hA2add' 3 (le_refl 3)).2
    rw [← mulLoop_eq_upto] at hYpres
    -- denote of the whole step
    have hden : denote (sqStep 0) s = denote (mulLoop wMulLoop) s' := by
      rw [sqStep, denote_append, ← hs']
    show sqReg.valOf (denote (sqStep 0) s) r = _
    have hr2 : r < 2 := by simpa using hr
    interval_cases r
    · -- r = 0: multiplicand preserved
      rw [sqRun]
      show regValRange wMulLoop.Y (denote (sqStep 0) s) 3 = ZMod.val (2 : ZMod 3)
      rw [hden, hYpres]
    · -- r = 1: output value = a·a mod 3
      rw [sqRun]
      show regValRange wMulLoop.B (denote (sqStep 0) s) 3 = ((2 : ZMod 3) * (2 : ZMod 3)).val
      rw [hden, hBval, hXa, mul_bridge]

/-- The `sq`-step output value is `1` (`= (2·2) mod 3`). -/
theorem sq_step_value :
    sqReg.valOf (denote (compile sqStep [Instr.sq 0].length) sqState) 1 = 1 := by
  rw [sq_step_assembly_correct]
  show (evalProgram [(2 : ZMod 3)] [Instr.sq 0] 1).val = 1
  rw [evalProgram, sqRun]; decide

/-! ## Part 3 — the shared `copyReg` layout + the `add` opcode through `compile_correct`

The `add` / `sub` folds run on a fresh ambient `Fin 60` at `n = 3`, `N = 3`. The `copyReg`-wrapper
layout `copyLayout bbase` copies source block `B = {bbase, bbase+1, bbase+2}` into the output block
`Aop = {6,7,8}`; `addCopy := copyLayout 3` (source `b` = block `1`), `subCopy := copyLayout 0` (source
`a` = block `0`). Its filler `ModAddLayout` registers (never touched by `copyReg`) sit at `[30, 49)`. -/

/-- The shared `copyReg` layout on `Fin 60`: source `B = {bbase,…}`, destination `Aop = {6,7,8}`,
filler registers in `[30, 49)`. (`bbase + 3 ≤ 6` keeps `B` disjoint from `Aop`.) -/
def copyLayout (bbase : ℕ) (hb : bbase + 3 ≤ 6) : ModDoubleLayout 60 3 where
  addLayout :=
    { Aop i := ⟨6 + min i 2, by omega⟩
      B i := ⟨bbase + min i 2, by omega⟩
      Cadd i := ⟨30 + min i 3, by omega⟩
      A1 i := ⟨34 + min i 2, by omega⟩
      C1 i := ⟨37 + min i 3, by omega⟩
      A2 i := ⟨41 + min i 2, by omega⟩
      C2 i := ⟨44 + min i 3, by omega⟩
      anc := ⟨48, by omega⟩
      hAopB i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hCaddinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hC1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hBA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hBC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hC2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
      hflagA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflagB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflagC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hflaganc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hA2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hC2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hC2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hancC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hCaddanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
      hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega }

/-- The in-place modular adder layout on `Fin 60`: addend `Aop = {0,1,2}`, accumulator/output
`B = {6,7,8}`, reduce data in `[9, 28)`. -/
def addOp : ModAddLayout 60 3 where
  Aop i := ⟨0 + min i 2, by omega⟩
  B i := ⟨6 + min i 2, by omega⟩
  Cadd i := ⟨9 + min i 3, by omega⟩
  A1 i := ⟨13 + min i 2, by omega⟩
  C1 i := ⟨16 + min i 3, by omega⟩
  A2 i := ⟨20 + min i 2, by omega⟩
  C2 i := ⟨23 + min i 3, by omega⟩
  anc := ⟨27, by omega⟩
  hAopB i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBCadd i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hCaddinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA1C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hC1inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2C2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hC2inj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hflagA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflagB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflagC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflaganc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancA2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancC2 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hA2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hC2A1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hC2C1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancA1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancC1 j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCaddA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCaddC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCaddA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCaddC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCaddanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopA1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopC1 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopA2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopC2 i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAopanc i := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega

/-- The `add` copy layout (source `b` = block `1`, wires `{3,4,5}`). -/
def addCopy : ModDoubleLayout 60 3 := copyLayout 3 (by norm_num)

/-- The register-block layout for the `add` step: block `0` = addend `a` (`addOp.Aop`), block `1` =
the `b` source (`addCopy.B`), block `2` = the output (`addOp.B`). -/
def addReg : RegBlockLayout 60 3 where
  block r i := if r = 0 then addOp.Aop i else if r = 1 then addCopy.B i else addOp.B i

/-- The compiled `add` step circuit: copy `b` into the output block, then the in-place modular add. -/
def addStep : ℕ → Circuit 60 := fun _ => copyReg addCopy ++ modAdd addOp

/-- Step `t`'s self-precondition for `add`: fresh-zero output block (`addCopy.Aop = addOp.B`), reduce
presets `A1 = 2³ − 3 = 5`, `A2 = 3`, clean carries / ancilla. -/
def addPre : ℕ → State 60 → Prop := fun _ s =>
  (∀ i, i < 3 → s (addCopy.Aop i) = false)
    ∧ regValRange addOp.A1 s 3 = 2 ^ 3 - 3
    ∧ regValRange addOp.A2 s 3 = 3
    ∧ (∀ j, s (addOp.Cadd j) = false)
    ∧ (∀ j, s (addOp.C1 j) = false)
    ∧ (∀ j, s (addOp.C2 j) = false)
    ∧ s addOp.anc = false

/-- The `add` input state on `Fin 60`: block `0` (`a`) `= 2` (wire `1`), block `1` (`b`) `= 2`
(wire `4`), `addOp.A1 = 5` (wires `13,15`), `addOp.A2 = 3` (wires `20,21`); everything else `false`. -/
def addState : State 60 := fun w =>
  decide (w.val = 1 ∨ w.val = 4 ∨ w.val = 13 ∨ w.val = 15 ∨ w.val = 20 ∨ w.val = 21)

/-- `addState` is `false` off the six set bits. -/
theorem addState_false {w : Fin 60} (h1 : w.val ≠ 1) (h4 : w.val ≠ 4) (h13 : w.val ≠ 13)
    (h15 : w.val ≠ 15) (h20 : w.val ≠ 20) (h21 : w.val ≠ 21) : addState w = false := by
  simp only [addState, decide_eq_false_iff_not]; omega

/-- The `ZMod 3` register file of `[.add 0 1]` on inputs `[2, 2]`: `[2, 2, 2+2]` (i.e. `[2, 2, 1]`). -/
theorem addRun :
    runProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.add 0 1]
      = [(2 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3) + (2 : ZMod 3)] := by
  simp only [runProgram, evalInstr, regGet, List.cons_append, List.nil_append]

/-- The `add` self-preconditions hold at `addState`. -/
theorem addPre_at_state : addPre 0 addState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> decide
  · decide
  · decide
  · intro j; refine addState_false ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp only [addOp]; omega)
  · intro j; refine addState_false ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp only [addOp]; omega)
  · intro j; refine addState_false ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp only [addOp]; omega)
  · refine addState_false ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp only [addOp]; omega)

/-- **The `add` opcode assembled through `compile_correct`.** The compiled one-step circuit for
`[.add 0 1]` over `ZMod 3`, on `addState` (inputs `2`, `2`), leaves the output block (register `2`)
holding `(evalProgram [2,2] [.add 0 1] 2).val` — the bit circuit (copy `b`, then the in-place modular
add) computes `(a + b)` mod `3`, value-correct, via the verified SSA fold. -/
theorem add_step_assembly_correct :
    addReg.valOf (denote (compile addStep [Instr.add 0 1].length) addState) 2
      = (evalProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.add 0 1] 2).val := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  refine compile_correct addReg [(2 : ZMod 3), (2 : ZMod 3)] [Instr.add 0 1] addStep addPre
    addState ?_ ?_ ?_ ?_ 2 (by decide)
  · -- hbase
    intro r hr
    have hr2 : r < 2 := by simpa using hr
    rw [addRun]
    interval_cases r
    · show regValRange addOp.Aop addState 3 = ZMod.val (2 : ZMod 3); decide
    · show regValRange addCopy.B addState 3 = ZMod.val (2 : ZMod 3); decide
  · -- hpre0
    intro t ht
    have : t = 0 := by simpa using ht
    subst this; exact addPre_at_state
  · -- hpre_frame: vacuous
    intro t t' ht't ht s hsp
    have : t < 1 := by simpa using ht
    omega
  · -- hstep
    intro t ht s hHolds hsp r hr
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    obtain ⟨hOut0, hA1, hA2, hCadd, hC1, hC2, hanc⟩ := hsp
    have hAval : regValRange addOp.Aop s 3 = ZMod.val (2 : ZMod 3) := by
      have h0 := hHolds 0 (by simp); rw [addRun] at h0; simpa using h0
    have hBval : regValRange addCopy.B s 3 = ZMod.val (2 : ZMod 3) := by
      have h1 := hHolds 1 (by simp); rw [addRun] at h1; simpa using h1
    -- output value via addWrap_correct
    have hout := addWrap_correct addCopy addOp s (N := 3)
      (a := ZMod.val (2 : ZMod 3)) (b := ZMod.val (2 : ZMod 3))
      (by decide) rfl hOut0 hBval (by decide) hAval (by decide) hA1 hA2 hCadd hC1 hC2 hanc
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)
    -- frame: block 0 (a) and block 1 (b) preserved through the step
    set s1 := denote (copyReg addCopy) s with hs1
    have hCadd_s1 : ∀ j, s1 (addOp.Cadd j) = false := fun j => by
      rw [hs1, copyReg_preserves (L := addCopy) s (addOp.Cadd j)
        (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)]
      exact hCadd j
    have hA_s1 : regValRange addOp.Aop s1 3 = ZMod.val (2 : ZMod 3) := by
      rw [hs1, copyReg_preserves_reg addCopy s addOp.Aop 3
        (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.Aop]; omega)]
      exact hAval
    have hA0 : regValRange addOp.Aop (denote (modAdd addOp) s1) 3 = ZMod.val (2 : ZMod 3) :=
      modAdd_preserves_operand addOp s1 hCadd_s1 hA_s1
    have hB_s1 : regValRange addCopy.B s1 3 = ZMod.val (2 : ZMod 3) := by
      rw [hs1, copyReg_correct_B addCopy s hOut0]; exact hBval
    have hB_final : regValRange addCopy.B (denote (modAdd addOp) s1) 3 = ZMod.val (2 : ZMod 3) := by
      rw [modAdd_preserves_block addOp s1 addCopy.B 3
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i => by rw [ne_eq, Fin.ext_iff]; dsimp only [addOp, addCopy, copyLayout, ModDoubleLayout.B]; omega)]
      exact hB_s1
    have hden : denote (addStep 0) s = denote (modAdd addOp) s1 := by
      rw [addStep, denote_append, ← hs1]
    show addReg.valOf (denote (addStep 0) s) r = _
    have hr3 : r < 3 := by simpa using hr
    interval_cases r
    · rw [addRun]
      show regValRange addOp.Aop (denote (addStep 0) s) 3 = ZMod.val (2 : ZMod 3)
      rw [hden]; exact hA0
    · rw [addRun]
      show regValRange addCopy.B (denote (addStep 0) s) 3 = ZMod.val (2 : ZMod 3)
      rw [hden]; exact hB_final
    · rw [addRun]
      show regValRange addOp.B (denote (addStep 0) s) 3 = ((2 : ZMod 3) + (2 : ZMod 3)).val
      rw [show denote (addStep 0) s = denote (copyReg addCopy ++ modAdd addOp) s from rfl, hout,
        add_bridge]

/-- The `add`-step output value is `1` (`= (2+2) mod 3`). -/
theorem add_step_value :
    addReg.valOf (denote (compile addStep [Instr.add 0 1].length) addState) 2 = 1 := by
  rw [add_step_assembly_correct]
  show (evalProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.add 0 1] 2).val = 1
  rw [evalProgram, addRun]; decide

/-! ## Part 4 — the `sub` opcode through `compile_correct` -/

/-- The in-place modular subtractor layout on `Fin 60`: minuend/output `B = {6,7,8}`, subtrahend
`Sub = {3,4,5}`, fix data in `[9, 21)`. -/
def subOp : ModSubLayout 60 3 where
  B i := ⟨6 + min i 2, by omega⟩
  Sub i := ⟨3 + min i 2, by omega⟩
  Bor i := ⟨9 + min i 3, by omega⟩
  Nreg i := ⟨13 + min i 2, by omega⟩
  C i := ⟨16 + min i 3, by omega⟩
  anc := ⟨20, by omega⟩
  hBSub i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBBor i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hSubBor i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hSubinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBorinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hBNreg i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hBC i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hNregC i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hNreginj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hCinj i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hflagNreg j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflagB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflagC j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hflaganc := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancNreg j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancB j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancC j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hNregSub i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hNregBor i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCSub i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCBor i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancSub j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hancBor j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hSubNreg i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hSubC i j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hSubanc j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega

/-- The `sub` copy layout (minuend `a` = block `0`, wires `{0,1,2}`). -/
def subCopy : ModDoubleLayout 60 3 := copyLayout 0 (by norm_num)

/-- The register-block layout for the `sub` step: block `0` = minuend `a` (`subCopy.B`), block `1` =
subtrahend `b` (`subOp.Sub`), block `2` = output (`subOp.B`). -/
def subReg : RegBlockLayout 60 3 where
  block r i := if r = 0 then subCopy.B i else if r = 1 then subOp.Sub i else subOp.B i

/-- The compiled `sub` step circuit: copy the minuend into the output block, then the in-place
modular subtract. -/
def subStep : ℕ → Circuit 60 := fun _ => copyReg subCopy ++ modSub subOp

/-- Step `t`'s self-precondition for `sub`: fresh-zero output block (`subCopy.Aop = subOp.B`), fix
preset `Nreg = 3`, clean borrow / fix-carry / ancilla. -/
def subPre : ℕ → State 60 → Prop := fun _ s =>
  (∀ i, i < 3 → s (subCopy.Aop i) = false)
    ∧ regValRange subOp.Nreg s 3 = 3
    ∧ (∀ j, s (subOp.Bor j) = false)
    ∧ (∀ j, s (subOp.C j) = false)
    ∧ s subOp.anc = false

/-- The `sub` input state on `Fin 60`: block `0` (`a`) `= 1` (wire `0`), block `1` (`b`) `= 2`
(wire `4`), `subOp.Nreg = 3` (wires `13,14`); everything else `false`. -/
def subState : State 60 := fun w =>
  decide (w.val = 0 ∨ w.val = 4 ∨ w.val = 13 ∨ w.val = 14)

/-- `subState` is `false` off the four set bits. -/
theorem subState_false {w : Fin 60} (h0 : w.val ≠ 0) (h4 : w.val ≠ 4) (h13 : w.val ≠ 13)
    (h14 : w.val ≠ 14) : subState w = false := by
  simp only [subState, decide_eq_false_iff_not]; omega

/-- The `ZMod 3` register file of `[.sub 0 1]` on inputs `[1, 2]`: `[1, 2, 1-2]` (i.e. `[1, 2, 2]`). -/
theorem subRun :
    runProgram [(1 : ZMod 3), (2 : ZMod 3)] [Instr.sub 0 1]
      = [(1 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3) - (2 : ZMod 3)] := by
  simp only [runProgram, evalInstr, regGet, List.cons_append, List.nil_append]

/-- The `sub` self-preconditions hold at `subState`. -/
theorem subPre_at_state : subPre 0 subState := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> decide
  · decide
  · intro j; refine subState_false ?_ ?_ ?_ ?_ <;> (dsimp only [subOp]; omega)
  · intro j; refine subState_false ?_ ?_ ?_ ?_ <;> (dsimp only [subOp]; omega)
  · refine subState_false ?_ ?_ ?_ ?_ <;> (dsimp only [subOp]; omega)

/-- **The `sub` opcode assembled through `compile_correct`.** The compiled one-step circuit for
`[.sub 0 1]` over `ZMod 3`, on `subState` (inputs `1`, `2`), leaves the output block (register `2`)
holding `(evalProgram [1,2] [.sub 0 1] 2).val` — the bit circuit (copy the minuend, then the in-place
modular subtract) computes `(a − b)` mod `3` in the truncation-safe form `(a + N − b) % N`,
value-correct, via the verified SSA fold (this input exercises the wraparound branch `a < b`). -/
theorem sub_step_assembly_correct :
    subReg.valOf (denote (compile subStep [Instr.sub 0 1].length) subState) 2
      = (evalProgram [(1 : ZMod 3), (2 : ZMod 3)] [Instr.sub 0 1] 2).val := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  refine compile_correct subReg [(1 : ZMod 3), (2 : ZMod 3)] [Instr.sub 0 1] subStep subPre
    subState ?_ ?_ ?_ ?_ 2 (by decide)
  · -- hbase
    intro r hr
    have hr2 : r < 2 := by simpa using hr
    rw [subRun]
    interval_cases r
    · show regValRange subCopy.B subState 3 = ZMod.val (1 : ZMod 3); decide
    · show regValRange subOp.Sub subState 3 = ZMod.val (2 : ZMod 3); decide
  · -- hpre0
    intro t ht
    have : t = 0 := by simpa using ht
    subst this; exact subPre_at_state
  · -- hpre_frame: vacuous
    intro t t' ht't ht s hsp
    have : t < 1 := by simpa using ht
    omega
  · -- hstep
    intro t ht s hHolds hsp r hr
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    obtain ⟨hOut0, hNreg, hBor, hC, hanc⟩ := hsp
    have ha : regValRange subCopy.B s 3 = ZMod.val (1 : ZMod 3) := by
      have h0 := hHolds 0 (by simp); rw [subRun] at h0; simpa using h0
    have hb : regValRange subOp.Sub s 3 = ZMod.val (2 : ZMod 3) := by
      have h1 := hHolds 1 (by simp); rw [subRun] at h1; simpa using h1
    -- output value via subWrap_correct
    have hout := subWrap_correct subCopy subOp s (N := 3)
      (a := ZMod.val (1 : ZMod 3)) (b := ZMod.val (2 : ZMod 3))
      (by decide) rfl hOut0 ha (by decide) hb (by decide) hNreg hBor hC hanc
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)
      (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
      (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)
    -- frame: block 0 (minuend a) and block 1 (subtrahend b) preserved through the step
    set s1 := denote (copyReg subCopy) s with hs1
    have hBor_s1 : ∀ j, s1 (subOp.Bor j) = false := fun j => by
      rw [hs1, copyReg_preserves (L := subCopy) s (subOp.Bor j)
        (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)]
      exact hBor j
    have hB_s1 : regValRange subCopy.B s1 3 = ZMod.val (1 : ZMod 3) := by
      rw [hs1, copyReg_correct_B subCopy s hOut0]; exact ha
    have hB0_final : regValRange subCopy.B (denote (modSub subOp) s1) 3 = ZMod.val (1 : ZMod 3) := by
      rw [modSub_preserves_block subOp s1 subCopy.B 3
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i j => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)]
      exact hB_s1
    have hSub_s1 : regValRange subOp.Sub s1 3 = ZMod.val (2 : ZMod 3) := by
      rw [hs1, copyReg_preserves_reg subCopy s subOp.Sub 3
        (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.B]; omega)
        (fun i k => by rw [ne_eq, Fin.ext_iff]; dsimp only [subOp, subCopy, copyLayout, ModDoubleLayout.Aop]; omega)]
      exact hb
    have hSub_final : regValRange subOp.Sub (denote (modSub subOp) s1) 3 = ZMod.val (2 : ZMod 3) :=
      modSub_preserves_subtrahend subOp s1 hBor_s1 hSub_s1
    have hden : denote (subStep 0) s = denote (modSub subOp) s1 := by
      rw [subStep, denote_append, ← hs1]
    show subReg.valOf (denote (subStep 0) s) r = _
    have hr3 : r < 3 := by simpa using hr
    interval_cases r
    · rw [subRun]
      show regValRange subCopy.B (denote (subStep 0) s) 3 = ZMod.val (1 : ZMod 3)
      rw [hden]; exact hB0_final
    · rw [subRun]
      show regValRange subOp.Sub (denote (subStep 0) s) 3 = ZMod.val (2 : ZMod 3)
      rw [hden]; exact hSub_final
    · rw [subRun]
      show regValRange subOp.B (denote (subStep 0) s) 3 = ((1 : ZMod 3) - (2 : ZMod 3)).val
      rw [show denote (subStep 0) s = denote (copyReg subCopy ++ modSub subOp) s from rfl, hout,
        sub_bridge]

/-- The `sub`-step output value is `2` (`= (1 − 2) mod 3`, the wraparound branch). -/
theorem sub_step_value :
    subReg.valOf (denote (compile subStep [Instr.sub 0 1].length) subState) 2 = 2 := by
  rw [sub_step_assembly_correct]
  show (evalProgram [(1 : ZMod 3), (2 : ZMod 3)] [Instr.sub 0 1] 2).val = 2
  rw [evalProgram, subRun]; decide

/-! ## Part 5 — the per-opcode closure headline

All six `ECDLP.Instr` opcode kinds now route through the verified SSA fold `compile_correct`, each
landing on the `(evalProgram inputs prog out).val` field value of the corresponding `ZMod p` operation:
`neg` (STEP 1, `worked_compile_correct`, a 2-step double-negation), `nsmul` / `mul` (STEP 3), and
`sq` / `add` / `sub` (STEP 4, this file). The per-opcode field-correctness infrastructure of the
SLP → circuit router is closed; the full multi-step `doublingProgram` assembly remains named mechanical
residue (the heterogeneous `hpre_frame` inductive step of the fold is exercised only there, not by these
one-step programs). -/

/-- **Per-opcode closure.** Every one of the six opcode kinds has a `*_step_assembly_correct`-style
theorem landing the output block on the `evalProgram`-`.val` field value through the verified SSA fold
`compile_correct`. This conjunction genuinely bundles all six: `neg` (`worked_compile_correct`, STEP 1,
a 2-step `[.neg 0, .neg 1]` double-negation), `mul` / `nsmul` (STEP 3), and `sq` / `add` / `sub`
(STEP 4, this file). The name and type now agree (six conjuncts, six witnesses). -/
theorem all_six_opcodes_through_fold :
    (wLayout.valOf (denote (compile wStep wProg.length) rtState) 2
        = (evalProgram [(3 : ZMod 5)] wProg 2).val)
      ∧ (mulReg.valOf
          (denote (compile mulStep [Instr.mul 1 0].length) (wState false true false false true false)) 2
        = (evalProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.mul 1 0] 2).val)
      ∧ (nsmulReg.valOf
          (denote (compile nsmulStep [Instr.nsmul 3 0].length) (constMulState false false true)) 1
        = (evalProgram [(4 : ZMod 5)] [Instr.nsmul 3 0] 1).val)
      ∧ (sqReg.valOf (denote (compile sqStep [Instr.sq 0].length) sqState) 1
        = (evalProgram [(2 : ZMod 3)] [Instr.sq 0] 1).val)
      ∧ (addReg.valOf (denote (compile addStep [Instr.add 0 1].length) addState) 2
        = (evalProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.add 0 1] 2).val)
      ∧ (subReg.valOf (denote (compile subStep [Instr.sub 0 1].length) subState) 2
        = (evalProgram [(1 : ZMod 3), (2 : ZMod 3)] [Instr.sub 0 1] 2).val) :=
  ⟨worked_compile_correct, mul_step_assembly_correct, nsmul_step_assembly_correct,
    sq_step_assembly_correct, add_step_assembly_correct, sub_step_assembly_correct⟩

/-! ## Part 6 — `#eval` cross-checks (`runArr` / `regValRangeArr`, certified by `regValRangeArr_eq`)

The compiled one-step circuits, run on the strict `Array Bool` evaluator, print the field-operation
values the `*_step_assembly_correct` theorems constrain. -/

-- `sq` assembled output, register 1: prints `1` (= `2·2 mod 3`).
#eval regValRangeArr (sqReg.block 1)
  (runArr (compile sqStep 1) (ofState sqState)) 3
-- 1

-- `add` assembled output, register 2: prints `1` (= `(2+2) mod 3`).
#eval regValRangeArr (addReg.block 2)
  (runArr (compile addStep 1) (ofState addState)) 3
-- 1

-- `sub` assembled output, register 2: prints `2` (= `(1-2) mod 3`).
#eval regValRangeArr (subReg.block 2)
  (runArr (compile subStep 1) (ofState subState)) 3
-- 2

/-- The `sub`-assembly `#eval` is the genuine `denote`-based router output: by `regValRangeArr_eq`, the
fast `Array` read of register `2` equals the `regValRange (denote …)` quantity
`sub_step_assembly_correct` constrains. -/
example : regValRangeArr (subReg.block 2)
    (runArr (compile subStep 1) (ofState subState)) 3
      = subReg.valOf (denote (compile subStep 1) subState) 2 :=
  regValRangeArr_eq (subReg.block 2) (compile subStep 1) subState 3

end Reversible
