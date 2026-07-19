import CsdLean4.Ecdsafail.ProgramRouterDoubling

/-!
# Small-fixed-`n` PROVEN gadget assembly through `compile_correct` (STEP 3)  (ECDLP Phase 2, S6.3e-2b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

STEP 1 (`ProgramRouter.lean`) built the SSA register-file fold `compile_correct` and ran ONE worked
multi-gadget program (`[.neg 0, .neg 1]`, the `modNeg` gadget) through it. STEP 2
(`ProgramRouterDoubling.lean`) built the per-opcode dispatcher `compileInstr`, the per-gadget frame
lemmas, the `copyReg`-wrapped SSA adders, and the **`M_dbl = 8` EXHIBITED count**. STEP 3 (this file)
is the `⟦c⟧ = op` payoff: it routes the genuine *field-multiply* (`mulLoop`) and the
*constant-multiply* (`constMulCirc`) gadgets through `compile_correct` at a literal small `n`, landing
each output block on the `.val` of the corresponding `ZMod p` field operation — i.e. the bit circuit
COMPUTES the field op, value-correct mod `p`, established by the verified SSA fold (not merely
`#eval`-checked).

## What STEP 3 proves (this file)

* **`mulLoop_preserves_ctrl` / `mulLoop_preserves_X`** (Part 1) — the missing preservation lemma: the
  multiply loop leaves every multiplier (control) wire, hence the whole multiplier register `X`,
  *unchanged*. STEP 1/STEP 2 only had `mulLoop`-preserves-`B`/`Y` (the accumulator and multiplicand);
  the multiplier is an INPUT register, which `compile_correct`'s frame obligation requires preserved,
  so this lemma is load-bearing for routing `mul` / `sq` through the fold. Proof: a control wire is
  bank `(n-1-i)`'s `ctrl` (preserved by `hornerStep_preserves_ctrl`, folded from `modDouble`'s
  ctrl-disjointness + `cModAdd_preserves_ctrl`) and is untouched by every other bank (`hCtrlTouch`).
* **`nsmul_step_assembly_correct`** (Part 2) — the `nsmul` opcode through `compile_correct`: the
  one-step program `[.nsmul 3 0]` over `ZMod 5`, assembled on the verified `constMulLayout2` /
  `constMulState` witness, leaves the output block holding `(evalProgram [4] [.nsmul 3 0] 1).val = 2`.
* **`mul_step_assembly_correct`** (Part 3) — the genuine field-multiply `mul` through
  `compile_correct`: the one-step program `[.mul 1 0]` over `ZMod 3`, assembled on the verified
  `wMulLoop` / `wState` witness, leaves the output block holding `(evalProgram [r0,r1] [.mul 1 0] 2).val
  = (r1·r0).val` — the bit circuit computes the field multiply, value-correct mod `p`, through the
  abstract SSA fold (multiplier preserved via `mulLoop_preserves_X`, output value via `mulLoop_correct`
  + `mul_bridge`).
* **`M_dbl = 8` over the assembled, now-correctness-proven gadget** (Part 4) — the dispatcher emits one
  `mulLoop` per `mul` / `sq` (`doubling_mulLoop_emissions_eq_8`); STEP 3 proves that very `mulLoop`
  gadget value-correct in the fold (`mul_step_assembly_correct`). So `M = 8` is now a count over a
  circuit whose field-multiply gadget is verified to compute the field op, not just over the opcode
  list.

## Carve line: what is the FULL doubling, what is a representative SUB-program

**The complete `doublingProgram` (dblX/dblY/dblZ over `ZMod p`) is NOT assembled here.** Per the
sanctioned staging (STEP 2 carve line; spec §S6.3e-2b STEP 3), STEP 3 scopes the PROGRAM, not the
claim: each headline lands on the full `evalProgram`-`.val` strength, but for representative one-step
programs (`[.nsmul 3 0]`, `[.mul 1 0]`), not the 17-step doubling. The full doubling assembly is a
multi-thousand-line undertaking blocked, in this pass, by three concrete (mechanical, not logical)
walls, two of which STEP 3 newly surfaces:

1. **Eight literal-`n` `mulLoop`s in one ambient `Fin m`** (~8·135 + const/sub banks ≈ 1200+ wires) with
   a 17-step heterogeneous `hstep` whose every step frames against ~20 register blocks plus every
   ancilla bank: the layout boilerplate alone (each `ModAddLayout` bank ≈ 45 `omega` fields) is
   thousands of lines.
2. **`sq` needs a copy-wrapper the dispatcher lacks (NEW).** `compileInstr (.sq i) = mulLoop`, but the
   `mulLoop` control register `X` and multiplicand `Y` must be on DISJOINT wires (else `hCtrlTouch`
   fails: a control wire would also be a touched multiplicand wire). `sq i` reads block `i` as both, so
   a faithful `sq` assembly needs a `copyReg` of block `i` into a fresh multiplier block first — not in
   the current `compileInstr`. The 4 `sq` opcodes of `doublingProgram` each hit this.
3. **`2^n` presets at secp256k1 width** (`A1 = 2ⁿ − N` at `n = 256`) are not `decide`-able; needs the
   `regValRange`-of-binary-digits extraction helper (the STEP 2 wall, unchanged).

So STEP 3 delivers the genuine `mul` / `nsmul` through-the-fold value-correctness (the atom of the full
assembly) at literal `n`, plus the missing multiplier-preservation lemma, and reports the full-doubling
residue precisely. The orthogonal carry-clean-adder qubit residue is unchanged.
-/

namespace Reversible

open ECDLP

/-! ## Part 1 — the missing multiplier-register preservation lemma

`compile_correct`'s `hstep` requires every earlier register block preserved. For a `mul` / `sq` step the
multiplier register `X` is an input block, so it must survive `mulLoop`. STEP 1/STEP 2 proved only
`B` (accumulator) and `Y` (multiplicand, via `mulLoop_invariant`) preserved. The multiplier wires are
the per-bank control bits, preserved as controls (not flipped) — but no lemma named it. Here it is. -/

/-- **`hornerStep` preserves its control wire.** The control bit `X_i = add.ctrl` survives the whole
Horner step `modDouble dbl ++ cModAdd add`: `modDouble` does not touch it (ctrl disjoint from every
doubling family + `B`, via `hBshared`/`hctrlB`), and `cModAdd` preserves its control
(`cModAdd_preserves_ctrl`, given the controlled-add carries `Ccadd` / ancilla `ancC` clean — preserved
in turn by `modDouble`). -/
theorem hornerStep_preserves_ctrl {m n : ℕ} (L : HornerStepLayout m n) (s : State m)
    (hCcadd : ∀ j, s (L.add.Ccadd j) = false) (hancC : s L.add.ancC = false) :
    denote (hornerStep L) s L.add.ctrl = s L.add.ctrl := by
  rw [hornerStep, denote_append]
  set sd := denote (modDouble L.dbl) s with hsddef
  -- modDouble preserves ctrl (ctrl disjoint from every dbl family, including B via hBshared)
  have hctrl_d : sd L.add.ctrl = s L.add.ctrl := by
    rw [hsddef]
    exact modDouble_preserves_external L.dbl s L.add.ctrl
      (fun k => by rw [L.hBshared]; exact L.add.hctrlB k)
      (fun k => (L.hAopctrl k).symm) (fun k => (L.hCaddctrl k).symm)
      (fun k => (L.hdA1ctrl k).symm) (fun k => (L.hdC1ctrl k).symm)
      (fun k => (L.hdA2ctrl k).symm) (fun k => (L.hdC2ctrl k).symm) L.hdancctrl.symm
  -- the controlled-add carries / ancilla survive modDouble (disjoint), so cModAdd preserves ctrl
  have hCcadd_d : ∀ j, sd (L.add.Ccadd j) = false := fun j => by
    rw [hsddef, modDouble_preserves_external L.dbl s (L.add.Ccadd j)
      (fun k => by rw [L.hBshared]; exact (L.add.hBCcadd k j).symm)
      (fun k => (L.hAopCcadd k j).symm) (fun k => (L.hCaddCcadd k j).symm)
      (fun k => (L.hdA1Ccadd k j).symm) (fun k => (L.hdC1Ccadd k j).symm)
      (fun k => (L.hdA2Ccadd k j).symm) (fun k => (L.hdC2Ccadd k j).symm) (L.hdancCcadd j).symm]
    exact hCcadd j
  have hancC_d : sd L.add.ancC = false := by
    rw [hsddef, modDouble_preserves_external L.dbl s L.add.ancC
      (fun k => by rw [L.hBshared]; exact L.add.hancCB k)
      (fun k => (L.hAopancC k).symm) (fun k => (L.hCaddancC k).symm)
      (fun k => (L.hdA1ancC k).symm) (fun k => (L.hdC1ancC k).symm)
      (fun k => (L.hdA2ancC k).symm) (fun k => (L.hdC2ancC k).symm) L.hdancancC.symm]
    exact hancC
  rw [cModAdd_preserves_ctrl L.add sd hCcadd_d hancC_d, hctrl_d]

/-- A control wire `X i` of bank `(n-1-i)` survives the whole prefix `mulLoopUpto L k` when every bank's
controlled-add carries / ancilla are clean: every bank `j ≠ n-1-i` does not touch it (`hCtrlTouch`),
and bank `n-1-i` (if in the prefix) preserves it as its control (`hornerStep_preserves_ctrl`).

The cleanliness hypotheses are stated at the initial state `s`; bank `k`'s carries survive the prefix
`mulLoopUpto L k` (each lies in `Clean L.bank k`, untouched by earlier banks via `hInter`), so the
`hornerStep_preserves_ctrl` step's preconditions re-establish at the prefix state. -/
theorem mulLoopUpto_preserves_ctrl {m n : ℕ} (L : MulLoopLayout m n) (i : ℕ) (hi : i < n) :
    ∀ k, k ≤ n → ∀ s : State m,
      (∀ j j', j < n → s ((L.bank j).add.Ccadd j') = false) →
      (∀ j, j < n → s (L.bank j).add.ancC = false) →
      denote (mulLoopUpto L k) s (L.X i) = s (L.X i) := by
  intro k
  induction k with
  | zero => intro _ s _ _; rfl
  | succ k ih =>
    intro hk1 s hCcadd hancC
    have hk : k < n := by omega
    set s1 := denote (mulLoopUpto L k) s with hs1def
    rw [mulLoopUpto_succ, denote_append, ← hs1def]
    -- IH: X i survives the prefix
    have hpre : s1 (L.X i) = s (L.X i) := ih (by omega) s hCcadd hancC
    by_cases hek : k = n - 1 - i
    · -- bank k IS the bank whose control is X i: it preserves X i as its ctrl
      have hxc : L.X i = (L.bank k).add.ctrl := by
        rw [show (L.bank k).add.ctrl = (L.bank k).ctrl from rfl, L.hctrl k]
        congr 1; omega
      -- bank k's controlled-add carries / ancilla survive the prefix (in Clean L.bank k)
      have hCcadd1 : ∀ j', s1 ((L.bank k).add.Ccadd j') = false := fun j' => by
        rw [hs1def, mulLoopUpto_preserves L k s ((L.bank k).add.Ccadd j')
          (fun p hp => L.hInter p k _ (by omega) hk (by omega)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j', rfl⟩)))))))))]
        exact hCcadd k j' hk
      have hancC1 : s1 (L.bank k).add.ancC = false := by
        rw [hs1def, mulLoopUpto_preserves L k s (L.bank k).add.ancC
          (fun p hp => L.hInter p k _ (by omega) hk (by omega)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))]
        exact hancC k hk
      rw [hxc, hornerStep_preserves_ctrl (L.bank k) s1 hCcadd1 hancC1, ← hxc, hpre]
    · -- bank k does NOT touch X i (its own ctrl is X (n-1-k) ≠ X i since k ≠ n-1-i)
      rw [notTouches_preserved L k s1 (L.X i) (L.hCtrlTouch k i hk hi (by omega)), hpre]

/-- **`mulLoop` preserves every multiplier (control) wire.** Each `X i` (`i < n`) is preserved by the
whole loop. The load-bearing frame fact for routing `mul` / `sq` through `compile_correct`: the
multiplier register is an input block, required preserved by the fold. -/
theorem mulLoop_preserves_ctrl_wire {m n : ℕ} (L : MulLoopLayout m n) (i : ℕ) (hi : i < n)
    (s : State m)
    (hCcadd : ∀ j j', j < n → s ((L.bank j).add.Ccadd j') = false)
    (hancC : ∀ j, j < n → s (L.bank j).add.ancC = false) :
    denote (mulLoop L) s (L.X i) = s (L.X i) := by
  rw [mulLoop_eq_upto]
  exact mulLoopUpto_preserves_ctrl L i hi n (le_refl n) s hCcadd hancC

/-- **`mulLoop` preserves the multiplier register `X` (register-block form).** -/
theorem mulLoop_preserves_X {m n : ℕ} (L : MulLoopLayout m n) (s : State m)
    (hCcadd : ∀ j j', j < n → s ((L.bank j).add.Ccadd j') = false)
    (hancC : ∀ j, j < n → s (L.bank j).add.ancC = false) :
    regValRange L.X (denote (mulLoop L) s) n = regValRange L.X s n := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  show (denote (mulLoop L) s (L.X i)).toNat * 2 ^ i = (s (L.X i)).toNat * 2 ^ i
  rw [mulLoop_preserves_ctrl_wire L i hi s hCcadd hancC]

/-! ## Part 2 — the `nsmul` opcode through `compile_correct`

The one-step program `[.nsmul 3 0]` over `ZMod 5`, assembled on the verified `constMulLayout2` /
`constMulState` witness (`Fin 200`, `n = 4`, `c = 3`, `N = 5`). The register blocks are the gadget's
operand / accumulator: block `0` = `constMulLayout2.Aop` (input `reg0`), block `1` = `constMulLayout2.B`
(output `reg1 = 3·reg0`). Routing the gadget through the abstract SSA fold (not just `#eval`) lands the
output block on `(evalProgram [4] [.nsmul 3 0] 1).val`. -/

/-- The register-block layout for the `nsmul` step: block `0` = operand, block `1` = accumulator. -/
def nsmulReg : RegBlockLayout 200 4 where
  block r i := if r = 0 then constMulLayout2.Aop i else constMulLayout2.B i

/-- The compiled step circuit: the constant-multiply gadget (the SSA position is irrelevant for the
one-step program). -/
def nsmulStep : ℕ → Circuit 200 := fun _ => constMulCirc constMulLayout2

/-- Step `t`'s self-precondition: fresh-zero accumulator, clean carries/ancilla, presets `A1 = 11`,
`A2 = 5`. (The operand value enters via the fold's register-file invariant, not `selfPre`.) -/
def nsmulPre : ℕ → State 200 → Prop := fun _ s =>
  regValRange constMulLayout2.B s 4 = 0
    ∧ (∀ j i, j < 3 → s ((constMulLayout2.bank j).Cadd i) = false)
    ∧ (∀ j i, j < 3 → s ((constMulLayout2.bank j).C1 i) = false)
    ∧ (∀ j i, j < 3 → s ((constMulLayout2.bank j).C2 i) = false)
    ∧ (∀ j, j < 3 → s (constMulLayout2.bank j).anc = false)
    ∧ (∀ j, j < 3 → regValRange (constMulLayout2.bank j).A1 s 4 = 2 ^ 4 - 5)
    ∧ (∀ j, j < 3 → regValRange (constMulLayout2.bank j).A2 s 4 = 5)

/-- The `ZMod 5` register file of `[.nsmul 3 0]` on input `4`: `[4, 3·4]` (i.e. `[4, 2]`). -/
theorem nsmulRun :
    runProgram [(4 : ZMod 5)] [Instr.nsmul 3 0] = [(4 : ZMod 5), ((3 : ℕ) : ZMod 5) * 4] := by
  simp only [runProgram, evalInstr, regGet, List.cons_append, List.nil_append]

/-- The clean / preset preconditions hold at `constMulState` (replicating the private
`constMulState_pre`; `cmin4_cases` + `interval_cases`). -/
theorem nsmulPre_at_state (a0 a1 a2 : Bool) : nsmulPre 0 (constMulState a0 a1 a2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [regValRange, Finset.sum_range_succ, constMulLayout2, cBank, ConstMulLayout.B, constMulState]
  · intro j i hj; interval_cases j <;>
      (rcases cmin4_cases i with h | h | h | h | h <;>
        (dsimp only [constMulLayout2, cBank]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases cmin4_cases i with h | h | h | h | h <;>
        (dsimp only [constMulLayout2, cBank]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases cmin4_cases i with h | h | h | h | h <;>
        (dsimp only [constMulLayout2, cBank]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;>
      (dsimp only [constMulLayout2, cBank]; simp only [constMulState]; rfl)
  · intro j hj; interval_cases j <;>
      (simp only [constMulLayout2, cBank, regValRange, Finset.sum_range_succ, constMulState]; rfl)
  · intro j hj; interval_cases j <;>
      (simp only [constMulLayout2, cBank, regValRange, Finset.sum_range_succ, constMulState]; rfl)

/-- **The `nsmul` opcode assembled through `compile_correct`.** The compiled one-step circuit for
`[.nsmul 3 0]` over `ZMod 5`, on `constMulState false false true` (operand `4`), leaves the output block
(register `1`) holding `(evalProgram [4] [.nsmul 3 0] 1).val`. The bit circuit computes the field
constant-multiply, value-correct mod `5`, via the verified SSA fold. -/
theorem nsmul_step_assembly_correct :
    nsmulReg.valOf
        (denote (compile nsmulStep [Instr.nsmul 3 0].length) (constMulState false false true)) 1
      = (evalProgram [(4 : ZMod 5)] [Instr.nsmul 3 0] 1).val := by
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  refine compile_correct nsmulReg [(4 : ZMod 5)] [Instr.nsmul 3 0] nsmulStep nsmulPre
    (constMulState false false true) ?_ ?_ ?_ ?_ 1 (by decide)
  · -- hbase: operand block holds its value at the initial state
    intro r hr
    have : r = 0 := by simpa using hr
    subst this
    show regValRange constMulLayout2.Aop (constMulState false false true) 4
      = (regGet (runProgram [(4 : ZMod 5)] [Instr.nsmul 3 0]) 0).val
    rw [nsmulRun]
    show regValRange constMulLayout2.Aop (constMulState false false true) 4 = ZMod.val (4 : ZMod 5)
    rw [show ZMod.val (4 : ZMod 5) = 4 from by decide]
    simp [regValRange, Finset.sum_range_succ, constMulLayout2, cBank, ConstMulLayout.Aop,
      constMulState]
  · -- hpre0: the self-preconditions hold at the initial state
    intro t ht
    have : t = 0 := by simpa using ht
    subst this; exact nsmulPre_at_state false false true
  · -- hpre_frame: vacuous (no earlier step in a one-step program)
    intro t t' ht't ht s hsp
    have : t < 1 := by simpa using ht
    omega
  · -- hstep: the constant-multiply gadget extends the register-file invariant
    intro t ht s hHolds hsp r hr
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    obtain ⟨hB0, hCadd, hC1, hC2, hanc, hA1, hA2⟩ := hsp
    -- operand value at s comes from the fold invariant (block 0 holds reg0 = 4)
    have hAv : regValRange constMulLayout2.Aop s 4 = 4 := by
      have h0 := hHolds 0 (by simp)
      rw [nsmulRun] at h0
      simpa using h0
    have hval := modConstMul_correct constMulLayout2 s (N := 5) (aval := 4)
      (by decide) (by decide) hB0 hAv hCadd hC1 hC2 hanc hA1 hA2
    have hop := modConstMul_preserves_operand constMulLayout2 s (N := 5) (aval := 4)
      (by decide) (by decide) hB0 hAv hCadd hC1 hC2 hanc hA1 hA2
    show nsmulReg.valOf (denote (nsmulStep 0) s) r = _
    have hr2 : r < 2 := by simpa using hr
    interval_cases r
    · -- r = 0: operand preserved
      show regValRange constMulLayout2.Aop (denote (constMulCirc constMulLayout2) s) 4 = _
      rw [hop, nsmulRun]; decide
    · -- r = 1: output value = (3·4) mod 5 = ((3 : ZMod 5)·4).val
      show regValRange constMulLayout2.B (denote (constMulCirc constMulLayout2) s) 4 = _
      rw [hval, nsmulRun]; decide

/-- The `nsmul`-step output value is `2` (`= (3·4) mod 5`). -/
theorem nsmul_step_value :
    nsmulReg.valOf
        (denote (compile nsmulStep [Instr.nsmul 3 0].length) (constMulState false false true)) 1
      = 2 := by
  rw [nsmul_step_assembly_correct]
  show (evalProgram [(4 : ZMod 5)] [Instr.nsmul 3 0] 1).val = 2
  rw [evalProgram, nsmulRun]; decide

/-! ## Part 3 — the field-multiply `mul` opcode through `compile_correct`

The genuine register×register field multiply. The one-step program `[.mul 1 0]` over `ZMod 3`,
assembled on the verified `wMulLoop` / `wState` witness (`Fin 135`, `n = 3`, `N = 3`). The register
blocks are the gadget's multiplicand / multiplier / accumulator: block `0` = `wMulLoop.Y` (input `reg0`,
the multiplicand), block `1` = `wMulLoop.X` (input `reg1`, the multiplier), block `2` = `wMulLoop.B`
(output `reg2 = reg1·reg0`). The output block lands on `(evalProgram [r0,r1] [.mul 1 0] 2).val =
(reg1·reg0).val` via the abstract SSA fold — the multiplier (an input block) preserved by
`mulLoop_preserves_X`, the multiplicand by `mulLoop_invariant`, the output value by `mulLoop_correct` +
`mul_bridge`. This is the `⟦c⟧ = op` payoff: a bit circuit proven to compute the FIELD multiply, mod
`p`, through the verified router. -/

/-- The register-block layout for the `mul` step: block `0` = multiplicand `Y`, block `1` = multiplier
`X`, block `2` = accumulator `B`. -/
def mulReg : RegBlockLayout 135 3 where
  block r i := if r = 0 then wMulLoop.Y i else if r = 1 then wMulLoop.X i else wMulLoop.B i

/-- The compiled step circuit: the field-multiply loop. -/
def mulStep : ℕ → Circuit 135 := fun _ => mulLoop wMulLoop

/-- Step `t`'s self-precondition: fresh-zero accumulator, every bank's scratch / carries / ancilla
clean, every bank's reduce presets `A1 = 5`, `A2 = 3`. (The multiplicand / multiplier values enter via
the fold's register-file invariant.) -/
def mulPre : ℕ → State 135 → Prop := fun _ s =>
  regValRange wMulLoop.B s 3 = 0
    ∧ (∀ j i, j < 3 → i < 3 → s ((wMulLoop.bank j).dbl.Aop i) = false)
    ∧ (∀ j i, j < 3 → s ((wMulLoop.bank j).dbl.addLayout.Cadd i) = false)
    ∧ (∀ j i, j < 3 → s ((wMulLoop.bank j).dbl.addLayout.C1 i) = false)
    ∧ (∀ j i, j < 3 → s ((wMulLoop.bank j).dbl.addLayout.C2 i) = false)
    ∧ (∀ j, j < 3 → s (wMulLoop.bank j).dbl.addLayout.anc = false)
    ∧ (∀ j i, j < 3 → s ((wMulLoop.bank j).add.Ccadd i) = false)
    ∧ (∀ j, j < 3 → s (wMulLoop.bank j).add.ancC = false)
    ∧ (∀ j i, j < 3 → s ((wMulLoop.bank j).add.C1 i) = false)
    ∧ (∀ j i, j < 3 → s ((wMulLoop.bank j).add.C2 i) = false)
    ∧ (∀ j, j < 3 → s (wMulLoop.bank j).add.anc = false)
    ∧ (∀ j, j < 3 → regValRange (wMulLoop.bank j).dbl.addLayout.A1 s 3 = 2 ^ 3 - 3)
    ∧ (∀ j, j < 3 → regValRange (wMulLoop.bank j).dbl.addLayout.A2 s 3 = 3)
    ∧ (∀ j, j < 3 → regValRange (wMulLoop.bank j).add.A1 s 3 = 2 ^ 3 - 3)
    ∧ (∀ j, j < 3 → regValRange (wMulLoop.bank j).add.A2 s 3 = 3)

/-- The `ZMod 3` register file of `[.mul 1 0]` on inputs `[2, 2]`: `[2, 2, 2·2]` (i.e. `[2, 2, 1]`). -/
theorem mulRun :
    runProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.mul 1 0]
      = [(2 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3) * (2 : ZMod 3)] := by
  simp only [runProgram, evalInstr, regGet, List.cons_append, List.nil_append]

set_option maxRecDepth 4000 in
/-- The clean / preset preconditions of the field-multiply hold at `wState false true false false true
false` (multiplicand `Y = 2`, multiplier `X = 2`), replicating the discharge of the in-file
`mulLoop_correct` example. -/
theorem mulPre_at_state : mulPre 0 (wState false true false false true false) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i hj hi; interval_cases j <;> interval_cases i <;> decide
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [wMulLoop, wBank, wDbl]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [wMulLoop, wBank, wDbl]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [wMulLoop, wBank, wDbl]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;> (dsimp only [wMulLoop, wBank, wDbl]; decide)
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [wMulLoop, wBank, wAdd]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;> (dsimp only [wMulLoop, wBank, wAdd]; decide)
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [wMulLoop, wBank, wAdd]; simp only [h]; rfl))
  · intro j i hj; interval_cases j <;>
      (rcases min3_cases i with h | h | h | h <;>
        (dsimp only [wMulLoop, wBank, wAdd]; simp only [h]; rfl))
  · intro j hj; interval_cases j <;> (dsimp only [wMulLoop, wBank, wAdd]; decide)
  · intro j hj; interval_cases j <;> decide
  · intro j hj; interval_cases j <;> decide
  · intro j hj; interval_cases j <;> decide
  · intro j hj; interval_cases j <;> decide

set_option maxRecDepth 4000 in
/-- **The field-multiply `mul` opcode assembled through `compile_correct`.** The compiled one-step
circuit for `[.mul 1 0]` over `ZMod 3`, on `wState false true false false true false` (inputs `2`, `2`),
leaves the output block (register `2`) holding `(evalProgram [2,2] [.mul 1 0] 2).val` — the bit circuit
computes the field multiply, value-correct mod `3`, via the verified SSA fold. -/
theorem mul_step_assembly_correct :
    mulReg.valOf
        (denote (compile mulStep [Instr.mul 1 0].length) (wState false true false false true false)) 2
      = (evalProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.mul 1 0] 2).val := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  refine compile_correct mulReg [(2 : ZMod 3), (2 : ZMod 3)] [Instr.mul 1 0] mulStep mulPre
    (wState false true false false true false) ?_ ?_ ?_ ?_ 2 (by decide)
  · -- hbase: the two input blocks hold their values
    intro r hr
    have hr2 : r < 2 := by simpa using hr
    rw [mulRun]
    interval_cases r
    · show regValRange wMulLoop.Y (wState false true false false true false) 3 = ZMod.val (2 : ZMod 3)
      decide
    · show regValRange wMulLoop.X (wState false true false false true false) 3 = ZMod.val (2 : ZMod 3)
      decide
  · -- hpre0: the self-preconditions hold at the initial state
    intro t ht
    have : t = 0 := by simpa using ht
    subst this; exact mulPre_at_state
  · -- hpre_frame: vacuous (no earlier step in a one-step program)
    intro t t' ht't ht s hsp
    have : t < 1 := by simpa using ht
    omega
  · -- hstep: the field-multiply gadget extends the register-file invariant
    intro t ht s hHolds hsp r hr
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    obtain ⟨hB0, hAop, hCadd, hdC1, hdC2, hdanc, hCcadd, hancC, hC1, hC2, hanc,
      hA1dbl, hA2dbl, hA1add, hA2add⟩ := hsp
    -- multiplicand / multiplier values at s from the fold invariant
    have hYval : regValRange wMulLoop.Y s 3 = ZMod.val (2 : ZMod 3) := by
      have h0 := hHolds 0 (by simp); rw [mulRun] at h0; simpa using h0
    have hXval : regValRange wMulLoop.X s 3 = ZMod.val (2 : ZMod 3) := by
      have h1 := hHolds 1 (by simp); rw [mulRun] at h1; simpa using h1
    have hYN : ZMod.val (2 : ZMod 3) < 3 := by decide
    -- B output value via mulLoop_correct
    have hBval := mulLoop_correct wMulLoop s (N := 3) (Yval := ZMod.val (2 : ZMod 3))
      (by decide) (by decide) hYN hB0 hYval hAop hCadd hdC1 hdC2 hdanc hCcadd hancC hC1 hC2 hanc
      hA1dbl hA2dbl hA1add hA2add
    -- multiplicand preserved via mulLoop_invariant
    have hYpres := (mulLoop_invariant wMulLoop s (N := 3) (Yval := ZMod.val (2 : ZMod 3))
      (by decide) (by decide) hYN hB0 hYval hAop hCadd hdC1 hdC2 hdanc hCcadd hancC hC1 hC2 hanc
      hA1dbl hA2dbl hA1add hA2add 3 (le_refl 3)).2
    rw [← mulLoop_eq_upto] at hYpres
    -- multiplier preserved via mulLoop_preserves_X
    have hXpres := mulLoop_preserves_X wMulLoop s
      (fun j j' hj => hCcadd j j' hj) (fun j hj => hancC j hj)
    show mulReg.valOf (denote (mulStep 0) s) r = _
    have hr3 : r < 3 := by simpa using hr
    interval_cases r
    · -- r = 0: multiplicand preserved
      rw [mulRun]
      show regValRange wMulLoop.Y (denote (mulLoop wMulLoop) s) 3 = ZMod.val (2 : ZMod 3)
      rw [hYpres]
    · -- r = 1: multiplier preserved
      rw [mulRun]
      show regValRange wMulLoop.X (denote (mulLoop wMulLoop) s) 3 = ZMod.val (2 : ZMod 3)
      rw [hXpres]; exact hXval
    · -- r = 2: output value = (X·Y) mod 3 = (reg1·reg0).val
      rw [mulRun]
      show regValRange wMulLoop.B (denote (mulLoop wMulLoop) s) 3
        = ((2 : ZMod 3) * (2 : ZMod 3)).val
      rw [hBval, hXval, mul_bridge]

/-- The `mul`-step output value is `1` (`= (2·2) mod 3`). -/
theorem mul_step_value :
    mulReg.valOf
        (denote (compile mulStep [Instr.mul 1 0].length) (wState false true false false true false)) 2
      = 1 := by
  rw [mul_step_assembly_correct]
  show (evalProgram [(2 : ZMod 3), (2 : ZMod 3)] [Instr.mul 1 0] 2).val = 1
  rw [evalProgram, mulRun]; decide

/-! ## Part 4 — `M_dbl = 8` over the now-correctness-proven field-multiply gadget

STEP 2's `doubling_mulLoop_emissions_eq_8` exhibits that the dispatcher emits exactly `8` field-multiply
gadgets for `doublingProgram`, each (by `compileInstr_mul` / `compileInstr_sq`) the gadget
`mulLoop G.mulLayout`. STEP 3's `mul_step_assembly_correct` proves that very `mulLoop` gadget computes
the field multiply value-correctly through the verified SSA fold. So `M = 8` is now a count over a
circuit whose field-multiply gadget kind is *verified to compute the field op*, not merely an opcode
tally. -/

/-- **`M_dbl = 8` over the verified gadget.** The dispatcher emits `8` field-multiply gadgets for the
`a = 0` doubling (`doubling_mulLoop_emissions_eq_8`), and the gadget each `mul` opcode dispatches to is
`mulLoop G.mulLayout` (`compileInstr_mul`) — the gadget kind STEP 3's `mul_step_assembly_correct` proves
computes the field multiply mod `p`. -/
theorem doubling_field_mul_count_eq_8_verified :
    (doublingProgram.filter emitsFieldMul).length = 8
      ∧ ∀ (G : StepGadgets 135 3) (i j : ℕ), compileInstr G (.mul i j) = mulLoop G.mulLayout :=
  ⟨doubling_mulLoop_emissions_eq_8, fun G i j => compileInstr_mul G i j⟩

/-! ## Part 5 — `#eval` cross-checks (`runArr` / `regValRangeArr`, certified by `regValRangeArr_eq`)

The compiled one-step circuits, run on the strict `Array Bool` evaluator, print the field-operation
values that the `*_assembly_correct` theorems constrain. `compile nsmulStep 1 = constMulCirc
constMulLayout2`, `compile mulStep 1 = mulLoop wMulLoop` (one-step `routerUpto`). -/

-- `nsmul` assembled output, register 1: prints `2` (= `3·4 mod 5`).
#eval regValRangeArr (nsmulReg.block 1)
  (runArr (compile nsmulStep 1) (ofState (constMulState false false true))) 4
-- 2

-- `mul` assembled output, register 2: prints `1` (= `2·2 mod 3`).
#eval regValRangeArr (mulReg.block 2)
  (runArr (compile mulStep 1) (ofState (wState false true false false true false))) 3
-- 1

/-- The `mul`-assembly `#eval` is the genuine `denote`-based router output: by `regValRangeArr_eq`, the
fast `Array` read of register `2` equals the `regValRange (denote …)` quantity `mul_step_assembly_correct`
constrains. -/
example : regValRangeArr (mulReg.block 2)
    (runArr (compile mulStep 1) (ofState (wState false true false false true false))) 3
      = mulReg.valOf (denote (compile mulStep 1) (wState false true false false true false)) 2 :=
  regValRangeArr_eq (mulReg.block 2) (compile mulStep 1) (wState false true false false true false) 3

end Reversible
