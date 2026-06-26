import CsdLean4.Mathlib.QuantumInfo.Reversible.ProgramRouter
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularConst

/-!
# SLP → circuit dispatcher + doubling assembly (STEP 2)  (ECDLP Phase 2, Stage S6.3e-2b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

STEP 1 (`ProgramRouter.lean`) built the reusable register-block layout schema, the `ℕ`-`% p` ↔
`ZMod p`-`.val` arithmetic bridge for every field opcode, the abstract SSA register-file fold
(`compile_correct`), and one worked multi-gadget `modNeg` instance. STEP 2 builds the **per-opcode
dispatcher** that maps each of the six `ECDLP.Instr` opcodes to its verified field-arithmetic gadget,
the two not-yet-built per-gadget external frame lemmas, the `copyReg`-wrapped SSA-fresh adders, and the
**`M_dbl = 8` exhibited-count** result connecting the dispatcher's field-multiply emissions to the
DERIVED doubling multiplication count.

## What STEP 2 proves (this file)

* **`mulLoop_preserves_external` / `modConstMul_preserves_external`** (Part 1) — the two per-gadget
  external frame lemmas the SSA fold's `hstep` frame obligation needs (a wire untouched by every bank
  is preserved by the whole gadget), folded from the existing prefix-frame lemmas. The register-block
  forms (`*_preserves_block`) are the shape `compile_correct`'s `hstep` consumes for the *other*
  blocks.
* **`compileInstr`** (Part 2) — the dispatcher `StepGadgets m n → Instr → Circuit m`, mapping
  `mul`/`sq → mulLoop`, `add → copyReg ++ modAdd`, `sub → copyReg ++ modSub`, `nsmul → constMulCirc`,
  `neg → modNeg`. The six dispatch equations hold by `rfl` (`compileInstr_*`), the per-opcode contract.
* **`addWrap_correct` / `subWrap_correct`** (Part 3) — the `copyReg`-wrapper correctness lemmas for the
  in-place `modAdd`/`modSub` gadgets: copying a source into the fresh output block first, then running
  the in-place op, yields the SSA-fresh `(a + b) % N` / `(a − b) % N` in the output, with the addend /
  subtrahend preserved. Discharges deliverable-1's explicit `copyReg`-wrapper requirement.
* **The `M_dbl = 8` exhibited count** (Part 4) — `doubling_mulLoop_emissions`:
  `(doublingProgram.filter emitsFieldMul).length = M_dbl = 8`. The dispatcher emits exactly one
  `mulLoop` field-multiply gadget per `mul`/`sq` opcode (`compileInstr_emits_mulLoop`), so the number
  of `mulLoop` gadgets in the dispatched doubling circuit is the DERIVED count `M_dbl`, not a free
  parameter. `#eval` cross-checks on the verified `wMulLoop` / `constMulLayout2` witnesses exercise the
  `mul` and `nsmul` dispatch paths end-to-end.

## Carve line: what STEP 2 does NOT do — the genuine wall

STEP 2 builds the dispatcher and exhibits `M_dbl = 8` as a count of the dispatched circuit's
field-multiply gadgets. It does **not** run the full `doublingProgram` through `compile_correct` to a
proof that the assembled *bit* circuit computes the secp256k1 doubling over `ZMod p`. That full
assembly is blocked, not by the schema's inhabitability (`contigBlock_injOn` settles that for every
register count), but by two concrete infrastructure walls:

1. **Parametric general-`n` `mulLoop` layout (nonlinear-stride `omega` wall).** A `MulLoopLayout m n`
   has `n` Horner banks; bank `j` sits at offset `perBankStride(n) · j`. For *symbolic* `n` the stride
   is itself a function of `n`, so the inter-bank disjointness offsets are the product of two variables
   (`perBankStride(n) · j`), which `omega` (linear) cannot discharge. The corpus sidesteps this by
   fixing `n = 3` literally (`wMulLoop`, stride `42`), restoring linearity. A full doubling therefore
   needs eight `mulLoop` layouts at a *literal* `n`, each at a distinct base in one ambient `Fin m`.
2. **Preset bit-extraction (`2^n`-decidability wall).** The reduce presets `A1 = 2ⁿ − N`, `A2 = N`
   must be set in the initial state and proved by `regValRange … = 2ⁿ − N`. At secp256k1 width
   `n = 256` (`N = p ≈ 2²⁵⁶`) a concrete state cannot discharge this by `decide`; it needs a
   "`regValRange` of the binary digits of `K` equals `K`" extraction lemma not yet in the corpus.

So the realistic full assembly is the *small-fixed-`n`* doubling (eight literal-`n` `mulLoop`s + the
const/sub layouts in one ambient `Fin m` + the 17-step heterogeneous `hstep` discharge), which is the
**S6.3e-3** sub-step. **Named residue (unchanged):** the per-step fresh-ancilla banks leave dirty
carries / borrow flags (`Θ(n²)` qubits per multiply); in-place reuse needs the carry-clean /
ancilla-restoring adder the corpus does NOT yet provide.
-/

namespace Reversible

open ECDLP

variable {m n : ℕ}

/-! ## Part 1 — the two missing per-gadget external frame lemmas

`compile_correct`'s `hstep` requires each step's gadget to preserve every *other* register block (the
frame obligation). For `mulLoop` and `modConstMul` the "preserves every external wire" forms were not
yet named; they fold directly from the existing prefix-frame lemmas (`mulLoopUpto_preserves` at `k = n`,
`constMulUpto_preserves` at `k = c`). -/

/-- **`mulLoop` external frame.** A wire untouched by every bank `j < n` survives the whole multiply
loop. (`mulLoopUpto_preserves` at `k = n`, via `mulLoop_eq_upto`.) -/
theorem mulLoop_preserves_external (L : MulLoopLayout m n) (s : State m) (w : Fin m)
    (hw : ∀ j, j < n → ¬ Touches L.bank j w) :
    denote (mulLoop L) s w = s w := by
  rw [mulLoop_eq_upto]
  exact mulLoopUpto_preserves L n s w hw

/-- **`mulLoop` register-block frame.** A register `f` whose every wire is untouched by every bank
survives `mulLoop` (the form the SSA fold reads off for the *other* blocks). -/
theorem mulLoop_preserves_block (L : MulLoopLayout m n) (s : State m) (f : ℕ → Fin m) (q : ℕ)
    (hf : ∀ i, ∀ j, j < n → ¬ Touches L.bank j (f i)) :
    regValRange f (denote (mulLoop L) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (mulLoop L) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [mulLoop_preserves_external L s (f i) (hf i)]

/-- **`modConstMul` external frame.** A wire untouched by every bank `j < c` survives the whole
constant-multiply. (`constMulUpto_preserves` at `k = c`, via `constMul_eq_upto`.) -/
theorem modConstMul_preserves_external {c : ℕ} (L : ConstMulLayout m n c) (s : State m) (w : Fin m)
    (hw : ∀ j, j < c → ¬ CTouches L.bank j w) :
    denote (constMulCirc L) s w = s w := by
  rw [constMul_eq_upto]
  exact constMulUpto_preserves L c s w hw

/-- **`modConstMul` register-block frame.** A register `f` whose every wire is untouched by every bank
survives `constMulCirc`. -/
theorem modConstMul_preserves_block {c : ℕ} (L : ConstMulLayout m n c) (s : State m) (f : ℕ → Fin m)
    (q : ℕ) (hf : ∀ i, ∀ j, j < c → ¬ CTouches L.bank j (f i)) :
    regValRange f (denote (constMulCirc L) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (constMulCirc L) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [modConstMul_preserves_external L s (f i) (hf i)]

/-! ## Part 2 — the per-opcode dispatcher

`compileInstr` maps each `ECDLP.Instr` opcode to its verified gadget. The gadget *layouts* (which wire
blocks each opcode reads / writes) are supplied by the caller via `StepGadgets`, so the dispatcher is
purely the opcode → gadget routing; the operand register indices `i, j` of the instruction are encoded
in the supplied layout. The in-place `add` / `sub` gadgets overwrite their accumulator, so SSA-fresh
output needs a `copyReg` of a source into the fresh block first (Part 3 proves these wrappers correct);
`nsmul` / `neg` / `mul` / `sq` are `copyReg`-free. -/

/-- The per-step gadget layouts the dispatcher selects from, all on one ambient `Fin m` for `n`-bit
blocks. The caller wires the instruction's operand registers into the chosen blocks. -/
structure StepGadgets (m n : ℕ) where
  /-- `mul i j` / `sq i`: the field-multiply loop (`X = block i`, `Y = block j`, accumulator `B` =
  the fresh output block). -/
  mulLayout : MulLoopLayout m n
  /-- `add`: the `copyReg` source→output layout (copies a source block into the fresh output `B`). -/
  addCopy : ModDoubleLayout m n
  /-- `add`: the in-place modular adder (`Aop` = the other source, `B` = the output). -/
  addOp : ModAddLayout m n
  /-- `sub`: the `copyReg` minuend→output layout. -/
  subCopy : ModDoubleLayout m n
  /-- `sub`: the in-place modular subtractor (`B` = output = minuend copy, `Sub` = subtrahend). -/
  subOp : ModSubLayout m n
  /-- `nsmul c i`: the constant-multiply (`c` banks; `Aop` = block `i`, accumulator `B` = output). -/
  nsmulLayout : (c : ℕ) → ConstMulLayout m n c
  /-- `neg i`: the modular negation (`= modSub` with the minuend held `0`; `Sub` = block `i`). -/
  negOp : ModSubLayout m n

/-- **The SLP → circuit per-opcode dispatcher.** Maps each `ECDLP.Instr` opcode to its verified
field-arithmetic gadget on the supplied per-step layouts. -/
def compileInstr (G : StepGadgets m n) : Instr → Circuit m
  | .mul _ _   => mulLoop G.mulLayout
  | .sq _      => mulLoop G.mulLayout
  | .add _ _   => copyReg G.addCopy ++ modAdd G.addOp
  | .sub _ _   => copyReg G.subCopy ++ modSub G.subOp
  | .nsmul c _ => constMulCirc (G.nsmulLayout c)
  | .neg _     => modNeg G.negOp

/-! ### The per-opcode dispatch contract (all by `rfl`) -/

theorem compileInstr_mul (G : StepGadgets m n) (i j : ℕ) :
    compileInstr G (.mul i j) = mulLoop G.mulLayout := rfl

theorem compileInstr_sq (G : StepGadgets m n) (i : ℕ) :
    compileInstr G (.sq i) = mulLoop G.mulLayout := rfl

theorem compileInstr_add (G : StepGadgets m n) (i j : ℕ) :
    compileInstr G (.add i j) = copyReg G.addCopy ++ modAdd G.addOp := rfl

theorem compileInstr_sub (G : StepGadgets m n) (i j : ℕ) :
    compileInstr G (.sub i j) = copyReg G.subCopy ++ modSub G.subOp := rfl

theorem compileInstr_nsmul (G : StepGadgets m n) (c i : ℕ) :
    compileInstr G (.nsmul c i) = constMulCirc (G.nsmulLayout c) := rfl

theorem compileInstr_neg (G : StepGadgets m n) (i : ℕ) :
    compileInstr G (.neg i) = modNeg G.negOp := rfl

/-! ## Part 3 — the `copyReg`-wrapped SSA-fresh adders / subtractors

The SLP `add i j` / `sub i j` produce a value into a *fresh* register, but `modAdd` / `modSub`
overwrite their accumulator `B` in place. The wrapper copies a source block into the fresh output block
(`copyReg`, output register `B := Lc.Aop = Lop.B`), then runs the in-place op. The correctness lemmas
below thread the copy step (`copyReg_correct_operand` writes the source into the output; the disjoint
presets / carries survive via `copyReg_preserves`) into the gadget correctness lemma. -/

/-- A register family `f` disjoint from `copyReg Lc`'s touched wires (`Lc.B`, `Lc.Aop`) survives the
copy. The register-block form of `copyReg_preserves`. -/
theorem copyReg_preserves_reg (Lc : ModDoubleLayout m n) (s : State m) (f : ℕ → Fin m) (q : ℕ)
    (hB : ∀ i k, f i ≠ Lc.B k) (hA : ∀ i k, f i ≠ Lc.Aop k) :
    regValRange f (denote (copyReg Lc) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (copyReg Lc) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [copyReg_preserves s (f i) (hB i) (hA i)]

/-- **The SSA-fresh modular adder.** With the fresh output block `Lc.Aop = Lop.B` initialised `0`, the
copy writes source-`b` (held in `Lc.B`) into the output; then `modAdd` adds source-`a` (held in
`Lop.Aop`, disjoint from the copy wires), leaving the output block holding `(a + b) % N`.

The disjointness hypotheses (`Lop.Aop / A1 / A2 / Cadd / C1 / C2 / anc` distinct from `Lc.B`, `Lc.Aop`)
are exactly what makes the addend, presets and clean carries survive the copy so `modAdd_correct`'s
hypotheses re-establish. -/
theorem addWrap_correct (Lc : ModDoubleLayout m n) (Lop : ModAddLayout m n) (s : State m)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hOutEq : Lc.Aop = Lop.B)
    (hOut0 : ∀ i, i < n → s (Lc.Aop i) = false)
    (hBcopy : regValRange Lc.B s n = b) (hbN : b < N)
    (hAval : regValRange Lop.Aop s n = a) (haN : a < N)
    (hA1 : regValRange Lop.A1 s n = 2 ^ n - N) (hA2 : regValRange Lop.A2 s n = N)
    (hCadd : ∀ j, s (Lop.Cadd j) = false) (hC1 : ∀ j, s (Lop.C1 j) = false)
    (hC2 : ∀ j, s (Lop.C2 j) = false) (hanc : s Lop.anc = false)
    (dAopB : ∀ i k, Lop.Aop i ≠ Lc.B k) (dAopAop : ∀ i k, Lop.Aop i ≠ Lc.Aop k)
    (dA1B : ∀ i k, Lop.A1 i ≠ Lc.B k) (dA1Aop : ∀ i k, Lop.A1 i ≠ Lc.Aop k)
    (dA2B : ∀ i k, Lop.A2 i ≠ Lc.B k) (dA2Aop : ∀ i k, Lop.A2 i ≠ Lc.Aop k)
    (dCaddB : ∀ j k, Lop.Cadd j ≠ Lc.B k) (dCaddAop : ∀ j k, Lop.Cadd j ≠ Lc.Aop k)
    (dC1B : ∀ j k, Lop.C1 j ≠ Lc.B k) (dC1Aop : ∀ j k, Lop.C1 j ≠ Lc.Aop k)
    (dC2B : ∀ j k, Lop.C2 j ≠ Lc.B k) (dC2Aop : ∀ j k, Lop.C2 j ≠ Lc.Aop k)
    (dancB : ∀ k, Lop.anc ≠ Lc.B k) (dancAop : ∀ k, Lop.anc ≠ Lc.Aop k) :
    regValRange Lop.B (denote (copyReg Lc ++ modAdd Lop) s) n = (a + b) % N := by
  set scp := denote (copyReg Lc) s with hscpdef
  rw [denote_append, ← hscpdef]
  -- output block (= Lop.B = Lc.Aop) holds b after the copy
  have hBscp : regValRange Lop.B scp n = b := by
    rw [← hOutEq, hscpdef, copyReg_correct_operand Lc s hOut0, hBcopy]
  -- addend Lop.Aop survives the copy (disjoint), still a
  have hAscp : regValRange Lop.Aop scp n = a := by
    rw [hscpdef, copyReg_preserves_reg Lc s Lop.Aop n dAopB dAopAop, hAval]
  -- presets survive the copy
  have hA1scp : regValRange Lop.A1 scp n = 2 ^ n - N := by
    rw [hscpdef, copyReg_preserves_reg Lc s Lop.A1 n dA1B dA1Aop, hA1]
  have hA2scp : regValRange Lop.A2 scp n = N := by
    rw [hscpdef, copyReg_preserves_reg Lc s Lop.A2 n dA2B dA2Aop, hA2]
  -- clean carries / ancilla survive the copy
  have hCaddscp : ∀ j, scp (Lop.Cadd j) = false := fun j => by
    rw [hscpdef, copyReg_preserves s (Lop.Cadd j) (dCaddB j) (dCaddAop j)]; exact hCadd j
  have hC1scp : ∀ j, scp (Lop.C1 j) = false := fun j => by
    rw [hscpdef, copyReg_preserves s (Lop.C1 j) (dC1B j) (dC1Aop j)]; exact hC1 j
  have hC2scp : ∀ j, scp (Lop.C2 j) = false := fun j => by
    rw [hscpdef, copyReg_preserves s (Lop.C2 j) (dC2B j) (dC2Aop j)]; exact hC2 j
  have hancscp : scp Lop.anc = false := by
    rw [hscpdef, copyReg_preserves s Lop.anc dancB dancAop]; exact hanc
  exact modAdd_correct Lop scp hCaddscp hC1scp hC2scp hancscp h2N hA1scp hA2scp hAscp hBscp haN hbN

/-- **The SSA-fresh modular subtractor.** With the fresh output block `Lc.Aop = Lop.B` initialised `0`,
the copy writes the minuend-`a` (held in `Lc.B`) into the output; then `modSub` subtracts the
subtrahend-`b` (held in `Lop.Sub`, disjoint from the copy wires), leaving the output block holding
`(a + N − b) % N = (a − b) mod N`. -/
theorem subWrap_correct (Lc : ModDoubleLayout m n) (Lop : ModSubLayout m n) (s : State m)
    {N a b : ℕ} (hN : N ≤ 2 ^ n)
    (hOutEq : Lc.Aop = Lop.B)
    (hOut0 : ∀ i, i < n → s (Lc.Aop i) = false)
    (hBcopy : regValRange Lc.B s n = a) (haN : a < N)
    (hSubval : regValRange Lop.Sub s n = b) (hbN : b < N)
    (hNreg : regValRange Lop.Nreg s n = N)
    (hBor : ∀ j, s (Lop.Bor j) = false) (hC : ∀ j, s (Lop.C j) = false) (hanc : s Lop.anc = false)
    (dSubB : ∀ i k, Lop.Sub i ≠ Lc.B k) (dSubAop : ∀ i k, Lop.Sub i ≠ Lc.Aop k)
    (dNregB : ∀ i k, Lop.Nreg i ≠ Lc.B k) (dNregAop : ∀ i k, Lop.Nreg i ≠ Lc.Aop k)
    (dBorB : ∀ j k, Lop.Bor j ≠ Lc.B k) (dBorAop : ∀ j k, Lop.Bor j ≠ Lc.Aop k)
    (dCB : ∀ j k, Lop.C j ≠ Lc.B k) (dCAop : ∀ j k, Lop.C j ≠ Lc.Aop k)
    (dancB : ∀ k, Lop.anc ≠ Lc.B k) (dancAop : ∀ k, Lop.anc ≠ Lc.Aop k) :
    regValRange Lop.B (denote (copyReg Lc ++ modSub Lop) s) n = (a + N - b) % N := by
  set scp := denote (copyReg Lc) s with hscpdef
  rw [denote_append, ← hscpdef]
  have hBscp : regValRange Lop.B scp n = a := by
    rw [← hOutEq, hscpdef, copyReg_correct_operand Lc s hOut0, hBcopy]
  have hSubscp : regValRange Lop.Sub scp n = b := by
    rw [hscpdef, copyReg_preserves_reg Lc s Lop.Sub n dSubB dSubAop, hSubval]
  have hNregscp : regValRange Lop.Nreg scp n = N := by
    rw [hscpdef, copyReg_preserves_reg Lc s Lop.Nreg n dNregB dNregAop, hNreg]
  have hBorscp : ∀ j, scp (Lop.Bor j) = false := fun j => by
    rw [hscpdef, copyReg_preserves s (Lop.Bor j) (dBorB j) (dBorAop j)]; exact hBor j
  have hCscp : ∀ j, scp (Lop.C j) = false := fun j => by
    rw [hscpdef, copyReg_preserves s (Lop.C j) (dCB j) (dCAop j)]; exact hC j
  have hancscp : scp Lop.anc = false := by
    rw [hscpdef, copyReg_preserves s Lop.anc dancB dancAop]; exact hanc
  exact modSub_correct Lop scp hBorscp hCscp hancscp hN hNregscp hBscp hSubscp haN hbN

/-! ## Part 4 — the `M_dbl = 8` exhibited count

The dispatcher emits exactly one `mulLoop` field-multiply gadget per `mul` / `sq` opcode
(`compileInstr_emits_mulLoop`). So the number of `mulLoop` gadgets in the dispatched
`doublingProgram` circuit is the count of `mul` / `sq` opcodes, which is the DERIVED
`mulCount doublingProgram = M_dbl = 8`.

**Honest carve (this is an OPCODE-level count, not a circuit-structural one).** `emitsFieldMul` is a
predicate on `Instr`; the count below is `(filter emitsFieldMul).length` over the program list, i.e.
`mulCount doublingProgram` re-expressed. It is glued to the dispatcher by `compileInstr_emits_mulLoop`
(each `mul`/`sq` branch emits one `mulLoop`) plus the six-branch definition of `compileInstr`. This is
NOT a count over an assembled `Circuit` proven to compute the doubling over `ZMod p` — that full
assembly is the walled STEP 3 (see the module carve line). So `M_dbl = 8` here is "the dispatcher
emits 8 field-multiply gadgets", not "the verified doubling circuit uses 8 field multiplies". -/

/-- The opcodes the dispatcher compiles to a `mulLoop` field-multiply gadget: `mul` and `sq`. -/
def emitsFieldMul : Instr → Bool
  | .mul _ _ => true
  | .sq _    => true
  | _        => false

/-- For a field-multiply opcode the dispatcher emits exactly the single `mulLoop` gadget. -/
theorem compileInstr_emits_mulLoop (G : StepGadgets m n) (instr : Instr)
    (h : emitsFieldMul instr = true) :
    compileInstr G instr = mulLoop G.mulLayout := by
  cases instr with
  | mul i j => rfl
  | sq i => rfl
  | add i j => simp only [emitsFieldMul] at h; exact absurd h Bool.false_ne_true
  | sub i j => simp only [emitsFieldMul] at h; exact absurd h Bool.false_ne_true
  | nsmul c i => simp only [emitsFieldMul] at h; exact absurd h Bool.false_ne_true
  | neg i => simp only [emitsFieldMul] at h; exact absurd h Bool.false_ne_true

/-- **The dispatched field-multiply gadget count equals the DERIVED `mulCount`.** The number of
`mulLoop` gadgets the dispatcher emits over a program is the count of its `mul` / `sq` opcodes, which is
exactly `mulCount` (the value the ECDLP estimate calls `M`). -/
theorem mulLoopEmissions_eq_mulCount (prog : Program) :
    (prog.filter emitsFieldMul).length = mulCount prog := by
  induction prog with
  | nil => rfl
  | cons a rest ih =>
    cases a <;> simp [emitsFieldMul, mulCount, ih] <;> omega

/-- **The `M_dbl = 8` exhibited count.** The number of `mulLoop` field-multiply gadgets the dispatcher
emits for `doublingProgram` is the DERIVED count `M_dbl` (`= mulCount doublingProgram`). With the
dispatcher exhibited, `M = M_dbl` is now a property of an exhibited circuit's gadget list, not a free
parameter. -/
theorem doubling_mulLoop_emissions :
    (doublingProgram.filter emitsFieldMul).length = M_dbl :=
  mulLoopEmissions_eq_mulCount doublingProgram

/-- The exhibited `mulLoop`-gadget count for the secp256k1 `a = 0` doubling is `8`. -/
theorem doubling_mulLoop_emissions_eq_8 :
    (doublingProgram.filter emitsFieldMul).length = 8 := by
  rw [doubling_mulLoop_emissions]; exact M_dbl_eq

/-! ### Worked `#eval` cross-checks of the dispatch paths

The `mul` and `nsmul` dispatch paths, exercised on the verified standalone witnesses. By
`compileInstr_mul` the circuit `compileInstr G (.mul i j)` IS `mulLoop G.mulLayout`; the `#eval` below
runs `mulLoop wMulLoop` (`= compileInstr _ (.mul 0 1)` for any bundle with `mulLayout = wMulLoop`) on
the verified `wState`, reading `X · Y mod 3`. Likewise `compileInstr_nsmul` routes `.nsmul c i` to
`constMulCirc (G.nsmulLayout c)`; the `#eval` runs `constMulCirc constMulLayout2` (`= 3 · aval mod 5`).

A single ambient `Fin m` bundle over all six opcodes is the assembly the wall blocks (see the carve
line); these `#eval`s exercise the dispatcher's *emitted gadgets* (the RHS of the dispatch equations)
on the verified per-gadget witnesses. -/

-- `mul` path: `compileInstr _ (.mul 0 1) = mulLoop wMulLoop`; `X = 4, Y = 2, N = 3 ↦ 8 mod 3 = 2`.
#eval regValRangeArr wMulLoop.B
  (runArr (mulLoop wMulLoop) (ofState (wState false true false false false true))) 3
-- 2

-- `nsmul` path: `compileInstr _ (.nsmul 3 0) = constMulCirc constMulLayout2`; `3 · 2 mod 5 = 1`.
#eval regValRangeArr constMulLayout2.B
  (runArr (constMulCirc constMulLayout2) (ofState (constMulState false true false))) 4
-- 1

/-- The `mul`-path `#eval` is the genuine `denote` semantics of the dispatched gadget: by
`regValRangeArr_eq`, the fast `Array` read equals `regValRange (denote (mulLoop wMulLoop) …)`, and
`mulLoop wMulLoop = compileInstr G (.mul 0 1)` for any `G` with `G.mulLayout = wMulLoop`
(`compileInstr_mul`). -/
example : regValRangeArr wMulLoop.B
    (runArr (mulLoop wMulLoop) (ofState (wState false true false false false true))) 3
      = regValRange wMulLoop.B
        (denote (mulLoop wMulLoop) (wState false true false false false true)) 3 :=
  regValRangeArr_eq wMulLoop.B (mulLoop wMulLoop) (wState false true false false false true) 3

end Reversible
