import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularConst
import CsdLean4.Mathlib.QuantumInfo.ECDLP.PointDouble
import Mathlib.Data.ZMod.Basic

/-!
# SLP → circuit router infrastructure (STEP 1)  (ECDLP Phase 2, Stage S6.3e-2b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module is **STEP 1 of the SLP → circuit router**: the reusable register-block layout schema, the
`ℕ`-`% p` ↔ `ZMod p`-`.val` arithmetic bridge for every field opcode, the abstract SSA register-file
fold that threads the invariant *"block `k` holds `(fₖ : ZMod p).val`"* across a compiled program, and
ONE worked, harness-cross-checked instance.

The straight-line program model is `ECDLP.Program` (`PointDouble.lean`): an SSA register file
(`runProgram` appends each opcode's output) over a `CommRing R`. The router compiles a program over
`R := ZMod p` (reduction modulus `N := p`) into a `Reversible.Circuit m` built from the verified
field-op gadgets one tranche below (`modAdd` / `modSub` / `mulLoop` / `modConstMul` / `modNeg`).

## What STEP 1 proves (this file)

* **`RegBlockLayout`** — the scalable register-block schema: program register `k`, bit `i` ↦ wire
  `block k i : Fin m`. Inhabitability at scale is the theorem `contigBlock_injOn`: the contiguous
  stride assignment `block k i = k·n + i` is injective on `[0, numRegs) × [0, n)` whenever
  `numRegs · n ≤ m`, for **every** register count `numRegs` (the audit-flagged scaling axis — many
  opcodes sharing one ambient `Fin m` stay disjoint).
* **The `ZMod p` bridge** (`add_bridge`, `mul_bridge`, `nsmul_bridge`, `neg_bridge`, `sub_bridge`):
  each verified gadget's `% p` `ℕ`-arithmetic output equals the `.val` of the corresponding `ZMod p`
  field operation, connecting the bit-level `mod N` semantics of the gadgets to the field semantics
  `evalProgram (ZMod p)`. Most are thin restatements of Mathlib (`add`/`mul` are `.symm` of
  `ZMod.val_add`/`val_mul`; `neg` aliases `ZMod.neg_val'`); the genuinely new one is `sub_bridge`,
  whose truncation-safe `(x.val + p − y.val) % p` form handles wraparound, unlike Mathlib's
  `ZMod.val_sub` (which assumes `y.val ≤ x.val`).
* **`router_holds` / `compile_correct`** — the abstract SSA fold: given per-step value+frame
  guarantees (`hstep`) and self-precondition preservation (`hpre0` / `hpre_frame`), the compiled
  prefix maintains the register-file invariant, so the final block holds
  `(evalProgram (ZMod p) inputs prog out).val`. The fold is opcode-agnostic and reusable for the full
  dispatcher.
* **Worked instance** (`worked_*`): the 2-step program `[.neg 0, .neg 1]` over `ZMod 5`, with a
  concrete `RegBlockLayout 40 3` and two `modNeg` gadgets sharing the ambient `Fin 40` on disjoint
  fresh ancilla banks. Every fold hypothesis is discharged from the verified gadgets; the headline
  `compile_correct` fires, landing on `(evalProgram (ZMod 5) [3] [.neg 0, .neg 1] 2).val = 3`. A
  `runArr` / `regValRangeArr` `#eval` cross-check (certified equal to the `denote` value by
  `regValRangeArr_eq`) confirms it end-to-end.

## Carve line: STEP 1 vs STEP 2

STEP 1 builds the **router skeleton + bridge + abstract fold + a worked multi-gadget instance** and
exhibits inhabitability at scale. It does **not** build the full per-opcode dispatcher nor the
secp256k1 doubling assembly. Deferred to **STEP 2**:

1. The `compileInstr : Instr → … → Circuit m` dispatcher emitting the gadget for *each* of the six
   opcodes (including `copyReg`-wrapping for the in-place `add` / `sub` — their `B` register is
   overwritten, so SSA-fresh output needs a `copyReg` of a source into the fresh block first;
   `nsmul` / `neg` / `mul` / `sq` are `copyReg`-free, their accumulator starting at `0`).
2. The full `doublingProgram` (≈20 registers, `M_dbl = 8` exhibited as a router count) assembled and
   run through `compile_correct`.

**Named residue (unchanged from the gadget tranche):** the per-step fresh-ancilla banks leave dirty
carries / borrow flags (`Θ(n²)` qubits per multiply); in-place reuse needs the **carry-clean /
ancilla-restoring** adder the corpus does NOT yet provide. STEP 1's worked instance uses only the
`copyReg`-free `modNeg` gadget, so the only "real-gadget routing" exercised here is `neg`; the bridge
lemmas, however, cover all six opcodes.
-/

namespace Reversible

open ECDLP

variable {m n : ℕ}

/-! ## Part 0 — SSA register-file helpers (over a `CommRing`)

`runProgram` appends each opcode's output, so a register index below the current file length is stable
under further appends. These purely structural lemmas let the router's base case read the inputs and
let the headline read off `evalProgram`. -/

/-- A register index below the prefix length reads the same after appending more registers. -/
theorem regGet_append_left {R : Type*} [CommRing R] (L M : List R) :
    ∀ i, i < L.length → regGet (L ++ M) i = regGet L i := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ j =>
      show regGet (xs ++ M) j = regGet xs j
      exact ih j (by simpa using hi)

/-- `runProgram` over a concatenation is sequential. -/
theorem runProgram_append {R : Type*} [CommRing R] (regs : List R) :
    ∀ (p1 p2 : Program), runProgram regs (p1 ++ p2) = runProgram (runProgram regs p1) p2 := by
  intro p1
  induction p1 generalizing regs with
  | nil => intro p2; rfl
  | cons a rest ih => intro p2; simp only [List.cons_append, runProgram]; exact ih _ p2

/-- The register file grows by exactly the program length. -/
theorem runProgram_length {R : Type*} [CommRing R] (regs : List R) :
    ∀ prog : Program, (runProgram regs prog).length = regs.length + prog.length := by
  intro prog
  induction prog generalizing regs with
  | nil => simp [runProgram]
  | cons a rest ih => simp only [runProgram]; rw [ih]; simp [List.length_append]; omega

/-- An input register reads its input value regardless of the program appended after it. -/
theorem regGet_runProgram_of_lt {R : Type*} [CommRing R] (inputs : List R) :
    ∀ (prog : Program) (i : ℕ), i < inputs.length →
      regGet (runProgram inputs prog) i = regGet inputs i := by
  intro prog
  induction prog generalizing inputs with
  | nil => intro i _; rfl
  | cons a rest ih =>
    intro i hi
    show regGet (runProgram (inputs ++ [evalInstr inputs a]) rest) i = regGet inputs i
    rw [ih (inputs ++ [evalInstr inputs a]) i (by rw [List.length_append]; omega)]
    exact regGet_append_left inputs [evalInstr inputs a] i hi

/-! ## Part 1 — the `ℕ`-`% p` ↔ `ZMod p`-`.val` bridge

The verified gadgets compute `(… ) % N` over `ℕ` bit registers (`N := p`); `evalProgram (ZMod p)`
computes the field operation. These lemmas are the hinge: the gadget's `ℕ` output is the `.val` of the
field result. Each is general (every `p` with `NeZero p`, every `ZMod p` operand). -/

variable {p : ℕ}

/-- Additive inverse, `.val` form: `(-y).val = (p - y.val) % p`. This is Mathlib's `ZMod.neg_val'`
(stated with the operands in this order); kept as a named local alias since `neg_bridge`/`sub_bridge`
both consume it. -/
theorem zmod_neg_val [NeZero p] (y : ZMod p) : (-y).val = (p - y.val) % p := ZMod.neg_val' y

/-- The add gadget bridge: `(x.val + y.val) % p = (x + y).val`. A `.symm` of `ZMod.val_add`. -/
theorem add_bridge [NeZero p] (x y : ZMod p) : (x.val + y.val) % p = (x + y).val :=
  (ZMod.val_add x y).symm

/-- The multiply gadget bridge: `(x.val * y.val) % p = (x * y).val`. A `.symm` of `ZMod.val_mul`
(which needs no `NeZero`). -/
theorem mul_bridge (x y : ZMod p) : (x.val * y.val) % p = (x * y).val :=
  (ZMod.val_mul x y).symm

/-- The constant-multiply gadget bridge: `(c * x.val) % p = ((c : ZMod p) * x).val` for a classical
constant `c : ℕ` (`evalInstr`'s `.nsmul c i` is `(c : R) * regGet`). -/
theorem nsmul_bridge [NeZero p] (c : ℕ) (x : ZMod p) :
    (c * x.val) % p = ((c : ZMod p) * x).val := by
  rw [ZMod.val_mul, ZMod.val_natCast]
  conv_lhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt (ZMod.val_lt x)]

/-- The negation gadget bridge: `(p - y.val) % p = (-y).val`. -/
theorem neg_bridge [NeZero p] (y : ZMod p) : (p - y.val) % p = (-y).val :=
  (zmod_neg_val y).symm

/-- The subtract gadget bridge: `(x.val + p - y.val) % p = (x - y).val` (the gadget produces
`(a + N − b) % N`, the truncation-safe form). -/
theorem sub_bridge [NeZero p] (x y : ZMod p) : (x.val + p - y.val) % p = (x - y).val := by
  have hy : y.val < p := ZMod.val_lt y
  rw [sub_eq_add_neg, ZMod.val_add, zmod_neg_val]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  congr 1
  omega

/-! ## Part 2 — the modular-subtraction external frame (a new gadget frame lemma)

`modSub`/`modNeg` lacked a full "preserves every external wire" frame lemma (only the subtrahend was
covered). The router's SSA fold needs it: a `modNeg` step must leave every *other* register block (and
every *other* step's fresh ancilla bank) untouched. Composed from the existing borrow-step frame
(`rippleSub_subStep_preserves`) and the controlled-add frame (`cRippleCirc_preserves_external`). -/

/-- **`modSub` frame.** A wire `w` disjoint from every `modSub`-touched family
(`B, Sub, Bor, Nreg, C, anc`) is left unchanged by `modSub L`. -/
theorem modSub_preserves_external (L : ModSubLayout m n) (s : State m) (w : Fin m)
    (hB : ∀ j, w ≠ L.B j) (hSub : ∀ j, w ≠ L.Sub j) (hBor : ∀ j, w ≠ L.Bor j)
    (hNreg : ∀ j, w ≠ L.Nreg j) (hC : ∀ j, w ≠ L.C j) (hanc : w ≠ L.anc) :
    denote (modSub L) s w = s w := by
  rw [modSub, denote_append]
  rw [cRippleCirc_preserves_external L.fixStep (denote (rippleSub L.subStep) s) w
    (hBor n) hanc (fun k _ => hNreg k) (fun k _ => hB k) (fun k _ => hC k)]
  exact rippleSub_subStep_preserves (L := L) s w hB hSub hBor

/-- **`modNeg` register-block frame.** `modNeg L` preserves the value of a register `f` whose wires
are disjoint from every `modSub`-touched family. The fold's frame obligation for the *other* blocks. -/
theorem modNeg_preserves_block (L : ModSubLayout m n) (s : State m) (f : ℕ → Fin m) (q : ℕ)
    (hB : ∀ i j, f i ≠ L.B j) (hSub : ∀ i j, f i ≠ L.Sub j) (hBor : ∀ i j, f i ≠ L.Bor j)
    (hNreg : ∀ i j, f i ≠ L.Nreg j) (hC : ∀ i j, f i ≠ L.C j) (hanc : ∀ i, f i ≠ L.anc) :
    regValRange f (denote (modNeg L) s) q = regValRange f s q := by
  apply Finset.sum_congr rfl
  intro i _
  show (denote (modNeg L) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [modNeg, modSub_preserves_external L s (f i)
    (hB i) (hSub i) (hBor i) (hNreg i) (hC i) (hanc i)]

/-! ## Part 3 — the register-block layout schema and the abstract SSA fold -/

/-- A **register-block layout** on `Fin m` for `n`-bit blocks: program register `r`, bit `i` ↦ wire
`block r i`. The fold is agnostic to how blocks are placed; inhabitability/disjointness at scale is the
separate theorem `contigBlock_injOn`. -/
structure RegBlockLayout (m n : ℕ) where
  /-- Register `r`, bit `i` ↦ wire. -/
  block : ℕ → ℕ → Fin m

/-- The value held in register block `r` of the layout, read off the low `n` bits as an `ℕ`. -/
def RegBlockLayout.valOf (L : RegBlockLayout m n) (s : State m) (r : ℕ) : ℕ :=
  regValRange (L.block r) s n

/-- The contiguous stride placement: register `r`, bit `i` ↦ wire `(r·n + i) mod m`. The canonical
inhabitant of `RegBlockLayout` (the `mod m` is inert on the in-range indices `r·n + i < m`). -/
def contigBlock (m n : ℕ) (hm : 0 < m) : ℕ → ℕ → Fin m :=
  fun r i => ⟨(r * n + i) % m, Nat.mod_lt _ hm⟩

/-- **Inhabitability at scale (the audit-flagged property).** The contiguous stride placement is
injective on `[0, numRegs) × [0, n)` whenever `numRegs · n ≤ m`, for **every** register count
`numRegs`. So arbitrarily many opcodes' blocks share one ambient `Fin m` without collision — the
`Θ(·)`-fresh-bank schema does not silently become uninhabitable as the program grows. -/
theorem contigBlock_injOn (hn : 0 < n) {numRegs : ℕ} (hm : numRegs * n ≤ m) (hm0 : 0 < m)
    {r r' i i' : ℕ} (hr : r < numRegs) (hr' : r' < numRegs) (hi : i < n) (hi' : i' < n)
    (h : contigBlock m n hm0 r i = contigBlock m n hm0 r' i') : r = r' ∧ i = i' := by
  have hb : r * n + i < m := by
    have h1 : r * n + i < (r + 1) * n := by rw [Nat.succ_mul]; omega
    have h2 : (r + 1) * n ≤ numRegs * n := by gcongr; omega
    omega
  have hb' : r' * n + i' < m := by
    have h1 : r' * n + i' < (r' + 1) * n := by rw [Nat.succ_mul]; omega
    have h2 : (r' + 1) * n ≤ numRegs * n := by gcongr; omega
    omega
  rw [contigBlock, contigBlock, Fin.mk.injEq,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h
  -- r·n + i = r'·n + i' with i,i' < n ⇒ r = r', i = i'
  have hmod_i : (r * n + i) % n = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have hmod_i' : (r' * n + i') % n = i' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
  have hi_eq : i = i' := by rw [← hmod_i, ← hmod_i', h]
  refine ⟨?_, hi_eq⟩
  have hrn : r * n = r' * n := by omega
  exact Nat.eq_of_mul_eq_mul_right hn hrn

/-- The compiled prefix: the first `k` step circuits concatenated (the induction handle for the fold). -/
def routerUpto (step : ℕ → Circuit m) (k : ℕ) : Circuit m :=
  (List.range k).flatMap step

@[simp] theorem routerUpto_zero (step : ℕ → Circuit m) : routerUpto step 0 = [] := rfl

theorem routerUpto_succ (step : ℕ → Circuit m) (k : ℕ) :
    routerUpto step (k + 1) = routerUpto step k ++ step k := by
  simp [routerUpto, List.range_succ, List.flatMap_append]

/-- The full compiled circuit for a `len`-step program. -/
def compile (step : ℕ → Circuit m) (len : ℕ) : Circuit m := routerUpto step len

/-- **Self-precondition transport.** Each step `t`'s non-source preconditions (`selfPre t`, e.g. clean
ancilla / fresh-zero output block / constant presets) survive every *earlier* step, hence the prefix:
`selfPre t (denote (routerUpto step k) s0)` for `k ≤ t`. -/
theorem selfPre_routerUpto (step : ℕ → Circuit m) (selfPre : ℕ → State m → Prop)
    (len : ℕ) (s0 : State m)
    (hpre0 : ∀ t, t < len → selfPre t s0)
    (hpre_frame : ∀ t t', t' < t → t < len → ∀ s, selfPre t s → selfPre t (denote (step t') s)) :
    ∀ t, t < len → ∀ k, k ≤ t → selfPre t (denote (routerUpto step k) s0) := by
  intro t ht k
  induction k with
  | zero => intro _; simpa using hpre0 t ht
  | succ k ih =>
    intro hk
    rw [routerUpto_succ, denote_append]
    exact hpre_frame t k (by omega) ht _ (ih (by omega))

/-- **The abstract SSA register-file fold.** Given:
* `hbase` — the input blocks `[0, numInputs)` hold their `ZMod p` values at `s0`;
* `hpre0` / `hpre_frame` — each step's self-preconditions hold at `s0` and survive earlier steps;
* `hstep` — running step `t` from a state where blocks `[0, numInputs+t)` are correct and `selfPre t`
  holds extends correctness to block `numInputs+t` (value) while preserving the earlier blocks (frame),
then after the first `k` steps the register-file invariant holds up to block `numInputs + k`. -/
theorem router_holds (L : RegBlockLayout m n) (vals : ℕ → ZMod p)
    (step : ℕ → Circuit m) (selfPre : ℕ → State m → Prop)
    (numInputs len : ℕ) (s0 : State m)
    (hbase : ∀ r, r < numInputs → L.valOf s0 r = (vals r).val)
    (hpre0 : ∀ t, t < len → selfPre t s0)
    (hpre_frame : ∀ t t', t' < t → t < len → ∀ s, selfPre t s → selfPre t (denote (step t') s))
    (hstep : ∀ t, t < len → ∀ s, (∀ r, r < numInputs + t → L.valOf s r = (vals r).val) →
      selfPre t s → ∀ r, r < numInputs + t + 1 →
        L.valOf (denote (step t) s) r = (vals r).val) :
    ∀ k, k ≤ len → ∀ r, r < numInputs + k →
      L.valOf (denote (routerUpto step k) s0) r = (vals r).val := by
  intro k
  induction k with
  | zero => intro _ r hr; simpa using hbase r (by omega)
  | succ k ih =>
    intro hk r hr
    have hkl : k < len := by omega
    have ihk := ih (by omega)
    have hsp : selfPre k (denote (routerUpto step k) s0) :=
      selfPre_routerUpto step selfPre len s0 hpre0 hpre_frame k hkl k (le_refl k)
    rw [routerUpto_succ, denote_append]
    exact hstep k hkl _ ihk hsp r (by omega)

/-- **Router correctness headline.** Under the abstract fold hypotheses, with `vals` the `ZMod p`
register file `regGet (runProgram inputs prog)`, the compiled circuit leaves the output block holding
`(evalProgram inputs prog out).val` for every `out < numInputs + prog.length`. -/
theorem compile_correct (L : RegBlockLayout m n) [NeZero p]
    (inputs : List (ZMod p)) (prog : Program)
    (step : ℕ → Circuit m) (selfPre : ℕ → State m → Prop) (s0 : State m)
    (hbase : ∀ r, r < inputs.length →
      L.valOf s0 r = (regGet (runProgram inputs prog) r).val)
    (hpre0 : ∀ t, t < prog.length → selfPre t s0)
    (hpre_frame : ∀ t t', t' < t → t < prog.length →
      ∀ s, selfPre t s → selfPre t (denote (step t') s))
    (hstep : ∀ t, t < prog.length → ∀ s,
      (∀ r, r < inputs.length + t → L.valOf s r = (regGet (runProgram inputs prog) r).val) →
      selfPre t s → ∀ r, r < inputs.length + t + 1 →
        L.valOf (denote (step t) s) r = (regGet (runProgram inputs prog) r).val)
    (out : ℕ) (hout : out < inputs.length + prog.length) :
    L.valOf (denote (compile step prog.length) s0) out = (evalProgram inputs prog out).val := by
  rw [compile, evalProgram]
  exact router_holds L (regGet (runProgram inputs prog)) step selfPre inputs.length prog.length s0
    hbase hpre0 hpre_frame hstep prog.length (le_refl _) out hout

/-! ## Part 4 — worked instance: `[.neg 0, .neg 1]` over `ZMod 5`

A genuine 2-step routed program on a single ambient `Fin 40`, with two `modNeg` gadgets on **disjoint
fresh ancilla banks** (directly exercising the audit-flagged multi-gadget shared-`Fin m`
inhabitability). Inputs `[3]`; the program computes `reg1 = -reg0`, `reg2 = -reg1`, so
`evalProgram [3] [.neg 0, .neg 1] 2 = 3`. Block layout (`n = 3` bits, `N := p = 5`):
* register blocks `block r` = wires `[3r, 3r+3)` (`r = 0,1,2`): wires `0..8`;
* step 0 private bank: `Bor 9..12`, `C 13..16`, `Nreg 17..19 (= 5)`, `anc 20`;
* step 1 private bank: `Bor 21..24`, `C 25..28`, `Nreg 29..31 (= 5)`, `anc 32`. -/

/-- The worked register-block layout on `Fin 40`, `n = 3`: register `r`, bit `i` ↦ wire `3r + i`
(the contiguous stride, written in the `min _ 39` form the gadget layouts also use, so the gadgets'
`B` / `Sub` registers are definitionally these blocks). -/
def wLayout : RegBlockLayout 40 3 := ⟨fun r i => ⟨min (3 * r + i) 39, by omega⟩⟩

/-- Step `t`'s `modNeg` (`= modSub`) layout: minuend `B = block (t+1)` (the fresh output, init `0`),
subtrahend `Sub = block t` (the source), and a private bank at base `9 + 12t`. -/
def negStepLayout (t : ℕ) (hlt : 9 + 12 * t + 12 ≤ 40) : ModSubLayout 40 3 where
  B i := ⟨3 * (t + 1) + min i 2, by omega⟩
  Sub i := ⟨3 * t + min i 2, by omega⟩
  Bor i := ⟨9 + 12 * t + min i 3, by omega⟩
  Nreg i := ⟨17 + 12 * t + min i 2, by omega⟩
  C i := ⟨13 + 12 * t + min i 3, by omega⟩
  anc := ⟨20 + 12 * t, by omega⟩
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

/-- The two worked-instance steps (`t ≥ 2` is unused; falls back to step 1). -/
def wStepLayout (t : ℕ) : ModSubLayout 40 3 :=
  if t = 0 then negStepLayout 0 (by norm_num) else negStepLayout 1 (by norm_num)

theorem wStepLayout_zero : wStepLayout 0 = negStepLayout 0 (by norm_num) := rfl

theorem wStepLayout_one : wStepLayout 1 = negStepLayout 1 (by norm_num) := rfl

/-- The compiled step circuit for SSA position `t`: `modNeg` on `wStepLayout t`. -/
def wStep (t : ℕ) : Circuit 40 := modNeg (wStepLayout t)

/-- Step `t`'s self-precondition: fresh-zero output block, clean borrow/fix-carry/ancilla, `Nreg = 5`. -/
def wSelfPre (t : ℕ) (s : State 40) : Prop :=
  regValRange (wStepLayout t).B s 3 = 0
    ∧ (∀ j, s ((wStepLayout t).Bor j) = false)
    ∧ (∀ j, s ((wStepLayout t).C j) = false)
    ∧ s (wStepLayout t).anc = false
    ∧ regValRange (wStepLayout t).Nreg s 3 = 5

/-- The worked program and inputs. -/
def wProg : Program := [Instr.neg 0, Instr.neg 1]

/-- The worked initial state on `Fin 40`: input block `block 0 = 3`, both `Nreg` banks preset to `5`,
everything else `false`. -/
def rtState : State 40 := fun w =>
  decide (w.val = 0 ∨ w.val = 1 ∨ w.val = 17 ∨ w.val = 19 ∨ w.val = 29 ∨ w.val = 31)

/-- The `ZMod 5` register file of the worked program: `[3, -3, 3]` (i.e. `[3, 2, 3]`). -/
theorem wRunProgram :
    runProgram ([(3 : ZMod 5)]) wProg = [(3 : ZMod 5), -3, 3] := by
  show runProgram [(3 : ZMod 5)] [Instr.neg 0, Instr.neg 1] = _
  simp only [runProgram, evalInstr, regGet, List.cons_append, List.nil_append, neg_neg]

/-! ### Worked-instance discharge

Each `wStepLayout t` is a concrete `ModSubLayout 40 3` (`negStepLayout 0` / `negStepLayout 1`) with
footprint `vals` in `[3t, 3t+5] ∪ [9+12t, 20+12t]`. The two banks are disjoint, sharing only the
register blocks they read/write — exactly the multi-gadget-on-one-`Fin m` configuration the audit flags.
The preservation helper `negStep_preserves` discharges every frame obligation by `omega` on those
ranges. -/

/-- A wire outside `negStepLayout t`'s footprint survives the `modNeg` step. The frame workhorse. -/
theorem negStep_preserves (t : ℕ) (htlt : 9 + 12 * t + 12 ≤ 40) (s : State 40) (w : Fin 40)
    (hw1 : w.val < 3 * t ∨ 3 * t + 5 < w.val)
    (hw2 : w.val < 9 + 12 * t ∨ 20 + 12 * t < w.val) :
    denote (modNeg (negStepLayout t htlt)) s w = s w := by
  rw [modNeg]
  apply modSub_preserves_external
  · intro j; rw [ne_eq, Fin.ext_iff]; simp only [negStepLayout]; omega
  · intro j; rw [ne_eq, Fin.ext_iff]; simp only [negStepLayout]; omega
  · intro j; rw [ne_eq, Fin.ext_iff]; simp only [negStepLayout]; omega
  · intro j; rw [ne_eq, Fin.ext_iff]; simp only [negStepLayout]; omega
  · intro j; rw [ne_eq, Fin.ext_iff]; simp only [negStepLayout]; omega
  · rw [ne_eq, Fin.ext_iff]; simp only [negStepLayout]; omega

/-- Register-value form of `negStep_preserves` over the low 3 bits. -/
theorem regValRange_negStep_preserved (t : ℕ) (htlt : 9 + 12 * t + 12 ≤ 40) (s : State 40)
    (f : ℕ → Fin 40)
    (hf1 : ∀ i, i < 3 → (f i).val < 3 * t ∨ 3 * t + 5 < (f i).val)
    (hf2 : ∀ i, i < 3 → (f i).val < 9 + 12 * t ∨ 20 + 12 * t < (f i).val) :
    regValRange f (denote (modNeg (negStepLayout t htlt)) s) 3 = regValRange f s 3 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  show (denote (modNeg (negStepLayout t htlt)) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
  rw [negStep_preserves t htlt s (f i) (hf1 i hi) (hf2 i hi)]

/-- The register block `r` and a gadget register `f` that agree on `.val` over `[0, 3)` carry the same
value (the `min (3r+i) 39` block form vs the `base + min i w` gadget form coincide in range). -/
theorem valOf_eq_regValRange (f : ℕ → Fin 40) (s : State 40) (r : ℕ)
    (h : ∀ i, i < 3 → (wLayout.block r i).val = (f i).val) :
    wLayout.valOf s r = regValRange f s 3 := by
  simp only [RegBlockLayout.valOf, regValRange]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Fin.ext (h i hi)]

/-- The `ZMod 5` register file's per-step recurrence: `vals (t+1) = - vals t` for the two steps. -/
theorem wStep_neg (t : ℕ) (ht : t < 2) :
    regGet (runProgram [(3 : ZMod 5)] wProg) (1 + t)
      = - regGet (runProgram [(3 : ZMod 5)] wProg) t := by
  rw [wRunProgram]
  interval_cases t <;> rfl

/-- **Base case**: the input block holds its value at `rtState`. -/
theorem worked_hbase : ∀ r, r < ([(3 : ZMod 5)]).length →
    wLayout.valOf rtState r = (regGet (runProgram [(3 : ZMod 5)] wProg) r).val := by
  intro r hr
  have hr1 : r < 1 := hr
  interval_cases r
  rw [wRunProgram]
  show regValRange (wLayout.block 0) rtState 3 = ((3 : ZMod 5)).val
  simp only [wLayout, rtState, regValRange, Finset.sum_range_succ,
    Finset.sum_range_zero]
  decide

/-- `rtState` is `false` on any wire whose value avoids the six set bits `{0,1,17,19,29,31}`. -/
theorem rtState_false {w : Fin 40} (h0 : w.val ≠ 0) (h1 : w.val ≠ 1) (h17 : w.val ≠ 17)
    (h19 : w.val ≠ 19) (h29 : w.val ≠ 29) (h31 : w.val ≠ 31) : rtState w = false := by
  simp only [rtState, decide_eq_false_iff_not]
  omega

/-- A `negStepLayout`-bank's `Bor`/`C`/`anc` wires are `false` at `rtState` (they avoid the set bits). -/
theorem worked_clean (t : ℕ) (htlt : 9 + 12 * t + 12 ≤ 40) :
    (∀ j, rtState ((negStepLayout t htlt).Bor j) = false)
      ∧ (∀ j, rtState ((negStepLayout t htlt).C j) = false)
      ∧ rtState (negStepLayout t htlt).anc = false := by
  refine ⟨fun j => rtState_false ?_ ?_ ?_ ?_ ?_ ?_, fun j => rtState_false ?_ ?_ ?_ ?_ ?_ ?_,
    rtState_false ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
    (simp only [negStepLayout]; omega)

theorem worked_hpre0 : ∀ t, t < wProg.length → wSelfPre t rtState := by
  intro t ht
  have ht2 : t < 2 := by simpa [wProg] using ht
  interval_cases t
  · obtain ⟨hBor, hC, hanc⟩ := worked_clean 0 (by norm_num)
    refine ⟨?_, hBor, hC, hanc, ?_⟩ <;>
      simp only [wStepLayout_zero, negStepLayout, regValRange, Finset.sum_range_succ,
        Finset.sum_range_zero] <;> decide
  · obtain ⟨hBor, hC, hanc⟩ := worked_clean 1 (by norm_num)
    refine ⟨?_, hBor, hC, hanc, ?_⟩ <;>
      simp only [wStepLayout_one, negStepLayout, regValRange, Finset.sum_range_succ,
        Finset.sum_range_zero] <;> decide

/-- **Self-preconditions survive earlier steps.** Only `t = 1`, `t' = 0` is non-vacuous: step 0's
footprint `[0,5] ∪ [9,20]` is disjoint from step 1's self-precondition wires (`{6,7,8} ∪ [21,32]`). -/
theorem worked_hpre_frame : ∀ t t', t' < t → t < wProg.length →
    ∀ s, wSelfPre t s → wSelfPre t (denote (wStep t') s) := by
  intro t t' ht't ht s hsp
  have ht2 : t < 2 := by simpa [wProg] using ht
  interval_cases t <;> interval_cases t'
  -- t = 1, t' = 0
  simp only [wSelfPre, wStepLayout_one] at hsp ⊢
  obtain ⟨hB0, hBor, hC, hanc, hNreg⟩ := hsp
  rw [wStep, wStepLayout_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [regValRange_negStep_preserved 0 (by norm_num) s (negStepLayout 1 (by norm_num)).B
      (by intro i hi; simp only [negStepLayout]; omega)
      (by intro i hi; simp only [negStepLayout]; omega)]
    exact hB0
  · intro j
    rw [negStep_preserves 0 (by norm_num) s ((negStepLayout 1 (by norm_num)).Bor j)
      (by simp only [negStepLayout]; omega)
      (by simp only [negStepLayout]; omega)]
    exact hBor j
  · intro j
    rw [negStep_preserves 0 (by norm_num) s ((negStepLayout 1 (by norm_num)).C j)
      (by simp only [negStepLayout]; omega)
      (by simp only [negStepLayout]; omega)]
    exact hC j
  · rw [negStep_preserves 0 (by norm_num) s (negStepLayout 1 (by norm_num)).anc
      (by simp only [negStepLayout]; omega)
      (by simp only [negStepLayout]; omega)]
    exact hanc
  · rw [regValRange_negStep_preserved 0 (by norm_num) s (negStepLayout 1 (by norm_num)).Nreg
      (by intro i hi; simp only [negStepLayout]; omega)
      (by intro i hi; simp only [negStepLayout]; omega)]
    exact hNreg

/-- **Per-step transition.** Running step `t` extends the register-file invariant: the output block
holds the `ZMod 5` negation (value, via `modNeg_correct` + `neg_bridge`), and every earlier block is
preserved (subtrahend frame for the source, external frame otherwise). -/
theorem worked_hstep : ∀ t, t < wProg.length → ∀ s : State 40,
    (∀ r, r < ([(3 : ZMod 5)]).length + t →
      wLayout.valOf s r = (regGet (runProgram [(3 : ZMod 5)] wProg) r).val) →
    wSelfPre t s → ∀ r, r < ([(3 : ZMod 5)]).length + t + 1 →
      wLayout.valOf (denote (wStep t) s) r
        = (regGet (runProgram [(3 : ZMod 5)] wProg) r).val := by
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  intro t ht s hHolds hsp r hr
  have ht2 : t < 2 := by simpa [wProg] using ht
  have hlen : ([(3 : ZMod 5)]).length = 1 := rfl
  rw [hlen] at hHolds hr
  interval_cases t
  · -- step 0: out = 1 (= -reg0), source = reg0
    simp only [wSelfPre, wStepLayout_zero] at hsp
    obtain ⟨hB0, hBor, hC, hanc, hNreg⟩ := hsp
    rw [wStep, wStepLayout_zero]
    have hsrc : wLayout.valOf s 0 = (regGet (runProgram [(3 : ZMod 5)] wProg) 0).val :=
      hHolds 0 (by omega)
    have hSubval : regValRange (negStepLayout 0 (by norm_num)).Sub s 3
        = (regGet (runProgram [(3 : ZMod 5)] wProg) 0).val := by
      rw [← valOf_eq_regValRange (negStepLayout 0 (by norm_num)).Sub s 0
        (by intro i hi; simp only [wLayout, negStepLayout]; omega)]
      exact hsrc
    have hval := modNeg_correct (negStepLayout 0 (by norm_num)) s hBor hC hanc
      (by norm_num) (by norm_num) hNreg hB0 hSubval (ZMod.val_lt _)
    have hsubpres : regValRange (negStepLayout 0 (by norm_num)).Sub
        (denote (modNeg (negStepLayout 0 (by norm_num))) s) 3
        = (regGet (runProgram [(3 : ZMod 5)] wProg) 0).val :=
      modSub_preserves_subtrahend (negStepLayout 0 (by norm_num)) s hBor hSubval
    interval_cases r
    · -- r = 0 = source: subtrahend preserved
      rw [valOf_eq_regValRange (negStepLayout 0 (by norm_num)).Sub _ 0
        (by intro i hi; simp only [wLayout, negStepLayout]; omega), hsubpres]
    · -- r = 1 = out: value
      rw [valOf_eq_regValRange (negStepLayout 0 (by norm_num)).B _ 1
        (by intro i hi; simp only [wLayout, negStepLayout]; omega),
        hval, neg_bridge, ← wStep_neg 0 (by norm_num)]
  · -- step 1: out = 2 (= -reg1), source = reg1
    simp only [wSelfPre, wStepLayout_one] at hsp
    obtain ⟨hB0, hBor, hC, hanc, hNreg⟩ := hsp
    rw [wStep, wStepLayout_one]
    have hsrc : wLayout.valOf s 1 = (regGet (runProgram [(3 : ZMod 5)] wProg) 1).val :=
      hHolds 1 (by omega)
    have hSubval : regValRange (negStepLayout 1 (by norm_num)).Sub s 3
        = (regGet (runProgram [(3 : ZMod 5)] wProg) 1).val := by
      rw [← valOf_eq_regValRange (negStepLayout 1 (by norm_num)).Sub s 1
        (by intro i hi; simp only [wLayout, negStepLayout]; omega)]
      exact hsrc
    have hval := modNeg_correct (negStepLayout 1 (by norm_num)) s hBor hC hanc
      (by norm_num) (by norm_num) hNreg hB0 hSubval (ZMod.val_lt _)
    have hsubpres : regValRange (negStepLayout 1 (by norm_num)).Sub
        (denote (modNeg (negStepLayout 1 (by norm_num))) s) 3
        = (regGet (runProgram [(3 : ZMod 5)] wProg) 1).val :=
      modSub_preserves_subtrahend (negStepLayout 1 (by norm_num)) s hBor hSubval
    interval_cases r
    · -- r = 0: other block, preserved by external frame
      rw [valOf_eq_regValRange (wLayout.block 0) _ 0 (fun i _ => rfl),
        regValRange_negStep_preserved 1 (by norm_num) s (wLayout.block 0)
          (by intro i hi; simp only [wLayout]; omega)
          (by intro i hi; simp only [wLayout]; omega),
        ← valOf_eq_regValRange (wLayout.block 0) s 0 (fun i _ => rfl)]
      exact hHolds 0 (by omega)
    · -- r = 1 = source: subtrahend preserved
      rw [valOf_eq_regValRange (negStepLayout 1 (by norm_num)).Sub _ 1
        (by intro i hi; simp only [wLayout, negStepLayout]; omega), hsubpres]
    · -- r = 2 = out: value
      rw [valOf_eq_regValRange (negStepLayout 1 (by norm_num)).B _ 2
        (by intro i hi; simp only [wLayout, negStepLayout]; omega),
        hval, neg_bridge, ← wStep_neg 1 (by norm_num)]

/-- **The worked router headline.** The compiled 2-step circuit for `[.neg 0, .neg 1]` over `ZMod 5`,
run on `rtState`, leaves the output block (register 2) holding
`(evalProgram [3] [.neg 0, .neg 1] 2).val = 3`. Fires the abstract `compile_correct` on the discharged
hypotheses. -/
theorem worked_compile_correct :
    wLayout.valOf (denote (compile wStep wProg.length) rtState) 2
      = (evalProgram [(3 : ZMod 5)] wProg 2).val := by
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  exact compile_correct wLayout [(3 : ZMod 5)] wProg wStep wSelfPre rtState
    worked_hbase worked_hpre0 worked_hpre_frame worked_hstep 2 (by decide)

/-- The output value is `3` (= `evalProgram [3] [.neg 0, .neg 1] 2`, the double negation of `3`). -/
theorem worked_value : wLayout.valOf (denote (compile wStep wProg.length) rtState) 2 = 3 := by
  rw [worked_compile_correct]
  show (evalProgram [(3 : ZMod 5)] wProg 2).val = 3
  rw [evalProgram, wRunProgram]
  decide

/-! ### Harness `#eval` cross-check (`runArr` / `regValRangeArr`, certified by `regValRangeArr_eq`)

The strict `Array Bool` evaluator computes the same `denote` value (`regValRangeArr_eq`) instantly. The
output block (register 2, wires 6/7/8) reads `3`: `neg (neg 3) = 3` over `ZMod 5`. -/

-- The compiled router output, register 2: prints `3`.
#eval regValRangeArr (wLayout.block 2)
  (runArr (compile wStep wProg.length) (ofState rtState)) 3
-- 3

-- Register 1 (the intermediate `-3 = 2`): prints `2`.
#eval regValRangeArr (wLayout.block 1)
  (runArr (compile wStep wProg.length) (ofState rtState)) 3
-- 2

/-- The `#eval` value is the genuine `denote`-based router output: by `regValRangeArr_eq`, the fast
`Array` read of register 2 equals the `regValRange (denote …)` that `worked_value` constrains to `3`. -/
example : regValRangeArr (wLayout.block 2)
    (runArr (compile wStep wProg.length) (ofState rtState)) 3
      = wLayout.valOf (denote (compile wStep wProg.length) rtState) 2 :=
  regValRangeArr_eq (wLayout.block 2) (compile wStep wProg.length) rtState 3

end Reversible
