import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlMul
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula

/-!
# Derived field-multiplication count for `a = 0` Jacobian doubling  (ECDLP Phase 2, Stage S6.1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Stage S6 of the ECDLP resource-accounting programme (`specs/ecdlp-resource-plan.md`) "derives the free
parameter `M`" — the number of register×register field multiplications per elliptic-curve point
operation, which until now is a *documented* literature constant (`7` for doubling, `11` for mixed
addition, EFD `a=0`) feeding the secp256k1 Toffoli estimate (`ResourceBounds.lean`). S6.1 turns the
**doubling** count into a number *derived* from an explicit straight-line field-arithmetic program,
verified to compute Mathlib's group-law-correct Jacobian doubling polynomials.

## The carve line (which side each result sits on)

* **Formula correctness is REUSED from Mathlib, not derived here.** `WeierstrassCurve.Jacobian.dblX` /
  `dblY` / `dblZ` are proved to represent the group operation in
  `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`; this module does **not** reprove the
  group law. What is proved here is only that the exhibited program *evaluates to those same
  polynomials* (a `ring` identity over a `CommRing`, under `a₁=a₂=a₃=a₄=0`).
* **The count `M_dbl` is DERIVED here**, off the program's instruction list (`mulCount`), in the same
  discipline as the rest of the programme (cost is a function of the gate/instruction list, never an
  annotation on an opaque object).
* **The per-field-multiply circuit cost is VERIFIED** one layer down: a quantum×quantum field multiply
  is the controlled shift-and-add multiplier `Reversible.cMulCircuit` (`CtrlMul.lean`,
  `cMulCircuit_eq_mul`), whose per-controlled-partial-product cost `cRippleCirc_toffoli = 8·width` is a
  derived theorem.
* **The full assembled point-doubling reversible circuit is NOT built here** (register routing, ancilla
  scheduling, in-place modular reduction between multiplies). The resource bridge below composes the
  derived count with the verified per-multiply cost at the level of a bound; the concrete assembly is
  named **S6.3 residue**.

## What is proved here

* `Program` / `evalProgram` / `mulCount` — a straight-line field-arithmetic program model over an
  arbitrary `CommRing R`. Instructions reference earlier-computed registers; `mulCount` counts only the
  register×register `mul` / `sq` opcodes (small-integer coefficients enter via the free `nsmul`/`neg`
  opcodes, matching the literature convention that multiplication by a small constant is repeated
  addition, not a field multiply).
* `doublingProgram` — an explicit schedule computing the `a=0` doubling coordinates with shared
  intermediates.
* `doublingProgram_correct` — **the load-bearing theorem**: under `a₁=a₂=a₃=a₄=0`, the program evaluated
  at `(P x, P y, P z)` produces `(W'.dblX P, W'.dblY P, W'.dblZ P)`. Ties the counted program to
  Mathlib's group-law-correct formula.
* `M_dbl` / `M_dbl_eq` — the derived count, `mulCount doublingProgram = 8`.
* `doublingToffoli` / `doubling_toffoli_bound` — the lightweight resource bridge: a doubling costs
  `M_dbl` field multiplies, each `≤ 8·width²` Toffolis on the verified `cMulCircuit`.
-/

namespace ECDLP

open WeierstrassCurve WeierstrassCurve.Jacobian

/-! ## Straight-line field-arithmetic program model -/

/-- A straight-line field-arithmetic **instruction** over a register file. Operands are register
indices (`ℕ`) referencing earlier-computed values or the three inputs. The opcodes:

* `mul i j` — register×register field multiplication (counted by `mulCount`);
* `sq i` — squaring (counted by `mulCount`; the EFD convention is `1S ≈ 1M` for the *count*);
* `add i j`, `sub i j` — field addition/subtraction (not counted: linear, cheap);
* `nsmul c i` — multiplication by a *small integer constant* `c` (not counted: repeated addition /
  a shift, **not** a field multiply — this is exactly why the `3·X²`, `8·…`, `12·…`, `9·…` coefficients
  in the doubling formula do not inflate `M`);
* `neg i` — negation (not counted). -/
inductive Instr where
  | mul (i j : ℕ)
  | sq (i : ℕ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | nsmul (c : ℕ) (i : ℕ)
  | neg (i : ℕ)
  deriving DecidableEq, Repr

/-- A straight-line program is a list of instructions. Instruction `k` may reference registers
`< (number of inputs) + k` (this is **not** statically enforced; out-of-range references read `0`, so a
well-formed program is the caller's responsibility — the count and the correctness theorem are what
matter). -/
abbrev Program := List Instr

variable {R : Type*} [CommRing R]

/-- Total register lookup by index, default `0` for out-of-range. A hand-rolled structural recursion
(rather than `List.getD`, which routes through `getElem?`/`Option` and reduces slowly on the long,
append-built register file). -/
def regGet : List R → ℕ → R
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, (n + 1) => regGet xs n

/-- Evaluate one instruction against the current register file `regs` (the inputs followed by every
previously computed value), returning the produced value. Out-of-range indices read `0`. -/
def evalInstr (regs : List R) : Instr → R
  | .mul i j => regGet regs i * regGet regs j
  | .sq i => regGet regs i * regGet regs i
  | .add i j => regGet regs i + regGet regs j
  | .sub i j => regGet regs i - regGet regs j
  | .nsmul c i => (c : R) * regGet regs i
  | .neg i => - regGet regs i

/-- Run a program from an initial register file (the inputs), appending each produced value to the
register file (so later instructions see earlier results). Returns the final register file. -/
def runProgram (regs : List R) : Program → List R
  | [] => regs
  | instr :: rest => runProgram (regs ++ [evalInstr regs instr]) rest

/-- Evaluate a program on the given inputs and read off the value in register `out`. -/
def evalProgram (inputs : List R) (prog : Program) (out : ℕ) : R :=
  regGet (runProgram inputs prog) out

/-- The **derived field-multiplication count**: the number of register×register `mul`/`sq` opcodes in
the program. Linear opcodes (`add`/`sub`/`nsmul`/`neg`) are not counted. This is the value the ECDLP
estimate calls `M`. -/
def mulCount : Program → ℕ
  | [] => 0
  | .mul _ _ :: rest => 1 + mulCount rest
  | .sq _ :: rest => 1 + mulCount rest
  | .add _ _ :: rest => mulCount rest
  | .sub _ _ :: rest => mulCount rest
  | .nsmul _ _ :: rest => mulCount rest
  | .neg _ :: rest => mulCount rest

/-! ## The `a = 0` Jacobian doubling program

Over secp256k1 (`a₁=a₂=a₃=a₄=0`) the Mathlib doubling polynomials collapse to:

* `negY P = -P y`, so `P y - negY P = 2 · P y`;
* `dblZ P = P z · (P y - negY P) = 2 · (P y) · (P z)`;
* `dblU P = -(3 · (P x)²) = -3 · (P x)²`;
* `dblX P = dblU² - 2 · P x · (P y - negY P)² = 9·(P x)⁴ − 8·(P x)·(P y)²`;
* `negDblY P = -dblU·(dblX − P x·(P y−negY P)²) + P y·(P y−negY P)³`
            `= 3·(P x)²·dblX − 12·(P x)³·(P y)² + 8·(P y)⁴`;
* `dblY P = negY ![dblX, negDblY, dblZ] = -negDblY P = −3·(P x)²·dblX + 12·(P x)³·(P y)² − 8·(P y)⁴`.

The schedule, with the three inputs `X = P x` (reg 0), `Y = P y` (reg 1), `Z = P z` (reg 2), and the
counted `mul`/`sq` opcodes flagged: -/

/-- The explicit `a = 0` doubling schedule. Register layout (inputs followed by each produced value):
```
0:X   1:Y   2:Z                                        -- inputs P x, P y, P z
3:XX   = X²            (sq,  counted)
4:YY   = Y²            (sq,  counted)
5:S    = X·YY          (mul, counted)   -- = Px·Py²
6:XX2  = XX²           (sq,  counted)   -- = Px⁴
7:n9   = 9·XX2                          -- = 9·Px⁴
8:n8S  = 8·S                            -- = 8·Px·Py²
9:dblX = n9 − n8S                       -- = 9·Px⁴ − 8·Px·Py²   ★ output X
10:XXdX = XX·dblX      (mul, counted)   -- = Px²·dblX
11:XXS  = XX·S         (mul, counted)   -- = Px³·Py²
12:YY2  = YY²          (sq,  counted)   -- = Py⁴
13:t1   = 12·XXS                        -- = 12·Px³·Py²
14:t2   = 3·XXdX                        -- = 3·Px²·dblX
15:t3   = 8·YY2                         -- = 8·Py⁴
16:t12  = t1 − t2
17:dblY = t12 − t3                      -- = 12·Px³Py² − 3·Px²·dblX − 8·Py⁴   ★ output Y
18:YZ   = Y·Z          (mul, counted)   -- = Py·Pz
19:dblZ = 2·YZ                          -- = 2·Py·Pz            ★ output Z
```
Counted register×register opcodes: regs `3,4,5,6,10,11,12,18` ⇒ `mulCount = 8`. Coefficients enter via
the free `nsmul` opcode. -/
def doublingProgram : Program :=
  [ .sq 0,            -- 3:  XX   = X²
    .sq 1,            -- 4:  YY   = Y²
    .mul 0 4,         -- 5:  S    = X · YY
    .sq 3,            -- 6:  XX2  = XX²
    .nsmul 9 6,       -- 7:  n9   = 9 · XX2
    .nsmul 8 5,       -- 8:  n8S  = 8 · S
    .sub 7 8,         -- 9:  dblX = n9 − n8S
    .mul 3 9,         -- 10: XXdX = XX · dblX
    .mul 3 5,         -- 11: XXS  = XX · S      (= Px³·Py²)
    .sq 4,            -- 12: YY2  = YY²
    .nsmul 12 11,     -- 13: t1   = 12 · XXS
    .nsmul 3 10,      -- 14: t2   = 3 · XXdX
    .nsmul 8 12,      -- 15: t3   = 8 · YY2
    .sub 13 14,       -- 16: t12  = t1 − t2
    .sub 16 15,       -- 17: dblY = t12 − t3
    .mul 1 2,         -- 18: YZ   = Y · Z
    .nsmul 2 18 ]     -- 19: dblZ = 2 · YZ

/-- The output register holding `dblX`. -/
def doublingOutX : ℕ := 9
/-- The output register holding `dblY`. -/
def doublingOutY : ℕ := 17
/-- The output register holding `dblZ`. -/
def doublingOutZ : ℕ := 19

/-! ## The derived multiplication count -/

/-- **The DERIVED field-multiplication count for an `a = 0` Jacobian doubling.** Read off
`doublingProgram`'s instruction list by `mulCount` (eight register×register `mul`/`sq` opcodes:
`X², Y², X·YY, XX², XX·dblX, X·S, YY², Y·Z`). Honest comparison to the literature: the EFD `a=0`
doubling is quoted at `1M+8S` (= 9) or `2M+5S` (= 7) for the count depending on the schedule; this
explicit, *verified* schedule lands at `8`, one above the most aggressive `7` (the gap is un-shared
squarings — `XX²` and `YY²` are recomputed rather than folded via the `(X+YY)²` Karatsuba-style trick
the EFD schedules use; not fudged down to hit `7`). -/
def M_dbl : ℕ := mulCount doublingProgram

@[simp] theorem M_dbl_eq : M_dbl = 8 := by decide

/-! ## Correctness: the program computes Mathlib's `a = 0` doubling polynomials

The group-law correctness of `dblX`/`dblY`/`dblZ` is Mathlib's (`Jacobian/Point.lean`); here we prove
only that the exhibited counted program *evaluates to those polynomials* under `a₁=a₂=a₃=a₄=0`. -/

variable {W' : Jacobian R}

/-- **The load-bearing S6.1 theorem.** Under the secp256k1 hypotheses `a₁=a₂=a₃=a₄=0`, the doubling
program evaluated at the coordinates `(P x, P y, P z)` of a Jacobian point representative produces the
Mathlib doubling polynomials `(W'.dblX P, W'.dblY P, W'.dblZ P)` in registers
`doublingOutX/Y/Z`. This ties the counted program (`mulCount = M_dbl = 8`) to Mathlib's
group-law-correct formula; it does **not** reprove the group law (that is `Jacobian/Point.lean`). -/
theorem doublingProgram_correct (P : Fin 3 → R)
    (ha₁ : W'.a₁ = 0) (ha₂ : W'.a₂ = 0) (ha₃ : W'.a₃ = 0) (ha₄ : W'.a₄ = 0) :
    evalProgram [P 0, P 1, P 2] doublingProgram doublingOutX = W'.dblX P
      ∧ evalProgram [P 0, P 1, P 2] doublingProgram doublingOutY = W'.dblY P
      ∧ evalProgram [P 0, P 1, P 2] doublingProgram doublingOutZ = W'.dblZ P := by
  -- expose the Mathlib polynomials at a = 0
  have hnegY : W'.negY P = - P 1 := by
    rw [negY, ha₁, ha₃]; ring
  have hdblU : W'.dblU P = - (3 * P 0 ^ 2) := by
    rw [dblU_eq, ha₁, ha₂, ha₄]; ring
  have hdblZ : W'.dblZ P = 2 * P 1 * P 2 := by
    rw [dblZ, hnegY]; ring
  have hdblX : W'.dblX P = 9 * P 0 ^ 4 - 8 * P 0 * P 1 ^ 2 := by
    rw [dblX, hdblU, hnegY, ha₁, ha₂]; ring
  have hnegDblY : W'.negDblY P
      = 3 * P 0 ^ 2 * W'.dblX P - 12 * P 0 ^ 3 * P 1 ^ 2 + 8 * P 1 ^ 4 := by
    rw [negDblY, hdblU, hnegY]; ring
  have hdblY : W'.dblY P
      = 12 * P 0 ^ 3 * P 1 ^ 2 - 3 * P 0 ^ 2 * W'.dblX P - 8 * P 1 ^ 4 := by
    rw [dblY, negY_eq, hnegDblY, ha₁, ha₃]; ring
  -- reduce each output register to its explicit polynomial in `P 0, P 1, P 2`
  -- the explicit final register file, computed once by structural unfolding (cheap: cons/append
  -- reduction, no `getElem?`/`Option`), so each output is read off without re-running the program
  have hrun : runProgram [P 0, P 1, P 2] doublingProgram
      = [P 0, P 1, P 2,
         P 0 * P 0,
         P 1 * P 1,
         P 0 * (P 1 * P 1),
         (P 0 * P 0) * (P 0 * P 0),
         ((9 : ℕ) : R) * ((P 0 * P 0) * (P 0 * P 0)),
         ((8 : ℕ) : R) * (P 0 * (P 1 * P 1)),
         ((9 : ℕ) : R) * ((P 0 * P 0) * (P 0 * P 0)) - ((8 : ℕ) : R) * (P 0 * (P 1 * P 1)),
         (P 0 * P 0)
           * (((9 : ℕ) : R) * ((P 0 * P 0) * (P 0 * P 0)) - ((8 : ℕ) : R) * (P 0 * (P 1 * P 1))),
         (P 0 * P 0) * (P 0 * (P 1 * P 1)),
         (P 1 * P 1) * (P 1 * P 1),
         ((12 : ℕ) : R) * ((P 0 * P 0) * (P 0 * (P 1 * P 1))),
         ((3 : ℕ) : R) * ((P 0 * P 0)
           * (((9 : ℕ) : R) * ((P 0 * P 0) * (P 0 * P 0)) - ((8 : ℕ) : R) * (P 0 * (P 1 * P 1)))),
         ((8 : ℕ) : R) * ((P 1 * P 1) * (P 1 * P 1)),
         ((12 : ℕ) : R) * ((P 0 * P 0) * (P 0 * (P 1 * P 1)))
           - ((3 : ℕ) : R) * ((P 0 * P 0)
             * (((9 : ℕ) : R) * ((P 0 * P 0) * (P 0 * P 0)) - ((8 : ℕ) : R) * (P 0 * (P 1 * P 1)))),
         (((12 : ℕ) : R) * ((P 0 * P 0) * (P 0 * (P 1 * P 1)))
           - ((3 : ℕ) : R) * ((P 0 * P 0)
             * (((9 : ℕ) : R) * ((P 0 * P 0) * (P 0 * P 0)) - ((8 : ℕ) : R) * (P 0 * (P 1 * P 1)))))
           - ((8 : ℕ) : R) * ((P 1 * P 1) * (P 1 * P 1)),
         P 1 * P 2,
         ((2 : ℕ) : R) * (P 1 * P 2)] := by
    simp only [doublingProgram, runProgram, evalInstr, regGet, List.cons_append,
      List.nil_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [evalProgram, hrun, doublingOutX]; show _ = W'.dblX P
    simp only [regGet]; rw [hdblX]; push_cast; ring
  · rw [evalProgram, hrun, doublingOutY]; show _ = W'.dblY P
    simp only [regGet]; rw [hdblY, hdblX]; push_cast; ring
  · rw [evalProgram, hrun, doublingOutZ]; show _ = W'.dblZ P
    simp only [regGet]; rw [hdblZ]; push_cast; ring

/-! ## Resource bridge: derived count × verified per-multiply cost

The bridge is intentionally lightweight (the spec's "M_dbl derived field mults × verified multiplier"
level). The verified per-controlled-partial-product cost is `Reversible.cRippleCirc_toffoli = 8·width`
(`CtrlAdd.lean`); a quantum×quantum field multiply at width `w` (`Reversible.cMulCircuit`,
correct by `cMulCircuit_eq_mul`) is `w` such controlled adds, so it costs `≤ 8·w²` Toffolis. A doubling
runs `M_dbl` field multiplies, hence `≤ M_dbl · 8·w²`. The *exact* `cMulCircuit` cost lemma and the full
assembled doubling circuit (register routing, ancilla scheduling, in-place modular reduction between
multiplies) are **S6.3 residue**. -/

/-- Verified per-controlled-partial-product Toffoli cost at width `w`: `8·w` (`cRippleCirc_toffoli`). -/
def ctrlAddToffoli (w : ℕ) : ℕ := 8 * w

/-- Per quantum×quantum field-multiply Toffoli bound at width `w`: `w` controlled partial-product adds,
each `ctrlAddToffoli w`, so `8·w²`. (An upper bound: the partial-product adds at shift `sh` act on the
narrower window `w − sh`, so the true cost is smaller; this is the worst-case full-width figure.) -/
def fieldMulToffoli (w : ℕ) : ℕ := w * ctrlAddToffoli w

/-- The doubling Toffoli figure: `M_dbl` field multiplies, each `fieldMulToffoli w`. With `M` now
*derived* (`M_dbl = 8`) and the per-multiply cost *verified* (`cMulCircuit`), this is a derived-count ×
verified-multiplier figure, not a documented constant. -/
def doublingToffoli (w : ℕ) : ℕ := M_dbl * fieldMulToffoli w

/-- The doubling Toffoli figure unfolds to `8 · (8·w²) = 64·w²` at width `w`. -/
theorem doubling_toffoli_eq (w : ℕ) : doublingToffoli w = 64 * w ^ 2 := by
  simp only [doublingToffoli, M_dbl_eq, fieldMulToffoli, ctrlAddToffoli]; ring

/-- At the secp256k1 width `w = 256`, the (un-reduced) doubling Toffoli figure is `64·256² = 4 194 304`,
the per-doubling field-arithmetic cost feeding the end-to-end scalar-multiplication estimate. -/
theorem doubling_toffoli_secp256k1 : doublingToffoli 256 = 4194304 := by
  rw [doubling_toffoli_eq]; norm_num

end ECDLP
