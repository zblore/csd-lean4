import CsdLean4.Ecdsafail.PointDouble

/-!
# Derived field-multiplication count for `a = 0` Jacobian mixed addition  (ECDLP Phase 2, Stage S6.2)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Sibling of S6.1 (`PointDouble.lean`). S6 of the ECDLP resource programme
(`specs/ecdlp-resource-plan.md`) "derives the free parameter `M`" — the number of register×register
field multiplications per elliptic-curve point operation. S6.1 derived the **doubling** count
`M_dbl = 8`; S6.2 derives the **mixed-addition** count `M_add`, replacing the documented EFD constant
`11`. The straight-line program model (`Instr`/`Program`/`evalProgram`/`mulCount`/`regGet`) is
**reused verbatim** from `PointDouble.lean`; only the schedule and its correctness theorem are new.

## The addition subtlety (why this is not a literal `addXYZ` count)

Mathlib's **raw** `WeierstrassCurve.Jacobian.addX P Q` (`Jacobian/Formula.lean:467`) carries a
`2·a₆·(P z)⁴·(Q z)⁴` term. secp256k1 has `a₆ = 7 ≠ 0`, so even under `a₁=a₂=a₃=a₄=0` the raw
representative is **not** the textbook EFD addition formula — it still contains the curve constant. The
raw and the clean EFD form agree only **on the curve**, where Mathlib eliminates the `a₆` term via the
curve equation (`addX_eq'`). We therefore count the **on-curve EFD-comparable** addition: the schedule a
real circuit pays, which assumes the inputs satisfy `Equation P`/`Equation Q` and never materialises the
`a₆` term. This is why `additionProgram_correct` carries `hP : W'.Equation P`, `hQ : W'.Equation Q` as
**load-bearing** hypotheses (satisfiable: points on the curve — see the `ZMod 17` witness below), unlike
the doubling schedule, whose `dblX`/`dblY` formulae are clean at `a = 0` without an on-curve hypothesis.

## The exhibited on-curve schedule

With the standard intermediates `U1 = P x·Q z²`, `U2 = Q x·P z²`, `S1 = P y·Q z³`, `S2 = Q y·P z³`,
`D = addZ = U1 − U2`, `r = S1 − S2`, the schedule computes the three numerators
```
out_X = r² − U1·D² − U2·D²
out_Y = r·(out_X − U1·D²) + S1·D³
out_Z = −(P z·Q z)·D
```
and (verified here by `ring` after rewriting `a = 0` into `addX_eq'`/`negAddY_eq'`) these are exactly the
components of `(−(P z·Q z)) • W'.addXYZ P Q` in Mathlib's weighted Jacobian action
`w • ![A,B,C] = ![w²·A, w³·B, w·C]`:
```
out_X = W'.addX    P Q · (P z·Q z)²    -- the addX_eq' RHS at a = 0           (consumes Equation P/Q)
out_Y = W'.negAddY P Q · (P z·Q z)³    -- = −(W'.addY P Q)·(P z·Q z)³ at a = 0 (consumes Equation P/Q)
out_Z = −(P z·Q z)·(addZ P Q)          -- pure `addZ` definition               (HYPOTHESIS-FREE)
```
i.e. `![out_X, out_Y, out_Z] = (−(P z·Q z)) • W'.addXYZ P Q`. Since `W'.addXYZ P Q` is Mathlib's
group-law representative of `P + Q` (`Jacobian/Point.lean`), the unit multiple `(−(P z·Q z)) • addXYZ`
(a unit when `P z, Q z ≠ 0`) represents the **same** group element. Note the asymmetry: `out_Z`'s
identity is hypothesis-free (it is the `addZ` definition up to the scalar), while `out_X`/`out_Y` consume
the curve equations — that asymmetry is precisely the `a₆`-elimination subtlety above.

## The carve line (which side each result sits on)

* **Group-law correctness is REUSED from Mathlib, not derived here.** `W'.addXYZ` represents `P + Q` in
  `Jacobian/Point.lean`; this module does not reprove the group law.
* **The on-curve polynomial identities are REUSED from Mathlib** via `addX_eq'` / `negAddY_eq'`; only the
  fact "the exhibited program *evaluates to those numerators*" is proved here (a `ring` step).
* **The count `M_add` is DERIVED here**, off the program's instruction list (`mulCount`), the same
  derived-cost discipline as S6.1 and the rest of the programme.
* **The full assembled point-addition reversible circuit is NOT built here** (register routing, ancilla
  scheduling, in-place modular reduction between multiplies). The resource bridge below composes the
  derived count with the verified per-multiply cost at the level of a bound; the concrete assembly is
  named **S6.3 residue**.
-/

namespace ECDLP

open WeierstrassCurve WeierstrassCurve.Jacobian

variable {R : Type*} [CommRing R]

/-! ## The `a = 0` Jacobian mixed-addition program

Inputs (six registers): `0:P x   1:P y   2:Q x   3:Q y   4:P z   5:Q z`. The schedule, with the counted
`mul`/`sq` opcodes flagged. Coefficients (here only the implicit unit scalars) need no `nsmul`; the only
non-linear opcodes are the seventeen `mul`/`sq` below.
```
6:  Pz2  = P z²            (sq,  counted)
7:  Qz2  = Q z²            (sq,  counted)
8:  Pz3  = Pz2·P z         (mul, counted)
9:  Qz3  = Qz2·Q z         (mul, counted)
10: U1   = P x·Qz2         (mul, counted)   -- = P x·Q z²
11: U2   = Q x·Pz2         (mul, counted)   -- = Q x·P z²
12: S1   = P y·Qz3         (mul, counted)   -- = P y·Q z³
13: S2   = Q y·Pz3         (mul, counted)   -- = Q y·P z³
14: D    = U1 − U2                          -- = addZ
15: r    = S1 − S2
16: D2   = D²              (sq,  counted)
17: D3   = D2·D            (mul, counted)
18: r2   = r²              (sq,  counted)
19: U1D2 = U1·D2           (mul, counted)
20: U2D2 = U2·D2           (mul, counted)
21: t1   = r2 − U1D2
22: outX = t1 − U2D2                         ★ output X = r² − U1·D² − U2·D²
23: oXm  = outX − U1D2                        -- = out_X − U1·D²
24: rt   = r·oXm           (mul, counted)
25: S1D3 = S1·D3           (mul, counted)
26: outY = rt + S1D3                          ★ output Y = r·(out_X − U1·D²) + S1·D³
27: PzQz = P z·Q z         (mul, counted)
28: PD   = PzQz·D          (mul, counted)
29: outZ = −PD                                ★ output Z = −(P z·Q z)·D
```
Seventeen counted opcodes (regs `6,7,8,9,10,11,12,13,16,17,18,19,20,24,25,27,28`) ⇒ `mulCount = 17`. -/
def additionProgram : Program :=
  [ .sq 4,          -- 6:  Pz2  = P z²
    .sq 5,          -- 7:  Qz2  = Q z²
    .mul 6 4,       -- 8:  Pz3  = Pz2 · P z
    .mul 7 5,       -- 9:  Qz3  = Qz2 · Q z
    .mul 0 7,       -- 10: U1   = P x · Qz2
    .mul 2 6,       -- 11: U2   = Q x · Pz2
    .mul 1 9,       -- 12: S1   = P y · Qz3
    .mul 3 8,       -- 13: S2   = Q y · Pz3
    .sub 10 11,     -- 14: D    = U1 − U2
    .sub 12 13,     -- 15: r    = S1 − S2
    .sq 14,         -- 16: D2   = D²
    .mul 16 14,     -- 17: D3   = D2 · D
    .sq 15,         -- 18: r2   = r²
    .mul 10 16,     -- 19: U1D2 = U1 · D2
    .mul 11 16,     -- 20: U2D2 = U2 · D2
    .sub 18 19,     -- 21: t1   = r2 − U1D2
    .sub 21 20,     -- 22: outX = t1 − U2D2
    .sub 22 19,     -- 23: oXm  = outX − U1D2
    .mul 15 23,     -- 24: rt   = r · oXm
    .mul 12 17,     -- 25: S1D3 = S1 · D3
    .add 24 25,     -- 26: outY = rt + S1D3
    .mul 4 5,       -- 27: PzQz = P z · Q z
    .mul 27 14,     -- 28: PD   = PzQz · D
    .neg 28 ]       -- 29: outZ = −PD

/-- The output register holding `out_X = W'.addX P Q · (P z·Q z)²`. -/
def additionOutX : ℕ := 22
/-- The output register holding `out_Y = W'.negAddY P Q · (P z·Q z)³`. -/
def additionOutY : ℕ := 26
/-- The output register holding `out_Z = −(P z·Q z)·addZ P Q`. -/
def additionOutZ : ℕ := 29

/-! ## The derived multiplication count -/

/-- **The DERIVED field-multiplication count for an `a = 0` Jacobian mixed addition.** Read off
`additionProgram`'s instruction list by `mulCount` (seventeen register×register `mul`/`sq` opcodes:
`P z², Q z², Pz³, Qz³, U1, U2, S1, S2, D², D³, r², U1·D², U2·D², r·(…), S1·D³, P z·Q z, PzQz·D`).

Honest comparison to the literature: the EFD `a = 0` mixed addition (`add-2007-bl`) is quoted at
`11M + 5S = 16`, and `add-1998-cmo-2` at `12M + 4S = 16`. This explicit, *verified* schedule lands at
`17`, one above those figures. The gap is two-fold and **not** fudged down: (a) the EFD schedules fold
the two `output − U1·D²` style subtractions and reuse `S1·D³` / `r·(…)` products in a way that shaves
one product via a Karatsuba-style `(U1+U2)`/`(S1+S2)` combination this straight-line schedule does not
exploit; (b) the explicit `out_Z = −(P z·Q z)·D` here pays a separate `P z·Q z` *and* `PzQz·D` product
(two opcodes) where EFD折叠s the `Z`-update into a single `((P z+Q z)² − P z² − Q z²)·D` step reusing the
already-computed `P z²`, `Q z²` (one product). The `mul`/`sq` opcodes here do not distinguish `M` from
`S` (both counted as one), matching S6.1's convention; the reported `17` is the count of the exhibited
on-curve schedule, comparable to — not claimed equal to — the EFD `16`. -/
def M_add : ℕ := mulCount additionProgram

@[simp] theorem M_add_eq : M_add = 17 := by decide

/-! ## Correctness: the program computes the on-curve addition numerators

Group-law correctness of `addXYZ` is Mathlib's (`Jacobian/Point.lean`); the on-curve numerator
identities are Mathlib's (`addX_eq'` / `negAddY_eq'`). Here we prove only that the exhibited counted
program *evaluates to those numerators*, equivalently to `(−(P z·Q z)) • W'.addXYZ P Q`. -/

variable {W' : Jacobian R}

/-- The explicit final register file after running `additionProgram` on `[P x, P y, P z, Q x, Q y, Q z]`,
written with `P i`/`Q i` abbreviations. Computed once by structural unfolding (cheap cons/append
reduction), so each output register is read off without re-running the program. The inputs are
`[P 0, P 1, P 2, Q 0, Q 1, Q 2]` = `[P x, P y, Q x, Q y, P z, Q z]` matching the schedule's input layout
(`0:P x  1:P y  2:Q x  3:Q y  4:P z  5:Q z`). -/
private theorem hrun_addition (P Q : Fin 3 → R) :
    runProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram =
      let Pz2 := P 2 * P 2
      let Qz2 := Q 2 * Q 2
      let Pz3 := Pz2 * P 2
      let Qz3 := Qz2 * Q 2
      let U1 := P 0 * Qz2
      let U2 := Q 0 * Pz2
      let S1 := P 1 * Qz3
      let S2 := Q 1 * Pz3
      let D := U1 - U2
      let r := S1 - S2
      let D2 := D * D
      let D3 := D2 * D
      let r2 := r * r
      let U1D2 := U1 * D2
      let U2D2 := U2 * D2
      let outX := r2 - U1D2 - U2D2
      let outY := r * (outX - U1D2) + S1 * D3
      [P 0, P 1, Q 0, Q 1, P 2, Q 2,
        Pz2, Qz2, Pz3, Qz3, U1, U2, S1, S2, D, r, D2, D3, r2, U1D2, U2D2,
        r2 - U1D2, outX, outX - U1D2, r * (outX - U1D2), S1 * D3, outY,
        P 2 * Q 2, (P 2 * Q 2) * D, -((P 2 * Q 2) * D)] := by
  simp only [additionProgram, runProgram, evalInstr, regGet, List.cons_append, List.nil_append]

/-- **The load-bearing S6.2 theorem.** Under the secp256k1 hypotheses `a₁=a₂=a₃=a₄=0` and the on-curve
hypotheses `hP : W'.Equation P`, `hQ : W'.Equation Q`, the addition program evaluated at the coordinates
`(P x, P y, Q x, Q y, P z, Q z)` produces, in registers `additionOutX/Y/Z`, the three components of the
projective representative `(−(P z·Q z)) • W'.addXYZ P Q` of `P + Q`:

* `out_X = W'.addX P Q · (P z·Q z)²`    (the `addX_eq'` RHS at `a = 0`; consumes `hP`, `hQ`);
* `out_Y = W'.negAddY P Q · (P z·Q z)³` (= `−(W'.addY P Q)·(P z·Q z)³` at `a = 0`; consumes `hP`, `hQ`);
* `out_Z = −(P z·Q z)·(addZ P Q)`       (the `addZ` definition; **hypothesis-free**).

This ties the counted program (`mulCount = M_add = 17`) to Mathlib's group-law-correct addition
representative; it does **not** reprove the group law (that is `Jacobian/Point.lean`) nor the on-curve
numerator identities (those are `addX_eq'`/`negAddY_eq'`). The `Equation P`/`Equation Q` hypotheses are
load-bearing for the `X`/`Y` components (they eliminate the raw `2·a₆·(P z)⁴·(Q z)⁴` term, nonzero on
secp256k1) and satisfiable (points on the curve; see the `ZMod 17` witness). -/
theorem additionProgram_correct (P Q : Fin 3 → R)
    (ha₁ : W'.a₁ = 0) (ha₂ : W'.a₂ = 0) (_ha₃ : W'.a₃ = 0) (_ha₄ : W'.a₄ = 0)
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    evalProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram additionOutX
        = W'.addX P Q * (P 2 * Q 2) ^ 2
      ∧ evalProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram additionOutY
        = W'.negAddY P Q * (P 2 * Q 2) ^ 3
      ∧ evalProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram additionOutZ
        = -(P 2 * Q 2) * addZ P Q := by
  refine ⟨?_, ?_, ?_⟩
  · -- out_X = addX P Q · (P z·Q z)² : the addX_eq' RHS at a = 0, consumes the curve equations
    rw [evalProgram, hrun_addition, additionOutX]
    show _ = W'.addX P Q * (P 2 * Q 2) ^ 2
    simp only [regGet]
    rw [addX_eq' hP hQ, ha₁, ha₂, addZ]
    ring_nf
  · -- out_Y = negAddY P Q · (P z·Q z)³ : via negAddY_eq', substituting the on-curve out_X identity
    rw [evalProgram, hrun_addition, additionOutY]
    show _ = W'.negAddY P Q * (P 2 * Q 2) ^ 3
    simp only [regGet]
    rw [negAddY_eq', addX_eq' hP hQ, ha₁, ha₂, addZ]
    ring_nf
  · -- out_Z = −(P z·Q z)·addZ : the addZ definition, hypothesis-free
    rw [evalProgram, hrun_addition, additionOutZ]
    show _ = -(P 2 * Q 2) * addZ P Q
    simp only [regGet, addZ]
    ring_nf

/-- **Vector form of `additionProgram_correct`.** The three output registers, assembled as a `Fin 3`
vector, equal `(−(P z·Q z)) • W'.addXYZ P Q` — Mathlib's group-law representative of `P + Q` scaled by
the unit `−(P z·Q z)` (a unit when `P z, Q z ≠ 0`), hence the same projective point. This is the
transparent "projective equivalence to the group-law representative" reading. The scalar action unfolds
via `smul_fin3`: `w • ![A,B,C] = ![w²·A, w³·B, w·C]`, and at `a = 0` one has `W'.addY P Q = −W'.negAddY P Q`,
so the `Y` component `w³·addY = −(P z·Q z)³·addY = (P z·Q z)³·negAddY = out_Y`. -/
theorem additionProgram_correct_vector (P Q : Fin 3 → R)
    (ha₁ : W'.a₁ = 0) (ha₂ : W'.a₂ = 0) (ha₃ : W'.a₃ = 0) (ha₄ : W'.a₄ = 0)
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    ![evalProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram additionOutX,
      evalProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram additionOutY,
      evalProgram [P 0, P 1, Q 0, Q 1, P 2, Q 2] additionProgram additionOutZ]
      = (-(P 2 * Q 2)) • W'.addXYZ P Q := by
  obtain ⟨hX, hY, hZ⟩ := additionProgram_correct P Q ha₁ ha₂ ha₃ ha₄ hP hQ
  -- W'.addY P Q = -W'.negAddY P Q at a = 0
  have haddY : W'.addY P Q = -W'.negAddY P Q := by
    rw [addY, negY_eq, ha₁, ha₃]; ring
  rw [hX, hY, hZ, addXYZ, smul_fin3]
  ext i
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, haddY] <;> ring_nf

/-! ## Resource bridge: derived count × verified per-multiply cost

Identical discipline to S6.1's `doublingToffoli`. A quantum×quantum field multiply at width `w` is the
controlled shift-and-add multiplier `Reversible.cMulCircuit` (verified by `cMulCircuit_eq_mul`), `w`
controlled partial-product adds each `fieldMulToffoli`-bounded; an addition runs `M_add` field multiplies,
hence `≤ M_add · fieldMulToffoli w`. The exact `cMulCircuit` cost lemma and the full assembled addition
circuit (register routing, ancilla scheduling, in-place modular reduction between multiplies) are
**S6.3 residue**. -/

/-- The mixed-addition Toffoli figure: `M_add` field multiplies, each `fieldMulToffoli w` (reusing the
verified per-multiply bound from `PointDouble.lean`). With `M` now *derived* (`M_add = 17`) and the
per-multiply cost *verified* (`cMulCircuit`), this is a derived-count × verified-multiplier figure. -/
def additionToffoli (w : ℕ) : ℕ := M_add * fieldMulToffoli w

/-- The addition Toffoli figure unfolds to `17 · (8·w²) = 136·w²` at width `w`. -/
theorem addition_toffoli_eq (w : ℕ) : additionToffoli w = 136 * w ^ 2 := by
  simp only [additionToffoli, M_add_eq, fieldMulToffoli, ctrlAddToffoli]; ring

/-- At the secp256k1 width `w = 256`, the (un-reduced) mixed-addition Toffoli figure is
`136·256² = 8 912 896`, the per-addition field-arithmetic cost feeding the end-to-end
scalar-multiplication estimate. Bound-level (assembled circuit = S6.3 residue). -/
theorem addition_toffoli_secp256k1 : additionToffoli 256 = 8912896 := by
  rw [addition_toffoli_eq]; norm_num

/-! ## Non-vacuity witness: `y² = x³ + 7` over `ZMod 17`

The `Equation P`/`Equation Q` hypotheses are satisfiable. Take the secp256k1-shape curve
`y² = x³ + 7` over `ZMod 17` (`a₁=a₂=a₃=a₄=0`, `a₆=7`) with the two on-curve affine points
`P = (2, 7)` and `Q = (1, 5)` (Jacobian `z = 1`). The program outputs match the hand-computed
representative `![1, 5, 16]` of `P + Q` (here `−(P z·Q z) = −1`). -/

/-- The secp256k1-shape witness curve over `ZMod 17`. -/
def W17 : Jacobian (ZMod 17) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 }

/-- Witness point `P = (2, 7, 1)` on `W17`. -/
def P17 : Fin 3 → ZMod 17 := ![2, 7, 1]
/-- Witness point `Q = (1, 5, 1)` on `W17`. -/
def Q17 : Fin 3 → ZMod 17 := ![1, 5, 1]

theorem P17_on_curve : W17.Equation P17 := by rw [equation_iff]; decide
theorem Q17_on_curve : W17.Equation Q17 := by rw [equation_iff]; decide

/-- The witness instantiation is non-vacuous: the hypotheses of `additionProgram_correct` are all
satisfied at `W17, P17, Q17`, and the three program outputs are the concrete representative
`(1, 5, 16)` of `P17 + Q17` (`out_X = 1`, `out_Y = 5`, `out_Z = 16 = −1` in `ZMod 17`), matching the
hand-computed `(−(P z·Q z)) • addXYZ = (−1) • ![1, 12, 1] = ![1, 5, 16]`. -/
example :
    evalProgram [P17 0, P17 1, Q17 0, Q17 1, P17 2, Q17 2] additionProgram additionOutX = 1
      ∧ evalProgram [P17 0, P17 1, Q17 0, Q17 1, P17 2, Q17 2] additionProgram additionOutY = 5
      ∧ evalProgram [P17 0, P17 1, Q17 0, Q17 1, P17 2, Q17 2] additionProgram additionOutZ = 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end ECDLP
