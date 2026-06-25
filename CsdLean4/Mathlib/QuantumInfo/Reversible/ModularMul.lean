import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularDouble
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAddCtrl
import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval

/-!
# Reversible interleaved modular multiply — the verified Horner LOOP BODY  (ECDLP Phase 2, Stage S6.3d-2a)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module **verifies the loop body of the interleaved MSB-first modular multiply** over `𝔽_p`,
`acc ← (2·acc + [X_i]·Y) mod N`, by chaining the two already-verified blocks one tranche below:

```
hornerStep L = modDouble L.dbl ++ cModAdd L.add
```

* **modDouble** `modDouble L.dbl` (S6.3d-1, `modDouble_correct` / `modDouble_in_range`): with the
  accumulator `B` holding `c < N`, its scratch operand `dbl.Aop` initialised `0`, presets
  `A1 = 2ⁿ − N`, `A2 = N`, clean carries / ancilla, and `2N ≤ 2ⁿ`, it leaves `B ← (2c) mod N`, with
  `(2c) mod N < N`. It touches only its own wires `{B, dbl.Aop, dbl.Cadd, dbl.A1, dbl.C1, dbl.A2,
  dbl.C2, dbl.anc}`, so the multiplicand `Y = add.Aop`, the control bit `X_i = add.ctrl`, and the
  controlled-add step's fresh carries / presets / ancilla all survive it (the frame lemmas
  `modDouble_preserves_external` and corollaries below).
* **cModAdd** `cModAdd L.add` (S6.3c, `cModAdd_correct`): now `B = d := (2c) mod N < N`, operand
  `Aop = Y` (`Yval < N`), control `ctrl = X_i`. It leaves
  `B ← if X_i then (Yval + d) mod N else d`.

Composition (the loop-body identity, absorbing the inner `mod N` via `Nat.add_mod` / `Nat.mod_add_mod`):

* `X_i` set: `(Yval + (2c mod N)) mod N = (Yval + 2c) mod N = (2c + Yval) mod N`.
* `X_i` clear: `(2c) mod N = (2c + 0) mod N`.

So `hornerStep_correct` gives `B ← (2*c + (if X_i then Yval else 0)) mod N`.

## Carve line (what this is, and is NOT)

This is the verified **LOOP BODY** of the interleaved MSB-first modular multiply,
`acc ← (2·acc + [X_i]·Y) mod N`, composing the verified `modDouble` (S6.3d-1) and `cModAdd` (S6.3c).
The 2-step composition is delivered two ways: (i) the proven `mulStep2_correct`, which chains
`hornerStep_correct` twice over two banks sharing `B` and `Y` with fresh per-bank wires, concluding
`acc = (X · Yval) mod N` for the 2-bit multiplier `X = 2·X₁ + X₀`; and (ii) a concrete `Fin 92`
instance (`mulCircuit2` / `mulState2`) whose three `#eval` / `decide` witnesses realise
`X = 3 ↦ 0`, `X = 2 ↦ 1`, `X = 1 ↦ 2` at `Y = 2`, `N = 3` (the verified `n = 2` modular multiply).

**This is NOT the general-`n` multiply.** The general-`n` Horner loop — the induction folding
`hornerStep` over all `n` bits of `X` with the invariant `acc = (X ≫ i)·Y mod N` — is the subsequent
tranche **S6.3d-2b**, NOT built here.

**Named residue (the fresh-ancilla / dirty-carry model, inherited from S6.3d-1 and S6.3c):**

1. **Fresh per-iteration wires (O(n²) qubits).** Each Horner step is supplied its OWN doubling
   scratch / carries / ancilla and its OWN controlled-add carries / ancilla, disjoint from the
   previous step's. The 2-step demo exhibits exactly this: two banks, fresh wires each. Across `n`
   steps this is `Θ(n²)` ancilla. In-place reuse (`Θ(n)` qubits) needs the **carry-clean /
   ancilla-restoring** adder the corpus does NOT yet provide (Cuccaro-style inline carry-uncompute,
   or the self-cleaning high-bit modular adder). That carry-clean adder is the genuine orthogonal
   residue, NOT built here.
2. **Only the multiplicand `Y` must persist across steps.** The loop reads each `X_i` once (the bit
   wire of step `i` is dead after step `i`), but `Y = add.Aop` must survive every step; this is the
   load-bearing `hornerStep_preserves_Y`.

## Honest cost

`hornerStep_toffoli` derives `30n` Toffolis from the exhibited gate list: modDouble `12n`
(`modDouble_toffoli`) + cModAdd `18n` (`cModularAdd_toffoli`), composed through
`cost_comp_toffoli_count`.
-/

namespace Reversible

variable {m n : ℕ}

/-! ### Generic frame: a wire external to `modReduce` / `modAdd` / `modDouble` survives

`modDouble L = copyReg L ++ modAdd L.addLayout` and `modAdd L = rippleCirc L.addStep ++ modReduce
L.reduceStep`. Each block is a frame lemma over its wire families; the three lemmas below compose them
so that a wire disjoint from every modDouble-touched family passes through unchanged. These are the
only genuinely new structural lemmas of this tranche. -/

/-- **`modReduce` frame.** A wire `w` disjoint from every reduce-step family
(`B, A1, C1, A2, C2, anc`) is left unchanged by `modReduce L`. Mirrors
`modReduce_reduceStep_preserves_Aop` but abstracted to an arbitrary external wire and a bare
`ModReduceLayout`. -/
theorem modReduce_preserves_external (L : ModReduceLayout m n) (s : State m) (w : Fin m)
    (hB : ∀ j, w ≠ L.B j) (hA1 : ∀ j, w ≠ L.A1 j) (hC1 : ∀ j, w ≠ L.C1 j)
    (hA2 : ∀ j, w ≠ L.A2 j) (hC2 : ∀ j, w ≠ L.C2 j) (hanc : w ≠ L.anc) :
    denote (modReduce L) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [modReduce, List.append_assoc, List.mem_append] at hg
  rcases hg with hg | hg
  · -- step 1: rippleCirc L.stepOne, wires {A1, B, C1}
    rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
    obtain ⟨k, _hk, hgk⟩ := hg
    simp only [rippleSlice, fullAdder, ModReduceLayout.stepOne, List.mem_cons, List.not_mem_nil,
      or_false] at hgk
    rcases hgk with rfl | rfl | rfl | rfl <;>
      simp [gateWires, hA1 k, hB k, hC1 k, hC1 (k + 1)]
  · rw [List.mem_append] at hg
    rcases hg with hg | hg
    · -- step 2: [X (C1 n)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp [gateWires, hC1 n]
    · -- step 3: cRippleCirc L.stepThree
      rw [cRippleCirc, cRipplePrefix, List.mem_flatMap] at hg
      obtain ⟨k, _hk, hgk⟩ := hg
      simp only [cRippleSlice, cfullAdder, ModReduceLayout.stepThree, List.mem_cons,
        List.not_mem_nil, or_false] at hgk
      rcases hgk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [gateWires, hA2 k, hB k, hC2 k, hC2 (k + 1), hanc, hC1 n]

/-- **`modAdd` frame.** A wire `w` disjoint from every modAdd-touched family
(`Aop, B, Cadd, A1, C1, A2, C2, anc`) is left unchanged by `modAdd L`. Composes
`rippleCirc_addStep_preserves` (add step) with `modReduce_preserves_external` (reduce step). -/
theorem modAdd_preserves_external (L : ModAddLayout m n) (s : State m) (w : Fin m)
    (hAop : ∀ j, w ≠ L.Aop j) (hB : ∀ j, w ≠ L.B j) (hCadd : ∀ j, w ≠ L.Cadd j)
    (hA1 : ∀ j, w ≠ L.A1 j) (hC1 : ∀ j, w ≠ L.C1 j) (hA2 : ∀ j, w ≠ L.A2 j)
    (hC2 : ∀ j, w ≠ L.C2 j) (hanc : w ≠ L.anc) :
    denote (modAdd L) s w = s w := by
  rw [modAdd, denote_append]
  rw [modReduce_preserves_external L.reduceStep _ w hB hA1 hC1 hA2 hC2 hanc]
  exact rippleCirc_addStep_preserves (L := L) s w hAop hB hCadd

/-- **`modDouble` frame.** A wire `w` disjoint from every modDouble-touched family
(`B`, the scratch operand `dbl.Aop`, and the bundled add layout's `Cadd, A1, C1, A2, C2, anc`) is
left unchanged by `modDouble L`. Composes `copyReg_preserves` (copy step) with
`modAdd_preserves_external` (the bundled `modAdd`). -/
theorem modDouble_preserves_external (L : ModDoubleLayout m n) (s : State m) (w : Fin m)
    (hB : ∀ j, w ≠ L.B j) (hAop : ∀ j, w ≠ L.Aop j)
    (hCadd : ∀ j, w ≠ L.addLayout.Cadd j) (hA1 : ∀ j, w ≠ L.addLayout.A1 j)
    (hC1 : ∀ j, w ≠ L.addLayout.C1 j) (hA2 : ∀ j, w ≠ L.addLayout.A2 j)
    (hC2 : ∀ j, w ≠ L.addLayout.C2 j) (hanc : w ≠ L.addLayout.anc) :
    denote (modDouble L) s w = s w := by
  rw [modDouble, denote_append]
  rw [modAdd_preserves_external L.addLayout _ w hAop hB hCadd hA1 hC1 hA2 hC2 hanc]
  exact copyReg_preserves (L := L) s w hB hAop

/-- **`cModAdd` frame.** A wire `w` disjoint from every cModAdd-touched family
(`Aop, B, Ccadd, ctrl, ancC` of the controlled add, and `A1, C1, A2, C2, anc` of the reduce) is left
unchanged by `cModAdd L`. Composes `cRippleCirc_preserves_external` (controlled add step) with
`modReduce_preserves_external` (reduce step). Register hyps are bounded (`< n` / `< n + 1`), as in
`cRippleCirc_preserves_external`. -/
theorem cModAdd_preserves_external (L : CModAddLayout m n) (s : State m) (w : Fin m)
    (hAop : ∀ k, k < n → w ≠ L.Aop k) (hB : ∀ k, w ≠ L.B k) (hctrl : w ≠ L.ctrl)
    (hCcadd : ∀ k, k < n + 1 → w ≠ L.Ccadd k) (hancC : w ≠ L.ancC)
    (hA1 : ∀ j, w ≠ L.A1 j) (hC1 : ∀ j, w ≠ L.C1 j) (hA2 : ∀ j, w ≠ L.A2 j)
    (hC2 : ∀ j, w ≠ L.C2 j) (hanc : w ≠ L.anc) :
    denote (cModAdd L) s w = s w := by
  rw [cModAdd, denote_append]
  rw [modReduce_preserves_external L.reduceStep _ w hB hA1 hC1 hA2 hC2 hanc]
  exact cRippleCirc_preserves_external L.cAddStep s w hctrl hancC hAop (fun k _ => hB k) hCcadd

/-! ### The Horner-step layout

A `HornerStepLayout` bundles the S6.3d-1 doubling sub-layout `dbl` and the S6.3c controlled-add
sub-layout `add`, sharing the accumulator (`dbl.B = add.B`, the running `acc`), with the doubling's
wires (scratch operand + carries + ancilla) and the controlled-add's wires (carries + ancilla)
**fresh and disjoint** from each other, from the multiplicand `Y = add.Aop`, and from the control bit
`X_i = add.ctrl`. The cross-disjointness fields are exactly what `modDouble_preserves_external` needs
to re-establish every `cModAdd_correct` hypothesis through the doubling. -/

/-- A Horner-step layout for `n`-bit registers on `Fin m`. The two sub-layouts share the accumulator
`B`; everything else of the doubling block is disjoint from everything the controlled-add block reads
or carries. -/
structure HornerStepLayout (m n : ℕ) where
  /-- The S6.3d-1 doubling sub-layout (its `B` is the shared accumulator). -/
  dbl : ModDoubleLayout m n
  /-- The S6.3c controlled-add sub-layout (`add.Aop = Y`, `add.ctrl = X_i`, `add.B` the shared `acc`). -/
  add : CModAddLayout m n
  /-- Sharing: the two blocks act on the **same** accumulator register `B`. -/
  hBshared : dbl.B = add.B
  -- the doubling scratch operand `dbl.Aop` is disjoint from every controlled-add external family
  hAopAop : ∀ i j, dbl.Aop i ≠ add.Aop j
  hAopctrl : ∀ i, dbl.Aop i ≠ add.ctrl
  hAopCcadd : ∀ i j, dbl.Aop i ≠ add.Ccadd j
  hAopancC : ∀ i, dbl.Aop i ≠ add.ancC
  hAopA1 : ∀ i j, dbl.Aop i ≠ add.A1 j
  hAopC1 : ∀ i j, dbl.Aop i ≠ add.C1 j
  hAopA2 : ∀ i j, dbl.Aop i ≠ add.A2 j
  hAopC2 : ∀ i j, dbl.Aop i ≠ add.C2 j
  hAopanc : ∀ i, dbl.Aop i ≠ add.anc
  -- the doubling add-carry chain `dbl.Cadd` is disjoint from every controlled-add external family
  hCaddAop : ∀ i j, dbl.addLayout.Cadd i ≠ add.Aop j
  hCaddctrl : ∀ i, dbl.addLayout.Cadd i ≠ add.ctrl
  hCaddCcadd : ∀ i j, dbl.addLayout.Cadd i ≠ add.Ccadd j
  hCaddancC : ∀ i, dbl.addLayout.Cadd i ≠ add.ancC
  hCaddA1 : ∀ i j, dbl.addLayout.Cadd i ≠ add.A1 j
  hCaddC1 : ∀ i j, dbl.addLayout.Cadd i ≠ add.C1 j
  hCaddA2 : ∀ i j, dbl.addLayout.Cadd i ≠ add.A2 j
  hCaddC2 : ∀ i j, dbl.addLayout.Cadd i ≠ add.C2 j
  hCaddanc : ∀ i, dbl.addLayout.Cadd i ≠ add.anc
  -- the doubling reduce constant `dbl.A1` is disjoint from every controlled-add external family
  hdA1Aop : ∀ i j, dbl.addLayout.A1 i ≠ add.Aop j
  hdA1ctrl : ∀ i, dbl.addLayout.A1 i ≠ add.ctrl
  hdA1Ccadd : ∀ i j, dbl.addLayout.A1 i ≠ add.Ccadd j
  hdA1ancC : ∀ i, dbl.addLayout.A1 i ≠ add.ancC
  hdA1A1 : ∀ i j, dbl.addLayout.A1 i ≠ add.A1 j
  hdA1C1 : ∀ i j, dbl.addLayout.A1 i ≠ add.C1 j
  hdA1A2 : ∀ i j, dbl.addLayout.A1 i ≠ add.A2 j
  hdA1C2 : ∀ i j, dbl.addLayout.A1 i ≠ add.C2 j
  hdA1anc : ∀ i, dbl.addLayout.A1 i ≠ add.anc
  -- the doubling reduce carry `dbl.C1` is disjoint from every controlled-add external family
  hdC1Aop : ∀ i j, dbl.addLayout.C1 i ≠ add.Aop j
  hdC1ctrl : ∀ i, dbl.addLayout.C1 i ≠ add.ctrl
  hdC1Ccadd : ∀ i j, dbl.addLayout.C1 i ≠ add.Ccadd j
  hdC1ancC : ∀ i, dbl.addLayout.C1 i ≠ add.ancC
  hdC1A1 : ∀ i j, dbl.addLayout.C1 i ≠ add.A1 j
  hdC1C1 : ∀ i j, dbl.addLayout.C1 i ≠ add.C1 j
  hdC1A2 : ∀ i j, dbl.addLayout.C1 i ≠ add.A2 j
  hdC1C2 : ∀ i j, dbl.addLayout.C1 i ≠ add.C2 j
  hdC1anc : ∀ i, dbl.addLayout.C1 i ≠ add.anc
  -- the doubling reduce constant `dbl.A2` is disjoint from every controlled-add external family
  hdA2Aop : ∀ i j, dbl.addLayout.A2 i ≠ add.Aop j
  hdA2ctrl : ∀ i, dbl.addLayout.A2 i ≠ add.ctrl
  hdA2Ccadd : ∀ i j, dbl.addLayout.A2 i ≠ add.Ccadd j
  hdA2ancC : ∀ i, dbl.addLayout.A2 i ≠ add.ancC
  hdA2A1 : ∀ i j, dbl.addLayout.A2 i ≠ add.A1 j
  hdA2C1 : ∀ i j, dbl.addLayout.A2 i ≠ add.C1 j
  hdA2A2 : ∀ i j, dbl.addLayout.A2 i ≠ add.A2 j
  hdA2C2 : ∀ i j, dbl.addLayout.A2 i ≠ add.C2 j
  hdA2anc : ∀ i, dbl.addLayout.A2 i ≠ add.anc
  -- the doubling reduce carry `dbl.C2` is disjoint from every controlled-add external family
  hdC2Aop : ∀ i j, dbl.addLayout.C2 i ≠ add.Aop j
  hdC2ctrl : ∀ i, dbl.addLayout.C2 i ≠ add.ctrl
  hdC2Ccadd : ∀ i j, dbl.addLayout.C2 i ≠ add.Ccadd j
  hdC2ancC : ∀ i, dbl.addLayout.C2 i ≠ add.ancC
  hdC2A1 : ∀ i j, dbl.addLayout.C2 i ≠ add.A1 j
  hdC2C1 : ∀ i j, dbl.addLayout.C2 i ≠ add.C1 j
  hdC2A2 : ∀ i j, dbl.addLayout.C2 i ≠ add.A2 j
  hdC2C2 : ∀ i j, dbl.addLayout.C2 i ≠ add.C2 j
  hdC2anc : ∀ i, dbl.addLayout.C2 i ≠ add.anc
  -- the doubling reduce ancilla `dbl.anc` is disjoint from every controlled-add external family
  hdancAop : ∀ j, dbl.addLayout.anc ≠ add.Aop j
  hdancctrl : dbl.addLayout.anc ≠ add.ctrl
  hdancCcadd : ∀ j, dbl.addLayout.anc ≠ add.Ccadd j
  hdancancC : dbl.addLayout.anc ≠ add.ancC
  hdancA1 : ∀ j, dbl.addLayout.anc ≠ add.A1 j
  hdancC1 : ∀ j, dbl.addLayout.anc ≠ add.C1 j
  hdancA2 : ∀ j, dbl.addLayout.anc ≠ add.A2 j
  hdancC2 : ∀ j, dbl.addLayout.anc ≠ add.C2 j
  hdancanc : dbl.addLayout.anc ≠ add.anc

variable {L : HornerStepLayout m n}

/-- The shared accumulator register (`acc`), the `B` of both sub-layouts. -/
def HornerStepLayout.B (L : HornerStepLayout m n) : ℕ → Fin m := L.add.B

/-- The control wire `X_i` for this Horner step (the controlled-add's `ctrl`). -/
def HornerStepLayout.ctrl (L : HornerStepLayout m n) : Fin m := L.add.ctrl

/-- The multiplicand register `Y` (the controlled-add's read-only operand). -/
def HornerStepLayout.Y (L : HornerStepLayout m n) : ℕ → Fin m := L.add.Aop

/-- **The Horner-step circuit.** Double the accumulator (`modDouble`), then conditionally add the
multiplicand `Y` controlled on the bit `X_i` (`cModAdd`). -/
def hornerStep (L : HornerStepLayout m n) : Circuit m :=
  modDouble L.dbl ++ cModAdd L.add

/-! ### modDouble preserves the controlled-add block's external wires

Each corollary specialises `modDouble_preserves_external` to one controlled-add family, feeding the
eight cross-disjointness fields for that family. These re-establish `cModAdd_correct`'s hypotheses at
the post-doubling state. -/

private theorem modDouble_pres_addAop (s : State m) (j : ℕ) :
    denote (modDouble L.dbl) s (L.add.Aop j) = s (L.add.Aop j) :=
  modDouble_preserves_external L.dbl s (L.add.Aop j)
    (fun k => by rw [L.hBshared]; exact (L.add.hAopB j k))
    (fun k => (L.hAopAop k j).symm) (fun k => (L.hCaddAop k j).symm)
    (fun k => (L.hdA1Aop k j).symm) (fun k => (L.hdC1Aop k j).symm)
    (fun k => (L.hdA2Aop k j).symm) (fun k => (L.hdC2Aop k j).symm) (L.hdancAop j).symm

private theorem modDouble_pres_addctrl (s : State m) :
    denote (modDouble L.dbl) s L.add.ctrl = s L.add.ctrl :=
  modDouble_preserves_external L.dbl s L.add.ctrl
    (fun k => by rw [L.hBshared]; exact L.add.hctrlB k)
    (fun k => (L.hAopctrl k).symm) (fun k => (L.hCaddctrl k).symm)
    (fun k => (L.hdA1ctrl k).symm) (fun k => (L.hdC1ctrl k).symm)
    (fun k => (L.hdA2ctrl k).symm) (fun k => (L.hdC2ctrl k).symm) L.hdancctrl.symm

private theorem modDouble_pres_addCcadd (s : State m) (j : ℕ) :
    denote (modDouble L.dbl) s (L.add.Ccadd j) = s (L.add.Ccadd j) :=
  modDouble_preserves_external L.dbl s (L.add.Ccadd j)
    (fun k => by rw [L.hBshared]; exact (L.add.hBCcadd k j).symm)
    (fun k => (L.hAopCcadd k j).symm) (fun k => (L.hCaddCcadd k j).symm)
    (fun k => (L.hdA1Ccadd k j).symm) (fun k => (L.hdC1Ccadd k j).symm)
    (fun k => (L.hdA2Ccadd k j).symm) (fun k => (L.hdC2Ccadd k j).symm) (L.hdancCcadd j).symm

private theorem modDouble_pres_addancC (s : State m) :
    denote (modDouble L.dbl) s L.add.ancC = s L.add.ancC :=
  modDouble_preserves_external L.dbl s L.add.ancC
    (fun k => by rw [L.hBshared]; exact L.add.hancCB k)
    (fun k => (L.hAopancC k).symm) (fun k => (L.hCaddancC k).symm)
    (fun k => (L.hdA1ancC k).symm) (fun k => (L.hdC1ancC k).symm)
    (fun k => (L.hdA2ancC k).symm) (fun k => (L.hdC2ancC k).symm) L.hdancancC.symm

private theorem modDouble_pres_addA1 (s : State m) (j : ℕ) :
    denote (modDouble L.dbl) s (L.add.A1 j) = s (L.add.A1 j) :=
  modDouble_preserves_external L.dbl s (L.add.A1 j)
    (fun k => by rw [L.hBshared]; exact (L.add.hBA1 k j).symm)
    (fun k => (L.hAopA1 k j).symm) (fun k => (L.hCaddA1 k j).symm)
    (fun k => (L.hdA1A1 k j).symm) (fun k => (L.hdC1A1 k j).symm)
    (fun k => (L.hdA2A1 k j).symm) (fun k => (L.hdC2A1 k j).symm) (L.hdancA1 j).symm

private theorem modDouble_pres_addC1 (s : State m) (j : ℕ) :
    denote (modDouble L.dbl) s (L.add.C1 j) = s (L.add.C1 j) :=
  modDouble_preserves_external L.dbl s (L.add.C1 j)
    (fun k => by rw [L.hBshared]; exact (L.add.hBC1 k j).symm)
    (fun k => (L.hAopC1 k j).symm) (fun k => (L.hCaddC1 k j).symm)
    (fun k => (L.hdA1C1 k j).symm) (fun k => (L.hdC1C1 k j).symm)
    (fun k => (L.hdA2C1 k j).symm) (fun k => (L.hdC2C1 k j).symm) (L.hdancC1 j).symm

private theorem modDouble_pres_addA2 (s : State m) (j : ℕ) :
    denote (modDouble L.dbl) s (L.add.A2 j) = s (L.add.A2 j) :=
  modDouble_preserves_external L.dbl s (L.add.A2 j)
    (fun k => by rw [L.hBshared]; exact (L.add.hBA2 k j).symm)
    (fun k => (L.hAopA2 k j).symm) (fun k => (L.hCaddA2 k j).symm)
    (fun k => (L.hdA1A2 k j).symm) (fun k => (L.hdC1A2 k j).symm)
    (fun k => (L.hdA2A2 k j).symm) (fun k => (L.hdC2A2 k j).symm) (L.hdancA2 j).symm

private theorem modDouble_pres_addC2 (s : State m) (j : ℕ) :
    denote (modDouble L.dbl) s (L.add.C2 j) = s (L.add.C2 j) :=
  modDouble_preserves_external L.dbl s (L.add.C2 j)
    (fun k => by rw [L.hBshared]; exact (L.add.hBC2 k j).symm)
    (fun k => (L.hAopC2 k j).symm) (fun k => (L.hCaddC2 k j).symm)
    (fun k => (L.hdA1C2 k j).symm) (fun k => (L.hdC1C2 k j).symm)
    (fun k => (L.hdA2C2 k j).symm) (fun k => (L.hdC2C2 k j).symm) (L.hdancC2 j).symm

private theorem modDouble_pres_addanc (s : State m) :
    denote (modDouble L.dbl) s L.add.anc = s L.add.anc :=
  modDouble_preserves_external L.dbl s L.add.anc
    (fun k => by rw [L.hBshared]; exact L.add.hancB k)
    (fun k => (L.hAopanc k).symm) (fun k => (L.hCaddanc k).symm)
    (fun k => (L.hdA1anc k).symm) (fun k => (L.hdC1anc k).symm)
    (fun k => (L.hdA2anc k).symm) (fun k => (L.hdC2anc k).symm) L.hdancanc.symm

/-- **`hornerStep` frame.** A wire `w` disjoint from every wire of BOTH blocks survives the whole
Horner step (`modDouble L.dbl ++ cModAdd L.add`). Used by the 2-step demo to transport bank 2's clean
presets / scratch / carries through bank 1. The modDouble families are
`{B, dbl.Aop, dbl.Cadd, dbl.A1, dbl.C1, dbl.A2, dbl.C2, dbl.anc}`; the cModAdd families are
`{add.Aop, add.B, add.Ccadd, add.ctrl, add.ancC, add.A1, add.C1, add.A2, add.C2, add.anc}`. -/
theorem hornerStep_preserves_external (L : HornerStepLayout m n) (s : State m) (w : Fin m)
    (hB : ∀ j, w ≠ L.dbl.B j) (hdAop : ∀ j, w ≠ L.dbl.Aop j)
    (hdCadd : ∀ j, w ≠ L.dbl.addLayout.Cadd j) (hdA1 : ∀ j, w ≠ L.dbl.addLayout.A1 j)
    (hdC1 : ∀ j, w ≠ L.dbl.addLayout.C1 j) (hdA2 : ∀ j, w ≠ L.dbl.addLayout.A2 j)
    (hdC2 : ∀ j, w ≠ L.dbl.addLayout.C2 j) (hdanc : w ≠ L.dbl.addLayout.anc)
    (hAop : ∀ k, k < n → w ≠ L.add.Aop k) (haddB : ∀ j, w ≠ L.add.B j) (hctrl : w ≠ L.add.ctrl)
    (hCcadd : ∀ k, k < n + 1 → w ≠ L.add.Ccadd k) (hancC : w ≠ L.add.ancC)
    (hA1 : ∀ j, w ≠ L.add.A1 j) (hC1 : ∀ j, w ≠ L.add.C1 j) (hA2 : ∀ j, w ≠ L.add.A2 j)
    (hC2 : ∀ j, w ≠ L.add.C2 j) (hanc : w ≠ L.add.anc) :
    denote (hornerStep L) s w = s w := by
  rw [hornerStep, denote_append]
  rw [cModAdd_preserves_external L.add _ w hAop haddB hctrl hCcadd hancC hA1 hC1 hA2 hC2 hanc]
  exact modDouble_preserves_external L.dbl s w hB hdAop hdCadd hdA1 hdC1 hdA2 hdC2 hdanc

/-! ### Value correctness of the Horner step -/

/-- **The verified Horner loop body** `acc ← (2·acc + [X_i]·Y) mod N`. For a `HornerStepLayout` with
the accumulator `B` holding `c < N`, the multiplicand register `Y = add.Aop` holding `Yval < N`,
`2N ≤ 2ⁿ`, **both** sub-layouts' presets (`A1 = 2ⁿ − N`, `A2 = N`), all carries / ancillas clean, and
the scratch operands of the doubling zeroed, `hornerStep L` leaves register `B` holding
`(2·c + (if X_i then Yval else 0)) mod N`.

Proof. The doubling step (`modDouble_correct` / `modDouble_in_range`) writes `(2c) mod N < N` to `B`,
preserves `Y`, `X_i`, and the controlled-add block's presets / clean carries / ancillas
(`modDouble_pres_add*`). The controlled add (`cModAdd_correct`) then writes
`if X_i then (Yval + (2c mod N)) mod N else (2c mod N)`. In the set branch
`Nat.add_mod_mod` absorbs the inner reduction: `(Yval + (2c mod N)) mod N = (Yval + 2c) mod N =
(2c + Yval) mod N`; in the clear branch `(2c) mod N = (2c + 0) mod N`. -/
theorem hornerStep_correct (L : HornerStepLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.dbl.Aop i) = false)
    (hCadd_dbl : ∀ j, s (L.dbl.addLayout.Cadd j) = false)
    (hC1_dbl : ∀ j, s (L.dbl.addLayout.C1 j) = false)
    (hC2_dbl : ∀ j, s (L.dbl.addLayout.C2 j) = false)
    (hanc_dbl : s L.dbl.addLayout.anc = false)
    (hCcadd : ∀ j, s (L.add.Ccadd j) = false) (hancC : s L.add.ancC = false)
    (hC1 : ∀ j, s (L.add.C1 j) = false) (hC2 : ∀ j, s (L.add.C2 j) = false)
    (hanc : s L.add.anc = false)
    {N c Yval : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1_dbl : regValRange L.dbl.addLayout.A1 s n = 2 ^ n - N)
    (hA2_dbl : regValRange L.dbl.addLayout.A2 s n = N)
    (hA1 : regValRange L.add.A1 s n = 2 ^ n - N) (hA2 : regValRange L.add.A2 s n = N)
    (hB : regValRange L.B s n = c) (hcN : c < N)
    (hY : regValRange L.Y s n = Yval) (hYN : Yval < N) :
    regValRange L.B (denote (hornerStep L) s) n
      = (2 * c + (if s L.add.ctrl then Yval else 0)) % N := by
  -- decompose at the doubling step
  set s' := denote (modDouble L.dbl) s with hs'def
  have hdenote : denote (hornerStep L) s = denote (cModAdd L.add) s' := by
    rw [hornerStep, denote_append, ← hs'def]
  rw [hdenote]
  -- DOUBLING STEP: B ← (2c) mod N, with (2c) mod N < N
  have hBd : regValRange L.dbl.B s n = c := by rw [show L.dbl.B = L.B from L.hBshared]; exact hB
  have hB' : regValRange L.add.B s' n = (2 * c) % N := by
    rw [hs'def, ← L.hBshared]
    exact modDouble_correct L.dbl s hAop0 hCadd_dbl hC1_dbl hC2_dbl hanc_dbl h2N hA1_dbl hA2_dbl
      hBd hcN
  have hBrange : (2 * c) % N < N := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le c) hcN)
  -- DOUBLING STEP frame: the controlled-add block's external wires survive
  have hAopcm : regValRange L.add.Aop s' n = Yval := by
    rw [← hY]; show regValRange L.add.Aop s' n = regValRange L.Y s n
    apply Finset.sum_congr rfl
    intro j _
    show (s' (L.add.Aop j)).toNat * 2 ^ j = (s (L.add.Aop j)).toNat * 2 ^ j
    rw [hs'def, modDouble_pres_addAop]
  have hA1cm : regValRange L.add.A1 s' n = 2 ^ n - N := by
    rw [← hA1]
    apply Finset.sum_congr rfl
    intro j _
    show (s' (L.add.A1 j)).toNat * 2 ^ j = (s (L.add.A1 j)).toNat * 2 ^ j
    rw [hs'def, modDouble_pres_addA1]
  have hA2cm : regValRange L.add.A2 s' n = N := by
    rw [← hA2]
    apply Finset.sum_congr rfl
    intro j _
    show (s' (L.add.A2 j)).toNat * 2 ^ j = (s (L.add.A2 j)).toNat * 2 ^ j
    rw [hs'def, modDouble_pres_addA2]
  have hCcaddcm : ∀ j, s' (L.add.Ccadd j) = false := by
    intro j; rw [hs'def, modDouble_pres_addCcadd]; exact hCcadd j
  have hancCcm : s' L.add.ancC = false := by rw [hs'def, modDouble_pres_addancC]; exact hancC
  have hC1cm : ∀ j, s' (L.add.C1 j) = false := by
    intro j; rw [hs'def, modDouble_pres_addC1]; exact hC1 j
  have hC2cm : ∀ j, s' (L.add.C2 j) = false := by
    intro j; rw [hs'def, modDouble_pres_addC2]; exact hC2 j
  have hanccm : s' L.add.anc = false := by rw [hs'def, modDouble_pres_addanc]; exact hanc
  have hctrlcm : s' L.add.ctrl = s L.add.ctrl := by rw [hs'def, modDouble_pres_addctrl]
  -- CONTROLLED ADD STEP: B ← if ctrl then (Yval + (2c)%N) % N else (2c)%N
  have hcm := cModAdd_correct L.add s' hCcaddcm hancCcm hC1cm hC2cm hanccm h2N hA1cm hA2cm
    hAopcm hB' hYN hBrange
  show regValRange L.B (denote (cModAdd L.add) s') n
      = (2 * c + (if s L.add.ctrl then Yval else 0)) % N
  rw [show L.B = L.add.B from rfl, hcm, hctrlcm]
  -- absorb the inner mod N and match the target form on each branch
  cases s L.add.ctrl with
  | true =>
    simp only [if_true]
    rw [Nat.add_mod_mod, Nat.add_comm Yval (2 * c)]
  | false =>
    simp only [Bool.false_eq_true, if_false, Nat.add_zero]

/-- **The Horner-step output is a genuine residue in `[0, N)`.** Corollary of `hornerStep_correct`
and `Nat.mod_lt`. -/
theorem hornerStep_in_range (L : HornerStepLayout m n) (s : State m)
    (hAop0 : ∀ i, i < n → s (L.dbl.Aop i) = false)
    (hCadd_dbl : ∀ j, s (L.dbl.addLayout.Cadd j) = false)
    (hC1_dbl : ∀ j, s (L.dbl.addLayout.C1 j) = false)
    (hC2_dbl : ∀ j, s (L.dbl.addLayout.C2 j) = false)
    (hanc_dbl : s L.dbl.addLayout.anc = false)
    (hCcadd : ∀ j, s (L.add.Ccadd j) = false) (hancC : s L.add.ancC = false)
    (hC1 : ∀ j, s (L.add.C1 j) = false) (hC2 : ∀ j, s (L.add.C2 j) = false)
    (hanc : s L.add.anc = false)
    {N c Yval : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hA1_dbl : regValRange L.dbl.addLayout.A1 s n = 2 ^ n - N)
    (hA2_dbl : regValRange L.dbl.addLayout.A2 s n = N)
    (hA1 : regValRange L.add.A1 s n = 2 ^ n - N) (hA2 : regValRange L.add.A2 s n = N)
    (hB : regValRange L.B s n = c) (hcN : c < N)
    (hY : regValRange L.Y s n = Yval) (hYN : Yval < N) (hNpos : 0 < N) :
    regValRange L.B (denote (hornerStep L) s) n < N := by
  rw [hornerStep_correct L s hAop0 hCadd_dbl hC1_dbl hC2_dbl hanc_dbl hCcadd hancC hC1 hC2 hanc
    h2N hA1_dbl hA2_dbl hA1 hA2 hB hcN hY hYN]
  exact Nat.mod_lt _ hNpos

/-- **The multiplicand `Y` is preserved.** `hornerStep L` leaves `Y = add.Aop` at its initial value:
the doubling block is disjoint from `Y` (`modDouble_pres_addAop`), and the controlled add reads `Y`
read-only (`cModAdd_preserves_operand`). This is the load-bearing persistence: the loop reuses the
SAME `Y` across all bit positions. -/
theorem hornerStep_preserves_Y (L : HornerStepLayout m n) (s : State m)
    (hCcadd : ∀ j, s (L.add.Ccadd j) = false) (hancC : s L.add.ancC = false) {Yval : ℕ}
    (hY : regValRange L.Y s n = Yval) :
    regValRange L.Y (denote (hornerStep L) s) n = Yval := by
  rw [← hY]
  set s' := denote (modDouble L.dbl) s with hs'def
  have hdenote : denote (hornerStep L) s = denote (cModAdd L.add) s' := by
    rw [hornerStep, denote_append, ← hs'def]
  rw [hdenote]
  -- Y survives the doubling (disjoint) ...
  have hYd : regValRange L.add.Aop s' n = regValRange L.add.Aop s n := by
    apply Finset.sum_congr rfl
    intro j _
    show (s' (L.add.Aop j)).toNat * 2 ^ j = (s (L.add.Aop j)).toNat * 2 ^ j
    rw [hs'def, modDouble_pres_addAop]
  -- ... and is read-only across the controlled add
  have hCcadd' : ∀ j, s' (L.add.Ccadd j) = false := by
    intro j; rw [hs'def, modDouble_pres_addCcadd]; exact hCcadd j
  have hancC' : s' L.add.ancC = false := by rw [hs'def, modDouble_pres_addancC]; exact hancC
  show regValRange L.add.Aop (denote (cModAdd L.add) s') n = regValRange L.Y s n
  rw [cModAdd_preserves_operand L.add s' hCcadd' hancC' hYd, show L.Y = L.add.Aop from rfl]

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the Horner step**: `30n` Toffolis, from the exhibited gate list.
Doubling step `12n` (`modDouble_toffoli`) + controlled add step `18n` (`cModularAdd_toffoli`),
composed through `cost_comp_toffoli_count`. -/
theorem hornerStep_toffoli (L : HornerStepLayout m n) :
    (circuitCost (hornerStep L)).toffoli = 30 * n := by
  rw [hornerStep, cost_comp_toffoli_count, modDouble_toffoli, cModularAdd_toffoli]
  omega

/-! ### 2-step composition: the verified `n = 2` modular multiply

Two Horner-step banks `L1` (high bit `X₁`) then `L2` (low bit `X₀`) sharing the accumulator `B` and
the multiplicand `Y`, with **fresh** per-bank scratch / carries / ancilla. Starting from `acc = 0`:

* step 1 leaves `acc₁ = (X₁·Yval) mod N` (`hornerStep_correct L1`, `c = 0`);
* step 2 leaves `acc₂ = (2·acc₁ + X₀·Yval) mod N = ((2·X₁ + X₀)·Yval) mod N = (X·Yval) mod N`
  (`hornerStep_correct L2`, `c = acc₁`), where `X = 2·X₁ + X₀` is the 2-bit multiplier.

The load-bearing inter-bank obligation is that bank 1 leaves bank 2's clean presets / scratch /
carries / ancilla and the low control bit `X₀` UNTOUCHED — taken here as the `hp_*` hypotheses, each
dischargeable from inter-bank disjointness via `hornerStep_preserves_external` (the fresh-wire model;
see the `mulCircuit2` `#eval` cross-check for a concrete instance that satisfies them). This exhibits
that the loop body composes; the general-`n` Horner induction is **S6.3d-2b**, NOT proved here. -/
theorem mulStep2_correct (L1 L2 : HornerStepLayout m n) (s : State m)
    -- the two banks share the accumulator and the multiplicand
    (hBshare : L2.B = L1.B) (hYshare : L2.Y = L1.Y)
    -- bank-1 hypotheses (its own clean presets / scratch / carries)
    (h1Aop0 : ∀ i, i < n → s (L1.dbl.Aop i) = false)
    (h1Cadd_dbl : ∀ j, s (L1.dbl.addLayout.Cadd j) = false)
    (h1C1_dbl : ∀ j, s (L1.dbl.addLayout.C1 j) = false)
    (h1C2_dbl : ∀ j, s (L1.dbl.addLayout.C2 j) = false)
    (h1anc_dbl : s L1.dbl.addLayout.anc = false)
    (h1Ccadd : ∀ j, s (L1.add.Ccadd j) = false) (h1ancC : s L1.add.ancC = false)
    (h1C1 : ∀ j, s (L1.add.C1 j) = false) (h1C2 : ∀ j, s (L1.add.C2 j) = false)
    (h1anc : s L1.add.anc = false)
    -- bank-2 hypotheses at the INITIAL state (transported through bank 1 by the hp_* facts)
    (h2Aop0 : ∀ i, i < n → s (L2.dbl.Aop i) = false)
    (h2Cadd_dbl : ∀ j, s (L2.dbl.addLayout.Cadd j) = false)
    (h2C1_dbl : ∀ j, s (L2.dbl.addLayout.C1 j) = false)
    (h2C2_dbl : ∀ j, s (L2.dbl.addLayout.C2 j) = false)
    (h2anc_dbl : s L2.dbl.addLayout.anc = false)
    (h2Ccadd : ∀ j, s (L2.add.Ccadd j) = false) (h2ancC : s L2.add.ancC = false)
    (h2C1 : ∀ j, s (L2.add.C1 j) = false) (h2C2 : ∀ j, s (L2.add.C2 j) = false)
    (h2anc : s L2.add.anc = false)
    {N Yval : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNpos : 0 < N)
    -- both banks' reduce presets
    (h1A1_dbl : regValRange L1.dbl.addLayout.A1 s n = 2 ^ n - N)
    (h1A2_dbl : regValRange L1.dbl.addLayout.A2 s n = N)
    (h1A1 : regValRange L1.add.A1 s n = 2 ^ n - N) (h1A2 : regValRange L1.add.A2 s n = N)
    (h2A1_dbl : regValRange L2.dbl.addLayout.A1 s n = 2 ^ n - N)
    (h2A2_dbl : regValRange L2.dbl.addLayout.A2 s n = N)
    (h2A1 : regValRange L2.add.A1 s n = 2 ^ n - N) (h2A2 : regValRange L2.add.A2 s n = N)
    -- the shared accumulator starts at 0; the shared multiplicand holds Yval < N
    (hB0 : regValRange L1.B s n = 0) (hY : regValRange L1.Y s n = Yval) (hYN : Yval < N)
    -- INTER-BANK: bank 1 leaves bank 2's clean presets / scratch / carries / low ctrl untouched
    (hp_2Aop : ∀ i, denote (hornerStep L1) s (L2.dbl.Aop i) = s (L2.dbl.Aop i))
    (hp_2dCadd : ∀ j, denote (hornerStep L1) s (L2.dbl.addLayout.Cadd j) = s (L2.dbl.addLayout.Cadd j))
    (hp_2dC1 : ∀ j, denote (hornerStep L1) s (L2.dbl.addLayout.C1 j) = s (L2.dbl.addLayout.C1 j))
    (hp_2dC2 : ∀ j, denote (hornerStep L1) s (L2.dbl.addLayout.C2 j) = s (L2.dbl.addLayout.C2 j))
    (hp_2danc : denote (hornerStep L1) s L2.dbl.addLayout.anc = s L2.dbl.addLayout.anc)
    (hp_2dA1 : ∀ j, denote (hornerStep L1) s (L2.dbl.addLayout.A1 j) = s (L2.dbl.addLayout.A1 j))
    (hp_2dA2 : ∀ j, denote (hornerStep L1) s (L2.dbl.addLayout.A2 j) = s (L2.dbl.addLayout.A2 j))
    (hp_2Ccadd : ∀ j, denote (hornerStep L1) s (L2.add.Ccadd j) = s (L2.add.Ccadd j))
    (hp_2ancC : denote (hornerStep L1) s L2.add.ancC = s L2.add.ancC)
    (hp_2C1 : ∀ j, denote (hornerStep L1) s (L2.add.C1 j) = s (L2.add.C1 j))
    (hp_2C2 : ∀ j, denote (hornerStep L1) s (L2.add.C2 j) = s (L2.add.C2 j))
    (hp_2anc : denote (hornerStep L1) s L2.add.anc = s L2.add.anc)
    (hp_2A1 : ∀ j, denote (hornerStep L1) s (L2.add.A1 j) = s (L2.add.A1 j))
    (hp_2A2 : ∀ j, denote (hornerStep L1) s (L2.add.A2 j) = s (L2.add.A2 j))
    (hp_2ctrl : denote (hornerStep L1) s L2.add.ctrl = s L2.add.ctrl)
    -- bank 1 preserves the multiplicand (read-only Y survives step 1)
    (h1Ccadd' : ∀ j, s (L1.add.Ccadd j) = false) (h1ancC' : s L1.add.ancC = false) :
    regValRange L2.B (denote (hornerStep L2) (denote (hornerStep L1) s)) n
      = ((2 * (if s L1.add.ctrl then 1 else 0) + (if s L2.add.ctrl then 1 else 0)) * Yval) % N := by
  set s1 := denote (hornerStep L1) s with hs1def
  -- STEP 1: acc₁ = (2·0 + X₁·Yval) mod N = (X₁·Yval) mod N  (c = 0)
  have hstep1 : regValRange L1.B s1 n = (if s L1.add.ctrl then Yval else 0) % N := by
    have := hornerStep_correct L1 s h1Aop0 h1Cadd_dbl h1C1_dbl h1C2_dbl h1anc_dbl h1Ccadd h1ancC
      h1C1 h1C2 h1anc h2N h1A1_dbl h1A2_dbl h1A1 h1A2 hB0 hNpos hY hYN
    simpa using this
  set acc1 := (if s L1.add.ctrl then Yval else 0) % N with hacc1def
  have hacc1N : acc1 < N := by rw [hacc1def]; exact Nat.mod_lt _ hNpos
  -- the shared accumulator value at s1 read through L2.B (= L1.B)
  have hB1 : regValRange L2.B s1 n = acc1 := by rw [show L2.B = L1.B from hBshare]; exact hstep1
  -- the shared multiplicand survives step 1, read through L2.Y (= L1.Y)
  have hY1 : regValRange L2.Y s1 n = Yval := by
    rw [show L2.Y = L1.Y from hYshare]
    exact hornerStep_preserves_Y L1 s h1Ccadd' h1ancC' hY
  -- bank-2 clean presets / scratch / carries survive step 1 (the hp_* facts)
  have h2Aop0' : ∀ i, i < n → s1 (L2.dbl.Aop i) = false := fun i hi => by
    rw [hp_2Aop]; exact h2Aop0 i hi
  have h2Cadd' : ∀ j, s1 (L2.dbl.addLayout.Cadd j) = false := fun j => by
    rw [hp_2dCadd]; exact h2Cadd_dbl j
  have h2C1d' : ∀ j, s1 (L2.dbl.addLayout.C1 j) = false := fun j => by
    rw [hp_2dC1]; exact h2C1_dbl j
  have h2C2d' : ∀ j, s1 (L2.dbl.addLayout.C2 j) = false := fun j => by
    rw [hp_2dC2]; exact h2C2_dbl j
  have h2ancd' : s1 L2.dbl.addLayout.anc = false := by rw [hp_2danc]; exact h2anc_dbl
  have h2Ccadd' : ∀ j, s1 (L2.add.Ccadd j) = false := fun j => by
    rw [hp_2Ccadd]; exact h2Ccadd j
  have h2ancC' : s1 L2.add.ancC = false := by rw [hp_2ancC]; exact h2ancC
  have h2C1' : ∀ j, s1 (L2.add.C1 j) = false := fun j => by
    rw [hp_2C1]; exact h2C1 j
  have h2C2' : ∀ j, s1 (L2.add.C2 j) = false := fun j => by
    rw [hp_2C2]; exact h2C2 j
  have h2anc' : s1 L2.add.anc = false := by rw [hp_2anc]; exact h2anc
  -- bank-2 presets (regValRange) survive step 1
  have h2A1d' : regValRange L2.dbl.addLayout.A1 s1 n = 2 ^ n - N := by
    rw [← h2A1_dbl]; exact Finset.sum_congr rfl fun j _ => by
      show (s1 (L2.dbl.addLayout.A1 j)).toNat * 2 ^ j = _
      rw [hp_2dA1]
  have h2A2d' : regValRange L2.dbl.addLayout.A2 s1 n = N := by
    rw [← h2A2_dbl]; exact Finset.sum_congr rfl fun j _ => by
      show (s1 (L2.dbl.addLayout.A2 j)).toNat * 2 ^ j = _
      rw [hp_2dA2]
  have h2A1' : regValRange L2.add.A1 s1 n = 2 ^ n - N := by
    rw [← h2A1]; exact Finset.sum_congr rfl fun j _ => by
      show (s1 (L2.add.A1 j)).toNat * 2 ^ j = _
      rw [hp_2A1]
  have h2A2' : regValRange L2.add.A2 s1 n = N := by
    rw [← h2A2]; exact Finset.sum_congr rfl fun j _ => by
      show (s1 (L2.add.A2 j)).toNat * 2 ^ j = _
      rw [hp_2A2]
  -- STEP 2: acc₂ = (2·acc₁ + X₀·Yval) mod N
  have hstep2 := hornerStep_correct L2 s1 h2Aop0' h2Cadd' h2C1d' h2C2d' h2ancd' h2Ccadd' h2ancC'
    h2C1' h2C2' h2anc' h2N h2A1d' h2A2d' h2A1' h2A2' hB1 hacc1N hY1 hYN
  rw [hstep2]
  -- bank-2 ctrl value at s1 = its value at s
  rw [show s1 L2.add.ctrl = s L2.add.ctrl by rw [hp_2ctrl]]
  -- arithmetic: (2·acc₁ + X₀·Yval) mod N = ((2·X₁ + X₀)·Yval) mod N. Reduce the `if`s, absorb the
  -- inner `mod N` on acc₁ (`Nat.zero_mod` / `Nat.mod_eq_of_lt hYN`), then equate the two `_ % N`
  -- arguments (`congr 1` + `omega`).
  rw [hacc1def]
  cases hX1 : s L1.add.ctrl <;> cases hX0 : s L2.add.ctrl <;>
    simp only [if_true, if_false, Bool.false_eq_true, Nat.zero_mod, Nat.mod_eq_of_lt hYN]
  all_goals first | rfl | (congr 1; omega)

/-! ### Concrete `#eval` cross-check: the verified `n = 2` modular multiply on `Fin 92`

Two Horner-step banks laid out on `Fin 92`, `n = 3` register width (forced by `2N ≤ 2ⁿ` for `N = 3`),
sharing the accumulator `B → {0,1,2}` and the multiplicand `Y → {3,4,5}`, with a 2-bit multiplier
`X` on the dedicated control wires `{6, 7}` (wire `6` = bank-1 control `X₁`, the HIGH bit; wire `7` =
bank-2 control `X₀`, the LOW bit). Every other wire family is FRESH per bank (the `Θ(n²)`-ancilla
fresh-wire model): bank 1 on `{8..49}`, bank 2 on `{50..91}`.

The full circuit is `modDouble dbl1 ++ cModAdd add1 ++ modDouble dbl2 ++ cModAdd add2` — exactly
`hornerStep` (bank 1) followed by `hornerStep` (bank 2). Reading register `B` (low 3 bits) off the
strict `Array Bool` evaluator (`runArr`, via the proven bridge `regValRangeArr_eq`) gives the value
the chained `hornerStep_correct` / `mulStep2_correct` constrain, computed instantly. The three
witnesses below realise `X · Yval mod N` for `Yval = 2`, `N = 3`: `X = 3 ↦ 0`, `X = 2 ↦ 1`,
`X = 1 ↦ 2`. -/

/-- Bank-1 doubling sub-layout (scratch `{8,9,10}`, carries/presets `{11..29}`). -/
def dbl1 : ModDoubleLayout 92 3 where
  addLayout :=
    { Aop i := if i = 0 then 8 else if i = 1 then 9 else 10
      B i := if i = 0 then 0 else if i = 1 then 1 else 2
      Cadd i := if i = 0 then 11 else if i = 1 then 12 else if i = 2 then 13 else 14
      A1 i := if i = 0 then 15 else if i = 1 then 16 else 17
      C1 i := if i = 0 then 18 else if i = 1 then 19 else if i = 2 then 20 else 21
      A2 i := if i = 0 then 22 else if i = 1 then 23 else 24
      C2 i := if i = 0 then 25 else if i = 1 then 26 else if i = 2 then 27 else 28
      anc := 29
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
      hAopanc i := by split_ifs <;> decide }

/-- Bank-1 controlled-add sub-layout (`Aop = Y → {3,4,5}`, `ctrl = 6`, carries/presets `{30..49}`). -/
def add1 : CModAddLayout 92 3 where
  Aop i := if i = 0 then 3 else if i = 1 then 4 else 5
  B i := if i = 0 then 0 else if i = 1 then 1 else 2
  Ccadd i := if i = 0 then 30 else if i = 1 then 31 else if i = 2 then 32 else 33
  ctrl := 6
  ancC := 34
  A1 i := if i = 0 then 35 else if i = 1 then 36 else 37
  C1 i := if i = 0 then 38 else if i = 1 then 39 else if i = 2 then 40 else 41
  A2 i := if i = 0 then 42 else if i = 1 then 43 else 44
  C2 i := if i = 0 then 45 else if i = 1 then 46 else if i = 2 then 47 else 48
  anc := 49
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

/-- Bank-2 doubling sub-layout (scratch `{50,51,52}`, carries/presets `{53..71}`). -/
def dbl2 : ModDoubleLayout 92 3 where
  addLayout :=
    { Aop i := if i = 0 then 50 else if i = 1 then 51 else 52
      B i := if i = 0 then 0 else if i = 1 then 1 else 2
      Cadd i := if i = 0 then 53 else if i = 1 then 54 else if i = 2 then 55 else 56
      A1 i := if i = 0 then 57 else if i = 1 then 58 else 59
      C1 i := if i = 0 then 60 else if i = 1 then 61 else if i = 2 then 62 else 63
      A2 i := if i = 0 then 64 else if i = 1 then 65 else 66
      C2 i := if i = 0 then 67 else if i = 1 then 68 else if i = 2 then 69 else 70
      anc := 71
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
      hAopanc i := by split_ifs <;> decide }

/-- Bank-2 controlled-add sub-layout (`Aop = Y → {3,4,5}`, `ctrl = 7`, carries/presets `{72..91}`). -/
def add2 : CModAddLayout 92 3 where
  Aop i := if i = 0 then 3 else if i = 1 then 4 else 5
  B i := if i = 0 then 0 else if i = 1 then 1 else 2
  Ccadd i := if i = 0 then 72 else if i = 1 then 73 else if i = 2 then 74 else 75
  ctrl := 7
  ancC := 76
  A1 i := if i = 0 then 77 else if i = 1 then 78 else 79
  C1 i := if i = 0 then 80 else if i = 1 then 81 else if i = 2 then 82 else 83
  A2 i := if i = 0 then 84 else if i = 1 then 85 else 86
  C2 i := if i = 0 then 87 else if i = 1 then 88 else if i = 2 then 89 else 90
  anc := 91
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

/-- The full 2-step modular-multiply circuit: bank-1 Horner step then bank-2 Horner step. -/
def mulCircuit2 : Circuit 92 :=
  modDouble dbl1 ++ cModAdd add1 ++ modDouble dbl2 ++ cModAdd add2

/-- Concrete input state on `Fin 92`: shared accumulator `B = 0` (wires `{0,1,2}`), multiplicand
`Y = (y0,y1,y2)` (wires `{3,4,5}`), 2-bit multiplier `X` = high bit `x1` (wire `6`) + low bit `x0`
(wire `7`); both banks' presets `A1 = 5 = 2³ − 3` and `A2 = 3`; all scratch / carries / ancillas
`false`. Parameterised by the data bits. -/
def mulState2 (y0 y1 y2 x1 x0 : Bool) : State 92 := fun w =>
  if w = 3 then y0 else if w = 4 then y1 else if w = 5 then y2          -- Y
  else if w = 6 then x1 else if w = 7 then x0                            -- X (high, low)
  else if w = 15 then true else if w = 17 then true                     -- bank1.dbl A1 = 5
  else if w = 22 then true else if w = 23 then true                     -- bank1.dbl A2 = 3
  else if w = 35 then true else if w = 37 then true                     -- bank1.add A1 = 5
  else if w = 42 then true else if w = 43 then true                     -- bank1.add A2 = 3
  else if w = 57 then true else if w = 59 then true                     -- bank2.dbl A1 = 5
  else if w = 64 then true else if w = 65 then true                     -- bank2.dbl A2 = 3
  else if w = 77 then true else if w = 79 then true                     -- bank2.add A1 = 5
  else if w = 84 then true else if w = 85 then true                     -- bank2.add A2 = 3
  else false

-- `X = 3 (bits 1,1), Y = 2, N = 3 ↦ (3·2) mod 3 = 0`. Prints `0`, instantly.
#eval regValRangeArr add2.B (runArr mulCircuit2 (ofState (mulState2 false true false true true))) 3
-- 0

-- `X = 2 (bits 1,0), Y = 2, N = 3 ↦ (2·2) mod 3 = 1`. Prints `1`, instantly.
#eval regValRangeArr add2.B (runArr mulCircuit2 (ofState (mulState2 false true false true false))) 3
-- 1

-- `X = 1 (bits 0,1), Y = 2, N = 3 ↦ (1·2) mod 3 = 2`. Prints `2`, instantly.
#eval regValRangeArr add2.B (runArr mulCircuit2 (ofState (mulState2 false true false false true))) 3
-- 2

-- Green, fast, theorem-independent value checks (kernel-reduced via the strict `Array` evaluator).
set_option maxRecDepth 8000 in
example : regValRangeArr add2.B
    (runArr mulCircuit2 (ofState (mulState2 false true false true true))) 3 = 0 := by decide

set_option maxRecDepth 8000 in
example : regValRangeArr add2.B
    (runArr mulCircuit2 (ofState (mulState2 false true false true false))) 3 = 1 := by decide

set_option maxRecDepth 8000 in
example : regValRangeArr add2.B
    (runArr mulCircuit2 (ofState (mulState2 false true false false true))) 3 = 2 := by decide

/-- The cross-check is faithful to the real `denote`-based semantics: by `regValRangeArr_eq`, the
fast `Array` value (`0`, above) *is* the `regValRange (denote …)` quantity the chained
`hornerStep_correct` / `mulStep2_correct` constrain. -/
example : regValRangeArr add2.B
    (runArr mulCircuit2 (ofState (mulState2 false true false true true))) 3
      = regValRange add2.B (denote mulCircuit2 (mulState2 false true false true true)) 3 :=
  regValRangeArr_eq add2.B mulCircuit2 (mulState2 false true false true true) 3

end Reversible
