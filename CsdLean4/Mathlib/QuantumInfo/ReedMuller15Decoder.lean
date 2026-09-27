/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ReedMuller15Errors
public import CsdLean4.Mathlib.QuantumInfo.ControlledGate

/-!
# The decoder of the `[[15, 1, 3]]` protocol as an explicit `CNOT` circuit

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #79, the last part of `R-004`'s
protocol (`specs/magic-plan.md`, "The split"): #77 read the output off the logical coefficients of
the accepted state, and this file decodes it with a circuit.

The `[15, 4]` simplex code has a **linear** logical-`Z` readout. Columns `1`, `2`, `3` of the
parity-check matrix sum to zero, so `f(x) = x₀ + x₁ + x₂` vanishes on every codeword
(`logicalBit_codeword`) and is `1` on the all-ones shift `codeword a + 𝟙` (`logicalBit_add_one`).
The decoder therefore needs **no Hadamard**: sixteen `CNOT`s suffice.

## The `CNOT` layer (general `m`, `namespace Controlled`)

`cnotAct a b` is the label action of `CNOT`, an involution once `a ≠ b` (`cnotAct_cnotAct`), and
★ `cnotGate'_apply` identifies #83's matrix as its permutation matrix — the bridge from the entry
algebra of `ControlledGate.lean` to a map on bitstrings, in the same shape as `xGate_apply`. On
amplitudes a `CNOT` is a pullback, ★ `cnotGate'_mulVec_apply`: `(C v)(k) = v (cnotAct a b k)`, and
★★ `cnotListMat_mulVec_apply` iterates that over a list of `CNOT`s (`cnotListMat`, the product with
the **first gate of the list rightmost**, unitary by `cnotListMat_mem_unitaryGroup`): the amplitude
map is the reversed composition `cnotListPull`.

## The decoder (`m = 15`)

* `decoderList` is the circuit: `CNOT(1 → 0)` and `CNOT(2 → 0)` compute the logical bit onto wire
  `0`, then `CNOT(0 → j)` for `j = 1, …, 14` clear the all-ones component from the other wires —
  sixteen gates (`decoderList_length`), and `decoderCircuit` is their product;
* ★ `cnotListPull_decoderList`: the circuit pulls labels back by `decodeLabelInv`, so
  ★★ `decoderCircuit_mulVec_apply` and `toEuclideanLin_decoderCircuit_apply` give every decoded
  amplitude as `(D ψ)(z) = ψ (decodeLabelInv z)`. `decodeLabelInv` is inverse to `decodeLabel`
  (`decodeLabel_decodeLabelInv`, `decodeLabelInv_decodeLabel`), which is the forward reading:
  ★ `decoderCircuit_mulVec_basisState`, `D|x⟩ = |decodeLabel x⟩`, the logical bit on wire `0` and
  the all-ones component cleared;
* ★★ `decoderCircuit_logical_update`: **wire `0` carries the logical qubit.** For every label `k` of
  the other fourteen wires the decoded amplitude at `k[0 ↦ 1]` is `λ` times the one at `k[0 ↦ 0]`,
  where `λ` is the logical coefficient of the input `|0̄⟩ + λ|1̄⟩`. The ratio is the same whatever the
  fourteen residual wires carry, which is why measuring them does not disturb wire `0`. The pair is
  not vacuous: `decoderCircuit_logical_apply_zero` gives amplitude `1` at the zero label;
* ★★★ `decoderCircuit_encodedMagic` and `decoderCircuit_encodedMagic_apply`: **the decoded output is
  #77's `outQubit e`.** For an undetected pattern `e` the amplitudes on wire `0` are those of
  `outQubit e = |0⟩ + (−1)^{|e|} e^{−iπ/4}|1⟩`, which is `√2 · Z^{|e|} T†|+⟩` (`outQubit_eq`) and
  the magic state up to the Clifford `S` (`sGate_magicConj`).

The mechanism in one line is `decodeLabelInv_update_one`:
`decodeLabelInv (k[0 ↦ 1]) = decodeLabelInv (k[0 ↦ 0]) + 𝟙`. The `1`-sector of wire `0` pulls back
to the coset `C + 𝟙`, which is exactly where `|1̄⟩` lives, and the `0`-sector pulls back into the
kernel of the readout, where `|1̄⟩` has no amplitude at all (`logical1_apply_of_logicalBit_zero`).

## Honest scope

⚠️ The fourteen residual wires are not exhibited as a tensor factor: what is proved is the
amplitude ratio at every residual label, the same statement in coordinates. A factorised form would
need the relabelling `(Fin 15 → Fin 2) ≃ Fin 2 × (Fin 14 → Fin 2)`.
⚠️ No measurement of the residual wires is modelled here; the row's "measures the fourteen syndrome
qubits" is covered only in the sense above, that the ratio does not depend on their label.
⚠️ The circuit is a product of `CNOT`s, hence Clifford, but the corpus has no `IsClifford`
predicate: the claim is carried by the explicit list `decoderList` and by unitarity
(`decoderCircuit_mem_unitaryGroup`). BACKLOG #79 priced a `CNOT`/`H` circuit; the Hadamard turned
out to be unnecessary for this code.
⚠️ Nothing here normalises anything: `logical0`, `logical1` and `outQubit` are the unnormalised
states of #76 and #77.

## Source

S. Bravyi, A. Kitaev, PRA 71 (2005) 022316 §IV; `QuantumInfo/ReedMuller15Code.lean` (#76),
`QuantumInfo/ReedMuller15Errors.lean` (#77), `QuantumInfo/ControlledGate.lean` (#83);
`specs/magic-plan.md`; `specs/BACKLOG.md` #79; `specs/future-work.md`.
-/

@[expose] public section

open Finset Matrix
open scoped ComplexConjugate

namespace QuantumInfo

namespace Controlled

open MultiControlled

/-! ### `CNOT` as a permutation of the computational basis -/

/-- The label action of `CNOT` with control `a` and target `b`: the target gains the control. -/
def cnotAct {m : ℕ} (a b : Fin m) (x : Fin m → Fin 2) : Fin m → Fin 2 :=
  Function.update x b (x b + x a)

@[simp] theorem cnotAct_apply_self {m : ℕ} (a b : Fin m) (x : Fin m → Fin 2) :
    cnotAct a b x b = x b + x a := by
  rw [cnotAct, Function.update_self]

theorem cnotAct_apply_of_ne {m : ℕ} {a b i : Fin m} (hi : i ≠ b) (x : Fin m → Fin 2) :
    cnotAct a b x i = x i := by
  rw [cnotAct, Function.update_of_ne hi]

/-- `CNOT` is an involution on labels. -/
@[simp] theorem cnotAct_cnotAct {m : ℕ} {a b : Fin m} (hab : a ≠ b) (x : Fin m → Fin 2) :
    cnotAct a b (cnotAct a b x) = x := by
  funext i
  by_cases hi : i = b
  · subst hi
    rw [cnotAct_apply_self, cnotAct_apply_self, cnotAct_apply_of_ne hab]
    generalize x i = p
    generalize x a = q
    revert p q
    decide
  · rw [cnotAct_apply_of_ne hi, cnotAct_apply_of_ne hi]

theorem cnotAct_eq_iff {m : ℕ} {a b : Fin m} (hab : a ≠ b) {k x : Fin m → Fin 2} :
    cnotAct a b k = x ↔ k = cnotAct a b x := by
  constructor
  · intro h
    rw [← h, cnotAct_cnotAct hab]
  · intro h
    rw [h, cnotAct_cnotAct hab]

/-- The `2 × 2` block of `CNOT` is the bit flip, read as a condition on the two labels. -/
theorem blockEntry_flip (p q : Fin 2) :
    blockEntry p q 0 1 1 0 = if q = p + 1 then (1 : ℂ) else 0 := by
  fin_cases p <;> fin_cases q <;> simp +decide [blockEntry]

/-- ★ **`CNOT` is the permutation matrix of `cnotAct`** — the same shape as `xGate_apply`. -/
theorem cnotGate'_apply {m : ℕ} {a b : Fin m} (hab : a ≠ b) (k l : Fin m → Fin 2) :
    cnotGate' a b k l = if l = cnotAct a b k then 1 else 0 := by
  by_cases hag : ∀ i, i ≠ b → k i = l i
  · have hiff : l = cnotAct a b k ↔ l b = k b + k a := by
      constructor
      · intro h
        rw [h, cnotAct_apply_self]
      · intro h
        funext i
        by_cases hi : i = b
        · subst hi
          rw [h, cnotAct_apply_self]
        · rw [cnotAct_apply_of_ne hi]
          exact (hag i hi).symm
    by_cases hctrl : k a = 1
    · rw [cnotGate', ctrlSet_apply_of_ctrl hag
        (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hctrl), blockEntry_flip]
      have hcond : (l b = k b + 1) ↔ (l = cnotAct a b k) := by rw [hiff, hctrl]
      by_cases h : l b = k b + 1
      · rw [if_pos h, if_pos (hcond.mp h)]
      · rw [if_neg h, if_neg (fun hk => h (hcond.mpr hk))]
    · have hka : k a = 0 := by
        rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (k a) with h | h
        · exact h
        · exact absurd h hctrl
      rw [cnotGate', ctrlSet_apply_of_not_ctrl hag
        (fun hc => hctrl (hc a (Finset.mem_singleton_self a)))]
      have hcond : (k b = l b) ↔ (l = cnotAct a b k) := by
        rw [hiff, hka, add_zero]
        exact eq_comm
      by_cases h : k b = l b
      · rw [if_pos h, if_pos (hcond.mp h)]
      · rw [if_neg h, if_neg (fun hk => h (hcond.mpr hk))]
  · rw [cnotGate', ctrlSet_apply_of_not_agree hag, if_neg]
    intro h
    exact hag fun i hi => by rw [h, cnotAct_apply_of_ne hi]

/-- ★ **`CNOT` on amplitudes is the pullback along `cnotAct`.** -/
theorem cnotGate'_mulVec_apply {m : ℕ} {a b : Fin m} (hab : a ≠ b)
    (v : (Fin m → Fin 2) → ℂ) (k : Fin m → Fin 2) :
    (cnotGate' a b *ᵥ v) k = v (cnotAct a b k) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (cnotAct a b k)]
  · rw [cnotGate'_apply hab, if_pos rfl, one_mul]
  · intro l _ hl
    rw [cnotGate'_apply hab, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### A list of `CNOT`s -/

/-- The matrix of a list of `CNOT`s: the **first gate of the list acts first**, so it is rightmost
in the product. -/
noncomputable def cnotListMat {m : ℕ} (l : List (Fin m × Fin m)) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  l.foldr (fun p M => M * cnotGate' p.1 p.2) 1

@[simp] theorem cnotListMat_nil {m : ℕ} :
    cnotListMat ([] : List (Fin m × Fin m)) = 1 := rfl

@[simp] theorem cnotListMat_cons {m : ℕ} (p : Fin m × Fin m) (l : List (Fin m × Fin m)) :
    cnotListMat (p :: l) = cnotListMat l * cnotGate' p.1 p.2 := rfl

/-- The label map a list of `CNOT`s pulls amplitudes back along: the reversed composition, so the
**last gate of the list is applied first**. -/
def cnotListPull {m : ℕ} (l : List (Fin m × Fin m)) (k : Fin m → Fin 2) : Fin m → Fin 2 :=
  l.foldr (fun p y => cnotAct p.1 p.2 y) k

@[simp] theorem cnotListPull_nil {m : ℕ} (k : Fin m → Fin 2) :
    cnotListPull [] k = k := rfl

@[simp] theorem cnotListPull_cons {m : ℕ} (p : Fin m × Fin m) (l : List (Fin m × Fin m))
    (k : Fin m → Fin 2) :
    cnotListPull (p :: l) k = cnotAct p.1 p.2 (cnotListPull l k) := rfl

/-- ★★ **A `CNOT` circuit acts on amplitudes as one label pullback.** -/
theorem cnotListMat_mulVec_apply {m : ℕ} :
    ∀ (l : List (Fin m × Fin m)), (∀ p ∈ l, p.1 ≠ p.2) →
      ∀ (v : (Fin m → Fin 2) → ℂ) (k : Fin m → Fin 2),
        (cnotListMat l *ᵥ v) k = v (cnotListPull l k) := by
  intro l
  induction l with
  | nil =>
      intro _ v k
      rw [cnotListMat_nil, Matrix.one_mulVec, cnotListPull_nil]
  | cons p l ih =>
      intro hl v k
      obtain ⟨a, b⟩ := p
      have hab : a ≠ b := hl (a, b) (List.mem_cons_self ..)
      rw [cnotListMat_cons, ← Matrix.mulVec_mulVec,
        ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ k,
        cnotGate'_mulVec_apply hab, cnotListPull_cons]

theorem cnotListMat_mem_unitaryGroup {m : ℕ} :
    ∀ (l : List (Fin m × Fin m)), (∀ p ∈ l, p.1 ≠ p.2) →
      cnotListMat l ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [cnotListMat_nil]
      exact one_mem _
  | cons p l ih =>
      intro hl
      obtain ⟨a, b⟩ := p
      rw [cnotListMat_cons]
      exact mul_mem (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
        (cnotGate'_mem_unitaryGroup a b (hl (a, b) (List.mem_cons_self ..)))

end Controlled

namespace ReedMuller15

open Controlled

/-! ### The logical readout of the simplex code -/

/-- The logical `Z` readout `f(x) = x₀ + x₁ + x₂`: zero on the code, one on its all-ones shift. -/
def logicalBit (x : Fin 15 → Fin 2) : Fin 2 := x 0 + x 1 + x 2

theorem logicalBit_add_one (x : Fin 15 → Fin 2) : logicalBit (x + 1) = logicalBit x + 1 := by
  rw [logicalBit, logicalBit]
  simp only [Pi.add_apply, Pi.one_apply]
  generalize x 0 = p
  generalize x 1 = q
  generalize x 2 = r
  revert p q r
  decide

/-- The readout vanishes on the code: columns `1`, `2`, `3` of the parity-check matrix sum to
zero. -/
theorem logicalBit_codeword (a : Fin 4 → Fin 2) : logicalBit (codeword a) = 0 := by
  revert a
  decide

theorem logicalBit_update_zero (k : Fin 15 → Fin 2) (v : Fin 2) :
    logicalBit (Function.update k 0 v) = v + k 1 + k 2 := by
  rw [logicalBit, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 15) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 15) ≠ 0)]

/-! ### The label map of the decoder and its inverse -/

/-- What the decoder does to a label: the readout onto wire `0`, cleared from the others. -/
def decodeLabel (x : Fin 15 → Fin 2) (j : Fin 15) : Fin 2 :=
  if j = 0 then logicalBit x else x j + logicalBit x

theorem decodeLabel_zero (x : Fin 15 → Fin 2) : decodeLabel x 0 = logicalBit x := by
  rw [decodeLabel, if_pos rfl]

theorem decodeLabel_of_ne {j : Fin 15} (hj : j ≠ 0) (x : Fin 15 → Fin 2) :
    decodeLabel x j = x j + logicalBit x := by
  rw [decodeLabel, if_neg hj]

/-- The inverse label map: wire `0` is added back to the others, and the readout of the *result*
lands on wire `0`. -/
def decodeLabelInv (y : Fin 15 → Fin 2) (j : Fin 15) : Fin 2 :=
  if j = 0 then logicalBit y else y j + y 0

theorem decodeLabelInv_zero (y : Fin 15 → Fin 2) : decodeLabelInv y 0 = logicalBit y := by
  rw [decodeLabelInv, if_pos rfl]

theorem decodeLabelInv_of_ne {j : Fin 15} (hj : j ≠ 0) (y : Fin 15 → Fin 2) :
    decodeLabelInv y j = y j + y 0 := by
  rw [decodeLabelInv, if_neg hj]

theorem logicalBit_decodeLabel (x : Fin 15 → Fin 2) : logicalBit (decodeLabel x) = x 0 := by
  rw [logicalBit, decodeLabel_zero, decodeLabel_of_ne (by decide : (1 : Fin 15) ≠ 0),
    decodeLabel_of_ne (by decide : (2 : Fin 15) ≠ 0), logicalBit]
  generalize x 0 = p
  generalize x 1 = q
  generalize x 2 = r
  revert p q r
  decide

theorem logicalBit_decodeLabelInv (y : Fin 15 → Fin 2) : logicalBit (decodeLabelInv y) = y 0 := by
  rw [logicalBit, decodeLabelInv_zero, decodeLabelInv_of_ne (by decide : (1 : Fin 15) ≠ 0),
    decodeLabelInv_of_ne (by decide : (2 : Fin 15) ≠ 0), logicalBit]
  generalize y 0 = p
  generalize y 1 = q
  generalize y 2 = r
  revert p q r
  decide

theorem decodeLabel_decodeLabelInv (y : Fin 15 → Fin 2) : decodeLabel (decodeLabelInv y) = y := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [decodeLabel_zero, logicalBit_decodeLabelInv]
  · rw [decodeLabel_of_ne hj, decodeLabelInv_of_ne hj, logicalBit_decodeLabelInv]
    generalize y j = p
    generalize y 0 = q
    revert p q
    decide

theorem decodeLabelInv_decodeLabel (x : Fin 15 → Fin 2) : decodeLabelInv (decodeLabel x) = x := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [decodeLabelInv_zero, logicalBit_decodeLabel]
  · rw [decodeLabelInv_of_ne hj, decodeLabel_of_ne hj, decodeLabel_zero]
    generalize x j = p
    generalize logicalBit x = q
    revert p q
    decide

/-! ### The circuit -/

/-- The targets of the clearing layer: every wire but `0`. -/
def cleanTargets : List (Fin 15) := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem mem_cleanTargets {j : Fin 15} (hj : j ≠ 0) : j ∈ cleanTargets := by
  revert j
  decide

/-- The decoder: `CNOT(1 → 0)` and `CNOT(2 → 0)` compute the logical bit onto wire `0`, then
`CNOT(0 → j)` clears it from every other wire. Sixteen gates, no Hadamard. -/
def decoderList : List (Fin 15 × Fin 15) :=
  (1, 0) :: (2, 0) :: cleanTargets.map fun t => ((0 : Fin 15), t)

theorem decoderList_length : decoderList.length = 16 := by decide

theorem ne_zero_of_mem_cleanTargets {t : Fin 15} (ht : t ∈ cleanTargets) : t ≠ 0 := by
  revert t
  decide

theorem decoderList_ne : ∀ p ∈ decoderList, p.1 ≠ p.2 := by
  intro p hp
  rw [decoderList, List.mem_cons, List.mem_cons] at hp
  rcases hp with h | h | h
  · rw [h]
    decide
  · rw [h]
    decide
  · obtain ⟨t, ht, hpt⟩ := List.mem_map.mp h
    rw [← hpt]
    exact Ne.symm (ne_zero_of_mem_cleanTargets ht)

/-- The decoder circuit, as the product of its sixteen `CNOT` matrices. -/
noncomputable def decoderCircuit : Matrix (Fin 15 → Fin 2) (Fin 15 → Fin 2) ℂ :=
  cnotListMat decoderList

theorem decoderCircuit_mem_unitaryGroup :
    decoderCircuit ∈ Matrix.unitaryGroup (Fin 15 → Fin 2) ℂ :=
  cnotListMat_mem_unitaryGroup decoderList decoderList_ne

/-- The clearing layer adds wire `0` to each of its targets. -/
theorem cnotListPull_clean : ∀ (l : List (Fin 15)), (0 : Fin 15) ∉ l → l.Nodup →
    ∀ (y : Fin 15 → Fin 2) (j : Fin 15),
      cnotListPull (l.map fun t => ((0 : Fin 15), t)) y j
        = if j ∈ l then y j + y 0 else y j := by
  intro l
  induction l with
  | nil =>
      intro _ _ y j
      rw [List.map_nil, cnotListPull_nil, if_neg List.not_mem_nil]
  | cons t l ih =>
      intro h0 hnd y j
      have htl : t ∉ l := (List.nodup_cons.mp hnd).1
      have hih := ih (fun h => h0 (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2 y
      rw [List.map_cons, cnotListPull_cons]
      have hz0 : cnotListPull (l.map fun t => ((0 : Fin 15), t)) y 0 = y 0 := by
        rw [hih 0, if_neg (fun h => h0 (List.mem_cons_of_mem _ h))]
      by_cases hj : j = t
      · subst hj
        rw [cnotAct_apply_self, hz0, hih j, if_neg htl, if_pos (List.mem_cons_self ..)]
      · rw [cnotAct_apply_of_ne hj, hih j]
        by_cases hjl : j ∈ l
        · rw [if_pos hjl, if_pos (List.mem_cons_of_mem _ hjl)]
        · rw [if_neg hjl, if_neg (fun h => by
            rcases List.mem_cons.mp h with h1 | h2
            · exact hj h1
            · exact hjl h2)]

/-- ★ **The circuit pulls labels back by `decodeLabelInv`.** -/
theorem cnotListPull_decoderList (y : Fin 15 → Fin 2) :
    cnotListPull decoderList y = decodeLabelInv y := by
  have hclean := cnotListPull_clean cleanTargets (by decide) (by decide) y
  funext j
  rw [decoderList, cnotListPull_cons, cnotListPull_cons]
  by_cases hj : j = 0
  · subst hj
    rw [cnotAct_apply_self, cnotAct_apply_self,
      cnotAct_apply_of_ne (by decide : (1 : Fin 15) ≠ 0), hclean 0, hclean 1, hclean 2,
      if_neg (by decide : (0 : Fin 15) ∉ cleanTargets),
      if_pos (by decide : (1 : Fin 15) ∈ cleanTargets),
      if_pos (by decide : (2 : Fin 15) ∈ cleanTargets), decodeLabelInv_zero, logicalBit]
    generalize y 0 = p
    generalize y 1 = q
    generalize y 2 = r
    revert p q r
    decide
  · rw [cnotAct_apply_of_ne hj, cnotAct_apply_of_ne hj, hclean j,
      if_pos (mem_cleanTargets hj), decodeLabelInv_of_ne hj]

/-- ★★ **Every decoded amplitude.** -/
theorem decoderCircuit_mulVec_apply (v : (Fin 15 → Fin 2) → ℂ) (z : Fin 15 → Fin 2) :
    (decoderCircuit *ᵥ v) z = v (decodeLabelInv z) := by
  rw [decoderCircuit, cnotListMat_mulVec_apply decoderList decoderList_ne v z,
    cnotListPull_decoderList]

/-- The same, on register states. -/
theorem toEuclideanLin_decoderCircuit_apply (ψ : QReg 15) (z : Fin 15 → Fin 2) :
    Matrix.toEuclideanLin decoderCircuit ψ z = ψ (decodeLabelInv z) :=
  decoderCircuit_mulVec_apply (WithLp.ofLp ψ) z

/-- ★ **The forward reading**: the circuit sends the basis label `x` to `decodeLabel x`, the logical
bit on wire `0` and the all-ones component cleared from the rest. -/
theorem decoderCircuit_mulVec_basisState (x : Fin 15 → Fin 2) :
    decoderCircuit *ᵥ WithLp.ofLp (basisState x)
      = WithLp.ofLp (basisState (decodeLabel x)) := by
  funext k
  rw [decoderCircuit_mulVec_apply]
  show basisState x (decodeLabelInv k) = basisState (decodeLabel x) k
  rw [basisState_apply, basisState_apply]
  refine if_congr ?_ rfl rfl
  constructor
  · intro h
    rw [← h, decodeLabel_decodeLabelInv]
  · intro h
    rw [h, decodeLabelInv_decodeLabel]

/-! ### The logical states under the decoder -/

theorem logical0_apply (x : Fin 15 → Fin 2) :
    logical0 x = ∑ a : Fin 4 → Fin 2, if x = codeword a then 1 else 0 := by
  rw [logical0, sum_coord]
  exact Finset.sum_congr rfl fun a _ => basisState_apply _ _

theorem logical1_apply (x : Fin 15 → Fin 2) :
    logical1 x = ∑ a : Fin 4 → Fin 2, if x = codeword a + 1 then 1 else 0 := by
  rw [logical1, sum_coord]
  exact Finset.sum_congr rfl fun a _ => basisState_apply _ _

/-- `|1̄⟩` has no amplitude where the readout vanishes: its labels are the coset `C + 𝟙`. -/
theorem logical1_apply_of_logicalBit_zero {x : Fin 15 → Fin 2} (hx : logicalBit x = 0) :
    logical1 x = 0 := by
  rw [logical1_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [if_neg]
  intro h
  rw [h, logicalBit_add_one, logicalBit_codeword] at hx
  exact absurd hx (by decide)

theorem logical0_apply_add_one (x : Fin 15 → Fin 2) : logical0 (x + 1) = logical1 x := by
  rw [logical0_apply, logical1_apply]
  refine Finset.sum_congr rfl fun a _ => if_congr ?_ rfl rfl
  constructor
  · intro h
    rw [← h, fin2_add_add_self]
  · intro h
    rw [h, fin2_add_add_self]

theorem logical1_apply_add_one (x : Fin 15 → Fin 2) : logical1 (x + 1) = logical0 x := by
  rw [logical0_apply, logical1_apply]
  refine Finset.sum_congr rfl fun a _ => if_congr ?_ rfl rfl
  constructor
  · intro h
    rw [← fin2_add_add_self x 1, h, fin2_add_add_self]
  · intro h
    rw [h]

theorem logical0_apply_zero : logical0 (0 : Fin 15 → Fin 2) = 1 := by
  have hz : codeword (0 : Fin 4 → Fin 2) = (0 : Fin 15 → Fin 2) := by decide
  rw [logical0_apply, Finset.sum_eq_single (0 : Fin 4 → Fin 2)]
  · rw [if_pos hz.symm]
  · intro a _ ha
    rw [if_neg]
    intro h
    exact ha (codeword_injective (h.symm.trans hz.symm))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Wire `0` carries the logical qubit -/

/-- **The mechanism.** The `1`-sector of wire `0` pulls back to the all-ones shift of the
`0`-sector — the coset `C + 𝟙`, which is where `|1̄⟩` lives. -/
theorem decodeLabelInv_update_one (k : Fin 15 → Fin 2) :
    decodeLabelInv (Function.update k 0 1)
      = decodeLabelInv (Function.update k 0 0) + 1 := by
  funext j
  rw [Pi.add_apply, Pi.one_apply]
  by_cases hj : j = 0
  · subst hj
    rw [decodeLabelInv_zero, decodeLabelInv_zero, logicalBit_update_zero,
      logicalBit_update_zero]
    generalize k 1 = q
    generalize k 2 = r
    revert q r
    decide
  · rw [decodeLabelInv_of_ne hj, decodeLabelInv_of_ne hj, Function.update_of_ne hj,
      Function.update_of_ne hj, Function.update_self, Function.update_self]
    generalize k j = p
    revert p
    decide

theorem decodeLabelInv_zero_label : decodeLabelInv (0 : Fin 15 → Fin 2) = 0 := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [decodeLabelInv_zero, logicalBit]
    rfl
  · rw [decodeLabelInv_of_ne hj]
    rfl

/-- ★★ **The decoded state carries the logical qubit on wire `0`.** Whatever the other fourteen
wires do, the amplitude in the `1`-sector of wire `0` is `λ` times the amplitude in the `0`-sector:
the decoded state is `|0⟩ + λ|1⟩` on wire `0`, uniformly in the residual label. -/
theorem decoderCircuit_logical_update (lam : ℂ) (k : Fin 15 → Fin 2) :
    Matrix.toEuclideanLin decoderCircuit (logical0 + lam • logical1) (Function.update k 0 1)
      = lam * Matrix.toEuclideanLin decoderCircuit (logical0 + lam • logical1)
          (Function.update k 0 0) := by
  have hbit : logicalBit (decodeLabelInv (Function.update k 0 0)) = 0 := by
    rw [logicalBit_decodeLabelInv, Function.update_self]
  have h1 : logical1 (decodeLabelInv (Function.update k 0 0)) = 0 :=
    logical1_apply_of_logicalBit_zero hbit
  rw [toEuclideanLin_decoderCircuit_apply, toEuclideanLin_decoderCircuit_apply,
    decodeLabelInv_update_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, logical0_apply_add_one, logical1_apply_add_one, h1]
  ring

/-- The pair above is not vacuous: the `0`-sector carries amplitude `1` at the zero label. -/
theorem decoderCircuit_logical_apply_zero (lam : ℂ) :
    Matrix.toEuclideanLin decoderCircuit (logical0 + lam • logical1)
        (0 : Fin 15 → Fin 2) = 1 := by
  have hbit : logicalBit (0 : Fin 15 → Fin 2) = 0 := by
    rw [logicalBit]
    rfl
  rw [toEuclideanLin_decoderCircuit_apply, decodeLabelInv_zero_label, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, logical0_apply_zero,
    logical1_apply_of_logicalBit_zero hbit, mul_zero, add_zero]

/-! ### The decoded output of the protocol -/

theorem outQubit_apply_zero (e : Fin 15 → Fin 2) : outQubit e (fun _ => 0) = 1 := by
  rw [outQubit, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, basisState_apply, basisState_apply,
    if_pos rfl, if_neg (by decide : ¬((fun _ => (0 : Fin 2)) = (fun _ => (1 : Fin 2)))),
    mul_zero, add_zero]

theorem outQubit_apply_one (e : Fin 15 → Fin 2) :
    outQubit e (fun _ => 1) = signChar (parity e) * tPhaseInv := by
  rw [outQubit, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, basisState_apply, basisState_apply,
    if_pos rfl, if_neg (by decide : ¬((fun _ => (1 : Fin 2)) = (fun _ => (0 : Fin 2)))),
    mul_one, zero_add]

/-- ★★★ **The decoder outputs `outQubit e` on wire `0`.** For an undetected pattern `e`, the decoded
amplitudes of the accepted state on wire `0` are exactly those of #77's
`outQubit e = |0⟩ + (−1)^{|e|} e^{−iπ/4}|1⟩`, at every label of the other fourteen wires. -/
theorem decoderCircuit_encodedMagic {e : Fin 15 → Fin 2} (he : syndromeF e = 0)
    (k : Fin 15 → Fin 2) (v : Fin 2) :
    Matrix.toEuclideanLin decoderCircuit (pauliOp 0 e (tTrans logicalPlus))
        (Function.update k 0 v)
      = outQubit e (fun _ => v)
        * Matrix.toEuclideanLin decoderCircuit (pauliOp 0 e (tTrans logicalPlus))
            (Function.update k 0 0) := by
  rw [pauliOp_z_encodedMagic he]
  rcases (by decide : ∀ w : Fin 2, w = 0 ∨ w = 1) v with hv | hv
  · rw [hv, outQubit_apply_zero, one_mul]
  · rw [hv, outQubit_apply_one, decoderCircuit_logical_update]

/-- ★★★ **The output qubit, with its amplitudes.** At the zero label of the other fourteen wires the
decoded amplitudes *are* those of `outQubit e`: the protocol's output is `√2 · Z^{|e|} T†|+⟩`
(`outQubit_eq`), the magic state up to the Clifford `S` (`sGate_magicConj`). -/
theorem decoderCircuit_encodedMagic_apply {e : Fin 15 → Fin 2} (he : syndromeF e = 0)
    (v : Fin 2) :
    Matrix.toEuclideanLin decoderCircuit (pauliOp 0 e (tTrans logicalPlus))
        (Function.update (0 : Fin 15 → Fin 2) 0 v) = outQubit e (fun _ => v) := by
  have hupd : Function.update (0 : Fin 15 → Fin 2) 0 0 = 0 := by
    funext j
    by_cases hj : j = 0
    · rw [hj, Function.update_self]
      rfl
    · rw [Function.update_of_ne hj]
  rw [decoderCircuit_encodedMagic he 0 v, pauliOp_z_encodedMagic he, hupd,
    decoderCircuit_logical_apply_zero, mul_one]

end ReedMuller15

end QuantumInfo
