/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.MultiControlled

/-!
# Controlled gates on a set of control qubits

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #83, the reachable core of the
re-split row #72 (`R-005`; `specs/magic-plan.md`, "The split").

One definition covers the whole gate vocabulary of the Clifford+T chain. For a control set `S`, a
target `j ∉ S` and a control pattern `pat`, `ctrlSet S j pat a b c d` applies the `2 × 2` block
`!![a, b; c, d]` to qubit `j` of those basis labels that match `pat` on `S`, and the identity on the
rest:

* `S = ∅` is a **single-qubit gate** (`singleGate`, and `xGate` for the bit flip);
* `S = {a}` with the flip block is **`CNOT`** (`cnotGate'`);
* `S = univ.erase j` is the **multiply-controlled gate** of #71 — ★ `ctrlSet_erase_eq_ctrlGate`
  identifies them, so the two-level theory of #70 and #71 applies verbatim.

The algebra is blockwise, and that is the point: ★★ `ctrlSet_mul` says controlled gates on a fixed
`(S, j, pat)` multiply by multiplying their `2 × 2` blocks, so they are a copy of the `2 × 2`
matrices inside the big matrix algebra; ★ `ctrlSet_conjTranspose` transposes the block,
`ctrlSet_one` is the identity, and hence ★ `ctrlSet_mem_unitaryGroup` — such a gate is unitary
exactly when its block is.

* `agree_off_iff`, `sum_collapse_update` — the two-element collapse every computation here uses;
* `ctrlSet`, its three entry lemmas, `ctrlSet_one`, ★★ `ctrlSet_mul`,
  ★ `ctrlSet_conjTranspose`, ★ `ctrlSet_mem_unitaryGroup`;
* `singleGate`, `xGate`, `cnotGate'` and their unitarity, `xGate_mul_self`;
  ★ `ctrlSet_erase_eq_ctrlGate`.

## Honest scope

⚠️ This is the vocabulary, not yet the decomposition. Writing a multiply-controlled gate as a
product of `CNOT`s and single-qubit gates needs three further pieces, and they are numbered: the
control pattern must be freed by conjugating with `X` gates on the control qubits, so that only the
*number* of controls matters (BACKLOG #83's companion, also #85); the `z`-`y`-`z` Euler decomposition
of a `2 × 2` unitary with the `ABC` identity for one control (#84, shared with #81); and the
control-count recursion through square roots (#85). The work-qubit ladder is **not** a substitute:
it reproduces a multiply-controlled gate only on the sector where the work qubits are `0`, not as a
matrix identity, which is what #73 consumes.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.3;
A. Barenco et al., PRA 52 (1995) 3457 §V–VII; `specs/magic-plan.md`; `specs/BACKLOG.md` #83, #84,
#85; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace Controlled

open TwoLevel MultiControlled

variable {m : ℕ}

/-! ### The two-element collapse -/

/-- A label agrees with `k` away from `j` exactly when it is one of the two labels obtained by
setting the `j`-th qubit. -/
theorem agree_off_iff {j : Fin m} {p k : Fin m → Fin 2} :
    (∀ i, i ≠ j → p i = k i) ↔ p = Function.update k j 0 ∨ p = Function.update k j 1 := by
  constructor
  · intro h
    rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (p j) with hpj | hpj
    · exact Or.inl (eq_update_iff.mpr ⟨h, hpj⟩)
    · exact Or.inr (eq_update_iff.mpr ⟨h, hpj⟩)
  · intro h i hi
    rcases h with h | h <;> rw [h, Function.update_of_ne hi]

/-- Every sum here collapses to the two labels that agree with `k` away from the target. -/
theorem sum_collapse_update (j : Fin m) (k : Fin m → Fin 2) (f : (Fin m → Fin 2) → ℂ)
    (hf : ∀ p, ¬(∀ i, i ≠ j → p i = k i) → f p = 0) :
    ∑ p, f p = f (Function.update k j 0) + f (Function.update k j 1) := by
  refine sum_eq_pair update_ne_update f fun p hp0 hp1 => hf p ?_
  intro hagree
  rcases agree_off_iff.mp hagree with h | h
  · exact hp0 h
  · exact hp1 h

/-! ### The controlled gate -/

/-- The gate controlled on the qubits of `S` with pattern `pat`, acting by the `2 × 2` block
`!![a, b; c, d]` on the target qubit `j`. -/
def ctrlSet (S : Finset (Fin m)) (j : Fin m) (pat : Fin m → Fin 2) (a b c d : ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := fun k l =>
  if (∀ i, i ≠ j → k i = l i) then
    (if ∀ i ∈ S, k i = pat i then blockEntry (k j) (l j) a b c d
      else if k j = l j then 1 else 0)
  else 0

variable {S : Finset (Fin m)} {j : Fin m} {pat : Fin m → Fin 2} {a b c d : ℂ}

theorem ctrlSet_apply_of_not_agree {k l : Fin m → Fin 2} (h : ¬(∀ i, i ≠ j → k i = l i)) :
    ctrlSet S j pat a b c d k l = 0 := by
  rw [ctrlSet, if_neg h]

theorem ctrlSet_apply_of_ctrl {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ j → k i = l i)
    (hc : ∀ i ∈ S, k i = pat i) :
    ctrlSet S j pat a b c d k l = blockEntry (k j) (l j) a b c d := by
  rw [ctrlSet, if_pos hag, if_pos hc]

theorem ctrlSet_apply_of_not_ctrl {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ j → k i = l i)
    (hc : ¬(∀ i ∈ S, k i = pat i)) :
    ctrlSet S j pat a b c d k l = if k j = l j then 1 else 0 := by
  rw [ctrlSet, if_pos hag, if_neg hc]

theorem ctrlSet_one (S : Finset (Fin m)) (j : Fin m) (pat : Fin m → Fin 2) :
    ctrlSet S j pat 1 0 0 1 = 1 := by
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · have hkl : k = l ↔ k j = l j := by
      constructor
      · intro h
        rw [h]
      · intro h
        funext i
        by_cases hi : i = j
        · rw [hi, h]
        · exact hag i hi
    by_cases hc : ∀ i ∈ S, k i = pat i
    · rw [ctrlSet_apply_of_ctrl hag hc, Matrix.one_apply, blockEntry]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k j) with hkj | hkj <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l j) with hlj | hlj <;>
        simp_all
    · rw [ctrlSet_apply_of_not_ctrl hag hc, Matrix.one_apply]
      by_cases h : k j = l j
      · rw [if_pos h, if_pos (hkl.mpr h)]
      · rw [if_neg h, if_neg (fun hc' => h (hkl.mp hc'))]
  · rw [ctrlSet_apply_of_not_agree hag, Matrix.one_apply, if_neg]
    intro h
    exact hag (fun i _ => by rw [h])

/-- ★ **Controlled gates on a fixed control set, target and pattern multiply blockwise.** -/
theorem ctrlSet_mul (hjS : j ∉ S) (a b c d a' b' c' d' : ℂ) :
    ctrlSet S j pat a b c d * ctrlSet S j pat a' b' c' d'
      = ctrlSet S j pat (a * a' + b * c') (a * b' + b * d') (c * a' + d * c')
          (c * b' + d * d') := by
  have hne : ∀ i ∈ S, i ≠ j := fun i hi hij => hjS (by rw [← hij]; exact hi)
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · -- the sum collapses to the two labels agreeing with `k` away from `j`
    have hcol : (ctrlSet S j pat a b c d * ctrlSet S j pat a' b' c' d') k l
        = ctrlSet S j pat a b c d k (Function.update k j 0) *
            ctrlSet S j pat a' b' c' d' (Function.update k j 0) l
          + ctrlSet S j pat a b c d k (Function.update k j 1) *
            ctrlSet S j pat a' b' c' d' (Function.update k j 1) l := by
      rw [Matrix.mul_apply]
      refine sum_collapse_update j k _ fun p hp => ?_
      rw [ctrlSet_apply_of_not_agree (fun hc => hp fun i hi => (hc i hi).symm), zero_mul]
    have hag0 : ∀ i, i ≠ j → k i = Function.update k j 0 i := fun i hi => by
      rw [Function.update_of_ne hi]
    have hag1 : ∀ i, i ≠ j → k i = Function.update k j 1 i := fun i hi => by
      rw [Function.update_of_ne hi]
    have hagl0 : ∀ i, i ≠ j → Function.update k j 0 i = l i := fun i hi => by
      rw [Function.update_of_ne hi]
      exact hag i hi
    have hagl1 : ∀ i, i ≠ j → Function.update k j 1 i = l i := fun i hi => by
      rw [Function.update_of_ne hi]
      exact hag i hi
    have hc0 : (∀ i ∈ S, Function.update k j 0 i = pat i) ↔ ∀ i ∈ S, k i = pat i := by
      constructor
      · intro h i hi
        rw [← Function.update_of_ne (hne i hi) (0 : Fin 2) k]
        exact h i hi
      · intro h i hi
        rw [Function.update_of_ne (hne i hi)]
        exact h i hi
    have hc1 : (∀ i ∈ S, Function.update k j 1 i = pat i) ↔ ∀ i ∈ S, k i = pat i := by
      constructor
      · intro h i hi
        rw [← Function.update_of_ne (hne i hi) (1 : Fin 2) k]
        exact h i hi
      · intro h i hi
        rw [Function.update_of_ne (hne i hi)]
        exact h i hi
    rw [hcol]
    by_cases hc : ∀ i ∈ S, k i = pat i
    · rw [ctrlSet_apply_of_ctrl hag0 hc, ctrlSet_apply_of_ctrl hag1 hc,
        ctrlSet_apply_of_ctrl hagl0 (hc0.mpr hc), ctrlSet_apply_of_ctrl hagl1 (hc1.mpr hc),
        ctrlSet_apply_of_ctrl hag hc]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k j) with hkj | hkj <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l j) with hlj | hlj <;>
        simp [hkj, hlj, blockEntry]
    · rw [ctrlSet_apply_of_not_ctrl hag0 hc, ctrlSet_apply_of_not_ctrl hag1 hc,
        ctrlSet_apply_of_not_ctrl hagl0 (fun hcc => hc (hc0.mp hcc)),
        ctrlSet_apply_of_not_ctrl hagl1 (fun hcc => hc (hc1.mp hcc)),
        ctrlSet_apply_of_not_ctrl hag hc]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k j) with hkj | hkj <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l j) with hlj | hlj <;>
        simp [hkj, hlj]
  · rw [ctrlSet_apply_of_not_agree hag, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : ∀ i, i ≠ j → k i = p i
    · rw [ctrlSet_apply_of_not_agree (fun hc => hag fun i hi => (hp i hi).trans (hc i hi)),
        mul_zero]
    · rw [ctrlSet_apply_of_not_agree hp, zero_mul]

theorem ctrlSet_conjTranspose (hjS : j ∉ S) (a b c d : ℂ) :
    (ctrlSet S j pat a b c d)ᴴ
      = ctrlSet S j pat (starRingEnd ℂ a) (starRingEnd ℂ c) (starRingEnd ℂ b)
          (starRingEnd ℂ d) := by
  have hne : ∀ i ∈ S, i ≠ j := fun i hi hij => hjS (by rw [← hij]; exact hi)
  ext k l
  rw [Matrix.conjTranspose_apply]
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · have hagsym : ∀ i, i ≠ j → l i = k i := fun i hi => (hag i hi).symm
    have hciff : (∀ i ∈ S, l i = pat i) ↔ ∀ i ∈ S, k i = pat i := by
      constructor
      · intro h i hi
        rw [hag i (hne i hi), h i hi]
      · intro h i hi
        rw [hagsym i (hne i hi), h i hi]
    by_cases hc : ∀ i ∈ S, k i = pat i
    · rw [ctrlSet_apply_of_ctrl hagsym (hciff.mpr hc), ctrlSet_apply_of_ctrl hag hc, blockEntry,
        blockEntry]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k j) with hkj | hkj <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l j) with hlj | hlj <;>
        simp_all
    · rw [ctrlSet_apply_of_not_ctrl hagsym (fun hcc => hc (hciff.mp hcc)),
        ctrlSet_apply_of_not_ctrl hag hc]
      by_cases h : k j = l j
      · rw [if_pos h, if_pos h.symm, star_one]
      · rw [if_neg h, if_neg (fun hc' => h hc'.symm), star_zero]
  · rw [ctrlSet_apply_of_not_agree hag, ctrlSet_apply_of_not_agree
      (fun hc => hag fun i hi => (hc i hi).symm), star_zero]

/-- ★ A controlled gate is unitary exactly when its block is. -/
theorem ctrlSet_mem_unitaryGroup (hjS : j ∉ S) {a b c d : ℂ}
    (h1 : starRingEnd ℂ a * a + starRingEnd ℂ c * c = 1)
    (h2 : starRingEnd ℂ b * b + starRingEnd ℂ d * d = 1)
    (h3 : starRingEnd ℂ a * b + starRingEnd ℂ c * d = 0)
    (h4 : starRingEnd ℂ b * a + starRingEnd ℂ d * c = 0) :
    ctrlSet S j pat a b c d ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show (ctrlSet S j pat a b c d)ᴴ * ctrlSet S j pat a b c d = 1
  rw [ctrlSet_conjTranspose hjS, ctrlSet_mul hjS, h1, h4, h3, h2, ctrlSet_one]

/-! ### The gate vocabulary -/

/-- A single-qubit gate: no controls. -/
def singleGate (j : Fin m) (a b c d : ℂ) : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  ctrlSet ∅ j (fun _ => 0) a b c d

/-- The single-qubit bit flip on qubit `j`. -/
def xGate (j : Fin m) : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := singleGate j 0 1 1 0

/-- `CNOT` with control `a` and target `b`: one control qubit. -/
def cnotGate' (a b : Fin m) : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  ctrlSet {a} b (fun _ => 1) 0 1 1 0

theorem singleGate_mem_unitaryGroup (j : Fin m) {a b c d : ℂ}
    (h1 : starRingEnd ℂ a * a + starRingEnd ℂ c * c = 1)
    (h2 : starRingEnd ℂ b * b + starRingEnd ℂ d * d = 1)
    (h3 : starRingEnd ℂ a * b + starRingEnd ℂ c * d = 0)
    (h4 : starRingEnd ℂ b * a + starRingEnd ℂ d * c = 0) :
    singleGate j a b c d ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  rw [singleGate]
  exact ctrlSet_mem_unitaryGroup (Finset.notMem_empty j) h1 h2 h3 h4

theorem xGate_mem_unitaryGroup (j : Fin m) :
    xGate j ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ :=
  singleGate_mem_unitaryGroup j (by simp) (by simp) (by simp) (by simp)

theorem xGate_mul_self (j : Fin m) : xGate j * xGate j = 1 := by
  rw [xGate, singleGate, ctrlSet_mul (Finset.notMem_empty j),
    show (0:ℂ) * 0 + 1 * 1 = 1 by norm_num,
    show (0:ℂ) * 1 + 1 * 0 = 0 by norm_num, show (1:ℂ) * 0 + 0 * 1 = 0 by norm_num,
    show (1:ℂ) * 1 + 0 * 0 = 1 by norm_num, ctrlSet_one]

theorem cnotGate'_mem_unitaryGroup (a b : Fin m) (hab : a ≠ b) :
    cnotGate' a b ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  rw [cnotGate']
  exact ctrlSet_mem_unitaryGroup (by simpa using Ne.symm hab) (by simp) (by simp) (by simp)
    (by simp)

/-- ★ **The full control set gives the multiply-controlled gate of #71**, so the two-level theory
of #70 and #71 applies to it verbatim. -/
theorem ctrlSet_erase_eq_ctrlGate (j : Fin m) (pat : Fin m → Fin 2) (a b c d : ℂ) :
    ctrlSet (Finset.univ.erase j) j pat a b c d = ctrlGate j pat a b c d := by
  ext k l
  have hmem : ∀ i : Fin m, i ∈ Finset.univ.erase j ↔ i ≠ j := by
    intro i
    simp
  by_cases hk : ∀ i, i ≠ j → k i = pat i
  · by_cases hl : ∀ i, i ≠ j → l i = pat i
    · have hag : ∀ i, i ≠ j → k i = l i := fun i hi => (hk i hi).trans (hl i hi).symm
      rw [ctrlSet_apply_of_ctrl hag (fun i hi => hk i ((hmem i).mp hi)), ctrlGate, if_pos ⟨hk, hl⟩]
    · have hag : ¬(∀ i, i ≠ j → k i = l i) := by
        intro hag
        exact hl fun i hi => (hag i hi).symm.trans (hk i hi)
      rw [ctrlSet_apply_of_not_agree hag, ctrlGate, if_neg (by tauto)]
      have hkl : k ≠ l := by
        intro h
        exact hag fun i _ => by rw [h]
      rw [if_neg hkl]
  · by_cases hl : ∀ i, i ≠ j → l i = pat i
    · have hag : ¬(∀ i, i ≠ j → k i = l i) := by
        intro hag
        exact hk fun i hi => (hag i hi).trans (hl i hi)
      rw [ctrlSet_apply_of_not_agree hag, ctrlGate, if_neg (by tauto)]
      have hkl : k ≠ l := by
        intro h
        exact hag fun i _ => by rw [h]
      rw [if_neg hkl]
    · rw [ctrlGate, if_neg (by tauto)]
      by_cases hag : ∀ i, i ≠ j → k i = l i
      · rw [ctrlSet_apply_of_not_ctrl hag (fun hc => hk fun i hi => hc i ((hmem i).mpr hi))]
        have hkl : k = l ↔ k j = l j := by
          constructor
          · intro h
            rw [h]
          · intro h
            funext i
            by_cases hi : i = j
            · rw [hi, h]
            · exact hag i hi
        by_cases h : k j = l j
        · rw [if_pos h, if_pos (hkl.mpr h)]
        · rw [if_neg h, if_neg (fun hc => h (hkl.mp hc))]
      · rw [ctrlSet_apply_of_not_agree hag, if_neg]
        intro h
        exact hag fun i _ => by rw [h]

end Controlled

end QuantumInfo

end
