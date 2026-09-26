/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ControlledGate
public import CsdLean4.Mathlib.QuantumInfo.EulerDecomposition

/-!
# One control: `C¹(U)` from two `CNOT`s and single-qubit gates

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #84, part (e2) of `R-005`
(`specs/magic-plan.md`, "The split"), the circuit half; the `2 × 2` half is
`EulerDecomposition.lean`.

Nielsen–Chuang Figure 4.6: **a gate with one control is a product of two `CNOT`s and four
single-qubit gates** — ★★ `ctrlOf_eq_circuit`. The mechanism is the `ABC` identity of
`EulerDecomposition.lean`: on the control bit `0` the two `CNOT`s act trivially and the target sees
`A B C = 1`, on the control bit `1` they each insert an `X` and it sees `e^{iα} A X B X C = U`.

The proof needs one piece of gate algebra, and that piece is the content of this file. `ctrlChoice`
is the family of gates that apply the `2 × 2` block `M b` to the target when the control carries
the bit `b`. It is **closed under products, blockwise in each branch separately** (★★
`ctrlChoice_mul`), and it contains every gate the circuit uses:

* a single-qubit gate on the *target* is `ctrlChoice` with a constant family
  (`gateOf_eq_ctrlChoice`);
* a *diagonal* single-qubit gate on the *control* is `ctrlChoice` with scalar branches
  (★ `diagGate_eq_ctrlChoice`) — the one place the control qubit is addressed;
* `CNOT` is `ctrlChoice` with branches `1` and `X` (`cnotGate'_eq_ctrlChoice`);
* the one-control gate itself is `ctrlChoice` with branches `1` and `U`
  (`ctrlOf_eq_ctrlChoice`).

So the whole circuit collapses to one `ctrlChoice`, and the identity is checked one control bit at
a time. `gateOf` and `ctrlOf` are #83's `singleGate` and `ctrlSet {a} j` addressed by a `2 × 2`
matrix instead of four scalars (`blockEntry_eq_apply` is the bridge).

* `ctrlChoice`, `ctrlChoice_apply_of_agree`, `ctrlChoice_apply_of_not_agree`, `ctrlChoice_one`,
  ★★ `ctrlChoice_mul`;
* `blockEntry_eq_apply`, `gateOf`, `ctrlOf`, `unitary_entries`, `gateOf_mem_unitaryGroup`,
  `ctrlOf_mem_unitaryGroup`;
* `gateOf_eq_ctrlChoice`, `diagGate_apply`, `ctrlChoice_diag_apply`, ★ `diagGate_eq_ctrlChoice`,
  `cnotGate'_eq_ctrlChoice`,
  ★ `ctrlOf_eq_ctrlChoice`;
* ★★ `ctrlOf_eq_circuit`.

## Honest scope

⚠️ One control. The control-count recursion (`C^k(U)` from `C^{k-1}(√U)`) and the pattern
normalisation that frees the control values are BACKLOG #85; `ctrlChoice_mul` is the algebra they
will be stated in.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.3
(Figure 4.6 and Corollary 4.2); `CsdLean4/Mathlib/QuantumInfo/ControlledGate.lean` for the gate
vocabulary; `specs/magic-plan.md`; `specs/BACKLOG.md` #84, #85; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace Controlled

open TwoLevel MultiControlled Euler

variable {m : ℕ}

/-! ### The one-control gate family -/

/-- The gate that applies the `2 × 2` block `M b` to the target qubit `j` of those basis labels
whose control qubit `a` carries the bit `b`. -/
def ctrlChoice (a j : Fin m) (M : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := fun k l =>
  if (∀ i, i ≠ j → k i = l i) then M (k a) (k j) (l j) else 0

variable {a j : Fin m} {M N : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}

theorem ctrlChoice_apply_of_agree {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ j → k i = l i) :
    ctrlChoice a j M k l = M (k a) (k j) (l j) := by
  rw [ctrlChoice, if_pos hag]

theorem ctrlChoice_apply_of_not_agree {k l : Fin m → Fin 2} (h : ¬(∀ i, i ≠ j → k i = l i)) :
    ctrlChoice a j M k l = 0 := by
  rw [ctrlChoice, if_neg h]

theorem ctrlChoice_one (a j : Fin m) : ctrlChoice a j (fun _ => 1) = 1 := by
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
    rw [ctrlChoice_apply_of_agree hag, Matrix.one_apply, Matrix.one_apply]
    by_cases h : k j = l j
    · rw [if_pos h, if_pos (hkl.mpr h)]
    · rw [if_neg h, if_neg fun hc => h (hkl.mp hc)]
  · rw [ctrlChoice_apply_of_not_agree hag, Matrix.one_apply, if_neg]
    intro h
    exact hag fun i _ => by rw [h]

/-- ★★ **One-control gates multiply blockwise, in each branch separately.** The control bit is
untouched by both factors, so the two branches never mix: this is the algebra every circuit
identity with one control is checked in. -/
theorem ctrlChoice_mul (haj : a ≠ j) (M N : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlChoice a j M * ctrlChoice a j N = ctrlChoice a j (fun b => M b * N b) := by
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · have hcol : (ctrlChoice a j M * ctrlChoice a j N) k l
        = ctrlChoice a j M k (Function.update k j 0)
            * ctrlChoice a j N (Function.update k j 0) l
          + ctrlChoice a j M k (Function.update k j 1)
            * ctrlChoice a j N (Function.update k j 1) l := by
      rw [Matrix.mul_apply]
      refine sum_collapse_update j k _ fun p hp => ?_
      rw [ctrlChoice_apply_of_not_agree (fun hc => hp fun i hi => (hc i hi).symm), zero_mul]
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
    rw [hcol, ctrlChoice_apply_of_agree hag0, ctrlChoice_apply_of_agree hag1,
      ctrlChoice_apply_of_agree hagl0, ctrlChoice_apply_of_agree hagl1,
      ctrlChoice_apply_of_agree hag, Function.update_of_ne haj, Function.update_of_ne haj]
    simp only [Function.update_self, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [ctrlChoice_apply_of_not_agree hag, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : ∀ i, i ≠ j → k i = p i
    · rw [ctrlChoice_apply_of_not_agree
        (fun hc => hag fun i hi => (hp i hi).trans (hc i hi)), mul_zero]
    · rw [ctrlChoice_apply_of_not_agree hp, zero_mul]

/-! ### The vocabulary of #83, addressed by a `2 × 2` matrix -/

theorem blockEntry_eq_apply (p q : Fin 2) (x y z w : ℂ) :
    blockEntry p q x y z w = !![x, y; z, w] p q := by
  fin_cases p <;> fin_cases q <;> simp [blockEntry]

/-- The single-qubit gate on `j` given by a `2 × 2` matrix. -/
def gateOf (j : Fin m) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  singleGate j (M 0 0) (M 0 1) (M 1 0) (M 1 1)

/-- The gate `M` on qubit `j` controlled by qubit `a`. -/
def ctrlOf (a j : Fin m) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  ctrlSet {a} j (fun _ => 1) (M 0 0) (M 0 1) (M 1 0) (M 1 1)

/-- Unitarity of a `2 × 2` matrix, entry by entry — the form #83's gates ask for. -/
theorem unitary_entries {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    starRingEnd ℂ (M 0 0) * M 0 0 + starRingEnd ℂ (M 1 0) * M 1 0 = 1 ∧
      starRingEnd ℂ (M 0 1) * M 0 1 + starRingEnd ℂ (M 1 1) * M 1 1 = 1 ∧
        starRingEnd ℂ (M 0 0) * M 0 1 + starRingEnd ℂ (M 1 0) * M 1 1 = 0 ∧
          starRingEnd ℂ (M 0 1) * M 0 0 + starRingEnd ℂ (M 1 1) * M 1 0 = 0 := by
  have h : Mᴴ * M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hM
  have key : ∀ i i' : Fin 2, starRingEnd ℂ (M 0 i) * M 0 i' + starRingEnd ℂ (M 1 i) * M 1 i'
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) i i' := by
    intro i i'
    have h2 := congrFun (congrFun h i) i'
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.conjTranspose_apply, ← starRingEnd_apply, ← starRingEnd_apply] at h2
    exact h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key 0 0, Matrix.one_apply_eq]
  · rw [key 1 1, Matrix.one_apply_eq]
  · rw [key 0 1, Matrix.one_apply_ne (by decide)]
  · rw [key 1 0, Matrix.one_apply_ne (by decide)]

theorem gateOf_mem_unitaryGroup (j : Fin m) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    gateOf j M ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  obtain ⟨h1, h2, h3, h4⟩ := unitary_entries hM
  exact singleGate_mem_unitaryGroup j h1 h2 h3 h4

theorem ctrlOf_mem_unitaryGroup (haj : a ≠ j) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ctrlOf a j M ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  obtain ⟨h1, h2, h3, h4⟩ := unitary_entries hM
  exact ctrlSet_mem_unitaryGroup (by simpa using Ne.symm haj) h1 h2 h3 h4

/-! ### Every gate of the circuit is a `ctrlChoice` -/

theorem gateOf_eq_ctrlChoice (M : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf j M = ctrlChoice a j (fun _ => M) := by
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · rw [gateOf, singleGate, ctrlSet_apply_of_ctrl hag (by simp),
      ctrlChoice_apply_of_agree hag, blockEntry_eq_apply, ← Matrix.eta_fin_two M]
  · rw [gateOf, singleGate, ctrlSet_apply_of_not_agree hag, ctrlChoice_apply_of_not_agree hag]

/-- A diagonal single-qubit gate is diagonal on basis labels, with the value read off the qubit it
acts on. -/
theorem diagGate_apply (p q : ℂ) (k l : Fin m → Fin 2) :
    singleGate a p 0 0 q k l = if k = l then (if k a = 0 then p else q) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [singleGate, ctrlSet_apply_of_ctrl (fun i _ => rfl) (by simp), if_pos rfl, blockEntry]
    rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with h | h <;> rw [h] <;> simp
  · rw [if_neg hkl, singleGate]
    by_cases hag : ∀ i, i ≠ a → k i = l i
    · have hka : k a ≠ l a := fun hi => hkl (funext fun i' => by
        by_cases h : i' = a
        · rw [h, hi]
        · exact hag i' h)
      rw [ctrlSet_apply_of_ctrl hag (by simp)]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with h | h <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l a) with h' | h' <;>
        simp_all [blockEntry]
    · rw [ctrlSet_apply_of_not_agree hag]

/-- The same shape for the one-control gate whose branches are scalars. -/
theorem ctrlChoice_diag_apply (p q : ℂ) (k l : Fin m → Fin 2) :
    ctrlChoice a j (fun b => if b = 0 then p • (1 : Matrix (Fin 2) (Fin 2) ℂ) else q • 1) k l
      = if k = l then (if k a = 0 then p else q) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ctrlChoice_apply_of_agree (fun i _ => rfl), if_pos rfl]
    rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with h | h <;> rw [h] <;> simp
  · rw [if_neg hkl]
    by_cases hag : ∀ i, i ≠ j → k i = l i
    · have hkj : k j ≠ l j := fun hi => hkl (funext fun i' => by
        by_cases h : i' = j
        · rw [h, hi]
        · exact hag i' h)
      rw [ctrlChoice_apply_of_agree hag]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with h | h <;> rw [h] <;>
        simp [Matrix.one_apply_ne hkj]
    · rw [ctrlChoice_apply_of_not_agree hag]

/-- ★ A **diagonal** single-qubit gate on the control qubit is a one-control gate with scalar
branches. This is the only place the control qubit is addressed directly, and it is how the global
phase of the `ABC` identity enters the circuit. -/
theorem diagGate_eq_ctrlChoice (p q : ℂ) :
    singleGate a p 0 0 q
      = ctrlChoice a j (fun b => if b = 0 then p • (1 : Matrix (Fin 2) (Fin 2) ℂ) else q • 1) := by
  ext k l
  rw [diagGate_apply, ctrlChoice_diag_apply]

theorem ctrlOf_eq_ctrlChoice (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlOf a j M = ctrlChoice a j (fun b => if b = 0 then 1 else M) := by
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with hka | hka
    · rw [ctrlOf, ctrlSet_apply_of_not_ctrl hag (by simp [hka]),
        ctrlChoice_apply_of_agree hag, hka, if_pos rfl, Matrix.one_apply]
    · rw [ctrlOf, ctrlSet_apply_of_ctrl hag (by simp [hka]), ctrlChoice_apply_of_agree hag, hka,
        if_neg (show ¬((1 : Fin 2) = 0) by decide), blockEntry_eq_apply, ← Matrix.eta_fin_two M]
  · rw [ctrlOf, ctrlSet_apply_of_not_agree hag, ctrlChoice_apply_of_not_agree hag]

theorem cnotGate'_eq_ctrlChoice (a j : Fin m) :
    cnotGate' a j = ctrlChoice a j (fun b => if b = 0 then 1 else xMat) := by
  rw [show cnotGate' a j = ctrlOf a j xMat by simp [cnotGate', ctrlOf, xMat],
    ctrlOf_eq_ctrlChoice xMat]

/-! ### The circuit -/

/-- ★★ **A gate with one control is a product of two `CNOT`s and four single-qubit gates**
(Nielsen–Chuang Figure 4.6). The phase of the `ABC` identity rides on the control line as the
diagonal gate `diag (1, e^{iα})`; the control bit `0` leaves the target `A B C = 1`, and the control
bit `1` inserts the two `X`s, leaving it `e^{iα} A X B X C = U`. -/
theorem ctrlOf_eq_circuit (haj : a ≠ j) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ A * B * C = 1 ∧
          ctrlOf a j U = singleGate a 1 0 0 (expI α) * gateOf j A * cnotGate' a j * gateOf j B
              * cnotGate' a j * gateOf j C := by
  obtain ⟨α, A, B, C, hA, hB, hC, habc, hUeq⟩ := exists_abc hU
  refine ⟨α, A, B, C, hA, hB, hC, habc, ?_⟩
  rw [ctrlOf_eq_ctrlChoice U, diagGate_eq_ctrlChoice (j := j) 1 (expI α),
    gateOf_eq_ctrlChoice (a := a) A, cnotGate'_eq_ctrlChoice a j,
    gateOf_eq_ctrlChoice (a := a) B, gateOf_eq_ctrlChoice (a := a) C,
    ctrlChoice_mul haj, ctrlChoice_mul haj, ctrlChoice_mul haj, ctrlChoice_mul haj,
    ctrlChoice_mul haj]
  congr 1
  funext b
  rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) b with hb | hb
  · rw [hb]
    simp only [reduceIte, one_smul, one_mul, mul_one]
    exact habc.symm
  · rw [hb]
    repeat rw [if_neg (show ¬((1 : Fin 2) = 0) by decide)]
    rw [hUeq]
    simp only [Matrix.smul_mul, one_mul]

end Controlled

end QuantumInfo
