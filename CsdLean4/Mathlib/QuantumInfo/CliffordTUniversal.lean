/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ControlRecursion
public import CsdLean4.Mathlib.QuantumInfo.CliffordTDensity

/-!
# Clifford+T is universal: dense in `U(2ⁿ)` modulo phase

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #73, part (f) of `R-005`, **which
it closes**: the last residue of the quantum-computing chain that had a Lean shape.

★★ `exists_phase_mem_cliffordTmLim`: **every unitary on `m ≥ 1` qubits becomes a limit of
Clifford+T circuits after multiplication by a single global phase.** The file assembles the whole
chain and supplies the three joints it was missing.

**The exact product** (★★ `mem_closure_elementary`): every unitary on `m` qubits is a *finite,
exact* product of `CNOT`s and single-qubit gates. That is #70's two-level decomposition, then #71's
Gray-code sandwich, then #85's control-count recursion. The joint is ★
`block_mem_unitaryGroup_of_ctrlSetOf`, the converse of `ctrlSet_mem_unitaryGroup`: the earlier rows
deliver a controlled gate *known to be unitary*, while #85 asks for its `2 × 2` block to be unitary,
and the block's unitarity follows by evaluating the relation `UᴴU = 1` at the labels that differ only
on the target, where the sum collapses to two terms.

**The lift.** Sending a `2 × 2` gate to the `m`-qubit gate on one qubit is a monoid homomorphism
(`gateOfHom`) and continuous (`continuous_gateOf`), so it carries the closure of the one-qubit
Clifford+T words into the closure of the `m`-qubit circuits (★ `gateOf_mem_cliffordTmLim`). The step
that makes "modulo phase" survive is `gateOf_smul`: **a phase on the block is a global phase on the
gate**, because the gate is the block tensored with the identity, so scalars pull straight out. Were
that false the phases of #81 would become relative phases and the argument would not close.

**The phases add.** The gates that become limits after one global phase are themselves a submonoid
(`phaseLim`), so the exact product of elementary gates inherits a single phase, the sum of the
factors' phases, without any bookkeeping over lists.

* ★ `ctrlSetOf_eq_of_block`, ★ `block_mem_unitaryGroup_of_ctrlSetOf`,
  `block_mem_unitaryGroup_of_ctrlGate`;
* `isMultiCtrlX_mem_closure`, `isMultiCtrlGate_mem_closure`, ★ `twoLevel_mem_closure`,
  ★★ `mem_closure_elementary`;
* `gateOf_eq_ctrlSetOf`, `gateOf_apply_of_agree`, `gateOf_apply_of_not_agree`, `gateOf_one`,
  `gateOf_mul`, `gateOf_smul`, `gateOfHom`, `continuous_gateOf`;
* `cliffordTGates`, `cliffordTm`, `cliffordTmLim`, `cliffordTm_le_lim`, `isClosed_cliffordTmLim`,
  ★ `gateOf_mem_cliffordTmLim`;
* `smul_mul_smul_eq`, `phaseLim`, `mem_phaseLim_iff`, `elementary_le_phaseLim`,
  ★★ `exists_phase_mem_cliffordTmLim`.

## Honest scope

⚠️ Density, not exactness, and no gate counts. The statement is membership in a *topological
closure*: for every unitary and every accuracy there is a Clifford+T circuit that close, which is
what gate synthesis needs, and all that is true of a countable gate set. How the circuit's length
grows as the accuracy tightens is Solovay–Kitaev, BACKLOG #74, deliberately **not claimed**.
⚠️ `m ≥ 1`. The `m = 0` case is the scalars and carries no gates.
⚠️ The single-qubit factors of the exact product are genuine `U(2)` elements; it is only after the
approximation step that everything is Clifford+T. The two statements are kept separate on purpose.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.5
(Theorem 4.1 through §4.5.3); C. M. Dawson, M. A. Nielsen, quant-ph/0505030;
`CsdLean4/Mathlib/LinearAlgebra/Matrix/TwoLevel.lean` (#70),
`CsdLean4/Mathlib/QuantumInfo/MultiControlled.lean` (#71),
`ControlRecursion.lean` (#85) and `CliffordTDensity.lean` (#81); `specs/magic-plan.md`;
`specs/BACKLOG.md` #73; `specs/residues.tsv` `R-005`; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace Controlled

open TwoLevel MultiControlled Euler

variable {m : ℕ}

/-! ### A unitary controlled gate has a unitary block

The decompositions of #70 and #71 deliver a controlled gate and the knowledge that it is unitary;
#85 asks for its `2 × 2` block to be unitary. This is the missing converse of
`ctrlSet_mem_unitaryGroup`: evaluate the unitarity relation at the labels that differ only on the
target.
-/

theorem ctrlSetOf_eq_of_block {S : Finset (Fin m)} {j : Fin m} {pat : Fin m → Fin 2} (a b c d : ℂ) :
    ctrlSetOf S j pat !![a, b; c, d] = ctrlSet S j pat a b c d := by
  rw [ctrlSetOf]
  norm_num

/-- ★ **A controlled gate is unitary only if its block is.** -/
theorem block_mem_unitaryGroup_of_ctrlSetOf {S : Finset (Fin m)} {j : Fin m} (hjS : j ∉ S)
    (pat : Fin m → Fin 2) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ctrlSetOf S j pat M ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) :
    M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hne : ∀ i ∈ S, i ≠ j := fun i hi hij => hjS (by rw [← hij]; exact hi)
  have hG : (ctrlSetOf S j pat M)ᴴ * ctrlSetOf S j pat M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp h
  have hself : ∀ z : Fin 2, Function.update pat j z j = z := fun z => Function.update_self _ _ _
  have hag : ∀ z w : Fin 2, ∀ i, i ≠ j →
      Function.update pat j z i = Function.update pat j w i := fun z w i hi => by
    rw [Function.update_of_ne hi, Function.update_of_ne hi]
  have hctrl : ∀ z : Fin 2, ∀ i ∈ S, Function.update pat j z i = pat i := fun z i hi => by
    rw [Function.update_of_ne (hne i hi)]
  rw [Matrix.mem_unitaryGroup_iff']
  show Mᴴ * M = 1
  ext x y
  have hcol := congrFun (congrFun hG (Function.update pat j x)) (Function.update pat j y)
  rw [Matrix.mul_apply] at hcol
  have hvanish : ∀ p : Fin m → Fin 2, ¬(∀ i, i ≠ j → p i = Function.update pat j x i) →
      (ctrlSetOf S j pat M)ᴴ (Function.update pat j x) p
        * ctrlSetOf S j pat M p (Function.update pat j y) = 0 := by
    intro p hp
    rw [Matrix.conjTranspose_apply, ctrlSetOf_apply_of_not_agree hp, star_zero, zero_mul]
  rw [sum_collapse_update j (Function.update pat j x) _ hvanish] at hcol
  have hidem : ∀ z : Fin 2,
      Function.update (Function.update pat j x) j z = Function.update pat j z := fun z => by
    rw [Function.update_idem]
  rw [hidem, hidem, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
    ctrlSetOf_apply_block (hag 0 x) (hctrl 0), ctrlSetOf_apply_block (hag 0 y) (hctrl 0),
    ctrlSetOf_apply_block (hag 1 x) (hctrl 1), ctrlSetOf_apply_block (hag 1 y) (hctrl 1)] at hcol
  simp only [hself] at hcol
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
    hcol, Matrix.one_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos (show Function.update pat j x = Function.update pat j y by rw [hxy])]
  · rw [if_neg hxy, if_neg ?_]
    intro hc
    exact hxy (by rw [← hself x, ← hself y, hc])

theorem block_mem_unitaryGroup_of_ctrlGate {j : Fin m} {pat : Fin m → Fin 2} {a b c d : ℂ}
    (h : ctrlGate j pat a b c d ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) :
    !![a, b; c, d] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  refine block_mem_unitaryGroup_of_ctrlSetOf (S := Finset.univ.erase j)
    (Finset.notMem_erase j Finset.univ) pat ?_
  rw [ctrlSetOf_eq_of_block, ctrlSet_erase_eq_ctrlGate]
  exact h

/-! ### Every unitary is an exact product of `CNOT`s and single-qubit gates -/

theorem isMultiCtrlX_mem_closure {X : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hX : IsMultiCtrlX X) : X ∈ Submonoid.closure (elementary m) := by
  obtain ⟨j, pat, rfl⟩ := hX
  have h := ctrlGateOf_mem_closure j pat (U := xMat) xMat_mem_unitaryGroup
  rw [show xMat 0 0 = 0 from by norm_num [xMat], show xMat 0 1 = 1 from by norm_num [xMat],
    show xMat 1 0 = 1 from by norm_num [xMat], show xMat 1 1 = 0 from by norm_num [xMat]] at h
  exact h

theorem isMultiCtrlGate_mem_closure {W : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hW : IsMultiCtrlGate W) (hWu : W ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) :
    W ∈ Submonoid.closure (elementary m) := by
  obtain ⟨j, pat, a, b, c, d, rfl⟩ := hW
  have hblock := block_mem_unitaryGroup_of_ctrlGate hWu
  have h := ctrlGateOf_mem_closure j pat (U := !![a, b; c, d]) hblock
  norm_num at h
  exact h

/-- ★ A two-level unitary is a product of `CNOT`s and single-qubit gates: #71's Gray-code sandwich
fed into #85. -/
theorem twoLevel_mem_closure {V : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hV : IsTwoLevel V) (hVu : V ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) :
    V ∈ Submonoid.closure (elementary m) := by
  obtain ⟨u, v, huv, hid⟩ := hV
  obtain ⟨L, W, hL, hW, hVeq, hWu⟩ := exists_multiCtrl_sandwich huv hid
  rw [hVeq]
  refine mul_mem (mul_mem ?_ (isMultiCtrlGate_mem_closure hW (hWu hVu))) ?_
  · exact Submonoid.list_prod_mem _ fun X hX => isMultiCtrlX_mem_closure (hL X hX).1
  · refine Submonoid.list_prod_mem _ fun X hX => ?_
    exact isMultiCtrlX_mem_closure (hL X (List.mem_reverse.mp hX)).1

/-- ★★ **Every unitary on `m` qubits is an exact product of `CNOT`s and single-qubit gates** —
the two-level decomposition of #70, the Gray-code sandwich of #71 and the control-count recursion
of #85, composed. -/
theorem mem_closure_elementary (hm : 0 < m) {U : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) :
    U ∈ Submonoid.closure (elementary m) := by
  have hcard : 1 < Fintype.card (Fin m → Fin 2) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact Nat.one_lt_two_pow_iff.mpr (Nat.pos_iff_ne_zero.mp hm)
  obtain ⟨L, hL, hLprod⟩ := exists_twoLevel_prod hcard U hU
  rw [← hLprod]
  exact Submonoid.list_prod_mem _ fun V hV => twoLevel_mem_closure (hL V hV).1 (hL V hV).2

/-! ### Lifting a single-qubit gate to `m` qubits -/

theorem gateOf_eq_ctrlSetOf (j : Fin m) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf j M = ctrlSetOf ∅ j (fun _ => 0) M := rfl

theorem gateOf_apply_of_agree {j : Fin m} {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ j → k i = l i)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : gateOf j M k l = M (k j) (l j) := by
  rw [gateOf_eq_ctrlSetOf, ctrlSetOf_apply_block hag (by simp)]

theorem gateOf_apply_of_not_agree {j : Fin m} {k l : Fin m → Fin 2}
    (hag : ¬∀ i, i ≠ j → k i = l i) (M : Matrix (Fin 2) (Fin 2) ℂ) : gateOf j M k l = 0 := by
  rw [gateOf_eq_ctrlSetOf, ctrlSetOf_apply_of_not_agree hag]

theorem gateOf_one (j : Fin m) : gateOf j 1 = 1 := by
  have h : ctrlSetOf ∅ j (fun _ => (0 : Fin 2)) (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = ctrlSet ∅ j (fun _ => 0) 1 0 0 1 := by
    rw [ctrlSetOf]
    norm_num
  rw [gateOf_eq_ctrlSetOf, h, ctrlSet_one]

theorem gateOf_mul (j : Fin m) (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf j (M * N) = gateOf j M * gateOf j N := by
  rw [gateOf_eq_ctrlSetOf, gateOf_eq_ctrlSetOf, gateOf_eq_ctrlSetOf, ctrlSetOf, ctrlSetOf,
    ctrlSetOf, ctrlSet_mul (Finset.notMem_empty j)]
  congr 1 <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **A phase on the block is a global phase on the gate** — the step that makes "modulo phase"
survive the lift, because the gate is the block tensored with the identity. -/
theorem gateOf_smul (j : Fin m) (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf j (c • M) = c • gateOf j M := by
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · rw [gateOf_apply_of_agree hag, Matrix.smul_apply, Matrix.smul_apply,
      gateOf_apply_of_agree hag]
  · rw [gateOf_apply_of_not_agree hag, Matrix.smul_apply, gateOf_apply_of_not_agree hag,
      smul_zero]

/-- Lifting a single-qubit gate to `m` qubits is a monoid homomorphism. -/
def gateOfHom (j : Fin m) :
    Matrix (Fin 2) (Fin 2) ℂ →* Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ where
  toFun := gateOf j
  map_one' := gateOf_one j
  map_mul' := gateOf_mul j

theorem continuous_gateOf (j : Fin m) :
    Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => gateOf j M := by
  refine continuous_matrix fun k l => ?_
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · simp only [gateOf_apply_of_agree hag]
    exact (continuous_apply (l j)).comp (continuous_apply (k j))
  · simp only [gateOf_apply_of_not_agree hag]
    exact continuous_const

/-! ### Clifford+T on `m` qubits -/

/-- The Clifford+T gate set on `m` qubits: `H` and `T` on any qubit, `CNOT` on any ordered pair. -/
noncomputable def cliffordTGates (m : ℕ) : Set (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :=
  {g | (∃ j : Fin m, g = gateOf j CliffordT.hGateM) ∨
    (∃ j : Fin m, g = gateOf j CliffordT.tGateM) ∨
    (∃ a b : Fin m, a ≠ b ∧ g = cnotGate' a b)}

/-- The monoid of Clifford+T circuits on `m` qubits. -/
noncomputable def cliffordTm (m : ℕ) : Submonoid (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :=
  Submonoid.closure (cliffordTGates m)

/-- The limits of Clifford+T circuits on `m` qubits: a closed submonoid. -/
noncomputable def cliffordTmLim (m : ℕ) : Submonoid (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :=
  (cliffordTm m).topologicalClosure

theorem cliffordTm_le_lim : cliffordTm m ≤ cliffordTmLim m := Submonoid.le_topologicalClosure _

theorem isClosed_cliffordTmLim :
    IsClosed ((cliffordTmLim m) : Set (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)) :=
  Submonoid.isClosed_topologicalClosure _

/-- ★ **The one-qubit density transfers to `m` qubits**: lifting is a continuous homomorphism, so it
carries the closure of the one-qubit words into the closure of the `m`-qubit circuits. -/
theorem gateOf_mem_cliffordTmLim (j : Fin m) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ SU2.cliffordTLim) : gateOf j M ∈ cliffordTmLim m := by
  have hle : SU2.cliffordT ≤ Submonoid.comap (gateOfHom j) (cliffordTmLim m) := by
    rw [SU2.cliffordT, Submonoid.closure_le]
    intro x hx
    rcases hx with hx | hx
    · subst hx
      exact cliffordTm_le_lim (Submonoid.subset_closure (Or.inl ⟨j, rfl⟩))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact cliffordTm_le_lim (Submonoid.subset_closure (Or.inr (Or.inl ⟨j, rfl⟩)))
  have hclosed : IsClosed
      ((Submonoid.comap (gateOfHom j) (cliffordTmLim m)) :
        Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    isClosed_cliffordTmLim.preimage (continuous_gateOf j)
  exact Submonoid.topologicalClosure_minimal _ hle hclosed hM

/-! ### Clifford+T is dense in `U(2ⁿ)` modulo phase -/

theorem smul_mul_smul_eq (c d : ℂ) (A B : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :
    (c * d) • (A * B) = (c • A) * (d • B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The gates that become limits of Clifford+T circuits after one global phase. They form a
submonoid, which is what lets the phases of the factors add up. -/
noncomputable def phaseLim (m : ℕ) : Submonoid (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) where
  carrier := {g | ∃ φ : ℝ, Euler.expI φ • g ∈ cliffordTmLim m}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨φ, ha⟩ := ha
    obtain ⟨ψ, hb⟩ := hb
    refine ⟨φ + ψ, ?_⟩
    rw [Euler.expI_add, smul_mul_smul_eq]
    exact mul_mem ha hb
  one_mem' := ⟨0, by rw [Euler.expI_zero, one_smul]; exact (cliffordTmLim m).one_mem⟩

theorem mem_phaseLim_iff {g : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ} :
    g ∈ phaseLim m ↔ ∃ φ : ℝ, Euler.expI φ • g ∈ cliffordTmLim m := Iff.rfl

theorem elementary_le_phaseLim : elementary m ⊆ (phaseLim m : Set _) := by
  intro g hg
  rcases hg with ⟨j, M, hM, rfl⟩ | ⟨a, b, hab, rfl⟩
  · obtain ⟨φ, hφ⟩ := SU2.exists_phase_mem_cliffordTLim hM
    refine mem_phaseLim_iff.mpr ⟨φ, ?_⟩
    rw [← gateOf_smul]
    exact gateOf_mem_cliffordTmLim j hφ
  · refine mem_phaseLim_iff.mpr ⟨0, ?_⟩
    rw [Euler.expI_zero, one_smul]
    exact cliffordTm_le_lim (Submonoid.subset_closure (Or.inr (Or.inr ⟨a, b, hab, rfl⟩)))

/-- ★★ **Clifford+T is universal: dense in `U(2ⁿ)` modulo phase.** Every unitary on `m ≥ 1` qubits
becomes a limit of Clifford+T circuits after multiplication by a single global phase. This is the
statement `R-005` asked for, and it closes it. -/
theorem exists_phase_mem_cliffordTmLim (hm : 0 < m)
    {U : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) :
    ∃ φ : ℝ, Euler.expI φ • U ∈ cliffordTmLim m :=
  mem_phaseLim_iff.mp
    (Submonoid.closure_le.mpr elementary_le_phaseLim (mem_closure_elementary hm hU))

end Controlled

end QuantumInfo
