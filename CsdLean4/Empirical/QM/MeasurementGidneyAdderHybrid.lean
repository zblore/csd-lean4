/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.MeasurementGidneyAdder
public import CsdLean4.Mathlib.QuantumInfo.Reversible.HybridLift

/-!
# The measurement-based Gidney adder on the full register: the `n`-fold hybrid amplitude equality

**Category:** 3-Local (QM-validity content; no CSD ontology).

`MeasurementGidneyAdder.lean` re-costs the Gidney adder — `n` Toffoli forward, `0` on the measured
reverse pass — and `MeasurementAdderHybrid.lean` proved the amplitude-level statement for the
AND-adder. This module is the same statement for the Gidney adder, on the general hybrid
semantics of `HybridLift.lean`. Here the per-Toffoli picture *is* right: the reverse block of a
Gidney cell is `[CX cin cout, CCX a b cout, CX cin b, CX cin a]`, and when its Toffoli fires the
ancilla `cout` holds exactly the fresh AND `(a ⊕ cin) ∧ (b ⊕ cin)` of the (still shifted) addend
wires — an AND-shaped block, so Gidney's single-CZ gadget is exact there, one per cell, with the
two un-shifting CNOTs kept as unitaries around it (`gidneyHybridCell`).

* `gidneyHybridAdd L mo` — the forward and sum passes as unitaries, then the hybrid reverse pass
  `gidneyHybridUncompute L mo n` (cells `n−1, …, 0`; the Toffoli of each replaced by the gadget
  with outcome `mo k`).
* `gidneyHybrid_invariant` — the run compared with the unitary reverse pass, cell by cell: off
  the outcome ancillas the two agree (the agreement propagation `denoteGate_agree`, gate by
  gate), the ancillas hold the outcomes, and every gadget meets its AND
  (`MAJ(a,b,c) ⊕ c = (a ⊕ c) ∧ (b ⊕ c)`, `majority_xor_carry`, on the forward carry invariant).
* ★★ `gidneyHybridAdd_amplitude` — **the `n`-fold hybrid amplitude equality**: on every basis
  input with clean ancillas the hybrid adder produces `(√2)⁻¹^n • |out⟩`, where `out` agrees
  with the unitary adder's output on every wire except the `n` carry ancillas
  (`gidneyHybridAdd_shadow_data`) — so the sum register holds `(A + B) mod 2ⁿ`
  (`gidneyHybridAdd_sum`) and the addends are restored (`gidneyHybridAdd_shadow_A`, `_B`) — and
  the ancillas hold the outcomes (`gidneyHybridAdd_shadow_outcome`). By linearity the same holds
  for any superposition of clean-ancilla inputs (`hybridLin_sum`).

With `MeasurementAdderHybrid.lean` this closes link 11's measurement-gadget strand: both
measurement-based adders of the corpus are amplitude-exact on the full register, at the Toffoli
counts their re-costs state (`n` here, `3n` there).

## Honest scope

Per-outcome representation: each of the `2ⁿ` outcome strings has probability `2⁻ⁿ` and every
branch carries the right data. The Toffoli count of the reverse pass is `0` as
`gidneyMeasAddToffoli_eq` states; the measurement count is `n`. No ECDSA resource claim.
-/

@[expose] public section

open scoped Matrix
open QuantumInfo
open Reversible

namespace CSD.Empirical.QM

variable {m n : ℕ}

/-! ## Boolean facts -/

/-- `MAJ(a,b,c) ⊕ c = (a ⊕ c) ∧ (b ⊕ c)`: the Gidney cell's fresh AND is the carry-out minus the
carry-in. -/
lemma majority_xor_carry (a b c : Bool) : (majority a b c ^^ c) = ((a ^^ c) && (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- A Boolean AND in the `Fin 2` recast: the product, as the one-pair parity. -/
lemma regOfState_and (x y : Bool) :
    (if (x && y) then (1 : Fin 2) else 0)
      = (if x then (1 : Fin 2) else 0) * (if y then (1 : Fin 2) else 0) + 0 := by
  cases x <;> cases y <;> decide

/-! ## The hybrid reverse pass -/

/-- **The hybrid reverse block of cell `k`:** the reversed Gidney cell with its Toffoli replaced by
the single-correction gadget on the fresh AND `(A k ⊕ G k) ∧ (B k ⊕ G k)`, the un-shifting CNOTs
kept as unitaries. -/
def gidneyHybridCell (L : GidneyLayout m n) (k : ℕ) (mo : Fin 2) : List (HybridGate m) :=
  [.gate (.CX (L.G k) (L.G (k + 1))), .measure [(L.A k, L.B k)] (L.G (k + 1)) mo,
    .gate (.CX (L.G k) (L.B k)), .gate (.CX (L.G k) (L.A k))]

/-- The unitary reverse block of cell `k`: the same gates with the Toffoli in place. -/
lemma inverse_gidneyForwardSlice (L : GidneyLayout m n) (k : ℕ) :
    inverse (gidneyForwardSlice L k)
      = [.CX (L.G k) (L.G (k + 1)), .CCX (L.A k) (L.B k) (L.G (k + 1)), .CX (L.G k) (L.B k),
          .CX (L.G k) (L.A k)] := rfl

/-- **The hybrid reverse pass** over cells `k−1, …, 0` (cell `k−1` first, as in the reverse
pass). -/
def gidneyHybridUncompute (L : GidneyLayout m n) (mo : ℕ → Fin 2) : ℕ → List (HybridGate m)
  | 0 => []
  | k + 1 => gidneyHybridCell L k (mo k) ++ gidneyHybridUncompute L mo k

/-- The unitary reverse pass over cells `k−1, …, 0`, in the same shape. -/
def gidneyUnitaryUncompute (L : GidneyLayout m n) : ℕ → Circuit m
  | 0 => []
  | k + 1 => inverse (gidneyForwardSlice L k) ++ gidneyUnitaryUncompute L k

/-- **The hybrid Gidney adder:** the forward and sum passes as unitaries, then the hybrid reverse
pass over all `n` cells. -/
def gidneyHybridAdd (L : GidneyLayout m n) (mo : ℕ → Fin 2) : List (HybridGate m) :=
  (gidneyForward L ++ andSumPass L.toAnd).map HybridGate.gate ++ gidneyHybridUncompute L mo n

lemma gidneyForwardPrefix_succ (L : GidneyLayout m n) (k : ℕ) :
    gidneyForwardPrefix L (k + 1) = gidneyForwardPrefix L k ++ gidneyForwardSlice L k := by
  simp only [gidneyForwardPrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The shaped unitary reverse pass is the reverse pass. -/
lemma gidneyUnitaryUncompute_eq (L : GidneyLayout m n) :
    ∀ k, gidneyUnitaryUncompute L k = inverse (gidneyForwardPrefix L k)
  | 0 => rfl
  | k + 1 => by
    show inverse (gidneyForwardSlice L k) ++ gidneyUnitaryUncompute L k = _
    rw [gidneyUnitaryUncompute_eq L k, gidneyForwardPrefix_succ]
    simp only [inverse, List.reverse_append]

lemma gadgetCount_gidneyHybridUncompute (L : GidneyLayout m n) (mo : ℕ → Fin 2) :
    ∀ k, gadgetCount (gidneyHybridUncompute L mo k) = k
  | 0 => rfl
  | k + 1 => by
    show gadgetCount (gidneyHybridCell L k (mo k) ++ gidneyHybridUncompute L mo k) = k + 1
    simp only [gidneyHybridCell, List.cons_append, List.nil_append, gadgetCount,
      gadgetCount_gidneyHybridUncompute L mo k]

lemma gadgetCount_gidneyHybridAdd (L : GidneyLayout m n) (mo : ℕ → Fin 2) :
    gadgetCount (gidneyHybridAdd L mo) = n := by
  rw [gidneyHybridAdd, gadgetCount_gate_list_append, gadgetCount_gidneyHybridUncompute]

/-! ## The invariant -/

/-- Off the outcome ancillas of cells `k, …, n−1`, the register state `u` read as Booleans agrees
with the Boolean state `T`. -/
def AgreeOff (L : GidneyLayout m n) (k : ℕ) (u : Fin m → Fin 2) (T : State m) : Prop :=
  ∀ i : Fin m, (∀ j, k ≤ j → j < n → i ≠ L.G (j + 1)) → stateOfReg u i = T i

/-- The outcome ancillas of cells `k, …, n−1` hold their outcomes. -/
def HoldsOutcomes (L : GidneyLayout m n) (mo : ℕ → Fin 2) (k : ℕ) (u : Fin m → Fin 2) : Prop :=
  ∀ j, k ≤ j → j < n → u (L.G (j + 1)) = mo j

/-- The wires of cells `0, …, k−1` still hold their post-forward values. -/
def CellsFresh (L : GidneyLayout m n) (t T : State m) (k : ℕ) : Prop :=
  ∀ j, j < k → T (L.A j) = t (L.A j) ∧ T (L.B j) = t (L.B j) ∧ T (L.G j) = t (L.G j)
    ∧ T (L.G (j + 1)) = t (L.G (j + 1))

/-- **The hybrid reverse pass against the unitary one, cell by cell.** If, before the cells
`k−1, …, 0`, the register state agrees with the Boolean state off the outcome ancillas of the
cells already processed, those hold their outcomes, and the cells to come are still fresh, then
the hybrid pass is well-formed, its shadow agrees with the unitary pass off all outcome ancillas,
and every outcome ancilla holds its outcome. -/
theorem gidneyHybrid_invariant (L : GidneyLayout m n) (mo : ℕ → Fin 2) (t : State m)
    (hcell : ∀ j, j < n → (t (L.G (j + 1)) ^^ t (L.G j)) = (t (L.A j) && t (L.B j))) :
    ∀ k, k ≤ n → ∀ (u : Fin m → Fin 2) (T : State m),
      AgreeOff L k u T → HoldsOutcomes L mo k u → CellsFresh L t T k →
        WellFormed (gidneyHybridUncompute L mo k) u
          ∧ AgreeOff L 0 (shadow (gidneyHybridUncompute L mo k) u)
              (denote (gidneyUnitaryUncompute L k) T)
          ∧ HoldsOutcomes L mo 0 (shadow (gidneyHybridUncompute L mo k) u)
  | 0, _, u, T, hu, ho, _ => ⟨trivial, hu, ho⟩
  | k + 1, hk, u, T, hu, ho, hf => by
    obtain ⟨hfA, hfB, hfG, hfG1⟩ := hf k (Nat.lt_succ_self k)
    have hkn : k < n := by omega
    -- the wires of cell `k` against the outcome ancillas
    have hGk1_ne : ∀ j, k + 1 ≤ j → j < n → L.G (k + 1) ≠ L.G (j + 1) := fun j hj hjn h => by
      have := L.hGinj (k + 1) (j + 1) (by omega) (by omega) h
      omega
    have hGk_ne : ∀ j, k ≤ j → j < n → L.G k ≠ L.G (j + 1) := fun j hj hjn h => by
      have := L.hGinj k (j + 1) (by omega) (by omega) h
      omega
    have hcc : L.G k ≠ L.G (k + 1) := fun h => by
      have := L.hGinj k (k + 1) (by omega) (by omega) h
      omega
    have hoa : L.G (k + 1) ≠ L.A k := (L.hAG k (k + 1)).symm
    have hob : L.G (k + 1) ≠ L.B k := (L.hBG k (k + 1)).symm
    -- the four steps, Boolean side
    set T₁ := denoteGate (.CX (L.G k) (L.G (k + 1))) T with hT₁
    set T₂ := denoteGate (.CCX (L.A k) (L.B k) (L.G (k + 1))) T₁ with hT₂
    set T₃ := denoteGate (.CX (L.G k) (L.B k)) T₂ with hT₃
    set T₄ := denoteGate (.CX (L.G k) (L.A k)) T₃ with hT₄
    -- the four steps, register side
    set u₁ := (HybridGate.gate (.CX (L.G k) (L.G (k + 1)))).shadow u with hu₁
    set u₂ := Function.update u₁ (L.G (k + 1)) (mo k) with hu₂
    set u₃ := (HybridGate.gate (.CX (L.G k) (L.B k))).shadow u₂ with hu₃
    set u₄ := (HybridGate.gate (.CX (L.G k) (L.A k))).shadow u₃ with hu₄
    -- (1) after `CX cin cout`: agreement off the ancillas of cells `≥ k+1`
    have h1 : ∀ i : Fin m, (∀ j, k + 1 ≤ j → j < n → i ≠ L.G (j + 1)) →
        stateOfReg u₁ i = T₁ i := by
      intro i hi
      rw [hu₁, stateOfReg_shadow_gate]
      refine denoteGate_agree (P := fun i => ∀ j, k + 1 ≤ j → j < n → i ≠ L.G (j + 1)) ?_ hu i hi
      intro w hw
      simp only [gateWires, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact fun j hj hjn => hGk_ne j (by omega) hjn
      · exact hGk1_ne
    -- (2) after the gadget / the Toffoli: agreement off the ancillas of cells `≥ k`
    have h2 : ∀ i : Fin m, (∀ j, k ≤ j → j < n → i ≠ L.G (j + 1)) →
        stateOfReg u₂ i = T₂ i := by
      intro i hi
      have hi' : i ≠ L.G (k + 1) := hi k le_rfl hkn
      rw [hu₂, stateOfReg_update, Function.update_of_ne hi', hT₂, denoteGate,
        if_neg (not_or.mpr ⟨hoa, hob⟩), Function.update_of_ne hi']
      exact h1 i fun j hj hjn => hi j (by omega) hjn
    -- (3) after `CX cin b`
    have h3 : ∀ i : Fin m, (∀ j, k ≤ j → j < n → i ≠ L.G (j + 1)) →
        stateOfReg u₃ i = T₃ i := by
      intro i hi
      rw [hu₃, stateOfReg_shadow_gate]
      refine denoteGate_agree (P := fun i => ∀ j, k ≤ j → j < n → i ≠ L.G (j + 1)) ?_ h2 i hi
      intro w hw
      simp only [gateWires, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hGk_ne
      · exact fun j _ _ => L.hBG k (j + 1)
    -- (4) after `CX cin a`
    have h4 : AgreeOff L k u₄ T₄ := by
      intro i hi
      rw [hu₄, stateOfReg_shadow_gate]
      refine denoteGate_agree (P := fun i => ∀ j, k ≤ j → j < n → i ≠ L.G (j + 1)) ?_ h3 i hi
      intro w hw
      simp only [gateWires, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hGk_ne
      · exact fun j _ _ => L.hAG k (j + 1)
    -- the outcome ancillas of cells `≥ k` after the block
    have hout : HoldsOutcomes L mo k u₄ := by
      intro j hj hjn
      rw [hu₄, shadow_gate_apply_of_not_mem_target _ _ (by
          simp only [gateTarget, Finset.mem_singleton]; exact (L.hAG k (j + 1)).symm),
        hu₃, shadow_gate_apply_of_not_mem_target _ _ (by
          simp only [gateTarget, Finset.mem_singleton]; exact (L.hBG k (j + 1)).symm),
        hu₂, Function.update_apply]
      rcases Nat.lt_or_ge k j with hjk | hjk
      · rw [if_neg (hGk1_ne j (by omega) hjn).symm, hu₁,
          shadow_gate_apply_of_not_mem_target _ _ (by
            simp only [gateTarget, Finset.mem_singleton]; exact (hGk1_ne j (by omega) hjn).symm)]
        exact ho j (by omega) hjn
      · have hjk' : j = k := by omega
        subst hjk'
        rw [if_pos rfl]
    -- the cells `< k` stay fresh: the block writes only `G (k+1)`, `B k`, `A k`
    have hT₄T : ∀ i : Fin m, i ≠ L.A k → i ≠ L.B k → i ≠ L.G (k + 1) → T₄ i = T i := by
      intro i hia hib hig
      have : T₄ = denote (inverse (gidneyForwardSlice L k)) T := rfl
      rw [this]
      refine denote_apply_of_forall_not_mem_target _ (fun g hg hmem => ?_) T
      rw [inverse, List.mem_reverse] at hg
      rcases gidneyForwardSlice_target hg hmem with h | h | h
      · exact hia h
      · exact hib h
      · exact hig h
    have hfresh : CellsFresh L t T₄ k := by
      intro j hj
      obtain ⟨hA', hB', hG', hG1'⟩ := hf j (by omega)
      have hjn : j < n := by omega
      have hAA : L.A j ≠ L.A k := fun h => by have := L.hAinj j k hjn hkn h; omega
      have hBB : L.B j ≠ L.B k := fun h => by have := L.hBinj j k hjn hkn h; omega
      have hGk1 : L.G j ≠ L.G (k + 1) := fun h => by
        have := L.hGinj j (k + 1) (by omega) (by omega) h; omega
      have hG1k1 : L.G (j + 1) ≠ L.G (k + 1) := fun h => by
        have := L.hGinj (j + 1) (k + 1) (by omega) (by omega) h; omega
      exact ⟨by rw [hT₄T _ hAA (L.hAB j k) (L.hAG j (k + 1)), hA'],
        by rw [hT₄T _ (L.hAB k j).symm hBB (L.hBG j (k + 1)), hB'],
        by rw [hT₄T _ (L.hAG k j).symm (L.hBG k j).symm hGk1, hG'],
        by rw [hT₄T _ (L.hAG k (j + 1)).symm (L.hBG k (j + 1)).symm hG1k1, hG1']⟩
    -- the induction hypothesis on the remaining cells
    obtain ⟨hwf, hagree, hout'⟩ :=
      gidneyHybrid_invariant L mo t hcell k (by omega) u₄ T₄ h4 hout hfresh
    -- the gadget meets its AND: `u₁ cout = u₁ a · u₁ b`
    have hgad : u₁ (L.G (k + 1)) = andParity [(L.A k, L.B k)] u₁ := by
      have hvc := val_eq_of_stateOfReg_eq (h1 (L.G (k + 1)) hGk1_ne)
      have hva := val_eq_of_stateOfReg_eq (h1 (L.A k) fun j _ _ => L.hAG k (j + 1))
      have hvb := val_eq_of_stateOfReg_eq (h1 (L.B k) fun j _ _ => L.hBG k (j + 1))
      have hTc : T₁ (L.G (k + 1)) = (t (L.A k) && t (L.B k)) := by
        rw [hT₁, denoteGate, if_neg hcc, Function.update_self, hfG, hfG1, Bool.xor_comm,
          hcell k hkn]
      have hTa : T₁ (L.A k) = t (L.A k) := by
        rw [hT₁, denoteGate_apply_of_not_mem_target (by
          simp only [gateTarget, Finset.mem_singleton]; exact (L.hAG k (k + 1)))]
        exact hfA
      have hTb : T₁ (L.B k) = t (L.B k) := by
        rw [hT₁, denoteGate_apply_of_not_mem_target (by
          simp only [gateTarget, Finset.mem_singleton]; exact (L.hBG k (k + 1)))]
        exact hfB
      simp only [andParity, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hvc, hva, hvb, hTc, hTa, hTb]
      exact regOfState_and _ _
    -- assemble
    refine ⟨?_, ?_, ?_⟩
    · show WellFormed (gidneyHybridCell L k (mo k) ++ gidneyHybridUncompute L mo k) u
      simp only [gidneyHybridCell, List.cons_append, List.nil_append]
      rw [wellFormed_gate_cons, wellFormed_measure_cons]
      refine ⟨?_, hgad, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨L.hAG k (k + 1), L.hBG k (k + 1)⟩
      · rw [wellFormed_gate_cons, wellFormed_gate_cons]
        exact hwf
    · show AgreeOff L 0 (shadow (gidneyHybridCell L k (mo k) ++ gidneyHybridUncompute L mo k) u)
        (denote (inverse (gidneyForwardSlice L k) ++ gidneyUnitaryUncompute L k) T)
      rw [shadow_append, denote_append]
      exact hagree
    · show HoldsOutcomes L mo 0
        (shadow (gidneyHybridCell L k (mo k) ++ gidneyHybridUncompute L mo k) u)
      rw [shadow_append]
      exact hout'

/-! ## The carry invariant after the forward and sum passes -/

/-- After the forward and sum passes, each cell's fresh AND is its carry-out minus its carry-in:
`G (j+1) ⊕ G j = A j ∧ B j` on the (shifted) addend wires. -/
lemma gidneyPrefix_cell (L : GidneyLayout m n) (s : State m) (hG0 : ∀ j, s (L.G j) = false)
    (j : ℕ) (hj : j < n) :
    (denote (gidneyForward L ++ andSumPass L.toAnd) s (L.G (j + 1))
        ^^ denote (gidneyForward L ++ andSumPass L.toAnd) s (L.G j))
      = (denote (gidneyForward L ++ andSumPass L.toAnd) s (L.A j)
          && denote (gidneyForward L ++ andSumPass L.toAnd) s (L.B j)) := by
  rw [denote_append]
  have hsum : ∀ w : Fin m, (∀ i, i < n → w ≠ L.S i) →
      denote (andSumPass L.toAnd) (denote (gidneyForward L) s) w
        = denote (gidneyForward L) s w :=
    fun w hw => andSumPrefix_preserves_of_ne_S L.toAnd _ n hw
  rw [hsum _ (fun i _ h => L.hSG i (j + 1) h.symm), hsum _ (fun i _ h => L.hSG i j h.symm),
    hsum _ (fun i _ h => L.hAS j i h), hsum _ (fun i _ h => L.hBS j i h)]
  obtain ⟨hG, -, hA, hB, -, -⟩ := gidneyForward_invariant L s hG0 n le_rfl
  rw [gidneyForward, hG (j + 1) (by omega), hG j (by omega), hA j hj, hB j hj]
  exact majority_xor_carry _ _ _

/-! ## ★★ The n-fold hybrid amplitude equality -/

/-- The hybrid run is well-formed on every clean-ancilla basis input, and its shadow is the
unitary adder's output off the outcome ancillas, which hold the outcomes. -/
theorem gidneyHybridAdd_invariant (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) :
    WellFormed (gidneyHybridAdd L mo) (regOfState s)
      ∧ AgreeOff L 0 (shadow (gidneyHybridAdd L mo) (regOfState s)) (denote (gidneyAdd L) s)
      ∧ HoldsOutcomes L mo 0 (shadow (gidneyHybridAdd L mo) (regOfState s)) := by
  have hden : denote (gidneyAdd L) s
      = denote (gidneyUnitaryUncompute L n) (denote (gidneyForward L ++ andSumPass L.toAnd) s) := by
    rw [gidneyUnitaryUncompute_eq]
    exact denote_append (gidneyForward L ++ andSumPass L.toAnd) (inverse (gidneyForward L)) s
  have h := gidneyHybrid_invariant L mo _ (gidneyPrefix_cell L s hG0) n le_rfl
    (regOfState (denote (gidneyForward L ++ andSumPass L.toAnd) s))
    (denote (gidneyForward L ++ andSumPass L.toAnd) s)
    (fun i _ => congrFun (stateOfReg_regOfState _) i) (fun j hj hjn => absurd hjn (by omega))
    (fun j _ => ⟨rfl, rfl, rfl, rfl⟩)
  rw [gidneyHybridAdd, wellFormed_gate_list_append, stateOfReg_regOfState, shadow_append,
    shadow_gate_list, stateOfReg_regOfState, hden]
  exact h

/-- ★★ **The `n`-fold hybrid amplitude equality for the Gidney adder.** On every basis input with
clean carry ancillas, the hybrid adder — forward and sum passes, then the gadget on each cell's
fresh AND with outcomes `mo` — produces `(√2)⁻¹^n • |out⟩`, `out` the run's shadow. -/
theorem gidneyHybridAdd_amplitude (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) :
    hybridLin (gidneyHybridAdd L mo) (basisState (regOfState s))
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ n
          • basisState (shadow (gidneyHybridAdd L mo) (regOfState s)) := by
  rw [hybridLin_basisState _ _ (gidneyHybridAdd_invariant L mo s hG0).1,
    gadgetCount_gidneyHybridAdd]

/-- **The data agree with the unitary adder** on every wire other than the `n` carry ancillas
`G 1, …, G n`. -/
theorem gidneyHybridAdd_shadow_data (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (i : Fin m) (hi : ∀ j, j < n → i ≠ L.G (j + 1)) :
    shadow (gidneyHybridAdd L mo) (regOfState s) i = regOfState (denote (gidneyAdd L) s) i :=
  val_eq_of_stateOfReg_eq ((gidneyHybridAdd_invariant L mo s hG0).2.1 i fun j _ => hi j)

/-- **The ancillas hold the outcomes.** -/
theorem gidneyHybridAdd_shadow_outcome (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (j : ℕ) (hj : j < n) :
    shadow (gidneyHybridAdd L mo) (regOfState s) (L.G (j + 1)) = mo j :=
  (gidneyHybridAdd_invariant L mo s hG0).2.2 j (Nat.zero_le j) hj

/-- **The sum is right on every branch:** the sum register holds `(A + B) mod 2ⁿ`, exactly as for
the unitary adder (`gidneyAdd_correct`). -/
theorem gidneyHybridAdd_sum (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (hS0 : ∀ i, s (L.S i) = false) :
    regValRange L.S (stateOfReg (shadow (gidneyHybridAdd L mo) (regOfState s))) n
      = (regValRange L.A s n + regValRange L.B s n) % 2 ^ n := by
  rw [← gidneyAdd_correct L s hG0 hS0]
  unfold regValRange
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(gidneyHybridAdd_invariant L mo s hG0).2.1 (L.S i) fun j _ _ => L.hSG i (j + 1)]

/-- **The addends are restored on every branch** (the un-shifting CNOTs run as unitaries). -/
theorem gidneyHybridAdd_shadow_A (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (k : ℕ) :
    shadow (gidneyHybridAdd L mo) (regOfState s) (L.A k) = regOfState s (L.A k) := by
  rw [gidneyHybridAdd_shadow_data L mo s hG0 (L.A k) fun j _ => L.hAG k (j + 1)]
  simp only [regOfState, gidneyAdd_preserves_A]

theorem gidneyHybridAdd_shadow_B (L : GidneyLayout m n) (mo : ℕ → Fin 2) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (k : ℕ) :
    shadow (gidneyHybridAdd L mo) (regOfState s) (L.B k) = regOfState s (L.B k) := by
  rw [gidneyHybridAdd_shadow_data L mo s hG0 (L.B k) fun j _ => L.hBG k (j + 1)]
  simp only [regOfState, gidneyAdd_preserves_B]

end CSD.Empirical.QM

end
