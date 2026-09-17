/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.WedgeForm
public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.WedgeShuffle

/-!
# The top power of a real 2-form on a weighted pair tuple

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Analysis.Normed.Module.Alternating`).

A tuple of `2k` vectors is a **weighted pair tuple** for the 2-form `β` when `β` pairs the two
members of pair `j` (the slots `2j` and `2j + 1`) to `± c j` and kills everything else. On such a
tuple the `k`-th exterior power of `β` (`ContinuousAlternatingMap.wedgePow`) is `k!` times the
product of the weights: through the shuffle sum on a weighted pair family
(`wedge_mul_apply_weightedPairs`) each of the `k + 1` pairs is moved into the last two slots in
turn, and what is left behind is a weighted pair tuple of `k` pairs.

* `pairIdx`, `memIdx` — the pair and the member a slot of `Fin (2k)` belongs to;
  `pairIdx_powEquiv`, `memIdx_powEquiv` — through the re-indexing
  `powEquiv k : Fin (2k) ⊕ Fin 2 ≃ Fin (2(k+1))` the power recurses along, they are `slotPair`
  and `slotMem`;
* `IsWeightedPairTuple β c u`, with `isWeightedPairTuple_iff` (the family form through `powEquiv`)
  and `IsWeightedPairTuple.pairRep` (moving one pair into the last two slots leaves a weighted
  pair tuple, with that pair's weight replaced by the last one's: `removeWeight`);
* ★★ `wedgePow_apply_of_isWeightedPairTuple` — **the count**: `β^{∧k} u = k! · ∏ⱼ c j`;
  ★ `wedgePow_apply_of_isPairTuple` — all weights `1`: `β^{∧k} u = k!`.

## Honest scope

⚠️ Real-valued 2-forms, and the tuple must be paired by `β` exactly; nothing is said about
`β^{∧k}` on other tuples.

References: `Alternating/WedgeShuffle.lean` (the shuffle sum); `Geometry/Manifold/WedgeForm.lean`
(`wedgePow`, `powEquiv`); consumers `Instances/ProjectiveSpaceFubiniStudyVolume.lean` (the standard
symplectic form on standard pairs) and `Instances/ProjectiveSpaceTorusVolume.lean` (the sum of the
Fubini–Study form and the torus area form on the product basis).
-/

@[expose] public section

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Pairs and members of `Fin (2k)` -/

section Slots

variable {k : ℕ}

/-- The pair a slot of `Fin (2k)` belongs to. -/
def pairIdx (p : Fin (2 * k)) : Fin k := ⟨p / 2, by omega⟩

/-- `pairIdx`, unfolded: the definitional equation. -/
theorem pairIdx_def (p : Fin (2 * k)) : pairIdx p = ⟨p / 2, by omega⟩ := rfl

/-- Which member of its pair a slot of `Fin (2k)` is. -/
def memIdx (p : Fin (2 * k)) : Fin 2 := ⟨p % 2, by omega⟩

/-- `memIdx`, unfolded: the definitional equation. -/
theorem memIdx_def (p : Fin (2 * k)) : memIdx p = ⟨p % 2, by omega⟩ := rfl

theorem coe_powEquiv_inl (p : Fin (2 * k)) :
    ((DifferentialForm.powEquiv k (Sum.inl p) : Fin (2 * (k + 1))) : ℕ) = p := rfl

theorem coe_powEquiv_inr (b : Fin 2) :
    ((DifferentialForm.powEquiv k (Sum.inr b) : Fin (2 * (k + 1))) : ℕ) = 2 * k + b := rfl

theorem pairIdx_powEquiv_inl (p : Fin (2 * k)) :
    pairIdx (DifferentialForm.powEquiv k (Sum.inl p)) = slotPair (Sum.inl p) :=
  Fin.ext (by simp [pairIdx, slotPair, coe_powEquiv_inl])

theorem pairIdx_powEquiv_inr (b : Fin 2) :
    pairIdx (DifferentialForm.powEquiv k (Sum.inr b)) = slotPair (Sum.inr b) :=
  Fin.ext (by simp [pairIdx, slotPair, coe_powEquiv_inr]; omega)

theorem memIdx_powEquiv_inl (p : Fin (2 * k)) :
    memIdx (DifferentialForm.powEquiv k (Sum.inl p)) = slotMem (Sum.inl p) :=
  Fin.ext (by simp [memIdx, slotMem, coe_powEquiv_inl])

theorem memIdx_powEquiv_inr (b : Fin 2) :
    memIdx (DifferentialForm.powEquiv k (Sum.inr b)) = slotMem (k := k) (Sum.inr b) :=
  Fin.ext (by simp [memIdx, slotMem, coe_powEquiv_inr]; omega)

/-- Through `powEquiv`, `pairIdx` is `slotPair`. -/
theorem pairIdx_powEquiv (x : Fin (2 * k) ⊕ Fin 2) :
    pairIdx (DifferentialForm.powEquiv k x) = slotPair x := by
  rcases x with p | b
  · exact pairIdx_powEquiv_inl p
  · exact pairIdx_powEquiv_inr b

/-- Through `powEquiv`, `memIdx` is `slotMem`. -/
theorem memIdx_powEquiv (x : Fin (2 * k) ⊕ Fin 2) :
    memIdx (DifferentialForm.powEquiv k x) = slotMem x := by
  rcases x with p | b
  · exact memIdx_powEquiv_inl p
  · exact memIdx_powEquiv_inr b

/-- The pair of an `inl` slot is its `pairIdx`, as a pair of `k + 1`. -/
theorem slotPair_inl_eq_castSucc (p : Fin (2 * k)) :
    slotPair (Sum.inl p) = Fin.castSucc (pairIdx p) := rfl

/-- The member of an `inl` slot is its `memIdx`. -/
theorem slotMem_inl_eq_memIdx (p : Fin (2 * k)) : slotMem (Sum.inl p) = memIdx p := rfl

end Slots

/-! ### Weighted pair tuples -/

section Tuple

variable {k : ℕ}

/-- A tuple of `2k` vectors is a **weighted pair tuple** for the 2-form `β`, with weights `c`,
when `β` pairs the two members of pair `j` (the slots `2j` and `2j + 1`) to `± c j` and kills
everything else. -/
def IsWeightedPairTuple (β : E [⋀^Fin 2]→L[ℝ] ℝ) (c : Fin k → ℝ) (u : Fin (2 * k) → E) : Prop :=
  ∀ p q, β ![u p, u q]
    = if pairIdx p = pairIdx q then c (pairIdx p) * pairSign (memIdx p) (memIdx q) else 0

/-- A weighted pair tuple of `k + 1` pairs, read through `powEquiv k`, is a weighted pair
family, and conversely. -/
theorem isWeightedPairTuple_iff {β : E [⋀^Fin 2]→L[ℝ] ℝ} {c : Fin (k + 1) → ℝ}
    {u : Fin (2 * (k + 1)) → E} :
    IsWeightedPairTuple β c u
      ↔ IsWeightedPairFamily β c (fun x => u (DifferentialForm.powEquiv k x)) := by
  constructor
  · intro hu x y
    have h := hu (DifferentialForm.powEquiv k x) (DifferentialForm.powEquiv k y)
    rw [pairIdx_powEquiv, pairIdx_powEquiv, memIdx_powEquiv, memIdx_powEquiv] at h
    exact h
  · intro hu p q
    obtain ⟨x, rfl⟩ := (DifferentialForm.powEquiv k).surjective p
    obtain ⟨y, rfl⟩ := (DifferentialForm.powEquiv k).surjective q
    rw [pairIdx_powEquiv, pairIdx_powEquiv, memIdx_powEquiv, memIdx_powEquiv]
    exact hu x y

/-- The weights with pair `j` replaced by the last pair. -/
def removeWeight (c : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : Fin k → ℝ :=
  fun i => if Fin.castSucc i = j then c (Fin.last k) else c (Fin.castSucc i)

/-- The weight of pair `j` times the product of the remaining weights is the product of all. -/
theorem mul_prod_removeWeight (c : Fin (k + 1) → ℝ) (j : Fin (k + 1)) :
    c j * ∏ i, removeWeight c j i = ∏ i, c i := by
  rw [Fin.prod_univ_castSucc c]
  induction j using Fin.lastCases with
  | last =>
    have h : ∀ i : Fin k, removeWeight c (Fin.last k) i = c (Fin.castSucc i) := fun i =>
      if_neg (Fin.castSucc_lt_last i).ne
    simp only [h]
    ring
  | cast j₀ =>
    rw [← Finset.mul_prod_erase Finset.univ (fun i => removeWeight c (Fin.castSucc j₀) i)
        (Finset.mem_univ j₀),
      ← Finset.mul_prod_erase Finset.univ (fun i => c (Fin.castSucc i)) (Finset.mem_univ j₀)]
    have h1 : removeWeight c (Fin.castSucc j₀) j₀ = c (Fin.last k) := if_pos rfl
    have h2 : ∀ i ∈ Finset.univ.erase j₀,
        removeWeight c (Fin.castSucc j₀) i = c (Fin.castSucc i) := fun i hi =>
      if_neg fun h => Finset.ne_of_mem_erase hi (Fin.castSucc_inj.1 h)
    rw [h1, Finset.prod_congr rfl h2]
    ring

/-- Moving pair `j` into the last two slots (`pairRep j`) leaves a weighted pair tuple of `k`
pairs, with the weight of pair `j` replaced by the last one's. -/
theorem IsWeightedPairTuple.pairRep {β : E [⋀^Fin 2]→L[ℝ] ℝ} {c : Fin (k + 1) → ℝ}
    {u : Fin (2 * (k + 1)) → E} (hu : IsWeightedPairTuple β c u) (j : Fin (k + 1)) :
    IsWeightedPairTuple β (removeWeight c j)
      (fun i => u (DifferentialForm.powEquiv k (ContinuousAlternatingMap.pairRep j (Sum.inl i)))) := by
  have key : ∀ i : Fin (2 * k),
      u (DifferentialForm.powEquiv k (ContinuousAlternatingMap.pairRep j (Sum.inl i)))
      = if Fin.castSucc (pairIdx i) = j
        then u (DifferentialForm.powEquiv k (Sum.inr (memIdx i)))
        else u (DifferentialForm.powEquiv k (Sum.inl i)) := by
    intro i
    rw [pairRep_inl, slotPair_inl_eq_castSucc, slotMem_inl_eq_memIdx]
    split_ifs <;> rfl
  intro p q
  have hne : ∀ i : Fin k, Fin.last k ≠ Fin.castSucc i := fun i => (Fin.castSucc_lt_last i).ne'
  have hne' : ∀ i : Fin k, Fin.castSucc i ≠ Fin.last k := fun i => (Fin.castSucc_lt_last i).ne
  dsimp only
  rw [key p, key q]
  by_cases hp : Fin.castSucc (pairIdx p) = j <;> by_cases hq : Fin.castSucc (pairIdx q) = j
  · rw [if_pos hp, if_pos hq, hu, if_pos (Fin.castSucc_inj.1 (hp.trans hq.symm))]
    simp only [pairIdx_powEquiv, memIdx_powEquiv, slotPair_inr, slotMem_inr, if_true,
      removeWeight, hp]
  · rw [if_pos hp, if_neg hq, hu,
      if_neg fun h : pairIdx p = pairIdx q => hq (by rw [← h]; exact hp)]
    simp only [pairIdx_powEquiv, slotPair_inr, slotPair_inl_eq_castSucc, hne, if_false]
  · rw [if_neg hp, if_pos hq, hu,
      if_neg fun h : pairIdx p = pairIdx q => hp (by rw [h]; exact hq)]
    simp only [pairIdx_powEquiv, slotPair_inr, slotPair_inl_eq_castSucc, hne', if_false]
  · rw [if_neg hp, if_neg hq, hu]
    simp only [pairIdx_powEquiv, memIdx_powEquiv, slotPair_inl_eq_castSucc,
      slotMem_inl_eq_memIdx, Fin.castSucc_inj, removeWeight, hp, if_false]

/-- ★★ **The count.** The `k`-th power of a real 2-form on a weighted pair tuple of `k` pairs is
`k!` times the product of the weights. -/
theorem wedgePow_apply_of_isWeightedPairTuple (β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    ∀ (k : ℕ) (c : Fin k → ℝ) (u : Fin (2 * k) → E), IsWeightedPairTuple β c u →
      wedgePow β k u = (k.factorial : ℝ) * ∏ j, c j
  | 0, _, _, _ => by simp [wedgePow]
  | k + 1, c, u, hu => by
    simp only [wedgePow]
    rw [domDomCongr_apply, wedge_mul_apply_weightedPairs (isWeightedPairTuple_iff.1 hu)]
    have hterm : ∀ j : Fin (k + 1),
        wedgePow β k (fun i => u (DifferentialForm.powEquiv k (pairRep j (Sum.inl i))))
          = (k.factorial : ℝ) * ∏ i, removeWeight c j i := fun j =>
      wedgePow_apply_of_isWeightedPairTuple β k _ _ (hu.pairRep j)
    have hsum : ∀ j : Fin (k + 1),
        c j * ((k.factorial : ℝ) * ∏ i, removeWeight c j i) = k.factorial * ∏ j, c j :=
      fun j => by rw [mul_left_comm, mul_prod_removeWeight]
    simp only [hterm, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.factorial_succ]
    push_cast
    ring

/-- ★ On a pair tuple (all weights `1`) the `k`-th power is `k!`. -/
theorem wedgePow_apply_of_isPairTuple (β : E [⋀^Fin 2]→L[ℝ] ℝ) {u : Fin (2 * k) → E}
    (hu : IsWeightedPairTuple β (fun _ => 1) u) : wedgePow β k u = (k.factorial : ℝ) := by
  rw [wedgePow_apply_of_isWeightedPairTuple β k _ u hu]
  simp

end Tuple

end ContinuousAlternatingMap

end
