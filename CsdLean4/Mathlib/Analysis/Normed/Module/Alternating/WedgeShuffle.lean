/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.WedgeCLM
public import Mathlib.GroupTheory.Perm.Finite

/-!
# The shuffle sum of a wedge with a 2-form, on a pair family

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Analysis.Normed.Module.Alternating`).

Milestone **M6(b)** of the top-power plan, the combinatorial half. The wedge
`α ∧ β` of a `2k`-form with a 2-form, evaluated on `2k + 2` vectors, is a signed sum over the
shuffle classes `Equiv.Perm.ModSumCongr (Fin (2k)) (Fin 2)` (`wedge_apply`). When the vectors
come in `k + 1` **pairs** on which `β` is `±1` within a pair and `0` across pairs
(`IsPairFamily`), only the classes sending the two `β`-slots into one pair survive, and each
such class has a representative made of **two disjoint transpositions** — of sign `+1` — that
moves that pair into the `β`-slots and leaves a family of `k` pairs behind:

* `slotPair`, `slotMem`, `slotOf` — the bookkeeping of pairs on `Fin (2k) ⊕ Fin 2` (`inl p` is
  in pair `p / 2`, member `p % 2`; the two `inr` slots form the last pair);
* `pairRep j` — the two-transposition representative for pair `j` (the identity for the last
  pair); `pairRep_inl`, `pairRep_inr`, ★ `sign_pairRep`;
* `modSumCongr_mk_eq_of_inr`, `exists_inr_eq_of_mk_eq` — two permutations are in one shuffle
  class iff they send the `inr` slots to the same places (Mathlib's
  `mem_sumCongrHom_range_of_perm_mapsTo_inl`);
* `classTerm`, `classTerm_mk''`, `slotPair_eq_of_classTerm_ne_zero`,
  `mk_eq_pairRep_of_classTerm_ne_zero`, `classTerm_pairRep`;
* ★★ `wedge_mul_apply_pairs` — **the shuffle sum on a pair family**:
  `(α ∧ β) u = ∑ⱼ α (u ∘ pairRep j ∘ inl)`.

No sign is ever computed beyond `sign (swap · ·) = -1` twice: that is the whole point of the
two-transposition representative, and it is what makes the count of the top power of the
standard symplectic form (`Instances/ProjectiveSpaceFubiniStudyVolume.lean`) an induction with
no combinatorics left in it.

## Honest scope

⚠️ Real-valued forms with the codomains paired by multiplication only. ⚠️ Nothing is said about
`α ∧ β` off pair families.

**Provenance and references.** The top-power plan (M6(b)); `Alternating/Wedge.lean` (`wedge_apply`),
`Alternating/WedgeCLM.lean` (`liftTensor_summand_mk''`);
`Mathlib/LinearAlgebra/Alternating/DomCoprod.lean`; `Mathlib/GroupTheory/Perm/Finite.lean`;
the completed-work ledger.
-/

@[expose] public section

open Equiv

namespace ContinuousAlternatingMap

section Slots

variable {k : ℕ}

/-- The pair a slot of `Fin (2k) ⊕ Fin 2` belongs to: `inl p` is in pair `p / 2`, the two `inr`
slots form the last pair. -/
def slotPair : Fin (2 * k) ⊕ Fin 2 → Fin (k + 1)
  | .inl p => ⟨p / 2, by omega⟩
  | .inr _ => Fin.last k

/-- Which member of its pair a slot is. -/
def slotMem : Fin (2 * k) ⊕ Fin 2 → Fin 2
  | .inl p => ⟨p % 2, by omega⟩
  | .inr b => b

/-- The slot of member `m` of pair `j`. -/
def slotOf (j : Fin (k + 1)) (m : Fin 2) : Fin (2 * k) ⊕ Fin 2 :=
  if h : (j : ℕ) < k then .inl ⟨2 * j + m, by omega⟩ else .inr m

theorem slotPair_slotOf (j : Fin (k + 1)) (m : Fin 2) : slotPair (slotOf j m) = j := by
  unfold slotOf
  split_ifs with h
  · simp only [slotPair]; ext; simp; omega
  · simp only [slotPair]; ext; simp; omega

theorem slotMem_slotOf (j : Fin (k + 1)) (m : Fin 2) : slotMem (slotOf j m) = m := by
  unfold slotOf
  split_ifs with h
  · simp only [slotMem]; ext; simp; omega
  · rfl

theorem slotOf_slotPair_slotMem (x : Fin (2 * k) ⊕ Fin 2) :
    slotOf (slotPair x) (slotMem x) = x := by
  rcases x with p | b
  · show slotOf ⟨(p : ℕ) / 2, by omega⟩ ⟨(p : ℕ) % 2, by omega⟩ = Sum.inl p
    unfold slotOf
    rw [dif_pos (show ((⟨(p : ℕ) / 2, by omega⟩ : Fin (k + 1)) : ℕ) < k by
      show (p : ℕ) / 2 < k; omega)]
    refine congrArg Sum.inl (Fin.ext ?_)
    show 2 * ((p : ℕ) / 2) + (p : ℕ) % 2 = p
    exact Nat.div_add_mod (p : ℕ) 2
  · simp [slotPair, slotMem, slotOf]

theorem slot_ext {x y : Fin (2 * k) ⊕ Fin 2} (h₁ : slotPair x = slotPair y)
    (h₂ : slotMem x = slotMem y) : x = y := by
  rw [← slotOf_slotPair_slotMem x, ← slotOf_slotPair_slotMem y, h₁, h₂]

/-- The two-transposition representative of the shuffle class that sends pair `j` into the two
`inr` slots (the identity when `j` is the last pair). -/
def pairRep (j : Fin (k + 1)) : Perm (Fin (2 * k) ⊕ Fin 2) :=
  if h : (j : ℕ) < k then
    swap (.inl ⟨2 * j, by omega⟩) (.inr 0) * swap (.inl ⟨2 * j + 1, by omega⟩) (.inr 1)
  else 1

theorem pairRep_inr (j : Fin (k + 1)) (m : Fin 2) : pairRep j (.inr m) = slotOf j m := by
  unfold pairRep slotOf
  split_ifs with h
  · fin_cases m
    · simp [Perm.mul_apply, swap_apply_of_ne_of_ne]
    · simp [Perm.mul_apply, swap_apply_of_ne_of_ne, swap_apply_right]
  · rfl

theorem pairRep_inl (j : Fin (k + 1)) (p : Fin (2 * k)) :
    pairRep j (.inl p) = if slotPair (.inl p) = j then .inr (slotMem (.inl p)) else .inl p := by
  unfold pairRep
  split_ifs with h hp hp
  · have hp' : (p : ℕ) / 2 = j := by
      have := congrArg Fin.val hp; simpa [slotPair] using this
    have hcases : (p : ℕ) = 2 * j ∨ (p : ℕ) = 2 * j + 1 := by
      rcases Nat.mod_two_eq_zero_or_one (p : ℕ) with h0 | h1 <;> omega
    simp only [slotMem]
    rcases hcases with hpv | hpv
    · have hpe : p = ⟨2 * j, by omega⟩ := Fin.ext hpv
      rw [hpe]
      have hne : (Sum.inl (⟨2 * j, by omega⟩ : Fin (2 * k)) : Fin (2 * k) ⊕ Fin 2)
          ≠ Sum.inl ⟨2 * j + 1, by omega⟩ := by
        intro he; have := congrArg Fin.val (Sum.inl.inj he); simp at this
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hne Sum.inl_ne_inr, swap_apply_left]
      congr 1; ext; simp
    · have hpe : p = ⟨2 * j + 1, by omega⟩ := Fin.ext hpv
      rw [hpe]
      have hne : (Sum.inr (1 : Fin 2) : Fin (2 * k) ⊕ Fin 2) ≠ Sum.inr 0 := by simp
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne Sum.inr_ne_inl hne]
      congr 1; ext; simp
  · have h1 : (Sum.inl p : Fin (2 * k) ⊕ Fin 2) ≠ .inl ⟨2 * j, by omega⟩ := by
      intro he; apply hp; simp only [slotPair]; ext
      have := congrArg Fin.val (Sum.inl.inj he); simp at this ⊢; omega
    have h2 : (Sum.inl p : Fin (2 * k) ⊕ Fin 2) ≠ .inl ⟨2 * j + 1, by omega⟩ := by
      intro he; apply hp; simp only [slotPair]; ext
      have := congrArg Fin.val (Sum.inl.inj he); simp at this ⊢; omega
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 Sum.inl_ne_inr,
      swap_apply_of_ne_of_ne h1 Sum.inl_ne_inr]
  · exfalso; apply h; simp only [slotPair] at hp
    have := congrArg Fin.val hp; simp at this; omega
  · rfl

theorem sign_pairRep (j : Fin (k + 1)) : Perm.sign (pairRep j) = 1 := by
  unfold pairRep
  split_ifs with h
  · rw [Perm.sign_mul, Perm.sign_swap (by simp), Perm.sign_swap (by simp)]; norm_num
  · simp

end Slots

section Classes

variable {k : ℕ}

open Equiv.Perm

/-- Two permutations whose images of the `inr` slots agree lie in the same shuffle class. -/
theorem modSumCongr_mk_eq_of_inr {σ₁ σ₂ : Perm (Fin (2 * k) ⊕ Fin 2)}
    (h : ∀ m, ∃ m', σ₁ (Sum.inr m) = σ₂ (Sum.inr m')) :
    (Quotient.mk'' σ₁ : Perm.ModSumCongr (Fin (2 * k)) (Fin 2)) = Quotient.mk'' σ₂ := by
  refine (QuotientGroup.eq (s := (sumCongrHom (Fin (2 * k)) (Fin 2)).range)).2
    (mem_sumCongrHom_range_of_perm_mapsTo_inl ?_)
  rintro _ ⟨p, rfl⟩
  rw [Perm.mul_apply]
  rcases hx : σ₁⁻¹ (σ₂ (Sum.inl p)) with q | m
  · exact ⟨q, rfl⟩
  · exfalso
    have h1 : σ₁ (Sum.inr m) = σ₂ (Sum.inl p) := by
      rw [← hx]; simp
    obtain ⟨m', hm'⟩ := h m
    rw [hm'] at h1
    exact Sum.inr_ne_inl (σ₂.injective h1)

/-- In one shuffle class, the images of the `inr` slots agree. -/
theorem exists_inr_eq_of_mk_eq {σ ρ : Perm (Fin (2 * k) ⊕ Fin 2)}
    (h : (Quotient.mk'' σ : Perm.ModSumCongr (Fin (2 * k)) (Fin 2)) = Quotient.mk'' ρ)
    (m : Fin 2) : ∃ m', σ (Sum.inr m) = ρ (Sum.inr m') := by
  obtain ⟨⟨τ₁, τ₂⟩, hτ⟩ :=
    (QuotientGroup.eq (s := (sumCongrHom (Fin (2 * k)) (Fin 2)).range)).1 h
  refine ⟨τ₂⁻¹ m, ?_⟩
  have hτ' : τ₁.sumCongr τ₂ = σ⁻¹ * ρ := hτ
  have hρ : ρ = σ * τ₁.sumCongr τ₂ := by
    rw [hτ', mul_inv_cancel_left]
  rw [hρ, Perm.mul_apply, Perm.sumCongr_apply, Sum.map_inr]
  simp

end Classes

section Shuffle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

open Equiv.Perm ContinuousLinearMap

/-- The sign of a pairing: `1` for (member 0, member 1), `-1` the other way round, `0` otherwise. -/
def pairSign (a b : Fin 2) : ℝ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

/-- A family of `2k + 2` vectors is a **pair family** for the 2-form `β` when `β` pairs the two
members of each pair to `±1` and kills everything else. -/
def IsPairFamily (β : E [⋀^Fin 2]→L[ℝ] ℝ) (u : Fin (2 * k) ⊕ Fin 2 → E) : Prop :=
  ∀ x y, β ![u x, u y] = if slotPair x = slotPair y then pairSign (slotMem x) (slotMem y) else 0

/-- One shuffle-class term of the real-valued wedge. -/
noncomputable def classTerm (α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ) (β : E [⋀^Fin 2]→L[ℝ] ℝ)
    (u : Fin (2 * k) ⊕ Fin 2 → E) (q : Perm.ModSumCongr (Fin (2 * k)) (Fin 2)) : ℝ :=
  liftTensor (mul ℝ ℝ) (AlternatingMap.domCoprod.summand α.toAlternatingMap β.toAlternatingMap q u)

theorem classTerm_mk'' (α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ) (β : E [⋀^Fin 2]→L[ℝ] ℝ)
    (u : Fin (2 * k) ⊕ Fin 2 → E) (σ : Perm (Fin (2 * k) ⊕ Fin 2)) :
    classTerm α β u (Quotient.mk'' σ)
      = (Perm.sign σ : ℤ) • (α (fun i => u (σ (Sum.inl i))) * β (fun i => u (σ (Sum.inr i)))) := by
  rw [classTerm, liftTensor_summand_mk'']
  rfl

theorem wedge_mul_apply_eq_sum_classTerm (α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ)
    (β : E [⋀^Fin 2]→L[ℝ] ℝ) (u : Fin (2 * k) ⊕ Fin 2 → E) :
    wedge (mul ℝ ℝ) α β u = ∑ q, classTerm α β u q := by
  rw [wedge_apply]
  rfl

theorem beta_inr_eq (β : E [⋀^Fin 2]→L[ℝ] ℝ) (u : Fin (2 * k) ⊕ Fin 2 → E)
    (σ : Perm (Fin (2 * k) ⊕ Fin 2)) :
    β (fun i => u (σ (Sum.inr i))) = β ![u (σ (Sum.inr 0)), u (σ (Sum.inr 1))] := by
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A class term vanishes unless the two `inr` slots land in one pair. -/
theorem slotPair_eq_of_classTerm_ne_zero {α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ}
    {β : E [⋀^Fin 2]→L[ℝ] ℝ} {u : Fin (2 * k) ⊕ Fin 2 → E} (hu : IsPairFamily β u)
    (σ : Perm (Fin (2 * k) ⊕ Fin 2)) (h : classTerm α β u (Quotient.mk'' σ) ≠ 0) :
    slotPair (σ (Sum.inr 0)) = slotPair (σ (Sum.inr 1)) := by
  by_contra hne
  apply h
  rw [classTerm_mk'', beta_inr_eq, hu, if_neg hne, mul_zero, smul_zero]

/-- A non-vanishing class is the class of the two-transposition representative of its pair. -/
theorem mk_eq_pairRep_of_classTerm_ne_zero {α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ}
    {β : E [⋀^Fin 2]→L[ℝ] ℝ} {u : Fin (2 * k) ⊕ Fin 2 → E} (hu : IsPairFamily β u)
    (σ : Perm (Fin (2 * k) ⊕ Fin 2)) (h : classTerm α β u (Quotient.mk'' σ) ≠ 0) :
    (Quotient.mk'' σ : Perm.ModSumCongr (Fin (2 * k)) (Fin 2))
      = Quotient.mk'' (pairRep (slotPair (σ (Sum.inr 0)))) := by
  have hp := slotPair_eq_of_classTerm_ne_zero hu σ h
  refine modSumCongr_mk_eq_of_inr fun m => ⟨slotMem (σ (Sum.inr m)), ?_⟩
  rw [pairRep_inr]
  fin_cases m
  · exact (slotOf_slotPair_slotMem _).symm
  · rw [hp]
    exact (slotOf_slotPair_slotMem _).symm

/-- The class term of the representative of pair `j`. -/
theorem classTerm_pairRep {α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ} {β : E [⋀^Fin 2]→L[ℝ] ℝ}
    {u : Fin (2 * k) ⊕ Fin 2 → E} (hu : IsPairFamily β u) (j : Fin (k + 1)) :
    classTerm α β u (Quotient.mk'' (pairRep j)) = α (fun i => u (pairRep j (Sum.inl i))) := by
  rw [classTerm_mk'', sign_pairRep, beta_inr_eq, pairRep_inr, pairRep_inr, hu,
    if_pos (by rw [slotPair_slotOf, slotPair_slotOf]), slotMem_slotOf, slotMem_slotOf]
  simp [pairSign]

/-- ★ **The shuffle sum on a pair family.** The wedge of a `2k`-form with a 2-form, on a pair
family, is the sum over the pairs of the `2k`-form on the family with that pair moved into the
2-form's slots. -/
theorem wedge_mul_apply_pairs {α : E [⋀^Fin (2 * k)]→L[ℝ] ℝ} {β : E [⋀^Fin 2]→L[ℝ] ℝ}
    {u : Fin (2 * k) ⊕ Fin 2 → E} (hu : IsPairFamily β u) :
    wedge (mul ℝ ℝ) α β u = ∑ j : Fin (k + 1), α (fun i => u (pairRep j (Sum.inl i))) := by
  rw [wedge_mul_apply_eq_sum_classTerm]
  refine Finset.sum_bij_ne_zero (fun q _ _ => slotPair (Quotient.out q (Sum.inr 0)))
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro q₁ _ h₁ q₂ _ h₂ hj
    have hq₁ : (Quotient.mk'' (Quotient.out q₁) : Perm.ModSumCongr (Fin (2 * k)) (Fin 2)) = q₁ :=
      Quotient.out_eq q₁
    have hq₂ : (Quotient.mk'' (Quotient.out q₂) : Perm.ModSumCongr (Fin (2 * k)) (Fin 2)) = q₂ :=
      Quotient.out_eq q₂
    have e₁ := mk_eq_pairRep_of_classTerm_ne_zero hu (Quotient.out q₁) (by rwa [hq₁])
    have e₂ := mk_eq_pairRep_of_classTerm_ne_zero hu (Quotient.out q₂) (by rwa [hq₂])
    rw [hq₁] at e₁
    rw [hq₂] at e₂
    rw [e₁, e₂, hj]
  · intro j _ hj
    refine ⟨Quotient.mk'' (pairRep j), Finset.mem_univ _, ?_, ?_⟩
    · rwa [classTerm_pairRep hu]
    · have hq : (Quotient.mk'' (Quotient.out (Quotient.mk'' (pairRep j) :
          Perm.ModSumCongr (Fin (2 * k)) (Fin 2))) : Perm.ModSumCongr (Fin (2 * k)) (Fin 2))
          = Quotient.mk'' (pairRep j) := Quotient.out_eq _
      obtain ⟨m', hm'⟩ := exists_inr_eq_of_mk_eq hq 0
      rw [hm', pairRep_inr, slotPair_slotOf]
  · intro q _ hq
    have hq' : (Quotient.mk'' (Quotient.out q) : Perm.ModSumCongr (Fin (2 * k)) (Fin 2)) = q :=
      Quotient.out_eq q
    have e := mk_eq_pairRep_of_classTerm_ne_zero hu (Quotient.out q) (by rwa [hq'])
    rw [hq'] at e
    exact (congrArg (classTerm α β u) e).trans (classTerm_pairRep hu _)

end Shuffle

end ContinuousAlternatingMap
