/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ModeLocality

/-!
# CV-8 (i): the local algebra — `SupportedOn` is a unital *-subalgebra

**Category:** CV (continuous variables — the multi-mode field).

`CV/ModeLocality.lean` defined `SupportedOn S` and proved that disjoint
supports commute. This module upgrades the support notion to what
Haag–Kastler actually posits: **the operators supported on `S` form a unital
*-subalgebra** — the *local algebra* of the region, at the finite cutoff:

* `SupportedOn.one`, `.add`, `.smul`, `.mul`, `.star` — closure under the
  *-algebra operations. The product case is the load-bearing one: the
  surviving intermediate configurations of `(A·B) c d` agree with `c` off
  `S`, and the bijection `e ↦ (e on S, c' off S)` matches the two sums
  entry-for-entry.
* `SupportedOn.mono` — a bigger region supports everything the smaller one
  does. Not a formality: the `indep` field for the bigger region gives
  *weaker* hypotheses, and the proof needs the same offDiag-kills-both
  rescue as the product case (a mode moved in `S' \ S` zeroes both
  entries).

These are exactly the pieces the spreading bound needs
(`CV/SupportSpreading.lean`): conjugation by a `T`-supported unitary lands
in the `S ∪ T` algebra by `star`, `mul`, and `mono` alone.

## References

`CV/ModeLocality.lean` (`SupportedOn`, `commute_of_disjointSupport`);
`CV/SupportSpreading.lean` (CV-8 (ii)–(iv)); `specs/cv-stage3-plan.md` §3b;
`specs/future-work.md` (row CV-8). Haag, *Local Quantum Physics* (1992).
-/

@[expose] public section

open Matrix

namespace CSD.CV

variable {K N : ℕ} {S S' : Finset (Fin K)}
variable {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}

/-! ### Closure under the *-algebra operations -/

/-- The identity is supported on every region. -/
protected theorem SupportedOn.one :
    SupportedOn S (1 : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) := by
  constructor
  · intro c d k _ hcd
    exact Matrix.one_apply_ne fun h => hcd (congrFun h k)
  · intro c d c' d' h1 h2 h3 h4
    by_cases h : c = d
    · have h' : c' = d' := funext fun k => by
        by_cases hk : k ∈ S
        · rw [← h1 k hk, ← h2 k hk, h]
        · exact h4 k hk
      rw [h, h', Matrix.one_apply_eq, Matrix.one_apply_eq]
    · have h' : c' ≠ d' := fun hcd' => h (funext fun k => by
        by_cases hk : k ∈ S
        · rw [h1 k hk, h2 k hk, hcd']
        · exact h3 k hk)
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']

/-- Sums of `S`-supported operators are `S`-supported. -/
protected theorem SupportedOn.add (hA : SupportedOn S A)
    (hB : SupportedOn S B) : SupportedOn S (A + B) := by
  constructor
  · intro c d k hk hcd
    rw [Matrix.add_apply, hA.offDiag hk hcd, hB.offDiag hk hcd, add_zero]
  · intro c d c' d' h1 h2 h3 h4
    rw [Matrix.add_apply, Matrix.add_apply, hA.indep h1 h2 h3 h4,
      hB.indep h1 h2 h3 h4]

/-- Differences of `S`-supported operators are `S`-supported. -/
protected theorem SupportedOn.sub (hA : SupportedOn S A)
    (hB : SupportedOn S B) : SupportedOn S (A - B) := by
  constructor
  · intro c d k hk hcd
    rw [Matrix.sub_apply, hA.offDiag hk hcd, hB.offDiag hk hcd, sub_zero]
  · intro c d c' d' h1 h2 h3 h4
    rw [Matrix.sub_apply, Matrix.sub_apply, hA.indep h1 h2 h3 h4,
      hB.indep h1 h2 h3 h4]

/-- Scalar multiples of `S`-supported operators are `S`-supported. -/
protected theorem SupportedOn.smul (z : ℂ) (hA : SupportedOn S A) :
    SupportedOn S (z • A) := by
  constructor
  · intro c d k hk hcd
    rw [Matrix.smul_apply, hA.offDiag hk hcd, smul_zero]
  · intro c d c' d' h1 h2 h3 h4
    rw [Matrix.smul_apply, Matrix.smul_apply, hA.indep h1 h2 h3 h4]

/-- Adjoints of `S`-supported operators are `S`-supported. -/
protected theorem SupportedOn.star (hA : SupportedOn S A) :
    SupportedOn S (star A) := by
  constructor
  · intro c d k hk hcd
    rw [Matrix.star_apply, hA.offDiag hk (Ne.symm hcd), star_zero]
  · intro c d c' d' h1 h2 h3 h4
    rw [Matrix.star_apply, Matrix.star_apply,
      hA.indep h2 h1 (fun k hk => (h3 k hk).symm)
        (fun k hk => (h4 k hk).symm)]

/-- **Products of `S`-supported operators are `S`-supported** — the closure
that makes `SupportedOn S` an algebra. The surviving intermediate
configurations agree with `c` off `S`; the bijection
`e ↦ (e on S, c' off S)` matches the two collapsed sums term-for-term. -/
protected theorem SupportedOn.mul (hA : SupportedOn S A)
    (hB : SupportedOn S B) : SupportedOn S (A * B) := by
  classical
  constructor
  · intro c d k hk hcd
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases h : c k = e k
    · rw [hB.offDiag hk (fun hed => hcd (h.trans hed)), mul_zero]
    · rw [hA.offDiag hk h, zero_mul]
  · intro c d c' d' h1 h2 h3 h4
    rw [Matrix.mul_apply, Matrix.mul_apply]
    -- Restrict both sums to the surviving intermediate configurations.
    have hcollapse : ∀ (x y : FieldConfig K N),
        (∑ e, A x e * B e y)
          = ∑ e ∈ Finset.univ.filter
              (fun e : FieldConfig K N => ∀ k, k ∉ S → e k = x k),
              A x e * B e y := by
      intro x y
      refine (Finset.sum_filter_of_ne fun e _ hne => ?_).symm
      by_contra hnot
      push Not at hnot
      obtain ⟨k, hk, hek⟩ := hnot
      exact hne (by rw [hA.offDiag hk (fun h => hek h.symm), zero_mul])
    rw [hcollapse c d, hcollapse c' d']
    -- The bijection between the two surviving families.
    refine Finset.sum_bij'
      (fun e _ => fun k => if k ∈ S then e k else c' k)
      (fun e _ => fun k => if k ∈ S then e k else c k) ?_ ?_ ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨Finset.mem_univ _, fun k hk => by simp [hk]⟩
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨Finset.mem_univ _, fun k hk => by simp [hk]⟩
    · intro e he
      rw [Finset.mem_filter] at he
      funext k
      by_cases hk : k ∈ S
      · simp [hk]
      · simp only [hk, if_false]
        exact (he.2 k hk).symm
    · intro e he
      rw [Finset.mem_filter] at he
      funext k
      by_cases hk : k ∈ S
      · simp [hk]
      · simp only [hk, if_false]
        exact (he.2 k hk).symm
    · intro e he
      rw [Finset.mem_filter] at he
      have hAeq : A c e = A c' (fun k => if k ∈ S then e k else c' k) :=
        hA.indep h1 (fun k hk => by simp [hk])
          (fun k hk => (he.2 k hk).symm) (fun k hk => by simp [hk])
      have hBeq : B e d = B (fun k => if k ∈ S then e k else c' k) d' :=
        hB.indep (fun k hk => by simp [hk]) h2
          (fun k hk => (he.2 k hk).trans (h3 k hk))
          (fun k hk => by simp only [hk, if_false]; exact h4 k hk)
      rw [hAeq, hBeq]

/-! ### Monotonicity -/

/-- **Monotonicity**: a bigger region supports everything the smaller one
does. The `indep` case needs the offDiag rescue — a mode moved in `S' \ S`
zeroes both entries. -/
protected theorem SupportedOn.mono (hSS' : S ⊆ S') (hA : SupportedOn S A) :
    SupportedOn S' A := by
  constructor
  · intro c d k hk hcd
    exact hA.offDiag (fun hkS => hk (hSS' hkS)) hcd
  · intro c d c' d' h1 h2 h3 h4
    by_cases hout : ∀ k, k ∉ S → c k = d k
    · have hout' : ∀ k, k ∉ S → c' k = d' k := fun k hk => by
        by_cases hk' : k ∈ S'
        · rw [← h1 k hk', ← h2 k hk']
          exact hout k hk
        · exact h4 k hk'
      exact hA.indep (fun k hk => h1 k (hSS' hk))
        (fun k hk => h2 k (hSS' hk)) hout hout'
    · push Not at hout
      obtain ⟨k, hkS, hne⟩ := hout
      have hkS' : k ∈ S' := by
        by_contra hk'
        exact hne (h3 k hk')
      rw [hA.offDiag hkS hne,
        hA.offDiag hkS (by rw [← h1 k hkS', ← h2 k hkS']; exact hne)]

end CSD.CV
