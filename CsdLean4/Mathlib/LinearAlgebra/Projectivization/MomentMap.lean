/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The torus moment map on complex projective space, in coordinates

**Category:** 1-Mathlib (CSD-free; the coordinate function `[z] ↦ (|zᵢ|²/‖z‖²)ᵢ` on `ℙ ℂ (ℂⁿ)`).

A point of `ℙ ℂ (EuclideanSpace ℂ ι)` is a ray `[z]`, and the squared moduli of its
coordinates, normalised by `‖z‖²`, do not depend on the representative. The resulting function

    `momentMap [z] i = ‖z i‖² / ‖z‖²`

takes values in the standard simplex: every coordinate is nonnegative and the coordinates sum
to one. It is the moment map of the coordinate-phase torus action for the Fubini–Study form,
up to the factor that form's normalisation fixes (the Hamiltonian of the action is
`2 Σ θₖ momentMap · k`, so the moment map in the Hamiltonian sense is twice this function);
this file proves only the coordinate facts, and the manifold-level statement that earns the
name lives downstream (`Projectivization.torusField_isHamiltonianVectorField` and
`range_momentMap` in `Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean`).

## Main declarations

* `Projectivization.momentMap` — the coordinate function, defined through `rep`.
* `momentMap_mk` — its value on `mk ℂ ψ hψ` is `‖ψ i‖² / ‖ψ‖²` (representative independence).
* `momentMap_nonneg`, `momentMap_sum_eq_one`, `momentMap_le_one` — the simplex constraints.
* `momentMap_mk_eq_inner_sq` — for a unit vector, `momentMap [ψ] i = ‖⟨eᵢ, ψ⟩‖²` with
  `eᵢ = EuclideanSpace.single i 1`: the coordinate is the squared overlap with the `i`-th basis
  vector.
* `momentMap_mk_of_norm_eq` — equal-modulus coordinates land at the barycentre `1/N`.
* `continuous_momentMap`, `measurable_momentMap` — regularity, by descent through the quotient
  map `mk'` (the defining formula goes through the choice-based `rep`, which is not continuous).

## Provenance

Moved verbatim from `CsdLean4/LF4/MomentMap.lean` (2026-09-16), where it was introduced as the
torus moment map whose coordinates are the Born weights of a preparation in the measurement
eigenbasis. `CSD.LF4` re-exports these names, so that file remains the entry point for the
programme-level reading; this file is the mathematics. Recorded in the completed-work ledger
(`specs/future-work.md`, KG-4).

## References

* Bengtsson, Życzkowski, *Geometry of Quantum States*, 2nd ed., §4.4 (the Fubini–Study geometry
  of `ℂℙⁿ` and the torus action).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The torus moment map on `ℙ ℂ (ℂᴺ)`, in coordinates: `Φ([z])ᵢ = ‖zᵢ‖²/‖z‖²`.
Well defined on the projective point (scale invariant; see `momentMap_mk`). -/
noncomputable def momentMap (p : ℙ ℂ (EuclideanSpace ℂ ι)) (i : ι) : ℝ :=
  ‖p.rep i‖ ^ 2 / ‖p.rep‖ ^ 2

omit [DecidableEq ι] in
/-- Each moment coordinate is nonnegative. -/
lemma momentMap_nonneg (p : ℙ ℂ (EuclideanSpace ℂ ι)) (i : ι) :
    0 ≤ momentMap p i :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

omit [DecidableEq ι] in
/-- The moment coordinates sum to one: the image lands in the standard simplex. -/
lemma momentMap_sum_eq_one (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    ∑ i, momentMap p i = 1 := by
  have hrep2 : ‖p.rep‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr p.rep_nonzero)
  unfold momentMap
  rw [← Finset.sum_div, ← EuclideanSpace.norm_sq_eq, div_self hrep2]

omit [DecidableEq ι] in
/-- Each moment coordinate is at most one (`‖p.rep i‖² ≤ ∑ⱼ ‖p.rep j‖² = ‖p.rep‖²`). -/
lemma momentMap_le_one (p : ℙ ℂ (EuclideanSpace ℂ ι)) (i : ι) :
    momentMap p i ≤ 1 := by
  have hpos : 0 < ‖p.rep‖ ^ 2 := pow_pos (norm_pos_iff.mpr p.rep_nonzero) 2
  rw [momentMap, div_le_one hpos, EuclideanSpace.norm_sq_eq]
  exact Finset.single_le_sum (f := fun j => ‖p.rep j‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

omit [DecidableEq ι] in
/-- The coordinate ratio `‖vᵢ‖²/‖v‖²` is invariant under nonzero rescaling of `v`
(the projective well-definedness of `momentMap`). -/
lemma momentRatio_smul (c : ℂ) (hc : c ≠ 0) (v : EuclideanSpace ℂ ι) (i : ι) :
    ‖(c • v) i‖ ^ 2 / ‖c • v‖ ^ 2 = ‖v i‖ ^ 2 / ‖v‖ ^ 2 := by
  rw [PiLp.smul_apply, smul_eq_mul, norm_smul, norm_mul, mul_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]

omit [DecidableEq ι] in
/-- The moment map evaluated at a representative `ψ`: `Φ([ψ])ᵢ = ‖ψᵢ‖²/‖ψ‖²`.
The value depends only on `ψ` (not on the chosen `rep`), by scale invariance. -/
lemma momentMap_mk (ψ : EuclideanSpace ℂ ι) (hψ : ψ ≠ 0) (i : ι) :
    momentMap (mk ℂ ψ hψ) i = ‖ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  obtain ⟨a, ha⟩ :=
    (mk_eq_mk_iff ℂ (mk ℂ ψ hψ).rep ψ (rep_nonzero _) hψ).mp (mk_rep _)
  unfold momentMap
  rw [← ha]
  simp only [Units.smul_def]
  exact momentRatio_smul (↑a) (Units.ne_zero a) ψ i

/-- **The moment coordinate is a squared overlap.** For a unit vector `ψ`, the `i`-th coordinate
of the moment map at `[ψ]` equals `‖⟨eᵢ, ψ⟩‖²` for the standard basis vector
`eᵢ = EuclideanSpace.single i 1`. -/
theorem momentMap_mk_eq_inner_sq (ψ : EuclideanSpace ℂ ι) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : ι) :
    momentMap (mk ℂ ψ hψ0) i = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  rw [momentMap_mk ψ hψ0 i, hψ, one_pow, div_one,
      EuclideanSpace.inner_single_left, map_one, one_mul]

omit [DecidableEq ι] in
/-- **Equal-modulus coordinates sit at the barycentre.** If every coordinate of `ψ` has the same
modulus, the moment map of `[ψ]` is the uniform weight `1/|ι|` in every coordinate; the
normalisation is immaterial (`momentMap_mk` divides it out). -/
lemma momentMap_mk_of_norm_eq (ψ : EuclideanSpace ℂ ι) (hψ0 : ψ ≠ 0) {a : ℝ}
    (hψ : ∀ j, ‖ψ j‖ = a) (i : ι) :
    momentMap (mk ℂ ψ hψ0) i = 1 / Fintype.card ι := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hψ0 (by ext j; simpa using hψ j)
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (@Fintype.card_pos ι _ ⟨i⟩).ne'
  rw [momentMap_mk, EuclideanSpace.norm_sq_eq]
  simp only [hψ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-! ### Regularity: `momentMap` is continuous, hence measurable

`momentMap` is *defined* through `p.rep`, a `Classical.choice` representative, so it cannot be
attacked directly: `Projectivization.rep` is not continuous as a map out of `ℙ`. The route is
the quotient. The coordinate ratio `v ↦ ‖vᵢ‖²/‖v‖²` is continuous on the nonzero subtype and
scale invariant (`momentRatio_smul`), and `mk'` is a quotient map (`isQuotientMap_mk'`), so the
descended function is continuous. Measurability follows because `ℙ K V` carries the Borel
σ-algebra of that topology (`instBorelSpace`). -/

omit [DecidableEq ι] in
/-- **The moment coordinate is continuous**, by descent through the quotient map `mk'`. -/
theorem continuous_momentMap (i : ι) :
    Continuous (fun p : ℙ ℂ (EuclideanSpace ℂ ι) => momentMap p i) := by
  rw [continuous_iff_continuous_comp_mk']
  have hcomp : ((fun p : ℙ ℂ (EuclideanSpace ℂ ι) => momentMap p i) ∘ (mk' ℂ))
      = fun v : { v : EuclideanSpace ℂ ι // v ≠ 0 } =>
          ‖(v : EuclideanSpace ℂ ι) i‖ ^ 2 / ‖(v : EuclideanSpace ℂ ι)‖ ^ 2 := by
    funext v
    exact momentMap_mk (v : EuclideanSpace ℂ ι) v.2 i
  rw [hcomp]
  have hnum : Continuous fun v : { v : EuclideanSpace ℂ ι // v ≠ 0 } =>
      ‖(v : EuclideanSpace ℂ ι) i‖ ^ 2 :=
    (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp continuous_subtype_val).norm).pow 2
  have hden : Continuous fun v : { v : EuclideanSpace ℂ ι // v ≠ 0 } =>
      ‖(v : EuclideanSpace ℂ ι)‖ ^ 2 :=
    (continuous_subtype_val.norm).pow 2
  exact hnum.div hden fun v => pow_ne_zero _ (norm_ne_zero_iff.mpr v.2)

omit [DecidableEq ι] in
/-- **The moment coordinate is measurable**, since `ℙ ℂ V` carries the Borel σ-algebra of the
quotient topology (`instBorelSpace`). -/
theorem measurable_momentMap (i : ι) :
    Measurable (fun p : ℙ ℂ (EuclideanSpace ℂ ι) => momentMap p i) :=
  (continuous_momentMap i).measurable

end Projectivization
