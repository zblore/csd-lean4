/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Lebesgue measure on `ℂⁿ` as the Haar measure of its standard real basis

**Category:** 1-Mathlib (CSD-free; upstream targets
`Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean` and
`Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean`).

`Fin n → ℂ` carries the product Lebesgue measure `volume`, and `EuclideanSpace ℂ (Fin n)` the
volume of its real inner-product structure. Both are the Haar measure of the standard real basis
`(e_j, i·e_j)_j`, and the identification `ofLp` between the two spaces is volume preserving.

* `parallelepiped_pi_basis` — a product basis has the product parallelepiped;
* `Complex.volume_parallelepiped_basisOneI` — Lebesgue measure on `ℂ` gives the unit square of
  `basisOneI` mass `1` (`basisOneI` is the orthonormal basis `orthonormalBasisOneI`);
* ★ `Complex.addHaar_pi_basisOneI_reindex` — **the Haar measure of the standard real basis of
  `Fin n → ℂ`** (any reindexing of `Pi.basis fun _ => basisOneI`) **is Lebesgue measure**;
* `Complex.euclideanBasis n`, `Complex.orthonormal_euclideanBasis`,
  `Complex.euclideanOrthonormalBasis n` — the same family in `EuclideanSpace ℂ (Fin n)`, indexed by
  `Fin (2 * n)`, is a real orthonormal basis;
* ★ `Complex.measurePreserving_ofLp` — **`ofLp : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ)` is volume
  preserving**, the inner-product volume on the left and the product Lebesgue measure on the right.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- The parallelepiped of a product basis is the product of the parallelepipeds. -/
theorem parallelepiped_pi_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → Type*}
    [∀ i, Fintype (η i)] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℝ (M i)]
    (b : ∀ i, Module.Basis (η i) ℝ (M i)) :
    parallelepiped (Pi.basis b) = Set.pi Set.univ fun i => parallelepiped (b i) := by
  ext x
  simp only [mem_parallelepiped_iff, Set.mem_pi, Set.mem_univ, true_implies]
  have key : ∀ (t : (Σ i, η i) → ℝ) (i : ι),
      (∑ jk, t jk • Pi.basis b jk) i = ∑ k, t ⟨i, k⟩ • b i k := by
    intro t i
    rw [Finset.sum_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    simp only [Pi.smul_apply, Pi.basis_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj.symm]
    · simp
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    exact ⟨fun k => t ⟨i, k⟩, ⟨fun k => ht.1 ⟨i, k⟩, fun k => ht.2 ⟨i, k⟩⟩, key t i⟩
  · intro h
    choose t ht using h
    refine ⟨fun jk => t jk.1 jk.2, ⟨fun jk => (ht jk.1).1.1 jk.2, fun jk => (ht jk.1).1.2 jk.2⟩, ?_⟩
    funext i
    rw [key]
    exact (ht i).2

namespace Complex

/-- Lebesgue measure on `ℂ` gives the unit square `parallelepiped basisOneI` mass `1`: `basisOneI`
is the orthonormal basis `orthonormalBasisOneI`. -/
theorem volume_parallelepiped_basisOneI : volume (parallelepiped basisOneI) = 1 := by
  have h : (⇑basisOneI : Fin 2 → ℂ) = ⇑orthonormalBasisOneI := by
    rw [← toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis]
  rw [h]
  exact orthonormalBasisOneI.volume_parallelepiped

/-- ★ **The Haar measure of the standard real basis of `Fin n → ℂ` is Lebesgue measure**, for any
indexing of the family `(e_j, i·e_j)_j`: the reindexing does not change the Haar measure, the
product basis has the product unit cube, and each factor's unit square has Lebesgue mass `1`. -/
theorem addHaar_pi_basisOneI_reindex {n : ℕ} {ι : Type*} [Fintype ι]
    (e : (Σ _ : Fin n, Fin 2) ≃ ι) :
    ((Pi.basis fun _ : Fin n => basisOneI).reindex e).addHaar = volume := by
  rw [Module.Basis.addHaar_reindex, Module.Basis.addHaar_eq_iff, Module.Basis.coe_parallelepiped,
    parallelepiped_pi_basis, volume_pi, Measure.pi_pi, Finset.prod_const,
    volume_parallelepiped_basisOneI, one_pow]

/-- The index equivalence `(Σ _ : Fin n, Fin 2) ≃ Fin (2 * n)` behind the standard real basis. -/
def sigmaFinTwoEquiv (n : ℕ) : (Σ _ : Fin n, Fin 2) ≃ Fin (2 * n) :=
  (Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans (finProdFinEquiv.trans (finCongr (by ring)))

/-- The standard real basis `(e_j, i·e_j)_j` of `EuclideanSpace ℂ (Fin n)`, indexed by
`Fin (2 * n)`. -/
def euclideanBasis (n : ℕ) : Module.Basis (Fin (2 * n)) ℝ (EuclideanSpace ℂ (Fin n)) :=
  ((Pi.basis fun _ : Fin n => basisOneI).reindex (sigmaFinTwoEquiv n)).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).toLinearEquiv.symm

theorem euclideanBasis_map_ofLp (n : ℕ) :
    (euclideanBasis n).map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).toLinearEquiv
      = (Pi.basis fun _ : Fin n => basisOneI).reindex (sigmaFinTwoEquiv n) :=
  Module.Basis.eq_of_apply_eq fun i => by
    rw [Module.Basis.map_apply, euclideanBasis, Module.Basis.map_apply,
      LinearEquiv.apply_symm_apply]

theorem euclideanBasis_apply (n : ℕ) (c : Fin (2 * n)) :
    euclideanBasis n c
      = WithLp.toLp 2 (Pi.single ((sigmaFinTwoEquiv n).symm c).1
          (basisOneI ((sigmaFinTwoEquiv n).symm c).2)) := by
  simp [euclideanBasis, Module.Basis.map_apply, Module.Basis.coe_reindex, Pi.basis_apply]

/-- The standard real basis of `EuclideanSpace ℂ (Fin n)` is orthonormal for the real inner
product `re ⟪·,·⟫`: distinct coordinates are orthogonal, and `1, i` are orthonormal in `ℂ`. -/
theorem orthonormal_euclideanBasis (n : ℕ) : Orthonormal ℝ (euclideanBasis n) := by
  rw [orthonormal_iff_ite]
  intro a b
  have hone : ∀ k l : Fin 2, ⟪basisOneI k, basisOneI l⟫_ℝ = if k = l then 1 else 0 := by
    intro k l
    have h := (orthonormal_iff_ite.mp orthonormalBasisOneI.orthonormal) k l
    rwa [← OrthonormalBasis.coe_toBasis, toBasis_orthonormalBasisOneI] at h
  rw [euclideanBasis_apply, euclideanBasis_apply, PiLp.inner_apply]
  rcases ha : (sigmaFinTwoEquiv n).symm a with ⟨j, k⟩
  rcases hb : (sigmaFinTwoEquiv n).symm b with ⟨j', k'⟩
  have hab : a = b ↔ j = j' ∧ k = k' := by
    rw [← (sigmaFinTwoEquiv n).symm.injective.eq_iff, ha, hb, Sigma.mk.inj_iff, heq_iff_eq]
  rw [Finset.sum_eq_single j]
  · by_cases hj : j = j'
    · subst hj
      change ⟪(Pi.single j (basisOneI k) : Fin n → ℂ) j,
        (Pi.single j (basisOneI k') : Fin n → ℂ) j⟫_ℝ = _
      rw [Pi.single_eq_same, Pi.single_eq_same, hone]
      by_cases hk : k = k'
      · subst hk
        rw [if_pos rfl, if_pos (hab.mpr ⟨rfl, rfl⟩)]
      · rw [if_neg hk, if_neg (fun h => hk (hab.mp h).2)]
    · change ⟪(Pi.single j (basisOneI k) : Fin n → ℂ) j,
        (Pi.single j' (basisOneI k') : Fin n → ℂ) j⟫_ℝ = _
      rw [Pi.single_eq_of_ne hj, inner_zero_right, if_neg (fun h => hj (hab.mp h).1)]
  · intro i _ hi
    change ⟪(Pi.single j (basisOneI k) : Fin n → ℂ) i,
      (Pi.single j' (basisOneI k') : Fin n → ℂ) i⟫_ℝ = 0
    rw [Pi.single_eq_of_ne hi, inner_zero_left]
  · simp

/-- The standard real basis of `EuclideanSpace ℂ (Fin n)`, as an orthonormal basis. -/
def euclideanOrthonormalBasis (n : ℕ) :
    OrthonormalBasis (Fin (2 * n)) ℝ (EuclideanSpace ℂ (Fin n)) :=
  (euclideanBasis n).toOrthonormalBasis (orthonormal_euclideanBasis n)

theorem euclideanOrthonormalBasis_toBasis (n : ℕ) :
    (euclideanOrthonormalBasis n).toBasis = euclideanBasis n :=
  Module.Basis.toBasis_toOrthonormalBasis _ _

/-- ★ **`ofLp : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ)` is volume preserving**: the volume of the
real inner-product structure on the left is the Haar measure of the orthonormal basis
`euclideanOrthonormalBasis n` (`OrthonormalBasis.addHaar_eq_volume`), whose image is the standard
real basis of `Fin n → ℂ`, whose Haar measure is Lebesgue measure. -/
theorem measurePreserving_ofLp (n : ℕ) :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ)) volume volume := by
  refine ⟨(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).continuous.measurable, ?_⟩
  rw [← (euclideanOrthonormalBasis n).addHaar_eq_volume, euclideanOrthonormalBasis_toBasis]
  have h := Module.Basis.map_addHaar (euclideanBasis n)
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ))
  rw [euclideanBasis_map_ofLp, addHaar_pi_basisOneI_reindex] at h
  exact h

end Complex
