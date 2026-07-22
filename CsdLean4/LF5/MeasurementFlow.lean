/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF5.VonNeumannUnitary
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive

/-!
# LF5: the von Neumann measurement flow (LF5-B)

**Category:** 3-Local (LF5 measurement-dynamics layer).

This is **LF5-B** of `specs/lf5-plan.md`: the deterministic measurement flow
`Φ_vN ≠ id` on the dilated projective ontic space, induced by the LF5-A von
Neumann coupling unitary `vnUnitary N` (the adder-permutation coupling
`eⱼ ⊗ a₀ ↦ eⱼ ⊗ aⱼ` on the system × apparatus index `Fin N × Fin N`).

## Design choice: reindex onto the `Fin m` FS infrastructure (option (a))

The Fubini–Study infrastructure (`fubiniStudyMeasure`,
`fubiniStudyMeasure_smul_invariant`, the projective `MulAction` of
`Matrix.unitaryGroup (Fin n) ℂ`) is `Fin n`-indexed. The dilated index here is
`Fin N × Fin N`. Rather than generalising the audited Cat-1 FS files to an
arbitrary fintype index (option (b), wide blast radius), this module
**reindexes** `vnUnitary N` along an equiv `e : Fin N × Fin N ≃ Fin m`
(`Matrix.reindex` preserves unitary-group membership,
`reindex_mem_unitaryGroup`) and defines the flow as the smul action of the
reindexed unitary `vnUnitaryReindexed N e` on `ℙ ℂ (EuclideanSpace ℂ (Fin m))`.

The equiv is a *parameter*, not fixed to `finProdFinEquiv : Fin N × Fin N ≃
Fin (N * N)`. **LF5-C/LF5-D consequence:** LF4's POVM volume engine
(`povm_born_eq_dilated_volume`, `povm_born_frequency_volume`) consumes an
arbitrary `e : Fin N × ι ≃ Fin (M + 1)`, so the downstream tranches can
instantiate the flow, the `blockProj` pointer regions, and the
volume/frequency theorems with one shared equiv and no `N·N = M + 1`
arithmetic casts. The plan's `ℂℙ^{N·N−1}` reading is the instantiation
`e := finProdFinEquiv`, `m := N * N`.

## Relation to the plan's `projMap` framing

`specs/lf5-plan.md` phrases the flow as `projMap (vnUnitary)` (the projective
image of a `LinearIsometryEquiv`, `WignerRigidity.lean`). We use the
`Matrix.unitaryGroup` smul action instead, because the FS-invariance theorem
`fubiniStudyMeasure_smul_invariant` is stated for it. The two framings agree
mathematically — both send `mk v` to `mk (U v)` (`smul_mk_eq_mk` resp.
`projMap_mk`) — but the agreement is **not formalised here** (no
`LinearIsometryEquiv` packaging of `vnUnitaryReindexed` is constructed; the
smul action is the form consumed downstream). `measurementFlow_mk_single` is
the computed basis-ray instance (the flow permutes computational-basis rays
by the adder `vnPerm N`).

## Main results

- `measurementFlow` — the flow `p ↦ vnUnitaryReindexed N e • p` on
  `ℙ ℂ (EuclideanSpace ℂ (Fin m))`, the projective von Neumann coupling.
- `measurementFlow_measurePreserving` — FS-invariance: the Liouville
  (`hΦ_pres`) content making the flow a physically admissible ontic dynamics.
- `measurementFlow_ne_id` — for `1 < N` the flow is genuinely not the
  identity: the basis ray at `e (1, 0)` (system `1`, apparatus ground) moves
  to the distinct basis ray at `e (1, 1)`.

## Honest scope (D1 increment)

This module exercises a **genuine `Φ ≠ id` measurement dynamics** on the
dilated ontic space — the D1 increment, under the de-isolation reading of
`specs/carve-out-plan.md` §6 (the apparatus de-isolates; the pointer-outcome
regions are the context-fixed apparatus basis blocks, not carved). It does
**not** re-derive the Born number: downstream (LF5-D) the Born weight still
comes from the existing FS-volume = Born engine. Single-system projective
tier; entangled measurements and the A5 sector posit are deferred
(`specs/lf5-plan.md` §0).

Reference: `specs/lf5-plan.md` (LF5-B).
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF5

variable {N : ℕ} [NeZero N] {m : ℕ}

/-! ## Reindexing the coupling unitary onto `Fin m` -/

/-- Reindexing a square matrix along an `Equiv` preserves unitary-group
membership: `(reindex e e A)ᴴ (reindex e e A) = reindex e e (Aᴴ A) = 1` via
`Matrix.conjTranspose_submatrix`, `Matrix.submatrix_mul_equiv`, and
`Matrix.submatrix_one_equiv`. Generic helper (Mathlib upstream candidate —
`Matrix.UnitaryGroup` currently has no reindex API). -/
lemma reindex_mem_unitaryGroup {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  show (Matrix.reindex e e A)ᴴ * Matrix.reindex e e A = 1
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    show Aᴴ * A = 1 from hA, Matrix.submatrix_one_equiv]

/-- The **reindexed von Neumann coupling unitary**: `vnUnitary N` transported
along `e : Fin N × Fin N ≃ Fin m` onto the `Fin m`-indexed space where the
Fubini–Study infrastructure lives, packaged as a `Matrix.unitaryGroup` element
(this is what the projective smul action consumes). -/
noncomputable def vnUnitaryReindexed (N : ℕ) [NeZero N] {m : ℕ}
    (e : Fin N × Fin N ≃ Fin m) : Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Matrix.reindex e e (vnUnitary N),
   reindex_mem_unitaryGroup e (vnUnitary_mem_unitaryGroup (N := N))⟩

lemma vnUnitaryReindexed_val (e : Fin N × Fin N ≃ Fin m) :
    (vnUnitaryReindexed N e).val = Matrix.reindex e e (vnUnitary N) := rfl

/-- **Basis action of the reindexed coupling.** The reindexed unitary realises
the adder bijection `vnPerm N` on the reindexed computational basis:
`e_{e a} ↦ e_{e (vnPerm N a)}`. Reduces to LF5-A's `vnUnitary_mulVec_single`
through `Matrix.submatrix_mulVec_equiv`. -/
lemma vnUnitaryReindexed_mulVec_single (e : Fin N × Fin N ≃ Fin m)
    (a : Fin N × Fin N) :
    (vnUnitaryReindexed N e).val *ᵥ Pi.single (e a) (1 : ℂ)
      = Pi.single (e (vnPerm N a)) (1 : ℂ) := by
  rw [vnUnitaryReindexed_val, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Equiv.symm_symm]
  have h1 : Pi.single (e a) (1 : ℂ) ∘ ⇑e = Pi.single a (1 : ℂ) := by
    funext k
    simp only [Function.comp_apply, Pi.single_apply]
    exact if_congr (EmbeddingLike.apply_eq_iff_eq e) rfl rfl
  rw [h1, vnUnitary_mulVec_single]
  funext x
  simp only [Function.comp_apply, Pi.single_apply]
  exact if_congr (Equiv.symm_apply_eq e) rfl rfl

/-- Euclidean (`PiLp 2`) form of the basis action: `toEuclideanLin` of the
reindexed coupling sends the basis vector at `e a` to the one at
`e (vnPerm N a)`. -/
lemma vnUnitaryReindexed_toEuclideanLin_single (e : Fin N × Fin N ≃ Fin m)
    (a : Fin N × Fin N) :
    Matrix.toEuclideanLin (vnUnitaryReindexed N e).val
        (EuclideanSpace.single (e a) (1 : ℂ))
      = EuclideanSpace.single (e (vnPerm N a)) (1 : ℂ) := by
  show WithLp.toLp 2 ((vnUnitaryReindexed N e).val *ᵥ Pi.single (e a) (1 : ℂ))
      = EuclideanSpace.single (e (vnPerm N a)) (1 : ℂ)
  rw [vnUnitaryReindexed_mulVec_single]
  rfl

/-! ## Distinct basis rays -/

/-- A computational-basis vector is nonzero. -/
lemma single_one_ne_zero {n : ℕ} (i : Fin n) :
    (EuclideanSpace.single i (1 : ℂ)) ≠ 0 := fun h =>
  one_ne_zero ((PiLp.single_eq_zero_iff 2 i).mp h)

/-- Distinct computational-basis vectors are non-collinear, so they project to
distinct rays: any scalar relation `c • e_k = e_i` evaluated at coordinate `i`
gives `0 = 1`. -/
lemma mk_single_ne {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ)) (single_one_ne_zero i)
      ≠ Projectivization.mk ℂ (EuclideanSpace.single k (1 : ℂ))
          (single_one_ne_zero k) := by
  rw [Ne, Projectivization.mk_eq_mk_iff']
  rintro ⟨c, hc⟩
  have h := congrFun (congrArg WithLp.ofLp hc) i
  simp only [WithLp.ofLp_smul, PiLp.ofLp_single, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same, Pi.single_eq_of_ne hik, mul_zero] at h
  exact zero_ne_one h

/-! ## The measurement flow -/

/-- **The von Neumann measurement flow `Φ_vN`** (LF5-B): the deterministic
self-map of the dilated projective ontic space `ℙ ℂ (EuclideanSpace ℂ (Fin m))`
given by the smul action of the reindexed coupling unitary. At
`e := finProdFinEquiv`, `m := N * N` this is the plan's flow on `ℂℙ^{N·N−1}`;
it agrees with the `projMap` framing on every ray (both send `mk v` to
`mk (U v)`, see the module docstring). -/
noncomputable def measurementFlow (N : ℕ) [NeZero N] {m : ℕ}
    (e : Fin N × Fin N ≃ Fin m) :
    ℙ ℂ (EuclideanSpace ℂ (Fin m)) → ℙ ℂ (EuclideanSpace ℂ (Fin m)) :=
  fun p => vnUnitaryReindexed N e • p

lemma measurementFlow_apply (e : Fin N × Fin N ≃ Fin m)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin m))) :
    measurementFlow N e p = vnUnitaryReindexed N e • p := rfl

/-- **Basis-ray action of the flow.** The measurement flow permutes the
computational-basis rays by the adder bijection: the ray at index `e a` moves
to the ray at `e (vnPerm N a)`. At the ground apparatus `a = (j, 0)` this is
the projective copy `[e_j ⊗ a₀] ↦ [e_j ⊗ a_j]` (LF5-C input). -/
lemma measurementFlow_mk_single (e : Fin N × Fin N ≃ Fin m) (a : Fin N × Fin N) :
    measurementFlow N e
        (Projectivization.mk ℂ (EuclideanSpace.single (e a) (1 : ℂ))
          (single_one_ne_zero _))
      = Projectivization.mk ℂ (EuclideanSpace.single (e (vnPerm N a)) (1 : ℂ))
          (single_one_ne_zero _) := by
  haveI : NeZero m := ⟨fun h => Fin.elim0 (h ▸ e a)⟩
  refine (smul_mk_eq_mk (vnUnitaryReindexed N e) _ (single_one_ne_zero _)).trans ?_
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ (single_one_ne_zero _)).mpr
    ⟨1, by rw [one_smul]; exact (vnUnitaryReindexed_toEuclideanLin_single e a).symm⟩

@[measurability, fun_prop]
lemma measurementFlow_measurable (e : Fin N × Fin N ≃ Fin m) :
    Measurable (measurementFlow N e) :=
  (continuous_const_smul (vnUnitaryReindexed N e)).measurable

/-- **FS-invariance of the measurement flow (the Liouville / `hΦ_pres`
content).** The von Neumann measurement flow preserves the Fubini–Study
typicality measure on the dilated projective ontic space, so it is a
physically admissible deterministic ontic dynamics in the LF1 sense.
Composes `fubiniStudyMeasure_smul_invariant` with measurability of the
constant smul. -/
theorem measurementFlow_measurePreserving (e : Fin N × Fin N ≃ Fin m)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin m))) :
    MeasurePreserving (measurementFlow N e)
      (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  ⟨measurementFlow_measurable e,
   fubiniStudyMeasure_smul_invariant (vnUnitaryReindexed N e) p₀⟩

/-- **The measurement flow is genuinely not the identity** (for `1 < N`; at
`N = 1` the adder is trivially the identity). Witness: the basis ray at
`e (1, 0)` (system `1`, apparatus ground) moves to the distinct basis ray at
`e (1, 1)` — the coupling correlates the apparatus with the system. This is
the `Φ_vN ≠ id` half of the D1 increment. -/
theorem measurementFlow_ne_id (hN : 1 < N) (e : Fin N × Fin N ≃ Fin m) :
    measurementFlow N e ≠ id := by
  intro hid
  have hj0 : (⟨1, hN⟩ : Fin N) ≠ 0 := by
    simp [Fin.ext_iff]
  have hne : e (⟨1, hN⟩, 0) ≠ e (vnPerm N (⟨1, hN⟩, 0)) := by
    rw [vnPerm_ground]
    intro h
    exact hj0 (Prod.ext_iff.mp (e.injective h)).2.symm
  have hmove := measurementFlow_mk_single (N := N) e (⟨1, hN⟩, 0)
  rw [hid, id_eq] at hmove
  exact mk_single_ne hne hmove

end LF5
end CSD
