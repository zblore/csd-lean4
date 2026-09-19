/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import CsdLean4.Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The quotient topology on projective space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidates).

`ℙ K V` is the quotient of the nonzero vectors `{v : V // v ≠ 0}` by the action of `Kˣ`.
When `V` carries a topology we give `ℙ K V` the quotient topology, and we show that the
quotient map `Projectivization.mk'` is an open quotient map as soon as scalar multiplication
by units of `K` is continuous on `V`.

## Main results

* `Projectivization.instTopologicalSpace`: the quotient topology on `ℙ K V`.
* `Projectivization.isQuotientMap_mk'`, `Projectivization.continuous_mk'`:
  `mk' K : {v : V // v ≠ 0} → ℙ K V` is a quotient map, in particular continuous.
* `Projectivization.isOpenQuotientMap_mk'`: `mk' K` is an open quotient map when `Kˣ` acts
  continuously on `V`.
* `Projectivization.continuous_iff`: a map out of `ℙ K V` is continuous iff its composite with
  `mk' K` is.

Beyond the upstream text, and staying here:

* `Projectivization.continuous_lift`: a scale-invariant continuous function on the nonzero
  subtype descends continuously, the topological companion of `lift_measurable`.
* `Projectivization.mapOfInjective_continuous`, `Projectivization.mapEquiv` and its lemmas:
  continuity of the map induced by an injective linear map, and the `LinearEquiv` action.
* `Projectivization.instT2Space`, `Projectivization.instCompactSpace`: `ℙ K V` is compact
  Hausdorff for `[RCLike K]` and finite-dimensional normed `V`.
* `Projectivization.connectedSpace_of_isConnected_nonzero`: connectedness from connectedness of
  the nonzero vectors.

## Provenance

Staged as upstream Mathlib material. **The first section below is the Mathlib pull-request text
verbatim** (`Mathlib/LinearAlgebra/Projectivization/Topology.lean`, six declarations), so that
this repository and the pull request are the same code and any drift between them is visible.
Two divergences, both forced by this repository's Mathlib pin and neither touching a statement:
the module-system header and this docstring, which the lints here require; and `isOpenMap_mk'`
spelling the coinducing step `isQuotientMap_mk'.isCoinducing.isOpen_preimage`, since
`IsQuotientMap.isOpen_preimage` postdates the pin. The remaining sections are this repository's
own and are the second pull request's material (Hausdorffness, compactness) or stay here.

The `Kˣ`-action on `{v : V // v ≠ 0}` is Mathlib's, through `Units.nonZeroSubMul`; the
continuity instance it needs is staged in `CsdLean4/Mathlib/Topology/Algebra/MulAction.lean`.
Until 2026-09-19 this file carried its own `scaleNonzero` / `scaleNonzeroHomeo` reimplementation
of that action and its own saturation lemma, 461 lines against the 82 of the pull request.

## Tags

projectivization, projective space, quotient topology
-/

@[expose] public section

open Set Function Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*}

section AlgebraicTopology

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-! ### The upstream text

Everything between here and the end of this section is the Mathlib pull request verbatim.
It is wrapped in a section of its own so that its `variable` lines stop where the pull
request file stops, and do not reach the material this repository keeps below. -/

section

/-- Two nonzero vectors have the same image in `ℙ K V` iff one is a unit multiple of the other,
for the action of `Kˣ` on `{v : V // v ≠ 0}`. -/
theorem mk'_eq_mk'_iff (v w : {v : V // v ≠ 0}) :
    mk' K v = mk' K w ↔ ∃ a : Kˣ, a • w = v := by
  rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff]
  simp only [Subtype.ext_iff, Units.smul_coe]

/-- The saturation of a set of nonzero vectors under `mk'` is the union of its translates by the
units of `K`. -/
theorem preimage_image_mk' (U : Set {v : V // v ≠ 0}) :
    mk' K ⁻¹' (mk' K '' U) = ⋃ a : Kˣ, (a • ·) '' U := by
  ext v
  simp only [mem_preimage, mem_image, mk'_eq_mk'_iff, mem_iUnion]
  exact ⟨fun ⟨w, hw, a, h⟩ ↦ ⟨a⁻¹, w, hw, by rw [← h, inv_smul_smul]⟩,
    fun ⟨a, w, hw, h⟩ ↦ ⟨w, hw, a⁻¹, by rw [← h, inv_smul_smul]⟩⟩

variable [TopologicalSpace V]

/-- The quotient topology on `ℙ K V`, coinduced by `Projectivization.mk'`. -/
instance instTopologicalSpace : TopologicalSpace (ℙ K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))

theorem isQuotientMap_mk' : IsQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  isQuotientMap_quotient_mk'

@[continuity, fun_prop]
theorem continuous_mk' : Continuous (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_quotient_mk'

variable {α : Type*} [TopologicalSpace α]

theorem continuous_iff {f : ℙ K V → α} : Continuous f ↔ Continuous (f ∘ mk' K) :=
  isQuotientMap_mk'.continuous_iff

variable [ContinuousConstSMul Kˣ V]

theorem isOpenMap_mk' : IsOpenMap (mk' K : {v : V // v ≠ 0} → ℙ K V) := fun U hU ↦ by
  rw [← isQuotientMap_mk'.isCoinducing.isOpen_preimage, preimage_image_mk']
  exact isOpen_iUnion fun a ↦ isOpenMap_smul a U hU

theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  ⟨Quotient.mk''_surjective, continuous_mk', isOpenMap_mk'⟩

end

/-! ### Continuity descent

Companion to the `lift_measurable` / `measurable_iff_measurable_comp_mk'` pair in
`MeasureSpace.lean`: a scale-invariant continuous function on the nonzero subtype descends to a
continuous function on `ℙ K V`. -/

section Descent

variable [TopologicalSpace V] {α : Type*} [TopologicalSpace α]

/-- A scale-invariant continuous function on the nonzero subtype descends to a continuous
function on `ℙ K V`. Topological companion to `lift_measurable` in `MeasureSpace.lean`. -/
theorem continuous_lift (f : {v : V // v ≠ 0} → α)
    (hf : ∀ (a b : {v : V // v ≠ 0}) (t : K), a = t • (b : V) → f a = f b)
    (hf_cont : Continuous f) :
    Continuous (Projectivization.lift f hf) := by
  rw [continuous_iff]
  exact hf_cont

end Descent

/-! ### Continuity of `Projectivization.map`

A continuous injective linear map between modules descends to a
continuous map between projectivizations. Builds on `continuous_iff`
above via the standard `mk'` quotient-map characterisation of
continuity. -/

section MapContinuity

variable [TopologicalSpace V]
variable {W : Type*} [AddCommGroup W] [Module K W] [TopologicalSpace W]

/-- A continuous injective linear map descends to a continuous map on
projectivizations. -/
theorem mapOfInjective_continuous
    (f : V →ₗ[K] W) (hf : Function.Injective f) (hf_cont : Continuous f) :
    Continuous (Projectivization.map f hf) := by
  rw [continuous_iff]
  -- The composition `(map f hf) ∘ mk' K` equals `mk' K ∘ f_sub` where
  -- `f_sub` is the corestriction of `f` to the nonzero subtype (with
  -- output non-zero via `hf`). Both factors are continuous: `mk'` by
  -- `continuous_mk'`, and `f_sub` via `subtype_mk` applied to `f`'s
  -- continuity composed with subtype projection.
  exact continuous_mk'.comp
    ((hf_cont.comp continuous_subtype_val).subtype_mk _)

end MapContinuity

/-! ### `LinearEquiv` action on projectivization

A linear self-equivalence `e : V ≃ₗ[K] V` induces a self-map
`mapEquiv e : ℙ K V → ℙ K V` via `Projectivization.map` and the
canonical injectivity of an equivalence. The construction respects
the group structure of `V ≃ₗ[K] V` via `Projectivization.map_id`
and `Projectivization.map_comp`. -/

section LinearEquivAction

/-- A linear self-equivalence induces a self-map of the projectivization. -/
def mapEquiv (e : V ≃ₗ[K] V) : ℙ K V → ℙ K V :=
  Projectivization.map e.toLinearMap e.injective

@[simp]
lemma mapEquiv_refl : mapEquiv (LinearEquiv.refl K V) = id :=
  Projectivization.map_id

/-- The induced map of the identity equivalence is the identity.
Syntactic alias for `mapEquiv_refl` under the `Group` notation `1`
for `LinearEquiv.refl` (definitionally equal via
`LinearEquiv.one_eq_refl`). -/
@[simp]
lemma mapEquiv_one : mapEquiv (1 : V ≃ₗ[K] V) = id :=
  mapEquiv_refl

/-- The induced map of a product of linear self-equivalences equals
the composition of the induced maps. Discharged via
`Projectivization.map_comp` applied to the toLinearMap composition:
`(e₁ * e₂).toLinearMap = e₁.toLinearMap.comp e₂.toLinearMap` (= `*`
in the linear-endomorphism ring; both equal by `rfl` via
`LinearEquiv.coe_toLinearMap_mul` + `LinearMap.mul_eq_comp`). -/
lemma mapEquiv_mul (e₁ e₂ : V ≃ₗ[K] V) :
    mapEquiv (e₁ * e₂) = mapEquiv e₁ ∘ mapEquiv e₂ :=
  Projectivization.map_comp e₂.toLinearMap e₂.injective
    e₁.toLinearMap e₁.injective

/-- The action of `V ≃ₗ[K] V` on `ℙ K V` is Mathlib's `Projectivization.instMulAction`
(`Mathlib/LinearAlgebra/Projectivization/Action.lean`: any group acting `K`-linearly on `V` acts on
`ℙ K V`), specialised to `G := V ≃ₗ[K] V` through `LinearEquiv.applyDistribMulAction`; on
representatives it is `mapEquiv`. Until 2026-09-16 this file declared its own instance under the
same auto-generated name, which made the two files impossible to import together. -/
@[simp]
lemma mapEquiv_smul_eq (e : V ≃ₗ[K] V) (p : ℙ K V) : e • p = mapEquiv e p := rfl

variable [TopologicalSpace V]

/-- The `mapEquiv` of a continuous linear equivalence is continuous. -/
theorem mapEquiv_continuous (e : V ≃ₗ[K] V) (he : Continuous (e : V → V)) :
    Continuous (mapEquiv e) :=
  mapOfInjective_continuous e.toLinearMap e.injective he

end LinearEquivAction

end AlgebraicTopology

/-! ### Hausdorffness and compactness under normed finite-dim hypotheses

Under `[RCLike K]` (so `K ∈ {ℝ, ℂ}` with the usual analytic structure)
and `[NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]`,
the projectivization `ℙ K V` is a compact Hausdorff space.

The hypothesis pattern can be relaxed to `[NontriviallyNormedField K]`
+ `[LocallyCompactSpace K]` + `[NormedAlgebra ℝ K]` (sufficient for the
unit-sphere normalisation argument), but the `RCLike` form covers the
case of interest (`K = ℂ`) with strictly less typeclass friction. -/

section NormedFiniteDim

-- Note: the outer `[DivisionRing K] [AddCommGroup V] [Module K V]`
-- instances of `section AlgebraicTopology` are deliberately *not* in
-- scope here, to avoid an `AddCommGroup V` diamond with
-- `[NormedAddCommGroup V]`'s own derivation path. `[RCLike K]` +
-- `[NormedAddCommGroup V]` + `[NormedSpace K V]` re-introduce the
-- equivalents through a single path, and Mathlib lemmas in this section
-- (`mem_sphere_zero_iff_norm`, `norm_smul`, `RCLike.norm_ofReal`,
-- `mk_eq_mk_iff'`) then unify cleanly.
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- The K-collinearity relation on the nonzero subtype is closed.

Two nonzero vectors `v, w` represent the same projective point iff their
pair is linearly dependent (`mk_eq_mk_iff'` + `LinearIndependent.pair_iff'`),
and the set of linearly dependent pairs is the complement of an open set
via `isOpen_setOfPred_linearIndependent`. -/
lemma isClosed_collinearity_relation :
    IsClosed { p : { v : V // v ≠ 0 } × { v : V // v ≠ 0 } |
                mk' K p.1 = mk' K p.2 } := by
  -- Map `(v_sub, w_sub) ↦ ![w, v] : Fin 2 → V`. The collinearity set is
  -- the preimage of `¬ LinearIndependent K`-pairs, which is the
  -- complement of `isOpen_setOfPred_linearIndependent`.
  let f : { v : V // v ≠ 0 } × { v : V // v ≠ 0 } → (Fin 2 → V) :=
    fun p => ![(p.2 : V), (p.1 : V)]
  have hf : Continuous f := by
    refine continuous_pi (fun i => ?_)
    fin_cases i
    · exact continuous_subtype_val.comp continuous_snd
    · exact continuous_subtype_val.comp continuous_fst
  have h_eq : { p : { v : V // v ≠ 0 } × { v : V // v ≠ 0 } |
                  mk' K p.1 = mk' K p.2 }
            = f ⁻¹' { g : Fin 2 → V | LinearIndependent K g }ᶜ := by
    ext ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, f]
    rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff' K v w hv hw,
        LinearIndependent.pair_iff' hw]
    push Not
    rfl
  rw [h_eq]
  exact isOpen_setOfPred_linearIndependent.isClosed_compl.preimage hf

/-- `ℙ K V` is Hausdorff under finite-dimensional normed hypotheses on
`V`. Routes through the open-quotient-map criterion
`t2Space_iff_of_isOpenQuotientMap` plus `isClosed_collinearity_relation`. -/
instance instT2Space : T2Space (ℙ K V) :=
  (t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_mk').mpr
    isClosed_collinearity_relation

/-- `ℙ K V` is compact under finite-dimensional normed hypotheses on
`V`. The unit sphere `Metric.sphere (0 : V) 1` is compact as a subtype
(Heine-Borel in finite-dim normed; `FiniteDimensional.proper_rclike` +
`Metric.sphere.compactSpace`), and the corestriction of `mk K` to the
sphere is a continuous surjection from sphere to `ℙ K V` (every
projective point has a unit-norm representative obtained by
normalising `p.rep`). -/
instance instCompactSpace : CompactSpace (ℙ K V) := by
  have : ProperSpace V := FiniteDimensional.proper_rclike K V
  -- Define the corestricted projection sphere → ℙ K V.
  let g : Metric.sphere (0 : V) 1 → ℙ K V :=
    fun v => mk K (v : V) (by
      intro hv
      have h1 : ‖(v : V)‖ = 1 := by
        have := v.2; rwa [Metric.mem_sphere, dist_zero_right] at this
      rw [hv, norm_zero] at h1
      exact one_ne_zero h1.symm)
  have hg_cont : Continuous g :=
    continuous_quotient_mk'.comp (continuous_induced_rng.mpr continuous_subtype_val)
  have hg_surj : Function.Surjective g := by
    intro p
    have hrep_ne : p.rep ≠ 0 := p.rep_nonzero
    have hrep_norm_pos : 0 < ‖p.rep‖ := norm_pos_iff.mpr hrep_ne
    have h_norm_eq : ‖((‖p.rep‖⁻¹ : ℝ) : K) • p.rep‖ = 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hrep_norm_pos)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hrep_ne)
    have h_sphere : ((‖p.rep‖⁻¹ : ℝ) : K) • p.rep ∈ Metric.sphere (0 : V) 1 :=
      mem_sphere_zero_iff_norm.mpr h_norm_eq
    refine ⟨⟨((‖p.rep‖⁻¹ : ℝ) : K) • p.rep, h_sphere⟩, ?_⟩
    -- `g ⟨smul_vec, h_sphere⟩ = p` via `mk_eq_mk_iff'` and `mk_rep`.
    show mk K (((‖p.rep‖⁻¹ : ℝ) : K) • p.rep) _ = p
    conv_rhs => rw [← p.mk_rep]
    rw [mk_eq_mk_iff' K _ _ _ hrep_ne]
    exact ⟨((‖p.rep‖⁻¹ : ℝ) : K), rfl⟩
  exact ⟨hg_surj.range_eq ▸ isCompact_range hg_cont⟩

/-- In finite-dim normed setting over `RCLike`, every linear self-equivalence
of `V` is continuous (Banach), so its induced projectivization map is
continuous for free. -/
theorem mapEquiv_continuous_of_finiteDim (e : V ≃ₗ[K] V) :
    Continuous (mapEquiv e) :=
  mapEquiv_continuous e (e : V →ₗ[K] V).continuous_of_finiteDimensional

/-- Each individual `(V ≃ₗ[K] V)`-action on `ℙ K V` is continuous in
the finite-dim normed setting. This is `ContinuousConstSMul`, which
captures continuity in the action argument for every fixed group
element. Joint continuity in both arguments (`ContinuousSMul`) is a
strictly stronger statement requiring a topology on `V ≃ₗ[K] V`
itself; deferred. -/
instance instContinuousConstSMul :
    ContinuousConstSMul (V ≃ₗ[K] V) (ℙ K V) where
  continuous_const_smul e := mapEquiv_continuous_of_finiteDim e

end NormedFiniteDim

/-! ### Connectedness

The projectivization of a module whose nonzero vectors form a connected set is itself
connected: it is the continuous image of `{v // v ≠ 0}` under `mk'`. Downstream, for an
`RCLike` field and real rank `> 1`, the nonzero set is connected because the complement of a
point in a real normed space of rank `> 1` is connected
(`isConnected_compl_singleton_of_one_lt_rank`). -/

section Connectedness

variable [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]

omit [TopologicalSpace V] in
/-- The canonical surjection `mk'` is surjective onto the projectivization. -/
theorem mk'_surjective : Function.Surjective (mk' K (V := V)) := fun p =>
  ⟨⟨p.rep, p.rep_nonzero⟩, by rw [mk'_eq_mk]; exact p.mk_rep⟩

/-- If the nonzero vectors form a connected set, the projectivization is a connected
space. -/
theorem connectedSpace_of_isConnected_nonzero
    (h : IsConnected {v : V | v ≠ 0}) : ConnectedSpace (ℙ K V) := by
  have h' : ConnectedSpace {v : V // v ≠ 0} := Subtype.connectedSpace h
  exact mk'_surjective.connectedSpace continuous_mk'

end Connectedness

end Projectivization
