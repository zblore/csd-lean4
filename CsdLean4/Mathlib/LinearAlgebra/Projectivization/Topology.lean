import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Topology on projectivization

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidates).

The quotient topology on `Projectivization K V` is inherited from
`instTopologicalSpaceQuotient`. Because `Projectivization K V` is a `def`
(not `@[reducible]`) over `Quotient (projectivizationSetoid K V)`,
typeclass synthesis does not unfold it; this file installs the explicit
`TopologicalSpace (ℙ K V)` instance and develops its consequences:

- `Projectivization.continuous_mk'`: the canonical surjection
  `{v : V // v ≠ 0} → ℙ K V` is continuous.
- `Projectivization.isOpenMap_mk'`: the canonical surjection is an open
  map. Proved directly using
  `mk' ⁻¹' (mk' '' U) = ⋃ a : Kˣ, scaleNonzero a '' U`.
- `Projectivization.isQuotientMap_mk'` and
  `Projectivization.isOpenQuotientMap_mk'`: combine openness + continuity
  + surjectivity.

For `[RCLike K]` and finite-dimensional normed `V`:

- `Projectivization.instT2Space`: Hausdorffness, via the open-quotient-map
  criterion `t2Space_iff_of_isOpenQuotientMap` reduced to closedness of
  the K-collinearity relation, which in turn follows from
  `isOpen_setOfPred_linearIndependent` and `LinearIndependent.pair_iff'`.
- `Projectivization.instCompactSpace`: compactness, via continuous
  surjection from `Metric.sphere (0 : V) 1` (compact by Heine-Borel in
  finite-dim normed).

## Provenance

Staged as upstream Mathlib material. All declarations live under
`namespace Projectivization` with no `CsdLean4`-namespace prefix; the file
is intended to land in
`Mathlib/LinearAlgebra/Projectivization/Topology.lean` once usage
stabilises. Naming, docstring format, and import discipline track Mathlib
idiom.

## Tags

projectivization, projective space, quotient topology
-/

open Set Function Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*}

section AlgebraicTopology

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The quotient topology on `Projectivization K V`.

`Projectivization` is a `def` over `Quotient (projectivizationSetoid K V)`,
so the generic `instTopologicalSpaceQuotient` does not fire by typeclass
synthesis alone. We provide the explicit forwarding instance. -/
instance instTopologicalSpace [TopologicalSpace V] :
    TopologicalSpace (ℙ K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))

section TopologicalDivisionRing

variable [TopologicalSpace V]

/-- The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is continuous. -/
@[continuity]
theorem continuous_mk' : Continuous (mk' K : { v : V // v ≠ 0 } → ℙ K V) :=
  continuous_quotient_mk'

end TopologicalDivisionRing

/-- Scaling by a unit `a : Kˣ` corestricts to a self-map of the nonzero
subtype `{v : V // v ≠ 0}`. -/
def scaleNonzero (a : Kˣ) (v : { v : V // v ≠ 0 }) : { v : V // v ≠ 0 } :=
  ⟨(a : K) • (v : V), smul_ne_zero a.ne_zero v.2⟩

@[simp]
lemma scaleNonzero_coe (a : Kˣ) (v : { v : V // v ≠ 0 }) :
    (scaleNonzero a v : V) = (a : K) • (v : V) := rfl

lemma scaleNonzero_mul (a b : Kˣ) (v : { v : V // v ≠ 0 }) :
    scaleNonzero a (scaleNonzero b v) = scaleNonzero (a * b) v := by
  apply Subtype.ext
  simp [scaleNonzero, mul_smul, Units.val_mul]

@[simp]
lemma scaleNonzero_one (v : { v : V // v ≠ 0 }) :
    scaleNonzero (1 : Kˣ) v = v := by
  apply Subtype.ext
  simp [scaleNonzero]

section TopologicalAction

variable [TopologicalSpace V] [ContinuousConstSMul K V]

/-- Scaling by a unit, viewed as a self-map of `{v : V // v ≠ 0}`, is
continuous: it is the corestriction of the continuous map
`(a : K) • · : V → V` along the subtype inclusion. -/
lemma continuous_scaleNonzero (a : Kˣ) :
    Continuous (scaleNonzero a : { v : V // v ≠ 0 } → { v : V // v ≠ 0 }) :=
  continuous_induced_rng.mpr <|
    (continuous_const_smul (a : K)).comp continuous_subtype_val

/-- Scaling by a unit is a homeomorphism of the nonzero subtype, with
inverse given by scaling by the inverse unit. -/
def scaleNonzeroHomeo (a : Kˣ) : { v : V // v ≠ 0 } ≃ₜ { v : V // v ≠ 0 } where
  toFun := scaleNonzero a
  invFun := scaleNonzero a⁻¹
  left_inv v := by
    rw [scaleNonzero_mul, inv_mul_cancel, scaleNonzero_one]
  right_inv v := by
    rw [scaleNonzero_mul, mul_inv_cancel, scaleNonzero_one]
  continuous_toFun := continuous_scaleNonzero a
  continuous_invFun := continuous_scaleNonzero a⁻¹

end TopologicalAction

/-- **Saturation lemma**: pulling the image of a set `U ⊆ {v : V // v ≠ 0}`
back through `mk' K` recovers the orbit of `U` under the `Kˣ` scaling
action on the nonzero subtype.

This is the projectivization analogue of
`MulAction.quotient_preimage_image_eq_union_mul`. The projectivization
setoid (defined as `(MulAction.orbitRel Kˣ V).comap (↑)`) gives the same
orbit relation on the nonzero subtype as the unit-action; this lemma
makes that explicit at the set level. -/
lemma mk'_preimage_mk'_image (U : Set { v : V // v ≠ 0 }) :
    (mk' K) ⁻¹' ((mk' K) '' U) = ⋃ a : Kˣ, scaleNonzero a '' U := by
  ext w
  constructor
  · rintro ⟨v, hv, hvw⟩
    rw [mem_iUnion]
    rw [mk'_eq_mk, mk'_eq_mk] at hvw
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff K _ _ v.2 w.2).mp hvw
    -- `ha : (a : K) • (w : V) = (v : V)` via Units.smul_def
    refine ⟨a⁻¹, v, hv, ?_⟩
    apply Subtype.ext
    simp only [scaleNonzero_coe, Units.val_inv_eq_inv_val]
    -- Goal: ((a : Kˣ) : K)⁻¹ • (v : V) = (w : V)
    have hsmul : ((a : Kˣ) : K) • (w : V) = (v : V) := ha
    rw [← hsmul, ← mul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
  · intro hw
    rw [mem_iUnion] at hw
    obtain ⟨a, v, hv, hvw⟩ := hw
    refine ⟨v, hv, ?_⟩
    rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff]
    refine ⟨a⁻¹, ?_⟩
    -- Goal: ((a⁻¹ : Kˣ) : K) • (w : V) = (v : V)
    -- have `hvw : scaleNonzero a v = w` ⟹ `(w : V) = (a : K) • (v : V)`
    have hcoe : (w : V) = ((a : Kˣ) : K) • (v : V) := by
      rw [← hvw, scaleNonzero_coe]
    show ((a⁻¹ : Kˣ) : K) • (w : V) = (v : V)
    rw [hcoe, ← mul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ a.ne_zero, one_smul]

section TopologicalAction

variable [TopologicalSpace V] [ContinuousConstSMul K V]

/-- The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is an open map. -/
theorem isOpenMap_mk' : IsOpenMap (mk' K : { v : V // v ≠ 0 } → ℙ K V) := by
  intro U hU
  -- `mk'(U)` is open in `ℙ K V` iff `mk' ⁻¹' (mk' '' U)` is open in
  -- `{v : V // v ≠ 0}`, because the quotient topology is coinduced by `mk'`.
  change IsOpen (mk' K ⁻¹' (mk' K '' U))
  rw [mk'_preimage_mk'_image]
  exact isOpen_iUnion fun a => (scaleNonzeroHomeo a).isOpenMap _ hU

/-- The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is a quotient map.

Combines openness, continuity, and surjectivity via `IsOpenMap.isQuotientMap`. -/
theorem isQuotientMap_mk' :
    IsQuotientMap (mk' K : { v : V // v ≠ 0 } → ℙ K V) :=
  isOpenMap_mk'.isQuotientMap continuous_quotient_mk' Quot.mk_surjective

/-- The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is an open
quotient map. -/
theorem isOpenQuotientMap_mk' :
    IsOpenQuotientMap (mk' K : { v : V // v ≠ 0 } → ℙ K V) :=
  ⟨Quot.mk_surjective, continuous_quotient_mk', isOpenMap_mk'⟩

/-! ### Continuity descent

Companions to the `lift_measurable` / `measurable_iff_measurable_comp_mk'`
pair in `MeasureSpace.lean`: a function out of `ℙ K V` is continuous iff
its precomposition with `mk'` is, and a scale-invariant continuous
function on the nonzero subtype descends to a continuous function on
`ℙ K V`. -/

/-- A function out of `ℙ K V` is continuous iff its precomposition with
`mk'` is continuous. Topological companion to
`measurable_iff_measurable_comp_mk'` in `MeasureSpace.lean`. -/
theorem continuous_iff_continuous_comp_mk' {α : Type*} [TopologicalSpace α]
    (g : ℙ K V → α) :
    Continuous g ↔ Continuous (g ∘ (mk' K : _ → ℙ K V)) :=
  isQuotientMap_mk'.continuous_iff

/-- A scale-invariant continuous function on the nonzero subtype
descends to a continuous function on `ℙ K V`. Topological companion to
`lift_measurable` in `MeasureSpace.lean`. -/
theorem continuous_lift {α : Type*} [TopologicalSpace α]
    (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (hf_cont : Continuous f) :
    Continuous (Projectivization.lift f hf) := by
  rw [continuous_iff_continuous_comp_mk']
  exact hf_cont

end TopologicalAction

/-! ### Continuity of `Projectivization.map`

A continuous injective linear map between modules descends to a
continuous map between projectivizations. Builds on `continuous_lift`
above via the standard `mk'` quotient-map characterisation of
continuity. -/

section MapContinuity

variable [TopologicalSpace V] [ContinuousConstSMul K V]
variable {W : Type*} [AddCommGroup W] [Module K W] [TopologicalSpace W]

/-- A continuous injective linear map descends to a continuous map on
projectivizations. -/
theorem mapOfInjective_continuous
    (f : V →ₗ[K] W) (hf : Function.Injective f) (hf_cont : Continuous f) :
    Continuous (Projectivization.map f hf) := by
  rw [continuous_iff_continuous_comp_mk']
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

/-- `V ≃ₗ[K] V` acts on `Projectivization K V` via `mapEquiv`.

The group structure on `V ≃ₗ[K] V` (`LinearEquiv.automorphismGroup`,
with `1 = refl` and `e₁ * e₂ = e₂.trans e₁`) transports to a
`MulAction` on `ℙ K V` because `Projectivization.map_id` discharges
`one_smul` and `Projectivization.map_comp` discharges `mul_smul`. -/
instance instMulAction : MulAction (V ≃ₗ[K] V) (ℙ K V) where
  smul := mapEquiv
  one_smul p := congrFun mapEquiv_one p
  mul_smul e₁ e₂ p := congrFun (mapEquiv_mul e₁ e₂) p

@[simp]
lemma mapEquiv_smul_eq (e : V ≃ₗ[K] V) (p : ℙ K V) : e • p = mapEquiv e p := rfl

variable [TopologicalSpace V] [ContinuousConstSMul K V]

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
case-of-interest (`K = ℂ` for LF4) with strictly less typeclass friction. -/

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
  haveI : ProperSpace V := FiniteDimensional.proper_rclike K V
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

end Projectivization
