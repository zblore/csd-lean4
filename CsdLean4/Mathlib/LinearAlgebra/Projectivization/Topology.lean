import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Maps.OpenQuotient

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

The Hausdorff and compactness instances (under normed finite-dim
hypotheses) live in a companion file.

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
    have := congrArg (((a : Kˣ) : K)⁻¹ • ·) hsmul
    simp only at this
    rw [← mul_smul, inv_mul_cancel₀ a.ne_zero, one_smul] at this
    exact this.symm
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

end TopologicalAction

end Projectivization
