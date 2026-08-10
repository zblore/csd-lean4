/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible

/-!
# The fundamental group of the circle

**Category:** 1-Mathlib (CSD-free).

Mathlib has the whole covering-space apparatus — path lifting, the monodromy
theorem, the monodromy permutation representation, and
`IsAddQuotientCoveringMap.fundamentalGroupEquiv`, which identifies the
fundamental group of the base of a simply-connected quotient covering with the
(opposite of the) deck group. It also has
`Circle.isAddQuotientCoveringMap_exp`, exhibiting `Circle.exp : ℝ → Circle` as
exactly such a covering with deck group `2πℤ`. What it does **not** state
anywhere is the classical consequence, that the circle's fundamental group is
`ℤ` and in particular is nontrivial.

This module supplies it. Everything here is a short application of the two
results above; the mathematical work was already done upstream.

* `Circle.fundamentalGroupEquivZMultiples` — `π₁(S¹) ≃* (2πℤ)ᵐᵒᵖ`, written
  multiplicatively.
* ★ `Circle.fundamentalGroup_nontrivial` — the circle's fundamental group is
  nontrivial. This is the form downstream obstruction arguments consume: a
  loop-exchange acting nontrivially on `π₁` cannot be joined to the identity.
* `Circle.not_simplyConnectedSpace` — the circle is not simply connected.

## Why this is here

It is the first brick of the relocation-generation obstruction
(`specs/BACKLOG.md`): a time-one map of a flow is homotopic to the identity, so
it acts trivially on `π₁`, whereas exchanging two identical factors of a product
arena does not. That argument needs one nontrivial fundamental group to run
against, and the record arenas' torus factors supply it.

## References

`Mathlib/Topology/Homotopy/Lifting.lean` (`fundamentalGroupEquiv`,
`monodromy_theorem`); `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`
(`isAddQuotientCoveringMap_exp`); `specs/future-work.md`; `MATHLIB-GAPS.md`.
-/

@[expose] public section

open Real

namespace Circle

/-- The basepoint `0 : ℝ` lies in the fibre of `Circle.exp` over `1`. -/
def expFibreZero : (Circle.exp ⁻¹' {1} : Set ℝ) := ⟨0, by simp⟩

@[simp] theorem expFibreZero_val : (expFibreZero : ℝ) = 0 := rfl

/-- **The fundamental group of the circle is its deck group.** `Circle.exp` is a
quotient covering with deck group `2πℤ` and simply-connected total space `ℝ`, so
the upstream `fundamentalGroupEquiv` applies verbatim. -/
noncomputable def fundamentalGroupEquivZMultiples :
    FundamentalGroup Circle 1 ≃* (Multiplicative (AddSubgroup.zmultiples (2 * π)))ᵐᵒᵖ :=
  Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv expFibreZero

/-- The deck group `2πℤ` is nontrivial, since `2π ≠ 0`. -/
theorem nontrivial_zmultiples_two_pi : Nontrivial (AddSubgroup.zmultiples (2 * π)) := by
  refine ⟨⟨0, ⟨2 * π, AddSubgroup.mem_zmultiples _⟩, ?_⟩⟩
  simp [Subtype.ext_iff, Real.pi_ne_zero]

/-- ★ **The circle's fundamental group is nontrivial.** The classical fact, here
a transport of `nontrivial_zmultiples_two_pi` along the deck-group equivalence.

This is the form the obstruction arguments consume: any self-map joined to the
identity by a flow induces the identity on `π₁`, so a map inducing a nonidentity
automorphism is not a time-one flow map. -/
theorem fundamentalGroup_nontrivial : Nontrivial (FundamentalGroup Circle 1) := by
  have : Nontrivial (AddSubgroup.zmultiples (2 * π)) := nontrivial_zmultiples_two_pi
  exact fundamentalGroupEquivZMultiples.symm.injective.nontrivial

/-- **The circle is not simply connected.** A simply connected space has
subsingleton fundamental group, which contradicts
`fundamentalGroup_nontrivial`. -/
theorem not_simplyConnectedSpace : ¬ SimplyConnectedSpace Circle := by
  intro h
  have hsub : Subsingleton (FundamentalGroup Circle 1) := inferInstance
  exact (not_subsingleton_iff_nontrivial.mpr fundamentalGroup_nontrivial) hsub

/-- ★ **The circle is not contractible.** A contractible space is simply
connected (`SimplyConnectedSpace.ofContractible`). -/
theorem not_contractibleSpace : ¬ ContractibleSpace Circle := fun _ =>
  not_simplyConnectedSpace inferInstance

end Circle

namespace AddCircle

/-- ★ **The additive circle is not contractible**, for any nonzero period,
transported from `Circle.not_contractibleSpace` along
`AddCircle.homeomorphCircle`. This is the form the record arenas consume, since
`LF4.KTorus` is a product of copies of `AddCircle 1`. -/
theorem not_contractibleSpace {T : ℝ} (hT : T ≠ 0) : ¬ ContractibleSpace (AddCircle T) :=
  fun _ => Circle.not_contractibleSpace (AddCircle.homeomorphCircle hT).symm.contractibleSpace

end AddCircle
