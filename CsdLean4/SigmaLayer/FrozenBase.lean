/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ChartIntegralCurve

/-!
# SigmaLayer/FrozenBase: a frozen base forbids an outcome-dependent generator

**Category:** dynamical measurement — `specs/frozen-base-obstruction-scoping.md` brick 1.

## The statement

Both of the corpus's record-creating witnesses freeze the base **pointwise**: `Prod.fst ∘
evolve = Prod.fst`, from which `shear_base_marginal_unchanged` and
`pointerEvolve_base_marginal_unchanged` follow by `rfl`. This module prices that choice.

> **(a) ∧ (c′) ⇒ ¬(b)** — a generator that is `C¹` on a Darboux chart (a), whose flow leaves
> the base block pointwise fixed (c′), **cannot depend on the base** — so it cannot depend on
> the outcome index, and no record correlated with the outcome can be created (¬b).

* ★ `BaseFrozen` — (c′) as a condition on the generator: both partials vanish on the base
  block `S`. This is exactly "the base components of `hamiltonianField H` are identically
  zero", i.e. `ẋ_S = 0` and `ẏ_S = 0`.
* ★★ `baseConstant_of_baseFrozen` — the theorem. A base-frozen `C¹` generator takes the same
  value at any two points that agree off `S`.
* ★★ `not_baseFrozen_of_outcomeDependent` — the contrapositive, in the shape the obstruction
  is used: a generator that *does* distinguish two base sectors sharing a fibre point is not
  base-frozen. Its flow must move the base.

## Why the base block carries BOTH coordinates

`LF4.KSigma N = ℂℙ^{N-1} × T²` is a full even-dimensional symplectic factor: base positions
*and* base momenta both live in the base slot. So (c′) kills both halves of
`(∂_y 𝓗, −∂_x 𝓗)` on `S`, and the conclusion is that `𝓗` is base-**constant**, not merely
locally constant. ⚠️ *This is the correction that makes the argument non-circular*: reading
(c′) as killing only one partial yields "locally constant with seams", which is
`¬(a)` assumed in order to derive `¬(a)`. See `specs/frozen-base-obstruction-scoping.md` §5.

## ⚠️ Honest scope

**Two side conditions, both explicit in the statements, and neither is automatic.**

1. **Product `ω`.** The chart is `Chart n = (Fin n → ℝ) × (Fin n → ℝ)` with the canonical
   form, and `S`/`T` split the index set. True of `PointerArena N K := LF4.KSigma N × Pointer
   K`, a product of Kähler factors; **false in general** — a coupling that geometrically
   entangles system and apparatus need not split, and then the base component of the field
   picks up fibre derivatives through the cross terms and this argument dies.
2. **`C¹`.** `Differentiable ℝ H` is a hypothesis, not a consequence. Dropping it is exactly
   the seam horn (`RecordLayer/PiecewiseHamiltonian.lean`).

**This does not say back-reaction is required, and does not say the corpus's witnesses are
defective.** `RecordLayer/JointFlowTransfer.lean` proves the opposite direction — a genuine
joint lift *does* move the base, and back-reaction is harmless to records and Born
(`IsJointLift.moment_marginal_unchanged`). What this module adds is the price of the *other*
choice: freezing the base costs outcome-dependence of the generator. Both are theorems; the
corpus is not forced onto either horn.

**And it is a chart statement.** Nothing here transports to the arena — that transport is
the missing arrow (`SigmaLayer/ChartBracket.lean` honest scope, unchanged), and the
mathematics of `H_int(M)` **remains open** (⚠️ RESIDUE(R-016)). Which physical interaction an
apparatus realises is a permanent boundary rather than open work (⚠️ RESIDUE(R-015)).

## References

`specs/frozen-base-obstruction-scoping.md` (brick 1, and §5 for the withdrawn draft);
`specs/BACKLOG.md` A2/A3/A4; `specs/future-work.md`;
`SigmaLayer/ChartBracket.lean` (`Chart`, `dPos`, `dMom`, `hamiltonianField`);
`SigmaLayer/ChartIntegralCurve.lean` (brick 0 — the integral curve exists and is unique);
`RecordLayer/ShearWitness.lean` (`shear_base_marginal_unchanged`, the frozen base);
`RecordLayer/JointFlowTransfer.lean` (`IsJointLift.moment_marginal_unchanged`, the other
horn); `RecordLayer/PiecewiseHamiltonian.lean` (dropping `C¹`).
-/

@[expose] public section

namespace CSD.SigmaLayer

open Set

variable {n : ℕ}

/-! ### Coordinate expansion of a chart functional -/

/-- Any chart covector is determined by its values on the coordinate directions: the
gradient expansion `L Δ = Σᵢ Δxᵢ · L(∂xᵢ) + Σᵢ Δyᵢ · L(∂yᵢ)`. -/
theorem clm_apply_eq_sum (L : Chart n →L[ℝ] ℝ) (Δ : Chart n) :
    L Δ = (∑ i, Δ.1 i * L (posDir i)) + ∑ i, Δ.2 i * L (momDir i) := by
  classical
  have hpos : (∑ i, Δ.1 i • posDir (n := n) i) = (Δ.1, 0) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      funext j
      rw [Finset.sum_apply]
      simp [posDir, Pi.single_apply, mul_ite, Finset.sum_ite_eq]
    · rw [Prod.snd_sum]
      simp [posDir]
  have hmom : (∑ i, Δ.2 i • momDir (n := n) i) = (0, Δ.2) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp [momDir]
    · rw [Prod.snd_sum]
      funext j
      rw [Finset.sum_apply]
      simp [momDir, Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hsplit : Δ = (∑ i, Δ.1 i • posDir (n := n) i) + ∑ i, Δ.2 i • momDir (n := n) i := by
    rw [hpos, hmom]
    exact Prod.ext (by simp) (by simp)
  conv_lhs => rw [hsplit]
  rw [map_add, map_sum, map_sum]
  simp [smul_eq_mul]

/-- The gradient expansion for `fderiv`, in the corpus's `dPos`/`dMom` notation. -/
theorem fderiv_apply_eq_sum (H : Chart n → ℝ) (z Δ : Chart n) :
    fderiv ℝ H z Δ = (∑ i, Δ.1 i * dPos H z i) + ∑ i, Δ.2 i * dMom H z i :=
  clm_apply_eq_sum (fderiv ℝ H z) Δ

/-! ### The frozen base -/

/-- **(c′) The base is pointwise frozen.** Both partials of the generator vanish on the base
block `S`, which is exactly "the base components of `hamiltonianField H` are identically
zero": `ẋ_S = ∂_y H = 0` and `ẏ_S = −∂_x H = 0`. -/
def BaseFrozen (H : Chart n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ z, ∀ i ∈ S, dPos H z i = 0 ∧ dMom H z i = 0

/-- The frozen base is literally the vanishing of the field's base components. -/
theorem hamiltonianField_base_eq_zero {H : Chart n → ℝ} {S : Finset (Fin n)}
    (h : BaseFrozen H S) (z : Chart n) (i : Fin n) (hi : i ∈ S) :
    (hamiltonianField H z).1 i = 0 ∧ (hamiltonianField H z).2 i = 0 := by
  obtain ⟨hx, hy⟩ := h z i hi
  exact ⟨hy, by simp [hamiltonianField, hx]⟩

/-- Two chart points **agree off `S`**: they share every coordinate outside the base block. -/
def AgreeOff (S : Finset (Fin n)) (z z' : Chart n) : Prop :=
  ∀ i ∉ S, z.1 i = z'.1 i ∧ z.2 i = z'.2 i

/-- A frozen generator annihilates every direction supported in `S`. -/
theorem fderiv_apply_eq_zero_of_baseFrozen {H : Chart n → ℝ} {S : Finset (Fin n)}
    (h : BaseFrozen H S) (z Δ : Chart n)
    (hΔ : ∀ i ∉ S, Δ.1 i = 0 ∧ Δ.2 i = 0) :
    fderiv ℝ H z Δ = 0 := by
  classical
  rw [fderiv_apply_eq_sum]
  have h1 : (∑ i, Δ.1 i * dPos H z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [(h z i hi).1, mul_zero]
    · rw [(hΔ i hi).1, zero_mul]
  have h2 : (∑ i, Δ.2 i * dMom H z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [(h z i hi).2, mul_zero]
    · rw [(hΔ i hi).2, zero_mul]
  rw [h1, h2, add_zero]

/-! ### ★★ The obstruction -/

/-- ★★ **A frozen base forces a base-constant generator.** If `H` is differentiable (a) and
base-frozen (c′), it takes the same value at any two points agreeing off the base block.

The proof is the segment argument: the difference of two such points is supported in `S`, a
frozen generator annihilates every such direction, so `H` is constant along the segment. -/
theorem baseConstant_of_baseFrozen {H : Chart n → ℝ} {S : Finset (Fin n)}
    (hdiff : Differentiable ℝ H) (h : BaseFrozen H S) {z z' : Chart n}
    (hagree : AgreeOff S z z') : H z = H z' := by
  classical
  set Δ : Chart n := z' - z with hΔdef
  have hΔ : ∀ i ∉ S, Δ.1 i = 0 ∧ Δ.2 i = 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hagree i hi
    exact ⟨by simp [hΔdef, h1], by simp [hΔdef, h2]⟩
  -- The segment `t ↦ z + t • Δ`, and `H` along it.
  set g : ℝ → ℝ := fun t => H (z + t • Δ) with hgdef
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • Δ) Δ t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const Δ).const_add z
  have hg : ∀ t : ℝ, HasDerivAt g 0 t := by
    intro t
    have hcomp : HasDerivAt g (fderiv ℝ H (z + t • Δ) Δ) t :=
      HasFDerivAt.comp_hasDerivAt t (hdiff (z + t • Δ)).hasFDerivAt (hpath t)
    rwa [fderiv_apply_eq_zero_of_baseFrozen h _ Δ hΔ] at hcomp
  have hconst : g 1 = g 0 :=
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  have h0 : g 0 = H z := by simp [hgdef]
  have h1 : g 1 = H z' := by
    simp only [hgdef, one_smul, hΔdef]
    congr 1
    abel
  rw [← h0, ← h1, hconst]

/-- ★★ **The contrapositive, in the shape the obstruction is used.** A generator that
*distinguishes* two base sectors sharing their fibre data — which is what "the interaction
depends on the outcome index" means — is **not** base-frozen. Its flow must move the base.

This is the price of the frozen-base design, stated as a theorem: exact outcome-dependence
and a pointwise-frozen base are incompatible for a `C¹` generator on a product chart. -/
theorem not_baseFrozen_of_outcomeDependent {H : Chart n → ℝ} {S : Finset (Fin n)}
    (hdiff : Differentiable ℝ H) {z z' : Chart n}
    (hagree : AgreeOff S z z') (hne : H z ≠ H z') : ¬ BaseFrozen H S :=
  fun h => hne (baseConstant_of_baseFrozen hdiff h hagree)

end CSD.SigmaLayer
