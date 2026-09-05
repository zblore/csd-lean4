/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CellLawFreedom
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.HamiltonianVectorField

/-!
# RecordLayer/CellLawForced: what does force the cell law

**Category:** 7-SigmaLayer (the record layer's own foundations).
**TERM-SCOPE(Hamiltonian)** — the vector-field sense, at the *linear* level; `specs/TERMS.md`.

`CellLawFreedom.lean` proves the negative half: torus **invariance**, normalisation, support and
measurability do not single out the moment map. This module proves the positive half, and the gap
between them is one word. `sqRate` is invariant under the torus action; the moment map **generates**
it. Generation is the moment-map equation `ι_{X_i} ω = dΦᵢ`, and it forces the rates.

## What is proved

★★ `torusGenerated_eq_momentMap` — if a `ContextField`'s rates are the degree-0 normalisations of
Hamiltonians for the coordinate phase rotations, then they **are** the moment map. Not up to a
constant: exactly, and with **no side hypothesis at all** — not even `N ≥ 2`.

⚠️ **Where the rigidity actually lives**, because it is easy to misattribute and a first draft of
this header did. The additive constant is killed by **homogeneity**, not by the context field's
axioms: `rate` is a function of the *ray*, the homogenisation has degree two, so rescaling a
representative by `2` forces `k = 4k`. `sum_one` and `nonneg` are never used. (In the *manifold*
argument the division of labour is the other way — on `ℂℙᴺ⁻¹` circle-Hamiltonians genuinely carry
the freedom `Φᵢ + cᵢ`, and there the simplex axioms are exactly what remove it. This proof enacts
that argument's shape on a linear predicate that never had the freedom.)

The chain: ★ `isPhaseHamiltonian_coordEnergy` (the coordinate energy `‖xᵢ‖²/2` generates the `i`-th
phase rotation — the instantiation of `quadraticEnergy_hamiltonian_duality` at the coordinate
projection); ★ `IsPhaseHamiltonian.eq_coordEnergy_add` (uniqueness up to an additive constant, from
`is_const_of_fderiv_eq_zero` on the connected model); then the two pinning steps above.

★ `isTorusGenerated_momentContext` — the hypothesis is inhabited, so the theorem is not vacuous.

★ `sqContext_not_torusGenerated` — and the rival of `CellLawFreedom.lean` fails it. This is a *one
line* consequence of the two modules together: if `sqContext` generated the rotations it would equal
the moment map, contradicting `rate_field_not_forced_by_torus_symmetry`. The freedom theorem is what
makes the forcing theorem bite.

## What this settles, and at what price

**Settles:** what the corpus has to assume about the cell law. `specs/POSITS.md` Posit 1 is
**restated, not discharged** — the posit count is unchanged and the honest headline is that its
*quality* improves: from *the rates are this formula* to *the rates generate the phase rotations of
the measurement context's pointer torus*. That is the definition of a moment map.

The gain is **anti-circularity**, and it is the real prize here. The old premise was a Born-shaped
formula `‖pᵢ‖²/‖p‖²` feeding a derivation of Born — the very worry `GlobalBasin.lean`'s
anti-circularity note fences off. The new premise, `ι_{X_i} ω = dF`, mentions no probability, no
amplitude, no Born target: it is a condition on generating a group action. The Born *shape* of the
rates is now derived from a non-probabilistic geometric premise.

And the premise is **not** a noncontextuality assumption — it is single-context, one basis, with no
cross-basis family anywhere in it. The Gleason/frame-function route, which would have cost
noncontextuality (`specs/cell-law-scoping.md`, stage 2), is not needed and is not taken. So
"Gleason-free" survives intact for both the volume theorem and the cell law.

⚠️ **What is *not* settled, stated at full strength.** `IsTorusGenerated c` is extensionally
equivalent to `c.rate = momentMap` — the theorem above is one direction, and
`isTorusGenerated_momentContext` is the other. So this is a *characterisation*, and the forcing is
conditional on a premise as strong as the cell law itself, differently and better expressed. Nothing
in `ContextField`, in the dynamics, or anywhere else in the corpus compels a context's rates to be
Hamiltonian generators of its pointer torus. Deriving *that* from the de-isolation dynamics is the
`H_int` frontier, and it is not attempted here.

**Price, stated plainly.** This is the **linear** statement, on the Hermitian model `ℂᴺ` with the
Kähler structure taken as given (`Kahler.fundamentalForm`; the pointwise triple is
`IsFubiniStudyKahler`). The manifold statement — that this is *the* moment map of the `Tⁿ` action on
`ℂℙᴺ⁻¹` for the Fubini–Study symplectic form — remains unformalised, Mathlib having no symplectic
manifold API (`MATHLIB-ABSENT(file:Mathlib/Geometry/Manifold/DifferentialForm)`). ⚠️ **The Kähler
and manifold structures are posited, deliberately** (author decision 2026-09-04); what is proved is
that *given* them the rate field is forced. The descent from `ℂᴺ` to `ℂℙᴺ⁻¹` is by explicit degree-0
homogenisation (`IsTorusGenerated`), not by manifold theory, so no quotient machinery is assumed.

**Two conventions are visible in the predicate and should stay visible.** `IsTorusGenerated` asks
for a Hamiltonian defined and differentiable on all of `ℂᴺ`; `momentContext` supplies one
(`‖xᵢ‖²/2`, polynomial), and since `ℂᴺ ∖ {0}` is connected any solution on the punctured space
extends, so this costs nothing. And the form's **scale** is fixed — `phaseGen` fixes unit-speed
rotation, `fundamentalForm` fixes `ω u (J u) = ‖u‖²`. Rescaling `ω ↦ λω` does not produce a rival
cell law: it makes the predicate uninhabited among context fields, since `sum_one` rejects
`λ · momentMap`. (`CellLawFreedom.lean` records the same scale point.)

⚠️ Constant-shifted fields `momentMap + c` with `∑cᵢ = 0` *are* circle-Hamiltonians on `ℂℙᴺ⁻¹` and
fail this predicate — so it is intensionally stricter than the manifold condition. No legitimate
rival is excluded by that: every such field violates `nonneg`, since each `momentMapᵢ` attains `0`.

## References

`RecordLayer/CellLawFreedom.lean` (`sqContext`, `rate_field_not_forced_by_torus_symmetry` — the
negative half this module completes); `RecordLayer/GlobalBasin.lean` (`ContextField`,
`momentContext`, `globalBasin_born`); `Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean`
(`quadraticEnergy_hamiltonian_duality`, `hamiltonianVectorFieldOf`, `fundamentalForm`);
`LF4/MomentMap.lean` (`momentMap_mk`, `euclidean_norm_sq_eq_sum`); `LF4/KahlerOnticSetup.lean`
(`IsFubiniStudyKahler` — the posited structure); `specs/POSITS.md` (Posit 1, restated here — *not* discharged);
`specs/cell-law-scoping.md` (why the frame-function route was declined);
`specs/future-work.md` ("Cell-law characterisation"); `specs/TERMS.md` (Hamiltonian, two senses).
-/

@[expose] public section

open Kahler

namespace CSD
namespace RecordLayer

open LF4

variable {N : ℕ}

/-! ### The coordinate projection and its energy

CSD-free linear algebra; an upstream candidate alongside `HamiltonianVectorField.lean`. -/

/-- The `i`-th coordinate projection, as a continuous linear map. -/
noncomputable def coordProj (i : Fin N) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (EuclideanSpace.proj i).smulRight (EuclideanSpace.single i (1 : ℂ))

lemma coordProj_apply (i : Fin N) (x : EuclideanSpace ℂ (Fin N)) :
    coordProj i x = EuclideanSpace.single i (x i) := by
  ext j
  simp [coordProj, PiLp.single_apply]

lemma coordProj_symm (i : Fin N) (u v : EuclideanSpace ℂ (Fin N)) :
    inner ℂ (coordProj i u) v = inner ℂ u (coordProj i v) := by
  simp [coordProj_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, mul_comm]

/-- The `i`-th **coordinate energy** `‖xᵢ‖²/2` — the quadratic energy of the `i`-th projection. -/
noncomputable def coordEnergy (i : Fin N) (x : EuclideanSpace ℂ (Fin N)) : ℝ := ‖x i‖ ^ 2 / 2

lemma quadraticEnergy_coordProj (i : Fin N) :
    quadraticEnergy (coordProj i) = coordEnergy (N := N) i := by
  funext x
  have h : ‖x i‖ ^ 2 = (x i).re * (x i).re + (x i).im * (x i).im := by
    rw [← RCLike.normSq_eq_def' (x i)]; simp [Complex.normSq_apply]
  simp [quadraticEnergy, metric, coordProj_apply, EuclideanSpace.inner_single_right,
    coordEnergy, h]
  ring

@[simp] lemma coordEnergy_zero (i : Fin N) :
    coordEnergy i (0 : EuclideanSpace ℂ (Fin N)) = 0 := by
  simp [coordEnergy]

/-- The coordinate energies sum to half the squared norm — the identity that will pin the
constants against `ContextField.sum_one`. -/
lemma sum_coordEnergy (x : EuclideanSpace ℂ (Fin N)) :
    ∑ i, coordEnergy i x = ‖x‖ ^ 2 / 2 := by
  simp only [coordEnergy, ← Finset.sum_div]
  rw [← euclidean_norm_sq_eq_sum]

/-! ### Generating the phase rotation -/

/-- The generator of the `i`-th coordinate phase rotation, `-(i · Pᵢ x)`. -/
noncomputable def phaseGen (i : Fin N) (x : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  -(Complex.I • coordProj i x)

/-- `F` is a **Hamiltonian for the `i`-th phase rotation**: `ι_{X_i} ω = dF`. This is the
moment-map equation, at the linear level, and it is the property `sqRate` lacks. -/
def IsPhaseHamiltonian (F : EuclideanSpace ℂ (Fin N) → ℝ) (i : Fin N) : Prop :=
  Differentiable ℝ F ∧ ∀ x v, fundamentalForm (phaseGen i x) v = fderiv ℝ F x v

/-- ★ **The coordinate energy generates the phase rotation.** The instantiation of
`quadraticEnergy_hamiltonian_duality` at the coordinate projection — the ingredient the linear
Hamiltonian layer had and never used. -/
theorem isPhaseHamiltonian_coordEnergy (i : Fin N) :
    IsPhaseHamiltonian (coordEnergy (N := N) i) i := by
  constructor
  · intro x
    rw [← quadraticEnergy_coordProj i]
    exact (hasFDerivAt_quadraticEnergy (coordProj i) (coordProj_symm i) x).differentiableAt
  · intro x v
    have := quadraticEnergy_hamiltonian_duality (coordProj i) (coordProj_symm i) x v
    rw [quadraticEnergy_coordProj i] at this
    rwa [hamiltonianVectorFieldOf, complexStructure] at this

/-- ★ **Uniqueness up to an additive constant.** Two Hamiltonians for the same vector field have
equal differentials, and `ℂᴺ` is connected, so they differ by a constant. -/
theorem IsPhaseHamiltonian.eq_coordEnergy_add {F : EuclideanSpace ℂ (Fin N) → ℝ} {i : Fin N}
    (h : IsPhaseHamiltonian F i) (x : EuclideanSpace ℂ (Fin N)) :
    F x = coordEnergy i x + F 0 := by
  obtain ⟨hdiff, hgen⟩ := h
  obtain ⟨hdiff', hgen'⟩ := isPhaseHamiltonian_coordEnergy (N := N) i
  have hfd : ∀ y, fderiv ℝ F y = fderiv ℝ (coordEnergy (N := N) i) y := by
    intro y; ext v; rw [← hgen y v, hgen' y v]
  have hg : ∀ y, fderiv ℝ (fun z => F z - coordEnergy (N := N) i z) y = 0 := by
    intro y
    have h1 : HasFDerivAt (fun z => F z - coordEnergy (N := N) i z)
        (fderiv ℝ F y - fderiv ℝ (coordEnergy (N := N) i) y) y :=
      (hdiff y).hasFDerivAt.sub (hdiff' y).hasFDerivAt
    rw [hfd y, sub_self] at h1
    exact h1.fderiv
  have hconst := is_const_of_fderiv_eq_zero (hdiff.sub hdiff') hg x 0
  have h0 : coordEnergy (N := N) i (0 : EuclideanSpace ℂ (Fin N)) = 0 := by simp [coordEnergy]
  simp only [Pi.sub_apply] at hconst
  linarith [hconst, h0]

/-! ### The cell law, forced -/

/-- A context field is **torus-generated** when its rates are the degree-0 normalisations of
Hamiltonians for the coordinate phase rotations — i.e. when they are moment coordinates.

This is the hypothesis that does the work, and it is the one `sqContext` fails: invariance under
the torus is weaker than generating it. -/
def IsTorusGenerated (c : ContextField N) : Prop :=
  ∀ i : Fin N, ∃ F : EuclideanSpace ℂ (Fin N) → ℝ, IsPhaseHamiltonian F i ∧
    ∀ (x : EuclideanSpace ℂ (Fin N)) (hx : x ≠ 0),
      c.rate (Projectivization.mk ℂ x hx) i = F x / (‖x‖ ^ 2 / 2)

/-- ★ **The hypothesis is inhabited** — the moment-map field is torus-generated, so the forcing
theorem below is not vacuous. -/
theorem isTorusGenerated_momentContext : IsTorusGenerated (momentContext N) := by
  intro i
  refine ⟨coordEnergy i, isPhaseHamiltonian_coordEnergy i, ?_⟩
  intro x hx
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  show momentMap (Projectivization.mk ℂ x hx) i = _
  rw [momentMap_mk x hx i, coordEnergy]
  field_simp

/-- ★★ **The cell law is forced, given generation.** A context field whose rates generate the
coordinate phase rotations *is* the moment map — exactly, not up to a constant, and with no side
hypothesis. The additive freedom left by `IsPhaseHamiltonian.eq_coordEnergy_add` is removed by
**homogeneity**: the rate is a function of the ray while the homogenisation has degree two, so
rescaling a representative by `2` forces `k = 4k`. ⚠️ The context field's own axioms (`sum_one`,
`nonneg`) are **not** used — an earlier draft of this docstring said they were, which was a
misreading of the proof route; see the header.

With `CellLawFreedom.rate_field_not_forced_by_torus_symmetry` this locates the boundary precisely:
torus *invariance* leaves a continuum of rate fields, torus *generation* leaves exactly one. -/
theorem torusGenerated_eq_momentMap (c : ContextField N)
    (h : IsTorusGenerated c) (p : CPN N) (i : Fin N) :
    c.rate p i = momentMap p i := by
  choose F hF hrate using h
  -- The additive constant vanishes, and it is **homogeneity** that kills it, not the context
  -- field's axioms: `c.rate` is a function of the ray, while the homogenisation has degree two,
  -- so rescaling a representative by `2` forces `F i 0 = 4 * F i 0`.
  have hzero : F i 0 = 0 := by
    set x : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single i (1 : ℂ) with hx_def
    have hx : x ≠ 0 := by simp [hx_def, PiLp.single_eq_zero_iff]
    have hy : (2 : ℂ) • x ≠ 0 := by
      simp [hx_def, PiLp.single_eq_zero_iff]
    have hmk : Projectivization.mk ℂ ((2 : ℂ) • x) hy = Projectivization.mk ℂ x hx := by
      rw [Projectivization.mk_eq_mk_iff]
      exact ⟨Units.mk0 (2 : ℂ) two_ne_zero, rfl⟩
    have hxn : ‖x‖ = 1 := by simp [hx_def, PiLp.norm_single]
    have hxi : ‖x i‖ = 1 := by simp [hx_def]
    have hyn : ‖(2 : ℂ) • x‖ = 2 := by
      rw [norm_smul, hxn]; simp
    have hyi : ‖((2 : ℂ) • x) i‖ = 2 := by
      simp [hx_def]
    have e1 := hrate i x hx
    have e2 := hrate i ((2 : ℂ) • x) hy
    rw [hmk, e1] at e2
    rw [(hF i).eq_coordEnergy_add x, (hF i).eq_coordEnergy_add ((2 : ℂ) • x)] at e2
    rw [coordEnergy, coordEnergy, hxn, hxi, hyn, hyi] at e2
    norm_num at e2
    linarith
  have key : ∀ (x : EuclideanSpace ℂ (Fin N)) (hx : x ≠ 0),
      c.rate (Projectivization.mk ℂ x hx) i = coordEnergy i x / (‖x‖ ^ 2 / 2) := by
    intro x hx
    rw [hrate i x hx, (hF i).eq_coordEnergy_add x, hzero, add_zero]
  have hrep := Projectivization.mk_rep p
  have hpn : p.rep ≠ 0 := p.rep_nonzero
  have hn : ‖p.rep‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hpn)
  calc c.rate p i
      = c.rate (Projectivization.mk ℂ p.rep hpn) i := by rw [hrep]
    _ = coordEnergy i p.rep / (‖p.rep‖ ^ 2 / 2) := key p.rep hpn
    _ = momentMap p i := by
        rw [coordEnergy]
        show _ = ‖p.rep i‖ ^ 2 / ‖p.rep‖ ^ 2
        field_simp

/-- ★ **The rival cell law fails the generating condition.** `sqContext` matches the moment map on
every property the corpus verifies of it and is still not it, so by the forcing theorem it cannot
generate the phase rotations. The freedom theorem is exactly what makes this a one-line
consequence — the two modules are one argument. -/
theorem sqContext_not_torusGenerated : ¬ IsTorusGenerated (sqContext 3) := by
  intro h
  obtain ⟨p, i, hne⟩ := rate_field_not_forced_by_torus_symmetry
  have heq := torusGenerated_eq_momentMap (N := 3) (sqContext 3) h p i
  rw [sqContext_rate] at heq
  exact hne heq

end RecordLayer
end CSD
