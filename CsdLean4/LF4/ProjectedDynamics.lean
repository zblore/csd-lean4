/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.UnitarySelection
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# W5: projected CSD dynamics = projective action of a one-parameter unitary family

**Category:** 3-Local (projected CSD dynamics = projective action of a one-parameter unitary family).

This module is the milestone of the CSD dynamics spine. It shows that the
projected ontic flow of a Kähler ontic setup, once the W3 Wigner selection has
placed every time-`t` map on the unitary branch, IS the projective action of a
one-parameter unitary family `{U_t}`. This is the honest Lean-first reading of
"projected CSD dynamics recovers finite-dimensional Schrödinger evolution".

## What is proved (the achievable core)

* `projectedFlow_eq_unitary_family` (PROVED, the milestone): given the W3
  selection output `hU : ∀ t, ProjUnitary d t`, the projected flow is the
  projective action of a one-parameter unitary family:
  `∃ U : ℝ → unitaryGroup, ∀ t p, d.projectedFlow t p = U t • p`. Choice over
  the per-`t` existentials (`Classical.choice`, foundational-triple). The
  unitary family comes from `hU` / W3 (the Wigner selection), NOT from
  `flow_preserves_volume`: measure-preservation does not imply
  transition-probability preservation (measure ≠ metric, the §13.2 trap).

* `unitaryFamily_projective_representation` (PROVED, the ray-level group law):
  under the explicit ONE-PARAMETER-GROUP hypotheses on the projected flow
  (`d.projectedFlow (s+t) = d.projectedFlow s ∘ d.projectedFlow t`,
  `d.projectedFlow 0 = id`), the selected unitary family is a PROJECTIVE
  one-parameter representation: `U (s+t) • p = (U s * U t) • p` and
  `U 0 • p = p` for every `p`. This is the group law at the projective (ray)
  level, the level at which the projected flow lives. The group hypotheses are
  physical inputs, NOT carried by `KahlerOnticSetup` (its `flow` field has no
  one-parameter-group law, by design); they are surfaced as explicit
  hypotheses.

## What is STAGED (the deeper residual, precisely named)

The vector-level `U_t = exp(-i t H)` for a Hermitian generator `H` (the
Schrödinger form) is NOT claimed here. Two ingredients are missing and named
(BOTH SINCE DISCHARGED downstream: S2 by `Mathlib/Analysis/Matrix/StoneC1.lean`
(2026-07-05, C^1 form) and S1 by `LF4/PhaseLift.lean` (2026-07-07, on the
coboundary datum), whose `projectedFlow_schrodinger_form` is the assembled
capstone; this module's staging remarks describe the honest scope of THIS
file):

  (S1) **The projective-to-vector phase lift.** The ray-level representation
       `U (s+t) • p = (U s * U t) • p` only forces `U (s+t)` and `U s * U t`
       to agree UP TO A PHASE (they act identically on every ray). Promoting
       this to a genuine vector-level group `U (s+t) = U s * U t` requires
       killing the projective phase cocycle `c(s,t) ∈ U(1)`, i.e. a section of
       `U(N) → PU(N)` that is a group homomorphism. That lift is a physical /
       cohomological input not carried by the setup.

  (S2) **Finite-dimensional Stone's theorem.** Even with a genuine vector-level
       strongly-continuous one-parameter unitary group, recovering the
       self-adjoint generator `H` with `U_t = exp(-i t H)` is Stone's theorem.
       Mathlib (this toolchain) has `Matrix.exp` and `exp_conjTranspose` but
       NO Stone's theorem for one-parameter unitary groups (`Stone*` in Mathlib
       is Stone-Weierstrass / Stone-Cech / Stone-separation, all unrelated). So
       the generator-recovery direction is unavailable upstream.

The CONVERSE direction IS available and is recorded as a genuine realizability
witness: `expNegITH_unitary_group` shows that for any Hermitian `H`,
`t ↦ exp(-i t H)` is a genuine vector-level one-parameter unitary GROUP. This
certifies the `exp(-itH)` target form is inhabited (the Schrödinger family is a
real object), while making explicit that it is the converse of Stone, not
Stone: it constructs `U_t` FROM `H`, it does not recover `H` from an abstract
projected flow.

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `busch`,
no `sorry`, no `native_decide`, no new axioms. Reuses W2/W3 (`KahlerOnticSetup`,
`ProjUnitary`, the `Matrix.unitaryGroup` action from `Unitary.lean`) and
Mathlib's `Matrix.exp`; nothing is re-proved.
-/

open MeasureTheory
open scoped LinearAlgebra.Projectivization
open Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ## Part 1: the milestone (projective action of a one-parameter unitary family) -/

/-- **The W5 milestone (PROVED).** Given the W3 Wigner-selection output
`hU : ∀ t, ProjUnitary d t` (every time-`t` projected map is on the unitary
branch), the projected flow is the projective action of a single one-parameter
unitary family `{U_t}`:

    `∃ U : ℝ → unitaryGroup (Fin N) ℂ, ∀ t p, d.projectedFlow t p = U t • p`.

This is choice over the per-`t` existentials packaged in `ProjUnitary`
(`Classical.choice`, foundational-triple). The unitary family is supplied by
`hU` / the Wigner selection, NOT by `flow_preserves_volume`: the projected flow
being measure-preserving does not make it transition-probability preserving
(measure ≠ metric), so the unitary structure genuinely enters through the W3
FS-isometry posit, not the Liouville field. -/
theorem projectedFlow_eq_unitary_family
    (d : KahlerOnticSetup N) (hU : ∀ t, ProjUnitary d t) :
    ∃ U : ℝ → Matrix.unitaryGroup (Fin N) ℂ,
      ∀ t p, d.projectedFlow t p = U t • p := by
  choose U hU' using hU
  exact ⟨U, hU'⟩

/-! ## Part 2: the ray-level one-parameter projective representation -/

/-- **The ray-level group law (PROVED).** Under the explicit
one-parameter-group hypotheses on the projected flow (`hgrp` composition,
`h0` identity), any unitary family `U` realising the projected flow
(`hfam`) is a PROJECTIVE one-parameter representation:

    `U (s + t) • p = (U s * U t) • p`   and   `U 0 • p = p`   for all `p`.

The equalities hold at the RAY level (as maps on `ℙ ℂ (EuclideanSpace ℂ (Fin N))`);
they do NOT assert the vector-level identities `U (s+t) = U s * U t`,
`U 0 = 1`, which would additionally require killing the projective phase
cocycle (residual S1, see the module docstring). The group hypotheses are
physical inputs not carried by `KahlerOnticSetup`; they are surfaced here as
explicit arguments. -/
theorem unitaryFamily_projective_representation
    (d : KahlerOnticSetup N)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (hfam : ∀ t p, d.projectedFlow t p = U t • p)
    (hgrp : ∀ s t, d.projectedFlow (s + t)
            = d.projectedFlow s ∘ d.projectedFlow t)
    (h0 : d.projectedFlow 0 = id) :
    (∀ (s t : ℝ) (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))),
        U (s + t) • p = (U s * U t) • p)
      ∧ (∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)), U 0 • p = p) := by
  refine ⟨fun s t p => ?_, fun p => ?_⟩
  · have h1 : U (s + t) • p = d.projectedFlow (s + t) p := (hfam _ _).symm
    rw [h1, hgrp s t, Function.comp_apply, hfam s (d.projectedFlow t p),
      hfam t p, mul_smul]
  · have hp : d.projectedFlow 0 p = U 0 • p := hfam 0 p
    rw [h0, id_eq] at hp
    exact hp.symm

/-- The projected flow, packaged directly as a projective one-parameter
representation from the W3 selection plus the group hypotheses: the milestone
family and the ray-level group law together. -/
theorem projectedFlow_projective_one_parameter_representation
    (d : KahlerOnticSetup N)
    (hU : ∀ t, ProjUnitary d t)
    (hgrp : ∀ s t, d.projectedFlow (s + t)
            = d.projectedFlow s ∘ d.projectedFlow t)
    (h0 : d.projectedFlow 0 = id) :
    ∃ U : ℝ → Matrix.unitaryGroup (Fin N) ℂ,
      (∀ t p, d.projectedFlow t p = U t • p)
        ∧ (∀ (s t : ℝ) (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))),
            U (s + t) • p = (U s * U t) • p)
        ∧ (∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)), U 0 • p = p) := by
  obtain ⟨U, hfam⟩ := projectedFlow_eq_unitary_family d hU
  obtain ⟨hgrp', h0'⟩ :=
    unitaryFamily_projective_representation d U hfam hgrp h0
  exact ⟨U, hfam, hgrp', h0'⟩

/-! ## Part 3 (STAGED): the `exp(-itH)` converse realizability witness

The Stone direction (recover a Hermitian `H` with `U_t = exp(-i t H)` from an
abstract projected flow) is unavailable: it needs the phase lift S1 and
finite-dim Stone S2, neither in this toolchain. The CONVERSE direction is
available and recorded here as a genuine realizability witness: for any
Hermitian `H`, `t ↦ exp(-i t H)` is a genuine vector-level one-parameter
unitary group. This certifies the Schrödinger target form is inhabited, and
makes explicit that it is the converse of Stone (it builds `U_t` from `H`, it
does not recover `H`). -/

section Exp

open scoped Matrix.Norms.Operator
open scoped Matrix
open NormedSpace

/-- The candidate Schrödinger generator matrix `-(i t) H` for a time `t` and a
matrix `H`. When `H` is Hermitian and `t` real this is skew-Hermitian, so its
matrix exponential is unitary. -/
noncomputable def schrodingerGen (H : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (-(t : ℂ) * Complex.I) • H

/-- For Hermitian `H`, the generator `-(i t) H` is skew-Hermitian:
`(schrodingerGen H t)ᴴ = - schrodingerGen H t`. -/
theorem schrodingerGen_star {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    (schrodingerGen H t)ᴴ = -schrodingerGen H t := by
  unfold schrodingerGen
  rw [Matrix.conjTranspose_smul, hH, ← neg_smul]
  congr 1
  simp only [star_mul', star_neg, RCLike.star_def, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- **`exp(-itH)` is unitary (PROVED).** For Hermitian `H` and real `t`, the
matrix exponential `exp(schrodingerGen H t) = exp(-i t H)` lies in
`unitaryGroup (Fin N) ℂ`: the generator is skew-Hermitian, so
`(exp A)ᴴ = exp (Aᴴ) = exp (-A)` and `exp A * exp (-A) = exp 0 = 1`. -/
theorem schrodingerGen_exp_mem_unitaryGroup {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp (schrodingerGen H t) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, schrodingerGen_star hH t,
    ← Matrix.exp_add_of_commute (schrodingerGen H t) (-schrodingerGen H t)
      (Commute.neg_right (Commute.refl (schrodingerGen H t))),
    add_neg_cancel, NormedSpace.exp_zero]

/-- The unitary `exp(-i t H) ∈ unitaryGroup` as a bundled group element. -/
noncomputable def schrodingerUnitary {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (t : ℝ) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨NormedSpace.exp (schrodingerGen H t), schrodingerGen_exp_mem_unitaryGroup hH t⟩

/-- **The `exp(-itH)` family is a vector-level one-parameter unitary GROUP
(PROVED, the converse realizability witness).** For Hermitian `H`, the family
`U t = exp(-i t H)` satisfies `U (s + t) = U s * U t` and `U 0 = 1` as genuine
matrix / unitary-group identities (NOT merely up to phase). This certifies the
Schrödinger target form `exp(-itH)` is inhabited.

Honest scope: this is the CONVERSE of Stone (it constructs `U_t` FROM `H`); it
does NOT recover `H` from an abstract projected flow. The projected-flow →
generator direction remains staged on the phase lift (S1) and finite-dim Stone
(S2); see the module docstring. -/
theorem expNegITH_unitary_group {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) :
    (∀ s t, schrodingerUnitary hH (s + t)
        = schrodingerUnitary hH s * schrodingerUnitary hH t)
      ∧ schrodingerUnitary hH 0 = 1 := by
  constructor
  · intro s t
    apply Subtype.ext
    show NormedSpace.exp (schrodingerGen H (s + t))
      = NormedSpace.exp (schrodingerGen H s) * NormedSpace.exp (schrodingerGen H t)
    have hcomm : Commute (schrodingerGen H s) (schrodingerGen H t) :=
      ((Commute.refl H).smul_left _).smul_right _
    have hadd : schrodingerGen H (s + t)
        = schrodingerGen H s + schrodingerGen H t := by
      unfold schrodingerGen
      rw [← add_smul]
      congr 1
      push_cast
      ring
    rw [hadd, Matrix.exp_add_of_commute _ _ hcomm]
  · apply Subtype.ext
    show NormedSpace.exp (schrodingerGen H 0) = 1
    unfold schrodingerGen
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, zero_smul]
    exact NormedSpace.exp_zero

end Exp

/-! ## Non-vacuity on the `trivialKahlerOnticSetup` witness -/

/-- The milestone fires on the inhabitation witness: `hU` holds (the identity
flow is `ProjUnitary` via `1`), so the projected flow is the projective action
of the constant unitary family `U t = 1`. Genuine (`id = (1 : _) • ·`), not
vacuous. -/
theorem trivialKahlerOnticSetup_eq_unitary_family
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∃ U : ℝ → Matrix.unitaryGroup (Fin N) ℂ,
      ∀ t p, (trivialKahlerOnticSetup N p₀).projectedFlow t p = U t • p :=
  projectedFlow_eq_unitary_family (trivialKahlerOnticSetup N p₀)
    (trivialKahlerOnticSetup_projUnitary N p₀)

/-- The full projective one-parameter representation fires on the inhabitation
witness: the identity flow IS a one-parameter group (`projectedFlow t = id` for
all `t`, so composition and identity hold on the nose), so the milestone family
`U t = 1` is a genuine trivial one-parameter representation. -/
theorem trivialKahlerOnticSetup_projective_representation
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∃ U : ℝ → Matrix.unitaryGroup (Fin N) ℂ,
      (∀ t p, (trivialKahlerOnticSetup N p₀).projectedFlow t p = U t • p)
        ∧ (∀ (s t : ℝ) (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))),
            U (s + t) • p = (U s * U t) • p)
        ∧ (∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)), U 0 • p = p) := by
  refine projectedFlow_projective_one_parameter_representation
    (trivialKahlerOnticSetup N p₀)
    (trivialKahlerOnticSetup_projUnitary N p₀) ?_ rfl
  intro s t
  rfl

/-- The `exp(-itH)` realizability witness is non-vacuous: the zero generator
`H = 0` (Hermitian) gives the constant unitary family `exp(0) = 1`, a genuine
one-parameter unitary group. Confirms `expNegITH_unitary_group`'s hypotheses
are satisfiable. -/
theorem expNegITH_unitary_group_zero (N : ℕ) :
    (∀ s t : ℝ, schrodingerUnitary (H := (0 : Matrix (Fin N) (Fin N) ℂ))
          Matrix.isHermitian_zero (s + t)
        = schrodingerUnitary Matrix.isHermitian_zero s
            * schrodingerUnitary Matrix.isHermitian_zero t)
      ∧ schrodingerUnitary (H := (0 : Matrix (Fin N) (Fin N) ℂ))
          Matrix.isHermitian_zero 0 = 1 :=
  expNegITH_unitary_group Matrix.isHermitian_zero

end LF4
end CSD
