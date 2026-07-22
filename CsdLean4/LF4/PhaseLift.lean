/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.ProjectedDynamics
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.PhaseRigidity
import CsdLean4.Mathlib.Analysis.Matrix.StoneC1

/-!
# W5-S1: the projective-to-vector phase lift

**Category:** 3-Programme (CSD dynamics spine, W5 residual S1).

This module discharges the S1 residual of W5 (`ProjectedDynamics.lean`): it
makes the `U(1)` phase cocycle of the projected-flow unitary family a real
object, proves it obeys the 2-cocycle law, and shows that a trivialising
phase function (the coboundary datum) upgrades the ray-level projective
representation to a GENUINE vector-level one-parameter unitary group realising
the projected flow. Wired to the W5-S2 finite-dimensional Stone theorem
(`StoneC1.lean`), this yields the full Schrödinger form: the projected flow is
`p ↦ exp(-itH) • p` for a Hermitian generator `H`.

## What is proved

* `projectedFlow_phase_cocycle`: the cocycle EXISTS. Given a unitary family
  realising a one-parameter projected flow, phase rigidity
  (`Projectivization.exists_unit_smul_of_smul_eq_smul`, the kernel of
  `U(N) → PU(N)` is the circle) extracts `c : ℝ → ℝ → ℂ` with `‖c s t‖ = 1`
  and `U (s+t) = c s t • (U s * U t)` at the matrix level. This names the
  obstruction: the family is a genuine group iff `c` can be killed.
* `phase_cocycle_identity`: any such `c` obeys the 2-cocycle law
  `c s (t+u) * c t u = c (s+t) u * c s t` (associativity, `N ≠ 0`).
* `projectedFlow_phase_lift` (**the S1 theorem**): a phase function
  `b : ℝ → ℂ`, `‖b t‖ = 1`, trivialising the cocycle
  (`c s t * b (s+t) = b s * b t`, i.e. `c = δb` is a coboundary) rescales the
  family to `phaseLiftFamily U b hb : ℝ → unitaryGroup` which (i) realises the
  SAME projected flow (phases act trivially on rays), (ii) satisfies the
  vector-level group law `V (s+t) = V s * V t` on the nose, and (iii) has
  `V 0 = 1`. The projective phase freedom is killed.
* `projectedFlow_schrodinger_form` (**the W5 capstone, S1 × S2**): adding the
  C^1 datum (a skew-Hermitian `A` with `V' t = V t * A`), the S2 Stone theorem
  recovers the generator: there is a Hermitian `H` (namely `i A`) with
  `d.projectedFlow t p = schrodingerUnitary hH t • p`, i.e. the projected CSD
  flow IS `exp(-itH)`-conjugation on rays. This is the Schrödinger form of the
  W-series chain.

## What is HYPOTHESIS (honest posture, load-bearing)

The coboundary datum `b` is the S1 physical/cohomological input, staged
exactly as W3 staged its clopen datum: `H²(ℝ, U(1))` does not vanish
algebraically (antisymmetric bicharacters survive on `ℝ` as a `ℚ`-vector
space), so the bare ray-level group law genuinely does NOT force a vector
lift; killing `c` requires a regularity/cohomological input (Bargmann: for
CONTINUOUS cocycles `H²_cont(ℝ, U(1)) = 0`; formalising that is a named
follow-on, not claimed here). Likewise the C^1 datum in the capstone is the
S2 smoothness posit. Both are surfaced as explicit hypotheses on an explicit
family `U` / cocycle `c` — NOT extracted by choice inside the theorem — so a
caller who owns concrete data can discharge them.

## Non-vacuity

On `trivialKahlerOnticSetup` the whole chain fires end-to-end with the
constant family `U = 1`, trivial cocycle `c = 1`, trivial phase `b = 1`, and
zero generator: `trivialKahlerOnticSetup_phase_lift` (the lift) and
`trivialKahlerOnticSetup_schrodinger_form` (the full Schrödinger form with
`H = 0`). Genuine, not vacuous: every hypothesis is discharged concretely.

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `busch`,
no `sorry`, no `native_decide`, no new axioms. Reuses W5
(`ProjectedDynamics`), the phase-rigidity Mathlib layer (`PhaseRigidity`), and
the W5-S2 Stone theorem (`StoneC1`); nothing is re-proved.
-/

open MeasureTheory
open scoped LinearAlgebra.Projectivization
open scoped Matrix
open scoped Matrix.Norms.L2Operator
open Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ## Part 1: the cocycle exists (the obstruction, named) -/

/-- **The `U(1)` phase cocycle exists.** For a unitary family realising a
one-parameter projected flow, each pair of times yields (by phase rigidity:
the kernel of `U(N) → PU(N)` is the circle) a unit-modulus scalar `c s t`
with `U (s+t) = c s t • (U s * U t)` at the matrix level. The family is a
genuine vector-level group precisely when `c` can be trivialised; `c` is the
named obstruction that residual S1 must kill. -/
theorem projectedFlow_phase_cocycle
    (d : KahlerOnticSetup N)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (hfam : ∀ t p, d.projectedFlow t p = U t • p)
    (hgrp : ∀ s t, d.projectedFlow (s + t)
            = d.projectedFlow s ∘ d.projectedFlow t) :
    ∃ c : ℝ → ℝ → ℂ, (∀ s t, ‖c s t‖ = 1) ∧
      ∀ s t, (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
        = c s t • ((U s : Matrix (Fin N) (Fin N) ℂ)
            * (U t : Matrix (Fin N) (Fin N) ℂ)) := by
  have key : ∀ s t : ℝ, ∃ ph : ℂ, ‖ph‖ = 1 ∧
      (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
        = ph • ((U s : Matrix (Fin N) (Fin N) ℂ)
            * (U t : Matrix (Fin N) (Fin N) ℂ)) := by
    intro s t
    have hray : ∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)),
        U (s + t) • p = (U s * U t) • p := by
      intro p
      rw [← hfam (s + t) p, hgrp s t, Function.comp_apply,
        hfam s (d.projectedFlow t p), hfam t p, mul_smul]
    obtain ⟨ph, h1, h2⟩ :=
      Projectivization.exists_unit_smul_of_smul_eq_smul (U (s + t)) (U s * U t) hray
    exact ⟨ph, h1, h2⟩
  choose c h1 h2 using key
  exact ⟨c, h1, h2⟩

/-- Scalars acting on a fixed unitary are injective (`N ≠ 0`): cancel a
common unitary factor in a scalar identity by multiplying with its star and
evaluating a diagonal entry. -/
private lemma smul_unitary_cancel (hN : N ≠ 0) {x y : ℂ}
    (W : Matrix.unitaryGroup (Fin N) ℂ)
    (h : x • (W : Matrix (Fin N) (Fin N) ℂ)
        = y • (W : Matrix (Fin N) (Fin N) ℂ)) :
    x = y := by
  have hWs : (W : Matrix (Fin N) (Fin N) ℂ)
      * star (W : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self W
  have h2 : x • (1 : Matrix (Fin N) (Fin N) ℂ)
      = y • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    calc x • (1 : Matrix (Fin N) (Fin N) ℂ)
        = x • ((W : Matrix (Fin N) (Fin N) ℂ)
            * star (W : Matrix (Fin N) (Fin N) ℂ)) := by rw [hWs]
      _ = (x • (W : Matrix (Fin N) (Fin N) ℂ))
            * star (W : Matrix (Fin N) (Fin N) ℂ) := (smul_mul_assoc _ _ _).symm
      _ = (y • (W : Matrix (Fin N) (Fin N) ℂ))
            * star (W : Matrix (Fin N) (Fin N) ℂ) := by rw [h]
      _ = y • ((W : Matrix (Fin N) (Fin N) ℂ)
            * star (W : Matrix (Fin N) (Fin N) ℂ)) := smul_mul_assoc _ _ _
      _ = y • (1 : Matrix (Fin N) (Fin N) ℂ) := by rw [hWs]
  have i₀ : Fin N := ⟨0, Nat.pos_of_ne_zero hN⟩
  have h3 := congrFun (congrFun h2 i₀) i₀
  simpa [Matrix.smul_apply, Matrix.one_apply_eq] using h3

/-- **The 2-cocycle law.** Any unit-phase family `c` relating `U (s+t)` to
`U s * U t` obeys `c s (t+u) * c t u = c (s+t) u * c s t` — associativity of
the unitary family forces the cocycle identity. (For `N = 0` the scalar is
not pinned by the matrix equation, hence the `N ≠ 0` hypothesis.) -/
theorem phase_cocycle_identity (hN : N ≠ 0)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (c : ℝ → ℝ → ℂ)
    (hc : ∀ s t, (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
        = c s t • ((U s : Matrix (Fin N) (Fin N) ℂ)
            * (U t : Matrix (Fin N) (Fin N) ℂ)))
    (s t u : ℝ) :
    c s (t + u) * c t u = c (s + t) u * c s t := by
  have hW : ((U s * U t * U u : Matrix.unitaryGroup (Fin N) ℂ)
        : Matrix (Fin N) (Fin N) ℂ)
      = (U s : Matrix (Fin N) (Fin N) ℂ) * (U t : Matrix (Fin N) (Fin N) ℂ)
          * (U u : Matrix (Fin N) (Fin N) ℂ) := rfl
  have e1 : (U (s + (t + u)) : Matrix (Fin N) (Fin N) ℂ)
      = (c s (t + u) * c t u)
          • ((U s * U t * U u : Matrix.unitaryGroup (Fin N) ℂ)
              : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hW, mul_assoc, hc s (t + u), hc t u, mul_smul_comm, smul_smul]
  have e2 : (U (s + t + u) : Matrix (Fin N) (Fin N) ℂ)
      = (c (s + t) u * c s t)
          • ((U s * U t * U u : Matrix.unitaryGroup (Fin N) ℂ)
              : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hW, hc (s + t) u, hc s t, smul_mul_assoc, smul_smul]
  apply smul_unitary_cancel hN (U s * U t * U u)
  rw [← e1, ← e2, add_assoc]

/-! ## Part 2: the phase lift (the S1 theorem) -/

/-- The rescaled family `t ↦ b t • U t`: the candidate vector-level group
obtained by absorbing the phase function `b` into the unitary family. -/
noncomputable def phaseLiftFamily (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (b : ℝ → ℂ) (hb : ∀ t, ‖b t‖ = 1) (t : ℝ) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨b t • (U t : Matrix (Fin N) (Fin N) ℂ),
    Matrix.UnitaryGroup.unit_smul_mem (hb t) (U t).property⟩

@[simp] lemma phaseLiftFamily_val (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (b : ℝ → ℂ) (hb : ∀ t, ‖b t‖ = 1) (t : ℝ) :
    (phaseLiftFamily U b hb t : Matrix (Fin N) (Fin N) ℂ)
      = b t • (U t : Matrix (Fin N) (Fin N) ℂ) := rfl

/-- **The projective-to-vector phase lift (residual S1, discharged on the
coboundary datum).** If the phase cocycle `c` of the unitary family is a
coboundary — trivialised by a unit-phase function `b` via
`c s t * b (s+t) = b s * b t` — then the rescaled family
`V t = b t • U t` is a GENUINE vector-level one-parameter unitary group
(`V (s+t) = V s * V t` and `V 0 = 1` as unitary-group identities, NOT merely
up to phase) realising the same projected flow. The coboundary datum is the
honest S1 residual input: `H²(ℝ, U(1))` does not vanish algebraically, so
some such input is genuinely required (see the module docstring). -/
theorem projectedFlow_phase_lift
    (d : KahlerOnticSetup N)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (hfam : ∀ t p, d.projectedFlow t p = U t • p)
    (c : ℝ → ℝ → ℂ)
    (hc : ∀ s t, (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
        = c s t • ((U s : Matrix (Fin N) (Fin N) ℂ)
            * (U t : Matrix (Fin N) (Fin N) ℂ)))
    (b : ℝ → ℂ) (hb : ∀ t, ‖b t‖ = 1)
    (hcob : ∀ s t, c s t * b (s + t) = b s * b t) :
    (∀ t p, d.projectedFlow t p = phaseLiftFamily U b hb t • p)
      ∧ (∀ s t, phaseLiftFamily U b hb (s + t)
          = phaseLiftFamily U b hb s * phaseLiftFamily U b hb t)
      ∧ phaseLiftFamily U b hb 0 = 1 := by
  have hgrp : ∀ s t, phaseLiftFamily U b hb (s + t)
      = phaseLiftFamily U b hb s * phaseLiftFamily U b hb t := by
    intro s t
    apply Subtype.ext
    show b (s + t) • (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
      = (b s • (U s : Matrix (Fin N) (Fin N) ℂ))
          * (b t • (U t : Matrix (Fin N) (Fin N) ℂ))
    rw [hc s t, smul_smul, smul_mul_smul_comm, ← hcob s t,
      mul_comm (b (s + t)) (c s t)]
  have h0 : phaseLiftFamily U b hb 0 = 1 := by
    have h00 := hgrp 0 0
    rw [add_zero] at h00
    exact (mul_left_cancel (a := phaseLiftFamily U b hb 0)
      (by rw [mul_one]; exact h00)).symm
  refine ⟨fun t p => ?_, hgrp, h0⟩
  rw [hfam t p]
  exact (Projectivization.smul_eq_smul_of_eq_smul
    (phaseLiftFamily_val U b hb t) p).symm

/-! ## Part 3: the W5 capstone (S1 × S2 ⇒ the Schrödinger form) -/

/-- **The W5 capstone: projected CSD flow in Schrödinger form.** Combining the
S1 coboundary datum (`b` trivialises the phase cocycle `c`) with the S2 C^1
datum (the lifted family solves `V' = V * A` for a skew-Hermitian generator
`A`), the finite-dimensional Stone theorem recovers the Hermitian generator:
there is a Hermitian `H` (namely `i A`) with

    `d.projectedFlow t p = schrodingerUnitary hH t • p`,

i.e. the projected flow IS conjugation by `exp(-itH)` on rays — the
Schrödinger form of the W-series chain. Both data are explicit physical
inputs (S1 cohomological, S2 smoothness), staged as hypotheses on an explicit
family, exactly as W3 staged its clopen datum. -/
theorem projectedFlow_schrodinger_form
    (d : KahlerOnticSetup N)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (hfam : ∀ t p, d.projectedFlow t p = U t • p)
    (c : ℝ → ℝ → ℂ)
    (hc : ∀ s t, (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
        = c s t • ((U s : Matrix (Fin N) (Fin N) ℂ)
            * (U t : Matrix (Fin N) (Fin N) ℂ)))
    (b : ℝ → ℂ) (hb : ∀ t, ‖b t‖ = 1)
    (hcob : ∀ s t, c s t * b (s + t) = b s * b t)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : star A = -A)
    (hderiv : ∀ t, HasDerivAt
        (fun τ : ℝ => (phaseLiftFamily U b hb τ : Matrix (Fin N) (Fin N) ℂ))
        ((phaseLiftFamily U b hb t : Matrix (Fin N) (Fin N) ℂ) * A) t) :
    ∃ H : Matrix (Fin N) (Fin N) ℂ, ∃ hH : H.IsHermitian,
      ∀ t p, d.projectedFlow t p = schrodingerUnitary hH t • p := by
  obtain ⟨hact, hgrp, h0⟩ := projectedFlow_phase_lift d U hfam c hc b hb hcob
  have h0' : (phaseLiftFamily U b hb 0 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [h0]
    rfl
  have hexp := CSD.StoneC1.eq_exp_of_hasDeriv A
    (fun τ : ℝ => (phaseLiftFamily U b hb τ : Matrix (Fin N) (Fin N) ℂ))
    hderiv h0'
  have hH : (Complex.I • A).IsHermitian := by
    show (Complex.I • A)ᴴ = Complex.I • A
    rw [Matrix.conjTranspose_smul]
    rw [show star Complex.I = -Complex.I by simp]
    rw [show Aᴴ = -A from hA]
    module
  refine ⟨Complex.I • A, hH, fun t p => ?_⟩
  rw [hact t p]
  congr 1
  apply Subtype.ext
  have hgen : schrodingerGen (Complex.I • A) t = t • A := by
    unfold schrodingerGen
    rw [smul_smul]
    rw [show -(t : ℂ) * Complex.I * Complex.I = (t : ℂ) by
      rw [mul_assoc, Complex.I_mul_I]; ring]
    ext i j
    simp [Complex.real_smul]
  show b t • (U t : Matrix (Fin N) (Fin N) ℂ)
      = NormedSpace.exp (schrodingerGen (Complex.I • A) t)
  rw [hgen]
  exact hexp t

/-! ## The Σ-level capstone: the ontic flow projects to Schrödinger evolution

The ray-level `projectedFlow_schrodinger_form` above is a statement about
`d.projectedFlow` alone. This next theorem is the one that makes the sector
substrate LOAD-BEARING: it consumes `d.projectable` (the descent equation
`pi (flow t x) = projectedFlow t (pi x)`) together with the ontic flow
`d.flow` and the projection `d.pi` to conclude that the DETERMINISTIC Σ-flow,
pushed to ray space through `π`, is `exp(-itH)`-conjugation. This is the honest
"Schrödinger dynamics from the posited ontic sector" statement — the whole
point of packaging the dynamics as a `KahlerOnticSetup`. -/

/-- **The Σ-level Schrödinger capstone (PROVED; the substrate-consuming form).**
Under the same S1 (coboundary) + S2 (C¹) data as `projectedFlow_schrodinger_form`,
the projection of the deterministic ontic flow is a one-parameter unitary
(Schrödinger) evolution on rays:

    `∀ t x, d.pi (d.flow t x) = exp(-i t H) • d.pi x`,

for a Hermitian generator `H`. Unlike the ray-level form, this GENUINELY
consumes the sector fields `d.projectable`, `d.flow`, `d.pi`: it is the
statement that the CSD ontic dynamics on `Σ`, viewed through the operational
projection `π`, IS finite-dimensional Schrödinger evolution. It is the forward
direction of the dynamics spine landed on the substrate, not merely on the
already-projected map. -/
theorem sigmaFlow_schrodinger_form
    (d : KahlerOnticSetup N)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (hfam : ∀ t p, d.projectedFlow t p = U t • p)
    (c : ℝ → ℝ → ℂ)
    (hc : ∀ s t, (U (s + t) : Matrix (Fin N) (Fin N) ℂ)
        = c s t • ((U s : Matrix (Fin N) (Fin N) ℂ)
            * (U t : Matrix (Fin N) (Fin N) ℂ)))
    (b : ℝ → ℂ) (hb : ∀ t, ‖b t‖ = 1)
    (hcob : ∀ s t, c s t * b (s + t) = b s * b t)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : star A = -A)
    (hderiv : ∀ t, HasDerivAt
        (fun τ : ℝ => (phaseLiftFamily U b hb τ : Matrix (Fin N) (Fin N) ℂ))
        ((phaseLiftFamily U b hb t : Matrix (Fin N) (Fin N) ℂ) * A) t) :
    ∃ H : Matrix (Fin N) (Fin N) ℂ, ∃ hH : H.IsHermitian,
      ∀ t x, d.pi (d.flow t x) = schrodingerUnitary hH t • d.pi x := by
  obtain ⟨H, hH, hray⟩ :=
    projectedFlow_schrodinger_form d U hfam c hc b hb hcob A hA hderiv
  refine ⟨H, hH, fun t x => ?_⟩
  rw [d.projectable t x, hray t (d.pi x)]

/-! ## Non-vacuity on the `trivialKahlerOnticSetup` witness -/

/-- The phase lift FIRES on the inhabitation witness: the constant family
`U = 1` realises the identity flow with trivial cocycle `c = 1`, trivialised
by the trivial phase `b = 1`; the lifted family is a genuine vector-level
one-parameter unitary group. Confirms the S1 hypotheses are jointly
satisfiable and the conclusion genuine. -/
theorem trivialKahlerOnticSetup_phase_lift
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∃ V : ℝ → Matrix.unitaryGroup (Fin N) ℂ,
      (∀ t p, (trivialKahlerOnticSetup N p₀).projectedFlow t p = V t • p)
        ∧ (∀ s t, V (s + t) = V s * V t) ∧ V 0 = 1 := by
  obtain ⟨hact, hgrp, h0⟩ :=
    projectedFlow_phase_lift (trivialKahlerOnticSetup N p₀)
      (fun _ => 1) (fun _ p => (one_smul _ p).symm)
      (fun _ _ => 1) (fun _ _ => by simp)
      (fun _ => 1) (fun _ => norm_one) (fun _ _ => rfl)
  exact ⟨_, hact, hgrp, h0⟩

/-- The full Schrödinger form FIRES on the inhabitation witness: with the
constant family, trivial cocycle/phase, and zero generator (`A = 0`, so
`H = i·0 = 0` Hermitian), the capstone concludes the identity flow is
`exp(-it·0) = 1` conjugation on rays. Confirms every capstone hypothesis
(S1 coboundary + S2 C^1) is concretely dischargeable. -/
theorem trivialKahlerOnticSetup_schrodinger_form
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∃ H : Matrix (Fin N) (Fin N) ℂ, ∃ hH : H.IsHermitian,
      ∀ t p, (trivialKahlerOnticSetup N p₀).projectedFlow t p
        = schrodingerUnitary hH t • p := by
  apply projectedFlow_schrodinger_form (trivialKahlerOnticSetup N p₀)
    (fun _ => 1) (fun _ p => (one_smul _ p).symm)
    (fun _ _ => 1) (fun _ _ => by simp)
    (fun _ => 1) (fun _ => norm_one) (fun _ _ => rfl)
    (0 : Matrix (Fin N) (Fin N) ℂ) (by simp)
  intro t
  have h1 : (fun τ : ℝ =>
      (phaseLiftFamily (N := N) (fun _ => 1) (fun _ => 1) (fun _ => norm_one) τ
        : Matrix (Fin N) (Fin N) ℂ)) = fun _ => 1 := by
    funext τ
    rw [phaseLiftFamily_val, one_smul]
    rfl
  rw [h1, mul_zero]
  exact hasDerivAt_const t 1

/-- The Σ-level capstone FIRES on the inhabitation witness: the identity ontic
flow (`flow t = id`, `pi = id`, `projectable` by `rfl`) projects to the
identity `exp(-it·0) = 1` on rays. Confirms the substrate-consuming form's
hypotheses are jointly dischargeable and the descent equation genuinely closes
the loop (`d.pi (d.flow t x) = x = 1 • x`). -/
theorem trivialKahlerOnticSetup_sigmaFlow_schrodinger_form
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∃ H : Matrix (Fin N) (Fin N) ℂ, ∃ hH : H.IsHermitian,
      ∀ t x, (trivialKahlerOnticSetup N p₀).pi
          ((trivialKahlerOnticSetup N p₀).flow t x)
        = schrodingerUnitary hH t • (trivialKahlerOnticSetup N p₀).pi x := by
  apply sigmaFlow_schrodinger_form (trivialKahlerOnticSetup N p₀)
    (fun _ => 1) (fun _ p => (one_smul _ p).symm)
    (fun _ _ => 1) (fun _ _ => by simp)
    (fun _ => 1) (fun _ => norm_one) (fun _ _ => rfl)
    (0 : Matrix (Fin N) (Fin N) ℂ) (by simp)
  intro t
  have h1 : (fun τ : ℝ =>
      (phaseLiftFamily (N := N) (fun _ => 1) (fun _ => 1) (fun _ => norm_one) τ
        : Matrix (Fin N) (Fin N) ℂ)) = fun _ => 1 := by
    funext τ
    rw [phaseLiftFamily_val, one_smul]
    rfl
  rw [h1, mul_zero]
  exact hasDerivAt_const t 1

end LF4
end CSD
