/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.QuadCoupledFlow

/-!
# The Hamiltonian flow of a ray coupled to five tori

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #389 — the author's programme "From `Σ` to
physical spacetime", milestone M6, step (4) of the plan of 2026-11-14: the manifold, form,
energy, flow and invariant measure of the radar arena of UA-18, which has five pointers.

The arena is `ℂℙᴺ × (T²)⁵`, with the energy

  `𝓗 = −2⟨A⟩ − 2⟨B_A⟩ f(θ₂) − 2⟨B_B⟩ g(ψ₂) − 2⟨B_C⟩ k(χ₂) − 2⟨B_D⟩ l(ξ₂) − 2⟨B_E⟩ r(ζ₂)`.

It is `LF4/PointerStep.lean` applied once more, to the four-torus arena of
`LF4/QuadCoupledFlow.lean`: the form is `stepForm quadForm` (`pentaForm`,
`pentaForm_isSymplectic`) and the energy is `stepEnergy` of the four-torus energy and the ray
observable `−2⟨B_E⟩` (`fiveCoupledEnergy`).

* `PentaModel`, `PentaSigma`, `pentaForm`, `pentaForm_isSymplectic`;
* `quadRayEnergy`, `contMDiff_quadRayEnergy`, `fiveCoupledEnergy`, `fiveCoupledEnergy_apply`,
  `contMDiff_fiveCoupledEnergy`, `fourCoupledEnergy_add_smul_quadRayEnergy`;
* `fiveCoupledFlow`, ★ `fiveCoupledFlow_apply` — **the five-torus flow is a skew product over
  the fifth conserved angle**;
* `fiveCoupledFlow_fst_of_lift_eq_zero`, `fiveCoupledFlow_snd_of_lift_eq_zero` — on a fibre
  where the fifth profile vanishes;
* `pentaMuL`, ★ `pentaMuL_map_fiveCoupledFlow` — **the flow preserves `μ_FS ⊗ vol⁵`**.

## Exact scope

* **One more application of the step theorem.** Nothing here is new mathematics beyond
  `LF4/PointerStep.lean`. No arena indexed by the number of tori is defined.
* **Only the bare arena of UA-18.** The matrices are arbitrary Hermitian matrices on the ray's
  space. The three carriers, the walls, the coincidence projectors, the clock packets and the
  five readings of UA-18 are not defined here, and no record is read.
* **The coupling's form is assumed**, as in #368: each pointer's term is a ray observable times
  a function of that pointer's conserved angle. No moving angle enters the energy and there is
  no term between pointers.
* **The measure statement is invariance only.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-15,
UA-18, UO-16, UD-95, UD-96, UD-122, UD-139); `LF4/PointerStep.lean` (`stepForm`, `stepEnergy`,
`hamiltonianFlow_stepEnergy`, `map_hamiltonianFlow_stepEnergy`, `hamiltonianFlow_congr`);
`LF4/QuadCoupledFlow.lean` (`quadForm`, `fourCoupledEnergy`, `fourCoupledFlow`, `quadMuL`,
`quadMuL_map_fourCoupledFlow`, `threeCoupledEnergy_add_smul_triRayEnergy`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The five-torus arena and its symplectic form -/

/-- The five-torus arena's normed model. -/
abbrev PentaModel (N : ℕ) : Type := QuadModel N × (ℝ × ℝ)

/-- The five-torus arena `ℂℙᴺ × (T²)⁵`. -/
abbrev PentaSigma (N : ℕ) : Type := QuadSigma N × KTorus

/-- **The five-torus arena's symplectic form**: the step over `quadForm`. -/
noncomputable def pentaForm (N : ℕ) :
    DifferentialForm 𝓘(ℝ, PentaModel N) (PentaSigma N) ∞ (Fin 2) ℝ :=
  stepForm (quadForm N)

/-- **`ℂℙᴺ × (T²)⁵` is a symplectic manifold.** -/
theorem pentaForm_isSymplectic (N : ℕ) : (pentaForm N).IsSymplectic :=
  stepForm_isSymplectic (quadForm_isSymplectic N)

/-! ### The energy -/

section Energy

variable {f g k l r : ℝ → ℝ} (A BA BB BC BD BE : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **A ray observable read on the four-torus arena**: `−2⟨C⟩` at the ray. -/
noncomputable def quadRayEnergy (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : QuadSigma N) :
    ℝ :=
  triRayEnergy C p.1

theorem contMDiff_quadRayEnergy (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ContMDiff 𝓘(ℝ, QuadModel N) 𝓘(ℝ, ℝ) ∞ (quadRayEnergy (N := N) C) :=
  (contMDiff_triRayEnergy C).comp
    (Prod.contMDiff_fst_self (E := TriModel N) (F := ℝ × ℝ) (M := TriSigma N) (N := KTorus))

/-- **The five-torus energy**: the step over the four-torus energy. -/
noncomputable def fiveCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1) :
    PentaSigma N → ℝ :=
  stepEnergy (fourCoupledEnergy A BA BB BC BD hf hg hk hl) (quadRayEnergy BE) hr

/-- The five-torus energy, term by term. -/
theorem fiveCoupledEnergy_apply (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (x : CPN (N + 1)) (θ ψ χ ξ ζ : KTorus) :
    fiveCoupledEnergy A BA BB BC BD BE hf hg hk hl hr (((((x, θ), ψ), χ), ξ), ζ)
      = schrodingerHamiltonian A x + schrodingerHamiltonian BA x * hf.lift θ.2
        + schrodingerHamiltonian BB x * hg.lift ψ.2
        + schrodingerHamiltonian BC x * hk.lift χ.2
        + schrodingerHamiltonian BD x * hl.lift ξ.2
        + schrodingerHamiltonian BE x * hr.lift ζ.2 :=
  rfl

/-- The five-torus energy is `C^∞`. -/
theorem contMDiff_fiveCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) :
    ContMDiff 𝓘(ℝ, PentaModel N) 𝓘(ℝ, ℝ) ∞
      (fiveCoupledEnergy A BA BB BC BD BE hf hg hk hl hr) :=
  contMDiff_stepEnergy (contMDiff_fourCoupledEnergy A BA BB BC BD hf hg hk hl hc hcg hck hcl)
    (contMDiff_quadRayEnergy BE) hr hcr

/-- **Adding `c` times the ray observable `−2⟨B_E⟩` to the four-torus energy is replacing `A`
by `A + c B_E`.** -/
theorem fourCoupledEnergy_add_smul_quadRayEnergy (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)
    (c : ℝ) :
    fourCoupledEnergy A BA BB BC BD hf hg hk hl + c • quadRayEnergy BE
      = fourCoupledEnergy (A + ((c : ℝ) : ℂ) • BE) BA BB BC BD hf hg hk hl := by
  funext p
  have h := congrFun (threeCoupledEnergy_add_smul_triRayEnergy A BA BB BC BE hf hg hk c) p.1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fourCoupledEnergy, stepEnergy,
    quadRayEnergy]
  linarith

/-! ### The flow -/

/-- **The flow of the five-torus energy**: the Hamiltonian flow of `fiveCoupledEnergy` for the
form `pentaForm`. -/
noncomputable def fiveCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ) :
    PentaSigma N → PentaSigma N :=
  (pentaForm_isSymplectic N).hamiltonianFlow
    (contMDiff_fiveCoupledEnergy A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr) t

/-- ★ **The five-torus flow is a skew product over the fifth conserved angle.** With `ζ₂`
held, the ray and the first four tori move by the four-torus flow with uncoupled matrix
`A + r(ζ₂) B_E`, the fifth pointer's moving angle advances by `r'(ζ₂)` times the accumulated
`−2⟨B_E⟩` along that orbit, and `ζ₂` is fixed. -/
theorem fiveCoupledFlow_apply (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ) (q : QuadSigma N) (ζ : KTorus) :
    fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t (q, ζ)
      = (fourCoupledFlow (A + ((hr.lift ζ.2 : ℝ) : ℂ) • BE) BA BB BC BD hf hg hk hl hc hcg hck
            hcl t q,
          (ζ.1 + ((hr.deriv_periodic.lift ζ.2 * ∫ u in (0 : ℝ)..t,
              quadRayEnergy BE
                (fourCoupledFlow (A + ((hr.lift ζ.2 : ℝ) : ℂ) • BE) BA BB BC BD hf hg hk hl hc
                  hcg hck hcl u q) : ℝ) : AddCircle (1 : ℝ)), ζ.2)) := by
  have h := hamiltonianFlow_stepEnergy (quadForm_isSymplectic N)
    (contMDiff_fourCoupledEnergy A BA BB BC BD hf hg hk hl hc hcg hck hcl)
    (contMDiff_quadRayEnergy BE) hr hcr t q ζ
  have hflow : (quadForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul
          (contMDiff_fourCoupledEnergy A BA BB BC BD hf hg hk hl hc hcg hck hcl)
          (contMDiff_quadRayEnergy BE) (hr.lift ζ.2))
      = (quadForm_isSymplectic N).hamiltonianFlow
        (contMDiff_fourCoupledEnergy (A + ((hr.lift ζ.2 : ℝ) : ℂ) • BE) BA BB BC BD hf hg hk hl
          hc hcg hck hcl) :=
    hamiltonianFlow_congr (quadForm_isSymplectic N)
      (fourCoupledEnergy_add_smul_quadRayEnergy A BA BB BC BD BE hf hg hk hl (hr.lift ζ.2)) _ _
  simp only [hflow] at h
  exact h

/-- On a fibre where the fifth profile vanishes the ray and the first four pointers move as
on the four-pointer arena. -/
theorem fiveCoupledFlow_fst_of_lift_eq_zero (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)
    (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ)
    (q : QuadSigma N) {ζ : KTorus} (hz : hr.lift ζ.2 = 0) :
    (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t (q, ζ)).1
      = fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t q := by
  rw [fiveCoupledFlow_apply]
  simp only [hz, Complex.ofReal_zero, zero_smul, add_zero]

/-- The fifth pointer on a fibre where its profile vanishes: turned by `r'(ζ₂)` times the
accumulated `−2⟨B_E⟩` along the four-pointer orbit. -/
theorem fiveCoupledFlow_snd_of_lift_eq_zero (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)
    (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ)
    (q : QuadSigma N) {ζ : KTorus} (hz : hr.lift ζ.2 = 0) :
    (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t (q, ζ)).2
      = (ζ.1 + ((hr.deriv_periodic.lift ζ.2 * ∫ u in (0 : ℝ)..t,
          quadRayEnergy BE (fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl u q) : ℝ) :
            AddCircle (1 : ℝ)), ζ.2) := by
  rw [fiveCoupledFlow_apply]
  simp only [hz, Complex.ofReal_zero, zero_smul, add_zero]

/-! ### The preserved measure -/

/-- **The measure of the five-torus arena**: `μ_FS ⊗ vol_{T²}` five times. -/
noncomputable def pentaMuL (p₀ : CPN (N + 1)) : Measure (PentaSigma N) :=
  (quadMuL p₀).prod (volume : Measure KTorus)

variable {A BA BB BC BD BE}

set_option synthInstance.maxSize 4096 in
/-- ★ **The flow of the five-torus energy preserves `μ_FS ⊗ vol⁵`**, for all Hermitian
matrices: the step over the four-torus statement. -/
theorem pentaMuL_map_fiveCoupledFlow (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hBE : BE.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (p₀ : CPN (N + 1)) (t : ℝ) :
    Measure.map (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t)
        (pentaMuL p₀) = pentaMuL p₀ := by
  have h1 : SFinite (echoMuL p₀) := by
    unfold echoMuL
    infer_instance
  have h2 : SFinite (triMuL p₀) := by
    unfold triMuL
    infer_instance
  have h3 : SFinite (quadMuL p₀) := by
    unfold quadMuL
    infer_instance
  refine map_hamiltonianFlow_stepEnergy (quadForm_isSymplectic N)
    (contMDiff_fourCoupledEnergy A BA BB BC BD hf hg hk hl hc hcg hck hcl)
    (contMDiff_quadRayEnergy BE) hr hcr (quadMuL p₀) t fun c => ?_
  rw [hamiltonianFlow_congr (quadForm_isSymplectic N)
    (fourCoupledEnergy_add_smul_quadRayEnergy A BA BB BC BD BE hf hg hk hl c) _
    (contMDiff_fourCoupledEnergy (A + ((c : ℝ) : ℂ) • BE) BA BB BC BD hf hg hk hl hc hcg hck
      hcl)]
  exact quadMuL_map_fourCoupledFlow (isHermitian_add_real_smul hA hBE c) hBA hBB hBC hBD hf hg
    hk hl hc hcg hck hcl p₀ t

end Energy

end LF4
end CSD

end
