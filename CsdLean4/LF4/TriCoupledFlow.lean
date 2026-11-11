/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PointerStep

/-!
# The Hamiltonian flow of a ray coupled to three tori

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #368 — the author's programme "From `Σ` to
physical spacetime", the arena M6 needs: a clock's pointer and two detectors' pointers under one
flow. Remainder (a) of #367.

The arena is `ℂℙᴺ × T² × T² × T²`, with the energy

  `𝓗(x, θ, ψ, χ) = −2⟨A⟩ − 2⟨B_A⟩ f(θ₂) − 2⟨B_B⟩ g(ψ₂) − 2⟨B_C⟩ k(χ₂)`.

It is not built by hand. It is `LF4/PointerStep.lean` applied to the two-torus arena of
`EchoCoupledFlow.lean`: the form is `stepForm echoForm` (`triForm`, `triForm_isSymplectic`), and
the energy is `stepEnergy` of the two-torus energy and the ray observable `−2⟨B_C⟩`
(`threeCoupledEnergy`).

**The flow.** `threeCoupledFlow` is the Hamiltonian flow of that energy. Adding `c` times the ray
observable `−2⟨B_C⟩` to the two-torus energy is replacing `A` by `A + c B_C`
(`twoCoupledEnergy_add_smul_echoRayEnergy`). So the step theorem gives:

  `Φ_t(q, χ) = (Φ²_t[A + k(χ₂) B_C](q), (χ₁ + k'(χ₂) ∫₀ᵗ (−2⟨B_C⟩) du, χ₂))`,

with `Φ²[A']` the two-torus flow with uncoupled matrix `A'` and the integral taken along its
orbit (`threeCoupledFlow_apply`). Unfolding the two-torus closed form: the ray moves by the
Schrödinger unitary of `A + f(θ₂) B_A + g(ψ₂) B_B + k(χ₂) B_C`, each of the three first angles
advances by its profile's derivative times the accumulated `−2⟨B⟩` of its own operator along that
one orbit, and the three second angles are fixed (`threeCoupledFlow_closed`).

**The measure.** `triMuL` is `μ_FS ⊗ vol_{T²} ⊗ vol_{T²} ⊗ vol_{T²}`, and the flow preserves it
(`triMuL_map_threeCoupledFlow`), from the two-torus statement and the step.

## Exact scope

* **Three tori, by one application of the step.** A fourth is one more application. No arena
  with a variable number of tori is defined.
* **The couplings' form is assumed**, as for one and two tori: each torus is coupled to one
  Hermitian operator on the ray through its second angle only, and there is no term between the
  tori. The three second angles are conserved.
* **The measure statement is read off the closed form.** The top-form measure of `triForm` is
  not identified with `triMuL`.
* **No physics here.** Which operators the three tori are coupled to, and what is read on them,
  is in `RecordLayer`.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-13,
UA-15, UD-95, UD-96); `LF4/PointerStep.lean` (`stepForm`, `stepEnergy`,
`hamiltonianFlow_stepEnergy`, `map_hamiltonianFlow_stepEnergy`, `hamiltonianFlow_congr`);
`LF4/EchoCoupledFlow.lean` (`echoForm`, `twoCoupledEnergy`, `twoCoupledMatrix`, `twoAccumA`,
`twoAccumB`); `LF4/EchoVolume.lean` (`twoCoupledFlow`, `twoCoupledFlow_apply`, `echoMuL`,
`echoMuL_map_twoCoupledFlow`); `LF4/ArenaCoupledFlow.lean` (`schrodingerHamiltonian_add`,
`schrodingerHamiltonian_real_smul`, `isHermitian_add_real_smul`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The three-torus arena and its symplectic form -/

/-- The three-torus arena's normed model. -/
abbrev TriModel (N : ℕ) : Type := EchoModel N × (ℝ × ℝ)

/-- The three-torus arena `ℂℙᴺ × T² × T² × T²`. -/
abbrev TriSigma (N : ℕ) : Type := EchoSigma N × KTorus

/-- **The three-torus arena's symplectic form**: the step over `echoForm`. -/
noncomputable def triForm (N : ℕ) :
    DifferentialForm 𝓘(ℝ, TriModel N) (TriSigma N) ∞ (Fin 2) ℝ :=
  stepForm (echoForm N)

/-- ★ **`ℂℙᴺ × T² × T² × T²` is a symplectic manifold.** -/
theorem triForm_isSymplectic (N : ℕ) : (triForm N).IsSymplectic :=
  stepForm_isSymplectic (echoForm_isSymplectic N)

/-! ### The energy -/

section Energy

variable {f g k : ℝ → ℝ} (A BA BB BC : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **A ray observable read on the two-torus arena**: `−2⟨C⟩` at the ray. -/
noncomputable def echoRayEnergy (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : EchoSigma N) :
    ℝ :=
  schrodingerHamiltonian C p.1.1

theorem contMDiff_echoRayEnergy (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ContMDiff 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ) ∞ (echoRayEnergy (N := N) C) :=
  (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) C)).comp
    (Prod.contMDiff_fst_self (E := ArenaModel N) (F := ℝ × ℝ) (M := KSigma (N + 1))
      (N := KTorus))

/-- **The three-torus energy**
`−2⟨A⟩ − 2⟨B_A⟩ f(θ₂) − 2⟨B_B⟩ g(ψ₂) − 2⟨B_C⟩ k(χ₂)`: the step over the two-torus energy. -/
noncomputable def threeCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) : TriSigma N → ℝ :=
  stepEnergy (twoCoupledEnergy A BA BB hf hg) (echoRayEnergy BC) hk

/-- The three-torus energy, term by term. -/
theorem threeCoupledEnergy_apply (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (x : CPN (N + 1)) (θ ψ χ : KTorus) :
    threeCoupledEnergy A BA BB BC hf hg hk (((x, θ), ψ), χ)
      = schrodingerHamiltonian A x + schrodingerHamiltonian BA x * hf.lift θ.2
        + schrodingerHamiltonian BB x * hg.lift ψ.2
        + schrodingerHamiltonian BC x * hk.lift χ.2 :=
  rfl

/-- The three-torus energy is `C^∞`. -/
theorem contMDiff_threeCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) :
    ContMDiff 𝓘(ℝ, TriModel N) 𝓘(ℝ, ℝ) ∞ (threeCoupledEnergy A BA BB BC hf hg hk) :=
  contMDiff_stepEnergy (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg)
    (contMDiff_echoRayEnergy BC) hk hck

/-- ★ **Adding `c` times the ray observable `−2⟨B_C⟩` to the two-torus energy is replacing `A`
by `A + c B_C`.** -/
theorem twoCoupledEnergy_add_smul_echoRayEnergy (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (c : ℝ) :
    twoCoupledEnergy A BA BB hf hg + c • echoRayEnergy BC
      = twoCoupledEnergy (A + ((c : ℝ) : ℂ) • BC) BA BB hf hg := by
  funext p
  have h1 := congrFun (schrodingerHamiltonian_add (N := N) A (((c : ℝ) : ℂ) • BC)) p.1.1
  have h2 := congrFun (schrodingerHamiltonian_real_smul (N := N) c BC) p.1.1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, twoCoupledEnergy, coupledEnergy,
    echoRayEnergy]
  rw [h1, h2]
  ring

/-! ### The flow -/

/-- **The flow of the three-torus energy** on `ℂℙᴺ × T² × T² × T²`: the Hamiltonian flow of
`threeCoupledEnergy` for the form `triForm`. -/
noncomputable def threeCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) : TriSigma N → TriSigma N :=
  (triForm_isSymplectic N).hamiltonianFlow
    (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck) t

theorem continuous_threeCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) :
    Continuous (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t) :=
  (triForm_isSymplectic N).continuous_hamiltonianFlow _ t

set_option synthInstance.maxSize 1024 in
theorem measurable_threeCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) :
    Measurable (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t) :=
  (continuous_threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t).measurable

theorem threeCoupledFlow_zero (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (x : TriSigma N) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck 0 x = x :=
  integralFlow_zero ((triForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
    (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck)) x

/-- The flow is a one-parameter group. -/
theorem threeCoupledFlow_add (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (s t : ℝ) (x : TriSigma N) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck (s + t) x
      = threeCoupledFlow A BA BB BC hf hg hk hc hcg hck s
          (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t x) :=
  integralFlow_add ((triForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
    (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck)) s t x

/-- ★★★ **The three-torus flow is a skew product over the third conserved angle.** With `χ₂`
held, the ray and the first two tori move by the two-torus flow with uncoupled matrix
`A + k(χ₂) B_C`, the third pointer's moving angle advances by `k'(χ₂)` times the accumulated
`−2⟨B_C⟩` along that orbit, and `χ₂` is fixed. -/
theorem threeCoupledFlow_apply (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (q : EchoSigma N) (χ : KTorus) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (q, χ)
      = (twoCoupledFlow (A + ((hk.lift χ.2 : ℝ) : ℂ) • BC) BA BB hf hg hc hcg t q,
          (χ.1 + ((hk.deriv_periodic.lift χ.2 * ∫ u in (0 : ℝ)..t,
              schrodingerHamiltonian BC
                (twoCoupledFlow (A + ((hk.lift χ.2 : ℝ) : ℂ) • BC) BA BB hf hg hc hcg u
                  q).1.1 : ℝ) : AddCircle (1 : ℝ)), χ.2)) := by
  have h := hamiltonianFlow_stepEnergy (echoForm_isSymplectic N)
    (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg) (contMDiff_echoRayEnergy BC) hk hck t q χ
  have hflow : (echoForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg)
          (contMDiff_echoRayEnergy BC) (hk.lift χ.2))
      = (echoForm_isSymplectic N).hamiltonianFlow
        (contMDiff_twoCoupledEnergy (A + ((hk.lift χ.2 : ℝ) : ℂ) • BC) BA BB hf hg hc hcg) :=
    hamiltonianFlow_congr (echoForm_isSymplectic N)
      (twoCoupledEnergy_add_smul_echoRayEnergy A BA BB BC hf hg (hk.lift χ.2)) _ _
  simp only [hflow] at h
  exact h

variable {A BA BB BC}

/-- ★★★ **The three-torus flow in closed form.** The ray moves by the Schrödinger unitary of
`A + f(θ₂) B_A + g(ψ₂) B_B + k(χ₂) B_C`; `θ₁`, `ψ₁`, `χ₁` advance by `f'(θ₂)`, `g'(ψ₂)`, `k'(χ₂)`
times the accumulated `−2⟨B_A⟩`, `−2⟨B_B⟩`, `−2⟨B_C⟩` along that one orbit; `θ₂`, `ψ₂`, `χ₂` are
fixed. -/
theorem threeCoupledFlow_closed (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (t : ℝ) (x : CPN (N + 1)) (θ ψ χ : KTorus) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (((x, θ), ψ), χ)
      = (((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian
              (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) t • x,
            (θ.1 + ((hf.deriv_periodic.lift θ.2 * twoAccumA
                (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
              AddCircle (1 : ℝ)), θ.2)),
           (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * twoAccumB
                (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
              AddCircle (1 : ℝ)), ψ.2)),
          (χ.1 + ((hk.deriv_periodic.lift χ.2 * ∫ u in (0 : ℝ)..t,
              schrodingerHamiltonian BC (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian
                (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) u • x) :
                ℝ) : AddCircle (1 : ℝ)), χ.2)) := by
  rw [threeCoupledFlow_apply]
  simp only [twoCoupledFlow_apply (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg
    hc hcg]

/-! ### The preserved measure -/

/-- **The measure of the three-torus arena**: `μ_FS ⊗ vol_{T²} ⊗ vol_{T²} ⊗ vol_{T²}`. -/
noncomputable def triMuL (p₀ : CPN (N + 1)) : Measure (TriSigma N) :=
  (echoMuL p₀).prod (volume : Measure KTorus)

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The flow of the three-torus energy preserves
`μ_FS ⊗ vol_{T²} ⊗ vol_{T²} ⊗ vol_{T²}`**, for every `N` and all Hermitian matrices: the step
over the two-torus statement. -/
theorem triMuL_map_threeCoupledFlow (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (p₀ : CPN (N + 1)) (t : ℝ) :
    Measure.map (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t) (triMuL p₀) = triMuL p₀ := by
  have : SFinite (echoMuL p₀) := by
    unfold echoMuL
    infer_instance
  refine map_hamiltonianFlow_stepEnergy (echoForm_isSymplectic N)
    (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg) (contMDiff_echoRayEnergy BC) hk hck
    (echoMuL p₀) t fun c => ?_
  rw [hamiltonianFlow_congr (echoForm_isSymplectic N)
    (twoCoupledEnergy_add_smul_echoRayEnergy A BA BB BC hf hg c) _
    (contMDiff_twoCoupledEnergy (A + ((c : ℝ) : ℂ) • BC) BA BB hf hg hc hcg)]
  exact echoMuL_map_twoCoupledFlow (isHermitian_add_real_smul hA hBC c) hBA hBB hf hg hc hcg p₀ t

end Energy

end LF4
end CSD

end
