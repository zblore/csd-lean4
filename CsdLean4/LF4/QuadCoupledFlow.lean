/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.TriCoupledFlow

/-!
# The Hamiltonian flow of a ray coupled to four tori

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #381 — the author's programme "From `Σ` to
physical spacetime", a prerequisite for M6: an arena on which a clock's pointer that runs
throughout sits beside the gated pointer of #376 and the two region pointers.

The arena is `ℂℙᴺ × T² × T² × T² × T²`, with the energy

  `𝓗 = −2⟨A⟩ − 2⟨B_A⟩ f(θ₂) − 2⟨B_B⟩ g(ψ₂) − 2⟨B_C⟩ k(χ₂) − 2⟨B_D⟩ l(ξ₂)`.

It is `LF4/PointerStep.lean` applied once more, to the three-torus arena of
`LF4/TriCoupledFlow.lean`: the form is `stepForm triForm` (`quadForm`,
`quadForm_isSymplectic`) and the energy is `stepEnergy` of the three-torus energy and the ray
observable `−2⟨B_D⟩` (`fourCoupledEnergy`).

* `QuadModel`, `QuadSigma`, `quadForm`, `quadForm_isSymplectic`;
* `triRayEnergy`, `contMDiff_triRayEnergy`, `fourCoupledEnergy`, `fourCoupledEnergy_apply`,
  `contMDiff_fourCoupledEnergy`, `threeCoupledEnergy_add_smul_triRayEnergy`;
* `fourCoupledFlow`, ★ `fourCoupledFlow_apply` — **the four-torus flow is a skew product over
  the fourth conserved angle**: with `ξ₂` held, the ray and the first three tori move by the
  three-torus flow with uncoupled matrix `A + l(ξ₂) B_D`, and `ξ₁` advances by `l'(ξ₂)` times
  the accumulated `−2⟨B_D⟩` along that orbit;
* `fourCoupledFlow_fst_of_lift_eq_zero`, `fourCoupledFlow_snd_of_lift_eq_zero` — on a fibre
  where the fourth profile vanishes;
* `quadMuL`, ★ `quadMuL_map_fourCoupledFlow` — **the flow preserves
  `μ_FS ⊗ vol ⊗ vol ⊗ vol ⊗ vol`**.

## Exact scope

* **One more application of the step theorem.** Nothing here is new mathematics beyond
  `LF4/PointerStep.lean`; the three-torus arena was the same construction one level down. No
  arena indexed by the number of tori is defined.
* **The coupling's form is assumed**, as in #368: each pointer's term is a ray observable times
  a function of that pointer's conserved angle. No moving angle enters the energy and there is
  no term between pointers.
* **The measure statement is invariance only.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-15,
UA-17, UD-95, UD-96, UD-122); `LF4/PointerStep.lean` (`stepForm`, `stepEnergy`,
`hamiltonianFlow_stepEnergy`, `map_hamiltonianFlow_stepEnergy`, `hamiltonianFlow_congr`);
`LF4/TriCoupledFlow.lean` (`triForm`, `threeCoupledEnergy`, `threeCoupledFlow`, `triMuL`,
`triMuL_map_threeCoupledFlow`, `twoCoupledEnergy_add_smul_echoRayEnergy`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The four-torus arena and its symplectic form -/

/-- The four-torus arena's normed model. -/
abbrev QuadModel (N : ℕ) : Type := TriModel N × (ℝ × ℝ)

/-- The four-torus arena `ℂℙᴺ × T² × T² × T² × T²`. -/
abbrev QuadSigma (N : ℕ) : Type := TriSigma N × KTorus

/-- **The four-torus arena's symplectic form**: the step over `triForm`. -/
noncomputable def quadForm (N : ℕ) :
    DifferentialForm 𝓘(ℝ, QuadModel N) (QuadSigma N) ∞ (Fin 2) ℝ :=
  stepForm (triForm N)

/-- **`ℂℙᴺ × T² × T² × T² × T²` is a symplectic manifold.** -/
theorem quadForm_isSymplectic (N : ℕ) : (quadForm N).IsSymplectic :=
  stepForm_isSymplectic (triForm_isSymplectic N)

/-! ### The energy -/

section Energy

variable {f g k l : ℝ → ℝ} (A BA BB BC BD : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **A ray observable read on the three-torus arena**: `−2⟨C⟩` at the ray. -/
noncomputable def triRayEnergy (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : TriSigma N) :
    ℝ :=
  echoRayEnergy C p.1

theorem contMDiff_triRayEnergy (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ContMDiff 𝓘(ℝ, TriModel N) 𝓘(ℝ, ℝ) ∞ (triRayEnergy (N := N) C) :=
  (contMDiff_echoRayEnergy C).comp
    (Prod.contMDiff_fst_self (E := EchoModel N) (F := ℝ × ℝ) (M := EchoSigma N) (N := KTorus))

/-- **The four-torus energy**: the step over the three-torus energy. -/
noncomputable def fourCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) : QuadSigma N → ℝ :=
  stepEnergy (threeCoupledEnergy A BA BB BC hf hg hk) (triRayEnergy BD) hl

/-- The four-torus energy, term by term. -/
theorem fourCoupledEnergy_apply (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (x : CPN (N + 1))
    (θ ψ χ ξ : KTorus) :
    fourCoupledEnergy A BA BB BC BD hf hg hk hl ((((x, θ), ψ), χ), ξ)
      = schrodingerHamiltonian A x + schrodingerHamiltonian BA x * hf.lift θ.2
        + schrodingerHamiltonian BB x * hg.lift ψ.2
        + schrodingerHamiltonian BC x * hk.lift χ.2
        + schrodingerHamiltonian BD x * hl.lift ξ.2 :=
  rfl

/-- The four-torus energy is `C^∞`. -/
theorem contMDiff_fourCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) :
    ContMDiff 𝓘(ℝ, QuadModel N) 𝓘(ℝ, ℝ) ∞ (fourCoupledEnergy A BA BB BC BD hf hg hk hl) :=
  contMDiff_stepEnergy (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck)
    (contMDiff_triRayEnergy BD) hl hcl

/-- **Adding `c` times the ray observable `−2⟨B_D⟩` to the three-torus energy is replacing `A`
by `A + c B_D`.** -/
theorem threeCoupledEnergy_add_smul_triRayEnergy (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (c : ℝ) :
    threeCoupledEnergy A BA BB BC hf hg hk + c • triRayEnergy BD
      = threeCoupledEnergy (A + ((c : ℝ) : ℂ) • BD) BA BB BC hf hg hk := by
  funext p
  have h := congrFun (twoCoupledEnergy_add_smul_echoRayEnergy A BA BB BD hf hg c) p.1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, threeCoupledEnergy, stepEnergy,
    triRayEnergy]
  linarith

/-! ### The flow -/

/-- **The flow of the four-torus energy**: the Hamiltonian flow of `fourCoupledEnergy` for the
form `quadForm`. -/
noncomputable def fourCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ) :
    QuadSigma N → QuadSigma N :=
  (quadForm_isSymplectic N).hamiltonianFlow
    (contMDiff_fourCoupledEnergy A BA BB BC BD hf hg hk hl hc hcg hck hcl) t

/-- ★ **The four-torus flow is a skew product over the fourth conserved angle.** With `ξ₂`
held, the ray and the first three tori move by the three-torus flow with uncoupled matrix
`A + l(ξ₂) B_D`, the fourth pointer's moving angle advances by `l'(ξ₂)` times the accumulated
`−2⟨B_D⟩` along that orbit, and `ξ₂` is fixed. -/
theorem fourCoupledFlow_apply (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ)
    (q : TriSigma N) (ξ : KTorus) :
    fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t (q, ξ)
      = (threeCoupledFlow (A + ((hl.lift ξ.2 : ℝ) : ℂ) • BD) BA BB BC hf hg hk hc hcg hck t q,
          (ξ.1 + ((hl.deriv_periodic.lift ξ.2 * ∫ u in (0 : ℝ)..t,
              triRayEnergy BD
                (threeCoupledFlow (A + ((hl.lift ξ.2 : ℝ) : ℂ) • BD) BA BB BC hf hg hk hc hcg
                  hck u q) : ℝ) : AddCircle (1 : ℝ)), ξ.2)) := by
  have h := hamiltonianFlow_stepEnergy (triForm_isSymplectic N)
    (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck) (contMDiff_triRayEnergy BD)
    hl hcl t q ξ
  have hflow : (triForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck)
          (contMDiff_triRayEnergy BD) (hl.lift ξ.2))
      = (triForm_isSymplectic N).hamiltonianFlow
        (contMDiff_threeCoupledEnergy (A + ((hl.lift ξ.2 : ℝ) : ℂ) • BD) BA BB BC hf hg hk hc
          hcg hck) :=
    hamiltonianFlow_congr (triForm_isSymplectic N)
      (threeCoupledEnergy_add_smul_triRayEnergy A BA BB BC BD hf hg hk (hl.lift ξ.2)) _ _
  simp only [hflow] at h
  exact h

/-- On a fibre where the fourth profile vanishes the ray and the first three pointers move as
on the three-pointer arena. -/
theorem fourCoupledFlow_fst_of_lift_eq_zero (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (t : ℝ) (q : TriSigma N) {ξ : KTorus} (hz : hl.lift ξ.2 = 0) :
    (fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t (q, ξ)).1
      = threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t q := by
  rw [fourCoupledFlow_apply]
  simp only [hz, Complex.ofReal_zero, zero_smul, add_zero]

/-- The fourth pointer on a fibre where its profile vanishes: turned by `l'(ξ₂)` times the
accumulated `−2⟨B_D⟩` along the three-pointer orbit. -/
theorem fourCoupledFlow_snd_of_lift_eq_zero (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (t : ℝ) (q : TriSigma N) {ξ : KTorus} (hz : hl.lift ξ.2 = 0) :
    (fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t (q, ξ)).2
      = (ξ.1 + ((hl.deriv_periodic.lift ξ.2 * ∫ u in (0 : ℝ)..t,
          triRayEnergy BD (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck u q) : ℝ) :
            AddCircle (1 : ℝ)), ξ.2) := by
  rw [fourCoupledFlow_apply]
  simp only [hz, Complex.ofReal_zero, zero_smul, add_zero]

/-! ### The preserved measure -/

/-- **The measure of the four-torus arena**: `μ_FS ⊗ vol_{T²}` four times. -/
noncomputable def quadMuL (p₀ : CPN (N + 1)) : Measure (QuadSigma N) :=
  (triMuL p₀).prod (volume : Measure KTorus)

variable {A BA BB BC BD}

set_option synthInstance.maxSize 2048 in
/-- ★ **The flow of the four-torus energy preserves `μ_FS ⊗ vol ⊗ vol ⊗ vol ⊗ vol`**, for all
Hermitian matrices: the step over the three-torus statement. -/
theorem quadMuL_map_fourCoupledFlow (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (p₀ : CPN (N + 1)) (t : ℝ) :
    Measure.map (fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t) (quadMuL p₀)
      = quadMuL p₀ := by
  have h1 : SFinite (echoMuL p₀) := by
    unfold echoMuL
    infer_instance
  have h2 : SFinite (triMuL p₀) := by
    unfold triMuL
    infer_instance
  refine map_hamiltonianFlow_stepEnergy (triForm_isSymplectic N)
    (contMDiff_threeCoupledEnergy A BA BB BC hf hg hk hc hcg hck) (contMDiff_triRayEnergy BD)
    hl hcl (triMuL p₀) t fun c => ?_
  rw [hamiltonianFlow_congr (triForm_isSymplectic N)
    (threeCoupledEnergy_add_smul_triRayEnergy A BA BB BC BD hf hg hk c) _
    (contMDiff_threeCoupledEnergy (A + ((c : ℝ) : ℂ) • BD) BA BB BC hf hg hk hc hcg hck)]
  exact triMuL_map_threeCoupledFlow (isHermitian_add_real_smul hA hBD c) hBA hBB hBC hf hg hk
    hc hcg hck p₀ t

end Energy

end LF4
end CSD

end
