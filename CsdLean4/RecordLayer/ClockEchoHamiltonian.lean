/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.CrossCoupledFlow
public import CsdLean4.RecordLayer.ClockEchoCoupling
public import CsdLean4.RecordLayer.EchoHamiltonian

/-!
# The coupled clock and echo is a Hamiltonian flow

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #225, the generation half of #212.

#212 built the coupled device's dynamics as data on `ClockEchoArena`: the echo's step, and the clock's
step with its carrier detuned at `A` by the echo's pointer. Read on
`Σ = (ℂℙ³ × T² × T²) × (ℂℙ³ × T²)` through the index bridge of #195, it is the Hamiltonian flow, for
the symplectic form `echoForm ⊕ arenaForm` of `LF4/CrossCoupledFlow.lean`, of

  `−(2/ħ)(J⟨X⟩ + g_A f_A(θ₂ᴬ) n_A + g_B f_B(θ₂ᴮ) n_B) − (2/ħ)(J_c⟨X_c⟩ + g_c f_c(θ₂ᴬ) n_{A,c} + g f(θ₂ʰ) n_{B,c})`,

which is `−(2/ħ)` times #212's joint energy, cross term `g_c f_c(θ₂ᴬ) n_{A,c}` included.

* `coupledToSigma`, `crossView_coupledToSigma` — the arena read on `Σ`; the cross view of the
  transported point is the transported clock's view;
* `coupledEnergySigma`, `contMDiff_coupledEnergySigma`, ★★ `coupledEnergySigma_eq` — **the
  Hamiltonian is `−(2/ħ)` times #212's joint energy**;
* ★★★ `hamiltonianFlow_coupledFlow` — **the coupled flow is the Hamiltonian flow of its energy**:
  pointer `A`'s angle advanced by the echo's accumulation plus the clock carrier's is exactly what
  the cross term's field prescribes (`echoAmountA_eq` at the echo and at the clock's view);
* `measurable_coupledToSigma`, ★ `map_hamiltonianFlow_coupledFlow` — Liouville, inherited from #212
  through the identification;
* ★★★ `coupled_hamiltonian` — the package.

With `RecordLayer/ClockEchoCoupling.lean` (#212) this closes the coupled device the way
`RecordLayer/EchoHamiltonian.lean` closed the uncoupled echo (#202): dynamics, records and budget
there, generation here. **No universal `c`, no Lorentz invariance**; the #187 and #190 headers stand.

References: `specs/BACKLOG.md` #225, #212, #202, #195, #39; `LF4/CrossCoupledFlow.lean`,
`RecordLayer/EchoHamiltonian.lean` (`echoToSigma`, `echoEnergySigma_eq`,
`arenaEquiv_twoDetuned_arenaFlow`, `echoAmountA_eq`, `echoAmountB_eq`),
`RecordLayer/ClockEchoCoupling.lean` (`coupledFlow`, `clockView`, `coupledEnergy`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

section Coupled

variable (J ħ : ℝ) (A B : PointerCoupling) (Jc : ℝ) (Cc C : PointerCoupling)

/-! ### The coupled device read on `Σ` -/

/-- The coupled device's arena read on `Σ = (ℂℙ³ × T² × T²) × (ℂℙ³ × T²)`: the echo through
`echoToSigma`, the clock's carrier through the index bridge, the hand as it is. -/
noncomputable def coupledToSigma (x : ClockEchoArena) : CrossSigma 3 3 :=
  (echoToSigma x.1, (arenaEquiv 2 2 x.2.1, x.2.2))

/-- **The cross view of the transported point is the transported clock's view.** -/
theorem crossView_coupledToSigma (x : ClockEchoArena) :
    crossView (coupledToSigma x) = echoToSigma (clockView x) := rfl

/-- ★ **The coupled device's Hamiltonian on `Σ`**: the echo's
`−(2/ħ)(J⟨X⟩ + g_A f_A(θ₂ᴬ) n_A + g_B f_B(θ₂ᴮ) n_B)` plus the clock's
`−(2/ħ)(J_c⟨X_c⟩ + g_c f_c(θ₂ᴬ) n_{A,c} + g f(θ₂ʰ) n_{B,c})`, whose middle term couples the clock's
ray to the echo's pointer `A`. -/
noncomputable def coupledEnergySigma : CrossSigma 3 3 → ℝ :=
  crossEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) (hamA Jc ħ) (hamOccA Cc.g ħ) (hamB C.g ħ)
    A.periodic B.periodic Cc.periodic C.periodic

theorem contMDiff_coupledEnergySigma (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f)
    (hcCc : ContDiff ℝ ∞ Cc.f) (hcC : ContDiff ℝ ∞ C.f) :
    ContMDiff 𝓘(ℝ, CrossModel 3 3) 𝓘(ℝ, ℝ) ∞ (coupledEnergySigma J ħ A B Jc Cc C) :=
  contMDiff_crossEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) (hamA Jc ħ) (hamOccA Cc.g ħ)
    (hamB C.g ħ) A.periodic B.periodic Cc.periodic C.periodic hcA hcB hcCc hcC

/-- ★★ **The Hamiltonian is `−(2/ħ)` times #212's joint energy**, cross term included. -/
theorem coupledEnergySigma_eq (x : ClockEchoArena) :
    coupledEnergySigma J ħ A B Jc Cc C (coupledToSigma x)
      = -(2 / ħ) * coupledEnergy J A B Jc Cc C x := by
  show echoEnergySigma J ħ A B (echoToSigma x.1) + echoEnergySigma Jc ħ Cc C (echoToSigma (clockView x))
    = _
  rw [echoEnergySigma_eq, echoEnergySigma_eq, coupledEnergy]
  ring

/-! ### The identification -/

/-- ★★★ **The coupled clock-and-echo flow is the Hamiltonian flow of its energy.** Read on
`Σ = (ℂℙ³ × T² × T²) × (ℂℙ³ × T²)`, #212's `coupledFlow` is `hamiltonianFlow (coupledEnergySigma)`
for the symplectic form `echoForm ⊕ arenaForm`: pointer `A`'s angle is advanced by the echo's
accumulation and the clock carrier's, as the cross term prescribes. -/
theorem hamiltonianFlow_coupledFlow (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f)
    (hcCc : ContDiff ℝ ∞ Cc.f) (hcC : ContDiff ℝ ∞ C.f) (t : ℝ) (x : ClockEchoArena) :
    (crossForm_isSymplectic 3 3).hamiltonianFlow
        (contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC) t (coupledToSigma x)
      = coupledToSigma (coupledFlow J ħ A B Jc Cc C t x) := by
  show (crossForm_isSymplectic 3 3).hamiltonianFlow
      (contMDiff_crossEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) (hamA Jc ħ) (hamOccA Cc.g ħ)
        (hamB C.g ħ) A.periodic B.periodic Cc.periodic C.periodic hcA hcB hcCc hcC) t
      (((arenaEquiv 2 2 x.1.1, x.1.2.1), x.1.2.2), (arenaEquiv 2 2 x.2.1, x.2.2)) = _
  rw [hamiltonianFlow_crossEnergy (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ)
    (hamB_isHermitian B.g ħ) (hamA_isHermitian Jc ħ) (hamOccA_isHermitian Cc.g ħ)
    (hamB_isHermitian C.g ħ) A.periodic B.periodic Cc.periodic C.periodic hcA hcB hcCc hcC]
  refine Prod.ext (Prod.ext (Prod.ext ?_ (Prod.ext ?_ rfl)) (Prod.ext ?_ rfl))
    (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact (arenaEquiv_twoDetuned_arenaFlow J ħ A B _ _ t x.1.1).symm
  · show x.1.2.1.1 + (((A.periodic.deriv_periodic.lift x.1.2.1.2
          * twoAccumA (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ)
            A.periodic B.periodic x.1.2.1.2 x.1.2.2.2 (arenaEquiv 2 2 x.1.1) t
        + Cc.periodic.deriv_periodic.lift x.1.2.1.2
          * twoAccumA (hamA_isHermitian Jc ħ) (hamOccA_isHermitian Cc.g ħ)
            (hamB_isHermitian C.g ħ) Cc.periodic C.periodic x.1.2.1.2 x.2.2.2
            (arenaEquiv 2 2 x.2.1) t : ℝ)) : AddCircle (1 : ℝ))
      = x.1.2.1.1 + ((echoAmountA J ħ A B t x.1 : ℝ) : AddCircle (1 : ℝ))
        + ((echoAmountA Jc ħ Cc C t (clockView x) : ℝ) : AddCircle (1 : ℝ))
    rw [echoAmountA_eq J ħ A B x.1 t, ← echoAmountA_eq Jc ħ Cc C (clockView x) t, AddCircle.coe_add,
      add_assoc]
    rfl
  · show x.1.2.2.1 + (((B.periodic.deriv_periodic.lift x.1.2.2.2
          * twoAccumB (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ)
            A.periodic B.periodic x.1.2.1.2 x.1.2.2.2 (arenaEquiv 2 2 x.1.1) t : ℝ)) :
          AddCircle (1 : ℝ))
      = x.1.2.2.1 + ((echoAmountB J ħ A B t x.1 : ℝ) : AddCircle (1 : ℝ))
    rw [echoAmountB_eq J ħ A B x.1 t]
  · exact (arenaEquiv_twoDetuned_arenaFlow Jc ħ Cc C _ _ t x.2.1).symm
  · show x.2.2.1 + (((C.periodic.deriv_periodic.lift x.2.2.2
          * twoAccumB (hamA_isHermitian Jc ħ) (hamOccA_isHermitian Cc.g ħ)
            (hamB_isHermitian C.g ħ) Cc.periodic C.periodic x.1.2.1.2 x.2.2.2
            (arenaEquiv 2 2 x.2.1) t : ℝ)) : AddCircle (1 : ℝ))
      = x.2.2.1 + ((echoAmountB Jc ħ Cc C t (clockView x) : ℝ) : AddCircle (1 : ℝ))
    rw [← echoAmountB_eq Jc ħ Cc C (clockView x) t]
    rfl

theorem measurable_coupledToSigma : Measurable coupledToSigma := by
  have he : Measurable fun x : ClockEchoArena => arenaEquiv 2 2 x.1.1 :=
    ((continuous_arenaEquiv 2 2).comp continuous_fst.fst).measurable
  have hc : Measurable fun x : ClockEchoArena => arenaEquiv 2 2 x.2.1 :=
    ((continuous_arenaEquiv 2 2).comp continuous_snd.fst).measurable
  exact ((he.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd).prodMk
    (hc.prodMk measurable_snd.snd)

set_option synthInstance.maxSize 512 in
/-- ★ **Liouville on `Σ`**, inherited from #212 through the identification: the Hamiltonian flow
preserves the transported `(Fubini–Study × Haar²)²` measure. -/
theorem map_hamiltonianFlow_coupledFlow (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f)
    (hcCc : ContDiff ℝ ∞ Cc.f) (hcC : ContDiff ℝ ∞ C.f) (t : ℝ) (p₀ p₁ : FieldArena 2 2) :
    Measure.map ((crossForm_isSymplectic 3 3).hamiltonianFlow
        (contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC) t)
        (Measure.map coupledToSigma (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)))
      = Measure.map coupledToSigma
          (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)) := by
  have hmf : Measurable ((crossForm_isSymplectic 3 3).hamiltonianFlow
      (contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC) t) :=
    ((crossForm_isSymplectic 3 3).continuous_hamiltonianFlow _ t).measurable
  have hmp : MeasurePreserving (coupledFlow J ħ A B Jc Cc C t)
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))
      (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)) :=
    (clockStep_measurePreserving ħ Jc Cc C t p₀ p₁).comp (echoStep_measurePreserving J ħ A B t p₀ p₁)
  rw [Measure.map_map hmf measurable_coupledToSigma]
  have hcomp : (crossForm_isSymplectic 3 3).hamiltonianFlow
      (contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC) t ∘ coupledToSigma
        = coupledToSigma ∘ coupledFlow J ħ A B Jc Cc C t := by
    funext x
    exact hamiltonianFlow_coupledFlow J ħ A B Jc Cc C hcA hcB hcCc hcC t x
  rw [hcomp, ← Measure.map_map measurable_coupledToSigma hmp.measurable, hmp.map_eq]

/-- ★★★ **The coupled clock and echo, generated.** On
`Σ = (ℂℙ³ × T² × T²) × (ℂℙ³ × T²)` with the symplectic form `echoForm ⊕ arenaForm`: the coupled
Hamiltonian is smooth, its Hamiltonian flow is #212's `coupledFlow` read on `Σ`, the Hamiltonian is
`−(2/ħ)` times #212's joint energy (cross term included), and the transported Liouville measure is
preserved. -/
theorem coupled_hamiltonian (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f)
    (hcCc : ContDiff ℝ ∞ Cc.f) (hcC : ContDiff ℝ ∞ C.f) :
    ContMDiff 𝓘(ℝ, CrossModel 3 3) 𝓘(ℝ, ℝ) ∞ (coupledEnergySigma J ħ A B Jc Cc C)
      ∧ (∀ (t : ℝ) (x : ClockEchoArena),
          (crossForm_isSymplectic 3 3).hamiltonianFlow
              (contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC) t (coupledToSigma x)
            = coupledToSigma (coupledFlow J ħ A B Jc Cc C t x))
      ∧ (∀ x : ClockEchoArena, coupledEnergySigma J ħ A B Jc Cc C (coupledToSigma x)
          = -(2 / ħ) * coupledEnergy J A B Jc Cc C x)
      ∧ (∀ (t : ℝ) (p₀ p₁ : FieldArena 2 2),
          Measure.map ((crossForm_isSymplectic 3 3).hamiltonianFlow
              (contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC) t)
            (Measure.map coupledToSigma
              (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume)))
          = Measure.map coupledToSigma
              (((fsMeasure p₀).prod volume).prod ((fsMeasure p₁).prod volume))) :=
  ⟨contMDiff_coupledEnergySigma J ħ A B Jc Cc C hcA hcB hcCc hcC,
    hamiltonianFlow_coupledFlow J ħ A B Jc Cc C hcA hcB hcCc hcC,
    coupledEnergySigma_eq J ħ A B Jc Cc C,
    map_hamiltonianFlow_coupledFlow J ħ A B Jc Cc C hcA hcB hcCc hcC⟩

end Coupled

end CSD.RecordLayer

end
