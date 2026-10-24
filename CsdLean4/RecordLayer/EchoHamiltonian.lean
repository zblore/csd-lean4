/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.EchoCoupledFlow
public import CsdLean4.RecordLayer.ActivatedHamiltonian
public import CsdLean4.RecordLayer.EchoArena

/-!
# The echo is a Hamiltonian flow on `ℂℙ³ × T² × T²`

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #202, the generation half (out of #39).

#199 built the echo's dynamics as data on `FieldArena 2 2 × (T² × T²)`. Read on `Σ = ℂℙ³ × T² × T²`
through the index bridge of #195, it is the Hamiltonian flow, for the symplectic form
`arenaForm ⊕ dψ₁ ∧ dψ₂` of `LF4/EchoCoupledFlow.lean`, of

  `−(2/ħ) (J⟨X⟩ + g_A f_A(θ₂ᴬ) n_A + g_B f_B(θ₂ᴮ) n_B)`,

which is `−(2/ħ)` times #199's joint energy. The second half of #202: the clock factor is #195's
`activated_hamiltonian`, the echo factor is this file, and the clock-and-echo arena is their product.

* `hamOccA`, `schrodingerHamiltonian_hamOccA` — the sender occupancy on `Σ`'s index;
* `echoEnergySigma`, `contMDiff_echoEnergySigma`, ★★ `echoEnergySigma_eq` — **the Hamiltonian is `−(2/ħ)` times
  #199's joint energy**; `echoToSigma` — the echo arena read on `Σ`;
* `twoCoupledMatrix_eq`, `reindex_twoDetunedGen`, ★★ `idxUnitary_twoDetunedFlow` — **the reindexed
  two-site detuned exchange is the Schrödinger unitary of `A + f_A(θ₂ᴬ) B_A + f_B(θ₂ᴮ) B_B`** (ODE
  uniqueness in the matrix algebra); `arenaEquiv_twoDetuned_arenaFlow`;
* `twoAccumA_eq`, `twoAccumB_eq`, ★ `echoAmountA_eq`, `echoAmountB_eq` — **the pointer
  displacements of the Hamiltonian flow are #199's lifted displacements**;
* ★★★ `hamiltonianFlow_echoFlow` — **the echo is the Hamiltonian flow of its energy**, read on `Σ`;
  ★ `map_hamiltonianFlow_echoFlow` — Liouville, inherited from #199 through the identification;
* ★★★ `echo_hamiltonian` — the package.

References: `specs/BACKLOG.md` #202, #199, #195, #39; `LF4/EchoCoupledFlow.lean`,
`RecordLayer/ActivatedHamiltonian.lean` (`hamA`, `hamB`, `hopIdx`, `reindexCLM`, the proof pattern),
`RecordLayer/EchoArena.lean`, `CV/TwoSiteDetuned.lean` (`twoDetunedGen`, `occB_twoDetunedFlow`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD.RecordLayer

/-! ### The sender occupancy on `Σ` -/

/-- The sender occupancy, scaled by `g/ħ`, on `Σ`'s index. -/
noncomputable def hamOccA (g ħ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex hopIdx hopIdx (((g / ħ : ℝ) : ℂ) • occA)

theorem occA_isHermitian : occA.IsHermitian := occA_conjTranspose

theorem hamOccA_isHermitian (g ħ : ℝ) : (hamOccA g ħ).IsHermitian :=
  (occA_isHermitian.smul (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal]))).reindex
    hopIdx

theorem schrodingerHamiltonian_hamOccA (g ħ : ℝ) (p : FieldArena 2 2) :
    schrodingerHamiltonian (hamOccA g ħ) (arenaEquiv 2 2 p) = -(2 * g / ħ) * momentMap p excA := by
  rw [schrodingerHamiltonian, expectation_eq_arenaObs, hamOccA, arenaObs_reindex_hop,
    arenaObs_real_smul, occA, arenaObs_single_eq_momentMap]
  ring

section Echo

variable (J ħ : ℝ) (A B : PointerCoupling)

/-! ### The energy on `Σ` -/

/-- ★ **The echo's Hamiltonian on `Σ`**: `−(2/ħ)(J⟨X⟩ + g_A f_A(θ₂ᴬ) n_A + g_B f_B(θ₂ᴮ) n_B)`. -/
noncomputable def echoEnergySigma : EchoSigma 3 → ℝ :=
  twoCoupledEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) A.periodic B.periodic

theorem contMDiff_echoEnergySigma (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f) :
    ContMDiff 𝓘(ℝ, EchoModel 3) 𝓘(ℝ, ℝ) ∞ (echoEnergySigma J ħ A B) :=
  contMDiff_twoCoupledEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) A.periodic B.periodic hcA hcB

/-- The echo arena read on `Σ`: the ray through the index bridge, the two tori as they are. -/
noncomputable def echoToSigma (x : EchoArena) : EchoSigma 3 := ((arenaEquiv 2 2 x.1, x.2.1), x.2.2)

/-- ★★ **The Hamiltonian is `−(2/ħ)` times #199's joint energy**, read on `Σ`. -/
theorem echoEnergySigma_eq (x : EchoArena) :
    echoEnergySigma J ħ A B (echoToSigma x) = -(2 / ħ) * echoEnergy J A B x := by
  show twoCoupledEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) A.periodic B.periodic
    ((arenaEquiv 2 2 x.1, x.2.1), x.2.2) = _
  rw [twoCoupledEnergy, coupledEnergy, schrodingerHamiltonian_hamA, schrodingerHamiltonian_hamOccA,
    schrodingerHamiltonian_hamB, echoEnergy, echoDetA, echoDetB, detuningAt, detuningAt]
  show -(2 * J / ħ) * arenaObs hopX x.1 + -(2 * A.g / ħ) * momentMap x.1 excA * A.periodic.lift x.2.1.2
      + -(2 * B.g / ħ) * momentMap x.1 excB * B.periodic.lift x.2.2.2
    = -(2 / ħ) * (J * arenaObs hopX x.1 + A.g * A.periodic.lift x.2.1.2 * momentMap x.1 excA
      + B.g * B.periodic.lift x.2.2.2 * momentMap x.1 excB)
  ring

/-! ### The reindexed two-site exchange is the Schrödinger unitary of the two-angle matrix -/

/-- The two-angle matrix is the reindexed two-site detuned Hamiltonian over `ħ`. -/
theorem twoCoupledMatrix_eq (φ ψ : AddCircle (1 : ℝ)) :
    twoCoupledMatrix (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) A.periodic B.periodic φ ψ
      = Matrix.reindex hopIdx hopIdx (((1 / ħ : ℝ) : ℂ)
          • twoDetunedH J (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ)) := by
  unfold twoCoupledMatrix coupledMatrix hamA hamOccA hamB twoDetunedH detuningAt
  simp only [reindex_smul_hop, reindex_add_hop]
  push_cast
  module

/-- The reindexed two-site generator, as a multiple of the two-angle matrix. -/
theorem reindex_twoDetunedGen (φ ψ : AddCircle (1 : ℝ)) :
    Matrix.reindex hopIdx hopIdx
        (twoDetunedGen J ħ (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ))
      = (-Complex.I) • twoCoupledMatrix (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) A.periodic
          B.periodic φ ψ := by
  rw [twoCoupledMatrix_eq, twoDetunedGen]
  simp only [reindex_smul_hop]
  rw [smul_smul]
  congr 1
  ring

/-- ★★ **The reindexed two-site detuned exchange is the Schrödinger unitary of
`A + f_A(θ₂ᴬ) B_A + f_B(θ₂ᴮ) B_B`**: both solve `U' = −i H U`, `U 0 = 1`. -/
theorem idxUnitary_twoDetunedFlow (φ ψ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxUnitary hopIdx
        ((twoDetunedFlow J ħ (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ)).flow t)
      = Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian (hamA_isHermitian J ħ)
          (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ) A.periodic B.periodic φ ψ) t := by
  apply Subtype.ext
  rw [idxUnitary_val, twoDetunedFlow_val]
  set G := twoDetunedGen J ħ (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ) with hG
  show Matrix.reindex hopIdx hopIdx (exp (t • G))
    = exp (Matrix.schrodingerGen (twoCoupledMatrix (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ)
        A.periodic B.periodic φ ψ) t)
  have hU : ∀ c : ℂ, HasDerivAt (fun c : ℂ => reindexCLM (exp (c • G)))
      (Matrix.reindex hopIdx hopIdx G * reindexCLM (exp (c • G))) c := by
    intro c
    have h := reindexCLM.hasFDerivAt.comp_hasDerivAt c (hasDerivAt_exp_smul_const' G c)
    refine h.congr_deriv ?_
    rw [reindexCLM_apply, reindexCLM_apply, Matrix.reindex_mul]
  have h0 : (fun c : ℂ => reindexCLM (exp (c • G))) 0 = 1 := by
    simp only [zero_smul, exp_zero, reindexCLM_apply, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
  have hexp := exp_smul_eq_of_hasDerivAt _ h0 hU (t : ℂ)
  simp only [reindexCLM_apply] at hexp
  rw [matrix_real_smul, hexp, Matrix.schrodingerGen, hG, reindex_twoDetunedGen, smul_smul]
  congr 1
  congr 1
  ring

/-- The transported ray of the two-site exchange is the two-angle Schrödinger orbit. -/
theorem arenaEquiv_twoDetuned_arenaFlow (φ ψ : AddCircle (1 : ℝ)) (t : ℝ) (p : FieldArena 2 2) :
    arenaEquiv 2 2
        ((twoDetunedFlow J ħ (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ)).arenaFlow
          t p)
      = Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian (hamA_isHermitian J ħ)
          (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ) A.periodic B.periodic φ ψ) t
        • arenaEquiv 2 2 p := by
  rw [FieldStructuredFlow.arenaFlow, ← arenaKick_arenaEquiv, ← arenaKick_eq_smul']
  congr 1
  exact idxUnitary_twoDetunedFlow J ħ A B φ ψ t

/-! ### The displacements -/

/-- The accumulated `−2⟨B_A⟩` along the transported orbit is `−(2g_A/ħ)` times #199's accumulated
occupancy of `A`. -/
theorem twoAccumA_eq (φ ψ : AddCircle (1 : ℝ)) (p : FieldArena 2 2) (t : ℝ) :
    twoAccumA (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ)
        A.periodic B.periodic φ ψ (arenaEquiv 2 2 p) t
      = -(2 * A.g / ħ)
          * occAccumA J ħ (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ) p t := by
  unfold twoAccumA occAccumA
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show schrodingerHamiltonian (hamOccA A.g ħ) (Matrix.schrodingerUnitary _ s • arenaEquiv 2 2 p)
    = -(2 * A.g / ħ) * occHistA J ħ (detuningAt A.g A.periodic φ) (detuningAt B.g B.periodic ψ) p s
  rw [← arenaEquiv_twoDetuned_arenaFlow, schrodingerHamiltonian_hamOccA, occHistA, occA,
    arenaObs_single_eq_momentMap]

/-- The accumulated `−2⟨B_B⟩` along the transported orbit is `−(2g_B/ħ)` times the accumulated
occupancy of `B`. -/
theorem twoAccumB_eq (φ ψ : AddCircle (1 : ℝ)) (p : FieldArena 2 2) (t : ℝ) :
    twoAccumB (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ)
        A.periodic B.periodic φ ψ (arenaEquiv 2 2 p) t
      = -(2 * B.g / ħ)
          * occAccum J ħ (detuningAt B.g B.periodic ψ - detuningAt A.g A.periodic φ) p t := by
  unfold twoAccumB occAccum
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show schrodingerHamiltonian (hamB B.g ħ) (Matrix.schrodingerUnitary _ s • arenaEquiv 2 2 p)
    = -(2 * B.g / ħ)
        * occHist J ħ (detuningAt B.g B.periodic ψ - detuningAt A.g A.periodic φ) p s
  rw [← arenaEquiv_twoDetuned_arenaFlow, schrodingerHamiltonian_hamB, ← occB_twoDetunedFlow, occB,
    arenaObs_single_eq_momentMap]

/-- ★ **Pointer `A`'s displacement of the Hamiltonian flow is #199's lifted displacement.** -/
theorem echoAmountA_eq (x : EchoArena) (t : ℝ) :
    A.periodic.deriv_periodic.lift x.2.1.2
        * twoAccumA (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ)
          A.periodic B.periodic x.2.1.2 x.2.2.2 (arenaEquiv 2 2 x.1) t
      = echoAmountA J ħ A B t x := by
  rw [twoAccumA_eq, echoAmountA, rateAt]
  unfold echoDetA echoDetB
  ring

/-- ★ **Pointer `B`'s displacement of the Hamiltonian flow is #199's lifted displacement.** -/
theorem echoAmountB_eq (x : EchoArena) (t : ℝ) :
    B.periodic.deriv_periodic.lift x.2.2.2
        * twoAccumB (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ) (hamB_isHermitian B.g ħ)
          A.periodic B.periodic x.2.1.2 x.2.2.2 (arenaEquiv 2 2 x.1) t
      = echoAmountB J ħ A B t x := by
  rw [twoAccumB_eq, echoAmountB, rateAt]
  unfold echoDetA echoDetB
  ring

/-! ### The identification -/

/-- ★★★ **The echo is the Hamiltonian flow of its energy.** Read on `Σ = ℂℙ³ × T² × T²` through the
index bridge, `echoFlow J ħ A B t` is `hamiltonianFlow (echoEnergySigma J ħ A B) t` for the symplectic
form `arenaForm ⊕ dψ₁ ∧ dψ₂`. -/
theorem hamiltonianFlow_echoFlow (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f) (t : ℝ)
    (x : EchoArena) :
    (echoForm_isSymplectic 3).hamiltonianFlow (contMDiff_echoEnergySigma J ħ A B hcA hcB) t
        (echoToSigma x)
      = echoToSigma (echoFlow J ħ A B t x) := by
  show (echoForm_isSymplectic 3).hamiltonianFlow
      (contMDiff_twoCoupledEnergy (hamA J ħ) (hamOccA A.g ħ) (hamB B.g ħ) A.periodic B.periodic
        hcA hcB) t ((arenaEquiv 2 2 x.1, x.2.1), x.2.2)
    = ((arenaEquiv 2 2 (echoFlow J ħ A B t x).1, (echoFlow J ħ A B t x).2.1),
        (echoFlow J ħ A B t x).2.2)
  rw [hamiltonianFlow_twoCoupledEnergy (hamA_isHermitian J ħ) (hamOccA_isHermitian A.g ħ)
    (hamB_isHermitian B.g ħ) A.periodic B.periodic hcA hcB, echoFlow_fst, echoFlow_pointerA,
    echoFlow_pointerB]
  unfold echoDetA echoDetB
  rw [arenaEquiv_twoDetuned_arenaFlow, echoAmountA_eq, echoAmountB_eq]
  rfl

set_option synthInstance.maxSize 512 in
/-- ★ **Liouville on `Σ`**, inherited from #199 through the identification: the Hamiltonian flow
preserves the transported Fubini–Study × Haar⁴ measure. -/
theorem map_hamiltonianFlow_echoFlow (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f) (t : ℝ)
    (p₀ : FieldArena 2 2) :
    Measure.map ((echoForm_isSymplectic 3).hamiltonianFlow (contMDiff_echoEnergySigma J ħ A B hcA hcB) t)
        (Measure.map (echoToSigma) ((fsMeasure p₀).prod volume))
      = Measure.map (echoToSigma) ((fsMeasure p₀).prod volume) := by
  have hme : Measurable (echoToSigma) := by
    unfold echoToSigma
    exact (((continuous_arenaEquiv 2 2).comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)).measurable.prodMk (continuous_snd.comp continuous_snd).measurable
  have hmf : Measurable ((echoForm_isSymplectic 3).hamiltonianFlow
      (contMDiff_echoEnergySigma J ħ A B hcA hcB) t) :=
    ((echoForm_isSymplectic 3).continuous_hamiltonianFlow _ t).measurable
  rw [Measure.map_map hmf hme]
  have hcomp : (echoForm_isSymplectic 3).hamiltonianFlow (contMDiff_echoEnergySigma J ħ A B hcA hcB) t
      ∘ echoToSigma = echoToSigma ∘ echoFlow J ħ A B t := by
    funext x
    exact hamiltonianFlow_echoFlow J ħ A B hcA hcB t x
  rw [hcomp, ← Measure.map_map hme (echoFlow_measurePreserving J ħ A B t p₀).measurable,
    (echoFlow_measurePreserving J ħ A B t p₀).map_eq]

/-- ★★★ **The echo, generated.** On `Σ = ℂℙ³ × T² × T²` with the symplectic form
`arenaForm ⊕ dψ₁ ∧ dψ₂`: the Hamiltonian `−(2/ħ)(J⟨X⟩ + g_A f_A(θ₂ᴬ) n_A + g_B f_B(θ₂ᴮ) n_B)` is smooth,
its Hamiltonian flow is #199's `echoFlow` read through the index bridge, the Hamiltonian is `−(2/ħ)`
times #199's joint energy, and the transported Liouville measure is preserved. -/
theorem echo_hamiltonian (hcA : ContDiff ℝ ∞ A.f) (hcB : ContDiff ℝ ∞ B.f) :
    ContMDiff 𝓘(ℝ, EchoModel 3) 𝓘(ℝ, ℝ) ∞ (echoEnergySigma J ħ A B)
      ∧ (∀ (t : ℝ) (x : EchoArena),
          (echoForm_isSymplectic 3).hamiltonianFlow (contMDiff_echoEnergySigma J ħ A B hcA hcB) t
              (echoToSigma x)
            = echoToSigma (echoFlow J ħ A B t x))
      ∧ (∀ x : EchoArena, echoEnergySigma J ħ A B (echoToSigma x) = -(2 / ħ) * echoEnergy J A B x)
      ∧ (∀ (t : ℝ) (p₀ : FieldArena 2 2),
          Measure.map ((echoForm_isSymplectic 3).hamiltonianFlow
              (contMDiff_echoEnergySigma J ħ A B hcA hcB) t)
            (Measure.map (echoToSigma) ((fsMeasure p₀).prod volume))
          = Measure.map (echoToSigma) ((fsMeasure p₀).prod volume)) :=
  ⟨contMDiff_echoEnergySigma J ħ A B hcA hcB, hamiltonianFlow_echoFlow J ħ A B hcA hcB,
    echoEnergySigma_eq J ħ A B, map_hamiltonianFlow_echoFlow J ħ A B hcA hcB⟩

end Echo

end CSD.RecordLayer

end
