/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ArenaCoupledFlow
public import CsdLean4.RecordLayer.ActivatedWrite
public import CsdLean4.CV.ArenaIndexBridge

/-!
# The activated write is a Hamiltonian flow on the arena

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #195 (out of #39; the author's second
operational-geometry brief, #191–#197).

#194 built the dynamics of the activated write as data — a two-time, measure-preserving flow on
`FieldArena 2 2 × T²` whose ray runs the detuned exchange and whose pointer obeys
`θ̇₁ = −(2g/ħ) f'(θ₂) n_B(p(t))`. This module identifies it with **the Hamiltonian flow of the
joint energy on the arena** of `LF4/ArenaSymplectic.lean` (R-016′), through the index bridge
`FibredFieldArena 2 2 ≃ Σ = ℂℙ³ × T²` of `CV/ArenaIndexBridge.lean`:

  `𝓗 = −(2/ħ) · (J⟨X⟩ + g f(θ₂) n_B) = coupledEnergy (J X/ħ) (g n_B/ħ) f`,

so that `activeFlow` is `hamiltonianFlow 𝓗` read on the field arena — and the pointer rate of #194
is *forced*: with this corpus's Fubini–Study form the Schrödinger unitary of `H` is the flow of
`−2⟨H⟩`, and the coupled term inherits the same factor.

* `hopIdx`, `hamA`, `hamB` — the hop and the receiver occupancy, reindexed to `Fin 4` and scaled
  by `1/ħ`; `hamA_isHermitian`, `hamB_isHermitian`;
* `expectation_eq_arenaObs` — the two expectation functionals of the corpus agree;
* ★ `activatedEnergy`, ★★ `activatedEnergy_eq` — **the Hamiltonian is `−(2/ħ)` times #194's
  `activeEnergy`**, read on `Σ`;
* ★★ `idxUnitary_detunedFlow` — **the reindexed detuned exchange is the Schrödinger unitary of
  `A + f(θ₂) B`**, by the ODE uniqueness of `ExpUnique.lean` in the matrix algebra;
  `arenaEquiv_arenaFlow`;
* `schrodingerHamiltonian_hamB`, `coupledAccum_eq`, ★ `pointerAmount_eq` — **the accumulated
  `−2⟨B⟩` along the orbit is the lifted pointer displacement of #194**;
* ★★★ `hamiltonianFlow_activeFlow` — **`activeFlow` is the Hamiltonian flow of `𝓗`**, transported
  along the index bridge;
* ★ `arenaVolume_map_activeFlow` — Liouville for the arena volume of `arenaForm^4`, as a corollary;
* ★★★ `activated_hamiltonian` — the package.

## Honest scope

* The Hamiltonian is stated with the corpus's normalisation, `−(2/ħ)` times the row's `𝓗`. The
  row's pointer rate `g f'(θ₂)` was the naive normalisation; the arena form fixes it to
  `−(2g/ħ) f'(θ₂)`, and #194's `rateAt` now carries that factor. Nothing else in #194 changed.
* The identification is along `fibredArenaEquiv 2 2`, a relabelling of the four configurations;
  the fibre needs no transport. It is pointwise; the measure statement is the arena's own
  Liouville theorem read through the relabelling.
* `f` is `C^∞` here (the flow machinery needs a smooth Hamiltonian); #194 needs only `C¹`.
* The chart-level route (`SigmaLayer/UntriggeredFlow.lean`) is not taken: the arena route closes
  the row without the transport boundary R-016 would have left.

References: `specs/BACKLOG.md` #195, #194, #39; `LF4/ArenaCoupledFlow.lean`
(`coupledEnergy`, `hamiltonianFlow_coupledEnergy`); `LF4/ArenaSymplectic.lean` (`arenaForm`,
`arenaVolume_map_hamiltonianFlow`); `CV/ArenaIndexBridge.lean` (`arenaEquiv`, `fibredArenaEquiv`,
`arenaKick_arenaEquiv`, `arenaObs_arenaEquiv`); `RecordLayer/ActivatedWrite.lean`;
`Mathlib/Analysis/Normed/Algebra/ExpUnique.lean` (`exp_smul_eq_of_hasDerivAt`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD.RecordLayer

/-! ### The expectation functionals agree -/

/-- The expectation of `ProjectiveSpaceSchrodingerFlow.lean` is the arena observable of
`ArenaBridge.lean`. -/
theorem expectation_eq_arenaObs {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (q : ℙ ℂ (Ambient n)) : expectation H q = arenaObs H q := by
  rw [expectation, arenaObs, arenaDM]
  set v := q.rep with hv
  have key : (dmVec v * H).trace
      = (((‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ * inner ℂ v (Matrix.toEuclideanLin H v) := by
    rw [Matrix.trace, PiLp.inner_apply, Finset.mul_sum]
    simp only [Matrix.diag_apply, Matrix.mul_apply, dmVec_apply', toEuclideanLin_coord,
      Matrix.mulVec, dotProduct, RCLike.inner_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def]
    ring
  rw [key, ← Complex.ofReal_inv, RCLike.re_to_complex, Complex.re_ofReal_mul, div_eq_inv_mul]

/-! ### The matrices on `Σ` -/

/-- The configuration index of the two-site exchange as `Fin 4`. -/
noncomputable def hopIdx : HopConfig ≃ Fin 4 := configEquiv 2 2

/-- The hop, scaled by `1/ħ`, on `Σ`'s index. -/
noncomputable def hamA (J ħ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex hopIdx hopIdx (((J / ħ : ℝ) : ℂ) • hopX)

/-- The receiver occupancy, scaled by `g/ħ`, on `Σ`'s index. -/
noncomputable def hamB (g ħ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex hopIdx hopIdx (((g / ħ : ℝ) : ℂ) • occB)

/-- Arena observables transport along the exchange's relabelling. -/
theorem arenaObs_reindex_hop (A : Matrix HopConfig HopConfig ℂ) (p : FieldArena 2 2) :
    arenaObs (Matrix.reindex hopIdx hopIdx A) (arenaEquiv 2 2 p) = arenaObs A p :=
  arenaObs_reindex hopIdx A p

theorem hopX_isHermitian : hopX.IsHermitian := hopX_conjTranspose

theorem occB_isHermitian : occB.IsHermitian := occB_conjTranspose

theorem hamA_isHermitian (J ħ : ℝ) : (hamA J ħ).IsHermitian :=
  (hopX_isHermitian.smul (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal]))).reindex hopIdx

theorem hamB_isHermitian (g ħ : ℝ) : (hamB g ħ).IsHermitian :=
  (occB_isHermitian.smul (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal]))).reindex hopIdx

/-- Reindexing is linear: scalars. -/
theorem reindex_smul_hop (c : ℂ) (M : Matrix HopConfig HopConfig ℂ) :
    Matrix.reindex hopIdx hopIdx (c • M) = c • Matrix.reindex hopIdx hopIdx M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Reindexing is linear: sums. -/
theorem reindex_add_hop (M N : Matrix HopConfig HopConfig ℂ) :
    Matrix.reindex hopIdx hopIdx (M + N)
      = Matrix.reindex hopIdx hopIdx M + Matrix.reindex hopIdx hopIdx N := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

section Energy

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- ★ **The Hamiltonian of the activated write on `Σ`**: `−(2/ħ)(J⟨X⟩ + g f(θ₂) n_B)`. -/
noncomputable def activatedEnergy : KSigma 4 → ℝ := coupledEnergy (hamA J ħ) (hamB g ħ) hf

theorem contMDiff_activatedEnergy (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ArenaModel 3) 𝓘(ℝ, ℝ) ∞ (activatedEnergy J ħ g hf) :=
  contMDiff_coupledEnergy (hamA J ħ) (hamB g ħ) hf hc

theorem schrodingerHamiltonian_hamA (p : FieldArena 2 2) :
    schrodingerHamiltonian (hamA J ħ) (arenaEquiv 2 2 p) = -(2 * J / ħ) * arenaObs hopX p := by
  rw [schrodingerHamiltonian, expectation_eq_arenaObs, hamA, arenaObs_reindex_hop,
    arenaObs_real_smul]
  ring

theorem schrodingerHamiltonian_hamB (p : FieldArena 2 2) :
    schrodingerHamiltonian (hamB g ħ) (arenaEquiv 2 2 p) = -(2 * g / ħ) * momentMap p excB := by
  rw [schrodingerHamiltonian, expectation_eq_arenaObs, hamB, arenaObs_reindex_hop,
    arenaObs_real_smul, occB, arenaObs_single_eq_momentMap]
  ring

/-- ★★ **The Hamiltonian is `−(2/ħ)` times #194's joint energy**, read on `Σ`. -/
theorem activatedEnergy_eq (x : ActiveArena) :
    activatedEnergy J ħ g hf (fibredArenaEquiv 2 2 x) = -(2 / ħ) * activeEnergy J g hf x := by
  show coupledEnergy (hamA J ħ) (hamB g ħ) hf (arenaEquiv 2 2 x.1, x.2) = _
  rw [coupledEnergy, schrodingerHamiltonian_hamA, schrodingerHamiltonian_hamB, activeEnergy,
    detuningAt]
  show _ = -(2 / ħ) * (J * arenaObs hopX x.1 + g * hf.lift x.2.2 * momentMap x.1 excB)
  unfold torusPotential
  ring

end Energy

/-! ### The reindexed detuned exchange is the Schrödinger unitary of `A + f(θ₂) B` -/

section Transport

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- The state-dependent matrix of the coupled flow is the reindexed detuned Hamiltonian over `ħ`. -/
theorem coupledMatrix_eq (φ : AddCircle (1 : ℝ)) :
    coupledMatrix (hamA J ħ) (hamB g ħ) hf φ
      = Matrix.reindex hopIdx hopIdx (((1 / ħ : ℝ) : ℂ) • detunedH J (detuningAt g hf φ)) := by
  unfold coupledMatrix hamA hamB detunedH detuningAt
  simp only [reindex_smul_hop, reindex_add_hop]
  push_cast
  module

/-- The reindexing of matrices, as a continuous linear map. -/
noncomputable def reindexCLM : Matrix HopConfig HopConfig ℂ →L[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℂ ℂ hopIdx hopIdx).toLinearMap

@[simp] theorem reindexCLM_apply (M : Matrix HopConfig HopConfig ℂ) :
    reindexCLM M = Matrix.reindex hopIdx hopIdx M := rfl

/-- The reindexed generator, as a multiple of the state-dependent matrix. -/
theorem reindex_detunedGen (φ : AddCircle (1 : ℝ)) :
    Matrix.reindex hopIdx hopIdx (detunedGen J ħ (detuningAt g hf φ))
      = (-Complex.I) • coupledMatrix (hamA J ħ) (hamB g ħ) hf φ := by
  rw [coupledMatrix_eq, detunedGen]
  simp only [reindex_smul_hop]
  rw [smul_smul]
  congr 1
  ring

/-- ★★ **The reindexed detuned exchange is the Schrödinger unitary of `A + f(θ₂) B`**: both solve
`U' = −i H U`, `U 0 = 1` in the matrix algebra, so both are `exp (−i t H)`. -/
theorem idxUnitary_detunedFlow (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxUnitary hopIdx ((detunedFlow J ħ (detuningAt g hf φ)).flow t)
      = Matrix.schrodingerUnitary (coupledMatrix_isHermitian (hamA_isHermitian J ħ)
          (hamB_isHermitian g ħ) hf φ) t := by
  apply Subtype.ext
  rw [idxUnitary_val, detunedFlow_val]
  show Matrix.reindex hopIdx hopIdx (exp (t • detunedGen J ħ (detuningAt g hf φ)))
    = exp (Matrix.schrodingerGen (coupledMatrix (hamA J ħ) (hamB g ħ) hf φ) t)
  have hU : ∀ c : ℂ, HasDerivAt
      (fun c : ℂ => reindexCLM (exp (c • detunedGen J ħ (detuningAt g hf φ))))
      (Matrix.reindex hopIdx hopIdx (detunedGen J ħ (detuningAt g hf φ))
        * reindexCLM (exp (c • detunedGen J ħ (detuningAt g hf φ)))) c := by
    intro c
    have h := reindexCLM.hasFDerivAt.comp_hasDerivAt c
      (hasDerivAt_exp_smul_const' (detunedGen J ħ (detuningAt g hf φ)) c)
    refine h.congr_deriv ?_
    rw [reindexCLM_apply, reindexCLM_apply, Matrix.reindex_mul]
  have h0 : (fun c : ℂ => reindexCLM (exp (c • detunedGen J ħ (detuningAt g hf φ)))) 0 = 1 := by
    simp only [zero_smul, exp_zero, reindexCLM_apply, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
  have hexp := exp_smul_eq_of_hasDerivAt _ h0 hU (t : ℂ)
  simp only [reindexCLM_apply] at hexp
  rw [matrix_real_smul, hexp, Matrix.schrodingerGen, reindex_detunedGen, smul_smul]
  congr 1
  congr 1
  ring

/-- The transported ray of the detuned exchange is the Schrödinger orbit of `A + f(θ₂) B`. -/
theorem arenaEquiv_arenaFlow (φ : AddCircle (1 : ℝ)) (t : ℝ) (p : FieldArena 2 2) :
    arenaEquiv 2 2 ((detunedFlow J ħ (detuningAt g hf φ)).arenaFlow t p)
      = Matrix.schrodingerUnitary (coupledMatrix_isHermitian (hamA_isHermitian J ħ)
          (hamB_isHermitian g ħ) hf φ) t • arenaEquiv 2 2 p := by
  rw [FieldStructuredFlow.arenaFlow, ← arenaKick_arenaEquiv, ← arenaKick_eq_smul']
  congr 1
  exact idxUnitary_detunedFlow J ħ g hf φ t

/-- The accumulated `−2⟨B⟩` along the transported orbit is `−(2g/ħ)` times the accumulated
occupancy of #194. -/
theorem coupledAccum_eq (φ : AddCircle (1 : ℝ)) (p : FieldArena 2 2) (t : ℝ) :
    coupledAccum (hamA_isHermitian J ħ) (hamB_isHermitian g ħ) hf φ (arenaEquiv 2 2 p) t
      = -(2 * g / ħ) * occAccum J ħ (detuningAt g hf φ) p t := by
  unfold coupledAccum occAccum
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show schrodingerHamiltonian (hamB g ħ) (Matrix.schrodingerUnitary _ s • arenaEquiv 2 2 p)
    = -(2 * g / ħ) * occHist J ħ (detuningAt g hf φ) p s
  rw [← arenaEquiv_arenaFlow, schrodingerHamiltonian_hamB, occHist_eq_momentMap]

/-- ★ **The pointer displacement of the Hamiltonian flow is #194's lifted displacement.** -/
theorem pointerAmount_eq (x : ActiveArena) (t : ℝ) :
    hf.deriv_periodic.lift x.2.2
        * coupledAccum (hamA_isHermitian J ħ) (hamB_isHermitian g ħ) hf x.2.2 (arenaEquiv 2 2 x.1) t
      = pointerAmount J ħ g hf t x := by
  rw [coupledAccum_eq, pointerAmount, rateAt]
  ring

/-- ★★★ **The activated write is the Hamiltonian flow of its energy.** Read on `Σ` through the
index bridge, `activeFlow J ħ g hf t` is `hamiltonianFlow (activatedEnergy J ħ g hf) t` for the
arena symplectic form. -/
theorem hamiltonianFlow_activeFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : ActiveArena) :
    (arenaForm_isSymplectic 3).hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t
        (fibredArenaEquiv 2 2 x)
      = fibredArenaEquiv 2 2 (activeFlow J ħ g hf t x) := by
  show (arenaForm_isSymplectic 3).hamiltonianFlow
      (contMDiff_coupledEnergy (hamA J ħ) (hamB g ħ) hf hc) t (arenaEquiv 2 2 x.1, x.2)
    = (arenaEquiv 2 2 (activeFlow J ħ g hf t x).1, (activeFlow J ħ g hf t x).2)
  rw [hamiltonianFlow_coupledEnergy (hamA_isHermitian J ħ) (hamB_isHermitian g ħ) hf hc,
    activeFlow_fst, activeFlow_snd, arenaEquiv_arenaFlow, pointerAmount_eq]
  rfl

/-- ★ **Liouville on the arena volume** for the activated write, read on `Σ`. -/
theorem arenaVolume_map_activeFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Measure.map (fun p : KSigma 4 =>
        fibredArenaEquiv 2 2 (activeFlow J ħ g hf t ((fibredArenaEquiv 2 2).symm p)))
      (arenaVolume 3) = arenaVolume 3 := by
  have h : (fun p : KSigma 4 =>
      fibredArenaEquiv 2 2 (activeFlow J ħ g hf t ((fibredArenaEquiv 2 2).symm p)))
      = (arenaForm_isSymplectic 3).hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t := by
    funext p
    rw [← hamiltonianFlow_activeFlow J ħ g hf hc t, Equiv.apply_symm_apply]
  rw [h]
  exact arenaVolume_map_hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t

/-- ★★★ **The activated write, generated.** On `Σ = ℂℙ³ × T²` with the arena symplectic form:
the Hamiltonian `−(2/ħ)(J⟨X⟩ + g f(θ₂) n_B)` is smooth, its Hamiltonian flow is #194's
`activeFlow` read through the index bridge, the Hamiltonian is `−(2/ħ)` times #194's joint energy,
and the arena volume is preserved. -/
theorem activated_hamiltonian (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ArenaModel 3) 𝓘(ℝ, ℝ) ∞ (activatedEnergy J ħ g hf)
      ∧ (∀ (t : ℝ) (x : ActiveArena),
          (arenaForm_isSymplectic 3).hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t
              (fibredArenaEquiv 2 2 x)
            = fibredArenaEquiv 2 2 (activeFlow J ħ g hf t x))
      ∧ (∀ x : ActiveArena,
          activatedEnergy J ħ g hf (fibredArenaEquiv 2 2 x) = -(2 / ħ) * activeEnergy J g hf x)
      ∧ (∀ t : ℝ, Measure.map (fun p : KSigma 4 =>
          fibredArenaEquiv 2 2 (activeFlow J ħ g hf t ((fibredArenaEquiv 2 2).symm p)))
            (arenaVolume 3) = arenaVolume 3) :=
  ⟨contMDiff_activatedEnergy J ħ g hf hc, hamiltonianFlow_activeFlow J ħ g hf hc,
    activatedEnergy_eq J ħ g hf, arenaVolume_map_activeFlow J ħ g hf hc⟩

end Transport

end CSD.RecordLayer

end
