/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ArenaVolume
public import CsdLean4.RecordLayer.ActivatedHamiltonian
public import CsdLean4.RecordLayer.DiracDetector
public import CsdLean4.RecordLayer.GalileanTransformation

/-!
# A Dirac carrier and a pointer in one Hamiltonian arena

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #349 — milestone **M1A** of the author's
programme "From `Σ` to physical spacetime" (2026-11-09): the Dirac-chain-to-Hamiltonian-pointer
bridge.

The lattice Dirac chain of `CV/DiracClockChain.lean` and its site detectors
(`RecordLayer/DiracDetector.lean`) were so far **not on the symplectic arena**: the detector's
register integrates `siteWeight` by definition, with no Hamiltonian behind it. This module puts the
one-particle Dirac ring and a torus pointer on the arena `Σ = ℂℙ^{2M+1} × T²` of
`LF4/ArenaSymplectic.lean` (R-016′) and generates both from **one** energy,

  `𝓗(p, θ) = −2⟨H_D⟩_p − 2 g f(θ₂) ⟨P_j⟩_p = coupledEnergy (H_D) (g P_j) f`,

by instantiating `LF4/ArenaCoupledFlow.lean` (the pattern of
`RecordLayer/ActivatedHamiltonian.lean`, #195). `P_j` is the occupancy projector of site `j`. The
pointer responds to the occupancy the dynamics produces; nothing schedules the write.

## The index bridge and the site projector

* `diracIdx M : ZMod (M + 1) × Fin 2 ≃ Fin (2M + 2)` (`diracIdx_val`), `diracArenaEquiv M` — the
  ring of `M + 1` sites, two components each, as the projective sector of `Σ`;
* `reindex_exp_smul` — reindexing commutes with `exp (t • ·)` (ODE uniqueness, `ExpUnique.lean`);
* `siteProj j` — **the Hermitian site-occupancy projector** `Σ_c |j, c⟩⟨j, c|`:
  `siteProj_isHermitian`, `siteProj_mul_self`, `siteProj_eq_single`, ★ `arenaObs_siteProj`
  (`⟨P_j⟩_p` is the sum of the two moment coordinates of site `j`), `arenaObs_siteProj_nonneg`,
  `arenaObs_siteProj_le_one`, `arenaObs_siteProj_mk` (it is `siteWeight / ‖ψ‖²` of
  `DiracDetector.lean`).

## The energy and its flow

* `diracA`, `diracB` (the reindexed `H_D` and `g P_j`), `diracA_isHermitian`,
  `diracB_isHermitian`, `schrodingerHamiltonian_diracA`, `schrodingerHamiltonian_diracB`;
* ★ `diracPointerEnergy`, `contMDiff_diracPointerEnergy`, ★★ `diracPointerEnergy_eq` — **the energy
  is `−2⟨H_D⟩ − 2 g f(θ₂) ⟨P_j⟩`**, read on the Dirac arena;
* `diracPointerH` (`H_D + g f(θ₂) P_j`), `diracPointerH_isHermitian`, `coupledMatrix_diracPointer`,
  `diracPointerGen_skew`;
  `diracCarrierU` (the carrier's propagator, a `flowU`), `diracCarrierU_val`, `diracCarrierU_zero`,
  ★★ `hasDerivAt_diracCarrierU` — **the carrier's equation `U̇ = −i (H_D + g f(θ₂) P_j) U`**;
  `idxUnitary_diracCarrierU`, `diracArenaEquiv_kick`;
* `diracPointerShift` (`−2 g f'(θ₂) ∫₀ᵗ ⟨P_j⟩`), `diracPointerShift_zero`,
  `coupledAccum_diracPointer`, `diracPointerShift_eq`, ★★ `hasDerivAt_diracPointerShift` — **the
  pointer's equation `θ̇₁ = −2 g f'(θ₂) ⟨P_j⟩_{p(t)}`**; `diracPointerShift_zero_coupling`
  (control: `g = 0`, no response);
* ★ `diracPointerFlow` (the Hamiltonian flow of the energy), `diracPointerFlow_zero`,
  `diracPointerFlow_add`, ★★★ `diracPointerFlow_apply` — **the flow in closed form**: the carrier
  by `exp (−i t (H_D + g f(θ₂) P_j))`, `θ₁` advanced by the pointer shift, `θ₂` fixed
  (`diracPointerFlow_snd_snd`);
* ★★ `hamiltonianVectorField_diracPointer_snd` — **the pointer component of the Hamiltonian vector
  field is `(−2 g f'(θ₂) ⟨P_j⟩, 0)`**, read off `ι_X ω = d𝓗` without integrating the flow;
* ★★ `diracPointerEnergy_flow` — **energy conservation**; ★★ `arenaVolume_map_diracPointerFlow`,
  `kMuL_map_diracPointerFlow` — **Liouville**, for the arena volume and for the corpus's
  `μ_FS ⊗ vol`.

## The checked special case

Profile `trainF` (`−sin(2πx)/(2π)`, `f(0) = 0`, `f'(0) = −1`), carrier on site `j`, pointer at
`(0, 0)`:

* `contDiff_trainF`, `trainF_lift_zero`, `trainF_deriv_lift_zero`; `siteRay j`,
  `arenaObs_siteProj_siteRay` (`⟨P_j⟩ = 1`), `arenaObs_siteProj_siteRay_of_ne` (`⟨P_k⟩ = 0` at
  every other site);
* `diracPointerH_trainF_zero` — on the fibre `θ₂ = 0` the carrier runs the free `H_D`;
* ★★ `hasDerivAt_diracPointerShift_siteRay` — **the pointer's rate at `t = 0` is `2g`**, from the
  flow; ★★ `hamiltonianVectorField_diracPointer_siteRay` — **the same `2g`** from the vector field,
  independently; `hasDerivAt_diracPointerShift_siteRay_of_ne` (a detector at another site starts
  at rate `0`);
* ★★★ `exists_diracPointerFlow_pointer_ne` — **for `g ≠ 0` the Hamiltonian flow moves the
  pointer**: at some time its `θ₁` is not where it started.
* ★★★ `diracPointer_hamiltonian` — the package.

## Honest scope

* **One particle on a finite ring.** The carrier is the single-excitation Dirac ring of `M + 1`
  sites, `ℂℙ^{2M+1}`; no second quantisation, no continuum limit, units `ħ = 1`.
* **A skew product.** `𝓗` does not depend on `θ₁`, so `θ₂` is conserved and the carrier sees the
  *static* site potential `g f(θ₂) P_j`; the moving angle `θ₁` does not feed back on the carrier.
  The interaction is mutual only through the conserved `θ₂`.
* **The normalisation is the corpus's**: with this Fubini–Study form `exp (−i t H)` is the flow of
  `−2⟨H⟩`, which fixes the factor `−2` in the pointer rate.
* **`f` is `C^∞`** (the flow machinery needs a smooth Hamiltonian).
* **Nothing is recorded yet.** No outcome region, threshold, persistence or `ActualOccurrence` is
  stated here; no clock is built; no statement about Born weights, causal order or spacetime is
  made. The pointer rate reads `⟨P_j⟩`, the occupancy of the *state*, which is not a detection
  probability claim.
* The nontriviality is checked at one point (`t = 0`, the carrier on site `j`) and as an
  existence statement; the time at which the pointer has moved is not estimated here.
  `RecordLayer/DiracPointerWrite.lean` (#351) bounds the displacement over an interval.
* The link to `DiracDetector.lean` here is `arenaObs_siteProj_mk` only. That module's `detFlow`
  registers are identified with this flow's pointer in `RecordLayer/DiracPointerWrite.lean`
  (`diracPointerShift_eq_register`, on the fibres with `f(θ₂) = 0`).

References: `specs/BACKLOG.md` #349, #252, #251, #249, #195, #39; `specs/future-work.md`;
`LF4/ArenaCoupledFlow.lean` (`coupledEnergy`, `hamiltonianFlow_coupledEnergy`,
`coupledField_eq_hamiltonianVectorField`, `hasDerivAt_coupledAccum`); `LF4/ArenaSymplectic.lean`
(`arenaForm_isSymplectic`, `arenaVolume_map_hamiltonianFlow`); `LF4/ArenaVolume.lean`
(`kMuL_map_hamiltonianFlow`); `CV/DiracClockChain.lean` (`diracHam`, `diracHam_isHermitian`);
`CV/ArenaIndexBridge.lean` (`idxArenaEquiv`, `idxUnitary`, `arenaObs_reindex`,
`arenaKick_reindex`); `CV/ArenaBridge.lean` (`flowU`); `RecordLayer/ActivatedHamiltonian.lean`
(`expectation_eq_arenaObs`, `idxUnitary_detunedFlow`); `RecordLayer/DiracDetector.lean`
(`siteWeight`); `RecordLayer/GalileanTransformation.lean` (`trainF`);
`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean`
(`IsSymplectic.comp_eq_of_isMIntegralCurve_hamiltonianVectorField`);
`Mathlib/Analysis/Normed/Algebra/ExpUnique.lean` (`exp_smul_eq_of_hasDerivAt`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace DifferentialForm
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Reindexing commutes with the exponential -/

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reindexing commutes with `exp (t • ·)`: both sides solve `U' = (reindex X) U`, `U 0 = 1`. -/
theorem reindex_exp_smul (e : ι ≃ κ) (X : Matrix ι ι ℂ) (t : ℝ) :
    Matrix.reindex e e (exp (t • X)) = exp (t • Matrix.reindex e e X) := by
  let R : Matrix ι ι ℂ →L[ℝ] Matrix κ κ ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℝ ℂ e e).toLinearMap
  have hR : ∀ Y, R Y = Matrix.reindex e e Y := fun _ => rfl
  have hU : ∀ c : ℝ, HasDerivAt (fun c : ℝ => R (exp (c • X)))
      (Matrix.reindex e e X * R (exp (c • X))) c := by
    intro c
    have h := R.hasFDerivAt.comp_hasDerivAt c (hasDerivAt_exp_smul_const' X c)
    refine h.congr_deriv ?_
    rw [hR, hR, Matrix.reindex_mul]
  have h0 : (fun c : ℝ => R (exp (c • X))) 0 = 1 := by
    simp only [zero_smul, exp_zero, hR, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  have h := exp_smul_eq_of_hasDerivAt _ h0 hU t
  simpa only [hR] using h

end Reindex

/-! ### The index bridge -/

/-- **The index bridge**: `(site, component)` of the Dirac ring of `M + 1` sites as the index
`Fin (2M + 2)` of the projective sector of `Σ`. -/
def diracIdx (M : ℕ) : ZMod (M + 1) × Fin 2 ≃ Fin (2 * M + 1 + 1) :=
  (finProdFinEquiv (m := M + 1) (n := 2)).trans (finCongr (by omega))

/-- The bridge sends `(j, c)` to `c + 2j`. -/
theorem diracIdx_val (M : ℕ) (j : ZMod (M + 1)) (c : Fin 2) :
    ((diracIdx M (j, c) : Fin (2 * M + 1 + 1)) : ℕ) = c + 2 * j.val := rfl

/-- The Dirac arena `ℙ(ℂ^{ring × 2})` as the projective sector `ℂℙ^{2M+1}` of `Σ`. -/
noncomputable def diracArenaEquiv (M : ℕ) : GenArena (ZMod (M + 1) × Fin 2) ≃ CPN (2 * M + 1 + 1) :=
  idxArenaEquiv (diracIdx M)

/-! ### The site-occupancy projector -/

section Site

variable {L : ℕ} [NeZero L]

/-- **The site-occupancy projector** `P_j = Σ_c |j, c⟩⟨j, c|` of the Dirac ring. -/
def siteProj (j : ZMod L) : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ :=
  Matrix.diagonal fun p => if p.1 = j then 1 else 0

omit [NeZero L] in
theorem siteProj_isHermitian (j : ZMod L) : (siteProj j).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [siteProj, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    split_ifs <;> simp
  · simp [h, Ne.symm h]

/-- `P_j` is idempotent: with `siteProj_isHermitian`, an orthogonal projector. -/
theorem siteProj_mul_self (j : ZMod L) : siteProj j * siteProj j = siteProj j := by
  rw [siteProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

omit [NeZero L] in
/-- `P_j` is the sum of the two basis projectors of site `j`. -/
theorem siteProj_eq_single (j : ZMod L) :
    siteProj j = Matrix.single (j, 0) (j, 0) (1 : ℂ) + Matrix.single (j, 1) (j, 1) (1 : ℂ) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp only [siteProj, Matrix.diagonal_apply, Matrix.add_apply, Matrix.single_apply, Prod.mk.injEq]
  by_cases hk : j = k
  · subst hk
    by_cases hl : j = l
    · subst hl
      fin_cases a <;> fin_cases b <;> simp
    · fin_cases a <;> fin_cases b <;> simp [hl]
  · have hk' : ¬k = j := fun h => hk h.symm
    simp [hk, hk']

/-- ★ **The occupancy of site `j` at a ray** is the sum of its two moment coordinates. -/
theorem arenaObs_siteProj (j : ZMod L) (p : GenArena (ZMod L × Fin 2)) :
    arenaObs (siteProj j) p = momentMap p (j, 0) + momentMap p (j, 1) := by
  rw [siteProj_eq_single, arenaObs_add, arenaObs_single_eq_momentMap, arenaObs_single_eq_momentMap]

theorem arenaObs_siteProj_nonneg (j : ZMod L) (p : GenArena (ZMod L × Fin 2)) :
    0 ≤ arenaObs (siteProj j) p := by
  rw [arenaObs_siteProj]
  exact add_nonneg (momentMap_nonneg p _) (momentMap_nonneg p _)

theorem arenaObs_siteProj_le_one (j : ZMod L) (p : GenArena (ZMod L × Fin 2)) :
    arenaObs (siteProj j) p ≤ 1 := by
  rw [arenaObs_siteProj, ← momentMap_sum_eq_one p]
  have hne : ((j, 0) : ZMod L × Fin 2) ≠ (j, 1) := by simp
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i => momentMap p i) (Finset.subset_univ {((j, 0) : ZMod L × Fin 2), (j, 1)})
    (fun i _ _ => momentMap_nonneg p i)
  rwa [Finset.sum_pair hne] at h

/-- The occupancy at the ray of `ψ` is the site weight of `DiracDetector.lean` over `‖ψ‖²`. -/
theorem arenaObs_siteProj_mk (j : ZMod L) {v : EuclideanSpace ℂ (ZMod L × Fin 2)} (hv : v ≠ 0) :
    arenaObs (siteProj j) (Projectivization.mk ℂ v hv) = siteWeight v j / ‖v‖ ^ 2 := by
  rw [arenaObs_siteProj, momentMap_mk, momentMap_mk, siteWeight, Fin.sum_univ_two, add_div]

end Site

/-! ### The matrices on `Σ` -/

section Arena

variable {M : ℕ}

variable (M) in
/-- The Dirac Hamiltonian of the ring on `Σ`'s index. -/
noncomputable def diracA (J μ : ℝ) : Matrix (Fin (2 * M + 1 + 1)) (Fin (2 * M + 1 + 1)) ℂ :=
  Matrix.reindex (diracIdx M) (diracIdx M) (diracHam J μ)

/-- The occupancy of site `j`, scaled by the coupling `g`, on `Σ`'s index. -/
noncomputable def diracB (g : ℝ) (j : ZMod (M + 1)) :
    Matrix (Fin (2 * M + 1 + 1)) (Fin (2 * M + 1 + 1)) ℂ :=
  Matrix.reindex (diracIdx M) (diracIdx M) ((g : ℂ) • siteProj j)

variable (M) in
theorem diracA_isHermitian (J μ : ℝ) : (diracA M J μ).IsHermitian :=
  (diracHam_isHermitian J μ).reindex (diracIdx M)

theorem diracB_isHermitian (g : ℝ) (j : ZMod (M + 1)) : (diracB g j).IsHermitian :=
  ((siteProj_isHermitian j).smul
    (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal]))).reindex (diracIdx M)

theorem schrodingerHamiltonian_diracA (J μ : ℝ) (p : GenArena (ZMod (M + 1) × Fin 2)) :
    schrodingerHamiltonian (diracA M J μ) (diracArenaEquiv M p)
      = -2 * arenaObs (diracHam J μ) p := by
  rw [schrodingerHamiltonian, expectation_eq_arenaObs, diracA]
  exact congrArg (fun r : ℝ => -2 * r) (arenaObs_reindex (diracIdx M) _ p)

theorem schrodingerHamiltonian_diracB (g : ℝ) (j : ZMod (M + 1))
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    schrodingerHamiltonian (diracB g j) (diracArenaEquiv M p)
      = -(2 * g) * arenaObs (siteProj j) p := by
  rw [schrodingerHamiltonian, expectation_eq_arenaObs, diracB]
  have h : arenaObs (Matrix.reindex (diracIdx M) (diracIdx M) ((g : ℂ) • siteProj j))
      (diracArenaEquiv M p) = g * arenaObs (siteProj j) p :=
    (arenaObs_reindex (diracIdx M) _ p).trans (arenaObs_real_smul g _ p)
  rw [h]
  ring

/-! ### The energy -/

variable {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-- ★ **The joint energy of the Dirac carrier and the pointer on `Σ`**:
`−2⟨H_D⟩ − 2 g f(θ₂) ⟨P_j⟩`. -/
noncomputable def diracPointerEnergy : KSigma (2 * M + 1 + 1) → ℝ :=
  coupledEnergy (diracA M J μ) (diracB g j) hf

theorem contMDiff_diracPointerEnergy (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ArenaModel (2 * M + 1)) 𝓘(ℝ, ℝ) ∞ (diracPointerEnergy J μ g j hf) :=
  contMDiff_coupledEnergy (diracA M J μ) (diracB g j) hf hc

/-- ★★ **The energy is `−2⟨H_D⟩_p − 2 g f(θ₂) ⟨P_j⟩_p`**, read on the Dirac arena. -/
theorem diracPointerEnergy_eq (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) :
    diracPointerEnergy J μ g j hf (diracArenaEquiv M p, θ)
      = -2 * arenaObs (diracHam J μ) p - 2 * g * hf.lift θ.2 * arenaObs (siteProj j) p := by
  show coupledEnergy (diracA M J μ) (diracB g j) hf (diracArenaEquiv M p, θ) = _
  rw [coupledEnergy, schrodingerHamiltonian_diracA, schrodingerHamiltonian_diracB]
  show _ + _ * hf.lift θ.2 = _
  ring

/-! ### The carrier: `U̇ = −i (H_D + g f(θ₂) P_j) U` -/

/-- **The carrier's Hamiltonian at pointer angle `φ = θ₂`**: `H_D + g f(φ) P_j`. -/
noncomputable def diracPointerH (φ : AddCircle (1 : ℝ)) :
    Matrix (ZMod (M + 1) × Fin 2) (ZMod (M + 1) × Fin 2) ℂ :=
  diracHam J μ + ((g * hf.lift φ : ℝ) : ℂ) • siteProj j

theorem diracPointerH_isHermitian (φ : AddCircle (1 : ℝ)) :
    (diracPointerH J μ g j hf φ).IsHermitian :=
  (diracHam_isHermitian J μ).add ((siteProj_isHermitian j).smul
    (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal])))

/-- The state-dependent matrix of the coupled flow is the reindexed carrier Hamiltonian. -/
theorem coupledMatrix_diracPointer (φ : AddCircle (1 : ℝ)) :
    coupledMatrix (diracA M J μ) (diracB g j) hf φ
      = Matrix.reindex (diracIdx M) (diracIdx M) (diracPointerH J μ g j hf φ) := by
  unfold coupledMatrix diracA diracB diracPointerH
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  push_cast
  ring

theorem diracPointerGen_skew (φ : AddCircle (1 : ℝ)) :
    ((-Complex.I) • diracPointerH J μ g j hf φ)ᴴ
      = -((-Complex.I) • diracPointerH J μ g j hf φ) := by
  rw [Matrix.conjTranspose_smul, (diracPointerH_isHermitian J μ g j hf φ).eq]
  simp

/-- **The carrier's propagator** `exp (−i t (H_D + g f(φ) P_j))`, a unitary of the Dirac ring. -/
noncomputable def diracCarrierU (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    Matrix.unitaryGroup (ZMod (M + 1) × Fin 2) ℂ :=
  flowU (diracPointerGen_skew J μ g j hf φ) t

theorem diracCarrierU_val (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    (diracCarrierU J μ g j hf φ t).val = exp (t • ((-Complex.I) • diracPointerH J μ g j hf φ)) :=
  rfl

theorem diracCarrierU_zero (φ : AddCircle (1 : ℝ)) : diracCarrierU J μ g j hf φ 0 = 1 := by
  apply Subtype.ext
  rw [diracCarrierU_val, zero_smul, exp_zero]
  rfl

/-- ★★ **The carrier's equation**: `U̇(t) = −i (H_D + g f(θ₂) P_j) U(t)`, the lattice Dirac
equation with the pointer's static site potential. -/
theorem hasDerivAt_diracCarrierU (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (diracCarrierU J μ g j hf φ s).val)
      (((-Complex.I) • diracPointerH J μ g j hf φ) * (diracCarrierU J μ g j hf φ t).val) t :=
  hasDerivAt_exp_smul_const' ((-Complex.I) • diracPointerH J μ g j hf φ) t

/-- The reindexed carrier propagator is the Schrödinger unitary of the coupled matrix. -/
theorem idxUnitary_diracCarrierU (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxUnitary (diracIdx M) (diracCarrierU J μ g j hf φ t)
      = Matrix.schrodingerUnitary (coupledMatrix_isHermitian (diracA_isHermitian M J μ)
          (diracB_isHermitian g j) hf φ) t := by
  apply Subtype.ext
  rw [idxUnitary_val, diracCarrierU_val]
  show _ = exp (Matrix.schrodingerGen (coupledMatrix (diracA M J μ) (diracB g j) hf φ) t)
  rw [reindex_exp_smul, Matrix.schrodingerGen_eq_real_smul, coupledMatrix_diracPointer]
  congr 2

/-- The transported carrier orbit is the Schrödinger orbit of the coupled matrix. -/
theorem diracArenaEquiv_kick (φ : AddCircle (1 : ℝ)) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracArenaEquiv M (arenaKick (diracCarrierU J μ g j hf φ t) p)
      = Matrix.schrodingerUnitary (coupledMatrix_isHermitian (diracA_isHermitian M J μ)
          (diracB_isHermitian g j) hf φ) t • diracArenaEquiv M p := by
  rw [← idxUnitary_diracCarrierU, ← arenaKick_eq_smul']
  exact (arenaKick_reindex (diracIdx M) _ p).symm

/-! ### The pointer: `θ̇₁ = −2 g f'(θ₂) ⟨P_j⟩` -/

/-- **The pointer's lifted displacement**: `−2 g f'(φ) ∫₀ᵗ ⟨P_j⟩` along the carrier's orbit. -/
noncomputable def diracPointerShift (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    (t : ℝ) : ℝ :=
  -(2 * g) * hf.deriv_periodic.lift φ
    * ∫ s in (0 : ℝ)..t, arenaObs (siteProj j) (arenaKick (diracCarrierU J μ g j hf φ s) p)

theorem diracPointerShift_zero (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracPointerShift J μ g j hf φ p 0 = 0 := by
  rw [diracPointerShift, intervalIntegral.integral_same, mul_zero]

/-- Control: with the coupling off the pointer does not respond. -/
theorem diracPointerShift_zero_coupling (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) : diracPointerShift J μ 0 j hf φ p t = 0 := by
  rw [diracPointerShift, mul_zero, neg_zero, zero_mul, zero_mul]

/-- The accumulated `−2⟨B⟩` of the coupled flow is `−2g` times the accumulated occupancy. -/
theorem coupledAccum_diracPointer (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    (t : ℝ) :
    coupledAccum (diracA_isHermitian M J μ) (diracB_isHermitian g j) hf φ (diracArenaEquiv M p) t
      = -(2 * g) * ∫ s in (0 : ℝ)..t,
          arenaObs (siteProj j) (arenaKick (diracCarrierU J μ g j hf φ s) p) := by
  unfold coupledAccum
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show schrodingerHamiltonian (diracB g j) (Matrix.schrodingerUnitary _ s • diracArenaEquiv M p)
    = -(2 * g) * arenaObs (siteProj j) (arenaKick (diracCarrierU J μ g j hf φ s) p)
  rw [← diracArenaEquiv_kick, schrodingerHamiltonian_diracB]

theorem diracPointerShift_eq (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2))
    (t : ℝ) :
    hf.deriv_periodic.lift φ * coupledAccum (diracA_isHermitian M J μ) (diracB_isHermitian g j)
        hf φ (diracArenaEquiv M p) t
      = diracPointerShift J μ g j hf φ p t := by
  rw [coupledAccum_diracPointer, diracPointerShift]
  ring

/-- ★★ **The pointer's equation**: `θ̇₁ = −2 g f'(θ₂) ⟨P_j⟩_{p(t)}`, the occupancy of site `j` at
the carrier's current state. -/
theorem hasDerivAt_diracPointerShift (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    HasDerivAt (fun s => diracPointerShift J μ g j hf φ p s)
      (-(2 * g) * hf.deriv_periodic.lift φ
        * arenaObs (siteProj j) (arenaKick (diracCarrierU J μ g j hf φ t) p)) t := by
  have h := (hasDerivAt_coupledAccum (diracA_isHermitian M J μ) (diracB_isHermitian g j) hf φ
    (diracArenaEquiv M p) t).const_mul (hf.deriv_periodic.lift φ)
  rw [← diracArenaEquiv_kick, schrodingerHamiltonian_diracB] at h
  have hfun : (fun s => diracPointerShift J μ g j hf φ p s)
      = fun s => hf.deriv_periodic.lift φ * coupledAccum (diracA_isHermitian M J μ)
          (diracB_isHermitian g j) hf φ (diracArenaEquiv M p) s :=
    funext fun s => (diracPointerShift_eq J μ g j hf φ p s).symm
  rw [hfun]
  refine h.congr_deriv ?_
  ring

/-! ### The Hamiltonian flow -/

/-- ★ **The joint dynamics**: the Hamiltonian flow of `diracPointerEnergy` for the arena
symplectic form. -/
noncomputable def diracPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    KSigma (2 * M + 1 + 1) → KSigma (2 * M + 1 + 1) :=
  (arenaForm_isSymplectic (2 * M + 1)).hamiltonianFlow
    (contMDiff_diracPointerEnergy J μ g j hf hc) t

theorem diracPointerFlow_zero (hc : ContDiff ℝ ∞ f) (x : KSigma (2 * M + 1 + 1)) :
    diracPointerFlow J μ g j hf hc 0 x = x :=
  integralFlow_zero ((arenaForm_isSymplectic (2 * M + 1)).contMDiff_hamiltonianVectorField_tangent
    (contMDiff_diracPointerEnergy J μ g j hf hc)) x

theorem diracPointerFlow_add (hc : ContDiff ℝ ∞ f) (s t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    diracPointerFlow J μ g j hf hc (s + t) x
      = diracPointerFlow J μ g j hf hc s (diracPointerFlow J μ g j hf hc t x) :=
  integralFlow_add ((arenaForm_isSymplectic (2 * M + 1)).contMDiff_hamiltonianVectorField_tangent
    (contMDiff_diracPointerEnergy J μ g j hf hc)) s t x

/-- ★★★ **The coupled Dirac and pointer equations, solved.** The Hamiltonian flow of
`−2⟨H_D⟩ − 2 g f(θ₂) ⟨P_j⟩` moves the carrier by `exp (−i t (H_D + g f(θ₂) P_j))`, advances `θ₁`
by `−2 g f'(θ₂) ∫₀ᵗ ⟨P_j⟩` along that orbit, and fixes `θ₂`. -/
theorem diracPointerFlow_apply (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) :
    diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, θ)
      = (diracArenaEquiv M (arenaKick (diracCarrierU J μ g j hf θ.2 t) p),
          (θ.1 + ((diracPointerShift J μ g j hf θ.2 p t : ℝ) : AddCircle (1 : ℝ)), θ.2)) := by
  show (arenaForm_isSymplectic (2 * M + 1)).hamiltonianFlow
      (contMDiff_coupledEnergy (diracA M J μ) (diracB g j) hf hc) t (diracArenaEquiv M p, θ) = _
  rw [hamiltonianFlow_coupledEnergy (diracA_isHermitian M J μ) (diracB_isHermitian g j) hf hc,
    diracArenaEquiv_kick, diracPointerShift_eq]

/-- The angle `θ₂` is conserved. -/
theorem diracPointerFlow_snd_snd (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    (diracPointerFlow J μ g j hf hc t x).2.2 = x.2.2 := by
  obtain ⟨y, θ⟩ := x
  obtain ⟨p, rfl⟩ := (diracArenaEquiv M).surjective y
  rw [diracPointerFlow_apply]

/-- ★★ **The pointer component of the Hamiltonian vector field** of the joint energy is
`(−2 g f'(θ₂) ⟨P_j⟩, 0)`: the pointer's equation from `ι_X ω = d𝓗`, without the flow. -/
theorem hamiltonianVectorField_diracPointer_snd (hd : Differentiable ℝ f)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) :
    ((arenaForm_isSymplectic (2 * M + 1)).hamiltonianVectorField (diracPointerEnergy J μ g j hf)
        (diracArenaEquiv M p, θ) : ArenaModel (2 * M + 1)).2
      = (-(2 * g) * hf.deriv_periodic.lift θ.2 * arenaObs (siteProj j) p, 0) := by
  have h := congrFun (coupledField_eq_hamiltonianVectorField (diracA_isHermitian M J μ)
    (diracB_isHermitian g j) hf hd) (diracArenaEquiv M p, θ)
  have h2 : ((arenaForm_isSymplectic (2 * M + 1)).hamiltonianVectorField
      (diracPointerEnergy J μ g j hf) (diracArenaEquiv M p, θ) : ArenaModel (2 * M + 1)).2
      = (schrodingerHamiltonian (diracB g j) (diracArenaEquiv M p)
          * hf.deriv_periodic.lift θ.2, 0) :=
    (congrArg (fun v : ArenaModel (2 * M + 1) => v.2) h).symm
  rw [h2, schrodingerHamiltonian_diracB]
  congr 1
  ring

/-! ### Conservation -/

/-- ★★ **Energy conservation**: the joint energy is constant along the joint flow. -/
theorem diracPointerEnergy_flow (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    diracPointerEnergy J μ g j hf (diracPointerFlow J μ g j hf hc t x)
      = diracPointerEnergy J μ g j hf x := by
  have hH := contMDiff_diracPointerEnergy J μ g j hf hc
  have hγ := isMIntegralCurve_integralFlow
    ((arenaForm_isSymplectic (2 * M + 1)).contMDiff_hamiltonianVectorField_tangent hH) x
  have h := (arenaForm_isSymplectic (2 * M + 1)).comp_eq_of_isMIntegralCurve_hamiltonianVectorField
    (diracPointerEnergy J μ g j hf) (hH.mdifferentiable (by simp)) hγ t 0
  rw [integralFlow_zero] at h
  exact h

/-- ★★ **Liouville**: the joint flow preserves the arena volume of `arenaForm ^ (2M + 2)`. -/
theorem arenaVolume_map_diracPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Measure.map (diracPointerFlow J μ g j hf hc t) (arenaVolume (2 * M + 1))
      = arenaVolume (2 * M + 1) :=
  arenaVolume_map_hamiltonianFlow (contMDiff_diracPointerEnergy J μ g j hf hc) t

/-- **Liouville for the corpus's `μ_FS ⊗ vol_{T²}`.** -/
theorem kMuL_map_diracPointerFlow (hc : ContDiff ℝ ∞ f) (p₀ : CPN (2 * M + 1 + 1)) (t : ℝ) :
    Measure.map (diracPointerFlow J μ g j hf hc t) (kMuL p₀) = kMuL p₀ :=
  kMuL_map_hamiltonianFlow (2 * M + 1) p₀ (contMDiff_diracPointerEnergy J μ g j hf hc) t

end Arena

/-! ### The checked special case: the coupling is not identically zero -/

section Check

theorem contDiff_trainF : ContDiff ℝ ∞ trainF := by
  unfold trainF
  exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).neg).div_const _

theorem trainF_lift_zero : trainF_periodic.lift (0 : AddCircle (1 : ℝ)) = 0 := by
  show trainF_periodic.lift (((0 : ℝ) : AddCircle (1 : ℝ))) = 0
  rw [Function.Periodic.lift_coe]
  simp [trainF]

theorem trainF_deriv_lift_zero :
    trainF_periodic.deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -1 := by
  show trainF_periodic.deriv_periodic.lift (((0 : ℝ) : AddCircle (1 : ℝ))) = -1
  rw [Function.Periodic.lift_coe, (hasDerivAt_trainF 0).deriv]
  simp

variable {L : ℕ} [NeZero L]

/-- The carrier localised on site `j` (first component). -/
noncomputable def siteRay (j : ZMod L) : GenArena (ZMod L × Fin 2) :=
  Projectivization.mk ℂ (EuclideanSpace.single (j, 0) (1 : ℂ))
    (fun h => by simpa using congrArg (fun v : EuclideanSpace ℂ (ZMod L × Fin 2) => v (j, 0)) h)

/-- The carrier on site `j` occupies site `j`. -/
theorem arenaObs_siteProj_siteRay (j : ZMod L) : arenaObs (siteProj j) (siteRay j) = 1 := by
  rw [siteRay, arenaObs_siteProj, momentMap_mk, momentMap_mk]
  simp

/-- Locality of the read-out: the carrier on site `j` does not occupy any other site. -/
theorem arenaObs_siteProj_siteRay_of_ne {j k : ZMod L} (h : k ≠ j) :
    arenaObs (siteProj k) (siteRay j) = 0 := by
  rw [siteRay, arenaObs_siteProj, momentMap_mk, momentMap_mk]
  simp [h]

variable {M : ℕ} (J μ g : ℝ) (j : ZMod (M + 1))

/-- On the fibre `θ₂ = 0` of the profile `trainF` the carrier runs the free Dirac Hamiltonian. -/
theorem diracPointerH_trainF_zero :
    diracPointerH J μ g j trainF_periodic 0 = diracHam J μ := by
  rw [diracPointerH, trainF_lift_zero, mul_zero, Complex.ofReal_zero, zero_smul, add_zero]

/-- ★★ **The pointer responds**: with the carrier on site `j` and the pointer at `θ₂ = 0`, the
pointer's rate at `t = 0` is `2g`. -/
theorem hasDerivAt_diracPointerShift_siteRay :
    HasDerivAt (fun s => diracPointerShift J μ g j trainF_periodic 0 (siteRay j) s) (2 * g) 0 := by
  have h := hasDerivAt_diracPointerShift J μ g j trainF_periodic 0 (siteRay j) 0
  rw [diracCarrierU_zero, arenaKick_eq_smul', one_smul, arenaObs_siteProj_siteRay,
    trainF_deriv_lift_zero] at h
  refine h.congr_deriv ?_
  ring

/-- Locality: a detector at another site `k ≠ j` starts at rate `0`. -/
theorem hasDerivAt_diracPointerShift_siteRay_of_ne {k : ZMod (M + 1)} (h : k ≠ j) :
    HasDerivAt (fun s => diracPointerShift J μ g k trainF_periodic 0 (siteRay j) s) 0 0 := by
  have h' := hasDerivAt_diracPointerShift J μ g k trainF_periodic 0 (siteRay j) 0
  rw [diracCarrierU_zero, arenaKick_eq_smul', one_smul, arenaObs_siteProj_siteRay_of_ne h,
    mul_zero] at h'
  exact h'

/-- ★★ **The same rate from the vector field**, independently of the flow: at the carrier on site
`j` and the pointer at `(0, 0)`, the Hamiltonian vector field has pointer component `(2g, 0)`. -/
theorem hamiltonianVectorField_diracPointer_siteRay :
    ((arenaForm_isSymplectic (2 * M + 1)).hamiltonianVectorField
        (diracPointerEnergy J μ g j trainF_periodic)
        (diracArenaEquiv M (siteRay j), ((0, 0) : KTorus)) : ArenaModel (2 * M + 1)).2
      = (2 * g, 0) := by
  rw [hamiltonianVectorField_diracPointer_snd J μ g j trainF_periodic
    (contDiff_trainF.differentiable (by simp)), arenaObs_siteProj_siteRay]
  show (-(2 * g) * trainF_periodic.deriv_periodic.lift (0 : AddCircle (1 : ℝ)) * 1, (0 : ℝ)) = _
  rw [trainF_deriv_lift_zero]
  congr 1
  ring

/-- ★★★ **A verified nontrivial interaction**: for `g ≠ 0`, the Hamiltonian flow of the joint
energy moves the pointer. Starting from the carrier on site `j` and the pointer at `(0, 0)`, at
some time the pointer's `θ₁` is not `0`. -/
theorem exists_diracPointerFlow_pointer_ne (hg : g ≠ 0) :
    ∃ t : ℝ, (diracPointerFlow J μ g j trainF_periodic contDiff_trainF t
      (diracArenaEquiv M (siteRay j), ((0, 0) : KTorus))).2.1 ≠ 0 := by
  set D : ℝ → ℝ := fun s => diracPointerShift J μ g j trainF_periodic 0 (siteRay j) s with hDdef
  have hD : HasDerivAt D (2 * g) 0 := hasDerivAt_diracPointerShift_siteRay J μ g j
  have hD0 : D 0 = 0 := diracPointerShift_zero J μ g j trainF_periodic 0 (siteRay j)
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), D t ≠ 0 :=
    hD.eventually_ne (mul_ne_zero two_ne_zero hg)
  have hlt : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |D t| < 1 := by
    have h : ∀ᶠ t in 𝓝 (0 : ℝ), |D t| < 1 := by
      have hc : Filter.Tendsto (fun t => |D t|) (𝓝 0) (𝓝 |D 0|) := hD.continuousAt.abs
      rw [hD0, abs_zero] at hc
      exact hc.eventually (gt_mem_nhds one_pos)
    exact h.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht0, ht1⟩ := (hne.and hlt).exists
  refine ⟨t, ?_⟩
  rw [diracPointerFlow_apply]
  show (0 : AddCircle (1 : ℝ)) + ((D t : ℝ) : AddCircle (1 : ℝ)) ≠ 0
  rw [zero_add]
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
  have hn' : (n : ℝ) = D t := by simpa using hn
  have hn0 : n = 0 := by
    have : |(n : ℝ)| < 1 := hn' ▸ ht1
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  exact ht0 (by rw [← hn', hn0, Int.cast_zero])

/-- ★★★ **A Dirac carrier and a pointer in one Hamiltonian arena.** On `Σ = ℂℙ^{2M+1} × T²` with
the arena symplectic form: the joint energy `−2⟨H_D⟩ − 2 g f(θ₂) ⟨P_j⟩` is smooth; its Hamiltonian
flow moves the carrier by `exp (−i t (H_D + g f(θ₂) P_j))` and the pointer by
`θ̇₁ = −2 g f'(θ₂) ⟨P_j⟩`, with `θ₂` fixed; the energy and the arena volume are conserved; and for
the profile `trainF` and `g ≠ 0` the pointer moves. -/
theorem diracPointer_hamiltonian {f : ℝ → ℝ} (hf : Function.Periodic f 1)
    (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ArenaModel (2 * M + 1)) 𝓘(ℝ, ℝ) ∞ (diracPointerEnergy J μ g j hf)
      ∧ (∀ (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus),
          diracPointerEnergy J μ g j hf (diracArenaEquiv M p, θ)
            = -2 * arenaObs (diracHam J μ) p - 2 * g * hf.lift θ.2 * arenaObs (siteProj j) p)
      ∧ (∀ (t : ℝ) (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus),
          diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, θ)
            = (diracArenaEquiv M (arenaKick (diracCarrierU J μ g j hf θ.2 t) p),
                (θ.1 + ((diracPointerShift J μ g j hf θ.2 p t : ℝ) : AddCircle (1 : ℝ)), θ.2)))
      ∧ (∀ (φ : AddCircle (1 : ℝ)) (t : ℝ),
          HasDerivAt (fun s : ℝ => (diracCarrierU J μ g j hf φ s).val)
            (((-Complex.I) • diracPointerH J μ g j hf φ) * (diracCarrierU J μ g j hf φ t).val) t)
      ∧ (∀ (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ),
          HasDerivAt (fun s => diracPointerShift J μ g j hf φ p s)
            (-(2 * g) * hf.deriv_periodic.lift φ
              * arenaObs (siteProj j) (arenaKick (diracCarrierU J μ g j hf φ t) p)) t)
      ∧ (∀ (t : ℝ) (x : KSigma (2 * M + 1 + 1)),
          diracPointerEnergy J μ g j hf (diracPointerFlow J μ g j hf hc t x)
            = diracPointerEnergy J μ g j hf x)
      ∧ (∀ t : ℝ, Measure.map (diracPointerFlow J μ g j hf hc t) (arenaVolume (2 * M + 1))
          = arenaVolume (2 * M + 1))
      ∧ (g ≠ 0 → ∃ t : ℝ, (diracPointerFlow J μ g j trainF_periodic contDiff_trainF t
          (diracArenaEquiv M (siteRay j), ((0, 0) : KTorus))).2.1 ≠ 0) :=
  ⟨contMDiff_diracPointerEnergy J μ g j hf hc, diracPointerEnergy_eq J μ g j hf,
    diracPointerFlow_apply J μ g j hf hc, hasDerivAt_diracCarrierU J μ g j hf,
    hasDerivAt_diracPointerShift J μ g j hf, diracPointerEnergy_flow J μ g j hf hc,
    arenaVolume_map_diracPointerFlow J μ g j hf hc, exists_diracPointerFlow_pointer_ne J μ g j⟩

end Check

end CSD.RecordLayer

end
