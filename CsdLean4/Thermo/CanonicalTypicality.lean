/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.BornFS
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# TH1: canonical typicality -- thermal equilibrium from Fubini-Study volume

**Category:** conceptually 1-Mathlib (CSD-free general quantum statistical
mechanics on the Fubini-Study Kaehler structure); kept under `CSD.Thermo` as the
flagship first tranche of the thermodynamics track (`specs/thermo-plan.md`, TH1).

## What is proved (the achievable core, EXPECTATION only)

For a global pure state drawn from the Fubini-Study measure `mu_FS` on
`CP^{N-1}`, the *average* density operator is maximally mixed, and the *average*
reduced state of any tensor subsystem is maximally mixed on that subsystem:

- `fs_first_moment`: `E_{mu_FS}[ |psi><psi| ] = (1/N) I` on `CP^{N-1}`. The
  average pure-state density matrix over Fubini-Study is `(1/N) I_N`. A genuine
  integral computation via Fubini-Study U(N)-invariance (a "twirl" / Schur
  argument executed entrywise): permutation invariance forces all diagonal
  entries equal (each `1/N` by normalisation and `momentMap_sum_eq_one`), and a
  sign-flip diagonal unitary forces every off-diagonal entry to zero.
- `canonical_typicality_expectation`: for `H = H_S (x) H_E` with `N = d_S * d_E`,
  the average reduced state `E_{mu_FS}[ Tr_E |psi><psi| ] = (1/d_S) I_S`. The
  headline: partial-tracing the Fubini-Study first moment gives the canonical
  (maximally mixed, equal-energy / microcanonical) state on the subsystem. This
  is the FS-average ANALOGUE of `LF6.maxEntangled_marginal_uniform` (which gives
  the maximally-mixed marginal for the one specific maximally-entangled state):
  here the maximally-mixed reduced state arises for the Fubini-Study *average*
  over all pure states. (Analogy at the mathematical level, not a formal Lean
  dependency: this theorem does not cite that lemma.)

## Honest scope (load-bearing)

**EXPECTATION, not TYPICAL.** This tranche proves the reduced state is canonical
*in expectation* over `mu_FS`. The strictly stronger *typical-state*
(concentration / Levy) statement -- that a `mu_FS`-typical single pure state has a
reduced state close to `I_S/d_S` with probability `1 - O(exp(-c d_E))` for a small
subsystem in a large environment (Popescu-Short-Winter / Goldstein-Lebowitz-
Tumulka-Zanghi) -- is the named residual (see the `Concentration residual` section
below). It is NOT proved here: it needs measure concentration on high-dimensional
spheres (Levy's lemma: Lipschitz + isoperimetry), which Mathlib does not carry.
No `sorry`, no axiom is used to paper over this; the average is what lands.

**NOT dynamical thermalisation.** This is a typicality (volume-average) statement,
not a proof that a given initial state thermalises under a dynamics (that needs
mixing / ETH, out of scope).

**CSD reading.** Born-from-volume (the moment-map / Duistermaat-Heckman cluster,
`fs_born_volume_ratio_N`, Gleason-free) becomes thermal-equilibrium-from-volume:
the canonical subsystem state is the Fubini-Study volume-average. The
CSD-distinctive claim that this equilibrium *emerges from deterministic
microdynamics* rests on the A5 (sector / typicality-law posit) and D1 (dynamics)
residues shared with all of LF4/LF6; this file posits `mu_FS` as the sampling law
(A5) and proves the statistical-mechanical consequence, it does not derive `mu_FS`
from a flow.

All results are foundational-triple-only (no `busch_effect_gleason`, no
`native_decide`, no `sorry`).

Reference: `specs/thermo-plan.md` (TH1).
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators ComplexConjugate

namespace CSD
namespace Thermo

open CSD.LF4

variable {N : ℕ}

/-! ## The density matrix entry of a projective ray -/

/-- **The density-matrix entry of a ray.** For a projective point `p`, the
`(i, j)` entry of the rank-1 density operator `|psi><psi| / ‖psi‖²` of any
representative. Fully scale-invariant (both modulus and phase cancel), so it is a
genuine function of the ray. Diagonal entries are the moment-map coordinates
(`rayDensity_diag`). -/
noncomputable def rayDensity (p : CPN N) (i j : Fin N) : ℂ :=
  p.rep i * conj (p.rep j) / ((‖p.rep‖ : ℂ) ^ 2)

/-- Scale-invariance of the density entry under nonzero rescaling of the vector. -/
lemma rayDensity_smul (c : ℂ) (hc : c ≠ 0) (v : EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    (c • v) i * conj ((c • v) j) / ((‖c • v‖ : ℂ) ^ 2)
      = v i * conj (v j) / ((‖v‖ : ℂ) ^ 2) := by
  have hc2 : ((‖c‖ : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast (norm_ne_zero_iff.mpr hc))
  rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, norm_smul]
  push_cast
  rw [mul_pow]
  rw [show c * v i * (conj c * conj (v j)) = (c * conj c) * (v i * conj (v j)) by ring]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [mul_div_mul_left _ _ hc2]

/-- The density entry on a representative `psi`: scale-invariant, so it descends
from the vector. -/
lemma rayDensity_mk (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0) (i j : Fin N) :
    rayDensity (Projectivization.mk ℂ ψ hψ) i j
      = ψ i * conj (ψ j) / ((‖ψ‖ : ℂ) ^ 2) := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ ψ hψ).rep ψ
        (Projectivization.rep_nonzero _) hψ).mp (Projectivization.mk_rep _)
  unfold rayDensity
  rw [← ha]
  simp only [Units.smul_def]
  exact rayDensity_smul (↑a) (Units.ne_zero a) ψ i j

/-- **The diagonal density entries are the moment-map coordinates**
(`rayDensity p i i = |psi_i|²/‖psi‖² = momentMap p i`). This is what links the
first moment's diagonal to the Duistermaat-Heckman / Born content. -/
lemma rayDensity_diag (p : CPN N) (i : Fin N) :
    rayDensity p i i = ((momentMap p i : ℝ) : ℂ) := by
  unfold rayDensity momentMap
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-! ## Measurability, boundedness, integrability -/

/-- A single coordinate norm is bounded by the vector norm. -/
lemma coord_norm_le (v : EuclideanSpace ℂ (Fin N)) (i : Fin N) : ‖v i‖ ≤ ‖v‖ := by
  have h : ‖v i‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [euclidean_norm_sq_eq_sum]
    exact Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖v i‖ = Real.sqrt (‖v i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)

/-- **The density entries are measurable** on `CP^{N-1}`. Scale-invariant, so it
descends from the measurable coordinate function on the nonzero subtype
(same `measurable_iff_measurable_comp_mk'` route as `momentMap_measurable`). -/
lemma rayDensity_measurable (i j : Fin N) :
    Measurable (fun p : CPN N => rayDensity p i j) := by
  borelize (EuclideanSpace ℂ (Fin N))
  rw [Projectivization.measurable_iff_measurable_comp_mk']
  have hcomp : (fun p : CPN N => rayDensity p i j) ∘ (Projectivization.mk' ℂ)
      = fun w : { v : EuclideanSpace ℂ (Fin N) // v ≠ 0 } =>
          (w : EuclideanSpace ℂ (Fin N)) i * conj ((w : EuclideanSpace ℂ (Fin N)) j)
            / ((‖(w : EuclideanSpace ℂ (Fin N))‖ : ℂ) ^ 2) := by
    funext w
    show rayDensity (Projectivization.mk ℂ (w : EuclideanSpace ℂ (Fin N)) w.2) i j = _
    rw [rayDensity_mk]
  rw [hcomp]
  refine Measurable.div ?_ ?_
  · refine Measurable.mul ?_ ?_
    · exact (((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).measurable)
    · exact (Complex.continuous_conj.comp
        ((EuclideanSpace.proj j).continuous.comp continuous_subtype_val)).measurable
  · exact ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.norm)).pow 2).measurable

/-- **The density entries are bounded by one.** `‖rayDensity p i j‖ ≤ 1`
(coordinate norms bounded by the vector norm). -/
lemma rayDensity_norm_le_one (p : CPN N) (i j : Fin N) : ‖rayDensity p i j‖ ≤ 1 := by
  have hpos : (0 : ℝ) < ‖p.rep‖ ^ 2 := pow_pos (norm_pos_iff.mpr p.rep_nonzero) 2
  unfold rayDensity
  rw [norm_div, norm_mul, RCLike.norm_conj]
  rw [show ‖((‖p.rep‖ : ℂ) ^ 2)‖ = ‖p.rep‖ ^ 2 by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]]
  rw [div_le_one hpos, sq]
  exact mul_le_mul (coord_norm_le p.rep i) (coord_norm_le p.rep j)
    (norm_nonneg _) (norm_nonneg _)

/-- The density entries are integrable against Fubini-Study (bounded + measurable
on a probability measure). -/
lemma rayDensity_integrable (p₀ : CPN N) (i j : Fin N) :
    Integrable (fun p => rayDensity p i j) (fubiniStudyMeasure p₀) :=
  Integrable.of_bound (rayDensity_measurable i j).aestronglyMeasurable 1
    (ae_of_all _ (fun p => rayDensity_norm_le_one p i j))

/-- The moment coordinate is integrable against Fubini-Study. -/
lemma momentMap_integrable (p₀ : CPN N) (i : Fin N) :
    Integrable (fun p => momentMap p i) (fubiniStudyMeasure p₀) :=
  Integrable.of_bound (momentMap_measurable i).aestronglyMeasurable 1
    (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (momentMap_nonneg p i)]
      exact momentMap_le_one p i))

/-! ## The two symmetry unitaries: sign flip and permutation -/

/-- A general nonzero-preservation for the unitary matrix action (local re-proof;
the corpus's `toEuclideanLin_unitary_ne_zero` is `private`). -/
lemma toLin_unit_ne_zero (U : Matrix.unitaryGroup (Fin N) ℂ)
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  exact hv ((toEuclideanLinearEquiv U).injective (h.trans (LinearEquiv.map_zero _).symm))

/-- The projective unitary action, written as `mk` of the matrix action on `rep`. -/
lemma smul_eq_mk [NeZero N] (U : Matrix.unitaryGroup (Fin N) ℂ) (p : CPN N) :
    U • p = Projectivization.mk ℂ ((Matrix.toEuclideanLin U.val) p.rep)
      (toLin_unit_ne_zero U p.rep_nonzero) := by
  conv_lhs => rw [← p.mk_rep]
  exact smul_mk_eq_mk U p.rep p.rep_nonzero

/-- **The sign-flip matrix** `diag(1, ..., -1, ..., 1)` with `-1` at index `i`.
A real diagonal `±1` unitary; used to kill off-diagonal first-moment entries. -/
noncomputable def signFlipMat (i : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun k => if k = i then -1 else 1)

lemma signFlipMat_mem (i : Fin N) : signFlipMat i ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar : star (signFlipMat i) = signFlipMat i := by
    rw [signFlipMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    rw [Pi.star_apply]
    split_ifs <;> simp
  rw [hstar]
  simp only [signFlipMat, Matrix.diagonal_mul_diagonal]
  rw [show (fun k : Fin N => (if k = i then (-1 : ℂ) else 1) * if k = i then -1 else 1)
        = (1 : Fin N → ℂ) by funext k; simp only [Pi.one_apply]; split_ifs <;> norm_num]
  exact Matrix.diagonal_one

/-- The sign-flip unitary as a group element. -/
noncomputable def signFlip (i : Fin N) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨signFlipMat i, signFlipMat_mem i⟩

@[simp] lemma signFlip_val (i : Fin N) : (signFlip i).val = signFlipMat i := rfl

/-- Coordinate action of the sign-flip. -/
lemma toEuclideanLin_signFlip_coord (i : Fin N) (v : EuclideanSpace ℂ (Fin N)) (a : Fin N) :
    (Matrix.toEuclideanLin (signFlipMat i) v) a = (if a = i then -1 else 1) * v a := by
  rw [signFlipMat, Matrix.toLpLin_apply]
  simp [Matrix.mulVec_diagonal]

/-- The sign-flip is norm-preserving (squared form). -/
lemma signFlip_normSq (i : Fin N) (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin (signFlipMat i) v)‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [toEuclideanLin_signFlip_coord, norm_mul]
  rw [show ‖(if a = i then (-1 : ℂ) else 1)‖ = 1 by split_ifs <;> simp, one_mul]

/-- **The permutation matrix** of `sigma`, packaged as a unitary group element. -/
noncomputable def permU (σ : Equiv.Perm (Fin N)) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨Equiv.Perm.permMatrix ℂ σ, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
        Matrix.permMatrix_one]⟩

@[simp] lemma permU_val (σ : Equiv.Perm (Fin N)) : (permU σ).val = Equiv.Perm.permMatrix ℂ σ := rfl

/-- Coordinate action of a permutation unitary: `(P_sigma v)_a = v_{sigma a}`. -/
lemma toEuclideanLin_perm_coord (σ : Equiv.Perm (Fin N)) (v : EuclideanSpace ℂ (Fin N))
    (a : Fin N) :
    (Matrix.toEuclideanLin (Equiv.Perm.permMatrix ℂ σ) v) a = v (σ a) := by
  rw [Matrix.toLpLin_apply]
  simp [Matrix.permMatrix_mulVec]

/-- Permutation unitaries are norm-preserving. -/
lemma perm_normSq (σ : Equiv.Perm (Fin N)) (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin (Equiv.Perm.permMatrix ℂ σ) v)‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
  have h1 : ∀ a, ‖(Matrix.toEuclideanLin (Equiv.Perm.permMatrix ℂ σ) v) a‖ ^ 2 = ‖v (σ a)‖ ^ 2 := by
    intro a; rw [toEuclideanLin_perm_coord]
  simp_rw [h1]
  exact Equiv.sum_comp σ (fun a => ‖v a‖ ^ 2)

/-! ## The moment map transforms by permutation of coordinates -/

/-- **Permutation equivariance of the moment map.**
`momentMap (P_sigma . p) a = momentMap p (sigma a)`. -/
lemma momentMap_permU [NeZero N] (σ : Equiv.Perm (Fin N)) (p : CPN N) (a : Fin N) :
    momentMap ((permU σ) • p) a = momentMap p (σ a) := by
  rw [smul_eq_mk, momentMap_mk]
  unfold momentMap
  rw [permU_val, toEuclideanLin_perm_coord, perm_normSq]

/-! ## Off-diagonal first-moment entries vanish (sign-flip symmetry) -/

/-- The sign-flip sends an off-diagonal density entry to its negative:
`rayDensity ((signFlip i) . p) i j = - rayDensity p i j` for `j ≠ i`. -/
lemma signFlip_smul_offdiag [NeZero N] (i j : Fin N) (hji : j ≠ i) (p : CPN N) :
    rayDensity ((signFlip i) • p) i j = - rayDensity p i j := by
  rw [smul_eq_mk, rayDensity_mk, signFlip_val, toEuclideanLin_signFlip_coord,
      toEuclideanLin_signFlip_coord, if_pos rfl, if_neg hji, one_mul, neg_one_mul]
  have hden : (‖(Matrix.toEuclideanLin (signFlipMat i) p.rep)‖ : ℂ) ^ 2 = (‖p.rep‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, signFlip_normSq, Complex.ofReal_pow]
  rw [hden]
  unfold rayDensity
  ring

/-- **The Fubini-Study first moment is diagonal: off-diagonal entries vanish.**
For `i ≠ j`, `E_{mu_FS}[ rayDensity . i j ] = 0`. Genuine change-of-variables
against the sign-flip unitary (Fubini-Study invariance) plus the pointwise
sign flip: `M = -M`. -/
theorem fsFirstMoment_offdiag [NeZero N] (p₀ : CPN N) (i j : Fin N) (hij : i ≠ j) :
    ∫ p, rayDensity p i j ∂(fubiniStudyMeasure p₀) = 0 := by
  set μ := fubiniStudyMeasure p₀ with hμ
  set g : CPN N → CPN N := fun p => (signFlip i) • p with hg_def
  have hg : Measurable g := (continuous_const_smul (signFlip i)).measurable
  have hinv : Measure.map g μ = μ := fubiniStudyMeasure_smul_invariant (signFlip i) p₀
  have hf : AEStronglyMeasurable (fun p => rayDensity p i j) μ :=
    (rayDensity_measurable i j).aestronglyMeasurable
  have hchange : ∫ p, rayDensity p i j ∂μ = ∫ p, rayDensity (g p) i j ∂μ := by
    calc ∫ p, rayDensity p i j ∂μ
        = ∫ p, rayDensity p i j ∂(Measure.map g μ) := by rw [hinv]
      _ = ∫ p, rayDensity (g p) i j ∂μ :=
          integral_map hg.aemeasurable (by rw [hinv]; exact hf)
  have hpt : (fun p => rayDensity (g p) i j) = fun p => - rayDensity p i j := by
    funext p; exact signFlip_smul_offdiag i j hij.symm p
  have hstep : ∫ p, rayDensity (g p) i j ∂μ = - ∫ p, rayDensity p i j ∂μ := by
    rw [hpt, integral_neg]
  have hMM : ∫ p, rayDensity p i j ∂μ = - ∫ p, rayDensity p i j ∂μ := hchange.trans hstep
  have hsum : ∫ p, rayDensity p i j ∂μ + ∫ p, rayDensity p i j ∂μ = 0 := by
    nth_rewrite 2 [hMM]; ring
  have h2 : (2 : ℂ) * (∫ p, rayDensity p i j ∂μ) = 0 := by rw [two_mul]; exact hsum
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-! ## Diagonal first-moment entries equal `1/N` (permutation symmetry) -/

/-- **Diagonal first-moment entries are equal across coordinates** (permutation
symmetry): `E[momentMap . i] = E[momentMap . k]`. -/
theorem fsFirstMoment_diag_swap [NeZero N] (p₀ : CPN N) (i k : Fin N) :
    ∫ p, momentMap p i ∂(fubiniStudyMeasure p₀)
      = ∫ p, momentMap p k ∂(fubiniStudyMeasure p₀) := by
  set μ := fubiniStudyMeasure p₀ with hμ
  set σ := Equiv.swap i k with hσ
  set g : CPN N → CPN N := fun p => (permU σ) • p with hg_def
  have hg : Measurable g := (continuous_const_smul (permU σ)).measurable
  have hinv : Measure.map g μ = μ := fubiniStudyMeasure_smul_invariant (permU σ) p₀
  have hf : AEStronglyMeasurable (fun p => momentMap p i) μ :=
    (momentMap_measurable i).aestronglyMeasurable
  calc ∫ p, momentMap p i ∂μ
      = ∫ p, momentMap p i ∂(Measure.map g μ) := by rw [hinv]
    _ = ∫ p, momentMap (g p) i ∂μ := integral_map hg.aemeasurable (by rw [hinv]; exact hf)
    _ = ∫ p, momentMap p (σ i) ∂μ := by simp_rw [hg_def, momentMap_permU]
    _ = ∫ p, momentMap p k ∂μ := by rw [Equiv.swap_apply_left]

/-- **The diagonal first-moment entry is `1/N`.** All `N` diagonal integrals are
equal (permutation symmetry) and sum to `1` (`momentMap_sum_eq_one` +
`measure_univ`), so each is `1/N`. -/
theorem fsFirstMoment_diag [NeZero N] (p₀ : CPN N) (i : Fin N) :
    ∫ p, momentMap p i ∂(fubiniStudyMeasure p₀) = (N : ℝ)⁻¹ := by
  set μ := fubiniStudyMeasure p₀ with hμ
  have hall : ∀ k : Fin N, ∫ p, momentMap p k ∂μ = ∫ p, momentMap p i ∂μ :=
    fun k => (fsFirstMoment_diag_swap p₀ i k).symm
  have hsum : ∑ k : Fin N, ∫ p, momentMap p k ∂μ = 1 := by
    rw [← integral_finsetSum Finset.univ (fun k _ => momentMap_integrable p₀ k)]
    have hone : (fun p => ∑ k : Fin N, momentMap p k) = fun _ => (1 : ℝ) := by
      funext p; exact momentMap_sum_eq_one p
    rw [hone, integral_const, probReal_univ, one_smul]
  have hNc : (N : ℝ) * (∫ p, momentMap p i ∂μ) = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun k _ => hall k), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp
  linear_combination hNc

/-! ## Deliverable 1: the Fubini-Study first moment -/

/-- **The Fubini-Study first-moment matrix** `E_{mu_FS}[ |psi><psi| ]`, entrywise. -/
noncomputable def fsFirstMoment (p₀ : CPN N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ∫ p, rayDensity p i j ∂(fubiniStudyMeasure p₀)

/-- **Deliverable 1 (the key lemma): the Fubini-Study first moment is maximally
mixed.** `E_{mu_FS}[ |psi><psi| ] = (1/N) I` on `CP^{N-1}`. The average pure-state
density operator over Fubini-Study is the maximally mixed state. Proved by a
genuine integral computation: off-diagonal entries vanish by sign-flip invariance
(`fsFirstMoment_offdiag`), diagonal entries are `1/N` by permutation invariance +
normalisation (`fsFirstMoment_diag`). Foundational-triple, Gleason-free. -/
theorem fs_first_moment [NeZero N] (p₀ : CPN N) :
    fsFirstMoment p₀ = ((N : ℂ)⁻¹) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  rw [fsFirstMoment, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, mul_one]
    have hfun : (fun p => rayDensity p i i) = fun p => ((momentMap p i : ℝ) : ℂ) := by
      funext p; exact rayDensity_diag p i
    have hof : ∫ p, ((momentMap p i : ℝ) : ℂ) ∂(fubiniStudyMeasure p₀)
        = ((∫ p, momentMap p i ∂(fubiniStudyMeasure p₀) : ℝ) : ℂ) := integral_ofReal
    rw [hfun, hof, fsFirstMoment_diag p₀ i, Complex.ofReal_inv, Complex.ofReal_natCast]
  · rw [if_neg h, mul_zero]
    exact fsFirstMoment_offdiag p₀ i j h

/-! ## Deliverable 2: canonical typicality in expectation (the headline) -/

variable {dS dE : ℕ}

/-- The rank-1 density matrix of a ray as a genuine `Matrix`. -/
noncomputable def rayDensityMat (p : CPN N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (rayDensity p)

/-- The **reduced density matrix** of a ray, obtained by reindexing along a
system-environment tensor split `e : Fin d_S × Fin d_E ≃ Fin N` and taking the
partial trace over the environment (`Matrix.traceRight`, the genuine corpus
partial trace). -/
noncomputable def reducedRayDensity (e : Fin dS × Fin dE ≃ Fin N) (p : CPN N) :
    Matrix (Fin dS) (Fin dS) ℂ :=
  Matrix.traceRight ((rayDensityMat p).submatrix e e)

/-- The reduced density entry as an explicit environment sum. -/
lemma reducedRayDensity_apply (e : Fin dS × Fin dE ≃ Fin N) (p : CPN N) (i i' : Fin dS) :
    reducedRayDensity e p i i' = ∑ k : Fin dE, rayDensity p (e (i, k)) (e (i', k)) := by
  unfold reducedRayDensity rayDensityMat
  rw [Matrix.traceRight_apply]
  rfl

/-- **The average reduced state**, entrywise: `E_{mu_FS}[ Tr_E |psi><psi| ]`. -/
noncomputable def fsReducedFirstMoment (e : Fin dS × Fin dE ≃ Fin N) (p₀ : CPN N) :
    Matrix (Fin dS) (Fin dS) ℂ :=
  Matrix.of fun i i' => ∫ p, reducedRayDensity e p i i' ∂(fubiniStudyMeasure p₀)

/-- **Deliverable 2 (the headline): canonical typicality in expectation.** For a
tensor split `H = H_S (x) H_E` with `N = d_S * d_E` (encoded by the reindex equiv
`e`), the Fubini-Study *average* reduced state is the canonical (maximally mixed,
equal-energy / microcanonical) state on the subsystem:
`E_{mu_FS}[ Tr_E |psi><psi| ] = (1/d_S) I_S`.

This is "thermal equilibrium from Fubini-Study volume", the FS-average ANALOGUE
of `LF6.maxEntangled_marginal_uniform` (the specific maximally-entangled state's
marginal) -- an analogy, not a formal Lean dependency (this theorem does not cite
that lemma). Proof: partial-trace the first
moment (`fs_first_moment`); the environment sum of `(1/N) delta` over `d_E`
diagonal cells is `(d_E/N) delta = (1/d_S) delta`.

HONEST SCOPE: expectation (average), not the typical single state (concentration /
Levy; see the residual section in the module docstring). Foundational-triple. -/
theorem canonical_typicality_expectation [NeZero N] [NeZero dS] [NeZero dE]
    (e : Fin dS × Fin dE ≃ Fin N) (p₀ : CPN N) :
    fsReducedFirstMoment e p₀ = ((dS : ℂ)⁻¹) • (1 : Matrix (Fin dS) (Fin dS) ℂ) := by
  have hNval : N = dS * dE := by
    have h := Fintype.card_congr e
    simpa [Fintype.card_prod] using h.symm
  have hdS : (dS : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dS)
  have hdE : (dE : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dE)
  ext i i'
  rw [fsReducedFirstMoment, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  -- integrand = sum over environment of density entries; push the integral inside
  have hfun : (fun p => reducedRayDensity e p i i')
      = fun p => ∑ k : Fin dE, rayDensity p (e (i, k)) (e (i', k)) := by
    funext p; exact reducedRayDensity_apply e p i i'
  rw [hfun, integral_finsetSum Finset.univ
        (fun k _ => rayDensity_integrable p₀ (e (i, k)) (e (i', k)))]
  -- each summand is the first-moment entry = (N)⁻¹ * delta_{i i'}
  have hentry : ∀ k : Fin dE, ∫ p, rayDensity p (e (i, k)) (e (i', k)) ∂(fubiniStudyMeasure p₀)
      = (N : ℂ)⁻¹ * (if i = i' then 1 else 0) := by
    intro k
    have hfm := congrFun (congrFun (fs_first_moment p₀) (e (i, k))) (e (i', k))
    rw [fsFirstMoment, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hfm
    rw [hfm]
    congr 1
    by_cases h : i = i'
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hh => h (by
        have := e.injective hh; exact (Prod.mk.injEq _ _ _ _ ▸ this).1))]
  simp_rw [hentry]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- (d_E) * ((N)⁻¹ * delta) = (d_S)⁻¹ * delta
  rw [hNval]
  by_cases h : i = i'
  · rw [if_pos h, mul_one, mul_one]
    push_cast
    field_simp
  · rw [if_neg h, mul_zero, mul_zero, mul_zero]

/-! ## Concentration residual (the named stretch -- NOT proved here)

The strictly stronger **typical-state** statement (canonical typicality proper,
Popescu-Short-Winter / Goldstein-Lebowitz-Tumulka-Zanghi) is:

> for a small subsystem `d_S` in a large environment `d_E`, a `mu_FS`-typical
> single pure state `psi` has reduced state close to `I_S/d_S`:
> `mu_FS { psi : ‖ Tr_E |psi><psi| - I_S/d_S ‖ >= eps } <= C * exp(-c * d_E * eps²)`.

This is **not** proved here. It requires **Levy's lemma** (measure concentration on
the high-dimensional sphere `S^{2N-1}`: an `L`-Lipschitz function concentrates
around its mean with Gaussian tails of width `~ L/sqrt(N)`), which follows from the
sphere's isoperimetric inequality / Ricci-curvature lower bound. Mathlib carries
neither Levy's lemma nor the spherical isoperimetric inequality, so the
concentration upgrade is the named residual of this tranche. The `fs_first_moment`
result above is exactly the *mean* around which Levy's lemma would concentrate;
what is missing is only the deviation bound, not the target value.

No `sorry` / axiom stands in for this: TH1 delivers the EXPECTATION, and names the
concentration precisely as the residual. -/

end Thermo
end CSD
