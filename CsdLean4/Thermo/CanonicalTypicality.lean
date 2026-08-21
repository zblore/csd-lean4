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
public import Mathlib.Probability.Moments.Variance

/-!
# TH1: canonical typicality -- thermal equilibrium from Fubini-Study volume

**Category:** conceptually 1-Mathlib (CSD-free general quantum statistical
mechanics on the Fubini-Study Kaehler structure); kept under `CSD.Thermo` as the
flagship first tranche of the thermodynamics track (`specs/thermo-plan.md`, TH1).

**Glossary:** https://glossary.constraintsurfacedynamics.com/canonical-typicality/
Plain-language, CSD-role and formal statements of canonical typicality, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

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

**EXPECTATION + CHEBYSHEV, not exponential.** This tranche proves the reduced
state is canonical *in expectation* over `mu_FS`, and (Q24, 2026-08-21) that
diagonal statistics of a *single* `mu_FS`-sample concentrate at the
maximally-mixed value at polynomial rate `Var = O(1/N)`
(`fs_chebyshev_concentration`, from the exact second moments
`fs_x_sq_moment` / `fs_x_cross_moment` -- twirl algebra, no isoperimetry).
The strictly stronger EXPONENTIAL *typical-state* (Levy) statement -- reduced
state close to `I_S/d_S` with probability `1 - O(exp(-c d_E))` for a small
subsystem in a large environment (Popescu-Short-Winter / Goldstein-Lebowitz-
Tumulka-Zanghi) -- is the named residual (see the `Concentration residual`
section below). It is NOT proved here: it needs measure concentration on
high-dimensional spheres (Levy's lemma: Lipschitz + isoperimetry), which
Mathlib does not carry. No `sorry`, no axiom is used to paper over this.

**NOT dynamical thermalisation.** This is a typicality (volume-average) statement,
not a proof that a given initial state thermalises under a dynamics (that needs
mixing / ETH, out of scope).

**CSD reading.** Born-from-volume (the moment-map / Duistermaat-Heckman cluster,
`fs_born_volume_ratio_N`, Gleason-free) becomes thermal-equilibrium-from-volume:
the canonical subsystem state is the Fubini-Study volume-average. The
CSD-distinctive claim that this equilibrium *emerges from deterministic
microdynamics* rests on the SO-1 (sector / typicality-law posit) and D1 (dynamics)
residues shared with all of LF4/LF6; this file posits `mu_FS` as the sampling law
(SO-1) and proves the statistical-mechanical consequence, it does not derive `mu_FS`
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

No `sorry` / axiom stands in for this: TH1 delivers the EXPECTATION and (Q24,
below) the POLYNOMIAL Chebyshev tier, and names the exponential tier precisely
as the residual. -/

/-! ## Q24: the Chebyshev tier — second moments and polynomial concentration

(2026-08-21, `specs/th1-concentration-scoping.md`.) The concentration residual
above splits into two tiers. The EXPONENTIAL (Lévy) tier still needs spherical
isoperimetry and stays the recorded Mathlib-scale residual. The POLYNOMIAL
(Chebyshev) tier needs only second moments, and those turn out to require **no
integrals at all**: TH1's own twirl style, one moment higher, determines them
algebraically. With `a := E[xᵢ²]`, `b := E[xᵢxⱼ]` (`i ≠ j`, `x := momentMap`):
permutation swaps make `a` index-free; the pointwise normalisation integrates
to `a + (N−1)b = 1/N`; and invariance under a two-coordinate Hadamard rotation
— with a sign flip killing the linear cross term and a quarter-phase flip
halving the squared real part — gives `a = 2b` FOR EACH PAIR separately. Solve:
`a = 2/(N(N+1))`, `b = 1/(N(N+1))` — the Dirichlet values, by twirl algebra.
Downstream: the second moment of any diagonal statistic is exact
(`fs_linear_sq_moment`, giving `Var = O(1/N)`) and Chebyshev gives
polynomial-rate typicality (`fs_chebyshev_concentration`), with no
isoperimetry anywhere. -/

/-! ### The quarter-phase unitary -/

/-- **The quarter-phase matrix** `diag(1, ..., I, ..., 1)` with `Complex.I` at
index `i`. The `signFlipMat` pattern with a genuinely complex phase; used to
kill squared off-diagonal entries (`r² ↦ −r²`) and to equate `E[(Re r)²]` with
`E[(Im r)²]`. -/
noncomputable def phaseFlipMat (i : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun k => if k = i then Complex.I else 1)

lemma phaseFlipMat_mem (i : Fin N) : phaseFlipMat i ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, phaseFlipMat, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [show (fun k : Fin N => (star fun k : Fin N => if k = i then Complex.I else 1) k
        * (if k = i then Complex.I else 1)) = (1 : Fin N → ℂ) by
    funext k
    rw [Pi.star_apply, Pi.one_apply]
    split_ifs <;> simp]
  exact Matrix.diagonal_one

/-- The quarter-phase unitary as a group element. -/
noncomputable def phaseFlip (i : Fin N) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨phaseFlipMat i, phaseFlipMat_mem i⟩

@[simp] lemma phaseFlip_val (i : Fin N) : (phaseFlip i).val = phaseFlipMat i := rfl

/-- Coordinate action of the quarter-phase. -/
lemma toEuclideanLin_phaseFlip_coord (i : Fin N) (v : EuclideanSpace ℂ (Fin N)) (a : Fin N) :
    (Matrix.toEuclideanLin (phaseFlipMat i) v) a = (if a = i then Complex.I else 1) * v a := by
  rw [phaseFlipMat, Matrix.toLpLin_apply]
  simp [Matrix.mulVec_diagonal]

/-- The quarter-phase is norm-preserving (squared form). -/
lemma phaseFlip_normSq (i : Fin N) (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin (phaseFlipMat i) v)‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [toEuclideanLin_phaseFlip_coord, norm_mul]
  rw [show ‖(if a = i then Complex.I else 1)‖ = 1 by split_ifs <;> simp, one_mul]

/-! ### The two-coordinate Hadamard rotation -/

/-- **The Hadamard rotation matrix** at the (distinct) coordinate pair `(i, j)`:
the `(1/√2)·[[1,1],[1,−1]]` block on `{i,j}`, the identity elsewhere. Real
symmetric; mixes exactly two coordinates. -/
noncomputable def hadamardMat (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b =>
    if a = i then (if b = i then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      else if b = j then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)
    else if a = j then (if b = i then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      else if b = j then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)
    else (if b = a then 1 else 0)

/-- The Hadamard-rotation entries, unfolded. -/
lemma hadamardMat_apply (i j a b : Fin N) :
    hadamardMat i j a b =
      if a = i then (if b = i then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        else if b = j then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)
      else if a = j then (if b = i then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        else if b = j then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)
      else (if b = a then 1 else 0) := rfl

/-- Off the pair `{i, j}`, a Hadamard-rotation row is a delta row. -/
lemma hadamardMat_apply_of_ne (i j : Fin N) {a : Fin N} (hai : a ≠ i) (haj : a ≠ j)
    (b : Fin N) : hadamardMat i j a b = if b = a then 1 else 0 := by
  rw [hadamardMat_apply, if_neg hai, if_neg haj]

/-- The Hadamard rotation is Hermitian (real symmetric). -/
lemma hadamardMat_conjTranspose (i j : Fin N) (hij : i ≠ j) :
    (hadamardMat i j)ᴴ = hadamardMat i j := by
  ext a b
  rw [Matrix.conjTranspose_apply, hadamardMat_apply, hadamardMat_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [Complex.conj_ofReal, Ne.symm hij, eq_comm]

lemma hadamardMat_mem (i j : Fin N) (hij : i ≠ j) :
    hadamardMat i j ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num [Complex.ofReal_inv]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    hadamardMat_conjTranspose i j hij]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  -- Restrict the sum to the pair `{i, j}` in the two block rows; the delta rows
  -- collapse to a single term.
  by_cases hai : a = i
  · -- row `i`: supported on `{i, j}`.
    rw [hai]
    rw [show (∑ c, hadamardMat i j i c * hadamardMat i j c b)
        = ∑ c ∈ ({i, j} : Finset (Fin N)), hadamardMat i j i c * hadamardMat i j c b from
      (Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        push Not at hc
        rw [hadamardMat_apply i j i c, if_pos rfl, if_neg hc.1, if_neg hc.2,
          zero_mul])).symm]
    rw [Finset.sum_pair hij]
    rw [hadamardMat_apply i j i i, if_pos rfl, if_pos rfl,
      hadamardMat_apply i j i j, if_pos rfl, if_neg (Ne.symm hij), if_pos rfl,
      hadamardMat_apply i j i b, if_pos rfl,
      hadamardMat_apply i j j b, if_neg (Ne.symm hij), if_pos rfl]
    by_cases hbi : b = i
    · rw [if_pos hbi, if_pos hbi, if_pos hbi.symm, hs]
      norm_num
    · rw [if_neg hbi, if_neg hbi, if_neg (fun h : i = b => hbi h.symm)]
      by_cases hbj : b = j
      · rw [if_pos hbj, if_pos hbj]
        ring
      · rw [if_neg hbj, if_neg hbj]
        ring
  · by_cases haj : a = j
    · -- row `j`: supported on `{i, j}`.
      rw [haj]
      rw [show (∑ c, hadamardMat i j j c * hadamardMat i j c b)
          = ∑ c ∈ ({i, j} : Finset (Fin N)), hadamardMat i j j c * hadamardMat i j c b from
        (Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hc
          push Not at hc
          rw [hadamardMat_apply i j j c, if_neg (Ne.symm hij), if_pos rfl,
            if_neg hc.1, if_neg hc.2, zero_mul])).symm]
      rw [Finset.sum_pair hij]
      rw [hadamardMat_apply i j j i, if_neg (Ne.symm hij), if_pos rfl, if_pos rfl,
        hadamardMat_apply i j j j, if_neg (Ne.symm hij), if_pos rfl,
        if_neg (Ne.symm hij), if_pos rfl,
        hadamardMat_apply i j i b, if_pos rfl,
        hadamardMat_apply i j j b, if_neg (Ne.symm hij), if_pos rfl]
      by_cases hbi : b = i
      · rw [if_pos hbi, if_pos hbi, if_neg (fun h : j = b => hij (h.trans hbi).symm)]
        ring
      · rw [if_neg hbi, if_neg hbi]
        by_cases hbj : b = j
        · rw [if_pos hbj, if_pos hbj, if_pos hbj.symm]
          rw [show -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * -((Real.sqrt 2 : ℝ) : ℂ)⁻¹
              = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ by ring, hs]
          norm_num
        · rw [if_neg hbj, if_neg hbj, if_neg (fun h : j = b => hbj h.symm)]
          ring
    · -- delta row: the sum collapses to `c = a`.
      rw [Finset.sum_eq_single a
        (fun c _ hca => by rw [hadamardMat_apply_of_ne i j hai haj, if_neg hca, zero_mul])
        (fun ha => absurd (Finset.mem_univ a) ha)]
      rw [hadamardMat_apply_of_ne i j hai haj, if_pos rfl, one_mul,
        hadamardMat_apply i j a b, if_neg hai, if_neg haj]
      by_cases hab : b = a
      · rw [if_pos hab, if_pos hab.symm]
      · rw [if_neg hab, if_neg (fun h : a = b => hab h.symm)]

/-- The Hadamard rotation as a unitary group element. -/
noncomputable def hadamardU (i j : Fin N) (hij : i ≠ j) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨hadamardMat i j, hadamardMat_mem i j hij⟩

@[simp] lemma hadamardU_val (i j : Fin N) (hij : i ≠ j) :
    (hadamardU i j hij).val = hadamardMat i j := rfl

/-! ### Coordinate actions of the new unitaries -/

/-- Coordinate `i` of the Hadamard rotation: `(H v)ᵢ = (vᵢ + vⱼ)/√2`. -/
lemma toEuclideanLin_hadamard_coord_i (i j : Fin N) (hij : i ≠ j)
    (v : EuclideanSpace ℂ (Fin N)) :
    (Matrix.toEuclideanLin (hadamardMat i j) v) i
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (v i + v j) := by
  rw [Matrix.toLpLin_apply]
  show ∑ c, hadamardMat i j i c * v c = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (v i + v j)
  rw [show (∑ c, hadamardMat i j i c * v c)
      = ∑ c ∈ ({i, j} : Finset (Fin N)), hadamardMat i j i c * v c from
    (Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      push Not at hc
      rw [hadamardMat_apply i j i c, if_pos rfl, if_neg hc.1, if_neg hc.2,
        zero_mul])).symm]
  rw [Finset.sum_pair hij]
  rw [hadamardMat_apply i j i i, if_pos rfl, if_pos rfl,
    hadamardMat_apply i j i j, if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
  ring

/-- Coordinate `j` of the Hadamard rotation: `(H v)ⱼ = (vᵢ − vⱼ)/√2`. -/
lemma toEuclideanLin_hadamard_coord_j (i j : Fin N) (hij : i ≠ j)
    (v : EuclideanSpace ℂ (Fin N)) :
    (Matrix.toEuclideanLin (hadamardMat i j) v) j
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (v i - v j) := by
  rw [Matrix.toLpLin_apply]
  show ∑ c, hadamardMat i j j c * v c = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (v i - v j)
  rw [show (∑ c, hadamardMat i j j c * v c)
      = ∑ c ∈ ({i, j} : Finset (Fin N)), hadamardMat i j j c * v c from
    (Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      push Not at hc
      rw [hadamardMat_apply i j j c, if_neg (Ne.symm hij), if_pos rfl,
        if_neg hc.1, if_neg hc.2, zero_mul])).symm]
  rw [Finset.sum_pair hij]
  rw [hadamardMat_apply i j j i, if_neg (Ne.symm hij), if_pos rfl, if_pos rfl,
    hadamardMat_apply i j j j, if_neg (Ne.symm hij), if_pos rfl,
    if_neg (Ne.symm hij), if_pos rfl]
  ring

/-- Away from the pair, the Hadamard rotation fixes coordinates. -/
lemma toEuclideanLin_hadamard_coord_ne (i j : Fin N) {a : Fin N}
    (hai : a ≠ i) (haj : a ≠ j) (v : EuclideanSpace ℂ (Fin N)) :
    (Matrix.toEuclideanLin (hadamardMat i j) v) a = v a := by
  rw [Matrix.toLpLin_apply]
  show ∑ c, hadamardMat i j a c * v c = v a
  rw [Finset.sum_eq_single a
    (fun c _ hca => by
      rw [hadamardMat_apply_of_ne i j hai haj, if_neg hca, zero_mul])
    (fun ha => absurd (Finset.mem_univ a) ha)]
  rw [hadamardMat_apply_of_ne i j hai haj, if_pos rfl, one_mul]

/-- The Hadamard rotation is norm-preserving (squared form): the parallelogram
law on the pair, the identity elsewhere. -/
lemma hadamard_normSq (i j : Fin N) (hij : i ≠ j) (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin (hadamardMat i j) v)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hs2 : ((Real.sqrt 2 : ℝ))⁻¹ ^ 2 = 2⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
  rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum,
    ← Finset.sum_add_sum_compl ({i, j} : Finset (Fin N))
      (fun a => ‖(Matrix.toEuclideanLin (hadamardMat i j) v) a‖ ^ 2),
    ← Finset.sum_add_sum_compl ({i, j} : Finset (Fin N))
      (fun a => ‖v a‖ ^ 2)]
  congr 1
  · rw [Finset.sum_pair hij, Finset.sum_pair hij,
      toEuclideanLin_hadamard_coord_i i j hij, toEuclideanLin_hadamard_coord_j i j hij]
    have hnorm : ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg 2)]
    rw [norm_mul, norm_mul, hnorm, mul_pow, mul_pow, hs2]
    have hpar := parallelogram_law_with_norm ℂ (v i) (v j)
    rw [show ‖v i + v j‖ ^ 2 = ‖v i + v j‖ * ‖v i + v j‖ from sq _,
      show ‖v i - v j‖ ^ 2 = ‖v i - v j‖ * ‖v i - v j‖ from sq _,
      show ‖v i‖ ^ 2 = ‖v i‖ * ‖v i‖ from sq _,
      show ‖v j‖ ^ 2 = ‖v j‖ * ‖v j‖ from sq _]
    linarith [hpar]
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at ha
    push Not at ha
    rw [toEuclideanLin_hadamard_coord_ne i j ha.1 ha.2]

/-! ### Actions on the moment coordinates and the density entry -/

/-- The sign flip fixes every moment coordinate. -/
lemma momentMap_signFlip [NeZero N] (i : Fin N) (p : CPN N) (a : Fin N) :
    momentMap ((signFlip i) • p) a = momentMap p a := by
  rw [smul_eq_mk, momentMap_mk]
  unfold momentMap
  rw [signFlip_val, toEuclideanLin_signFlip_coord, signFlip_normSq]
  rw [norm_mul, show ‖(if a = i then (-1 : ℂ) else 1)‖ = 1 by split_ifs <;> simp,
    one_mul]

/-- The quarter-phase fixes every moment coordinate. -/
lemma momentMap_phaseFlip [NeZero N] (i : Fin N) (p : CPN N) (a : Fin N) :
    momentMap ((phaseFlip i) • p) a = momentMap p a := by
  rw [smul_eq_mk, momentMap_mk]
  unfold momentMap
  rw [phaseFlip_val, toEuclideanLin_phaseFlip_coord, phaseFlip_normSq]
  rw [norm_mul, show ‖(if a = i then Complex.I else 1)‖ = 1 by split_ifs <;> simp,
    one_mul]

/-- The quarter-phase multiplies the `(i, j)` density entry by `I` (`j ≠ i`). -/
lemma phaseFlip_smul_cross [NeZero N] (i j : Fin N) (hji : j ≠ i) (p : CPN N) :
    rayDensity ((phaseFlip i) • p) i j = Complex.I * rayDensity p i j := by
  rw [smul_eq_mk, rayDensity_mk, phaseFlip_val, toEuclideanLin_phaseFlip_coord,
      toEuclideanLin_phaseFlip_coord, if_pos rfl, if_neg hji, one_mul]
  have hden : (‖(Matrix.toEuclideanLin (phaseFlipMat i) p.rep)‖ : ℂ) ^ 2
      = (‖p.rep‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, phaseFlip_normSq, Complex.ofReal_pow]
  rw [hden]
  unfold rayDensity
  ring

/-- **The Hadamard rotation mixes the pair through the density entry**:
`x'ᵢ = (xᵢ + xⱼ + 2·Re r)/2` with `r` the `(i,j)` density entry. -/
lemma momentMap_hadamard [NeZero N] (i j : Fin N) (hij : i ≠ j) (p : CPN N) :
    momentMap ((hadamardU i j hij) • p) i
      = (momentMap p i + momentMap p j + 2 * (rayDensity p i j).re) / 2 := by
  rw [smul_eq_mk, momentMap_mk]
  rw [show (hadamardU i j hij).val = hadamardMat i j from rfl]
  rw [toEuclideanLin_hadamard_coord_i i j hij, hadamard_normSq i j hij]
  unfold momentMap rayDensity
  have hD : (0 : ℝ) < ‖p.rep‖ ^ 2 := pow_pos (norm_pos_iff.mpr p.rep_nonzero) 2
  have hnorm : ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [norm_mul, hnorm, mul_pow,
    show ((Real.sqrt 2 : ℝ))⁻¹ ^ 2 = 2⁻¹ by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]]
  -- ‖z + w‖² = ‖z‖² + ‖w‖² + 2·Re(z·conj w), then divide through.
  have hexp : ‖p.rep i + p.rep j‖ ^ 2
      = ‖p.rep i‖ ^ 2 + ‖p.rep j‖ ^ 2 + 2 * ((p.rep i) * conj (p.rep j)).re := by
    have h := Complex.normSq_add (p.rep i) (p.rep j)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq] at h
    exact h
  rw [hexp]
  rw [show ((‖p.rep‖ : ℝ) : ℂ) ^ 2 = ((‖p.rep‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.div_ofReal_re]
  field_simp

/-! ### The twirl transport, packaged once -/

/-- **The change-of-variables engine**: a Fubini–Study integral of a measurable
real statistic equals its integral against any unitary pushforward. The
`fsFirstMoment_offdiag` calc, packaged for reuse. -/
lemma fs_integral_unitary (p₀ : CPN N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    {f : CPN N → ℝ} (hf : Measurable f) :
    ∫ p, f p ∂(fubiniStudyMeasure p₀) = ∫ p, f (U • p) ∂(fubiniStudyMeasure p₀) := by
  set μ := fubiniStudyMeasure p₀ with hμ
  have hg : Measurable fun p : CPN N => U • p := (continuous_const_smul U).measurable
  have hinv : Measure.map (fun p : CPN N => U • p) μ = μ :=
    fubiniStudyMeasure_smul_invariant U p₀
  calc ∫ p, f p ∂μ
      = ∫ p, f p ∂(Measure.map (fun p : CPN N => U • p) μ) := by rw [hinv]
    _ = ∫ p, f (U • p) ∂μ :=
        integral_map hg.aemeasurable (by rw [hinv]; exact hf.aestronglyMeasurable)

/-! ### Measurability and integrability of the second-moment integrands -/

lemma re_rayDensity_measurable (i j : Fin N) :
    Measurable fun p : CPN N => (rayDensity p i j).re :=
  Complex.measurable_re.comp (rayDensity_measurable i j)

lemma abs_re_rayDensity_le_one (p : CPN N) (i j : Fin N) :
    |(rayDensity p i j).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (rayDensity_norm_le_one p i j)

lemma abs_im_rayDensity_le_one (p : CPN N) (i j : Fin N) :
    |(rayDensity p i j).im| ≤ 1 :=
  (Complex.abs_im_le_norm _).trans (rayDensity_norm_le_one p i j)

lemma abs_momentMap_le_one (p : CPN N) (i : Fin N) : |momentMap p i| ≤ 1 := by
  rw [abs_of_nonneg (momentMap_nonneg p i)]
  exact momentMap_le_one p i

/-- Integrability of a product of two of the bounded statistics, from explicit
`[-1, 1]` bounds. -/
lemma fs_integrable_mul (p₀ : CPN N) {f g : CPN N → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ p, |f p| ≤ 1) (hgb : ∀ p, |g p| ≤ 1) :
    Integrable (fun p => f p * g p) (fubiniStudyMeasure p₀) :=
  Integrable.of_bound (hf.mul hg).aestronglyMeasurable 1
    (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (hfb p) (abs_nonneg _) (hgb p)))

/-! ### The kill lemmas -/

/-- **The linear cross terms die**: `E[xₐ · Re r] = 0` for the `(i,j)` density
entry `r` (`j ≠ i`), by the sign flip at `i`. -/
lemma fs_cross_linear_zero (p₀ : CPN N) [NeZero N] (a i j : Fin N) (hji : j ≠ i) :
    ∫ p, momentMap p a * (rayDensity p i j).re ∂(fubiniStudyMeasure p₀) = 0 := by
  set μ := fubiniStudyMeasure p₀ with hμ
  have hmeas : Measurable fun p : CPN N => momentMap p a * (rayDensity p i j).re :=
    (momentMap_measurable a).mul (re_rayDensity_measurable i j)
  have hM : ∫ p, momentMap p a * (rayDensity p i j).re ∂μ
      = - ∫ p, momentMap p a * (rayDensity p i j).re ∂μ := by
    calc ∫ p, momentMap p a * (rayDensity p i j).re ∂μ
        = ∫ p, momentMap ((signFlip i) • p) a
            * (rayDensity ((signFlip i) • p) i j).re ∂μ :=
          fs_integral_unitary p₀ (signFlip i) hmeas
      _ = ∫ p, -(momentMap p a * (rayDensity p i j).re) ∂μ :=
          integral_congr_ae (ae_of_all _ (fun p => by
            dsimp only
            rw [momentMap_signFlip, signFlip_smul_offdiag i j hji, Complex.neg_re]
            ring))
      _ = - ∫ p, momentMap p a * (rayDensity p i j).re ∂μ := integral_neg _
  linarith

/-- Pointwise: `(Re r)² + (Im r)² = xᵢ·xⱼ` — the squared modulus of the density
entry is the product of the two moment coordinates. -/
lemma rayDensity_re_sq_add_im_sq (p : CPN N) (i j : Fin N) :
    (rayDensity p i j).re ^ 2 + (rayDensity p i j).im ^ 2
      = momentMap p i * momentMap p j := by
  have h2 : Complex.normSq (rayDensity p i j) = momentMap p i * momentMap p j := by
    unfold rayDensity momentMap
    rw [map_div₀ Complex.normSq, map_mul Complex.normSq, Complex.normSq_conj]
    rw [show Complex.normSq ((‖p.rep‖ : ℂ) ^ 2) = (‖p.rep‖ ^ 2) ^ 2 by
      rw [map_pow, Complex.normSq_ofReal]; ring]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have hD : (0 : ℝ) < ‖p.rep‖ ^ 2 := pow_pos (norm_pos_iff.mpr p.rep_nonzero) 2
    field_simp
  rw [← h2, Complex.normSq_apply, pow_two, pow_two]

/-- `E[(Re r)²] = E[(Im r)²]`, by the quarter-phase flip at `i`. -/
lemma fs_re_sq_eq_im_sq (p₀ : CPN N) [NeZero N] (i j : Fin N) (hji : j ≠ i) :
    ∫ p, (rayDensity p i j).re ^ 2 ∂(fubiniStudyMeasure p₀)
      = ∫ p, (rayDensity p i j).im ^ 2 ∂(fubiniStudyMeasure p₀) := by
  have hmeas : Measurable fun p : CPN N => (rayDensity p i j).re ^ 2 :=
    (re_rayDensity_measurable i j).pow_const 2
  calc ∫ p, (rayDensity p i j).re ^ 2 ∂(fubiniStudyMeasure p₀)
      = ∫ p, (rayDensity ((phaseFlip i) • p) i j).re ^ 2 ∂(fubiniStudyMeasure p₀) :=
        fs_integral_unitary p₀ (phaseFlip i) hmeas
    _ = ∫ p, (rayDensity p i j).im ^ 2 ∂(fubiniStudyMeasure p₀) :=
        integral_congr_ae (ae_of_all _ (fun p => by
          dsimp only
          rw [phaseFlip_smul_cross i j hji]
          rw [show (Complex.I * rayDensity p i j).re = -(rayDensity p i j).im by
            rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring]
          ring))

/-- **The squared real part carries half the product**: `E[(Re r)²] = E[xᵢxⱼ]/2`. -/
lemma fs_re_sq_moment (p₀ : CPN N) [NeZero N] (i j : Fin N) (hij : i ≠ j) :
    ∫ p, (rayDensity p i j).re ^ 2 ∂(fubiniStudyMeasure p₀)
      = (∫ p, momentMap p i * momentMap p j ∂(fubiniStudyMeasure p₀)) / 2 := by
  have int_re2 : Integrable (fun p : CPN N => (rayDensity p i j).re ^ 2)
      (fubiniStudyMeasure p₀) := by
    refine fs_integrable_mul p₀ (re_rayDensity_measurable i j)
      (re_rayDensity_measurable i j) (abs_re_rayDensity_le_one · i j)
      (abs_re_rayDensity_le_one · i j) |>.congr ?_
    exact ae_of_all _ (fun p => by simp only [pow_two])
  have int_im2 : Integrable (fun p : CPN N => (rayDensity p i j).im ^ 2)
      (fubiniStudyMeasure p₀) := by
    refine fs_integrable_mul p₀ (Complex.measurable_im.comp (rayDensity_measurable i j))
      (Complex.measurable_im.comp (rayDensity_measurable i j))
      (abs_im_rayDensity_le_one · i j) (abs_im_rayDensity_le_one · i j) |>.congr ?_
    exact ae_of_all _ (fun p => by simp only [Function.comp_apply, pow_two])
  have hsum : ∫ p, ((rayDensity p i j).re ^ 2 + (rayDensity p i j).im ^ 2)
        ∂(fubiniStudyMeasure p₀)
      = ∫ p, momentMap p i * momentMap p j ∂(fubiniStudyMeasure p₀) :=
    integral_congr_ae (ae_of_all _ (fun p => rayDensity_re_sq_add_im_sq p i j))
  rw [integral_add int_re2 int_im2] at hsum
  rw [← fs_re_sq_eq_im_sq p₀ i j (Ne.symm hij)] at hsum
  linarith

/-- Second moments of the coordinates are index-independent (permutation swap). -/
lemma fs_x_sq_swap (p₀ : CPN N) [NeZero N] (i k : Fin N) :
    ∫ p, momentMap p i ^ 2 ∂(fubiniStudyMeasure p₀)
      = ∫ p, momentMap p k ^ 2 ∂(fubiniStudyMeasure p₀) := by
  calc ∫ p, momentMap p i ^ 2 ∂(fubiniStudyMeasure p₀)
      = ∫ p, momentMap ((permU (Equiv.swap i k)) • p) i ^ 2 ∂(fubiniStudyMeasure p₀) :=
        fs_integral_unitary p₀ (permU (Equiv.swap i k))
          ((momentMap_measurable i).pow_const 2)
    _ = ∫ p, momentMap p ((Equiv.swap i k) i) ^ 2 ∂(fubiniStudyMeasure p₀) :=
        integral_congr_ae (ae_of_all _ (fun p => by dsimp only; rw [momentMap_permU]))
    _ = ∫ p, momentMap p k ^ 2 ∂(fubiniStudyMeasure p₀) := by
        rw [Equiv.swap_apply_left]

/-! ### The engine: `a = 2b`, per pair -/

/-- ★ **The Hadamard identity `a = 2b`** (Q24, the route discovery): invariance of
the second moment under the two-coordinate Hadamard rotation, with the sign flip
killing the linear cross terms and the quarter-phase halving the squared real
part, forces `E[xᵢ²] = 2·E[xᵢxⱼ]` — for each pair separately, with no integral
ever computed. -/
theorem fs_x_sq_eq_two_cross (p₀ : CPN N) [NeZero N] {i j : Fin N} (hij : i ≠ j) :
    ∫ p, momentMap p i ^ 2 ∂(fubiniStudyMeasure p₀)
      = 2 * ∫ p, momentMap p i * momentMap p j ∂(fubiniStudyMeasure p₀) := by
  set μ := fubiniStudyMeasure p₀ with hμ
  -- integrability of the six expansion pieces
  have hx : ∀ a : Fin N, Measurable fun p : CPN N => momentMap p a := momentMap_measurable
  have hr : Measurable fun p : CPN N => (rayDensity p i j).re :=
    re_rayDensity_measurable i j
  have int_xi2 : Integrable (fun p : CPN N => momentMap p i ^ 2) μ := by
    refine (fs_integrable_mul p₀ (hx i) (hx i) (abs_momentMap_le_one · i)
      (abs_momentMap_le_one · i)).congr (ae_of_all _ (fun p => by simp only [pow_two]))
  have int_xj2 : Integrable (fun p : CPN N => momentMap p j ^ 2) μ := by
    refine (fs_integrable_mul p₀ (hx j) (hx j) (abs_momentMap_le_one · j)
      (abs_momentMap_le_one · j)).congr (ae_of_all _ (fun p => by simp only [pow_two]))
  have int_re2 : Integrable (fun p : CPN N => (rayDensity p i j).re ^ 2) μ := by
    refine (fs_integrable_mul p₀ hr hr (abs_re_rayDensity_le_one · i j)
      (abs_re_rayDensity_le_one · i j)).congr (ae_of_all _ (fun p => by simp only [pow_two]))
  have int_xy : Integrable (fun p : CPN N => momentMap p i * momentMap p j) μ :=
    fs_integrable_mul p₀ (hx i) (hx j) (abs_momentMap_le_one · i)
      (abs_momentMap_le_one · j)
  have int_xire : Integrable (fun p : CPN N => momentMap p i * (rayDensity p i j).re) μ :=
    fs_integrable_mul p₀ (hx i) hr (abs_momentMap_le_one · i)
      (abs_re_rayDensity_le_one · i j)
  have int_xjre : Integrable (fun p : CPN N => momentMap p j * (rayDensity p i j).re) μ :=
    fs_integrable_mul p₀ (hx j) hr (abs_momentMap_le_one · j)
      (abs_re_rayDensity_le_one · i j)
  -- the Hadamard transport
  have key : ∫ p, momentMap p i ^ 2 ∂μ
      = ∫ p, ((momentMap p i + momentMap p j + 2 * (rayDensity p i j).re) / 2) ^ 2 ∂μ := by
    calc ∫ p, momentMap p i ^ 2 ∂μ
        = ∫ p, momentMap ((hadamardU i j hij) • p) i ^ 2 ∂μ :=
          fs_integral_unitary p₀ (hadamardU i j hij) ((hx i).pow_const 2)
      _ = _ := integral_congr_ae (ae_of_all _ (fun p => by
            dsimp only
            rw [momentMap_hadamard i j hij p]))
  -- expand the square into six integrable pieces
  have hpt : ∀ p : CPN N,
      ((momentMap p i + momentMap p j + 2 * (rayDensity p i j).re) / 2) ^ 2
        = (momentMap p i ^ 2 + (momentMap p j ^ 2 + (4 * (rayDensity p i j).re ^ 2
          + (2 * (momentMap p i * momentMap p j)
            + (4 * (momentMap p i * (rayDensity p i j).re)
              + 4 * (momentMap p j * (rayDensity p i j).re)))))) / 4 :=
    fun p => by ring
  simp only [hpt] at key
  rw [integral_div] at key
  -- cumulative integrabilities, stated in lambda form so `integral_add` matches
  have i6 : Integrable (fun p : CPN N =>
      4 * (momentMap p j * (rayDensity p i j).re)) μ := int_xjre.const_mul 4
  have i5l : Integrable (fun p : CPN N =>
      4 * (momentMap p i * (rayDensity p i j).re)) μ := int_xire.const_mul 4
  have i5 : Integrable (fun p : CPN N =>
      4 * (momentMap p i * (rayDensity p i j).re)
        + 4 * (momentMap p j * (rayDensity p i j).re)) μ := i5l.add i6
  have i4l : Integrable (fun p : CPN N =>
      2 * (momentMap p i * momentMap p j)) μ := int_xy.const_mul 2
  have i4 : Integrable (fun p : CPN N =>
      2 * (momentMap p i * momentMap p j)
        + (4 * (momentMap p i * (rayDensity p i j).re)
          + 4 * (momentMap p j * (rayDensity p i j).re))) μ := i4l.add i5
  have i3l : Integrable (fun p : CPN N =>
      4 * (rayDensity p i j).re ^ 2) μ := int_re2.const_mul 4
  have i3 : Integrable (fun p : CPN N =>
      4 * (rayDensity p i j).re ^ 2
        + (2 * (momentMap p i * momentMap p j)
          + (4 * (momentMap p i * (rayDensity p i j).re)
            + 4 * (momentMap p j * (rayDensity p i j).re)))) μ := i3l.add i4
  have i2 : Integrable (fun p : CPN N =>
      momentMap p j ^ 2 + (4 * (rayDensity p i j).re ^ 2
        + (2 * (momentMap p i * momentMap p j)
          + (4 * (momentMap p i * (rayDensity p i j).re)
            + 4 * (momentMap p j * (rayDensity p i j).re))))) μ := int_xj2.add i3
  rw [integral_add int_xi2 i2, integral_add int_xj2 i3, integral_add i3l i4,
    integral_add i4l i5, integral_add i5l i6,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul] at key
  -- the values, bridged through the `set`-folded measure
  have hz1 : ∫ p, momentMap p i * (rayDensity p i j).re ∂μ = 0 := by
    rw [hμ]; exact fs_cross_linear_zero p₀ i i j (Ne.symm hij)
  have hz2 : ∫ p, momentMap p j * (rayDensity p i j).re ∂μ = 0 := by
    rw [hμ]; exact fs_cross_linear_zero p₀ j i j (Ne.symm hij)
  have hre : ∫ p, (rayDensity p i j).re ^ 2 ∂μ
      = (∫ p, momentMap p i * momentMap p j ∂μ) / 2 := by
    rw [hμ]; exact fs_re_sq_moment p₀ i j hij
  have hsw : ∫ p, momentMap p j ^ 2 ∂μ = ∫ p, momentMap p i ^ 2 ∂μ := by
    rw [hμ]; exact (fs_x_sq_swap p₀ i j).symm
  rw [hz1, hz2, hre, hsw] at key
  linarith

/-! ### The second moments themselves

With `a = 2b` (per pair) and the integrated normalisation
`a + (N−1)·b = 1/N`, both moments are determined: `a = 2/(N(N+1))`,
`b = 1/(N(N+1))` — the Dirichlet values, with no simplex integral in sight. -/

/-- ★ **The diagonal second moment**: `E[xᵢ²] = 2/(N(N+1))`. -/
theorem fs_x_sq_moment [NeZero N] (p₀ : CPN N) (i : Fin N) :
    ∫ p, momentMap p i ^ 2 ∂(fubiniStudyMeasure p₀)
      = 2 / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have hx : ∀ a : Fin N, Measurable fun p : CPN N => momentMap p a := momentMap_measurable
  have int_pair : ∀ k : Fin N, Integrable
      (fun p : CPN N => momentMap p i * momentMap p k) (fubiniStudyMeasure p₀) :=
    fun k => fs_integrable_mul p₀ (hx i) (hx k) (abs_momentMap_le_one · i)
      (abs_momentMap_le_one · k)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the integrated normalisation: `Σ_k E[xᵢxₖ] = E[xᵢ] = 1/N`
  have hsum : ∑ k : Fin N, ∫ p, momentMap p i * momentMap p k ∂(fubiniStudyMeasure p₀)
      = (N : ℝ)⁻¹ := by
    rw [← integral_finsetSum Finset.univ (fun k _ => int_pair k)]
    calc ∫ p, ∑ k : Fin N, momentMap p i * momentMap p k ∂(fubiniStudyMeasure p₀)
        = ∫ p, momentMap p i ∂(fubiniStudyMeasure p₀) :=
          integral_congr_ae (ae_of_all _ (fun p => by
            dsimp only
            rw [← Finset.mul_sum, momentMap_sum_eq_one, mul_one]))
      _ = (N : ℝ)⁻¹ := fsFirstMoment_diag p₀ i
  -- split off the diagonal term
  rw [← Finset.add_sum_erase Finset.univ
    (fun k => ∫ p, momentMap p i * momentMap p k ∂(fubiniStudyMeasure p₀))
    (Finset.mem_univ i)] at hsum
  have hdiag : ∫ p, momentMap p i * momentMap p i ∂(fubiniStudyMeasure p₀)
      = ∫ p, momentMap p i ^ 2 ∂(fubiniStudyMeasure p₀) :=
    integral_congr_ae (ae_of_all _ (fun p => by dsimp only; rw [← pow_two]))
  rw [hdiag] at hsum
  -- every off-diagonal term is half the diagonal one (`a = 2b`)
  rw [show ∑ k ∈ Finset.univ.erase i,
        ∫ p, momentMap p i * momentMap p k ∂(fubiniStudyMeasure p₀)
      = ∑ _k ∈ Finset.univ.erase i,
        (∫ p, momentMap p i ^ 2 ∂(fubiniStudyMeasure p₀)) / 2 from
    Finset.sum_congr rfl (fun k hk => by
      rw [fs_x_sq_eq_two_cross p₀ ((Finset.ne_of_mem_erase hk).symm)]
      ring)] at hsum
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)), Nat.cast_one] at hsum
  -- solve the linear equation `S + (N−1)·S/2 = 1/N`
  rw [show ((N : ℝ))⁻¹ = 1 / (N : ℝ) from (one_div _).symm,
    eq_div_iff hNpos.ne'] at hsum
  rw [eq_div_iff (mul_pos hNpos (by linarith : (0:ℝ) < (N:ℝ) + 1)).ne']
  linear_combination 2 * hsum

/-- ★ **The cross second moment**: `E[xᵢxⱼ] = 1/(N(N+1))` for `i ≠ j`. -/
theorem fs_x_cross_moment [NeZero N] (p₀ : CPN N) {i j : Fin N} (hij : i ≠ j) :
    ∫ p, momentMap p i * momentMap p j ∂(fubiniStudyMeasure p₀)
      = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have h := fs_x_sq_eq_two_cross p₀ hij
  rw [fs_x_sq_moment p₀ i] at h
  linear_combination -h / 2

/-! ### Diagonal statistics: expectation, second moment, Chebyshev -/

/-- The expectation of a diagonal statistic `Σ λₖ·xₖ` is `(Σλ)/N` — the
maximally-mixed value. -/
theorem fs_linear_expectation [NeZero N] (p₀ : CPN N) (lam : Fin N → ℝ) :
    ∫ p, ∑ k, lam k * momentMap p k ∂(fubiniStudyMeasure p₀)
      = (∑ k, lam k) / N := by
  rw [integral_finsetSum Finset.univ (fun k _ =>
    (momentMap_integrable p₀ k).const_mul (lam k))]
  calc ∑ k : Fin N, ∫ p, lam k * momentMap p k ∂(fubiniStudyMeasure p₀)
      = ∑ k : Fin N, lam k * (N : ℝ)⁻¹ :=
        Finset.sum_congr rfl (fun k _ => by
          rw [integral_const_mul, fsFirstMoment_diag p₀ k])
    _ = (∑ k, lam k) / N := by rw [div_eq_mul_inv, ← Finset.sum_mul]

/-- ★ **The second moment of a diagonal statistic**:
`E[(Σ λₖxₖ)²] = ((Σλ)² + Σλ²)/(N(N+1))`. -/
theorem fs_linear_sq_moment [NeZero N] (p₀ : CPN N) (lam : Fin N → ℝ) :
    ∫ p, (∑ k, lam k * momentMap p k) ^ 2 ∂(fubiniStudyMeasure p₀)
      = ((∑ k, lam k) ^ 2 + ∑ k, lam k ^ 2) / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have hx : ∀ a : Fin N, Measurable fun p : CPN N => momentMap p a := momentMap_measurable
  have int_pair : ∀ a b : Fin N, Integrable
      (fun p : CPN N => lam a * lam b * (momentMap p a * momentMap p b))
      (fubiniStudyMeasure p₀) := fun a b =>
    (fs_integrable_mul p₀ (hx a) (hx b) (abs_momentMap_le_one · a)
      (abs_momentMap_le_one · b)).const_mul (lam a * lam b)
  calc ∫ p, (∑ k, lam k * momentMap p k) ^ 2 ∂(fubiniStudyMeasure p₀)
      = ∫ p, ∑ a, ∑ b, lam a * lam b * (momentMap p a * momentMap p b)
          ∂(fubiniStudyMeasure p₀) :=
        integral_congr_ae (ae_of_all _ (fun p => by
          dsimp only
          rw [pow_two, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl (fun a _ =>
            Finset.sum_congr rfl (fun b _ => by ring))))
    _ = ∑ a, ∑ b, ∫ p, lam a * lam b * (momentMap p a * momentMap p b)
          ∂(fubiniStudyMeasure p₀) := by
        rw [integral_finsetSum Finset.univ (fun a _ =>
          integrable_finsetSum Finset.univ (fun b _ => int_pair a b))]
        exact Finset.sum_congr rfl (fun a _ =>
          integral_finsetSum Finset.univ (fun b _ => int_pair a b))
    _ = ∑ a, ∑ b, lam a * lam b *
          (if b = a then 2 / ((N:ℝ) * ((N:ℝ)+1)) else 1 / ((N:ℝ) * ((N:ℝ)+1))) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
          rw [integral_const_mul]
          by_cases hba : b = a
          · rw [if_pos hba, hba]
            congr 1
            calc ∫ p, momentMap p a * momentMap p a ∂(fubiniStudyMeasure p₀)
                = ∫ p, momentMap p a ^ 2 ∂(fubiniStudyMeasure p₀) :=
                  integral_congr_ae (ae_of_all _ (fun p => by
                    dsimp only; rw [← pow_two]))
              _ = 2 / ((N:ℝ) * ((N:ℝ)+1)) := fs_x_sq_moment p₀ a
          · rw [if_neg hba, fs_x_cross_moment p₀ (fun h => hba h.symm)]))
    _ = ((∑ k, lam k) ^ 2 + ∑ k, lam k ^ 2) / ((N : ℝ) * ((N : ℝ) + 1)) := by
        rw [show (∑ a, ∑ b, lam a * lam b *
            (if b = a then 2 / ((N:ℝ) * ((N:ℝ)+1)) else 1 / ((N:ℝ) * ((N:ℝ)+1))))
          = ∑ a : Fin N, (lam a * (∑ k, lam k) * (1 / ((N:ℝ) * ((N:ℝ)+1)))
              + lam a ^ 2 * (1 / ((N:ℝ) * ((N:ℝ)+1)))) from
          Finset.sum_congr rfl (fun a _ => by
            rw [show (∑ b, lam a * lam b *
                (if b = a then 2 / ((N:ℝ) * ((N:ℝ)+1)) else 1 / ((N:ℝ) * ((N:ℝ)+1))))
              = ∑ b : Fin N, (lam a * (1 / ((N:ℝ) * ((N:ℝ)+1))) * lam b
                  + (if b = a then lam a * lam b * (1 / ((N:ℝ) * ((N:ℝ)+1))) else 0)) from
              Finset.sum_congr rfl (fun b _ => by split_ifs <;> ring)]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_eq_single a (fun b _ hba => if_neg hba)
                (fun ha => absurd (Finset.mem_univ a) ha), if_pos rfl]
            ring)]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
          ← Finset.sum_mul]
        ring

/-- ★★ **Chebyshev-grade canonical typicality** (Q24, diagonal form): a single
Fubini–Study sample concentrates its diagonal statistics at the
maximally-mixed value, at rate `Var = (N·Σλ² − (Σλ)²)/(N²(N+1)) = O(1/N)` —
polynomial concentration with no isoperimetry, from the twirl algebra alone. -/
theorem fs_chebyshev_concentration [NeZero N] (p₀ : CPN N) (lam : Fin N → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (fubiniStudyMeasure p₀)
        {p | ε ≤ |(∑ k, lam k * momentMap p k) - (∑ k, lam k) / N|}
      ≤ ENNReal.ofReal ((((N:ℝ) * ∑ k, lam k ^ 2 - (∑ k, lam k) ^ 2)
          / ((N:ℝ) ^ 2 * ((N:ℝ) + 1))) / ε ^ 2) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hXmeas : Measurable fun p : CPN N => ∑ k, lam k * momentMap p k :=
    Finset.measurable_sum Finset.univ (fun k _ =>
      (momentMap_measurable k).const_mul (lam k))
  have hX2 : MemLp (fun p : CPN N => ∑ k, lam k * momentMap p k) 2
      (fubiniStudyMeasure p₀) :=
    MemLp.of_bound hXmeas.aestronglyMeasurable (∑ k, |lam k|)
      (ae_of_all _ (fun p => by
        rw [Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun k _ => ?_))
        rw [abs_mul]
        calc |lam k| * |momentMap p k| ≤ |lam k| * 1 :=
              mul_le_mul_of_nonneg_left (abs_momentMap_le_one p k) (abs_nonneg _)
          _ = |lam k| := mul_one _))
  have hEX : ∫ p, ∑ k, lam k * momentMap p k ∂(fubiniStudyMeasure p₀)
      = (∑ k, lam k) / N := fs_linear_expectation p₀ lam
  have hvar : ProbabilityTheory.variance
        (fun p : CPN N => ∑ k, lam k * momentMap p k) (fubiniStudyMeasure p₀)
      = ((N:ℝ) * ∑ k, lam k ^ 2 - (∑ k, lam k) ^ 2)
          / ((N:ℝ) ^ 2 * ((N:ℝ) + 1)) := by
    rw [ProbabilityTheory.variance_eq_sub hX2]
    rw [show ((fun p : CPN N => ∑ k, lam k * momentMap p k) ^ 2)
        = fun p : CPN N => (∑ k, lam k * momentMap p k) ^ 2 from
      funext (fun p => Pi.pow_apply _ _ _)]
    rw [show (∫ p, (∑ k, lam k * momentMap p k) ^ 2 ∂(fubiniStudyMeasure p₀))
        = ((∑ k, lam k) ^ 2 + ∑ k, lam k ^ 2) / ((N : ℝ) * ((N : ℝ) + 1)) from
      fs_linear_sq_moment p₀ lam]
    rw [show (∫ p, ∑ k, lam k * momentMap p k ∂(fubiniStudyMeasure p₀))
        = (∑ k, lam k) / N from hEX]
    have hN1 : ((N:ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  calc (fubiniStudyMeasure p₀)
        {p | ε ≤ |(∑ k, lam k * momentMap p k) - (∑ k, lam k) / N|}
      = (fubiniStudyMeasure p₀)
          {p | ε ≤ |(∑ k, lam k * momentMap p k)
            - ∫ q, ∑ k, lam k * momentMap q k ∂(fubiniStudyMeasure p₀)|} := by
        rw [hEX]
    _ ≤ ENNReal.ofReal (ProbabilityTheory.variance
          (fun p : CPN N => ∑ k, lam k * momentMap p k)
          (fubiniStudyMeasure p₀) / ε ^ 2) :=
        ProbabilityTheory.meas_ge_le_variance_div_sq hX2 hε
    _ = ENNReal.ofReal ((((N:ℝ) * ∑ k, lam k ^ 2 - (∑ k, lam k) ^ 2)
          / ((N:ℝ) ^ 2 * ((N:ℝ) + 1))) / ε ^ 2) := by rw [hvar]

end Thermo
end CSD
