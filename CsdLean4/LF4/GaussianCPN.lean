import CsdLean4.LF4.GaussianFS
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# LF4 general-N Part 1: `gaussianCPN = fubiniStudyMeasure` on `ℂℙ^{N-1}`

The general-`N` analogue of `GaussianCP.lean` (which handled the qubit `N = 2`):
the Fubini–Study measure on `ℂℙ^{N-1}` is the projectivised standard Gaussian on
`ℂ^N`. This is **Slice B** of the general-N Duistermaat–Heckman programme
(`specs/general-n-dh-plan.md`), the cleanest standalone increment, and unblocks the
Gaussian-route block law (Part 2a) and the Gamma→Dirichlet crux (Part 2b).

To keep `stdGaussian` on a clean *real* `EuclideanSpace` (avoiding the ℝ/ℂ
typeclass diamond on `EuclideanSpace ℂ (Fin N)`), we transport through a hand-built
real coordinate isometry `coordsN : ℝ^{N×2} ≃ₗᵢ[ℝ] ℂ^N`,
`y ↦ (i ↦ y(i,0) + y(i,1)·I)`. The real space is indexed by `Fin N × Fin 2`
(rather than `Fin (2N)`) so each complex coordinate `i` reads its real/imaginary
parts off the clean pair `(i,0)`, `(i,1)` — no `2i`/`2i+1` index arithmetic.

The discharged qubit file `GaussianCP.lean` is left untouched: its `Fin 4`-indexed
machinery (`coords`, `regroup4`, …) is load-bearing for the retired
`fs_moment_pushforward_uniform` axiom, so this is a parallel general-N development
rather than a refactor.
-/

open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### C1 — the real coordinate isometry `ℝ^{N×2} ≃ₗᵢ[ℝ] ℂ^N` -/

/-- **C1 (general N).** The real coordinate isometry
`ℝ^{N×2} ≃ₗᵢ[ℝ] ℂ^N`, `y ↦ (i ↦ y(i,0) + y(i,1)·I)`. -/
noncomputable def coordsN :
    EuclideanSpace ℝ (Fin N × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun y := (WithLp.equiv 2 (Fin N → ℂ)).symm
    (fun i => (y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I)
  invFun z := (WithLp.equiv 2 (Fin N × Fin 2 → ℝ)).symm
    (fun p => if p.2 = 0 then (z p.1).re else (z p.1).im)
  map_add' x y := by
    ext i
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_add, PiLp.toLp_apply, Pi.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_smul, PiLp.toLp_apply, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    change _ = (c : ℂ) * _
    push_cast
    ring
  left_inv y := by
    ext p
    obtain ⟨i, j⟩ := p
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    fin_cases j <;> simp
  right_inv z := by
    ext i
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, show (1 : Fin 2) = 0 ↔ False by decide,
      if_true, if_false]
    exact Complex.re_add_im (z i)
  norm_map' y := by
    show ‖(WithLp.equiv 2 (Fin N → ℂ)).symm
        (fun i => (y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I)‖ = ‖y‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_two]
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Real.norm_eq_abs, sq_abs]
    ring

/-! ### C2/C3 — the projectivised Gaussian -/

/-- **C2 (general N).** The standard Gaussian transported to `ℂ^N`. -/
noncomputable def gaussianHN : Measure (EuclideanSpace ℂ (Fin N)) :=
  Measure.map coordsN (stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2)))

instance instProbGaussianHN : IsProbabilityMeasure (gaussianHN (N := N)) := by
  unfold gaussianHN
  exact Measure.isProbabilityMeasure_map coordsN.continuous.measurable.aemeasurable

/-- The projectivisation map `ℂ^N → ℂℙ^{N-1}`, junk value `p₀` at `0`. -/
noncomputable def gaussianProjN (p₀ : CPN N) (v : EuclideanSpace ℂ (Fin N)) : CPN N :=
  if h : v = 0 then p₀ else Projectivization.mk ℂ v h

lemma measurable_gaussianProjN (p₀ : CPN N) : Measurable (gaussianProjN p₀) := by
  refine measurable_of_measurable_on_compl_singleton 0 ?_
  have hrestr : {v : EuclideanSpace ℂ (Fin N) | v ≠ 0}.restrict (gaussianProjN p₀)
      = fun v => Projectivization.mk' ℂ ⟨v.1, v.2⟩ := by
    funext v
    simp only [Set.restrict_apply, gaussianProjN, dif_neg v.2, Projectivization.mk'_eq_mk]
  rw [hrestr]
  exact Projectivization.measurable_mk'.comp (measurable_subtype_coe.subtype_mk)

/-- **C3 (general N).** The projectivised Gaussian on `ℂℙ^{N-1}`. -/
noncomputable def gaussianCPN (p₀ : CPN N) : Measure (CPN N) :=
  Measure.map (gaussianProjN p₀) gaussianHN

instance instProbGaussianCPN (p₀ : CPN N) : IsProbabilityMeasure (gaussianCPN p₀) := by
  unfold gaussianCPN
  exact Measure.isProbabilityMeasure_map (measurable_gaussianProjN p₀).aemeasurable

/-! ### C4 — `U(N)`-invariance -/

/-- The `ℂ`-linear matrix action `toEuclideanLin U.val` is measurable. -/
lemma measurable_toEuclideanLinN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (Matrix.toEuclideanLin U.val) :=
  (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin U.val)).measurable

/-- A unitary's `toEuclideanLin` action sends nonzero vectors to nonzero vectors. -/
lemma toEuclideanLinN_ne_zero (U : Matrix.unitaryGroup (Fin N) ℂ)
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  apply hv
  have hnorm : ‖(Matrix.toEuclideanLin U.val) v‖ = ‖v‖ := unitary_norm_preserving U v
  rw [h, norm_zero] at hnorm
  exact norm_eq_zero.mp hnorm.symm

/-- `Uᴴ * U = 1` for a unitary matrix. -/
lemma unitary_conjTranspose_mulN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.valᴴ * U.val = 1 := by
  have h := U.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rwa [Matrix.star_eq_conjTranspose] at h

/-- `U * Uᴴ = 1` for a unitary matrix. -/
lemma unitary_mul_conjTransposeN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.val * U.valᴴ = 1 := by
  have h := U.2
  rw [Matrix.mem_unitaryGroup_iff] at h
  rwa [Matrix.star_eq_conjTranspose] at h

/-- `toEuclideanLin U.val` is `ℝ`-linear for the scalar action. -/
lemma toEuclideanLinN_real_smul (U : Matrix.unitaryGroup (Fin N) ℂ)
    (c : ℝ) (w : EuclideanSpace ℂ (Fin N)) :
    (Matrix.toEuclideanLin U.val) (c • w) = c • (Matrix.toEuclideanLin U.val) w := by
  apply (WithLp.equiv 2 (Fin N → ℂ)).injective
  simp only [WithLp.equiv_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_smul]
  exact Matrix.mulVec_smul _ _ _

/-- The real conjugate isometry `conjRN U : ℝ^{N×2} ≃ₗᵢ[ℝ] ℝ^{N×2}`, conjugating
the unitary action on `ℂ^N` through `coordsN`. -/
noncomputable def conjRN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℝ (Fin N × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N × Fin 2) where
  toFun y := coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))
  invFun z := coordsN.symm ((Matrix.toEuclideanLin U.valᴴ) (coordsN z))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, map_smul, toEuclideanLinN_real_smul]
  left_inv y := by
    show coordsN.symm ((Matrix.toEuclideanLin U.valᴴ)
        (coordsN (coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))))) = y
    rw [LinearIsometryEquiv.apply_symm_apply]
    rw [← LinearIsometryEquiv.symm_apply_apply coordsN y]
    apply congrArg coordsN.symm
    apply (WithLp.equiv 2 (Fin N → ℂ)).injective
    simp only [WithLp.equiv_apply, LinearIsometryEquiv.apply_symm_apply,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, unitary_conjTranspose_mulN, Matrix.one_mulVec]
  right_inv z := by
    show coordsN.symm ((Matrix.toEuclideanLin U.val)
        (coordsN (coordsN.symm ((Matrix.toEuclideanLin U.valᴴ) (coordsN z))))) = z
    rw [LinearIsometryEquiv.apply_symm_apply]
    rw [← LinearIsometryEquiv.symm_apply_apply coordsN z]
    apply congrArg coordsN.symm
    apply (WithLp.equiv 2 (Fin N → ℂ)).injective
    simp only [WithLp.equiv_apply, LinearIsometryEquiv.apply_symm_apply,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, unitary_mul_conjTransposeN, Matrix.one_mulVec]
  norm_map' y := by
    show ‖coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))‖ = ‖y‖
    rw [LinearIsometryEquiv.norm_map, unitary_norm_preserving, LinearIsometryEquiv.norm_map]

/-- `coordsN ∘ conjRN U = toEuclideanLin U.val ∘ coordsN`. -/
lemma coordsN_conjRN (U : Matrix.unitaryGroup (Fin N) ℂ)
    (y : EuclideanSpace ℝ (Fin N × Fin 2)) :
    coordsN (conjRN U y) = (Matrix.toEuclideanLin U.val) (coordsN y) := by
  show coordsN (coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- `gaussianHN` is invariant under the unitary matrix action on `ℂ^N`. -/
lemma gaussianHN_map_unitary (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (Matrix.toEuclideanLin U.val) gaussianHN = gaussianHN := by
  unfold gaussianHN
  rw [Measure.map_map (measurable_toEuclideanLinN U) coordsN.continuous.measurable]
  have hcomp : (Matrix.toEuclideanLin U.val) ∘ coordsN = coordsN ∘ (conjRN U) := by
    funext y
    simp only [Function.comp_apply, coordsN_conjRN]
  rw [hcomp, ← Measure.map_map coordsN.continuous.measurable (conjRN U).continuous.measurable,
    stdGaussian_map (conjRN U)]

/-! ### No-atoms at the origin -/

/-- `stdGaussian (ℝ^{N×2})` is not a Dirac measure (needs the space nonempty,
i.e. `N ≥ 1`). -/
lemma stdGaussianN_ne_dirac [NeZero N] (x : EuclideanSpace ℝ (Fin N × Fin 2)) :
    stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2)) ≠ Measure.dirac x := by
  intro hx
  set i₀ : Fin N × Fin 2 := (⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, 0) with hi₀
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) :=
    innerSL ℝ (EuclideanSpace.single i₀ (1 : ℝ)) with hLdef
  have hLnorm : ‖L‖ = 1 := by
    rw [hLdef, innerSL_apply_norm, PiLp.norm_single, norm_one]
  have hvar : Var[L; stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2))] = 1 := by
    rw [variance_dual_stdGaussian, hLnorm, one_pow]
  rw [hx, ProbabilityTheory.variance_dirac] at hvar
  exact zero_ne_one hvar

instance instNoAtomsStdGaussianN [NeZero N] :
    NoAtoms (stdGaussian (EuclideanSpace ℝ (Fin N × Fin 2))) :=
  ProbabilityTheory.IsGaussian.noAtoms stdGaussianN_ne_dirac

/-- The origin is `gaussianHN`-null. -/
lemma gaussianHN_singleton_zero [NeZero N] :
    gaussianHN {(0 : EuclideanSpace ℂ (Fin N))} = 0 := by
  unfold gaussianHN
  rw [Measure.map_apply coordsN.continuous.measurable (measurableSet_singleton 0)]
  have : (coordsN ⁻¹' {(0 : EuclideanSpace ℂ (Fin N))})
      = {(0 : EuclideanSpace ℝ (Fin N × Fin 2))} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, map_eq_zero_iff coordsN coordsN.injective]
  rw [this, measure_singleton]

/-! ### C4 (invariance) and C5 (identification) -/

/-- **C4 (general N).** `gaussianCPN p₀` is `U(N)`-invariant. -/
lemma gaussianCPN_smul_invariant [NeZero N] (p₀ : CPN N) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun p => U • p) (gaussianCPN p₀) = gaussianCPN p₀ := by
  unfold gaussianCPN
  rw [Measure.map_map (continuous_const_smul U).measurable (measurable_gaussianProjN p₀)]
  have hae : ((fun p => U • p) ∘ gaussianProjN p₀)
      =ᵐ[gaussianHN] (gaussianProjN p₀ ∘ (Matrix.toEuclideanLin U.val)) := by
    refine ae_iff.mpr ?_
    refine measure_mono_null ?_ gaussianHN_singleton_zero
    intro v hv
    simp only [Set.mem_setOf_eq, Function.comp_apply] at hv
    by_contra hv0
    simp only [Set.mem_singleton_iff] at hv0
    apply hv
    rw [gaussianProjN, dif_neg hv0, gaussianProjN,
      dif_neg (toEuclideanLinN_ne_zero U hv0), smul_mk_eq_mk U v hv0]
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_gaussianProjN p₀) (measurable_toEuclideanLinN U),
    gaussianHN_map_unitary U]

/-- **C5 (general N): the projectivised Gaussian equals the Fubini–Study measure
on `ℂℙ^{N-1}`.** The general-N analogue of `gaussianCP_eq_fubiniStudy`. -/
lemma gaussianCPN_eq_fubiniStudy [NeZero N] (p₀ : CPN N) :
    gaussianCPN p₀ = fubiniStudyMeasure p₀ :=
  fubiniStudyMeasure_unique p₀ (gaussianCPN p₀) (gaussianCPN_smul_invariant p₀)

end LF4
end CSD
