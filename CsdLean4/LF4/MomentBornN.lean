import CsdLean4.LF4.MomentDirichletN
import CsdLean4.LF4.BornVolume

/-!
# LF4 general-N Slice E (Born lift): Born = Fubini–Study volume ratio on Σ

The general-N analogue of `fs_born_volume_ratio_qubit` (qubit, `N = 2`), now
**unconditional** — the qubit's `h_uniform` hypothesis is the Slice E headline
`fs_moment_joint_dirichlet_N`, which is a theorem. Three steps:

* **E4a `fs_volume_eq_dirichlet`** — the Duistermaat–Heckman volume law on `Σ`:
  the Fubini–Study measure of a measurable moment-coordinate region `R ⊆ openSimplexFree`
  is `M!` times its Lebesgue volume.
* **E4b `volume_openSimplexFree`** — the standard simplex has volume `(M!)⁻¹`, forced
  by `μ_FS` being a probability measure (a simplex-volume fact derived via Kähler
  geometry + Gaussians).
* **E4c `fs_born_volume_ratio_N`** — for each free coordinate `i : Fin M`, the FS
  measure of the `i`-th barycentric region (pulled back through the moment map) equals
  the Born weight `‖⟨e_{castSucc i}, ψ⟩‖²`. No carving, no `busch_effect_gleason`.

## Honest scope

This lands Born on the `N-1` free coordinates `castSucc i`, `i : Fin M` (the qubit
gave `1` of `2`; this gives `N-1` of `N`). The last coordinate (the dropped apex,
index `M`) requires the affine apex map or an a.e.-partition argument; it is the
documented residual. The genericity hypothesis `∀ j, 0 < ‖⟨eⱼ,ψ⟩‖²` (no vanishing
amplitude) makes `freeBornVec ψ` an interior simplex point, so the barycentric region
is a homeomorphic image of the open simplex (hence open, measurable) and stays inside.
-/

open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {M : ℕ}

/-- The free-coordinate moment map `p ↦ ratioN (momentMap p)` is measurable. -/
theorem measurable_ratio_momentMap :
    Measurable (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i)) := by
  have hmoment : Measurable (fun p : CPN (M + 1) => fun i => momentMap p i) :=
    measurable_pi_lambda _ (fun i => momentMap_measurable i)
  have hratio : Measurable (ratioN (M := M)) :=
    measurable_pi_lambda _ (fun k => (measurable_pi_apply _).div
      (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)))
  exact hratio.comp hmoment

/-- **E4a: the Duistermaat–Heckman volume law on `Σ`.** For a measurable region `R` of
the free moment simplex with `R ⊆ openSimplexFree`, the Fubini–Study measure of its
pullback equals `M!` times the Lebesgue volume of `R`. Unconditional; the genuine
general-N DH content on `Σ`. -/
theorem fs_volume_eq_dirichlet (p₀ : CPN (M + 1)) {R : Set (Fin M → ℝ)}
    (hR : MeasurableSet R) (hRsub : R ⊆ openSimplexFree) :
    fubiniStudyMeasure p₀ ((fun p => ratioN (fun i => momentMap p i)) ⁻¹' R)
      = (Nat.factorial M : ℝ≥0∞) * volume R := by
  rw [← Measure.map_apply measurable_ratio_momentMap hR, fs_moment_joint_dirichlet_N,
    Measure.smul_apply, Measure.restrict_apply hR, smul_eq_mul,
    Set.inter_eq_left.mpr hRsub]

/-- **E4b: the standard simplex has volume `(M!)⁻¹`.** Forced by `μ_FS` being a
probability measure: pushing it forward gives `M! · vol|_{openSimplexFree}`, whose total
mass is `1`. A simplex-volume fact obtained via the Kähler/Gaussian route. -/
theorem volume_openSimplexFree :
    volume (openSimplexFree (M := M)) = (Nat.factorial M : ℝ≥0∞)⁻¹ := by
  set p₀ : CPN (M + 1) :=
    Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin (M + 1)) (1 : ℂ))
      (by simp [EuclideanSpace.single]) with hp₀
  have hkey : (Nat.factorial M : ℝ≥0∞) * volume (openSimplexFree (M := M)) = 1 := by
    have h := congrArg (fun μ : Measure (Fin M → ℝ) => μ Set.univ)
      (fs_moment_joint_dirichlet_N p₀)
    simp only [Measure.map_apply measurable_ratio_momentMap MeasurableSet.univ,
      Set.preimage_univ, measure_univ, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul] at h
    exact h.symm
  have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
  have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc volume (openSimplexFree (M := M))
      = ((Nat.factorial M : ℝ≥0∞)⁻¹ * (Nat.factorial M : ℝ≥0∞)) * volume (openSimplexFree (M := M)) := by
        rw [ENNReal.inv_mul_cancel hfac hfac_top, one_mul]
    _ = (Nat.factorial M : ℝ≥0∞)⁻¹ * ((Nat.factorial M : ℝ≥0∞) * volume (openSimplexFree (M := M))) := by
        rw [mul_assoc]
    _ = (Nat.factorial M : ℝ≥0∞)⁻¹ := by rw [hkey, mul_one]

/-! ### E4c: the barycentric region and the Born volume ratio -/

/-- Coordinate formula for the vertex-replacement map:
`(replaceMap b i t) k = b k · t i + (t k if k ≠ i else 0)`. -/
theorem replaceMap_apply {N : ℕ} (b : Fin N → ℝ) (i : Fin N) (t : Fin N → ℝ) (k : Fin N) :
    (replaceMap b i) t k = b k * t i + (if k = i then 0 else t k) := by
  classical
  rw [replaceMap, Matrix.toLin'_apply]
  show (∑ j, ((1 : Matrix (Fin N) (Fin N) ℝ).updateCol i b) k j * t j) = _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_apply, if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hj), Matrix.one_apply, ite_mul,
      one_mul, zero_mul]),
    Finset.sum_ite_eq (Finset.univ.erase i) k t]
  by_cases hk : k = i <;> simp [Finset.mem_erase, hk]

/-- The open free simplex is an open set. -/
theorem isOpen_openSimplexFree {M : ℕ} : IsOpen (openSimplexFree (M := M)) := by
  rw [openSimplexFree, Set.setOf_and]
  refine IsOpen.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
  · exact isOpen_lt (continuous_finset_sum _ fun k _ => continuous_apply k) continuous_const

/-- The `i`-th barycentric region stays inside the simplex when `b` is an interior
point (`b ∈ openSimplexFree`): the subdivision of the simplex at an interior point. -/
theorem replaceMap_image_subset {M : ℕ} (b : Fin M → ℝ) (i : Fin M)
    (hb : b ∈ openSimplexFree) :
    (replaceMap b i) '' openSimplexFree ⊆ openSimplexFree := by
  obtain ⟨hbpos, hbsum⟩ := hb
  rintro _ ⟨t, ⟨htpos, htsum⟩, rfl⟩
  have hcompl : ∑ k, (if k = i then (0 : ℝ) else t k) = (∑ k, t k) - t i := by
    have h1 : ∑ k, ((if k = i then (0 : ℝ) else t k) + (if i = k then t k else 0)) = ∑ k, t k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : k = i
      · subst hk; simp
      · rw [if_neg hk, if_neg (Ne.symm hk), add_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i t,
      if_pos (Finset.mem_univ i)] at h1
    linarith
  refine ⟨fun k => ?_, ?_⟩
  · rw [replaceMap_apply]
    by_cases hk : k = i
    · rw [if_pos hk, add_zero]; exact mul_pos (hbpos k) (htpos i)
    · rw [if_neg hk]; nlinarith [hbpos k, htpos i, htpos k]
  · rw [Finset.sum_congr rfl (fun k _ => replaceMap_apply b i t k), Finset.sum_add_distrib,
      ← Finset.sum_mul, hcompl]
    nlinarith [htsum, mul_pos (htpos i) (sub_pos.mpr hbsum)]

/-- **E4c: Born weight = Fubini–Study volume ratio on `Σ` (general N, free coords).**
For a fully-generic unit preparation `ψ` (no vanishing amplitude), the Fubini–Study
measure of the `i`-th barycentric region of the moment simplex (pulled back through
the moment map) equals the Born weight `‖⟨e_{castSucc i}, ψ⟩‖²`. Unconditional — the
qubit `h_uniform` hypothesis is now the proved headline `fs_moment_joint_dirichlet_N`.
No carving, no `busch_effect_gleason`. -/
theorem fs_born_volume_ratio_N (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) (i : Fin M) :
    fubiniStudyMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' (replaceMap (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) i
            '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  -- The free Born vector's `i`-th coordinate is the Born weight at `castSucc i`.
  have hbi : b i = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2 := by
    rw [hb]
    simp only [ratioN]
    rw [show (∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j) = 1 from
        momentMap_sum_eq_one _, div_one,
      momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc i)]
  -- `b` is an interior simplex point (all free coords positive, sum < 1).
  have hbmem : b ∈ openSimplexFree := by
    refine ⟨fun k => ?_, ?_⟩
    · rw [hb]; simp only [ratioN]
      rw [show (∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j) = 1 from momentMap_sum_eq_one _,
        div_one, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc k)]
      exact hpos _
    · rw [hb]; simp only [ratioN]
      rw [show (∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j) = 1 from momentMap_sum_eq_one _]
      simp only [div_one]
      -- ∑ k, momentMap [ψ] (castSucc k) < 1, since the apex coordinate is positive.
      have hsum1 : ∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j = 1 := momentMap_sum_eq_one _
      have hlast : 0 < momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.last M) := by
        rw [momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.last M)]; exact hpos _
      have hsplit : ∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j
          = (∑ k : Fin M, momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.castSucc k))
            + momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.last M) := Fin.sum_univ_castSucc _
      rw [hsplit] at hsum1
      linarith
  -- det ≠ 0 (= the Born weight, positive), so the region is open, hence measurable.
  have hdet : LinearMap.det (replaceMap b i) ≠ 0 := by
    rw [replaceMap_det, hbi]; exact ne_of_gt (hpos _)
  have hopen : IsOpen ((replaceMap b i) '' openSimplexFree) :=
    LinearMap.isOpenMap_of_finiteDimensional _
      (LinearMap.equivOfDetNeZero (replaceMap b i) hdet).surjective _ isOpen_openSimplexFree
  -- Apply E4a (region measurable + ⊆ openSimplexFree), then E4b and the volume scaling.
  rw [fs_volume_eq_dirichlet p₀ hopen.measurableSet (replaceMap_image_subset b i hbmem),
    replaceMap_image_volume b i (le_of_lt (hbi ▸ hpos (Fin.castSucc i))), volume_openSimplexFree,
    hbi]
  have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
  have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← mul_assoc, mul_comm (Nat.factorial M : ℝ≥0∞)
      (ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2)),
    mul_assoc, ENNReal.mul_inv_cancel hfac hfac_top, mul_one]

end LF4
end CSD
