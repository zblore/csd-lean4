import CsdLean4.LF4.MomentBornN
import CsdLean4.LF4.BornFrequencyPartition

/-!
# LF4 general-N capstone: Busch-free frequency → Born for all N coordinates

The headline empirical payoff of the general-N Duistermaat–Heckman / Born-from-Kähler-
volume programme. The qubit had `qubit_born_frequency_convergence_uncond` (single
outcome, `N = 2`); this is the joint, general-`N`, **unconditional, Busch-free** form:

For i.i.d. trials drawn from the genuine Fubini–Study measure on `ℂℙ^M`, the empirical
frequencies of the `N` barycentric moment-outcome regions converge — on a single
almost-sure event — to the Born weights `‖⟨eᵢ, ψ⟩‖²` of a fully-generic preparation `ψ`.

The Born values enter through `fs_born_volume_ratio_N` (free coordinates) and
`fs_born_volume_ratio_N_apex` (the dropped apex), which are **theorems** (the qubit
`h_uniform` is the proved headline `fs_moment_joint_dirichlet_N`). So the whole chain
is foundational-triple-only: deterministic repeated-trial typicality (LF1) + Born =
Kähler volume (the moment-map cluster) ⟹ frequencies → Born, with Born *derived* from
the symplectic geometry, never imported via Gleason/`busch_effect_gleason`.

Genericity hypothesis `∀ j, 0 < ‖⟨eⱼ, ψ⟩‖²` (no vanishing amplitude): makes the free
Born vector an interior simplex point, so every barycentric region is a homeomorphic
image of the open simplex (open, measurable) and stays inside it.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {M : ℕ}

/-! ### Reusable openness (ψ-agnostic) -/

/-- The image of the open simplex under a `det ≠ 0` vertex-replacement map is open. -/
theorem replaceMap_image_isOpen (b : Fin M → ℝ) (i : Fin M)
    (h : LinearMap.det (replaceMap b i) ≠ 0) :
    IsOpen ((replaceMap b i) '' openSimplexFree) :=
  LinearMap.isOpenMap_of_finiteDimensional _
    (LinearMap.equivOfDetNeZero (replaceMap b i) h).surjective _ isOpen_openSimplexFree

/-- The image of the open simplex under the `det ≠ 0` affine apex map is open. -/
theorem apexLin_image_isOpen (b : Fin M → ℝ) (h : LinearMap.det (apexLin b) ≠ 0) :
    IsOpen ((fun x => apexLin b x + b) '' openSimplexFree) := by
  rw [show (fun x => apexLin b x + b) '' openSimplexFree
        = (fun y => y + b) '' (apexLin b '' openSimplexFree) from
      (Set.image_image (fun y : Fin M → ℝ => y + b) (⇑(apexLin b)) openSimplexFree).symm]
  exact (Homeomorph.addRight b).isOpenMap _
    (LinearMap.isOpenMap_of_finiteDimensional _
      (LinearMap.equivOfDetNeZero (apexLin b) h).surjective _ isOpen_openSimplexFree)

/-! ### Free Born vector coordinates -/

/-- The `k`-th free Born coordinate is the Born weight at `castSucc k`. -/
theorem ratioN_momentMap_castSucc (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (k : Fin M) :
    ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc k) (1 : ℂ)) ψ‖ ^ 2 := by
  simp only [ratioN]
  rw [show (∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j) = 1 from momentMap_sum_eq_one _,
    div_one, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc k)]

/-- `1 − ∑(free Born coords)` is the Born weight at the apex (`Fin.last M`). -/
theorem one_sub_sum_ratioN_momentMap (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) :
    (1 : ℝ) - ∑ k, ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2 := by
  have hsum1 : ∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j = 1 := momentMap_sum_eq_one _
  rw [Fin.sum_univ_castSucc] at hsum1
  have heq : ∑ k, ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ∑ k : Fin M, momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.castSucc k) :=
    Finset.sum_congr rfl (fun k _ => by
      rw [ratioN_momentMap_castSucc ψ hψ0 hψ k, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc k)])
  rw [heq, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.last M)] at *
  linarith

/-! ### The Born outcome regions and the capstone -/

/-- The `N = M+1` barycentric Born outcome regions on `ℂℙ^M`: the `replaceMap`
sub-simplices for the free coordinates and the affine apex region for the last,
pulled back through the moment map. -/
noncomputable def bornRegion (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    Fin (M + 1) → Set (CPN (M + 1)) :=
  Fin.lastCases
    ((fun p => ratioN (fun j => momentMap p j))
      ⁻¹' ((fun x => apexLin (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) x
          + ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) '' openSimplexFree))
    (fun k => (fun p => ratioN (fun j => momentMap p j))
      ⁻¹' (replaceMap (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) k
          '' openSimplexFree))

/-- Each Born region is measurable (an open image pulled back through a measurable map).
An hpos-free form is available: `bornRegion_measurable_uncond` (`BornRegionUncond.lean`). -/
theorem bornRegion_measurable (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) :
    ∀ i, MeasurableSet (bornRegion ψ hψ0 i) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  refine Fin.lastCases ?_ ?_
  · rw [bornRegion, Fin.lastCases_last]
    refine measurable_ratio_momentMap (apexLin_image_isOpen b ?_).measurableSet
    rw [apexLin_det, hb, one_sub_sum_ratioN_momentMap ψ hψ0 hψ]
    exact ne_of_gt (hpos _)
  · intro k
    rw [bornRegion, Fin.lastCases_castSucc]
    refine measurable_ratio_momentMap (replaceMap_image_isOpen b k ?_).measurableSet
    rw [replaceMap_det, hb, ratioN_momentMap_castSucc ψ hψ0 hψ k]
    exact ne_of_gt (hpos _)

/-- The Fubini–Study measure of the `i`-th Born region is the Born weight
`‖⟨eᵢ, ψ⟩‖²` (real form). The "Born = ontic volume" content, supplied by the
volume route — `fs_born_volume_ratio_N` / `_apex`, no Busch.
An hpos-free form is available: `bornRegion_fs_measure_uncond` (`BornRegionUncond.lean`). -/
theorem bornRegion_fs_measure (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) :
    ∀ i, (fubiniStudyMeasure p₀ (bornRegion ψ hψ0 i)).toReal
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  refine Fin.lastCases ?_ ?_
  · rw [bornRegion, Fin.lastCases_last, fs_born_volume_ratio_N_apex p₀ ψ hψ0 hψ hpos,
      ENNReal.toReal_ofReal (le_of_lt (hpos _))]
  · intro k
    rw [bornRegion, Fin.lastCases_castSucc, fs_born_volume_ratio_N p₀ ψ hψ0 hψ hpos k,
      ENNReal.toReal_ofReal (le_of_lt (hpos _))]

/-- **General-`N` Busch-free joint frequency → Born convergence.** For i.i.d. trials
drawn from the Fubini–Study measure on `ℂℙ^M`, the empirical frequencies of the `N`
barycentric Born regions converge, on a single almost-sure event, to the Born weights
`‖⟨eᵢ, ψ⟩‖²` of a fully-generic preparation `ψ`. Foundational-triple-only; **no**
`busch_effect_gleason`. The CSD thesis realised end-to-end for general `N`:
deterministic typicality + Born = Kähler volume ⟹ frequencies → Born.
An hpos-free form is available: `born_frequency_convergence_N_uncond`
(`BornRegionUncond.lean`). -/
theorem born_frequency_convergence_N (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ hψ0 i) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' bornRegion ψ hψ0 i) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  born_frequency_convergence_partition (bornRegion ψ hψ0)
    (bornRegion_measurable ψ hψ0 hψ hpos)
    (fun i => ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    (bornRegion_fs_measure p₀ ψ hψ0 hψ hpos) X hX hlaw hindep

end LF4
end CSD
