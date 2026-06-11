import CsdLean4.LF4.BornFrequencyN
import CsdLean4.LF4.POVMVolume

/-!
# LF4: the Born-region volume/frequency engine, unconditional (genericity retired)

**Category:** 3-Local (LF4 Born-from-Kähler-volume engine, hpos-free upgrade).

The general-`N` Born = FS-volume engine (`fs_born_volume_ratio_N` / `_apex`,
`bornRegion_fs_measure`, `born_frequency_convergence_N`) and the POVM tranche
wrappers (`povm_born_eq_dilated_volume`, `povm_born_frequency_volume`) carried a
**genericity hypothesis** `hpos : ∀ j, 0 < ‖⟨eⱼ, ψ⟩‖²` (no vanishing amplitude).
This file retires that caveat: every result is re-proved for an arbitrary unit
`ψ ≠ 0`, with statements otherwise verbatim (`_uncond` suffixes). **Additive**:
the audited originals in `MomentBornN.lean` / `BornFrequencyN.lean` /
`POVMVolume.lean` are untouched; corpus-wide call-site migration is deferred.

## The per-cell dichotomy

For any unit `ψ`, the free Born vector `b` lies in the **closed** free simplex
(`0 ≤ b k`, `∑ b ≤ 1` — free, from `momentMap_sum_eq_one` + nonnegativity of
`‖·‖²`). Per cell:

* **positive branch** (`b i > 0`): `det (replaceMap b i) = b i ≠ 0` per cell (no
  joint hypothesis), and the simplex-subdivision subset lemma survives with only
  the closed-simplex bounds (`replaceMap_image_subset_of_closedSimplex`). The
  audited `fs_volume_eq_dirichlet` + `replaceMap_image_volume` route then runs
  verbatim.
* **zero branch** (`b i = 0`): `det = 0`, so the cell's Lebesgue volume vanishes
  (`Measure.addHaar_image_linearMap` at `|det| = 0`); the joint Dirichlet law
  (`fs_volume_eq_dirichlet_inter`, no subset hypothesis) then forces the FS
  measure of the pulled-back cell to `0` — which **is** the Born weight.
* **apex cell**: the same dichotomy on `1 − ∑ b` via `apexLin` (affine image =
  translate of a linear image).

Measurability of a degenerate (det-0) image cannot use the open-image argument;
instead every cell image is measurable **det-free**: `openSimplexFree` is an
open subset of `ℝ^M`, hence σ-compact, and continuous images of σ-compact sets
are σ-compact, hence Borel (`image_openSimplexFree_measurableSet`).

No carving: the regions are the same ψ-indexed moment-subdivision cells as the
audited engine; the zero-weight cells genuinely collapse to FS-null sets, they
are not redefined to hit Born values. Gleason-free throughout (no
`busch_effect_gleason`).
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

open CSD.LF2

variable {M : ℕ}

/-! ### Det-free measurability of the barycentric cell images (σ-compact route) -/

/-- The open free simplex is σ-compact: it is an open subset of the locally
compact, second-countable `ℝ^M`, hence itself a locally compact second-countable
space, hence σ-compact (`sigmaCompactSpace_of_locallyCompact_secondCountable`). -/
theorem isSigmaCompact_openSimplexFree :
    IsSigmaCompact (openSimplexFree (M := M)) := by
  haveI : LocallyCompactSpace (openSimplexFree (M := M)) :=
    (isOpen_openSimplexFree (M := M)).locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

/-- **Det-free measurability of continuous images of the open simplex.** The
continuous image of a σ-compact set is σ-compact — a countable union of
compacts, each closed (T2) hence Borel. Replaces the open-image argument, which
dies at `det = 0`. -/
theorem image_openSimplexFree_measurableSet {f : (Fin M → ℝ) → (Fin M → ℝ)}
    (hf : Continuous f) : MeasurableSet (f '' openSimplexFree) := by
  obtain ⟨K, hK, hKeq⟩ := isSigmaCompact_openSimplexFree.image hf
  rw [← hKeq]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

/-- The `i`-th barycentric cell image is measurable, for **every** `b` (no
determinant hypothesis). -/
theorem replaceMap_image_measurableSet (b : Fin M → ℝ) (i : Fin M) :
    MeasurableSet ((replaceMap b i) '' openSimplexFree) :=
  image_openSimplexFree_measurableSet (replaceMap b i).continuous_of_finiteDimensional

/-- The apex barycentric cell image is measurable, for **every** `b` (no
determinant hypothesis). -/
theorem apexMap_image_measurableSet (b : Fin M → ℝ) :
    MeasurableSet ((fun x => apexLin b x + b) '' openSimplexFree) :=
  image_openSimplexFree_measurableSet
    ((apexLin b).continuous_of_finiteDimensional.add continuous_const)

/-! ### The joint Dirichlet law without the subset hypothesis -/

/-- The Duistermaat–Heckman volume law for an **arbitrary** measurable region
`R` (no `R ⊆ openSimplexFree`): the FS measure of the pullback is `M!` times the
Lebesgue volume of `R ∩ openSimplexFree`. The zero-branch workhorse — the proof
is `fs_volume_eq_dirichlet`'s minus its final subset rewrite. -/
theorem fs_volume_eq_dirichlet_inter (p₀ : CPN (M + 1)) {R : Set (Fin M → ℝ)}
    (hR : MeasurableSet R) :
    fubiniStudyMeasure p₀ ((fun p => ratioN (fun i => momentMap p i)) ⁻¹' R)
      = (Nat.factorial M : ℝ≥0∞) * volume (R ∩ openSimplexFree) := by
  rw [← Measure.map_apply measurable_ratio_momentMap hR, fs_moment_joint_dirichlet_N,
    Measure.smul_apply, Measure.restrict_apply hR, smul_eq_mul]

/-! ### Subset lemmas under the closed-simplex bounds -/

/-- **Subdivision subset lemma, closed-simplex form.** The `i`-th barycentric
cell stays inside the simplex assuming only `0 ≤ b`, `∑ b ≤ 1`, and the
**per-cell** positivity `0 < b i` (the only coordinate whose strict positivity
the `k = i` coordinate of the image needs). Replaces the joint-genericity
hypothesis `b ∈ openSimplexFree` of `replaceMap_image_subset`. -/
theorem replaceMap_image_subset_of_closedSimplex (b : Fin M → ℝ) (i : Fin M)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k ≤ 1) (hbi : 0 < b i) :
    (replaceMap b i) '' openSimplexFree ⊆ openSimplexFree := by
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
    · rw [if_pos hk, add_zero, hk]
      exact mul_pos hbi (htpos i)
    · rw [if_neg hk]
      have hbk := mul_nonneg (hb0 k) (le_of_lt (htpos i))
      linarith [htpos k]
  · rw [Finset.sum_congr rfl (fun k _ => replaceMap_apply b i t k), Finset.sum_add_distrib,
      ← Finset.sum_mul, hcompl]
    nlinarith [htsum, mul_nonneg (sub_nonneg.mpr hbsum) (le_of_lt (htpos i))]

/-- **Apex subset lemma, closed-simplex form.** The apex cell stays inside the
simplex assuming only `0 ≤ b` and `∑ b < 1` (which *is* the apex positive-branch
hypothesis: the apex weight is `1 − ∑ b`). Replaces `b ∈ openSimplexFree` of
`apexMap_image_subset`. -/
theorem apexMap_image_subset_of_closedSimplex (b : Fin M → ℝ)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k < 1) :
    (fun x => apexLin b x + b) '' openSimplexFree ⊆ openSimplexFree := by
  rintro _ ⟨t, ⟨htpos, htsum⟩, rfl⟩
  have happ : ∀ k, (apexLin b t + b) k = t k + (1 - ∑ j, t j) * b k := by
    intro k; rw [Pi.add_apply, apexLin_apply]; ring
  refine ⟨fun k => ?_, ?_⟩
  · show (0 : ℝ) < (apexLin b t + b) k
    rw [happ]
    have hbk := mul_nonneg (le_of_lt (sub_pos.mpr htsum)) (hb0 k)
    linarith [htpos k]
  · show ∑ k, (apexLin b t + b) k < 1
    simp_rw [happ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_pos (sub_pos.mpr htsum) (sub_pos.mpr hbsum)]

/-! ### Apex cell volume (any `b` in the closed simplex) -/

/-- The apex cell's Lebesgue volume is `(1 − ∑ b)` times the simplex volume, for
any `b` with `∑ b ≤ 1` — including the degenerate `∑ b = 1`, where the affine
image is a translate of a `det = 0` linear image, hence null. (Translation
invariance + `Measure.addHaar_image_linearMap` + `apexLin_det`.) -/
theorem apexMap_image_volume (b : Fin M → ℝ) (hb : 0 ≤ 1 - ∑ k, b k) :
    volume ((fun x => apexLin b x + b) '' openSimplexFree)
      = ENNReal.ofReal (1 - ∑ k, b k) * volume (openSimplexFree (M := M)) := by
  have hregion : (fun x => apexLin b x + b) '' openSimplexFree
      = (fun y => y + b) '' (apexLin b '' openSimplexFree) :=
    (Set.image_image (fun y : Fin M → ℝ => y + b) (⇑(apexLin b)) openSimplexFree).symm
  have htrans : volume ((fun y : Fin M → ℝ => y + b) '' (apexLin b '' openSimplexFree))
      = volume (apexLin b '' openSimplexFree) := by
    rw [show (fun y : Fin M → ℝ => y + b) '' (apexLin b '' openSimplexFree)
          = (fun y => y + (-b)) ⁻¹' (apexLin b '' openSimplexFree) from by
        ext y; simp only [Set.mem_image, Set.mem_preimage]
        exact ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx,
          fun hy => ⟨y + (-b), hy, by abel⟩⟩,
      measure_preimage_add_right]
  rw [hregion, htrans, Measure.addHaar_image_linearMap, apexLin_det, abs_of_nonneg hb]

/-! ### The unconditional volume headlines (per-cell dichotomy) -/

/-- **Born = FS-volume ratio, free coordinates, unconditional.** Statement of
`fs_born_volume_ratio_N` with the genericity hypothesis `hpos` removed: valid
for **every** unit preparation `ψ ≠ 0`. Positive cells by the closed-simplex
subset argument; zero cells by the det-0 null image + the joint Dirichlet law
(the cell's FS volume genuinely vanishes — no carving). -/
theorem fs_born_volume_ratio_N_uncond (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin M) :
    fubiniStudyMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' (replaceMap (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) i
            '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  have hbi : b i = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2 := by
    rw [hb]; exact ratioN_momentMap_castSucc ψ hψ0 hψ i
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [hb, ratioN_momentMap_castSucc ψ hψ0 hψ k]; positivity
  have hbsum : ∑ k, b k ≤ 1 := by
    have h := one_sub_sum_ratioN_momentMap ψ hψ0 hψ
    rw [← hb] at h
    linarith [sq_nonneg ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖]
  rcases (hb0 i).lt_or_eq with hbi_pos | hbi_zero
  · -- positive branch: det = b i ≠ 0, the audited route verbatim.
    have hdet : LinearMap.det (replaceMap b i) ≠ 0 := by
      rw [replaceMap_det]; exact ne_of_gt hbi_pos
    rw [fs_volume_eq_dirichlet p₀ (replaceMap_image_isOpen b i hdet).measurableSet
        (replaceMap_image_subset_of_closedSimplex b i hb0 hbsum hbi_pos),
      replaceMap_image_volume b i (hb0 i), volume_openSimplexFree, hbi]
    have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← mul_assoc, mul_comm (Nat.factorial M : ℝ≥0∞)
        (ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2)),
      mul_assoc, ENNReal.mul_inv_cancel hfac hfac_top, mul_one]
  · -- zero branch: det = 0 ⟹ the cell is Lebesgue-null ⟹ FS-null = Born weight.
    have hvol : volume ((replaceMap b i) '' openSimplexFree) = 0 := by
      rw [replaceMap_image_volume b i (hb0 i), ← hbi_zero, ENNReal.ofReal_zero, zero_mul]
    have hinter : volume ((replaceMap b i '' openSimplexFree) ∩ openSimplexFree) = 0 :=
      measure_mono_null Set.inter_subset_left hvol
    rw [fs_volume_eq_dirichlet_inter p₀ (replaceMap_image_measurableSet b i), hinter,
      mul_zero, ← hbi, ← hbi_zero, ENNReal.ofReal_zero]

/-- **Born = FS-volume ratio, apex coordinate, unconditional.** Statement of
`fs_born_volume_ratio_N_apex` with `hpos` removed: the dichotomy on the apex
weight `1 − ∑ b`. -/
theorem fs_born_volume_ratio_N_apex_uncond (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fubiniStudyMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' ((fun x => apexLin (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) x
              + ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  have hlast : (1 : ℝ) - ∑ k, b k
      = ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2 := by
    have h := one_sub_sum_ratioN_momentMap ψ hψ0 hψ
    rw [← hb] at h
    exact h
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [hb, ratioN_momentMap_castSucc ψ hψ0 hψ k]; positivity
  have hb_nonneg : 0 ≤ 1 - ∑ k, b k := by rw [hlast]; positivity
  rcases hb_nonneg.lt_or_eq with hpos | hzero
  · -- positive branch: apex weight 1 − ∑b > 0 (= the subset lemma's hypothesis).
    have hbsum : ∑ k, b k < 1 := by linarith
    have hdet : LinearMap.det (apexLin b) ≠ 0 := by
      rw [apexLin_det]; exact ne_of_gt hpos
    rw [fs_volume_eq_dirichlet p₀ (apexLin_image_isOpen b hdet).measurableSet
        (apexMap_image_subset_of_closedSimplex b hb0 hbsum),
      apexMap_image_volume b hb_nonneg, volume_openSimplexFree, hlast]
    have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← mul_assoc, mul_comm (Nat.factorial M : ℝ≥0∞)
        (ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2)),
      mul_assoc, ENNReal.mul_inv_cancel hfac hfac_top, mul_one]
  · -- zero branch: ∑b = 1 ⟹ det (apexLin b) = 0 ⟹ null cell = Born weight 0.
    have hvol : volume ((fun x => apexLin b x + b) '' openSimplexFree) = 0 := by
      rw [apexMap_image_volume b hb_nonneg, ← hzero, ENNReal.ofReal_zero, zero_mul]
    have hinter :
        volume (((fun x => apexLin b x + b) '' openSimplexFree) ∩ openSimplexFree) = 0 :=
      measure_mono_null Set.inter_subset_left hvol
    rw [fs_volume_eq_dirichlet_inter p₀ (apexMap_image_measurableSet b), hinter,
      mul_zero, ← hlast, ← hzero, ENNReal.ofReal_zero]

/-! ### The unconditional Born regions, frequency capstone, POVM wrappers -/

/-- Each Born region is measurable — for **every** `ψ ≠ 0` (no norm or
genericity hypothesis; the σ-compact image argument is det-free). -/
theorem bornRegion_measurable_uncond (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    ∀ i, MeasurableSet (bornRegion ψ hψ0 i) := by
  refine Fin.lastCases ?_ ?_
  · rw [bornRegion, Fin.lastCases_last]
    exact measurable_ratio_momentMap (apexMap_image_measurableSet _)
  · intro k
    rw [bornRegion, Fin.lastCases_castSucc]
    exact measurable_ratio_momentMap (replaceMap_image_measurableSet _ k)

/-- **Born = FS volume of the Born regions, unconditional** (real form).
`bornRegion_fs_measure` minus `hpos`. -/
theorem bornRegion_fs_measure_uncond (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    ∀ i, (fubiniStudyMeasure p₀ (bornRegion ψ hψ0 i)).toReal
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  refine Fin.lastCases ?_ ?_
  · rw [bornRegion, Fin.lastCases_last, fs_born_volume_ratio_N_apex_uncond p₀ ψ hψ0 hψ,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro k
    rw [bornRegion, Fin.lastCases_castSucc, fs_born_volume_ratio_N_uncond p₀ ψ hψ0 hψ k,
      ENNReal.toReal_ofReal (sq_nonneg _)]

/-- **General-`N` Busch-free joint frequency → Born convergence, unconditional.**
`born_frequency_convergence_N` minus `hpos`: valid for every unit preparation,
vanishing amplitudes included (their regions are FS-null and their frequencies
converge to `0` = the Born weight). Foundational-triple-only. -/
theorem born_frequency_convergence_N_uncond (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
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
    (bornRegion_measurable_uncond ψ hψ0)
    (fun i => ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    (bornRegion_fs_measure_uncond p₀ ψ hψ0 hψ) X hX hlaw hindep

section POVM

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **POVM Born weight as a sum of FS volumes, unconditional (P.3b minus
`hpos`).** The dilated state may have vanishing amplitudes (as the von Neumann
post-flow state does on every off-diagonal cell); the corresponding cells are
FS-null and contribute `0` to the block sum. -/
theorem povm_born_eq_dilated_volume_uncond {M : ℕ} (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (i : ι)
    (e : (Fin N × ι) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (hnorm : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ)‖ = 1) :
    P.weight ψ i
      = ∑ n : Fin N,
          (fubiniStudyMeasure p₀
            (bornRegion (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
              (by intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm)
              (e (n, i)))).toReal := by
  set ψ' := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ) with hψ'
  have hψ'0 : ψ' ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
  have hinner : ∀ n : Fin N,
      ‖inner ℂ (EuclideanSpace.single (e (n, i)) (1 : ℂ)) ψ'‖ ^ 2
        = ‖inner ℂ (EuclideanSpace.single ((n, i) : Fin N × ι) (1 : ℂ))
            (Matrix.toEuclideanLin D.V ψ)‖ ^ 2 := by
    intro n
    rw [hψ', ← EuclideanSpace.piLpCongrLeft_single e (n, i) (1 : ℂ),
      LinearIsometryEquiv.inner_map_map]
  rw [povm_born_eq_block_sum P D ψ i]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bornRegion_fs_measure_uncond p₀ ψ' hψ'0 hnorm (e (n, i)), hinner n]

/-- **POVM empirical frequencies → POVM Born weight, unconditional (P.4 minus
`hpos`).** Valid for every unit dilated preparation, vanishing dilated
amplitudes included. -/
theorem povm_born_frequency_volume_uncond {M : ℕ} (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (e : (Fin N × ι) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : ι,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (P.weight ψ i)) := by
  filter_upwards [born_frequency_convergence_N_uncond p₀ ψ' hψ'0 hnorm X hX hlaw hindep]
    with ω hω
  intro i
  have hlim := tendsto_finset_sum (Finset.univ : Finset (Fin N))
    (fun n (_ : n ∈ Finset.univ) => hω (e (n, i)))
  rwa [show (∑ n : Fin N, ‖inner ℂ (EuclideanSpace.single (e (n, i)) (1 : ℂ)) ψ'‖ ^ 2)
        = P.weight ψ i from by
      rw [povm_born_eq_block_sum P D ψ i, hψ'eq]
      exact Finset.sum_congr rfl (fun n _ => piLpCongrLeft_inner_single_sq e _ (n, i))] at hlim

end POVM

end LF4
end CSD
