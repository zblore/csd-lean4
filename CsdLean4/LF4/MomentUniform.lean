import CsdLean4.LF4.MomentRatioUniform
import CsdLean4.LF4.GaussianCP
import CsdLean4.LF4.MomentMap
import CsdLean4.LF4.DuistermaatHeckman

/-!
# LF4 plan B, Part 2, Slice 4: assembly + discharge of `fs_moment_pushforward_uniform`

Composes the three closed slices into the moment-marginal headline and discharges
the Duistermaat–Heckman axiom for the qubit:

`fs_moment_pushforward_uniform_thm : (momentMap · 0)∗ fubiniStudyMeasure p₀
  = volume.restrict (Icc 0 1)`.

Chain:
- **L5.2c (bridge)** `regroupPi_map`: `regroup4∗ (pi gaussianReal) = gaussian2 × gaussian2`,
  via `finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4`
  (`measurePreserving_piCongrLeft` + `measurePreserving_sumPiEquivProdPi`
  + `measurePreserving_finTwoArrow`); the composite equiv equals `regroup4` exactly.
- **L5** `moment_marginal_uniform_pi`: `Tpi∗ (pi gaussianReal) = volume.restrict (Ioo 0 1)`,
  composing the bridge with `blockSqNorm_map_gaussian2_prod` (L5.2b) and
  `ratioSqNorm_map_expHalf_prod` (L5.3).
- **L6** rewrites `fubiniStudyMeasure = gaussianCP` (Part 1), pushes through
  `gaussianProj`/`coords` to `stdGaussian(ℝ⁴) = (pi gaussianReal).map (toLp 2)`,
  identifies the moment composition with `Tpi` a.e. (off the null `{0}`), and
  applies L5; `Ioo 0 1 → Icc 0 1` since the endpoints are `volume`-null.

This retires `CSD.LF4.fs_moment_pushforward_uniform` from the axiom list (it becomes
a theorem); the unconditional qubit Born results become foundational-triple-only.
See `specs/plan-b-detail.md` Part 2, Slice 4.
-/

open MeasureTheory ProbabilityTheory Module Real Set Matrix.UnitaryGroup
open scoped ENNReal

namespace CSD
namespace LF4

/-- Regroup `Fin 4 → ℝ` coordinates into two pairs `((y₀,y₁),(y₂,y₃))`. -/
def regroup4 (y : Fin 4 → ℝ) : (ℝ × ℝ) × (ℝ × ℝ) := ((y 0, y 1), (y 2, y 3))

set_option maxHeartbeats 1000000 in
/-- **L5.2c (the bridge).** `regroup4∗ (pi gaussianReal) = gaussian2 × gaussian2`.
Via `finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4` (which sends `inl 0,inl 1,inr 0,inr 1`
to `0,1,2,3`), so the composite measure-preserving equiv has underlying map
`regroup4` (`hfun`). -/
theorem regroupPi_map :
    Measure.map regroup4 (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1))
      = gaussian2.prod gaussian2 := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) finSumFinEquiv).symm
      (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 1)) := by
    have hpc := measurePreserving_piCongrLeft (μ := fun _ : Fin 4 => gaussianReal 0 1)
      (f := (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4))
    exact hpc.symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))
      (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 1))
      ((Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))) :=
    measurePreserving_sumPiEquivProdPi (fun _ => gaussianReal 0 1)
  have h3 : MeasurePreserving
      (Prod.map (⇑MeasurableEquiv.finTwoArrow) (⇑MeasurableEquiv.finTwoArrow))
      ((Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)))
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
        ((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    (measurePreserving_finTwoArrow _).prod (measurePreserving_finTwoArrow _)
  have hfun : regroup4
      = ((Prod.map (⇑MeasurableEquiv.finTwoArrow) (⇑MeasurableEquiv.finTwoArrow))
          ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)))
          ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) finSumFinEquiv).symm := by
    funext y
    have hsymm : ∀ s : Fin 2 ⊕ Fin 2,
        (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) finSumFinEquiv).symm y s
          = y (finSumFinEquiv s) := by
      intro s
      change (Equiv.piCongrLeft (fun _ : Fin 4 => ℝ) finSumFinEquiv).symm y s = y (finSumFinEquiv s)
      rw [Equiv.piCongrLeft_symm_apply]
    simp only [Function.comp_apply, regroup4, Prod.map_apply,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.finTwoArrow_apply, hsymm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> exact congrArg y (by decide)
  have hA : Measurable (Prod.map (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)))
      (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)))) :=
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurable.prodMap
      (MeasurableEquiv.finTwoArrow (α := ℝ)).measurable
  have hB : Measurable (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).measurable
  have hC : Measurable (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.measurable
  rw [hfun, ← Measure.map_map (hA.comp hB) hC, ← Measure.map_map hA hB,
    h1.map_eq, h2.map_eq, h3.map_eq, ← gaussian2_eq_prod]

/-- The squared-norm-block map. -/
noncomputable def blockLsq : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ :=
  Prod.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)

/-- The ratio map. -/
noncomputable def ratioFn : ℝ × ℝ → ℝ := fun q => q.1 / (q.1 + q.2)

/-- The full moment-marginal map on `Fin 4 → ℝ`:
`Tpi y = (y₀²+y₁²)/(y₀²+y₁²+y₂²+y₃²)`. -/
noncomputable def Tpi : (Fin 4 → ℝ) → ℝ := ratioFn ∘ blockLsq ∘ regroup4

theorem measurable_regroup4 : Measurable regroup4 := by
  unfold regroup4; fun_prop

/-- **L5.** `Tpi∗ (pi gaussianReal) = volume.restrict (Ioo 0 1)`. -/
theorem moment_marginal_uniform_pi :
    Measure.map Tpi (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1))
      = (volume : Measure ℝ).restrict (Ioo 0 1) := by
  have hb : Measurable blockLsq := by unfold blockLsq; fun_prop
  have hr : Measurable ratioFn := by
    unfold ratioFn; exact measurable_fst.div (measurable_fst.add measurable_snd)
  rw [Tpi, ← Measure.map_map hr (hb.comp measurable_regroup4),
    ← Measure.map_map hb measurable_regroup4, regroupPi_map,
    show Measure.map blockLsq (gaussian2.prod gaussian2) = expHalf.prod expHalf from
      blockSqNorm_map_gaussian2_prod,
    show Measure.map ratioFn (expHalf.prod expHalf) = (volume : Measure ℝ).restrict (Ioo 0 1) from
      ratioSqNorm_map_expHalf_prod]

/-- The `pi gaussianReal` measure has no atom at the origin. -/
theorem pi_gaussianReal_singleton_zero :
    Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) {(0 : Fin 4 → ℝ)} = 0 := by
  rw [show ({(0 : Fin 4 → ℝ)} : Set (Fin 4 → ℝ)) = Set.univ.pi (fun _ => {(0 : ℝ)}) by
      ext f; simp only [Set.mem_singleton_iff, Set.mem_univ_pi, funext_iff]; rfl,
    Measure.pi_pi]
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  exact Finset.prod_eq_zero (Finset.mem_univ 0) (measure_singleton 0)

set_option maxHeartbeats 1000000 in
/-- **L6 / discharge.** The moment-map coordinate pushes the genuine Fubini–Study
measure on `ℂℙ¹` to the uniform measure on `[0,1]`. This is the qubit
Duistermaat–Heckman / Archimedes fact, now a *theorem* (no longer an axiom),
discharged via the Gaussian-induced realisation of `μ_FS` (Part 1) and the
moment-marginal computation (Slices 1–3). Formerly the axiom
`fs_moment_pushforward_uniform` (DuistermaatHeckman.lean). -/
theorem fs_moment_pushforward_uniform (p₀ : CPN 2) :
    Measure.map (fun p => momentMap p 0) (fubiniStudyMeasure p₀)
      = (volume : Measure ℝ).restrict (Set.Icc 0 1) := by
  rw [show (volume : Measure ℝ).restrict (Set.Icc 0 1)
        = (volume : Measure ℝ).restrict (Ioo 0 1) from (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm,
    ← moment_marginal_uniform_pi, ← gaussianCP_eq_fubiniStudy, gaussianCP, gaussianH,
    Measure.map_map (momentMap_measurable 0) (measurable_gaussianProj p₀),
    Measure.map_map ((momentMap_measurable 0).comp (measurable_gaussianProj p₀))
      coords.continuous.measurable,
    ← map_pi_eq_stdGaussian,
    Measure.map_map (((momentMap_measurable 0).comp (measurable_gaussianProj p₀)).comp
      coords.continuous.measurable) (by fun_prop)]
  refine Measure.map_congr ?_
  have hae : ∀ᵐ y ∂(Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)), y ≠ (0 : Fin 4 → ℝ) := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [show {a : Fin 4 → ℝ | a = 0} = {(0 : Fin 4 → ℝ)} from by ext a; simp]
    exact pi_gaussianReal_singleton_zero
  filter_upwards [hae] with y hy
  simp only [Function.comp_apply]
  -- abbreviate the lifted vector and establish it is nonzero
  set v : EuclideanSpace ℂ (Fin 2) := coords (WithLp.toLp 2 y) with hvdef
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    intro h
    apply hy
    have hz : (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 4)) = 0 :=
      coords.injective (by rw [h, map_zero])
    simpa using congrArg (WithLp.equiv 2 (Fin 4 → ℝ)) hz
  rw [gaussianProj, dif_neg hv0, momentMap_mk v hv0 0]
  -- `v 0 = y₀ + y₁·i`, `‖v‖² = ∑ yᵢ²`.
  have hv0val : ‖v 0‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    have hv0eq : v 0 = ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := rfl
    rw [hv0eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hvnorm : ‖v‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := by
    rw [hvdef, coords.norm_map, EuclideanSpace.norm_eq, Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_four]
    norm_num [Real.norm_eq_abs, sq_abs]
  rw [hv0val, hvnorm, Tpi, Function.comp_apply, Function.comp_apply, regroup4, blockLsq,
    Prod.map_apply, ratioFn]
  congr 1
  ring

/-- **Unconditional qubit Born = Fubini–Study volume ratio on `ℂℙ¹`.** The genuine
`fubiniStudyMeasure` of the moment sublevel set at `[ψ]` equals the Born weight
`‖⟨e₀, ψ⟩‖²`. Foundational-triple-only (the DH/Archimedes input
`fs_moment_pushforward_uniform` is now a theorem); **no** `busch_effect_gleason`. -/
theorem fs_born_volume_ratio_qubit_uncond
    (p₀ : CPN 2) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fubiniStudyMeasure p₀
        {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0}
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2) :=
  fs_born_volume_ratio_qubit p₀ ψ hψ0 hψ (fs_moment_pushforward_uniform p₀)

/-- **Unconditional Busch-free qubit Born frequency convergence.** For i.i.d.
trials from the Fubini–Study measure on `ℂℙ¹`, the empirical frequency of the
moment sublevel outcome converges almost surely to the Born weight `‖⟨e₀, ψ⟩‖²`.
Foundational-triple-only; **no** `busch_effect_gleason`. The CSD thesis realised
unconditionally for the qubit: deterministic typicality + Born = Kähler volume ⟹
frequencies → Born. -/
theorem qubit_born_frequency_convergence_uncond
    (p₀ : CPN 2) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Filter.Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        Filter.atTop
        (nhds (‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2)) :=
  qubit_born_frequency_convergence p₀ ψ hψ0 hψ (fs_moment_pushforward_uniform p₀) X hX hlaw hindep

end LF4
end CSD
