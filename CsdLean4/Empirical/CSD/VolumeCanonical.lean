/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.TrialWitness
public import CsdLean4.Empirical.CSD.BellVolume
public import CsdLean4.Empirical.CSD.GHZVolume
public import CsdLean4.Empirical.CSD.HardyVolume
public import CsdLean4.Empirical.CSD.MalusVolume
public import CsdLean4.Empirical.CSD.SternGerlachVolume
public import CsdLean4.Empirical.CSD.TrineVolume
public import CsdLean4.Empirical.CSD.USDVolume
public import CsdLean4.Empirical.CSD.SICVolume
public import CsdLean4.Empirical.CSD.SIC3Volume
public import CsdLean4.Empirical.CSD.MUB3Volume
public import CsdLean4.Empirical.CSD.QutritPOVMVolume
public import CsdLean4.Empirical.CSD.ContextVolume

/-!
# Empirical/CSD: every volume-frequency headline on the canonical i.i.d. FS witness

**Category:** 3-Local (CSD-ontic volume series, trial-witness coverage tranche).

Each headline of the `Empirical/CSD/*Volume` series quantifies over an abstract
i.i.d. trial bundle `(Ω, Pr, X, hX, hlaw, hindep)`. The canonical FS coordinate
process of `CsdLean4/LF4/TrialWitness.lean`
(`fsTrialMeasure p₀ = Measure.infinitePi (fun _ => fubiniStudyMeasure p₀)`,
`fsTrial N n = (· n)`) inhabits that bundle for **any** measurable region family
(`fsTrial_pairwise_indepFun_indicator`). This file wires the witness into every
remaining volume headline, so each acquires a `_canonical` corollary whose
hypothesis set is **Lean-inhabited**, not merely classically satisfiable.

Each `_canonical` conclusion is the parent's conclusion **verbatim** with
`Pr := fsTrialMeasure p₀` and `X := fsTrial _` substituted; the body is a bare
term-mode application of the parent (no restatement), mirroring
`LF4.born_frequency_convergence_N_canonical`. The region family supplied to the
witness is exactly the parent's `hindep` region family:

* `bornRegion ψ' …` (rotated / dilated state) for the barycentric-cell parents
  (Bell, GHZ, Hardy, Trine, USD, SIC, SIC3, MUB3, QutritPOVM, the Context family),
  with measurability `bornRegion_measurable_uncond`;
* the moment-map sublevel set `{p | momentMap p 0 ≤ momentMap [ψ] 0}` for the
  qubit chain (Malus, Stern-Gerlach), with measurability
  `(momentMap_measurable 0) measurableSet_Iic`.

The POVM headline `LF4.povm_born_frequency_volume_canonical` lives in
`TrialWitness.lean` itself (import-direction constraint:
`POVMVolume → BornRegionUncond → TrialWitness`).

## Honest scope

This is **coverage / completeness**, not new mathematics or a thesis advance: the
witness and the discharge mechanism already existed (the i.i.d. trial-witness
tranche); this file leaves no volume-frequency headline merely
classically-satisfiable. The honest-scope caveat is unchanged: this is the
**measure-theoretic existence** of the i.i.d. sampling law; the physical reading
of repeated preparation as FS-typical i.i.d. draws remains the LF1 typicality /
A5 posit, not derived by constructing the process. Foundational-triple-only;
Gleason-free (no `busch_effect_gleason`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge

/-! ### Bell singlet (CPN 4) -/

namespace BellVolume

/-- `bell_singlet_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem bell_singlet_born_frequency_volume_canonical (θ : ℝ) (p₀ : CPN 4) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial 4 k) ⁻¹' bornRegion (bellSingletVec θ) (bellSingletVec_ne_zero θ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (bellSingletVec θ)‖ ^ 2)) :=
  bell_singlet_born_frequency_volume θ p₀
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (bellSingletVec θ) (bellSingletVec_ne_zero θ))
      (bornRegion_measurable_uncond (bellSingletVec θ) (bellSingletVec_ne_zero θ)))

end BellVolume

/-! ### GHZ (CPN 8) -/

namespace GHZVolume

/-- `ghz_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem ghz_born_frequency_volume_canonical (Φ : ℝ) (p₀ : CPN 8) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 8,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial 8 k) ⁻¹' bornRegion (ghzVec Φ) (ghzVec_ne_zero Φ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (ghzVec Φ)‖ ^ 2)) :=
  ghz_born_frequency_volume Φ p₀
    (fsTrial 8) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion (ghzVec Φ) (ghzVec_ne_zero Φ))
      (bornRegion_measurable_uncond (ghzVec Φ) (ghzVec_ne_zero Φ)))

end GHZVolume

/-! ### Hardy (CPN 4) -/

namespace HardyVolume

/-- `hardy_max_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem hardy_max_born_frequency_volume_canonical (p₀ : CPN 4) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial 4 k) ⁻¹' bornRegion hardyVolVec hardyVolVec_ne_zero i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) hardyVolVec‖ ^ 2)) :=
  hardy_max_born_frequency_volume p₀
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion hardyVolVec hardyVolVec_ne_zero)
      (bornRegion_measurable_uncond hardyVolVec hardyVolVec_ne_zero))

end HardyVolume

/-! ### Malus / Stern-Gerlach (CPN 2, moment-map sublevel region) -/

namespace MalusVolume

/-- `csd_malus_law` on the canonical i.i.d. FS process. The region family is the
moment-map sublevel set; measurability via `(momentMap_measurable 0)
measurableSet_Iic`, supplied through a `Unit`-indexed family. -/
theorem csd_malus_law_canonical (θ : ℝ) (p₀ : CPN 2) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((fsTrial 2 i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ (malusVec θ) (malusVec_ne_zero θ)) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (Real.cos (θ / 2) ^ 2)) :=
  csd_malus_law θ p₀
    (fsTrial 2) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (fun _ : Unit => {p : CPN 2 | momentMap p 0 ≤
          momentMap (Projectivization.mk ℂ (malusVec θ) (malusVec_ne_zero θ)) 0})
      (fun _ => (momentMap_measurable 0) measurableSet_Iic) ())

end MalusVolume

namespace SternGerlachVolume

/-- `csd_sg_volume_certain` on the canonical i.i.d. FS process. -/
theorem csd_sg_volume_certain_canonical (p₀ : CPN 2) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((fsTrial 2 i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ zPlusVec zPlusVec_ne_zero) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (1 : ℝ)) :=
  csd_sg_volume_certain p₀
    (fsTrial 2) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (fun _ : Unit => {p : CPN 2 | momentMap p 0 ≤
          momentMap (Projectivization.mk ℂ zPlusVec zPlusVec_ne_zero) 0})
      (fun _ => (momentMap_measurable 0) measurableSet_Iic) ())

/-- `csd_sg_volume_half` on the canonical i.i.d. FS process. -/
theorem csd_sg_volume_half_canonical (p₀ : CPN 2) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((fsTrial 2 i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ balVec balVec_ne_zero) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (1 / 2 : ℝ)) :=
  csd_sg_volume_half p₀
    (fsTrial 2) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (fun _ : Unit => {p : CPN 2 | momentMap p 0 ≤
          momentMap (Projectivization.mk ℂ balVec balVec_ne_zero) 0})
      (fun _ => (momentMap_measurable 0) measurableSet_Iic) ())

end SternGerlachVolume

/-! ### POVM-dilation barycentric headlines (Trine, USD, SIC, SIC3, MUB3, QutritPOVM) -/

namespace TrineVolume

open CSD.LF2 CSD.LF4

/-- `trine_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem trine_born_frequency_volume_canonical
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 3) ≃ Fin 6)
    (ψ' : EuclideanSpace ℂ (Fin 6))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin trineNaimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 6) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ k : Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 6 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (trinePOVM.weight ψ k)) :=
  trine_born_frequency_volume ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 6) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end TrineVolume

namespace USDVolume

open CSD.LF2 CSD.LF4 CSD.Empirical.QM.USD

/-- `usd_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem usd_born_frequency_volume_canonical (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 3) ≃ Fin 6)
    (ψ' : EuclideanSpace ℂ (Fin 6))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin (usdNaimark s hs0 hs1).V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 6) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ k : Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 6 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds ((usdPOVM s hs0 hs1).weight ψ k)) :=
  usd_born_frequency_volume s hs0 hs1 ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 6) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end USDVolume

namespace SICVolume

open CSD.LF2 CSD.LF4

/-- `sic_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem sic_born_frequency_volume_canonical
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 4) ≃ Fin 8)
    (ψ' : EuclideanSpace ℂ (Fin 8))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin sicNaimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 8) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ k : Fin 4,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 8 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (sicPOVM.weight ψ k)) :=
  sic_born_frequency_volume ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 8) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end SICVolume

namespace SIC3Volume

open CSD.LF2 CSD.LF4

/-- `sic3_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem sic3_born_frequency_volume_canonical
    (ψ : EuclideanSpace ℂ (Fin 3)) (e : (Fin 3 × (Fin 3 × Fin 3)) ≃ Fin 27)
    (ψ' : EuclideanSpace ℂ (Fin 27))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin sic3Naimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 27) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 3 × Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 3,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 27 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (sic3POVM.weight ψ i)) :=
  sic3_born_frequency_volume ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 27) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end SIC3Volume

namespace MUB3Volume

open CSD.LF2 CSD.LF4

/-- `mub3_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem mub3_born_frequency_volume_canonical
    (ψ : EuclideanSpace ℂ (Fin 3)) (e : (Fin 3 × (Fin 4 × Fin 3)) ≃ Fin 36)
    (ψ' : EuclideanSpace ℂ (Fin 36))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin mub3Naimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 36) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 4 × Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 3,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 36 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (mub3POVM.weight ψ i)) :=
  mub3_born_frequency_volume ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 36) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end MUB3Volume

namespace QutritPOVMVolume

open CSD.LF2 CSD.LF4

/-- `noisy_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem noisy_born_frequency_volume_canonical (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 3)) (e : (Fin 3 × Fin 3) ≃ Fin 9)
    (ψ' : EuclideanSpace ℂ (Fin 9))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin (noisyNaimark ε hε0 hε1).V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 9) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ k : Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 3,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 9 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds ((noisyPOVM ε hε0 hε1).weight ψ k)) :=
  noisy_born_frequency_volume ε hε0 hε1 ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 9) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end QutritPOVMVolume

/-! ### Projective measurement contexts (CPN (M+1)): the rotated-basis cells -/

namespace ContextVolume

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `context_born_frequency_volume` on the canonical i.i.d. FS process. The region
family is the rotated-basis cell `bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ)`. -/
theorem context_born_frequency_volume_canonical
    (p₀ : CPN (M + 1))
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial (M + 1) k) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (B i) ψ‖ ^ 2)) :=
  context_born_frequency_volume p₀ B ψ hψ
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ))
      (bornRegion_measurable_uncond (B.repr ψ) (repr_ne_zero B ψ hψ)))

omit [Fintype ι] in
/-- `block_born_frequency_volume_event` on the canonical i.i.d. FS process. The
**inhabited block form** (the union-event restatement of `block_born_frequency_volume`,
which is superseded for the canonical purpose; its sum-form canonical is omitted). -/
theorem block_born_frequency_volume_event_canonical
    (p₀ : CPN (M + 1))
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    (blk : Fin (M + 1) → ι) (a : ι) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial (M + 1) k) ⁻¹' (⋃ i ∈ Finset.univ.filter (fun i => blk i = a),
                    bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (∑ i ∈ Finset.univ.filter (fun i => blk i = a),
          ‖inner ℂ (B i) ψ‖ ^ 2)) :=
  block_born_frequency_volume_event p₀ B ψ hψ blk a
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ))
      (bornRegion_measurable_uncond (B.repr ψ) (repr_ne_zero B ψ hψ)))

/-- `zz_parity_born_frequency_volume` on the canonical i.i.d. FS process. -/
theorem zz_parity_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1, 0] : Fin 4 → Fin 2) i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
                    (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (3 : Fin 4) (1 : ℂ)) ψ‖ ^ 2)) :=
  zz_parity_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
        (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ))
      (bornRegion_measurable_uncond ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
        (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ)))

end ContextVolume

end CSDBridge
end Empirical
end CSD
