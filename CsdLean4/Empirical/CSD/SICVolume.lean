/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.POVMNaimark
public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF2.EffectAux

/-!
# Empirical/CSD: the d=2 SIC-POVM and its Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic layer; the third *non-projective* (POVM) entry in
the volume-frequency series, after the trine and USD).

The **SIC-POVM** (symmetric informationally-complete POVM) in dimension 2 is the
tetrahedral qubit measurement: four fiducial states `|ψₖ⟩` whose Bloch vectors form
a regular tetrahedron, with effects `Eₖ = (1/2)|ψₖ⟩⟨ψₖ|`. It is *symmetric* in the
strong sense that the pairwise overlaps are all equal, `|⟨ψⱼ,ψₖ⟩|² = 1/3` for `j ≠ k`
(`sic_inner_normSq` below) — the defining SIC property — and *informationally
complete* (four outcomes span the operator space of a qubit). It is a genuine POVM:
`∑ₖ Eₖ = I` holds because `∑ₖ |ψₖ⟩⟨ψₖ| = 2 I` (the tetrahedral tight-frame relation).

The explicit fiducial set used here:
`ψ₀ = |0⟩`, `ψₖ = (1/√3)|0⟩ + √(2/3)·ω^{k-1}|1⟩` (`k = 1,2,3`), `ω = e^{2πi/3}`, i.e.
the second components are `√6/3`, `−√6/6 ± i√2/2`.

This file:
- builds `sicPOVM : POVM 2 (Fin 4)` (a `scaledRankOneEffect (1/2)` helper + completeness);
- proves the equiangular SIC property `|⟨ψⱼ,ψₖ⟩|² = 1/3`;
- gives the closed-form Born weights `pₖ(ψ) = (1/2)‖⟨ψ, ψₖ⟩‖²`;
- runs the POVM through the tranche: `canonicalNaimark sicPOVM` is the dilation, and
  `sic_born_frequency_volume` lands the four SIC outcome frequencies as **Fubini–Study
  volumes** on the dilated `Σ' = ℂℙ⁷` — carving-free, Gleason-free.

The capstone routes through the hpos-free engine (`povm_born_frequency_volume_uncond`,
`LF4/BornRegionUncond.lean`), so no genericity hypothesis on the dilated state is
carried (2026-06-11 migration).
-/

@[expose] public section

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace SICVolume

open CSD.LF2 CSD.LF4

/-! ### Square-root facts -/

lemma r2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma r3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma r6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

/-! ### The SIC fiducial states -/

/-- The complex amplitudes of the four tetrahedral SIC states on the computational
basis. `ω = e^{2πi/3}` enters as `ω = −1/2 + i√3/2`, so `√(2/3)·ω = −√6/6 + i√2/2`
and `√(2/3)·ω² = −√6/6 − i√2/2`. -/
noncomputable def sicAmp : Fin 4 → Fin 2 → ℂ
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => ((Real.sqrt 3 / 3 : ℝ) : ℂ)
  | 1, 1 => ((Real.sqrt 6 / 3 : ℝ) : ℂ)
  | 2, 0 => ((Real.sqrt 3 / 3 : ℝ) : ℂ)
  | 2, 1 => ((-(Real.sqrt 6) / 6 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I
  | 3, 0 => ((Real.sqrt 3 / 3 : ℝ) : ℂ)
  | 3, 1 => ((-(Real.sqrt 6) / 6 : ℝ) : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I

/-- The four SIC states as unit vectors in `ℂ²`. -/
noncomputable def sicState (k : Fin 4) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (sicAmp k 0) + EuclideanSpace.single 1 (sicAmp k 1)

lemma sicState_ofLp (k : Fin 4) (i : Fin 2) : (sicState k).ofLp i = sicAmp k i := by
  fin_cases i <;> simp [sicState, EuclideanSpace.single]

lemma sicState_apply (k : Fin 4) (i : Fin 2) : sicState k i = sicAmp k i := by
  fin_cases i <;> simp [sicState, EuclideanSpace.single]

/-- `‖z‖² = z.re·z.re + z.im·z.im`, the bridge to real coordinates. -/
lemma normSq_coord (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

lemma sicState_norm (k : Fin 4) : ‖sicState k‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, sicState_ofLp, sicState_ofLp]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  congr 1
  fin_cases k <;>
    simp only [sicAmp, normSq_coord, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.sub_re,
      Complex.sub_im] <;>
    nlinarith [r2, r3, r6]

/-! ### The tetrahedral tight-frame relation and the POVM -/

/-- `∑ₖ |ψₖ⟩⟨ψₖ| = 2 I` — the tetrahedral tight-frame relation that makes the SIC a
valid POVM. -/
lemma sic_outer_sum :
    ∑ k : Fin 4, outerProduct (sicState k) = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hentry : ∀ k : Fin 4,
      outerProduct (sicState k) i j = sicAmp k i * star (sicAmp k j) := by
    intro k
    rw [outerProduct, Matrix.vecMulVec_apply, sicState_apply, sicState_apply]
  simp_rw [hentry]
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp only [sicAmp, Fin.zero_eta, Fin.mk_one, Matrix.one_apply, Fin.reduceEq, Complex.star_def,
      reduceIte] <;>
    (apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        Complex.zero_re, Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat] <;>
      nlinarith [r2, r3, r6])

/-- The `k`-th SIC effect `Eₖ = (1/2)|ψₖ⟩⟨ψₖ|`. -/
noncomputable def sicEffect (k : Fin 4) : Effect 2 :=
  scaledRankOneEffect (1 / 2) (by norm_num) (by norm_num) (sicState k) (sicState_norm k)

/-- **Completeness:** `∑ₖ Eₖ = (1/2)·(2 I) = I`. The SIC is a genuine POVM. -/
lemma sic_complete : ∑ k : Fin 4, (sicEffect k).M = 1 := by
  have : ∑ k : Fin 4, (sicEffect k).M
      = ((1 / 2 : ℝ) : ℂ) • ∑ k : Fin 4, outerProduct (sicState k) := by
    rw [Finset.smul_sum]; rfl
  rw [this, sic_outer_sum, smul_smul]
  norm_num

/-- **The d=2 SIC-POVM** `{Eₖ = (1/2)|ψₖ⟩⟨ψₖ|}ₖ` — the tetrahedral symmetric
informationally-complete (non-projective) qubit measurement. -/
noncomputable def sicPOVM : POVM 2 (Fin 4) where
  E := sicEffect
  complete := sic_complete

/-! ### The equiangular SIC property -/

/-- `⟨x, y⟩ = star(x₀)·y₀ + star(x₁)·y₁` on `ℂ²`. -/
lemma inner_two (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ x y = star (x.ofLp 0) * y.ofLp 0 + star (x.ofLp 1) * y.ofLp 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [Pi.star_apply]; ring

/-- **The defining SIC symmetry:** all pairwise overlaps are equal,
`|⟨ψⱼ, ψₖ⟩|² = 1/3` for `j ≠ k`. The four states are equiangular — a regular
tetrahedron in the Bloch ball. -/
lemma sic_inner_normSq (j k : Fin 4) (hjk : j ≠ k) :
    ‖inner ℂ (sicState j) (sicState k)‖ ^ 2 = 1 / 3 := by
  rw [inner_two, sicState_ofLp, sicState_ofLp, sicState_ofLp, sicState_ofLp, normSq_coord]
  fin_cases j <;> fin_cases k <;> first
    | (exact absurd rfl hjk)
    | (simp only [sicAmp, Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, Complex.zero_re, Complex.zero_im] ; nlinarith [r2, r3, r6])

/-! ### The SIC Born weights as Kähler volumes -/

/-- **Closed-form SIC Born weights:** for a unit preparation `ψ`,
`pₖ(ψ) = (1/2)‖⟨ψ, ψₖ⟩‖²`. -/
theorem sic_weight_eq (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) (k : Fin 4) :
    sicPOVM.weight ψ k = 1 / 2 * ‖inner ℂ ψ (sicState k)‖ ^ 2 := by
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((sicEffect k).M) ψ)) = _
  rw [sicEffect, scaledRankOneEffect_M]
  exact scaledRankOne_quadratic (1 / 2) (sicState k) ψ (sicState_norm k) hψ

/-- The canonical Naimark dilation of the SIC POVM (it exists, like every POVM's). -/
noncomputable def sicNaimark : NaimarkDilation sicPOVM := canonicalNaimark sicPOVM

/-- **The SIC POVM Born weights as Kähler volumes (the capstone).** Instantiating
`povm_born_frequency_volume_uncond` at the tetrahedral SIC POVM: i.i.d. Fubini–Study
trials on the dilated ontic `Σ' = ℂℙ⁷` have the `k`-th SIC outcome's empirical
frequency converge, on a single almost-sure event, to the SIC Born weight
`pₖ(ψ) = ⟨ψ, Eₖ ψ⟩ = (1/2)‖⟨ψₖ,ψ⟩‖²` — realised as a sum of Fubini–Study volumes of
the dilated barycentric cells. The **third non-projective (POVM) entry in the
volume-frequency series**, after the trine and USD; carving-free, Gleason-free, and
(since the 2026-06-11 hpos migration) with no genericity hypothesis on the dilated
state. -/
theorem sic_born_frequency_volume
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 4) ≃ Fin 8)
    (ψ' : EuclideanSpace ℂ (Fin 8))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin sicNaimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN 8) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 8) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 8,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ k : Fin 4,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (sicPOVM.weight ψ k)) :=
  povm_born_frequency_volume_uncond sicPOVM sicNaimark ψ e ψ' hψ'eq hψ'0 hnorm
    p₀ X hX hlaw hindep

end SICVolume
end CSDBridge
end Empirical
end CSD
