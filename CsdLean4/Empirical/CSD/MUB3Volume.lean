import CsdLean4.LF4.POVMNaimark
import CsdLean4.LF4.BornRegionUncond
import CsdLean4.LF2.EffectAux

/-!
# Empirical/CSD: the d=3 mutually-unbiased-bases POVM and its Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic layer; a second non-qubit (`N = 3`) symmetric entry in
the volume-frequency series — the complete set of mutually unbiased bases in dimension 3).

In dimension `d = 3` there are `d + 1 = 4` **mutually unbiased bases** (MUBs): the
computational basis together with three Fourier-type bases from the Heisenberg–Weyl /
Alltop construction, `v_{a,j}[l] = ω^{a l² + j l}/√3` (`a, j ∈ Fin 3`, `ω = e^{2πi/3}`).
Any two vectors from *different* bases satisfy `|⟨v, w⟩|² = 1/d = 1/3` — they are
*unbiased* (`mub3_unbiased`). The `4 · 3 = 12` vectors form a tight frame, so the effects
`Eₖ = (1/4)|ψₖ⟩⟨ψₖ|` give a genuine (non-projective) POVM with `∑ Eₖ = I₃`: pooling a
measurement in each of the 4 bases with prior `1/4`.

This file:
- builds `mub3POVM : POVM 3 (Fin 4 × Fin 3)` (a `scaledRankOneEffect (1/4)` helper + the
  tight-frame completeness `∑|ψₖ⟩⟨ψₖ| = 4 I₃`);
- proves the defining unbiasedness `|⟨v, w⟩|² = 1/3` across distinct bases;
- gives the closed-form Born weights `p_{b,j}(ψ) = (1/4)‖⟨v_{b,j}, ψ⟩‖²`;
- runs it through the POVM tranche: `canonicalNaimark mub3POVM` is the dilation, and
  `mub3_born_frequency_volume` lands the twelve outcome frequencies as **Fubini–Study
  volumes** on the dilated ontic `Σ' = ℂℙ³⁵` — carving-free, Gleason-free.

The dilation lives on `ℂℙ^{N·|ι|−1} = ℂℙ³⁵` (`N = 3`, `|ι| = 12`). The capstone routes
through the hpos-free engine (`povm_born_frequency_volume_uncond`,
`LF4/BornRegionUncond.lean`), so no genericity hypothesis on the dilated state is
carried (2026-06-11 migration) — notably, MUB vectors themselves (which zero the other
two outcomes of their own basis) are covered.

## Source

Wootters, Fields 1989, *Ann. Phys.* **191**, 363 (MUBs from finite fields); Ivonovic 1981.
The d=3 MUB POVM is the canonical complete-MUB measurement.
-/

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace MUB3Volume

open CSD.LF2 CSD.LF4

/-! ### Constants and square-root facts -/

/-- `1/√3`. -/
noncomputable def cc : ℂ := ((Real.sqrt 3 / 3 : ℝ) : ℂ)
/-- `ω = e^{2πi/3} = −1/2 + i√3/2`. -/
noncomputable def om : ℂ := ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I
/-- `ω² = e^{−2πi/3} = −1/2 − i√3/2`. -/
noncomputable def om2 : ℂ := ((-1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

private lemma r3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma r3_4 : Real.sqrt 3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, r3]; norm_num

private lemma normSq_coord (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

/-! ### The 12 MUB vectors -/

/-- The amplitudes of the twelve MUB vectors `v_{b,j}` (basis `b ∈ Fin 4`, vector
`j ∈ Fin 3`) on the computational basis. Basis `0` is computational; bases `1,2,3` are the
Fourier-type bases `a = b−1`, `v_{a,j}[l] = ω^{a l² + j l}/√3`. -/
noncomputable def mubAmp : Fin 4 → Fin 3 → Fin 3 → ℂ
  -- basis 0: computational `e_j`
  | 0, 0, 0 => 1 | 0, 0, 1 => 0 | 0, 0, 2 => 0
  | 0, 1, 0 => 0 | 0, 1, 1 => 1 | 0, 1, 2 => 0
  | 0, 2, 0 => 0 | 0, 2, 1 => 0 | 0, 2, 2 => 1
  -- basis 1 (a = 0): (1, ωʲ, ω²ʲ)/√3
  | 1, 0, 0 => cc | 1, 0, 1 => cc | 1, 0, 2 => cc
  | 1, 1, 0 => cc | 1, 1, 1 => cc * om | 1, 1, 2 => cc * om2
  | 1, 2, 0 => cc | 1, 2, 1 => cc * om2 | 1, 2, 2 => cc * om
  -- basis 2 (a = 1): (1, ω^{1+j}, ω^{1+2j})/√3
  | 2, 0, 0 => cc | 2, 0, 1 => cc * om | 2, 0, 2 => cc * om
  | 2, 1, 0 => cc | 2, 1, 1 => cc * om2 | 2, 1, 2 => cc
  | 2, 2, 0 => cc | 2, 2, 1 => cc | 2, 2, 2 => cc * om2
  -- basis 3 (a = 2): (1, ω^{2+j}, ω^{2+2j})/√3
  | 3, 0, 0 => cc | 3, 0, 1 => cc * om2 | 3, 0, 2 => cc * om2
  | 3, 1, 0 => cc | 3, 1, 1 => cc | 3, 1, 2 => cc * om
  | 3, 2, 0 => cc | 3, 2, 1 => cc * om | 3, 2, 2 => cc

/-- The twelve MUB vectors as unit vectors in `ℂ³`. -/
noncomputable def mubVec (b : Fin 4) (j : Fin 3) : EuclideanSpace ℂ (Fin 3) :=
  EuclideanSpace.single 0 (mubAmp b j 0) + EuclideanSpace.single 1 (mubAmp b j 1)
    + EuclideanSpace.single 2 (mubAmp b j 2)

lemma mubVec_ofLp (b : Fin 4) (j : Fin 3) (l : Fin 3) : (mubVec b j).ofLp l = mubAmp b j l := by
  fin_cases l <;> simp [mubVec, EuclideanSpace.single]

lemma mubVec_apply (b : Fin 4) (j : Fin 3) (l : Fin 3) : mubVec b j l = mubAmp b j l := by
  fin_cases l <;> simp [mubVec, EuclideanSpace.single]

lemma mubVec_norm (b : Fin 4) (j : Fin 3) : ‖mubVec b j‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, mubVec_ofLp, mubVec_ofLp, mubVec_ofLp]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  congr 1
  fin_cases b <;> fin_cases j <;>
    simp only [mubAmp, cc, om, om2, normSq_coord, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] <;>
    nlinarith [r3, r3_4]

/-! ### The tight-frame relation and the POVM -/

/-- `∑_{b,j} |v_{b,j}⟩⟨v_{b,j}| = 4 I₃` — the MUB tight-frame relation (4 bases, each a
resolution of the identity). -/
lemma mub3_outer_sum :
    ∑ b : Fin 4, ∑ j : Fin 3, outerProduct (mubVec b j)
      = (4 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i k
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply]
  have hentry : ∀ b : Fin 4, ∀ j : Fin 3,
      outerProduct (mubVec b j) i k = mubAmp b j i * star (mubAmp b j k) := by
    intro b j
    rw [outerProduct, Matrix.vecMulVec_apply, mubVec_apply, mubVec_apply]
  simp_rw [hentry, Fin.sum_univ_three, Fin.sum_univ_four]
  fin_cases i <;> fin_cases k <;>
    (rw [Matrix.smul_apply, smul_eq_mul];
      first
        | rw [Matrix.one_apply_eq]
        | rw [Matrix.one_apply_ne (by decide)]) <;>
    simp only [mubAmp, cc, om, om2, Complex.star_def, mul_one, mul_zero] <;>
    (apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im, Complex.re_ofNat,
        Complex.im_ofNat] <;>
      ring_nf <;>
      nlinarith [r3, r3_4])

/-- The `(b,j)`-th MUB effect `E_{b,j} = (1/4)|v_{b,j}⟩⟨v_{b,j}|`. -/
noncomputable def mubEffect (i : Fin 4 × Fin 3) : Effect 3 :=
  scaledRankOneEffect (1 / 4) (by norm_num) (by norm_num)
    (mubVec i.1 i.2) (mubVec_norm i.1 i.2)

/-- **Completeness:** `∑_{b,j} E_{b,j} = (1/4)(4 I₃) = I₃`. The MUB pooling is a POVM. -/
lemma mub3_complete : ∑ i : Fin 4 × Fin 3, (mubEffect i).M = 1 := by
  have : ∑ i : Fin 4 × Fin 3, (mubEffect i).M
      = ((1 / 4 : ℝ) : ℂ) • ∑ b : Fin 4, ∑ j : Fin 3, outerProduct (mubVec b j) := by
    rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.smul_sum]
    rfl
  rw [this, mub3_outer_sum, smul_smul]
  norm_num

/-- **The d=3 complete-MUB POVM** `{E_{b,j} = (1/4)|v_{b,j}⟩⟨v_{b,j}|}` — pooling a
measurement in each of the four mutually unbiased bases with prior `1/4`. -/
noncomputable def mub3POVM : POVM 3 (Fin 4 × Fin 3) where
  E := mubEffect
  complete := mub3_complete

/-! ### The unbiasedness property -/

/-- `⟨x, y⟩ = ∑ⱼ star(xⱼ)·yⱼ` on `ℂ³`. -/
private lemma inner_three (x y : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ x y = star (x.ofLp 0) * y.ofLp 0 + star (x.ofLp 1) * y.ofLp 1
      + star (x.ofLp 2) * y.ofLp 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp only [Pi.star_apply]; ring

set_option maxHeartbeats 1600000 in
/-- **Mutual unbiasedness:** any two vectors from *different* bases overlap with
`|⟨v_{b,j}, v_{b',j'}⟩|² = 1/d = 1/3`. The defining MUB property. -/
lemma mub3_unbiased (b b' : Fin 4) (j j' : Fin 3) (h : b ≠ b') :
    ‖inner ℂ (mubVec b j) (mubVec b' j')‖ ^ 2 = 1 / 3 := by
  rw [inner_three, mubVec_ofLp, mubVec_ofLp, mubVec_ofLp, mubVec_ofLp, mubVec_ofLp,
    mubVec_ofLp, normSq_coord]
  fin_cases b <;> fin_cases b' <;> fin_cases j <;> fin_cases j' <;>
    first
      | exact absurd rfl h
      | (simp only [mubAmp, cc, om, om2, Complex.star_def, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.neg_re,
          Complex.neg_im] <;> ring_nf <;> nlinarith [r3, r3_4])

/-! ### The Born weights as Kähler volumes -/

/-- **Closed-form MUB Born weights:** for a unit preparation `ψ`,
`p_{b,j}(ψ) = (1/4)‖⟨v_{b,j}, ψ⟩‖²`. -/
theorem mub3_weight_eq (ψ : EuclideanSpace ℂ (Fin 3)) (hψ : ‖ψ‖ = 1) (i : Fin 4 × Fin 3) :
    mub3POVM.weight ψ i = 1 / 4 * ‖inner ℂ ψ (mubVec i.1 i.2)‖ ^ 2 := by
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((mubEffect i).M) ψ)) = _
  rw [mubEffect, scaledRankOneEffect_M]
  exact scaledRankOne_quadratic (1 / 4) (mubVec i.1 i.2) ψ (mubVec_norm i.1 i.2) hψ

/-- The canonical Naimark dilation of the d=3 MUB POVM. -/
noncomputable def mub3Naimark : NaimarkDilation mub3POVM := canonicalNaimark mub3POVM

/-- **The d=3 MUB POVM Born weights as Kähler volumes (the capstone).** Instantiating
`povm_born_frequency_volume_uncond` at the complete-MUB measurement: i.i.d. Fubini–Study
trials on the dilated ontic `Σ' = ℂℙ³⁵` have each of the twelve outcome frequencies
converge, on a single almost-sure event, to the Born weight
`p_{b,j}(ψ) = (1/4)‖⟨v_{b,j},ψ⟩‖²` — realised as a sum of Fubini–Study volumes of the
dilated barycentric cells. A second non-qubit symmetric entry; carving-free,
Gleason-free, and (since the 2026-06-11 hpos migration) with no genericity hypothesis
on the dilated state. -/
theorem mub3_born_frequency_volume
    (ψ : EuclideanSpace ℂ (Fin 3)) (e : (Fin 3 × (Fin 4 × Fin 3)) ≃ Fin 36)
    (ψ' : EuclideanSpace ℂ (Fin 36))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin mub3Naimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN 36) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 36) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 36,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 4 × Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 3,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (mub3POVM.weight ψ i)) :=
  povm_born_frequency_volume_uncond mub3POVM mub3Naimark ψ e ψ' hψ'eq hψ'0 hnorm
    p₀ X hX hlaw hindep

end MUB3Volume
end CSDBridge
end Empirical
end CSD
