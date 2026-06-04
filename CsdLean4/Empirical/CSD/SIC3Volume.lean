import CsdLean4.LF4.POVMNaimark
import CsdLean4.LF4.POVMVolume
import CsdLean4.LF2.EffectAux

/-!
# Empirical/CSD: the d=3 SIC-POVM (Hesse) and its Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic layer; the first **symmetric** non-qubit (`N = 3`)
entry in the volume-frequency series — the genuine dimension-3 SIC).

The **d=3 SIC-POVM** (symmetric informationally-complete POVM in dimension three) is the
Hesse configuration: the `9 = d²` Weyl–Heisenberg orbit states of the fiducial
`f = (0, 1, −1)/√2`, `ψ_{a,b} = Xᵃ Zᵇ f` with `X` the cyclic shift `|j⟩ ↦ |j+1⟩`, `Z` the
clock `|j⟩ ↦ ωʲ|j⟩`, `ω = e^{2πi/3}`. Concretely

```
ψ_{0,b} ∝ (0, ωᵇ, −ω²ᵇ),   ψ_{1,b} ∝ (−ω²ᵇ, 0, ωᵇ),   ψ_{2,b} ∝ (ωᵇ, −ω²ᵇ, 0)
```

(each `× 1/√2`). The effects are `E_{a,b} = (1/3)|ψ_{a,b}⟩⟨ψ_{a,b}|`; it is a genuine
POVM because the orbit is a tight frame, `∑_{a,b}|ψ_{a,b}⟩⟨ψ_{a,b}| = 3 I₃`, so
`∑ E_{a,b} = I₃`. It is *symmetric* in the strong (SIC) sense `|⟨ψⱼ,ψₖ⟩|² = 1/4` for
`j ≠ k` (`sic3_inner_normSq`), the dimension-3 analogue of the qubit tetrahedron.

This file:
- builds `sic3POVM : POVM 3 (Fin 3 × Fin 3)` (a `scaledRankOneEffect (1/3)` helper + the
  Weyl–Heisenberg tight-frame completeness);
- proves the equiangular SIC property `|⟨ψⱼ,ψₖ⟩|² = 1/4`;
- gives the closed-form Born weights `p_{a,b}(ψ) = (1/3)‖⟨ψ_{a,b}, ψ⟩‖²`;
- runs it through the POVM tranche: `canonicalNaimark sic3POVM` is the dilation, and
  `sic3_born_frequency_volume` lands the nine outcome frequencies as **Fubini–Study
  volumes** on the dilated ontic `Σ' = ℂℙ²⁶` — carving-free, Gleason-free.

The first *symmetric* qutrit entry; the dilation lives on `ℂℙ^{N·|ι|−1} = ℂℙ²⁶`
(`N = 3`, `|ι| = 9`). The genericity `hpos` is carried as in the general capstone.

## Source

Zauner 1999 (thesis); Renes, Blume-Kohout, Scott, Caves 2004, *J. Math. Phys.* **45**,
2171 (the d=3 SIC / Hesse configuration).
-/

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace SIC3Volume

open CSD.LF2 CSD.LF4

/-! ### Constants and square-root facts -/

/-- `1/√2`. -/
noncomputable def cc : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
/-- `ω = e^{2πi/3} = −1/2 + i√3/2`. -/
noncomputable def om : ℂ := ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I
/-- `ω² = e^{−2πi/3} = −1/2 − i√3/2`. -/
noncomputable def om2 : ℂ := ((-1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

private lemma r2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma r3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma r6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
private lemma r2_4 : Real.sqrt 2 ^ 4 = 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, r2]; norm_num
private lemma r3_4 : Real.sqrt 3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, r3]; norm_num

/-- `‖z‖² = z.re·z.re + z.im·z.im`, the bridge to real coordinates. -/
private lemma normSq_coord (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

/-! ### The 9 SIC fiducial states (Weyl–Heisenberg orbit) -/

/-- The amplitudes of the nine SIC states `ψ_{a,b}` (`a, b ∈ Fin 3`) on the
computational basis. `ψ_{a,b}[j] = ω^{(j−a)b}·f_{j−a}` with `f = (0, 1, −1)/√2`. -/
noncomputable def sicAmp : Fin 3 → Fin 3 → Fin 3 → ℂ
  | 0, 0, 0 => 0 | 0, 0, 1 => cc | 0, 0, 2 => -cc
  | 0, 1, 0 => 0 | 0, 1, 1 => cc * om | 0, 1, 2 => -cc * om2
  | 0, 2, 0 => 0 | 0, 2, 1 => cc * om2 | 0, 2, 2 => -cc * om
  | 1, 0, 0 => -cc | 1, 0, 1 => 0 | 1, 0, 2 => cc
  | 1, 1, 0 => -cc * om2 | 1, 1, 1 => 0 | 1, 1, 2 => cc * om
  | 1, 2, 0 => -cc * om | 1, 2, 1 => 0 | 1, 2, 2 => cc * om2
  | 2, 0, 0 => cc | 2, 0, 1 => -cc | 2, 0, 2 => 0
  | 2, 1, 0 => cc * om | 2, 1, 1 => -cc * om2 | 2, 1, 2 => 0
  | 2, 2, 0 => cc * om2 | 2, 2, 1 => -cc * om | 2, 2, 2 => 0

/-- The nine SIC states as unit vectors in `ℂ³`. -/
noncomputable def sicState (a b : Fin 3) : EuclideanSpace ℂ (Fin 3) :=
  EuclideanSpace.single 0 (sicAmp a b 0) + EuclideanSpace.single 1 (sicAmp a b 1)
    + EuclideanSpace.single 2 (sicAmp a b 2)

lemma sicState_ofLp (a b : Fin 3) (j : Fin 3) : (sicState a b).ofLp j = sicAmp a b j := by
  fin_cases j <;> simp [sicState, EuclideanSpace.single]

lemma sicState_apply (a b : Fin 3) (j : Fin 3) : sicState a b j = sicAmp a b j := by
  fin_cases j <;> simp [sicState, EuclideanSpace.single]

lemma sicState_norm (a b : Fin 3) : ‖sicState a b‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, sicState_ofLp, sicState_ofLp, sicState_ofLp]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  congr 1
  fin_cases a <;> fin_cases b <;>
    simp only [sicAmp, cc, om, om2, normSq_coord, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] <;>
    nlinarith [r2, r3, r6]

/-! ### The Weyl–Heisenberg tight-frame relation and the POVM -/

/-- `∑_{a,b} |ψ_{a,b}⟩⟨ψ_{a,b}| = 3 I₃` — the tight-frame relation making the SIC a POVM. -/
lemma sic3_outer_sum :
    ∑ a : Fin 3, ∑ b : Fin 3, outerProduct (sicState a b)
      = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply]
  have hentry : ∀ a b : Fin 3,
      outerProduct (sicState a b) i j = sicAmp a b i * star (sicAmp a b j) := by
    intro a b
    rw [outerProduct, Matrix.vecMulVec_apply, sicState_apply, sicState_apply]
  simp_rw [hentry, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.smul_apply, smul_eq_mul];
      first
        | rw [Matrix.one_apply_eq]
        | rw [Matrix.one_apply_ne (by decide)]) <;>
    simp only [sicAmp, cc, om, om2, Complex.star_def, mul_one, mul_zero] <;>
    (apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im, Complex.re_ofNat,
        Complex.im_ofNat] <;>
      ring_nf <;>
      nlinarith [r2, r3, r6])

/-- The `(a,b)`-th SIC effect `E_{a,b} = (1/3)|ψ_{a,b}⟩⟨ψ_{a,b}|`. -/
noncomputable def sicEffect (i : Fin 3 × Fin 3) : Effect 3 :=
  scaledRankOneEffect (1 / 3) (by norm_num) (by norm_num)
    (sicState i.1 i.2) (sicState_norm i.1 i.2)

/-- **Completeness:** `∑_{a,b} E_{a,b} = (1/3)(3 I₃) = I₃`. The d=3 SIC is a genuine POVM. -/
lemma sic3_complete : ∑ i : Fin 3 × Fin 3, (sicEffect i).M = 1 := by
  have : ∑ i : Fin 3 × Fin 3, (sicEffect i).M
      = ((1 / 3 : ℝ) : ℂ) • ∑ a : Fin 3, ∑ b : Fin 3, outerProduct (sicState a b) := by
    rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
    rfl
  rw [this, sic3_outer_sum, smul_smul]
  norm_num

/-- **The d=3 SIC-POVM** `{E_{a,b} = (1/3)|ψ_{a,b}⟩⟨ψ_{a,b}|}` — the Hesse symmetric
informationally-complete qutrit measurement. -/
noncomputable def sic3POVM : POVM 3 (Fin 3 × Fin 3) where
  E := sicEffect
  complete := sic3_complete

/-! ### The equiangular SIC property -/

/-- `⟨x, y⟩ = ∑ⱼ star(xⱼ)·yⱼ` on `ℂ³`. -/
private lemma inner_three (x y : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ x y = star (x.ofLp 0) * y.ofLp 0 + star (x.ofLp 1) * y.ofLp 1
      + star (x.ofLp 2) * y.ofLp 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp only [Pi.star_apply]; ring

set_option maxHeartbeats 1600000 in
/-- **The defining SIC symmetry:** all pairwise overlaps are equal,
`|⟨ψⱼ, ψₖ⟩|² = 1/4` for `j ≠ k`. The nine states are equiangular — the dimension-3
analogue of the Bloch tetrahedron (`1/(d+1) = 1/4`). -/
lemma sic3_inner_normSq (a b c d : Fin 3) (h : (a, b) ≠ (c, d)) :
    ‖inner ℂ (sicState a b) (sicState c d)‖ ^ 2 = 1 / 4 := by
  rw [inner_three, sicState_ofLp, sicState_ofLp, sicState_ofLp, sicState_ofLp, sicState_ofLp,
    sicState_ofLp, normSq_coord]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
      | exact absurd rfl h
      | (simp only [sicAmp, cc, om, om2, Complex.star_def, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.neg_re,
          Complex.neg_im] <;> ring_nf <;> nlinarith [r2, r3, r2_4, r3_4])

/-! ### The Born weights as Kähler volumes -/

/-- **Closed-form SIC Born weights:** for a unit preparation `ψ`,
`p_{a,b}(ψ) = (1/3)‖⟨ψ_{a,b}, ψ⟩‖²`. -/
theorem sic3_weight_eq (ψ : EuclideanSpace ℂ (Fin 3)) (hψ : ‖ψ‖ = 1) (i : Fin 3 × Fin 3) :
    sic3POVM.weight ψ i = 1 / 3 * ‖inner ℂ ψ (sicState i.1 i.2)‖ ^ 2 := by
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((sicEffect i).M) ψ)) = _
  rw [sicEffect, scaledRankOneEffect_M]
  exact scaledRankOne_quadratic (1 / 3) (sicState i.1 i.2) ψ (sicState_norm i.1 i.2) hψ

/-- The canonical Naimark dilation of the d=3 SIC POVM. -/
noncomputable def sic3Naimark : NaimarkDilation sic3POVM := canonicalNaimark sic3POVM

/-- **The d=3 SIC-POVM Born weights as Kähler volumes (the capstone).** Instantiating
`povm_born_frequency_volume` at the Hesse SIC: i.i.d. Fubini–Study trials on the dilated
ontic `Σ' = ℂℙ²⁶` have each SIC outcome's empirical frequency converge, on a single
almost-sure event, to the SIC Born weight `p_{a,b}(ψ) = ⟨ψ, E_{a,b} ψ⟩ = (1/3)‖⟨ψ_{a,b},ψ⟩‖²`
— realised as a sum of Fubini–Study volumes of the dilated barycentric cells. The first
*symmetric* non-qubit entry in the volume-frequency series; carving-free, Gleason-free.
The genericity `hpos` is carried as in the general capstone. -/
theorem sic3_born_frequency_volume
    (ψ : EuclideanSpace ℂ (Fin 3)) (e : (Fin 3 × (Fin 3 × Fin 3)) ≃ Fin 27)
    (ψ' : EuclideanSpace ℂ (Fin 27))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin sic3Naimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (hpos : ∀ j : Fin 27, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ'‖ ^ 2)
    (p₀ : CPN 27) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 27) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 27,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 3 × Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 3,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (sic3POVM.weight ψ i)) :=
  povm_born_frequency_volume sic3POVM sic3Naimark ψ e ψ' hψ'eq hψ'0 hnorm hpos
    p₀ X hX hlaw hindep

end SIC3Volume
end CSDBridge
end Empirical
end CSD
