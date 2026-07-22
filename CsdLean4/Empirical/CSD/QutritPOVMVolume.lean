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
# Empirical/CSD: the unsharp qutrit POVM and its Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic layer; the **first non-qubit (`N = 3`) entry** in the
volume-frequency series, and the first genuinely non-projective qutrit POVM).

The **unsharp (white-noise) measurement** is the textbook model of a noisy detector and
the canonical reason POVMs are needed beyond the projective formalism: a sharp basis
measurement `{|k⟩⟨k|}` degraded by depolarising noise of strength `ε`,

```
Eₖ = (1 − ε)|k⟩⟨k| + (ε/3) I₃        (k ∈ Fin 3,  0 ≤ ε ≤ 1).
```

For `ε ∈ (0, 1)` each `Eₖ` is a genuine (rank-3, non-projector) effect, so this is a real
POVM requiring a Naimark dilation rather than a projective measurement. Completeness is
immediate: `∑ₖ Eₖ = (1 − ε) ∑ₖ|k⟩⟨k| + ε I₃ = (1 − ε) I₃ + ε I₃ = I₃`.

This file:
- builds `noisyPOVM ε : POVM 3 (Fin 3)` (a direct `Effect` construction + completeness);
- gives the closed-form Born weights `pₖ(ψ) = (1 − ε)‖⟨k, ψ⟩‖² + ε/3`;
- runs it through the POVM tranche: `canonicalNaimark (noisyPOVM ε)` is the dilation, and
  `noisy_born_frequency_volume` lands the three outcome frequencies as **Fubini–Study
  volumes** on the dilated ontic `Σ' = ℂℙ⁸` — carving-free, Gleason-free.

This is the first entry exercising the general-`N` Naimark→volume machinery past the
qubit: the dilation lives on `ℂℙ^{N·|ι|−1} = ℂℙ⁸` for `N = 3`, `|ι| = 3`. The capstone
routes through the hpos-free engine (`povm_born_frequency_volume_uncond`,
`LF4/BornRegionUncond.lean`), so no genericity hypothesis on the dilated state is
carried (2026-06-11 migration).

## Source

Unsharp / POVM measurements: Busch, Lahti, Mittelstaedt, *The Quantum Theory of
Measurement* (1996); depolarising noise is the standard detector-noise model.
-/

@[expose] public section

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QutritPOVMVolume

open CSD.LF2 CSD.LF4

/-! ### The computational basis of `ℂ³` -/

/-- The `k`-th computational basis vector `|k⟩` of `ℂ³`. -/
noncomputable def basisVec (k : Fin 3) : EuclideanSpace ℂ (Fin 3) :=
  EuclideanSpace.single k (1 : ℂ)

@[simp] lemma basisVec_norm (k : Fin 3) : ‖basisVec k‖ = 1 := by
  rw [basisVec, PiLp.norm_single]; simp

/-- `∑ₖ |k⟩⟨k| = I₃` — completeness of the computational basis. -/
lemma basis_outer_sum :
    ∑ k : Fin 3, outerProduct (basisVec k) = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rw [Matrix.sum_apply, Matrix.one_apply]
  have hk : ∀ k : Fin 3, outerProduct (basisVec k) i j
      = (if i = k then (1 : ℂ) else 0) * star (if j = k then (1 : ℂ) else 0) := by
    intro k
    rw [outerProduct, Matrix.vecMulVec_apply]
    simp only [basisVec, PiLp.single_apply]
  simp_rw [hk]
  fin_cases i <;> fin_cases j <;> simp

/-! ### The unsharp effects and POVM -/

/-- The unsharp effect `Eₖ = (1 − ε)|k⟩⟨k| + (ε/3) I₃`. A genuine (rank-3) effect for
`ε ∈ (0, 1)`; `ε = 0` is the sharp projector, `ε = 1` the trivial `I₃/3`. -/
noncomputable def noisyEffect (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (k : Fin 3) : Effect 3 where
  M := ((1 - ε : ℝ) : ℂ) • outerProduct (basisVec k)
        + ((ε / 3 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
  isHermitian :=
    ((outerProduct_isHermitian (basisVec k)).smul (k := ((1 - ε : ℝ) : ℂ))
        (Complex.conj_ofReal _)).add
      (Matrix.isHermitian_one.smul (k := ((ε / 3 : ℝ) : ℂ)) (Complex.conj_ofReal _))
  nonneg :=
    (psd_smul (outerProduct_posSemidef (basisVec k)) (by linarith)).add
      (psd_smul Matrix.PosSemidef.one (by linarith))
  le_one := by
    have hdecomp :
        (1 : Matrix (Fin 3) (Fin 3) ℂ)
            - (((1 - ε : ℝ) : ℂ) • outerProduct (basisVec k)
                + ((ε / 3 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
          = ((1 - ε / 3 : ℝ) : ℂ) • (1 - outerProduct (basisVec k))
            + ((2 * ε / 3 : ℝ) : ℂ) • outerProduct (basisVec k) := by
      push_cast
      module
    rw [hdecomp]
    exact (psd_smul (one_sub_outerProduct_posSemidef (basisVec k) (basisVec_norm k))
        (by linarith)).add
      (psd_smul (outerProduct_posSemidef (basisVec k)) (by linarith))

@[simp] lemma noisyEffect_M (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (k : Fin 3) :
    (noisyEffect ε hε0 hε1 k).M
      = ((1 - ε : ℝ) : ℂ) • outerProduct (basisVec k)
        + ((ε / 3 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := rfl

/-- **Completeness:** `∑ₖ Eₖ = (1 − ε) I₃ + ε I₃ = I₃`. -/
lemma noisy_complete (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∑ k : Fin 3, (noisyEffect ε hε0 hε1 k).M = 1 := by
  simp_rw [noisyEffect_M]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, basis_outer_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  push_cast
  module

/-- **The unsharp qutrit POVM** `{Eₖ = (1−ε)|k⟩⟨k| + (ε/3)I₃}ₖ` — a genuine
non-projective qutrit measurement. -/
noncomputable def noisyPOVM (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : POVM 3 (Fin 3) where
  E := noisyEffect ε hε0 hε1
  complete := noisy_complete ε hε0 hε1

/-! ### The Born weights as Kähler volumes -/

/-- **Closed-form unsharp Born weights:** for a unit preparation `ψ`,
`pₖ(ψ) = (1 − ε)‖⟨k, ψ⟩‖² + ε/3`. The signal term `(1−ε)‖⟨k,ψ⟩‖²` plus the uniform
noise floor `ε/3`. -/
theorem noisy_weight_eq (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 3)) (hψ : ‖ψ‖ = 1) (k : Fin 3) :
    (noisyPOVM ε hε0 hε1).weight ψ k
      = (1 - ε) * ‖inner ℂ ψ (basisVec k)‖ ^ 2 + ε / 3 := by
  have hI : Matrix.toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℂ) ψ = ψ := by
    rw [Matrix.toLpLin_apply]; simp
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((noisyEffect ε hε0 hε1 k).M) ψ)) = _
  rw [noisyEffect_M, map_add, LinearMap.add_apply, inner_add_right, map_add,
    scaledRankOne_quadratic (1 - ε) (basisVec k) ψ (basisVec_norm k) hψ]
  congr 1
  rw [map_smul, LinearMap.smul_apply, hI, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
  simp

/-- The canonical Naimark dilation of the unsharp qutrit POVM. -/
noncomputable def noisyNaimark (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    NaimarkDilation (noisyPOVM ε hε0 hε1) := canonicalNaimark (noisyPOVM ε hε0 hε1)

/-- **The unsharp qutrit POVM Born weights as Kähler volumes (the capstone).**
Instantiating `povm_born_frequency_volume_uncond` at the unsharp qutrit measurement:
i.i.d. Fubini–Study trials on the dilated ontic `Σ' = ℂℙ⁸` have the `k`-th outcome's
empirical frequency converge, on a single almost-sure event, to the Born weight
`pₖ(ψ) = ⟨ψ, Eₖ ψ⟩ = (1 − ε)‖⟨k,ψ⟩‖² + ε/3` — realised as a sum of Fubini–Study volumes
of the dilated barycentric cells. The **first non-qubit (`N = 3`) entry in the
volume-frequency series**, and the first non-projective qutrit POVM; carving-free,
Gleason-free, and (since the 2026-06-11 hpos migration) with no genericity hypothesis
on the dilated state — the sharp limit `ε = 0` at a basis state is covered. -/
theorem noisy_born_frequency_volume (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 3)) (e : (Fin 3 × Fin 3) ≃ Fin 9)
    (ψ' : EuclideanSpace ℂ (Fin 9))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin (noisyNaimark ε hε0 hε1).V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN 9) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 9) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 9,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ k : Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 3,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds ((noisyPOVM ε hε0 hε1).weight ψ k)) :=
  povm_born_frequency_volume_uncond (noisyPOVM ε hε0 hε1) (noisyNaimark ε hε0 hε1) ψ e ψ'
    hψ'eq hψ'0 hnorm p₀ X hX hlaw hindep

end QutritPOVMVolume
end CSDBridge
end Empirical
end CSD
