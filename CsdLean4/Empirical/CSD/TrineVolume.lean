import CsdLean4.LF4.POVMNaimark
import CsdLean4.LF4.BornRegionUncond
import CsdLean4.LF2.EffectAux

/-!
# Empirical/CSD: the qubit trine POVM and its Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic layer; the first *non-projective* (POVM) entry in
the volume-frequency series — SG, Malus, Bell, GHZ, Hardy were all projective).

The **trine** is the canonical minimal symmetric qubit POVM: three states
`|ψₖ⟩` whose Bloch vectors sit at 120° in a great circle, with effects
`Eₖ = (2/3)|ψₖ⟩⟨ψₖ|`. It is a genuine POVM — `∑ₖ Eₖ = I` holds *only* because the
three projectors sum to `(3/2)I` — and cannot be realised projectively (three
outcomes on a 2-dimensional space).

This file:
- builds `trinePOVM : POVM 2 (Fin 3)` (a `scaledRankOneEffect` helper + completeness);
- gives the closed-form Born weights `pₖ(ψ) = (2/3)‖⟨ψₖ, ψ⟩‖²`;
- runs it through the POVM tranche: `canonicalNaimark trinePOVM` is the dilation,
  and `trine_born_frequency_volume` lands the trine outcome frequencies as
  **Fubini–Study volumes** on the dilated `Σ' = ℂℙ⁵` — carving-free, Gleason-free.

The trine has no structural zeros (for generic `ψ` all three weights are nonzero).
The capstone is unconditional: it routes through the hpos-free engine
(`povm_born_frequency_volume_uncond`, `LF4/BornRegionUncond.lean`), so no
genericity hypothesis on the dilated state is carried (2026-06-11 migration);
vanishing dilated amplitudes give FS-null cells.
-/

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace TrineVolume

open CSD.LF2 CSD.LF4

/-! ### The trine states and POVM -/

/-- The (real) amplitudes of the three trine states on the computational basis:
Bloch vectors at 120° in the x–z great circle.
`ψ₀ = |0⟩`, `ψ₁ = (1/2)|0⟩ + (√3/2)|1⟩`, `ψ₂ = (1/2)|0⟩ − (√3/2)|1⟩`. -/
noncomputable def trineAmp : Fin 3 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 0
  | 1, 0 => 1 / 2 | 1, 1 => Real.sqrt 3 / 2
  | 2, 0 => 1 / 2 | 2, 1 => -(Real.sqrt 3 / 2)

/-- The three trine states as unit vectors in `ℂ²`. -/
noncomputable def trineState (k : Fin 3) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 ((trineAmp k 0 : ℝ) : ℂ)
    + EuclideanSpace.single 1 ((trineAmp k 1 : ℝ) : ℂ)

lemma trineState_ofLp (k : Fin 3) (i : Fin 2) :
    (trineState k).ofLp i = ((trineAmp k i : ℝ) : ℂ) := by
  fin_cases i <;> simp [trineState, EuclideanSpace.single]

lemma trineAmp_sq_sum (k : Fin 3) : trineAmp k 0 ^ 2 + trineAmp k 1 ^ 2 = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases k <;> simp only [trineAmp] <;> nlinarith [h3]

lemma trineState_norm (k : Fin 3) : ‖trineState k‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, trineState_ofLp, trineState_ofLp,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    trineAmp_sq_sum, Real.sqrt_one]

lemma trineState_apply (k : Fin 3) (i : Fin 2) : trineState k i = ((trineAmp k i : ℝ) : ℂ) := by
  fin_cases i <;> simp [trineState, EuclideanSpace.single]

/-- `∑ₖ |ψₖ⟩⟨ψₖ| = (3/2) I` — the Gram relation that makes the trine a valid POVM. -/
lemma trine_outer_sum :
    ∑ k : Fin 3, outerProduct (trineState k)
      = ((3 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h3c : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  ext i j
  rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hentry : ∀ k : Fin 3, outerProduct (trineState k) i j
      = ((trineAmp k i : ℝ) : ℂ) * ((trineAmp k j : ℝ) : ℂ) := by
    intro k
    rw [outerProduct, Matrix.vecMulVec_apply, trineState_apply, trineState_apply,
      Complex.star_def, Complex.conj_ofReal]
  simp_rw [hentry]
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [trineAmp]
  · rw [Matrix.one_apply_eq]; push_cast; ring
  · rw [Matrix.one_apply_ne (by decide)]; push_cast; ring
  · rw [Matrix.one_apply_ne (by decide)]; push_cast; ring
  · rw [Matrix.one_apply_eq]; push_cast; linear_combination (1 / 2 : ℂ) * h3c

/-! ### The trine POVM -/

/-- The `k`-th trine effect `Eₖ = (2/3)|ψₖ⟩⟨ψₖ|`. -/
noncomputable def trineEffect (k : Fin 3) : Effect 2 :=
  scaledRankOneEffect (2 / 3) (by norm_num) (by norm_num) (trineState k) (trineState_norm k)

/-- **Completeness:** `∑ₖ Eₖ = (2/3)(3/2) I = I`. The trine is a genuine POVM. -/
lemma trine_complete : ∑ k : Fin 3, (trineEffect k).M = 1 := by
  have : ∑ k : Fin 3, (trineEffect k).M = ((2 / 3 : ℝ) : ℂ) • ∑ k : Fin 3, outerProduct (trineState k) := by
    rw [Finset.smul_sum]; rfl
  rw [this, trine_outer_sum, smul_smul, ← Complex.ofReal_mul]
  norm_num

/-- **The qubit trine POVM** `{Eₖ = (2/3)|ψₖ⟩⟨ψₖ|}ₖ` — the canonical minimal
symmetric (non-projective) qubit measurement. -/
noncomputable def trinePOVM : POVM 2 (Fin 3) where
  E := trineEffect
  complete := trine_complete

/-! ### The trine Born weights as Kähler volumes -/

/-- **Closed-form trine Born weights:** for a unit preparation `ψ`,
`pₖ(ψ) = (2/3)‖⟨ψ, ψₖ⟩‖²` — the symmetric 120°-measurement outcome probabilities. -/
theorem trine_weight_eq (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) (k : Fin 3) :
    trinePOVM.weight ψ k = 2 / 3 * ‖inner ℂ ψ (trineState k)‖ ^ 2 := by
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((trineEffect k).M) ψ)) = _
  rw [trineEffect, scaledRankOneEffect_M]
  exact scaledRankOne_quadratic (2 / 3) (trineState k) ψ (trineState_norm k) hψ

/-- The canonical Naimark dilation of the trine POVM (it exists, like every POVM's). -/
noncomputable def trineNaimark : NaimarkDilation trinePOVM := canonicalNaimark trinePOVM

/-- **The trine POVM Born weights as Kähler volumes (the capstone).** Instantiating
`povm_born_frequency_volume_uncond` at the trine: i.i.d. Fubini–Study trials on the
dilated ontic `Σ' = ℂℙ⁵` have the `k`-th trine outcome's empirical frequency converge,
on a single almost-sure event, to the trine Born weight `pₖ(ψ) = ⟨ψ, Eₖ ψ⟩` (the
symmetric 120°-measurement outcome probability `(2/3)‖⟨ψₖ,ψ⟩‖²`) — realised as a sum of
Fubini–Study volumes of the dilated barycentric cells. The **first
non-projective (POVM) entry in the volume-frequency series**; carving-free,
Gleason-free, and (since the 2026-06-11 hpos migration) with no genericity
hypothesis on the dilated state. -/
theorem trine_born_frequency_volume
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 3) ≃ Fin 6)
    (ψ' : EuclideanSpace ℂ (Fin 6))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin trineNaimark.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN 6) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 6) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 6,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ k : Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (trinePOVM.weight ψ k)) :=
  povm_born_frequency_volume_uncond trinePOVM trineNaimark ψ e ψ' hψ'eq hψ'0 hnorm
    p₀ X hX hlaw hindep

end TrineVolume
end CSDBridge
end Empirical
end CSD
