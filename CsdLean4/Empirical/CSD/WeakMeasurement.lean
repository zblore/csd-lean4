import CsdLean4.LF4.POVMNaimark
import CsdLean4.LF4.BornRegionUncond
import CsdLean4.LF4.TrialWitness
import CsdLean4.LF2.EffectAux

/-!
# Empirical/CSD: weak / unsharp measurement as a partial volume nudge (Build 15c)

**Category:** 3-Local (CSD-ontic volume layer; the unsharp-POVM / continuous-strength
entry of the open-system tranche, after einselection (15a) and QEC-decoherence (15b)).

A **weak (unsharp) measurement** of strength `η ∈ [0,1]` is the one-parameter qubit
POVM interpolating the sharp `σ_z` measurement (`η = 1`) and no measurement at all
(`η = 0`):

```
weakEffectPlus  η = (1/2) (I + η σ_z),   weakEffectMinus η = (1/2) (I − η σ_z),
```

with `σ_z = !![1,0;0,-1]`. The two effects are PSD with eigenvalues `(1±η)/2 ∈ [0,1]`
and sum to `I`, so `{weakEffectPlus η, weakEffectMinus η}` is a genuine (non-projective
for `0 < η < 1`) POVM `weakPOVM η`.

## The interpolation (the genuine content)

The plus-outcome Born weight on a unit preparation `ψ` is

```
⟨ψ, weakEffectPlus η ψ⟩ = (1 + η (‖ψ₀‖² − ‖ψ₁‖²)) / 2 = (1 + η ⟨ψ, σ_z ψ⟩) / 2,
```

(`weak_born_weight_plus`, `weak_born_weight_plus_unit`), so the information content
(the deviation of the weight from `1/2`) scales linearly with `η`:

- **`η = 0` (no measurement):** `weakEffectPlus 0 = (1/2) I`, weight `= 1/2` for *every*
  `ψ` — no information and (the maximally unsharp, trivial POVM, connecting to 15a's
  degenerate scalar·I, no basis distinguished);
- **`η = 1` (projective):** `weakEffectPlus 1 = |0⟩⟨0|` the sharp `σ_z`-projector, weight
  `= ‖ψ₀‖² = ‖⟨e₀, ψ⟩‖²` the full Born weight (the sharp carve).

`weak_born_unsharp_interpolation` states both endpoints; `weak_partial_information_witness`
exhibits an intermediate `η = 1/2` weight `3/4` strictly between the trivial `1/2` and the
sharp Born weight `1` (genuine partial information).

## The CSD volume reading (the "nudge")

Run `weakPOVM η` through the POVM tranche: `canonicalNaimark` is its Naimark dilation, and
`povm_born_frequency_volume_uncond` reads the weak-outcome Born weight as a sum of
Fubini–Study **volumes** on the dilated ontic `Σ' = ℂℙ³` — carving-free, Gleason-free,
unconditional (`weak_born_frequency_volume`). The honest reading: the weak measurement is a
**partial volume nudge** — at `η = 0` the dilated volumes are the trivial `1/2` split (no
nudge), at `η = 1` the full projective carve, intermediate `η` a partial nudge of the
Σ-volume.

## Honest scope: static / operational vs continuous dynamics

This is the **static / operational** weak measurement: the unsharp POVM, its Born weights,
and the volume reading. The **continuous** measurement — repeated weak measurements as a
*dynamical* flow, measurement-strength-as-time, weak-value back-action as a Σ-flow — is the
dynamics question, **gated to D1 / the entangled tier (LF6)** and NOT claimed here. The
"nudge vs carve" is the operational / volume reading; the ontic flow that realises the nudge
is D1-gated. Every concrete `SectorData` still carries `Φ = id`.

All exports are foundational-triple-only (off `busch_effect_gleason`): concrete `Matrix`
algebra over the `Effect` / `POVM` types and the unconditional FS-volume engine.
-/

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace WeakMeasurement

open CSD.LF2 CSD.LF4

/-! ### The measurement axis and the computational basis vectors -/

/-- The measurement observable `σ_z = !![1,0;0,-1]` (the unit Pauli-Z axis). -/
noncomputable def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The computational basis vector `e₀ = |0⟩`. -/
noncomputable def e0 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The computational basis vector `e₁ = |1⟩`. -/
noncomputable def e1 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

lemma e0_ofLp_zero : e0.ofLp 0 = 1 := by simp [e0, EuclideanSpace.single]
lemma e0_ofLp_one : e0.ofLp 1 = 0 := by simp [e0, EuclideanSpace.single]
lemma e1_ofLp_zero : e1.ofLp 0 = 0 := by simp [e1, EuclideanSpace.single]
lemma e1_ofLp_one : e1.ofLp 1 = 1 := by simp [e1, EuclideanSpace.single]

lemma e0_norm : ‖e0‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two,
    show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  simp [e0, EuclideanSpace.single]

lemma e1_norm : ‖e1‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two,
    show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  simp [e1, EuclideanSpace.single]

/-! ### The unsharp effects -/

/-- The plus-outcome unsharp effect matrix `(1/2)(I + η σ_z)`. -/
noncomputable def weakPlusM (η : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (η : ℂ) • σz)

/-- The minus-outcome unsharp effect matrix `(1/2)(I − η σ_z)`. -/
noncomputable def weakMinusM (η : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - (η : ℂ) • σz)

/-- `|0⟩⟨0| = !![1,0;0,0]`. -/
lemma outer_e0 : outerProduct e0 = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outerProduct, Matrix.vecMulVec_apply, e0, EuclideanSpace.single]

/-- `|1⟩⟨1| = !![0,0;0,1]`. -/
lemma outer_e1 : outerProduct e1 = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outerProduct, Matrix.vecMulVec_apply, e1, EuclideanSpace.single]

/-- `(1/2)(I + η σ_z) = ((1+η)/2)|0⟩⟨0| + ((1−η)/2)|1⟩⟨1|` — the diagonal form. -/
lemma weakPlusM_decomp (η : ℝ) :
    weakPlusM η = (((1 + η) / 2 : ℝ) : ℂ) • outerProduct e0
      + (((1 - η) / 2 : ℝ) : ℂ) • outerProduct e1 := by
  rw [outer_e0, outer_e1, weakPlusM, σz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] <;> ring

/-- `(1/2)(I − η σ_z) = ((1−η)/2)|0⟩⟨0| + ((1+η)/2)|1⟩⟨1|`. -/
lemma weakMinusM_decomp (η : ℝ) :
    weakMinusM η = (((1 - η) / 2 : ℝ) : ℂ) • outerProduct e0
      + (((1 + η) / 2 : ℝ) : ℂ) • outerProduct e1 := by
  rw [outer_e0, outer_e1, weakMinusM, σz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

/-- `weakPlusM η` is Hermitian. -/
lemma weakPlusM_isHermitian (η : ℝ) : (weakPlusM η).IsHermitian := by
  rw [weakPlusM_decomp]
  exact ((outerProduct_isHermitian e0).smul (k := (((1 + η) / 2 : ℝ) : ℂ))
      (Complex.conj_ofReal _)).add
    ((outerProduct_isHermitian e1).smul (k := (((1 - η) / 2 : ℝ) : ℂ))
      (Complex.conj_ofReal _))

/-- `weakMinusM η` is Hermitian. -/
lemma weakMinusM_isHermitian (η : ℝ) : (weakMinusM η).IsHermitian := by
  rw [weakMinusM_decomp]
  exact ((outerProduct_isHermitian e0).smul (k := (((1 - η) / 2 : ℝ) : ℂ))
      (Complex.conj_ofReal _)).add
    ((outerProduct_isHermitian e1).smul (k := (((1 + η) / 2 : ℝ) : ℂ))
      (Complex.conj_ofReal _))

/-- **Unsharpness constraint (plus):** `weakPlusM η` is PSD for `0 ≤ η ≤ 1` (eigenvalues
`(1±η)/2 ∈ [0,1]`). -/
lemma weakPlusM_psd (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : (weakPlusM η).PosSemidef := by
  rw [weakPlusM_decomp]
  exact (psd_smul (outerProduct_posSemidef e0) (by linarith)).add
    (psd_smul (outerProduct_posSemidef e1) (by linarith))

/-- **Unsharpness constraint (minus):** `weakMinusM η` is PSD for `0 ≤ η ≤ 1`. -/
lemma weakMinusM_psd (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : (weakMinusM η).PosSemidef := by
  rw [weakMinusM_decomp]
  exact (psd_smul (outerProduct_posSemidef e0) (by linarith)).add
    (psd_smul (outerProduct_posSemidef e1) (by linarith))

/-- **POVM completeness at the matrix level:** `(1/2)(I+ησ) + (1/2)(I−ησ) = I`. -/
lemma weakM_sum (η : ℝ) : weakPlusM η + weakMinusM η = 1 := by
  rw [weakPlusM, weakMinusM, ← smul_add,
    show ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (η : ℂ) • σz)
        + ((1 : Matrix (Fin 2) (Fin 2) ℂ) - (η : ℂ) • σz)
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) from by rw [two_smul]; abel,
    smul_smul, show (1 / 2 : ℂ) * 2 = 1 from by norm_num, one_smul]

/-- The plus-outcome unsharp effect `weakEffectPlus η = (1/2)(I + η σ_z)`. -/
noncomputable def weakEffectPlus (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : Effect 2 where
  M := weakPlusM η
  isHermitian := weakPlusM_isHermitian η
  nonneg := weakPlusM_psd η h0 h1
  le_one := by
    have hcompl : (1 : Matrix (Fin 2) (Fin 2) ℂ) - weakPlusM η = weakMinusM η := by
      rw [← weakM_sum η]; abel
    rw [hcompl]; exact weakMinusM_psd η h0 h1

/-- The minus-outcome unsharp effect `weakEffectMinus η = (1/2)(I − η σ_z)`. -/
noncomputable def weakEffectMinus (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : Effect 2 where
  M := weakMinusM η
  isHermitian := weakMinusM_isHermitian η
  nonneg := weakMinusM_psd η h0 h1
  le_one := by
    have hcompl : (1 : Matrix (Fin 2) (Fin 2) ℂ) - weakMinusM η = weakPlusM η := by
      rw [← weakM_sum η]; abel
    rw [hcompl]; exact weakPlusM_psd η h0 h1

/-- **(Part A) The unsharp effects sum to the identity.** -/
theorem weak_effects_sum_one (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    (weakEffectPlus η h0 h1).M + (weakEffectMinus η h0 h1).M = 1 :=
  weakM_sum η

/-- **(Part A) The unsharpness constraint: both effects are PosSemidef.** Together with
`weak_effects_sum_one` and the `Effect.le_one` fields, `{weakEffectPlus η, weakEffectMinus η}`
is a genuine POVM. -/
theorem weak_effect_psd (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    (weakEffectPlus η h0 h1).M.PosSemidef ∧ (weakEffectMinus η h0 h1).M.PosSemidef :=
  ⟨weakPlusM_psd η h0 h1, weakMinusM_psd η h0 h1⟩

/-- **(Part A) The unsharp POVM** `{(1/2)(I+ησ), (1/2)(I−ησ)}` of strength `η`, indexed by
`Fin 2` (`0 = +`, `1 = −`). -/
noncomputable def weakPOVM (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : POVM 2 (Fin 2) where
  E := ![weakEffectPlus η h0 h1, weakEffectMinus η h0 h1]
  complete := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact weakM_sum η

lemma weakPOVM_weight_zero (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) :
    (weakPOVM η h0 h1).weight ψ 0
      = RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakPlusM η) ψ)) := rfl

lemma weakPOVM_weight_one (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) :
    (weakPOVM η h0 h1).weight ψ 1
      = RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakMinusM η) ψ)) := rfl

/-! ### Born weights -/

private lemma re_add (a b : ℂ) : RCLike.re (a + b) = RCLike.re a + RCLike.re b := by
  simp only [← RCLike.reLm_coe, map_add]

private lemma inner_two (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ x y = star (x.ofLp 0) * y.ofLp 0 + star (x.ofLp 1) * y.ofLp 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [Pi.star_apply]; ring

lemma inner_psi_e0 (ψ : EuclideanSpace ℂ (Fin 2)) : inner ℂ ψ e0 = star (ψ.ofLp 0) := by
  rw [inner_two, e0_ofLp_zero, e0_ofLp_one, mul_one, mul_zero, add_zero]

lemma inner_psi_e1 (ψ : EuclideanSpace ℂ (Fin 2)) : inner ℂ ψ e1 = star (ψ.ofLp 1) := by
  rw [inner_two, e1_ofLp_zero, e1_ofLp_one, mul_zero, mul_one, zero_add]

lemma normSq_inner_psi_e0 (ψ : EuclideanSpace ℂ (Fin 2)) :
    ‖inner ℂ ψ e0‖ ^ 2 = ‖ψ.ofLp 0‖ ^ 2 := by rw [inner_psi_e0, norm_star]

lemma normSq_inner_psi_e1 (ψ : EuclideanSpace ℂ (Fin 2)) :
    ‖inner ℂ ψ e1‖ ^ 2 = ‖ψ.ofLp 1‖ ^ 2 := by rw [inner_psi_e1, norm_star]

lemma sum_ofLp_normSq (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    ‖ψ.ofLp 0‖ ^ 2 + ‖ψ.ofLp 1‖ ^ 2 = 1 := by
  have h := euclidean_norm_sq_eq_sum ψ
  rw [Fin.sum_univ_two, hψ, one_pow] at h
  exact h.symm

/-- **(Part B) The weak Born weight (explicit-amplitude form).** For a unit preparation,
`⟨ψ, weakEffectPlus η ψ⟩ = ((1+η)/2)‖ψ₀‖² + ((1−η)/2)‖ψ₁‖²`. -/
theorem weak_born_weight_plus (η : ℝ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakPlusM η) ψ))
      = (1 + η) / 2 * ‖ψ.ofLp 0‖ ^ 2 + (1 - η) / 2 * ‖ψ.ofLp 1‖ ^ 2 := by
  have hsplit : RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakPlusM η) ψ))
      = RCLike.re (inner ℂ ψ
          (Matrix.toEuclideanLin ((((1 + η) / 2 : ℝ) : ℂ) • outerProduct e0) ψ))
        + RCLike.re (inner ℂ ψ
          (Matrix.toEuclideanLin ((((1 - η) / 2 : ℝ) : ℂ) • outerProduct e1) ψ)) := by
    rw [weakPlusM_decomp, map_add, LinearMap.add_apply, inner_add_right, re_add]
  rw [hsplit, scaledRankOne_quadratic _ e0 ψ e0_norm hψ,
    scaledRankOne_quadratic _ e1 ψ e1_norm hψ, normSq_inner_psi_e0, normSq_inner_psi_e1]

/-- The minus analogue: `⟨ψ, weakEffectMinus η ψ⟩ = ((1−η)/2)‖ψ₀‖² + ((1+η)/2)‖ψ₁‖²`. -/
theorem weak_born_weight_minus (η : ℝ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakMinusM η) ψ))
      = (1 - η) / 2 * ‖ψ.ofLp 0‖ ^ 2 + (1 + η) / 2 * ‖ψ.ofLp 1‖ ^ 2 := by
  have hsplit : RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakMinusM η) ψ))
      = RCLike.re (inner ℂ ψ
          (Matrix.toEuclideanLin ((((1 - η) / 2 : ℝ) : ℂ) • outerProduct e0) ψ))
        + RCLike.re (inner ℂ ψ
          (Matrix.toEuclideanLin ((((1 + η) / 2 : ℝ) : ℂ) • outerProduct e1) ψ)) := by
    rw [weakMinusM_decomp, map_add, LinearMap.add_apply, inner_add_right, re_add]
  rw [hsplit, scaledRankOne_quadratic _ e0 ψ e0_norm hψ,
    scaledRankOne_quadratic _ e1 ψ e1_norm hψ, normSq_inner_psi_e0, normSq_inner_psi_e1]

/-- **(Part B) The weak Born weight in `σ_z`-expectation form.** For a unit preparation,
`⟨ψ, weakEffectPlus η ψ⟩ = (1 + η (‖ψ₀‖² − ‖ψ₁‖²)) / 2 = (1 + η ⟨ψ, σ_z ψ⟩)/2`. The
deviation from `1/2` scales linearly with the strength `η`. -/
theorem weak_born_weight_plus_unit (η : ℝ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakPlusM η) ψ))
      = (1 + η * (‖ψ.ofLp 0‖ ^ 2 - ‖ψ.ofLp 1‖ ^ 2)) / 2 := by
  rw [weak_born_weight_plus η ψ hψ]
  have h : ‖ψ.ofLp 1‖ ^ 2 = 1 - ‖ψ.ofLp 0‖ ^ 2 := by
    have := sum_ofLp_normSq ψ hψ; linarith
  rw [h]; ring

/-! ### The no-measurement ↔ projective interpolation -/

/-- **(Part B headline) The unsharp interpolation: no-measurement (`η=0`) ↔ projective
(`η=1`).** For every unit preparation `ψ`:

1. `weakEffectPlus 0 = (1/2) I` — the maximally unsharp / trivial POVM (no basis
   distinguished, cf. 15a's degenerate scalar·I);
2. its weight is `1/2` regardless of `ψ` — no information;
3. `weakEffectPlus 1 = |0⟩⟨0|` — the sharp `σ_z`-projector;
4. its weight is `‖ψ₀‖² = ‖⟨e₀,ψ⟩‖²` — the full Born weight (the sharp carve).

So `η` is the measurement strength / sharpness, interpolating no-measurement ↔ projective. -/
theorem weak_born_unsharp_interpolation (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    weakPlusM 0 = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakPlusM 0) ψ)) = 1 / 2
    ∧ weakPlusM 1 = outerProduct e0
    ∧ RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (weakPlusM 1) ψ)) = ‖ψ.ofLp 0‖ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [weakPlusM, Complex.ofReal_zero, zero_smul, add_zero]
  · rw [weak_born_weight_plus 0 ψ hψ]
    have h := sum_ofLp_normSq ψ hψ; norm_num; linarith
  · rw [weakPlusM_decomp,
      show ((1 + 1) / 2 : ℝ) = 1 from by norm_num,
      show ((1 - 1) / 2 : ℝ) = 0 from by norm_num,
      Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero]
  · rw [weak_born_weight_plus 1 ψ hψ]; ring

/-- **(Part B) Genuine partial information (non-vacuity).** At intermediate strength
`η = 1/2` on the basis preparation `e₀` (sharp Born weight `1`, no-measurement weight `1/2`),
the weak plus-weight is `3/4` — strictly between the trivial `1/2` and the sharp Born weight
`‖e₀.ofLp 0‖² = 1`. Neither trivial nor sharp: genuine partial information. -/
theorem weak_partial_information_witness :
    (1 : ℝ) / 2 < RCLike.re (inner ℂ e0 (Matrix.toEuclideanLin (weakPlusM (1 / 2)) e0))
    ∧ RCLike.re (inner ℂ e0 (Matrix.toEuclideanLin (weakPlusM (1 / 2)) e0))
        < ‖e0.ofLp 0‖ ^ 2 := by
  rw [weak_born_weight_plus (1 / 2) e0 e0_norm, e0_ofLp_zero, e0_ofLp_one]
  norm_num

/-! ### The CSD volume reading (the "nudge") -/

/-- The canonical Naimark dilation of the unsharp POVM (it exists, like every POVM's). The
ancilla is the apparatus; the dilated ontic space is `Σ' = ℂℙ³`. -/
noncomputable def weakNaimark (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    NaimarkDilation (weakPOVM η h0 h1) := canonicalNaimark (weakPOVM η h0 h1)

/-- **(Part C) The weak-measurement Born weights as Kähler volumes (the volume companion).**
Instantiating the unconditional POVM volume engine `povm_born_frequency_volume_uncond` at the
unsharp `weakPOVM η`: i.i.d. Fubini–Study trials on the dilated ontic `Σ' = ℂℙ³` have the
`i`-th weak-outcome empirical frequency converge, on a single almost-sure event, to the weak
Born weight `(weakPOVM η).weight ψ i` — realised as a sum of Fubini–Study volumes of the
dilated barycentric cells.

This is the **partial volume nudge** reading: at `η = 0` the dilated volumes are the trivial
`1/2` split (no nudge); at `η = 1` the full projective carve; intermediate `η` a partial
nudge of the Σ-volume. Carving-free, Gleason-free, unconditional (no genericity on the
dilated state). The ontic *flow* that realises the nudge dynamically is D1-gated (LF6), not
claimed here. -/
theorem weak_born_frequency_volume (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 2) ≃ Fin 4)
    (ψ' : EuclideanSpace ℂ (Fin 4))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin (weakNaimark η h0 h1).V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN 4) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 4,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 2,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds ((weakPOVM η h0 h1).weight ψ i)) :=
  povm_born_frequency_volume_uncond (weakPOVM η h0 h1) (weakNaimark η h0 h1) ψ e ψ' hψ'eq
    hψ'0 hnorm p₀ X hX hlaw hindep

/-- `weak_born_frequency_volume` on the canonical i.i.d. FS process (the trial bundle is
discharged, so the hypothesis set is Lean-inhabited). -/
theorem weak_born_frequency_volume_canonical (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 2) ≃ Fin 4)
    (ψ' : EuclideanSpace ℂ (Fin 4))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin (weakNaimark η h0 h1).V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1) (p₀ : CPN 4) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 2,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((fsTrial 4 l) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds ((weakPOVM η h0 h1).weight ψ i)) :=
  weak_born_frequency_volume η h0 h1 ψ e ψ' hψ'eq hψ'0 hnorm p₀
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end WeakMeasurement
end CSDBridge
end Empirical
end CSD
