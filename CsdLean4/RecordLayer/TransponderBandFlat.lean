/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderBandGate
public import CsdLean4.RecordLayer.TransponderMeetingPacket

/-!
# The band against one energy for the second level: the spread of energies times the time

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2) for the transponder of
UA-21; fourth brick on it).

With the swap acting everywhere, each mode of the band turns at its own rate
(`RecordLayer/TransponderBandRabi.lean`), so the orbit of a packet is a packet whose
amplitudes are modulated mode by mode, and the flat-packet bounds do not say where it is.
Here it is compared with the transponder that has **one** energy `E 1` for its second level
and no hopping, whose orbit is `χ` in the two levels with two coefficients
(`exp_levels_swap_mulVec_inLevel_zero`) and so stays where `χ` is. The two generators differ
by `H₁ − E 1` on the second level. Along the reference orbit the second level holds at most
`|g|/Ω` of `χ`, so the two orbits differ by at most `(|g|/Ω) ‖(H₁ − E 1) χ‖ s`.

`‖(H₁ − E 1) χ‖` is the spread of the packet's energies about `E 1`. The bound is small for
a time short against the inverse of that spread: while the launched part has moved less
than the packet's own width.

* `bandDefect`, `bandBlocks_eq_add_bandDefect`, `bandDefect_isHermitian`,
  `blockDiagonal_bandDefect_mulVec_inLevel_zero`,
  `blockDiagonal_bandDefect_mulVec_inLevel_one`;
* `norm_neg_exp_mul_I_sin_mul` — the size of the reference orbit's second-level coefficient;
* `sqrt_sum_norm_sq_bandDefect_levels_orbit_le` — the defect on the reference orbit;
* ★★★ `sqrt_sum_norm_sq_exp_band_sub_levels_le` — **the banded transponder's orbit of `χ` in
  the first level is the two-level transponder's orbit within
  `(|g|/Ω) ‖(H₁ − E 1) χ‖ s`**;
* ★ `sum_norm_sq_exp_compositeH_sub_prod` — for a product with a messenger, the difference of
  two orbits that differ in the second carrier's Hamiltonian is the messenger's norm times
  the second carrier's difference.

## Honest scope

⚠️ **Transponder only, swap ungated.** No messenger enters the main statement and no gate.
With `RecordLayer/TransponderBandGate.lean` this is what is needed to evaluate the gate's
error; the evaluation is not made here.

⚠️ **A short-time bound.** It grows linearly in `s` and says nothing once
`‖(H₁ − E 1) χ‖ s` is of order one. In that time the launched part has not left the packet,
so this does not show the return leaving: it shows where the transponder is **during** the
contact. The free motion after the contact is `transponder_band_swapped_moves`.

⚠️ **`‖(H₁ − E 1) χ‖` is not evaluated** for the lattice Dirac band and a flat packet. `χ` has
norm `1` by hypothesis.

⚠️ **Flow times.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UA-21,
UO-26, UD-262, UD-266, UD-267, UD-268; §9.4); `RecordLayer/TransponderBandRabi.lean`
(`exp_levels_swap_mulVec_inLevel_zero`); `RecordLayer/TransponderBandGate.lean`
(`norm_exp_gated_sub_ungated_mul_le`); `Mathlib/Analysis/Matrix/DuhamelState.lean`
(`Matrix.norm_exp_neg_I_add_sub_mul_le`); `RecordLayer/TransponderLaunchState.lean`
(`norm_mul_vecMulVec`); `RecordLayer/CoincidenceOrbit.lean` (`exp_compositeH_mulVec_prod`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

section Defect

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **What the band adds to one energy `c` for the second level**: nothing on the first level,
`H₁ − c` on the second. -/
def bandDefect (c : ℝ) (H₁ : Matrix n n ℂ) : Fin 2 → Matrix n n ℂ :=
  ![0, H₁ - ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)]

omit [Fintype n] in
/-- The transponder of UA-21 is level energies with no hopping, plus the defect. -/
theorem bandBlocks_eq_add_bandDefect (E : Fin 2 → ℝ) (H₁ : Matrix n n ℂ) :
    Matrix.blockDiagonal (bandBlocks (E 0) H₁)
      = Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + Matrix.blockDiagonal (bandDefect (E 1) H₁) := by
  rw [← Matrix.blockDiagonal_add]
  congr 1
  funext l
  fin_cases l
  · show ((E 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ) = ((E 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ) + 0
    rw [add_zero]
  · show H₁ = ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ) + (H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
    abel

omit [Fintype n] in
/-- The defect is Hermitian when the second level's Hamiltonian is. -/
theorem bandDefect_isHermitian (c : ℝ) {H₁ : Matrix n n ℂ} (hH₁ : H₁.IsHermitian) :
    ∀ l, (bandDefect c H₁ l).IsHermitian := by
  intro l
  fin_cases l
  · exact Matrix.isHermitian_zero
  · exact hH₁.sub (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal])))

/-- The defect annihilates the first level. -/
theorem blockDiagonal_bandDefect_mulVec_inLevel_zero (c : ℝ) (H₁ : Matrix n n ℂ)
    (χ : n → ℂ) :
    Matrix.blockDiagonal (bandDefect c H₁) *ᵥ inLevel 0 χ = 0 := by
  rw [blockDiagonal_mulVec_inLevel]
  show inLevel 0 ((0 : Matrix n n ℂ) *ᵥ χ) = 0
  rw [Matrix.zero_mulVec]
  funext q
  simp [inLevel]

/-- The defect acts on the second level by `H₁ − c`. -/
theorem blockDiagonal_bandDefect_mulVec_inLevel_one (c : ℝ) (H₁ : Matrix n n ℂ)
    (χ : n → ℂ) :
    Matrix.blockDiagonal (bandDefect c H₁) *ᵥ inLevel 1 χ
      = inLevel 1 ((H₁ - ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) := by
  rw [blockDiagonal_mulVec_inLevel]
  rfl

/-- The size of the second-level coefficient of a turning orbit. -/
theorem norm_neg_exp_mul_I_sin_mul (c Ω g s : ℝ) :
    ‖-(Complex.exp (-(Complex.I * ((c : ℝ) : ℂ)) * s)
        * (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ) * ((g / Ω : ℝ) : ℂ)))‖
      = |Real.sin (Ω * s)| * |g / Ω| := by
  have hre : (-(Complex.I * ((c : ℝ) : ℂ)) * (s : ℂ)).re = 0 := by simp
  rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_exp, hre, Real.exp_zero,
    Complex.norm_I, ← Complex.ofReal_sin, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, one_mul, one_mul]

/-- **The defect on the reference orbit.** Along the orbit of `χ` in the first level under
level energies `E`, no hopping and the swap, the defect has size at most
`(|g|/Ω) ‖(H₁ − E 1) χ‖`. -/
theorem sqrt_sum_norm_sq_bandDefect_levels_orbit_le (E : Fin 2 → ℝ) (H₁ : Matrix n n ℂ)
    (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω) (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2) (χ : n → ℂ)
    (u : ℝ) :
    Real.sqrt (∑ q, ‖((Matrix.blockDiagonal (bandDefect (E 1) H₁)
        * exp (u • ((-Complex.I) • (Matrix.blockDiagonal
            (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
          + (g : ℂ) • levelSwap n)))) *ᵥ inLevel 0 χ) q‖ ^ 2)
      ≤ |g| / Ω * Real.sqrt (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2)
        := by
  rw [← Matrix.mulVec_mulVec, exp_levels_swap_mulVec_inLevel_zero E g hΩ hΩ2 χ u,
    Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    blockDiagonal_bandDefect_mulVec_inLevel_zero, blockDiagonal_bandDefect_mulVec_inLevel_one,
    smul_zero, zero_sub, smul_neg, smul_smul, ← neg_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, sum_norm_sq_inLevel, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), norm_neg_exp_mul_I_sin_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [abs_div, abs_of_pos hΩ]
  exact mul_le_of_le_one_left (div_nonneg (abs_nonneg g) hΩ.le) (Real.abs_sin_le_one _)

variable [Nonempty n]

/-- ★★★ **The band against one energy for the second level.** The transponder of UA-21 with
the first-level energy `E 0` and a Hermitian second-level Hamiltonian `H₁`, and the swap term
`g X` with no gate. `Ω > 0` with `Ω² = g² + ((E 1 − E 0)/2)²`. For `χ` of norm `1` and
`s ≥ 0`, the orbit of `χ` in the first level differs from its orbit under the level energies
`E` with no hopping by at most `(|g|/Ω) ‖(H₁ − E 1) χ‖ s`. -/
theorem sqrt_sum_norm_sq_exp_band_sub_levels_le (E : Fin 2 → ℝ) {H₁ : Matrix n n ℂ}
    (hH₁ : H₁.IsHermitian) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2) {χ : n → ℂ} (hχ : ∑ p, ‖χ p‖ ^ 2 = 1)
    {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (∑ q, ‖(exp (s • ((-Complex.I) • (Matrix.blockDiagonal (bandBlocks (E 0) H₁)
            + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 χ
          - exp (s • ((-Complex.I) • (Matrix.blockDiagonal
              (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 χ) q‖ ^ 2)
      ≤ |g| / Ω * Real.sqrt (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2)
        * s := by
  have hgS : ((g : ℂ) • levelSwap n).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (levelSwap_isHermitian n).eq,
      Complex.star_def, Complex.conj_ofReal]
  have hEh : ∀ l : Fin 2, (((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun l =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hB := (blockDiagonal_isHermitian hEh).add hgS
  have hDh := blockDiagonal_isHermitian (bandDefect_isHermitian (E 1) hH₁)
  have hsum : Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n
      = Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
          + (g : ℂ) • levelSwap n + Matrix.blockDiagonal (bandDefect (E 1) H₁) := by
    rw [bandBlocks_eq_add_bandDefect E H₁]
    abel
  have hv1 : ∑ q, ‖inLevel 0 χ q‖ ^ 2 = 1 := by rw [sum_norm_sq_inLevel, hχ]
  have hstar := (norm_vecMulVec_star_of_sum_eq_one hv1).1
  have h := Matrix.norm_exp_neg_I_add_sub_mul_le _ _
    (Matrix.vecMulVec (inLevel 0 χ) (star (inLevel 0 χ))) hB hDh hs
  rw [← hsum, norm_mul_vecMulVec, hstar, mul_one, Matrix.sub_mulVec] at h
  refine h.trans ?_
  calc ∫ u in (0 : ℝ)..s, ‖Matrix.blockDiagonal (bandDefect (E 1) H₁)
          * exp (u • ((-Complex.I) • (Matrix.blockDiagonal
              (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • levelSwap n)))
          * Matrix.vecMulVec (inLevel 0 χ) (star (inLevel 0 χ))‖
      ≤ ∫ _u in (0 : ℝ)..s, |g| / Ω * Real.sqrt
          (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on hs
          ((Matrix.continuous_norm_mul_exp_smul_mul _ _ _).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) fun u _ => ?_
        rw [norm_mul_vecMulVec, hstar, mul_one]
        exact sqrt_sum_norm_sq_bandDefect_levels_orbit_le E H₁ g hΩ hΩ2 χ u
    _ = |g| / Ω * Real.sqrt
          (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) * s := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

end Defect

/-! ### A product with a messenger -/

section Product

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- ★ **Two composite orbits that differ in the second carrier's Hamiltonian.** For a product
`ψ ⊗ φ`, the squared norm of the difference is the squared norm of the first carrier's orbit
times that of the difference of the second carrier's two orbits. -/
theorem sum_norm_sq_exp_compositeH_sub_prod (A₀ : Matrix ι ι ℂ) (C C' : Matrix κ κ ℂ)
    (s : ℝ) (ψ : ι → ℂ) (φ : κ → ℂ) :
    ∑ x : ι × κ, ‖(exp (s • ((-Complex.I) • compositeH A₀ C))
            *ᵥ (fun y : ι × κ => ψ y.1 * φ y.2)
          - exp (s • ((-Complex.I) • compositeH A₀ C'))
            *ᵥ (fun y : ι × κ => ψ y.1 * φ y.2)) x‖ ^ 2
      = (∑ p, ‖(exp (s • ((-Complex.I) • A₀)) *ᵥ ψ) p‖ ^ 2)
        * ∑ q, ‖(exp (s • ((-Complex.I) • C)) *ᵥ φ
            - exp (s • ((-Complex.I) • C')) *ᵥ φ) q‖ ^ 2 := by
  rw [exp_compositeH_mulVec_prod, exp_compositeH_mulVec_prod, ← sum_norm_sq_prod]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.sub_apply, mul_sub]

end Product

end CSD.RecordLayer

end
