/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderBandRabi
public import CsdLean4.RecordLayer.TransponderReading

/-!
# The gated contact term against the ungated one, for any transponder

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2) for the transponder of
UA-21; third brick on it).

`RecordLayer/TransponderBandRabi.lean` solves the transponder of UA-21 with the swap term
acting everywhere. The term of UA-19 (b) acts only where the two carriers are in contact.
Here the two are compared, for any Hermitian transponder Hamiltonian `C` and any Hermitian
involution `Y` that does not move the transponder between sites: the gated term is the
ungated one less `g Y P'`, with `P'` the projector on the configurations where the carriers
are apart, so the two orbits differ by at most `|g|` times the time the **ungated** orbit
spends apart.

`RecordLayer/TransponderRabi.lean` (`norm_exp_sub_rabi_mul_le`) and
`RecordLayer/TransponderDetuned.lean` (`norm_exp_sub_rabi_add_mul_le`) have this for a `Y`
that commutes with the free Hamiltonian or turns about a fixed axis. No such hypothesis is
made here, and the reference orbit is not solved here.

* `compositeH_add_smul` — the ungated term is a term of the transponder's own Hamiltonian;
* ★★★ `norm_exp_gated_sub_ungated_mul_le` — **the orbit under `H₀ + g · gate · Y` is the
  orbit under `H₀ + g Y` within `|g| ∫₀ᵗ ‖P' e^{−is(H₀ + gY)} X‖ ds`**;
* ★★ `abs_norm_mul_gated_sub_ungated_le` — the same for the norm of any part `Q`, `‖Q‖ ≤ 1`;
* ★★★ `transponder_band_gated_second_level` — **for the transponder of UA-21: the
  second-level part under the gated term is the second-level part under the ungated term,
  within that integral**.

## Honest scope

⚠️ **The integral is not evaluated.** It is the amplitude, along the ungated orbit, of the
configurations where the carriers are apart. Along that orbit the part of the transponder
that has reached the second level moves, so the bound is small only while the contact
region holds both the resting part and the part that has left (UA-21, risk (iii)). No packet
is put in here.

⚠️ **So no launch by a meeting is shown yet.** With `RecordLayer/TransponderBandRabi.lean`
the reference orbit of a transponder mode is known, but not yet the reference orbit of a
product with a messenger, nor its weight apart.

⚠️ **Contact from the flow time `0`.** A run that starts apart needs the two-stage form of
`RecordLayer/TransponderDetunedMeeting.lean`.

⚠️ **Flow times.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UA-21,
UO-26, UD-258, UD-262, UD-266, UD-267; §9.4); `RecordLayer/TransponderBandRabi.lean`
(`exp_bandContact_mulVec_inLevel_zero`); `Mathlib/Analysis/Matrix/DuhamelState.lean`
(`Matrix.norm_exp_neg_I_add_sub_mul_le`); `RecordLayer/UnifiedCoincidence.lean` (`coincProj`,
`gateOp`, `one_sub_coincProj`, `coincProj_mul_one_kronecker`);
`RecordLayer/TransponderRabi.lean` (`norm_exp_sub_rabi_mul_le`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

section Gate

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
/-- The ungated term is a term of the second carrier's own Hamiltonian. -/
theorem compositeH_add_smul (M₀ : Matrix ι ι ℂ) (C Y : Matrix κ κ ℂ) (g : ℂ) :
    compositeH M₀ (C + g • Y) = compositeH M₀ C + g • ((1 : Matrix ι ι ℂ) ⊗ₖ Y) := by
  unfold compositeH
  rw [Matrix.kronecker_add, Matrix.kronecker_smul, add_assoc]

variable [Nonempty ι] [Nonempty κ]

/-- ★★★ **The gated contact term against the ungated one.** `M₀`, `C` and `Y` are Hermitian,
`Y² = 1`, and `Y` has no entry between different sites of the second carrier. For a real `g`
and `t ≥ 0` the orbit of `X` under `M₀ ⊗ 1 + 1 ⊗ C + g · gate · Y` is its orbit under
`M₀ ⊗ 1 + 1 ⊗ (C + g Y)` within `|g| ∫₀ᵗ ‖P' e^{−is(M₀ ⊗ 1 + 1 ⊗ (C + gY))} X‖ ds`, where `P'`
projects on the configurations where the two carriers are not in the relation `r`. -/
theorem norm_exp_gated_sub_ungated_mul_le (σ : ι → S) (τ : κ → S) (r : S → S → Prop)
    [DecidableRel r] {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian) {C Y : Matrix κ κ ℂ}
    (hC : C.IsHermitian) (hYh : Y.IsHermitian) (hYY : Y * Y = 1)
    (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (g : ℝ) (X : Matrix (ι × κ) (ι × κ) ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (compositeH M₀ C + (g : ℂ) • gateOp σ τ r Y)))
        - exp (t • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y)))) * X‖
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y))) * X‖ := by
  have hgY : ((g : ℂ) • Y).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hYh.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hH := compositeH_isHermitian hM (hC.add hgY)
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ Y).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one hYh
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ Y) * ((1 : Matrix ι ι ℂ) ⊗ₖ Y) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, hYY, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ Y‖ ≤ 1 := norm_le_one_of_isHermitian_invol hSh hSS
  have hPS' := coincProj_mul_one_kronecker (ι := ι) σ τ (fun a b => ¬ r a b) hY
  have hGS : gateOp σ τ r Y - (1 : Matrix ι ι ℂ) ⊗ₖ Y
      = -(((1 : Matrix ι ι ℂ) ⊗ₖ Y) * coincProj σ τ (fun a b => ¬ r a b)) := by
    rw [← hPS', ← one_sub_coincProj σ τ r, gateOp, sub_mul, one_mul, neg_sub]
  have hG := gateOp_isHermitian σ τ r hYh hY
  have hV : ((g : ℂ) • (gateOp σ τ r Y - (1 : Matrix ι ι ℂ) ⊗ₖ Y)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (hG.sub hSh).eq, Complex.star_def,
      Complex.conj_ofReal]
  have hsum : compositeH M₀ C + (g : ℂ) • gateOp σ τ r Y
      = compositeH M₀ (C + (g : ℂ) • Y)
        + (g : ℂ) • (gateOp σ τ r Y - (1 : Matrix ι ι ℂ) ⊗ₖ Y) := by
    rw [compositeH_add_smul, smul_sub]
    abel
  have h := Matrix.norm_exp_neg_I_add_sub_mul_le _ _ X hH hV ht
  rw [← hsum] at h
  refine h.trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on ht
    ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
    ((continuous_const.mul (Matrix.continuous_norm_mul_exp_smul_mul _
      (coincProj σ τ fun a b => ¬ r a b) X)).intervalIntegrable _ _) fun s _ => ?_
  have e1 : ((1 : Matrix ι ι ℂ) ⊗ₖ Y) * coincProj σ τ (fun a b => ¬ r a b)
        * exp (s • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y))) * X
      = ((1 : Matrix ι ι ℂ) ⊗ₖ Y) * (coincProj σ τ (fun a b => ¬ r a b)
        * exp (s • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y))) * X) := by
    simp only [mul_assoc]
  rw [hGS, smul_neg, neg_mul, neg_mul, norm_neg, smul_mul_assoc, smul_mul_assoc, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, e1]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg g)
  exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)

/-- ★★ **The same for the norm of any part.** For `Q` with `‖Q‖ ≤ 1`, the norms of `Q` applied
to the two orbits differ by at most the same integral. -/
theorem abs_norm_mul_gated_sub_ungated_le (σ : ι → S) (τ : κ → S) (r : S → S → Prop)
    [DecidableRel r] {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian) {C Y : Matrix κ κ ℂ}
    (hC : C.IsHermitian) (hYh : Y.IsHermitian) (hYY : Y * Y = 1)
    (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (g : ℝ) {Q : Matrix (ι × κ) (ι × κ) ℂ}
    (hQ : ‖Q‖ ≤ 1) (X : Matrix (ι × κ) (ι × κ) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    |‖Q * exp (t • ((-Complex.I) • (compositeH M₀ C + (g : ℂ) • gateOp σ τ r Y))) * X‖
        - ‖Q * exp (t • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y))) * X‖|
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y))) * X‖ := by
  have e : Q * exp (t • ((-Complex.I) • (compositeH M₀ C + (g : ℂ) • gateOp σ τ r Y))) * X
        - Q * exp (t • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y))) * X
      = Q * ((exp (t • ((-Complex.I) • (compositeH M₀ C + (g : ℂ) • gateOp σ τ r Y)))
          - exp (t • ((-Complex.I) • compositeH M₀ (C + (g : ℂ) • Y)))) * X) := by
    simp only [mul_assoc, mul_sub, sub_mul]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [e]
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hQ).trans
    (norm_exp_gated_sub_ungated_mul_le σ τ r hM hC hYh hYY hY g X ht))

end Gate

/-! ### The transponder of UA-21 -/

section Band

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **The transponder of UA-21: the gated term launches what the ungated term does, within
the time spent apart.** The transponder has the first-level energy `E₀` and a Hermitian
second-level Hamiltonian `H₁`. For every `X` and `t ≥ 0`, the part of the orbit of `X` with
the transponder in its second level has, under the contact term of UA-19 (b), the norm it has
under the swap term acting everywhere, within `|g| ∫₀ᵗ ‖P' e^{−isH_u} X‖ ds`. Here `H_u` is
the Hamiltonian with the swap acting everywhere and `P'` projects on the configurations
where the two carriers are apart. -/
theorem transponder_band_gated_second_level (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian) (E₀ : ℝ) {H₁ : Matrix n n ℂ}
    (hH₁ : H₁.IsHermitian) (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    |‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀
              (Matrix.blockDiagonal (bandBlocks E₀ H₁))
            + (g : ℂ) • gateOp σ τ r (levelSwap n)))) * X‖
        - ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • compositeH M₀
              (Matrix.blockDiagonal (bandBlocks E₀ H₁) + (g : ℂ) • levelSwap n))) * X‖|
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀
              (Matrix.blockDiagonal (bandBlocks E₀ H₁) + (g : ℂ) • levelSwap n))) * X‖ :=
  abs_norm_mul_gated_sub_ungated_le σ τ r hM
    (blockDiagonal_isHermitian (bandBlocks_isHermitian E₀ hH₁)) (levelSwap_isHermitian n)
    levelSwap_mul_self hτ g
    (norm_le_one_of_isHermitian_idem (one_kronecker_levelProj_isHermitian 1)
      (one_kronecker_levelProj_mul_self 1)) X ht

end Band

end CSD.RecordLayer

end
