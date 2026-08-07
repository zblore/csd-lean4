/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Interaction
public import CsdLean4.CV.DynamicalLocality
public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormDiagonal

/-!
# CV-9: small-coupling pricing — locality violation is linear in the coupling

**Category:** CV (continuous variables — the multi-mode field).

CV-8 bounded WHERE interaction moves support (the light cone); this module
prices HOW MUCH, in operator norm, via the Duhamel bound
(`Matrix.norm_exp_smul_neg_I_sub_le`, generalized to arbitrary finite index
for exactly this use):

* `freeField_perturbed_exp_dist_le` — for ANY Hermitian perturbation `V`
  (diagonal or not — hopping interactions included):
  `‖exp (-(iτ)•(H_field + λ•V)) − freeFieldU τ‖ ≤ |τ|·|λ|·‖V‖`. The
  pricing needs no closed-form step for the perturbed drive.
* ★ `interactingU_dist_le` — the CV-7 diagonal drive: with `|v| ≤ C`
  pointwise, `‖interactingU τ λ v − freeFieldU τ‖ ≤ |τ|·(|λ|·C)` (the
  diagonal L2-norm bound `Matrix.l2_opNorm_diagonal_le`).
* `heisenberg_dist_le` — Heisenberg stability: conjugation by nearby
  unitaries moves any observable by at most `2·‖U − W‖·‖A‖` (C*-identity
  `‖U‖ = 1` + submultiplicativity).
* ★★ `heisenberg_interactingU_near_supported` — **the price of locality
  violation**: the interacting Heisenberg observable of an `S`-supported
  `A` stays within `2·|τ|·|λ|·C·‖A‖` of an `S`-supported operator (the
  free-evolved one, CV-6). Switching on a coupling `λ` costs locality at
  most **linearly in `λ`** — the CV rhyme of the record half-life bound
  `μ ≤ n·ε` (`RecordDegradation.lean`).

⚠️ All norms here are the **scoped `Matrix.Norms.L2Operator` (C*) norm**
(`open scoped Matrix.Norms.L2Operator`), never the elementwise or Frobenius
norm — consumers must open the same scope. Honest scope: the bounds are
inequalities; whether the linear price is attained (an actual violation
rate) is a dynamics question not claimed here, and the light cone for
non-diagonal drives is CV-8's recorded residue.

## References

`CV/Interaction.lean` (CV-7); `CV/SupportSpreading.lean` (CV-8);
`CV/DynamicalLocality.lean` (CV-6, the free-evolved comparator);
`CsdLean4/Mathlib/Analysis/Matrix/DuhamelBound.lean` (the engine);
`CsdLean4/Mathlib/Analysis/Matrix/L2OpNormDiagonal.lean`;
`specs/cv-stage3-plan.md` §3c; `specs/future-work.md` (row CV-9);
`Empirical/CSD/QuantumChaos/RecordDegradation.lean` (the record-side rhyme).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix NormedSpace

namespace CSD.CV

variable {K N : ℕ}

instance instNonemptyFieldConfig [NeZero N] : Nonempty (FieldConfig K N) :=
  ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

/-! ### Hermitian bookkeeping -/

/-- A real diagonal is Hermitian. -/
lemma isHermitian_diagonal_ofReal {ι : Type*} [DecidableEq ι] (w : ι → ℝ) :
    (Matrix.diagonal (fun i => ((w i : ℝ) : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [Complex.conj_ofReal]

/-- The free-field Hamiltonian is Hermitian. -/
theorem fieldHamiltonian_isHermitian (K N : ℕ) :
    (fieldHamiltonian K N).IsHermitian := by
  rw [show fieldHamiltonian K N
      = Matrix.diagonal (fun c => ((fieldEnergy c : ℝ) : ℂ)) from rfl]
  exact isHermitian_diagonal_ofReal _

/-- Real scaling preserves Hermiticity. -/
lemma isHermitian_real_smul
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : A.IsHermitian) (r : ℝ) : (r • A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hA.eq]

/-! ### The Duhamel price of a perturbation -/

/-- The `-(iτ)`-scaling in Schrödinger form, for the Duhamel interface. -/
lemma neg_I_mul_smul_eq {τ : ℝ}
    (M : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    (-(Complex.I * (τ : ℂ))) • M = τ • ((-Complex.I) • M) := by
  rw [← smul_assoc, Complex.real_smul]
  congr 1
  ring

/-- **The Duhamel price of any Hermitian perturbation** — diagonal or not,
no closed-form step needed:
`‖exp (-(iτ)•(H_field + λ•V)) − freeFieldU τ‖ ≤ |τ|·(|λ|·‖V‖)`. -/
theorem freeField_perturbed_exp_dist_le [NeZero N] (τ lam : ℝ)
    {V : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hV : V.IsHermitian) :
    ‖exp ((-(Complex.I * (τ : ℂ))) • (fieldHamiltonian K N + lam • V))
        - (freeFieldU K N τ).val‖ ≤ |τ| * (|lam| * ‖V‖) := by
  rw [freeFieldU_eq_exp, neg_I_mul_smul_eq, neg_I_mul_smul_eq]
  calc ‖exp (τ • ((-Complex.I) • (fieldHamiltonian K N + lam • V)))
        - exp (τ • ((-Complex.I) • fieldHamiltonian K N))‖
      ≤ |τ| * ‖(fieldHamiltonian K N + lam • V) - fieldHamiltonian K N‖ :=
        Matrix.norm_exp_smul_neg_I_sub_le _ _
          ((fieldHamiltonian_isHermitian K N).add (isHermitian_real_smul hV lam))
          (fieldHamiltonian_isHermitian K N) τ
    _ = |τ| * (|lam| * ‖V‖) := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

/-- ★ **The interacting drive stays within `|τ|·|λ|·C` of the free drive**
when the potential is pointwise bounded by `C` — the CV-7 step, priced. -/
theorem interactingU_dist_le [NeZero N] (τ lam : ℝ)
    (v : FieldConfig K N → ℝ) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C) :
    ‖(interactingU K N τ lam v).val - (freeFieldU K N τ).val‖
      ≤ |τ| * (|lam| * C) := by
  rw [interactingU_eq_exp]
  refine le_trans
    (freeField_perturbed_exp_dist_le τ lam (interactionHamiltonian_isHermitian v)) ?_
  gcongr
  rw [show interactionHamiltonian v
      = Matrix.diagonal (fun c => ((v c : ℝ) : ℂ)) from rfl]
  exact Matrix.l2_opNorm_diagonal_le _ hC fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hv c

/-! ### Heisenberg stability and the price of locality violation -/

/-- **Heisenberg stability**: conjugation by nearby unitaries moves any
observable by at most `2·‖U − W‖·‖A‖` (C*-identity + submultiplicativity). -/
theorem heisenberg_dist_le [NeZero N]
    (U W : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    ‖heisenberg U A - heisenberg W A‖ ≤ 2 * ‖U.val - W.val‖ * ‖A‖ := by
  have h3 : ∀ X Y Z : Matrix (FieldConfig K N) (FieldConfig K N) ℂ,
      ‖X * Y * Z‖ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ := fun X Y Z =>
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le X Y) (norm_nonneg Z))
  have hsplit : heisenberg U A - heisenberg W A
      = star U.val * A * (U.val - W.val)
        + star (U.val - W.val) * A * W.val := by
    rw [heisenberg, heisenberg, star_sub]
    noncomm_ring
  have hUs : ‖star U.val‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    exact CStarRing.norm_of_mem_unitary U.property
  have hW : ‖W.val‖ = 1 := CStarRing.norm_of_mem_unitary W.property
  have h1 := h3 (star U.val) A (U.val - W.val)
  have h2 := h3 (star (U.val - W.val)) A W.val
  rw [hUs] at h1
  rw [show ‖star (U.val - W.val)‖ = ‖U.val - W.val‖ from by
      rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose],
    hW] at h2
  calc ‖heisenberg U A - heisenberg W A‖
      = ‖star U.val * A * (U.val - W.val)
          + star (U.val - W.val) * A * W.val‖ := by rw [hsplit]
    _ ≤ ‖star U.val * A * (U.val - W.val)‖
          + ‖star (U.val - W.val) * A * W.val‖ := norm_add_le _ _
    _ ≤ 1 * ‖A‖ * ‖U.val - W.val‖ + ‖U.val - W.val‖ * ‖A‖ * 1 :=
        add_le_add h1 h2
    _ = 2 * ‖U.val - W.val‖ * ‖A‖ := by ring

/-- The interacting Heisenberg observable stays within `2·|τ|·|λ|·C·‖A‖`
of the free-evolved one. -/
theorem heisenberg_interactingU_dist_le [NeZero N] (τ lam : ℝ)
    (v : FieldConfig K N → ℝ) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    ‖heisenberg (interactingU K N τ lam v) A
        - heisenberg (freeFieldU K N τ) A‖
      ≤ 2 * (|τ| * (|lam| * C)) * ‖A‖ := by
  refine le_trans (heisenberg_dist_le _ _ A) ?_
  gcongr
  exact interactingU_dist_le τ lam v hC hv

/-- ★★ **The price of locality violation is linear in the coupling**: the
interacting Heisenberg observable of an `S`-supported `A` stays within
`2·|τ|·|λ|·C·‖A‖` of an `S`-supported operator — the free-evolved one,
which CV-6 keeps on `S` exactly. The CV rhyme of the record half-life
bound `μ ≤ n·ε`. -/
theorem heisenberg_interactingU_near_supported [NeZero N]
    {S : Finset (Fin K)} (τ lam : ℝ) (v : FieldConfig K N → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn S A) :
    ∃ B, SupportedOn S B ∧
      ‖heisenberg (interactingU K N τ lam v) A - B‖
        ≤ 2 * (|τ| * (|lam| * C)) * ‖A‖ :=
  ⟨heisenberg (freeFieldU K N τ) A, heisenberg_freeFieldU_supportedOn τ hA,
    heisenberg_interactingU_dist_le τ lam v hC hv A⟩

end CSD.CV
