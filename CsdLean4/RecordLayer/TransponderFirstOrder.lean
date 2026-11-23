/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderAtRest
public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelOrbitRemainder

/-!
# A signal does leave: the transponder's second level fills while the carriers are in contact

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2), the caused return: a
signal does leave, with its weight).

`RecordLayer/TransponderAtRest.lean` shows nothing is launched before the messenger's box
reaches the transponder. Here the first-order term of the contact term is evaluated while
the two carriers are in contact, for a transponder whose two levels have the same
Hamiltonian.

## The first-order term

* `duhamelFirst_of_commute` — for a perturbation `W` that commutes with the generator, the
  first-order term is `t · W e^{tA} X`;
* `norm_duhamelFirst_sub_le` — two perturbations give first-order terms that differ by at
  most the accumulated action of their difference on the unperturbed orbit;
* ★★★ `norm_exp_sub_mul_sub_first_le` — **the first-order term, evaluated.** For `G = S P`
  with `S` commuting with `H₀` and `G − S = −S P'`: the perturbed orbit of `X` under
  `H₀ + g G` is the free orbit plus `−i g t · S e^{−itH₀} X`, within
  `|g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds + |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖ ds) t`.

## The transponder

* ★★★ `transponder_first_order` — the contact term of UA-19 with a transponder whose level
  swap commutes with its Hamiltonian: `S` the level swap, `P` the coincidence projector,
  `P'` the projector of the complementary relation ("apart");
* ★★★ `transponder_launch_ge` — **a signal does leave**: the perturbed orbit departs from the
  free one by at least
  `|g| t ‖X‖ − |g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds − |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖ ds) t`;
* `levelSwap_mul_blockDiagonal_smul_one` — a transponder at rest with one energy for both
  levels meets the commutation hypothesis.

## Honest scope

⚠️ **Contact from the flow time `0`.** The leading term `|g| t` counts the whole of `[0, t]`;
the term with `P'` is the accumulated amplitude of the free orbit on configurations where
the two carriers are apart, and is small only if they are in contact throughout. The run
"apart, then in contact" is not composed here.

⚠️ **The two levels have the same Hamiltonian** (the level swap commutes with it). With
different energies the leading term carries an oscillating factor; that case is not treated.

⚠️ **First order.** The last term is of order `g² t²`; the statement says something leaves
only while `|g| t` is small. It does not show the second level fills.

⚠️ **For a matrix `X`, in the operator norm.** The departure of the perturbed orbit from the
free one is bounded below; that the departure is in the second level is not stated here
(it is, for an `X` in the first level, since the leading term is a level swap).

⚠️ **The weights of the two projectors along the free orbit are left as integrals.** No
packet is put in; no instance with numbers. No pointer, no arena.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-212, UD-216, UD-226, UD-252, UD-253); `specs/unified-records-spacetime-task-plans.md` (§9,
item 2); `Mathlib/Analysis/Matrix/DuhamelFirstOrder.lean` (`Matrix.duhamelFirst`,
`Matrix.duhamelKernel`); `Mathlib/Analysis/Matrix/DuhamelOrbitRemainder.lean`
(`Matrix.norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit`,
`Matrix.norm_duhamelKernel_le_integral`); `Mathlib/Analysis/Matrix/DuhamelSector.lean`
(`Matrix.mul_exp_smul_eq_of_commute`); `RecordLayer/UnifiedCoincidence.lean` (`gateOp`,
`coincProj`, `one_sub_coincProj`, `coincProj_mul_one_kronecker`);
`RecordLayer/UnifiedTransponder.lean` (`one_kronecker_mul_compositeH`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The first-order term -/

section FirstOrder

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- For a perturbation that commutes with the generator, the first-order term is
`t · W e^{tA} X`. -/
theorem duhamelFirst_of_commute (A W X : Matrix m m ℂ) (h : W * A = A * W) (t : ℝ) :
    Matrix.duhamelFirst A W X t = t • (W * exp (t • A) * X) := by
  have hc : ∀ s : ℝ, W * exp (s • A) = exp (s • A) * W := fun s =>
    Matrix.mul_exp_smul_eq_of_commute h s
  have hint : ∀ s : ℝ, exp ((-s) • A) * W * exp (s • A) * X = W * X := fun s => by
    have hinv := Matrix.exp_smul_mul_exp_neg_smul A (-s)
    rw [neg_neg] at hinv
    calc exp ((-s) • A) * W * exp (s • A) * X
        = exp ((-s) • A) * (W * exp (s • A)) * X := by rw [mul_assoc (exp ((-s) • A))]
      _ = exp ((-s) • A) * exp (s • A) * W * X := by rw [hc s, ← mul_assoc]
      _ = W * X := by rw [hinv, one_mul]
  rw [Matrix.duhamelFirst, Matrix.duhamelKernel]
  simp only [hint]
  rw [intervalIntegral.integral_const, sub_zero, mul_smul_comm, ← mul_assoc, ← hc t]

/-- Two perturbations give first-order terms that differ by at most the accumulated action
of their difference on the unperturbed orbit. -/
theorem norm_duhamelFirst_sub_le (A W W' X : Matrix m m ℂ) (hA : Aᴴ = -A) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖Matrix.duhamelFirst A W X t - Matrix.duhamelFirst A W' X t‖
      ≤ ∫ s in (0 : ℝ)..t, ‖(W - W') * exp (s • A) * X‖ := by
  have hk : Matrix.duhamelKernel A W X t - Matrix.duhamelKernel A W' X t
      = Matrix.duhamelKernel A (W - W') X t := by
    unfold Matrix.duhamelKernel
    rw [← intervalIntegral.integral_sub
      ((Matrix.continuous_duhamelIntegrand A W X).intervalIntegrable _ _)
      ((Matrix.continuous_duhamelIntegrand A W' X).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [mul_sub, sub_mul]
  rw [Matrix.duhamelFirst, Matrix.duhamelFirst, ← mul_sub, hk]
  refine (norm_mul_le _ _).trans ?_
  rw [Matrix.l2_opNorm_exp_smul_skew A hA t, one_mul]
  exact Matrix.norm_duhamelKernel_le_integral A (W - W') X hA ht

/-- ★★★ **The first-order term, evaluated.** `H₀` and `G` are Hermitian, `G = S P` with
`‖S‖ ≤ 1`, `‖P‖ ≤ 1`, `S` commutes with `H₀`, and `G − S = −S P'`. For a real `g` and
`t ≥ 0` the orbit of `X` under `H₀ + g G` is the free orbit plus `−i g t · S e^{−itH₀} X`,
within `|g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds + |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖ ds) t`. -/
theorem norm_exp_sub_mul_sub_first_le (H₀ G S P P' X : Matrix m m ℂ) (g : ℝ)
    (hH₀ : H₀.IsHermitian) (hG : G.IsHermitian) (hSH : S * H₀ = H₀ * S) (hS1 : ‖S‖ ≤ 1)
    (hP1 : ‖P‖ ≤ 1) (hGP : G = S * P) (hGS : G - S = -(S * P')) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G))) - exp (t • ((-Complex.I) • H₀))) * X
        - (-Complex.I * g * t) • (S * exp (t • ((-Complex.I) • H₀)) * X)‖
      ≤ |g| * (∫ s in (0 : ℝ)..t, ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖)
        + |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖) * t := by
  have hA : ((-Complex.I) • H₀)ᴴ = -((-Complex.I) • H₀) := Matrix.conjTranspose_neg_I_smul hH₀
  have hV : ((g : ℂ) • G).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hG.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hG1 : ‖G‖ ≤ 1 := by
    rw [hGP]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul hS1 hP1 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hVn : ‖(g : ℂ) • G‖ ≤ |g| := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg g) hG1
  have hW'A : ((-Complex.I) • ((g : ℂ) • S)) * ((-Complex.I) • H₀)
      = ((-Complex.I) • H₀) * ((-Complex.I) • ((g : ℂ) • S)) :=
    ((((show Commute S H₀ from hSH).smul_left (g : ℂ)).smul_left (-Complex.I)).smul_right
      (-Complex.I)).eq
  have h1 := Matrix.norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit H₀ ((g : ℂ) • G) X
    hH₀ hV ht
  have hB := norm_duhamelFirst_sub_le ((-Complex.I) • H₀) ((-Complex.I) • ((g : ℂ) • G))
    ((-Complex.I) • ((g : ℂ) • S)) X hA ht
  have hC := duhamelFirst_of_commute ((-Complex.I) • H₀) ((-Complex.I) • ((g : ℂ) • S)) X
    hW'A t
  have hlead : (t : ℝ) • ((-Complex.I) • ((g : ℂ) • S) * exp (t • ((-Complex.I) • H₀)) * X)
      = (-Complex.I * g * t) • (S * exp (t • ((-Complex.I) • H₀)) * X) := by
    rw [← Complex.coe_smul t]
    simp only [smul_mul_assoc, smul_smul]
    congr 1
    ring
  rw [hC, hlead] at hB
  -- the difference of the two perturbations on the orbit
  have hpt : ∀ s : ℝ,
      ‖((-Complex.I) • ((g : ℂ) • G) - (-Complex.I) • ((g : ℂ) • S))
          * exp (s • ((-Complex.I) • H₀)) * X‖
        ≤ |g| * ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [← smul_sub, ← smul_sub, hGS]
    simp only [smul_mul_assoc, neg_mul, norm_smul, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)) (abs_nonneg g)
  have hI1 : ∫ s in (0 : ℝ)..t,
        ‖((-Complex.I) • ((g : ℂ) • G) - (-Complex.I) • ((g : ℂ) • S))
          * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ P' X)).intervalIntegrable _ _)
      fun s _ => hpt s
  -- the remainder
  have hpt2 : ∀ s : ℝ, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ‖P * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [hGP]
    simp only [smul_mul_assoc, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)) (abs_nonneg g)
  have hI2 : ∫ s in (0 : ℝ)..t, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ P X)).intervalIntegrable _ _)
      fun s _ => hpt2 s
  have hI2nn : 0 ≤ ∫ s in (0 : ℝ)..t, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖ :=
    intervalIntegral.integral_nonneg ht fun s _ => norm_nonneg _
  have hrem : ‖(g : ℂ) • G‖
        * (∫ s in (0 : ℝ)..t, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖) * t
      ≤ |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖) * t :=
    mul_le_mul_of_nonneg_right (mul_le_mul hVn hI2 hI2nn (abs_nonneg g)) ht
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G))) - exp (t • ((-Complex.I) • H₀))) * X)
    (Matrix.duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • ((g : ℂ) • G)) X t)
    ((-Complex.I * g * t) • (S * exp (t • ((-Complex.I) • H₀)) * X))
  linarith [htri, h1, hB, hI1, hrem]

end FirstOrder

/-! ### The transponder -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **The first-order term of the contact term of UA-19.** The transponder's level swap
commutes with its Hamiltonian. For a real `g`, any `X` and `t ≥ 0`, the orbit of `X` is the
free orbit plus `−i g t` times the level swap of the free orbit, within
`|g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds + |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖ ds) t`, `P` the coincidence
projector of the messenger and the transponder and `P'` that of the complementary
relation. -/
theorem transponder_first_order (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X
        - (-Complex.I * g * t) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      ≤ |g| * (∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        + |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) * t := by
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh
      (by rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self,
        Matrix.one_kronecker_one])
  have hP1 : ‖coincProj σ τ r‖ ≤ 1 := by
    rw [coincProj]
    exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp
  have hPS := coincProj_mul_one_kronecker (ι := ι) σ τ r hτ
  have hPS' := coincProj_mul_one_kronecker (ι := ι) σ τ (fun a b => ¬ r a b) hτ
  have hGP : gateOp σ τ r (levelSwap n)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ r := by
    rw [gateOp, hPS]
  have hGS : gateOp σ τ r (levelSwap n) - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n
      = -(((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ (fun a b => ¬ r a b)) := by
    rw [← hPS', ← one_sub_coincProj σ τ r, gateOp, sub_mul, one_mul, neg_sub]
  exact norm_exp_sub_mul_sub_first_le _ _ _ _ _ X g
    (compositeH_isHermitian hM (blockDiagonal_isHermitian hT))
    (gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ)
    (one_kronecker_mul_compositeH M₀ hS) hS1 hP1 hGP hGS ht

/-- ★★★ **A signal does leave.** Under the hypotheses of `transponder_first_order`, the orbit
of `X` departs from the free orbit by at least
`|g| t ‖X‖ − |g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds − |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖ ds) t`. -/
theorem transponder_launch_ge (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    |g| * t * ‖X‖
        - |g| * (∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        - |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) * t
      ≤ ‖(exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X‖ := by
  have hfirst := transponder_first_order σ τ r hτ hM hT hS g X ht
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hA := Matrix.conjTranspose_neg_I_smul hH₀
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh hSS
  -- the leading term has the size of `X`
  have hinv := Matrix.exp_smul_mul_exp_neg_smul
    ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)) (-t)
  rw [neg_neg] at hinv
  have hX : X = exp ((-t) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
      * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)) := by
    rw [← mul_assoc ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n), ← mul_assoc
      ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n), hSS, one_mul, ← mul_assoc, hinv, one_mul]
  have hlead : ‖X‖ ≤ ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
      * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
    calc ‖X‖ = ‖exp ((-t) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
          * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
            * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
              * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))‖ :=
          congrArg norm hX
      _ ≤ ‖exp ((-t) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))‖
          * (‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖
            * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
              * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * (1 * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
              * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) := by
          rw [Matrix.l2_opNorm_exp_smul_skew _ hA (-t)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hS1 (norm_nonneg _)) zero_le_one
      _ = _ := by rw [one_mul, one_mul]
  have hc : ‖(-Complex.I * g * t) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      = |g| * t * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
    rw [norm_smul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht]
  have h2 := norm_sub_norm_le
    ((-Complex.I * g * t) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
      * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))
    ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n))))
        - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X)
  rw [norm_sub_rev, hc] at h2
  have h3 := mul_le_mul_of_nonneg_left hlead (mul_nonneg (abs_nonneg g) ht)
  linarith

omit [Nonempty n] in
/-- A transponder at rest with one energy for both levels: its level swap commutes with its
Hamiltonian. -/
theorem levelSwap_mul_blockDiagonal_smul_one (E : ℝ) :
    levelSwap n * Matrix.blockDiagonal (fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = Matrix.blockDiagonal (fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        * levelSwap n := by
  have hd : Matrix.blockDiagonal (fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = ((E : ℝ) : ℂ) • (1 : Matrix (n × Fin 2) (n × Fin 2) ℂ) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.blockDiagonal_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
      smul_eq_mul]
    split_ifs <;> simp_all
  rw [hd, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

end Transponder

end CSD.RecordLayer

end
