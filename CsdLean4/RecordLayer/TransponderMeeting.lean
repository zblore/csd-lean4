/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderFirstOrder

/-!
# Apart, then in contact: the departure starts at the meeting

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, items (1) and (2) in one run, the
caused return).

`RecordLayer/TransponderFirstOrder.lean` evaluates the first-order term of the contact term
for carriers in contact from the flow time `0`. Here the run has two parts: apart up to a
flow time `t₁`, in contact from `t₁` to `t`. The leading term counts only the second part.

* ★★ `norm_duhamelFirst_sub_meeting_le` — for a perturbation `W`, a second one `W'` that
  commutes with the generator, and `0 ≤ t₁ ≤ t`: the first-order term of `W` is
  `(t − t₁) · W' e^{tA} X` within the accumulated action of `W` on the unperturbed orbit up
  to `t₁` plus that of `W − W'` from `t₁` to `t`;
* ★★★ `norm_exp_sub_mul_sub_first_meeting_le` — for `G = S P`, `S` commuting with `H₀`,
  `G − S = −S P'`: the orbit of `X` under `H₀ + g G` is the free orbit plus
  `−i g (t − t₁) · S e^{−itH₀} X`, within
  `|g| ∫₀^{t₁} ‖P e^{−isH₀} X‖ + |g| ∫_{t₁}^{t} ‖P' e^{−isH₀} X‖ + |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖) t`;
* ★★★ `transponder_first_order_meeting` — the contact term of UA-19, `S` the level swap, `P`
  "in contact", `P'` "apart";
* ★★★ `transponder_launch_meeting_ge` — **the departure starts at the meeting**: the orbit
  departs from the free one by at least `|g| (t − t₁) ‖X‖` less those three terms.

## Honest scope

⚠️ **`t₁` is a parameter, not a time read off the flow.** The statement holds for every
`0 ≤ t₁ ≤ t`; it is useful for a `t₁` before which the carriers are apart and after which
they are in contact, and it does not say there is one. Between "apart" and "in contact"
there is in general a time of partial contact, which goes into the error terms.

⚠️ **The two levels have the same Hamiltonian**, as in UD-253.

⚠️ **First order.** The last term is of order `g² t²`.

⚠️ **For a matrix `X`, in the operator norm.** No packet is put in; the three weights are left
as integrals along the free orbit. No pointer, no arena.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-252, UD-253, UD-254); `specs/unified-records-spacetime-task-plans.md` (§9, items 1 and 2);
`RecordLayer/TransponderFirstOrder.lean` (`transponder_first_order`,
`duhamelFirst_of_commute`); `Mathlib/Analysis/Matrix/DuhamelFirstOrder.lean`
(`Matrix.duhamelFirst`, `Matrix.duhamelKernel`);
`Mathlib/Analysis/Matrix/DuhamelOrbitRemainder.lean`
(`Matrix.norm_duhamelKernel_le_integral`,
`Matrix.norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The first-order term over a run in two parts -/

section FirstOrder

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- ★★ **The first-order term over a run in two parts.** `W'` commutes with the generator `A`.
For `0 ≤ t₁ ≤ t` the first-order term of `W` is `(t − t₁) · W' e^{tA} X`, within the
accumulated action of `W` on the unperturbed orbit up to `t₁` plus that of `W − W'` from
`t₁` to `t`. -/
theorem norm_duhamelFirst_sub_meeting_le (A W W' X : Matrix m m ℂ) (hA : Aᴴ = -A)
    (h : W' * A = A * W') {t₁ t : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t) :
    ‖Matrix.duhamelFirst A W X t - (t - t₁) • (W' * exp (t • A) * X)‖
      ≤ (∫ s in (0 : ℝ)..t₁, ‖W * exp (s • A) * X‖)
        + ∫ s in t₁..t, ‖(W - W') * exp (s • A) * X‖ := by
  have hc : ∀ s : ℝ, W' * exp (s • A) = exp (s • A) * W' := fun s =>
    Matrix.mul_exp_smul_eq_of_commute h s
  have hint : ∀ s : ℝ, exp ((-s) • A) * W' * exp (s • A) * X = W' * X := fun s => by
    have hinv := Matrix.exp_smul_mul_exp_neg_smul A (-s)
    rw [neg_neg] at hinv
    calc exp ((-s) • A) * W' * exp (s • A) * X
        = exp ((-s) • A) * (W' * exp (s • A)) * X := by rw [mul_assoc (exp ((-s) • A))]
      _ = exp ((-s) • A) * exp (s • A) * W' * X := by rw [hc s, ← mul_assoc]
      _ = W' * X := by rw [hinv, one_mul]
  have hiW := Matrix.continuous_duhamelIntegrand A W X
  have hiW' := Matrix.continuous_duhamelIntegrand A W' X
  have hsplit : Matrix.duhamelKernel A W X t
      = Matrix.duhamelKernel A W X t₁
        + ∫ s in t₁..t, exp ((-s) • A) * W * exp (s • A) * X := by
    unfold Matrix.duhamelKernel
    exact (intervalIntegral.integral_add_adjacent_intervals (hiW.intervalIntegrable _ _)
      (hiW.intervalIntegrable _ _)).symm
  have hmid : ∫ s in t₁..t, exp ((-s) • A) * W * exp (s • A) * X
      = (∫ s in t₁..t, exp ((-s) • A) * (W - W') * exp (s • A) * X)
        + (t - t₁) • (W' * X) := by
    have e1 : ∫ s in t₁..t, exp ((-s) • A) * (W - W') * exp (s • A) * X
        = (∫ s in t₁..t, exp ((-s) • A) * W * exp (s • A) * X)
          - ∫ s in t₁..t, exp ((-s) • A) * W' * exp (s • A) * X := by
      rw [← intervalIntegral.integral_sub (hiW.intervalIntegrable _ _)
        (hiW'.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [mul_sub, sub_mul]
    have e2 : ∫ s in t₁..t, exp ((-s) • A) * W' * exp (s • A) * X = (t - t₁) • (W' * X) := by
      simp only [hint]
      rw [intervalIntegral.integral_const]
    rw [e1, e2, sub_add_cancel]
  have hlead : exp (t • A) * ((t - t₁) • (W' * X)) = (t - t₁) • (W' * exp (t • A) * X) := by
    rw [mul_smul_comm, ← mul_assoc, ← hc t]
  have hK2 : ‖∫ s in t₁..t, exp ((-s) • A) * (W - W') * exp (s • A) * X‖
      ≤ ∫ s in t₁..t, ‖(W - W') * exp (s • A) * X‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm h12).trans ?_
    refine intervalIntegral.integral_mono_on h12
      ((Matrix.continuous_duhamelIntegrand A (W - W') X).norm.intervalIntegrable _ _)
      ((Matrix.continuous_norm_mul_exp_smul_mul A (W - W') X).intervalIntegrable _ _)
      fun s _ => ?_
    calc ‖exp ((-s) • A) * (W - W') * exp (s • A) * X‖
        = ‖exp ((-s) • A) * ((W - W') * exp (s • A) * X)‖ := by simp only [mul_assoc]
      _ ≤ ‖exp ((-s) • A)‖ * ‖(W - W') * exp (s • A) * X‖ := norm_mul_le _ _
      _ = ‖(W - W') * exp (s • A) * X‖ := by
          rw [Matrix.l2_opNorm_exp_smul_skew A hA (-s), one_mul]
  have hK1 := Matrix.norm_duhamelKernel_le_integral A W X hA h1
  have hrew : Matrix.duhamelFirst A W X t - (t - t₁) • (W' * exp (t • A) * X)
      = exp (t • A) * (Matrix.duhamelKernel A W X t₁
        + ∫ s in t₁..t, exp ((-s) • A) * (W - W') * exp (s • A) * X) := by
    rw [Matrix.duhamelFirst, hsplit, hmid, ← hlead, ← mul_sub, ← add_assoc, add_sub_cancel_right]
  rw [hrew]
  refine (norm_mul_le _ _).trans ?_
  rw [Matrix.l2_opNorm_exp_smul_skew A hA t, one_mul]
  exact (norm_add_le _ _).trans (add_le_add hK1 hK2)

/-- ★★★ **Apart, then in contact: the first-order term.** `H₀` and `G` are Hermitian,
`G = S P` with `‖S‖ ≤ 1`, `‖P‖ ≤ 1`, `S` commutes with `H₀`, and `G − S = −S P'`. For a real
`g` and `0 ≤ t₁ ≤ t` the orbit of `X` under `H₀ + g G` is the free orbit plus
`−i g (t − t₁) · S e^{−itH₀} X`, within
`|g| ∫₀^{t₁} ‖P e^{−isH₀} X‖ + |g| ∫_{t₁}^{t} ‖P' e^{−isH₀} X‖`
`+ |g| (|g| ∫₀ᵗ ‖P e^{−isH₀} X‖) t`. -/
theorem norm_exp_sub_mul_sub_first_meeting_le (H₀ G S P P' X : Matrix m m ℂ) (g : ℝ)
    (hH₀ : H₀.IsHermitian) (hG : G.IsHermitian) (hSH : S * H₀ = H₀ * S) (hS1 : ‖S‖ ≤ 1)
    (hP1 : ‖P‖ ≤ 1) (hGP : G = S * P) (hGS : G - S = -(S * P')) {t₁ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G))) - exp (t • ((-Complex.I) • H₀))) * X
        - (-Complex.I * g * (t - t₁)) • (S * exp (t • ((-Complex.I) • H₀)) * X)‖
      ≤ |g| * (∫ s in (0 : ℝ)..t₁, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖)
        + |g| * (∫ s in t₁..t, ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖)
        + |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖) * t := by
  have ht : 0 ≤ t := h1.trans h12
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
  have hrem0 := Matrix.norm_exp_neg_I_add_sub_mul_sub_duhamelFirst_le_orbit H₀ ((g : ℂ) • G) X
    hH₀ hV ht
  have hB := norm_duhamelFirst_sub_meeting_le ((-Complex.I) • H₀)
    ((-Complex.I) • ((g : ℂ) • G)) ((-Complex.I) • ((g : ℂ) • S)) X hA hW'A h1 h12
  have hlead : (t - t₁) • ((-Complex.I) • ((g : ℂ) • S) * exp (t • ((-Complex.I) • H₀)) * X)
      = (-Complex.I * g * (t - t₁)) • (S * exp (t • ((-Complex.I) • H₀)) * X) := by
    rw [← Complex.coe_smul (t - t₁)]
    simp only [smul_mul_assoc, smul_smul]
    congr 1
    push_cast
    ring
  rw [hlead] at hB
  have hptG : ∀ s : ℝ, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ‖P * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [hGP]
    simp only [smul_mul_assoc, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)) (abs_nonneg g)
  have hptW : ∀ s : ℝ, ‖(-Complex.I) • ((g : ℂ) • G) * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ‖P * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    have e : ‖(-Complex.I) • ((g : ℂ) • G) * exp (s • ((-Complex.I) • H₀)) * X‖
        = ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖ := by
      rw [smul_mul_assoc, smul_mul_assoc, norm_smul, norm_neg, Complex.norm_I, one_mul]
    rw [e]
    exact hptG s
  have hptD : ∀ s : ℝ,
      ‖((-Complex.I) • ((g : ℂ) • G) - (-Complex.I) • ((g : ℂ) • S))
          * exp (s • ((-Complex.I) • H₀)) * X‖
        ≤ |g| * ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    rw [← smul_sub, ← smul_sub, hGS]
    simp only [smul_mul_assoc, neg_mul, norm_smul, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)) (abs_nonneg g)
  have hI0 : ∫ s in (0 : ℝ)..t₁,
        ‖(-Complex.I) • ((g : ℂ) • G) * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ∫ s in (0 : ℝ)..t₁, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on h1
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ P X)).intervalIntegrable _ _)
      fun s _ => hptW s
  have hI1 : ∫ s in t₁..t,
        ‖((-Complex.I) • ((g : ℂ) • G) - (-Complex.I) • ((g : ℂ) • S))
          * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ∫ s in t₁..t, ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on h12
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ P' X)).intervalIntegrable _ _)
      fun s _ => hptD s
  have hI2 : ∫ s in (0 : ℝ)..t, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ P X)).intervalIntegrable _ _)
      fun s _ => hptG s
  have hI2nn : 0 ≤ ∫ s in (0 : ℝ)..t, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖ :=
    intervalIntegral.integral_nonneg ht fun s _ => norm_nonneg _
  have hrem : ‖(g : ℂ) • G‖
        * (∫ s in (0 : ℝ)..t, ‖(g : ℂ) • G * exp (s • ((-Complex.I) • H₀)) * X‖) * t
      ≤ |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖) * t :=
    mul_le_mul_of_nonneg_right (mul_le_mul hVn hI2 hI2nn (abs_nonneg g)) ht
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G))) - exp (t • ((-Complex.I) • H₀))) * X)
    (Matrix.duhamelFirst ((-Complex.I) • H₀) ((-Complex.I) • ((g : ℂ) • G)) X t)
    ((-Complex.I * g * (t - t₁)) • (S * exp (t • ((-Complex.I) • H₀)) * X))
  linarith [htri, hrem0, hB, hI0, hI1, hrem]

end FirstOrder

/-! ### The transponder -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **Apart, then in contact, for the contact term of UA-19.** The transponder's level
swap commutes with its Hamiltonian. For a real `g`, any `X` and `0 ≤ t₁ ≤ t`, the orbit of
`X` is the free orbit plus `−i g (t − t₁)` times the level swap of the free orbit, within
the accumulated amplitude "in contact" up to `t₁`, the accumulated amplitude "apart" from
`t₁` to `t`, each times `|g|`, and a term of second order. -/
theorem transponder_first_order_meeting (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ) {t₁ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t) :
    ‖(exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X
        - (-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      ≤ |g| * (∫ s in (0 : ℝ)..t₁, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        + |g| * (∫ s in t₁..t, ‖coincProj σ τ (fun a b => ¬ r a b)
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
  exact norm_exp_sub_mul_sub_first_meeting_le _ _ _ _ _ X g
    (compositeH_isHermitian hM (blockDiagonal_isHermitian hT))
    (gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ)
    (one_kronecker_mul_compositeH M₀ hS) hS1 hP1 hGP hGS h1 h12

/-- ★★★ **The departure starts at the meeting.** Under the hypotheses of
`transponder_first_order_meeting`, the orbit of `X` departs from the free orbit by at least
`|g| (t − t₁) ‖X‖`, less `|g|` times the accumulated amplitude "in contact" up to `t₁`,
`|g|` times the accumulated amplitude "apart" from `t₁` to `t`, and the second-order
term. -/
theorem transponder_launch_meeting_ge (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ) {t₁ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t) :
    |g| * (t - t₁) * ‖X‖
        - |g| * (∫ s in (0 : ℝ)..t₁, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        - |g| * (∫ s in t₁..t, ‖coincProj σ τ (fun a b => ¬ r a b)
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        - |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) * t
      ≤ ‖(exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X‖ := by
  have hfirst := transponder_first_order_meeting σ τ r hτ hM hT hS g X h1 h12
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hA := Matrix.conjTranspose_neg_I_smul hH₀
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh hSS
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
  have hc : ‖(-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      = |g| * (t - t₁) * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
    have e : ‖(-Complex.I * g * ((t : ℂ) - (t₁ : ℂ)))‖ = |g| * (t - t₁) := by
      rw [← Complex.ofReal_sub, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 h12)]
    rw [norm_smul, e]
  have h2 := norm_sub_norm_le
    ((-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
      * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))
    ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n))))
        - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X)
  rw [norm_sub_rev, hc] at h2
  have h3 := mul_le_mul_of_nonneg_left hlead
    (mul_nonneg (abs_nonneg g) (sub_nonneg.2 h12))
  linarith

end Transponder

end CSD.RecordLayer

end
