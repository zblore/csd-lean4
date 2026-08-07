/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Oscillator
public import CsdLean4.CV.InteractionPrice
public import CsdLean4.CV.ModeLocality

/-!
# CV-10: finite-cutoff power counting — the price scales with operator grade

**Category:** CV (continuous variables — the multi-mode field).

The honest finite content of EFT power counting: grade an interaction by its
**operator content** (how many quadrature factors), and track how the CV-9
Duhamel price scales with the cutoff `N`:

* `annihilation_l2_opNorm_le` / `Q_l2_opNorm_le` — the norm-growth bricks:
  `‖a‖ ≤ √N` (via the C*-identity `‖a‖² = ‖a†a‖ = ‖N̂‖` — no spectral
  asymptotics) and `‖Q‖ ≤ √(2N)`.
* `l2_opNorm_modeOp_le` — embedding a single-mode operator into the field
  does not increase its norm (`modeOp` is block-diagonal over the
  spectator configurations).
* `gradedInteraction k m` — the grade-`m` interaction `Q_k^m` on the field
  (Hermitian), with `‖Q_k^m‖ ≤ √(2N)^m`.
* ★ `gradedInteraction_price_le` — the Duhamel price of the grade-`m`
  interaction is `≤ |τ|·|λ|·√(2N)^m`: **the certified price bound grows
  with the cutoff like `N^{m/2}`, exponent = the operator grade**.
* ★★ `gradedInteraction_renormalized_price_le` — with the coupling
  renormalized as `λ₀/√(2N)^m`, the price is `≤ |τ|·|λ₀|` — **uniform in
  the cutoff**. Cutoff-stability of a grade-`m` interaction's certified
  effect costs exactly the power `N^{-m/2}` of coupling: relevant /
  irrelevant as a theorem about the cutoff scaling of the price bound.

The contrast class needs no new theorem: a *bounded* potential (`|v| ≤ C`
with `C` cutoff-independent — any density coupling with bounded `g`) is
priced cutoff-uniformly at unrenormalized coupling by CV-9's
`interactingU_dist_le` directly.

⚠️ Norms are the scoped **`Matrix.Norms.L2Operator` (C*) norm** throughout.
Honest scope: these are upper bounds on the *certified price*, with no
lower bounds — so no claim that an unrenormalized coupling actually
diverges, and no claim the price is attained; "relevant/irrelevant" here
means scaling of the bound, not an RG statement, and nothing continuum is
asserted (`ApproxCCR.no_exact_finite_ccr` stands).

## References

`CV/Oscillator.lean` (`annihilation`, `creation`, `Q`,
`creation_mul_annihilation`); `CV/ModeLocality.lean` (`modeOp`);
`CV/InteractionPrice.lean` (CV-9, `freeField_perturbed_exp_dist_le`);
`specs/cv-stage3-plan.md` §3d; `specs/future-work.md` (row CV-10).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix NormedSpace

namespace CSD.CV

variable {K N : ℕ}

/-! ### Norm growth of the single-mode operators -/

/-- **The ladder-operator norm brick**: `‖a‖ ≤ √N`, by the C*-identity
`‖a‖² = ‖a†a‖ = ‖N̂‖` and the diagonal bound — no spectral asymptotics. -/
theorem annihilation_l2_opNorm_le : ‖annihilation N‖ ≤ Real.sqrt N := by
  have hnum : ‖numberOp N‖ ≤ (N : ℝ) := by
    rw [show numberOp N = Matrix.diagonal (fun i : Fin N => ((i : ℕ) : ℂ)) from rfl]
    exact Matrix.l2_opNorm_diagonal_le _ (Nat.cast_nonneg N) fun i => by
      rw [Complex.norm_natCast]
      exact_mod_cast le_of_lt i.isLt
  have hsq : ‖annihilation N‖ * ‖annihilation N‖ ≤ (N : ℝ) := by
    calc ‖annihilation N‖ * ‖annihilation N‖
        = ‖(annihilation N)ᴴ * annihilation N‖ :=
          (Matrix.l2_opNorm_conjTranspose_mul_self _).symm
      _ = ‖numberOp N‖ := by
          rw [show (annihilation N)ᴴ = creation N from rfl,
            creation_mul_annihilation]
      _ ≤ (N : ℝ) := hnum
  calc ‖annihilation N‖
      = Real.sqrt (‖annihilation N‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by rw [sq]; exact hsq)

/-- The creation operator has the same norm bound. -/
theorem creation_l2_opNorm_le : ‖creation N‖ ≤ Real.sqrt N := by
  rw [show creation N = (annihilation N)ᴴ from rfl,
    Matrix.l2_opNorm_conjTranspose]
  exact annihilation_l2_opNorm_le

/-- **The quadrature norm brick**: `‖Q‖ ≤ √(2N)`. -/
theorem Q_l2_opNorm_le : ‖Q N‖ ≤ Real.sqrt (2 * N) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnorm : ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc ‖Q N‖
      = ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (annihilation N + creation N)‖ := by
        rw [show Q N = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
          • (annihilation N + creation N) from rfl]
    _ = (Real.sqrt 2)⁻¹ * ‖annihilation N + creation N‖ := by
        rw [norm_smul, hnorm]
    _ ≤ (Real.sqrt 2)⁻¹ * (Real.sqrt N + Real.sqrt N) := by
        gcongr
        exact (norm_add_le _ _).trans
          (add_le_add annihilation_l2_opNorm_le creation_l2_opNorm_le)
    _ = Real.sqrt 2 * Real.sqrt N := by
        field_simp
        linear_combination (-(Real.sqrt N)) * h2
    _ = Real.sqrt (2 * N) := (Real.sqrt_mul (by norm_num) N).symm

/-! ### Embedding into the field does not grow the norm -/

/-- Split a configuration at mode `k`: the spectator assignment and the
`k`-occupation. -/
def modeSplit (k : Fin K) :
    FieldConfig K N ≃ ({j : Fin K // j ≠ k} → Fin N) × Fin N where
  toFun c := (fun j => c j.1, c k)
  invFun p := fun j => if h : j = k then p.2 else p.1 ⟨j, h⟩
  left_inv c := by
    funext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  right_inv p := by
    refine Prod.ext (funext fun j => ?_) ?_
    · simp [j.2]
    · simp

@[simp] lemma modeSplit_symm_apply_self (k : Fin K)
    (s : {j : Fin K // j ≠ k} → Fin N) (n : Fin N) :
    (modeSplit (N := N) k).symm (s, n) k = n := by
  simp [modeSplit]

lemma update_modeSplit_symm (k : Fin K)
    (s : {j : Fin K // j ≠ k} → Fin N) (n i : Fin N) :
    Function.update ((modeSplit (N := N) k).symm (s, n)) k i
      = (modeSplit k).symm (s, i) := by
  funext j
  by_cases h : j = k
  · subst h; simp [modeSplit]
  · simp [modeSplit, Function.update_apply, h]

/-- The field action of `modeOp` collapses to the single-mode action along
the `k`-fibre. -/
lemma modeOp_mulVec_apply (k : Fin K) (a : Matrix (Fin N) (Fin N) ℂ)
    (x : FieldConfig K N → ℂ) (c : FieldConfig K N) :
    (modeOp k a *ᵥ x) c = ∑ n, a (c k) n * x (Function.update c k n) := by
  classical
  show ∑ d, modeOp k a c d * x d = ∑ n, a (c k) n * x (Function.update c k n)
  have hinj : Function.Injective (Function.update c k) := fun n n' h => by
    have := congrFun h k
    simpa [Function.update_apply] using this
  have himg : ∑ d, modeOp k a c d * x d
      = ∑ d ∈ Finset.univ.image (Function.update c k),
          modeOp k a c d * x d := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro d _ hd
    rw [show modeOp k a c d
        = if (∀ j, j ≠ k → c j = d j) then a (c k) (d k) else 0 from rfl,
      if_neg, zero_mul]
    intro hall
    exact hd (Finset.mem_image.mpr ⟨d k, Finset.mem_univ _, funext fun j => by
      by_cases hj : j = k
      · subst hj; simp [Function.update_apply]
      · simp [Function.update_apply, hj, hall j hj]⟩)
  rw [himg, Finset.sum_image fun n _ n' _ h => hinj h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [modeOp_apply_of_agree k a fun j hj => by
      simp [Function.update_apply, hj]]
  congr 1
  simp [Function.update_apply]

/-- **Embedding a single-mode operator into the field does not increase its
norm**: `modeOp` is block-diagonal over the spectator configurations. -/
theorem l2_opNorm_modeOp_le (k : Fin K) (a : Matrix (Fin N) (Fin N) ℂ) :
    ‖modeOp k a‖ ≤ ‖a‖ := by
  classical
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => ?_
  have hval : ((Matrix.toEuclideanLin (𝕜 := ℂ)).trans
        LinearMap.toContinuousLinearMap (modeOp k a)) x
      = (EuclideanSpace.equiv (FieldConfig K N) ℂ).symm
          (modeOp k a *ᵥ x.ofLp) := rfl
  rw [hval]
  set y : ({j : Fin K // j ≠ k} → Fin N) → EuclideanSpace ℂ (Fin N) :=
    fun s => (EuclideanSpace.equiv (Fin N) ℂ).symm
      (fun n => x.ofLp ((modeSplit k).symm (s, n))) with hy
  have hsplit : ∀ f : FieldConfig K N → ℝ,
      (∑ c, f c) = ∑ s, ∑ n, f ((modeSplit (N := N) k).symm (s, n)) :=
    fun f =>
      ((Equiv.sum_comp (modeSplit (N := N) k).symm f).symm).trans
        (Fintype.sum_prod_type
          (f := fun p => f ((modeSplit (N := N) k).symm p)))
  have hcoord : ∀ (s : {j : Fin K // j ≠ k} → Fin N) (n : Fin N),
      (modeOp k a *ᵥ x.ofLp) ((modeSplit (N := N) k).symm (s, n))
        = (a *ᵥ (y s).ofLp) n := by
    intro s n
    rw [modeOp_mulVec_apply,
      show ((modeSplit (N := N) k).symm (s, n)) k = n from
        modeSplit_symm_apply_self k s n]
    show (∑ i, a n i * x.ofLp
        (Function.update ((modeSplit (N := N) k).symm (s, n)) k i))
      = ∑ i, a n i * (y s).ofLp i
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [update_modeSplit_symm]
    rfl
  have hy2 : ∀ s, ‖y s‖ ^ 2
      = ∑ n, ‖x.ofLp ((modeSplit (N := N) k).symm (s, n))‖ ^ 2 := by
    intro s
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun n _ => rfl
  have hx2 : ∑ s, ‖y s‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hsplit]
    exact Finset.sum_congr rfl fun s _ => hy2 s
  have hblock : ∀ s, (∑ n, ‖(a *ᵥ (y s).ofLp) n‖ ^ 2)
      ≤ (‖a‖ * ‖y s‖) ^ 2 := by
    intro s
    have hb : (∑ n, ‖(a *ᵥ (y s).ofLp) n‖ ^ 2)
        = ‖(EuclideanSpace.equiv (Fin N) ℂ).symm (a *ᵥ (y s).ofLp)‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun n _ => rfl
    rw [hb]
    exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec a (y s)) 2
  have hmain : ‖(EuclideanSpace.equiv (FieldConfig K N) ℂ).symm
        (modeOp k a *ᵥ x.ofLp)‖ ^ 2 ≤ (‖a‖ * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    calc (∑ c, ‖((EuclideanSpace.equiv (FieldConfig K N) ℂ).symm
            (modeOp k a *ᵥ x.ofLp)).ofLp c‖ ^ 2)
        = ∑ c, ‖(modeOp k a *ᵥ x.ofLp) c‖ ^ 2 :=
          Finset.sum_congr rfl fun c _ => rfl
      _ = ∑ s, ∑ n, ‖(modeOp k a *ᵥ x.ofLp)
            ((modeSplit (N := N) k).symm (s, n))‖ ^ 2 := hsplit _
      _ = ∑ s, ∑ n, ‖(a *ᵥ (y s).ofLp) n‖ ^ 2 :=
          Finset.sum_congr rfl fun s _ =>
            Finset.sum_congr rfl fun n _ => by rw [hcoord s n]
      _ ≤ ∑ s, (‖a‖ * ‖y s‖) ^ 2 := Finset.sum_le_sum fun s _ => hblock s
      _ = ‖a‖ ^ 2 * ∑ s, ‖y s‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = (‖a‖ * ‖x‖) ^ 2 := by rw [hx2]; ring
  calc ‖(EuclideanSpace.equiv (FieldConfig K N) ℂ).symm
        (modeOp k a *ᵥ x.ofLp)‖
      = Real.sqrt (‖(EuclideanSpace.equiv (FieldConfig K N) ℂ).symm
          (modeOp k a *ᵥ x.ofLp)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖a‖ * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hmain
    _ = ‖a‖ * ‖x‖ :=
        Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ### The graded interaction and its price -/

/-- `modeOp` commutes with the adjoint. -/
lemma modeOp_conjTranspose (k : Fin K) (a : Matrix (Fin N) (Fin N) ℂ) :
    (modeOp k a)ᴴ = modeOp k aᴴ := by
  ext c d
  rw [Matrix.conjTranspose_apply,
    show modeOp k a d c
      = if (∀ j, j ≠ k → d j = c j) then a (d k) (c k) else 0 from rfl,
    show modeOp k aᴴ c d
      = if (∀ j, j ≠ k → c j = d j) then aᴴ (c k) (d k) else 0 from rfl]
  by_cases h : ∀ j, j ≠ k → c j = d j
  · rw [if_pos h, if_pos fun j hj => (h j hj).symm,
      Matrix.conjTranspose_apply]
  · rw [if_neg h, if_neg (fun h' => h fun j hj => (h' j hj).symm), star_zero]

/-- **The grade-`m` interaction**: `Q_k^m` — `m` quadrature factors on mode
`k`, embedded in the field. -/
noncomputable def gradedInteraction (K : ℕ) {N : ℕ} (k : Fin K) (m : ℕ) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  modeOp k (Q N ^ m)

/-- The graded interaction is Hermitian. -/
theorem gradedInteraction_isHermitian (k : Fin K) (m : ℕ) :
    (gradedInteraction K (N := N) k m).IsHermitian := by
  rw [Matrix.IsHermitian, gradedInteraction, modeOp_conjTranspose,
    ((Q_isHermitian (N := N)).pow m).eq]

/-- The graded interaction's norm grows at most like `√(2N)^m` — exponent
= the operator grade. -/
theorem gradedInteraction_l2_opNorm_le (k : Fin K) {m : ℕ} (hm : 0 < m) :
    ‖gradedInteraction K (N := N) k m‖ ≤ Real.sqrt (2 * N) ^ m := by
  refine (l2_opNorm_modeOp_le k _).trans ?_
  refine (norm_pow_le' (Q N) hm).trans ?_
  exact pow_le_pow_left₀ (norm_nonneg _) Q_l2_opNorm_le m

/-- ★ **Power counting of the price**: the Duhamel price of the grade-`m`
interaction is `≤ |τ|·|λ|·√(2N)^m` — the certified bound grows with the
cutoff like `N^{m/2}`, exponent = the operator grade. -/
theorem gradedInteraction_price_le [NeZero N] (τ lam : ℝ) (k : Fin K)
    {m : ℕ} (hm : 0 < m) :
    ‖exp ((-(Complex.I * (τ : ℂ))) •
        (fieldHamiltonian K N + lam • gradedInteraction K k m))
      - (freeFieldU K N τ).val‖
      ≤ |τ| * (|lam| * Real.sqrt (2 * N) ^ m) := by
  refine le_trans
    (freeField_perturbed_exp_dist_le τ lam (gradedInteraction_isHermitian k m)) ?_
  gcongr
  exact gradedInteraction_l2_opNorm_le k hm

/-- ★★ **Renormalization by the grade**: with the coupling scaled as
`λ₀/√(2N)^m`, the price of the grade-`m` interaction is `≤ |τ|·|λ₀|` —
**uniform in the cutoff**. Cutoff-stability of the certified effect costs
exactly the power `N^{-m/2}` of coupling: relevant/irrelevant as a theorem
about the cutoff scaling of the price bound. -/
theorem gradedInteraction_renormalized_price_le [NeZero N] (τ lam₀ : ℝ)
    (k : Fin K) {m : ℕ} (hm : 0 < m) :
    ‖exp ((-(Complex.I * (τ : ℂ))) •
        (fieldHamiltonian K N
          + (lam₀ / Real.sqrt (2 * N) ^ m) • gradedInteraction K k m))
      - (freeFieldU K N τ).val‖
      ≤ |τ| * |lam₀| := by
  have hD : (0 : ℝ) < Real.sqrt (2 * N) ^ m := by
    have h1 : (0 : ℝ) < 2 * N := by
      have := Nat.pos_of_ne_zero (NeZero.ne N)
      positivity
    positivity
  refine le_trans (gradedInteraction_price_le τ _ k hm) ?_
  rw [abs_div, abs_of_nonneg (le_of_lt hD),
    div_mul_cancel₀ _ (ne_of_gt hD)]

end CSD.CV
