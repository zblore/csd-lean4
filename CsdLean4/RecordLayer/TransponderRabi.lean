/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderSecondLevel

/-!
# Beyond first order: the second level fills as `sin (g t)` while the carriers are in contact

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2), the caused return: a
signal does leave, with its weight).

The first-order statements of `RecordLayer/TransponderSecondLevel.lean` hold while `|g| t` is
small and give an amplitude of that size. Here the contact term with the gate removed is
solved exactly: the level swap `S` commutes with `H₀` and squares to one, so
`e^{−it(H₀ + gS)} = e^{−itH₀} (cos (gt) − i sin (gt) S)`. The gated term is then compared
with it, the difference being the amplitude of the orbit on configurations where the two
carriers are apart.

* ★★ `exp_smul_neg_I_smul_mulVec_of_invol`, `exp_smul_neg_I_smul_of_invol` — for `S² = 1`:
  `e^{−iθS} = cos θ − i sin θ · S`;
* `rabi_commute`, `norm_rabi_le_one` — that matrix commutes with what `S` commutes with, and
  has norm at most `1` for a Hermitian `S`;
* ★★ `exp_neg_I_add_smul_of_commute_invol` — `e^{−it(H₀ + gS)} = e^{−itH₀} (cos gt − i sin gt S)`;
* ★★★ `norm_exp_sub_rabi_mul_le` — for `G` with `G − S = −S P'`, `P'` commuting with `S`:
  the orbit of `X` under `H₀ + g G` is that product applied to `X`, within
  `|g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds`. **No second-order term.**
* `levelProj_one_mul_freeOrbit`, `levelProj_one_mul_swap_freeOrbit`,
  `norm_le_norm_swap_freeOrbit` — the level algebra along the free orbit;
* ★★★ `transponder_rabi_second_level_ge` — the contact term of UA-19, `X` with the transponder
  in its first level: the part with the transponder in its second level has norm at least
  `|sin (g t)| ‖X‖ − |g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds`;
* ★★★ `transponder_rabi_flatPacket_ge` — **the flat packet and a transponder at rest in its
  first level, wholly in contact up to `t`: the part of the state with the transponder in
  its second level has norm at least `|sin (g t)| − |g| √(flatTailD t) · t`.**

## Honest scope

⚠️ **Contact from the flow time `0`.** The error is `|g|` times the accumulated amplitude
"apart" over the whole of `[0, t]`; a run that starts apart is not treated here (the
first-order statement of UD-254 is).

⚠️ **The error grows like `|g| t`.** At `g t = π/2` it is `(π/2) √(tail)`: the second level
is shown nearly full only for a packet with a small tail that stays wholly in contact for
the time `π/(2|g|)`.

⚠️ **The two levels have the same Hamiltonian** (the level swap commutes with it).

⚠️ **The box condition is a hypothesis** in the packet statement; no instance with numbers.

⚠️ **The amplitude, not its place.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-211, UD-253, UD-256, UD-258); `specs/unified-records-spacetime-task-plans.md` (§9, items 2
and 4); `Mathlib/Analysis/Matrix/DuhamelState.lean` (`Matrix.norm_exp_neg_I_add_sub_mul_le`);
`RecordLayer/DiracArrival.lean` (`exp_mulVec_of_mulVec_eq_smul`);
`RecordLayer/TransponderSecondLevel.lean` (`levelProj_one_mul_levelSwap`,
`levelProj_zero_add_one`, `norm_one_kronecker_levelProj_le`);
`RecordLayer/TransponderMeetingPacket.lean`
(`norm_coincProj_freeOrbit_flatPacket_resting_le`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The exponential of an involution -/

section Involution

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- ★★ **The group of an involution, on a vector**: for `S² = 1`,
`e^{−iθS} v = cos θ · v − i sin θ · S v`. -/
theorem exp_smul_neg_I_smul_mulVec_of_invol {S : Matrix m m ℂ} (hSS : S * S = 1) (θ : ℝ)
    (v : m → ℂ) :
    exp (θ • ((-Complex.I) • S)) *ᵥ v
      = Complex.cos θ • v - (Complex.I * Complex.sin θ) • (S *ᵥ v) := by
  have hSSv : ∀ u : m → ℂ, S *ᵥ (S *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
  obtain ⟨vp, hvp⟩ : ∃ vp : m → ℂ, vp = (1 / 2 : ℂ) • (v + S *ᵥ v) := ⟨_, rfl⟩
  obtain ⟨vm, hvm⟩ : ∃ vm : m → ℂ, vm = (1 / 2 : ℂ) • (v - S *ᵥ v) := ⟨_, rfl⟩
  have hp : S *ᵥ vp = vp := by
    rw [hvp, Matrix.mulVec_smul, Matrix.mulVec_add, hSSv, add_comm]
  have hm : S *ᵥ vm = -vm := by
    rw [hvm, Matrix.mulVec_smul, Matrix.mulVec_sub, hSSv, ← smul_neg, neg_sub]
  have hAp : (θ • ((-Complex.I) • S)) *ᵥ vp = (-(Complex.I * θ)) • vp := by
    rw [← smul_assoc, Complex.real_smul, Matrix.smul_mulVec, hp]
    congr 1
    ring
  have hAm : (θ • ((-Complex.I) • S)) *ᵥ vm = (Complex.I * θ) • vm := by
    rw [← smul_assoc, Complex.real_smul, Matrix.smul_mulVec, hm, smul_neg, ← neg_smul]
    congr 1
    ring
  have hv : v = vp + vm := by
    rw [hvp, hvm]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hSv : S *ᵥ v = vp - vm := by
    rw [hvp, hvm]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e1 : Complex.exp (-(Complex.I * θ)) = Complex.cos θ - Complex.sin θ * Complex.I := by
    rw [show -(Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  have e2 : Complex.exp (Complex.I * θ) = Complex.cos θ + Complex.sin θ * Complex.I := by
    rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I]
  rw [hSv]
  calc exp (θ • ((-Complex.I) • S)) *ᵥ v
      = exp (θ • ((-Complex.I) • S)) *ᵥ (vp + vm) := by rw [← hv]
    _ = Complex.exp (-(Complex.I * θ)) • vp + Complex.exp (Complex.I * θ) • vm := by
        rw [Matrix.mulVec_add, exp_mulVec_of_mulVec_eq_smul hAp,
          exp_mulVec_of_mulVec_eq_smul hAm, ← Complex.exp_eq_exp_ℂ]
    _ = Complex.cos θ • v - (Complex.I * Complex.sin θ) • (vp - vm) := by
        rw [e1, e2]
        conv_rhs => rw [hv]
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring

/-- ★★ **The group of an involution**: for `S² = 1`, `e^{−iθS} = cos θ − i sin θ · S`. -/
theorem exp_smul_neg_I_smul_of_invol {S : Matrix m m ℂ} (hSS : S * S = 1) (θ : ℝ) :
    exp (θ • ((-Complex.I) • S))
      = Complex.cos θ • (1 : Matrix m m ℂ) - (Complex.I * Complex.sin θ) • S := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, exp_smul_neg_I_smul_mulVec_of_invol hSS,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- `cos θ − i sin θ · S` commutes with whatever `S` commutes with. -/
theorem rabi_commute {S M : Matrix m m ℂ} (h : M * S = S * M) (c d : ℂ) :
    M * (c • (1 : Matrix m m ℂ) - d • S) = (c • (1 : Matrix m m ℂ) - d • S) * M := by
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, h]

/-- For a Hermitian involution `S`, `cos θ − i sin θ · S` has norm at most `1`. -/
theorem norm_rabi_le_one [Nonempty m] {S : Matrix m m ℂ} (hSh : S.IsHermitian) (hSS : S * S = 1)
    (θ : ℝ) :
    ‖Complex.cos θ • (1 : Matrix m m ℂ) - (Complex.I * Complex.sin θ) • S‖ ≤ 1 := by
  rw [← exp_smul_neg_I_smul_of_invol hSS θ]
  exact (Matrix.l2_opNorm_exp_smul_skew _ (Matrix.conjTranspose_neg_I_smul hSh) θ).le

/-- ★★ **The contact term with the gate removed, solved.** For `S² = 1` commuting with `H₀`:
`e^{−it(H₀ + gS)} = e^{−itH₀} (cos (gt) − i sin (gt) S)`. -/
theorem exp_neg_I_add_smul_of_commute_invol {H₀ S : Matrix m m ℂ} (hSH : S * H₀ = H₀ * S)
    (hSS : S * S = 1) (g t : ℝ) :
    exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • S)))
      = exp (t • ((-Complex.I) • H₀))
        * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix m m ℂ)
          - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ)) • S) := by
  have e : t • ((-Complex.I) • (H₀ + (g : ℂ) • S))
      = t • ((-Complex.I) • H₀) + (g * t) • ((-Complex.I) • S) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have hc : Commute (t • ((-Complex.I) • H₀)) ((g * t) • ((-Complex.I) • S)) :=
    ((((show Commute H₀ S from hSH.symm).smul_left (-Complex.I)).smul_right
      (-Complex.I)).smul_left t).smul_right (g * t)
  rw [e, Matrix.exp_add_of_commute _ _ hc, exp_smul_neg_I_smul_of_invol hSS]

end Involution

/-! ### The gated term against the ungated one -/

section Compare

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- ★★★ **The gated contact term against the ungated one.** `H₀`, `G`, `S` are Hermitian,
`S² = 1`, `S` commutes with `H₀`; `G − S = −S P'` with `P'` commuting with `S`. For a real
`g` and `t ≥ 0` the orbit of `X` under `H₀ + g G` is
`e^{−itH₀} (cos (gt) − i sin (gt) S) X` within `|g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds`. -/
theorem norm_exp_sub_rabi_mul_le (H₀ G S P' X : Matrix m m ℂ) (g : ℝ)
    (hH₀ : H₀.IsHermitian) (hG : G.IsHermitian) (hSh : S.IsHermitian) (hSS : S * S = 1)
    (hSH : S * H₀ = H₀ * S) (hP'S : P' * S = S * P') (hGS : G - S = -(S * P')) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
        - exp (t • ((-Complex.I) • H₀))
          * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ)) • S)) * X‖
      ≤ |g| * ∫ s in (0 : ℝ)..t, ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := by
  have hS1 : ‖S‖ ≤ 1 := norm_le_one_of_isHermitian_invol hSh hSS
  have hsm : ∀ {M : Matrix m m ℂ}, M.IsHermitian → ((g : ℂ) • M).IsHermitian := fun {M} hM => by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hH' : (H₀ + (g : ℂ) • S).IsHermitian := hH₀.add (hsm hSh)
  have hV : ((g : ℂ) • (G - S)).IsHermitian := hsm (hG.sub hSh)
  have hsum : H₀ + (g : ℂ) • G = (H₀ + (g : ℂ) • S) + (g : ℂ) • (G - S) := by
    rw [smul_sub]
    abel
  have h := Matrix.norm_exp_neg_I_add_sub_mul_le (H₀ + (g : ℂ) • S) ((g : ℂ) • (G - S)) X hH'
    hV ht
  rw [← hsum, exp_neg_I_add_smul_of_commute_invol hSH hSS g t] at h
  refine h.trans ?_
  have hSA : S * ((-Complex.I) • H₀) = ((-Complex.I) • H₀) * S := by
    rw [mul_smul_comm, smul_mul_assoc, hSH]
  have hpt : ∀ s : ℝ,
      ‖(g : ℂ) • (G - S) * exp (s • ((-Complex.I) • (H₀ + (g : ℂ) • S))) * X‖
        ≤ |g| * ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := fun s => by
    have hSU := Matrix.mul_exp_smul_eq_of_commute hSA s
    have hMS : (P' * exp (s • ((-Complex.I) • H₀))) * S
        = S * (P' * exp (s • ((-Complex.I) • H₀))) := by
      rw [mul_assoc, ← hSU, ← mul_assoc, hP'S, mul_assoc]
    have hMR := rabi_commute hMS (Complex.cos ((g * s : ℝ) : ℂ))
      (Complex.I * Complex.sin ((g * s : ℝ) : ℂ))
    have e1 : S * P' * (exp (s • ((-Complex.I) • H₀))
          * (Complex.cos ((g * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((g * s : ℝ) : ℂ)) • S)) * X
        = S * ((Complex.cos ((g * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((g * s : ℝ) : ℂ)) • S)
          * (P' * exp (s • ((-Complex.I) • H₀)) * X)) := by
      calc S * P' * (exp (s • ((-Complex.I) • H₀))
            * (Complex.cos ((g * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
              - (Complex.I * Complex.sin ((g * s : ℝ) : ℂ)) • S)) * X
          = S * ((P' * exp (s • ((-Complex.I) • H₀)))
            * (Complex.cos ((g * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
              - (Complex.I * Complex.sin ((g * s : ℝ) : ℂ)) • S)) * X := by
            simp only [mul_assoc]
        _ = S * ((Complex.cos ((g * s : ℝ) : ℂ) • (1 : Matrix m m ℂ)
              - (Complex.I * Complex.sin ((g * s : ℝ) : ℂ)) • S)
            * (P' * exp (s • ((-Complex.I) • H₀)))) * X := by rw [hMR]
        _ = _ := by simp only [mul_assoc]
    rw [exp_neg_I_add_smul_of_commute_invol hSH hSS g s, hGS, smul_mul_assoc, smul_mul_assoc,
      neg_mul, neg_mul, e1, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg g)
    refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hS1).trans ?_)
    exact (norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_rabi_le_one hSh hSS (g * s)))
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on ht
    ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
    ((continuous_const.mul
      (Matrix.continuous_norm_mul_exp_smul_mul _ P' X)).intervalIntegrable _ _)
    fun s _ => hpt s

end Compare

/-! ### The transponder -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

omit [Nonempty ι] [Nonempty n] in
/-- The free orbit of a state in the first level stays in the first level. -/
theorem levelProj_one_mul_freeOrbit (M₀ : Matrix ι ι ℂ) (T : Fin 2 → Matrix n n ℂ)
    {X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ}
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) (t : ℝ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X = 0 := by
  rw [Matrix.mul_exp_smul_eq_of_commute
    (((show Commute ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        (compositeH M₀ (Matrix.blockDiagonal T)) from
      one_kronecker_mul_compositeH M₀ (levelProj_mul_blockDiagonal T 1)).smul_right
        (-Complex.I)).eq) t, mul_assoc, hX, mul_zero]

omit [Nonempty ι] [Nonempty n] in
/-- The level swap of the free orbit of a state in the first level is in the second. -/
theorem levelProj_one_mul_swap_freeOrbit (M₀ : Matrix ι ι ℂ) (T : Fin 2 → Matrix n n ℂ)
    {X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ}
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) (t : ℝ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X := by
  have hQS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, levelProj_one_mul_levelSwap]
  have hQ0X : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) * X = X := by
    have hsum : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) + ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        = 1 := by
      rw [← Matrix.kronecker_add, levelProj_zero_add_one, Matrix.one_kronecker_one]
    have := congrArg (· * X) hsum
    simp only [add_mul, hX, add_zero, one_mul] at this
    exact this
  have hcomm : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
      = exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) :=
    Matrix.mul_exp_smul_eq_of_commute
      (((show Commute ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0)
          (compositeH M₀ (Matrix.blockDiagonal T)) from
        one_kronecker_mul_compositeH M₀ (levelProj_mul_blockDiagonal T 0)).smul_right
          (-Complex.I)).eq) t
  calc ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X) := by
        simp only [mul_assoc]
    _ = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0)
            * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X := by
        rw [hQS]
        simp only [mul_assoc]
    _ = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
            * (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 0) * X)) := by
        rw [hcomm]
        simp only [mul_assoc]
    _ = _ := by rw [hQ0X, mul_assoc]

/-- The level swap of the free orbit is at least as large as the state. -/
theorem norm_le_norm_swap_freeOrbit {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ) (t : ℝ) :
    ‖X‖ ≤ ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
      * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
  have hA := Matrix.conjTranspose_neg_I_smul
    (compositeH_isHermitian hM (blockDiagonal_isHermitian hT))
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh hSS
  have hinv := Matrix.exp_smul_mul_exp_neg_smul
    ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)) (-t)
  rw [neg_neg] at hinv
  have hXeq : X = exp ((-t) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
      * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)) := by
    rw [← mul_assoc ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n), ← mul_assoc
      ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n), hSS, one_mul, ← mul_assoc, hinv, one_mul]
  calc ‖X‖ = ‖exp ((-t) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
        * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
            * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))‖ :=
        congrArg norm hXeq
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

/-- ★★★ **The second level fills as `sin (g t)` while the carriers are in contact.** The
transponder's level swap commutes with its Hamiltonian. For a real `g`, `X` with the
transponder in its first level and `t ≥ 0`, the part of the orbit of `X` with the
transponder in its second level has norm at least
`|sin (g t)| ‖X‖ − |g| ∫₀ᵗ ‖P' e^{−isH₀} X‖ ds`, `P'` the projector on the configurations
where the two carriers are apart. -/
theorem transponder_rabi_second_level_ge (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) {t : ℝ} (ht : 0 ≤ t) :
    |Real.sin (g * t)| * ‖X‖
        - |g| * (∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
      ≤ ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          * X‖ := by
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hSH := one_kronecker_mul_compositeH M₀ hS
  have hPS' := coincProj_mul_one_kronecker (ι := ι) σ τ (fun a b => ¬ r a b) hτ
  have hGS : gateOp σ τ r (levelSwap n) - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n
      = -(((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ (fun a b => ¬ r a b)) := by
    rw [← hPS', ← one_sub_coincProj σ τ r, gateOp, sub_mul, one_mul, neg_sub]
  have hcmp := norm_exp_sub_rabi_mul_le _ _ _ _ X g hH₀
    (gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ) hSh hSS hSH hPS' hGS ht
  have hQ1 := norm_one_kronecker_levelProj_le (n := n) ι 1
  have hSA : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))
      = ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) := by
    rw [mul_smul_comm, smul_mul_assoc, hSH]
  have hSU := Matrix.mul_exp_smul_eq_of_commute hSA t
  -- the second-level part of the ungated orbit
  have hmain : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
          * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
            - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ)) • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))
          * X)
      = -((Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
        • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)) := by
    have e : exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
          * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
            - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ)) • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))
          * X
        = Complex.cos ((g * t : ℝ) : ℂ)
            • (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)
          - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
            • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
              * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X) := by
      rw [mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, mul_one, smul_mul_assoc,
        smul_mul_assoc, hSU]
    rw [e, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc,
      levelProj_one_mul_freeOrbit M₀ T hX t, smul_zero, zero_sub,
      levelProj_one_mul_swap_freeOrbit M₀ T hX t]
  have hsplit : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n)))) * X
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
              + (g : ℂ) • gateOp σ τ r (levelSwap n))))
            - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
              * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
                - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
                  • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))) * X)
        - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
          • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
            * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X) := by
    rw [sub_mul, mul_sub, hmain, sub_neg_eq_add, add_sub_cancel_right, mul_assoc]
  have hQD := (norm_mul_le ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
    ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
        + (g : ℂ) • gateOp σ τ r (levelSwap n))))
      - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
        * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
          - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
            • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))) * X)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hQ1)
  have hc : ‖(Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
        • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      = |Real.sin (g * t)| * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
    rw [norm_smul, ← Complex.ofReal_sin, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have htri := norm_sub_norm_le
    ((Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
      • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))
    (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n))))
        - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
          * (Complex.cos ((g * t : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
            - (Complex.I * Complex.sin ((g * t : ℝ) : ℂ))
              • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))) * X))
  rw [norm_sub_rev, ← hsplit, hc] at htri
  have h3 := mul_le_mul_of_nonneg_left (norm_le_norm_swap_freeOrbit hM hT X t)
    (abs_nonneg (Real.sin (g * t)))
  linarith

end Transponder

/-! ### The packet -/

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **The flat packet in contact with a transponder at rest.** The messenger is the flat
packet of the lattice Dirac field of any dimension; the transponder is at rest with one
energy for both levels, in a state of norm `1` in its first level, supported on the sites
`B`. If up to the flow time `t` every site of the packet's moving box is related to every
site of `B`, the part of the state at `t` with the transponder in its second level has norm
at least `|sin (g t)| − |g| √(flatTailD t) · t`. -/
theorem transponder_rabi_flatPacket_ge (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E g : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    (hφn : ∑ q, ‖φ q‖ ^ 2 = 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t : ℝ} (ht : 0 ≤ t)
    (hcon : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      r a b) :
    |Real.sin (g * t)| - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * t)
      ≤ Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
            ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I)
            • (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
        *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2) := by
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  obtain ⟨hstar, hX1⟩ := norm_vecMulVec_star_of_sum_eq_one hΨ1
  have hT : ∀ l : Fin 2, (((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hM := latticeDiracHam_isHermitian (L := L) h J μ
  have hΨ0 : ((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1)
      *ᵥ (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) = 0 := by
    rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal]
    funext y
    rw [Matrix.mulVec_diagonal]
    by_cases hy : y.2.2 = 1
    · simp [hφ y.2 hy]
    · simp [hy]
  have hX0 : ((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1)
      * Matrix.vecMulVec
        (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
        (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) = 0 := by
    rw [Matrix.mul_vecMulVec, hΨ0]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have key := transponder_rabi_second_level_ge
    (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r hτ
    hM hT (levelSwap_mul_blockDiagonal_smul_one E) g
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)) hX0 ht
  rw [norm_mul_vecMulVec, hstar, mul_one, hX1, mul_one] at key
  have hP' : ∀ s, 0 ≤ s → s ≤ t → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t) :=
    fun s hs hst => (norm_coincProj_freeOrbit_flatPacket_resting_le τ (fun a b => ¬ r a b) h
      he hn hμ E lo hN hNL k₀ hw0 hw hγ φ hφn B hφB hs
      (fun a ha b hb => not_not.2 (hcon s hs hst a ha b hb))).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hst))
  have hcont' := Matrix.continuous_norm_mul_exp_smul_mul
    ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
      (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    (coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ (fun a b => ¬ r a b))
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2))
  have hIc := intervalIntegral.integral_mono_on ht (hcont'.intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t))) fun s hs => hP' s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at hIc
  have e2 := mul_le_mul_of_nonneg_left hIc (abs_nonneg g)
  linarith [key, e2]

end Packet

end CSD.RecordLayer

end
