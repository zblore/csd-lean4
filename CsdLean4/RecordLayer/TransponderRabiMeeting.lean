/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderRabi

/-!
# Apart, then in contact, beyond first order: the second level fills from the meeting

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, items (1) and (2) in one run, the
caused return, beyond first order).

`RecordLayer/TransponderRabi.lean` compares the gated contact term with the ungated one for
carriers in contact from the flow time `0`. Here the run has two parts: up to `t₁` it is
compared with the free orbit, and from `t₁` with the ungated term. The reference orbit is
free up to `t₁` and turns by `cos (g (t − t₁)) − i sin (g (t − t₁)) S` after.

* ★★★ `norm_exp_sub_rabi_meeting_mul_le` — for `G = S P`, `G − S = −S P'`, `0 ≤ t₁ ≤ t`: the
  orbit of `X` under `H₀ + g G` is `e^{−itH₀} (cos (g (t − t₁)) − i sin (g (t − t₁)) S) X`
  within `|g| ∫₀^{t₁} ‖P e^{−isH₀} X‖ + |g| ∫_{t₁}^{t} ‖P' e^{−isH₀} X‖`. **No second-order
  term.**
* `levelProj_one_mul_rabi_freeOrbit` — the second-level part of that reference orbit;
* ★★★ `transponder_rabi_meeting_second_level_ge` — the contact term of UA-19, `X` with the
  transponder in its first level: the part in the second level has norm at least
  `|sin (g (t − t₁))| ‖X‖` less those two terms;
* ★★★ `transponder_rabi_flatPacket_meeting_ge` — **the flat packet and a transponder at rest
  in its first level; the moving box apart from the transponder's sites up to `t₁` and
  wholly in contact from `t₂`: the second level's amplitude at `t` is at least**

  `|sin (g (t − t₂))| − |g| (√ε₁ t₁ + (t₂ − t₁)) − |g| √ε (t − t₂)`,

  `ε₁ = flatTailD t₁`, `ε = flatTailD t`.

## Honest scope

⚠️ **The error is linear in `|g|` times the times involved.** It has no term of second order
in `g`, but `|g| (t₂ − t₁)`, the whole time of partial contact, is subtracted. For the
instance of UD-257 that time is three quarters of the dwell, and the bound stays small: by
hand, at most about `0.02`. An order-one amplitude needs a geometry in which the dwell is
long against the time of partial contact; none is exhibited.

⚠️ **The two box conditions are hypotheses.**

⚠️ **The two levels have the same Hamiltonian.**

⚠️ **The amplitude, not its place.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-254, UD-256, UD-258, UD-259); `RecordLayer/TransponderRabi.lean`
(`norm_exp_sub_rabi_mul_le`, `rabi_commute`, `levelProj_one_mul_freeOrbit`,
`levelProj_one_mul_swap_freeOrbit`, `norm_le_norm_swap_freeOrbit`);
`Mathlib/Analysis/Matrix/DuhamelState.lean` (`Matrix.norm_exp_neg_I_add_sub_mul_le`);
`RecordLayer/TransponderMeetingPacket.lean`
(`norm_coincProj_freeOrbit_flatPacket_resting_le`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The comparison over a run in two parts -/

section Compare

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

omit [Nonempty m] in
/-- The group at a sum of times. -/
theorem exp_add_smul_eq_mul (B : Matrix m m ℂ) (a b : ℝ) :
    exp ((a + b) • B) = exp (a • B) * exp (b • B) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl B).smul_left a).smul_right b)]

/-- ★★★ **Apart, then in contact, beyond first order.** `H₀`, `G`, `S` are Hermitian,
`S² = 1`, `S` commutes with `H₀`; `G = S P` with `‖P‖ ≤ 1`, and `G − S = −S P'` with `P'`
commuting with `S`. For a real `g` and `0 ≤ t₁ ≤ t` the orbit of `X` under `H₀ + g G` is
`e^{−itH₀} (cos (g (t − t₁)) − i sin (g (t − t₁)) S) X`, within
`|g| ∫₀^{t₁} ‖P e^{−isH₀} X‖ ds + |g| ∫_{t₁}^{t} ‖P' e^{−isH₀} X‖ ds`. -/
theorem norm_exp_sub_rabi_meeting_mul_le (H₀ G S P P' X : Matrix m m ℂ) (g : ℝ)
    (hH₀ : H₀.IsHermitian) (hG : G.IsHermitian) (hSh : S.IsHermitian) (hSS : S * S = 1)
    (hSH : S * H₀ = H₀ * S) (hGP : G = S * P) (hP'S : P' * S = S * P')
    (hGS : G - S = -(S * P')) {t₁ t : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t) :
    ‖(exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
        - exp (t • ((-Complex.I) • H₀))
          * (Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ)) • S)) * X‖
      ≤ |g| * (∫ s in (0 : ℝ)..t₁, ‖P * exp (s • ((-Complex.I) • H₀)) * X‖)
        + |g| * ∫ s in t₁..t, ‖P' * exp (s • ((-Complex.I) • H₀)) * X‖ := by
  have hτ : 0 ≤ t - t₁ := sub_nonneg.2 h12
  have hS1 : ‖S‖ ≤ 1 := norm_le_one_of_isHermitian_invol hSh hSS
  have hV : ((g : ℂ) • G).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hG.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hB := Matrix.conjTranspose_neg_I_smul (hH₀.add hV)
  have hSA : S * ((-Complex.I) • H₀) = ((-Complex.I) • H₀) * S := by
    rw [mul_smul_comm, smul_mul_assoc, hSH]
  have hSU := Matrix.mul_exp_smul_eq_of_commute hSA t₁
  have hRU := rabi_commute hSU.symm (Complex.cos ((g * (t - t₁) : ℝ) : ℂ))
    (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
  have hBs : exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
      = exp ((t - t₁) • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
        * exp (t₁ • ((-Complex.I) • (H₀ + (g : ℂ) • G))) := by
    rw [← exp_add_smul_eq_mul, sub_add_cancel]
  have hAs : exp (t • ((-Complex.I) • H₀))
      = exp ((t - t₁) • ((-Complex.I) • H₀)) * exp (t₁ • ((-Complex.I) • H₀)) := by
    rw [← exp_add_smul_eq_mul, sub_add_cancel]
  have hdec : (exp (t • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
        - exp (t • ((-Complex.I) • H₀))
          * (Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix m m ℂ)
            - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ)) • S)) * X
      = exp ((t - t₁) • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
          * ((exp (t₁ • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
            - exp (t₁ • ((-Complex.I) • H₀))) * X)
        + (exp ((t - t₁) • ((-Complex.I) • (H₀ + (g : ℂ) • G)))
            - exp ((t - t₁) • ((-Complex.I) • H₀))
              * (Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix m m ℂ)
                - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ)) • S))
          * (exp (t₁ • ((-Complex.I) • H₀)) * X) := by
    rw [hBs, hAs, mul_assoc (exp ((t - t₁) • ((-Complex.I) • H₀))), hRU]
    generalize Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix m m ℂ)
      - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ)) • S = Rm
    noncomm_ring
  rw [hdec]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_exp_smul_skew _ hB (t - t₁), one_mul]
    refine (Matrix.norm_exp_neg_I_add_sub_mul_le H₀ ((g : ℂ) • G) X hH₀ hV h1).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h1
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ X).intervalIntegrable _ _)
      ((continuous_const.mul
        (Matrix.continuous_norm_mul_exp_smul_mul _ P X)).intervalIntegrable _ _)
      fun s _ => ?_
    rw [hGP]
    simp only [smul_mul_assoc, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hS1)) (abs_nonneg g)
  · refine (norm_exp_sub_rabi_mul_le H₀ G S P' (exp (t₁ • ((-Complex.I) • H₀)) * X) g hH₀ hG
      hSh hSS hSH hP'S hGS hτ).trans (le_of_eq ?_)
    congr 1
    have hint : ∀ s : ℝ, P' * exp (s • ((-Complex.I) • H₀))
          * (exp (t₁ • ((-Complex.I) • H₀)) * X)
        = P' * exp ((s + t₁) • ((-Complex.I) • H₀)) * X := fun s => by
      rw [exp_add_smul_eq_mul]
      simp only [mul_assoc]
    simp only [hint]
    rw [intervalIntegral.integral_comp_add_right
      (fun u : ℝ => ‖P' * exp (u • ((-Complex.I) • H₀)) * X‖) t₁, zero_add, sub_add_cancel]

end Compare

/-! ### The transponder -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

omit [Nonempty ι] [Nonempty n] in
/-- The second-level part of `e^{−itH₀} (c − d S) X`, for `X` in the first level, is
`−d S e^{−itH₀} X`. -/
theorem levelProj_one_mul_rabi_freeOrbit (M₀ : Matrix ι ι ℂ) {T : Fin 2 → Matrix n n ℂ}
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    {X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ}
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) (t : ℝ) (c d : ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
          * (c • (1 : Matrix _ _ ℂ) - d • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)) * X)
      = -(d • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)) := by
  have hSA : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))
      = ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) := by
    rw [mul_smul_comm, smul_mul_assoc, one_kronecker_mul_compositeH M₀ hS]
  have hSU := Matrix.mul_exp_smul_eq_of_commute hSA t
  have e : exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
        * (c • (1 : Matrix _ _ ℂ) - d • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)) * X
      = c • (exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)
        - d • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X) := by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, mul_one, smul_mul_assoc,
      smul_mul_assoc, hSU]
  rw [e, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc,
    levelProj_one_mul_freeOrbit M₀ T hX t, smul_zero, zero_sub,
    levelProj_one_mul_swap_freeOrbit M₀ T hX t]

/-- ★★★ **The second level fills from the meeting.** The transponder's level swap commutes
with its Hamiltonian. For a real `g`, `X` with the transponder in its first level and
`0 ≤ t₁ ≤ t`, the part of the orbit of `X` with the transponder in its second level has norm
at least `|sin (g (t − t₁))| ‖X‖`, less `|g|` times the accumulated amplitude "in contact"
up to `t₁` and `|g|` times the accumulated amplitude "apart" from `t₁` to `t`. -/
theorem transponder_rabi_meeting_second_level_ge (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) {t₁ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t) :
    |Real.sin (g * (t - t₁))| * ‖X‖
        - |g| * (∫ s in (0 : ℝ)..t₁, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        - |g| * (∫ s in t₁..t, ‖coincProj σ τ (fun a b => ¬ r a b)
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
  have hPS := coincProj_mul_one_kronecker (ι := ι) σ τ r hτ
  have hPS' := coincProj_mul_one_kronecker (ι := ι) σ τ (fun a b => ¬ r a b) hτ
  have hGP : gateOp σ τ r (levelSwap n)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ r := by
    rw [gateOp, hPS]
  have hGS : gateOp σ τ r (levelSwap n) - (1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n
      = -(((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * coincProj σ τ (fun a b => ¬ r a b)) := by
    rw [← hPS', ← one_sub_coincProj σ τ r, gateOp, sub_mul, one_mul, neg_sub]
  have hcmp := norm_exp_sub_rabi_meeting_mul_le _ _ _ _ _ X g hH₀
    (gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ) hSh hSS hSH hGP hPS' hGS h1 h12
  have hQ1 := norm_one_kronecker_levelProj_le (n := n) ι 1
  have hmain := levelProj_one_mul_rabi_freeOrbit M₀ hS hX t
    (Complex.cos ((g * (t - t₁) : ℝ) : ℂ)) (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
  have hsplit : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n)))) * X
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
              + (g : ℂ) • gateOp σ τ r (levelSwap n))))
            - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
              * (Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
                - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
                  • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))) * X)
        - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
          • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
            * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X) := by
    rw [sub_mul, mul_sub, hmain, sub_neg_eq_add, add_sub_cancel_right, mul_assoc]
  have hQD := (norm_mul_le ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
    ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
        + (g : ℂ) • gateOp σ τ r (levelSwap n))))
      - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
        * (Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
          - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
            • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))) * X)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hQ1)
  have hc : ‖(Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
        • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      = |Real.sin (g * (t - t₁))| * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
    rw [norm_smul, ← Complex.ofReal_sin, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have htri := norm_sub_norm_le
    ((Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
      • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))
    (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n))))
        - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
          * (Complex.cos ((g * (t - t₁) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)
            - (Complex.I * Complex.sin ((g * (t - t₁) : ℝ) : ℂ))
              • ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n))) * X))
  rw [norm_sub_rev, ← hsplit, hc] at htri
  have h3 := mul_le_mul_of_nonneg_left (norm_le_norm_swap_freeOrbit hM hT X t)
    (abs_nonneg (Real.sin (g * (t - t₁))))
  linarith

end Transponder

/-! ### The packet -/

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **The second level fills from the time the packet's box reaches the transponder,
beyond first order.** The messenger is the flat packet of the lattice Dirac field of any
dimension; the transponder is at rest with one energy for both levels, in a state of norm
`1` in its first level, supported on the sites `B`. For `0 ≤ t₁ ≤ t₂ ≤ t`: if no site of the
packet's moving box is related to a site of `B` up to `t₁`, and every site of it is related
to every site of `B` from `t₂` to `t`, then the part of the state at `t` with the
transponder in its second level has norm at least

`|sin (g (t − t₂))| − |g| (√ε₁ t₁ + (t₂ − t₁)) − |g| √ε (t − t₂)`,

`ε₁ = flatTailD t₁`, `ε = flatTailD t`. -/
theorem transponder_rabi_flatPacket_meeting_ge (τ : n × Fin 2 → κ → ZMod L)
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
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t₁ t₂ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (h2t : t₂ ≤ t)
    (hsep : ∀ s, 0 ≤ s → s ≤ t₁ → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b)
    (hcon : ∀ s, t₂ ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      r a b) :
    |Real.sin (g * (t - t₂))|
        - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁))
        - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * (t - t₂))
      ≤ Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
            ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I)
            • (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
        *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2) := by
  have ht2 : 0 ≤ t₂ := h1.trans h12
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  obtain ⟨hstar, hX1⟩ := norm_vecMulVec_star_of_sum_eq_one hΨ1
  have hT : ∀ l : Fin 2, (((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hM := latticeDiracHam_isHermitian (L := L) h J μ
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hA := Matrix.conjTranspose_neg_I_smul hH₀
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
  have key := transponder_rabi_meeting_second_level_ge
    (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r hτ
    hM hT (levelSwap_mul_blockDiagonal_smul_one E) g
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)) hX0 ht2 h2t
  rw [norm_mul_vecMulVec, hstar, mul_one, hX1, mul_one] at key
  have hP : ∀ s, 0 ≤ s → s ≤ t₁ → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) :=
    fun s hs hs1 => (norm_coincProj_freeOrbit_flatPacket_resting_le τ r h he hn hμ E lo hN hNL
      k₀ hw0 hw hγ φ hφn B hφB hs (hsep s hs hs1)).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hs1))
  have hP' : ∀ s, t₂ ≤ s → s ≤ t → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t) :=
    fun s hs hst => (norm_coincProj_freeOrbit_flatPacket_resting_le τ (fun a b => ¬ r a b) h
      he hn hμ E lo hN hNL k₀ hw0 hw hγ φ hφn B hφB (ht2.trans hs)
      (fun a ha b hb => not_not.2 (hcon s hs hst a ha b hb))).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hst))
  have hP1 : ‖coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r‖ ≤ 1 := by
    rw [coincProj]
    exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp
  have hcrude : ∀ s : ℝ, ‖coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r
      * exp (s • ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
          (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
      * Matrix.vecMulVec
        (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
        (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)‖ ≤ 1 := fun s => by
    refine (norm_mul_le _ _).trans ?_
    rw [hX1, mul_one]
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_exp_smul_skew _ hA s, mul_one]
    exact hP1
  have hcont := Matrix.continuous_norm_mul_exp_smul_mul
    ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
      (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    (coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r)
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2))
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
  have hIa := intervalIntegral.integral_mono_on h1 (hcont.intervalIntegrable 0 t₁)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t₁))) fun s hs => hP s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hIa
  have hIb := intervalIntegral.integral_mono_on h12 (hcont.intervalIntegrable t₁ t₂)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s _ => hcrude s
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hIb
  have hI1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 t₁) (hcont.intervalIntegrable t₁ t₂)).symm
  have hIc := intervalIntegral.integral_mono_on h2t (hcont'.intervalIntegrable t₂ t)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t))) fun s hs => hP' s hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hIc
  have hg := abs_nonneg g
  have e1 := mul_le_mul_of_nonneg_left (by linarith [hI1, hIa, hIb] :
    (∫ s in (0 : ℝ)..t₂, _) ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁)) hg
  have e2 := mul_le_mul_of_nonneg_left hIc hg
  linarith [key, e1, e2]

end Packet

end CSD.RecordLayer

end
