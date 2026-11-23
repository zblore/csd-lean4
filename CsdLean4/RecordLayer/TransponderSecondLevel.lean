/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderMeetingPacket

/-!
# What leaves is in the transponder's second level

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2), the caused return: a
signal does leave, with its weight).

`transponder_launch_meeting_ge` and `transponder_launch_flatPacket_meeting_ge` bound below
the departure of the orbit from the free orbit. Here the transponder starts in its first
level and the bound is for the part of the state with the transponder in its second level:
the quantity `transponder_launch_le_coincidence` bounds above.

* `levelProj_one_mul_levelSwap`, `levelProj_zero_add_one` — the level swap carries the first
  level to the second; the two level projectors add to the identity;
* `norm_one_kronecker_levelProj_le` — the projector on a level has norm at most `1`;
* ★★★ `transponder_second_level_meeting_ge` — for `X` with the transponder in its first level
  and `0 ≤ t₁ ≤ t`: the part of the orbit with the transponder in its second level has norm
  at least `|g| (t − t₁) ‖X‖` less the three terms of UD-254;
* ★★★ `transponder_second_level_flatPacket_meeting_ge` — **for the flat packet and a
  transponder at rest in its first level: with the moving box apart from the transponder's
  sites up to `t₁` and wholly in contact from `t₂`, the part of the state with the
  transponder in its second level at `t` has norm at least the bound of UD-255.**

With `transponder_launch_flatPacket_resting_le` (UD-252) the second level's amplitude is
bounded on both sides: at most `|g| √(flatTailD t) · t` before the box reaches the
transponder, at least `|g| (t − t₂)` less errors after.

## Honest scope

⚠️ **First order.** The last error term is of order `g² t²`: the lower bound is positive only
while `|g| t` is small against `(t − t₂)/t`. The second level is not shown to fill.

⚠️ **The two box conditions are hypotheses**, and the time `t₂ − t₁` of partial contact is
counted in full as error. No relation, sites and times in numbers.

⚠️ **The transponder is at rest with one energy for both levels** in the packet statement;
in the matrix statement its level swap commutes with its Hamiltonian.

⚠️ **The amplitude in the second level, not where it is.** Its place and its later motion
(item (3) of the task plan's §9) are not treated. No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-226, UD-252, UD-254, UD-255, UD-256); `RecordLayer/TransponderMeeting.lean`
(`transponder_first_order_meeting`); `RecordLayer/TransponderMeetingPacket.lean`
(`norm_coincProj_freeOrbit_flatPacket_resting_le`, `sum_norm_sq_flatPacketD`);
`RecordLayer/UnifiedTransponder.lean` (`levelProj`, `levelProj_mul_blockDiagonal`,
`one_kronecker_mul_compositeH`); `Mathlib/Analysis/Matrix/DuhamelSector.lean`
(`Matrix.mul_exp_smul_eq_of_commute`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The levels -/

section Levels

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The level swap carries the first level to the second. -/
theorem levelProj_one_mul_levelSwap :
    levelProj n 1 * levelSwap n = levelSwap n * levelProj n 0 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [levelProj, levelSwap, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp

omit [Fintype n] in
/-- The two level projectors add to the identity. -/
theorem levelProj_zero_add_one : levelProj n 0 + levelProj n 1 = 1 := by
  rw [levelProj, levelProj, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext x
  obtain ⟨a, i⟩ := x
  fin_cases i <;> simp

/-- The projector on a level, on the composite, has norm at most `1`. -/
theorem norm_one_kronecker_levelProj_le (ι : Type*) [Fintype ι] [DecidableEq ι] (l : Fin 2) :
    ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal]
  exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp

end Levels

/-! ### The second level -/

section Transponder

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **What leaves is in the second level.** Under the hypotheses of
`transponder_first_order_meeting`, for `X` with the transponder in its first level: the part
of the orbit of `X` with the transponder in its second level has norm at least
`|g| (t − t₁) ‖X‖`, less `|g|` times the accumulated amplitude "in contact" up to `t₁`, `|g|`
times the accumulated amplitude "apart" from `t₁` to `t`, and the second-order term. -/
theorem transponder_second_level_meeting_ge (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hS : levelSwap n * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelSwap n)
    (g : ℝ) (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) {t₁ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t) :
    |g| * (t - t₁) * ‖X‖
        - |g| * (∫ s in (0 : ℝ)..t₁, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        - |g| * (∫ s in t₁..t, ‖coincProj σ τ (fun a b => ¬ r a b)
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖)
        - |g| * (|g| * ∫ s in (0 : ℝ)..t, ‖coincProj σ τ r
            * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) * t
      ≤ ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          * X‖ := by
  have hfirst := transponder_first_order_meeting σ τ r hτ hM hT hS g X h1 h12
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hA := Matrix.conjTranspose_neg_I_smul hH₀
  have hSh : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n).IsHermitian :=
    CSD.CV.kronecker_isHermitian Matrix.isHermitian_one (levelSwap_isHermitian n)
  have hSS : ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, levelSwap_mul_self, Matrix.one_kronecker_one]
  have hS1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n‖ ≤ 1 :=
    norm_le_one_of_isHermitian_invol hSh hSS
  have hQ1 := norm_one_kronecker_levelProj_le (n := n) ι 1
  -- the level algebra
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
  have hcomm : ∀ l : Fin 2, ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
      = exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l) := fun l =>
    Matrix.mul_exp_smul_eq_of_commute
      (((show Commute ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l)
          (compositeH M₀ (Matrix.blockDiagonal T)) from
        one_kronecker_mul_compositeH M₀ (levelProj_mul_blockDiagonal T l)).smul_right
          (-Complex.I)).eq) t
  have hQSUX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X := by
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
          rw [hcomm 0]
          simp only [mul_assoc]
      _ = _ := by rw [hQ0X, mul_assoc]
  have hQU0 : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X = 0 := by
    rw [hcomm 1, mul_assoc, hX, mul_zero]
  -- the second-level part of the orbit is the second-level part of the departure
  have hdec : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
              + (g : ℂ) • gateOp σ τ r (levelSwap n))))
            - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X
          - (-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
            * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))
        + (-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
            * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          * X := by
    rw [mul_sub, mul_smul_comm, hQSUX, sub_add_cancel, sub_mul, mul_sub, ← mul_assoc,
      ← mul_assoc, hQU0, sub_zero]
  -- the leading term has the size of `X`
  have hinv := Matrix.exp_smul_mul_exp_neg_smul
    ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)) (-t)
  rw [neg_neg] at hinv
  have hXeq : X = exp ((-t) • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))
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
  have hc : ‖(-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X)‖
      = |g| * (t - t₁) * ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖ := by
    have e : ‖(-Complex.I * g * ((t : ℂ) - (t₁ : ℂ)))‖ = |g| * (t - t₁) := by
      rw [← Complex.ofReal_sub, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 h12)]
    rw [norm_smul, e]
  have hQR := (norm_mul_le ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
    ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
          + (g : ℂ) • gateOp σ τ r (levelSwap n))))
        - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X
      - (-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
        * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))).trans
    (mul_le_of_le_one_left (norm_nonneg _) hQ1)
  have htri := norm_add_le
    (((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
        + (g : ℂ) • gateOp σ τ r (levelSwap n))))
      * X)
    (-(((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      * ((exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) * X
        - (-Complex.I * g * (t - t₁)) • (((1 : Matrix ι ι ℂ) ⊗ₖ levelSwap n)
          * exp (t • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X))))
  rw [← hdec, add_neg_cancel_comm, norm_neg, hc, hdec] at htri
  have h3 := mul_le_mul_of_nonneg_left hlead
    (mul_nonneg (abs_nonneg g) (sub_nonneg.2 h12))
  linarith

end Transponder

/-! ### The packet -/

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **The second level fills from the time the packet's box reaches the transponder.** The
messenger is the flat packet of the lattice Dirac field of any dimension; the transponder is
at rest with one energy for both levels, in a state of norm `1` in its first level,
supported on the sites `B`. For `0 ≤ t₁ ≤ t₂ ≤ t`: if no site of the packet's moving box is
related to a site of `B` up to `t₁`, and every site of it is related to every site of `B`
from `t₂` to `t`, then the part of the state at `t` with the transponder in its second level
has norm at least

`|g| (t − t₂) − |g| (√ε₁ t₁ + (t₂ − t₁)) − |g| √ε (t − t₂) − |g| (|g| (√ε₁ t₁ + (t − t₁))) t`,

`ε₁ = flatTailD t₁`, `ε = flatTailD t`. -/
theorem transponder_second_level_flatPacket_meeting_ge (τ : n × Fin 2 → κ → ZMod L)
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
    |g| * (t - t₂)
        - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁))
        - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * (t - t₂))
        - |g| * (|g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t - t₁))) * t
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
  have ht : 0 ≤ t := ht2.trans h2t
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
  have key := transponder_second_level_meeting_ge
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
  have hIb : ∀ u : ℝ, t₁ ≤ u → ∫ s in t₁..u, _ ≤ u - t₁ := fun u hu => by
    have := intervalIntegral.integral_mono_on hu (hcont.intervalIntegrable t₁ u)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s _ => hcrude s
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  have hsplit : ∀ u : ℝ, (∫ s in (0 : ℝ)..u, _) = (∫ s in (0 : ℝ)..t₁, _) + ∫ s in t₁..u, _ :=
    fun u => (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 t₁) (hcont.intervalIntegrable t₁ u)).symm
  have hI1 := hsplit t₂
  have hI3 := hsplit t
  have hIc := intervalIntegral.integral_mono_on h2t (hcont'.intervalIntegrable t₂ t)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t))) fun s hs => hP' s hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hIc
  have hb2 := hIb t₂ h12
  have hb3 := hIb t (h12.trans h2t)
  have hg := abs_nonneg g
  have e1 := mul_le_mul_of_nonneg_left (by linarith [hI1, hIa, hb2] :
    (∫ s in (0 : ℝ)..t₂, _) ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁)) hg
  have e2 := mul_le_mul_of_nonneg_left hIc hg
  have e3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (by linarith [hI3, hIa, hb3] :
      (∫ s in (0 : ℝ)..t, _) ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t - t₁)) hg)
    hg) ht
  linarith [key, e1, e2, e3]

end Packet

end CSD.RecordLayer

end
