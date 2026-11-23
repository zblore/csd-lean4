/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTransponder
public import CsdLean4.RecordLayer.CoincidenceOrbit
public import CsdLean4.RecordLayer.TorusArrival

/-!
# No launch without a meeting, for a state: the bound under the integral

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (1), the caused return;
remainder (a) of the row: the passage to the operator norm under the integral, and the moving
boxes).

`transponder_launch_le_coincidence` (UD-226) bounds the launched part of a matrix `X` by
`‖Q‖ |g| ∫₀ᵗ ‖P e^{−isH₀} X‖ ds`, in the operator norm. `sum_norm_sq_coincProj_freeOrbit_prod_le`
(UD-240) bounds `P e^{−isH₀}` on a product vector, in the Euclidean norm. This module joins
them.

* ★★ `l2_opNorm_vecMulVec` — the operator norm of a rank-one matrix `a bᵀ` is the product of
  the Euclidean norms of `a` and `b`;
* `norm_mul_vecMulVec` — `‖M (a bᵀ)‖ = ‖M a‖ ‖b‖`;
* ★★★ `transponder_launch_vec_le` — **for a state vector `Ψ` with the transponder in its
  first level: the Euclidean norm of the part with the transponder in its second level at
  `t ≥ 0` is at most `‖Q‖ |g| ∫₀ᵗ ‖P e^{−isH₀} Ψ‖ ds`**;
* ★★★ `transponder_launch_prod_le` — for a product `ψ ⊗ φ` of a messenger and a transponder:
  if at every flow time up to `t` there are sets of sites `A s`, `B s` with no pair in the
  relation and the two carriers' weights off them give at most `η²`, the launched part is at
  most `‖Q‖ |g| η t`;
* ★★★ `transponder_launch_flatPacket_le` — **the moving boxes**: the messenger is the flat
  packet of the lattice Dirac field of any dimension, `A s` its moving box. If no site of
  the moving box is related to a site of `B` up to `t`, and the transponder keeps all but
  `ε_B` of its weight on `B`, the launched part is at most
  `‖Q‖ |g| √(flatTailD t + ε_B) · t`.

## Honest scope

⚠️ **An upper bound: nothing is shown to be launched.** This is item (1) of UO-26, no signal
before the meeting. Items (2) to (5) are untouched.

⚠️ **The bound grows like `t`.** It is small only while `|g| √(tail) t` is small; the square
root is of the packet's tail, not the tail.

⚠️ **The transponder's weights are hypotheses**: that its norm is at most `1` and that it
keeps all but `ε_B` of its weight on `B` along its own orbit. No transponder state is
exhibited.

⚠️ **The carriers' own Hamiltonians only**: `H₀` is the uncoupled composite and the coupling
is the contact term of UA-19 with a real strength `g`. No pointer, no arena.

⚠️ **`‖Q‖` is left as it is** (it is the norm of a projector, at most `1`; not used here).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-222, UD-226, UD-236, UD-240, UD-251); `RecordLayer/UnifiedTransponder.lean`
(`transponder_launch_le_coincidence`, `levelProj`); `RecordLayer/CoincidenceOrbit.lean`
(`sum_norm_sq_coincProj_freeOrbit_prod_le`); `RecordLayer/CoincidenceBoxes.lean`
(`sum_ite_fst_eq_regionWeightD_compl`); `RecordLayer/TorusDetector.lean`
(`exp_mulVec_packetD`); `RecordLayer/TorusArrival.lean` (`flatTailD`, `flatTailD_mono`);
`CV/DiracPacketWindowD.lean` (`regionWeightD_flatPacket_compl_movedBoxD_le_window`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The operator norm of a rank-one matrix -/

section RankOne

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- ★★ **The operator norm of a rank-one matrix** is the product of the Euclidean norms of its
two vectors. -/
theorem l2_opNorm_vecMulVec (a b : m → ℂ) :
    ‖Matrix.vecMulVec a b‖
      = Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have hna : ‖(WithLp.toLp 2 a : EuclideanSpace ℂ m)‖ = Real.sqrt (∑ i, ‖a i‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have hnb : ‖(WithLp.toLp 2 b : EuclideanSpace ℂ m)‖ = Real.sqrt (∑ i, ‖b i‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have hnsb : ‖(WithLp.toLp 2 (star b) : EuclideanSpace ℂ m)‖
      = Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp
  have hmv : ∀ x : m → ℂ, Matrix.vecMulVec a b *ᵥ x = (b ⬝ᵥ x) • a := fun x => by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hin : ∀ x : EuclideanSpace ℂ m,
      inner ℂ (WithLp.toLp 2 (star b) : EuclideanSpace ℂ m) x = b ⬝ᵥ x.ofLp := fun x => by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hval : ∀ x : EuclideanSpace ℂ m,
      ‖(EuclideanSpace.equiv m ℂ).symm (Matrix.vecMulVec a b *ᵥ x.ofLp)‖
        = ‖b ⬝ᵥ x.ofLp‖ * Real.sqrt (∑ i, ‖a i‖ ^ 2) := fun x => by
    rw [hmv, ← hna]
    exact norm_smul (b ⬝ᵥ x.ofLp) (WithLp.toLp 2 a : EuclideanSpace ℂ m)
  refine le_antisymm ?_ ?_
  · rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) fun x => ?_
    have hx : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (Matrix.vecMulVec a b) x
        = (EuclideanSpace.equiv m ℂ).symm (Matrix.vecMulVec a b *ᵥ x.ofLp) := rfl
    rw [hx, hval]
    have hcs := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (star b) : EuclideanSpace ℂ m) x
    rw [hin, hnsb] at hcs
    calc ‖b ⬝ᵥ x.ofLp‖ * Real.sqrt (∑ i, ‖a i‖ ^ 2)
        ≤ Real.sqrt (∑ i, ‖b i‖ ^ 2) * ‖x‖ * Real.sqrt (∑ i, ‖a i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hcs (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) * ‖x‖ := by ring
  · by_cases hb : Real.sqrt (∑ i, ‖b i‖ ^ 2) = 0
    · rw [hb, mul_zero]
      exact norm_nonneg _
    · have hbpos : 0 < Real.sqrt (∑ i, ‖b i‖ ^ 2) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hb)
      have h1 := Matrix.l2_opNorm_mulVec (Matrix.vecMulVec a b)
        (WithLp.toLp 2 (star b) : EuclideanSpace ℂ m)
      have hself : ‖b ⬝ᵥ star b‖ = Real.sqrt (∑ i, ‖b i‖ ^ 2) ^ 2 := by
        have h2 := hin (WithLp.toLp 2 (star b) : EuclideanSpace ℂ m)
        rw [inner_self_eq_norm_sq_to_K, hnsb] at h2
        have h3 : b ⬝ᵥ star b
            = ((Real.sqrt (∑ i, ‖b i‖ ^ 2) : ℝ) : ℂ) ^ 2 := h2.symm
        rw [h3, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      have h4 := hval (WithLp.toLp 2 (star b) : EuclideanSpace ℂ m)
      have h5 : ‖b ⬝ᵥ star b‖ * Real.sqrt (∑ i, ‖a i‖ ^ 2)
          ≤ ‖Matrix.vecMulVec a b‖ * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
        rw [← hnsb]
        exact h4 ▸ h1
      rw [hself] at h5
      refine le_of_mul_le_mul_right ?_ hbpos
      calc Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)
            * Real.sqrt (∑ i, ‖b i‖ ^ 2)
          = Real.sqrt (∑ i, ‖b i‖ ^ 2) ^ 2 * Real.sqrt (∑ i, ‖a i‖ ^ 2) := by ring
        _ ≤ ‖Matrix.vecMulVec a b‖ * Real.sqrt (∑ i, ‖b i‖ ^ 2) := h5

/-- `‖M (a bᵀ)‖ = ‖M a‖ ‖b‖`. -/
theorem norm_mul_vecMulVec (M : Matrix m m ℂ) (a b : m → ℂ) :
    ‖M * Matrix.vecMulVec a b‖
      = Real.sqrt (∑ i, ‖(M *ᵥ a) i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  rw [Matrix.mul_vecMulVec, l2_opNorm_vecMulVec]

end RankOne

/-! ### The launch bound for a state -/

section Launch

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

/-- ★★★ **No launch without a meeting, for a state vector.** For `Ψ` with the transponder in
its first level, the part with the transponder in its second level at the time `t ≥ 0` has
Euclidean norm at most `‖Q‖ |g| ∫₀ᵗ ‖P e^{−isH₀} Ψ‖ ds`, `P` the coincidence projector of the
messenger and the transponder. -/
theorem transponder_launch_vec_le (σ : ι → S) (τ : n × Fin 2 → S) (r : S → S → Prop)
    [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian) (g : ℝ)
    (Ψ : ι × (n × Fin 2) → ℂ)
    (hΨ : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) *ᵥ Ψ = 0) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n))))) *ᵥ Ψ) x‖ ^ 2)
      ≤ ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1‖
        * (|g| * ∫ s in (0 : ℝ)..t,
            Real.sqrt (∑ x, ‖((coincProj σ τ r
              * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) *ᵥ Ψ) x‖
                ^ 2)) := by
  have hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * Matrix.vecMulVec Ψ (star Ψ) = 0 := by
    rw [Matrix.mul_vecMulVec, hΨ]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have hmat := transponder_launch_le_coincidence σ τ r hτ hM hT g
    (Matrix.vecMulVec Ψ (star Ψ)) hX ht
  simp only [norm_mul_vecMulVec] at hmat
  rw [intervalIntegral.integral_mul_const] at hmat
  have hI : 0 ≤ ∫ s in (0 : ℝ)..t,
      Real.sqrt (∑ x, ‖((coincProj σ τ r
        * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T)))) *ᵥ Ψ) x‖ ^ 2) :=
    intervalIntegral.integral_nonneg ht fun s _ => Real.sqrt_nonneg _
  by_cases hN : Real.sqrt (∑ x, ‖star Ψ x‖ ^ 2) = 0
  · have hsum : ∑ x, ‖star Ψ x‖ ^ 2 = 0 :=
      (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 hN
    have hz : Ψ = 0 := by
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hsum x
        (Finset.mem_univ x)
      simpa using this
    rw [hz]
    simp only [Matrix.mulVec_zero, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    exact mul_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg g)
      (intervalIntegral.integral_nonneg ht fun s _ => le_rfl))
  · refine le_of_mul_le_mul_right ?_ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hN))
    calc _ ≤ _ := hmat
      _ = _ := by ring

/-- ★★★ **A messenger and a transponder whose boxes are not in contact.** The state is the
product `ψ ⊗ φ`, the transponder in its first level. If at every flow time `s` of `[0, t]`
there are sets of sites `A s`, `B s` with no pair in the relation `r`, and the weight of the
messenger's orbit off `A s` times the transponder's norm plus the messenger's norm times the
weight of the transponder's orbit off `B s` is at most `η²`, then the part with the
transponder in its second level at `t` has norm at most `‖Q‖ |g| η t`. -/
theorem transponder_launch_prod_le [DecidableEq S] (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian) (g : ℝ)
    (ψ : ι → ℂ) (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    {t η : ℝ} (ht : 0 ≤ t) (hη : 0 ≤ η) (A B : ℝ → Finset S)
    (hAB : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ A s, ∀ b ∈ B s, ¬ r a b)
    (hw : ∀ s, 0 ≤ s → s ≤ t →
      (∑ p, if σ p ∈ A s then 0 else ‖(exp (s • ((-Complex.I) • M₀)) *ᵥ ψ) p‖ ^ 2)
          * (∑ q, ‖(exp (s • ((-Complex.I) • Matrix.blockDiagonal T)) *ᵥ φ) q‖ ^ 2)
        + (∑ p, ‖(exp (s • ((-Complex.I) • M₀)) *ᵥ ψ) p‖ ^ 2)
          * (∑ q, if τ q ∈ B s then 0
              else ‖(exp (s • ((-Complex.I) • Matrix.blockDiagonal T)) *ᵥ φ) q‖ ^ 2)
        ≤ η ^ 2) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp σ τ r (levelSwap n)))))
          *ᵥ fun y : ι × (n × Fin 2) => ψ y.1 * φ y.2) x‖ ^ 2)
      ≤ ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1‖ * (|g| * (η * t)) := by
  have hΨ : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
      *ᵥ (fun y : ι × (n × Fin 2) => ψ y.1 * φ y.2) = 0 := by
    rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal]
    funext y
    rw [Matrix.mulVec_diagonal]
    by_cases hy : y.2.2 = 1
    · simp [hφ y.2 hy]
    · simp [hy]
  refine (transponder_launch_vec_le σ τ r hτ hM hT g _ hΨ ht).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg g))
    (norm_nonneg _)
  have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (C := η) (f := fun s : ℝ => Real.sqrt (∑ x, ‖((coincProj σ τ r
      * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))))
        *ᵥ fun y : ι × (n × Fin 2) => ψ y.1 * φ y.2) x‖ ^ 2)) fun s hs => by
    rw [Set.uIoc_of_le ht] at hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← Matrix.mulVec_mulVec]
    have h1 := sum_norm_sq_coincProj_freeOrbit_prod_le σ τ r M₀ (Matrix.blockDiagonal T) s ψ φ
      (hAB s hs.1.le hs.2)
    have h2 := Real.sqrt_le_sqrt (h1.trans (hw s hs.1.le hs.2))
    rwa [Real.sqrt_sq hη] at h2
  rw [sub_zero, abs_of_nonneg ht] at key
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans key)

end Launch

/-! ### The moving boxes -/

section Boxes

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **No launch before the packet's box reaches the transponder.** The messenger is the
flat packet of the lattice Dirac field of any dimension; the transponder starts in its first
level, with norm at most `1` along its orbit and all but `ε_B` of its weight on the sites
`B`. If up to the flow time `t` no site of the packet's moving box is in the relation `r`
with a site of `B`, the part with the transponder in its second level at `t` has norm at
most `‖Q‖ |g| √(flatTailD t + ε_B) · t`. -/
theorem transponder_launch_flatPacket_le (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian) (g : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    (B : Finset (κ → ZMod L)) {t εB : ℝ} (ht : 0 ≤ t) (hεB : 0 ≤ εB)
    (hsep : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b)
    (hφ1 : ∀ s, 0 ≤ s → s ≤ t →
      ∑ q, ‖(exp (s • ((-Complex.I) • Matrix.blockDiagonal T)) *ᵥ φ) q‖ ^ 2 ≤ 1)
    (hφB : ∀ s, 0 ≤ s → s ≤ t →
      (∑ q, if τ q ∈ B then 0
        else ‖(exp (s • ((-Complex.I) • Matrix.blockDiagonal T)) *ᵥ φ) q‖ ^ 2) ≤ εB) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
          ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH (latticeDiracHam (L := L) α β J μ)
              (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
          *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
            packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
              (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2)
      ≤ ‖(1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1‖
        * (|g| * (Real.sqrt (flatTailD L J μ Nw w γ t + εB) * t)) := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  have hnorm : ∀ s : ℝ, ∑ p, ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) s p‖ ^ 2 = 1 := fun s => by
    rw [← re_chainInnerD_self, chainInnerD_packetD_unitAmpD h he hn hμ hD, sum_flatAmpD_sq lo hN,
      Complex.ofReal_re]
  have hcompl : ∀ s : ℝ, 0 ≤ s →
      regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) s) (movedBoxD L J μ k₀ (fun _ => 1) γ s)ᶜ
        ≤ flatTailD L J μ Nw w γ s := fun s hs => by
    have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
      lo hN hNL k₀ hw0 hw s hγ
    rw [abs_of_nonneg hs] at hh
    rw [flatTailD]
    exact hh
  have htail0 : 0 ≤ flatTailD L J μ Nw w γ t :=
    (regionWeightD_nonneg _ _).trans (hcompl t ht)
  refine transponder_launch_prod_le (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r hτ
    (latticeDiracHam_isHermitian h J μ) hT g _ φ hφ ht (Real.sqrt_nonneg _)
    (fun s => movedBoxD L J μ k₀ (fun _ => 1) γ s) (fun _ => B) hsep fun s hs hst => ?_
  rw [Real.sq_sqrt (add_nonneg htail0 hεB), exp_mulVec_packetD h J μ e₀ _ _ s,
    sum_ite_fst_eq_regionWeightD_compl, hnorm s, one_mul]
  have h1 := (hcompl s hs).trans (flatTailD_mono (J := J) hμ Nw hw0 hγ hst)
  have h2 := mul_le_mul h1 (hφ1 s hs hst) (Finset.sum_nonneg fun _ _ => sq_nonneg _) htail0
  linarith [hφB s hs hst]

end Boxes

end CSD.RecordLayer

end
