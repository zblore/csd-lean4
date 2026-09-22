/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Extremal

/-!
# Gleason's theorem, finite-dimensional: the core lemma — every nonnegative frame function on
`S²` is a quadratic form

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, stage
57(e): Cooke–Keane–Moran §7, the general case, and with it **Gleason's core lemma**
★★ `frameFunction_regular_sphere`.

The argument. Let `f` be a frame function on `S² ⊂ ℝ³`, nonnegative (hence bounded by its
weight `W`). By stage (d) it attains its supremum `M` at some `p`; a minimiser of
`f + ⟪p, ·⟫²` is a point `r ⟂ p` where `f` attains its infimum `m`. With `q = r × p` this is a
frame; put `α = f q`, so `M + α + m = W`, and let `g s = M ⟪p,s⟫² + α ⟪q,s⟫² + m ⟪r,s⟫²` — the
quadratic form `f` ought to be.

* **The pole identities.** `f + f ∘ rot p` attains its supremum `2M` at `p` and is constant on
  the equator of `p`, so the simple-frame-function theorem (stage (c)) gives
  `f s + f (rot p s) = (W − M) + (3M − W)⟪p,s⟫²` (`IsFrameFunction.add_rot_of_forall_le`);
  likewise at the minimum `r`, applied to `−f` (`add_rot_of_forall_ge`). The quadratic form `g`
  satisfies the same two identities (a computation in the frame, `quadFrame_add_rot_p`,
  `quadFrame_add_rot_r`), so `h = g − f` satisfies `h (rot p s) = −h s`, `h (rot r s) = −h s`
  and `h (−s) = h s`.
* **The symmetries.** Since `rot p ∘ rot p` is the half-turn about `p`, the reflection in each
  coordinate plane preserves `h` (`flip_p`, `flip_q`, `flip_r`); composing with `rot p` and
  `rot r`, the reflections in the planes `x = ±y` and `y = ±z` negate `h`, so **`h` vanishes on
  those four great circles** (`vanish_p_eq_q`, …).
* **The endgame** (this replaces the paper's count of zeros on great circles). If `h ≠ 0`, its
  supremum `M' > 0` is attained at some `p'` (stage (d)) and the pole identity for `h` reads
  `h s + h (rot p' s) = M'(3⟪p',s⟫² − 1)`. On a great circle with unit normal `n` on which `h`
  vanishes there is a point `t` with `rot p' t` on the same circle, hence `⟪p',t⟫² = 1/3`, and
  the geometry of `t` forces `⟪p', n⟫² = 1/2` (`inner_sq_eq_half_of_vanish`). For the four
  normals `(p ± q)/√2`, `(q ± r)/√2` this gives `⟪p',p⟫² + ⟪p',q⟫² = 1 = ⟪p',q⟫² + ⟪p',r⟫²`,
  so with Parseval `p' = ±q`; but `h q = α − α = 0`, contradicting `M' > 0`. Hence `f = g`.

With `Gleason/Reduction.lean` this proves the finite-dimensional Gleason theorem
(`Gleason/Core.lean`).

## Source

Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117–128, §7 (the
choice of `p, r, q`, the target form, the identities (*) and the Claim); the endgame is
different from the paper's.
-/

@[expose] public section

open Matrix
open scoped Matrix InnerProductSpace

namespace Gleason

/-! ### Cross-product algebra -/

lemma ext_coe {x y : EuclideanSpace ℝ (Fin 3)} (h : ⇑x = ⇑y) : x = y :=
  PiLp.ext fun i => congrFun h i

/-- The cyclic symmetry of the scalar triple product: `⟪u, v × w⟫ = ⟪w, u × v⟫`. -/
lemma inner_cross_perm (u v w : EuclideanSpace ℝ (Fin 3)) :
    ⟪u, cross v w⟫_ℝ = ⟪w, cross u v⟫_ℝ := by
  rw [real_inner_eq_dotProduct, real_inner_eq_dotProduct, coe_cross, coe_cross,
    triple_product_permutation (⇑u) (⇑v) (⇑w), triple_product_permutation (⇑v) (⇑w) (⇑u)]

lemma cross_eq_neg_cross (x y : EuclideanSpace ℝ (Fin 3)) : cross x y = -cross y x := by
  apply ext_coe
  rw [WithLp.ofLp_neg, coe_cross, coe_cross, cross_anticomm]

/-- The vector triple product `(u × v) × w = ⟪u,w⟫ v − ⟪v,w⟫ u`. -/
lemma cross_cross_left (u v w : EuclideanSpace ℝ (Fin 3)) :
    cross (cross u v) w = ⟪u, w⟫_ℝ • v - ⟪v, w⟫_ℝ • u := by
  apply ext_coe
  rw [coe_cross, coe_cross, cross_cross_eq_smul_sub_smul, WithLp.ofLp_sub, WithLp.ofLp_smul,
    WithLp.ofLp_smul, real_inner_eq_dotProduct, real_inner_eq_dotProduct]

/-! ### A frame `(p, q, r)` with `q = r × p`, and its table -/

/-- A right-handed frame: `p, r` orthonormal and `q = r × p`. -/
structure Frame (p q r : EuclideanSpace ℝ (Fin 3)) : Prop where
  /-- `‖p‖ = 1`. -/
  hp : ‖p‖ = 1
  /-- `‖r‖ = 1`. -/
  hr : ‖r‖ = 1
  /-- `p ⟂ r`. -/
  hpr : ⟪p, r⟫_ℝ = 0
  /-- `q = r × p`. -/
  hq : q = cross r p

namespace Frame

variable {p q r : EuclideanSpace ℝ (Fin 3)} (F : Frame p q r)
include F

lemma hrp : ⟪r, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact F.hpr

lemma hq1 : ‖q‖ = 1 := by rw [F.hq]; exact norm_cross_of_orthonormal F.hr F.hp F.hrp

lemma hpq : ⟪p, q⟫_ℝ = 0 := by rw [F.hq]; exact inner_cross_right r p

lemma hqr : ⟪q, r⟫_ℝ = 0 := by rw [F.hq, real_inner_comm]; exact inner_cross_left r p

lemma hqp : ⟪q, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact F.hpq

lemma hrq : ⟪r, q⟫_ℝ = 0 := by rw [real_inner_comm]; exact F.hqr

lemma hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, F.hp]; norm_num

lemma hqq : ⟪q, q⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, F.hq1]; norm_num

lemma hrr : ⟪r, r⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, F.hr]; norm_num

lemma orthonormal : Orthonormal ℝ ![p, q, r] :=
  orthonormal_triple_iff.mpr ⟨F.hp, F.hq1, F.hr, F.hpq, F.hpr, F.hqr⟩

/-- The table: `q × p = −r`. -/
lemma cross_q_p : cross q p = -r := by
  rw [F.hq, cross_cross_left, F.hrp, real_inner_self_eq_norm_sq, F.hp]
  simp

lemma cross_q_r : cross q r = p := by
  rw [F.hq, cross_cross_left, real_inner_self_eq_norm_sq, F.hr, F.hpr]
  simp

lemma cross_p_r : cross p r = -q := by rw [cross_eq_neg_cross, ← F.hq]

/-- The expansion `s = ⟪p,s⟫ p + ⟪q,s⟫ q + ⟪r,s⟫ r`. -/
lemma expand (s : EuclideanSpace ℝ (Fin 3)) :
    s = ⟪p, s⟫_ℝ • p + ⟪q, s⟫_ℝ • q + ⟪r, s⟫_ℝ • r := by
  have h := (orthonormalBasisOfTriple F.orthonormal).sum_repr' s
  simp only [coe_orthonormalBasisOfTriple, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  exact h.symm

/-- Two vectors with the same frame coordinates are equal. -/
lemma eq_of_inner {a b : EuclideanSpace ℝ (Fin 3)} (h1 : ⟪p, a⟫_ℝ = ⟪p, b⟫_ℝ)
    (h2 : ⟪q, a⟫_ℝ = ⟪q, b⟫_ℝ) (h3 : ⟪r, a⟫_ℝ = ⟪r, b⟫_ℝ) : a = b := by
  calc a = ⟪p, a⟫_ℝ • p + ⟪q, a⟫_ℝ • q + ⟪r, a⟫_ℝ • r := F.expand a
    _ = ⟪p, b⟫_ℝ • p + ⟪q, b⟫_ℝ • q + ⟪r, b⟫_ℝ • r := by rw [h1, h2, h3]
    _ = b := (F.expand b).symm

/-- Parseval: `⟪p,s⟫² + ⟪q,s⟫² + ⟪r,s⟫² = ‖s‖²`. -/
lemma sum_sq (s : EuclideanSpace ℝ (Fin 3)) :
    ⟪p, s⟫_ℝ ^ 2 + ⟪q, s⟫_ℝ ^ 2 + ⟪r, s⟫_ℝ ^ 2 = ‖s‖ ^ 2 := by
  have h := (orthonormalBasisOfTriple F.orthonormal).sum_inner_mul_inner s s
  simp only [coe_orthonormalBasisOfTriple, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    real_inner_self_eq_norm_sq] at h
  rw [← h, real_inner_comm s p, real_inner_comm s q, real_inner_comm s r]
  ring

/-- The rotation about `p` in frame coordinates: `(x, y, z) ↦ (x, −z, y)`. -/
lemma inner_p_rot_p (s : EuclideanSpace ℝ (Fin 3)) : ⟪p, rot p s⟫_ℝ = ⟪p, s⟫_ℝ := by
  rw [rot, inner_add_right, real_inner_smul_right, F.hpp, inner_cross_left]; ring

lemma inner_q_rot_p (s : EuclideanSpace ℝ (Fin 3)) : ⟪q, rot p s⟫_ℝ = -⟪r, s⟫_ℝ := by
  rw [rot, inner_add_right, real_inner_smul_right, F.hqp, inner_cross_perm, F.cross_q_p,
    inner_neg_right, real_inner_comm r s]; ring

lemma inner_r_rot_p (s : EuclideanSpace ℝ (Fin 3)) : ⟪r, rot p s⟫_ℝ = ⟪q, s⟫_ℝ := by
  rw [rot, inner_add_right, real_inner_smul_right, F.hrp, inner_cross_perm, ← F.hq,
    real_inner_comm q s]; ring

/-- The rotation about `r` in frame coordinates: `(x, y, z) ↦ (−y, x, z)`. -/
lemma inner_p_rot_r (s : EuclideanSpace ℝ (Fin 3)) : ⟪p, rot r s⟫_ℝ = -⟪q, s⟫_ℝ := by
  rw [rot, inner_add_right, real_inner_smul_right, F.hpr, inner_cross_perm, F.cross_p_r,
    inner_neg_right, real_inner_comm q s]; ring

lemma inner_q_rot_r (s : EuclideanSpace ℝ (Fin 3)) : ⟪q, rot r s⟫_ℝ = ⟪p, s⟫_ℝ := by
  rw [rot, inner_add_right, real_inner_smul_right, F.hqr, inner_cross_perm, F.cross_q_r,
    real_inner_comm p s]; ring

lemma inner_r_rot_r (s : EuclideanSpace ℝ (Fin 3)) : ⟪r, rot r s⟫_ℝ = ⟪r, s⟫_ℝ := by
  rw [rot, inner_add_right, real_inner_smul_right, F.hrr, inner_cross_left]; ring

end Frame

/-! ### The inverse rotation, as an adjoint -/

/-- The rotation by `−90°` about `p`: `n ↦ ⟪p, n⟫ p − p × n`. -/
noncomputable def rotInv (p n : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  ⟪p, n⟫_ℝ • p - cross p n

/-- `⟪n, rot p s⟫ = ⟪rotInv p n, s⟫`. -/
lemma inner_rot_eq_inner_rotInv (p n s : EuclideanSpace ℝ (Fin 3)) :
    ⟪n, rot p s⟫_ℝ = ⟪rotInv p n, s⟫_ℝ := by
  rw [rot, rotInv, inner_add_right, real_inner_smul_right, inner_sub_left,
    real_inner_smul_left, inner_cross_perm n p s, cross_eq_neg_cross n p, inner_neg_right,
    real_inner_comm n p, real_inner_comm (cross p n) s]
  ring

lemma norm_rotInv {p n : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1) (hn : ‖n‖ = 1) :
    ‖rotInv p n‖ = 1 := by
  refine norm_eq_one_of_real_inner_self ?_
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  have hnn : ⟪n, n⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hc : ⟪p, cross p n⟫_ℝ = 0 := inner_cross_left p n
  have hc' : ⟪cross p n, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact hc
  simp only [rotInv, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hpp, hc, hc', inner_cross_cross, hnn]
  rw [real_inner_comm n p]
  ring

/-! ### The pole identities -/

namespace IsFrameFunction

variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W : ℝ} {p : EuclideanSpace ℝ (Fin 3)}

/-- **The pole identity at a maximum.** If `f` attains its supremum at `p`, then
`f s + f (rot p s) = (W − f p) + (3 f p − W) ⟪p, s⟫²` for every unit `s`. -/
theorem add_rot_of_forall_le (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) :
    ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 →
      f s + f (rot p s) = (W - f p) + (3 * f p - W) * latitude p s := by
  obtain ⟨e₀, he₀, hpe₀⟩ := exists_unit_orthogonal p
  have hE : ∀ e ∈ equator p, Gleason.symmetrise p f e = Gleason.symmetrise p f e₀ :=
    fun e he => symmetrise_equator hf hp he ⟨he₀, hpe₀⟩
  have hM' : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 →
      Gleason.symmetrise p f u ≤ Gleason.symmetrise p f p :=
    fun u hu => by rw [symmetrise_pole hp]; exact symmetrise_le hp hM hu
  have hval : Gleason.symmetrise p f e₀ = W - f p := by
    have h := hf.eq_of_triple (orthonormal_cross hp he₀ hpe₀)
    have h2 : rot p e₀ = cross p e₀ := by rw [rot, hpe₀, zero_smul, zero_add]
    rw [Gleason.symmetrise, h2]; linarith
  intro s hs
  have := (hf.symmetrise hp).eq_add_mul_latitude hp hM' hE s hs
  rw [symmetrise_pole hp, hval, Gleason.symmetrise] at this
  rw [this]
  ring

/-- **The pole identity at a minimum.** If `f` attains its infimum at `r`, then
`f s + f (rot r s) = (W − f r) − (W − 3 f r) ⟪r, s⟫²` for every unit `s`. -/
theorem add_rot_of_forall_ge (hf : IsFrameFunction ℝ f W) {r : EuclideanSpace ℝ (Fin 3)}
    (hr : ‖r‖ = 1) (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f r ≤ f u) :
    ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 →
      f s + f (rot r s) = (W - f r) - (W - 3 * f r) * latitude r s := by
  intro s hs
  have h := hf.neg.add_rot_of_forall_le hr
    (fun u hu => by show -f u ≤ -f r; linarith [hm u hu]) s hs
  beta_reduce at h
  linarith

end IsFrameFunction

/-! ### The target quadratic form -/

/-- The quadratic form `M ⟪p,s⟫² + α ⟪q,s⟫² + m ⟪r,s⟫²`. -/
noncomputable def quadFrame (M α m : ℝ) (p q r s : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  M * ⟪p, s⟫_ℝ ^ 2 + α * ⟪q, s⟫_ℝ ^ 2 + m * ⟪r, s⟫_ℝ ^ 2

section QuadFrame

variable {p q r : EuclideanSpace ℝ (Fin 3)} (F : Frame p q r) {M α m W : ℝ}
include F

lemma isFrameFunction_quadFrame : IsFrameFunction ℝ (quadFrame M α m p q r) (M + α + m) := by
  have h1 := (isFrameFunction_inner_sq F.hp).smul M
  have h2 := (isFrameFunction_inner_sq F.hq1).smul α
  have h3 := (isFrameFunction_inner_sq F.hr).smul m
  have := (h1.add h2).add h3
  simp only [mul_one] at this
  exact this

omit F in
lemma quadFrame_neg (s : EuclideanSpace ℝ (Fin 3)) :
    quadFrame M α m p q r (-s) = quadFrame M α m p q r s := by
  simp only [quadFrame, inner_neg_right, neg_sq]

/-- The pole identity for the quadratic form at `p`. -/
lemma quadFrame_add_rot_p (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) :
    quadFrame M α m p q r s + quadFrame M α m p q r (rot p s)
      = (α + m) + (2 * M - (α + m)) * latitude p s := by
  have h := F.sum_sq s
  rw [hs, one_pow] at h
  simp only [quadFrame, latitude, F.inner_p_rot_p, F.inner_q_rot_p, F.inner_r_rot_p, neg_sq]
  linear_combination (α + m) * h

/-- The pole identity for the quadratic form at `r`. -/
lemma quadFrame_add_rot_r (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) :
    quadFrame M α m p q r s + quadFrame M α m p q r (rot r s)
      = (M + α) - ((M + α) - 2 * m) * latitude r s := by
  have h := F.sum_sq s
  rw [hs, one_pow] at h
  simp only [quadFrame, latitude, F.inner_p_rot_r, F.inner_q_rot_r, F.inner_r_rot_r, neg_sq]
  linear_combination (M + α) * h

omit F in
lemma quadFrame_nonneg (hM : 0 ≤ M) (hα : 0 ≤ α) (hm : 0 ≤ m) (s : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ quadFrame M α m p q r s := by
  unfold quadFrame; positivity

lemma quadFrame_le (hM : M ≤ W) (hα : α ≤ W) (hm : m ≤ W) (s : EuclideanSpace ℝ (Fin 3))
    (hs : ‖s‖ = 1) : quadFrame M α m p q r s ≤ W := by
  have h := F.sum_sq s
  rw [hs, one_pow] at h
  have hW1 : W * (⟪p, s⟫_ℝ ^ 2 + ⟪q, s⟫_ℝ ^ 2 + ⟪r, s⟫_ℝ ^ 2) = W := by rw [h, mul_one]
  have h1 := mul_le_mul_of_nonneg_right hM (sq_nonneg ⟪p, s⟫_ℝ)
  have h2 := mul_le_mul_of_nonneg_right hα (sq_nonneg ⟪q, s⟫_ℝ)
  have h3 := mul_le_mul_of_nonneg_right hm (sq_nonneg ⟪r, s⟫_ℝ)
  unfold quadFrame
  linarith

omit F in
/-- The quadratic form as a matrix: `s ⬝ A s` with `A = M p pᵀ + α q qᵀ + m r rᵀ`. -/
lemma quadFrame_eq_dotProduct (s : EuclideanSpace ℝ (Fin 3)) :
    quadFrame M α m p q r s = ⇑s ⬝ᵥ ((M • vecMulVec (⇑p) (⇑p) + α • vecMulVec (⇑q) (⇑q)
      + m • vecMulVec (⇑r) (⇑r)) *ᵥ ⇑s) := by
  simp only [quadFrame, real_inner_eq_dotProduct, dotProduct, Matrix.mulVec, Matrix.add_apply,
    Matrix.smul_apply, vecMulVec_apply, Fin.sum_univ_three, smul_eq_mul]
  ring

end QuadFrame

/-! ### The circle lemma -/

/-- **A great circle of zeros sits at latitude `1/2` from the pole of the identity.** If
`h s + h (rot p' s) = M'(3⟪p',s⟫² − 1)` on the sphere with `M' ≠ 0`, and `h` vanishes on the
great circle with unit normal `n`, then `⟪p', n⟫² = 1/2`. -/
theorem inner_sq_eq_half_of_vanish {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    {p' n : EuclideanSpace ℝ (Fin 3)} {M' : ℝ} (hp' : ‖p'‖ = 1) (hM' : M' ≠ 0)
    (hid : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 →
      h s + h (rot p' s) = M' * (3 * ⟪p', s⟫_ℝ ^ 2 - 1))
    (hn : ‖n‖ = 1) (hz : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → ⟪n, s⟫_ℝ = 0 → h s = 0) :
    ⟪p', n⟫_ℝ ^ 2 = 1 / 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ⟪p', n⟫_ℝ := ⟨_, rfl⟩
  have ha1 : a ^ 2 ≤ 1 := by
    rw [ha, ← sq_abs]
    calc |⟪p', n⟫_ℝ| ^ 2 ≤ (‖p'‖ * ‖n‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm p' n) 2
      _ = 1 := by rw [hp', hn]; norm_num
  have hpp : ⟪p', p'⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp']; norm_num
  have hnn : ⟪n, n⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hprot : ∀ t, ⟪p', rot p' t⟫_ℝ = ⟪p', t⟫_ℝ := fun t => by
    rw [rot, inner_add_right, real_inner_smul_right, hpp, inner_cross_left]; ring
  rcases eq_or_lt_of_le ha1 with h1 | h1
  · -- `n = ± p'`: the whole equator of `p'` is a circle of zeros, so `M' = 0`
    exfalso
    have hnp : n = a • p' := by
      have h2 : ‖n - a • p'‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm p' n, ← ha, norm_smul, hn,
          hp', Real.norm_eq_abs, mul_one, sq_abs, one_pow]
        linear_combination (-1 : ℝ) * h1
      exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))
    obtain ⟨t, ht, hpt⟩ := exists_unit_orthogonal p'
    have hz1 : h t = 0 := hz t ht (by rw [hnp, real_inner_smul_left, hpt, mul_zero])
    have hz2 : h (rot p' t) = 0 := hz _ (norm_rot hp' ht) (by
      rw [hnp, real_inner_smul_left, hprot, hpt, mul_zero])
    have := hid t ht
    rw [hz1, hz2, hpt] at this
    exact hM' (by linear_combination this)
  · -- the point `t ∝ n × rotInv p' n` and its rotation both lie on the circle
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin 3), w = rotInv p' n := ⟨_, rfl⟩
    have hw1 : ‖w‖ = 1 := by rw [hw]; exact norm_rotInv hp' hn
    have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw1]; norm_num
    have hnw : ⟪n, w⟫_ℝ = a ^ 2 := by
      rw [hw, rotInv, inner_sub_right, real_inner_smul_right, inner_cross_right,
        real_inner_comm p' n, ← ha]
      ring
    have hcross : ⟪cross p' n, cross p' n⟫_ℝ = 1 - a ^ 2 := by
      rw [inner_cross_cross, hpp, hnn, ← ha, real_inner_comm p' n, ← ha]; ring
    obtain ⟨x, hx⟩ : ∃ x : EuclideanSpace ℝ (Fin 3), x = cross n w := ⟨_, rfl⟩
    have hxx : ⟪x, x⟫_ℝ = 1 - a ^ 4 := by
      rw [hx, inner_cross_cross, hnn, hww, real_inner_comm n w, hnw]; ring
    have h7 : (0 : ℝ) < 1 - a ^ 2 := by linarith
    have h8 : (0 : ℝ) < 1 + a ^ 2 := by positivity
    have hxpos : 0 < ⟪x, x⟫_ℝ := by
      rw [hxx, show (1 : ℝ) - a ^ 4 = (1 - a ^ 2) * (1 + a ^ 2) by ring]
      exact mul_pos h7 h8
    have hxn : 0 < ‖x‖ := by
      rw [real_inner_self_eq_norm_sq] at hxpos
      nlinarith [norm_nonneg x]
    have hpx : ⟪p', x⟫_ℝ = -(1 - a ^ 2) := by
      rw [hx, inner_cross_perm, hw, rotInv, inner_sub_left, real_inner_smul_left,
        inner_cross_left, hcross]
      ring
    obtain ⟨t, ht⟩ : ∃ t : EuclideanSpace ℝ (Fin 3), t = (‖x‖⁻¹ : ℝ) • x := ⟨_, rfl⟩
    have ht1 : ‖t‖ = 1 := by
      rw [ht, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn), inv_mul_cancel₀ hxn.ne']
    have hnt : ⟪n, t⟫_ℝ = 0 := by
      rw [ht, real_inner_smul_right, hx, inner_cross_left, mul_zero]
    have hwt : ⟪w, t⟫_ℝ = 0 := by
      rw [ht, real_inner_smul_right, hx, inner_cross_right, mul_zero]
    have hz1 : h t = 0 := hz t ht1 hnt
    have hz2 : h (rot p' t) = 0 := hz _ (norm_rot hp' ht1) (by
      rw [inner_rot_eq_inner_rotInv, ← hw]; exact hwt)
    have hid' := hid t ht1
    rw [hz1, hz2] at hid'
    have h3 : ⟪p', t⟫_ℝ ^ 2 = 1 / 3 := by
      have : M' * (3 * ⟪p', t⟫_ℝ ^ 2 - 1) = 0 := by linarith
      have h4 := (mul_eq_zero.mp this).resolve_left hM'
      linarith
    -- `⟪p', t⟫² (1 + a²) = (1 − a²)`
    have h9 : (1 : ℝ) - a ^ 4 ≠ 0 := by rw [hxx] at hxpos; exact hxpos.ne'
    have h5 : ⟪p', t⟫_ℝ ^ 2 * (1 + a ^ 2) = 1 - a ^ 2 := by
      rw [ht, real_inner_smul_right, hpx, mul_pow, inv_pow, ← real_inner_self_eq_norm_sq, hxx,
        neg_sq, inv_mul_eq_div, div_mul_eq_mul_div, div_eq_iff h9]
      ring
    rw [h3] at h5
    rw [← ha]
    linarith

/-! ### The reflections, and the four circles of zeros -/

/-- The reflection in the plane orthogonal to `a`. -/
noncomputable def reflect (a s : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  s - (2 * ⟪a, s⟫_ℝ) • a

section Zeros

variable {p q r : EuclideanSpace ℝ (Fin 3)} (F : Frame p q r) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
  (heven : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h (-s) = h s)
  (hrotp : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h (rot p s) = -h s)
  (hrotr : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h (rot r s) = -h s)
include F heven hrotp hrotr

omit heven hrotp hrotr in
/-- The half-turn about `p`: `rot p (rot p s) = 2⟪p,s⟫ p − s`. -/
lemma rot_rot_p (s : EuclideanSpace ℝ (Fin 3)) :
    rot p (rot p s) = (2 * ⟪p, s⟫_ℝ) • p - s := by
  refine F.eq_of_inner ?_ ?_ ?_ <;>
    simp only [inner_sub_right, real_inner_smul_right, F.hpp, F.hqp, F.hrp, F.inner_p_rot_p,
      F.inner_q_rot_p, F.inner_r_rot_p] <;> ring

omit heven hrotp hrotr in
lemma rot_rot_r (s : EuclideanSpace ℝ (Fin 3)) :
    rot r (rot r s) = (2 * ⟪r, s⟫_ℝ) • r - s := by
  refine F.eq_of_inner ?_ ?_ ?_ <;>
    simp only [inner_sub_right, real_inner_smul_right, F.hpr, F.hqr, F.hrr, F.inner_p_rot_r,
      F.inner_q_rot_r, F.inner_r_rot_r] <;> ring

omit hrotr in
/-- The reflection in `p^⊥` preserves `h`. -/
lemma flip_p (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) : h (reflect p s) = h s := by
  have h1 : reflect p s = -(rot p (rot p s)) := by rw [reflect, rot_rot_p F]; abel
  rw [h1, heven _ (norm_rot F.hp (norm_rot F.hp hs)), hrotp _ (norm_rot F.hp hs), hrotp s hs,
    neg_neg]

omit hrotp in
/-- The reflection in `r^⊥` preserves `h`. -/
lemma flip_r (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) : h (reflect r s) = h s := by
  have h1 : reflect r s = -(rot r (rot r s)) := by rw [reflect, rot_rot_r F]; abel
  rw [h1, heven _ (norm_rot F.hr (norm_rot F.hr hs)), hrotr _ (norm_rot F.hr hs), hrotr s hs,
    neg_neg]

/-- The reflection in `q^⊥` preserves `h`: it is the reflection in `r^⊥` composed with the
half-turn about `p`. -/
lemma flip_q (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) : h (reflect q s) = h s := by
  have h1 : reflect q s = reflect r (rot p (rot p s)) := by
    refine F.eq_of_inner ?_ ?_ ?_ <;>
      simp only [reflect, inner_sub_right, real_inner_smul_right, F.hpq, F.hqq, F.hrq, F.hpr,
        F.hqr, F.hrr, F.inner_p_rot_p, F.inner_q_rot_p, F.inner_r_rot_p] <;> ring
  rw [h1, flip_r F heven hrotr _ (norm_rot F.hp (norm_rot F.hp hs)), hrotp _ (norm_rot F.hp hs),
    hrotp s hs, neg_neg]

/-- `h` vanishes on the great circle `⟪p, s⟫ = ⟪q, s⟫`. -/
lemma vanish_p_eq_q (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1)
    (hpq : ⟪p, s⟫_ℝ = ⟪q, s⟫_ℝ) : h s = 0 := by
  have h1 : s = reflect p (rot r s) := by
    refine F.eq_of_inner ?_ ?_ ?_ <;>
      simp only [reflect, inner_sub_right, real_inner_smul_right, F.hpp, F.hqp, F.hrp,
        F.inner_p_rot_r, F.inner_q_rot_r, F.inner_r_rot_r] <;> linarith
  have h2 : h s = -h s := by
    conv_lhs => rw [h1]
    rw [flip_p F heven hrotp _ (norm_rot F.hr hs), hrotr s hs]
  linarith

/-- `h` vanishes on the great circle `⟪p, s⟫ = −⟪q, s⟫`. -/
lemma vanish_p_eq_neg_q (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1)
    (hpq : ⟪p, s⟫_ℝ = -⟪q, s⟫_ℝ) : h s = 0 := by
  have h1 : s = reflect q (rot r s) := by
    refine F.eq_of_inner ?_ ?_ ?_ <;>
      simp only [reflect, inner_sub_right, real_inner_smul_right, F.hpq, F.hqq, F.hrq,
        F.inner_p_rot_r, F.inner_q_rot_r, F.inner_r_rot_r] <;> linarith
  have h2 : h s = -h s := by
    conv_lhs => rw [h1]
    rw [flip_q F heven hrotp hrotr _ (norm_rot F.hr hs), hrotr s hs]
  linarith

/-- `h` vanishes on the great circle `⟪q, s⟫ = ⟪r, s⟫`. -/
lemma vanish_q_eq_r (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1)
    (hqr : ⟪q, s⟫_ℝ = ⟪r, s⟫_ℝ) : h s = 0 := by
  have h1 : s = reflect q (rot p s) := by
    refine F.eq_of_inner ?_ ?_ ?_ <;>
      simp only [reflect, inner_sub_right, real_inner_smul_right, F.hpq, F.hqq, F.hrq,
        F.inner_p_rot_p, F.inner_q_rot_p, F.inner_r_rot_p] <;> linarith
  have h2 : h s = -h s := by
    conv_lhs => rw [h1]
    rw [flip_q F heven hrotp hrotr _ (norm_rot F.hp hs), hrotp s hs]
  linarith

/-- `h` vanishes on the great circle `⟪q, s⟫ = −⟪r, s⟫`. -/
lemma vanish_q_eq_neg_r (s : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1)
    (hqr : ⟪q, s⟫_ℝ = -⟪r, s⟫_ℝ) : h s = 0 := by
  have h1 : s = reflect r (rot p s) := by
    refine F.eq_of_inner ?_ ?_ ?_ <;>
      simp only [reflect, inner_sub_right, real_inner_smul_right, F.hpr, F.hqr, F.hrr,
        F.inner_p_rot_p, F.inner_q_rot_p, F.inner_r_rot_p] <;> linarith
  have h2 : h s = -h s := by
    conv_lhs => rw [h1]
    rw [flip_r F heven hrotr _ (norm_rot F.hp hs), hrotp s hs]
  linarith

end Zeros

/-! ### The core lemma -/

/-- ★★ **Gleason's core lemma (CKM, the Theorem of §3).** Every nonnegative frame function on
the unit sphere of `ℝ³` is the restriction of a symmetric quadratic form. -/
theorem frameFunction_regular_sphere (f : EuclideanSpace ℝ (Fin 3) → ℝ) {W : ℝ}
    (hf : IsFrameFunction ℝ f W) (h0 : ∀ x, ‖x‖ = 1 → 0 ≤ f x) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧ ∀ x, ‖x‖ = 1 → f x = ⇑x ⬝ᵥ (A *ᵥ ⇑x) := by
  have hW : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ W := fun u hu =>
    hf.le_weight_of_nonneg h0 hu
  -- the maximum `M = f p`
  obtain ⟨p, hp, hpM⟩ := hf.exists_forall_le hW h0
  -- the infimum `m`, attained at some `r ⟂ p`: minimise `f + ⟪p, ·⟫²`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = sphereInf f := ⟨_, rfl⟩
  have hmle : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u := fun u hu => by
    rw [hm]; exact sphereInf_le h0 hu
  have hf2 : IsFrameFunction ℝ (fun s => f s + ⟪p, s⟫_ℝ ^ 2) (W + 1) :=
    hf.add (isFrameFunction_inner_sq hp)
  obtain ⟨r, hr, hrmin⟩ := hf2.exists_forall_ge (M := W + 1) (m := m)
    (fun u hu => by
      show f u + ⟪p, u⟫_ℝ ^ 2 ≤ W + 1
      have := latitude_le_one hp hu
      rw [latitude] at this
      linarith [hW u hu])
    (fun u hu => by
      show m ≤ f u + ⟪p, u⟫_ℝ ^ 2
      linarith [hmle u hu, sq_nonneg ⟪p, u⟫_ℝ])
  have hr2 : f r + ⟪p, r⟫_ℝ ^ 2 ≤ m := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨t, ht, hpt, hft⟩ := hf.exists_orthogonal_lt hpM (m := m)
      (fun ε hε => by
        obtain ⟨u, hu, h⟩ := exists_lt_sphereInf_add (f := f) hε
        exact ⟨u, hu, by rw [hm]; exact h⟩) (ξ := δ) hp (by linarith)
    have h1 : f r + ⟪p, r⟫_ℝ ^ 2 ≤ f t + ⟪p, t⟫_ℝ ^ 2 := hrmin t ht
    rw [hpt, zero_pow two_ne_zero, add_zero] at h1
    linarith
  have hpr : ⟪p, r⟫_ℝ = 0 := by
    have := hmle r hr
    have h2 : ⟪p, r⟫_ℝ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp h2
  have hfr : f r = m := by
    have := hmle r hr
    rw [hpr, zero_pow two_ne_zero, add_zero] at hr2
    linarith
  have hrm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f r ≤ f u := fun u hu => by
    rw [hfr]; exact hmle u hu
  -- the frame `(p, q, r)`, the value `α = f q`, and the target form `g`
  obtain ⟨q, hq⟩ : ∃ q : EuclideanSpace ℝ (Fin 3), q = cross r p := ⟨_, rfl⟩
  have F : Frame p q r := ⟨hp, hr, hpr, hq⟩
  have hWsum : f p + f q + f r = W := hf.eq_of_triple F.orthonormal
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ, g = quadFrame (f p) (f q) (f r) p q r :=
    ⟨_, rfl⟩
  have hgframe : IsFrameFunction ℝ g (f p + f q + f r) := by
    rw [hg]; exact isFrameFunction_quadFrame F
  -- the pole identities for `f`
  have hfp := hf.add_rot_of_forall_le hp hpM
  have hfr' := hf.add_rot_of_forall_ge hr hrm
  -- `h = g − f` is negated by both rotations and is even
  obtain ⟨h, hh⟩ : ∃ h : EuclideanSpace ℝ (Fin 3) → ℝ, h = fun s => g s - f s := ⟨_, rfl⟩
  have hrotp : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h (rot p s) = -h s := by
    intro s hs
    have h1 := hfp s hs
    have h2 := quadFrame_add_rot_p F (M := f p) (α := f q) (m := f r) s hs
    rw [← hg] at h2
    rw [hh]
    show g (rot p s) - f (rot p s) = -(g s - f s)
    linear_combination h2 - h1 + (1 - latitude p s) * hWsum
  have hrotr : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h (rot r s) = -h s := by
    intro s hs
    have h1 := hfr' s hs
    have h2 := quadFrame_add_rot_r F (M := f p) (α := f q) (m := f r) s hs
    rw [← hg] at h2
    rw [hh]
    show g (rot r s) - f (rot r s) = -(g s - f s)
    linear_combination h2 - h1 + (1 - latitude r s) * hWsum
  have heven : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h (-s) = h s := by
    intro s hs
    rw [hh]
    show g (-s) - f (-s) = g s - f s
    rw [hf.neg_apply hs, hg, quadFrame_neg]
  have hhframe : IsFrameFunction ℝ h ((f p + f q + f r) - W) := by
    rw [hh]; exact hgframe.sub hf
  -- `h` vanishes on the sphere; otherwise its maximum `M' > 0` at `p'` contradicts the circle
  -- lemma on the four circles `x = ±y`, `y = ±z`
  have hzero : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h s = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀, hs₀0⟩ := hcon
    have hbdd_le : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → h u ≤ W := fun u hu => by
      have := quadFrame_le F (M := f p) (α := f q) (m := f r) (hW p hp) (hW q F.hq1)
        (hW r hr) u hu
      rw [← hg] at this
      rw [hh]
      show g u - f u ≤ W
      linarith [h0 u hu]
    have hbdd_ge : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → -W ≤ h u := fun u hu => by
      have := quadFrame_nonneg (p := p) (q := q) (r := r) (h0 p hp) (h0 q F.hq1) (h0 r hr) u
      rw [← hg] at this
      rw [hh]
      show -W ≤ g u - f u
      linarith [hW u hu]
    obtain ⟨p', hp', hp'M⟩ := hhframe.exists_forall_le hbdd_le hbdd_ge
    have hM'pos : 0 < h p' := by
      have h1 := hp'M s₀ hs₀
      have h2 := hp'M _ (norm_rot hp hs₀)
      rw [hrotp s₀ hs₀] at h2
      rcases lt_or_gt_of_ne hs₀0 with h3 | h3 <;> linarith
    -- the pole identity for `h` at `p'`
    have hid : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 →
        h s + h (rot p' s) = h p' * (3 * ⟪p', s⟫_ℝ ^ 2 - 1) := by
      intro s hs
      have := hhframe.add_rot_of_forall_le hp' hp'M s hs
      rw [this, latitude]
      have hW' : f p + f q + f r - W = 0 := by linarith
      rw [hW']
      ring
    -- the four circles of zeros are at latitude `1/2` from `p'`
    have hc2 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hc0 : (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
    have hnorm : ∀ a b : EuclideanSpace ℝ (Fin 3), ‖a‖ = 1 → ‖b‖ = 1 → ⟪a, b⟫_ℝ = 0 →
        ‖(Real.sqrt 2)⁻¹ • (a - b)‖ = 1 ∧ ‖(Real.sqrt 2)⁻¹ • (a + b)‖ = 1 := by
      intro a b ha hb hab
      have haa : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
      have hbb : ⟪b, b⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
      have hba : ⟪b, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hab
      constructor <;> refine norm_eq_one_of_real_inner_self ?_ <;>
        simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
          inner_add_left, inner_add_right, haa, hbb, hab, hba] <;>
        linear_combination 2 * hc2
    obtain ⟨hn1, hn2⟩ := hnorm p q hp F.hq1 F.hpq
    obtain ⟨hn3, hn4⟩ := hnorm q r F.hq1 hr F.hqr
    have hz1 := inner_sq_eq_half_of_vanish hp' hM'pos.ne' hid hn1 fun s hs hns => by
      rw [real_inner_smul_left, inner_sub_left] at hns
      have := (mul_eq_zero.mp hns).resolve_left hc0
      exact vanish_p_eq_q F heven hrotp hrotr s hs (by linarith)
    have hz2 := inner_sq_eq_half_of_vanish hp' hM'pos.ne' hid hn2 fun s hs hns => by
      rw [real_inner_smul_left, inner_add_left] at hns
      have := (mul_eq_zero.mp hns).resolve_left hc0
      exact vanish_p_eq_neg_q F heven hrotp hrotr s hs (by linarith)
    have hz3 := inner_sq_eq_half_of_vanish hp' hM'pos.ne' hid hn3 fun s hs hns => by
      rw [real_inner_smul_left, inner_sub_left] at hns
      have := (mul_eq_zero.mp hns).resolve_left hc0
      exact vanish_q_eq_r F heven hrotp hrotr s hs (by linarith)
    have hz4 := inner_sq_eq_half_of_vanish hp' hM'pos.ne' hid hn4 fun s hs hns => by
      rw [real_inner_smul_left, inner_add_left] at hns
      have := (mul_eq_zero.mp hns).resolve_left hc0
      exact vanish_q_eq_neg_r F heven hrotp hrotr s hs (by linarith)
    rw [real_inner_smul_right, inner_sub_right, mul_pow, hc2] at hz1
    rw [real_inner_smul_right, inner_add_right, mul_pow, hc2] at hz2
    rw [real_inner_smul_right, inner_sub_right, mul_pow, hc2] at hz3
    rw [real_inner_smul_right, inner_add_right, mul_pow, hc2] at hz4
    have hpar := F.sum_sq p'
    rw [hp', one_pow, real_inner_comm p' p, real_inner_comm p' q, real_inner_comm p' r] at hpar
    -- hence `⟪p', q⟫² = 1`, so `p' = ±q`, where `h` vanishes
    have hv : ⟪p', q⟫_ℝ ^ 2 = 1 := by linear_combination hz1 + hz2 + hz3 + hz4 - hpar
    have hp'q : p' = ⟪p', q⟫_ℝ • q := by
      have h2 : ‖p' - ⟪p', q⟫_ℝ • q‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, F.hq1, mul_one,
          Real.norm_eq_abs, sq_abs, hp', one_pow]
        linear_combination (-1 : ℝ) * hv
      exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))
    have hhq : h q = 0 := by
      rw [hh]
      show g q - f q = 0
      rw [hg, quadFrame, F.hpq, F.hqq, F.hrq]; ring
    have hvv : (⟪p', q⟫_ℝ - 1) * (⟪p', q⟫_ℝ + 1) = 0 := by linear_combination hv
    have hp'0 : h p' = 0 := by
      rcases mul_eq_zero.mp hvv with h1 | h1
      · rw [hp'q, sub_eq_zero.mp h1, one_smul]; exact hhq
      · rw [hp'q, show ⟪p', q⟫_ℝ = -1 by linarith, neg_one_smul, heven q F.hq1]; exact hhq
    linarith
  -- conclusion: `f = g` on the sphere, a symmetric quadratic form
  refine ⟨f p • vecMulVec (⇑p) (⇑p) + f q • vecMulVec (⇑q) (⇑q) + f r • vecMulVec (⇑r) (⇑r),
    ?_, fun x hx => ?_⟩
  · refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  · have := hzero x hx
    rw [hh] at this
    have h2 : g x - f x = 0 := this
    rw [← quadFrame_eq_dotProduct, ← hg]
    linarith

end Gleason

end
