/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.SimpleFrame
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Gleason's theorem, finite-dimensional: bounded frame functions attain their extremal values

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, stage
57(d): Cooke–Keane–Moran §6 — the second of the two risk points of the core lemma. A bounded
frame function on `S² ⊂ ℝ³` attains its supremum (★ `IsFrameFunction.exists_forall_le`) and its
infimum (`IsFrameFunction.exists_forall_ge`).

The argument, in the paper's four steps, with the Lean shape of each:

* **A maximising sequence and its limit.** `u n` with `f (u n) → sup f`; a convergent
  subsequence by compactness of the sphere (`IsCompact.tendsto_subseq`), limit `p`. Suppose
  `f p < sup f`; then eventually `u n ≠ p` and `⟪p, u n⟫ > 0`.
* **Step 1, changing coordinates.** For each `q` near `p`, a rigid motion `motion p e₀ e₁ q`
  with `motion p = q` and `motion c_q = p`, where `c_q` lies on the meridian of `e₀` at
  parameter `meridianParam p q = √(1 − ⟪p,q⟫²)/⟪p,q⟫` (`exists_motion`: the linear isometry
  sending the orthonormal basis `(c_q, d_q, e₁)` to `(p, d'_q, p × d'_q)`,
  `OrthonormalBasis.equiv`).
  `g_q = f ∘ motion` is again a frame function (`IsFrameFunction.comp_inner`).
* **Step 2, symmetrisation.** `rot p s = ⟪p, s⟫ p + p × s` is the `90°` rotation about `p`
  (`inner_rot_rot`); `symmetrise p g s = g s + g (rot p s)` is a frame function of weight `2W`,
  bounded by `2m` and `2M`, with `symmetrise p g p = 2 g p`, and **constant on the equator**
  (`symmetrise_equator`: the four-point identity for the orthonormal pairs `(e, p × e)`).
* **Step 3, the limit.** The functions `H n = symmetrise p g_{u n}` restricted to the sphere lie
  in the compact box `[2m, 2M]^{S²}` (Tychonoff, `isCompact_univ_pi`); a cluster point `h₀`
  (`IsCompact.exists_clusterPt`) is a frame function, is at most `2M`, is constant on the
  equator (closed conditions, `mem_of_clusterPt`), and has `h₀ p = 2 sup f`
  (`eq_of_clusterPt_of_tendsto`). By the simple-frame-function theorem
  (`IsFrameFunction.eq_add_mul_latitude`) it is `m' + (2 sup f − m') ⟪p, ·⟫²`.
* **Step 4.** A fixed point `c⋆` on the meridian of `e₀` close to `p` has `h₀ c⋆ > 2 sup f − ε`,
  and frequently `H n c⋆` is within `ε` of it (`clusterPt_iff_frequently`); for such an `n`
  large enough, `c_{u n}` is higher than `c⋆` on the same meridian, so `c⋆` is reached from
  `c_{u n}` in two descents (`descent_step_ray`), and the approximate basic lemma
  (`IsFrameFunction.descent_lt_add`) gives `H n c_{u n} > H n c⋆ − 6ε`; but
  `H n c_{u n} = f p + f (…) ≤ f p + sup f`. Hence `f p > sup f − 8ε` for every `ε`, the
  contradiction.

## Source

Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117–128, §6.
-/

@[expose] public section

open Matrix Real Filter Topology
open scoped Matrix InnerProductSpace

namespace Gleason

/-! ### The `90°` rotation about the pole -/

/-- The right-hand rotation by `90°` about `p`: `s ↦ ⟪p, s⟫ p + p × s`. -/
noncomputable def rot (p s : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  ⟪p, s⟫_ℝ • p + cross p s

lemma cross_self' (v : EuclideanSpace ℝ (Fin 3)) : cross v v = 0 := by
  rw [cross, cross_self]; rfl

/-- A vector with `⟪v, v⟫ = 1` is a unit vector. -/
lemma norm_eq_one_of_real_inner_self {v : EuclideanSpace ℝ (Fin 3)} (h : ⟪v, v⟫_ℝ = 1) :
    ‖v‖ = 1 := by
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v]

section Rot

variable {p : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1)
include hp

/-- The rotation preserves inner products (Lagrange's identity). -/
lemma inner_rot_rot (x y : EuclideanSpace ℝ (Fin 3)) :
    ⟪rot p x, rot p y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have h1 : ⟪cross p x, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact inner_cross_left p x
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  simp only [rot, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hpp,
    inner_cross_left, h1, inner_cross_cross, RCLike.conj_to_real]
  rw [real_inner_comm x p]
  ring

lemma norm_rot {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : ‖rot p s‖ = 1 := by
  refine norm_eq_one_of_real_inner_self ?_
  rw [inner_rot_rot hp, real_inner_self_eq_norm_sq, hs]; norm_num

lemma rot_pole : rot p p = p := by
  rw [rot, real_inner_self_eq_norm_sq, hp, cross_self']
  simp

lemma rot_mem_equator {e : EuclideanSpace ℝ (Fin 3)} (he : e ∈ equator p) :
    rot p e ∈ equator p := by
  have h : rot p e = cross p e := by rw [rot, he.2, zero_smul, zero_add]
  rw [h]
  exact ⟨norm_cross_of_orthonormal hp he.1 he.2, inner_cross_left p e⟩

omit hp in
lemma inner_rot_of_equator {e : EuclideanSpace ℝ (Fin 3)} (he : e ∈ equator p) :
    ⟪e, rot p e⟫_ℝ = 0 := by
  rw [rot, he.2, zero_smul, zero_add]
  exact inner_cross_right p e

end Rot

/-! ### Frame functions composed with inner-product-preserving maps; symmetrisation -/

namespace IsFrameFunction

variable {f g : EuclideanSpace ℝ (Fin 3) → ℝ} {W : ℝ}

/-- A frame function composed with an inner-product-preserving map is a frame function of the
same weight. -/
theorem comp_inner (hf : IsFrameFunction ℝ f W)
    {T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hT : ∀ x y, ⟪T x, T y⟫_ℝ = ⟪x, y⟫_ℝ) : IsFrameFunction ℝ (fun s => f (T s)) W := by
  intro b
  have hb : Orthonormal ℝ fun i => T (b i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hT]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  exact hf.sum_triple hb

end IsFrameFunction

/-- **Symmetrisation about the pole:** `g s + g (rot p s)`. -/
noncomputable def symmetrise (p : EuclideanSpace ℝ (Fin 3)) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (s : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  g s + g (rot p s)

section Symmetrise

variable {p : EuclideanSpace ℝ (Fin 3)} {g : EuclideanSpace ℝ (Fin 3) → ℝ} {W m M : ℝ}

theorem IsFrameFunction.symmetrise (hg : IsFrameFunction ℝ g W) (hp : ‖p‖ = 1) :
    IsFrameFunction ℝ (Gleason.symmetrise p g) (W + W) :=
  hg.add (hg.comp_inner (inner_rot_rot hp))

lemma symmetrise_pole (hp : ‖p‖ = 1) : symmetrise p g p = 2 * g p := by
  rw [symmetrise, rot_pole hp]; ring

lemma symmetrise_le (hp : ‖p‖ = 1) (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → g u ≤ M)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : symmetrise p g s ≤ 2 * M := by
  have := hM s hs
  have := hM _ (norm_rot hp hs)
  rw [symmetrise]; linarith

lemma le_symmetrise (hp : ‖p‖ = 1) (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ g u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : 2 * m ≤ symmetrise p g s := by
  have := hm s hs
  have := hm _ (norm_rot hp hs)
  rw [symmetrise]; linarith

/-- **The symmetrisation is constant on the equator** (the four-point identity for the
orthonormal pairs `(e, p × e)`). -/
lemma symmetrise_equator (hg : IsFrameFunction ℝ g W) (hp : ‖p‖ = 1)
    {e e' : EuclideanSpace ℝ (Fin 3)} (he : e ∈ equator p) (he' : e' ∈ equator p) :
    symmetrise p g e = symmetrise p g e' := by
  have hre := rot_mem_equator hp he
  have hre' := rot_mem_equator hp he'
  exact hg.four_point hp he.1 hre.1 he'.1 hre'.1 (by rw [real_inner_comm]; exact he.2)
    (by rw [real_inner_comm]; exact hre.2) (by rw [real_inner_comm]; exact he'.2)
    (by rw [real_inner_comm]; exact hre'.2) (inner_rot_of_equator he) (inner_rot_of_equator he')

end Symmetrise

/-! ### The rigid motion taking the pole to a nearby point -/

/-- The meridian parameter of `q`: the tangent coordinate `√(1 − ⟪p,q⟫²)/⟪p,q⟫` of the point
of the meridian of `e₀` at the latitude of `q`. -/
noncomputable def meridianParam (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.sqrt (1 - ⟪p, q⟫_ℝ ^ 2) / ⟪p, q⟫_ℝ

/-- The tangent vector with a real coordinate. -/
lemma tangent_ofReal (e₁ e₂ : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    tangent e₁ e₂ (r : ℂ) = r • e₁ := by
  simp [tangent]

/-- The strict form of `latitude_le_one`: off the pole, `⟪p, q⟫ < 1` on the northern
hemisphere. -/
lemma inner_lt_one_of_ne {p q : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1) (hq : q ∈ northern p)
    (hqp : q ≠ p) : ⟪p, q⟫_ℝ < 1 := by
  have h1 := latitude_le_one hp hq.1
  rcases eq_or_lt_of_le h1 with h | h
  · exact absurd (eq_pole_of_latitude_eq_one hp hq h) hqp
  · rw [latitude] at h
    nlinarith [hq.2]

/-- **The rigid motion (CKM §6, Step 1).** For a unit `q ≠ p` in the open northern hemisphere
there is an inner-product-preserving `T` with `T p = q` and `T c_q = p`, where `c_q` is the point
of the meridian of `e₀` with tangent coordinate `meridianParam p q`. -/
theorem exists_motion {p e₀ e₁ : EuclideanSpace ℝ (Fin 3)} (he : Orthonormal ℝ ![p, e₀, e₁])
    {q : EuclideanSpace ℝ (Fin 3)} (hq : ‖q‖ = 1) (hpq : 0 < ⟪p, q⟫_ℝ) (hqp : q ≠ p) :
    ∃ T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ x y, ⟪T x, T y⟫_ℝ = ⟪x, y⟫_ℝ) ∧ T p = q ∧
        T (lift p (tangent e₀ e₁ (meridianParam p q : ℂ))) = p := by
  obtain ⟨hp, he₀, he₁, hpe₀, hpe₁, he₀e₁⟩ := orthonormal_triple_iff.mp he
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  have h00 : ⟪e₀, e₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he₀]; norm_num
  have h11 : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he₁]; norm_num
  have he₀p : ⟪e₀, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact hpe₀
  have he₁p : ⟪e₁, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact hpe₁
  have he₁e₀ : ⟪e₁, e₀⟫_ℝ = 0 := by rw [real_inner_comm]; exact he₀e₁
  -- the coefficients `a = ⟪p, q⟫`, `b = √(1 − a²)`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ⟪p, q⟫_ℝ := ⟨_, rfl⟩
  have ha0 : 0 < a := ha ▸ hpq
  have ha1 : a < 1 := ha ▸ inner_lt_one_of_ne hp ⟨hq, hpq.le⟩ hqp
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Real.sqrt (1 - a ^ 2) := ⟨_, rfl⟩
  have hb0 : 0 < b := hb ▸ Real.sqrt_pos.mpr ha2
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [hb, Real.sq_sqrt ha2.le]; ring
  -- `w = q − a p ⟂ p` has norm `b`
  have hqp' : ⟪q, p⟫_ℝ = a := by rw [real_inner_comm, ha]
  have hw : ⟪p, q - a • p⟫_ℝ = 0 := by
    rw [inner_sub_right, inner_smul_right, hpp, ← ha]; ring
  have hwn : ‖q - a • p‖ = b := by
    have h : ‖q - a • p‖ ^ 2 = b ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, hqp', norm_smul, hq, hp, Real.norm_eq_abs,
        abs_of_pos ha0]
      linear_combination (-1 : ℝ) * hab
    exact (sq_eq_sq₀ (norm_nonneg _) hb0.le).mp h
  -- the first frame `(c, d, e₁)` and the second `(p, d', p × d')`
  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin 3), c = a • p + b • e₀ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : EuclideanSpace ℝ (Fin 3), d = (-b) • p + a • e₀ := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : EuclideanSpace ℝ (Fin 3), d' = b⁻¹ • (a • p - q) := ⟨_, rfl⟩
  have hcc : ⟪c, c⟫_ℝ = 1 := by
    simp only [hc, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hpp, h00,
      hpe₀, he₀p, RCLike.conj_to_real]
    linear_combination hab
  have hdd : ⟪d, d⟫_ℝ = 1 := by
    simp only [hd, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hpp, h00,
      hpe₀, he₀p, RCLike.conj_to_real]
    linear_combination hab
  have hcd : ⟪c, d⟫_ℝ = 0 := by
    simp only [hc, hd, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hpp,
      h00, hpe₀, he₀p, RCLike.conj_to_real]
    ring
  have hce₁ : ⟪c, e₁⟫_ℝ = 0 := by
    simp only [hc, inner_add_left, inner_smul_left, hpe₁, he₀e₁, RCLike.conj_to_real]; ring
  have hde₁ : ⟪d, e₁⟫_ℝ = 0 := by
    simp only [hd, inner_add_left, inner_smul_left, hpe₁, he₀e₁, RCLike.conj_to_real]; ring
  have h1 : Orthonormal ℝ ![c, d, e₁] :=
    orthonormal_triple_iff.mpr ⟨norm_eq_one_of_real_inner_self hcc,
      norm_eq_one_of_real_inner_self hdd, he₁, hcd, hce₁, hde₁⟩
  have hd'n : ‖d'‖ = 1 := by
    rw [hd', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb0), ← neg_sub, norm_neg,
      hwn, inv_mul_cancel₀ hb0.ne']
  have hpd' : ⟪p, d'⟫_ℝ = 0 := by
    rw [hd', inner_smul_right, ← neg_sub, inner_neg_right, hw]; ring
  have h2 : Orthonormal ℝ ![p, d', cross p d'] := orthonormal_cross hp hd'n hpd'
  -- the isometry sending the first frame to the second
  obtain ⟨T, hT⟩ : ∃ T : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      T = (orthonormalBasisOfTriple h1).equiv (orthonormalBasisOfTriple h2) (Equiv.refl _) :=
    ⟨_, rfl⟩
  have hTc : T c = p := by
    have := (orthonormalBasisOfTriple h1).equiv_apply_basis (orthonormalBasisOfTriple h2)
      (Equiv.refl _) 0
    simpa [hT, coe_orthonormalBasisOfTriple] using this
  have hTd : T d = d' := by
    have := (orthonormalBasisOfTriple h1).equiv_apply_basis (orthonormalBasisOfTriple h2)
      (Equiv.refl _) 1
    simpa [hT, coe_orthonormalBasisOfTriple] using this
  -- `p = a c − b d`, so `T p = a p − b d' = q`
  have hpcd : p = a • c - b • d := by
    rw [hc, hd, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      show b * -b = -(b * b) by ring, neg_smul, mul_comm b a]
    calc p = (a * a + b * b) • p := by
          rw [show a * a + b * b = 1 by nlinarith [hab], one_smul]
      _ = _ := by rw [add_smul]; abel
  refine ⟨T, fun x y => T.inner_map_map x y, ?_, ?_⟩
  · rw [hpcd, map_sub, map_smul, map_smul, hTc, hTd, hd', smul_smul, mul_inv_cancel₀ hb0.ne',
      one_smul]
    abel
  · -- `c` is the lift of the meridian point
    have hr : meridianParam p q = b / a := by rw [meridianParam, ← ha, ← hb]
    have hlift : lift p (tangent e₀ e₁ (meridianParam p q : ℂ)) = c := by
      rw [tangent_ofReal, hr]
      have hv : ⟪p, (b / a) • e₀⟫_ℝ = 0 := by rw [inner_smul_right, hpe₀, mul_zero]
      have hn2 : ‖p + (b / a) • e₀‖ ^ 2 = (a⁻¹) ^ 2 := by
        rw [norm_sq_add_of_inner_zero hp hv, norm_smul, he₀, mul_one, Real.norm_eq_abs,
          abs_of_pos (div_pos hb0 ha0), div_pow, inv_pow, inv_eq_one_div,
          eq_div_iff (pow_ne_zero 2 ha0.ne'), add_mul, one_mul,
          div_mul_cancel₀ _ (pow_ne_zero 2 ha0.ne')]
        exact hab
      have hn : ‖p + (b / a) • e₀‖ = a⁻¹ :=
        (sq_eq_sq₀ (norm_nonneg _) (inv_pos.mpr ha0).le).mp hn2
      rw [lift, hn, inv_inv, smul_add, smul_smul, mul_div_cancel₀ _ ha0.ne', hc]
    rw [hlift, hTc]

open Classical in
/-- **The rigid motion**, as a total function: the choice of `exists_motion` where its
hypotheses hold, the identity elsewhere. -/
noncomputable def motion (p e₀ e₁ q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  if h : Orthonormal ℝ ![p, e₀, e₁] ∧ ‖q‖ = 1 ∧ 0 < ⟪p, q⟫_ℝ ∧ q ≠ p then
    Classical.choose (exists_motion h.1 h.2.1 h.2.2.1 h.2.2.2)
  else id

section Motion

variable {p e₀ e₁ q : EuclideanSpace ℝ (Fin 3)}

/-- The motion always preserves inner products. -/
lemma motion_inner (p e₀ e₁ q x y : EuclideanSpace ℝ (Fin 3)) :
    ⟪motion p e₀ e₁ q x, motion p e₀ e₁ q y⟫_ℝ = ⟪x, y⟫_ℝ := by
  unfold motion
  split_ifs with h
  · exact (Classical.choose_spec (exists_motion h.1 h.2.1 h.2.2.1 h.2.2.2)).1 x y
  · rfl

lemma norm_motion (p e₀ e₁ q : EuclideanSpace ℝ (Fin 3)) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ‖x‖ = 1) : ‖motion p e₀ e₁ q x‖ = 1 := by
  refine norm_eq_one_of_real_inner_self ?_
  rw [motion_inner, real_inner_self_eq_norm_sq, hx]; norm_num

lemma motion_pole (he : Orthonormal ℝ ![p, e₀, e₁]) (hq : ‖q‖ = 1) (hpq : 0 < ⟪p, q⟫_ℝ)
    (hqp : q ≠ p) : motion p e₀ e₁ q p = q := by
  unfold motion
  rw [dif_pos ⟨he, hq, hpq, hqp⟩]
  exact (Classical.choose_spec (exists_motion he hq hpq hqp)).2.1

lemma motion_meridian (he : Orthonormal ℝ ![p, e₀, e₁]) (hq : ‖q‖ = 1) (hpq : 0 < ⟪p, q⟫_ℝ)
    (hqp : q ≠ p) :
    motion p e₀ e₁ q (lift p (tangent e₀ e₁ (meridianParam p q : ℂ))) = p := by
  unfold motion
  rw [dif_pos ⟨he, hq, hpq, hqp⟩]
  exact (Classical.choose_spec (exists_motion he hq hpq hqp)).2.2

end Motion

/-! ### Cluster points -/

/-- A cluster point of a filter supported in a closed set lies in it. -/
lemma mem_of_clusterPt {X : Type*} [TopologicalSpace X] {F : Filter X} {x : X} {K : Set X}
    (hx : ClusterPt x F) (hK : IsClosed K) (hF : F ≤ 𝓟 K) : x ∈ K := by
  have := hx.mono hF
  rwa [← mem_closure_iff_clusterPt, hK.closure_eq] at this

/-- In a Hausdorff space, a cluster point of a convergent filter is its limit. -/
lemma eq_of_clusterPt_of_tendsto {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*}
    {l : Filter ι} {u : ι → X} {x y : X} (hx : ClusterPt x (map u l))
    (hy : Tendsto u l (𝓝 y)) : x = y :=
  eq_of_nhds_neBot (hx.mono hy)

/-! ### Bounded frame functions attain their extremal values -/

namespace IsFrameFunction

variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W : ℝ}

/-- ★ **Bounded frame functions attain their supremum (CKM §6, Theorem).** -/
theorem exists_forall_le (hf : IsFrameFunction ℝ f W) {M m : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u) :
    ∃ p : EuclideanSpace ℝ (Fin 3), ‖p‖ = 1 ∧
      ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p := by
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = sphereSup f := ⟨_, rfl⟩
  have hM'le : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M' :=
    fun u hu => hM' ▸ le_sphereSup hM hu
  -- a maximising sequence and a convergent subsequence
  have hseq : ∀ n : ℕ, ∃ u : EuclideanSpace ℝ (Fin 3),
      ‖u‖ = 1 ∧ M' - 1 / ((n : ℝ) + 1) < f u := by
    intro n
    obtain ⟨u, hu, h⟩ := exists_sphereSup_sub_lt (f := f) (δ := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨u, hu, hM' ▸ h⟩
  choose v hv1 hv2 using hseq
  obtain ⟨p, hpS, φ, hφ, hlim⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).tendsto_subseq (x := v)
      (fun n => mem_sphere_zero_iff_norm.mpr (hv1 n))
  have hp : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hpS
  obtain ⟨u, hu⟩ : ∃ u : ℕ → EuclideanSpace ℝ (Fin 3), u = v ∘ φ := ⟨_, rfl⟩
  have hu1 : ∀ n, ‖u n‖ = 1 := fun n => by rw [hu]; exact hv1 (φ n)
  have hul : Tendsto u atTop (𝓝 p) := hu ▸ hlim
  have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 M') := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n : ℕ => M' - 1 / ((φ n : ℝ) + 1)) (h := fun _ => M') ?_ tendsto_const_nhds ?_ ?_
    · have h1 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using h1.const_sub M'
    · intro n; rw [hu]; exact (hv2 (φ n)).le
    · intro n; exact hM'le _ (hu1 n)
  refine ⟨p, hp, fun w hw => ?_⟩
  suffices hfp : M' ≤ f p from (hM'le w hw).trans hfp
  by_contra hlt
  push Not at hlt
  -- eventually the sequence avoids the pole and lies in its open hemisphere
  have hev_ne : ∀ᶠ n in atTop, u n ≠ p :=
    (hfu.eventually_const_lt hlt).mono fun n hn hne => by rw [hne] at hn; exact lt_irrefl _ hn
  have hinner : Tendsto (fun n => ⟪p, u n⟫_ℝ) atTop (𝓝 ⟪p, p⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto p).comp hul
  rw [real_inner_self_eq_norm_sq, hp, one_pow] at hinner
  have hev_pos : ∀ᶠ n in atTop, 0 < ⟪p, u n⟫_ℝ := hinner.eventually_const_lt zero_lt_one
  -- Step 1: the frame at the pole and the moved frame functions
  obtain ⟨e₀, he₀, hpe₀⟩ := exists_unit_orthogonal p
  have he : Orthonormal ℝ ![p, e₀, cross p e₀] := orthonormal_cross hp he₀ hpe₀
  obtain ⟨g, hg⟩ : ∃ g : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ,
      g = fun n x => f (motion p e₀ (cross p e₀) (u n) x) := ⟨_, rfl⟩
  have hgframe : ∀ n, IsFrameFunction ℝ (g n) W := fun n => by
    rw [hg]; exact hf.comp_inner (motion_inner p e₀ (cross p e₀) (u n))
  have hgle : ∀ n x, ‖x‖ = 1 → g n x ≤ M' := fun n x hx => by
    rw [hg]; exact hM'le _ (norm_motion _ _ _ _ hx)
  have hgge : ∀ n x, ‖x‖ = 1 → m ≤ g n x := fun n x hx => by
    rw [hg]; exact hm _ (norm_motion _ _ _ _ hx)
  -- Step 2: symmetrise
  have hsym : ∀ n, IsFrameFunction ℝ (Gleason.symmetrise p (g n)) (W + W) :=
    fun n => (hgframe n).symmetrise hp
  -- Step 3: a cluster point in the box `[2m, 2M']^{S²}`
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ({s : EuclideanSpace ℝ (Fin 3) // ‖s‖ = 1} → ℝ),
      H = fun n s => Gleason.symmetrise p (g n) s.1 := ⟨_, rfl⟩
  have hbox : ∀ n, H n ∈ Set.pi Set.univ
      (fun _ : {s : EuclideanSpace ℝ (Fin 3) // ‖s‖ = 1} => Set.Icc (2 * m) (2 * M')) := by
    intro n
    rw [Set.mem_univ_pi]
    intro s
    rw [hH]
    exact ⟨le_symmetrise hp (hgge n) s.2, symmetrise_le hp (hgle n) s.2⟩
  obtain ⟨h₀, hh₀box, hh₀⟩ :=
    (isCompact_univ_pi fun _ : {s : EuclideanSpace ℝ (Fin 3) // ‖s‖ = 1} =>
      isCompact_Icc (a := 2 * m) (b := 2 * M')).exists_clusterPt (f := map H atTop)
      (by rw [le_principal_iff, mem_map]; exact univ_mem' hbox)
  rw [Set.mem_univ_pi] at hh₀box
  have hcp : ∀ s : {s : EuclideanSpace ℝ (Fin 3) // ‖s‖ = 1},
      ClusterPt (h₀ s) (map (fun n => H n s) atTop) := fun s => by
    have := hh₀.map (continuous_apply s).continuousAt tendsto_map
    rwa [Filter.map_map] at this
  -- the cluster point, extended to a function on the space
  obtain ⟨h, hh⟩ : ∃ h : EuclideanSpace ℝ (Fin 3) → ℝ,
      h = fun s => if hs : ‖s‖ = 1 then h₀ ⟨s, hs⟩ else 0 := ⟨_, rfl⟩
  have hhs : ∀ s (hs : ‖s‖ = 1), h s = h₀ ⟨s, hs⟩ := fun s hs => by rw [hh]; exact dif_pos hs
  have hhframe : IsFrameFunction ℝ h (W + W) := by
    intro b
    have hb : ∀ i, ‖b i‖ = 1 := b.orthonormal.norm_eq_one
    rw [Fin.sum_univ_three, hhs _ (hb 0), hhs _ (hb 1), hhs _ (hb 2)]
    refine mem_of_clusterPt (K := {x : {s : EuclideanSpace ℝ (Fin 3) // ‖s‖ = 1} → ℝ |
        x ⟨b 0, hb 0⟩ + x ⟨b 1, hb 1⟩ + x ⟨b 2, hb 2⟩ = W + W}) hh₀
      (isClosed_eq (by fun_prop) continuous_const) ?_
    rw [le_principal_iff, mem_map]
    refine univ_mem' fun n => ?_
    show H n ⟨b 0, hb 0⟩ + H n ⟨b 1, hb 1⟩ + H n ⟨b 2, hb 2⟩ = W + W
    have := (hsym n) b
    rw [Fin.sum_univ_three] at this
    rw [hH]
    exact this
  have hhle : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → h s ≤ 2 * M' := fun s hs => by
    rw [hhs s hs]; exact (hh₀box ⟨s, hs⟩).2
  have hhge : ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → 2 * m ≤ h s := fun s hs => by
    rw [hhs s hs]; exact (hh₀box ⟨s, hs⟩).1
  have hhp : h p = 2 * M' := by
    rw [hhs p hp]
    have hev : ∀ᶠ n in atTop, H n ⟨p, hp⟩ = 2 * f (u n) := by
      filter_upwards [hev_ne, hev_pos] with n hne hpos
      rw [hH]
      show Gleason.symmetrise p (g n) p = 2 * f (u n)
      rw [symmetrise_pole hp, hg]
      show 2 * f (motion p e₀ (cross p e₀) (u n) p) = 2 * f (u n)
      rw [motion_pole he (hu1 n) hpos hne]
    have ht : Tendsto (fun n => H n ⟨p, hp⟩) atTop (𝓝 (2 * M')) :=
      (hfu.const_mul 2).congr' (hev.mono fun n hn => hn.symm)
    exact eq_of_clusterPt_of_tendsto (hcp ⟨p, hp⟩) ht
  have hhE : ∀ e ∈ equator p, h e = h e₀ := by
    intro e he'
    rw [hhs e he'.1, hhs e₀ he₀]
    refine mem_of_clusterPt (K := {x : {s : EuclideanSpace ℝ (Fin 3) // ‖s‖ = 1} → ℝ |
        x ⟨e, he'.1⟩ = x ⟨e₀, he₀⟩}) hh₀ (isClosed_eq (continuous_apply _) (continuous_apply _)) ?_
    rw [le_principal_iff, mem_map]
    refine univ_mem' fun n => ?_
    show H n ⟨e, he'.1⟩ = H n ⟨e₀, he₀⟩
    rw [hH]
    exact symmetrise_equator (hgframe n) hp he' ⟨he₀, hpe₀⟩
  -- the simple-frame-function theorem for the cluster point
  have hkey := hhframe.eq_add_mul_latitude hp (fun w hw => (hhle w hw).trans_eq hhp.symm) hhE
  -- Step 4: the fixed point `c` on the meridian of `e₀`, close to the pole
  have hmM : m ≤ M' := (hm p hp).trans (hM'le p hp)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (M' - f p) / 8 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (M' - m) + 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (ε / D) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr (div_pos hε0 (by linarith))
  have hr2 : r ^ 2 = ε / D := by rw [hr]; exact Real.sq_sqrt (div_pos hε0 (by linarith)).le
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin 3),
      c = lift p (tangent e₀ (cross p e₀) (r : ℂ)) := ⟨_, rfl⟩
  have hcN : c ∈ northern p ∧ c ≠ p := by rw [hc]; exact lift_tangent_mem he (r : ℂ) hrC
  have hlat : latitude p c = 1 / (1 + r ^ 2) := by
    rw [hc, latitude_lift hp (inner_pole_tangent he _), norm_tangent he, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0]
  have hhc : 2 * M' - ε < h c := by
    have h1 := hkey c hcN.1.1
    rw [hlat, hhp] at h1
    have hm' : 2 * m ≤ h e₀ := hhge e₀ he₀
    have h1r : (1 : ℝ) + r ^ 2 ≠ 0 := by positivity
    have h2 : h c = 2 * M' - (2 * M' - h e₀) * (r ^ 2 / (1 + r ^ 2)) := by
      rw [h1]; field_simp; ring
    rw [h2]
    have h3 : (2 * M' - h e₀) * (r ^ 2 / (1 + r ^ 2)) ≤ (D - 1) * r ^ 2 := by
      have hq : r ^ 2 / (1 + r ^ 2) ≤ r ^ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
      have : 2 * M' - h e₀ ≤ D - 1 := by rw [hD]; linarith
      exact mul_le_mul this hq (by positivity) (by rw [hD]; linarith)
    have h4 : (D - 1) * r ^ 2 < ε := by
      rw [hr2, mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  -- frequently the moved frame function is close to the cluster point at `c`
  have hfreq : ∃ᶠ n in atTop, h₀ ⟨c, hcN.1.1⟩ - ε < H n ⟨c, hcN.1.1⟩ := by
    have := (clusterPt_iff_frequently.mp (hcp ⟨c, hcN.1.1⟩)) (Set.Ioi (h₀ ⟨c, hcN.1.1⟩ - ε))
      (Ioi_mem_nhds (by linarith))
    rwa [frequently_map] at this
  -- eventually the moved pole is higher than `c` on the same meridian
  have hev_r : ∀ᶠ n in atTop, meridianParam p (u n) < r := by
    have hsq : Tendsto (fun n => ⟪p, u n⟫_ℝ ^ 2) atTop (𝓝 ((1 : ℝ) ^ 2)) := hinner.pow 2
    rw [one_pow] at hsq
    have hlt1 : 1 / (1 + r ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg r]
    filter_upwards [hsq.eventually_const_lt hlt1, hev_pos] with n hn hpos
    rw [meridianParam, div_lt_iff₀ hpos, Real.sqrt_lt' (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  have hev_f : ∀ᶠ n in atTop, M' - ε < f (u n) := hfu.eventually_const_lt (by linarith)
  obtain ⟨n, hn1, hne, hpos, hnr, hnf⟩ :=
    (hfreq.and_eventually (hev_ne.and (hev_pos.and (hev_r.and hev_f)))).exists
  -- the two-step descent from the moved pole `cₙ` down to `c`
  obtain ⟨rn, hrn⟩ : ∃ rn : ℝ, rn = meridianParam p (u n) := ⟨_, rfl⟩
  have hrn0 : 0 < rn := by
    rw [hrn, meridianParam]
    refine div_pos (Real.sqrt_pos.mpr ?_) hpos
    have := inner_lt_one_of_ne hp ⟨hu1 n, hpos.le⟩ hne
    nlinarith
  have hrnC : (rn : ℂ) ≠ 0 := by exact_mod_cast hrn0.ne'
  obtain ⟨cn, hcn⟩ : ∃ cn : EuclideanSpace ℝ (Fin 3),
      cn = lift p (tangent e₀ (cross p e₀) (rn : ℂ)) := ⟨_, rfl⟩
  have hcnN : cn ∈ northern p ∧ cn ≠ p := by rw [hcn]; exact lift_tangent_mem he (rn : ℂ) hrnC
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = rn / r := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos hrn0 hr0
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hr0, hrn]; exact hnr.le
  obtain ⟨hst1, hst2⟩ := descent_step_ray (r : ℂ) hρ0 hρ1
  have hρr : (ρ : ℂ) * (r : ℂ) = (rn : ℂ) := by
    rw [← Complex.ofReal_mul, hρ, div_mul_cancel₀ _ hr0.ne']
  obtain ⟨z', hz'⟩ : ∃ z' : ℂ,
      z' = (ρ : ℂ) * (r : ℂ) * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I) := ⟨_, rfl⟩
  have hz'0 : z' ≠ 0 := by
    rw [hz']
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ0.ne') hrC) ?_
    intro h0
    have := congrArg Complex.re h0
    simp at this
  rw [← hz'] at hst1 hst2
  obtain ⟨zp, hzp⟩ : ∃ zp : EuclideanSpace ℝ (Fin 3),
      zp = lift p (tangent e₀ (cross p e₀) z') := ⟨_, rfl⟩
  have hzpN : zp ∈ northern p ∧ zp ≠ p := by rw [hzp]; exact lift_tangent_mem he z' hz'0
  have hstep1 : zp ∈ descent p cn := by
    rw [hzp, hcn, ← hρr, lift_tangent_mem_descent_iff he
      (mul_ne_zero (by exact_mod_cast hρ0.ne') hrC)]
    exact hst1
  have hstep2 : c ∈ descent p zp := by
    rw [hc, hzp, lift_tangent_mem_descent_iff he hz'0]
    exact hst2
  -- the approximate basic lemma for the symmetrised moved frame function, twice
  have hsle : ∀ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 → Gleason.symmetrise p (g n) w ≤ 2 * M' :=
    fun w hw => symmetrise_le hp (hgle n) hw
  have hspole : 2 * M' - 3 * ε < Gleason.symmetrise p (g n) p := by
    rw [symmetrise_pole hp, hg]
    show 2 * M' - 3 * ε < 2 * f (motion p e₀ (cross p e₀) (u n) p)
    rw [motion_pole he (hu1 n) hpos hne]
    linarith
  have hsE : ∀ e ∈ equator p, Gleason.symmetrise p (g n) e = Gleason.symmetrise p (g n) e₀ :=
    fun e he' => symmetrise_equator (hgframe n) hp he' ⟨he₀, hpe₀⟩
  have hA := (hsym n).descent_lt_add hp hsle hspole hsE hzpN.1 hzpN.2 hstep2
  have hB := (hsym n).descent_lt_add hp hsle hspole hsE hcnN.1 hcnN.2 hstep1
  -- the value at the moved pole is at most `f p + M'`
  have hcn_le : Gleason.symmetrise p (g n) cn ≤ f p + M' := by
    rw [Gleason.symmetrise, hg]
    show f (motion p e₀ (cross p e₀) (u n) cn)
      + f (motion p e₀ (cross p e₀) (u n) (rot p cn)) ≤ f p + M'
    rw [hcn, hrn, motion_meridian he (hu1 n) hpos hne, ← hrn, ← hcn]
    have := hM'le _ (norm_motion p e₀ (cross p e₀) (u n) (norm_rot hp hcnN.1.1))
    linarith
  have hHc : H n ⟨c, hcN.1.1⟩ = Gleason.symmetrise p (g n) c := by rw [hH]
  rw [hHc, ← hhs c hcN.1.1] at hn1
  linarith

/-- **Bounded frame functions attain their infimum.** -/
theorem exists_forall_ge (hf : IsFrameFunction ℝ f W) {M m : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u) :
    ∃ p : EuclideanSpace ℝ (Fin 3), ‖p‖ = 1 ∧
      ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f p ≤ f u := by
  obtain ⟨p, hp, h⟩ := hf.neg.exists_forall_le (M := -m) (m := -M)
    (fun u hu => by linarith [hm u hu]) (fun u hu => by linarith [hM u hu])
  refine ⟨p, hp, fun u hu => ?_⟩
  have := h u hu
  linarith

/-- A bounded frame function attains `sphereSup`. -/
theorem exists_eq_sphereSup (hf : IsFrameFunction ℝ f W) {M m : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u) :
    ∃ p : EuclideanSpace ℝ (Fin 3), ‖p‖ = 1 ∧ f p = sphereSup f := by
  obtain ⟨p, hp, h⟩ := hf.exists_forall_le hM hm
  exact ⟨p, hp, le_antisymm (le_sphereSup hM hp) (sphereSup_le h)⟩

end IsFrameFunction

end Gleason

end
