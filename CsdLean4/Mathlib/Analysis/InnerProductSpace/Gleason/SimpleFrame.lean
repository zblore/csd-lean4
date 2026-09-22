/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Piron
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Warmup
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order.Basic

/-!
# Gleason's theorem, finite-dimensional: the basic lemma and the simple frame functions

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, stage
57(c): Cooke–Keane–Moran §4 (the basic lemma) and the theorem of §5 — Gleason's theorem for
the *simple* frame functions, those attaining their supremum at a point `p` and constant on
the equator of `p`. Bell's and Piron's elementary proofs of the extreme case end here.

For a frame function `f` on `S² ⊂ ℝ³` and a unit pole `p`:

* `IsFrameFunction.equator_le` — if `f p = sup f` and `f = m` on the equator then `m = inf f`
  (P4 at the pole); `IsFrameFunction.equator_lt_add` is the approximate version;
* **the basic lemma** `IsFrameFunction.descent_le` — under the same hypotheses, `f s' ≤ f s`
  for every `s'` on the descent through `s` (the four-point identity on the great circle
  `D_s`, whose point orthogonal to `s` lies on the equator); `IsFrameFunction.descent_lt_add`
  is the approximate version (`f p > sup f − ξ` gives `f s' − ξ < f s`);
* `IsFrameFunction.le_of_latitude_lt` — `f` is monotone in latitude on the northern
  hemisphere, by Piron's geometric lemma (`exists_descent_chain`) and the basic lemma along the
  chain;
* `exists_frame_of_latitudes` — for `a + b + c = 1` there is a frame in the northern hemisphere
  with latitudes `a, b, c` (transport a unit vector of square roots through an orthonormal
  basis of `p^⊥`);
* the suprema and infima of `f` over the parallels (`parallelSup`, `parallelInf`), which are
  interlaced by monotonicity, so that the set of latitudes where they differ is a family of
  disjoint open intervals, hence countable (`Set.PairwiseDisjoint.countable_of_isOpen`);
* ★ **the simple-frame-function theorem** `IsFrameFunction.eq_add_mul_latitude` — if
  `f p = sup f` and `f = m` on the equator of `p`, then `f s = m + (f p − m) ⟪p, s⟫²` for every
  unit `s`: Warmup Theorem II (`eq_self_of_monotone_sum_eq_one`) applied to the common value of
  `parallelSup` and `parallelInf` off the countable exceptional set, then a squeeze that shows
  the exceptional set is empty. `IsFrameFunction.eq_latitude_of_normalised` is the normalised
  form (`f p = 1`, `f = 0` on the equator: `f s = latitude p s`).

## Source

Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117–128, §4 and the
Theorem of §5; Piron, *Foundations of Quantum Physics* (1976); Bell 1966, *Rev. Mod. Phys.*
**38**, 447 (the extreme case).
-/

@[expose] public section

open Matrix Real
open scoped Matrix InnerProductSpace

namespace Gleason

/-! ### More about latitudes and the coldest vector -/

section Latitude

variable {p s : EuclideanSpace ℝ (Fin 3)}

lemma latitude_nonneg (p s : EuclideanSpace ℝ (Fin 3)) : 0 ≤ latitude p s := sq_nonneg _

lemma latitude_le_one (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) : latitude p s ≤ 1 := by
  rw [latitude, ← sq_abs]
  calc |⟪p, s⟫_ℝ| ^ 2 ≤ (‖p‖ * ‖s‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm p s) 2
    _ = 1 := by rw [hp, hs]; norm_num

lemma latitude_self (hp : ‖p‖ = 1) : latitude p p = 1 := by
  rw [latitude, real_inner_self_eq_norm_sq, hp]; norm_num

lemma latitude_neg (p s : EuclideanSpace ℝ (Fin 3)) : latitude p (-s) = latitude p s := by
  rw [latitude, latitude, inner_neg_right, neg_sq]

lemma pole_mem_northern (hp : ‖p‖ = 1) : p ∈ northern p :=
  ⟨hp, by rw [real_inner_self_eq_norm_sq, hp]; norm_num⟩

/-- The only point of the northern hemisphere at latitude `1` is the pole. -/
lemma eq_pole_of_latitude_eq_one (hp : ‖p‖ = 1) (hs : s ∈ northern p)
    (hl : latitude p s = 1) : s = p := by
  have h1 : ⟪p, s⟫_ℝ = 1 := by
    have h2 : (⟪p, s⟫_ℝ - 1) * (⟪p, s⟫_ℝ + 1) = 0 := by
      rw [latitude] at hl; linear_combination hl
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith [hs.2]
  have h3 : ‖p - s‖ ^ 2 = 0 := by rw [norm_sub_sq_real, hp, hs.1, h1]; norm_num
  exact (sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))).symm

/-- A point of the northern hemisphere at latitude `0` is on the equator. -/
lemma mem_equator_of_latitude_eq_zero (hs : s ∈ northern p) (hl : latitude p s = 0) :
    s ∈ equator p :=
  ⟨hs.1, pow_eq_zero_iff two_ne_zero |>.mp hl⟩

/-- Off the pole, `p − ⟪p, s⟫ s` is nonzero. -/
lemma sub_inner_smul_ne_zero (hp : ‖p‖ = 1) (hs : s ∈ northern p) (hsp : s ≠ p) :
    p - ⟪p, s⟫_ℝ • s ≠ 0 := by
  intro h
  have hps : p = ⟪p, s⟫_ℝ • s := sub_eq_zero.mp h
  have h1 : ‖p‖ = ‖⟪p, s⟫_ℝ • s‖ := by conv_lhs => rw [hps]
  rw [hp, norm_smul, hs.1, mul_one, Real.norm_eq_abs, abs_of_nonneg hs.2] at h1
  rw [← h1, one_smul] at hps
  exact hsp hps.symm

lemma norm_coldest (hp : ‖p‖ = 1) (hs : s ∈ northern p) (hsp : s ≠ p) :
    ‖coldest p s‖ = 1 := by
  have h := norm_pos_iff.mpr (sub_inner_smul_ne_zero hp hs hsp)
  rw [coldest, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ h.ne']

/-- The point of the descent orthogonal to `s` lies on the equator: `⟪p, s × s^⊥⟫ = 0`. -/
lemma inner_pole_cross_coldest (p s : EuclideanSpace ℝ (Fin 3)) :
    ⟪p, cross s (coldest p s)⟫_ℝ = 0 := by
  have h : ⟪p, cross s (coldest p s)⟫_ℝ = ⟪coldest p s, cross p s⟫_ℝ := by
    rw [real_inner_eq_dotProduct, real_inner_eq_dotProduct, coe_cross, coe_cross,
      triple_product_permutation (⇑p) (⇑s) (⇑(coldest p s)),
      triple_product_permutation (⇑s) (⇑(coldest p s)) (⇑p)]
  rw [h, coldest, inner_smul_left, inner_sub_left, inner_smul_left, inner_cross_left,
    inner_cross_right]
  simp

end Latitude

/-! ### The equator is the minimum; the basic lemma -/

namespace IsFrameFunction

variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W m : ℝ} {p : EuclideanSpace ℝ (Fin 3)}

/-- **The equator value is the minimum** (CKM §4, from P4 at the pole): if `f p = sup f` and
`f = m` on the equator of `p`, then `m ≤ f u` for every unit `u`. -/
theorem equator_le (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) : m ≤ f u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht, hpt, hft⟩ := hf.exists_orthogonal_lt hM (m := f u)
    (fun δ hδ => ⟨u, hu, by linarith⟩) (ξ := m - f u) hp (by linarith)
  have := hE t ⟨ht, hpt⟩
  linarith

/-- The approximate form: if `f p > M − ξ` with `M` an upper bound and `f = m` on the equator,
then `m − ξ < f u` for every unit `u`. -/
theorem equator_lt_add (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1) {M ξ : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) (hpξ : M - ξ < f p)
    (hE : ∀ e ∈ equator p, f e = m) {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    m - ξ < f u := by
  by_contra hle
  push Not at hle
  obtain ⟨t, ht, hpt, hft⟩ := hf.exists_orthogonal_lt hM (m := f u)
    (fun δ hδ => ⟨u, hu, by linarith⟩) (ξ := ξ) hp hpξ
  have := hE t ⟨ht, hpt⟩
  linarith

/-- **The basic lemma (CKM §4).** If `f p = sup f` and `f` is constant on the equator of `p`,
then `f s' ≤ f s` for every `s ≠ p` in the northern hemisphere and every `s'` on the descent
through `s`. -/
theorem descent_le (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m)
    {s s' : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) (hsp : s ≠ p)
    (hs' : s' ∈ descent p s) : f s' ≤ f s := by
  have hc1 : ‖coldest p s‖ = 1 := norm_coldest hp hs hsp
  have hsc : ⟪s, coldest p s⟫_ℝ = 0 := inner_coldest_self p hs.1
  have hs'c : ⟪s', coldest p s⟫_ℝ = 0 := hs'.2
  have hs'1 : ‖s'‖ = 1 := hs'.1.1
  have ht : ‖cross s (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs.1 hc1 hsc
  have ht' : ‖cross s' (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs'1 hc1 hs'c
  have h4 := hf.four_point hc1 hs.1 ht hs'1 ht' hsc
    (by rw [real_inner_comm]; exact inner_cross_right s _) hs'c
    (by rw [real_inner_comm]; exact inner_cross_right s' _) (inner_cross_left s _)
    (inner_cross_left s' _)
  have htE : f (cross s (coldest p s)) = m := hE _ ⟨ht, inner_pole_cross_coldest p s⟩
  have ht'm : m ≤ f (cross s' (coldest p s)) := hf.equator_le hp hM hE ht'
  linarith

/-- **The approximate basic lemma (CKM §4).** If `f p > sup f − ξ` and `f` is constant on the
equator of `p`, then `f s' − ξ < f s` for `s'` on the descent through `s ≠ p`. -/
theorem descent_lt_add (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1) {M ξ : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) (hpξ : M - ξ < f p)
    (hE : ∀ e ∈ equator p, f e = m)
    {s s' : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) (hsp : s ≠ p)
    (hs' : s' ∈ descent p s) : f s' - ξ < f s := by
  have hc1 : ‖coldest p s‖ = 1 := norm_coldest hp hs hsp
  have hsc : ⟪s, coldest p s⟫_ℝ = 0 := inner_coldest_self p hs.1
  have hs'c : ⟪s', coldest p s⟫_ℝ = 0 := hs'.2
  have hs'1 : ‖s'‖ = 1 := hs'.1.1
  have ht : ‖cross s (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs.1 hc1 hsc
  have ht' : ‖cross s' (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs'1 hc1 hs'c
  have h4 := hf.four_point hc1 hs.1 ht hs'1 ht' hsc
    (by rw [real_inner_comm]; exact inner_cross_right s _) hs'c
    (by rw [real_inner_comm]; exact inner_cross_right s' _) (inner_cross_left s _)
    (inner_cross_left s' _)
  have htE : f (cross s (coldest p s)) = m := hE _ ⟨ht, inner_pole_cross_coldest p s⟩
  have ht'm : m - ξ < f (cross s' (coldest p s)) := hf.equator_lt_add hp hM hpξ hE ht'
  linarith

/-- **Monotonicity in latitude (CKM §5).** Under the hypotheses of the basic lemma, `f` is
monotone in latitude on the northern hemisphere: `latitude p s < latitude p t → f s ≤ f t`. -/
theorem le_of_latitude_lt (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m)
    {s t : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) (ht : t ∈ northern p)
    (hl : latitude p s < latitude p t) : f s ≤ f t := by
  rcases eq_or_ne t p with rfl | htp
  · exact hM s hs.1
  have hsp : s ≠ p := by
    rintro rfl
    have := latitude_le_one hp ht.1
    rw [latitude_self hp] at hl
    linarith
  obtain ⟨n, c, -, hc⟩ := exists_descent_chain hp ht htp hs hsp hl
  have key : ∀ i, i ≤ n → f (c i) ≤ f (c 0) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      exact (hf.descent_le hp hM hE (hc.mem k (by omega)).1 (hc.mem k (by omega)).2
        (hc.step k (by omega))).trans (ih (by omega))
  have := key n le_rfl
  rwa [hc.head, hc.last] at this

end IsFrameFunction

/-! ### Frames with prescribed latitudes -/

/-- **A frame with prescribed latitudes.** For `a + b + c = 1`, `a, b, c ≥ 0`, there is a frame
`(q₀, q₁, q₂)` in the northern hemisphere of `p` with latitudes `a, b, c`: transport the unit
vector `(√a, √b, √c)`, completed to an orthonormal basis, through an orthonormal basis
`(p, e₁, e₂)`. -/
lemma exists_frame_of_latitudes {p : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    ∃ q : Fin 3 → EuclideanSpace ℝ (Fin 3), Orthonormal ℝ q ∧ (∀ j, q j ∈ northern p) ∧
      latitude p (q 0) = a ∧ latitude p (q 1) = b ∧ latitude p (q 2) = c := by
  obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
  obtain ⟨B, hB⟩ : ∃ B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      ⇑B = ![p, e₁, cross p e₁] :=
    ⟨orthonormalBasisOfTriple (orthonormal_cross hp he₁ hpe₁), coe_orthonormalBasisOfTriple _⟩
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3),
      v = WithLp.toLp 2 ![Real.sqrt a, Real.sqrt b, Real.sqrt c] := ⟨_, rfl⟩
  have hv1 : ‖v‖ = 1 := by
    rw [hv, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sq_sqrt hc, habc]
  obtain ⟨w, hw, hvw⟩ := exists_unit_orthogonal v
  obtain ⟨V, hV⟩ : ∃ V : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      ⇑V = ![v, w, cross v w] :=
    ⟨orthonormalBasisOfTriple (orthonormal_cross hv1 hw hvw), coe_orthonormalBasisOfTriple _⟩
  have hV0 : V 0 = v := by rw [hV]; rfl
  have hB0 : B 0 = p := by rw [hB]; rfl
  have hinner : ∀ j k : Fin 3,
      ⟪∑ i, (V i) j • B i, ∑ i, (V i) k • B i⟫_ℝ = if j = k then 1 else 0 := by
    intro j k
    rw [B.orthonormal.inner_sum]
    have h := congrFun (congrFun (colMatrix_mul_conjTranspose_of_orthonormalBasis V) j) k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colMatrix_apply, star_trivial,
      Matrix.one_apply] at h
    simpa [RCLike.conj_to_real] using h
  have hq : Orthonormal ℝ fun j : Fin 3 => ∑ i, (V i) j • B i := orthonormal_iff_ite.mpr hinner
  have hpq : ∀ j, ⟪p, ∑ i, (V i) j • B i⟫_ℝ = (V 0) j := by
    intro j
    rw [← hB0]
    exact B.orthonormal.inner_right_sum _ (Finset.mem_univ 0)
  have hv0 : ∀ j, 0 ≤ (V 0) j := by
    intro j
    rw [hV0, hv]
    fin_cases j <;> simp [Real.sqrt_nonneg]
  refine ⟨fun j => ∑ i, (V i) j • B i, hq, fun j => ⟨hq.norm_eq_one j, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpq]; exact hv0 j
  · rw [latitude, hpq, hV0, hv]; simp [Real.sq_sqrt ha]
  · rw [latitude, hpq, hV0, hv]; simp [Real.sq_sqrt hb]
  · rw [latitude, hpq, hV0, hv]; simp [Real.sq_sqrt hc]

/-! ### Suprema and infima over the parallels -/

/-- The values of `f` on the `l`-th parallel of the northern hemisphere. -/
def parallelValues (p : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ) (l : ℝ) :
    Set ℝ :=
  f '' {s | s ∈ northern p ∧ latitude p s = l}

/-- The supremum of `f` over the `l`-th parallel. -/
noncomputable def parallelSup (p : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (l : ℝ) : ℝ :=
  sSup (parallelValues p f l)

/-- The infimum of `f` over the `l`-th parallel. -/
noncomputable def parallelInf (p : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (l : ℝ) : ℝ :=
  sInf (parallelValues p f l)

section Parallels

variable {p : EuclideanSpace ℝ (Fin 3)} {f : EuclideanSpace ℝ (Fin 3) → ℝ} {l : ℝ}

lemma mem_parallelValues {s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    f s ∈ parallelValues p f (latitude p s) :=
  ⟨s, ⟨hs, rfl⟩, rfl⟩

lemma parallelValues_nonempty (hp : ‖p‖ = 1) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    (parallelValues p f l).Nonempty := by
  obtain ⟨q, -, hqN, hq0, -, -⟩ := exists_frame_of_latitudes hp hl.1
    (by linarith [hl.2] : 0 ≤ 1 - l) le_rfl (by ring)
  exact ⟨f (q 0), q 0, ⟨hqN 0, hq0⟩, rfl⟩

lemma bddAbove_parallelValues (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1) :
    BddAbove (parallelValues p f l) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h1 s hs.1

lemma bddBelow_parallelValues (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u) :
    BddBelow (parallelValues p f l) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h0 s hs.1

lemma le_parallelSup (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    f s ≤ parallelSup p f (latitude p s) :=
  le_csSup (bddAbove_parallelValues h1) (mem_parallelValues hs)

lemma parallelInf_le (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    parallelInf p f (latitude p s) ≤ f s :=
  csInf_le (bddBelow_parallelValues h0) (mem_parallelValues hs)

lemma parallelSup_le_one (hp : ‖p‖ = 1) (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1)
    (hl : l ∈ Set.Icc (0 : ℝ) 1) : parallelSup p f l ≤ 1 := by
  refine csSup_le (parallelValues_nonempty hp hl) ?_
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h1 s hs.1

lemma parallelInf_nonneg (hp : ‖p‖ = 1)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ parallelInf p f l := by
  refine le_csInf (parallelValues_nonempty hp hl) ?_
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h0 s hs.1

lemma parallelInf_le_parallelSup (hp : ‖p‖ = 1)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u)
    (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    parallelInf p f l ≤ parallelSup p f l := by
  obtain ⟨x, hx⟩ := parallelValues_nonempty (f := f) hp hl
  exact (csInf_le (bddBelow_parallelValues h0) hx).trans (le_csSup (bddAbove_parallelValues h1) hx)

/-- **The parallels are interlaced:** for `l < l'`, every value on the `l`-th parallel is at
most every value on the `l'`-th. -/
lemma parallelSup_le_parallelInf (hp : ‖p‖ = 1)
    (hmono : ∀ s t : EuclideanSpace ℝ (Fin 3), s ∈ northern p → t ∈ northern p →
      latitude p s < latitude p t → f s ≤ f t)
    {l' : ℝ} (hl : 0 ≤ l) (hl' : l' ≤ 1) (hll' : l < l') :
    parallelSup p f l ≤ parallelInf p f l' := by
  refine csSup_le (parallelValues_nonempty hp ⟨hl, by linarith⟩) ?_
  rintro _ ⟨s, ⟨hs, hsl⟩, rfl⟩
  refine le_csInf (parallelValues_nonempty hp ⟨by linarith, hl'⟩) ?_
  rintro _ ⟨t, ⟨ht, htl⟩, rfl⟩
  exact hmono s t hs ht (by rw [hsl, htl]; exact hll')

lemma parallelValues_zero (hE : ∀ e ∈ equator p, f e = 0) :
    parallelValues p f 0 = {0} := by
  obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
  ext x
  constructor
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    exact hE s (mem_equator_of_latitude_eq_zero hs hl)
  · rintro rfl
    exact ⟨e₁, ⟨⟨he₁, hpe₁.ge⟩, by rw [latitude, hpe₁]; norm_num⟩, hE e₁ ⟨he₁, hpe₁⟩⟩

lemma parallelValues_one (hp : ‖p‖ = 1) : parallelValues p f 1 = {f p} := by
  ext x
  constructor
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    rw [eq_pole_of_latitude_eq_one hp hs hl]
    rfl
  · rintro rfl
    exact ⟨p, ⟨pole_mem_northern hp, latitude_self hp⟩, rfl⟩

lemma parallelSup_zero (hE : ∀ e ∈ equator p, f e = 0) : parallelSup p f 0 = 0 := by
  rw [parallelSup, parallelValues_zero hE, csSup_singleton]

lemma parallelInf_zero (hE : ∀ e ∈ equator p, f e = 0) : parallelInf p f 0 = 0 := by
  rw [parallelInf, parallelValues_zero hE, csInf_singleton]

lemma parallelSup_one (hp : ‖p‖ = 1) : parallelSup p f 1 = f p := by
  rw [parallelSup, parallelValues_one hp, csSup_singleton]

lemma parallelInf_one (hp : ‖p‖ = 1) : parallelInf p f 1 = f p := by
  rw [parallelInf, parallelValues_one hp, csInf_singleton]

end Parallels

/-! ### The simple frame functions -/

namespace IsFrameFunction

variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W m : ℝ} {p : EuclideanSpace ℝ (Fin 3)}

/-- **The simple-frame-function theorem, normalised (CKM §5).** A frame function with
`f p = 1 = sup f` and `f = 0` on the equator of `p` is the latitude: `f s = ⟪p, s⟫²`. -/
theorem eq_latitude_of_normalised (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1) (hfp : f p = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1) (hE : ∀ e ∈ equator p, f e = 0) :
    ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → f s = latitude p s := by
  have hMp : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p := fun u hu => hfp ▸ hM u hu
  have h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u :=
    fun u hu => hf.equator_le hp hMp hE hu
  have hmono : ∀ s t : EuclideanSpace ℝ (Fin 3), s ∈ northern p → t ∈ northern p →
      latitude p s < latitude p t → f s ≤ f t :=
    fun s t hs ht hl => hf.le_of_latitude_lt hp hMp hE hs ht hl
  -- the weight is one
  have hW : W = 1 := by
    obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
    have h := hf.eq_of_triple (orthonormal_cross hp he₁ hpe₁)
    rw [hfp, hE e₁ ⟨he₁, hpe₁⟩,
      hE (cross p e₁) ⟨norm_cross_of_orthonormal hp he₁ hpe₁, inner_cross_left p e₁⟩] at h
    linarith
  -- the exceptional set of latitudes where sup and inf differ
  obtain ⟨C, hC⟩ : ∃ C : Set ℝ,
      C = {l | l ∈ Set.Ioo (0 : ℝ) 1 ∧ parallelInf p f l < parallelSup p f l} := ⟨_, rfl⟩
  have hCsub : C ⊆ Set.Ioo 0 1 := by rw [hC]; exact fun l hl => hl.1
  have hagree : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → l ∉ C →
      parallelInf p f l = parallelSup p f l := by
    intro l hl hlC
    rcases eq_or_lt_of_le hl.1 with rfl | hl0
    · rw [parallelInf_zero hE, parallelSup_zero hE]
    rcases eq_or_lt_of_le hl.2 with rfl | hl1
    · rw [parallelInf_one hp, parallelSup_one hp]
    refine le_antisymm (parallelInf_le_parallelSup hp h0 hM hl) ?_
    by_contra hlt
    push Not at hlt
    exact hlC (by rw [hC]; exact ⟨⟨hl0, hl1⟩, hlt⟩)
  -- it is countable: the gaps are disjoint open intervals
  have hCc : C.Countable := by
    have hdisj : C.PairwiseDisjoint fun l => Set.Ioo (parallelInf p f l) (parallelSup p f l) := by
      intro l hl l' hl' hne
      have hl2 := hCsub hl
      have hl'2 := hCsub hl'
      rcases lt_or_gt_of_ne hne with h | h
      · refine Set.disjoint_left.mpr fun x hx hx' => ?_
        have := parallelSup_le_parallelInf hp hmono hl2.1.le hl'2.2.le h
        linarith [hx.2, hx'.1]
      · refine Set.disjoint_left.mpr fun x hx hx' => ?_
        have := parallelSup_le_parallelInf hp hmono hl'2.1.le hl2.2.le h
        linarith [hx.1, hx'.2]
    exact hdisj.countable_of_isOpen (fun l _ => isOpen_Ioo)
      (fun l hl => Set.nonempty_Ioo.mpr (by rw [hC] at hl; exact hl.2))
  -- Warmup Theorem II on the common value
  have hwarm : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → l ∉ C → parallelSup p f l = l := by
    refine eq_self_of_monotone_sum_eq_one hCc hCsub (parallelSup_zero hE) ?_ ?_
    · intro a b ha hb _ _ hab
      exact (parallelSup_le_parallelInf hp hmono ha.1 hb.2 hab).trans
        (parallelInf_le_parallelSup hp h0 hM hb)
    · intro a b c ha hb hc haC hbC hcC habc
      obtain ⟨q, hq, hqN, hqa, hqb, hqc⟩ := exists_frame_of_latitudes hp ha.1 hb.1 hc.1 habc
      have hsum := hf.sum_triple hq
      rw [Fin.sum_univ_three, hW] at hsum
      have e0 : f (q 0) = parallelSup p f a := by
        have h1 := le_parallelSup hM (hqN 0)
        have h2 := parallelInf_le h0 (hqN 0)
        rw [hqa] at h1 h2
        rw [hagree a ha haC] at h2
        exact le_antisymm h1 h2
      have e1 : f (q 1) = parallelSup p f b := by
        have h1 := le_parallelSup hM (hqN 1)
        have h2 := parallelInf_le h0 (hqN 1)
        rw [hqb] at h1 h2
        rw [hagree b hb hbC] at h2
        exact le_antisymm h1 h2
      have e2 : f (q 2) = parallelSup p f c := by
        have h1 := le_parallelSup hM (hqN 2)
        have h2 := parallelInf_le h0 (hqN 2)
        rw [hqc] at h1 h2
        rw [hagree c hc hcC] at h2
        exact le_antisymm h1 h2
      linarith
  -- the squeeze: every parallel's supremum is at most its latitude, and its infimum at least
  have hsup_le : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → parallelSup p f l ≤ l := by
    intro l hl
    rcases eq_or_lt_of_le hl.2 with rfl | hl1
    · exact parallelSup_le_one hp hM ⟨zero_le_one, le_rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨l', hl'⟩ : ∃ l', l' ∈ Set.Ioo l (min 1 (l + ε)) ∧ l' ∉ C := by
      by_contra hcon
      push Not at hcon
      have h := hCc.mono fun x hx => hcon x hx
      rw [Cardinal.Real.Ioo_countable_iff] at h
      exact absurd h (not_le.mpr (lt_min hl1 (by linarith)))
    have hl'I : l' ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hl.1.trans hl'.1.1.le, hl'.1.2.le.trans (min_le_left _ _)⟩
    calc parallelSup p f l ≤ parallelInf p f l' :=
          parallelSup_le_parallelInf hp hmono hl.1 hl'I.2 hl'.1.1
      _ = parallelSup p f l' := hagree l' hl'I hl'.2
      _ = l' := hwarm l' hl'I hl'.2
      _ ≤ l + ε := hl'.1.2.le.trans (min_le_right _ _)
  have hle_inf : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → l ≤ parallelInf p f l := by
    intro l hl
    rcases eq_or_lt_of_le hl.1 with rfl | hl0
    · exact parallelInf_nonneg hp h0 ⟨le_rfl, zero_le_one⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨l'', hl''⟩ : ∃ l'', l'' ∈ Set.Ioo (max 0 (l - ε)) l ∧ l'' ∉ C := by
      by_contra hcon
      push Not at hcon
      have h := hCc.mono fun x hx => hcon x hx
      rw [Cardinal.Real.Ioo_countable_iff] at h
      exact absurd h (not_le.mpr (max_lt hl0 (by linarith)))
    have hl''I : l'' ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(le_max_left _ _).trans hl''.1.1.le, hl''.1.2.le.trans hl.2⟩
    have h1 : l - ε < l'' := lt_of_le_of_lt (le_max_right _ _) hl''.1.1
    have h2 := parallelSup_le_parallelInf hp hmono hl''I.1 hl.2 hl''.1.2
    rw [hwarm l'' hl''I hl''.2] at h2
    linarith
  -- the conclusion on the northern hemisphere, then by `f (−s) = f s`
  have hN : ∀ s : EuclideanSpace ℝ (Fin 3), s ∈ northern p → f s = latitude p s := by
    intro s hs
    have hl : latitude p s ∈ Set.Icc (0 : ℝ) 1 := ⟨latitude_nonneg p s, latitude_le_one hp hs.1⟩
    exact le_antisymm ((le_parallelSup hM hs).trans (hsup_le _ hl))
      ((hle_inf _ hl).trans (parallelInf_le h0 hs))
  intro s hs
  rcases le_or_gt 0 ⟪p, s⟫_ℝ with h | h
  · exact hN s ⟨hs, h⟩
  · have := hN (-s) ⟨by rw [norm_neg, hs], by rw [inner_neg_right]; linarith⟩
    rwa [hf.neg_apply hs, latitude_neg] at this

/-- ★ **The simple-frame-function theorem (CKM §5, Theorem).** If a frame function attains its
supremum at `p` and takes the constant value `m` on the equator of `p`, then
`f s = m + (f p − m) ⟪p, s⟫²` for every unit `s`. -/
theorem eq_add_mul_latitude (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m) :
    ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → f s = m + (f p - m) * latitude p s := by
  have hmin : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u :=
    fun u hu => hf.equator_le hp hM hE hu
  rcases eq_or_lt_of_le (hmin p hp) with hmp | hmp
  · intro s hs
    have h1 := hM s hs
    have h2 := hmin s hs
    rw [← hmp, sub_self, zero_mul, add_zero]
    linarith
  have hne : f p - m ≠ 0 := by linarith
  have hpos : 0 < f p - m := by linarith
  have hg : IsFrameFunction ℝ (fun u => (f p - m)⁻¹ * (f u - m)) ((f p - m)⁻¹ * (W - 3 * m)) := by
    have := (hf.sub (IsFrameFunction.const (𝕜 := ℝ) (n := 3) m)).smul (f p - m)⁻¹
    simpa using this
  have key := hg.eq_latitude_of_normalised hp (by simp [inv_mul_cancel₀ hne])
    (fun u hu => by
      rw [inv_mul_le_iff₀ hpos, mul_one]
      linarith [hM u hu])
    (fun e he => by simp [hE e he])
  intro s hs
  have h := key s hs
  rw [← h]
  field_simp
  ring

end IsFrameFunction

end Gleason

end
