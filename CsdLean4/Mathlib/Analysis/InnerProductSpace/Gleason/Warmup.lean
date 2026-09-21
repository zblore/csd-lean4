/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Polarization
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Gleason's theorem, finite-dimensional: the two "warmup" theorems on `[0, 1]`

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, stage
57(a), second half: Cooke–Keane–Moran §3 — the one-dimensional "abelianised" versions of
Gleason's theorem, which the core lemma's proof (§5) applies along the latitudes of the sphere.

* **Warmup Theorem I** (`affine_of_sum_eq_const`): a bounded `f : [0, 1] → ℝ` with
  `f a + f b + f c` constant whenever `a + b + c = 1` is affine, `f a = (w − 3 f 0) a + f 0`.
  The engine is `linear_of_add_on_Icc`: an additive function on `[0, 1]` that is bounded there is
  linear — additivity is extended to `ℝ` by `x ↦ g (fract x) + ⌊x⌋ g 1` and
  `Gleason.additive_bounded_linear` (Cauchy's equation with a local bound) finishes.
* **Warmup Theorem II** (`eq_self_of_monotone_sum_eq_one`): let `C ⊆ (0, 1)` be countable and
  `f` be defined off `C` with `f 0 = 0`, monotone on `[0, 1] \ C`, and `f a + f b + f c = 1`
  whenever `a + b + c = 1` off `C`. Then `f a = a` off `C`. The proof picks `a₀ ∈ (0, 1)` outside
  the countable set of rational multiples of `C` and `1 − C`, so that every rational multiple
  `r a₀` and its complement `1 − r a₀` avoid `C`; additivity on those gives `f (r a₀) = r f a₀`,
  monotonicity squeezes every other point between rational multiples, and the frame identity at
  one triple pins the slope to `1`.

## Source

Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117–128, §3.
-/

@[expose] public section

namespace Gleason

/-! ### Warmup Theorem I -/

/-- An additive function on `[0, 1]` that is bounded there is linear: `g a = a · g 1`. The
additivity is extended to all of `ℝ` by `x ↦ g (fract x) + ⌊x⌋ g 1`. -/
theorem linear_of_add_on_Icc {g : ℝ → ℝ} (hg0 : g 0 = 0)
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 → g (a + b) = g a + g b)
    {K : ℝ} (hK : ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → |g a| ≤ K) :
    ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → g a = a * g 1 := by
  -- the extension to `ℝ`
  set G : ℝ → ℝ := fun x => g (Int.fract x) + (⌊x⌋ : ℝ) * g 1 with hG
  have hGadd : ∀ x y : ℝ, G (x + y) = G x + G y := by
    intro x y
    have hu0 := Int.fract_nonneg x
    have hu1 := Int.fract_lt_one x
    have hv0 := Int.fract_nonneg y
    have hv1 := Int.fract_lt_one y
    have hx : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
    have hy : y = ⌊y⌋ + Int.fract y := (Int.floor_add_fract y).symm
    rcases lt_or_ge (Int.fract x + Int.fract y) 1 with hlt | hge
    · have hfl : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
      have hfr : Int.fract (x + y) = Int.fract x + Int.fract y := by
        rw [Int.fract, hfl]
        push_cast
        linarith
      simp only [hG, hfr, hfl]
      rw [hadd _ _ hu0 hv0 hlt.le]
      push_cast
      ring
    · have hfl : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
      have hfr : Int.fract (x + y) = Int.fract x + Int.fract y - 1 := by
        rw [Int.fract, hfl]
        push_cast
        linarith
      -- `g u + g v = g (u + v − 1) + g 1`
      have h1 : g (Int.fract x) = g (Int.fract x + Int.fract y - 1) + g (1 - Int.fract y) := by
        have := hadd (Int.fract x + Int.fract y - 1) (1 - Int.fract y) (by linarith) (by linarith)
          (by linarith)
        rwa [show Int.fract x + Int.fract y - 1 + (1 - Int.fract y) = Int.fract x by ring] at this
      have h2 : g 1 = g (1 - Int.fract y) + g (Int.fract y) := by
        have := hadd (1 - Int.fract y) (Int.fract y) (by linarith) hv0 (by linarith)
        rwa [show 1 - Int.fract y + Int.fract y = 1 by ring] at this
      simp only [hG, hfr, hfl]
      push_cast
      linarith
  have hGbound : ∀ x : ℝ, |x| ≤ 1 → |G x| ≤ K + 2 * |g 1| := by
    intro x hx
    have hfl1 : (⌊x⌋ : ℝ) ≤ 2 := by
      have := Int.floor_le x
      have := (abs_le.mp hx).2
      linarith
    have hfl2 : -2 ≤ (⌊x⌋ : ℝ) := by
      have := Int.lt_floor_add_one x
      have := (abs_le.mp hx).1
      linarith
    have hfr := hK (Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have habs : |(⌊x⌋ : ℝ) * g 1| ≤ 2 * |g 1| := by
      rw [abs_mul]
      have : |(⌊x⌋ : ℝ)| ≤ 2 := abs_le.mpr ⟨hfl2, hfl1⟩
      nlinarith [abs_nonneg (g 1), abs_nonneg (⌊x⌋ : ℝ)]
    calc |G x| = |g (Int.fract x) + (⌊x⌋ : ℝ) * g 1| := rfl
      _ ≤ |g (Int.fract x)| + |(⌊x⌋ : ℝ) * g 1| := abs_add_le _ _
      _ ≤ K + 2 * |g 1| := add_le_add hfr habs
  have hlin := additive_bounded_linear G hGadd hGbound
  have hG1 : G 1 = g 1 := by
    simp only [hG, Int.fract_one, Int.floor_one, Int.cast_one, one_mul, hg0, zero_add]
  intro a ha
  rcases eq_or_lt_of_le ha.2 with rfl | ha1
  · ring
  · have hGa : G a = g a := by
      simp only [hG, Int.fract_eq_self.mpr ⟨ha.1, ha1⟩, Int.floor_eq_zero_iff.mpr ⟨ha.1, ha1⟩,
        Int.cast_zero, zero_mul, add_zero]
    rw [← hGa, hlin a, hG1]

/-- **Warmup Theorem I (CKM §3).** A bounded `f : [0, 1] → ℝ` such that `f a + f b + f c` has
the same value `w` whenever `a + b + c = 1` is affine: `f a = (w − 3 f 0) a + f 0`. -/
theorem affine_of_sum_eq_const {f : ℝ → ℝ} {w K : ℝ}
    (hK : ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → |f a| ≤ K)
    (h : ∀ a b c : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → c ∈ Set.Icc (0 : ℝ) 1 →
      a + b + c = 1 → f a + f b + f c = w) :
    ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → f a = (w - 3 * f 0) * a + f 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set g : ℝ → ℝ := fun a => f a - f 0 with hg
  have hg0 : g 0 = 0 := by simp [hg]
  have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 → g (a + b) = g a + g b := by
    intro a b ha hb hab
    have e1 := h a b (1 - a - b) ⟨ha, by linarith⟩ ⟨hb, by linarith⟩ ⟨by linarith, by linarith⟩
      (by ring)
    have e2 := h (a + b) 0 (1 - a - b) ⟨by linarith, hab⟩ h0 ⟨by linarith, by linarith⟩ (by ring)
    simp only [hg]
    linarith
  have hKg : ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → |g a| ≤ K + |f 0| := by
    intro a ha
    calc |g a| = |f a - f 0| := rfl
      _ ≤ |f a| + |f 0| := abs_sub _ _
      _ ≤ K + |f 0| := add_le_add (hK a ha) le_rfl
  have hlin := linear_of_add_on_Icc hg0 hadd hKg
  have hg1 : g 1 = w - 3 * f 0 := by
    have := h 1 0 0 h1 h0 h0 (by ring)
    simp only [hg]
    linarith
  intro a ha
  have := hlin a ha
  simp only [hg] at this hg1
  rw [hg1] at this
  linarith

/-! ### Warmup Theorem II -/

/-- **Warmup Theorem II (CKM §3).** Let `C ⊆ (0, 1)` be countable and `f : ℝ → ℝ` satisfy, on
`[0, 1] \ C`: `f 0 = 0`, `f` is monotone, and `f a + f b + f c = 1` whenever `a + b + c = 1`.
Then `f a = a` on `[0, 1] \ C`. -/
theorem eq_self_of_monotone_sum_eq_one {C : Set ℝ} (hC : C.Countable) (hC1 : C ⊆ Set.Ioo 0 1)
    {f : ℝ → ℝ} (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → b ∉ C →
      a < b → f a ≤ f b)
    (hsum : ∀ a b c : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      c ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → b ∉ C → c ∉ C → a + b + c = 1 → f a + f b + f c = 1) :
    ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → f a = a := by
  have h0C : (0 : ℝ) ∉ C := fun h => by simpa using (hC1 h).1
  have h1C : (1 : ℝ) ∉ C := fun h => by simpa using (hC1 h).2
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- `f 1 = 1`
  have hf1 : f 1 = 1 := by
    have := hsum 1 0 0 h1I h0I h0I h1C h0C h0C (by ring)
    linarith
  -- the countable set of rational quotients of `C` and `1 − C`
  set Ct : Set ℝ := ((fun p : ℝ × ℚ => p.1 / (p.2 : ℝ)) '' (C ×ˢ Set.univ)) ∪
    ((fun p : ℝ × ℚ => (1 - p.1) / (p.2 : ℝ)) '' (C ×ˢ Set.univ)) with hCt
  have hCt_count : Ct.Countable :=
    ((hC.prod Set.countable_univ).image _).union ((hC.prod Set.countable_univ).image _)
  have hIoo : ¬ (Set.Ioo (0 : ℝ) 1).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]; norm_num
  obtain ⟨a₀, ha₀I, ha₀⟩ : ∃ a₀, a₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ a₀ ∉ Ct := by
    by_contra hcon
    push Not at hcon
    exact hIoo (hCt_count.mono fun x hx => hcon x hx)
  have ha₀0 : 0 < a₀ := ha₀I.1
  have ha₀1 : a₀ < 1 := ha₀I.2
  have ha₀C : a₀ ∉ C := fun h => ha₀ (Or.inl ⟨(a₀, 1), ⟨h, Set.mem_univ _⟩, by simp⟩)
  -- rational multiples of `a₀` and their complements avoid `C`
  have good : ∀ r : ℚ, 0 ≤ r → (r : ℝ) * a₀ ≤ 1 → (r : ℝ) * a₀ ∉ C ∧ 1 - (r : ℝ) * a₀ ∉ C := by
    intro r hr hr1
    constructor
    · intro hmem
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hmem
        exact h0C hmem
      have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      apply ha₀
      refine Or.inl ⟨((r : ℝ) * a₀, r), ⟨hmem, Set.mem_univ _⟩, ?_⟩
      simp only
      field_simp
    · intro hmem
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hmem
        exact h1C hmem
      have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      apply ha₀
      refine Or.inr ⟨(1 - (r : ℝ) * a₀, r), ⟨hmem, Set.mem_univ _⟩, ?_⟩
      simp only
      field_simp
      ring
  -- additivity on rational multiples of `a₀`
  have hadd : ∀ r r' : ℚ, 0 ≤ r → 0 ≤ r' → ((r + r' : ℚ) : ℝ) * a₀ ≤ 1 →
      f (((r + r' : ℚ) : ℝ) * a₀) = f ((r : ℝ) * a₀) + f ((r' : ℝ) * a₀) := by
    intro r r' hr hr' hrr'
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr
    have hr'0 : (0 : ℝ) ≤ r' := by exact_mod_cast hr'
    have hs : ((r + r' : ℚ) : ℝ) = (r : ℝ) + r' := by push_cast; ring
    rw [hs] at hrr' ⊢
    have hra : (r : ℝ) * a₀ ≤ 1 := by nlinarith
    have hr'a : (r' : ℝ) * a₀ ≤ 1 := by nlinarith
    obtain ⟨g1, -⟩ := good r hr hra
    obtain ⟨g2, -⟩ := good r' hr' hr'a
    obtain ⟨g3, g4⟩ := good (r + r') (by positivity) (by rw [hs]; exact hrr')
    rw [hs] at g3 g4
    have e1 := hsum ((r : ℝ) * a₀) ((r' : ℝ) * a₀) (1 - ((r : ℝ) + r') * a₀)
      ⟨by positivity, hra⟩ ⟨by positivity, hr'a⟩ ⟨by linarith, by nlinarith⟩ g1 g2 g4 (by ring)
    have e2 := hsum (((r : ℝ) + r') * a₀) 0 (1 - ((r : ℝ) + r') * a₀)
      ⟨by positivity, hrr'⟩ h0I ⟨by linarith, by nlinarith⟩ g3 h0C g4 (by ring)
    linarith
  -- natural multiples
  have hnat : ∀ (n : ℕ) (r : ℚ), 0 ≤ r → ((n * r : ℚ) : ℝ) * a₀ ≤ 1 →
      f (((n * r : ℚ) : ℝ) * a₀) = n * f ((r : ℝ) * a₀) := by
    intro n r hr
    induction n with
    | zero => intro _; simp [hf0]
    | succ k ih =>
      intro hk
      have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr
      have hcast : (((k + 1 : ℕ) * r : ℚ) : ℝ) = ((k * r + r : ℚ) : ℝ) := by push_cast; ring
      rw [hcast, hadd (k * r) r (by positivity) hr (by rw [← hcast]; exact hk)]
      have hk' : ((k * r : ℚ) : ℝ) * a₀ ≤ 1 := by
        have h1 : (((k + 1 : ℕ) * r : ℚ) : ℝ) = ((k * r : ℚ) : ℝ) + (r : ℝ) := by push_cast; ring
        rw [h1] at hk
        nlinarith
      rw [ih hk']
      push_cast
      ring
  -- rational homogeneity: `f (r a₀) = r f a₀`
  have hrat : ∀ r : ℚ, 0 ≤ r → (r : ℝ) * a₀ ≤ 1 → f ((r : ℝ) * a₀) = r * f a₀ := by
    intro r hr hr1
    set n : ℕ := r.den with hn
    set m : ℕ := r.num.toNat with hm
    have hnpos : (0 : ℚ) < n := by rw [hn]; exact_mod_cast r.den_pos
    have hmr : (m : ℚ) = r.num := by
      rw [hm, ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr)]
    have hr_eq : r = m * (1 / n) := by
      rw [hmr, hn, mul_one_div, Rat.num_div_den]
    -- `f (a₀ / n) = f a₀ / n`
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hcast1 : ((n * (1 / n : ℚ) : ℚ) : ℝ) = 1 := by
      push_cast
      field_simp
    have hunit : f ((((1 : ℚ) / n : ℚ) : ℝ) * a₀) = f a₀ / n := by
      have h := hnat n (1 / n) (by positivity) (by rw [hcast1]; linarith)
      rw [hcast1, one_mul] at h
      field_simp
      linarith
    have h := hnat m (1 / n) (by positivity) (by rw [← hr_eq]; exact hr1)
    rw [← hr_eq] at h
    rw [h, hunit, hr_eq]
    push_cast
    field_simp
  -- `0 ≤ f a₀`, and the squeeze
  have hfa₀ : 0 ≤ f a₀ := by
    have := hmono 0 a₀ h0I ⟨ha₀0.le, ha₀1.le⟩ h0C ha₀C ha₀0
    linarith
  set κ : ℝ := f a₀ / a₀ with hκ
  have hsq : ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → a < 1 → f a = κ * a := by
    intro a ha haC ha1
    have hfa0 : 0 < f a₀ + 1 := by linarith
    apply le_antisymm
    · -- from above: `a < r a₀ < 1`
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hlt : a / a₀ < min (1 / a₀) (a / a₀ + ε / (f a₀ + 1)) := by
        refine lt_min ?_ ?_
        · exact div_lt_div_of_pos_right ha1 ha₀0
        · have : 0 < ε / (f a₀ + 1) := by positivity
          linarith
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      have hr1' : a < (r : ℝ) * a₀ := by
        rw [div_lt_iff₀ ha₀0] at hr1; linarith
      have hr2a : (r : ℝ) < 1 / a₀ := lt_of_lt_of_le hr2 (min_le_left _ _)
      have hr2b : (r : ℝ) < a / a₀ + ε / (f a₀ + 1) := lt_of_lt_of_le hr2 (min_le_right _ _)
      have hra1 : (r : ℝ) * a₀ < 1 := by
        rw [lt_div_iff₀ ha₀0] at hr2a; linarith
      have hr0 : (0 : ℝ) ≤ r := by
        have : 0 ≤ a / a₀ := div_nonneg ha.1 ha₀0.le
        linarith
      have hr0' : 0 ≤ r := by exact_mod_cast hr0
      obtain ⟨g1, -⟩ := good r hr0' hra1.le
      have hm := hmono a ((r : ℝ) * a₀) ha ⟨mul_nonneg hr0 ha₀0.le, hra1.le⟩ haC g1 hr1'
      rw [hrat r hr0' hra1.le] at hm
      calc f a ≤ (r : ℝ) * f a₀ := hm
        _ ≤ (a / a₀ + ε / (f a₀ + 1)) * f a₀ := by
          exact mul_le_mul_of_nonneg_right hr2b.le hfa₀
        _ = κ * a + ε * (f a₀ / (f a₀ + 1)) := by
          rw [hκ]; field_simp
        _ ≤ κ * a + ε := by
          have : f a₀ / (f a₀ + 1) ≤ 1 := by
            rw [div_le_one hfa0]; linarith
          nlinarith
    · -- from below: `r a₀ < a`, or `a = 0`
      rcases eq_or_lt_of_le ha.1 with rfl | ha0
      · rw [hf0]; simp
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hlt : max 0 (a / a₀ - ε / (f a₀ + 1)) < a / a₀ := by
        refine max_lt (by positivity) ?_
        have : 0 < ε / (f a₀ + 1) := by positivity
        linarith
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      have hr0 : (0 : ℝ) ≤ r := le_trans (le_max_left _ _) hr1.le
      have hr0' : 0 ≤ r := by exact_mod_cast hr0
      have hr1b : a / a₀ - ε / (f a₀ + 1) < r := lt_of_le_of_lt (le_max_right _ _) hr1
      have hra : (r : ℝ) * a₀ < a := by
        rw [lt_div_iff₀ ha₀0] at hr2; linarith
      have hra1 : (r : ℝ) * a₀ ≤ 1 := by linarith [ha.2]
      obtain ⟨g1, -⟩ := good r hr0' hra1
      have hm := hmono ((r : ℝ) * a₀) a ⟨mul_nonneg hr0 ha₀0.le, hra1⟩ ha g1 haC hra
      rw [hrat r hr0' hra1] at hm
      have key : κ * a - ε ≤ f a := by
        calc κ * a - ε ≤ κ * a - ε * (f a₀ / (f a₀ + 1)) := by
              have : f a₀ / (f a₀ + 1) ≤ 1 := by
                rw [div_le_one hfa0]; linarith
              nlinarith
          _ = (a / a₀ - ε / (f a₀ + 1)) * f a₀ := by
              rw [hκ]; field_simp
          _ ≤ (r : ℝ) * f a₀ := mul_le_mul_of_nonneg_right hr1b.le hfa₀
          _ ≤ f a := hm
      linarith
  -- the slope is `1`: the triple `(a₀/4, a₀/4, 1 − a₀/2)`
  have hκ1 : κ = 1 := by
    have hq : ((1 / 4 : ℚ) : ℝ) = 1 / 4 := by norm_num
    obtain ⟨g1, -⟩ := good (1 / 4) (by norm_num) (by rw [hq]; linarith)
    obtain ⟨-, g2⟩ := good (1 / 2) (by norm_num) (by norm_num; linarith)
    rw [hq] at g1
    rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at g2
    have e := hsum (1 / 4 * a₀) (1 / 4 * a₀) (1 - 1 / 2 * a₀) ⟨by positivity, by linarith⟩
      ⟨by positivity, by linarith⟩ ⟨by linarith, by linarith⟩ g1 g1 g2 (by ring)
    rw [hsq _ ⟨by positivity, by linarith⟩ g1 (by linarith),
      hsq _ ⟨by linarith, by linarith⟩ g2 (by linarith)] at e
    linarith
  intro a ha haC
  rcases eq_or_lt_of_le ha.2 with rfl | ha1
  · exact hf1
  · rw [hsq a ha haC ha1, hκ1, one_mul]

end Gleason

end
