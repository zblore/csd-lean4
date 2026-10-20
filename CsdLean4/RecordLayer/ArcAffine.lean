/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.NullSeamGeneralN
public import CsdLean4.Mathlib.MeasureTheory.GluedMeasurePreserving

/-!
# Affine transport between arcs of the record circle, and between rectangles of the fibre

**Category:** 7-SigmaLayer (the record layer — library-shaped, kept here because it is written in
the record layer's own coordinate `rep`).
BACKLOG #137; consumed by `SkewReroute.lean`.

An arc of the record circle is `rep ⁻¹' Ioc x₀ (x₀ + w)`, and the affine map
`arcMap x₀ α λ : θ ↦ ⟨α + λ (rep θ − x₀)⟩` carries it onto the arc `rep ⁻¹' Ioc α (α + λ w)`,
stretching by `λ`. This file proves the transport law for Haar measure — ★ `map_restrict_arcMap`:
the restriction of `volume` to the source arc pushes forward to `λ⁻¹` times the restriction to the
target arc — and its product on the fibre `T²` — ★★ `map_restrict_rectMap`: a map that stretches
by `λ₁` in `θ₁` and by `λ₂` in `θ₂` with `λ₁ λ₂ = 1` carries the restriction to a rectangle onto the
restriction to the image rectangle **exactly**. With `GluedMeasurePreserving.lean` this is all a
rectangle exchange needs.

Also here: `existsUnique_mem_circleCell` — for a probability vector the cells `circleCell r i`
tile the circle **exactly**, every point in exactly one cell (the Born cells of
`CircleFibre.lean` are a.e.-total there; the exact form is what a pointwise readout needs).

## Honest scope

* The arcs are read in the representative `rep ∈ (0, 1]`, so all arcs sit inside one turn; the
  wrap-around arc is not treated (none of the consumers' cells wrap).
* `λ > 0` throughout: orientation-preserving transport only.

References: `CircleFibre.lean` (`rep`, `circleCell`, `volume_rep_preimage`),
`NullSeamGeneralN.lean` (`loSum_zero_val`, `loSum_succ_val`, `loSum_last_add`),
Mathlib `AddCircle.measurePreserving_mk`, `Real.map_volume_mul_left`; `specs/BACKLOG.md` #137.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

/-! ### Exact tiling by the cells of a probability vector -/

/-- A point lies in a cell only if the cell has positive width. -/
theorem pos_of_mem_circleCell {k : ℕ} {r : Fin k → ℝ} {i : Fin k} {θ : CircleFibre}
    (hθ : θ ∈ circleCell r i) : 0 < r i := by
  have h1 : loSum r i < rep θ := hθ.1
  have h2 : rep θ ≤ loSum r i + r i := hθ.2
  linarith

/-- ★ **The cells of a probability vector tile the circle exactly**: every point lies in exactly
one cell. -/
theorem existsUnique_mem_circleCell {k : ℕ} (r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (θ : CircleFibre) : ∃! i, θ ∈ circleCell r i := by
  classical
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      subst h
      simp at hsum
    · exact h
  have hs0 : 0 < rep θ := rep_pos _
  have hs1 : rep θ ≤ 1 := rep_le_one _
  let S := Finset.univ.filter (fun i : Fin k => loSum r i < rep θ)
  have h0 : (⟨0, hk⟩ : Fin k) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [loSum_zero_val r rfl]
    exact hs0
  obtain ⟨i, hiS, hmax⟩ := S.exists_max_image (fun i : Fin k => (i : ℕ)) ⟨_, h0⟩
  have hi : loSum r i < rep θ := (Finset.mem_filter.1 hiS).2
  have hmem : θ ∈ circleCell r i := by
    refine ⟨hi, ?_⟩
    by_cases hlast : i.val + 1 = k
    · rw [loSum_last_add r hsum hlast]
      exact hs1
    · have hlt : i.val + 1 < k := lt_of_le_of_ne i.isLt hlast
      have hj : ¬ loSum r ⟨i.val + 1, hlt⟩ < rep θ := by
        intro hjs
        have := hmax ⟨i.val + 1, hlt⟩ (by simp [S, hjs])
        simp at this
      rw [not_lt, loSum_succ_val r (show (⟨i.val + 1, hlt⟩ : Fin k).val = i.val + 1 from rfl)]
        at hj
      exact hj
  refine ⟨i, hmem, fun j hj => ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint r hr hne) hj hmem

/-! ### The affine map of an arc -/

/-- **The affine map of the record circle** `θ ↦ ⟨α + λ (rep θ − x₀)⟩`: it carries the arc starting
at `x₀` to the arc starting at `α`, stretched by `λ`. -/
def arcMap (x₀ α lam : ℝ) (θ : CircleFibre) : CircleFibre :=
  ((α + lam * (rep θ - x₀) : ℝ) : CircleFibre)

/-- The quotient map `ℝ → CircleFibre` is measurable. -/
theorem measurable_coe_circleFibre : Measurable (fun x : ℝ => (x : CircleFibre)) :=
  (AddCircle.measurePreserving_mk (1 : ℝ) 0).measurable

theorem measurable_arcMap (x₀ α lam : ℝ) : Measurable (arcMap x₀ α lam) :=
  measurable_coe_circleFibre.comp
    (measurable_const.add (measurable_const.mul (measurable_rep.sub measurable_const)))

/-- **Pointwise transport**: a point of the source arc lands in the target arc, at the affine
image of its representative. -/
theorem arcMap_mem {x₀ α lam w : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hαw : α + lam * w ≤ 1)
    {θ : CircleFibre} (hθ : rep θ ∈ Ioc x₀ (x₀ + w)) :
    rep (arcMap x₀ α lam θ) = α + lam * (rep θ - x₀)
      ∧ rep (arcMap x₀ α lam θ) ∈ Ioc α (α + lam * w) := by
  have h1 : 0 < lam * (rep θ - x₀) := mul_pos hlam (sub_pos.2 hθ.1)
  have h2 : lam * (rep θ - x₀) ≤ lam * w :=
    mul_le_mul_of_nonneg_left (by linarith [hθ.2]) hlam.le
  have hmem : α + lam * (rep θ - x₀) ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [arcMap, rep_coe_of_mem_Ioc hmem]
  exact ⟨rfl, ⟨by linarith, by linarith⟩⟩

/-! ### The transport law for Haar measure -/

/-- Haar measure on the circle, read through `rep`, is Lebesgue measure on one turn. -/
theorem map_rep_volume :
    (volume : Measure CircleFibre).map rep = (volume : Measure ℝ).restrict (Ioc 0 1) :=
  Measure.ext fun S hS => by
    rw [Measure.map_apply measurable_rep hS, volume_rep_preimage hS, Measure.restrict_apply hS]

/-- Lebesgue measure on one turn, pushed to the circle, is Haar measure. -/
theorem map_coe_restrict_volume :
    ((volume : Measure ℝ).restrict (Ioc 0 1)).map (fun x : ℝ => (x : CircleFibre))
      = (volume : Measure CircleFibre) := by
  have h := (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq
  simpa using h

/-- The restriction of Haar measure to an arc, pushed to `ℝ` by `rep`, is Lebesgue measure on the
corresponding interval. -/
theorem map_rep_restrict_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ((volume : Measure CircleFibre).restrict (rep ⁻¹' Ioc a b)).map rep
      = (volume : Measure ℝ).restrict (Ioc a b) := by
  rw [← Measure.restrict_map measurable_rep measurableSet_Ioc, map_rep_volume,
    Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  exact inter_eq_left.2 fun x hx => ⟨lt_of_le_of_lt ha hx.1, le_trans hx.2 hb⟩

/-- Lebesgue measure on an interval inside one turn, pushed to the circle, is Haar measure on the
corresponding arc. -/
theorem map_coe_restrict_interval {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ((volume : Measure ℝ).restrict (Ioc a b)).map (fun x : ℝ => (x : CircleFibre))
      = (volume : Measure CircleFibre).restrict (rep ⁻¹' Ioc a b) := by
  have hmeasJ : MeasurableSet (rep ⁻¹' Ioc a b : Set CircleFibre) := measurable_rep measurableSet_Ioc
  rw [← map_coe_restrict_volume, Measure.restrict_map measurable_coe_circleFibre hmeasJ,
    Measure.restrict_restrict (measurable_coe_circleFibre hmeasJ)]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Ioc]
  constructor
  · intro h
    have hx : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha h.1, le_trans h.2 hb⟩
    refine ⟨?_, hx⟩
    rw [rep_coe_of_mem_Ioc hx]
    exact h
  · rintro ⟨h1, h2⟩
    rwa [rep_coe_of_mem_Ioc h2] at h1

/-- The affine map of the line scales Lebesgue measure by `λ⁻¹`. -/
theorem map_volume_affine {lam : ℝ} (hlam : 0 < lam) (c x₀ : ℝ) :
    (volume : Measure ℝ).map (fun x : ℝ => c + lam * (x - x₀))
      = ENNReal.ofReal lam⁻¹ • (volume : Measure ℝ) := by
  have hfun : (fun x : ℝ => c + lam * (x - x₀))
      = (fun y : ℝ => (c - lam * x₀) + y) ∘ (fun x : ℝ => lam * x) := by
    funext x
    simp only [Function.comp_apply]
    ring
  rw [hfun, ← Measure.map_map (measurable_const_add _) (measurable_const_mul _),
    Real.map_volume_mul_left hlam.ne', Measure.map_smul _ (measurable_const_add _).aemeasurable,
    (measurePreserving_add_left volume (c - lam * x₀)).map_eq, abs_of_pos (inv_pos.2 hlam)]

/-- The affine map's preimage of the target interval is the source interval. -/
theorem preimage_affine_Ioc {lam : ℝ} (hlam : 0 < lam) (α x₀ w : ℝ) :
    (fun x : ℝ => α + lam * (x - x₀)) ⁻¹' Ioc α (α + lam * w) = Ioc x₀ (x₀ + w) := by
  ext x
  simp only [mem_preimage, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hle
      have hle' : x ≤ x₀ := not_lt.mp hle
      nlinarith [mul_nonneg hlam.le (sub_nonneg.2 hle')]
    · by_contra hlt
      have hlt' : x₀ + w < x := not_le.mp hlt
      nlinarith [mul_pos hlam (sub_pos.2 hlt')]
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith [mul_pos hlam (sub_pos.2 h1)]
    · nlinarith [mul_le_mul_of_nonneg_left (show x - x₀ ≤ w by linarith) hlam.le]

/-- ★ **The transport law for an arc.** The restriction of Haar measure to the source arc pushes
forward under `arcMap` to `λ⁻¹` times the restriction to the target arc. -/
theorem map_restrict_arcMap {x₀ α lam w : ℝ} (hx₀ : 0 ≤ x₀) (hxw : x₀ + w ≤ 1) (hlam : 0 < lam)
    (hα : 0 ≤ α) (hαw : α + lam * w ≤ 1) :
    ((volume : Measure CircleFibre).restrict (rep ⁻¹' Ioc x₀ (x₀ + w))).map (arcMap x₀ α lam)
      = ENNReal.ofReal lam⁻¹
          • (volume : Measure CircleFibre).restrict (rep ⁻¹' Ioc α (α + lam * w)) := by
  have hg : Measurable (fun x : ℝ => α + lam * (x - x₀)) :=
    measurable_const.add (measurable_const.mul (measurable_id.sub measurable_const))
  have hfun : arcMap x₀ α lam
      = (fun x : ℝ => (x : CircleFibre)) ∘ (fun x : ℝ => α + lam * (x - x₀)) ∘ rep := by
    funext θ
    rfl
  rw [hfun, ← Measure.map_map measurable_coe_circleFibre (hg.comp measurable_rep),
    ← Measure.map_map hg measurable_rep, map_rep_restrict_arc hx₀ hxw,
    ← preimage_affine_Ioc hlam α x₀ w, ← Measure.restrict_map hg measurableSet_Ioc,
    map_volume_affine hlam, Measure.restrict_smul,
    Measure.map_smul _ measurable_coe_circleFibre.aemeasurable, map_coe_restrict_interval hα hαw]

/-! ### Rectangles of the fibre -/

/-- **The affine map of a rectangle of the fibre**: `arcMap` in each coordinate. -/
def rectMap (x₀ α lam₁ y₀ β lam₂ : ℝ) : LF4.KTorus → LF4.KTorus :=
  Prod.map (arcMap x₀ α lam₁) (arcMap y₀ β lam₂)

theorem measurable_rectMap (x₀ α lam₁ y₀ β lam₂ : ℝ) :
    Measurable (rectMap x₀ α lam₁ y₀ β lam₂) :=
  (measurable_arcMap x₀ α lam₁).prodMap (measurable_arcMap y₀ β lam₂)

/-- ★★ **The transport law for a rectangle, Jacobian one.** Stretching by `λ₁` in `θ₁` and `λ₂` in
`θ₂` with `λ₁ λ₂ = 1` carries the restriction of `volume` to the source rectangle **exactly** onto
the restriction to the target rectangle. -/
theorem map_restrict_rectMap {x₀ α lam₁ w y₀ β lam₂ h : ℝ} (hx₀ : 0 ≤ x₀) (hxw : x₀ + w ≤ 1)
    (hlam₁ : 0 < lam₁) (hα : 0 ≤ α) (hαw : α + lam₁ * w ≤ 1) (hy₀ : 0 ≤ y₀) (hyh : y₀ + h ≤ 1)
    (hlam₂ : 0 < lam₂) (hβ : 0 ≤ β) (hβh : β + lam₂ * h ≤ 1) (hjac : lam₁ * lam₂ = 1) :
    ((volume : Measure LF4.KTorus).restrict
        ((rep ⁻¹' Ioc x₀ (x₀ + w)) ×ˢ (rep ⁻¹' Ioc y₀ (y₀ + h)))).map
          (rectMap x₀ α lam₁ y₀ β lam₂)
      = (volume : Measure LF4.KTorus).restrict
          ((rep ⁻¹' Ioc α (α + lam₁ * w)) ×ˢ (rep ⁻¹' Ioc β (β + lam₂ * h))) := by
  rw [rectMap, Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
    ← Measure.map_prod_map _ _ (measurable_arcMap _ _ _) (measurable_arcMap _ _ _),
    map_restrict_arcMap hx₀ hxw hlam₁ hα hαw, map_restrict_arcMap hy₀ hyh hlam₂ hβ hβh,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hlam₁.le), ← mul_inv, hjac, inv_one, ENNReal.ofReal_one,
    one_smul]

end CSD.RecordLayer

end

end
