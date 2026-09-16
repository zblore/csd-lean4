/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Complex projective space is an analytic manifold

**TERM-SCOPE(Kahler)** — "top-power identity" appears below in the *restricted* sense
the terms register records, and in the negative: the identity is what this module does NOT
prove. (Repository bookkeeping; it goes with the `References` block if this is sent upstream.)

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Geometry.Manifold.Instances`, beside `Sphere.lean`).

At the pin, `Projectivization` carries a topology
(staged in this repository), a measurable space, a metric — and **no charted-space instance
anywhere**, so `ℂℙⁿ` was not a manifold in Lean and nothing on it could be differentiated.
MATHLIB-ABSENT(ChartedSpace.projectivization)

This module builds the standard affine atlas and both instances:

* `Projectivization.chartAtIdx i` — the affine chart on `{p | pᵢ ≠ 0}`,
  `[z₀ : ⋯ : zₙ] ↦ (z_{σᵢ(0)}/zᵢ, …, z_{σᵢ(n-1)}/zᵢ)` where `σᵢ = Fin.succAbove i` skips the
  `i`-th slot, with inverse `w ↦ [Fin.insertNth i 1 w]`;
* ★ `Projectivization.instChartedSpace` — `ℂℙⁿ` is a charted space;
* ★ `Projectivization.instIsManifold` — and an **analytic** (`ω`) manifold, not merely `C^∞`:
  the transition maps are ratios of coordinates of `Fin.insertNth i 1 w`, so each is a
  quotient of an affine function by a nonvanishing affine function.

## Design notes

**Why `rep` rather than a quotient lift.** The chart map is defined on the *chosen*
representative (`Projectivization.rep`), which makes well-definedness free but says nothing
about continuity — `rep` is a choice function. Continuity is recovered separately, from
`mk'` being an **open quotient map** (`isQuotientMap_mk'`, staged here) restricted to the
open chart source: `Topology.IsQuotientMap.restrictPreimage_isOpen` turns continuity of the
chart into continuity of the ratio map on nonzero vectors, which is elementary.

**Why the model space is `Fin n → ℂ` and not `EuclideanSpace ℂ (Fin n)`.** At the pin
`WithLp` is a genuine structure rather than a type synonym, so every element of
`EuclideanSpace` must be built through `WithLp.toLp` and every chart formula would carry
that wrapper. The sup-norm `Pi` type is norm-equivalent, carries the same smooth and
analytic structure, and keeps the charts readable. The ambient space stays
`EuclideanSpace ℂ (Fin (n+1))`, which is what the projective space of interest is built on.

## Honest scope

* **This is `ℂℙⁿ` over `ℂ`, on the Euclidean ambient space.** The same charts work over any
  nontrivially normed field and for `ℙ 𝕜 (Fin (n+1) → 𝕜)`; that generalisation is not made
  here and is a natural follow-up.
* **Nothing about forms.** Making `ℂℙⁿ` a manifold does not give differential forms *on*
  manifolds — that is step (2) of the plan and is upstream's own stated TODO. In
  particular the top-power identity `ω^(N-1)/(N-1)! = μ_FS` is still not provable; what
  steps (0) and (1) between them buy is that it can be *said*.
* **No relation to the Fubini–Study metric or measure is proved here.** The charted
  structure is topological/analytic only; that `μ_FS` is the Liouville volume of the
  induced form remains open (step (3)).

**Provenance and references.** The Mathlib-gaps register (Kahler / symplectic manifold API, step (0));
the backlog (XL, "Manifold exterior calculus");
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean` (the quotient topology and
`isQuotientMap_mk'`); `Mathlib.Geometry.Manifold.Instances.Sphere` (the analogous
construction upstream, from stereographic projection).
-/

@[expose] public section

open Projectivization Topology Set
open scoped LinearAlgebra.Projectivization Manifold ContDiff

namespace Projectivization

variable {n : ℕ}

/-- The ambient coordinate space of `ℂℙⁿ`. -/
abbrev Ambient (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))

/-! ### The affine chart, on representatives -/

/-- The affine chart formula on a representative: divide the other coordinates by the
`i`-th one. -/
noncomputable def coordRatio (i : Fin (n + 1)) (v : Ambient n) : Fin n → ℂ :=
  fun j => v (i.succAbove j) / v i

/-- Insert `1` in slot `i`: the affine section of the `i`-th chart. -/
noncomputable def insertOne (i : Fin (n + 1)) (w : Fin n → ℂ) : Ambient n :=
  WithLp.toLp 2 (i.insertNth 1 w)

@[simp]
lemma insertOne_apply_same (i : Fin (n + 1)) (w : Fin n → ℂ) : insertOne i w i = 1 := by
  simp [insertOne]

@[simp]
lemma insertOne_apply_succAbove (i : Fin (n + 1)) (w : Fin n → ℂ) (j : Fin n) :
    insertOne i w (i.succAbove j) = w j := by
  simp [insertOne]

lemma insertOne_ne_zero (i : Fin (n + 1)) (w : Fin n → ℂ) : insertOne i w ≠ 0 := by
  intro h
  have h0 : insertOne i w i = 0 := by rw [h]; simp
  rw [insertOne_apply_same] at h0
  exact one_ne_zero h0

lemma smul_ofLp (c : ℂ) (v : Ambient n) (k : Fin (n + 1)) : (c • v) k = c * v k := rfl

/-- Coordinate ratios do not see the choice of representative. -/
lemma coordRatio_smul (a : ℂˣ) (i : Fin (n + 1)) (v : Ambient n) :
    coordRatio i (a • v) = coordRatio i v := by
  funext j
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  simp only [coordRatio, Units.smul_def, smul_ofLp]
  rw [mul_div_mul_left _ _ ha]

/-! ### The chart maps on `ℂℙⁿ` -/

/-- The `i`-th affine chart of `ℂℙⁿ`. Well defined because `coordRatio` is
representative-independent. -/
noncomputable def chartFun (i : Fin (n + 1)) (p : ℙ ℂ (Ambient n)) : Fin n → ℂ :=
  coordRatio i p.rep

/-- The inverse of the `i`-th affine chart. -/
noncomputable def chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) : ℙ ℂ (Ambient n) :=
  mk ℂ (insertOne i w) (insertOne_ne_zero i w)

/-- The domain of the `i`-th chart: the points whose `i`-th coordinate does not vanish. -/
def chartSource (i : Fin (n + 1)) : Set (ℙ ℂ (Ambient n)) := {p | p.rep i ≠ 0}

lemma chartFun_mk (i : Fin (n + 1)) (v : Ambient n) (hv : v ≠ 0) :
    chartFun i (mk ℂ v hv) = coordRatio i v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ v hv
  rw [chartFun, ← ha, coordRatio_smul]

lemma rep_ne_zero_iff (i : Fin (n + 1)) (v : Ambient n) (hv : v ≠ 0) :
    (mk ℂ v hv).rep i ≠ 0 ↔ v i ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  simp [Units.smul_def, a.ne_zero]

lemma mem_chartSource_mk (i : Fin (n + 1)) (v : Ambient n) (hv : v ≠ 0) :
    mk ℂ v hv ∈ chartSource i ↔ v i ≠ 0 :=
  rep_ne_zero_iff i v hv

lemma preimage_chartSource (i : Fin (n + 1)) :
    (mk' ℂ) ⁻¹' (chartSource i) = {v : {v : Ambient n // v ≠ 0} | (v : Ambient n) i ≠ 0} := by
  ext v
  exact rep_ne_zero_iff i (v : Ambient n) v.2

lemma continuous_coord (k : Fin (n + 1)) :
    Continuous fun v : {v : Ambient n // v ≠ 0} => (v : Ambient n) k := by fun_prop

/-- The chart domain is open: its `mk'`-preimage is a nonvanishing-coordinate condition, and
`mk'` is a quotient map. -/
lemma isOpen_chartSource (i : Fin (n + 1)) : IsOpen (chartSource (n := n) i) := by
  rw [← (isQuotientMap_mk' (K := ℂ) (V := Ambient n)).isOpen_preimage, preimage_chartSource]
  exact isOpen_ne_fun (continuous_coord i) continuous_const

/-! ### The chart is a homeomorphism onto its image -/

lemma chartFun_chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) :
    chartFun i (chartInv i w) = w := by
  funext j
  rw [chartInv, chartFun_mk]
  simp [coordRatio]

lemma continuous_insertOne (i : Fin (n + 1)) : Continuous (insertOne (n := n) i) := by
  unfold insertOne
  fun_prop

lemma continuous_chartInv (i : Fin (n + 1)) : Continuous (chartInv (n := n) i) := by
  have h : chartInv (n := n) i
      = (mk' ℂ) ∘ fun w => (⟨insertOne i w, insertOne_ne_zero i w⟩ :
          {v : Ambient n // v ≠ 0}) := rfl
  rw [h]
  exact continuous_mk'.comp ((continuous_insertOne i).subtype_mk _)

/-- On the chart domain the affine section recovers the representative up to scale. -/
lemma insertOne_chartFun (i : Fin (n + 1)) (p : ℙ ℂ (Ambient n)) (hp : p.rep i ≠ 0) :
    insertOne i (chartFun i p) = (p.rep i)⁻¹ • p.rep := by
  ext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [inv_mul_cancel₀ hp]
  · intro j
    simp [chartFun, coordRatio, div_eq_inv_mul]

lemma chartInv_chartFun (i : Fin (n + 1)) (p : ℙ ℂ (Ambient n)) (hp : p.rep i ≠ 0) :
    chartInv i (chartFun i p) = p := by
  rw [chartInv]
  conv_rhs => rw [← p.mk_rep]
  rw [mk_eq_mk_iff]
  refine ⟨Units.mk0 (p.rep i)⁻¹ (inv_ne_zero hp), ?_⟩
  simpa [Units.smul_def] using (insertOne_chartFun i p hp).symm

/-- Continuity of the chart map. The chart is defined through `rep`, which is a choice
function and carries no continuity of its own; what supplies it is that `mk'` restricted to
the (open) chart domain is still a quotient map. -/
lemma continuousOn_chartFun (i : Fin (n + 1)) :
    ContinuousOn (chartFun (n := n) i) (chartSource i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hq : IsQuotientMap ((chartSource i).restrictPreimage (mk' ℂ)) :=
    (isQuotientMap_mk' (K := ℂ) (V := Ambient n)).restrictPreimage_isOpen
      (isOpen_chartSource i)
  rw [hq.continuous_iff]
  have hcomp : ((chartSource i).domRestrict (chartFun (n := n) i)) ∘
        (chartSource i).restrictPreimage (mk' ℂ)
      = fun v : ↥((mk' ℂ) ⁻¹' chartSource i) =>
          coordRatio i ((v : {v : Ambient n // v ≠ 0}) : Ambient n) := by
    funext v
    simp [Set.domRestrict, Set.restrictPreimage, mk'_eq_mk, chartFun_mk]
  rw [hcomp]
  refine continuous_pi fun j => Continuous.div (by fun_prop) (by fun_prop) fun v => ?_
  have h2 : mk' ℂ (v : {v : Ambient n // v ≠ 0}) ∈ chartSource i := Set.mem_preimage.mp v.2
  rw [mk'_eq_mk] at h2
  exact (mem_chartSource_mk i _ _).mp h2

lemma chartInv_mem_chartSource (i : Fin (n + 1)) (w : Fin n → ℂ) :
    chartInv i w ∈ chartSource i := by
  rw [chartInv]
  exact (mem_chartSource_mk i _ _).mpr (by rw [insertOne_apply_same]; exact one_ne_zero)

/-- ★ **The `i`-th affine chart of `ℂℙⁿ`**, as an open partial homeomorphism onto
`Fin n → ℂ`. -/
noncomputable def chartAtIdx (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ℙ ℂ (Ambient n)) (Fin n → ℂ) where
  toFun := chartFun i
  invFun := chartInv i
  source := chartSource i
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' w _ := chartInv_mem_chartSource i w
  left_inv' p hp := chartInv_chartFun i p hp
  right_inv' w _ := chartFun_chartInv i w
  open_source := isOpen_chartSource i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_chartFun i
  continuousOn_invFun := (continuous_chartInv i).continuousOn

/-! ### The charted space and manifold instances -/

lemma exists_ne_zero_coord (p : ℙ ℂ (Ambient n)) : ∃ i, p.rep i ≠ 0 := by
  by_contra h
  refine p.rep_nonzero ?_
  ext k
  simpa using not_exists.mp h k

/-- Some coordinate index at which the point does not vanish; the chart chosen at `p`. -/
noncomputable def idx (p : ℙ ℂ (Ambient n)) : Fin (n + 1) := (exists_ne_zero_coord p).choose

lemma idx_spec (p : ℙ ℂ (Ambient n)) : p.rep (idx p) ≠ 0 := (exists_ne_zero_coord p).choose_spec

/-- ★ **Complex projective space is a charted space**, on the standard affine atlas. -/
noncomputable instance instChartedSpace :
    ChartedSpace (Fin n → ℂ) (ℙ ℂ (Ambient n)) where
  atlas := Set.range chartAtIdx
  chartAt p := chartAtIdx (idx p)
  mem_chart_source p := idx_spec p
  chart_mem_atlas p := ⟨idx p, rfl⟩

/-- Each coordinate of the affine section is analytic in the chart variable: it is either the
constant `1` or a coordinate projection. -/
lemma contDiff_insertOne_coord (i m : Fin (n + 1)) :
    ContDiff ℂ ω (fun w : Fin n → ℂ => insertOne i w m) := by
  refine Fin.succAboveCases i ?_ ?_ m
  · simp only [insertOne_apply_same]
    exact contDiff_const
  · intro j
    simp only [insertOne_apply_succAbove]
    exact contDiff_apply ℂ ℂ j

/-- The transition maps are analytic: each component is a ratio of two coordinates of
`insertNth i 1 w`, and the denominator does not vanish on the overlap. -/
lemma contDiffOn_transition (i j : Fin (n + 1)) :
    ContDiffOn ℂ ω (fun w : Fin n → ℂ => coordRatio j (insertOne i w))
      {w : Fin n → ℂ | insertOne i w j ≠ 0} := by
  refine contDiffOn_pi.2 fun k => ?_
  exact ContDiffOn.div (contDiff_insertOne_coord i _).contDiffOn
    (contDiff_insertOne_coord i j).contDiffOn fun w hw => hw

/-- ★ **Complex projective space is an analytic manifold.**

Not merely `C^∞`: the transition maps are quotients of coordinates of `Fin.insertNth i 1 w`
with nonvanishing denominators, so `ω` comes out of the same argument. -/
noncomputable instance instIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin n → ℂ)) ω (ℙ ℂ (Ambient n)) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  have hset : ((chartAtIdx (n := n) i).symm ≫ₕ chartAtIdx j).source
      = {w : Fin n → ℂ | insertOne i w j ≠ 0} := by
    ext w
    simp [chartAtIdx, chartInv, mem_chartSource_mk, insertOne]
  have hfun : ∀ w : Fin n → ℂ,
      ((chartAtIdx (n := n) i).symm ≫ₕ chartAtIdx j) w = coordRatio j (insertOne i w) := by
    intro w
    show chartFun j (chartInv i w) = _
    rw [chartInv, chartFun_mk]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq, hset]
  exact (contDiffOn_transition i j).congr fun w _ => hfun w

/-- ★ **The same atlas, read over `ℝ`.** A `ℂ`-analytic manifold is `ℝ`-analytic
(`ContDiffOn.restrict_scalars`), and the real structure is the one a *real* differential
form — the Fubini–Study form is `ℝ`-bilinear, not `ℂ`-bilinear — has to live on. -/
noncomputable instance instIsManifoldReal :
    IsManifold (modelWithCornersSelf ℝ (Fin n → ℂ)) ω (ℙ ℂ (Ambient n)) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  have hset : ((chartAtIdx (n := n) i).symm ≫ₕ chartAtIdx j).source
      = {w : Fin n → ℂ | insertOne i w j ≠ 0} := by
    ext w
    simp [chartAtIdx, chartInv, mem_chartSource_mk, insertOne]
  have hfun : ∀ w : Fin n → ℂ,
      ((chartAtIdx (n := n) i).symm ≫ₕ chartAtIdx j) w = coordRatio j (insertOne i w) := by
    intro w
    show chartFun j (chartInv i w) = _
    rw [chartInv, chartFun_mk]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq, hset]
  exact ((contDiffOn_transition i j).restrict_scalars ℝ).congr fun w _ => hfun w

end Projectivization
