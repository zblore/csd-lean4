/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SkewFibrePartition
public import CsdLean4.RecordLayer.ArcAffine
public import CsdLean4.LF3.SettingLocalityLocal

/-!
# The setting-locality primitive at the I3 record basins: the skew rectangle exchange

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #137 (out of #131 obligation (4)): the instantiation the audit asked for.

## The choice, in one paragraph

**I3**, and the reroute is a **rectangle exchange**. Under I3 the fibre `T²` is tiled exactly by the
skew cells `skewCell q s t = A_s × B_{s,t}` of the joint context's table `q`
(`existsUnique_mem_skewCell`); A reads the `θ₁`-cell, B the `θ₂`-cell *conditional on A's*. A change
of B's setting leaves A's cells alone when the tables are no-signalling (`rowSum` independent of
`b`), so **A's reroute is the identity** (`wingA_eq_of_rowSum_eq`). For B, a change of A's setting
`a ↦ a'` replaces the table `q = Q⟨a, b⟩` by `q' = Q⟨a', b⟩`, and B's region for the outcome `t`,
`⋃ₛ A_s × B_{s,t}`, is a different staircase of the same total height `colSum t`. The reroute
**normalises** each skew cell `A_s × B_{s,t}` onto a rectangle `N_{s,t}` of the horizontal band
`[0,1) × C_t` (`C_t` the arc of `colSum t`), by the Jacobian-one affine map that stretches `θ₁` by
`(rate s t / colSum t) / rowSum s` and `θ₂` by its reciprocal (`toNormal`, `normalize`), and then
**denormalises** with the inverse exchange for `q'` (`toSkew`, `denormalize`):
`reroute q q' = denormalize q' ∘ normalize q`. Each half is a glued family of Jacobian-one affine
rectangle maps between two exact tilings (`GluedMeasurePreserving.lean`, `ArcAffine.lean`), hence
measure-preserving (★★ `measurePreserving_reroute`); the band `C_t` is the same for `q` and `q'`
because `colSum` is, so B's reading is carried along (★★ `wingB_reroute`). The map is *not*
fibrewise (it moves `θ₁` across A's cells), which is exactly what
`eq_of_vadd_preimage_circleCell_eq` said it must do.

## What is proved

* `existsUnique_mem_skewCell`, `existsUnique_mem_normalCell`: the skew cells and the normal cells
  are **exact** tilings of the fibre; `skewIdx` / `normalIdx` read the cell of a point.
* `toNormal`, `toSkew`: the Jacobian-one affine maps between a skew cell and its normal cell, and
  back; `toNormal_mem`, `toSkew_mem` (pointwise), ★ `map_restrict_toNormal`, ★ `map_restrict_toSkew`
  (the measure transport, exact).
* `normalize`, `denormalize`: the glued exchanges; ★★ `measurePreserving_normalize`,
  ★★ `measurePreserving_denormalize`.
* `reroute q q'`: ★★ `measurePreserving_reroute`, ★★ `wingB_reroute` (needs `q.colSum = q'.colSum`);
  `wingA_eq_of_rowSum_eq`.
* The LF3 instance, for a family of `2 × 2` tables `Q : MeasurementContext → JointRates 2 2`:
  `skewOutcomeMaps Q` (A reads the `θ₁`-cell, B the conditional `θ₂`-cell, as signs),
  `measurable_skewOutcomeMaps`; ★★★ `skewLocalSettingLocalityA` (identity reroute, needs A's
  marginal independent of `b`), ★★★ `skewLocalSettingLocalityB` (the rectangle exchange, needs B's
  marginal independent of `a`); ★★★ `operationalNoSignalling_skew`: **operational no-signalling
  for the I3 record basins, derived from the primitive** — not assumed from the tables' marginals,
  although it needs them to agree, which is what makes the primitive instantiable at all.

## ⚠️ The finding: the blind primitive is unsatisfiable here

`LF3.RemoteSettingLocalityB` wants one `reroute a a'` for **all** `b`. The exchange above depends on
`b` through `Q⟨a, b⟩`, and no `b`-blind map can replace it for Bell-violating tables: a `b`-blind
map carries `R_t(a,b) ∩ R_{t'}(a,b')` onto `R_t(a',b) ∩ R_{t'}(a',b')`, so the counterfactual joint
law of B's two readings would have to be independent of `a`, and for the singlet at the CHSH
settings it is not (the computation is in `LF3/SettingLocalityLocal.lean`). What the record layer
satisfies is the **local-setting-aware** primitive `LocalSettingLocalityB`, which derives the same
no-signalling. Formalising the obstruction is a priced row.

## Honest scope

* **The fibre, with the tables as data.** `Σ = T²` here with Haar measure; the base-coupled version
  (`SkewBasin.lean`'s `skewBasin` over `KSigma N`, with `epistemicMeasure p = δ_p ⊗ vol`) is the
  same construction fibrewise over the base point and is priced as the continuation.
* **No-signalling of the tables is a hypothesis** on `Q` (`rowSum` independent of `b`, `colSum` of
  `a`). It is what the Born tables of any joint context satisfy, and it is *necessary* for the
  primitive (the readings' marginals must agree); nothing here derives it from dynamics.
* **`2 × 2` outcomes** in the LF3 instance, because `SharedContextOutcomeMaps` reads `Sign × Sign`;
  the exchange itself is for arbitrary `m × n`.
* **No `P_st`.** The tables are arbitrary no-signalling tables; the singlet is not instantiated.

References: `SkewFibrePartition.lean` (`skewCell`, `JointRates`, `eq_of_vadd_preimage_circleCell_eq`),
`ArcAffine.lean` (`rectMap`, `map_restrict_rectMap`, `existsUnique_mem_circleCell`),
`Mathlib/MeasureTheory/GluedMeasurePreserving.lean` (`glue`, `measurePreserving_glue`),
`LF3/SettingLocalityLocal.lean` (`LocalSettingLocalityA/B`,
`operationalNoSignalling_of_localSettingLocality`); `specs/BACKLOG.md` #137, #131 obligation (4).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

variable {m n : ℕ}

/-! ### The normal form: bands by B's outcome, split by A's share of the column -/

namespace JointRates

variable (q : JointRates m n)

/-- A's share of B's column `t`: `rate s t / colSum t`. -/
def colFrac (t : Fin n) (s : Fin m) : ℝ := q.rate s t / q.colSum t

theorem colFrac_nonneg (t : Fin n) (s : Fin m) : 0 ≤ q.colFrac t s :=
  div_nonneg (q.nonneg s t) (q.colSum_nonneg t)

theorem sum_colFrac_of_pos {t : Fin n} (h : 0 < q.colSum t) : ∑ s, q.colFrac t s = 1 := by
  simp only [colFrac, ← Finset.sum_div]
  show q.colSum t / q.colSum t = 1
  exact div_self h.ne'

theorem colSum_mul_colFrac (t : Fin n) (s : Fin m) : q.colSum t * q.colFrac t s = q.rate s t := by
  by_cases h : q.colSum t = 0
  · have : q.rate s t = 0 := by
      have hle : q.rate s t ≤ q.colSum t :=
        Finset.single_le_sum (fun s' _ => q.nonneg s' t) (Finset.mem_univ s)
      linarith [q.nonneg s t]
    rw [h, this, zero_mul]
  · rw [colFrac, mul_div_cancel₀ _ h]

theorem rate_pos_iff (s : Fin m) (t : Fin n) :
    0 < q.rate s t ↔ 0 < q.rowSum s ∧ 0 < q.condRate s t := by
  constructor
  · intro h
    have hrow : 0 < q.rowSum s := by
      rcases (q.rowSum_nonneg s).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (q.rate_eq_zero_of_rowSum_eq_zero h'.symm t) h.ne'
    exact ⟨hrow, div_pos h hrow⟩
  · rintro ⟨h1, h2⟩
    rw [← q.rowSum_mul_condRate]
    exact mul_pos h1 h2

theorem colSum_pos_of_rate_pos {s : Fin m} {t : Fin n} (h : 0 < q.rate s t) : 0 < q.colSum t :=
  lt_of_lt_of_le h (Finset.single_le_sum (fun s' _ => q.nonneg s' t) (Finset.mem_univ s))

theorem colFrac_pos_of_rate_pos {s : Fin m} {t : Fin n} (h : 0 < q.rate s t) :
    0 < q.colFrac t s :=
  div_pos h (q.colSum_pos_of_rate_pos h)

end JointRates

/-- **The normal cell** of the outcome pair `(s, t)`: A's share of B's column, in `θ₁`, times the
arc of B's marginal, in `θ₂`. The normal cells with the same `t` tile the band `[0,1) × C_t`. -/
def normalCell (q : JointRates m n) (s : Fin m) (t : Fin n) : Set LF4.KTorus :=
  circleCell (q.colFrac t) s ×ˢ circleCell q.colSum t

theorem measurableSet_normalCell (q : JointRates m n) (s : Fin m) (t : Fin n) :
    MeasurableSet (normalCell q s t) :=
  (measurableSet_circleCell _ s).prod (measurableSet_circleCell _ t)

/-! ### Both families tile the fibre exactly -/

/-- ★ **The skew cells tile the fibre exactly**: every point lies in exactly one. -/
theorem existsUnique_mem_skewCell (q : JointRates m n) (θ : LF4.KTorus) :
    ∃! st : Fin m × Fin n, θ ∈ skewCell q st.1 st.2 := by
  obtain ⟨s, hs, -⟩ := existsUnique_mem_circleCell q.rowSum q.rowSum_nonneg q.sum_rowSum θ.1
  have hpos : 0 < q.rowSum s := pos_of_mem_circleCell hs
  obtain ⟨t, ht, -⟩ := existsUnique_mem_circleCell (q.condRate s) (q.condRate_nonneg s)
    (q.sum_condRate_of_pos hpos) θ.2
  refine ⟨(s, t), ⟨hs, ht⟩, fun st' hst' => ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (skewCell_pairwiseDisjoint q hne) hst' ⟨hs, ht⟩

/-- Distinct normal cells are disjoint: different `t` separate in `θ₂`, the same `t` with different
`s` in `θ₁`. -/
theorem normalCell_pairwiseDisjoint (q : JointRates m n) :
    Pairwise (Function.onFun Disjoint fun st : Fin m × Fin n => normalCell q st.1 st.2) := by
  intro st st' hne
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  by_cases ht : st.2 = st'.2
  · have hs : st.1 ≠ st'.1 := fun h => hne (Prod.ext h ht)
    have h1 : x.1 ∈ circleCell (q.colFrac st.2) st.1 := hx.1
    have h2 : x.1 ∈ circleCell (q.colFrac st.2) st'.1 := by
      rw [ht]; exact hx'.1
    exact Set.disjoint_left.mp
      (circleCell_pairwiseDisjoint _ (q.colFrac_nonneg st.2) hs) h1 h2
  · exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint _ q.colSum_nonneg ht) hx.2 hx'.2

/-- ★ **The normal cells tile the fibre exactly.** -/
theorem existsUnique_mem_normalCell (q : JointRates m n) (θ : LF4.KTorus) :
    ∃! st : Fin m × Fin n, θ ∈ normalCell q st.1 st.2 := by
  obtain ⟨t, ht, -⟩ := existsUnique_mem_circleCell q.colSum q.colSum_nonneg q.sum_colSum θ.2
  have hpos : 0 < q.colSum t := pos_of_mem_circleCell ht
  obtain ⟨s, hs, -⟩ := existsUnique_mem_circleCell (q.colFrac t) (q.colFrac_nonneg t)
    (q.sum_colFrac_of_pos hpos) θ.1
  refine ⟨(s, t), ⟨hs, ht⟩, fun st' hst' => ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (normalCell_pairwiseDisjoint q hne) hst' ⟨hs, ht⟩

/-- The cell of a point, in the skew tiling. -/
def skewIdx (q : JointRates m n) (θ : LF4.KTorus) : Fin m × Fin n :=
  glueIdx (existsUnique_mem_skewCell q) θ

theorem mem_skewCell_skewIdx (q : JointRates m n) (θ : LF4.KTorus) :
    θ ∈ skewCell q (skewIdx q θ).1 (skewIdx q θ).2 :=
  mem_glueIdx (existsUnique_mem_skewCell q) θ

theorem skewIdx_eq_of_mem (q : JointRates m n) {θ : LF4.KTorus} {s : Fin m} {t : Fin n}
    (h : θ ∈ skewCell q s t) : skewIdx q θ = (s, t) :=
  glueIdx_eq (existsUnique_mem_skewCell q) (i := (s, t)) h

/-- The cell of a point, in the normal tiling. -/
def normalIdx (q : JointRates m n) (θ : LF4.KTorus) : Fin m × Fin n :=
  glueIdx (existsUnique_mem_normalCell q) θ

theorem mem_normalCell_normalIdx (q : JointRates m n) (θ : LF4.KTorus) :
    θ ∈ normalCell q (normalIdx q θ).1 (normalIdx q θ).2 :=
  mem_glueIdx (existsUnique_mem_normalCell q) θ

/-- A point of the band `C_t` has normal index `t` in the second slot. -/
theorem normalIdx_snd_eq_of_mem (q : JointRates m n) {θ : LF4.KTorus} {t : Fin n}
    (h : θ.2 ∈ circleCell q.colSum t) : (normalIdx q θ).2 = t := by
  by_contra hne
  exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint _ q.colSum_nonneg hne)
    (mem_normalCell_normalIdx q θ).2 h

/-- Membership in a cell forces a positive rate. -/
theorem rate_pos_of_mem_skewCell (q : JointRates m n) {θ : LF4.KTorus} {s : Fin m} {t : Fin n}
    (h : θ ∈ skewCell q s t) : 0 < q.rate s t :=
  (q.rate_pos_iff s t).2 ⟨pos_of_mem_circleCell h.1, pos_of_mem_circleCell h.2⟩

theorem rate_pos_of_mem_normalCell (q : JointRates m n) {θ : LF4.KTorus} {s : Fin m} {t : Fin n}
    (h : θ ∈ normalCell q s t) : 0 < q.rate s t := by
  have h1 : 0 < q.colFrac t s := pos_of_mem_circleCell h.1
  have h2 : 0 < q.colSum t := pos_of_mem_circleCell h.2
  rw [← q.colSum_mul_colFrac]
  exact mul_pos h2 h1

/-! ### The affine pieces -/

/-- **The piece of the normalisation**: the Jacobian-one affine map of the skew cell `(s, t)` onto
its normal cell. -/
def toNormal (q : JointRates m n) (s : Fin m) (t : Fin n) : LF4.KTorus → LF4.KTorus :=
  rectMap (loSum q.rowSum s) (loSum (q.colFrac t) s) (q.colFrac t s / q.rowSum s)
    (loSum (q.condRate s) t) (loSum q.colSum t) (q.colSum t / q.condRate s t)

/-- **The piece of the denormalisation**: the inverse affine map, normal cell onto skew cell. -/
def toSkew (q : JointRates m n) (s : Fin m) (t : Fin n) : LF4.KTorus → LF4.KTorus :=
  rectMap (loSum (q.colFrac t) s) (loSum q.rowSum s) (q.rowSum s / q.colFrac t s)
    (loSum q.colSum t) (loSum (q.condRate s) t) (q.condRate s t / q.colSum t)

theorem measurable_toNormal (q : JointRates m n) (s : Fin m) (t : Fin n) :
    Measurable (toNormal q s t) := measurable_rectMap _ _ _ _ _ _

theorem measurable_toSkew (q : JointRates m n) (s : Fin m) (t : Fin n) :
    Measurable (toSkew q s t) := measurable_rectMap _ _ _ _ _ _

/-- The lower endpoints of the cells are non-negative. -/
theorem loSum_nonneg' {k : ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 ≤ r i) (i : Fin k) : 0 ≤ loSum r i :=
  Finset.sum_nonneg fun j _ => hr j

/-- **Pointwise**: a point of the skew cell lands in the normal cell. -/
theorem toNormal_mem (q : JointRates m n) {s : Fin m} {t : Fin n} {θ : LF4.KTorus}
    (h : θ ∈ skewCell q s t) : toNormal q s t θ ∈ normalCell q s t := by
  have hrate := rate_pos_of_mem_skewCell q h
  obtain ⟨hrow, hcond⟩ := (q.rate_pos_iff s t).1 hrate
  have hcol := q.colSum_pos_of_rate_pos hrate
  have hfrac := q.colFrac_pos_of_rate_pos hrate
  have h1 := arcMap_mem (x₀ := loSum q.rowSum s) (w := q.rowSum s)
    (div_pos hfrac hrow) (loSum_nonneg' (q.colFrac_nonneg t) s)
    (by rw [div_mul_cancel₀ _ hrow.ne']
        exact loSum_add_self_le_one _ (q.colFrac_nonneg t) (q.sum_colFrac_of_pos hcol) s) h.1
  have h2 := arcMap_mem (x₀ := loSum (q.condRate s) t) (w := q.condRate s t)
    (div_pos hcol hcond) (loSum_nonneg' q.colSum_nonneg t)
    (by rw [div_mul_cancel₀ _ hcond.ne']
        exact loSum_add_self_le_one _ q.colSum_nonneg q.sum_colSum t) h.2
  refine ⟨?_, ?_⟩
  · have := h1.2
    rwa [div_mul_cancel₀ _ hrow.ne'] at this
  · have := h2.2
    rwa [div_mul_cancel₀ _ hcond.ne'] at this

/-- **Pointwise**: a point of the normal cell lands in the skew cell. -/
theorem toSkew_mem (q : JointRates m n) {s : Fin m} {t : Fin n} {θ : LF4.KTorus}
    (h : θ ∈ normalCell q s t) : toSkew q s t θ ∈ skewCell q s t := by
  have hrate := rate_pos_of_mem_normalCell q h
  obtain ⟨hrow, hcond⟩ := (q.rate_pos_iff s t).1 hrate
  have hcol := q.colSum_pos_of_rate_pos hrate
  have hfrac := q.colFrac_pos_of_rate_pos hrate
  have h1 := arcMap_mem (x₀ := loSum (q.colFrac t) s) (w := q.colFrac t s)
    (div_pos hrow hfrac) (loSum_nonneg' q.rowSum_nonneg s)
    (by rw [div_mul_cancel₀ _ hfrac.ne']
        exact q.loSum_rowSum_le_one s) h.1
  have h2 := arcMap_mem (x₀ := loSum q.colSum t) (w := q.colSum t)
    (div_pos hcond hcol) (loSum_nonneg' (q.condRate_nonneg s) t)
    (by rw [div_mul_cancel₀ _ hcol.ne']
        exact q.loSum_condRate_le_one s t) h.2
  refine ⟨?_, ?_⟩
  · have := h1.2
    rwa [div_mul_cancel₀ _ hfrac.ne'] at this
  · have := h2.2
    rwa [div_mul_cancel₀ _ hcol.ne'] at this

/-- A skew cell with zero rate is empty. -/
theorem skewCell_eq_empty_of_rate_eq_zero (q : JointRates m n) {s : Fin m} {t : Fin n}
    (h : q.rate s t = 0) : skewCell q s t = ∅ := by
  ext θ
  simp only [mem_empty_iff_false, iff_false]
  intro hθ
  exact (rate_pos_of_mem_skewCell q hθ).ne' h

/-- A normal cell with zero rate is empty. -/
theorem normalCell_eq_empty_of_rate_eq_zero (q : JointRates m n) {s : Fin m} {t : Fin n}
    (h : q.rate s t = 0) : normalCell q s t = ∅ := by
  ext θ
  simp only [mem_empty_iff_false, iff_false]
  intro hθ
  exact (rate_pos_of_mem_normalCell q hθ).ne' h

/-- ★ **The measure transport of a normalisation piece**: exact, with no scalar. -/
theorem map_restrict_toNormal (q : JointRates m n) (s : Fin m) (t : Fin n) :
    ((volume : Measure LF4.KTorus).restrict (skewCell q s t)).map (toNormal q s t)
      = (volume : Measure LF4.KTorus).restrict (normalCell q s t) := by
  rcases (q.nonneg s t).lt_or_eq with hrate | hrate
  · obtain ⟨hrow, hcond⟩ := (q.rate_pos_iff s t).1 hrate
    have hcol := q.colSum_pos_of_rate_pos hrate
    have hfrac := q.colFrac_pos_of_rate_pos hrate
    have hjac : q.colFrac t s / q.rowSum s * (q.colSum t / q.condRate s t) = 1 := by
      rw [div_mul_div_comm, mul_comm (q.colFrac t s), q.colSum_mul_colFrac,
        q.rowSum_mul_condRate, div_self hrate.ne']
    have key := map_restrict_rectMap (x₀ := loSum q.rowSum s) (w := q.rowSum s)
      (α := loSum (q.colFrac t) s) (lam₁ := q.colFrac t s / q.rowSum s)
      (y₀ := loSum (q.condRate s) t) (h := q.condRate s t) (β := loSum q.colSum t)
      (lam₂ := q.colSum t / q.condRate s t)
      (loSum_nonneg' q.rowSum_nonneg s) (q.loSum_rowSum_le_one s) (div_pos hfrac hrow)
      (loSum_nonneg' (q.colFrac_nonneg t) s)
      (by rw [div_mul_cancel₀ _ hrow.ne']
          exact loSum_add_self_le_one _ (q.colFrac_nonneg t) (q.sum_colFrac_of_pos hcol) s)
      (loSum_nonneg' (q.condRate_nonneg s) t) (q.loSum_condRate_le_one s t) (div_pos hcol hcond)
      (loSum_nonneg' q.colSum_nonneg t)
      (by rw [div_mul_cancel₀ _ hcond.ne']
          exact loSum_add_self_le_one _ q.colSum_nonneg q.sum_colSum t) hjac
    rw [div_mul_cancel₀ _ hrow.ne', div_mul_cancel₀ _ hcond.ne'] at key
    exact key
  · rw [skewCell_eq_empty_of_rate_eq_zero q hrate.symm,
      normalCell_eq_empty_of_rate_eq_zero q hrate.symm, Measure.restrict_empty, Measure.map_zero]

/-- ★ **The measure transport of a denormalisation piece**: exact, with no scalar. -/
theorem map_restrict_toSkew (q : JointRates m n) (s : Fin m) (t : Fin n) :
    ((volume : Measure LF4.KTorus).restrict (normalCell q s t)).map (toSkew q s t)
      = (volume : Measure LF4.KTorus).restrict (skewCell q s t) := by
  rcases (q.nonneg s t).lt_or_eq with hrate | hrate
  · obtain ⟨hrow, hcond⟩ := (q.rate_pos_iff s t).1 hrate
    have hcol := q.colSum_pos_of_rate_pos hrate
    have hfrac := q.colFrac_pos_of_rate_pos hrate
    have hjac : q.rowSum s / q.colFrac t s * (q.condRate s t / q.colSum t) = 1 := by
      rw [div_mul_div_comm, q.rowSum_mul_condRate, mul_comm (q.colFrac t s),
        q.colSum_mul_colFrac, div_self hrate.ne']
    have key := map_restrict_rectMap (x₀ := loSum (q.colFrac t) s) (w := q.colFrac t s)
      (α := loSum q.rowSum s) (lam₁ := q.rowSum s / q.colFrac t s)
      (y₀ := loSum q.colSum t) (h := q.colSum t) (β := loSum (q.condRate s) t)
      (lam₂ := q.condRate s t / q.colSum t)
      (loSum_nonneg' (q.colFrac_nonneg t) s)
      (loSum_add_self_le_one _ (q.colFrac_nonneg t) (q.sum_colFrac_of_pos hcol) s)
      (div_pos hrow hfrac) (loSum_nonneg' q.rowSum_nonneg s)
      (by rw [div_mul_cancel₀ _ hfrac.ne']
          exact q.loSum_rowSum_le_one s)
      (loSum_nonneg' q.colSum_nonneg t) (loSum_add_self_le_one _ q.colSum_nonneg q.sum_colSum t)
      (div_pos hcond hcol) (loSum_nonneg' (q.condRate_nonneg s) t)
      (by rw [div_mul_cancel₀ _ hcol.ne']
          exact q.loSum_condRate_le_one s t) hjac
    rw [div_mul_cancel₀ _ hfrac.ne', div_mul_cancel₀ _ hcol.ne'] at key
    exact key
  · rw [skewCell_eq_empty_of_rate_eq_zero q hrate.symm,
      normalCell_eq_empty_of_rate_eq_zero q hrate.symm, Measure.restrict_empty, Measure.map_zero]

/-! ### The glued exchanges -/

/-- **The normalisation**: on each skew cell, its affine piece. -/
def normalize (q : JointRates m n) : LF4.KTorus → LF4.KTorus :=
  glue (existsUnique_mem_skewCell q) fun st => toNormal q st.1 st.2

/-- **The denormalisation**: on each normal cell, its affine piece. -/
def denormalize (q : JointRates m n) : LF4.KTorus → LF4.KTorus :=
  glue (existsUnique_mem_normalCell q) fun st => toSkew q st.1 st.2

theorem normalize_mem (q : JointRates m n) {θ : LF4.KTorus} {s : Fin m} {t : Fin n}
    (h : θ ∈ skewCell q s t) : normalize q θ ∈ normalCell q s t := by
  rw [normalize, glue_eq_of_mem _ _ (i := (s, t)) h]
  exact toNormal_mem q h

theorem denormalize_mem (q : JointRates m n) {θ : LF4.KTorus} {s : Fin m} {t : Fin n}
    (h : θ ∈ normalCell q s t) : denormalize q θ ∈ skewCell q s t := by
  rw [denormalize, glue_eq_of_mem _ _ (i := (s, t)) h]
  exact toSkew_mem q h

/-- ★★ **The normalisation preserves Haar measure** — the gluing theorem over the exact tilings. -/
theorem measurePreserving_normalize (q : JointRates m n) :
    MeasurePreserving (normalize q) (volume : Measure LF4.KTorus) volume :=
  measurePreserving_glue volume (existsUnique_mem_skewCell q)
    (fun st => measurableSet_skewCell q st.1 st.2) (existsUnique_mem_normalCell q)
    (fun st => measurableSet_normalCell q st.1 st.2) (fun st => measurable_toNormal q st.1 st.2)
    (fun st => map_restrict_toNormal q st.1 st.2)

/-- ★★ **The denormalisation preserves Haar measure.** -/
theorem measurePreserving_denormalize (q : JointRates m n) :
    MeasurePreserving (denormalize q) (volume : Measure LF4.KTorus) volume :=
  measurePreserving_glue volume (existsUnique_mem_normalCell q)
    (fun st => measurableSet_normalCell q st.1 st.2) (existsUnique_mem_skewCell q)
    (fun st => measurableSet_skewCell q st.1 st.2) (fun st => measurable_toSkew q st.1 st.2)
    (fun st => map_restrict_toSkew q st.1 st.2)

/-! ### The reroute -/

/-- **The reroute from the table `q` to the table `q'`**: normalise along `q`, denormalise along
`q'`. -/
def reroute (q q' : JointRates m n) : LF4.KTorus → LF4.KTorus :=
  denormalize q' ∘ normalize q

/-- ★★ **The reroute preserves Haar measure.** -/
theorem measurePreserving_reroute (q q' : JointRates m n) :
    MeasurePreserving (reroute q q') (volume : Measure LF4.KTorus) volume :=
  (measurePreserving_denormalize q').comp (measurePreserving_normalize q)

/-- ★★ **B's reading is carried along the reroute** when B's marginal is the same in both tables:
the normal form of a point of B's `t`-region lies in the band `C_t`, and the band is the same for
`q'`, so the denormalisation lands in `q'`'s `t`-region. -/
theorem wingB_reroute {q q' : JointRates m n} (hcol : q.colSum = q'.colSum) (θ : LF4.KTorus) :
    (skewIdx q' (reroute q q' θ)).2 = (skewIdx q θ).2 := by
  set st := skewIdx q θ with hst
  have hθ : θ ∈ skewCell q st.1 st.2 := mem_skewCell_skewIdx q θ
  have h1 : normalize q θ ∈ normalCell q st.1 st.2 := normalize_mem q hθ
  have hband : (normalize q θ).2 ∈ circleCell q'.colSum st.2 := by
    rw [← hcol]; exact h1.2
  have h2 : (normalIdx q' (normalize q θ)).2 = st.2 := normalIdx_snd_eq_of_mem q' hband
  have h3 : denormalize q' (normalize q θ)
      ∈ skewCell q' (normalIdx q' (normalize q θ)).1 (normalIdx q' (normalize q θ)).2 :=
    denormalize_mem q' (mem_normalCell_normalIdx q' _)
  rw [reroute, Function.comp_apply, skewIdx_eq_of_mem q' h3, h2]

/-- A's reading does not depend on the table beyond A's marginal: with the same `rowSum`, the same
`θ₁`-cell. -/
theorem wingA_eq_of_rowSum_eq {q q' : JointRates m n} (hrow : q.rowSum = q'.rowSum)
    (θ : LF4.KTorus) : (skewIdx q' θ).1 = (skewIdx q θ).1 := by
  have h : θ.1 ∈ circleCell q'.rowSum (skewIdx q θ).1 := by
    rw [← hrow]; exact (mem_skewCell_skewIdx q θ).1
  by_contra hne
  exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint _ q'.rowSum_nonneg hne)
    (mem_skewCell_skewIdx q' θ).1 h

/-! ### The LF3 instance: the I3 record basins satisfy the local-setting-aware primitive -/

open LF3

/-- The outcome index as a sign: `0 ↦ plus`, `1 ↦ minus`. -/
def signOfFin : Fin 2 → Sign := ![Sign.plus, Sign.minus]

/-- **The I3 outcome maps** of a family of `2 × 2` joint tables, one per context: A reads the
`θ₁`-cell of the context's table, B the conditional `θ₂`-cell. -/
def skewOutcomeMaps (Q : MeasurementContext → JointRates 2 2) :
    SharedContextOutcomeMaps LF4.KTorus where
  F := fun C θ => (signOfFin (skewIdx (Q C) θ).1, signOfFin (skewIdx (Q C) θ).2)

/-- The cell index is measurable: its level sets are the cells. -/
theorem measurable_skewIdx (q : JointRates m n) : Measurable (skewIdx q) := by
  refine measurable_to_countable' fun st => ?_
  have : skewIdx q ⁻¹' {st} = skewCell q st.1 st.2 := by
    ext θ
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => h ▸ mem_skewCell_skewIdx q θ, fun h => skewIdx_eq_of_mem q h⟩
  rw [this]
  exact measurableSet_skewCell q st.1 st.2

theorem measurable_skewOutcomeMaps (Q : MeasurementContext → JointRates 2 2) :
    MeasurableSharedContextOutcomeMaps (skewOutcomeMaps Q) := by
  intro C
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_of_countable signOfFin).comp (measurable_fst.comp (measurable_skewIdx (Q C)))
  · exact (measurable_of_countable signOfFin).comp (measurable_snd.comp (measurable_skewIdx (Q C)))

/-- ★★★ **The A-wing primitive at the I3 basins**, with the identity as reroute: A's reading does
not depend on B's setting when A's marginal does not. -/
def skewLocalSettingLocalityA (Q : MeasurementContext → JointRates 2 2)
    (hrow : ∀ a b b', (Q ⟨a, b⟩).rowSum = (Q ⟨a, b'⟩).rowSum) :
    LocalSettingLocalityA (volume : Measure LF4.KTorus) (skewOutcomeMaps Q) where
  reroute := fun _ _ _ θ => θ
  measurePreserving := fun _ _ _ => MeasurePreserving.id _
  wingA_invariant := by
    intro a b b' θ
    show signOfFin (skewIdx (Q ⟨a, b'⟩) θ).1 = signOfFin (skewIdx (Q ⟨a, b⟩) θ).1
    rw [wingA_eq_of_rowSum_eq (hrow a b b') θ]

/-- ★★★ **The B-wing primitive at the I3 basins**, with the skew rectangle exchange as reroute:
measure-preserving, and B's reading is carried along when B's marginal does not depend on A's
setting. -/
def skewLocalSettingLocalityB (Q : MeasurementContext → JointRates 2 2)
    (hcol : ∀ a a' b, (Q ⟨a, b⟩).colSum = (Q ⟨a', b⟩).colSum) :
    LocalSettingLocalityB (volume : Measure LF4.KTorus) (skewOutcomeMaps Q) where
  reroute := fun a a' b => reroute (Q ⟨a, b⟩) (Q ⟨a', b⟩)
  measurePreserving := fun a a' b => measurePreserving_reroute (Q ⟨a, b⟩) (Q ⟨a', b⟩)
  wingB_invariant := by
    intro a a' b θ
    show signOfFin (skewIdx (Q ⟨a', b⟩) (reroute (Q ⟨a, b⟩) (Q ⟨a', b⟩) θ)).2
      = signOfFin (skewIdx (Q ⟨a, b⟩) θ).2
    rw [wingB_reroute (hcol a a' b) θ]

/-- ★★★ **Operational no-signalling for the I3 record basins, derived from the primitive.** For any
family of no-signalling `2 × 2` tables, the fibre with its skew partition satisfies both
local-setting-aware primitives, hence remote marginal invariance on both wings. -/
theorem operationalNoSignalling_skew (Q : MeasurementContext → JointRates 2 2)
    (hrow : ∀ a b b', (Q ⟨a, b⟩).rowSum = (Q ⟨a, b'⟩).rowSum)
    (hcol : ∀ a a' b, (Q ⟨a, b⟩).colSum = (Q ⟨a', b⟩).colSum) :
    OperationalNoSignalling (volume : Measure LF4.KTorus) (skewOutcomeMaps Q) :=
  operationalNoSignalling_of_localSettingLocality (measurable_skewOutcomeMaps Q)
    (skewLocalSettingLocalityA Q hrow) (skewLocalSettingLocalityB Q hcol)

end CSD.RecordLayer

end

end
