/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SingletSkewTables
public import CsdLean4.RecordLayer.SkewBasin

/-!
# The skew reroute over the base: setting locality for `Σ = KSigma N` and the epistemic measure

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #155 (out of ~~#137~~): the base-coupled version.

~~#137~~ instantiated the local-setting-aware primitive on the fibre `T²` with the tables as data.
~~#135~~'s `JointContextField` attaches a table to every base point and reads the skew basin
`skewBasin c s t = {x | x.2 ∈ skewCell (c.rates x.1) s t}`. This file lifts the reroute: at `x`,
exchange along the tables **at `x`'s own base point**,

  `rerouteBasin c c' x = (x.1, reroute (c.rates x.1) (c'.rates x.1) x.2)`.

* **Measurability is the work**, and it is where the parameters of the affine pieces enter as
  measurable functions of the base point: `measurable_rectMap_param` (an affine rectangle map whose
  six parameters are measurable in the base point is jointly measurable), the regularity of the
  column data (`measurable_colSum`, `measurable_colFrac`, `measurable_loSum_colFrac`,
  `measurable_loSum_colSum`), the measurable `normalBasin`, and the glued maps over the base
  `normalizeB`, `denormalizeB` with ★ `measurable_normalizeB`, ★ `measurable_denormalizeB` — the
  preimage of a set splits along the finitely many skew basins, exactly as in the fibre proof.
* ★★ `measurePreserving_rerouteBasin`: for every preparation `p`, the reroute preserves
  `epistemicMeasure p = δ_p ⊗ vol`. Almost everywhere for that measure `x.1 = p`, so the reroute
  agrees a.e. with `Prod.map id (reroute (c.rates p) (c'.rates p))`, which preserves `δ_p ⊗ vol` by
  the fibre theorem.
* ★★ `wingB_rerouteBasin`, `wingA_eq_of_rowSum_eq'`: the readings transport pointwise, from the
  fibre statements at the base point `x.1`.
* The LF3 instance on `Σ`: `skewBasinOutcomeMaps Q` for a family of joint context fields
  `Q : MeasurementContext → JointContextField N 2 2`, ★★★ `skewBasinLocalSettingLocalityA/B` for
  every `p`, ★★★ `operationalNoSignalling_skewBasin` — **operational no-signalling for the I3 record
  basins on `Σ` itself, for the epistemic measure of every preparation**, and
  ★★★ `operationalNoSignalling_skewBasin_singlet` for the singlet as a constant field.

## Honest scope

* The no-signalling of the tables is a hypothesis **at every base point** (`rowSum` independent of
  `b`, `colSum` of `a`, pointwise in `p`), which is what any Born-derived joint context field
  satisfies and what the readings' marginals require.
* The measure is `epistemicMeasure p`, one preparation at a time, as everywhere in the record
  layer; the primitive is stated per measure, so this is the statement at the right level.
* `2 × 2` outcomes in the LF3 instance; the exchange is for arbitrary `m × n`.

References: `SkewReroute.lean` (`reroute`, `measurePreserving_reroute`, `wingB_reroute`,
`skewOutcomeMaps`), `SkewBasin.lean` (`JointContextField`, `skewBasin`, `measurableSet_skewBasin`,
`constJointContext`), `SingletSkewTables.lean` (`singletTables`), `ArcAffine.lean` (`rectMap`),
`LF3/SettingLocalityLocal.lean`; `specs/BACKLOG.md` #155, ~~#137~~, ~~#135~~.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

open LF3

variable {N m n : ℕ}

/-! ### Regularity of the column data over the base -/

namespace JointContextField

variable (c : JointContextField N m n)

theorem measurable_colSum (t : Fin n) : Measurable fun p => (c.rates p).colSum t :=
  Finset.measurable_sum Finset.univ fun s _ => c.measurable_rate s t

theorem measurable_colFrac (t : Fin n) (s : Fin m) :
    Measurable fun p => (c.rates p).colFrac t s :=
  (c.measurable_rate s t).div (c.measurable_colSum t)

theorem measurable_loSum_colFrac (t : Fin n) (s : Fin m) :
    Measurable fun p => loSum ((c.rates p).colFrac t) s := by
  classical
  simpa [loSum] using
    Finset.measurable_sum (Finset.univ.filter fun k : Fin m => (k : ℕ) < (s : ℕ))
      fun k _ => c.measurable_colFrac t k

theorem measurable_loSum_colSum (t : Fin n) :
    Measurable fun p => loSum (c.rates p).colSum t := by
  classical
  simpa [loSum] using
    Finset.measurable_sum (Finset.univ.filter fun k : Fin n => (k : ℕ) < (t : ℕ))
      fun k _ => c.measurable_colSum k

end JointContextField

/-! ### The normal basin -/

/-- **The normal basin** of the outcome pair: the fibre point lies in the normal cell of the table at
its own base point. -/
def normalBasin (c : JointContextField N m n) (s : Fin m) (t : Fin n) : Set (LF4.KSigma N) :=
  {x | x.2 ∈ normalCell (c.rates x.1) s t}

theorem measurableSet_normalBasin (c : JointContextField N m n) (s : Fin m) (t : Fin n) :
    MeasurableSet (normalBasin c s t) := by
  have hrep1 : Measurable fun x : LF4.KSigma N => rep x.2.1 :=
    measurable_rep.comp (measurable_fst.comp measurable_snd)
  have hrep2 : Measurable fun x : LF4.KSigma N => rep x.2.2 :=
    measurable_rep.comp (measurable_snd.comp measurable_snd)
  have hbase : Measurable fun x : LF4.KSigma N => x.1 := measurable_fst
  have hlo1 : Measurable fun x : LF4.KSigma N => loSum ((c.rates x.1).colFrac t) s :=
    (c.measurable_loSum_colFrac t s).comp hbase
  have hhi1 : Measurable fun x : LF4.KSigma N =>
      loSum ((c.rates x.1).colFrac t) s + (c.rates x.1).colFrac t s :=
    hlo1.add ((c.measurable_colFrac t s).comp hbase)
  have hlo2 : Measurable fun x : LF4.KSigma N => loSum (c.rates x.1).colSum t :=
    (c.measurable_loSum_colSum t).comp hbase
  have hhi2 : Measurable fun x : LF4.KSigma N =>
      loSum (c.rates x.1).colSum t + (c.rates x.1).colSum t :=
    hlo2.add ((c.measurable_colSum t).comp hbase)
  exact ((measurableSet_lt hlo1 hrep1).inter (measurableSet_le hrep1 hhi1)).inter
    ((measurableSet_lt hlo2 hrep2).inter (measurableSet_le hrep2 hhi2))

/-! ### Affine rectangle maps with parameters measurable in the base point -/

/-- An affine rectangle map whose six parameters are measurable functions of the base point is
jointly measurable on `Σ`. -/
theorem measurable_rectMap_param {x₀ α lam₁ y₀ β lam₂ : LF4.CPN N → ℝ} (hx₀ : Measurable x₀)
    (hα : Measurable α) (hlam₁ : Measurable lam₁) (hy₀ : Measurable y₀) (hβ : Measurable β)
    (hlam₂ : Measurable lam₂) :
    Measurable fun x : LF4.KSigma N =>
      rectMap (x₀ x.1) (α x.1) (lam₁ x.1) (y₀ x.1) (β x.1) (lam₂ x.1) x.2 := by
  have hbase : Measurable fun x : LF4.KSigma N => x.1 := measurable_fst
  have hrep1 : Measurable fun x : LF4.KSigma N => rep x.2.1 :=
    measurable_rep.comp (measurable_fst.comp measurable_snd)
  have hrep2 : Measurable fun x : LF4.KSigma N => rep x.2.2 :=
    measurable_rep.comp (measurable_snd.comp measurable_snd)
  have h1 : Measurable fun x : LF4.KSigma N =>
      ((α x.1 + lam₁ x.1 * (rep x.2.1 - x₀ x.1) : ℝ) : CircleFibre) :=
    measurable_coe_circleFibre.comp
      ((hα.comp hbase).add ((hlam₁.comp hbase).mul (hrep1.sub (hx₀.comp hbase))))
  have h2 : Measurable fun x : LF4.KSigma N =>
      ((β x.1 + lam₂ x.1 * (rep x.2.2 - y₀ x.1) : ℝ) : CircleFibre) :=
    measurable_coe_circleFibre.comp
      ((hβ.comp hbase).add ((hlam₂.comp hbase).mul (hrep2.sub (hy₀.comp hbase))))
  exact h1.prodMk h2

theorem measurable_toNormal_param (c : JointContextField N m n) (s : Fin m) (t : Fin n) :
    Measurable fun x : LF4.KSigma N => toNormal (c.rates x.1) s t x.2 :=
  measurable_rectMap_param (c.measurable_loSum_rowSum s) (c.measurable_loSum_colFrac t s)
    ((c.measurable_colFrac t s).div (c.measurable_rowSum s)) (c.measurable_loSum_condRate s t)
    (c.measurable_loSum_colSum t) ((c.measurable_colSum t).div (c.measurable_condRate s t))

theorem measurable_toSkew_param (c : JointContextField N m n) (s : Fin m) (t : Fin n) :
    Measurable fun x : LF4.KSigma N => toSkew (c.rates x.1) s t x.2 :=
  measurable_rectMap_param (c.measurable_loSum_colFrac t s) (c.measurable_loSum_rowSum s)
    ((c.measurable_rowSum s).div (c.measurable_colFrac t s)) (c.measurable_loSum_colSum t)
    (c.measurable_loSum_condRate s t) ((c.measurable_condRate s t).div (c.measurable_colSum t))

/-! ### The glued exchanges over the base -/

/-- The normalisation along the table at the point's own base point. -/
def normalizeB (c : JointContextField N m n) (x : LF4.KSigma N) : LF4.KTorus :=
  normalize (c.rates x.1) x.2

/-- The denormalisation along the table at the point's own base point. -/
def denormalizeB (c : JointContextField N m n) (x : LF4.KSigma N) : LF4.KTorus :=
  denormalize (c.rates x.1) x.2

theorem normalizeB_eq_of_mem (c : JointContextField N m n) {x : LF4.KSigma N} {s : Fin m}
    {t : Fin n} (h : x ∈ skewBasin c s t) : normalizeB c x = toNormal (c.rates x.1) s t x.2 :=
  glue_eq_of_mem (existsUnique_mem_skewCell (c.rates x.1))
    (fun st => toNormal (c.rates x.1) st.1 st.2) (i := (s, t)) h

theorem denormalizeB_eq_of_mem (c : JointContextField N m n) {x : LF4.KSigma N} {s : Fin m}
    {t : Fin n} (h : x ∈ normalBasin c s t) : denormalizeB c x = toSkew (c.rates x.1) s t x.2 :=
  glue_eq_of_mem (existsUnique_mem_normalCell (c.rates x.1))
    (fun st => toSkew (c.rates x.1) st.1 st.2) (i := (s, t)) h

/-- ★ **The normalisation over the base is measurable**: its preimages split along the skew basins. -/
theorem measurable_normalizeB (c : JointContextField N m n) : Measurable (normalizeB c) := by
  intro S hS
  have hsplit : normalizeB c ⁻¹' S
      = ⋃ st : Fin m × Fin n,
          (skewBasin c st.1 st.2 ∩ (fun x : LF4.KSigma N => toNormal (c.rates x.1) st.1 st.2 x.2) ⁻¹' S) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      refine ⟨skewIdx (c.rates x.1) x.2, mem_skewCell_skewIdx _ _, ?_⟩
      rwa [← normalizeB_eq_of_mem c (mem_skewCell_skewIdx (c.rates x.1) x.2)]
    · rintro ⟨st, hst, hx⟩
      rwa [normalizeB_eq_of_mem c hst]
  rw [hsplit]
  exact MeasurableSet.iUnion fun st =>
    (measurableSet_skewBasin c st.1 st.2).inter (measurable_toNormal_param c st.1 st.2 hS)

/-- ★ **The denormalisation over the base is measurable.** -/
theorem measurable_denormalizeB (c : JointContextField N m n) : Measurable (denormalizeB c) := by
  intro S hS
  have hsplit : denormalizeB c ⁻¹' S
      = ⋃ st : Fin m × Fin n,
          (normalBasin c st.1 st.2 ∩ (fun x : LF4.KSigma N => toSkew (c.rates x.1) st.1 st.2 x.2) ⁻¹' S) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      refine ⟨normalIdx (c.rates x.1) x.2, mem_normalCell_normalIdx _ _, ?_⟩
      rwa [← denormalizeB_eq_of_mem c (mem_normalCell_normalIdx (c.rates x.1) x.2)]
    · rintro ⟨st, hst, hx⟩
      rwa [denormalizeB_eq_of_mem c hst]
  rw [hsplit]
  exact MeasurableSet.iUnion fun st =>
    (measurableSet_normalBasin c st.1 st.2).inter (measurable_toSkew_param c st.1 st.2 hS)

/-! ### The reroute over the base -/

/-- **The reroute over the base**: at `x`, exchange along the tables at `x`'s own base point. -/
def rerouteBasin (c c' : JointContextField N m n) (x : LF4.KSigma N) : LF4.KSigma N :=
  (x.1, denormalizeB c' (x.1, normalizeB c x))

theorem rerouteBasin_eq (c c' : JointContextField N m n) (x : LF4.KSigma N) :
    rerouteBasin c c' x = (x.1, reroute (c.rates x.1) (c'.rates x.1) x.2) := rfl

theorem measurable_rerouteBasin (c c' : JointContextField N m n) :
    Measurable (rerouteBasin c c') :=
  measurable_fst.prodMk
    ((measurable_denormalizeB c').comp (measurable_fst.prodMk (measurable_normalizeB c)))

/-- Under `δ_p ⊗ vol`, almost every point lies over `p`. -/
theorem ae_fst_eq (p : LF4.CPN N) : ∀ᵐ x ∂(epistemicMeasure p), x.1 = p := by
  rw [ae_iff]
  have hset : {x : LF4.KSigma N | ¬ x.1 = p} = ({p}ᶜ : Set (LF4.CPN N)) ×ˢ (univ : Set LF4.KTorus) := by
    ext x
    simp [Set.mem_prod]
  rw [hset, epistemicMeasure, Measure.prod_prod,
    Measure.dirac_apply' _ (measurableSet_singleton p).compl]
  simp

/-- ★★ **The reroute over the base preserves the epistemic measure of every preparation.** Almost
everywhere for `δ_p ⊗ vol` the base point is `p`, so the reroute agrees a.e. with the fibre
reroute at `p` in the second factor, which preserves `δ_p ⊗ vol`. -/
theorem measurePreserving_rerouteBasin (c c' : JointContextField N m n) (p : LF4.CPN N) :
    MeasurePreserving (rerouteBasin c c') (epistemicMeasure p) (epistemicMeasure p) := by
  refine ⟨measurable_rerouteBasin c c', ?_⟩
  have hae : rerouteBasin c c'
      =ᵐ[epistemicMeasure p] Prod.map id (reroute (c.rates p) (c'.rates p)) := by
    filter_upwards [ae_fst_eq p] with x hx
    rw [rerouteBasin_eq]
    refine Prod.ext ?_ ?_
    · simp
    · show reroute (c.rates x.1) (c'.rates x.1) x.2 = reroute (c.rates p) (c'.rates p) x.2
      rw [hx]
  rw [Measure.map_congr hae]
  exact ((MeasurePreserving.id (Measure.dirac p)).prod
    (measurePreserving_reroute (c.rates p) (c'.rates p))).map_eq

/-! ### The readings transport -/

/-- The cell of a point of `Σ`, read at its own base point. -/
def skewBasinIdx (c : JointContextField N m n) (x : LF4.KSigma N) : Fin m × Fin n :=
  skewIdx (c.rates x.1) x.2

theorem skewBasinIdx_preimage_singleton (c : JointContextField N m n) (st : Fin m × Fin n) :
    skewBasinIdx c ⁻¹' {st} = skewBasin c st.1 st.2 := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, skewBasinIdx, mem_skewBasin_iff]
  exact ⟨fun h => h ▸ mem_skewCell_skewIdx _ _, fun h => skewIdx_eq_of_mem _ h⟩

theorem measurable_skewBasinIdx (c : JointContextField N m n) : Measurable (skewBasinIdx c) := by
  refine measurable_to_countable' fun st => ?_
  rw [skewBasinIdx_preimage_singleton]
  exact measurableSet_skewBasin c st.1 st.2

/-- ★★ **B's reading is carried along the reroute over the base**, when B's marginal agrees at
every base point. -/
theorem wingB_rerouteBasin {c c' : JointContextField N m n}
    (hcol : ∀ p, (c.rates p).colSum = (c'.rates p).colSum) (x : LF4.KSigma N) :
    (skewBasinIdx c' (rerouteBasin c c' x)).2 = (skewBasinIdx c x).2 :=
  wingB_reroute (hcol x.1) x.2

/-- A's reading does not depend on the field beyond A's marginal at the base point. -/
theorem wingA_eq_of_rowSum_eq' {c c' : JointContextField N m n}
    (hrow : ∀ p, (c.rates p).rowSum = (c'.rates p).rowSum) (x : LF4.KSigma N) :
    (skewBasinIdx c' x).1 = (skewBasinIdx c x).1 :=
  wingA_eq_of_rowSum_eq (hrow x.1) x.2

/-! ### The LF3 instance on `Σ` -/

/-- **The I3 outcome maps on `Σ`** of a family of joint context fields, one per context. -/
def skewBasinOutcomeMaps (Q : MeasurementContext → JointContextField N 2 2) :
    SharedContextOutcomeMaps (LF4.KSigma N) where
  F := fun C x => (signOfFin (skewBasinIdx (Q C) x).1, signOfFin (skewBasinIdx (Q C) x).2)

theorem measurable_skewBasinOutcomeMaps (Q : MeasurementContext → JointContextField N 2 2) :
    MeasurableSharedContextOutcomeMaps (skewBasinOutcomeMaps Q) := by
  intro C
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_of_countable signOfFin).comp
      (measurable_fst.comp (measurable_skewBasinIdx (Q C)))
  · exact (measurable_of_countable signOfFin).comp
      (measurable_snd.comp (measurable_skewBasinIdx (Q C)))

/-- ★★★ **The A-wing primitive on `Σ`**, identity reroute, for every preparation. -/
def skewBasinLocalSettingLocalityA (Q : MeasurementContext → JointContextField N 2 2)
    (hrow : ∀ a b b' p, ((Q ⟨a, b⟩).rates p).rowSum = ((Q ⟨a, b'⟩).rates p).rowSum)
    (p : LF4.CPN N) :
    LocalSettingLocalityA (epistemicMeasure p) (skewBasinOutcomeMaps Q) where
  reroute := fun _ _ _ x => x
  measurePreserving := fun _ _ _ => MeasurePreserving.id _
  wingA_invariant := by
    intro a b b' x
    show signOfFin (skewBasinIdx (Q ⟨a, b'⟩) x).1 = signOfFin (skewBasinIdx (Q ⟨a, b⟩) x).1
    rw [wingA_eq_of_rowSum_eq' (hrow a b b') x]

/-- ★★★ **The B-wing primitive on `Σ`**, the rectangle exchange over the base, for every
preparation. -/
def skewBasinLocalSettingLocalityB (Q : MeasurementContext → JointContextField N 2 2)
    (hcol : ∀ a a' b p, ((Q ⟨a, b⟩).rates p).colSum = ((Q ⟨a', b⟩).rates p).colSum)
    (p : LF4.CPN N) :
    LocalSettingLocalityB (epistemicMeasure p) (skewBasinOutcomeMaps Q) where
  reroute := fun a a' b => rerouteBasin (Q ⟨a, b⟩) (Q ⟨a', b⟩)
  measurePreserving := fun a a' b => measurePreserving_rerouteBasin (Q ⟨a, b⟩) (Q ⟨a', b⟩) p
  wingB_invariant := by
    intro a a' b x
    show signOfFin (skewBasinIdx (Q ⟨a', b⟩) (rerouteBasin (Q ⟨a, b⟩) (Q ⟨a', b⟩) x)).2
      = signOfFin (skewBasinIdx (Q ⟨a, b⟩) x).2
    rw [wingB_rerouteBasin (hcol a a' b) x]

/-- ★★★ **Operational no-signalling for the I3 record basins on `Σ`, for the epistemic measure of
every preparation, derived from the primitive.** -/
theorem operationalNoSignalling_skewBasin (Q : MeasurementContext → JointContextField N 2 2)
    (hrow : ∀ a b b' p, ((Q ⟨a, b⟩).rates p).rowSum = ((Q ⟨a, b'⟩).rates p).rowSum)
    (hcol : ∀ a a' b p, ((Q ⟨a, b⟩).rates p).colSum = ((Q ⟨a', b⟩).rates p).colSum)
    (p : LF4.CPN N) :
    OperationalNoSignalling (epistemicMeasure p) (skewBasinOutcomeMaps Q) :=
  operationalNoSignalling_of_localSettingLocality (measurable_skewBasinOutcomeMaps Q)
    (skewBasinLocalSettingLocalityA Q hrow p) (skewBasinLocalSettingLocalityB Q hcol p)

/-- The singlet's tables as a constant joint context field over the base. -/
def singletField (N : ℕ) (C : MeasurementContext) : JointContextField N 2 2 :=
  constJointContext (singletTables C)

/-- ★★★ **The singlet on the I3 record basins of `Σ` is operationally no-signalling, for every
preparation, by the primitive.** -/
theorem operationalNoSignalling_skewBasin_singlet (N : ℕ) (p : LF4.CPN N) :
    OperationalNoSignalling (epistemicMeasure p) (skewBasinOutcomeMaps (singletField N)) :=
  operationalNoSignalling_skewBasin (singletField N)
    (fun a b b' _ => singletTables_rowSum_eq a b b')
    (fun a a' b _ => singletTables_colSum_eq a a' b) p

end CSD.RecordLayer

end

end
