/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Fubini–Study as a Lebesgue-absolutely-continuous pushforward

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The Fubini–Study measure was built (`FubiniStudy.lean`) as a Haar pushforward from the unitary
group, and characterised (`FubiniStudyUnique.lean`) as THE `U(N)`-invariant probability measure
on `ℂℙ^{N−1}`. This file gives it a **Lebesgue-absolutely-continuous source**: the normalized
Lebesgue measure on the punctured unit ball of `ℂᴺ` pushes forward through `Projectivization.mk`
to a `U(N)`-invariant probability measure — hence, by uniqueness, to `fubiniStudyMeasure p₀`.

The payoff is a **null-set transport principle**: any ray set whose vector cone is
Lebesgue-null is Fubini–Study-null (`fubiniStudyMeasure_null_of_cone`). Combined with the
elementary slicing lemmas proved here (the zero set of the coordinate quadratic
`v a · v b = v c · v d` is null — Fubini slicing, no polynomial theory), this is what turns
"the entangled rays have positive measure" into "**almost every** ray is entangled" downstream
(`RecordLayer/EntangledMeasure.lean`).

## Main declarations

* `pi_null_of_ae_slice_null` — the Fubini slicing vehicle on `Fin (n+1) → ℂ`.
* `pi_coord_zero_null`, `pi_quadratic_null` — coordinate hyperplanes and the coordinate
  quadratic's zero set are Lebesgue-null. (A general `polynomial_zeroSet_null` would subsume
  these; it is deliberately NOT built — nothing in flight needs it. See
  `specs/mathlib-gaps-plan.md`.)
* `volume_ofLp_preimage_null` — null sets transport from the pi space to `EuclideanSpace ℂ`
  (two additive Haar measures agree up to a positive scalar; no exact normalisation chased).
* `toEuclideanIsometry` — a unitary matrix as a `ℂ`-linear isometry equiv of `ℂᴺ` (through
  `Matrix.toEuclideanCLM`), with the `ℝ`-restriction `toEuclideanIsometryReal` feeding
  `LinearIsometryEquiv.measurePreserving`.
* `ballMeasure` — the normalized Lebesgue measure on the punctured unit ball; `projOfVec` — the
  junk-totalised `mk`.
* `map_ballMeasure_eq_fubiniStudy` — ★ the pushforward identity, by uniqueness.
* `fubiniStudyMeasure_null_of_cone` — ★★ the null-transport principle.
-/

@[expose] public section

open MeasureTheory Matrix Set Metric
open scoped LinearAlgebra.Projectivization ENNReal

namespace Matrix.UnitaryGroup

/-! ### Fubini slicing on the pi space -/

section Slicing

/-- **The slicing vehicle**: a set of `Fin (n+1) → ℂ` is Lebesgue-null as soon as, for almost
every value of the remaining coordinates, its slice in coordinate `i` is null in `ℂ`. -/
lemma pi_null_of_ae_slice_null {n : ℕ} (i : Fin (n + 1))
    {S : Set (Fin (n + 1) → ℂ)} (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => (volume : Measure ℂ)),
      (volume : Measure ℂ) {z : ℂ | Fin.insertNth (α := fun _ => ℂ) i z y ∈ S} = 0) :
    (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℂ)) S = 0 := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i with he
  have hpres := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (volume : Measure ℂ)) i
  have hT : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hS
  have h1 : (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℂ)) S
      = ((volume : Measure ℂ).prod (Measure.pi fun _ : Fin n => volume))
          (e.symm ⁻¹' S) := by
    conv_lhs => rw [show S = e ⁻¹' (e.symm ⁻¹' S) by
      rw [← Set.preimage_comp, MeasurableEquiv.symm_comp_self, Set.preimage_id]]
    exact hpres.measure_preimage hT.nullMeasurableSet
  have h2 : ((Measure.pi fun _ : Fin n => (volume : Measure ℂ)).prod (volume : Measure ℂ))
        (Prod.swap ⁻¹' (e.symm ⁻¹' S))
      = ((volume : Measure ℂ).prod (Measure.pi fun _ : Fin n => volume))
          (e.symm ⁻¹' S) := by
    conv_rhs => rw [← Measure.prod_swap]
    rw [Measure.map_apply measurable_swap hT]
  rw [h1, ← h2, Measure.measure_prod_null (measurable_swap hT)]
  filter_upwards [h] with y hy
  have hset : (Prod.mk y ⁻¹' (Prod.swap ⁻¹' (e.symm ⁻¹' S)))
      = {z : ℂ | Fin.insertNth (α := fun _ => ℂ) i z y ∈ S} := by
    ext z
    exact Iff.rfl
  rw [hset]
  exact hy

/-- Coordinate hyperplanes are Lebesgue-null. -/
lemma pi_coord_zero_null {n : ℕ} (b : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℂ)) {v | v b = 0} = 0 := by
  refine pi_null_of_ae_slice_null b
    ((measurable_pi_apply b) (measurableSet_singleton 0))
    (Filter.Eventually.of_forall fun y => ?_)
  have hset : {z : ℂ | Fin.insertNth (α := fun _ => ℂ) b z y ∈ {v | v b = 0}} = {0} := by
    ext z
    simp [Fin.insertNth_apply_same]
  rw [hset]
  exact measure_singleton 0

/-- **The coordinate quadratic's zero set is Lebesgue-null**: for indices `b, c, d` distinct
from `a`, the set `{v | v a · v b = v c · v d}` is null. Fubini slicing: for almost every
choice of the other coordinates the `b`-value is nonzero (coordinate hyperplanes are null),
and then the `a`-slice is a single point. -/
lemma pi_quadratic_null {n : ℕ} {a b c d : Fin (n + 1)}
    (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a) :
    (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℂ))
      {v | v a * v b = v c * v d} = 0 := by
  obtain ⟨jb, hjb⟩ := Fin.exists_succAbove_eq hb
  obtain ⟨jc, hjc⟩ := Fin.exists_succAbove_eq hc
  obtain ⟨jd, hjd⟩ := Fin.exists_succAbove_eq hd
  have hmeas : MeasurableSet {v : Fin (n + 1) → ℂ | v a * v b = v c * v d} :=
    measurableSet_eq_fun
      ((measurable_pi_apply a).mul (measurable_pi_apply b))
      ((measurable_pi_apply c).mul (measurable_pi_apply d))
  rcases n with _ | m
  · exact jb.elim0
  refine pi_null_of_ae_slice_null a hmeas ?_
  have hae : ∀ᵐ y ∂(Measure.pi fun _ : Fin (m + 1) => (volume : Measure ℂ)),
      y jb ≠ 0 := by
    rw [ae_iff]
    simpa using pi_coord_zero_null jb
  filter_upwards [hae] with y hy
  have hset : {z : ℂ | (Fin.insertNth (α := fun _ => ℂ) a z y) a
          * (Fin.insertNth (α := fun _ => ℂ) a z y) b
        = (Fin.insertNth (α := fun _ => ℂ) a z y) c
          * (Fin.insertNth (α := fun _ => ℂ) a z y) d}
      = {(y jc * y jd) / y jb} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ← hjb, ← hjc, ← hjd,
      Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    constructor
    · intro h
      rw [eq_div_iff hy]
      linear_combination h
    · intro h
      rw [eq_div_iff hy] at h
      linear_combination h
  rw [hset]
  exact measure_singleton _

/-- `pi_quadratic_null` at an arbitrary positive dimension (the form consumers apply, where
the dimension is a product rather than a literal successor). -/
lemma pi_quadratic_null' {M : ℕ} [NeZero M] {a b c d : Fin M}
    (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a) :
    (Measure.pi fun _ : Fin M => (volume : Measure ℂ))
      {v | v a * v b = v c * v d} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 :=
    ⟨M - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne M))).symm⟩
  exact pi_quadratic_null hb hc hd

end Slicing

/-! ### Null transport from the pi space to `EuclideanSpace ℂ` -/

section Transport

variable {N : ℕ}

/-- The identity `EuclideanSpace ℂ (Fin N) ≃L (Fin N → ℂ)`. -/
noncomputable def euclideanCLE (N : ℕ) :
    EuclideanSpace ℂ (Fin N) ≃L[ℂ] (Fin N → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ _

/-- The pushforward of the canonical volume on `EuclideanSpace ℂ (Fin N)` through the
identity to the pi space is an additive Haar measure. -/
lemma isAddHaarMeasure_map_euclideanCLE :
    ((volume : Measure (EuclideanSpace ℂ (Fin N))).map (euclideanCLE N)).IsAddHaarMeasure :=
  (euclideanCLE N).toContinuousAddEquiv.isAddHaarMeasure_map _

/-- **Null transport**: a Lebesgue-null set of the pi space pulls back to a volume-null set
of `EuclideanSpace ℂ (Fin N)`. Two additive Haar measures on the pi space are mutually
absolutely continuous, so their null sets coincide; no exact normalisation is needed. -/
lemma volume_ofLp_preimage_null {S : Set (Fin N → ℂ)} (hS : MeasurableSet S)
    (h : (Measure.pi fun _ : Fin N => (volume : Measure ℂ)) S = 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin N))) ((euclideanCLE N) ⁻¹' S) = 0 := by
  have hHaar : ((volume : Measure (EuclideanSpace ℂ (Fin N))).map
      (euclideanCLE N)).IsAddHaarMeasure := isAddHaarMeasure_map_euclideanCLE
  have hpi : (Measure.pi fun _ : Fin N => (volume : Measure ℂ))
      = (volume : Measure (Fin N → ℂ)) := (volume_pi).symm
  rw [hpi] at h
  have hac : ((volume : Measure (EuclideanSpace ℂ (Fin N))).map (euclideanCLE N))
      ≪ (volume : Measure (Fin N → ℂ)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hmap : ((volume : Measure (EuclideanSpace ℂ (Fin N))).map (euclideanCLE N)) S = 0 :=
    hac h
  rw [← Measure.map_apply (euclideanCLE N).continuous.measurable hS]
  exact hmap

end Transport

/-! ### The unitary group acts by volume-preserving isometries of `ℂᴺ` -/

section Isometry

variable {N : ℕ}

/-- The application-level bridge from `Matrix.toEuclideanCLM` to `Matrix.toEuclideanLin`
(their coincidence is `rfl` in Mathlib's own module; only the coercion layer is unfolded
here, so the unexposed internals never block it). -/
lemma toEuclideanCLM_apply_eq (A : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) A x = Matrix.toEuclideanLin A x := by
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rfl

/-- Composition of matrix actions is the action of the product — through `map_mul` of the
star-algebra equivalence, dodging the cross-module defeq wall. -/
lemma toEuclideanLin_comp_apply (A B : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x)
      = Matrix.toEuclideanLin (A * B) x := by
  rw [← toEuclideanCLM_apply_eq, ← toEuclideanCLM_apply_eq, ← toEuclideanCLM_apply_eq,
    map_mul]
  rfl

/-- The identity matrix acts as the identity. -/
lemma toEuclideanLin_one_apply (x : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) x = x := by
  rw [← toEuclideanCLM_apply_eq, map_one]
  rfl

/-- A unitary matrix as a `ℂ`-linear isometry equiv of `ℂᴺ`: the inverse is the star, and a
unitary operator preserves the inner product via the adjoint. -/
noncomputable def toEuclideanIsometry (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) := by
  refine LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinearMap
      (Matrix.toEuclideanLin U.val) (Matrix.toEuclideanLin (star U.val)) ?_ ?_) ?_
  · apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, toEuclideanLin_comp_apply,
      Matrix.mem_unitaryGroup_iff.mp U.2, toEuclideanLin_one_apply, LinearMap.id_apply]
  · apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, toEuclideanLin_comp_apply,
      Matrix.mem_unitaryGroup_iff'.mp U.2, toEuclideanLin_one_apply, LinearMap.id_apply]
  · intro x y
    have hadj : Matrix.toEuclideanLin ((U.val)ᴴ)
        = LinearMap.adjoint (Matrix.toEuclideanLin U.val) :=
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint U.val
    have hone : Matrix.toEuclideanLin ((U.val)ᴴ) ((Matrix.toEuclideanLin U.val) y) = y := by
      rw [toEuclideanLin_comp_apply, show (U.val)ᴴ * U.val = 1 by
          rw [← Matrix.star_eq_conjTranspose]
          exact Matrix.mem_unitaryGroup_iff'.mp U.2,
        toEuclideanLin_one_apply]
    calc inner ℂ ((Matrix.toEuclideanLin U.val) x) ((Matrix.toEuclideanLin U.val) y)
        = inner ℂ x (LinearMap.adjoint (Matrix.toEuclideanLin U.val)
            ((Matrix.toEuclideanLin U.val) y)) := by
          rw [LinearMap.adjoint_inner_right]
      _ = inner ℂ x (Matrix.toEuclideanLin ((U.val)ᴴ)
            ((Matrix.toEuclideanLin U.val) y)) := by rw [hadj]
      _ = inner ℂ x y := by rw [hone]

@[simp] lemma toEuclideanIsometry_apply (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    toEuclideanIsometry U v = Matrix.toEuclideanLin U.val v := rfl

/-- The `ℝ`-restriction of the unitary isometry (feeding
`LinearIsometryEquiv.measurePreserving`). -/
noncomputable def toEuclideanIsometryReal (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) :=
  ⟨(toEuclideanIsometry U).toLinearEquiv.restrictScalars ℝ,
    (toEuclideanIsometry U).norm_map⟩

/-- The unitary action on `ℂᴺ` preserves the canonical volume. -/
lemma measurePreserving_toEuclideanLin (U : Matrix.unitaryGroup (Fin N) ℂ) :
    MeasurePreserving (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v)
      volume volume :=
  (toEuclideanIsometryReal U).measurePreserving

/-- The unitary action preserves the punctured unit ball. -/
lemma toEuclideanLin_preimage_ball (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v) ⁻¹'
        (ball (0 : EuclideanSpace ℂ (Fin N)) 1 \ {0})
      = ball (0 : EuclideanSpace ℂ (Fin N)) 1 \ {0} := by
  ext v
  simp only [Set.mem_preimage, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc ‖v‖ = ‖toEuclideanIsometry U v‖ := ((toEuclideanIsometry U).norm_map v).symm
        _ < 1 := h1
    · intro hv0
      exact h2 (by rw [hv0]; exact (Matrix.toEuclideanLin U.val).map_zero)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc ‖Matrix.toEuclideanLin U.val v‖ = ‖v‖ := (toEuclideanIsometry U).norm_map v
        _ < 1 := h1
    · intro h0
      exact h2 ((toEuclideanIsometry U).map_eq_zero_iff.mp h0)

end Isometry

/-! ### The normalized ball measure and its projective pushforward -/

section BallMeasure

variable {N : ℕ} [NeZero N]

/-- The punctured unit ball of `ℂᴺ`. -/
def puncturedBall (N : ℕ) : Set (EuclideanSpace ℂ (Fin N)) :=
  ball (0 : EuclideanSpace ℂ (Fin N)) 1 \ {0}

omit [NeZero N] in
lemma measurableSet_puncturedBall :
    MeasurableSet (puncturedBall N) :=
  measurableSet_ball.diff (measurableSet_singleton 0)

/-- The origin is volume-null (positive complex dimension) — routed through the pi space and
the coordinate-hyperplane lemma, needing no atom-class instance on `EuclideanSpace`. -/
lemma volume_singleton_zero :
    (volume : Measure (EuclideanSpace ℂ (Fin N))) {0} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 :=
    ⟨N - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))).symm⟩
  have hsub : ({0} : Set (Fin (n + 1) → ℂ)) ⊆ {v | v 0 = 0} := by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    simp [hv]
  have hpin : (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℂ))
      ({0} : Set (Fin (n + 1) → ℂ)) = 0 :=
    measure_mono_null hsub (pi_coord_zero_null 0)
  have htrans := volume_ofLp_preimage_null (N := n + 1)
    (S := ({0} : Set (Fin (n + 1) → ℂ))) (measurableSet_singleton 0) hpin
  rwa [show (euclideanCLE (n + 1)) ⁻¹' ({0} : Set (Fin (n + 1) → ℂ)) = {0} from by
    ext v
    simp [Set.mem_preimage, map_eq_zero_iff (euclideanCLE (n + 1))
      (euclideanCLE (n + 1)).injective]] at htrans

lemma volume_puncturedBall_pos : 0 < (volume : Measure (EuclideanSpace ℂ (Fin N)))
    (puncturedBall N) := by
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin N))) {0} = 0 :=
    volume_singleton_zero
  have hpos := measure_ball_pos (volume : Measure (EuclideanSpace ℂ (Fin N)))
    (0 : EuclideanSpace ℂ (Fin N)) (one_pos)
  calc (0 : ℝ≥0∞) < volume (ball (0 : EuclideanSpace ℂ (Fin N)) 1) := hpos
    _ = volume (puncturedBall N) := by
        rw [puncturedBall, measure_sdiff_null h0]

omit [NeZero N] in
lemma volume_puncturedBall_lt_top : (volume : Measure (EuclideanSpace ℂ (Fin N)))
    (puncturedBall N) < ⊤ :=
  lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top

/-- The normalized Lebesgue measure on the punctured unit ball of `ℂᴺ`: an absolutely
continuous, `U(N)`-invariant probability measure on the nonzero vectors. -/
noncomputable def ballMeasure (N : ℕ) : Measure (EuclideanSpace ℂ (Fin N)) :=
  ((volume : Measure (EuclideanSpace ℂ (Fin N))) (puncturedBall N))⁻¹
    • (volume : Measure (EuclideanSpace ℂ (Fin N))).restrict (puncturedBall N)

instance : IsProbabilityMeasure (ballMeasure N) := by
  constructor
  rw [ballMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel volume_puncturedBall_pos.ne'
    volume_puncturedBall_lt_top.ne

omit [NeZero N] in
lemma ballMeasure_absolutelyContinuous :
    ballMeasure N ≪ (volume : Measure (EuclideanSpace ℂ (Fin N))) := by
  intro s hs
  rw [ballMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply₀' measurableSet_puncturedBall.nullMeasurableSet]
  exact mul_eq_zero.mpr (Or.inr (measure_mono_null Set.inter_subset_left hs))

omit [NeZero N] in
/-- The unitary action preserves the ball measure. -/
lemma map_toEuclideanLin_ballMeasure (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v)
      (ballMeasure N) = ballMeasure N := by
  rw [ballMeasure, Measure.map_smul]
  congr 1
  calc Measure.map (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v)
        ((volume : Measure (EuclideanSpace ℂ (Fin N))).restrict (puncturedBall N))
      = Measure.map (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v)
          ((volume : Measure (EuclideanSpace ℂ (Fin N))).restrict
            ((fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v) ⁻¹'
              (puncturedBall N))) := by
        rw [show (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v) ⁻¹'
            (puncturedBall N) = puncturedBall N from toEuclideanLin_preimage_ball U]
    _ = (Measure.map (fun v : EuclideanSpace ℂ (Fin N) => Matrix.toEuclideanLin U.val v)
          (volume : Measure (EuclideanSpace ℂ (Fin N)))).restrict (puncturedBall N) :=
        (Measure.restrict_map (measurePreserving_toEuclideanLin U).measurable
          measurableSet_puncturedBall).symm
    _ = (volume : Measure (EuclideanSpace ℂ (Fin N))).restrict (puncturedBall N) := by
        rw [(measurePreserving_toEuclideanLin U).map_eq]

open scoped Classical in
/-- The junk-totalised projectivization map: `mk` off zero, an arbitrary fixed ray at zero. -/
noncomputable def projOfVec (N : ℕ) [NeZero N] :
    EuclideanSpace ℂ (Fin N) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) := fun v =>
  if h : v = 0 then
    Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin N) (1 : ℂ)) (by
      intro hz
      have := congrFun (congrArg (fun w : EuclideanSpace ℂ (Fin N) =>
        (w : Fin N → ℂ)) hz) 0
      simp at this)
  else Projectivization.mk ℂ v h

lemma projOfVec_of_ne_zero {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    projOfVec N v = Projectivization.mk ℂ v hv := by
  rw [projOfVec, dif_neg hv]

lemma measurable_projOfVec : Measurable (projOfVec N) := by
  classical
  have hmk : Measurable fun v : {w : EuclideanSpace ℂ (Fin N) // w ≠ 0} =>
      Projectivization.mk' ℂ v :=
    (Projectivization.continuous_mk' (K := ℂ)).measurable
  refine measurable_of_restrict_of_restrict_compl
    (measurableSet_singleton (0 : EuclideanSpace ℂ (Fin N))) ?_ ?_
  · -- on `{0}` the map is the constant junk value
    show Measurable fun x : ({(0 : EuclideanSpace ℂ (Fin N))} : Set _) =>
      projOfVec N x.val
    have hrestr : (fun x : ({(0 : EuclideanSpace ℂ (Fin N))} : Set _) => projOfVec N x.val)
        = fun _ => projOfVec N 0 := by
      funext x
      have hx : x.val = (0 : EuclideanSpace ℂ (Fin N)) := x.2
      rw [hx]
    rw [hrestr]
    exact measurable_const
  · -- off `{0}` the map is `mk'` through the nonzero subtype
    show Measurable fun x : (({(0 : EuclideanSpace ℂ (Fin N))} : Set _)ᶜ : Set _) =>
      projOfVec N x.val
    have hrestr :
        (fun x : (({(0 : EuclideanSpace ℂ (Fin N))} : Set _)ᶜ : Set _) => projOfVec N x.val)
        = fun x => Projectivization.mk' ℂ
            (⟨x.val, x.2⟩ : {w : EuclideanSpace ℂ (Fin N) // w ≠ 0}) := by
      funext x
      have hx : x.val ≠ (0 : EuclideanSpace ℂ (Fin N)) := x.2
      rw [projOfVec_of_ne_zero hx]
      rfl
    rw [hrestr]
    exact hmk.comp (measurable_subtype_coe.subtype_mk)

end BallMeasure

/-! ### ★ The pushforward identity and ★★ the null-transport principle -/

section Pushforward

variable {N : ℕ} [NeZero N]

/-- ★ **The Fubini–Study measure is the projectivization of normalized Lebesgue measure on
the punctured unit ball** — by invariance and the uniqueness theorem. This gives Fubini–Study
an absolutely-continuous source. -/
theorem map_ballMeasure_eq_fubiniStudy (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Measure.map (projOfVec N) (ballMeasure N) = fubiniStudyMeasure p₀ := by
  have hprob : IsProbabilityMeasure (Measure.map (projOfVec N) (ballMeasure N)) :=
    Measure.isProbabilityMeasure_map measurable_projOfVec.aemeasurable
  refine fubiniStudyMeasure_unique p₀ _ ?_
  intro U
  have hsmul_meas : Measurable (fun p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) => U • p) :=
    (continuous_smul.comp (Continuous.prodMk continuous_const continuous_id)).measurable
  rw [Measure.map_map hsmul_meas measurable_projOfVec]
  have hne : {v : EuclideanSpace ℂ (Fin N) | v ≠ 0}ᶜ = {0} := by
    ext v
    simp
  have hzero : ballMeasure N ({v : EuclideanSpace ℂ (Fin N) | v ≠ 0}ᶜ) = 0 := by
    rw [hne]
    exact ballMeasure_absolutelyContinuous volume_singleton_zero
  have hae : ((fun p => U • p) ∘ projOfVec N)
      =ᵐ[ballMeasure N]
      ((projOfVec N) ∘ (fun v => Matrix.toEuclideanLin U.val v)) := by
    filter_upwards [MeasureTheory.mem_ae_iff.mpr hzero] with v hv
    have hv0 : v ≠ 0 := hv
    have hUv0 : Matrix.toEuclideanLin U.val v ≠ 0 := by
      intro h0
      exact hv0 ((toEuclideanIsometry U).map_eq_zero_iff.mp h0)
    simp only [Function.comp_apply, projOfVec_of_ne_zero hv0,
      projOfVec_of_ne_zero hUv0]
    exact smul_mk_eq_mk U v hv0
  rw [Measure.map_congr hae, ← Measure.map_map measurable_projOfVec
    (measurePreserving_toEuclideanLin U).measurable,
    map_toEuclideanLin_ballMeasure U]

/-- ★★ **The null-transport principle**: a ray set whose vector cone is Lebesgue-null is
Fubini–Study-null. The cone is taken over the nonzero vectors. -/
theorem fubiniStudyMeasure_null_of_cone (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N)))
    {S : Set (ℙ ℂ (EuclideanSpace ℂ (Fin N)))} (hS : MeasurableSet S)
    (hcone : (volume : Measure (EuclideanSpace ℂ (Fin N)))
      {v : EuclideanSpace ℂ (Fin N) | ∃ h : v ≠ 0, Projectivization.mk ℂ v h ∈ S} = 0) :
    fubiniStudyMeasure p₀ S = 0 := by
  rw [← map_ballMeasure_eq_fubiniStudy p₀,
    Measure.map_apply measurable_projOfVec hS]
  have hsub : (projOfVec N) ⁻¹' S
      ⊆ {v : EuclideanSpace ℂ (Fin N) | ∃ h : v ≠ 0, Projectivization.mk ℂ v h ∈ S}
        ∪ {0} := by
    intro v hv
    by_cases h0 : v = 0
    · exact Or.inr h0
    · exact Or.inl ⟨h0, by rwa [← projOfVec_of_ne_zero h0]⟩
  refine measure_mono_null hsub
    (measure_union_null (ballMeasure_absolutelyContinuous hcone)
      (ballMeasure_absolutelyContinuous volume_singleton_zero))

end Pushforward

end Matrix.UnitaryGroup
