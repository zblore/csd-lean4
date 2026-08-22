/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# A metric on projectivization: the projection embedding

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate — there is no
`MetricSpace` on `Projectivization` anywhere in Mathlib today, only the staged topology).

Over an `RCLike` field with an inner product, each projective point `p : ℙ K V` determines the
**rank-one orthogonal projection** onto its line, `rankOneProj v = (‖v‖²)⁻¹ • ⟪v, ·⟫ • v` —
scale-invariant in `v`, so it descends to `toProjCLM : ℙ K V → (V →L[K] V)`. This map is
injective and continuous off the (staged) quotient topology; since `ℙ K V` is compact
(finite dimension) and the operator space is Hausdorff, it is a closed embedding, and the
operator-norm distance pulls back to a `MetricSpace` instance on `ℙ K V` **whose topology is
definitionally the existing quotient topology** (`Topology.IsEmbedding.comapMetricSpace`,
which `replaceTopology`s). The distance is

  `dist p q = ‖toProjCLM p − toProjCLM q‖`  (`Projectivization.dist_eq`),

the gap metric between the lines — the standard operator-theoretic metrisation of the
Fubini–Study topology.

## Main declarations

* `Projectivization.rankOneProj` — the rank-one projection onto a vector's line, with
  `rankOneProj_smul` (scale invariance) and `rankOneProj_self_apply` (idempotence anchor).
* `Projectivization.toProjCLM` — the descended projection map on `ℙ K V`;
  `toProjCLM_mk`, `continuous_toProjCLM`, `injective_toProjCLM`.
* `Projectivization.isClosedEmbedding_toProjCLM` — compact-to-Hausdorff closed embedding.
* `Projectivization.instMetricSpace` — the pulled-back metric, topology-compatible by
  construction; `Projectivization.dist_eq` — the distance formula.

## Downstream (this repo)

The quantified ε-ball forms of the C2 support arc (`specs/BACKLOG.md` Q28: "every ε-ball
around a product ray", "states closer than `2ε` have overlapping ε-preparations") become
statable; the topological forms already landed. See `MATHLIB-GAPS.md` (the FS-metric row this
closes) and `specs/mathlib-gaps-plan.md` (MG-1).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*} [RCLike K] [NormedAddCommGroup V] [InnerProductSpace K V]

/-! ### The rank-one projection onto a line -/

/-- The **rank-one projection onto the line of `v`**: `x ↦ (‖v‖²)⁻¹ ⟪v, x⟫ • v`. For unit `v`
this is the orthogonal projection onto `span {v}`; the normalisation makes it scale-invariant
(`rankOneProj_smul`), which is what lets it descend to the projectivization. -/
noncomputable def rankOneProj (v : V) : V →L[K] V :=
  ((‖v‖ : K) ^ 2)⁻¹ • (innerSL K v).smulRight v

lemma rankOneProj_apply (v x : V) :
    rankOneProj (K := K) v x = (((‖v‖ : K) ^ 2)⁻¹ * inner K v x) • v := by
  simp [rankOneProj, ContinuousLinearMap.smulRight_apply, smul_smul]

omit [InnerProductSpace K V] in
/-- The square of a nonzero vector's norm, coerced, is nonzero. -/
lemma normSq_coe_ne_zero {v : V} (hv : v ≠ 0) : ((‖v‖ : K)) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))

/-- The projection fixes its own line: `rankOneProj v v = v`. -/
lemma rankOneProj_self_apply {v : V} (hv : v ≠ 0) : rankOneProj (K := K) v v = v := by
  rw [rankOneProj_apply, inner_self_eq_norm_sq_to_K,
    inv_mul_cancel₀ (normSq_coe_ne_zero hv), one_smul]

/-- **Scale invariance**: the projection depends only on the line. -/
lemma rankOneProj_smul (t : K) {v : V} (ht : t ≠ 0) (hv : v ≠ 0) :
    rankOneProj (K := K) (t • v) = rankOneProj (K := K) v := by
  ext x
  rw [rankOneProj_apply, rankOneProj_apply, inner_smul_left, smul_smul]
  have hn : ((‖t • v‖ : ℝ) : K) ^ 2 = ((‖t‖ : ℝ) : K) ^ 2 * ((‖v‖ : ℝ) : K) ^ 2 := by
    rw [norm_smul]
    push_cast
    ring
  rw [hn, ← RCLike.conj_mul t]
  have hct : (starRingEnd K) t ≠ 0 := star_ne_zero.mpr ht
  have hv2 : ((‖v‖ : ℝ) : K) ^ 2 ≠ 0 := normSq_coe_ne_zero hv
  field_simp

/-! ### The descended projection map on `ℙ K V` -/

/-- Scale invariance, in the exact shape `Projectivization.lift` consumes. -/
lemma rankOneProj_lift_aux (a b : { v : V // v ≠ 0 }) (t : K)
    (hab : (a : V) = t • (b : V)) :
    rankOneProj (K := K) (a : V) = rankOneProj (K := K) (b : V) := by
  have ht : t ≠ 0 := by
    rintro rfl
    exact a.2 (by simpa using hab)
  rw [hab]
  exact rankOneProj_smul t ht b.2

/-- **The projection embedding** of projective space into the operator space: a projective
point goes to the rank-one projection onto its line. -/
noncomputable def toProjCLM : ℙ K V → (V →L[K] V) :=
  Projectivization.lift (fun v => rankOneProj (K := K) (v : V)) rankOneProj_lift_aux

@[simp] lemma toProjCLM_mk (v : V) (hv : v ≠ 0) :
    toProjCLM (mk K v hv) = rankOneProj (K := K) v :=
  Projectivization.lift_mk _ _ _ hv

/-- The projection map is continuous off the quotient topology: the representative-level map
is continuous (the bounded-bilinear `smulRight` composed with the continuous `innerSL`, scaled
by the nonvanishing inverse norm-square), and the staged `continuous_lift` descends it. -/
lemma continuous_toProjCLM : Continuous (toProjCLM : ℙ K V → V →L[K] V) := by
  refine continuous_lift _ rankOneProj_lift_aux ?_
  have hsc : Continuous fun v : { v : V // v ≠ 0 } => (((‖(v : V)‖ : ℝ) : K) ^ 2)⁻¹ := by
    refine Continuous.inv₀ ?_ (fun v => normSq_coe_ne_zero v.2)
    exact (RCLike.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val)).pow 2
  have hb : Continuous fun p : (V →L[K] K) × V => p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL K V V).isBoundedBilinearMap.continuous
  have hsr : Continuous fun v : { v : V // v ≠ 0 } =>
      (innerSL K (v : V)).smulRight (v : V) :=
    hb.comp (((innerSL K).continuous.comp continuous_subtype_val).prodMk
      continuous_subtype_val)
  exact hsc.smul hsr

/-- **Injectivity**: distinct lines have distinct projections. Applying the equal projections
to a representative of the second line, the first projection fixes it, so the representatives
are collinear. -/
lemma injective_toProjCLM : Function.Injective (toProjCLM : ℙ K V → V →L[K] V) := by
  intro p q h
  rw [← p.mk_rep, ← q.mk_rep] at h ⊢
  rw [toProjCLM_mk, toProjCLM_mk] at h
  have happ : rankOneProj (K := K) p.rep q.rep = rankOneProj (K := K) q.rep q.rep := by
    rw [h]
  rw [rankOneProj_self_apply q.rep_nonzero, rankOneProj_apply] at happ
  exact ((mk_eq_mk_iff' K q.rep p.rep q.rep_nonzero p.rep_nonzero).mpr ⟨_, happ⟩).symm

/-! ### The metric -/

variable [FiniteDimensional K V]

/-- The projection embedding is a **closed embedding**: continuous and injective from the
compact `ℙ K V` (staged `instCompactSpace`) into the Hausdorff operator space. -/
lemma isClosedEmbedding_toProjCLM :
    Topology.IsClosedEmbedding (toProjCLM : ℙ K V → V →L[K] V) :=
  continuous_toProjCLM.isClosedEmbedding injective_toProjCLM

/-- **The metric on projectivization**: the operator-norm distance between the lines'
projections, pulled back through the closed embedding. `comapMetricSpace` installs the metric
with `replaceTopology`, so the metric topology is definitionally the staged quotient
topology — no diamond with `instTopologicalSpace`. -/
noncomputable instance instMetricSpace : MetricSpace (ℙ K V) :=
  Topology.IsEmbedding.comapMetricSpace toProjCLM
    isClosedEmbedding_toProjCLM.isEmbedding

/-- **The distance formula**: the gap between the lines, as the operator-norm distance of
their projections. -/
lemma dist_eq (p q : ℙ K V) :
    dist p q = ‖toProjCLM p - toProjCLM q‖ :=
  dist_eq_norm (toProjCLM p) (toProjCLM q)

end Projectivization
