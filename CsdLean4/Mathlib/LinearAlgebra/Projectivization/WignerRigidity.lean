import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# Step (1) of the Wigner / Fubini–Study rigidity converse

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

This file builds **STEP (1)** of the Wigner / Fubini–Study rigidity converse on
top of the transition-probability foundation
(`Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean`). It
delivers:

* `TransProbPreserving f` — the predicate that a self-map `f : ℙ ℂ E → ℙ ℂ E`
  preserves the transition probability `transProb`;
* `TransProbPreserving.injective` — such a map is injective (a transition
  probability `1` forces coincidence, via `transProb_self` and
  `transProb_eq_one_iff`);
* `transProbPreserving_unitary` — the **realisability inclusion**: every unitary
  in `Matrix.unitaryGroup (Fin N) ℂ`, acting on `ℂℙ^{N-1}`, is
  `TransProbPreserving`. This is the `U(N) → TransProbPreserving` map whose
  surjectivity-up-to-phase is the deferred Wigner statement;
* `TransProbPreserving.orthogonal` / `.inner_rep_eq_zero_iff` — preservation of
  orthogonality, both as a `transProb = 0` face and an `inner = 0` face;
* `TransProbPreserving.pairwise_orthogonal` and
  `orthonormalBasis_pairwise_orthogonal` — the "orthonormal frame ↦ pairwise
  orthogonal family" content: an orthonormal basis induces a pairwise-orthogonal
  projective family, and a `TransProbPreserving` map sends it to one.

## Steps (2a) and (2b) (proved here): image frame and candidate unitary

* **(2a) The image orthonormal frame.** `imageVec` is the unit-normalised
  canonical representative of the image ray `f (mk (b i))`; `imageVec_norm`,
  `imageVec_ne_zero`, and `imageVec_orthonormal` (off-diagonals transported from
  the source frame through `TransProbPreserving.inner_rep_eq_zero_iff`) make it
  an orthonormal family, packaged as `imageOrthonormalBasis` (an orthonormal
  family of cardinality `N` in `EuclideanSpace ℂ (Fin N)`, `finrank = N`, spans).
  `mk_imageOrthonormalBasis` records that the `i`-th image ONB vector spans the
  image ray: `mk (imageOrthonormalBasis i) = f (mk (b i))`.
* **(2b) The candidate unitary.** `candidateUnitary hf b` is the
  `OrthonormalBasis.equiv` change of frame `b ↦ imageOrthonormalBasis hf b`
  along the identity reindexing of `Fin N`, a genuine `≃ₗᵢ[ℂ]`. The headline
  `candidateUnitary_agrees_on_basis` is the agreement on the basis points:
  `mk (candidateUnitary hf b (b i)) = f (mk (b i))` for every `i`.

## Open target (not proved here): the Wigner converse, steps (2c)/(2d)

The converse of the realisability inclusion `transProbPreserving_unitary` is the
**Wigner / Fubini–Study rigidity theorem**:

> `theorem (informal): TransProbPreserving f → ∃ U : Matrix.unitaryGroup (Fin N) ℂ,
>   f = fun p => U • p`

equivalently, the isometry group of `ℂℙⁿ` with the Fubini–Study metric is the
projective unitary group `PU(n+1)`. It is **not** stated here as an axiom or a
`sorry`. With (2a)/(2b) in hand (a candidate unitary agreeing with `f` on a
fixed orthonormal frame), the two **remaining steps** are:

* **(2c) Extending agreement off the basis.** The candidate unitary agrees with
  `f` on the basis rays; extending the agreement to *all* of `ℂℙ^{N-1}` requires
  fixing the relative phases of `f` on superposition states `f (mk (b i + b j))`
  and checking consistency of these phases across overlapping superpositions
  (the coherence/cocycle crux). Over ℂ this pins `f` to a map that is either
  ℂ-linear or conjugate-ℂ-linear, agreeing with `candidateUnitary` (resp. its
  conjugate) everywhere.
* **(2d) Ruling out the antiunitary branch.** Transition-probability preservation
  alone admits both the unitary and antiunitary classes. The
  holomorphic / Kähler complex structure on `ℂℙⁿ` selects the unitary
  (ℂ-linear) branch. **Critical honesty note:** steps (2c)/(2d) must *derive*
  ℂ-linearity from the overlap data plus the Kähler structure, **not** assume it
  as a hypothesis. A smuggled linearity hypothesis would beg the question — the
  whole content of the converse is that the metric/transition data, plus the
  complex structure, *force* unitarity rather than merely permitting it. In
  particular `candidateUnitary` is built from a *chosen* frame, and (2c) is what
  certifies it is `f` itself (up to the antiunitary alternative) rather than one
  of many unitaries matching `f` on that one frame.

## Provenance

Staged as upstream Mathlib material. All declarations live under
`namespace Projectivization` with no `CsdLean4`-namespace prefix; the
`CsdLean4/Mathlib/...` location is the only staging signal. Intended location:
`Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean`.

## Tags

projectivization, transition probability, Fubini-Study, Wigner theorem,
unitary group, complex projective space, isometry, orthogonality
-/

open scoped LinearAlgebra.Projectivization ComplexOrder
open Matrix

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Diagonal value of the projective transition probability -/

/-- The diagonal value of the projective transition probability is `1`: any
projective point coincides with itself. Reduces to `transProbVec_self` on the
(nonzero) canonical representative via `transProb_mk`. -/
lemma transProb_self (p : ℙ ℂ E) : transProb p p = 1 := by
  conv_lhs => rw [← p.mk_rep]
  rw [transProb_mk p.rep_nonzero p.rep_nonzero, transProbVec_self p.rep_nonzero]

/-! ## The transition-probability-preserving predicate -/

/-- A self-map of `ℙ ℂ E` is **transition-probability preserving** when it
preserves `transProb` on every pair of projective points. The
realisability direction `transProbPreserving_unitary` shows every unitary
action is such a map; the converse (every such map is induced by a unitary) is
the open Wigner target documented in the module header. -/
def TransProbPreserving (f : ℙ ℂ E → ℙ ℂ E) : Prop :=
  ∀ p q, transProb (f p) (f q) = transProb p q

/-! ## Realisability inclusion: `U(N) → TransProbPreserving` -/

variable {N : ℕ}

/-- A transition-probability-preserving self-map of `ℂℙ^{N-1}` is injective: if
`f p = f q` then `transProb p q = transProb (f p) (f q) = transProb (f p) (f p)
= 1`, so `p = q` by `transProb_eq_one_iff`. (The coincidence characterisation
`transProb_eq_one_iff` is the `EuclideanSpace ℂ (Fin N)` ingredient.) -/
theorem TransProbPreserving.injective
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f) :
    Function.Injective f := by
  intro p q hpq
  rw [← transProb_eq_one_iff, ← hf p q, hpq, transProb_self]

/-- **Realisability inclusion.** Every unitary in `Matrix.unitaryGroup (Fin N) ℂ`,
acting on `ℂℙ^{N-1}`, is transition-probability preserving. Immediate from
`transProb_smul_unitary`. This is the `U(N) → TransProbPreserving` map; the
surjectivity-up-to-phase of this map is the deferred Wigner statement. -/
theorem transProbPreserving_unitary
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    TransProbPreserving (fun p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) => U • p) :=
  fun p q => transProb_smul_unitary U p q

/-! ## Orthogonality preservation -/

/-- `mk`-level orthogonality rewriter: for nonzero representatives `v, w`, the
projective transition probability of `mk v`, `mk w` vanishes iff `v ⟂ w`.
Routes through `transProb_mk` and the fact that the (positive) denominator of
`transProbVec` is irrelevant to vanishing. -/
lemma transProb_mk_eq_zero_iff {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    transProb (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) = 0
      ↔ (inner ℂ v w : ℂ) = 0 := by
  rw [transProb_mk hv hw]
  unfold transProbVec
  have hden : ‖v‖ ^ 2 * ‖w‖ ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  simp only [hden, or_false, pow_eq_zero_iff (n := 2) (by norm_num), norm_eq_zero]

/-- **Orthogonality preservation (transProb face).** A transition-probability-
preserving map preserves orthogonality of projective points (read as
`transProb = 0`): the hypothesis rewrites the LHS to the RHS. -/
theorem TransProbPreserving.orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℙ ℂ E → ℙ ℂ E} (hf : TransProbPreserving f) (p q : ℙ ℂ E) :
    transProb (f p) (f q) = 0 ↔ transProb p q = 0 := by
  rw [hf p q]

/-- **Orthogonality preservation (inner-product face).** A transition-probability-
preserving self-map of `ℂℙ^{N-1}` preserves orthogonality of the canonical
representatives. Combines `.orthogonal` with the orthogonality characterisation
`transProb_eq_zero_iff` on both sides. -/
theorem TransProbPreserving.inner_rep_eq_zero_iff
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f) (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (inner ℂ (f p).rep (f q).rep : ℂ) = 0 ↔ (inner ℂ p.rep q.rep : ℂ) = 0 := by
  rw [← transProb_eq_zero_iff, ← transProb_eq_zero_iff, hf p q]

/-! ## Orthogonal projective families and orthonormal frames -/

/-- Orthogonality of two projective points, read off the transition
probability: `Orthogonal p q` means `transProb p q = 0` (equivalently, the
representatives are inner-product orthogonal). -/
def Orthogonal (p q : ℙ ℂ E) : Prop := transProb p q = 0

/-- **Orthogonal family preservation.** A transition-probability-preserving map
sends a pairwise-orthogonal projective family to a pairwise-orthogonal family.
Pointwise consequence of `.orthogonal`. -/
theorem TransProbPreserving.pairwise_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℙ ℂ E → ℙ ℂ E} (hf : TransProbPreserving f)
    {ι : Type*} {P : ι → ℙ ℂ E}
    (h : Pairwise (fun i j => transProb (P i) (P j) = 0)) :
    Pairwise (fun i j => transProb (f (P i)) (f (P j)) = 0) :=
  fun i j hij => (hf.orthogonal (P i) (P j)).mpr (h hij)

/-- **Orthonormal frame ↦ pairwise-orthogonal projective family.** An
orthonormal basis of `EuclideanSpace ℂ (Fin N)` induces a pairwise-orthogonal
family of projective points (distinct basis rays are orthogonal). Uses
`b.orthonormal.2` (the off-diagonal vanishing of an `Orthonormal` family) and
the `mk`-level rewriter `transProb_mk_eq_zero_iff`. Composing with
`TransProbPreserving.pairwise_orthogonal` exhibits the "orthonormal frame ↦
pairwise-orthogonal family" content at the orthogonality level. -/
theorem orthonormalBasis_pairwise_orthogonal
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Pairwise (fun i j =>
      transProb (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
        (Projectivization.mk ℂ (b j) (b.orthonormal.ne_zero j)) = 0) :=
  fun i j hij =>
    (transProb_mk_eq_zero_iff (b.orthonormal.ne_zero i) (b.orthonormal.ne_zero j)).mpr
      (b.orthonormal.2 hij)

/-! ## Step (2a): the image orthonormal frame

A `TransProbPreserving` map `f` together with a source orthonormal basis `b`
produces an orthonormal family of *image* representatives, the unit-normalised
canonical reps of the image rays `f (mk (b i))`. Pairwise orthogonality is
transported from the source frame through `inner_rep_eq_zero_iff`; the diagonal
is unit by construction. Indexed by `Fin N` in a space of `finrank = N`, the
family is an orthonormal basis. Each image ONB vector spans the image ray:
`mk (imageOrthonormalBasis i) = f (mk (b i))`. -/

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- The `i`-th source basis projective point `mk (b i)`. A definitional
abbreviation kept folded inside the helper lemmas; the public headlines
(`mk_imageOrthonormalBasis`, `candidateUnitary_agrees_on_basis`) restate it as
the explicit `mk ℂ (b i) (b.orthonormal.ne_zero i)`. -/
noncomputable def srcPoint
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)

/-- `srcPoint` unfolds to the explicit `mk` of the basis vector. -/
lemma srcPoint_eq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    srcPoint b i = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := rfl

/-- The unit-normalised canonical representative of the image ray
`f (mk (b i))`. Normalising the (nonzero) rep `(f (srcPoint b i)).rep` by the
real reciprocal of its norm (cast to `ℂ`) gives a unit vector spanning the same
ray. -/
noncomputable def imageVec
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    EuclideanSpace ℂ (Fin N) :=
  ((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ) • (f (srcPoint b i)).rep

/-- The reciprocal-norm scalar in `imageVec` is nonzero (the rep is nonzero, so
its norm is positive). -/
private lemma imageVec_scalar_ne_zero
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hne : (f (srcPoint b i)).rep ≠ 0 := (f (srcPoint b i)).rep_nonzero
  have hpos : (0 : ℝ) < ‖(f (srcPoint b i)).rep‖ := norm_pos_iff.mpr hne
  exact_mod_cast (ne_of_gt (inv_pos.mpr hpos))

/-- `imageVec` is nonzero. -/
lemma imageVec_ne_zero
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    imageVec hf b i ≠ 0 := by
  unfold imageVec
  exact smul_ne_zero (imageVec_scalar_ne_zero hf b i) (f (srcPoint b i)).rep_nonzero

/-- `imageVec` has unit norm: the reciprocal-norm scaling normalises the rep. -/
lemma imageVec_norm
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ‖imageVec hf b i‖ = 1 := by
  have hpos : (0 : ℝ) < ‖(f (srcPoint b i)).rep‖ :=
    norm_pos_iff.mpr (f (srcPoint b i)).rep_nonzero
  unfold imageVec
  rw [norm_smul, Complex.norm_real, norm_inv, Real.norm_eq_abs,
      abs_of_pos hpos, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The image family `imageVec hf b` is orthonormal. Off-diagonal: the source
basis rays are orthogonal (`orthonormalBasis_pairwise_orthogonal` +
`transProb_eq_zero_iff` on the canonical reps), `inner_rep_eq_zero_iff hf`
transports this to the *image* reps, and the scalar normalisation factors pull
out of `inner` leaving `0`. Diagonal: `imageVec_norm`. -/
lemma imageVec_orthonormal
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Orthonormal ℂ (imageVec hf b) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases eq_or_ne i j with hij | hij
  · subst hij
    simp only [if_true]
    rw [inner_self_eq_norm_sq_to_K, imageVec_norm hf b i]
    norm_num
  · simp only [if_neg hij]
    -- source rays orthogonal ⇒ source reps orthogonal ⇒ image reps orthogonal
    have hsrc : transProb (srcPoint b i) (srcPoint b j) = 0 :=
      orthonormalBasis_pairwise_orthogonal b hij
    have hsrc_inner : (inner ℂ (srcPoint b i).rep (srcPoint b j).rep : ℂ) = 0 :=
      (transProb_eq_zero_iff (srcPoint b i) (srcPoint b j)).mp hsrc
    have himg_inner : (inner ℂ (f (srcPoint b i)).rep (f (srcPoint b j)).rep : ℂ) = 0 :=
      (hf.inner_rep_eq_zero_iff (srcPoint b i) (srcPoint b j)).mpr hsrc_inner
    unfold imageVec
    rw [inner_smul_left, inner_smul_right, himg_inner, mul_zero, mul_zero]

/-- The image orthonormal family, packaged as an `OrthonormalBasis (Fin N)`:
an orthonormal family of cardinality `N` in `EuclideanSpace ℂ (Fin N)`
(`finrank = N`) spans the whole space, so `OrthonormalBasis.mk` applies. -/
noncomputable def imageOrthonormalBasis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) := by
  refine OrthonormalBasis.mk (imageVec_orthonormal hf b) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro x _
    exact (Subsingleton.elim x 0) ▸ Submodule.zero_mem _
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hcard : Fintype.card (Fin N) = Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [(imageVec_orthonormal hf b).linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- `imageOrthonormalBasis` evaluates to `imageVec` (the `OrthonormalBasis.mk`
apply lemma). -/
lemma imageOrthonormalBasis_apply
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    imageOrthonormalBasis hf b i = imageVec hf b i := by
  unfold imageOrthonormalBasis
  rw [OrthonormalBasis.coe_mk]

/-- **The image ONB vector's ray is the image ray.** `imageVec hf b i` is a
nonzero scalar multiple of `(f (srcPoint b i)).rep`, so `mk (imageVec ..)`
equals `mk ((f (srcPoint b i)).rep) = f (srcPoint b i)` by the `mk`-scaling
characterisation `mk_eq_mk_iff'` and `mk_rep`. -/
lemma mk_imageOrthonormalBasis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    Projectivization.mk ℂ (imageOrthonormalBasis hf b i)
        ((imageOrthonormalBasis_apply hf b i).symm ▸ imageVec_ne_zero hf b i)
      = f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)) := by
  show _ = f (srcPoint b i)
  -- mk (imageONB i) = mk (imageVec i) = mk ((f (srcPoint i)).rep) = f (srcPoint i).
  -- `mk` is proof-irrelevant in the nonzero hypothesis, so the dependent proof
  -- argument is immaterial; chain three `mk` equalities.
  have hrep_ne : (f (srcPoint b i)).rep ≠ 0 := (f (srcPoint b i)).rep_nonzero
  have h1 : Projectivization.mk ℂ (imageOrthonormalBasis hf b i)
        ((imageOrthonormalBasis_apply hf b i).symm ▸ imageVec_ne_zero hf b i)
      = Projectivization.mk ℂ (imageVec hf b i) (imageVec_ne_zero hf b i) := by
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_
    exact ⟨1, by rw [one_smul, imageOrthonormalBasis_apply]⟩
  have h2 : Projectivization.mk ℂ (imageVec hf b i) (imageVec_ne_zero hf b i)
      = Projectivization.mk ℂ (f (srcPoint b i)).rep hrep_ne := by
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_
    exact ⟨((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ), rfl⟩
  rw [h1, h2, Projectivization.mk_rep]

/-! ## Step (2b): the candidate unitary

The candidate unitary is the `OrthonormalBasis.equiv` change-of-frame
`b ↦ imageOrthonormalBasis hf b` along the identity reindexing. On the source
basis vectors it reproduces the image ONB vectors, hence (via
`mk_imageOrthonormalBasis`) agrees ray-by-ray with `f` on the basis points.
This is the unitary candidate for the Wigner converse; the open content is
extending the agreement off the basis (step (2c)) and ruling out the antiunitary
branch (step (2d)). -/

/-- The candidate unitary: the linear isometry equivalence carrying the source
orthonormal basis `b` to the image orthonormal basis along the identity
reindexing of `Fin N`. -/
noncomputable def candidateUnitary
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  b.equiv (imageOrthonormalBasis hf b) (Equiv.refl (Fin N))

/-- The candidate unitary sends the `i`-th source basis vector to the `i`-th
image ONB vector. From `OrthonormalBasis.equiv_apply_basis` and
`Equiv.refl_apply`. -/
lemma candidateUnitary_apply_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    candidateUnitary hf b (b i) = imageOrthonormalBasis hf b i := by
  unfold candidateUnitary
  rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]

/-- **Step (2b) headline.** The candidate unitary agrees with `f` on the basis
points: the ray spanned by `candidateUnitary hf b (b i)` is exactly the image
ray `f (mk (b i))`. Composes `candidateUnitary_apply_basis` (the image ONB
vector) with `mk_imageOrthonormalBasis` (its ray is the image ray). -/
theorem candidateUnitary_agrees_on_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    Projectivization.mk ℂ (candidateUnitary hf b (b i))
        ((candidateUnitary hf b).toLinearEquiv.map_ne_zero_iff.mpr (b.orthonormal.ne_zero i))
      = f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)) := by
  rw [← mk_imageOrthonormalBasis hf b i]
  -- both rays are `mk` of the same vector `imageOrthonormalBasis hf b i`
  -- (after rewriting `candidateUnitary hf b (b i)` to it); `mk` is irrelevant to
  -- the nonzero-proof argument.
  congr 1
  · exact candidateUnitary_apply_basis hf b i

end Projectivization
