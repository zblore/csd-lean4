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

## Step (2c) frame reduction (proved here): the reduced map fixes the basis

* **The projective image of an isometry equiv.** `projMap e` is the
  `Projectivization.map` of a linear isometry equivalence `e`'s underlying
  injective linear map. It preserves the transition probability
  (`transProb_projMap`, via the vector-level `transProbVec_linearIsometryEquiv`
  from `e.inner_map_map` and `e.norm_map`), hence is `TransProbPreserving`
  (`projMap_transProbPreserving`). `TransProbPreserving.comp` gives closure of
  the predicate under composition. (All general in `E`.)
* **The frame-reduced map.** `reducedMap hf b := projMap (candidateUnitary hf b).symm ∘ f`
  is `TransProbPreserving` (`reducedMap_transProbPreserving`) and **fixes every
  source basis ray** (`reducedMap_fixes_basis`):
  `reducedMap hf b (mk (b i)) = mk (b i)` for every `i`. The proof rewrites
  `f (mk (b i))` backward via `candidateUnitary_agrees_on_basis`, pushes the
  inverse candidate unitary's projective map through `projMap_mk`, and applies
  `LinearIsometryEquiv.symm_apply_apply`.

This reduces the open converse to the **Wigner normal-form problem** for the
reduced map, addressed in Stages 1–3 below.

## Stage 1 (proved here): moduli preservation

* `TransProbPreserving.transProb_of_fixed` — a preserving map fixing a point `q`
  preserves the transition probability from every point to `q`.
* `transProb_srcPoint` — the transition probability to the `i`-th basis ray is the
  normalised squared modulus of the `i`-th coordinate `b.repr ψ i`.
* `reducedMap_coord_modulus` — **Stage 1 headline**: writing
  `reducedMap hf b (mk ψ) = mk φ`, the modulus profile
  `‖b.repr φ i‖² / ‖φ‖² = ‖b.repr ψ i‖² / ‖ψ‖²` is preserved coordinate-by-coordinate.

## Stage 2 (proved here): the two-level phase normal form

* `add_basis_ne_zero`, `repr_eq_pair_of_support`, `mk_eq_two_level_of_profile` —
  support and reconstruction infrastructure.
* `reducedMap_two_level_normal_form` — **Stage 2 headline**: for distinct
  `i₀ ≠ i`, `reducedMap hf b (mk (b i₀ + b i)) = mk (b i₀ + ε • b i)` for a
  unimodular `ε`. The image ray is pinned up to the single phase `ε`.

Both stages are derived from `TransProbPreserving` alone; **no ℂ-linearity is
assumed** anywhere.

## Stage 3 (open target, not proved): the phase cocycle and the dichotomy

The converse of the realisability inclusion `transProbPreserving_unitary` is the
**Wigner / Fubini–Study rigidity theorem**:

> `theorem (informal): TransProbPreserving f → (∃ U : Matrix.unitaryGroup (Fin N) ℂ,`
> `  f = fun p => U • p) ∨ (∃ antiunitary A, f = A-ray-action)`

equivalently, the isometry group of `ℂℙⁿ` with the Fubini–Study metric is the
projective **semi**-unitary group. It is **not** stated here as an axiom or a
`sorry`. With Stages 1–2 in hand, the residual is the phase-cocycle coherence of
the Stage-2 phases `εᵢ` and the resulting unitary/antiunitary dichotomy; the
precise three-piece residual is documented in the `Stage 3 (residual)` section at
the end of this file. **Critical honesty notes (load-bearing).**

* `reducedMap_fixes_basis` does **not** make `reducedMap` the identity: the
  diagonal-phase freedom is genuine and is exactly the Stage-2 phase `ε`, pinned
  only by the Stage-3 cocycle. Do not read frame reduction as `reducedMap = id`
  nor as `f = projMap (candidateUnitary hf b)`.
* Transition-probability preservation over `ℂ` admits both the unitary and the
  antiunitary classes; the holomorphic / Kähler complex structure selects the
  unitary one. Stage 3 must *derive* ℂ-linearity from the overlap data, **not**
  assume it: a smuggled linearity hypothesis would beg the question.

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

/-! ## Step (2c) frame reduction: projective image of an isometry equiv

The projective map `projMap e` of a linear isometry equivalence `e` preserves
`transProb` (`transProb_projMap`), so it is `TransProbPreserving`
(`projMap_transProbPreserving`). Composing `f` with the projective map of the
*inverse* candidate unitary yields `reducedMap`, which is `TransProbPreserving`
and **fixes every basis ray** (`reducedMap_fixes_basis`). This reduces the open
converse step (2c) to the single Wigner normal-form lemma stated in the module
header. These declarations are general in `E` wherever they do not consume the
`EuclideanSpace`-specific `candidateUnitary`. -/

section ProjMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The projective self-map induced by a linear isometry equivalence `e`: the
`Projectivization.map` of `e`'s underlying (injective) linear map. -/
noncomputable def projMap (e : E ≃ₗᵢ[ℂ] E) : ℙ ℂ E → ℙ ℂ E :=
  Projectivization.map e.toLinearEquiv.toLinearMap e.injective

/-- `projMap e` sends `mk v` to `mk (e v)`. The nonzero side is `e v ≠ 0` from
`e.injective` (an injective linear map is zero-preserving), packaged through
`Projectivization.map_mk`. -/
lemma projMap_mk (e : E ≃ₗᵢ[ℂ] E) (v : E) (hv : v ≠ 0) :
    projMap e (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (e v) (e.toLinearEquiv.map_ne_zero_iff.mpr hv) := by
  unfold projMap
  rw [Projectivization.map_mk]
  rfl

/-- **Transition probability is invariant under a linear isometry equivalence
(vector level).** `transProbVec (e u) (e v) = transProbVec u v`: the numerator
is fixed by `e.inner_map_map`, the denominator by `e.norm_map`. -/
lemma transProbVec_linearIsometryEquiv (e : E ≃ₗᵢ[ℂ] E) (u v : E) :
    transProbVec (e u) (e v) = transProbVec u v := by
  unfold transProbVec
  rw [e.inner_map_map u v, e.norm_map u, e.norm_map v]

/-- **`projMap e` preserves `transProb` (projective level).** Reduce both points
to `mk` of their canonical reps, push `projMap` through `projMap_mk`, collapse to
`transProbVec` via `transProb_mk`, then apply
`transProbVec_linearIsometryEquiv`. -/
lemma transProb_projMap (e : E ≃ₗᵢ[ℂ] E) (p q : ℙ ℂ E) :
    transProb (projMap e p) (projMap e q) = transProb p q := by
  conv_lhs => rw [← p.mk_rep, ← q.mk_rep]
  rw [projMap_mk e p.rep p.rep_nonzero, projMap_mk e q.rep q.rep_nonzero,
      transProb_mk]
  conv_rhs => rw [← p.mk_rep, ← q.mk_rep, transProb_mk p.rep_nonzero q.rep_nonzero]
  exact transProbVec_linearIsometryEquiv e p.rep q.rep

/-- **`projMap e` is `TransProbPreserving`.** Immediate from `transProb_projMap`.
General in `E`. -/
theorem projMap_transProbPreserving (e : E ≃ₗᵢ[ℂ] E) :
    TransProbPreserving (projMap e) :=
  fun p q => transProb_projMap e p q

/-- **Composition of `TransProbPreserving` maps.** `g ∘ f` preserves `transProb`
when both `g` and `f` do. General in `E`. -/
theorem TransProbPreserving.comp {g f : ℙ ℂ E → ℙ ℂ E}
    (hg : TransProbPreserving g) (hf : TransProbPreserving f) :
    TransProbPreserving (fun p => g (f p)) :=
  fun p q => by rw [hg (f p) (f q), hf p q]

end ProjMap

/-! ## Step (2c) frame reduction: the reduced map fixes every basis ray

`reducedMap hf b := projMap (candidateUnitary hf b).symm ∘ f`. It is
`TransProbPreserving` and fixes every source basis ray, since on `srcPoint b i`
the candidate unitary's projective map reproduces `f`'s value (by
`candidateUnitary_agrees_on_basis`) and its inverse returns to the basis ray. -/

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- The **frame-reduced map**: post-compose `f` with the projective map of the
*inverse* candidate unitary. Designed so that the basis rays become fixed
points. -/
noncomputable def reducedMap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun p => projMap (candidateUnitary hf b).symm (f p)

/-- **`reducedMap` is `TransProbPreserving`.** It is the composition
`projMap (candidateUnitary hf b).symm ∘ f`; compose `hf` with
`projMap_transProbPreserving`. -/
theorem reducedMap_transProbPreserving
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    TransProbPreserving (reducedMap hf b) :=
  (projMap_transProbPreserving (candidateUnitary hf b).symm).comp hf

/-- **HEADLINE (frame reduction).** The frame-reduced map fixes every source
basis ray: `reducedMap hf b (mk (b i)) = mk (b i)`.

Proof chain. Write `U := candidateUnitary hf b`. By definition
`reducedMap hf b (srcPoint b i) = projMap U.symm (f (srcPoint b i))`. Rewrite
`f (srcPoint b i)` backward via `candidateUnitary_agrees_on_basis` to
`mk (U (b i))`; push `projMap U.symm` through `projMap_mk` to
`mk (U.symm (U (b i)))`; and `U.symm (U (b i)) = b i` by
`LinearIsometryEquiv.symm_apply_apply`. `mk` is proof-irrelevant in its nonzero
hypothesis, so the dependent nonzero proofs are immaterial.

**Critical honesty note.** Fixing the basis rays does *not* make `reducedMap`
the identity: the diagonal-phase freedom is genuine and is exactly what the
remaining normal-form lemma (step (2c)) must pin down. Do not read this as
`reducedMap = id` or `f = projMap (candidateUnitary hf b)`. -/
theorem reducedMap_fixes_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    reducedMap hf b (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := by
  set U := candidateUnitary hf b with hU
  show projMap U.symm (f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)
  rw [← candidateUnitary_agrees_on_basis hf b i, ← hU,
      projMap_mk U.symm (U (b i))
        ((candidateUnitary hf b).toLinearEquiv.map_ne_zero_iff.mpr (b.orthonormal.ne_zero i))]
  -- `U.symm (U (b i)) = b i`; `mk` is irrelevant to the nonzero-proof argument.
  congr 1
  exact U.symm_apply_apply (b i)

/-! ## Stage 1: moduli preservation

A `TransProbPreserving` map fixing a projective point `q` preserves the
transition probability from every point to `q` (`TransProbPreserving.transProb_of_fixed`).
Applied to `reducedMap hf b`, which fixes every source basis ray, this shows the
**modulus profile** of the coordinates in the basis `b` is preserved: writing
`reducedMap hf b (mk ψ) = mk φ`, the normalised squared modulus
`‖b.repr ψ i‖² / ‖ψ‖²` of each coordinate is preserved
(`reducedMap_coord_modulus`). This is the coordinate-free heart of the Wigner
normal-form argument; it does not yet pin phases. -/

/-- **Moduli-preservation kernel.** A transition-probability-preserving map
fixing a projective point `q` preserves the transition probability from every
point to `q`. General in `E`. -/
theorem TransProbPreserving.transProb_of_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {g : ℙ ℂ E → ℙ ℂ E} (hg : TransProbPreserving g)
    {q : ℙ ℂ E} (hq : g q = q) (p : ℙ ℂ E) :
    transProb (g p) q = transProb p q := by
  conv_lhs => rw [← hq]
  exact hg p q

/-- The transition probability from `mk ψ` to the `i`-th source basis ray
`srcPoint b i` is the normalised squared modulus of the `i`-th coordinate
`b.repr ψ i`. Uses `norm_inner_symm` and `OrthonormalBasis.repr_apply_apply` to
identify `‖⟪ψ, b i⟫‖ = ‖b.repr ψ i‖`, and `Orthonormal.norm_eq_one` to drop the
unit basis norm from the denominator. -/
lemma transProb_srcPoint
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    transProb (Projectivization.mk ℂ ψ hψ) (srcPoint b i)
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  rw [srcPoint_eq, transProb_mk hψ (b.orthonormal.ne_zero i)]
  unfold transProbVec
  rw [b.orthonormal.norm_eq_one i, one_pow, mul_one, norm_inner_symm,
      ← b.repr_apply_apply]

/-- **Stage 1 (moduli preservation).** Writing `reducedMap hf b (mk ψ) = mk φ`,
the normalised squared modulus of every coordinate in the basis `b` is preserved:
`‖b.repr φ i‖² / ‖φ‖² = ‖b.repr ψ i‖² / ‖ψ‖²`, where `φ` is the canonical
representative of the image ray. Combines the moduli-preservation kernel
`TransProbPreserving.transProb_of_fixed` (with `q = srcPoint b i`, fixed by
`reducedMap_fixes_basis`) and the coordinate reading `transProb_srcPoint`. -/
theorem reducedMap_coord_modulus
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (reducedMap hf b (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(reducedMap hf b (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have hfix : reducedMap hf b (srcPoint b i) = srcPoint b i := by
    rw [srcPoint_eq]; exact reducedMap_fixes_basis hf b i
  have key := (reducedMap_transProbPreserving hf b).transProb_of_fixed hfix
    (Projectivization.mk ℂ ψ hψ)
  rw [transProb_srcPoint b hψ i] at key
  set gp := reducedMap hf b (Projectivization.mk ℂ ψ hψ) with hgp
  have hgp_coord : transProb gp (srcPoint b i)
      = ‖b.repr gp.rep i‖ ^ 2 / ‖gp.rep‖ ^ 2 := by
    conv_lhs => rw [← Projectivization.mk_rep gp]
    exact transProb_srcPoint b gp.rep_nonzero i
  rw [← hgp_coord, key]

/-! ## Stage 2: the two-level phase normal form

For distinct indices `i₀ ≠ i`, the frame-reduced map sends the superposition ray
`mk (b i₀ + b i)` to a ray `mk (b i₀ + ε • b i)` with `ε` unimodular
(`reducedMap_two_level_normal_form`). Stage 1 forces the image rep to be
supported on `{i₀, i}` with equal coordinate moduli there; normalising the ray so
that the `i₀`-coordinate is `1` leaves a single unit phase `ε := d_i / d_{i₀}`.
The genuine content is the support restriction plus the modulus equality; the
phase `ε` is *not* yet pinned to `1` (that is Stage 3, the cocycle). -/

/-- The sum of two distinct basis vectors is nonzero: its squared norm is `2`
(Pythagoras via `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`, using the
orthogonality `b.orthonormal.2 hij` and the unit norms). -/
lemma add_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    (b i₀ + b i : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have h2 : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖
      * ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ = 2 := by
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
          (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀,
        b.orthonormal.norm_eq_one i]
    norm_num
  rw [h, norm_zero, mul_zero] at h2
  norm_num at h2

/-- **Support reconstruction.** A vector whose coordinates in the basis `b`
vanish outside `{i₀, i}` is the pair sum of its two surviving coordinates.
`OrthonormalBasis.sum_repr` expands `φ`, `Finset.sum_subset` drops the null
coordinates, and `Finset.sum_pair` collapses the two-element sum. -/
lemma repr_eq_pair_of_support
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (φ : EuclideanSpace ℂ (Fin N)) {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0) :
    φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i := by
  have hvanish : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      j ∉ ({i₀, i} : Finset (Fin N)) → b.repr φ j • b j = 0 := by
    intro j _ hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    push_neg at hj
    rw [hsupp j hj.1 hj.2, zero_smul]
  calc φ = ∑ j, b.repr φ j • b j := (b.sum_repr φ).symm
    _ = ∑ j ∈ ({i₀, i} : Finset (Fin N)), b.repr φ j • b j :=
          (Finset.sum_subset (Finset.subset_univ _) hvanish).symm
    _ = b.repr φ i₀ • b i₀ + b.repr φ i • b i := Finset.sum_pair hij

/-- **Profile ⇒ two-level normal form.** A nonzero vector supported on `{i₀, i}`
with equal coordinate moduli there (and nonzero `i₀`-coordinate) spans the ray
`mk (b i₀ + ε • b i)` for the unit phase `ε := (b.repr φ i) / (b.repr φ i₀)`.
Factoring `b.repr φ i₀` out of the pair reconstruction rescales the ray; the
modulus equality gives `‖ε‖ = 1`. -/
lemma mk_eq_two_level_of_profile
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {φ : EuclideanSpace ℂ (Fin N)} (hφ : φ ≠ 0) {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0)
    (ha : b.repr φ i₀ ≠ 0)
    (hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖) :
    ∃ (ε : ℂ) (hne : (b i₀ + ε • b i : EuclideanSpace ℂ (Fin N)) ≠ 0),
      ‖ε‖ = 1 ∧
      Projectivization.mk ℂ φ hφ = Projectivization.mk ℂ (b i₀ + ε • b i) hne := by
  have hrec : φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i :=
    repr_eq_pair_of_support b φ hij hsupp
  set a := b.repr φ i₀ with ha_def
  set c := b.repr φ i with hc_def
  have hfactor : a • (b i₀ + (c / a) • b i) = φ := by
    have hac : a * (c / a) = c := by field_simp
    rw [smul_add, smul_smul, hac, ← hrec]
  have hne : (b i₀ + (c / a) • b i : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hfactor
    exact hφ hfactor.symm
  refine ⟨c / a, hne, ?_, ?_⟩
  · rw [norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  · exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i₀ + (c / a) • b i) hφ hne).mpr
      ⟨a, hfactor⟩

/-- **Stage 2 (two-level phase normal form).** For distinct `i₀ ≠ i`, the
frame-reduced map sends the superposition ray `mk (b i₀ + b i)` to
`mk (b i₀ + ε • b i)` for a unimodular `ε`. Stage 1 (`reducedMap_coord_modulus`)
forces the image rep to be supported on `{i₀, i}` with equal moduli there;
`mk_eq_two_level_of_profile` packages the ray normal form. This pins the image
ray up to the single phase `ε`; pinning `ε = 1` (globally coherently) is the
Stage 3 cocycle, not proved here. -/
theorem reducedMap_two_level_normal_form
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    ∃ (ε : ℂ) (hne : (b i₀ + ε • b i : EuclideanSpace ℂ (Fin N)) ≠ 0),
      ‖ε‖ = 1 ∧
      reducedMap hf b
          (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i₀ + ε • b i) hne := by
  -- Coordinates of the source superposition `w = b i₀ + b i`.
  have hwj : ∀ j, b.repr (b i₀ + b i) j
      = (if j = i₀ then (1 : ℂ) else 0) + (if j = i then 1 else 0) := by
    intro j
    rw [b.repr_apply_apply, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal j i₀,
        orthonormal_iff_ite.mp b.orthonormal j i]
  have hwi0 : b.repr (b i₀ + b i) i₀ = 1 := by
    rw [hwj i₀, if_pos rfl, if_neg hij, add_zero]
  have hwi : b.repr (b i₀ + b i) i = 1 := by
    rw [hwj i, if_neg (Ne.symm hij), if_pos rfl, zero_add]
  have hwnorm : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
          (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀,
        b.orthonormal.norm_eq_one i]
    norm_num
  -- The image rep `φ` and the transported moduli (Stage 1).
  set φ := (reducedMap hf b
      (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))).rep
    with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hmodj : ∀ j, ‖b.repr φ j‖ ^ 2 / ‖φ‖ ^ 2
      = ‖b.repr (b i₀ + b i) j‖ ^ 2
          / ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
    intro j
    rw [hφ_def]
    exact reducedMap_coord_modulus hf b (add_basis_ne_zero b hij) j
  -- Support of `φ` is `{i₀, i}`.
  have hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0 := by
    intro j hj0 hji
    have hz : ‖b.repr φ j‖ ^ 2 / ‖φ‖ ^ 2 = 0 := by
      rw [hmodj j, hwj j, if_neg hj0, if_neg hji, add_zero, norm_zero]
      norm_num
    have hsq : ‖b.repr φ j‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact h
      · exact absurd h (ne_of_gt hφpos)
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hsq
  -- The `i₀`-coordinate of `φ` is nonzero (its modulus² is `‖φ‖²/2`).
  have ha : b.repr φ i₀ ≠ 0 := by
    intro h
    have hmj := hmodj i₀
    rw [hwi0, h, norm_zero, hwnorm, norm_one] at hmj
    norm_num at hmj
  -- The `i` and `i₀` coordinate moduli agree.
  have hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    have hi := hmodj i
    have hi0 := hmodj i₀
    rw [hwi, norm_one, hwnorm] at hi
    rw [hwi0, norm_one, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff (ne_of_gt hφpos) (ne_of_gt hφpos)] at hd
    have heq2 : ‖b.repr φ i‖ ^ 2 = ‖b.repr φ i₀‖ ^ 2 :=
      mul_right_cancel₀ (ne_of_gt hφpos) hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), heq2]
  -- Assemble via the profile normal form.
  obtain ⟨ε, hne, hεnorm, hmkeq⟩ :=
    mk_eq_two_level_of_profile b hφne hij hsupp ha hmod
  refine ⟨ε, hne, hεnorm, ?_⟩
  rw [← hmkeq]
  exact (Projectivization.mk_rep _).symm

/-! ## Stage 3 (residual): the phase cocycle and the unitary/antiunitary dichotomy

Stages 1–2 are proved above with **no linearity assumed** on `f`: only
`TransProbPreserving`. What remains to close the Wigner / Fubini–Study converse is
the **phase cocycle** step and the resulting dichotomy. This is stated here
precisely as the open target; it is **not** an axiom and **not** a `sorry`.

**State reached.** Write `g := reducedMap hf b` (`TransProbPreserving`, fixes
every basis ray). Stage 1 (`reducedMap_coord_modulus`) gives, for every
`p = mk ψ` with image rep `φ`, the modulus profile
`‖b.repr φ j‖² / ‖φ‖² = ‖b.repr ψ j‖² / ‖ψ‖²` for all `j`. Stage 2
(`reducedMap_two_level_normal_form`) gives, for each `i ≠ i₀`, a unit phase
`εᵢ` with `g (mk (b i₀ + b i)) = mk (b i₀ + εᵢ • b i)`.

**Residual crux (open).** The remaining content is the coherence of the `εᵢ`
across overlapping superpositions, in three linked pieces, none of which may
assume ℂ-linearity:

1. **Diagonal-phase reduction.** Post-compose `g` with `projMap D⁻¹` for the
   diagonal unitary `D` with `D (b i₀) = b i₀`, `D (b i) = εᵢ⁻¹ • b i` (which
   fixes every basis ray, so the frame reduction is preserved). After this, the
   reduced map fixes `mk (b i₀ + b i)` for **every** `i`.

2. **General coordinate phase.** For a general `ψ = ∑ cⱼ bⱼ`, the transition
   probabilities `transProb (g (mk ψ)) (mk (b i₀ + b i))` together with the
   Stage-1 moduli pin each image coordinate `dⱼ` to `cⱼ` up to a *single* phase
   per index, and the further overlaps with `mk (b i + b j)` force those phases
   to satisfy a 2-cocycle relation `θ(i,j) = θ(i₀,j) − θ(i₀,i)`.

3. **Trivial-cocycle dichotomy.** The cocycle is a coboundary in exactly two
   ways over `ℂ`: either `dⱼ = cⱼ` for all `j` (⇒ `g = id` on rays, the
   ℂ-linear / unitary branch) or `dⱼ = conj cⱼ` for all `j` (⇒ `g = conj` on
   rays, the antiunitary branch). Over `ℂ`, transition-probability preservation
   alone admits both; the holomorphic / Kähler complex structure selects the
   first. **ℂ-linearity is an output of this step, never an input.**

**Assembly (once the residual is closed).** Inverting the frame reduction,
`f = projMap (candidateUnitary hf b) ∘ g`; with the dichotomy this yields either
`∃ e : E ≃ₗᵢ[ℂ] E, ∀ p, f p = projMap e p` (unitary branch, then bridge to
`Matrix.unitaryGroup` via the isometry's matrix) or the antiunitary analogue
`f = projMap (candidateUnitary hf b) ∘ conjProj` for the ray-map `conjProj` of
complex conjugation in the basis `b`. The final headline

> `TransProbPreserving f → (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • p)`
> `  ∨ (∃ antiunitary A, ∀ p, f p = A-ray-action p)`

is deliberately **not** stated as a theorem here, because the dichotomy (item 3)
is not yet discharged. -/

end Projectivization
