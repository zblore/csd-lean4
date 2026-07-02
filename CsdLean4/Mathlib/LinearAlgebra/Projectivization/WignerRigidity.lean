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

## The antiunitary witness (proved here): `conjProj`

`conjProj` is coordinatewise complex conjugation as a ray map
(`conjVec` on representatives), a **concrete** `TransProbPreserving` inhabitant
(`conjProj_transProbPreserving`) of the **antiunitary** class: `conjVec` is
conjugate-linear (`conjVec_smul : conjVec (c • ψ) = conj c • conjVec ψ`), not the
underlying map of any `≃ₗᵢ[ℂ]`. This makes the eventual dichotomy non-vacuous on
the antiunitary side. Built on the conjugation inner/norm identities
`conjVec_inner : ⟪conjVec u, conjVec v⟫ = conj ⟪u, v⟫` and
`conjVec_norm : ‖conjVec ψ‖ = ‖ψ‖`.

## Stage 3 piece 1 (proved here): the diagonal-phase reduction

`diagUnitary b ε hε` is the diagonal-in-`b` isometry with unit-modulus phases
`ε` (via the `ε`-scaled orthonormal basis, `scaledBasis`); `twoLevelPhase`
extracts the Stage-2 phases anchored at `ε i₀ := 1`; and
`diagReducedMap hf b i₀ := projMap D⁻¹ ∘ reducedMap hf b` (with `D` built from
those phases) is `TransProbPreserving` (`diagReducedMap_transProbPreserving`),
fixes every basis ray (`diagReducedMap_fixes_basis`), **and** fixes the two-level
rays `mk (b i₀ + b i)` for every `i ≠ i₀` (`diagReducedMap_fixes_two_level`).
This is the setup the cocycle step (pieces 2–3) consumes. `D` is constructed
*from* the extracted phases, not posited of `f`: **no ℂ-linearity is assumed.**

## Stage 3 piece 2 (proved here): the cocycle coboundary structure

On the diagonally reduced map `g := diagReducedMap hf b i₀` the coordinate
overlap algebra pins the pairwise relative phases up to sign:

* `diagReducedMap_coord_modulus` — Stage-1 moduli transported to `g`.
* `diagReducedMap_two_level_relphase` — the anchored real-part relation
  `Re(d̄_{i₀} d_i)/‖φ‖² = Re(c̄_{i₀} c_i)/‖ψ‖²`.
* `diagReducedMap_fixes_three_level` (**W4**) — the equal triple ray
  `mk (b i₀ + b i + b j)` is fixed, via moduli + saturation
  (`norm_eq_re_imp_eq`, `eq_of_re_conj_mul_eq`) + `repr_eq_triple_of_support`.
* `diagReducedMap_fixes_two_level_general` (**W4**) — the non-anchored ray
  `mk (b i + b j)` (`i, j ≠ i₀`) is fixed, using the triple as a probe.
* `diagReducedMap_pairwise_relphase` (**W4**) — the unconditional pairwise
  real-part relation for all `i, j ≠ i₀`, the full **coboundary structure**.

Every probe is real-coordinate, so the fixings are consistent with **both** the
unitary and antiunitary branches: piece 2 establishes the coboundary structure,
**not** the global sign (that is piece 3). **No ℂ-linearity is assumed.**

## Stage 3 (open target, not proved): the phase cocycle and the dichotomy

The converse of the realisability inclusion `transProbPreserving_unitary` is the
**Wigner / Fubini–Study rigidity theorem**:

> `theorem (informal): TransProbPreserving f → (∃ U : Matrix.unitaryGroup (Fin N) ℂ,`
> `  f = fun p => U • p) ∨ (∃ antiunitary A, f = A-ray-action)`

equivalently, the isometry group of `ℂℙⁿ` with the Fubini–Study metric is the
projective **semi**-unitary group. It is **not** stated here as an axiom or a
`sorry`. With Stages 1–2 and Stage 3 pieces 1–2 in hand (piece 2 CLOSED via the
W4 triple-support probe: `diagReducedMap_fixes_three_level`,
`diagReducedMap_fixes_two_level_general`, `diagReducedMap_pairwise_relphase`), the
residual is piece 3: the unitary/antiunitary dichotomy from the now-established
phase-cocycle coboundary structure, plus the Kähler selection; the precise
residual is documented in the `Stage 3 (residual)` section at the end of this
file. **Scope of "piece 2 CLOSED" (load-bearing):** piece 2 delivers the
*sign-free real-part relations* — the full pairwise data `Re(conj dᵢ·dⱼ)/‖φ‖² =
Re(conj cᵢ·cⱼ)/‖ψ‖²` (equivalently the pairwise cosines `cos(βⱼ−βᵢ)=cos(αⱼ−αᵢ)`)
for every pair, which pin the phase configuration up to global rotation AND a
single global reflection. The phrases "2-cocycle"/"coboundary structure" are
narrative labels: no formal `Complex.arg`-based additive identity
`θ(i,j)=θ(i₀,j)−θ(i₀,i)` or `H²` object is constructed, because extracting one
presupposes choosing an `arg` branch — i.e. resolving the ± reflection — which is
precisely piece 3. **Critical honesty notes (load-bearing).**

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

/-! ## The antiunitary witness `conjProj`

Over `ℂ`, transition-probability preservation admits a second class beyond the
unitary one: the **antiunitary** class, realised by complex conjugation. This
subsection builds it concretely. `conjVec` is coordinatewise complex conjugation
on `EuclideanSpace ℂ (Fin N)`, a **conjugate-linear** isometry
(`conjVec_smul` shows the semilinear scaling law `conjVec (c • ψ) = conj c • conjVec ψ`,
which is *not* the linear law of any `≃ₗᵢ[ℂ]`). Its ray map `conjProj` is
`TransProbPreserving` (`conjProj_transProbPreserving`), so the eventual
Wigner dichotomy is not vacuous on the antiunitary side. -/

/-- Coordinatewise complex conjugation on `EuclideanSpace ℂ (Fin N)`: the
conjugate-linear isometry `ψ ↦ (fun i => conj (ψ i))`. -/
noncomputable def conjVec (ψ : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i => (starRingEnd ℂ) (ψ.ofLp i))

/-- `conjVec` acts coordinatewise: `(conjVec ψ) i = conj (ψ i)` (definitional). -/
lemma conjVec_ofLp (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (conjVec ψ).ofLp i = (starRingEnd ℂ) (ψ.ofLp i) := rfl

/-- **Conjugation inner identity.** `⟪conjVec u, conjVec v⟫ = conj ⟪u, v⟫`.
Reduces via `PiLp.inner_apply` to the coordinatewise identity
`conj(conj (u i)) * conj (v i) = conj (conj (u i) * v i)` (`RCLike.inner_apply'`,
`map_mul`, `Complex.conj_conj`). -/
lemma conjVec_inner (u v : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ (conjVec u) (conjVec v) : ℂ) = (starRingEnd ℂ) (inner ℂ u v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply', RCLike.inner_apply', map_mul, conjVec_ofLp, conjVec_ofLp,
      Complex.conj_conj]

/-- **Conjugation norm identity.** `‖conjVec ψ‖ = ‖ψ‖`. Both squared norms are
the real part of the (conjugation-swapped) self inner product `conjVec_inner`;
`RCLike.conj_re` drops the conjugation on the real part. -/
lemma conjVec_norm (ψ : EuclideanSpace ℂ (Fin N)) : ‖conjVec ψ‖ = ‖ψ‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (conjVec ψ)), ← Real.sqrt_sq (norm_nonneg ψ)]
  congr 1
  rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
  have h2 : RCLike.re (inner ℂ (conjVec ψ) (conjVec ψ) : ℂ)
      = RCLike.re ((starRingEnd ℂ) (inner ℂ ψ ψ)) := by rw [conjVec_inner]
  rwa [RCLike.conj_re] at h2

/-- **Semilinearity of `conjVec`.** `conjVec (c • ψ) = conj c • conjVec ψ`. This
conjugate-linear scaling law witnesses that `conjVec` is genuinely antiunitary:
it is not the linear scaling law satisfied by any `≃ₗᵢ[ℂ]`, so `conjProj` is not
`projMap` of a complex-linear isometry equivalence. -/
lemma conjVec_smul (c : ℂ) (ψ : EuclideanSpace ℂ (Fin N)) :
    conjVec (c • ψ) = (starRingEnd ℂ) c • conjVec ψ := by
  ext i
  show (starRingEnd ℂ) ((c • ψ).ofLp i) = ((starRingEnd ℂ) c • conjVec ψ).ofLp i
  simp [conjVec_ofLp, map_mul]

/-- `conjVec` preserves nonvanishing: `‖conjVec ψ‖ = ‖ψ‖ ≠ 0`. -/
lemma conjVec_ne_zero {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) : conjVec ψ ≠ 0 := by
  rw [← norm_ne_zero_iff, conjVec_norm]; exact norm_ne_zero_iff.mpr hψ

/-- **Conjugation preserves the vector transition probability.**
`transProbVec (conjVec u) (conjVec v) = transProbVec u v`: the numerator is
fixed since `‖conj ⟪u,v⟫‖ = ‖⟪u,v⟫‖` (`conjVec_inner` + `RCLike.norm_conj`), the
denominator by `conjVec_norm`. -/
lemma conjVec_transProbVec (u v : EuclideanSpace ℂ (Fin N)) :
    transProbVec (conjVec u) (conjVec v) = transProbVec u v := by
  unfold transProbVec
  rw [conjVec_inner, RCLike.norm_conj, conjVec_norm, conjVec_norm]

/-- The **antiunitary ray map**: complex conjugation of the canonical
representative. Total and well-defined (conjugation is norm-preserving and
injective, so the image ray does not depend on representative choice up to the
scaling `conjVec_smul` absorbs). -/
noncomputable def conjProj (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ (conjVec p.rep) (conjVec_ne_zero p.rep_nonzero)

/-- **HEADLINE (antiunitary witness).** `conjProj` is `TransProbPreserving`.
Reduce both image rays to `mk (conjVec ·.rep)` via `transProb_mk`, then apply
`conjVec_transProbVec`. This exhibits a concrete `TransProbPreserving` inhabitant
of the **antiunitary** class: `conjVec` is conjugate-linear (`conjVec_smul`), not
the underlying map of any `≃ₗᵢ[ℂ]`, so `conjProj` is not `projMap` of a unitary.
The eventual Wigner dichotomy is thus non-vacuous on the antiunitary side. -/
theorem conjProj_transProbPreserving :
    TransProbPreserving (conjProj (N := N)) := by
  intro p q
  show transProb (Projectivization.mk ℂ (conjVec p.rep) _)
      (Projectivization.mk ℂ (conjVec q.rep) _) = transProb p q
  rw [transProb_mk (conjVec_ne_zero p.rep_nonzero) (conjVec_ne_zero q.rep_nonzero),
      conjVec_transProbVec]
  rfl

/-- **Ray-map identity for `conjProj` on arbitrary representatives.**
`conjProj (mk v hv) = mk (conjVec v)`. The canonical representative of `mk v hv`
is `a • v` for some nonzero `a`; `conjVec (a • v) = conj a • conjVec v`
(`conjVec_smul`), a nonzero rescaling, so both sides span the same ray. This is
the representative-independent form of `conjProj`, needed for the eventual
antiunitary assembly (Stage 3). -/
lemma conjProj_mk {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    conjProj (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (conjVec v) (conjVec_ne_zero hv) := by
  unfold conjProj
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ (Projectivization.mk ℂ v hv).rep v
    (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(starRingEnd ℂ) a, ?_⟩
  rw [← ha, conjVec_smul]

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

/-! ## Stage 3 piece 1: the diagonal-phase reduction

The first piece of the Stage 3 residual, on the critical path to the dichotomy.
It removes the Stage-2 two-level phases by post-composing the frame-reduced map
`g = reducedMap hf b` with a diagonal isometry `D⁻¹` in the basis `b`.

* **The diagonal isometry.** For a unit-modulus phase family `ε : Fin N → ℂ`
  (`∀ i, ‖ε i‖ = 1`), the scaled family `fun i => ε i • b i` is again an
  orthonormal basis (`scaledBasis`); `diagUnitary b ε hε` is the `≃ₗᵢ[ℂ]`
  carrying `b` to it, so `diagUnitary (b i) = ε i • b i`
  (`diagUnitary_apply_basis`) and `(diagUnitary).symm (b i) = (ε i)⁻¹ • b i`
  (`diagUnitary_symm_apply_basis`). This is diagonal *in the basis `b`*, not in
  the standard basis, so it is built as an `OrthonormalBasis.equiv`, not a
  `Matrix.diagonal`.
* **The extracted phases.** `twoLevelPhase hf b i₀` reads off, per index, the
  Stage-2 phase `εᵢ` from `reducedMap_two_level_normal_form` (anchored at
  `ε i₀ := 1`), with `‖twoLevelPhase hf b i₀ j‖ = 1` for every `j`
  (`twoLevelPhase_norm`).
* **The diagonally-reduced map.** `diagReducedMap hf b i₀ := projMap (D).symm ∘
  reducedMap hf b` with `D := diagUnitary b (twoLevelPhase hf b i₀) …`. It is
  `TransProbPreserving` (`diagReducedMap_transProbPreserving`), still fixes every
  basis ray (`diagReducedMap_fixes_basis`), and additionally **fixes the
  two-level rays** `mk (b i₀ + b i)` for every `i ≠ i₀`
  (`diagReducedMap_fixes_two_level`) — the setup the cocycle step (pieces 2–3)
  consumes. **No ℂ-linearity is assumed:** `D` is constructed *from* the
  extracted phases, not posited of `f`. -/

/-- The scaled family `fun i => ε i • b i` is orthonormal when every phase is
unit modulus (`‖ε i‖ = 1`): the off-diagonals inherit `b`'s orthogonality, and
the diagonal is `conj (ε i) * ε i = ‖ε i‖² = 1` (`RCLike.conj_mul`). -/
lemma scaled_orthonormal
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    Orthonormal ℂ (fun i => ε i • b i) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [if_true, mul_one]
    rw [RCLike.conj_mul, hε i]; norm_num
  · simp [h]

/-- The `ε`-scaled family spans: cardinality `N` linearly independent vectors in
`finrank = N`. Kept a separate `Prop` lemma so `scaledBasis` is a term-mode `def`
(a tactic-mode data `def` would over-include ambient section variables). -/
lemma scaled_span
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i => ε i • b i)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro x _
    exact (Subsingleton.elim x 0) ▸ Submodule.zero_mem _
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hcard : Fintype.card (Fin N) = Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [(scaled_orthonormal b ε hε).linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- The `ε`-scaled orthonormal basis (an orthonormal family of cardinality `N`
in `finrank = N`, so `OrthonormalBasis.mk` applies). -/
noncomputable def scaledBasis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  OrthonormalBasis.mk (scaled_orthonormal b ε hε) (scaled_span b ε hε)

/-- `scaledBasis` evaluates to the scaled basis vector (`OrthonormalBasis.mk`
apply). -/
lemma scaledBasis_apply
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    scaledBasis b ε hε i = ε i • b i := by
  unfold scaledBasis; rw [OrthonormalBasis.coe_mk]

/-- The **diagonal isometry in the basis `b`**: the `≃ₗᵢ[ℂ]` carrying `b` to the
`ε`-scaled basis along the identity reindexing. Diagonal in `b`
(`diagUnitary (b i) = ε i • b i`), unit modulus per coordinate. -/
noncomputable def diagUnitary
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  b.equiv (scaledBasis b ε hε) (Equiv.refl (Fin N))

/-- `diagUnitary` scales the `i`-th basis vector by `ε i`. -/
lemma diagUnitary_apply_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    diagUnitary b ε hε (b i) = ε i • b i := by
  unfold diagUnitary
  rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, scaledBasis_apply]

/-- The inverse `diagUnitary` scales the `i`-th basis vector by `(ε i)⁻¹`.
`diagUnitary ((ε i)⁻¹ • b i) = b i` (since `ε i ≠ 0`), then
`symm_apply_apply`. -/
lemma diagUnitary_symm_apply_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    (diagUnitary b ε hε).symm (b i) = (ε i)⁻¹ • b i := by
  have hεne : ε i ≠ 0 := by rw [← norm_ne_zero_iff, hε i]; norm_num
  have h : diagUnitary b ε hε ((ε i)⁻¹ • b i) = b i := by
    rw [map_smul, diagUnitary_apply_basis, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  conv_lhs => rw [← h]
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The Stage-2 phase, extracted per index and anchored at `ε i₀ := 1`.
For `j ≠ i₀`, `twoLevelPhase hf b i₀ j` is the unit phase `εⱼ` supplied by
`reducedMap_two_level_normal_form` for the pair `(i₀, j)`. -/
noncomputable def twoLevelPhase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ j : Fin N) : ℂ :=
  if h : j = i₀ then 1
  else Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := j) (Ne.symm h))

/-- The anchor phase is `1`: `twoLevelPhase hf b i₀ i₀ = 1`. -/
lemma twoLevelPhase_self
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    twoLevelPhase hf b i₀ i₀ = 1 := by
  unfold twoLevelPhase; rw [dif_pos rfl]

/-- Every extracted phase is unit modulus: `‖twoLevelPhase hf b i₀ j‖ = 1`
(anchor `‖1‖ = 1`; off-anchor from the Stage-2 `choose_spec`). -/
lemma twoLevelPhase_norm
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ j : Fin N) :
    ‖twoLevelPhase hf b i₀ j‖ = 1 := by
  unfold twoLevelPhase
  rcases eq_or_ne j i₀ with h | h
  · rw [dif_pos h, norm_one]
  · rw [dif_neg h]
    obtain ⟨_, hnorm, _⟩ :=
      Classical.choose_spec (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := j) (Ne.symm h))
    exact hnorm

/-- The **diagonally-reduced map**: `projMap D⁻¹ ∘ reducedMap hf b`, where
`D := diagUnitary b (twoLevelPhase hf b i₀) …` is the diagonal isometry built
from the extracted phases. -/
noncomputable def diagReducedMap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun p => projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
    (reducedMap hf b p)

/-- **`diagReducedMap` is `TransProbPreserving`.** Composition of the
preserving `projMap D⁻¹` and the preserving `reducedMap hf b`. -/
lemma diagReducedMap_transProbPreserving
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    TransProbPreserving (diagReducedMap hf b i₀) :=
  (projMap_transProbPreserving
    (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm).comp
    (reducedMap_transProbPreserving hf b)

/-- **`diagReducedMap` still fixes every basis ray.** `reducedMap` fixes
`mk (b i)`, then `projMap D⁻¹` sends it to `mk ((ε i)⁻¹ • b i) = mk (b i)`
(scaling invariance). -/
lemma diagReducedMap_fixes_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ i : Fin N) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := by
  show projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
      (reducedMap hf b _) = _
  rw [reducedMap_fixes_basis hf b i, projMap_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(twoLevelPhase hf b i₀ i)⁻¹, ?_⟩
  rw [diagUnitary_symm_apply_basis]

/-- **HEADLINE (diagonal-phase reduction).** The diagonally-reduced map fixes
the two-level superposition ray `mk (b i₀ + b i)` for every `i ≠ i₀`.

Proof. Stage 2 (`reducedMap_two_level_normal_form`, extracted through
`twoLevelPhase`) gives `reducedMap hf b (mk (b i₀ + b i)) = mk (b i₀ + c • b i)`
with `c := twoLevelPhase hf b i₀ i` unit modulus. Applying `D⁻¹`:
`D⁻¹ (b i₀) = (ε i₀)⁻¹ • b i₀ = b i₀` (anchor `ε i₀ = 1`) and
`D⁻¹ (b i) = c⁻¹ • b i`, so `D⁻¹ (b i₀ + c • b i) = b i₀ + (c c⁻¹) • b i =
b i₀ + b i`. Hence the ray is fixed. This is the setup consumed by the cocycle
step (pieces 2–3): a `TransProbPreserving` map fixing every basis ray and every
two-level ray `mk (b i₀ + b i)`. **No ℂ-linearity assumed.** -/
theorem diagReducedMap_fixes_two_level
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i : Fin N} (hij : i₀ ≠ i) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij) := by
  obtain ⟨_, hnorm, heq⟩ :=
    Classical.choose_spec (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij)
  have hci : twoLevelPhase hf b i₀ i
      = Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij) := by
    rw [twoLevelPhase, dif_neg (Ne.symm hij)]
  set c := Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij) with hc
  have hcne : c ≠ 0 := by rw [← norm_ne_zero_iff, hnorm]; norm_num
  show projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
      (reducedMap hf b _) = _
  rw [heq, projMap_mk]
  have hcomp :
      (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
        (b i₀ + c • b i) = b i₀ + b i := by
    rw [map_add, map_smul, diagUnitary_symm_apply_basis, diagUnitary_symm_apply_basis,
        twoLevelPhase_self hf b i₀, hci]
    simp only [inv_one, one_smul, smul_smul]
    rw [mul_inv_cancel₀ hcne, one_smul]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, hcomp]

/-! ## Stage 3 piece 2: coordinate moduli, the two-level relative phase, cocycle datum

Piece 2 of the Stage-3 residual, the derivation-heavy core, built on the diagonally
reduced map `h := diagReducedMap hf b i₀` (`TransProbPreserving`, fixing every basis
ray and every anchored two-level ray `mk (b i₀ + b i)`). Writing `h (mk ψ) = mk φ`,
`cⱼ := b.repr ψ j`, `dⱼ := b.repr φ j`:

* **Moduli** (`coord_modulus_of_fixes_basis`, `diagReducedMap_coord_modulus`):
  `‖dⱼ‖² / ‖φ‖² = ‖cⱼ‖² / ‖ψ‖²`, for any `TransProbPreserving` map fixing the basis
  rays.
* **Two-level relative phase** (`two_level_relphase_of_fixes`,
  `diagReducedMap_two_level_relphase`) — the heart of piece 2:
  `Re(d̄_{i₀} d_i) / ‖φ‖² = Re(c̄_{i₀} c_i) / ‖ψ‖²`, i.e.
  `arg(d_i / d_{i₀}) = ± arg(c_i / c_{i₀})`. The overlap fixes only the real part;
  the sign of the imaginary part — the cocycle's ℤ/2 datum — stays free.
* **Conditional pairwise relation** (`diagReducedMap_pairwise_relphase_of_fixed`):
  for any pair `(i, j)` whose two-level ray is fixed by `h`, the analogous relation
  `Re(d̄_i d_j) / ‖φ‖² = Re(c̄_i c_j) / ‖ψ‖²` holds.

**No ℂ-linearity of `f`/`h` is used anywhere below**: every relation comes from the
`transProb`/`transProbVec` overlap algebra, the fixed-point content of
`diagReducedMap`, and the moduli. The precise residual is documented after the
lemmas and in the `Stage 3 (residual)` section. -/

/-- **Complex parallelogram expansion.** For `A B : ℂ`,
`‖A + B‖² = ‖A‖² + ‖B‖² + 2·Re(conj A · B)`. Via `Complex.normSq_add` and
`Complex.normSq_eq_norm_sq`; `(A · conj B).re = (conj A · B).re` since `re` is
conjugation-invariant. -/
lemma cnorm_add_sq (A B : ℂ) :
    ‖A + B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * ((starRingEnd ℂ) A * B).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add]
  have hre : (A * (starRingEnd ℂ) B).re = ((starRingEnd ℂ) A * B).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  rw [hre]

/-- The inner product of `ψ` with a basis vector is the conjugate of the
corresponding coordinate: `⟪ψ, b j⟫ = conj (b.repr ψ j)`. From
`OrthonormalBasis.repr_apply_apply` (`b.repr ψ j = ⟪b j, ψ⟫`) and
`inner_conj_symm`. -/
lemma inner_eq_conj_repr
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    (inner ℂ ψ (b j) : ℂ) = (starRingEnd ℂ) (b.repr ψ j) := by
  rw [b.repr_apply_apply]
  exact (inner_conj_symm ψ (b j)).symm

/-- The inner product of `ψ` with a two-level basis sum unfolds to the conjugate
of the coordinate sum: `⟪ψ, b i₀ + b i⟫ = conj (b.repr ψ i₀ + b.repr ψ i)`. -/
lemma inner_add_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i₀ i : Fin N) :
    (inner ℂ ψ (b i₀ + b i) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i₀ + b.repr ψ i) := by
  rw [inner_add_right, inner_eq_conj_repr b ψ i₀, inner_eq_conj_repr b ψ i, map_add]

/-- The squared norm of a two-level basis sum is `2` (Pythagoras via
`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` and the unit norms). -/
lemma add_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
        (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀, b.orthonormal.norm_eq_one i]
  norm_num

/-- **Two-level overlap in coordinates.** The transition probability from `mk ψ`
to the two-level ray `mk (b i₀ + b i)` is
`‖b.repr ψ i₀ + b.repr ψ i‖² / (‖ψ‖² · 2)`. Combines `transProb_mk`,
`inner_add_basis` (the numerator), `RCLike.norm_conj`, and `add_basis_norm_sq`
(the denominator's `‖b i₀ + b i‖² = 2`). -/
lemma transProb_two_level
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) {i₀ i : Fin N} (hij : i₀ ≠ i) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = ‖b.repr ψ i₀ + b.repr ψ i‖ ^ 2 / (‖ψ‖ ^ 2 * 2) := by
  rw [transProb_mk hψ (add_basis_ne_zero b hij)]
  unfold transProbVec
  rw [inner_add_basis, RCLike.norm_conj, add_basis_norm_sq b hij]

/-- **Moduli preservation for a basis-fixing preserver.** Any
`TransProbPreserving` map `g` that fixes every source basis ray preserves the
normalised squared modulus of every coordinate:
`‖b.repr (g (mk ψ)).rep i‖² / ‖(g (mk ψ)).rep‖² = ‖b.repr ψ i‖² / ‖ψ‖²`.
Generalises `reducedMap_coord_modulus` off `reducedMap` to an abstract `g`; the
proof is the same `transProb_of_fixed` + `transProb_srcPoint` composition. -/
theorem coord_modulus_of_fixes_basis
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ j, g (srcPoint b j) = srcPoint b j)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have key := hg.transProb_of_fixed (hfixb i) (Projectivization.mk ℂ ψ hψ)
  rw [transProb_srcPoint b hψ i] at key
  set gp := g (Projectivization.mk ℂ ψ hψ) with hgp
  have hgp_coord : transProb gp (srcPoint b i)
      = ‖b.repr gp.rep i‖ ^ 2 / ‖gp.rep‖ ^ 2 := by
    conv_lhs => rw [← Projectivization.mk_rep gp]
    exact transProb_srcPoint b gp.rep_nonzero i
  rw [← hgp_coord, key]

/-- **Two-level relative-phase constraint (general).** Let `g` be
`TransProbPreserving`, fixing every basis ray and the two-level ray
`mk (b i₀ + b i)`. Writing `g (mk ψ) = mk φ`, the *real part* of the relative
phase between the `i₀`- and `i`-coordinates is preserved:
`Re(conj d_{i₀} · d_i) / ‖φ‖² = Re(conj c_{i₀} · c_i) / ‖ψ‖²`, with
`cⱼ = b.repr ψ j`, `dⱼ = b.repr φ j`.

Proof. The two-level overlap `transProb (g (mk ψ)) (mk (b i₀ + b i))` equals
`transProb (mk ψ) (mk (b i₀ + b i))` because `g` fixes the two-level ray
(`transProb_of_fixed`); `transProb_two_level` reads both as
`‖·₀ + ·ᵢ‖² / (‖·‖² · 2)`. Cross-multiplying and expanding the numerators with
`cnorm_add_sq` leaves, after cancelling the modulus terms via
`coord_modulus_of_fixes_basis`, exactly the real-part relation.

**No linearity is used**: this is pure overlap algebra. The imaginary part of
`conj d_{i₀} · d_i` — the sign of the relative phase, the cocycle's ℤ/2 datum —
is *not* pinned, and the result holds for both the unitary (`d = c`) and
antiunitary (`d = conj c`) branches. -/
theorem two_level_relphase_of_fixes
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ j, g (srcPoint b j) = srcPoint b j)
    {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hfix2 : g (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i₀)
          * b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i).re
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i₀) * b.repr ψ i).re / ‖ψ‖ ^ 2 := by
  have hA := hg.transProb_of_fixed hfix2 (Projectivization.mk ℂ ψ hψ)
  rw [transProb_two_level b hψ hij] at hA
  have md0 := coord_modulus_of_fixes_basis hg b hfixb hψ i₀
  have mdi := coord_modulus_of_fixes_basis hg b hfixb hψ i
  set q := g (Projectivization.mk ℂ ψ hψ) with hq
  have hLHS : transProb q (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = ‖b.repr q.rep i₀ + b.repr q.rep i‖ ^ 2 / (‖q.rep‖ ^ 2 * 2) := by
    conv_lhs => rw [← q.mk_rep]
    exact transProb_two_level b q.rep_nonzero hij
  rw [hLHS] at hA
  have hDφ : ‖q.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr q.rep_nonzero)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hcross := (div_eq_div_iff (mul_ne_zero hDφ (by norm_num : (2 : ℝ) ≠ 0))
    (mul_ne_zero hDψ (by norm_num : (2 : ℝ) ≠ 0))).mp hA
  rw [cnorm_add_sq, cnorm_add_sq] at hcross
  have hm0 := (div_eq_div_iff hDφ hDψ).mp md0
  have hmi := (div_eq_div_iff hDφ hDψ).mp mdi
  rw [div_eq_div_iff hDφ hDψ]
  linear_combination (1 / 4 : ℝ) * hcross - (1 / 2 : ℝ) * hm0 - (1 / 2 : ℝ) * hmi

/-- **Moduli preservation for the diagonally reduced map.** Instance of
`coord_modulus_of_fixes_basis` for `diagReducedMap hf b i₀`. -/
theorem diagReducedMap_coord_modulus
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 :=
  coord_modulus_of_fixes_basis (diagReducedMap_transProbPreserving hf b i₀) b
    (fun j => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ j) hψ i

/-- **HEADLINE (two-level relative phase, the heart of piece 2).** The diagonally
reduced map `diagReducedMap hf b i₀` preserves the real part of the relative phase
between the anchor coordinate `i₀` and any coordinate `i ≠ i₀`:
`Re(conj d_{i₀} · d_i) / ‖φ‖² = Re(conj c_{i₀} · c_i) / ‖ψ‖²`, i.e.
`arg(d_i / d_{i₀}) = ± arg(c_i / c_{i₀})`. Instance of `two_level_relphase_of_fixes`
with the basis fixing (`diagReducedMap_fixes_basis`) and the anchored two-level
fixing (`diagReducedMap_fixes_two_level`). The `±` sign is genuinely free (only the
real part is pinned) and no ℂ-linearity is assumed. -/
theorem diagReducedMap_two_level_relphase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i : Fin N} (hij : i₀ ≠ i)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i₀)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i₀) * b.repr ψ i).re / ‖ψ‖ ^ 2 :=
  two_level_relphase_of_fixes (diagReducedMap_transProbPreserving hf b i₀) b
    (fun j => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ j)
    hij (diagReducedMap_fixes_two_level hf b hij) hψ

/-- **Conditional pairwise relative phase (the (i, j) leg of the 2-cocycle).**
For a pair `(i, j)` whose two-level ray `mk (b i + b j)` is fixed by
`diagReducedMap hf b i₀`, the relative-phase relation
`Re(conj d_i · d_j) / ‖φ‖² = Re(conj c_i · c_j) / ‖ψ‖²` holds. Immediate instance
of `two_level_relphase_of_fixes` for the pair `(i, j)`. The fixing hypothesis
`hfix` is the *only* residual input: the anchored diagonal reduction supplies it
for `i = i₀` (`diagReducedMap_fixes_two_level`) but not for general non-anchored
pairs (see the residual note). -/
theorem diagReducedMap_pairwise_relphase_of_fixed
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    (hfix : diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).re / ‖ψ‖ ^ 2 :=
  two_level_relphase_of_fixes (diagReducedMap_transProbPreserving hf b i₀) b
    (fun k => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k)
    hij hfix hψ

/-! ## Stage 3 piece 2 (W4): triple-support probe and the non-anchored two-level fixing

The non-anchored two-level fixing `g (mk (b i + b j)) = mk (b i + b j)` for
`i, j ≠ i₀` — the missing input that upgrades the pairwise relative-phase relation
to unconditional — is derived here through a **triple-support probe**. The equal
triple ray `mk (b i₀ + b i + b j)` is first shown fixed
(`diagReducedMap_fixes_three_level`), then used as a probe carrying both `i` and
`j` to fix the non-anchored two-level ray
(`diagReducedMap_fixes_two_level_general`), whence the conditional pairwise leg
becomes unconditional (`diagReducedMap_pairwise_relphase`).

**Critical honesty (audit).** Every probe here is a **real-coordinate**
superposition (all surviving source coordinates `= 1`), so its ray is fixed by
the identity and by coordinatewise conjugation **alike**: fixing it is consistent
with **both** the unitary (`d = c`) and antiunitary (`d = conj c`) branches, and
does **not** collapse the global unitary/antiunitary choice. What is established
is the **coboundary structure** of the phase cocycle (the pairwise real-part
relations), not the global sign (piece 3). No ℂ-linearity is assumed: every
alignment comes from moduli preservation, a single fixed-probe overlap, and the
saturation lemma. -/

/-- **Saturation.** A complex number whose real part equals its modulus is that
real part: `‖z‖ = z.re → z = z.re`. Squaring, `z.re² = ‖z‖² = z.re² + z.im²`
forces `z.im = 0`. -/
lemma norm_eq_re_imp_eq {z : ℂ} (h : ‖z‖ = z.re) : z = (z.re : ℂ) := by
  have him : z.im = 0 := by
    have h1 : z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_apply]; exact Complex.normSq_eq_norm_sq z
    have hsq : ‖z‖ ^ 2 = z.re * z.re := by rw [h]; ring
    rw [hsq] at h1
    have : z.im * z.im = 0 := by linarith
    exact mul_self_eq_zero.mp this
  rw [Complex.ext_iff]
  exact ⟨by simp, by rw [him]; simp⟩

/-- **Phase alignment from a saturated overlap.** If two complex numbers have
equal modulus `‖c‖ = ‖a‖`, with `a ≠ 0`, and the real part of `conj a · c`
saturates the modulus product `Re(conj a · c) = ‖a‖²`, then `c = a`. Route:
`‖conj a · c‖ = ‖a‖‖c‖ = ‖a‖²`, so `Re = ‖·‖`; `norm_eq_re_imp_eq` makes
`conj a · c` real and equal to `‖a‖² = conj a · a`; cancel `conj a ≠ 0`. This is
the neutral alignment step; applied to a real-coordinate probe it aligns `d = a`
on **both** the unitary and antiunitary branches, so it does not collapse the
sign. -/
lemma eq_of_re_conj_mul_eq {a c : ℂ} (ha : a ≠ 0) (hmod : ‖c‖ = ‖a‖)
    (hre : ((starRingEnd ℂ) a * c).re = ‖a‖ ^ 2) : c = a := by
  have hnorm : ‖(starRingEnd ℂ) a * c‖ = ((starRingEnd ℂ) a * c).re := by
    rw [norm_mul, RCLike.norm_conj, hmod, hre]; ring
  have hsat : (starRingEnd ℂ) a * c = (((starRingEnd ℂ) a * c).re : ℂ) :=
    norm_eq_re_imp_eq hnorm
  rw [hre] at hsat
  have haa : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]; norm_cast
  have hca : (starRingEnd ℂ) a * c = (starRingEnd ℂ) a * a := by rw [hsat, haa]
  have hconj_ne : (starRingEnd ℂ) a ≠ 0 := star_ne_zero.mpr ha
  exact mul_left_cancel₀ hconj_ne hca

/-- **Triple-support reconstruction.** A vector whose coordinates in the basis
`b` vanish outside `{i₀, i, j}` (distinct) is the triple sum of its three
surviving coordinates. `OrthonormalBasis.sum_repr` expands `φ`,
`Finset.sum_subset` drops the null coordinates, and the three-element
`Finset.sum` collapses. The 3-support analogue of `repr_eq_pair_of_support`. -/
lemma repr_eq_triple_of_support
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (φ : EuclideanSpace ℂ (Fin N)) {i₀ i j : Fin N}
    (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j)
    (hsupp : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → b.repr φ k = 0) :
    φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i + b.repr φ j • b j := by
  have hvanish : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      k ∉ ({i₀, i, j} : Finset (Fin N)) → b.repr φ k • b k = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hsupp k hk.1 hk.2.1 hk.2.2, zero_smul]
  calc φ = ∑ k, b.repr φ k • b k := (b.sum_repr φ).symm
    _ = ∑ k ∈ ({i₀, i, j} : Finset (Fin N)), b.repr φ k • b k :=
          (Finset.sum_subset (Finset.subset_univ _) hvanish).symm
    _ = b.repr φ i₀ • b i₀ + b.repr φ i • b i + b.repr φ j • b j := by
          rw [Finset.sum_insert (by simp [h0i, h0j]),
              Finset.sum_insert (by simp [hij]), Finset.sum_singleton, add_assoc]

/-- The squared norm of a triple basis sum is `3` (Pythagoras: `b i₀ + b i ⟂ b j`
and `‖b i₀ + b i‖² = 2`, `‖b j‖² = 1`). -/
lemma add3_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    ‖(b i₀ + b i + b j : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 3 := by
  have hperp : (inner ℂ (b i₀ + b i : EuclideanSpace ℂ (Fin N)) (b j) : ℂ) = 0 := by
    rw [inner_add_left, orthonormal_iff_ite.mp b.orthonormal i₀ j,
        orthonormal_iff_ite.mp b.orthonormal i j, if_neg h0j, if_neg hij, add_zero]
  have h3 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀ + b i) (b j) hperp
  rw [pow_two, h3]
  have e1 : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖
      * ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ = 2 := by
    rw [← pow_two]; exact add_basis_norm_sq b h0i
  rw [e1, b.orthonormal.norm_eq_one j]; norm_num

/-- A triple of distinct basis vectors sums to a nonzero vector (norm² = `3`). -/
lemma add3_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    (b i₀ + b i + b j : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have hn := add3_basis_norm_sq b h0i h0j hij
  rw [h, norm_zero, zero_pow (by norm_num)] at hn
  norm_num at hn

/-- The inner product of `ψ` with a triple basis sum unfolds to the conjugate of
the coordinate sum: `⟪ψ, b i₀ + b i + b j⟫ = conj (c_{i₀} + c_i + c_j)`. -/
lemma inner_add3_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i₀ i j : Fin N) :
    (inner ℂ ψ (b i₀ + b i + b j) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i₀ + b.repr ψ i + b.repr ψ j) := by
  rw [inner_add_right, inner_add_basis, inner_eq_conj_repr, ← map_add]

/-- **Triple parallelogram expansion.** `‖A + B + C‖² = ‖A‖² + ‖B‖² + ‖C‖²
+ 2·Re(conj A · B) + 2·Re(conj A · C) + 2·Re(conj B · C)`. Two applications of
`cnorm_add_sq` plus `Re(conj (A+B) · C) = Re(conj A · C) + Re(conj B · C)`. -/
lemma cnorm_add3_sq (A B C : ℂ) :
    ‖A + B + C‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2
      + 2 * ((starRingEnd ℂ) A * B).re + 2 * ((starRingEnd ℂ) A * C).re
      + 2 * ((starRingEnd ℂ) B * C).re := by
  rw [cnorm_add_sq (A + B) C, cnorm_add_sq A B]
  have hsplit : ((starRingEnd ℂ) (A + B) * C).re
      = ((starRingEnd ℂ) A * C).re + ((starRingEnd ℂ) B * C).re := by
    rw [map_add, add_mul, Complex.add_re]
  rw [hsplit]; ring

/-- **Triple-level overlap in coordinates.** The transition probability from
`mk ψ` to the equal triple ray `mk (b i₀ + b i + b j)` is
`‖c_{i₀} + c_i + c_j‖² / (‖ψ‖² · 3)`. Combines `transProb_mk`, `inner_add3_basis`
(numerator), `RCLike.norm_conj`, and `add3_basis_norm_sq` (denominator). -/
lemma transProb_three_level
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0)
    {i₀ i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i₀ + b i + b j) (add3_basis_ne_zero b h0i h0j hij))
      = ‖b.repr ψ i₀ + b.repr ψ i + b.repr ψ j‖ ^ 2 / (‖ψ‖ ^ 2 * 3) := by
  rw [transProb_mk hψ (add3_basis_ne_zero b h0i h0j hij)]
  unfold transProbVec
  rw [inner_add3_basis, RCLike.norm_conj, add3_basis_norm_sq b h0i h0j hij]

/-! ## Stage 3 piece 2 (W4): the triple and non-anchored two-level fixings -/

/-- **HEADLINE (triple-support fixing).** The diagonally reduced map fixes the
equal triple superposition ray `mk (b i₀ + b i + b j)` for distinct `i₀, i, j`.

Proof. Write `g := diagReducedMap hf b i₀`, `φ := (g (mk w)).rep` with
`w := b i₀ + b i + b j`. Stage-1 moduli (`coord_modulus_of_fixes_basis`) restrict
`φ` to support `{i₀, i, j}` with equal coordinate moduli `‖d_k‖² = ‖φ‖²/3`. The
two anchored two-level fixings (`diagReducedMap_two_level_relphase` at the probe
`w`) pin `Re(conj d_{i₀} · d_i) = ‖φ‖²/3 = ‖d_{i₀}‖²` and likewise for `j`, which
saturates the modulus product; `eq_of_re_conj_mul_eq` forces `d_i = d_{i₀}` and
`d_j = d_{i₀}`, so `φ = d_{i₀} · w` and `mk φ = mk w`.

**Audit note.** The source coordinates `c_{i₀} = c_i = c_j = 1` are real, so this
fixing is consistent with both `d = c` (unitary) and `d = conj c` (antiunitary):
it establishes cocycle coboundary structure, **not** the global sign. No
ℂ-linearity is assumed. -/
theorem diagReducedMap_fixes_three_level
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i j : Fin N}
    (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i₀ + b i + b j) (add3_basis_ne_zero b h0i h0j hij))
      = Projectivization.mk ℂ (b i₀ + b i + b j) (add3_basis_ne_zero b h0i h0j hij) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  set w : EuclideanSpace ℂ (Fin N) := b i₀ + b i + b j with hw_def
  have hwne : w ≠ 0 := add3_basis_ne_zero b h0i h0j hij
  have hwnorm : ‖w‖ ^ 2 = 3 := add3_basis_norm_sq b h0i h0j hij
  have hwk : ∀ k, b.repr w k
      = (if k = i₀ then (1 : ℂ) else 0) + (if k = i then 1 else 0)
        + (if k = j then 1 else 0) := by
    intro k
    rw [hw_def, b.repr_apply_apply, inner_add_right, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal k i₀,
        orthonormal_iff_ite.mp b.orthonormal k i,
        orthonormal_iff_ite.mp b.orthonormal k j]
  have hwi0 : b.repr w i₀ = 1 := by rw [hwk i₀, if_pos rfl, if_neg h0i, if_neg h0j]; ring
  have hwi : b.repr w i = 1 := by rw [hwk i, if_neg (Ne.symm h0i), if_pos rfl, if_neg hij]; ring
  have hwj : b.repr w j = 1 := by
    rw [hwk j, if_neg (Ne.symm h0j), if_neg (Ne.symm hij), if_pos rfl]; ring
  have hwzero : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → b.repr w k = 0 := by
    intro k hk0 hki hkj; rw [hwk k, if_neg hk0, if_neg hki, if_neg hkj]; ring
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b hfixb hwne k
    rwa [← hφ_def] at h
  have hsupp : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → b.repr φ k = 0 := by
    intro k hk0 hki hkj
    have hm := hcm k
    rw [hwzero k hk0 hki hkj, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  have md : ∀ k, k = i₀ ∨ k = i ∨ k = j → ‖b.repr φ k‖ ^ 2 = ‖φ‖ ^ 2 / 3 := by
    intro k hk
    have hm := hcm k
    have hck : ‖b.repr w k‖ ^ 2 = 1 := by
      rcases hk with h | h | h
      · rw [h, hwi0, norm_one, one_pow]
      · rw [h, hwi, norm_one, one_pow]
      · rw [h, hwj, norm_one, one_pow]
    rw [hck, hwnorm] at hm
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hm
    rw [eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hm]
  have md_i0 := md i₀ (Or.inl rfl)
  have md_i := md i (Or.inr (Or.inl rfl))
  have md_j := md j (Or.inr (Or.inr rfl))
  have ha0 : b.repr φ i₀ ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by norm_num)] at md_i0
    exact absurd md_i0.symm (div_pos hφpos (by norm_num)).ne'
  have hrel_i : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re / ‖φ‖ ^ 2
      = ((starRingEnd ℂ) (b.repr w i₀) * b.repr w i).re / ‖w‖ ^ 2 := by
    have h := diagReducedMap_two_level_relphase hf b i₀ h0i hwne
    rwa [← hφ_def] at h
  rw [hwi0, hwi, hwnorm] at hrel_i
  simp only [map_one, mul_one, Complex.one_re] at hrel_i
  have hrel_j : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ j).re / ‖φ‖ ^ 2
      = ((starRingEnd ℂ) (b.repr w i₀) * b.repr w j).re / ‖w‖ ^ 2 := by
    have h := diagReducedMap_two_level_relphase hf b i₀ h0j hwne
    rwa [← hφ_def] at h
  rw [hwi0, hwj, hwnorm] at hrel_j
  simp only [map_one, mul_one, Complex.one_re] at hrel_j
  have hre_i : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re = ‖b.repr φ i₀‖ ^ 2 := by
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hrel_i
    rw [md_i0, eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hrel_i]
  have hre_j : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ j).re = ‖b.repr φ i₀‖ ^ 2 := by
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hrel_j
    rw [md_i0, eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hrel_j]
  have hmod_i : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), md_i, md_i0]
  have hmod_j : ‖b.repr φ j‖ = ‖b.repr φ i₀‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ j)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), md_j, md_i0]
  have hdi : b.repr φ i = b.repr φ i₀ := eq_of_re_conj_mul_eq ha0 hmod_i hre_i
  have hdj : b.repr φ j = b.repr φ i₀ := eq_of_re_conj_mul_eq ha0 hmod_j hre_j
  have hrec : φ = b.repr φ i₀ • w := by
    have h1 := repr_eq_triple_of_support b φ h0i h0j hij hsupp
    rw [hdi, hdj] at h1
    rw [hw_def, smul_add, smul_add]; exact h1
  have hmkeq : Projectivization.mk ℂ φ hφne = Projectivization.mk ℂ w hwne :=
    (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i₀, hrec.symm⟩
  calc diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne :=
        (Projectivization.mk_rep (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne))).symm
    _ = Projectivization.mk ℂ w hwne := hmkeq

/-- **HEADLINE (non-anchored two-level fixing).** The diagonally reduced map fixes
**every** two-level superposition ray `mk (b i + b j)` with `i, j ≠ i₀`,
`i ≠ j` — not only the anchored ones. This upgrades the pairwise relative-phase
leg to unconditional.

Proof. Write `g := diagReducedMap hf b i₀`, `φ := (g (mk w')).rep`,
`w' := b i + b j`. Stage-1 moduli restrict `φ` to support `{i, j}`
(`d_{i₀} = 0`) with `‖d_i‖² = ‖d_j‖² = ‖φ‖²/2`. The **fixed triple ray**
`mk (b i₀ + b i + b j)` (`diagReducedMap_fixes_three_level`) — a probe carrying
both `i` and `j` — used through `transProb_of_fixed` gives the overlap identity
`‖d_i + d_j‖² / (‖φ‖²·3) = ‖1 + 1‖² / (2·3)`, whence
`Re(conj d_i · d_j) = ‖φ‖²/2 = ‖d_i‖²`, saturating the modulus product;
`eq_of_re_conj_mul_eq` forces `d_j = d_i`, so `φ = d_i · w'` and `mk φ = mk w'`.

**Audit note.** The probe `b i₀ + b i + b j` and the source `b i + b j` are
real-coordinate: consistent with both branches. Coboundary structure, not global
sign. No ℂ-linearity assumed. -/
theorem diagReducedMap_fixes_two_level_general
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i j : Fin N}
    (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  set w : EuclideanSpace ℂ (Fin N) := b i + b j with hw_def
  have hwne : w ≠ 0 := add_basis_ne_zero b hij
  have hwnorm : ‖w‖ ^ 2 = 2 := add_basis_norm_sq b hij
  have hwk : ∀ k, b.repr w k = (if k = i then (1 : ℂ) else 0) + (if k = j then 1 else 0) := by
    intro k
    rw [hw_def, b.repr_apply_apply, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal k i, orthonormal_iff_ite.mp b.orthonormal k j]
  have hwi : b.repr w i = 1 := by rw [hwk i, if_pos rfl, if_neg hij]; ring
  have hwj : b.repr w j = 1 := by rw [hwk j, if_neg (Ne.symm hij), if_pos rfl]; ring
  have hwi0 : b.repr w i₀ = 0 := by rw [hwk i₀, if_neg h0i, if_neg h0j]; ring
  have hwzero : ∀ k, k ≠ i → k ≠ j → b.repr w k = 0 := by
    intro k hki hkj; rw [hwk k, if_neg hki, if_neg hkj]; ring
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b hfixb hwne k
    rwa [← hφ_def] at h
  have hsupp : ∀ k, k ≠ i → k ≠ j → b.repr φ k = 0 := by
    intro k hki hkj
    have hm := hcm k
    rw [hwzero k hki hkj, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  have hd0 : b.repr φ i₀ = 0 := hsupp i₀ h0i h0j
  have md : ∀ k, k = i ∨ k = j → ‖b.repr φ k‖ ^ 2 = ‖φ‖ ^ 2 / 2 := by
    intro k hk
    have hm := hcm k
    have hck : ‖b.repr w k‖ ^ 2 = 1 := by
      rcases hk with h | h
      · rw [h, hwi, norm_one, one_pow]
      · rw [h, hwj, norm_one, one_pow]
    rw [hck, hwnorm] at hm
    rw [div_eq_div_iff hden (by norm_num : (2 : ℝ) ≠ 0)] at hm
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]; linarith [hm]
  have md_i := md i (Or.inl rfl)
  have md_j := md j (Or.inr rfl)
  have ha_i : b.repr φ i ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by norm_num)] at md_i
    exact absurd md_i.symm (div_pos hφpos (by norm_num)).ne'
  -- triple-support probe overlap
  have hfix3 := diagReducedMap_fixes_three_level hf b h0i h0j hij
  have hoverlap := hg.transProb_of_fixed hfix3 (Projectivization.mk ℂ w hwne)
  rw [show diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne) = Projectivization.mk ℂ φ hφne
        from (Projectivization.mk_rep
          (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne))).symm,
      transProb_three_level b hφne h0i h0j hij,
      transProb_three_level b hwne h0i h0j hij,
      hd0, hwi0, hwi, hwj, hwnorm, zero_add, zero_add] at hoverlap
  have h11 : ‖(1 : ℂ) + 1‖ ^ 2 = 4 := by
    rw [cnorm_add_sq]
    simp only [norm_one, one_pow, map_one, mul_one, Complex.one_re]; norm_num
  rw [h11] at hoverlap
  have hDφ : ‖φ‖ ^ 2 * 3 ≠ 0 := mul_ne_zero hden (by norm_num)
  have hcross := (div_eq_div_iff hDφ (by norm_num : (2 : ℝ) * 3 ≠ 0)).mp hoverlap
  rw [cnorm_add_sq, md_i, md_j] at hcross
  have hRe : ((starRingEnd ℂ) (b.repr φ i) * b.repr φ j).re = ‖b.repr φ i‖ ^ 2 := by
    rw [md_i, eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]; nlinarith [hcross]
  have hmod_ij : ‖b.repr φ j‖ = ‖b.repr φ i‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ j)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i)), md_j, md_i]
  have hdj : b.repr φ j = b.repr φ i := eq_of_re_conj_mul_eq ha_i hmod_ij hRe
  have hrec : φ = b.repr φ i • w := by
    have h1 := repr_eq_pair_of_support b φ hij hsupp
    rw [hdj] at h1
    rw [hw_def, smul_add]; exact h1
  have hmkeq : Projectivization.mk ℂ φ hφne = Projectivization.mk ℂ w hwne :=
    (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i, hrec.symm⟩
  calc diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne :=
        (Projectivization.mk_rep (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne))).symm
    _ = Projectivization.mk ℂ w hwne := hmkeq

/-- **HEADLINE (unconditional pairwise relative phase, the 2-cocycle coboundary).**
For **any** distinct `i, j ≠ i₀`, the diagonally reduced map preserves the real
part of the relative phase between coordinates `i` and `j`:
`Re(conj d_i · d_j) / ‖φ‖² = Re(conj c_i · c_j) / ‖ψ‖²`, for every source ray
`mk ψ`. Discharges the `hfix` hypothesis of
`diagReducedMap_pairwise_relphase_of_fixed` via the non-anchored two-level fixing
`diagReducedMap_fixes_two_level_general`.

Together with `diagReducedMap_two_level_relphase` (the anchored legs
`(i₀, k)`), the pairwise legs `(i, j)` here give the full **coboundary
structure** of the phase 2-cocycle — the real-part relations
`Re(c̄_i d_j) = Re(c̄_i c_j)·‖φ‖²/‖ψ‖²` for all pairs — with the ± sign of the
imaginary parts still free (the ℤ/2 datum resolved only by piece 3). No
ℂ-linearity is assumed. -/
theorem diagReducedMap_pairwise_relphase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).re / ‖ψ‖ ^ 2 :=
  diagReducedMap_pairwise_relphase_of_fixed hf b i₀ hij
    (diagReducedMap_fixes_two_level_general hf b h0i h0j hij) hψ

/-! ## Stage 3 (residual): the phase cocycle and the unitary/antiunitary dichotomy

Stages 1–2 are proved above with **no linearity assumed** on `f`: only
`TransProbPreserving`. **Stage 3 piece 1 (the diagonal-phase reduction) is
proved** (`diagReducedMap` + `diagReducedMap_fixes_two_level`), and **Stage 3
piece 2 is now CLOSED**: the moduli (`diagReducedMap_coord_modulus`), the
two-level relative-phase constraint (`diagReducedMap_two_level_relphase`, the
heart of piece 2), the **triple-support fixing**
(`diagReducedMap_fixes_three_level`), the **non-anchored two-level fixing**
(`diagReducedMap_fixes_two_level_general`, W4), and the resulting
**unconditional pairwise relative phase** (`diagReducedMap_pairwise_relphase`).
What remains to close the Wigner / Fubini–Study converse is the **dichotomy**
(piece 3) plus the Kähler selection. This is stated here precisely as the open
target; it is **not** an axiom and **not** a `sorry`.

**Audit note (W4, load-bearing).** Every probe used to establish the fixings —
the triple `mk (b i₀ + b i + b j)` and the pair `mk (b i + b j)` — is a
**real-coordinate** superposition; its ray is fixed by the identity and by
coordinatewise conjugation alike, so each fixing is consistent with **both** the
unitary (`d = c`) and antiunitary (`d = conj c`) branches. Piece 2 establishes
the **cocycle coboundary structure** (the pairwise real-part relations); it does
**not** collapse the global unitary/antiunitary sign, which is precisely piece 3.
`diagReducedMap` is **not** concluded to be the identity.

**State reached.** Write `g := reducedMap hf b` (`TransProbPreserving`, fixes
every basis ray). Stage 1 (`reducedMap_coord_modulus`) gives, for every
`p = mk ψ` with image rep `φ`, the modulus profile
`‖b.repr φ j‖² / ‖φ‖² = ‖b.repr ψ j‖² / ‖ψ‖²` for all `j`. Stage 2
(`reducedMap_two_level_normal_form`) gives, for each `i ≠ i₀`, a unit phase
`εᵢ` with `g (mk (b i₀ + b i)) = mk (b i₀ + εᵢ • b i)`. Stage 3 piece 1
(`diagReducedMap_fixes_two_level`) then removes these phases: the diagonally
reduced map `g' := diagReducedMap hf b i₀` is `TransProbPreserving`, fixes every
basis ray **and** every two-level ray `mk (b i₀ + b i)`.

**Residual crux.** The content is the coherence of the phases across overlapping
superpositions, in three linked pieces (pieces 1–2 discharged; piece 3 open),
none of which may assume ℂ-linearity:

1. **Diagonal-phase reduction (DONE).** Post-compose `g` with `projMap D⁻¹` for
   the diagonal isometry `D` (in the basis `b`) with `D (b i₀) = b i₀`,
   `D (b i) = εᵢ • b i` (so `D⁻¹` fixes every basis ray, preserving the frame
   reduction). After this, the reduced map fixes `mk (b i₀ + b i)` for **every**
   `i`. Realised here as `diagUnitary` / `diagReducedMap` /
   `diagReducedMap_fixes_two_level`.

2. **General coordinate phase (piece 2, CLOSED via W4).**
   For a general `ψ = ∑ cⱼ bⱼ` the two-level overlap
   `transProb (g (mk ψ)) (mk (b i₀ + b i))` together with the Stage-1 moduli pins
   the *real part* of each anchored relative phase, `Re(d̄_{i₀} d_i)/‖φ‖² =
   Re(c̄_{i₀} c_i)/‖ψ‖²` (`diagReducedMap_two_level_relphase`), leaving the sign of
   the imaginary part free — the cocycle's ℤ/2 datum.

   The **non-anchored fixing** `g (mk (b i + b j)) = mk (b i + b j)` for
   `i, j ≠ i₀` — the input that upgrades the pairwise leg to an unconditional
   relation — is now derived (**W4**). The anchored two-level probes
   `{mk (b i₀ + b k)}` each see only one of `i`, `j`, so a probe carrying *both*
   coordinates is needed: the equal three-level ray `mk (b i₀ + b i + b j)`. It is
   fixed by a relative-phase *saturation* argument (moduli equality forces
   `Re = |·|`, hence phase alignment: `norm_eq_re_imp_eq` / `eq_of_re_conj_mul_eq`)
   on triple-support states plus the triple-support reconstruction
   (`repr_eq_triple_of_support`), giving `diagReducedMap_fixes_three_level`. Using
   that fixed triple as a probe (through `transProb_of_fixed`) fixes the
   non-anchored pair (`diagReducedMap_fixes_two_level_general`), whence the
   unconditional pairwise real-part relation `Re(d̄_i d_j)/‖φ‖² =
   Re(c̄_i c_j)/‖ψ‖²` for all `i, j ≠ i₀` (`diagReducedMap_pairwise_relphase`).
   Together with the anchored legs these are the full **coboundary structure** of
   the phase 2-cocycle. The saturation probes are real-coordinate and keep both
   ± branches alive: piece 2 does **not** fix the global sign.

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
