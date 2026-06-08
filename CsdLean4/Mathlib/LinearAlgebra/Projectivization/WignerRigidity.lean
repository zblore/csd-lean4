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

## Open target (not proved here): the Wigner converse

The converse of the realisability inclusion `transProbPreserving_unitary` is the
**Wigner / Fubini–Study rigidity theorem**:

> `theorem (informal): TransProbPreserving f → ∃ U : Matrix.unitaryGroup (Fin N) ℂ,
>   f = fun p => U • p`

equivalently, the isometry group of `ℂℙⁿ` with the Fubini–Study metric is the
projective unitary group `PU(n+1)`. It is **not** stated here as an axiom or a
`sorry`. The two **remaining steps** are:

* **(2) Semilinear extraction.** Reconstruct a (semi)linear map agreeing with
  `f` by phase-tracking through superposition states: the transition data fixes
  `f` on basis rays and their orthogonality structure, but recovering the action
  on superpositions requires bookkeeping the relative phases, and consistency of
  these phases across overlapping superpositions is the coherence/cocycle crux.
  Over ℂ this produces a map that is either ℂ-linear or conjugate-ℂ-linear.
* **(3) Ruling out the antiunitary branch.** Transition-probability preservation
  alone admits both the unitary and antiunitary classes. The
  holomorphic / Kähler complex structure on `ℂℙⁿ` selects the unitary
  (ℂ-linear) branch. **Critical honesty note:** step (3) must *derive*
  ℂ-linearity from the Kähler structure, **not** assume it as a hypothesis. A
  smuggled linearity hypothesis would beg the question — the whole content of
  the converse is that the metric/transition data, plus the complex structure,
  *force* unitarity rather than merely permitting it.

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

end Projectivization
