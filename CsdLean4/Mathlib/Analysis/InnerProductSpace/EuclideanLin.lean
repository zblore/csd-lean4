/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Five facts about `EuclideanSpace` the corpus kept re-proving

**Category:** 1-Mathlib (CSD-free; one upstream candidate, four specialisations).
BACKLOG #146 cluster (D).

Each of these was proved independently in two or three layers, which is what `check-duplicates`
reported. They are collected here because they cross layers: `LF2` through `Thermo` and
`Empirical` all need them, so no CSD layer is the right owner.

## One upstream candidate

`Matrix.norm_toEuclideanLin_of_isom` — that `Aᴴ A = 1` makes `A`'s action norm-preserving. Mathlib
has no norm or isometry lemma for `toLpLin`/`toEuclideanLin` at all (its API is `toLpLin_apply`,
`_one`, `_mul`, `_mul_same`, `_pow`, `_symm_comp`, the determinant, and the adjoint bridge). This
one arrived with that verdict already written twice: `LF5/DilationFromFlow.lean` called its copy a
"generic helper (Mathlib upstream candidate)", and `CV/ArenaBridge.lean` carried a
character-for-character identical second copy whose docstring explained why — *"restated to keep
CV free of an LF5 import"*. That is a request for this file, made twice.

## Four convenience specialisations, which must not be offered upstream

* `EuclideanSpace.single_one_ne_zero` is `PiLp.single_eq_zero_iff` with `one_ne_zero`;
* `EuclideanSpace.normSq_inner_single` is `EuclideanSpace.inner_single_left` with `map_one`;
* `Complex.inner_ofReal_ofReal` is `RCLike.inner_apply` with `Complex.conj_ofReal`.
* `Matrix.toEuclideanLin_mul_apply` is `@[simp] Matrix.toLpLin_mul_same` **applied to a vector**.
  Upstream states composition as an equality of maps; the corpus always needs it applied, and had
  **five** copies of the applied form. A first draft of this file added a sixth with a docstring
  asserting Mathlib has no `_mul` lemma for `toEuclideanLin` — which is false, and looked true
  only because the upstream name is `toLpLin`, `toEuclideanLin` being `toLpLin 2 2`. The same
  mistake was live in `Empirical/CSD/Algorithms/CircuitFlow.lean`, whose `toEuclideanLin_pow_apply`
  re-derived `@[simp] toLpLin_pow` by induction; under #146 (D) it cites it instead.

They are here to be written once, not because upstream lacks them.

## What this file deliberately does **not** hold, and why that matters

Two facts that looked like they belonged here turned out to have homes already, and #146 (D)
retired their duplicates by **citing** rather than by moving them:

* **nonzero image of a unitary** — `Matrix.UnitaryGroup.toEuclideanLin_unitary_ne_zero`, in
  [`UnitaryTransitive.lean`](../../LinearAlgebra/Projectivization/UnitaryTransitive.lean);
* **the trace-of-outer-product bridge** — `LF2.trace_outer_mul_eq_inner`, which is about
  `LF2.outerProduct` and so is not Cat-1 material at all.

A file like this earns its keep only while everything in it is genuinely homeless, so the
exclusions are part of its content.

References: the consumers listed in `specs/BACKLOG.md` #146 (D); `scripts/check-duplicates.sh`;
`specs/BACKLOG.md` #146, ~~#145~~.
-/

@[expose] public section

open scoped ComplexConjugate

namespace Matrix

/-- **An isometry of matrices induces a norm-preserving map.** `‖Aψ‖² = re⟪Aψ, Aψ⟫ =
re⟪ψ, Aᴴ A ψ⟫ = ‖ψ‖²`, through the matrix-operator adjoint bridge.

`A` need not be square: `Aᴴ A = 1` on the source is all that is used, so this covers a dilation
into a larger space, which is the use that first wanted it. -/
lemma norm_toEuclideanLin_of_isom {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix κ ι ℂ} (hA : Aᴴ * A = 1)
    (ψ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin A ψ‖ = ‖ψ‖ := by
  have hinner : inner ℂ (Matrix.toEuclideanLin A ψ) (Matrix.toEuclideanLin A ψ)
      = inner ℂ ψ ψ := by
    rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A),
      show (Matrix.toEuclideanLin A).adjoint = Matrix.toEuclideanLin Aᴴ from
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm,
      show Matrix.toEuclideanLin Aᴴ (Matrix.toEuclideanLin A ψ)
          = Matrix.toEuclideanLin (Aᴴ * A) ψ from by
        simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply],
      hA,
      show Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) = LinearMap.id from
        Matrix.toLpLin_one 2,
      LinearMap.id_apply]
  have hsq : ‖Matrix.toEuclideanLin A ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- **`toEuclideanLin` turns matrix multiplication into composition**, applied to a vector.

⚠️ A specialisation: `@[simp] Matrix.toLpLin_mul_same` is the same fact as an equality
of maps, and this is it applied. Five layers wrote the applied form themselves. -/
lemma toEuclideanLin_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (A * B) v
      = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

end Matrix

namespace EuclideanSpace

variable {ι : Type*}

/-- A computational-basis vector is nonzero.

⚠️ A specialisation of `PiLp.single_eq_zero_iff`, not a new fact. It is here because three layers
each wrote their own by three different proofs: `LF5.single_one_ne_zero`,
`LF4.cpBasisVec_ne_zero` and `RecordLayer.single_ne_zero'`. -/
lemma single_one_ne_zero [DecidableEq ι] (i : ι) :
    (EuclideanSpace.single i (1 : ℂ)) ≠ 0 := fun h =>
  one_ne_zero ((PiLp.single_eq_zero_iff 2 i).mp h)

/-- **The inner product against a basis vector is that coordinate**, over any index type.

⚠️ A specialisation of `EuclideanSpace.inner_single_left`. It had four copies — `Fin 4` twice,
`Fin 8`, and the dilated `Fin N × ι` of `LF4/POVMVolume.lean` — of which the duplicate scan could
group only the two that shared a type. -/
lemma normSq_inner_single [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (i : ι) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp i‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

end EuclideanSpace

namespace Complex

/-- The inner product of two real scalars, inside `ℂ`.

⚠️ A specialisation of `RCLike.inner_apply` with `Complex.conj_ofReal`. Two contextuality files
wrote it independently, as `cplx_scalar_inner` and `mp_scalar_inner`, with the same proof. -/
lemma inner_ofReal_ofReal (a b : ℝ) : (inner ℂ ((a : ℂ)) ((b : ℂ)) : ℂ) = ((a * b : ℝ) : ℂ) := by
  rw [RCLike.inner_apply, Complex.conj_ofReal]; push_cast; ring

end Complex

end
