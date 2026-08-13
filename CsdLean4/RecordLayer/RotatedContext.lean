/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology

/-!
# SigmaLayer/RotatedContext: context fields in an arbitrary orthonormal basis

**Category:** record layer / dynamical measurement (the first unitary-covariance step).

`momentContext N` is the context field of an apparatus measuring in the *standard* basis. This
module produces the context field of an apparatus measuring in **any** orthonormal basis `b`:

  `basisContext b` — rates are the moment map read in `b`-coordinates, via the projective
  coordinate change `basisCoord b` induced by the isometry `ψ ↦ b.repr ψ`.

The point (`basisContext_rate_mk`): at a unit preparation `ψ`, the rate of outcome `i` is
`‖⟨b i, ψ⟩‖²` — the Born weight **in the rotated basis**. Since `csd_sequential_born`
(`Empirical/CSD/SequentialMeasurement.lean`) holds for *any* context field, this immediately
extends the sequential-measurement layer to cross-basis follow-ups: measure in the computational
basis, then read the collapsed state in any basis `b`. That is the missing piece for
intercept-resend eavesdropping (`Empirical/CSD/Crypto/BB84Sequential.lean`), where Eve's
computational-basis measurement is followed by Bob's conjugate-basis read.

## Why this is the unitary-covariance seed

The recorded unitary-covariance extension asks for the full equivariance
`rate (U • p) = rate p ∘ σ(U)` of the measurement layer under the projective unitary group. This
module builds the *object* that extension quantifies over — the rotated context — and proves its
`ContextField` obligations (measurability via `Projectivization.mapOfInjective_continuous`, the
simplex constraints via transport along the isometry). *(Addendum 2026-08-02: the equivariance
law itself has since landed — `SigmaLayer/RotatedSwap.lean`, `measurement_covariance`.)*

## References

`SigmaLayer/GlobalBasin.lean` (`ContextField`, `momentContext`, `globalBasin_prob`);
`Mathlib/LinearAlgebra/Projectivization/Topology.lean` (`mapOfInjective_continuous` — the staged
continuity lemma); `LF4/MomentMap.lean` (`momentMap_mk_eq_inner_sq`, `measurable_momentMap`);
`Empirical/CSD/SequentialMeasurement.lean` (the consumer); `specs/BACKLOG.md` (unitary
covariance); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD.RecordLayer

variable {N : ℕ}

/-- If `ψ ≠ 0` then its basis representation is nonzero — the coordinate isometry has trivial
kernel. -/
lemma repr_ne_zero (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (h : ψ ≠ 0) : b.repr ψ ≠ 0 :=
  fun h0 => h (b.repr.map_eq_zero_iff.mp h0)

/-- The projective coordinate change induced by an orthonormal basis `b`: the descent of the
isometry `ψ ↦ b.repr ψ` to `ℂℙ^{N−1}`. -/
noncomputable def basisCoord (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    LF4.CPN N → LF4.CPN N :=
  Projectivization.map b.repr.toLinearEquiv.toLinearMap b.repr.toLinearEquiv.injective

lemma basisCoord_mk (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) :
    basisCoord b (Projectivization.mk ℂ ψ hψ0)
      = Projectivization.mk ℂ (b.repr ψ) (repr_ne_zero b hψ0) :=
  Projectivization.map_mk b.repr.toLinearEquiv.toLinearMap b.repr.toLinearEquiv.injective ψ hψ0

lemma continuous_basisCoord (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Continuous (basisCoord b) :=
  Projectivization.mapOfInjective_continuous b.repr.toLinearEquiv.toLinearMap
    b.repr.toLinearEquiv.injective b.repr.continuous

/-- **The rotated context field**: the context of an apparatus measuring in the orthonormal
basis `b`. Rates are the moment map read in `b`-coordinates; the `ContextField` obligations
transport along the coordinate isometry. `basisContext` of the standard basis has the same
rates as `momentContext` (`basisContext_basisFun_rate`, below). -/
noncomputable def basisContext (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ContextField N where
  rate p i := LF4.momentMap (basisCoord b p) i
  measurable_rate i := (LF4.measurable_momentMap i).comp (continuous_basisCoord b).measurable
  nonneg _p i := LF4.momentMap_nonneg _ i
  sum_one _p := LF4.momentMap_sum_eq_one _

@[simp] theorem basisContext_rate (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (p : LF4.CPN N) : (basisContext b).rate p = LF4.momentMap (basisCoord b p) := rfl

/-- **★ The rotated rate is the rotated Born weight.** At a unit preparation `ψ`, the
basis-`b` context assigns outcome `i` the weight `‖⟨b i, ψ⟩‖²` — the Born rule in the rotated
basis, obtained by transport rather than re-derivation. -/
theorem basisContext_rate_mk (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin N) :
    (basisContext b).rate (Projectivization.mk ℂ ψ hψ0) i
      = ‖(inner ℂ (b i) ψ : ℂ)‖ ^ 2 := by
  have hnorm : ‖b.repr ψ‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hψ]
  rw [basisContext_rate, basisCoord_mk,
    LF4.momentMap_mk_eq_inner_sq (b.repr ψ) (repr_ne_zero b hψ0) hnorm i,
    EuclideanSpace.inner_single_left, map_one, one_mul, OrthonormalBasis.repr_apply_apply]

/-- **The standard basis reproduces `momentContext`**: the rotated construction at
`EuclideanSpace.basisFun` has literally the moment map's rates — the consistency claim, as a
theorem rather than prose. -/
theorem basisContext_basisFun_rate (p : LF4.CPN N) (i : Fin N) :
    (basisContext (EuclideanSpace.basisFun (Fin N) ℂ)).rate p i
      = (momentContext N).rate p i := by
  rw [basisContext_rate, momentContext_rate]
  suffices h : basisCoord (EuclideanSpace.basisFun (Fin N) ℂ) p = p by rw [h]
  conv_lhs => rw [← p.mk_rep]
  conv_rhs => rw [← p.mk_rep]
  rw [basisCoord_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨1, by
    rw [one_smul]
    exact (PiLp.ext fun j => rfl :
      (EuclideanSpace.basisFun (Fin N) ℂ).repr p.rep = p.rep).symm⟩

end CSD.RecordLayer
