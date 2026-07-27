/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.BornFS
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# LF4/BlochProjection: the general-axis Born weight on `ℂℙ^{N-1}` (context-fixed qubit, A7)

**Category:** 2-LF4 (Kähler / moment-map layer — sphere-measure infrastructure).

The **general-axis Bloch projection** `blochProj a p = |⟨a, rep p⟩|² / ‖rep p‖²`: for a unit axis
`a` and a projective point `p = [φ]`, this is the Born weight `|⟨a|φ⟩|²` of the state along `a`.
It generalises `momentMap p i = |⟨eᵢ|φ⟩|²` (the reference-axis case `a = eᵢ`) to an arbitrary
axis, and is the shared foundation for the context-fixed qubit measurement (Paper C A7,
`specs/record-layer-plan.md` §2): the hemispheres `H±(n)` are cut by `blochProj n`, and the spread
density from a prep `ψ` is a function of `blochProj ψ`.

Key facts, all foundational-triple, no `sorry`:
* `blochProj_mk` — scale-invariance (well-defined on the projective point);
* `toEuclideanLin_unitary_norm` — the unitary matrix action is an isometry (from
  `Projectivization.inner_toEuclideanLin_unitary`);
* `blochProj_smul` — `U(N)`-equivariance: `blochProj a (U • p) = |⟨a, U·rep p⟩|² / ‖rep p‖²`;
* `blochProj_measurable` — Borel measurability (mirrors `momentMap_measurable`).

## References
`LF4/MomentMap.lean` (`momentMap`, `momentMap_mk`, `momentRatio_smul` — the reference-axis case);
`LF4/BornFS.lean` (`momentMap_measurable`); `Thermo/CanonicalTypicality.lean` (`smul_eq_mk`);
`specs/record-layer-plan.md` §2 (the qubit context-fixed crux).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

variable {N : ℕ}

/-- **General-axis Bloch projection.** `blochProj a p = |⟨a, rep p⟩|² / ‖rep p‖²` — for a unit axis
`a`, the Born weight `|⟨a|φ⟩|²` of the state `p = [φ]` along `a`. Well-defined on the projective
point (scale-invariant; see `blochProj_mk`). Generalises `momentMap p i` (the case `a = eᵢ`). -/
noncomputable def blochProj (a : EuclideanSpace ℂ (Fin N)) (p : CPN N) : ℝ :=
  ‖inner ℂ a p.rep‖ ^ 2 / ‖p.rep‖ ^ 2

/-- The ratio `|⟨a, c•v⟩|²/‖c•v‖²` is invariant under nonzero rescaling of `v` (projective
well-definedness of `blochProj`). -/
lemma blochRatio_smul (a : EuclideanSpace ℂ (Fin N)) (c : ℂ) (hc : c ≠ 0)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖inner ℂ a (c • v)‖ ^ 2 / ‖c • v‖ ^ 2 = ‖inner ℂ a v‖ ^ 2 / ‖v‖ ^ 2 := by
  rw [inner_smul_right, norm_mul, norm_smul, mul_pow, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]

/-- **Scale-invariance / representative form:** `blochProj a [ψ] = |⟨a, ψ⟩|² / ‖ψ‖²` for any nonzero
representative `ψ` of the projective point. -/
lemma blochProj_mk (a ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0) :
    blochProj a (Projectivization.mk ℂ ψ hψ) = ‖inner ℂ a ψ‖ ^ 2 / ‖ψ‖ ^ 2 := by
  obtain ⟨u, hu⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ ψ hψ).rep ψ
        (Projectivization.rep_nonzero _) hψ).mp (Projectivization.mk_rep _)
  unfold blochProj
  rw [← hu]
  simp only [Units.smul_def]
  exact blochRatio_smul a (↑u) (Units.ne_zero u) ψ

/-- For a unit axis and unit representative, `blochProj a [ψ] = |⟨a, ψ⟩|²`. -/
lemma blochProj_mk_unit (a ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    blochProj a (Projectivization.mk ℂ ψ hψ0) = ‖inner ℂ a ψ‖ ^ 2 := by
  rw [blochProj_mk, hψ, one_pow, div_one]

/-- Each Bloch projection is nonnegative. -/
lemma blochProj_nonneg (a : EuclideanSpace ℂ (Fin N)) (p : CPN N) : 0 ≤ blochProj a p :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The unitary matrix action is an isometry:** `‖U·v‖ = ‖v‖`, from
`Projectivization.inner_toEuclideanLin_unitary` at `x = y = v`. -/
lemma toEuclideanLin_unitary_norm (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin U.val) v‖ = ‖v‖ := by
  have h := Projectivization.inner_toEuclideanLin_unitary (N := N) U v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖(Matrix.toEuclideanLin U.val) v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  have := norm_nonneg ((Matrix.toEuclideanLin U.val) v)
  nlinarith [norm_nonneg v, sq_nonneg (‖(Matrix.toEuclideanLin U.val) v‖ - ‖v‖)]

/-- **`U(N)`-equivariance of the Bloch projection.** `blochProj a (U • p) = |⟨a, U·rep p⟩|² /
‖rep p‖²`: pushing the point by `U` acts as `U` on the representative, and `U` is an isometry so the
denominator is unchanged. -/
lemma blochProj_smul [NeZero N] (a : EuclideanSpace ℂ (Fin N))
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p : CPN N) :
    blochProj a (U • p)
      = ‖inner ℂ a ((Matrix.toEuclideanLin U.val) p.rep)‖ ^ 2 / ‖p.rep‖ ^ 2 := by
  conv_lhs => rw [← p.mk_rep]
  rw [Matrix.UnitaryGroup.smul_mk_eq_mk U p.rep p.rep_nonzero, blochProj_mk,
    toEuclideanLin_unitary_norm]

/-- **Borel measurability of the Bloch projection** (mirrors `momentMap_measurable`). -/
theorem blochProj_measurable (a : EuclideanSpace ℂ (Fin N)) :
    Measurable (fun p : CPN N => blochProj a p) := by
  borelize (EuclideanSpace ℂ (Fin N))
  rw [Projectivization.measurable_iff_measurable_comp_mk']
  have hcomp : (fun p : CPN N => blochProj a p) ∘ (Projectivization.mk' ℂ)
      = fun w : { v : EuclideanSpace ℂ (Fin N) // v ≠ 0 } =>
          ‖inner ℂ a (w : EuclideanSpace ℂ (Fin N))‖ ^ 2
            / ‖(w : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
    funext w
    show blochProj a (Projectivization.mk ℂ (w : EuclideanSpace ℂ (Fin N)) w.2) = _
    rw [blochProj_mk]
  rw [hcomp]
  refine Measurable.div ?_ ?_
  · exact ((((continuous_const (y := a)).inner continuous_subtype_val)).norm.pow 2).measurable
  · exact ((continuous_subtype_val.norm).pow 2).measurable

end CSD.LF4
