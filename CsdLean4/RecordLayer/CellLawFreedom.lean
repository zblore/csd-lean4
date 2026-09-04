/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin
public import CsdLean4.RecordLayer.HamiltonianSignature

/-!
# RecordLayer/CellLawFreedom: the moment-map cell law is a posit, and here is why

**Category:** 7-SigmaLayer (the record layer's own foundations).

`globalBasin_born` reads the Born weights off the fibre partition at `momentContext`, and the
corpus's prose has read that as *the rates are forced by the Kähler structure*.

**In the standard symplectic reading that is true, and this module does not dispute it.** A moment
map for the `Tⁿ` action on connected `ℂℙ^{N−1}` is unique up to an additive constant; sum-one and
non-negativity pin the constant to zero. (At the form's fixed scale — the corpus normalisation
`ω u (J u) = ‖u‖²` of `IsFubiniStudyKahler`; rescaling `ω ↦ λω` readmits a family `λΦ + c`.)

**But that argument is unformalised, and what Lean verifies does not carry it.** Mathlib has no
symplectic API, so the corpus never states the moment-map equation `ι_{X_i} ω = dΦᵢ` — see the
boundary note in `LF4/MomentMap.lean`. `momentMap` is *defined* by the coordinate formula, and what
is machine-checked about it is that formula plus its symmetries. This module shows those do **not**
pin it down: `globalBasin_prob` holds for **every** `ContextField`, `momentContext` is one field
among many, and `bornRate` is a definition. Relative to the machine-checked corpus the cell law is a
**structural posit**, and the prose that cites `momentMap_mk` for "forced" is citing a
scale-invariance lemma for a claim it does not make.

This module makes that concrete rather than conceding it in prose, by exhibiting a second,
fully functioning cell law.

## What is exhibited

★ `sqContext` — the *normalised-squares* field `x ↦ x²/∑x²` composed with the moment map. It is a
`ContextField` in good standing: non-negative, normalised, measurable. It is
**torus-invariant** (★ `sqRate_phaseDiag_invariant`, inherited from
`momentMap_phaseDiag_invariant`), it **vanishes exactly where the moment map does**
(★ `sqRate_eq_zero_iff`), and — since `globalBasin_prob` is generic — it drives the whole basin
machinery, producing its own Born-like weights (★ `globalBasin_prob_sqContext`).

★★ `rate_field_not_forced_by_torus_symmetry` — and it is **not** the moment map: at the explicit
state `ψ = (2, 1, 1)` in `ℂℙ²`, whose moment coordinates are `(⅔, ⅙, ⅙)`, the normalised-squares
field gives outcome `0` the rate `8/9` where the moment map gives `⅔`.

## What this settles, and what it does not

**Settles:** torus invariance, normalisation, measurability and the support condition — the
properties the corpus actually verifies — do **not** characterise the moment map. So the step
"the rates are torus-equivariant and normalised, hence they are the moment map" is invalid;
equivariance is shared by a continuum of other fields, of which this is one. The symplectic
argument above is untouched, because `sqRate` is *not* a moment map for the torus action: no
`ι_{X_i} ω = d(sqRateᵢ)` holds. What fails is the weak package, which is the only package in Lean.

**Does not settle:** whether some *stronger* condition characterises the moment map. The natural
candidate is consistency across bases — a rate field defined for every orthogonal decomposition
and additive under merging outcomes is a frame function, and for `N ≥ 3` that is Gleason's
hypothesis (⚠️ RESIDUE(R-018)). Whether the corpus's `effect_gleason_representation` transfers (it fixes a state and
varies effects; the cell law fixes a context and varies the state) is open and is stage 2 of
`specs/cell-law-scoping.md`. ⚠️ If noncontextuality is what forces the cell law, then
"Gleason-free" is true of the *volume theorem* and false of the *choice of cell law* — a
distinction worth keeping.

⚠️ **Not a claim that nothing in the corpus distinguishes them.** Two things do. (i) The
Duistermaat–Heckman results: the moment map pushes `μ_FS` forward to the flat law on `[0,1]`
(`LF4/MomentUniform.lean`, `fs_moment_pushforward_uniform`) and to the Dirichlet law on the simplex
(`LF4/MomentDirichletN.lean`, `fs_moment_joint_dirichlet_N`); `sqRate`'s pushforward is neither.
That is a proved asymmetry — though not a characterisation (any `μ_FS`-preserving precomposition
shares a pushforward), and no record-layer selection argument currently invokes it. (ii) `bornRate`
has a flow-carved witness (`shearDeIsolationInteraction` discharges `basin_rate` from a constructed
propagator); `sqRate` has none. What selects `momentContext` in this corpus is agreement with the
Born target — which is the thing MD-1 wants *derived*, hence the posit.

**Not a defect report.** The machinery is correct and `globalBasin_born` is true. What is
corrected is an account of *why* it is true.

## References

`RecordLayer/GlobalBasin.lean` (`ContextField`, `globalBasin_prob`, `momentContext`,
`globalBasin_born`); `RecordLayer/MomentMapRace.lean` (`bornRate_eq_momentMap` — the
identification whose docstring this module qualifies); `RecordLayer/HamiltonianSignature.lean`
(`momentMap_phaseDiag_invariant`, the torus action); `LF4/MomentMap.lean` (`momentMap_nonneg`,
`momentMap_sum_eq_one`, `momentMap_mk`); `LF4/MomentUniform.lean`,
`LF4/MomentDirichletN.lean` (the Duistermaat–Heckman pushforward laws); `specs/POSITS.md` (Posit 1);
`specs/cell-law-scoping.md` (stage 2); `specs/future-work.md` ("Cell-law characterisation (stage 2)").
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace RecordLayer

open LF4

variable {N : ℕ}

/-! ### A second cell law -/

/-- The **normalised-squares rate**: `x ↦ xᵢ² / ∑ₖ xₖ²` applied to the moment coordinates.

Chosen because it shares every symmetry property the moment map is usually motivated by, and is
not the moment map. -/
noncomputable def sqRate (p : CPN N) (i : Fin N) : ℝ :=
  (momentMap p i) ^ 2 / ∑ k, (momentMap p k) ^ 2

/-- The denominator is positive: the moment coordinates are non-negative and sum to one, so they
cannot all vanish. -/
lemma sq_sum_pos (p : CPN N) : 0 < ∑ k, (momentMap p k) ^ 2 := by
  -- some coordinate is nonzero, since the coordinates sum to one
  obtain ⟨j, hj⟩ : ∃ j, momentMap p j ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑ k, momentMap p k = 0 := Finset.sum_eq_zero fun k _ => h k
    rw [momentMap_sum_eq_one] at this
    exact one_ne_zero this
  have hpos : 0 < (momentMap p j) ^ 2 := by positivity
  calc (0:ℝ) < (momentMap p j) ^ 2 := hpos
    _ ≤ ∑ k, (momentMap p k) ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (momentMap p k)) (Finset.mem_univ j)

lemma sqRate_nonneg (p : CPN N) (i : Fin N) : 0 ≤ sqRate p i :=
  div_nonneg (sq_nonneg _) (le_of_lt (sq_sum_pos p))

lemma sqRate_sum_eq_one (p : CPN N) : ∑ i, sqRate p i = 1 := by
  show (∑ i, (momentMap p i) ^ 2 / ∑ k, (momentMap p k) ^ 2) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (sq_sum_pos p))

lemma measurable_sqRate (i : Fin N) : Measurable fun p : CPN N => sqRate p i := by
  refine Measurable.div ((measurable_momentMap i).pow_const 2) ?_
  exact Finset.measurable_sum _ fun k _ => (measurable_momentMap k).pow_const 2

/-- ★ **A second cell law.** The normalised-squares field is a `ContextField` in good standing —
so every theorem `GlobalBasin.lean` proves for an arbitrary context field applies to it. -/
noncomputable def sqContext (N : ℕ) : ContextField N where
  rate := sqRate
  measurable_rate := measurable_sqRate
  nonneg := sqRate_nonneg
  sum_one := sqRate_sum_eq_one

@[simp] theorem sqContext_rate (p : CPN N) : (sqContext N).rate p = sqRate p := rfl

/-! ### It has the symmetries the moment map is motivated by -/

/-- ★ **Torus-invariant.** The diagonal phase action preserves every moment coordinate, hence the
normalised-squares field built from them. This is the property usually offered as the reason the
moment map is canonical; it does not distinguish the two fields. -/
theorem sqRate_phaseDiag_invariant (φ : Fin N → ℝ) (p : CPN N) (i : Fin N) :
    sqRate (phaseDiag φ • p) i = sqRate p i := by
  simp only [sqRate, momentMap_phaseDiag_invariant]

/-- ★ **Same support.** The rate vanishes exactly where the moment coordinate does, so the
"vanishes off the `i`-th coordinate hyperplane" condition does not distinguish them either. -/
theorem sqRate_eq_zero_iff (p : CPN N) (i : Fin N) :
    sqRate p i = 0 ↔ momentMap p i = 0 := by
  rw [sqRate, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    · exact absurd h (ne_of_gt (sq_sum_pos p))
  · intro h; left; rw [h]; ring

/-- ★ **It drives the basin machinery.** `globalBasin_prob` is generic in the context field, so the
alternative cell law produces its own weights on its own basins. This makes it a genuine
underdetermination witness *for the interface* — not a rival account of measurement: it is not
empirically adequate, giving `8/9` where Born requires `⅔`. That is the point. Empirical adequacy,
not geometry, is what picks `momentContext` out. -/
theorem globalBasin_prob_sqContext (i : Fin N) (p : CPN N) :
    epistemicMeasure p (globalBasin (sqContext N) i) = ENNReal.ofReal (sqRate p i) :=
  globalBasin_prob (sqContext N) i p


/-! ### The separation -/

/-- The witness state `(2, 1, 1)` in `ℂℙ²`, unnormalised. Rational entries deliberately: the
moment coordinates come out `(⅔, ⅙, ⅙)` with no square roots, and the two rate fields separate
there. -/
noncomputable def witState : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![2, 1, 1]

lemma witState_ne_zero : witState ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 3) => v 0) h
  simp [witState] at this

lemma norm_sq_witState : ‖witState‖ ^ 2 = 6 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [witState, Fin.sum_univ_three]
  norm_num

lemma momentMap_witState_zero :
    momentMap (Projectivization.mk ℂ witState witState_ne_zero) 0 = 2 / 3 := by
  rw [momentMap_mk witState witState_ne_zero 0, norm_sq_witState]
  simp [witState]
  norm_num

lemma momentMap_witState (i : Fin 3) :
    momentMap (Projectivization.mk ℂ witState witState_ne_zero) i
      = ![2/3, 1/6, 1/6] i := by
  rw [momentMap_mk witState witState_ne_zero i, norm_sq_witState]
  fin_cases i <;> norm_num [witState]

lemma sq_sum_witState :
    ∑ k, (momentMap (Projectivization.mk ℂ witState witState_ne_zero) k) ^ 2 = 1 / 2 := by
  simp only [momentMap_witState, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- ★★ **The cell law is not forced by the symmetries usually offered for it.**

At `[(2,1,1)] ∈ ℂℙ²` the moment map gives outcome `0` the rate `⅔`; the normalised-squares field
— torus-invariant, normalised, measurable, with the same support — gives it `8/9`. So no argument
from equivariance, normalisation and support can single out the moment map: those hypotheses hold
of both.

`momentContext` is therefore a **choice**, and the Born weights of `globalBasin_born` follow from
that choice together with the fibre-volume machinery, not from the geometry alone. What might
still characterise it — consistency across bases, i.e. a frame-function hypothesis — is stage 2
and is not claimed here. -/
theorem rate_field_not_forced_by_torus_symmetry :
    ∃ (p : CPN 3) (i : Fin 3), sqRate p i ≠ momentMap p i := by
  refine ⟨Projectivization.mk ℂ witState witState_ne_zero, 0, ?_⟩
  rw [sqRate, sq_sum_witState, momentMap_witState_zero]
  norm_num

end RecordLayer
end CSD
