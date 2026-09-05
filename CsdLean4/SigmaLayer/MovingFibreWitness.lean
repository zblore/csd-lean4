/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ApproxProjectability
public import CsdLean4.Mathlib.Dynamics.CatMapWitness

/-!
# SigmaLayer/MovingFibreWitness: an `ε > 0` projectable Hamiltonian, and a fibre that moves

**Category:** 7-SigmaLayer (the projective-sector layer, Paper C — the A5 approximate regime).

`EpsProjectable` is Σ1's central object, and until now **every instance of it had `ε = 0`**
(`diagOnticEnergy`, `RecordLayer/ApproxProjectability.lean`; the moment-map signature,
`RecordLayer/HamiltonianSignature.lean`). An interface whose only inhabitants sit at the degenerate
parameter is not populated in the sense that matters: the `ε = 0` case is exactly "factors through
`π`" (`epsProjectable_zero_iff`), so those instances say nothing about the approximate regime. This
module supplies the missing inhabitant.

## What is exhibited

★ `movingFibreEnergy h g ε` — the shape Paper C's approximate regime asks for, `H = h ∘ π + ε·f·g`
with the fibre profile `f = catObs/2` taken from the corpus's own hyperbolic-torus witness:

  `H (p, θ) = h p + ε · (g p · (catObs θ / 2))`

★ `movingFibreEnergy_epsProjectable` — it is `EpsProjectable` at `ε`, for every `ε ≥ 0` and every
base profile `g` bounded by one. The bound is the pointwise oscillation `|catObs θ − catObs θ'| ≤ 2`
against the `/2`.

★★ `movingFibreEnergy_not_projectable` — **and the fibre genuinely moves.** For `ε > 0` and `g p ≠ 0`
the Hamiltonian is *not* `EpsProjectable` at `0`, so it does not factor through `π`. This is the
non-vacuity that matters: without it the witness could be an `ε = 0` instance wearing a parameter,
which is precisely the defect the module exists to fix. The proof runs through `cat_nontrivial`
(`⟨f²⟩ ≠ ⟨f⟩²`): a constant fibre profile has zero variance, and `catObs` does not.

★ `catStroke` — the hyperbolic fibre map, `cat` presented on `KTorus` with the properties a fibre
stroke needs (`catStroke_measurePreserving`, `catStroke_bijective`, `catStroke_continuous`). ⚠️ It is
**hyperbolic, not a translation**, which is the point: a translation cannot decorrelate
(`not_hasCorrelationDecay_of_compactGroup`) while this map has correlations exactly zero at every
nonzero lag (`cat_hasCorrelationDecay`).

## ⚠️ Scope, and one thing the item asked for that does not typecheck

`KTorus` **is** `Torus2` — both are `AddCircle 1 × AddCircle 1` — so the cat map is literally a map
on the corpus's own fibre. No transport is needed and none is hidden.

⚠️ **`quantum_effective_shadowing` cannot be instantiated at this witness, and the plan that asked
for it was working from a wrong premise.** That theorem is about *matrices*
(`H H₀ : Matrix (Fin N) (Fin N) ℂ`, `‖H − H₀‖ ≤ ε`), whereas `EpsProjectable` is about *ontic
Hamiltonians on `KSigma N`*. The two are the same idea at different levels and the corpus has no
bridge between them; supplying one is a separate piece of work, not a corollary. Nothing here
claims the shadowing bound for this witness.

⚠️ This populates the *predicate*, not the dynamics: no flow is constructed whose generator this is,
and `catStroke` is offered as an available hyperbolic fibre map rather than wired into a
`ConstraintDynamics`. What is closed is the "no `ε > 0` instance" gap
(`specs/reconstruction-status.md` §7); what is not closed is A5's approximate regime as a dynamical
statement.

## References

`RecordLayer/ApproxProjectability.lean` (`EpsProjectable`, `epsProjectable_zero_iff`,
`epsProjectable_mono`, `quantum_effective_shadowing`); `Mathlib/Dynamics/CatMapWitness.lean`
(`cat`, `catObs`, `cat_nontrivial`, `cat_hasCorrelationDecay`, `measurePreserving_cat`);
`Mathlib/Dynamics/CompactGroupNoMixing.lean` (`not_hasCorrelationDecay_of_compactGroup` — why a
translation would not do); `LF4/KahlerInstance.lean` (`KSigma`, `KTorus`);
`specs/reconstruction-status.md` §7; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace SigmaLayer

open LF4 RecordLayer

variable {N : ℕ}

/-! ### The hyperbolic fibre map -/

/-- The **hyperbolic fibre stroke**: the cat map, presented on the corpus's own fibre `KTorus`.

⚠️ Hyperbolic, deliberately. A torus *translation* provably cannot decorrelate
(`not_hasCorrelationDecay_of_compactGroup`); this map has correlations exactly zero at every nonzero
lag (`cat_hasCorrelationDecay`). Offered here as an available fibre map; it is **not** wired into a
`ConstraintDynamics`. -/
noncomputable def catStroke : KTorus → KTorus := MeasureTheory.cat

theorem catStroke_measurePreserving :
    MeasurePreserving catStroke (volume : Measure KTorus) (volume : Measure KTorus) :=
  MeasureTheory.measurePreserving_cat

theorem catStroke_bijective : Function.Bijective catStroke :=
  MeasureTheory.bijective_cat

theorem catStroke_continuous : Continuous catStroke :=
  MeasureTheory.continuous_cat

/-! ### The `ε > 0` witness -/

/-- The **moving-fibre ontic Hamiltonian**, in the shape Paper C's approximate regime asks for:
`H = h ∘ π + ε · f · g` with fibre profile `f = catObs/2` and base profile `g`. -/
noncomputable def movingFibreEnergy (h g : CPN N → ℝ) (ε : ℝ) : KSigma N → ℝ :=
  fun x => h x.1 + ε * (g x.1 * (MeasureTheory.catObs x.2 / 2))

/-- ★ **The witness is `EpsProjectable` at `ε`.** Fibre oscillation is bounded by `ε` because
`catObs` is bounded by one and the profile is halved. -/
theorem movingFibreEnergy_epsProjectable (h g : CPN N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ p, |g p| ≤ 1) :
    EpsProjectable (movingFibreEnergy h g ε) ε := by
  intro p θ θ'
  have hcat : |MeasureTheory.catObs θ - MeasureTheory.catObs θ'| ≤ 2 := by
    have h1 := MeasureTheory.abs_catObs_le_one θ
    have h2 := MeasureTheory.abs_catObs_le_one θ'
    calc |MeasureTheory.catObs θ - MeasureTheory.catObs θ'|
        ≤ |MeasureTheory.catObs θ| + |MeasureTheory.catObs θ'| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  have hrw : movingFibreEnergy h g ε (p, θ) - movingFibreEnergy h g ε (p, θ')
      = ε * g p * ((MeasureTheory.catObs θ - MeasureTheory.catObs θ') / 2) := by
    simp only [movingFibreEnergy]
    ring
  rw [hrw, abs_mul, abs_mul]
  have hgp : |g p| ≤ 1 := hg p
  have habs : |(MeasureTheory.catObs θ - MeasureTheory.catObs θ') / 2| ≤ 1 := by
    rw [abs_div]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    linarith [hcat]
  calc |ε| * |g p| * |(MeasureTheory.catObs θ - MeasureTheory.catObs θ') / 2|
      ≤ |ε| * 1 * 1 := by
        apply mul_le_mul _ habs (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hgp (abs_nonneg _)
    _ = ε := by rw [abs_of_nonneg hε]; ring

/-- ★★ **And the fibre genuinely moves.** For `ε > 0` at a base point where the profile does not
vanish, the witness is **not** `EpsProjectable` at `0` — equivalently, it does not factor through
`π` (`epsProjectable_zero_iff`).

This is the non-vacuity the module exists for. Without it the witness could be an `ε = 0` instance
wearing a parameter, which is exactly the defect being fixed. The proof is variance: a constant
fibre profile would give `⟨f²⟩ = ⟨f⟩²`, and `cat_nontrivial` says `catObs` does not. -/
theorem movingFibreEnergy_not_projectable (h g : CPN N → ℝ) {ε : ℝ} (hε : 0 < ε)
    {p : CPN N} (hgp : g p ≠ 0) :
    ¬ EpsProjectable (movingFibreEnergy h g ε) 0 := by
  intro hzero
  -- zero oscillation forces the fibre profile to be constant
  have hconst : ∀ θ θ' : KTorus,
      MeasureTheory.catObs θ = MeasureTheory.catObs θ' := by
    intro θ θ'
    have hle := hzero p θ θ'
    have heq : movingFibreEnergy h g ε (p, θ) = movingFibreEnergy h g ε (p, θ') := by
      have := abs_nonneg (movingFibreEnergy h g ε (p, θ) - movingFibreEnergy h g ε (p, θ'))
      have hzero' : |movingFibreEnergy h g ε (p, θ) - movingFibreEnergy h g ε (p, θ')| = 0 :=
        le_antisymm hle this
      linarith [abs_eq_zero.mp hzero']
    simp only [movingFibreEnergy] at heq
    have hne : ε * g p ≠ 0 := mul_ne_zero (ne_of_gt hε) hgp
    have h4 : ε * (g p * (MeasureTheory.catObs θ / 2))
        = ε * (g p * (MeasureTheory.catObs θ' / 2)) := add_left_cancel heq
    have h5 : (ε * g p) * MeasureTheory.catObs θ = (ε * g p) * MeasureTheory.catObs θ' := by
      linear_combination 2 * h4
    exact mul_left_cancel₀ hne h5
  -- a constant observable has zero variance; `catObs` does not
  have hc : ∀ θ : KTorus, MeasureTheory.catObs θ = MeasureTheory.catObs 0 := fun θ => hconst θ 0
  refine MeasureTheory.cat_nontrivial ?_
  have h1 : ∫ q, MeasureTheory.catObs q * MeasureTheory.catObs q
      ∂(volume : Measure MeasureTheory.Torus2)
      = MeasureTheory.catObs 0 * MeasureTheory.catObs 0 := by
    simp_rw [hc]
    simp
  have h2 : ∫ q, MeasureTheory.catObs q ∂(volume : Measure MeasureTheory.Torus2)
      = MeasureTheory.catObs 0 := by
    simp_rw [hc]
    simp
  rw [h1, h2]
  ring

end SigmaLayer
end CSD
