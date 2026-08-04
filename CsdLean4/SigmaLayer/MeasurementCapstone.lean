/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.UnifiedArena
public import CsdLean4.SigmaLayer.RotatedSwap
public import CsdLean4.SigmaLayer.JoinClosure
public import CsdLean4.SigmaLayer.PointerBorn
public import CsdLean4.SigmaLayer.PointerGeneration

/-!
# SigmaLayer/MeasurementCapstone: one theorem for projective measurement dynamics

**Category:** capstone — the second external review's step 4, and the consolidation the
closure count was asking for.

## Why another capstone — and why this is the last one for this layer

The corpus grew tranche by tranche, and each tranche earned its own closure so its claims
were citable the day they landed: `unifiedArenaClosure` (rank-one, one arena),
`RotatedSwapClosure`/`measurement_covariance` (every apparatus basis),
`joinWitness_blockLuders` (degenerate Lüders on the projective join), and
`smoothWitnessClosure` (the smooth-Hamiltonian horn). Four closures is the *symptom* of that
history, not a design. This module is the *cure*: **one Prop bundling all four**, so that
"CSD reconstructs projective measurement dynamically" is henceforth a single citation —
`projectiveMeasurementCapstone` — rather than a conjunction scattered over four modules. The
constituent closures remain in place as the construction record and for pin stability; new
prose should cite this one.

## What the capstone asserts, per field

For every dimension, Hermitian generator, base point, and unit preparation:

* `rank_one` — one arena carries isolated Schrödinger dynamics **and** the complete
  rank-one measurement reconstruction (records created/exclusive/persistent, dynamical
  Born, rank-one Lüders, i.i.d. frequencies, mixed states), one Liouville measure family.
* `every_basis` — the full six-fact measurement closure holds for **every** orthonormal
  apparatus basis and every preparation: the computational basis is a parameter, not
  preferred structure of `Σ`.
* `degenerate` — for **every** block structure, the **complete degenerate package on one
  protocol** (`DegenerateMeasurementClosure`, `JoinClosure.lean`): ready/record creation/
  exclusivity/persistence, Liouville preservation, the coarse dynamical Born mass
  (calibration-independent), and the ψ-dependent degenerate Lüders update — the demand
  `swap_not_blockLuders` proved impossible for fixed ray-level calibrations **on blocks of
  dimension ≥ 2** (*Corrected 2026-08-04 (codebase audit).* — that hypothesis, `j₁ ≠ j₂` with `b j₁ = b j₂`, was omitted here;
  at rank one the swap witness *does* satisfy the demand, which is `swap_luders_born`)
  (*upgraded
  from bare `BlockLudersObligation` 2026-08-03, fourth external review*).
* `smooth` — the smooth horn exists at every `ε`: a witness that is jointly continuous in
  time and state, with a positive-measure ready state and the `ε`-Born sandwich
  (`SmoothWitnessClosure` on the canonical moment-map context). *Its Schrödinger generation
  is the separate `generation` field below.* ⚠️ *Corrected 2026-08-04 (codebase audit):
  this bullet credited
  `SmoothWitnessClosure` with generation, which the very next bullet says it does not
  contain — that closure predates brick 5 and has no generator field.*
* `generation` — the smooth horn's Schrödinger equation itself: at **every** time the
  ramped propagator satisfies the ODE with the explicit Hermitian generator `pointerHeff w`
  and the rate factor `smoothTransition′(t)`, for every weight vector (*field added 2026-08-03, fourth external
  review: `SmoothWitnessClosure` predates brick 5 and does not contain the generation
  theorem — now a capstone field rather than a satellite*).

⚠️ **Honest scope.** The fields quantify over *different witnesses* — that is the
multi-horn framing (author decision 2026-08-03, `docs/TOUR.md` §"Which horn is the right
one?"), not an accident: exact **everywhere**-correlated records and continuous dynamics
are jointly impossible (`no_everywhere_correlation`), so the capstone asserts each horn
where it lives. (Since that decision the fork has grown a third horn —
`NullSeamWitness.lean` — making it a **trilemma**: seams, `ε`-Born, or Dirac calibration.
This capstone indexes the first two; the third is stated on its own closure.) It indexes the layer's closures; it does not claim one witness carries all
of them. The `generation` field is **fibrewise** Schrödinger — the joint-arena
back-reacting flow is the recorded research row (`PointerGeneration.lean` honest-scope,
fourth review). Mixed *preparations* landed separately (`MixedSwap.lean`), as did POVM /
instrument dynamics (`PovmDynamics.lean`, 2026-08-03 — the "recorded extension" note that
previously stood here is discharged) and the outcome-conditioned mixed update
(`MixedLuders.lean`, same day: `mixed_post_bayes`, `mixed_luders_followup` — *the stale
"remains open" note that stood here is discharged, fifth review*). The `smooth` field is
stated as `Nonempty` because `SmoothWitnessClosure` carries data (its protocol), keeping
this capstone a `Prop`.

## References

`specs/BACKLOG.md` (the capstone row — this discharges it); second external review
2026-08-02 (step 4); `specs/reconstruction-status.md` §2a. Constituents:
`SigmaLayer/UnifiedArena.lean`, `RotatedSwap.lean`, `JoinLuders.lean`, `PointerBorn.lean`.
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : LF4.CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)

/-- ★★★ **The projective-measurement capstone**: rank-one on one arena, every apparatus
basis, degenerate blocks, and the smooth horn — the corpus's four measurement closures as
one `Prop`. -/
structure ProjectiveMeasurementCapstone : Prop where
  /-- One arena: isolated Schrödinger dynamics + the complete rank-one reconstruction. -/
  rank_one : UnifiedArenaClosure H hH p₀ ψ hψ0
  /-- Every orthonormal apparatus basis, every preparation: the six-fact closure. -/
  every_basis : ∀ (bON : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (φ : EuclideanSpace ℂ (Fin (M + 1))), RotatedSwapClosure bON φ
  /-- Every block structure: the complete degenerate package on one protocol —
  ready/record/exclusivity/persistence, Liouville, the coarse dynamical Born mass, and
  ψ-dependent degenerate Lüders (upgraded from bare `BlockLudersObligation`, 2026-08-03). -/
  degenerate : ∀ {K : ℕ} (b : Fin (M + 1) → Fin K), DegenerateMeasurementClosure b ψ
  /-- The smooth horn, at every `ε`: jointly continuous record dynamics with a
  positive-measure ready state and the `ε`-Born sandwich, on the canonical moment-map
  context. (Generation is the separate `generation` field — `SmoothWitnessClosure` has no
  generator field; wording corrected 2026-08-04.) -/
  smooth : ∀ {ε δ : ℝ}, 0 < ε → 0 < δ → δ ≤ 1 / 2 →
    Nonempty (SmoothWitnessClosure (momentContext (M + 1)) ε δ)
  /-- The generation theorem as a field: at **every** time the ramped propagator satisfies
  the Schrödinger ODE with the explicit Hermitian generator `pointerHeff w`, for every
  weight vector — hence at every ontic point of the smooth witness. *Strengthened 2026-08-04
  (B1b): the ramp is now `C^∞`, so the open-window restriction is gone; the price is the
  rate factor `smoothTransition′(t)`, and outside `[0,1]` it vanishes so the ODE reads
  `U̇ = 0` — persistence as an ODE.* Fibrewise by design; the joint-arena flow is A1/A2. -/
  generation : ∀ {K : ℕ} (w : Fin K → ℝ) (s t : ℝ),
    HasDerivAt (fun u => couplingUAt (pointerRamp u - pointerRamp s) w)
      (deriv Real.smoothTransition t •
        (couplingUAt (pointerRamp t - pointerRamp s) w * ((-Complex.I) • pointerHeff w))) t

/-- ★★★ **The capstone holds** — for every Hermitian generator, base point, and unit
preparation. One citation for the dynamical reconstruction of projective measurement. -/
theorem projectiveMeasurementCapstone (hψ : ‖ψ‖ = 1) :
    ProjectiveMeasurementCapstone H hH p₀ ψ hψ0 where
  rank_one := unifiedArenaClosure H hH p₀ ψ hψ0 hψ
  every_basis := measurement_covariance
  degenerate := fun b => degenerateMeasurementClosure b ψ
  smooth := fun hε hδpos hδ => ⟨smoothWitnessClosureCanonical hε hδpos hδ⟩
  generation := fun w s t => rampedU_schrodinger w s t

end CSD.RecordLayer
