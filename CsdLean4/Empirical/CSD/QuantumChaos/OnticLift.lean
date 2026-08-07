/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Incubator.QuantumChaos.FloquetInterface
public import CsdLean4.LF4.ManyToOnePillars

/-!
# The ontic lift of a Floquet evolution (quantum-chaos workstream, H3)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

The "admits an ontic lift under stated hypotheses" clause of the §H3 pilot:
every unitary-generated Floquet step (`FloquetEvolution.ofUnitary U` — one of
the exactly two classes `wigner_rigidity` allows) lifts to a Liouville-
preserving step on the ontic sector `Σ = ℂℙ^{N-1} × T²` (`LF4.KSigma`), whose
projection is the interface's ray dynamics.

* `floquetOnticStep U` — the Σ-level step `(p, θ) ↦ (U • p, θ)`: the ray is
  rotated, the fibre rides along. Definitionally the time-1 flow of the
  constant-family `manyToOneSetup`, so measure preservation is inherited, not
  re-proved (`floquetOnticStep_measurePreserving`).
* `ofUnitary_projStep_smul` — the interface's ray step for `ofUnitary U` IS
  the `U • ·` action on `ℂℙ^{N-1}`.
* ★ `floquetOnticStep_lifts` / `floquetOnticStep_iterate_lifts` — the lift
  equations: `π ∘ Φ = projStep ∘ π`, and for every `n`,
  `π ∘ Φ^[n] = projIterate n ∘ π` — the ontic step projects to the interface's
  ray dynamics, period by period.

Stated hypotheses, honestly: the step is unitary-generated (`ofUnitary U` on
`Fin N`; the kicked-Ising model's product index reaches this via reindexing,
an §H follow-up), and the lift presented is the canonical fibre-fixing one —
existence, not uniqueness. Cross-references: `specs/external-library-map.md`
(the workstream architecture), `specs/future-work.md` (long-horizon rows),
`LF4/ManyToOnePillars.lean` (the reused sector machinery).
-/

@[expose] public section

open MeasureTheory
open scoped LinearAlgebra.Projectivization

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4

variable {N : ℕ}

/-- The ontic (Σ-level) one-period step of a unitary-generated Floquet
evolution: rotate the ray, fix the fibre. Definitionally the time-1 flow of
the constant-family `manyToOneSetup`. -/
noncomputable def floquetOnticStep (U : Matrix.unitaryGroup (Fin N) ℂ) :
    KSigma N → KSigma N :=
  fun x => (U • x.1, x.2)

/-- The ontic step preserves the Liouville measure `kMuL = μ_FS ⊗ vol` —
inherited from the constant-family `manyToOneSetup`'s flow, not re-proved. -/
theorem floquetOnticStep_measurePreserving [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    MeasurePreserving (floquetOnticStep U) (kMuL p₀) (kMuL p₀) :=
  (manyToOneSetup (fun _ => U) p₀).flow_preserves_volume 1

/-- Iterates of the ontic step preserve the Liouville measure. -/
theorem floquetOnticStep_iterate_measurePreserving [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) (n : ℕ) :
    MeasurePreserving ((floquetOnticStep U)^[n]) (kMuL p₀) (kMuL p₀) :=
  (floquetOnticStep_measurePreserving U p₀).iterate n

/-- The interface's ray step for `ofUnitary U` is the `U • ·` action on
`ℂℙ^{N-1}` (bridging `projMap` of the adapter's isometry to the corpus's
`MulAction`). -/
theorem ofUnitary_projStep_smul (U : Matrix.unitaryGroup (Fin N) ℂ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (FloquetEvolution.ofUnitary U).projStep p = U • p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [FloquetEvolution.projStep, Projectivization.projMap_mk,
      Projectivization.smul_mk_eq_mk_toEuclideanLin U hv,
      Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, FloquetEvolution.ofUnitary_step_apply]⟩

/-- ★ **The lift equation**: the ontic step projects to the interface's ray
dynamics — `π (Φ x) = projStep (π x)` with `π = Prod.fst`. -/
theorem floquetOnticStep_lifts (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : KSigma N) :
    (floquetOnticStep U x).1 = (FloquetEvolution.ofUnitary U).projStep x.1 :=
  (ofUnitary_projStep_smul U x.1).symm

/-- The iterated ray dynamics is iterated smul. -/
theorem ofUnitary_projIterate_smul (U : Matrix.unitaryGroup (Fin N) ℂ)
    (n : ℕ) (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (FloquetEvolution.ofUnitary U).projIterate n p = (U • ·)^[n] p := by
  induction n with
  | zero => rw [FloquetEvolution.projIterate_zero]; rfl
  | succ n ih =>
    rw [FloquetEvolution.projIterate_succ, Function.comp_apply, ih,
      Function.iterate_succ_apply', ofUnitary_projStep_smul]

/-- ★ **The iterated lift equation**: for every period count `n`,
`π (Φ^[n] x) = projIterate n (π x)` — the ontic dynamics projects to the
interface's ray dynamics, period by period. -/
theorem floquetOnticStep_iterate_lifts (U : Matrix.unitaryGroup (Fin N) ℂ)
    (n : ℕ) (x : KSigma N) :
    ((floquetOnticStep U)^[n] x).1
      = (FloquetEvolution.ofUnitary U).projIterate n x.1 := by
  rw [ofUnitary_projIterate_smul]
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

end CSD.Empirical.QuantumChaos
