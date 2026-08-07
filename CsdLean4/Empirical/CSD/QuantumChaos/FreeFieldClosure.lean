/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FreeFieldFloquet
public import CsdLean4.Empirical.CSD.QuantumChaos.Capstone

/-!
# The free field reaches the pilot closure (CV-5, CSD side)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

`CV/FreeFieldFloquet.lean` built the free field's stroboscopic step
(`freeFieldU`, a diagonal-phase unitary provably equal to
`exp (-(iτ) • H_field)`). This module carries it into the §H3 ontic
machinery, which is stated over `Fin`-indexed unitaries:

* `card_fieldConfig` — the configuration space has `N ^ K` points.
* `freeFieldUFin` — the free-field step reindexed to
  `Fin (card (FieldConfig K N))` along `Fintype.equivFin` (unitarity by
  `reindex_mem_unitaryGroup`, the same seam the kicked-Ising pilot used for
  `kickedIsingU₄`).
* ★ `freeField_pilotClosure` — **the CV pillar satisfies the full §H3 pilot
  closure**: exact information preservation at every period, induced
  projective dynamics, the measure-preserving ontic lift on `KSigma`, and
  sure record persistence under uncoupled post-record driving — for every
  cutoff `(K, N)`, period `τ`, and base point.

So the quantum-chaos vertical (interface → ontic lift → records) and the CV
vertical (modes → free field) meet: the same closure instance covers both
the kicked-Ising model and the free field at a cutoff. Honest scope: free
dynamics at a finite cutoff; coupled record driving is priced separately
(`RecordDegradation.lean`, `CouplingWitness.lean`), and interacting drives
are future work.

## References

`CV/FreeFieldFloquet.lean` (CV-5, the step and its exp-legitimacy);
`CV/DynamicalLocality.lean` (CV-6, the locality consequence);
`Empirical/CSD/QuantumChaos/Capstone.lean` (`FloquetPilotClosure`);
`Incubator/QuantumChaos/KickedIsingPilot.lean`
(`reindex_mem_unitaryGroup`); `specs/external-library-map.md` §H;
`specs/BACKLOG.md`; `specs/future-work.md`.
-/

@[expose] public section

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4 CSD.CV

variable {K N : ℕ}

/-- The configuration space of `K` modes at `N` levels has `N ^ K` points. -/
theorem card_fieldConfig (K N : ℕ) :
    Fintype.card (FieldConfig K N) = N ^ K := by
  simp [Fintype.card_fun]

instance [NeZero N] : NeZero (Fintype.card (FieldConfig K N)) := by
  have : Nonempty (FieldConfig K N) :=
    ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  exact ⟨Fintype.card_ne_zero⟩

/-- The free-field stroboscopic step, reindexed to
`Fin (card (FieldConfig K N))` so the `Fin N` ontic machinery (`KSigma`,
`floquetOnticStep`, the pilot closure) applies directly. -/
noncomputable def freeFieldUFin (K N : ℕ) (τ : ℝ) :
    Matrix.unitaryGroup (Fin (Fintype.card (FieldConfig K N))) ℂ :=
  ⟨Matrix.reindex (Fintype.equivFin (FieldConfig K N))
      (Fintype.equivFin (FieldConfig K N)) (freeFieldU K N τ).val,
    reindex_mem_unitaryGroup _ (freeFieldU K N τ).property⟩

/-- ★ **The CV pillar reaches the §H3 pilot closure**: the free field at any
cutoff satisfies all four universal clauses — information preservation,
induced projective dynamics, the measure-preserving ontic lift, and sure
record persistence — for every period `τ` and base point. -/
theorem freeField_pilotClosure [NeZero N] (τ : ℝ)
    (p₀ : CPN (Fintype.card (FieldConfig K N))) :
    FloquetPilotClosure (freeFieldUFin K N τ) p₀ :=
  floquetPilotClosure _ _

end CSD.Empirical.QuantumChaos
