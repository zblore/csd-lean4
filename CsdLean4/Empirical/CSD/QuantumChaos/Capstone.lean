/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.RecordPersistence
public import CsdLean4.Incubator.QuantumChaos.KickedIsingPilot

/-!
# The quantum-chaos pilot capstone (H3)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

The §H3 pilot statement, as one citable closure: *a repeated
finite-dimensional unitary evolution preserves global information, may change
restricted accessibility, induces projective dynamics, admits an ontic lift
under stated hypotheses, and preserves a formed record when the record sector
is invariant.*

`FloquetPilotClosure U p₀` bundles the four universal clauses for any
unitary-generated step (fields quantified over all period counts `n`), and
`floquetPilotClosure` discharges it for EVERY unitary `U` and base point `p₀`
— existence by construction, on the corpus's own sector machinery. The
existential clause ("MAY change restricted accessibility") is witnessed
separately by the concrete model: ★ `kickedIsing_changes_marginal`
(`Incubator/QuantumChaos/KickedIsingPilot.lean`) — at kick angle `π/2` the
two-qubit kicked-Ising step moves the reduced first-qubit state while every
global overlap is exactly invariant.

Like the corpus's other capstones, this is a **witness/feature index over the
named constituents** (a consistency closure), not a uniqueness or emergence
claim; the constituent theorems are the citable content. Scope: the ontic
lift is the canonical fibre-fixing one on `KSigma N` for `Fin N`-indexed
steps; record persistence is under the product-form (uncoupled) hypothesis —
coupled post-record driving is the thread's open continuation. See
`specs/external-library-map.md` §H and `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory
open scoped LinearAlgebra.Projectivization

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4

variable {N : ℕ}

/-- **The pilot closure**: the four universal clauses of the §H3 statement
for a unitary-generated Floquet evolution, at every period count. -/
structure FloquetPilotClosure [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) : Prop where
  /-- Global information is preserved: every overlap is an exact invariant of
  every period count. -/
  info_preserved : ∀ (n : ℕ) (u v : EuclideanSpace ℂ (Fin N)),
    (inner ℂ ((FloquetEvolution.ofUnitary U).iterate n u)
      ((FloquetEvolution.ofUnitary U).iterate n v) : ℂ) = inner ℂ u v
  /-- Projective dynamics is induced, transition-probability preserving at
  every period count (the `wigner_rigidity` hypothesis). -/
  projective : ∀ n : ℕ,
    Projectivization.TransProbPreserving
      ((FloquetEvolution.ofUnitary U).projIterate n)
  /-- The ontic lift preserves the Liouville measure at every period count. -/
  ontic_measure : ∀ n : ℕ,
    MeasurePreserving ((floquetOnticStep U)^[n]) (kMuL p₀) (kMuL p₀)
  /-- The ontic lift projects to the ray dynamics, period by period. -/
  ontic_projects : ∀ (n : ℕ) (x : KSigma N),
    ((floquetOnticStep U)^[n] x).1
      = (FloquetEvolution.ofUnitary U).projIterate n x.1
  /-- Formed records persist surely under uncoupled post-record driving:
  every record cylinder is set-invariant at every period count. -/
  records_persist : ∀ (Rec : Type) (S : Set Rec) (n : ℕ),
    (floquetRecordStep U Rec)^[n] ⁻¹' (Prod.snd ⁻¹' S) = Prod.snd ⁻¹' S

/-- ★★ **The pilot closure holds for every unitary-generated Floquet
evolution** — the §H3 vertical result, discharged on the corpus's own sector
machinery. The accessibility-change clause is witnessed by the concrete
model: `kickedIsing_changes_marginal`. -/
theorem floquetPilotClosure [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    FloquetPilotClosure U p₀ where
  info_preserved n u v :=
    (FloquetEvolution.ofUnitary U).inner_iterate_iterate n u v
  projective n :=
    (FloquetEvolution.ofUnitary U).projIterate_transProbPreserving n
  ontic_measure n :=
    floquetOnticStep_iterate_measurePreserving U p₀ n
  ontic_projects n x :=
    floquetOnticStep_iterate_lifts U n x
  records_persist _Rec S n :=
    floquetRecordStep_record_invariant U S n

end CSD.Empirical.QuantumChaos
