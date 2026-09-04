/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.OnticLift

/-!
# Record persistence under post-record Floquet evolution (H3)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

The "preserves a formed record when the record sector is invariant" clause of
the §H3 pilot. Setting: after a record has formed, the arena factors as
`system × record`, and post-record evolution that does not couple to the
record factor acts as `Φ ×ˢ id`. Then:

* `record_cylinder_invariant` — every record cylinder (an event read off the
  record factor alone) is **set-invariant**: `(Φ ×ˢ id)⁻¹ R = R`. Not merely
  measure-preserved: the event is literally the same set, so the record
  persists surely, not just almost surely.
* `record_cylinder_iterate_invariant` — the same for every period count.
* `prodMap_iterate` — `(Φ ×ˢ id)^[n] = Φ^[n] ×ˢ id` (the record factor stays
  untouched for all time).
* `floquetRecordStep_*` — the CSD instantiation on `(KSigma N) × Rec`: the
  Floquet ontic step extended by the identity on a record factor is
  measure-preserving for `kMuL ⊗ ν` and leaves every record cylinder
  invariant at every period.

The **stated hypothesis** is the product form — the post-record dynamics does
not couple to the record sector. That is exactly the regime the corpus's
record modules call persistence (cf. `RecordLayer/RecordPersistence.lean`,
`RecordLayer/KSigmaRecord.lean`: there records persist under the *protocol's*
own dynamics; here under arbitrary post-record Floquet driving of the system
factor). Coupled post-record dynamics — where the drive can erase records —
is the §H thread's genuinely open continuation, priced by
`collapse_accuracy_bound`-style results, and is deliberately out of the pilot.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4

section Generic

variable {X R : Type*}

/-- Post-record evolution that does not couple to the record factor. -/
def postRecordStep (f : X → X) : X × R → X × R :=
  Prod.map f id

/-- `(f ×ˢ id)^[n] = f^[n] ×ˢ id`: the record factor stays untouched for all
time. -/
lemma prodMap_iterate (f : X → X) (n : ℕ) :
    (postRecordStep (R := R) f)^[n] = postRecordStep (f^[n]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    rw [Function.iterate_succ_apply', ih]
    show (f (f^[n] x.1), x.2) = (f^[n + 1] x.1, x.2)
    rw [Function.iterate_succ_apply']

/-- ★ **Record cylinders are set-invariant** under uncoupled post-record
evolution: the record event is literally the same set after the step. -/
theorem record_cylinder_invariant (f : X → X) (S : Set R) :
    postRecordStep f ⁻¹' (Prod.snd ⁻¹' S) = Prod.snd ⁻¹' S := by
  ext ⟨x, r⟩
  simp [postRecordStep]

/-- ★ Record cylinders are set-invariant at every period count. -/
theorem record_cylinder_iterate_invariant (f : X → X) (S : Set R) (n : ℕ) :
    (postRecordStep (R := R) f)^[n] ⁻¹' (Prod.snd ⁻¹' S) = Prod.snd ⁻¹' S := by
  rw [prodMap_iterate]
  exact record_cylinder_invariant _ S

/-- Uncoupled post-record evolution preserves any product measure whose
system marginal the step preserves. -/
theorem postRecordStep_measurePreserving
    [MeasurableSpace X] [MeasurableSpace R]
    {f : X → X} {μ : Measure X} [SFinite μ] (hf : MeasurePreserving f μ μ)
    (ν : Measure R) [SFinite ν] :
    MeasurePreserving (postRecordStep f) (μ.prod ν) (μ.prod ν) :=
  hf.prod (MeasurePreserving.id ν)

end Generic

/-! ### The CSD instantiation: Floquet driving after a record has formed -/

variable {N : ℕ}

/-- The Floquet ontic step extended to a record-carrying arena
`(KSigma N) × Rec`, acting trivially on the record factor. -/
noncomputable def floquetRecordStep (U : Matrix.unitaryGroup (Fin N) ℂ)
    (Rec : Type*) : KSigma N × Rec → KSigma N × Rec :=
  postRecordStep (floquetOnticStep U)

/-- The record-extended Floquet step preserves `kMuL ⊗ ν`. -/
theorem floquetRecordStep_measurePreserving [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N)
    {Rec : Type*} [MeasurableSpace Rec] (ν : Measure Rec) [SFinite ν] :
    MeasurePreserving (floquetRecordStep U Rec)
      ((kMuL p₀).prod ν) ((kMuL p₀).prod ν) :=
  postRecordStep_measurePreserving
    (floquetOnticStep_measurePreserving U p₀) ν

/-- ★ **Records persist under post-record Floquet driving**: every record
cylinder is the same set at every period count. -/
theorem floquetRecordStep_record_invariant
    (U : Matrix.unitaryGroup (Fin N) ℂ) {Rec : Type*} (S : Set Rec) (n : ℕ) :
    (floquetRecordStep U Rec)^[n] ⁻¹' (Prod.snd ⁻¹' S) = Prod.snd ⁻¹' S :=
  record_cylinder_iterate_invariant _ S n

end CSD.Empirical.QuantumChaos
