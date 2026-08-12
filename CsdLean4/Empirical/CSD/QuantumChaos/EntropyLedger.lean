/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.DerivedCoupling
public import CsdLean4.Empirical.CSD.QuantumChaos.CarrierPersistence
public import CsdLean4.Mathlib.QuantumInfo.Entropy
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The entropy ledger: carrier erosion prices coarse entropy production
(§Q Q4)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics;
`specs/BACKLOG.md` §Q Q4, the H7 follow-up).

Fine-grained entropy is constant — measure preservation is the floor
everywhere in this corpus. So whatever "entropy production" accompanies
record erosion must be **coarse**: an artefact of reading the record
register through a partition. This module makes that ledger precise and
prices it, framed strictly as **retrodiction reliability** — every quantity
is a present-tense measure of a present-tense set.

## The three quantities and how they chain

* `retrodictionSuccess Φ ρ n` — the set where reading the register **now**
  (period `n`) and asserting "this was the formation value" is correct.
  Reliability is its measure. It contains `recordIntact n` (a register that
  never moved certainly retrodicts), so the §H half-life bound prices it:
  ★ `measure_retrodictionSuccess_compl_le` — retrodiction fails on measure
  at most `n · ε`, with `ε` the per-step coupling `μ (recordFlip Φ ρ)`.
* `erosionFraction μ Φ ρ n` — the eroded fraction `μ (recordIntact n)ᶜ` as
  a real number. It starts at `0` (`erosionFraction_zero`), **never
  decreases** (`erosionFraction_monotone` — the ledger's substrate is
  one-way, the second-law shape at the register), and is priced linearly
  (`erosionFraction_le`).
* `ledgerEntropy μ Φ ρ n` — the coarse entropy of the two-cell register
  partition `{intact, eroded}`: `binEntropy (erosionFraction n)`. It opens
  at `0` (`ledgerEntropy_zero`: record formation starts a clean ledger) and
  ★★ `ledgerEntropy_le` prices it by the **same coupling knob**: below the
  half-filling point, `ledgerEntropy n ≤ binEntropy (n · ε)`. One `ε`,
  three readings — reliability, erosion, entropy.

## The link to the corpus's entropy

★ `vonNeumannEntropy_ledgerState` identifies the ledger with the von
Neumann entropy of the register's two-cell diagonal state
`ledgerState e = diag(1 − e, e)`: the measure-side ledger **is** the
quantity governed by the pinch H-theorem (`vonNeumannEntropy_le_pinching`,
TH2 in `Thermo/SecondLaw.lean` — cited, not imported). Density credentials
are supplied (`ledgerState_posSemidef`, `ledgerState_trace`).

## The derived instantiation (Q1/Q2 chain closed onto Q4)

For the qubit phase flip, Q2's Duistermaat–Heckman law computed the
coupling exactly (`deficitKick_phaseFlip_coupling`: `ε = 1 − δ/2`), so both
sides land with **no free parameter**:
`deficitKick_phaseFlip_reliability` (retrodiction fails on at most
`n·(1 − δ/2)`) and `deficitKick_phaseFlip_ledger` (the ledger fills at most
to `binEntropy (n·(1 − δ/2))`).

## Honest scope

No Fano-type converse is claimed (a lower bound on retrodiction error in
terms of conditional entropy needs joint-distribution machinery this module
does not build), and the two-cell ledger is the **register's**
coarse-graining, not a thermodynamic entropy of anything larger. Note also
that `retrodictionSuccess` may transiently exceed `recordIntact` (a readout
can flip back); the inequalities are stated in the honest direction.

Cross-references: `specs/future-work.md`, `specs/BACKLOG.md` §Q (Q4);
`recordIntact_compl_measure_le` (§H), `carrier_persistence_window` (H7),
`recordEvent_measure_invariant` (the event side that does NOT erode),
`entropy_production_nonneg` (TH2's matrix-side companion).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4 Matrix.UnitaryGroup

section Generic

variable {A V : Type*}

/-! ### Retrodiction: read the register now, assert the formation value -/

/-- **The retrodiction-success set**: points where the period-`n` readout
still equals the formation readout, so reading the register *now* and
asserting "this was the recorded value" is correct. Present-tense
checkable: membership is a condition on the current state. -/
def retrodictionSuccess (Φ : A → A) (ρ : A → V) (n : ℕ) : Set A :=
  {a | ρ (Φ^[n] a) = ρ a}

/-- At formation (`n = 0`) retrodiction is certain. -/
@[simp] lemma retrodictionSuccess_zero (Φ : A → A) (ρ : A → V) :
    retrodictionSuccess Φ ρ 0 = Set.univ :=
  Set.eq_univ_of_forall fun _ => rfl

/-- An intact carrier certainly retrodicts: `recordIntact` demands the
readout never moved through period `n`, which in particular pins period
`n` itself. -/
lemma recordIntact_subset_retrodictionSuccess (Φ : A → A) (ρ : A → V)
    (n : ℕ) :
    recordIntact Φ ρ n ⊆ retrodictionSuccess Φ ρ n :=
  fun _ ha => ha n le_rfl

/-- At formation nothing is eroded: `recordIntact 0` is everything. -/
lemma recordIntact_zero (Φ : A → A) (ρ : A → V) :
    recordIntact Φ ρ 0 = Set.univ := by
  refine Set.eq_univ_of_forall fun a k hk => ?_
  rw [Nat.le_zero.mp hk]
  rfl

variable [MeasurableSpace A] {μ : Measure A}

/-- ★ **Retrodiction reliability is priced by the coupling**: under a
measure-preserving step, reading the register at period `n` retrodicts the
formation value except on measure at most `n · ε`, where `ε` is the
per-step record-sector coupling. The half-life bound
(`recordIntact_compl_measure_le`), rerouted through
`recordIntact_subset_retrodictionSuccess`. -/
theorem measure_retrodictionSuccess_compl_le {Φ : A → A} {ρ : A → V}
    (hΦ : MeasurePreserving Φ μ μ) (hD : MeasurableSet (recordFlip Φ ρ))
    (n : ℕ) :
    μ (retrodictionSuccess Φ ρ n)ᶜ ≤ n • μ (recordFlip Φ ρ) :=
  le_trans
    (measure_mono (Set.compl_subset_compl.mpr
      (recordIntact_subset_retrodictionSuccess Φ ρ n)))
    (recordIntact_compl_measure_le hΦ hD n)

/-! ### The erosion fraction: the ledger's one-way substrate -/

/-- **The erosion fraction**: the measure of the eroded set
`(recordIntact n)ᶜ`, as a real number. The scalar the ledger is a function
of. -/
noncomputable def erosionFraction (μ : Measure A) (Φ : A → A) (ρ : A → V)
    (n : ℕ) : ℝ :=
  (μ (recordIntact Φ ρ n)ᶜ).toReal

/-- The ledger opens empty: `erosionFraction 0 = 0`. -/
@[simp] lemma erosionFraction_zero (μ : Measure A) (Φ : A → A) (ρ : A → V) :
    erosionFraction μ Φ ρ 0 = 0 := by
  show (μ (recordIntact Φ ρ 0)ᶜ).toReal = 0
  rw [recordIntact_zero, Set.compl_univ, measure_empty]
  simp

/-- The erosion fraction is nonnegative. -/
lemma erosionFraction_nonneg (μ : Measure A) (Φ : A → A) (ρ : A → V)
    (n : ℕ) :
    0 ≤ erosionFraction μ Φ ρ n :=
  ENNReal.toReal_nonneg

/-- For a probability measure the erosion fraction is at most one. -/
lemma erosionFraction_le_one [IsProbabilityMeasure μ] (Φ : A → A)
    (ρ : A → V) (n : ℕ) :
    erosionFraction μ Φ ρ n ≤ 1 := by
  calc erosionFraction μ Φ ρ n
      ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    _ = 1 := ENNReal.toReal_one

/-- ★ **Erosion is one-way**: the eroded fraction never decreases — the
second-law shape at the record register, from carrier antitonicity alone
(`recordIntact_antitone`; no dynamics hypothesis beyond finiteness of the
measure). Contrast the event side, which does not erode at all
(`recordEvent_measure_invariant`). -/
theorem erosionFraction_monotone [IsFiniteMeasure μ] (Φ : A → A)
    (ρ : A → V) :
    Monotone (erosionFraction μ Φ ρ) :=
  fun _ _ hnm =>
    ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono (Set.compl_subset_compl.mpr
        (recordIntact_antitone Φ ρ hnm)))

/-- **Erosion is priced linearly** by the per-step coupling: the real-number
form of the half-life bound. -/
theorem erosionFraction_le [IsFiniteMeasure μ] {Φ : A → A} {ρ : A → V}
    (hΦ : MeasurePreserving Φ μ μ) (hD : MeasurableSet (recordFlip Φ ρ))
    (n : ℕ) :
    erosionFraction μ Φ ρ n ≤ (n : ℝ) * (μ (recordFlip Φ ρ)).toReal := by
  have h := recordIntact_compl_measure_le hΦ hD n
  rw [nsmul_eq_mul] at h
  have hfin : (n : ℝ≥0∞) * μ (recordFlip Φ ρ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top μ _)
  calc erosionFraction μ Φ ρ n
      ≤ ((n : ℝ≥0∞) * μ (recordFlip Φ ρ)).toReal := ENNReal.toReal_mono hfin h
    _ = (n : ℝ) * (μ (recordFlip Φ ρ)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-! ### The ledger: two-cell coarse entropy, priced by the same knob -/

/-- **The entropy ledger**: the coarse (Shannon) entropy of the two-cell
register partition `{intact, eroded}` at period `n`. All entropy here is
coarse — the fine-grained entropy is constant because the dynamics
preserves the measure. -/
noncomputable def ledgerEntropy (μ : Measure A) (Φ : A → A) (ρ : A → V)
    (n : ℕ) : ℝ :=
  Real.binEntropy (erosionFraction μ Φ ρ n)

/-- Record formation opens a clean ledger: `ledgerEntropy 0 = 0`. -/
@[simp] lemma ledgerEntropy_zero (μ : Measure A) (Φ : A → A) (ρ : A → V) :
    ledgerEntropy μ Φ ρ 0 = 0 := by
  show Real.binEntropy (erosionFraction μ Φ ρ 0) = 0
  rw [erosionFraction_zero, Real.binEntropy_zero]

/-- The ledger is nonnegative (the erosion fraction lies in `[0, 1]` for a
probability measure). -/
lemma ledgerEntropy_nonneg [IsProbabilityMeasure μ] (Φ : A → A) (ρ : A → V)
    (n : ℕ) :
    0 ≤ ledgerEntropy μ Φ ρ n :=
  Real.binEntropy_nonneg (erosionFraction_nonneg μ Φ ρ n)
    (erosionFraction_le_one Φ ρ n)

/-- ★★ **The ledger is priced by the same coupling knob**: below the
half-filling point (`n · ε ≤ 1/2`), the coarse entropy of the register
partition after `n` periods is at most `binEntropy (n · ε)` — the same
per-step coupling `ε` that prices retrodiction reliability
(`measure_retrodictionSuccess_compl_le`) bounds how far the entropy ledger
can fill. One knob, three readings: reliability, erosion, entropy. -/
theorem ledgerEntropy_le [IsProbabilityMeasure μ] {Φ : A → A} {ρ : A → V}
    (hΦ : MeasurePreserving Φ μ μ) (hD : MeasurableSet (recordFlip Φ ρ))
    {n : ℕ}
    (hn : (n : ℝ) * (μ (recordFlip Φ ρ)).toReal ≤ 2⁻¹) :
    ledgerEntropy μ Φ ρ n
      ≤ Real.binEntropy ((n : ℝ) * (μ (recordFlip Φ ρ)).toReal) := by
  have hle := erosionFraction_le hΦ hD n
  have h0 := erosionFraction_nonneg μ Φ ρ n
  show Real.binEntropy (erosionFraction μ Φ ρ n) ≤ _
  exact Real.binEntropy_strictMonoOn.monotoneOn
    ⟨h0, hle.trans hn⟩ ⟨by positivity, hn⟩ hle

/-! ### The register's coarse state: the ledger is a von Neumann entropy -/

/-- **The register's two-cell coarse state**: the diagonal density with
weights `(1 − e, e)` — kept mass on the intact cell, eroded mass on its
complement. -/
noncomputable def ledgerState (e : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => (RCLike.ofReal (![1 - e, e] i) : ℂ)

/-- The register state is Hermitian (real diagonal). -/
lemma ledgerState_isHermitian (e : ℝ) : (ledgerState e).IsHermitian :=
  Matrix.isHermitian_diagonal_of_self_adjoint _
    (funext fun i => RCLike.conj_ofReal (K := ℂ) (![1 - e, e] i))

/-- The register state has unit trace. -/
lemma ledgerState_trace (e : ℝ) : (ledgerState e).trace = 1 := by
  show (Matrix.diagonal fun i => (RCLike.ofReal (![1 - e, e] i) : ℂ)).trace = 1
  rw [Matrix.trace_diagonal, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- The register state is positive semidefinite for `e ∈ [0, 1]`. -/
lemma ledgerState_posSemidef {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    (ledgerState e).PosSemidef := by
  show (Matrix.diagonal fun i =>
    (RCLike.ofReal (![1 - e, e] i) : ℂ)).PosSemidef
  refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
  fin_cases i
  · simpa using (RCLike.ofReal_nonneg (K := ℂ)).mpr
      (by linarith : (0:ℝ) ≤ 1 - e)
  · simpa using (RCLike.ofReal_nonneg (K := ℂ)).mpr h0

/-- ★ **The ledger is a von Neumann entropy**: the two-cell coarse entropy
equals `S(diag(1 − e, e))` — the measure-side ledger is exactly the
quantity the pinch H-theorem (`vonNeumannEntropy_le_pinching`, TH2)
governs on the matrix side. -/
theorem vonNeumannEntropy_ledgerState (e : ℝ) :
    QuantumInfo.vonNeumannEntropy (ledgerState_isHermitian e)
      = Real.binEntropy e := by
  have h : (Matrix.diagonal fun i =>
      (RCLike.ofReal (![1 - e, e] i) : ℂ)).IsHermitian :=
    ledgerState_isHermitian e
  show QuantumInfo.vonNeumannEntropy h = Real.binEntropy e
  rw [QuantumInfo.vonNeumannEntropy_diagonal h, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  exact add_comm _ _

end Generic

/-! ### The derived instantiation: the phase flip, with no free parameter -/

/-- The unit circle's volume is a probability measure (`RecordCircle` is
`AddCircle 1`, total mass `1`). -/
instance : IsProbabilityMeasure (volume : Measure RecordCircle) :=
  ⟨by rw [AddCircle.measure_univ]; exact ENNReal.ofReal_one⟩

/-- ★ **Derived retrodiction reliability** (qubit, phase flip): with the
coupling computed exactly by the Duistermaat–Heckman law
(`deficitKick_phaseFlip_coupling`), retrodiction from the present register
fails on measure at most `n · (1 − δ/2)` — no free parameter. -/
theorem deficitKick_phaseFlip_reliability (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (p₀ : CPN 2) {δ : ℝ} (hδ0 : 0 < δ)
    {kick : RecordCircle} (hkick : kick ≠ 0) (n : ℕ) :
    ((fubiniStudyMeasure p₀).prod volume)
        (retrodictionSuccess (deficitTriggeredKick V phaseFlipW δ kick)
          Prod.snd n)ᶜ
      ≤ n • ENNReal.ofReal (1 - δ / 2) := by
  have hflip_meas : MeasurableSet
      (recordFlip (deficitTriggeredKick V phaseFlipW δ kick) Prod.snd) := by
    rw [deficitTriggeredKick, recordFlip_triggeredRecordKick _ _ hkick]
    exact (measurableSet_deficitTrigger phaseFlipW δ).prod MeasurableSet.univ
  have h := measure_retrodictionSuccess_compl_le
    (deficitTriggeredKick_measurePreserving V phaseFlipW δ kick p₀)
    hflip_meas n
  rwa [deficitKick_phaseFlip_coupling V p₀ hδ0 hkick] at h

/-- ★ **The derived ledger** (qubit, phase flip): below half-filling the
entropy ledger is at most `binEntropy (n · (1 − δ/2))` — erosion,
reliability, and entropy production all priced by the single coupling the
DH law computed. Closes the Q1 → Q2 → Q4 chain with no free parameter. -/
theorem deficitKick_phaseFlip_ledger (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (p₀ : CPN 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    {kick : RecordCircle} (hkick : kick ≠ 0) {n : ℕ}
    (hn : (n : ℝ) * (1 - δ / 2) ≤ 2⁻¹) :
    ledgerEntropy ((fubiniStudyMeasure p₀).prod volume)
        (deficitTriggeredKick V phaseFlipW δ kick) Prod.snd n
      ≤ Real.binEntropy ((n : ℝ) * (1 - δ / 2)) := by
  have hflip_meas : MeasurableSet
      (recordFlip (deficitTriggeredKick V phaseFlipW δ kick) Prod.snd) := by
    rw [deficitTriggeredKick, recordFlip_triggeredRecordKick _ _ hkick]
    exact (measurableSet_deficitTrigger phaseFlipW δ).prod MeasurableSet.univ
  have htoReal : (((fubiniStudyMeasure p₀).prod volume)
      (recordFlip (deficitTriggeredKick V phaseFlipW δ kick)
        Prod.snd)).toReal = 1 - δ / 2 := by
    rw [deficitKick_phaseFlip_coupling V p₀ hδ0 hkick,
      ENNReal.toReal_ofReal (by linarith)]
  have h := ledgerEntropy_le
    (deficitTriggeredKick_measurePreserving V phaseFlipW δ kick p₀)
    hflip_meas (n := n) (by rw [htoReal]; exact hn)
  rwa [htoReal] at h

end CSD.Empirical.QuantumChaos
