/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SkewReroute
public import CsdLean4.LF3.OperationalNoSignalling

/-!
# The singlet on the I3 record basins is operationally no-signalling, by the primitive

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #157 (out of ~~#137~~): the concrete instance.

~~#137~~ instantiated the local-setting-aware primitive at the I3 basins for an **arbitrary** family of
no-signalling `2 × 2` tables. The corpus's singlet kernel supplies the family: `P_st a b s t =
(1 − s t a·b)/4` (`LF3/Singlet/Kernel.lean`), with both marginals exactly `1/2` at every context
(`marginal_a_eq_half`, `marginal_b_eq_half`). This file packages it and takes the corollary.

* `singletJointRates a b : JointRates 2 2` — the singlet's table at the context `⟨a, b⟩`, with
  outcomes indexed by `Fin 2` through `signOfFin`; `singletJointRates_rate`, `_rowSum`, `_colSum`
  (both marginals `1/2`).
* `singletTables : MeasurementContext → JointRates 2 2`, and its no-signalling in the form the
  reroutes need: `singletTables_rowSum_eq`, `singletTables_colSum_eq`.
* `volume_skewCell_singlet` — **the skew cells carry the singlet's joint probabilities exactly**,
  `volume (skewCell (singletJointRates a b) s t) = P_st a b s t`.
* ★★★ `skewLocalSettingLocalityBSinglet` — the rectangle exchange **is** a B-wing reroute for the
  singlet; ★★★ `operationalNoSignalling_skew_singlet` — **the singlet on the I3 record basins is
  operationally no-signalling, derived from the primitive**, on the same fibre partition whose
  cells carry the Bell-violating joint law.

## Honest scope

* As in ~~#137~~: the fibre with Haar measure, the base-coupled version being #155; and the
  `2 × 2` outcome sets are read as `Sign` through `signOfFin` (`0 ↦ plus`, `1 ↦ minus`).
* The blind B-primitive is **not** instantiated, and cannot be (the finding of ~~#137~~; its proof
  is #156). What is instantiated is the primitive the derivation consumes.

References: `SkewReroute.lean` (`skewOutcomeMaps`, `skewLocalSettingLocalityB`,
`operationalNoSignalling_skew`), `LF3/Singlet/Kernel.lean` (`P_st`, `P_st_nonneg`,
`marginal_a_eq_half`, `marginal_b_eq_half`), `LF3/OperationalNoSignalling.lean`
(`singlet_operational_no_signalling`, the kernel-level verification this now derives from a
primitive); `specs/BACKLOG.md` #157, ~~#137~~.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

open LF3

@[simp] theorem signOfFin_zero : signOfFin 0 = Sign.plus := rfl

@[simp] theorem signOfFin_one : signOfFin 1 = Sign.minus := rfl

/-! ### The singlet's table at a context -/

/-- **The singlet's joint table at the context `⟨a, b⟩`**, outcomes indexed by `Fin 2` through
`signOfFin`. -/
def singletJointRates (a b : DetectorSetting) : JointRates 2 2 where
  rate := fun s t => P_st a b (signOfFin s) (signOfFin t)
  nonneg := fun s t => P_st_nonneg a b _ _
  sum_one := by
    have h0 := marginal_a_eq_half a b Sign.plus
    have h1 := marginal_a_eq_half a b Sign.minus
    rw [Sign.sum_univ] at h0 h1
    simp only [Fin.sum_univ_two, signOfFin_zero, signOfFin_one]
    linarith

@[simp] theorem singletJointRates_rate (a b : DetectorSetting) (s t : Fin 2) :
    (singletJointRates a b).rate s t = P_st a b (signOfFin s) (signOfFin t) := rfl

/-- A's marginal is `1/2` at every context. -/
theorem singletJointRates_rowSum (a b : DetectorSetting) (s : Fin 2) :
    (singletJointRates a b).rowSum s = 1 / 2 := by
  have h := marginal_a_eq_half a b (signOfFin s)
  rw [Sign.sum_univ] at h
  unfold JointRates.rowSum
  simp only [Fin.sum_univ_two, singletJointRates_rate, signOfFin_zero, signOfFin_one]
  exact h

/-- B's marginal is `1/2` at every context. -/
theorem singletJointRates_colSum (a b : DetectorSetting) (t : Fin 2) :
    (singletJointRates a b).colSum t = 1 / 2 := by
  have h := marginal_b_eq_half a b (signOfFin t)
  rw [Sign.sum_univ] at h
  unfold JointRates.colSum
  simp only [Fin.sum_univ_two, singletJointRates_rate, signOfFin_zero, signOfFin_one]
  exact h

/-- **The singlet's tables, one per context.** -/
def singletTables (C : MeasurementContext) : JointRates 2 2 := singletJointRates C.a C.b

/-- A's marginal does not depend on B's setting. -/
theorem singletTables_rowSum_eq (a b b' : DetectorSetting) :
    (singletTables ⟨a, b⟩).rowSum = (singletTables ⟨a, b'⟩).rowSum := by
  funext s
  simp only [singletTables, singletJointRates_rowSum]

/-- B's marginal does not depend on A's setting. -/
theorem singletTables_colSum_eq (a a' b : DetectorSetting) :
    (singletTables ⟨a, b⟩).colSum = (singletTables ⟨a', b⟩).colSum := by
  funext t
  simp only [singletTables, singletJointRates_colSum]

/-! ### The skew cells carry the singlet's law -/

/-- ★ **The skew cells carry the singlet's joint probabilities exactly.** -/
theorem volume_skewCell_singlet (a b : DetectorSetting) (s t : Fin 2) :
    (volume : Measure LF4.KTorus) (skewCell (singletJointRates a b) s t)
      = ENNReal.ofReal (P_st a b (signOfFin s) (signOfFin t)) :=
  volume_skewCell (singletJointRates a b) s t

/-! ### ★★★ The instance -/

/-- ★★★ **The rectangle exchange is a B-wing reroute for the singlet.** -/
def skewLocalSettingLocalityBSinglet :
    LocalSettingLocalityB (volume : Measure LF4.KTorus) (skewOutcomeMaps singletTables) :=
  skewLocalSettingLocalityB singletTables singletTables_colSum_eq

/-- ★★★ **The identity is an A-wing reroute for the singlet.** -/
def skewLocalSettingLocalityASinglet :
    LocalSettingLocalityA (volume : Measure LF4.KTorus) (skewOutcomeMaps singletTables) :=
  skewLocalSettingLocalityA singletTables singletTables_rowSum_eq

/-- ★★★ **The singlet on the I3 record basins is operationally no-signalling, derived from the
primitive** — on the fibre partition whose cells carry the Bell-violating joint law
(`volume_skewCell_singlet`). -/
theorem operationalNoSignalling_skew_singlet :
    OperationalNoSignalling (volume : Measure LF4.KTorus) (skewOutcomeMaps singletTables) :=
  operationalNoSignalling_skew singletTables singletTables_rowSum_eq singletTables_colSum_eq

end CSD.RecordLayer

end

end
