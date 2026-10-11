/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.TwoWingRecord
public import CsdLean4.Empirical.QM.Bell

/-!
# The two-wing record violates the CHSH bound

**Category:** 3-Local (the entangled de-isolation tier).
BACKLOG #131, obligation **(4)**, the **Bell** half.

The no-signalling half of obligation (4) landed with `LF3.symmTranslationLocalityB` (the primitive's
missing model) and the marginal theorems of
[`TwoWingRecord.lean`](TwoWingRecord.lean). This is the other half, and it is the last item on #131
with a price: **the CHSH combination of the two-wing record correlations is `−2√2`.**

## What is new here, and what is imported

⚠️ **No Bell theorem is proved here, and none is needed.** The singlet's `E(a, b) = −a·b` is
`LF3.correlation_eq_neg_dot`, the `−2√2` at the canonical angles is
`Empirical.Bell.chsh_singlet_at_optimal_angles`, and the local-hidden-variable bound `|S| ≤ 2` is
`Empirical.QM.E91.lhvCHSH_abs_le_two` over a genuine measure-theoretic model. All three are
imported.

**What is new is the quantity being correlated.** Until now the corpus' CHSH was a function of
`P_st` — an algebraic kernel. Here it is a function of the **measures of record events on `Σ`**:
sets of ontic microstates, read in `epistemicMeasure`, **after the de-isolation flow from the
prepared ray**. So for the first time Bell violation is a statement about the *same objects* as
no-signalling (`toReal_measure_preimage_wingAEvent_eq_of_setting`), record stability
(`RecordLayer.measure_drift_wingCode_ne_le`) and causal separation
(`CV.spacelike_twoWing`) — which is exactly what #131 asked for and what "within the same
dynamical model" means.

* `recordCorrelation e p` — the correlation of the two-wing record events at a ray;
* ★★★ `recordCorrelation_eq_correlation` and ★★★ `recordCorrelation_eq_neg_dotR` — it **is** the
  singlet correlation, `−a·b`, at every setting pair and with no genericity hypothesis;
* `preparedRecordCorrelation a b` — the same read **at the prepared, pre-measurement ray**, through
  `liftBase localDeisolationFlow`, with ★★★ `preparedRecordCorrelation_eq_correlation`;
* ★★★ `chsh_preparedRecord_eq_neg_two_sqrt_two` — the CHSH of the four prepared-ray record
  correlations is `−2√2` at the canonical angles;
* ★★★ `bellClassicalBound_lt_abs_chsh_preparedRecord` — and that **exceeds the
  local-hidden-variable bound**: `2 < |S| = 2√2`.

## Honest scope

⚠️ **The four terms are four different runs.** Each `preparedRecordCorrelation a b` is evaluated in
its *own* prepared measure, at the ray `preparedRay a b` built from `localNudgeVec a b`. That is
what a Bell test is — four setting configurations, separate runs — but it is **not** the single-`μ`
idealisation `LF3.OperationalNoSignalling` is stated in. Both are in the corpus and they must not be
run together: the no-signalling predicate fixes one measure across contexts (which *is* the
measurement-independence premise), while this statement ranges over four preparations.

⚠️ **This does not make CSD local, and does not pretend to.** The record events move with the joint
context (`RecordLayer.wingCode_ne_of_mem_of_mem`), so the outcome maps are not of product-partition
arity and `LF6.no_product_partition_realises_singlet` does not apply — which is why a violation is
possible at all. Nothing here is a non-contextual value assignment, and the violation is of the
**LHV** bound, not of anything CSD claims.

⚠️ **`P_st` is not re-derived and the angles are not optimised.** `chshA`, `chshA'`, `chshB`,
`chshB'` are the canonical settings already in `Empirical/QM/Bell.lean`; nothing here shows they are
optimal (that is Tsirelson, `chsh_inner_bound`, also already there).

⚠️ **Still not `C-1`.** Causal adjacency is supplied through `CV.twoWingGraph`, and nothing here
shows that the apparent nonlocality is a consequence of projection alone. #131 says so explicitly,
and obligation (4) being discharged does not change it.

References: [`TwoWingRecord.lean`](TwoWingRecord.lean) (`recordCorrelation`'s ingredients:
`pointerDecode`, `toReal_measure_wingEvent_eq_P_st`,
`toReal_measure_preimage_wingEvent_eq_P_st`, `preparedRay`),
[`NudgeLocality.lean`](NudgeLocality.lean) (`localNudgeVec`),
`Empirical/QM/Bell.lean` (`correlation`, `chshOperator`, `chsh_singlet_at_optimal_angles`,
`bellClassicalBoundValue`, `chsh_classical_bound_violated`),
`Empirical/QM/Crypto/E91.lean` (`lhvCHSH_abs_le_two`, the LHV bound this exceeds),
`LF3/Singlet/Kernel.lean` (`P_st`, `dotR`);
`specs/BACKLOG.md` #131 obligation (4); `specs/two-wing-experiment-scoping.md` §6.
-/

@[expose] public section

open MeasureTheory
open scoped LinearAlgebra.Projectivization
open CSD.LF3 CSD.RecordLayer CSD.Empirical.Bell

noncomputable section

namespace CSD.LF6

open CSD.LF4

/-! ### The correlation of the record events -/

/-- **The two-wing record correlation at a ray**: the `±1`-weighted sum of the Born weights of the
joint record events. The quantity a Bell test measures, with the outcomes read off `Σ` rather than
off an algebraic kernel. -/
def recordCorrelation {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p : CPN (M + 1)) : ℝ :=
  ∑ st : Sign × Sign, st.1.val * st.2.val *
    (epistemicMeasure p (wingEvent (momentContext (M + 1)) (pointerDecode e) st)).toReal

/-- ★★★ **The record correlation is the singlet correlation.** Term by term, by
`toReal_measure_wingEvent_eq_P_st`: the measure of the record event for `(s, t)` *is* `P_st a b s t`,
so the sum is the kernel's own correlation. No genericity hypothesis. -/
theorem recordCorrelation_eq_correlation {M : ℕ} (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) :
    recordCorrelation e (Projectivization.mk ℂ ψ' hψ'0) = correlation a b := by
  show ∑ st : Sign × Sign, st.1.val * st.2.val *
      (epistemicMeasure (Projectivization.mk ℂ ψ' hψ'0)
        (wingEvent (momentContext (M + 1)) (pointerDecode e) st)).toReal
    = ∑ st : Sign × Sign, st.1.val * st.2.val * P_st a b st.1 st.2
  refine Finset.sum_congr rfl fun st _ => ?_
  rw [toReal_measure_wingEvent_eq_P_st a b e ψ' hψ'eq hψ'0 st.1 st.2]

/-- ★★★ **Hence `−a·b`**, the singlet's closed form, now as a statement about the measures of
record events. -/
theorem recordCorrelation_eq_neg_dotR {M : ℕ} (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) :
    recordCorrelation e (Projectivization.mk ℂ ψ' hψ'0) = -(dotR a b) := by
  rw [recordCorrelation_eq_correlation a b e ψ' hψ'eq hψ'0]
  exact Empirical.Bell.correlation_eq_neg_dot a b

/-! ### Read at the prepared ray, along the flow -/

/-- **The two-wing record correlation of a run**: the same `±1`-weighted sum, but in the **prepared,
pre-measurement** epistemic measure, with the record events pulled back along the lifted
de-isolation flow. This is the correlation of an actual run of the experiment. -/
def preparedRecordCorrelation (a b : DetectorSetting) : ℝ :=
  ∑ st : Sign × Sign, st.1.val * st.2.val *
    (epistemicMeasure (preparedRay a b)
      (liftBase localDeisolationFlow ⁻¹'
        wingEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) st)).toReal

/-- ★★★ **The run's record correlation is the singlet correlation.** Everything about the dynamics
is already in `toReal_measure_preimage_wingEvent_eq_P_st`; this is that theorem summed against the
`±1` weights. -/
theorem preparedRecordCorrelation_eq_correlation (a b : DetectorSetting) :
    preparedRecordCorrelation a b = correlation a b := by
  show ∑ st : Sign × Sign, st.1.val * st.2.val *
      (epistemicMeasure (preparedRay a b)
        (liftBase localDeisolationFlow ⁻¹'
          wingEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) st)).toReal
    = ∑ st : Sign × Sign, st.1.val * st.2.val * P_st a b st.1 st.2
  refine Finset.sum_congr rfl fun st _ => ?_
  rw [toReal_measure_preimage_wingEvent_eq_P_st a b st.1 st.2]

theorem preparedRecordCorrelation_eq_neg_dotR (a b : DetectorSetting) :
    preparedRecordCorrelation a b = -(dotR a b) := by
  rw [preparedRecordCorrelation_eq_correlation]
  exact Empirical.Bell.correlation_eq_neg_dot a b

/-! ### The CHSH violation -/

/-- **The CHSH combination of the four runs' record correlations.** Four setting configurations,
four prepared rays, four flows — as in an actual Bell test. -/
def chshPreparedRecord : ℝ :=
  preparedRecordCorrelation chshA chshB - preparedRecordCorrelation chshA chshB'
    + preparedRecordCorrelation chshA' chshB + preparedRecordCorrelation chshA' chshB'

/-- The record CHSH is the kernel's CHSH, term by term. -/
theorem chshPreparedRecord_eq_chshOperator :
    chshPreparedRecord = chshOperator chshA chshA' chshB chshB' := by
  rw [chshPreparedRecord, chshOperator, preparedRecordCorrelation_eq_correlation,
    preparedRecordCorrelation_eq_correlation, preparedRecordCorrelation_eq_correlation,
    preparedRecordCorrelation_eq_correlation]

/-- ★★★ **The two-wing record's CHSH value is `−2√2`.** The correlated quantities are measures of
record events on `Σ`, in the prepared epistemic measure, after the de-isolation flow — so this is
the Bell half of #131 obligation (4): the same model that carries no-signalling, record stability
and causal separation also violates CHSH. -/
theorem chsh_preparedRecord_eq_neg_two_sqrt_two :
    chshPreparedRecord = -(2 * Real.sqrt 2) := by
  rw [chshPreparedRecord_eq_chshOperator]
  exact chsh_singlet_at_optimal_angles

/-- ★★★ **And it exceeds the local-hidden-variable bound.** `2 < 2√2`, with the bound itself proved
over a genuine measure-theoretic hidden-variable model in
`Empirical.QM.E91.lhvCHSH_abs_le_two` — so no such model reproduces this record's statistics. -/
theorem bellClassicalBound_lt_abs_chsh_preparedRecord :
    bellClassicalBoundValue < |chshPreparedRecord| := by
  rw [chsh_preparedRecord_eq_neg_two_sqrt_two, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2)]
  exact chsh_classical_bound_violated

end CSD.LF6

end

end
