/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.NudgeLocality
public import CsdLean4.RecordLayer.TwoWingCoarsening

/-!
# The two-wing record of the local de-isolation flow

**Category:** 3-Local (the entangled de-isolation tier).
BACKLOG #131, obligation **(1)**, second half: tying the record events to `LF6`'s pointer blocks.

## What was missing, and it was not a number

`LF6`'s clause (3) already says the de-isolation reproduces the singlet, and `NudgeLocality`'s
`localDeisolation_A_marginal_volume_eq_half` already says each wing's marginal is `1/2` at every
setting pair. **Those numbers are not re-proved here, they are imported.** What was missing is that
every one of those statements is about a *sum over an index set* —

    ∑ n : Fin 4, (epistemicMeasure p (globalBasin (momentContext (M+1)) (e (n, stIdx (s,t))))).toReal

— and a sum of numbers is not an event. There was no **set** whose measure is "the two wings
recorded `(s, t)`", so there was nothing to transport along the flow, nothing to intersect, and
nothing to factor through a macroscopic coordinate. #131's blocker (I) having been resolved by
option I1, [`TwoWingCoarsening.lean`](../RecordLayer/TwoWingCoarsening.lean) supplies those sets as
coarsenings of the fine basins, and this file identifies the coarsening that `LF6`'s index map
realises.

## What is proved

* `pointerDecode e` — **the decoding `LF6` was using implicitly**: a basin index `i : Fin (M+1)`
  records the wing pair `stIdx⁻¹ (e⁻¹ i).2`, the system index `n` being exactly what the pointer
  block sums over. ★ `filter_pointerDecode` is the index transport of the audit's §3: the fine cells
  the decoding sends to `(s,t)` are *precisely* `LF6`'s pointer block `{e (n, stIdx (s,t)) | n}`;
* ★★★ `toReal_measure_wingEvent_eq_P_st` — **the two-wing record event's Born weight is the
  singlet's joint distribution**, `P_st a b s t`, at every setting pair (no genericity hypothesis,
  routing through `localDeisolation_pointer_volume_local`). This is clause (3) restated about **one
  event** rather than a sum, which is what makes everything below possible;
* ★★★ `toReal_measure_preimage_wingEvent_eq_P_st` — **one physical record history.** The
  probability, *in the prepared pre-measurement epistemic measure*, that the run ends with the two
  wings recording `(s, t)` is `P_st a b s t`. The Born clause was only ever available at the
  post-measurement ray; composing it with `measure_preimage_liftBase` and clause (6)
  (`localDeisolationFlow_realises_localNaimark`) moves it to the prepared ray, which is where an
  experiment starts. **This is the obligation;**
* ★★★ `toReal_measure_wingAEvent_eq_half` / ★★★ `toReal_measure_wingBEvent_eq_half` and
  ★★ `toReal_measure_preimage_wingAEvent_eq_half` — each wing's marginal is `1/2`, as an **event
  probability** and then **along the flow from the prepared ray**. The arithmetic is
  `LF3.marginal_a_eq_half`, imported; what is new is that these are measures of sets and that they
  hold at the start of the run;
* ★★ `toReal_measure_preimage_wingAEvent_eq_of_setting` — **operational no-signalling along the
  dynamics**: A's wing-event probability is the same for `b` and `b'`, with each side evaluated in
  its own prepared measure and after its own flow. It also **discharges, for the singlet, the premise
  that `measure_wingAEvent_eq_of_fineSum_eq` leaves open** — #131 recorded that premise as not
  discharged, and for this model it now is;
* ★★ `factorsThrough_wingEvent_pointerDecode` — the two-wing events are **macroscopic**: preimages
  of #102's record string, which is obligation (5)'s shape at this instance.

## Honest scope

⚠️ **The marginals and no-signalling are imported arithmetic, not new content.**
`localDeisolation_A_marginal_volume_eq_half` and `localDeisolation_no_signalling_A` already prove
them for the index sums. The contribution here is the *event* formulation and the *prepared-ray*
formulation, not the numbers.

⚠️ **One ontic selector.** Everything here inherits option I1's concession: the two wings are two
readings of `x.2.1`. See [`TwoWingCoarsening.lean`](../RecordLayer/TwoWingCoarsening.lean) and
BACKLOG row 132.

⚠️ **Not Bell, and not `C-1`.** No CHSH value is computed here and no causal structure is used;
obligation (3) (records to causal regions) and obligation (4)'s Bell half are separate, and the
missing `RemoteSettingLocalityB` witness of the audit's §4 is still missing. Nothing here shows that
apparent nonlocality is a consequence of projection alone.

⚠️ **The preparation is the moduli-free local object.** `localNudgeVec a b = (U_A(a) ⊗ U_B(b))ᴴ ψ⁻`,
not `nudgedSinglet`, which strips every phase — see `NudgeLocality`'s erratum. That is why no
genericity hypothesis appears.

⚠️ **One flow, one measurement.** `liftBase localDeisolationFlow` moves the base and leaves the
record medium fixed, so this says nothing about record *writes* on the fibre
(`RecordLayer.sigmaShift`) or about record stability over time, which is obligation (2).

References: [`NudgeLocality.lean`](NudgeLocality.lean)
(`localNudgeVec`, `localDeisolation_pointer_volume_local`,
`localDeisolation_A_marginal_volume_eq_half`), [`LocalDeisolationFlow.lean`](LocalDeisolationFlow.lean)
(`localDeisolationFlow`, `localDeisolationFlow_realises_localNaimark`, `localEmbedGround`,
`localDeisolation_capstone`), [`SingletDeisolationFlow.lean`](SingletDeisolationFlow.lean) (`stIdx`),
[`TwoWingCoarsening.lean`](../RecordLayer/TwoWingCoarsening.lean) (`coarseEvent`, `wingEvent`,
`measure_coarseEvent`, `measure_wingAEvent_eq_sum`, `factorsThrough_coarseEvent`),
[`FlowRecordHistory.lean`](../RecordLayer/FlowRecordHistory.lean) (`liftBase`,
`measure_preimage_liftBase`), `LF3/Singlet/Kernel.lean` (`P_st`), `Empirical/QM/Bell.lean`
(`marginal_a_eq_half`); `specs/BACKLOG.md` #131 obligation (1), #132;
`specs/two-wing-experiment-scoping.md` §3 (the index transport) and §6.
-/

@[expose] public section

open Matrix Complex MeasureTheory
open scoped ENNReal Kronecker LinearAlgebra.Projectivization
open CSD.LF3 CSD.RecordLayer

noncomputable section

namespace CSD.LF6

open CSD.LF4

/-! ### The decoding `LF6` was using implicitly -/

/-- **The pointer decoding.** A basin index `i : Fin (M+1)` carries a system index and a pointer
index through `e`; the *pointer* half is the two-wing outcome, and the system half is exactly what
`LF6`'s pointer-block sum traces out. -/
def pointerDecode {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (i : Fin (M + 1)) : Sign × Sign :=
  stIdx.symm (e.symm i).2

@[simp]
theorem pointerDecode_apply {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (n : Fin 4)
    (st : Sign × Sign) : pointerDecode e (e (n, stIdx st)) = st := by
  simp [pointerDecode]

theorem pointerDecode_eq_iff {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (i : Fin (M + 1))
    (st : Sign × Sign) : pointerDecode e i = st ↔ ∃ n : Fin 4, i = e (n, stIdx st) := by
  constructor
  · intro h
    refine ⟨(e.symm i).1, ?_⟩
    have h2 : (e.symm i).2 = stIdx st := stIdx.symm_apply_eq.1 h
    rw [← h2]
    simp
  · rintro ⟨n, rfl⟩
    simp

/-- ★ **The index transport of the audit's §3.** The fine cells the pointer decoding sends to
`(s, t)` are *precisely* `LF6`'s pointer block — so the coarsening of
[`TwoWingCoarsening.lean`](../RecordLayer/TwoWingCoarsening.lean) and the index map of clause (3)
describe the same set of basins, and nothing has been quietly re-indexed. -/
theorem filter_pointerDecode {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (st : Sign × Sign) :
    (Finset.univ.filter fun i => pointerDecode e i = st)
      = Finset.univ.image fun n : Fin 4 => e (n, stIdx st) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    pointerDecode_eq_iff]
  constructor <;> (rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩)

theorem injOn_pointerBlock {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (st : Sign × Sign) :
    Set.InjOn (fun n : Fin 4 => e (n, stIdx st)) ↑(Finset.univ : Finset (Fin 4)) := by
  intro x _ y _ hxy
  simpa using e.injective hxy

/-! ### The pointer block is one event -/

/-- **The two-wing record event's weight is the pointer-block sum.** The left-hand side is the
measure of a *set*; the right-hand side is the sum `LF6`'s clause (3) is stated in. -/
theorem measure_wingEvent_pointerDecode {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1))
    (p : CPN (M + 1)) (st : Sign × Sign) :
    epistemicMeasure p (wingEvent (momentContext (M + 1)) (pointerDecode e) st)
      = ∑ n : Fin 4,
          epistemicMeasure p (globalBasin (momentContext (M + 1)) (e (n, stIdx st))) := by
  show epistemicMeasure p (coarseEvent (momentContext (M + 1)) (pointerDecode e) st) = _
  rw [measure_coarseEvent, filter_pointerDecode, Finset.sum_image (injOn_pointerBlock e st)]

theorem toReal_measure_wingEvent_pointerDecode {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1))
    (p : CPN (M + 1)) (st : Sign × Sign) :
    (epistemicMeasure p (wingEvent (momentContext (M + 1)) (pointerDecode e) st)).toReal
      = ∑ n : Fin 4,
          (epistemicMeasure p (globalBasin (momentContext (M + 1)) (e (n, stIdx st)))).toReal := by
  rw [measure_wingEvent_pointerDecode, ENNReal.toReal_sum fun n _ => measure_ne_top _ _]

/-! ### The singlet's joint law, as one event's Born weight -/

/-- ★★★ **The two-wing record event reproduces the singlet.** The Born weight of "the two wings
recorded `(s, t)`" is `P_st a b s t`, at **every** setting pair.

This is `LF6`'s clause (3) restated about a single event instead of a sum over a pointer block, and
that restatement is the point: an event can be transported along the flow, which is what the next
theorem does. The arithmetic is `localDeisolation_pointer_volume_local`, imported. -/
theorem toReal_measure_wingEvent_eq_P_st {M : ℕ} (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) (s t : Sign) :
    (epistemicMeasure (Projectivization.mk ℂ ψ' hψ'0)
        (wingEvent (momentContext (M + 1)) (pointerDecode e) (s, t))).toReal
      = P_st a b s t := by
  rw [toReal_measure_wingEvent_pointerDecode]
  exact localDeisolation_pointer_volume_local a b e ψ' hψ'eq hψ'0 s t

/-- ★★★ **The A-wing's event probability is `1/2`**, at every setting pair. The marginal arithmetic
is `LF3.marginal_a_eq_half`; what is new is that the left-hand side is the measure of a set, obtained
from the joint events by `measure_wingAEvent_eq_sum` rather than by summing numbers. -/
theorem toReal_measure_wingAEvent_eq_half {M : ℕ} (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) (s : Sign) :
    (epistemicMeasure (Projectivization.mk ℂ ψ' hψ'0)
        (wingAEvent (momentContext (M + 1)) (pointerDecode e) s)).toReal
      = 1 / 2 := by
  rw [measure_wingAEvent_eq_sum, ENNReal.toReal_sum fun t _ => measure_ne_top _ _,
    Finset.sum_congr rfl fun t _ =>
      toReal_measure_wingEvent_eq_P_st a b e ψ' hψ'eq hψ'0 s t]
  exact marginal_a_eq_half a b s

/-- ★★★ **The B-wing's event probability is `1/2`**, symmetrically. -/
theorem toReal_measure_wingBEvent_eq_half {M : ℕ} (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) (t : Sign) :
    (epistemicMeasure (Projectivization.mk ℂ ψ' hψ'0)
        (wingBEvent (momentContext (M + 1)) (pointerDecode e) t)).toReal
      = 1 / 2 := by
  rw [measure_wingBEvent_eq_sum, ENNReal.toReal_sum fun s _ => measure_ne_top _ _,
    Finset.sum_congr rfl fun s _ =>
      toReal_measure_wingEvent_eq_P_st a b e ψ' hψ'eq hψ'0 s t]
  exact marginal_b_eq_half a b t

/-- ★★ **The two-wing events are macroscopic**: each is a preimage of #102's record string, so the
wing reading is visible at the level of the coarse projection and not only on the microstate. This
is obligation (5)'s shape at this instance. -/
theorem factorsThrough_wingEvent_pointerDecode {M : ℕ} (e : Fin 4 × Fin 4 ≃ Fin (M + 1))
    (st : Sign × Sign) :
    FactorsThrough (recordString fun _ : Fin 1 => momentContext (M + 1))
      (wingEvent (momentContext (M + 1)) (pointerDecode e) st) :=
  factorsThrough_coarseEvent (fun _ : Fin 1 => momentContext (M + 1)) 0 (pointerDecode e) st

/-! ### One physical record history

The flow carries the prepared ray to the dilated one (clause (6)), and
`measure_preimage_liftBase` carries the record event back, so the Born statement moves from the
post-measurement ray to where an experiment actually starts. -/

/-- The **prepared, pre-measurement** ray: the singlet in the wings' own bases, both pointers in
their ground state. -/
def preparedRay (a b : DetectorSetting) : CPN (4 * 4) :=
  Projectivization.mk ℂ
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
      (Matrix.toEuclideanLin localEmbedGround (localNudgeVec a b)))
    (localEmbed_ne_zero _ (localNudgeVec_ne_zero a b))

/-- The **post-measurement** ray, where `LF6`'s Born clause is stated. -/
def dilatedRay (a b : DetectorSetting) : CPN (4 * 4) :=
  Projectivization.mk ℂ
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
      (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (localDil_ne_zero _ (localNudgeVec_ne_zero a b))

/-- The local product flow carries the prepared ray to the dilated one: clause (6) at the local
preparation. -/
theorem localDeisolationFlow_preparedRay (a b : DetectorSetting) :
    localDeisolationFlow (preparedRay a b) = dilatedRay a b :=
  localDeisolationFlow_realises_localNaimark (localNudgeVec a b) (localNudgeVec_ne_zero a b)

theorem measurable_localDeisolationFlow : Measurable localDeisolationFlow :=
  (localDeisolationFlow_measurePreserving (Classical.arbitrary (CPN (4 * 4)))).measurable

/-- ★★★ **One physical record history.** The probability, in the **prepared** epistemic measure,
that the run ends with the two wings recording `(s, t)` is the singlet's joint distribution
`P_st a b s t`.

`LF6`'s Born clause is stated at the post-measurement ray; this is the same statement about the run
that *starts* at the prepared ray, which is what an experiment is. It is obligation (1) of #131,
and it needs all three pieces: clause (6) for the dynamics, `measure_preimage_liftBase` for the
measure, and the coarsening for the event. -/
theorem toReal_measure_preimage_wingEvent_eq_P_st (a b : DetectorSetting) (s t : Sign) :
    (epistemicMeasure (preparedRay a b)
        (liftBase localDeisolationFlow ⁻¹'
          wingEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) (s, t))).toReal
      = P_st a b s t := by
  rw [measure_preimage_liftBase
      (S := wingEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) (s, t))
      measurable_localDeisolationFlow _
      (measurableSet_coarseEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) (s, t)),
    localDeisolationFlow_preparedRay]
  exact toReal_measure_wingEvent_eq_P_st a b finProdFinEquiv _ rfl _ s t

/-- ★★ **The A-wing's marginal, along the flow from the prepared ray**, is `1/2`. -/
theorem toReal_measure_preimage_wingAEvent_eq_half (a b : DetectorSetting) (s : Sign) :
    (epistemicMeasure (preparedRay a b)
        (liftBase localDeisolationFlow ⁻¹'
          wingAEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) s)).toReal
      = 1 / 2 := by
  rw [measure_preimage_liftBase
      (S := wingAEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) s)
      measurable_localDeisolationFlow _
      (measurableSet_coarseEvent (momentContext (4 * 4))
        (Prod.fst ∘ pointerDecode finProdFinEquiv) s),
    localDeisolationFlow_preparedRay]
  exact toReal_measure_wingAEvent_eq_half a b finProdFinEquiv _ rfl _ s

/-- ★★ **Operational no-signalling along the dynamics.** A's record-event probability is the same
whether B's setting is `b` or `b'`, with each side evaluated in its own prepared measure and after
its own flow — so nothing B does can be read off A's record statistics.

This also **discharges, for the singlet, the premise** that
`RecordLayer.measure_wingAEvent_eq_of_fineSum_eq` leaves open: there the summed fine weights were
assumed equal, and here `LF3.marginal_a_eq_half` supplies that equality. #131 recorded the premise as
not discharged; for this model it now is. -/
theorem toReal_measure_preimage_wingAEvent_eq_of_setting (a b b' : DetectorSetting) (s : Sign) :
    (epistemicMeasure (preparedRay a b)
        (liftBase localDeisolationFlow ⁻¹'
          wingAEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) s)).toReal
      = (epistemicMeasure (preparedRay a b')
        (liftBase localDeisolationFlow ⁻¹'
          wingAEvent (momentContext (4 * 4)) (pointerDecode finProdFinEquiv) s)).toReal := by
  rw [toReal_measure_preimage_wingAEvent_eq_half a b s,
    toReal_measure_preimage_wingAEvent_eq_half a b' s]

end CSD.LF6

end

end
