/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRecordHistoryBridge
public import CsdLean4.RecordLayer.UnifiedRadarRay
public import CsdLean4.RecordLayer.UnifiedTurnedRays
public import CsdLean4.SigmaLayer.IsolationPreparation

/-!
# A preparation of positive measure for the radar's record history

**Category:** 7-SigmaLayer. BACKLOG ~~#438~~, last brick (Task 2 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (2)).

`RecordLayer/UnifiedRecordHistoryBridge.lean` makes the five tick counts of the radar theorem
recorded facts whose events are measurable sets of initial states, and shows the run's start
in their compatible region for the family's ray and an open set of pointer angles. One ray
has Fubini–Study measure zero, so that was not a preparation. Here the compatible region of
a five-fact history is shown to have non-zero `μ_FS ⊗ vol⁵` measure.

## The turned rays, relabelled

* ★★ `fsMeasure_image_turnedRays_pos` — the image of `turnedRays P r` under the labelling of
  the basis has positive Fubini–Study measure, for any reference point.

## The starts of the walled chain's run

* `RadarCountBounds` — the four comparisons of `WallRadarGeometry` as one statement about
  five counts;
* `radarStartRay`, ★ `wallRunRay_eq_flow` — the run from any ray is the orbit of its start
  under `wallDynamics`;
* ★★ `WallRadarGeometry.mem_compatibleSet_ray` — its counts are a record history of the start;
* `radarStartSet`, ★★★ `pentaMuL_radarStartSet_pos` — the starts with the ray turned within
  `r` and the five angles within `ρ` have positive `μ_FS ⊗ vol⁵` measure: the set contains a
  product, and the product measure of a product is the product of the measures.

## The preparation

* ★★★ `csd_radar_history_preparation` — for `k ≥ 100` and an even ring with `M ≥ 210000 N³`
  there are strengths such that, for every labelling, every reference point and every choice
  of flow times in the five reading windows, there are five counts whose history is a
  `HistoryPreparation` of the walled chain's dynamics and which satisfy the Lorentz statement
  within `152 K/k`, the bound on the rest observer's time within `53 K/k`, and the comparison
  of intervals.

## Honest scope

⚠️ **The counts are not named.** Every start of `radarStartSet` is compatible with some
history whose counts satisfy the bounds; there are countably many histories; so one of them
has a compatible region of non-zero measure. Which one is not said, and the counts may
depend on the labelling, the reference point and the reading times. It is not stated that
the family's own start lies in that region.

⚠️ **Non-zero, with no value.** No lower bound for the measure is given. The set it comes
from has radii `1/(12000 k²)` and `1/(24000 k²)`, which shrink along the family.

⚠️ **Positive measure in the arena, not in a fibre.** The measure is `μ_FS ⊗ vol⁵` of the
whole arena (`pentaMuL`), with the rays varied. No fibre measure by disintegration is used.

⚠️ **Conditioning on the history is ordinary conditioning.** `HistoryPreparation.toPreparation`
gives the normalised restriction of the arena's measure to the compatible region. That is a
statement about the measure, not an interaction, and no register holds the counts.

⚠️ **The strengths are asserted to exist.** One family, one velocity, one distance, `1 + 1`.
The Lorentz statement is that of #402 about five tick counts in flow-time windows.

References: `specs/BACKLOG.md` ~~#438~~, ~~#436~~; `specs/unified-record-spacetime-plan.md`
(UO-25, UD-208, UD-213, UD-214, UD-215, UD-218, UD-219);
`RecordLayer/UnifiedRecordHistoryBridge.lean` (`wallDynamics`, `wallReadout`, `radarHistory`,
`TickReadout.mem_compatibleSet_startFacts`); `RecordLayer/UnifiedRadarRay.lean`
(`radar_family_lorentz_ray`); `RecordLayer/UnifiedTurnedRays.lean` (`turnedRays`);
`RecordLayer/UnifiedRadarGeometry.lean` (`WallRadarLorentz.geometry`, `isOpen_nearStart`,
`isOpenPosMeasure_volume_prod`); `SigmaLayer/IsolationPreparation.lean`
(`HistoryPreparation`); `CV/ArenaIndexBridge.lean` (`arenaKick_reindex`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.SigmaLayer MeasureTheory Set CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup
open scoped ContDiff Manifold Matrix Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The turned rays, relabelled -/

section Rays

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- ★★ **The turned rays keep positive Fubini–Study measure under a relabelling of the
basis.** The image of `turnedRays P r` under `idxArenaEquiv e` has positive measure for any
reference point of the measure on the relabelled space. -/
theorem fsMeasure_image_turnedRays_pos (e : ι ≃ κ) (p₀ : GenArena κ) (P : GenArena ι)
    {r : ℝ} (hr : 0 < r) :
    0 < fsMeasure p₀ (idxArenaEquiv e '' turnedRays P r) := by
  obtain ⟨V, hV⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup κ ℂ) p₀ (idxArenaEquiv e P)
  have hcont : Continuous fun U : Matrix.unitaryGroup κ ℂ =>
      ‖((U * V⁻¹).val.submatrix e e : Matrix ι ι ℂ) - 1‖ :=
    (((continuous_subtype_val.comp (continuous_id.mul continuous_const)).matrix_submatrix e e).sub
      continuous_const).norm
  have hopen : IsOpen {U : Matrix.unitaryGroup κ ℂ |
      ‖((U * V⁻¹).val.submatrix e e : Matrix ι ι ℂ) - 1‖ < r} :=
    isOpen_lt hcont continuous_const
  have hne : {U : Matrix.unitaryGroup κ ℂ |
      ‖((U * V⁻¹).val.submatrix e e : Matrix ι ι ℂ) - 1‖ < r}.Nonempty := by
    refine ⟨V, ?_⟩
    show ‖((V * V⁻¹).val.submatrix e e : Matrix ι ι ℂ) - 1‖ < r
    rw [mul_inv_cancel]
    simpa using hr
  have hsub : {U : Matrix.unitaryGroup κ ℂ |
      ‖((U * V⁻¹).val.submatrix e e : Matrix ι ι ℂ) - 1‖ < r}
      ⊆ orbitMap p₀ ⁻¹' (idxArenaEquiv e '' turnedRays P r) := by
    intro U hU
    refine ⟨arenaKick (idxUnitary e.symm (U * V⁻¹)) P,
      ⟨idxUnitary e.symm (U * V⁻¹), hU, rfl⟩, ?_⟩
    have h1 : idxUnitary e (idxUnitary e.symm (U * V⁻¹)) = U * V⁻¹ := by
      apply Subtype.ext
      simp [idxUnitary]
    show idxArenaEquiv e (arenaKick (idxUnitary e.symm (U * V⁻¹)) P) = orbitMap p₀ U
    rw [← arenaKick_reindex, h1, arenaKick_eq_smul', ← hV, smul_smul, inv_mul_cancel_right,
      orbitMap]
  calc 0 < unitaryHaarProb {U : Matrix.unitaryGroup κ ℂ |
        ‖((U * V⁻¹).val.submatrix e e : Matrix ι ι ℂ) - 1‖ < r} :=
        hopen.measure_pos unitaryHaarProb hne
    _ ≤ unitaryHaarProb (orbitMap p₀ ⁻¹' (idxArenaEquiv e '' turnedRays P r)) :=
        measure_mono hsub
    _ ≤ fsMeasure p₀ (idxArenaEquiv e '' turnedRays P r) :=
        Measure.le_map_apply (orbit_map_measurable p₀).aemeasurable _

end Rays

/-! ### The starts of the walled chain's run -/

/-- **The four comparisons of one radar run's counts** (`WallRadarGeometry`, #432): the boost
of the rest observer's coordinates of the relay event against the moving observer's, component
by component; the rest observer's time; and the two intervals. -/
def RadarCountBounds (R₀ v E₁ E₂ T₀ B : ℝ) (Ne Nr Nμ Nρ Nm : ℕ) : Prop :=
  |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).1 - (movingEvent R₀ Ne Nr Nμ).1| ≤ E₁
  ∧ |(lorentzBoost 1 (-v) (restEvent R₀ Nρ Nm)).2 - (movingEvent R₀ Ne Nr Nμ).2| ≤ E₂
  ∧ |(restEvent R₀ Nρ Nm).1 - T₀| ≤ B
  ∧ |radarInterval (movingEvent R₀ Ne Nr Nμ) - radarInterval (restEvent R₀ Nρ Nm)|
      ≤ E₁ * (2 * ((|T₀| + B) / Real.sqrt (1 - v ^ 2)) + E₁)
        + E₂ * (2 * ((|T₀| + B) / Real.sqrt (1 - v ^ 2)) + E₂)

section WallRay

variable (n N : ℕ) {M : ℕ} (μ Δ w gA gB : ℝ) {D : ℕ}
  (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
    × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1))

/-- **The start of a run from any ray of the composite carrier**, as one point of the
arena. -/
def radarStartRay
    (P : GenArena ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2))))
    (θ ψ χ ξ ζ : KTorus) : PentaSigma D :=
  (((((idxArenaEquiv e P, θ), ψ), χ), ξ), ζ)

/-- ★ **The walled chain's run from any ray is the orbit of its start under the dynamics.** -/
theorem wallRunRay_eq_flow
    (P : GenArena ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2))))
    (θ ψ χ ξ ζ : KTorus) (t : ℝ) :
    wallRunRay n N M μ Δ w gA gB e P θ ψ χ ξ ζ t
      = (wallDynamics n N M μ Δ w gA gB e p₀).flow t (radarStartRay e P θ ψ χ ξ ζ) :=
  rfl

variable {n N μ Δ w gA gB}

set_option synthInstance.maxSize 4096 in
/-- ★★ **The counts of a run from any ray are a record history of its start.** From the
conclusion of the radar theorem for `wallRunRay`: the start is in the compatible region of
the five facts, and the counts satisfy the four comparisons. -/
theorem WallRadarGeometry.mem_compatibleSet_ray
    {P : GenArena ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)))}
    {θ ψ χ ξ ζ : KTorus} {R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ T₀ B : ℝ}
    (h : WallRadarGeometry M (fun e => wallRunRay n N M μ Δ w gA gB e P θ ψ χ ξ ζ)
      R₀ v tb t3 t4 t5 tbM tcM tbR tcR E₁ E₂ T₀ B)
    {se sr sμ sρ sm : ℝ} (hse1 : tb ≤ se) (hse2 : se ≤ t3) (hsr1 : t4 ≤ sr) (hsr2 : sr ≤ t5)
    (hsμ1 : tbM ≤ sμ) (hsμ2 : sμ ≤ tcM) (hsρ1 : tbR ≤ sρ) (hsρ2 : sρ ≤ tcR)
    (hsm1 : tbM ≤ sm) (hsm2 : sm ≤ tcM) :
    ∃ Ne Nr Nμ Nρ Nm : ℕ,
      radarStartRay e P θ ψ χ ξ ζ
          ∈ compatibleSet (wallReadout n N M μ Δ w gA gB e p₀).semantics
            (radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm)
      ∧ RadarCountBounds R₀ v E₁ E₂ T₀ B Ne Nr Nμ Nρ Nm := by
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, i1, i2, i3, i4⟩ :=
    h D e se hse1 hse2 sr hsr1 hsr2 sμ hsμ1 hsμ2 sρ hsρ1 hsρ2 sm hsm1 hsm2
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, ?_, i1, i2, i3, i4⟩
  refine (wallReadout n N M μ Δ w gA gB e p₀).mem_compatibleSet_startFacts
    [(0, se, Ne), (1, sr, Nr), (2, sμ, Nμ), (3, sρ, Nρ), (4, sm, Nm)] _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [c1, c2, c3, c4, c5]

/-- **The starts near a ray**: the ray `P` turned by a unitary within `r` of the identity,
with five pointer angles within `ρ` of `(1/12, 0)`. -/
def radarStartSet
    (P : GenArena ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2))))
    (r ρ : ℝ) : Set (PentaSigma D) :=
  {x | ∃ W : Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2))) ℂ, ‖W.val - 1‖ < r ∧ ∃ θ ψ χ ξ ζ : KTorus,
    NearStart ρ θ ∧ NearStart ρ ψ ∧ NearStart ρ χ ∧ NearStart ρ ξ ∧ NearStart ρ ζ
      ∧ x = radarStartRay e (arenaKick W P) θ ψ χ ξ ζ}

set_option synthInstance.maxSize 4096 in
/-- ★★★ **The starts near a ray have positive measure in the arena**, for `μ_FS ⊗ vol⁵` with
any reference point: the set contains the product of the relabelled turned rays and five
copies of the box of angles. -/
theorem pentaMuL_radarStartSet_pos
    (P : GenArena ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2))))
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    0 < pentaMuL p₀ (radarStartSet e P r ρ) := by
  have hsub : (((((idxArenaEquiv e '' turnedRays P r) ×ˢ {θ : KTorus | NearStart ρ θ})
      ×ˢ {θ : KTorus | NearStart ρ θ}) ×ˢ {θ : KTorus | NearStart ρ θ})
      ×ˢ {θ : KTorus | NearStart ρ θ}) ×ˢ {θ : KTorus | NearStart ρ θ}
      ⊆ radarStartSet e P r ρ := by
    rintro ⟨⟨⟨⟨⟨a, θ⟩, ψ⟩, χ⟩, ξ⟩, ζ⟩ ⟨⟨⟨⟨⟨⟨y, ⟨W, hW, rfl⟩, rfl⟩, hθ⟩, hψ⟩, hχ⟩, hξ⟩, hζ⟩
    exact ⟨W, hW, θ, ψ, χ, ξ, ζ, hθ, hψ, hχ, hξ, hζ, rfl⟩
  have hpos : (volume : Measure KTorus).IsOpenPosMeasure := isOpenPosMeasure_volume_prod
  have hB : (volume : Measure KTorus) {θ : KTorus | NearStart ρ θ} ≠ 0 :=
    ((isOpen_nearStart ρ).measure_pos volume ⟨_, nearStart_start hρ⟩).ne'
  have hA : fsMeasure p₀ (idxArenaEquiv e '' turnedRays P r) ≠ 0 :=
    (fsMeasure_image_turnedRays_pos e p₀ P hr).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [pentaMuL, Measure.prod_prod, quadMuL, Measure.prod_prod, triMuL, Measure.prod_prod,
    echoMuL, Measure.prod_prod, kMuL, Measure.prod_prod]
  exact ENNReal.mul_pos (ENNReal.mul_pos (ENNReal.mul_pos (ENNReal.mul_pos
    (ENNReal.mul_pos hA hB).ne' hB).ne' hB).ne' hB).ne' hB

end WallRay

/-! ### The preparation -/

section Family

set_option synthInstance.maxSize 4096 in
/-- ★★★ **A preparation of positive measure for the radar's record history.** For `k ≥ 100`
and a ring with an even number `M + 1 = 2H` of sites, `M ≥ 210000 N³`, with the carriers,
gates and times of `radar_family_lorentz`: there are strengths `g_A, g_B > 0` such that, for
every labelling of the basis, every reference point of the measure and every choice of flow
times in the five reading windows, there are five counts for which

* the history of the five recorded facts with those counts has a compatible region of
  non-zero `μ_FS ⊗ vol⁵` measure, so it is a `HistoryPreparation` of the walled chain's
  dynamics; and
* the counts satisfy the Lorentz statement within `152 K/k`, the bound on the rest
  observer's time within `53 K/k`, and the comparison of intervals. -/
theorem csd_radar_history_preparation {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ gA gB : ℝ, 0 < gA ∧ 0 < gB
      ∧ ∀ (D : ℕ) (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
          × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1)),
        ∀ se, famTb k ≤ se → se ≤ famT3 k → ∀ sr, famT4 k ≤ sr → sr ≤ famT5 k →
        ∀ sμ, famTbM k M ≤ sμ → sμ ≤ famTcM k M → ∀ sρ, famTbR k M ≤ sρ → sρ ≤ famTcR k M →
        ∀ sm, famTbM k M ≤ sm → sm ≤ famTcM k M →
        ∃ (Ne Nr Nμ Nρ Nm : ℕ)
          (HP : HistoryPreparation
            (wallDynamics (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
              gA gB e p₀) (tickSignature (Fin 5))
            (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
              gA gB e p₀).semantics),
          HP.history = radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm
          ∧ RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
              (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
              (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
              (53 * (wallK k / k)) Ne Nr Nμ Nρ Nm := by
  obtain ⟨hψ, gA, gB, hΨA, hΨB, a1, -, a3, -, hall⟩ := radar_family_lorentz_ray hk hM hH
  refine ⟨gA, gB, a1, a3, ?_⟩
  intro D e p₀ se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  have hX0 : (0 : ℝ) < k := by
    have : (100 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [this]
  have hv := vRel_half_one
  have habs : |vRel 1 1 (1 / 2)| < 1 := by
    rw [abs_of_pos hv.1]
    linarith only [hv.2]
  have hr : (0 : ℝ) < 1 / (12000 * (k : ℝ) ^ 2) := by positivity
  have hρ : (0 : ℝ) < 1 / (24000 * (k : ℝ) ^ 2) := by positivity
  have hpos := pentaMuL_radarStartSet_pos e p₀
    (prodRay (chainRay _ hψ) (prodRay (deviceRay (deviceShift (H : ZMod (M + 1)) _)
      (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB))) hr hρ
  -- every start of the set is compatible with a history whose counts satisfy the bounds
  have hcov : radarStartSet e
      (prodRay (chainRay _ hψ) (prodRay (deviceRay (deviceShift (H : ZMod (M + 1)) _)
        (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB)))
      (1 / (12000 * (k : ℝ) ^ 2)) (1 / (24000 * (k : ℝ) ^ 2))
      ⊆ ⋃ c : ℕ × ℕ × ℕ × ℕ × ℕ,
        {x | RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
              (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
              (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
              (53 * (wallK k / k)) c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
          ∧ x ∈ compatibleSet
            (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
              gA gB e p₀).semantics
            (radarHistory se sr sμ sρ sm c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)} := by
    rintro x ⟨W, hW, θ, ψ, χ, ξ, ζ, hθ, hψ', hχ, hξ, hζ, rfl⟩
    obtain ⟨Ne, Nr, Nμ, Nρ, Nm, hx, hb⟩ :=
      ((hall W hW.le θ ψ χ ξ ζ hθ hψ' hχ hξ hζ).geometry habs).mem_compatibleSet_ray e p₀
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact Set.mem_iUnion.2 ⟨(Ne, Nr, Nμ, Nρ, Nm), hb, hx⟩
  by_contra hcon
  refine hpos.ne' (measure_mono_null hcov (measure_iUnion_null fun c => ?_))
  by_contra hne
  have hb : RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
      (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
      (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
      (53 * (wallK k / k)) c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 := by
    by_contra hb
    have hnull : ∀ S : Set (PentaSigma D), S = ∅ → pentaMuL p₀ S = 0 := fun S h => by
      rw [h]
      exact measure_empty
    exact hne (hnull _ (Set.eq_empty_of_forall_notMem fun x hx => hb hx.1))
  exact hcon ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2,
    ⟨radarHistory se sr sμ sρ sm c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2,
      fun h0 => hne (measure_mono_null (fun _ hx => hx.2) h0)⟩, rfl, hb⟩

end Family

end CSD.RecordLayer

end
