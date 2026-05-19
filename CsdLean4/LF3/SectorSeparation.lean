import CsdLean4.LF3.Hamiltonian

/-!
# LF3 SectorSeparation: sector-state decomposition and pointer-leakage bounds

**Category:** 3-Local (LF3 sector-separated final state, per-wing pointer overlaps, leakage bound).

Paper §4 / §9.6. (Renamed from `BranchSeparation` in Phase 11, 2026-05-18,
to align with the volume-ratios reading: the four `(s, t)` regions are
eigensectors / volume domains, not Everettian branches.)

Defines the sector-separated final state, the per-wing pointer-overlap
observables, and the cross-sector readout mass; bundles the per-side leakage
parameters as `PointerLeakageBounds`; proves the sector-decomposition law
(definitional under `MeasurementUnitary.action`) and the operational
distinguishability bound.

The amplitude `cAmp : Sign → Sign → ℂ` is carried as an external parameter; the
concrete singlet amplitude is supplied later in `Singlet/State.lean` so the
import direction stays `SectorSeparation → Singlet/State`.
-/

open scoped BigOperators

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- Sector state `|B_{st}⟩ = |s, t⟩ ⊗ uA|φ_A⁰⟩ ⊗ uB|φ_B⁰⟩`, packaged through
    the joint eigenstate field of `MeasurementUnitary`. Each sector labels
    one of the four spin pointer-eigenspaces `(s, t) ∈ Sign × Sign`. -/
noncomputable def sectorState
    (M : MeasurementUnitary S) (s t : Sign)
    (φA0 : K_A) (φB0 : K_B) : H_SA :=
  M.jointEig (s, t) (M.ptrTransA s φA0) (M.ptrTransB t φB0)

/-- Sector-separated final state after the measurement unitary acts on the
    initial pointer state, with the amplitude `cAmp` (carrying the
    detector-setting dependence) supplied externally. -/
noncomputable def finalState
    (M : MeasurementUnitary S)
    (cAmp : Sign → Sign → ℂ)
    (φA0 : K_A) (φB0 : K_B) : H_SA :=
  ∑ st : Sign × Sign, cAmp st.1 st.2 • sectorState M st.1 st.2 φA0 φB0

/-- `s'`-sector Born weight of the A-pointer translated by `M.ptrTransA s`
    starting from `φA0`. -/
noncomputable def pointerOverlapA
    (S : SystemApparatusSetup K_A K_B H_SA) (M : MeasurementUnitary S)
    (φA0 : K_A) (s' s : Sign) : ℝ :=
  ‖S.ptrA.proj s' (M.ptrTransA s φA0)‖ ^ 2

/-- `t'`-sector Born weight of the B-pointer translated by `M.ptrTransB t`
    starting from `φB0`. -/
noncomputable def pointerOverlapB
    (S : SystemApparatusSetup K_A K_B H_SA) (M : MeasurementUnitary S)
    (φB0 : K_B) (t' t : Sign) : ℝ :=
  ‖S.ptrB.proj t' (M.ptrTransB t φB0)‖ ^ 2

/-- Total Born mass landing on a cross-sector readout after measurement: for
    each spin sector `(s, t)` with amplitude `cAmp s t`, the squared amplitude
    is weighted by the cross-sector overlap mass on each side. -/
noncomputable def crossSectorReadoutMass
    (S : SystemApparatusSetup K_A K_B H_SA) (M : MeasurementUnitary S)
    (cAmp : Sign → Sign → ℂ) (φA0 : K_A) (φB0 : K_B) : ℝ :=
  ∑ st : Sign × Sign,
    ‖cAmp st.1 st.2‖ ^ 2
      * (pointerOverlapA S M φA0 st.1.neg st.1
         + pointerOverlapB S M φB0 st.2.neg st.2)

/-- Per-side pointer-leakage bounds (paper §4.7). `εA`, `εB` upper-bound the
    wrong-sector pointer overlap on each wing; the `_right` fields lower-bound
    the correct-sector overlap. Parameterised over the apparatus `S`, the
    measurement unitary `M`, and the chosen initial pointer states `φA0, φB0`
    (needed to make the overlap predicates well-typed). -/
structure PointerLeakageBounds
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    (S : SystemApparatusSetup K_A K_B H_SA)
    (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) where
  /-- A-wing leakage parameter. -/
  εA      : ℝ
  /-- B-wing leakage parameter. -/
  εB      : ℝ
  /-- The A-wing leakage parameter is non-negative. -/
  εA_nn   : 0 ≤ εA
  /-- The B-wing leakage parameter is non-negative. -/
  εB_nn   : 0 ≤ εB
  /-- Wrong-sector overlap on the A side is bounded by `εA`. -/
  A_wrong : ∀ s, pointerOverlapA S M φA0 s.neg s ≤ εA
  /-- Wrong-sector overlap on the B side is bounded by `εB`. -/
  B_wrong : ∀ t, pointerOverlapB S M φB0 t.neg t ≤ εB
  /-- Right-sector overlap on the A side is at least `1 - εA`. -/
  A_right : ∀ s, 1 - εA ≤ pointerOverlapA S M φA0 s s
  /-- Right-sector overlap on the B side is at least `1 - εB`. -/
  B_right : ∀ t, 1 - εB ≤ pointerOverlapB S M φB0 t t

/-! ### Theorem targets (paper §4.11 / spec §9.6) -/

/-- Sector decomposition of the final state (paper §4.5): the final state is
    the four-term sum of sector states weighted by `cAmp`. Definitional
    unfolding of `finalState`. -/
theorem finalState_sector_decomposition
    (M : MeasurementUnitary S) (cAmp : Sign → Sign → ℂ)
    (φA0 : K_A) (φB0 : K_B) :
    finalState M cAmp φA0 φB0
      = ∑ st : Sign × Sign,
          cAmp st.1 st.2 • sectorState M st.1 st.2 φA0 φB0 := rfl

/-- Cross-sector readout mass is bounded by `εA + εB` given amplitude
    normalisation (paper §4.11). The proof sums the per-side leakage bounds
    weighted by `‖cAmp st‖²` and uses `∑ ‖cAmp st‖² ≤ 1`.

    **Disclosure-infrastructure status.** This theorem is standalone in
    the current Lean tree: no LF3 export consumes it. `LF3_finite_leakage_theorem`
    routes through the operator-form `LeakageCompat.sectorVolume_dev` field
    (in `Projectors/SectorVolume.lean`) instead, which is structurally a
    more direct bound on the quantity the chain capstones actually consume.
    The geometric `sector_separation_leakage_bound` here is kept as paper-side
    disclosure infrastructure: it makes the §4.11 inequality formally available
    even though the operator-form path supersedes it in the v1.00 chain. A v2
    refactor connecting the two would replace `LeakageCompat.sectorVolume_dev`
    with a derived form using this lemma plus a Cauchy-Schwarz step. Not
    scheduled for LF4. -/
theorem sector_separation_leakage_bound
    (M : MeasurementUnitary S) (cAmp : Sign → Sign → ℂ)
    (φA0 : K_A) (φB0 : K_B)
    (L : PointerLeakageBounds S M φA0 φB0)
    (hAmp : ∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2 ≤ 1) :
    crossSectorReadoutMass S M cAmp φA0 φB0 ≤ L.εA + L.εB := by
  unfold crossSectorReadoutMass
  have hSum_le :
      (∑ st : Sign × Sign,
          ‖cAmp st.1 st.2‖ ^ 2
            * (pointerOverlapA S M φA0 st.1.neg st.1
               + pointerOverlapB S M φB0 st.2.neg st.2))
        ≤ ∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2 * (L.εA + L.εB) := by
    apply Finset.sum_le_sum
    intro st _
    have hAbs_nn : 0 ≤ ‖cAmp st.1 st.2‖ ^ 2 := sq_nonneg _
    have hOverlap_le :
        pointerOverlapA S M φA0 st.1.neg st.1
          + pointerOverlapB S M φB0 st.2.neg st.2
          ≤ L.εA + L.εB :=
      add_le_add (L.A_wrong st.1) (L.B_wrong st.2)
    exact mul_le_mul_of_nonneg_left hOverlap_le hAbs_nn
  have hε_nn : 0 ≤ L.εA + L.εB := add_nonneg L.εA_nn L.εB_nn
  have hFactor :
      (∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2 * (L.εA + L.εB))
        = (∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2) * (L.εA + L.εB) := by
    rw [← Finset.sum_mul]
  have hBudget :
      (∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2) * (L.εA + L.εB)
        ≤ 1 * (L.εA + L.εB) :=
    mul_le_mul_of_nonneg_right hAmp hε_nn
  calc
    _ ≤ ∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2 * (L.εA + L.εB) := hSum_le
    _ = (∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2) * (L.εA + L.εB) := hFactor
    _ ≤ 1 * (L.εA + L.εB) := hBudget
    _ = L.εA + L.εB := by ring

end LF3
end CSD
