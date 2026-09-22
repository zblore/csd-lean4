/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.SingletKahler
public import CsdLean4.LF4.KahlerFlow

/-!
# SL-2: a genuine `Φ ≠ id` on the concrete ENTANGLED (singlet) sector

**Category:** 3-Local (a genuine `Φ ≠ id` on the concrete ENTANGLED (singlet) sector).

D1c-1 (`LF4/KahlerFlow.lean`) discharged the "`Φ = id` in the concrete Kähler
instance" debt for the GENERIC sector: `kSectorDataFlow` carries the non-identity
measure-preserving flow `Φ = kFlow sh` (a free `T²`-fibre translation), and
`kFlow_frequency_convergence` makes its Liouville-preservation *load-bearing* (it
pins the law of the evolved trials `kFlow sh ∘ sample`).

This module does the same for the **entangled** sector — the two-qubit singlet on
`Σ = ℂℙ³ × T²` (`LF4/SingletKahler.lean`), SL-2. The singlet preparation
`ofKählerPreparation` was built over `kSectorData` (`Φ = id`); here it is rebuilt
over `kSectorDataFlow p₀ sh` (`Φ = kFlow sh`, nonidentity when `sh ≠ 0`), and the per-sector frequency
capstone fires with the trials genuinely **evolved by the sector's own flow**.

The mechanism is exact and requires no new engine. An LF1 `OutcomeRegion`'s scored
event is `preEvent = Φ ⁻¹' Ω` (`LF1/Outcomes.lean`), so with `Φ = kFlow sh` the
capstone scores `X ⁻¹' preEvent = (kFlow sh ∘ X) ⁻¹' kRegion` — each sampled
microstate is pushed one flow-step before its outcome block is read. Preservation of the preparation law
is load-bearing through `bridge_op_p`: the carving identity now reads
`kMuPsi (kFlow sh ⁻¹' kRegion) = kMuPsi (kRegion) = P_st`, the first equality being
`kFlow_measurePreserving_muPsi` (the singlet analogue of `kFlow_measurePreserving`).
So the empirical frequency of the flow-evolved singlet trials still converges a.s.
to the Born weight `P_st`.

## Deliverables

* `kFlow_measurePreserving_muPsi` — `kFlow sh` preserves the singlet fibre law
  `μψ = δ_{[singlet]} ⊗ vol_{T²}` (fixes the base ray, translates the fibre);
* `ofKählerPreparationFlow` — the singlet `PureSingletPreparation` over the
  fibre-flow sector `kSectorDataFlow p₀ sh`;
* `ofKählerPreparationFlow_phi_ne_id` — its sector carries `Φ ≠ id` when `sh ≠ 0`;
* `ofKählerPreparationFlow_flow_frequency_convergence` — the per-sector empirical
  frequencies of the trials **evolved by `kFlow sh`** converge a.s. to `P_st`.

## Honest scope (unchanged from D1c-1)

`kFlow` is a free fibre translation. It fixes the projective ray and is
nonidentity when `sh ≠ 0`; the constructors and frequency theorem also
allow `sh = 0`. The preservation proof here concerns the preparation law
`kMuPsi`, separately from ambient Liouville measure. It does not construct
a measurement interaction or a Hamiltonian flow from the Kähler form.
The singlet law and calibrated arcs are supplied by the concrete model.
Those anchored arcs overlap; the capstone gives per-event frequencies,
without asserting a partition into exclusive outcomes. The proof uses
only the foundational axioms.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open CSD.LF3

namespace CSD
namespace LF4

variable (ctx : CSD.LF3.MeasurementContext)

/-! ### `kFlow` preserves the singlet fibre law `μψ` -/

/-- **The fibre flow preserves the singlet fibre law.** `kFlow sh` fixes the base
ray (so it preserves the Dirac `δ_{[singlet]}` on `ℂℙ³`) and translates the `T²`
fibre (so it preserves the Haar volume there). This is the singlet analogue of
`kFlow_measurePreserving`, and the preparation-law preservation that makes `Φ`
load-bearing in the frequency capstone below. -/
theorem kFlow_measurePreserving_muPsi (sh : KTorus) :
    MeasurePreserving (kFlow (N := 4) sh) kMuPsi kMuPsi := by
  have h1 : MeasurePreserving (fun x : AddCircle (1 : ℝ) => sh.1 + x)
      (volume : Measure (AddCircle (1 : ℝ))) (volume : Measure (AddCircle (1 : ℝ))) :=
    measurePreserving_add_left _ sh.1
  have h2 : MeasurePreserving (fun x : AddCircle (1 : ℝ) => sh.2 + x)
      (volume : Measure (AddCircle (1 : ℝ))) (volume : Measure (AddCircle (1 : ℝ))) :=
    measurePreserving_add_left _ sh.2
  have htransl : MeasurePreserving (fun t : KTorus => sh + t)
      (volume : Measure KTorus) (volume : Measure KTorus) := h1.prod h2
  exact (MeasurePreserving.id (Measure.dirac singletRay)).prod htransl

/-! ### The preparation bundle over the fibre-flow sector

The bridge and static pure-preparation components reference the sector through its
projection `π = Prod.fst` and Liouville measure `μL = kMuL p₀` — both DEFINITIONALLY
equal between `kSectorData` and `kSectorDataFlow` (they differ only in `Φ`). So the
bridge and static preparation proofs port verbatim. The scored pre-event
changes, and its mass proof uses preservation of `kMuPsi`. -/

/-- The axiom-free measure bridge for the fibre-flow sector (`c = 1`, `π∗μL = μFS`
via `Measure.fst_prod`), identical to `kBridge` — the bridge does not see `Φ`. -/
noncomputable def kBridgeFlow (p₀ : CPN 4) (sh : KTorus) :
    LF2.MeasureBridgeData (kSectorDataFlow p₀ sh) (fsMeasure p₀) where
  is_inv := fun U =>
    ⟨(continuous_const_smul U).measurable, fsMeasure_smul_invariant U p₀⟩
  c := 1
  bridge_eq := by
    show Measure.map (kSectorDataFlow p₀ sh).π
        ((kSectorDataFlow p₀ sh).μL : Measure (KSigma 4)) = 1 • fsMeasure p₀
    rw [one_smul]
    show Measure.map Prod.fst (kMuL p₀) = fsMeasure p₀
    rw [kMuL, ← Measure.fst, Measure.fst_prod]

/-- The singlet `PurePreparation` over the fibre-flow sector (constant `rep`, Dirac
concentration through `π = Prod.fst`), identical to `kPurePrep`. -/
noncomputable def kPurePrepFlow (p₀ : CPN 4) (sh : KTorus) :
    LF2.PurePreparation (kSectorDataFlow p₀ sh) kMuPsi 4 where
  ψ := singletPsi
  unit_ψ := singletPsi_norm
  rep := kRep
  hrep_unit := kRep_unit
  hrep_meas := kRep_meas
  ray_point := singletRay
  rep_at_ray := rfl
  push_dirac := by
    show Measure.map (kSectorDataFlow p₀ sh).π kMuPsi = Measure.dirac singletRay
    exact kMuPsi_push

/-- The per-sector outcome region over the `Φ ≠ id` ontic setup: same carved set
`kRegion` as `kOutcomeRegion` (the region is base-flow-agnostic). Its scored event
is `preEvent = kFlow sh ⁻¹' kRegion` — the flow enters HERE. -/
noncomputable def kOutcomeRegionFlow (p₀ : CPN 4) (sh : KTorus) (s t : Sign) :
    (kOnticSetupFlow p₀ sh).OutcomeRegion where
  Ω := kRegion ctx s t
  hΩ_meas := kRegion_measurable ctx s t

/-- **SL-2: the singlet preparation on the fibre-flow sector.** The concrete
`LF3.PureSingletPreparation` for the two-qubit singlet over `kSectorDataFlow p₀ sh`
(`Φ = kFlow sh`, nonidentity when `sh ≠ 0`). Identical to `ofKählerPreparation` except the underlying
sector carries the fibre flow, so the scored event is
`preEvent = kFlow sh ⁻¹' kRegion`. `bridge_op_p` holds because
`kMuPsi (kFlow sh ⁻¹' kRegion) = kMuPsi (kRegion) = P_st` — the first equality is
`kFlow`'s preservation of the preparation law (`kFlow_measurePreserving_muPsi`), now
load-bearing; the second is the carving identity `kMuPsi_kRegion`. -/
noncomputable def ofKählerPreparationFlow
    (p₀ : CPN 4) (sh : KTorus) (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t) :
    LF3.PureSingletPreparation (kSectorDataFlow p₀ sh) ctx 4 :=
  LF3.PureSingletPreparation.ofWeights
    kMuPsi inferInstance
    (fsMeasure p₀) inferInstance
    (kBridgeFlow p₀ sh)
    (kPurePrepFlow p₀ sh)
    (by decide)
    (kJED ctx hgen)
    (kOutcomeRegionFlow ctx p₀ sh)
    (by
      intro s t
      show kMuPsi (kFlow sh ⁻¹' kRegion ctx s t) = _
      rw [(kFlow_measurePreserving_muPsi sh).measure_preimage
            (kRegion_measurable ctx s t).nullMeasurableSet,
          kMuPsi_kRegion])

/-- The underlying sector genuinely carries `Φ ≠ id` (for any nonzero fibre shift),
via `kFlow_ne_id`. This is the SL-2 headline: the concrete ENTANGLED sector now
carries a genuine non-identity flow. -/
theorem ofKählerPreparationFlow_phi_ne_id (p₀ : CPN 4) {sh : KTorus} (hsh : sh ≠ 0) :
    (kSectorDataFlow p₀ sh).toOntic.Φ ≠ id :=
  kFlow_ne_id p₀ hsh

/-- The scored event of the flow preparation is the flow-pullback of the carved
region: `preEvent = kFlow sh ⁻¹' kRegion`. So scoring trial `X n` on it reads
`X n ⁻¹' preEvent = (kFlow sh ∘ X n) ⁻¹' kRegion` — the microstate is evolved one
flow-step before its outcome block is checked. -/
lemma ofKählerPreparationFlow_preEvent
    (p₀ : CPN 4) (sh : KTorus) (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t)
    (s t : Sign) :
    ((ofKählerPreparationFlow ctx p₀ sh hgen).O_region s t).preEvent
      = kFlow sh ⁻¹' kRegion ctx s t := rfl

/-! ### The load-bearing capstone: frequencies of flow-evolved singlet trials -/

open Filter Topology in
/-- The singlet event frequencies survive the fibre flow. Measurable trials
    have common law `kMuPsi` and pairwise independent evolved indicators for
    each sector. Applying `kFlow sh` to every sample retains the calibrated
    masses because `kFlow_measurePreserving_muPsi` preserves this law.
    The result includes the zero shift; nonzero shifts give nonidentity
    flow. It proves per-event convergence, not an exclusive outcome law. -/
theorem ofKählerPreparationFlow_flow_frequency_convergence
    (p₀ : CPN 4) (sh : KTorus) (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = kMuPsi)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator ((kFlow sh ∘ X n) ⁻¹' kRegion ctx s t) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator ((kFlow sh ∘ X i) ⁻¹' kRegion ctx s t)
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (P_st ctx.a ctx.b s t)) := by
  intro s t
  have hind' : ∀ s t,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator
              (X n ⁻¹' ((ofKählerPreparationFlow ctx p₀ sh hgen).O_region s t).preEvent)
              (fun _ => (1 : ℝ)))) := fun s t => by
    simpa only [ofKählerPreparationFlow_preEvent, ← Set.preimage_comp] using hindep s t
  have hconv := LF3.LF3_singlet_frequency_convergence
    (kSectorDataFlow p₀ sh) ctx (ofKählerPreparationFlow ctx p₀ sh hgen) hX hlaw hind' s t
  simpa only [ofKählerPreparationFlow_preEvent, ← Set.preimage_comp] using hconv

end LF4
end CSD
