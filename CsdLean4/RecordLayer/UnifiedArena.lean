/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapClosure
public import CsdLean4.SigmaLayer.FiniteQMClosure

/-!
# SigmaLayer/UnifiedArena: the engine migration — operational content on the swap arena

**Category:** 7-SigmaLayer (the record layer — arena unification, step 2 of 2).

## What this is

`CsdFiniteQMClosure` was honest that it conjoined an **operational** closure on
`productDynamics` over `ℂℙ^M × T²` with a **dynamical** closure on the swap arena — *"both
hold"*, not *"one theory covers both"*. This module ends that split **for the rank-one
projective tier**: one arena carries the isolated Schrödinger dynamics AND the rank-one
measurement dynamics AND Born AND rank-one Lüders AND mixed-state weights/frequencies.
*(Scope corrected 2026-08-02, second external review: the **degenerate** update lives on the
companion projective-join witness (`JoinLuders.lean`), the any-basis closure is the separate
`RotatedSwapClosure`, and mixed/POVM **dynamics** remain open — a single
projective-measurement capstone bundling all of these is a recorded open item,
`specs/BACKLOG.md`.)*

The arena is `UnifiedArena M = ((ℂℙ^M × T²) × T²_R) × (Fin (M+1) → Σ_sys)` — system (base ray +
system fibre), pointer register, calibrated ancilla bank. Its Liouville measure
`arenaLiouville = (kMuL ⊗ vol) ⊗ Π kMuL` is `swapMeasure` at `μs = kMuL p₀`, so
**`swapEvolve_measurePreserving` already provides measurement-preservation against it** — the
measure the measurement dynamics preserves *is* the Liouville measure the isolated flow
preserves. That coincidence is the engine migration's mathematical content.

## The field mapping from `FiniteQMClosure` (all eleven accounted for)

| operational field | fate on the unified arena |
|---|---|
| `isolated_flow_measure_preserving` | **migrated** — `arenaIso` (the lifted `exp(-itH)`) preserves `arenaLiouville` |
| `schrodinger_projection` | **migrated** — `arenaRay ∘ arenaIso t = productProjectedFlow t ∘ arenaRay` |
| `fubini_study_bridge` | **migrated** — `(arenaRay)_* arenaLiouville = μ_FS` |
| `measurement_preserving` | **migrated & upgraded** — the *record-creating* propagator `swapEvolve` preserves `arenaLiouville` (the operational field's de-isolation interaction did not create persistent records) |
| `readout_ae_total`, `records_established`, `records_time_physical` | **superseded** — the `measurement` field's record creation/persistence is context-fixed and dynamical, strictly stronger than the preparation-indexed `vnPointerOutcome` readout (the MD-1 repair) |
| `born_frequency` | **migrated** — same i.i.d. LLN, trials sampling `arenaLiouville`, regions the arena cylinders of the Born regions |
| `conditioning_is_luders` | **superseded** — the `measurement` field's `luders_followup` is the *dynamical* Lüders update (collapse as pushforward), strictly stronger than conditioning-as-prediction |
| `mixed_born` | **migrated** — spectral mixtures of arena cylinder measures reproduce `Tr(ρEᵢ)` |
| `mixed_born_frequency` | **migrated** (same day, second pass) — `arena_mixed_born_frequency`: the two-stage mixture LLN through the system-slot marginal, with `arenaMixtureRegion` a `Prod.map` preimage so the transfer is `rfl`-level |

## ⚠️ Honest scope

* The isolated lift `arenaIso` acts by `exp(-itH)` on the **system slot** and identity on
  register and bank: the apparatus is idle between measurements, and the bank is re-calibrated
  per round (the calibration posit of `SwapLuders.lean`, unchanged).
* The propagator alternation — isolate, then measure, then isolate — is now a **theorem**
  (`arena_round_trip`, second pass same day): the record is created from the evolved state's
  selector and survives subsequent isolated evolution, because the pointer register is a
  conserved coordinate of the lifted flow (`readout_arenaIso` — definitional). The composition
  was not even stateable before the migration.
* Everything the predecessor capstones honestly scoped stays scoped: the piecewise-Hamiltonian
  classification of the measurement propagator (`PiecewiseHamiltonian.lean`), the calibration
  posit, rank-one first measurements.

## References

`SigmaLayer/FiniteQMClosure.lean` (the operational predecessor, untouched);
`RecordLayer/SwapClosure.lean` (`SwapMeasurementClosure` — the dynamical half);
`SigmaLayer/MeasureBridge.lean` (`productDynamics`, `productSector`,
`productSector_hasFubiniStudyPushforward`); `SigmaLayer/DynamicsBridge.lean`
(`productDynamicsBridge.projectable`); `RecordLayer/SwapWitness.lean` (`swapMeasure`,
`swapEvolve_measurePreserving`); `SigmaLayer/UnifiedFlowedRecords.lean`
(`unified_born_frequency`); `SigmaLayer/MixedOntic.lean` (`mixed_ontic_born_weight`);
`specs/BACKLOG.md` (the engine-migration row, closed by this module).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer CSD.LF4 CSD.LF5 CSD.LF2 Matrix.UnitaryGroup

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CPN (M + 1))

/-- **The unified arena**: system (base ray + system fibre) × pointer register × calibrated
ancilla bank — the one space carrying both the isolated Schrödinger dynamics and the
measurement dynamics. -/
abbrev UnifiedArena (M : ℕ) := SwapArena (KSigma (M + 1)) (M + 1)

/-- **The arena Liouville measure**: Liouville on the system slot, Haar on the register,
Liouville on every bank slot. This is `swapMeasure` at `μs = kMuL p₀` — so the measurement
propagator's measure-preservation theorem applies to it verbatim. -/
noncomputable def arenaLiouville (M : ℕ) (p₀ : CPN (M + 1)) : Measure (UnifiedArena M) :=
  swapMeasure (kMuL p₀) (M + 1)

instance : IsProbabilityMeasure (arenaLiouville M p₀) := by
  unfold arenaLiouville
  infer_instance

/-- **The isolated flow, lifted to the arena**: `exp(-itH)` on the system slot, identity on
register and bank. -/
noncomputable def arenaIso (t : ℝ) : UnifiedArena M → UnifiedArena M :=
  fun x => (((productDynamics H hH p₀).flow t x.1.1, x.1.2), x.2)

/-- **The ray projection of the arena**: project the system slot to its base ray. -/
noncomputable def arenaRay : UnifiedArena M → CPN (M + 1) :=
  fun x => (productSector H hH p₀).pi x.1.1

/-! ### Marginals -/

/-- The product model's Liouville measure is `kMuL` — the identification the migration rests
on. -/
lemma productDynamics_muL :
    ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1))) = kMuL p₀ := rfl

/-- Cylinder sets over the system slot carry exactly the system Liouville measure. -/
lemma arenaLiouville_cylinder (S : Set (KSigma (M + 1))) :
    arenaLiouville M p₀ ((fun x : UnifiedArena M => x.1.1) ⁻¹' S) = kMuL p₀ S := by
  have h : ((fun x : UnifiedArena M => x.1.1) ⁻¹' S)
      = (S ×ˢ (univ : Set KTorus)) ×ˢ (univ : Set (Fin (M + 1) → KSigma (M + 1))) := by
    ext x
    simp [Set.mem_prod]
  rw [arenaLiouville, swapMeasure, h, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, mul_one]

/-- The system-slot marginal of the arena Liouville measure is the system Liouville
measure. -/
lemma arenaLiouville_sys_marginal :
    Measure.map (fun x : UnifiedArena M => x.1.1) (arenaLiouville M p₀) = kMuL p₀ := by
  have hm : Measurable fun x : UnifiedArena M => x.1 :=
    measurable_fst
  rw [show (fun x : UnifiedArena M => x.1.1)
      = (Prod.fst : KSigma (M + 1) × KTorus → KSigma (M + 1))
        ∘ (fun x : UnifiedArena M => x.1) from rfl,
    ← Measure.map_map measurable_fst hm]
  show ((arenaLiouville M p₀).fst).fst = kMuL p₀
  rw [arenaLiouville, swapMeasure, Measure.fst_prod, Measure.fst_prod]

/-! ### The migrated isolated dynamics -/

/-- **The lifted isolated flow preserves the arena Liouville measure.** -/
theorem arenaIso_measurePreserving (t : ℝ) :
    MeasurePreserving (arenaIso H hH p₀ t) (arenaLiouville M p₀) (arenaLiouville M p₀) := by
  have h : arenaIso H hH p₀ t
      = Prod.map (Prod.map ((productDynamics H hH p₀).flow t) id) id := rfl
  rw [h, arenaLiouville, swapMeasure]
  exact (((productDynamics H hH p₀).flow_preserves t).prod (MeasurePreserving.id _)).prod
    (MeasurePreserving.id _)

/-- **The lifted flow projects to Schrödinger evolution on rays** — the Schrödinger pillar, on
the unified arena. -/
theorem arenaIso_schrodinger (t : ℝ) (x : UnifiedArena M) :
    arenaRay H hH p₀ (arenaIso H hH p₀ t x)
      = productProjectedFlow H hH t (arenaRay H hH p₀ x) :=
  (productDynamicsBridge H hH p₀).projectable t x.1.1

/-- **The Fubini–Study bridge, on the unified arena**: the ray-projected law of the arena
Liouville measure is the Fubini–Study measure. -/
theorem arenaRay_pushforward :
    Measure.map (arenaRay H hH p₀) (arenaLiouville M p₀) = fubiniStudyMeasure p₀ := by
  have hm : Measurable fun x : UnifiedArena M => x.1.1 :=
    measurable_fst.comp measurable_fst
  rw [show arenaRay H hH p₀
      = (productSector H hH p₀).pi ∘ (fun x : UnifiedArena M => x.1.1) from rfl,
    ← Measure.map_map (productSector H hH p₀).measurable_pi hm,
    arenaLiouville_sys_marginal]
  exact productSector_hasFubiniStudyPushforward H hH p₀

/-! ### The unified closure -/

variable (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)

/-- **★★ The unified-arena closure: one arena carries isolated dynamics and the complete
rank-one projective measurement reconstruction.** *(Scope corrected 2026-08-02 — see the
module header: degenerate Lüders lives on the join witness; a bundling capstone is recorded.)*

The successor of `CsdFiniteQMClosure`'s two-arena conjunction: every field is a statement about
`UnifiedArena M` and its Liouville measure `arenaLiouville`. Isolated Schrödinger dynamics,
Fubini–Study bridge, measurement dynamics (record creation, exclusivity, persistence,
dynamical Born, rank-one Lüders), i.i.d. Born frequencies, and mixed-state Born weights — one
arena, one measure family. The field mapping from the operational closure (migrated /
upgraded / superseded / recorded) is the module header's table. -/
structure UnifiedArenaClosure : Prop where
  /-- The lifted isolated flow preserves the arena Liouville measure. -/
  isolated_flow_measure_preserving :
    ∀ t, MeasurePreserving (arenaIso H hH p₀ t) (arenaLiouville M p₀) (arenaLiouville M p₀)
  /-- The lifted flow projects to Schrödinger evolution `exp(-itH) • ·` on rays. -/
  schrodinger_projection :
    ∀ t x, arenaRay H hH p₀ (arenaIso H hH p₀ t x)
      = productProjectedFlow H hH t (arenaRay H hH p₀ x)
  /-- The ray-projected law of the arena Liouville measure is Fubini–Study (B1). -/
  fubini_study_bridge :
    Measure.map (arenaRay H hH p₀) (arenaLiouville M p₀) = fubiniStudyMeasure p₀
  /-- The record-creating measurement propagator preserves the SAME Liouville measure. -/
  measurement_preserving :
    ∀ s t : CSD.SigmaLayer.OnticTime,
      MeasurePreserving (swapEvolve (basinIndex (momentContext (M + 1))) s t)
        (arenaLiouville M p₀) (arenaLiouville M p₀)
  /-- Measurement as a process on this arena: ready ⇒ no record, record created, outcomes
  exclusive, record persists, dynamical Born, rank-one Lüders (`SwapMeasurementClosure`). -/
  measurement : SwapMeasurementClosure (M + 1) ψ
  /-- Born frequency: i.i.d. trials of the arena Liouville measure land in the arena cylinder
  of the Born region with frequency → `‖⟨eᵢ,ψ⟩‖²`. -/
  born_frequency : ∀ {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → UnifiedArena M) (_ : ∀ n, Measurable (X n))
    (_ : ∀ n, Measure.map (X n) Pr = arenaLiouville M p₀)
    (_ : ∀ i : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
        (fun n => Set.indicator
          ((X n) ⁻¹' ((fun a : UnifiedArena M => a.1.1)
            ⁻¹' ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i))) (fun _ => (1 : ℝ))))),
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Filter.Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' ((fun a : UnifiedArena M => a.1.1)
                  ⁻¹' ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i)))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        Filter.atTop (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2))
  /-- Mixed states: spectral mixtures of arena cylinder measures reproduce `Tr(ρEᵢ)`. -/
  mixed_born : ∀ (ρ : DensityOperator (M + 1)) (i : Fin (M + 1)),
    ∑ j, ρ.isHermitian.eigenvalues j
        * (arenaLiouville M p₀ ((fun a : UnifiedArena M => a.1.1) ⁻¹'
            ((productSector H hH p₀).pi ⁻¹'
              bornRegion (ρ.isHermitian.eigenvectorBasis j) (eigenvectorBasis_ne_zero ρ j) i))).toReal
      = traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one i))

/-- **★★ The unified-arena closure holds** — for every Hermitian `H`, base point `p₀`, and unit
state `ψ`: one arena, one Liouville measure family, the rank-one reconstruction. -/
theorem unifiedArenaClosure (hψ : ‖ψ‖ = 1) :
    UnifiedArenaClosure H hH p₀ ψ hψ0 where
  isolated_flow_measure_preserving := arenaIso_measurePreserving H hH p₀
  schrodinger_projection := arenaIso_schrodinger H hH p₀
  fubini_study_bridge := arenaRay_pushforward H hH p₀
  measurement_preserving s t :=
    swapEvolve_measurePreserving (kMuL p₀) (basinIndex (momentContext (M + 1)))
      (measurable_basinIndex (momentContext (M + 1))) s t
  measurement := swapMeasurementClosure ψ
  born_frequency := fun X hX hlaw hindep =>
    unified_born_frequency H hH p₀ ψ hψ0 hψ
      (fun n ω => (X n ω).1.1)
      (fun n => (measurable_fst.comp measurable_fst).comp (hX n))
      (fun n => by
        have hm : Measurable fun a : UnifiedArena M => a.1.1 :=
          measurable_fst.comp measurable_fst
        rw [show (fun ω => (X n ω).1.1)
            = (fun a : UnifiedArena M => a.1.1) ∘ (X n) from rfl,
          ← Measure.map_map hm (hX n), hlaw n, arenaLiouville_sys_marginal p₀,
          productDynamics_muL H hH p₀])
      hindep
  mixed_born := fun ρ i => by
    have h := mixed_ontic_born_weight H hH p₀ ρ i
    rw [productDynamics_muL] at h
    simpa only [arenaLiouville_cylinder] using h

/-! ### The mixed two-stage LLN, on the arena (the first recorded residue, discharged) -/

/-- The two-stage mixture measure on the arena: draw a spectral component, then an arena
microstate from the arena Liouville measure. -/
noncomputable def arenaMixtureMeasure (ρ : DensityOperator (M + 1)) :
    Measure (Fin (M + 1) × UnifiedArena M) :=
  (eigenvalueMeasure ρ).prod (arenaLiouville M p₀)

/-- The mixed outcome-`i` region on the arena: the system-slot cylinder of the two-stage Born
region. -/
def arenaMixtureRegion (ρ : DensityOperator (M + 1)) (i : Fin (M + 1)) :
    Set (Fin (M + 1) × UnifiedArena M) :=
  (Prod.map id (fun a : UnifiedArena M => a.1.1)) ⁻¹' mixtureRegion H hH p₀ ρ i

/-- **Mixed-state Born frequencies, on the unified arena.** For i.i.d. two-stage trials of any
density operator `ρ` — spectral component, then arena microstate — the outcome-`i` frequency
converges a.s. to `Tr(ρ Eᵢ)`. Transfers from `unified_mixed_born_frequency` through the
system-slot marginal; discharges the residue recorded at the migration. -/
theorem arena_mixed_born_frequency (ρ : DensityOperator (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (Y : ℕ → Ω → Fin (M + 1) × UnifiedArena M) (hY : ∀ n, Measurable (Y n))
    (hlaw : ∀ n, Measure.map (Y n) Pr = arenaMixtureMeasure p₀ ρ)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
        (fun n => Set.indicator ((Y n) ⁻¹' arenaMixtureRegion H hH p₀ ρ i)
          (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Filter.Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((Y k) ⁻¹' arenaMixtureRegion H hH p₀ ρ i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        Filter.atTop
        (nhds (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
          (single_norm_one i)))) := by
  have hm : Measurable (Prod.map (id : Fin (M + 1) → Fin (M + 1))
      (fun a : UnifiedArena M => a.1.1)) :=
    measurable_id.prodMap (measurable_fst.comp measurable_fst)
  exact unified_mixed_born_frequency H hH p₀ ρ
    (fun n ω => Prod.map id (fun a : UnifiedArena M => a.1.1) (Y n ω))
    (fun n => hm.comp (hY n))
    (fun n => by
      have hg : Measurable fun a : UnifiedArena M => a.1.1 :=
        measurable_fst.comp measurable_fst
      rw [show (fun ω => Prod.map id (fun a : UnifiedArena M => a.1.1) (Y n ω))
          = (Prod.map id (fun a : UnifiedArena M => a.1.1)) ∘ (Y n) from rfl,
        ← Measure.map_map hm (hY n), hlaw n, arenaMixtureMeasure,
        ← Measure.map_prod_map _ _ measurable_id hg,
        Measure.map_id, arenaLiouville_sys_marginal p₀, mixtureMeasure, productDynamics_muL])
    hindep

/-! ### The round trip (the second recorded residue, discharged) -/

/-- **Records are invariant under isolated evolution**: the lifted `exp(-itH)` never touches
the pointer register, so the readout is a conserved quantity of the isolated flow. This is what
"the record is a stable fact of `Σ`" means dynamically. -/
theorem readout_arenaIso (s : ℝ) (y : UnifiedArena M) :
    (swapProtocol (basinIndex (momentContext (M + 1)))
        (measurable_basinIndex (momentContext (M + 1)))).readout (arenaIso H hH p₀ s y)
      = (swapProtocol (basinIndex (momentContext (M + 1)))
          (measurable_basinIndex (momentContext (M + 1)))).readout y := rfl

/-- **★ The round trip: isolate, measure, isolate — the record is created and survives.**
Evolve freely for time `r`; if the evolved state sits in the selector-`i` ready set, run the
measurement: the record `i` is created, and any subsequent isolated evolution for time `s`
leaves it standing. The first statement in the corpus that composes the Schrödinger propagator
and the measurement propagator on one arena — the composition that was not even *stateable*
before the migration. -/
theorem arena_round_trip (r s : ℝ) (i : Fin (M + 1)) (x : UnifiedArena M)
    (hx : arenaIso H hH p₀ r x ∈ selReadyBank (basinIndex (momentContext (M + 1))) i) :
    (swapProtocol (basinIndex (momentContext (M + 1)))
        (measurable_basinIndex (momentContext (M + 1)))).readout
      (arenaIso H hH p₀ s
        ((swapProtocol (basinIndex (momentContext (M + 1)))
            (measurable_basinIndex (momentContext (M + 1)))).evolve 0 1
          (arenaIso H hH p₀ r x)))
      = some i := by
  rw [readout_arenaIso]
  exact (swapProtocol _ _).readout_evolve_outcomeSector
    (swap_correlates (basinIndex (momentContext (M + 1)))
      (measurable_basinIndex (momentContext (M + 1))) i hx)

end CSD.RecordLayer
