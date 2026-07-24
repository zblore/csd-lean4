/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.LF1.GeneralFrequency
public import Mathlib.MeasureTheory.Group.Measure

/-!
# LF4 Tranche A: a non-trivial measure-preserving flow on the Kähler instance

**Category:** 3-Local (a non-trivial measure-preserving flow on the Kähler instance).

Every concrete `SectorData` built so far (`LF4/Instance.lean`,
`LF4/KahlerInstance.lean`, `Tests/Examples.lean`) hard-codes `Φ := id`, so the
LF1 deterministic-typicality theorem, when instantiated, runs the strong law
over i.i.d. preparation draws with **no ontic evolution**. The `hΦ_pres`
(Liouville preservation) field is consumed only via its measurability content;
its preservation payload has never been load-bearing (see `LF1/Setup.lean`).

This module installs the first **non-trivial** deterministic flow on the
existing Kähler space `KSigma N = ℂℙ^{N-1} × T²`: a constant translation
`kFlow sh : (p, t) ↦ (p, sh + t)` on the `T²` fibre. It is measure-preserving
for `kMuL = μFS ⊗ vol_{T²}` because the fibre volume is the (translation-
invariant) Haar measure on `AddCircle 1 × AddCircle 1`, and it acts trivially on
the base. The frequency capstone `kFlow_frequency_convergence` fires the
law-agnostic LF1 theorem `freq_tendsto_of_iid` on the **evolved** trials
`kFlow sh ∘ sampleₙ`, and the measure-preservation of `kFlow` is exactly what
pins `law(kFlow sh ∘ sampleₙ) = kMuL p₀`, hence the limiting frequency to the
volume ratio `(kMuL O).toReal`. So `hΦ_pres` is load-bearing here for the first
time.

## What this does and does not establish

- **Does:** exhibits `Φ ≠ id` on a genuinely compact-Kähler `Σ`, makes the LF1
  deterministic structure non-vacuous on a concrete instance, and shows the
  ontic volume ratio is *stable under deterministic evolution* — the structural
  role Sigma0 §2.4 assigns to `(Φ_t)∗ μL = μL`. The flow preserves projective
  rays (`kFlow_preserves_rays`: `(kFlow sh p).1 = p.1`, i.e. `π ∘ kFlow = π`
  since `(kSectorData _).π = Prod.fst`), matching CSD's constraint-surface
  reading — the flow moves only within a fibre over a fixed quantum state `[ψ]`.
- **Does not:** escape the carve-out. The limit `(kMuL O).toReal` is the chosen
  volume of `O`; a translation flow has Haar as its invariant measure, so even
  with Birkhoff the space-average is the carved measure. Deriving the outcome
  *region* (and hence its Born weight) from the dynamics is Tranche B
  (`specs/carve-out-plan.md` §4, the §9.5 / G3b target), not this module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- The fibre-translation flow on `Σ = ℂℙ^{N-1} × T²`: translate the `T²`
coordinate by a fixed `sh`, leaving the base ray fixed. -/
noncomputable def kFlow (sh : KTorus) : KSigma N → KSigma N := fun p => (p.1, sh + p.2)

@[simp] lemma kFlow_apply (sh : KTorus) (p : KSigma N) :
    kFlow sh p = (p.1, sh + p.2) := rfl

/-- The fibre flow preserves projective rays: `(kFlow sh p).1 = p.1`. Since
`(kSectorData _).π = Prod.fst`, this is the constraint-surface compatibility
hypothesis `h_flow_π` of `SectorData.outcomeOfProjective` — the deterministic
flow moves only within the fibre over a fixed quantum state `[ψ]`. -/
@[simp] lemma kFlow_preserves_rays (sh : KTorus) (p : KSigma N) :
    (kFlow sh p).1 = p.1 := rfl

/-- **The flow is non-trivial** for a nonzero fibre shift: dynamics is genuinely
present, unlike the `Φ = id` base instances. -/
theorem kFlow_ne_id (p₀ : CPN N) {sh : KTorus} (hsh : sh ≠ 0) :
    kFlow (N := N) sh ≠ id := by
  intro h
  exact hsh (by simpa using congrArg Prod.snd (congrFun h (p₀, 0)))

/-- **The flow is measure-preserving for the Kähler/Liouville volume.** This is
the genuine `hΦ_pres` content (Liouville's theorem) for a non-identity flow:
translation is Haar-invariant on the `T²` fibre and the base factor is fixed. -/
theorem kFlow_measurePreserving (p₀ : CPN N) (sh : KTorus) :
    MeasurePreserving (kFlow (N := N) sh) (kMuL p₀) (kMuL p₀) := by
  have h1 : MeasurePreserving (fun x : AddCircle (1 : ℝ) => sh.1 + x)
      (volume : Measure (AddCircle (1 : ℝ))) (volume : Measure (AddCircle (1 : ℝ))) :=
    measurePreserving_add_left _ sh.1
  have h2 : MeasurePreserving (fun x : AddCircle (1 : ℝ) => sh.2 + x)
      (volume : Measure (AddCircle (1 : ℝ))) (volume : Measure (AddCircle (1 : ℝ))) :=
    measurePreserving_add_left _ sh.2
  have htransl : MeasurePreserving (fun t : KTorus => sh + t)
      (volume : Measure KTorus) (volume : Measure KTorus) := h1.prod h2
  exact (MeasurePreserving.id (fubiniStudyMeasure p₀)).prod htransl

/-- **Tranche A frequency capstone.** For i.i.d. preparation draws `sampleₙ` with
common law `kMuL p₀`, the empirical frequency of a measurable outcome region `O`
evaluated on the **evolved** states `kFlow sh ∘ sampleₙ` converges almost surely
to the ontic volume ratio `(kMuL p₀ O).toReal`.

The deterministic flow `kFlow sh` (non-trivial for `sh ≠ 0`, by `kFlow_ne_id`) is
applied to every sampled microstate, and `kFlow_measurePreserving` is what makes
`law(kFlow sh ∘ sampleₙ) = kMuL p₀`, hence pins the limit to the volume ratio.
This is the LF1 deterministic-typicality theorem realised with a genuine flow on
a compact-Kähler `Σ`. -/
theorem kFlow_frequency_convergence
    (p₀ : CPN N) (sh : KTorus)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (sample : ℕ → Ω → KSigma N) (hsample : ∀ n, Measurable (sample n))
    (hlaw : ∀ n, Measure.map (sample n) Pr = kMuL p₀)
    {O : Set (KSigma N)} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator ((kFlow sh ∘ sample n) ⁻¹' O) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator ((kFlow sh ∘ sample i) ⁻¹' O) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (kMuL p₀ O).toReal) := by
  have hmp := kFlow_measurePreserving p₀ sh
  -- Measure preservation is load-bearing: it pins the law of the evolved trials.
  have hlaw' : ∀ n, Measure.map (kFlow sh ∘ sample n) Pr = kMuL p₀ := fun n => by
    rw [← Measure.map_map hmp.measurable (hsample n), hlaw n, hmp.map_eq]
  exact LF1.freq_tendsto_of_iid (fun n => hmp.measurable.comp (hsample n)) hlaw' hO hindep

/-! ## D1c-1: the concrete Kähler `SectorData` with `Φ = kFlow ≠ id`

Every concrete `SectorData` shipped so far (`cpSectorData`, `kSectorData`)
hard-codes `Φ := id` in its underlying `OnticSetup`, leaving the standing
structural debt: the corpus has a genuine measure-preserving non-identity flow
(`kFlow`, above) but no concrete `SectorData` *carrying* it. This block
discharges that debt for the Kähler instance by rebuilding `kOnticSetup` /
`kSectorData` with `Φ := kFlow sh`.

Only the three flow-related `OnticSetup` fields change (`Φ`, `hΦ_pres`, and the
derived `measurable_Φ`); `μL`, `Ω0`, and their hypotheses are reused verbatim.
The `SectorData` `G`-action fields (`measurable_smul_σ`, `measurable_smul_P`,
`hμL_inv`, `hπ_equiv`) are about the `U(N)`-action and `π = Prod.fst`, never
about `Φ`, so they are reused verbatim from `kSectorData` (`hμL_inv` reads
`toOntic.μL`, which is unchanged `= kMuL p₀`).

**Honest scope.** `kFlow` is a *free* `T²`-fibre translation: a genuine
measure-preserving `Φ ≠ id`, but dynamically trivial — it is **not** a
measurement / de-isolation flow (LF5's `Φ_vN`), nor a symplectic / Hamiltonian
flow generated by the Kähler form. So this is the **structural** discharge of
the "`Φ = id` in the concrete Kähler instance" debt, not its physical content.
Deferred (D1c-2): threading a de-isolation or Hamiltonian flow as the instance's
`Φ`. **SO-1 is untouched** — D1c is necessary-but-not-sufficient for deriving the
sector + Fubini–Study typicality from the dynamics (SO-1 additionally needs the
flow ergodic / mixing to force `μFS`). `cpSectorData` still carries `Φ = id`;
only the Kähler instance is addressed here. -/

variable [NeZero N]

/-- The Kähler `OnticSetup` with the **non-identity** flow `Φ := kFlow sh`.
Identical to `kOnticSetup p₀` except for the three flow fields: `Φ` is the fibre
translation, `hΦ_pres` is `kFlow_measurePreserving` (genuine Liouville content,
not `MeasurePreserving.id`). `μL`, `Ω0`, and their hypotheses are reused. -/
noncomputable def kOnticSetupFlow (p₀ : CPN N) (sh : KTorus) :
    CSD.LF1.OnticSetup (KSigma N) where
  μL := ⟨kMuL p₀, inferInstance⟩
  Φ := kFlow sh
  hΦ_pres := kFlow_measurePreserving p₀ sh
  Ω0 := Set.univ
  hΩ0_meas := MeasurableSet.univ
  hΩ0_nonzero := by
    show (kMuL p₀) Set.univ ≠ 0
    rw [measure_univ]; exact one_ne_zero

/-- **The concrete compact-Kähler `SectorData` carrying a genuine
measure-preserving `Φ ≠ id`.** Identical to `kSectorData p₀` except its
underlying ontic data is `kOnticSetupFlow p₀ sh` (so `Φ = kFlow sh`). The
`G = U(N)` action fields are reused verbatim from `kSectorData`; none of them
mention `Φ`. -/
noncomputable def kSectorDataFlow (p₀ : CPN N) (sh : KTorus) :
    CSD.LF2.SectorData (KSigma N) (CPN N) (Matrix.unitaryGroup (Fin N) ℂ) where
  toOntic := kOnticSetupFlow p₀ sh
  π := Prod.fst
  measurable_π := measurable_fst
  measurable_smul_σ := (kSectorData p₀).measurable_smul_σ
  measurable_smul_P := (kSectorData p₀).measurable_smul_P
  hμL_inv := (kSectorData p₀).hμL_inv
  hπ_equiv := (kSectorData p₀).hπ_equiv

/-- The instance's flow is exactly `kFlow sh` (definitional). -/
@[simp] lemma kSectorDataFlow_phi (p₀ : CPN N) (sh : KTorus) :
    (kSectorDataFlow p₀ sh).toOntic.Φ = kFlow sh := rfl

/-- **D1c-1 headline.** The concrete Kähler `SectorData` genuinely carries
`Φ ≠ id`: the structural "`Φ = id` in the concrete Kähler instance" debt is
discharged. Reuses `kFlow_ne_id`. -/
theorem kSectorDataFlow_phi_ne_id (p₀ : CPN N) {sh : KTorus} (hsh : sh ≠ 0) :
    (kSectorDataFlow p₀ sh).toOntic.Φ ≠ id :=
  kFlow_ne_id p₀ hsh

/-- The instance's flow is measure-preserving for the Kähler/Liouville volume
`kMuL p₀` (the genuine `hΦ_pres` content surfaced on the `SectorData`). -/
theorem kSectorDataFlow_phi_measurePreserving (p₀ : CPN N) (sh : KTorus) :
    MeasureTheory.MeasurePreserving (kSectorDataFlow p₀ sh).toOntic.Φ
      (kMuL p₀) (kMuL p₀) :=
  kFlow_measurePreserving p₀ sh

/-- **Non-vacuity link to LF1.** The LF1 deterministic-typicality theorem is
non-vacuous on `kSectorDataFlow`: for i.i.d. preparation draws, the empirical
frequency of a measurable outcome region `O` evaluated on the states evolved by
the **instance's own flow** `(kSectorDataFlow p₀ sh).toOntic.Φ` converges almost
surely to the ontic volume ratio `(kMuL p₀ O).toReal`. This is just
`kFlow_frequency_convergence` stated through the instance (`Φ = kFlow sh` is
definitional), so the moving flow that pins the limit is the `SectorData`'s own
`Φ ≠ id`, not the identity. LF1 is cited, not re-proved. -/
theorem kSectorDataFlow_frequency_convergence
    (p₀ : CPN N) (sh : KTorus)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (sample : ℕ → Ω → KSigma N) (hsample : ∀ n, Measurable (sample n))
    (hlaw : ∀ n, Measure.map (sample n) Pr = kMuL p₀)
    {O : Set (KSigma N)} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            (((kSectorDataFlow p₀ sh).toOntic.Φ ∘ sample n) ⁻¹' O)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                (((kSectorDataFlow p₀ sh).toOntic.Φ ∘ sample i) ⁻¹' O)
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (kMuL p₀ O).toReal) :=
  kFlow_frequency_convergence p₀ sh sample hsample hlaw hO hindep

end LF4
end CSD
