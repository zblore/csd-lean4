import CsdLean4.LF4.KahlerInstance
import CsdLean4.LF1.GeneralFrequency
import Mathlib.MeasureTheory.Group.Measure

/-!
# LF4 Tranche A: a non-trivial measure-preserving flow on the Kähler instance

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

end LF4
end CSD
