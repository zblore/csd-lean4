import CsdLean4.LF4.BothPillars
import CsdLean4.LF4.KahlerInstance

/-!
# C7: both pillars on a genuine many-to-one-`π` object

The C4 both-pillars object `rotationSetup` (`LF4/BothPillars.lean`) uses `π = id`
— the DEGENERATE one-to-one case (`Σ = ` ray space, fibres = points). Paper C's
axiom A3, and the CSD ontology generally, want `π : Σ → ℂℙ^{N-1}` to be a genuine
**smooth many-to-one** projection: `Σ` strictly LARGER than ray space, each ray
`[ψ]` the image of a whole fibre `π⁻¹([ψ])` of ontic microstates. A genuine
many-to-one `π` already existed in the corpus (`KSigma = ℂℙ^{N-1} × T²`,
`π = Prod.fst`, fibres `= T²`, `KahlerFlow.lean`) but on the older `SectorData`
track and with a flow (`kFlow`) that acts TRIVIALLY on rays. And `rotationSetup`
had the non-trivial ray flow but `π = id`. **No single object had BOTH.**

This module builds that object.

* `manyToOneSetup U p₀` — a `KahlerOnticSetup N` on the fibred ontic space
  `Σ = ℂℙ^{N-1} × T²` with the genuine many-to-one projection `π = Prod.fst`
  (fibres `= T²`, `manyToOneSetup_pi_not_injective`), Liouville measure the
  product Kähler volume `kMuL = μ_FS ⊗ vol_{T²}`, and a flow that ROTATES THE
  BASE RAY by `U t` while leaving the fibre fixed. So its projected flow is the
  genuine ray action `U t • ·` (non-trivial for the rotation, unlike `kFlow`),
  while `π` is genuinely many-to-one (unlike `rotationSetup`).

* `manyToOneRotationSetup p₀` — the concrete `N = 2` witness with `U = rotU`
  (the `ℂℙ¹` rotation), and `manyToOneRotationSetup_both_pillars` fires BOTH
  pillars on it:
  - **(A) Schrödinger** — the projected flow is `exp(-itH)`-conjugation on rays,
    `H = σ_y`, inherited verbatim from `rotationSetup_schrodinger_form` (the base
    ray action is identical);
  - **(B) Born** — sampling the fibred Liouville measure `kMuL p₀` and scoring
    the FIBRED Born region `π⁻¹'(bornRegion ψ i)` gives empirical frequencies
    converging a.s. to the Born weights `‖⟨eᵢ,ψ⟩‖²`.

The Born pillar here genuinely EXERCISES the many-to-one projection: the outcome
region on `Σ` is the fibred set `π⁻¹'(bornRegion ψ i) = bornRegion ψ i ×ˢ T²`,
and its typicality volume equals the base Born weight precisely because the fibre
volume is normalized to `1` — the pushforward bridge `Prod.fst_* kMuL = μ_FS`
(`k_measure_bridge` / `Measure.fst_prod`). This is the many-to-one analogue of
C4's `unitaryFlowSetup_born_frequency`, reducing to `born_frequency_convergence_N`
on the projected trials `π ∘ X`.

## Honest scope

This removes the `π = id` degeneracy flagged in the Paper-C cross-check
(`connectivity-manifest.md`, the A3 caveat): one `KahlerOnticSetup` object now
carries BOTH a genuine many-to-one `π` AND a non-trivial projected ray flow,
with both pillars proved on it. It does **NOT** close the deep gap (L7 / FND-1):
the Born trials still SAMPLE `kMuL` i.i.d.; they are not evolved by the flow, and
the weights are not derived from the dynamics. The fibre flow here is trivial
(the flow moves only the base ray), so this is not the de-isolation / Hamiltonian
fibre dynamics either. The Kähler-geometry fields remain honest placeholders (L1).

## Provenance

Foundational-triple only; Gleason-free. Reuses `rotationSetup_schrodinger_form`
(Schrödinger), `born_frequency_convergence_N` (Born), `kMuL` / `Measure.fst_prod`
(the marginal bridge); nothing re-proved.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ} [NeZero N]

/-! ## The many-to-one lift constructor -/

/-- **A `KahlerOnticSetup` with a genuine many-to-one `π` AND a non-trivial
projected flow.** `Σ = ℂℙ^{N-1} × T²` (fibred over ray space), `π = Prod.fst`
(many-to-one, fibres `= T²`), Liouville measure the product Kähler volume
`kMuL = μ_FS ⊗ vol_{T²}`, and `flow t (p, θ) = (U t • p, θ)` — the ray is rotated
by `U t`, the fibre is fixed. So `projectedFlow t = (U t • ·)` is the genuine ray
action (non-trivial for a non-trivial `U`), while `π` is genuinely many-to-one.

Measure-preservation is `μ_FS`'s `U(N)`-invariance on the base times the identity
on the fibre. The two Kähler-geometry placeholder fields mirror `unitaryFlowSetup`:
`IsLiouvilleKahlerVolume` carries the normalized-volume core (`kMuL` is a
probability measure, `instProbKMuL`); `IsKahlerSector` stays the honest
unformalizable `True` posit. -/
noncomputable def manyToOneSetup
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    KahlerOnticSetup N where
  Sigma := KSigma N
  compact_sigma := inferInstance
  IsKahlerSector := True
  kahler_condition := trivial
  liouvilleMeasure := kMuL p₀
  IsLiouvilleKahlerVolume := IsProbabilityMeasure (kMuL p₀)
  liouville_eq_kahler_volume := inferInstance
  pi := Prod.fst
  pi_measurable := measurable_fst
  flow := fun t p => (U t • p.1, p.2)
  flow_preserves_volume := fun t => by
    have hbase : MeasurePreserving (fun q : CPN N => U t • q)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
      ⟨(continuous_const_smul (U t)).measurable, fubiniStudyMeasure_smul_invariant (U t) p₀⟩
    exact hbase.prod (MeasurePreserving.id (volume : Measure KTorus))
  projectedFlow := fun t p => U t • p
  projectable := fun _ _ => rfl

omit [NeZero N] in
@[simp] lemma manyToOneSetup_pi
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    (manyToOneSetup U p₀).pi = Prod.fst := rfl

omit [NeZero N] in
@[simp] lemma manyToOneSetup_flow
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) (t : ℝ) (p : KSigma N) :
    (manyToOneSetup U p₀).flow t p = (U t • p.1, p.2) := rfl

omit [NeZero N] in
@[simp] lemma manyToOneSetup_projectedFlow
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) (t : ℝ) (p : CPN N) :
    (manyToOneSetup U p₀).projectedFlow t p = U t • p := rfl

omit [NeZero N] in
@[simp] lemma manyToOneSetup_liouvilleMeasure
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    (manyToOneSetup U p₀).liouvilleMeasure = kMuL p₀ := rfl

omit [NeZero N] in
/-- **The projection is genuinely many-to-one** (fibres `= T²`, not points): for
any nonzero fibre shift `sh`, the ontic states `(p, sh)` and `(p, 0)` are DISTINCT
yet share the ray `π (p, _) = p`. So `π` is not injective — the defining feature
Paper C's A3 asks for, and exactly what `rotationSetup` (`π = id`) lacks. -/
theorem manyToOneSetup_pi_not_injective
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ p : CPN N)
    {sh : KTorus} (hsh : sh ≠ 0) :
    ¬ Function.Injective (manyToOneSetup U p₀).pi := by
  intro hinj
  have hpair : ((p, sh) : KSigma N) = (p, 0) := hinj rfl
  exact hsh (by simpa using congrArg Prod.snd hpair)

/-! ## The concrete rotation witness at `N = 2` -/

/-- The concrete **many-to-one, non-trivial-ray-flow** `KahlerOnticSetup 2`:
`Σ = ℂℙ¹ × T²`, `π = Prod.fst`, and the base ray rotated by the `ℂℙ¹` rotation
`R(t)`. Genuine many-to-one `π` (fibres `= T²`) AND genuine projected ray flow
(`R(t) • ·`) on ONE object. -/
noncomputable def manyToOneRotationSetup (p₀ : CPN 2) : KahlerOnticSetup 2 :=
  manyToOneSetup rotU p₀

/-- The projected flow of the rotation witness is genuinely `≠ id` (same ray
action as `rotationSetup`, at `t = π/2` sending `[e₀] ↦ [e₁]`). Combined with
`manyToOneSetup_pi_not_injective`, this object has BOTH a many-to-one `π` AND a
non-trivial projected flow — the C7 target. -/
theorem manyToOneRotationSetup_projectedFlow_ne_id (p₀ : CPN 2) :
    ∃ t : ℝ, (manyToOneRotationSetup p₀).projectedFlow t ≠ id :=
  rotationSetup_projectedFlow_ne_id p₀

/-! ## The Born pillar on the many-to-one object -/

/-- **Born frequencies from the fibred Liouville measure, scoring the fibred Born
region.** For `manyToOneSetup U p₀`, sampling its Liouville measure `kMuL p₀`
i.i.d. and scoring the FIBRED Born region `π⁻¹'(bornRegion ψ i)` (`= bornRegion ψ i
×ˢ T²`), the empirical frequencies converge a.s. to the Born weights `‖⟨eᵢ,ψ⟩‖²`.

This is the many-to-one analogue of `unitaryFlowSetup_born_frequency`. It genuinely
uses the projection: the fibred region's `kMuL`-volume equals the base Born weight
because the fibre volume is normalized (`Prod.fst_* kMuL = μ_FS`, `Measure.fst_prod`),
so the statement reduces to `born_frequency_convergence_N` on the projected trials
`π ∘ X`. -/
theorem manyToOneSetup_born_frequency {M : ℕ}
    (U : ℝ → Matrix.unitaryGroup (Fin (M + 1)) ℂ) (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → KSigma (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (manyToOneSetup U p₀).liouvilleMeasure)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' ((manyToOneSetup U p₀).pi ⁻¹' bornRegion ψ hψ0 i))
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' ((manyToOneSetup U p₀).pi ⁻¹' bornRegion ψ hψ0 i))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  -- The fibred-region preimage under `X` is the base-region preimage under `π ∘ X`.
  have hpre : ∀ (n : ℕ) (i : Fin (M + 1)),
      (X n) ⁻¹' ((manyToOneSetup U p₀).pi ⁻¹' bornRegion ψ hψ0 i)
        = ((manyToOneSetup U p₀).pi ∘ X n) ⁻¹' bornRegion ψ hψ0 i := fun n i => rfl
  simp only [hpre] at hindep ⊢
  -- Apply the general-N Born capstone to the projected trials `π ∘ X`.
  refine born_frequency_convergence_N p₀ ψ hψ0 hψ hpos
    (fun n => (manyToOneSetup U p₀).pi ∘ X n)
    (fun n => (manyToOneSetup U p₀).pi_measurable.comp (hX n)) ?_ hindep
  -- The projected trials sample `μ_FS` (the marginal of the fibred `kMuL`).
  intro n
  calc Measure.map ((manyToOneSetup U p₀).pi ∘ X n) Pr
      = Measure.map (manyToOneSetup U p₀).pi (Measure.map (X n) Pr) :=
        (Measure.map_map (manyToOneSetup U p₀).pi_measurable (hX n)).symm
    _ = Measure.map (manyToOneSetup U p₀).pi ((manyToOneSetup U p₀).liouvilleMeasure) :=
        congrArg (Measure.map (manyToOneSetup U p₀).pi) (hlaw n)
    _ = fubiniStudyMeasure p₀ := by
        show Measure.map Prod.fst (kMuL p₀) = fubiniStudyMeasure p₀
        rw [kMuL, ← Measure.fst, Measure.fst_prod]

/-! ## The C7 headline: both pillars on one many-to-one object -/

/-- **C7: both pillars on ONE genuine many-to-one-`π` object.** For the single
`KahlerOnticSetup 2` instance `manyToOneRotationSetup p₀` — whose `Σ = ℂℙ¹ × T²`,
`π = Prod.fst` is genuinely many-to-one (`manyToOneSetup_pi_not_injective`), and
whose projected flow is a non-trivial ray rotation
(`manyToOneRotationSetup_projectedFlow_ne_id`):

* **(A) Schrödinger** — the projected deterministic flow is `exp(-itH)`-conjugation
  on rays for a Hermitian `H` (`= σ_y`), `π(Φ_t x) = exp(-itH) • π(x)`, inherited
  from `rotationSetup_schrodinger_form` (the base ray action is identical);
* **(B) Born** — sampling its Liouville measure `kMuL p₀` and scoring the FIBRED
  Born region `π⁻¹'(bornRegion ψ i)` gives empirical frequencies converging a.s.
  to the Born weights `‖⟨eᵢ,ψ⟩‖²`.

Both about the *same* object, whose projection is genuinely many-to-one — the
`π = id` degeneracy of `rotationSetup_both_pillars` removed (the Paper-C A3
caveat). Standing gap unchanged: the Born trials still sample `kMuL` rather than
being evolved by the flow (L7 / FND-1). -/
theorem manyToOneRotationSetup_both_pillars (p₀ : CPN 2)
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → KSigma 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (manyToOneRotationSetup p₀).liouvilleMeasure)
    (hindep : ∀ i : Fin 2,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' ((manyToOneRotationSetup p₀).pi ⁻¹' bornRegion ψ hψ0 i))
            (fun _ => (1 : ℝ))))) :
    (∃ H : Matrix (Fin 2) (Fin 2) ℂ, ∃ hH : H.IsHermitian,
        ∀ t x, (manyToOneRotationSetup p₀).pi ((manyToOneRotationSetup p₀).flow t x)
          = schrodingerUnitary hH t • (manyToOneRotationSetup p₀).pi x)
      ∧ (∀ᵐ ω ∂ Pr, ∀ i : Fin 2,
          Tendsto
            (fun m : ℕ =>
              (∑ k ∈ Finset.range m,
                  Set.indicator
                    ((X k) ⁻¹' ((manyToOneRotationSetup p₀).pi ⁻¹' bornRegion ψ hψ0 i))
                    (fun _ => (1 : ℝ)) ω) / (m : ℝ))
            atTop
            (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2))) := by
  refine ⟨?_, manyToOneSetup_born_frequency rotU p₀ ψ hψ0 hψ hpos X hX hlaw hindep⟩
  obtain ⟨H, hH, hSchro⟩ := rotationSetup_schrodinger_form p₀
  exact ⟨H, hH, fun t x => hSchro t x.1⟩

end LF4
end CSD
