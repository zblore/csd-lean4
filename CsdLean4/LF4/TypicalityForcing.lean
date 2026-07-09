import CsdLean4.LF4.ObservableFlow
import CsdLean4.LF4.BornFS
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# A5 onramp: where the Fubini–Study typicality measure comes from

This file isolates the honest content of the A5 datum (`SectorData.(π, G)`,
`AXIOMS.md §3.3`) at the level of the **typicality measure**: which measure is the
canonical sampling law on the sector `Σ = ℂℙ^{N-1}`, and by what.

## IMPORTANT — what forces typicality (read first)

**Typicality is forced by the LAW OF LARGE NUMBERS** (LF1, `LF1_main_theorem_ae` /
`freq_tendsto_of_iid`; papers A & B): over repeated **i.i.d. preparations**, empirical
frequencies converge almost surely to the **volume weights of the sampling measure**.
That is the entire typicality-forcing mechanism — no time-average, no Birkhoff /
single-flow-ergodicity hypothesis. The results in THIS file are NOT the
typicality-forcing mechanism; they concern a *different* question — **which measure**
is the canonical sampling law (A), and a negative about the stat-mech single-flow
ergodicity route which CSD does not use (B/B′).

## The two honest results

**(A) The FS typicality MEASURE is singled out by the sector symmetry `G = U(N)` (a
measure-characterisation, NOT the typicality-forcing).**
`fubiniStudy_forced_by_symmetry` restates the corpus's axiom-free uniqueness
theorem `fubiniStudyMeasure_unique` (Phase G4,
`Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean`): **any**
`U(N)`-invariant probability measure on the sector **is** the Fubini–Study measure.
So FS is the *symmetry-canonical* sampling measure — the Born = FS-volume measure
(the input to the Duistermaat–Heckman cluster `fs_born_volume_ratio_N` /
`born_frequency_convergence_N`) is *singled out* by the sector symmetry, the A5
`(π, G)` datum, rather than posited as an arbitrary independent law. The **LLN** then
forces frequencies to its volume ratios. This is about the measure CHOICE, via the
**symmetry group**, NOT via any single flow and NOT the convergence mechanism.

**(B) A single ontic flow does NOT force FS (the obstruction).**
`obsFlow_not_uniquely_ergodic` exhibits, for `obsFlow` (the diagonal-phase
Hamiltonian flow `t ↦ exp(i t Â)` of `LF4/ObservableFlow.lean`), **two distinct**
`obsFlow`-invariant probability measures: the Fubini–Study measure and the Dirac
measure `δ_{[eⱼ]}` at a computational-basis eigenstate ray. Because `obsFlow` is a
diagonal phase flow, every basis ray `[eⱼ]` is an eigenvector and is a fixed point
(`obsFlow_fixes_eigenstate`), so `δ_{[eⱼ]}` is invariant
(`dirac_eigenstate_obsFlow_invariant`); and `δ_{[eⱼ]} ≠ μFS` because FS is
`U(N)`-invariant while `δ_{[eⱼ]}` is moved by a unitary swapping `[eⱼ] ↔ [eₖ]`.
Hence `obsFlow` is not uniquely ergodic: a single deterministic flow cannot single
out FS. This is *why* the concrete instances `cpSectorDataFlow` / `kSectorDataFlow`
(D1c-1/2), whose `Φ` is one such flow, do not discharge A5.

**(B′) The obstruction is GENERIC, not accidental: a CONSERVED QUANTITY.**
`obsFlow_continuum_invariant` strengthens (B) from "≥ 2" to a **continuum**
(`Set.InjOn` on `[0,1]`) of pairwise-distinct `obsFlow`-invariant probability
measures. The *structural reason* is a **constant of motion**: the Born
coordinates `momentMap · i` are conserved along `obsFlow`
(`momentMap_obsFlow`, reused from `LF4/ObservableFlow.lean` — the diagonal phase
`e^{itλᵢ}` leaves `|ψᵢ|²` unchanged). The genuine content is the
conserved-quantity reweighting principle `map_withDensity_of_conserved`: if `h`
is `obsFlow`-invariant (`h ∘ obsFlow = h`) and `μ` is `obsFlow`-invariant, then
`μ.withDensity (g ∘ h)` is again `obsFlow`-invariant — instantiated at
`h = momentMap · i` by `withDensity_momentMap_obsFlow_invariant`. So invariant
measures are abundant precisely because `obsFlow` carries a non-trivial conserved
quantity; the obstruction to unique ergodicity is structural. (The explicit
continuum witness is the convex-combination family
`s ↦ s·μFS + (1−s)·δ_{[e₀]}`, `s ∈ [0,1]`, a clean genuine continuum; the
conserved Born coordinates are the *why*.) This still does **not** force FS and
does **not** close A5 — it sharpens the obstruction.

## Honest scope (the whole point — claim NOTHING more)

This tranche does **not** close A5, and does **not** force typicality (the **LLN**
does that, LF1 / papers A & B — see the note above). It (i) shows the FS typicality
*measure* is **singled out** by the sector symmetry `G = U(N)` (a measure-characterisation,
reusing the uniqueness theorem — the LLN then forces frequencies to it), (ii) proves
*no single ontic flow* singles out FS via its own dynamics (the obstruction — a negative
about the **single-flow ergodicity / Birkhoff route, which CSD does NOT use**; it
reinforces that the LLN/i.i.d. route is the operative one), and (iii) thereby **pins the
residual A5 primitive to `G` itself**: the symmetry group `U(N)` is the datum the
canonical measure follows from, and `G`-from-dynamics — deriving the `U(N)`-symmetry of
the ontic flow from the deterministic substrate — is exactly **D1**, the deepest open
content (`Φ = id` in every concrete `SectorData`, or a single non-ergodic phase flow in
D1c). We claim **nothing** about deriving `G`, and nothing about typicality-forcing
beyond the LLN.

`a5_onramp` conjoins (A) and (B). Foundational-triple-only (no `busch_effect_gleason`);
`invariant_measure_uniqueness_cpn` / `fubiniStudyMeasure_unique` are axiom-free.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ} [NeZero N]

/-! ## Computational-basis eigenstate rays -/

omit [NeZero N] in
/-- The computational-basis vector `eⱼ = single j 1` is nonzero. -/
lemma cpBasisVec_ne_zero (j : Fin N) : (EuclideanSpace.single j (1 : ℂ)) ≠ 0 := by
  intro h
  have h2 : (EuclideanSpace.single j (1 : ℂ)) j = (0 : EuclideanSpace ℂ (Fin N)) j := by
    rw [h]
  rw [PiLp.single_apply] at h2
  simp at h2

/-- The computational-basis eigenstate **ray** `[eⱼ] ∈ ℂℙ^{N-1}`. -/
noncomputable def cpBasisRay (j : Fin N) : CPN N :=
  Projectivization.mk ℂ (EuclideanSpace.single j (1 : ℂ)) (cpBasisVec_ne_zero j)

omit [NeZero N] in
/-- Distinct indices give distinct basis rays (`[eⱼ] ≠ [eₖ]` for `j ≠ k`): if they
were equal, some scalar `a` would satisfy `a • eₖ = eⱼ`, impossible at coordinate
`j` (`0 = a·0 ≠ 1`). -/
lemma cpBasisRay_ne (j k : Fin N) (hjk : j ≠ k) : cpBasisRay j ≠ cpBasisRay k := by
  intro he
  rw [cpBasisRay, cpBasisRay] at he
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ _ _ (cpBasisVec_ne_zero j) (cpBasisVec_ne_zero k)).mp he
  -- `a • eₖ` vanishes at coordinate `j` (since `j ≠ k`); but `ha` makes it `eⱼ`, value `1` there.
  have hj : (a • EuclideanSpace.single k (1 : ℂ)) j = 0 := by
    simp only [PiLp.smul_apply, PiLp.single_apply, if_neg hjk, smul_zero]
  rw [ha, PiLp.single_apply, if_pos rfl] at hj
  exact one_ne_zero hj

/-! ## (B) — the eigenstate ray is a fixed point of `obsFlow` -/

/-- **The diagonal-phase flow fixes every computational-basis ray.**
`obsFlow λ t [eⱼ] = [eⱼ]`: the diagonal `obsUnitary λ t` scales `eⱼ` by the unit
phase `obsPhase λ t j`, which is the same projective ray. (This is exactly why the
`Φ ≠ id` witness `obsFlow_ne_id` must use a *superposition* ray, never a basis ray.) -/
theorem obsFlow_fixes_eigenstate (lam : Fin N → ℝ) (t : ℝ) (j : Fin N) :
    obsFlow lam t (cpBasisRay j) = cpBasisRay j := by
  rw [cpBasisRay]
  simp only [obsFlow]
  rw [smul_mk_eq_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨obsPhase lam t j, ?_⟩
  ext i
  rw [obsUnitary_toEuclideanLin_apply]
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · ring

/-- **The Dirac measure at an eigenstate ray is `obsFlow`-invariant.**
Immediate from `Measure.map_dirac` and the fixed-point `obsFlow_fixes_eigenstate`. -/
theorem dirac_eigenstate_obsFlow_invariant (lam : Fin N → ℝ) (t : ℝ) (j : Fin N) :
    Measure.map (obsFlow lam t) (Measure.dirac (cpBasisRay j))
      = Measure.dirac (cpBasisRay j) := by
  have hmeas : Measurable (obsFlow lam t) :=
    (continuous_const_smul (obsUnitary lam t)).measurable
  rw [Measure.map_dirac' hmeas, obsFlow_fixes_eigenstate lam t j]

/-! ## Dirac injectivity on the (Hausdorff Borel) sector -/

omit [NeZero N] in
/-- Distinct points give distinct Dirac measures on `ℂℙ^{N-1}` (singletons are
measurable: `Projectivization.instMeasurableSingletonClass`). -/
lemma dirac_ne_of_ne {p q : CPN N} (h : p ≠ q) :
    (Measure.dirac p : Measure (CPN N)) ≠ Measure.dirac q := by
  intro he
  have hms : MeasurableSet ({q} : Set (CPN N)) := measurableSet_singleton q
  have h1 : (Measure.dirac p : Measure (CPN N)) {q} = 1 := by
    rw [he]; exact (dirac_eq_one_iff_mem hms).mpr rfl
  rw [dirac_eq_one_iff_mem hms] at h1
  exact h h1

/-! ## (A) — the FS typicality MEASURE is singled out by the sector symmetry `G = U(N)` -/

/-- **(A) The FS typicality measure is singled out by the sector symmetry** (a
measure-characterisation, NOT the typicality-forcing — typicality is forced by the
LLN, LF1 / papers A & B; see the file header). Any `U(N)`-invariant probability
measure on the sector `Σ = ℂℙ^{N-1}` **is** the Fubini–Study measure. A restatement
of the axiom-free `fubiniStudyMeasure_unique` (Phase G4): FS is the *symmetry-canonical*
sampling measure — the Born = FS-volume measure consumed downstream is *singled out*
by the `A5` `(π, G)` sector datum rather than posited as an arbitrary law; the LLN then
forces frequencies to its volume ratios. The characterisation is via the symmetry
*group*, not via any single flow (contrast (B) below). -/
theorem fubiniStudy_forced_by_symmetry (p₀ : CPN N)
    (μ : Measure (CPN N)) [IsProbabilityMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
        MeasurePreserving (fun p => U • p) μ μ) :
    μ = fubiniStudyMeasure p₀ :=
  fubiniStudyMeasure_unique p₀ μ (fun U => (hμ_inv U).map_eq)

/-! ## (B) — a single ontic flow does not force FS -/

/-- **(B) The honest negative.** `obsFlow` is **not uniquely ergodic**: it admits at
least two distinct invariant probability measures — the Fubini–Study measure `μFS`
(invariant by `obsFlow_measurePreserving`) and the Dirac measure `δ_{[e₀]}` at a
computational-basis eigenstate ray (invariant by `dirac_eigenstate_obsFlow_invariant`,
since the diagonal phase flow fixes basis rays). They differ: FS is `U(N)`-invariant
while `δ_{[e₀]}` is moved to `δ_{[e₁]}` by a unitary swapping the two rays
(transitivity of the `U(N)`-action), and distinct rays give distinct Dirac measures.

So **no single deterministic ontic flow forces FS** — only the full sector symmetry
`G = U(N)` does (result (A)). This is the obstruction behind the naive
"single ergodic flow whose unique invariant measure is `μFS`" picture, and the reason
`cpSectorDataFlow` / `kSectorDataFlow` (D1c) do not discharge A5. -/
theorem obsFlow_not_uniquely_ergodic (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    ∃ μ ν : Measure (CPN N),
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      Measure.map (obsFlow lam t) μ = μ ∧
      Measure.map (obsFlow lam t) ν = ν ∧ μ ≠ ν := by
  refine ⟨fubiniStudyMeasure p₀, Measure.dirac (cpBasisRay (obsIdx0 hN)),
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · -- μFS is obsFlow-invariant (the Liouville / FS-invariance content).
    exact (obsFlow_measurePreserving lam t p₀).map_eq
  · -- δ_{[e₀]} is obsFlow-invariant (basis ray is a fixed point).
    exact dirac_eigenstate_obsFlow_invariant lam t (obsIdx0 hN)
  · -- μFS ≠ δ_{[e₀]}: otherwise the swap unitary moves a U(N)-invariant Dirac.
    intro hμν
    have hqr : cpBasisRay (obsIdx0 hN) ≠ cpBasisRay (obsIdx1 hN) :=
      cpBasisRay_ne _ _ (obsIdx0_ne_obsIdx1 hN)
    obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ)
      (cpBasisRay (obsIdx0 hN)) (cpBasisRay (obsIdx1 hN))
    have hFSinv := fubiniStudyMeasure_smul_invariant U p₀
    rw [hμν, Measure.map_dirac' (continuous_const_smul U).measurable] at hFSinv
    -- hFSinv : δ_{U•[e₀]} = δ_{[e₀]}, and U•[e₀] = [e₁].
    have hru : (Measure.dirac (cpBasisRay (obsIdx1 hN)) : Measure (CPN N))
        = Measure.dirac (cpBasisRay (obsIdx0 hN)) := by
      have hstep : (Measure.dirac (cpBasisRay (obsIdx1 hN)) : Measure (CPN N))
          = Measure.dirac ((fun p => U • p) (cpBasisRay (obsIdx0 hN))) := by
        congr 1; exact hU.symm
      rw [hstep, hFSinv]
    exact (dirac_ne_of_ne hqr.symm) hru

/-! ## (B′) — the conserved quantity and the continuum of invariant measures -/

/-- **Conserved-quantity reweighting principle (the genuine structural content).**
If a measure-preserving map `T` admits a conserved measurable density
`d` (`d ∘ T = d`), then reweighting an invariant measure `μ` by `d` is again
`T`-invariant: `map T (μ.withDensity d) = μ.withDensity d`. The change of variables
uses `d ∘ T = d` together with `map T μ = μ`
(`MeasurePreserving.lintegral_comp`). General Mathlib-style lemma (no CSD content);
kept local. -/
theorem map_withDensity_of_conserved {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {T : α → α} (hT : MeasureTheory.MeasurePreserving T μ μ)
    {d : α → ENNReal} (hd : Measurable d) (hcons : ∀ x, d (T x) = d x) :
    MeasureTheory.Measure.map T (μ.withDensity d) = μ.withDensity d := by
  ext E hE
  rw [Measure.map_apply hT.measurable hE, withDensity_apply d (hT.measurable hE),
      withDensity_apply d hE, ← lintegral_indicator (hT.measurable hE) d,
      ← lintegral_indicator hE d]
  have hcomp : (T ⁻¹' E).indicator d = fun a => E.indicator d (T a) := by
    funext a
    by_cases ha : T a ∈ E
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr ha) d, Set.indicator_of_mem ha d]
      exact (hcons a).symm
    · rw [Set.indicator_of_notMem (fun h => ha (Set.mem_preimage.mp h)) d,
          Set.indicator_of_notMem ha d]
  rw [hcomp]
  exact hT.lintegral_comp (hd.indicator hE)

/-- **The Born coordinate is a conserved reweighting of every `obsFlow`-invariant
measure.** Instantiating `map_withDensity_of_conserved` at the conserved Born
coordinate `momentMap · i` (`momentMap_obsFlow`): for any measurable density
profile `g`, the reweighted Fubini–Study measure
`μFS.withDensity (g ∘ momentMap · i)` is `obsFlow`-invariant. This is the genuine
conserved-quantity mechanism behind the abundance of invariant measures: the Born
coordinates being constants of motion lets one reweight the typicality measure
freely without breaking invariance. (It does **not** by itself produce a continuum
of *probability* measures — that needs normalisation, i.e. the Duistermaat–Heckman
pushforward law of `momentMap`; the explicit probability continuum below uses the
convex-combination route instead. The conserved coordinate is the structural
reason.) -/
theorem withDensity_momentMap_obsFlow_invariant
    (lam : Fin N → ℝ) (t : ℝ) (p₀ : CPN N) (i : Fin N)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    Measure.map (obsFlow lam t)
        ((fubiniStudyMeasure p₀).withDensity (fun p => g (momentMap p i)))
      = (fubiniStudyMeasure p₀).withDensity (fun p => g (momentMap p i)) :=
  map_withDensity_of_conserved (obsFlow_measurePreserving lam t p₀)
    (hg.comp (momentMap_measurable i)) (fun p => by rw [momentMap_obsFlow])

/-- **(B′) The obstruction is generic: a CONTINUUM of `obsFlow`-invariant
probability measures.** Strengthens `obsFlow_not_uniquely_ergodic` (≥ 2) to an
uncountable, pairwise-distinct family (`Set.InjOn` on `[0,1]`). The witness is the
convex-combination family `f s = s · μFS + (1−s) · δ_{[e₀]}` of the two invariant
probability measures of (B): each is a probability measure (masses sum to one),
each is `obsFlow`-invariant (`map` is `ℝ≥0∞`-linear and fixes both summands), and
they are pairwise distinct — evaluating on `{[e₀]}ᶜ` gives `f s ({[e₀]}ᶜ) =
ofReal s · μFS({[e₀]}ᶜ)` with `μFS({[e₀]}ᶜ) ∈ (0, ∞)` (positivity from
`μFS({[e₀]}) < 1`, which follows from `U(N)`-invariance: `μFS{[e₀]} = μFS{[e₁]}`
on disjoint singletons, so `2·μFS{[e₀]} ≤ 1`), hence `s ↦ f s ({[e₀]}ᶜ)` is
injective.

**The structural reason** for this abundance is the conserved Born coordinate
(`momentMap_obsFlow`, `map_withDensity_of_conserved`,
`withDensity_momentMap_obsFlow_invariant`): a deterministic flow with a
non-trivial constant of motion cannot be uniquely ergodic. **Honest scope:** this
does **not** force FS and does **not** close A5, and typicality is forced not by any
flow but by the **LLN** (LF1 / papers A & B). The FS *measure* is singled out by the
full sector symmetry `G = U(N)` (result (A), `fubiniStudy_forced_by_symmetry`); this
result is a negative about the single-flow ergodicity route (which CSD does not use).
The residue is `G`-from-`D1`. -/
theorem obsFlow_continuum_invariant (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    ∃ f : ℝ → Measure (CPN N),
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
          IsProbabilityMeasure (f s) ∧ Measure.map (obsFlow lam t) (f s) = f s)
      ∧ Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
  classical
  have hmeas : Measurable (obsFlow lam t) :=
    (continuous_const_smul (obsUnitary lam t)).measurable
  set r0 : CPN N := cpBasisRay (obsIdx0 hN) with hr0def
  set r1 : CPN N := cpBasisRay (obsIdx1 hN) with hr1def
  have hr01 : r0 ≠ r1 := cpBasisRay_ne _ _ (obsIdx0_ne_obsIdx1 hN)
  -- δ_{[e₀]} is obsFlow-invariant (the (B) datum, re-expressed in `r0`).
  have hdinv : Measure.map (obsFlow lam t) (Measure.dirac r0) = Measure.dirac r0 := by
    rw [hr0def]; exact dirac_eigenstate_obsFlow_invariant lam t (obsIdx0 hN)
  -- μFS{[e₀]} = μFS{[e₁]} by U(N)-invariance and the swap unitary.
  have hswap : fubiniStudyMeasure p₀ {r1} = fubiniStudyMeasure p₀ {r0} := by
    obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ) r0 r1
    have hpre : (fun p => U • p) ⁻¹' {r1} = {r0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        have h2 : U • x = U • r0 := h.trans hU.symm
        simpa only [inv_smul_smul] using congrArg (fun y => U⁻¹ • y) h2
      · intro h; rw [h]; exact hU
    have hinv := fubiniStudyMeasure_smul_invariant U p₀
    calc fubiniStudyMeasure p₀ {r1}
        = (Measure.map (fun p => U • p) (fubiniStudyMeasure p₀)) {r1} := by rw [hinv]
      _ = fubiniStudyMeasure p₀ ((fun p => U • p) ⁻¹' {r1}) :=
          Measure.map_apply (continuous_const_smul U).measurable (measurableSet_singleton r1)
      _ = fubiniStudyMeasure p₀ {r0} := by rw [hpre]
  -- μFS{[e₀]} < 1.
  have hc1 : fubiniStudyMeasure p₀ {r0} < 1 := by
    have hcc : fubiniStudyMeasure p₀ {r0} + fubiniStudyMeasure p₀ {r0} ≤ 1 := by
      calc fubiniStudyMeasure p₀ {r0} + fubiniStudyMeasure p₀ {r0}
          = fubiniStudyMeasure p₀ {r0} + fubiniStudyMeasure p₀ {r1} := by rw [hswap]
        _ = fubiniStudyMeasure p₀ ({r0} ∪ {r1}) :=
            (measure_union (by simpa using hr01) (measurableSet_singleton r1)).symm
        _ ≤ fubiniStudyMeasure p₀ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hreal : (fubiniStudyMeasure p₀ {r0}).toReal + (fubiniStudyMeasure p₀ {r0}).toReal ≤ 1 := by
      calc (fubiniStudyMeasure p₀ {r0}).toReal + (fubiniStudyMeasure p₀ {r0}).toReal
          = (fubiniStudyMeasure p₀ {r0} + fubiniStudyMeasure p₀ {r0}).toReal :=
            (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)).symm
        _ ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hcc
        _ = 1 := ENNReal.toReal_one
    have hcr : (fubiniStudyMeasure p₀ {r0}).toReal < 1 := by linarith
    calc fubiniStudyMeasure p₀ {r0}
        = ENNReal.ofReal (fubiniStudyMeasure p₀ {r0}).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hcr
      _ = 1 := ENNReal.ofReal_one
  -- {[e₀]}ᶜ has positive finite μFS-mass and is δ_{[e₀]}-null.
  have hAfin : fubiniStudyMeasure p₀ ({r0}ᶜ) ≠ ⊤ := measure_ne_top _ _
  have hAval : fubiniStudyMeasure p₀ ({r0}ᶜ) = 1 - fubiniStudyMeasure p₀ {r0} := by
    rw [measure_compl (measurableSet_singleton r0) (measure_ne_top _ _), measure_univ]
  have hApos : fubiniStudyMeasure p₀ ({r0}ᶜ) ≠ 0 := by
    rw [hAval, ne_eq, tsub_eq_zero_iff_le, not_le]; exact hc1
  have hdir0 : Measure.dirac r0 ({r0}ᶜ) = 0 := by
    simp [Measure.dirac_apply' r0 (measurableSet_singleton r0).compl]
  refine ⟨fun s => ENNReal.ofReal s • fubiniStudyMeasure p₀
            + ENNReal.ofReal (1 - s) • Measure.dirac r0, ?_, ?_⟩
  · -- Each `f s` (s ∈ [0,1]) is an invariant probability measure.
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    refine ⟨⟨?_⟩, ?_⟩
    · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
          measure_univ, measure_univ, mul_one, mul_one,
          ← ENNReal.ofReal_add hs0 (by linarith), show s + (1 - s) = 1 by ring,
          ENNReal.ofReal_one]
    · rw [Measure.map_add _ _ hmeas, Measure.map_smul, Measure.map_smul,
          (obsFlow_measurePreserving lam t p₀).map_eq, hdinv]
  · -- Pairwise distinct: `s ↦ f s ({[e₀]}ᶜ) = ofReal s · μFS({[e₀]}ᶜ)` is injective.
    intro s hs s' hs' hss
    have hfsA : ∀ x : ℝ,
        (ENNReal.ofReal x • fubiniStudyMeasure p₀
            + ENNReal.ofReal (1 - x) • Measure.dirac r0) ({r0}ᶜ)
          = ENNReal.ofReal x * fubiniStudyMeasure p₀ ({r0}ᶜ) := fun x => by
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
          hdir0, mul_zero, add_zero]
    have key := congrArg (fun μ : Measure (CPN N) => μ ({r0}ᶜ)) hss
    simp only [] at key
    rw [hfsA s, hfsA s'] at key
    have hofeq : ENNReal.ofReal s = ENNReal.ofReal s' :=
      (ENNReal.mul_left_inj hApos hAfin).mp key
    have hconv := congrArg ENNReal.toReal hofeq
    rwa [ENNReal.toReal_ofReal hs.1, ENNReal.toReal_ofReal hs'.1] at hconv

/-! ## (B′′) — `obsFlow` is not even `μFS`-ERGODIC (the sharper, FS-specific obstruction)

`obsFlow_not_uniquely_ergodic` (≥ 2 invariant measures) and `obsFlow_continuum_invariant`
(a continuum) say `obsFlow` does not *uniquely* single out `μFS`. They do **not** say
`obsFlow` fails to be ergodic *with respect to `μFS` itself*: a non-uniquely-ergodic map can
still be ergodic for one of its invariant measures. This block proves the sharper statement:
`obsFlow` is **not `μFS`-ergodic**, because it has a non-trivial `μFS`-invariant set
(`{m₀ ≥ m₁}`), of measure strictly between `0` and `1`. The structural reason is exactly the
conserved Born coordinate `momentMap · i` (`momentMap_obsFlow`): a *non-constant* constant of
motion produces a non-trivial invariant set, which is precisely the failure of ergodicity.
**Framing (LLN, not ergodicity):** CSD forces *typicality* by the LAW OF LARGE NUMBERS over
i.i.d. preparations (LF1 / papers A & B), NOT by single-flow time-averaging. So this result is a
**negative about the stat-mech single-flow ergodicity (Birkhoff) route — a route CSD does not
use**: it shows one cannot shortcut to `μFS` through one flow's dynamics, which *reinforces* that
the LLN/i.i.d. route (with the symmetry-canonical measure of (A)) is the operative one. It is NOT
an obstruction to CSD's typicality (there is none — the LLN does the forcing). -/

/-- **The Fubini–Study measure has full support.** Any nonempty open set `O ⊆ ℂℙ^{N-1}` has
positive `μFS` mass. `μFS = (orbitMap p₀)∗ unitaryHaarProb`; the orbit-map preimage of a
nonempty open `O` is open (continuity) and nonempty (U(N)-transitivity), and Haar measure is
`IsOpenPosMeasure`. (General Mathlib-style projective-geometry fact; the witness sets below use
it to bound the invariant set away from `0` and `1`.) -/
theorem fubiniStudyMeasure_pos_of_isOpen (p₀ : CPN N) {O : Set (CPN N)}
    (hO : IsOpen O) (hne : O.Nonempty) :
    fubiniStudyMeasure p₀ O ≠ 0 := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ) p₀ q
  have hopen : IsOpen (orbitMap p₀ ⁻¹' O) := hO.preimage (orbit_map_continuous p₀)
  have hnem : (orbitMap p₀ ⁻¹' O).Nonempty :=
    ⟨U, by rw [Set.mem_preimage, orbitMap, hU]; exact hq⟩
  rw [fubiniStudyMeasure, Measure.map_apply (orbit_map_measurable p₀) hO.measurableSet]
  exact hopen.measure_ne_zero unitaryHaarProb hnem

omit [NeZero N] in
/-- The strict moment-coordinate comparison `{p | momentMap p i < momentMap p j}` is **open**.
Pulled back through the open quotient map `mk'`, it is `{v ≠ 0 | ‖vᵢ‖²/‖v‖² < ‖vⱼ‖²/‖v‖²}`,
open as a strict inequality of continuous functions; its image under the open map `mk'` is the
set itself (surjectivity). Uses `Projectivization.isOpenMap_mk'` / `momentMap_mk`. -/
theorem isOpen_momentMap_lt (i j : Fin N) :
    IsOpen {p : CPN N | momentMap p i < momentMap p j} := by
  have hsurj : Function.Surjective
      (Projectivization.mk' ℂ : {v : EuclideanSpace ℂ (Fin N) // v ≠ 0} → CPN N) :=
    Projectivization.isOpenQuotientMap_mk'.surjective
  have hcont : ∀ k : Fin N, Continuous
      (fun v : {w : EuclideanSpace ℂ (Fin N) // w ≠ 0} =>
        ‖(v : EuclideanSpace ℂ (Fin N)) k‖ ^ 2 / ‖(v : EuclideanSpace ℂ (Fin N))‖ ^ 2) := by
    intro k
    have h1 : Continuous (fun v : {w : EuclideanSpace ℂ (Fin N) // w ≠ 0} =>
        (v : EuclideanSpace ℂ (Fin N)) k) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin N => ℂ) k).comp continuous_subtype_val
    have h2 : Continuous (fun v : {w : EuclideanSpace ℂ (Fin N) // w ≠ 0} =>
        (v : EuclideanSpace ℂ (Fin N))) := continuous_subtype_val
    exact (h1.norm.pow 2).div (h2.norm.pow 2)
      (fun v => pow_ne_zero 2 (norm_ne_zero_iff.mpr v.2))
  rw [← Set.image_preimage_eq {p : CPN N | momentMap p i < momentMap p j} hsurj]
  apply Projectivization.isOpenMap_mk'
  have hpre : (Projectivization.mk' ℂ ⁻¹' {p : CPN N | momentMap p i < momentMap p j})
      = {v : {w : EuclideanSpace ℂ (Fin N) // w ≠ 0} |
          ‖(v : EuclideanSpace ℂ (Fin N)) i‖ ^ 2 / ‖(v : EuclideanSpace ℂ (Fin N))‖ ^ 2 <
          ‖(v : EuclideanSpace ℂ (Fin N)) j‖ ^ 2 / ‖(v : EuclideanSpace ℂ (Fin N))‖ ^ 2} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Projectivization.mk'_eq_mk, momentMap_mk]
  rw [hpre]
  exact isOpen_lt (hcont i) (hcont j)

omit [NeZero N] in
/-- The moment-map coordinate at a computational-basis ray: `momentMap [eᵣ] q = δ_{qr}`.
The non-constancy witness for the conserved Born coordinate. -/
lemma momentMap_cpBasisRay (q r : Fin N) :
    momentMap (cpBasisRay r) q = if q = r then 1 else 0 := by
  rw [cpBasisRay, momentMap_mk, PiLp.norm_single, norm_one, one_pow, div_one,
    PiLp.single_apply]
  split_ifs with h
  · rw [norm_one, one_pow]
  · rw [norm_zero]; norm_num

/-- **(1) The non-constant conserved observable (the conceptual heart).** The Born coordinate
`momentMap · i` is, for `obsFlow`, simultaneously:

* a **constant of motion** — `momentMap (obsFlow λ t p) i = momentMap p i` for every `p`
  (`momentMap_obsFlow`: the diagonal phase `e^{itλᵢ}` leaves `|ψᵢ|²` unchanged);
* **measurable** (`momentMap_measurable`);
* **non-constant** — it takes the value `1` at `[eᵢ]` and `0` at `[eⱼ]` (`j ≠ i`)
  (`momentMap_cpBasisRay`).

This is exactly a *non-constant constant of motion*. Its existence is the obstruction to
ergodicity (next theorem): an ergodic flow has only a.e.-constant conserved observables. -/
theorem momentMap_obsFlow_nonconstant_conserved (hN : 1 < N) (lam : Fin N → ℝ) (t : ℝ) :
    (∀ p, momentMap (obsFlow lam t p) (obsIdx0 hN) = momentMap p (obsIdx0 hN))
    ∧ Measurable (fun p : CPN N => momentMap p (obsIdx0 hN))
    ∧ ∃ p q : CPN N, momentMap p (obsIdx0 hN) ≠ momentMap q (obsIdx0 hN) := by
  refine ⟨fun p => momentMap_obsFlow lam t p (obsIdx0 hN), momentMap_measurable _,
    cpBasisRay (obsIdx0 hN), cpBasisRay (obsIdx1 hN), ?_⟩
  rw [momentMap_cpBasisRay, momentMap_cpBasisRay, if_pos rfl,
    if_neg (obsIdx0_ne_obsIdx1 hN)]
  norm_num

/-- **(2) Headline: `obsFlow` is NOT `μFS`-ergodic.** The set `S = {p | momentMap p 1 ≤
momentMap p 0}` (`{m₀ ≥ m₁}`) is an `obsFlow`-invariant measurable set with
`0 < μFS S < 1`, contradicting the zero-one law `PreErgodic.prob_eq_zero_or_one`.

* **Invariant** (`obsFlow ⁻¹' S = S`): both coordinates are conserved (`momentMap_obsFlow`).
* **Measurable**: `measurableSet_le` of two `momentMap_measurable` coordinates.
* **`μFS S ≠ 0`**: `S ⊇ {m₁ < m₀}`, open (`isOpen_momentMap_lt`) and nonempty (`[e₀]` has
  `m₁ = 0 < 1 = m₀`), so positive by full support (`fubiniStudyMeasure_pos_of_isOpen`).
* **`μFS S ≠ 1`**: `Sᶜ = {m₀ < m₁}`, open and nonempty (`[e₁]` has `m₀ = 0 < 1 = m₁`), so
  positive; hence `μFS S = 1 − μFS Sᶜ < 1`.

This is **sharper than `obsFlow_not_uniquely_ergodic`**: not merely "≥ 2 invariant measures",
but "`μFS` itself is not an ergodic measure for `obsFlow`". The two are independent — a
non-uniquely-ergodic map can still be ergodic for a particular invariant measure. The
obstruction is the non-constant conserved Born coordinate of (1). -/
theorem obsFlow_not_ergodic (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    ¬ Ergodic (obsFlow lam t) (fubiniStudyMeasure p₀) := by
  intro herg
  set i := obsIdx0 hN with hi
  set j := obsIdx1 hN with hj
  have hji : j ≠ i := by rw [hi, hj]; exact (obsIdx0_ne_obsIdx1 hN).symm
  set S : Set (CPN N) := {p | momentMap p j ≤ momentMap p i} with hS
  -- S is measurable.
  have hSmeas : MeasurableSet S :=
    measurableSet_le (momentMap_measurable j) (momentMap_measurable i)
  -- S is obsFlow-invariant (both coordinates conserved).
  have hSinv : obsFlow lam t ⁻¹' S = S := by
    ext p
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, momentMap_obsFlow]
  -- The zero-one law: μFS S ∈ {0, 1}.
  have h01 := herg.toPreErgodic.prob_eq_zero_or_one hSmeas hSinv
  -- μFS S ≠ 0: S contains the open nonempty set {m_j < m_i}.
  have hsub : {p : CPN N | momentMap p j < momentMap p i} ⊆ S := by
    rw [hS]; exact Set.setOf_subset_setOf.2 (fun p => le_of_lt)
  have hgtne : {p : CPN N | momentMap p j < momentMap p i}.Nonempty :=
    ⟨cpBasisRay i, by
      simp only [Set.mem_setOf_eq, momentMap_cpBasisRay, if_neg hji]; norm_num⟩
  have hSne : fubiniStudyMeasure p₀ S ≠ 0 := by
    intro h0
    exact (fubiniStudyMeasure_pos_of_isOpen p₀ (isOpen_momentMap_lt j i) hgtne)
      (le_antisymm (h0 ▸ measure_mono hsub) (zero_le _))
  -- μFS S ≠ 1: Sᶜ = {m_i < m_j} is open nonempty, hence positive.
  have hScompl : Sᶜ = {p : CPN N | momentMap p i < momentMap p j} := by
    rw [hS]; ext p; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hltne : {p : CPN N | momentMap p i < momentMap p j}.Nonempty :=
    ⟨cpBasisRay j, by
      simp only [Set.mem_setOf_eq, momentMap_cpBasisRay, if_neg hji.symm]; norm_num⟩
  have hScpos : fubiniStudyMeasure p₀ Sᶜ ≠ 0 := by
    rw [hScompl]; exact fubiniStudyMeasure_pos_of_isOpen p₀ (isOpen_momentMap_lt i j) hltne
  -- Combine: neither 0 nor 1 is possible.
  rcases h01 with h0 | h1
  · exact hSne h0
  · exact hScpos <| by
      rw [measure_compl hSmeas (measure_ne_top _ _), measure_univ, h1, tsub_self]

/-! ## Capstone -/

/-- **A5 single-flow obstruction capstone.** Packages the obstruction story:

1. `momentMap_obsFlow_nonconstant_conserved` — a single flow (`obsFlow`) carries a
   **non-constant conserved observable**, the Born coordinate `momentMap · 0` (conserved,
   measurable, takes distinct values at `[e₀]`, `[e₁]`).
2. `obsFlow_not_ergodic` — therefore `obsFlow` is **not `μFS`-ergodic**: the non-constant
   constant of motion produces a non-trivial `μFS`-invariant set (`{m₀ ≥ m₁}`, measure in
   `(0,1)`).

**Honest scope (LLN, not ergodicity).** Typicality is forced by the LAW OF LARGE NUMBERS
(LF1 / papers A & B), NOT by an ergodic flow. This result CLOSES the **single-flow ergodicity
(Birkhoff) obstruction story** — a route CSD does NOT use: `obsFlow`, with its conserved Born
coordinates, is provably not `μFS`-ergodic, so one cannot shortcut to `μFS` through one flow's
dynamics. That reinforces the LLN/i.i.d. route rather than exposing a gap. It does **not** close
A5: the FS *measure* is singled out by the full sector symmetry `G = U(N)`
(`fubiniStudy_forced_by_symmetry`) and the LLN forces frequencies to it; the residue is
`G`-from-`D1` — deriving the `U(N)`-symmetry of the ontic dynamics from the deterministic
substrate, which remains open (`Φ = id` / single non-ergodic phase flow in the concrete
`SectorData` instances). -/
theorem a5_obstruction_capstone (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    ((∀ p, momentMap (obsFlow lam t p) (obsIdx0 hN) = momentMap p (obsIdx0 hN))
      ∧ Measurable (fun p : CPN N => momentMap p (obsIdx0 hN))
      ∧ ∃ p q : CPN N, momentMap p (obsIdx0 hN) ≠ momentMap q (obsIdx0 hN))
    ∧ ¬ Ergodic (obsFlow lam t) (fubiniStudyMeasure p₀) :=
  ⟨momentMap_obsFlow_nonconstant_conserved hN lam t, obsFlow_not_ergodic hN p₀ lam t⟩

/-- **A5 onramp.** Conjunction of the two honest results:

* **(A)** `fubiniStudy_forced_by_symmetry`: any `U(N)`-invariant probability measure on the
  sector `ℂℙ^{N-1}` **is** the Fubini–Study measure — so the FS sampling *measure* is
  *singled out* by the sector symmetry `G = U(N)`, not posited as an arbitrary law.
* **(B)** `obsFlow_not_uniquely_ergodic`: a single ontic flow (`obsFlow`) does **not**
  single out FS via its dynamics — it has at least two distinct invariant probability measures.

**Honest framing (LLN, not ergodicity).** Typicality — frequencies converging to the measure's
volume weights — is forced by the **LAW OF LARGE NUMBERS** (LF1 / papers A & B) over i.i.d.
preparations, NOT by symmetry and NOT by an ergodic flow. (A) only singles out *which* measure is
canonical (the unique `G`-invariant one); (B) is a negative about the single-flow ergodicity route
CSD does not use. So this does **not** force typicality (the LLN does) and does **not** close A5;
the residual A5 primitive is `G = U(N)` **itself**, which reduces to **D1** (deriving the
`U(N)`-symmetry of the ontic dynamics from the deterministic substrate — *not done*, the deepest
open content). It locates the measure-characterisation in the symmetry and pins the residue. -/
theorem a5_onramp (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    (∀ (μ : Measure (CPN N)), IsProbabilityMeasure μ →
        (∀ U : Matrix.unitaryGroup (Fin N) ℂ, MeasurePreserving (fun p => U • p) μ μ) →
        μ = fubiniStudyMeasure p₀)
    ∧
    (∃ μ ν : Measure (CPN N),
        IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
        Measure.map (obsFlow lam t) μ = μ ∧
        Measure.map (obsFlow lam t) ν = ν ∧ μ ≠ ν) := by
  refine ⟨fun μ hp h => ?_, obsFlow_not_uniquely_ergodic hN p₀ lam t⟩
  haveI := hp
  exact fubiniStudy_forced_by_symmetry p₀ μ h

end LF4
end CSD
