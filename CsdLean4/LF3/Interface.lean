import CsdLean4.LF3.Setup
import CsdLean4.LF3.Hamiltonian
import CsdLean4.LF3.SectorSeparation
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Projectors.SectorVolume
import CsdLean4.LF3.Projectors.LF2Interface
import CsdLean4.LF3.Singlet.State
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.Singlet.Kernel
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF1.MainTheorem
import CsdLean4.LF2.Interface
import CsdLean4.LF2.Preparation

/-!
# LF3 Interface: the LF1 ↔ LF2 ↔ LF3 chain closure

**Category:** 3-Local (LF3 headline exports: `LF3_main_theorem`, `LF3_finite_leakage_theorem`, three chain capstones).

Paper §9.13 / spec §10.5.

Five exported theorems, in descending order of programme-level importance:

1. `LF3_singlet_frequency_convergence_born`: repeated singlet trials produce
   frequencies that converge a.s. to `‖cAmp s t (a, b)‖²`. The Born-rule
   form of the empirical chain — the reason LF3 exists.
2. `LF3_singlet_frequency_convergence`: the pre-Born form of the same chain,
   landing on `P_{st}(a, b) = (1 − st a·b)/4`.
3. `LF3_singlet_frequency_convergence_born_inner`: bra-ket variant landing on
   `‖⟨v, ψ⁻⟩‖²` for a caller-supplied joint spin eigenstate `v`.
4. `LF3_main_theorem`: eight-conjunct strong-readout package (kernel,
   correlation, A-marginal, B-marginal, no-signalling on each side,
   pointer-completeness on each side).
5. `LF3_finite_leakage_theorem`: four-conjunct finite-leakage stability.

The conceptual chain (what a fully discharged `PureSingletPreparation` would
compose) is:

- `Projectors.LF2Interface.sectorVolume_eq_LF2_Born` (LF3 → LF2 Born form)
- `LF2.Interface.LF1_main_theorem_projective` (LF2 → LF1 frequency limit)
- `LF1.MainTheorem.LF1_main_theorem_ae` (LF1 a.s. convergence)
- `Singlet.Kernel.cst_squared_eq` (algebraic core, axiom-free)

The actual proof bodies below currently consume the bundled `PureSingletPreparation`
field `prep.weight_eq_P_st`, which packages the first two components above into
a single hypothesis pending LF4 discharge. The chain capstones therefore compose
`LF1_main_theorem_projective` + `prep.weight_eq_P_st` + `cst_squared_eq`
directly; `sectorVolume_eq_LF2_Born` enters through `weight_eq_P_st` once LF4
supplies the structural constructor.
-/

open scoped BigOperators
open MeasureTheory Set Filter

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]

/-! ### Strong-readout main theorem (paper §9.13) -/

/-- **`LF3_main_theorem`** — eight-conjunct strong-readout package.

Conjuncts (paper §9.13 + §7.10 + §2.8):
  1. Singlet kernel `P_st = (1 − st·a·b)/4`.
  2. Bell-singlet correlation `∑ st · P_st = −a·b`.
  3. A-marginal `∑_t P_st = 1/2`.
  4. B-marginal `∑_s P_st = 1/2`.
  5. Operational no-signalling, A side.
  6. Operational no-signalling, B side.
  7. Pointer-completeness on the A wing.
  8. Pointer-completeness on the B wing. -/
theorem LF3_main_theorem
    (S : SystemApparatusSetup K_A K_B H_SA) (ctx : MeasurementContext) :
    (∀ s t : Sign, P_st ctx.a ctx.b s t = (1 - s.val * t.val * dotR ctx.a ctx.b) / 4)
    ∧ (∑ st : Sign × Sign, st.1.val * st.2.val * P_st ctx.a ctx.b st.1 st.2
         = -(dotR ctx.a ctx.b))
    ∧ (∀ s : Sign, ∑ t : Sign, P_st ctx.a ctx.b s t = 1/2)
    ∧ (∀ t : Sign, ∑ s : Sign, P_st ctx.a ctx.b s t = 1/2)
    ∧ (∀ a b b' : DetectorSetting, ∀ s : Sign,
        (∑ t : Sign, P_st a b s t) = (∑ t : Sign, P_st a b' s t))
    ∧ (∀ a a' b : DetectorSetting, ∀ t : Sign,
        (∑ s : Sign, P_st a b s t) = (∑ s : Sign, P_st a' b s t))
    ∧ (S.ptrA.proj .plus + S.ptrA.proj .minus = (1 : K_A →L[ℂ] K_A))
    ∧ (S.ptrB.proj .plus + S.ptrB.proj .minus = (1 : K_B →L[ℂ] K_B)) :=
  ⟨fun s t => context_singlet_kernel ctx s t,
   context_correlation_eq_neg_dot ctx,
   context_marginal_a ctx,
   context_marginal_b ctx,
   no_signalling_strong_readout_a,
   no_signalling_strong_readout_b,
   pointer_a_complete S,
   pointer_b_complete S⟩

/-! ### Finite-leakage main theorem (paper §9.13 §7) -/

/-- **`LF3_finite_leakage_theorem`** — four-conjunct finite-leakage stability.

Each conjunct gives a quantitative deviation bound from the strong-readout
ideal. The leakage parameters `εA`, `εB` are supplied through a
`LeakageCompat` structure parameterising the abstract pointer/measurement
data; in the strong-readout limit `εA = εB = 0` and each bound reduces to
the corresponding strong-readout identity from `LF3_main_theorem`. -/
theorem LF3_finite_leakage_theorem
    {S : SystemApparatusSetup K_A K_B H_SA}
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (ctx : MeasurementContext)
    (L : LeakageCompat P M φA0 φB0) :
    -- (1) Pointer-sector probability deviation
    (∀ s t : Sign,
      |sectorVolume P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) s t
        - P_st ctx.a ctx.b s t|
        ≤ L.εA + L.εB + L.εA * L.εB)
    -- (2) Correlation deviation
    ∧ |(∑ st : Sign × Sign,
          st.1.val * st.2.val
            * sectorVolume P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) st.1 st.2)
       - (-(dotR ctx.a ctx.b))|
       ≤ 4 * (L.εA + L.εB + L.εA * L.εB)
    -- (3) A-marginal deviation
    ∧ (∀ s : Sign,
        |(∑ t : Sign, sectorVolume P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) s t) - 1/2|
          ≤ 2 * (L.εA + L.εB + L.εA * L.εB))
    -- (4) B-marginal deviation
    ∧ (∀ t : Sign,
        |(∑ s : Sign, sectorVolume P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) s t) - 1/2|
          ≤ 2 * (L.εA + L.εB + L.εA * L.εB)) :=
  ⟨fun s t => singlet_pointer_probability_finite_leakage P M φA0 φB0 ctx.a ctx.b L s t,
   correlation_finite_leakage_bound P M φA0 φB0 ctx.a ctx.b L,
   fun s => marginal_a_finite_leakage_bound P M φA0 φB0 ctx.a ctx.b L s,
   fun t => marginal_b_finite_leakage_bound P M φA0 φB0 ctx.a ctx.b L t⟩

/-! ### LF1 ↔ LF2 ↔ LF3 empirical chain (paper §9.13, spec §10.5)

The full empirical interpretation chain, under the option (B) design
(2026-05-18):

```
LF3 pointer-sector weight P_st(a, b)
  = (via born_rank_one + jed.born_eq_P_st = OP_p_at_jointEig_eq_P_st)
  OP.p (rankOneEffect (jed.eig s t))
  = (via prep.bridge_op_p, the LF4 discharge target)
  prepMeasure((prep.O_region s t).preEvent)
  = (via LF1.MainTheorem.LF1_main_theorem_ae)
  LF1 trial-frequency limit lim n→∞ (1/n) ∑ 𝟙_{O_{st}}(ω_k)
```

The chain bridge `prep.bridge_op_p` discharges the LF1 ontic outcome
weight as `ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))`, where
the OP is built from `μFS + bridge + prepMeasure + PP.rep` via
`LF2.OperationalPackage.fromPreparation`. The `OP.p ↔ P_st` identity is
discharged by `LF3.OP_p_at_jointEig_eq_P_st` (cites `busch_effect_gleason`
via `LF2.pure_state_born_weights_of_certainty`). LF4-todo §2
(preparation ↔ Hilbert correspondence) and §7 (projective-first outcomes)
are the two LF4 work items behind the `bridge_op_p` hypothesis. -/

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **Pre-Born form of the empirical chain.** For each `(s, t)` pointer
    sector, the empirical frequency of `prep.O_region s t` over
    repeated trials converges almost surely to `P_{st}(a, b) = (1 − st a·b)/4`,
    given:
    - an LF2 sector structure `D` with projection `π`,
    - an LF1 trial model `T` over `D.toOntic`,
    - a `PureSingletPreparation D ctx N` bundle (option (B)) supplying:
      the projective reference measure `μFS` + measure bridge, the static
      pure preparation `PP` with rep + Dirac concentration, the joint
      spin eigenstate data `jed` for `ctx` (with the Born identity
      `‖⟨PP.ψ, eig s t⟩‖² = P_st`), the ontic outcome regions, and the
      bridge `prepMeasure((O_region s t).preEvent) = OP.p ↔ rank-1 sector
      effect` (LF4 discharge target),
    - pairwise independence of the trial indicators on the
      `prep.O_region s t` family. -/
theorem LF3_singlet_frequency_convergence
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n))) :
    ∀ s t, ∀ᵐ ω ∂ T.trialMeasure,
       Tendsto
         (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
         atTop
         (nhds (P_st ctx.a ctx.b s t)) := by
  intro s t
  have h_ae := D.toOntic.LF1_main_theorem_ae T (prep.O_region s t) (hindep s t)
  have h_weight : (prep.O_region s t).weightReal = P_st ctx.a ctx.b s t := by
    show ENNReal.toReal (((D.toOntic.prepMeasure :
            MeasureTheory.ProbabilityMeasure SigmaSpace) : MeasureTheory.Measure SigmaSpace)
              (prep.O_region s t).preEvent) = _
    rw [prep.weight_eq_P_st s t]
    exact ENNReal.toReal_ofReal (P_st_nonneg ctx.a ctx.b s t)
  rwa [h_weight] at h_ae

/-- **Born-mediated form of the empirical chain (closed-form amplitude).**
    Identifies the pre-Born target `P_{st}(a, b)` with the squared
    closed-form singlet amplitude `‖cAmp s t (a, b)‖²` via `cst_squared_eq`.
    `cAmp` is the real-valued representative `√P_st`; the bra-ket form
    `‖⟨v, ψ⁻⟩‖²` is recovered by `LF3_singlet_frequency_convergence_born_inner`
    below, given an actual joint spin eigenstate `v`. -/
theorem LF3_singlet_frequency_convergence_born
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n))) :
    ∀ s t, ∀ᵐ ω ∂ T.trialMeasure,
       Tendsto
         (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
         atTop
         (nhds (‖cAmp ctx.a ctx.b s t‖ ^ 2)) := by
  intro s t
  have h_pre := LF3_singlet_frequency_convergence D T ctx prep hindep s t
  rw [← cst_squared_eq ctx.a ctx.b s t] at h_pre
  exact h_pre

/-- **Born-form empirical chain with a genuine bra-ket amplitude.** The
    empirical frequency converges to `‖⟨v_{st}, ψ⁻⟩‖²` where `v_{st}` is an
    actual joint spin eigenstate `|s_a, t_b⟩` supplied by the caller. The
    `h_inner` hypothesis says `‖⟨v_{st}, ψ⁻⟩‖² = P_{st}(a, b)`, which is the
    rank-1 projector identity (`jointSpinProj = |v⟩⟨v|`) plus the
    expectation calculation; a v2 with a constructed `jointSpinEig` from the
    spectral decomposition of `jointSpinProj` discharges it.

    This is the **physically faithful** form of the LF1↔LF2↔LF3 chain: the
    RHS `‖⟨v, ψ⁻⟩‖²` is a genuine Hilbert-space inner product, not a
    closed-form repackaging. -/
theorem LF3_singlet_frequency_convergence_born_inner
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n)))
    (jointSpinEig : Sign → Sign → EuclideanSpace ℂ (Fin 2 × Fin 2))
    (h_inner : ∀ s t,
        ‖inner ℂ (jointSpinEig s t) singlet‖ ^ 2 = P_st ctx.a ctx.b s t) :
    ∀ s t, ∀ᵐ ω ∂ T.trialMeasure,
       Tendsto
         (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
         atTop
         (nhds (‖inner ℂ (jointSpinEig s t) singlet‖ ^ 2)) := by
  intro s t
  have h_pre := LF3_singlet_frequency_convergence D T ctx prep hindep s t
  rw [← h_inner s t] at h_pre
  exact h_pre

/-! ### Joint partition convergence (Phase 8)

The per-sector capstones above give `∀ s t, ∀ᵐ ω, Tendsto ...` — the
order is "for each sector, a.s. convergence to that sector's P_st".
For chain consumers that need the joint a.s. statement — "almost surely,
for *every* sector simultaneously the empirical frequency converges to
the corresponding P_st" — the order swaps to `∀ᵐ ω, ∀ s t, Tendsto ...`.

The swap is a finite-intersection-of-full-measure-sets argument:
`Sign × Sign` is finite (hence countable), and Mathlib's
`MeasureTheory.ae_all_iff` provides the swap for countable index types.
This is the standard "joint vs per-element" upgrade pattern. -/

/-- **Joint partition convergence (pre-Born form).** Almost surely on
    the trial-sequence probability space, for *every* pointer sector
    `(s, t)` simultaneously the empirical frequency of
    `prep.O_region s t` converges to `P_st ctx.a ctx.b s t`. Cf.
    `LF3_singlet_frequency_convergence` which gives the per-sector
    statement. -/
theorem LF3_singlet_frequency_convergence_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
       ∀ s t,
         Tendsto
           (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
           atTop
           (nhds (P_st ctx.a ctx.b s t)) := by
  rw [MeasureTheory.ae_all_iff]
  intro s
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact LF3_singlet_frequency_convergence D T ctx prep hindep s t

/-- **Joint partition convergence (Born form, closed-form amplitude).**
    Almost surely, for every `(s, t)` the empirical frequency converges
    to `‖cAmp ctx.a ctx.b s t‖²`. Joint version of
    `LF3_singlet_frequency_convergence_born`. -/
theorem LF3_singlet_frequency_convergence_born_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
       ∀ s t,
         Tendsto
           (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
           atTop
           (nhds (‖cAmp ctx.a ctx.b s t‖ ^ 2)) := by
  rw [MeasureTheory.ae_all_iff]
  intro s
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact LF3_singlet_frequency_convergence_born D T ctx prep hindep s t

/-- **Joint partition convergence (Born form, bra-ket amplitude).**
    Almost surely, for every `(s, t)` the empirical frequency converges
    to `‖⟨jointSpinEig s t, singlet⟩‖²`. Joint version of
    `LF3_singlet_frequency_convergence_born_inner`. -/
theorem LF3_singlet_frequency_convergence_born_inner_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n)))
    (jointSpinEig : Sign → Sign → EuclideanSpace ℂ (Fin 2 × Fin 2))
    (h_inner : ∀ s t,
        ‖inner ℂ (jointSpinEig s t) singlet‖ ^ 2 = P_st ctx.a ctx.b s t) :
    ∀ᵐ ω ∂ T.trialMeasure,
       ∀ s t,
         Tendsto
           (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
           atTop
           (nhds (‖inner ℂ (jointSpinEig s t) singlet‖ ^ 2)) := by
  rw [MeasureTheory.ae_all_iff]
  intro s
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact LF3_singlet_frequency_convergence_born_inner D T ctx prep hindep
    jointSpinEig h_inner s t

end LF3
end CSD
