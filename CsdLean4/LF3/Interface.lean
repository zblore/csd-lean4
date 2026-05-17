import CsdLean4.LF3.Setup
import CsdLean4.LF3.Hamiltonian
import CsdLean4.LF3.BranchSeparation
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Projectors.BranchWeight
import CsdLean4.LF3.Projectors.LF2Interface
import CsdLean4.LF3.Singlet.State
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.Singlet.Kernel
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF1.MainTheorem
import CsdLean4.LF2.Interface

/-!
# LF3 Interface: the LF1 ↔ LF2 ↔ LF3 chain closure

Paper §9.13 / spec §10.5.

Four exported theorems, in descending order of programme-level importance:

1. `LF3_singlet_frequency_convergence_born`: repeated singlet trials produce
   frequencies that converge a.s. to `‖cAmp s t (a, b)‖²`. The Born-rule
   form of the empirical chain — the reason LF3 exists.
2. `LF3_singlet_frequency_convergence`: the pre-Born form of the same chain,
   landing on `P_{st}(a, b) = (1 − st a·b)/4`.
3. `LF3_main_theorem`: eight-conjunct strong-readout package (kernel,
   correlation, A-marginal, B-marginal, no-signalling on each side,
   pointer-completeness on each side).
4. `LF3_finite_leakage_theorem`: four-conjunct finite-leakage stability.

The chain composes:
- `Projectors.LF2Interface.branchWeight_eq_LF2_Born` (LF3 → LF2 Born form)
- `LF2.Interface.LF1_main_theorem_projective` (LF2 → LF1 frequency limit)
- `LF1.MainTheorem.LF1_main_theorem_ae` (LF1 a.s. convergence)
- `Singlet.Kernel.cst_squared_eq` (algebraic core, axiom-free)
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
      |branchWeight P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) s t
        - P_st ctx.a ctx.b s t|
        ≤ L.εA + L.εB + L.εA * L.εB)
    -- (2) Correlation deviation
    ∧ |(∑ st : Sign × Sign,
          st.1.val * st.2.val
            * branchWeight P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) st.1 st.2)
       - (-(dotR ctx.a ctx.b))|
       ≤ 4 * (L.εA + L.εB + L.εA * L.εB)
    -- (3) A-marginal deviation
    ∧ (∀ s : Sign,
        |(∑ t : Sign, branchWeight P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) s t) - 1/2|
          ≤ 2 * (L.εA + L.εB + L.εA * L.εB))
    -- (4) B-marginal deviation
    ∧ (∀ t : Sign,
        |(∑ s : Sign, branchWeight P (finalState M (cAmp ctx.a ctx.b) φA0 φB0) s t) - 1/2|
          ≤ 2 * (L.εA + L.εB + L.εA * L.εB)) :=
  ⟨fun s t => singlet_pointer_probability_finite_leakage P M φA0 φB0 ctx.a ctx.b L s t,
   correlation_finite_leakage_bound P M φA0 φB0 ctx.a ctx.b L,
   fun s => marginal_a_finite_leakage_bound P M φA0 φB0 ctx.a ctx.b L s,
   fun t => marginal_b_finite_leakage_bound P M φA0 φB0 ctx.a ctx.b L t⟩

/-! ### LF1 ↔ LF2 ↔ LF3 empirical chain (paper §9.13, spec §10.5)

The full empirical interpretation chain:

```
LF3 pointer-sector weight P_st(a, b)
  = (via projectiveWeight identity, hLF2 hypothesis)
  LF2 projective weight over outcome region O_{st}
  = (via LF2.Interface.lf1_weight_eq_projective_weight)
  LF1 pulled-back ontic weight μprep(D.π⁻¹ O_{st})
  = (via LF1.MainTheorem.LF1_main_theorem_ae)
  LF1 trial-frequency limit lim n→∞ (1/n) ∑ 𝟙_{O_{st}}(ω_k)
```

The `hLF2` hypothesis supplies the LF2/LF3 connection at the rank-1 singlet;
it is the composition of LF4-todo §2 (preparation ↔ Hilbert correspondence)
and LF4-todo §7 (projective-first outcomes) — see `specs/LF4-todo.md`. -/

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]

/-- **Pre-Born form of the empirical chain.** For each `(s, t)` pointer
    sector, the empirical frequency of `D.π ⁻¹' (prep.O_st s t)` over
    repeated trials converges almost surely to `P_{st}(a, b) = (1 − st a·b)/4`,
    given:
    - an LF2 sector structure `D` with projection `π`,
    - an LF1 trial model `T` over `D.toOntic`,
    - a `PureSingletPreparation D ctx` bundle supplying the projective
      outcome family, its ontic counterpart, the correspondence between
      them, and the LF2 → LF3 Born identity (this is the discharge
      target for LF4-todo §2 + §7; see `PurePreparation.lean`),
    - pairwise independence of the trial indicators on the
      `prep.O_region s t` family. -/
theorem LF3_singlet_frequency_convergence
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext)
    (prep : PureSingletPreparation D ctx)
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
  have h_proj := CSD.LF2.LF1_main_theorem_projective D T (prep.O_region s t)
    (hindep s t) (prep.O_st_measurable s t) (prep.correspondence s t)
  rw [prep.weight_eq_P_st s t] at h_proj
  rwa [ENNReal.toReal_ofReal (P_st_nonneg ctx.a ctx.b s t)] at h_proj

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
    (ctx : MeasurementContext)
    (prep : PureSingletPreparation D ctx)
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
    (ctx : MeasurementContext)
    (prep : PureSingletPreparation D ctx)
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

end LF3
end CSD
