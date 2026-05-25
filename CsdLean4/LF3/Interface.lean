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
import CsdLean4.LF1.GeneralFrequency
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
   `‖⟨prep.PP.ψ, prep.jed.eig s t⟩‖²` — the genuine Hilbert-space inner
   product between the bundle's pure-preparation vector and the bundle's
   joint spin eigenstate, via `prep.jed.born_eq_P_st`.
4. `LF3_main_theorem`: eight-conjunct strong-readout package (kernel,
   correlation, A-marginal, B-marginal, no-signalling on each side,
   pointer-completeness on each side).
5. `LF3_finite_leakage_theorem`: four-conjunct finite-leakage stability.

## Two-layer architecture: bundle (data) vs theorem (composition)

The chain capstones in this module follow a deliberate **bundle +
theorem** separation:

- **The `PureSingletPreparation D ctx N` bundle**
  (`LF3.PurePreparation`) carries the **load-bearing hypotheses**
  needed by the empirical chain: the posited fibre trial law `μψ`, the
  projective reference measure + measure bridge, the static pure
  preparation `PP` over `μψ` (with Dirac concentration), the joint spin
  eigenstate data `jed` (with the Born identity hypothesis
  `‖⟨PP.ψ, eig s t⟩‖² = P_st`), and the major hypothesis `bridge_op_p`
  (ontic outcome weight ↔ OP.p — the LF4-todo §2 + §7 discharge target).
  The bundle's fields are *data*: they encode what the caller must
  supply to apply the theorem.

- **The chain capstone theorems** (`LF3_singlet_frequency_convergence`,
  `_born`, `_born_inner`, plus the `_joint` variants) are *theorem
  compositions* on top of the bundle. They take i.i.d. trials
  `X : ℕ → Ω → Σ` with common law `μψ` (the posited fibre law) and
  compose the bundle's hypotheses with three external pieces:
  + `LF1.GeneralFrequency.freq_tendsto_of_iid` — the law-agnostic SLLN
    frequency limit (axiom-free; the posited-fibre replacement for
    `LF1_main_theorem_ae`, whose `μL`-conditional `prepMeasure` cannot
    model a fibre-concentrated pure preparation under the measure
    bridge);
  + `LF3.OP_p_at_jointEig_eq_P_st` — Busch-mediated rank-1 step
    (cites `busch_effect_gleason`);
  + `LF3.Singlet.Kernel.cst_squared_eq` — algebraic
    `P_st = ‖cAmp‖²` (axiom-free).
  The two further conceptual pieces named below
  (`sectorVolume_eq_LF2_Born`, `LF1_main_theorem_projective`) are
  what `prep.weight_eq_P_st` (and thereby `bridge_op_p`) packages
  for the theorem composition.

A fully discharged chain at LF4 would unfold the bundle into the
following composition:

- `Projectors.LF2Interface.sectorVolume_eq_LF2_Born` (LF3 → LF2 Born form)
- `LF2.Interface.LF1_main_theorem_projective` (LF2 → LF1 frequency limit)
- `LF1.GeneralFrequency.freq_tendsto_of_iid` (fibre-law a.s. convergence)
- `Singlet.Kernel.cst_squared_eq` (algebraic core, axiom-free)

Pre-LF4, the proof bodies below consume the bundle's
`weight_eq_P_st` theorem (which itself composes `bridge_op_p` with
`OP_p_at_jointEig_eq_P_st`); `sectorVolume_eq_LF2_Born` enters
through `weight_eq_P_st` once LF4 supplies the structural
constructor. The reader should track:

- *What's proven*: the theorem composition machinery, sorry-free.
- *What's assumed*: everything packed into `prep : PureSingletPreparation`.
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

/-- **PACKAGING-ONLY: zero new content.** Body is an anonymous-record
`⟨context_singlet_kernel, context_correlation_eq_neg_dot, context_marginal_a,
context_marginal_b, no_signalling_strong_readout_a, no_signalling_strong_readout_b,
pointer_a_complete, pointer_b_complete⟩` over eight separately-exported
theorems. The "main theorem" label is a labelled handle on existing
content; no proof obligation is discharged here that is not discharged
by the conjuncts individually. See `PLACEHOLDERS.md §9`.

**`LF3_main_theorem`** — eight-conjunct strong-readout package.

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

/-- **PACKAGING-ONLY: zero new content.** Body is an anonymous-record
over four separately-exported theorems
(`singlet_pointer_probability_finite_leakage`, `correlation_finite_leakage_bound`,
`marginal_a_finite_leakage_bound`, `marginal_b_finite_leakage_bound`).
The "theorem" label is a labelled handle on existing content. See
`PLACEHOLDERS.md §9`.

**`LF3_finite_leakage_theorem`** — four-conjunct finite-leakage stability.

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
  μψ((prep.O_region s t).preEvent)
  = (via LF1.GeneralFrequency.freq_tendsto_of_iid)
  fibre trial-frequency limit lim M→∞ (1/M) ∑ 𝟙_{O_{st}}(X i ω)
```

The chain bridge `prep.bridge_op_p` discharges the ontic outcome weight
under the **posited fibre law** `μψ` as
`ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))`, where the OP is
built from `μFS + bridge + μψ + PP.rep` via
`LF2.OperationalPackage.fromPreparation`. The `OP.p ↔ P_st` identity is
discharged by `LF3.OP_p_at_jointEig_eq_P_st` (cites `busch_effect_gleason`
via `LF2.pure_state_born_weights_of_certainty`). The frequency limit is
`LF1.freq_tendsto_of_iid` applied to i.i.d. trials `X : ℕ → Ω → Σ` with
common law `μψ` — **not** `LF1_main_theorem_ae`, whose `μL`-conditional
`prepMeasure` is incompatible with a fibre-concentrated pure preparation
under the continuous measure bridge (see `PurePreparation.lean` and
`LF4-todo §8`). LF4-todo §2 (preparation ↔ Hilbert correspondence) and §7
(projective-first outcomes) are the two LF4 work items behind the
`bridge_op_p` hypothesis. -/

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
    - a `PureSingletPreparation D ctx N` bundle (option (B)) supplying:
      the **posited fibre trial law** `μψ`, the projective reference
      measure `μFS` + measure bridge, the static pure preparation `PP`
      over `μψ` with rep + Dirac concentration, the joint spin eigenstate
      data `jed` for `ctx` (with the Born identity
      `‖⟨PP.ψ, eig s t⟩‖² = P_st`), the ontic outcome regions, and the
      bridge `μψ((O_region s t).preEvent) = OP.p ↔ rank-1 sector
      effect` (LF4 discharge target),
    - i.i.d. trials `X : ℕ → Ω → Σ` over a probability space `Pr` whose
      common law is the fibre law `μψ` (`hlaw`),
    - pairwise independence of the trial indicators on the
      `(prep.O_region s t).preEvent` family. -/
theorem LF3_singlet_frequency_convergence
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
       Tendsto
         (fun M : ℕ =>
           (∑ i ∈ Finset.range M,
               Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
             / (M : ℝ))
         atTop
         (nhds (P_st ctx.a ctx.b s t)) := by
  intro s t
  have hfreq :=
    LF1.freq_tendsto_of_iid hX hlaw (prep.O_region s t).measurable_preEvent (hindep s t)
  rwa [prep.weight_eq_P_st s t, ENNReal.toReal_ofReal (P_st_nonneg ctx.a ctx.b s t)] at hfreq

/-- **Born-mediated form of the empirical chain (closed-form amplitude).**
    Identifies the pre-Born target `P_{st}(a, b)` with the squared
    closed-form singlet amplitude `‖cAmp s t (a, b)‖²` via `cst_squared_eq`.
    `cAmp` is the real-valued representative `√P_st`; the bra-ket form
    `‖⟨v, ψ⁻⟩‖²` is recovered by `LF3_singlet_frequency_convergence_born_inner`
    below, given an actual joint spin eigenstate `v`. -/
theorem LF3_singlet_frequency_convergence_born
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
       Tendsto
         (fun M : ℕ =>
           (∑ i ∈ Finset.range M,
               Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
             / (M : ℝ))
         atTop
         (nhds (‖cAmp ctx.a ctx.b s t‖ ^ 2)) := by
  intro s t
  have h_pre := LF3_singlet_frequency_convergence D ctx prep hX hlaw hindep s t
  rw [← cst_squared_eq ctx.a ctx.b s t] at h_pre
  exact h_pre

/-- **HYPOTHESIS-DOES-THE-WORK: rewrites the pre-Born conclusion via
the bundle field `prep.jed.born_eq_P_st`**, which IS the Born identity
for the joint spin eigenstate. The conclusion `Tendsto … (‖⟨ψ, eig s t⟩‖²)`
is equivalent to the pre-Born conclusion under this bundled identity.
The Born identity is the entire content of the rewrite. See
`PLACEHOLDERS.md §10`. The bundle field is catalogued at
`BRIDGE-OBLIGATIONS.md §2.1` (LF4-todo §2 + §7).

**Born-form empirical chain with a genuine bra-ket amplitude.** The
    empirical frequency converges to `‖⟨ψ, eig s t⟩‖²` where `eig s t` is
    the joint spin eigenstate `|s_a, t_b⟩` supplied by the bundle's
    `prep.jed`, and `ψ = prep.PP.ψ` is the pure-preparation Hilbert vector.
    The Born identity `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t` is the
    bundled field `prep.jed.born_eq_P_st` (the LF4-todo §2 + §7 discharge
    target carried as a structural hypothesis pre-LF4).

    This is the **physically faithful** form of the LF1↔LF2↔LF3 chain: the
    RHS is a genuine Hilbert-space inner product between the bundle's
    pure-preparation vector and the bundle's joint spin eigenstate, not a
    closed-form repackaging and not an unbound caller-supplied vector. -/
theorem LF3_singlet_frequency_convergence_born_inner
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
       Tendsto
         (fun M : ℕ =>
           (∑ i ∈ Finset.range M,
               Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
             / (M : ℝ))
         atTop
         (nhds (‖inner ℂ prep.PP.ψ (prep.jed.eig s t)‖ ^ 2)) := by
  intro s t
  have h_pre := LF3_singlet_frequency_convergence D ctx prep hX hlaw hindep s t
  rw [← prep.jed.born_eq_P_st s t] at h_pre
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
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
       ∀ s t,
         Tendsto
           (fun M : ℕ =>
             (∑ i ∈ Finset.range M,
                 Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
               / (M : ℝ))
           atTop
           (nhds (P_st ctx.a ctx.b s t)) := by
  rw [MeasureTheory.ae_all_iff]
  intro s
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact LF3_singlet_frequency_convergence D ctx prep hX hlaw hindep s t

/-- **Joint partition convergence (Born form, closed-form amplitude).**
    Almost surely, for every `(s, t)` the empirical frequency converges
    to `‖cAmp ctx.a ctx.b s t‖²`. Joint version of
    `LF3_singlet_frequency_convergence_born`. -/
theorem LF3_singlet_frequency_convergence_born_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
       ∀ s t,
         Tendsto
           (fun M : ℕ =>
             (∑ i ∈ Finset.range M,
                 Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
               / (M : ℝ))
           atTop
           (nhds (‖cAmp ctx.a ctx.b s t‖ ^ 2)) := by
  rw [MeasureTheory.ae_all_iff]
  intro s
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact LF3_singlet_frequency_convergence_born D ctx prep hX hlaw hindep s t

/-- **Joint partition convergence (Born form, bra-ket amplitude).**
    Almost surely, for every `(s, t)` the empirical frequency converges
    to `‖⟨prep.PP.ψ, prep.jed.eig s t⟩‖²`. Joint version of
    `LF3_singlet_frequency_convergence_born_inner`. -/
theorem LF3_singlet_frequency_convergence_born_inner_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) {N : ℕ}
    (prep : PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
       ∀ s t,
         Tendsto
           (fun M : ℕ =>
             (∑ i ∈ Finset.range M,
                 Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
               / (M : ℝ))
           atTop
           (nhds (‖inner ℂ prep.PP.ψ (prep.jed.eig s t)‖ ^ 2)) := by
  rw [MeasureTheory.ae_all_iff]
  intro s
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact LF3_singlet_frequency_convergence_born_inner D ctx prep hX hlaw hindep s t

end LF3
end CSD
