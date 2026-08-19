/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.SharedContextMap
public import CsdLean4.LF3.OperationalNoSignalling
public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.LF4.SingletKahler
public import CsdLean4.RecordLayer.CircleFibre

/-!
# LF6/C1BellConsistency: no compatible global CHSH assignment

**Category:** 6-Entanglement (the C1 four-answer obstruction).

**Glossary:** https://glossary.constraintsurfacedynamics.com/contextuality/
Plain-language, CSD-role and formal statements of contextuality, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

**Glossary:** https://glossary.constraintsurfacedynamics.com/bell-chsh/
Plain-language, CSD-role and formal statements of Bell and CHSH, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

`LF3/ContextMap.lean` used to claim that `ContextIndexedOutcomeMaps` and
`GlobalCHSHAssignment` "being different types carries the Bell-consistency
content". **That is false**: different structures establish only definitional
separation. This module supplies the actual obstruction, on the shared state
space `SigmaSpace` that C1 posits.

* `CompatibleWithGlobalCHSH` — at each of the four CHSH contexts, the joint
  outcome's components *are* the global assignment's setting-local responses.
* ★★ `no_compatible_global_chsh_assignment_realises_singlet` — no measurable
  shared-context outcome family compatible with any global assignment
  reproduces the singlet correlations at the four CHSH settings.
* `compatibleGlobalCHSH_nonvacuous` — the predicate is inhabited, so the no-go
  is a **separation** and not an artefact of an unsatisfiable hypothesis. This
  mirrors `productPartition_nonvacuous`, which exists for the same reason.

## The positive half (added 2026-08-13, Q19)

The obstruction above was, until Q19, conditional in its reproduction slot:
nothing inhabited `ReproducesSingletAtCHSH`. This module now also builds the
**explicit contextual model** on the concrete singlet arena `(KSigma 4, kMuPsi)`
— for each context, the first torus coordinate is read through the four
cumulative arcs (`RecordLayer.circleCell`) whose lengths are the context's own
singlet weights `P_st` — and proves:

* `ReproducesSingletTableAt` — the **full-table** reproduction predicate: every
  joint outcome's probability is `P_st`. Strictly stronger than the
  correlation-level `ReproducesSingletAtCHSH` (a family can match the four
  correlations with degenerate marginals; the table cannot), and the model is
  proved against the table **at every context**, not only the four.
* ★ `singletContextualModel_table` / `singletContextualModel_reproduces` — the
  model reproduces the table (hence marginals `1/2` and correlations `−a·b`),
  and `ReproducesSingletAtCHSH` follows via `integral_wing_mul_of_table`.
* ★★ `c1_singlet_contextual_capstone` — **existence and obstruction in one
  statement**: there IS a measurable shared-context family reproducing the
  singlet (table and correlations), and NO global CHSH assignment is compatible
  with it. Contextual models can do what non-contextual ones provably cannot —
  the C1 separation with both halves witnessed.

## What is and is not assumed

Measurability is assumed **only** of the object C1 posits, the shared-context
outcome family `F`. The four setting-local responses of the global assignment
are *derived* measurable from that plus compatibility, via
`SharedContextOutcomeMaps.measurable_wingA/B`. Nothing here assumes the global
assignment is measurable.

Only the **four CHSH settings** are constrained. The theorem does not require
the singlet to be reproduced at every detector setting, so it is strictly weaker
in hypothesis than `no_product_partition_realises_singlet` and does not subsume
it.

## References

`LF3/SharedContextMap.lean`; `LF3/ContextMap.lean` (`GlobalCHSHAssignment`);
`LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`);
`Empirical/QM/Crypto/E91.lean` (`lhvCHSH_abs_le_two`);
`specs/c1-correction-plan.md` §3 D1, D2.
-/

@[expose] public section

open MeasureTheory
open CSD.LF3

namespace CSD.LF6

open CSD.Empirical.QM.E91 CSD.Empirical.Bell

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace]

/-- The A-wing setting selected by `i : Fin 2` in the CHSH quadruple. -/
noncomputable def chshSettingA (i : Fin 2) : DetectorSetting :=
  if i = 0 then chshA else chshA'

/-- The B-wing setting selected by `j : Fin 2` in the CHSH quadruple. -/
noncomputable def chshSettingB (j : Fin 2) : DetectorSetting :=
  if j = 0 then chshB else chshB'

/-- The four CHSH measurement contexts. -/
noncomputable def chshContext (i j : Fin 2) : MeasurementContext :=
  ⟨chshSettingA i, chshSettingB j⟩

/-- The global assignment's A-wing response at index `i`. -/
def globalA (G : GlobalCHSHAssignment SigmaSpace) (i : Fin 2) (l : SigmaSpace) : Sign :=
  if i = 0 then G.A1 l else G.A2 l

/-- The global assignment's B-wing response at index `j`. -/
def globalB (G : GlobalCHSHAssignment SigmaSpace) (j : Fin 2) (l : SigmaSpace) : Sign :=
  if j = 0 then G.B1 l else G.B2 l

/-- **Compatibility.** At each of the four CHSH contexts the shared-context
outcome map's components are exactly the global assignment's setting-local
responses. This is compatibility of the local *components*, not merely the
existence of some map carrying four context-labelled results. -/
def CompatibleWithGlobalCHSH (S : SharedContextOutcomeMaps SigmaSpace)
    (G : GlobalCHSHAssignment SigmaSpace) : Prop :=
  ∀ (i j : Fin 2) (l : SigmaSpace), S.F (chshContext i j) l = (globalA G i l, globalB G j l)

/-- **Reproducing the singlet at the four CHSH contexts.** -/
noncomputable def ReproducesSingletAtCHSH (μ : Measure SigmaSpace)
    (S : SharedContextOutcomeMaps SigmaSpace) : Prop :=
  ∀ i j : Fin 2,
    ∫ l, ((S.wingA (chshContext i j) l).val : ℝ) * ((S.wingB (chshContext i j) l).val : ℝ) ∂μ
      = correlation (chshSettingA i) (chshSettingB j)

/-- **Reproducing the full singlet table at a context**: every joint outcome carries exactly
its singlet weight `P_st`. Strictly stronger than matching the correlation — a family can
match `∑ st·P` with degenerate marginals, but the table pins the marginals at `1/2` too.
This is the predicate the positive model is proved against, at every context. -/
noncomputable def ReproducesSingletTableAt (μ : Measure SigmaSpace) (S : SharedContextOutcomeMaps SigmaSpace)
    (C : MeasurementContext) : Prop :=
  ∀ s t : Sign, μ {l | S.F C l = (s, t)} = ENNReal.ofReal (P_st C.a C.b s t)

/-- **From the table to the correlation.** Any measurable family reproducing the full table
at a context has wing-product expectation equal to the singlet correlation there — the
outcome partition decomposes the product into four indicator terms whose masses are the
table entries, and `correlation` *is* that weighted sum by definition. -/
theorem integral_wing_mul_of_table (μ : Measure SigmaSpace) [IsProbabilityMeasure μ]
    (S : SharedContextOutcomeMaps SigmaSpace) (C : MeasurementContext)
    (hS : Measurable (S.F C))
    (htab : ReproducesSingletTableAt μ S C) :
    ∫ l, ((S.wingA C l).val : ℝ) * ((S.wingB C l).val : ℝ) ∂μ
      = correlation C.a C.b := by
  have hmeas : ∀ p : Sign × Sign, MeasurableSet {l | S.F C l = p} := by
    intro p
    have hset : {l | S.F C l = p} = S.F C ⁻¹' ({p.1} ×ˢ {p.2}) := by
      ext l
      simp [Prod.ext_iff]
    have h1 : MeasurableSet ({p.1} : Set Sign) := trivial
    have h2 : MeasurableSet ({p.2} : Set Sign) := trivial
    rw [hset]
    exact hS (h1.prod h2)
  have hint : ∀ p ∈ (Finset.univ : Finset (Sign × Sign)),
      Integrable (fun l =>
        (p.1.val * p.2.val) * Set.indicator {l' | S.F C l' = p} (fun _ => (1 : ℝ)) l) μ := by
    intro p _
    apply Integrable.const_mul
    exact (integrable_const (1 : ℝ)).indicator (hmeas p)
  have hfun : (fun l => ((S.wingA C l).val : ℝ) * ((S.wingB C l).val : ℝ))
      = fun l => ∑ p : Sign × Sign,
          (p.1.val * p.2.val) * Set.indicator {l' | S.F C l' = p} (fun _ => (1 : ℝ)) l := by
    funext l
    rw [Finset.sum_eq_single (S.F C l)
      (fun p _ hp => by
        have hnot : l ∉ {l' | S.F C l' = p} :=
          fun h => hp (Eq.symm (show S.F C l = p from h))
        rw [Set.indicator_of_notMem hnot]
        ring)
      (fun h => absurd (Finset.mem_univ _) h),
      Set.indicator_of_mem (show l ∈ {l' | S.F C l' = S.F C l} from rfl)]
    simp [SharedContextOutcomeMaps.wingA, SharedContextOutcomeMaps.wingB]
  rw [hfun, MeasureTheory.integral_finsetSum _ hint]
  have hterm : ∀ p : Sign × Sign,
      (∫ l, (p.1.val * p.2.val)
          * Set.indicator {l' | S.F C l' = p} (fun _ => (1 : ℝ)) l ∂μ)
        = p.1.val * p.2.val * P_st C.a C.b p.1 p.2 := by
    rintro ⟨s, t⟩
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator_const _ (hmeas (s, t)),
      smul_eq_mul, mul_one, measureReal_def, htab s t,
      ENNReal.toReal_ofReal (P_st_nonneg _ _ _ _)]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rfl

/-! ### The obstruction -/

omit [MeasurableSpace SigmaSpace] in
/-- Compatibility identifies the A-wing component with the global response. -/
lemma wingA_eq_globalA {S : SharedContextOutcomeMaps SigmaSpace} {G : GlobalCHSHAssignment SigmaSpace}
    (hcomp : CompatibleWithGlobalCHSH S G) (i j : Fin 2) (l : SigmaSpace) :
    S.wingA (chshContext i j) l = globalA G i l := by
  rw [SharedContextOutcomeMaps.wingA, hcomp i j l]

omit [MeasurableSpace SigmaSpace] in
/-- Compatibility identifies the B-wing component with the global response. -/
lemma wingB_eq_globalB {S : SharedContextOutcomeMaps SigmaSpace} {G : GlobalCHSHAssignment SigmaSpace}
    (hcomp : CompatibleWithGlobalCHSH S G) (i j : Fin 2) (l : SigmaSpace) :
    S.wingB (chshContext i j) l = globalB G j l := by
  rw [SharedContextOutcomeMaps.wingB, hcomp i j l]

/-- ★★ **The C1 four-answer obstruction.**

No measurable shared-context outcome family compatible with any global CHSH
assignment reproduces the singlet correlations at the four CHSH settings.

Measurability is assumed only of `S` — the object C1 posits — and the four
setting-local responses are derived from it.

**Notation bridge.** The binder `SigmaSpace` is named for the intended CSD
instantiation (the ontic surface `Σ`; the capstone below instantiates it at
`KSigma 4`), but mathematically it is **Bell's `Λ`** — an *arbitrary* measurable
space with a probability measure. Nothing in the hypotheses restricts to CSD's
substrate; the theorem transfers to any theory of this shape, which is exactly
its force (`necessity-audit.md`). The QM-side LHV bound it reduces to
(`lhvCHSH_abs_le_two`, `E91.lean`) keeps Bell's `Λ` for the same reason in the
other direction: it is literature-facing. -/
theorem no_compatible_global_chsh_assignment_realises_singlet
    (μ : Measure SigmaSpace) [IsProbabilityMeasure μ]
    (S : SharedContextOutcomeMaps SigmaSpace) (G : GlobalCHSHAssignment SigmaSpace)
    (hS : MeasurableSharedContextOutcomeMaps S)
    (hcomp : CompatibleWithGlobalCHSH S G)
    (hrep : ReproducesSingletAtCHSH μ S) :
    False := by
  refine absurd (lhvCHSH_abs_le_two (Λ := SigmaSpace) (SettingA := Fin 2) (SettingB := Fin 2) μ
    (fun i l => ((globalA G i l).val : ℝ)) (fun j l => ((globalB G j l).val : ℝ))
    ?_ ?_ ?_ ?_ 0 1 0 1) ?_
  · -- A-wing measurability, DERIVED from `hS` and compatibility
    intro i
    have h := S.measurable_wingA_val hS (chshContext i 0)
    have he : (fun l => ((S.wingA (chshContext i 0) l).val : ℝ))
        = fun l => ((globalA G i l).val : ℝ) := by
      funext l; rw [wingA_eq_globalA hcomp i 0 l]
    rwa [he] at h
  · -- B-wing measurability, DERIVED
    intro j
    have h := S.measurable_wingB_val hS (chshContext 0 j)
    have he : (fun l => ((S.wingB (chshContext 0 j) l).val : ℝ))
        = fun l => ((globalB G j l).val : ℝ) := by
      funext l; rw [wingB_eq_globalB hcomp 0 j l]
    rwa [he] at h
  · exact fun i l => sign_val_eq_one_or _
  · exact fun j l => sign_val_eq_one_or _
  · -- the CHSH combination is the singlet's, which exceeds the LHV cap
    have hcorr : ∀ i j : Fin 2,
        lhvCorrelation μ (fun i l => ((globalA G i l).val : ℝ))
          (fun j l => ((globalB G j l).val : ℝ)) i j
          = correlation (chshSettingA i) (chshSettingB j) := by
      intro i j
      rw [← hrep i j]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun l => ?_))
      simp only [wingA_eq_globalA hcomp, wingB_eq_globalB hcomp]
    have hval : lhvCHSH μ (fun i l => ((globalA G i l).val : ℝ))
        (fun j l => ((globalB G j l).val : ℝ)) 0 1 0 1
        = chshOperator chshA chshA' chshB chshB' := by
      unfold lhvCHSH chshOperator
      rw [hcorr 0 0, hcorr 0 1, hcorr 1 0, hcorr 1 1]
      simp only [chshSettingA, chshSettingB]
      norm_num
    rw [hval, chsh_singlet_at_optimal_angles]
    have hpos : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
    rw [abs_neg, abs_of_pos hpos]
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      have h := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)
      rwa [Real.sqrt_one] at h
    intro hle
    linarith

/-! ### Non-vacuity -/

/-- **Non-vacuity of the obstruction.** Compatible measurable shared-context
families *exist* and reproduce *some* correlation — just not the singlet's. The
all-`plus` family is compatible with the all-`plus` global assignment and has
constant correlation `1`; the singlet correlation `−a·b` is non-constant, so it
does not reproduce the singlet.

So `no_compatible_global_chsh_assignment_realises_singlet` is a genuine
**separation** and not an artefact of an unsatisfiable predicate. This mirrors
`productPartition_nonvacuous`, which exists for exactly the same reason. -/
theorem compatibleGlobalCHSH_nonvacuous (μ : Measure SigmaSpace) [IsProbabilityMeasure μ] :
    ∃ (S : SharedContextOutcomeMaps SigmaSpace) (G : GlobalCHSHAssignment SigmaSpace),
      MeasurableSharedContextOutcomeMaps S ∧ CompatibleWithGlobalCHSH S G ∧
      ∀ i j : Fin 2,
        ∫ l, ((S.wingA (chshContext i j) l).val : ℝ)
            * ((S.wingB (chshContext i j) l).val : ℝ) ∂μ = 1 := by
  refine ⟨⟨fun _ _ => (Sign.plus, Sign.plus)⟩,
    ⟨fun _ => Sign.plus, fun _ => Sign.plus, fun _ => Sign.plus, fun _ => Sign.plus⟩,
    fun _ => measurable_const, ?_, ?_⟩
  · intro i j l
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    show ∫ _ : SigmaSpace, ((Sign.plus.val : ℝ) * (Sign.plus.val : ℝ)) ∂μ = 1
    simp [Sign.val]

/-! ### The positive half: the explicit contextual model on `(KSigma 4, kMuPsi)` -/

section SingletModel

open CSD.RecordLayer CSD.LF4 Set

/-- The four joint outcomes, enumerated in a fixed order. -/
def signPair : Fin 4 → Sign × Sign
  | 0 => (Sign.plus, Sign.plus)
  | 1 => (Sign.plus, Sign.minus)
  | 2 => (Sign.minus, Sign.plus)
  | 3 => (Sign.minus, Sign.minus)

/-- The inverse enumeration. -/
def pairIndex : Sign × Sign → Fin 4
  | (Sign.plus, Sign.plus) => 0
  | (Sign.plus, Sign.minus) => 1
  | (Sign.minus, Sign.plus) => 2
  | (Sign.minus, Sign.minus) => 3

@[simp] lemma signPair_pairIndex (p : Sign × Sign) : signPair (pairIndex p) = p := by
  rcases p with ⟨s, t⟩
  cases s <;> cases t <;> rfl

/-- The four singlet weights of a context, in `signPair` order. -/
noncomputable def pstWeights (C : MeasurementContext) : Fin 4 → ℝ :=
  fun k => P_st C.a C.b (signPair k).1 (signPair k).2

lemma pstWeights_nonneg (C : MeasurementContext) (k : Fin 4) : 0 ≤ pstWeights C k :=
  P_st_nonneg C.a C.b _ _

/-- The four singlet weights sum to `1`. -/
lemma sum_pstWeights (C : MeasurementContext) : ∑ k, pstWeights C k = 1 := by
  rw [Fin.sum_univ_four]
  show P_st C.a C.b Sign.plus Sign.plus + P_st C.a C.b Sign.plus Sign.minus
      + P_st C.a C.b Sign.minus Sign.plus + P_st C.a C.b Sign.minus Sign.minus = 1
  unfold P_st
  simp only [Sign.val_plus, Sign.val_minus]
  ring

/-- Each cumulative cell fits inside one turn of the circle. -/
lemma loSum_pstWeights_add_le_one (C : MeasurementContext) (k : Fin 4) :
    loSum (pstWeights C) k + pstWeights C k ≤ 1 := by
  have hnotmem : k ∉ Finset.univ.filter (fun j : Fin 4 => (j : ℕ) < (k : ℕ)) := by simp
  have hle : ∑ j ∈ insert k (Finset.univ.filter (fun j : Fin 4 => (j : ℕ) < (k : ℕ))),
      pstWeights C j ≤ ∑ j, pstWeights C j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => pstWeights_nonneg C j)
  rw [Finset.sum_insert hnotmem, sum_pstWeights] at hle
  rw [loSum]
  linarith

/-- The context's outcome-`k` cell on the arena: the first torus coordinate lies in the
`k`-th cumulative arc (`RecordLayer.circleCell`) of the context's own singlet weights. -/
noncomputable def singletCell (C : MeasurementContext) (k : Fin 4) : Set (KSigma 4) :=
  (fun l : KSigma 4 => l.2.1) ⁻¹' circleCell (pstWeights C) k

lemma measurableSet_singletCell (C : MeasurementContext) (k : Fin 4) :
    MeasurableSet (singletCell C k) :=
  (measurable_fst.comp measurable_snd) (measurableSet_circleCell _ _)

lemma singletCell_disjoint (C : MeasurementContext) {k j : Fin 4} (h : k ≠ j) :
    Disjoint (singletCell C k) (singletCell C j) :=
  Disjoint.preimage _ (circleCell_pairwiseDisjoint (pstWeights C) (pstWeights_nonneg C) h)

/-- **The arena measure of an outcome cell is exactly its singlet weight.** The base is a
Dirac (mass `1` on the whole base), the second torus coordinate is free (mass `1`), and
the first-coordinate arc carries `volume_circleCell`'s value. -/
lemma kMuPsi_singletCell (C : MeasurementContext) (k : Fin 4) :
    kMuPsi (singletCell C k) = ENNReal.ofReal (pstWeights C k) := by
  have hprod : singletCell C k
      = (univ : Set (CPN 4))
        ×ˢ (circleCell (pstWeights C) k ×ˢ (univ : Set (AddCircle (1 : ℝ)))) := by
    ext ⟨p, θ₁, θ₂⟩
    simp [singletCell, Set.mem_prod]
  have hk : kMuPsi = (Measure.dirac singletRay).prod (volume : Measure KTorus) := rfl
  have hvol : (volume : Measure KTorus)
      = ((volume : Measure (AddCircle (1 : ℝ)))).prod (volume : Measure (AddCircle (1 : ℝ))) :=
    Measure.volume_eq_prod (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ))
  rw [hprod, hk, Measure.prod_prod, hvol, Measure.prod_prod,
    volume_circleCell (pstWeights C) (pstWeights_nonneg C) (loSum_pstWeights_add_le_one C) k]
  simp

open scoped Classical in
/-- **The explicit contextual singlet model.** For each context, the shared ontic state's
first torus coordinate is read through the four cumulative arcs of the context's own
singlet weights; the outcome is the arc's joint sign pair. Contextual by construction —
different contexts carve different arcs — which is exactly what the capstone shows a
globally CHSH-compatible family cannot be. -/
noncomputable def singletContextualF (C : MeasurementContext) (l : KSigma 4) : Sign × Sign :=
  if l ∈ singletCell C 0 then signPair 0
  else if l ∈ singletCell C 1 then signPair 1
  else if l ∈ singletCell C 2 then signPair 2
  else signPair 3

/-- The model, packaged as a shared-context outcome family. -/
noncomputable def singletContextualModel : SharedContextOutcomeMaps (KSigma 4) :=
  ⟨singletContextualF⟩

/-- The model is measurable at every context. -/
theorem singletContextualModel_measurable :
    MeasurableSharedContextOutcomeMaps singletContextualModel := by
  intro C
  show Measurable (singletContextualF C)
  unfold singletContextualF
  refine Measurable.ite (measurableSet_singletCell C 0) measurable_const ?_
  refine Measurable.ite (measurableSet_singletCell C 1) measurable_const ?_
  exact Measurable.ite (measurableSet_singletCell C 2) measurable_const measurable_const

lemma level_zero (C : MeasurementContext) :
    {l | singletContextualModel.F C l = signPair 0} = singletCell C 0 := by
  ext l
  show singletContextualF C l = signPair 0 ↔ l ∈ singletCell C 0
  unfold singletContextualF
  split_ifs with h0 h1 h2
  · exact iff_of_true rfl h0
  · exact iff_of_false (by decide) h0
  · exact iff_of_false (by decide) h0
  · exact iff_of_false (by decide) h0

lemma level_one (C : MeasurementContext) :
    {l | singletContextualModel.F C l = signPair 1} = singletCell C 1 := by
  ext l
  show singletContextualF C l = signPair 1 ↔ l ∈ singletCell C 1
  unfold singletContextualF
  split_ifs with h0 h1 h2
  · exact iff_of_false (by decide)
      (Set.disjoint_left.mp (singletCell_disjoint C (by decide : (0 : Fin 4) ≠ 1)) h0)
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

lemma level_two (C : MeasurementContext) :
    {l | singletContextualModel.F C l = signPair 2} = singletCell C 2 := by
  ext l
  show singletContextualF C l = signPair 2 ↔ l ∈ singletCell C 2
  unfold singletContextualF
  split_ifs with h0 h1 h2
  · exact iff_of_false (by decide)
      (Set.disjoint_left.mp (singletCell_disjoint C (by decide : (0 : Fin 4) ≠ 2)) h0)
  · exact iff_of_false (by decide)
      (Set.disjoint_left.mp (singletCell_disjoint C (by decide : (1 : Fin 4) ≠ 2)) h1)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

lemma level_three (C : MeasurementContext) :
    {l | singletContextualModel.F C l = signPair 3}
      = (singletCell C 0 ∪ singletCell C 1 ∪ singletCell C 2)ᶜ := by
  ext l
  show singletContextualF C l = signPair 3
      ↔ l ∈ (singletCell C 0 ∪ singletCell C 1 ∪ singletCell C 2)ᶜ
  unfold singletContextualF
  split_ifs with h0 h1 h2
  · exact iff_of_false (by decide)
      (fun hmem => hmem (Set.mem_union_left _ (Set.mem_union_left _ h0)))
  · exact iff_of_false (by decide)
      (fun hmem => hmem (Set.mem_union_left _ (Set.mem_union_right _ h1)))
  · exact iff_of_false (by decide) (fun hmem => hmem (Set.mem_union_right _ h2))
  · exact iff_of_true rfl (by simp [h0, h1, h2])

/-- The complement of the first three cells carries the fourth weight. -/
lemma kMuPsi_singletCell_compl (C : MeasurementContext) :
    kMuPsi (singletCell C 0 ∪ singletCell C 1 ∪ singletCell C 2)ᶜ
      = ENNReal.ofReal (pstWeights C 3) := by
  have hm0 := measurableSet_singletCell C 0
  have hm1 := measurableSet_singletCell C 1
  have hm2 := measurableSet_singletCell C 2
  have hunion : kMuPsi (singletCell C 0 ∪ singletCell C 1 ∪ singletCell C 2)
      = ENNReal.ofReal (pstWeights C 0) + ENNReal.ofReal (pstWeights C 1)
        + ENNReal.ofReal (pstWeights C 2) := by
    rw [measure_union ((singletCell_disjoint C (by decide : (0 : Fin 4) ≠ 2)).union_left
      (singletCell_disjoint C (by decide : (1 : Fin 4) ≠ 2))) hm2,
      measure_union (singletCell_disjoint C (by decide : (0 : Fin 4) ≠ 1)) hm1,
      kMuPsi_singletCell, kMuPsi_singletCell, kMuPsi_singletCell]
  rw [measure_compl ((hm0.union hm1).union hm2) (measure_ne_top _ _), measure_univ, hunion,
    ← ENNReal.ofReal_add (pstWeights_nonneg C 0) (pstWeights_nonneg C 1),
    ← ENNReal.ofReal_add (add_nonneg (pstWeights_nonneg C 0) (pstWeights_nonneg C 1))
      (pstWeights_nonneg C 2)]
  have hsum := sum_pstWeights C
  rw [Fin.sum_univ_four] at hsum
  have h1 : (1 : ENNReal)
      = ENNReal.ofReal (pstWeights C 0 + pstWeights C 1 + pstWeights C 2)
        + ENNReal.ofReal (pstWeights C 3) := by
    rw [← ENNReal.ofReal_add (add_nonneg (add_nonneg (pstWeights_nonneg C 0)
        (pstWeights_nonneg C 1)) (pstWeights_nonneg C 2)) (pstWeights_nonneg C 3),
      show pstWeights C 0 + pstWeights C 1 + pstWeights C 2 + pstWeights C 3 = 1 from hsum]
    simp
  rw [h1, ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]

/-- ★ **The model reproduces the full singlet table — at every context.** Each joint
outcome's arena probability is exactly its singlet weight `P_st`, so the marginals are
`1/2` and the correlations are `−a·b`. Stated at every context, not only the four CHSH
ones. -/
theorem singletContextualModel_table (C : MeasurementContext) :
    ReproducesSingletTableAt kMuPsi singletContextualModel C := by
  intro s t
  cases s <;> cases t
  · rw [show ((Sign.plus, Sign.plus) : Sign × Sign) = signPair 0 from by decide,
      level_zero, kMuPsi_singletCell]
    rfl
  · rw [show ((Sign.plus, Sign.minus) : Sign × Sign) = signPair 1 from by decide,
      level_one, kMuPsi_singletCell]
    rfl
  · rw [show ((Sign.minus, Sign.plus) : Sign × Sign) = signPair 2 from by decide,
      level_two, kMuPsi_singletCell]
    rfl
  · rw [show ((Sign.minus, Sign.minus) : Sign × Sign) = signPair 3 from by decide,
      level_three, kMuPsi_singletCell_compl]
    rfl

/-- ★ **The model reproduces the singlet correlations at the four CHSH contexts.** The
inhabitant `ReproducesSingletAtCHSH` was missing until Q19 — the obstruction's
reproduction slot is now witnessed, not merely hypothesised. -/
theorem singletContextualModel_reproduces :
    ReproducesSingletAtCHSH kMuPsi singletContextualModel := by
  unfold ReproducesSingletAtCHSH
  intro i j
  exact integral_wing_mul_of_table kMuPsi singletContextualModel (chshContext i j)
    (singletContextualModel_measurable _) (singletContextualModel_table (chshContext i j))

/-- ★★ **The C1 contextual capstone: existence and obstruction in one statement.** On the
concrete singlet arena `(KSigma 4, kMuPsi)` there IS a measurable shared-context outcome
family that reproduces the singlet — the full `P_st` table at every context, hence the
CHSH correlations — and NO global CHSH assignment is compatible with it. Contextual
models do what non-contextual ones provably cannot; both halves are now witnessed, so the
C1 separation is not conditional on an unproven reproduction hypothesis.

Scope unchanged from the obstruction: only the four CHSH settings are constrained by the
incompatibility half (the table half holds at every context), and this does not subsume
`no_product_partition_realises_singlet`. -/
theorem c1_singlet_contextual_capstone :
    ∃ S : SharedContextOutcomeMaps (KSigma 4),
      MeasurableSharedContextOutcomeMaps S ∧
      (∀ C, ReproducesSingletTableAt kMuPsi S C) ∧
      ReproducesSingletAtCHSH kMuPsi S ∧
      ∀ G : GlobalCHSHAssignment (KSigma 4), ¬ CompatibleWithGlobalCHSH S G := by
  refine ⟨singletContextualModel, singletContextualModel_measurable,
    singletContextualModel_table, singletContextualModel_reproduces, fun G hcomp => ?_⟩
  exact no_compatible_global_chsh_assignment_realises_singlet kMuPsi singletContextualModel G
    singletContextualModel_measurable hcomp singletContextualModel_reproduces

/-! ### The operational no-signalling predicate, inhabited

`LF3/OperationalNoSignalling.lean` defines `OperationalNoSignalling μ S` of an
outcome family and a measure, but until now nothing inhabited it: the only
theorems in that module (`singlet_operational_no_signalling`,
`singlet_marginals_eq_half`) are finite-sum identities over the closed-form
kernel `P_st`, with no measure and no outcome map in sight. C1 §4 states its
marginals as `μ(F⁻¹{(s,t)})`, so the kernel lemmas were standing in for a claim
about a different object — the same substitution Q19 removed from the
reproduction slot. With the full table in hand the repair is a corollary. -/

omit [MeasurableSpace SigmaSpace] in
/-- The A-wing fibre is the union of the two joint fibres above it. -/
lemma wingA_fibre_eq (S : SharedContextOutcomeMaps SigmaSpace) (C : MeasurementContext) (s : Sign) :
    {l | S.wingA C l = s}
      = {l | S.F C l = (s, Sign.plus)} ∪ {l | S.F C l = (s, Sign.minus)} := by
  ext l
  show S.wingA C l = s ↔ _
  rw [SharedContextOutcomeMaps.wingA]
  rcases hF : S.F C l with ⟨s', t'⟩
  cases t' <;> simp [Set.mem_union, hF]

omit [MeasurableSpace SigmaSpace] in
/-- The B-wing fibre, symmetrically. -/
lemma wingB_fibre_eq (S : SharedContextOutcomeMaps SigmaSpace) (C : MeasurementContext) (t : Sign) :
    {l | S.wingB C l = t}
      = {l | S.F C l = (Sign.plus, t)} ∪ {l | S.F C l = (Sign.minus, t)} := by
  ext l
  show S.wingB C l = t ↔ _
  rw [SharedContextOutcomeMaps.wingB]
  rcases hF : S.F C l with ⟨s', t'⟩
  cases s' <;> simp [Set.mem_union, hF]

omit [MeasurableSpace SigmaSpace] in
/-- The two joint fibres above a wing value are disjoint. -/
lemma joint_fibre_disjoint (S : SharedContextOutcomeMaps SigmaSpace) (C : MeasurementContext)
    {p q : Sign × Sign} (h : p ≠ q) :
    Disjoint {l | S.F C l = p} {l | S.F C l = q} := by
  rw [Set.disjoint_left]
  intro l hp hq
  exact h (hp ▸ hq ▸ rfl)

/-- **A-wing marginal of any table-reproducing family is `1/2`.** The wing fibre is
the disjoint union of its two joint fibres, whose masses are `P_st`, and those sum
to `1/2` by `marginal_a_eq_half`. -/
lemma wingA_marginal_of_table {μ : Measure SigmaSpace} (S : SharedContextOutcomeMaps SigmaSpace)
    (C : MeasurementContext) (hS : Measurable (S.F C))
    (htab : ReproducesSingletTableAt μ S C) (s : Sign) :
    μ {l | S.wingA C l = s} = ENNReal.ofReal (1 / 2) := by
  have hm : ∀ p : Sign × Sign, MeasurableSet {l | S.F C l = p} := fun p => by
    have : {l | S.F C l = p} = S.F C ⁻¹' {p} := rfl
    rw [this]
    exact hS (measurableSet_singleton p)
  rw [wingA_fibre_eq, measure_union (joint_fibre_disjoint S C (by simp)) (hm _),
    htab s Sign.plus, htab s Sign.minus,
    ← ENNReal.ofReal_add (P_st_nonneg C.a C.b s Sign.plus) (P_st_nonneg C.a C.b s Sign.minus)]
  congr 1
  have h := marginal_a_eq_half C.a C.b s
  rwa [Sign.sum_univ] at h

/-- **B-wing marginal of any table-reproducing family is `1/2`.** -/
lemma wingB_marginal_of_table {μ : Measure SigmaSpace} (S : SharedContextOutcomeMaps SigmaSpace)
    (C : MeasurementContext) (hS : Measurable (S.F C))
    (htab : ReproducesSingletTableAt μ S C) (t : Sign) :
    μ {l | S.wingB C l = t} = ENNReal.ofReal (1 / 2) := by
  have hm : ∀ p : Sign × Sign, MeasurableSet {l | S.F C l = p} := fun p => by
    have : {l | S.F C l = p} = S.F C ⁻¹' {p} := rfl
    rw [this]
    exact hS (measurableSet_singleton p)
  rw [wingB_fibre_eq, measure_union (joint_fibre_disjoint S C (by simp)) (hm _),
    htab Sign.plus t, htab Sign.minus t,
    ← ENNReal.ofReal_add (P_st_nonneg C.a C.b Sign.plus t) (P_st_nonneg C.a C.b Sign.minus t)]
  congr 1
  have h := marginal_b_eq_half C.a C.b t
  rwa [Sign.sum_univ] at h

/-- ★ **The exhibited model is operationally no-signalling.** Every wing marginal is
`1/2` at every context, so it is in particular invariant under a change of the remote
setting. This inhabits `LF3.OperationalNoSignalling` — the predicate C1 §4 is about —
rather than restating the kernel identity. -/
theorem singletContextualModel_no_signalling :
    OperationalNoSignalling kMuPsi singletContextualModel := by
  constructor
  · intro a b b' s
    rw [wingA_marginal_of_table singletContextualModel ⟨a, b⟩
        (singletContextualModel_measurable _) (singletContextualModel_table _) s,
      wingA_marginal_of_table singletContextualModel ⟨a, b'⟩
        (singletContextualModel_measurable _) (singletContextualModel_table _) s]
  · intro a a' b t
    rw [wingB_marginal_of_table singletContextualModel ⟨a, b⟩
        (singletContextualModel_measurable _) (singletContextualModel_table _) t,
      wingB_marginal_of_table singletContextualModel ⟨a', b⟩
        (singletContextualModel_measurable _) (singletContextualModel_table _) t]

/-! ### The every-setting no-go, discharged against the exhibited model

`no_product_partition_realises_singlet` is C1's *stronger* result (§3.2, §5.1): it
quantifies over every detector-setting pair, not just the four CHSH ones. But its
reproduction hypothesis `ReproducesSinglet` had no inhabitant either, so the no-go
was conditional in exactly the way the CHSH one was before Q19. The exhibited model
discharges it: its table holds at **every** context, so its correlation is the
singlet's everywhere, and the no-go then says the model's own wing responses cannot
be detached from the context. -/

/-- The model reproduces the singlet correlation at every context, not only the
four CHSH ones -- immediate from the every-context table. -/
theorem singletContextualModel_correlation (C : MeasurementContext) :
    integral kMuPsi (fun l => ((singletContextualModel.wingA C l).val : Real)
        * ((singletContextualModel.wingB C l).val : Real))
      = correlation C.a C.b :=
  integral_wing_mul_of_table kMuPsi singletContextualModel C
    (singletContextualModel_measurable C) (singletContextualModel_table C)

/-- **The exhibited model is irreducibly contextual.** Its wing responses cannot be
written as setting-local functions `RA a`, `RB b` of the state alone. This is C1 section
5.1's claim -- that Alice's response cannot be detached from the complete measurement
context and reused across Bob's alternatives -- as a theorem about an exhibited object
rather than a hypothesis. Routed through the every-setting no-go, whose reproduction
hypothesis the model discharges. -/
theorem singletContextualModel_not_product :
    Not (exists RA RB : DetectorSetting -> KSigma 4 -> Real,
        IsProductPartition RA RB /\
        (forall (a b : DetectorSetting) (l : KSigma 4),
          ((singletContextualModel.wingA (MeasurementContext.mk a b) l).val : Real) = RA a l) /\
        (forall (a b : DetectorSetting) (l : KSigma 4),
          ((singletContextualModel.wingB (MeasurementContext.mk a b) l).val : Real) = RB b l)) := by
  rintro ⟨RA, RB, hPP, hA, hB⟩
  refine no_product_partition_realises_singlet kMuPsi RA RB hPP ?_
  intro a b
  have hfun : (fun l => RA a l * RB b l)
      = fun l => ((singletContextualModel.wingA (MeasurementContext.mk a b) l).val : Real)
          * ((singletContextualModel.wingB (MeasurementContext.mk a b) l).val : Real) := by
    funext l
    rw [← hA a b l, ← hB a b l]
  show integral kMuPsi (fun l => RA a l * RB b l) = _
  rw [hfun, singletContextualModel_correlation (MeasurementContext.mk a b), singletCorrelation]

end SingletModel

end CSD.LF6

