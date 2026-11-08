/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.SyndromeDecoder
public import CsdLean4.Mathlib.QuantumInfo.RectGeometry

/-!
# The exact one-level reduction

**Category:** 1-Mathlib (CSD-free). BACKLOG #323 (split from #319).

A level-`k` run is a chain of rectangles — leading recovery `T j`, gadget `G j`, trailing recovery
`T (j + 1)` — each recovery shared by two neighbours (`recRun`, #316). Mark any set of rectangles
bad. Move the syndrome-keeping decoder `X ↦ W X W†` (#316) from the end of the run to its start:

* past a **good** rectangle it moves past the gadget and the trailing recovery, and stops after the
  leading one;
* past a **bad** rectangle it moves by inserting `W† W = 1`, and the bad rectangle becomes a
  faulty location on logical ⊗ syndrome that **absorbs its leading recovery** — so the good
  rectangle before it is checked **without its trailing recovery**, `IsGoodAfter D U T G id`.

The bookkeeping is exact: each recovery belongs to exactly one stage (`inRec`, `outRec`, `stage`),
the run regroups into the stages (★★ `recRun_eq_ovIdeal_stage`), and the decoded run **is** the
run of the lifted stages on logical ⊗ syndrome (★★★ `conj_recRun_eq`). On the input the run feeds
it, a good stage acts on the logical register as its ideal gate (★★★
`partialTraceRight_liftRect_stage`); a bad stage is an arbitrary map that may read and write the
syndrome — the environment-coupled faulty location one level down.

## Classical feed-forward

The maps are arbitrary maps on one register `n`, so measurements and classically controlled gates
are maps on a register that includes the classical bits; nothing here distinguishes them.

## The noise

The bad set is #322's badness, with the chain taken in **decoding order** — rectangle `j` of the
run is rectangle `N − 1 − j` of the family, so a rectangle is truncated by its bad *successor*
(`timeBad`). Then (★★★ `exact_reduction_of_rectFamily`) for every fault pattern the decoded run is
the reduced run with good locations ideal on their inputs, and the reduced fault pattern is
local stochastic with parameter `A p²` (`isLocalStochastic_map_reducePat`, #322); every rectangle
is good with probability at least `1 − N A p²` (★★ `one_sub_le_measure_forall_timeBad_eq_false`),
and then the decoded run is the ideal logical run (`decode_recRun_of_isGoodAfter`, #316).

## Honest scope

⚠️ **Goodness is a hypothesis**, code-specific as in #316: `IsGoodAfter` with the truncated trailing
recovery. At the Steane code the full form is ~~#321~~'s `steane_rect_isGoodAfter`; the truncated
form `IsGoodAfter D U T G id` is not proved there.

⚠️ **One block at a time.** The chain is serialised: a recovery is shared only with the next stage.
A two-block gadget (`CNOT̄`) shares a recovery with a successor that is not next in the serialised
run; moving it there needs the stages in between, on other blocks, to commute with it. That is
#332.

⚠️ **Maps, not channels**, as in #316: no positivity or trace preservation.

⚠️ **The reduced run is not traced in the middle.** A bad stage acts on logical ⊗ syndrome, so the
reduced run is a run on `m × s`, with the syndrome as environment; making the next level's
rectangles good for such locations is #324.

## References

P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, §§ 4–5 (the `*`-decoder
moved through the circuit, truncated extended rectangles);
`Mathlib/QuantumInfo/SyndromeDecoder.lean` (#316), `Mathlib/QuantumInfo/RectGeometry.lean` (#322);
`specs/BACKLOG.md` #323, #319, #324, #332, #315; `specs/future-work.md`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuantumInfo

variable {n m s : Type*}

/-! ### Who owns each recovery -/

section Stages

variable (b : ℕ → Bool) (N : ℕ) (T G : ℕ → Matrix n n ℂ → Matrix n n ℂ)

/-- The leading recovery of rectangle `j` belongs to it when it is bad (a bad rectangle absorbs
it). -/
def inRec (j : ℕ) : Matrix n n ℂ → Matrix n n ℂ :=
  if j < N ∧ b j = true then T j else id

/-- The trailing recovery of rectangle `j` belongs to it unless its successor is bad. -/
def outRec (j : ℕ) : Matrix n n ℂ → Matrix n n ℂ :=
  if j + 1 < N ∧ b (j + 1) = true then id else T (j + 1)

/-- **Stage `j`**: rectangle `j` with the recoveries it owns. -/
def stage (j : ℕ) : Matrix n n ℂ → Matrix n n ℂ :=
  outRec b N T j ∘ G j ∘ inRec b N T j

/-- The input to the first stage: the first recovery is applied unless rectangle `0` owns it. -/
def runInit (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  if 0 < N ∧ b 0 = true then ρ else T 0 ρ

theorem inRec_of_good {j : ℕ} (hj : b j = false) : inRec b N T j = id := by
  unfold inRec
  rw [ite_eq_right (by simp [hj])]

theorem recRun_eq_stage (ρ : Matrix n n ℂ) :
    ∀ k ≤ N, recRun T G k ρ
      = if k < N ∧ b k = true then T k (ovIdeal (stage b N T G) k (runInit b N T ρ))
        else ovIdeal (stage b N T G) k (runInit b N T ρ)
  | 0, _ => by
    by_cases h : 0 < N ∧ b 0 = true
    · simp only [ovIdeal_zero, runInit, ite_eq_left h]
      rfl
    · simp only [ovIdeal_zero, runInit, ite_eq_right h]
      rfl
  | k + 1, hk => by
    have ih := recRun_eq_stage ρ k (by omega)
    have hstep : recRun T G (k + 1) ρ
        = T (k + 1) (G k (inRec b N T k (ovIdeal (stage b N T G) k (runInit b N T ρ)))) := by
      show T (k + 1) (G k (recRun T G k ρ)) = _
      rw [ih]
      unfold inRec
      have hk' : k < N := by omega
      by_cases h : b k = true
      · rw [ite_eq_left ⟨hk', h⟩, ite_eq_left ⟨hk', h⟩]
      · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right (fun h' => h h'.2)]
        rfl
    rw [hstep, ovIdeal_succ]
    unfold stage outRec
    by_cases h : k + 1 < N ∧ b (k + 1) = true
    · rw [ite_eq_left h, ite_eq_left h]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
      rfl

/-- ★★ **The run regroups into its stages**: every recovery belongs to exactly one stage. -/
theorem recRun_eq_ovIdeal_stage (ρ : Matrix n n ℂ) :
    recRun T G N ρ = ovIdeal (stage b N T G) N (runInit b N T ρ) := by
  have h := recRun_eq_stage b N T G ρ N le_rfl
  rwa [ite_eq_right (fun h' => (lt_irrefl N h'.1).elim)] at h

/-- A good rectangle's input in the run is the output of its leading recovery. -/
theorem ovIdeal_stage_of_good (ρ : Matrix n n ℂ) {j : ℕ} (hj : j ≤ N) (hg : b j = false) :
    ovIdeal (stage b N T G) j (runInit b N T ρ) = recRun T G j ρ := by
  rw [recRun_eq_stage b N T G ρ j hj, ite_eq_right (fun h' => by simp [hg] at h')]

end Stages

variable [Fintype n] [Fintype m] [Fintype s] [DecidableEq n]

/-! ### The decoded run is the reduced run -/

/-- Lifting a map and applying it to a decoded state decodes its output. -/
theorem liftRect_conj {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1)
    (R : Matrix n n ℂ → Matrix n n ℂ) (Z : Matrix n n ℂ) :
    liftRect W R (W * Z * Wᴴ) = W * R Z * Wᴴ := by
  unfold liftRect
  congr 3
  calc Wᴴ * (W * Z * Wᴴ) * W = (Wᴴ * W) * Z * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [hW, Matrix.one_mul, Matrix.mul_one]

/-- ★★★ **The decoded run is the reduced run, exactly**: for any set of bad rectangles, the run
conjugated by `W` is the run of the lifted stages on logical ⊗ syndrome. -/
theorem conj_recRun_eq {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1) (b : ℕ → Bool) (N : ℕ)
    (T G : ℕ → Matrix n n ℂ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    W * recRun T G N ρ * Wᴴ
      = ovIdeal (fun j => liftRect W (stage b N T G j)) N (W * runInit b N T ρ * Wᴴ) := by
  rw [recRun_eq_ovIdeal_stage b N T G ρ, conj_ovIdeal hW]

/-- ★★★ **A good location of the reduced run is its ideal gate on the input the run feeds it**:
if rectangle `j` is good after its leading recovery with the trailing recovery it owns, the lifted
stage `j`, applied to what the reduced run gives it, acts on the logical register as `U`. -/
theorem partialTraceRight_liftRect_stage {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1)
    (b : ℕ → Bool) (N : ℕ) (T G : ℕ → Matrix n n ℂ → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    {j : ℕ} (hj : j < N) (hg : b j = false) {U : Matrix m m ℂ}
    (hgood : IsGoodAfter (synDecode W) U (T j) (G j) (outRec b N T j)) :
    partialTraceRight (liftRect W (stage b N T G j)
        (ovIdeal (fun i => liftRect W (stage b N T G i)) j (W * runInit b N T ρ * Wᴴ)))
      = U * partialTraceRight
          (ovIdeal (fun i => liftRect W (stage b N T G i)) j (W * runInit b N T ρ * Wᴴ)) * Uᴴ := by
  rw [← conj_ovIdeal hW, ovIdeal_stage_of_good b N T G ρ hj.le hg]
  obtain ⟨Y, hY⟩ := recRun_eq_apply T G j ρ
  rw [hY, liftRect_conj hW]
  have hs : stage b N T G j (T j Y) = outRec b N T j (G j (T j Y)) := by
    unfold stage
    rw [inRec_of_good b N T hg]
    rfl
  rw [hs]
  exact hgood Y

/-! ### Joined with the badness of #322 -/

section Noise

variable {ι : Type*} [DecidableEq ι]

/-- **Badness in time order**: rectangle `j` of a run of `N` is rectangle `N − 1 − j` of the
family, which lists the rectangles in decoding order. -/
def timeBad (F : RectFamily ι) (N : ℕ) (ω : ι → Bool) (j : ℕ) : Bool :=
  F.bad ω (N - 1 - j)

/-- ★★★ **The exact one-level reduction, joined with the noise.** For a family `F` of rectangles in
decoding order and every fault pattern `ω`: the decoded run is the reduced run of the lifted
stages, and every rectangle that is not bad is its ideal gate on its input, provided it is good
after its leading recovery with the trailing recovery it owns. -/
theorem exact_reduction_of_rectFamily {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1)
    (F : RectFamily ι) (N : ℕ) (T G : (ι → Bool) → ℕ → Matrix n n ℂ → Matrix n n ℂ)
    (U : ℕ → Matrix m m ℂ)
    (hgood : ∀ ω, ∀ j < N, timeBad F N ω j = false →
      IsGoodAfter (synDecode W) (U j) (T ω j) (G ω j) (outRec (timeBad F N ω) N (T ω) j))
    (ω : ι → Bool) (ρ : Matrix n n ℂ) :
    W * recRun (T ω) (G ω) N ρ * Wᴴ
        = ovIdeal (fun j => liftRect W (stage (timeBad F N ω) N (T ω) (G ω) j)) N
          (W * runInit (timeBad F N ω) N (T ω) ρ * Wᴴ) ∧
      ∀ j < N, timeBad F N ω j = false →
        partialTraceRight (liftRect W (stage (timeBad F N ω) N (T ω) (G ω) j)
            (ovIdeal (fun i => liftRect W (stage (timeBad F N ω) N (T ω) (G ω) i)) j
              (W * runInit (timeBad F N ω) N (T ω) ρ * Wᴴ)))
          = U j * partialTraceRight
              (ovIdeal (fun i => liftRect W (stage (timeBad F N ω) N (T ω) (G ω) i)) j
                (W * runInit (timeBad F N ω) N (T ω) ρ * Wᴴ)) * (U j)ᴴ :=
  ⟨conj_recRun_eq hW _ N (T ω) (G ω) ρ, fun j hj hg =>
    partialTraceRight_liftRect_stage hW _ N (T ω) (G ω) ρ hj hg (hgood ω j hj hg)⟩

/-- ★★ **Every rectangle is good with probability at least `1 − N A p²`**, under local stochastic
noise of parameter `p` with at most `A` malignant pairs per rectangle. -/
theorem one_sub_le_measure_forall_timeBad_eq_false (F : RectFamily ι) {μ : Measure (ι → Bool)}
    [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hμ : IsLocalStochastic μ p) {A : ℕ}
    (hA : ∀ j, (F.M j).card ≤ A) (N : ℕ) :
    1 - (N : ℝ≥0∞) * ((A : ℝ≥0∞) * p ^ 2)
      ≤ μ {ω | ∀ j < N, timeBad F N ω j = false} := by
  have hbad := F.measure_exists_bad_le hμ hA (Finset.range N)
  rw [Finset.card_range] at hbad
  have hsub : {ω : ι → Bool | ∀ j < N, timeBad F N ω j = false}ᶜ
      ⊆ {ω | ∃ j ∈ Finset.range N, F.bad ω j = true} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, Bool.not_eq_false] at hω
    obtain ⟨j, hj, hb⟩ := hω
    exact ⟨N - 1 - j, Finset.mem_range.2 (by omega), hb⟩
  have h1 := measure_mono (μ := μ) hsub
  have h2 : 1 ≤ μ {ω : ι → Bool | ∀ j < N, timeBad F N ω j = false}
      + μ {ω : ι → Bool | ∀ j < N, timeBad F N ω j = false}ᶜ := by
    rw [← measure_univ (μ := μ)]
    exact (measure_mono (Set.union_compl_self _).ge).trans (measure_union_le _ _)
  calc 1 - (N : ℝ≥0∞) * ((A : ℝ≥0∞) * p ^ 2)
      ≤ 1 - μ {ω : ι → Bool | ∀ j < N, timeBad F N ω j = false}ᶜ :=
        tsub_le_tsub_left (h1.trans hbad) 1
    _ ≤ μ {ω : ι → Bool | ∀ j < N, timeBad F N ω j = false} :=
        tsub_le_iff_right.2 h2

omit [DecidableEq n] in
/-- With no rectangle bad, every stage is the rectangle with its trailing recovery, so the reduced
run is #316's chain and the decoded run is the ideal logical run. -/
theorem decode_recRun_of_forall_timeBad_eq_false {W : Matrix (m × s) n ℂ} (F : RectFamily ι)
    (N : ℕ) (T G : ℕ → Matrix n n ℂ → Matrix n n ℂ) (U : ℕ → Matrix m m ℂ) {ω : ι → Bool}
    (hω : ∀ j < N, timeBad F N ω j = false)
    (hgood : ∀ j < N, IsGoodAfter (synDecode W) (U j) (T j) (G j) (outRec (timeBad F N ω) N T j))
    (ρ : Matrix n n ℂ) :
    synDecode W (recRun T G N ρ)
      = ovIdeal (fun j Y => U j * Y * (U j)ᴴ) N (synDecode W (T 0 ρ)) := by
  refine decode_recRun_of_isGoodAfter (fun j hj => ?_) N le_rfl ρ
  have h := hgood j hj
  have hout : outRec (timeBad F N ω) N T j = T (j + 1) := by
    unfold outRec
    by_cases h' : j + 1 < N
    · rw [ite_eq_right (fun h'' => by simp [hω (j + 1) h'] at h'')]
    · rw [ite_eq_right (fun h'' => h' h''.1)]
  rwa [hout] at h

end Noise

end QuantumInfo
