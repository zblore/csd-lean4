import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.ZMod.Basic

/-!
# The CGLMP qudit Bell inequality and its local-hidden-variable bound

**Category:** Cat-1 (CSD-free general qudit Bell theory; a Mathlib-upstream-staging
candidate). Natural namespace `ProbabilityTheory.CGLMP`, no CSD wrapper.

This file formalises the Collins-Gisin-Linden-Massar-Popescu (CGLMP 2002) Bell
inequality for two parties, two settings per party, and `d` outcomes per setting.
It is the `d`-outcome generalisation of the two-outcome CHSH/Bell bound
(`|S| <= 2`).

## The local-hidden-variable model

Two parties. Each has two measurement settings (indexed by `Bool`), each setting
having `d` outcomes (in `ZMod d`). A **deterministic local-hidden-variable (LHV)
model** is a probability space `(Λ, μ)` of hidden variables together with local
response functions

```
A B : Bool → Λ → ZMod d,
```

with `A s l` Alice's outcome for setting `s` at hidden state `l` (Bob's `B`
likewise). Setting-locality on the shared `Λ` is the factorisation assumption.
The joint LHV probability of the mod-`d` outcome relation `A_x - B_y = k` is

```
lhvTable μ A B x y k = (μ {l | A x l - B y l = k}).toReal.
```

## The CGLMP functional `I_d`

Following the standard expression (settings `A_1 = A false`, `A_2 = A true`,
`B_1 = B false`, `B_2 = B true`, all outcome relations mod `d`):

```
I_d = ∑_{k=0}^{⌊d/2⌋-1} (1 - 2k/(d-1)) *
      ( [P(A_1=B_1+k) + P(B_1=A_2+k+1) + P(A_2=B_2+k) + P(B_2=A_1+k)]
      - [P(A_1=B_1-k-1) + P(B_1=A_2-k) + P(A_2=B_2-k-1) + P(B_2=A_1-k-1)] ).
```

Every term is rewritten in the single orientation `P(A_x - B_y = m)` using
`P(B_b = A_a + m) = P(A_a - B_b = -m)`; the result is `cglmp` applied to an
abstract probability table `p : Bool → Bool → ZMod d → K`. `cglmpLHV` is `cglmp`
on the LHV table. The classical (CGLMP) bound is `I_d ≤ 2`, and it is tight
(achieved by a deterministic strategy; see `scaledDetZ` and the numeric facts).

## Results

* `cglmpLHV_eq_integral` (general `d`): the CGLMP functional of an LHV model is
  the `μ`-average of its deterministic (per-hidden-state) CGLMP values. This is
  the linearity/reduction identity: an LHV model is a mixture of deterministic
  product strategies.
* `cglmpLHV_le_of_det_le` (general `d`, load-bearing): if every deterministic
  strategy has CGLMP value `≤ C`, then every LHV model has `cglmpLHV ≤ C`. This
  reduces the continuous LHV bound to the finite optimisation over
  `(ZMod d)^4` strategies.
* `cglmpDet_le_two`, `cglmp_lhv_bound_two` / `_three` / `_four`: the LHV bound
  `I_d ≤ 2` for `d = 2, 3, 4`. The finite optimisation is discharged by `decide`
  on the division-cleared integer functional `scaledDetZ` over `(ZMod d)^4`.
* `scaledDetZ_le_general`, `cglmp_lhv_bound` (general `d`): the numeric bound
  `scaledDetZ ≤ 2*(d-1)` and hence `I_d ≤ 2` for **every** `d ≥ 2`, proved by the
  CGLMP counting argument (the sawtooth reduction + the cyclic constraint), not by
  `decide`. This closes the numeric bound at full dimensional generality.

## Honest scope

* The reduction (`cglmpLHV_eq_integral`, `cglmpLHV_le_of_det_le`) is **general
  `d`**: the LHV-to-finite-optimisation bridge holds for every `d ≥ 2`.
* The numeric bound `I_d ≤ 2` is proved for **`d = 2, 3, 4`** by `decide` on the
  81 (`d = 3`) / 256 (`d = 4`) deterministic strategies (concrete anchors) AND for
  **every** `d ≥ 2` by the CGLMP counting argument (`scaledDetZ_le_general`,
  `cglmp_lhv_bound`). The general-`d` bound is the sawtooth reduction
  `scaledDetZ = -2 - 2·d·t` (`t ≥ -1` integer) forced by the cyclic constraint on
  the four outcome differences; it is a genuine proof, not `decide` (which only
  reduces at fixed `d`) and not axiomatised. `d = 3` is the genuine first qudit
  Bell inequality beyond CHSH.
* `d = 2` reduces to the CHSH bound: `⌊2/2⌋ = 1`, coefficient `1`, and the
  eight terms are the CHSH probabilities. This is a sanity anchor, not the
  deliverable; the two-outcome CHSH `|S| ≤ 2` already lives elsewhere.

Reference: Collins, Gisin, Linden, Massar, Popescu, *Phys. Rev. Lett.* **88**,
040404 (2002).
-/

open scoped BigOperators
open MeasureTheory

namespace ProbabilityTheory
namespace CGLMP

/-! ### The CGLMP functional on an abstract probability table -/

/-- The CGLMP bracket at index `k`: the eight-term signed combination of joint
outcome-relation probabilities. `p x y m` reads `P(A_x - B_y = m)`. The four
"positive" terms and four "negative" terms are the standard CGLMP grouping,
rewritten into the single orientation `A_x - B_y`. -/
def cglmpBracket {K : Type*} [Field K] (d : ℕ)
    (p : Bool → Bool → ZMod d → K) (k : ℕ) : K :=
  let κ : ZMod d := (k : ZMod d)
  ( p false false κ + p true false (-(κ + 1)) + p true true κ + p false true (-κ) )
    - ( p false false (-κ - 1) + p true false κ + p true true (-κ - 1) + p false true (κ + 1) )

/-- The CGLMP functional `I_d` on an abstract probability table `p`:
`∑_{k<⌊d/2⌋} (1 - 2k/(d-1)) * cglmpBracket d p k`. -/
def cglmp {K : Type*} [Field K] (d : ℕ) (p : Bool → Bool → ZMod d → K) : K :=
  ∑ k ∈ Finset.range (d / 2), (1 - 2 * (k : K) / ((d : K) - 1)) * cglmpBracket d p k

/-- The deterministic probability table for a fixed local strategy
`(a1, a2, b1, b2)` (Alice's outcomes for settings `false, true`, then Bob's):
`P(A_x - B_y = k)` is `1` if the strategy realises the relation, else `0`. -/
def detTable {K : Type*} [Field K] {d : ℕ} (a1 a2 b1 b2 : ZMod d) :
    Bool → Bool → ZMod d → K :=
  fun x y k => if (bif x then a2 else a1) - (bif y then b2 else b1) = k then 1 else 0

/-! ### The division-cleared integer functional (for the finite optimisation)

`decide` cannot reduce the rational/real functional (`Rat`/`Real` arithmetic does
not compute in the kernel). Multiplying the inequality `I_d ≤ 2` through by
`(d - 1) > 0` clears the denominators, giving an integer-valued functional
`scaledDetZ` that `decide` can evaluate over the finite strategy space. -/

/-- The integer indicator `⟦a - b = k⟧ ∈ {0, 1}`. -/
def detIndZ {d : ℕ} (a b k : ZMod d) : ℤ := if a - b = k then 1 else 0

/-- The integer CGLMP bracket (same eight-term structure as `cglmpBracket`, over
`ℤ`). -/
def bracketZ {d : ℕ} (a1 a2 b1 b2 : ZMod d) (k : ℕ) : ℤ :=
  let κ : ZMod d := (k : ZMod d)
  ( detIndZ a1 b1 κ + detIndZ a2 b1 (-(κ + 1)) + detIndZ a2 b2 κ + detIndZ a1 b2 (-κ) )
    - ( detIndZ a1 b1 (-κ - 1) + detIndZ a2 b1 κ + detIndZ a2 b2 (-κ - 1) + detIndZ a1 b2 (κ + 1) )

/-- The division-cleared integer CGLMP value of a deterministic strategy:
`(d - 1) * I_d^det = ∑_{k<⌊d/2⌋} (d - 1 - 2k) * bracketZ`. Kernel-`decide`-able
over `(ZMod d)^4`. -/
def scaledDetZ {d : ℕ} (a1 a2 b1 b2 : ZMod d) : ℤ :=
  ∑ k ∈ Finset.range (d / 2), ((d : ℤ) - 1 - 2 * k) * bracketZ a1 a2 b1 b2 k

/-- The real deterministic bracket equals the integer bracket cast to `ℝ`. -/
lemma cglmpBracket_detTable_eq {d : ℕ} (a1 a2 b1 b2 : ZMod d) (k : ℕ) :
    cglmpBracket d (detTable (K := ℝ) a1 a2 b1 b2) k = (bracketZ a1 a2 b1 b2 k : ℝ) := by
  simp only [cglmpBracket, bracketZ, detTable, detIndZ, Bool.cond_true, Bool.cond_false]
  push_cast
  ring

/-- The real deterministic CGLMP value equals `scaledDetZ / (d - 1)` (for
`d ≥ 2`). -/
lemma cglmp_detTable_eq {d : ℕ} (hd : 2 ≤ d) (a1 a2 b1 b2 : ZMod d) :
    cglmp d (detTable (K := ℝ) a1 a2 b1 b2) = (scaledDetZ a1 a2 b1 b2 : ℝ) / ((d : ℝ) - 1) := by
  have hne : ((d : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [cglmp, scaledDetZ]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cglmpBracket_detTable_eq]
  field_simp

/-! ### The LHV model and the CGLMP functional on it -/

variable {Λ : Type*} [MeasurableSpace Λ] {d : ℕ}

/-- The joint LHV probability table: `P(A_x - B_y = k) = μ {l | A x l - B y l = k}`
(as a real number). -/
noncomputable def lhvTable (μ : Measure Λ) (A B : Bool → Λ → ZMod d) :
    Bool → Bool → ZMod d → ℝ :=
  fun x y k => (μ {l | A x l - B y l = k}).toReal

/-- The CGLMP functional of an LHV model. -/
noncomputable def cglmpLHV (μ : Measure Λ) (A B : Bool → Λ → ZMod d) : ℝ :=
  cglmp d (lhvTable μ A B)

/-- Each LHV probability is the integral of the deterministic indicator over the
hidden variable: `P(A_x - B_y = k) = ∫ ⟦A x l - B y l = k⟧ dμ`. -/
lemma lhvTable_eq_integral [NeZero d] (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y))
    (x y : Bool) (k : ZMod d) :
    lhvTable μ A B x y k
      = ∫ l, detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l) x y k ∂μ := by
  have hset : MeasurableSet {l | A x l - B y l = k} :=
    ((hA x).sub (hB y)) (measurableSet_singleton k)
  have hfun : (fun l => detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l) x y k)
      = Set.indicator {l | A x l - B y l = k} 1 := by
    funext l; cases x <;> cases y <;> simp [detTable, Set.indicator_apply]
  rw [hfun, integral_indicator_one hset, lhvTable, measureReal_def]

/-- The deterministic indicator is integrable (bounded by `1`, measurable). -/
lemma detTable_integrable [NeZero d] (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y))
    (x y : Bool) (k : ZMod d) :
    Integrable (fun l => detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l) x y k) μ := by
  have hset : MeasurableSet {l | A x l - B y l = k} :=
    ((hA x).sub (hB y)) (measurableSet_singleton k)
  have hfun : (fun l => detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l) x y k)
      = Set.indicator {l | A x l - B y l = k} 1 := by
    funext l; cases x <;> cases y <;> simp [detTable, Set.indicator_apply]
  rw [hfun]
  exact (integrable_const (1 : ℝ)).indicator hset

/-! ### The deterministic reduction (general `d`) -/

/-- **The CGLMP reduction identity (general `d`).** The CGLMP functional of an LHV
model is the `μ`-average of the deterministic (per-hidden-state) CGLMP values. An
LHV model is a mixture of the deterministic product strategies
`(A false l, A true l, B false l, B true l)`; `cglmp` is linear in the probability
table, and the integral commutes with the finite linear combination. -/
theorem cglmpLHV_eq_integral [NeZero d] (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    cglmpLHV μ A B
      = ∫ l, cglmp d (detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l)) ∂μ := by
  set F : Λ → Bool → Bool → ZMod d → ℝ :=
    fun l => detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l) with hF
  have hterm : ∀ x y k, lhvTable μ A B x y k = ∫ l, F l x y k ∂μ := fun x y k =>
    lhvTable_eq_integral μ A B hA hB x y k
  have hint : ∀ x y k, Integrable (fun l => F l x y k) μ := fun x y k =>
    detTable_integrable μ A B hA hB x y k
  have hbint : ∀ k, Integrable (fun l => cglmpBracket d (F l) k) μ := by
    intro k
    simp only [cglmpBracket]
    exact ((((hint false false _).add (hint true false _)).add (hint true true _)).add
      (hint false true _)).sub
      ((((hint false false _).add (hint true false _)).add (hint true true _)).add
      (hint false true _))
  -- push the integral through the eight-term bracket, term by term
  have hbracket : ∀ k, ∫ l, cglmpBracket d (F l) k ∂μ = cglmpBracket d (lhvTable μ A B) k := by
    intro k
    simp only [cglmpBracket]
    have hP : Integrable (fun l => F l false false (k : ZMod d)
        + F l true false (-((k : ZMod d) + 1)) + F l true true (k : ZMod d)
        + F l false true (-(k : ZMod d))) μ :=
      (((hint false false _).add (hint true false _)).add (hint true true _)).add (hint false true _)
    have hP3 : Integrable (fun l => F l false false (k : ZMod d)
        + F l true false (-((k : ZMod d) + 1)) + F l true true (k : ZMod d)) μ :=
      ((hint false false _).add (hint true false _)).add (hint true true _)
    have hP2 : Integrable (fun l => F l false false (k : ZMod d)
        + F l true false (-((k : ZMod d) + 1))) μ :=
      (hint false false _).add (hint true false _)
    have hN : Integrable (fun l => F l false false (-(k : ZMod d) - 1)
        + F l true false (k : ZMod d) + F l true true (-(k : ZMod d) - 1)
        + F l false true ((k : ZMod d) + 1)) μ :=
      (((hint false false _).add (hint true false _)).add (hint true true _)).add (hint false true _)
    have hN3 : Integrable (fun l => F l false false (-(k : ZMod d) - 1)
        + F l true false (k : ZMod d) + F l true true (-(k : ZMod d) - 1)) μ :=
      ((hint false false _).add (hint true false _)).add (hint true true _)
    have hN2 : Integrable (fun l => F l false false (-(k : ZMod d) - 1)
        + F l true false (k : ZMod d)) μ :=
      (hint false false _).add (hint true false _)
    rw [integral_sub hP hN,
      integral_add hP3 (hint false true _), integral_add hP2 (hint true true _),
        integral_add (hint false false _) (hint true false _),
      integral_add hN3 (hint false true _), integral_add hN2 (hint true true _),
        integral_add (hint false false _) (hint true false _),
      ← hterm, ← hterm, ← hterm, ← hterm, ← hterm, ← hterm, ← hterm, ← hterm]
  rw [cglmpLHV, cglmp, show (fun l => cglmp d (F l))
      = (fun l => ∑ k ∈ Finset.range (d / 2),
          (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) * cglmpBracket d (F l) k) from rfl,
    integral_finset_sum _ (fun k _ => (hbint k).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, hbracket k]

/-- The pointwise deterministic CGLMP value is integrable over the hidden
variable (finite linear combination of integrable indicators). -/
lemma cglmpDet_integrable [NeZero d] (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    Integrable
      (fun l => cglmp d (detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l))) μ := by
  have hbint : ∀ k, Integrable (fun l => cglmpBracket d
      (detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l)) k) μ := by
    intro k
    simp only [cglmpBracket]
    exact ((((detTable_integrable μ A B hA hB false false _).add
      (detTable_integrable μ A B hA hB true false _)).add
      (detTable_integrable μ A B hA hB true true _)).add
      (detTable_integrable μ A B hA hB false true _)).sub
      ((((detTable_integrable μ A B hA hB false false _).add
      (detTable_integrable μ A B hA hB true false _)).add
      (detTable_integrable μ A B hA hB true true _)).add
      (detTable_integrable μ A B hA hB false true _))
  simp only [cglmp]
  exact integrable_finset_sum _ (fun k _ => (hbint k).const_mul _)

/-- **The LHV-to-finite-optimisation bound (general `d`, load-bearing).** If every
deterministic strategy `(a1, a2, b1, b2) ∈ (ZMod d)^4` has CGLMP value `≤ C`, then
every LHV model has `cglmpLHV ≤ C`. This is the convexity/averaging step: it
reduces the continuous LHV bound to a finite optimisation over the deterministic
strategies. -/
theorem cglmpLHV_le_of_det_le [NeZero d] (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y))
    (C : ℝ) (hdet : ∀ a1 a2 b1 b2 : ZMod d, cglmp d (detTable (K := ℝ) a1 a2 b1 b2) ≤ C) :
    cglmpLHV μ A B ≤ C := by
  rw [cglmpLHV_eq_integral μ A B hA hB]
  calc ∫ l, cglmp d (detTable (K := ℝ) (A false l) (A true l) (B false l) (B true l)) ∂μ
      ≤ ∫ _l : Λ, C ∂μ :=
        integral_mono (cglmpDet_integrable μ A B hA hB) (integrable_const C)
          (fun l => hdet _ _ _ _)
    _ = C := by simp

/-! ### The finite optimisation, discharged for `d = 2, 3, 4` -/

/-- Finite check `d = 2` (16 strategies): the division-cleared integer functional
is `≤ 2*(d-1)`. -/
lemma scaledDetZ_le_two : ∀ a1 a2 b1 b2 : ZMod 2, scaledDetZ a1 a2 b1 b2 ≤ 2 * ((2 : ℤ) - 1) := by
  decide

/-- Finite check `d = 3` (81 strategies): the first qudit Bell inequality beyond
CHSH. -/
lemma scaledDetZ_le_three : ∀ a1 a2 b1 b2 : ZMod 3, scaledDetZ a1 a2 b1 b2 ≤ 2 * ((3 : ℤ) - 1) := by
  decide

/-- Finite check `d = 4` (256 strategies), genuinely rational coefficient. -/
lemma scaledDetZ_le_four : ∀ a1 a2 b1 b2 : ZMod 4, scaledDetZ a1 a2 b1 b2 ≤ 2 * ((4 : ℤ) - 1) := by
  decide

/-- The deterministic CGLMP bound `I_d^det ≤ 2`, given the integer optimisation
`scaledDetZ ≤ 2*(d-1)`. Bridges the `decide`-friendly integer bound to the real
functional via `cglmp_detTable_eq`. -/
theorem cglmpDet_le_two {d : ℕ} (hd : 2 ≤ d)
    (hb : ∀ a1 a2 b1 b2 : ZMod d, scaledDetZ a1 a2 b1 b2 ≤ 2 * ((d : ℤ) - 1))
    (a1 a2 b1 b2 : ZMod d) :
    cglmp d (detTable (K := ℝ) a1 a2 b1 b2) ≤ 2 := by
  have hpos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [cglmp_detTable_eq hd, div_le_iff₀ hpos]
  have hcast : (scaledDetZ a1 a2 b1 b2 : ℝ) ≤ 2 * ((d : ℝ) - 1) := by
    have := hb a1 a2 b1 b2; push_cast at this ⊢; exact_mod_cast this
  linarith

/-- **CGLMP LHV bound, `d = 2`.** Reduces to CHSH; sanity anchor. -/
theorem cglmp_lhv_bound_two (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod 2) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    cglmpLHV μ A B ≤ 2 :=
  cglmpLHV_le_of_det_le μ A B hA hB 2
    (fun a1 a2 b1 b2 => cglmpDet_le_two (by norm_num) scaledDetZ_le_two a1 a2 b1 b2)

/-- **CGLMP LHV bound, `d = 3`.** The first genuine qudit Bell inequality beyond
CHSH: every deterministic local-hidden-variable model of two qutrits obeys
`I_3 ≤ 2`. -/
theorem cglmp_lhv_bound_three (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod 3) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    cglmpLHV μ A B ≤ 2 :=
  cglmpLHV_le_of_det_le μ A B hA hB 2
    (fun a1 a2 b1 b2 => cglmpDet_le_two (by norm_num) scaledDetZ_le_three a1 a2 b1 b2)

/-- **CGLMP LHV bound, `d = 4`.** `I_4 ≤ 2` (genuinely rational coefficient
`1 - 2/3`). -/
theorem cglmp_lhv_bound_four (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod 4) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    cglmpLHV μ A B ≤ 2 :=
  cglmpLHV_le_of_det_le μ A B hA hB 2
    (fun a1 a2 b1 b2 => cglmpDet_le_two (by norm_num) scaledDetZ_le_four a1 a2 b1 b2)

/-! ### Tightness (the bound `2` is achieved) -/

/-- **The `d = 3` bound is tight.** Some deterministic strategy attains
`scaledDetZ = 2*(d-1)`, i.e. `I_3^det = 2`. Together with `scaledDetZ_le_three`
this certifies the CGLMP classical bound is exactly `2` (achieved), not a loose
over-estimate. Hence the functional is the genuine CGLMP inequality, not a
relabelled trivial bound. -/
lemma scaledDetZ_three_tight :
    ∃ a1 a2 b1 b2 : ZMod 3, scaledDetZ a1 a2 b1 b2 = 2 * ((3 : ℤ) - 1) := by decide

/-- **The `d = 4` bound is tight.** -/
lemma scaledDetZ_four_tight :
    ∃ a1 a2 b1 b2 : ZMod 4, scaledDetZ a1 a2 b1 b2 = 2 * ((4 : ℤ) - 1) := by decide

/-! ### The general-`d` LHV bound (the CGLMP counting argument)

The numeric optimisation `scaledDetZ ≤ 2*(d-1)` is discharged for **all** `d`
(not merely `d = 2, 3, 4` via `decide`) by the CGLMP counting argument. The core
is the **sawtooth reduction**: the division-cleared functional collapses to four
values of the single linear-on-representatives sawtooth `S(r) = d - 1 - 2·val(r)`,
evaluated at the four outcome differences `a₁−b₁, a₂−b₁, a₂−b₂, (a₁−b₂)−1`. The
cyclic constraint `(a₁−b₁) − (a₂−b₁) + (a₂−b₂) − ((a₁−b₂)−1) = 1` (mod `d`) then
forces `scaledDetZ = -2 - 2·d·t` with `t ≥ -1` (integer), whence
`scaledDetZ ≤ 2(d-1)`, tight at `t = -1`. No `decide`, no dimension restriction. -/

/-- The CGLMP sawtooth `S(r) = d - 1 - 2·val(r)`: the single coefficient function
to which the division-cleared functional collapses. Linear in the standard
representative `val r`; its antisymmetric arm structure (the low arm `k` and the
high arm `d-1-k`) is exactly the CGLMP weight pattern `d - 1 - 2k`. -/
def sawtooth (d : ℕ) (r : ZMod d) : ℤ := (d : ℤ) - 1 - 2 * (r.val : ℤ)

/-- `val (-r - 1) = d - 1 - val r`: the reflection carrying the low arm to the
high arm. -/
lemma val_neg_sub_one [NeZero d] (r : ZMod d) :
    (-r - 1 : ZMod d).val = d - 1 - r.val := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hlt : r.val < d := ZMod.val_lt r
  have hle : r.val ≤ d - 1 := by omega
  have hlt2 : d - 1 - r.val < d := by omega
  have hcast : (-r - 1 : ZMod d) = ((d - 1 - r.val : ℕ) : ZMod d) := by
    rw [Nat.cast_sub hle, Nat.cast_sub hd1, ZMod.natCast_self, Nat.cast_one,
      ZMod.natCast_zmod_val]
    ring
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt2]

/-- The positive-arm collector: `∑_k (d-1-2k)·⟦r = k⟧` picks out the single term
`k = val r` when `val r < ⌊d/2⌋`. -/
lemma sawtooth_sum_pos [NeZero d] (r : ZMod d) :
    ∑ k ∈ Finset.range (d/2), ((d:ℤ)-1-2*(k:ℤ)) * (if r = (k:ZMod d) then (1:ℤ) else 0)
      = if r.val < d/2 then ((d:ℤ)-1-2*(r.val:ℤ)) else 0 := by
  rw [Finset.sum_congr rfl (fun k hk => ?_)]
  · rw [Finset.sum_ite_eq' (Finset.range (d/2)) r.val (fun k => ((d:ℤ)-1-2*(k:ℤ)))]
    simp only [Finset.mem_range]
  · have hk' : k < d := by simp only [Finset.mem_range] at hk; omega
    have hiff : (r = (k:ZMod d)) ↔ (k = r.val) := by
      constructor
      · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt hk']
      · intro h; rw [h, ZMod.natCast_zmod_val]
    rw [if_congr hiff rfl rfl, mul_ite, mul_one, mul_zero]

/-- The negative-arm collector: `∑_k (d-1-2k)·⟦r = -k-1⟧` picks out the reflected
term `k = d-1-val r`. -/
lemma sawtooth_sum_neg [NeZero d] (r : ZMod d) :
    ∑ k ∈ Finset.range (d/2), ((d:ℤ)-1-2*(k:ℤ)) * (if r = -(k:ZMod d)-1 then (1:ℤ) else 0)
      = if (d-1-r.val) < d/2 then ((d:ℤ)-1-2*((d-1-r.val : ℕ):ℤ)) else 0 := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  rw [Finset.sum_congr rfl (fun k hk => ?_)]
  · rw [Finset.sum_ite_eq' (Finset.range (d/2)) (d-1-r.val) (fun k => ((d:ℤ)-1-2*(k:ℤ)))]
    simp only [Finset.mem_range]
  · have hk' : k < d := by simp only [Finset.mem_range] at hk; omega
    have hiff : (r = -(k:ZMod d)-1) ↔ (k = d-1-r.val) := by
      have hkc : ((k:ZMod d) = -r-1) ↔ (k = d-1-r.val) := by
        constructor
        · intro h
          have hv : (k:ZMod d).val = (-r-1 : ZMod d).val := by rw [h]
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk', val_neg_sub_one] at hv
          exact hv
        · intro h; rw [h]
          have hc : ((d - 1 - r.val : ℕ) : ZMod d) = (-r - 1 : ZMod d) := by
            have hle : r.val ≤ d - 1 := by have := ZMod.val_lt r; omega
            rw [Nat.cast_sub hle, Nat.cast_sub hd1, ZMod.natCast_self, Nat.cast_one,
              ZMod.natCast_zmod_val]; ring
          rw [hc]
      rw [← hkc]; constructor <;> intro h <;> (rw [h]; ring)
    rw [if_congr hiff rfl rfl, mul_ite, mul_one, mul_zero]

/-- **The sawtooth collapse.** The weighted difference of the two arm collectors
equals the sawtooth `S(r)` for every `r` (both arms and the middle fixed point
covered by the same linear formula `d - 1 - 2·val r`). -/
lemma sawtooth_weighted_sum [NeZero d] (r : ZMod d) :
    ∑ k ∈ Finset.range (d/2), ((d:ℤ)-1-2*(k:ℤ)) *
        ((if r = (k:ZMod d) then (1:ℤ) else 0) - (if r = -(k:ZMod d)-1 then (1:ℤ) else 0))
      = sawtooth d r := by
  have hlt : r.val < d := ZMod.val_lt r
  simp only [mul_sub, Finset.sum_sub_distrib, sawtooth_sum_pos, sawtooth_sum_neg]
  unfold sawtooth
  split_ifs <;> omega

/-- **The per-index bracket identity.** The integer CGLMP bracket at index `k`
equals the signed combination of the four differences' arm summands. This is the
purely combinatorial rewrite of `bracketZ` into the sawtooth arms; the `a₁−b₂`
difference carries the `-1` shift (via `(a₁−b₂)−1`). -/
lemma bracketZ_eq_sawtooth_summand (a1 a2 b1 b2 : ZMod d) (k : ℕ) :
    bracketZ a1 a2 b1 b2 k
      = ((if a1-b1 = (k:ZMod d) then (1:ℤ) else 0) - (if a1-b1 = -(k:ZMod d)-1 then (1:ℤ) else 0))
      - ((if a2-b1 = (k:ZMod d) then (1:ℤ) else 0) - (if a2-b1 = -(k:ZMod d)-1 then (1:ℤ) else 0))
      + ((if a2-b2 = (k:ZMod d) then (1:ℤ) else 0) - (if a2-b2 = -(k:ZMod d)-1 then (1:ℤ) else 0))
      - ((if (a1-b2)-1 = (k:ZMod d) then (1:ℤ) else 0) - (if (a1-b2)-1 = -(k:ZMod d)-1 then (1:ℤ) else 0)) := by
  simp only [bracketZ, detIndZ]
  rw [show (-((k:ZMod d)+1) : ZMod d) = -(k:ZMod d)-1 from by ring]
  have eB : ((a1-b2)-1 = -(k:ZMod d)-1) = (a1-b2 = -(k:ZMod d)) := by
    apply propext; constructor <;> intro h <;> linear_combination h
  have eC : ((a1-b2)-1 = (k:ZMod d)) = (a1-b2 = (k:ZMod d)+1) := by
    apply propext; constructor <;> intro h <;> linear_combination h
  simp only [eB, eC]
  ring

/-- **The sawtooth reduction (general `d`).** The division-cleared functional
equals the signed sum of the four sawtooth values at the outcome differences. This
is the structural half of the counting argument: `scaledDetZ` is fully determined
by the four differences and the single sawtooth `S`. -/
lemma scaledDetZ_eq_sawtooth [NeZero d] (a1 a2 b1 b2 : ZMod d) :
    scaledDetZ a1 a2 b1 b2
      = sawtooth d (a1-b1) - sawtooth d (a2-b1) + sawtooth d (a2-b2) - sawtooth d ((a1-b2)-1) := by
  rw [scaledDetZ, ← sawtooth_weighted_sum (a1-b1), ← sawtooth_weighted_sum (a2-b1),
      ← sawtooth_weighted_sum (a2-b2), ← sawtooth_weighted_sum ((a1-b2)-1)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bracketZ_eq_sawtooth_summand]; ring

/-- **The general-`d` CGLMP numeric bound (the counting argument).** For every
deterministic strategy `(a₁, a₂, b₁, b₂) ∈ (ZMod d)^4` and every `d ≥ 2`,
`scaledDetZ ≤ 2*(d-1)`. This discharges the named residual `cglmpDet_le_two`'s
hypothesis for all `d`: the sawtooth reduction gives
`scaledDetZ = -2 - 2·d·t` where `t` is the integer witnessing the cyclic
constraint `∑(differences) ≡ 1 (mod d)`, and the outcome-difference bounds
`0 ≤ val < d` force `t ≥ -1`, hence `scaledDetZ ≤ 2(d-1)` (tight at `t = -1`;
cf. `scaledDetZ_three_tight`, `scaledDetZ_four_tight`). -/
theorem scaledDetZ_le_general [NeZero d] (hd : 2 ≤ d) (a1 a2 b1 b2 : ZMod d) :
    scaledDetZ a1 a2 b1 b2 ≤ 2 * ((d:ℤ) - 1) := by
  rw [scaledDetZ_eq_sawtooth]
  unfold sawtooth
  have hconstr : (a1-b1) - (a2-b1) + (a2-b2) - ((a1-b2)-1) = (1 : ZMod d) := by ring
  have hqZ : ((a2-b1).val:ℤ) < d := by exact_mod_cast ZMod.val_lt (a2-b1)
  have hsZ : (((a1-b2)-1).val:ℤ) < d := by exact_mod_cast ZMod.val_lt ((a1-b2)-1)
  have hp0 : (0:ℤ) ≤ ((a1-b1).val:ℤ) := Int.natCast_nonneg _
  have hr0 : (0:ℤ) ≤ ((a2-b2).val:ℤ) := Int.natCast_nonneg _
  have hdpos : (0:ℤ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdvd : (d:ℤ) ∣ (((a1-b1).val : ℤ) - (a2-b1).val + (a2-b2).val - ((a1-b2)-1).val - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [ZMod.natCast_zmod_val]
    rw [sub_eq_zero]
    linear_combination hconstr
  obtain ⟨t, ht⟩ := hdvd
  have htge : -1 ≤ t := by
    by_contra hcon
    push_neg at hcon
    have ht2 : t ≤ -2 := by omega
    have hmul : (d:ℤ) * t ≤ (d:ℤ) * (-2) := mul_le_mul_of_nonneg_left ht2 (le_of_lt hdpos)
    nlinarith [ht, hqZ, hsZ, hp0, hr0]
  have hdt : (d:ℤ) * (-1) ≤ (d:ℤ) * t := mul_le_mul_of_nonneg_left htge (le_of_lt hdpos)
  linarith [ht, hdt]

/-- **The CGLMP LHV bound, general `d`.** For every `d ≥ 2` and every deterministic
local-hidden-variable model of two `d`-outcome parties, the CGLMP functional obeys
`I_d ≤ 2`. Composes the LHV-to-finite-optimisation reduction
(`cglmpLHV_le_of_det_le`) with the general-`d` counting argument
(`scaledDetZ_le_general`) through the integer-to-real bridge (`cglmpDet_le_two`).
This closes the numeric bound at full dimensional generality; the `d = 2, 3, 4`
`decide` variants (`cglmp_lhv_bound_two/_three/_four`) are the concrete anchors. -/
theorem cglmp_lhv_bound (μ : Measure Λ) [IsProbabilityMeasure μ] (hd : 2 ≤ d)
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    cglmpLHV μ A B ≤ 2 := by
  haveI : NeZero d := ⟨by omega⟩
  exact cglmpLHV_le_of_det_le μ A B hA hB 2
    (fun a1 a2 b1 b2 =>
      cglmpDet_le_two hd (fun a1 a2 b1 b2 => scaledDetZ_le_general hd a1 a2 b1 b2) a1 a2 b1 b2)

end CGLMP
end ProbabilityTheory
