/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Register
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Amplitude amplification: the closed form and the `⌊π/(4θ)⌋` bound (BHMT)

**Category:** 1-Mathlib (CSD-free).

**Glossary:** https://glossary.constraintsurfacedynamics.com/amplitude-amplification/
Plain-language, CSD-role and formal statements of amplitude amplification, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

Brassard–Høyer–Mosca–Tapp amplitude amplification (quant-ph/0005055), the theorem Grover's
algorithm is an instance of, on a register over an arbitrary finite computational basis `ι`
with an arbitrary good set `G : Finset ι`:

* **The two-reflection rotation.** The amplification step
  `ampStep φ G = reflect φ ∘ oracleFlip G` — reflection about the initial state composed with
  the sign flip on the good coordinates — acts on the plane spanned by the (unit) good and bad
  components as a **rotation by `2θ`** (`ampStep_ampState`), where `sin θ = √(goodProb G φ)`.
* ★★ **The closed form** (`amplitude_amplification`): for any unit `ψ` with
  `0 < goodProb G ψ < 1`, after `j` amplification rounds the success probability is exactly
  `sin²((2j+1)·θ)` with `θ = arcsin √(goodProb G ψ)`. No asymptotics.
* ★ **The optimal count** (`amplitude_amplification_succeeds`): `m = ⌊π/(4θ)⌋` rounds land the
  angle within `θ` of `π/2`, so the success probability is at least `1 − a`.
* ★ **The quadratic speedup** (`amplification_query_bound`): `m ≤ π/(4√a)`, since
  `√a = sin θ ≤ θ`.
* Non-vacuity at a closed instance (`amplification_quarter`): at `a = 1/4` a **single** round
  succeeds with certainty (`θ = π/6`, `3θ = π/2`).

Grover's algorithm is the instance `φ = uniform superposition`, `G = {w}`
(`Empirical/QM/Algorithms/Grover.lean` re-derives its headline from this module), and the
`k`-marked-items generalisation is the instance `|G| = k` (`grover_multi_success`, same file).

## Honest scope

Query counting is by rounds of the abstract step; no oracle model or gate decomposition is
claimed (the same matrix-level scope as `Fourier.lean`/`PhaseEstimation.lean`). The degenerate
boundaries are real and excluded by hypothesis: `goodProb = 0` leaves no plane to rotate and
`goodProb = 1` nothing to amplify. Amplitude *estimation* (BHMT Thm 12) is assembled in
`AmplitudeEstimation.lean` from this module's eigenstructure section. For unknown `a`, the
**QSearch engine** (BHMT Lemma 2) is the final section here: a uniformly random round count
below `M` succeeds with average probability `≥ 1/4` once `M·sin 2θ ≥ 1`
(`qsearch_average`) — the paper's Thm 3 wraps this in an exponential-doubling schedule whose
expected-runtime bookkeeping is a probabilistic-process argument, recorded in
`specs/amplitude-amplification-plan.md` (AA-6) and not formalised.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The operators -/

/-- The **good-coordinate truncation** `P_G ψ`: keep the amplitudes on `G`, zero elsewhere. -/
noncomputable def goodProj (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (WithLp.equiv 2 (ι → ℂ)).symm (fun i => if i ∈ G then ψ i else 0)

omit [Fintype ι] in
@[simp] lemma goodProj_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    goodProj G ψ i = if i ∈ G then ψ i else 0 := rfl

/-- The **success probability** of `ψ` against the good set `G`: `∑_{i ∈ G} ‖ψ i‖²`. -/
noncomputable def goodProb (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : ℝ := ∑ i ∈ G, ‖ψ i‖ ^ 2

omit [Fintype ι] [DecidableEq ι] in
lemma goodProb_nonneg (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : 0 ≤ goodProb G ψ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype ι] [DecidableEq ι] in
/-- The success probability is the sum of the Born probabilities over the good set. -/
lemma goodProb_eq_sum_prob (G : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    goodProb G ψ = ∑ i ∈ G, prob ψ i := rfl

/-- The **oracle reflection** `I − 2 P_G`: a phase flip on the good coordinates. -/
noncomputable def oracleFlip (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  ψ - (2 : ℂ) • goodProj G ψ

omit [Fintype ι] in
lemma oracleFlip_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    oracleFlip G ψ i = ψ i - 2 * (if i ∈ G then ψ i else 0) := by
  rw [oracleFlip, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply,
    goodProj_apply, smul_eq_mul]

/-- The **reflection about a state** `2|φ⟩⟨φ| − I` (the generalised diffusion operator). -/
noncomputable def reflect (φ ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (2 * inner ℂ φ ψ) • φ - ψ

/-- One **amplification step**: the oracle flip followed by reflection about `φ`. -/
noncomputable def ampStep (φ : EuclideanSpace ℂ ι) (G : Finset ι)
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  reflect φ (oracleFlip G ψ)

/-! ## The rotation plane -/

/-- The **rotation-plane state at angle `γ`**: `(sin γ) g + (cos γ) b` for a good unit
component `g` and a bad unit component `b`. -/
noncomputable def ampState (g b : EuclideanSpace ℂ ι) (γ : ℝ) : EuclideanSpace ℂ ι :=
  (Real.sin γ : ℂ) • g + (Real.cos γ : ℂ) • b

omit [Fintype ι] [DecidableEq ι] in
lemma ampState_apply (g b : EuclideanSpace ℂ ι) (γ : ℝ) (i : ι) :
    ampState g b γ i = (Real.sin γ : ℂ) * g i + (Real.cos γ : ℂ) * b i := by
  rw [ampState, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, WithLp.ofLp_smul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

omit [Fintype ι] in
/-- Truncating the plane state to `G` keeps exactly the good component. -/
lemma goodProj_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (γ : ℝ) :
    goodProj G (ampState g b γ) = (Real.sin γ : ℂ) • g := by
  ext i
  rw [goodProj_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ G
  · rw [if_pos hi, ampState_apply, hbsupp i hi, mul_zero, add_zero]
  · rw [if_neg hi, hgsupp i hi, mul_zero]

omit [Fintype ι] in
/-- **The oracle flip negates the angle**: `oracleFlip (ampState γ) = ampState (−γ)`. -/
lemma oracleFlip_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (γ : ℝ) :
    oracleFlip G (ampState g b γ) = ampState g b (-γ) := by
  rw [oracleFlip, goodProj_ampState hgsupp hbsupp, ampState, ampState,
    Real.sin_neg, Real.cos_neg]
  push_cast
  module

omit [DecidableEq ι] in
/-- The plane's inner-product law: `⟨ampState θ, ampState δ⟩ = cos (θ − δ)` for orthonormal
`g`, `b`. -/
lemma inner_ampState {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0) (θ δ : ℝ) :
    inner ℂ (ampState g b θ) (ampState g b δ) = (Real.cos (θ - δ) : ℂ) := by
  have hbg : inner ℂ b g = 0 := by
    rw [← inner_conj_symm, hgb, map_zero]
  rw [ampState, ampState]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hgg, hbb, hgb, hbg, Complex.conj_ofReal, mul_zero, mul_one]
  push_cast [Real.cos_sub]
  ring

/-! ### The two product-to-sum identities that make two reflections a rotation -/

lemma two_cos_sub_mul_sin (θ δ : ℝ) :
    2 * Real.cos (θ - δ) * Real.sin θ - Real.sin δ = Real.sin (2 * θ - δ) := by
  rw [show 2 * θ - δ = θ + (θ - δ) from by ring, Real.sin_add, Real.sin_sub, Real.cos_sub]
  linear_combination Real.sin δ * Real.sin_sq_add_cos_sq θ

lemma two_cos_sub_mul_cos (θ δ : ℝ) :
    2 * Real.cos (θ - δ) * Real.cos θ - Real.cos δ = Real.cos (2 * θ - δ) := by
  rw [show 2 * θ - δ = θ + (θ - δ) from by ring, Real.cos_add, Real.sin_sub, Real.cos_sub]
  linear_combination Real.cos δ * Real.sin_sq_add_cos_sq θ

omit [DecidableEq ι] in
/-- **Reflection about the `θ`-state reflects the plane angle**:
`reflect (ampState θ) (ampState δ) = ampState (2θ − δ)`. -/
lemma reflect_ampState {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0) (θ δ : ℝ) :
    reflect (ampState g b θ) (ampState g b δ) = ampState g b (2 * θ - δ) := by
  rw [reflect, inner_ampState hgg hbb hgb]
  rw [ampState, ampState, ampState, ← two_cos_sub_mul_sin θ δ, ← two_cos_sub_mul_cos θ δ]
  push_cast
  module

/-- ★ **The two-reflection rotation (the heart of BHMT):** one amplification step advances the
plane angle by `2θ`, where `θ` is the angle of the reflecting state `φ = ampState θ`. -/
theorem ampStep_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0)
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (θ γ : ℝ) :
    ampStep (ampState g b θ) G (ampState g b γ) = ampState g b (γ + 2 * θ) := by
  rw [ampStep, oracleFlip_ampState hgsupp hbsupp, reflect_ampState hgg hbb hgb θ (-γ),
    show 2 * θ - -γ = γ + 2 * θ from by ring]

/-- **The iterated rotation:** `j` amplification steps from the `θ`-state reach the
`(2j+1)θ`-state. -/
theorem ampStep_iterate {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0)
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (θ : ℝ) (j : ℕ) :
    (ampStep (ampState g b θ) G)^[j] (ampState g b θ)
      = ampState g b ((2 * j + 1) * θ) := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply,
      show ((2 * (0 : ℕ) + 1) : ℝ) * θ = θ from by push_cast; ring]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ampStep_ampState hgg hbb hgb hgsupp hbsupp]
    congr 1
    push_cast
    ring

omit [Fintype ι] [DecidableEq ι] in
/-- The plane state's success probability is `sin² γ` (the bad component vanishes on `G` and
the good component carries unit weight there). -/
lemma goodProb_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hbsupp : ∀ i ∈ G, b i = 0) (hgood : ∑ i ∈ G, ‖g i‖ ^ 2 = 1) (γ : ℝ) :
    goodProb G (ampState g b γ) = Real.sin γ ^ 2 := by
  rw [goodProb]
  have hterm : ∀ i ∈ G, ‖ampState g b γ i‖ ^ 2 = Real.sin γ ^ 2 * ‖g i‖ ^ 2 := by
    intro i hi
    rw [ampState_apply, hbsupp i hi, mul_zero, add_zero, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hgood, mul_one]

/-! ## The decomposition of a state into its good and bad unit components -/

/-- The **good unit component** of `ψ` against `G`. -/
noncomputable def goodUnit (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (Real.sqrt (goodProb G ψ) : ℂ)⁻¹ • goodProj G ψ

/-- The **bad unit component** of `ψ` against `G`. -/
noncomputable def badUnit (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (Real.sqrt (1 - goodProb G ψ) : ℂ)⁻¹ • (ψ - goodProj G ψ)

omit [Fintype ι] in
lemma goodUnit_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    goodUnit G ψ i = (Real.sqrt (goodProb G ψ) : ℂ)⁻¹ * (if i ∈ G then ψ i else 0) := by
  rw [goodUnit, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, goodProj_apply]

omit [Fintype ι] in
lemma badUnit_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    badUnit G ψ i = (Real.sqrt (1 - goodProb G ψ) : ℂ)⁻¹
      * (ψ i - (if i ∈ G then ψ i else 0)) := by
  rw [badUnit, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sub, Pi.sub_apply,
    goodProj_apply]

omit [Fintype ι] in
lemma goodUnit_supp (G : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    ∀ i ∉ G, goodUnit G ψ i = 0 := by
  intro i hi
  rw [goodUnit_apply, if_neg hi, mul_zero]

omit [Fintype ι] in
lemma badUnit_supp (G : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    ∀ i ∈ G, badUnit G ψ i = 0 := by
  intro i hi
  rw [badUnit_apply, if_pos hi, sub_self, mul_zero]

section Decomposition

variable {G : Finset ι} {ψ : EuclideanSpace ℂ ι}

omit [Fintype ι] [DecidableEq ι] in
private lemma sqrt_goodProb_ne (ha0 : 0 < goodProb G ψ) :
    ((Real.sqrt (goodProb G ψ) : ℝ) : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr ha0).ne'

omit [Fintype ι] [DecidableEq ι] in
private lemma sqrt_badProb_ne (ha1 : goodProb G ψ < 1) :
    ((Real.sqrt (1 - goodProb G ψ) : ℝ) : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr (by linarith)).ne'

omit [Fintype ι] in
/-- The good unit component carries unit weight on `G`. -/
lemma goodUnit_weight (ha0 : 0 < goodProb G ψ) :
    ∑ i ∈ G, ‖goodUnit G ψ i‖ ^ 2 = 1 := by
  have hterm : ∀ i ∈ G, ‖goodUnit G ψ i‖ ^ 2 = (goodProb G ψ)⁻¹ * ‖ψ i‖ ^ 2 := by
    intro i hi
    rw [goodUnit_apply, if_pos hi, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (goodProb_nonneg G ψ)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact inv_mul_cancel₀ ha0.ne'

/-- `⟨g, g⟩ = 1` for the good unit component. -/
lemma inner_goodUnit_self (ha0 : 0 < goodProb G ψ) :
    inner ℂ (goodUnit G ψ) (goodUnit G ψ) = 1 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', RCLike.conj_mul]
  norm_cast
  have hfull : ∑ i : ι, ‖goodUnit G ψ i‖ ^ 2 = ∑ i ∈ G, ‖goodUnit G ψ i‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => by
      rw [goodUnit_supp G ψ i hi, norm_zero]; norm_num)).symm
  rw [hfull, goodUnit_weight ha0]
  norm_num

/-- `⟨b, b⟩ = 1` for the bad unit component (unit `ψ`). -/
lemma inner_badUnit_self (hψ : ‖ψ‖ = 1) (ha1 : goodProb G ψ < 1) :
    inner ℂ (badUnit G ψ) (badUnit G ψ) = 1 := by
  have hane : (1 : ℝ) - goodProb G ψ ≠ 0 := by linarith
  have hoff : ∑ i ∈ Gᶜ, ‖ψ i‖ ^ 2 = 1 - goodProb G ψ := by
    have htot : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
      have h := normSq_eq_sum_prob ψ
      rw [hψ, one_pow] at h
      simpa [prob] using h.symm
    have hsplit := Finset.sum_add_sum_compl G (fun i => ‖ψ i‖ ^ 2)
    rw [htot] at hsplit
    rw [goodProb]
    linarith [hsplit]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', RCLike.conj_mul]
  norm_cast
  have hfull : ∑ i : ι, ‖badUnit G ψ i‖ ^ 2 = ∑ i ∈ Gᶜ, ‖badUnit G ψ i‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ Gᶜ) (fun i _ hi => by
      rw [badUnit_supp G ψ i (by simpa using hi), norm_zero]; norm_num)).symm
  have hterm : ∀ i ∈ Gᶜ, ‖badUnit G ψ i‖ ^ 2
      = (1 - goodProb G ψ)⁻¹ * ‖ψ i‖ ^ 2 := by
    intro i hi
    have hiG : i ∉ G := by simpa using hi
    rw [badUnit_apply, if_neg hiG, sub_zero, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - goodProb G ψ)]
  have hsum2 : ∑ i ∈ Gᶜ, ‖badUnit G ψ i‖ ^ 2
      = (1 - goodProb G ψ)⁻¹ * ∑ i ∈ Gᶜ, ‖ψ i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hfull, hsum2, hoff, inv_mul_cancel₀ hane]
  norm_num

/-- `⟨g, b⟩ = 0`: the components live on disjoint coordinates. -/
lemma inner_goodUnit_badUnit :
    inner ℂ (goodUnit G ψ) (badUnit G ψ) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ G
  · rw [RCLike.inner_apply', badUnit_supp G ψ i hi, mul_zero]
  · rw [RCLike.inner_apply', goodUnit_supp G ψ i hi, map_zero, zero_mul]

omit [Fintype ι] in
/-- **The decomposition:** `ψ = ampState (goodUnit) (badUnit) (arcsin √a)`. -/
lemma ampState_decomposition (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    ψ = ampState (goodUnit G ψ) (badUnit G ψ)
        (Real.arcsin (Real.sqrt (goodProb G ψ))) := by
  have hs1 : Real.sqrt (goodProb G ψ) ≤ 1 := by
    calc Real.sqrt (goodProb G ψ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha1.le
      _ = 1 := Real.sqrt_one
  have hsin : Real.sin (Real.arcsin (Real.sqrt (goodProb G ψ)))
      = Real.sqrt (goodProb G ψ) :=
    Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ) ≤ 0) (Real.sqrt_nonneg _)) hs1
  have hcos : Real.cos (Real.arcsin (Real.sqrt (goodProb G ψ)))
      = Real.sqrt (1 - goodProb G ψ) := by
    rw [Real.cos_arcsin, Real.sq_sqrt (goodProb_nonneg G ψ)]
  rw [ampState, hsin, hcos, goodUnit, badUnit, smul_smul, smul_smul,
    mul_inv_cancel₀ (sqrt_goodProb_ne ha0), mul_inv_cancel₀ (sqrt_badProb_ne ha1),
    one_smul, one_smul, add_sub_cancel]

/-! ## The headline -/

/-- ★★ **Amplitude amplification (BHMT), the closed form.** For a unit state `ψ` with success
probability `a = goodProb G ψ` strictly between `0` and `1`, `j` rounds of the amplification
step `ampStep ψ G` — reflect about `ψ` after flipping the good-coordinate signs — yield success
probability exactly `sin²((2j+1)·θ)`, `θ = arcsin √a`. Grover's algorithm and its `k`-marked
generalisation are instances (`Empirical/QM/Algorithms/Grover.lean`). -/
theorem amplitude_amplification (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) (j : ℕ) :
    goodProb G ((ampStep ψ G)^[j] ψ)
      = Real.sin ((2 * j + 1) * Real.arcsin (Real.sqrt (goodProb G ψ))) ^ 2 := by
  have hgg := inner_goodUnit_self (G := G) (ψ := ψ) ha0
  have hbb := inner_badUnit_self (G := G) (ψ := ψ) hψ ha1
  have hgb := inner_goodUnit_badUnit (G := G) (ψ := ψ)
  have hgs := goodUnit_supp G ψ
  have hbs := badUnit_supp G ψ
  have hdec := ampState_decomposition (G := G) (ψ := ψ) ha0 ha1
  calc goodProb G ((ampStep ψ G)^[j] ψ)
      = goodProb G ((ampStep (ampState (goodUnit G ψ) (badUnit G ψ)
            (Real.arcsin (Real.sqrt (goodProb G ψ)))) G)^[j]
          (ampState (goodUnit G ψ) (badUnit G ψ)
            (Real.arcsin (Real.sqrt (goodProb G ψ))))) := by rw [← hdec]
    _ = goodProb G (ampState (goodUnit G ψ) (badUnit G ψ)
          ((2 * j + 1) * Real.arcsin (Real.sqrt (goodProb G ψ)))) := by
        rw [ampStep_iterate hgg hbb hgb hgs hbs]
    _ = Real.sin ((2 * j + 1) * Real.arcsin (Real.sqrt (goodProb G ψ))) ^ 2 :=
        goodProb_ampState hbs (goodUnit_weight ha0) _

end Decomposition

/-! ## The optimal count and the quadratic speedup -/

section OptimalCount

variable {G : Finset ι} {ψ : EuclideanSpace ℂ ι}

/-- ★ **The `⌊π/(4θ)⌋` round count succeeds with probability at least `1 − a`.** The chosen
count lands the accumulated angle within `θ` of `π/2`, where the success probability is at
least `cos²θ = 1 − a`. This is the bound Grover analyses defer to "downstream arithmetic": here
it is a theorem about the closed form. -/
theorem amplitude_amplification_succeeds (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    1 - goodProb G ψ ≤ goodProb G
      ((ampStep ψ G)^[⌊Real.pi
          / (4 * Real.arcsin (Real.sqrt (goodProb G ψ)))⌋₊] ψ) := by
  set a := goodProb G ψ with ha
  set θ := Real.arcsin (Real.sqrt a) with hθdef
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0)
  have hθhalf : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin θ = Real.sqrt a := by
    rw [hθdef]
    exact Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg a))
      (by calc Real.sqrt a ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha1.le
            _ = 1 := Real.sqrt_one)
  set m := ⌊Real.pi / (4 * θ)⌋₊ with hm
  rw [amplitude_amplification G ψ hψ ha0 ha1 m]
  set x := (2 * (m : ℝ) + 1) * θ with hx
  -- the angle window: `π/2 − θ < x ≤ π/2 + θ`
  have hfl : (m : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
  have hfu : Real.pi / (4 * θ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hwin : |Real.pi / 2 - x| ≤ θ := by
    rw [abs_le]
    constructor
    · -- `x ≤ π/2 + θ` from `m ≤ π/(4θ)`
      have h1 : 2 * (m : ℝ) * θ ≤ Real.pi / 2 := by
        have := mul_le_mul_of_nonneg_right hfl (le_of_lt (by positivity : (0:ℝ) < 2 * θ))
        calc 2 * (m : ℝ) * θ = (m : ℝ) * (2 * θ) := by ring
          _ ≤ Real.pi / (4 * θ) * (2 * θ) := this
          _ = Real.pi / 2 := by field_simp; ring
      rw [hx]; nlinarith [h1]
    · -- `π/2 − θ < x` from `π/(4θ) < m + 1`
      have h2 : Real.pi / 2 < 2 * ((m : ℝ) + 1) * θ := by
        have := mul_lt_mul_of_pos_right hfu (by positivity : (0:ℝ) < 2 * θ)
        calc Real.pi / 2 = Real.pi / (4 * θ) * (2 * θ) := by field_simp; ring
          _ < ((m : ℝ) + 1) * (2 * θ) := this
          _ = 2 * ((m : ℝ) + 1) * θ := by ring
      rw [hx]; nlinarith [h2]
  -- `sin x ≥ cos θ` on the window
  have hsinx : Real.cos θ ≤ Real.sin x := by
    have h1 : Real.sin x = Real.cos (Real.pi / 2 - x) := (Real.cos_pi_div_two_sub x).symm
    have h2 : Real.cos (Real.pi / 2 - x) = Real.cos |Real.pi / 2 - x| :=
      (Real.cos_abs _).symm
    rw [h1, h2]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (le_trans hθhalf (by linarith [Real.pi_pos])) hwin
  -- conclude: `sin²x ≥ cos²θ = 1 − a`
  have hcossq : Real.cos θ ^ 2 = 1 - a := by
    rw [Real.cos_sq', hsin, Real.sq_sqrt ha0.le]
  have hcos0 : 0 ≤ Real.cos θ := by
    rw [hθdef]; exact Real.cos_arcsin_nonneg _
  calc 1 - a = Real.cos θ ^ 2 := hcossq.symm
    _ ≤ Real.sin x ^ 2 := by nlinarith [hsinx, hcos0]

omit [Fintype ι] [DecidableEq ι] in
/-- ★ **The quadratic speedup as an inequality:** the chosen round count is at most
`π/(4√a)`, since `√a = sin θ ≤ θ`. -/
theorem amplification_query_bound (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    (⌊Real.pi / (4 * Real.arcsin (Real.sqrt (goodProb G ψ)))⌋₊ : ℝ)
      ≤ Real.pi / (4 * Real.sqrt (goodProb G ψ)) := by
  set a := goodProb G ψ
  set θ := Real.arcsin (Real.sqrt a) with hθdef
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0)
  have hsin : Real.sin θ = Real.sqrt a := by
    rw [hθdef]
    exact Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg a))
      (by calc Real.sqrt a ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha1.le
            _ = 1 := Real.sqrt_one)
  have hle : Real.sqrt a ≤ θ := by
    rw [← hsin]
    exact Real.sin_le hθ0.le
  calc (⌊Real.pi / (4 * θ)⌋₊ : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
    _ ≤ Real.pi / (4 * Real.sqrt a) := by
        apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity)
        nlinarith [hle]

/-- **Non-vacuity at a closed instance:** at success probability exactly `1/4` a *single*
amplification round succeeds with certainty — `θ = π/6`, and `3θ = π/2`. -/
theorem amplification_quarter (hψ : ‖ψ‖ = 1) (ha : goodProb G ψ = 1 / 4) :
    goodProb G (ampStep ψ G ψ) = 1 := by
  have h := amplitude_amplification G ψ hψ (by rw [ha]; norm_num) (by rw [ha]; norm_num) 1
  rw [Function.iterate_one] at h
  rw [h, ha]
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  have harcsin : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [hsqrt, harcsin,
    show (2 * (1 : ℕ) + 1) * (Real.pi / 6) = Real.pi / 2 from by push_cast; ring,
    Real.sin_pi_div_two, one_pow]

end OptimalCount

/-! ## The eigenstructure of the amplification step (AA-5a)

On the rotation plane the step `Q = ampStep (ampState θ) G` is a rotation by `2θ`, so its
eigenvectors there are `g ± i·b` with eigenvalues `e^{±2iθ}` — the fact amplitude *estimation*
(BHMT Thm 12) feeds to phase estimation. This section delivers the eigenstructure and the
estimate's error algebra; the two-register kickback marginal is AA-5b
(`specs/amplitude-amplification-plan.md`). -/

section EigenStructure

omit [Fintype ι] in
lemma goodProj_add (G : Finset ι) (ψ χ : EuclideanSpace ℂ ι) :
    goodProj G (ψ + χ) = goodProj G ψ + goodProj G χ := by
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, goodProj_apply]
  split_ifs
  · rfl
  · norm_num

omit [Fintype ι] in
lemma goodProj_smul (G : Finset ι) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    goodProj G (c • ψ) = c • goodProj G ψ := by
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, goodProj_apply, smul_eq_mul]
  split_ifs
  · rfl
  · rw [mul_zero]

omit [Fintype ι] in
lemma oracleFlip_add (G : Finset ι) (ψ χ : EuclideanSpace ℂ ι) :
    oracleFlip G (ψ + χ) = oracleFlip G ψ + oracleFlip G χ := by
  rw [oracleFlip, oracleFlip, oracleFlip, goodProj_add]
  module

omit [Fintype ι] in
lemma oracleFlip_smul (G : Finset ι) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    oracleFlip G (c • ψ) = c • oracleFlip G ψ := by
  rw [oracleFlip, oracleFlip, goodProj_smul]
  module

omit [DecidableEq ι] in
lemma reflect_add (φ ψ χ : EuclideanSpace ℂ ι) :
    reflect φ (ψ + χ) = reflect φ ψ + reflect φ χ := by
  rw [reflect, reflect, reflect, inner_add_right]
  module

omit [DecidableEq ι] in
lemma reflect_smul (φ : EuclideanSpace ℂ ι) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    reflect φ (c • ψ) = c • reflect φ ψ := by
  rw [reflect, reflect, inner_smul_right]
  module

/-- **The amplification step is additive.** -/
lemma ampStep_add (φ : EuclideanSpace ℂ ι) (G : Finset ι) (ψ χ : EuclideanSpace ℂ ι) :
    ampStep φ G (ψ + χ) = ampStep φ G ψ + ampStep φ G χ := by
  rw [ampStep, ampStep, ampStep, oracleFlip_add, reflect_add]

/-- **The amplification step is `ℂ`-homogeneous.** -/
lemma ampStep_smul (φ : EuclideanSpace ℂ ι) (G : Finset ι) (c : ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    ampStep φ G (c • ψ) = c • ampStep φ G ψ := by
  rw [ampStep, ampStep, oracleFlip_smul, reflect_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma ampState_zero (g b : EuclideanSpace ℂ ι) : ampState g b 0 = b := by
  rw [ampState, Real.sin_zero, Real.cos_zero]
  push_cast
  module

omit [Fintype ι] [DecidableEq ι] in
lemma ampState_pi_div_two (g b : EuclideanSpace ℂ ι) :
    ampState g b (Real.pi / 2) = g := by
  rw [ampState, Real.sin_pi_div_two, Real.cos_pi_div_two]
  push_cast
  module

/-- `e^{ix} = cos x + (sin x)·i` with the real trigonometric functions, coerced. -/
lemma exp_ofReal_mul_I (x : ℝ) :
    Complex.exp ((x : ℝ) * Complex.I)
      = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The `e^{+2iθ}` eigenvector of the amplification step on the rotation plane: `g + i·b`. -/
noncomputable def eigenPlus (g b : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  g + Complex.I • b

/-- The `e^{−2iθ}` eigenvector: `g − i·b`. -/
noncomputable def eigenMinus (g b : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  g - Complex.I • b

omit [Fintype ι] [DecidableEq ι] in
/-- The eigenvectors recombine to the good component: `v₊ + v₋ = 2g`. -/
lemma eigenPlus_add_eigenMinus (g b : EuclideanSpace ℂ ι) :
    eigenPlus g b + eigenMinus g b = (2 : ℂ) • g := by
  rw [eigenPlus, eigenMinus]
  module

omit [Fintype ι] [DecidableEq ι] in
/-- The eigenvectors recombine to the bad component: `v₊ − v₋ = 2i·b`. -/
lemma eigenPlus_sub_eigenMinus (g b : EuclideanSpace ℂ ι) :
    eigenPlus g b - eigenMinus g b = (2 * Complex.I) • b := by
  rw [eigenPlus, eigenMinus]
  module

variable {G : Finset ι} {g b : EuclideanSpace ℂ ι}

private lemma ampStep_g (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G g = ampState g b (Real.pi / 2 + 2 * θ) := by
  have h := ampStep_ampState hgg hbb hgb hgsupp hbsupp θ (Real.pi / 2)
  rwa [ampState_pi_div_two] at h

private lemma ampStep_b (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G b = ampState g b (2 * θ) := by
  have h := ampStep_ampState hgg hbb hgb hgsupp hbsupp θ 0
  rw [ampState_zero] at h
  rwa [zero_add] at h

/-- ★ **The `+` eigenvector equation:** on the rotation plane the amplification step has
`g + i·b` as an eigenvector with eigenvalue `e^{2iθ}`. This is the spectral fact amplitude
estimation hands to phase estimation. -/
theorem ampStep_eigenPlus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G (eigenPlus g b)
      = Complex.exp ((2 * θ : ℝ) * Complex.I) • eigenPlus g b := by
  rw [eigenPlus, ampStep_add, ampStep_smul,
    ampStep_g hgg hbb hgb hgsupp hbsupp θ, ampStep_b hgg hbb hgb hgsupp hbsupp θ]
  have hsin : Real.sin (Real.pi / 2 + 2 * θ) = Real.cos (2 * θ) := by
    rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hcos : Real.cos (Real.pi / 2 + 2 * θ) = -Real.sin (2 * θ) := by
    rw [Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    ampState_apply, hsin, hcos, exp_ofReal_mul_I, Complex.ofReal_neg]
  linear_combination (-(Real.sin (2 * θ) : ℂ) * b i) * Complex.I_mul_I

/-- ★ **The `−` eigenvector equation:** `g − i·b` carries eigenvalue `e^{−2iθ}`. -/
theorem ampStep_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G (eigenMinus g b)
      = Complex.exp ((-(2 * θ) : ℝ) * Complex.I) • eigenMinus g b := by
  rw [eigenMinus, sub_eq_add_neg, ← neg_smul, ampStep_add, ampStep_smul,
    ampStep_g hgg hbb hgb hgsupp hbsupp θ, ampStep_b hgg hbb hgb hgsupp hbsupp θ]
  have hsin : Real.sin (Real.pi / 2 + 2 * θ) = Real.cos (2 * θ) := by
    rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hcos : Real.cos (Real.pi / 2 + 2 * θ) = -Real.sin (2 * θ) := by
    rw [Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  rw [show Complex.exp ((-(2 * θ) : ℝ) * Complex.I)
      = (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * Complex.I from by
    rw [exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]; ring]
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    ampState_apply, hsin, hcos, Complex.ofReal_neg]
  linear_combination (-(Real.sin (2 * θ) : ℂ) * b i) * Complex.I_mul_I

/-- **Iterated eigen-action:** `j` amplification steps scale the `+` eigenvector by
`e^{2ijθ}` — the phase a counting register would estimate. -/
theorem ampStep_iterate_eigenPlus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (j : ℕ) :
    (ampStep (ampState g b θ) G)^[j] (eigenPlus g b)
      = Complex.exp ((2 * j * θ : ℝ) * Complex.I) • eigenPlus g b := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply,
      show ((2 * (0 : ℕ) * θ : ℝ)) = 0 from by push_cast; ring, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ampStep_smul,
      ampStep_eigenPlus hgg hbb hgb hgsupp hbsupp θ, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- **Iterated eigen-action, `−` branch:** `j` steps scale the `−` eigenvector by
`e^{−2ijθ}`. -/
theorem ampStep_iterate_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (j : ℕ) :
    (ampStep (ampState g b θ) G)^[j] (eigenMinus g b)
      = Complex.exp ((-(2 * j * θ) : ℝ) * Complex.I) • eigenMinus g b := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply,
      show ((-(2 * (0 : ℕ) * θ) : ℝ)) = 0 from by push_cast; ring, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ampStep_smul,
      ampStep_eigenMinus hgg hbb hgb hgsupp hbsupp θ, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- The iterated amplification step is additive. -/
lemma ampStep_iterate_add (φ : EuclideanSpace ℂ ι) (G : Finset ι) (j : ℕ)
    (ψ χ : EuclideanSpace ℂ ι) :
    (ampStep φ G)^[j] (ψ + χ) = (ampStep φ G)^[j] ψ + (ampStep φ G)^[j] χ := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply,
      Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, ampStep_add]

/-- The iterated amplification step is `ℂ`-homogeneous. -/
lemma ampStep_iterate_smul (φ : EuclideanSpace ℂ ι) (G : Finset ι) (j : ℕ) (k : ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    (ampStep φ G)^[j] (k • ψ) = k • (ampStep φ G)^[j] ψ := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      ampStep_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- **The eigen-decomposition of the rotation-plane state:**
`ampState γ = (−i/2)e^{iγ}·v₊ + (i/2)e^{−iγ}·v₋` — branch weights `1/4·‖v₊‖² = 1/2` each. The
bridge from the amplification plane to the phase-estimation branches. -/
lemma ampState_eq_eigen (g b : EuclideanSpace ℂ ι) (γ : ℝ) :
    ampState g b γ
      = (-Complex.I / 2 * Complex.exp ((γ : ℝ) * Complex.I)) • eigenPlus g b
        + (Complex.I / 2 * Complex.exp ((-γ : ℝ) * Complex.I)) • eigenMinus g b := by
  rw [show Complex.exp ((-γ : ℝ) * Complex.I)
      = (Real.cos γ : ℂ) - (Real.sin γ : ℂ) * Complex.I from by
    rw [exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]; ring,
    exp_ofReal_mul_I]
  ext i
  simp only [eigenPlus, eigenMinus, ampState_apply, WithLp.ofLp_add, Pi.add_apply,
    WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  linear_combination ((Real.sin γ : ℂ) * g i + (Real.cos γ : ℂ) * b i) * Complex.I_mul_I

omit [DecidableEq ι] in
/-- The two eigenvectors are orthogonal. -/
lemma inner_eigenPlus_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    inner ℂ (eigenPlus g b) (eigenMinus g b) = 0 := by
  have hbg : inner ℂ b g = 0 := by rw [← inner_conj_symm, hgb, map_zero]
  simp only [eigenPlus, eigenMinus, inner_add_left, inner_sub_right, inner_smul_left,
    inner_smul_right, hgg, hbb, hgb, hbg, Complex.conj_I]
  linear_combination Complex.I_mul_I

omit [DecidableEq ι] in
/-- `‖v₊‖² = 2`. -/
lemma inner_eigenPlus_self (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    inner ℂ (eigenPlus g b) (eigenPlus g b) = 2 := by
  have hbg : inner ℂ b g = 0 := by rw [← inner_conj_symm, hgb, map_zero]
  simp only [eigenPlus, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hgg, hbb, hgb, hbg, Complex.conj_I]
  linear_combination (-1 : ℂ) * Complex.I_mul_I

omit [DecidableEq ι] in
/-- `‖v₋‖² = 2`. -/
lemma inner_eigenMinus_self (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    inner ℂ (eigenMinus g b) (eigenMinus g b) = 2 := by
  have hbg : inner ℂ b g = 0 := by rw [← inner_conj_symm, hgb, map_zero]
  simp only [eigenMinus, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hgg, hbb, hgb, hbg, Complex.conj_I]
  linear_combination (-1 : ℂ) * Complex.I_mul_I

omit [DecidableEq ι] in
/-- The coordinate-sum form of `‖v₊‖² = 2`. -/
lemma sum_sq_eigenPlus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    ∑ y, ‖eigenPlus g b y‖ ^ 2 = 2 := by
  have h : (inner ℂ (eigenPlus g b) (eigenPlus g b) : ℂ)
      = ((∑ y, ‖eigenPlus g b y‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply', RCLike.conj_mul]
    norm_cast
  have h2 := h.symm.trans (inner_eigenPlus_self hgg hbb hgb)
  exact_mod_cast h2

omit [DecidableEq ι] in
/-- The coordinate-sum form of `‖v₋‖² = 2`. -/
lemma sum_sq_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    ∑ y, ‖eigenMinus g b y‖ ^ 2 = 2 := by
  have h : (inner ℂ (eigenMinus g b) (eigenMinus g b) : ℂ)
      = ((∑ y, ‖eigenMinus g b y‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply', RCLike.conj_mul]
    norm_cast
  have h2 := h.symm.trans (inner_eigenMinus_self hgg hbb hgb)
  exact_mod_cast h2

end EigenStructure

/-! ## The estimate's error algebra (BHMT Lemma 7 shape) -/

omit [Fintype ι] [DecidableEq ι] in
/-- The `sin²` difference in product form: `sin²x − sin²y = sin(x+y)·sin(x−y)`. -/
lemma sin_sq_sub_sin_sq (x y : ℝ) :
    Real.sin x ^ 2 - Real.sin y ^ 2 = Real.sin (x + y) * Real.sin (x - y) := by
  rw [Real.sin_add, Real.sin_sub]
  linear_combination (-(Real.sin x ^ 2)) * Real.sin_sq_add_cos_sq y
    + (Real.sin y ^ 2) * Real.sin_sq_add_cos_sq x

omit [Fintype ι] [DecidableEq ι] in
/-- ★ **The `sin²` perturbation bound:**
`|sin²x − sin²y| ≤ |sin 2y|·|x−y| + |x−y|²` — the Lipschitz-plus-quadratic control that turns
a phase-estimate error into an amplitude-estimate error. -/
theorem abs_sin_sq_sub_sin_sq_le (x y : ℝ) :
    |Real.sin x ^ 2 - Real.sin y ^ 2| ≤ |Real.sin (2 * y)| * |x - y| + |x - y| ^ 2 := by
  rw [sin_sq_sub_sin_sq, abs_mul]
  have h1 : |Real.sin (x + y)| ≤ |Real.sin (2 * y)| + |x - y| := by
    have hlip := Real.abs_sin_sub_sin_le (x + y) (2 * y)
    rw [show x + y - 2 * y = x - y from by ring] at hlip
    have htri : |Real.sin (x + y)| - |Real.sin (2 * y)|
        ≤ |Real.sin (x + y) - Real.sin (2 * y)| := abs_sub_abs_le_abs_sub _ _
    linarith
  have h2 : |Real.sin (x - y)| ≤ |x - y| := Real.abs_sin_le_abs
  nlinarith [h1, h2, abs_nonneg (x - y), abs_nonneg (Real.sin (x + y))]

omit [Fintype ι] [DecidableEq ι] in
/-- ★ **The amplitude-estimation error bound (BHMT Lemma 7).** If the true amplitude is
`a = sin²θ` (with `cos θ = √(1−a)`) and the estimated angle `θ'` is within `ε` of `θ`, then
the estimated amplitude `sin²θ'` is within `2√(a(1−a))·ε + ε²` of `a`. With the
phase-estimation window `ε = π/T` this is the standard
`|ã − a| ≤ 2π√(a(1−a))/T + π²/T²`; instantiating it on the two-register kickback marginal is
AA-5b. -/
theorem amplitude_estimation_error {a : ℝ} (ha0 : 0 ≤ a)
    {θ θ' : ℝ} (hθ : Real.sin θ = Real.sqrt a) (hθc : Real.cos θ = Real.sqrt (1 - a))
    {ε : ℝ} (hδ : |θ' - θ| ≤ ε) :
    |Real.sin θ' ^ 2 - a| ≤ 2 * Real.sqrt (a * (1 - a)) * ε + ε ^ 2 := by
  have hsin2 : |Real.sin (2 * θ)| = 2 * Real.sqrt (a * (1 - a)) := by
    rw [Real.sin_two_mul, hθ, hθc, Real.sqrt_mul ha0,
      abs_of_nonneg (by positivity)]
    ring
  have ha' : Real.sin θ ^ 2 = a := by rw [hθ, Real.sq_sqrt ha0]
  have h := abs_sin_sq_sub_sin_sq_le θ' θ
  rw [ha', hsin2] at h
  have habs2 : |θ' - θ| ^ 2 ≤ ε ^ 2 := by nlinarith [abs_nonneg (θ' - θ)]
  have hmul : 2 * Real.sqrt (a * (1 - a)) * |θ' - θ|
      ≤ 2 * Real.sqrt (a * (1 - a)) * ε :=
    mul_le_mul_of_nonneg_left hδ (by positivity)
  linarith

/-! ## Unknown amplitude: the averaged rotation (QSearch engine, BHMT Lemma 2)

When `a` is unknown the optimal count `⌊π/(4θ)⌋` cannot be computed. BHMT's remedy: pick the
round count uniformly at random below a guess `M`. The average success probability has an
exact closed form — the odd-angle `sin²` sum telescopes — and once `M·sin 2θ ≥ 1` it is at
least `1/4`, independent of `a`. The exponential-doubling schedule built on this
(BHMT Thm 3) is algorithmic bookkeeping and not formalised. -/

omit [Fintype ι] [DecidableEq ι] in
/-- The double angle of the odd angle: `cos(2·(2m+1)θ) = 1 − 2 sin²((2m+1)θ)`. -/
lemma cos_two_mul_odd (t : ℝ) :
    Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
  rw [Real.cos_two_mul]
  linear_combination 2 * Real.sin_sq_add_cos_sq t

omit [Fintype ι] [DecidableEq ι] in
/-- **The telescoped average (product form, BHMT Lemma 2):**
`4 sin(2θ) · ∑_{m<M} sin²((2m+1)θ) = 2M sin(2θ) − sin(4Mθ)` — exactly, for every `θ`. The
`sin²` sum telescopes through `sin(2A+2θ) − sin(2A−2θ) = 2 cos(2A) sin(2θ)` at the odd
angles `A = (2m+1)θ`. -/
lemma sum_sin_sq_odd_mul (θ : ℝ) (M : ℕ) :
    4 * Real.sin (2 * θ) * ∑ m ∈ Finset.range M, Real.sin ((2 * m + 1) * θ) ^ 2
      = 2 * M * Real.sin (2 * θ) - Real.sin (4 * M * θ) := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have key : Real.sin (4 * ((k : ℝ) + 1) * θ) - Real.sin (4 * k * θ)
        = 2 * Real.sin (2 * θ) * (1 - 2 * Real.sin ((2 * k + 1) * θ) ^ 2) := by
      rw [show 4 * ((k : ℝ) + 1) * θ = 2 * ((2 * k + 1) * θ) + 2 * θ from by ring,
        show 4 * (k : ℝ) * θ = 2 * ((2 * k + 1) * θ) - 2 * θ from by ring,
        Real.sin_add, Real.sin_sub, cos_two_mul_odd ((2 * (k : ℝ) + 1) * θ)]
      ring
    push_cast
    linear_combination key

omit [Fintype ι] [DecidableEq ι] in
/-- **The quarter bound:** once the guess `M` satisfies `M·sin 2θ ≥ 1`, the average success
probability of a uniformly random round count below `M` is at least `1/4`
(the sum is at least `M/4`). -/
lemma sum_sin_sq_odd_ge (θ : ℝ) (M : ℕ) (hpos : 0 < Real.sin (2 * θ))
    (hM : 1 ≤ M * Real.sin (2 * θ)) :
    (M : ℝ) / 4 ≤ ∑ m ∈ Finset.range M, Real.sin ((2 * m + 1) * θ) ^ 2 := by
  have h := sum_sin_sq_odd_mul θ M
  have hb : Real.sin (4 * M * θ) ≤ 1 := Real.sin_le_one _
  nlinarith [h, hb, hM, hpos]

/-- ★ **The QSearch engine (BHMT Lemma 2 on the register):** for any unit state with unknown
success probability `0 < a < 1`, as soon as the guess `M` satisfies `M · 2√(a(1−a)) ≥ 1`, the
amplification rounds `0, …, M−1` have **total** success probability at least `M/4` — i.e., a
uniformly random round count below `M` succeeds with average probability `≥ 1/4`, with no
knowledge of `a`. This is the engine of BHMT's unknown-`a` search; the exponential-doubling
schedule wrapping it (their Thm 3) is not formalised. -/
theorem qsearch_average (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) (M : ℕ)
    (hM : 1 ≤ M * (2 * Real.sqrt (goodProb G ψ * (1 - goodProb G ψ)))) :
    (M : ℝ) / 4 ≤ ∑ m ∈ Finset.range M, goodProb G ((ampStep ψ G)^[m] ψ) := by
  set a := goodProb G ψ with ha
  set θ := Real.arcsin (Real.sqrt a) with hθdef
  have hterm : ∀ m : ℕ, goodProb G ((ampStep ψ G)^[m] ψ) = Real.sin ((2 * m + 1) * θ) ^ 2 :=
    fun m => amplitude_amplification G ψ hψ ha0 ha1 m
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  have hsqle : Real.sqrt a ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ha1.le
  have hsθ : Real.sin θ = Real.sqrt a :=
    Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg a)) hsqle
  have hcθ : Real.cos θ = Real.sqrt (1 - a) := by
    rw [hθdef, Real.cos_arcsin, Real.sq_sqrt ha0.le]
  have hs2 : Real.sin (2 * θ) = 2 * Real.sqrt (a * (1 - a)) := by
    rw [Real.sin_two_mul, hsθ, hcθ, Real.sqrt_mul ha0.le]
    ring
  have hpos : 0 < Real.sin (2 * θ) := by
    rw [hs2]
    have h1a : 0 < a * (1 - a) := mul_pos ha0 (by linarith)
    have := Real.sqrt_pos.mpr h1a
    linarith
  refine sum_sin_sq_odd_ge θ M hpos ?_
  rw [hs2]
  exact hM

end QuantumInfo
