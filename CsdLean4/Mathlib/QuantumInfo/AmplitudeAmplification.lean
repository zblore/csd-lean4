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
`goodProb = 1` nothing to amplify. The unknown-`a` QSearch schedule (BHMT Thm 3) and amplitude
*estimation* (BHMT Thm 12, which would consume `PhaseEstimation.lean`) are recorded in
`specs/amplitude-amplification-plan.md` (AA-5/AA-6) and not attempted here.
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

end QuantumInfo
