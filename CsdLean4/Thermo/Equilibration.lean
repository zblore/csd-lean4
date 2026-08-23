/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.ReducedSecondMoment
public import CsdLean4.Mathlib.Dynamics.CorrelationDecay
public import CsdLean4.Mathlib.Topology.Algebra.CompactRecurrence

/-!
# E4: equilibration of time-averaged reduced states, as a conditional theorem

The equilibration arc's fourth item (`specs/equilibration-arc-plan.md` E4). It spends the generic
engine `CsdLean4/Mathlib/Dynamics/CorrelationDecay.lean` on the observables E1 built.

## ⚠️ This is a conditional, and the antecedent is the whole content

Both theorems below have the shape

  *if* the flow preserves `μ_FS`, *and* its correlations for this observable decay with a
  summable envelope, *then* the time averages converge to the Fubini–Study average.

**Neither hypothesis is proved, exhibited, or claimed to hold for any Σ.** Nothing in the corpus
proves that any dynamics mixes, and nothing here changes that. What E4 buys is a *reformulation*:
equilibration stops being a dephasing story and becomes an ergodic-theoretic statement whose one
hypothesis is explicit, quantitative, and checkable in principle. Producing an actual witness for
the antecedent is E5's separate job, and until that exists these theorems are conditionals with
an unpopulated antecedent — which is exactly why the hypothesis is named in the signature rather
than folded into a definition.

## What is proved

* ★★ `blockPop_timeAverage_tendsto` — time-averaged **subsystem populations** converge in `L²` to
  `d_B/N` (`= 1/d_A`, the maximally-mixed value, by `fs_blockPop_mean`);
* ★★ `hsDeviationNormSq_timeAverage_tendsto` — the time-averaged **Hilbert–Schmidt deviation**
  `‖ρ_A − I_A/d_A‖₂²` converges in `L²` to the Lubkin–Page value `(d_A+d_B)/(N+1) − 1/d_A`
  that E1 computed (`fs_hsDeviationNormSq`). This is E4 composed with E1.

## ⚠️ And the antecedent is *empty* for unitary Σ-dynamics (E5/E6)

* ★★ `not_hasCorrelationDecay_blockPop_of_unitary` — for `d_A ≥ 2` and **any** unitary `U`, the
  antecedent is false along `p ↦ U • p`, for every summable envelope. A unitary generates a
  relatively compact group, so its correlations are almost periodic and cannot decay.
* ★ `not_hasCorrelationDecay_blockPop_of_periodic` — the same for any periodic `Φ`, unitary or not.

So the conditionals above are sound machinery whose hypothesis finite-dimensional unitary dynamics
cannot meet. **Read that as a limitation, not a refutation**: equilibration in this setting rests
on the typicality results (E1/E2), not on mixing. The engine itself is not vacuous —
`CsdLean4/Mathlib/Dynamics/CorrelationDecayWitness.lean` exhibits a genuine witness (the doubling
map on the circle), which is precisely a *non-atomic, non-unitary* system.

## ⚠️ Honest scope

* **Discrete time.** `Φ` is a single map and `Φ^[t]` its iterates; a continuous Σ-flow enters by
  sampling at a fixed timestep. The continuous-time statement is not proved — so a continuous
  unitary Σ-flow is covered only through its time-`τ` samples, which is what E6 rules out.
* **`L²` convergence**, from a second-moment bound. Almost-everywhere convergence is what
  pointwise Birkhoff would give and is not available (`MATHLIB-GAPS.md`).
* The flow is a hypothesis, not a construction: no Σ-dynamics is built here, and in particular
  the `D1` dynamics residue is untouched. `μ_FS`-preservation is likewise assumed, not derived.
* H-TENSOR is inherited from E1: the bipartition travels as the explicit `e` in every signature.

Reference: `specs/equilibration-arc-plan.md` (E4, and E5 for the non-vacuity requirement);
`MATHLIB-GAPS.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators

namespace CSD.Thermo

open CSD.LF4

variable {N dA dB : ℕ} [NeZero N]

/-- ★★ **Time-averaged subsystem populations equilibrate — conditionally.**

If `Φ` preserves the Fubini–Study measure and the population's correlations decay with a summable
envelope `ε`, then the Birkhoff averages of `(ρ_A)_{aa}` converge in `L²` to `d_B/N`, which
`fs_blockPop_mean` identifies as the maximally-mixed value `1/d_A`.

The correlation hypothesis is stated at **one lag**, which is the form a physical estimate
produces; `HasCorrelationDecay.of_measurePreserving` turns it into the two-index form the engine
consumes. -/
theorem blockPop_timeAverage_tendsto (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA)
    {Φ : CPN N → CPN N} {ε : ℕ → ℝ}
    (hΦ : MeasurePreserving Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    (hlag : ∀ u : ℕ,
      |(∫ p, blockPop e p a * blockPop e (Φ^[u] p) a ∂(fubiniStudyMeasure p₀))
        - (∫ q, blockPop e q a ∂(fubiniStudyMeasure p₀)) ^ 2| ≤ ε u)
    (hsum : Summable ε) :
    Filter.Tendsto
      (fun T : ℕ => ∫ p, (birkhoffAverage ℝ Φ (fun q => blockPop e q a) T p - (dB : ℝ) / N) ^ 2
        ∂(fubiniStudyMeasure p₀))
      Filter.atTop (nhds 0) := by
  have hf : Measurable (fun q : CPN N => blockPop e q a) := blockPop_measurable e a
  have hdec := MeasureTheory.HasCorrelationDecay.of_measurePreserving hΦ hf hlag
  have hmean : ∀ t : ℕ, ∫ p, blockPop e (Φ^[t] p) a ∂(fubiniStudyMeasure p₀)
      = ∫ q, blockPop e q a ∂(fubiniStudyMeasure p₀) := fun t =>
    MeasureTheory.integral_iterate_of_measurePreserving hΦ hf.aestronglyMeasurable t
  have h := MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq hΦ.measurable hf
    zero_le_one (fun p => abs_blockPop_le_one e p a) hmean hdec hsum
  rwa [fs_blockPop_mean p₀ e a] at h

/-- ★★ **E4 composed with E1.** Under the same two hypotheses, the time-averaged Hilbert–Schmidt
deviation of the reduced state from maximally mixed converges in `L²` to the Lubkin–Page value
`(d_A + d_B)/(N + 1) − 1/d_A` proved in `fs_hsDeviationNormSq`.

For a large environment that value is `O(1/d_A · d_A/d_B)`-small, so the conditional reads: a
`μ_FS`-preserving flow with decaying correlations spends almost all of its time with the
subsystem near maximally mixed. Again — *conditional*; see the header. -/
theorem hsDeviationNormSq_timeAverage_tendsto (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {Φ : CPN N → CPN N} {ε : ℕ → ℝ}
    (hΦ : MeasurePreserving Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    (hlag : ∀ u : ℕ,
      |(∫ p, hsDeviationNormSq e p * hsDeviationNormSq e (Φ^[u] p) ∂(fubiniStudyMeasure p₀))
        - (∫ q, hsDeviationNormSq e q ∂(fubiniStudyMeasure p₀)) ^ 2| ≤ ε u)
    (hsum : Summable ε) :
    Filter.Tendsto
      (fun T : ℕ => ∫ p, (birkhoffAverage ℝ Φ (fun q => hsDeviationNormSq e q) T p
          - (((dA : ℝ) + (dB : ℝ)) / ((N : ℝ) + 1) - ((dA : ℝ))⁻¹)) ^ 2
        ∂(fubiniStudyMeasure p₀))
      Filter.atTop (nhds 0) := by
  have hf : Measurable (fun q : CPN N => hsDeviationNormSq e q) := hsDeviationNormSq_measurable e
  have hC : (0 : ℝ) ≤ (dA : ℝ) ^ 2 * (1 + (dB : ℝ) ^ 2) := by positivity
  have hbd : ∀ p : CPN N, |hsDeviationNormSq e p| ≤ (dA : ℝ) ^ 2 * (1 + (dB : ℝ) ^ 2) := by
    intro p
    rw [abs_of_nonneg (hsDeviationNormSq_nonneg e p)]
    exact hsDeviationNormSq_le e p
  have hdec := MeasureTheory.HasCorrelationDecay.of_measurePreserving hΦ hf hlag
  have hmean : ∀ t : ℕ, ∫ p, hsDeviationNormSq e (Φ^[t] p) ∂(fubiniStudyMeasure p₀)
      = ∫ q, hsDeviationNormSq e q ∂(fubiniStudyMeasure p₀) := fun t =>
    MeasureTheory.integral_iterate_of_measurePreserving hΦ hf.aestronglyMeasurable t
  have h := MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq hΦ.measurable hf hC hbd
    hmean hdec hsum
  rwa [fs_hsDeviationNormSq p₀ e] at h

/-! ### ⚠️ E5's sharpness check: when the antecedent is *empty* -/

/-- The Q24 arithmetic both no-goes run on: for a **nontrivial** subsystem the population's
second moment does not equal the square of its mean. `fs_blockPop_sq` and `fs_blockPop_mean` give
`(d_B²+d_B)/(N(N+1))` and `d_B/N`, and those agree exactly when `N = d_B`, i.e. `d_A = 1`. -/
lemma blockPop_variance_ne (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA)
    (hdA : 2 ≤ dA) :
    ∫ p, blockPop e p a * blockPop e p a ∂(fubiniStudyMeasure p₀)
      ≠ (∫ q, blockPop e q a ∂(fubiniStudyMeasure p₀)) ^ 2 := by
  intro hvar
  have hsq : ∫ p, blockPop e p a * blockPop e p a ∂(fubiniStudyMeasure p₀)
      = ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) := by
    rw [integral_congr_ae (ae_of_all _ (fun p => (pow_two (blockPop e p a)).symm))]
    exact fs_blockPop_sq p₀ e a
  rw [hsq, fs_blockPop_mean p₀ e a] at hvar
  -- arithmetic: the two Q24 values agree only when `N = d_B`, i.e. `d_A = 1`
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNmul := card_eq_mul_of_tensorEquiv e
  have hdBn : dB ≠ 0 := by rintro rfl; exact hN0 (by simpa using hNmul)
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hdBne : (dB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdBn
  have hN1ne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hNR : (N : ℝ) = (dA : ℝ) * (dB : ℝ) := by exact_mod_cast hNmul
  have hcross : ((dB : ℝ) ^ 2 + (dB : ℝ)) * (N : ℝ) ^ 2
      = (dB : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) + 1)) := by
    have e1 : ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1))
        * ((N : ℝ) * ((N : ℝ) + 1)) * (N : ℝ) ^ 2
        = ((dB : ℝ) ^ 2 + (dB : ℝ)) * (N : ℝ) ^ 2 := by field_simp
    have e2 : ((dB : ℝ) / (N : ℝ)) ^ 2 * ((N : ℝ) * ((N : ℝ) + 1)) * (N : ℝ) ^ 2
        = (dB : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) + 1)) := by field_simp
    rw [← e1, ← e2, hvar]
  have hfac : (N : ℝ) * (dB : ℝ) * ((N : ℝ) - (dB : ℝ)) = 0 := by linear_combination hcross
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hNne h'
    · exact hdBne h'
  · have hNd : (N : ℝ) = (dB : ℝ) := by linarith [sub_eq_zero.mp h]
    have hdA1 : (dA : ℝ) = 1 := by
      have hmul : (dA : ℝ) * (dB : ℝ) = 1 * (dB : ℝ) := by rw [one_mul, ← hNR, hNd]
      exact mul_right_cancel₀ hdBne hmul
    have h2 : (2 : ℝ) ≤ (dA : ℝ) := by exact_mod_cast hdA
    linarith

/-- ⚠️ **No periodic flow satisfies E4's antecedent for a nontrivial subsystem.**

If `Φ^[k] = id` and `d_A ≥ 2`, then `HasCorrelationDecay` for the population observable is
**false** for every summable envelope. So `blockPop_timeAverage_tendsto`, applied to a periodic
Σ-flow, is a conditional whose antecedent cannot be met.

The proof is Q24 arithmetic against the periodic no-go. A periodic map forces `⟨x²⟩ = ⟨x⟩²`
(`HasCorrelationDecay.integral_mul_self_eq_of_periodic`), whereas `fs_blockPop_sq` and
`fs_blockPop_mean` give `⟨x²⟩ = (d_B²+d_B)/(N(N+1))` and `⟨x⟩ = d_B/N`. Those agree exactly when
`N = d_B`, i.e. when `d_A = 1` — no subsystem at all.

**Superseded in strength by `not_hasCorrelationDecay_blockPop_of_unitary`** (E6, below), which
drops the periodicity hypothesis entirely: *no* unitary flow satisfies the antecedent. This
periodic version is kept because it applies to any periodic `Φ`, not only to unitary ones. -/
theorem not_hasCorrelationDecay_blockPop_of_periodic
    (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) (hdA : 2 ≤ dA)
    {Φ : CPN N → CPN N} {ε : ℕ → ℝ} {k : ℕ} (hk : 0 < k) (hper : Φ^[k] = id)
    (hsum : Summable ε) :
    ¬ MeasureTheory.HasCorrelationDecay (fubiniStudyMeasure p₀) Φ
        (fun q => blockPop e q a) ε := fun hdec =>
  blockPop_variance_ne p₀ e a hdA (hdec.integral_mul_self_eq_of_periodic hk hper hsum)

/-! ### ★★ Q12-d route 2: the finite-horizon statement, which E6 does *not* reach -/

/-- ★★ **Equilibration at a finite horizon — and this one a unitary Σ-flow can have.**

If the population's correlations are within `ε` on lags *below `T`*, the time average at horizon
`T` sits within `(2/T) Σ_{u<T} ε u` of the maximally-mixed value. No summability, no limit.

**Why this matters.** `not_hasCorrelationDecay_blockPop_of_unitary` (E6) shows no unitary flow can
satisfy the *asymptotic* antecedent: its powers recur, so the correlations recur. That argument
needs the bound **at arbitrarily large lags** and says nothing over a bounded window. A unitary
flow on a large space can decorrelate for a very long time before recurring — which is what a
physical environment does — and this theorem is exactly the statement that survives.

So E4's conclusion is *not* lost for finite-dimensional unitary dynamics; what is lost is its
asymptotic form. `specs/q12-fibre-mechanism-scoping.md` records this as `Q12-d` route 2, the
recommended escape from `W1`.

⚠️ **Still conditional, and the antecedent is still not exhibited.** Nothing here shows any
particular Σ-flow has small `ε` on lags below `T`; that is a quantitative estimate about a specific
dynamics, and it remains open. What has changed is that the hypothesis is no longer *provably
unsatisfiable* — which is what E6 established for the asymptotic version. -/
theorem blockPop_timeAverage_le_of_finiteHorizon (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    (a : Fin dA) {Φ : CPN N → CPN N} {ε : ℕ → ℝ} {T : ℕ}
    (hΦ : MeasurePreserving Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    (hdec : MeasureTheory.HasCorrelationDecayUpTo (fubiniStudyMeasure p₀) Φ
      (fun q => blockPop e q a) ε T)
    (hT : 0 < T) :
    ∫ p, (birkhoffAverage ℝ Φ (fun q => blockPop e q a) T p - (dB : ℝ) / N) ^ 2
        ∂(fubiniStudyMeasure p₀)
      ≤ 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u := by
  have hf : Measurable (fun q : CPN N => blockPop e q a) := blockPop_measurable e a
  have hmean : ∀ t : ℕ, ∫ p, blockPop e (Φ^[t] p) a ∂(fubiniStudyMeasure p₀)
      = ∫ q, blockPop e q a ∂(fubiniStudyMeasure p₀) := fun t =>
    MeasureTheory.integral_iterate_of_measurePreserving hΦ hf.aestronglyMeasurable t
  have h := MeasureTheory.integral_birkhoffAverage_sub_sq_le_cesaro hΦ.measurable hf
    zero_le_one (fun p => abs_blockPop_le_one e p a) hmean hdec hT
  rwa [fs_blockPop_mean p₀ e a] at h

/-! ### E6: the analytic bridge to the general unitary no-go

The three lemmas below are generic (no CSD content) and are **extraction candidates** for
`Mathlib/QuantumInfo/`; they live here to keep the rebuild surface small while E6 is in progress.
-/

omit [NeZero N] in
lemma toEuclideanLin_comp (A B : Matrix (Fin N) (Fin N) ℂ) (v : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) = Matrix.toEuclideanLin (A * B) v := by
  ext k
  show (A *ᵥ (B *ᵥ (WithLp.ofLp v))) k = ((A * B) *ᵥ WithLp.ofLp v) k
  rw [Matrix.mulVec_mulVec]

omit [NeZero N] in
/-- **A unitary matrix acts as an isometry.** The general statement behind the per-gate
`signFlip_normSq` / `perm_normSq` / `hadamard_normSq` of `CanonicalTypicality`. -/
lemma norm_toEuclideanLin_unitary (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖Matrix.toEuclideanLin U.val v‖ = ‖v‖ := by
  have hUU : U.valᴴ * U.val = 1 := by
    have h := U.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    rwa [Matrix.star_eq_conjTranspose] at h
  have hinner : (inner ℂ (Matrix.toEuclideanLin U.val v) (Matrix.toEuclideanLin U.val v) : ℂ)
      = inner ℂ v v := by
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      toEuclideanLin_comp, hUU]
    congr 1
    ext k
    show ((1 : Matrix (Fin N) (Fin N) ℂ) *ᵥ WithLp.ofLp v) k = _
    rw [Matrix.one_mulVec]
  have hsq : ‖Matrix.toEuclideanLin U.val v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  have h1 : (0 : ℝ) ≤ ‖Matrix.toEuclideanLin U.val v‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

omit [NeZero N] in
lemma continuous_unitaryEntry (k j : Fin N) :
    Continuous (fun V : Matrix.unitaryGroup (Fin N) ℂ => V.val k j) :=
  continuous_subtype_val.matrix_elem k j

/-- **The deviation of a unitary from the identity**, measured entrywise in `ℓ¹`.

`ℓ¹` rather than `ℓ²` deliberately: it makes the uniform estimate below a triangle inequality
plus `coord_norm_le`, with no Cauchy–Schwarz and no square roots anywhere. -/
noncomputable def matDev (V : Matrix.unitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ k : Fin N, ∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖

omit [NeZero N] in
lemma matDev_nonneg (V : Matrix.unitaryGroup (Fin N) ℂ) : 0 ≤ matDev V :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

omit [NeZero N] in
lemma continuous_matDev : Continuous (matDev (N := N)) :=
  continuous_finsetSum _ (fun k _ => continuous_finsetSum _ (fun j _ =>
    ((continuous_unitaryEntry k j).sub continuous_const).norm))

omit [NeZero N] in
@[simp] lemma matDev_one : matDev (1 : Matrix.unitaryGroup (Fin N) ℂ) = 0 := by
  simp [matDev]

omit [NeZero N] in
lemma toEuclideanLin_entry (A : Matrix (Fin N) (Fin N) ℂ) (v : EuclideanSpace ℂ (Fin N))
    (k : Fin N) : (Matrix.toEuclideanLin A v) k = ∑ j : Fin N, A k j * v j :=
  Complex.ext rfl rfl

omit [NeZero N] in
/-- One coordinate of `(V - 1)ψ`, bounded by the `ℓ¹` deviation of that **row** times `‖ψ‖`.
Triangle inequality plus `coord_norm_le` — this is where the `ℓ¹` choice pays off. -/
lemma norm_sub_coord_le (V : Matrix.unitaryGroup (Fin N) ℂ) (v : EuclideanSpace ℂ (Fin N))
    (k : Fin N) :
    ‖(Matrix.toEuclideanLin V.val v) k - v k‖
      ≤ (∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖) * ‖v‖ := by
  have hv : v k = (Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) v) k := by
    rw [toEuclideanLin_entry]
    simp [Matrix.one_apply]
  rw [hv, toEuclideanLin_entry, toEuclideanLin_entry, ← Finset.sum_sub_distrib]
  calc ‖∑ j : Fin N, (V.val k j * v j - (1 : Matrix (Fin N) (Fin N) ℂ) k j * v j)‖
      ≤ ∑ j : Fin N, ‖V.val k j * v j - (1 : Matrix (Fin N) (Fin N) ℂ) k j * v j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖ * ‖v‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [← sub_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (coord_norm_le v j) (norm_nonneg _)
    _ = (∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖) * ‖v‖ := by
        rw [← Finset.sum_mul]

/-- **The uniform estimate, one coordinate.** The moment map moves by at most twice the `ℓ¹`
deviation of the acting unitary's row — *uniformly in the state*, which is what replaces the
unavailable dominated-convergence argument. -/
lemma abs_momentMap_smul_sub_le (V : Matrix.unitaryGroup (Fin N) ℂ) (p : CPN N) (k : Fin N) :
    |momentMap (V • p) k - momentMap p k|
      ≤ 2 * ∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖ := by
  have hψn : (0 : ℝ) < ‖p.rep‖ := norm_pos_iff.mpr p.rep_nonzero
  have hSnn : (0 : ℝ) ≤ ∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hw : momentMap (V • p) k
      = ‖(Matrix.toEuclideanLin V.val p.rep) k‖ ^ 2 / ‖p.rep‖ ^ 2 := by
    rw [smul_eq_mk, momentMap_mk, norm_toEuclideanLin_unitary]
  have hp : momentMap p k = ‖p.rep k‖ ^ 2 / ‖p.rep‖ ^ 2 := rfl
  have ha : ‖(Matrix.toEuclideanLin V.val p.rep) k‖ ≤ ‖p.rep‖ := by
    have h := coord_norm_le (Matrix.toEuclideanLin V.val p.rep) k
    rwa [norm_toEuclideanLin_unitary] at h
  have hb : ‖p.rep k‖ ≤ ‖p.rep‖ := coord_norm_le p.rep k
  have hd : |‖(Matrix.toEuclideanLin V.val p.rep) k‖ - ‖p.rep k‖|
      ≤ (∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖) * ‖p.rep‖ :=
    le_trans (abs_norm_sub_norm_le _ _) (norm_sub_coord_le V p.rep k)
  rw [hw, hp, div_sub_div_same, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p.rep‖ ^ 2), div_le_iff₀ (by positivity)]
  rw [abs_le] at hd ⊢
  constructor <;>
    nlinarith [hd.1, hd.2, ha, hb, norm_nonneg ((Matrix.toEuclideanLin V.val p.rep) k),
      norm_nonneg (p.rep k), hψn, hSnn]

omit [NeZero N] in
lemma blockPop_eq_sum (e : Fin N ≃ Fin dA × Fin dB) (q : CPN N) (a : Fin dA) :
    blockPop e q a = ∑ b : Fin dB, momentMap q (e.symm (a, b)) := rfl

/-- ★ **The uniform estimate for the population observable**: it moves by at most `2 · matDev V`,
*uniformly in the state*. Summing the coordinate estimate over the `a`-block and discarding the
other blocks (all terms nonnegative) turns the row sums into the full `matDev`. -/
lemma abs_blockPop_smul_sub_le (e : Fin N ≃ Fin dA × Fin dB)
    (V : Matrix.unitaryGroup (Fin N) ℂ) (p : CPN N) (a : Fin dA) :
    |blockPop e (V • p) a - blockPop e p a| ≤ 2 * matDev V := by
  have hrow : ∀ k : Fin N,
      (0 : ℝ) ≤ ∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖ :=
    fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hslice : ∑ b : Fin dB,
        ∑ j : Fin N, ‖V.val (e.symm (a, b)) j
          - (1 : Matrix (Fin N) (Fin N) ℂ) (e.symm (a, b)) j‖
      ≤ matDev V := by
    rw [matDev, ← Equiv.sum_comp e.symm
      (fun k => ∑ j : Fin N, ‖V.val k j - (1 : Matrix (Fin N) (Fin N) ℂ) k j‖),
      Fintype.sum_prod_type]
    exact Finset.single_le_sum
      (f := fun a' : Fin dA => ∑ b : Fin dB,
        ∑ j : Fin N, ‖V.val (e.symm (a', b)) j
          - (1 : Matrix (Fin N) (Fin N) ℂ) (e.symm (a', b)) j‖)
      (fun a' _ => Finset.sum_nonneg (fun b _ => hrow _)) (Finset.mem_univ a)
  calc |blockPop e (V • p) a - blockPop e p a|
      = |∑ b : Fin dB, (momentMap (V • p) (e.symm (a, b)) - momentMap p (e.symm (a, b)))| := by
        rw [blockPop_eq_sum, blockPop_eq_sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ b : Fin dB, |momentMap (V • p) (e.symm (a, b)) - momentMap p (e.symm (a, b))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Fin dB, 2 * ∑ j : Fin N, ‖V.val (e.symm (a, b)) j
          - (1 : Matrix (Fin N) (Fin N) ℂ) (e.symm (a, b)) j‖ :=
        Finset.sum_le_sum (fun b _ => abs_momentMap_smul_sub_le V p _)
    _ = 2 * ∑ b : Fin dB, ∑ j : Fin N, ‖V.val (e.symm (a, b)) j
          - (1 : Matrix (Fin N) (Fin N) ℂ) (e.symm (a, b)) j‖ := by rw [← Finset.mul_sum]
    _ ≤ 2 * matDev V := by linarith

/-- ★ **The correlation moves by at most `2 · matDev V`.** The uniform estimate integrates
directly — no dominated convergence, which is what `FirstCountableTopology`'s absence rules out. -/
lemma abs_corr_smul_sub_le (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA)
    (V : Matrix.unitaryGroup (Fin N) ℂ) :
    |(∫ p, blockPop e p a * blockPop e (V • p) a ∂(fubiniStudyMeasure p₀))
        - (∫ p, blockPop e p a * blockPop e p a ∂(fubiniStudyMeasure p₀))|
      ≤ 2 * matDev V := by
  have hmV : Measurable (fun p : CPN N => V • p) := (continuous_const_smul V).measurable
  have hf : Measurable (fun q : CPN N => blockPop e q a) := blockPop_measurable e a
  have hi1 : Integrable (fun p : CPN N => blockPop e p a * blockPop e (V • p) a)
      (fubiniStudyMeasure p₀) :=
    fs_integrable_mul p₀ hf (hf.comp hmV) (fun p => abs_blockPop_le_one e p a)
      (fun p => abs_blockPop_le_one e (V • p) a)
  have hi2 : Integrable (fun p : CPN N => blockPop e p a * blockPop e p a)
      (fubiniStudyMeasure p₀) :=
    fs_integrable_mul p₀ hf hf (fun p => abs_blockPop_le_one e p a)
      (fun p => abs_blockPop_le_one e p a)
  rw [← integral_sub hi1 hi2]
  have hpt : ∀ p : CPN N,
      ‖blockPop e p a * blockPop e (V • p) a - blockPop e p a * blockPop e p a‖
        ≤ 2 * matDev V := by
    intro p
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    calc |blockPop e p a| * |blockPop e (V • p) a - blockPop e p a|
        ≤ 1 * (2 * matDev V) :=
          mul_le_mul (abs_blockPop_le_one e p a) (abs_blockPop_smul_sub_le e V p a)
            (abs_nonneg _) zero_le_one
      _ = 2 * matDev V := one_mul _
  simpa using norm_integral_le_of_norm_le_const (μ := fubiniStudyMeasure p₀) (ae_of_all _ hpt)

omit [NeZero N] in
lemma smul_iterate (U : Matrix.unitaryGroup (Fin N) ℂ) (u : ℕ) (p : CPN N) :
    (fun q : CPN N => U • q)^[u] p = (U ^ u) • p := by
  induction u with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']

/-- ★★ **E6, the general no-go: no unitary flow satisfies E4's antecedent for a nontrivial
subsystem.** For `d_A ≥ 2` and any unitary `U`, `HasCorrelationDecay` for the population
observable along `p ↦ U • p` is **false** for every summable envelope.

This is the almost-periodicity obstruction in full, no longer restricted to the periodic case.
Three ingredients, each proved: `matDev` recurrence of the powers `U ^ n`
(`exists_le_pow_mem_of_compactSpace`, using that `Matrix.unitaryGroup` is a compact group), the
uniform transfer `abs_corr_smul_sub_le`, and the reduction of decay to recurrence
(`HasCorrelationDecay.integral_mul_self_eq_of_recurrent`). Q24's arithmetic
(`blockPop_variance_ne`) supplies the contradiction.

**Read it as a limitation, not a refutation.** E4's machinery is sound; what this says is that its
antecedent is not populated by finite-dimensional unitary Σ-dynamics, so equilibration in that
setting must rest on the typicality results (E1/E2) rather than on mixing. -/
theorem not_hasCorrelationDecay_blockPop_of_unitary
    (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) (hdA : 2 ≤ dA)
    (U : Matrix.unitaryGroup (Fin N) ℂ) {ε : ℕ → ℝ} (hsum : Summable ε) :
    ¬ MeasureTheory.HasCorrelationDecay (fubiniStudyMeasure p₀) (fun q : CPN N => U • q)
        (fun q => blockPop e q a) ε := by
  intro hdec
  refine blockPop_variance_ne p₀ e a hdA
    (hdec.integral_mul_self_eq_of_recurrent (fun δ hδ M => ?_) hsum)
  have hopen : IsOpen {V : Matrix.unitaryGroup (Fin N) ℂ | matDev V < δ / 2} :=
    isOpen_lt continuous_matDev continuous_const
  have hmem : (1 : Matrix.unitaryGroup (Fin N) ℂ) ∈ {V | matDev V < δ / 2} := by
    show matDev (1 : Matrix.unitaryGroup (Fin N) ℂ) < δ / 2
    rw [matDev_one]
    linarith
  obtain ⟨u, hMu, hu⟩ := exists_le_pow_mem_of_compactSpace U (hopen.mem_nhds hmem) M
  refine ⟨u, hMu, ?_⟩
  have hlt : matDev (U ^ u) < δ / 2 := hu
  have hcongr : ∫ x, blockPop e x a
        * blockPop e ((fun q : CPN N => U • q)^[u] x) a ∂(fubiniStudyMeasure p₀)
      = ∫ x, blockPop e x a * blockPop e ((U ^ u) • x) a ∂(fubiniStudyMeasure p₀) :=
    integral_congr_ae (ae_of_all _ (fun x => by
      dsimp only
      rw [smul_iterate U u x]))
  have hbound := abs_corr_smul_sub_le p₀ e a (U ^ u)
  rw [hcongr]
  linarith

end CSD.Thermo
