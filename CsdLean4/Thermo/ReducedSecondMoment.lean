/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.CanonicalTypicality

/-!
# E1: the Fubini–Study second moment of the reduced state

**Category:** conceptually 1-Mathlib (CSD-free quantum statistical mechanics), kept under
`CSD.Thermo` beside TH-1.

The equilibration arc's first item (`specs/equilibration-arc-plan.md` E1) — in the Q24 scoping
note's vocabulary, its gated bricks B4/B5. TH-1 proved the *first* moment (the mean reduced
state is `I_A/d_A`); Q24 proved the Fubini–Study *second* moments of the moment map by twirl
algebra. This module spends both on the reduced state itself.

## ⚠️ H-TENSOR — the bipartition is a hypothesis, never an inference

Every statement carries the bipartition as an **explicit argument**

  `e : Fin N ≃ Fin dA × Fin dB`

exactly as `canonical_typicality_expectation` does. It is deliberately *not* obtained from a
tensor-product API (`QuantumInfo.regTensorEquiv` would make that easy, and is the temptation
this note exists to block). Rationale: a silently-chosen factorisation is a structural posit
doing load-bearing work — a second `D1`. Which factorisation is meant is physics input, so it
belongs in the signature where a reader and a referee can see it.
*(TODO(author): confirm the intended `D4`/`G6` referent — in this repo those IDs name an audit
record and a root-repair item, so they are presumably paper-side.)*

## What is proved

With `x_i = momentMap p i` and `r_{ij} = rayDensity p i j`:

* `blockPop` — the subsystem populations `(ρ_A)_{aa} = Σ_b x_{e⁻¹(a,b)}`, a **linear** statistic
  in the moment map, so Q24's linear moments apply verbatim (`blockPop_eq_linear`);
* ★ `fs_blockPop_mean` — `E[(ρ_A)_{aa}] = d_B/N` (`= 1/d_A`), the first moment in moment-map
  form;
* ★ `fs_blockPop_sq` — `E[(ρ_A)_{aa}²] = (d_B² + d_B)/(N(N+1))`;
* `signFlip_smul_rayDensity_ne` — a sign flip leaves a density entry alone when it touches
  neither index (companion to `signFlip_smul_offdiag`);
* ★ `fs_redOff_cross_vanish` — the genuinely four-index expectations vanish: a coordinate
  occurring an odd number of times is killed by the sign flip. This is the novel ingredient;
  everything else here is Q24 specialised;
* ★★ `fs_redOff_normSq` — `E|(ρ_A)_{aa'}|² = d_B/(N(N+1))` for `a ≠ a'`: expanding the modulus
  of the sum, the `b = b'` terms are the landed cross moment and the `b ≠ b'` terms vanish.

And then the assembly those moments were for:

* `reducedMatrix` / `hsDeviation` / `hsDeviationNormSq` — the reduced state as a matrix, its
  deviation `ρ_A − I_A/d_A`, and the entrywise Hilbert–Schmidt norm squared of that deviation;
* ★ `fs_hsDeviation_diag_sq` and ★ `fs_hsDeviation_off_sq` — the two kinds of entry;
* ★★ `fs_hsDeviationNormSq` — **the Lubkin–Page purity average**
  `E‖ρ_A − I_A/d_A‖₂² = (d_A + d_B)/(N + 1) − 1/d_A`. The cardinality identity `N = d_A d_B`
  it needs is read off the bipartition itself (`card_eq_mul_of_tensorEquiv`), not assumed;
* ★ `fs_hsDeviation_typicality` — Markov on that second moment, i.e. the statement in the form
  "a Fubini–Study-typical ray has a near-maximally-mixed subsystem".

## ⚠️ Honest scope — what is NOT proved here

* The **trace-norm** form the brief asks for would follow by `‖·‖₁ ≤ √d_A ‖·‖₂`, which needs the
  matrix-norm API rather than these moment computations.
* The reduced state is written **entrywise in the ray-density vocabulary**, which is what makes
  Q24's twirl results apply directly. Identifying these entries with `Matrix.traceRight` of the
  projector (the `canonical_typicality_expectation` spelling) is index bookkeeping, not done
  here — so `hsDeviationNormSq` is *defined* as the sum of squared moduli of the entries of
  `ρ_A − I_A/d_A` rather than derived from a `Matrix` norm instance.
* The concentration here is **Markov on a quadratic functional**, which is weaker than
  `fs_chebyshev_concentration`. Chebyshev does apply, but to the *linear* statistics: each
  individual population `blockPop e · a` is one of Q24's `∑ λₖ xₖ` and gets the `O(1/N)` rate.
  Exponential (Lévy) rates remain out of reach — see `MATHLIB-GAPS.md`.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators ComplexConjugate

namespace CSD.Thermo

open CSD.LF4

variable {N dA dB : ℕ} [NeZero N]

/-! ### The reduced state's entries, in moment-map / ray-density vocabulary -/

/-- The block indicator: `1` on the wires of subsystem level `a`. -/
noncomputable def blockIndicator (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) (k : Fin N) : ℝ :=
  if (e k).1 = a then 1 else 0

/-- **The subsystem population** `(ρ_A)_{aa}`: the total moment-map weight of the `a`-block. -/
noncomputable def blockPop (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) : ℝ :=
  ∑ b : Fin dB, momentMap p (e.symm (a, b))

/-- **The off-diagonal entry** `(ρ_A)_{aa'}` of the reduced state. -/
noncomputable def redOff (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a a' : Fin dA) : ℂ :=
  ∑ b : Fin dB, rayDensity p (e.symm (a, b)) (e.symm (a', b))

omit [NeZero N] in
/-- The population is the linear statistic of the block indicator — the bridge that lets Q24's
linear moment theorems apply unchanged. -/
lemma blockPop_eq_linear (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    blockPop e p a = ∑ k : Fin N, blockIndicator e a k * momentMap p k := by
  classical
  rw [blockPop, ← Equiv.sum_comp e.symm (fun k => blockIndicator e a k * momentMap p k),
    Fintype.sum_prod_type]
  symm
  calc (∑ a' : Fin dA, ∑ b : Fin dB,
          blockIndicator e a (e.symm (a', b)) * momentMap p (e.symm (a', b)))
      = ∑ b : Fin dB, blockIndicator e a (e.symm (a, b)) * momentMap p (e.symm (a, b)) :=
        Finset.sum_eq_single a
          (fun a' _ ha' => Finset.sum_eq_zero (fun b _ => by
            simp only [blockIndicator, Equiv.apply_symm_apply, if_neg ha', zero_mul]))
          (fun h => absurd (Finset.mem_univ a) h)
    _ = ∑ b : Fin dB, momentMap p (e.symm (a, b)) :=
        Finset.sum_congr rfl (fun b _ => by
          simp only [blockIndicator, Equiv.apply_symm_apply, if_pos, one_mul])

/-! ### The block indicator's own sums -/

omit [NeZero N] in
lemma sum_blockIndicator (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∑ k : Fin N, blockIndicator e a k = (dB : ℝ) := by
  classical
  rw [← Equiv.sum_comp e.symm (fun k => blockIndicator e a k), Fintype.sum_prod_type]
  calc (∑ a' : Fin dA, ∑ b : Fin dB, blockIndicator e a (e.symm (a', b)))
      = ∑ b : Fin dB, blockIndicator e a (e.symm (a, b)) :=
        Finset.sum_eq_single a
          (fun a' _ ha' => Finset.sum_eq_zero (fun b _ => by
            simp only [blockIndicator, Equiv.apply_symm_apply, if_neg ha']))
          (fun h => absurd (Finset.mem_univ a) h)
    _ = ∑ _b : Fin dB, (1 : ℝ) :=
        Finset.sum_congr rfl (fun b _ => by
          simp only [blockIndicator, Equiv.apply_symm_apply, if_pos])
    _ = (dB : ℝ) := by simp

omit [NeZero N] in
lemma sum_blockIndicator_sq (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∑ k : Fin N, blockIndicator e a k ^ 2 = (dB : ℝ) := by
  rw [← sum_blockIndicator e a]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [blockIndicator]
  split_ifs <;> norm_num

/-! ### ★ The population's first and second moments (Q24's linear moments, specialised) -/

/-- ★ **The mean subsystem population is `d_B/N`** (that is, `1/d_A`) — the first moment. -/
theorem fs_blockPop_mean (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∫ p, blockPop e p a ∂(fubiniStudyMeasure p₀) = (dB : ℝ) / N := by
  have h : (fun p : CPN N => blockPop e p a)
      = fun p => ∑ k : Fin N, blockIndicator e a k * momentMap p k :=
    funext (fun p => blockPop_eq_linear e p a)
  rw [h, fs_linear_expectation p₀ (blockIndicator e a), sum_blockIndicator]

/-- ★ **The population's second moment**: `(d_B² + d_B)/(N(N+1))`. -/
theorem fs_blockPop_sq (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∫ p, (blockPop e p a) ^ 2 ∂(fubiniStudyMeasure p₀)
      = ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have h : (fun p : CPN N => (blockPop e p a) ^ 2)
      = fun p => (∑ k : Fin N, blockIndicator e a k * momentMap p k) ^ 2 :=
    funext (fun p => by rw [blockPop_eq_linear e p a])
  rw [h, fs_linear_sq_moment p₀ (blockIndicator e a), sum_blockIndicator,
    sum_blockIndicator_sq]

/-! ### The sign flip away from both indices -/

/-- **A sign flip that touches neither index leaves the density entry alone.** The companion of
`signFlip_smul_offdiag` (which handles the case where the flipped coordinate *is* one of the
indices), and the engine behind the four-index vanishing below. -/
lemma signFlip_smul_rayDensity_ne (k i j : Fin N) (hik : i ≠ k) (hjk : j ≠ k) (p : CPN N) :
    rayDensity ((signFlip k) • p) i j = rayDensity p i j := by
  rw [smul_eq_mk, rayDensity_mk, signFlip_val, toEuclideanLin_signFlip_coord,
    toEuclideanLin_signFlip_coord, if_neg hik, if_neg hjk, one_mul, one_mul]
  have hden : (‖(Matrix.toEuclideanLin (signFlipMat k) p.rep)‖ : ℂ) ^ 2
      = (‖p.rep‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, signFlip_normSq, Complex.ofReal_pow]
  rw [hden]
  rfl

/-! ### ★★ The off-diagonal second moment -/

/-- ★ **The four-index expectations vanish.** For `a ≠ a'` and `b ≠ b'`, the coordinate
`e⁻¹(a,b)` occurs an odd number of times in the product, so the sign flip there negates the
integrand and the integral is its own negative. -/
theorem fs_redOff_cross_vanish (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {a a' : Fin dA} (haa : a ≠ a') {b b' : Fin dB} (hbb : b ≠ b') :
    ∫ p, ((rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
          + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im)
      ∂(fubiniStudyMeasure p₀) = 0 := by
  have hjk : e.symm (a', b) ≠ e.symm (a, b) :=
    fun h => haa (congrArg Prod.fst (e.symm.injective h)).symm
  have hi'k : e.symm (a, b') ≠ e.symm (a, b) :=
    fun h => hbb (congrArg Prod.snd (e.symm.injective h)).symm
  have hj'k : e.symm (a', b') ≠ e.symm (a, b) :=
    fun h => haa (congrArg Prod.fst (e.symm.injective h)).symm
  have hmeas : Measurable (fun p : CPN N =>
      (rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
          * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
        + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
          * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im) := by
    refine Measurable.add ?_ ?_
    · exact ((Complex.measurable_re.comp (rayDensity_measurable _ _)).mul
        (Complex.measurable_re.comp (rayDensity_measurable _ _)))
    · exact ((Complex.measurable_im.comp (rayDensity_measurable _ _)).mul
        (Complex.measurable_im.comp (rayDensity_measurable _ _)))
  have h := fs_integral_unitary p₀ (signFlip (e.symm (a, b))) hmeas
  rw [integral_congr_ae (ae_of_all _ (fun p : CPN N => by
      rw [signFlip_smul_offdiag _ _ hjk,
        signFlip_smul_rayDensity_ne _ _ _ hi'k hj'k,
        Complex.neg_re, Complex.neg_im]
      ring :
    ∀ p : CPN N,
      (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b)) (e.symm (a', b))).re
          * (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b')) (e.symm (a', b'))).re
        + (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b)) (e.symm (a', b))).im
          * (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b')) (e.symm (a', b'))).im
      = -((rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
          + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im))),
    integral_neg] at h
  linarith

/-! ### ★★ The off-diagonal second moment -/

/-- The `b`-th summand of an off-diagonal reduced entry, named so the expansion below stays
readable. -/
noncomputable def redTerm (e : Fin N ≃ Fin dA × Fin dB) (a a' : Fin dA) (b : Fin dB)
    (p : CPN N) : ℂ :=
  rayDensity p (e.symm (a, b)) (e.symm (a', b))

omit [NeZero N] in
lemma redOff_eq_sum (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a a' : Fin dA) :
    redOff e p a a' = ∑ b : Fin dB, redTerm e a a' b p := rfl

omit [NeZero N] in
/-- The `b = b'` term of the expansion is a product of two moment-map coordinates. -/
lemma redTerm_self (e : Fin N ≃ Fin dA × Fin dB) (a a' : Fin dA) (b : Fin dB) (p : CPN N) :
    (redTerm e a a' b p).re * (redTerm e a a' b p).re
        + (redTerm e a a' b p).im * (redTerm e a a' b p).im
      = momentMap p (e.symm (a, b)) * momentMap p (e.symm (a', b)) := by
  rw [← pow_two, ← pow_two]
  exact rayDensity_re_sq_add_im_sq p _ _

omit [NeZero N] in
lemma redTerm_measurable (e : Fin N ≃ Fin dA × Fin dB) (a a' : Fin dA) (b : Fin dB) :
    Measurable (redTerm e a a' b) := rayDensity_measurable _ _

/-- ★★ **The off-diagonal entries' second moment**: `E|(ρ_A)_{aa'}|² = d_B/(N(N+1))` for
`a ≠ a'`. The `b = b'` terms contribute the landed cross moment `E[x_i x_j]`; the `b ≠ b'`
terms vanish by `fs_redOff_cross_vanish`. -/
theorem fs_redOff_normSq (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {a a' : Fin dA} (haa : a ≠ a') :
    ∫ p, Complex.normSq (redOff e p a a') ∂(fubiniStudyMeasure p₀)
      = (dB : ℝ) / ((N : ℝ) * ((N : ℝ) + 1)) := by
  classical
  have hexp : ∀ p : CPN N, Complex.normSq (redOff e p a a')
      = ∑ b : Fin dB, ∑ b' : Fin dB,
          ((redTerm e a a' b p).re * (redTerm e a a' b' p).re
            + (redTerm e a a' b p).im * (redTerm e a a' b' p).im) := by
    intro p
    rw [Complex.normSq_apply, redOff_eq_sum, Complex.re_sum, Complex.im_sum,
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => (Finset.sum_add_distrib).symm)
  have hmeas : ∀ b b' : Fin dB, Measurable (fun p : CPN N =>
      (redTerm e a a' b p).re * (redTerm e a a' b' p).re
        + (redTerm e a a' b p).im * (redTerm e a a' b' p).im) := by
    intro b b'
    exact ((Complex.measurable_re.comp (redTerm_measurable e a a' b)).mul
        (Complex.measurable_re.comp (redTerm_measurable e a a' b'))).add
      ((Complex.measurable_im.comp (redTerm_measurable e a a' b)).mul
        (Complex.measurable_im.comp (redTerm_measurable e a a' b')))
  have hint : ∀ b b' : Fin dB, Integrable (fun p : CPN N =>
      (redTerm e a a' b p).re * (redTerm e a a' b' p).re
        + (redTerm e a a' b p).im * (redTerm e a a' b' p).im)
      (fubiniStudyMeasure p₀) := by
    intro b b'
    refine Integrable.of_bound (hmeas b b').aestronglyMeasurable 2
      (ae_of_all _ (fun p => ?_))
    have h1 := abs_re_rayDensity_le_one p (e.symm (a, b)) (e.symm (a', b))
    have h2 := abs_re_rayDensity_le_one p (e.symm (a, b')) (e.symm (a', b'))
    have h3 := abs_im_rayDensity_le_one p (e.symm (a, b)) (e.symm (a', b))
    have h4 := abs_im_rayDensity_le_one p (e.symm (a, b')) (e.symm (a', b'))
    have hb1 := abs_le.mp (show |(redTerm e a a' b p).re * (redTerm e a a' b' p).re| ≤ 1 by
      rw [abs_mul]; exact mul_le_one₀ h1 (abs_nonneg _) h2)
    have hb2 := abs_le.mp (show |(redTerm e a a' b p).im * (redTerm e a a' b' p).im| ≤ 1 by
      rw [abs_mul]; exact mul_le_one₀ h3 (abs_nonneg _) h4)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  have hdiag : ∀ b : Fin dB, ∫ p,
      ((redTerm e a a' b p).re * (redTerm e a a' b p).re
        + (redTerm e a a' b p).im * (redTerm e a a' b p).im)
      ∂(fubiniStudyMeasure p₀) = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
    intro b
    have hne : e.symm (a, b) ≠ e.symm (a', b) :=
      fun h => haa (congrArg Prod.fst (e.symm.injective h))
    rw [integral_congr_ae (ae_of_all _ (fun p => redTerm_self e a a' b p))]
    exact fs_x_cross_moment p₀ hne
  have hoff : ∀ b b' : Fin dB, b ≠ b' → ∫ p,
      ((redTerm e a a' b p).re * (redTerm e a a' b' p).re
        + (redTerm e a a' b p).im * (redTerm e a a' b' p).im)
      ∂(fubiniStudyMeasure p₀) = 0 :=
    fun b b' hbb => fs_redOff_cross_vanish p₀ e haa hbb
  rw [integral_congr_ae (ae_of_all _ hexp),
    integral_finsetSum Finset.univ
      (fun b _ => integrable_finsetSum Finset.univ (fun b' _ => hint b b'))]
  have hrow : ∀ b : Fin dB, ∫ p, (∑ b' : Fin dB,
      ((redTerm e a a' b p).re * (redTerm e a a' b' p).re
        + (redTerm e a a' b p).im * (redTerm e a a' b' p).im))
      ∂(fubiniStudyMeasure p₀) = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
    intro b
    rw [integral_finsetSum Finset.univ (fun b' _ => hint b b'),
      Finset.sum_eq_single b
        (fun b' _ hb' => hoff b b' (Ne.symm hb'))
        (fun h => absurd (Finset.mem_univ b) h)]
    exact hdiag b
  rw [Finset.sum_congr rfl (fun b _ => hrow b), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### The reduced state as a matrix, and its deviation from maximal mixing -/

/-- **The reduced density matrix** of a ray, entrywise in the ray-density vocabulary:
`(ρ_A)_{aa'} = Σ_b r_{(a,b),(a',b)}`. (Still entrywise — identifying this with
`Matrix.traceRight` of the projector is the bookkeeping the header declares out of scope.) -/
noncomputable def reducedMatrix (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) :
    Matrix (Fin dA) (Fin dA) ℂ :=
  Matrix.of fun a a' => redOff e p a a'

omit [NeZero N] in
@[simp] lemma reducedMatrix_apply (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a a' : Fin dA) :
    reducedMatrix e p a a' = redOff e p a a' := rfl

omit [NeZero N] in
/-- **The diagonal of the reduced matrix is the subsystem population** — the bridge between
the two vocabularies of this file (`rayDensity_diag` under the `b`-sum). -/
lemma redOff_diag (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    redOff e p a a = ((blockPop e p a : ℝ) : ℂ) := by
  rw [redOff, blockPop]
  push_cast
  exact Finset.sum_congr rfl (fun b _ => rayDensity_diag p _)

/-- **The deviation from the maximally mixed state**, `ρ_A − I_A/d_A`. -/
noncomputable def hsDeviation (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) :
    Matrix (Fin dA) (Fin dA) ℂ :=
  reducedMatrix e p - ((dA : ℂ))⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ)

omit [NeZero N] in
/-- On the diagonal the deviation is real: the population minus `1/d_A`. -/
lemma hsDeviation_diag (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    hsDeviation e p a a = ((blockPop e p a - ((dA : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [hsDeviation, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    reducedMatrix_apply, redOff_diag, smul_eq_mul, mul_one]
  push_cast
  ring

omit [NeZero N] in
/-- Off the diagonal, subtracting a multiple of the identity changes nothing. -/
lemma hsDeviation_off (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) {a a' : Fin dA}
    (haa : a ≠ a') : hsDeviation e p a a' = redOff e p a a' := by
  rw [hsDeviation, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne haa,
    reducedMatrix_apply, smul_zero, sub_zero]

/-- **The Hilbert–Schmidt norm squared of the deviation**, `‖ρ_A − I_A/d_A‖₂²`, written
entrywise as the sum of squared moduli of the entries. -/
noncomputable def hsDeviationNormSq (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) : ℝ :=
  ∑ a : Fin dA, ∑ a' : Fin dA, Complex.normSq (hsDeviation e p a a')

/-! ### Analytic plumbing for the population -/

omit [NeZero N] in
lemma blockPop_measurable (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    Measurable (fun p : CPN N => blockPop e p a) :=
  Finset.measurable_sum Finset.univ (fun b _ => momentMap_measurable (e.symm (a, b)))

omit [NeZero N] in
lemma blockPop_nonneg (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    0 ≤ blockPop e p a :=
  Finset.sum_nonneg (fun _b _ => momentMap_nonneg p _)

omit [NeZero N] in
/-- A subsystem population is at most one: it is a sub-sum of the moment map's simplex sum. -/
lemma blockPop_le_one (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    blockPop e p a ≤ 1 := by
  classical
  rw [blockPop_eq_linear, ← momentMap_sum_eq_one p]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [blockIndicator]
  split_ifs
  · rw [one_mul]
  · rw [zero_mul]
    exact momentMap_nonneg p k

omit [NeZero N] in
lemma abs_blockPop_le_one (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    |blockPop e p a| ≤ 1 :=
  abs_le.mpr ⟨by linarith [blockPop_nonneg e p a], blockPop_le_one e p a⟩

omit [NeZero N] in
lemma blockPop_integrable (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    Integrable (fun p : CPN N => blockPop e p a) (fubiniStudyMeasure p₀) :=
  Integrable.of_bound (blockPop_measurable e a).aestronglyMeasurable 1
    (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs]
      exact abs_blockPop_le_one e p a))

omit [NeZero N] in
lemma blockPop_sq_integrable (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    Integrable (fun p : CPN N => (blockPop e p a) ^ 2) (fubiniStudyMeasure p₀) :=
  (fs_integrable_mul p₀ (blockPop_measurable e a) (blockPop_measurable e a)
      (fun p => abs_blockPop_le_one e p a) (fun p => abs_blockPop_le_one e p a)).congr
    (Filter.Eventually.of_forall (fun _p => (pow_two _).symm))

omit [NeZero N] in
/-- The bipartition's cardinality identity, read off the equivalence itself: `N = d_A · d_B`.
Part of H-TENSOR's point — the factorisation is carried by `e`, so its arithmetic is too. -/
lemma card_eq_mul_of_tensorEquiv (e : Fin N ≃ Fin dA × Fin dB) : N = dA * dB := by
  simpa using Fintype.card_congr e

/-! ### ★ The diagonal contribution -/

/-- ★ **The diagonal deviation's second moment**:
`E[((ρ_A)_{aa} − 1/d_A)²] = (d_B² + d_B)/(N(N+1)) − 1/d_A²`.

The mean population is *exactly* `1/d_A` (that is what `d_B/N = 1/d_A` says once `N = d_A d_B`
is read off the bipartition), so the cross term collapses against the constant and only one
subtraction survives. -/
theorem fs_hsDeviation_diag_sq (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∫ p, Complex.normSq (hsDeviation e p a a) ∂(fubiniStudyMeasure p₀)
      = ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) - ((dA : ℝ))⁻¹ ^ 2 := by
  have hNmul := card_eq_mul_of_tensorEquiv e
  have hN0 : N ≠ 0 := NeZero.ne N
  have hdA0 : (dA : ℝ) ≠ 0 := by
    have h : dA ≠ 0 := by rintro rfl; exact hN0 (by simpa using hNmul)
    exact_mod_cast h
  have hdB0 : (dB : ℝ) ≠ 0 := by
    have h : dB ≠ 0 := by rintro rfl; exact hN0 (by simpa using hNmul)
    exact_mod_cast h
  have hNR : (N : ℝ) = (dA : ℝ) * (dB : ℝ) := by exact_mod_cast hNmul
  have hmean : (dB : ℝ) / (N : ℝ) = ((dA : ℝ))⁻¹ := by
    rw [hNR]; field_simp
  have hconst : ∫ _p : CPN N, (((dA : ℝ))⁻¹ ^ 2) ∂(fubiniStudyMeasure p₀)
      = ((dA : ℝ))⁻¹ ^ 2 := by simp
  have hI1 : Integrable (fun p : CPN N => (blockPop e p a) ^ 2) (fubiniStudyMeasure p₀) :=
    blockPop_sq_integrable p₀ e a
  have hI2 : Integrable (fun p : CPN N => (-(2 * ((dA : ℝ))⁻¹)) * blockPop e p a)
      (fubiniStudyMeasure p₀) := (blockPop_integrable p₀ e a).const_mul _
  have hI3 : Integrable (fun p : CPN N =>
        (-(2 * ((dA : ℝ))⁻¹)) * blockPop e p a + ((dA : ℝ))⁻¹ ^ 2)
      (fubiniStudyMeasure p₀) := integrable_add_const_iff.mpr hI2
  calc ∫ p, Complex.normSq (hsDeviation e p a a) ∂(fubiniStudyMeasure p₀)
      = ∫ p, ((blockPop e p a) ^ 2
            + ((-(2 * ((dA : ℝ))⁻¹)) * blockPop e p a + ((dA : ℝ))⁻¹ ^ 2))
          ∂(fubiniStudyMeasure p₀) :=
        integral_congr_ae (ae_of_all _ (fun p => by
          dsimp only
          rw [hsDeviation_diag, Complex.normSq_ofReal]
          ring))
    _ = (∫ p, (blockPop e p a) ^ 2 ∂(fubiniStudyMeasure p₀))
          + ((-(2 * ((dA : ℝ))⁻¹)) * ∫ p, blockPop e p a ∂(fubiniStudyMeasure p₀)
              + ((dA : ℝ))⁻¹ ^ 2) := by
        rw [integral_add hI1 hI3, integral_add hI2 (integrable_const _),
          integral_const_mul, hconst]
    _ = ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) - ((dA : ℝ))⁻¹ ^ 2 := by
        rw [fs_blockPop_sq, fs_blockPop_mean, hmean]
        ring

/-! ### ★ The off-diagonal contribution, and entrywise integrability -/

omit [NeZero N] in
lemma redOff_measurable (e : Fin N ≃ Fin dA × Fin dB) (a a' : Fin dA) :
    Measurable (fun p : CPN N => redOff e p a a') :=
  Finset.measurable_sum Finset.univ (fun _b _ => rayDensity_measurable _ _)

omit [NeZero N] in
lemma norm_redOff_le (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a a' : Fin dA) :
    ‖redOff e p a a'‖ ≤ (dB : ℝ) := by
  rw [redOff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b : Fin dB, ‖rayDensity p (e.symm (a, b)) (e.symm (a', b))‖
      ≤ ∑ _b : Fin dB, (1 : ℝ) :=
        Finset.sum_le_sum (fun _b _ => rayDensity_norm_le_one p _ _)
    _ = (dB : ℝ) := by simp

omit [NeZero N] in
lemma normSq_redOff_measurable (e : Fin N ≃ Fin dA × Fin dB) (a a' : Fin dA) :
    Measurable (fun p : CPN N => Complex.normSq (redOff e p a a')) := by
  have h : Measurable (fun p : CPN N => redOff e p a a') := redOff_measurable e a a'
  have hrw : (fun p : CPN N => Complex.normSq (redOff e p a a'))
      = fun p => (redOff e p a a').re * (redOff e p a a').re
          + (redOff e p a a').im * (redOff e p a a').im :=
    funext (fun p => Complex.normSq_apply _)
  rw [hrw]
  exact ((Complex.measurable_re.comp h).mul (Complex.measurable_re.comp h)).add
    ((Complex.measurable_im.comp h).mul (Complex.measurable_im.comp h))

omit [NeZero N] in
/-- Every entry of the deviation is square-integrable against Fubini–Study. Proved by cases:
the diagonal is the (bounded) population deviation, the off-diagonal a sum of `d_B` density
entries each of modulus at most one. -/
lemma normSq_hsDeviation_integrable (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    (a a' : Fin dA) :
    Integrable (fun p : CPN N => Complex.normSq (hsDeviation e p a a'))
      (fubiniStudyMeasure p₀) := by
  by_cases haa : a = a'
  · subst haa
    have hI1 : Integrable (fun p : CPN N => (blockPop e p a) ^ 2) (fubiniStudyMeasure p₀) :=
      blockPop_sq_integrable p₀ e a
    have hI2 : Integrable (fun p : CPN N => (-(2 * ((dA : ℝ))⁻¹)) * blockPop e p a)
        (fubiniStudyMeasure p₀) := (blockPop_integrable p₀ e a).const_mul _
    have hI3 : Integrable (fun p : CPN N =>
          (-(2 * ((dA : ℝ))⁻¹)) * blockPop e p a + ((dA : ℝ))⁻¹ ^ 2)
        (fubiniStudyMeasure p₀) := integrable_add_const_iff.mpr hI2
    have hI4 : Integrable (fun p : CPN N => (blockPop e p a) ^ 2
          + ((-(2 * ((dA : ℝ))⁻¹)) * blockPop e p a + ((dA : ℝ))⁻¹ ^ 2))
        (fubiniStudyMeasure p₀) := hI1.add hI3
    refine hI4.congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only
    rw [hsDeviation_diag, Complex.normSq_ofReal]
    ring
  · have hpt : ∀ p : CPN N, Complex.normSq (redOff e p a a')
        = Complex.normSq (hsDeviation e p a a') := fun p => by
      rw [hsDeviation_off e p haa]
    have hbd : ∀ p : CPN N, ‖Complex.normSq (redOff e p a a')‖ ≤ (dB : ℝ) ^ 2 := by
      intro p
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (redOff e p a a'), norm_redOff_le e p a a']
    exact (Integrable.of_bound (normSq_redOff_measurable e a a').aestronglyMeasurable
      ((dB : ℝ) ^ 2) (ae_of_all _ hbd)).congr (Filter.Eventually.of_forall hpt)

/-- ★ **The off-diagonal contribution**: `E|(ρ_A)_{aa'}|² = d_B/(N(N+1))` for `a ≠ a'` —
subtracting `I_A/d_A` leaves these entries untouched, so this is `fs_redOff_normSq`. -/
theorem fs_hsDeviation_off_sq (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {a a' : Fin dA} (haa : a ≠ a') :
    ∫ p, Complex.normSq (hsDeviation e p a a') ∂(fubiniStudyMeasure p₀)
      = (dB : ℝ) / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have hpt : ∀ p : CPN N, Complex.normSq (hsDeviation e p a a')
      = Complex.normSq (redOff e p a a') := fun p => by rw [hsDeviation_off e p haa]
  rw [integral_congr_ae (ae_of_all _ hpt)]
  exact fs_redOff_normSq p₀ e haa

/-! ### ★★ The Hilbert–Schmidt assembly -/

/-- ★★ **The Lubkin–Page purity average, in Hilbert–Schmidt form**:

  `E‖ρ_A − I_A/d_A‖₂² = (d_A + d_B)/(N + 1) − 1/d_A`

(equivalently `E[Tr ρ_A²] = (d_A + d_B)/(N + 1)`, since `‖ρ_A − I_A/d_A‖₂² = Tr ρ_A² − 1/d_A`
for any trace-one `ρ_A`).

Every ingredient is one of the moments above: the `d_A` diagonal entries each contribute
`fs_hsDeviation_diag_sq`, the `d_A(d_A − 1)` off-diagonal entries each contribute
`fs_hsDeviation_off_sq`, and `N = d_A d_B` — read off the bipartition `e` itself by
`card_eq_mul_of_tensorEquiv` — collapses the result.

For a large environment (`d_B ≫ d_A`) the right-hand side is `≈ d_B/(N+1) ≈ 1/d_A`, so the
deviation's mean square is second order: a Fubini–Study-typical global ray has a subsystem
state close to maximally mixed. Combined with `fs_chebyshev_concentration` this is
canonical typicality at Chebyshev grade. -/
theorem fs_hsDeviationNormSq (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) :
    ∫ p, hsDeviationNormSq e p ∂(fubiniStudyMeasure p₀)
      = ((dA : ℝ) + (dB : ℝ)) / ((N : ℝ) + 1) - ((dA : ℝ))⁻¹ := by
  classical
  have hNmul := card_eq_mul_of_tensorEquiv e
  have hN0 : N ≠ 0 := NeZero.ne N
  have hdAn : dA ≠ 0 := by rintro rfl; exact hN0 (by simpa using hNmul)
  have hdBn : dB ≠ 0 := by rintro rfl; exact hN0 (by simpa using hNmul)
  have hdA0 : (dA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdAn
  have hdB0 : (dB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdBn
  have hNR : (N : ℝ) = (dA : ℝ) * (dB : ℝ) := by exact_mod_cast hNmul
  have hden : (dA : ℝ) * (dB : ℝ) + 1 ≠ 0 := by positivity
  have hrow : ∀ a : Fin dA,
      ∫ p, (∑ a' : Fin dA, Complex.normSq (hsDeviation e p a a')) ∂(fubiniStudyMeasure p₀)
        = (((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) - ((dA : ℝ))⁻¹ ^ 2)
          + ((dA : ℝ) - 1) * ((dB : ℝ) / ((N : ℝ) * ((N : ℝ) + 1))) := by
    intro a
    have herase : ∑ a' ∈ Finset.univ.erase a,
        (∫ p, Complex.normSq (hsDeviation e p a a') ∂(fubiniStudyMeasure p₀))
        = ((dA : ℝ) - 1) * ((dB : ℝ) / ((N : ℝ) * ((N : ℝ) + 1))) := by
      rw [Finset.sum_congr rfl (fun a' ha' =>
          fs_hsDeviation_off_sq p₀ e (Ne.symm (Finset.mem_erase.mp ha').1)),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hdAn), Nat.cast_one]
    rw [integral_finsetSum Finset.univ
        (fun a' _ => normSq_hsDeviation_integrable p₀ e a a'),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ a), herase,
      fs_hsDeviation_diag_sq p₀ e a]
    ring
  simp only [hsDeviationNormSq]
  rw [integral_finsetSum Finset.univ (fun a _ =>
      integrable_finsetSum Finset.univ (fun a' _ => normSq_hsDeviation_integrable p₀ e a a')),
    Finset.sum_congr rfl (fun a _ => hrow a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hNR]
  field_simp
  ring

/-! ### ★ The typicality statement (Markov) -/

omit [NeZero N] in
lemma hsDeviationNormSq_nonneg (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) :
    0 ≤ hsDeviationNormSq e p :=
  Finset.sum_nonneg (fun _a _ =>
    Finset.sum_nonneg (fun _a' _ => Complex.normSq_nonneg _))

omit [NeZero N] in
lemma hsDeviationNormSq_integrable (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) :
    Integrable (fun p : CPN N => hsDeviationNormSq e p) (fubiniStudyMeasure p₀) :=
  integrable_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun a' _ => normSq_hsDeviation_integrable p₀ e a a'))

omit [NeZero N] in
lemma normSq_hsDeviation_measurable (e : Fin N ≃ Fin dA × Fin dB) (a a' : Fin dA) :
    Measurable (fun p : CPN N => Complex.normSq (hsDeviation e p a a')) := by
  by_cases haa : a = a'
  · subst haa
    have hrw : (fun p : CPN N => Complex.normSq (hsDeviation e p a a))
        = fun p => (blockPop e p a - ((dA : ℝ))⁻¹) ^ 2 :=
      funext (fun p => by rw [hsDeviation_diag, Complex.normSq_ofReal]; ring)
    rw [hrw]
    exact ((blockPop_measurable e a).sub measurable_const).pow_const 2
  · have hrw : (fun p : CPN N => Complex.normSq (hsDeviation e p a a'))
        = fun p => Complex.normSq (redOff e p a a') :=
      funext (fun p => by rw [hsDeviation_off e p haa])
    rw [hrw]
    exact normSq_redOff_measurable e a a'

omit [NeZero N] in
lemma hsDeviationNormSq_measurable (e : Fin N ≃ Fin dA × Fin dB) :
    Measurable (fun p : CPN N => hsDeviationNormSq e p) :=
  Finset.measurable_sum _ (fun a _ =>
    Finset.measurable_sum _ (fun a' _ => normSq_hsDeviation_measurable e a a'))

omit [NeZero N] in
/-- A crude but uniform entry bound, enough to make the functional a bounded observable. -/
lemma normSq_hsDeviation_le (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a a' : Fin dA) :
    Complex.normSq (hsDeviation e p a a') ≤ 1 + (dB : ℝ) ^ 2 := by
  by_cases haa : a = a'
  · subst haa
    have hdApos : 0 < dA := Fin.pos a
    have hdA1 : (1 : ℝ) ≤ (dA : ℝ) := Nat.one_le_cast.mpr hdApos
    have hd0 : (0 : ℝ) ≤ ((dA : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg dA)
    have hd1 : ((dA : ℝ))⁻¹ ≤ 1 := by
      rw [inv_eq_one_div, div_le_one (by linarith : (0 : ℝ) < (dA : ℝ))]
      exact hdA1
    rw [hsDeviation_diag, Complex.normSq_ofReal]
    nlinarith [blockPop_nonneg e p a, blockPop_le_one e p a, sq_nonneg ((dB : ℝ))]
  · rw [hsDeviation_off e p haa, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (redOff e p a a'), norm_redOff_le e p a a']

omit [NeZero N] in
/-- The Hilbert–Schmidt functional is a **bounded** observable — what lets the equilibration
engine (`MeasureTheory.HasCorrelationDecay`) accept it. -/
lemma hsDeviationNormSq_le (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) :
    hsDeviationNormSq e p ≤ (dA : ℝ) ^ 2 * (1 + (dB : ℝ) ^ 2) := by
  calc hsDeviationNormSq e p
      = ∑ a : Fin dA, ∑ a' : Fin dA, Complex.normSq (hsDeviation e p a a') := rfl
    _ ≤ ∑ _a : Fin dA, ∑ _a' : Fin dA, (1 + (dB : ℝ) ^ 2) :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun a' _ => normSq_hsDeviation_le e p a a'))
    _ = (dA : ℝ) ^ 2 * (1 + (dB : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- ★ **Canonical typicality, in usable form.** Markov's inequality on the second moment: the
Fubini–Study probability that a ray's subsystem state sits Hilbert–Schmidt-far from maximally
mixed is at most `((d_A+d_B)/(N+1) − 1/d_A)/ε`.

Note this is *Markov* on a quadratic functional, not `fs_chebyshev_concentration` — the latter
applies to the linear moment-map statistics (each individual population `blockPop` is one of
those, and does get the Chebyshev rate). -/
theorem fs_hsDeviation_typicality (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {ε : ℝ} (hε : 0 < ε) :
    (fubiniStudyMeasure p₀).real {p | ε ≤ hsDeviationNormSq e p}
      ≤ (((dA : ℝ) + (dB : ℝ)) / ((N : ℝ) + 1) - ((dA : ℝ))⁻¹) / ε := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun p => hsDeviationNormSq_nonneg e p))
    (hsDeviationNormSq_integrable p₀ e) ε
  rw [fs_hsDeviationNormSq p₀ e] at h
  rw [le_div_iff₀ hε]
  linarith

end CSD.Thermo
