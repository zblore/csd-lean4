/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.BornWrapper

/-!
# LF2/EffectGleason: the Busch effect-Gleason theorem, PROVED (discharges the former axiom)

**Category:** 3-Local (LF2 operational stratum — the effect-Gleason representation theorem).

Earlier revisions of `LF2/BornWrapper.lean` imported the Busch effect-Gleason theorem as the
axiom `busch_effect_gleason`: every effect-additive, bounded, normalised probability assignment
`OP.p` on effects is `OP.p E = Tr(ρ E)` for a *unique* density operator `ρ`. This module
**discharges** that axiom — it is proved here as `OperationalPackage.effect_gleason_representation`
(2026-07-21), so the corpus imports **zero** axioms beyond the foundational triple
(`CONVENTIONS.md §8.1`, `AXIOMS.md §2.2`, `specs/BACKLOG.md`). The `axiom` was deleted from
`BornWrapper.lean` and its two named consumers (`born_form_of_package`,
`pure_state_born_weights_of_certainty`) relocated here (signatures unchanged), since they now
depend on the proof, which imports `BornWrapper`. Busch's proof (Busch 2003, "A Simple Proof of
Gleason's Theorem") is short in finite dimensions because additivity over the *effect* algebra
gives linearity directly, bypassing the frame-function analysis of projective Gleason.

## Proof arc (bottom-up)

1. **This module — the foundational layer (`p` is a monotone, additive functional).**
   * `Effect.smul` — `t • E` is an effect for `t ∈ [0,1]` (the scalar action used throughout).
   * `OperationalPackage.p_zero` — `p 0 = 0` (from `p 0 = p(0 ⊕ 0) = 2 p 0`).
   * `OperationalPackage.p_mono` — `E.M ≤ F.M` (Löwner) ⟹ `p E ≤ p F` (additivity + `nonneg`).
   * `OperationalPackage.p_smul_add` — `p((a+b) • E) = p(a • E) + p(b • E)` for `a,b,a+b ∈ [0,1]`
     (scalar additivity of `t ↦ p(t • E)` on `[0,1]`).
   * `OperationalPackage.p_smul_mono` — `t ↦ p(t • E)` is monotone on `[0,1]`.
2. **This module — homogeneity** `p(t • E) = t · p E` for `t ∈ [0,1]` (`p_smul_homog`,
   `smulVal_homog`): the monotone + additive (Cauchy) equation `f(a+b) = f(a)+f(b)` on `[0,1]`
   forces `f(t) = t f(1)` — via integer scaling (`smulVal_natMul`), rational homogeneity
   (`smulVal_rat`), and the density squeeze (`exists_rat_btwn` + monotonicity).
3. **Reconstruction — spectral reduction, polarisation, and the ρ-build (delivered).**
   The **spectral reduction** is done: `p_finsetSum` (finite additivity),
   `Effect.eigenvalues_le_one` (effect eigenvalues `∈ [0,1]`), `Effect.sum_eigenEffect_M`
   (`E = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`), and `p_eq_eigen_sum` (`p(E) = ∑ᵢ λᵢ · p(|eᵢ⟩⟨eᵢ|)`) reduce the whole
   representation problem to determining `p` on rank-one projectors. The **polarisation
   identities** are done: `outerProduct_parallelogram` (`|u+v⟩⟨u+v| + |u−v⟩⟨u−v| = 2|u⟩⟨u| +
   2|v⟩⟨v|`, cross terms cancel) and `outerProduct_polarization_real` — the algebraic core that
   lets `p`, being additive, inherit the parallelogram law. The **sub-unit rank-one effect**
   `outerEffect v` (`|v⟩⟨v|` for any `‖v‖ ≤ 1`, needed for the combinations `u ± v`, `u ± iv`),
   the **degree-2 homogeneity** `p_outerEffect_smul` (`p(|c·v⟩⟨c·v|) = c²·p(|v⟩⟨v|)`), and the
   **Cauchy–Schwarz sum bound** `one_sub_two_outerProduct_posSemidef` (`I − |a⟩⟨a| − |b⟩⟨b|` PSD
   for `‖a‖²+‖b‖²≤1`, via CS not an eigenvalue bound), and the **`p`-level parallelogram law**
   `p_parallelogram` (`p(|u+v⟩⟨u+v|) + p(|u−v⟩⟨u−v|) = 2p(|u⟩⟨u|) + 2p(|v⟩⟨v|)` for
   `‖u‖²+‖v‖²≤½`, from the matrix identity + additivity + the `√2`-doubling `p_outerEffect_sqrt2`)
   are done. The **ρ-build** (step 3b-final) is now done as well: `qform` (the degree-2
   homogeneous extension of `v ↦ p(|v⟩⟨v|)` off the unit ball) satisfies the *unrestricted*
   parallelogram law (`qform_parallelogram`); the Jordan–von Neumann argument makes its
   polarisation `qpolar` bi-additive (`qpolar_add_left`) and — via `additive_bounded_linear`,
   which replaces the classical continuity step by the bound `0 ≤ q ≤ ‖·‖²` —
   `ℝ`-bihomogeneous (`qpolar_smul_real`); the complex polarisation `qsesq` is then sesquilinear
   (`qsesq_add_right`, `qsesq_smul_right`, `qsesq_conj_symm`) with `qsesq_self : S(v,v) = q v`,
   and its matrix on the standard basis `qmatrix` is Hermitian (`qmatrix_isHermitian`) with
   `p_outerEffect_eq_trace : p(|v⟩⟨v|) = Tr(R · |v⟩⟨v|)` and — through the spectral reduction —
   `p_eq_trace : p E = Tr(R · E)` for **every** effect.
4. **Positivity / normalisation + uniqueness (step 4 — done).** `p ≥ 0 ⟹ R` PSD
   (`qmatrix_posSemidef`); `p I = 1 ⟹ Tr R = 1` (`qmatrix_trace_one`); uniqueness because a
   complex matrix is determined by its quadratic form (`matrix_eq_zero_of_quadForm_zero`, a
   polarisation) via `qdensity_unique`. This packages `R = qmatrix` as the `DensityOperator`
   `qdensity` and yields `effect_gleason_representation` (`∃!`), the statement the axiom asserted.

## Honest scope

**Delivered here — the complete theorem.** Steps 1–2 (monotone/additive layer + homogeneity
`p(t•E) = t·p E`), the **spectral reduction** (`p(E) = ∑ᵢ λᵢ · p(|eᵢ⟩⟨eᵢ|)`), the **polarisation
identities** (step 3b), the **ρ-build** (step 3b-final: `p E = Tr(R · E)`, `p_eq_trace`), and
**step 4** (PSD / unit-trace / uniqueness), assembled into
`OperationalPackage.effect_gleason_representation`. All foundational-triple (`propext`,
`Classical.choice`, `Quot.sound`), no `sorry`, no placeholder — verified by AxiomAudit. The
`busch_effect_gleason` axiom has been **removed** from `BornWrapper.lean`; this module is the
proof.

References: `LF2/BornWrapper.lean` (`Effect`, `DensityOperator`, `OperationalPackage`,
`traceForm`, `rankOneDensity_unique_of_certainty`, `born_quadratic`); Busch 2003
(`quant-ph/9909073`); Jordan–von Neumann 1935
(the parallelogram characterisation polarised in §J–§K); `AXIOMS.md §2.2`;
`CONVENTIONS.md §8.1`; `specs/BACKLOG.md`; `specs/future-work.md`.
-/

open Matrix Unitary
open scoped ComplexOrder

namespace CSD.LF2

variable {N : ℕ}

namespace Effect

/-- **Effect extensionality on the matrix field.** Two effects are equal iff their underlying
matrices are equal (the `Hermitian`/`PosSemidef`/`le_one` fields are `Prop`, proof-irrelevant). -/
theorem ext_M {E F : Effect N} (h : E.M = F.M) : E = F := by
  cases E; cases F; cases h; rfl

/-- **Scalar action on an effect.** For `t ∈ [0,1]`, `t • E` is again an effect: `t • M` is
Hermitian and PSD (`t ≥ 0`), and `1 - t • M = (1 - M) + (1 - t) • M` is PSD (`t ≤ 1`). -/
noncomputable def smul (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (E : Effect N) : Effect N where
  M := (t : ℂ) • E.M
  isHermitian := by
    show ((t : ℂ) • E.M)ᴴ = (t : ℂ) • E.M
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, E.isHermitian.eq]
  nonneg := E.nonneg.smul (by exact_mod_cast ht0)
  le_one := by
    have hc0 : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_zero]; exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - t)
    have hsplit : (1 : Matrix (Fin N) (Fin N) ℂ) - (t : ℂ) • E.M
        = (1 - E.M) + ((1 - t : ℝ) : ℂ) • E.M := by
      push_cast; module
    rw [hsplit]
    exact E.le_one.add (E.nonneg.smul hc0)

@[simp] lemma smul_M (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (E : Effect N) :
    (Effect.smul t ht0 ht1 E).M = (t : ℂ) • E.M := rfl

/-- **A finite sum of effects whose total is `≤ I` is an effect.** Hermiticity and PSD of the
sum are automatic; `le_one` is the hypothesis (as in `Effect.add`). -/
noncomputable def finsetSum {ι : Type*} (s : Finset ι) (E : ι → Effect N)
    (h : (1 - ∑ i ∈ s, (E i).M).PosSemidef) : Effect N where
  M := ∑ i ∈ s, (E i).M
  isHermitian := by
    show (∑ i ∈ s, (E i).M)ᴴ = ∑ i ∈ s, (E i).M
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => (E i).isHermitian
  nonneg := Matrix.posSemidef_sum _ fun i _ => (E i).nonneg
  le_one := h

@[simp] lemma finsetSum_M {ι : Type*} (s : Finset ι) (E : ι → Effect N)
    (h : (1 - ∑ i ∈ s, (E i).M).PosSemidef) :
    (Effect.finsetSum s E h).M = ∑ i ∈ s, (E i).M := rfl

end Effect

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **`p 0 = 0`.** From additivity `p 0 = p(0 ⊕ 0) = 2 · p 0`. -/
theorem p_zero : OP.p Effect.zero = 0 := by
  set z : Effect N := Effect.zero with hz
  have hLe : (1 - (z.M + z.M)).PosSemidef := by
    simpa [hz, Effect.zero] using (Matrix.PosSemidef.one (n := Fin N) (R := ℂ))
  have hzz : Effect.add z z hLe = z :=
    Effect.ext_M (by simp [Effect.add, hz, Effect.zero])
  have hadd := OP.additivity z z hLe
  rw [hzz] at hadd
  linarith

/-- **Monotonicity.** If `E.M ≤ F.M` in the Löwner order (`F.M - E.M` PSD), then `p E ≤ p F`.
Write `F = E ⊕ (F − E)`, an effect sum, and use `p(F−E) ≥ 0`. -/
theorem p_mono {E F : Effect N} (h : (F.M - E.M).PosSemidef) : OP.p E ≤ OP.p F := by
  let G : Effect N :=
    { M := F.M - E.M
      isHermitian := F.isHermitian.sub E.isHermitian
      nonneg := h
      le_one := by
        have hrw : (1 : Matrix (Fin N) (Fin N) ℂ) - (F.M - E.M) = (1 - F.M) + E.M := by abel
        rw [hrw]; exact F.le_one.add E.nonneg }
  have hLe : (1 - (E.M + G.M)).PosSemidef := by
    have hEG : E.M + G.M = F.M := by show E.M + (F.M - E.M) = F.M; abel
    rw [hEG]; exact F.le_one
  have hEF : Effect.add E G hLe = F :=
    Effect.ext_M (by show E.M + (F.M - E.M) = F.M; abel)
  have hadd := OP.additivity E G hLe
  rw [hEF] at hadd
  have hG : 0 ≤ OP.p G := OP.nonneg G
  linarith

/-- **Scalar additivity of `t ↦ p(t • E)` on `[0,1]`.** For `a, b ≥ 0` with `a + b ≤ 1`,
`p((a+b) • E) = p(a • E) + p(b • E)` — the Cauchy relation whose monotone solution is
`p(t • E) = t · p E` (the deferred homogeneity step). -/
theorem p_smul_add {E : Effect N} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    OP.p (Effect.smul (a + b) (by linarith) hab E)
      = OP.p (Effect.smul a ha (by linarith) E) + OP.p (Effect.smul b hb (by linarith) E) := by
  have hLe : (1 - ((Effect.smul a ha (by linarith) E).M
      + (Effect.smul b hb (by linarith) E).M)).PosSemidef := by
    have hsum : (Effect.smul a ha (by linarith) E).M + (Effect.smul b hb (by linarith) E).M
        = (Effect.smul (a + b) (by linarith) hab E).M := by
      simp only [Effect.smul_M]; push_cast; module
    rw [hsum]; exact (Effect.smul (a + b) (by linarith) hab E).le_one
  have hadd := OP.additivity (Effect.smul a ha (by linarith) E)
    (Effect.smul b hb (by linarith) E) hLe
  have hEq : Effect.add (Effect.smul a ha (by linarith) E) (Effect.smul b hb (by linarith) E) hLe
      = Effect.smul (a + b) (by linarith) hab E :=
    Effect.ext_M (by simp only [Effect.add, Effect.smul_M]; push_cast; module)
  rw [hEq] at hadd
  exact hadd

/-- **`t ↦ p(t • E)` is monotone on `[0,1]`.** Immediate from `p_mono`: `s ≤ t` gives
`(t − s) • E.M` PSD, so `s • E.M ≤ t • E.M`. -/
theorem p_smul_mono {E : Effect N} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    OP.p (Effect.smul s hs0 (le_trans hst ht1) E) ≤ OP.p (Effect.smul t (le_trans hs0 hst) ht1 E) := by
  refine OP.p_mono ?_
  simp only [Effect.smul_M]
  have hrw : (t : ℂ) • E.M - (s : ℂ) • E.M = ((t - s : ℝ) : ℂ) • E.M := by push_cast; module
  rw [hrw]
  exact E.nonneg.smul (by rw [← Complex.ofReal_zero]; exact_mod_cast (by linarith : (0 : ℝ) ≤ t - s))

/-! ### C — homogeneity `p(t • E) = t · p E` on `[0,1]` (Route B step 2)

The monotone + additive (Cauchy) functional equation `f(a+b) = f(a)+f(b)` on `[0,1]` forces
`f(t) = t·f(1)`. We package `f(t) = p(t•E)` as a total function `smulVal` (0 outside `[0,1]`)
to avoid carrying the `0 ≤ t ≤ 1` proofs, prove homogeneity on the naturals-ratio `m/n` (from
additivity), and squeeze to all reals by density of the rationals + monotonicity. -/

/-- `p(t • E)` as a total function of `t` (`0` outside `[0,1]`), for the Cauchy/monotone analysis. -/
noncomputable def smulVal (E : Effect N) (t : ℝ) : ℝ :=
  if h : 0 ≤ t ∧ t ≤ 1 then OP.p (Effect.smul t h.1 h.2 E) else 0

lemma smulVal_of {E : Effect N} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OP.smulVal E t = OP.p (Effect.smul t ht0 ht1 E) := dif_pos ⟨ht0, ht1⟩

lemma smulVal_zero (E : Effect N) : OP.smulVal E 0 = 0 := by
  rw [OP.smulVal_of (le_refl 0) zero_le_one,
    show Effect.smul (0 : ℝ) (le_refl 0) zero_le_one E = Effect.zero from
      Effect.ext_M (by simp [Effect.smul_M, Effect.zero]), OP.p_zero]

lemma smulVal_one (E : Effect N) : OP.smulVal E 1 = OP.p E := by
  rw [OP.smulVal_of zero_le_one (le_refl 1),
    show Effect.smul (1 : ℝ) zero_le_one (le_refl 1) E = E from
      Effect.ext_M (by simp [Effect.smul_M])]

lemma smulVal_nonneg (E : Effect N) (t : ℝ) : 0 ≤ OP.smulVal E t := by
  rw [smulVal]; split
  · exact OP.nonneg _
  · exact le_refl 0

lemma smulVal_add {E : Effect N} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    OP.smulVal E (a + b) = OP.smulVal E a + OP.smulVal E b := by
  rw [OP.smulVal_of (by linarith) hab, OP.smulVal_of ha (by linarith), OP.smulVal_of hb (by linarith)]
  exact OP.p_smul_add ha hb hab

lemma smulVal_mono {E : Effect N} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    OP.smulVal E s ≤ OP.smulVal E t := by
  rw [OP.smulVal_of hs0 (le_trans hst ht1), OP.smulVal_of (le_trans hs0 hst) ht1]
  exact OP.p_smul_mono hs0 hst ht1

/-- **Integer scaling.** `p((n·s) • E) = n · p(s • E)` for `s ≥ 0` and `n·s ≤ 1` (induction on `n`
via additivity). -/
theorem smulVal_natMul {E : Effect N} {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) (hn : (n : ℝ) * s ≤ 1) :
    OP.smulVal E ((n : ℝ) * s) = (n : ℝ) * OP.smulVal E s := by
  induction n with
  | zero => simp [smulVal_zero]
  | succ n ih =>
    have hns : (n : ℝ) * s ≤ 1 := by
      have hle : (n : ℝ) * s ≤ ((n + 1 : ℕ) : ℝ) * s :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) hs0
      linarith
    have hstep : ((n + 1 : ℕ) : ℝ) * s = (n : ℝ) * s + s := by push_cast; ring
    rw [hstep] at hn ⊢
    rw [OP.smulVal_add (mul_nonneg (Nat.cast_nonneg n) hs0) hs0 hn, ih hns]
    push_cast; ring

/-- **Reciprocal.** `p((1/n) • E) = (1/n) · p(E)` for `n ≥ 1`. -/
theorem smulVal_recip {E : Effect N} (n : ℕ) (hn : 1 ≤ n) :
    OP.smulVal E (1 / (n : ℝ)) = (1 / (n : ℝ)) * OP.smulVal E 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key := OP.smulVal_natMul (E := E) (s := 1 / (n : ℝ)) (by positivity) n
    (by rw [mul_one_div, div_self (ne_of_gt hn0)])
  rw [mul_one_div, div_self (ne_of_gt hn0)] at key
  rw [key]; field_simp

/-- **Rational homogeneity.** `p((q) • E) = q · p(E)` for `q ∈ [0,1] ∩ ℚ`. -/
theorem smulVal_rat {E : Effect N} (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    OP.smulVal E (q : ℝ) = (q : ℝ) * OP.smulVal E 1 := by
  have hd0 : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hcast : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0)).symm
  have hmn1 : (q.num.toNat : ℝ) * (1 / (q.den : ℝ)) ≤ 1 := by
    rw [mul_one_div, ← hcast]; exact_mod_cast hq1
  have hstep := OP.smulVal_natMul (E := E) (s := 1 / (q.den : ℝ)) (by positivity) q.num.toNat hmn1
  rw [mul_one_div] at hstep
  rw [hcast, hstep, OP.smulVal_recip q.den q.pos]
  ring

/-- **Homogeneity (the Cauchy/monotone squeeze).** `p(t • E) = t · p(E)` for all `t ∈ [0,1]`.
The rational homogeneity + monotonicity pin `smulVal E t` between `q·c` values for rationals
`q` arbitrarily close to `t` (density), forcing `smulVal E t = t·c` with `c = p(E)`. -/
theorem smulVal_homog {E : Effect N} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OP.smulVal E t = t * OP.smulVal E 1 := by
  set c := OP.smulVal E 1 with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact OP.smulVal_nonneg E 1
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · -- smulVal E t ≤ t*c + ε
    rcases eq_or_lt_of_le ht1 with rfl | h1
    · rw [← hc]; linarith [hε]
    · obtain ⟨q, hq_lt, hq_ub⟩ := exists_rat_btwn (show t < min 1 (t + ε / (c + 1)) from lt_min h1 (by have := div_pos hε hc1; linarith))
      have hqt : t ≤ (q : ℝ) := le_of_lt hq_lt
      have hq1 : (q : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hq_ub (min_le_left _ _))
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans ht0 hqt
      calc OP.smulVal E t ≤ OP.smulVal E (q : ℝ) := OP.smulVal_mono ht0 hqt hq1
        _ = (q : ℝ) * c := by rw [OP.smulVal_rat q (by exact_mod_cast hq0) (by exact_mod_cast hq1), hc]
        _ ≤ (t + ε / (c + 1)) * c := by
              apply mul_le_mul_of_nonneg_right _ hc0
              exact le_of_lt (lt_of_lt_of_le hq_ub (min_le_right _ _))
        _ = t * c + ε / (c + 1) * c := by ring
        _ ≤ t * c + ε := by
              have : ε / (c + 1) * c ≤ ε := by
                rw [div_mul_eq_mul_div, div_le_iff₀ hc1]; nlinarith [hε, hc0]
              linarith
  · -- t*c ≤ smulVal E t + ε
    rcases eq_or_lt_of_le ht0 with rfl | h0
    · rw [zero_mul]; have h := OP.smulVal_nonneg E 0; linarith
    · obtain ⟨q, hq_lb, hq_lt⟩ := exists_rat_btwn (show max (t - ε / (c + 1)) 0 < t from max_lt (by have := div_pos hε hc1; linarith) h0)
      have hqt : (q : ℝ) ≤ t := le_of_lt hq_lt
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hq_lb)
      have hq1 : (q : ℝ) ≤ 1 := le_trans hqt ht1
      have hlb : t - ε / (c + 1) < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq_lb
      have hstep : (q : ℝ) * c ≤ OP.smulVal E t := by
        have hrq : OP.smulVal E (q : ℝ) = (q : ℝ) * c := by
          rw [OP.smulVal_rat q (by exact_mod_cast hq0) (by exact_mod_cast hq1), ← hc]
        rw [← hrq]; exact OP.smulVal_mono hq0 hqt ht1
      have hεc : ε / (c + 1) * c ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hc1]; nlinarith [hε, hc0]
      nlinarith [hstep, hlb, hc0]

/-- **Homogeneity, effect form.** `p(t • E) = t · p(E)` for `t ∈ [0,1]`. -/
theorem p_smul_homog {E : Effect N} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OP.p (Effect.smul t ht0 ht1 E) = t * OP.p E := by
  rw [← OP.smulVal_of ht0 ht1, OP.smulVal_homog ht0 ht1, OP.smulVal_one]

/-! ### D — finite additivity (Route B step 3, building block) -/

/-- **Finite additivity.** For a family of effects whose total is `≤ I`, `p(∑ᵢ Eᵢ) = ∑ᵢ p(Eᵢ)`.
Induction on the index set via the pairwise `additivity`; each partial sum stays `≤ I` because
the omitted effects are PSD. The prerequisite for reducing `p` on an arbitrary effect to `p` on
the rank-one projectors of its spectral decomposition. -/
theorem p_finsetSum {ι : Type*} [DecidableEq ι] (E : ι → Effect N) (s : Finset ι) :
    ∀ (h : (1 - ∑ i ∈ s, (E i).M).PosSemidef),
      OP.p (Effect.finsetSum s E h) = ∑ i ∈ s, OP.p (E i) := by
  induction s using Finset.induction with
  | empty =>
    intro h
    rw [show Effect.finsetSum (∅ : Finset ι) E h = Effect.zero from
      Effect.ext_M (by simp [Effect.finsetSum, Effect.zero]), OP.p_zero, Finset.sum_empty]
  | insert a s' ha ih =>
    intro h
    have hins : ∑ i ∈ insert a s', (E i).M = (E a).M + ∑ i ∈ s', (E i).M := Finset.sum_insert ha
    have h' : (1 - ∑ i ∈ s', (E i).M).PosSemidef := by
      have hrw : (1 : Matrix (Fin N) (Fin N) ℂ) - ∑ i ∈ s', (E i).M
          = (1 - ∑ i ∈ insert a s', (E i).M) + (E a).M := by rw [hins]; abel
      rw [hrw]; exact h.add (E a).nonneg
    have hLe : (1 - ((E a).M + (Effect.finsetSum s' E h').M)).PosSemidef := by
      simp only [Effect.finsetSum_M]; rw [← hins]; exact h
    rw [show Effect.finsetSum (insert a s') E h
          = Effect.add (E a) (Effect.finsetSum s' E h') hLe from
        Effect.ext_M (by simp only [Effect.finsetSum_M, Effect.add]; rw [hins]),
      OP.additivity, ih h', Finset.sum_insert ha]

end OperationalPackage

/-! ### E — spectral reduction (Route B step 3): `p(E) = ∑ᵢ λᵢ · p(|eᵢ⟩⟨eᵢ|)` -/

namespace Effect

/-- **Effect eigenvalues are `≤ 1`.** For an effect `E` (so `1 - E.M` is PSD), each eigenvalue of
`E.M` is `≤ 1`: on the eigenvector `eᵢ`, `⟨eᵢ, (1-E.M) eᵢ⟩ = 1 - λᵢ ≥ 0`. -/
theorem eigenvalues_le_one (E : Effect N) (i : Fin N) :
    E.isHermitian.eigenvalues i ≤ 1 := by
  set x : Fin N → ℂ := ⇑(E.isHermitian.eigenvectorBasis i) with hx
  have hnorm : ‖E.isHermitian.eigenvectorBasis i‖ = 1 :=
    E.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
  have hxx : star x ⬝ᵥ x = 1 := by
    have h1 : star x ⬝ᵥ x
        = inner ℂ (E.isHermitian.eigenvectorBasis i) (E.isHermitian.eigenvectorBasis i) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]; exact dotProduct_comm _ _
    rw [h1, inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  have hmv : E.M *ᵥ x = (E.isHermitian.eigenvalues i : ℂ) • x := by
    rw [hx]; exact E.isHermitian.mulVec_eigenvectorBasis i
  have hnn : (0 : ℂ) ≤ star x ⬝ᵥ ((1 - E.M) *ᵥ x) := E.le_one.dotProduct_mulVec_nonneg x
  have hval : star x ⬝ᵥ ((1 - E.M) *ᵥ x) = ((1 - E.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [sub_mulVec, Matrix.one_mulVec, hmv, dotProduct_sub, dotProduct_smul, hxx, smul_eq_mul,
      mul_one]
    push_cast; ring
  rw [hval] at hnn
  have hle : (0 : ℝ) ≤ 1 - E.isHermitian.eigenvalues i := Complex.zero_le_real.mp hnn
  linarith

/-- **The eigenvalue-scaled rank-one projectors of an effect are effects.** `λᵢ • |eᵢ⟩⟨eᵢ|` with
`λᵢ = eigenvalues i ∈ [0,1]` and `eᵢ = eigenvectorBasis i` (unit norm). -/
noncomputable def eigenEffect (E : Effect N) (i : Fin N) : Effect N :=
  Effect.smul (E.isHermitian.eigenvalues i) (E.nonneg.eigenvalues_nonneg i)
    (E.eigenvalues_le_one i)
    (rankOneEffect (E.isHermitian.eigenvectorBasis i)
      (E.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i))

@[simp] lemma eigenEffect_M (E : Effect N) (i : Fin N) :
    (E.eigenEffect i).M
      = (E.isHermitian.eigenvalues i : ℂ) • outerProduct (E.isHermitian.eigenvectorBasis i) := by
  simp only [eigenEffect, Effect.smul_M, rankOneEffect]

/-- **`E` is the finite sum of its eigen-effects.** `E.M = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` (the Hermitian spectral
theorem, same computation as `density_eq_eigen_ensemble`). -/
theorem sum_eigenEffect_M (E : Effect N) :
    ∑ i, (E.eigenEffect i).M = E.M := by
  simp only [eigenEffect_M]
  symm
  set hA := E.isHermitian with hA_def
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    outerProduct, Matrix.vecMulVec_apply, smul_eq_mul, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

end Effect

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **Spectral reduction of `p` (Route B step 3).** For every effect `E`,
`p(E) = ∑ᵢ λᵢ · p(|eᵢ⟩⟨eᵢ|)` — the eigenvalue-weighted sum of `p` on the rank-one projectors of
`E`'s spectral decomposition. Reduces the entire representation problem to determining `p` on
rank-one projectors. Combines finite additivity + homogeneity with the spectral theorem. -/
theorem p_eq_eigen_sum (E : Effect N) :
    OP.p E = ∑ i, E.isHermitian.eigenvalues i
      * OP.p (rankOneEffect (E.isHermitian.eigenvectorBasis i)
          (E.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i)) := by
  have hLe : (1 - ∑ i, (E.eigenEffect i).M).PosSemidef := by rw [E.sum_eigenEffect_M]; exact E.le_one
  have hEeq : Effect.finsetSum Finset.univ (E.eigenEffect) hLe = E :=
    Effect.ext_M (by rw [Effect.finsetSum_M, E.sum_eigenEffect_M])
  calc OP.p E = OP.p (Effect.finsetSum Finset.univ (E.eigenEffect) hLe) := by rw [hEeq]
    _ = ∑ i, OP.p (E.eigenEffect i) := OP.p_finsetSum _ _ hLe
    _ = ∑ i, E.isHermitian.eigenvalues i
          * OP.p (rankOneEffect (E.isHermitian.eigenvectorBasis i)
              (E.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact OP.p_smul_homog (E.nonneg.eigenvalues_nonneg i) (E.eigenvalues_le_one i)

end OperationalPackage

/-! ### F0 — the sub-unit rank-one effect `|v⟩⟨v|` for `‖v‖ ≤ 1`

`rankOneEffect` is defined only for *unit* vectors. The polarisation reconstruction needs
`|v⟩⟨v|` as an effect for the (generally non-unit) combinations `u ± v`, `u ± iv`; this requires
`‖v‖ ≤ 1`. -/

/-- **`outerProduct` under complex scaling.** `|c•v⟩⟨c•v| = |c|² · |v⟩⟨v|`. -/
theorem outerProduct_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin N)) :
    outerProduct (c • v) = ((c * star c) : ℂ) • outerProduct v := by
  ext i j
  simp only [outerProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, PiLp.smul_apply,
    smul_eq_mul, star_mul']
  ring

/-- **The sub-unit rank-one effect** `|v⟩⟨v|` for `‖v‖ ≤ 1`. PSD is automatic; `le_one` holds
because `1 - |v⟩⟨v| = (1 - |v̂⟩⟨v̂|) + (1-‖v‖²)|v̂⟩⟨v̂|`, both PSD. -/
noncomputable def outerEffect (v : EuclideanSpace ℂ (Fin N)) (hv : ‖v‖ ≤ 1) : Effect N where
  M := outerProduct v
  isHermitian := outerProduct_isHermitian v
  nonneg := outerProduct_posSemidef v
  le_one := by
    rcases eq_or_ne v 0 with rfl | hne
    · have h0 : outerProduct (0 : EuclideanSpace ℂ (Fin N)) = 0 := by
        ext i j; simp [outerProduct, Matrix.vecMulVec_apply]
      rw [h0, sub_zero]; exact Matrix.PosSemidef.one
    · set φ : EuclideanSpace ℂ (Fin N) := (‖v‖⁻¹ : ℂ) • v with hφ
      have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hne
      have hφnorm : ‖φ‖ = 1 := by
        rw [hφ, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          inv_mul_cancel₀ (ne_of_gt hvpos)]
      have hv_eq : v = (‖v‖ : ℂ) • φ := by
        rw [hφ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hvpos), one_smul]
      have houter : outerProduct v = ((‖v‖ ^ 2 : ℝ) : ℂ) • outerProduct φ := by
        conv_lhs => rw [hv_eq]
        rw [outerProduct_smul]
        congr 1
        rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]; push_cast; ring
      have hsplit : (1 : Matrix (Fin N) (Fin N) ℂ) - outerProduct v
          = (1 - outerProduct φ) + ((1 - ‖v‖ ^ 2 : ℝ) : ℂ) • outerProduct φ := by
        rw [houter]; push_cast; module
      rw [hsplit]
      refine (one_sub_outerProduct_posSemidef φ hφnorm).add
        ((outerProduct_posSemidef φ).smul ?_)
      rw [← Complex.ofReal_zero]
      exact_mod_cast (by nlinarith [hv, hvpos, sq_nonneg (‖v‖ - 1)] : (0:ℝ) ≤ 1 - ‖v‖ ^ 2)

@[simp] lemma outerEffect_M (v : EuclideanSpace ℂ (Fin N)) (hv : ‖v‖ ≤ 1) :
    (outerEffect v hv).M = outerProduct v := rfl

/-- On a unit vector, `outerEffect` agrees with `rankOneEffect`. -/
lemma outerEffect_eq_rankOneEffect (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    outerEffect φ (le_of_eq hφ) = rankOneEffect φ hφ :=
  Effect.ext_M rfl

/-! ### F — the polarisation identities (Route B step 3b, building blocks)

The reconstruction of `ρ` from the rank-one values `φ ↦ p(|φ⟩⟨φ|)` rests on polarisation: the
diagonal quadratic form must come from a sesquilinear form. Its algebraic core is that the
rank-one projectors satisfy the parallelogram law at the matrix level — the cross terms of
`|u±v⟩⟨u±v|` cancel — so `p`, being additive, inherits the parallelogram law. -/

/-- **Matrix parallelogram identity for rank-one projectors.**
`|u+v⟩⟨u+v| + |u−v⟩⟨u−v| = 2|u⟩⟨u| + 2|v⟩⟨v|`: the off-diagonal cross terms
`|u⟩⟨v| + |v⟩⟨u|` appear with opposite signs in the two sums and cancel. Pure matrix algebra. -/
theorem outerProduct_parallelogram (u v : EuclideanSpace ℂ (Fin N)) :
    outerProduct (u + v) + outerProduct (u - v)
      = (2 : ℂ) • outerProduct u + (2 : ℂ) • outerProduct v := by
  ext i j
  simp only [outerProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, star_add, star_sub]
  ring

/-- **Rank-one polarisation (real part).**
`|u+v⟩⟨u+v| − |u−v⟩⟨u−v| = 2(|u⟩⟨v| + |v⟩⟨u|)`: the difference isolates the cross terms
(the "real part" of the sesquilinear form the reconstruction recovers). -/
theorem outerProduct_polarization_real (u v : EuclideanSpace ℂ (Fin N)) :
    outerProduct (u + v) - outerProduct (u - v)
      = (2 : ℂ) • Matrix.vecMulVec (fun i => u i) (fun i => star (v i))
        + (2 : ℂ) • Matrix.vecMulVec (fun i => v i) (fun i => star (u i)) := by
  ext i j
  simp only [outerProduct, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul,
    star_add, star_sub]
  ring

/-! ### F1 — the Cauchy–Schwarz sum-of-projectors bound (Route B step 3b)

The additivity step of the `p`-level parallelogram needs `|a⟩⟨a| + |b⟩⟨b| ≤ I` when
`‖a‖² + ‖b‖² ≤ 1`. This is Cauchy–Schwarz, not an eigenvalue bound:
`⟨x, (I − |a⟩⟨a| − |b⟩⟨b|) x⟩ = ‖x‖² − |⟨a,x⟩|² − |⟨b,x⟩|² ≥ ‖x‖²(1 − ‖a‖² − ‖b‖²) ≥ 0`. -/

/-- The `|a⟩⟨a|` quadratic form: `⟨x, |a⟩⟨a| x⟩ = |⟨a,x⟩|²` (the squared norm of the standard
Hermitian pairing `c := star ⇑a ⬝ᵥ x`). -/
private lemma quad_outerProduct (a : EuclideanSpace ℂ (Fin N)) (x : Fin N → ℂ) :
    star x ⬝ᵥ (outerProduct a *ᵥ x) = ((‖star (⇑a) ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
  set c := star (⇑a) ⬝ᵥ x with hc
  have hrow : ∀ i, (outerProduct a *ᵥ x) i = (⇑a) i * c := by
    intro i
    simp only [outerProduct, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.star_apply, hc,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hstar : (∑ i, star (x i) * (⇑a) i) = star c := by
    rw [hc]; simp only [dotProduct, Pi.star_apply, star_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul', star_star]; ring
  have hval : star x ⬝ᵥ (outerProduct a *ᵥ x) = c * star c := by
    simp only [dotProduct, Pi.star_apply, hrow]
    rw [← hstar, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval, ← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **Cauchy–Schwarz sum bound.** For `‖a‖² + ‖b‖² ≤ 1`, `I − |a⟩⟨a| − |b⟩⟨b|` is PSD.
`⟨x, (I − |a⟩⟨a| − |b⟩⟨b|) x⟩ = ‖x‖² − |⟨a,x⟩|² − |⟨b,x⟩|² ≥ ‖x‖²(1 − ‖a‖² − ‖b‖²) ≥ 0`. -/
theorem one_sub_two_outerProduct_posSemidef {a b : EuclideanSpace ℂ (Fin N)}
    (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 1) :
    (1 - outerProduct a - outerProduct b).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (((Matrix.isHermitian_one).sub (outerProduct_isHermitian a)).sub
      (outerProduct_isHermitian b)) fun x => ?_
  set X : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 x with hX
  have hxx : star x ⬝ᵥ x = ((‖X‖ : ℂ)) ^ 2 := by
    rw [dotProduct_comm]
    have hi : x ⬝ᵥ star x = (inner ℂ X X : ℂ) := (EuclideanSpace.inner_eq_star_dotProduct X X).symm
    rw [hi, inner_self_eq_norm_sq_to_K]; norm_cast
  have hCS : ∀ w : EuclideanSpace ℂ (Fin N),
      ‖star (⇑w) ⬝ᵥ x‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖X‖ ^ 2 := by
    intro w
    have hval : (inner ℂ X w : ℂ) = star (star (⇑w) ⬝ᵥ x) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [hX, dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    have hnorm : ‖star (⇑w) ⬝ᵥ x‖ = ‖(inner ℂ X w : ℂ)‖ := by rw [hval, norm_star]
    rw [hnorm]
    calc ‖(inner ℂ X w : ℂ)‖ ^ 2 ≤ (‖X‖ * ‖w‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm X w) 2
      _ = ‖w‖ ^ 2 * ‖X‖ ^ 2 := by ring
  have hquad : star x ⬝ᵥ ((1 - outerProduct a - outerProduct b) *ᵥ x)
      = (((‖X‖ ^ 2 - ‖star (⇑a) ⬝ᵥ x‖ ^ 2 - ‖star (⇑b) ⬝ᵥ x‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, quad_outerProduct, hxx]
    push_cast; ring
  rw [hquad]
  refine Complex.zero_le_real.mpr ?_
  nlinarith [hCS a, hCS b, sq_nonneg ‖X‖, norm_nonneg (star (⇑a) ⬝ᵥ x),
    norm_nonneg (star (⇑b) ⬝ᵥ x)]

/-! ### G — `p`-level homogeneity of the rank-one form (Route B step 3b) -/

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **Homogeneity of the rank-one value.** `p(|c·v⟩⟨c·v|) = c² · p(|v⟩⟨v|)` for real `c ∈ [0,1]`
and `‖v‖ ≤ 1`: `|c·v⟩⟨c·v| = c² • |v⟩⟨v| = Effect.smul c² |v⟩⟨v|`, then apply `p_smul_homog`.
The degree-2 homogeneity of the quadratic form `v ↦ p(|v⟩⟨v|)`. -/
theorem p_outerEffect_smul (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (v : EuclideanSpace ℂ (Fin N)) (hv : ‖v‖ ≤ 1) :
    OP.p (outerEffect ((c : ℂ) • v)
        (by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
            exact le_trans (mul_le_of_le_one_left (norm_nonneg v) hc1) hv))
      = c ^ 2 * OP.p (outerEffect v hv) := by
  have hsq : (c ^ 2 : ℝ) ≤ 1 := by nlinarith
  have heq : outerEffect ((c : ℂ) • v)
      (by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
          exact le_trans (mul_le_of_le_one_left (norm_nonneg v) hc1) hv)
      = Effect.smul (c ^ 2) (by positivity) hsq (outerEffect v hv) := by
    refine Effect.ext_M ?_
    rw [outerEffect_M, Effect.smul_M, outerEffect_M, outerProduct_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]; push_cast; ring
  rw [heq, OP.p_smul_homog (by positivity) hsq]

/-- **`p` depends only on the vector, not the norm-bound proof.** For equal vectors, the
`outerEffect` values (and hence their `p`) agree. -/
theorem p_congr_outerEffect {w v : EuclideanSpace ℂ (Fin N)} (h : w = v)
    (hw : ‖w‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    OP.p (outerEffect w hw) = OP.p (outerEffect v hv) := by
  subst h; rfl

/-- **`√2`-doubling of the rank-one value.** `p(|√2·v⟩⟨√2·v|) = 2·p(|v⟩⟨v|)`. Inverts
`p_outerEffect_smul` at `c = 1/√2`: `|v⟩⟨v| = ½·|√2·v⟩⟨√2·v|`. -/
theorem p_outerEffect_sqrt2 (v : EuclideanSpace ℂ (Fin N)) (hv : ‖v‖ ≤ 1)
    (hsv : ‖(Real.sqrt 2 : ℂ) • v‖ ≤ 1) :
    OP.p (outerEffect ((Real.sqrt 2 : ℂ) • v) hsv) = 2 * OP.p (outerEffect v hv) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc0 : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hc1 : (1 / Real.sqrt 2 : ℝ) ≤ 1 := by
    rw [div_le_one hs2]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hinv : ((1 / Real.sqrt 2 : ℝ) : ℂ) • ((Real.sqrt 2 : ℂ) • v) = v := by
    rw [smul_smul, ← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (ne_of_gt hs2),
      Complex.ofReal_one, one_smul]
  have key := OP.p_outerEffect_smul (1 / Real.sqrt 2) hc0 hc1 ((Real.sqrt 2 : ℂ) • v) hsv
  rw [OP.p_congr_outerEffect hinv _ hv] at key
  rw [key]
  have : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [this]; ring

/-- **The `p`-level parallelogram law (Route B step 3b).** For `‖u‖² + ‖v‖² ≤ ½`,
`p(|u+v⟩⟨u+v|) + p(|u−v⟩⟨u−v|) = 2·p(|u⟩⟨u|) + 2·p(|v⟩⟨v|)`. The matrix parallelogram identity
(`outerProduct_parallelogram`) makes the two effect-sums equal; additivity (with the CS sum
bound as the `≤ I` hypothesis) + the `√2`-doubling homogeneity give the scalar `2`s. This is the
property that forces the diagonal form `v ↦ p(|v⟩⟨v|)` to come from a sesquilinear form. -/
theorem p_parallelogram {u v : EuclideanSpace ℂ (Fin N)}
    (huv : ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hpv : ‖u + v‖ ≤ 1) (hmv : ‖u - v‖ ≤ 1) :
    OP.p (outerEffect (u + v) hpv) + OP.p (outerEffect (u - v) hmv)
      = 2 * OP.p (outerEffect u hu) + 2 * OP.p (outerEffect v hv) := by
  -- the norm parallelogram: ‖u+v‖² + ‖u−v‖² = 2(‖u‖²+‖v‖²) ≤ 1
  have hnormpar : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := parallelogram_law_with_norm ℝ u v
  have hsum_le : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 ≤ 1 := by rw [hnormpar]; linarith
  -- √2-scaled vectors and their sub-unit bounds
  have hsu : ‖(Real.sqrt 2 : ℂ) • u‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), norm_nonneg u, Real.sqrt_nonneg 2, huv]
  have hsv : ‖(Real.sqrt 2 : ℂ) • v‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), norm_nonneg v, Real.sqrt_nonneg 2, huv]
  -- the two effect-sums share a matrix (parallelogram identity), so their p agree
  have hM : outerProduct (u + v) + outerProduct (u - v)
      = outerProduct ((Real.sqrt 2 : ℂ) • u) + outerProduct ((Real.sqrt 2 : ℂ) • v) := by
    rw [outerProduct_parallelogram u v, outerProduct_smul, outerProduct_smul]
    have h2 : (Real.sqrt 2 : ℂ) * star (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [h2]
  have hLe1 : (1 - ((outerEffect (u + v) hpv).M + (outerEffect (u - v) hmv).M)).PosSemidef := by
    rw [outerEffect_M, outerEffect_M, sub_add_eq_sub_sub]
    exact one_sub_two_outerProduct_posSemidef hsum_le
  have hLe2 : (1 - ((outerEffect ((Real.sqrt 2 : ℂ) • u) hsu).M
      + (outerEffect ((Real.sqrt 2 : ℂ) • v) hsv).M)).PosSemidef := by
    rw [outerEffect_M, outerEffect_M, ← hM]; rw [outerEffect_M, outerEffect_M] at hLe1; exact hLe1
  have hadd1 := OP.additivity (outerEffect (u + v) hpv) (outerEffect (u - v) hmv) hLe1
  have hadd2 := OP.additivity (outerEffect ((Real.sqrt 2 : ℂ) • u) hsu)
    (outerEffect ((Real.sqrt 2 : ℂ) • v) hsv) hLe2
  have hsame : Effect.add (outerEffect (u + v) hpv) (outerEffect (u - v) hmv) hLe1
      = Effect.add (outerEffect ((Real.sqrt 2 : ℂ) • u) hsu)
          (outerEffect ((Real.sqrt 2 : ℂ) • v) hsv) hLe2 :=
    Effect.ext_M (by simp only [Effect.add, outerEffect_M]; exact hM)
  rw [hsame] at hadd1
  rw [hadd1] at hadd2
  -- hadd2 : p(oe(u+v)) + p(oe(u-v)) = p(oe(√2 u)) + p(oe(√2 v))
  rw [hadd2, OP.p_outerEffect_sqrt2 u hu hsu, OP.p_outerEffect_sqrt2 v hv hsv]

end OperationalPackage

/-! ### H — the global quadratic form `q v = ‖v‖² · p(|v̂⟩⟨v̂|)` (Route B step 3b-final)

`p (outerEffect v ·)` lives only on the sub-unit ball, while the polarisation argument needs a
quadratic form defined on all vectors (the combinations `u ± v`, `u ± i·v` leave the ball). The
degree-2 homogeneous extension `q` supplies it: it agrees with `p ∘ outerEffect` where the
latter is defined (`qform_eq_p`), so the sub-unit `p_parallelogram` becomes the *unrestricted*
parallelogram law (`qform_parallelogram`). -/

/-- The normalised representative `‖v‖⁻¹ • v` is sub-unit (norm `1` unless `v = 0`). -/
theorem norm_inv_norm_smul_le_one (v : EuclideanSpace ℂ (Fin N)) :
    ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ ≤ 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖⁻¹)]
  rcases eq_or_ne v 0 with rfl | hne
  · simp
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- **`|c·v⟩⟨c·v| = |v⟩⟨v|` for a phase `‖c‖ = 1`.** -/
theorem outerProduct_smul_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ (Fin N)) :
    outerProduct (c • v) = outerProduct v := by
  rw [outerProduct_smul, ← starRingEnd_apply, RCLike.mul_conj, hc]
  simp

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **`p` on `outerEffect` depends only on the matrix `|v⟩⟨v|`.** -/
theorem p_outerEffect_congr_M {w v : EuclideanSpace ℂ (Fin N)}
    (h : outerProduct w = outerProduct v) (hw : ‖w‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    OP.p (outerEffect w hw) = OP.p (outerEffect v hv) := by
  rw [show outerEffect w hw = outerEffect v hv from Effect.ext_M h]

/-- **The global quadratic form** `q v = ‖v‖² · p(|v̂⟩⟨v̂|)`, `v̂ = ‖v‖⁻¹ • v`.

`p (outerEffect v ·)` is defined only for `‖v‖ ≤ 1`; the reconstruction needs a quadratic form
on *all* of `EuclideanSpace ℂ (Fin N)`. The formula gives `q 0 = 0` automatically (the `‖v‖²`
factor), agrees with `p ∘ outerEffect` on the sub-unit ball (`qform_eq_p`), and is degree-2
homogeneous under arbitrary complex scaling (`qform_smul`). -/
noncomputable def qform (v : EuclideanSpace ℂ (Fin N)) : ℝ :=
  ‖v‖ ^ 2 * OP.p (outerEffect (((‖v‖⁻¹ : ℝ) : ℂ) • v) (norm_inv_norm_smul_le_one v))

/-- `0 ≤ q v` (from `OP.nonneg`). -/
theorem qform_nonneg (v : EuclideanSpace ℂ (Fin N)) : 0 ≤ OP.qform v :=
  mul_nonneg (by positivity) (OP.nonneg _)

/-- `q v ≤ ‖v‖²` (from `OP.le_one`). With `qform_nonneg` this is the local bound feeding the
Cauchy-equation argument in `qpolar_smul_real`. -/
theorem qform_le_normSq (v : EuclideanSpace ℂ (Fin N)) : OP.qform v ≤ ‖v‖ ^ 2 := by
  have h1 := OP.le_one (outerEffect (((‖v‖⁻¹ : ℝ) : ℂ) • v) (norm_inv_norm_smul_le_one v))
  have h2 : (0:ℝ) ≤ ‖v‖ ^ 2 := by positivity
  calc OP.qform v ≤ ‖v‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = ‖v‖ ^ 2 := mul_one _

/-- `q 0 = 0`. -/
@[simp] theorem qform_zero : OP.qform (0 : EuclideanSpace ℂ (Fin N)) = 0 := by simp [qform]

/-- **Degree-2 homogeneity of `q` under complex scaling:** `q(c • v) = ‖c‖² · q v`. The modulus
of `c` scales the `‖v‖²` prefactor; its phase is invisible to `|v⟩⟨v|`
(`outerProduct_smul_of_norm_one`). -/
theorem qform_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin N)) :
    OP.qform (c • v) = ‖c‖ ^ 2 * OP.qform v := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hphase : ‖((‖c‖⁻¹ : ℝ) : ℂ) * c‖ = 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖c‖⁻¹), inv_mul_cancel₀ hcn]
  have h1 : ((‖c • v‖⁻¹ : ℝ) : ℂ) • (c • v)
      = (((‖c‖⁻¹ : ℝ) : ℂ) * c) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) := by
    rw [smul_smul, smul_smul, norm_smul, mul_inv]
    congr 1
    push_cast
    ring
  have h2 : outerProduct (((‖c • v‖⁻¹ : ℝ) : ℂ) • (c • v))
      = outerProduct (((‖v‖⁻¹ : ℝ) : ℂ) • v) := by
    rw [h1, outerProduct_smul_of_norm_one hphase]
  simp only [qform]
  rw [OP.p_outerEffect_congr_M h2 (norm_inv_norm_smul_le_one _) (norm_inv_norm_smul_le_one v),
    norm_smul]
  ring

/-- **`q` agrees with `p ∘ outerEffect` on the sub-unit ball:** `q v = p(|v⟩⟨v|)` for `‖v‖ ≤ 1`.
The bridge between the global quadratic form and the operational data (`p_outerEffect_smul` at
`c = ‖v‖`). -/
theorem qform_eq_p {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ ≤ 1) :
    OP.qform v = OP.p (outerEffect v hv) := by
  rcases eq_or_ne v 0 with rfl | hne
  · have h0 : outerEffect (0 : EuclideanSpace ℂ (Fin N)) hv = Effect.zero := by
      refine Effect.ext_M ?_
      ext i j
      simp [outerEffect, outerProduct, Matrix.vecMulVec_apply, Effect.zero]
    rw [h0, OP.p_zero, qform_zero]
  · have hpos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hne
    have hkey := OP.p_outerEffect_smul ‖v‖ (le_of_lt hpos) hv
      (((‖v‖⁻¹ : ℝ) : ℂ) • v) (norm_inv_norm_smul_le_one v)
    have heq : ((‖v‖ : ℝ) : ℂ) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) = v := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hpos),
        Complex.ofReal_one, one_smul]
    rw [OP.p_congr_outerEffect heq _ hv] at hkey
    rw [qform, ← hkey]

/-- **`q` is even:** `q(−v) = q v` (the unit phase `−1`). -/
theorem qform_neg (v : EuclideanSpace ℂ (Fin N)) : OP.qform (-v) = OP.qform v := by
  have := OP.qform_smul (-1) v
  simpa using this

/-- **The unrestricted parallelogram law for `q`.** `q(u+v) + q(u−v) = 2 q u + 2 q v` for *all*
`u, v` — the sub-unit `p_parallelogram` transported off the ball by scaling both vectors down by
`t = (2(1+‖u‖+‖v‖))⁻¹` and dividing out `t²` (`qform_smul`). This is the hypothesis of the
Jordan–von Neumann argument below. -/
theorem qform_parallelogram (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qform (u + v) + OP.qform (u - v) = 2 * OP.qform u + 2 * OP.qform v := by
  set t : ℝ := (2 * (1 + ‖u‖ + ‖v‖))⁻¹ with ht
  have hden : (0:ℝ) < 2 * (1 + ‖u‖ + ‖v‖) := by positivity
  have htpos : 0 < t := inv_pos.mpr hden
  have hnt : ‖((t : ℝ) : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hu2 : ‖((t : ℝ) : ℂ) • u‖ ≤ 1/2 := by
    rw [norm_smul, hnt, ht, inv_mul_eq_div, div_le_iff₀ hden]
    nlinarith [norm_nonneg u, norm_nonneg v]
  have hv2 : ‖((t : ℝ) : ℂ) • v‖ ≤ 1/2 := by
    rw [norm_smul, hnt, ht, inv_mul_eq_div, div_le_iff₀ hden]
    nlinarith [norm_nonneg u, norm_nonneg v]
  have hsum : ‖((t : ℝ) : ℂ) • u‖ ^ 2 + ‖((t : ℝ) : ℂ) • v‖ ^ 2 ≤ 1/2 := by
    nlinarith [norm_nonneg (((t : ℝ) : ℂ) • u), norm_nonneg (((t : ℝ) : ℂ) • v)]
  have hu1 : ‖((t : ℝ) : ℂ) • u‖ ≤ 1 := by linarith
  have hv1 : ‖((t : ℝ) : ℂ) • v‖ ≤ 1 := by linarith
  have hpv : ‖((t : ℝ) : ℂ) • u + ((t : ℝ) : ℂ) • v‖ ≤ 1 :=
    le_trans (norm_add_le _ _) (by linarith)
  have hmv : ‖((t : ℝ) : ℂ) • u - ((t : ℝ) : ℂ) • v‖ ≤ 1 :=
    le_trans (norm_sub_le _ _) (by linarith)
  have key := OP.p_parallelogram hsum hu1 hv1 hpv hmv
  rw [← OP.qform_eq_p hpv, ← OP.qform_eq_p hmv, ← OP.qform_eq_p hu1,
    ← OP.qform_eq_p hv1] at key
  rw [show ((t : ℝ) : ℂ) • u + ((t : ℝ) : ℂ) • v = ((t : ℝ) : ℂ) • (u + v) from
      (smul_add _ _ _).symm,
    show ((t : ℝ) : ℂ) • u - ((t : ℝ) : ℂ) • v = ((t : ℝ) : ℂ) • (u - v) from
      (smul_sub _ _ _).symm,
    OP.qform_smul, OP.qform_smul, OP.qform_smul, OP.qform_smul, hnt] at key
  have ht2 : t ^ 2 ≠ 0 := by positivity
  refine mul_left_cancel₀ ht2 ?_
  linear_combination key

end OperationalPackage

/-! ### I — Cauchy's functional equation with a local bound (Route B step 3b-final)

The Jordan–von Neumann polarisation gives additivity of `f u v = q(u+v) − q(u−v)` in each slot,
hence `ℚ`-homogeneity. Upgrading to `ℝ`-homogeneity is where the classical proof invokes
continuity — unavailable here, since `p` is an arbitrary probability assignment. Boundedness is
the substitute: `0 ≤ q ≤ ‖·‖²` bounds `f` on the unit ball, and a bounded additive function on
`ℝ` is linear. -/

/-- **Cauchy's functional equation with a local bound.** An additive `g : ℝ → ℝ` that is bounded
on `[-1,1]` is linear: `g t = t · g 1`.

No continuity is assumed (and none is available: `p` is an arbitrary probability assignment).
The proof is the classical squeeze on `h y = g y − y · g 1`: `h` is additive, kills every
integer (`h m = m · h 1 = 0`), and is bounded on `[-1,1]`; for any `x` and any `n ≥ 1`,
`n · h x = h (n x − ⌊n x⌋)` lands in that bounded window, so `|h x| ≤ (M + |g 1|)/n → 0`.

Used by `OperationalPackage.qpolar_smul_real`, where the local bound comes from `qform_nonneg`
and `qform_le_normSq`. -/
theorem additive_bounded_linear (g : ℝ → ℝ) (hadd : ∀ s t : ℝ, g (s + t) = g s + g t)
    {M : ℝ} (hM : ∀ t : ℝ, |t| ≤ 1 → |g t| ≤ M) (x : ℝ) : g x = x * g 1 := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ y, h y = g y - y * g 1 := ⟨_, fun _ => rfl⟩
  have hadd' : ∀ s t : ℝ, h (s + t) = h s + h t := by
    intro s t; rw [hh, hh, hh, hadd s t]; ring
  have hzero : h 0 = 0 := by
    have h0 := hadd' 0 0; rw [add_zero] at h0; linarith
  have hone : h 1 = 0 := by rw [hh]; ring
  have hnat : ∀ (n : ℕ) (y : ℝ), h ((n : ℝ) * y) = (n : ℝ) * h y := by
    intro n
    induction n with
    | zero => intro y; simp [hzero]
    | succ k ih =>
      intro y
      have hstep : ((k + 1 : ℕ) : ℝ) * y = (k : ℝ) * y + y := by push_cast; ring
      rw [hstep, hadd', ih]; push_cast; ring
  have hneg : ∀ y : ℝ, h (-y) = - h y := by
    intro y
    have hy := hadd' y (-y)
    rw [add_neg_cancel, hzero] at hy
    linarith
  have hnatz : ∀ n : ℕ, h ((n : ℝ)) = 0 := by
    intro n
    have hn := hnat n 1
    rw [mul_one, hone, mul_zero] at hn
    exact hn
  have hint : ∀ m : ℤ, h ((m : ℝ)) = 0 := by
    intro m
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = n ∨ m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    rcases hn with hn | hn
    · subst hn; exact_mod_cast hnatz n
    · subst hn
      have hcast : (((-(n : ℤ)) : ℤ) : ℝ) = -((n : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, hneg, hnatz n, neg_zero]
  have hM' : ∀ y : ℝ, |y| ≤ 1 → |h y| ≤ M + |g 1| := by
    intro y hy
    have h1 : |h y| ≤ |g y| + |y * g 1| := by
      rw [hh]
      have hg1 := le_abs_self (g y)
      have hg2 := neg_abs_le (g y)
      have hy1 := le_abs_self (y * g 1)
      have hy2 := neg_abs_le (y * g 1)
      rw [abs_le]
      constructor <;> linarith
    have h2 : |y * g 1| ≤ |g 1| := by
      rw [abs_mul]
      nlinarith [abs_nonneg (g 1), abs_nonneg y]
    linarith [hM y hy]
  have hsq : ∀ n : ℕ, 0 < n → |h x| ≤ (M + |g 1|) / n := by
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hr0 : 0 ≤ (n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) := sub_nonneg.mpr (Int.floor_le _)
    have hr1 : (n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) < 1 := by
      have hlt := Int.lt_floor_add_one ((n : ℝ) * x)
      linarith
    have hsplit : h ((n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ)) = (n : ℝ) * h x := by
      have hs := hadd' ((n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ)) (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ))
      have heq : (n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) + ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ)
          = (n : ℝ) * x := by ring
      rw [heq, hint, add_zero] at hs
      rw [← hs, hnat n x]
    have habs : |h ((n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ))| ≤ M + |g 1| :=
      hM' _ (by rw [abs_of_nonneg hr0]; linarith)
    rw [hsplit, abs_mul, abs_of_pos hn0] at habs
    rw [le_div_iff₀ hn0]
    linarith
  have hMnn : (0:ℝ) ≤ M := le_trans (abs_nonneg (g 0)) (hM 0 (by norm_num))
  have hx0 : h x = 0 := by
    by_contra hne
    have hpos : 0 < |h x| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt ((M + |g 1|) / |h x|)
    have hq : (0:ℝ) ≤ (M + |g 1|) / |h x| := by positivity
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exfalso; rw [Nat.cast_zero] at hn; linarith
      · exact hp
    have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
    have hb := hsq n hnpos
    rw [div_lt_iff₀ hpos] at hn
    rw [le_div_iff₀ hn0] at hb
    nlinarith
  rw [hh] at hx0
  linarith

/-! ### J — the polarisation difference `f u v = q(u+v) − q(u−v)` (Route B step 3b-final) -/

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **The polarisation difference** `f u v = q(u+v) − q(u−v)` — four times the real part of the
sesquilinear form being reconstructed. Symmetric (`qpolar_symm`), additive (`qpolar_add_left`)
and `ℝ`-homogeneous (`qpolar_smul_real`) in each slot. -/
noncomputable def qpolar (u v : EuclideanSpace ℂ (Fin N)) : ℝ :=
  OP.qform (u + v) - OP.qform (u - v)

/-- `f` is symmetric: `q(v−u) = q(−(u−v)) = q(u−v)`. -/
theorem qpolar_symm (u v : EuclideanSpace ℂ (Fin N)) : OP.qpolar u v = OP.qpolar v u := by
  have h : v - u = -(u - v) := by abel
  rw [qpolar, qpolar, h, OP.qform_neg, add_comm]

/-- `f 0 v = q v − q(−v) = 0` (evenness of `q`). -/
theorem qpolar_zero_left (v : EuclideanSpace ℂ (Fin N)) : OP.qpolar 0 v = 0 := by
  rw [qpolar, zero_add, zero_sub, OP.qform_neg, sub_self]

/-- `f u (−v) = − f u v` (the two `q`-terms swap). -/
theorem qpolar_neg_right (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qpolar u (-v) = - OP.qpolar u v := by
  rw [qpolar, qpolar, ← sub_eq_add_neg, sub_neg_eq_add]; ring

/-- **The halving identity (Jordan–von Neumann core).** `f u v + f w v = 2 · f ((u+w)/2) v`:
apply the parallelogram law at `(a ± v, b)` with `a = (u+w)/2`, `b = (u−w)/2` (so `a + b = u`
and `a − b = w`) and subtract the two instances — the `q b` terms cancel. -/
private theorem qpolar_add_half (u w v : EuclideanSpace ℂ (Fin N)) :
    OP.qpolar u v + OP.qpolar w v = 2 * OP.qpolar (((2:ℂ)⁻¹) • (u + w)) v := by
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  set a : EuclideanSpace ℂ (Fin N) := ((2:ℂ)⁻¹) • (u + w) with ha
  set b : EuclideanSpace ℂ (Fin N) := ((2:ℂ)⁻¹) • (u - w) with hb
  have hab1 : a + b = u := by
    rw [ha, hb, ← smul_add, show (u + w) + (u - w) = (2:ℂ) • u from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hab2 : a - b = w := by
    rw [ha, hb, ← smul_sub, show (u + w) - (u - w) = (2:ℂ) • w from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have par1 := OP.qform_parallelogram (a + v) b
  have par2 := OP.qform_parallelogram (a - v) b
  rw [show a + v + b = u + v from by rw [← hab1]; abel,
    show a + v - b = w + v from by rw [← hab2]; abel] at par1
  rw [show a - v + b = u - v from by rw [← hab1]; abel,
    show a - v - b = w - v from by rw [← hab2]; abel] at par2
  simp only [qpolar]
  linarith

/-- **Additivity of the polarisation difference in the first slot.** `f (u+w) v = f u v + f w v`:
the halving identity at `(u, w)` and at `(u+w, 0)` (where `f 0 v = 0`) share a right-hand
side. -/
theorem qpolar_add_left (u w v : EuclideanSpace ℂ (Fin N)) :
    OP.qpolar (u + w) v = OP.qpolar u v + OP.qpolar w v := by
  have h1 := OP.qpolar_add_half u w v
  have h2 := OP.qpolar_add_half (u + w) 0 v
  simp only [OP.qpolar_zero_left, add_zero] at h2
  linarith

/-- **Real homogeneity of the polarisation difference in the first slot.** `f (t • u) v =
t · f u v` for every *real* `t`. Additivity alone gives only `ℚ`-homogeneity; the upgrade to `ℝ`
is `additive_bounded_linear`, whose local bound is `0 ≤ q ≤ ‖·‖²` (`qform_nonneg`,
`qform_le_normSq`) — no continuity of `p` is needed or available. -/
theorem qpolar_smul_real (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qpolar (((t : ℝ) : ℂ) • u) v = t * OP.qpolar u v := by
  have hadd : ∀ s r : ℝ, OP.qpolar ((((s + r : ℝ)) : ℂ) • u) v
      = OP.qpolar (((s : ℝ) : ℂ) • u) v + OP.qpolar (((r : ℝ) : ℂ) • u) v := by
    intro s r
    rw [show (((s + r : ℝ)) : ℂ) • u = ((s : ℝ) : ℂ) • u + ((r : ℝ) : ℂ) • u from by
      push_cast; rw [add_smul], OP.qpolar_add_left]
  have hbound : ∀ s : ℝ, |s| ≤ 1 → |OP.qpolar (((s : ℝ) : ℂ) • u) v| ≤ (‖u‖ + ‖v‖) ^ 2 := by
    intro s hs
    have hsn : ‖((s : ℝ) : ℂ) • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg u, abs_nonneg s]
    have hp : ‖((s:ℝ):ℂ) • u + v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_add_le _ _) (by linarith)
    have hm : ‖((s:ℝ):ℂ) • u - v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_sub_le _ _) (by linarith)
    have h1 := OP.qform_nonneg (((s:ℝ):ℂ) • u + v)
    have h2 := OP.qform_nonneg (((s:ℝ):ℂ) • u - v)
    have h3 := OP.qform_le_normSq (((s:ℝ):ℂ) • u + v)
    have h4 := OP.qform_le_normSq (((s:ℝ):ℂ) • u - v)
    rw [abs_le, qpolar]
    constructor
    · nlinarith [norm_nonneg (((s:ℝ):ℂ) • u - v), norm_nonneg u, norm_nonneg v]
    · nlinarith [norm_nonneg (((s:ℝ):ℂ) • u + v), norm_nonneg u, norm_nonneg v]
  have hlin := additive_bounded_linear (fun s : ℝ => OP.qpolar (((s : ℝ) : ℂ) • u) v) hadd
    hbound t
  simpa using hlin

end OperationalPackage

/-! ### K — the polarised sesquilinear form `S` (Route B step 3b-final)

With `f` bi-additive and `ℝ`-bihomogeneous, the complex polarisation
`S(u,v) = ¼ f(u,v) − (i/4) f(u, i·v)` is sesquilinear: linear in `v` (the `i`-homogeneity
`S(u, i·v) = i·S(u,v)` is pure algebra of the formula), conjugate-linear in `u` by conjugate
symmetry, and `S(v,v) = q v`. -/

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **The polarised sesquilinear form.**
`S(u,v) = ¼ f(u,v) − (i/4) f(u, i·v)`, the complex polarisation of `q`. It is additive
(`qsesq_add_right`) and `ℂ`-homogeneous (`qsesq_smul_right`) in `v`, conjugate-symmetric
(`qsesq_conj_symm`), and restricts to `q` on the diagonal (`qsesq_self`) — exactly the
sesquilinear form whose matrix is the density operator Busch's theorem asserts. -/
noncomputable def qsesq (u v : EuclideanSpace ℂ (Fin N)) : ℂ :=
  ((OP.qpolar u v : ℝ) : ℂ) / 4 - Complex.I * ((OP.qpolar u (Complex.I • v) : ℝ) : ℂ) / 4

/-- `S(u, 0) = 0`. -/
theorem qsesq_zero_right (u : EuclideanSpace ℂ (Fin N)) : OP.qsesq u 0 = 0 := by
  simp [qsesq, qpolar]

/-- Additivity of `f` in the second slot (by symmetry from `qpolar_add_left`). -/
theorem qpolar_add_right (u v w : EuclideanSpace ℂ (Fin N)) :
    OP.qpolar u (v + w) = OP.qpolar u v + OP.qpolar u w := by
  rw [OP.qpolar_symm u (v + w), OP.qpolar_add_left, OP.qpolar_symm v u, OP.qpolar_symm w u]

/-- Real homogeneity of `f` in the second slot (by symmetry from `qpolar_smul_real`). -/
theorem qpolar_smul_real_right (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qpolar u (((t : ℝ) : ℂ) • v) = t * OP.qpolar u v := by
  rw [OP.qpolar_symm u (((t : ℝ) : ℂ) • v), OP.qpolar_smul_real, OP.qpolar_symm v u]

/-- **Additivity of `S` in the second slot.** -/
theorem qsesq_add_right (u v w : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq u (v + w) = OP.qsesq u v + OP.qsesq u w := by
  simp only [qsesq, smul_add, OP.qpolar_add_right]
  push_cast
  ring

/-- **Real homogeneity of `S` in the second slot.** -/
theorem qsesq_smul_real_right (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq u (((t : ℝ) : ℂ) • v) = (t : ℂ) * OP.qsesq u v := by
  have hcomm : Complex.I • (((t : ℝ) : ℂ) • v) = ((t : ℝ) : ℂ) • (Complex.I • v) :=
    smul_comm _ _ _
  simp only [qsesq, hcomm, OP.qpolar_smul_real_right]
  push_cast
  ring

/-- **`S(u, i·v) = i · S(u,v)`** — pure algebra of the polarisation formula (`i·(i·v) = −v`),
no additivity needed. -/
theorem qsesq_smul_I_right (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq u (Complex.I • v) = Complex.I * OP.qsesq u v := by
  have hII : Complex.I • (Complex.I • v) = -v := by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  simp only [qsesq, hII, OP.qpolar_neg_right]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Complex homogeneity in the second slot:** `S(u, c•v) = c · S(u,v)`. Split
`c = Re c + i · Im c` and combine `qsesq_smul_real_right` with `qsesq_smul_I_right`. -/
theorem qsesq_smul_right (c : ℂ) (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq u (c • v) = c * OP.qsesq u v := by
  have hdecomp : c • v = ((c.re : ℝ) : ℂ) • v + ((c.im : ℝ) : ℂ) • (Complex.I • v) := by
    rw [smul_smul, ← add_smul]
    congr 1
    exact (Complex.re_add_im c).symm
  rw [hdecomp, OP.qsesq_add_right, OP.qsesq_smul_real_right, OP.qsesq_smul_real_right,
    OP.qsesq_smul_I_right]
  have hc : ((c.re : ℝ) : ℂ) + ((c.im : ℝ) : ℂ) * Complex.I = c := Complex.re_add_im c
  linear_combination OP.qsesq u v * hc

/-- **Conjugate symmetry:** `S(v,u) = conj (S(u,v))`. The real part is symmetric
(`qpolar_symm`); the imaginary part flips because `q(v ± i·u) = q(u ∓ i·v)` (multiply by the
unit phase `∓i` and use `qform_smul`). With `qsesq_smul_right` this makes `S` conjugate-linear
in its *first* slot. -/
theorem qsesq_conj_symm (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq v u = (starRingEnd ℂ) (OP.qsesq u v) := by
  have h1 : OP.qform (v + Complex.I • u) = OP.qform (u - Complex.I • v) := by
    have hI : Complex.I • (u - Complex.I • v) = v + Complex.I • u := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add, add_comm]
    rw [← hI, OP.qform_smul]
    simp
  have h2 : OP.qform (v - Complex.I • u) = OP.qform (u + Complex.I • v) := by
    have hI : (-Complex.I) • (u + Complex.I • v) = v - Complex.I • u := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [← hI, OP.qform_smul]
    simp
  have hpol : OP.qpolar v (Complex.I • u) = - OP.qpolar u (Complex.I • v) := by
    simp only [qpolar, h1, h2]
    ring
  simp only [qsesq, OP.qpolar_symm v u, hpol]
  simp only [map_sub, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- **`S` restricts to `q` on the diagonal:** `S(v,v) = q v`. The diagonal value is
`f v v = 4 q v` (degree-2 homogeneity at `2`), and the imaginary term vanishes because
`q(v − i·v) = q(v + i·v)` (unit phase `−i`). -/
theorem qsesq_self (v : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq v v = ((OP.qform v : ℝ) : ℂ) := by
  have hdiag : OP.qpolar v v = 4 * OP.qform v := by
    have h2 : v + v = ((2 : ℝ) : ℂ) • v := by push_cast; rw [two_smul]
    have hn2 : ‖((2 : ℝ) : ℂ)‖ ^ 2 = 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [qpolar, h2, OP.qform_smul, hn2, sub_self, OP.qform_zero, sub_zero]
  have hIv : OP.qpolar v (Complex.I • v) = 0 := by
    have hneg : (-Complex.I) • (v + Complex.I • v) = v - Complex.I • v := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [qpolar, ← hneg, OP.qform_smul]
    simp
  rw [qsesq, hdiag, hIv]
  push_cast
  ring

end OperationalPackage

/-! ### L — the reconstructed matrix `R` and the representation theorem (Route B step 3b-final)

`R j k := S(eⱼ, eₖ)` on the standard basis. Sesquilinearity turns the basis expansion of `v`
into `q v = ⟨v, R v⟩ = Tr(R · |v⟩⟨v|)`, i.e. `p(|v⟩⟨v|) = Tr(R · |v⟩⟨v|)`; the spectral
reduction lifts this to `p E = Tr(R · E)` for every effect. -/

/-- **Standard-basis expansion in `EuclideanSpace`:** `v = ∑ᵢ vᵢ • eᵢ`. -/
theorem euclidean_sum_single (v : EuclideanSpace ℂ (Fin N)) :
    ∑ i, (v i) • (EuclideanSpace.single i (1:ℂ)) = v := by
  ext j
  simp
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **`Tr(R · |v⟩⟨v|) = ⟨v, R v⟩`.** The trace pairing against a rank-one projector is the
quadratic form of `R` — the identity turning the sesquilinear reconstruction into the
Born-style trace formula. -/
theorem trace_mul_outerProduct (R : Matrix (Fin N) (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    (R * outerProduct v).trace = star (⇑v) ⬝ᵥ (R *ᵥ (⇑v)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct,
    Matrix.vecMulVec_apply, dotProduct, Pi.star_apply, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **`S` is linear over finite sums in the second slot.** -/
theorem qsesq_sum_right {ι : Type*} (u : EuclideanSpace ℂ (Fin N)) (s : Finset ι) (c : ι → ℂ)
    (e : ι → EuclideanSpace ℂ (Fin N)) :
    OP.qsesq u (∑ i ∈ s, c i • e i) = ∑ i ∈ s, c i * OP.qsesq u (e i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [OP.qsesq_zero_right]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, OP.qsesq_add_right, OP.qsesq_smul_right, ih]

/-- **`S` is conjugate-linear over finite sums in the first slot** (via `qsesq_conj_symm`). -/
theorem qsesq_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → EuclideanSpace ℂ (Fin N)) (w : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq (∑ i ∈ s, c i • e i) w = ∑ i ∈ s, (starRingEnd ℂ) (c i) * OP.qsesq (e i) w := by
  rw [OP.qsesq_conj_symm w (∑ i ∈ s, c i • e i), OP.qsesq_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  exact (OP.qsesq_conj_symm w (e i)).symm

/-- **The reconstructed matrix** `R j k = S(eⱼ, eₖ)` on the standard basis — the candidate
density operator of Busch's theorem (its positivity and unit trace are step 4). -/
noncomputable def qmatrix : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    OP.qsesq (EuclideanSpace.single j (1:ℂ)) (EuclideanSpace.single k (1:ℂ))

/-- **`R` is Hermitian**, directly from `qsesq_conj_symm`. -/
theorem qmatrix_isHermitian : OP.qmatrix.IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, qmatrix, Matrix.of_apply, Complex.star_def]
  exact (OP.qsesq_conj_symm (EuclideanSpace.single k (1:ℂ))
    (EuclideanSpace.single j (1:ℂ))).symm

/-- **`S` is the sesquilinear form of `R`:** `S(u,v) = ⟨u, R v⟩`. Expand both slots in the
standard basis (`qsesq_sum_left`, `qsesq_sum_right`). -/
theorem qsesq_eq_dotProduct (u v : EuclideanSpace ℂ (Fin N)) :
    OP.qsesq u v = star (⇑u) ⬝ᵥ (OP.qmatrix *ᵥ (⇑v)) := by
  conv_lhs => rw [← euclidean_sum_single u, ← euclidean_sum_single v]
  rw [OP.qsesq_sum_left]
  simp only [OP.qsesq_sum_right, dotProduct, Pi.star_apply, Matrix.mulVec, qmatrix,
    Matrix.of_apply, Finset.mul_sum, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **`q` is the quadratic form of `R`:** `q v = ⟨v, R v⟩`. -/
theorem qform_eq_dotProduct (v : EuclideanSpace ℂ (Fin N)) :
    ((OP.qform v : ℝ) : ℂ) = star (⇑v) ⬝ᵥ (OP.qmatrix *ᵥ (⇑v)) := by
  rw [← OP.qsesq_self v, OP.qsesq_eq_dotProduct]

/-- **The rank-one representation (Route B step 3b-final).** `p(|v⟩⟨v|) = Tr(R · |v⟩⟨v|)` for
every sub-unit `v`: the operational probability of every rank-one effect is a trace against one
fixed Hermitian matrix. This is what the polarisation programme was for. -/
theorem p_outerEffect_eq_trace {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ ≤ 1) :
    ((OP.p (outerEffect v hv) : ℝ) : ℂ) = (OP.qmatrix * outerProduct v).trace := by
  rw [← OP.qform_eq_p hv, OP.qform_eq_dotProduct, trace_mul_outerProduct]

/-- **Full representation on all effects (Route B step 3b-final, capstone).**
`p E = Tr(R · E)` for *every* effect `E` — the rank-one representation lifted through the
spectral reduction (`p_eq_eigen_sum`, `Effect.sum_eigenEffect_M`).

This is the content of Busch's theorem except the *state* conditions on `R`. What remains
(step 4) is `R.PosSemidef` (from `OP.nonneg`), `R.trace = 1` (from `OP.total_one`), and
uniqueness (non-degeneracy of the trace pairing) — which together make `R` a `DensityOperator`
and replace the `busch_effect_gleason` axiom in `LF2/BornWrapper.lean`. -/
theorem p_eq_trace (E : Effect N) :
    ((OP.p E : ℝ) : ℂ) = (OP.qmatrix * E.M).trace := by
  have hE : E.M = ∑ i, (E.isHermitian.eigenvalues i : ℂ)
      • outerProduct (E.isHermitian.eigenvectorBasis i) :=
    (E.sum_eigenEffect_M).symm.trans (Finset.sum_congr rfl fun i _ => Effect.eigenEffect_M E i)
  conv_rhs => rw [hE, Matrix.mul_sum, Matrix.trace_sum]
  rw [OP.p_eq_eigen_sum E]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have hnorm : ‖E.isHermitian.eigenvectorBasis i‖ = 1 :=
    E.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
  rw [← outerEffect_eq_rankOneEffect _ hnorm]
  exact OP.p_outerEffect_eq_trace (le_of_eq hnorm)

end OperationalPackage

/-! ### M — step 4: positivity, normalisation, uniqueness, and the discharged theorem
(Route B step 4, capstone)

The three state conditions on the reconstructed `R = OP.qmatrix`: `R.PosSemidef` (from
`OP.nonneg`), `R.trace = 1` (from `OP.total_one`), and — the only genuinely new argument —
*uniqueness*, from the fact that a complex matrix is determined by its quadratic form
(`matrix_eq_zero_of_quadForm_zero`, a polarisation). Together they package `R` as a
`DensityOperator` and prove `effect_gleason_representation`, the statement the
`busch_effect_gleason` axiom used to assert. -/

/-- **A complex matrix is determined by its quadratic form.** If `star x ⬝ᵥ (D *ᵥ x) = 0` for
every `x`, then `D = 0`. Over `ℂ` the diagonal of a sesquilinear form recovers the whole form by
polarisation, so a vanishing quadratic form forces every entry to vanish. -/
theorem matrix_eq_zero_of_quadForm_zero {D : Matrix (Fin N) (Fin N) ℂ}
    (hQ : ∀ x : Fin N → ℂ, star x ⬝ᵥ (D *ᵥ x) = 0) : D = 0 := by
  have hI : star (Complex.I) = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hB : ∀ u v : Fin N → ℂ, star u ⬝ᵥ (D *ᵥ v) = 0 := by
    intro u v
    have h1 := hQ (u + v)
    have h2 := hQ (u - v)
    have h3 := hQ (u + Complex.I • v)
    have h4 := hQ (u - Complex.I • v)
    simp only [star_add, star_sub, star_smul, hI, mulVec_add, mulVec_sub, Matrix.mulVec_smul,
      add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, neg_mul] at h1 h2 h3 h4
    have key : (4 : ℂ) * (star u ⬝ᵥ (D *ᵥ v)) = 0 := by
      linear_combination h1 - h2 - Complex.I * h3 + Complex.I * h4
        + (2 * (star u ⬝ᵥ (D *ᵥ v)) - 2 * (star v ⬝ᵥ (D *ᵥ u))) * hII
    have h4ne : (4 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp key).resolve_left h4ne
  ext j k
  have hjk := hB (Pi.single j 1) (Pi.single k 1)
  rw [Matrix.mulVec_single_one] at hjk
  simpa [dotProduct, Matrix.col_apply, Pi.single_apply, Finset.sum_ite_eq', eq_comm] using hjk

/-- **The trace of a product of two Hermitian matrices is real.** `Tr(A·B)^conj = Tr(B·A) =
Tr(A·B)`. -/
theorem trace_mul_isHermitian_real {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (starRingEnd ℂ) ((A * B).trace) = (A * B).trace := by
  calc (starRingEnd ℂ) ((A * B).trace)
      = ((A * B)ᴴ).trace := by rw [starRingEnd_apply, ← Matrix.trace_conjTranspose]
    _ = (B * A).trace := by rw [Matrix.conjTranspose_mul, hA.eq, hB.eq]
    _ = (A * B).trace := Matrix.trace_mul_comm _ _

/-- **The trace form lifts to the complex trace.** For a density operator `ρ` and effect `E`
(both Hermitian), `Tr(ρ·E)` is real, so `↑(traceForm ρ E) = Tr(ρ.M·E.M)`. -/
theorem traceForm_ofReal (ρ : DensityOperator N) (E : Effect N) :
    ((traceForm ρ E : ℝ) : ℂ) = (ρ.M * E.M).trace := by
  have him : ((ρ.M * E.M).trace).im = 0 :=
    Complex.conj_eq_iff_im.mp (trace_mul_isHermitian_real ρ.isHermitian E.isHermitian)
  apply Complex.ext
  · simp [traceForm]
  · simp [traceForm, him]

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **Step 4a — the reconstructed matrix is positive semidefinite.** `R.PosSemidef` from
`qform_nonneg` and `qform_eq_dotProduct` (`⟨x, R x⟩ = q x ≥ 0`), with `R` Hermitian. -/
theorem qmatrix_posSemidef : OP.qmatrix.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg OP.qmatrix_isHermitian fun x => ?_
  have hx := OP.qform_eq_dotProduct (WithLp.toLp 2 x)
  have hcoe : ⇑(WithLp.toLp 2 x) = x := rfl
  rw [hcoe] at hx
  rw [← hx]
  exact Complex.zero_le_real.mpr (OP.qform_nonneg _)

/-- **Step 4b — the reconstructed matrix has unit trace.** `R.trace = 1` from `OP.total_one`
(`p I = 1`) and `p_eq_trace` at `E = Effect.one` (`Tr(R · I) = Tr R`). -/
theorem qmatrix_trace_one : OP.qmatrix.trace = 1 := by
  have h := OP.p_eq_trace Effect.one
  rw [OP.total_one] at h
  simpa [Effect.one] using h.symm

/-- **The reconstructed density operator** `R = OP.qmatrix`, packaged with its PSD + unit-trace
witnesses. -/
noncomputable def qdensity : DensityOperator N where
  M := OP.qmatrix
  isHermitian := OP.qmatrix_isHermitian
  nonneg := OP.qmatrix_posSemidef
  trace_one := OP.qmatrix_trace_one

@[simp] lemma qdensity_M : OP.qdensity.M = OP.qmatrix := rfl

/-- **`p` is the trace form of `qdensity`.** From `p_eq_trace` (`↑(p E) = Tr(R·E)`) and
`traceForm_ofReal` (`↑(traceForm ρ E) = Tr(R·E)`), by injectivity of `ℝ ↪ ℂ`. -/
theorem p_eq_traceForm_qdensity (E : Effect N) :
    OP.p E = traceForm OP.qdensity E := by
  have h1 := OP.p_eq_trace E
  have h2 := traceForm_ofReal OP.qdensity E
  rw [qdensity_M] at h2
  exact Complex.ofReal_injective (h1.trans h2.symm)

/-- **Step 4c — uniqueness.** Any density operator whose trace form reproduces `p` on every
effect equals `qdensity`. Their difference `D` is Hermitian with `Tr(D · E) = 0` for every
effect; taking `E = |v⟩⟨v|` (sub-unit) gives `⟨v, D v⟩ = 0` on the whole unit ball, and scaling
+ polarisation (`matrix_eq_zero_of_quadForm_zero`) forces `D = 0`. -/
theorem qdensity_unique (ρ : DensityOperator N)
    (hρ : ∀ E : Effect N, OP.p E = traceForm ρ E) :
    ρ = OP.qdensity := by
  suffices hM : ρ.M = OP.qmatrix by
    obtain ⟨M, _, _, _⟩ := ρ; cases hM; rfl
  set D : Matrix (Fin N) (Fin N) ℂ := ρ.M - OP.qmatrix with hD
  -- `Tr(D · E.M) = 0` for every effect E
  have htr : ∀ E : Effect N, (D * E.M).trace = 0 := by
    intro E
    have e1 : ((OP.p E : ℝ) : ℂ) = (ρ.M * E.M).trace := by
      rw [hρ E]; exact traceForm_ofReal ρ E
    have e2 : ((OP.p E : ℝ) : ℂ) = (OP.qmatrix * E.M).trace := OP.p_eq_trace E
    rw [hD, Matrix.sub_mul, Matrix.trace_sub, ← e1, ← e2, sub_self]
  -- quadratic form of D vanishes on the whole space
  have hquad : ∀ x : Fin N → ℂ, star x ⬝ᵥ (D *ᵥ x) = 0 := by
    intro x
    set X : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 x with hX
    set t : ℝ := (1 + ‖X‖)⁻¹ with ht
    have htpos : 0 < t := by positivity
    have hle : ‖((t : ℝ) : ℂ) • X‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht,
        inv_mul_eq_div, div_le_one (by positivity)]
      linarith [norm_nonneg X]
    have hE := htr (outerEffect (((t : ℝ) : ℂ) • X) hle)
    rw [outerEffect_M, trace_mul_outerProduct] at hE
    have hcoe : ⇑(((t : ℝ) : ℂ) • X) = ((t : ℝ) : ℂ) • x := rfl
    rw [hcoe, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul] at hE
    have htne : ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, or_self]
      exact ne_of_gt htpos
    exact (mul_eq_zero.mp hE).resolve_left htne
  have hDzero : D = 0 := matrix_eq_zero_of_quadForm_zero hquad
  rw [hD] at hDzero
  exact sub_eq_zero.mp hDzero

/-- **Busch effect-Gleason (finite dim), proved.** For every operational package there is a
**unique** density operator `ρ` with `p E = Tr(ρ · E)` for every effect. This discharges the
`busch_effect_gleason` axiom: `qdensity` witnesses existence (`p_eq_traceForm_qdensity`) and
`qdensity_unique` gives uniqueness. -/
theorem effect_gleason_representation (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E :=
  ⟨OP.qdensity, OP.p_eq_traceForm_qdensity, fun ρ hρ => OP.qdensity_unique ρ hρ⟩

end OperationalPackage

/-- **Born-form assignment (spec §5.4 wrapper).** The unique density operator representing an
operational package — now a **theorem** (`effect_gleason_representation`), not an axiom. The
dimension hypothesis `hN : 2 ≤ N` is retained for signature compatibility with the spec and with
downstream callers, though the reconstruction in fact works for every `N`. -/
theorem born_form_of_package
    {N : ℕ} (_hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E :=
  OP.effect_gleason_representation

/-- **Strengthened composite endpoint.** Given only a **purity hypothesis** — that the
operational package assigns probability one to the rank-1 effect through `ψ`, i.e. the
preparation is "certain" to produce `ψ` — the Born quadratic form `|⟨ψ|φ⟩|²` falls out for every
rank-1 outcome. Relocated from `LF2/BornWrapper.lean` (2026-07-21) because it now composes the
**proven** `effect_gleason_representation` (was `busch_effect_gleason`) with
`rankOneDensity_unique_of_certainty` and `born_quadratic`; `hN` is retained for the spec
signature. -/
theorem pure_state_born_weights_of_certainty
    {N : ℕ} (_hN : 2 ≤ N) (OP : OperationalPackage N)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (h_certain : OP.p (rankOneEffect ψ hψ) = 1)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    OP.p (rankOneEffect φ hφ) = ‖inner ℂ ψ φ‖ ^ 2 := by
  obtain ⟨ρ, hρ_spec, _hρ_unique⟩ := OP.effect_gleason_representation
  have hρ_eq : ρ = rankOneDensity ψ hψ := by
    refine rankOneDensity_unique_of_certainty ψ hψ ρ ?_
    rw [← hρ_spec]; exact h_certain
  rw [hρ_spec, hρ_eq]
  exact born_quadratic ψ φ hψ hφ

end CSD.LF2
