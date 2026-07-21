/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.BornWrapper

/-!
# LF2/EffectGleason: discharging the `busch_effect_gleason` axiom (Busch effect-Gleason)

**Category:** 3-Local (LF2 operational stratum — the effect-Gleason representation theorem).

`LF2/BornWrapper.lean` imports the Busch effect-Gleason theorem as the axiom
`busch_effect_gleason`: for `N ≥ 2`, every effect-additive, bounded, normalised probability
assignment `OP.p` on effects is `OP.p E = Tr(ρ E)` for a *unique* density operator `ρ`. This
module works toward **discharging** that axiom — proving it, so the corpus reaches "three
axioms, zero imported" (`CONVENTIONS.md §8.1`, `AXIOMS.md §2.2`, `specs/BACKLOG.md`). Busch's
proof (Busch 2003, "A Simple Proof of Gleason's Theorem") is short in finite dimensions
because additivity over the *effect* algebra gives linearity directly, bypassing the
frame-function analysis of projective Gleason.

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
3. **Reconstruction (spectral reduction + polarisation identities delivered; ρ-build deferred).**
   The **spectral reduction** is done: `p_finsetSum` (finite additivity),
   `Effect.eigenvalues_le_one` (effect eigenvalues `∈ [0,1]`), `Effect.sum_eigenEffect_M`
   (`E = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`), and `p_eq_eigen_sum` (`p(E) = ∑ᵢ λᵢ · p(|eᵢ⟩⟨eᵢ|)`) reduce the whole
   representation problem to determining `p` on rank-one projectors. The **polarisation
   identities** are done: `outerProduct_parallelogram` (`|u+v⟩⟨u+v| + |u−v⟩⟨u−v| = 2|u⟩⟨u| +
   2|v⟩⟨v|`, cross terms cancel) and `outerProduct_polarization_real` — the algebraic core that
   lets `p`, being additive, inherit the parallelogram law. The **sub-unit rank-one effect**
   `outerEffect v` (`|v⟩⟨v|` for any `‖v‖ ≤ 1`, needed for the combinations `u ± v`, `u ± iv`)
   and the **degree-2 homogeneity** `p_outerEffect_smul` (`p(|c·v⟩⟨c·v|) = c²·p(|v⟩⟨v|)`) are
   done. **Deferred:** the ρ-build itself — the `p`-level parallelogram (needs a sum-of-projectors
   `≤ I` eigenvalue bound) and using it to show `φ ↦ p(|φ⟩⟨φ|)` comes from a sesquilinear form,
   giving a Hermitian `ρ` with `p(|φ⟩⟨φ|) = ⟨φ|ρ|φ⟩`.
4. **(Deferred) Positivity/normalisation + uniqueness** — `p ≥ 0 ⟹ ρ` PSD; `p I = 1 ⟹ Tr ρ = 1`;
   uniqueness from non-degeneracy of the trace pairing. This yields
   `theorem busch_effect_gleason … := …`, replacing the axiom in `BornWrapper.lean`.

## Honest scope

**Delivered here:** steps 1–2 (monotone/additive layer + homogeneity `p(t•E) = t·p E`), the
**spectral reduction** (`p(E) = ∑ᵢ λᵢ · p(|eᵢ⟩⟨eᵢ|)`), and the **polarisation identities**
(step 3b core). **Deferred:** the ρ-build (assemble `ρ` from the polarisation of the rank-one
values) and step 4 (positivity/normalisation + uniqueness) — tracked in `specs/BACKLOG.md`
("Discharge `busch_effect_gleason`"). This module builds axiom-free (foundational triple) and
does **not** yet remove the axiom; it is a genuine partial layer of that discharge, not a stub.

References: `LF2/BornWrapper.lean` (`Effect`, `DensityOperator`, `OperationalPackage`,
`traceForm`, `busch_effect_gleason`); Busch 2003 (`quant-ph/9909073`); `AXIOMS.md §2.2`;
`CONVENTIONS.md §8.1`; `specs/BACKLOG.md`.
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

end OperationalPackage

end CSD.LF2
