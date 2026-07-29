/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ContextFixedA7
public import CsdLean4.LF4.BornRegionUncond

/-!
# Discharging the abundance hypothesis for Fubini–Study at `N ≥ 3`

`SigmaLayer/ContextFixedA7.lean` proved the **cap** — a base-only, `U(N)`-covariant, non-negative
preparation density `g` vanishes a.e. below `½` — **conditional** on an abundance hypothesis:
that two overlap coordinates can jointly take values in any positive-measure set below `½`.

This file discharges that hypothesis for the actual Fubini–Study measure, so the cap becomes
unconditional at `N ≥ 3`.

## The mechanism

The corpus already knows where `μ_FS` goes under the moment map: `fs_volume_eq_dirichlet_inter`
says the pushforward is the **uniform (Dirichlet) measure on the open simplex**,

  `μ_FS ((ratioN ∘ momentMap) ⁻¹' R) = M! · vol (R ∩ openSimplexFree)`.

So abundance becomes a question about Lebesgue measure on `Fin M → ℝ`: does the set where two
chosen coordinates land in `T` meet the open simplex in positive volume? For `M ≥ 2` it does, and
the construction is explicit — put the two chosen coordinates in `T` and every other coordinate in
a small interval `(0, ε)`.

The one subtlety is that `T ⊆ (0, ½)` gives `tⱼ + tₖ < 1` **pointwise but not uniformly**, so the
room left for the other coordinates is not bounded below. `exists_trunc_of_volume_pos` fixes that
by first passing to a positive-measure part of `T` bounded away from `½`.

## Why `M ≥ 2`, i.e. `N ≥ 3`

`M = N − 1` is the number of free simplex coordinates. Two *distinct* free coordinates exist
exactly when `M ≥ 2`, i.e. `N ≥ 3`. At `N = 2` there is a single free coordinate and the second
Born weight is `1 − s₁` — functionally dependent, which is precisely
`ContextFixedA7.joint_degenerate_of_sum_eq_one`, the qubit's escape route. So the dimension count
that makes this file work is the same one that makes the qubit exempt.

## Status

With `fs_joint_abundance` the cap is unconditional at `N ≥ 3`. That is a **derived** structural
constraint on any base-only A7 construction, replacing the numerical evidence the retracted
"provably dead" row rested on. It is still **not** the no-go: the generic-`ψ` requirement and the
harmonic argument remain open (see `ContextFixedA7.lean`'s header and `specs/BACKLOG.md`).

## References

`SigmaLayer/ContextFixedA7.lean` (the reduction and the cap);
`LF4/BornRegionUncond.lean` (`fs_volume_eq_dirichlet_inter`);
`LF4/MomentRatioUniformN.lean` (`openSimplexFree`, `ratioN`);
`LF4/MomentMap.lean` (`momentMap_sum_eq_one`); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set Matrix.UnitaryGroup CSD.LF4

namespace CSD.SigmaLayer

/-! ### Truncating a low set away from `½` -/

/-- A positive-measure set below `½` has a positive-measure part bounded **away** from `½`.
Needed because `T ⊆ (0,½)` bounds `tⱼ + tₖ < 1` pointwise but not uniformly, and the product
construction below needs uniform room for the remaining coordinates. -/
theorem exists_trunc_of_volume_pos {T : Set ℝ} (hT : T ⊆ Set.Iio (1 / 2 : ℝ))
    (hpos : 0 < volume T) :
    ∃ c : ℝ, c < 1 / 2 ∧ 0 < volume (T ∩ Set.Iio c) := by
  by_contra hcon
  push Not at hcon
  -- Every point of `T` is below `1/2 - 1/(m+1)` for some `m`.
  have hcov : T ⊆ ⋃ m : ℕ, (T ∩ Set.Iio (1 / 2 - 1 / (m + 1) : ℝ)) := by
    intro t ht
    have hlt : t < 1 / 2 := hT ht
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0:ℝ) < 1 / 2 - t by linarith)
    exact Set.mem_iUnion.mpr ⟨m, ht, by simp only [Set.mem_Iio]; linarith⟩
  have hnull : volume (⋃ m : ℕ, (T ∩ Set.Iio (1 / 2 - 1 / (m + 1) : ℝ))) = 0 := by
    refine measure_iUnion_null fun m => ?_
    have hc : (1 / 2 - 1 / (m + 1) : ℝ) < 1 / 2 := by
      have : (0:ℝ) < 1 / (m + 1) := by positivity
      linarith
    exact nonpos_iff_eq_zero.mp (hcon _ hc)
  exact absurd (measure_mono_null hcov hnull) (ne_of_gt hpos)

/-! ### Positivity on the open simplex -/

/-- **The explicit witness set.** Two chosen coordinates in `T'`, every other in `(0, ε)`. -/
private noncomputable def boxSet {M : ℕ} (T' : Set ℝ) (ε : ℝ) (j k : Fin M) : Fin M → Set ℝ :=
  fun i => if i = j then T' else if i = k then T' else Set.Ioo 0 ε

/-- **Abundance on the simplex.** For `M ≥ 2` and a positive-measure `T ⊆ (0,½)`, the set where
coordinates `j ≠ k` both land in `T` meets the open simplex in positive volume. -/
theorem volume_inter_openSimplexFree_pos {M : ℕ} {T : Set ℝ} {j k : Fin M} (hjk : j ≠ k)
    (hT : T ⊆ Set.Ioo 0 (1 / 2 : ℝ)) (hpos : 0 < volume T) :
    0 < volume ({t : Fin M → ℝ | t j ∈ T ∧ t k ∈ T} ∩ openSimplexFree) := by
  classical
  -- Bound `T` away from `1/2`.
  obtain ⟨c, hc2, hcpos⟩ :=
    exists_trunc_of_volume_pos (hT.trans Set.Ioo_subset_Iio_self) hpos
  set T' : Set ℝ := T ∩ Set.Iio c with hT'
  have hT'sub : T' ⊆ T := Set.inter_subset_left
  have hT'lt : ∀ x ∈ T', x < c := fun x hx => hx.2
  have hT'pos0 : ∀ x ∈ T', 0 < x := fun x hx => (hT (hT'sub hx)).1
  -- Room for the other coordinates.
  set ε : ℝ := (1 - 2 * c) / (M + 1) with hε
  have hc1 : 0 < 1 - 2 * c := by linarith
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hMε : (M : ℝ) * ε < 1 - 2 * c := by
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    have hmul : (M : ℝ) * ε * ((M:ℝ) + 1) < (1 - 2 * c) * ((M:ℝ) + 1) := by
      rw [hε]; field_simp; nlinarith [hc1]
    exact lt_of_mul_lt_mul_right hmul (le_of_lt hM1)
  -- The witness product set.
  have hbox_pos : 0 < volume (Set.pi Set.univ (boxSet T' ε j k)) := by
    rw [volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    by_cases h1 : i = j
    · simp only [boxSet, if_pos h1]; exact ne_of_gt hcpos
    · by_cases h2 : i = k
      · simp only [boxSet, if_neg h1, if_pos h2]; exact ne_of_gt hcpos
      · simp only [boxSet, if_neg h1, if_neg h2, Real.volume_Ioo, sub_zero]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr hεpos)
  refine lt_of_lt_of_le hbox_pos (measure_mono ?_)
  intro t ht
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at ht
  have htj : t j ∈ T' := by simpa [boxSet] using ht j
  have htk : t k ∈ T' := by simpa [boxSet, Ne.symm hjk, hjk] using ht k
  have hother : ∀ i, i ≠ j → i ≠ k → t i ∈ Set.Ioo 0 ε := by
    intro i h1 h2; simpa [boxSet, if_neg h1, if_neg h2] using ht i
  refine ⟨⟨hT'sub htj, hT'sub htk⟩, ?_, ?_⟩
  · -- all coordinates strictly positive
    intro i
    by_cases h1 : i = j
    · subst h1; exact hT'pos0 _ htj
    · by_cases h2 : i = k
      · subst h2; exact hT'pos0 _ htk
      · exact (hother i h1 h2).1
  · -- the coordinates sum to less than 1
    have hsplit : ∑ i, t i
        = t j + (t k + ∑ i ∈ (Finset.univ.erase j).erase k, t i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)]
    have hrest : ∑ i ∈ (Finset.univ.erase j).erase k, t i ≤ (M : ℝ) * ε := by
      calc ∑ i ∈ (Finset.univ.erase j).erase k, t i
          ≤ ∑ _i ∈ (Finset.univ.erase j).erase k, ε := by
            refine Finset.sum_le_sum fun i hi => ?_
            have h2 : i ≠ k := (Finset.mem_erase.mp hi).1
            have h1 : i ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
            exact le_of_lt (hother i h1 h2).2
        _ = ((Finset.univ.erase j).erase k).card * ε := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M : ℝ) * ε := by
            refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hεpos)
            have := Finset.card_le_univ ((Finset.univ.erase j).erase k)
            simpa using (Nat.cast_le (α := ℝ)).mpr this
    have hj := hT'lt _ htj
    have hk := hT'lt _ htk
    rw [hsplit]
    linarith

/-! ### The abundance hypothesis, discharged for Fubini–Study -/

/-- **The Fubini–Study measure supplies the abundance hypothesis at `N ≥ 3`.**

Two distinct free moment coordinates jointly take values in any positive-measure `T ⊆ (0,½)` on a
set of positive `μ_FS`-measure. Via `fs_volume_eq_dirichlet_inter` this is exactly the simplex
positivity above, and `M ≥ 2` — i.e. `N ≥ 3` — is what makes two distinct free coordinates
available. -/
theorem fs_joint_abundance {M : ℕ} (p₀ : CPN (M + 1)) {j k : Fin M} (hjk : j ≠ k)
    {T : Set ℝ} (hTm : MeasurableSet T) (hT : T ⊆ Set.Ioo 0 (1 / 2 : ℝ))
    (hpos : 0 < volume T) :
    0 < fubiniStudyMeasure p₀
      {p : CPN (M + 1) | momentMap p (Fin.castSucc j) ∈ T ∧ momentMap p (Fin.castSucc k) ∈ T} := by
  classical
  have hR : MeasurableSet {t : Fin M → ℝ | t j ∈ T ∧ t k ∈ T} :=
    ((measurable_pi_apply j) hTm).inter ((measurable_pi_apply k) hTm)
  -- The moment coordinates *are* the free simplex coordinates, since the moments sum to one.
  have hset : {p : CPN (M + 1) |
        momentMap p (Fin.castSucc j) ∈ T ∧ momentMap p (Fin.castSucc k) ∈ T}
      = (fun p => ratioN (fun i => momentMap p i)) ⁻¹' {t : Fin M → ℝ | t j ∈ T ∧ t k ∈ T} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, ratioN]
    rw [momentMap_sum_eq_one p, div_one, div_one]
  rw [hset, fs_volume_eq_dirichlet_inter p₀ hR]
  refine ENNReal.mul_pos (by exact_mod_cast Nat.factorial_ne_zero M) ?_ |>.trans_le (le_refl _)
  exact ne_of_gt (volume_inter_openSimplexFree_pos hjk hT hpos)

/-- **★ The cap, unconditional at `N ≥ 3`.**

A base-only, `U(N)`-covariant, non-negative preparation density reproducing Born on the
Fubini–Study sector **vanishes almost everywhere on overlap values below `½`** — no hypothesis
left over. The `N = 2` solution `4(2s−1)₊` is supported exactly on `(½, 1]`, so the bound is
sharp and attained; and `N = 2` is exempt for the reason recorded in
`ContextFixedA7.joint_degenerate_of_sum_eq_one`. -/
theorem fs_cap_unconditional {M : ℕ} (p₀ : CPN (M + 1)) {j k : Fin M} (hjk : j ≠ k)
    {g : ℝ → ℝ} (hgm : Measurable g)
    (hdisj : fubiniStudyMeasure p₀
        (overlapSupport g (fun p => momentMap p (Fin.castSucc j)) ∩
         overlapSupport g (fun p => momentMap p (Fin.castSucc k))) = 0) :
    volume ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ)) = 0 :=
  cap_of_joint_nondegenerate (μ := fubiniStudyMeasure p₀)
    (s := fun (i : Fin (M + 1)) (p : CPN (M + 1)) => momentMap p i)
    (j := Fin.castSucc j) (k := Fin.castSucc k) hgm hdisj
    fun _T hTm hT hpos => fs_joint_abundance p₀ hjk hTm hT hpos

end CSD.SigmaLayer
