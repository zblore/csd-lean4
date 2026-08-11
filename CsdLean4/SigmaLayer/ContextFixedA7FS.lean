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
`CSD.SigmaLayer.joint_degenerate_of_sum_eq_one` (`SigmaLayer/ContextFixedA7.lean`), the qubit's escape route. So the dimension count
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
sharp and attained.

`N = 2` is exempt **structurally**, and this proof needs nothing to exclude it: the statement
quantifies over distinct `j k : Fin M`, which is uninhabited unless `M ≥ 2`, i.e. `N = M + 1 ≥ 3`.
For *why* the qubit escapes the cap — the mathematical content, which is not used here — see
`CSD.SigmaLayer.joint_degenerate_of_sum_eq_one` (`SigmaLayer/ContextFixedA7.lean`). -/
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

/-! ### Balanced states are not negligible

`vanishes_below_of_balanced` needs states whose overlaps are *all* small — near the barycentre of
the simplex. `∑ᵢ sᵢ = 1` forces `maxᵢ sᵢ ≥ 1/n`, and every threshold above that is met on a set of
positive measure, witnessed by a box around the barycentre.

The geometry is split from the arithmetic deliberately: `box_in_simplex` takes the centre `b` and
half-width `d` as *abstract* reals constrained by linear relations plus the single identity
`M·b = 1 − b`, so every step inside it is linear. The concrete choice `b = 1/(M+1)`,
`d = min(b, c−b)/(M+1)` is then made once, in `volume_balanced_inter_openSimplexFree_pos`. -/

/-- A box of half-width `d` about a centre `b` with `M·b = 1 − b` lies in the open simplex and is
balanced below `c`. All hypotheses are linear in `b`, `d`, `c` and the products `M·b`, `M·d`. -/
private theorem box_in_simplex {M : ℕ} (hM : 0 < M) {b d c : ℝ}
    (hb : (M : ℝ) * b = 1 - b) (_hbpos : 0 < b) (_hd0 : 0 < d) (hdb : d < b)
    (hdMb : (M : ℝ) * d < b) (hdMc : (M : ℝ) * d < c - b) (hbdc : b + d ≤ c) :
    Set.pi Set.univ (fun _ : Fin M => Set.Ioo (b - d) (b + d))
      ⊆ {t : Fin M → ℝ | (∀ i, t i ≤ c) ∧ 1 - ∑ i, t i ≤ c} ∩ openSimplexFree := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hne : (Finset.univ : Finset (Fin M)).Nonempty := Finset.univ_nonempty
  have hcard : (Finset.univ : Finset (Fin M)).card = M :=
    Finset.card_univ.trans (Fintype.card_fin M)
  have hplus : (M : ℝ) * (b + d) = (1 - b) + (M : ℝ) * d := by rw [mul_add, hb]
  have hminus : (M : ℝ) * (b - d) = (1 - b) - (M : ℝ) * d := by rw [mul_sub, hb]
  intro t ht
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo] at ht
  have hlo : ∀ i, b - d < t i := fun i => (ht i).1
  have hhi : ∀ i, t i < b + d := fun i => (ht i).2
  have hsum_lt : ∑ i, t i < (M : ℝ) * (b + d) := by
    have h := Finset.sum_lt_sum_of_nonempty hne (fun i (_ : i ∈ Finset.univ) => hhi i)
    rwa [Finset.sum_const, hcard, nsmul_eq_mul] at h
  have hsum_gt : (M : ℝ) * (b - d) < ∑ i, t i := by
    have h := Finset.sum_lt_sum_of_nonempty hne (fun i (_ : i ∈ Finset.univ) => hlo i)
    rwa [Finset.sum_const, hcard, nsmul_eq_mul] at h
  refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_, ?_⟩
  · linarith [hhi i]
  · linarith
  · linarith [hlo i]
  · linarith

/-- **Balanced states occupy positive volume in the simplex.** -/
theorem volume_balanced_inter_openSimplexFree_pos {M : ℕ} (hM : 0 < M) {c : ℝ}
    (hc : 1 / ((M : ℝ) + 1) < c) :
    0 < volume ({t : Fin M → ℝ | (∀ i, t i ≤ c) ∧ 1 - ∑ i, t i ≤ c} ∩ openSimplexFree) := by
  classical
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hbpos : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
  have hb : (M : ℝ) * (1 / ((M : ℝ) + 1)) = 1 - 1 / ((M : ℝ) + 1) := by
    field_simp; ring
  -- `e` is the room available in both directions; `d = e/(M+1)` shrinks it enough for `M` copies.
  have hepos : 0 < min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) :=
    lt_min hbpos (by linarith)
  have hMd : (M : ℝ) * (min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))
      < min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) := by
    rw [mul_div_assoc', div_lt_iff₀ hM1]
    have hring : min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1)
        = (M : ℝ) * min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1))
          + min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) := by ring
    rw [hring]; linarith
  have hd0 : 0 < min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1) := by positivity
  have hdle : min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)
      ≤ (M : ℝ) * (min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)) :=
    le_mul_of_one_le_left hd0.le hone
  have hbox : 0 < volume (Set.pi Set.univ (fun _ : Fin M =>
      Set.Ioo (1 / ((M : ℝ) + 1) - min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))
              (1 / ((M : ℝ) + 1) + min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)))) := by
    rw [volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hdself : min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)
      ≤ min (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1)) :=
    div_le_self hepos.le (by linarith)
  refine lt_of_lt_of_le hbox (measure_mono (box_in_simplex hM hb hbpos hd0 ?_ ?_ ?_ ?_))
  · linarith [min_le_left (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1))]
  · linarith [min_le_left (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1))]
  · linarith [min_le_right (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1))]
  · linarith [min_le_right (1 / ((M : ℝ) + 1)) (c - 1 / ((M : ℝ) + 1))]

/-- **Balanced states have positive Fubini–Study measure** — the `hbalanced` hypothesis of
`vanishes_below_of_balanced`, discharged for `μ_FS`. -/
theorem fs_balanced_abundance {M : ℕ} (hM : 0 < M) (p₀ : CPN (M + 1)) {c : ℝ}
    (hc : 1 / ((M : ℝ) + 1) < c) :
    0 < fubiniStudyMeasure p₀ {p : CPN (M + 1) | ∀ i, momentMap p i ≤ c} := by
  classical
  have hRfor : MeasurableSet {t : Fin M → ℝ | ∀ i, t i ≤ c} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  have hRlast : MeasurableSet {t : Fin M → ℝ | 1 - ∑ i, t i ≤ c} :=
    measurableSet_le
      (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
      measurable_const
  have hset : {p : CPN (M + 1) | ∀ i, momentMap p i ≤ c}
      = (fun p => ratioN (fun i => momentMap p i)) ⁻¹'
          {t : Fin M → ℝ | (∀ i, t i ≤ c) ∧ 1 - ∑ i, t i ≤ c} := by
    ext p
    have hsum : ∑ j, momentMap p j = 1 := momentMap_sum_eq_one p
    have hsplit : (∑ i : Fin M, momentMap p (Fin.castSucc i)) + momentMap p (Fin.last M) = 1 := by
      rw [← Fin.sum_univ_castSucc]; exact hsum
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, ratioN, hsum, div_one]
    constructor
    · exact fun h => ⟨fun i => h _, by linarith [h (Fin.last M)]⟩
    · rintro ⟨h1, h2⟩ j
      exact Fin.lastCases (by linarith) h1 j
  have hR : MeasurableSet {t : Fin M → ℝ | (∀ i, t i ≤ c) ∧ 1 - ∑ i, t i ≤ c} :=
    hRfor.inter hRlast
  rw [hset, fs_volume_eq_dirichlet_inter p₀ hR]
  exact ENNReal.mul_pos (by exact_mod_cast Nat.factorial_ne_zero M)
    (ne_of_gt (volume_balanced_inter_openSimplexFree_pos hM hc))

end CSD.SigmaLayer
