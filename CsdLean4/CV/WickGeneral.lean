/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Wick

/-!
# CV-23d: Wick's theorem for an arbitrary equal-time word

**Category:** 3-Local (CV; continuous variables — the multi-mode field).

`CV/Wick.lean` resolved the equal-time `2n`-point function *by pattern*: single-mode moments
(`modeOpQ_pow_two_mul_vac`, `(2n−1)‼·(½)ⁿ` for `n < N`), two-block factorisation
(`modeOpQ_pow_mul_pow_vac`), and the remark that longer grouped words iterate the clustering and
interleaved words commute into grouped form. This module states the resulting theorem once, for an
**arbitrary word** of quadratures — any length, any modes, any interleaving — so that the equal-time
Wick expansion is a single formula rather than a pattern table.

* `wordOp l` — the operator of a word `l : List (Fin K)` of modes, the product of the mode
  quadratures in the written order;
* `wickMoment m` — the Gaussian moment `(m − 1)‼ / 2^{m/2}` for even `m`, and `0` for odd `m`: the
  number of perfect matchings of `m` letters, each pairing carrying the vacuum two-point value `½`;
* `wordOp_eq_modeOp_pow_mul` — any word is one mode's block times the word with that mode removed
  (the interleaving commutes out, `commute_modeOp`); `wordOp_supportedOn` — a word is supported on
  its modes;
* ★ `wordOp_vac_eq_prod_pow` — **clustering**: the vacuum expectation of any word is the product,
  over modes, of the single-mode moments of the mode's multiplicity in the word
  (`diag_entry_mul_of_disjointSupport`, block by block);
* ★★ `wordOp_vac_eq_prod_wickMoment` — **Wick's theorem at equal time, for every word**: below the
  truncation threshold, `⟨vac∣ Q_{k₁} ⋯ Q_{k_m} ∣vac⟩ = ∏_k wickMoment (count k)`; in particular the
  expectation vanishes whenever some mode occurs an odd number of times
  (`wordOp_vac_eq_zero_of_odd_count`), and for a word of `2n` letters all of one mode it is
  `(2n−1)‼ · (½)ⁿ`.

**The pairing reading.** A perfect matching of the word's `m` letters that pairs only equal modes
contributes `∏ ½` over its `m/2` pairs, and there are `∏_k (count k − 1)‼` such matchings (a matching
of a multiset factors over the mode classes, and a `2j`-letter class has `(2j−1)‼` matchings). So
`∏_k wickMoment (count k)` *is* the sum over pairings of the product of two-point functions, in the
form that does not need a type of matchings. The matching-indexed sum itself is a combinatorial
restatement and is not separately stated here.

## Honest scope

⚠️ **Equal time.** Every quadrature sits at the same time; the pairing value is the vacuum
fluctuation `½` and carries no phase. The time-separated formula, whose pairings carry the
stroboscopic kernels `K(nᵢ, nⱼ)`, is the four-point theorem `timeFourPoint_wick` and is not
generalised here (the value then depends on *which* letters pair, so multiplicities do not
determine it).

⚠️ **Below the truncation threshold**, `count k / 2 < N` for every mode `k`: exactly the single-mode
ladder's threshold (`Q_pow_two_mul_vac`), because the clustering reduces the word to single-mode
moments. Above it the truncated ladder is no longer Gaussian, as `CV/Wick.lean` documents at
`N = 2` and `N = 3`.

⚠️ The free (mode-diagonal) drive only, as for the whole Wick chain; no continuum limit
(`ApproxCCR.no_exact_finite_ccr`).

References: `CV/Wick.lean` (the moment ladder and the two-block clustering); `CV/Propagator.lean`
(`diag_entry_mul_of_disjointSupport`); `CV/ModeLocality.lean` (`commute_modeOp`,
`modeOp_supportedOn`); `CV/LocalAlgebra.lean` (`SupportedOn.mul`, `.mono`, `.one`);
`specs/BACKLOG.md` #36(b); `specs/future-work.md`.
-/

@[expose] public section

open Matrix
open scoped Nat

namespace CSD.CV

variable {K N : ℕ}

/-! ### The word operator and the Gaussian moment -/

/-- The operator of a word of modes: the product of the mode quadratures, in the written order. -/
noncomputable def wordOp (l : List (Fin K)) : Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  (l.map fun k => modeOp k (Q N)).prod

@[simp] theorem wordOp_nil : wordOp (N := N) ([] : List (Fin K)) = 1 := rfl

theorem wordOp_cons (k : Fin K) (l : List (Fin K)) :
    wordOp (N := N) (k :: l) = modeOp k (Q N) * wordOp l := rfl

/-- The Gaussian vacuum moment of `m` quadratures of one mode: `(m − 1)‼ / 2^{m/2}` for even `m`,
the number of perfect matchings of `m` letters times `½` per pair, and `0` for odd `m`. -/
noncomputable def wickMoment (m : ℕ) : ℂ :=
  if Even m then (((m - 1)‼ : ℕ) : ℂ) / 2 ^ (m / 2) else 0

theorem wickMoment_even (n : ℕ) : wickMoment (2 * n) = (((2 * n - 1)‼ : ℕ) : ℂ) / 2 ^ n := by
  rw [wickMoment, if_pos (even_two_mul n), Nat.mul_div_cancel_left n two_pos]

theorem wickMoment_odd (n : ℕ) : wickMoment (2 * n + 1) = 0 := by
  rw [wickMoment, if_neg]
  exact Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n)

/-- The single-mode ladder, indexed by the multiplicity: below threshold the vacuum moment of
`Q^m` is `wickMoment m`. -/
theorem Q_pow_vac_eq_wickMoment [NeZero N] (m : ℕ) (hm : m / 2 < N) :
    (Q N ^ m) 0 0 = wickMoment m := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [wickMoment_even, Q_pow_two_mul_vac n (by omega)]
  · rw [wickMoment_odd, Q_pow_two_mul_add_one_vac]

/-! ### A word is its mode blocks -/

/-- Any word is one mode's block, at that mode's multiplicity, times the word with the mode
removed: the interleaved occurrences commute out past the other modes. -/
theorem wordOp_eq_modeOp_pow_mul (k : Fin K) (l : List (Fin K)) :
    wordOp (N := N) l = modeOp k (Q N ^ l.count k) * wordOp (l.filter (· ≠ k)) := by
  induction l with
  | nil => simp [modeOp_one]
  | cons j l ih =>
    by_cases hjk : j = k
    · subst hjk
      rw [wordOp_cons, ih, List.count_cons_self, List.filter_cons_of_neg (by simp), pow_succ',
        ← modeOp_mul, Matrix.mul_assoc]
    · rw [wordOp_cons, ih, List.count_cons_of_ne hjk, List.filter_cons_of_pos (by simpa using hjk),
        wordOp_cons, ← Matrix.mul_assoc, commute_modeOp hjk, Matrix.mul_assoc]

/-- A word is supported on the set of its modes. -/
theorem wordOp_supportedOn (l : List (Fin K)) :
    SupportedOn l.toFinset (wordOp (N := N) l) := by
  induction l with
  | nil => exact SupportedOn.one
  | cons j l ih =>
    rw [wordOp_cons, List.toFinset_cons]
    exact ((modeOp_supportedOn j _).mono
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))).mul
      (ih.mono (Finset.subset_insert _ _))

/-- The vacuum diagonal of a single-mode block is the single-mode moment. -/
theorem modeOp_pow_vac_entry [NeZero N] (k : Fin K) (m : ℕ) :
    (modeOp k (Q N ^ m)) (vacCfg K N) (vacCfg K N) = (Q N ^ m) 0 0 := by
  rw [modeOp_apply_of_agree k _ (fun _ _ => rfl), vacCfg_apply]

/-! ### Clustering, and Wick's theorem for every word -/

/-- ★ **Clustering.** The vacuum expectation of any word is the product over modes of the
single-mode moments at the mode's multiplicity. -/
theorem wordOp_vac_eq_prod_pow [NeZero N] (l : List (Fin K)) :
    wordOp (N := N) l (vacCfg K N) (vacCfg K N) = ∏ k : Fin K, (Q N ^ l.count k) 0 0 := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  cases l with
  | nil => simp
  | cons k l =>
    -- split off mode `k`'s block; the rest is shorter and avoids `k`
    have hsplit := wordOp_eq_modeOp_pow_mul (N := N) k (k :: l)
    set l' := (k :: l).filter (· ≠ k) with hl'
    have hlen : l'.length < n := by
      rw [← hn, hl', List.filter_cons_of_neg (by simp)]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    have hk' : k ∉ l'.toFinset := by
      simp [hl']
    have hdisj : Disjoint ({k} : Finset (Fin K)) l'.toFinset := by
      simpa using hk'
    rw [hsplit, diag_entry_mul_of_disjointSupport hdisj (modeOp_supportedOn k _)
      (wordOp_supportedOn l'), modeOp_pow_vac_entry, ih l'.length hlen l' rfl]
    -- the product over modes: the `k` factor from the block, the rest from `l'`
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (Q N ^ (k :: l).count j) 0 0)
      (Finset.mem_univ k)]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (Q N ^ l'.count j) 0 0) (Finset.mem_univ k)]
    have hk0 : l'.count k = 0 := by
      rw [List.count_eq_zero]
      simp [hl', List.mem_filter]
    rw [hk0, pow_zero, Matrix.one_apply_eq, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    rw [hl', List.count_filter (by simpa using hjk)]

/-- ★★ **Wick's theorem at equal time, for every word.** Below the truncation threshold, the vacuum
expectation of any product of mode quadratures is the product over modes of the Gaussian moment of
the mode's multiplicity: `∏_k wickMoment (count k)`, which is the sum over perfect matchings pairing
equal modes of `½` per pair. -/
theorem wordOp_vac_eq_prod_wickMoment [NeZero N] (l : List (Fin K))
    (hN : ∀ k : Fin K, l.count k / 2 < N) :
    wordOp (N := N) l (vacCfg K N) (vacCfg K N) = ∏ k : Fin K, wickMoment (l.count k) := by
  rw [wordOp_vac_eq_prod_pow]
  exact Finset.prod_congr rfl fun k _ => Q_pow_vac_eq_wickMoment _ (hN k)

/-- The length form of the threshold: `length / 2 < N` suffices for every mode. -/
theorem wordOp_vac_eq_prod_wickMoment_of_length [NeZero N] (l : List (Fin K))
    (hN : l.length / 2 < N) :
    wordOp (N := N) l (vacCfg K N) (vacCfg K N) = ∏ k : Fin K, wickMoment (l.count k) :=
  wordOp_vac_eq_prod_wickMoment l fun _ =>
    lt_of_le_of_lt (Nat.div_le_div_right List.count_le_length) hN

/-- A word in which some mode occurs an odd number of times has vanishing vacuum expectation. -/
theorem wordOp_vac_eq_zero_of_odd_count [NeZero N] (l : List (Fin K)) {k : Fin K}
    (hk : Odd (l.count k)) :
    wordOp (N := N) l (vacCfg K N) (vacCfg K N) = 0 := by
  rw [wordOp_vac_eq_prod_pow]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  obtain ⟨n, hn⟩ := hk
  rw [hn, Q_pow_two_mul_add_one_vac]

/-- The all-one-mode word of `2n` letters: `(2n−1)‼ · (½)ⁿ`, the moment ladder recovered. -/
theorem wordOp_replicate_vac [NeZero N] (k : Fin K) (n : ℕ) (hn : n < N) :
    wordOp (N := N) (List.replicate (2 * n) k) (vacCfg K N) (vacCfg K N)
      = (((2 * n - 1)‼ : ℕ) : ℂ) / 2 ^ n := by
  classical
  rw [wordOp_vac_eq_prod_wickMoment _ fun j => ?_]
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), List.count_replicate_self,
      wickMoment_even, Finset.prod_eq_one, mul_one]
    intro j hj
    have hjk : k ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
    simp [List.count_replicate, hjk, wickMoment, Nat.doubleFactorial]
  · rw [List.count_replicate]
    split_ifs
    · rwa [Nat.mul_div_cancel_left n two_pos]
    · rw [Nat.zero_div]; exact Nat.pos_of_ne_zero (NeZero.ne N)

end CSD.CV
