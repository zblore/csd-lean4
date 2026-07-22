/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Algorithms.ShorRecovery
public import CsdLean4.Empirical.QM.Algorithms.ShorRandomA

/-!
# Shor's algorithm — factoring capstone (ties GOOD ⟹ nontrivial factor of `N`)

**Category:** 3-Local (QM-validity), pure finite number theory.

This file closes the Shor classical-reduction chain by connecting the **GOOD** success predicate
(`Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1`, in the units group `(ZMod N)ˣ`, the object the
random-`a` probability bound `shor_success_prob_ge_general` counts) to an **actual nontrivial
divisor** of `N` (the object the factoring reduction `shor_factor_of_even_order` /
`nontrivial_factor` produces).

Two results:

* `shor_random_a_yields_factor` — **pointwise**: a GOOD unit `a` yields a proper nontrivial factor
  `gcd(x - 1, N)` of `N`, where `x` lifts `a ^ (orderOf a / 2)`. Bridges the units-group `≠ ±1`
  conditions of the GOOD predicate to the `ZMod`-coercion `≠ ±1` hypotheses of
  `shor_factor_of_even_order`.
* `shor_factor_prob_ge` — **probability capstone**: a uniformly random unit `a` mod `N` (odd, with
  `≥ 2` distinct prime factors) yields a proper nontrivial factor with probability `≥ 1/2`. The
  GOOD filter is contained in the factor-yielding filter (`shor_random_a_yields_factor`), so the
  `≥ 1/2` bound on the GOOD frequency (`shor_success_prob_ge_general`) transports to the factor
  frequency by `Finset` cardinality monotonicity and `ℚ` division monotonicity.

Both are foundational-triple-only (no `busch_effect_gleason`, no measure axioms): the content is
elementary finite number theory composed on top of the already-verified S6 reduction and the S7
counting bound.
-/

@[expose] public section

namespace CSD.Empirical.QM.Shor

/-- **Pointwise: a GOOD unit yields a nontrivial factor.**
For `a : (ZMod N)ˣ` satisfying the Shor GOOD predicate (`Even (orderOf a)` and
`a ^ (orderOf a / 2) ≠ -1` in the **units** group) and any integer `x` lifting
`a ^ (orderOf a / 2)`, the natural number `gcd(x - 1, N)` is a proper nontrivial divisor of `N`.

Bridges the units-group `≠ -1` condition (and the derived `≠ 1`) to the `ZMod`-coercion
hypotheses of `shor_factor_of_even_order` (S6). The `≠ 1` side is derived from
`0 < orderOf a / 2 < orderOf a` (so `orderOf a ∤ orderOf a / 2`, hence `a ^ (orderOf a / 2) ≠ 1`
by `orderOf_dvd_iff_pow_eq_one`); both `±1` units conditions are pushed to the coercion via
`Units.val_inj` (`Units.val_eq_one` for `1`, `Units.val_neg`/`Units.val_one` for `-1`). -/
theorem shor_random_a_yields_factor (N : ℕ) (hN : 1 < N) (a : (ZMod N)ˣ)
    (hgood : Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1) (x : ℤ)
    (hx : (x : ZMod N) = ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N)) :
    1 < Int.gcd (x - 1) (N : ℤ) ∧ Int.gcd (x - 1) (N : ℤ) < N
      ∧ Int.gcd (x - 1) (N : ℤ) ∣ N := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hr, hne⟩ := hgood
  -- the half exponent is strictly between 0 and the order
  have hopos : 0 < orderOf a := orderOf_pos a
  have hhalf2 : orderOf a / 2 * 2 = orderOf a := Nat.div_mul_cancel hr.two_dvd
  have hk_pos : 0 < orderOf a / 2 := by omega
  have hk_lt : orderOf a / 2 < orderOf a := by omega
  -- `a ^ (orderOf a / 2) ≠ 1` in the units group
  have hne1u : a ^ (orderOf a / 2) ≠ 1 := by
    intro hpow
    have hdvd : orderOf a ∣ orderOf a / 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hle : orderOf a ≤ orderOf a / 2 := Nat.le_of_dvd hk_pos hdvd
    omega
  -- discharge `hy1 : ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ 1`
  have hy1 : ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ 1 :=
    fun h => hne1u (Units.val_eq_one.mp h)
  -- discharge `hy2 : ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1`
  have hy2 : ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1 := by
    -- `((-1 : (ZMod N)ˣ) : ZMod N) = -1`
    have hcoeNeg : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by
      rw [Units.val_neg, Units.val_one]
    intro hcon
    apply hne
    -- `(u : ZMod N) = ((-1 : (ZMod N)ˣ) : ZMod N) ↔ u = -1` via `Units.val_inj`
    rw [← hcoeNeg] at hcon
    exact Units.val_inj.mp hcon
  exact shor_factor_of_even_order N hN a hr hy1 hy2 x hx

/-- **Probability capstone: a random unit yields a nontrivial factor with probability `≥ 1/2`.**
For odd `N` with at least two distinct prime factors, the fraction of units `a : (ZMod N)ˣ` for
which the canonical integer representative of `a ^ (orderOf a / 2)` yields a proper nontrivial
divisor `gcd(· - 1, N)` of `N` is at least `1/2`.

The canonical representative is `xrep a := (((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ)`,
which lifts `a ^ (orderOf a / 2)` (`hxrep` below, via `Int.cast_natCast` + `ZMod.natCast_val` +
`ZMod.cast_id`). By `shor_random_a_yields_factor` every GOOD unit lands in the factor-yielding
filter, so the GOOD filter is `⊆` the factor filter; cardinality monotonicity
(`Finset.card_le_card`) and `ℚ` division monotonicity (`gcongr`) then transport the `≥ 1/2` GOOD
frequency bound (`shor_success_prob_ge_general`) to the factor frequency. -/
theorem shor_factor_prob_ge (N : ℕ) [NeZero N] (hodd : Odd N) (hN : 2 ≤ N.primeFactors.card) :
    (1 : ℚ) / 2 ≤
      ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
        1 < Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ)
          ∧ Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ) < N)).card : ℚ)
        / (Fintype.card (ZMod N)ˣ : ℚ) := by
  classical
  -- `1 < N`: a modulus with ≥ 2 distinct prime factors is > 1 (`primeFactors 0 = primeFactors 1 = ∅`).
  have hN1 : 1 < N := by
    have hne0 : N ≠ 0 := NeZero.ne N
    have hne1 : N ≠ 1 := by
      intro h
      rw [h, Nat.primeFactors_one, Finset.card_empty] at hN
      omega
    omega
  -- GOOD filter ⊆ factor-yielding filter (pointwise via `shor_random_a_yields_factor`).
  have hsubset :
      (Finset.univ.filter (fun a : (ZMod N)ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1))
        ⊆ (Finset.univ.filter (fun a : (ZMod N)ˣ =>
          1 < Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ)
            ∧ Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ) < N)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    -- the canonical representative lifts `a ^ (orderOf a / 2)`
    set y : ZMod N := ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) with hy
    have hxrep : (((y.val : ℤ)) : ZMod N) = y := by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
    obtain ⟨h1, h2, _⟩ := shor_random_a_yields_factor N hN1 a ha (y.val : ℤ) hxrep
    exact ⟨h1, h2⟩
  -- cardinality monotonicity
  have hcard := Finset.card_le_card hsubset
  -- `#units > 0`
  have hpos : (0 : ℚ) < (Fintype.card (ZMod N)ˣ : ℚ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ZMod N)ˣ)
  -- ℚ division monotonicity from the cardinality inequality
  have hmono :
      ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
          Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℚ)
        / (Fintype.card (ZMod N)ˣ : ℚ)
      ≤ ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
          1 < Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ)
            ∧ Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ) < N)).card : ℚ)
        / (Fintype.card (ZMod N)ˣ : ℚ) := by
    have hcardq :
        ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
            Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℚ)
          ≤ ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
            1 < Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ)
              ∧ Int.gcd ((((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) (N : ℤ) < N)).card : ℚ) := by
      exact_mod_cast hcard
    gcongr
  -- chain with the GOOD frequency bound
  exact le_trans (shor_success_prob_ge_general N hodd hN) hmono

end CSD.Empirical.QM.Shor
