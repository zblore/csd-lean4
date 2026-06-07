import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Shor's algorithm — period recovery (S5, uniqueness route)

**Category:** 3-Local (QM-validity), pure finite number theory.

Tranche S5 of `specs/shor-plan.md`. After phase estimation (S4) a single run yields a count `c`
with `|c/T - s/r| ≤ 1/(2T)` for the true order `r` (`s/r` in lowest terms). This file proves the
**recovery-correctness content**: that bound, together with `r·r' < T`, pins down `s/r`
**uniquely** among lowest-terms fractions, so the order `r` is **determined** by the measurement.

The argument is the elementary "distinct fractions are far apart" estimate
(`abs_sub_rat_ge`: distinct `a/b`, `c/d` differ by at least `1/(b·d)`), not the continued-fraction
machinery. Mathlib has the forward CF bound (`abs_sub_convergents_le'`) but not the Legendre
converse; this route sidesteps it.

**Honest scope.** This is the information-theoretic *determination* of `r` (why recovery is
possible: the measurement has a unique consistent answer). It is NOT the constructive
continued-fraction *computation* of `r` from `c/T`; the constructive Legendre-on-`GenContFract`
extraction is a heavier, separately-scoped alternative, deferred.

Composition with S4 (`ShorCore.phase_estimation_lower_bound`): S4 gives `prob ≥ 4/π²` for the
closest-integer outcome, i.e. the event `|c/T - s/r| ≤ 1/(2T)`; S5 shows that on that event `r` is
determined. For Shor with `T ≥ N² > r²` (so `r, r' < √T` and `r·r' < T` with slack) a single run
determines `r` with probability `≥ 4/π²`.

Tranche S6 (`nontrivial_factor`) adds the **classical reduction** "order-finding implies
factoring": for an even order `r` of a unit `a` with `a^(r/2) ≢ ±1 (mod N)`, the element
`x = a^(r/2)` is a nontrivial square root of unity (`N ∣ x²-1`, `N ∤ x±1`), and
`gcd(x-1, N)` is then a proper nontrivial divisor of `N`. This is the step that turns the
quantum period output into an actual factor.
-/

namespace CSD.Empirical.QM.Shor

/-- **Distinct fractions are far apart:** two unequal rationals `a/b`, `c/d` with positive
denominators differ by at least `1/(b·d)`. The numerator `a·d - c·b` is a nonzero integer. -/
theorem abs_sub_rat_ge (a b c d : ℤ) (hb : 0 < b) (hd : 0 < d)
    (hne : (a : ℚ) / b ≠ (c : ℚ) / d) :
    (1 : ℚ) / (b * d) ≤ |(a : ℚ) / b - (c : ℚ) / d| := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbd : (0 : ℚ) < (b : ℚ) * d := by
    have : (0 : ℤ) < b * d := mul_pos hb hd
    exact_mod_cast this
  -- the numerator is a nonzero integer
  have hn0 : (a * d - c * b : ℤ) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hne
    rw [div_eq_div_iff hb' hd']
    exact_mod_cast h
  -- combine over the common denominator
  have hcomb : (a : ℚ) / b - (c : ℚ) / d = ((a * d - c * b : ℤ) : ℚ) / ((b : ℚ) * d) := by
    rw [div_sub_div _ _ hb' hd']
    push_cast
    ring
  have h1n : (1 : ℚ) ≤ |((a * d - c * b : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]
    have hz : (1 : ℤ) ≤ |a * d - c * b| := by
      have := abs_pos.mpr hn0
      omega
    exact_mod_cast hz
  rw [hcomb, abs_div, abs_of_pos hbd]
  gcongr

/-- **Uniqueness of a close fraction:** if `a/b` and `c/d` (positive denominators with
`b·d < T`) are both within `1/(2T)` of the same rational `x`, they are equal. -/
theorem approx_unique (x : ℚ) (a b c d : ℤ) (hb : 0 < b) (hd : 0 < d) (T : ℤ)
    (hbd : b * d < T) (h₁ : |x - (a : ℚ) / b| ≤ 1 / (2 * T))
    (h₂ : |x - (c : ℚ) / d| ≤ 1 / (2 * T)) :
    (a : ℚ) / b = (c : ℚ) / d := by
  by_contra hne
  have hbdpos : (0 : ℚ) < (b : ℚ) * d := by
    have : (0 : ℤ) < b * d := mul_pos hb hd
    exact_mod_cast this
  have hTpos : (0 : ℚ) < (T : ℚ) := by
    have : (0 : ℤ) < T := lt_trans (mul_pos hb hd) hbd
    exact_mod_cast this
  -- close fractions: |a/b - c/d| ≤ 1/T
  have hTne : (T : ℚ) ≠ 0 := ne_of_gt hTpos
  have hclose : |(a : ℚ) / b - (c : ℚ) / d| ≤ 1 / T := by
    have htri : |(a : ℚ) / b - (c : ℚ) / d| ≤ |x - (a : ℚ) / b| + |x - (c : ℚ) / d| := by
      have h := abs_sub_le ((a : ℚ) / b) x ((c : ℚ) / d)
      rwa [abs_sub_comm ((a : ℚ) / b) x] at h
    have key : (1 : ℚ) / (2 * T) + 1 / (2 * T) = 1 / T := by field_simp; ring
    have hadd : |x - (a : ℚ) / b| + |x - (c : ℚ) / d| ≤ 1 / (2 * T) + 1 / (2 * T) :=
      add_le_add h₁ h₂
    rw [key] at hadd
    exact le_trans htri hadd
  -- far fractions: |a/b - c/d| ≥ 1/(b·d) > 1/T
  have hfar : (1 : ℚ) / ((b : ℚ) * d) ≤ |(a : ℚ) / b - (c : ℚ) / d| := abs_sub_rat_ge a b c d hb hd hne
  have hbdT : ((b : ℚ) * d) < (T : ℚ) := by exact_mod_cast hbd
  have hlt : (1 : ℚ) / T < 1 / ((b : ℚ) * d) := by
    apply one_div_lt_one_div_of_lt hbdpos hbdT
  linarith [hclose, hfar, hlt]

/-- **Shor period determination (headline):** the measured count `c` determines the order `r`.
Given the true `s/r` and any candidate `s'/r'`, both in lowest terms with `r·r' < T` and both
within `1/(2T)` of `c/T`, the two coincide: `s = s'` and `r = r'`. So the order `r` is the unique
denominator consistent with the measurement. -/
theorem shor_period_determined (c T s r s' r' : ℕ) (hr : 0 < r) (hr' : 0 < r')
    (hrr' : r * r' < T) (hcop : Nat.Coprime s r) (hcop' : Nat.Coprime s' r')
    (h  : |(c : ℚ) / T - (s : ℚ) / r| ≤ 1 / (2 * T))
    (h' : |(c : ℚ) / T - (s' : ℚ) / r'| ≤ 1 / (2 * T)) :
    s = s' ∧ r = r' := by
  -- the two fractions are equal by uniqueness
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  have hr'Z : (0 : ℤ) < (r' : ℤ) := by exact_mod_cast hr'
  have hrr'Z : (r : ℤ) * (r' : ℤ) < (T : ℤ) := by exact_mod_cast hrr'
  have h₁ : |(c : ℚ) / (T : ℚ) - ((s : ℤ) : ℚ) / ((r : ℤ) : ℚ)| ≤ 1 / (2 * ((T : ℤ) : ℚ)) := by
    push_cast; exact h
  have h₂ : |(c : ℚ) / (T : ℚ) - ((s' : ℤ) : ℚ) / ((r' : ℤ) : ℚ)| ≤ 1 / (2 * ((T : ℤ) : ℚ)) := by
    push_cast; exact h'
  have heqfrac : ((s : ℤ) : ℚ) / ((r : ℤ) : ℚ) = ((s' : ℤ) : ℚ) / ((r' : ℤ) : ℚ) :=
    approx_unique ((c : ℚ) / (T : ℚ)) (s : ℤ) (r : ℤ) (s' : ℤ) (r' : ℤ) hrZ hr'Z (T : ℤ) hrr'Z h₁ h₂
  -- normalise casts to ℕ and cross-multiply: s * r' = s' * r
  have heqfrac' : (s : ℚ) / (r : ℚ) = (s' : ℚ) / (r' : ℚ) := by push_cast at heqfrac; exact heqfrac
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr'Q : (r' : ℚ) ≠ 0 := by exact_mod_cast hr'.ne'
  rw [div_eq_div_iff hrQ hr'Q] at heqfrac'
  have hcross : s * r' = s' * r := by exact_mod_cast heqfrac'
  -- coprime lowest-terms uniqueness: r ∣ r' and r' ∣ r, so r = r'
  have hrdvd : r ∣ r' := by
    have hd : r ∣ s * r' := by rw [hcross]; exact dvd_mul_left r s'
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hd
  have hr'dvd : r' ∣ r := by
    have hd : r' ∣ s' * r := by rw [← hcross]; exact dvd_mul_left r' s
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop'.symm hd
  have hreq : r = r' := Nat.dvd_antisymm hrdvd hr'dvd
  refine ⟨?_, hreq⟩
  rw [← hreq] at hcross
  exact Nat.eq_of_mul_eq_mul_right hr hcross

/-- **S6 — factoring from a nontrivial square root of unity (the classical Shor step).**
If `x` is a nontrivial square root of `1` modulo `N` (so `N ∣ x²-1` but `N ∤ x-1` and
`N ∤ x+1`), then `g := gcd(x-1, N)` is a proper nontrivial divisor of `N`:
`1 < g`, `g < N`, and `g ∣ N`. Here `Int.gcd : ℤ → ℤ → ℕ`, so all three conjuncts are
statements about the natural number `g`. This is the reduction that converts the quantum
order-finding output into an actual factor of `N`. -/
theorem nontrivial_factor (N : ℕ) (hN : 1 < N) (x : ℤ)
    (hsq : (N : ℤ) ∣ x ^ 2 - 1) (hne1 : ¬ (N : ℤ) ∣ x - 1) (hne2 : ¬ (N : ℤ) ∣ x + 1) :
    1 < Int.gcd (x - 1) (N : ℤ) ∧ Int.gcd (x - 1) (N : ℤ) < N ∧ Int.gcd (x - 1) (N : ℤ) ∣ N := by
  set g := Int.gcd (x - 1) (N : ℤ) with hg
  -- g ∣ N (in ℕ), bridged from the ℤ divisibility `↑g ∣ (N:ℤ)`
  have hgZ : (g : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right (x - 1) (N : ℤ)
  have hgN : g ∣ N := Int.natCast_dvd_natCast.mp hgZ
  -- N ≠ 0
  have hNpos : 0 < N := by omega
  -- g ≤ N
  have hle : g ≤ N := Nat.le_of_dvd hNpos hgN
  -- g < N: else (N:ℤ) ∣ x-1, contradicting hne1
  have hlt : g < N := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hgx : (g : ℤ) ∣ (x - 1) := Int.gcd_dvd_left (x - 1) (N : ℤ)
      rw [h] at hgx
      exact hne1 hgx
  -- 1 < g
  have hgpos : g ≠ 0 := by
    intro h0
    rw [hg, Int.gcd_eq_zero_iff] at h0
    have : (N : ℤ) = 0 := h0.2
    have : N = 0 := by exact_mod_cast this
    omega
  have hgne1 : g ≠ 1 := by
    intro h1
    -- g = 1 ⟹ IsCoprime (x-1) N
    have hcop : IsCoprime (x - 1) (N : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; rw [hg] at h1; exact h1
    -- N ∣ (x-1)*(x+1)
    have hfac : (N : ℤ) ∣ (x - 1) * (x + 1) := by
      have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
      rwa [this] at hsq
    -- coprime cancellation ⟹ N ∣ x+1, contradiction
    have hcopN : IsCoprime (N : ℤ) (x - 1) := hcop.symm
    exact hne2 (hcopN.dvd_of_dvd_mul_left hfac)
  have h1lt : 1 < g := by omega
  exact ⟨h1lt, hlt, hgN⟩

/-- **S6 existential corollary:** a nontrivial square root of unity exhibits a proper
nontrivial divisor of `N`. -/
theorem N_has_nontrivial_factor (N : ℕ) (hN : 1 < N) (x : ℤ)
    (hsq : (N : ℤ) ∣ x ^ 2 - 1) (hne1 : ¬ (N : ℤ) ∣ x - 1) (hne2 : ¬ (N : ℤ) ∣ x + 1) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  obtain ⟨h1, h2, h3⟩ := nontrivial_factor N hN x hsq hne1 hne2
  exact ⟨Int.gcd (x - 1) (N : ℤ), h3, h1, h2⟩

end CSD.Empirical.QM.Shor
