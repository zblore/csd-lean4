import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Shor's algorithm — random-`a` success, per-cyclic-factor v₂ distribution bound (S7b)

**Category:** 3-Local (QM-validity), pure finite group theory.

Tranche **S7b** of `specs/shor-plan.md` §S7 — the meaty, self-contained, reusable core of the
random-`a` ≥ 1/2 success-probability argument. In a finite cyclic group `G` of even order, no
single "2-adic-valuation-of-order" class can exceed half the group:

```
2 · #{a ∈ G : v₂(orderOf a) = k} ≤ |G|     for every k.
```

This is the per-factor input to the CRT counting bound (S7a/S7d): the per-prime-power factors of
`(ZMod N)ˣ` are cyclic of even order, and this bound on each factor drives `2·#BAD ≤ |G|`.

## Route (generator, not totient)

Let `n = |G|`, `c = v₂(n)` (so `c ≥ 1` since `n` is even). Pick a generator `g`
(`IsCyclic.exists_generator`), with `orderOf g = n`. The power map `t : Fin n ↦ g ^ t` is a
bijection `Fin n ≃ G` (`pow_injOn_Iio_orderOf` + a card count). Under it the order-valuation class
transports to a subset of a **parity class** of `Fin n`:

- `orderOf (g ^ t) = n / gcd n t` (`orderOf_pow` + `orderOf g = n`);
- `v₂(orderOf (g ^ t)) = c − min(c, v₂ t)` (`Nat.factorization_div` on the divisor `gcd n t`
  + `Nat.factorization_gcd`);
- hence `v₂(orderOf (g ^ t)) = c ⟺ v₂ t = 0 ⟺ t odd`, and any class `k ≠ c` forces `v₂ t ≥ 1`,
  i.e. `t` even.

So the class `k = c` injects into `{t : Fin n | t odd}` and every class `k ≠ c` injects into
`{t : Fin n | t even}`; each parity class of `Fin n` has cardinality `n/2` (`Nat.card_multiples`
for the odd residues, complement for the even). Therefore every class has cardinality `≤ n/2`,
i.e. `2 · #class ≤ n`.

This avoids the divisor-reindexing of the totient route (`IsCyclic.card_orderOf_eq_totient` +
`Nat.sum_totient`); the generator bijection carries the whole count.

**Honest scope.** S7b only. The `−1`-characterisation (S7c), the two-factor CRT framing (S7a), and
the assembly into `2·#GOOD ≥ |G|` (S7d) are separate, not in this file.
-/

namespace CSD.Empirical.QM.Shor

open Finset

/-- **Parity counting in `Fin n` (odd residues).** The number of `t : Fin n` with `t` odd
(`¬ 2 ∣ t`) is `n / 2`. Via `Nat.card_multiples n 2 = #{e ∈ range n | 2 ∣ e+1} = n/2` and
`2 ∣ e+1 ⟺ ¬ 2 ∣ e`. -/
theorem card_odd_fin (n : ℕ) :
    (Finset.univ.filter (fun t : Fin n => ¬ 2 ∣ (t : ℕ))).card = n / 2 := by
  -- transport the `Fin n` filter to a `range n` filter
  rw [Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun t => if ¬ 2 ∣ t then 1 else 0),
    ← Finset.card_filter, ← Nat.card_multiples n 2]
  congr 1
  apply Finset.filter_congr
  intro x _hx
  constructor <;> intro h <;> omega

/-- **Parity counting in `Fin n` (even residues), `n` even.** The number of `t : Fin n` with `t`
even (`2 ∣ t`) is `n / 2`. By complement against `card_odd_fin` and `card_filter_add_card_filter_not`. -/
theorem card_even_fin (n : ℕ) (hn : Even n) :
    (Finset.univ.filter (fun t : Fin n => 2 ∣ (t : ℕ))).card = n / 2 := by
  have hodd := card_odd_fin n
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun t : Fin n => 2 ∣ (t : ℕ))
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  obtain ⟨m, hm⟩ := hn
  omega

/-- **The valuation fact.** For `g` a generator of `G` with `orderOf g = n` and `0 < t < n`,
the 2-adic valuation of `orderOf (g ^ t)` is `v₂ n − min(v₂ n, v₂ t)`.

Uses `orderOf_pow` (`orderOf (g^t) = n / gcd n t`), `Nat.factorization_div` (on the divisor
`gcd n t`), and `Nat.factorization_gcd`. -/
theorem v2_orderOf_pow {G : Type*} [Group G] [Fintype G] {g : G} {n : ℕ}
    (hgord : orderOf g = n) {t : ℕ} (htpos : 0 < t) (htlt : t < n) :
    (orderOf (g ^ t)).factorization 2
      = n.factorization 2 - min (n.factorization 2) (t.factorization 2) := by
  have hn0 : n ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  -- orderOf (g^t) = orderOf g / gcd (orderOf g) t = n / gcd n t
  have hord : orderOf (g ^ t) = n / Nat.gcd n t := by
    rw [orderOf_pow, hgord]
  rw [hord]
  have hdvd : Nat.gcd n t ∣ n := Nat.gcd_dvd_left n t
  rw [Nat.factorization_div hdvd]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  rw [Nat.factorization_gcd hn0 ht0]
  simp [Finsupp.inf_apply]

/-- **The per-cyclic-factor 2-adic-valuation distribution bound (S7b).**

In a finite cyclic group `G` of even order, no single "2-adic-valuation-of-order" class exceeds
half the group:
```
2 · #{a ∈ G : v₂(orderOf a) = k} ≤ |G|     for every k.
```
where `v₂(orderOf a) = (orderOf a).factorization 2`.

Route: generator bijection `t : Fin n ↦ g ^ t`, the valuation fact `v2_orderOf_pow`, and parity
counting (`card_odd_fin` / `card_even_fin`). The class `k = c := v₂ n` injects into the odd
residues; every class `k ≠ c` injects into the even residues; each parity class has `n/2` elements.
-/
theorem card_v2_orderOf_le {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (hev : Even (Fintype.card G)) (k : ℕ) :
    2 * (Finset.univ.filter (fun a : G => (orderOf a).factorization 2 = k)).card
      ≤ Fintype.card G := by
  classical
  set n := Fintype.card G with hn
  -- pick a generator
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgord : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  -- the power bijection Fin n ≃ G
  have hbij : Function.Bijective (fun t : Fin n => g ^ (t : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by rw [Fintype.card_fin]⟩
    intro i j hij
    simp only at hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := g)
    · simp only [Set.mem_Iio]; rw [hgord]; exact i.isLt
    · simp only [Set.mem_Iio]; rw [hgord]; exact j.isLt
    · exact hij
  set e : Fin n ≃ G := Equiv.ofBijective _ hbij with he
  -- transport the class filter from G to Fin n along e
  have hemap : ∀ t : Fin n, e t = g ^ (t : ℕ) := fun t => rfl
  have htransport :
      (Finset.univ.filter (fun a : G => (orderOf a).factorization 2 = k)).card
        = (Finset.univ.filter
            (fun t : Fin n => (orderOf (g ^ (t : ℕ))).factorization 2 = k)).card := by
    rw [← Finset.card_image_of_injective
      (Finset.univ.filter (fun t : Fin n => (orderOf (g ^ (t : ℕ))).factorization 2 = k))
      e.injective]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ha
      refine ⟨e.symm a, ?_, ?_⟩
      · rw [← hemap (e.symm a), e.apply_symm_apply]; exact ha
      · exact e.apply_symm_apply a
    · rintro ⟨t, ht, rfl⟩
      rw [hemap t]; exact ht
  rw [htransport]
  -- c := v₂ n ; c ≥ 1 since n even
  set c := n.factorization 2 with hc
  have hn0 : n ≠ 0 := Fintype.card_ne_zero
  have hcpos : 1 ≤ c := by
    rw [hc, Nat.one_le_iff_ne_zero, Ne, Nat.factorization_eq_zero_iff]
    push_neg
    exact ⟨Nat.prime_two, even_iff_two_dvd.mp hev, hn0⟩
  -- It suffices to show the class injects into a parity class of `Fin n` (card `n/2`).
  -- Case split on `k = c`.
  by_cases hk : k = c
  · -- class `k = c` ⊆ odd residues
    subst hk
    have hle : (Finset.univ.filter
        (fun t : Fin n => (orderOf (g ^ (t : ℕ))).factorization 2 = c)).card
        ≤ (Finset.univ.filter (fun t : Fin n => ¬ 2 ∣ (t : ℕ))).card := by
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      -- ht : v₂(orderOf(g^t)) = c.  Show ¬ 2 ∣ t.
      rcases Nat.eq_zero_or_pos (t : ℕ) with ht0 | htpos
      · -- t = 0 ⟹ orderOf(g^0) = 1, v₂ = 0 ≠ c (c ≥ 1) — contradiction
        rw [ht0, pow_zero, orderOf_one] at ht
        simp at ht
        omega
      · -- t > 0 : use the valuation fact
        rw [v2_orderOf_pow hgord htpos t.isLt] at ht
        -- ht : c - min(c, v₂ t) = c  ⟹ min = 0 ⟹ v₂ t = 0 ⟹ ¬ 2 ∣ t
        have hmin : min c ((t : ℕ).factorization 2) = 0 := by omega
        have hvt : (t : ℕ).factorization 2 = 0 := by
          rcases Nat.le_total c ((t:ℕ).factorization 2) with h | h
          · rw [min_eq_left h] at hmin; omega
          · rw [min_eq_right h] at hmin; exact hmin
        intro hcon
        rw [Nat.factorization_eq_zero_iff] at hvt
        rcases hvt with h | h | h
        · exact h Nat.prime_two
        · exact h hcon
        · omega
    rw [card_odd_fin n] at hle
    omega
  · -- class `k ≠ c` ⊆ even residues
    have hle : (Finset.univ.filter
        (fun t : Fin n => (orderOf (g ^ (t : ℕ))).factorization 2 = k)).card
        ≤ (Finset.univ.filter (fun t : Fin n => 2 ∣ (t : ℕ))).card := by
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      -- ht : v₂(orderOf(g^t)) = k ≠ c.  Show 2 ∣ t.
      rcases Nat.eq_zero_or_pos (t : ℕ) with ht0 | htpos
      · rw [ht0]; exact Dvd.intro 0 rfl
      · rw [v2_orderOf_pow hgord htpos t.isLt] at ht
        -- ht : c - min(c, v₂ t) = k ≠ c.  Since k ≠ c, min ≠ 0, so v₂ t ≥ 1, so 2 ∣ t.
        have hmin : min c ((t:ℕ).factorization 2) ≠ 0 := by
          intro h0; rw [h0, Nat.sub_zero] at ht; exact hk ht.symm
        have hvt : 1 ≤ (t : ℕ).factorization 2 := by
          rcases Nat.le_total c ((t:ℕ).factorization 2) with h | h
          · rw [min_eq_left h] at hmin; omega
          · rw [min_eq_right h] at hmin; omega
        -- v₂ t ≥ 1 ⟹ 2 ∣ t
        by_contra hcon
        rw [Nat.factorization_eq_zero_of_not_dvd hcon] at hvt
        omega
    rw [card_even_fin n hev] at hle
    omega

/-! ## S7c — the `−1` characterisation (abstract cyclic core)

In a finite cyclic group `G`, the unique order-2 element `z` (e.g. `-1` in a units group) is hit
by `a ^ (R/2)` exactly when the 2-adic valuation of `orderOf a` equals that of `R`. This is the
per-cyclic-factor core of Shor's "`a^(r/2) = -1`" success condition (S7).
-/

/-- **ℕ valuation lemma (Step A).** For `m ∣ R` with `R` even and both nonzero, `m` divides the
half `R/2` iff its 2-adic valuation is *strictly* below that of `R`. The non-2 primes are
unconstrained by halving (`m ∣ R` already bounds them); the `p = 2` slot drops by exactly one
(`Nat.factorization_div` on the divisor `2`, `(2).factorization = single 2 1`). -/
private theorem dvd_half_iff_v2_lt {m R : ℕ} (hm : m ≠ 0) (hR0 : R ≠ 0)
    (h2R : 2 ∣ R) (hmR : m ∣ R) :
    m ∣ (R / 2) ↔ m.factorization 2 < R.factorization 2 := by
  have hR2 : R / 2 ≠ 0 := by
    obtain ⟨k, hk⟩ := h2R; omega
  have hvR1 : 1 ≤ R.factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hR0).mp h2R
  have hfac : (R / 2).factorization = R.factorization - (2 : ℕ).factorization :=
    Nat.factorization_div h2R
  have hfac2 : (R / 2).factorization 2 = R.factorization 2 - 1 := by
    rw [hfac, Finsupp.tsub_apply, Nat.Prime.factorization Nat.prime_two,
      Finsupp.single_eq_same]
  have hfacne : ∀ p, p ≠ 2 → (R / 2).factorization p = R.factorization p := by
    intro p hp
    rw [hfac, Finsupp.tsub_apply, Nat.Prime.factorization Nat.prime_two,
      Finsupp.single_eq_of_ne hp, Nat.sub_zero]
  have hmleR : ∀ p, m.factorization p ≤ R.factorization p := by
    have := (Nat.factorization_le_iff_dvd hm hR0).mpr hmR
    intro p; exact (Finsupp.le_def.mp this) p
  rw [← Nat.factorization_le_iff_dvd hm hR2, Finsupp.le_def]
  constructor
  · intro h
    have h2 := h 2
    rw [hfac2] at h2
    omega
  · intro hlt p
    by_cases hp2 : p = 2
    · subst hp2; rw [hfac2]; omega
    · rw [hfacne p hp2]; exact hmleR p

/-- **Square-root-of-1 dichotomy in a finite cyclic group (Step B).** If `w ^ 2 = 1` and `z` is an
order-2 element of the cyclic group, then `w` is either `1` or `z`: the order-2 elements form a
singleton (`IsCyclic.card_orderOf_eq_totient`, `Nat.totient 2 = 1`), so `w` of order 2 must equal
`z`. -/
private theorem sqrt_one_dichotomy {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    {z : G} (hz : orderOf z = 2) {w : G} (hw : w ^ 2 = 1) :
    w = 1 ∨ w = z := by
  classical
  have h2card : 2 ∣ Fintype.card G := hz ▸ orderOf_dvd_card
  have hsing : (Finset.univ.filter (fun a : G => orderOf a = 2)).card = 1 := by
    rw [IsCyclic.card_orderOf_eq_totient h2card]; decide
  have hwdvd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hw
  rcases (Nat.dvd_prime Nat.prime_two).mp hwdvd with h1 | h2
  · left; exact orderOf_eq_one_iff.mp h1
  · right
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsing
    have hwmem : w ∈ Finset.univ.filter (fun a : G => orderOf a = 2) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h2
    have hzmem : z ∈ Finset.univ.filter (fun a : G => orderOf a = 2) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hz
    rw [hx, Finset.mem_singleton] at hwmem hzmem
    rw [hwmem, hzmem]

/-- **S7c — the `−1` characterisation, abstract cyclic core.**

In a finite cyclic group `G` with unique order-2 element `z`, and `a` an element whose order
divides an even `R ≠ 0`:
```
a ^ (R / 2) = z   ↔   v₂(orderOf a) = v₂(R).
```
`a ^ (R/2)` is a square-root of `1` (its square is `a ^ R = 1`), so by the cyclic dichotomy
(`sqrt_one_dichotomy`) it is `1` or `z`. It is `1` exactly when `orderOf a ∣ R/2`, i.e.
`v₂(orderOf a) < v₂(R)` (`dvd_half_iff_v2_lt`). Since `orderOf a ∣ R` forces
`v₂(orderOf a) ≤ v₂(R)`, the negation of the strict inequality is precisely equality, which is
therefore equivalent to hitting `z`. This is the per-cyclic-factor input to the Shor
`a^(r/2) = -1` success condition. -/
theorem pow_half_eq_orderTwo_iff {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    {z : G} (hz : orderOf z = 2)
    {a : G} {R : ℕ} (hR : Even R) (hR0 : R ≠ 0) (hdvd : orderOf a ∣ R) :
    a ^ (R / 2) = z ↔ (orderOf a).factorization 2 = R.factorization 2 := by
  classical
  set m := orderOf a with hm
  have hm0 : m ≠ 0 := by rw [hm]; exact (orderOf_pos a).ne'
  have h2R : 2 ∣ R := hR.two_dvd
  have hmleR : m.factorization 2 ≤ R.factorization 2 := by
    have := (Nat.factorization_le_iff_dvd hm0 hR0).mpr hdvd
    exact (Finsupp.le_def.mp this) 2
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by decide)
  have hsq : (a ^ (R / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    have : R / 2 * 2 = R := by omega
    rw [this]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hdich := sqrt_one_dichotomy hz hsq
  have heq1 : a ^ (R / 2) = 1 ↔ m.factorization 2 < R.factorization 2 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← hm]
    exact dvd_half_iff_v2_lt hm0 hR0 h2R hdvd
  constructor
  · intro hzeq
    have hne1 : a ^ (R / 2) ≠ 1 := by rw [hzeq]; exact hz1
    have : ¬ (m.factorization 2 < R.factorization 2) := fun h => hne1 (heq1.mpr h)
    omega
  · intro heq
    have hnlt : ¬ (m.factorization 2 < R.factorization 2) := by omega
    have hne1 : a ^ (R / 2) ≠ 1 := fun h => hnlt (heq1.mp h)
    rcases hdich with h | h
    · exact absurd h hne1
    · exact h

/-! ## S7a — two-factor CRT framing for units

The Chinese Remainder Theorem gives a ring isomorphism `ZMod (m*n) ≃+* ZMod m × ZMod n`
for coprime `m, n` (`ZMod.chineseRemainder`). Restricting to units and splitting the product
gives a multiplicative isomorphism `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`. This is the
two-factor framing the S7d assembly needs: it transports `orderOf` to an `lcm` of per-factor
orders (`unitsCRT_orderOf`), sends the success witness `-1` to the per-factor `(-1, -1)`
(`unitsCRT_neg_one`), and factors the group cardinality (`card_units_mul`).

**Cyclicity-agnostic.** Nothing here uses cyclicity of the factors; it holds for any coprime
`m, n`. Cyclicity of the per-prime-power factors enters only in S7d, where this framing is
iterated against the prime-power factorisation of `N`. -/

/-- **The CRT units isomorphism (S7a).** For coprime `m, n`, the units of `ZMod (m*n)` split
as a product of the units of each factor:
`(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.

Built from the ring CRT iso `ZMod.chineseRemainder` by `Units.mapEquiv` (units functor on a
`MulEquiv`) followed by `MulEquiv.prodUnits` (units of a product = product of units). This is the
exact Mathlib idiom used in `Mathlib.RingTheory.ZMod.UnitsCyclic`. -/
noncomputable def unitsCRT {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- **`orderOf` transport across the CRT split (S7a).** The order of a unit of `ZMod (m*n)` is
the least common multiple of the orders of its two CRT components:
`orderOf a = lcm (orderOf (unitsCRT h a).1) (orderOf (unitsCRT h a).2)`.

A `MulEquiv` preserves `orderOf` (`MulEquiv.orderOf_eq`), and `orderOf` of a pair is the `lcm`
of the component orders (`Prod.orderOf`). This is the lcm fact the S7d counting bound consumes. -/
theorem unitsCRT_orderOf {m n : ℕ} (h : m.Coprime n) (a : (ZMod (m * n))ˣ) :
    orderOf a = Nat.lcm (orderOf (unitsCRT h a).1) (orderOf (unitsCRT h a).2) := by
  rw [← (unitsCRT h).orderOf_eq a, Prod.orderOf]

/-- **The `-1` split (S7a).** The CRT units iso sends the success witness `-1` to the per-factor
`(-1, -1)`. The iso is induced from a ring isomorphism, which sends `-1 ↦ -1`; the units functor
and `prodUnits` preserve this. Proved by `Units.ext`/`Prod.ext` reduction to the underlying ring
values, where `RingEquiv.map_neg_one` (via `map_neg`, `map_one`) fires. -/
theorem unitsCRT_neg_one {m n : ℕ} (h : m.Coprime n) :
    unitsCRT h (-1) = (-1, -1) := by
  apply Prod.ext
  · -- first component, as units of `ZMod m`
    apply Units.ext
    show ((unitsCRT h (-1)).1 : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m)
    simp only [unitsCRT, MulEquiv.trans_apply, MulEquiv.prodUnits,
      MulEquiv.coe_mk, Equiv.coe_fn_mk, MonoidHom.prod_apply, Units.coe_map,
      MonoidHom.coe_fst, Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe,
      RingEquiv.coe_toMulEquiv, MulEquiv.coe_mk, Units.val_neg, Units.val_one]
    rw [map_neg, map_one, Prod.fst_neg, Prod.fst_one]
  · -- second component, as units of `ZMod n`
    apply Units.ext
    show ((unitsCRT h (-1)).2 : ZMod n) = ((-1 : (ZMod n)ˣ) : ZMod n)
    simp only [unitsCRT, MulEquiv.trans_apply, MulEquiv.prodUnits,
      MulEquiv.coe_mk, Equiv.coe_fn_mk, MonoidHom.prod_apply, Units.coe_map,
      MonoidHom.coe_snd, Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe,
      RingEquiv.coe_toMulEquiv, MulEquiv.coe_mk, Units.val_neg, Units.val_one]
    rw [map_neg, map_one, Prod.snd_neg, Prod.snd_one]

/-- **Cardinality factorisation (S7a).** For coprime `m, n` (both nonzero), the number of units of
`ZMod (m*n)` is the product of the per-factor unit counts:
`#(ZMod (m*n))ˣ = #(ZMod m)ˣ · #(ZMod n)ˣ`.

Transport the cardinality across `unitsCRT` (`Fintype.card_congr`) and split the product
(`Fintype.card_prod`). (Equivalently `ZMod.card_units_eq_totient` + `Nat.totient_mul`.) -/
theorem card_units_mul {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
    Fintype.card (ZMod (m * n))ˣ
      = Fintype.card (ZMod m)ˣ * Fintype.card (ZMod n)ˣ := by
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [Fintype.card_congr (unitsCRT h).toEquiv, Fintype.card_prod]

/-! ## S7d-1 — the diagonal count (abstract)

The per-factor distribution bound `card_v2_orderOf_le` (S7b) summed over a second finite group.
For a finite group `G₁` and a finite cyclic group `G₂` of even order, the "matched-v₂" diagonal
`{(p₁, p₂) : v₂(orderOf p₁) = v₂(orderOf p₂)}` of the product is no more than half:
```
2 · #{(p₁, p₂) : v₂(orderOf p₁) = v₂(orderOf p₂)} ≤ |G₁| · |G₂|.
```
This is the abstract counting step the S7d assembly iterates against the prime-power factorisation:
only the second factor needs cyclicity / even order; the first is an arbitrary finite group the
count sums over.
-/

/-- **S7d-1 — the diagonal count (abstract).** For a finite group `G₁` and a finite cyclic group
`G₂` of even order, the matched-2-adic-valuation diagonal of the product group is at most half:
```
2 · #{(p₁, p₂) : v₂(orderOf p₁) = v₂(orderOf p₂)} ≤ |G₁| · |G₂|.
```

Route: decompose the product-filter cardinality into a sum over the first coordinate
(`Finset.card_filter` + `Fintype.sum_prod_type`), recognise each fiber as S7b's filter at
`k = v₂(orderOf a₁)`, apply `card_v2_orderOf_le (G := G₂)` per fiber, and sum
(`Finset.mul_sum` + `Finset.sum_le_sum` + `Finset.sum_const`). Only `G₂` carries
`IsCyclic` / `Even`; `G₁` is the summation index. -/
theorem two_mul_card_diag_le {G₁ G₂ : Type*}
    [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] [IsCyclic G₂]
    (h₂ : Even (Fintype.card G₂)) :
    2 * (Finset.univ.filter (fun p : G₁ × G₂ =>
        (orderOf p.1).factorization 2 = (orderOf p.2).factorization 2)).card
      ≤ Fintype.card G₁ * Fintype.card G₂ := by
  classical
  -- Step 1: decompose the product-filter card into a sum over the first coordinate.
  -- `Finset.card_filter` turns the card into a sum of `if`-indicators, `Fintype.sum_prod_type`
  -- splits the product sum, and `Finset.card_filter` recombines the inner sum. The inner
  -- predicate `v₂(orderOf a₂) = v₂(orderOf a₁)` is the product predicate at `p = (a₁, a₂)`
  -- read off-diagonally (`eq` is symmetric), handled in the per-summand `if`-branches.
  have hdecomp :
      (Finset.univ.filter (fun p : G₁ × G₂ =>
          (orderOf p.1).factorization 2 = (orderOf p.2).factorization 2)).card
        = ∑ a₁ : G₁, (Finset.univ.filter
            (fun a₂ : G₂ => (orderOf a₂).factorization 2
              = (orderOf a₁).factorization 2)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a₁ _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a₂ _
    by_cases h : (orderOf a₂).factorization 2 = (orderOf a₁).factorization 2
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [hdecomp, Finset.mul_sum]
  -- Step 2/3: bound each fiber by S7b and sum the constant bound.
  calc ∑ a₁ : G₁, 2 * (Finset.univ.filter
            (fun a₂ : G₂ => (orderOf a₂).factorization 2
              = (orderOf a₁).factorization 2)).card
      ≤ ∑ _a₁ : G₁, Fintype.card G₂ := by
          apply Finset.sum_le_sum
          intro a₁ _
          exact card_v2_orderOf_le (G := G₂) h₂ ((orderOf a₁).factorization 2)
    _ = Fintype.card G₁ * Fintype.card G₂ := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## S7d-2a — the BAD characterisation (abstract two-factor core)

For a product `p = (p₁, p₂)` of two finite cyclic groups, each carrying a distinguished order-2
element (`z₁`, `z₂`, playing the role of `−1`), Shor's per-pair success witness is `r` even and
`p ^ (r/2) ≠ (z₁, z₂)` (where `r = orderOf p`). The complementary **BAD** event — the failure of
that witness — is characterised purely arithmetically: it holds iff the two component orders share
the same 2-adic valuation.

This is the two-factor heart of S7d: combined with the CRT split (`unitsCRT*`, S7a) and the
diagonal count (`two_mul_card_diag_le`, S7d-1) it turns the success-probability bound into the
matched-`v₂` diagonal count.
-/

/-- **S7d-2a — the BAD characterisation (abstract).** For a pair `p = (p₁, p₂)` of finite cyclic
groups with distinguished order-2 elements `z₁`, `z₂`, the Shor "BAD" event
`¬ (Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂))` holds iff the two components share the
same 2-adic valuation of order:
```
¬ (Even r ∧ p ^ (r/2) ≠ (z₁, z₂))   ↔   v₂(orderOf p₁) = v₂(orderOf p₂),    r := orderOf p.
```

Route: `Prod.orderOf` gives `r = lcm (orderOf p₁) (orderOf p₂)`, so (`Nat.factorization_lcm`)
`v₂ r = max (v₂ orderOf p₁) (v₂ orderOf p₂)`. `Even r ↔ 1 ≤ v₂ r` (`even_iff_two_dvd` +
`Nat.Prime.dvd_iff_one_le_factorization`). Splitting the product power componentwise
(`Prod.pow_fst` / `Prod.pow_snd`) and applying `pow_half_eq_orderTwo_iff` (S7c) per factor (with
the component-order divisibility `orderOf pᵢ ∣ r` from `Nat.dvd_lcm_left/right`) turns the
"`p^(r/2) = (z₁,z₂)`" condition into `v₂ orderOf p₁ = v₂ r ∧ v₂ orderOf p₂ = v₂ r`. A case split on
`Even r` plus `omega` (which handles `Nat.max`) collapses both disjuncts to `v₂ p₁ = v₂ p₂`. -/
theorem bad_iff_v2_eq {G₁ G₂ : Type*}
    [Group G₁] [Fintype G₁] [IsCyclic G₁] [Group G₂] [Fintype G₂] [IsCyclic G₂]
    {z₁ : G₁} (hz₁ : orderOf z₁ = 2) {z₂ : G₂} (hz₂ : orderOf z₂ = 2)
    (p : G₁ × G₂) :
    (¬ (Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)))
      ↔ (orderOf p.1).factorization 2 = (orderOf p.2).factorization 2 := by
  classical
  set a₁ := p.1 with ha₁
  set a₂ := p.2 with ha₂
  set d₁ := (orderOf a₁).factorization 2 with hd₁
  set d₂ := (orderOf a₂).factorization 2 with hd₂
  set r := orderOf p with hrdef
  have ho₁ : orderOf a₁ ≠ 0 := (orderOf_pos a₁).ne'
  have ho₂ : orderOf a₂ ≠ 0 := (orderOf_pos a₂).ne'
  have hr0 : r ≠ 0 := (orderOf_pos p).ne'
  -- r = lcm of component orders
  have hr : r = Nat.lcm (orderOf a₁) (orderOf a₂) := by
    rw [hrdef, Prod.orderOf]
  -- v₂ r = max d₁ d₂
  have hv2 : r.factorization 2 = max d₁ d₂ := by
    rw [hr, Nat.factorization_lcm ho₁ ho₂, hd₁, hd₂]
    rfl
  -- Even r ↔ 1 ≤ max d₁ d₂
  have hEvenIff : Even r ↔ 1 ≤ max d₁ d₂ := by
    rw [even_iff_two_dvd,
      Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hr0, hv2]
  -- component divisibility
  have hdvd₁ : orderOf a₁ ∣ r := hr ▸ Nat.dvd_lcm_left _ _
  have hdvd₂ : orderOf a₂ ∣ r := hr ▸ Nat.dvd_lcm_right _ _
  -- rewrite the LHS via `not_and_or`, `not_not`
  rw [not_and_or, not_not]
  -- componentwise power split
  have hsplit : p ^ (r / 2) = (z₁, z₂) ↔ a₁ ^ (r / 2) = z₁ ∧ a₂ ^ (r / 2) = z₂ := by
    rw [Prod.ext_iff, ha₁, ha₂, Prod.pow_fst, Prod.pow_snd]
  rw [hsplit]
  -- case split on `Even r`
  by_cases hev : Even r
  · -- Even r: the `¬ Even r` disjunct is false; reduce to the conjunction
    have hmax : 1 ≤ max d₁ d₂ := hEvenIff.mp hev
    have hc₁ := pow_half_eq_orderTwo_iff (z := z₁) hz₁ hev hr0 hdvd₁
    have hc₂ := pow_half_eq_orderTwo_iff (z := z₂) hz₂ hev hr0 hdvd₂
    rw [hv2] at hc₁ hc₂
    -- hc₁ : a₁ ^ (r/2) = z₁ ↔ d₁ = max d₁ d₂ ; hc₂ similarly
    rw [hc₁, hc₂]
    constructor
    · rintro (h | h)
      · exact absurd hev h
      · obtain ⟨e₁, e₂⟩ := h; omega
    · intro h
      right
      omega
  · -- ¬ Even r: the `¬ Even r` disjunct is true; both sides hold
    have hmax : max d₁ d₂ = 0 := by
      by_contra h
      exact hev (hEvenIff.mpr (by omega))
    constructor
    · intro _
      omega
    · intro _
      left
      exact hev

/-! ## S7d-2b-i — the abstract GOOD lower bound

The complement of the S7d-2a BAD characterisation against the S7d-1 diagonal count. The Shor
per-pair **GOOD** event is `Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)` (`r` even and the
half-power misses the joint `(z₁, z₂) = (−1, −1)` witness). GOOD is at least half:
```
|G₁| · |G₂| ≤ 2 · #GOOD.
```
-/

open Classical in
/-- **S7d-2b-i — the abstract GOOD lower bound.** For a pair of finite cyclic groups `G₁`, `G₂`
each with a distinguished order-2 element (`z₁`, `z₂`), the Shor "GOOD" event
`Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)` covers at least half the product group:
```
|G₁| · |G₂| ≤ 2 · #{p : Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)}.
```

Route (mechanical, no new math): `bad_iff_v2_eq` (S7d-2a) identifies the BAD filter (`¬ GOOD`) with
the matched-`v₂` diagonal filter via `Finset.filter_congr`; `card_filter_add_card_filter_not` gives
`#GOOD + #BAD = |G₁ × G₂|` (`Fintype.card_prod`); `two_mul_card_diag_le` (S7d-1) gives
`2 · #BAD ≤ |G₁|·|G₂|`. `omega` on `A + B = C`, `2·B ≤ C` ⟹ `C ≤ 2·A`. Even order of `G₂` is
derived from `hz₂` (`orderOf_dvd_card`). -/
theorem two_mul_card_good_ge {G₁ G₂ : Type*}
    [Group G₁] [Fintype G₁] [IsCyclic G₁] [Group G₂] [Fintype G₂] [IsCyclic G₂]
    {z₁ : G₁} (hz₁ : orderOf z₁ = 2) {z₂ : G₂} (hz₂ : orderOf z₂ = 2) :
    Fintype.card G₁ * Fintype.card G₂ ≤
      2 * (Finset.univ.filter (fun p : G₁ × G₂ =>
        Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂))).card := by
  classical
  -- `G₂` has even order: `orderOf z₂ = 2 ∣ |G₂|`.
  have h₂ : Even (Fintype.card G₂) :=
    even_iff_two_dvd.mpr (hz₂ ▸ orderOf_dvd_card)
  -- The BAD filter (`¬ GOOD`) equals the matched-`v₂` diagonal filter (S7d-2a).
  have hcongr :
      (Finset.univ.filter (fun p : G₁ × G₂ =>
          ¬ (Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂))))
        = (Finset.univ.filter (fun p : G₁ × G₂ =>
            (orderOf p.1).factorization 2 = (orderOf p.2).factorization 2)) :=
    Finset.filter_congr (fun p _ => bad_iff_v2_eq hz₁ hz₂ p)
  -- GOOD + BAD = |G₁ × G₂| = |G₁| · |G₂|.
  have hcomp :
      (Finset.univ.filter (fun p : G₁ × G₂ =>
          Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂))).card
        + (Finset.univ.filter (fun p : G₁ × G₂ =>
            ¬ (Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)))).card
        = Fintype.card G₁ * Fintype.card G₂ := by
    have hsplit :
        (Finset.univ.filter (fun p : G₁ × G₂ =>
            Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂))).card
          + (Finset.univ.filter (fun p : G₁ × G₂ =>
              ¬ (Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)))).card
          = (Finset.univ : Finset (G₁ × G₂)).card :=
      Finset.card_filter_add_card_filter_not
        (fun p : G₁ × G₂ => Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂))
    rw [Finset.card_univ, Fintype.card_prod] at hsplit
    exact hsplit
  -- 2 · #BAD ≤ |G₁| · |G₂| (S7d-1, rewritten to the BAD filter via `← hcongr`).
  have hdiag :
      2 * (Finset.univ.filter (fun p : G₁ × G₂ =>
          ¬ (Even (orderOf p) ∧ p ^ (orderOf p / 2) ≠ (z₁, z₂)))).card
        ≤ Fintype.card G₁ * Fintype.card G₂ := by
    rw [hcongr]; exact two_mul_card_diag_le h₂
  omega

/-! ## S7d-2b-ii — the general coprime transport (S7★ closing piece)

The abstract GOOD lower bound `two_mul_card_good_ge` (S7d-2b-i) is stated over a product of two
finite cyclic groups with distinguished order-2 elements. To land it on the actual units group
`(ZMod N)ˣ` of a composite `N = m·n` (coprime `m, n`), transport along the CRT units iso
`unitsCRT` (S7a): the Shor per-pair predicate `Even (orderOf a) ∧ a^(orderOf a/2) ≠ -1` corresponds
across `e := unitsCRT` to the product predicate against `(-1, -1)`, because `e` preserves `orderOf`
(`unitsCRT_orderOf` / `MulEquiv.orderOf_eq`) and sends `-1 ↦ (-1, -1)` (`unitsCRT_neg_one`). A
filter-card bijection (`Finset.card_bij` along `e`) plus the cardinality factorisation
`card_units_mul` then carries the bound onto `(ZMod (m·n))ˣ`.
-/

open Classical in
/-- **S7d-2b-ii — the general coprime transport.** For coprime `m, n` with cyclic unit groups
each having `orderOf (-1) = 2`, the Shor "GOOD" event covers at least half of `(ZMod (m·n))ˣ`:
```
|(ZMod (m·n))ˣ| ≤ 2 · #{a : Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1}.
```

Route: transport `two_mul_card_good_ge` (S7d-2b-i) across `unitsCRT h : (ZMod (m·n))ˣ ≃*
(ZMod m)ˣ × (ZMod n)ˣ` (S7a). The Shor predicate corresponds across the iso (`unitsCRT` preserves
`orderOf` via `MulEquiv.orderOf_eq` and sends `-1 ↦ (-1, -1)` via `unitsCRT_neg_one`), giving a
filter-card bijection (`Finset.card_bij`); `card_units_mul` factors `|(ZMod (m·n))ˣ|`. -/
theorem shor_good_transport {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n)
    [IsCyclic (ZMod m)ˣ] [IsCyclic (ZMod n)ˣ]
    (hm : orderOf (-1 : (ZMod m)ˣ) = 2) (hn : orderOf (-1 : (ZMod n)ˣ) = 2) :
    Fintype.card (ZMod (m * n))ˣ ≤
      2 * (Finset.univ.filter (fun a : (ZMod (m * n))ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card := by
  set e := unitsCRT hmn with he
  have horder : ∀ a, orderOf (e a) = orderOf a := fun a => (e.orderOf_eq a)
  have hneg : e (-1) = (-1, -1) := unitsCRT_neg_one hmn
  -- predicate transport across the iso `e`
  have hpred : ∀ a : (ZMod (m * n))ˣ,
      (Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)
        ↔ (Even (orderOf (e a)) ∧ (e a) ^ (orderOf (e a) / 2) ≠ (-1, -1)) := by
    intro a
    rw [horder a]
    apply and_congr_right
    intro _
    constructor
    · intro h hc
      apply h
      have : e (a ^ (orderOf a / 2)) = e (-1) := by rw [map_pow, hc, hneg]
      exact (EmbeddingLike.apply_eq_iff_eq e).mp this
    · intro h hc
      apply h
      rw [← hneg, ← hc, map_pow]
  -- filter-card transport: `e` restricts to a bijection of the GOOD filters
  have hcard :
      (Finset.univ.filter (fun a : (ZMod (m * n))ˣ =>
          Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card
        = (Finset.univ.filter (fun b : (ZMod m)ˣ × (ZMod n)ˣ =>
          Even (orderOf b) ∧ b ^ (orderOf b / 2) ≠ (-1, -1))).card := by
    apply Finset.card_bij (fun a _ => e a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (hpred a).mp ha
    · intro a₁ _ a₂ _ h
      exact e.injective h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      refine ⟨e.symm b, ?_, ?_⟩
      · rw [(hpred (e.symm b)), e.apply_symm_apply]; exact hb
      · exact e.apply_symm_apply b
  -- assemble: S7d-2b-i on the product, then factor the card and transport the filter
  have hbound := two_mul_card_good_ge (G₁ := (ZMod m)ˣ) (G₂ := (ZMod n)ˣ) hm hn
  rw [card_units_mul hmn, hcard]
  convert hbound using 4

/-! ## S7★ — the prime-power headline

Instantiating the general coprime transport at `m = p^α`, `n = q^β` for distinct odd primes `p, q`
gives the Shor random-`a` success bound on the actual units group of a (two-prime-power) composite
modulus: a uniformly random unit is GOOD (yields a non-trivial factor via the order-finding step)
with probability at least `1/2`.

The per-factor hypotheses of `shor_good_transport` are discharged from primality: coprimality via
`Nat.Coprime.pow` on `Nat.coprime_primes`; cyclicity via `ZMod.isCyclic_units_of_prime_pow`
(the odd-prime-power units group is cyclic); and `orderOf (-1) = 2` via `orderOf_neg_one`
(`= 2` since `ringChar (ZMod (p^α)) = p^α ≠ 2` for `p` an odd prime, `α ≥ 1`).
-/

/-- **S7★ — Shor random-`a` success, prime-power headline.** For distinct odd primes `p ≠ q` and
exponents `α, β ≥ 1`, the Shor "GOOD" event covers at least half of `(ZMod (p^α·q^β))ˣ`:
```
|(ZMod (p^α·q^β))ˣ| ≤ 2 · #{a : Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1}.
```

A uniformly random unit `a` mod `N = p^α·q^β` has even multiplicative order and `a^(r/2) ≢ -1`
(so the order-finding step yields a non-trivial factor of `N`) with probability `≥ 1/2`. Proof:
instantiate `shor_good_transport` (S7d-2b-ii) at `m = p^α`, `n = q^β`, discharging coprimality
(`Nat.Coprime.pow`), cyclicity (`ZMod.isCyclic_units_of_prime_pow`), and `orderOf (-1) = 2`
(`orderOf_neg_one` with `ringChar = p^α ≠ 2`).

The `[Fact p.Prime] [Fact q.Prime]` instance arguments are required only so the statement's
`Fintype (ZMod (p^α·q^β))ˣ` synthesises (via `NeZero (p^α)`, derived from `Fact p.Prime`); they
carry no content beyond the explicit `hp`, `hq`. -/
theorem shor_random_a_success {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) {α β : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    Fintype.card (ZMod (p ^ α * q ^ β))ˣ ≤
      2 * (Finset.univ.filter (fun a : (ZMod (p ^ α * q ^ β))ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card := by
  have hcop : (p ^ α).Coprime (q ^ β) :=
    Nat.Coprime.pow α β ((Nat.coprime_primes hp hq).mpr hpq)
  have hcyc_m : IsCyclic (ZMod (p ^ α))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 α
  have hcyc_n : IsCyclic (ZMod (q ^ β))ˣ := ZMod.isCyclic_units_of_prime_pow q hq hq2 β
  -- orderOf (-1) = 2 in each odd-prime-power units group
  have hm : orderOf (-1 : (ZMod (p ^ α))ˣ) = 2 := by
    have hne2 : p ^ α ≠ 2 := by
      have h3 : 3 ≤ p := by
        rcases hp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · have := hp.two_le; omega
      have : 3 ≤ p ^ α := le_trans h3 (Nat.le_self_pow (by omega) p)
      omega
    have hfact : Fact (1 < p ^ α) := ⟨by
      calc 1 < p := hp.one_lt
        _ ≤ p ^ α := Nat.le_self_pow (by omega) p⟩
    have : Nontrivial (ZMod (p ^ α)) := ZMod.nontrivial _
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
      ZMod.ringChar_zmod_n, if_neg hne2]
  have hn : orderOf (-1 : (ZMod (q ^ β))ˣ) = 2 := by
    have hne2 : q ^ β ≠ 2 := by
      have h3 : 3 ≤ q := by
        rcases hq.eq_two_or_odd with h | h
        · exact absurd h hq2
        · have := hq.two_le; omega
      have : 3 ≤ q ^ β := le_trans h3 (Nat.le_self_pow (by omega) q)
      omega
    have hfact : Fact (1 < q ^ β) := ⟨by
      calc 1 < q := hq.one_lt
        _ ≤ q ^ β := Nat.le_self_pow (by omega) q⟩
    have : Nontrivial (ZMod (q ^ β)) := ZMod.nontrivial _
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
      ZMod.ringChar_zmod_n, if_neg hne2]
  exact shor_good_transport hcop hm hn

/-- **S7★ — Shor random-`a` success, probability reading.** The counting bound
`shor_random_a_success` restated as a probability: under uniform sampling of a unit
`a` mod `N = p^α·q^β` (distinct odd primes, `α, β ≥ 1`), the success probability
`#GOOD / #units` is at least `1/2`:
```
1/2 ≤ #{a : Even (orderOf a) ∧ a^(orderOf a/2) ≠ -1} / |(ZMod N)ˣ|.
```

Pure `ℚ`-arithmetic corollary of `shor_random_a_success` (`|units| ≤ 2·#GOOD`): clear the
denominator (`le_div_iff₀`, with `0 < |units|` from `Fintype.card_pos` — a units group is
nonempty via `1`), `push_cast`, and `linarith` against the cast counting bound. -/
theorem shor_success_prob_ge {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) {α β : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (1 : ℚ) / 2 ≤
      ((Finset.univ.filter (fun a : (ZMod (p ^ α * q ^ β))ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℚ)
        / (Fintype.card (ZMod (p ^ α * q ^ β))ˣ : ℚ) := by
  -- the counting bound: |units| ≤ 2 · #GOOD (same GOOD filter)
  have hcard := shor_random_a_success hp hq hp2 hq2 hpq hα hβ
  -- |units| > 0 : the units group is nonempty (`1` is a unit)
  have hpos : 0 < Fintype.card (ZMod (p ^ α * q ^ β))ˣ :=
    Fintype.card_pos
  have hposq : (0 : ℚ) < (Fintype.card (ZMod (p ^ α * q ^ β))ˣ : ℚ) := by
    exact_mod_cast hpos
  rw [le_div_iff₀ hposq]
  -- goal: 1/2 * |units| ≤ #GOOD ; from |units| ≤ 2·#GOOD over ℕ, cast to ℚ
  have hcardq : (Fintype.card (ZMod (p ^ α * q ^ β))ˣ : ℚ)
      ≤ 2 * ((Finset.univ.filter (fun a : (ZMod (p ^ α * q ^ β))ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℚ) := by
    exact_mod_cast hcard
  linarith

/-! ## gen-C — the `m`-fold diagonal count (abstract)

The general-`m` analogue of `two_mul_card_diag_le` (S7d-1). For a finite indexed family of finite
cyclic groups `(G i)` where the distinguished factor `i₀` has even order, the "fully matched"
diagonal — tuples whose components ALL share the same 2-adic valuation of order — is at most half
the product group:
```
2 · #{f : ∀ i, v₂(orderOf (f i)) = v₂(orderOf (f i₀))} ≤ ∏ i, |G i|.
```
Only the distinguished factor `i₀` needs even order; the remaining factors are summed over.

Route (product-of-sums): partition the diagonal by the common valuation `k`
(`Finset.card_eq_sum_card_fiberwise` along the key `f ↦ v₂(orderOf (f i₀))`); each fiber is a
`Fintype.piFinset` of per-component valuation classes, so its card is `∏ i, cₖ(i)`
(`Fintype.card_piFinset`); factor out `i₀` (`Finset.mul_prod_erase`) and bound `2·cₖ(i₀) ≤ |G i₀|`
by `card_v2_orderOf_le` (S7b); the remaining erased sum `∑ₖ ∏_{i≠i₀} cₖ(i)` is bounded by
`∏_{i≠i₀} |G i|` via a disjoint-`biUnion` count of the per-`k` `piFinset`s over the subtype
`{i // i ≠ i₀}` (disjoint because membership pins `v₂(orderOf (g i)) = k` for every `i ≠ i₀`,
so all the free components agree on `k`).

**Spec correction (load-bearing hypothesis surfaced).** The task statement omitted any free factor
besides `i₀`; as literally stated the theorem is FALSE when `ι` is a singleton `{i₀}`: there the
diagonal predicate `∀ i, v₂(orderOf (f i)) = v₂(orderOf (f i₀))` reduces to the tautology
`v₂(orderOf (f i₀)) = v₂(orderOf (f i₀))`, so the filter is all of `univ` and `2·|univ| ≤ |G i₀|`
i.e. `2·N ≤ N` fails for `N > 0`. The two-factor `two_mul_card_diag_le` is true precisely because
`G₁` is an always-present free factor that the count sums over; the faithful `m`-fold analogue must
carry a free factor, here as `(i₁ : ι) (hi₁ : i₁ ≠ i₀)`. This is not a weakening of the intended
content (the intended content is the genuinely-summed `m`-fold diagonal with `m ≥ 2`); it names the
hypothesis that was silently required. -/
open Classical in
theorem two_mul_card_pi_diag_le {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, IsCyclic (G i)]
    (i₀ : ι) (h₀ : Even (Fintype.card (G i₀))) (i₁ : ι) (hi₁ : i₁ ≠ i₀) :
    2 * (Finset.univ.filter (fun f : (Π i, G i) =>
        ∀ i, (orderOf (f i)).factorization 2 = (orderOf (f i₀)).factorization 2)).card
      ≤ ∏ i, Fintype.card (G i) := by
  classical
  -- abbreviations
  set d : ∀ i, G i → ℕ := fun i a => (orderOf a).factorization 2 with hd
  -- per-component valuation-class filter and its cardinality
  set filt : ℕ → ∀ i, Finset (G i) :=
    fun k i => Finset.univ.filter (fun a : G i => d i a = k) with hfilt
  set c : ℕ → ι → ℕ := fun k i => (filt k i).card with hc
  set N : ℕ := Fintype.card (G i₀) with hN
  have hN0 : N ≠ 0 := Fintype.card_ne_zero
  -- the diagonal filter
  set A : Finset (Π i, G i) :=
    Finset.univ.filter (fun f : (Π i, G i) => ∀ i, d i (f i) = d i₀ (f i₀)) with hA
  -- Step 1: partition `A` by the common valuation `k = d i₀ (f i₀) ∈ range (N+1)`.
  have hkey_mapsTo : (↑A : Set (Π i, G i)).MapsTo (fun f => d i₀ (f i₀)) (Finset.range (N + 1)) := by
    intro f _hf
    simp only [Finset.coe_range, Set.mem_Iio]
    -- d i₀ (f i₀) < orderOf (f i₀) ≤ N < N + 1
    have hlt : d i₀ (f i₀) < orderOf (f i₀) := Nat.factorization_lt 2 (orderOf_pos (f i₀)).ne'
    have hle : orderOf (f i₀) ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (hN ▸ orderOf_dvd_card)
    omega
  have hstep1 :
      A.card = ∑ k ∈ Finset.range (N + 1),
        (Finset.univ.filter (fun f : (Π i, G i) => ∀ i, d i (f i) = k)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hkey_mapsTo]
    apply Finset.sum_congr rfl
    intro k _hk
    congr 1
    ext f
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hall, hkey⟩
      intro i; rw [hall i, hkey]
    · intro hall
      exact ⟨fun i => by rw [hall i, hall i₀], hall i₀⟩
  -- Step 2: each fiber is a product of per-component class counts.
  have hfiber : ∀ k,
      (Finset.univ.filter (fun f : (Π i, G i) => ∀ i, d i (f i) = k)).card = ∏ i, c k i := by
    intro k
    have hset :
        (Finset.univ.filter (fun f : (Π i, G i) => ∀ i, d i (f i) = k))
          = Fintype.piFinset (filt k) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hfilt]
    rw [hset, Fintype.card_piFinset]
  -- assemble Steps 1+2: A.card = ∑ₖ ∏ᵢ c k i
  have hAcard : A.card = ∑ k ∈ Finset.range (N + 1), ∏ i, c k i := by
    rw [hstep1]; exact Finset.sum_congr rfl (fun k _ => hfiber k)
  -- Step 3: factor out `i₀` and bound `2 · c k i₀ ≤ N` by S7b.
  have hS7b : ∀ k, 2 * c k i₀ ≤ N := by
    intro k
    have := card_v2_orderOf_le (G := G i₀) h₀ k
    simpa [hc, hfilt, hN, d] using this
  -- Step 4: the erased sum `∑ₖ ∏_{i≠i₀} c k i ≤ ∏_{i≠i₀} |G i|`.
  -- Index by the subtype `{i // i ≠ i₀}`; the per-`k` `piFinset`s are pairwise disjoint.
  have herased :
      (∑ k ∈ Finset.range (N + 1), ∏ i ∈ Finset.univ.erase i₀, c k i)
        ≤ ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) := by
    -- rewrite erased products as products over the subtype `{i // i ≠ i₀}`
    have hsub : ∀ (g : ι → ℕ),
        ∏ i ∈ Finset.univ.erase i₀, g i = ∏ i : {i // i ≠ i₀}, g i.1 := by
      intro g
      refine Finset.prod_subtype (Finset.univ.erase i₀) (p := fun i => i ≠ i₀) ?_ g
      intro x; simp [Finset.mem_erase]
    -- the per-`k` `piFinset` over the subtype
    set B : ℕ → Finset (Π i : {i // i ≠ i₀}, G i.1) :=
      fun k => Fintype.piFinset (fun i : {i // i ≠ i₀} => filt k i.1) with hB
    -- each erased product is the card of `B k`
    have hBcard : ∀ k, ∏ i ∈ Finset.univ.erase i₀, c k i = (B k).card := by
      intro k
      rw [hsub (c k), hB, Fintype.card_piFinset]
    -- the family `B` is pairwise disjoint over `range (N+1)`: any tuple in `B k` pins the free
    -- index `i₁` to valuation `k`, so distinct `k` give disjoint `B k`.
    have hdisj : ((Finset.range (N + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint B := by
      intro j _hj k _hk hjk
      refine Finset.disjoint_left.mpr ?_
      intro g hgj hgk
      apply hjk
      set i₁' : {i // i ≠ i₀} := ⟨i₁, hi₁⟩ with hi₁'
      have hj' : g i₁' ∈ filt j i₁'.1 := (Fintype.mem_piFinset.mp hgj) i₁'
      have hk' : g i₁' ∈ filt k i₁'.1 := (Fintype.mem_piFinset.mp hgk) i₁'
      rw [hfilt, Finset.mem_filter] at hj' hk'
      rw [← hj'.2, hk'.2]
    -- sum of cards = card of disjoint biUnion ≤ Fintype.card of the whole pi-type
    calc (∑ k ∈ Finset.range (N + 1), ∏ i ∈ Finset.univ.erase i₀, c k i)
        = ∑ k ∈ Finset.range (N + 1), (B k).card := by
          exact Finset.sum_congr rfl (fun k _ => hBcard k)
      _ = ((Finset.range (N + 1)).biUnion B).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Π i : {i // i ≠ i₀}, G i.1) := Finset.card_le_univ _
      _ = ∏ i : {i // i ≠ i₀}, Fintype.card (G i.1) := Fintype.card_pi
      _ = ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) :=
          (hsub (fun i => Fintype.card (G i))).symm
  -- Step 5: combine. 2·A.card = ∑ₖ (2·c k i₀)·∏_{erase} c k i ≤ N·∑ₖ ∏_{erase} c k i ≤ ∏ |G i|.
  rw [hAcard, Finset.mul_sum]
  calc (∑ k ∈ Finset.range (N + 1), 2 * ∏ i, c k i)
      = ∑ k ∈ Finset.range (N + 1), (2 * c k i₀) * ∏ i ∈ Finset.univ.erase i₀, c k i := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [← Finset.mul_prod_erase Finset.univ (c k) (Finset.mem_univ i₀)]
        ring
    _ ≤ ∑ k ∈ Finset.range (N + 1), N * ∏ i ∈ Finset.univ.erase i₀, c k i := by
        apply Finset.sum_le_sum
        intro k _hk
        exact Nat.mul_le_mul_right _ (hS7b k)
    _ = N * ∑ k ∈ Finset.range (N + 1), ∏ i ∈ Finset.univ.erase i₀, c k i := by
        rw [Finset.mul_sum]
    _ ≤ N * ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) :=
        Nat.mul_le_mul_left _ herased
    _ = ∏ i, Fintype.card (G i) := by
        rw [hN, Finset.mul_prod_erase Finset.univ (fun i => Fintype.card (G i)) (Finset.mem_univ i₀)]

/-! ## gen-A — indexed-product plumbing for the general-`m` Shor bound

Three reusable facts for the `m`-fold (`ι`-indexed) CRT framing, the indexed analogue of the
two-factor S7a primitives (`unitsCRT*`):

- `orderOf_pi`: the order of a tuple in a finite product is the `lcm` of component orders (the
  `m`-fold `Prod.orderOf`);
- `unitsPiCRT`: the indexed units-CRT iso `(ZMod (∏ N i))ˣ ≃* Π i, (ZMod (N i))ˣ`, built from the
  ring CRT iso `ZMod.prodEquivPi` by the units functor (`Units.mapEquiv`) and the
  units-of-a-product splitting (`MulEquiv.piUnits`) — the `m`-fold analogue of `unitsCRT` (S7a);
- `unitsPiCRT_neg_one`: that iso sends the success witness `-1` to the constant tuple `fun _ => -1`
  (the `m`-fold `unitsCRT_neg_one`).

Cyclicity-agnostic: nothing here uses cyclicity of the factors (it enters only at the assembly,
where `orderOf_pi` feeds the lcm into the `gen-C` diagonal count `two_mul_card_pi_diag_le`). -/

/-- **`orderOf` in a finite indexed product = lcm of component orders (gen-A).** The order of a
tuple `f : Π i, G i` in a finite product of finite monoids is the least common multiple of the
component orders. This is exactly Mathlib's `Pi.orderOf`; re-exported here under the
`CSD.Empirical.QM.Shor` namespace as the named `m`-fold analogue of `Prod.orderOf` (which drives
`unitsCRT_orderOf`, S7a). -/
theorem orderOf_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Monoid (G i)]
    [∀ i, Fintype (G i)] (f : Π i, G i) :
    orderOf f = (Finset.univ : Finset ι).lcm (fun i => orderOf (f i)) :=
  Pi.orderOf f

/-- **The indexed units-CRT isomorphism (gen-A).** For a finite family `N : ι → ℕ` that is
pairwise coprime, the units of `ZMod (∏ i, N i)` split as a product of the units of each factor:
`(ZMod (∏ i, N i))ˣ ≃* Π i, (ZMod (N i))ˣ`.

Built from the ring CRT iso `ZMod.prodEquivPi` by `Units.mapEquiv` (units functor on a `MulEquiv`)
followed by `MulEquiv.piUnits` (units of a product = product of units). This is the `m`-fold
analogue of the two-factor `unitsCRT` (S7a), mirroring its construction exactly. The coprimality
hypothesis is in `ZMod.prodEquivPi`'s native spelling `Pairwise (Function.onFun Nat.Coprime N)`. -/
noncomputable def unitsPiCRT {ι : Type*} [Fintype ι] (N : ι → ℕ)
    (hcop : Pairwise (Function.onFun Nat.Coprime N)) :
    (ZMod (∏ i, N i))ˣ ≃* Π i, (ZMod (N i))ˣ :=
  (Units.mapEquiv (ZMod.prodEquivPi N hcop).toMulEquiv).trans MulEquiv.piUnits

/-- **The `-1` split (gen-A).** The indexed units-CRT iso sends the success witness `-1` to the
constant tuple `fun _ => -1`. The iso is induced from a ring isomorphism, which sends `-1 ↦ -1`;
the units functor and `piUnits` preserve this componentwise. Proved by `funext`/`Units.ext`
reduction to the underlying ring values at each `i`, where the `piUnits` component is defeq to the
underlying coercion of `Units.mapEquiv (…)` at `i`, and `map_neg`/`map_one` of the ring iso fire.
This is the `m`-fold analogue of `unitsCRT_neg_one` (S7a). -/
theorem unitsPiCRT_neg_one {ι : Type*} [Fintype ι] (N : ι → ℕ)
    (hcop : Pairwise (Function.onFun Nat.Coprime N)) :
    unitsPiCRT N hcop (-1) = fun _ => -1 := by
  funext i
  apply Units.ext
  -- the `piUnits` component is defeq to the underlying coercion of `Units.mapEquiv (…)` at `i`
  show ((((Units.mapEquiv (ZMod.prodEquivPi N hcop).toMulEquiv) (-1)) : Π i, ZMod (N i)) i)
      = ((-1 : (ZMod (N i))ˣ) : ZMod (N i))
  rw [Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv,
    Units.val_neg, Units.val_one, map_neg, map_one, Pi.neg_apply, Pi.one_apply,
    Units.val_neg, Units.val_one]

end CSD.Empirical.QM.Shor
