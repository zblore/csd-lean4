import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
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

end CSD.Empirical.QM.Shor
