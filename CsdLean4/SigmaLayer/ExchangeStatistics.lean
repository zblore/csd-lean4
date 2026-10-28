/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ManyIdenticalParticles

/-!
# SigmaLayer/ExchangeStatistics: only bosons and fermions

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #216, after ~~#206~~ (`SigmaLayer/IdenticalParticles.lean`) and ~~#214~~
(`SigmaLayer/ManyIdenticalParticles.lean`).

Permuting identical particles should not change the physical state, so it may multiply the
state vector by a number at most. This module proves that the only numbers that can occur are
those of the bosons (always `1`) and of the fermions (the sign of the permutation): there is no
third kind of one-dimensional exchange statistics at finite dimension.

## What is proved

* ★ `map_swap_eq_map_swap` — a multiplicative character of a symmetric group takes one value on
  every transposition (all transpositions are conjugate, `Equiv.Perm.isConj_swap`);
* ★★ `perm_char_eq_one_or_sign` — **the trivial character and the sign are the only characters of
  a symmetric group** with values in an integral domain (`Equiv.Perm.swap_induction_on`), and
  `perm_char_eq_one_or_permSign` on `Fin n`;
* ★★ `eq_one_or_eq_neg_one_of_permOp_swap` — if exchanging two particles multiplies a nonzero
  state by `c`, then `c = ±1`: no exchange phase other than `±1` (no anyons in this setting);
* `IsExchangeEigenstate x` — every permutation keeps the ray of `x`; ★★★
  `isExchangeEigenstate_iff` — **a state whose ray every permutation keeps is a boson or a
  fermion**, and conversely;
* ★★ `le_nBosonSector_or_le_nFermionSector` — a subspace on which each permutation acts as a
  scalar lies in the boson sector or in the fermion sector;
* ★ `eq_zero_of_mem_nBosonSector_of_mem_nFermionSector` — for `n ≥ 2` the two alternatives exclude
  each other on nonzero states;
* ★ `exists_not_isExchangeEigenstate` — three particles in two modes have states whose ray some
  permutation moves: the restriction to exchange eigenstates is a restriction, not a theorem about
  every state;
* ★★★ `exchange_statistics` — the capstone.

## Honest scope

⚠️ **The premise is the postulate's content.** That a permutation of identical particles keeps the
physical state (the ray) is assumed, not derived: it is what "identical" means here. Given it, the
`±1` dichotomy is a theorem. Without it the space also carries the mixed-symmetry components of
~~#214~~'s `sectors_not_exhaustive` (parastatistics), described in ~~#219~~
(`SigmaLayer/MixedSymmetry.lean`).

⚠️ **Spin–statistics proper** — which particles take which sign — needs Lorentz covariance and is
not a finite-dimensional statement; it is BACKLOG #218, on the scope ladder's relativistic rung.

⚠️ **Anyons** are excluded only in this setting, where exchange is a permutation; in two spatial
dimensions the exchange group is the braid group and other phases occur. The corpus has no braid
group arena.

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/ManyIdenticalParticles.lean`
(`permOp`, `permSign`, `nBosonSector`, `nFermionSector`, `sectors_not_exhaustive`);
`SigmaLayer/IdenticalParticles.lean`; Mathlib `Equiv.Perm.isConj_swap`,
`Equiv.Perm.swap_induction_on`, `Equiv.Perm.sign_swap`; `specs/BACKLOG.md` #216.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

/-! ### The characters of a symmetric group -/

section Character

variable {α : Type*} [DecidableEq α]

/-- A multiplicative character of a symmetric group takes one value on every transposition. -/
theorem map_swap_eq_map_swap {M : Type*} [CommMonoid M] (χ : Equiv.Perm α →* M) {w x y z : α}
    (hwx : w ≠ x) (hyz : y ≠ z) : χ (Equiv.swap w x) = χ (Equiv.swap y z) :=
  isConj_iff_eq.1 (χ.map_isConj (Equiv.Perm.isConj_swap hwx hyz))

theorem map_swap_mul_self {M : Type*} [Monoid M] (χ : Equiv.Perm α →* M) (x y : α) :
    χ (Equiv.swap x y) * χ (Equiv.swap x y) = 1 := by
  rw [← map_mul, Equiv.swap_mul_self, map_one]

/-- **The trivial character and the sign are the only characters of a symmetric group** with
values in an integral domain. -/
theorem perm_char_eq_one_or_sign [Fintype α] {R : Type*} [CommRing R] [NoZeroDivisors R]
    (χ : Equiv.Perm α →* R) :
    (∀ σ, χ σ = 1) ∨ ∀ σ, χ σ = ((Equiv.Perm.sign σ : ℤ) : R) := by
  by_cases h : ∃ a b : α, a ≠ b
  · obtain ⟨a, b, hab⟩ := h
    have hall : ∀ x y : α, x ≠ y → χ (Equiv.swap x y) = χ (Equiv.swap a b) :=
      fun x y hxy => map_swap_eq_map_swap χ hxy hab
    rcases mul_self_eq_one_iff.1 (map_swap_mul_self χ a b) with hc | hc
    · refine Or.inl fun σ => Equiv.Perm.swap_induction_on σ (map_one χ) ?_
      intro f x y hxy ih
      rw [map_mul, ih, hall x y hxy, hc, mul_one]
    · refine Or.inr fun σ => Equiv.Perm.swap_induction_on σ (by simp) ?_
      intro f x y hxy ih
      rw [map_mul, ih, hall x y hxy, hc]
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
  · simp only [not_exists, ne_eq, not_not] at h
    refine Or.inl fun σ => ?_
    rw [show σ = 1 from Equiv.ext fun x => h _ _, map_one]

end Character

variable {n N : ℕ}

/-- The characters of `Equiv.Perm (Fin n)` with complex values are `1` and `permSign`. -/
theorem perm_char_eq_one_or_permSign (χ : Equiv.Perm (Fin n) →* ℂ) :
    (∀ σ, χ σ = 1) ∨ ∀ σ, χ σ = permSign σ :=
  perm_char_eq_one_or_sign χ

/-! ### Exchange phases -/

/-- **The exchange phase is `±1`**: if exchanging two particles multiplies a nonzero state by `c`,
then `c = 1` or `c = -1`. -/
theorem eq_one_or_eq_neg_one_of_permOp_swap {x : ManyParticle n N} (hx : x ≠ 0) (i j : Fin n)
    {c : ℂ} (hc : permOp N (Equiv.swap i j) x = c • x) : c = 1 ∨ c = -1 := by
  have h := permOp_mul (N := N) (Equiv.swap i j) (Equiv.swap i j) x
  rw [Equiv.swap_mul_self, permOp_one, hc, map_smul, hc, smul_smul] at h
  have h1 : (c * c) • x = (1 : ℂ) • x := by rw [one_smul]; exact h.symm
  exact mul_self_eq_one_iff.1 (smul_left_injective ℂ hx h1)

/-- **An exchange eigenstate**: every permutation of the particles keeps the ray of `x`. -/
def IsExchangeEigenstate (x : ManyParticle n N) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∃ c : ℂ, permOp N σ x = c • x

theorem isExchangeEigenstate_of_mem_nBosonSector {x : ManyParticle n N}
    (hx : x ∈ nBosonSector n N) : IsExchangeEigenstate x :=
  fun σ => ⟨1, by rw [one_smul]; exact mem_nBosonSector.1 hx σ⟩

theorem isExchangeEigenstate_of_mem_nFermionSector {x : ManyParticle n N}
    (hx : x ∈ nFermionSector n N) : IsExchangeEigenstate x :=
  fun σ => ⟨permSign σ, mem_nFermionSector.1 hx σ⟩

/-- **A state whose ray every permutation keeps is a boson or a fermion.** -/
theorem IsExchangeEigenstate.mem_or_mem {x : ManyParticle n N} (hx : IsExchangeEigenstate x) :
    x ∈ nBosonSector n N ∨ x ∈ nFermionSector n N := by
  by_cases h0 : x = 0
  · exact Or.inl (h0 ▸ Submodule.zero_mem _)
  choose c hc using hx
  have huniq : ∀ σ (d : ℂ), permOp N σ x = d • x → c σ = d :=
    fun σ d hd => smul_left_injective ℂ h0 ((hc σ).symm.trans hd)
  let χ : Equiv.Perm (Fin n) →* ℂ :=
    { toFun := c
      map_one' := huniq 1 1 (by rw [permOp_one, one_smul])
      map_mul' := fun σ τ => huniq (σ * τ) _ (by
        rw [permOp_mul, hc τ, map_smul, hc σ, smul_smul, mul_comm]) }
  rcases perm_char_eq_one_or_permSign χ with h | h
  · refine Or.inl (mem_nBosonSector.2 fun σ => ?_)
    rw [hc σ, show c σ = 1 from h σ, one_smul]
  · refine Or.inr (mem_nFermionSector.2 fun σ => ?_)
    rw [hc σ, show c σ = permSign σ from h σ]

/-- **Exchange eigenstates are exactly the bosons and the fermions.** -/
theorem isExchangeEigenstate_iff {x : ManyParticle n N} :
    IsExchangeEigenstate x ↔ x ∈ nBosonSector n N ∨ x ∈ nFermionSector n N :=
  ⟨IsExchangeEigenstate.mem_or_mem, fun h => h.elim isExchangeEigenstate_of_mem_nBosonSector
    isExchangeEigenstate_of_mem_nFermionSector⟩

/-- **A sector on which each permutation acts as a scalar is bosonic or fermionic.** -/
theorem le_nBosonSector_or_le_nFermionSector {V : Submodule ℂ (ManyParticle n N)}
    (hV : ∀ σ : Equiv.Perm (Fin n), ∃ c : ℂ, ∀ x ∈ V, permOp N σ x = c • x) :
    V ≤ nBosonSector n N ∨ V ≤ nFermionSector n N := by
  by_cases hV0 : V = ⊥
  · exact Or.inl (hV0 ▸ bot_le)
  obtain ⟨x₀, hx₀, h0⟩ := (Submodule.ne_bot_iff V).1 hV0
  choose c hc using hV
  have heig : IsExchangeEigenstate x₀ := fun σ => ⟨c σ, hc σ x₀ hx₀⟩
  rcases heig.mem_or_mem with hb | hf
  · refine Or.inl fun x hx => mem_nBosonSector.2 fun σ => ?_
    have h1 : c σ • x₀ = (1 : ℂ) • x₀ := by rw [one_smul, ← hc σ x₀ hx₀, mem_nBosonSector.1 hb σ]
    rw [hc σ x hx, smul_left_injective ℂ h0 h1, one_smul]
  · refine Or.inr fun x hx => mem_nFermionSector.2 fun σ => ?_
    have h1 : c σ • x₀ = permSign σ • x₀ := by rw [← hc σ x₀ hx₀, mem_nFermionSector.1 hf σ]
    rw [hc σ x hx, smul_left_injective ℂ h0 h1]

/-- For `n ≥ 2` no nonzero state is both a boson and a fermion. -/
theorem eq_zero_of_mem_nBosonSector_of_mem_nFermionSector (hn : 2 ≤ n) {x : ManyParticle n N}
    (hb : x ∈ nBosonSector n N) (hf : x ∈ nFermionSector n N) : x = 0 :=
  inner_self_eq_zero.1 (inner_eq_zero_of_mem_nBosonSector hn hb hf)

/-- **Not every state is an exchange eigenstate**: three particles in two modes, two in mode `0`
and one in mode `1`, as a configuration state. -/
theorem exists_not_isExchangeEigenstate : ∃ x : ManyParticle 3 2, ¬ IsExchangeEigenstate x := by
  refine ⟨WithLp.toLp 2 fun c => if c = ![0, 0, 1] then 1 else 0, fun h => ?_⟩
  rcases h.mem_or_mem with hb | hf
  · have hne : (![0, 0, 1] ∘ Equiv.swap 0 2 : Fin 3 → Fin 2) ≠ ![0, 0, 1] := by decide
    have := mem_nBosonSector_iff_apply.1 hb (Equiv.swap 0 2) ![0, 0, 1]
    simp [hne] at this
  · have := apply_eq_zero_of_not_injective hf (c := ![0, 0, 1]) (by decide)
    simp at this

/-! ### The capstone -/

/-- **Only bosons and fermions.**

1. the characters of the permutation group are `1` and the sign;
2. an exchange of two particles multiplies a nonzero state by `±1` if by anything;
3. a state whose ray every permutation keeps is a boson or a fermion, and conversely;
4. a subspace on which each permutation acts as a scalar is bosonic or fermionic;
5. for `n ≥ 2` the two alternatives exclude each other;
6. three particles in two modes have states that are not exchange eigenstates. -/
theorem exchange_statistics :
    (∀ χ : Equiv.Perm (Fin n) →* ℂ, (∀ σ, χ σ = 1) ∨ ∀ σ, χ σ = permSign σ)
    ∧ (∀ x : ManyParticle n N, x ≠ 0 → ∀ (i j : Fin n) (c : ℂ),
        permOp N (Equiv.swap i j) x = c • x → c = 1 ∨ c = -1)
    ∧ (∀ x : ManyParticle n N,
        IsExchangeEigenstate x ↔ x ∈ nBosonSector n N ∨ x ∈ nFermionSector n N)
    ∧ (∀ V : Submodule ℂ (ManyParticle n N),
        (∀ σ : Equiv.Perm (Fin n), ∃ c : ℂ, ∀ x ∈ V, permOp N σ x = c • x) →
          V ≤ nBosonSector n N ∨ V ≤ nFermionSector n N)
    ∧ (2 ≤ n → ∀ x : ManyParticle n N, x ∈ nBosonSector n N → x ∈ nFermionSector n N → x = 0)
    ∧ ∃ x : ManyParticle 3 2, ¬ IsExchangeEigenstate x :=
  ⟨perm_char_eq_one_or_permSign,
    fun _ hx i j _ hc => eq_one_or_eq_neg_one_of_permOp_swap hx i j hc,
    fun _ => isExchangeEigenstate_iff,
    fun _ hV => le_nBosonSector_or_le_nFermionSector hV,
    fun hn _ hb hf => eq_zero_of_mem_nBosonSector_of_mem_nFermionSector hn hb hf,
    exists_not_isExchangeEigenstate⟩

end CSD.SigmaLayer
