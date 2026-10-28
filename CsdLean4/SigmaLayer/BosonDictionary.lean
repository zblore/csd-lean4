/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.BosonFock
public import CsdLean4.SigmaLayer.FermionDictionary
public import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# SigmaLayer/BosonDictionary: first and second quantisation as operators, for bosons

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #221, the boson half of ~~#220~~ (`SigmaLayer/FermionDictionary.lean`), after ~~#215~~
(`SigmaLayer/BosonFock.lean`).

## What is proved

* `occNat c` — the occupation numbers of a configuration `c : Fin n → Fin K`: invariant under
  permutations (`occNat_comp_perm`), shifted by one under `Fin.cons` (`occNat_cons`) and under
  removing a particle (`occNat_succAbove`);
* ★★ `card_comp_eq` — **the coset count**: `#{σ | m ∘ σ = c}` is `∏_k P_k!` when `c` and `m` have the
  same occupation numbers `P`, and `0` otherwise (`DomMulAct.stabilizer_card`); hence ★★
  `card_fibre_mul_prod_factorial` — **the number of configurations with occupation numbers `P`
  times `∏ P_k!` is `n!`**;
* `bosonFirst hL` — the **first-quantisation map** `FieldSpace K L → ManyParticle n K` for `n < L`:
  `√(∏ P_k!/n!)` times the Fock amplitude on the occupation numbers; it lands in the boson sector
  (`bosonFirst_mem`) and ★★★ `inner_bosonFirst_of_mem` — **is an isometry on the `n`-quantum
  sector**;
* ★★ `bosonFirst_bosonFockBasis` — **a Fock basis state is the normalised symmetrised product** of the
  basis orbitals of a configuration with its occupation numbers;
* `bCreate1 k` — first-quantised creation, `√(n+1)` times the symmetrised `e_k ⊗ ·`
  (`bCreate1_apply`: `(1/√(n+1)) ∑_p [c p = k] x (c ∘ p.succAbove)`); ★★★ `bosonFirst_bCreate` —
  **`Φ_{n+1} (b_k† y) = bCreate1 k (Φ_n y)`** below the cutoff;
* `bAnnihilate1 k` — `√(n+1) x (k, ·)`; ★★★ `bosonFirst_bAnnihilate` — **`Φ_n (b_k y) =
  bAnnihilate1 k (Φ_{n+1} y)`** below the cutoff;
* ★★★ `boson_dictionary` — the capstone.

## Honest scope

⚠️ **Below the cutoff.** Every statement needs `n + 1 < L` (or `n < L`): the truncated ladder
operators agree with the first-quantised ones only where the truncation does not act.

⚠️ **One-body operators** `dΓ(h)` are BACKLOG #222.

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/BosonFock.lean`
(`bCreate`, `bAnnihilate`, `bosonFockSector`, `monoOccEquiv`); `SigmaLayer/FermionDictionary.lean`
(`consLin`, `splitPermEquiv`); `SigmaLayer/ManyIdenticalParticles.lean` (`nBosonSector`,
`symmetrizer`); `CV/Oscillator.lean` (`creation`, `annihilation`); Mathlib
`DomMulAct.stabilizer_card`, `Equiv.Perm.ofFn_comp_perm`; `specs/BACKLOG.md` #221.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

open CSD.CV

variable {n K L : ℕ}

/-! ### Occupation numbers of a configuration -/

/-- **The occupation numbers** of a configuration: how many particles sit in each mode. -/
def occNat (c : ManyConfig n K) (m : Fin K) : ℕ := (List.ofFn c).count m

theorem occNat_eq_card (c : ManyConfig n K) (m : Fin K) :
    occNat c m = (Finset.univ.filter (c · = m)).card := by
  rw [Finset.card_filter]
  induction n with
  | zero => simp [occNat]
  | succ n ih =>
    rw [occNat, List.ofFn_succ, List.count_cons, Fin.sum_univ_succ]
    have := ih (fun i => c i.succ)
    rw [occNat] at this
    rw [this]
    by_cases h : c 0 = m <;> simp [h, add_comm]

theorem occNat_le (c : ManyConfig n K) (m : Fin K) : occNat c m ≤ n := by
  rw [occNat]
  exact (List.count_le_length).trans (by rw [List.length_ofFn])

theorem sum_occNat (c : ManyConfig n K) : ∑ m, occNat c m = n := by
  have := Multiset.sum_count_eq_card (s := Finset.univ)
    (m := (List.ofFn c : Multiset (Fin K))) (fun a _ => Finset.mem_univ a)
  simpa [occNat] using this

theorem occNat_comp_perm (c : ManyConfig n K) (σ : Equiv.Perm (Fin n)) :
    occNat (c ∘ σ) = occNat c :=
  funext fun m => (σ.ofFn_comp_perm c).count_eq m

theorem occNat_cons (k : Fin K) (c : ManyConfig n K) (m : Fin K) :
    occNat (Fin.cons k c : Fin (n + 1) → Fin K) m = occNat c m + if k = m then 1 else 0 := by
  rw [occNat, List.ofFn_succ, List.count_cons]
  simp [occNat]

theorem occNat_succAbove (c : Fin (n + 1) → Fin K) (p : Fin (n + 1)) (m : Fin K) :
    occNat c m = occNat (c ∘ p.succAbove) m + if c p = m then 1 else 0 := by
  have h := occNat_comp_perm c p.cycleRange.symm
  rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm] at h
  rw [← h, occNat_cons]
  rfl

/-- Monotone configurations with the same occupation numbers are equal. -/
theorem monotone_eq_of_occNat_eq {m m' : ManyConfig n K} (hm : Monotone m) (hm' : Monotone m')
    (h : occNat m = occNat m') : m = m' := by
  have hperm : List.Perm (List.ofFn m) (List.ofFn m') :=
    List.perm_iff_count.2 fun a => congrFun h a
  exact List.ofFn_injective (hperm.eq_of_sortedLE hm.sortedLE_ofFn hm'.sortedLE_ofFn)

/-- Configurations with the same occupation numbers differ by a permutation. -/
theorem exists_perm_of_occNat_eq {c m : ManyConfig n K} (h : occNat c = occNat m) :
    ∃ τ : Equiv.Perm (Fin n), c = m ∘ τ := by
  have hs : c ∘ Tuple.sort c = m ∘ Tuple.sort m :=
    monotone_eq_of_occNat_eq (Tuple.monotone_sort c) (Tuple.monotone_sort m)
      (by rw [occNat_comp_perm, occNat_comp_perm, h])
  refine ⟨Tuple.sort m * (Tuple.sort c)⁻¹, funext fun i => ?_⟩
  have := congrFun hs ((Tuple.sort c)⁻¹ i)
  simpa [Equiv.Perm.mul_apply] using this

/-! ### The coset count -/

/-- **The coset count**: the permutations carrying `m` to `c` number `∏_k P_k!` when the two
configurations have the same occupation numbers `P`, and none otherwise. -/
theorem card_comp_eq (m c : ManyConfig n K) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => m ∘ σ = c).card
      = if occNat c = occNat m then ∏ k, (occNat m k).factorial else 0 := by
  classical
  split_ifs with h
  · obtain ⟨τ, rfl⟩ := exists_perm_of_occNat_eq h
    have hstab : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => m ∘ σ = m).card
        = ∏ k, (occNat m k).factorial := by
      rw [← Fintype.card_subtype, DomMulAct.stabilizer_card]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [occNat_eq_card, Fintype.card_subtype]
    rw [← hstab]
    refine Finset.card_equiv (Equiv.mulRight τ⁻¹) fun σ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    constructor
    · intro hσ
      funext i
      have := congrFun hσ (τ⁻¹ i)
      simpa [Equiv.Perm.mul_apply] using this
    · intro hσ
      funext i
      have := congrFun hσ (τ i)
      simpa [Equiv.Perm.mul_apply] using this
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro σ _ rfl
    exact h (occNat_comp_perm m σ)

/-- **The fibre count**: the configurations with the occupation numbers `P` of `m`, times `∏ P_k!`,
are `n!`. -/
theorem card_fibre_mul_prod_factorial (m : ManyConfig n K) :
    (Finset.univ.filter fun c : ManyConfig n K => occNat c = occNat m).card
      * ∏ k, (occNat m k).factorial = n.factorial := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
    (t := Finset.univ.filter fun c : ManyConfig n K => occNat c = occNat m)
    (f := fun σ : Equiv.Perm (Fin n) => m ∘ σ)
    (fun σ _ => by simp [occNat_comp_perm])
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, Finset.sum_congr rfl fun c hc => by
    rw [card_comp_eq, ite_eq_left (Finset.mem_filter.1 hc).2], Finset.sum_const, smul_eq_mul]

/-! ### The first-quantisation map -/

/-- The occupation configuration of `c` on the truncated lattice, for `n < L`. -/
def occOf (hL : n < L) (c : ManyConfig n K) : FieldConfig K L :=
  fun m => ⟨occNat c m, (occNat_le c m).trans_lt hL⟩

theorem occOf_comp_perm (hL : n < L) (c : ManyConfig n K) (σ : Equiv.Perm (Fin n)) :
    occOf hL (c ∘ σ) = occOf hL c := by
  funext m
  simp [occOf, occNat_comp_perm]

theorem bOccTotal_occOf (hL : n < L) (c : ManyConfig n K) : bOccTotal (occOf hL c) = n := by
  simp [bOccTotal, occOf, sum_occNat]

/-- `√(∏ P_k!/n!)`, the boson weight of the occupation numbers `P`. -/
noncomputable def occWeight (n : ℕ) (P : Fin K → ℕ) : ℝ :=
  Real.sqrt ((∏ k, (P k).factorial : ℕ) / n.factorial)

theorem occWeight_nonneg (n : ℕ) (P : Fin K → ℕ) : 0 ≤ occWeight n P := Real.sqrt_nonneg _

theorem occWeight_sq (n : ℕ) (P : Fin K → ℕ) :
    occWeight n P ^ 2 = (∏ k, (P k).factorial : ℕ) / n.factorial :=
  Real.sq_sqrt (by positivity)

/-- **The first-quantisation map** for bosons: `√(∏ P_k!/n!)` times the Fock amplitude on the
occupation numbers. -/
noncomputable def bosonFirst (hL : n < L) : FieldSpace K L →ₗ[ℂ] ManyParticle n K where
  toFun y := WithLp.toLp 2 fun c => (occWeight n (occNat c) : ℂ) * y (occOf hL c)
  map_add' y y' := by ext c; simp [mul_add]
  map_smul' a y := by ext c; simp [mul_left_comm]

theorem bosonFirst_apply (hL : n < L) (y : FieldSpace K L) (c : ManyConfig n K) :
    bosonFirst hL y c = (occWeight n (occNat c) : ℂ) * y (occOf hL c) := rfl

theorem bosonFirst_mem (hL : n < L) (y : FieldSpace K L) :
    bosonFirst hL y ∈ nBosonSector n K :=
  mem_nBosonSector_iff_apply.2 fun σ c => by
    rw [bosonFirst_apply, bosonFirst_apply, occNat_comp_perm, occOf_comp_perm]

/-- **The inner product of first-quantised states** is the inner product of the Fock amplitudes on
the `n`-quantum configurations. -/
theorem inner_bosonFirst (hL : n < L) (y y' : FieldSpace K L) :
    ⟪bosonFirst hL y, bosonFirst hL y'⟫_ℂ
      = ∑ d : BosonOcc K L n, y' d.1 * (starRingEnd ℂ) (y d.1) := by
  classical
  let H : MonoConfig n K → ℂ := fun m => y' (occOf hL m.1) * (starRingEnd ℂ) (y (occOf hL m.1))
  let sortOf : ManyConfig n K → MonoConfig n K := fun c => ⟨c ∘ Tuple.sort c, Tuple.monotone_sort c⟩
  have hsortOcc : ∀ c, occNat (sortOf c).1 = occNat c := fun c => occNat_comp_perm c _
  have hterm : ∀ c, bosonFirst hL y' c * (starRingEnd ℂ) (bosonFirst hL y c)
      = ((occWeight n (occNat c) ^ 2 : ℝ) : ℂ) * H (sortOf c) := fun c => by
    have hocc : occOf hL (sortOf c).1 = occOf hL c := occOf_comp_perm hL c _
    simp only [bosonFirst_apply, H, hocc, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, hterm]
  rw [← Finset.sum_fiberwise Finset.univ sortOf]
  have hfib : ∀ m : MonoConfig n K, ∑ c ∈ Finset.univ.filter (fun c => sortOf c = m),
      ((occWeight n (occNat c) ^ 2 : ℝ) : ℂ) * H (sortOf c) = H m := fun m => by
    have hset : Finset.univ.filter (fun c => sortOf c = m)
        = Finset.univ.filter (fun c : ManyConfig n K => occNat c = occNat m.1) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro rfl
        exact (hsortOcc c).symm
      · intro h
        exact Subtype.ext (monotone_eq_of_occNat_eq (Tuple.monotone_sort c) m.2
          (by rw [hsortOcc, h]))
    rw [hset, Finset.sum_congr rfl fun c hc => by
      rw [show sortOf c = m from Subtype.ext (monotone_eq_of_occNat_eq (Tuple.monotone_sort c) m.2
        (by rw [hsortOcc, (Finset.mem_filter.1 hc).2])), (Finset.mem_filter.1 hc).2],
      Finset.sum_const, nsmul_eq_mul, occWeight_sq]
    have hcount := card_fibre_mul_prod_factorial m.1
    have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hR : ((Finset.univ.filter fun c : ManyConfig n K => occNat c = occNat m.1).card : ℝ)
        * ((∏ k, (occNat m.1 k).factorial : ℕ) / n.factorial : ℝ) = 1 := by
      rw [← mul_div_assoc, div_eq_one_iff_eq hfact]
      exact_mod_cast hcount
    have hC : ((Finset.univ.filter fun c : ManyConfig n K => occNat c = occNat m.1).card : ℂ)
        * (((∏ k, (occNat m.1 k).factorial : ℕ) / n.factorial : ℝ) : ℂ) = 1 := by
      exact_mod_cast hR
    rw [← mul_assoc, hC, one_mul]
  rw [Finset.sum_congr rfl fun m _ => hfib m]
  exact Fintype.sum_equiv (monoOccEquiv hL) _ _ fun m => rfl

/-- **The first-quantisation map is an isometry on the `n`-quantum sector.** -/
theorem inner_bosonFirst_of_mem (hL : n < L) {y : FieldSpace K L} (hy : y ∈ bosonFockSector K L n)
    (y' : FieldSpace K L) :
    ⟪bosonFirst hL y, bosonFirst hL y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
  classical
  rw [inner_bosonFirst, PiLp.inner_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun d : FieldConfig K L => bOccTotal d = n)]
  rw [Fintype.sum_eq_zero (fun d : {d : FieldConfig K L // ¬ bOccTotal d = n} =>
      ⟪y d.1, y' d.1⟫_ℂ) (fun d => by rw [hy d.1 d.2, inner_zero_left]), add_zero]
  exact Finset.sum_congr rfl fun d _ => by rw [RCLike.inner_apply]

/-! ### Fock basis states -/

/-- The bosonic Fock basis state with occupation numbers `d`. -/
noncomputable def bosonFockBasis (d : FieldConfig K L) : FieldSpace K L :=
  WithLp.toLp 2 (Pi.single d 1)

theorem prodState_basisOrbital_apply (m c : ManyConfig n K) :
    prodState (fun i => basisOrbital (m i)) c = if c = m then 1 else 0 := by
  simp only [prodState, PiLp.toLp_apply, basisOrbital, Pi.single_apply]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- **A Fock basis state is the normalised symmetrised product** of the basis orbitals of any
configuration `m` with its occupation numbers. -/
theorem bosonFirst_bosonFockBasis (hL : n < L) (m : ManyConfig n K) :
    bosonFirst hL (bosonFockBasis (occOf hL m))
      = ((Real.sqrt (n.factorial / (∏ k, (occNat m k).factorial : ℕ)) : ℝ) : ℂ)
        • symmetrizer n K (prodState fun i => basisOrbital (m i)) := by
  classical
  ext c
  rw [bosonFirst_apply, PiLp.smul_apply, symmetrizer_apply, PiLp.smul_apply, WithLp.ofLp_sum,
    Finset.sum_apply]
  simp only [permOp_apply, prodState_basisOrbital_apply, smul_eq_mul]
  have hcount : ∑ σ : Equiv.Perm (Fin n), (if c ∘ σ = m then (1 : ℂ) else 0)
      = if occNat c = occNat m then ((∏ k, (occNat m k).factorial : ℕ) : ℂ) else 0 := by
    rw [Finset.sum_boole]
    have h := card_comp_eq c m
    have hcard : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => c ∘ σ = m).card
        = if occNat c = occNat m then ∏ k, (occNat m k).factorial else 0 := by
      rw [h]
      by_cases hcm : occNat c = occNat m
      · rw [ite_eq_left hcm.symm, ite_eq_left hcm, hcm]
      · rw [ite_eq_right (Ne.symm hcm), ite_eq_right hcm]
    rw [hcard]
    split_ifs <;> simp
  rw [hcount]
  simp only [bosonFockBasis, PiLp.toLp_apply, Pi.single_apply]
  by_cases hcm : occNat c = occNat m
  · have hocc : occOf hL c = occOf hL m := by
      funext k
      simp [occOf, hcm]
    rw [ite_eq_left hocc, ite_eq_left hcm, mul_one, hcm]
    have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hprod : (0 : ℝ) < (∏ k, (occNat m k).factorial : ℕ) := by
      exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
    have hR : occWeight n (occNat m) = Real.sqrt (n.factorial / (∏ k, (occNat m k).factorial : ℕ))
        * ((n.factorial : ℝ)⁻¹ * (∏ k, (occNat m k).factorial : ℕ)) := by
      unfold occWeight
      rw [Real.sqrt_div' _ hprod.le, Real.sqrt_div' _ hfact.le]
      have h1 := Real.mul_self_sqrt hfact.le
      have h2 := Real.mul_self_sqrt hprod.le
      have hs1 : 0 < Real.sqrt n.factorial := Real.sqrt_pos.2 hfact
      have hs2 : 0 < Real.sqrt (∏ k, (occNat m k).factorial : ℕ) := Real.sqrt_pos.2 hprod
      field_simp
      rw [Real.sq_sqrt hprod.le, Real.sq_sqrt hfact.le]
      ring
    rw [hR]
    push_cast
    ring
  · have hocc : occOf hL c ≠ occOf hL m := fun h => hcm (funext fun k => by
      have := congrArg (fun d : FieldConfig K L => (d k : ℕ)) h
      simpa [occOf] using this)
    rw [ite_eq_right hocc, ite_eq_right hcm]
    ring

/-! ### Creation -/

/-- **First-quantised creation** of a boson in mode `k`: `√(n+1)` times the symmetrised
`e_k ⊗ ·`. -/
noncomputable def bCreate1 (k : Fin K) : ManyParticle n K →ₗ[ℂ] ManyParticle (n + 1) K :=
  ((Real.sqrt (n + 1) : ℝ) : ℂ) • (symmetrizer (n + 1) K ∘ₗ consLin k)

/-- **The explicit form of first-quantised creation** on a boson:
`(1/√(n+1)) ∑_p [c p = k] x (c ∘ p.succAbove)`. -/
theorem bCreate1_apply (k : Fin K) {x : ManyParticle n K} (hx : x ∈ nBosonSector n K)
    (c : ManyConfig (n + 1) K) :
    bCreate1 k x c = ((Real.sqrt (n + 1))⁻¹ : ℝ)
      * ∑ p : Fin (n + 1), (if c p = k then x (c ∘ p.succAbove) else 0) := by
  have hterm : ∀ (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)),
      (consLin k x) (c ∘ splitPerm p e) = (if c p = k then x (c ∘ p.succAbove) else 0) :=
    fun p e => by
    have htail : Fin.tail (c ∘ splitPerm p e) = (c ∘ p.succAbove) ∘ e := by
      funext i
      simp [Fin.tail, splitPerm_succ]
    show (if (c ∘ splitPerm p e) 0 = k then x (Fin.tail (c ∘ splitPerm p e)) else 0) = _
    rw [htail, Function.comp_apply, splitPerm_zero, mem_nBosonSector_iff_apply.1 hx]
  simp only [bCreate1, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    PiLp.smul_apply, smul_eq_mul, symmetrizer_apply, WithLp.ofLp_sum, Finset.sum_apply,
    permOp_apply]
  rw [← (splitPermEquiv n).sum_comp, Fintype.sum_prod_type]
  simp only [splitPermEquiv, Equiv.ofBijective_apply, hterm, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Nat.factorial_succ]
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hsq : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 := Real.mul_self_sqrt hpos.le
  have hne : ((Real.sqrt (n + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hfact : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsqC : ((Real.sqrt (n + 1) : ℝ) : ℂ) * ((Real.sqrt (n + 1) : ℝ) : ℂ) = (n : ℂ) + 1 := by
    exact_mod_cast hsq
  push_cast
  field_simp
  linear_combination (∑ p : Fin (n + 1), (if c p = k then x (c ∘ p.succAbove) else 0)) * hsqC

theorem bCreate1_mem (k : Fin K) (x : ManyParticle n K) :
    bCreate1 k x ∈ nBosonSector (n + 1) K := by
  simp only [bCreate1, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply]
  exact Submodule.smul_mem _ _ (isProj_symmetrizer.map_mem _)

/-- The second-quantised creation operator on a configuration with a quantum in mode `k`. -/
theorem bCreate_apply_of_pos (k : Fin K) (y : FieldSpace K L) (d : FieldConfig K L)
    (hd : 0 < (d k : ℕ)) :
    bCreate k y d = ((Real.sqrt (d k : ℕ) : ℝ) : ℂ)
      * y (Function.update d k ⟨(d k : ℕ) - 1, by omega⟩) := by
  rw [bCreate, modeOp_apply, Finset.sum_eq_single ⟨(d k : ℕ) - 1, by omega⟩]
  · rw [creation_apply, ite_eq_left (by simp only; omega)]
  · intro m _ hm
    rw [creation_apply, ite_eq_right, zero_mul]
    intro h
    exact hm (Fin.ext (by simp only; omega))
  · exact fun h => absurd (Finset.mem_univ _) h

theorem bCreate_apply_of_eq_zero (k : Fin K) (y : FieldSpace K L) (d : FieldConfig K L)
    (hd : (d k : ℕ) = 0) : bCreate k y d = 0 := by
  rw [bCreate, modeOp_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [creation_apply, ite_eq_right (by omega), zero_mul]

/-- **Creation in the two pictures**: `Φ_{n+1} (b_k† y) = bCreate1 k (Φ_n y)` below the cutoff. -/
theorem bosonFirst_bCreate (hL : n + 1 < L) (k : Fin K) (y : FieldSpace K L) :
    bosonFirst hL (bCreate k y) = bCreate1 k (bosonFirst (Nat.lt_of_succ_lt hL) y) := by
  ext c
  rw [bosonFirst_apply, bCreate1_apply k (bosonFirst_mem _ y)]
  set P := occNat c with hP
  by_cases hk : P k = 0
  · rw [bCreate_apply_of_eq_zero k y _ (by simp [occOf, ← hP, hk]), mul_zero,
      Finset.sum_eq_zero, mul_zero]
    intro p _
    rw [ite_eq_right]
    intro hp
    have := occNat_succAbove c p k
    rw [← hP, hk, ite_eq_left hp] at this
    omega
  · have hpos : 0 < P k := Nat.pos_of_ne_zero hk
    rw [bCreate_apply_of_pos k y _ (by simpa [occOf, ← hP] using hpos)]
    -- every `p` with `c p = k` contributes the same term
    have hrem : ∀ p, c p = k → occNat (c ∘ p.succAbove) = Function.update P k (P k - 1) :=
      fun p hp => funext fun m => by
        have := occNat_succAbove c p m
        by_cases hm : m = k
        · subst hm
          rw [Function.update_self]
          rw [← hP, ite_eq_left hp] at this
          omega
        · rw [Function.update_of_ne hm]
          rw [← hP, ite_eq_right (fun h => hm (h.symm.trans hp)), add_zero] at this
          exact this.symm
    have hupd : ∀ p, c p = k → occOf (Nat.lt_of_succ_lt hL) (c ∘ p.succAbove)
        = Function.update (occOf hL c) k ⟨((occOf hL c) k : ℕ) - 1, by
          have := ((occOf hL c) k).isLt; omega⟩ := fun p hp => by
      funext m
      apply Fin.ext
      by_cases hm : m = k
      · subst hm
        simp [occOf, hrem p hp, ← hP]
      · simp [occOf, hrem p hp, Function.update_of_ne hm, ← hP]
    have hsum : ∑ p : Fin (n + 1), (if c p = k then bosonFirst (Nat.lt_of_succ_lt hL) y
          (c ∘ p.succAbove) else 0)
        = (P k : ℂ) * ((occWeight n (Function.update P k (P k - 1)) : ℝ) : ℂ)
          * y (Function.update (occOf hL c) k ⟨((occOf hL c) k : ℕ) - 1, by
              have := ((occOf hL c) k).isLt; omega⟩) := by
      rw [Finset.sum_congr rfl fun p _ => show (if c p = k then bosonFirst (Nat.lt_of_succ_lt hL) y
          (c ∘ p.succAbove) else 0) = if c p = k then ((occWeight n (Function.update P k (P k - 1))
            : ℝ) : ℂ) * y (Function.update (occOf hL c) k ⟨((occOf hL c) k : ℕ) - 1, by
              have := ((occOf hL c) k).isLt; omega⟩) else 0 from by
        split_ifs with hp
        · rw [bosonFirst_apply, hrem p hp, hupd p hp]
        · rfl]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hP, occNat_eq_card c k]
      ring
    rw [hsum]
    -- the arithmetic of the weights
    have hprod : (∏ m, (P m).factorial : ℕ)
        = P k * ∏ m, (Function.update P k (P k - 1) m).factorial := by
      have hrest : ∏ m ∈ Finset.univ.erase k, (Function.update P k (P k - 1) m).factorial
          = ∏ m ∈ Finset.univ.erase k, (P m).factorial :=
        Finset.prod_congr rfl fun m hm => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ (fun m => (Function.update P k (P k - 1) m).factorial)
          (Finset.mem_univ k), Function.update_self, hrest, ← mul_assoc,
        Nat.mul_factorial_pred hk]
    have hocck : ((occOf hL c) k : ℕ) = P k := by simp [occOf, ← hP]
    have hw : occWeight (n + 1) P * Real.sqrt (P k)
        = (Real.sqrt (n + 1))⁻¹ * (P k * occWeight n (Function.update P k (P k - 1))) := by
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hA : (0 : ℝ) ≤ (∏ m, (Function.update P k (P k - 1) m).factorial : ℕ) := by positivity
      unfold occWeight
      rw [hprod, Nat.factorial_succ]
      push_cast
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      rw [show ((P k : ℝ) * (∏ m, ((Function.update P k (P k - 1) m).factorial : ℝ)))
          / ((n + 1) * n.factorial)
          = (P k : ℝ) ^ 2 * ((∏ m, ((Function.update P k (P k - 1) m).factorial : ℝ))
            / n.factorial) / ((n + 1) * P k) by
        have : (P k : ℝ) ≠ 0 := by exact_mod_cast hk
        field_simp]
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have hsk : 0 < Real.sqrt (P k) := Real.sqrt_pos.2 (by exact_mod_cast hpos)
      have hsn : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 hn1
      field_simp
    have hwC : ((occWeight (n + 1) P : ℝ) : ℂ) * ((Real.sqrt (P k) : ℝ) : ℂ)
        = (((Real.sqrt (n + 1))⁻¹ : ℝ) : ℂ) * ((P k : ℂ) * ((occWeight n
          (Function.update P k (P k - 1)) : ℝ) : ℂ)) := by
      exact_mod_cast hw
    simp only [hocck]
    rw [← mul_assoc, hwC]
    push_cast
    ring

/-! ### Annihilation -/

/-- **First-quantised annihilation** of a boson in mode `k`: `√(n+1) x (k, ·)`. -/
noncomputable def bAnnihilate1 (k : Fin K) : ManyParticle (n + 1) K →ₗ[ℂ] ManyParticle n K where
  toFun x := WithLp.toLp 2 fun c => ((Real.sqrt (n + 1) : ℝ) : ℂ) * x (Fin.cons k c)
  map_add' x y := by ext c; simp [mul_add]
  map_smul' a x := by ext c; simp [mul_left_comm]

theorem bAnnihilate1_apply (k : Fin K) (x : ManyParticle (n + 1) K) (c : ManyConfig n K) :
    bAnnihilate1 k x c = ((Real.sqrt (n + 1) : ℝ) : ℂ) * x (Fin.cons k c) := rfl

/-- The second-quantised annihilation operator below the top level of mode `k`. -/
theorem bAnnihilate_apply_of_lt (k : Fin K) (y : FieldSpace K L) (d : FieldConfig K L)
    (hd : (d k : ℕ) + 1 < L) :
    bAnnihilate k y d = ((Real.sqrt ((d k : ℕ) + 1 : ℕ) : ℝ) : ℂ)
      * y (Function.update d k ⟨(d k : ℕ) + 1, hd⟩) := by
  rw [bAnnihilate, modeOp_apply, Finset.sum_eq_single ⟨(d k : ℕ) + 1, hd⟩]
  · rw [annihilation_apply, ite_eq_left rfl]
  · intro m _ hm
    rw [annihilation_apply, ite_eq_right, zero_mul]
    intro h
    exact hm (Fin.ext (by simp only; omega))
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **Annihilation in the two pictures**: `Φ_n (b_k y) = bAnnihilate1 k (Φ_{n+1} y)` below the
cutoff. -/
theorem bosonFirst_bAnnihilate (hL : n + 1 < L) (k : Fin K) (y : FieldSpace K L) :
    bosonFirst (Nat.lt_of_succ_lt hL) (bAnnihilate k y) = bAnnihilate1 k (bosonFirst hL y) := by
  ext c
  set P := occNat c with hP
  have hlt : ((occOf (Nat.lt_of_succ_lt hL) c) k : ℕ) + 1 < L := by
    have := occNat_le c k
    simp only [occOf]
    omega
  rw [bosonFirst_apply, bAnnihilate_apply_of_lt k y _ hlt, bAnnihilate1_apply, bosonFirst_apply]
  have hcons : occNat (Fin.cons k c : Fin (n + 1) → Fin K) = Function.update P k (P k + 1) :=
    funext fun m => by
      rw [occNat_cons]
      by_cases hm : m = k
      · subst hm
        simp [← hP]
      · simp [Function.update_of_ne hm, Ne.symm hm, ← hP]
  have hocc : occOf hL (Fin.cons k c : Fin (n + 1) → Fin K)
      = Function.update (occOf (Nat.lt_of_succ_lt hL) c) k
        ⟨((occOf (Nat.lt_of_succ_lt hL) c) k : ℕ) + 1, hlt⟩ := by
    funext m
    apply Fin.ext
    by_cases hm : m = k
    · subst hm
      simp [occOf, hcons, ← hP]
    · simp [occOf, hcons, Function.update_of_ne hm, ← hP]
  rw [hocc, hcons]
  have hocck : ((occOf (Nat.lt_of_succ_lt hL) c) k : ℕ) = P k := by simp [occOf, ← hP]
  simp only [hocck]
  have hprod : (∏ m, (Function.update P k (P k + 1) m).factorial : ℕ)
      = (P k + 1) * ∏ m, (P m).factorial := by
    have hrest : ∏ m ∈ Finset.univ.erase k, (Function.update P k (P k + 1) m).factorial
        = ∏ m ∈ Finset.univ.erase k, (P m).factorial :=
      Finset.prod_congr rfl fun m hm => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ (fun m => (P m).factorial) (Finset.mem_univ k),
      Function.update_self, Nat.factorial_succ, hrest]
    ring
  have hw : occWeight n P * Real.sqrt ((P k + 1 : ℕ) : ℝ)
      = Real.sqrt (n + 1) * occWeight (n + 1) (Function.update P k (P k + 1)) := by
    unfold occWeight
    rw [hprod, Nat.factorial_succ]
    push_cast
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hn1.le]
    congr 1
    field_simp
  have hwC : ((occWeight n P : ℝ) : ℂ) * ((Real.sqrt ((P k + 1 : ℕ) : ℝ) : ℝ) : ℂ)
      = ((Real.sqrt (n + 1) : ℝ) : ℂ)
        * ((occWeight (n + 1) (Function.update P k (P k + 1)) : ℝ) : ℂ) := by
    exact_mod_cast hw
  rw [← mul_assoc, hwC, mul_assoc]

/-! ### The capstone -/

/-- **First and second quantisation as operators, for bosons**, below the cutoff.

1. the first-quantisation map is an isometry on the `n`-quantum sector;
2. it sends each Fock basis state to the normalised symmetrised product of basis orbitals;
3. it carries `b_k†` to `√(n+1)` times symmetrised tensoring with `e_k`;
4. it carries `b_k` to `√(n+1)` times evaluation with a particle in mode `k`;
5. the configurations with given occupation numbers `P` number `n!/∏ P_k!`. -/
theorem boson_dictionary (hL : n + 1 < L) :
    (∀ y y' : FieldSpace K L, y ∈ bosonFockSector K L n →
        ⟪bosonFirst (Nat.lt_of_succ_lt hL) y, bosonFirst (Nat.lt_of_succ_lt hL) y'⟫_ℂ = ⟪y, y'⟫_ℂ)
    ∧ (∀ m : ManyConfig n K, bosonFirst (Nat.lt_of_succ_lt hL)
          (bosonFockBasis (occOf (Nat.lt_of_succ_lt hL) m))
        = ((Real.sqrt (n.factorial / (∏ k, (occNat m k).factorial : ℕ)) : ℝ) : ℂ)
          • symmetrizer n K (prodState fun i => basisOrbital (m i)))
    ∧ (∀ (k : Fin K) (y : FieldSpace K L),
        bosonFirst hL (bCreate k y) = bCreate1 k (bosonFirst (Nat.lt_of_succ_lt hL) y))
    ∧ (∀ (k : Fin K) (y : FieldSpace K L),
        bosonFirst (Nat.lt_of_succ_lt hL) (bAnnihilate k y) = bAnnihilate1 k (bosonFirst hL y))
    ∧ ∀ m : ManyConfig n K,
        (Finset.univ.filter fun c : ManyConfig n K => occNat c = occNat m).card
          * ∏ k, (occNat m k).factorial = n.factorial :=
  ⟨fun _ y' hy => inner_bosonFirst_of_mem _ hy y', bosonFirst_bosonFockBasis _,
    bosonFirst_bCreate hL, bosonFirst_bAnnihilate hL, card_fibre_mul_prod_factorial⟩

end CSD.SigmaLayer
