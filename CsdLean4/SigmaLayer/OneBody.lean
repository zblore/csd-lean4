/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.BosonDictionary

/-!
# SigmaLayer/OneBody: one-body operators in the two pictures

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #222, after ~~#220~~ (`SigmaLayer/FermionDictionary.lean`) and ~~#221~~
(`SigmaLayer/BosonDictionary.lean`).

A one-particle operator `h` acts on `n` identical particles as `∑_k h^{(k)}`, the same `h` on every
particle (`oneBody h`). In second quantisation it is `dΓ(h) = ∑_{ij} h_ij a_i† a_j` (`dGammaF`,
`dGammaB`). This module proves the two are the same operator under the first-quantisation maps of
~~#220~~ and ~~#221~~.

## What is proved

* `oneBody h` — `(∑_k h^{(k)} x)(c) = ∑_k ∑_m h (c k) m · x (c[k ↦ m])`;
* ★★ `sum_fCreate1_fAnnihilate1` / ★★ `sum_bCreate1_bAnnihilate1` — **the first-quantised
  identity** `∑_{ij} h_ij · Create1_i (Annihilate1_j x) = ∑_k h^{(k)} x` on antisymmetric and on
  symmetric `x` (for fermions the slot signs `(−1)^p` cancel in pairs);
* ★★★ `fermionFirst_dGammaF` — **`Φ_n (dΓ(h) y) = (∑_k h^{(k)}) (Φ_n y)` for fermions**, every `n`;
* ★★★ `bosonFirst_dGammaB` — **the same for bosons**, below the cutoff;
* `dGammaF_one`, `dGammaB_one` — `dΓ(1)` is the total number operator; ★★
  `toEuclideanLin_fieldHamiltonian` — **the CV track's free-field Hamiltonian is `dΓ(1) + K/2`**: the
  diagonal case, with its zero-point energy;
* ★★★ `one_body` — the capstone.

## Honest scope

⚠️ **One-body only.** Two-body interactions `½ ∑ V_ijkl a_i† a_j† a_l a_k` are not treated; they are
BACKLOG #223.

⚠️ **Bosons below the cutoff** (`n < L`), as in ~~#221~~.

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/FermionDictionary.lean`
(`fermionFirst_fCreate`, `fermionFirst_fAnnihilate`, `fCreate1_apply`); `SigmaLayer/BosonDictionary.lean`
(`bosonFirst_bCreate`, `bosonFirst_bAnnihilate`, `bCreate1_apply`); `CV/FieldModes.lean`
(`fieldHamiltonian`); Mathlib `Fin.cons_removeNth_eq_comp_cycleRange_symm`; `specs/BACKLOG.md` #222.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

open CSD.CV

variable {n N K L : ℕ}

/-! ### One-body operators in first quantisation -/

/-- **A one-particle matrix acting on every particle**, `∑_k h^{(k)}`. -/
noncomputable def oneBody (h : Matrix (Fin N) (Fin N) ℂ) : ManyParticle n N →ₗ[ℂ] ManyParticle n N where
  toFun x := WithLp.toLp 2 fun c => ∑ k, ∑ m, h (c k) m * x (Function.update c k m)
  map_add' x y := by
    ext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext c
    simp [Finset.mul_sum, mul_left_comm]

theorem oneBody_apply (h : Matrix (Fin N) (Fin N) ℂ) (x : ManyParticle n N) (c : ManyConfig n N) :
    oneBody h x c = ∑ k, ∑ m, h (c k) m * x (Function.update c k m) := rfl

/-- Re-inserting a particle in slot `p` is updating slot `p` and then rotating it to the front. -/
theorem cons_comp_succAbove_eq (c : Fin (n + 1) → Fin N) (p : Fin (n + 1)) (j : Fin N) :
    (Fin.cons j (c ∘ p.succAbove) : Fin (n + 1) → Fin N)
      = Function.update c p j ∘ p.cycleRange.symm := by
  rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm, Function.update_self]
  congr 1
  funext i
  simp [Fin.removeNth]

/-- Regrouping `∑_{ij} ∑_p [c p = i] h_ij X_pj` as `∑_p ∑_j h_{(c p) j} X_pj`. -/
theorem sum_sum_sum_ite (h : Matrix (Fin N) (Fin N) ℂ) (c : Fin (n + 1) → Fin N)
    (X : Fin (n + 1) → Fin N → ℂ) :
    ∑ i, ∑ j, ∑ p, (if c p = i then h i j * X p j else 0) = ∑ p, ∑ j, h (c p) j * X p j := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans Finset.sum_comm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

/-- **The first-quantised identity for fermions**:
`∑_{ij} h_ij · fCreate1 i (fAnnihilate1 j x) = ∑_k h^{(k)} x` on antisymmetric `x`. -/
theorem sum_fCreate1_fAnnihilate1 (h : Matrix (Fin N) (Fin N) ℂ) {x : ManyParticle (n + 1) N}
    (hx : x ∈ nFermionSector (n + 1) N) :
    ∑ i, ∑ j, h i j • fCreate1 i (fAnnihilate1 j x) = oneBody h x := by
  ext c
  have key : ∀ i j, h i j * fCreate1 i (fAnnihilate1 j x) c
      = ∑ p, (if c p = i then h i j * x (Function.update c p j) else 0) := fun i j => by
    rw [fCreate1_apply i (fAnnihilate1_mem j hx), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rw [fAnnihilate1_apply, cons_comp_succAbove_eq, mem_nFermionSector_iff_apply.1 hx,
        permSign_cycleRange_symm]
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have hs : (((Real.sqrt (n + 1))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (n + 1) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one]
      have hsign : ((-1 : ℂ) ^ (p : ℕ)) * (-1) ^ (p : ℕ) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      linear_combination (h i j * x (Function.update c p j)) * ((-1 : ℂ) ^ (p : ℕ) * (-1) ^ (p : ℕ)
        * hs + hsign)
    · simp
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, key, oneBody_apply]
  exact sum_sum_sum_ite h c fun p j => x (Function.update c p j)

/-- First-quantised boson annihilation keeps the boson sector. -/
theorem bAnnihilate1_mem (k : Fin K) {x : ManyParticle (n + 1) K}
    (hx : x ∈ nBosonSector (n + 1) K) : bAnnihilate1 k x ∈ nBosonSector n K := by
  refine mem_nBosonSector_iff_apply.2 fun σ c => ?_
  rw [bAnnihilate1_apply, bAnnihilate1_apply]
  have hcons : (Fin.cons k (c ∘ σ) : Fin (n + 1) → Fin K) = Fin.cons k c ∘ liftPerm σ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [liftPerm_zero]
    · simp [liftPerm_succ]
  rw [hcons, mem_nBosonSector_iff_apply.1 hx]

/-- **The first-quantised identity for bosons**:
`∑_{ij} h_ij · bCreate1 i (bAnnihilate1 j x) = ∑_k h^{(k)} x` on symmetric `x`. -/
theorem sum_bCreate1_bAnnihilate1 (h : Matrix (Fin K) (Fin K) ℂ) {x : ManyParticle (n + 1) K}
    (hx : x ∈ nBosonSector (n + 1) K) :
    ∑ i, ∑ j, h i j • bCreate1 i (bAnnihilate1 j x) = oneBody h x := by
  ext c
  have key : ∀ i j, h i j * bCreate1 i (bAnnihilate1 j x) c
      = ∑ p, (if c p = i then h i j * x (Function.update c p j) else 0) := fun i j => by
    rw [bCreate1_apply i (bAnnihilate1_mem j hx), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rw [bAnnihilate1_apply, cons_comp_succAbove_eq, mem_nBosonSector_iff_apply.1 hx]
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have hs : (((Real.sqrt (n + 1))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (n + 1) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one]
      linear_combination (h i j * x (Function.update c p j)) * hs
    · simp
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, key, oneBody_apply]
  exact sum_sum_sum_ite h c fun p j => x (Function.update c p j)

/-! ### One-body operators in second quantisation -/

/-- **`dΓ(h) = ∑_{ij} h_ij a_i† a_j`** on the fermionic Fock space. -/
noncomputable def dGammaF (h : Matrix (Fin N) (Fin N) ℂ) : Module.End ℂ (FieldSpace N 2) :=
  ∑ i, ∑ j, h i j • (fCreate i * fAnnihilate j)

/-- **`dΓ(h) = ∑_{ij} h_ij b_i† b_j`** on the bosonic Fock space. -/
noncomputable def dGammaB (h : Matrix (Fin K) (Fin K) ℂ) : Module.End ℂ (FieldSpace K L) :=
  ∑ i, ∑ j, h i j • (bCreate i * bAnnihilate j)

/-- `dΓ(1)` is the total number of fermions. -/
theorem dGammaF_one : dGammaF (1 : Matrix (Fin N) (Fin N) ℂ) = fTotalNumber N := by
  simp [dGammaF, Matrix.one_apply, ite_smul, fTotalNumber, fNumber]

/-- `dΓ(1)` is the total number of bosons. -/
theorem dGammaB_one : dGammaB (L := L) (1 : Matrix (Fin K) (Fin K) ℂ) = bTotalNumber K L := by
  simp [dGammaB, Matrix.one_apply, ite_smul, bTotalNumber, bNumber]

/-- **One-body operators in the two pictures, for fermions**: `Φ_n (dΓ(h) y) = (∑_k h^{(k)}) Φ_n y`. -/
theorem fermionFirst_dGammaF (h : Matrix (Fin N) (Fin N) ℂ) (y : FieldSpace N 2) :
    fermionFirst n N (dGammaF h y) = oneBody h (fermionFirst n N y) := by
  simp only [dGammaF, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum,
    map_smul]
  cases n with
  | zero =>
    have hzero : ∀ (i : Fin N) (w : FieldSpace N 2), fermionFirst 0 N (fCreate i w) = 0 :=
      fun i w => by
      ext c
      have hc : StrictMono c := fun a _ _ => Fin.elim0 a
      rw [fermionFirst_apply_strictMono _ ⟨c, hc⟩, PiLp.zero_apply, fCreate_apply]
      have : Finset.univ.image c = ∅ := by simp
      simp only
      rw [this]
      simp [occOfFinset_apply]
    simp only [hzero, smul_zero, Finset.sum_const_zero]
    ext c
    simp [oneBody_apply]
  | succ n =>
    have hij : ∀ i j, fermionFirst (n + 1) N (fCreate i (fAnnihilate j y))
        = fCreate1 i (fAnnihilate1 j (fermionFirst (n + 1) N y)) := fun i j => by
      rw [fermionFirst_fCreate, fermionFirst_fAnnihilate]
    simp only [hij]
    exact sum_fCreate1_fAnnihilate1 h (fermionFirst_mem y)

/-- **One-body operators in the two pictures, for bosons**, below the cutoff. -/
theorem bosonFirst_dGammaB (hL : n < L) (h : Matrix (Fin K) (Fin K) ℂ) (y : FieldSpace K L) :
    bosonFirst hL (dGammaB h y) = oneBody h (bosonFirst hL y) := by
  simp only [dGammaB, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum,
    map_smul]
  cases n with
  | zero =>
    have hzero : ∀ (i : Fin K) (w : FieldSpace K L), bosonFirst hL (bCreate i w) = 0 :=
      fun i w => by
      ext c
      rw [bosonFirst_apply, PiLp.zero_apply, bCreate_apply_of_eq_zero i w _ (by
        simp [occOf, occNat]), mul_zero]
    simp only [hzero, smul_zero, Finset.sum_const_zero]
    ext c
    simp [oneBody_apply]
  | succ n =>
    have hij : ∀ i j, bosonFirst hL (bCreate i (bAnnihilate j y))
        = bCreate1 i (bAnnihilate1 j (bosonFirst hL y)) := fun i j => by
      rw [bosonFirst_bCreate hL, bosonFirst_bAnnihilate hL]
    simp only [hij]
    exact sum_bCreate1_bAnnihilate1 h (bosonFirst_mem hL y)

/-- **The free-field Hamiltonian of the CV track is `dΓ(1) + K/2`**: the diagonal one-body operator,
with the zero-point energy `½` per mode. -/
theorem toEuclideanLin_fieldHamiltonian :
    Matrix.toEuclideanLin (fieldHamiltonian K L) = dGammaB 1 + ((K : ℂ) / 2) • 1 := by
  rw [dGammaB_one]
  apply LinearMap.ext
  intro y
  ext c
  rw [LinearMap.add_apply, PiLp.add_apply, bTotalNumber_apply, LinearMap.smul_apply,
    Module.End.one_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [fieldHamiltonian, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.toLp_apply,
    Matrix.mulVec_diagonal, fieldEnergy, oscEnergy, bOccTotal]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### The capstone -/

/-- **One-body operators in the two pictures.**

1. `∑_{ij} h_ij a_i† a_j` on the fermionic Fock space is `∑_k h^{(k)}` on every `n`-fermion sector;
2. `∑_{ij} h_ij b_i† b_j` on the bosonic Fock space is `∑_k h^{(k)}` on every `n`-boson sector
   below the cutoff;
3. `dΓ(1)` is the total number, for fermions and bosons;
4. the CV track's free-field Hamiltonian is `dΓ(1) + K/2`. -/
theorem one_body :
    (∀ (h : Matrix (Fin N) (Fin N) ℂ) (y : FieldSpace N 2),
        fermionFirst n N (dGammaF h y) = oneBody h (fermionFirst n N y))
    ∧ (∀ (hL : n < L) (h : Matrix (Fin K) (Fin K) ℂ) (y : FieldSpace K L),
        bosonFirst hL (dGammaB h y) = oneBody h (bosonFirst hL y))
    ∧ (dGammaF (1 : Matrix (Fin N) (Fin N) ℂ) = fTotalNumber N
        ∧ dGammaB (L := L) (1 : Matrix (Fin K) (Fin K) ℂ) = bTotalNumber K L)
    ∧ Matrix.toEuclideanLin (fieldHamiltonian K L) = dGammaB 1 + ((K : ℂ) / 2) • 1 :=
  ⟨fermionFirst_dGammaF, bosonFirst_dGammaB, ⟨dGammaF_one, dGammaB_one⟩,
    toEuclideanLin_fieldHamiltonian⟩

end CSD.SigmaLayer
