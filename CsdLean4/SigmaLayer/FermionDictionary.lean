/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FermionFock

/-!
# SigmaLayer/FermionDictionary: first and second quantisation as operators, for fermions

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #220 (fermion half), after ~~#215~~ (`SigmaLayer/FermionFock.lean`).

~~#215~~ identified each `n`-particle sector of the fermionic Fock space with the `n`-fermion sector
of first quantisation by the canonical map on amplitudes. This module normalises that map and shows
it carries the second-quantised operators to the first-quantised ones.

## What is proved

* `fermionFirst n N` — the **first-quantisation map** `FieldSpace N 2 → ManyParticle n N`: the
  amplitude on a strictly increasing configuration is `1/√n!` times the Fock amplitude on its set of
  occupied modes (`fermionFirst_apply_strictMono`), extended antisymmetrically
  (`fermionFirst_mem`);
* ★★★ `inner_fermionFirst_of_mem` — **it is an isometry on each `n`-particle sector**
  (`⟪Φ y, Φ y'⟫ = ⟪y, y'⟫`), from `inner_fermionFirst` and the regrouping of injective
  configurations by sorting (`Tuple.sum_injective_eq_sum_strictMono_perm`);
* ★★ `fermionFirst_fockBasis` — **a Fock basis state is a normalised Slater determinant** of the
  basis orbitals of its occupied modes;
* `fCreate1 j` — first-quantised creation, `√(n+1)` times the antisymmetrised `e_j ⊗ ·`, with the
  explicit form `fCreate1_apply` (`(1/√(n+1)) ∑_p (−1)^p [c p = j] x (c ∘ p.succAbove)`);
  ★★★ `fermionFirst_fCreate` — **`Φ_{n+1} (a_j† y) = fCreate1 j (Φ_n y)`**;
* `fAnnihilate1 j` — first-quantised annihilation, `√(n+1) x (j, ·)`; ★★★ `fermionFirst_fAnnihilate`
  — **`Φ_n (a_j y) = fAnnihilate1 j (Φ_{n+1} y)`**;
* the sign bookkeeping: `splitPermEquiv` (a permutation of `Fin (n+1)` is the image `p` of `0` and
  a permutation of the rest, of sign `(−1)^p · sign e`), and ★ `jwSign_image` (on a strictly
  increasing configuration the Jordan–Wigner sign of the `p`-th occupied mode is `(−1)^p`);
* ★★★ `fermion_dictionary` — the capstone.

## Honest scope

⚠️ **The boson half** (normalisation `√(∏ P_m!/n!)`, creation as symmetrised tensoring) is ~~#221~~
(`SigmaLayer/BosonDictionary.lean`); **one-body operators** — `dΓ(h) = ∑ h_ij a_i† a_j`
corresponding to `∑_k h^{(k)}` — are BACKLOG #222.

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/FermionFock.lean`
(`fCreate`, `fAnnihilate`, `jwSign`, `occOfFinset`); `SigmaLayer/ManyIdenticalParticles.lean`
(`nFermionSector`, `nFermionEquiv`, `antisymmetrizer`, `slater`);
`Mathlib/LinearAlgebra/Matrix/CauchyBinet.lean` (`Tuple.sum_injective_eq_sum_strictMono_perm`);
Mathlib `Fin.cycleRange`, `Fin.sign_cycleRange`, `Fin.cons_removeNth_eq_comp_cycleRange_symm`,
`Equiv.Perm.decomposeFin`; `specs/BACKLOG.md` #220.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

open CSD.CV

variable {n N : ℕ}

/-! ### Permutations of `Fin (n + 1)` by the image of `0` -/

/-- Fix `0` and act by `e` on the rest. -/
def liftPerm (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

theorem liftPerm_zero (e : Equiv.Perm (Fin n)) : liftPerm e 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 e

theorem liftPerm_succ (e : Equiv.Perm (Fin n)) (i : Fin n) : liftPerm e i.succ = (e i).succ := by
  rw [liftPerm, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]

theorem permSign_liftPerm (e : Equiv.Perm (Fin n)) : permSign (liftPerm e) = permSign e := by
  simp [permSign, liftPerm]

theorem permSign_cycleRange_symm (p : Fin (n + 1)) :
    permSign p.cycleRange.symm = (-1) ^ (p : ℕ) := by
  simp [permSign, Equiv.Perm.sign_symm, Fin.sign_cycleRange]

/-- The permutation sending `0` to `p` and `i + 1` to `p.succAbove (e i)`. -/
def splitPerm (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  p.cycleRange.symm * liftPerm e

theorem splitPerm_zero (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) : splitPerm p e 0 = p := by
  rw [splitPerm, Equiv.Perm.mul_apply, liftPerm_zero]
  exact (Equiv.symm_apply_eq _).2 (Fin.cycleRange_self p).symm

theorem splitPerm_succ (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    splitPerm p e i.succ = p.succAbove (e i) := by
  rw [splitPerm, Equiv.Perm.mul_apply, liftPerm_succ, Fin.cycleRange_symm_succ]

theorem permSign_splitPerm (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    permSign (splitPerm p e) = (-1) ^ (p : ℕ) * permSign e := by
  rw [splitPerm, permSign_mul, permSign_cycleRange_symm, permSign_liftPerm]

theorem splitPerm_injective :
    Function.Injective fun q : Fin (n + 1) × Equiv.Perm (Fin n) => splitPerm q.1 q.2 := by
  rintro ⟨p, e⟩ ⟨p', e'⟩ h
  have hp : p = p' := by
    have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ 0) h
    simpa only [splitPerm_zero] using this
  subst hp
  have he : e = e' := Equiv.ext fun i => by
    have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ i.succ) h
    simp only [splitPerm_succ] at this
    exact Fin.succAbove_right_injective this
  rw [he]

/-- The equivalence `(p, e) ↦ splitPerm p e` from `Fin (n + 1) × Perm (Fin n)` onto `Perm (Fin (n + 1))`:
bijective by `splitPerm_injective` and counting (`splitPerm_zero`, `splitPerm_succ` give its values). -/
noncomputable def splitPermEquiv (n : ℕ) : Fin (n + 1) × Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun q : Fin (n + 1) × Equiv.Perm (Fin n) => splitPerm q.1 q.2)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨splitPerm_injective, by
        rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
          Fintype.card_fin, Nat.factorial_succ]⟩)

/-! ### Occupied sets and signs -/

theorem occOfFinset_apply (S : Finset (Fin N)) (j : Fin N) :
    occOfFinset S j = if j ∈ S then 1 else 0 := rfl

theorem occOfFinset_erase (S : Finset (Fin N)) (j : Fin N) :
    occOfFinset (S.erase j) = Function.update (occOfFinset S) j 0 := by
  funext k
  by_cases h : k = j
  · subst h
    simp [occOfFinset_apply]
  · simp [occOfFinset_apply, h]

theorem occOfFinset_insert (S : Finset (Fin N)) (j : Fin N) :
    occOfFinset (insert j S) = Function.update (occOfFinset S) j 1 := by
  funext k
  by_cases h : k = j
  · subst h
    simp [occOfFinset_apply]
  · simp [occOfFinset_apply, h]

theorem occOfFinset_injective : Function.Injective (occOfFinset (N := N)) := by
  intro S T h
  ext j
  have := congrFun h j
  simp only [occOfFinset_apply] at this
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp_all

/-- The Jordan–Wigner sign of a set of occupied modes counts the occupied modes below. -/
theorem jwSign_occOfFinset (S : Finset (Fin N)) (j : Fin N) :
    jwSign (occOfFinset S) j = (-1) ^ (S.filter (· < j)).card := by
  have h : ∀ k, occParity (occOfFinset S k) = if k ∈ S then -1 else 1 := fun k => by
    by_cases hk : k ∈ S <;> simp [occParity, occOfFinset_apply, hk]
  rw [jwSign, Finset.prod_congr rfl fun k _ => h k, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one]
  congr 2
  ext k
  simp [and_comm]

theorem card_filter_image_lt {k : ℕ} {m : Fin k → Fin N} (hm : StrictMono m) (p : Fin k) :
    ((Finset.univ.image m).filter (· < m p)).card = p := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ hm.injective]
  have : Finset.univ.filter (fun i => m i < m p) = Finset.Iio p := by
    ext i
    simp [hm.lt_iff_lt]
  rw [this, Fin.card_Iio]

/-- **On a strictly increasing configuration the Jordan–Wigner sign of the `p`-th occupied mode is
`(−1)^p`.** -/
theorem jwSign_image {k : ℕ} {m : Fin k → Fin N} (hm : StrictMono m) (p : Fin k) :
    jwSign (occOfFinset (Finset.univ.image m)) (m p) = (-1) ^ (p : ℕ) := by
  rw [jwSign_occOfFinset, card_filter_image_lt hm]

/-- Two strictly increasing configurations with the same occupied set are equal. -/
theorem strictMono_eq_of_image_eq {k : ℕ} {c d : Fin k → Fin N} (hc : StrictMono c)
    (hd : StrictMono d) (h : Finset.univ.image c = Finset.univ.image d) : c = d :=
  congrArg Subtype.val ((strictConfigEquivFinset k N).injective
    (a₁ := ⟨c, hc⟩) (a₂ := ⟨d, hd⟩) (Subtype.ext h))

theorem image_comp_succAbove {c : Fin (n + 1) → Fin N} (hc : Function.Injective c)
    (p : Fin (n + 1)) :
    Finset.univ.image (c ∘ p.succAbove) = (Finset.univ.image c).erase (c p) := by
  rw [← Finset.image_image, Fin.image_succAbove_univ, ← Finset.image_erase hc]
  congr 1
  ext i
  simp

/-! ### The first-quantisation map -/

/-- `1/√n!`. -/
noncomputable def invSqrtFact (n : ℕ) : ℂ := ((Real.sqrt n.factorial)⁻¹ : ℝ)

theorem conj_invSqrtFact (n : ℕ) : (starRingEnd ℂ) (invSqrtFact n) = invSqrtFact n :=
  Complex.conj_ofReal _

theorem invSqrtFact_mul_self (n : ℕ) : invSqrtFact n * invSqrtFact n * n.factorial = 1 := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h : (Real.sqrt n.factorial)⁻¹ * (Real.sqrt n.factorial)⁻¹ * (n.factorial : ℝ) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  unfold invSqrtFact
  exact_mod_cast h

theorem invSqrtFact_succ (n : ℕ) :
    invSqrtFact (n + 1) = ((Real.sqrt (n + 1))⁻¹ : ℝ) * invSqrtFact n := by
  unfold invSqrtFact
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
  push_cast
  ring

/-- The Fock amplitudes on the `n`-element occupied sets, as a function on strictly increasing
configurations. -/
noncomputable def fockAmpLin (n N : ℕ) : FieldSpace N 2 →ₗ[ℂ] (StrictConfig n N → ℂ) where
  toFun y g := y (occOfFinset (Finset.univ.image g.1))
  map_add' y y' := by funext g; simp
  map_smul' a y := by funext g; simp

/-- **The first-quantisation map**: `1/√n!` times the Fock amplitude on the occupied set, extended
antisymmetrically. -/
noncomputable def fermionFirst (n N : ℕ) : FieldSpace N 2 →ₗ[ℂ] ManyParticle n N :=
  invSqrtFact n • ((nFermionSector n N).subtype ∘ₗ
    (nFermionEquiv (n := n) (N := N)).symm.toLinearMap ∘ₗ fockAmpLin n N)

theorem fermionFirst_mem (y : FieldSpace N 2) : fermionFirst n N y ∈ nFermionSector n N := by
  simp only [fermionFirst, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (Submodule.coe_mem _)

theorem nFermionEquiv_symm_apply (f : StrictConfig n N → ℂ) (g : StrictConfig n N) :
    ((nFermionEquiv (n := n) (N := N)).symm f : ManyParticle n N) g.1 = f g := by
  rw [show ((nFermionEquiv (n := n) (N := N)).symm f : ManyParticle n N) g.1
      = nFermionEquiv (nFermionEquiv.symm f) g from rfl, LinearEquiv.apply_symm_apply]

theorem fermionFirst_apply_strictMono (y : FieldSpace N 2) (g : StrictConfig n N) :
    fermionFirst n N y g.1 = invSqrtFact n * y (occOfFinset (Finset.univ.image g.1)) := by
  simp only [fermionFirst, LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul,
    LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
  rw [nFermionEquiv_symm_apply]
  rfl

/-- Two fermions agreeing on the strictly increasing configurations are equal. -/
theorem eq_of_mem_nFermionSector {x x' : ManyParticle n N} (hx : x ∈ nFermionSector n N)
    (hx' : x' ∈ nFermionSector n N) (h : ∀ g : StrictConfig n N, x g.1 = x' g.1) : x = x' := by
  have := nFermionEquiv.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨x', hx'⟩) (funext h)
  exact congrArg Subtype.val this

/-- **The inner product of first-quantised states** is the inner product of the Fock amplitudes on
the `n`-particle configurations. -/
theorem inner_fermionFirst (y y' : FieldSpace N 2) :
    ⟪fermionFirst n N y, fermionFirst n N y'⟫_ℂ
      = ∑ d : {d : FieldConfig N 2 // occTotal d = n}, y' d.1 * (starRingEnd ℂ) (y d.1) := by
  classical
  have hx := fermionFirst_mem (n := n) y
  have hx' := fermionFirst_mem (n := n) y'
  set x := fermionFirst n N y with hxdef
  set x' := fermionFirst n N y' with hx'def
  let G : ManyConfig n N → ℂ := fun c => x' c * (starRingEnd ℂ) (x c)
  have hinner : ⟪x, x'⟫_ℂ = ∑ c, G c := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [RCLike.inner_apply]
  have hzero : ∀ c : {c : ManyConfig n N // ¬ Function.Injective c}, G c.1 = 0 := fun c => by
    simp only [G, apply_eq_zero_of_not_injective hx c.2, map_zero, mul_zero]
  have hperm : ∀ (g : ManyConfig n N) (τ : Equiv.Perm (Fin n)), G (g ∘ τ) = G g := fun g τ => by
    simp only [G, mem_nFermionSector_iff_apply.1 hx, mem_nFermionSector_iff_apply.1 hx', map_mul]
    have hs : (starRingEnd ℂ) (permSign τ) = permSign τ := by simp [permSign]
    rw [hs]
    linear_combination (x' g * (starRingEnd ℂ) (x g)) * permSign_mul_self τ
  rw [hinner, ← Fintype.sum_subtype_add_sum_subtype Function.Injective, Fintype.sum_eq_zero _ hzero,
    add_zero, Tuple.sum_injective_eq_sum_strictMono_perm G]
  simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  refine Fintype.sum_equiv ((strictConfigEquivFinset n N).trans (finsetEquivOcc n N)) _ _
    fun g => ?_
  simp only [G, hxdef, hx'def]
  rw [fermionFirst_apply_strictMono y' g, fermionFirst_apply_strictMono y g, map_mul,
    conj_invSqrtFact]
  have := invSqrtFact_mul_self n
  calc (n.factorial : ℂ) * (invSqrtFact n * y' (occOfFinset (Finset.univ.image g.1))
        * (invSqrtFact n * (starRingEnd ℂ) (y (occOfFinset (Finset.univ.image g.1)))))
      = (invSqrtFact n * invSqrtFact n * n.factorial)
        * (y' (occOfFinset (Finset.univ.image g.1))
          * (starRingEnd ℂ) (y (occOfFinset (Finset.univ.image g.1)))) := by ring
    _ = _ := by rw [this, one_mul]; rfl

/-- **The first-quantisation map is an isometry on each `n`-particle sector.** -/
theorem inner_fermionFirst_of_mem {y : FieldSpace N 2} (hy : y ∈ fockSector N n)
    (y' : FieldSpace N 2) :
    ⟪fermionFirst n N y, fermionFirst n N y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
  classical
  rw [inner_fermionFirst, PiLp.inner_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun d : FieldConfig N 2 => occTotal d = n)]
  rw [Fintype.sum_eq_zero (fun d : {d : FieldConfig N 2 // ¬ occTotal d = n} =>
      ⟪y d.1, y' d.1⟫_ℂ) (fun d => by rw [hy d.1 d.2, inner_zero_left]), add_zero]
  exact Finset.sum_congr rfl fun d _ => by rw [RCLike.inner_apply]

/-! ### Fock basis states are Slater determinants -/

/-- The Fock basis state with the modes of `S` occupied. -/
noncomputable def fockBasis (S : Finset (Fin N)) : FieldSpace N 2 :=
  WithLp.toLp 2 (Pi.single (occOfFinset S) 1)

/-- The basis orbital `e_m`. -/
noncomputable def basisOrbital (m : Fin N) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (Pi.single m 1)

/-- **A Fock basis state is a normalised Slater determinant** of the basis orbitals of its occupied
modes, in increasing order. -/
theorem fermionFirst_fockBasis (S : Finset (Fin N)) (hS : S.card = n) :
    fermionFirst n N (fockBasis S)
      = invSqrtFact n • slater (fun k => basisOrbital (S.orderEmbOfFin hS k)) := by
  refine eq_of_mem_nFermionSector (fermionFirst_mem _)
    (Submodule.smul_mem _ _ (slater_mem_nFermionSector _)) fun g => ?_
  rw [fermionFirst_apply_strictMono, PiLp.smul_apply, smul_eq_mul, slater_apply]
  congr 1
  have hsm : StrictMono (S.orderEmbOfFin hS) := (S.orderEmbOfFin hS).strictMono
  have himS : Finset.univ.image (S.orderEmbOfFin hS) = S := Finset.coe_injective (by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin])
  by_cases himg : Finset.univ.image g.1 = S
  · have hg : g.1 = S.orderEmbOfFin hS :=
      strictMono_eq_of_image_eq g.2 hsm (himg.trans himS.symm)
    rw [himg]
    simp only [fockBasis, PiLp.toLp_apply, Pi.single_eq_same]
    have hmat : slaterMatrix (fun k => basisOrbital (S.orderEmbOfFin hS k)) g.1 = 1 := by
      ext i k
      simp only [slaterMatrix, Matrix.of_apply, basisOrbital, PiLp.toLp_apply, hg, Matrix.one_apply]
      by_cases hik : i = k
      · subst hik
        simp
      · rw [Pi.single_apply, ite_eq_right ((S.orderEmbOfFin hS).injective.ne hik), ite_eq_right hik]
    rw [hmat, Matrix.det_one]
  · have hne : occOfFinset (Finset.univ.image g.1) ≠ occOfFinset S :=
      fun h => himg (occOfFinset_injective h)
    simp only [fockBasis, PiLp.toLp_apply, Pi.single_apply, hne, ↓reduceIte]
    have hcard : (Finset.univ.image g.1).card = n := by
      rw [Finset.card_image_of_injective _ g.2.injective, Finset.card_univ, Fintype.card_fin]
    obtain ⟨i, hi⟩ : ∃ i, g.1 i ∉ S := by
      by_contra hall
      push Not at hall
      exact himg (Finset.eq_of_subset_of_card_le
        (fun m hm => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hm; exact hall i)
        (by rw [hS, hcard]))
    refine (Matrix.det_eq_zero_of_row_eq_zero i fun k => ?_).symm
    simp only [slaterMatrix, Matrix.of_apply, basisOrbital, PiLp.toLp_apply, Pi.single_apply]
    rw [ite_eq_right]
    rintro h
    exact hi (h ▸ Finset.orderEmbOfFin_mem S hS k)

/-! ### Creation -/

/-- `e_j ⊗ x`: a particle in mode `j` in slot `0`, the others in `x`. -/
noncomputable def consLin (j : Fin N) : ManyParticle n N →ₗ[ℂ] ManyParticle (n + 1) N where
  toFun x := WithLp.toLp 2 fun c => if c 0 = j then x (Fin.tail c) else 0
  map_add' x y := by
    ext c
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    ext c
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- **First-quantised creation** of a particle in mode `j`: `√(n+1)` times the antisymmetrised
`e_j ⊗ ·`. -/
noncomputable def fCreate1 (j : Fin N) : ManyParticle n N →ₗ[ℂ] ManyParticle (n + 1) N :=
  ((Real.sqrt (n + 1) : ℝ) : ℂ) • (antisymmetrizer (n + 1) N ∘ₗ consLin j)

theorem fCreate1_mem (j : Fin N) (x : ManyParticle n N) :
    fCreate1 j x ∈ nFermionSector (n + 1) N := by
  simp only [fCreate1, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply]
  exact Submodule.smul_mem _ _ (isProj_antisymmetrizer.map_mem _)

/-- **The explicit form of first-quantised creation** on a fermion:
`(1/√(n+1)) ∑_p (−1)^p [c p = j] x (c ∘ p.succAbove)`. -/
theorem fCreate1_apply (j : Fin N) {x : ManyParticle n N} (hx : x ∈ nFermionSector n N)
    (c : ManyConfig (n + 1) N) :
    fCreate1 j x c = ((Real.sqrt (n + 1))⁻¹ : ℝ)
      * ∑ p : Fin (n + 1), (-1) ^ (p : ℕ) * (if c p = j then x (c ∘ p.succAbove) else 0) := by
  have hterm : ∀ (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)),
      permSign (splitPerm p e) * (consLin j x) (c ∘ splitPerm p e)
        = (-1) ^ (p : ℕ) * (if c p = j then x (c ∘ p.succAbove) else 0) := fun p e => by
    have htail : Fin.tail (c ∘ splitPerm p e) = (c ∘ p.succAbove) ∘ e := by
      funext i
      simp [Fin.tail, splitPerm_succ]
    show permSign (splitPerm p e)
        * (if (c ∘ splitPerm p e) 0 = j then x (Fin.tail (c ∘ splitPerm p e)) else 0) = _
    rw [htail, Function.comp_apply, splitPerm_zero, permSign_splitPerm,
      mem_nFermionSector_iff_apply.1 hx]
    split_ifs
    · linear_combination ((-1) ^ (p : ℕ) * x (c ∘ p.succAbove)) * permSign_mul_self e
    · ring
  simp only [fCreate1, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    PiLp.smul_apply, smul_eq_mul, antisymmetrizer_apply, WithLp.ofLp_sum, Finset.sum_apply,
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
  linear_combination (∑ p : Fin (n + 1), (-1) ^ (p : ℕ) *
    (if c p = j then x (c ∘ p.succAbove) else 0)) * hsqC

/-- **Creation in the two pictures**: `Φ_{n+1} (a_j† y) = fCreate1 j (Φ_n y)`. -/
theorem fermionFirst_fCreate (j : Fin N) (y : FieldSpace N 2) :
    fermionFirst (n + 1) N (fCreate j y) = fCreate1 j (fermionFirst n N y) := by
  refine eq_of_mem_nFermionSector (fermionFirst_mem _) (fCreate1_mem _ _) fun c => ?_
  rw [fermionFirst_apply_strictMono, fCreate1_apply j (fermionFirst_mem y), fCreate_apply,
    invSqrtFact_succ]
  set S := Finset.univ.image c.1
  by_cases hj : ∃ p, c.1 p = j
  · obtain ⟨p, rfl⟩ := hj
    have hmem : occOfFinset S (c.1 p) = 1 := by
      rw [occOfFinset_apply, ite_eq_left (Finset.mem_image_of_mem _ (Finset.mem_univ p))]
    rw [ite_eq_left hmem, Finset.sum_eq_single p]
    · rw [ite_eq_left rfl, fermionFirst_apply_strictMono y ⟨c.1 ∘ p.succAbove,
        c.2.comp (Fin.strictMono_succAbove p)⟩]
      simp only
      rw [image_comp_succAbove c.2.injective, occOfFinset_erase, jwSign_image c.2]
      ring
    · intro p' _ hp'
      rw [ite_eq_right (fun h => hp' (c.2.injective h)), mul_zero]
    · exact fun h => absurd (Finset.mem_univ p) h
  · push Not at hj
    have hnot : occOfFinset S j = 0 := by
      rw [occOfFinset_apply, ite_eq_right]
      intro hm
      obtain ⟨p, _, hp⟩ := Finset.mem_image.1 hm
      exact hj p hp
    rw [ite_eq_right (by rw [hnot]; decide), mul_zero, Finset.sum_eq_zero, mul_zero]
    intro p _
    rw [ite_eq_right (hj p), mul_zero]

/-! ### Annihilation -/

/-- **First-quantised annihilation** of a particle in mode `j`: `√(n+1) x (j, ·)`. -/
noncomputable def fAnnihilate1 (j : Fin N) : ManyParticle (n + 1) N →ₗ[ℂ] ManyParticle n N where
  toFun x := WithLp.toLp 2 fun c => ((Real.sqrt (n + 1) : ℝ) : ℂ) * x (Fin.cons j c)
  map_add' x y := by ext c; simp [mul_add]
  map_smul' a x := by ext c; simp [mul_left_comm]

theorem fAnnihilate1_apply (j : Fin N) (x : ManyParticle (n + 1) N) (c : ManyConfig n N) :
    fAnnihilate1 j x c = ((Real.sqrt (n + 1) : ℝ) : ℂ) * x (Fin.cons j c) := rfl

theorem fAnnihilate1_mem (j : Fin N) {x : ManyParticle (n + 1) N}
    (hx : x ∈ nFermionSector (n + 1) N) : fAnnihilate1 j x ∈ nFermionSector n N := by
  refine mem_nFermionSector_iff_apply.2 fun σ c => ?_
  rw [fAnnihilate1_apply, fAnnihilate1_apply]
  have hcons : (Fin.cons j (c ∘ σ) : Fin (n + 1) → Fin N) = Fin.cons j c ∘ liftPerm σ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [liftPerm_zero]
    · simp [liftPerm_succ]
  rw [hcons, mem_nFermionSector_iff_apply.1 hx, permSign_liftPerm]
  ring

/-- **Annihilation in the two pictures**: `Φ_n (a_j y) = fAnnihilate1 j (Φ_{n+1} y)`. -/
theorem fermionFirst_fAnnihilate (j : Fin N) (y : FieldSpace N 2) :
    fermionFirst n N (fAnnihilate j y) = fAnnihilate1 j (fermionFirst (n + 1) N y) := by
  refine eq_of_mem_nFermionSector (fermionFirst_mem _) (fAnnihilate1_mem j (fermionFirst_mem _))
    fun c => ?_
  have hx := fermionFirst_mem (n := n + 1) (N := N) y
  rw [fermionFirst_apply_strictMono, fAnnihilate1_apply, fAnnihilate_apply]
  set S := Finset.univ.image c.1 with hSdef
  by_cases hj : j ∈ S
  · obtain ⟨p, _, hp⟩ := Finset.mem_image.1 hj
    have hocc : occOfFinset S j = 1 := by rw [occOfFinset_apply, ite_eq_left hj]
    rw [ite_eq_right (by rw [hocc]; decide), mul_zero]
    have hni : ¬ Function.Injective (Fin.cons j c.1 : Fin (n + 1) → Fin N) := fun h =>
      Fin.succ_ne_zero p (h (by simp [hp]))
    rw [apply_eq_zero_of_not_injective hx hni, mul_zero]
  · have hocc : occOfFinset S j = 0 := by rw [occOfFinset_apply, ite_eq_right hj]
    rw [ite_eq_left hocc]
    have hcardS : S.card = n := by
      rw [hSdef, Finset.card_image_of_injective _ c.2.injective, Finset.card_univ,
        Fintype.card_fin]
    have hcard : (insert j S).card = n + 1 := by rw [Finset.card_insert_of_notMem hj, hcardS]
    set m := (insert j S).orderEmbOfFin hcard
    have hm : StrictMono (m : Fin (n + 1) → Fin N) := m.strictMono
    have himm : Finset.univ.image (m : Fin (n + 1) → Fin N) = insert j S :=
      Finset.coe_injective (by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin])
    obtain ⟨p, hp⟩ : ∃ p, m p = j := by
      have : j ∈ Finset.univ.image (m : Fin (n + 1) → Fin N) := by
        rw [himm]
        exact Finset.mem_insert_self j S
      obtain ⟨p, _, hp⟩ := Finset.mem_image.1 this
      exact ⟨p, hp⟩
    have hrest : (m : Fin (n + 1) → Fin N) ∘ p.succAbove = c.1 := by
      refine strictMono_eq_of_image_eq (hm.comp (Fin.strictMono_succAbove p)) c.2 ?_
      rw [image_comp_succAbove hm.injective, himm, hp, Finset.erase_insert hj]
    have hcons : (Fin.cons j c.1 : Fin (n + 1) → Fin N)
        = (m : Fin (n + 1) → Fin N) ∘ p.cycleRange.symm := by
      rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm, hp]
      congr 1
      rw [← hrest]
      rfl
    rw [hcons, mem_nFermionSector_iff_apply.1 hx, permSign_cycleRange_symm,
      fermionFirst_apply_strictMono y ⟨m, hm⟩]
    simp only
    rw [himm, occOfFinset_insert, invSqrtFact_succ]
    have hjw : jwSign (occOfFinset S) j = (-1) ^ (p : ℕ) := by
      rw [← jwSign_update_of_not_lt (lt_irrefl j) (occOfFinset S) 1, ← occOfFinset_insert,
        ← himm, ← hp, jwSign_image hm]
    rw [hjw]
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have hsqC : ((Real.sqrt (n + 1) : ℝ) : ℂ) * ((Real.sqrt (n + 1))⁻¹ : ℝ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one]
    linear_combination (-(invSqrtFact n * (-1) ^ (p : ℕ)
      * y (Function.update (occOfFinset S) j 1))) * hsqC

/-! ### The capstone -/

/-- **First and second quantisation as operators, for fermions.**

1. the first-quantisation map is an isometry on each `n`-particle sector;
2. it sends each Fock basis state to the normalised Slater determinant of its occupied orbitals;
3. it carries second-quantised creation `a_j†` to `√(n+1)` times antisymmetrised tensoring with
   `e_j`;
4. it carries annihilation `a_j` to `√(n+1)` times evaluation with a particle in mode `j`. -/
theorem fermion_dictionary :
    (∀ y y' : FieldSpace N 2, y ∈ fockSector N n → y' ∈ fockSector N n →
        ⟪fermionFirst n N y, fermionFirst n N y'⟫_ℂ = ⟪y, y'⟫_ℂ)
    ∧ (∀ (S : Finset (Fin N)) (hS : S.card = n), fermionFirst n N (fockBasis S)
        = invSqrtFact n • slater (fun k => basisOrbital (S.orderEmbOfFin hS k)))
    ∧ (∀ (j : Fin N) (y : FieldSpace N 2),
        fermionFirst (n + 1) N (fCreate j y) = fCreate1 j (fermionFirst n N y))
    ∧ ∀ (j : Fin N) (y : FieldSpace N 2),
        fermionFirst n N (fAnnihilate j y) = fAnnihilate1 j (fermionFirst (n + 1) N y) :=
  ⟨fun _ y' hy _ => inner_fermionFirst_of_mem hy y', fermionFirst_fockBasis,
    fermionFirst_fCreate, fermionFirst_fAnnihilate⟩

end CSD.SigmaLayer
