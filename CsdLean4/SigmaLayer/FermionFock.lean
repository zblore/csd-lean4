/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FieldModes
public import CsdLean4.SigmaLayer.ManyIdenticalParticles

/-!
# SigmaLayer/FermionFock: second quantisation for fermions, exactly

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #215 (fermion half), after ~~#214~~ (`SigmaLayer/ManyIdenticalParticles.lean`).

The fermionic Fock space of `N` modes is the occupation lattice of the CV track with two levels
per mode, `FieldSpace N 2` (`CV/FieldModes.lean`): amplitudes on occupation configurations
`c : Fin N → Fin 2`. It is **finite**, of dimension `2^N`, and it is literally the `N`-qubit chain.

## What is proved

* `supportedOn p` — the states supported on the configurations satisfying `p`, a function space on
  them (`supportedOnEquiv`); for the fibres of any map, ★ `isInternal_supportedOn_fiber`: **the
  space is the orthogonal internal direct sum of the fibre subspaces**;
* `jwSign c j` — the Jordan–Wigner sign, the parity of the occupied modes before `j`; the creation
  and annihilation operators `fCreate j`, `fAnnihilate j`, with ★ `inner_fCreate`
  (**`fCreate j` is the adjoint of `fAnnihilate j`**);
* ★★★ **the canonical anticommutation relations, exactly**: `fAnnihilate_mul_fCreate_add`
  (`{a_i, a_j†} = δ_ij`), `fAnnihilate_mul_fAnnihilate_add` (`{a_i, a_j} = 0`),
  `fCreate_mul_fCreate_add` (`{a_i†, a_j†} = 0`) — in finite dimension, in contrast with the CCR
  (`no_exact_finite_ccr`, `CV/ApproxCCR.lean`);
* ★★ `fAnnihilate_eq_jwString_mul_qubitLower` — **Jordan–Wigner**: `a_j = Z_0 ⋯ Z_{j−1} σ⁻_j`
  with `qubitZ`, `qubitLower` the single-site operators of the qubit chain;
* `fNumber j = a_j† a_j` (occupation of mode `j`) and `fTotalNumber` (`∑ c j`);
* `fockSector n` — the `n`-particle sector, the eigenspace of the total number with eigenvalue `n`
  (`mem_fockSector_iff`); ★★ `isInternal_fockSector`: **the Fock space is the direct sum of the
  `n`-particle sectors**;
* ★★★ `fockFermionEquiv` — **the `n`-particle sector of the Fock space is the `n`-fermion sector of
  first quantisation** (`nFermionSector n N` of ~~#214~~), by the canonical map: the first-quantised
  amplitude on a strictly increasing configuration is the Fock amplitude on its set of occupied
  modes (`fockFermionEquiv_apply`); ★ `finrank_fockSector` (`N.choose n`), ★ `finrank_fermionFock`
  (`2^N`).

## Honest scope

⚠️ **The identification here is by the canonical map on amplitudes.** The operator dictionary — the
norm factor `√n!`, `a_j†` as antisymmetrised tensoring with the orbital `e_j`, Fock basis states as
Slater determinants — is ~~#220~~ (`SigmaLayer/FermionDictionary.lean`).

⚠️ **The sign convention** is the Jordan–Wigner order of the modes; any other order gives a unitarily
equivalent set of operators.

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/ManyIdenticalParticles.lean`
(`nFermionSector`, `nFermionEquiv`, `strictConfigEquivFinset`); `CV/FieldModes.lean` (`FieldSpace`);
`CV/ApproxCCR.lean` (`no_exact_finite_ccr`); Mathlib `OrthogonalFamily.independent`,
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`; `specs/BACKLOG.md` #215.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

open CSD.CV

/-! ### States supported on a set of configurations -/

section Supported

variable {ι : Type*} [Fintype ι]

/-- The states supported on the configurations satisfying `p`. -/
def supportedOn (p : ι → Prop) : Submodule ℂ (EuclideanSpace ℂ ι) where
  carrier := {x | ∀ c, ¬ p c → x c = 0}
  add_mem' hx hy c hc := by simp [hx c hc, hy c hc]
  zero_mem' c _ := by simp
  smul_mem' a x hx c hc := by simp [hx c hc]

omit [Fintype ι] in
theorem mem_supportedOn {p : ι → Prop} {x : EuclideanSpace ℂ ι} :
    x ∈ supportedOn p ↔ ∀ c, ¬ p c → x c = 0 := Iff.rfl

/-- A state supported on `p` is a function on `{c // p c}`. -/
noncomputable def supportedOnEquiv (p : ι → Prop) [DecidablePred p] :
    supportedOn p ≃ₗ[ℂ] ({c // p c} → ℂ) where
  toFun x c := (x : EuclideanSpace ℂ ι) c.1
  map_add' x y := by funext c; simp
  map_smul' a x := by funext c; simp
  invFun f := ⟨WithLp.toLp 2 fun c => if h : p c then f ⟨c, h⟩ else 0, fun c hc => by simp [hc]⟩
  left_inv x := Subtype.ext (by
    ext c
    by_cases h : p c
    · simp [h]
    · simp [h, x.2 c h])
  right_inv f := funext fun c => by simp [c.2]

theorem finrank_supportedOn (p : ι → Prop) [DecidablePred p] :
    finrank ℂ (supportedOn p) = Fintype.card {c // p c} := by
  rw [LinearEquiv.finrank_eq (supportedOnEquiv p), Module.finrank_fintype_fun_eq_card]

/-- States supported on disjoint sets are orthogonal. -/
theorem supportedOn_orthogonal {p q : ι → Prop} (h : ∀ c, ¬ (p c ∧ q c)) :
    supportedOn p ⟂ supportedOn q :=
  Submodule.isOrtho_iff_inner_eq.2 fun x hx y hy => by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hp : p c
    · rw [hy c fun hq => h c ⟨hp, hq⟩, inner_zero_right]
    · rw [hx c hp, inner_zero_left]

/-- The component of a state on the configurations satisfying `p`. -/
noncomputable def restrictTo (p : ι → Prop) [DecidablePred p] (x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun c => if p c then x c else 0

omit [Fintype ι] in
theorem restrictTo_mem (p : ι → Prop) [DecidablePred p] (x : EuclideanSpace ℂ ι) :
    restrictTo p x ∈ supportedOn p := fun c hc => by simp [restrictTo, hc]

/-- **The fibres of a map split the space orthogonally**: `EuclideanSpace ℂ ι` is the internal
direct sum of the states supported on the fibres of `f`. -/
theorem isInternal_supportedOn_fiber {κ : Type*} [DecidableEq κ] (f : ι → κ) :
    DirectSum.IsInternal fun k => supportedOn fun c => f c = k := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · refine OrthogonalFamily.independent (orthogonalFamily_iff_pairwise.2 fun k k' hkk' => ?_)
    exact supportedOn_orthogonal fun c h => hkk' (h.1.symm.trans h.2)
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = ∑ k ∈ Finset.univ.image f, restrictTo (fun c => f c = k) x := by
      ext c
      rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single (f c)]
      · simp [restrictTo]
      · intro k _ hk
        simp [restrictTo, Ne.symm hk]
      · intro h
        exact absurd (Finset.mem_image_of_mem f (Finset.mem_univ c)) h
    rw [hx]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.mem_iSup_of_mem k (restrictTo_mem (fun c => f c = k) x)

end Supported

/-! ### The Jordan–Wigner sign -/

variable {N : ℕ}

theorem fin_two_cases (v : Fin 2) : v = 0 ∨ v = 1 := by
  fin_cases v <;> simp

/-- The parity of an occupation: `1` for an empty mode, `−1` for an occupied one. -/
def occParity (v : Fin 2) : ℂ := if v = 0 then 1 else -1

theorem occParity_mul_self (v : Fin 2) : occParity v * occParity v = 1 := by
  unfold occParity
  split_ifs <;> norm_num

theorem star_occParity (v : Fin 2) : star (occParity v) = occParity v := by
  unfold occParity
  split_ifs <;> simp

/-- **The Jordan–Wigner sign** of mode `j` in the configuration `c`: the parity of the occupied
modes before `j`. -/
def jwSign (c : FieldConfig N 2) (j : Fin N) : ℂ :=
  ∏ k ∈ Finset.univ.filter (· < j), occParity (c k)

theorem jwSign_mul_self (c : FieldConfig N 2) (j : Fin N) : jwSign c j * jwSign c j = 1 := by
  rw [jwSign, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun k _ => occParity_mul_self (c k)

theorem star_jwSign (c : FieldConfig N 2) (j : Fin N) : star (jwSign c j) = jwSign c j := by
  rw [jwSign, star_prod]
  exact Finset.prod_congr rfl fun k _ => star_occParity (c k)

theorem conj_jwSign (c : FieldConfig N 2) (j : Fin N) : (starRingEnd ℂ) (jwSign c j) = jwSign c j :=
  star_jwSign c j

/-- Changing a mode at or after `j` leaves the sign of `j`. -/
theorem jwSign_update_of_not_lt {i j : Fin N} (h : ¬ i < j) (c : FieldConfig N 2) (v : Fin 2) :
    jwSign (Function.update c i v) j = jwSign c j := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hki : k ≠ i := by
    rintro rfl
    exact h (by simpa using hk)
  rw [Function.update_of_ne hki]

/-- Changing a mode before `j` multiplies the sign of `j` by the change of parity. -/
theorem jwSign_update_of_lt {i j : Fin N} (h : i < j) (c : FieldConfig N 2) (v : Fin 2) :
    jwSign (Function.update c i v) j = occParity v * occParity (c i) * jwSign c j := by
  have hi : i ∈ Finset.univ.filter (· < j) := by simp [h]
  unfold jwSign
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ (fun k => occParity (c k)) hi,
    Function.update_self]
  have hrest : ∏ k ∈ (Finset.univ.filter (· < j)).erase i, occParity (Function.update c i v k)
      = ∏ k ∈ (Finset.univ.filter (· < j)).erase i, occParity (c k) :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest]
  linear_combination (-(occParity v * ∏ k ∈ (Finset.univ.filter (· < j)).erase i,
    occParity (c k))) * occParity_mul_self (c i)

theorem update_of_eq {c : FieldConfig N 2} {i : Fin N} {v : Fin 2} (h : c i = v) :
    Function.update c i v = c :=
  h ▸ Function.update_eq_self i c

/-! ### Creation and annihilation -/

/-- **The fermionic annihilation operator** of mode `j`: the amplitude at `c` (mode `j` empty) is the
signed amplitude at `c` with mode `j` filled. -/
noncomputable def fAnnihilate (j : Fin N) : Module.End ℂ (FieldSpace N 2) where
  toFun x := WithLp.toLp 2 fun c => if c j = 0 then jwSign c j * x (Function.update c j 1) else 0
  map_add' x y := by
    ext c
    simp only [PiLp.add_apply]
    split_ifs <;> ring
  map_smul' a x := by
    ext c
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **The fermionic creation operator** of mode `j`. -/
noncomputable def fCreate (j : Fin N) : Module.End ℂ (FieldSpace N 2) where
  toFun x := WithLp.toLp 2 fun c => if c j = 1 then jwSign c j * x (Function.update c j 0) else 0
  map_add' x y := by
    ext c
    simp only [PiLp.add_apply]
    split_ifs <;> ring
  map_smul' a x := by
    ext c
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem fAnnihilate_apply (j : Fin N) (x : FieldSpace N 2) (c : FieldConfig N 2) :
    fAnnihilate j x c = if c j = 0 then jwSign c j * x (Function.update c j 1) else 0 := rfl

theorem fCreate_apply (j : Fin N) (x : FieldSpace N 2) (c : FieldConfig N 2) :
    fCreate j x c = if c j = 1 then jwSign c j * x (Function.update c j 0) else 0 := rfl

/-- Flip the occupation of mode `j`. -/
def flipMode (j : Fin N) : FieldConfig N 2 ≃ FieldConfig N 2 where
  toFun c := Function.update c j (if c j = 0 then 1 else 0)
  invFun c := Function.update c j (if c j = 0 then 1 else 0)
  left_inv c := by
    rcases fin_two_cases (c j) with h | h <;> simp [h, update_of_eq]
  right_inv c := by
    rcases fin_two_cases (c j) with h | h <;> simp [h, update_of_eq]

/-- **Creation is the adjoint of annihilation.** -/
theorem inner_fCreate (j : Fin N) (x y : FieldSpace N 2) :
    ⟪fCreate j x, y⟫_ℂ = ⟪x, fAnnihilate j y⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Fintype.sum_equiv (flipMode j) _ _ fun c => ?_
  rcases fin_two_cases (c j) with h | h
  · simp [flipMode, fCreate_apply, fAnnihilate_apply, h]
  · simp only [flipMode, Equiv.coe_fn_mk, h, fCreate_apply, fAnnihilate_apply, Function.update_self,
      ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, Function.update_idem, update_of_eq h,
      jwSign_update_of_not_lt (lt_irrefl j)]
    simp only [RCLike.inner_apply, map_mul, conj_jwSign]
    ring

/-! ### The canonical anticommutation relations -/

/-- **`{a_i, a_i†} = 1`.** -/
theorem fAnnihilate_mul_fCreate_add_self (i : Fin N) :
    fAnnihilate i * fCreate i + fCreate i * fAnnihilate i = 1 := by
  apply LinearMap.ext
  intro x
  ext c
  simp only [LinearMap.add_apply, Module.End.mul_apply, fAnnihilate_apply, fCreate_apply,
    PiLp.add_apply, Module.End.one_apply, Function.update_self, Function.update_idem,
    jwSign_update_of_not_lt (lt_irrefl i), ↓reduceIte]
  rcases fin_two_cases (c i) with h | h
  · simp [h, update_of_eq h, ← mul_assoc, jwSign_mul_self]
  · simp [h, update_of_eq h, ← mul_assoc, jwSign_mul_self]

/-- **`{a_i, a_j†} = 0` for `i ≠ j`.** -/
theorem fAnnihilate_mul_fCreate_add_of_ne {i j : Fin N} (hij : i ≠ j) :
    fAnnihilate i * fCreate j + fCreate j * fAnnihilate i = 0 := by
  apply LinearMap.ext
  intro x
  ext c
  simp only [LinearMap.add_apply, Module.End.mul_apply, fAnnihilate_apply, fCreate_apply,
    PiLp.add_apply, LinearMap.zero_apply, PiLp.zero_apply,
    Function.update_of_ne (Ne.symm hij), Function.update_of_ne hij,
    Function.update_comm (β := fun _ => Fin 2) hij 1 0 c]
  rcases fin_two_cases (c i) with hi | hi <;> rcases fin_two_cases (c j) with hj | hj <;>
    simp only [hi, hj, ↓reduceIte, mul_zero, add_zero,
      show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [jwSign_update_of_lt hlt, jwSign_update_of_not_lt (not_lt.2 hlt.le), hi]
    simp [occParity]
    ring
  · rw [jwSign_update_of_not_lt (not_lt.2 hgt.le), jwSign_update_of_lt hgt, hj]
    simp [occParity]
    ring

/-- **`{a_i, a_j†} = δ_ij`.** -/
theorem fAnnihilate_mul_fCreate_add (i j : Fin N) :
    fAnnihilate i * fCreate j + fCreate j * fAnnihilate i = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    exact fAnnihilate_mul_fCreate_add_self i
  · exact fAnnihilate_mul_fCreate_add_of_ne hij

/-- **`{a_i, a_j} = 0`.** -/
theorem fAnnihilate_mul_fAnnihilate_add (i j : Fin N) :
    fAnnihilate i * fAnnihilate j + fAnnihilate j * fAnnihilate i = 0 := by
  apply LinearMap.ext
  intro x
  ext c
  simp only [LinearMap.add_apply, Module.End.mul_apply, fAnnihilate_apply, PiLp.add_apply,
    LinearMap.zero_apply, PiLp.zero_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp only [Function.update_of_ne (Ne.symm hij), Function.update_of_ne hij,
      Function.update_comm (β := fun _ => Fin 2) hij 1 1 c]
    rcases fin_two_cases (c i) with hi | hi <;> rcases fin_two_cases (c j) with hj | hj <;>
      simp only [hi, hj, ↓reduceIte, mul_zero, add_zero,
        show (1 : Fin 2) ≠ 0 by decide]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · rw [jwSign_update_of_lt hlt, jwSign_update_of_not_lt (not_lt.2 hlt.le), hi]
      simp [occParity]
      ring
    · rw [jwSign_update_of_not_lt (not_lt.2 hgt.le), jwSign_update_of_lt hgt, hj]
      simp [occParity]
      ring

/-- **`{a_i†, a_j†} = 0`.** -/
theorem fCreate_mul_fCreate_add (i j : Fin N) :
    fCreate i * fCreate j + fCreate j * fCreate i = 0 := by
  apply LinearMap.ext
  intro x
  ext c
  simp only [LinearMap.add_apply, Module.End.mul_apply, fCreate_apply, PiLp.add_apply,
    LinearMap.zero_apply, PiLp.zero_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp only [Function.update_of_ne (Ne.symm hij), Function.update_of_ne hij,
      Function.update_comm (β := fun _ => Fin 2) hij 0 0 c]
    rcases fin_two_cases (c i) with hi | hi <;> rcases fin_two_cases (c j) with hj | hj <;>
      simp only [hi, hj, ↓reduceIte, mul_zero, add_zero,
        show (0 : Fin 2) ≠ 1 by decide]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · rw [jwSign_update_of_lt hlt, jwSign_update_of_not_lt (not_lt.2 hlt.le), hi]
      simp [occParity]
      ring
    · rw [jwSign_update_of_not_lt (not_lt.2 hgt.le), jwSign_update_of_lt hgt, hj]
      simp [occParity]
      ring

/-! ### Jordan–Wigner -/

/-- `Z` on site `k` of the qubit chain. -/
noncomputable def qubitZ (k : Fin N) : Module.End ℂ (FieldSpace N 2) where
  toFun x := WithLp.toLp 2 fun c => occParity (c k) * x c
  map_add' x y := by ext c; simp [mul_add]
  map_smul' a x := by ext c; simp [mul_left_comm]

/-- The lowering operator `|0⟩⟨1|` on site `j` of the qubit chain. -/
noncomputable def qubitLower (j : Fin N) : Module.End ℂ (FieldSpace N 2) where
  toFun x := WithLp.toLp 2 fun c => if c j = 0 then x (Function.update c j 1) else 0
  map_add' x y := by
    ext c
    simp only [PiLp.add_apply]
    split_ifs <;> ring
  map_smul' a x := by
    ext c
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The Jordan–Wigner string of mode `j`: `Z` on every site before `j`. -/
noncomputable def jwString (j : Fin N) : Module.End ℂ (FieldSpace N 2) :=
  (((List.finRange N).filter (· < j)).map qubitZ).prod

theorem list_prod_qubitZ_apply (l : List (Fin N)) (x : FieldSpace N 2) (c : FieldConfig N 2) :
    (l.map qubitZ).prod x c = (l.map fun k => occParity (c k)).prod * x c := by
  induction l generalizing x with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [show qubitZ k ((l.map qubitZ).prod x) c = occParity (c k) * (l.map qubitZ).prod x c from rfl,
      ih, mul_assoc]

theorem jwString_apply (j : Fin N) (x : FieldSpace N 2) (c : FieldConfig N 2) :
    jwString j x c = jwSign c j * x c := by
  rw [jwString, list_prod_qubitZ_apply, jwSign,
    ← List.prod_toFinset _ ((List.nodup_finRange N).filter _)]
  congr 2
  ext k
  simp

/-- **Jordan–Wigner**: `a_j = Z_0 ⋯ Z_{j−1} σ⁻_j` on the qubit chain. -/
theorem fAnnihilate_eq_jwString_mul_qubitLower (j : Fin N) :
    fAnnihilate j = jwString j * qubitLower j := by
  apply LinearMap.ext
  intro x
  ext c
  rw [Module.End.mul_apply, jwString_apply, fAnnihilate_apply]
  show _ = jwSign c j * (if c j = 0 then x (Function.update c j 1) else 0)
  split_ifs <;> simp

/-! ### Number operators and the `n`-particle sectors -/

/-- The occupation of mode `j`, `a_j† a_j`. -/
noncomputable def fNumber (j : Fin N) : Module.End ℂ (FieldSpace N 2) := fCreate j * fAnnihilate j

theorem fNumber_apply (j : Fin N) (x : FieldSpace N 2) (c : FieldConfig N 2) :
    fNumber j x c = ((c j : ℕ) : ℂ) * x c := by
  rw [fNumber, Module.End.mul_apply, fCreate_apply]
  rcases fin_two_cases (c j) with h | h
  · simp [h]
  · simp only [h, ↓reduceIte, fAnnihilate_apply, Function.update_self, Function.update_idem,
      update_of_eq h, jwSign_update_of_not_lt (lt_irrefl j), ← mul_assoc, jwSign_mul_self]
    simp

/-- The total number operator `∑ a_j† a_j`. -/
noncomputable def fTotalNumber (N : ℕ) : Module.End ℂ (FieldSpace N 2) := ∑ j, fNumber j

/-- The number of particles in a configuration. -/
def occTotal (c : FieldConfig N 2) : ℕ := ∑ j, (c j : ℕ)

theorem fTotalNumber_apply (x : FieldSpace N 2) (c : FieldConfig N 2) :
    fTotalNumber N x c = (occTotal c : ℂ) * x c := by
  rw [fTotalNumber, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [fNumber_apply, occTotal, Nat.cast_sum, Finset.sum_mul]

/-- **The `n`-particle sector of the Fock space.** -/
abbrev fockSector (N n : ℕ) : Submodule ℂ (FieldSpace N 2) :=
  supportedOn fun c : FieldConfig N 2 => occTotal c = n

/-- The `n`-particle sector is the eigenspace of the total number with eigenvalue `n`. -/
theorem mem_fockSector_iff {n : ℕ} {x : FieldSpace N 2} :
    x ∈ fockSector N n ↔ fTotalNumber N x = (n : ℂ) • x := by
  constructor
  · intro hx
    ext c
    rw [fTotalNumber_apply, PiLp.smul_apply, smul_eq_mul]
    by_cases h : occTotal c = n
    · rw [h]
    · rw [hx c h, mul_zero, mul_zero]
  · intro hx c hc
    have := congrArg (fun y : FieldSpace N 2 => y c) hx
    simp only [fTotalNumber_apply, PiLp.smul_apply, smul_eq_mul] at this
    have hne : (occTotal c : ℂ) - n ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hc)
    have h0 : ((occTotal c : ℂ) - n) * x c = 0 := by linear_combination this
    exact (mul_eq_zero.1 h0).resolve_left hne

/-- **The Fock space is the direct sum of the `n`-particle sectors.** -/
theorem isInternal_fockSector : DirectSum.IsInternal (fockSector N) :=
  isInternal_supportedOn_fiber occTotal

/-! ### The identification with first quantisation -/

/-- The configuration occupying exactly the modes of `S`. -/
def occOfFinset (S : Finset (Fin N)) : FieldConfig N 2 := fun j => if j ∈ S then 1 else 0

theorem card_filter_eq_occTotal (c : FieldConfig N 2) :
    (Finset.univ.filter (c · = 1)).card = occTotal c := by
  rw [occTotal, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases fin_two_cases (c j) with h | h <;> simp [h]

theorem occTotal_occOfFinset (S : Finset (Fin N)) : occTotal (occOfFinset S) = S.card := by
  rw [← card_filter_eq_occTotal]
  congr 1
  ext j
  simp [occOfFinset]

/-- **Sets of `n` occupied modes are the `n`-particle configurations.** -/
def finsetEquivOcc (n N : ℕ) :
    {S : Finset (Fin N) // S.card = n} ≃ {c : FieldConfig N 2 // occTotal c = n} where
  toFun S := ⟨occOfFinset S.1, by rw [occTotal_occOfFinset, S.2]⟩
  invFun c := ⟨Finset.univ.filter (c.1 · = 1), (card_filter_eq_occTotal c.1).trans c.2⟩
  left_inv S := by
    apply Subtype.ext
    ext j
    simp [occOfFinset]
  right_inv c := by
    apply Subtype.ext
    funext j
    rcases fin_two_cases (c.1 j) with h | h <;> simp [occOfFinset, h]

/-- **The `n`-particle Fock sector is the `n`-fermion sector of first quantisation**: the
first-quantised amplitude on a strictly increasing configuration is the Fock amplitude on its set of
occupied modes. -/
noncomputable def fockFermionEquiv (n N : ℕ) : fockSector N n ≃ₗ[ℂ] nFermionSector n N :=
  (supportedOnEquiv _).trans ((LinearEquiv.funCongrLeft ℂ ℂ
    ((strictConfigEquivFinset n N).trans (finsetEquivOcc n N))).trans nFermionEquiv.symm)

theorem fockFermionEquiv_apply (n N : ℕ) (y : fockSector N n) (g : StrictConfig n N) :
    (fockFermionEquiv n N y : ManyParticle n N) g.1
      = (y : FieldSpace N 2) (occOfFinset (Finset.univ.image g.1)) := by
  rw [show (fockFermionEquiv n N y : ManyParticle n N) g.1 = nFermionEquiv (fockFermionEquiv n N y) g
    from rfl]
  unfold fockFermionEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- **`n` fermions in the Fock space span `N.choose n` dimensions.** -/
theorem finrank_fockSector (n : ℕ) : finrank ℂ (fockSector N n) = N.choose n := by
  rw [LinearEquiv.finrank_eq (fockFermionEquiv n N), finrank_nFermionSector]

/-- The fermionic Fock space of `N` modes has dimension `2^N`. -/
theorem finrank_fermionFock : finrank ℂ (FieldSpace N 2) = 2 ^ N := by
  rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end CSD.SigmaLayer
