/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.IdenticalParticles
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# SigmaLayer/ManyIdenticalParticles: the boson and fermion sectors of `n` identical particles

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #214, the `n`-particle generalisation of ~~#206~~ (`SigmaLayer/IdenticalParticles.lean`).

`n` particles in `N` modes live on `ManyParticle n N = EuclideanSpace ℂ (Fin n → Fin N)`, amplitudes
on configurations `c` (particle `k` in mode `c k`). A permutation `σ` of the particles acts by
`(permOp N σ x) c = x (c ∘ σ)`. The bosonic sector is fixed by every permutation; the fermionic
sector is multiplied by the sign.

## What is proved

* `permOp` — the permutation action, as a matrix on the configuration arena (`permMatrix`): a
  representation (`permOp_mul`, `permOp_one`) by unitaries (`inner_permOp`);
* `nBosonSector n N`, `nFermionSector n N`, with the pointwise forms `mem_nBosonSector_iff_apply`
  (`x (c ∘ σ) = x c`) and `mem_nFermionSector_iff_apply` (`x (c ∘ σ) = sign σ · x c`);
* `symmetrizer` `(1/n!) ∑ σ` and `antisymmetrizer` `(1/n!) ∑ sign σ · σ`, ★ `isProj_symmetrizer`
  and ★ `isProj_antisymmetrizer`: each is the projection onto its sector;
* ★★ `apply_eq_zero_of_not_injective` — **Pauli exclusion for `n` fermions**: a fermionic amplitude
  vanishes on every configuration with two particles in one mode;
* **the dimensions, by sorting.** A boson amplitude is fixed by its values on the sorted
  (monotone) configurations, a fermion amplitude by its values on the strictly increasing ones
  (`Tuple.sort`, `Tuple.comp_perm_comp_sort_eq_comp_sort`): ★★ `nBosonEquiv` and ★★
  `nFermionEquiv` are linear equivalences onto the functions on those configurations. Counting
  them — strictly increasing tuples are `n`-element subsets (`strictConfigEquivFinset`), monotone
  ones are strictly increasing ones shifted by their position (`monoStrictEquiv`, stars and bars)
  — gives ★★★ `finrank_nBosonSector` (`(N + n − 1).choose n`) and ★★★ `finrank_nFermionSector`
  (`N.choose n`), and ★★ `finrank_nBosonSector_eq_card` / ★★ `finrank_nFermionSector_eq_card`:
  **one dimension per occupation configuration** (`P : Fin N → ℕ` with `∑ P = n` for bosons, the
  set of `n` occupied modes for fermions);
* ★ `nBosonSector_orthogonal` — for `n ≥ 2` a boson and a fermion are orthogonal; ★
  `sectors_not_exhaustive` — for `n = 3`, `N = 2` the two sectors have dimensions `4 + 0 < 8`:
  beyond two particles the boson and fermion sectors do **not** fill the space;
* `slater φ`, the Slater determinant of `n` orbitals: ★★ `slater_mem_nFermionSector`, ★★
  `slater_eq_factorial_smul_antisymmetrizer` (**it is the antisymmetrised product**, up to `n!`),
  ★★ `slater_eq_zero_of_not_linearIndependent` (dependent orbitals give no state);
* on the configuration arena: `IsPermSymmetric` (commutes with every permutation matrix), ★
  `isPermSymmetric_tensorPow` (the same unitary on every particle), `IsPermSymmetric.exp_smul`,
  ★★ `IsPermSymmetric.mem_nBosonSector` / `mem_nFermionSector` (**the sectors are invariant**) and
  ★★ `IsPermSymmetric.inner_eq_zero` (**superselection**, `n ≥ 2`);
* ★★★ `many_identical_particles` — the capstone.

## Honest scope

⚠️ **Consistency, not derivation**, as in ~~#206~~: the sectors are invariant and superselected
under permutation-symmetric dynamics; that nature uses only these two, and which for which particle,
is not proved here: the `±1` dichotomy for states whose ray every permutation keeps is ~~#216~~
(`SigmaLayer/ExchangeStatistics.lean`); which sign for which particle is BACKLOG #218.

⚠️ **The converse of `slater_eq_zero_of_not_linearIndependent`** — independent orbitals give a
nonzero Slater determinant — needs a nonzero `n × n` minor of an `N × n` matrix of rank `n`
(Cauchy–Binet); it is BACKLOG #217.

⚠️ **The other sectors.** For `n ≥ 3` the permutation action has components of mixed symmetry
(`sectors_not_exhaustive`); they carry parastatistics and are not studied here (BACKLOG #219).

The `n = 2` case is ~~#206~~ on the pair arena `Fin N × Fin N`; here the arena is `Fin 2 → Fin N`,
and the two dimension formulas agree (`(N + 1).choose 2`, `N.choose 2`).

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/IdenticalParticles.lean`
(`bosonSector`, `fermionSector`, `wedge`); `SigmaLayer/Symmetrization.lean`; Mathlib `Tuple.sort`,
`Finset.orderEmbOfFin`, `Sym.equivNatSumOfFintype`, `Matrix.det_permute`,
`Matrix.exists_mulVec_eq_zero_iff`; `specs/BACKLOG.md` #214.
-/

@[expose] public section

open Module Matrix NormedSpace
open scoped InnerProductSpace

namespace CSD.SigmaLayer

variable {n N : ℕ}

/-! ### The arena and the permutation action -/

/-- A configuration of `n` particles in `N` modes: particle `k` is in mode `c k`. -/
abbrev ManyConfig (n N : ℕ) : Type := Fin n → Fin N

/-- The `n`-particle Hilbert space `(ℂᴺ)^{⊗ n}`, as amplitudes on configurations. -/
abbrev ManyParticle (n N : ℕ) : Type := EuclideanSpace ℂ (ManyConfig n N)

/-- Relabelling the particles of a configuration by `σ`. -/
def permConfig (N : ℕ) (σ : Equiv.Perm (Fin n)) : ManyConfig n N ≃ ManyConfig n N where
  toFun c := c ∘ σ
  invFun c := c ∘ σ.symm
  left_inv c := by funext i; simp
  right_inv c := by funext i; simp

/-- **The permutation matrix** of `σ` on the configuration arena. -/
noncomputable def permMatrix (N : ℕ) (σ : Equiv.Perm (Fin n)) :
    Matrix (ManyConfig n N) (ManyConfig n N) ℂ :=
  (permConfig N σ).toPEquiv.toMatrix

/-- **The permutation action** of `σ` on `n`-particle states. -/
noncomputable def permOp (N : ℕ) (σ : Equiv.Perm (Fin n)) : ManyParticle n N →ₗ[ℂ] ManyParticle n N :=
  toEuclideanLin (permMatrix N σ)

theorem permOp_apply (σ : Equiv.Perm (Fin n)) (x : ManyParticle n N) (c : ManyConfig n N) :
    permOp N σ x c = x (c ∘ σ) := by
  simp [permOp, permMatrix, Matrix.toLpLin_apply, PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

theorem permOp_mul (τ σ : Equiv.Perm (Fin n)) (x : ManyParticle n N) :
    permOp N (τ * σ) x = permOp N τ (permOp N σ x) := by
  ext c
  simp only [permOp_apply]
  rfl

theorem permOp_one (x : ManyParticle n N) : permOp N 1 x = x := by
  ext c
  rw [permOp_apply]
  rfl

/-- The permutation action is unitary. -/
theorem inner_permOp (σ : Equiv.Perm (Fin n)) (x y : ManyParticle n N) :
    ⟪permOp N σ x, permOp N σ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [PiLp.inner_apply, permOp_apply]
  exact Fintype.sum_equiv (permConfig N σ) _ _ fun _ => rfl

/-- The sign of a permutation, as a complex number. -/
def permSign (σ : Equiv.Perm (Fin n)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

theorem permSign_mul (σ τ : Equiv.Perm (Fin n)) :
    permSign (σ * τ) = permSign σ * permSign τ := by
  simp [permSign, Equiv.Perm.sign_mul]

theorem permSign_inv (σ : Equiv.Perm (Fin n)) : permSign σ⁻¹ = permSign σ := by
  simp [permSign]

theorem permSign_one : permSign (1 : Equiv.Perm (Fin n)) = 1 := by
  simp [permSign]

theorem permSign_mul_self (σ : Equiv.Perm (Fin n)) : permSign σ * permSign σ = 1 := by
  rw [← permSign_mul]
  simp only [permSign, Equiv.Perm.sign_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-! ### The two sectors -/

/-- **The `n`-boson sector**: the states fixed by every permutation of the particles. -/
noncomputable def nBosonSector (n N : ℕ) : Submodule ℂ (ManyParticle n N) :=
  ⨅ σ : Equiv.Perm (Fin n), LinearMap.ker (permOp N σ - LinearMap.id)

/-- **The `n`-fermion sector**: the states each permutation multiplies by its sign. -/
noncomputable def nFermionSector (n N : ℕ) : Submodule ℂ (ManyParticle n N) :=
  ⨅ σ : Equiv.Perm (Fin n), LinearMap.ker (permOp N σ - permSign σ • LinearMap.id)

theorem mem_nBosonSector {x : ManyParticle n N} :
    x ∈ nBosonSector n N ↔ ∀ σ, permOp N σ x = x := by
  simp [nBosonSector, sub_eq_zero]

theorem mem_nFermionSector {x : ManyParticle n N} :
    x ∈ nFermionSector n N ↔ ∀ σ, permOp N σ x = permSign σ • x := by
  simp [nFermionSector, sub_eq_zero]

theorem mem_nBosonSector_iff_apply {x : ManyParticle n N} :
    x ∈ nBosonSector n N ↔ ∀ (σ : Equiv.Perm (Fin n)) c, x (c ∘ σ) = x c := by
  rw [mem_nBosonSector]
  constructor
  · intro h σ c
    have := congrArg (fun y : ManyParticle n N => y c) (h σ)
    simpa [permOp_apply] using this
  · intro h σ
    ext c
    rw [permOp_apply]
    exact h σ c

theorem mem_nFermionSector_iff_apply {x : ManyParticle n N} :
    x ∈ nFermionSector n N ↔ ∀ (σ : Equiv.Perm (Fin n)) c, x (c ∘ σ) = permSign σ * x c := by
  rw [mem_nFermionSector]
  constructor
  · intro h σ c
    have := congrArg (fun y : ManyParticle n N => y c) (h σ)
    simpa [permOp_apply] using this
  · intro h σ
    ext c
    rw [permOp_apply, PiLp.smul_apply, smul_eq_mul]
    exact h σ c

/-! ### The projectors -/

/-- **The symmetriser** `(1/n!) ∑ σ`. -/
noncomputable def symmetrizer (n N : ℕ) : ManyParticle n N →ₗ[ℂ] ManyParticle n N :=
  ((n.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permOp N σ

/-- **The antisymmetriser** `(1/n!) ∑ sign σ · σ`. -/
noncomputable def antisymmetrizer (n N : ℕ) : ManyParticle n N →ₗ[ℂ] ManyParticle n N :=
  ((n.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permSign σ • permOp N σ

theorem symmetrizer_apply (x : ManyParticle n N) :
    symmetrizer n N x = ((n.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permOp N σ x := by
  simp [symmetrizer]

theorem antisymmetrizer_apply (x : ManyParticle n N) :
    antisymmetrizer n N x
      = ((n.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permSign σ • permOp N σ x := by
  simp [antisymmetrizer]

theorem permOp_symmetrizer (τ : Equiv.Perm (Fin n)) (x : ManyParticle n N) :
    permOp N τ (symmetrizer n N x) = symmetrizer n N x := by
  rw [symmetrizer_apply, map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => (permOp_mul τ σ x).symm

theorem permOp_antisymmetrizer (τ : Equiv.Perm (Fin n)) (x : ManyParticle n N) :
    permOp N τ (antisymmetrizer n N x) = permSign τ • antisymmetrizer n N x := by
  rw [antisymmetrizer_apply, map_smul, map_sum, smul_comm (permSign τ)]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  show permOp N τ (permSign σ • permOp N σ x) = permSign τ • permSign (τ * σ) • permOp N (τ * σ) x
  rw [map_smul, ← permOp_mul, smul_smul, permSign_mul, ← mul_assoc, permSign_mul_self, one_mul]

theorem factorial_inv_smul_card_smul (x : ManyParticle n N) :
    ((n.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin n), x = x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), one_smul]

/-- The symmetriser is the projection onto the boson sector. -/
theorem isProj_symmetrizer : LinearMap.IsProj (nBosonSector n N) (symmetrizer n N) :=
  ⟨fun x => mem_nBosonSector.2 fun τ => permOp_symmetrizer τ x, fun x hx => by
    rw [symmetrizer_apply]
    simp only [mem_nBosonSector.1 hx]
    exact factorial_inv_smul_card_smul x⟩

/-- The antisymmetriser is the projection onto the fermion sector. -/
theorem isProj_antisymmetrizer : LinearMap.IsProj (nFermionSector n N) (antisymmetrizer n N) :=
  ⟨fun x => mem_nFermionSector.2 fun τ => permOp_antisymmetrizer τ x, fun x hx => by
    rw [antisymmetrizer_apply]
    simp only [mem_nFermionSector.1 hx, smul_smul, permSign_mul_self, one_smul]
    exact factorial_inv_smul_card_smul x⟩

/-! ### Pauli exclusion for `n` fermions -/

/-- **Pauli exclusion for `n` fermions.** A fermionic amplitude vanishes on every configuration that
puts two particles in one mode. -/
theorem apply_eq_zero_of_not_injective {x : ManyParticle n N} (hx : x ∈ nFermionSector n N)
    {c : ManyConfig n N} (hc : ¬ Function.Injective c) : x c = 0 := by
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  have hcs : c ∘ Equiv.swap i j = c := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hij]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := mem_nFermionSector_iff_apply.1 hx (Equiv.swap i j) c
  rw [hcs, permSign, Equiv.Perm.sign_swap hne] at h
  push_cast at h
  have h2 : (2 : ℂ) * x c = 0 := by linear_combination h
  simpa using h2

/-! ### Sorted configurations -/

/-- The monotone (sorted) configurations: one per boson orbit. -/
abbrev MonoConfig (n N : ℕ) : Type := {c : ManyConfig n N // Monotone c}

/-- The strictly increasing configurations: one per fermion orbit with no repeated mode. -/
abbrev StrictConfig (n N : ℕ) : Type := {c : ManyConfig n N // StrictMono c}

theorem strictMono_comp_sort {c : ManyConfig n N} (hc : Function.Injective c) :
    StrictMono (c ∘ Tuple.sort c) :=
  (Tuple.monotone_sort c).strictMono_of_injective (hc.comp (Tuple.sort c).injective)

theorem sort_comp_perm {c : ManyConfig n N} (hc : Function.Injective c)
    (σ : Equiv.Perm (Fin n)) : Tuple.sort (c ∘ σ) = σ⁻¹ * Tuple.sort c := by
  have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := c) (σ := σ)
  have h2 : ⇑σ ∘ ⇑(Tuple.sort (c ∘ σ)) = ⇑(Tuple.sort c) := hc.comp_left h
  rw [eq_inv_mul_iff_mul_eq]
  exact DFunLike.coe_injective (by rw [Equiv.Perm.coe_mul]; exact h2)

/-- Extend a function on sorted configurations to a boson amplitude. -/
noncomputable def bosonExtend (f : MonoConfig n N → ℂ) (c : ManyConfig n N) : ℂ :=
  f ⟨c ∘ Tuple.sort c, Tuple.monotone_sort c⟩

theorem bosonExtend_comp (f : MonoConfig n N → ℂ) (σ : Equiv.Perm (Fin n)) (c : ManyConfig n N) :
    bosonExtend f (c ∘ σ) = bosonExtend f c :=
  congrArg f (Subtype.ext Tuple.comp_perm_comp_sort_eq_comp_sort)

theorem bosonExtend_mono (f : MonoConfig n N → ℂ) (m : MonoConfig n N) :
    bosonExtend f m.1 = f m := by
  have hs : Tuple.sort m.1 = 1 := Tuple.sort_eq_refl_iff_monotone.2 m.2
  refine congrArg f (Subtype.ext ?_)
  show m.1 ∘ Tuple.sort m.1 = m.1
  rw [hs]
  rfl

open scoped Classical in
/-- Extend a function on strictly increasing configurations to a fermion amplitude. -/
noncomputable def fermionExtend (f : StrictConfig n N → ℂ) (c : ManyConfig n N) : ℂ :=
  if h : Function.Injective c then
    permSign (Tuple.sort c) * f ⟨c ∘ Tuple.sort c, strictMono_comp_sort h⟩
  else 0

theorem fermionExtend_comp (f : StrictConfig n N → ℂ) (σ : Equiv.Perm (Fin n))
    (c : ManyConfig n N) : fermionExtend f (c ∘ σ) = permSign σ * fermionExtend f c := by
  by_cases hc : Function.Injective c
  · have hcσ : Function.Injective (c ∘ σ) := hc.comp σ.injective
    have hsub : (⟨(c ∘ σ) ∘ Tuple.sort (c ∘ σ), strictMono_comp_sort hcσ⟩ : StrictConfig n N)
        = ⟨c ∘ Tuple.sort c, strictMono_comp_sort hc⟩ :=
      Subtype.ext Tuple.comp_perm_comp_sort_eq_comp_sort
    simp only [fermionExtend, hcσ, hc, ↓reduceDIte]
    rw [hsub, sort_comp_perm hc σ, permSign_mul, permSign_inv]
    ring
  · have hcσ : ¬ Function.Injective (c ∘ σ) := fun h => hc (by
      have := h.comp σ.symm.injective
      simpa [Function.comp_assoc] using this)
    simp only [fermionExtend, hcσ, hc, ↓reduceDIte, mul_zero]

theorem fermionExtend_strictMono (f : StrictConfig n N → ℂ) (m : StrictConfig n N) :
    fermionExtend f m.1 = f m := by
  have hs : Tuple.sort m.1 = 1 := Tuple.sort_eq_refl_iff_monotone.2 m.2.monotone
  have hsub : (⟨m.1 ∘ Tuple.sort m.1, strictMono_comp_sort m.2.injective⟩ : StrictConfig n N)
      = m := Subtype.ext (by
    show m.1 ∘ Tuple.sort m.1 = m.1
    rw [hs]
    rfl)
  simp only [fermionExtend, m.2.injective, ↓reduceDIte]
  rw [hsub, hs, permSign_one, one_mul]

theorem fermionExtend_restrict {x : ManyParticle n N} (hx : x ∈ nFermionSector n N)
    (c : ManyConfig n N) : fermionExtend (fun m : StrictConfig n N => x m.1) c = x c := by
  unfold fermionExtend
  split_ifs with h
  · dsimp only
    rw [mem_nFermionSector_iff_apply.1 hx, ← mul_assoc, permSign_mul_self, one_mul]
  · exact (apply_eq_zero_of_not_injective hx h).symm

/-- **A boson is its values on the sorted configurations.** -/
noncomputable def nBosonEquiv : nBosonSector n N ≃ₗ[ℂ] (MonoConfig n N → ℂ) where
  toFun x m := (x : ManyParticle n N) m.1
  map_add' x y := by funext m; simp
  map_smul' a x := by funext m; simp
  invFun f := ⟨WithLp.toLp 2 (bosonExtend f),
    mem_nBosonSector_iff_apply.2 fun σ c => bosonExtend_comp f σ c⟩
  left_inv x := Subtype.ext (by
    ext c
    exact mem_nBosonSector_iff_apply.1 x.2 (Tuple.sort c) c)
  right_inv f := funext fun m => bosonExtend_mono f m

/-- **A fermion is its values on the strictly increasing configurations.** -/
noncomputable def nFermionEquiv : nFermionSector n N ≃ₗ[ℂ] (StrictConfig n N → ℂ) where
  toFun x m := (x : ManyParticle n N) m.1
  map_add' x y := by funext m; simp
  map_smul' a x := by funext m; simp
  invFun f := ⟨WithLp.toLp 2 (fermionExtend f),
    mem_nFermionSector_iff_apply.2 fun σ c => fermionExtend_comp f σ c⟩
  left_inv x := Subtype.ext (by
    ext c
    exact fermionExtend_restrict x.2 c)
  right_inv f := funext fun m => fermionExtend_strictMono f m

/-! ### Counting sorted configurations -/

/-- **Strictly increasing tuples are subsets**: `c ↦ image c`, inverted by `Finset.orderEmbOfFin`. -/
noncomputable def strictConfigEquivFinset (n M : ℕ) :
    StrictConfig n M ≃ {s : Finset (Fin M) // s.card = n} where
  toFun c := ⟨Finset.univ.image c.1, by
    rw [Finset.card_image_of_injective _ c.2.injective, Finset.card_univ, Fintype.card_fin]⟩
  invFun s := ⟨Finset.orderEmbOfFin s.1 s.2, (Finset.orderEmbOfFin s.1 s.2).strictMono⟩
  left_inv c := Subtype.ext (Finset.orderEmbOfFin_unique _
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) c.2).symm
  right_inv s := Subtype.ext (Finset.coe_injective (by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]))

/-- A strictly increasing tuple gains at least one per step. -/
theorem add_sub_le_of_strictMono {M : ℕ} {d : Fin n → Fin M} (hd : StrictMono d) {i j : Fin n}
    (hij : i ≤ j) : (d i : ℕ) + ((j : ℕ) - i) ≤ d j := by
  suffices H : ∀ k (i j : Fin n), (j : ℕ) = i + k → (d i : ℕ) + k ≤ d j by
    rw [Fin.le_iff_val_le_val] at hij
    exact H _ i j (by omega)
  intro k
  induction k with
  | zero =>
    intro i j h
    rw [show j = i from Fin.ext (by omega)]
    simp
  | succ k ih =>
    intro i j h
    have hk : (i : ℕ) + k < n := by omega
    have h1 := ih i ⟨i + k, hk⟩ rfl
    have h2 : (d ⟨i + k, hk⟩ : ℕ) < d j :=
      Fin.lt_def.1 (hd (Fin.lt_def.2 (by simp only; omega)))
    omega

/-- **Stars and bars**: monotone tuples `Fin n → Fin N` are strictly increasing tuples
`Fin n → Fin (N + n − 1)`, by adding the position. -/
noncomputable def monoStrictEquiv (n N : ℕ) : MonoConfig n N ≃ StrictConfig n (N + n - 1) where
  toFun c := ⟨fun i => ⟨c.1 i + i, by have := (c.1 i).isLt; have := i.isLt; omega⟩,
    fun i j hij => by
      rw [Fin.lt_def] at hij ⊢
      have := Fin.le_iff_val_le_val.1 (c.2 (Fin.le_iff_val_le_val.2 hij.le))
      simp only
      omega⟩
  invFun d := ⟨fun i => ⟨d.1 i - i, by
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
      have h1 := add_sub_le_of_strictMono d.2 (i := i) (j := ⟨n - 1, by omega⟩)
        (Fin.le_iff_val_le_val.2 (by simp only; omega))
      have h0 := add_sub_le_of_strictMono d.2 (i := ⟨0, hn⟩) (j := i)
        (Fin.le_iff_val_le_val.2 (by simp only; omega))
      have h3 := (d.1 ⟨n - 1, by omega⟩).isLt
      have := i.isLt
      simp only at h1 h0
      omega⟩,
    fun i j hij => by
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
      have h1 := add_sub_le_of_strictMono d.2 hij
      have h0 := add_sub_le_of_strictMono d.2 (i := ⟨0, hn⟩) (j := i)
        (Fin.le_iff_val_le_val.2 (by simp only; omega))
      rw [Fin.le_iff_val_le_val] at hij ⊢
      simp only at h0 ⊢
      omega⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp
  right_inv d := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have h0 := add_sub_le_of_strictMono d.2 (i := ⟨0, hn⟩) (j := i)
      (Fin.le_iff_val_le_val.2 (by simp only; omega))
    simp only at h0 ⊢
    omega

/-- **`n` fermions in `N` modes span `N.choose n` dimensions.** -/
theorem finrank_nFermionSector : finrank ℂ (nFermionSector n N) = N.choose n := by
  classical
  rw [LinearEquiv.finrank_eq nFermionEquiv, Module.finrank_fintype_fun_eq_card,
    Fintype.card_congr (strictConfigEquivFinset n N), Fintype.card_finset_len, Fintype.card_fin]

/-- **`n` bosons in `N` modes span `(N + n − 1).choose n` dimensions.** -/
theorem finrank_nBosonSector : finrank ℂ (nBosonSector n N) = (N + n - 1).choose n := by
  classical
  rw [LinearEquiv.finrank_eq nBosonEquiv, Module.finrank_fintype_fun_eq_card,
    Fintype.card_congr (monoStrictEquiv n N), Fintype.card_congr (strictConfigEquivFinset n _),
    Fintype.card_finset_len, Fintype.card_fin]

/-- **One bosonic dimension per occupation configuration**: as many as ways to put `n` quanta into
`N` modes. -/
theorem finrank_nBosonSector_eq_card :
    finrank ℂ (nBosonSector n N) = Nat.card {P : Fin N → ℕ // ∑ i, P i = n} := by
  rw [finrank_nBosonSector, ← Nat.card_congr (Sym.equivNatSumOfFintype (Fin N) n),
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]

/-- **One fermionic dimension per set of `n` occupied modes.** -/
theorem finrank_nFermionSector_eq_card :
    finrank ℂ (nFermionSector n N) = Fintype.card {s : Finset (Fin N) // s.card = n} := by
  rw [finrank_nFermionSector, Fintype.card_finset_len, Fintype.card_fin]

/-- **Beyond two particles the two sectors do not fill the space**: three particles in two modes have
a four-dimensional boson sector, no fermion sector, and an eight-dimensional space. -/
theorem sectors_not_exhaustive :
    finrank ℂ (nBosonSector 3 2) + finrank ℂ (nFermionSector 3 2)
      < finrank ℂ (ManyParticle 3 2) := by
  rw [finrank_nBosonSector, finrank_nFermionSector, finrank_euclideanSpace]
  simp [Nat.choose]

/-- For `n ≥ 2` a boson and a fermion are orthogonal. -/
theorem inner_eq_zero_of_mem_nBosonSector (hn : 2 ≤ n) {x y : ManyParticle n N}
    (hx : x ∈ nBosonSector n N) (hy : y ∈ nFermionSector n N) : ⟪x, y⟫_ℂ = 0 := by
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h := inner_permOp (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) x y
  rw [mem_nBosonSector.1 hx, mem_nFermionSector.1 hy, inner_smul_right, permSign,
    Equiv.Perm.sign_swap hne] at h
  push_cast at h
  have h2 : (2 : ℂ) * ⟪x, y⟫_ℂ = 0 := by linear_combination -h
  simpa using h2

theorem nBosonSector_orthogonal (hn : 2 ≤ n) : nBosonSector n N ⟂ nFermionSector n N :=
  Submodule.isOrtho_iff_inner_eq.2 fun _ hx _ hy => inner_eq_zero_of_mem_nBosonSector hn hx hy

/-! ### Slater determinants -/

/-- The product state of `n` orbitals, particle `k` in orbital `φ k`. -/
noncomputable def prodState (φ : Fin n → EuclideanSpace ℂ (Fin N)) : ManyParticle n N :=
  WithLp.toLp 2 (fun c => ∏ k, φ k (c k))

/-- The `n × n` matrix of the orbitals evaluated at a configuration: row `i` is particle `i`. -/
noncomputable def slaterMatrix (φ : Fin n → EuclideanSpace ℂ (Fin N)) (c : ManyConfig n N) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => φ k (c i)

/-- **The Slater determinant** of `n` orbitals. -/
noncomputable def slater (φ : Fin n → EuclideanSpace ℂ (Fin N)) : ManyParticle n N :=
  WithLp.toLp 2 (fun c => (slaterMatrix φ c).det)

theorem slater_apply (φ : Fin n → EuclideanSpace ℂ (Fin N)) (c : ManyConfig n N) :
    slater φ c = (slaterMatrix φ c).det := rfl

/-- The Slater determinant is a fermion. -/
theorem slater_mem_nFermionSector (φ : Fin n → EuclideanSpace ℂ (Fin N)) :
    slater φ ∈ nFermionSector n N :=
  mem_nFermionSector_iff_apply.2 fun σ c => by
    rw [slater_apply, slater_apply,
      show slaterMatrix φ (c ∘ σ) = (slaterMatrix φ c).submatrix σ id from rfl,
      Matrix.det_permute]
    rfl

/-- **The Slater determinant is the antisymmetrised product state**, up to `n!`. -/
theorem slater_eq_factorial_smul_antisymmetrizer (φ : Fin n → EuclideanSpace ℂ (Fin N)) :
    slater φ = (n.factorial : ℂ) • antisymmetrizer n N (prodState φ) := by
  rw [antisymmetrizer_apply, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), one_smul]
  ext c
  rw [slater_apply, Matrix.det_apply', WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [PiLp.smul_apply, permOp_apply, smul_eq_mul]
  rfl

/-- **Dependent orbitals give no state**: the Slater determinant of linearly dependent orbitals is
zero. -/
theorem slater_eq_zero_of_not_linearIndependent {φ : Fin n → EuclideanSpace ℂ (Fin N)}
    (h : ¬ LinearIndependent ℂ φ) : slater φ = 0 := by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 h
  ext c
  rw [slater_apply, PiLp.zero_apply, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨g, fun h0 => hi (by rw [h0]; rfl), ?_⟩
  funext j
  have := congrArg (fun v : EuclideanSpace ℂ (Fin N) => v (c j)) hg
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.zero_apply] at this
  simp only [Matrix.mulVec, dotProduct, slaterMatrix, Matrix.of_apply, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### Sector restriction on the configuration arena -/

/-- **An operator of `n` identical particles**: one that commutes with every permutation. -/
def IsPermSymmetric (M : Matrix (ManyConfig n N) (ManyConfig n N) ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), Commute (permMatrix N σ) M

/-- The `n`-fold tensor power of a single-particle operator. -/
noncomputable def tensorPow (n : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (ManyConfig n N) (ManyConfig n N) ℂ :=
  Matrix.of fun c c' => ∏ k, U (c k) (c' k)

/-- The same operation applied to every particle is permutation-symmetric. -/
theorem isPermSymmetric_tensorPow (U : Matrix (Fin N) (Fin N) ℂ) :
    IsPermSymmetric (tensorPow n U) := by
  intro σ
  show permMatrix N σ * _ = _ * permMatrix N σ
  rw [permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext c c'
  simp only [Matrix.submatrix_apply, tensorPow, Matrix.of_apply, id]
  show ∏ k, U (c (σ k)) (c' k) = ∏ k, U (c k) (c' (σ.symm k))
  rw [← Equiv.prod_comp σ (fun j => U (c j) (c' (σ.symm j)))]
  simp

theorem IsPermSymmetric.exp_smul {H : Matrix (ManyConfig n N) (ManyConfig n N) ℂ}
    (hH : IsPermSymmetric H) (t : ℂ) : IsPermSymmetric (exp (t • H)) := fun σ =>
  ((hH σ).smul_right t).exp_right

theorem IsPermSymmetric.permOp_toEuclideanLin {M : Matrix (ManyConfig n N) (ManyConfig n N) ℂ}
    (hM : IsPermSymmetric M) (σ : Equiv.Perm (Fin n)) (x : ManyParticle n N) :
    permOp N σ (toEuclideanLin M x) = toEuclideanLin M (permOp N σ x) := by
  have := congrArg (fun A => toEuclideanLin A x) (hM σ).eq
  simpa [Matrix.toLpLin_mul_same, permOp] using this

/-- **The boson sector is invariant** under every permutation-symmetric operator. -/
theorem IsPermSymmetric.mem_nBosonSector {M : Matrix (ManyConfig n N) (ManyConfig n N) ℂ}
    (hM : IsPermSymmetric M) {x : ManyParticle n N} (hx : x ∈ nBosonSector n N) :
    toEuclideanLin M x ∈ nBosonSector n N := by
  rw [SigmaLayer.mem_nBosonSector] at hx ⊢
  intro σ
  rw [hM.permOp_toEuclideanLin, hx σ]

/-- **The fermion sector is invariant** under every permutation-symmetric operator. -/
theorem IsPermSymmetric.mem_nFermionSector {M : Matrix (ManyConfig n N) (ManyConfig n N) ℂ}
    (hM : IsPermSymmetric M) {x : ManyParticle n N} (hx : x ∈ nFermionSector n N) :
    toEuclideanLin M x ∈ nFermionSector n N := by
  rw [SigmaLayer.mem_nFermionSector] at hx ⊢
  intro σ
  rw [hM.permOp_toEuclideanLin, hx σ, map_smul]

/-- **Superselection for `n ≥ 2`.** No permutation-symmetric operator connects a boson to a
fermion. -/
theorem IsPermSymmetric.inner_eq_zero {M : Matrix (ManyConfig n N) (ManyConfig n N) ℂ}
    (hM : IsPermSymmetric M) (hn : 2 ≤ n) {x y : ManyParticle n N} (hx : x ∈ nBosonSector n N)
    (hy : y ∈ nFermionSector n N) : ⟪x, toEuclideanLin M y⟫_ℂ = 0 :=
  inner_eq_zero_of_mem_nBosonSector hn hx (hM.mem_nFermionSector hy)

/-! ### The capstone -/

/-- **`n` identical particles.**

1. the boson and fermion sectors have dimensions `(N + n − 1).choose n` and `N.choose n`, one per
   occupation configuration;
2. the symmetriser and antisymmetriser are the projections onto them;
3. Pauli exclusion: a fermion amplitude vanishes on every configuration with a repeated mode;
4. the Slater determinant is a fermion, the antisymmetrised product up to `n!`, and zero for
   dependent orbitals;
5. every evolution generated by a permutation-symmetric operator keeps each sector;
6. for `n ≥ 2`, no permutation-symmetric operator connects a boson to a fermion;
7. for three particles in two modes the two sectors do not fill the space. -/
theorem many_identical_particles :
    (finrank ℂ (nBosonSector n N) = (N + n - 1).choose n
        ∧ finrank ℂ (nBosonSector n N) = Nat.card {P : Fin N → ℕ // ∑ i, P i = n}
        ∧ finrank ℂ (nFermionSector n N) = N.choose n
        ∧ finrank ℂ (nFermionSector n N) = Fintype.card {s : Finset (Fin N) // s.card = n})
    ∧ (LinearMap.IsProj (nBosonSector n N) (symmetrizer n N)
        ∧ LinearMap.IsProj (nFermionSector n N) (antisymmetrizer n N))
    ∧ (∀ x ∈ nFermionSector n N, ∀ c : ManyConfig n N, ¬ Function.Injective c → x c = 0)
    ∧ (∀ φ : Fin n → EuclideanSpace ℂ (Fin N), slater φ ∈ nFermionSector n N
        ∧ slater φ = (n.factorial : ℂ) • antisymmetrizer n N (prodState φ)
        ∧ (¬ LinearIndependent ℂ φ → slater φ = 0))
    ∧ (∀ H : Matrix (ManyConfig n N) (ManyConfig n N) ℂ, IsPermSymmetric H → ∀ t : ℂ,
        (∀ x ∈ nBosonSector n N, toEuclideanLin (exp (t • H)) x ∈ nBosonSector n N)
        ∧ ∀ x ∈ nFermionSector n N, toEuclideanLin (exp (t • H)) x ∈ nFermionSector n N)
    ∧ (2 ≤ n → ∀ M : Matrix (ManyConfig n N) (ManyConfig n N) ℂ, IsPermSymmetric M →
        ∀ x ∈ nBosonSector n N, ∀ y ∈ nFermionSector n N, ⟪x, toEuclideanLin M y⟫_ℂ = 0)
    ∧ finrank ℂ (nBosonSector 3 2) + finrank ℂ (nFermionSector 3 2)
        < finrank ℂ (ManyParticle 3 2) :=
  ⟨⟨finrank_nBosonSector, finrank_nBosonSector_eq_card, finrank_nFermionSector,
      finrank_nFermionSector_eq_card⟩,
    ⟨isProj_symmetrizer, isProj_antisymmetrizer⟩,
    fun _ hx _ hc => apply_eq_zero_of_not_injective hx hc,
    fun φ => ⟨slater_mem_nFermionSector φ, slater_eq_factorial_smul_antisymmetrizer φ,
      slater_eq_zero_of_not_linearIndependent⟩,
    fun _ hH t => ⟨fun _ hx => (hH.exp_smul t).mem_nBosonSector hx,
      fun _ hx => (hH.exp_smul t).mem_nFermionSector hx⟩,
    fun hn _ hM _ hx _ hy => hM.inner_eq_zero hn hx hy,
    sectors_not_exhaustive⟩

end CSD.SigmaLayer
