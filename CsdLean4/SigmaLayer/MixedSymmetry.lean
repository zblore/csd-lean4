/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ExchangeStatistics

/-!
# SigmaLayer/MixedSymmetry: the mixed-symmetry sectors

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #219, after ~~#214~~ (`sectors_not_exhaustive`) and ~~#216~~ (`IsExchangeEigenstate`).

For `n ≥ 3` particles the boson and fermion sectors do not fill `(ℂᴺ)^{⊗n}` (~~#214~~), and the
remainder holds no state whose ray every permutation keeps (~~#216~~). This module describes the
remainder: the **mixed-symmetry sector**, the states with no boson and no fermion component. The
symmetrisation postulate is the statement that physical states never live there.

## What is proved

For every `n`:

* `inner_symmetrizer_left`, `inner_antisymmetrizer_left` — the two projectors are self-adjoint, so
  `ker_symmetrizer`, `ker_antisymmetrizer` — their kernels are the orthogonal complements;
* `mixedSector n N` (the common kernel), ★★ `mixedSector_eq_orthogonal` — **it is everything
  orthogonal to the bosons and the fermions**; ★★ `finrank_mixedSector_add` —
  **`N^n = C(N+n−1, n) + C(N, n) + dim(mixed)`** for `n ≥ 2`;
* `permOp_mem_mixedSector`, ★★ `map_mem_mixedSector` — **relabelling the particles, and every
  permutation-symmetric operator, keep the mixed sector**: an evolution operator commuting with
  every relabelling neither enters nor leaves it;
* `eq_zero_of_mem_mixedSector_of_isExchangeEigenstate` — no nonzero mixed state is an exchange
  eigenstate.

For three particles, explicitly:

* `sum_perm_fin_three`, `symmetrizer_three`, `antisymmetrizer_three` — the six relabellings;
* ★★ `mem_mixedSector_three_iff` — **the mixed sector is exactly where the cyclic average
  vanishes**, `x + C x + C² x = 0`; `sum_swaps_eq_zero_of_mem_mixedSector` — there the three transpositions sum
  to zero (the character of the two-dimensional representation of `S₃`: `0` on transpositions,
  `−1` on 3-cycles);
* `mixedEven N`, `mixedOdd N` — the mixed states symmetric and antisymmetric under exchanging
  particles `0` and `1`; `mixedEven_sup_mixedOdd`, `mixedEven_inf_mixedOdd` — the mixed sector is
  their direct sum;
* `mixedIntertwiner N` (`P₀₂ − P₁₂`), ★★ `mixedIntertwiner_mixedIntertwiner` (it squares to `3`
  on the mixed sector), ★★★ `mixedEvenEquivOdd` — **the two halves are isomorphic**: the mixed
  sector is two copies of one space, as `S₃`'s two-dimensional representation requires;
* ★★★ `three_mul_finrank_mixedSector_three` — **`dim(mixed) = 2N(N² − 1)/3`**, and
  ★★ `three_mul_finrank_mixedEven` — **each copy has dimension `N(N² − 1)/3`**, so
  `N³ = C(N+2, 3) + C(N, 3) + 2 · N(N² − 1)/3`;
* ★★★ `mixed_symmetry` — the capstone.

## Honest scope

⚠️ **The general isotypic decomposition is not here.** For `n ≥ 4` the mixed sector splits further,
by the irreducible representations of `S_n` (Young diagrams) with Schur–Weyl multiplicities; Mathlib
has no Specht modules or Young symmetrisers, and this module does not build them. The general-`n`
statements above (orthogonal complement, dimension count, invariance) hold for every `n`; the
two-copies structure is proved for `n = 3`, where the explicit projectors suffice.

⚠️ **"Two copies" is shown as an isomorphism of the two halves**, `mixedEven ≃ mixedOdd`, with the
character values on the sector. Irreducibility of `S₃`'s two-dimensional representation, as an
abstract representation-theory statement, is not formalised.

References: [`future-work.md`](../../specs/future-work.md) IP-1;
`SigmaLayer/ManyIdenticalParticles.lean` (`symmetrizer`, `antisymmetrizer`, `finrank_nBosonSector`, `finrank_nFermionSector`,
`sectors_not_exhaustive`, `nBosonSector_orthogonal`); `SigmaLayer/ExchangeStatistics.lean`
(`IsExchangeEigenstate.mem_or_mem`); `specs/BACKLOG.md` #219.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

variable {n N : ℕ}

/-! ### The projectors are self-adjoint -/

/-- The adjoint of a permutation is its inverse. -/
theorem inner_permOp_left (σ : Equiv.Perm (Fin n)) (x y : ManyParticle n N) :
    ⟪permOp N σ x, y⟫_ℂ = ⟪x, permOp N σ⁻¹ y⟫_ℂ := by
  rw [← inner_permOp σ x (permOp N σ⁻¹ y), ← permOp_mul, mul_inv_cancel, permOp_one]

/-- The symmetriser is self-adjoint. -/
theorem inner_symmetrizer_left (x y : ManyParticle n N) :
    ⟪symmetrizer n N x, y⟫_ℂ = ⟪x, symmetrizer n N y⟫_ℂ := by
  rw [symmetrizer_apply, symmetrizer_apply, inner_smul_left, inner_smul_right, sum_inner,
    inner_sum]
  simp only [inner_permOp_left, map_inv₀, Complex.conj_natCast]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => rfl

/-- The antisymmetriser is self-adjoint. -/
theorem inner_antisymmetrizer_left (x y : ManyParticle n N) :
    ⟪antisymmetrizer n N x, y⟫_ℂ = ⟪x, antisymmetrizer n N y⟫_ℂ := by
  rw [antisymmetrizer_apply, antisymmetrizer_apply, inner_smul_left, inner_smul_right, sum_inner,
    inner_sum]
  simp only [inner_smul_left, inner_smul_right, inner_permOp_left, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => ?_
  simp [permSign, Equiv.Perm.sign_inv]

/-- The kernel of the symmetriser is the orthogonal complement of the boson sector. -/
theorem ker_symmetrizer : LinearMap.ker (symmetrizer n N) = (nBosonSector n N)ᗮ := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_orthogonal']
  constructor
  · intro hx u hu
    rw [← isProj_symmetrizer.map_id u hu, ← inner_symmetrizer_left, hx, inner_zero_left]
  · intro hx
    refine (inner_self_eq_zero (𝕜 := ℂ)).1 ?_
    rw [inner_symmetrizer_left, isProj_symmetrizer.map_id _ (isProj_symmetrizer.map_mem x)]
    exact hx _ (isProj_symmetrizer.map_mem x)

/-- The kernel of the antisymmetriser is the orthogonal complement of the fermion sector. -/
theorem ker_antisymmetrizer : LinearMap.ker (antisymmetrizer n N) = (nFermionSector n N)ᗮ := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_orthogonal']
  constructor
  · intro hx u hu
    rw [← isProj_antisymmetrizer.map_id u hu, ← inner_antisymmetrizer_left, hx, inner_zero_left]
  · intro hx
    refine (inner_self_eq_zero (𝕜 := ℂ)).1 ?_
    rw [inner_antisymmetrizer_left,
      isProj_antisymmetrizer.map_id _ (isProj_antisymmetrizer.map_mem x)]
    exact hx _ (isProj_antisymmetrizer.map_mem x)

/-! ### The mixed-symmetry sector -/

/-- **The mixed-symmetry sector**: the states with no boson and no fermion component. -/
noncomputable def mixedSector (n N : ℕ) : Submodule ℂ (ManyParticle n N) :=
  LinearMap.ker (symmetrizer n N) ⊓ LinearMap.ker (antisymmetrizer n N)

theorem mem_mixedSector {x : ManyParticle n N} :
    x ∈ mixedSector n N ↔ symmetrizer n N x = 0 ∧ antisymmetrizer n N x = 0 := by
  simp [mixedSector]

/-- **The mixed sector is everything orthogonal to the bosons and the fermions.** -/
theorem mixedSector_eq_orthogonal :
    mixedSector n N = (nBosonSector n N ⊔ nFermionSector n N)ᗮ := by
  rw [mixedSector, ker_symmetrizer, ker_antisymmetrizer, Submodule.inf_orthogonal]

theorem nBosonSector_inf_nFermionSector (hn : 2 ≤ n) :
    nBosonSector n N ⊓ nFermionSector n N = ⊥ :=
  disjoint_iff.1 (nBosonSector_orthogonal hn).disjoint

/-- **The dimension count**: `N^n = C(N+n−1, n) + C(N, n) + dim(mixed)` for `n ≥ 2`. -/
theorem finrank_mixedSector_add (hn : 2 ≤ n) :
    finrank ℂ (mixedSector n N) + (N + n - 1).choose n + N.choose n = N ^ n := by
  have h := Submodule.finrank_add_finrank_orthogonal (nBosonSector n N ⊔ nFermionSector n N)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (nBosonSector n N) (nFermionSector n N)
  rw [nBosonSector_inf_nFermionSector hn, finrank_bot, add_zero, finrank_nBosonSector,
    finrank_nFermionSector] at hsup
  rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hsup,
    ← mixedSector_eq_orthogonal] at h
  omega

/-- The symmetriser does not see a relabelling of the input. -/
theorem symmetrizer_permOp (τ : Equiv.Perm (Fin n)) (x : ManyParticle n N) :
    symmetrizer n N (permOp N τ x) = symmetrizer n N x := by
  rw [symmetrizer_apply, symmetrizer_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) (fun σ => permOp N σ (permOp N τ x))
    (fun σ => permOp N σ x) fun σ => (permOp_mul σ τ x).symm

/-- The antisymmetriser sees a relabelling of the input through its sign. -/
theorem antisymmetrizer_permOp (τ : Equiv.Perm (Fin n)) (x : ManyParticle n N) :
    antisymmetrizer n N (permOp N τ x) = permSign τ • antisymmetrizer n N x := by
  rw [antisymmetrizer_apply, antisymmetrizer_apply, smul_comm (permSign τ)]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight τ)
    (fun σ => permSign σ • permOp N σ (permOp N τ x))
    (fun σ => permSign τ • permSign σ • permOp N σ x) fun σ => ?_
  simp only [Equiv.coe_mulRight]
  rw [← permOp_mul, smul_smul, permSign_mul, mul_comm (permSign σ), ← mul_assoc,
    permSign_mul_self, one_mul]

/-- **Relabelling the particles keeps the mixed sector.** -/
theorem permOp_mem_mixedSector (τ : Equiv.Perm (Fin n)) {x : ManyParticle n N}
    (hx : x ∈ mixedSector n N) : permOp N τ x ∈ mixedSector n N := by
  rw [mem_mixedSector] at hx ⊢
  rw [symmetrizer_permOp, antisymmetrizer_permOp, hx.1, hx.2, smul_zero]
  exact ⟨rfl, rfl⟩

/-- **Permutation-symmetric dynamics keeps the mixed sector**: an operator commuting with every
relabelling maps mixed states to mixed states. -/
theorem map_mem_mixedSector (T : ManyParticle n N →ₗ[ℂ] ManyParticle n N)
    (hT : ∀ σ y, T (permOp N σ y) = permOp N σ (T y)) {x : ManyParticle n N}
    (hx : x ∈ mixedSector n N) : T x ∈ mixedSector n N := by
  rw [mem_mixedSector] at hx ⊢
  have hS : symmetrizer n N (T x) = T (symmetrizer n N x) := by
    simp only [symmetrizer_apply, map_smul, map_sum, hT]
  have hA : antisymmetrizer n N (T x) = T (antisymmetrizer n N x) := by
    simp only [antisymmetrizer_apply, map_smul, map_sum, hT]
  rw [hS, hA, hx.1, hx.2, map_zero]
  exact ⟨rfl, rfl⟩

/-- **No mixed state is an exchange eigenstate**, beyond zero. -/
theorem eq_zero_of_mem_mixedSector_of_isExchangeEigenstate {x : ManyParticle n N}
    (hx : x ∈ mixedSector n N) (he : IsExchangeEigenstate x) : x = 0 := by
  rw [mem_mixedSector] at hx
  rcases he.mem_or_mem with hb | hf
  · rw [← isProj_symmetrizer.map_id x hb, hx.1]
  · rw [← isProj_antisymmetrizer.map_id x hf, hx.2]

/-! ### Three particles -/

/-- The transpositions of three particles. -/
abbrev swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The transpositions of three particles. -/
abbrev swap02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- The transpositions of three particles. -/
abbrev swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- A cyclic relabelling of three particles. -/
abbrev cycle3 : Equiv.Perm (Fin 3) := swap02 * swap12

/-- The inverse cyclic relabelling. -/
abbrev cycle3' : Equiv.Perm (Fin 3) := swap12 * swap02

theorem univ_perm_fin_three :
    (Finset.univ : Finset (Equiv.Perm (Fin 3))) = {1, cycle3, cycle3', swap01, swap02, swap12} := by
  decide

theorem sum_perm_fin_three {M : Type*} [AddCommMonoid M] (f : Equiv.Perm (Fin 3) → M) :
    ∑ σ, f σ = f 1 + f cycle3 + f cycle3' + f swap01 + f swap02 + f swap12 := by
  rw [univ_perm_fin_three, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

theorem permSign_swap_fin_three {i j : Fin 3} (h : i ≠ j) : permSign (Equiv.swap i j) = -1 := by
  simp [permSign, Equiv.Perm.sign_swap h]

/-- The symmetriser of three particles: the cyclic part plus the transposition part. -/
theorem symmetrizer_three (x : ManyParticle 3 N) :
    symmetrizer 3 N x = (6 : ℂ)⁻¹ • ((x + permOp N cycle3 x + permOp N cycle3' x)
      + (permOp N swap01 x + permOp N swap02 x + permOp N swap12 x)) := by
  rw [symmetrizer_apply, sum_perm_fin_three, permOp_one]
  congr 1
  abel

/-- The antisymmetriser of three particles: the cyclic part minus the transposition part. -/
theorem antisymmetrizer_three (x : ManyParticle 3 N) :
    antisymmetrizer 3 N x = (6 : ℂ)⁻¹ • ((x + permOp N cycle3 x + permOp N cycle3' x)
      - (permOp N swap01 x + permOp N swap02 x + permOp N swap12 x)) := by
  rw [antisymmetrizer_apply, sum_perm_fin_three, permOp_one, permSign_one, cycle3, cycle3',
    permSign_mul, permSign_mul, permSign_swap_fin_three (by decide),
    permSign_swap_fin_three (by decide), permSign_swap_fin_three (by decide)]
  congr 1
  simp only [one_smul, neg_mul_neg, mul_one, neg_smul]
  abel

/-- **Three particles: the mixed sector is where the cyclic average vanishes**,
`x + C x + C² x = 0` for a cyclic relabelling `C`. -/
theorem mem_mixedSector_three_iff {x : ManyParticle 3 N} :
    x ∈ mixedSector 3 N ↔ x + permOp N cycle3 x + permOp N cycle3' x = 0 := by
  rw [mem_mixedSector, symmetrizer_three, antisymmetrizer_three]
  set u := x + permOp N cycle3 x + permOp N cycle3' x
  set t := permOp N swap01 x + permOp N swap02 x + permOp N swap12 x
  constructor
  · rintro ⟨hS, hA⟩
    have h : (3 : ℂ)⁻¹ • u = 0 := by
      have := congrArg₂ (· + ·) hS hA
      simp only [add_zero, ← smul_add] at this
      rw [show u + t + (u - t) = (2 : ℂ) • u by rw [two_smul]; abel, smul_smul] at this
      norm_num at this
      simpa using this
    simpa using h
  · intro hu
    have hS := (isProj_symmetrizer (n := 3) (N := N)).map_mem x
    have hA := (isProj_antisymmetrizer (n := 3) (N := N)).map_mem x
    rw [symmetrizer_three] at hS
    rw [antisymmetrizer_three] at hA
    change (6 : ℂ)⁻¹ • (u + t) ∈ nBosonSector 3 N at hS
    change (6 : ℂ)⁻¹ • (u - t) ∈ nFermionSector 3 N at hA
    simp only [hu, zero_add, zero_sub, smul_neg] at hS hA ⊢
    have h0 : (6 : ℂ)⁻¹ • t ∈ nBosonSector 3 N ⊓ nFermionSector 3 N :=
      ⟨hS, by simpa using (nFermionSector 3 N).neg_mem hA⟩
    rw [nBosonSector_inf_nFermionSector (by norm_num), Submodule.mem_bot] at h0
    exact ⟨h0, by rw [h0, neg_zero]⟩

/-- On the mixed sector the three transpositions sum to zero. -/
theorem sum_swaps_eq_zero_of_mem_mixedSector {x : ManyParticle 3 N} (hx : x ∈ mixedSector 3 N) :
    permOp N swap01 x + permOp N swap02 x + permOp N swap12 x = 0 := by
  have hS := (mem_mixedSector.1 hx).1
  rw [symmetrizer_three, mem_mixedSector_three_iff.1 hx, zero_add, smul_eq_zero] at hS
  exact hS.resolve_left (by norm_num)

/-! ### Two copies -/

/-- The mixed states symmetric under exchanging particles `0` and `1`. -/
noncomputable def mixedEven (N : ℕ) : Submodule ℂ (ManyParticle 3 N) :=
  mixedSector 3 N ⊓ LinearMap.ker (permOp N swap01 - LinearMap.id)

/-- The mixed states antisymmetric under exchanging particles `0` and `1`. -/
noncomputable def mixedOdd (N : ℕ) : Submodule ℂ (ManyParticle 3 N) :=
  mixedSector 3 N ⊓ LinearMap.ker (permOp N swap01 + LinearMap.id)

theorem mem_mixedEven {x : ManyParticle 3 N} :
    x ∈ mixedEven N ↔ x ∈ mixedSector 3 N ∧ permOp N swap01 x = x := by
  simp [mixedEven, sub_eq_zero]

theorem mem_mixedOdd {x : ManyParticle 3 N} :
    x ∈ mixedOdd N ↔ x ∈ mixedSector 3 N ∧ permOp N swap01 x = -x := by
  simp [mixedOdd, add_eq_zero_iff_eq_neg]

/-- **The intertwiner** `P₀₂ − P₁₂`, which exchanges the two copies. -/
noncomputable def mixedIntertwiner (N : ℕ) : ManyParticle 3 N →ₗ[ℂ] ManyParticle 3 N :=
  permOp N swap02 - permOp N swap12

theorem mixedIntertwiner_apply (x : ManyParticle 3 N) :
    mixedIntertwiner N x = permOp N swap02 x - permOp N swap12 x := rfl

theorem mixedIntertwiner_mem_mixedSector {x : ManyParticle 3 N} (hx : x ∈ mixedSector 3 N) :
    mixedIntertwiner N x ∈ mixedSector 3 N :=
  sub_mem (permOp_mem_mixedSector _ hx) (permOp_mem_mixedSector _ hx)

theorem permOp_swap01_mixedIntertwiner (x : ManyParticle 3 N) :
    permOp N swap01 (mixedIntertwiner N x)
      = permOp N swap12 (permOp N swap01 x) - permOp N swap02 (permOp N swap01 x) := by
  rw [mixedIntertwiner_apply, map_sub, ← permOp_mul, ← permOp_mul, ← permOp_mul, ← permOp_mul,
    show swap01 * swap02 = swap12 * swap01 by decide,
    show swap01 * swap12 = swap02 * swap01 by decide]

theorem mixedIntertwiner_mem_mixedOdd {x : ManyParticle 3 N} (hx : x ∈ mixedEven N) :
    mixedIntertwiner N x ∈ mixedOdd N := by
  rw [mem_mixedEven] at hx
  refine mem_mixedOdd.2 ⟨mixedIntertwiner_mem_mixedSector hx.1, ?_⟩
  rw [permOp_swap01_mixedIntertwiner, hx.2, mixedIntertwiner_apply, neg_sub]

theorem mixedIntertwiner_mem_mixedEven {x : ManyParticle 3 N} (hx : x ∈ mixedOdd N) :
    mixedIntertwiner N x ∈ mixedEven N := by
  rw [mem_mixedOdd] at hx
  refine mem_mixedEven.2 ⟨mixedIntertwiner_mem_mixedSector hx.1, ?_⟩
  rw [permOp_swap01_mixedIntertwiner, hx.2, map_neg, map_neg, mixedIntertwiner_apply]
  abel

/-- **The intertwiner squares to `3` on the mixed sector.** -/
theorem mixedIntertwiner_mixedIntertwiner {x : ManyParticle 3 N} (hx : x ∈ mixedSector 3 N) :
    mixedIntertwiner N (mixedIntertwiner N x) = (3 : ℂ) • x := by
  have hu := mem_mixedSector_three_iff.1 hx
  rw [mixedIntertwiner_apply, mixedIntertwiner_apply, map_sub, map_sub, ← permOp_mul,
    ← permOp_mul, ← permOp_mul, ← permOp_mul, Equiv.swap_mul_self, Equiv.swap_mul_self,
    permOp_one]
  have h3 : (3 : ℂ) • x = x + x + x := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [h3]
  calc x - permOp N cycle3 x - (permOp N cycle3' x - x)
      = x + x + x - (x + permOp N cycle3 x + permOp N cycle3' x) := by abel
    _ = x + x + x := by rw [hu, sub_zero]

/-- **The two copies are isomorphic**: the intertwiner, with inverse a third of itself. -/
noncomputable def mixedEvenEquivOdd (N : ℕ) : mixedEven N ≃ₗ[ℂ] mixedOdd N where
  toFun x := ⟨mixedIntertwiner N x, mixedIntertwiner_mem_mixedOdd x.2⟩
  invFun y := ⟨(3 : ℂ)⁻¹ • mixedIntertwiner N y,
    (mixedEven N).smul_mem _ (mixedIntertwiner_mem_mixedEven y.2)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_smul _ _ _)
  left_inv x := Subtype.ext <| by
    change (3 : ℂ)⁻¹ • mixedIntertwiner N (mixedIntertwiner N x) = x
    rw [mixedIntertwiner_mixedIntertwiner (mem_mixedEven.1 x.2).1, smul_smul]
    norm_num
  right_inv y := Subtype.ext <| by
    change mixedIntertwiner N ((3 : ℂ)⁻¹ • mixedIntertwiner N y) = y
    rw [map_smul, mixedIntertwiner_mixedIntertwiner (mem_mixedOdd.1 y.2).1, smul_smul]
    norm_num

theorem mixedEven_sup_mixedOdd : mixedEven N ⊔ mixedOdd N = mixedSector 3 N := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
  have hsq : permOp N swap01 (permOp N swap01 x) = x := by
    rw [← permOp_mul, Equiv.swap_mul_self, permOp_one]
  refine Submodule.mem_sup.2 ⟨(2 : ℂ)⁻¹ • (x + permOp N swap01 x), ?_,
    (2 : ℂ)⁻¹ • (x - permOp N swap01 x), ?_, ?_⟩
  · refine mem_mixedEven.2 ⟨(mixedSector 3 N).smul_mem _ (add_mem hx (permOp_mem_mixedSector _ hx)),
      ?_⟩
    rw [map_smul, map_add, hsq, add_comm]
  · refine mem_mixedOdd.2 ⟨(mixedSector 3 N).smul_mem _ (sub_mem hx (permOp_mem_mixedSector _ hx)),
      ?_⟩
    rw [map_smul, map_sub, hsq, ← smul_neg, neg_sub]
  · rw [← smul_add, show x + permOp N swap01 x + (x - permOp N swap01 x) = (2 : ℂ) • x by
      rw [two_smul]; abel, smul_smul]
    norm_num

theorem mixedEven_inf_mixedOdd : mixedEven N ⊓ mixedOdd N = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  have h1 := (mem_mixedEven.1 hx.1).2
  have h2 := (mem_mixedOdd.1 hx.2).2
  rw [h1] at h2
  have : (2 : ℂ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; exact neg_add_cancel x
  simpa using this

/-- **The mixed sector is two copies of one space.** -/
theorem finrank_mixedSector_three_eq :
    finrank ℂ (mixedSector 3 N) = 2 * finrank ℂ (mixedEven N) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (mixedEven N) (mixedOdd N)
  rw [mixedEven_sup_mixedOdd, mixedEven_inf_mixedOdd, finrank_bot, add_zero,
    ← (mixedEvenEquivOdd N).finrank_eq] at h
  omega

/-- **Three particles in `N` modes: the mixed sector has dimension `2N(N² − 1)/3`.** -/
theorem three_mul_finrank_mixedSector_three :
    3 * finrank ℂ (mixedSector 3 N) = 2 * ((N + 1) * N * (N - 1)) := by
  have h := finrank_mixedSector_add (n := 3) (N := N) (by norm_num)
  rcases (show N < 3 ∨ 3 ≤ N by omega) with hN | hN
  · interval_cases N <;> simp_all [Nat.choose]
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
    have h1 := Nat.descFactorial_eq_factorial_mul_choose (M + 3 + 3 - 1) 3
    have h2 := Nat.descFactorial_eq_factorial_mul_choose (M + 3) 3
    simp only [Nat.descFactorial, Nat.factorial, show M + 3 + 3 - 1 = M + 5 by omega,
      show M + 3 - 1 = M + 2 by omega] at h1 h2 h ⊢
    simp only [show M + 5 - 2 = M + 3 by omega, show M + 5 - 1 = M + 4 by omega,
      show M + 3 - 2 = M + 1 by omega, Nat.sub_zero] at h1 h2
    nlinarith [h, h1, h2]

/-- **Each copy has dimension `N(N² − 1)/3`**: the multiplicity of the two-dimensional
representation of `S₃`. -/
theorem three_mul_finrank_mixedEven :
    3 * finrank ℂ (mixedEven N) = (N + 1) * N * (N - 1) := by
  have h := three_mul_finrank_mixedSector_three (N := N)
  rw [finrank_mixedSector_three_eq] at h
  omega

/-! ### The capstone -/

/-- **The mixed-symmetry sectors.**

1. the mixed sector is the orthogonal complement of the boson and fermion sectors, of dimension
   `N^n − C(N+n−1, n) − C(N, n)` for `n ≥ 2`;
2. every permutation-symmetric operator keeps it;
3. no nonzero mixed state is an exchange eigenstate;
4. for three particles it is exactly where the cyclic average vanishes;
5. for three particles it is two isomorphic copies of one space of dimension `N(N² − 1)/3`. -/
theorem mixed_symmetry :
    (mixedSector n N = (nBosonSector n N ⊔ nFermionSector n N)ᗮ
      ∧ (2 ≤ n → finrank ℂ (mixedSector n N) + (N + n - 1).choose n + N.choose n = N ^ n))
    ∧ (∀ T : ManyParticle n N →ₗ[ℂ] ManyParticle n N,
        (∀ σ y, T (permOp N σ y) = permOp N σ (T y)) →
          ∀ x ∈ mixedSector n N, T x ∈ mixedSector n N)
    ∧ (∀ x ∈ mixedSector n N, IsExchangeEigenstate x → x = 0)
    ∧ (∀ x : ManyParticle 3 N,
        x ∈ mixedSector 3 N ↔ x + permOp N cycle3 x + permOp N cycle3' x = 0)
    ∧ (mixedEven N ⊔ mixedOdd N = mixedSector 3 N ∧ mixedEven N ⊓ mixedOdd N = ⊥
        ∧ Nonempty (mixedEven N ≃ₗ[ℂ] mixedOdd N)
        ∧ 3 * finrank ℂ (mixedEven N) = (N + 1) * N * (N - 1)
        ∧ 3 * finrank ℂ (mixedSector 3 N) = 2 * ((N + 1) * N * (N - 1))) :=
  ⟨⟨mixedSector_eq_orthogonal, finrank_mixedSector_add⟩,
    fun T hT _ hx => map_mem_mixedSector T hT hx,
    fun _ hx he => eq_zero_of_mem_mixedSector_of_isExchangeEigenstate hx he,
    fun _ => mem_mixedSector_three_iff,
    ⟨mixedEven_sup_mixedOdd, mixedEven_inf_mixedOdd, ⟨mixedEvenEquivOdd N⟩,
      three_mul_finrank_mixedEven, three_mul_finrank_mixedSector_three⟩⟩

end CSD.SigmaLayer
