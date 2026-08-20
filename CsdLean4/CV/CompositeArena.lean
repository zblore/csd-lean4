/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ArenaBridge
public import CsdLean4.SigmaLayer.TensorReconstruction
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# P2: the composite arena — two sectors compose by mode concatenation, and the algebra forcing transports

**Category:** CV (continuous variables — composition of sectors at the arena
level; `eft-pillars-plan.md` P2).

The algebra half of composition is landed: `compositeAlgReconstruction`
(`SigmaLayer/TensorReconstruction.lean`) forces any composite carrying
commuting, generating local matrix algebras to BE the tensor product. P2 asked
for the arena-side analogue: what the composite of two ontic sectors *is*, and
whether that forcing transports. Scoped first in
`specs/composite-arena-plan.md`.

**What the composite is: mode concatenation.** The composite of a `K₁`-mode
sector and a `K₂`-mode sector is the `(K₁+K₂)`-mode sector — an arena the
corpus already has, not a new species. `configSplit` splits a joint
configuration into its two mode blocks, and everything is read through it:

* `sectorJoin` / `arenaJoin` — the Kronecker vector in field coordinates
  (`norm_sectorJoin : ‖u ⊗ v‖ = ‖u‖·‖v‖`) and the induced **Segre map** on
  rays, `FieldArena K₁ N → FieldArena K₂ N → FieldArena (K₁+K₂) N`.
* `leftOp` / `rightOp` — the two local operator algebras (reindexed `A ⊗ₖ 1`,
  `1 ⊗ₖ B`), with `leftHom` / `rightHom` the algebra-hom packagings, and
  ★ `leftOp_supportedOn` / `rightOp_supportedOn`: **the local subalgebras are
  mode-local** (`SupportedOn` their blocks), so every P1 theorem — statics,
  cones, strokes — applies to the composite arena with zero new proofs.
* Transport along the join: `arenaDM_join` (`ρ_{p⊗q} = ρ_p ⊗ₖ ρ_q`),
  ★ `arenaObs_join_left` / `arenaObs_join_right` (marginal readings exact),
  ★ `arenaObs_join_mul` (joint expectations of product observables factor —
  local tomography read on the arena), ★ `arenaKick_join` (product unitaries
  restrict along the join to the product action).
* ★★ `composite_no_signalling` — **no-signalling on the composite arena,
  exactly, for ALL states**: a kick built from a right-sector unitary leaves
  every left-sector arena observable invariant — on entangled points too,
  because it is an instance of P1's `arenaObs_kick_of_disjointSupport`, not a
  consequence of the join.
* ★★ `bell_not_join` — **entanglement is real at the arena level**: for
  `N ≥ 2` the Bell ray is not in the image of `arenaJoin`
  (`exists_bell_witness` makes it non-vacuous). The composite arena is
  strictly larger than the pair of components — the arena-side signature of
  `⊗` versus `×`.
* ★★ `composite_generate` + `compositeArenaForced` — **the algebra forcing
  transports**: the composite arena's own operator algebra, with its two
  mode-local subalgebras, satisfies the reconstruction's premises (they
  commute, `leftOp_comm_rightOp`, and generate, `composite_generate`), so the
  landed `compositeAlgReconstruction` applies and forces
  `Matrix C₁ ⊗[ℂ] Matrix C₂ ≃ₐ Matrix C₁₂`, with `compositeArenaForced_tmul`
  pinning the map as `A ⊗ₜ B ↦ leftOp A · rightOp B`. Consumed from the landed
  theorem, not re-proved.

⚠️ Honest scope: homogeneous field sectors — both factors share the level
count `N` and compose mode-disjointly, the field-native case the CV chain and
P1's arenas are built from. Heterogeneous composites (`N₁ ≠ N₂`, non-field
sectors) are not claimed here; they need the arena API generalised over its
index type (rule-of-two note: generalise `ArenaBridge` when next touched). The
fibre side of the composite is the product of record media, with per-sector
strokes covered by P1's generic machinery through `leftOp_supportedOn`; and
composite *mixed*-state theory (reduced states of entangled rays) is CV-26's
coarse-graining territory, not this pillar's.

## References

`specs/composite-arena-plan.md` (scoping); `specs/eft-pillars-plan.md` (P2);
`specs/future-work.md`; `SigmaLayer/TensorReconstruction.lean`
(`compositeAlgReconstruction`, consumed); `SigmaLayer/TensorGeneration.lean`
(`single_eq_smul`; the `Fin`-indexed generation this re-lands arena-natively);
`CV/ArenaBridge.lean` (`arenaDM`, `arenaObs`, `arenaKick`, the P1 statics);
`CV/ModeLocality.lean` (`SupportedOn`).
-/

@[expose] public section

open Matrix
open scoped Kronecker
open scoped TensorProduct
open scoped LinearAlgebra.Projectivization

namespace CSD.CV

variable {K₁ K₂ N : ℕ}

/-! ### Splitting a joint configuration into its mode blocks -/

/-- **The mode split**: a `(K₁+K₂)`-mode configuration is a pair of a
`K₁`-mode and a `K₂`-mode configuration. The composite arena is read through
this equivalence. -/
def configSplit : FieldConfig (K₁ + K₂) N ≃ FieldConfig K₁ N × FieldConfig K₂ N where
  toFun c := (fun i => c (Fin.castAdd K₂ i), fun j => c (Fin.natAdd K₁ j))
  invFun x := fun k => Fin.addCases (fun i => x.1 i) (fun j => x.2 j) k
  left_inv c := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · dsimp only
      rw [Fin.addCases_left]
    · dsimp only
      rw [Fin.addCases_right]
  right_inv x := by
    refine Prod.ext ?_ ?_
    · funext i
      dsimp only
      rw [Fin.addCases_left]
    · funext j
      dsimp only
      rw [Fin.addCases_right]

/-- The left mode block of the composite. -/
def leftModes (K₁ K₂ : ℕ) : Finset (Fin (K₁ + K₂)) :=
  Finset.univ.image (Fin.castAdd K₂)

/-- The right mode block of the composite. -/
def rightModes (K₁ K₂ : ℕ) : Finset (Fin (K₁ + K₂)) :=
  Finset.univ.image (Fin.natAdd K₁)

lemma mem_leftModes {k : Fin (K₁ + K₂)} :
    k ∈ leftModes K₁ K₂ ↔ ∃ i, Fin.castAdd K₂ i = k := by
  simp [leftModes]

lemma mem_rightModes {k : Fin (K₁ + K₂)} :
    k ∈ rightModes K₁ K₂ ↔ ∃ j, Fin.natAdd K₁ j = k := by
  simp [rightModes]

lemma natAdd_notMem_leftModes (j : Fin K₂) :
    Fin.natAdd K₁ j ∉ leftModes K₁ K₂ := by
  intro hj
  obtain ⟨i, hi⟩ := mem_leftModes.mp hj
  have : (Fin.castAdd K₂ i).val = (Fin.natAdd K₁ j).val := by rw [hi]
  rw [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

lemma castAdd_notMem_rightModes (i : Fin K₁) :
    Fin.castAdd K₂ i ∉ rightModes K₁ K₂ := by
  intro hi
  obtain ⟨j, hj⟩ := mem_rightModes.mp hi
  have : (Fin.natAdd K₁ j).val = (Fin.castAdd K₂ i).val := by rw [hj]
  rw [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- The two mode blocks are disjoint: left values are `< K₁`, right values
are `≥ K₁`. -/
lemma disjoint_leftModes_rightModes : Disjoint (leftModes K₁ K₂) (rightModes K₁ K₂) := by
  rw [Finset.disjoint_left]
  intro k hkl hkr
  obtain ⟨i, hi⟩ := mem_leftModes.mp hkl
  rw [← hi] at hkr
  exact castAdd_notMem_rightModes i hkr

/-! ### The join: the Kronecker vector and the Segre map -/

/-- **The sector join**: the Kronecker product of two field vectors, in field
coordinates. -/
noncomputable def sectorJoin (u : EuclideanSpace ℂ (FieldConfig K₁ N))
    (v : EuclideanSpace ℂ (FieldConfig K₂ N)) :
    EuclideanSpace ℂ (FieldConfig (K₁ + K₂) N) :=
  WithLp.toLp 2 (fun c => u (configSplit c).1 * v (configSplit c).2)

lemma sectorJoin_apply (u : EuclideanSpace ℂ (FieldConfig K₁ N))
    (v : EuclideanSpace ℂ (FieldConfig K₂ N)) (c : FieldConfig (K₁ + K₂) N) :
    sectorJoin u v c = u (configSplit c).1 * v (configSplit c).2 := rfl

/-- Pointwise reading of an equality of Euclidean vectors (`congrFun` through
the `WithLp` structure). -/
lemma euclid_congrFun {ι : Type*} [Fintype ι] {x y : EuclideanSpace ℂ ι}
    (h : x = y) (i : ι) : x i = y i := by rw [h]

/-- The join is bilinear on scalars: `(a•u) ⊗ (b•v) = (ab) • (u ⊗ v)`. -/
lemma sectorJoin_smul_smul (a b : ℂ) (u : EuclideanSpace ℂ (FieldConfig K₁ N))
    (v : EuclideanSpace ℂ (FieldConfig K₂ N)) :
    sectorJoin (a • u) (b • v) = (a * b) • sectorJoin u v := by
  ext c
  simp only [sectorJoin_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The join norm is multiplicative**: `‖u ⊗ v‖ = ‖u‖·‖v‖`. -/
lemma norm_sectorJoin (u : EuclideanSpace ℂ (FieldConfig K₁ N))
    (v : EuclideanSpace ℂ (FieldConfig K₂ N)) :
    ‖sectorJoin u v‖ = ‖u‖ * ‖v‖ := by
  have hsum : ∑ c, ‖sectorJoin u v c‖ ^ 2
      = (∑ a, ‖u a‖ ^ 2) * (∑ b, ‖v b‖ ^ 2) := by
    rw [Finset.sum_mul_sum,
      ← Equiv.sum_comp (configSplit (K₁ := K₁) (K₂ := K₂) (N := N)).symm
        (fun c => ‖sectorJoin u v c‖ ^ 2),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [sectorJoin_apply, Equiv.apply_symm_apply, norm_mul, mul_pow]
  have hsq : ‖sectorJoin u v‖ ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
    rw [← euclid_sum_norm_sq (sectorJoin u v), hsum,
      euclid_sum_norm_sq u, euclid_sum_norm_sq v, mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).mp hsq

/-- The join of nonzero vectors is nonzero. -/
lemma sectorJoin_ne_zero {u : EuclideanSpace ℂ (FieldConfig K₁ N)}
    {v : EuclideanSpace ℂ (FieldConfig K₂ N)} (hu : u ≠ 0) (hv : v ≠ 0) :
    sectorJoin u v ≠ 0 := by
  intro h0
  have := norm_sectorJoin u v
  rw [h0, norm_zero] at this
  rcases mul_eq_zero.mp this.symm with h | h
  · exact hu (norm_eq_zero.mp h)
  · exact hv (norm_eq_zero.mp h)

/-- **The Segre map**: the composite ray of a pair of sector rays. -/
noncomputable def arenaJoin (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    FieldArena (K₁ + K₂) N :=
  Projectivization.mk ℂ (sectorJoin p.rep q.rep)
    (sectorJoin_ne_zero (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q))

/-- The Segre map on representatives: the `rep` choices wash out. -/
lemma arenaJoin_mk {u : EuclideanSpace ℂ (FieldConfig K₁ N)} (hu : u ≠ 0)
    {v : EuclideanSpace ℂ (FieldConfig K₂ N)} (hv : v ≠ 0) :
    arenaJoin (Projectivization.mk ℂ u hu) (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (sectorJoin u v) (sectorJoin_ne_zero hu hv) := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (Projectivization.mk_rep (Projectivization.mk ℂ u hu))
  obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (Projectivization.mk_rep (Projectivization.mk ℂ v hv))
  rw [arenaJoin]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨a * b, by rw [← ha, ← hb, sectorJoin_smul_smul]⟩

/-! ### The local operator algebras -/

/-- **The composite reindex**: matrices over the pair of configuration spaces,
read as matrices over the joint configuration space. An algebra equivalence. -/
noncomputable def compositeReindex :
    Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ
      ≃ₐ[ℂ] Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (configSplit (K₁ := K₁) (K₂ := K₂) (N := N)).symm

lemma compositeReindex_apply
    (M : Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ)
    (c d : FieldConfig (K₁ + K₂) N) :
    compositeReindex M c d = M (configSplit c) (configSplit d) := by
  rw [compositeReindex, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.submatrix_apply]

lemma compositeReindex_conjTranspose
    (M : Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ) :
    (compositeReindex M)ᴴ = compositeReindex Mᴴ := by
  ext c d
  rw [Matrix.conjTranspose_apply, compositeReindex_apply, compositeReindex_apply,
    Matrix.conjTranspose_apply]

/-- Traces are preserved by the composite reindex. -/
lemma trace_compositeReindex
    (M : Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ) :
    (compositeReindex M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, compositeReindex_apply]
  exact Equiv.sum_comp (configSplit (K₁ := K₁) (K₂ := K₂) (N := N)) (fun x => M x x)

/-- A left-sector operator acting on the composite: `A ⊗ₖ 1`, reindexed. -/
noncomputable def leftOp (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) :
    Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  compositeReindex (A ⊗ₖ (1 : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ))

/-- A right-sector operator acting on the composite: `1 ⊗ₖ B`, reindexed. -/
noncomputable def rightOp (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) :
    Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  compositeReindex ((1 : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) ⊗ₖ B)

/-- The local products assemble to the reindexed Kronecker product. -/
lemma leftOp_mul_rightOp (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) :
    leftOp (K₂ := K₂) A * rightOp B = compositeReindex (A ⊗ₖ B) := by
  rw [leftOp, rightOp, ← map_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- ★ **The two local algebras commute** — locality of the composite. -/
lemma leftOp_comm_rightOp (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) :
    Commute (leftOp (K₂ := K₂) A) (rightOp B) := by
  rw [Commute, SemiconjBy, leftOp_mul_rightOp, rightOp, leftOp, ← map_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- `A ↦ A ⊗ₖ 1` as an algebra hom into the pair-indexed algebra. -/
noncomputable def kronLeftHom :
    Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ
      →ₐ[ℂ] Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ :=
  AlgHom.ofLinearMap
    { toFun := fun A => A ⊗ₖ (1 : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ)
      map_add' := fun A B => Matrix.add_kronecker A B 1
      map_smul' := fun c A => by
        simpa using Matrix.smul_kronecker c A
          (1 : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) }
    (by
      show (1 : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) ⊗ₖ 1 = 1
      exact Matrix.one_kronecker_one)
    (fun A B => by
      show (A * B) ⊗ₖ (1 : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ)
        = (A ⊗ₖ 1) * (B ⊗ₖ 1)
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul])

/-- `B ↦ 1 ⊗ₖ B` as an algebra hom into the pair-indexed algebra. -/
noncomputable def kronRightHom :
    Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ
      →ₐ[ℂ] Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ :=
  AlgHom.ofLinearMap
    { toFun := fun B => (1 : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) ⊗ₖ B
      map_add' := fun A B => Matrix.kronecker_add 1 A B
      map_smul' := fun c B => by
        simpa using Matrix.kronecker_smul c
          (1 : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) B }
    (by
      show (1 : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) ⊗ₖ 1 = 1
      exact Matrix.one_kronecker_one)
    (fun A B => by
      show (1 : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) ⊗ₖ (A * B)
        = (1 ⊗ₖ A) * (1 ⊗ₖ B)
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul])

/-- The left embedding as an algebra hom. -/
noncomputable def leftHom :
    Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ
      →ₐ[ℂ] Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  (compositeReindex (K₁ := K₁) (K₂ := K₂) (N := N)).toAlgHom.comp kronLeftHom

/-- The right embedding as an algebra hom. -/
noncomputable def rightHom :
    Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ
      →ₐ[ℂ] Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  (compositeReindex (K₁ := K₁) (K₂ := K₂) (N := N)).toAlgHom.comp kronRightHom

lemma leftHom_apply (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) :
    leftHom (K₂ := K₂) A = leftOp A := rfl

lemma rightHom_apply (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) :
    rightHom (K₁ := K₁) B = rightOp B := rfl

/-! ### The local algebras are mode-local: P1 machinery applies for free -/

/-- ★ **The left algebra is supported on the left mode block.** With this,
every P1 statement — exact statics, the Lieb-Robinson cone, record strokes —
applies to composite-arena local observables with zero new proofs. -/
lemma leftOp_supportedOn (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) :
    SupportedOn (leftModes K₁ K₂) (leftOp A) := by
  constructor
  · intro c d k hk hcd
    revert hk hcd
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · intro hi _
      exact absurd (mem_leftModes.mpr ⟨i, rfl⟩) hi
    · intro _ hj
      rw [leftOp, compositeReindex_apply, Matrix.kroneckerMap_apply]
      have hne : (configSplit c).2 ≠ (configSplit d).2 := fun h => hj (congrFun h j)
      rw [Matrix.one_apply_ne hne, mul_zero]
  · intro c d c' d' hS hS' hoff hoff'
    have hcast : ∀ i : Fin K₁, Fin.castAdd K₂ i ∈ leftModes K₁ K₂ :=
      fun i => mem_leftModes.mpr ⟨i, rfl⟩
    rw [leftOp, compositeReindex_apply, compositeReindex_apply,
      Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
    have h1 : (configSplit c).1 = (configSplit c').1 :=
      funext fun i => hS _ (hcast i)
    have h2 : (configSplit d).1 = (configSplit d').1 :=
      funext fun i => hS' _ (hcast i)
    have h3 : (configSplit c).2 = (configSplit d).2 :=
      funext fun j => hoff _ (natAdd_notMem_leftModes j)
    have h4 : (configSplit c').2 = (configSplit d').2 :=
      funext fun j => hoff' _ (natAdd_notMem_leftModes j)
    rw [h1, h2, h3, h4, Matrix.one_apply_eq, Matrix.one_apply_eq]

/-- ★ **The right algebra is supported on the right mode block.** -/
lemma rightOp_supportedOn (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) :
    SupportedOn (rightModes K₁ K₂) (rightOp B) := by
  constructor
  · intro c d k hk hcd
    revert hk hcd
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · intro _ hi
      rw [rightOp, compositeReindex_apply, Matrix.kroneckerMap_apply]
      have hne : (configSplit c).1 ≠ (configSplit d).1 := fun h => hi (congrFun h i)
      rw [Matrix.one_apply_ne hne, zero_mul]
    · intro hj _
      exact absurd (mem_rightModes.mpr ⟨j, rfl⟩) hj
  · intro c d c' d' hS hS' hoff hoff'
    have hnat : ∀ j : Fin K₂, Fin.natAdd K₁ j ∈ rightModes K₁ K₂ :=
      fun j => mem_rightModes.mpr ⟨j, rfl⟩
    rw [rightOp, compositeReindex_apply, compositeReindex_apply,
      Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
    have h1 : (configSplit c).2 = (configSplit c').2 :=
      funext fun j => hS _ (hnat j)
    have h2 : (configSplit d).2 = (configSplit d').2 :=
      funext fun j => hS' _ (hnat j)
    have h3 : (configSplit c).1 = (configSplit d).1 :=
      funext fun i => hoff _ (castAdd_notMem_rightModes i)
    have h4 : (configSplit c').1 = (configSplit d').1 :=
      funext fun i => hoff' _ (castAdd_notMem_rightModes i)
    rw [h1, h2, h3, h4, Matrix.one_apply_eq, Matrix.one_apply_eq]

/-! ### State transport: the density of a join is the Kronecker density -/

/-- Bridge to the canonical representative (`arenaDM` is definitionally
`dmVec ∘ rep`, restated as a lemma for cross-module use). -/
lemma arenaDM_eq_dmVec_rep {K N : ℕ} (p : FieldArena K N) :
    arenaDM p = dmVec p.rep := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [arenaDM_mk]

/-- **The density of a join is the Kronecker product of the densities**:
`ρ_{p⊗q} = ρ_p ⊗ₖ ρ_q`, read on the composite index. -/
theorem arenaDM_join (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    arenaDM (arenaJoin p q) = compositeReindex (arenaDM p ⊗ₖ arenaDM q) := by
  rw [arenaJoin, arenaDM_mk, arenaDM_eq_dmVec_rep, arenaDM_eq_dmVec_rep]
  set u := p.rep
  set v := q.rep
  ext c d
  rw [compositeReindex_apply, Matrix.kroneckerMap_apply,
    dmVec_apply', dmVec_apply', dmVec_apply', norm_sectorJoin,
    sectorJoin_apply, sectorJoin_apply]
  rw [show ((((‖u‖ * ‖v‖) ^ 2 : ℝ)) : ℂ)
      = ((‖u‖ ^ 2 : ℝ) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring,
    mul_inv, star_mul']
  ring

/-! ### Observable transport: marginals are exact, products factor -/

/-- ★ **The marginal reading is exact**: a left-sector observable read on a
join sees exactly the left component. No-signalling on product states, with no
hypotheses on `A`. -/
theorem arenaObs_join_left (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    arenaObs (leftOp A) (arenaJoin p q) = arenaObs A p := by
  rw [arenaObs, arenaObs, arenaDM_join, leftOp, ← map_mul,
    trace_compositeReindex, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, arenaDM_trace, mul_one]

/-- ★ The symmetric right marginal. -/
theorem arenaObs_join_right (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ)
    (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    arenaObs (rightOp B) (arenaJoin p q) = arenaObs B q := by
  rw [arenaObs, arenaObs, arenaDM_join, rightOp, ← map_mul,
    trace_compositeReindex, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, arenaDM_trace, one_mul]

/-- The expectation of a Hermitian observable in any ray is real. -/
lemma trace_arenaDM_mul_real {K N : ℕ} (p : FieldArena K N)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : Aᴴ = A) :
    ((arenaDM p * A).trace).im = 0 := by
  have hherm : (arenaDM p)ᴴ = arenaDM p := (arenaDM_posSemidef p).1
  have hstar : star ((arenaDM p * A).trace) = (arenaDM p * A).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hherm,
      Matrix.trace_mul_comm]
  rw [Complex.star_def] at hstar
  exact Complex.conj_eq_iff_im.mp hstar

/-- ★ **Local tomography on the arena**: the joint expectation of a product of
local observables factors into the product of local expectations, on every
join. (`A` Hermitian makes its expectation real, which is what lets the real
parts factor.) -/
theorem arenaObs_join_mul {A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ}
    (hA : Aᴴ = A) (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ)
    (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    arenaObs (leftOp A * rightOp B) (arenaJoin p q) = arenaObs A p * arenaObs B q := by
  rw [arenaObs, arenaObs, arenaObs, leftOp_mul_rightOp, arenaDM_join, ← map_mul,
    trace_compositeReindex, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp only [RCLike.re_to_complex]
  rw [Complex.mul_re, trace_arenaDM_mul_real p hA, zero_mul, sub_zero]

/-! ### Dynamics transport: product unitaries restrict along the join -/

/-- **The product unitary on the composite**: `U ⊗ₖ V`, reindexed. -/
noncomputable def joinU (U : Matrix.unitaryGroup (FieldConfig K₁ N) ℂ)
    (V : Matrix.unitaryGroup (FieldConfig K₂ N) ℂ) :
    Matrix.unitaryGroup (FieldConfig (K₁ + K₂) N) ℂ :=
  ⟨compositeReindex (U.val ⊗ₖ V.val), by
    have hU : (U.val)ᴴ * U.val = 1 := by
      have hmem := U.property
      rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    have hV : (V.val)ᴴ * V.val = 1 := by
      have hmem := V.property
      rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      compositeReindex_conjTranspose, ← map_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one, map_one]⟩

/-- Kicks on representatives: the `rep` choice washes out (general-`K` API,
placed here as its first consumer; `ArenaBridge` inlines the same dance). -/
lemma arenaKick_mk {K N : ℕ} (W : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    {v : EuclideanSpace ℂ (FieldConfig K N)} (hv : v ≠ 0) :
    arenaKick W (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (Matrix.toEuclideanLin W.val v)
          (toEuclideanLin_ne_zero W hv) := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (Projectivization.mk_rep (Projectivization.mk ℂ v hv))
  rw [arenaKick]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨a, by rw [← map_smul, ha]⟩

/-- The product unitary acts on join vectors as the pair of local actions. -/
lemma toEuclideanLin_joinU (U : Matrix.unitaryGroup (FieldConfig K₁ N) ℂ)
    (V : Matrix.unitaryGroup (FieldConfig K₂ N) ℂ)
    (u : EuclideanSpace ℂ (FieldConfig K₁ N)) (v : EuclideanSpace ℂ (FieldConfig K₂ N)) :
    Matrix.toEuclideanLin (joinU U V).val (sectorJoin u v)
      = sectorJoin (Matrix.toEuclideanLin U.val u) (Matrix.toEuclideanLin V.val v) := by
  ext c
  rw [show (Matrix.toEuclideanLin (joinU U V).val (sectorJoin u v)) c
      = ∑ d, (joinU U V).val c d * sectorJoin u v d from rfl,
    sectorJoin_apply,
    show (Matrix.toEuclideanLin U.val u) (configSplit c).1
      = ∑ b₁, U.val (configSplit c).1 b₁ * u b₁ from rfl,
    show (Matrix.toEuclideanLin V.val v) (configSplit c).2
      = ∑ b₂, V.val (configSplit c).2 b₂ * v b₂ from rfl,
    ← Equiv.sum_comp (configSplit (K₁ := K₁) (K₂ := K₂) (N := N)).symm
      (fun d => (joinU U V).val c d * sectorJoin u v d)]
  rw [Finset.sum_congr rfl fun y _ => by
    rw [show (joinU U V).val c (configSplit.symm y)
        = (U.val ⊗ₖ V.val) (configSplit c) (configSplit (configSplit.symm y)) from
        compositeReindex_apply _ c _,
      show sectorJoin u v (configSplit.symm y)
        = u (configSplit (configSplit.symm y)).1 * v (configSplit (configSplit.symm y)).2 from
        sectorJoin_apply u v _,
      Equiv.apply_symm_apply, Matrix.kroneckerMap_apply]]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  dsimp only
  ring

/-- ★ **Dynamics restrict along the join**: the product unitary's kick on the
composite arena is the pair of local kicks. -/
theorem arenaKick_join (U : Matrix.unitaryGroup (FieldConfig K₁ N) ℂ)
    (V : Matrix.unitaryGroup (FieldConfig K₂ N) ℂ)
    (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    arenaKick (joinU U V) (arenaJoin p q) = arenaJoin (arenaKick U p) (arenaKick V q) := by
  rw [show arenaJoin p q = Projectivization.mk ℂ (sectorJoin p.rep q.rep)
      (sectorJoin_ne_zero (Projectivization.rep_nonzero p)
        (Projectivization.rep_nonzero q)) from rfl,
    arenaKick_mk, arenaKick, arenaKick, arenaJoin_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1, by rw [one_smul, toEuclideanLin_joinU]⟩

/-- A right-sector unitary, acting on the composite. Its matrix is the
`rightOp` of the sector unitary's matrix. -/
noncomputable def rightU (V : Matrix.unitaryGroup (FieldConfig K₂ N) ℂ) :
    Matrix.unitaryGroup (FieldConfig (K₁ + K₂) N) ℂ :=
  joinU 1 V

lemma rightU_val (V : Matrix.unitaryGroup (FieldConfig K₂ N) ℂ) :
    (rightU (K₁ := K₁) V).val = rightOp V.val := rfl

/-- ★★ **No-signalling on the composite arena — exactly, and for ALL states.**
A kick built from a right-sector unitary leaves every left-sector arena
observable invariant, on every point of the composite arena, entangled points
included. This is an instance of P1's exact statics
(`arenaObs_kick_of_disjointSupport`) through the mode-locality of the two
subalgebras — not a consequence of the join, which is why it needs no product
form on the state. -/
theorem composite_no_signalling [NeZero N]
    (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (V : Matrix.unitaryGroup (FieldConfig K₂ N) ℂ)
    (x : FieldArena (K₁ + K₂) N) :
    arenaObs (leftOp A) (arenaKick (rightU V) x) = arenaObs (leftOp A) x := by
  refine arenaObs_kick_of_disjointSupport disjoint_leftModes_rightModes
    (leftOp_supportedOn A) ?_ x
  rw [rightU_val]
  exact rightOp_supportedOn V.val

/-! ### Entanglement: the composite arena is strictly larger than the pair -/

/-- The Bell vector over a pair of patterns per sector: equal weight on the
two aligned configuration pairs, zero elsewhere. -/
noncomputable def bellVec (x₀ x₁ : FieldConfig K₁ N) (y₀ y₁ : FieldConfig K₂ N) :
    EuclideanSpace ℂ (FieldConfig (K₁ + K₂) N) :=
  WithLp.toLp 2
    (fun c => if configSplit c = (x₀, y₀) ∨ configSplit c = (x₁, y₁) then 1 else 0)

lemma bellVec_apply (x₀ x₁ : FieldConfig K₁ N) (y₀ y₁ : FieldConfig K₂ N)
    (c : FieldConfig (K₁ + K₂) N) :
    bellVec x₀ x₁ y₀ y₁ c
      = if configSplit c = (x₀, y₀) ∨ configSplit c = (x₁, y₁) then 1 else 0 := rfl

lemma bellVec_ne_zero (x₀ x₁ : FieldConfig K₁ N) (y₀ y₁ : FieldConfig K₂ N) :
    bellVec x₀ x₁ y₀ y₁ ≠ 0 := by
  intro h0
  have h := euclid_congrFun h0 (configSplit.symm (x₀, y₀))
  rw [bellVec_apply, Equiv.apply_symm_apply, if_pos (Or.inl rfl),
    PiLp.zero_apply] at h
  exact one_ne_zero h

/-- ★★ **Entanglement is real at the arena level**: the Bell ray over two
distinct patterns per sector is NOT a join. The composite arena is strictly
larger than the pair of component arenas — the arena-side signature of the
tensor product against the Cartesian one. -/
theorem bell_not_join {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁)
    {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁)
    (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    arenaJoin p q ≠ Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
      (bellVec_ne_zero x₀ x₁ y₀ y₁) := by
  intro heq
  rw [arenaJoin] at heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  set u := p.rep
  set v := q.rep
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ha
    exact sectorJoin_ne_zero (Projectivization.rep_nonzero p)
      (Projectivization.rep_nonzero q) ha.symm
  have hread : ∀ z : FieldConfig K₁ N × FieldConfig K₂ N,
      u z.1 * v z.2 = a * (if z = (x₀, y₀) ∨ z = (x₁, y₁) then 1 else 0) := by
    intro z
    have h := euclid_congrFun ha (configSplit.symm z)
    simp only [PiLp.smul_apply, smul_eq_mul, bellVec_apply, sectorJoin_apply,
      Equiv.apply_symm_apply] at h
    exact h.symm
  have h00 : u x₀ * v y₀ = a := by
    have h := hread (x₀, y₀)
    rwa [if_pos (Or.inl rfl), mul_one] at h
  have h11 : u x₁ * v y₁ = a := by
    have h := hread (x₁, y₁)
    rwa [if_pos (Or.inr rfl), mul_one] at h
  have h01 : u x₀ * v y₁ = 0 := by
    have h := hread (x₀, y₁)
    rwa [if_neg (by
      rintro (h' | h')
      · exact hy (congrArg Prod.snd h').symm
      · exact hx (congrArg Prod.fst h')), mul_zero] at h
  have hu0 : u x₀ ≠ 0 := fun h => hane (by rw [← h00, h, zero_mul])
  have hv1 : v y₁ ≠ 0 := fun h => hane (by rw [← h11, h, mul_zero])
  exact (mul_ne_zero hu0 hv1) h01

/-- Two distinct patterns exist in each sector as soon as `N ≥ 2` (constant
configurations at two distinct levels), so `bell_not_join` is non-vacuous:
entangled rays exist on every composite arena with at least two levels. -/
theorem exists_bell_witness [NeZero K₁] [NeZero K₂] (hN : 2 ≤ N) :
    ∃ (x₀ x₁ : FieldConfig K₁ N) (y₀ y₁ : FieldConfig K₂ N), x₀ ≠ x₁ ∧ y₀ ≠ y₁ := by
  refine ⟨fun _ => ⟨0, by omega⟩, fun _ => ⟨1, by omega⟩,
    fun _ => ⟨0, by omega⟩, fun _ => ⟨1, by omega⟩, ?_, ?_⟩
  · intro h
    have h0 := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne K₁)⟩
    rw [Fin.mk.injEq] at h0
    omega
  · intro h
    have h0 := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne K₂)⟩
    rw [Fin.mk.injEq] at h0
    omega

/-! ### The transport: the algebra forcing lands on the composite arena -/

/-- Kronecker of unit basis matrices is the joint unit basis matrix (the
index-generic form of `SigmaLayer.single_prod`). -/
lemma single_kronecker_single (a₁ b₁ : FieldConfig K₁ N) (a₂ b₂ : FieldConfig K₂ N) :
    (Matrix.single a₁ b₁ (1 : ℂ)) ⊗ₖ (Matrix.single a₂ b₂ (1 : ℂ))
      = Matrix.single (a₁, a₂) (b₁, b₂) (1 : ℂ) := by
  ext ⟨c₁, c₂⟩ ⟨d₁, d₂⟩
  rw [Matrix.kronecker_apply]
  simp only [Matrix.single, Matrix.of_apply, Prod.mk.injEq]
  by_cases h1 : a₁ = c₁ <;> by_cases h2 : b₁ = d₁ <;>
    by_cases h3 : a₂ = c₂ <;> by_cases h4 : b₂ = d₂ <;> simp_all

/-- The composite reindex of a unit basis matrix. -/
lemma compositeReindex_single (x y : FieldConfig K₁ N × FieldConfig K₂ N) :
    compositeReindex (Matrix.single x y (1 : ℂ))
      = Matrix.single (configSplit.symm x) (configSplit.symm y) (1 : ℂ) := by
  ext c d
  obtain ⟨z, rfl⟩ : ∃ z, configSplit.symm z = c :=
    ⟨configSplit c, configSplit.symm_apply_apply c⟩
  obtain ⟨w, rfl⟩ : ∃ w, configSplit.symm w = d :=
    ⟨configSplit d, configSplit.symm_apply_apply d⟩
  rw [compositeReindex_apply]
  simp only [Equiv.apply_symm_apply, Matrix.single, Matrix.of_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- ★★ **The composite arena's local algebras generate** — the second premise
of the reconstruction, proved arena-natively: every joint operator is a linear
combination of products `leftOp E · rightOp E'` of unit local observables. The
composite algebra carries nothing beyond the local algebras and their
products. -/
theorem composite_generate :
    Algebra.adjoin ℂ
      (Set.range (leftHom (K₁ := K₁) (K₂ := K₂) (N := N))
        ∪ Set.range (rightHom (K₁ := K₁) (K₂ := K₂) (N := N))) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [matrix_eq_sum_single M]
  refine Subalgebra.sum_mem _ (fun c _ => Subalgebra.sum_mem _ (fun d _ => ?_))
  rw [CSD.SigmaLayer.single_eq_smul]
  refine Subalgebra.smul_mem _ ?_ _
  have hsingle : Matrix.single c d (1 : ℂ)
      = leftHom (Matrix.single (configSplit c).1 (configSplit d).1 (1 : ℂ))
        * rightHom (Matrix.single (configSplit c).2 (configSplit d).2 (1 : ℂ)) := by
    rw [leftHom_apply, rightHom_apply, leftOp_mul_rightOp, single_kronecker_single,
      show ((configSplit c).1, (configSplit c).2) = configSplit c from rfl,
      show ((configSplit d).1, (configSplit d).2) = configSplit d from rfl,
      compositeReindex_single, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [hsingle]
  exact mul_mem
    (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩))
    (Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩))

section Forced

variable (K₁ K₂ N)
variable [NeZero N]

/-- Field configuration spaces are nonempty once there is at least one level. -/
lemma fieldConfig_nonempty (K : ℕ) : Nonempty (FieldConfig K N) :=
  ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

/-- Configuration cardinalities are nonzero once there is at least one level. -/
lemma card_config_neZero (K : ℕ) : NeZero (Fintype.card (FieldConfig K N)) :=
  haveI := fieldConfig_nonempty N K
  NeZero.of_pos Fintype.card_pos

/-- Matrix algebras over configuration spaces are nontrivial. -/
lemma matrix_config_nontrivial (K : ℕ) :
    Nontrivial (Matrix (FieldConfig K N) (FieldConfig K N) ℂ) := by
  obtain ⟨c⟩ := fieldConfig_nonempty N K
  refine ⟨0, 1, fun h => ?_⟩
  have hcc := congrFun (congrFun h c) c
  rw [Matrix.zero_apply, Matrix.one_apply_eq] at hcc
  exact zero_ne_one hcc

/-- The left sector algebra through its `Fin`-index presentation (what the
`Fin`-indexed reconstruction consumes). -/
noncomputable def leftHomFin :
    Matrix (Fin (Fintype.card (FieldConfig K₁ N)))
        (Fin (Fintype.card (FieldConfig K₁ N))) ℂ
      →ₐ[ℂ] Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  (leftHom (K₁ := K₁) (K₂ := K₂) (N := N)).comp
    (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₁ N))).symm.toAlgHom

/-- The right sector algebra through its `Fin`-index presentation. -/
noncomputable def rightHomFin :
    Matrix (Fin (Fintype.card (FieldConfig K₂ N)))
        (Fin (Fintype.card (FieldConfig K₂ N))) ℂ
      →ₐ[ℂ] Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  (rightHom (K₁ := K₁) (K₂ := K₂) (N := N)).comp
    (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₂ N))).symm.toAlgHom

omit [NeZero N] in
lemma leftHomFin_comm_rightHomFin :
    ∀ A B, Commute (leftHomFin K₁ K₂ N A) (rightHomFin K₁ K₂ N B) := by
  intro A B
  rw [leftHomFin, rightHomFin, AlgHom.comp_apply, AlgHom.comp_apply,
    leftHom_apply, rightHom_apply]
  exact leftOp_comm_rightOp _ _

omit [NeZero N] in
lemma range_leftHomFin :
    Set.range (leftHomFin K₁ K₂ N)
      = Set.range (leftHom (K₁ := K₁) (K₂ := K₂) (N := N)) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    rw [leftHomFin, AlgHom.comp_apply]
    exact ⟨_, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₁ N)) A, by
      rw [leftHomFin, AlgHom.comp_apply]
      congr 1
      simp⟩

omit [NeZero N] in
lemma range_rightHomFin :
    Set.range (rightHomFin K₁ K₂ N)
      = Set.range (rightHom (K₁ := K₁) (K₂ := K₂) (N := N)) := by
  ext x
  constructor
  · rintro ⟨B, rfl⟩
    rw [rightHomFin, AlgHom.comp_apply]
    exact ⟨_, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₂ N)) B, by
      rw [rightHomFin, AlgHom.comp_apply]
      congr 1
      simp⟩

omit [NeZero N] in
lemma composite_generate_fin :
    Algebra.adjoin ℂ
      (Set.range (leftHomFin K₁ K₂ N) ∪ Set.range (rightHomFin K₁ K₂ N)) = ⊤ := by
  rw [range_leftHomFin, range_rightHomFin]
  exact composite_generate

/-- The landed reconstruction, applied: it acts as `reconMap` (definitional;
restated for cross-module rewriting). -/
lemma compositeAlgReconstruction_apply {m n : ℕ} [NeZero m] [NeZero n]
    {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜] [Nontrivial 𝒜]
    (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] 𝒜) (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] 𝒜)
    (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hgen : Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤)
    (x : Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    CSD.SigmaLayer.compositeAlgReconstruction ιA ιB hc hgen x
      = CSD.SigmaLayer.reconMap ιA ιB hc x := rfl

/-- ★★ **The algebra forcing transports to the composite arena.** The composite
arena's operator algebra, together with its two mode-local subalgebras,
satisfies the premises of `compositeAlgReconstruction` — the subalgebras
commute (`leftHomFin_comm_rightHomFin`) and generate (`composite_generate_fin`)
— so the landed forcing theorem applies and the composite algebra IS the
tensor product of the sector algebras:
`Matrix C₁ ⊗[ℂ] Matrix C₂ ≃ₐ[ℂ] Matrix C₁₂`. Not chosen: forced, by P2's own
arena-side locality and generation. -/
noncomputable def compositeArenaForced :
    (Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ
        ⊗[ℂ] Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ)
      ≃ₐ[ℂ] Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ :=
  haveI := card_config_neZero N K₁
  haveI := card_config_neZero N K₂
  haveI := matrix_config_nontrivial N (K₁ + K₂)
  (Algebra.TensorProduct.congr
      (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₁ N)))
      (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₂ N)))).trans
    (CSD.SigmaLayer.compositeAlgReconstruction
      (leftHomFin K₁ K₂ N) (rightHomFin K₁ K₂ N)
      (leftHomFin_comm_rightHomFin K₁ K₂ N) (composite_generate_fin K₁ K₂ N))

/-- The forced equivalence acts as the local product: `A ⊗ₜ B ↦ leftOp A ·
rightOp B`. The abstract forcing and the concrete mode-local embeddings agree
on the nose. -/
theorem compositeArenaForced_tmul
    (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (B : Matrix (FieldConfig K₂ N) (FieldConfig K₂ N) ℂ) :
    compositeArenaForced K₁ K₂ N (A ⊗ₜ[ℂ] B) = leftOp A * rightOp B := by
  have := card_config_neZero N K₁
  have := card_config_neZero N K₂
  have := matrix_config_nontrivial N (K₁ + K₂)
  rw [show compositeArenaForced K₁ K₂ N (A ⊗ₜ[ℂ] B)
      = (CSD.SigmaLayer.compositeAlgReconstruction
          (leftHomFin K₁ K₂ N) (rightHomFin K₁ K₂ N)
          (leftHomFin_comm_rightHomFin K₁ K₂ N) (composite_generate_fin K₁ K₂ N))
        ((Algebra.TensorProduct.congr
            (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₁ N)))
            (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (FieldConfig K₂ N))))
          (A ⊗ₜ[ℂ] B)) from rfl]
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    compositeAlgReconstruction_apply, CSD.SigmaLayer.reconMap_tmul,
    leftHomFin, rightHomFin, AlgHom.comp_apply, AlgHom.comp_apply,
    leftHom_apply, rightHom_apply]
  congr 1
  · congr 1
    simp
  · congr 1
    simp

omit [NeZero N] in
/-- The composite arena sits at exactly the forced dimension: the joint
configuration space has the product cardinality (the arena-side face of
`composite_dim_eq`). -/
theorem card_composite_config :
    Fintype.card (FieldConfig (K₁ + K₂) N)
      = Fintype.card (FieldConfig K₁ N) * Fintype.card (FieldConfig K₂ N) := by
  rw [Fintype.card_congr (configSplit (K₁ := K₁) (K₂ := K₂) (N := N))]
  exact Fintype.card_prod _ _

end Forced

end CSD.CV
