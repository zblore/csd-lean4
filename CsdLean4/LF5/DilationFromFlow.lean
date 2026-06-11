import CsdLean4.LF5.MeasurementFlow
import CsdLean4.LF4.POVMDilation

/-!
# LF5: de-isolation realises the Naimark dilation (LF5-C)

**Category:** 3-Local (LF5 measurement-dynamics layer).

This is **LF5-C** of `specs/lf5-plan.md`: the dilation isometry of the canonical
projective (computational-basis) measurement, **dynamically realised** by the von
Neumann coupling. The static, unmotivated Naimark embedding `V` of the LF4 POVM
tranche is here exhibited as

```
  V  =  U_vN ∘ (· ⊗ a₀)        (vnDilationV = vnUnitary * embedGround)
```

— embed the system in the apparatus ground state `a₀ = e₀`, then evolve by the
LF5-A von Neumann coupling unitary. The post-flow vector is the correlated state
`U_vN (ψ ⊗ a₀) = ∑ⱼ ψⱼ · (eⱼ ⊗ aⱼ)` (`vnDilationV_mulVec`), the pointer-outcome
regions are the **context-fixed apparatus blocks** `blockProj N i` (the apparatus
basis, not carved to Born), and the headline `vnNaimark` inhabits
`NaimarkDilation (basisPOVM N)`:

- `vnDilationV_isom`      — `Vᴴ V = 1` (the de-isolation embedding is isometric);
- `vnDilationV_pullback`  — `Vᴴ (blockProj N i) V = |eᵢ⟩⟨eᵢ|` (the crux: the
  context-fixed pointer block compresses to the projective effect);
- `measurementFlow_realises_dilation` — at the projective level, the LF5-B flow
  `Φ_vN` carries the embedded ray `[ψ ⊗ a₀]` exactly to the dilated ray `[Vψ]`,
  so the dilation is a *theorem of the dynamics*, not a gloss.

## Honest scope

Single-system projective tier (`basisPOVM`, the rank-1 computational-basis
measurement). The Born **number** is not re-derived here: downstream (LF5-D) it
comes from the existing FS-volume = Born engine; this module supplies the
*dynamical origin* of the dilation isometry that engine consumes. The FS
typicality law on the dilated sector (**A5**) is still posited, not derived.
Entangled / non-local de-isolation is deferred (`specs/lf5-plan.md` §0).

## LF5-D obstruction (recorded at planning, load-bearing)

The post-flow state `Vψ` has **zero amplitude on every off-diagonal cell**
`(j, k)` with `k ≠ j` (`vnDilationV_mulVec`). Hence the genericity hypothesis
`hpos` of `povm_born_eq_dilated_volume` / `povm_born_frequency_volume` (all
`N·N` dilated amplitudes nonzero) is **not satisfiable** at
`ψ' = piLpCongrLeft e (Vψ)` for `N ≥ 2` (at `N = 1` there is no off-diagonal
cell). LF5-D therefore cannot be a blind instantiation of
the P.3b/P.4 theorems: it needs either a zero-amplitude-tolerant volume reading
on the dilated space or a system-side reduction. `vnDilation_block_weight`
(block-`i` weight of the post-flow state = the Born weight `‖⟨eᵢ, ψ⟩‖²`) is the
Gleason-free analytic content already available on this side of that gap.

Reference: `specs/lf5-plan.md` (LF5-C).
-/

open Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4

/-! ## The computational-basis projective POVM -/

section BasisPOVM

variable {N : ℕ}

/-- **Rank-1 outer product of a basis vector is a matrix unit:**
`|eᵢ⟩⟨eᵢ| = single i i 1`. Entries: `(eᵢ)_a · star (eᵢ)_b = δ_{a i} δ_{b i}`. -/
lemma outerProduct_single (i : Fin N) :
    outerProduct (EuclideanSpace.single i (1 : ℂ)) = Matrix.single i i 1 := by
  ext a b
  simp only [outerProduct, Matrix.vecMulVec_apply, PiLp.single_apply,
    Matrix.single_apply]
  by_cases ha : a = i
  · by_cases hb : b = i
    · rw [if_pos ha, if_pos hb, star_one, one_mul, if_pos ⟨ha.symm, hb.symm⟩]
    · rw [if_neg hb, star_zero, mul_zero, if_neg (fun h => hb h.2.symm)]
  · rw [if_neg ha, zero_mul, if_neg (fun h => ha h.1.symm)]

/-- **The computational-basis projective POVM** `Eᵢ = |eᵢ⟩⟨eᵢ|`: the canonical
rank-1 projective measurement the von Neumann coupling reads out. Completeness
is `∑ᵢ |eᵢ⟩⟨eᵢ| = ∑ᵢ single i i 1 = 1`. -/
noncomputable def basisPOVM (N : ℕ) : POVM N (Fin N) where
  E i := rankOneEffect (EuclideanSpace.single i (1 : ℂ))
    (by rw [PiLp.norm_single]; exact norm_one)
  complete := by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) Matrix.sum_single_one
    exact outerProduct_single i

/-- The effect matrix of the basis POVM is the matrix unit `single i i 1`. -/
lemma basisPOVM_E_M (i : Fin N) :
    ((basisPOVM N).E i).M = Matrix.single i i 1 :=
  outerProduct_single i

/-- Action of the matrix unit `single i i 1` on a vector:
`(single i i 1 *ᵥ v) a = δ_{i a} · v i`. -/
private lemma single_one_mulVec_apply (i a : Fin N) (v : Fin N → ℂ) :
    (Matrix.single i i (1 : ℂ) *ᵥ v) a = if i = a then v i else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
  by_cases ha : i = a
  · rw [if_pos ha, Finset.sum_eq_single i]
    · rw [if_pos ⟨ha, rfl⟩, one_mul]
    · intro b _ hb
      rw [if_neg (fun h => hb h.2.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h => ha h.1), zero_mul]

/-- **Rank-1 Born weight of the basis POVM.** The `i`-th weight of preparation
`ψ` is the Born quadratic form `‖⟨eᵢ, ψ⟩‖²`. -/
theorem basisPOVM_weight (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (basisPOVM N).weight ψ i
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  have hinner : inner ℂ ψ (Matrix.toEuclideanLin (Matrix.single i i (1 : ℂ)) ψ)
      = ψ.ofLp i * star (ψ.ofLp i) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.toLin'_apply, Pi.star_apply]
      rw [single_one_mulVec_apply, if_pos rfl]
    · intro a _ ha
      simp only [Matrix.toLin'_apply, Pi.star_apply]
      rw [single_one_mulVec_apply, if_neg (Ne.symm ha), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  unfold POVM.weight
  rw [basisPOVM_E_M, hinner,
    show ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp i‖ ^ 2 from by
      rw [EuclideanSpace.inner_single_left, map_one, one_mul],
    ← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- Coordinate form of the basis-POVM Born weight: `pᵢ(ψ) = ‖ψᵢ‖²`. -/
theorem basisPOVM_weight_coord (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (basisPOVM N).weight ψ i = ‖ψ.ofLp i‖ ^ 2 := by
  rw [basisPOVM_weight, EuclideanSpace.inner_single_left, map_one, one_mul]

end BasisPOVM

/-! ## Isometry helper -/

/-- A matrix with `Aᴴ A = 1` induces a norm-preserving map on `EuclideanSpace`:
`‖Aψ‖² = re⟨Aψ, Aψ⟩ = re⟨ψ, Aᴴ A ψ⟩ = ‖ψ‖²` via the matrix↔operator adjoint
bridge. Generic helper (Mathlib upstream candidate). -/
lemma toEuclideanLin_norm_map_of_isom {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix κ ι ℂ} (hA : Aᴴ * A = 1)
    (ψ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin A ψ‖ = ‖ψ‖ := by
  have hinner : inner ℂ (Matrix.toEuclideanLin A ψ) (Matrix.toEuclideanLin A ψ)
      = inner ℂ ψ ψ := by
    rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A),
      show (Matrix.toEuclideanLin A).adjoint = Matrix.toEuclideanLin Aᴴ from
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm,
      show Matrix.toEuclideanLin Aᴴ (Matrix.toEuclideanLin A ψ)
          = Matrix.toEuclideanLin (Aᴴ * A) ψ from by
        simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply],
      hA,
      show Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) = LinearMap.id from
        Matrix.toLpLin_one 2,
      LinearMap.id_apply]
  have hsq : ‖Matrix.toEuclideanLin A ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-! ## The ground-state embedding `ψ ↦ ψ ⊗ a₀` -/

variable {N : ℕ} [NeZero N]

/-- **The ground-state embedding matrix** of `ψ ↦ ψ ⊗ a₀` (apparatus ground
`a₀ = e₀`): `(embedGround N)_{(j,k), m} = δ_{(j,k), (m,0)}`. -/
def embedGround (N : ℕ) [NeZero N] : Matrix (Fin N × Fin N) (Fin N) ℂ :=
  Matrix.of fun p m => if p = (m, 0) then 1 else 0

lemma embedGround_apply (p : Fin N × Fin N) (m : Fin N) :
    embedGround N p m = if p = (m, 0) then 1 else 0 := rfl

/-- Column `m` of the ground embedding is the dilated basis vector `e_{(m,0)}`
(system `m`, apparatus ground). -/
lemma embedGround_column (m : Fin N) :
    (fun p => embedGround N p m) = Pi.single ((m, 0) : Fin N × Fin N) (1 : ℂ) := by
  funext p
  rw [Pi.single_apply, embedGround_apply]

/-- **The embedded vector in coordinates:** `(ψ ⊗ a₀)_{(j,k)} = δ_{k,0} · ψⱼ`. -/
lemma embedGround_mulVec (v : Fin N → ℂ) (j k : Fin N) :
    (embedGround N *ᵥ v) (j, k) = if k = 0 then v j else 0 := by
  simp only [Matrix.mulVec, dotProduct, embedGround_apply, Prod.mk.injEq]
  by_cases hk : k = 0
  · rw [if_pos hk, Finset.sum_eq_single j]
    · rw [if_pos ⟨rfl, hk⟩, one_mul]
    · intro m _ hm
      rw [if_neg (fun h => hm h.1.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg (fun h => hk h.2), zero_mul]

/-- The ground embedding is an isometry: `embedᴴ embed = 1` (the columns
`e_{(m,0)}` are orthonormal). -/
theorem embedGround_isom : (embedGround N)ᴴ * embedGround N = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ p : Fin N × Fin N,
      (embedGround N)ᴴ a p * embedGround N p b
        = if p = (a, 0) ∧ p = (b, 0) then 1 else 0 := by
    intro p
    rw [Matrix.conjTranspose_apply, embedGround_apply, embedGround_apply]
    by_cases h1 : p = (a, 0)
    · rw [if_pos h1, star_one, one_mul]
      by_cases h2 : p = (b, 0)
      · rw [if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg h1, star_zero, zero_mul, if_neg (fun h => h1 h.1)]
  simp only [hterm]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single ((a, 0) : Fin N × Fin N)]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro p _ hp
      rw [if_neg (fun h => hp h.1)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro p _
    exact if_neg (fun h => hab (congrArg Prod.fst (h.1.symm.trans h.2)))

/-- Operator-level isometry of the ground embedding: `‖ψ ⊗ a₀‖ = ‖ψ‖`. -/
theorem embedGround_norm_map (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖Matrix.toEuclideanLin (embedGround N) ψ‖ = ‖ψ‖ :=
  toEuclideanLin_norm_map_of_isom embedGround_isom ψ

/-! ## The dynamically-realised dilation isometry `V = U_vN ∘ (· ⊗ a₀)` -/

/-- **The dynamically-realised Naimark dilation isometry**
`V = U_vN ∘ (· ⊗ a₀)`: embed the system in the apparatus ground state, then
evolve by the LF5-A von Neumann coupling. This replaces the unmotivated static
Naimark embedding of the LF4 POVM tranche with the de-isolation dynamics. -/
noncomputable def vnDilationV (N : ℕ) [NeZero N] :
    Matrix (Fin N × Fin N) (Fin N) ℂ :=
  vnUnitary N * embedGround N

/-- Column `m` of `V` is the correlated basis vector `e_{(m,m)}`: the coupling
sends `e_m ⊗ a₀` to `e_m ⊗ a_m` (`vnUnitary_mulVec_ground`). -/
lemma vnDilationV_column (m : Fin N) :
    (fun p => vnDilationV N p m) = Pi.single ((m, m) : Fin N × Fin N) (1 : ℂ) := by
  have h : (fun p => vnDilationV N p m)
      = vnUnitary N *ᵥ fun q => embedGround N q m := by
    funext p
    rw [show vnDilationV N = vnUnitary N * embedGround N from rfl, Matrix.mul_apply]
    rfl
  rw [h, embedGround_column, vnUnitary_mulVec_ground]

/-- **Entry formula:** `V_{p, m} = δ_{p, (m,m)}`. -/
lemma vnDilationV_apply (p : Fin N × Fin N) (m : Fin N) :
    vnDilationV N p m = if p = (m, m) then 1 else 0 := by
  have h := congrFun (vnDilationV_column (N := N) m) p
  rwa [Pi.single_apply] at h

/-- The dynamical reading of `V`, explicit: `V ψ = U_vN (ψ ⊗ a₀)` at the
`mulVec` level. -/
lemma vnDilationV_mulVec_eq (v : Fin N → ℂ) :
    vnDilationV N *ᵥ v = vnUnitary N *ᵥ (embedGround N *ᵥ v) :=
  (Matrix.mulVec_mulVec v (vnUnitary N) (embedGround N)).symm

/-- **The post-flow vector in coordinates:**
`U_vN (ψ ⊗ a₀) = ∑ⱼ ψⱼ · (eⱼ ⊗ aⱼ)`, i.e. `(Vψ)_{(j,k)} = δ_{k j} · ψⱼ`. The
system and the apparatus pointer are perfectly correlated; every off-diagonal
cell `(j, k)`, `k ≠ j`, carries zero amplitude (the LF5-D `hpos` obstruction
recorded in the module docstring). -/
lemma vnDilationV_mulVec (v : Fin N → ℂ) (j k : Fin N) :
    (vnDilationV N *ᵥ v) (j, k) = if k = j then v j else 0 := by
  simp only [Matrix.mulVec, dotProduct, vnDilationV_apply, Prod.mk.injEq]
  by_cases hk : k = j
  · rw [if_pos hk, Finset.sum_eq_single j]
    · rw [if_pos ⟨rfl, hk⟩, one_mul]
    · intro b _ hb
      rw [if_neg (fun h => hb h.1.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h => hk (h.2.trans h.1.symm)), zero_mul]

/-- **`V` is an isometry:** `Vᴴ V = embedᴴ (U_vNᴴ U_vN) embed = embedᴴ embed = 1`
(unitarity of the coupling + isometry of the ground embedding). -/
theorem vnDilationV_isom : (vnDilationV N)ᴴ * vnDilationV N = 1 := by
  rw [show vnDilationV N = vnUnitary N * embedGround N from rfl,
    Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (vnUnitary N)ᴴ (vnUnitary N) (embedGround N),
    vnUnitary_unitary, Matrix.one_mul, embedGround_isom]

/-- Operator-level isometry: `‖Vψ‖ = ‖ψ‖` (feeds LF5-D's `hnorm`). -/
theorem vnDilationV_norm_map (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖Matrix.toEuclideanLin (vnDilationV N) ψ‖ = ‖ψ‖ :=
  toEuclideanLin_norm_map_of_isom vnDilationV_isom ψ

/-- The pointer-`i` block projector acting on `V`:
`(Πᵢ V)_{(n,j), m} = δ_{j i} δ_{n m} δ_{m i}` — only the `(i, i)` cell of
column `i` survives. -/
lemma blockProj_mul_vnDilationV (i n j m : Fin N) :
    (blockProj N i * vnDilationV N) (n, j) m
      = if j = i ∧ n = m ∧ i = m then 1 else 0 := by
  have hrw : (blockProj N i * vnDilationV N) (n, j) m
      = (blockProj N i *ᵥ fun q => vnDilationV N q m) (n, j) := by
    rw [Matrix.mul_apply]; rfl
  rw [hrw, blockProj_mulVec]
  by_cases hj : j = i
  · rw [if_pos hj, vnDilationV_apply]
    by_cases hc : n = m ∧ i = m
    · rw [if_pos (show ((n, i) : Fin N × Fin N) = (m, m) from by rw [hc.1, hc.2]),
        if_pos ⟨hj, hc⟩]
    · rw [if_neg (fun h => hc ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩),
        if_neg (fun h => hc h.2)]
  · rw [if_neg hj, if_neg (fun h => hj h.1)]

/-- **The Naimark pullback, dynamically realised (the LF5-C crux):** the
context-fixed pointer block compresses through the de-isolation isometry to the
projective effect, `Vᴴ (blockProj N i) V = |eᵢ⟩⟨eᵢ|`. -/
theorem vnDilationV_pullback (i : Fin N) :
    (vnDilationV N)ᴴ * blockProj N i * vnDilationV N = ((basisPOVM N).E i).M := by
  rw [basisPOVM_E_M, Matrix.mul_assoc]
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hterm : ∀ n j : Fin N,
      (vnDilationV N)ᴴ a (n, j) * (blockProj N i * vnDilationV N) (n, j) b
        = if (n, j) = ((a, a) : Fin N × Fin N) ∧ (j = i ∧ n = b ∧ i = b)
            then 1 else 0 := by
    intro n j
    rw [Matrix.conjTranspose_apply, vnDilationV_apply, blockProj_mul_vnDilationV]
    by_cases h1 : (n, j) = ((a, a) : Fin N × Fin N)
    · rw [if_pos h1, star_one, one_mul]
      exact (if_congr (and_iff_right h1) rfl rfl).symm
    · rw [if_neg h1, star_zero, zero_mul, if_neg (fun h => h1 h.1)]
  simp only [hterm]
  rw [Matrix.single_apply]
  by_cases hab : i = a ∧ i = b
  · obtain ⟨ha, hb⟩ := hab
    rw [if_pos ⟨ha, hb⟩, Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · rw [if_pos ⟨rfl, ha.symm, ha.symm.trans hb, hb⟩]
      · intro j _ hj
        rw [if_neg (fun h => hj (congrArg Prod.snd h.1))]
      · intro h; exact absurd (Finset.mem_univ a) h
    · intro n _ hn
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hn (congrArg Prod.fst h.1))]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro n _
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (fun h =>
      hab ⟨h.2.1.symm.trans (congrArg Prod.snd h.1), h.2.2.2⟩)

/-- **The LF5-C headline: the canonical projective measurement's Naimark
dilation, dynamically realised by the von Neumann coupling.** The dilation
isometry is `V = U_vN ∘ (· ⊗ a₀)` — measurement-flow dynamics, not a static
embedding — and the pointer regions are the context-fixed apparatus blocks. -/
noncomputable def vnNaimark (N : ℕ) [NeZero N] : NaimarkDilation (basisPOVM N) :=
  ⟨vnDilationV N, vnDilationV_isom, vnDilationV_pullback⟩

/-- **Block-`i` weight of the post-flow state = the Born weight.** The dilated
projective Born weight of `Vψ = U_vN (ψ ⊗ a₀)` against the context-fixed
pointer block `Πᵢ` is `‖⟨eᵢ, ψ⟩‖²`. Composes the Naimark Born transfer with the
rank-1 basis-POVM weight; Gleason-free. -/
theorem vnDilation_block_weight (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    RCLike.re (inner ℂ (Matrix.toEuclideanLin (vnDilationV N) ψ)
        (Matrix.toEuclideanLin (blockProj N i)
          (Matrix.toEuclideanLin (vnDilationV N) ψ)))
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 :=
  ((vnNaimark N).born_transfer (basisPOVM N) ψ i).symm.trans (basisPOVM_weight ψ i)

/-! ## The LF5-B flow realises the dilation at the projective level -/

/-- Operator form of the factorisation `V = U_vN ∘ (· ⊗ a₀)`. -/
lemma toEuclideanLin_vnDilationV (ψ : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (vnDilationV N) ψ
      = Matrix.toEuclideanLin (vnUnitary N)
          (Matrix.toEuclideanLin (embedGround N) ψ) := by
  rw [show vnDilationV N = vnUnitary N * embedGround N from rfl]
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

omit [NeZero N] in
/-- **Reindex naturality:** transporting a matrix along `e` and a vector along
the `piLpCongrLeft e` isometry commutes with `toEuclideanLin`. Reduces to
`Matrix.submatrix_mulVec_equiv` at the function level. -/
lemma toEuclideanLin_reindex_piLpCongrLeft {m : ℕ} (e : Fin N × Fin N ≃ Fin m)
    (A : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
    (w : EuclideanSpace ℂ (Fin N × Fin N)) :
    Matrix.toEuclideanLin (Matrix.reindex e e A)
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e) w)
      = (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
          (Matrix.toEuclideanLin A w) := by
  show WithLp.toLp 2 (Matrix.reindex e e A *ᵥ (WithLp.ofLp w ∘ ⇑e.symm))
      = (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e) (Matrix.toEuclideanLin A w)
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rfl

/-- The reindexed post-flow vector is the reindexed coupling applied to the
reindexed embedded vector: the vector-level identity behind
`measurementFlow_realises_dilation`. -/
lemma piLpCongrLeft_vnDilationV {m : ℕ} (e : Fin N × Fin N ≃ Fin m)
    (ψ : EuclideanSpace ℂ (Fin N)) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanLin (vnDilationV N) ψ)
      = Matrix.toEuclideanLin (vnUnitaryReindexed N e).val
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
            (Matrix.toEuclideanLin (embedGround N) ψ)) := by
  rw [vnUnitaryReindexed_val, toEuclideanLin_reindex_piLpCongrLeft]
  exact congrArg _ (toEuclideanLin_vnDilationV ψ)

/-- The embedded vector of a nonzero preparation is nonzero. -/
lemma toEuclideanLin_embedGround_ne_zero (ψ : EuclideanSpace ℂ (Fin N))
    (hψ : ψ ≠ 0) : Matrix.toEuclideanLin (embedGround N) ψ ≠ 0 := by
  intro h
  apply hψ
  have hn := embedGround_norm_map (N := N) ψ
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The post-flow vector of a nonzero preparation is nonzero. -/
lemma toEuclideanLin_vnDilationV_ne_zero (ψ : EuclideanSpace ℂ (Fin N))
    (hψ : ψ ≠ 0) : Matrix.toEuclideanLin (vnDilationV N) ψ ≠ 0 := by
  intro h
  apply hψ
  have hn := vnDilationV_norm_map (N := N) ψ
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The reindexed embedded vector is nonzero (`piLpCongrLeft` is an isometry). -/
lemma piLpCongrLeft_embedGround_ne_zero {m : ℕ} (e : Fin N × Fin N ≃ Fin m)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanLin (embedGround N) ψ) ≠ 0 := by
  intro h
  apply toEuclideanLin_embedGround_ne_zero ψ hψ
  have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
    (Matrix.toEuclideanLin (embedGround N) ψ)
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The reindexed post-flow vector is nonzero. -/
lemma piLpCongrLeft_vnDilationV_ne_zero {m : ℕ} (e : Fin N × Fin N ≃ Fin m)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanLin (vnDilationV N) ψ) ≠ 0 := by
  intro h
  apply toEuclideanLin_vnDilationV_ne_zero ψ hψ
  have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
    (Matrix.toEuclideanLin (vnDilationV N) ψ)
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- **The flow ↔ dilation tie:** at the projective level, the LF5-B measurement
flow `Φ_vN` carries the embedded ray `[ψ ⊗ a₀]` exactly to the dilated ray
`[Vψ]`. The Naimark dilation consumed by the LF4 POVM volume engine is therefore
*dynamically realised* by the de-isolation flow — a theorem tying the flow to
the dilation, not a gloss. (The mathematical crux of the tranche is
`vnDilationV_pullback`; this theorem's content is the reindex naturality plus
the definitional factorisation `V = U_vN · embed`.) -/
theorem measurementFlow_realises_dilation {m : ℕ} (e : Fin N × Fin N ≃ Fin m)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0) :
    measurementFlow N e
        (Projectivization.mk ℂ
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
            (Matrix.toEuclideanLin (embedGround N) ψ))
          (piLpCongrLeft_embedGround_ne_zero e ψ hψ))
      = Projectivization.mk ℂ
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
            (Matrix.toEuclideanLin (vnDilationV N) ψ))
          (piLpCongrLeft_vnDilationV_ne_zero e ψ hψ) := by
  haveI : NeZero m := ⟨fun h => Fin.elim0 (h ▸ e ((0 : Fin N), 0))⟩
  rw [measurementFlow_apply]
  refine (smul_mk_eq_mk (vnUnitaryReindexed N e) _
      (piLpCongrLeft_embedGround_ne_zero e ψ hψ)).trans ?_
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _
      (piLpCongrLeft_vnDilationV_ne_zero e ψ hψ)).mpr
    ⟨1, by rw [one_smul]; exact piLpCongrLeft_vnDilationV e ψ⟩

end LF5
end CSD
