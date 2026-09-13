/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Channel
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Broadcasting: the BCFJS theorem, states can be broadcast iff they commute

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Row **BC** of
`specs/BACKLOG.md` (the BCFJS `iff` of `Empirical/QM/NoBroadcasting.lean`), milestones BC1–BC6: complete.

A channel `Φ : ℂⁿ → ℂⁿ ⊗ ℂⁿ` **broadcasts** `ρ` when both marginals of `Φ ρ` are `ρ`
(`Channel.Broadcasts`). Barnum–Caves–Fuchs–Jozsa–Schumacher (1996): a pair of states can be
broadcast by one channel iff they commute. This file proves both halves: the constructive half by
the classical copier in a joint eigenbasis, and the hard half by an elementary route through
support confinement (no fidelity, no relative entropy), assembled by induction on rank.

* `Channel.Broadcasts`, with `Broadcasts.add`, `.smul`, `.sub` — the condition is linear in
  the state, so a broadcaster of two states broadcasts their whole span;
* `Matrix.PosSemidef.mul_mul_conjTranspose_eq_zero_iff`, `Matrix.PosSemidef.eq_zero_of_sum_eq_zero`
  — the two positive-semidefinite squeezes the argument uses;
* ★ `Channel.Broadcasts.kronecker_mul_kraus_mul` — **support confinement**: if `Φ` broadcasts the
  positive semidefinite `ρ` and `P` is a projector with `P ρ = ρ`, every Kraus operator maps the
  range of `ρ` into `range P ⊗ range P`, `(P ⊗ P) Kᵢ ρ = Kᵢ ρ` (the compressed output
  `(Q ⊗ 1) Φ(ρ) (Q ⊗ 1)` has trace `Tr(ρ Q) = 0`, so it and each Kraus term vanish);
* `onbVec`, `onbProj`, `sum_onbProj` — an orthonormal basis of `ℂⁿ` as coordinate vectors, its
  rank-one projectors, and completeness; `copierKraus`, `copierChannel` — **the classical copier**
  `X ↦ ∑ₖ ⟨b k|X|b k⟩ · |b k b k⟩⟨b k b k|`, a channel; ★ `copierChannel_broadcasts` — it
  broadcasts every matrix diagonal in its basis;
* ★ `exists_orthonormalBasis_mulVec_eq_smul_of_commute` — **two commuting Hermitian matrices
  have a joint orthonormal eigenbasis** (Mathlib's joint eigenspace decomposition
  `LinearMap.IsSymmetric.directSum_isInternal_of_commute`, restricted to the finitely many
  eigenvalue pairs and collected into a basis);
* ★★ `exists_channel_broadcasts_of_commute` — **commuting Hermitian matrices can be broadcast**
  (BC1, the easy half of BCFJS);
* ★★ `Channel.Broadcasts.star_dotProduct_eq_zero_or_norm_eq_one` — **two broadcast pure states are
  orthogonal or parallel** (BC2): a broadcast pure state is cloned
  (`Broadcasts.kraus_mulVec_eq_smul_kronVec`, from support confinement with the rank-one
  projector), and trace preservation read on the two vectors
  (`Channel.star_dotProduct_eq_sum_kraus`) gives `⟨φ|ψ⟩ = ⟨φ|ψ⟩² ∑ᵢ conj bᵢ aᵢ` with
  `|∑ᵢ conj bᵢ aᵢ| ≤ 1` by Cauchy–Schwarz (`norm_star_dotProduct_sq_le`). This is the
  no-cloning theorem at channel level, and the rank-one case of the hard half;
* `suppProj A` — **the support projector**, the orthogonal projector onto the range of `A`
  (`Submodule.starProjection` read as a matrix): Hermitian, idempotent, `suppProj A * A = A`, and
  `suppProj A x = x ↔ x ∈ range A` (`suppProj_mulVec_eq_self_iff`);
* `nsq` (the squared norm `Re ⟨v|v⟩`), `IsHermitian.exists_top_eigenvalue` — the top eigenvalue
  of a Hermitian matrix bounds its Rayleigh quotient and is attained by a unit eigenvector;
  `nsq_proj_mulVec_le`, `proj_mulVec_eq_self_of_nsq_eq` — a projector contracts, with equality
  only on its range; `re_star_dotProduct_kronecker_mulVec_le` — **the tensor bound**
  `⟨x|Q ⊗ Q|x⟩ ≤ μ² ‖x‖²` from `⟨z|Q|z⟩ ≤ μ ‖z‖²`, through the identity
  `μ² − Q ⊗ Q = μ (μ − Q) ⊗ 1 + Q ⊗ (μ − Q)`;
* ★★ `Channel.Broadcasts.mul_eq_zero_of_range_disjoint` — **BC3: broadcast states with disjoint
  supports have orthogonal supports**, `B A = 0`. With `Q = P_A P_B P_A` and its top eigenvalue
  `μ`, attained at `u ∈ range A`, and `w = P_B u ∈ range B`: `μ = ⟨w|u⟩ = ∑ᵢ ⟨Kᵢ w|Kᵢ u⟩`, each
  term is `⟨Kᵢ w|(G ⊗ G) Kᵢ u⟩` by confinement, the tensor bound and Cauchy–Schwarz give
  `μ ≤ μ √μ`, so `μ ∈ {0, 1}`; `μ = 1` would put `u` in both ranges. BC2 is the rank-one case;
* `Matrix.PosSemidef.mul_eq_zero_of_trace_mul_eq_zero` (two positive semidefinite matrices with
  `Tr (X Y) = 0` have `X Y = 0`), `Channel.star_dotProduct_adjoint_mulVec`
  (`⟨v|Φ† P|v⟩ = ∑ᵢ ⟨Kᵢ v|P|Kᵢ v⟩`), `Channel.adjoint_kronecker_one_mulVec_eq_self` (the dual of
  `P ⊗ 1` fixes a vector whose Kraus images lie in `range P ⊗ ℂⁿ`), and the partial-trace
  identity `traceRight_kronecker_mul_mul_kronecker`,
  `Tr_B ((A ⊗ B) Y (C ⊗ D)) = A · Tr_B (Y (1 ⊗ D B)) · C` (with its `traceLeft` twin);
* ★ `Channel.Broadcasts.kronecker_mulVec_kraus_mulVec_sub` — **BC4 (i)**: if `Φ` broadcasts the
  positive semidefinite `τ` and every Kraus operator maps a subspace `V ⊆ supp τ` into `V ⊗ V`,
  then it maps `W = supp τ ⊖ V` into `W ⊗ W`: the dual `Φ† (P_V ⊗ 1)` fixes `V`, so its excess
  over `P_V` is positive semidefinite with zero trace against `τ` and kills the support;
* ★★ `Channel.Broadcasts.block_split` — **BC4: a cloned subspace splits a broadcast state into
  blocks, each broadcast**: `P_V τ P_W = 0`, and `Φ` broadcasts `P_V τ P_V` and `P_W τ P_W`. The
  cross blocks `Φ (P_V τ P_W)` are sandwiched between `P_V ⊗ P_V` and `P_W ⊗ P_W`
  (`kraus_block_sandwich`), whose partial traces vanish because `P_W P_V = 0`;
* `onbProjSet` (the projector onto the span of a subfamily of an orthonormal basis, with
  `onbProjSet_mul_self` and `star_dotProduct_onbProjSet_mulVec`), `nsq_eq_sum_onb` (Parseval),
  `re_star_dotProduct_mulVec_eq_sum_onb` (the Rayleigh quotient of a diagonalised matrix);
* ★★ `exists_boundary_point` — **BC5: the segment through two distinct states meets the boundary
  of the cone**: for positive semidefinite `ρ ≠ σ` of trace one there is `l ≥ 1` with
  `σ + l (ρ − σ)` positive semidefinite and a kernel vector outside `ker (ρ + σ)`. The admissible
  `l` form a closed bounded set (the traceless `ρ − σ` has a negative direction); at its
  supremum, a missing kernel vector would let the eigenvalue-`0` eigenvectors (which lie in
  `ker (ρ + σ)`, hence in `ker (ρ − σ)`) and the positive eigenvalues absorb a further step
  `δ = ε / (μ + 1)`, contradicting maximality;
* `suppProj_mulVec_eq_zero_iff` (the support projector of a Hermitian matrix vanishes exactly on
  its kernel), `Matrix.PosSemidef.add_mulVec_eq_zero_iff` (a positive combination of positive
  semidefinite matrices vanishes on `x` iff both do), `rank_lt_rank_of_ker` (**a strict kernel
  inclusion is a strict rank inequality**, by rank–nullity); `interProj P₁ P₂` — **the projector
  onto the intersection of two ranges**, `1 − suppProj ((1 − P₁) + (1 − P₂))`, with
  `interProj_mulVec_eq_self_iff` and `mul_interProj`; `interProj_kronecker_mulVec_eq_self` —
  **intersections of tensor squares**: a vector in `S₁ ⊗ S₁` and in `S₂ ⊗ S₂` lies in
  `(S₁ ∩ S₂) ⊗ (S₁ ∩ S₂)` (column by column, row by row);
* ★★★ `Channel.Broadcasts.mul_comm_of_posSemidef` — **BC6, the hard half of BCFJS: broadcast
  states commute.** Strong induction on `rank (ρ + σ)`: normalise to trace one
  (`Matrix.PosSemidef.exists_smul_trace_one`); take the two boundary points `τ₁, τ₂` of the
  segment (BC5), broadcast by linearity, with `[τ₁, τ₂] = (l₁ + l₂ − 1) [ρ, σ]`; with `V` the
  intersection of their supports, either `V = 0` and BC3 gives `τ₁ τ₂ = 0 = τ₂ τ₁`, or `V ≠ 0` is
  cloned by every Kraus operator, BC4 splits each `τᵢ` into a `V`-block and a complementary
  block, the two pairs of blocks are broadcast with strictly smaller rank of their sum
  (witnessed by the BC5 kernel vector and by a vector of `V`), so they commute by induction, and
  the cross products vanish;
* ★★★ `exists_channel_broadcasts_iff_commute` — **BCFJS: two positive semidefinite matrices can
  be broadcast by a single channel iff they commute** (BC1 and BC6);
* `exists_orthonormalBasis_mulVec_eq_smul_of_pairwise_commute` (a pairwise-commuting family of
  Hermitian matrices has a joint orthonormal eigenbasis), ★★
  `exists_channel_broadcasts_of_pairwise_commute`, and ★★★
  `exists_channel_broadcasts_family_iff_pairwise_commute` — **BCFJS for finite families**: a
  finite family of positive semidefinite matrices can be broadcast by a single channel iff its
  members pairwise commute (the copier in a joint eigenbasis one way, the pair theorem applied
  pairwise the other).

## Provenance

The literature proves the hard half through fidelity monotonicity (BCFJS 1996) or the equality
case of the relative-entropy data-processing inequality (Lindblad 1999). Neither is in Mathlib or
in this corpus, and neither is used here: the route above needs only support confinement, trace
preservation and elementary matrix analysis. Row **BC** of `specs/BACKLOG.md` records the
milestones BC1–BC6.

## Source

Barnum, Caves, Fuchs, Jozsa, Schumacher, *Phys. Rev. Lett.* **76**, 2818 (1996).
-/

@[expose] public section

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Function

namespace Matrix
variable {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R]

/-- **Partial trace over the first factor is a left module map over `I ⊗ X`.**
`traceLeft ((I ⊗ₖ X) · M) = X · traceLeft M`. -/
theorem traceLeft_one_kronecker_mul [DecidableEq m]
    (X : Matrix n n R) (M : Matrix (m × n) (m × n) R) :
    traceLeft (((1 : Matrix m m R) ⊗ₖ X) * M) = X * traceLeft M := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [traceLeft_apply, Matrix.mul_apply, Matrix.kronecker_apply, one_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, one_mul, Finset.mul_sum]
  have hk : ∀ k : m, (∑ x : m, ∑ y : n, if k = x then X i y * M (x, y) (k, j) else 0)
      = ∑ y : n, X i y * M (k, y) (k, j) := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_ite_eq]
    simp
  simp only [hk]
  exact Finset.sum_comm

/-- **Partial trace over the first factor is a right module map over `I ⊗ X`.**
`traceLeft (M · (I ⊗ₖ X)) = traceLeft M · X`. -/
theorem traceLeft_mul_one_kronecker [DecidableEq m]
    (M : Matrix (m × n) (m × n) R) (X : Matrix n n R) :
    traceLeft (M * ((1 : Matrix m m R) ⊗ₖ X)) = traceLeft M * X := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [traceLeft_apply, Matrix.mul_apply, Matrix.kronecker_apply, one_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, zero_mul, one_mul, mul_zero, Finset.sum_mul]
  have hk : ∀ k : m, (∑ x : m, ∑ y : n, if x = k then M (k, i) (x, y) * X y j else 0)
      = ∑ y : n, M (k, i) (k, y) * X y j := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_ite_eq']
    simp
  simp only [hk]
  exact Finset.sum_comm

end Matrix

namespace QuantumInfo

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- A channel `Φ : ℂⁿ → ℂⁿ ⊗ ℂⁿ` **broadcasts** `ρ` when both marginals of `Φ ρ` are `ρ`. -/
def Channel.Broadcasts (Φ : Channel n (n × n) ι) (ρ : Matrix n n ℂ) : Prop :=
  traceRight (Φ.apply ρ) = ρ ∧ traceLeft (Φ.apply ρ) = ρ

namespace Channel.Broadcasts

variable {Φ : Channel n (n × n) ι} {ρ σ : Matrix n n ℂ}

theorem add (hρ : Φ.Broadcasts ρ) (hσ : Φ.Broadcasts σ) : Φ.Broadcasts (ρ + σ) := by
  refine ⟨?_, ?_⟩
  · rw [Channel.apply_add, traceRight_add, hρ.1, hσ.1]
  · rw [Channel.apply_add, traceLeft_add, hρ.2, hσ.2]

theorem smul (hρ : Φ.Broadcasts ρ) (c : ℂ) : Φ.Broadcasts (c • ρ) := by
  refine ⟨?_, ?_⟩
  · rw [Channel.apply_smul, traceRight_smul, hρ.1]
  · rw [Channel.apply_smul, traceLeft_smul, hρ.2]

theorem sub (hρ : Φ.Broadcasts ρ) (hσ : Φ.Broadcasts σ) : Φ.Broadcasts (ρ - σ) := by
  refine ⟨?_, ?_⟩
  · rw [Channel.apply_sub, traceRight_sub, hρ.1, hσ.1]
  · rw [Channel.apply_sub, traceLeft_sub, hρ.2, hσ.2]

end Channel.Broadcasts

/-- For `ρ` positive semidefinite, `L ρ Lᴴ = 0` forces `L ρ = 0`: write `ρ = Bᴴ B`, so
`L ρ Lᴴ = (L Bᴴ)(L Bᴴ)ᴴ`. -/
theorem _root_.Matrix.PosSemidef.mul_mul_conjTranspose_eq_zero_iff {m : Type*}
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (L : Matrix m n ℂ) :
    L * ρ * Lᴴ = 0 ↔ L * ρ = 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  rw [star_eq_conjTranspose] at hB
  subst hB
  constructor
  · intro h
    have h1 : (L * Bᴴ) * (L * Bᴴ)ᴴ = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]
      simpa [Matrix.mul_assoc] using h
    have h2 : L * Bᴴ = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp h1
    rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
  · intro h
    rw [h, Matrix.zero_mul]

namespace Channel.Broadcasts

variable {Φ : Channel n (n × n) ι} {ρ : Matrix n n ℂ}

/-- A finite sum of positive semidefinite matrices that vanishes has every term zero. -/
theorem _root_.Matrix.PosSemidef.eq_zero_of_sum_eq_zero {m : Type*} [Fintype m]
    {T : ι → Matrix m m ℂ} (hT : ∀ i, (T i).PosSemidef) (h : ∑ i, T i = 0) (i : ι) : T i = 0 := by
  have htr : ∑ j, (T j).trace = 0 := by rw [← Matrix.trace_sum, h, Matrix.trace_zero]
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (T j).trace := fun j _ => (hT j).trace_nonneg
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr i (Finset.mem_univ i)
  exact ((hT i).trace_eq_zero_iff).mp this

/-- **Support confinement, first factor.** If `Φ` broadcasts the positive semidefinite `ρ` and
`P` is a projector with `P ρ = ρ`, then every Kraus operator maps the range of `ρ` into
`range P ⊗ ℂⁿ`: `(P ⊗ 1) Kᵢ ρ = Kᵢ ρ`. -/
theorem kronecker_one_mul_kraus_mul (h : Φ.Broadcasts ρ) (hρ : ρ.PosSemidef)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) (hPρ : P * ρ = ρ) (i : ι) :
    (P ⊗ₖ (1 : Matrix n n ℂ)) * (Φ.kraus i * ρ) = Φ.kraus i * ρ := by
  set Q : Matrix n n ℂ := 1 - P with hQ
  set K : Matrix (n × n) (n × n) ℂ := Q ⊗ₖ (1 : Matrix n n ℂ) with hK
  have hρP : ρ * P = ρ := by
    have := congrArg conjTranspose hPρ
    rwa [conjTranspose_mul, hP.eq, hρ.1.eq] at this
  have hρQ : ρ * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, hρP, sub_self]
  have hQ_herm : Q.IsHermitian := isHermitian_one.sub hP
  have hQ2 : Q * Q = Q := by
    rw [hQ, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hP2]
    abel
  have hK_herm : K.IsHermitian := by
    rw [hK, IsHermitian, conjTranspose_kronecker, conjTranspose_one, hQ_herm.eq]
  have hK2 : K * K = K := by rw [hK, ← mul_kronecker_mul, hQ2, Matrix.one_mul]
  -- the compressed output has trace zero, hence vanishes
  have htr : (K * Φ.apply ρ * K).trace = 0 := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm K, Matrix.mul_assoc, hK2, hK,
      ← trace_traceRight, traceRight_mul_kronecker_one, h.1, hρQ, trace_zero]
  have hpsd : (K * Φ.apply ρ * K).PosSemidef := by
    have := (Φ.apply_posSemidef hρ).conjTranspose_mul_mul_same K
    rwa [hK_herm.eq] at this
  have hKRK : K * Φ.apply ρ * K = 0 := (hpsd.trace_eq_zero_iff).mp htr
  -- each Kraus term is compressed to zero
  have hterm : ∀ j, K * (Φ.kraus j * ρ * (Φ.kraus j)ᴴ) * K = 0 := by
    refine Matrix.PosSemidef.eq_zero_of_sum_eq_zero (fun j => ?_) ?_
    · have := (hρ.mul_mul_conjTranspose_same (Φ.kraus j)).conjTranspose_mul_mul_same K
      rwa [hK_herm.eq] at this
    · rw [← hKRK, Channel.apply_def, Finset.mul_sum, Finset.sum_mul]
  have hi : (K * Φ.kraus i) * ρ * (K * Φ.kraus i)ᴴ = 0 := by
    rw [conjTranspose_mul, hK_herm.eq]
    simpa [Matrix.mul_assoc] using hterm i
  have hKKρ : K * Φ.kraus i * ρ = 0 := (hρ.mul_mul_conjTranspose_eq_zero_iff _).mp hi
  -- `K = 1 - P ⊗ 1`
  have hK1 : K = 1 - P ⊗ₖ (1 : Matrix n n ℂ) := by
    rw [hK, hQ, sub_eq_add_neg, add_kronecker, one_kronecker_one, ← neg_one_smul ℂ P,
      smul_kronecker, neg_one_smul, sub_eq_add_neg]
  rw [hK1, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc] at hKKρ
  exact (sub_eq_zero.mp hKKρ).symm

/-- **Support confinement, second factor**: `(1 ⊗ P) Kᵢ ρ = Kᵢ ρ`. -/
theorem one_kronecker_mul_kraus_mul (h : Φ.Broadcasts ρ) (hρ : ρ.PosSemidef)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) (hPρ : P * ρ = ρ) (i : ι) :
    ((1 : Matrix n n ℂ) ⊗ₖ P) * (Φ.kraus i * ρ) = Φ.kraus i * ρ := by
  set Q : Matrix n n ℂ := 1 - P with hQ
  set K : Matrix (n × n) (n × n) ℂ := (1 : Matrix n n ℂ) ⊗ₖ Q with hK
  have hρP : ρ * P = ρ := by
    have := congrArg conjTranspose hPρ
    rwa [conjTranspose_mul, hP.eq, hρ.1.eq] at this
  have hρQ : ρ * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, hρP, sub_self]
  have hQ_herm : Q.IsHermitian := isHermitian_one.sub hP
  have hQ2 : Q * Q = Q := by
    rw [hQ, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hP2]
    abel
  have hK_herm : K.IsHermitian := by
    rw [hK, IsHermitian, conjTranspose_kronecker, conjTranspose_one, hQ_herm.eq]
  have hK2 : K * K = K := by rw [hK, ← mul_kronecker_mul, hQ2, Matrix.one_mul]
  have htr : (K * Φ.apply ρ * K).trace = 0 := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm K, Matrix.mul_assoc, hK2, hK,
      ← trace_traceLeft, traceLeft_mul_one_kronecker, h.2, hρQ, trace_zero]
  have hpsd : (K * Φ.apply ρ * K).PosSemidef := by
    have := (Φ.apply_posSemidef hρ).conjTranspose_mul_mul_same K
    rwa [hK_herm.eq] at this
  have hKRK : K * Φ.apply ρ * K = 0 := (hpsd.trace_eq_zero_iff).mp htr
  have hterm : ∀ j, K * (Φ.kraus j * ρ * (Φ.kraus j)ᴴ) * K = 0 := by
    refine Matrix.PosSemidef.eq_zero_of_sum_eq_zero (fun j => ?_) ?_
    · have := (hρ.mul_mul_conjTranspose_same (Φ.kraus j)).conjTranspose_mul_mul_same K
      rwa [hK_herm.eq] at this
    · rw [← hKRK, Channel.apply_def, Finset.mul_sum, Finset.sum_mul]
  have hi : (K * Φ.kraus i) * ρ * (K * Φ.kraus i)ᴴ = 0 := by
    rw [conjTranspose_mul, hK_herm.eq]
    simpa [Matrix.mul_assoc] using hterm i
  have hKKρ : K * Φ.kraus i * ρ = 0 := (hρ.mul_mul_conjTranspose_eq_zero_iff _).mp hi
  have hK1 : K = 1 - (1 : Matrix n n ℂ) ⊗ₖ P := by
    rw [hK, hQ, sub_eq_add_neg, kronecker_add, one_kronecker_one, ← neg_one_smul ℂ P,
      kronecker_smul, neg_one_smul, sub_eq_add_neg]
  rw [hK1, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc] at hKKρ
  exact (sub_eq_zero.mp hKKρ).symm

/-- **Support confinement.** If `Φ` broadcasts the positive semidefinite `ρ` and `P` is a
projector with `P ρ = ρ`, every Kraus operator maps the range of `ρ` into `range P ⊗ range P`:
`(P ⊗ P) Kᵢ ρ = Kᵢ ρ`. -/
theorem kronecker_mul_kraus_mul (h : Φ.Broadcasts ρ) (hρ : ρ.PosSemidef)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) (hPρ : P * ρ = ρ) (i : ι) :
    (P ⊗ₖ P) * (Φ.kraus i * ρ) = Φ.kraus i * ρ := by
  have hPP : P ⊗ₖ P = (P ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ P) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hPP, Matrix.mul_assoc, h.one_kronecker_mul_kraus_mul hρ hP hP2 hPρ i,
    h.kronecker_one_mul_kraus_mul hρ hP hP2 hPρ i]

end Channel.Broadcasts

/-! ### Commuting states are broadcastable: the classical copier in a joint eigenbasis -/

section Copier

variable (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))

/-- The coordinate vector of `b k`. -/
noncomputable def onbVec (k : n) : n → ℂ := WithLp.ofLp (b k)

theorem star_onbVec_dotProduct (k l : n) :
    star (onbVec b k) ⬝ᵥ onbVec b l = if k = l then 1 else 0 := by
  have := (orthonormal_iff_ite.mp b.orthonormal) k l
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
  exact this

theorem star_onbVec_dotProduct_self (k : n) : star (onbVec b k) ⬝ᵥ onbVec b k = 1 := by
  rw [star_onbVec_dotProduct, if_pos rfl]

/-- The rank-one projector `|b k⟩⟨b k|`. -/
noncomputable def onbProj (k : n) : Matrix n n ℂ := vecMulVec (onbVec b k) (star (onbVec b k))

/-- **Completeness**: `∑ₖ |b k⟩⟨b k| = 1`. -/
theorem sum_onbProj : ∑ k, onbProj b k = 1 := by
  set U : Matrix n n ℂ := Matrix.of fun i k => onbVec b k i with hU
  have hUU : Uᴴ * U = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← star_onbVec_dotProduct b k l]
    simp [hU, dotProduct, Matrix.conjTranspose_apply]
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hUU
  ext i j
  rw [← hUU', Matrix.mul_apply, Matrix.sum_apply]
  simp [onbProj, vecMulVec_apply, hU, Matrix.conjTranspose_apply]

/-- The Kraus operator `|b k ⊗ b k⟩⟨b k|` of the copier. -/
noncomputable def copierKraus (k : n) : Matrix (n × n) n ℂ :=
  vecMulVec (fun p => onbVec b k p.1 * onbVec b k p.2) (star (onbVec b k))

theorem copierKraus_conjTranspose_mul (k : n) :
    (copierKraus b k)ᴴ * copierKraus b k = onbProj b k := by
  rw [copierKraus, conjTranspose_vecMulVec, star_star, vecMulVec_mul_vecMulVec]
  have : (star fun p : n × n => onbVec b k p.1 * onbVec b k p.2) ⬝ᵥ
      (fun p : n × n => onbVec b k p.1 * onbVec b k p.2) = 1 := by
    simp only [dotProduct, Pi.star_apply, star_mul', Fintype.sum_prod_type]
    have h := star_onbVec_dotProduct_self b k
    simp only [dotProduct, Pi.star_apply] at h
    calc (∑ a, ∑ c, star (onbVec b k a) * star (onbVec b k c) * (onbVec b k a * onbVec b k c))
        = (∑ a, star (onbVec b k a) * onbVec b k a) * ∑ c, star (onbVec b k c) * onbVec b k c := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      _ = 1 := by rw [h, one_mul]
  rw [this, one_smul, onbProj]

/-- **The copier channel** of an orthonormal basis: `X ↦ ∑ₖ ⟨b k| X |b k⟩ · |b k b k⟩⟨b k b k|`. -/
noncomputable def copierChannel : Channel n (n × n) n where
  kraus := copierKraus b
  tp := by rw [Finset.sum_congr rfl fun k _ => copierKraus_conjTranspose_mul b k, sum_onbProj]

theorem copierChannel_kraus (k : n) : (copierChannel b).kraus k = copierKraus b k := rfl

omit [DecidableEq n] in
/-- The copier on a rank-one term: `Kₖ ρ Kₖᴴ = ⟨b k|ρ|b k⟩ • |b k b k⟩⟨b k b k|`. -/
theorem copierKraus_mul_mul_conjTranspose (ρ : Matrix n n ℂ) (k : n) :
    copierKraus b k * ρ * (copierKraus b k)ᴴ
      = (star (onbVec b k) ⬝ᵥ (ρ *ᵥ onbVec b k)) •
          vecMulVec (fun p : n × n => onbVec b k p.1 * onbVec b k p.2)
            (star fun p : n × n => onbVec b k p.1 * onbVec b k p.2) := by
  rw [copierKraus, conjTranspose_vecMulVec, star_star, vecMulVec_mul, vecMulVec_mul_vecMulVec,
    ← dotProduct_mulVec, Matrix.vecMulVec_smul]

omit [DecidableEq n] in
theorem traceRight_kron_vecMulVec (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    traceRight (vecMulVec (fun p : n × n => v p.1 * v p.2) (star fun p : n × n => v p.1 * v p.2))
      = vecMulVec v (star v) := by
  ext i j
  simp only [traceRight_apply, vecMulVec_apply, Pi.star_apply, star_mul']
  simp only [dotProduct, Pi.star_apply] at hv
  calc (∑ c, v i * v c * (star (v j) * star (v c)))
      = (v i * star (v j)) * ∑ c, star (v c) * v c := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => by ring
    _ = v i * star (v j) := by rw [hv, mul_one]

omit [DecidableEq n] in
theorem traceLeft_kron_vecMulVec (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    traceLeft (vecMulVec (fun p : n × n => v p.1 * v p.2) (star fun p : n × n => v p.1 * v p.2))
      = vecMulVec v (star v) := by
  ext i j
  simp only [traceLeft_apply, vecMulVec_apply, Pi.star_apply, star_mul']
  simp only [dotProduct, Pi.star_apply] at hv
  calc (∑ c, v c * v i * (star (v c) * star (v j)))
      = (v i * star (v j)) * ∑ c, star (v c) * v c := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => by ring
    _ = v i * star (v j) := by rw [hv, mul_one]

/-- A matrix diagonal in the basis `b` is the sum of its eigenvalues times the projectors. -/
theorem eq_sum_smul_onbProj {ρ : Matrix n n ℂ} {r : n → ℂ}
    (hdiag : ∀ k, ρ *ᵥ onbVec b k = r k • onbVec b k) :
    ρ = ∑ k, r k • onbProj b k := by
  calc ρ = ρ * ∑ k, onbProj b k := by rw [sum_onbProj, Matrix.mul_one]
    _ = ∑ k, r k • onbProj b k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [onbProj, mul_vecMulVec, hdiag k, Matrix.smul_vecMulVec]

/-- ★ **The copier broadcasts every matrix diagonal in its basis.** -/
theorem copierChannel_broadcasts {ρ : Matrix n n ℂ} {r : n → ℂ}
    (hdiag : ∀ k, ρ *ᵥ onbVec b k = r k • onbVec b k) :
    (copierChannel b).Broadcasts ρ := by
  have hval : ∀ k, star (onbVec b k) ⬝ᵥ (ρ *ᵥ onbVec b k) = r k := by
    intro k
    rw [hdiag k, dotProduct_smul, star_onbVec_dotProduct_self, smul_eq_mul, mul_one]
  have happly : (copierChannel b).apply ρ = ∑ k, r k •
      vecMulVec (fun p : n × n => onbVec b k p.1 * onbVec b k p.2)
        (star fun p : n × n => onbVec b k p.1 * onbVec b k p.2) := by
    rw [Channel.apply_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [copierChannel_kraus, copierKraus_mul_mul_conjTranspose, hval]
  refine ⟨?_, ?_⟩
  · rw [happly, traceRight_sum, eq_sum_smul_onbProj b hdiag]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [traceRight_smul, traceRight_kron_vecMulVec _ (star_onbVec_dotProduct_self b k), onbProj]
  · rw [happly, traceLeft_sum, eq_sum_smul_onbProj b hdiag]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [traceLeft_smul, traceLeft_kron_vecMulVec _ (star_onbVec_dotProduct_self b k), onbProj]

end Copier

/-! ### Joint eigenbasis of commuting Hermitian matrices -/

section JointEigenbasis

open Module.End in
/-- **Two commuting Hermitian matrices have a joint orthonormal eigenbasis** (Mathlib's
`LinearMap.IsSymmetric.directSum_isInternal_of_commute`, read through `Matrix.toEuclideanLin`). -/
theorem exists_orthonormalBasis_mulVec_eq_smul_of_commute {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hc : ρ * σ = σ * ρ) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (r s : n → ℂ),
      (∀ k, ρ *ᵥ onbVec b k = r k • onbVec b k) ∧ (∀ k, σ *ᵥ onbVec b k = s k • onbVec b k) := by
  classical
  set A : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin ρ with hAdef
  set B : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin σ with hBdef
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hρ
  have hB : B.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hσ
  have hAB : Commute A B := by
    change A * B = B * A
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, hAdef, hBdef,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, hc]
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have horth := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  set V : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ n) :=
    fun i => eigenspace A i.2 ⊓ eigenspace B i.1 with hV
  -- restrict to the finitely many joint eigenvalue pairs
  set f : Module.End.Eigenvalues A × Module.End.Eigenvalues B → ℂ × ℂ :=
    fun p => (p.2.val, p.1.val) with hf
  have hfinj : Function.Injective f := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hf] at h1 h2
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h1)
  have horth' := horth.comp hfinj
  have hsup : (⨆ g, V (f g)) = iSup V := by
    apply le_antisymm
    · exact iSup_comp_le V f
    · refine iSup_le fun i => ?_
      by_cases hA' : Module.End.HasEigenvalue A i.2
      · by_cases hB' : Module.End.HasEigenvalue B i.1
        · exact le_iSup (fun g => V (f g)) (⟨i.2, hA'⟩, ⟨i.1, hB'⟩)
        · have h0 : eigenspace B i.1 = ⊥ := by
            by_contra hne; exact hB' (Module.End.hasEigenvalue_iff.mpr hne)
          simp [V, h0]
      · have h0 : eigenspace A i.2 = ⊥ := by
          by_contra hne; exact hA' (Module.End.hasEigenvalue_iff.mpr hne)
        simp [V, h0]
  have hint' : DirectSum.IsInternal (fun g => V (f g)) := by
    refine (horth'.isInternal_iff).mpr ?_
    have h1 : (iSup V)ᗮ = ⊥ := horth.isInternal_iff.mp hint
    rw [← hsup] at h1
    exact h1
  set b1 := hint'.collectedOrthonormalBasis horth' (fun p => stdOrthonormalBasis ℂ (V (f p)))
    with hb1
  have hcard : Fintype.card (Σ p : Module.End.Eigenvalues A × Module.End.Eigenvalues B,
      Fin (Module.finrank ℂ (V (f p))))
      = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b1.toBasis, finrank_euclideanSpace]
  set e := Fintype.equivOfCardEq hcard with he
  refine ⟨b1.reindex e, fun k => ((e.symm k).1.1 : ℂ), fun k => ((e.symm k).1.2 : ℂ), ?_, ?_⟩
  · intro k
    have hmem := hint'.collectedOrthonormalBasis_mem horth'
      (fun p => stdOrthonormalBasis ℂ (V (f p))) (e.symm k)
    have h1 : A (b1 (e.symm k)) = ((e.symm k).1.1 : ℂ) • b1 (e.symm k) :=
      mem_eigenspace_iff.mp hmem.1
    simp only [onbVec, OrthonormalBasis.reindex_apply]
    have h2 : WithLp.ofLp (A (b1 (e.symm k))) = ρ *ᵥ WithLp.ofLp (b1 (e.symm k)) := rfl
    rw [← h2, h1, WithLp.ofLp_smul]
  · intro k
    have hmem := hint'.collectedOrthonormalBasis_mem horth'
      (fun p => stdOrthonormalBasis ℂ (V (f p))) (e.symm k)
    have h1 : B (b1 (e.symm k)) = ((e.symm k).1.2 : ℂ) • b1 (e.symm k) :=
      mem_eigenspace_iff.mp hmem.2
    simp only [onbVec, OrthonormalBasis.reindex_apply]
    have h2 : WithLp.ofLp (B (b1 (e.symm k))) = σ *ᵥ WithLp.ofLp (b1 (e.symm k)) := rfl
    rw [← h2, h1, WithLp.ofLp_smul]

/-- ★★ **Commuting Hermitian matrices can be broadcast**: the copier in a joint eigenbasis
broadcasts both (the easy half of BCFJS). -/
theorem exists_channel_broadcasts_of_commute {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hc : ρ * σ = σ * ρ) :
    ∃ Φ : Channel n (n × n) n, Φ.Broadcasts ρ ∧ Φ.Broadcasts σ := by
  obtain ⟨b, r, s, hr, hs⟩ := exists_orthonormalBasis_mulVec_eq_smul_of_commute hρ hσ hc
  exact ⟨copierChannel b, copierChannel_broadcasts b hr, copierChannel_broadcasts b hs⟩

end JointEigenbasis

/-! ### Broadcasting two pure states forces them orthogonal or parallel (the cloning core) -/

section PurePure

variable {Φ : Channel n (n × n) ι}

/-- The product vector `x ⊗ y` on `n × n`. -/
def kronVec (x y : n → ℂ) : n × n → ℂ := fun p => x p.1 * y p.2

omit [Fintype n] [DecidableEq n] in
theorem kronecker_vecMulVec_star (x y : n → ℂ) :
    vecMulVec x (star x) ⊗ₖ vecMulVec y (star y)
      = vecMulVec (kronVec x y) (star (kronVec x y)) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [kronecker_apply, vecMulVec_apply, kronVec, Pi.star_apply, star_mul']
  ring

omit [DecidableEq n] in
theorem star_kronVec_dotProduct (x y x' y' : n → ℂ) :
    star (kronVec x y) ⬝ᵥ kronVec x' y' = (star x ⬝ᵥ x') * (star y ⬝ᵥ y') := by
  simp only [dotProduct, kronVec, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

omit [DecidableEq n] in
theorem vecMulVec_mulVec' {m : Type*} (u : m → ℂ) (v w : n → ℂ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **A broadcast pure state is cloned**: every Kraus operator sends `ψ` to a multiple of
`ψ ⊗ ψ` (support confinement with the rank-one projector `|ψ⟩⟨ψ|`). -/
theorem Channel.Broadcasts.kraus_mulVec_eq_smul_kronVec {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (h : Φ.Broadcasts (vecMulVec ψ (star ψ))) (i : ι) :
    Φ.kraus i *ᵥ ψ = (star (kronVec ψ ψ) ⬝ᵥ (Φ.kraus i *ᵥ ψ)) • kronVec ψ ψ := by
  set P := vecMulVec ψ (star ψ) with hPdef
  have hP : P.IsHermitian := by rw [hPdef, IsHermitian, conjTranspose_vecMulVec, star_star]
  have hP2 : P * P = P := by rw [hPdef, vecMulVec_mul_vecMulVec, hψ, one_smul]
  have hconf := h.kronecker_mul_kraus_mul (posSemidef_vecMulVec_self_star ψ) hP hP2 hP2 i
  rw [hPdef, kronecker_vecMulVec_star, mul_vecMulVec, vecMulVec_mul_vecMulVec] at hconf
  have := congrArg (fun M => M *ᵥ ψ) hconf
  simp only [vecMulVec_mulVec', smul_dotProduct, hψ, smul_eq_mul, mul_one, one_smul] at this
  exact this.symm

/-- The trace-preservation identity read on two vectors: `⟨φ|ψ⟩ = ∑ᵢ ⟨Kᵢ φ|Kᵢ ψ⟩`. -/
theorem Channel.star_dotProduct_eq_sum_kraus (Φ : Channel n (n × n) ι) (φ ψ : n → ℂ) :
    star φ ⬝ᵥ ψ = ∑ i, star (Φ.kraus i *ᵥ φ) ⬝ᵥ (Φ.kraus i *ᵥ ψ) := by
  have h1 : star φ ⬝ᵥ ψ = star φ ⬝ᵥ ((∑ i, (Φ.kraus i)ᴴ * Φ.kraus i) *ᵥ ψ) := by
    rw [Φ.tp, Matrix.one_mulVec]
  rw [h1, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- Cauchy–Schwarz for `dotProduct`: `‖⟨x|y⟩‖² ≤ ⟨x|x⟩ ⟨y|y⟩` (real parts). -/
theorem norm_star_dotProduct_sq_le {m : Type*} [Fintype m] (x y : m → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  set X : EuclideanSpace ℂ m := WithLp.toLp 2 x
  set Y : EuclideanSpace ℂ m := WithLp.toLp 2 y
  have hXY : inner ℂ X Y = star x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hnorm : ∀ z : m → ℂ, (star z ⬝ᵥ z).re = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ m)‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← hXY, hnorm x, hnorm y]
  have := norm_inner_le_norm (𝕜 := ℂ) X Y
  calc ‖inner ℂ X Y‖ ^ 2 ≤ (‖X‖ * ‖Y‖) ^ 2 := by gcongr
    _ = ‖X‖ ^ 2 * ‖Y‖ ^ 2 := by ring

/-- ★★ **Two broadcast pure states are orthogonal or parallel.** If one channel broadcasts both
`|ψ⟩⟨ψ|` and `|φ⟩⟨φ|` (unit vectors), then `⟨φ|ψ⟩ = 0` or `‖⟨φ|ψ⟩‖ = 1`: each Kraus operator
clones both, and trace preservation gives `⟨φ|ψ⟩ = ⟨φ|ψ⟩² ∑ᵢ conj bᵢ aᵢ` with `|∑ᵢ conj bᵢ aᵢ| ≤ 1`.
This is the no-cloning theorem for channels, and the rank-one case of the hard half of BCFJS. -/
theorem Channel.Broadcasts.star_dotProduct_eq_zero_or_norm_eq_one {ψ φ : n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1)
    (h1 : Φ.Broadcasts (vecMulVec ψ (star ψ))) (h2 : Φ.Broadcasts (vecMulVec φ (star φ))) :
    star φ ⬝ᵥ ψ = 0 ∨ ‖star φ ⬝ᵥ ψ‖ = 1 := by
  set a : ι → ℂ := fun i => star (kronVec ψ ψ) ⬝ᵥ (Φ.kraus i *ᵥ ψ) with ha
  set b : ι → ℂ := fun i => star (kronVec φ φ) ⬝ᵥ (Φ.kraus i *ᵥ φ) with hb
  have hKa : ∀ i, Φ.kraus i *ᵥ ψ = a i • kronVec ψ ψ := fun i =>
    h1.kraus_mulVec_eq_smul_kronVec hψ i
  have hKb : ∀ i, Φ.kraus i *ᵥ φ = b i • kronVec φ φ := fun i =>
    h2.kraus_mulVec_eq_smul_kronVec hφ i
  set c : ℂ := star φ ⬝ᵥ ψ with hc
  -- `c = c² S`
  have hcS : c = c ^ 2 * (star b ⬝ᵥ a) := by
    calc c = ∑ i, star (Φ.kraus i *ᵥ φ) ⬝ᵥ (Φ.kraus i *ᵥ ψ) := Φ.star_dotProduct_eq_sum_kraus φ ψ
      _ = ∑ i, star (b i) * a i * c ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hKa, hKb, star_smul, smul_dotProduct, dotProduct_smul, star_kronVec_dotProduct, ← hc]
          simp only [smul_eq_mul]
          ring
      _ = c ^ 2 * (star b ⬝ᵥ a) := by
          rw [dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply]
          ring
  -- `∑ |aᵢ|² = 1 = ∑ |bᵢ|²`
  have hnorm : ∀ (ξ : n → ℂ) (x : ι → ℂ), star ξ ⬝ᵥ ξ = 1 →
      (∀ i, Φ.kraus i *ᵥ ξ = x i • kronVec ξ ξ) → star x ⬝ᵥ x = 1 := by
    intro ξ x hξ hK
    calc star x ⬝ᵥ x = ∑ i, star (x i) * x i := by simp [dotProduct]
      _ = ∑ i, star (Φ.kraus i *ᵥ ξ) ⬝ᵥ (Φ.kraus i *ᵥ ξ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hK i, star_smul, smul_dotProduct, dotProduct_smul, star_kronVec_dotProduct, hξ]
          simp only [smul_eq_mul]
          ring
      _ = star ξ ⬝ᵥ ξ := (Φ.star_dotProduct_eq_sum_kraus ξ ξ).symm
      _ = 1 := hξ
  have ha1 := hnorm ψ a hψ hKa
  have hb1 := hnorm φ b hφ hKb
  -- `‖S‖ ≤ 1` and `‖c‖ ≤ 1`
  have hS : ‖star b ⬝ᵥ a‖ ≤ 1 := by
    have := norm_star_dotProduct_sq_le b a
    rw [hb1, ha1, Complex.one_re, mul_one] at this
    nlinarith [norm_nonneg (star b ⬝ᵥ a)]
  have hc1 : ‖c‖ ≤ 1 := by
    have := norm_star_dotProduct_sq_le φ ψ
    rw [hφ, hψ, Complex.one_re, mul_one] at this
    nlinarith [norm_nonneg c]
  -- `‖c‖ ≤ ‖c‖²`
  have hle : ‖c‖ ≤ ‖c‖ ^ 2 := by
    calc ‖c‖ = ‖c ^ 2 * (star b ⬝ᵥ a)‖ := by rw [← hcS]
      _ = ‖c‖ ^ 2 * ‖star b ⬝ᵥ a‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖c‖ ^ 2 * 1 := by gcongr
      _ = ‖c‖ ^ 2 := mul_one _
  by_cases h0 : c = 0
  · exact Or.inl h0
  · right
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr h0
    have : 1 ≤ ‖c‖ := by nlinarith
    exact le_antisymm hc1 this

end PurePure


/-! ### The support projector of a matrix -/

section SupportProjector

/-- The orthogonal projector onto the range of `A`, as a matrix. -/
noncomputable def suppProj (A : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.toEuclideanLin.symm
    ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)

theorem toEuclideanLin_suppProj (A : Matrix n n ℂ) :
    Matrix.toEuclideanLin (suppProj A)
      = ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection :
          EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) := by
  rw [suppProj, LinearEquiv.apply_symm_apply]

theorem suppProj_mulVec (A : Matrix n n ℂ) (x : n → ℂ) :
    suppProj A *ᵥ x
      = WithLp.ofLp ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection (WithLp.toLp 2 x)) := by
  have := congrArg (fun L => WithLp.ofLp (L (WithLp.toLp 2 x))) (toEuclideanLin_suppProj A)
  simpa [Matrix.toLpLin_apply] using this

theorem suppProj_mulVec_eq_self_iff (A : Matrix n n ℂ) (x : n → ℂ) :
    suppProj A *ᵥ x = x ↔ ∃ y, A *ᵥ y = x := by
  rw [suppProj_mulVec]
  constructor
  · intro h
    have h' : (LinearMap.range (Matrix.toEuclideanLin A)).starProjection (WithLp.toLp 2 x)
        = WithLp.toLp 2 x := by
      apply WithLp.ofLp_injective
      simpa using h
    obtain ⟨y, hy⟩ := Submodule.starProjection_eq_self_iff.mp h'
    refine ⟨WithLp.ofLp y, ?_⟩
    have := congrArg WithLp.ofLp hy
    simpa [Matrix.toLpLin_apply] using this
  · rintro ⟨y, rfl⟩
    have hmem : WithLp.toLp 2 (A *ᵥ y) ∈ LinearMap.range (Matrix.toEuclideanLin A) :=
      ⟨WithLp.toLp 2 y, by simp [Matrix.toLpLin_apply]⟩
    rw [Submodule.starProjection_eq_self_iff.mpr hmem]

theorem suppProj_mul_self (A : Matrix n n ℂ) : suppProj A * suppProj A = suppProj A := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, toEuclideanLin_suppProj]
  exact congrArg ContinuousLinearMap.toLinearMap
    (LinearMap.range (Matrix.toEuclideanLin A)).isIdempotentElem_starProjection

theorem suppProj_isHermitian (A : Matrix n n ℂ) : (suppProj A).IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, toEuclideanLin_suppProj]
  exact (LinearMap.range (Matrix.toEuclideanLin A)).starProjection_isSymmetric

theorem suppProj_mul (A : Matrix n n ℂ) : suppProj A * A = A := by
  ext i j
  have h := (suppProj_mulVec_eq_self_iff A (A *ᵥ Pi.single j 1)).mpr ⟨_, rfl⟩
  have := congrFun h i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem mul_suppProj_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A * suppProj A = A := by
  have := congrArg conjTranspose (suppProj_mul A)
  rwa [conjTranspose_mul, (suppProj_isHermitian A).eq, hA.eq] at this

end SupportProjector

/-! ### Squared norms, and the top eigenvalue of a Hermitian matrix -/

section Norm

omit [DecidableEq n] in
/-- `‖v‖²` as the real part of `⟨v|v⟩`. -/
def nsq (v : n → ℂ) : ℝ := (star v ⬝ᵥ v).re

omit [DecidableEq n] in
theorem nsq_eq_sum (v : n → ℂ) : nsq v = ∑ i, ‖v i‖ ^ 2 := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq n] in
theorem nsq_nonneg (v : n → ℂ) : 0 ≤ nsq v := by
  rw [nsq_eq_sum]; positivity

omit [DecidableEq n] in
theorem nsq_eq_zero_iff (v : n → ℂ) : nsq v = 0 ↔ v = 0 := by
  rw [nsq_eq_sum]
  constructor
  · intro h
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖v i‖).mp h
    funext i
    simpa using this i (Finset.mem_univ i)
  · rintro rfl; simp

omit [DecidableEq n] in
theorem star_dotProduct_self_eq_nsq (v : n → ℂ) : star v ⬝ᵥ v = (nsq v : ℂ) := by
  rw [nsq_eq_sum, Complex.ofReal_sum]
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

omit [DecidableEq n] in
theorem nsq_mulVec {m : Type*} [Fintype m] (M : Matrix m n ℂ) (x : n → ℂ) :
    nsq (M *ᵥ x) = (star x ⬝ᵥ ((Mᴴ * M) *ᵥ x)).re := by
  rw [nsq, star_mulVec, dotProduct_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul]

omit [DecidableEq n] in
theorem nsq_smul (c : ℂ) (v : n → ℂ) : nsq (c • v) = ‖c‖ ^ 2 * nsq v := by
  simp only [nsq_eq_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq n] in
/-- `⟨z| P_k |z⟩ = |⟨v_k|z⟩|²` for the rank-one projector of a basis vector. -/
theorem star_dotProduct_onbProj_mulVec (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (k : n)
    (z : n → ℂ) :
    star z ⬝ᵥ (onbProj b k *ᵥ z) = ((‖star (onbVec b k) ⬝ᵥ z‖ ^ 2 : ℝ) : ℂ) := by
  rw [onbProj, vecMulVec_mulVec', dotProduct_smul, smul_eq_mul, star_dotProduct z (onbVec b k),
    Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]

end Norm

section TopEigenvalue

/-- **The top eigenvalue of a Hermitian matrix** bounds its Rayleigh quotient and is attained by
a unit eigenvector: from `Matrix.IsHermitian.eigenvectorBasis` and completeness. -/
theorem IsHermitian.exists_top_eigenvalue [Nonempty n] {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) :
    ∃ (μ : ℝ) (u : n → ℂ), star u ⬝ᵥ u = 1 ∧ Q *ᵥ u = (μ : ℂ) • u ∧
      ∀ z, (star z ⬝ᵥ (Q *ᵥ z)).re ≤ μ * nsq z := by
  set b := hQ.eigenvectorBasis with hb
  set r := hQ.eigenvalues with hr
  have hdiag : ∀ k, Q *ᵥ onbVec b k = ((r k : ℝ) : ℂ) • onbVec b k := by
    intro k
    have := hQ.mulVec_eigenvectorBasis k
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
    exact this
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  refine ⟨r k₀, onbVec b k₀, star_onbVec_dotProduct_self b k₀, hdiag k₀, fun z => ?_⟩
  have hQz : Q *ᵥ z = ∑ k, ((r k : ℝ) : ℂ) • (onbProj b k *ᵥ z) := by
    rw [eq_sum_smul_onbProj b hdiag, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec]
  have hz : nsq z = ∑ k, ‖star (onbVec b k) ⬝ᵥ z‖ ^ 2 := by
    have h1 : star z ⬝ᵥ z = star z ⬝ᵥ ((∑ k, onbProj b k) *ᵥ z) := by
      rw [sum_onbProj, Matrix.one_mulVec]
    rw [nsq, h1, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_dotProduct_onbProj_mulVec, Complex.ofReal_re]
  rw [hQz, dotProduct_sum, Complex.re_sum, hz, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [dotProduct_smul, star_dotProduct_onbProj_mulVec, smul_eq_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hk₀ k (Finset.mem_univ k)) (sq_nonneg _)

end TopEigenvalue

/-! ### Projector inequalities -/

section Projector

omit [DecidableEq n] in
theorem posSemidef_of_isHermitian_of_re_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (h : ∀ x, 0 ≤ (star x ⬝ᵥ M *ᵥ x).re) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => ?_
  rw [Complex.nonneg_iff]
  exact ⟨h x, (hM.im_star_dotProduct_mulVec_self x).symm⟩

omit [DecidableEq n] in
theorem nsq_mulVec_of_proj {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) (x : n → ℂ) :
    nsq (P *ᵥ x) = (star x ⬝ᵥ P *ᵥ x).re := by
  rw [nsq_mulVec, hP.eq, hP2]

omit [Fintype n] in
theorem one_sub_proj_isHermitian {P : Matrix n n ℂ} (hP : P.IsHermitian) : (1 - P).IsHermitian :=
  isHermitian_one.sub hP

theorem one_sub_proj_mul_self {P : Matrix n n ℂ} (hP2 : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hP2]
  abel

theorem nsq_one_sub_proj_mulVec {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P)
    (x : n → ℂ) : nsq ((1 - P) *ᵥ x) = nsq x - nsq (P *ᵥ x) := by
  rw [nsq_mulVec_of_proj (one_sub_proj_isHermitian hP) (one_sub_proj_mul_self hP2),
    Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re,
    nsq_mulVec_of_proj hP hP2, nsq]

/-- A projector is a contraction: `‖P x‖² ≤ ‖x‖²`. -/
theorem nsq_proj_mulVec_le {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) (x : n → ℂ) :
    nsq (P *ᵥ x) ≤ nsq x := by
  have := nsq_nonneg ((1 - P) *ᵥ x)
  rw [nsq_one_sub_proj_mulVec hP hP2] at this
  linarith

/-- Equality in the contraction forces `P x = x`. -/
theorem proj_mulVec_eq_self_of_nsq_eq {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P)
    (x : n → ℂ) (h : nsq (P *ᵥ x) = nsq x) : P *ᵥ x = x := by
  have h0 : nsq ((1 - P) *ᵥ x) = 0 := by rw [nsq_one_sub_proj_mulVec hP hP2, h, sub_self]
  have := (nsq_eq_zero_iff _).mp h0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  exact this.symm

end Projector

/-! ### The tensor bound `Q ⊗ Q ≤ μ²` -/

section TensorBound

/-- If `⟨z|Q|z⟩ ≤ μ ‖z‖²` for a Hermitian `Q ≥ 0` then `⟨x|Q ⊗ Q|x⟩ ≤ μ² ‖x‖²`: the identity
`μ² − Q ⊗ Q = μ (μ − Q) ⊗ 1 + Q ⊗ (μ − Q)` with both terms positive semidefinite. -/
theorem re_star_dotProduct_kronecker_mulVec_le {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {μ : ℝ}
    (hμ : 0 ≤ μ) (hbound : ∀ z, (star z ⬝ᵥ (Q *ᵥ z)).re ≤ μ * nsq z) (x : n × n → ℂ) :
    (star x ⬝ᵥ ((Q ⊗ₖ Q) *ᵥ x)).re ≤ μ ^ 2 * nsq x := by
  have hμQ : ((μ : ℂ) • (1 : Matrix n n ℂ) - Q).PosSemidef := by
    refine posSemidef_of_isHermitian_of_re_nonneg
      ((isHermitian_one.smul (Complex.conj_ofReal μ)).sub hQ.1) fun z => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have := hbound z
    unfold nsq at this
    linarith
  -- the identity `μ² − Q ⊗ Q = μ (μ − Q) ⊗ 1 + Q ⊗ (μ − Q)`
  have hid : ((μ : ℂ) ^ 2) • (1 : Matrix (n × n) (n × n) ℂ) - Q ⊗ₖ Q
      = (μ : ℂ) • (((μ : ℂ) • (1 : Matrix n n ℂ) - Q) ⊗ₖ (1 : Matrix n n ℂ))
        + Q ⊗ₖ ((μ : ℂ) • (1 : Matrix n n ℂ) - Q) := by
    ext ⟨a, c⟩ ⟨a', c'⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, kronecker_apply,
      Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs <;> simp_all <;> ring
  have hpsd1 : (((μ : ℂ) • (1 : Matrix n n ℂ) - Q) ⊗ₖ (1 : Matrix n n ℂ)).PosSemidef :=
    hμQ.kronecker Matrix.PosSemidef.one
  have hpsd2 : (Q ⊗ₖ ((μ : ℂ) • (1 : Matrix n n ℂ) - Q)).PosSemidef := hQ.kronecker hμQ
  have h1 := hpsd1.dotProduct_mulVec_nonneg x
  have h2 := hpsd2.dotProduct_mulVec_nonneg x
  rw [Complex.nonneg_iff] at h1 h2
  have hsub : (star x ⬝ᵥ ((((μ : ℂ) ^ 2) • (1 : Matrix (n × n) (n × n) ℂ) - Q ⊗ₖ Q) *ᵥ x)).re
      = μ ^ 2 * nsq x - (star x ⬝ᵥ ((Q ⊗ₖ Q) *ᵥ x)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, nsq]
  have hre : 0 ≤ (star x ⬝ᵥ ((((μ : ℂ) ^ 2) • (1 : Matrix (n × n) (n × n) ℂ) - Q ⊗ₖ Q) *ᵥ x)).re := by
    rw [hid, Matrix.add_mulVec, dotProduct_add, Complex.add_re, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Complex.re_ofReal_mul]
    exact add_nonneg (mul_nonneg hμ h1.1) h2.1
  linarith

end TensorBound

/-! ### BC3: broadcast states with disjoint supports have orthogonal supports -/

section DisjointSupports

variable {ι : Type*} [Fintype ι] {Φ : Channel n (n × n) ι}

/-- The squared norms of the Kraus images sum to the squared norm: `∑ᵢ ‖Kᵢ x‖² = ‖x‖²`. -/
theorem Channel.sum_nsq_kraus_mulVec (Φ : Channel n (n × n) ι) (x : n → ℂ) :
    ∑ i, nsq (Φ.kraus i *ᵥ x) = nsq x := by
  simp only [nsq]
  rw [Φ.star_dotProduct_eq_sum_kraus x x, Complex.re_sum]

/-- ★★ **BC3. Broadcast states with disjoint supports have orthogonal supports.** If one channel
broadcasts the positive semidefinite `A` and `B` and their ranges meet only in `0`, then `B A = 0`.
With `P_A, P_B` the support projectors and `Q = P_A P_B P_A`, the top eigenvalue `μ` of `Q` with
unit eigenvector `u ∈ range A` and `w = P_B u ∈ range B` gives `μ = ⟨w|u⟩ = ∑ᵢ ⟨Kᵢ w|Kᵢ u⟩`;
support confinement puts `Kᵢ u` in `range A ⊗ range A` and `Kᵢ w` in `range B ⊗ range B`, the
tensor bound `Q ⊗ Q ≤ μ²` and Cauchy–Schwarz give `μ ≤ μ √μ`, so `μ ∈ {0, 1}`; `μ = 1` would put
`u` in both ranges, hence `μ = 0`, `P_B P_A = 0` and `B A = 0`. -/
theorem Channel.Broadcasts.mul_eq_zero_of_range_disjoint {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (h1 : Φ.Broadcasts A) (h2 : Φ.Broadcasts B)
    (hdisj : ∀ x, (∃ y, A *ᵥ y = x) → (∃ z, B *ᵥ z = x) → x = 0) : B * A = 0 := by
  classical
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact Matrix.ext fun i _ => (hempty.false i).elim
  set PA := suppProj A with hPAdef
  set PB := suppProj B with hPBdef
  have hPA : PA.IsHermitian := suppProj_isHermitian A
  have hPB : PB.IsHermitian := suppProj_isHermitian B
  have hPA2 : PA * PA = PA := suppProj_mul_self A
  have hPB2 : PB * PB = PB := suppProj_mul_self B
  have hPAA : PA * A = A := suppProj_mul A
  have hPBB : PB * B = B := suppProj_mul B
  set G := PB * PA with hGdef
  set Q := Gᴴ * G with hQdef
  have hQherm : Q.IsHermitian := isHermitian_conjTranspose_mul_self G
  have hQpsd : Q.PosSemidef := posSemidef_conjTranspose_mul_self G
  obtain ⟨μ, u, hu1, hQu, hbound⟩ := IsHermitian.exists_top_eigenvalue hQherm
  have hGz : ∀ z, nsq (G *ᵥ z) ≤ μ * nsq z := fun z => by rw [nsq_mulVec]; exact hbound z
  have hnu : nsq u = 1 := by rw [nsq, hu1, Complex.one_re]
  have hμ0 : 0 ≤ μ := by
    have := nsq_nonneg (G *ᵥ u)
    rwa [nsq_mulVec, hQu, dotProduct_smul, hu1, smul_eq_mul, mul_one, Complex.ofReal_re] at this
  -- it suffices to show `G = 0`
  suffices hG : G = 0 by
    calc B * A = B * PB * (PA * A) := by rw [hPAA, mul_suppProj_of_isHermitian hB.1]
      _ = B * G * A := by rw [hGdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = 0 := by rw [hG, Matrix.mul_zero, Matrix.zero_mul]
  by_cases hμ : μ = 0
  · rw [Matrix.ext_iff_mulVec]
    intro z
    rw [Matrix.zero_mulVec, ← nsq_eq_zero_iff]
    have := hGz z
    rw [hμ, zero_mul] at this
    exact le_antisymm this (nsq_nonneg _)
  exfalso
  have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
  -- `u ∈ range A`
  have hQeq : Q = PA * PB * PA := by
    rw [hQdef, hGdef, conjTranspose_mul, hPB.eq, hPA.eq, Matrix.mul_assoc PA PB (PB * PA),
      ← Matrix.mul_assoc PB PB PA, hPB2, Matrix.mul_assoc PA PB PA]
  have hPAu : PA *ᵥ u = u := by
    have hu : u = (μ⁻¹ : ℂ) • (Q *ᵥ u) := by
      rw [hQu, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hμ,
        Complex.ofReal_one, one_smul]
    have hPAQ : PA * Q = Q := by
      rw [hQeq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPA2]
    calc PA *ᵥ u = PA *ᵥ ((μ⁻¹ : ℂ) • (Q *ᵥ u)) := by rw [← hu]
      _ = (μ⁻¹ : ℂ) • ((PA * Q) *ᵥ u) := by rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      _ = u := by rw [hPAQ, ← hu]
  obtain ⟨y, hy⟩ := (suppProj_mulVec_eq_self_iff A u).mp hPAu
  set w := PB *ᵥ u with hwdef
  have hPBw : PB *ᵥ w = w := by rw [hwdef, Matrix.mulVec_mulVec, hPB2]
  obtain ⟨z, hz⟩ := (suppProj_mulVec_eq_self_iff B w).mp hPBw
  -- the two key scalars: `⟨u|P_B u⟩ = μ`
  have huPBu : star u ⬝ᵥ (PB *ᵥ u) = (μ : ℂ) := by
    have h := congrArg (fun v => star u ⬝ᵥ v) hQu
    simp only [dotProduct_smul, hu1, smul_eq_mul, mul_one] at h
    rw [hQeq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPAu, dotProduct_mulVec] at h
    have hPAu' : star u ᵥ* PA = star u := by rw [← hPA.eq, ← star_mulVec, hPAu]
    rwa [hPAu'] at h
  have hwu : star w ⬝ᵥ u = (μ : ℂ) := by
    rw [hwdef, star_mulVec, ← dotProduct_mulVec, hPB.eq, huPBu]
  have hnw : nsq w = μ := by
    rw [hwdef, nsq_mulVec_of_proj hPB hPB2, huPBu, Complex.ofReal_re]
  have hμ1 : μ ≤ 1 := by
    have := nsq_proj_mulVec_le hPB hPB2 u
    rwa [← hwdef, hnw, hnu] at this
  -- trace preservation read on `(w, u)`
  have hsum : (μ : ℂ) = ∑ i, star (Φ.kraus i *ᵥ w) ⬝ᵥ (Φ.kraus i *ᵥ u) := by
    rw [← hwu]; exact Φ.star_dotProduct_eq_sum_kraus w u
  -- support confinement of the Kraus images
  have hKu : ∀ i, (PA ⊗ₖ PA) *ᵥ (Φ.kraus i *ᵥ u) = Φ.kraus i *ᵥ u := by
    intro i
    have := congrArg (fun M => M *ᵥ y) (h1.kronecker_mul_kraus_mul hA hPA hPA2 hPAA i)
    simpa only [← Matrix.mulVec_mulVec, hy] using this
  have hKw : ∀ i, (PB ⊗ₖ PB) *ᵥ (Φ.kraus i *ᵥ w) = Φ.kraus i *ᵥ w := by
    intro i
    have := congrArg (fun M => M *ᵥ z) (h2.kronecker_mul_kraus_mul hB hPB hPB2 hPBB i)
    simpa only [← Matrix.mulVec_mulVec, hz] using this
  -- each term is `⟨Kᵢ w|(G ⊗ G) Kᵢ u⟩`
  have hPBPB : (PB ⊗ₖ PB).IsHermitian := by
    rw [IsHermitian, conjTranspose_kronecker, hPB.eq]
  have hGG : (PB ⊗ₖ PB) * (PA ⊗ₖ PA) = G ⊗ₖ G := by rw [← mul_kronecker_mul]
  have hterm : ∀ i, star (Φ.kraus i *ᵥ w) ⬝ᵥ (Φ.kraus i *ᵥ u)
      = star (Φ.kraus i *ᵥ w) ⬝ᵥ ((G ⊗ₖ G) *ᵥ (Φ.kraus i *ᵥ u)) := by
    intro i
    conv_lhs => rw [← hKw i, ← hKu i]
    rw [star_mulVec, hPBPB.eq, ← dotProduct_mulVec,
      Matrix.mulVec_mulVec (Φ.kraus i *ᵥ u) (PB ⊗ₖ PB) (PA ⊗ₖ PA), hGG]
  -- the per-term bound `‖tᵢ‖ ≤ μ √pᵢ √qᵢ`
  set p : ι → ℝ := fun i => nsq (Φ.kraus i *ᵥ w) with hpdef
  set q : ι → ℝ := fun i => nsq (Φ.kraus i *ᵥ u) with hqdef
  have hp : ∑ i, p i = μ := by rw [hpdef, Φ.sum_nsq_kraus_mulVec, hnw]
  have hq : ∑ i, q i = 1 := by rw [hqdef, Φ.sum_nsq_kraus_mulVec, hnu]
  have hterm_le : ∀ i, ‖star (Φ.kraus i *ᵥ w) ⬝ᵥ (Φ.kraus i *ᵥ u)‖
      ≤ μ * (Real.sqrt (p i) * Real.sqrt (q i)) := by
    intro i
    rw [hterm i]
    have hcs := norm_star_dotProduct_sq_le (Φ.kraus i *ᵥ w) ((G ⊗ₖ G) *ᵥ (Φ.kraus i *ᵥ u))
    change ‖_‖ ^ 2 ≤ nsq (Φ.kraus i *ᵥ w) * nsq ((G ⊗ₖ G) *ᵥ (Φ.kraus i *ᵥ u)) at hcs
    have hGGx : nsq ((G ⊗ₖ G) *ᵥ (Φ.kraus i *ᵥ u)) ≤ μ ^ 2 * q i := by
      rw [nsq_mulVec, conjTranspose_kronecker, ← mul_kronecker_mul]
      exact re_star_dotProduct_kronecker_mulVec_le hQpsd hμ0 hbound _
    have hsq : ‖star (Φ.kraus i *ᵥ w) ⬝ᵥ ((G ⊗ₖ G) *ᵥ (Φ.kraus i *ᵥ u))‖ ^ 2
        ≤ (μ * (Real.sqrt (p i) * Real.sqrt (q i))) ^ 2 := by
      calc _ ≤ p i * (μ ^ 2 * q i) :=
            hcs.trans (mul_le_mul_of_nonneg_left hGGx (nsq_nonneg _))
        _ = (μ * (Real.sqrt (p i) * Real.sqrt (q i))) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)]
            ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  -- summing: `μ ≤ μ √μ`
  have hμle : μ ≤ μ * Real.sqrt μ := by
    calc μ = ‖(μ : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hμ0]
      _ = ‖∑ i, star (Φ.kraus i *ᵥ w) ⬝ᵥ (Φ.kraus i *ᵥ u)‖ := by rw [← hsum]
      _ ≤ ∑ i, ‖star (Φ.kraus i *ᵥ w) ⬝ᵥ (Φ.kraus i *ᵥ u)‖ := norm_sum_le _ _
      _ ≤ ∑ i, μ * (Real.sqrt (p i) * Real.sqrt (q i)) := Finset.sum_le_sum fun i _ => hterm_le i
      _ = μ * ∑ i, Real.sqrt (p i) * Real.sqrt (q i) := by rw [Finset.mul_sum]
      _ ≤ μ * Real.sqrt μ := by
          refine mul_le_mul_of_nonneg_left ?_ hμ0
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun i => Real.sqrt (p i)) (fun i => Real.sqrt (q i))
          have hpp : ∑ i, Real.sqrt (p i) ^ 2 = μ := by
            rw [← hp]; exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (nsq_nonneg _)
          have hqq : ∑ i, Real.sqrt (q i) ^ 2 = 1 := by
            rw [← hq]; exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (nsq_nonneg _)
          rw [hpp, hqq, mul_one] at hcs
          exact (Real.le_sqrt (Finset.sum_nonneg fun i _ => by positivity) hμ0).mpr hcs
  have hμge : 1 ≤ μ := by
    have h1' : μ * 1 ≤ μ * Real.sqrt μ := by rw [mul_one]; exact hμle
    exact Real.one_le_sqrt.mp (le_of_mul_le_mul_left h1' hμpos)
  have hμeq : μ = 1 := le_antisymm hμ1 hμge
  -- `μ = 1` puts `u` in `range B` as well, so `u = 0`
  have hPBu : PB *ᵥ u = u :=
    proj_mulVec_eq_self_of_nsq_eq hPB hPB2 u (by rw [← hwdef, hnw, hnu, hμeq])
  obtain ⟨z', hz'⟩ := (suppProj_mulVec_eq_self_iff B u).mp hPBu
  have hu0 : u = 0 := hdisj u ⟨y, hy⟩ ⟨z', hz'⟩
  have := hnu
  rw [hu0, (nsq_eq_zero_iff (0 : n → ℂ)).mpr rfl] at this
  exact zero_ne_one this

end DisjointSupports

section BlockSplit

variable {ι : Type*} [Fintype ι] {Φ : Channel n (n × n) ι}


/-- Two positive semidefinite matrices with `Tr (X Y) = 0` satisfy `X Y = 0`. -/
theorem _root_.Matrix.PosSemidef.mul_eq_zero_of_trace_mul_eq_zero {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : (X * Y).trace = 0) : X * Y = 0 := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  rw [star_eq_conjTranspose] at hC hD
  subst hC hD
  -- Tr (Cᴴ C Dᴴ D) = Tr ((D Cᴴ)ᴴ (D Cᴴ))
  have h' : ((D * Cᴴ)ᴴ * (D * Cᴴ)).trace = 0 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, ← h]
    -- Tr (C Dᴴ D Cᴴ) = Tr (Cᴴ C Dᴴ D)
    rw [show C * Dᴴ * (D * Cᴴ) = (C * Dᴴ * D) * Cᴴ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hDC : D * Cᴴ = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h'
  calc Cᴴ * C * (Dᴴ * D) = Cᴴ * (D * Cᴴ)ᴴ * D := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = 0 := by rw [hDC, conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- The dual of `P ⊗ 1` is contracted by `1` when `P` is a projector. -/
theorem Channel.one_sub_adjoint_kronecker_one_posSemidef (Φ : Channel n (n × n) ι)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) :
    ((1 : Matrix n n ℂ) - Φ.adjoint (P ⊗ₖ (1 : Matrix n n ℂ))).PosSemidef := by
  have hPpsd : P.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self P
    rwa [hP.eq, hP2] at this
  have hQpsd : ((1 : Matrix n n ℂ) - P).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self ((1 : Matrix n n ℂ) - P)
    rwa [(isHermitian_one.sub hP).eq, one_sub_proj_mul_self hP2] at this
  refine Φ.adjoint_le_one (hPpsd.kronecker Matrix.PosSemidef.one) ?_
  have : (1 : Matrix (n × n) (n × n) ℂ) - P ⊗ₖ (1 : Matrix n n ℂ)
      = ((1 : Matrix n n ℂ) - P) ⊗ₖ (1 : Matrix n n ℂ) := by
    ext ⟨a, c⟩ ⟨a', c'⟩
    simp only [Matrix.sub_apply, kronecker_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [this]
  exact hQpsd.kronecker Matrix.PosSemidef.one

theorem Channel.one_sub_adjoint_one_kronecker_posSemidef (Φ : Channel n (n × n) ι)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) :
    ((1 : Matrix n n ℂ) - Φ.adjoint ((1 : Matrix n n ℂ) ⊗ₖ P)).PosSemidef := by
  have hPpsd : P.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self P
    rwa [hP.eq, hP2] at this
  have hQpsd : ((1 : Matrix n n ℂ) - P).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self ((1 : Matrix n n ℂ) - P)
    rwa [(isHermitian_one.sub hP).eq, one_sub_proj_mul_self hP2] at this
  refine Φ.adjoint_le_one (Matrix.PosSemidef.one.kronecker hPpsd) ?_
  have : (1 : Matrix (n × n) (n × n) ℂ) - (1 : Matrix n n ℂ) ⊗ₖ P
      = (1 : Matrix n n ℂ) ⊗ₖ ((1 : Matrix n n ℂ) - P) := by
    ext ⟨a, c⟩ ⟨a', c'⟩
    simp only [Matrix.sub_apply, kronecker_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [this]
  exact Matrix.PosSemidef.one.kronecker hQpsd

/-- `⟨v| Φ† P |v⟩ = ∑ᵢ ⟨Kᵢ v| P |Kᵢ v⟩`. -/
theorem Channel.star_dotProduct_adjoint_mulVec (Φ : Channel n (n × n) ι)
    (P : Matrix (n × n) (n × n) ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (Φ.adjoint P *ᵥ v)
      = ∑ i, star (Φ.kraus i *ᵥ v) ⬝ᵥ (P *ᵥ (Φ.kraus i *ᵥ v)) := by
  rw [Channel.adjoint_def, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- The dual of `P ⊗ 1` fixes every vector `v` all of whose Kraus images lie in `range P ⊗ ℂⁿ`. -/
theorem Channel.adjoint_kronecker_one_mulVec_eq_self (Φ : Channel n (n × n) ι)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) {v : n → ℂ}
    (hv : ∀ i, (P ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (Φ.kraus i *ᵥ v) = Φ.kraus i *ᵥ v) :
    Φ.adjoint (P ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v = v := by
  have hle := Φ.one_sub_adjoint_kronecker_one_posSemidef hP hP2
  have hzero : star v ⬝ᵥ (((1 : Matrix n n ℂ) - Φ.adjoint (P ⊗ₖ (1 : Matrix n n ℂ))) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Φ.star_dotProduct_adjoint_mulVec,
      Φ.star_dotProduct_eq_sum_kraus v v]
    simp only [hv, sub_self]
  have := (hle.dotProduct_mulVec_zero_iff v).mp hzero
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  exact this.symm

theorem Channel.adjoint_one_kronecker_mulVec_eq_self (Φ : Channel n (n × n) ι)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) {v : n → ℂ}
    (hv : ∀ i, ((1 : Matrix n n ℂ) ⊗ₖ P) *ᵥ (Φ.kraus i *ᵥ v) = Φ.kraus i *ᵥ v) :
    Φ.adjoint ((1 : Matrix n n ℂ) ⊗ₖ P) *ᵥ v = v := by
  have hle := Φ.one_sub_adjoint_one_kronecker_posSemidef hP hP2
  have hzero : star v ⬝ᵥ (((1 : Matrix n n ℂ) - Φ.adjoint ((1 : Matrix n n ℂ) ⊗ₖ P)) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Φ.star_dotProduct_adjoint_mulVec,
      Φ.star_dotProduct_eq_sum_kraus v v]
    simp only [hv, sub_self]
  have := (hle.dotProduct_mulVec_zero_iff v).mp hzero
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  exact this.symm

omit [DecidableEq n] in
theorem star_dotProduct_proj_mulVec_eq_nsq {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (hP2 : P * P = P) (y : n → ℂ) : star y ⬝ᵥ (P *ᵥ y) = (nsq (P *ᵥ y) : ℂ) := by
  apply Complex.ext
  · rw [nsq_mulVec_of_proj hP hP2, Complex.ofReal_re]
  · rw [Complex.ofReal_im]
    simpa using hP.im_star_dotProduct_mulVec_self y

omit [Fintype n] in
theorem kronecker_one_sub_left (P : Matrix n n ℂ) :
    ((1 : Matrix n n ℂ) - P) ⊗ₖ (1 : Matrix n n ℂ) = 1 - P ⊗ₖ (1 : Matrix n n ℂ) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [Matrix.sub_apply, kronecker_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype n] in
theorem kronecker_one_sub_right (P : Matrix n n ℂ) :
    (1 : Matrix n n ℂ) ⊗ₖ ((1 : Matrix n n ℂ) - P) = 1 - (1 : Matrix n n ℂ) ⊗ₖ P := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [Matrix.sub_apply, kronecker_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **BC4 (i): the complement of a cloned subspace inside the support is confined too.** If `Φ`
broadcasts the positive semidefinite `τ`, `P_V` is a projector onto a subspace `V` of the support
of `τ`, and every Kraus operator maps `V` into `V ⊗ V`, then every Kraus operator maps
`W = supp τ ⊖ V` into `W ⊗ W`. The dual `Φ† (P_V ⊗ 1)` fixes `V`, so its excess over `P_V` is
positive semidefinite with zero trace against `τ`, hence kills the support; on `W` this says every
`Kᵢ w` lies in `V^⊥ ⊗ ℂⁿ`, symmetrically in `ℂⁿ ⊗ V^⊥`, and support confinement finishes. -/
theorem Channel.Broadcasts.kronecker_mulVec_kraus_mulVec_sub {τ : Matrix n n ℂ}
    (hτ : τ.PosSemidef) (h : Φ.Broadcasts τ)
    {PV : Matrix n n ℂ} (hPV : PV.IsHermitian) (hPV2 : PV * PV = PV) (hsub : suppProj τ * PV = PV)
    (hclone : ∀ i, (PV ⊗ₖ PV) * (Φ.kraus i * PV) = Φ.kraus i * PV) (i : ι) (x : n → ℂ) :
    ((suppProj τ - PV) ⊗ₖ (suppProj τ - PV)) *ᵥ (Φ.kraus i *ᵥ ((suppProj τ - PV) *ᵥ x))
      = Φ.kraus i *ᵥ ((suppProj τ - PV) *ᵥ x) := by
  set PS := suppProj τ with hPSdef
  have hPS : PS.IsHermitian := suppProj_isHermitian τ
  have hPS2 : PS * PS = PS := suppProj_mul_self τ
  have hPSτ : PS * τ = τ := suppProj_mul τ
  have hPVPS : PV * PS = PV := by
    have := congrArg conjTranspose hsub
    rwa [conjTranspose_mul, hPS.eq, hPV.eq] at this
  set PW := PS - PV with hPWdef
  have hPSPW : PS * PW = PW := by rw [hPWdef, Matrix.mul_sub, hPS2, hsub]
  have hPVPW : PV * PW = 0 := by rw [hPWdef, Matrix.mul_sub, hPVPS, hPV2, sub_self]
  set w := PW *ᵥ x with hwdef
  have hPSw : PS *ᵥ w = w := by rw [hwdef, Matrix.mulVec_mulVec, hPSPW]
  obtain ⟨y, hy⟩ := (suppProj_mulVec_eq_self_iff τ w).mp hPSw
  have hconf : (PS ⊗ₖ PS) *ᵥ (Φ.kraus i *ᵥ w) = Φ.kraus i *ᵥ w := by
    have := congrArg (fun N => N *ᵥ y) (h.kronecker_mul_kraus_mul hτ hPS hPS2 hPSτ i)
    simpa only [← Matrix.mulVec_mulVec, hy] using this
  have hPVw : PV *ᵥ w = 0 := by rw [hwdef, Matrix.mulVec_mulVec, hPVPW, Matrix.zero_mulVec]
  -- the generic half: a projector `R` on the product with `R (Kⱼ P_V v) = Kⱼ P_V v`,
  -- `Tr (Φ† R · τ) = Tr (P_V τ)`, gives `R (Kⱼ w) = 0`
  have key : ∀ R : Matrix (n × n) (n × n) ℂ, R.IsHermitian → R * R = R →
      (∀ v, Φ.adjoint R *ᵥ (PV *ᵥ v) = PV *ᵥ v) →
      (Φ.adjoint R * τ).trace = (PV * τ).trace →
      ∀ j, R *ᵥ (Φ.kraus j *ᵥ w) = 0 := by
    intro R hR hR2 hMv htrace j
    set M := Φ.adjoint R with hMdef
    have hRpsd : R.PosSemidef := by
      have := posSemidef_conjTranspose_mul_self R
      rwa [hR.eq, hR2] at this
    have hMpsd : M.PosSemidef := Φ.adjoint_posSemidef hRpsd
    have hM : M.IsHermitian := hMpsd.1
    have hMPV : M * PV = PV := by
      rw [Matrix.ext_iff_mulVec]; intro v; rw [← Matrix.mulVec_mulVec]; exact hMv v
    have hPVM : PV * M = PV := by
      have := congrArg conjTranspose hMPV
      rwa [conjTranspose_mul, hM.eq, hPV.eq] at this
    have hM0 : M - PV = (1 - PV)ᴴ * M * (1 - PV) := by
      rw [(isHermitian_one.sub hPV).eq]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hMPV, hPVM, hPV2]
      abel
    have hM0psd : (M - PV).PosSemidef := by
      rw [hM0]; exact hMpsd.conjTranspose_mul_mul_same _
    have htr : ((M - PV) * τ).trace = 0 := by
      rw [Matrix.sub_mul, Matrix.trace_sub, htrace, sub_self]
    have hM0τ : (M - PV) * τ = 0 := hM0psd.mul_eq_zero_of_trace_mul_eq_zero hτ htr
    have hwM : star w ⬝ᵥ (M *ᵥ w) = 0 := by
      have h1 : M *ᵥ w = PV *ᵥ w + (M - PV) *ᵥ w := by rw [Matrix.sub_mulVec]; abel
      have h3 : (M - PV) *ᵥ w = 0 := by
        rw [← hy, Matrix.mulVec_mulVec, hM0τ, Matrix.zero_mulVec]
      rw [h1, dotProduct_add, hPVw, h3]
      simp
    rw [hMdef, Φ.star_dotProduct_adjoint_mulVec] at hwM
    simp only [star_dotProduct_proj_mulVec_eq_nsq hR hR2] at hwM
    rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hwM
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => nsq_nonneg _).mp hwM j (Finset.mem_univ j)
    exact (nsq_eq_zero_iff _).mp this
  -- first factor
  have hR1 : (PV ⊗ₖ (1 : Matrix n n ℂ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_kronecker, conjTranspose_one, hPV.eq]
  have hR1sq : (PV ⊗ₖ (1 : Matrix n n ℂ)) * (PV ⊗ₖ 1) = PV ⊗ₖ 1 := by
    rw [← mul_kronecker_mul, hPV2, Matrix.one_mul]
  have hfix1 : ∀ j v, (PV ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (Φ.kraus j *ᵥ (PV *ᵥ v))
      = Φ.kraus j *ᵥ (PV *ᵥ v) := by
    intro j v
    have hc := congrArg (fun N => N *ᵥ v) (hclone j)
    simp only [← Matrix.mulVec_mulVec] at hc
    conv_lhs => rw [← hc]
    rw [Matrix.mulVec_mulVec, ← mul_kronecker_mul, hPV2, Matrix.one_mul, hc]
  have h1 := key (PV ⊗ₖ 1) hR1 hR1sq
    (fun v => Φ.adjoint_kronecker_one_mulVec_eq_self hPV hPV2 (hfix1 · v))
    (by rw [← Φ.adjoint_trace_mul, ← trace_traceRight, traceRight_kronecker_one_mul, h.1]) i
  -- second factor
  have hR2 : ((1 : Matrix n n ℂ) ⊗ₖ PV).IsHermitian := by
    rw [IsHermitian, conjTranspose_kronecker, conjTranspose_one, hPV.eq]
  have hR2sq : ((1 : Matrix n n ℂ) ⊗ₖ PV) * (1 ⊗ₖ PV) = 1 ⊗ₖ PV := by
    rw [← mul_kronecker_mul, hPV2, Matrix.one_mul]
  have hfix2 : ∀ j v, ((1 : Matrix n n ℂ) ⊗ₖ PV) *ᵥ (Φ.kraus j *ᵥ (PV *ᵥ v))
      = Φ.kraus j *ᵥ (PV *ᵥ v) := by
    intro j v
    have hc := congrArg (fun N => N *ᵥ v) (hclone j)
    simp only [← Matrix.mulVec_mulVec] at hc
    conv_lhs => rw [← hc]
    rw [Matrix.mulVec_mulVec, ← mul_kronecker_mul, hPV2, Matrix.one_mul, hc]
  have h2 := key (1 ⊗ₖ PV) hR2 hR2sq
    (fun v => Φ.adjoint_one_kronecker_mulVec_eq_self hPV hPV2 (hfix2 · v))
    (by rw [← Φ.adjoint_trace_mul, ← trace_traceLeft, traceLeft_one_kronecker_mul, h.2]) i
  -- assemble: `P_W ⊗ P_W = (P_S ⊗ P_S) ((1 − P_V) ⊗ 1) (1 ⊗ (1 − P_V))`
  have hfac : PW ⊗ₖ PW = (PS ⊗ₖ PS) * (((1 : Matrix n n ℂ) - PV) ⊗ₖ (1 : Matrix n n ℂ))
      * ((1 : Matrix n n ℂ) ⊗ₖ ((1 : Matrix n n ℂ) - PV)) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, hPWdef]
    simp only [Matrix.mul_one, Matrix.mul_sub, hsub]
  rw [hfac, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, kronecker_one_sub_right,
    Matrix.sub_mulVec, Matrix.one_mulVec, h2, sub_zero, kronecker_one_sub_left, Matrix.sub_mulVec,
    Matrix.one_mulVec, h1, sub_zero, hconf]

/-- `Tr_B ((A ⊗ B) Y (C ⊗ D)) = A · Tr_B (Y (1 ⊗ D B)) · C`. -/
theorem traceRight_kronecker_mul_mul_kronecker (A B C D : Matrix n n ℂ)
    (Y : Matrix (n × n) (n × n) ℂ) :
    traceRight ((A ⊗ₖ B) * Y * (C ⊗ₖ D))
      = A * traceRight (Y * ((1 : Matrix n n ℂ) ⊗ₖ (D * B))) * C := by
  have e1 : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have e2 : C ⊗ₖ D = ((1 : Matrix n n ℂ) ⊗ₖ D) * (C ⊗ₖ (1 : Matrix n n ℂ)) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [e1, e2,
    show (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B) * Y
        * (((1 : Matrix n n ℂ) ⊗ₖ D) * (C ⊗ₖ (1 : Matrix n n ℂ)))
      = (A ⊗ₖ (1 : Matrix n n ℂ)) * (((1 : Matrix n n ℂ) ⊗ₖ B) * (Y * ((1 : Matrix n n ℂ) ⊗ₖ D)))
        * (C ⊗ₖ (1 : Matrix n n ℂ)) by simp only [Matrix.mul_assoc],
    traceRight_mul_kronecker_one, traceRight_kronecker_one_mul, traceRight_one_kronecker_mul_comm,
    Matrix.mul_assoc Y, ← mul_kronecker_mul, Matrix.one_mul]

/-- `Tr_A ((A ⊗ B) Y (C ⊗ D)) = B · Tr_A (Y (C A ⊗ 1)) · D`. -/
theorem traceLeft_kronecker_mul_mul_kronecker (A B C D : Matrix n n ℂ)
    (Y : Matrix (n × n) (n × n) ℂ) :
    traceLeft ((A ⊗ₖ B) * Y * (C ⊗ₖ D))
      = B * traceLeft (Y * ((C * A) ⊗ₖ (1 : Matrix n n ℂ))) * D := by
  have e1 : A ⊗ₖ B = ((1 : Matrix n n ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix n n ℂ)) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have e2 : C ⊗ₖ D = (C ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ D) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [e1, e2,
    show ((1 : Matrix n n ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix n n ℂ)) * Y
        * ((C ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ D))
      = ((1 : Matrix n n ℂ) ⊗ₖ B) * ((A ⊗ₖ (1 : Matrix n n ℂ)) * (Y * (C ⊗ₖ (1 : Matrix n n ℂ))))
        * ((1 : Matrix n n ℂ) ⊗ₖ D) by simp only [Matrix.mul_assoc],
    traceLeft_mul_one_kronecker, traceLeft_one_kronecker_mul, traceLeft_kronecker_one_mul_comm,
    Matrix.mul_assoc Y, ← mul_kronecker_mul, Matrix.one_mul]

omit [DecidableEq n] in
/-- One Kraus term of a cross block is sandwiched between the two block projectors. -/
theorem kraus_block_sandwich {K : Matrix (n × n) n ℂ} {P Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    {RP RQ : Matrix (n × n) (n × n) ℂ} (hRQ : RQ.IsHermitian)
    (hKP : RP * (K * P) = K * P) (hKQ : RQ * (K * Q) = K * Q) (τ : Matrix n n ℂ) :
    K * (P * τ * Q) * Kᴴ = RP * (K * (P * τ * Q) * Kᴴ) * RQ := by
  have e : K * (P * τ * Q) * Kᴴ = (K * P) * τ * (K * Q)ᴴ := by
    rw [conjTranspose_mul, hQ.eq]; simp only [Matrix.mul_assoc]
  rw [e]
  conv_lhs => rw [← hKP, ← hKQ]
  rw [conjTranspose_mul, hRQ.eq]
  simp only [Matrix.mul_assoc]

/-- ★★ **BC4: a cloned subspace splits a broadcast state into blocks, each broadcast.** If `Φ`
broadcasts the positive semidefinite `τ`, `P_V` is a projector onto a subspace `V` of the support
`S` of `τ`, and every Kraus operator maps `V` into `V ⊗ V`, then with `P_W = P_S − P_V`:
`P_V τ P_W = 0` (so `τ = P_V τ P_V + P_W τ P_W`), and `Φ` broadcasts both blocks. The cross
blocks `Φ(P_V τ P_W)` are sandwiched between `P_V ⊗ P_V` and `P_W ⊗ P_W`, whose partial traces
vanish because `P_W P_V = 0`; the diagonal blocks are supported where they should be. -/
theorem Channel.Broadcasts.block_split {τ : Matrix n n ℂ} (hτ : τ.PosSemidef) (h : Φ.Broadcasts τ)
    {PV : Matrix n n ℂ} (hPV : PV.IsHermitian) (hPV2 : PV * PV = PV) (hsub : suppProj τ * PV = PV)
    (hclone : ∀ i, (PV ⊗ₖ PV) * (Φ.kraus i * PV) = Φ.kraus i * PV) :
    PV * τ * (suppProj τ - PV) = 0 ∧ Φ.Broadcasts (PV * τ * PV) ∧
      Φ.Broadcasts ((suppProj τ - PV) * τ * (suppProj τ - PV)) := by
  set PS := suppProj τ with hPSdef
  have hPS : PS.IsHermitian := suppProj_isHermitian τ
  have hPS2 : PS * PS = PS := suppProj_mul_self τ
  have hPSτ : PS * τ = τ := suppProj_mul τ
  have hτPS : τ * PS = τ := mul_suppProj_of_isHermitian hτ.1
  have hPVPS : PV * PS = PV := by
    have := congrArg conjTranspose hsub
    rwa [conjTranspose_mul, hPS.eq, hPV.eq] at this
  set PW := PS - PV with hPWdef
  have hPW : PW.IsHermitian := hPS.sub hPV
  have hPVPW : PV * PW = 0 := by rw [hPWdef, Matrix.mul_sub, hPVPS, hPV2, sub_self]
  have hPWPV : PW * PV = 0 := by rw [hPWdef, Matrix.sub_mul, hsub, hPV2, sub_self]
  have hKW : ∀ i, (PW ⊗ₖ PW) * (Φ.kraus i * PW) = Φ.kraus i * PW := by
    intro i
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h.kronecker_mulVec_kraus_mulVec_sub hτ hPV hPV2 hsub hclone i x
  have hVV : (PV ⊗ₖ PV).IsHermitian := by rw [IsHermitian, conjTranspose_kronecker, hPV.eq]
  have hWW : (PW ⊗ₖ PW).IsHermitian := by rw [IsHermitian, conjTranspose_kronecker, hPW.eq]
  -- the four blocks and their images
  have himage : ∀ (P Q : Matrix n n ℂ) (RP RQ : Matrix (n × n) (n × n) ℂ), Q.IsHermitian →
      RQ.IsHermitian → (∀ i, RP * (Φ.kraus i * P) = Φ.kraus i * P) →
      (∀ i, RQ * (Φ.kraus i * Q) = Φ.kraus i * Q) →
      Φ.apply (P * τ * Q) = RP * Φ.apply (P * τ * Q) * RQ := by
    intro P Q RP RQ hQ hRQ hKP hKQ
    rw [Channel.apply_def, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => kraus_block_sandwich hQ hRQ (hKP i) (hKQ i) τ
  have hVW := himage PV PW (PV ⊗ₖ PV) (PW ⊗ₖ PW) hPW hWW hclone hKW
  have hWV := himage PW PV (PW ⊗ₖ PW) (PV ⊗ₖ PV) hPV hVV hKW hclone
  have hVVi := himage PV PV (PV ⊗ₖ PV) (PV ⊗ₖ PV) hPV hVV hclone hclone
  have hWWi := himage PW PW (PW ⊗ₖ PW) (PW ⊗ₖ PW) hPW hWW hKW hKW
  -- partial traces of the cross blocks vanish
  have hPW2 : PW * PW = PW := by
    rw [hPWdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPS2, hsub, hPVPS, hPV2]
    abel
  have hcrossR : ∀ (P Q : Matrix n n ℂ) (X : Matrix (n × n) (n × n) ℂ), Q * P = 0 →
      X = (P ⊗ₖ P) * X * (Q ⊗ₖ Q) → traceRight X = 0 := by
    intro P Q X hQP hX
    rw [hX, traceRight_kronecker_mul_mul_kronecker, hQP, Matrix.kronecker_zero, Matrix.mul_zero,
      traceRight_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hcrossL : ∀ (P Q : Matrix n n ℂ) (X : Matrix (n × n) (n × n) ℂ), Q * P = 0 →
      X = (P ⊗ₖ P) * X * (Q ⊗ₖ Q) → traceLeft X = 0 := by
    intro P Q X hQP hX
    rw [hX, traceLeft_kronecker_mul_mul_kronecker, hQP, Matrix.zero_kronecker, Matrix.mul_zero,
      traceLeft_zero, Matrix.mul_zero, Matrix.zero_mul]
  -- the diagonal blocks are supported on their subspace
  have hdiagR : ∀ (P : Matrix n n ℂ) (X : Matrix (n × n) (n × n) ℂ), P * P = P →
      X = (P ⊗ₖ P) * X * (P ⊗ₖ P) → P * traceRight X * P = traceRight X := by
    intro P X hP2 hX
    have hXt : traceRight X = P * traceRight (X * ((1 : Matrix n n ℂ) ⊗ₖ (P * P))) * P := by
      conv_lhs => rw [hX]
      exact traceRight_kronecker_mul_mul_kronecker P P P P X
    rw [hXt]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hP2]
  have hdiagL : ∀ (P : Matrix n n ℂ) (X : Matrix (n × n) (n × n) ℂ), P * P = P →
      X = (P ⊗ₖ P) * X * (P ⊗ₖ P) → P * traceLeft X * P = traceLeft X := by
    intro P X hP2 hX
    have hXt : traceLeft X = P * traceLeft (X * ((P * P) ⊗ₖ (1 : Matrix n n ℂ))) * P := by
      conv_lhs => rw [hX]
      exact traceLeft_kronecker_mul_mul_kronecker P P P P X
    rw [hXt]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hP2]
  -- the decomposition of `τ`
  have hτdec : τ = PV * τ * PV + PV * τ * PW + PW * τ * PV + PW * τ * PW := by
    have : PS = PV + PW := by rw [hPWdef]; abel
    calc τ = PS * τ * PS := by rw [hPSτ, hτPS]
      _ = _ := by rw [this]; simp only [Matrix.add_mul, Matrix.mul_add]; abel
  have hτR : τ = traceRight (Φ.apply (PV * τ * PV)) + traceRight (Φ.apply (PW * τ * PW)) := by
    have := h.1
    conv_lhs at this => rw [hτdec]
    rw [Channel.apply_add, Channel.apply_add, Channel.apply_add, traceRight_add, traceRight_add,
      traceRight_add, hcrossR PV PW _ hPWPV hVW, hcrossR PW PV _ hPVPW hWV, add_zero,
      add_zero] at this
    exact this.symm
  have hτL : τ = traceLeft (Φ.apply (PV * τ * PV)) + traceLeft (Φ.apply (PW * τ * PW)) := by
    have := h.2
    conv_lhs at this => rw [hτdec]
    rw [Channel.apply_add, Channel.apply_add, Channel.apply_add, traceLeft_add, traceLeft_add,
      traceLeft_add, hcrossL PV PW _ hPWPV hVW, hcrossL PW PV _ hPVPW hWV, add_zero,
      add_zero] at this
    exact this.symm
  have hRV := hdiagR PV _ hPV2 hVVi
  have hRW := hdiagR PW _ hPW2 hWWi
  have hLV := hdiagL PV _ hPV2 hVVi
  have hLW := hdiagL PW _ hPW2 hWWi
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- `P_V τ P_W = 0`
    conv_lhs => rw [hτR]
    rw [Matrix.mul_add, Matrix.add_mul, ← hRV, ← hRW]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PV PW, hPVPW, Matrix.zero_mul, Matrix.mul_zero]
    simp
  · conv_rhs => rw [hτR]
    rw [Matrix.mul_add, Matrix.add_mul, ← hRV, ← hRW]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PV PV, hPV2, ← Matrix.mul_assoc PV PW, hPVPW, Matrix.zero_mul, add_zero]
  · conv_rhs => rw [hτL]
    rw [Matrix.mul_add, Matrix.add_mul, ← hLV, ← hLW]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PV PV, hPV2, ← Matrix.mul_assoc PV PW, hPVPW, Matrix.zero_mul, add_zero]
  · conv_rhs => rw [hτR]
    rw [Matrix.mul_add, Matrix.add_mul, ← hRV, ← hRW]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PW PV, hPWPV, Matrix.zero_mul, zero_add, hPW2, ← Matrix.mul_assoc PW PW,
      hPW2]
  · conv_rhs => rw [hτL]
    rw [Matrix.mul_add, Matrix.add_mul, ← hLV, ← hLW]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PW PV, hPWPV, Matrix.zero_mul, zero_add, hPW2, ← Matrix.mul_assoc PW PW,
      hPW2]

/-! ### Eigen-expansions -/

section EigenExpansion

variable (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))

/-- Parseval: `‖z‖² = ∑ₖ |⟨b k|z⟩|²`. -/
theorem nsq_eq_sum_onb (z : n → ℂ) : nsq z = ∑ k, ‖star (onbVec b k) ⬝ᵥ z‖ ^ 2 := by
  have h1 : star z ⬝ᵥ z = star z ⬝ᵥ ((∑ k, onbProj b k) *ᵥ z) := by
    rw [sum_onbProj, Matrix.one_mulVec]
  rw [nsq, h1, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_dotProduct_onbProj_mulVec, Complex.ofReal_re]

/-- The Rayleigh quotient of a matrix diagonal in `b`: `⟨z|Q|z⟩ = ∑ₖ rₖ |⟨b k|z⟩|²`. -/
theorem re_star_dotProduct_mulVec_eq_sum_onb {Q : Matrix n n ℂ} {r : n → ℂ}
    (hdiag : ∀ k, Q *ᵥ onbVec b k = r k • onbVec b k) (z : n → ℂ) :
    (star z ⬝ᵥ (Q *ᵥ z)).re
      = ∑ k, (r k * ((‖star (onbVec b k) ⬝ᵥ z‖ ^ 2 : ℝ) : ℂ)).re := by
  have hQz : Q *ᵥ z = ∑ k, r k • (onbProj b k *ᵥ z) := by
    rw [eq_sum_smul_onbProj b hdiag, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec]
  rw [hQz, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_smul, star_dotProduct_onbProj_mulVec, smul_eq_mul]

theorem onbProj_mul_onbProj (j k : n) :
    onbProj b j * onbProj b k = if j = k then onbProj b k else 0 := by
  rw [onbProj, onbProj, vecMulVec_mul_vecMulVec, star_onbVec_dotProduct]
  split_ifs with h
  · subst h; rw [one_smul]
  · rw [zero_smul, Matrix.vecMulVec_zero]

/-- The projector onto the span of a subfamily of the basis. -/
noncomputable def onbProjSet (K : Finset n) : Matrix n n ℂ := ∑ k ∈ K, onbProj b k

omit [DecidableEq n] in
theorem onbProjSet_isHermitian (K : Finset n) : (onbProjSet b K).IsHermitian := by
  rw [onbProjSet, IsHermitian, conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [onbProj, conjTranspose_vecMulVec, star_star]

theorem onbProjSet_mul_self (K : Finset n) : onbProjSet b K * onbProjSet b K = onbProjSet b K := by
  rw [onbProjSet, Finset.sum_mul_sum]
  simp only [onbProj_mul_onbProj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_ite_eq' K k, if_pos hk]

omit [DecidableEq n] in
theorem star_dotProduct_onbProjSet_mulVec (K : Finset n) (z : n → ℂ) :
    star z ⬝ᵥ (onbProjSet b K *ᵥ z) = ((∑ k ∈ K, ‖star (onbVec b k) ⬝ᵥ z‖ ^ 2 : ℝ) : ℂ) := by
  rw [onbProjSet, Matrix.sum_mulVec, dotProduct_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _ => star_dotProduct_onbProj_mulVec b k z

end EigenExpansion

/-! ### BC5: the segment through two distinct states meets the boundary of the cone -/

section Boundary

omit [DecidableEq n] in
/-- A nonzero traceless Hermitian matrix has a direction of negative expectation. -/
theorem exists_re_star_dotProduct_neg_of_trace_eq_zero {d : Matrix n n ℂ} (hd : d.IsHermitian)
    (htr : d.trace = 0) (hne : d ≠ 0) : ∃ v, (star v ⬝ᵥ (d *ᵥ v)).re < 0 := by
  by_contra hcon
  push Not at hcon
  have hpsd : d.PosSemidef := posSemidef_of_isHermitian_of_re_nonneg hd hcon
  exact hne ((hpsd.trace_eq_zero_iff).mp htr)

/-- ★★ **BC5. The segment through two distinct states meets the boundary of the cone.** For
positive semidefinite `ρ ≠ σ` of trace one there is `l ≥ 1` such that
`τ = σ + l (ρ − σ) = l ρ + (1 − l) σ` is positive semidefinite and has a kernel vector outside the
kernel of `ρ + σ` (so its support is strictly smaller). The set of such `l` is closed and bounded
(the traceless `ρ − σ` has a negative direction), so its supremum `l₁` belongs to it; if `τ = f l₁`
had no such kernel vector, `f (l₁ + δ)` would still be positive semidefinite for small `δ`
(the eigenvectors of `τ` with eigenvalue `0` lie in `ker (ρ + σ)`, hence in `ker (ρ − σ)`, and on
the rest the positive eigenvalues dominate), contradicting maximality. -/
theorem exists_boundary_point [Nonempty n] {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (hne : ρ ≠ σ) :
    ∃ l : ℝ, 1 ≤ l ∧ (σ + (l : ℂ) • (ρ - σ)).PosSemidef ∧
      ∃ x, (σ + (l : ℂ) • (ρ - σ)) *ᵥ x = 0 ∧ (ρ + σ) *ᵥ x ≠ 0 := by
  classical
  set d := ρ - σ with hddef
  have hd : d.IsHermitian := hρ.1.sub hσ.1
  have hdtr : d.trace = 0 := by rw [hddef, trace_sub, hρ1, hσ1, sub_self]
  have hdne : d ≠ 0 := by rw [hddef]; exact sub_ne_zero.mpr hne
  set f : ℝ → Matrix n n ℂ := fun l => σ + (l : ℂ) • d with hfdef
  have hf_herm : ∀ l, (f l).IsHermitian := fun l =>
    hσ.1.add (hd.smul (Complex.conj_ofReal l))
  have hform : ∀ l x, (star x ⬝ᵥ (f l *ᵥ x)).re
      = (star x ⬝ᵥ (σ *ᵥ x)).re + l * (star x ⬝ᵥ (d *ᵥ x)).re := by
    intro l x
    simp only [hfdef, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  have hf_psd_iff : ∀ l, (f l).PosSemidef ↔
      ∀ x, 0 ≤ (star x ⬝ᵥ (σ *ᵥ x)).re + l * (star x ⬝ᵥ (d *ᵥ x)).re := by
    intro l
    constructor
    · intro h x
      rw [← hform]
      exact (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg x)).1
    · intro h
      refine posSemidef_of_isHermitian_of_re_nonneg (hf_herm l) fun x => ?_
      rw [hform]; exact h x
  set L : Set ℝ := {l | 1 ≤ l ∧ (f l).PosSemidef} with hLdef
  have hf1 : f 1 = ρ := by simp [hfdef, hddef]
  have h1L : (1 : ℝ) ∈ L := ⟨le_rfl, by rw [hf1]; exact hρ⟩
  obtain ⟨v, hv⟩ := exists_re_star_dotProduct_neg_of_trace_eq_zero hd hdtr hdne
  have hbdd : BddAbove L := by
    refine ⟨(star v ⬝ᵥ (σ *ᵥ v)).re / (-(star v ⬝ᵥ (d *ᵥ v)).re), fun l hl => ?_⟩
    have := (hf_psd_iff l).mp hl.2 v
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hclosed : IsClosed L := by
    have : L = Set.Ici (1 : ℝ) ∩ ⋂ x : n → ℂ,
        {l : ℝ | 0 ≤ (star x ⬝ᵥ (σ *ᵥ x)).re + l * (star x ⬝ᵥ (d *ᵥ x)).re} := by
      ext l
      simp only [hLdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iInter,
        hf_psd_iff]
    rw [this]
    exact isClosed_Ici.inter (isClosed_iInter fun x =>
      isClosed_le continuous_const (continuous_const.add (continuous_id.mul continuous_const)))
  have hmem : sSup L ∈ L := hclosed.csSup_mem ⟨1, h1L⟩ hbdd
  set l₁ := sSup L with hl₁
  refine ⟨l₁, hmem.1, hmem.2, ?_⟩
  by_contra hcon
  push Not at hcon
  -- the perturbation argument
  set τ := f l₁ with hτdef
  have hτ : τ.PosSemidef := hmem.2
  set b := hτ.1.eigenvectorBasis with hb
  set e := hτ.1.eigenvalues with he
  have he0 : ∀ k, 0 ≤ e k := hτ.eigenvalues_nonneg
  have hdiag : ∀ k, τ *ᵥ onbVec b k = ((e k : ℝ) : ℂ) • onbVec b k := fun k => by
    have := hτ.1.mulVec_eigenvectorBasis k
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
    exact this
  -- eigenvectors of eigenvalue `0` kill `ρ`, `σ` and `d`
  have hker : ∀ k, e k = 0 → d *ᵥ onbVec b k = 0 := by
    intro k hk
    have hτk : τ *ᵥ onbVec b k = 0 := by rw [hdiag, hk]; simp
    have hsum := hcon _ hτk
    have h0 : star (onbVec b k) ⬝ᵥ (ρ *ᵥ onbVec b k) + star (onbVec b k) ⬝ᵥ (σ *ᵥ onbVec b k)
        = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hsum, dotProduct_zero]
    obtain ⟨hρ0, hσ0⟩ := (add_eq_zero_iff_of_nonneg (hρ.dotProduct_mulVec_nonneg _)
      (hσ.dotProduct_mulVec_nonneg _)).mp h0
    rw [hddef, Matrix.sub_mulVec, (hρ.dotProduct_mulVec_zero_iff _).mp hρ0,
      (hσ.dotProduct_mulVec_zero_iff _).mp hσ0, sub_zero]
  -- the positive eigenvalues
  set K' : Finset n := Finset.univ.filter (fun k => e k ≠ 0) with hK'
  have hK'ne : K'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ k, e k = 0 := fun k => by
      by_contra h
      have : k ∈ K' := by rw [hK']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty k)
    have hsum0 : ρ + σ = 0 := by
      rw [← Matrix.mul_one (ρ + σ), ← sum_onbProj b, Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [onbProj, mul_vecMulVec, hcon _ (by rw [hdiag, hall k]; simp), Matrix.zero_vecMulVec]
    have := congrArg Matrix.trace hsum0
    rw [trace_add, hρ1, hσ1, trace_zero] at this
    norm_num at this
  set ε := K'.inf' hK'ne e with hε
  have hεpos : 0 < ε := by
    rw [hε, Finset.lt_inf'_iff]
    intro k hk
    exact lt_of_le_of_ne (he0 k) (Ne.symm (Finset.mem_filter.mp hk).2)
  have hεle : ∀ k ∈ K', ε ≤ e k := fun k hk => Finset.inf'_le _ hk
  -- a bound on the negative part of `d`
  obtain ⟨μ', -, -, -, hbound⟩ := IsHermitian.exists_top_eigenvalue (Q := -d) hd.neg
  set m := max μ' 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  have hbound' : ∀ y, -(star y ⬝ᵥ (d *ᵥ y)).re ≤ m * nsq y := fun y => by
    have := hbound y
    rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] at this
    calc _ ≤ μ' * nsq y := this
      _ ≤ m * nsq y := mul_le_mul_of_nonneg_right (le_max_left _ _) (nsq_nonneg _)
  set δ := ε / (m + 1) with hδ
  have hδpos : 0 < δ := div_pos hεpos (by linarith)
  have hδm : δ * m ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  -- `f (l₁ + δ)` is still positive semidefinite
  have hpsd : (f (l₁ + δ)).PosSemidef := by
    rw [hf_psd_iff]
    intro x
    have hτx : (star x ⬝ᵥ (τ *ᵥ x)).re
        = (star x ⬝ᵥ (σ *ᵥ x)).re + l₁ * (star x ⬝ᵥ (d *ᵥ x)).re := hform l₁ x
    have hexp : (star x ⬝ᵥ (τ *ᵥ x)).re = ∑ k, e k * ‖star (onbVec b k) ⬝ᵥ x‖ ^ 2 := by
      rw [re_star_dotProduct_mulVec_eq_sum_onb b hdiag]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    set P' := onbProjSet b K' with hP'
    have hdP'' : d = d * P' := by
      calc d = d * ∑ k, onbProj b k := by rw [sum_onbProj, Matrix.mul_one]
        _ = ∑ k, d * onbProj b k := Finset.mul_sum _ _ _
        _ = ∑ k ∈ K', d * onbProj b k := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro k _ hk
            have hk0 : e k = 0 := by
              by_contra h
              exact hk (by rw [hK']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            rw [onbProj, mul_vecMulVec, hker k hk0, Matrix.zero_vecMulVec]
        _ = d * P' := by rw [hP', onbProjSet, Finset.mul_sum]
    have hdP' : d * P' = d := hdP''.symm
    have hP'd : P' * d = d := by
      have := congrArg conjTranspose hdP'
      rwa [conjTranspose_mul, (onbProjSet_isHermitian b K').eq, hd.eq] at this
    have hdx : (star x ⬝ᵥ (d *ᵥ x)).re = (star (P' *ᵥ x) ⬝ᵥ (d *ᵥ (P' *ᵥ x))).re := by
      rw [Matrix.mulVec_mulVec, hdP', star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
        (onbProjSet_isHermitian b K').eq, hP'd]
    have hnsqP' : nsq (P' *ᵥ x) = ∑ k ∈ K', ‖star (onbVec b k) ⬝ᵥ x‖ ^ 2 := by
      rw [nsq_mulVec_of_proj (onbProjSet_isHermitian b K') (onbProjSet_mul_self b K'),
        star_dotProduct_onbProjSet_mulVec, Complex.ofReal_re]
    set S := ∑ k ∈ K', ‖star (onbVec b k) ⬝ᵥ x‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
    have hd_lb : -(m * S) ≤ (star x ⬝ᵥ (d *ᵥ x)).re := by
      rw [hdx]
      have := hbound' (P' *ᵥ x)
      rw [hnsqP'] at this
      linarith
    have hτ_lb : ε * S ≤ (star x ⬝ᵥ (τ *ᵥ x)).re := by
      rw [hexp, hS, Finset.mul_sum]
      calc ∑ k ∈ K', ε * ‖star (onbVec b k) ⬝ᵥ x‖ ^ 2
          ≤ ∑ k ∈ K', e k * ‖star (onbVec b k) ⬝ᵥ x‖ ^ 2 :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hεle k hk) (sq_nonneg _)
        _ ≤ ∑ k, e k * ‖star (onbVec b k) ⬝ᵥ x‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun k _ _ => mul_nonneg (he0 k) (sq_nonneg _)
    have h1 : δ * (-(m * S)) ≤ δ * (star x ⬝ᵥ (d *ᵥ x)).re :=
      mul_le_mul_of_nonneg_left hd_lb hδpos.le
    have h2 : 0 ≤ (ε - δ * m) * S := mul_nonneg (by linarith) hS0
    nlinarith [hτx, hτ_lb, h1, h2]
  have hin : l₁ + δ ∈ L := ⟨by linarith [hmem.1], hpsd⟩
  have := le_csSup hbdd hin
  linarith

end Boundary

end BlockSplit


/-! ### Kernel facts -/

section Kernels

/-- The support projector of a Hermitian matrix vanishes exactly on its kernel. -/
theorem suppProj_mulVec_eq_zero_iff {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    suppProj A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  rw [suppProj_mulVec]
  constructor
  · intro h
    have h' : (LinearMap.range (Matrix.toEuclideanLin A)).starProjection (WithLp.toLp 2 x) = 0 := by
      apply WithLp.ofLp_injective
      simpa using h
    have hmem := (Submodule.starProjection_apply_eq_zero_iff _).mp h'
    -- `x ⊥ range A`, so `⟨A y, x⟩ = 0` for all `y`; with `A` Hermitian, `A x = 0`
    have hall : ∀ y : n → ℂ, star (A *ᵥ y) ⬝ᵥ x = 0 := by
      intro y
      have := (Submodule.mem_orthogonal _ _).mp hmem (Matrix.toEuclideanLin A (WithLp.toLp 2 y))
        ⟨WithLp.toLp 2 y, rfl⟩
      rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
        WithLp.ofLp_toLp, dotProduct_comm] at this
      exact this
    -- take `y = A x`
    have h2 := hall (A *ᵥ x)
    rw [star_mulVec, ← dotProduct_mulVec, hA.eq] at h2
    exact dotProduct_star_self_eq_zero.mp h2
  · intro h
    have hmem : WithLp.toLp 2 x ∈ (LinearMap.range (Matrix.toEuclideanLin A))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro u ⟨y, rfl⟩
      rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
        WithLp.ofLp_toLp, star_mulVec, dotProduct_comm, ← dotProduct_mulVec, hA.eq, h,
        dotProduct_zero]
    rw [(Submodule.starProjection_apply_eq_zero_iff _).mpr hmem]
    rfl

omit [DecidableEq n] in
/-- A positive combination of positive semidefinite matrices vanishes on `x` iff both do. -/
theorem _root_.Matrix.PosSemidef.add_mulVec_eq_zero_iff {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (x : n → ℂ) : (A + B) *ᵥ x = 0 ↔ A *ᵥ x = 0 ∧ B *ᵥ x = 0 := by
  constructor
  · intro h
    have h0 : star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ x) = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, h, dotProduct_zero]
    obtain ⟨hA0, hB0⟩ := (add_eq_zero_iff_of_nonneg (hA.dotProduct_mulVec_nonneg _)
      (hB.dotProduct_mulVec_nonneg _)).mp h0
    exact ⟨(hA.dotProduct_mulVec_zero_iff _).mp hA0, (hB.dotProduct_mulVec_zero_iff _).mp hB0⟩
  · rintro ⟨h1, h2⟩
    rw [Matrix.add_mulVec, h1, h2, add_zero]

omit [DecidableEq n] in
theorem smul_mulVec_eq_zero_iff {A : Matrix n n ℂ} {c : ℂ} (hc : c ≠ 0) (x : n → ℂ) :
    (c • A) *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  rw [Matrix.smul_mulVec, smul_eq_zero, or_iff_right hc]

omit [DecidableEq n] in
/-- **Strict rank comparison from a strict kernel inclusion.** -/
theorem rank_lt_rank_of_ker {A B : Matrix n n ℂ} (hAB : ∀ x, B *ᵥ x = 0 → A *ᵥ x = 0)
    {x : n → ℂ} (hx : A *ᵥ x = 0) (hBx : B *ᵥ x ≠ 0) : A.rank < B.rank := by
  have hker : LinearMap.ker B.mulVecLin < LinearMap.ker A.mulVecLin := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun heq => ?_
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
      exact hAB y hy
    · have : x ∈ LinearMap.ker B.mulVecLin := by
        rw [heq, LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
      exact hBx this
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have h3 := Submodule.finrank_lt_finrank_of_lt hker
  unfold Matrix.rank
  omega

end Kernels

/-! ### The intersection projector, and intersections of tensor squares -/

section Intersection

omit [DecidableEq n] in
theorem proj_posSemidef {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) :
    P.PosSemidef := by
  have := posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hP2] at this

theorem one_sub_proj_posSemidef {P : Matrix n n ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) :
    ((1 : Matrix n n ℂ) - P).PosSemidef :=
  proj_posSemidef (isHermitian_one.sub hP) (one_sub_proj_mul_self hP2)

/-- The projector onto the intersection of the ranges of two projectors:
`1 − suppProj ((1 − P₁) + (1 − P₂))`, since the kernel of the positive semidefinite sum is the
intersection of the kernels. -/
noncomputable def interProj (P₁ P₂ : Matrix n n ℂ) : Matrix n n ℂ :=
  1 - suppProj ((1 - P₁) + (1 - P₂))

theorem interProj_isHermitian (P₁ P₂ : Matrix n n ℂ) : (interProj P₁ P₂).IsHermitian :=
  isHermitian_one.sub (suppProj_isHermitian _)

theorem interProj_mul_self (P₁ P₂ : Matrix n n ℂ) :
    interProj P₁ P₂ * interProj P₁ P₂ = interProj P₁ P₂ :=
  one_sub_proj_mul_self (suppProj_mul_self _)

theorem interProj_mulVec_eq_self_iff {P₁ P₂ : Matrix n n ℂ} (hP₁ : P₁.IsHermitian)
    (hP₁2 : P₁ * P₁ = P₁) (hP₂ : P₂.IsHermitian) (hP₂2 : P₂ * P₂ = P₂) (x : n → ℂ) :
    interProj P₁ P₂ *ᵥ x = x ↔ P₁ *ᵥ x = x ∧ P₂ *ᵥ x = x := by
  have hQ : ((1 : Matrix n n ℂ) - P₁ + (1 - P₂)).IsHermitian :=
    (isHermitian_one.sub hP₁).add (isHermitian_one.sub hP₂)
  rw [interProj, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_self, suppProj_mulVec_eq_zero_iff hQ,
    (one_sub_proj_posSemidef hP₁ hP₁2).add_mulVec_eq_zero_iff
      (one_sub_proj_posSemidef hP₂ hP₂2), Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [sub_eq_zero]
  exact and_congr eq_comm eq_comm

theorem mul_interProj {P₁ P₂ : Matrix n n ℂ} (hP₁ : P₁.IsHermitian)
    (hP₁2 : P₁ * P₁ = P₁) (hP₂ : P₂.IsHermitian) (hP₂2 : P₂ * P₂ = P₂) :
    P₁ * interProj P₁ P₂ = interProj P₁ P₂ ∧ P₂ * interProj P₁ P₂ = interProj P₁ P₂ := by
  constructor <;>
  · rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec]
    have h := (interProj_mulVec_eq_self_iff hP₁ hP₁2 hP₂ hP₂2 (interProj P₁ P₂ *ᵥ x)).mp
      (by rw [Matrix.mulVec_mulVec, interProj_mul_self])
    first | exact h.1 | exact h.2

theorem kronecker_one_mulVec_apply (A : Matrix n n ℂ) (z : n × n → ℂ) (a c : n) :
    ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ z) (a, c) = (A *ᵥ fun a' => z (a', c)) a := by
  classical
  simp only [Matrix.mulVec, dotProduct, kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem one_kronecker_mulVec_apply (B : Matrix n n ℂ) (z : n × n → ℂ) (a c : n) :
    (((1 : Matrix n n ℂ) ⊗ₖ B) *ᵥ z) (a, c) = (B *ᵥ fun c' => z (a, c')) c := by
  classical
  simp only [Matrix.mulVec, dotProduct, kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type,
    ite_mul, zero_mul, one_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- A vector fixed by `P ⊗ P` is fixed by `P ⊗ 1` and by `1 ⊗ P`. -/
theorem kronecker_one_mulVec_eq_self_of {P : Matrix n n ℂ} (hP2 : P * P = P) {z : n × n → ℂ}
    (h : (P ⊗ₖ P) *ᵥ z = z) :
    (P ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ z = z ∧ ((1 : Matrix n n ℂ) ⊗ₖ P) *ᵥ z = z := by
  constructor
  · conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← mul_kronecker_mul, hP2, Matrix.one_mul, h]
  · conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← mul_kronecker_mul, hP2, Matrix.one_mul, h]

/-- **Intersections of tensor squares**: a vector in `S₁ ⊗ S₁` and in `S₂ ⊗ S₂` lies in
`(S₁ ∩ S₂) ⊗ (S₁ ∩ S₂)`, column by column and row by row. -/
theorem interProj_kronecker_mulVec_eq_self {P₁ P₂ : Matrix n n ℂ} (hP₁ : P₁.IsHermitian)
    (hP₁2 : P₁ * P₁ = P₁) (hP₂ : P₂.IsHermitian) (hP₂2 : P₂ * P₂ = P₂) {z : n × n → ℂ}
    (h1 : (P₁ ⊗ₖ P₁) *ᵥ z = z) (h2 : (P₂ ⊗ₖ P₂) *ᵥ z = z) :
    (interProj P₁ P₂ ⊗ₖ interProj P₁ P₂) *ᵥ z = z := by
  set I := interProj P₁ P₂ with hI
  have hIleft : (I ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ z = z := by
    funext ⟨a, c⟩
    rw [kronecker_one_mulVec_apply]
    have hc1 : P₁ *ᵥ (fun a' => z (a', c)) = fun a' => z (a', c) := by
      funext a'
      have := congrFun (kronecker_one_mulVec_eq_self_of hP₁2 h1).1 (a', c)
      rwa [kronecker_one_mulVec_apply] at this
    have hc2 : P₂ *ᵥ (fun a' => z (a', c)) = fun a' => z (a', c) := by
      funext a'
      have := congrFun (kronecker_one_mulVec_eq_self_of hP₂2 h2).1 (a', c)
      rwa [kronecker_one_mulVec_apply] at this
    exact congrFun ((interProj_mulVec_eq_self_iff hP₁ hP₁2 hP₂ hP₂2 _).mpr ⟨hc1, hc2⟩) a
  have hIright : ((1 : Matrix n n ℂ) ⊗ₖ I) *ᵥ z = z := by
    funext ⟨a, c⟩
    rw [one_kronecker_mulVec_apply]
    have hc1 : P₁ *ᵥ (fun c' => z (a, c')) = fun c' => z (a, c') := by
      funext c'
      have := congrFun (kronecker_one_mulVec_eq_self_of hP₁2 h1).2 (a, c')
      rwa [one_kronecker_mulVec_apply] at this
    have hc2 : P₂ *ᵥ (fun c' => z (a, c')) = fun c' => z (a, c') := by
      funext c'
      have := congrFun (kronecker_one_mulVec_eq_self_of hP₂2 h2).2 (a, c')
      rwa [one_kronecker_mulVec_apply] at this
    exact congrFun ((interProj_mulVec_eq_self_iff hP₁ hP₁2 hP₂ hP₂2 _).mpr ⟨hc1, hc2⟩) c
  calc (I ⊗ₖ I) *ᵥ z = (I ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (((1 : Matrix n n ℂ) ⊗ₖ I) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    _ = z := by rw [hIright, hIleft]

end Intersection

/-! ### BC6: the rank induction, and the BCFJS theorem -/

section Main

variable {ι : Type*} [Fintype ι] {Φ : Channel n (n × n) ι}

omit [DecidableEq n] in
/-- Normalisation of a nonzero positive semidefinite matrix to trace one. -/
theorem _root_.Matrix.PosSemidef.exists_smul_trace_one {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (h0 : ρ ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (((t⁻¹ : ℝ) : ℂ) • ρ).PosSemidef ∧ (((t⁻¹ : ℝ) : ℂ) • ρ).trace = 1 ∧
      ρ = (t : ℂ) • (((t⁻¹ : ℝ) : ℂ) • ρ) := by
  have htr0 : ρ.trace ≠ 0 := fun h => h0 ((hρ.trace_eq_zero_iff).mp h)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hρ.trace_nonneg
  set t := ρ.trace.re with ht
  have htr : ρ.trace = (t : ℂ) := Complex.ext rfl (by simp [← him])
  have htpos : 0 < t := lt_of_le_of_ne hre fun h => htr0 (by rw [htr, ← h]; simp)
  refine ⟨t, htpos, hρ.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr htpos.le)), ?_, ?_⟩
  · rw [trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ htpos.ne',
      Complex.ofReal_one]
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ htpos.ne', Complex.ofReal_one, one_smul]

/-- ★★★ **BCFJS, the hard half: broadcast states commute.** If one channel broadcasts two
positive semidefinite matrices, they commute. Strong induction on `rank (ρ + σ)`: normalise to
trace one, take the two boundary points `τ₁, τ₂` of the segment (BC5; they are broadcast by
linearity and `[ρ, σ]` is a positive multiple of `[τ₁, τ₂]`); with `V` the intersection of their
supports (`interProj`), either `V = 0` and BC3 gives `τ₁ τ₂ = 0 = τ₂ τ₁`, or `V ≠ 0` is cloned by
every Kraus operator (`interProj_kronecker_mulVec_eq_self`), BC4 splits each `τᵢ` into a `V`-block
and a complementary block, both pairs of blocks are broadcast with strictly smaller rank of the
sum (`rank_lt_rank_of_ker`, witnessed by the BC5 kernel vector and by a vector of `V`), so they
commute by induction, and the cross products vanish. -/
theorem Channel.Broadcasts.mul_comm_of_posSemidef {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h1 : Φ.Broadcasts ρ) (h2 : Φ.Broadcasts σ) : ρ * σ = σ * ρ := by
  classical
  suffices H : ∀ r : ℕ, ∀ ρ σ : Matrix n n ℂ, ρ.PosSemidef → σ.PosSemidef → Φ.Broadcasts ρ →
      Φ.Broadcasts σ → (ρ + σ).rank ≤ r → ρ * σ = σ * ρ from
    H _ ρ σ hρ hσ h1 h2 le_rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro ρ σ hρ hσ h1 h2 hr
  by_cases hρ0 : ρ = 0
  · subst hρ0; simp
  by_cases hσ0 : σ = 0
  · subst hσ0; simp
  -- normalise to trace one
  obtain ⟨a, ha, hρ', hρ'1, hρeq⟩ := hρ.exists_smul_trace_one hρ0
  obtain ⟨b, hb, hσ', hσ'1, hσeq⟩ := hσ.exists_smul_trace_one hσ0
  set ρ' := ((a⁻¹ : ℝ) : ℂ) • ρ with hρ'def
  set σ' := ((b⁻¹ : ℝ) : ℂ) • σ with hσ'def
  have h1' : Φ.Broadcasts ρ' := h1.smul _
  have h2' : Φ.Broadcasts σ' := h2.smul _
  suffices hcomm : ρ' * σ' = σ' * ρ' by
    have e1 : ρ * σ = ((a : ℂ) * (b : ℂ)) • (ρ' * σ') := by
      rw [hρeq, hσeq, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have e2 : σ * ρ = ((a : ℂ) * (b : ℂ)) • (σ' * ρ') := by
      rw [hρeq, hσeq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
    rw [e1, e2, hcomm]
  by_cases heq : ρ' = σ'
  · rw [heq]
  -- the kernels of `ρ + σ` and `ρ' + σ'` agree
  have hker : ∀ x, (ρ + σ) *ᵥ x = 0 ↔ (ρ' + σ') *ᵥ x = 0 := by
    intro x
    rw [hρ.add_mulVec_eq_zero_iff hσ, hρ'.add_mulVec_eq_zero_iff hσ',
      hρ'def, hσ'def, smul_mulVec_eq_zero_iff (by simp [ha.ne']),
      smul_mulVec_eq_zero_iff (by simp [hb.ne'])]
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact Matrix.ext fun i _ => (hempty.false i).elim
  -- the two boundary points of the segment
  obtain ⟨l₁, hl₁, hτ₁, x₁, hτ₁x, hx₁⟩ := exists_boundary_point hρ' hσ' hρ'1 hσ'1 heq
  obtain ⟨l₂, hl₂, hτ₂, x₂, hτ₂x, hx₂⟩ := exists_boundary_point hσ' hρ' hσ'1 hρ'1 (Ne.symm heq)
  set τ₁ := σ' + (l₁ : ℂ) • (ρ' - σ') with hτ₁def
  set τ₂ := ρ' + (l₂ : ℂ) • (σ' - ρ') with hτ₂def
  have hb₁ : Φ.Broadcasts τ₁ := h2'.add ((h1'.sub h2').smul _)
  have hb₂ : Φ.Broadcasts τ₂ := h1'.add ((h2'.sub h1').smul _)
  -- `[τ₁, τ₂] = (l₁ + l₂ − 1) [ρ', σ']`
  have hcommrel : τ₁ * τ₂ - τ₂ * τ₁ = ((l₁ + l₂ - 1 : ℝ) : ℂ) • (ρ' * σ' - σ' * ρ') := by
    rw [hτ₁def, hτ₂def]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, smul_add, smul_smul]
    push_cast
    module
  have hc : ((l₁ + l₂ - 1 : ℝ) : ℂ) ≠ 0 := by
    have : (l₁ + l₂ - 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  suffices hτcomm : τ₁ * τ₂ = τ₂ * τ₁ by
    have h := hcommrel
    rw [hτcomm, sub_self] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h.symm).resolve_left hc)
  -- `ker (ρ + σ) ⊆ ker τᵢ`
  have hkerτ : ∀ x, (ρ + σ) *ᵥ x = 0 → τ₁ *ᵥ x = 0 ∧ τ₂ *ᵥ x = 0 := by
    intro x hx
    rw [hker] at hx
    obtain ⟨hρx, hσx⟩ := (hρ'.add_mulVec_eq_zero_iff hσ' x).mp hx
    constructor <;> simp [hτ₁def, hτ₂def, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
      hρx, hσx]
  -- support projectors and the intersection
  set P₁ := suppProj τ₁ with hP₁def
  set P₂ := suppProj τ₂ with hP₂def
  have hP₁ : P₁.IsHermitian := suppProj_isHermitian τ₁
  have hP₁2 : P₁ * P₁ = P₁ := suppProj_mul_self τ₁
  have hP₂ : P₂.IsHermitian := suppProj_isHermitian τ₂
  have hP₂2 : P₂ * P₂ = P₂ := suppProj_mul_self τ₂
  set PV := interProj P₁ P₂ with hPVdef
  have hPV : PV.IsHermitian := interProj_isHermitian P₁ P₂
  have hPV2 : PV * PV = PV := interProj_mul_self P₁ P₂
  obtain ⟨hP₁PV, hP₂PV⟩ := mul_interProj hP₁ hP₁2 hP₂ hP₂2
  have hPVP₁ : PV * P₁ = PV := by
    have := congrArg conjTranspose hP₁PV
    rwa [conjTranspose_mul, hPV.eq, hP₁.eq] at this
  have hPVP₂ : PV * P₂ = PV := by
    have := congrArg conjTranspose hP₂PV
    rwa [conjTranspose_mul, hPV.eq, hP₂.eq] at this
  -- `V` is cloned by every Kraus operator
  have hclone : ∀ i, (PV ⊗ₖ PV) * (Φ.kraus i * PV) = Φ.kraus i * PV := by
    intro i
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    set v := PV *ᵥ x with hv
    have hPVv : PV *ᵥ v = v := by rw [hv, Matrix.mulVec_mulVec, hPV2]
    obtain ⟨hP₁v, hP₂v⟩ := (interProj_mulVec_eq_self_iff hP₁ hP₁2 hP₂ hP₂2 v).mp hPVv
    obtain ⟨y₁, hy₁⟩ := (suppProj_mulVec_eq_self_iff τ₁ v).mp hP₁v
    obtain ⟨y₂, hy₂⟩ := (suppProj_mulVec_eq_self_iff τ₂ v).mp hP₂v
    have hc1 : (P₁ ⊗ₖ P₁) *ᵥ (Φ.kraus i *ᵥ v) = Φ.kraus i *ᵥ v := by
      have := congrArg (fun N => N *ᵥ y₁)
        (hb₁.kronecker_mul_kraus_mul hτ₁ hP₁ hP₁2 (suppProj_mul τ₁) i)
      simpa only [← Matrix.mulVec_mulVec, hy₁] using this
    have hc2 : (P₂ ⊗ₖ P₂) *ᵥ (Φ.kraus i *ᵥ v) = Φ.kraus i *ᵥ v := by
      have := congrArg (fun N => N *ᵥ y₂)
        (hb₂.kronecker_mul_kraus_mul hτ₂ hP₂ hP₂2 (suppProj_mul τ₂) i)
      simpa only [← Matrix.mulVec_mulVec, hy₂] using this
    exact interProj_kronecker_mulVec_eq_self hP₁ hP₁2 hP₂ hP₂2 hc1 hc2
  by_cases hV : PV = 0
  · -- `V = 0`: the supports are disjoint (BC3)
    have hdisj : ∀ x, (∃ y, τ₁ *ᵥ y = x) → (∃ z, τ₂ *ᵥ z = x) → x = 0 := by
      intro x hx1 hx2
      have h1x := (suppProj_mulVec_eq_self_iff τ₁ x).mpr hx1
      have h2x := (suppProj_mulVec_eq_self_iff τ₂ x).mpr hx2
      have := (interProj_mulVec_eq_self_iff hP₁ hP₁2 hP₂ hP₂2 x).mpr ⟨h1x, h2x⟩
      rw [← hPVdef, hV, Matrix.zero_mulVec] at this
      exact this.symm
    have e1 : τ₂ * τ₁ = 0 :=
      Channel.Broadcasts.mul_eq_zero_of_range_disjoint hτ₁ hτ₂ hb₁ hb₂ hdisj
    have e2 : τ₁ * τ₂ = 0 :=
      Channel.Broadcasts.mul_eq_zero_of_range_disjoint hτ₂ hτ₁ hb₂ hb₁ fun x a b => hdisj x b a
    rw [e1, e2]
  · -- `V ≠ 0`: split both boundary states along `V` (BC4) and use the induction hypothesis
    obtain ⟨v, hv0, hPVv⟩ : ∃ v, v ≠ 0 ∧ PV *ᵥ v = v := by
      by_contra hcon
      push Not at hcon
      apply hV
      rw [Matrix.ext_iff_mulVec]
      intro x
      rw [Matrix.zero_mulVec]
      by_contra h
      exact hcon (PV *ᵥ x) h (by rw [Matrix.mulVec_mulVec, hPV2])
    obtain ⟨hcross₁, hbV₁, hbW₁⟩ := hb₁.block_split hτ₁ hPV hPV2 hP₁PV hclone
    obtain ⟨hcross₂, hbV₂, hbW₂⟩ := hb₂.block_split hτ₂ hPV hPV2 hP₂PV hclone
    set PW₁ := P₁ - PV with hPW₁def
    set PW₂ := P₂ - PV with hPW₂def
    have hPW₁ : PW₁.IsHermitian := hP₁.sub hPV
    have hPW₂ : PW₂.IsHermitian := hP₂.sub hPV
    -- the block decompositions of `τᵢ`
    have hdec : ∀ (τ P : Matrix n n ℂ), τ.PosSemidef → P.IsHermitian → P * τ = τ → τ * P = τ →
        P * PV = PV → PV * τ * (P - PV) = 0 → τ = PV * τ * PV + (P - PV) * τ * (P - PV) := by
      intro τ P hτ hP hPτ hτP hPPV hcross
      have hcross' : (P - PV) * τ * PV = 0 := by
        have := congrArg conjTranspose hcross
        rwa [conjTranspose_mul, conjTranspose_mul, hτ.1.eq, hPV.eq, conjTranspose_sub, hPV.eq,
          hP.eq, conjTranspose_zero, ← Matrix.mul_assoc] at this
      calc τ = (PV + (P - PV)) * τ * (PV + (P - PV)) := by rw [add_sub_cancel, hPτ, hτP]
        _ = PV * τ * PV + (P - PV) * τ * (P - PV) := by
            simp only [Matrix.add_mul, Matrix.mul_add, hcross, hcross', add_zero, zero_add]
    have hτ₁dec := hdec τ₁ P₁ hτ₁ hP₁ (suppProj_mul τ₁) (mul_suppProj_of_isHermitian hτ₁.1) hP₁PV
      hcross₁
    have hτ₂dec := hdec τ₂ P₂ hτ₂ hP₂ (suppProj_mul τ₂) (mul_suppProj_of_isHermitian hτ₂.1) hP₂PV
      hcross₂
    -- positivity of the blocks
    have hV₁ : (PV * τ₁ * PV).PosSemidef := by
      have := hτ₁.conjTranspose_mul_mul_same PV; rwa [hPV.eq] at this
    have hV₂ : (PV * τ₂ * PV).PosSemidef := by
      have := hτ₂.conjTranspose_mul_mul_same PV; rwa [hPV.eq] at this
    have hW₁ : (PW₁ * τ₁ * PW₁).PosSemidef := by
      have := hτ₁.conjTranspose_mul_mul_same PW₁; rwa [hPW₁.eq] at this
    have hW₂ : (PW₂ * τ₂ * PW₂).PosSemidef := by
      have := hτ₂.conjTranspose_mul_mul_same PW₂; rwa [hPW₂.eq] at this
    -- orthogonality of `V` and the complements
    have hPVPW₁ : PV * PW₁ = 0 := by rw [hPW₁def, Matrix.mul_sub, hPVP₁, hPV2, sub_self]
    have hPVPW₂ : PV * PW₂ = 0 := by rw [hPW₂def, Matrix.mul_sub, hPVP₂, hPV2, sub_self]
    have hPW₁PV : PW₁ * PV = 0 := by rw [hPW₁def, Matrix.sub_mul, hP₁PV, hPV2, sub_self]
    have hPW₂PV : PW₂ * PV = 0 := by rw [hPW₂def, Matrix.sub_mul, hP₂PV, hPV2, sub_self]
    -- kernel vectors of `ρ + σ` are killed by every projector in sight
    have hkerP : ∀ x, (ρ + σ) *ᵥ x = 0 →
        P₁ *ᵥ x = 0 ∧ P₂ *ᵥ x = 0 ∧ PV *ᵥ x = 0 ∧ PW₁ *ᵥ x = 0 ∧ PW₂ *ᵥ x = 0 := by
      intro x hx
      obtain ⟨h1x, h2x⟩ := hkerτ x hx
      have hP₁x : P₁ *ᵥ x = 0 := (suppProj_mulVec_eq_zero_iff hτ₁.1 x).mpr h1x
      have hP₂x : P₂ *ᵥ x = 0 := (suppProj_mulVec_eq_zero_iff hτ₂.1 x).mpr h2x
      have hPVx : PV *ᵥ x = 0 := by
        rw [← hPVP₁, ← Matrix.mulVec_mulVec, hP₁x, Matrix.mulVec_zero]
      refine ⟨hP₁x, hP₂x, hPVx, ?_, ?_⟩
      · rw [hPW₁def, Matrix.sub_mulVec, hP₁x, hPVx, sub_zero]
      · rw [hPW₂def, Matrix.sub_mulVec, hP₂x, hPVx, sub_zero]
    -- the `V`-pair has smaller rank
    have hrankV : (PV * τ₁ * PV + PV * τ₂ * PV).rank < (ρ + σ).rank := by
      refine rank_lt_rank_of_ker (fun x hx => ?_) (x := x₁) ?_ ?_
      · obtain ⟨-, -, hPVx, -, -⟩ := hkerP x hx
        simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hPVx, Matrix.mulVec_zero, add_zero]
      · have hP₁x : P₁ *ᵥ x₁ = 0 := (suppProj_mulVec_eq_zero_iff hτ₁.1 x₁).mpr hτ₁x
        have hPVx : PV *ᵥ x₁ = 0 := by
          rw [← hPVP₁, ← Matrix.mulVec_mulVec, hP₁x, Matrix.mulVec_zero]
        simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hPVx, Matrix.mulVec_zero, add_zero]
      · rw [Ne, hker]; exact hx₁
    have hcommV := ih _ (lt_of_lt_of_le hrankV hr) _ _ hV₁ hV₂ hbV₁ hbV₂ le_rfl
    -- the `W`-pair has smaller rank
    have hrankW : (PW₁ * τ₁ * PW₁ + PW₂ * τ₂ * PW₂).rank < (ρ + σ).rank := by
      refine rank_lt_rank_of_ker (fun x hx => ?_) (x := v) ?_ ?_
      · obtain ⟨-, -, -, hW₁x, hW₂x⟩ := hkerP x hx
        simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hW₁x, hW₂x, Matrix.mulVec_zero,
          add_zero]
      · have hP₁v : P₁ *ᵥ v = v := by rw [← hPVv, Matrix.mulVec_mulVec, hP₁PV]
        have hP₂v : P₂ *ᵥ v = v := by rw [← hPVv, Matrix.mulVec_mulVec, hP₂PV]
        have hW₁v : PW₁ *ᵥ v = 0 := by rw [hPW₁def, Matrix.sub_mulVec, hP₁v, hPVv, sub_self]
        have hW₂v : PW₂ *ᵥ v = 0 := by rw [hPW₂def, Matrix.sub_mulVec, hP₂v, hPVv, sub_self]
        simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hW₁v, hW₂v, Matrix.mulVec_zero,
          add_zero]
      · intro hv
        obtain ⟨hP₁v, -, -, -, -⟩ := hkerP v hv
        have hP₁v' : P₁ *ᵥ v = v := by rw [← hPVv, Matrix.mulVec_mulVec, hP₁PV]
        exact hv0 (by rw [← hP₁v', hP₁v])
    have hcommW := ih _ (lt_of_lt_of_le hrankW hr) _ _ hW₁ hW₂ hbW₁ hbW₂ le_rfl
    -- assemble: the cross products vanish
    have hc1 : PV * τ₁ * PV * (PW₂ * τ₂ * PW₂) = 0 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc PV PW₂, hPVPW₂]; simp
    have hc2 : PW₁ * τ₁ * PW₁ * (PV * τ₂ * PV) = 0 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc PW₁ PV, hPW₁PV]; simp
    have hc3 : PV * τ₂ * PV * (PW₁ * τ₁ * PW₁) = 0 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc PV PW₁, hPVPW₁]; simp
    have hc4 : PW₂ * τ₂ * PW₂ * (PV * τ₁ * PV) = 0 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc PW₂ PV, hPW₂PV]; simp
    calc τ₁ * τ₂ = (PV * τ₁ * PV + PW₁ * τ₁ * PW₁) * (PV * τ₂ * PV + PW₂ * τ₂ * PW₂) := by
          rw [← hτ₁dec, ← hτ₂dec]
      _ = PV * τ₁ * PV * (PV * τ₂ * PV) + PW₁ * τ₁ * PW₁ * (PW₂ * τ₂ * PW₂) := by
          simp only [Matrix.add_mul, Matrix.mul_add, hc1, hc2, add_zero, zero_add]
      _ = PV * τ₂ * PV * (PV * τ₁ * PV) + PW₂ * τ₂ * PW₂ * (PW₁ * τ₁ * PW₁) := by
          rw [hcommV, hcommW]
      _ = (PV * τ₂ * PV + PW₂ * τ₂ * PW₂) * (PV * τ₁ * PV + PW₁ * τ₁ * PW₁) := by
          simp only [Matrix.add_mul, Matrix.mul_add, hc3, hc4, add_zero, zero_add]
      _ = τ₂ * τ₁ := by rw [← hτ₁dec, ← hτ₂dec]

universe u in
/-- ★★★ **BCFJS (Barnum–Caves–Fuchs–Jozsa–Schumacher 1996).** Two positive semidefinite matrices
can be broadcast by a single channel if and only if they commute. -/
theorem exists_channel_broadcasts_iff_commute {n : Type u} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (∃ (κ : Type u) (_ : Fintype κ) (Φ : Channel n (n × n) κ), Φ.Broadcasts ρ ∧ Φ.Broadcasts σ)
      ↔ ρ * σ = σ * ρ := by
  constructor
  · rintro ⟨κ, _, Φ, h1, h2⟩
    exact Channel.Broadcasts.mul_comm_of_posSemidef hρ hσ h1 h2
  · intro hc
    obtain ⟨Φ, h1, h2⟩ := exists_channel_broadcasts_of_commute hρ.1 hσ.1 hc
    exact ⟨n, inferInstance, Φ, h1, h2⟩

end Main


section Family

open Module.End in
/-- **A pairwise-commuting family of Hermitian matrices has a joint orthonormal eigenbasis**
(Mathlib's `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`, restricted to the finitely many
joint eigenvalue functions and collected into a basis). -/
theorem exists_orthonormalBasis_mulVec_eq_smul_of_pairwise_commute {κ : Type*} [Fintype κ]
    {ρ : κ → Matrix n n ℂ} (hρ : ∀ k, (ρ k).IsHermitian)
    (hc : ∀ j k, ρ j * ρ k = ρ k * ρ j) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (r : κ → n → ℂ),
      ∀ k i, ρ k *ᵥ onbVec b i = r k i • onbVec b i := by
  classical
  set T : κ → (EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) :=
    fun k => Matrix.toEuclideanLin (ρ k) with hTdef
  have hT : ∀ k, (T k).IsSymmetric := fun k => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hρ k)
  have hC : Pairwise (Commute on T) := by
    intro j k _
    change T j * T k = T k * T j
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, hTdef]
    simp only
    rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, hc]
  have hsupV := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have horth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  set V : (κ → ℂ) → Submodule ℂ (EuclideanSpace ℂ n) :=
    fun α => ⨅ j, eigenspace (T j) (α j) with hV
  -- restrict to the joint eigenvalue functions
  set f : (∀ j, Module.End.Eigenvalues (T j)) → (κ → ℂ) := fun p j => (p j).val with hf
  have hfinj : Function.Injective f := by
    intro p q h
    funext j
    exact Subtype.ext (congrFun h j)
  have horth' := horth.comp hfinj
  have hsup : (⨆ p, V (f p)) = iSup V := by
    apply le_antisymm
    · exact iSup_comp_le V f
    · refine iSup_le fun α => ?_
      by_cases hall : ∀ j, Module.End.HasEigenvalue (T j) (α j)
      · exact le_iSup (fun p => V (f p)) (fun j => ⟨α j, hall j⟩)
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        have h0 : eigenspace (T j) (α j) = ⊥ := by
          by_contra hne; exact hj (Module.End.hasEigenvalue_iff.mpr hne)
        have : V α ≤ ⊥ := by
          calc V α ≤ eigenspace (T j) (α j) := iInf_le _ j
            _ = ⊥ := h0
        rw [le_bot_iff.mp this]
        exact bot_le
  have hint' : DirectSum.IsInternal (fun p => V (f p)) := by
    refine (horth'.isInternal_iff).mpr ?_
    rw [hsup, hsupV, Submodule.top_orthogonal_eq_bot]
  set b1 := hint'.collectedOrthonormalBasis horth' (fun p => stdOrthonormalBasis ℂ (V (f p)))
    with hb1
  have hcard : Fintype.card (Σ p : ∀ j, Module.End.Eigenvalues (T j),
      Fin (Module.finrank ℂ (V (f p)))) = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b1.toBasis, finrank_euclideanSpace]
  set e := Fintype.equivOfCardEq hcard with he
  refine ⟨b1.reindex e, fun k i => (((e.symm i).1 k : Module.End.Eigenvalues (T k)) : ℂ),
    fun k i => ?_⟩
  have hmem := hint'.collectedOrthonormalBasis_mem horth'
    (fun p => stdOrthonormalBasis ℂ (V (f p))) (e.symm i)
  have hk : b1 (e.symm i) ∈ eigenspace (T k) (((e.symm i).1 k : Module.End.Eigenvalues (T k)) : ℂ) :=
    (Submodule.mem_iInf _).mp hmem k
  have h1 : T k (b1 (e.symm i)) = (((e.symm i).1 k : Module.End.Eigenvalues (T k)) : ℂ) • b1 (e.symm i) :=
    mem_eigenspace_iff.mp hk
  simp only [onbVec, OrthonormalBasis.reindex_apply]
  have h2 : WithLp.ofLp (T k (b1 (e.symm i))) = ρ k *ᵥ WithLp.ofLp (b1 (e.symm i)) := rfl
  rw [← h2, h1, WithLp.ofLp_smul]

/-- ★★ **A pairwise-commuting family of Hermitian matrices can be broadcast** by one channel:
the copier in a joint eigenbasis. -/
theorem exists_channel_broadcasts_of_pairwise_commute {κ : Type*} [Fintype κ]
    {ρ : κ → Matrix n n ℂ} (hρ : ∀ k, (ρ k).IsHermitian)
    (hc : ∀ j k, ρ j * ρ k = ρ k * ρ j) :
    ∃ Φ : Channel n (n × n) n, ∀ k, Φ.Broadcasts (ρ k) := by
  obtain ⟨b, r, hr⟩ := exists_orthonormalBasis_mulVec_eq_smul_of_pairwise_commute hρ hc
  exact ⟨copierChannel b, fun k => copierChannel_broadcasts b (hr k)⟩

universe u in
/-- ★★★ **BCFJS for families.** A finite family of positive semidefinite matrices can be
broadcast by a single channel iff its members pairwise commute. -/
theorem exists_channel_broadcasts_family_iff_pairwise_commute {n : Type u} [Fintype n]
    [DecidableEq n] {κ : Type*} [Fintype κ] {ρ : κ → Matrix n n ℂ}
    (hρ : ∀ k, (ρ k).PosSemidef) :
    (∃ (ι : Type u) (_ : Fintype ι) (Φ : Channel n (n × n) ι), ∀ k, Φ.Broadcasts (ρ k))
      ↔ ∀ j k, ρ j * ρ k = ρ k * ρ j := by
  constructor
  · rintro ⟨ι, _, Φ, h⟩ j k
    exact Channel.Broadcasts.mul_comm_of_posSemidef (hρ j) (hρ k) (h j) (h k)
  · intro hc
    obtain ⟨Φ, h⟩ := exists_channel_broadcasts_of_pairwise_commute (fun k => (hρ k).1) hc
    exact ⟨n, inferInstance, Φ, h⟩

end Family

end QuantumInfo
