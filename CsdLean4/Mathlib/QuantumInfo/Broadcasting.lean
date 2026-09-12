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

/-!
# Broadcasting: the commuting half of BCFJS, support confinement, and disjoint supports

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Row **BC** of
`specs/BACKLOG.md` (the BCFJS `iff` of `Empirical/QM/NoBroadcasting.lean`), milestones BC1–BC3.

A channel `Φ : ℂⁿ → ℂⁿ ⊗ ℂⁿ` **broadcasts** `ρ` when both marginals of `Φ ρ` are `ρ`
(`Channel.Broadcasts`). Barnum–Caves–Fuchs–Jozsa–Schumacher (1996): a pair of states can be
broadcast by one channel iff they commute. This file proves the constructive half in full, the
structural lemma every proof of the other half rests on, and the rank-one case of that half.

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
  `μ ≤ μ √μ`, so `μ ∈ {0, 1}`; `μ = 1` would put `u` in both ranges. BC2 is the rank-one case.

## What is not here

The hard half for mixed states (broadcast ⇒ commute). The literature proves it through fidelity
monotonicity (BCFJS) or the equality case of the relative-entropy data-processing inequality
(Lindblad), neither of which is in Mathlib or in this corpus. `specs/BACKLOG.md` row BC records an
elementary route through the support confinement above; BC3 (this file) is its first brick, and
BC4–BC6 remain: a cloned subspace splits a broadcast state into blocks each broadcast; the segment
through two states meets the boundary of the cone at rank-deficient states; induction on the rank
of `ρ + σ`.

## Source

Barnum, Caves, Fuchs, Jozsa, Schumacher, *Phys. Rev. Lett.* **76**, 2818 (1996).
-/

@[expose] public section

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

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

end QuantumInfo
