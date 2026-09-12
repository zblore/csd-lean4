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
# Broadcasting: the commuting half of BCFJS, support confinement, and the cloning core

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Row **BC** of
`specs/BACKLOG.md` (the BCFJS `iff` of `Empirical/QM/NoBroadcasting.lean`), milestones BC1–BC2.

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
  no-cloning theorem at channel level, and the rank-one case of the hard half.

## What is not here

The hard half for mixed states (broadcast ⇒ commute). The literature proves it through fidelity
monotonicity (BCFJS) or the equality case of the relative-entropy data-processing inequality
(Lindblad), neither of which is in Mathlib or in this corpus. `specs/BACKLOG.md` row BC records an
elementary route through the support confinement above (BC3–BC6: disjoint supports are orthogonal
by the overlap bound; a cloned subspace splits a broadcast state into blocks each broadcast; the
segment through two states meets the boundary of the cone at rank-deficient states; induction on
the rank of `ρ + σ`), priced there.

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

end QuantumInfo
