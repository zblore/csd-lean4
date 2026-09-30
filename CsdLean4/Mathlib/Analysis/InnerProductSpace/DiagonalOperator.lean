/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Diagonal operators on a Hilbert basis

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #93(a).

Given a Hilbert basis `e : HilbertBasis ι 𝕜 E` and a family of **real** weights `l : ι → ℝ`, the
diagonal operator multiplies the `i`-th coefficient of a vector by `l i`. Unless the weights are
bounded this takes some vectors out of the space, so it is not a `ContinuousLinearMap` but a
`LinearPMap` on the natural domain of vectors whose weighted coefficients are still square-summable
— the standard model of an unbounded self-adjoint operator, and the shape every operator with a
known eigenbasis has.

* `HilbertBasis.diagDomain e l` — the natural domain, with ★ `basis_mem_diagDomain` (every basis
  vector is in it, whatever the weights) and ★★ `dense_diagDomain`;
* `HilbertBasis.diagOp e l` — the operator, with `repr_diagOp` its coefficients and
  ★ `diagOp_apply_basis` — **each basis vector is an eigenvector with eigenvalue `l i`**;
* ★★ `diagOp_isFormalAdjoint` (symmetry — the one place reality of the weights is used) and
  ★★★ `isSelfAdjoint_diagOp` — **the operator is self-adjoint**, the content being maximality:
  a vector the adjoint is defined at is already in the domain (`repr_adjoint_diagOp`);
* `LinearPMap.IsResolventAt`, `LinearPMap.resolventSet` and `LinearPMap.spectrum` — the spectrum of
  an operator with a domain, with ★ `LinearPMap.bijective_of_isResolventAt` reading the definition
  back (`T - z` is a bijection of the domain onto `E`) and
  ★ `LinearPMap.mem_spectrum_of_apply_eq_smul` (an eigenvalue is a spectral value);
* ★★ `mem_resolventSet_diagOp` and ★★ `closure_range_subset_spectrum_diagOp`, giving
  ★★★ `spectrum_diagOp` — **the spectrum is the closure of the weight set**, so a self-adjoint
  operator with any prescribed closed spectrum exists;
* `HilbertBasis.diagCLM` — the bounded companion (bounded weights, a genuine
  `ContinuousLinearMap`), which is what the resolvent is built from, plus the `ℓ²` multiplier
  `lpMul` and ★ `Memℓp.mul_of_bddAbove` underneath it.

## Honest scope

⚠️ **`LinearPMap.spectrum` is defined here, not imported.** Mathlib's `spectrum` is defined for
elements of an algebra, which an operator with a proper domain is not, so this module gives the
resolvent-set definition: `z` is a resolvent point when `T - z` has a two-sided inverse that is a
bounded operator on all of `E`. `bijective_of_isResolventAt` is the sanity check that this says what
it should. The comparison with `_root_.spectrum` for a bounded operator on the domain `⊤` is **not**
proved here; nothing below needs it.

⚠️ No functional calculus, no spectral measure, no resolution of the identity: the spectrum is
computed as a set, and that is all. Nor is the standard theorem that a self-adjoint operator has real
spectrum proved — for these operators it is visible in `spectrum_diagOp`, which exhibits the spectrum
as the closure of a set of real scalars, but the general statement is a different theorem.

⚠️ The weights are real by hypothesis. A complex family gives a perfectly good operator by the same
definitions, and it is symmetric only when the weights are real; nothing here is stated for the
complex case.

References: the construction is the multiplication-operator model behind the spectral theorem — e.g.
Reed–Simon I, Theorem VIII.4, or Rudin, *Functional Analysis* Ch. 13 — stated here on a Hilbert basis
rather than on an `L²` space. Consumer: `specs/BACKLOG.md` #93, whose items (b) and (c) would put the
twisted Laplacian of `Mathlib/QuantumInfo/AharonovBohmCircle.lean` into this form.
-/

@[expose] public section

open scoped ComplexConjugate ENNReal NNReal LinearPMap

noncomputable section

variable {ι 𝕜 : Type*} [RCLike 𝕜]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### `ℓ²` membership at the exponent `2` -/

/-- `Memℓp` at the exponent `2`, with the natural-number power the rest of the file uses. -/
theorem memℓp_two_iff {f : ι → 𝕜} : Memℓp f 2 ↔ Summable fun i => ‖f i‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  norm_num

/-- ★ **A bounded sequence multiplies `ℓ²` into itself.** -/
theorem Memℓp.mul_of_bddAbove {w f : ι → 𝕜} {C : ℝ} (hw : ∀ i, ‖w i‖ ≤ C)
    (hf : Memℓp f 2) : Memℓp (fun i => w i * f i) 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact memℓp_two_iff.2 (summable_empty)
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hw (Classical.arbitrary ι))
  refine memℓp_two_iff.2 (Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((memℓp_two_iff.1 hf).mul_left (C ^ 2)))
  calc ‖w i * f i‖ ^ 2 = (‖w i‖ * ‖f i‖) ^ 2 := by rw [norm_mul]
    _ ≤ (C * ‖f i‖) ^ 2 := by
        have := mul_le_mul_of_nonneg_right (hw i) (norm_nonneg (f i))
        nlinarith [norm_nonneg (f i), norm_nonneg (w i), mul_nonneg (norm_nonneg (w i))
          (norm_nonneg (f i))]
    _ = C ^ 2 * ‖f i‖ ^ 2 := by ring

/-- The `ℓ²` norm of a bounded multiple. -/
theorem lp.norm_mul_le_of_bddAbove {w : ι → 𝕜} {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C)
    (f : lp (fun _ : ι => 𝕜) 2) (hwf : Memℓp (fun i => w i * f i) 2) :
    ‖(⟨fun i => w i * f i, hwf⟩ : lp (fun _ : ι => 𝕜) 2)‖ ≤ C * ‖f‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (mul_nonneg hC (norm_nonneg f)) ?_
  have hnorm : ‖f‖ ^ (2 : ℝ≥0∞).toReal = ∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal :=
    lp.norm_rpow_eq_tsum hp f
  have hsum : Summable fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal := (memℓp_gen_iff hp).1 (lp.memℓp f)
  have hle : ∀ i, ‖(⟨fun i => w i * f i, hwf⟩ : lp (fun _ : ι => 𝕜) 2) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ C ^ (2 : ℝ≥0∞).toReal * ‖f i‖ ^ (2 : ℝ≥0∞).toReal := by
    intro i
    have h1 : ‖(⟨fun i => w i * f i, hwf⟩ : lp (fun _ : ι => 𝕜) 2) i‖ = ‖w i‖ * ‖f i‖ := by
      simp [norm_mul]
    rw [h1, ← Real.mul_rpow hC (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right (hw i) (norm_nonneg (f i))) hp.le
  calc ∑' i, ‖(⟨fun i => w i * f i, hwf⟩ : lp (fun _ : ι => 𝕜) 2) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' i, C ^ (2 : ℝ≥0∞).toReal * ‖f i‖ ^ (2 : ℝ≥0∞).toReal :=
        Summable.tsum_le_tsum hle ((memℓp_gen_iff hp).1 hwf) (hsum.mul_left _)
    _ = C ^ (2 : ℝ≥0∞).toReal * ‖f‖ ^ (2 : ℝ≥0∞).toReal := by rw [tsum_mul_left, hnorm]
    _ = (C * ‖f‖) ^ (2 : ℝ≥0∞).toReal := (Real.mul_rpow hC (norm_nonneg f)).symm

/-! ### The bounded multiplication operator on `ℓ²` -/

/-- Multiplication by a bounded sequence, as a continuous linear map on `ℓ²`. -/
def lpMul (w : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    lp (fun _ : ι => 𝕜) 2 →L[𝕜] lp (fun _ : ι => 𝕜) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => w i * f i, Memℓp.mul_of_bddAbove hw (lp.memℓp f)⟩
      map_add' := by
        intro f g
        ext i
        show w i * ((f : ι → 𝕜) i + (g : ι → 𝕜) i)
          = w i * (f : ι → 𝕜) i + w i * (g : ι → 𝕜) i
        ring
      map_smul' := by
        intro c f
        ext i
        simp [mul_left_comm] }
    C (fun f => lp.norm_mul_le_of_bddAbove hC hw f _)

@[simp]
theorem lpMul_apply (w : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C)
    (f : lp (fun _ : ι => 𝕜) 2) (i : ι) : lpMul w hC hw f i = w i * f i := rfl

theorem norm_lpMul_apply_le (w : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C)
    (f : lp (fun _ : ι => 𝕜) 2) : ‖lpMul w hC hw f‖ ≤ C * ‖f‖ :=
  lp.norm_mul_le_of_bddAbove hC hw f _

/-- Transporting `ℓ²` membership along a pointwise identity. -/
theorem memℓp_two_of_eq {f g : ι → 𝕜} (h : ∀ i, f i = g i) (hf : Memℓp f 2) : Memℓp g 2 :=
  (funext h : f = g) ▸ hf

/-! ### The diagonal operator of a real weight family -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The resolvent set of a partially defined operator

Mathlib's `spectrum` is defined for elements of an algebra, which an operator with a domain is not,
so the resolvent set is spelled out here: `z` is in it when `T - z` has a genuine bounded two-sided
inverse. -/

namespace LinearPMap

/-- `S` is a bounded inverse of `T - z`: it lands in the domain of `T`, it undoes `T - z` there,
and `T - z` undoes it on all of `E`. -/
structure IsResolventAt (T : E →ₗ.[𝕜] E) (z : 𝕜) (S : E →L[𝕜] E) : Prop where
  /-- The inverse lands in the domain of `T`. -/
  maps_mem : ∀ y : E, S y ∈ T.domain
  /-- `T - z` is a left inverse of `S` on all of `E`. -/
  right_inv : ∀ y : E, T ⟨S y, maps_mem y⟩ - z • S y = y
  /-- `S` is a left inverse of `T - z` on the domain of `T`. -/
  left_inv : ∀ x : T.domain, S (T x - z • (x : E)) = (x : E)

/-- The resolvent set: the scalars at which `T` has a bounded inverse. -/
def resolventSet (T : E →ₗ.[𝕜] E) : Set 𝕜 := {z | ∃ S : E →L[𝕜] E, IsResolventAt T z S}

/-- The spectrum of a partially defined operator: the complement of its resolvent set. This agrees
with `_root_.spectrum` for a `ContinuousLinearMap` read as a `LinearPMap` on `⊤`, and is stated
separately because an operator with a proper domain is not an element of an algebra. -/
def spectrum (T : E →ₗ.[𝕜] E) : Set 𝕜 := (resolventSet T)ᶜ

theorem mem_spectrum_iff {T : E →ₗ.[𝕜] E} {z : 𝕜} :
    z ∈ LinearPMap.spectrum T ↔ ∀ S : E →L[𝕜] E, ¬IsResolventAt T z S := by
  simp only [LinearPMap.spectrum, resolventSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists]

/-- ★ **At a resolvent point `T - z` really is a bijection of the domain onto `E`.** This is the
sanity check on the definition above: `resolventSet` says what the resolvent set should say. -/
theorem bijective_of_isResolventAt {T : E →ₗ.[𝕜] E} {z : 𝕜} {S : E →L[𝕜] E}
    (h : IsResolventAt T z S) :
    Function.Bijective fun x : T.domain => T x - z • (x : E) := by
  constructor
  · intro x y hxy
    refine Subtype.ext ?_
    rw [← h.left_inv x, ← h.left_inv y]
    exact congrArg S hxy
  · intro y
    exact ⟨⟨S y, h.maps_mem y⟩, h.right_inv y⟩

/-- ★ **An eigenvalue is in the spectrum.** -/
theorem mem_spectrum_of_apply_eq_smul {T : E →ₗ.[𝕜] E} {z : 𝕜} {x : T.domain}
    (hx : (x : E) ≠ 0) (hTx : T x = z • (x : E)) : z ∈ LinearPMap.spectrum T := by
  refine mem_spectrum_iff.2 fun S hS => hx ?_
  have h := hS.left_inv x
  rw [hTx, sub_self] at h
  simpa using h.symm

end LinearPMap

namespace HilbertBasis

variable (e : HilbertBasis ι 𝕜 E) (l : ι → ℝ)

/-- The natural domain of the diagonal operator with weights `l`: the vectors whose weighted
coefficient sequence is still square-summable. -/
def diagDomain : Submodule 𝕜 E where
  carrier := {f | Memℓp (fun i => (l i : 𝕜) * e.repr f i) 2}
  add_mem' := by
    intro f g hf hg
    have hf' : Memℓp (fun i => (l i : 𝕜) * e.repr f i) 2 := hf
    have hg' : Memℓp (fun i => (l i : 𝕜) * e.repr g i) 2 := hg
    refine memℓp_two_of_eq (fun i => ?_) (hf'.add hg')
    simp only [Pi.add_apply, map_add, lp.coeFn_add]
    ring
  zero_mem' := by
    refine memℓp_two_of_eq (f := (0 : ι → 𝕜)) (fun i => ?_) zero_memℓp
    simp
  smul_mem' := by
    intro c f hf
    have hf' : Memℓp (fun i => (l i : 𝕜) * e.repr f i) 2 := hf
    refine memℓp_two_of_eq (fun i => ?_) (hf'.const_smul c)
    simp only [Pi.smul_apply, map_smul, lp.coeFn_smul, smul_eq_mul]
    ring

theorem mem_diagDomain_iff {f : E} :
    f ∈ e.diagDomain l ↔ Memℓp (fun i => (l i : 𝕜) * e.repr f i) 2 := Iff.rfl

/-- Two vectors with the same coefficients are equal. -/
theorem eq_of_repr_eq {x y : E} (h : ∀ i, e.repr x i = e.repr y i) : x = y :=
  e.repr.injective (by ext i; exact h i)

/-- ★ Every basis vector lies in the domain, whatever the weights. -/
theorem basis_mem_diagDomain (i : ι) : e i ∈ e.diagDomain l := by
  classical
  refine memℓp_two_of_eq (f := ((lp.single 2 i ((l i : 𝕜)) : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜))
    (fun j => ?_) (lp.memℓp _)
  rw [e.repr_self, lp.coeFn_single, lp.coeFn_single]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- ★★ **The domain is dense**: it contains every basis vector, and their span is dense. -/
theorem dense_diagDomain : Dense ((e.diagDomain l : Submodule 𝕜 E) : Set E) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.2 (top_le_iff.1 ?_)
  rw [← e.dense_span]
  exact Submodule.topologicalClosure_mono
    (Submodule.span_le.2 (by rintro x ⟨i, rfl⟩; exact e.basis_mem_diagDomain l i))

/-- The diagonal operator with weights `l`, as a partially defined operator on `E`. -/
def diagOp : E →ₗ.[𝕜] E where
  domain := e.diagDomain l
  toFun :=
    { toFun := fun f => e.repr.symm ⟨fun i => (l i : 𝕜) * e.repr (f : E) i, f.2⟩
      map_add' := by
        intro f g
        refine e.eq_of_repr_eq fun i => ?_
        simp only [LinearIsometryEquiv.apply_symm_apply, map_add, lp.coeFn_add, Pi.add_apply,
          Submodule.coe_add]
        ring
      map_smul' := by
        intro c f
        refine e.eq_of_repr_eq fun i => ?_
        simp only [LinearIsometryEquiv.apply_symm_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
          smul_eq_mul, SetLike.val_smul, RingHom.id_apply]
        ring }

theorem diagOp_domain : (e.diagOp l).domain = e.diagDomain l := rfl

@[simp]
theorem repr_diagOp (f : (e.diagOp l).domain) (i : ι) :
    e.repr (e.diagOp l f) i = (l i : 𝕜) * e.repr (f : E) i := by
  have h : e.diagOp l f = e.repr.symm ⟨fun i => (l i : 𝕜) * e.repr (f : E) i,
      (e.mem_diagDomain_iff l).1 f.2⟩ := rfl
  rw [h, LinearIsometryEquiv.apply_symm_apply]

/-- ★ **Every weight is an eigenvalue**, with a basis vector as its eigenvector. -/
theorem diagOp_apply_basis (i : ι) :
    e.diagOp l ⟨e i, e.basis_mem_diagDomain l i⟩ = (l i : 𝕜) • e i := by
  classical
  refine e.eq_of_repr_eq fun j => ?_
  rw [repr_diagOp, map_smul, e.repr_self, lp.coeFn_smul, lp.coeFn_single, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-! ### Symmetry and self-adjointness -/

/-- ★★ **The diagonal operator of a real family is symmetric.** The weight comes out of either
slot unchanged, which is where reality of the weights is used and the only place it is needed. -/
theorem diagOp_isFormalAdjoint : (e.diagOp l).IsFormalAdjoint (e.diagOp l) := by
  intro x y
  rw [← e.repr.inner_map_map (e.diagOp l x) (y : E),
    ← e.repr.inner_map_map (x : E) (e.diagOp l y), lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [repr_diagOp, repr_diagOp, RCLike.inner_apply', RCLike.inner_apply', map_mul,
    RCLike.conj_ofReal]
  ring

section SelfAdjoint

variable [CompleteSpace E]

/-- The adjoint has the same coefficients as the operator itself: this is the computation behind
maximality, and hence behind self-adjointness. -/
theorem repr_adjoint_diagOp (y : (e.diagOp l)†.domain) (i : ι) :
    e.repr ((e.diagOp l)† y) i = (l i : 𝕜) * e.repr (y : E) i := by
  have hT : Dense (((e.diagOp l).domain : Submodule 𝕜 E) : Set E) := e.dense_diagDomain l
  have key := LinearPMap.adjoint_isFormalAdjoint (T := e.diagOp l) hT y
    ⟨e i, e.basis_mem_diagDomain l i⟩
  have hL : ⟪((e.diagOp l)† y : E), e i⟫ = (starRingEnd 𝕜) (e.repr ((e.diagOp l)† y) i) := by
    rw [e.repr_apply_apply, inner_conj_symm]
  have hR : ⟪(y : E), e i⟫ = (starRingEnd 𝕜) (e.repr (y : E) i) := by
    rw [e.repr_apply_apply, inner_conj_symm]
  rw [hL, e.diagOp_apply_basis l i, inner_smul_right, hR] at key
  have hconj : (starRingEnd 𝕜) (e.repr ((e.diagOp l)† y) i)
      = (starRingEnd 𝕜) ((l i : 𝕜) * e.repr (y : E) i) := by
    rw [map_mul, RCLike.conj_ofReal]
    exact key
  simpa using congrArg (starRingEnd 𝕜) hconj

/-- ★★★ **The diagonal operator of a real weight family is self-adjoint.** Symmetry is the easy
half; the content is maximality — a vector the adjoint is defined at already has a square-summable
weighted coefficient sequence, so the adjoint's domain cannot be larger. -/
theorem isSelfAdjoint_diagOp : IsSelfAdjoint (e.diagOp l) := by
  have hT : Dense (((e.diagOp l).domain : Submodule 𝕜 E) : Set E) := e.dense_diagDomain l
  have hle : e.diagOp l ≤ (e.diagOp l)† := (e.diagOp_isFormalAdjoint l).le_adjoint hT
  have hdom : (e.diagOp l).domain = ((e.diagOp l)†).domain := by
    refine le_antisymm hle.1 fun y hy => ?_
    refine (e.mem_diagDomain_iff l).2
      (memℓp_two_of_eq (f := fun i => e.repr ((e.diagOp l)† ⟨y, hy⟩) i)
        (fun i => e.repr_adjoint_diagOp l ⟨y, hy⟩ i) (lp.memℓp _))
  exact LinearPMap.isSelfAdjoint_def.2 (LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

end SelfAdjoint

/-! ### The bounded diagonal operator, and the spectrum -/

/-- Multiplying the coefficients by a **bounded** family, as a continuous linear map. This is the
bounded companion of `diagOp`, and the resolvent of `diagOp` is one of these. -/
def diagCLM (w : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) : E →L[𝕜] E :=
  e.repr.symm.toLinearIsometry.toContinuousLinearMap ∘L
    ((lpMul w hC hw) ∘L e.repr.toLinearIsometry.toContinuousLinearMap)

@[simp]
theorem repr_diagCLM (w : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (y : E) (i : ι) :
    e.repr (e.diagCLM w hC hw y) i = w i * e.repr y i := by
  have h : e.diagCLM w hC hw y = e.repr.symm (lpMul w hC hw (e.repr y)) := rfl
  rw [h, LinearIsometryEquiv.apply_symm_apply, lpMul_apply]

theorem norm_diagCLM_apply_le (w : ι → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (y : E) :
    ‖e.diagCLM w hC hw y‖ ≤ C * ‖y‖ := by
  have h : e.diagCLM w hC hw y = e.repr.symm (lpMul w hC hw (e.repr y)) := rfl
  rw [h, LinearIsometryEquiv.norm_map]
  calc ‖lpMul w hC hw (e.repr y)‖ ≤ C * ‖e.repr y‖ := norm_lpMul_apply_le w hC hw _
    _ = C * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]

/-- ★★ **Off the closure of the weights the operator has a bounded inverse**, namely the diagonal
operator with the reciprocal weights. The reciprocals are bounded there — that is exactly what being
off the closure says — and `l i / (l i − z)` is bounded too, which is what puts the inverse's values
back in the domain. -/
theorem mem_resolventSet_diagOp {z : 𝕜} (hz : z ∉ closure (Set.range fun i => ((l i : 𝕜)))) :
    z ∈ LinearPMap.resolventSet (e.diagOp l) := by
  obtain ⟨r, hr, hfar⟩ : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ ‖(l i : 𝕜) - z‖ := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z hz
    refine ⟨r, hr, fun i => ?_⟩
    by_contra hlt
    refine hball (?_ : (l i : 𝕜) ∈ Metric.ball z r) (subset_closure ⟨i, rfl⟩)
    rw [Metric.mem_ball, dist_eq_norm]
    exact not_le.1 hlt
  have hne : ∀ i, (l i : 𝕜) - z ≠ 0 := by
    intro i h
    have h' := hfar i
    rw [h, norm_zero] at h'
    linarith
  have hinv_le : ∀ i, ‖((l i : 𝕜) - z)⁻¹‖ ≤ r⁻¹ := by
    intro i
    rw [norm_inv]
    have h := one_div_le_one_div_of_le hr (hfar i)
    rwa [one_div, one_div] at h
  have hu : ∀ i, ‖(l i : 𝕜) * ((l i : 𝕜) - z)⁻¹‖ ≤ 1 + ‖z‖ * r⁻¹ := by
    intro i
    have h1 : 0 < ‖(l i : 𝕜) - z‖ := lt_of_lt_of_le hr (hfar i)
    have h2 : ‖(l i : 𝕜)‖ ≤ ‖(l i : 𝕜) - z‖ + ‖z‖ := by
      calc ‖(l i : 𝕜)‖ = ‖((l i : 𝕜) - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖(l i : 𝕜) - z‖ + ‖z‖ := norm_add_le _ _
    calc ‖(l i : 𝕜) * ((l i : 𝕜) - z)⁻¹‖ = ‖(l i : 𝕜)‖ * ‖(l i : 𝕜) - z‖⁻¹ := by
          rw [norm_mul, norm_inv]
      _ ≤ (‖(l i : 𝕜) - z‖ + ‖z‖) * ‖(l i : 𝕜) - z‖⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 1 + ‖z‖ * ‖(l i : 𝕜) - z‖⁻¹ := by
          field_simp
      _ ≤ 1 + ‖z‖ * r⁻¹ := by
          have := hinv_le i
          rw [norm_inv] at this
          nlinarith [norm_nonneg z]
  have hrpos : (0 : ℝ) ≤ r⁻¹ := by positivity
  set S : E →L[𝕜] E := e.diagCLM (fun i => ((l i : 𝕜) - z)⁻¹) hrpos hinv_le with hS_def
  have hSrepr : ∀ (y : E) (i : ι), e.repr (S y) i = ((l i : 𝕜) - z)⁻¹ * e.repr y i := by
    intro y i
    rw [hS_def, repr_diagCLM]
  have hmaps : ∀ y : E, S y ∈ (e.diagOp l).domain := by
    intro y
    refine (e.mem_diagDomain_iff l).2 (memℓp_two_of_eq
      (f := fun i => ((l i : 𝕜) * ((l i : 𝕜) - z)⁻¹) * e.repr y i) (fun i => ?_)
      (Memℓp.mul_of_bddAbove hu (lp.memℓp _)))
    rw [hSrepr]
    ring
  refine ⟨S, { maps_mem := hmaps, right_inv := ?_, left_inv := ?_ }⟩
  · intro y
    refine e.eq_of_repr_eq fun i => ?_
    rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_diagOp, map_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, hSrepr]
    have h := hne i
    field_simp
  · intro x
    refine e.eq_of_repr_eq fun i => ?_
    rw [hSrepr, map_sub, lp.coeFn_sub, Pi.sub_apply, repr_diagOp, map_smul, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]
    have h := hne i
    field_simp

/-- ★★ **Every limit of weights is in the spectrum.** The basis vectors are approximate
eigenvectors there, so no bounded inverse can exist: it would have to stretch a unit vector by
more than its own norm. -/
theorem closure_range_subset_spectrum_diagOp :
    closure (Set.range fun i => ((l i : 𝕜))) ⊆ LinearPMap.spectrum (e.diagOp l) := by
  intro z hz
  refine LinearPMap.mem_spectrum_iff.2 fun S hS => ?_
  have hnorm_one : ∀ i, ‖e i‖ = 1 := fun i => e.orthonormal.1 i
  have hkey : ∀ i, (1 : ℝ) ≤ ‖(l i : 𝕜) - z‖ * ‖S‖ := by
    intro i
    have h := hS.left_inv ⟨e i, e.basis_mem_diagDomain l i⟩
    rw [e.diagOp_apply_basis l i] at h
    have hsm : ((l i : 𝕜) - z) • e i = (l i : 𝕜) • e i - z • e i := sub_smul _ _ _
    rw [← hsm] at h
    have h2 : ((l i : 𝕜) - z) • S (e i) = e i := by
      rw [← ContinuousLinearMap.map_smul]
      exact h
    calc (1 : ℝ) = ‖e i‖ := (hnorm_one i).symm
      _ = ‖((l i : 𝕜) - z) • S (e i)‖ := by rw [h2]
      _ = ‖(l i : 𝕜) - z‖ * ‖S (e i)‖ := by rw [norm_smul]
      _ ≤ ‖(l i : 𝕜) - z‖ * (‖S‖ * ‖e i‖) := by
          gcongr
          exact S.le_opNorm _
      _ = ‖(l i : 𝕜) - z‖ * ‖S‖ := by rw [hnorm_one i, mul_one]
  obtain ⟨y, ⟨i, rfl⟩, hi⟩ := Metric.mem_closure_iff.1 hz (1 / (1 + ‖S‖)) (by positivity)
  have hdist : ‖(l i : 𝕜) - z‖ < 1 / (1 + ‖S‖) := by rwa [dist_eq_norm, norm_sub_rev] at hi
  have hmul : ‖(l i : 𝕜) - z‖ * (1 + ‖S‖) < 1 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖S‖)] at hdist
    linarith
  nlinarith [hkey i, norm_nonneg ((l i : 𝕜) - z), norm_nonneg S]

/-- ★★★ **The spectrum of a diagonal operator is the closure of its weight set.** Every weight is
an eigenvalue, every limit of weights is a spectral value, and nothing else is: off the closure the
reciprocal weights assemble a bounded inverse. With `isSelfAdjoint_diagOp` this is the spectral
picture of a self-adjoint operator with a prescribed spectrum. -/
theorem spectrum_diagOp :
    LinearPMap.spectrum (e.diagOp l) = closure (Set.range fun i => ((l i : 𝕜))) := by
  refine Set.eq_of_subset_of_subset (fun z hz => ?_) (e.closure_range_subset_spectrum_diagOp l)
  by_contra hcl
  exact hz (e.mem_resolventSet_diagOp l hcl)

/-- ★ **Every weight is an eigenvalue**, hence in the spectrum. -/
theorem mem_spectrum_diagOp (i : ι) : ((l i : 𝕜)) ∈ LinearPMap.spectrum (e.diagOp l) :=
  LinearPMap.mem_spectrum_of_apply_eq_smul
    (x := ⟨e i, e.basis_mem_diagDomain l i⟩)
    (by simpa using e.orthonormal.ne_zero i) (e.diagOp_apply_basis l i)

end HilbertBasis

end

end
