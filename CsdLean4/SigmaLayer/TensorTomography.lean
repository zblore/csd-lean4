/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.TensorReconstruction
public import CsdLean4.LF2.MixedEnsembleIx
public import CsdLean4.LF2.EffectGleason
public import CsdLean4.Mathlib.QuantumInfo.JointRegister
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.KroneckerAlgHom

/-!
# SigmaLayer/TensorTomography: the generation premise IS record-level local tomography (brick 2)

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)); the composites residue of the Q11
scoping session (`specs/unitary-tpp-scoping.md` §3.1 / §7 step 3), scoped in
`specs/generation-from-records-scoping.md`.

## What this module does

`SigmaLayer/TensorReconstruction.lean` forces the tensor product from two premises on a composite
observable algebra `𝒜` with local embeddings `ιA : M_m → 𝒜`, `ιB : M_n → 𝒜`: **locality** (the images
commute) and **generation** (`Algebra.adjoin ℂ (range ιA ∪ range ιB) = ⊤`). Locality is operational.
Generation is stated in algebra vocabulary — nothing in `compositeAlgReconstruction` says what an
experimenter does to check it. This module is the **premise conversion** (the Q11 template of
`RecordLayer/StatisticsRigidity.lean`): it restates generation as a property of the composite's
*record statistics* and proves the two are the same premise.

* `localProducts ιA ιB` — the joint operators `ιA A * ιB B`;
  `span_localProducts_eq_top_iff_adjoin_eq_top` — under locality the linear span of the local products
  is a unital subalgebra (`localProductsSubalgebra`), so **generation ⟺ the local products SPAN**.
* `LocallyTomographic ιA ιB` — the state-side principle in functional form: two linear functionals
  (states included) agreeing on every local product are equal. `locallyTomographic_iff_span_eq_top`: this is
  the same as the span condition, both ways (a proper subspace is killed by a nonzero functional).
* `productRecordRate ιA ιB ρ bA bB i j` — the joint record rate of the local outcomes `(i, j)`: the
  Born rate `Tr(ρ · ιA|bA i⟩⟨bA i| · ιB|bB j⟩⟨bB j|)` of the product of the two local rank-one
  projectors. `RecordLocallyTomographic ιA ιB`: two composite densities with the same joint record
  rates, for every pair of local orthonormal bases, are equal. This is local tomography in the
  vocabulary of the record layer — joint rates of local basis measurements (the LLN limit of the
  joint counts).
* ★★ `recordLocallyTomographic_iff_adjoin_eq_top` — under locality and star-preservation of the two
  embeddings, **record-level local tomography ⟺ generation**. Hence
  ★ `composite_dim_eq_of_recordLocallyTomographic` (`k = m · n`) and
  `compositeAlgReconstructionOfRecords` (`M_m ⊗ M_n ≃ₐ 𝒜`): the tensor reconstruction consumed with
  the record-level premise in place of the algebraic one.
* Non-vacuity: the Kronecker composite (`aliceHom` / `bobHom` — `NoCommunication.aliceOp` / `bobOp`
  bundled as `Matrix.kroneckerLeftAlgHom` / `kroneckerRightAlgHom`) satisfies all the hypotheses and
  is record-locally-tomographic (`kronecker_recordLocallyTomographic`) — the record form of
  `joint_mem_span_local`.

## The two directions (what the proof actually uses)

Generation ⟹ records: `ρ = σ` is detected by trace pairings against a spanning set
(`eq_of_trace_mul_eqOn_span`); the local products span, and each local factor is spanned by rank-one
projectors onto orthonormal-basis vectors (`span_onbProjectors_eq_top`, from the Hermitian spectral
theorem `IsHermitian.eq_eigen_outer` and `ℜ + i ℑ`); the pairings against product projectors are
the record rates, real because both factors are Hermitian (`trace_mul_isHermitian_real`).

Records ⟹ generation: if the local products do NOT span, a nonzero functional kills them
(`Submodule.exists_le_ker_of_lt_top`), realised as a trace pairing `X ↦ Tr(Y X)`
(`exists_forall_eq_trace_mul`). Star-preservation makes the local products star-closed, so `Yᴴ`
kills them too, so a nonzero **Hermitian** `H` does (`exists_isHermitian_ne_zero_of_trace_mul_eq_zero`);
`Tr H = 0` since `1` is a local product. Splitting the spectrum of `H` into its positive and negative
parts gives two densities `ρ ≠ σ` with `ρ.M − σ.M = c⁻¹ • H`
(`IsHermitian.exists_densityOperatorIx_sub_eq`) whose joint record rates all agree — contradicting
record tomography. Star-preservation is used in **both** directions (the record rates are real only
because the product projectors are Hermitian).

## ⚠️ Honest scope — read before citing

* This is **constraint work on the composite's observable algebra, one level above Σ** — the
  charter's "constrain Σ from above" applied to composites: it pins the composite sector (the
  epistemic projection of `Σ_AB`) given A6 locality + the record posit, and asserts nothing about
  `Σ_AB` beyond its sector. It is NOT record-layer (MD-1) progress: no `{Ωᵢ(M)}` is context-fixed
  here, no ontic record is realised, and no ontic structure is touched.
* It does NOT derive local tomography. It converts the premise: `hgen` is now an operational
  statement about joint counts. Whether the world is locally tomographic remains a posit, a permanent
  operational boundary (⚠️ RESIDUE(R-017)). Classical probability is locally tomographic and real
  quantum theory is not; local tomography alone does not select `ℂ`, and nothing here claims it does
  (the equivalence below uses `ℜ`/`ℑ`, so it is a fact about the complex composite).
* `LocallyTomographic` is stated on *all* linear functionals, `RecordLocallyTomographic` on all
  densities. The pure-state version (agreement on product projectors at every *pure* preparation) is
  not built here; under the same hypotheses it is equivalent, via the same subalgebra structure.
* `DensityOperatorIx` is used as the corpus's existing composite state type; no reading of composite
  densities as `Ω₀`-ignorance is a theorem of this module.

## References

`specs/generation-from-records-scoping.md` (the scoping); `specs/future-work.md` (P3);
`specs/reconstruction-status.md` (A6); `SigmaLayer/TensorReconstruction.lean`
(`compositeAlgReconstruction`, `composite_dim_eq` — consumed); `SigmaLayer/TensorGeneration.lean`
(`joint_mem_span_local`, `single_eq_smul`); `LF2/BornWrapper.lean` (`outerProduct`,
`IsHermitian.eq_eigen_outer`, `outerProduct_mul_outerProduct_trace`); `LF2/MixedEnsembleIx.lean`
(`DensityOperatorIx.rankOne`, `ensemble`, `traceForm_rankOne_outerProduct`); `LF2/EffectGleason.lean`
(`trace_mul_isHermitian_real`, and `matrix_eq_zero_of_quadForm_zero` — the quadratic-form
separation, a polarisation, which this module's functional-form separation
`exists_forall_eq_trace_mul` sits beside; both are distinct from the trace-pairing separation
`Matrix.ext_iff_trace_mul_left`/`_right`, whose existence form is
`Empirical/CSD/PointerCommutation.lean` `exists_trace_mul_ne`);
`RecordLayer/StatisticsRigidity.lean` (the Q11 conversion template, and
`productRecordRate_eq_bornRateBasis` — the record rates at a pure preparation ARE the basis-measurement
Born rates of the composite register). Pins: `Tests/AxiomAudit/SigmaLayer.lean`.
-/

@[expose] public section

open Matrix
open scoped Kronecker TensorProduct ComplexStarModule Pointwise
open CSD.LF2
open CSD.Empirical.QM

namespace CSD.SigmaLayer

/-! ### Trace pairings against a spanning set -/

section TracePairing

variable {κ : Type*} [Fintype κ]

/-- If `Y` trace-annihilates a star-closed set, so does `Yᴴ`. -/
theorem trace_conjTranspose_mul_eq_zero {s : Set (Matrix κ κ ℂ)} (hs : ∀ X ∈ s, star X ∈ s)
    {Y : Matrix κ κ ℂ} (hY : ∀ X ∈ s, (Y * X).trace = 0) (X : Matrix κ κ ℂ) (hX : X ∈ s) :
    (Yᴴ * X).trace = 0 := by
  have h := hY (star X) (hs X hX)
  rw [Matrix.star_eq_conjTranspose] at h
  have key : (Yᴴ * X).trace = star ((Y * Xᴴ).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.trace_mul_comm]
  rw [key, h, star_zero]

/-- A nonzero matrix trace-annihilating a star-closed set yields a nonzero **Hermitian** matrix
trace-annihilating it: one of `ℜ Y = (Y + Yᴴ)/2`, `ℑ Y = (Y − Yᴴ)/(2i)` is nonzero, and both
annihilate. -/
theorem exists_isHermitian_ne_zero_of_trace_mul_eq_zero {s : Set (Matrix κ κ ℂ)}
    (hs : ∀ X ∈ s, star X ∈ s) {Y : Matrix κ κ ℂ} (hY0 : Y ≠ 0)
    (hY : ∀ X ∈ s, (Y * X).trace = 0) :
    ∃ H : Matrix κ κ ℂ, H.IsHermitian ∧ H ≠ 0 ∧ ∀ X ∈ s, (H * X).trace = 0 := by
  have hYH := trace_conjTranspose_mul_eq_zero hs hY
  by_cases hre : (ℜ Y : Matrix κ κ ℂ) = 0
  · refine ⟨ℑ Y, Matrix.isHermitian_iff_isSelfAdjoint.mpr (ℑ Y).2, ?_, fun X hX => ?_⟩
    · intro him
      apply hY0
      rw [← realPart_add_I_smul_imaginaryPart Y, hre, him, smul_zero, add_zero]
    · rw [imaginaryPart_apply_coe, smul_mul_assoc, smul_mul_assoc, Matrix.trace_smul,
        Matrix.trace_smul, sub_mul, Matrix.trace_sub, Matrix.star_eq_conjTranspose, hY X hX,
        hYH X hX, sub_zero, smul_zero, smul_zero]
  · refine ⟨ℜ Y, Matrix.isHermitian_iff_isSelfAdjoint.mpr (ℜ Y).2, hre, fun X hX => ?_⟩
    rw [realPart_apply_coe, smul_mul_assoc, Matrix.trace_smul, add_mul, Matrix.trace_add,
      Matrix.star_eq_conjTranspose, hY X hX, hYH X hX, add_zero, smul_zero]

variable [DecidableEq κ]

/-- Two matrices whose trace pairings agree on a spanning set are equal. -/
theorem eq_of_trace_mul_eqOn_span {s : Set (Matrix κ κ ℂ)} (hs : Submodule.span ℂ s = ⊤)
    {D E : Matrix κ κ ℂ} (h : ∀ X ∈ s, (D * X).trace = (E * X).trace) : D = E := by
  rw [Matrix.ext_iff_trace_mul_right]
  have hDE : (Matrix.traceLinearMap κ ℂ ℂ).comp (LinearMap.mulLeft ℂ D)
      = (Matrix.traceLinearMap κ ℂ ℂ).comp (LinearMap.mulLeft ℂ E) :=
    LinearMap.ext_on hs fun X hX => h X hX
  exact fun X => LinearMap.congr_fun hDE X

/-- **Every linear functional on a matrix algebra is a trace pairing** `X ↦ Tr(Y X)`. The
functional-form separation lemma: a functional is determined by its values on the matrix units
(`matrix_eq_sum_single`). -/
theorem exists_forall_eq_trace_mul (f : Matrix κ κ ℂ →ₗ[ℂ] ℂ) :
    ∃ Y : Matrix κ κ ℂ, ∀ X, f X = (Y * X).trace := by
  refine ⟨Matrix.of fun j i => f (Matrix.single i j 1), fun X => ?_⟩
  have hsingle : ∀ i j, f (Matrix.single i j (X i j)) = X i j * f (Matrix.single i j 1) :=
    fun i j => by rw [single_eq_smul, map_smul, smul_eq_mul]
  conv_lhs => rw [matrix_eq_sum_single X]
  simp only [map_sum, hsingle, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

end TracePairing

/-! ### Rank-one projectors onto orthonormal-basis vectors span -/

section OnbProjectors

variable (ι : Type*) [Fintype ι]

/-- The rank-one projectors `|b i⟩⟨b i|` onto vectors of orthonormal bases of `ℂ^ι` — the effects
whose Born rates are the basis-measurement record rates. -/
def onbProjectors : Set (Matrix ι ι ℂ) :=
  Set.range fun p : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) × ι => outerProduct (p.1 p.2)

variable [DecidableEq ι]

/-- **The orthonormal-basis projectors span the matrix algebra.** A Hermitian matrix is a
combination of its eigenvector projectors (`IsHermitian.eq_eigen_outer`), and every matrix is
`ℜ + i ℑ` of Hermitian matrices. -/
theorem span_onbProjectors_eq_top : Submodule.span ℂ (onbProjectors ι) = ⊤ := by
  rw [eq_top_iff]
  intro A _
  have hherm : ∀ H : Matrix ι ι ℂ, H.IsHermitian → H ∈ Submodule.span ℂ (onbProjectors ι) :=
    fun H hH => by
      rw [IsHermitian.eq_eigen_outer hH]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(hH.eigenvectorBasis, i), rfl⟩)
  rw [← realPart_add_I_smul_imaginaryPart A]
  exact Submodule.add_mem _ (hherm _ (Matrix.isHermitian_iff_isSelfAdjoint.mpr (ℜ A).2))
    (Submodule.smul_mem _ _ (hherm _ (Matrix.isHermitian_iff_isSelfAdjoint.mpr (ℑ A).2)))

end OnbProjectors

/-! ### Local products, and generation as a span condition -/

section LocalProducts

variable {m n : ℕ} {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]
variable (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] 𝒜) (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] 𝒜)

/-- The **local products** `ιA A * ιB B` of a composite with local embeddings `ιA`, `ιB`. -/
def localProducts : Set 𝒜 := {X | ∃ A B, X = ιA A * ιB B}

theorem one_mem_localProducts : (1 : 𝒜) ∈ localProducts ιA ιB :=
  ⟨1, 1, by rw [map_one, map_one, one_mul]⟩

theorem apply_mem_localProducts_left (A : Matrix (Fin m) (Fin m) ℂ) :
    ιA A ∈ localProducts ιA ιB :=
  ⟨A, 1, by rw [map_one, mul_one]⟩

theorem apply_mem_localProducts_right (B : Matrix (Fin n) (Fin n) ℂ) :
    ιB B ∈ localProducts ιA ιB :=
  ⟨1, B, by rw [map_one, one_mul]⟩

variable {ιA ιB}

/-- Under locality the local products are closed under multiplication:
`(ιA A · ιB B)(ιA A' · ιB B') = ιA (A A') · ιB (B B')`. -/
theorem mul_mem_localProducts (hc : ∀ A B, Commute (ιA A) (ιB B)) {X Y : 𝒜}
    (hX : X ∈ localProducts ιA ιB) (hY : Y ∈ localProducts ιA ιB) :
    X * Y ∈ localProducts ιA ιB := by
  obtain ⟨A, B, rfl⟩ := hX
  obtain ⟨A', B', rfl⟩ := hY
  exact ⟨A * A', B * B', by rw [map_mul, map_mul, (hc A' B).symm.mul_mul_mul_comm]⟩

/-- Under locality and star-preservation the local products are star-closed. -/
theorem star_mem_localProducts [StarRing 𝒜] (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B))
    {X : 𝒜} (hX : X ∈ localProducts ιA ιB) : star X ∈ localProducts ιA ιB := by
  obtain ⟨A, B, rfl⟩ := hX
  exact ⟨star A, star B, by rw [star_mul, ← hsA, ← hsB]; exact (hc _ _).eq.symm⟩

variable (ιA ιB)

/-- Under locality, the span of the local products is a unital subalgebra. -/
noncomputable def localProductsSubalgebra (hc : ∀ A B, Commute (ιA A) (ιB B)) : Subalgebra ℂ 𝒜 :=
  Submodule.toSubalgebra (Submodule.span ℂ (localProducts ιA ιB))
    (Submodule.subset_span (one_mem_localProducts ιA ιB))
    (fun X Y hX hY => by
      -- `X * Y ∈ span s * span s = span (s * s) ≤ span s`
      have h := Submodule.mul_mem_mul hX hY
      rw [Submodule.span_mul_span] at h
      exact Submodule.span_mono
        (Set.mul_subset_iff.mpr fun X hX Y hY => mul_mem_localProducts hc hX hY) h)

@[simp] theorem localProductsSubalgebra_toSubmodule (hc : ∀ A B, Commute (ιA A) (ιB B)) :
    Subalgebra.toSubmodule (localProductsSubalgebra ιA ιB hc)
      = Submodule.span ℂ (localProducts ιA ιB) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- **Generation ⟺ the local products span.** Under locality, `Algebra.adjoin ℂ (range ιA ∪ range ιB)
= ⊤` (the generation premise of `compositeAlgReconstruction`) holds iff the linear span of the local
products is everything. -/
theorem span_localProducts_eq_top_iff_adjoin_eq_top (hc : ∀ A B, Commute (ιA A) (ιB B)) :
    Submodule.span ℂ (localProducts ιA ιB) = ⊤
      ↔ Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤ := by
  constructor
  · intro h
    have hle : Submodule.span ℂ (localProducts ιA ιB)
        ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB)) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨A, B, rfl⟩
        show _ ∈ Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB)
        exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨A, rfl⟩))
          (Algebra.subset_adjoin (Or.inr ⟨B, rfl⟩)))
    rw [h] at hle
    exact Algebra.toSubmodule_eq_top.mp (top_le_iff.mp hle)
  · intro h
    have hle : Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) ≤ localProductsSubalgebra ιA ιB hc :=
      Algebra.adjoin_le (by
        rintro _ (⟨A, rfl⟩ | ⟨B, rfl⟩)
        · exact Submodule.mem_toSubalgebra.mpr
            (Submodule.subset_span (apply_mem_localProducts_left ιA ιB A))
        · exact Submodule.mem_toSubalgebra.mpr
            (Submodule.subset_span (apply_mem_localProducts_right ιA ιB B)))
    rw [h] at hle
    rw [← localProductsSubalgebra_toSubmodule ιA ιB hc, Algebra.toSubmodule_eq_top]
    exact top_le_iff.mp hle

/-! ### State-side local tomography, functional form -/

/-- **Local tomography (state side, functional form):** two linear functionals on the composite
agreeing on every local product are equal — a composite state is determined by its local-product
expectations. -/
def LocallyTomographic : Prop :=
  ∀ f g : 𝒜 →ₗ[ℂ] ℂ, (∀ A B, f (ιA A * ιB B) = g (ιA A * ιB B)) → f = g

/-- **Functional-form local tomography ⟺ the local products span.** (⇐) is `LinearMap.ext_on`;
(⇒): a proper subspace is killed by a nonzero functional, which then agrees with `0` on every local
product. -/
theorem locallyTomographic_iff_span_eq_top :
    LocallyTomographic ιA ιB ↔ Submodule.span ℂ (localProducts ιA ιB) = ⊤ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨f, hf0, hker⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    exact hf0 (h f 0 fun A B => by
      rw [LinearMap.zero_apply]
      exact LinearMap.mem_ker.mp (hker (Submodule.subset_span ⟨A, B, rfl⟩)))
  · intro h f g hfg
    exact LinearMap.ext_on h (by rintro _ ⟨A, B, rfl⟩; exact hfg A B)

/-- Generation (the premise of `compositeAlgReconstruction`) is functional-form local tomography. -/
theorem locallyTomographic_iff_adjoin_eq_top (hc : ∀ A B, Commute (ιA A) (ιB B)) :
    LocallyTomographic ιA ιB ↔ Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤ :=
  (locallyTomographic_iff_span_eq_top ιA ιB).trans
    (span_localProducts_eq_top_iff_adjoin_eq_top ιA ιB hc)

end LocalProducts

/-! ### Record-level local tomography -/

section Records

variable {m n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
variable (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix κ κ ℂ)
  (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Matrix κ κ ℂ)

/-- **The joint record rate** of the local outcomes `(i, j)`: the Born rate, at the composite
preparation `ρ`, of the product of the local rank-one projectors onto `bA i` and `bB j` — the joint
rate of the two local basis measurements (the LLN limit of their joint count). -/
noncomputable def productRecordRate (ρ : DensityOperatorIx κ)
    (bA : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (bB : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (i : Fin m) (j : Fin n) : ℝ :=
  ρ.traceForm (ιA (outerProduct (bA i)) * ιB (outerProduct (bB j)))

/-- **Record-level local tomography:** two composite preparations with the same joint record rates
for every pair of local orthonormal bases are equal. -/
def RecordLocallyTomographic : Prop :=
  ∀ ρ σ : DensityOperatorIx κ,
    (∀ bA bB i j, productRecordRate ιA ιB ρ bA bB i j = productRecordRate ιA ιB σ bA bB i j) → ρ = σ

variable {ιA ιB}

/-- Under locality and star-preservation, the image of a pair of Hermitian local operators is
Hermitian. -/
theorem isHermitian_apply_mul_apply (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B))
    {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (ιA A * ιB B).IsHermitian := by
  rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, star_mul, ← hsA, ← hsB,
    Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hA.eq, hB.eq]
  exact (hc A B).eq.symm

/-- Born rates of a Hermitian effect agree iff the (real) trace pairings agree. -/
theorem traceForm_eq_iff_of_isHermitian (ρ σ : DensityOperatorIx κ) {P : Matrix κ κ ℂ}
    (hP : P.IsHermitian) :
    ρ.traceForm P = σ.traceForm P ↔ (ρ.M * P).trace = (σ.M * P).trace := by
  have hρ := Complex.conj_eq_iff_re.mp (trace_mul_isHermitian_real ρ.isHermitian hP)
  have hσ := Complex.conj_eq_iff_re.mp (trace_mul_isHermitian_real σ.isHermitian hP)
  simp only [DensityOperatorIx.traceForm, RCLike.re_to_complex]
  constructor
  · intro h
    rw [← hρ, ← hσ, h]
  · intro h
    rw [h]

/-- Under locality, the span of the local products lies in the span of the **product projectors**
`ιA |a⟩⟨a| · ιB |b⟩⟨b|` (`a`, `b` orthonormal-basis vectors) — the effects whose Born rates are the
joint record rates. -/
theorem span_localProducts_le_span_mul :
    Submodule.span ℂ (localProducts ιA ιB)
      ≤ Submodule.span ℂ (ιA '' onbProjectors (Fin m) * ιB '' onbProjectors (Fin n)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨A, B, rfl⟩
  rw [← Submodule.span_mul_span]
  refine Submodule.mul_mem_mul ?_ ?_
  · have h : A ∈ Submodule.span ℂ (onbProjectors (Fin m)) := by
      rw [span_onbProjectors_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := ιA.toLinearMap) h
    rwa [Submodule.map_span, AlgHom.coe_toLinearMap] at this
  · have h : B ∈ Submodule.span ℂ (onbProjectors (Fin n)) := by
      rw [span_onbProjectors_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := ιB.toLinearMap) h
    rwa [Submodule.map_span, AlgHom.coe_toLinearMap] at this

/-- **Generation ⟹ record-level local tomography.** If the local products span, two densities with
equal joint record rates have equal trace pairings on the product projectors, which span. -/
theorem recordLocallyTomographic_of_span_eq_top (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B))
    (hspan : Submodule.span ℂ (localProducts ιA ιB) = ⊤) :
    RecordLocallyTomographic ιA ιB := by
  intro ρ σ hρσ
  apply DensityOperatorIx.ext
  refine eq_of_trace_mul_eqOn_span
    (top_le_iff.mp (hspan ▸ span_localProducts_le_span_mul (ιA := ιA) (ιB := ιB))) ?_
  rintro _ ⟨_, ⟨_, ⟨⟨bA, i⟩, rfl⟩, rfl⟩, _, ⟨_, ⟨⟨bB, j⟩, rfl⟩, rfl⟩, rfl⟩
  exact (traceForm_eq_iff_of_isHermitian ρ σ (isHermitian_apply_mul_apply hc hsA hsB
    (outerProduct_isHermitian _) (outerProduct_isHermitian _))).mp (hρσ bA bB i j)

/-- **A traceless nonzero Hermitian matrix is a positive multiple of a difference of two densities:**
split the spectrum into positive and negative parts, `H = c (ρ − σ)` with
`ρ = ∑ max(λᵢ,0)/c · |eᵢ⟩⟨eᵢ|`, `σ = ∑ max(−λᵢ,0)/c · |eᵢ⟩⟨eᵢ|`, `c = ∑ max(λᵢ,0) > 0`. -/
theorem IsHermitian.exists_densityOperatorIx_sub_eq {H : Matrix κ κ ℂ} (hH : H.IsHermitian)
    (hH0 : H ≠ 0) (htr : H.trace = 0) :
    ∃ (ρ σ : DensityOperatorIx κ) (c : ℝ), 0 < c ∧ ρ.M - σ.M = (c : ℂ)⁻¹ • H := by
  set c : ℝ := ∑ i, max (hH.eigenvalues i) 0 with hc_def
  have hc_nonneg : ∀ i, 0 ≤ max (hH.eigenvalues i) 0 := fun i => le_max_right _ _
  have hsum_eig : ∑ i, hH.eigenvalues i = 0 := by
    have h := hH.trace_eq_sum_eigenvalues
    rw [htr, ← RCLike.ofReal_sum] at h
    exact RCLike.ofReal_eq_zero.mp h.symm
  have hc_pos : 0 < c := by
    rcases (Finset.sum_nonneg fun i _ => hc_nonneg i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hmax : ∀ i, max (hH.eigenvalues i) 0 = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc_nonneg i).mp h.symm i (Finset.mem_univ i)
      have hle : ∀ i, hH.eigenvalues i ≤ 0 := fun i => max_eq_right_iff.mp (hmax i)
      have hzero : ∀ i, hH.eigenvalues i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hle i).mp hsum_eig i (Finset.mem_univ i)
      exact hH0 (hH.eigenvalues_eq_zero_iff.mp (funext hzero))
  have hnorm : ∀ i, ‖hH.eigenvectorBasis i‖ = 1 := fun i => hH.eigenvectorBasis.orthonormal.1 i
  have hsum_pos : ∑ i, max (hH.eigenvalues i) 0 / c = 1 := by
    rw [← Finset.sum_div, div_self hc_pos.ne']
  have hsum_neg : ∑ i, max (-hH.eigenvalues i) 0 / c = 1 := by
    have hsplit : ∀ i, max (-hH.eigenvalues i) 0 = max (hH.eigenvalues i) 0 - hH.eigenvalues i :=
      fun i => by have := max_zero_sub_max_neg_zero_eq_self (hH.eigenvalues i); linarith
    rw [← Finset.sum_div, div_eq_one_iff_eq hc_pos.ne', hc_def]
    simp only [hsplit, Finset.sum_sub_distrib, hsum_eig, sub_zero]
  refine ⟨DensityOperatorIx.ensemble _ (fun i => div_nonneg (hc_nonneg i) hc_pos.le) hsum_pos
      (fun i => DensityOperatorIx.rankOne _ (hnorm i)),
    DensityOperatorIx.ensemble _ (fun i => div_nonneg (le_max_right _ _) hc_pos.le) hsum_neg
      (fun i => DensityOperatorIx.rankOne _ (hnorm i)), c, hc_pos, ?_⟩
  simp only [DensityOperatorIx.ensemble_M, DensityOperatorIx.rankOne_M]
  rw [← Finset.sum_sub_distrib]
  conv_rhs => rw [IsHermitian.eq_eigen_outer hH, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul, smul_smul, ← Complex.ofReal_sub, ← sub_div, max_zero_sub_max_neg_zero_eq_self,
    div_eq_inv_mul, Complex.ofReal_mul, Complex.ofReal_inv]

/-- **Record-level local tomography ⟹ generation.** If the local products do not span, a nonzero
Hermitian `H` trace-annihilates them; it is traceless (`1` is a local product), so it is a multiple of
a difference of two densities whose joint record rates all agree — contradicting record tomography. -/
theorem span_eq_top_of_recordLocallyTomographic (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B))
    (h : RecordLocallyTomographic ιA ιB) : Submodule.span ℂ (localProducts ιA ιB) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨Y, hY⟩ := exists_forall_eq_trace_mul f
  have hYs : ∀ X ∈ localProducts ιA ιB, (Y * X).trace = 0 := fun X hX => by
    rw [← hY]
    exact LinearMap.mem_ker.mp (hker (Submodule.subset_span hX))
  have hY0 : Y ≠ 0 := by
    rintro rfl
    apply hf0
    ext X
    rw [hY, zero_mul, Matrix.trace_zero, LinearMap.zero_apply]
  obtain ⟨H, hH, hH0, hHs⟩ := exists_isHermitian_ne_zero_of_trace_mul_eq_zero
    (fun X hX => star_mem_localProducts hc hsA hsB hX) hY0 hYs
  have htr : H.trace = 0 := by
    have h1 := hHs 1 (one_mem_localProducts ιA ιB)
    rwa [mul_one] at h1
  obtain ⟨ρ, σ, c, hcpos, hρσ⟩ := IsHermitian.exists_densityOperatorIx_sub_eq hH hH0 htr
  have heq : ρ = σ := h ρ σ fun bA bB i j => by
    have hP : ιA (outerProduct (bA i)) * ιB (outerProduct (bB j)) ∈ localProducts ιA ιB :=
      ⟨_, _, rfl⟩
    have h0 : ((ρ.M - σ.M) * (ιA (outerProduct (bA i)) * ιB (outerProduct (bB j)))).trace = 0 := by
      rw [hρσ, smul_mul_assoc, Matrix.trace_smul, hHs _ hP, smul_zero]
    rw [sub_mul, Matrix.trace_sub, sub_eq_zero] at h0
    simp only [productRecordRate, DensityOperatorIx.traceForm, h0]
  apply hH0
  have h0 : ρ.M - σ.M = 0 := by rw [heq, sub_self]
  rw [hρσ] at h0
  exact (smul_eq_zero.mp h0).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr hcpos.ne'))

variable (ιA ιB)

/-- ★★ **Record-level local tomography ⟺ generation.** Under locality and star-preservation of the
local embeddings, the generation premise of the tensor reconstruction is exactly: *the composite's
joint record rates of local basis measurements determine its state*. -/
theorem recordLocallyTomographic_iff_adjoin_eq_top (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B)) :
    RecordLocallyTomographic ιA ιB ↔ Algebra.adjoin ℂ (Set.range ιA ∪ Set.range ιB) = ⊤ :=
  ⟨fun h => (span_localProducts_eq_top_iff_adjoin_eq_top ιA ιB hc).mp
      (span_eq_top_of_recordLocallyTomographic hc hsA hsB h),
    fun h => recordLocallyTomographic_of_span_eq_top hc hsA hsB
      ((span_localProducts_eq_top_iff_adjoin_eq_top ιA ιB hc).mpr h)⟩

/-- Record-level and functional-form local tomography coincide under the same hypotheses. -/
theorem recordLocallyTomographic_iff_locallyTomographic (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B)) :
    RecordLocallyTomographic ιA ιB ↔ LocallyTomographic ιA ιB :=
  (recordLocallyTomographic_iff_adjoin_eq_top ιA ιB hc hsA hsB).trans
    (locallyTomographic_iff_adjoin_eq_top ιA ιB hc).symm

/-- **The tensor reconstruction with the record-level premise:** `M_m ⊗ M_n ≃ₐ M_κ` from locality,
star-preservation and record-level local tomography (`compositeAlgReconstruction` consumed with
`recordLocallyTomographic_iff_adjoin_eq_top`). -/
noncomputable def compositeAlgReconstructionOfRecords [NeZero m] [NeZero n] [Nonempty κ]
    (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B))
    (h : RecordLocallyTomographic ιA ιB) :
    Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix κ κ ℂ :=
  compositeAlgReconstruction ιA ιB hc
    ((recordLocallyTomographic_iff_adjoin_eq_top ιA ιB hc hsA hsB).mp h)

end Records

/-- ★ **The dimension corollary with the record-level premise:** a composite `M_k` with commuting,
star-preserving local embeddings whose joint record rates determine its state has `k = m · n`
(`composite_dim_eq` consumed through `recordLocallyTomographic_iff_adjoin_eq_top`). -/
theorem composite_dim_eq_of_recordLocallyTomographic {m n k : ℕ} [NeZero m] [NeZero n] [NeZero k]
    (ιA : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (ιB : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (hc : ∀ A B, Commute (ιA A) (ιB B))
    (hsA : ∀ A, ιA (star A) = star (ιA A)) (hsB : ∀ B, ιB (star B) = star (ιB B))
    (h : RecordLocallyTomographic ιA ιB) : k = m * n :=
  composite_dim_eq ιA ιB hc ((recordLocallyTomographic_iff_adjoin_eq_top ιA ιB hc hsA hsB).mp h)

/-! ### Non-vacuity: the Kronecker composite -/

section Kronecker

variable (m n : ℕ)

/-- Alice's local algebra `A ↦ A ⊗ₖ 1` as an algebra hom: `NoCommunication.aliceOp` bundled
(`Matrix.kroneckerLeftAlgHom`). -/
noncomputable def aliceHom :
    Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.kroneckerLeftAlgHom ℂ (Fin m) (Fin n)

/-- Bob's local algebra `B ↦ 1 ⊗ₖ B` as an algebra hom: `NoCommunication.bobOp` bundled
(`Matrix.kroneckerRightAlgHom`). -/
noncomputable def bobHom :
    Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.kroneckerRightAlgHom ℂ (Fin m) (Fin n)

variable {m n}

@[simp] theorem aliceHom_apply (A : Matrix (Fin m) (Fin m) ℂ) :
    aliceHom m n A = NoCommunication.aliceOp A := rfl

@[simp] theorem bobHom_apply (B : Matrix (Fin n) (Fin n) ℂ) :
    bobHom m n B = NoCommunication.bobOp B := rfl

theorem aliceHom_star (A : Matrix (Fin m) (Fin m) ℂ) :
    aliceHom m n (star A) = star (aliceHom m n A) :=
  Matrix.kroneckerLeftAlgHom_star A

theorem bobHom_star (B : Matrix (Fin n) (Fin n) ℂ) :
    bobHom m n (star B) = star (bobHom m n B) :=
  Matrix.kroneckerRightAlgHom_star B

/-- Locality of the Kronecker composite (`aliceOp_bobOp_commute` in bundled form). -/
theorem commute_aliceHom_bobHom (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Commute (aliceHom m n A) (bobHom m n B) :=
  Matrix.commute_kroneckerLeftAlgHom_kroneckerRightAlgHom A B

/-- The local products of the Kronecker composite are the joint local products of
`joint_mem_span_local`. -/
theorem localProducts_aliceHom_bobHom :
    localProducts (aliceHom m n) (bobHom m n)
      = {X | ∃ U Q, X = NoCommunication.aliceOp U * NoCommunication.bobOp Q} := rfl

/-- **The Kronecker local algebras generate** (`Matrix.adjoin_range_kroneckerLeftAlgHom_union_eq_top`;
the subalgebra form of `joint_mem_span_local`). -/
theorem kronecker_adjoin_eq_top :
    Algebra.adjoin ℂ (Set.range (aliceHom m n) ∪ Set.range (bobHom m n)) = ⊤ :=
  Matrix.adjoin_range_kroneckerLeftAlgHom_union_eq_top

/-- **The Kronecker composite is record-locally-tomographic:** joint rates of local basis
measurements determine the composite state. Non-vacuity of `RecordLocallyTomographic`. -/
theorem kronecker_recordLocallyTomographic :
    RecordLocallyTomographic (aliceHom m n) (bobHom m n) :=
  (recordLocallyTomographic_iff_adjoin_eq_top _ _ commute_aliceHom_bobHom aliceHom_star
    bobHom_star).mpr kronecker_adjoin_eq_top

/-- The Kronecker composite is locally tomographic in functional form. -/
theorem kronecker_locallyTomographic : LocallyTomographic (aliceHom m n) (bobHom m n) :=
  (locallyTomographic_iff_adjoin_eq_top _ _ commute_aliceHom_bobHom).mpr kronecker_adjoin_eq_top

end Kronecker

/-! ### Product projectors are projectors onto product vectors -/

section TensorState

variable {ι₁ ι₂ : Type*}

/-- The outer product of a product vector is the Kronecker product of the outer products:
`|φ ⊗ ψ⟩⟨φ ⊗ ψ| = |φ⟩⟨φ| ⊗ₖ |ψ⟩⟨ψ|`. -/
theorem outerProduct_tensorState (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) :
    outerProduct (QuantumInfo.tensorState φ ψ) = outerProduct φ ⊗ₖ outerProduct ψ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [outerProduct, Matrix.vecMulVec_apply, Matrix.kroneckerMap_apply,
    QuantumInfo.tensorState_apply, star_mul']
  ring

end TensorState

end CSD.SigmaLayer
