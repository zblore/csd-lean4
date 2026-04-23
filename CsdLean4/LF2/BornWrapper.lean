import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Order

/-!
# LF2 Born-Weight Wrapper

Spec §5. Packages the finite-dimensional probability assignment using
concrete matrix-based `Effect`/`DensityOperator` structures, an imported
`busch_effect_gleason` axiom, and (downstream phases) a proved Born quadratic
form for rank-1 outcomes on pure preparations.

This file is built incrementally; see the companion plan at
`specs/LF2-plan.md` §2.4.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ}

/-- **Effect on an N-dimensional complex Hilbert space.** A Hermitian matrix
    with `0 ≤ E` and `E ≤ I` (both expressed via `PosSemidef`). -/
structure Effect (N : ℕ) where
  /-- Underlying matrix. -/
  M           : Matrix (Fin N) (Fin N) ℂ
  /-- `E` is Hermitian. -/
  isHermitian : M.IsHermitian
  /-- `0 ≤ E`. -/
  nonneg      : M.PosSemidef
  /-- `E ≤ I`, i.e. `I - E` is PSD. -/
  le_one      : (1 - M).PosSemidef

/-- **Density operator on an N-dimensional complex Hilbert space.** A Hermitian
    PSD matrix with trace 1. -/
structure DensityOperator (N : ℕ) where
  /-- Underlying matrix. -/
  M           : Matrix (Fin N) (Fin N) ℂ
  /-- `ρ` is Hermitian. -/
  isHermitian : M.IsHermitian
  /-- `0 ≤ ρ`. -/
  nonneg      : M.PosSemidef
  /-- `Tr(ρ) = 1`. -/
  trace_one   : M.trace = 1

/-- **Trace-form pairing.** `Tr(ρ · E)` as a real number. The trace of a
    product of Hermitian matrices is real (self-adjoint), so taking the real
    part is not an approximation — it is an extraction. -/
noncomputable def traceForm (ρ : DensityOperator N) (E : Effect N) : ℝ :=
  RCLike.re ((ρ.M * E.M).trace)

namespace Effect

/-- The identity effect `I`. Represents the trivial always-true measurement
    outcome. -/
noncomputable def one : Effect N where
  M           := 1
  isHermitian := Matrix.isHermitian_one
  nonneg      := Matrix.PosSemidef.one
  le_one      := by simpa [sub_self] using (Matrix.PosSemidef.zero (n := Fin N) (R := ℂ))

/-- The zero effect. Represents the trivial always-false measurement outcome. -/
noncomputable def zero : Effect N where
  M           := 0
  isHermitian := Matrix.isHermitian_zero
  nonneg      := Matrix.PosSemidef.zero
  le_one      := by simpa [sub_zero] using (Matrix.PosSemidef.one (n := Fin N) (R := ℂ))

/-- **Conditional sum of effects.** If `E`, `F` are effects and `E + F ≤ I`,
    their sum is again an effect. Hermitian-ness and PSD of the sum are
    automatic (Hermitian matrices are closed under addition, PSD matrices
    form a convex cone); only `le_one` is a genuine precondition — hence its
    role as an explicit hypothesis. -/
noncomputable def add (E F : Effect N)
    (hLe : (1 - (E.M + F.M)).PosSemidef) : Effect N where
  M           := E.M + F.M
  isHermitian := E.isHermitian.add F.isHermitian
  nonneg      := E.nonneg.add F.nonneg
  le_one      := hLe

end Effect

/-- **Operational consistency package (spec Definition 5.1).** An assignment of
    probabilities to effects satisfying: non-negativity, boundedness by 1,
    total-one on the identity, and finite additivity when the sum remains
    below `I`. Unitary covariance (spec clause 3) is omitted from this minimal
    structure and may be added if the Busch axiom's precise statement
    requires it in a future refinement. -/
structure OperationalPackage (N : ℕ) where
  /-- Probability assignment. -/
  p          : Effect N → ℝ
  /-- `0 ≤ p(E)`. -/
  nonneg     : ∀ E, 0 ≤ p E
  /-- `p(E) ≤ 1`. -/
  le_one     : ∀ E, p E ≤ 1
  /-- `p(I) = 1`. -/
  total_one  : p Effect.one = 1
  /-- Finite additivity: if `E + F ≤ I` then `p(E + F) = p(E) + p(F)`. -/
  additivity : ∀ E F : Effect N, ∀ (hLe : (1 - (E.M + F.M)).PosSemidef),
                 p (Effect.add E F hLe) = p E + p F

/-- **Imported Busch effect-Gleason theorem (spec §5.2, §7.4).** Under the
    effect-additive operational consistency package of Definition 5.1 and
    dimension `N ≥ 2`, there is a unique density operator `ρ` such that
    `p(E) = Tr(ρ · E)` for every effect `E`.

    This is the load-bearing external input of the Born-weight wrapper and is
    not present in Mathlib. LF2 imports it axiomatically rather than
    rederiving it, per the explicit spec directive in §7.4. -/
axiom busch_effect_gleason
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E

/-- **Born-form assignment (spec §5.4 wrapper).** Thin wrapper exposing the
    Busch axiom under an `LF2`-namespaced name. -/
theorem born_form_of_package
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E :=
  busch_effect_gleason hN OP

/-! ### Rank-1 outer products

The construction `|φ⟩⟨φ|` as an N×N complex matrix, together with its basic
algebraic properties (Hermitian, PSD, trace). This is the raw matrix layer;
`rankOneEffect` / `rankOneDensity` (next phase) package it into the structure
types above. -/

/-- **Rank-1 outer product.** `|φ⟩⟨φ|` with entries `M i j = φ i * star (φ j)`. -/
noncomputable def outerProduct (φ : EuclideanSpace ℂ (Fin N)) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.vecMulVec (fun i => φ i) (fun i => star (φ i))

/-- The outer product is positive semi-definite. Immediate from the general
    fact `PosSemidef (vecMulVec a (star a))`. -/
lemma outerProduct_posSemidef (φ : EuclideanSpace ℂ (Fin N)) :
    (outerProduct φ).PosSemidef := by
  simpa [outerProduct] using
    Matrix.posSemidef_vecMulVec_self_star (R := ℂ) (fun i => φ i)

/-- The outer product is Hermitian (a consequence of being PSD). -/
lemma outerProduct_isHermitian (φ : EuclideanSpace ℂ (Fin N)) :
    (outerProduct φ).IsHermitian :=
  (outerProduct_posSemidef φ).isHermitian

/-- Trace of the outer product equals the Hilbert-space inner product
    `inner ℂ φ φ`. -/
lemma outerProduct_trace (φ : EuclideanSpace ℂ (Fin N)) :
    (outerProduct φ).trace = inner ℂ φ φ := by
  rw [outerProduct, Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct]
  rfl

/-- For a unit vector, the trace of the outer product is `1`. -/
lemma outerProduct_trace_of_unit_norm
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (outerProduct φ).trace = 1 := by
  rw [outerProduct_trace, inner_self_eq_norm_sq_to_K, hφ]
  simp

/-- Unfolding: the dot-product `φ ⬝ᵥ star φ` is the trace of the outer product.
    For a unit vector this equals `1`. -/
lemma dotProduct_self_star_of_unit_norm
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    ((fun i => φ i) : Fin N → ℂ) ⬝ᵥ (fun i => star (φ i)) = 1 := by
  have h := outerProduct_trace_of_unit_norm φ hφ
  rwa [outerProduct, Matrix.trace_vecMulVec] at h

/-- **Rank-1 projector is idempotent** for a unit vector: `P * P = P`.  This
    is the defining algebraic property of an orthogonal projection. -/
lemma outerProduct_mul_self_of_unit_norm
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    outerProduct φ * outerProduct φ = outerProduct φ := by
  rw [outerProduct, Matrix.vecMulVec_mul_vecMulVec]
  have h : ((fun i => star (φ i)) : Fin N → ℂ) ⬝ᵥ (fun i => φ i) = 1 := by
    rw [dotProduct_comm]; exact dotProduct_self_star_of_unit_norm φ hφ
  rw [h, one_smul]

/-- **`1 - P` is idempotent** when `P` is. Ring calculation: `(1-P)(1-P) =
    1 - 2P + P²` and `P² = P` gives `1 - P`. -/
lemma one_sub_outerProduct_mul_self_of_unit_norm
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (1 - outerProduct φ) * (1 - outerProduct φ) = 1 - outerProduct φ := by
  have hP := outerProduct_mul_self_of_unit_norm φ hφ
  -- Expand (1-P)(1-P) manually; matrix rings are non-commutative so `ring` won't
  -- reduce, but `sub_mul` / `mul_sub` distributivity + `hP` closes it with `abel`.
  rw [sub_mul, one_mul, mul_sub, mul_one, hP]
  abel

/-- **Rank-1 complement is PSD.** `(I - |φ⟩⟨φ|).PosSemidef` for unit `φ`.
    Proof: the matrix is Hermitian and idempotent, hence equal to its own
    product with its conjugate transpose, hence PSD. -/
lemma one_sub_outerProduct_posSemidef
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (1 - outerProduct φ).PosSemidef := by
  have hHerm : (1 - outerProduct φ).IsHermitian :=
    Matrix.isHermitian_one.sub (outerProduct_isHermitian φ)
  have hIdem := one_sub_outerProduct_mul_self_of_unit_norm φ hφ
  -- Rewrite (1 - P) = (1 - P) * (1 - P) = (1 - P) * (1 - P)ᴴ (Hermitian),
  -- and apply posSemidef_self_mul_conjTranspose.
  have key : (1 - outerProduct φ) = (1 - outerProduct φ) * (1 - outerProduct φ)ᴴ := by
    rw [hHerm.eq, hIdem]
  rw [key]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- **Rank-1 projector as an Effect.** `|φ⟩⟨φ|` for a unit vector `φ`. -/
noncomputable def rankOneEffect
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) : Effect N where
  M           := outerProduct φ
  isHermitian := outerProduct_isHermitian φ
  nonneg      := outerProduct_posSemidef φ
  le_one      := one_sub_outerProduct_posSemidef φ hφ

/-- **Rank-1 pure-state density operator.** `|ψ⟩⟨ψ|` for a unit vector `ψ`. -/
noncomputable def rankOneDensity
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) : DensityOperator N where
  M           := outerProduct ψ
  isHermitian := outerProduct_isHermitian ψ
  nonneg      := outerProduct_posSemidef ψ
  trace_one   := outerProduct_trace_of_unit_norm ψ hψ

/-- **Spec §5.4 — the Born quadratic form.** For a pure preparation `|ψ⟩` and
    a rank-1 projector outcome `|φ⟩⟨φ|` (both with unit norm), the trace-form
    probability equals `|⟨ψ|φ⟩|²`. -/
theorem born_quadratic
    (ψ φ : EuclideanSpace ℂ (Fin N))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceForm (rankOneDensity ψ hψ) (rankOneEffect φ hφ) = ‖inner ℂ ψ φ‖ ^ 2 := by
  simp only [traceForm, rankOneDensity, rankOneEffect, outerProduct]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul]
  -- The two inner dot-products are (Euclidean) inner products up to order.
  have h1 : ((fun i => star (ψ i)) : Fin N → ℂ) ⬝ᵥ (fun i => φ i) = inner ℂ ψ φ := by
    rw [dotProduct_comm]
    exact (EuclideanSpace.inner_eq_star_dotProduct ψ φ).symm
  have h2 : ((fun i => ψ i) : Fin N → ℂ) ⬝ᵥ (fun i => star (φ i)) = inner ℂ φ ψ :=
    (EuclideanSpace.inner_eq_star_dotProduct φ ψ).symm
  -- smul_eq_mul to unfold smul on ℂ.
  rw [smul_eq_mul, h1, h2]
  -- Conjugate symmetry: inner ℂ φ ψ = star (inner ℂ ψ φ)
  rw [show inner ℂ φ ψ = starRingEnd ℂ (inner ℂ ψ φ) from (inner_conj_symm φ ψ).symm]
  -- z * star z = ‖z‖^2 (in ℂ); then re strips the coercion.
  rw [RCLike.mul_conj]
  norm_cast

/-- **Composite endpoint (Busch-mediated form).** For an operational package
    whose Busch-extracted density operator is `rankOneDensity ψ` (i.e., the
    preparation is the pure state `|ψ⟩`), the probability of a rank-1 outcome
    `|φ⟩⟨φ|` is `|⟨ψ|φ⟩|²`.

    The hypothesis `hρ` — that `OP.p` already agrees with the trace form of
    `rankOneDensity ψ` on every effect — is the downstream consumption of
    `busch_effect_gleason` for the pure-preparation case. It is derivable from
    a weaker purity hypothesis via `rankOneDensity_unique_of_certainty` +
    `busch_effect_gleason`; see `pure_state_born_weights_of_certainty` below
    for the strengthened form. -/
theorem pure_state_born_weights
    {N : ℕ} (OP : OperationalPackage N)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (hρ : ∀ E : Effect N, OP.p E = traceForm (rankOneDensity ψ hψ) E)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    OP.p (rankOneEffect φ hφ) = ‖inner ℂ ψ φ‖ ^ 2 := by
  rw [hρ]
  exact born_quadratic ψ φ hψ hφ

/-- **Imported matrix fact — uniqueness of pure-state density from certainty.**

    A density operator `ρ` whose trace form pairs with `|ψ⟩⟨ψ|` to give `1`
    is necessarily `|ψ⟩⟨ψ|` itself.  Equivalently, the only density operator
    that assigns probability one to the rank-1 projector through `ψ` is
    `rankOneDensity ψ`.

    **Proof sketch** (standard, via the spectral theorem for Hermitian
    matrices — formalizing it in Mathlib requires non-trivial plumbing via
    `Matrix.IsHermitian.spectralTheorem` and PSD functional calculus, which
    is deferred to later work; axiomatised here as standard linear algebra):

    1.  The hypothesis `traceForm ρ (rankOneEffect ψ hψ) = 1` unfolds to
        `⟨ψ, ρ ψ⟩ = 1` in `ℂ`.
    2.  Using `ρ² ≤ ρ` (which holds for any density with spectrum in `[0,1]`)
        and Cauchy–Schwarz, `‖ρψ - ψ‖² = 0`, hence `ρψ = ψ`.  So `ψ` is an
        eigenvector of `ρ` with eigenvalue `1`.
    3.  From `Tr(ρ) = 1` together with `⟨ψ, ρψ⟩ = 1`, the contribution of
        `ψ^⊥` to the trace is zero.  By PSD, `ρ` vanishes on `ψ^⊥`.
    4.  Therefore `ρ = |ψ⟩⟨ψ|` as matrices; structurally `ρ = rankOneDensity ψ hψ`.

    The uniqueness is a standard consequence of the spectral theorem and is
    included in any introductory quantum-information text (e.g. Nielsen &
    Chuang, "Quantum Computation and Quantum Information"). It is imported
    here as an axiom alongside `invariant_measure_uniqueness` and
    `busch_effect_gleason`; proving it via Mathlib's spectral theorem is an
    LF3-scope task. -/
axiom rankOneDensity_unique_of_certainty
    {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ρ : DensityOperator N)
    (h_certain : traceForm ρ (rankOneEffect ψ hψ) = 1) :
    ρ = rankOneDensity ψ hψ

/-- **Strengthened composite endpoint.**  Given only a **purity hypothesis** —
    that the operational package assigns probability one to the rank-1
    effect through `ψ`, i.e. the preparation is "certain" to produce `ψ` —
    the Born quadratic form `|⟨ψ|φ⟩|²` falls out for every rank-1 outcome.

    This is the tightened version of `pure_state_born_weights` that derives
    the `hρ`-hypothesis from the weaker `h_certain`, using
    `busch_effect_gleason` to extract a density operator and
    `rankOneDensity_unique_of_certainty` to identify it as `rankOneDensity ψ`.
    The proof composes three named ingredients:
    `busch_effect_gleason`, `rankOneDensity_unique_of_certainty`, and
    `born_quadratic`. -/
theorem pure_state_born_weights_of_certainty
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (h_certain : OP.p (rankOneEffect ψ hψ) = 1)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    OP.p (rankOneEffect φ hφ) = ‖inner ℂ ψ φ‖ ^ 2 := by
  obtain ⟨ρ, hρ_spec, _hρ_unique⟩ := busch_effect_gleason hN OP
  have hρ_eq : ρ = rankOneDensity ψ hψ := by
    refine rankOneDensity_unique_of_certainty ψ hψ ρ ?_
    rw [← hρ_spec]
    exact h_certain
  rw [hρ_spec, hρ_eq]
  exact born_quadratic ψ φ hψ hφ

end LF2
end CSD
