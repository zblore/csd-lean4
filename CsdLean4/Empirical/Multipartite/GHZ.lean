import CsdLean4.LF3.Setup
import CsdLean4.Empirical.Bell
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Empirical: GHZ paradox (Mermin all-or-nothing form)

**Category:** 3-Local (currently placed under `CsdLean4/Empirical/Multipartite/`
alongside CSD-specific empirical-prediction re-exports). The content
itself is QM-generic — no CSD ontology, no `OnticSetup` / `SectorData` /
singlet machinery — and is **promotion-ready to 2-Framework** on demand.
Extraction to `CsdLean4/Framework/QM/` or upstreaming to
`Mathlib/QuantumMechanics/GHZParadox.lean` is deferred until LF4
creates the `Framework/` subtree (CONVENTIONS.md §1.Cat-2).

Mermin (1990) form of the Greenberger–Horne–Zeilinger paradox. The
three-qubit GHZ state `|GHZ⟩ = (|000⟩ + |111⟩) / √2` satisfies four
algebraic identities:

```
⟨GHZ| σ_x ⊗ σ_x ⊗ σ_x |GHZ⟩ = +1
⟨GHZ| σ_x ⊗ σ_y ⊗ σ_y |GHZ⟩ = −1
⟨GHZ| σ_y ⊗ σ_x ⊗ σ_y |GHZ⟩ = −1
⟨GHZ| σ_y ⊗ σ_y ⊗ σ_x |GHZ⟩ = −1
```

Multiplying the latter three gives `−1`. Under any local hidden-variable
(LHV) model that pre-assigns `±1` values to each wing's `σ_x` and `σ_y`
measurements, the LHV product simplifies (each value squared is `1`) to
`λ(0,x)² λ(0,y)² λ(1,x)² λ(1,y)² λ(2,x)² λ(2,y)² = +1`, contradicting QM's
`−1`.

This is the **structural** signature of QM non-locality: a single-shot
algebraic contradiction, not a statistical violation of an inequality
like CHSH. The Lean theorem `no_lhv_assignment_for_ghz` is `False`, not a
strict inequality.

## Sign convention

`|GHZ⟩ = (|000⟩ + |111⟩) / √2` with the LF3 Pauli packing
(`CsdLean4/LF3/Setup.lean`'s `pauliDot`, where `(0,0) = a_z`,
`(0,1) = a_x − i a_y`, `(1,0) = a_x + i a_y`, `(1,1) = −a_z`).
For `a = (1,0,0)` (X-axis, `chshA` in `Bell.lean`) and `a = (0,1,0)`
(Y-axis, `chshA'`), this gives the standard `σ_x = [[0,1],[1,0]]`,
`σ_y = [[0,−i],[i,0]]`. The four Mermin expectations then evaluate as
above; see the `private example` block below for the explicit
basis-vector computation that pins each sign.

## Experimental provenance

- Mermin 1990: *Phys. Rev. Lett.* **65**, 3373 ("Quantum mysteries revisited").
- Greenberger, Horne, Zeilinger 1989: original three-particle state.
- Pan, Bouwmeester, Daniell, Weinfurter, Zeilinger 2000:
  *Nature* **403**, 515 (experimental confirmation).

## Caveat on ontic grounding

These predictions verify CSD-against-QM equivalence on the projective
side. Full *ontic* grounding (Σ as a compact Kähler manifold, μL as the
Kähler volume form, the GHZ state as a Dirac concentration on a
specific projective ray) is the LF4 §8 obligation. Until then the
empirical content is conditional on the CSD ontic axioms supplying the
bridge data and the Dirac-concentration preparation.
-/

open Real Matrix
open scoped BigOperators ComplexConjugate Kronecker

namespace CSD
namespace Empirical
namespace GHZ

open CSD.LF3 CSD.Empirical.Bell

/-! ## The GHZ state and its basis components -/

/-- The three-qubit GHZ state `|GHZ⟩ = (|000⟩ + |111⟩) / √2`, with
`(0, 0, 0)` and `(1, 1, 1)` the canonical basis indices in
`Fin 2 × Fin 2 × Fin 2` matching the LF3 bipartite singlet's
`(0, 1) = |+−⟩, (1, 0) = |−+⟩` convention. -/
noncomputable def ghzState : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)
       + EuclideanSpace.single ((1, 1, 1) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ))

/-! ### Basis evaluations of `ghzState`

The state is nonzero only at `(0,0,0)` and `(1,1,1)`, each with
amplitude `1/√2`. The remaining six basis components are zero. These
are auxiliary lemmas for the expectation reducer below. -/

lemma ghz_apply_000 : ghzState (0, 0, 0) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_001 : ghzState (0, 0, 1) = 0 := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_010 : ghzState (0, 1, 0) = 0 := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_011 : ghzState (0, 1, 1) = 0 := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_100 : ghzState (1, 0, 0) = 0 := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_101 : ghzState (1, 0, 1) = 0 := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_110 : ghzState (1, 1, 0) = 0 := by
  simp [ghzState, EuclideanSpace.single]

lemma ghz_apply_111 : ghzState (1, 1, 1) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [ghzState, EuclideanSpace.single]

/-- The GHZ state is unit-normalised. Both nonzero amplitudes are
`1/√2`; sum of `|1/√2|² + |1/√2|² = 1/2 + 1/2 = 1`. -/
theorem ghz_norm : ‖ghzState‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h_norm_inv : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    show ghzState.ofLp (0, 0, 0) = ((Real.sqrt 2 : ℂ)⁻¹) from ghz_apply_000,
    show ghzState.ofLp (0, 0, 1) = (0 : ℂ) from ghz_apply_001,
    show ghzState.ofLp (0, 1, 0) = (0 : ℂ) from ghz_apply_010,
    show ghzState.ofLp (0, 1, 1) = (0 : ℂ) from ghz_apply_011,
    show ghzState.ofLp (1, 0, 0) = (0 : ℂ) from ghz_apply_100,
    show ghzState.ofLp (1, 0, 1) = (0 : ℂ) from ghz_apply_101,
    show ghzState.ofLp (1, 1, 0) = (0 : ℂ) from ghz_apply_110,
    show ghzState.ofLp (1, 1, 1) = ((Real.sqrt 2 : ℂ)⁻¹) from ghz_apply_111,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, zero_add, h_norm_inv]
  rw [show ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 from by norm_num, Real.sqrt_one]

/-! ## Tripartite Pauli operators -/

/-- The tripartite Pauli operator `σ·a ⊗ σ·b ⊗ σ·c` on the three-qubit
Hilbert space, right-associated as
`Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ`. -/
noncomputable def sigmaDotTriple (a b c : DetectorSetting) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (pauliDot a)
    (Matrix.kroneckerMap (· * ·) (pauliDot b) (pauliDot c))

/-- `(σ·a ⊗ σ·b ⊗ σ·c)² = I` on three qubits. Each `σ·a` is its own
square root of the identity (`pauliDot_sq`); the Kronecker product is
multiplicative. -/
lemma sigmaDotTriple_sq (a b c : DetectorSetting) :
    sigmaDotTriple a b c * sigmaDotTriple a b c = 1 := by
  unfold sigmaDotTriple
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauliDot_sq, pauliDot_sq, pauliDot_sq,
      Matrix.one_kronecker_one, Matrix.one_kronecker_one]

/-- The tripartite Pauli operator is Hermitian. Each `pauliDot a` is
Hermitian (`pauliDot_isHermitian`); Kronecker conjugation distributes. -/
lemma sigmaDotTriple_isHermitian (a b c : DetectorSetting) :
    (sigmaDotTriple a b c).IsHermitian := by
  unfold sigmaDotTriple Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
      (pauliDot_isHermitian a).eq, (pauliDot_isHermitian b).eq,
      (pauliDot_isHermitian c).eq]

/-! ## GHZ expectation reducer

The GHZ analogue of `LF3.expectation_formula`. For any
`(Fin 2 × Fin 2 × Fin 2)`-indexed matrix `M`, the expectation
`⟨GHZ| M |GHZ⟩` reduces to a half-sum over the four corner entries
at `(0,0,0)` and `(1,1,1)`. Of the 64 = 8 × 8 terms in the
double-sum unfolding, 60 vanish (each has a factor of zero from
one of the six off-corner basis components); the surviving 4 each
factor through `(1/√2)² = 1/2`. -/
theorem ghz_expectation_formula
    (M : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    inner ℂ ghzState (Matrix.toEuclideanLin M ghzState)
      = (1/2 : ℂ) *
          (M (0, 0, 0) (0, 0, 0) + M (0, 0, 0) (1, 1, 1)
            + M (1, 1, 1) (0, 0, 0) + M (1, 1, 1) (1, 1, 1)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin,
      dotProduct]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
             Matrix.mulVec, dotProduct, Pi.star_apply]
  simp only [show ghzState.ofLp (0, 0, 0) = ((Real.sqrt 2 : ℂ)⁻¹) from ghz_apply_000,
             show ghzState.ofLp (0, 0, 1) = (0 : ℂ) from ghz_apply_001,
             show ghzState.ofLp (0, 1, 0) = (0 : ℂ) from ghz_apply_010,
             show ghzState.ofLp (0, 1, 1) = (0 : ℂ) from ghz_apply_011,
             show ghzState.ofLp (1, 0, 0) = (0 : ℂ) from ghz_apply_100,
             show ghzState.ofLp (1, 0, 1) = (0 : ℂ) from ghz_apply_101,
             show ghzState.ofLp (1, 1, 0) = (0 : ℂ) from ghz_apply_110,
             show ghzState.ofLp (1, 1, 1) = ((Real.sqrt 2 : ℂ)⁻¹) from ghz_apply_111,
             star_zero,
             show star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) by
               rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]]
  linear_combination
    (M (0, 0, 0) (0, 0, 0) + M (0, 0, 0) (1, 1, 1)
      + M (1, 1, 1) (0, 0, 0) + M (1, 1, 1) (1, 1, 1)) * inv_sqrt_two_sq

/-! ## The four Mermin expectation theorems

`chshA = (1, 0, 0)` (X-axis) and `chshA' = (0, 1, 0)` (Y-axis) from
`Bell.lean`. `pauliDot chshA = σ_x = [[0,1],[1,0]]` and
`pauliDot chshA' = σ_y = [[0,−i],[i,0]]`. -/

/-- **GHZ ⟨XXX⟩ = +1.** Mermin 1990 identity #1. -/
theorem ghz_expectation_xxx :
    Complex.re
      (inner ℂ ghzState
        (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA chshA) ghzState)) = 1 := by
  rw [ghz_expectation_formula]
  simp only [sigmaDotTriple, Matrix.kroneckerMap_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11,
             chshA_vec_ofLp_0, chshA_vec_ofLp_1, chshA_vec_ofLp_2]
  push_cast
  ring_nf
  simp [Complex.one_re]

/-- **GHZ ⟨XYY⟩ = −1.** Mermin 1990 identity #2. -/
theorem ghz_expectation_xyy :
    Complex.re
      (inner ℂ ghzState
        (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA' chshA') ghzState)) = -1 := by
  rw [ghz_expectation_formula]
  simp only [sigmaDotTriple, Matrix.kroneckerMap_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11,
             chshA_vec_ofLp_0, chshA_vec_ofLp_1, chshA_vec_ofLp_2,
             chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, chshA'_vec_ofLp_2]
  push_cast
  ring_nf
  rw [show (Complex.I^2 : ℂ) = -1 from Complex.I_sq]
  simp [Complex.neg_re, Complex.one_re]

/-- **GHZ ⟨YXY⟩ = −1.** Mermin 1990 identity #3. -/
theorem ghz_expectation_yxy :
    Complex.re
      (inner ℂ ghzState
        (Matrix.toEuclideanLin (sigmaDotTriple chshA' chshA chshA') ghzState)) = -1 := by
  rw [ghz_expectation_formula]
  simp only [sigmaDotTriple, Matrix.kroneckerMap_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11,
             chshA_vec_ofLp_0, chshA_vec_ofLp_1, chshA_vec_ofLp_2,
             chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, chshA'_vec_ofLp_2]
  push_cast
  ring_nf
  rw [show (Complex.I^2 : ℂ) = -1 from Complex.I_sq]
  simp [Complex.neg_re, Complex.one_re]

/-- **GHZ ⟨YYX⟩ = −1.** Mermin 1990 identity #4. -/
theorem ghz_expectation_yyx :
    Complex.re
      (inner ℂ ghzState
        (Matrix.toEuclideanLin (sigmaDotTriple chshA' chshA' chshA) ghzState)) = -1 := by
  rw [ghz_expectation_formula]
  simp only [sigmaDotTriple, Matrix.kroneckerMap_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11,
             chshA_vec_ofLp_0, chshA_vec_ofLp_1, chshA_vec_ofLp_2,
             chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, chshA'_vec_ofLp_2]
  push_cast
  ring_nf
  rw [show (Complex.I^2 : ℂ) = -1 from Complex.I_sq]
  simp [Complex.neg_re, Complex.one_re]

/-! ## LHV impossibility (Mermin all-or-nothing) -/

/-- Two-element type indexing the X and Y measurement axes. -/
inductive PauliAxis
  | x : PauliAxis
  | y : PauliAxis
  deriving DecidableEq

/-- **No LHV ±1 assignment satisfies the four Mermin product
constraints simultaneously.**

Under any local hidden-variable model that pre-assigns `±1 ∈ ℤ` values
to each of the six measurement settings `(wing ∈ Fin 3) × (axis ∈ {x, y})`,
the product `λ(0,x)·λ(1,x)·λ(2,x)` must equal QM's `+1` from
`ghz_expectation_xxx`, while the three products `λ(0,x)·λ(1,y)·λ(2,y)`,
`λ(0,y)·λ(1,x)·λ(2,y)`, `λ(0,y)·λ(1,y)·λ(2,x)` must each equal `−1` from
the XYY, YXY, YYX expectations.

Multiplying all four product constraints: the LHS factors into
`λ(0,x)² · λ(0,y)² · λ(1,x)² · λ(1,y)² · λ(2,x)² · λ(2,y)²`, which is
`1` (each squared `±1` value is `1`). The RHS is `(+1)·(−1)·(−1)·(−1) = −1`.
Contradiction.

This is the **structural** (single-shot, algebraic) signature of QM
non-locality, distinct from CHSH's statistical inequality violation:
the conclusion is `False`, not a strict inequality.

**Experimental verification:** Pan, Bouwmeester, Daniell, Weinfurter,
Zeilinger 2000, *Nature* **403**, 515. -/
theorem no_lhv_assignment_for_ghz :
    ¬ ∃ (lambda : Fin 3 → PauliAxis → ℤ),
      (∀ i ax, lambda i ax = 1 ∨ lambda i ax = -1) ∧
      lambda 0 PauliAxis.x * lambda 1 PauliAxis.x * lambda 2 PauliAxis.x = 1 ∧
      lambda 0 PauliAxis.x * lambda 1 PauliAxis.y * lambda 2 PauliAxis.y = -1 ∧
      lambda 0 PauliAxis.y * lambda 1 PauliAxis.x * lambda 2 PauliAxis.y = -1 ∧
      lambda 0 PauliAxis.y * lambda 1 PauliAxis.y * lambda 2 PauliAxis.x = -1 := by
  rintro ⟨lambda, hpm, hxxx, hxyy, hyxy, hyyx⟩
  -- All six squares are 1.
  have h_sq : ∀ i ax, lambda i ax * lambda i ax = 1 := by
    intro i ax
    rcases hpm i ax with h | h <;> rw [h] <;> ring
  -- Product of all four constraints, simplified via the squares.
  have hprod :
      (lambda 0 PauliAxis.x * lambda 1 PauliAxis.x * lambda 2 PauliAxis.x) *
      (lambda 0 PauliAxis.x * lambda 1 PauliAxis.y * lambda 2 PauliAxis.y) *
      (lambda 0 PauliAxis.y * lambda 1 PauliAxis.x * lambda 2 PauliAxis.y) *
      (lambda 0 PauliAxis.y * lambda 1 PauliAxis.y * lambda 2 PauliAxis.x) =
      (lambda 0 PauliAxis.x * lambda 0 PauliAxis.x) *
      (lambda 0 PauliAxis.y * lambda 0 PauliAxis.y) *
      (lambda 1 PauliAxis.x * lambda 1 PauliAxis.x) *
      (lambda 1 PauliAxis.y * lambda 1 PauliAxis.y) *
      (lambda 2 PauliAxis.x * lambda 2 PauliAxis.x) *
      (lambda 2 PauliAxis.y * lambda 2 PauliAxis.y) := by ring
  rw [hxxx, hxyy, hyxy, hyyx] at hprod
  simp only [h_sq] at hprod
  norm_num at hprod

end GHZ
end Empirical
end CSD
