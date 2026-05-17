import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# LF3 Setup: signs, detector settings, system-apparatus interfaces, two-qubit Pauli layer

**Category:** 3-Local (LF3 foundational types and concrete two-qubit Pauli / spin-projector layer).

Paper §2 / §9.4.

Defines the foundational types (Sign, DetectorSetting), the abstract
pointer-readout and system-apparatus interfaces, and the concrete two-qubit
Pauli / spin-projector layer used by `Singlet/*`. The setup-level matrix
identities (§2.8: `pauliDot_isHermitian`, `pauliDot_sq`, `spinProj_idem`,
`spinProj_isHermitian`, `spinProj_complete`) are proved below from
`DetectorSetting.sum_sq_components_eq_one`, `Sign.val_mul_self`, and 2×2
matrix arithmetic.
-/

open Matrix Kronecker

namespace CSD
namespace LF3

/-! ### Sign type -/

/-- Two-element sign type for outcome labels (paper §9.4). -/
inductive Sign | plus | minus
  deriving DecidableEq, Fintype, Repr

namespace Sign

/-- Numerical value: `.plus ↦ 1`, `.minus ↦ -1`. -/
def val : Sign → ℝ
  | .plus  => 1
  | .minus => -1

/-- Sign negation. -/
def neg : Sign → Sign
  | .plus  => .minus
  | .minus => .plus

@[simp] lemma neg_neg (s : Sign) : s.neg.neg = s := by cases s <;> rfl
@[simp] lemma val_plus : (Sign.plus).val = 1 := rfl
@[simp] lemma val_minus : (Sign.minus).val = -1 := rfl
@[simp] lemma val_neg (s : Sign) : s.neg.val = -s.val := by cases s <;> simp [val, neg]
@[simp] lemma val_mul_self (s : Sign) : s.val * s.val = 1 := by cases s <;> simp [val]
@[simp] lemma val_sq (s : Sign) : s.val ^ 2 = 1 := by cases s <;> norm_num [val]

/-- Sum over `Sign` as a two-term sum. -/
lemma sum_univ {α : Type*} [AddCommMonoid α] (f : Sign → α) :
    ∑ s : Sign, f s = f Sign.plus + f Sign.minus := by
  rw [show (Finset.univ : Finset Sign) = {Sign.plus, Sign.minus} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

end Sign

/-! ### Matrix-vector adapter (non-deprecated)

`Matrix.ofLp_toEuclideanLin_apply` (used by the LF3 bridge proofs) was
deprecated in favour of `Matrix.ofLp_toLpLin` in a recent Mathlib refresh.
Provide a local `rfl`-alias to avoid both the deprecation warning and the
type-class friction of the new lemma (which exposes the `p q : ENNReal` Lp
parameters and routes through `Matrix.toLin'`). -/

theorem Matrix.ofLp_toEuclideanLin {m n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ((Matrix.toEuclideanLin M) v).ofLp = M *ᵥ v.ofLp := rfl

/-! ### Detector settings -/

/-- Detector setting: a unit vector in ℝ³ (paper §2.5). -/
structure DetectorSetting where
  /-- The underlying real 3-vector. -/
  vec  : EuclideanSpace ℝ (Fin 3)
  /-- The vector has unit norm. -/
  unit : ‖vec‖ = 1

namespace DetectorSetting

/-- For a unit vector in ℝ³, the sum of squared components is 1. -/
lemma sum_sq_components_eq_one (a : DetectorSetting) :
    a.vec 0 ^ 2 + a.vec 1 ^ 2 + a.vec 2 ^ 2 = 1 := by
  have h2 : ‖a.vec‖ ^ 2 = 1 := by rw [a.unit]; norm_num
  rw [@EuclideanSpace.norm_eq ℝ _ (Fin 3) _ a.vec] at h2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h2
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three] at h2
  exact h2

end DetectorSetting

/-! ### Abstract pointer-readout algebra -/

/-- Binary pointer-readout algebra on a finite-dimensional pointer Hilbert
    space `K` (paper §2.7, spec §9.11). Self-adjointness is stated via the
    inner-product equation directly, avoiding the `Star` typeclass synthesis
    on `K →L[ℂ] K` (which requires the adjoint construction + completeness). -/
structure BinaryPointerProjectors (K : Type*)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] where
  /-- The two sign-indexed projectors. -/
  proj        : Sign → K →L[ℂ] K
  /-- Each projector is self-adjoint with respect to the inner product. -/
  selfAdjoint : ∀ s x y, inner ℂ (proj s x) y = inner ℂ x (proj s y)
  /-- Each projector is idempotent. -/
  idem        : ∀ s, proj s ∘L proj s = proj s
  /-- The two projectors are mutually orthogonal. -/
  orthogonal  : proj .plus ∘L proj .minus = 0
  /-- The two projectors sum to the identity. -/
  complete    : proj .plus + proj .minus = (1 : K →L[ℂ] K)

/-! ### System-apparatus container -/

/-- Finite-dimensional system-apparatus container (paper §2.7). Carrier types
    and instances are type parameters, Mathlib idiom. -/
structure SystemApparatusSetup
    (K_A K_B H_SA : Type*)
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    where
  /-- Pointer-readout algebra on the A-side pointer space. -/
  ptrA : BinaryPointerProjectors K_A
  /-- Pointer-readout algebra on the B-side pointer space. -/
  ptrB : BinaryPointerProjectors K_B

/-! ### Concrete two-qubit Pauli / spin-projector layer

`HAB := EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/

/-- Pauli operator `σ·a = a_x σ_x + a_y σ_y + a_z σ_z` as a 2×2 matrix. -/
noncomputable def pauliDot (a : DetectorSetting) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((a.vec 2 : ℝ) : ℂ),                                  ((a.vec 0 : ℝ) : ℂ) - Complex.I * ((a.vec 1 : ℝ) : ℂ);
     ((a.vec 0 : ℝ) : ℂ) + Complex.I * ((a.vec 1 : ℝ) : ℂ), -((a.vec 2 : ℝ) : ℂ)]

/-- `(σ·a) ⊗ I` on `HAB`. -/
noncomputable def sigmaDotLeft (a : DetectorSetting) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (pauliDot a) 1

/-- `I ⊗ (σ·b)` on `HAB`. -/
noncomputable def sigmaDotRight (b : DetectorSetting) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) 1 (pauliDot b)

/-- `(σ·a) ⊗ (σ·b)` on `HAB`. -/
noncomputable def sigmaDotJoint (a b : DetectorSetting) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (pauliDot a) (pauliDot b)

/-- One-qubit spin projector `Πˢ(a) = (I + s σ·a) / 2`. -/
noncomputable def spinProj (s : Sign) (a : DetectorSetting) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (s.val : ℂ) • pauliDot a)

/-- Joint two-qubit spin projector `Πˢ(a) ⊗ Πᵗ(b)`. -/
noncomputable def jointSpinProj (s t : Sign) (a b : DetectorSetting) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (spinProj s a) (spinProj t b)

/-! ### Setup theorem targets (paper §2.8)

Each proof reduces to straightforward 2×2 matrix arithmetic over Mathlib's
`Matrix` / `!![…]` API plus `DetectorSetting.sum_sq_components_eq_one` and
`Sign.val_mul_self`. -/

/-- `σ·a` is Hermitian. Cell-by-cell from the `pauliDot` definition: diagonal
    entries are real (so `star = id`), off-diagonal entries are
    `a_x ∓ i a_y` (`star = ` flip the imaginary part). -/
theorem pauliDot_isHermitian (a : DetectorSetting) : (pauliDot a).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliDot, Matrix.conjTranspose_apply, Complex.conj_ofReal,
          Complex.conj_I, sub_eq_add_neg]

/-- `(σ·a)² = I` for a unit vector `a`. Diagonal entries collapse to
    `a_0² + a_1² + a_2² = 1` via `Complex.I_sq = -1`; off-diagonal entries
    cancel pairwise. -/
theorem pauliDot_sq (a : DetectorSetting) : pauliDot a * pauliDot a = 1 := by
  have hSum : ((a.vec 0 : ℝ) : ℂ)^2 + ((a.vec 1 : ℝ) : ℂ)^2 + ((a.vec 2 : ℝ) : ℂ)^2
              = (1 : ℂ) := by
    have h := a.sum_sq_components_eq_one
    have hcast : ((a.vec 0 : ℝ) : ℂ)^2 + ((a.vec 1 : ℝ) : ℂ)^2 + ((a.vec 2 : ℝ) : ℂ)^2
                  = (((a.vec 0)^2 + (a.vec 1)^2 + (a.vec 2)^2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, h, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pauliDot]
  · -- (0, 0): a₂² + (a₀ - I a₁)(a₀ + I a₁) = 1
    linear_combination hSum - ((a.vec 1 : ℝ) : ℂ)^2 * Complex.I_sq
  · -- (0, 1): a₂(a₀ - I a₁) + (a₀ - I a₁)(-a₂) = 0
    ring
  · -- (1, 0): (a₀ + I a₁) a₂ + (-a₂)(a₀ + I a₁) = 0
    ring
  · -- (1, 1): (a₀ + I a₁)(a₀ - I a₁) + (-a₂)(-a₂) = 1
    linear_combination hSum - ((a.vec 1 : ℝ) : ℂ)^2 * Complex.I_sq

/-- The spin projector is Hermitian. `(1/2) • (1 + s • σ·a)` is real-linear
    in the Hermitian operator `pauliDot a`; both scalars `1/2` and `s.val`
    are real, so `star`-fixed. -/
theorem spinProj_isHermitian (s : Sign) (a : DetectorSetting) :
    (spinProj s a).IsHermitian := by
  show (spinProj s a).conjTranspose = spinProj s a
  unfold spinProj
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      pauliDot_isHermitian a]
  simp [Complex.conj_ofReal]

/-- The spin projector is idempotent. Expand `((1/2) • A)² = (1/4) • A²`,
    where `A² = (1 + s·σ)² = 1 + 2s·σ + s²·σ² = 2 + 2s·σ = 2A` via
    `pauliDot_sq` and `Sign.val_mul_self`. -/
theorem spinProj_idem (s : Sign) (a : DetectorSetting) :
    spinProj s a * spinProj s a = spinProj s a := by
  unfold spinProj
  have hss : ((s.val : ℝ) : ℂ) * ((s.val : ℝ) : ℂ) = (1 : ℂ) := by
    have : (s.val : ℝ) * s.val = 1 := s.val_mul_self
    exact_mod_cast this
  -- The (s·σ)*(s·σ) cross term reduces to `1` via pauliDot_sq + s² = 1.
  have hSS_pauli :
      (((s.val : ℝ) : ℂ) • pauliDot a) * (((s.val : ℝ) : ℂ) • pauliDot a)
        = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliDot_sq, hss, one_smul]
  -- A² = 2 • A where A = 1 + s•σ; then (1/2 • A)² = (1/4) • 2A = (1/2) • A.
  have hA_sq :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((s.val : ℝ) : ℂ) • pauliDot a) *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((s.val : ℝ) : ℂ) • pauliDot a)
        = (2 : ℂ) •
            ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((s.val : ℝ) : ℂ) • pauliDot a) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    rw [hSS_pauli]
    module
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA_sq, smul_smul]
  rw [show ((1/2 : ℂ) * (1/2 : ℂ) * (2 : ℂ)) = (1/2 : ℂ) from by norm_num]

/-- The two spin projectors sum to the identity. -/
theorem spinProj_complete (a : DetectorSetting) :
    spinProj .plus a + spinProj .minus a = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold spinProj
  simp only [Sign.val_plus, Sign.val_minus, Complex.ofReal_one, Complex.ofReal_neg,
             neg_smul, one_smul]
  rw [show (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + pauliDot a)
         + (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + -pauliDot a)
         = (1 / 2 + 1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) by
    rw [smul_add, smul_add, add_smul]
    rw [smul_neg]
    abel]
  norm_num

/-! ### Pointer-completeness re-exports (paper §2.8) -/

section PointerComplete

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]

/-- Pointer-completeness re-export, A side (paper §2.8). -/
theorem pointer_a_complete (S : SystemApparatusSetup K_A K_B H_SA) :
    S.ptrA.proj .plus + S.ptrA.proj .minus = (1 : K_A →L[ℂ] K_A) :=
  S.ptrA.complete

/-- Pointer-completeness re-export, B side. -/
theorem pointer_b_complete (S : SystemApparatusSetup K_A K_B H_SA) :
    S.ptrB.proj .plus + S.ptrB.proj .minus = (1 : K_B →L[ℂ] K_B) :=
  S.ptrB.complete

end PointerComplete

end LF3
end CSD
