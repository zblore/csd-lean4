import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.RCLike.Basic

/-!
# Trace norm and trace distance (K3 foundation)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **trace norm** of a Hermitian matrix and the **trace distance** of two states, the
metric of statistical distinguishability:

  `traceNorm A = ∑ᵢ |λᵢ(A)|`   (sum of absolute eigenvalues = `Tr|A|` for Hermitian `A`),
  `traceDist ρ σ = ½ · traceNorm (ρ − σ)`.

This is the K3 metric-core tranche (K3 of `specs/qi-qec-roadmap.md`). It delivers the
**definitions** and the metric core short of the triangle inequality:

* non-negativity (`traceNorm_nonneg`, `traceDist_nonneg`);
* the **distinguishability headline** `traceDist ρ σ = 0 ↔ ρ = σ` (`traceDist_eq_zero_iff`) —
  zero trace distance iff the states are identical — via `eigenvalues_eq_zero_iff`;
* **symmetry** `traceDist ρ σ = traceDist σ ρ` (`traceDist_comm`), via the
  functional-calculus bridge `traceNorm A = Re Tr(cfc |·| A)` (`re_trace_cfc`) and
  `cfc_comp_neg` (`|−x| = |x|`);
* `traceNorm_of_posSemidef`: the trace norm of a PSD operator is its trace (so a density
  operator has trace norm `1`).

**Honest scope — deferred to a later K3 tranche.** Two results needing machinery Mathlib
lacks are *not* here:

* the **triangle inequality** (completing the metric) — needs the Schatten-1 norm structure
  (subadditivity of the singular-value sum), absent from Mathlib;
* the **CPTP data-processing inequality** `traceDist (Φρ) (Φσ) ≤ traceDist ρ σ` (channels
  cannot increase distinguishability) — needs the variational characterisation
  `D = max₀≤P≤I Tr(P(ρ−σ))`, a substantial build.

What is here is the eigenvalue-sum definition the deeper results will build on, plus the
distinguishability + symmetry core.
-/

open Matrix
open scoped ComplexOrder

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **trace norm** of a Hermitian matrix, `‖A‖₁ = ∑ᵢ |λᵢ(A)| = Tr|A|`: the sum of the
absolute values of its (real) eigenvalues. -/
noncomputable def traceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The **trace distance** `D(ρ,σ) = ½‖ρ − σ‖₁`: the metric of statistical
distinguishability. -/
noncomputable def traceDist {ρ σ : Matrix n n ℂ} (h : (ρ - σ).IsHermitian) : ℝ :=
  traceNorm h / 2

/-- The trace norm is non-negative. -/
lemma traceNorm_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) : 0 ≤ traceNorm hA :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The trace distance is non-negative. -/
lemma traceDist_nonneg {ρ σ : Matrix n n ℂ} (h : (ρ - σ).IsHermitian) : 0 ≤ traceDist h :=
  div_nonneg (traceNorm_nonneg h) (by norm_num)

/-- **The trace norm vanishes iff the matrix is zero.** From `∑ᵢ |λᵢ| = 0 ↔ all λᵢ = 0` and
`IsHermitian.eigenvalues_eq_zero_iff`. -/
lemma traceNorm_eq_zero_iff {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm hA = 0 ↔ A = 0 := by
  rw [traceNorm, Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg _]
  simp only [abs_eq_zero, Finset.mem_univ, forall_true_left]
  rw [← hA.eigenvalues_eq_zero_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- **Distinguishability headline: zero trace distance iff the states coincide.**
`traceDist ρ σ = 0 ↔ ρ = σ`. -/
lemma traceDist_eq_zero_iff {ρ σ : Matrix n n ℂ} (h : (ρ - σ).IsHermitian) :
    traceDist h = 0 ↔ ρ = σ := by
  rw [traceDist, div_eq_zero_iff]
  simp only [traceNorm_eq_zero_iff h, sub_eq_zero, OfNat.ofNat_ne_zero, or_false]

/-- The trace distance of a state to itself is zero. -/
@[simp] lemma traceDist_self {ρ : Matrix n n ℂ} (h : (ρ - ρ).IsHermitian) :
    traceDist h = 0 := by
  rw [traceDist_eq_zero_iff]

/-- **Bridge to the functional calculus:** `traceNorm A = Re Tr(cfc |·| A) = Re Tr|A|`.
The Hermitian functional calculus `cfc |·| A = U · diag(|λᵢ|) · Uᴴ`, whose trace is
`∑ᵢ |λᵢ|` by cyclicity of the trace and unitarity. This identifies the eigenvalue-sum
definition with the operator absolute value, the form on which `cfc_comp_neg` acts. -/
lemma re_trace_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq f]
  unfold Matrix.IsHermitian.cfc
  have huu : star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, huu, one_mul,
    Matrix.trace_diagonal, map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- Helper: `traceNorm` depends only on the underlying matrix (transport along `A = B`). -/
lemma traceNorm_congr {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A = B) : traceNorm hA = traceNorm hB := by subst hAB; rfl

/-- **The trace norm is invariant under negation:** `traceNorm (−A) = traceNorm A`. Via the
functional-calculus bridge and `cfc_comp_neg` (`|−x| = |x|`). -/
lemma traceNorm_neg {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm hA.neg = traceNorm hA := by
  rw [traceNorm, traceNorm, ← re_trace_cfc hA.neg (fun x => |x|),
    ← re_trace_cfc hA (fun x => |x|)]
  congr 2
  rw [← cfc_comp_neg (fun x : ℝ => |x|) A]
  simp only [abs_neg]

/-- **Symmetry of the trace distance:** `traceDist ρ σ = traceDist σ ρ`. -/
lemma traceDist_comm {ρ σ : Matrix n n ℂ} (h : (ρ - σ).IsHermitian)
    (h' : (σ - ρ).IsHermitian) : traceDist h = traceDist h' := by
  rw [traceDist, traceDist]
  congr 1
  rw [← traceNorm_neg h]
  exact traceNorm_congr h.neg h' (neg_sub ρ σ)

/-- **The trace norm of a positive-semidefinite operator is its trace.** Since a PSD operator
has non-negative eigenvalues, `∑ᵢ |λᵢ| = ∑ᵢ λᵢ = Tr A`. In particular a density operator
(PSD, unit trace) has trace norm `1`. -/
lemma traceNorm_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    traceNorm hA.1 = RCLike.re A.trace := by
  rw [traceNorm, hA.1.trace_eq_sum_eigenvalues, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [RCLike.ofReal_re, abs_of_nonneg (hA.eigenvalues_nonneg i)]

end QuantumInfo
