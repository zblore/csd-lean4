import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic

/-!
# Trace norm and trace distance (K3 foundation)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **trace norm** of a Hermitian matrix and the **trace distance** of two states, the
metric of statistical distinguishability:

  `traceNorm A = ∑ᵢ |λᵢ(A)|`   (sum of absolute eigenvalues = `Tr|A|` for Hermitian `A`),
  `traceDist ρ σ = ½ · traceNorm (ρ − σ)`.

This is the first tranche (K3 of `specs/qi-qec-roadmap.md`). It delivers the **definitions**
and the cleanly-reachable core:

* non-negativity (`traceNorm_nonneg`, `traceDist_nonneg`);
* the **distinguishability headline** `traceDist ρ σ = 0 ↔ ρ = σ` (`traceDist_eq_zero_iff`) —
  zero trace distance iff the states are identical — via `eigenvalues_eq_zero_iff`;
* `traceNorm_of_posSemidef`: the trace norm of a PSD operator is its trace (so a density
  operator has trace norm `1`).

**Honest scope — deferred to a later K3 tranche.** The results needing the spectrum-multiset
or Schatten-norm machinery that Mathlib lacks are *not* here:

* **symmetry** `traceDist ρ σ = traceDist σ ρ` and the **triangle inequality** (the full
  metric) — both need that the eigenvalue multiset of `−B` is the negation of that of `B`
  (a charpoly-root argument), and for the triangle, the Schatten-1 norm structure;
* the **CPTP data-processing inequality** `traceDist (Φρ) (Φσ) ≤ traceDist ρ σ` (channels
  cannot increase distinguishability) — needs the variational characterisation
  `D = max₀≤P≤I Tr(P(ρ−σ))`, a substantial build.

What is here is the eigenvalue-sum definition the deeper results will build on, plus the
state-distinguishability core that is robustly reachable today.
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

/-- **The trace norm of a positive-semidefinite operator is its trace.** Since a PSD operator
has non-negative eigenvalues, `∑ᵢ |λᵢ| = ∑ᵢ λᵢ = Tr A`. In particular a density operator
(PSD, unit trace) has trace norm `1`. -/
lemma traceNorm_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    traceNorm hA.1 = RCLike.re A.trace := by
  rw [traceNorm, hA.1.trace_eq_sum_eigenvalues, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [RCLike.ofReal_re, abs_of_nonneg (hA.eigenvalues_nonneg i)]

end QuantumInfo
