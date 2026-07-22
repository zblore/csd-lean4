/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.RCLike.Basic

/-!
# Trace norm and trace distance (K3 foundation)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **trace norm** of a Hermitian matrix and the **trace distance** of two states, the
metric of statistical distinguishability:

  `traceNorm A = ∑ᵢ |λᵢ(A)|`   (sum of absolute eigenvalues = `Tr|A|` for Hermitian `A`),
  `traceDist ρ σ = ½ · traceNorm (ρ − σ)`.

This is the K3 metric-core tranche (K3 of `specs/qi-qec-roadmap.md`). It delivers the
**definitions** and the complete metric:

* non-negativity (`traceNorm_nonneg`, `traceDist_nonneg`);
* the **distinguishability headline** `traceDist ρ σ = 0 ↔ ρ = σ` (`traceDist_eq_zero_iff`) —
  zero trace distance iff the states are identical — via `eigenvalues_eq_zero_iff`;
* **symmetry** `traceDist ρ σ = traceDist σ ρ` (`traceDist_comm`), via the
  functional-calculus bridge `traceNorm A = Re Tr(cfc |·| A)` (`re_trace_cfc`) and
  `cfc_comp_neg` (`|−x| = |x|`);
* the **triangle inequality** `traceDist ρ τ ≤ traceDist ρ σ + traceDist σ τ`
  (`traceDist_triangle`), completing the metric, reduced to trace-norm subadditivity
  `‖A+B‖₁ ≤ ‖A‖₁ + ‖B‖₁` (`traceNorm_add_le`). Since Mathlib registers no Loewner order on
  matrices and the signature `sgn`/positive projector are discontinuous, this is proved via
  the Jordan decomposition built from `Matrix.IsHermitian.cfc` (defined for *any* `f`,
  including the discontinuous `posProj`): `posPart`/`negPart`/`posProj`, the PSD-product
  trace bound `tr_psd_mul_nonneg` (`0 ≤ Re Tr(S·P)` for PSD `S,P`, via `√S = cfc √ S`), and
  the operator bound `Re Tr(A·P) ≤ Re Tr(A₊)` for `0 ≤ P ≤ I`;
* `traceNorm_of_posSemidef`: the trace norm of a PSD operator is its trace (so a density
  operator has trace norm `1`).

The `posPart`/`negPart`/`posProj` Jordan primitives and the `IsHermitian.cfc` algebra layer
are exposed as named `QuantumInfo` declarations: they recur in the next K3 tranche.

The **CPTP data-processing inequality** `traceDist (Φρ) (Φσ) ≤ traceDist ρ σ` (channels cannot
increase distinguishability) builds on this file's `posPart`/`posProj` machinery and the key
bound `re_trace_mul_le_re_trace_posPart` (the variational half `Re Tr((ρ−σ)·P) ≤ Re Tr((ρ−σ)₊)`,
achieved at `P = posProj (ρ−σ)`); it is proved in `DataProcessing.lean` (`channel_traceDist_le`,
done 2026-06-09) via the channel adjoint. So K3 (metric + data-processing) is complete.
-/

@[expose] public section

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

/-- Helper: `traceDist` depends only on the underlying difference matrix (transport along the
equality `ρ − σ = ρ' − σ'`). -/
lemma traceDist_congr {ρ σ ρ' σ' : Matrix n n ℂ} (h : (ρ - σ).IsHermitian)
    (h' : (ρ' - σ').IsHermitian) (heq : ρ - σ = ρ' - σ') : traceDist h = traceDist h' := by
  rw [traceDist, traceDist, traceNorm_congr h h' heq]

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

/-! ## Trace-norm subadditivity (the triangle inequality)

The route follows `specs/trace-distance-triangle-plan.md`: a Jordan decomposition of a
Hermitian matrix into positive/negative parts via the *Hermitian* functional calculus
`Matrix.IsHermitian.cfc f = U · diag(↑∘f∘λ) · Uᴴ` (defined for **any** `f : ℝ → ℝ`, so the
discontinuous positive-eigenspace projector is admissible), plus the linchpin
`tr_psd_mul_nonneg : 0 ≤ Re Tr(S·P)` for `S, P` positive-semidefinite. -/

/-- **`IsHermitian.cfc f` is Hermitian.** `U · diag(↑∘f∘λ) · Uᴴ` is self-adjoint because the
diagonal of real values is. -/
lemma cfc_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).IsHermitian := by
  unfold Matrix.IsHermitian.cfc Matrix.IsHermitian
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  have hstar : star (RCLike.ofReal ∘ f ∘ hA.eigenvalues : n → ℂ)
      = (RCLike.ofReal ∘ f ∘ hA.eigenvalues) := by funext i; simp
  rw [hstar]

/-- **Multiplicativity of `IsHermitian.cfc`:** `(hM.cfc f)·(hM.cfc g) = hM.cfc (f·g)`. The
two conjugating unitaries collapse via `Uᴴ U = 1` and `diagonal_mul_diagonal`. -/
lemma cfc_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f * hA.cfc g = hA.cfc (fun x => f x * g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  have huu : star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hdd : diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
        * diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues)
      = (diagonal (RCLike.ofReal ∘ (fun x => f x * g x) ∘ hA.eigenvalues) : Matrix n n ℂ) := by
    rw [diagonal_mul_diagonal]; congr 1; ext i; simp [Function.comp]
  calc (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
          * star (hA.eigenvectorUnitary : Matrix n n ℂ)
        * ((hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues)
          * star (hA.eigenvectorUnitary : Matrix n n ℂ))
      = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
          * (star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ))
          * diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues)
          * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
    _ = (hA.eigenvectorUnitary : Matrix n n ℂ) * (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
          * diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues))
          * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
        rw [huu]; simp only [Matrix.mul_assoc, mul_one]
    _ = (hA.eigenvectorUnitary : Matrix n n ℂ)
          * diagonal (RCLike.ofReal ∘ (fun x => f x * g x) ∘ hA.eigenvalues)
          * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by rw [hdd]

/-- **Additivity of `IsHermitian.cfc`:** `(hM.cfc f) + (hM.cfc g) = hM.cfc (f + g)`
(pointwise sum). Same conjugated-diagonal collapse as `cfc_mul`, with `diagonal_add`. -/
lemma cfc_add {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f + hA.cfc g = hA.cfc (fun x => f x + g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  congr 2
  rw [Matrix.diagonal_add]
  congr 1; ext i; simp [Function.comp]

/-- **Subtractivity of `IsHermitian.cfc`:** `(hM.cfc f) − (hM.cfc g) = hM.cfc (f − g)`. -/
lemma cfc_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f - hA.cfc g = hA.cfc (fun x => f x - g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  rw [Matrix.diagonal_sub]
  congr 1; ext i; simp [Function.comp]

/-- `IsHermitian.cfc (fun _ => 0) = 0`. -/
lemma cfc_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) : hA.cfc (fun _ => 0) = 0 := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  have h : (RCLike.ofReal ∘ (fun _ : ℝ => (0:ℝ)) ∘ hA.eigenvalues) = (fun _ : n => (0:ℂ)) := by
    funext i; simp
  rw [h, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- **Negation through `IsHermitian.cfc`:** `−(hM.cfc f) = hM.cfc (−f)`. -/
lemma cfc_neg {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    -hA.cfc f = hA.cfc (fun x => -f x) := by
  rw [← zero_sub, ← cfc_zero hA, cfc_sub]
  congr 1; funext x; simp

/-- `IsHermitian.cfc id = A`: the functional calculus of the identity recovers the operator
(the spectral theorem). -/
lemma cfc_id {A : Matrix n n ℂ} (hA : A.IsHermitian) : hA.cfc id = A := by
  conv_rhs => rw [hA.spectral_theorem]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  congr 2

/-- `IsHermitian.cfc` of a pointwise non-negative function is positive-semidefinite:
`U · diag(↑∘g∘λ) · Uᴴ` with `g ∘ λ ≥ 0`. -/
lemma cfc_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) :
    (hA.cfc g).PosSemidef := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  have hdiag : (diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues) : Matrix n n ℂ).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    refine RCLike.nonneg_iff.mpr ⟨?_, by simp [Function.comp]⟩
    simp only [Function.comp_apply, RCLike.ofReal_re]
    exact hg _
  have h := hdiag.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix n n ℂ)
  rwa [Matrix.star_eq_conjTranspose]

/-- **The linchpin (`TR-PSD`):** for positive-semidefinite `S, P`, `0 ≤ Re Tr(S·P)`. Route:
`√S := S.cfc Real.sqrt` is Hermitian with `√S·√S = S` (PSD eigenvalues), so
`Tr(S·P) = Tr(√S·P·(√S)ᴴ)` by trace cyclicity, and `√S·P·(√S)ᴴ` is PSD with non-negative
trace. -/
lemma tr_psd_mul_nonneg {S P : Matrix n n ℂ} (hS : S.PosSemidef) (hP : P.PosSemidef) :
    0 ≤ RCLike.re (S * P).trace := by
  set sqS : Matrix n n ℂ := hS.1.cfc Real.sqrt with hsqS_def
  have hsqS_herm : sqS.IsHermitian := cfc_isHermitian hS.1 Real.sqrt
  -- √S·√S = S, since `√λ·√λ = λ` for the non-negative eigenvalues of S.
  have hsq : sqS * sqS = S := by
    rw [hsqS_def, cfc_mul]
    -- `(fun x => √x·√x)` and `id` agree on the eigenvalues (all ≥ 0), so the cfc's coincide.
    have hcfc_eq : hS.1.cfc (fun x => Real.sqrt x * Real.sqrt x) = hS.1.cfc id := by
      unfold Matrix.IsHermitian.cfc
      congr 2
      funext i
      simp only [Function.comp_apply, id_eq]
      rw [Real.mul_self_sqrt (hS.eigenvalues_nonneg i)]
    rw [hcfc_eq, cfc_id hS.1]
  have h1 : (S * P).trace = (sqS * P * sqSᴴ).trace := by
    rw [← hsq, hsqS_herm.eq, Matrix.mul_assoc, Matrix.trace_mul_comm sqS (sqS * P),
      Matrix.mul_assoc]
  rw [h1]
  have hpsd : (sqS * P * sqSᴴ).PosSemidef := hP.mul_mul_conjTranspose_same sqS
  exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1

/-- The **positive part** of a Hermitian matrix, `A₊ = U · diag(λᵢ⁺) · Uᴴ` with
`λ⁺ = max λ 0`. Reusable Jordan-decomposition primitive. -/
noncomputable def posPart {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hA.cfc (fun x => max x 0)

/-- The **negative part** of a Hermitian matrix, `A₋ = U · diag(λᵢ⁻) · Uᴴ` with
`λ⁻ = max (−λ) 0`, so that `A = A₊ − A₋` and `|A| = A₊ + A₋`. -/
noncomputable def negPart {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hA.cfc (fun x => max (-x) 0)

/-- The **positive-eigenspace projector** `P₊ = U · diag(1_{λᵢ>0}) · Uᴴ`. Discontinuous, hence
built through `IsHermitian.cfc` (admissible for any `f`), never generic `cfc`. -/
noncomputable def posProj {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hA.cfc (fun x => if 0 < x then 1 else 0)

lemma posPart_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) : (posPart hA).PosSemidef :=
  cfc_posSemidef hA fun x => le_max_right x 0

lemma negPart_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) : (negPart hA).PosSemidef :=
  cfc_posSemidef hA fun x => le_max_right (-x) 0

lemma posProj_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) : (posProj hA).PosSemidef :=
  cfc_posSemidef hA fun x => by by_cases h : 0 < x <;> simp [h]

/-- `IsHermitian.cfc (fun _ => 1) = 1`. -/
lemma cfc_one {A : Matrix n n ℂ} (hA : A.IsHermitian) : hA.cfc (fun _ => 1) = 1 := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  have h : (RCLike.ofReal ∘ (fun _ : ℝ => (1:ℝ)) ∘ hA.eigenvalues) = (fun _ : n => (1:ℂ)) := by
    funext i; simp
  rw [h, show (diagonal (fun _ : n => (1:ℂ))) = (1 : Matrix n n ℂ) from Matrix.diagonal_one,
    Matrix.mul_one, Matrix.star_eq_conjTranspose]
  exact Unitary.coe_mul_star_self hA.eigenvectorUnitary

/-- `1 − P₊` is positive-semidefinite: it equals `hA.cfc (1_{x ≤ 0})`, a non-negative cfc. -/
lemma one_sub_posProj_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ((1 : Matrix n n ℂ) - posProj hA).PosSemidef := by
  rw [← cfc_one hA]
  unfold posProj
  rw [cfc_sub]
  exact cfc_posSemidef hA fun x => by by_cases h : 0 < x <;> simp [h]

/-- **`H · P₊ = H₊`** (the positive part as `H` times its positive-eigenspace projector):
pointwise `x · 1_{x>0} = max x 0`. -/
lemma mul_posProj_eq_posPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A * posProj hA = posPart hA := by
  have hstep : hA.cfc id * posProj hA = posPart hA := by
    unfold posProj posPart
    rw [cfc_mul]
    congr 1
    funext x
    simp only [id_eq]
    rcases le_or_gt x 0 with h | h
    · simp [not_lt.mpr h, max_eq_right h]
    · simp [h, max_eq_left (le_of_lt h)]
  rw [← hstep, cfc_id hA]

/-- **`H₊ + H₋ = |H|`** (the absolute value via the functional calculus): pointwise
`max x 0 + max (−x) 0 = |x|`. -/
lemma posPart_add_negPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    posPart hA + negPart hA = hA.cfc (fun x => |x|) := by
  unfold posPart negPart
  rw [cfc_add]
  congr 1
  funext x
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), add_zero, abs_of_nonneg h]
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), zero_add, abs_of_neg h]

/-- **`H₊ − H₋ = H`** (Jordan decomposition): pointwise `max x 0 − max (−x) 0 = x`. -/
lemma posPart_sub_negPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    posPart hA - negPart hA = A := by
  conv_rhs => rw [← cfc_id hA]
  unfold posPart negPart
  rw [cfc_sub]
  congr 1
  funext x
  simp only [id_eq]
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), zero_sub, neg_neg]

/-- The trace of `H₊` is real and equals `∑ᵢ λᵢ⁺`; combined with the matching `H₋` fact,
`traceNorm = Re Tr(H₊) + Re Tr(H₋)`. -/
lemma re_trace_posPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    RCLike.re (posPart hA).trace = ∑ i, max (hA.eigenvalues i) 0 := by
  unfold posPart
  rw [← hA.cfc_eq (fun x => max x 0), re_trace_cfc hA (fun x => max x 0)]

lemma re_trace_negPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    RCLike.re (negPart hA).trace = ∑ i, max (-hA.eigenvalues i) 0 := by
  unfold negPart
  rw [← hA.cfc_eq (fun x => max (-x) 0), re_trace_cfc hA (fun x => max (-x) 0)]

/-- **L5: `traceNorm H = Re Tr(H₊) + Re Tr(H₋)`** — the trace norm as the sum of the traces of
the two Jordan parts (`∑ |λᵢ| = ∑ λᵢ⁺ + ∑ λᵢ⁻`). -/
lemma traceNorm_eq_re_trace_posPart_add_negPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm hA = RCLike.re (posPart hA).trace + RCLike.re (negPart hA).trace := by
  rw [re_trace_posPart, re_trace_negPart, traceNorm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rcases le_or_gt 0 (hA.eigenvalues i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), add_zero, abs_of_nonneg h]
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), zero_add, abs_of_neg h]

/-- **L6 (key bound):** for Hermitian `A` and `P` with both `P` and `1 − P` positive-
semidefinite, `Re Tr(A·P) ≤ Re Tr(A₊)`. Write `A = A₊ − A₋`; then
`Tr(A·P) = Tr(A₊·P) − Tr(A₋·P) ≤ Tr(A₊·P) ≤ Tr(A₊)` by `tr_psd_mul_nonneg` twice
(`Tr(A₋·P) ≥ 0`, `Tr(A₊·(1−P)) ≥ 0`). -/
lemma re_trace_mul_le_re_trace_posPart {A P : Matrix n n ℂ} (hA : A.IsHermitian)
    (hP : P.PosSemidef) (hP' : ((1 : Matrix n n ℂ) - P).PosSemidef) :
    RCLike.re (A * P).trace ≤ RCLike.re (posPart hA).trace := by
  -- A·P = A₊·P − A₋·P.
  have hAP : A * P = posPart hA * P - negPart hA * P := by
    rw [← Matrix.sub_mul, posPart_sub_negPart]
  -- A₊ = A₊·P + A₊·(1−P).
  have hsplit : posPart hA = posPart hA * P + posPart hA * ((1 : Matrix n n ℂ) - P) := by
    rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  -- Step 1: Re Tr(A·P) ≤ Re Tr(A₊·P).
  have h1 : RCLike.re (A * P).trace ≤ RCLike.re (posPart hA * P).trace := by
    rw [hAP, Matrix.trace_sub, map_sub]
    have hnn : 0 ≤ RCLike.re (negPart hA * P).trace :=
      tr_psd_mul_nonneg (negPart_posSemidef hA) hP
    linarith
  -- Step 2: Re Tr(A₊·P) ≤ Re Tr(A₊).
  have h2 : RCLike.re (posPart hA * P).trace ≤ RCLike.re (posPart hA).trace := by
    conv_rhs => rw [hsplit]
    rw [Matrix.trace_add, map_add]
    have hnn : 0 ≤ RCLike.re (posPart hA * ((1 : Matrix n n ℂ) - P)).trace :=
      tr_psd_mul_nonneg (posPart_posSemidef hA) hP'
    linarith
  linarith

/-- **L7:** for Hermitian `A, B` and `H = A + B`, `Re Tr(H₊) ≤ Re Tr(A₊) + Re Tr(B₊)`. Use
`Tr(H₊) = Tr(H·P₊) = Tr(A·P₊) + Tr(B·P₊)` and the key bound `L6` on each summand with
`P = P₊(H)` (which has `P₊, 1 − P₊` both PSD). -/
lemma re_trace_posPart_add_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (posPart (hA.add hB)).trace
      ≤ RCLike.re (posPart hA).trace + RCLike.re (posPart hB).trace := by
  have hHherm : (A + B).IsHermitian := hA.add hB
  -- Tr(H₊) = Tr(H·P₊) = Tr(A·P₊) + Tr(B·P₊).
  have hHP : RCLike.re (posPart hHherm).trace
      = RCLike.re (A * posProj hHherm).trace + RCLike.re (B * posProj hHherm).trace := by
    rw [← mul_posProj_eq_posPart hHherm, Matrix.add_mul, Matrix.trace_add, map_add]
  rw [hHP]
  have hbA : RCLike.re (A * posProj hHherm).trace ≤ RCLike.re (posPart hA).trace :=
    re_trace_mul_le_re_trace_posPart hA (posProj_posSemidef hHherm)
      (one_sub_posProj_posSemidef hHherm)
  have hbB : RCLike.re (B * posProj hHherm).trace ≤ RCLike.re (posPart hB).trace :=
    re_trace_mul_le_re_trace_posPart hB (posProj_posSemidef hHherm)
      (one_sub_posProj_posSemidef hHherm)
  linarith

/-- **L6 (negative-part key bound):** for Hermitian `A` and `P` with `P, 1 − P` PSD,
`−Re Tr(A₋) ≤ Re Tr(A·P)`. From `Tr(A·P) = Tr(A₊·P) − Tr(A₋·P) ≥ 0 − Tr(A₋) = −Tr(A₋)`
(`Tr(A₊·P) ≥ 0`, `Tr(A₋·(1−P)) ≥ 0`). -/
lemma neg_re_trace_negPart_le_re_trace_mul {A P : Matrix n n ℂ} (hA : A.IsHermitian)
    (hP : P.PosSemidef) (hP' : ((1 : Matrix n n ℂ) - P).PosSemidef) :
    -RCLike.re (negPart hA).trace ≤ RCLike.re (A * P).trace := by
  have hAP : A * P = posPart hA * P - negPart hA * P := by
    rw [← Matrix.sub_mul, posPart_sub_negPart]
  have hsplit : negPart hA = negPart hA * P + negPart hA * ((1 : Matrix n n ℂ) - P) := by
    rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  rw [hAP, Matrix.trace_sub, map_sub]
  have hp : 0 ≤ RCLike.re (posPart hA * P).trace :=
    tr_psd_mul_nonneg (posPart_posSemidef hA) hP
  have hn : RCLike.re (negPart hA * P).trace ≤ RCLike.re (negPart hA).trace := by
    conv_rhs => rw [hsplit]
    rw [Matrix.trace_add, map_add]
    have : 0 ≤ RCLike.re (negPart hA * ((1 : Matrix n n ℂ) - P)).trace :=
      tr_psd_mul_nonneg (negPart_posSemidef hA) hP'
    linarith
  linarith

/-- **`H · P₋ = −H₋`** where `P₋ = 1 − P₊` is the non-positive-eigenspace projector:
pointwise `x · (1 − 1_{x>0}) = x · 1_{x≤0} = −max(−x) 0`. -/
lemma mul_one_sub_posProj_eq_neg_negPart {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A * ((1 : Matrix n n ℂ) - posProj hA) = -negPart hA := by
  have hstep : hA.cfc id * ((1 : Matrix n n ℂ) - posProj hA) = -negPart hA := by
    rw [← cfc_one hA]
    unfold posProj negPart
    rw [cfc_sub, cfc_mul, cfc_neg]
    congr 1
    funext x
    simp only [id_eq]
    rcases le_or_gt x 0 with h | h
    · rw [if_neg (not_lt.mpr h), max_eq_left (by linarith)]; ring
    · rw [if_pos h, max_eq_right (by linarith)]; ring
  rw [← hstep, cfc_id hA]

/-- **L7 (negative part):** `Re Tr(H₋) ≤ Re Tr(A₋) + Re Tr(B₋)` for `H = A + B`. -/
lemma re_trace_negPart_add_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (negPart (hA.add hB)).trace
      ≤ RCLike.re (negPart hA).trace + RCLike.re (negPart hB).trace := by
  have hHherm : (A + B).IsHermitian := hA.add hB
  -- Tr(H₋) = −Tr(H·P₋) = −Tr(A·P₋) − Tr(B·P₋).
  have hHP : RCLike.re (negPart hHherm).trace
      = -(RCLike.re (A * ((1 : Matrix n n ℂ) - posProj hHherm)).trace)
        + -(RCLike.re (B * ((1 : Matrix n n ℂ) - posProj hHherm)).trace) := by
    have h := mul_one_sub_posProj_eq_neg_negPart hHherm
    have h2 : (A + B) * ((1 : Matrix n n ℂ) - posProj hHherm) = -negPart hHherm := h
    rw [Matrix.add_mul] at h2
    have h3 : RCLike.re (negPart hHherm).trace
        = -(RCLike.re ((A * ((1 : Matrix n n ℂ) - posProj hHherm)
            + B * ((1 : Matrix n n ℂ) - posProj hHherm))).trace) := by
      rw [show A * ((1 : Matrix n n ℂ) - posProj hHherm)
          + B * ((1 : Matrix n n ℂ) - posProj hHherm) = -negPart hHherm from h2,
        Matrix.trace_neg, map_neg, neg_neg]
    rw [h3, Matrix.trace_add, map_add]; ring
  rw [hHP]
  have hbA : -RCLike.re (negPart hA).trace
      ≤ RCLike.re (A * ((1 : Matrix n n ℂ) - posProj hHherm)).trace :=
    neg_re_trace_negPart_le_re_trace_mul hA (one_sub_posProj_posSemidef hHherm)
      (by simpa using posProj_posSemidef hHherm)
  have hbB : -RCLike.re (negPart hB).trace
      ≤ RCLike.re (B * ((1 : Matrix n n ℂ) - posProj hHherm)).trace :=
    neg_re_trace_negPart_le_re_trace_mul hB (one_sub_posProj_posSemidef hHherm)
      (by simpa using posProj_posSemidef hHherm)
  linarith

/-- **L8: trace-norm subadditivity** `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁` for Hermitian `A, B`. Splits
`traceNorm = Re Tr(·₊) + Re Tr(·₋)` and bounds each part by `L7` (`posPart`) and its
negative-part counterpart. -/
lemma traceNorm_add_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (hA.add hB) ≤ traceNorm hA + traceNorm hB := by
  rw [traceNorm_eq_re_trace_posPart_add_negPart (hA.add hB),
    traceNorm_eq_re_trace_posPart_add_negPart hA,
    traceNorm_eq_re_trace_posPart_add_negPart hB]
  have hpos := re_trace_posPart_add_le hA hB
  have hneg := re_trace_negPart_add_le hA hB
  linarith

/-- **L9: the trace-distance triangle inequality** `D(ρ,τ) ≤ D(ρ,σ) + D(σ,τ)` — completing the
metric. From `traceNorm` subadditivity on `ρ − τ = (ρ − σ) + (σ − τ)` and `D = ½‖·‖₁`. -/
lemma traceDist_triangle {ρ σ τ : Matrix n n ℂ} (hρτ : (ρ - τ).IsHermitian)
    (hρσ : (ρ - σ).IsHermitian) (hστ : (σ - τ).IsHermitian) :
    traceDist hρτ ≤ traceDist hρσ + traceDist hστ := by
  unfold traceDist
  -- ρ − τ = (ρ − σ) + (σ − τ), so traceNorm (ρ−τ) = traceNorm of the sum.
  have hsum : traceNorm hρτ = traceNorm (hρσ.add hστ) :=
    traceNorm_congr hρτ (hρσ.add hστ) (by abel)
  rw [hsum]
  have := traceNorm_add_le hρσ hστ
  linarith

end QuantumInfo
