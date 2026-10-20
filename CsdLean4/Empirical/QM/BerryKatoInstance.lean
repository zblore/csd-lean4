/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.AdiabaticPhase
public import CsdLean4.Empirical.QM.BerryAdiabatic

/-!
# Berry's rotating field as an instance of Kato's adiabatic theorem

**Category:** 3-Local (QM-validity). BACKLOG #165 (out of ~~#88~~): ~~#56~~'s rigid rotation as
an instance of the general theorem — a regression and an honest comparison, nothing more.

`BerryAdiabatic.lean` solves the spin-½ in a rotating field *exactly* and reads off the phase with
an explicit `O(ω)` error. The general theorem (#158–#164) must specialise to it. Here it does:

* ★ `fieldHam_mul_self`, `fieldHam_trace`, `fieldHam_eigenvalues_sq`, `card_eigenvalues_eq_one` —
  `H(t)² = (B/2)² · 1` and `tr H(t) = 0`, so the eigenvalues of `H(t)` are exactly `±B/2`, one
  each (the general facts `Matrix.IsHermitian.eigenvalues_sq_eq_of_mul_self`,
  `Fintype.card_subtype_eq_one_of_two` are stated separately);
* ★★ `conePath` — **`H(t) = (B/2) n(t)·σ` is a `GappedPath`** with branch `B/2` and gap `B`;
  `contDiff_fieldHam` (every order), `conePath_mult_eq_one` (nondegenerate), `conePath_hex`,
  `conePath_proj_one_eq` (closed for `ω = 2π`);
* ★★ `conePath_isPhysPropagator` — **the exact propagator `V(Ts)` is the physical propagator at
  speed `T`** of the path `fieldHam θ (ωT) B`;
* ★ `coneSection_*` — BP-2's cone curve is a `C¹` unit section of the eigenline
  (`GappedPath.proj_toEuclideanCLM_apply_of_eq`), closed for `ω = 2π`;
* ★★★ `exists_norm_state_sub_phase_le` — **the general phase theorem, specialised**: there is `C`
  such that for every `ω > 0` (with `Ω ≠ 0`), after one turn `T = 2π/ω`,
  `‖ψ(T) − e^{i(−(B/2)T − π(1 − cos θ))} ψ₀‖ ≤ C ω / (2π)` — the same dynamical and geometric
  phases as ~~#56~~'s ★★★ `norm_inner_state_sub_exp_le`;
* `exists_norm_inner_state_sub_exp_le` — the overlap form, directly comparable with ~~#56~~;
* `berry_bound_eq_kato_form`, `berry_bound_le_kato_form` — **the honest comparison**: ~~#56~~'s
  explicit error `πω/(2(B − ω)) + (ω/(B − ω))²` is `π²/((B − ω) T) + 4π²/((B − ω)² T²)` in the
  general theorem's variable `T`, and for `ω ≤ B/2` it is at most `(2π(π + 2)/B) · ω/(2π)` — so in
  this model the general theorem's constant can be taken `C = 2π(π + 2)/g` for the overlap, with
  `g = B` the gap (a datapoint for BACKLOG #166, not a general formula).

## Honest scope

* The general constant `C` exists by compactness (#162) and is not computed; what is compared is
  the *shape* of the bound and the *phases*, which agree exactly, plus the explicit constant that
  ~~#56~~'s exact solution supplies for this one model.
* `Ω ≠ 0` (`rabiFreq θ ω B ≠ 0`) is the hypothesis under which ~~#56~~'s propagator is proved to
  solve the Schrödinger equation; it holds for `0 < ω < B`.
* The path parameter is `s = t/T`; the general theorem's `[0, 1]` is one turn of the field.

References: M. V. Berry, Proc. R. Soc. A 392 (1984) 45, §5; T. Kato, J. Phys. Soc. Japan 5 (1950);
`AdiabaticPhase.lean` (#164), `AdiabaticBornFock.lean` (#163), `AdiabaticComparison.lean` (#162),
`BerryAdiabatic.lean` (#56), `BerryPhase.lean` (BP-2); `specs/berry-phase-scoping.md` BP-5;
`specs/BACKLOG.md` #165, ~~#88~~, ~~#56~~.
-/

@[expose] public section

noncomputable section

open QuantumInfo.SU2 QuantumInfo.RotatingFrame GeometricPhase Matrix Set
open scoped Matrix Matrix.Norms.L2Operator Real ComplexConjugate

/-! ### Two general facts -/

/-- The eigenvalues of a Hermitian matrix with `A² = r² · 1` satisfy `μ² = r²`. -/
theorem Matrix.IsHermitian.eigenvalues_sq_eq_of_mul_self {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) {r : ℝ}
    (hsq : A * A = ((r ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (j : Fin N) :
    hA.eigenvalues j ^ 2 = r ^ 2 := by
  have hev := hA.mulVec_eigenvectorBasis j
  have he0 : (hA.eigenvectorBasis j).ofLp ≠ 0 := by
    intro h
    have h1 := hA.eigenvectorBasis.orthonormal.1 j
    rw [(WithLp.ofLp_eq_zero 2).1 h, norm_zero] at h1
    exact zero_ne_one h1
  have h1 : (A * A) *ᵥ (hA.eigenvectorBasis j).ofLp
      = ((hA.eigenvalues j ^ 2 : ℝ) : ℂ) • (hA.eigenvectorBasis j).ofLp := by
    rw [← mulVec_mulVec, hev, mulVec_smul, hev, smul_smul, ← Complex.coe_smul]
    congr 1
    push_cast
    ring
  rw [hsq, smul_mulVec, one_mulVec] at h1
  have h2 : (((r ^ 2 : ℝ) : ℂ) - ((hA.eigenvalues j ^ 2 : ℝ) : ℂ)) • (hA.eigenvectorBasis j).ofLp
      = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact_mod_cast (sub_eq_zero.1 h).symm
  · exact absurd h he0

/-- A real function on `Fin 2` with values in `{r, −r}`, `r ≠ 0`, summing to zero takes the
value `r` exactly once. -/
theorem Fintype.card_subtype_eq_one_of_two {f : Fin 2 → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hsq : ∀ j, f j ^ 2 = r ^ 2) (hsum : f 0 + f 1 = 0) : Fintype.card {j // f j = r} = 1 := by
  rw [Fintype.card_eq_one_iff]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq 0) with h0 | h0
  · have h1 : f 1 = -r := by linarith
    refine ⟨⟨0, h0⟩, fun y => ?_⟩
    obtain ⟨j, hj⟩ := y
    fin_cases j
    · rfl
    · exfalso
      have hj' : f 1 = r := hj
      exact hr (by linarith)
  · have h1 : f 1 = r := by linarith
    refine ⟨⟨1, h1⟩, fun y => ?_⟩
    obtain ⟨j, hj⟩ := y
    fin_cases j
    · exfalso
      have hj' : f 0 = r := hj
      exact hr (by linarith)
    · rfl

/-- `|⟪x, v⟫ − c| ≤ ‖v − c x‖` for a unit vector `x`. -/
theorem norm_inner_sub_le_norm_sub_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x : E} (hx : ‖x‖ = 1) (v : E) (c : ℂ) : ‖inner ℂ x v - c‖ ≤ ‖v - c • x‖ := by
  have h : inner ℂ x (v - c • x) = inner ℂ x v - c := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
    simp
  rw [← h]
  calc ‖inner ℂ x (v - c • x)‖ ≤ ‖x‖ * ‖v - c • x‖ := norm_inner_le_norm _ _
    _ = ‖v - c • x‖ := by rw [hx, one_mul]

namespace CSD
namespace Empirical
namespace QM
namespace BerryKato

open BerryAdiabatic

/-! ### The spectrum of `H(t)` -/

/-- `H(t)² = (B/2)² · 1`. -/
theorem fieldHam_mul_self (θ ω B t : ℝ) :
    fieldHam θ ω B t * fieldHam θ ω B t
      = (((B / 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hn : (B * Real.sin θ * Real.cos (ω * t)) ^ 2 + (B * Real.sin θ * Real.sin (ω * t)) ^ 2
      + (B * Real.cos θ) ^ 2 = B ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq (ω * t)
    have h2 := Real.sin_sq_add_cos_sq θ
    linear_combination (B ^ 2 * Real.sin θ ^ 2) * h1 + B ^ 2 * h2
  rw [fieldHam, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliAxis_mul_self, hn, smul_smul]
  congr 1
  push_cast
  ring

theorem fieldHam_trace (θ ω B t : ℝ) : (fieldHam θ ω B t).trace = 0 := by
  simp [fieldHam, pauliAxis, Matrix.trace, Fin.sum_univ_two]

/-- Every eigenvalue of `H(t)` has `μ² = (B/2)²`. -/
theorem fieldHam_eigenvalues_sq (θ ω B t : ℝ) (j : Fin 2) :
    (fieldHam_isHermitian θ ω B t).eigenvalues j ^ 2 = (B / 2) ^ 2 :=
  (fieldHam_isHermitian θ ω B t).eigenvalues_sq_eq_of_mul_self (fieldHam_mul_self θ ω B t) j

theorem fieldHam_eigenvalues_sum (θ ω B t : ℝ) :
    (fieldHam_isHermitian θ ω B t).eigenvalues 0 + (fieldHam_isHermitian θ ω B t).eigenvalues 1
      = 0 := by
  have h := (fieldHam_isHermitian θ ω B t).trace_eq_sum_eigenvalues
  rw [fieldHam_trace, Fin.sum_univ_two] at h
  have h2 : (((fieldHam_isHermitian θ ω B t).eigenvalues 0
      + (fieldHam_isHermitian θ ω B t).eigenvalues 1 : ℝ) : ℂ) = 0 := by
    push_cast
    exact h.symm
  exact_mod_cast h2

/-- ★ **`B/2` is a simple eigenvalue of `H(t)`.** -/
theorem card_eigenvalues_eq_one (θ ω : ℝ) {B : ℝ} (hB : 0 < B) (t : ℝ) :
    Fintype.card {j // (fieldHam_isHermitian θ ω B t).eigenvalues j = B / 2} = 1 :=
  Fintype.card_subtype_eq_one_of_two (by positivity) (fieldHam_eigenvalues_sq θ ω B t)
    (fieldHam_eigenvalues_sum θ ω B t)

/-! ### Smoothness and periodicity of the path -/

/-- `H(t)` as `cos ωt · M₁ + sin ωt · M₂ + M₃` with constant matrices. -/
theorem fieldHam_eq (θ ω B : ℝ) :
    fieldHam θ ω B = fun t => ((1 / 2 : ℝ) : ℂ) • (Real.cos (ω * t) • pauliAxis (B * Real.sin θ) 0 0
      + Real.sin (ω * t) • pauliAxis 0 (B * Real.sin θ) 0 + pauliAxis 0 0 (B * Real.cos θ)) := by
  funext t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fieldHam, pauliAxis] <;> ring

/-- The path is smooth to every order. -/
theorem contDiff_fieldHam (θ ω B : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (fieldHam θ ω B) := by
  rw [fieldHam_eq]
  refine ContDiff.const_smul _ (ContDiff.add (ContDiff.add ?_ ?_) contDiff_const)
  · exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).smul contDiff_const
  · exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).smul contDiff_const

/-- Rescaling the parameter: `H_ω(T s) = H_{ωT}(s)`. -/
theorem fieldHam_rescale (θ ω B T s : ℝ) : fieldHam θ ω B (T * s) = fieldHam θ (ω * T) B s := by
  unfold fieldHam
  rw [show ω * (T * s) = ω * T * s by ring]

/-- For `ω = 2π` the path closes after one unit of parameter. -/
theorem fieldHam_one_eq_zero (θ B : ℝ) : fieldHam θ (2 * π) B 1 = fieldHam θ (2 * π) B 0 := by
  simp [fieldHam, Real.cos_two_pi, Real.sin_two_pi]

/-! ### The gapped path -/

/-- ★★ **The rotating field is a gapped path**: branch `B/2`, gap `B`. -/
def conePath (θ ω : ℝ) {B : ℝ} (hB : 0 < B) : GappedPath 2 where
  H := fieldHam θ ω B
  isHermitian := fieldHam_isHermitian θ ω B
  lam := fun _ => B / 2
  continuous_lam := continuous_const
  g := B
  g_pos := hB
  gap := fun s j => by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (fieldHam_eigenvalues_sq θ ω B s j) with h | h
    · exact Or.inl h
    · right
      rw [h, show -(B / 2) - B / 2 = -B by ring, abs_neg, abs_of_pos hB]

theorem conePath_H (θ ω : ℝ) {B : ℝ} (hB : 0 < B) : (conePath θ ω hB).H = fieldHam θ ω B := rfl

theorem conePath_lam (θ ω : ℝ) {B : ℝ} (hB : 0 < B) (s : ℝ) : (conePath θ ω hB).lam s = B / 2 :=
  rfl

/-- The branch is an eigenvalue at every parameter. -/
theorem conePath_hex (θ ω : ℝ) {B : ℝ} (hB : 0 < B) (s : ℝ) :
    ∃ j, ((conePath θ ω hB).isHermitian s).eigenvalues j = (conePath θ ω hB).lam s := by
  have h : 0 < Fintype.card {j // (fieldHam_isHermitian θ ω B s).eigenvalues j = B / 2} := by
    rw [card_eigenvalues_eq_one θ ω hB s]
    exact zero_lt_one
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.1 h
  exact ⟨j, hj⟩

/-- ★ **The branch is nondegenerate.** -/
theorem conePath_mult_eq_one (θ ω : ℝ) {B : ℝ} (hB : 0 < B) : (conePath θ ω hB).mult 0 = 1 :=
  card_eigenvalues_eq_one θ ω hB 0

/-- For `ω = 2π` the eigenprojectors close up: `P 1 = P 0`. -/
theorem conePath_proj_one_eq (θ : ℝ) {B : ℝ} (hB : 0 < B) :
    (conePath θ (2 * π) hB).proj 1 = (conePath θ (2 * π) hB).proj 0 :=
  (conePath θ (2 * π) hB).proj_one_eq_of_closed (fieldHam_one_eq_zero θ B) rfl

/-! ### The exact propagator is the physical propagator -/

/-- ★★ **`V(Ts)` is the physical propagator at speed `T`** of the path `fieldHam θ (ωT) B`. -/
theorem conePath_isPhysPropagator (θ : ℝ) {ω B T : ℝ} (hB : 0 < B) (hΩ : rabiFreq θ ω B ≠ 0) :
    (conePath θ (ω * T) hB).IsPhysPropagator T (fun s => prop θ ω B (T * s)) where
  init := by simp [prop_zero]
  hasDerivWithinAt := fun s _ => by
    have h := (hasDerivAt_prop hΩ (T * s)).scomp s ((hasDerivAt_id s).const_mul T)
    refine h.hasDerivWithinAt.congr_deriv ?_
    simp only [mul_one, GappedPath.physGen, conePath_H, fieldHam_rescale,
      Matrix.smul_mul, ← Complex.coe_smul, smul_smul]
    rw [mul_comm (T : ℂ) (-Complex.I)]

/-! ### The cone curve is a section of the eigenline -/

/-- `H(s) ψ(s) = (B/2) ψ(s)` for the cone curve, in `toEuclideanCLM` form. -/
theorem toEuclideanCLM_fieldHam_coneCurve (θ ω B s : ℝ) :
    toEuclideanCLM (𝕜 := ℂ) (fieldHam θ ω B s) (BerryPhase.coneCurve θ (ω * s))
      = ((B / 2 : ℝ) : ℂ) • BerryPhase.coneCurve θ (ω * s) := by
  apply WithLp.ofLp_injective
  rw [ofLp_toEuclideanCLM, WithLp.ofLp_smul]
  exact fieldHam_mulVec_coneCurve θ ω B s

theorem coneSection_contDiff (θ ω : ℝ) :
    ContDiff ℝ 1 fun s : ℝ => BerryPhase.coneCurve θ (ω * s) :=
  (BerryPhase.contDiff_coneCurve θ).comp (contDiff_const.mul contDiff_id)

theorem coneSection_norm (θ ω s : ℝ) : ‖BerryPhase.coneCurve θ (ω * s)‖ = 1 :=
  BerryPhase.norm_coneCurve θ _

/-- ★ The cone curve lies in the eigenline of the path at every parameter. -/
theorem coneSection_proj (θ ω : ℝ) {B : ℝ} (hB : 0 < B) (s : ℝ) :
    toEuclideanCLM (𝕜 := ℂ) ((conePath θ ω hB).proj s) (BerryPhase.coneCurve θ (ω * s))
      = BerryPhase.coneCurve θ (ω * s) :=
  (conePath θ ω hB).proj_toEuclideanCLM_apply_of_eq s (toEuclideanCLM_fieldHam_coneCurve θ ω B s)

/-- For `ω = 2π` the section closes with total phase `0`. -/
theorem coneSection_cyclic (θ : ℝ) :
    BerryPhase.coneCurve θ (2 * π * 1)
      = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • BerryPhase.coneCurve θ (2 * π * 0) := by
  rw [mul_one, mul_zero]
  exact BerryPhase.coneCurve_cyclic θ

/-- The geometric phase of the section over one unit of parameter is Berry's `−π(1 − cos θ)`. -/
theorem coneSection_geometricPhase (θ : ℝ) :
    geometricPhase (fun s : ℝ => BerryPhase.coneCurve θ (2 * π * s)) 1 0
      = -π * (1 - Real.cos θ) :=
  geometricPhase_cone_loop θ (mul_one _)

/-! ### The general theorem, specialised -/

/-- The dynamical phase of the path over one unit of parameter at speed `T`: `e^{−iT·B/2}`. -/
theorem conePath_dynPhase (θ ω : ℝ) {B : ℝ} (hB : 0 < B) (T : ℝ) :
    (conePath θ ω hB).dynPhase T 1 = Complex.exp (-Complex.I * (T : ℂ) * ((B / 2 : ℝ) : ℂ)) := by
  rw [GappedPath.dynPhase]
  congr 2
  simp [conePath_lam]

/-- ★★★ **Kato's phase theorem specialised to Berry's rotating field.** There is a constant `C`
such that for every `ω > 0` with `Ω ≠ 0`, after one turn `T = 2π/ω`,

  `‖ψ(T) − e^{i(−(B/2)T − π(1 − cos θ))} ψ₀‖ ≤ C ω / (2π)`:

the same dynamical phase `−(B/2)T` and geometric phase `−π(1 − cos θ)` as ~~#56~~'s exact
`norm_inner_state_sub_exp_le`, with the general theorem's `O(1/T) = O(ω)` error. -/
theorem exists_norm_state_sub_phase_le (θ : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ, 0 < ω → rabiFreq θ ω B ≠ 0 →
      ‖state θ ω B (2 * π / ω)
          - Complex.exp (((-(B / 2) * (2 * π / ω) - π * (1 - Real.cos θ) : ℝ) : ℂ) * Complex.I)
            • spinUp θ‖
        ≤ C * ω / (2 * π) := by
  set Γ := conePath θ (2 * π) hB with hΓ
  obtain ⟨C, hC0, hC⟩ := Γ.exists_norm_sub_phase_smul_le (n := 2) le_rfl
    (contDiff_fieldHam θ (2 * π) B 2) (conePath_hex θ (2 * π) hB) (conePath_mult_eq_one θ (2 * π) hB)
    (coneSection_contDiff θ (2 * π)) (coneSection_norm θ (2 * π)) (coneSection_proj θ (2 * π) hB)
    (coneSection_cyclic θ)
  refine ⟨C, hC0, fun ω hω hΩ => ?_⟩
  set T : ℝ := 2 * π / ω with hT
  have hTpos : 0 < T := div_pos (by positivity) hω
  have hωT : ω * T = 2 * π := mul_div_cancel₀ _ hω.ne'
  have hprop := conePath_isPhysPropagator θ (T := T) hB hΩ
  rw [hωT] at hprop
  have h := hC T hTpos _ hprop
  rw [coneSection_geometricPhase, conePath_dynPhase, mul_zero, coneCurve_zero_eq_spinUp,
    ← Complex.exp_add] at h
  have hstate : toEuclideanCLM (𝕜 := ℂ) (prop θ ω B (T * 1)) (spinUp θ) = state θ ω B T := by
    rw [mul_one, state]
  rw [hstate] at h
  have hphase : Complex.exp (-Complex.I * (T : ℂ) * ((B / 2 : ℝ) : ℂ)
      + ((-π * (1 - Real.cos θ) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((-(B / 2) * T - π * (1 - Real.cos θ) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hphase] at h
  have hCT : C / T = C * ω / (2 * π) := by
    rw [hT]
    field_simp
  rw [hCT] at h
  exact h

/-- ★★ **The overlap form**, directly comparable with ~~#56~~'s `norm_inner_state_sub_exp_le`:
`|⟪ψ₀, ψ(T)⟫ − e^{i(−(B/2)T − π(1 − cos θ))}| ≤ C ω / (2π)`. -/
theorem exists_norm_inner_state_sub_exp_le (θ : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ, 0 < ω → rabiFreq θ ω B ≠ 0 →
      ‖inner ℂ (spinUp θ) (state θ ω B (2 * π / ω))
          - Complex.exp (((-(B / 2) * (2 * π / ω) - π * (1 - Real.cos θ) : ℝ) : ℂ) * Complex.I)‖
        ≤ C * ω / (2 * π) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_state_sub_phase_le θ hB
  refine ⟨C, hC0, fun ω hω hΩ => ?_⟩
  have hunit : ‖spinUp θ‖ = 1 := by
    rw [← coneCurve_zero_eq_spinUp]
    exact BerryPhase.norm_coneCurve θ 0
  exact (norm_inner_sub_le_norm_sub_smul hunit _ _).trans (hC ω hω hΩ)

/-! ### The honest comparison of constants -/

/-- ~~#56~~'s explicit error in the general theorem's variable `T = 2π/ω`:
`πω/(2(B − ω)) + (ω/(B − ω))² = π²/((B − ω) T) + 4π²/((B − ω)² T²)` — a `1/T` term with constant
`π²/(B − ω)` and a `1/T²` remainder. -/
theorem berry_bound_eq_kato_form {ω B T : ℝ} (hω : 0 < ω) (hωB : ω < B) (hT : ω * T = 2 * π) :
    π * ω / (2 * (B - ω)) + (ω / (B - ω)) ^ 2
      = π ^ 2 / ((B - ω) * T) + 4 * π ^ 2 / ((B - ω) ^ 2 * T ^ 2) := by
  have hd : B - ω ≠ 0 := by linarith
  have hTpos : 0 < T := by nlinarith [Real.pi_pos]
  have hω' : ω = 2 * π / T := by field_simp; linarith
  rw [hω']
  field_simp
  ring

/-- For `ω ≤ B/2`, ~~#56~~'s error is at most `(2π(π + 2)/B) · ω/(2π)`: in this model the general
theorem's constant can be taken to be `2π(π + 2)/g`, `g = B` the gap. -/
theorem berry_bound_le_kato_form {ω B : ℝ} (hω : 0 < ω) (hωB : ω ≤ B / 2) :
    π * ω / (2 * (B - ω)) + (ω / (B - ω)) ^ 2 ≤ 2 * π * (π + 2) / B * ω / (2 * π) := by
  have hB : 0 < B := by linarith
  have hd : B / 2 ≤ B - ω := by linarith
  have hd0 : 0 < B - ω := by linarith
  have h1 : π * ω / (2 * (B - ω)) ≤ π * ω / B := by
    apply div_le_div_of_nonneg_left (by positivity) hB
    linarith
  have h2 : ω / (B - ω) ≤ 2 * ω / B := by
    rw [div_le_div_iff₀ hd0 hB]
    nlinarith
  have h3 : (ω / (B - ω)) ^ 2 ≤ 2 * ω / B := by
    have h4 : 2 * ω / B ≤ 1 := by
      rw [div_le_one hB]
      linarith
    have h5 : 0 ≤ ω / (B - ω) := by positivity
    calc (ω / (B - ω)) ^ 2 ≤ (2 * ω / B) ^ 2 := by gcongr
      _ = (2 * ω / B) * (2 * ω / B) := sq _
      _ ≤ (2 * ω / B) * 1 := by gcongr
      _ = 2 * ω / B := mul_one _
  have hpi := Real.pi_pos
  calc π * ω / (2 * (B - ω)) + (ω / (B - ω)) ^ 2 ≤ π * ω / B + 2 * ω / B := add_le_add h1 h3
    _ = 2 * π * (π + 2) / B * ω / (2 * π) := by
        field_simp

end BerryKato
end QM
end Empirical
end CSD

end

end
