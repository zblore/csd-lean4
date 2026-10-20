/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.RieszProjector
public import CsdLean4.Mathlib.Analysis.Calculus.ContDiffParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The Riesz projector along a gapped path: smoothness and `P Ṗ P = 0`

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #159 (out of ~~#88~~, the second brick of Kato's adiabatic theorem).

A **gapped path** (`GappedPath N`) is a family `H s` of Hermitian matrices with a continuous
eigenvalue branch `lam s` isolated from the rest of the spectrum by a gap `g > 0`, uniformly in
`s`. Its **eigenprojector** `proj s` is the Riesz projector of `H s` over the disc of radius
`g/2` about `lam s` (`RieszProjector.lean`). This file proves that `proj` is as smooth as `H`,
and the identity `P Ṗ P = 0` that Kato's intertwiner (#160) is built on.

* `HasDerivAt.eq_mul_add_mul_of_idempotent`, ★ `HasDerivAt.mul_deriv_mul_eq_zero_of_idempotent` —
  **an idempotent `C¹` family has `Ṗ = ṖP + PṖ` and `P Ṗ P = 0`**: differentiate `P² = P` and
  sandwich. Any normed algebra.
* `resolventIntegrand`, `rieszProj_eq_integral`, `rieszProj_eq_integral_unit` — the Riesz
  projector as an interval integral over `[0, 1]` of the resolvent on the circle;
* `contDiffOn_inv_comp`, ★ `contDiffOn_circleIntegral` — the matrix inverse is `C^n` on units, and
  **a parametric circle integral of a jointly `C^n` integrand is `C^n`** (the general form, used
  again for the reduced resolvent in #162);
* ★★ `contDiffOn_rieszProj` — **over a fixed contour the Riesz projector is `C^n` in the
  matrix path**: the integrand is `C^n` jointly (the inverse is `C^n` on units,
  `contDiffAt_ringInverse`; the units form an open set, `Units.isOpen`), and a parametric interval
  integral of a jointly `C^n` integrand is `C^n` (`contDiffOn_intervalIntegral_of_contDiffOn`,
  generalised from `ℝ` to a normed codomain for this file);
* `GappedPath.proj_eq_near` — **the contour can be frozen locally**: for `|lam s − lam s₀| < g/4`
  the disc about `lam s₀` isolates the same eigenvalue, so `proj s` is the integral over the
  fixed circle about `lam s₀`;
* ★★ `GappedPath.contDiff_proj` — **`proj` is `C^n` whenever `H` is**, by the two previous items;
* `GappedPath.deriv_proj_eq`, ★ `GappedPath.proj_mul_deriv_mul_proj` — **`Ṗ = ṖP + PṖ` and
  `P Ṗ P = 0` along the path**;
* `GappedPath.proj_mul_self`, `proj_isHermitian`, `H_mul_proj` / `proj_mul_H` (`H P = lam • P`),
  `trace_proj` (the trace is the multiplicity), ★ `mult_eq` (**the multiplicity is constant**,
  by continuity of the trace into `ℕ`), ★ `contDiff_lam` — **the eigenvalue branch is `C^n`**
  whenever `H` is, as `lam s = tr(H s · P s) / mult`; so the continuity of `lam` assumed in
  `GappedPath` is all the regularity it ever needs.

## Honest scope

* Finite dimensions, `Fin N`, `𝕜 = ℂ`, the `L2Operator` norm scope throughout: the hypothesis
  `ContDiff ℝ n H` is smoothness into the matrix space with the operator norm (in finite
  dimensions this is entrywise smoothness, but no transfer lemma is used or needed here).
* The gap is uniform in `s` and the branch is given; nothing is said about eigenvalue crossings.
* `contDiffOn_rieszProj` asks for the circle to avoid the spectrum on an open set of parameters;
  openness of that set is NOT derived from continuity of eigenvalues (not in Mathlib) but
  supplied by the gap, through `proj_eq_near`.

References: T. Kato, *Perturbation Theory for Linear Operators*, II §1.4, §5.4; Kato 1950;
S. Teufel, *Adiabatic Perturbation Theory in Quantum Dynamics*, §2.1;
`RieszProjector.lean` (#158), `Analysis/Calculus/ContDiffParametricIntervalIntegral.lean` (#60);
`specs/BACKLOG.md` #159, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology Interval
open Matrix Metric Set Complex Real Filter intervalIntegral

noncomputable section

/-! ### An idempotent `C¹` family: `P Ṗ P = 0` -/

section Idempotent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- ★ **An idempotent `C¹` family has `P Ṗ P = 0`.** If `P t * P t = P t` for all `t` and `P` has
derivative `P'` at `s`, then `P s * P' * P s = 0`: differentiating `P² = P` gives
`P' = P' P + P P'`, and sandwiching with `P` gives `P P' P = 2 P P' P`. -/
theorem HasDerivAt.eq_mul_add_mul_of_idempotent {P : 𝕜 → A} {P' : A} {s : 𝕜}
    (hP : ∀ t, P t * P t = P t) (hd : HasDerivAt P P' s) : P' = P' * P s + P s * P' := by
  have h1 : HasDerivAt (fun t => P t * P t) (P' * P s + P s * P') s := hd.mul hd
  have h2 : (fun t => P t * P t) = P := funext hP
  rw [h2] at h1
  exact hd.unique h1

theorem HasDerivAt.mul_deriv_mul_eq_zero_of_idempotent {P : 𝕜 → A} {P' : A} {s : 𝕜}
    (hP : ∀ t, P t * P t = P t) (hd : HasDerivAt P P' s) : P s * P' * P s = 0 := by
  have h3 : P' = P' * P s + P s * P' := hd.eq_mul_add_mul_of_idempotent hP
  have h4 : P s * P' * P s = P s * P' * P s + P s * P' * P s := by
    calc P s * P' * P s = P s * (P' * P s + P s * P') * P s := by rw [← h3]
      _ = P s * P' * (P s * P s) + (P s * P s) * P' * P s := by noncomm_ring
      _ = P s * P' * P s + P s * P' * P s := by rw [hP s]
  exact add_left_cancel (h4.symm.trans (add_zero _).symm)

end Idempotent

namespace Matrix

variable {N : ℕ}

/-! ### Complex scalars on matrices, smoothly -/

/-- `ℂ`-scalar multiplication on matrices is `C^n` in both arguments, over `ℝ`. -/
theorem contDiff_smul_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → ℂ} {g : E → Matrix (Fin N) (Fin N) ℂ} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) : ContDiff ℝ n fun x => f x • g x :=
  (isBoundedBilinearMap_smul (𝕜 := ℝ) (A := ℂ)
    (E := Matrix (Fin N) (Fin N) ℂ)).contDiff.comp (hf.prodMk hg)

theorem contDiffOn_smul_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → ℂ} {g : E → Matrix (Fin N) (Fin N) ℂ} {s : Set E}
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) : ContDiffOn ℝ n (fun x => f x • g x) s :=
  (isBoundedBilinearMap_smul (𝕜 := ℝ) (A := ℂ)
    (E := Matrix (Fin N) (Fin N) ℂ)).contDiff.comp_contDiffOn (hf.prodMk hg)

/-- The trace as a continuous `ℝ`-linear map. -/
def traceCLM : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap (Fin N) ℂ ℂ).restrictScalars ℝ)

@[simp] theorem traceCLM_apply (A : Matrix (Fin N) (Fin N) ℂ) : traceCLM A = A.trace := rfl

/-! ### The Riesz projector over a fixed contour is smooth in the matrix -/

/-- The resolvent integrand on the circle `C(c, r)`: `(r i e^{iθ}) • (circleMap c r θ • 1 − A)⁻¹`,
with the inverse written as `Ring.inverse` so that its smoothness on units is Mathlib's. -/
def resolventIntegrand (c : ℂ) (r : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (circleMap 0 r θ * I) • Ring.inverse (circleMap c r θ • (1 : Matrix (Fin N) (Fin N) ℂ) - A)

/-- The Riesz projector as an interval integral over `[0, 2π]`. -/
theorem rieszProj_eq_integral (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (r : ℝ) :
    rieszProj A c r = (2 * π * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, resolventIntegrand c r A θ := by
  simp only [rieszProj, circleIntegral, deriv_circleMap, resolventIntegrand,
    nonsing_inv_eq_ringInverse]

/-- The Riesz projector as an interval integral over `[0, 1]`. -/
theorem rieszProj_eq_integral_unit (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (r : ℝ) :
    rieszProj A c r = (2 * π * I)⁻¹ • (2 * π : ℝ) •
      ∫ u in (0 : ℝ)..1, resolventIntegrand c r A (2 * π * u) := by
  rw [rieszProj_eq_integral]
  congr 1
  rw [integral_comp_mul_left (fun θ => resolventIntegrand c r A θ)
    (by positivity : (2 * π : ℝ) ≠ 0), mul_zero, mul_one, smul_smul,
    mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_smul]

/-- Composition with the matrix inverse is `C^n` where the matrix is a unit. -/
theorem contDiffOn_inv_comp {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → Matrix (Fin N) (Fin N) ℂ} (hΦ : ContDiff ℝ n Φ) {W : Set E}
    (hW : ∀ p ∈ W, IsUnit (Φ p)) : ContDiffOn ℝ n (fun p => (Φ p)⁻¹) W := by
  have hinv : ContDiffOn ℝ n (fun p => Ring.inverse (Φ p)) W := by
    refine ContDiffOn.comp (g := Ring.inverse) (f := Φ)
      (t := {x : Matrix (Fin N) (Fin N) ℂ | IsUnit x}) ?_ hΦ.contDiffOn fun p hp => hW p hp
    intro x hx
    have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := n) hx.unit
    rw [IsUnit.unit_spec] at h
    exact h.contDiffWithinAt
  exact hinv.congr fun p _ => nonsing_inv_eq_ringInverse _

/-- ★ **A parametric circle integral of a jointly `C^n` matrix-valued integrand is `C^n` in the
parameter**: if `(s, u) ↦ F s (circleMap c r (2πu))` is `C^n` on an open `W ⊇ V × [0, 1]`, then
`s ↦ ∮_{C(c, r)} F s z dz` is `C^n` on the open `V`. -/
theorem contDiffOn_circleIntegral {n : ℕ∞} {F : ℝ → ℂ → Matrix (Fin N) (Fin N) ℂ} {V : Set ℝ}
    (hV : IsOpen V) (c : ℂ) (r : ℝ) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hVW : ∀ s ∈ V, ∀ u ∈ Icc (0 : ℝ) 1, (s, u) ∈ W)
    (hF : ContDiffOn ℝ n (fun p : ℝ × ℝ => F p.1 (circleMap c r (2 * π * p.2))) W) :
    ContDiffOn ℝ n (fun s => ∮ z in C(c, r), F s z) V := by
  have hsc : ContDiff ℝ n fun p : ℝ × ℝ => circleMap 0 r (2 * π * p.2) * I :=
    ((contDiff_circleMap 0 r).comp (contDiff_const.mul contDiff_snd)).mul contDiff_const
  have hint := contDiffOn_intervalIntegral_of_contDiffOn (F := fun s u =>
    (circleMap 0 r (2 * π * u) * I) • F s (circleMap c r (2 * π * u))) hV hW hVW
    (contDiffOn_smul_of_contDiffOn hsc.contDiffOn hF)
  have heq : ∀ s, (∮ z in C(c, r), F s z) = (2 * π : ℝ) •
      ∫ u in (0 : ℝ)..1, (circleMap 0 r (2 * π * u) * I) • F s (circleMap c r (2 * π * u)) := by
    intro s
    simp only [circleIntegral, deriv_circleMap]
    rw [integral_comp_mul_left (fun θ => (circleMap 0 r θ * I) • F s (circleMap c r θ))
      (by positivity : (2 * π : ℝ) ≠ 0), mul_zero, mul_one, smul_smul,
      mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_smul]
  simp only [heq]
  exact hint.const_smul _

/-- ★★ **Over a fixed contour the Riesz projector is `C^n` in the matrix path.** If `H` is `C^n`
and, for every parameter in the open set `V`, no point of the circle `C(c, r)` is in the spectrum
of `H s`, then `s ↦ rieszProj (H s) c r` is `C^n` on `V`. -/
theorem contDiffOn_rieszProj {n : ℕ∞} {H : ℝ → Matrix (Fin N) (Fin N) ℂ} (hH : ContDiff ℝ n H)
    {V : Set ℝ} (hV : IsOpen V) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ s ∈ V, ∀ z ∈ sphere c r, IsUnit (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H s)) :
    ContDiffOn ℝ n (fun s => rieszProj (H s) c r) V := by
  set Φ : ℝ × ℝ → Matrix (Fin N) (Fin N) ℂ :=
    fun p => circleMap c r (2 * π * p.2) • (1 : Matrix (Fin N) (Fin N) ℂ) - H p.1 with hΦ
  have hΦc : ContDiff ℝ n Φ :=
    (contDiff_smul_of_contDiff ((contDiff_circleMap c r).comp (contDiff_const.mul contDiff_snd))
      contDiff_const).sub (hH.comp contDiff_fst)
  set W : Set (ℝ × ℝ) := Φ ⁻¹' {x | IsUnit x} with hW
  have hWo : IsOpen W := Units.isOpen.preimage hΦc.continuous
  have hVW : ∀ s ∈ V, ∀ u ∈ Icc (0 : ℝ) 1, (s, u) ∈ W := fun s hs u _ =>
    hu s hs _ (circleMap_mem_sphere c hr _)
  unfold rieszProj
  exact ContDiffOn.const_smul _
    (contDiffOn_circleIntegral hV c r hWo hVW (contDiffOn_inv_comp hΦc fun p hp => hp))

/-! ### Gapped paths -/

/-- A **gapped path** of Hermitian matrices: a continuous eigenvalue branch `lam` isolated by a
gap `g > 0` from the rest of the spectrum, uniformly in the parameter. -/
structure GappedPath (N : ℕ) where
  /-- The path of Hermitian matrices. -/
  H : ℝ → Matrix (Fin N) (Fin N) ℂ
  isHermitian : ∀ s, (H s).IsHermitian
  /-- The eigenvalue branch. -/
  lam : ℝ → ℝ
  continuous_lam : Continuous lam
  /-- The gap. -/
  g : ℝ
  g_pos : 0 < g
  /-- Every eigenvalue is either on the branch or at distance at least `g` from it. -/
  gap : ∀ s j, (isHermitian s).eigenvalues j = lam s ∨ g ≤ |(isHermitian s).eigenvalues j - lam s|

namespace GappedPath

variable (Γ : GappedPath N)

/-- The eigenprojector of the branch: the Riesz projector of `H s` over the disc of radius `g/2`
about `lam s`. -/
def proj (s : ℝ) : Matrix (Fin N) (Fin N) ℂ := rieszProj (Γ.H s) (Γ.lam s) (Γ.g / 2)

/-- The multiplicity of the branch at `s`. -/
def mult (s : ℝ) : ℕ := Fintype.card {j // (Γ.isHermitian s).eigenvalues j = Γ.lam s}

theorem dist_eigC (s : ℝ) (j : Fin N) (x : ℝ) :
    dist ((Γ.isHermitian s).eigC j) (x : ℂ) = |(Γ.isHermitian s).eigenvalues j - x| := by
  change dist (((Γ.isHermitian s).eigenvalues j : ℝ) : ℂ) (x : ℂ) = _
  rw [Complex.dist_of_im_eq (by simp)]
  simp [Real.dist_eq]

/-- The circle about `lam s` of radius `g/2` avoids the spectrum of `H s`. -/
theorem hcirc_self (s : ℝ) (j : Fin N) :
    dist ((Γ.isHermitian s).eigC j) (Γ.lam s : ℂ) ≠ Γ.g / 2 := by
  rw [Γ.dist_eigC]
  rcases Γ.gap s j with h | h
  · rw [h, sub_self, abs_zero]
    exact (half_pos Γ.g_pos).ne
  · intro h2
    linarith [Γ.g_pos]

/-- For `|lam s − lam s₀| < g/4`, the circle about `lam s₀` of radius `g/2` avoids the spectrum of
`H s` as well. -/
theorem hcirc_near {s s₀ : ℝ} (h : |Γ.lam s - Γ.lam s₀| < Γ.g / 4) (j : Fin N) :
    dist ((Γ.isHermitian s).eigC j) (Γ.lam s₀ : ℂ) ≠ Γ.g / 2 := by
  rw [Γ.dist_eigC]
  rcases Γ.gap s j with h1 | h1
  · rw [h1]
    intro h2
    linarith [Γ.g_pos]
  · intro h2
    have h3 := abs_sub_le ((Γ.isHermitian s).eigenvalues j) (Γ.lam s₀) (Γ.lam s)
    rw [abs_sub_comm (Γ.lam s₀) (Γ.lam s)] at h3
    linarith [Γ.g_pos]

/-- The indicator of the disc about `lam s` is the indicator of the branch. -/
theorem discInd_eq (s : ℝ) (j : Fin N) :
    (Γ.isHermitian s).discInd (Γ.lam s) (Γ.g / 2) j
      = if (Γ.isHermitian s).eigenvalues j = Γ.lam s then 1 else 0 := by
  unfold IsHermitian.discInd
  rw [Γ.dist_eigC]
  rcases Γ.gap s j with h | h
  · rw [h, sub_self, abs_zero]
    simp [half_pos Γ.g_pos]
  · have h1 : ¬ |(Γ.isHermitian s).eigenvalues j - Γ.lam s| < Γ.g / 2 := by
      intro h1
      linarith [Γ.g_pos]
    have h2 : (Γ.isHermitian s).eigenvalues j ≠ Γ.lam s := by
      intro h2
      rw [h2, sub_self, abs_zero] at h
      linarith [Γ.g_pos]
    simp only [h1, h2, ↓reduceIte]

/-- For `|lam s − lam s₀| < g/4`, the discs about `lam s` and `lam s₀` select the same
eigenvalues of `H s`. -/
theorem discInd_eq_near {s s₀ : ℝ} (h : |Γ.lam s - Γ.lam s₀| < Γ.g / 4) :
    (Γ.isHermitian s).discInd (Γ.lam s) (Γ.g / 2)
      = (Γ.isHermitian s).discInd (Γ.lam s₀) (Γ.g / 2) := by
  funext j
  rw [Γ.discInd_eq]
  unfold IsHermitian.discInd
  rw [Γ.dist_eigC]
  rcases Γ.gap s j with h1 | h1
  · rw [h1]
    have hlt : |Γ.lam s - Γ.lam s₀| < Γ.g / 2 := by linarith [Γ.g_pos]
    simp [hlt]
  · have h2 : (Γ.isHermitian s).eigenvalues j ≠ Γ.lam s := by
      intro h2
      rw [h2, sub_self, abs_zero] at h1
      linarith [Γ.g_pos]
    have h3 : ¬ |(Γ.isHermitian s).eigenvalues j - Γ.lam s₀| < Γ.g / 2 := by
      intro h3
      have h4 := abs_sub_le ((Γ.isHermitian s).eigenvalues j) (Γ.lam s₀) (Γ.lam s)
      rw [abs_sub_comm (Γ.lam s₀) (Γ.lam s)] at h4
      linarith [Γ.g_pos]
    simp only [h2, h3, ↓reduceIte]

/-- **The contour can be frozen locally**: for `|lam s − lam s₀| < g/4`, `proj s` is the Riesz
projector of `H s` over the fixed disc about `lam s₀`. -/
theorem proj_eq_near {s s₀ : ℝ} (h : |Γ.lam s - Γ.lam s₀| < Γ.g / 4) :
    Γ.proj s = rieszProj (Γ.H s) (Γ.lam s₀) (Γ.g / 2) := by
  unfold proj
  rw [(Γ.isHermitian s).rieszProj_eq_conjD (half_pos Γ.g_pos).le (Γ.hcirc_self s),
    (Γ.isHermitian s).rieszProj_eq_conjD (half_pos Γ.g_pos).le (Γ.hcirc_near h),
    Γ.discInd_eq_near h]

/-- Off the spectrum, `z • 1 − H s` is a unit. -/
theorem isUnit_smul_one_sub {s : ℝ} {z : ℂ} (hz : ∀ j, z ≠ (Γ.isHermitian s).eigC j) :
    IsUnit (z • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s) := by
  rw [isUnit_iff_isUnit_det]
  refine isUnit_det_of_left_inverse (B := (z • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s)⁻¹) ?_
  rw [(Γ.isHermitian s).inv_smul_one_sub_eq_conjD hz, (Γ.isHermitian s).smul_one_sub_eq_conjD,
    IsHermitian.conjD_mul_conjD]
  have : ((fun j => (z - (Γ.isHermitian s).eigC j)⁻¹) * fun j => z - (Γ.isHermitian s).eigC j)
      = 1 := by
    funext j
    exact inv_mul_cancel₀ (sub_ne_zero.2 (hz j))
  rw [this, IsHermitian.conjD_one]

/-- ★★ **The eigenprojector is `C^n` whenever the path is.** -/
theorem contDiff_proj {n : ℕ∞} (hH : ContDiff ℝ n Γ.H) : ContDiff ℝ n Γ.proj := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  set V : Set ℝ := {s | |Γ.lam s - Γ.lam s₀| < Γ.g / 4} with hV
  have hVo : IsOpen V :=
    isOpen_lt (continuous_abs.comp (Γ.continuous_lam.sub continuous_const)) continuous_const
  have hs₀ : s₀ ∈ V := by
    show |Γ.lam s₀ - Γ.lam s₀| < Γ.g / 4
    rw [sub_self, abs_zero]
    exact div_pos Γ.g_pos (by norm_num)
  have hsm : ContDiffOn ℝ n (fun s => rieszProj (Γ.H s) (Γ.lam s₀) (Γ.g / 2)) V :=
    contDiffOn_rieszProj hH hVo (half_pos Γ.g_pos).le fun s hs z hz =>
      Γ.isUnit_smul_one_sub ((Γ.isHermitian s).ne_eigC_of_mem_sphere (Γ.hcirc_near hs) hz)
  refine (hsm.contDiffAt (hVo.mem_nhds hs₀)).congr_of_eventuallyEq ?_
  filter_upwards [hVo.mem_nhds hs₀] with s hs
  exact Γ.proj_eq_near hs

/-! ### The algebra of the eigenprojector -/

theorem proj_mul_self (s : ℝ) : Γ.proj s * Γ.proj s = Γ.proj s :=
  (Γ.isHermitian s).rieszProj_mul_self (half_pos Γ.g_pos).le (Γ.hcirc_self s)

theorem proj_isHermitian (s : ℝ) : (Γ.proj s).IsHermitian :=
  (Γ.isHermitian s).rieszProj_isHermitian (half_pos Γ.g_pos).le (Γ.hcirc_self s)

/-- `H s · P s = lam s • P s`. -/
theorem H_mul_proj (s : ℝ) : Γ.H s * Γ.proj s = (Γ.lam s : ℂ) • Γ.proj s :=
  (Γ.isHermitian s).mul_rieszProj_eq_smul (half_pos Γ.g_pos).le (Γ.hcirc_self s) fun j hj => by
    rw [Γ.dist_eigC] at hj
    rcases Γ.gap s j with h | h
    · unfold IsHermitian.eigC
      rw [h]
      rfl
    · exfalso
      linarith [Γ.g_pos]

/-- `P s · H s = lam s • P s`. -/
theorem proj_mul_H (s : ℝ) : Γ.proj s * Γ.H s = (Γ.lam s : ℂ) • Γ.proj s := by
  unfold proj
  rw [← (Γ.isHermitian s).rieszProj_mul_comm (half_pos Γ.g_pos).le (Γ.hcirc_self s)]
  exact Γ.H_mul_proj s

/-- The eigenprojector has derivative `deriv Γ.proj s` at `s` once the path is `C¹`. -/
theorem hasDerivAt_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    HasDerivAt Γ.proj (deriv Γ.proj s) s := by
  have hn' : n ≠ 0 := by
    rintro rfl
    simp at hn
  exact ((Γ.contDiff_proj hH).differentiable (by exact_mod_cast hn') s).hasDerivAt

/-- `Ṗ = Ṗ P + P Ṗ` along a gapped `C¹` path. -/
theorem deriv_proj_eq {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    deriv Γ.proj s = deriv Γ.proj s * Γ.proj s + Γ.proj s * deriv Γ.proj s :=
  (Γ.hasDerivAt_proj hn hH s).eq_mul_add_mul_of_idempotent Γ.proj_mul_self

/-- ★ **`P Ṗ P = 0` along a gapped `C¹` path.** -/
theorem proj_mul_deriv_mul_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    Γ.proj s * deriv Γ.proj s * Γ.proj s = 0 :=
  (Γ.hasDerivAt_proj hn hH s).mul_deriv_mul_eq_zero_of_idempotent Γ.proj_mul_self

/-! ### The multiplicity is constant, and the branch is smooth -/

theorem _root_.Matrix.IsHermitian.trace_conjD {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (d : Fin N → ℂ) : (hH.conjD d).trace = ∑ j, d j := by
  unfold IsHermitian.conjD
  rw [trace_mul_comm, ← Matrix.mul_assoc, hH.star_eigU_mul_eigU, Matrix.one_mul, trace_diagonal]

/-- The trace of the eigenprojector is the multiplicity of the branch. -/
theorem trace_proj (s : ℝ) : (Γ.proj s).trace = (Γ.mult s : ℂ) := by
  classical
  unfold proj
  rw [(Γ.isHermitian s).rieszProj_eq_conjD (half_pos Γ.g_pos).le (Γ.hcirc_self s),
    (Γ.isHermitian s).trace_conjD]
  simp_rw [Γ.discInd_eq]
  rw [Finset.sum_boole]
  unfold mult
  rw [Fintype.card_subtype]

/-- Two naturals whose real casts are within `1` are equal. -/
theorem _root_.Nat.eq_of_dist_cast_lt_one {a b : ℕ} (h : dist (a : ℝ) (b : ℝ) < 1) : a = b := by
  rw [Real.dist_eq] at h
  have h1 := (abs_sub_lt_iff.1 h).1
  have h2 := (abs_sub_lt_iff.1 h).2
  have h3 : a < b + 1 := by exact_mod_cast (show (a : ℝ) < b + 1 by linarith)
  have h4 : b < a + 1 := by exact_mod_cast (show (b : ℝ) < a + 1 by linarith)
  omega

/-- ★ **The multiplicity of the branch is constant along the path.** -/
theorem mult_eq {n : ℕ∞} (hH : ContDiff ℝ n Γ.H) (s t : ℝ) : Γ.mult s = Γ.mult t := by
  have hc : Continuous fun s => (Γ.proj s).trace :=
    traceCLM.continuous.comp (Γ.contDiff_proj hH).continuous
  have hlc : IsLocallyConstant Γ.mult := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have h := Metric.tendsto_nhds.1 (hc.continuousAt (x := s)) 1 one_pos
    filter_upwards [h] with t ht
    rw [Γ.trace_proj, Γ.trace_proj] at ht
    refine Nat.eq_of_dist_cast_lt_one ?_
    have : dist ((Γ.mult t : ℕ) : ℂ) ((Γ.mult s : ℕ) : ℂ) = dist ((Γ.mult t : ℕ) : ℝ) ((Γ.mult s : ℕ) : ℝ) := by
      rw [Complex.dist_of_im_eq (by simp)]
      simp
    rw [this] at ht
    exact ht
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ s) (mem_univ t)

theorem mult_pos {s : ℝ} (hex : ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) : 0 < Γ.mult s :=
  Fintype.card_pos_iff.2 ⟨⟨hex.choose, hex.choose_spec⟩⟩

/-- `lam s = tr(H s · P s) / mult s` once the branch is an eigenvalue. -/
theorem ofReal_lam_eq {s : ℝ} (hex : ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    (Γ.lam s : ℂ) = (Γ.H s * Γ.proj s).trace / (Γ.mult s : ℂ) := by
  rw [Γ.H_mul_proj, trace_smul, Γ.trace_proj, smul_eq_mul, mul_div_assoc,
    div_self (Nat.cast_ne_zero.2 (Γ.mult_pos hex).ne'), mul_one]

/-- ★ **The eigenvalue branch is `C^n` whenever the path is**, provided it is an eigenvalue:
`lam s = tr(H s · P s) / mult`, with the multiplicity constant. -/
theorem contDiff_lam {n : ℕ∞} (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) : ContDiff ℝ n Γ.lam := by
  have h1 : ContDiff ℝ n fun s => (Γ.lam s : ℂ) := by
    have heq : (fun s => (Γ.lam s : ℂ)) = fun s => (Γ.H s * Γ.proj s).trace / (Γ.mult 0 : ℂ) := by
      funext s
      rw [Γ.ofReal_lam_eq (hex s), Γ.mult_eq hH s 0]
    rw [heq]
    exact (traceCLM.contDiff.comp (hH.mul (Γ.contDiff_proj hH))).div_const _
  have heq : Γ.lam = fun s => ((Γ.lam s : ℂ)).re := by
    funext s
    simp
  rw [heq]
  exact Complex.reCLM.contDiff.comp h1

end GappedPath

end Matrix

end

end
