/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ArenaSymplectic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The torus stroke is not globally Hamiltonian on the arena: the flux obstruction

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the corpus's arena).

`R-016″` (`specs/BACKLOG.md` ▶ OPEN QUEUE #28). `LF4/ArenaSymplectic.lean` proved the rigid torus
stroke `(0, a)` *locally* Hamiltonian on the arena (`isLocallyHamiltonian_torusStrokeField`,
`d (ι_X ω) = 0`). This module proves the other half of the classification
`RecordLayer/PiecewiseHamiltonian.lean` records in the chart, now at manifold level:

* ★★ `not_isHamiltonianVectorField_torusStrokeField` — **for `a ≠ 0`, no function `H` on the arena
  has `(0, a)` as its Hamiltonian vector field for `arenaForm`.** So the stroke is symplectic and
  locally Hamiltonian but not Hamiltonian: the flux `∮ dθ ≠ 0` of the withdrawn "piecewise
  Hamiltonian" reading, as a theorem about the symplectic manifold rather than a remark about a
  chart.

The argument is the one the row recorded. If `ι_{(0,a)} ω = dH`, then along every torus direction
`b` the derivative of `H` is the constant `area a b` (`mfderiv_apply_torus_of_isHamiltonianVectorField`):
`H` is then differentiable everywhere (else its derivative would be zero, and `a ≠ 0` gives a `b`
with `area a b ≠ 0`), and along the closed curve `s ↦ (x, (θ₁ + s b₁, θ₂ + s b₂))` for `s ∈ [0, 1]`
with `b = (1, 0)` or `(0, 1)` the energy `H` has constant derivative `area a b`
(`hasDerivAt_energy_torusCurve`), so it changes by `area a b` over the period
(`energy_torusCurve_one_sub_zero`) while the curve returns to its start (`torusCurve_one_eq_zero`).
Hence `−a₂ = 0` and `a₁ = 0`.

* `torusCurve x t₁ t₂ b` — the curve; `hasMFDerivAt_torusCurve` — its manifold derivative is
  `(0, b)`, from `AddCircle.hasMFDerivAt_coe_comp` on each circle factor and the self-model
  pairing lemma;
* `arenaForm_torus_pair` — `arenaForm p ![(0, a), (0, b)] = area a b`.

## Honest scope

⚠️ **`H` is any function.** `IsHamiltonianVectorField` quantifies over all `H : M → ℝ` with
`mfderiv` as the derivative (junk `0` where `H` is not differentiable), so the theorem excludes
non-smooth generators too; differentiability of `H` is *derived* from the equation.

⚠️ **Period `1` only**, the corpus's torus. The curve's return uses `AddCircle.coe_add_period` at
`T = 1`; the argument is the same for any period, restated.

References: `LF4/ArenaSymplectic.lean` (the arena, `torusStrokeField`,
`isLocallyHamiltonian_torusStrokeField`); `RecordLayer/PiecewiseHamiltonian.lean` (the chart-level
flux correction this module lifts); `Geometry/Manifold/TranslationAtlasForm.lean`
(`AddCircle.hasMFDerivAt_coe_comp`); `Geometry/Manifold/HamiltonianVectorField.lean`
(`IsHamiltonianVectorField`); `specs/BACKLOG.md` (#28); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Projectivization DifferentialForm Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The form on two torus vectors, and the derivative of `H` in a torus direction -/

/-- The arena form on two torus vectors is the area form of their torus parts. -/
theorem arenaForm_torus_pair (N : ℕ) (p : KSigma (N + 1)) (a b : ℝ × ℝ) :
    arenaForm N p ![(((0 : Fin N → ℂ), a) : ArenaModel N), (((0 : Fin N → ℂ), b) : ArenaModel N)]
      = TorusForm.area a b := by
  have key : ContinuousAlternatingMap.prodSum (toFlat (fsForm (n := N) p.1)) TorusForm.areaForm
      ![(((0 : Fin N → ℂ), a) : ArenaModel N), (((0 : Fin N → ℂ), b) : ArenaModel N)]
      = TorusForm.area a b := by
    rw [ContinuousAlternatingMap.prodSum_pair]
    have h0 : toFlat (fsForm (n := N) p.1) ![(((0 : Fin N → ℂ), a) : ArenaModel N).1,
        (((0 : Fin N → ℂ), b) : ArenaModel N).1] = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 0 rfl
    rw [h0, zero_add, TorusForm.areaForm_apply]
    rfl
  exact key

/-- Under `ι_{(0,a)} ω = dH`, the derivative of `H` in the torus direction `b` is `area a b`, at
every point. -/
theorem mfderiv_apply_torus_of_isHamiltonianVectorField {a : ℝ × ℝ} {H : KSigma (N + 1) → ℝ}
    (hH : IsHamiltonianVectorField (fun p => arenaForm N p) (torusStrokeField N a) H)
    (p : KSigma (N + 1)) (b : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p
        ((((0 : Fin N → ℂ), b) : ArenaModel N) : TangentSpace 𝓘(ℝ, ArenaModel N) p)
      = TorusForm.area a b :=
  (hH p ((((0 : Fin N → ℂ), b) : ArenaModel N) : TangentSpace 𝓘(ℝ, ArenaModel N) p)).symm.trans
    (arenaForm_torus_pair N p a b)

/-- A torus direction along which the area pairing with a nonzero `a` is nonzero. -/
theorem area_self_rot_pos {a : ℝ × ℝ} (ha : a ≠ 0) : 0 < TorusForm.area a (-a.2, a.1) := by
  have h : TorusForm.area a (-a.2, a.1) = a.1 * a.1 + a.2 * a.2 := by
    simp only [TorusForm.area]; ring
  rw [h]
  have hne : ¬ (a.1 = 0 ∧ a.2 = 0) := fun h' => ha (Prod.ext h'.1 h'.2)
  rcases not_and_or.1 hne with h1 | h2
  · exact add_pos_of_pos_of_nonneg (mul_self_pos.2 h1) (mul_self_nonneg _)
  · exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 h2)

/-- Under `ι_{(0,a)} ω = dH` with `a ≠ 0`, `H` is differentiable everywhere: a non-differentiable
point would have zero derivative, but the derivative in the direction `(−a₂, a₁)` is `|a|² ≠ 0`. -/
theorem mdifferentiableAt_of_isHamiltonianVectorField_torusStrokeField {a : ℝ × ℝ} (ha : a ≠ 0)
    {H : KSigma (N + 1) → ℝ}
    (hH : IsHamiltonianVectorField (fun p => arenaForm N p) (torusStrokeField N a) H)
    (p : KSigma (N + 1)) : MDifferentiableAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p := by
  by_contra hnd
  have h0 := mfderiv_zero_of_not_mdifferentiableAt hnd
  have h1 := mfderiv_apply_torus_of_isHamiltonianVectorField hH p (-a.2, a.1)
  rw [h0] at h1
  exact (area_self_rot_pos ha).ne h1

/-! ### The transverse curve -/

/-- The curve `s ↦ (x, (t₁ + s b₁, t₂ + s b₂))` on the arena: the base point fixed, the torus
point moving linearly in the direction `b`. -/
def torusCurve (N : ℕ) (x : CPN (N + 1)) (t₁ t₂ : ℝ) (b : ℝ × ℝ) (s : ℝ) : KSigma (N + 1) :=
  (x, (((t₁ + s * b.1 : ℝ) : AddCircle (1 : ℝ)), ((t₂ + s * b.2 : ℝ) : AddCircle (1 : ℝ))))

/-- The curve in the direction `(1, 0)` or `(0, 1)` returns to its start after time `1`: the
moving coordinate advances by the period. -/
theorem torusCurve_one_eq_zero (x : CPN (N + 1)) (t₁ t₂ : ℝ) {b : ℝ × ℝ}
    (hb : b = (1, 0) ∨ b = (0, 1)) : torusCurve N x t₁ t₂ b 1 = torusCurve N x t₁ t₂ b 0 := by
  rcases hb with rfl | rfl <;>
    simp only [torusCurve, mul_zero, mul_one, add_zero, AddCircle.coe_add_period]

/-- The manifold derivative of the curve is `(0, b)`. -/
theorem hasMFDerivAt_torusCurve (x : CPN (N + 1)) (t₁ t₂ : ℝ) (b : ℝ × ℝ) (s : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ArenaModel N) (torusCurve N x t₁ t₂ b) s
      (ContinuousLinearMap.smulRight
        (M₂ := TangentSpace 𝓘(ℝ, ArenaModel N) (torusCurve N x t₁ t₂ b s))
        (1 : ℝ →L[ℝ] ℝ) (((0 : Fin N → ℂ), b) : ArenaModel N)) := by
  have h1 : HasDerivAt (fun u : ℝ => t₁ + u * b.1) b.1 s := by
    simpa using ((hasDerivAt_id s).mul_const b.1).const_add t₁
  have h2 : HasDerivAt (fun u : ℝ => t₂ + u * b.2) b.2 s := by
    simpa using ((hasDerivAt_id s).mul_const b.2).const_add t₂
  have hc :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Fin N → ℂ)) x s).prodMk_self
      ((AddCircle.hasMFDerivAt_coe_comp (T := 1) h1).prodMk_self
        (AddCircle.hasMFDerivAt_coe_comp (T := 1) h2))
  refine hc.congr_deriv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (0 : Fin N → ℂ) = ((1 : ℝ →L[ℝ] ℝ) u) • (0 : Fin N → ℂ)
    exact (smul_zero ((1 : ℝ →L[ℝ] ℝ) u)).symm
  · rfl
  · rfl

/-! ### The energy along the curve, and the obstruction -/

/-- Under `ι_{(0,a)} ω = dH` with `a ≠ 0`, the energy along the curve has constant derivative
`area a b`. -/
theorem hasDerivAt_energy_torusCurve {a : ℝ × ℝ} (ha : a ≠ 0) {H : KSigma (N + 1) → ℝ}
    (hH : IsHamiltonianVectorField (fun p => arenaForm N p) (torusStrokeField N a) H)
    (x : CPN (N + 1)) (t₁ t₂ : ℝ) (b : ℝ × ℝ) (s : ℝ) :
    HasDerivAt (fun s => H (torusCurve N x t₁ t₂ b s)) (TorusForm.area a b) s := by
  have hHc := (mdifferentiableAt_of_isHamiltonianVectorField_torusStrokeField ha hH
    (torusCurve N x t₁ t₂ b s)).hasMFDerivAt
  have h := hHc.comp s (hasMFDerivAt_torusCurve x t₁ t₂ b s)
  have h' : HasFDerivAt (fun s => H (torusCurve N x t₁ t₂ b s))
      ((mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H (torusCurve N x t₁ t₂ b s)).comp
        (ContinuousLinearMap.smulRight
          (M₂ := TangentSpace 𝓘(ℝ, ArenaModel N) (torusCurve N x t₁ t₂ b s))
          (1 : ℝ →L[ℝ] ℝ) (((0 : Fin N → ℂ), b) : ArenaModel N))) s :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  rw [hasDerivAt_iff_hasFDerivAt]
  refine h'.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  set p := torusCurve N x t₁ t₂ b s
  set v : TangentSpace 𝓘(ℝ, ArenaModel N) p := (((0 : Fin N → ℂ), b) : ArenaModel N)
  have hm : mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p ((u : ℝ) • v)
      = (u : ℝ) • mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p v :=
    (mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p).map_smul (u : ℝ) v
  show mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p ((u : ℝ) • v) = (u : ℝ) • TorusForm.area a b
  rw [hm, mfderiv_apply_torus_of_isHamiltonianVectorField hH p b]
  rfl

/-- Under `ι_{(0,a)} ω = dH` with `a ≠ 0`, the energy changes by exactly `area a b` over one unit
of the curve's parameter. -/
theorem energy_torusCurve_one_sub_zero {a : ℝ × ℝ} (ha : a ≠ 0) {H : KSigma (N + 1) → ℝ}
    (hH : IsHamiltonianVectorField (fun p => arenaForm N p) (torusStrokeField N a) H)
    (x : CPN (N + 1)) (t₁ t₂ : ℝ) (b : ℝ × ℝ) :
    H (torusCurve N x t₁ t₂ b 1) - H (torusCurve N x t₁ t₂ b 0) = TorusForm.area a b := by
  set G : ℝ → ℝ := fun s => H (torusCurve N x t₁ t₂ b s) - TorusForm.area a b * s with hG
  have hGd : ∀ s, HasDerivAt G 0 s := fun s => by
    have h := (hasDerivAt_energy_torusCurve ha hH x t₁ t₂ b s).sub
      ((hasDerivAt_id s).const_mul (TorusForm.area a b))
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [hG]
  have hconst := constant_of_has_deriv_right_zero (f := G) (a := 0) (b := 1)
    (fun s _ => (hGd s).continuousAt.continuousWithinAt)
    (fun s _ => (hGd s).hasDerivWithinAt) 1 ⟨zero_le_one, le_refl _⟩
  simp only [hG, mul_one, mul_zero, sub_zero] at hconst
  linarith

/-- ★★ **The torus stroke is not Hamiltonian on the arena.** For `a ≠ 0`, no function
`H : KSigma (N+1) → ℝ` satisfies `ι_{(0,a)} arenaForm = dH`: along the closed curves in the
directions `(1, 0)` and `(0, 1)` such an `H` would change by `−a₂` and by `a₁`, and it returns to
its value. Together with `isLocallyHamiltonian_torusStrokeField`, the classification
"symplectic, locally Hamiltonian, not Hamiltonian" of the strokes, at manifold level. -/
theorem not_isHamiltonianVectorField_torusStrokeField {a : ℝ × ℝ} (ha : a ≠ 0)
    (H : KSigma (N + 1) → ℝ) :
    ¬ IsHamiltonianVectorField (fun p => arenaForm N p) (torusStrokeField N a) H := by
  intro hH
  obtain ⟨x⟩ : Nonempty (CPN (N + 1)) := inferInstance
  have h10 := energy_torusCurve_one_sub_zero ha hH x 0 0 (1, 0)
  have h01 := energy_torusCurve_one_sub_zero ha hH x 0 0 (0, 1)
  rw [torusCurve_one_eq_zero x 0 0 (Or.inl rfl), sub_self] at h10
  rw [torusCurve_one_eq_zero x 0 0 (Or.inr rfl), sub_self] at h01
  simp only [TorusForm.area, mul_one, mul_zero, zero_sub, sub_zero] at h10 h01
  exact ha (Prod.ext h01.symm (neg_eq_zero.1 h10.symm))

end LF4
end CSD

end
