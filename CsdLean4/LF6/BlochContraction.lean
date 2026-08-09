/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.DephasingSemigroup
public import CsdLean4.LF6.AmplitudeDamping

/-!
# LF6-3/LF6-4: Bloch-volume contraction — the open-system drift, measured

**Category:** LF6 (open-system / de-isolation dynamics).

The geometric signature that separates open from closed dynamics, on the two
proved qubit dissipators. Closed (unitary) dynamics preserves state-space
volume — the corpus carries that side as `schrodinger_flow_kahler_symplectomorphism`
and `fubiniStudyMeasure_smul_invariant`. This module proves the open side:
**both canonical dissipators contract Bloch volume, at exactly the same
rate `e^{-2γt}`, and the drift rate is the measurable decoherence rate.**

* `blochX/Y/Z` — Bloch coordinates of a `2×2` matrix (no positivity or
  normalisation assumed; for a density matrix they are the standard Bloch
  vector).
* The channel actions in Bloch form: dephasing shrinks the equatorial
  plane and fixes the axis (`blochX/Y/Z_dephasing`); damping shrinks the
  equator at half rate and drifts the axis toward the ground pole
  (`blochX/Y/Z_damping` — the `z`-action is affine, with offset weighted by
  the trace).
* `blochLinearDephasing` / `blochLinearDamping` — the linear parts, with
  `blochVec_dephasing` / `blochVec_damping` proving they ARE the actions
  (damping up to the trace-weighted pole offset).
* ★★ `det_blochLinearDephasing` / `det_blochLinearDamping` — **the
  volume-drift law**: both determinants equal `e^{-2γt}`. T2 dephasing
  (equator² × 1) and T1 damping (equator × axis, `e^{-γt/2}·e^{-γt/2}·e^{-γt}`)
  contract the Bloch ball's volume by the SAME factor — the marginal
  volume drift is a dissipation invariant, blind to how the contraction is
  distributed over axes (LF6-3).
* ★ Metrology A4 (LF6-4): `bloch_volume_closed` (`γ·t = 0` ⟹ volume factor
  `1` — the closed case is drift-free), `bloch_volume_lt_one` (any `γt > 0`
  is detected), `bloch_volume_decay_rate` (the initial drift rate is
  exactly `-2γ`), and `volume_drift_determines_rate` (one drift sample at
  any `t > 0` identifies `γ`). **Decoherence is not merely modelled: its
  rate is an observable of the volume drift.**

Honest scope: the two exhibited dissipators only — the general-generator
form of the volume-drift law waits on LF6-9's exponential-CP residual
(Mathlib-scale, recorded there); the closed-side volume preservation is
cited from the pure-state Kähler results, not re-proved at the density
level. Cross-references: `LF6/LindbladGenerator.lean` (both channels are
GKSL), `LF5/` (the reduced-state framing), `specs/future-work.md` rows
LF6-3/LF6-4.
-/

@[expose] public section

open Matrix

namespace CSD
namespace LF6

/-! ### Bloch coordinates -/

/-- Bloch `x`: the real part of the coherence sum. -/
noncomputable def blochX (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (ρ 0 1 + ρ 1 0).re

/-- Bloch `y`: the rotated coherence difference. -/
noncomputable def blochY (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Complex.I * (ρ 0 1 - ρ 1 0)).re

/-- Bloch `z`: the population difference. -/
noncomputable def blochZ (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (ρ 0 0 - ρ 1 1).re

/-- The Bloch vector. -/
noncomputable def blochVec (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![blochX ρ, blochY ρ, blochZ ρ]

/-! ### The channel actions in Bloch form -/

lemma blochX_dephasing (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochX (dephasingChannel γ t ρ) = Real.exp (-(γ * t)) * blochX ρ := by
  rw [blochX, blochX, dephasingChannel_apply_01, dephasingChannel_apply_10,
    ← mul_add, Complex.re_ofReal_mul]

lemma blochY_dephasing (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochY (dephasingChannel γ t ρ) = Real.exp (-(γ * t)) * blochY ρ := by
  rw [blochY, blochY, dephasingChannel_apply_01, dephasingChannel_apply_10]
  rw [show Complex.I * ((Real.exp (-(γ * t)) : ℂ) * ρ 0 1
      - (Real.exp (-(γ * t)) : ℂ) * ρ 1 0)
    = (Real.exp (-(γ * t)) : ℂ) * (Complex.I * (ρ 0 1 - ρ 1 0)) from by ring,
    Complex.re_ofReal_mul]

lemma blochZ_dephasing (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochZ (dephasingChannel γ t ρ) = blochZ ρ := by
  rw [blochZ, blochZ, dephasingChannel_apply_00, dephasingChannel_apply_11]

lemma blochX_damping (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochX (dampingChannel γ t ρ) = Real.exp (-(γ * t) / 2) * blochX ρ := by
  rw [blochX, blochX, dampingChannel_apply_01, dampingChannel_apply_10,
    ← mul_add, Complex.re_ofReal_mul]

lemma blochY_damping (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochY (dampingChannel γ t ρ) = Real.exp (-(γ * t) / 2) * blochY ρ := by
  rw [blochY, blochY, dampingChannel_apply_01, dampingChannel_apply_10]
  rw [show Complex.I * ((Real.exp (-(γ * t) / 2) : ℂ) * ρ 0 1
      - (Real.exp (-(γ * t) / 2) : ℂ) * ρ 1 0)
    = (Real.exp (-(γ * t) / 2) : ℂ) * (Complex.I * (ρ 0 1 - ρ 1 0)) from by
      ring,
    Complex.re_ofReal_mul]

/-- The damping `z`-action is affine: contraction toward the ground pole,
with the offset weighted by the trace. -/
lemma blochZ_damping (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochZ (dampingChannel γ t ρ)
      = Real.exp (-(γ * t)) * blochZ ρ
        + (1 - Real.exp (-(γ * t))) * ρ.trace.re := by
  rw [blochZ, blochZ, dampingChannel_apply_00, dampingChannel_apply_11,
    show ρ.trace = ρ 0 0 + ρ 1 1 from by
      rw [Matrix.trace, Fin.sum_univ_two]; rfl]
  rw [show ρ 0 0 + (1 - (Real.exp (-(γ * t)) : ℂ)) * ρ 1 1
      - (Real.exp (-(γ * t)) : ℂ) * ρ 1 1
    = (Real.exp (-(γ * t)) : ℂ) * (ρ 0 0 - ρ 1 1)
      + (1 - (Real.exp (-(γ * t)) : ℂ)) * (ρ 0 0 + ρ 1 1) from by ring]
  rw [Complex.add_re, Complex.re_ofReal_mul]
  congr 1
  rw [show ((1 : ℂ) - (Real.exp (-(γ * t)) : ℂ))
      = ((1 - Real.exp (-(γ * t)) : ℝ) : ℂ) from by push_cast; ring,
    Complex.re_ofReal_mul]

/-! ### The linear parts and the volume-drift law -/

/-- The dephasing Bloch superoperator: equatorial contraction, axis
fixed. -/
noncomputable def blochLinearDephasing (γ t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![Real.exp (-(γ * t)), Real.exp (-(γ * t)), 1]

/-- The damping Bloch superoperator (linear part): equatorial contraction
at half rate, axis contraction at full rate. -/
noncomputable def blochLinearDamping (γ t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal
    ![Real.exp (-(γ * t) / 2), Real.exp (-(γ * t) / 2), Real.exp (-(γ * t))]

/-- The dephasing Bloch action IS the linear map. -/
theorem blochVec_dephasing (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochVec (dephasingChannel γ t ρ)
      = blochLinearDephasing γ t *ᵥ blochVec ρ := by
  funext i
  fin_cases i <;>
    simp [blochVec, blochLinearDephasing, Matrix.mulVec_diagonal,
      blochX_dephasing, blochY_dephasing, blochZ_dephasing]

/-- The damping Bloch action is the linear map plus the trace-weighted
pole offset. -/
theorem blochVec_damping (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    blochVec (dampingChannel γ t ρ)
      = blochLinearDamping γ t *ᵥ blochVec ρ
        + ((1 - Real.exp (-(γ * t))) * ρ.trace.re) • ![0, 0, 1] := by
  funext i
  fin_cases i <;>
    simp [blochVec, blochLinearDamping, Matrix.mulVec_diagonal,
      blochX_damping, blochY_damping, blochZ_damping]

/-- ★★ **The dephasing volume-drift law**: T2 contracts Bloch volume by
exactly `e^{-2γt}` (equator² × fixed axis). -/
theorem det_blochLinearDephasing (γ t : ℝ) :
    (blochLinearDephasing γ t).det = Real.exp (-(2 * γ * t)) := by
  rw [blochLinearDephasing, Matrix.det_diagonal, Fin.prod_univ_three]
  show Real.exp (-(γ * t)) * Real.exp (-(γ * t)) * 1 = _
  rw [mul_one, ← Real.exp_add]
  ring_nf

/-- ★★ **The damping volume-drift law**: T1 contracts Bloch volume by
exactly the SAME `e^{-2γt}` (half-rate equator × full-rate axis) — the
volume drift is a dissipation invariant, blind to how the contraction is
distributed over axes. -/
theorem det_blochLinearDamping (γ t : ℝ) :
    (blochLinearDamping γ t).det = Real.exp (-(2 * γ * t)) := by
  rw [blochLinearDamping, Matrix.det_diagonal, Fin.prod_univ_three]
  show Real.exp (-(γ * t) / 2) * Real.exp (-(γ * t) / 2)
      * Real.exp (-(γ * t)) = _
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf

/-! ### Metrology A4: the drift is the observable (LF6-4) -/

/-- The closed case is drift-free: at `γ·t = 0` the volume factor is `1`. -/
theorem bloch_volume_closed {γ t : ℝ} (h : γ * t = 0) :
    (blochLinearDephasing γ t).det = 1 := by
  rw [det_blochLinearDephasing,
    show -(2 * γ * t) = -(2 * (γ * t)) from by ring, h]
  simp

/-- ★ **Openness is detected**: any `γ·t > 0` strictly contracts the
volume. -/
theorem bloch_volume_lt_one {γ t : ℝ} (h : 0 < γ * t) :
    (blochLinearDephasing γ t).det < 1 := by
  rw [det_blochLinearDephasing]
  have : -(2 * γ * t) < 0 := by nlinarith
  calc Real.exp (-(2 * γ * t)) < Real.exp 0 := Real.exp_lt_exp.mpr this
    _ = 1 := Real.exp_zero

/-- ★ **The initial drift rate is the decoherence rate**: the volume
factor's derivative at `t = 0` is exactly `-2γ` — measuring the drift
measures `γ`. -/
theorem bloch_volume_decay_rate (γ : ℝ) :
    HasDerivAt (fun t => (blochLinearDephasing γ t).det) (-(2 * γ)) 0 := by
  have h : (fun t => (blochLinearDephasing γ t).det)
      = fun t => Real.exp ((-(2 * γ)) * t) := by
    funext t
    rw [det_blochLinearDephasing]
    congr 1
    ring
  rw [h]
  have hlin : HasDerivAt (fun t : ℝ => (-(2 * γ)) * t) (-(2 * γ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(2 * γ))
  simpa using hlin.exp

/-- ★ **One drift sample identifies the rate**: equal volume factors at
any single `t > 0` force equal `γ` — the drift is a faithful observable
of the decoherence rate. -/
theorem volume_drift_determines_rate {γ₁ γ₂ t : ℝ} (ht : 0 < t)
    (h : (blochLinearDephasing γ₁ t).det = (blochLinearDephasing γ₂ t).det) :
    γ₁ = γ₂ := by
  rw [det_blochLinearDephasing, det_blochLinearDephasing] at h
  have := Real.exp_injective h
  have h2 : 2 * γ₁ * t = 2 * γ₂ * t := by linarith
  have := mul_right_cancel₀ (ne_of_gt ht) h2
  linarith

end LF6
end CSD
