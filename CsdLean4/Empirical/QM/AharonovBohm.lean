/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.AharonovBohmRing

/-!
# The Aharonov–Bohm effect, read as quantum mechanics

**Category:** 3-Local (QM-validity). BACKLOG #55, brick BP-4 of `specs/berry-phase-scoping.md`;
the flux twin `specs/qm-empirical-tests.md` ER3 asked for.

`Mathlib/QuantumInfo/AharonovBohmRing.lean` is the linear algebra: a ring of `N` sites with Peierls
phases, its levels `2 cos((2πm + Φ)/N)`, its diagonalisation by the discrete Fourier transform, and
its gauge covariance. This module reads those theorems as the experiment.

* ★★ `energy_lt_energy_of_flux_lt` — **the levels move with the flux**, strictly and continuously:
  a spectroscopic measurement on the ring sees `Φ`, although the field vanishes on every site the
  electron visits. That is the Aharonov–Bohm effect (Chambers 1960, Tonomura 1986 in the
  interference form).
* ★★ `oneBond_mulVec_gauge_mode` and ★★ `same_levels_of_gauge` — **the vector potential is not
  observable**: put the entire phase on one bond and the levels do not move, because the two rings
  are the same operator in two gauges.
* ★★ `flux_quantum` — the levels see `Φ` only modulo `2π`: flux is measured in units of the
  quantum, and `Φ` and `Φ + 2π` are indistinguishable by any measurement whatsoever.
* ★★★ `flux_not_gauge_artefact` — and yet `Φ = π` is not `Φ = 0`: no change of basis carries one
  three-site ring to the other. Both halves of the effect, in one file.
* The three-site levels as numbers: `levels_three_zero`, `levels_three_pi` — `{2, −1, −1}` at zero
  flux and `{1, −2, 1}` at half a quantum.

## Honest scope

⚠️ A lattice ring, not a solenoid: the flux enters through Peierls' substitution, which this model
takes as its definition, and "the field vanishes on the ring" is a statement about the model's
inputs, not a derived one. No double-slit, no interference pattern, no continuum limit
(`specs/berry-phase-scoping.md` BP-4).

⚠️ Nothing here is CSD-specific: the module records that the corpus reproduces the effect, which is
what the empirical-twin ledger asks of it.

References: Y. Aharonov, D. Bohm, Phys. Rev. 115 (1959) 485; R. G. Chambers, Phys. Rev. Lett. 5
(1960) 3; A. Tonomura et al., Phys. Rev. Lett. 56 (1986) 792; `specs/qm-empirical-tests.md` ER3;
`specs/berry-phase-scoping.md` BP-4; `specs/BACKLOG.md` #55.
-/

@[expose] public section

noncomputable section

open QuantumInfo.AharonovBohm
open scoped Real ComplexConjugate
open Matrix

namespace CSD
namespace Empirical
namespace QM
namespace AharonovBohm

/-! ### The levels move with the flux -/

/-- ★★ **The flux is observable, continuously.** On a ring of `N ≥ 3` sites the lowest level
`2 cos(Φ/N)` falls strictly as the flux grows through `[0, πN]`: a spectroscopic measurement reads
the flux off the ring, although the magnetic field vanishes at every site. -/
theorem energy_lt_energy_of_flux_lt {N : ℕ} (hN : 3 ≤ N) {Φ₁ Φ₂ : ℝ} (h0 : 0 ≤ Φ₁)
    (h12 : Φ₁ < Φ₂) (h2 : Φ₂ ≤ π * N) :
    ringEigval N Φ₂ 0 < ringEigval N Φ₁ 0 := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlt : Φ₁ / N < Φ₂ / N := by
    have hinv : 0 < 1 / (N : ℝ) := by positivity
    have hmul := mul_lt_mul_of_pos_right h12 hinv
    calc Φ₁ / N = Φ₁ * (1 / N) := by ring
      _ < Φ₂ * (1 / N) := hmul
      _ = Φ₂ / N := by ring
  have hle : Φ₂ / N ≤ π := by
    rw [div_le_iff₀ hNpos]
    linarith [h2]
  have hcos : Real.cos (Φ₂ / N) < Real.cos (Φ₁ / N) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) hle hlt
  rw [ringEigval, ringEigval]
  push_cast
  simp only [mul_zero, zero_add]
  linarith

/-! ### The vector potential is not observable -/

/-- ★★ **The gauge-transformed modes diagonalise the one-bond ring.** Moving the whole Peierls
phase onto a single bond moves the eigenvectors by a diagonal unitary and leaves every level where
it was. -/
theorem oneBond_mulVec_gauge_mode {N : ℕ} [NeZero N] (hN : 3 ≤ N) (Φ : ℝ) (m : ℤ) :
    ringHamOf N (oneBondPhase N Φ)
        *ᵥ ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N))
      = ((ringEigval N Φ m : ℝ) : ℂ)
        • ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N)) := by
  have hD : gaugeDiag N (oneBondGauge N Φ) * (gaugeDiag N (oneBondGauge N Φ))ᴴ = 1 :=
    mul_eq_one_comm.2 (gaugeDiag_conjTranspose_mul _)
  calc ringHamOf N (oneBondPhase N Φ)
        *ᵥ ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N))
      = ((gaugeDiag N (oneBondGauge N Φ))ᴴ * ringHam N Φ * gaugeDiag N (oneBondGauge N Φ))
          *ᵥ ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N)) := by
        rw [gaugeDiag_conj_ringHam_oneBond hN]
    _ = (gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ (ringHam N Φ *ᵥ (gaugeDiag N (oneBondGauge N Φ)
          *ᵥ ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N)))) :=
        mulVec_three _ _ _ _
    _ = (gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ (ringHam N Φ *ᵥ ringMode N (m : ZMod N)) := by
        rw [Matrix.mulVec_mulVec (ringMode N (m : ZMod N)) (gaugeDiag N (oneBondGauge N Φ))
          ((gaugeDiag N (oneBondGauge N Φ))ᴴ), hD, Matrix.one_mulVec]
    _ = (gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ (((ringEigval N Φ m : ℝ) : ℂ)
          • ringMode N (m : ZMod N)) := by rw [ringHam_mulVec_ringMode hN]
    _ = ((ringEigval N Φ m : ℝ) : ℂ)
          • ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N)) :=
        Matrix.mulVec_smul _ _ _

/-- ★★ **Redistributing the phase changes no level.** Every level of the uniform ring is a level of
the ring with the whole phase on one bond, and conversely by
`QuantumInfo.AharonovBohm.eq_ringEigval_of_mulVec`: the two gauges are spectroscopically
indistinguishable. -/
theorem same_levels_of_gauge {N : ℕ} [NeZero N] (hN : 3 ≤ N) (Φ : ℝ) (m : ℤ) :
    Module.End.HasEigenvalue (Matrix.mulVecLin (ringHamOf N (oneBondPhase N Φ)))
      ((ringEigval N Φ m : ℝ) : ℂ) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := (gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N)) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact oneBond_mulVec_gauge_mode hN Φ m
  · intro h0
    have hD : gaugeDiag N (oneBondGauge N Φ) * (gaugeDiag N (oneBondGauge N Φ))ᴴ = 1 :=
      mul_eq_one_comm.2 (gaugeDiag_conjTranspose_mul _)
    have h1 : gaugeDiag N (oneBondGauge N Φ)
        *ᵥ ((gaugeDiag N (oneBondGauge N Φ))ᴴ *ᵥ ringMode N (m : ZMod N)) = 0 := by
      rw [h0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, hD, Matrix.one_mulVec] at h1
    exact ringMode_ne_zero _ h1

/-! ### The flux quantum, and what survives it -/

/-- ★★ **A whole flux quantum is invisible.** The set of levels is unchanged by `Φ ↦ Φ + 2π`: no
measurement on the ring distinguishes fluxes differing by a quantum. -/
theorem flux_quantum (N : ℕ) (Φ : ℝ) :
    Set.range (ringEigval N (Φ + 2 * π)) = Set.range (ringEigval N Φ) :=
  range_ringEigval_add_two_pi Φ

/-- ★★★ **Half a quantum is visible.** No change of basis carries the flux-free three-site ring to
the ring with flux `π`: the Aharonov–Bohm phase is physical, not an artefact of the vector
potential's gauge. -/
theorem flux_not_gauge_artefact :
    ¬∃ U : Matrix (ZMod 3) (ZMod 3) ℂ, Uᴴ * U = 1 ∧ U * ringHam 3 0 * Uᴴ = ringHam 3 π :=
  not_exists_unitary_conj_ringHam

/-! ### The three-site ring, in numbers -/

/-- The level of the label `m` in terms of an explicitly simplified angle. -/
theorem ringEigval_eq_two_mul_cos {N : ℕ} {Φ : ℝ} {m : ℤ} {x : ℝ}
    (h : (2 * π * m + Φ) / N = x) : ringEigval N Φ m = 2 * Real.cos x := by
  rw [ringEigval, h]

theorem levels_three_zero :
    ringEigval 3 0 0 = 2 ∧ ringEigval 3 0 1 = -1 ∧ ringEigval 3 0 2 = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ringEigval_eq_two_mul_cos (x := 0) (by push_cast; ring), Real.cos_zero]
    norm_num
  · rw [ringEigval_eq_two_mul_cos (x := π - π / 3) (by push_cast; ring), Real.cos_sub,
      Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    ring
  · rw [ringEigval_eq_two_mul_cos (x := π + π / 3) (by push_cast; ring), Real.cos_add,
      Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    ring

theorem levels_three_pi :
    ringEigval 3 π 0 = 1 ∧ ringEigval 3 π 1 = -2 ∧ ringEigval 3 π 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ringEigval_eq_two_mul_cos (x := π / 3) (by push_cast; ring), Real.cos_pi_div_three]
    norm_num
  · rw [ringEigval_eq_two_mul_cos (x := π) (by push_cast; ring), Real.cos_pi]
    norm_num
  · rw [ringEigval_eq_two_mul_cos (x := 2 * π - π / 3) (by push_cast; ring), Real.cos_sub,
      Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_three]
    ring

end AharonovBohm
end QM
end Empirical
end CSD

end
