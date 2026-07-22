/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.SternGerlach
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Empirical: Malus's law (spin-1/2 Born probability)

**Category:** 3-Local. QM-validity layer (pure inner-product geometry, no CSD
ontology). The QM-side companion to `Empirical/CSD/MalusVolume.lean`: the same
`cos²(θ/2)` value, here as a textbook Born identity rather than a derived
Fubini-Study volume.

## What this file proves

For a spin-1/2 prepared in the `+`-eigenstate of spin along the polar angle `θ`,
`ψ_θ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩`, and measured along `+z`:

```
P(+_z | θ) = |⟨0|ψ_θ⟩|² = cos²(θ/2)        (Malus's law)
P(−_z | θ) = |⟨1|ψ_θ⟩|² = sin²(θ/2)
```

plus the basis-completeness identity `cos²(θ/2) + sin²(θ/2) = 1`.

Malus's law subsumes the two Stern-Gerlach values:

- `θ = 0`    ⟹  `cos²(0) = 1`     (`P(+_z | +_z) = 1`, `born_zPlus_zPlus`);
- `θ = π/2`  ⟹  `cos²(π/4) = 1/2`  (the canonical 50/50 split, `born_xPlus_zPlus`).

The angular law `cos²(θ/2)` is the spin-1/2 analogue of the classical optical
Malus law `I = I₀ cos²θ` (Malus 1809); the half-angle reflects the spin-1/2
double cover. It reuses the Stern-Gerlach `bornProb` (the doubly-normalised
`|⟨state|prep⟩|²`), so the result is invariant under (un)normalisation.

## Source

- Malus 1809 (optical, classical analogue).
- The spin-1/2 `cos²(θ/2)` form: standard QM (Sakurai, *Modern QM*; the
  rotated-spin projection probability).
-/

@[expose] public section

open CSD.Empirical.SternGerlach

namespace CSD
namespace Empirical
namespace Malus

/-! ### The θ-rotated spin state -/

/-- The spin-`θ` `+`-eigenstate `ψ_θ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩` (in the
unnormalised `Fin 2 → ℂ` convention; it is in fact a unit vector). -/
noncomputable def malus (θ : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos (θ / 2) : ℂ), (Real.sin (θ / 2) : ℂ)]

@[simp] lemma normSq_malus (θ : ℝ) : normSq (malus θ) = 1 := by
  unfold normSq malus
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  exact Real.cos_sq_add_sin_sq (θ / 2)

/-! ### Malus's law -/

/-- **Malus's law `P(+_z | θ) = cos²(θ/2)`.** The Born probability that a spin
prepared at polar angle `θ` is measured `+` along `z`. -/
theorem malus_law (θ : ℝ) : bornProb zPlus (malus θ) = Real.cos (θ / 2) ^ 2 := by
  have hinner : innerProd zPlus (malus θ) = (Real.cos (θ / 2) : ℂ) := by
    simp [innerProd, zPlus, malus, Fin.sum_univ_two]
  unfold bornProb
  rw [hinner, normSq_malus, normSq_zPlus, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num

/-- **Complementary outcome `P(−_z | θ) = sin²(θ/2)`.** -/
theorem malus_law_complement (θ : ℝ) :
    bornProb zMinus (malus θ) = Real.sin (θ / 2) ^ 2 := by
  have hinner : innerProd zMinus (malus θ) = (Real.sin (θ / 2) : ℂ) := by
    simp [innerProd, zMinus, malus, Fin.sum_univ_two]
  unfold bornProb
  rw [hinner, normSq_malus, normSq_zMinus, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num

/-- **Basis completeness:** the two `z`-outcome probabilities sum to 1. -/
theorem malus_basis_complete (θ : ℝ) :
    bornProb zPlus (malus θ) + bornProb zMinus (malus θ) = 1 := by
  rw [malus_law, malus_law_complement, Real.cos_sq_add_sin_sq]

/-! ### Recovery of the Stern-Gerlach values -/

/-- `θ = 0` recovers `P(+_z | +_z) = 1`: at zero angle the prep is `|0⟩`. -/
theorem malus_zero : bornProb zPlus (malus 0) = 1 := by
  rw [malus_law]; norm_num

/-- `θ = π/2` recovers the canonical 50/50 split `P = 1/2`. -/
theorem malus_pi_div_two : bornProb zPlus (malus (Real.pi / 2)) = 1 / 2 := by
  rw [malus_law, show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four,
    div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end Malus
end Empirical
end CSD
