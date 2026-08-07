/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Incubator.QuantumChaos.FloquetInterface

/-!
# Chaos diagnostics: the Loschmidt echo (quantum-chaos workstream, §H)

**Category:** Special (incubator — CSD-free; `upstream-candidate(physlib)`).

The first chaos diagnostic behind the interface (class 3 of the map's rule:
verified missing in Physlib 2026-08-07): the **Loschmidt echo**

  `L(n) = ‖⟨ψ, (F₂ⁿ)⁻¹ F₁ⁿ ψ⟩‖² = ‖⟨F₂ⁿ ψ, F₁ⁿ ψ⟩‖²`,

the fidelity between evolving `ψ` for `n` periods under `F₁` versus under a
perturbed drive `F₂`. Sensitivity of `L(n)` to the perturbation is the
standard dynamical-instability diagnostic.

The CSD reading, fixed by the interface's information-preservation lemmas:
BOTH evolutions preserve every global overlap exactly
(`inner_iterate_iterate`), so echo decay never signals information loss — it
measures the *divergence of two informationally lossless evolutions*, i.e.
where the preserved information has been relocated. That is scrambling as
relocation, the reading the ontic layer makes literal (records and
accessibility live in `Empirical/CSD/QuantumChaos/`).

API: `loschmidtEcho`, endpoint values (`loschmidtEcho_zero`,
`loschmidtEcho_self`), the unit-interval bounds (`loschmidtEcho_nonneg`,
`loschmidtEcho_le_one` via Cauchy–Schwarz + isometry), and symmetry
(`loschmidtEcho_comm`).
-/

@[expose] public section

namespace QuantumChaos

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Loschmidt echo**: the fidelity after `n` periods between the drive
`F₁` and the perturbed drive `F₂`, from the state `ψ`. -/
noncomputable def loschmidtEcho (F₁ F₂ : FloquetEvolution H) (ψ : H) (n : ℕ) :
    ℝ :=
  ‖(inner ℂ (F₂.iterate n ψ) (F₁.iterate n ψ) : ℂ)‖ ^ 2

/-- At `n = 0` the echo is the squared norm (`= 1` on unit states). -/
@[simp] lemma loschmidtEcho_zero (F₁ F₂ : FloquetEvolution H) {ψ : H}
    (hψ : ‖ψ‖ = 1) : loschmidtEcho F₁ F₂ ψ 0 = 1 := by
  simp [loschmidtEcho, hψ]

/-- The unperturbed echo is `1` at every period count: evolving twice the
same way never decays. -/
@[simp] lemma loschmidtEcho_self (F : FloquetEvolution H) {ψ : H}
    (hψ : ‖ψ‖ = 1) (n : ℕ) : loschmidtEcho F F ψ n = 1 := by
  simp [loschmidtEcho, F.norm_iterate_apply, hψ]

/-- The echo is nonnegative. -/
lemma loschmidtEcho_nonneg (F₁ F₂ : FloquetEvolution H) (ψ : H) (n : ℕ) :
    0 ≤ loschmidtEcho F₁ F₂ ψ n :=
  sq_nonneg _

/-- The echo is at most `1` on unit states: Cauchy–Schwarz, with both
evolutions norm-preserving. -/
lemma loschmidtEcho_le_one (F₁ F₂ : FloquetEvolution H) {ψ : H}
    (hψ : ‖ψ‖ = 1) (n : ℕ) : loschmidtEcho F₁ F₂ ψ n ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (F₂.iterate n ψ) (F₁.iterate n ψ)
  rw [F₁.norm_iterate_apply, F₂.norm_iterate_apply, hψ, mul_one] at h
  calc loschmidtEcho F₁ F₂ ψ n
      ≤ (1 : ℝ) ^ 2 := by
        rw [loschmidtEcho]
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 1 := one_pow 2

/-- The echo is symmetric in the two drives (conjugate-symmetry of the
inner product). -/
lemma loschmidtEcho_comm (F₁ F₂ : FloquetEvolution H) (ψ : H) (n : ℕ) :
    loschmidtEcho F₁ F₂ ψ n = loschmidtEcho F₂ F₁ ψ n := by
  rw [loschmidtEcho, loschmidtEcho, ← inner_conj_symm]
  rw [RCLike.norm_conj]

end QuantumChaos
