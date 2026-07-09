/-
Copyright (c) 2026 CSD contributors. All rights reserved.
-/
import CsdLean4.CV.Oscillator

/-!
# CV-4: the oscillator energy spectrum — finite-energy predictions recovered

CV-2/CV-3 (`CV/Oscillator.lean`) built the truncated-oscillator ladder operators
`a`, `a†`. This module reads off the **energy spectrum** and shows the truncation
recovers the finite-energy predictions of the ideal oscillator *exactly*.

The Hamiltonian is `H = a†a + ½` (`ℏω = 1`). Since `a†a = diag(0, 1, …, N−1)` is
the number operator, `H = diag(½, 3⁄2, …, N−1+½)` is diagonal, Hermitian, with the
Fock states `eₙ` as energy eigenstates:

    `H·eₙ = (n + ½)·eₙ`,    `Eₙ = n + ½`.

The payoff is that **`Eₙ = n + ½` carries no `N`**: the energy of level `n` is the
same in every truncation that contains it (`oscEnergy` is a function of `n` alone).
So the truncation is transparent for every level below the ceiling — the
zero-point energy `E₀ = ½`, the uniform ladder spacing `Eₙ₊₁ − Eₙ = 1` (the
harmonic-oscillator signature), and each level are all recovered exactly. The
finite cutoff distorts nothing below it; the only defect (CV-3) is at the top
level `N−1`.

## CSD reading

A finite operational sector reproduces the low-lying oscillator physics exactly:
the discrete, evenly-spaced energy ladder and its zero-point offset are
cutoff-independent. The continuum oscillator is the `N → ∞` limit, in which the
ladder simply extends; no low-energy prediction changes.

## Honest scope (load-bearing)

This reads the spectrum off the (already-built) number operator and states its
`N`-independence. It does **not** derive the oscillator dynamics or claim more
than the finite-spectrum recovery. Cat-1; foundational triple; CSD reading in the
docstrings only.

## Main results

- `hamiltonian_eq_diagonal` : `H = diag(n + ½)`.
- `hamiltonian_isHermitian` : `H` is a genuine self-adjoint observable (real spectrum).
- `hamiltonian_mulVec_single` : `H·eₙ = (n + ½)·eₙ` — Fock states are energy eigenstates.
- `oscEnergy` / `oscEnergy_gap` / `oscEnergy_ground` : the cutoff-free energy
  `Eₙ = n + ½`, uniform spacing `1`, zero-point `½`.
- `hamiltonian_groundEnergy` : `H·e₀ = ½·e₀` (the zero-point energy).
-/

namespace CSD.CV

open Matrix

variable (N : ℕ)

/-- The **oscillator Hamiltonian** `H = a†a + ½` (`ℏω = 1`). -/
noncomputable def hamiltonian : Matrix (Fin N) (Fin N) ℂ :=
  creation N * annihilation N + (2⁻¹ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- The **energy of level `n`**, `Eₙ = n + ½`. Crucially a function of `n` ALONE —
no dependence on the cutoff `N` — so it is the same in every truncation that
contains level `n`. -/
noncomputable def oscEnergy (n : ℕ) : ℝ := (n : ℝ) + 2⁻¹

variable {N}

/-- **`H = diag(½, 3⁄2, …, N−1+½)`.** The Hamiltonian is diagonal with the energy
levels on the diagonal. -/
theorem hamiltonian_eq_diagonal :
    hamiltonian N = Matrix.diagonal fun i : Fin N => ((oscEnergy (i : ℕ) : ℝ) : ℂ) := by
  rw [hamiltonian, creation_mul_annihilation, numberOp]
  ext i k
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, oscEnergy]
  by_cases h : i = k
  · subst h; simp only [↓reduceIte]; push_cast; ring
  · simp [h]

/-- **`H` is Hermitian** (a genuine self-adjoint observable — hence real energies). -/
theorem hamiltonian_isHermitian : (hamiltonian N).IsHermitian := by
  rw [Matrix.IsHermitian, hamiltonian_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [Complex.conj_ofReal]

/-- **The Fock states are energy eigenstates.** `H·eₙ = (n + ½)·eₙ`, so the Fock
basis diagonalises the Hamiltonian and the energy of level `n` is `Eₙ = n + ½`. -/
theorem hamiltonian_mulVec_single (n : Fin N) :
    (hamiltonian N).mulVec (Pi.single n 1 : Fin N → ℂ)
      = ((oscEnergy (n : ℕ) : ℝ) : ℂ) • (Pi.single n 1 : Fin N → ℂ) := by
  rw [hamiltonian_eq_diagonal]
  funext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

/-- **Uniform ladder spacing.** `Eₙ₊₁ − Eₙ = 1` — the equally-spaced spectrum that
is the harmonic oscillator's signature, exact and cutoff-free. -/
theorem oscEnergy_gap (n : ℕ) : oscEnergy (n + 1) - oscEnergy n = 1 := by
  simp only [oscEnergy]; push_cast; ring

/-- **Zero-point energy.** `E₀ = ½` — the ground-state energy, cutoff-free. -/
theorem oscEnergy_ground : oscEnergy 0 = 2⁻¹ := by
  simp only [oscEnergy]; norm_num

/-- **Cutoff-independence of finite-energy predictions.** For any two truncations,
levels with the same Fock index have the same energy: `Eₙ` depends only on `n`,
never on the cutoff `N`. This is the sense in which the truncated oscillator
recovers the ideal oscillator's finite-energy predictions exactly. -/
theorem oscEnergy_cutoff_independent {M : ℕ} (n : Fin N) (m : Fin M)
    (h : (n : ℕ) = (m : ℕ)) : oscEnergy (n : ℕ) = oscEnergy (m : ℕ) := by
  rw [h]

/-- **The ground-state energy as an eigenvalue equation.** `H·e₀ = ½·e₀`. -/
theorem hamiltonian_groundEnergy (hN : 0 < N) :
    (hamiltonian N).mulVec (Pi.single (⟨0, hN⟩ : Fin N) 1 : Fin N → ℂ)
      = ((2⁻¹ : ℝ) : ℂ) • (Pi.single (⟨0, hN⟩ : Fin N) 1 : Fin N → ℂ) := by
  rw [hamiltonian_mulVec_single]
  congr 1
  simp only [oscEnergy]
  norm_num

end CSD.CV
