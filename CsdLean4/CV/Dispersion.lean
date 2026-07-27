/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FieldModes

/-!
# CV/Dispersion: relativistic dispersion `ω_k = √(k² + m²)` (EFT Stage 2a)

**Category:** CV (continuous variables — the multi-mode field).

Stage 1 (`CV/FieldModes.lean`) built the free field at a cutoff as a product of unit-frequency
oscillators. Stage 2a gives the modes their **relativistic** frequencies: mode `k` carries
momentum `p k` and oscillates at

  `ω(m, p) = √(p² + m²)`,

so the field's quanta are relativistic particles of mass `m`. This is what makes the mode sum a
*relativistic* field rather than a generic collection of oscillators; spacetime itself is taken
as given (the EFT posture — cutoff-independence, not the continuum limit).

## What this file proves

**The dispersion relation itself.**

* `omega_sq_sub_sq` — the **mass shell** `ω² − p² = m²`: the Lorentz-invariant content of the
  dispersion relation, and the reason `m` deserves the name "mass".
* `abs_le_omega` — `|p| ≤ ω`: no mode carries energy below its momentum, the dispersion-level
  statement that excitations do not outrun the light cone.
* `abs_mass_le_omega` / `omega_zero` — the **mass gap** `|m| ≤ ω`, attained at `p = 0`: the rest
  energy is the floor.
* `omega_massless` — `ω(0, p) = |p|`, the light cone exactly.
* `omega_le_newtonian` — `ω ≤ m + p²/(2m)` for `m > 0`: the relativistic energy never exceeds
  the Newtonian rest-plus-kinetic energy. The non-relativistic limit stated as a clean
  inequality rather than an asymptotic expansion.
* `omega_mono` — higher momentum costs more energy.

**The relativistic field.**

* `relFieldEnergy` / `relFieldHamiltonian` — the free-field Hamiltonian with relativistic mode
  frequencies, `∑ₖ ω(m, pₖ)·(cₖ + ½)`; still **diagonal** in the configuration basis
  (`relFieldHamiltonian_mulVec_single`, `relFieldHamiltonian_isHermitian`), so the whole
  record-layer measurement account of `CV/OscillatorBorn.lean` applies verbatim — only the
  eigenvalues change.
* `relFieldEnergy_quantum` — **the headline**: adding one quantum to mode `k₀` raises the field
  energy by exactly `ω(m, p k₀)`. So the excitations *are* relativistic particles of mass `m`
  and momentum `p k₀`; the dispersion is a statement about the particle content, not a
  parameter choice.
* `relFieldEnergy_vacuum` — the zero-point energy `½∑ₖ ω(m, pₖ)`.
* `relFieldEnergy_cutoff_independent` — unchanged under raising the truncation, the Stage-1
  cutoff-independence carried to relativistic frequencies.

## What this file does NOT claim

Microcausality in its continuum form (`[φ(x), φ(y)] = 0` at spacelike separation) is **not**
proved here and does not hold exactly at a finite cutoff. The honest finite-cutoff locality
statement — the Haag–Kastler one, that observables supported on disjoint mode sets commute — is
`CV/ModeLocality.lean`. The continuum limit is deliberately deferred
(`CV/ApproxCCR.lean` `no_exact_finite_ccr`).

## References

`CV/FieldModes.lean` (Stage 1, the mode product); `CV/OscillatorSpectrum.lean` (`oscEnergy`,
`oscEnergy_cutoff_independent`); `CV/Position.lean` (the spatial lattice); `CV/ModeLocality.lean`
(Stage 2b, locality); `specs/BACKLOG.md` (the CV-chain row); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix

namespace CSD.CV

variable {K N : ℕ}

/-! ### The dispersion relation -/

/-- The **relativistic dispersion** `ω(m, p) = √(p² + m²)`: the frequency of the field mode of
momentum `p` for a field of mass `m`. -/
noncomputable def omega (m p : ℝ) : ℝ := Real.sqrt (p ^ 2 + m ^ 2)

theorem omega_nonneg (m p : ℝ) : 0 ≤ omega m p := Real.sqrt_nonneg _

/-- `ω² = p² + m²`. -/
theorem omega_sq (m p : ℝ) : (omega m p) ^ 2 = p ^ 2 + m ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **The mass shell `ω² − p² = m²`.** The Lorentz-invariant content of the dispersion relation:
the energy–momentum pair of a mode lies on the hyperboloid of invariant mass `m`. -/
theorem omega_sq_sub_sq (m p : ℝ) : (omega m p) ^ 2 - p ^ 2 = m ^ 2 := by
  rw [omega_sq]; ring

/-- **`|p| ≤ ω`** — a mode's energy is never less than its momentum. At the level of the
dispersion relation this is the statement that excitations stay inside the light cone. -/
theorem abs_le_omega (m p : ℝ) : |p| ≤ omega m p := by
  calc |p| = Real.sqrt (p ^ 2) := (Real.sqrt_sq_eq_abs p).symm
    _ ≤ Real.sqrt (p ^ 2 + m ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg m])

/-- **The mass gap `|m| ≤ ω`** — the rest energy is the floor of the spectrum. -/
theorem abs_mass_le_omega (m p : ℝ) : |m| ≤ omega m p := by
  calc |m| = Real.sqrt (m ^ 2) := (Real.sqrt_sq_eq_abs m).symm
    _ ≤ Real.sqrt (p ^ 2 + m ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg p])

/-- The mass gap is **attained**: a mode at rest has energy exactly `|m|`. -/
theorem omega_zero (m : ℝ) : omega m 0 = |m| := by
  rw [omega]; norm_num [Real.sqrt_sq_eq_abs]

/-- **The massless case is the light cone:** `ω(0, p) = |p|`. -/
theorem omega_massless (p : ℝ) : omega 0 p = |p| := by
  rw [omega]; norm_num [Real.sqrt_sq_eq_abs]

/-- A massive mode has strictly positive frequency. -/
theorem omega_pos {m : ℝ} (hm : m ≠ 0) (p : ℝ) : 0 < omega m p :=
  lt_of_lt_of_le (abs_pos.mpr hm) (abs_mass_le_omega m p)

/-- **The non-relativistic bound `ω ≤ m + p²/(2m)`.** The relativistic energy never exceeds the
Newtonian rest-plus-kinetic energy — the non-relativistic limit as an inequality, with no
asymptotic expansion. The gap is exactly the `p⁴/(4m²)` term. -/
theorem omega_le_newtonian {m : ℝ} (hm : 0 < m) (p : ℝ) :
    omega m p ≤ m + p ^ 2 / (2 * m) := by
  have hrhs : 0 ≤ m + p ^ 2 / (2 * m) := by positivity
  rw [omega, ← Real.sqrt_sq hrhs]
  refine Real.sqrt_le_sqrt ?_
  have hexp : (m + p ^ 2 / (2 * m)) ^ 2 = m ^ 2 + p ^ 2 + (p ^ 2 / (2 * m)) ^ 2 := by
    field_simp
    ring
  rw [hexp]
  nlinarith [sq_nonneg (p ^ 2 / (2 * m))]

/-- Higher momentum costs more energy. -/
theorem omega_mono (m : ℝ) {p q : ℝ} (h : |p| ≤ |q|) : omega m p ≤ omega m q := by
  refine Real.sqrt_le_sqrt ?_
  have : p ^ 2 ≤ q ^ 2 := by
    nlinarith [sq_abs p, sq_abs q, abs_nonneg p, abs_nonneg q]
  linarith

/-! ### The relativistic free field -/

variable (m : ℝ) (p : Fin K → ℝ)

/-- The **relativistic field energy** of a configuration: each mode `k` contributes
`ω(m, pₖ)·(cₖ + ½)`. Stage 1's `fieldEnergy` is the unit-frequency case. -/
noncomputable def relFieldEnergy (c : FieldConfig K N) : ℝ :=
  ∑ k, omega m (p k) * oscEnergy (c k)

/-- The **relativistic free-field Hamiltonian**: diagonal in the configuration basis with the
relativistic field energy on the diagonal. -/
noncomputable def relFieldHamiltonian (K N : ℕ) (m : ℝ) (p : Fin K → ℝ) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  Matrix.diagonal (fun c => ((relFieldEnergy m p c : ℝ) : ℂ))

/-- **Configurations are energy eigenstates**, now with relativistic eigenvalues. The Hamiltonian
stays diagonal in the configuration basis, so the record-layer measurement account carries over
verbatim from `CV/OscillatorBorn.lean` — only the eigenvalues change. -/
theorem relFieldHamiltonian_mulVec_single (c : FieldConfig K N) :
    (relFieldHamiltonian K N m p).mulVec (Pi.single c 1)
      = ((relFieldEnergy m p c : ℝ) : ℂ) • (Pi.single c 1) := by
  funext d
  rw [relFieldHamiltonian, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

/-- The relativistic Hamiltonian is Hermitian (diagonal with real entries). -/
theorem relFieldHamiltonian_isHermitian : (relFieldHamiltonian K N m p).IsHermitian := by
  rw [relFieldHamiltonian]
  exact Matrix.isHermitian_diagonal_of_self_adjoint _
    (funext fun c => RCLike.conj_ofReal (relFieldEnergy m p c))

/-- The field energy is non-negative (each mode contributes `ω ≥ 0` times `cₖ + ½ > 0`). -/
theorem relFieldEnergy_nonneg (c : FieldConfig K N) : 0 ≤ relFieldEnergy m p c :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (omega_nonneg _ _) (by rw [oscEnergy]; positivity)

/-- **The zero-point energy.** The empty configuration has energy `½∑ₖ ω(m, pₖ)`. -/
theorem relFieldEnergy_vacuum {N : ℕ} [NeZero N] :
    relFieldEnergy m p (fun _ => (0 : Fin N)) = (∑ k, omega m (p k)) / 2 := by
  rw [relFieldEnergy, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : oscEnergy ((0 : Fin N) : ℕ) = 2⁻¹ := by
    rw [oscEnergy, Fin.val_zero]
    norm_num
  show omega m (p k) * oscEnergy ((0 : Fin N) : ℕ) = omega m (p k) / 2
  rw [h0]
  ring

/-- **The headline: one quantum in mode `k₀` costs exactly `ω(m, p k₀)`.**

If `d` has one more quantum in mode `k₀` than `c`, and agrees with `c` elsewhere, the field
energy rises by exactly the relativistic frequency of that mode. So the field's excitations
*are* relativistic particles of mass `m` and momentum `p k₀` — the dispersion relation is a
statement about the particle content, not a parameter choice. -/
theorem relFieldEnergy_quantum {c d : FieldConfig K N} (k₀ : Fin K)
    (hk₀ : (d k₀ : ℕ) = (c k₀ : ℕ) + 1) (hrest : ∀ k, k ≠ k₀ → (d k : ℕ) = (c k : ℕ)) :
    relFieldEnergy m p d - relFieldEnergy m p c = omega m (p k₀) := by
  rw [relFieldEnergy, relFieldEnergy, ← Finset.sum_sub_distrib,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
  have hzero : ∀ k ∈ Finset.univ.erase k₀,
      omega m (p k) * oscEnergy (d k) - omega m (p k) * oscEnergy (c k) = 0 := by
    intro k hk
    rw [oscEnergy, oscEnergy, hrest k (Finset.ne_of_mem_erase hk)]
    ring
  rw [Finset.sum_eq_zero hzero, add_zero, oscEnergy, oscEnergy, hk₀]
  push_cast
  ring

/-- **Cutoff-independence.** Configurations with the same per-mode occupation have the same
relativistic field energy, regardless of the truncation — the Stage-1 statement carried to
relativistic frequencies. -/
theorem relFieldEnergy_cutoff_independent {K N M : ℕ} (m : ℝ) (p : Fin K → ℝ)
    (c : FieldConfig K N) (d : FieldConfig K M) (h : ∀ k, (c k : ℕ) = (d k : ℕ)) :
    relFieldEnergy m p c = relFieldEnergy m p d :=
  Finset.sum_congr rfl fun k _ => by
    rw [oscEnergy_cutoff_independent (c k) (d k) (h k)]

end CSD.CV
