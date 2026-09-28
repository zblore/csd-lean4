/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The Aharonov–Bohm effect on a ring of `N` sites

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #55, brick BP-4 of
`specs/berry-phase-scoping.md`.

A tight-binding ring of `N` sites threaded by a magnetic flux `Φ`: the amplitude to hop from `j`
to `j + 1` carries the Peierls phase `e^{i a j}`, and the flux is the phase accumulated around the
loop, `Φ = ∑ⱼ a j`. The whole Aharonov–Bohm effect is two theorems about this matrix:

* **the vector potential is not observable** — the individual bond phases can be moved around at
  will by a diagonal unitary (★★ `gaugeDiag_conj_ringHamOf`), and every such move leaves the total
  flux alone (★ `flux_gauge`); in particular the uniform ring is unitarily equivalent to the ring
  with the *whole* phase on one bond (★★★ `gaugeDiag_conj_ringHam_oneBond`);
* **the flux is observable** — the spectrum is `2 cos((2πm + Φ)/N)`, which moves with `Φ`
  (★★ `ringHam_mulVec_ringMode`, ★★ `dftMatrix_conj_ringHam`), and no unitary conjugation can undo
  that: ★★★ `not_exists_unitary_conj_ringHam` exhibits two fluxes on a three-site ring whose rings
  are not unitarily equivalent.

The spectrum depends on `Φ` only modulo `2π` (★ `ringEigval_add_two_pi`,
★★ `range_ringEigval_add_two_pi`): flux is measured in units of the quantum `2π`.

## Main declarations

* `ringHamOf N a` — the ring with bond phases `a`; `ringHam N Φ` — the uniform ring `a ≡ Φ/N`;
  `flux a = ∑ⱼ a j` with `flux_ringHam`; `ringHamOf_isHermitian` (for `3 ≤ N`);
* `ringMode N k` — the twisted Fourier mode `ψ_k(j) = e^{−2πi jk/N}`; `ringEigval N Φ m`;
* ★★ `ringHam_mulVec_ringMode` — **the modes are eigenvectors with eigenvalue
  `2 cos((2πm + Φ)/N)`**, `m` any integer label; ★ `hasEigenvalue_ringHam`;
* `dftMatrix N` — the unitary discrete Fourier matrix (★ `dftMatrix_conjTranspose_mul`), and
  ★★ `dftMatrix_conj_ringHam` — **the ring Hamiltonian is diagonalised by the discrete Fourier
  transform**, so ★★ `eq_ringEigval_of_mulVec` — those numbers are the *whole* spectrum;
* ★★ `gaugeDiag_conj_ringHamOf`, ★ `flux_gauge`, ★★★ `gaugeDiag_conj_ringHam_oneBond`;
* ★★★ `not_exists_unitary_conj_ringHam`.

## Honest scope

⚠️ Finite-dimensional: a ring of `N ≥ 3` sites, which is the lattice Aharonov–Bohm effect. The
continuum version on `L²(S¹)` — the operator `−(∂ − iΦ)²` with spectrum `(n − Φ)²` — is not here and
is not claimed (`specs/berry-phase-scoping.md` BP-4 says why: it is CV-scale).

⚠️ No solenoid, no vector potential as a `1`-form, no double slit: the flux enters as the phase of
the hopping amplitudes, which is Peierls' substitution taken as the definition of the model.

References: Y. Aharonov, D. Bohm, Phys. Rev. 115 (1959) 485; R. G. Chambers, Phys. Rev. Lett. 5
(1960) 3; A. Tonomura et al., Phys. Rev. Lett. 56 (1986) 792; R. Peierls, Z. Phys. 80 (1933) 763;
`specs/berry-phase-scoping.md` BP-4; `specs/BACKLOG.md` #55; `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open scoped Real ComplexConjugate
open Matrix

namespace QuantumInfo

namespace AharonovBohm

/-! ### The ring and its flux -/

variable {N : ℕ}

/-- The tight-binding ring of `N` sites with Peierls phases: `a j` is the phase of the hop from
site `j` to site `j + 1`, so the matrix element `⟨j + 1|H|j⟩` is `e^{i a j}` and the Hamiltonian is
Hermitian. -/
def ringHamOf (N : ℕ) (a : ZMod N → ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun i j =>
    if i = j + 1 then Complex.exp (((a j : ℝ) : ℂ) * Complex.I)
    else if j = i + 1 then conj (Complex.exp (((a i : ℝ) : ℂ) * Complex.I))
    else 0

/-- The flux threading the ring: the phase accumulated once around it. -/
def flux (N : ℕ) [Fintype (ZMod N)] (a : ZMod N → ℝ) : ℝ := ∑ j, a j

/-- The uniform gauge: the flux `Φ` shared equally among the `N` bonds. -/
def ringHam (N : ℕ) (Φ : ℝ) : Matrix (ZMod N) (ZMod N) ℂ := ringHamOf N fun _ => Φ / N

theorem flux_ringHam [NeZero N] (Φ : ℝ) : flux N (fun _ => Φ / N) = Φ := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [flux, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

/-- A ring with at least three sites has `2 ≠ 0` in its site group. -/
theorem two_ne_zero (hN : 3 ≤ N) : (2 : ZMod N) ≠ 0 := by
  have : NeZero N := ⟨by omega⟩
  intro h
  have h2 : ((2 : ℕ) : ZMod N) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd two_pos h2) (by omega)

/-- On a ring with at least three sites the two neighbours of a site are distinct. -/
theorem sub_one_ne_add_one (hN : 3 ≤ N) (i : ZMod N) : i - 1 ≠ i + 1 := by
  intro h
  exact two_ne_zero hN (by linear_combination -h)

/-- On a ring with at least three sites a site is not its own second neighbour. -/
theorem self_ne_add_two (hN : 3 ≤ N) (i : ZMod N) : i ≠ i + 2 := by
  intro h
  exact two_ne_zero hN (by linear_combination -h)

theorem ringHamOf_apply_of_ne {a : ZMod N → ℝ} {i j : ZMod N} (h1 : i ≠ j + 1) (h2 : j ≠ i + 1) :
    ringHamOf N a i j = 0 := by
  rw [ringHamOf, Matrix.of_apply, if_neg h1, if_neg h2]

theorem ringHamOf_apply_succ (a : ZMod N → ℝ) (j : ZMod N) :
    ringHamOf N a (j + 1) j = Complex.exp (((a j : ℝ) : ℂ) * Complex.I) := by
  rw [ringHamOf, Matrix.of_apply, if_pos rfl]

theorem ringHamOf_apply_pred (hN : 3 ≤ N) (a : ZMod N → ℝ) (j : ZMod N) :
    ringHamOf N a j (j + 1) = conj (Complex.exp (((a j : ℝ) : ℂ) * Complex.I)) := by
  rw [ringHamOf, Matrix.of_apply, if_neg (fun h => self_ne_add_two hN j (by linear_combination h)),
    if_pos rfl]

/-- ★ **The ring Hamiltonian is Hermitian.** -/
theorem ringHamOf_isHermitian (hN : 3 ≤ N) (a : ZMod N → ℝ) :
    Matrix.IsHermitian (ringHamOf N a) := by
  ext i j
  show conj (ringHamOf N a j i) = ringHamOf N a i j
  by_cases h1 : i = j + 1
  · have h2 : j ≠ i + 1 := fun h => self_ne_add_two hN j (by rw [h1] at h; linear_combination h)
    rw [h1, ringHamOf_apply_pred hN, ringHamOf_apply_succ, RingHomCompTriple.comp_apply,
      RingHom.id_apply]
  · by_cases h2 : j = i + 1
    · rw [h2, ringHamOf_apply_succ, ringHamOf_apply_pred hN]
    · rw [ringHamOf_apply_of_ne h2 h1, ringHamOf_apply_of_ne h1 h2, map_zero]

/-! ### The twisted Fourier modes -/

variable [NeZero N]

/-- The twisted Fourier mode `ψ_k(j) = e^{−2πi jk/N}` (the discrete-Fourier convention). -/
def ringMode (N : ℕ) [NeZero N] (k : ZMod N) : ZMod N → ℂ := fun j => ZMod.stdAddChar (-(j * k))

@[simp] theorem ringMode_zero (k : ZMod N) : ringMode N k 0 = 1 := by
  rw [ringMode]
  simp

theorem ringMode_ne_zero (k : ZMod N) : ringMode N k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [ringMode_zero] at h0
  exact one_ne_zero h0

theorem ringMode_sub_one (k j : ZMod N) :
    ringMode N k (j - 1) = ringMode N k j * ZMod.stdAddChar k := by
  rw [ringMode, ringMode, show -((j - 1) * k) = -(j * k) + k by ring, AddChar.map_add_eq_mul]

theorem ringMode_add_one (k j : ZMod N) :
    ringMode N k (j + 1) = ringMode N k j * ZMod.stdAddChar (-k) := by
  rw [ringMode, ringMode, show -((j + 1) * k) = -(j * k) + -k by ring, AddChar.map_add_eq_mul]

/-- The standard character at `−k` is the conjugate of the character at `k`: its values are on the
unit circle. -/
theorem stdAddChar_neg_eq_conj (k : ZMod N) :
    ZMod.stdAddChar (-k) = conj (ZMod.stdAddChar k) := by
  have hnorm : ‖ZMod.stdAddChar (N := N) k‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hmul : ZMod.stdAddChar (N := N) (-k) * ZMod.stdAddChar (N := N) k = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  rw [← Complex.inv_eq_conj hnorm]
  exact eq_inv_of_mul_eq_one_left hmul

/-- The eigenvalue attached to the integer label `m`: `2 cos((2πm + Φ)/N)`. -/
def ringEigval (N : ℕ) (Φ : ℝ) (m : ℤ) : ℝ := 2 * Real.cos ((2 * π * m + Φ) / N)

/-- The uniform bond phase times the character at an integer label is a single exponential. -/
theorem bondPhase_mul_stdAddChar (Φ : ℝ) (m : ℤ) :
    Complex.exp (((Φ / N : ℝ) : ℂ) * Complex.I) * ZMod.stdAddChar ((m : ZMod N))
      = Complex.exp ((((2 * π * m + Φ) / N : ℝ) : ℂ) * Complex.I) := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- ★★ **The twisted modes are the eigenvectors of the ring**, with eigenvalue
`2 cos((2πm + Φ)/N)` for any integer label `m` of the mode. This is the Aharonov–Bohm spectrum: the
flux shifts every level, and it does so continuously. -/
theorem ringHam_mulVec_ringMode (hN : 3 ≤ N) (Φ : ℝ) (m : ℤ) :
    ringHam N Φ *ᵥ ringMode N (m : ZMod N)
      = ((ringEigval N Φ m : ℝ) : ℂ) • ringMode N (m : ZMod N) := by
  funext i
  have hne : i - 1 ≠ i + 1 := sub_one_ne_add_one hN i
  have hzero : ∀ j ∈ (Finset.univ : Finset (ZMod N)),
      j ∉ ({i - 1, i + 1} : Finset (ZMod N)) →
      ringHam N Φ i j * ringMode N (m : ZMod N) j = 0 := by
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    have h1 : i ≠ j + 1 := fun h => hj.1 (by rw [h]; ring)
    rw [ringHam, ringHamOf_apply_of_ne h1 hj.2, zero_mul]
  rw [Matrix.mulVec, dotProduct,
    ← Finset.sum_subset (Finset.subset_univ ({i - 1, i + 1} : Finset (ZMod N))) hzero,
    Finset.sum_pair hne]
  have hup : ringHam N Φ i (i - 1) = Complex.exp (((Φ / N : ℝ) : ℂ) * Complex.I) := by
    have hsucc := ringHamOf_apply_succ (N := N) (fun _ => Φ / N) (i - 1)
    rw [show i - 1 + 1 = i by ring] at hsucc
    exact hsucc
  have hdown : ringHam N Φ i (i + 1) = conj (Complex.exp (((Φ / N : ℝ) : ℂ) * Complex.I)) := by
    rw [ringHam, ringHamOf_apply_pred hN]
  rw [hup, hdown, ringMode_sub_one, ringMode_add_one, Pi.smul_apply, smul_eq_mul,
    stdAddChar_neg_eq_conj, mul_comm (ringMode N (m : ZMod N) i) (ZMod.stdAddChar ((m : ZMod N))),
    ← mul_assoc, mul_comm (ringMode N (m : ZMod N) i) (conj (ZMod.stdAddChar ((m : ZMod N)))),
    ← mul_assoc, ← map_mul, bondPhase_mul_stdAddChar, ← add_mul]
  congr 1
  rw [Complex.add_conj, ringEigval]
  norm_cast
  rw [Complex.exp_ofReal_mul_I_re]

/-! ### The flux quantum: the spectrum sees `Φ` only modulo `2π` -/

omit [NeZero N] in
theorem ringEigval_add_two_pi (Φ : ℝ) (m : ℤ) :
    ringEigval N (Φ + 2 * π) m = ringEigval N Φ (m + 1) := by
  rw [ringEigval, ringEigval]
  congr 2
  push_cast
  ring

theorem ringEigval_add_card (Φ : ℝ) (m : ℤ) : ringEigval N Φ (m + N) = ringEigval N Φ m := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [ringEigval, ringEigval]
  push_cast
  rw [show (2 * π * ((m : ℝ) + N) + Φ) / N = (2 * π * m + Φ) / N + 2 * π by field_simp; ring,
    Real.cos_add_two_pi]

omit [NeZero N] in
/-- ★★ **One flux quantum changes nothing.** Adding `2π` to the flux permutes the levels — the
spectrum, as a set, is invariant. -/
theorem range_ringEigval_add_two_pi (Φ : ℝ) :
    Set.range (ringEigval N (Φ + 2 * π)) = Set.range (ringEigval N Φ) := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m + 1, (ringEigval_add_two_pi Φ m).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m - 1, ?_⟩
    rw [ringEigval_add_two_pi]
    congr 1
    ring

/-- ★ The levels of the ring are eigenvalues of its Hamiltonian, as `Module.End.HasEigenvalue`. -/
theorem hasEigenvalue_ringHam (hN : 3 ≤ N) (Φ : ℝ) (m : ℤ) :
    Module.End.HasEigenvalue (Matrix.mulVecLin (ringHam N Φ)) ((ringEigval N Φ m : ℝ) : ℂ) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := ringMode N (m : ZMod N)) ⟨?_, ringMode_ne_zero _⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  exact ringHam_mulVec_ringMode hN Φ m

/-! ### Gauge transformations: the vector potential is not observable -/

/-- A gauge transformation of the ring: the diagonal unitary `diag(e^{i g j})`. -/
def gaugeDiag (N : ℕ) (g : ZMod N → ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.diagonal fun j => Complex.exp (((g j : ℝ) : ℂ) * Complex.I)

theorem conj_exp_mul_I (u : ℝ) :
    conj (Complex.exp (((u : ℝ) : ℂ) * Complex.I)) = Complex.exp (((-u : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem conj_exp_mul_I_mul_self (u : ℝ) :
    conj (Complex.exp (((u : ℝ) : ℂ) * Complex.I)) * Complex.exp (((u : ℝ) : ℂ) * Complex.I)
      = 1 := by
  rw [conj_exp_mul_I, ← Complex.exp_add]
  norm_num

/-- A gauge transformation is unitary. -/
theorem gaugeDiag_conjTranspose_mul (g : ZMod N → ℝ) : (gaugeDiag N g)ᴴ * gaugeDiag N g = 1 := by
  rw [gaugeDiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.star_apply, RCLike.star_def]
  exact conj_exp_mul_I_mul_self (g j)

/-- ★★ **Gauge covariance of the ring.** Conjugating by the diagonal unitary `diag(e^{i g})` moves
the bond phases by the discrete gradient of `g`: the vector potential is not observable, only
gauge-equivalent descriptions of the same ring. -/
theorem gaugeDiag_conj_ringHamOf (hN : 3 ≤ N) (a g : ZMod N → ℝ) :
    (gaugeDiag N g)ᴴ * ringHamOf N a * gaugeDiag N g
      = ringHamOf N fun j => a j + g j - g (j + 1) := by
  ext i j
  rw [gaugeDiag, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply, RCLike.star_def]
  by_cases h1 : i = j + 1
  · subst h1
    rw [ringHamOf_apply_succ, ringHamOf_apply_succ, conj_exp_mul_I, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · by_cases h2 : j = i + 1
    · subst h2
      rw [ringHamOf_apply_pred hN, ringHamOf_apply_pred hN, conj_exp_mul_I (g i),
        conj_exp_mul_I (a i), conj_exp_mul_I (a i + g i - g (i + 1)), ← Complex.exp_add,
        ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [ringHamOf_apply_of_ne h1 h2, ringHamOf_apply_of_ne h1 h2, mul_zero, zero_mul]

/-- ★ **The flux is gauge-invariant**: the discrete gradient of `g` sums to zero around the ring. -/
theorem flux_gauge (a g : ZMod N → ℝ) :
    flux N (fun j => a j + g j - g (j + 1)) = flux N a := by
  have hshift : ∑ j, g (j + 1) = ∑ j, g j :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ fun j => rfl
  simp only [flux, Finset.sum_sub_distrib, Finset.sum_add_distrib, hshift]
  ring

/-! ### All the flux on one bond -/

/-- The gauge in which the whole flux sits on the single bond from `−1` to `0`. -/
def oneBondPhase (N : ℕ) (Φ : ℝ) : ZMod N → ℝ := fun j => if j = -1 then Φ else 0

theorem flux_oneBondPhase (Φ : ℝ) : flux N (oneBondPhase N Φ) = Φ := by
  simp [flux, oneBondPhase]

/-- The gauge function that pushes the uniform phases onto that one bond. -/
def oneBondGauge (N : ℕ) (Φ : ℝ) : ZMod N → ℝ := fun j => Φ / N * j.val

/-- Away from the distinguished site the successor's value is the successor of the value. -/
theorem val_add_one_of_ne (hN : 3 ≤ N) {j : ZMod N} (h : j ≠ -1) : (j + 1).val = j.val + 1 := by
  have hfact : Fact (1 < N) := ⟨by omega⟩
  have hlt : j.val + 1 < N := by
    have h1 : j.val < N := ZMod.val_lt j
    rcases Nat.lt_or_ge (j.val + 1) N with h2 | h2
    · exact h2
    · exfalso
      refine h ?_
      have hv : j.val = N - 1 := by omega
      have hcast : ((j.val : ℕ) : ZMod N) = j := ZMod.natCast_rightInverse j
      have hsum : ((N - 1 : ℕ) : ZMod N) + 1 = 0 := by
        calc ((N - 1 : ℕ) : ZMod N) + 1 = ((N - 1 + 1 : ℕ) : ZMod N) := by push_cast; ring
          _ = ((N : ℕ) : ZMod N) := by rw [show N - 1 + 1 = N by omega]
          _ = 0 := ZMod.natCast_self N
      rw [← hcast, hv]
      linear_combination hsum
  rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; exact hlt), ZMod.val_one]

/-- ★ The uniform phases, gauge-shifted by `oneBondGauge`, are exactly the one-bond phases. -/
theorem uniform_add_oneBondGauge (hN : 3 ≤ N) (Φ : ℝ) (j : ZMod N) :
    Φ / N + oneBondGauge N Φ j - oneBondGauge N Φ (j + 1) = oneBondPhase N Φ j := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  by_cases h : j = -1
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    subst h
    rw [oneBondPhase, if_pos rfl, oneBondGauge, oneBondGauge, neg_add_cancel, ZMod.val_zero,
      ZMod.val_neg_one]
    push_cast at hNne ⊢
    field_simp
    ring
  · rw [oneBondPhase, if_neg h, oneBondGauge, oneBondGauge, val_add_one_of_ne hN h]
    push_cast
    ring

/-- ★★★ **The whole flux can be put on a single bond.** The uniform ring and the ring whose entire
Peierls phase sits on the bond from `−1` to `0` are the same Hamiltonian in two gauges: conjugate by
one explicit diagonal unitary. The spectrum therefore cannot see how the phase is distributed — only
its total, the flux. -/
theorem gaugeDiag_conj_ringHam_oneBond (hN : 3 ≤ N) (Φ : ℝ) :
    (gaugeDiag N (oneBondGauge N Φ))ᴴ * ringHam N Φ * gaugeDiag N (oneBondGauge N Φ)
      = ringHamOf N (oneBondPhase N Φ) := by
  rw [ringHam, gaugeDiag_conj_ringHamOf hN]
  congr 1
  funext j
  exact uniform_add_oneBondGauge hN Φ j

/-! ### The discrete Fourier transform diagonalises the ring -/

/-- Three matrices acting on a vector, one at a time. -/
theorem mulVec_three (A B C : Matrix (ZMod N) (ZMod N) ℂ) (v : ZMod N → ℂ) :
    (A * B * C) *ᵥ v = A *ᵥ (B *ᵥ (C *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Character orthogonality on `ZMod N`: the sum of `stdAddChar (t · j)` over the ring is `N` for
`t = 0` and `0` otherwise. -/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ j : ZMod N, ZMod.stdAddChar (t * j) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- The integer label of a site is the site. -/
theorem intCast_val (k : ZMod N) : (((k.val : ℤ)) : ZMod N) = k := by
  push_cast
  exact ZMod.natCast_rightInverse k

/-- The discrete Fourier matrix of the ring: its columns are the twisted modes, normalised. -/
def dftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun j k => ringMode N k j / ((Real.sqrt N : ℝ) : ℂ)

theorem dftMatrix_apply (j k : ZMod N) :
    dftMatrix N j k = ringMode N k j / ((Real.sqrt N : ℝ) : ℂ) := rfl

/-- ★ **The Fourier matrix is unitary** — character orthogonality. -/
theorem dftMatrix_conjTranspose_mul : (dftMatrix N)ᴴ * dftMatrix N = 1 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNpos.le]
    norm_num
  have hne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.2 hNpos
  ext k k'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ j : ZMod N, (dftMatrix N)ᴴ k j * dftMatrix N j k'
      = ZMod.stdAddChar ((k - k') * j) / (N : ℂ) := by
    intro j
    rw [Matrix.conjTranspose_apply, dftMatrix_apply, dftMatrix_apply, RCLike.star_def, map_div₀,
      Complex.conj_ofReal, ringMode, ringMode, stdAddChar_neg_eq_conj, Complex.conj_conj,
      div_mul_div_comm, hsq, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_div, sum_stdAddChar_mul]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  by_cases h : k = k'
  · rw [if_pos h, if_pos (by rw [h]; ring), div_self hNc]
  · rw [if_neg h, if_neg (fun hz => h (by linear_combination hz))]
    simp

theorem dftMatrix_mul_conjTranspose : dftMatrix N * (dftMatrix N)ᴴ = 1 :=
  mul_eq_one_comm.2 dftMatrix_conjTranspose_mul

/-- ★★ **The ring Hamiltonian is diagonalised by the discrete Fourier transform**, with the
Aharonov–Bohm levels `2 cos((2πk + Φ)/N)` on the diagonal. -/
theorem dftMatrix_conj_ringHam (hN : 3 ≤ N) (Φ : ℝ) :
    (dftMatrix N)ᴴ * ringHam N Φ * dftMatrix N
      = Matrix.diagonal fun k => ((ringEigval N Φ (k.val : ℤ) : ℝ) : ℂ) := by
  have hcol : ringHam N Φ * dftMatrix N
      = dftMatrix N * Matrix.diagonal fun k => ((ringEigval N Φ (k.val : ℤ) : ℝ) : ℂ) := by
    ext i k
    have hmode := ringHam_mulVec_ringMode hN Φ (k.val : ℤ)
    rw [intCast_val] at hmode
    have hentry : (ringHam N Φ * dftMatrix N) i k
        = (ringHam N Φ *ᵥ fun j => dftMatrix N j k) i := rfl
    rw [hentry, Matrix.mul_diagonal, dftMatrix_apply]
    have hsmul : (fun j => dftMatrix N j k) = (((Real.sqrt N : ℝ) : ℂ)⁻¹ • ringMode N k) := by
      funext j
      rw [dftMatrix_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hsmul, Matrix.mulVec_smul, hmode, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      div_eq_inv_mul]
    ring
  rw [Matrix.mul_assoc, hcol, ← Matrix.mul_assoc, dftMatrix_conjTranspose_mul, Matrix.one_mul]

/-- ★★ **Those levels are the whole spectrum.** Every eigenvalue of the ring is one of the
`2 cos((2πk + Φ)/N)`. -/
theorem eq_ringEigval_of_mulVec (hN : 3 ≤ N) (Φ : ℝ) {μ : ℂ} {v : ZMod N → ℂ} (hv : v ≠ 0)
    (h : ringHam N Φ *ᵥ v = μ • v) :
    ∃ k : ZMod N, μ = ((ringEigval N Φ (k.val : ℤ) : ℝ) : ℂ) := by
  have hw : (dftMatrix N)ᴴ *ᵥ v ≠ 0 := by
    intro h0
    refine hv ?_
    have h1 : dftMatrix N *ᵥ ((dftMatrix N)ᴴ *ᵥ v) = 0 := by
      rw [h0, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, dftMatrix_mul_conjTranspose, Matrix.one_mulVec] at h1
  obtain ⟨k, hk⟩ : ∃ k, ((dftMatrix N)ᴴ *ᵥ v) k ≠ 0 := by
    by_contra hc
    exact hw (funext fun k => not_not.1 (fun hne => hc ⟨k, hne⟩))
  refine ⟨k, ?_⟩
  have hdiag : (Matrix.diagonal fun k => ((ringEigval N Φ (k.val : ℤ) : ℝ) : ℂ))
      *ᵥ ((dftMatrix N)ᴴ *ᵥ v) = μ • ((dftMatrix N)ᴴ *ᵥ v) :=
    calc (Matrix.diagonal fun k => ((ringEigval N Φ (k.val : ℤ) : ℝ) : ℂ))
          *ᵥ ((dftMatrix N)ᴴ *ᵥ v)
        = ((dftMatrix N)ᴴ * ringHam N Φ * dftMatrix N) *ᵥ ((dftMatrix N)ᴴ *ᵥ v) := by
          rw [dftMatrix_conj_ringHam hN Φ]
      _ = (dftMatrix N)ᴴ *ᵥ (ringHam N Φ *ᵥ (dftMatrix N *ᵥ ((dftMatrix N)ᴴ *ᵥ v))) :=
          mulVec_three _ _ _ _
      _ = (dftMatrix N)ᴴ *ᵥ (ringHam N Φ *ᵥ v) := by
          rw [Matrix.mulVec_mulVec v (dftMatrix N) ((dftMatrix N)ᴴ),
            dftMatrix_mul_conjTranspose, Matrix.one_mulVec]
      _ = (dftMatrix N)ᴴ *ᵥ (μ • v) := by rw [h]
      _ = μ • ((dftMatrix N)ᴴ *ᵥ v) := Matrix.mulVec_smul _ _ _
  have hcomp := congrFun hdiag k
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hcomp
  exact (mul_right_cancel₀ hk hcomp).symm

/-! ### The flux is observable -/

/-- At `Φ = π` no level of the three-site ring is `2`: `2 cos((2πm + π)/3) = 2` would force
`2m + 1 = 6n`. -/
theorem ringEigval_three_pi_ne_two (m : ℤ) : ringEigval 3 π m ≠ 2 := by
  intro h
  have hcos : Real.cos ((2 * π * m + π) / 3) = 1 := by
    rw [ringEigval] at h
    linarith
  rw [Real.cos_eq_one_iff] at hcos
  obtain ⟨n, hn⟩ := hcos
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hreal : 2 * (m : ℝ) + 1 = 6 * n := by
    field_simp at hn
    nlinarith [hn, Real.pi_pos]
  have hint : 2 * m + 1 = 6 * n := by exact_mod_cast hreal
  omega

theorem ringEigval_three_zero_zero : ringEigval 3 0 0 = 2 := by
  rw [ringEigval]
  norm_num

/-- ★★★ **The flux is observable: the Aharonov–Bohm phase is not a gauge artefact.** No unitary
conjugation carries the three-site ring with no flux to the three-site ring with flux `π` — the
level `2` of the first is not a level of the second. Together with `gaugeDiag_conj_ringHam_oneBond`
(the phases may be redistributed at will) this is the Aharonov–Bohm effect: the vector potential is
not observable, the flux is. -/
theorem not_exists_unitary_conj_ringHam :
    ¬∃ U : Matrix (ZMod 3) (ZMod 3) ℂ, Uᴴ * U = 1 ∧ U * ringHam 3 0 * Uᴴ = ringHam 3 π := by
  rintro ⟨U, hU, hconj⟩
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.2 hU
  have hmode := ringHam_mulVec_ringMode (N := 3) (by norm_num) 0 0
  rw [ringEigval_three_zero_zero] at hmode
  have hv : U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    have h1 : Uᴴ *ᵥ (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3)) = 0 := by
      rw [h0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] at h1
    exact ringMode_ne_zero _ h1
  have heig : ringHam 3 π *ᵥ (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3))
      = ((2 : ℝ) : ℂ) • (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3)) :=
    calc ringHam 3 π *ᵥ (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3))
        = (U * ringHam 3 0 * Uᴴ) *ᵥ (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3)) := by rw [hconj]
      _ = U *ᵥ (ringHam 3 0 *ᵥ (Uᴴ *ᵥ (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3)))) :=
          mulVec_three _ _ _ _
      _ = U *ᵥ (ringHam 3 0 *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3)) := by
          rw [Matrix.mulVec_mulVec (ringMode 3 ((0 : ℤ) : ZMod 3)) Uᴴ U, hU, Matrix.one_mulVec]
      _ = U *ᵥ (((2 : ℝ) : ℂ) • ringMode 3 ((0 : ℤ) : ZMod 3)) := by rw [hmode]
      _ = ((2 : ℝ) : ℂ) • (U *ᵥ ringMode 3 ((0 : ℤ) : ZMod 3)) := Matrix.mulVec_smul _ _ _
  obtain ⟨k, hk⟩ := eq_ringEigval_of_mulVec (N := 3) (by norm_num) π hv heig
  exact ringEigval_three_pi_ne_two _ (by exact_mod_cast hk.symm)

end AharonovBohm

end QuantumInfo

end
