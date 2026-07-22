/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NoncommRing

/-!
# CV-2 / CV-3: the truncated oscillator and the approximate CCR

**Category:** 3-Local (the truncated oscillator and the approximate CCR).

W4 (`CV/ApproxCCR.lean`) proved that no finite matrices satisfy the *exact*
canonical commutation relation `[Q, P] = iℏ·1` — the trace of a commutator is `0`,
the trace of `iℏ·1` is `iℏN ≠ 0`. CV-1 (`CV/Position.lean`) built a finite
position observable. This module builds the **conjugate `(Q, P)` pair** and the
sharp **approximate CCR**: the relation `[Q, P] = iℏ·1` holds *exactly* on a
low-energy sector, failing only by a rank-one defect at the top level — and it
*must* fail there, by exactly the amount that makes the trace vanish (W4).

The construction is the `N`-level truncated harmonic oscillator. With the
annihilation operator `a` (`a·eₙ = √n·e_{n-1}`) and creation `a† = aᴴ`:

* `creation_mul_annihilation` : `a†a = diag(0,1,…,N−1)` — the number operator;
* `annihilation_mul_creation` : `aa† = diag(1,2,…,N−1,0)`;
* `truncated_ccr` : `[a, a†] = 1 − N·|N−1⟩⟨N−1|` — the CCR with a rank-one defect
  at the top Fock level, the finite trace of both sides being `0` (W4).

Then `Q = (a + a†)/√2`, `P = (a − a†)/(i√2)` are Hermitian, and:

* `QP_commutator` : `[Q, P] = i·[a, a†]`;
* `ccr_exact_on_bulk` : `[Q, P]·eₙ = i·eₙ` for every `n ≠ N−1` — the **exact CCR
  on the low-energy sector** (all Fock levels but the top).

So the additive CCR is available *approximately*: exact away from the boundary,
with the unavoidable defect (W4) pushed entirely into the highest level. On states
with negligible top-level population the defect is negligible, i.e.
`‖[Q, P] − i·1‖` is small on the low-energy sector.

## CSD reading

A finite operational sector realises position and momentum as an approximately
canonical pair: the commutator is `i·1` throughout the bulk and departs from it
only at the sector's energy ceiling — the finite-information-capacity boundary.
The continuum CCR is the `N → ∞` limit in which the boundary recedes to infinity.

## Honest scope (load-bearing)

This constructs one concrete conjugate pair and proves its commutator exactly. It
does **not** derive continuous-variable QM and does **not** claim the oscillator
is canonical (W4 forbids that in finite dimension); the boundary defect is
displayed honestly, not hidden.

## Category

Cat-1: `annihilation`, `creation`, `Q`, `P` and all lemmas are CSD-free general
facts about finite complex matrices. The CSD interpretation lives only in the
docstrings.
-/

namespace CSD.CV

open Matrix

/-! ### Two index-sum helpers -/

/-- A single-term sum: `∑_{j:Fin N} [j = c]·v = [c < N]·v`. -/
lemma sum_ite_valEq (N c : ℕ) (v : ℂ) :
    (∑ j : Fin N, if (j : ℕ) = c then v else 0) = if c < N then v else 0 := by
  by_cases hc : c < N
  · rw [if_pos hc, Finset.sum_eq_single (⟨c, hc⟩ : Fin N)]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h; exact hj (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    intro h; exact hc (h ▸ j.isLt)

/-- A single-term sum for the shifted condition: `∑_{j:Fin N} [j+1 = c]·v =
`[1 ≤ c ∧ c ≤ N]·v`. -/
lemma sum_ite_valAdd (N c : ℕ) (v : ℂ) :
    (∑ j : Fin N, if (j : ℕ) + 1 = c then v else 0) = if 1 ≤ c ∧ c ≤ N then v else 0 := by
  by_cases hc : 1 ≤ c ∧ c ≤ N
  · obtain ⟨hc1, hcN⟩ := hc
    have hlt : c - 1 < N := by omega
    rw [if_pos ⟨hc1, hcN⟩, Finset.sum_eq_single (⟨c - 1, hlt⟩ : Fin N)]
    · rw [if_pos]; show c - 1 + 1 = c; omega
    · intro j _ hj
      rw [if_neg]
      intro h; exact hj (Fin.ext (by show (j : ℕ) = c - 1; omega))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    intro h; exact hc ⟨by omega, by have := j.isLt; omega⟩

/-- `(√n : ℂ)·(√n : ℂ) = n`. -/
lemma sqrt_mul_self_cast (n : ℕ) : (Real.sqrt n : ℂ) * (Real.sqrt n : ℂ) = (n : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  push_cast; ring

variable (N : ℕ)

/-! ### The ladder operators -/

/-- The **annihilation operator** on the `N`-level truncated oscillator:
`a·eₙ = √n·e_{n-1}` (and `a·e₀ = 0`). As a matrix, `a_{ij} = √j` when `i + 1 = j`,
else `0` (one super-diagonal of square roots). -/
noncomputable def annihilation : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if (i : ℕ) + 1 = (j : ℕ) then (Real.sqrt (j : ℕ) : ℂ) else 0

/-- The **creation operator** `a† = aᴴ`: `a†·eₙ = √(n+1)·e_{n+1}` (and
`a†·e_{N-1} = 0`, the truncation). -/
noncomputable def creation : Matrix (Fin N) (Fin N) ℂ := (annihilation N)ᴴ

/-- The **number operator** `N̂ = diag(0, 1, …, N−1)`. -/
noncomputable def numberOp : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => ((i : ℕ) : ℂ)

/-- The **top-level projector** `|N−1⟩⟨N−1|` = `diag(0, …, 0, 1)`, where the CCR
defect lives. -/
noncomputable def topProj : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) = N - 1 then 1 else 0

variable {N}

@[simp] lemma annihilation_apply (i j : Fin N) :
    annihilation N i j = if (i : ℕ) + 1 = (j : ℕ) then (Real.sqrt (j : ℕ) : ℂ) else 0 := rfl

@[simp] lemma creation_apply (i j : Fin N) :
    creation N i j = if (j : ℕ) + 1 = (i : ℕ) then (Real.sqrt (i : ℕ) : ℂ) else 0 := by
  rw [creation, Matrix.conjTranspose_apply, annihilation_apply]
  split_ifs with h
  · exact Complex.conj_ofReal _
  · exact star_zero _

/-! ### The two products -/

/-- **`a†a = N̂`**: creation ∘ annihilation is the number operator `diag(n)`. -/
theorem creation_mul_annihilation : creation N * annihilation N = numberOp N := by
  ext i k
  rw [Matrix.mul_apply, numberOp]
  rcases eq_or_ne i k with hik | hik
  · subst hik
    rw [Matrix.diagonal_apply, if_pos rfl]
    -- ∑_j [j+1=i]·√i · [j+1=i]·√i  =  (i:ℂ)
    have hconv : ∀ j : Fin N,
        creation N i j * annihilation N j i
          = if (j : ℕ) + 1 = (i : ℕ) then ((i : ℕ) : ℂ) else 0 := by
      intro j
      rw [creation_apply, annihilation_apply]
      by_cases h : (j : ℕ) + 1 = (i : ℕ)
      · rw [if_pos h, if_pos h, sqrt_mul_self_cast]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hconv j), sum_ite_valAdd]
    have hi : (i : ℕ) < N := i.isLt
    split_ifs with h
    · rfl
    · have h0 : (i : ℕ) = 0 := by omega
      rw [h0]; simp
  · rw [Matrix.diagonal_apply, if_neg hik]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [creation_apply, annihilation_apply]
    by_cases h1 : (j : ℕ) + 1 = (i : ℕ)
    · rw [if_neg (show ¬((j : ℕ) + 1 = (k : ℕ)) from fun h2 => hik (Fin.ext (by omega))),
        mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **`aa† = diag(1, 2, …, N−1, 0)`**: annihilation ∘ creation, the number
operator shifted up by one with a zero at the top level. -/
theorem annihilation_mul_creation :
    annihilation N * creation N
      = Matrix.diagonal fun i : Fin N => if (i : ℕ) + 1 < N then (((i : ℕ) + 1 : ℕ) : ℂ) else 0 := by
  ext i k
  rw [Matrix.mul_apply]
  rcases eq_or_ne i k with hik | hik
  · subst hik
    rw [Matrix.diagonal_apply, if_pos rfl]
    -- ∑_j [i+1=j]·√j · [i+1=j]·√j = if i+1<N then (i+1) else 0
    have hconv : ∀ j : Fin N,
        annihilation N i j * creation N j i
          = if (j : ℕ) = (i : ℕ) + 1 then (((i : ℕ) + 1 : ℕ) : ℂ) else 0 := by
      intro j
      rw [annihilation_apply, creation_apply]
      by_cases h : (i : ℕ) + 1 = (j : ℕ)
      · rw [if_pos h, if_pos h.symm, sqrt_mul_self_cast, h]
      · rw [if_neg h, if_neg (fun h2 => h h2.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hconv j), sum_ite_valEq]
  · rw [Matrix.diagonal_apply, if_neg hik]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [annihilation_apply, creation_apply]
    by_cases h1 : (i : ℕ) + 1 = (j : ℕ)
    · rw [if_neg (show ¬((k : ℕ) + 1 = (j : ℕ)) from fun h2 => hik (Fin.ext (by omega))),
        mul_zero]
    · rw [if_neg h1, zero_mul]

/-! ### The truncated CCR -/

/-- **The truncated CCR**: `[a, a†] = 1 − N·|N−1⟩⟨N−1|`. The canonical commutation
relation holds everywhere except a rank-one defect at the top Fock level. Both
sides have trace `0` (W4): `tr 1 = N` and `tr(N·|N−1⟩⟨N−1|) = N`. -/
theorem truncated_ccr :
    annihilation N * creation N - creation N * annihilation N = 1 - (N : ℂ) • topProj N := by
  rw [annihilation_mul_creation, creation_mul_annihilation, numberOp, topProj]
  ext i k
  simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hik : i = k
  · subst hik
    simp only [↓reduceIte]
    have hi : (i : ℕ) < N := i.isLt
    by_cases htop : (i : ℕ) + 1 < N
    · rw [if_pos htop, if_neg (show ¬((i : ℕ) = N - 1) by omega)]
      push_cast; ring
    · rw [if_neg htop, if_pos (show (i : ℕ) = N - 1 by omega)]
      rw [show (i : ℕ) = N - 1 by omega, Nat.cast_sub (by omega : 1 ≤ N)]
      push_cast; ring
  · simp [hik]

/-! ### The conjugate pair `Q`, `P` and the approximate CCR -/

variable (N)

/-- The **position quadrature** `Q = (a + a†)/√2`. -/
noncomputable def Q : Matrix (Fin N) (Fin N) ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (annihilation N + creation N)

/-- The **momentum quadrature** `P = (a − a†)/(i√2) = (−i/√2)·(a − a†)`. -/
noncomputable def P : Matrix (Fin N) (Fin N) ℂ :=
  (-Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (annihilation N - creation N)

variable {N}

/-- `√2·√2 = 2` in `ℂ`. -/
private lemma sqrt2_mul_sqrt2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- `√2 ≠ 0` in `ℂ`. -/
private lemma sqrt2_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  rw [Ne, Complex.ofReal_eq_zero]; positivity

/-- `Q` is Hermitian (a genuine self-adjoint observable). -/
theorem Q_isHermitian : (Q N).IsHermitian := by
  unfold Matrix.IsHermitian Q creation
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]

/-- `P` is Hermitian (a genuine self-adjoint observable). -/
theorem P_isHermitian : (P N).IsHermitian := by
  unfold Matrix.IsHermitian P creation
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose,
    show (annihilation N)ᴴ - annihilation N
        = -(annihilation N - (annihilation N)ᴴ) from (neg_sub _ _).symm,
    smul_neg, ← neg_smul]
  congr 1
  rw [Complex.star_def, map_mul, map_neg, Complex.conj_I, map_inv₀, Complex.conj_ofReal,
    neg_neg, neg_mul]

/-- **`[Q, P] = i·[a, a†]`**: the quadrature commutator is `i` times the ladder
commutator. -/
theorem QP_commutator :
    Q N * P N - P N * Q N
      = Complex.I • (annihilation N * creation N - creation N * annihilation N) := by
  unfold Q P
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_comm (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ (-Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹),
    ← smul_sub]
  have hop : (annihilation N + creation N) * (annihilation N - creation N)
        - (annihilation N - creation N) * (annihilation N + creation N)
      = (2 : ℂ) • (creation N * annihilation N - annihilation N * creation N) := by
    rw [two_smul]; noncomm_ring
  rw [hop, smul_smul,
    show annihilation N * creation N - creation N * annihilation N
        = -(creation N * annihilation N - annihilation N * creation N) from (neg_sub _ _).symm,
    smul_neg, ← neg_smul]
  congr 1
  rw [show -Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * 2
        = -Complex.I * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * 2 by ring,
    ← mul_inv, sqrt2_mul_sqrt2, mul_assoc, inv_mul_cancel₀ (two_ne_zero), mul_one]

/-- **The exact CCR on the low-energy sector.** For every Fock state below the top
level (`n ≠ N−1`), the quadratures satisfy the canonical commutation relation
exactly: `[Q, P]·eₙ = i·eₙ`. The defect (W4-forced) is confined to the top level,
so on any state with negligible top-level population `‖[Q,P] − i·1‖` is negligible. -/
theorem ccr_exact_on_bulk (j : Fin N) (hj : (j : ℕ) ≠ N - 1) :
    (Q N * P N - P N * Q N).mulVec (Pi.single j 1 : Fin N → ℂ)
      = Complex.I • (Pi.single j 1 : Fin N → ℂ) := by
  rw [QP_commutator, truncated_ccr, Matrix.smul_mulVec]
  congr 1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  have htop : (topProj N).mulVec (Pi.single j 1 : Fin N → ℂ) = 0 := by
    rw [topProj]
    funext i
    rw [Matrix.mulVec_diagonal, Pi.zero_apply, Pi.single_apply]
    by_cases h : i = j
    · subst h; rw [if_neg hj, zero_mul]
    · rw [if_neg h, mul_zero]
  rw [htop, smul_zero, sub_zero]

end CSD.CV
