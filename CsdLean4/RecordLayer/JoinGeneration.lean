/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.JoinArena
public import CsdLean4.RecordLayer.RelocationObstruction
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# SigmaLayer/JoinGeneration: the join relocation *is* generated

**Category:** dynamical measurement — the positive answer the swap
architecture could not give.

`RelocationObstruction.lean` showed the bank-swap collapse stroke cannot be
the time-one map of any flow, in two independent horns: a factor exchange of
a product arena is not homotopic to the identity, and the non-permutation
repair is not injective. This module shows the **join** architecture escapes
both, and escapes them for a structural reason rather than by luck.

## Why the join escapes

The bank arena is a **product**, `(Σ × pointer) × (Fin N → Σ)`, and
`pointerBankSwap` exchanges two of its factors. The join arena is
`ℂℙ^{N+N-1}`, a **single** projective space: `joinSwap b i p = joinU b i • p`
is the action of one unitary on one connected space. There are no two arena
factors to exchange, so horn one has nothing to act on, and a projective
unitary is bijective, so horn two has nothing to act on either.

That is the negative half. The positive half is that the escape is
constructive:

* `joinMat_mul_self` — the join permutation matrix is an **involution**, and
  `joinMat_conjTranspose` says it is **Hermitian**. So its eigenvalues are
  `±1`.
* `joinProj` — hence `Q = ½(1 - P)` is a Hermitian **idempotent**, the
  spectral projection onto the `-1` eigenspace.
* `joinFlowMat` — hence `U(t) = (1 - Q) + e^{iπt}Q` is a one-parameter family
  of unitaries with `U 0 = 1` and `U 1 = P`.
* ★★ `joinFlowMat_hasDerivAt` — and it solves the Schrödinger equation
  `U'(t) = (i·H)·U(t)` for the **explicit Hermitian generator** `H = π·Q`.
* ★★ `joinSwap_eq_flowTimeOne` — so the join relocation is the time-one map of
  a Hamiltonian flow.

No matrix exponential is needed: on an idempotent the exponential series
collapses to `1 + (e^z - 1)Q`, and writing that closed form down directly
turns the whole construction into algebra.

## What this settles

Collapse **can** be dynamics. `PointerGeneration.lean` generated the
record-creating stroke; this generates a relocation stroke. The obstruction in
`RelocationObstruction.lean` is therefore genuinely about the *swap
architecture*, exactly as its scope note claimed, and not about
collapse-as-dynamics in general.

The design rule it yields is sharp: a generated relocation must be a bijection
that is not a factor exchange, and the join route satisfies both by being a
unitary on an irreducible arena rather than a permutation of coordinates on a
reducible one.

⚠️ **Scope.** This generates the join *swap*, which is the relocation half of
the degenerate-Lüders witness (`JoinLuders.lean`). It does not by itself make
the whole two-stroke composite a single flow: the composite is still triggered
by a readout, and the trigger is where `no_everywhere_correlation` bites. What
is now established is that the *relocation* is not the obstacle.

## References

`RecordLayer/JoinArena.lean` (`joinMat`, `joinU`, `joinSwap`,
`joinSwap_measurePreserving`); `RecordLayer/JoinLuders.lean`
(`joinWitness_blockLuders`); `RecordLayer/RelocationObstruction.lean` (the two
horns this escapes); `RecordLayer/PointerGeneration.lean`
(`rampedU_schrodinger`, the record-stroke analogue); `specs/BACKLOG.md`.
-/

@[expose] public section

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace CSD.RecordLayer

variable {N K : ℕ}

/-! ### The join permutation is a Hermitian involution -/

/-- The join permutation matrix is **Hermitian**: it is real, and the
underlying permutation is an involution, so it is its own transpose. -/
theorem joinMat_conjTranspose (b : Fin N → Fin K) (i : Fin K) :
    (joinMat b i)ᴴ = joinMat b i := by
  funext j k
  simp only [Matrix.conjTranspose_apply, joinMat, Matrix.of_apply,
    apply_ite (star : ℂ → ℂ), star_one, star_zero]
  by_cases h : j = joinPerm b i k
  · rw [if_pos h, if_pos (by rw [h, joinPerm_involutive b i k])]
  · rw [if_neg h, if_neg (fun hk => h (by rw [hk, joinPerm_involutive b i j]))]

/-- The join permutation matrix is an **involution**. Being unitary and
Hermitian, it squares to the identity. -/
theorem joinMat_mul_self (b : Fin N → Fin K) (i : Fin K) :
    joinMat b i * joinMat b i = 1 := by
  have hu := joinMat_mem_unitaryGroup b i
  rw [Matrix.mem_unitaryGroup_iff] at hu
  calc joinMat b i * joinMat b i = joinMat b i * star (joinMat b i) := by
        rw [Matrix.star_eq_conjTranspose, joinMat_conjTranspose]
    _ = 1 := hu

/-! ### The spectral projection onto the `-1` eigenspace -/

/-- `Q = ½(1 - P)`: the spectral projection onto the `-1` eigenspace of the
join permutation. -/
noncomputable def joinProj (b : Fin N → Fin K) (i : Fin K) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℂ :=
  (1 / 2 : ℂ) • (1 - joinMat b i)

theorem joinProj_conjTranspose (b : Fin N → Fin K) (i : Fin K) :
    (joinProj b i)ᴴ = joinProj b i := by
  rw [joinProj, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, joinMat_conjTranspose]
  norm_num

/-- `Q` is **idempotent**, from `P² = 1`. -/
theorem joinProj_mul_self (b : Fin N → Fin K) (i : Fin K) :
    joinProj b i * joinProj b i = joinProj b i := by
  have hsq : (1 - joinMat b i) * (1 - joinMat b i) = (2 : ℂ) • (1 - joinMat b i) := by
    rw [sub_mul, mul_sub, mul_sub, joinMat_mul_self, one_mul, mul_one, two_smul]
    noncomm_ring
  rw [joinProj, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul]
  norm_num

/-- The complementary projection annihilates `Q`. -/
theorem one_sub_joinProj_mul (b : Fin N → Fin K) (i : Fin K) :
    (1 - joinProj b i) * joinProj b i = 0 := by
  rw [sub_mul, one_mul, joinProj_mul_self, sub_self]

theorem joinProj_mul_one_sub (b : Fin N → Fin K) (i : Fin K) :
    joinProj b i * (1 - joinProj b i) = 0 := by
  rw [mul_sub, mul_one, joinProj_mul_self, sub_self]

theorem one_sub_joinProj_mul_self (b : Fin N → Fin K) (i : Fin K) :
    (1 - joinProj b i) * (1 - joinProj b i) = 1 - joinProj b i := by
  rw [sub_mul, one_mul, joinProj_mul_one_sub, sub_zero]

/-! ### The flow -/

/-- ★ **The join flow.** `U(t) = (1 - Q) + e^{iπt}Q`, the phase rotation that
acts trivially on the `+1` eigenspace and by `e^{iπt}` on the `-1` eigenspace.

This is `exp(itπQ)` in closed form: on an idempotent the exponential series
collapses to `1 + (e^z - 1)Q`, so no matrix exponential is needed. -/
noncomputable def joinFlowMat (b : Fin N → Fin K) (i : Fin K) (t : ℝ) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℂ :=
  (1 - joinProj b i) + Complex.exp (Real.pi * Complex.I * t) • joinProj b i

@[simp] theorem joinFlowMat_zero (b : Fin N → Fin K) (i : Fin K) :
    joinFlowMat b i 0 = 1 := by
  rw [joinFlowMat]
  norm_num

/-- ★ **At time one the flow *is* the join permutation**, because `e^{iπ} = -1`
turns `(1 - Q) - Q = 1 - 2Q` back into `P`. -/
@[simp] theorem joinFlowMat_one (b : Fin N → Fin K) (i : Fin K) :
    joinFlowMat b i 1 = joinMat b i := by
  rw [joinFlowMat, joinProj]
  push_cast
  rw [mul_one, Complex.exp_pi_mul_I]
  module

/-- The scalar factor has modulus one. -/
theorem conj_exp_mul_exp (t : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Real.pi * Complex.I * t))
      * Complex.exp (Real.pi * Complex.I * t) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp [Complex.conj_I, mul_comm]

/-- ★ **The flow is unitary at every time.** -/
theorem joinFlowMat_mem_unitaryGroup (b : Fin N → Fin K) (i : Fin K) (t : ℝ) :
    joinFlowMat b i t ∈ Matrix.unitaryGroup (Fin (N + N)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hQH := joinProj_conjTranspose b i
  have hstar : star (joinFlowMat b i t)
      = (1 - joinProj b i)
        + (starRingEnd ℂ) (Complex.exp (Real.pi * Complex.I * t)) • joinProj b i := by
    rw [Matrix.star_eq_conjTranspose, joinFlowMat, Matrix.conjTranspose_add,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hQH]
    rfl
  have e2 : (1 - joinProj b i) * (Complex.exp (Real.pi * Complex.I * t) • joinProj b i) = 0 := by
    rw [Matrix.mul_smul, one_sub_joinProj_mul, smul_zero]
  have e3 : ((starRingEnd ℂ) (Complex.exp (Real.pi * Complex.I * t)) • joinProj b i)
      * (1 - joinProj b i) = 0 := by
    rw [Matrix.smul_mul, joinProj_mul_one_sub, smul_zero]
  have e4 : ((starRingEnd ℂ) (Complex.exp (Real.pi * Complex.I * t)) • joinProj b i)
      * (Complex.exp (Real.pi * Complex.I * t) • joinProj b i) = joinProj b i := by
    rw [Matrix.smul_mul, Matrix.mul_smul, joinProj_mul_self, smul_smul, conj_exp_mul_exp,
      one_smul]
  rw [hstar, joinFlowMat, add_mul, mul_add, mul_add,
    one_sub_joinProj_mul_self, e2, e3, e4]
  abel

/-- The join flow as a family of unitaries. -/
noncomputable def joinFlowU (b : Fin N → Fin K) (i : Fin K) (t : ℝ) :
    Matrix.unitaryGroup (Fin (N + N)) ℂ :=
  ⟨joinFlowMat b i t, joinFlowMat_mem_unitaryGroup b i t⟩

/-! ### The generator -/

/-- The **Hermitian generator** `H = π·Q` of the join flow. -/
noncomputable def joinGen (b : Fin N → Fin K) (i : Fin K) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℂ :=
  (Real.pi : ℂ) • joinProj b i

theorem joinGen_conjTranspose (b : Fin N → Fin K) (i : Fin K) :
    (joinGen b i)ᴴ = joinGen b i := by
  rw [joinGen, Matrix.conjTranspose_smul, joinProj_conjTranspose]
  simp

theorem joinGen_isHermitian (b : Fin N → Fin K) (i : Fin K) :
    (joinGen b i).IsHermitian := joinGen_conjTranspose b i

/-- The scalar path's derivative. -/
theorem hasDerivAt_expPath (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Real.pi * Complex.I * s))
      (Real.pi * Complex.I * Complex.exp (Real.pi * Complex.I * t)) t := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * w))
      ((Real.pi : ℂ) * Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (t : ℂ)))
      (t : ℂ) := by
    have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * Complex.I * w)
        ((Real.pi : ℂ) * Complex.I) (t : ℂ) := by
      simpa using (hasDerivAt_id ((t : ℂ))).const_mul ((Real.pi : ℂ) * Complex.I)
    simpa [mul_comm] using hlin.cexp
  exact he.comp_ofReal

/-- ★★ **The join flow solves the Schrödinger equation** for the explicit
Hermitian generator `H = π·Q`:

    `U'(t) = (i·H)·U(t)`.

This is the join-architecture analogue of `rampedU_schrodinger`, and it is what
`pointerBankSwap` provably cannot have. -/
theorem joinFlowMat_hasDerivAt (b : Fin N → Fin K) (i : Fin K) (t : ℝ) :
    HasDerivAt (joinFlowMat b i)
      ((Complex.I • joinGen b i) * joinFlowMat b i t) t := by
  have hd : HasDerivAt (joinFlowMat b i)
      ((Real.pi * Complex.I * Complex.exp (Real.pi * Complex.I * t)) • joinProj b i) t :=
    ((hasDerivAt_expPath t).smul_const (joinProj b i)).const_add (1 - joinProj b i)
  refine hd.congr_deriv ?_
  rw [joinGen, joinFlowMat, smul_smul, Matrix.smul_mul, mul_add,
    joinProj_mul_one_sub, Matrix.mul_smul, joinProj_mul_self, zero_add, smul_smul]
  congr 1
  ring

/-! ### The payoff: the join relocation is a flow at time one -/

/-- ★★ **The join relocation is the time-one map of a Hamiltonian flow.**

`joinSwap` acts as `joinU • p`, and `joinU` is `joinFlowU 1` for a flow that
starts at the identity and is generated by the Hermitian `joinGen`. So the
collapse stroke of the join architecture *is* dynamics, in exactly the sense
`RelocationObstruction.lean` proves the bank-swap stroke can never be. -/
theorem joinSwap_eq_flowTimeOne (b : Fin N → Fin K) (i : Fin K)
    (p : LF4.CPN (N + N)) :
    joinSwap b i p = (joinFlowU b i 1) • p := by
  rw [joinSwap, joinFlowU, joinU]
  congr 2
  exact (joinFlowMat_one b i).symm

/-- The flow starts at the identity, so it genuinely joins `id` to the
relocation. -/
theorem joinFlowU_zero_smul (b : Fin N → Fin K) (i : Fin K) (p : LF4.CPN (N + N)) :
    (joinFlowU b i 0) • p = p := by
  have h : joinFlowU b i 0 = 1 := by
    apply Subtype.ext
    exact joinFlowMat_zero b i
  rw [h, one_smul]

end CSD.RecordLayer
