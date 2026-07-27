/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Gates.SingleQubit

/-!
# Empirical/QM: the Hong–Ou–Mandel effect (two-photon interference)

**Category:** 3-Local (QM-validity content, no CSD ontology).

Two identical photons enter a 50:50 beamsplitter, one at each input port. Classically they
should exit in different ports half the time. Quantum mechanically the coincidence rate is
**exactly zero**: the photons always leave together. This is the Hong–Ou–Mandel dip
(Hong–Ou–Mandel 1987), and it is the cleanest experimental signature of **bosonic exchange
symmetry** — nothing about the beamsplitter itself produces it.

## The two-particle amplitude matrix

A two-particle state of a two-mode system is an amplitude matrix `S`, where `S i j` is the
amplitude for the first particle in mode `i` and the second in mode `j`. A mode transformation
`U` acts on it as `S ↦ U · S · Uᵀ` (`bsTwo`) — the induced action on a 2-tensor. The
beamsplitter is the Hadamard `qmH` of `Empirical/QM/Gates/SingleQubit.lean`: real, symmetric,
involutive — exactly a 50:50 splitter.

The exchange symmetry of the input is what distinguishes the three cases, and *only* that:

| input | `S` | statistics |
|---|---|---|
| `bosonIn` | symmetric, `(\|01⟩+\|10⟩)/√2` | bosons |
| `fermionIn` | antisymmetric, `(\|01⟩−\|10⟩)/√2` | fermions |
| `distinctIn` | neither, `\|01⟩` | distinguishable particles |

All three are unit vectors, all three see the *same* beamsplitter, and all three describe "one
particle in each input port". They differ only in exchange symmetry.

## What this file proves

* `bsTwo_bosonIn` — the output amplitude matrix is `!![s, 0; 0, −s]`: the off-diagonal
  (coincidence) entries **cancel identically**.
* `hom_coincidence_zero` — **the HOM dip**: `coincidenceProb = 0`. The two photons are never
  found in different output ports.
* `hom_bunching_one` — equivalently `bunchingProb = 1`; they always leave together, in an equal
  superposition of "both left" and "both right".
* `distinct_coincidence_half` — the classical baseline: distinguishable particles coincide with
  probability `½`. This is what the dip is a dip *below*.
* `fermion_coincidence_one` — the opposite extreme: fermions **always** anti-bunch (the Pauli
  exclusion statement for this geometry), `coincidenceProb = 1`.
* `hom_dip` — `0 < ½`, the dip is real and not an artefact of normalisation.
* `hom_exchange_trichotomy` — the capstone: `0 < ½ < 1` across boson / distinguishable /
  fermion with the beamsplitter and the input ports held fixed. Since the three inputs differ
  *only* in exchange symmetry, the coincidence rate is a direct readout of particle statistics.

The cancellation is visible in the algebra: for the symmetric input the two exchange paths
("both transmitted" and "both reflected") contribute with opposite sign, and `qmH` is
normalised so that they cancel exactly. Formally the whole effect is the single fact that
`H · σₓ · H` is **diagonal**.

## Scope

This is the two-particle sector of two modes — no Fock space, no field operators. That is
enough for HOM, whose content lives entirely in the two-photon amplitude. The bosonic
*creation-operator* formulation (`a†b† → ½(a†² − b†²)`) is the same computation in another
notation; the amplitude-matrix form avoids the unbounded-operator machinery that
`CV/ApproxCCR.lean` shows a finite model cannot carry exactly.

## References

`Empirical/QM/Gates/SingleQubit.lean` (`qmH`, `qmH_mul_self` — the beamsplitter);
`CV/FieldModes.lean` (the multi-mode field, for the Fock-space direction);
`CV/ApproxCCR.lean` (`no_exact_finite_ccr`, why creation operators stay out of the finite model);
`Empirical/QM/Bell.lean` (the build pattern); `specs/BACKLOG.md`; `specs/future-work.md`.
Hong, Ou, Mandel, *Phys. Rev. Lett.* **59**, 2044 (1987).
-/

@[expose] public section

open Matrix

namespace CSD.Empirical
namespace HOM

open CSD.Empirical.QM.Gates

/-! ### Scalars -/

/-- The amplitude `1/√2`. -/
noncomputable def rt2inv : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem rt2inv_mul_self : rt2inv * rt2inv = (1 / 2 : ℂ) := by
  rw [rt2inv, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem norm_rt2inv_sq : ‖rt2inv‖ ^ 2 = 1 / 2 := by
  rw [rt2inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ### The beamsplitter and its two-particle action -/

/-- The Hadamard written out entrywise — a real, symmetric, involutive 50:50 beamsplitter. -/
theorem qmH_eq_entries : qmH = !![rt2inv, rt2inv; rt2inv, -rt2inv] := by
  unfold qmH rt2inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem qmH_transpose : qmHᵀ = qmH := by
  rw [qmH_eq_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The **beamsplitter's action on a two-particle amplitude matrix**, `S ↦ U · S · Uᵀ`. -/
noncomputable def bsTwo (S : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  qmH * S * qmHᵀ

theorem bsTwo_eq (S : Matrix (Fin 2) (Fin 2) ℂ) : bsTwo S = qmH * S * qmH := by
  rw [bsTwo, qmH_transpose]

/-! ### The three inputs — identical but for exchange symmetry -/

/-- **Bosons**: the symmetrised input `(|01⟩ + |10⟩)/√2`, one photon in each port. -/
noncomputable def bosonIn : Matrix (Fin 2) (Fin 2) ℂ := !![0, rt2inv; rt2inv, 0]

/-- **Fermions**: the antisymmetrised input `(|01⟩ − |10⟩)/√2`. -/
noncomputable def fermionIn : Matrix (Fin 2) (Fin 2) ℂ := !![0, rt2inv; -rt2inv, 0]

/-- **Distinguishable particles**: the unsymmetrised input `|01⟩` — particle one in mode `0`,
particle two in mode `1`. -/
noncomputable def distinctIn : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The **coincidence probability**: the two particles leave in *different* output ports. -/
noncomputable def coincidenceProb (S : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖S 0 1‖ ^ 2 + ‖S 1 0‖ ^ 2

/-- The **bunching probability**: the two particles leave in the *same* output port. -/
noncomputable def bunchingProb (S : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖S 0 0‖ ^ 2 + ‖S 1 1‖ ^ 2

/-- All three inputs are unit vectors: they are genuinely comparable states. -/
theorem inputs_normalised :
    coincidenceProb bosonIn + bunchingProb bosonIn = 1 ∧
    coincidenceProb fermionIn + bunchingProb fermionIn = 1 ∧
    coincidenceProb distinctIn + bunchingProb distinctIn = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [coincidenceProb, bunchingProb, bosonIn, fermionIn, distinctIn, norm_rt2inv_sq] <;>
    norm_num

/-! ### The Hong–Ou–Mandel dip -/

/-- **The output of the symmetric input is purely bunched**: `H · σₓ · H` is diagonal, so the
coincidence amplitudes cancel identically. This single matrix identity *is* the HOM effect. -/
theorem bsTwo_bosonIn : bsTwo bosonIn = !![rt2inv, 0; 0, -rt2inv] := by
  rw [bsTwo_eq, qmH_eq_entries, bosonIn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rt2inv_mul_self] <;> ring

/-- **The Hong–Ou–Mandel dip.** Two identical bosons entering opposite ports of a 50:50
beamsplitter are *never* found in different output ports. -/
theorem hom_coincidence_zero : coincidenceProb (bsTwo bosonIn) = 0 := by
  rw [coincidenceProb, bsTwo_bosonIn]
  norm_num

/-- **Photon bunching.** Equivalently, they always leave together — in an equal superposition
of "both to the left" and "both to the right". -/
theorem hom_bunching_one : bunchingProb (bsTwo bosonIn) = 1 := by
  rw [bunchingProb, bsTwo_bosonIn]
  simp [norm_rt2inv_sq]
  norm_num

/-! ### The two comparison cases -/

/-- Distinguishable particles: each independently transmits or reflects. -/
theorem bsTwo_distinctIn : bsTwo distinctIn = !![1 / 2, -(1 / 2); 1 / 2, -(1 / 2)] := by
  rw [bsTwo_eq, qmH_eq_entries, distinctIn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rt2inv_mul_self]

/-- **The classical baseline `½`.** Distinguishable particles coincide half the time — this is
the level the HOM dip drops below. -/
theorem distinct_coincidence_half : coincidenceProb (bsTwo distinctIn) = 1 / 2 := by
  rw [coincidenceProb, bsTwo_distinctIn]
  norm_num

/-- Fermions: the antisymmetric input picks up `det U = −1` and is returned unchanged up to
sign, so its coincidence amplitude is *preserved*, not cancelled. -/
theorem bsTwo_fermionIn : bsTwo fermionIn = !![0, -rt2inv; rt2inv, 0] := by
  rw [bsTwo_eq, qmH_eq_entries, fermionIn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rt2inv_mul_self] <;> ring

/-- **Fermionic anti-bunching.** Two fermions in the same geometry leave in different ports with
probability `1` — the Pauli exclusion statement for a beamsplitter, and the exact opposite of
the bosonic case. -/
theorem fermion_coincidence_one : coincidenceProb (bsTwo fermionIn) = 1 := by
  rw [coincidenceProb, bsTwo_fermionIn]
  simp [norm_rt2inv_sq]
  norm_num

/-! ### The capstone -/

/-- **The dip is real.** The bosonic coincidence rate is strictly below the classical one. -/
theorem hom_dip : coincidenceProb (bsTwo bosonIn) < coincidenceProb (bsTwo distinctIn) := by
  rw [hom_coincidence_zero, distinct_coincidence_half]
  norm_num

/-- **Exchange symmetry is read out directly by the coincidence rate.**

With the beamsplitter and the input ports held fixed, and the three inputs differing *only* in
their exchange symmetry, the coincidence probability is `0` for bosons, `½` for distinguishable
particles and `1` for fermions. Bunching and anti-bunching are therefore statements about
particle statistics, not about the optics. -/
theorem hom_exchange_trichotomy :
    coincidenceProb (bsTwo bosonIn) < coincidenceProb (bsTwo distinctIn) ∧
    coincidenceProb (bsTwo distinctIn) < coincidenceProb (bsTwo fermionIn) ∧
    coincidenceProb (bsTwo bosonIn) = 0 ∧
    coincidenceProb (bsTwo distinctIn) = 1 / 2 ∧
    coincidenceProb (bsTwo fermionIn) = 1 := by
  refine ⟨hom_dip, ?_, hom_coincidence_zero, distinct_coincidence_half,
    fermion_coincidence_one⟩
  rw [distinct_coincidence_half, fermion_coincidence_one]
  norm_num

end HOM
end CSD.Empirical
