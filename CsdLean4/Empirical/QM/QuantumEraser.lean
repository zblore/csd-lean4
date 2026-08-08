/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.Metrology.Ramsey

/-!
# Empirical/QM/QuantumEraser: the quantum eraser (complementarity + which-path erasure)

The **quantum eraser** demonstrates complementarity: entangling a system qubit (the two
interferometer paths) with a **which-path marker** qubit destroys interference — but *erasing* the
which-path information (measuring the marker in the conjugate basis) restores it, in the
marker-conditioned joint statistics.

Setup: the maximally-entangled path–marker state `|Φ⟩ = (|00⟩ + |11⟩)/√2`. The system is read in the
interference basis with interferometer phase `φ`, `|φ_a⟩ ∝ |0⟩ + a·e^{iφ}|1⟩` (`a = ±1`); the marker
in the erasing (conjugate) basis `|c⟩ ∝ |0⟩ + c|1⟩` (`c = ±1`). The Born joint probability is

  `P(a, c) = (1 + a·c·cos φ)/4`.

* `eraser_joint` — the joint probability `(1 + ac·cos φ)/4`: a `φ`-dependent **fringe** — interference
  is present in the marker-conditioned statistics (the erasure).
* `eraser_no_interference` — the **system marginal** `∑_c P(a,c) = 1/2`, independent of `φ`: **no**
  interference when the marker is ignored (the which-path information is present, not erased).
* `eraser_fringe_bright` / `eraser_fringe_dark` — `P(+,+) = 1/2` at `φ=0`, `= 0` at `φ=π`: the
  conditioned fringe has **visibility 1**.

The contrast — flat marginal vs full-visibility conditioned fringe — is the eraser. The "delayed
choice" version is the same statistics: whether to erase can be chosen after the system is read.

**Experimental verification:** Kim et al. 2000 (delayed-choice eraser); Scully–Drühl 1982 (proposal).
**CSD note:** the marker measurement is a de-isolation forming a record; erasure = reading that
record in the conjugate basis, which is why the interference is recoverable only in the conditioned
(post-selected) subensemble — no interference is ever "restored" to the ignored marginal.

## References
`Empirical/CSD/MachZehnderVolume.lean` (single-qubit interference fringe `cos²(φ/2)`);
`Empirical/QM/Hardy.lean` (the bipartite `jointAmplitude` pattern);
`Empirical/Metrology/Ramsey.lean` (`Complex.sq_norm` / `normSq_add_mul_I` amplitude idiom).
-/

@[expose] public section

open scoped ComplexConjugate

namespace CSD.Empirical.QM.QuantumEraser

/-- Joint amplitude `⟨a ⊗ b | ψ⟩` for a bipartite state `ψ : Fin 2 × Fin 2 → ℂ` and single-qubit
bras `a, b : Fin 2 → ℂ`. -/
noncomputable def jointAmplitude (a b : Fin 2 → ℂ) (ψ : Fin 2 × Fin 2 → ℂ) : ℂ :=
  ∑ p : Fin 2 × Fin 2, star (a p.1) * star (b p.2) * ψ p

/-- The (unnormalised) maximally-entangled path–marker state `|Φ⟩ = |00⟩ + |11⟩`. -/
def bellVec : Fin 2 × Fin 2 → ℂ
  | (⟨0, _⟩, ⟨0, _⟩) => 1
  | (⟨0, _⟩, ⟨1, _⟩) => 0
  | (⟨1, _⟩, ⟨0, _⟩) => 0
  | (⟨1, _⟩, ⟨1, _⟩) => 1

/-- The system interference-basis bra `|φ_a⟩ ∝ |0⟩ + a·e^{iφ}|1⟩` (unnormalised). -/
noncomputable def sysBra (φ : ℝ) (a : ℝ) : Fin 2 → ℂ :=
  ![1, (a : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)]

/-- The marker erasing-basis bra `|c⟩ ∝ |0⟩ + c|1⟩` (unnormalised, `c = ±1`). -/
def markBra (c : ℝ) : Fin 2 → ℂ := ![1, (c : ℂ)]

/-- **The Born joint probability** `P(a, c)` of system outcome `a` and marker outcome `c`, with the
`√2·√2·√2 = √8` normalisation of the three unit vectors baked in. -/
noncomputable def bornP (φ a c : ℝ) : ℝ :=
  ‖jointAmplitude (sysBra φ a) (markBra c) bellVec‖ ^ 2 / 8

/-- The joint amplitude `⟨φ_a ⊗ c | Φ⟩ = 1 + a·c·(cos φ − i·sin φ)` (`= 1 + ac·e^{−iφ}`). -/
lemma jointAmp_eq (φ a c : ℝ) :
    jointAmplitude (sysBra φ a) (markBra c) bellVec
      = 1 + (a : ℂ) * (c : ℂ) * ((Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I) := by
  simp only [jointAmplitude, Fintype.sum_prod_type, Fin.sum_univ_two, sysBra, markBra, bellVec,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, add_zero,
    zero_add, one_mul, Complex.star_def, map_mul, map_add, map_one, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- **The Born joint probability `P(a, c) = (1 + a·c·cos φ)/4`** for `a, c ∈ {±1}` — a `φ`-dependent
interference fringe (present in the marker-conditioned statistics: the erasure). -/
theorem eraser_joint (φ : ℝ) {a c : ℝ} (ha : a = 1 ∨ a = -1) (hc : c = 1 ∨ c = -1) :
    bornP φ a c = (1 + a * c * Real.cos φ) / 4 := by
  have hw : (1 : ℂ) + (a : ℂ) * (c : ℂ) * ((Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I)
      = (↑(1 + a * c * Real.cos φ) : ℂ) + (↑(-(a * c * Real.sin φ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [bornP, jointAmp_eq, hw, Complex.sq_norm, Complex.normSq_add_mul_I]
  rcases ha with ha | ha <;> rcases hc with hc | hc <;> subst ha <;> subst hc <;>
    linear_combination (1 / 8 : ℝ) * Real.sin_sq_add_cos_sq φ

/-- **No interference in the system marginal:** ignoring the marker, `∑_c P(a,c) = 1/2`, independent
of the interferometer phase `φ` — the which-path information is present (not erased), so no fringe. -/
theorem eraser_no_interference (φ : ℝ) {a : ℝ} (ha : a = 1 ∨ a = -1) :
    bornP φ a 1 + bornP φ a (-1) = 1 / 2 := by
  rw [eraser_joint φ ha (Or.inl rfl), eraser_joint φ ha (Or.inr rfl)]
  ring

/-- **Bright fringe (erased):** the marker-conditioned joint `P(+,+) = 1/2` at zero phase. -/
theorem eraser_fringe_bright : bornP 0 1 1 = 1 / 2 := by
  rw [eraser_joint 0 (Or.inl rfl) (Or.inl rfl), Real.cos_zero]; norm_num

/-- **Dark fringe (erased):** `P(+,+) = 0` at phase `π` — the conditioned fringe has visibility `1`
(ranging over the full `[0, 1/2]`), in contrast to the flat marginal. -/
theorem eraser_fringe_dark : bornP Real.pi 1 1 = 0 := by
  rw [eraser_joint Real.pi (Or.inl rfl) (Or.inl rfl), Real.cos_pi]; norm_num

end CSD.Empirical.QM.QuantumEraser
