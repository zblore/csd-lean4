/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Propagator
public import CsdLean4.Thermo.FreeEnergy

/-!
# CV-24: the thermal tier at the cutoff — Gibbs field state, thermal propagator, exact KMS

**Category:** CV (continuous variables — the multi-mode field at finite temperature).

The first join of the two complete verticals: the Thermo track's Gibbs state (TH3,
`Thermo/FreeEnergy.lean`) instantiated on the CV track's free-field Hamiltonian. Every
temperature statement below is about **that** state — the object the TH3 variational
principle governs — not a separately posited Boltzmann matrix.

* `thermalFieldState β` — `gibbsState (fieldHamiltonian K N) _ β`, THE TH3 Gibbs state on
  the field. Because `fieldHamiltonian` is diagonal, the state has a **closed form**:
  ★ `thermalFieldState_eq` — the diagonal Boltzmann matrix with weights
  `exp(-β·E(c)) / fieldPartition`, obtained through `cfc_eq_conj_diagonal` at the
  trivial unitary; `fieldPartition_eq_partitionFn` reconciles the configuration-basis
  partition function with TH3's eigenvalue form via the trace normalisation.
* `fieldPartition_eq_pow` — the partition function **factorises over modes**,
  `Z_field = z_osc^K`, and ★ `thermalExpect_modeOp` is the **thermal mode marginal**: the
  thermal expectation of a single-mode observable is its single-mode Gibbs expectation —
  the thermal analogue of `modeMarginal_tprod_unit`.
* `thermalEvolve z` — Heisenberg evolution at **complex time**, entrywise
  `e^{iz(E_c − E_d)}·A_{cd}`; total and well-defined at every `z : ℂ` because the
  Hamiltonian is diagonal and the dimension finite — no analytic-continuation apparatus.
  `thermalEvolve_real_eq_heisenberg` ties the real-time slice to the CV chain's own
  stroboscopic evolution `heisenberg (freeFieldU τ ^ n)`.
* ★★ `thermal_kms` — **exact KMS at the cutoff**, the corpus's first KMS statement:
  `⟨A(t)·B⟩_β = ⟨B·A(t+iβ)⟩_β` for all matrices `A, B`, all `t, β`. At finite dimension
  with a diagonal Hamiltonian the identity is an entrywise exponential shuffle — the
  weight transport `w_c = w_d·e^{-β(E_c−E_d)}` — exactly as the Stage-7 feasibility
  check predicted.
* `thermalTwoPoint β τ n k l` — the thermal two-point function of the quadratures,
  `⟨Q_k(n)·Q_l⟩_β` under the free stroboscopic dynamics. `thermalTwoPoint_offdiag`:
  modes do not mix thermally (`= 0` for `k ≠ l` — the thermal companion of the vacuum
  propagator's `δ_{kl}`). ★ `thermalTwoPoint_diag` — the **closed form**: a single-mode
  Boltzmann average of one up-step and one down-step,

    `⟨Q_k(n)Q_k⟩_β = (1/z_osc)·∑_a e^{-β(a+½)}·( (a+1)/2·e^{-inτ}·[a+1<N] + a/2·e^{+inτ} )`,

  with the **truncation edge explicit**: the top level `a = N−1` has no up-step, so the
  `[a+1<N]` guard is the same truncation honesty the vacuum four-point's `2 < N` carries.
* ★ `thermalTwoPoint_tendsto_vacuum` — **the vacuum limit**: as `β → ∞` the thermal
  propagator converges to `freeTwoPoint` — the zero-point energies cancel between
  numerator and partition function, the reduced weights are geometric, and the ground
  level dominates. Finite sums only; no dominated convergence.

## Honest scope

The free (mode-diagonal) drive only, matching `freeTwoPoint`'s scope; interacting
corrections are priced by the CV-9/CV-12 ladder and not restated thermally. No continuum
limit (`ApproxCCR.no_exact_finite_ccr` stands) and no thermodynamic limit in `K`: every
statement is at the finite cutoff, where it is *exact*. The relativistic reading is the
same substitution as CV-13 (`relFieldHamiltonian`, spacing `ω(m,p)`), recorded not
restated. The `β → ∞` vacuum limit is
landed (`thermalTwoPoint_tendsto_vacuum`), so CV-24 carries no recorded residue.

## References

`specs/eft-stage7-plan.md` (row CV-24, the feasibility record this executes);
`specs/BACKLOG.md` (Q21); `Thermo/FreeEnergy.lean` (`gibbsState`, `gibbsWeight`,
`partitionFn`, `gibbsState_trace`); `Mathlib/QuantumInfo/Subadditivity.lean`
(`cfc_eq_conj_diagonal`); `CV/Propagator.lean` (`freeTwoPoint`, the walk-collapse
idiom, `diag_entry_mul_of_disjointSupport`); `CV/DynamicalLocality.lean`
(`heisenberg`, `heisenberg_phaseDiagU_apply`); `CV/FreeFieldFloquet.lean`
(`phaseDiagU`, `freeFieldU`); `CV/InteractionPrice.lean`
(`fieldHamiltonian_isHermitian`).
-/

@[expose] public section

open Matrix QuantumInfo
open CSD.Thermo

namespace CSD.CV

variable {K N : ℕ}

/-! ## The thermal field state and its closed form -/

/-- **The thermal field state**: the TH3 Gibbs state `ρ_β = e^{-βH}/Z` instantiated on
the free-field Hamiltonian — the Thermo↔CV join. -/
noncomputable def thermalFieldState (K N : ℕ) (β : ℝ) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  gibbsState (fieldHamiltonian K N) (fieldHamiltonian_isHermitian K N) β

/-- The configuration-basis partition function `∑_c e^{-β·E(c)}`. -/
noncomputable def fieldPartition (β : ℝ) (K N : ℕ) : ℝ :=
  ∑ c : FieldConfig K N, Real.exp (-β * fieldEnergy c)

/-- The single-mode partition function `z = ∑_m e^{-β·(m+½)}`. -/
noncomputable def oscPartition (β : ℝ) (N : ℕ) : ℝ :=
  ∑ m : Fin N, Real.exp (-β * oscEnergy m)

/-- The Boltzmann weight of a configuration. -/
noncomputable def thermalWeight (β : ℝ) (c : FieldConfig K N) : ℝ :=
  Real.exp (-β * fieldEnergy c) / fieldPartition β K N

lemma oscPartition_pos [NeZero N] (β : ℝ) : 0 < oscPartition β N :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The Gibbs state of the diagonal Hamiltonian is diagonal, with the Gibbs weights of
the configuration energies on the diagonal — `cfc_eq_conj_diagonal` at `U = 1`. -/
lemma thermalFieldState_eq_gibbs_diagonal (β : ℝ) :
    thermalFieldState K N β
      = Matrix.diagonal (fun c => ((gibbsWeight (fieldHamiltonian K N)
          (fieldHamiltonian_isHermitian K N) β (fieldEnergy c) : ℝ) : ℂ)) := by
  have h := cfc_eq_conj_diagonal (n := FieldConfig K N)
    (M := fieldHamiltonian K N) (U := 1)
    (fieldHamiltonian_isHermitian K N)
    (by simp)
    (fun c => fieldEnergy c)
    (by simp [fieldHamiltonian])
    (gibbsWeight (fieldHamiltonian K N) (fieldHamiltonian_isHermitian K N) β)
  simpa [thermalFieldState, gibbsState] using h

/-- The configuration-basis partition function agrees with TH3's eigenvalue form —
extracted from the trace normalisation `Tr ρ_β = 1`. -/
lemma fieldPartition_eq_partitionFn [NeZero N] (β : ℝ) :
    fieldPartition β K N
      = partitionFn (fieldHamiltonian K N) (fieldHamiltonian_isHermitian K N) β := by
  have : Nonempty (FieldConfig K N) := ⟨fun _ => 0⟩
  have htr := gibbsState_trace (fieldHamiltonian K N) (fieldHamiltonian_isHermitian K N) β
  rw [show gibbsState (fieldHamiltonian K N) (fieldHamiltonian_isHermitian K N) β
      = thermalFieldState K N β from rfl, thermalFieldState_eq_gibbs_diagonal,
    Matrix.trace_diagonal] at htr
  have hreal : (∑ c : FieldConfig K N, gibbsWeight (fieldHamiltonian K N)
      (fieldHamiltonian_isHermitian K N) β (fieldEnergy c)) = 1 := by
    have : ((∑ c : FieldConfig K N, gibbsWeight (fieldHamiltonian K N)
        (fieldHamiltonian_isHermitian K N) β (fieldEnergy c) : ℝ) : ℂ) = 1 := by
      push_cast at htr ⊢
      exact htr
    exact_mod_cast this
  have hZpos := partitionFn_pos (fieldHamiltonian K N) (fieldHamiltonian_isHermitian K N) β
  unfold gibbsWeight at hreal
  rw [← Finset.sum_div, div_eq_one_iff_eq hZpos.ne'] at hreal
  exact hreal

/-- ★ **The thermal field state, in closed form**: the diagonal Boltzmann matrix. -/
theorem thermalFieldState_eq [NeZero N] (β : ℝ) :
    thermalFieldState K N β
      = Matrix.diagonal (fun c => ((thermalWeight β c : ℝ) : ℂ)) := by
  rw [thermalFieldState_eq_gibbs_diagonal]
  congr 1
  funext c
  rw [thermalWeight, gibbsWeight, fieldPartition_eq_partitionFn]

/-! ## Thermal expectations -/

/-- The thermal expectation `⟨A⟩_β = Tr(ρ_β A)`. -/
noncomputable def thermalExpect (β : ℝ) (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    ℂ :=
  (thermalFieldState K N β * A).trace

/-- The thermal expectation is the Boltzmann-weighted diagonal sum. -/
theorem thermalExpect_eq [NeZero N] (β : ℝ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    thermalExpect β A = ∑ c, ((thermalWeight β c : ℝ) : ℂ) * A c c := by
  rw [thermalExpect, thermalFieldState_eq, Matrix.trace]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul]

/-! ## Complex-time evolution and exact KMS -/

/-- **Heisenberg evolution at complex time** under the free-field Hamiltonian,
entrywise `e^{iz(E_c − E_d)}·A_{cd}`. Total at every `z : ℂ`: the Hamiltonian is
diagonal and the dimension finite, so no analytic continuation is involved. -/
noncomputable def thermalEvolve (z : ℂ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  Matrix.of fun c d =>
    Complex.exp (Complex.I * z * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ)))
      * A c d

/-- The Heisenberg entry formula for the `n`-period free evolution, in phase-difference
form. -/
lemma heisenberg_freeFieldU_pow_apply (τ : ℝ) (n : ℕ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (c d : FieldConfig K N) :
    heisenberg (freeFieldU K N τ ^ n) A c d
      = Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)
          * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ))) * A c d := by
  rw [freeFieldU_pow, heisenberg_phaseDiagU_apply]
  have hstar : star (Complex.exp (-(Complex.I * ((n * (τ * fieldEnergy c) : ℝ) : ℂ))))
      = Complex.exp (Complex.I * ((n * (τ * fieldEnergy c) : ℝ) : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hstar, mul_comm (Complex.exp _) (A c d), mul_assoc, ← Complex.exp_add]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

/-- The real-time slice of the complex-time evolution IS the CV chain's stroboscopic
Heisenberg evolution. -/
theorem thermalEvolve_real_eq_heisenberg (τ : ℝ) (n : ℕ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    thermalEvolve ((((n : ℝ) * τ : ℝ)) : ℂ) A = heisenberg (freeFieldU K N τ ^ n) A := by
  ext c d
  rw [thermalEvolve, Matrix.of_apply, heisenberg_freeFieldU_pow_apply]

/-- The Boltzmann-weight transport identity: `w_c = w_d · e^{-β(E_c − E_d)}`. -/
lemma thermalWeight_transport (β : ℝ) (c d : FieldConfig K N) :
    thermalWeight β c
      = thermalWeight β d * Real.exp (-β * (fieldEnergy c - fieldEnergy d)) := by
  unfold thermalWeight
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

/-- ★★ **Exact KMS at the cutoff.** For every pair of observables and every `t, β`,

  `⟨A(t)·B⟩_β = ⟨B·A(t+iβ)⟩_β`.

The corpus's first KMS statement. At finite dimension with the diagonal free-field
Hamiltonian the identity is an entrywise exponential shuffle: the `iβ` shift converts
the Boltzmann weight at `c` into the weight at `d` (`thermalWeight_transport`), and the
double sum relabels. Exact — no approximation, no continuation, no cutoff error. -/
theorem thermal_kms [NeZero N] (β t : ℝ)
    (A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    thermalExpect β (thermalEvolve (t : ℂ) A * B)
      = thermalExpect β (B * thermalEvolve ((t : ℂ) + Complex.I * (β : ℂ)) A) := by
  rw [thermalExpect_eq, thermalExpect_eq]
  simp only [Matrix.mul_apply, thermalEvolve, Matrix.of_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hkey : ((thermalWeight β c : ℝ) : ℂ)
        * Complex.exp (Complex.I * (t : ℂ)
            * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ)))
      = ((thermalWeight β d : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((t : ℂ) + Complex.I * (β : ℂ))
            * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ))) := by
    rw [thermalWeight_transport β c d]
    have hsplit : Complex.I * ((t : ℂ) + Complex.I * (β : ℂ))
          * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ))
        = Complex.I * (t : ℂ)
            * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ))
          + ((-β * (fieldEnergy c - fieldEnergy d) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring
  calc ((thermalWeight β c : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (t : ℂ)
            * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ))) * A c d * B d c)
      = (((thermalWeight β c : ℝ) : ℂ)
          * Complex.exp (Complex.I * (t : ℂ)
              * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ)))) * (A c d * B d c) := by
        ring
    _ = (((thermalWeight β d : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((t : ℂ) + Complex.I * (β : ℂ))
              * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ)))) * (A c d * B d c) := by
        rw [hkey]
    _ = ((thermalWeight β d : ℝ) : ℂ)
        * (B d c * (Complex.exp (Complex.I * ((t : ℂ) + Complex.I * (β : ℂ))
            * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ))) * A c d)) := by
        ring

/-! ## The mode marginal -/

/-- The Boltzmann factor of a configuration is the product of its per-mode factors. -/
lemma boltzmann_prod (β : ℝ) (c : FieldConfig K N) :
    ((Real.exp (-β * fieldEnergy c) : ℝ) : ℂ)
      = ∏ j, ((Real.exp (-β * oscEnergy (c j)) : ℝ) : ℂ) := by
  have h : Real.exp (-β * fieldEnergy c) = ∏ j, Real.exp (-β * oscEnergy (c j)) := by
    rw [fieldEnergy, Finset.mul_sum, Real.exp_sum]
  rw [h]
  push_cast
  rfl

/-- The partition function factorises over modes: `Z_field = z_osc^K`. -/
theorem fieldPartition_eq_pow (β : ℝ) (K N : ℕ) :
    fieldPartition β K N = oscPartition β N ^ K := by
  classical
  unfold fieldPartition oscPartition
  have h : ∀ c : FieldConfig K N, Real.exp (-β * fieldEnergy c)
      = ∏ j, Real.exp (-β * oscEnergy (c j)) := by
    intro c
    rw [fieldEnergy, Finset.mul_sum, Real.exp_sum]
  simp only [h]
  have hK : (∑ m : Fin N, Real.exp (-β * oscEnergy m)) ^ K
      = ∏ _j : Fin K, ∑ m : Fin N, Real.exp (-β * oscEnergy m) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hK, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The distinguished-coordinate factorisation**: summing a Boltzmann-weighted
function of one mode over all configurations splits off that mode's Gibbs sum, the
spectator modes contributing one partition factor each. -/
lemma sum_boltzmann_mul_comp [NeZero N] (β : ℝ) (k : Fin K) (g : Fin N → ℂ) :
    ∑ c : FieldConfig K N, ((Real.exp (-β * fieldEnergy c) : ℝ) : ℂ) * g (c k)
      = ((oscPartition β N : ℝ) : ℂ) ^ (K - 1)
        * ∑ m : Fin N, ((Real.exp (-β * oscEnergy m) : ℝ) : ℂ) * g m := by
  classical
  set h : Fin K → Fin N → ℂ :=
    fun j m => if j = k then ((Real.exp (-β * oscEnergy m) : ℝ) : ℂ) * g m
      else ((Real.exp (-β * oscEnergy m) : ℝ) : ℂ) with hh
  have hterm : ∀ c : FieldConfig K N,
      ((Real.exp (-β * fieldEnergy c) : ℝ) : ℂ) * g (c k) = ∏ j, h j (c j) := by
    intro c
    rw [boltzmann_prod]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => h j (c j)) (Finset.mem_univ k)]
    have h1 : h k (c k) = ((Real.exp (-β * oscEnergy (c k)) : ℝ) : ℂ) * g (c k) := by
      rw [hh]
      simp
    have h2 : ∀ j ∈ Finset.univ.erase k, h j (c j)
        = ((Real.exp (-β * oscEnergy (c j)) : ℝ) : ℂ) := by
      intro j hj
      rw [hh]
      simp [Finset.ne_of_mem_erase hj]
    rw [h1, Finset.prod_congr rfl h2]
    ring
  simp only [hterm]
  rw [show (∑ c : FieldConfig K N, ∏ j, h j (c j))
      = ∏ j, ∑ m, h j m by
        rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ m, h j m) (Finset.mem_univ k)]
  have hk : (∑ m, h k m) = ∑ m : Fin N, ((Real.exp (-β * oscEnergy m) : ℝ) : ℂ) * g m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hh]
    simp
  have hoff : ∀ j ∈ Finset.univ.erase k, (∑ m, h j m) = ((oscPartition β N : ℝ) : ℂ) := by
    intro j hj
    rw [oscPartition]
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hh]
    simp [Finset.ne_of_mem_erase hj]
  rw [hk, Finset.prod_congr rfl hoff, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  ring

/-- The common tail: the thermal expectation of any observable whose diagonal reads a
single mode is the single-mode Gibbs average of that reading — the factorisation engine
both the mode marginal and the two-point closed form consume. -/
lemma thermalExpect_comp_mode [NeZero N] (β : ℝ) (k : Fin K) (g : Fin N → ℂ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (hA : ∀ c, A c c = g (c k)) :
    thermalExpect β A
      = (∑ m : Fin N, ((Real.exp (-β * oscEnergy m) : ℝ) : ℂ) * g m)
        / ((oscPartition β N : ℝ) : ℂ) := by
  rw [thermalExpect_eq]
  simp only [hA, thermalWeight]
  have hcast : ∀ c : FieldConfig K N,
      (((Real.exp (-β * fieldEnergy c) / fieldPartition β K N : ℝ)) : ℂ) * g (c k)
        = (((Real.exp (-β * fieldEnergy c) : ℝ)) : ℂ) * g (c k)
          / ((fieldPartition β K N : ℝ) : ℂ) := by
    intro c
    push_cast
    ring
  simp only [hcast]
  rw [← Finset.sum_div, sum_boltzmann_mul_comp β k g, fieldPartition_eq_pow]
  have hK : K = (K - 1) + 1 := (Nat.succ_pred_eq_of_pos k.pos).symm
  have hosc : ((oscPartition β N ^ K : ℝ) : ℂ)
      = ((oscPartition β N : ℝ) : ℂ) ^ (K - 1) * ((oscPartition β N : ℝ) : ℂ) := by
    rw [hK]
    push_cast
    ring
  rw [hosc]
  have hne : ((oscPartition β N : ℝ) : ℂ) ^ (K - 1) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (oscPartition_pos β).ne')
  field_simp

/-- ★ **The thermal mode marginal**: the thermal expectation of a single-mode observable
is its single-mode Gibbs expectation — the thermal analogue of
`modeMarginal_tprod_unit`. -/
theorem thermalExpect_modeOp [NeZero N] (β : ℝ) (k : Fin K)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    thermalExpect β (modeOp k a)
      = (∑ m : Fin N, ((Real.exp (-β * oscEnergy m) : ℝ) : ℂ) * a m m)
        / ((oscPartition β N : ℝ) : ℂ) :=
  thermalExpect_comp_mode β k (fun m => a m m) _
    (fun _c => modeOp_apply_of_agree k a (fun _ _ => rfl))

/-! ## The thermal two-point function -/

/-- The quadrature has zero diagonal: `Q` is strictly tridiagonal. -/
lemma Q_apply_self [NeZero N] (m : Fin N) : Q N m m = 0 := by
  simp [Q, annihilation, creation, Matrix.conjTranspose_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.of_apply]

/-- **The thermal two-point function** `⟨Q_k(n)·Q_l⟩_β`: the mode-`k` quadrature evolved
`n` free periods, against the mode-`l` quadrature, in the thermal state. -/
noncomputable def thermalTwoPoint [NeZero N] (β τ : ℝ) (n : ℕ) (k l : Fin K) : ℂ :=
  thermalExpect β (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) * modeOp l (Q N))

/-- **Modes do not mix thermally**: the thermal two-point function vanishes off the mode
diagonal — the thermal companion of the vacuum propagator's `δ_{kl}`. -/
theorem thermalTwoPoint_offdiag [NeZero N] (β τ : ℝ) (n : ℕ) {k l : Fin K}
    (hkl : k ≠ l) : thermalTwoPoint (K := K) (N := N) β τ n k l = 0 := by
  rw [thermalTwoPoint, thermalExpect_eq]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [diag_entry_mul_of_disjointSupport (R := {k}) (Y := {l})
    (Finset.disjoint_singleton.mpr hkl)
    (heisenberg_freeFieldU_pow_supportedOn τ n (modeOp_supportedOn k (Q N)))
    (modeOp_supportedOn l (Q N)) c]
  rw [modeOp_apply_of_agree l (Q N) (fun _ _ => rfl), Q_apply_self, mul_zero, mul_zero]

/-- Collapse of a configuration sum against mode-`k` locality: a summand vanishing off
"agrees with `c` away from `k`" reduces to a sum over the mode-`k` value. -/
lemma sum_collapse_of_support (c : FieldConfig K N) (k : Fin K)
    (F : FieldConfig K N → ℂ)
    (h0 : ∀ d, ¬ (∀ j, j ≠ k → c j = d j) → F d = 0) :
    ∑ d, F d = ∑ m : Fin N, F (Function.update c k m) := by
  classical
  have hinj : Function.Injective (Function.update c k) := fun m m' h => by
    have := congrFun h k
    simpa [Function.update_self] using this
  have himg : ∀ d ∈ Finset.univ, d ∉ Finset.univ.image (Function.update c k) → F d = 0 := by
    intro d _ hd
    refine h0 d fun hagree => hd ?_
    refine Finset.mem_image.mpr ⟨d k, Finset.mem_univ _, ?_⟩
    funext j
    by_cases hj : j = k
    · subst hj
      rw [Function.update_self]
    · rw [Function.update_of_ne hj]
      exact hagree j hj
  rw [← Finset.sum_subset (Finset.subset_univ _) himg,
    Finset.sum_image (fun m _ m' _ h => hinj h)]

/-- The field energy of a one-mode update. -/
lemma fieldEnergy_update (c : FieldConfig K N) (k : Fin K) (m : Fin N) :
    fieldEnergy (Function.update c k m)
      = fieldEnergy c - oscEnergy (c k) + oscEnergy m := by
  unfold fieldEnergy
  rw [← Finset.add_sum_erase _ (fun j => oscEnergy (Function.update c k m j))
      (Finset.mem_univ k),
    ← Finset.add_sum_erase _ (fun j => oscEnergy (c j)) (Finset.mem_univ k)]
  have h1 : oscEnergy ((Function.update c k m k : Fin N) : ℕ) = oscEnergy m := by
    rw [Function.update_self]
  have h2 : ∀ j ∈ Finset.univ.erase k,
      oscEnergy ((Function.update c k m j : Fin N) : ℕ) = oscEnergy (c j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h1, Finset.sum_congr rfl h2]
  ring

/-- The two-sided quadrature entry product: `Q_{am}·Q_{ma}` is `m/2` on the up-step
`m = a+1`, `a/2` on the down-step `m+1 = a`, and `0` elsewhere. -/
lemma Q_mul_Q_apply (a m : Fin N) :
    Q N a m * Q N m a
      = (if (a : ℕ) + 1 = (m : ℕ) then ((m : ℕ) : ℂ) / 2
          else if (m : ℕ) + 1 = (a : ℕ) then ((a : ℕ) : ℂ) / 2 else 0) := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  by_cases h1 : (a : ℕ) + 1 = (m : ℕ)
  · have h2 : ¬ ((m : ℕ) + 1 = (a : ℕ)) := by omega
    rw [if_pos h1]
    have hQam : Q N a m = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (m : ℕ) : ℝ) : ℂ) := by
      simp only [Q, Matrix.smul_apply, Matrix.add_apply, annihilation, creation,
        Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
      rw [if_pos h1, if_neg h2]
      simp
    have hQma : Q N m a = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (m : ℕ) : ℝ) : ℂ) := by
      simp only [Q, Matrix.smul_apply, Matrix.add_apply, annihilation, creation,
        Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
      rw [if_neg h2, if_pos h1]
      simp [Complex.conj_ofReal]
    have hsm : ((Real.sqrt (m : ℕ) : ℝ) : ℂ) * ((Real.sqrt (m : ℕ) : ℝ) : ℂ)
        = ((m : ℕ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [hQam, hQma]
    have hexpand : ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (m : ℕ) : ℝ) : ℂ))
        * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (m : ℕ) : ℝ) : ℂ))
        = (((Real.sqrt (m : ℕ) : ℝ) : ℂ) * ((Real.sqrt (m : ℕ) : ℝ) : ℂ))
          / (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) := by
      ring
    rw [hexpand, hs2, hsm]
  · by_cases h2 : (m : ℕ) + 1 = (a : ℕ)
    · rw [if_neg h1, if_pos h2]
      have hQam : Q N a m = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (a : ℕ) : ℝ) : ℂ) := by
        simp only [Q, Matrix.smul_apply, Matrix.add_apply, annihilation, creation,
          Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
        rw [if_neg h1, if_pos h2]
        simp [Complex.conj_ofReal]
      have hQma : Q N m a = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (a : ℕ) : ℝ) : ℂ) := by
        simp only [Q, Matrix.smul_apply, Matrix.add_apply, annihilation, creation,
          Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
        rw [if_pos h2, if_neg h1]
        simp
      have hsa : ((Real.sqrt (a : ℕ) : ℝ) : ℂ) * ((Real.sqrt (a : ℕ) : ℝ) : ℂ)
          = ((a : ℕ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        push_cast
        rfl
      rw [hQam, hQma]
      have hexpand : ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (a : ℕ) : ℝ) : ℂ))
          * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt (a : ℕ) : ℝ) : ℂ))
          = (((Real.sqrt (a : ℕ) : ℝ) : ℂ) * ((Real.sqrt (a : ℕ) : ℝ) : ℂ))
            / (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) := by
        ring
      rw [hexpand, hs2, hsa]
    · rw [if_neg h1, if_neg h2]
      have hQam : Q N a m = 0 := by
        simp only [Q, Matrix.smul_apply, Matrix.add_apply, annihilation, creation,
          Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
        rw [if_neg h1, if_neg h2]
        simp
      rw [hQam, zero_mul]

/-- The single-mode thermal walk: the phase-weighted quadrature return sum evaluates to
one up-step and one down-step. The up-step exists only below the cutoff ceiling — the
`[a+1 < N]` guard is the truncation honesty of `eqFourPoint_same`'s `2 < N`, here at
every level. -/
lemma qWalk_eval [NeZero N] (θ : ℝ) (a : Fin N) :
    (∑ m : Fin N, Complex.exp (Complex.I * (θ : ℂ)
        * (((oscEnergy a : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ)))
      * (Q N a m * Q N m a))
      = (if (a : ℕ) + 1 < N then (((a : ℕ) + 1 : ℕ) : ℂ) / 2
            * Complex.exp (-(Complex.I * (θ : ℂ))) else 0)
        + ((a : ℕ) : ℂ) / 2 * Complex.exp (Complex.I * (θ : ℂ)) := by
  have hΔup : ∀ m : Fin N, (a : ℕ) + 1 = (m : ℕ) →
      Complex.I * (θ : ℂ) * (((oscEnergy a : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ))
        = -(Complex.I * (θ : ℂ)) := by
    intro m hm
    have h : ((oscEnergy a : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ) = -1 := by
      rw [← Complex.ofReal_sub]
      have hr : oscEnergy (a : ℕ) - oscEnergy (m : ℕ) = -1 := by
        rw [oscEnergy, oscEnergy]
        have hm' : ((m : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
        rw [hm']
        ring
      rw [hr]
      norm_num
    rw [h]
    ring
  have hΔdown : ∀ m : Fin N, (m : ℕ) + 1 = (a : ℕ) →
      Complex.I * (θ : ℂ) * (((oscEnergy a : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ))
        = Complex.I * (θ : ℂ) := by
    intro m hm
    have h : ((oscEnergy a : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sub]
      have hr : oscEnergy (a : ℕ) - oscEnergy (m : ℕ) = 1 := by
        rw [oscEnergy, oscEnergy]
        have hm' : ((a : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
        rw [hm']
        ring
      rw [hr]
      norm_num
    rw [h]
    ring
  have hsummand : ∀ m : Fin N,
      Complex.exp (Complex.I * (θ : ℂ)
          * (((oscEnergy a : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ)))
        * (Q N a m * Q N m a)
      = (if (a : ℕ) + 1 = (m : ℕ)
            then ((m : ℕ) : ℂ) / 2 * Complex.exp (-(Complex.I * (θ : ℂ))) else 0)
        + (if (m : ℕ) + 1 = (a : ℕ)
            then ((a : ℕ) : ℂ) / 2 * Complex.exp (Complex.I * (θ : ℂ)) else 0) := by
    intro m
    rw [Q_mul_Q_apply]
    by_cases h1 : (a : ℕ) + 1 = (m : ℕ)
    · have h2 : ¬ ((m : ℕ) + 1 = (a : ℕ)) := by omega
      rw [if_pos h1, if_pos h1, if_neg h2, add_zero, hΔup m h1]
      ring
    · by_cases h2 : (m : ℕ) + 1 = (a : ℕ)
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, zero_add, hΔdown m h2]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, add_zero, mul_zero]
  simp only [hsummand]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hlt : (a : ℕ) + 1 < N
    · rw [if_pos hlt, Finset.sum_eq_single (⟨(a : ℕ) + 1, hlt⟩ : Fin N)]
      · rw [if_pos rfl]
      · intro b _ hb
        rw [if_neg fun h => hb (Fin.ext h.symm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hlt]
      refine (Finset.sum_eq_zero fun m _ => ?_)
      rw [if_neg (fun h => hlt (by omega))]
  · by_cases ha : (a : ℕ) = 0
    · have hz : ∀ m ∈ (Finset.univ : Finset (Fin N)), (if (m : ℕ) + 1 = (a : ℕ)
          then ((a : ℕ) : ℂ) / 2 * Complex.exp (Complex.I * (θ : ℂ)) else 0) = (0 : ℂ) := by
        intro m _
        rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, ha]
      norm_num
    · have haN : (a : ℕ) - 1 < N := lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
      rw [Finset.sum_eq_single (⟨(a : ℕ) - 1, haN⟩ : Fin N)]
      · rw [if_pos (show ((⟨(a : ℕ) - 1, haN⟩ : Fin N) : ℕ) + 1 = (a : ℕ) from
          Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero ha))]
      · intro b _ hb
        rw [if_neg fun h => hb (Fin.ext (show (b : ℕ) = (a : ℕ) - 1 by omega))]
      · intro h
        exact absurd (Finset.mem_univ _) h

/-- The diagonal entry of the evolved-against-static quadrature product is a single-mode
walk at the configuration's mode-`k` level — the two-point analogue of the vacuum
computation, at every configuration. -/
lemma evolved_mul_modeOpQ_diag [NeZero N] (τ : ℝ) (n : ℕ) (k : Fin K)
    (c : FieldConfig K N) :
    (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) * modeOp k (Q N)) c c
      = ∑ m : Fin N, Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)
          * (((oscEnergy (c k) : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ)))
        * (Q N (c k) m * Q N m (c k)) := by
  rw [Matrix.mul_apply]
  have h0 : ∀ d, ¬ (∀ j, j ≠ k → c j = d j) →
      heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) c d * modeOp k (Q N) d c = 0 := by
    intro d hd
    rw [heisenberg_freeFieldU_pow_apply]
    have hz : modeOp k (Q N) c d = 0 := by
      unfold modeOp
      rw [if_neg hd]
    rw [hz, mul_zero, zero_mul]
  rw [sum_collapse_of_support c k
    (fun d => heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) c d * modeOp k (Q N) d c) h0]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [heisenberg_freeFieldU_pow_apply]
  have hagree1 : ∀ j, j ≠ k → c j = (Function.update c k m) j := fun j hj =>
    (Function.update_of_ne hj _ _).symm
  have hagree2 : ∀ j, j ≠ k → (Function.update c k m) j = c j := fun j hj =>
    Function.update_of_ne hj _ _
  rw [modeOp_apply_of_agree k (Q N) hagree1, modeOp_apply_of_agree k (Q N) hagree2,
    Function.update_self]
  have hE : ((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy (Function.update c k m) : ℝ) : ℂ)
      = ((oscEnergy (c k) : ℝ) : ℂ) - ((oscEnergy m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, fieldEnergy_update]
    congr 1
    ring
  rw [hE]
  ring

/-- ★ **The thermal two-point function, in closed form.** On the mode diagonal the
thermal propagator is a single-mode Boltzmann average of one up-step and one down-step:

  `⟨Q_k(n)Q_k⟩_β = (1/z)·∑_a e^{-β(a+½)}·( (a+1)/2·e^{-inτ}·[a+1<N] + a/2·e^{+inτ} )`.

The truncation edge is explicit — the top level has no up-step — and at `β → ∞` the
`a = 0` term dominates, recovering the vacuum propagator `½·e^{-inτ}`
(`freeTwoPoint_eq`); the interacting correction rides the CV-9/CV-12 price unchanged. -/
theorem thermalTwoPoint_diag [NeZero N] (β τ : ℝ) (n : ℕ) (k : Fin K) :
    thermalTwoPoint (K := K) (N := N) β τ n k k
      = (∑ a : Fin N, ((Real.exp (-β * oscEnergy a) : ℝ) : ℂ)
          * ((if (a : ℕ) + 1 < N then (((a : ℕ) + 1 : ℕ) : ℂ) / 2
                * Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))) else 0)
              + ((a : ℕ) : ℂ) / 2
                * Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))))
        / ((oscPartition β N : ℝ) : ℂ) := by
  rw [thermalTwoPoint]
  exact thermalExpect_comp_mode β k _ _ (fun c => by
    rw [evolved_mul_modeOpQ_diag, qWalk_eval])

/-- ★ **The vacuum limit.** As `β → ∞` the thermal propagator converges to the vacuum
propagator: the ground level dominates the Boltzmann average, and the closed form's
`a = 0` term is exactly `freeTwoPoint`'s `½·e^{-inτ}`. The zero-point energies cancel
between numerator and partition function, so the limit is a statement about the reduced
geometric weights `e^{-βa}` — finite sums, no dominated convergence. -/
theorem thermalTwoPoint_tendsto_vacuum [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ)
    (k : Fin K) :
    Filter.Tendsto (fun β => thermalTwoPoint (K := K) (N := N) β τ n k k)
      Filter.atTop (nhds (freeTwoPoint (K := K) (N := N) τ n k k)) := by
  classical
  set g : Fin N → ℂ := fun a =>
    (if (a : ℕ) + 1 < N then (((a : ℕ) + 1 : ℕ) : ℂ) / 2
        * Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))) else 0)
      + ((a : ℕ) : ℂ) / 2 * Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)) with hg
  have hzero : (0 : ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hx : Filter.Tendsto (fun β : ℝ => ((Real.exp (-β) : ℝ) : ℂ))
      Filter.atTop (nhds 0) := by
    rw [show ((0 : ℂ)) = ((0 : ℝ) : ℂ) by norm_num]
    exact (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_exp_neg_atTop_nhds_zero
  have hval : (∑ a : Fin N, (0 : ℂ) ^ (a : ℕ) * g a) = g ⟨0, hzero⟩ := by
    rw [Finset.sum_eq_single (⟨0, hzero⟩ : Fin N)]
    · norm_num
    · intro b _ hb
      rw [zero_pow (fun h => hb (Fin.ext (show (b : ℕ) = 0 from h))), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hval1 : (∑ a : Fin N, (0 : ℂ) ^ (a : ℕ)) = 1 := by
    rw [Finset.sum_eq_single (⟨0, hzero⟩ : Fin N)]
    · norm_num
    · intro b _ hb
      rw [zero_pow (fun h => hb (Fin.ext (show (b : ℕ) = 0 from h)))]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hNum : Filter.Tendsto
      (fun β : ℝ => ∑ a : Fin N, ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ) * g a)
      Filter.atTop (nhds (g ⟨0, hzero⟩)) := by
    have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin N))
      (fun a _ => ((hx.pow (a : ℕ)).mul_const (g a)))
    rw [hval] at h1
    exact h1
  have hDen : Filter.Tendsto
      (fun β : ℝ => ∑ a : Fin N, ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ))
      Filter.atTop (nhds 1) := by
    have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin N))
      (fun a _ => (hx.pow (a : ℕ)))
    rw [hval1] at h1
    exact h1
  have heq : ∀ β : ℝ, thermalTwoPoint (K := K) (N := N) β τ n k k
      = (∑ a : Fin N, ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ) * g a)
        / (∑ a : Fin N, ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ)) := by
    intro β
    rw [thermalTwoPoint_diag]
    have hterm : ∀ a : Fin N, ((Real.exp (-β * oscEnergy a) : ℝ) : ℂ)
        = ((Real.exp (-β * 2⁻¹) : ℝ) : ℂ) * ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ) := by
      intro a
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_add, oscEnergy]
      congr 1
      ring
    have hnum : (∑ a : Fin N, ((Real.exp (-β * oscEnergy a) : ℝ) : ℂ) * g a)
        = ((Real.exp (-β * 2⁻¹) : ℝ) : ℂ)
          * ∑ a : Fin N, ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ) * g a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hterm a]
      ring
    have hZ : ((oscPartition β N : ℝ) : ℂ)
        = ((Real.exp (-β * 2⁻¹) : ℝ) : ℂ)
          * ∑ a : Fin N, ((Real.exp (-β) : ℝ) : ℂ) ^ (a : ℕ) := by
      rw [oscPartition, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      have := hterm a
      push_cast at this
      rw [this]
    rw [hnum, hZ, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
  have hfree : freeTwoPoint (K := K) (N := N) τ n k k = g ⟨0, hzero⟩ := by
    rw [freeTwoPoint_eq hN, if_pos rfl, hg]
    simp only []
    rw [if_pos (show ((⟨0, hzero⟩ : Fin N) : ℕ) + 1 < N from hN)]
    norm_num
  rw [hfree]
  refine Filter.Tendsto.congr (fun β => (heq β).symm) ?_
  have hdiv := hNum.div hDen one_ne_zero
  rw [div_one] at hdiv
  exact hdiv.congr (fun β => Pi.div_apply _ _ β)

end CSD.CV


