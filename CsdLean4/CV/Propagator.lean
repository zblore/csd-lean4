/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DynamicalLocality
public import CsdLean4.CV.InteractionPrice
public import CsdLean4.CV.SupportSpreading
public import CsdLean4.Mathlib.Analysis.Matrix.TrotterProduct
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormEntry

/-!
# CV-13: the finite free propagator — the chain computes a correlation function

**Category:** CV (continuous variables — the multi-mode field).

Every EFT statement so far has been structural (locality, cones) or a
bound (prices, power counting). This module produces the chain's first
**computed observable**: the free field's two-point function, in closed
form, oscillating at the excitation energy.

* `vacCfg` / `excCfg` — the vacuum configuration and the one-quantum
  configuration at mode `l`.
* `fieldEnergy_excCfg_sub` — the excitation costs exactly one energy
  quantum: `E(exc l) − E(vac) = 1` (the free spacing; under
  `relFieldHamiltonian` the same computation gives `ω(m, p_l)`, recorded
  below).
* `phaseDiagU_pow` / `freeFieldU_pow` — a diagonal-phase drive's `n`-th
  power is the drive at `n`-fold phase (so the Heisenberg entry formula
  applies at every period).
* `freeTwoPoint τ n k l` — the two-point function
  `⟨vac| Q_k(n) Q_l |vac⟩`, with `Q_k(n)` the CV-6 Heisenberg evolution of
  the mode-`k` quadrature under `n` free periods.
* ★★ `freeTwoPoint_eq` — **the lattice propagator**:
  `freeTwoPoint τ n k l = (1/2)·e^{-i n τ}·δ_{kl}`. Diagonal in the mode
  index (free modes do not mix), and oscillating at the excitation energy
  — the dispersion appearing as an *observable time dependence* rather
  than a spectrum label. `freeTwoPoint_zero` fixes the equal-time
  normalisation `1/2` (the vacuum quadrature fluctuation), and
  `norm_freeTwoPoint` shows the modulus is period-independent: the free
  propagator does not decay.
* ★ `twoPoint_interacting_dist_le` — switching on a diagonal interaction
  moves the two-point function by at most `2n·|τ|·|λ|·C·‖Q‖²`: the
  Born-approximation error, priced by the CV-9/CV-12 ladder.

⚠️ Honest scope: the free (or diagonal-drive) two-point function at a
finite cutoff, for the quadrature observables — not a general Wightman
function, and no continuum limit (`no_exact_finite_ccr` stands). The
relativistic reading is a substitution, not a separate theorem: replacing
`fieldHamiltonian` by `relFieldHamiltonian` replaces the spacing `1` by
`ω(m, p_l)` in the same computation (`CV/Dispersion.lean`,
`relFieldEnergy_quantum`), recorded as the CV-13 residue.

## References

`CV/FieldModes.lean` (`fieldEnergy`); `CV/Oscillator.lean` (`Q`, the
ladder entries); `CV/ModeLocality.lean` (`modeOp`);
`CV/DynamicalLocality.lean` (`heisenberg_phaseDiagU_apply`);
`CV/InteractionPrice.lean` (CV-9, the price);
`specs/eft-stage4-plan.md` (row CV-13); `specs/future-work.md`.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### The vacuum and one-quantum configurations -/

/-- The **vacuum configuration**: every mode unoccupied. -/
def vacCfg (K N : ℕ) [NeZero N] : FieldConfig K N := fun _ => 0

/-- The **one-quantum configuration** at mode `l`. -/
def excCfg [NeZero N] (hN : 1 < N) (l : Fin K) : FieldConfig K N :=
  Function.update (vacCfg K N) l ⟨1, hN⟩

@[simp] lemma vacCfg_apply [NeZero N] (k : Fin K) :
    (vacCfg K N) k = 0 := rfl

@[simp] lemma excCfg_self [NeZero N] (hN : 1 < N) (l : Fin K) :
    (excCfg (K := K) hN l) l = ⟨1, hN⟩ := by
  simp [excCfg]

lemma excCfg_of_ne [NeZero N] (hN : 1 < N) {l j : Fin K} (h : j ≠ l) :
    (excCfg (K := K) hN l) j = 0 := by
  simp [excCfg, h]

/-- Off its own mode, the one-quantum configuration agrees with the
vacuum. -/
lemma excCfg_agree [NeZero N] (hN : 1 < N) (l : Fin K) {j : Fin K}
    (h : j ≠ l) : (excCfg (K := K) hN l) j = (vacCfg K N) j := by
  rw [excCfg_of_ne hN h, vacCfg_apply]

/-- A configuration agreeing with the vacuum off `l` and carrying one
quantum at `l` IS the one-quantum configuration. -/
lemma eq_excCfg [NeZero N] (hN : 1 < N) {l : Fin K} {c : FieldConfig K N}
    (hoff : ∀ j, j ≠ l → c j = (vacCfg K N) j) (hat : (c l : ℕ) = 1) :
    c = excCfg hN l := by
  funext j
  by_cases h : j = l
  · subst h
    rw [excCfg_self]
    exact Fin.ext hat
  · rw [excCfg_of_ne hN h, hoff j h, vacCfg_apply]

/-- ★ **One quantum costs one unit of free energy**:
`E(exc l) − E(vac) = 1`. -/
theorem fieldEnergy_excCfg_sub [NeZero N] (hN : 1 < N) (l : Fin K) :
    fieldEnergy (excCfg (K := K) hN l) - fieldEnergy (vacCfg K N) = 1 := by
  classical
  rw [show fieldEnergy (excCfg (K := K) hN l)
      = ∑ k, oscEnergy ((excCfg (K := K) hN l) k : ℕ) from rfl,
    show fieldEnergy (vacCfg K N) = ∑ k, oscEnergy ((vacCfg K N) k : ℕ) from
      rfl, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single l]
  · rw [excCfg_self, vacCfg_apply, Fin.val_zero]
    show oscEnergy 1 - oscEnergy 0 = 1
    rw [oscEnergy, oscEnergy]
    norm_num
  · intro j _ hj
    rw [excCfg_of_ne hN hj, vacCfg_apply, sub_self]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-! ### Powers of a diagonal-phase drive -/

/-- The `n`-th power of a diagonal-phase unitary is the drive at `n`-fold
phase. -/
theorem phaseDiagU_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (n : ℕ) :
    phaseDiagU f ^ n = phaseDiagU (fun x => n * f x) := by
  apply Subtype.ext
  show (phaseDiagU f).val ^ n = (phaseDiagU (fun x => n * f x)).val
  rw [phaseDiagU_val, phaseDiagU_val, Matrix.diagonal_pow]
  congr 1
  funext x
  show Complex.exp (-(Complex.I * ((f x : ℝ) : ℂ))) ^ n
      = Complex.exp (-(Complex.I * (((n : ℝ) * f x : ℝ) : ℂ)))
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The free drive at period count `n`. -/
theorem freeFieldU_pow (K N : ℕ) (τ : ℝ) (n : ℕ) :
    freeFieldU K N τ ^ n
      = phaseDiagU (fun c : FieldConfig K N => n * (τ * fieldEnergy c)) :=
  phaseDiagU_pow _ n

/-! ### The quadrature entries at the vacuum -/

/-- `Q` connects the vacuum to the first excited level with amplitude
`1/√2`. -/
lemma Q_zero_one [NeZero N] (hN : 1 < N) :
    Q N (0 : Fin N) ⟨1, hN⟩ = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply]
  norm_num

/-- `Q` connects the first excited level back to the vacuum with the same
amplitude. -/
lemma Q_one_zero [NeZero N] (hN : 1 < N) :
    Q N ⟨1, hN⟩ (0 : Fin N) = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply]
  norm_num

/-- `Q` annihilates the vacuum except through the first excited level. -/
lemma Q_apply_zero_eq_zero [NeZero N] {m : Fin N} (hm : (m : ℕ) ≠ 1) :
    Q N m (0 : Fin N) = 0 := by
  have h0 : ((0 : Fin N) : ℕ) = 0 := Fin.val_zero N
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply, h0, if_neg (by omega), if_neg (by omega)]
  simp

/-- A pure phase has unit modulus. -/
lemma norm_exp_neg_I_mul_real (r : ℝ) :
    ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (r : ℂ)) = ((-r : ℝ) : ℂ) * Complex.I from by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-! ### The two-point function -/

/-- **The free two-point function**: `⟨vac| Q_k(n) Q_l |vac⟩`, with
`Q_k(n)` the Heisenberg evolution of the mode-`k` quadrature under `n`
free periods. -/
noncomputable def freeTwoPoint [NeZero N] (τ : ℝ) (n : ℕ) (k l : Fin K) :
    ℂ :=
  (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) * modeOp l (Q N))
    (vacCfg K N) (vacCfg K N)

/-- The one-quantum configuration is the only intermediate state the
right-hand quadrature reaches from the vacuum. -/
lemma modeOp_Q_apply_vac [NeZero N] (hN : 1 < N) (l : Fin K)
    (e : FieldConfig K N) (he : e ≠ excCfg hN l) :
    modeOp l (Q N) e (vacCfg K N) = 0 := by
  classical
  by_cases hoff : ∀ j, j ≠ l → e j = (vacCfg K N) j
  · rw [modeOp_apply_of_agree l (Q N) hoff]
    refine Q_apply_zero_eq_zero ?_
    intro hval
    exact he (eq_excCfg hN hoff hval)
  · rw [show modeOp l (Q N) e (vacCfg K N)
        = if (∀ j, j ≠ l → e j = (vacCfg K N) j)
            then Q N (e l) ((vacCfg K N) l) else 0 from rfl,
      if_neg hoff]

/-- ★★ **The lattice propagator.** The free two-point function is
diagonal in the mode index and oscillates at the excitation energy:
`⟨vac| Q_k(n) Q_l |vac⟩ = (1/2)·e^{-i n τ}·δ_{kl}`. -/
theorem freeTwoPoint_eq [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ)
    (k l : Fin K) :
    freeTwoPoint (K := K) (N := N) τ n k l
      = if k = l then
          (2 : ℂ)⁻¹ * Complex.exp (-(Complex.I * ((n * τ : ℝ) : ℂ)))
        else 0 := by
  classical
  rw [freeTwoPoint, Matrix.mul_apply]
  -- only the one-quantum configuration survives on the right
  rw [Finset.sum_eq_single (excCfg hN l)]
  · -- the surviving term
    rw [modeOp_apply_of_agree l (Q N) (fun j hj => by
        rw [excCfg_of_ne hN hj, vacCfg_apply]),
      excCfg_self, vacCfg_apply, Q_one_zero hN,
      freeFieldU_pow, heisenberg_phaseDiagU_apply]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl,
        modeOp_apply_of_agree k (Q N) (fun j hj => by
          rw [vacCfg_apply, excCfg_of_ne hN hj]),
        vacCfg_apply, excCfg_self, Q_zero_one hN]
      rw [show star (Complex.exp (-(Complex.I *
              ((n * (τ * fieldEnergy (vacCfg K N)) : ℝ) : ℂ))))
            * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
            * Complex.exp (-(Complex.I *
              ((n * (τ * fieldEnergy (excCfg (K := K) hN k)) : ℝ) : ℂ)))
            * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
          = ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹)
            * (star (Complex.exp (-(Complex.I *
                ((n * (τ * fieldEnergy (vacCfg K N)) : ℝ) : ℂ))))
              * Complex.exp (-(Complex.I *
                ((n * (τ * fieldEnergy (excCfg (K := K) hN k)) : ℝ) : ℂ))))
          from by ring]
      congr 1
      · rw [← mul_inv]
        norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]
      · have hdiff := fieldEnergy_excCfg_sub (K := K) hN k
        have hreal : (n : ℝ) * (τ * fieldEnergy (excCfg (K := K) hN k))
            - (n : ℝ) * (τ * fieldEnergy (vacCfg K N)) = (n : ℝ) * τ := by
          linear_combination (n : ℝ) * τ * hdiff
        rw [star_exp_phase_mul, hreal]
    · rw [if_neg hkl,
        show modeOp k (Q N) (vacCfg K N) (excCfg hN l)
          = if (∀ j, j ≠ k → (vacCfg K N) j = (excCfg hN l) j)
              then Q N ((vacCfg K N) k) ((excCfg hN l) k) else 0 from rfl,
        if_neg ?_]
      · ring
      · intro hall
        have := hall l (fun h => hkl h.symm)
        rw [vacCfg_apply, excCfg_self] at this
        exact absurd (congrArg Fin.val this) (by norm_num)
  · -- every other intermediate state contributes zero
    intro e _ hne
    rw [modeOp_Q_apply_vac hN l e hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The equal-time normalisation: the vacuum quadrature fluctuation is
`1/2` on the diagonal. -/
theorem freeTwoPoint_zero [NeZero N] (hN : 1 < N) (τ : ℝ) (k : Fin K) :
    freeTwoPoint (K := K) (N := N) τ 0 k k = (2 : ℂ)⁻¹ := by
  rw [freeTwoPoint_eq hN, if_pos rfl]
  norm_num

/-- **The free propagator does not decay**: its modulus is independent of
the period count (all the dynamics is in the phase). -/
theorem norm_freeTwoPoint [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ)
    (k : Fin K) :
    ‖freeTwoPoint (K := K) (N := N) τ n k k‖ = 1 / 2 := by
  rw [freeTwoPoint_eq hN, if_pos rfl, norm_mul, norm_exp_neg_I_mul_real]
  norm_num

/-! ### The interacting correction, priced -/

/-- The two-point function under the interacting drive. -/
noncomputable def interactingTwoPoint [NeZero N] (τ lam : ℝ)
    (v : FieldConfig K N → ℝ) (n : ℕ) (k l : Fin K) : ℂ :=
  (heisenberg (interactingU K N τ lam v ^ n) (modeOp k (Q N))
    * modeOp l (Q N)) (vacCfg K N) (vacCfg K N)

/-- ★ **The Born-approximation error, priced**: switching on a diagonal
interaction moves the two-point function by at most
`2n·|τ|·|λ|·C·‖Q_k‖·‖Q_l‖` — the CV-9 Duhamel price carried through the
CV-12 unitary telescoping and the entrywise bound. -/
theorem twoPoint_interacting_dist_le [NeZero N] (τ lam : ℝ)
    (v : FieldConfig K N → ℝ) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C)
    (n : ℕ) (k l : Fin K) :
    ‖interactingTwoPoint (K := K) (N := N) τ lam v n k l
        - freeTwoPoint (K := K) (N := N) τ n k l‖
      ≤ 2 * ((n : ℝ) * (|τ| * (|lam| * C))) * ‖modeOp k (Q N)‖
          * ‖modeOp l (Q N)‖ := by
  set X := heisenberg (interactingU K N τ lam v ^ n) (modeOp k (Q N)) with hX
  set Y := heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) with hY
  have hentry : interactingTwoPoint (K := K) (N := N) τ lam v n k l
      - freeTwoPoint (K := K) (N := N) τ n k l
      = ((X - Y) * modeOp l (Q N)) (vacCfg K N) (vacCfg K N) := by
    rw [interactingTwoPoint, freeTwoPoint, Matrix.sub_mul]
    rfl
  have hstep : ‖(interactingU K N τ lam v ^ n).val
      - (freeFieldU K N τ ^ n).val‖ ≤ (n : ℝ) * (|τ| * (|lam| * C)) := by
    have hpow : ‖(interactingU K N τ lam v).val ^ n
        - (freeFieldU K N τ).val ^ n‖
        ≤ (n : ℝ) * ‖(interactingU K N τ lam v).val
            - (freeFieldU K N τ).val‖ :=
      Matrix.norm_pow_sub_pow_le_of_unitary
        (interactingU K N τ lam v).property (freeFieldU K N τ).property n
    refine le_trans hpow ?_
    have := interactingU_dist_le (K := K) (N := N) τ lam v hC hv
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_left this hn0
  have hXY : ‖X - Y‖ ≤ 2 * ((n : ℝ) * (|τ| * (|lam| * C)))
      * ‖modeOp k (Q N)‖ := by
    refine le_trans (heisenberg_dist_le _ _ _) ?_
    gcongr
  calc ‖interactingTwoPoint (K := K) (N := N) τ lam v n k l
        - freeTwoPoint (K := K) (N := N) τ n k l‖
      = ‖((X - Y) * modeOp l (Q N)) (vacCfg K N) (vacCfg K N)‖ := by
        rw [hentry]
    _ ≤ ‖(X - Y) * modeOp l (Q N)‖ :=
        Matrix.norm_entry_le_l2_opNorm _ _ _
    _ ≤ ‖X - Y‖ * ‖modeOp l (Q N)‖ := norm_mul_le _ _
    _ ≤ 2 * ((n : ℝ) * (|τ| * (|lam| * C))) * ‖modeOp k (Q N)‖
          * ‖modeOp l (Q N)‖ :=
        mul_le_mul_of_nonneg_right hXY (norm_nonneg _)

end CSD.CV
