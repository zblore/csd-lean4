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

/-! ### CV-21 (Stage 6): vacuum clustering — correlations are local too

The dynamic cone (CV-18/19/20) says *signals* cannot cross disjoint
supports faster than the coupling allows. The statics companion: at the
cutoff, *correlations* across disjoint supports do not exist at all in the
vacuum — expectations factorise exactly. The proof is the same uniqueness
of the intermediate configuration that powers `commute_of_disjointSupport`:
between two visits to the same configuration, an `R`-supported and a
`Y`-supported operator admit only the trivial intermediate. -/

/-- **Diagonal entries multiply across disjoint supports**: for any
configuration `v`, `(A·B)(v,v) = A(v,v)·B(v,v)` when `A` and `B` live on
disjoint mode sets — the only intermediate configuration both tolerate is
`v` itself. -/
theorem diag_entry_mul_of_disjointSupport [NeZero N] {R Y : Finset (Fin K)}
    (hRY : Disjoint R Y)
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn Y B) (v : FieldConfig K N) :
    (A * B) v v = A v v * B v v := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single v]
  · intro c _ hc
    by_cases hcR : ∀ k, k ∉ R → v k = c k
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
      have hkR : k ∈ R := by
        by_contra hkR
        exact hk (hcR k hkR).symm
      have hkY : k ∉ Y := fun hkY => Finset.disjoint_left.mp hRY hkR hkY
      rw [hB.offDiag hkY hk, mul_zero]
    · push Not at hcR
      obtain ⟨k, hkR, hk⟩ := hcR
      rw [hA.offDiag hkR hk, zero_mul]
  · intro hv
    exact absurd (Finset.mem_univ v) hv

/-- ★★ **Vacuum clustering at the cutoff** (CV-21, Stage 6): vacuum
expectations of disjointly supported observables factorise exactly,
`⟨vac∣AB∣vac⟩ = ⟨vac∣A∣vac⟩·⟨vac∣B∣vac⟩`. There are no vacuum correlations
across disjoint mode sets — the statics companion to the Lieb–Robinson
cone: at the cutoff, correlations, like signals, are local. -/
theorem vacuum_clustering [NeZero N] {R Y : Finset (Fin K)}
    (hRY : Disjoint R Y)
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn Y B) :
    (A * B) (vacCfg K N) (vacCfg K N)
      = A (vacCfg K N) (vacCfg K N) * B (vacCfg K N) (vacCfg K N) :=
  diag_entry_mul_of_disjointSupport hRY hA hB (vacCfg K N)

/-! ### CV-22 (Stage 6): the four-point Wick table

The equal-time four-point function `⟨vac∣Q_k Q_l Q_m Q_p∣vac⟩`, resolved
by coincidence pattern. Every 4-tuple of modes falls into exactly one of:
some mode appears **once** (`eqFourPoint_single₁`–`₄`: the expectation
vanishes — every Wick pairing would carry a mismatched `δ`), **two
pairs** in any arrangement (`eqFourPoint_pair`/`_alt`/`_outer`: `= 1/4`,
the one surviving pairing `(½)²`), or **all four equal**
(`eqFourPoint_same`: `= 3/4 = 3·(½)²`, all three pairings surviving).
These are exactly Wick's values `Σ_pairings ∏ G` with `G(a,b) = ½δ_{ab}`
(`freeTwoPoint` at `n = 0`) — the table IS the four-point Wick theorem at
the cutoff, stated pattern-resolved; the packaged single-formula `δ`-sum
is a recorded packaging residue (assembly, not mathematics). Truncation
honesty: the all-equal case needs `2 < N` (the walk visits the two-quantum
level — at `N = 2` the value is `1/4`, not `3/4`); the two-pair cases need
only `1 < N`. Higher `2n`-point Wick is not claimed. -/

/-- `Q` vanishes on the vacuum diagonal. -/
lemma Q_zero_zero [NeZero N] : Q N 0 0 = 0 := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply]
  simp

/-- `Q` connects the first to the second level with amplitude `1`
(`√2/√2`). -/
lemma Q_one_two [NeZero N] (hN2 : 2 < N) :
    Q N ⟨1, by omega⟩ ⟨2, hN2⟩ = 1 := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply]
  norm_num

/-- `Q` connects the second level back to the first with amplitude `1`. -/
lemma Q_two_one [NeZero N] (hN2 : 2 < N) :
    Q N ⟨2, hN2⟩ ⟨1, by omega⟩ = 1 := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply]
  norm_num

/-- `Q` reaches the first level only from the vacuum and the second
level. -/
lemma Q_apply_one_eq_zero [NeZero N] (hN : 1 < N) {m : Fin N}
    (h0 : (m : ℕ) ≠ 0) (h2 : (m : ℕ) ≠ 2) :
    Q N m ⟨1, hN⟩ = 0 := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply,
    creation_apply,
    if_neg (show ¬((m : ℕ) + 1 = ((1 : ℕ))) from by omega),
    if_neg (show ¬((1 : ℕ) + 1 = ((m : ℕ))) from by omega)]
  simp

/-- The quadrature is a symmetric matrix. -/
lemma Q_symm [NeZero N] (i j : Fin N) : Q N i j = Q N j i := by
  rw [Q, Matrix.smul_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.add_apply, annihilation_apply, annihilation_apply,
    creation_apply, creation_apply]
  rw [add_comm]

/-- The mode quadrature is a symmetric matrix. -/
lemma modeOpQ_symm [NeZero N] (k : Fin K) (c d : FieldConfig K N) :
    modeOp k (Q N) c d = modeOp k (Q N) d c := by
  rw [modeOp, modeOp]
  by_cases h : ∀ j, j ≠ k → c j = d j
  · rw [if_pos h, if_pos (fun j hj => (h j hj).symm), Q_symm]
  · rw [if_neg h, if_neg (fun h' => h (fun j hj => (h' j hj).symm))]

/-- The **two-quantum configuration** at mode `l`. -/
def exc2Cfg [NeZero N] (hN2 : 2 < N) (l : Fin K) : FieldConfig K N :=
  Function.update (vacCfg K N) l ⟨2, hN2⟩

@[simp] lemma exc2Cfg_self [NeZero N] (hN2 : 2 < N) (l : Fin K) :
    (exc2Cfg (K := K) hN2 l) l = ⟨2, hN2⟩ := by
  simp [exc2Cfg]

lemma exc2Cfg_of_ne [NeZero N] (hN2 : 2 < N) {l j : Fin K} (h : j ≠ l) :
    (exc2Cfg (K := K) hN2 l) j = 0 := by
  simp [exc2Cfg, h]

lemma vacCfg_ne_exc2Cfg [NeZero N] (hN2 : 2 < N) (k : Fin K) :
    vacCfg K N ≠ exc2Cfg hN2 k := by
  intro h
  have hk := congrFun h k
  rw [vacCfg_apply, exc2Cfg_self] at hk
  exact absurd (congrArg Fin.val hk) (by simp)

/-- From the one-quantum configuration, the mode quadrature reaches only
the vacuum and the two-quantum configuration. -/
lemma modeOp_Q_apply_exc [NeZero N] (hN2 : 2 < N) (k : Fin K)
    {e : FieldConfig K N} (h0 : e ≠ vacCfg K N) (h2 : e ≠ exc2Cfg hN2 k) :
    modeOp k (Q N) e (excCfg (show 1 < N by omega) k) = 0 := by
  by_cases hoff : ∀ j, j ≠ k → e j = (vacCfg K N) j
  · rw [modeOp_apply_of_agree k _ (fun j hj => by
      rw [hoff j hj, vacCfg_apply, excCfg_of_ne _ hj]),
      excCfg_self]
    refine Q_apply_one_eq_zero (show 1 < N by omega) ?_ ?_
    · intro hval
      refine h0 (funext fun j => ?_)
      by_cases hj : j = k
      · subst hj
        rw [vacCfg_apply]
        exact Fin.ext (by simpa using hval)
      · rw [hoff j hj]
    · intro hval
      refine h2 (funext fun j => ?_)
      by_cases hj : j = k
      · subst hj
        rw [exc2Cfg_self]
        exact Fin.ext (by simpa using hval)
      · rw [hoff j hj, vacCfg_apply, exc2Cfg_of_ne hN2 hj]
  · rw [modeOp, if_neg (fun h' => hoff (fun j hj => by
      rw [h' j hj, excCfg_of_ne _ hj, vacCfg_apply]))]

/-- The equal-time single-mode second moment: `(Q_k²)(vac, vac) = 1/2`. -/
lemma modeOpQ_sq_vac [NeZero N] (hN : 1 < N) (k : Fin K) :
    (modeOp k (Q N) * modeOp k (Q N)) (vacCfg K N) (vacCfg K N)
      = 2⁻¹ := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
  · rw [modeOpQ_symm,
      modeOp_apply_of_agree k _ (fun j hj => by
        rw [excCfg_of_ne hN hj, vacCfg_apply]),
      excCfg_self, vacCfg_apply, Q_one_zero hN]
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  · intro c _ hc
    rw [modeOp_Q_apply_vac hN k c hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The column of `Q_k²` at the vacuum: mass `1/2` on the vacuum, `1/√2`
on the two-quantum configuration, nothing else. -/
lemma modeOpQ_sq_apply_vac [NeZero N] (hN2 : 2 < N) (k : Fin K)
    (e : FieldConfig K N) :
    (modeOp k (Q N) * modeOp k (Q N)) e (vacCfg K N)
      = if e = vacCfg K N then 2⁻¹
        else if e = exc2Cfg hN2 k then (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        else 0 := by
  classical
  have hN : 1 < N := by omega
  split_ifs with h1 h2
  · subst h1
    exact modeOpQ_sq_vac hN k
  · subst h2
    rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
    · rw [modeOp_apply_of_agree k _ (fun j hj => by
          rw [exc2Cfg_of_ne hN2 hj, excCfg_of_ne hN hj]),
        modeOp_apply_of_agree k _ (fun j hj => by
          rw [excCfg_of_ne hN hj, vacCfg_apply]),
        exc2Cfg_self, excCfg_self, vacCfg_apply, Q_two_one hN2,
        Q_one_zero hN, one_mul]
    · intro c _ hc
      rw [modeOp_Q_apply_vac hN k c hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
    · rw [modeOp_Q_apply_exc hN2 k h1 h2, zero_mul]
    · intro c _ hc
      rw [modeOp_Q_apply_vac hN k c hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The `Q_k²` column value at the two-quantum configuration. -/
lemma modeOpQ_sq_exc2_vac [NeZero N] (hN2 : 2 < N) (k : Fin K) :
    (modeOp k (Q N) * modeOp k (Q N)) (exc2Cfg hN2 k) (vacCfg K N)
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  rw [modeOpQ_sq_apply_vac hN2 k,
    if_neg (Ne.symm (vacCfg_ne_exc2Cfg hN2 k)), if_pos rfl]

/-- **The equal-time four-point function**
`⟨vac∣ Q_k Q_l Q_m Q_p ∣vac⟩`. -/
noncomputable def eqFourPoint [NeZero N] (k l m p : Fin K) : ℂ :=
  (modeOp k (Q N) * modeOp l (Q N) * modeOp m (Q N) * modeOp p (Q N))
    (vacCfg K N) (vacCfg K N)

/-- ★★ **All four equal**: `⟨vac∣Q_k⁴∣vac⟩ = 3/4` — Wick's three pairings
of `½` each, and the first place the two-quantum level enters (`2 < N`
required: at `N = 2` the value is `1/4`). -/
theorem eqFourPoint_same [NeZero N] (hN2 : 2 < N) (k : Fin K) :
    eqFourPoint (N := N) k k k k = 3 / 4 := by
  classical
  rw [eqFourPoint, mul_assoc (modeOp k (Q N) * modeOp k (Q N)),
    Matrix.mul_apply]
  have hsym : ∀ e, (modeOp k (Q N) * modeOp k (Q N)) (vacCfg K N) e
      = (modeOp k (Q N) * modeOp k (Q N)) e (vacCfg K N) := by
    intro e
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [modeOpQ_symm k (vacCfg K N) c, modeOpQ_symm k c e, mul_comm]
  rw [Finset.sum_congr rfl (fun e _ => by rw [hsym e])]
  rw [← Finset.sum_subset
      (Finset.subset_univ ({vacCfg K N, exc2Cfg hN2 k} : Finset _))
      (fun e _ he => by
        rw [modeOpQ_sq_apply_vac hN2 k e,
          if_neg (fun h => he (by simp [h])),
          if_neg (fun h => he (by simp [h])), zero_mul])]
  rw [Finset.sum_pair (vacCfg_ne_exc2Cfg hN2 k),
    modeOpQ_sq_vac (show 1 < N by omega) k, modeOpQ_sq_exc2_vac hN2 k]
  rw [show ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹)
      = 2⁻¹ from by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num]
  norm_num

/-- ★★ **Two pairs, grouped**: `⟨vac∣Q_k²Q_l²∣vac⟩ = 1/4` for `k ≠ l` —
the one surviving Wick pairing, via clustering
(`diag_entry_mul_of_disjointSupport`). -/
theorem eqFourPoint_pair [NeZero N] (hN : 1 < N) {k l : Fin K}
    (hkl : k ≠ l) :
    eqFourPoint (N := N) k k l l = 1 / 4 := by
  rw [eqFourPoint, mul_assoc (modeOp k (Q N) * modeOp k (Q N)),
    diag_entry_mul_of_disjointSupport (by simpa using hkl)
      ((modeOp_supportedOn k (Q N)).mul (modeOp_supportedOn k (Q N)))
      ((modeOp_supportedOn l (Q N)).mul (modeOp_supportedOn l (Q N))),
    modeOpQ_sq_vac hN k, modeOpQ_sq_vac hN l]
  norm_num

/-- **Two pairs, alternating**: `⟨vac∣Q_kQ_lQ_kQ_l∣vac⟩ = 1/4` — the
commutation of disjoint modes reduces it to the grouped case. -/
theorem eqFourPoint_alt [NeZero N] (hN : 1 < N) {k l : Fin K}
    (hkl : k ≠ l) :
    eqFourPoint (N := N) k l k l = 1 / 4 := by
  have h := eqFourPoint_pair (N := N) hN hkl
  rw [eqFourPoint] at h ⊢
  rw [mul_assoc (modeOp k (Q N)) (modeOp k (Q N)) (modeOp l (Q N)),
    commute_modeOp hkl, ← mul_assoc] at h
  exact h

/-- **Two pairs, nested**: `⟨vac∣Q_kQ_lQ_lQ_k∣vac⟩ = 1/4`. -/
theorem eqFourPoint_outer [NeZero N] (hN : 1 < N) {k l : Fin K}
    (hkl : k ≠ l) :
    eqFourPoint (N := N) k l l k = 1 / 4 := by
  have h := eqFourPoint_alt (N := N) hN hkl
  rw [eqFourPoint] at h ⊢
  rw [mul_assoc (modeOp k (Q N) * modeOp l (Q N))] at h
  nth_rewrite 2 [commute_modeOp hkl] at h
  rw [← mul_assoc] at h
  exact h

/-- A mode appearing **once** (first position) kills the expectation:
`Q` has no vacuum diagonal, and clustering isolates it. -/
theorem eqFourPoint_single₁ [NeZero N] {k l m p : Fin K}
    (h1 : k ≠ l) (h2 : k ≠ m) (h3 : k ≠ p) :
    eqFourPoint (N := N) k l m p = 0 := by
  classical
  have hsupp : SupportedOn ({l} ∪ {m} ∪ {p} : Finset (Fin K))
      (modeOp l (Q N) * modeOp m (Q N) * modeOp p (Q N)) := by
    refine SupportedOn.mul (SupportedOn.mul ?_ ?_) ?_
    · exact SupportedOn.mono
        (Finset.Subset.trans Finset.subset_union_left
          Finset.subset_union_left) (modeOp_supportedOn l (Q N))
    · exact SupportedOn.mono
        (Finset.Subset.trans Finset.subset_union_right
          Finset.subset_union_left) (modeOp_supportedOn m (Q N))
    · exact SupportedOn.mono Finset.subset_union_right
        (modeOp_supportedOn p (Q N))
  have hdisj : Disjoint ({k} : Finset (Fin K)) ({l} ∪ {m} ∪ {p}) := by
    simp only [Finset.disjoint_left, Finset.mem_singleton,
      Finset.mem_union]
    rintro x rfl
    simp [h1, h2, h3]
  rw [eqFourPoint, mul_assoc (modeOp k (Q N) * modeOp l (Q N)),
    mul_assoc (modeOp k (Q N)),
    diag_entry_mul_of_disjointSupport hdisj (modeOp_supportedOn k (Q N))
      (by rw [← mul_assoc]; exact hsupp),
    modeOp_apply_of_agree k _ (fun j _ => rfl), vacCfg_apply,
    Q_zero_zero, zero_mul]

/-- A mode appearing once (second position) kills the expectation. -/
theorem eqFourPoint_single₂ [NeZero N] {k l m p : Fin K}
    (h1 : l ≠ k) (h2 : l ≠ m) (h3 : l ≠ p) :
    eqFourPoint (N := N) k l m p = 0 := by
  have h := eqFourPoint_single₁ (N := N) (k := l) (l := k) (m := m)
    (p := p) h1 h2 h3
  rw [eqFourPoint] at h ⊢
  rw [commute_modeOp h1] at h
  exact h

/-- A mode appearing once (third position) kills the expectation. -/
theorem eqFourPoint_single₃ [NeZero N] {k l m p : Fin K}
    (h1 : m ≠ k) (h2 : m ≠ l) (h3 : m ≠ p) :
    eqFourPoint (N := N) k l m p = 0 := by
  have h := eqFourPoint_single₁ (N := N) (k := m) (l := k) (m := l)
    (p := p) h1 h2 h3
  rw [eqFourPoint] at h ⊢
  rw [commute_modeOp h1, mul_assoc (modeOp k (Q N)),
    commute_modeOp h2, ← mul_assoc] at h
  exact h

/-- A mode appearing once (fourth position) kills the expectation. -/
theorem eqFourPoint_single₄ [NeZero N] {k l m p : Fin K}
    (h1 : p ≠ k) (h2 : p ≠ l) (h3 : p ≠ m) :
    eqFourPoint (N := N) k l m p = 0 := by
  have h := eqFourPoint_single₁ (N := N) (k := p) (l := k) (m := l)
    (p := m) h1 h2 h3
  rw [eqFourPoint] at h ⊢
  rw [commute_modeOp h1, mul_assoc (modeOp k (Q N)), commute_modeOp h2,
    ← mul_assoc, mul_assoc (modeOp k (Q N) * modeOp l (Q N)),
    commute_modeOp h3, ← mul_assoc] at h
  exact h

/-- ★★ **Wick's four-point theorem at the cutoff, packaged** (CV-23a): above the
truncation threshold `2 < N` the equal-time four-point function IS the pairing sum

  `⟨Q_k Q_l Q_m Q_p⟩ = Σ_pairings ∏ ½δ
     = ¼(δ_{kl}δ_{mp} + δ_{km}δ_{lp} + δ_{kp}δ_{lm})`,

one formula over every mode pattern — the coincidence-pattern table (`eqFourPoint_same`,
`_pair`/`_alt`/`_outer`, `_single₁`–`₄`) assembled into the textbook shape. The `2 < N`
hypothesis is load-bearing exactly where the table says: at `N = 2` the all-equal
pattern is `1/4`, not the Gaussian `3/4`, and the formula fails — truncation honesty,
not a technical convenience. -/
theorem eqFourPoint_wick [NeZero N] (hN2 : 2 < N) (k l m p : Fin K) :
    eqFourPoint (N := N) k l m p
      = (if k = l then (2 : ℂ)⁻¹ else 0) * (if m = p then (2 : ℂ)⁻¹ else 0)
        + (if k = m then (2 : ℂ)⁻¹ else 0) * (if l = p then (2 : ℂ)⁻¹ else 0)
        + (if k = p then (2 : ℂ)⁻¹ else 0) * (if l = m then (2 : ℂ)⁻¹ else 0) := by
  have hN : 1 < N := by omega
  by_cases hkl : k = l
  · subst hkl
    by_cases hkm : k = m
    · subst hkm
      by_cases hkp : k = p
      · subst hkp
        rw [eqFourPoint_same hN2]
        norm_num
      · rw [eqFourPoint_single₄ (fun h => hkp h.symm) (fun h => hkp h.symm)
          (fun h => hkp h.symm)]
        simp [hkp]
    · by_cases hmp : m = p
      · subst hmp
        rw [eqFourPoint_pair hN hkm]
        simp [hkm]
        norm_num
      · rw [eqFourPoint_single₃ (fun h => hkm h.symm) (fun h => hkm h.symm) hmp]
        simp [hkm, hmp]
  · by_cases hkm : k = m
    · subst hkm
      by_cases hlp : l = p
      · subst hlp
        rw [eqFourPoint_alt hN (fun h => hkl h)]
        simp [hkl]
        norm_num
      · rw [eqFourPoint_single₂ (fun h => hkl h.symm) (fun h => hkl h.symm) hlp]
        simp [hkl, Ne.symm hkl, hlp]
    · by_cases hkp : k = p
      · subst hkp
        by_cases hlm : l = m
        · subst hlm
          rw [eqFourPoint_outer hN hkl]
          simp [hkl]
          norm_num
        · rw [eqFourPoint_single₂ (fun h => hkl h.symm) hlm (fun h => hkl h.symm)]
          simp [hkl, Ne.symm hkl, hlm]
      · rw [eqFourPoint_single₁ hkl hkm hkp]
        simp [hkl, hkm, hkp]

end CSD.CV

