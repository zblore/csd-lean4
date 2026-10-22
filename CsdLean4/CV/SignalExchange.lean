/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FieldStructuredFlow
public import CsdLean4.Mathlib.Analysis.Normed.Algebra.ExpUnique

/-!
# The signal exchange: a two-site hop, exact transfer with its phase, and the Rabi return

**Category:** 3-Local (CV; the smallest physical signal of the clock-and-echo programme).
BACKLOG #183 (out of #39; the first of #183–#189).

Two sites `A = 0` and `B = 1`, each holding `0` or `1` excitation (`FieldConfig 2 2`). The **hop**
`X = |10⟩⟨01| + |01⟩⟨10|` exchanges the one-excitation configurations and does nothing else, so
`X² = P` (the one-excitation projector) and `X P = X`, and the Schrödinger generator `−(i J/ħ) X`
of the Hamiltonian `H = J X` has the flow

  `U(t) = 1 + (cos θ − 1) P − i sin θ · X`,   `θ = J t / ħ`,

by the ODE uniqueness of `ExpUnique.lean`, not by a series. The sender's message is the occupancy of
`A` (`0` or `1`); the receiver reads the occupancy of `B`.

* `hopX`, `oneExc`, `hopGen`, ★ `hopFlow J ħ : FieldStructuredFlow 2 2` — **the exchange is an
  instance of the CSD field-structured dynamics**, so `FieldStructuredFlow.lightcone` applies to it
  with no further hypothesis;
* ★★ `hopFlow_val_eq` — the flow in closed form;
* `hopTime J ħ = π ħ / (2 J)`, ★★ `transfer_at_hopTime` — **the excitation at `A` becomes `−i` times
  the excitation at `B`**: the transfer is exact and the phase is a theorem;
* `roundTrip J ħ = 2 · hopTime`, ★★ `return_at_roundTrip` — **the echo is the Rabi return**: at
  `2 τ_hop` the excitation is back at `A` with phase `−1`, and the arena point is the message point
  again (`arenaFlow_roundTrip`); the round trip is nonzero (`roundTrip_pos`);
* `receiver_readout_one`, `receiver_readout_zero` — the receiver's readout `arenaObs occB` is
  `sin² θ` for message `1` and `0` for message `0`;
* ★★★ `receiver_distinguishes` — **at `τ_hop` the readout is `1` versus `0`**;
* ★ `partial_transfer_before_hopTime` — **complete transfer at `τ_hop` does not mean silence
  before it**: on `(0, τ_hop)` the readout is strictly between `0` and `1`;
* `influence_of_message` — the two preparations differ only in the occupancy of `A`
  (`msgConfig_siteB`) and give different receiver readouts: causal influence by comparison of
  preparations, not inferred from a correlation;
* ★★★ `signal_exchange` — the package.

## Drift check

The hop is quantum mechanics — the isolated item's Hamiltonian flow on the arena (R-016′), the
calculation engine. The *records* of emission at `A` and reception at `B` are ontic writes in `Σ`
and belong to #186; nothing here is a record. Successful transmission is a readout at a *stated*
time, not a propagation bound; the Lieb–Robinson cone of `FieldStructuredFlow.lightcone` bounds
what can happen, it does not say what does.

## Honest scope

* Two sites and one excitation; the "message" is a one-bit occupancy. Longer chains need a
  sequentially activated coupling schedule to transfer exactly, which this file does not claim.
* `J` and `ħ` are positive reals in consistent units (`J` an energy, `ħ` an action, `J/ħ` a rate);
  no numerical value is derived from either.
* Zero processing delay at `B`: the echo is the free Rabi return, not a reflection protocol.

References: `specs/BACKLOG.md` #183, #39, #186; `specs/records-to-spacetime-scoping.md` §4;
`CV/FieldStructuredFlow.lean` (`FieldStructuredFlow`, `lightcone`), `CV/ArenaBridge.lean`
(`arenaKick_mk`, `arenaObs`, `dmVec`), `Mathlib/Analysis/Normed/Algebra/ExpUnique.lean`.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

/-! ### Configurations: two sites, one bit each -/

/-- Two sites, occupancy `0` or `1`. -/
abbrev HopConfig := FieldConfig 2 2

/-- The vacuum. -/
def vacC : HopConfig := ![0, 0]

/-- One excitation at `A`. -/
def excA : HopConfig := ![1, 0]

/-- One excitation at `B`. -/
def excB : HopConfig := ![0, 1]

theorem excA_ne_excB : excA ≠ excB := by decide

theorem vacC_ne_excA : vacC ≠ excA := by decide

theorem vacC_ne_excB : vacC ≠ excB := by decide

/-- The sender's message `b` is the occupancy of `A`; `B` is empty in both preparations. -/
def msgConfig (b : Fin 2) : HopConfig := ![b, 0]

theorem msgConfig_zero : msgConfig 0 = vacC := rfl

theorem msgConfig_one : msgConfig 1 = excA := rfl

/-- The two preparations agree at the receiver's site. -/
theorem msgConfig_siteB (b : Fin 2) : msgConfig b 1 = 0 := rfl

/-! ### The hop and the one-excitation projector -/

/-- The hop `|10⟩⟨01| + |01⟩⟨10|`. -/
noncomputable def hopX : Matrix HopConfig HopConfig ℂ :=
  single excA excB 1 + single excB excA 1

/-- The projector on the one-excitation configurations. -/
noncomputable def oneExc : Matrix HopConfig HopConfig ℂ :=
  single excA excA 1 + single excB excB 1

theorem hopX_mul_hopX : hopX * hopX = oneExc := by
  simp only [hopX, oneExc, add_mul, mul_add, single_mul_single_same,
    single_mul_single_of_ne (1 : ℂ) excA excB excA excA_ne_excB.symm (1 : ℂ),
    single_mul_single_of_ne (1 : ℂ) excB excA excB excA_ne_excB (1 : ℂ), mul_one, zero_add, add_zero]
  exact add_comm _ _

theorem hopX_mul_oneExc : hopX * oneExc = hopX := by
  simp only [hopX, oneExc, add_mul, mul_add, single_mul_single_same,
    single_mul_single_of_ne (1 : ℂ) excA excB excA excA_ne_excB.symm (1 : ℂ),
    single_mul_single_of_ne (1 : ℂ) excB excA excB excA_ne_excB (1 : ℂ), mul_one, zero_add, add_zero]
  exact add_comm _ _

theorem single_conjTranspose {ι : Type*} [DecidableEq ι] (i j : ι) (a : ℂ) :
    (single i j a)ᴴ = single j i (star a) := by
  ext i' j'
  simp only [conjTranspose_apply, Matrix.single, Matrix.of_apply]
  by_cases h : j = i' ∧ i = j'
  · simp [h.1, h.2]
  · have h' : ¬ (i = j' ∧ j = i') := fun h' => h ⟨h'.2, h'.1⟩
    simp [h, h']

theorem hopX_conjTranspose : hopXᴴ = hopX := by
  rw [hopX, conjTranspose_add, single_conjTranspose, single_conjTranspose, star_one, add_comm]

/-! ### The generator and the field-structured flow -/

/-- The Schrödinger generator `−(i J/ħ) X` of the Hamiltonian `H = J X`. -/
noncomputable def hopGen (J ħ : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (-(Complex.I * ((J / ħ : ℝ) : ℂ))) • hopX

theorem hopGen_skew (J ħ : ℝ) : (hopGen J ħ)ᴴ = -(hopGen J ħ) :=
  skew_neg_I_smul_of_hermitian (J / ħ) hopX_conjTranspose

/-- On two sites every operator is supported on `{A, B}`. -/
theorem supportedOn_pair (M : Matrix HopConfig HopConfig ℂ) :
    SupportedOn ({0, 1} : Finset (Fin 2)) M where
  offDiag := by
    intro c d k hk _
    exact absurd (by fin_cases k <;> simp) hk
  indep := by
    intro c d c' d' hc hd _ _
    have hc' : c = c' := funext fun k => hc k (by fin_cases k <;> simp)
    have hd' : d = d' := funext fun k => hd k (by fin_cases k <;> simp)
    rw [hc', hd']

/-- ★ **The exchange as a field-structured flow**: one coupling edge `(A, B)` carrying the hop. -/
noncomputable def hopFlow (J ħ : ℝ) : FieldStructuredFlow 2 2 where
  edges := {(0, 1)}
  piece := fun _ => hopGen J ħ
  piece_supported := by
    intro e he
    rw [Finset.mem_singleton] at he
    subst he
    exact supportedOn_pair _
  gen_skew := by
    rw [Finset.sum_singleton]
    exact hopGen_skew J ħ

theorem hopFlow_val (J ħ t : ℝ) : ((hopFlow J ħ).flow t).val = exp (t • hopGen J ħ) := by
  simp only [FieldStructuredFlow.flow_val, hopFlow, Finset.sum_singleton]

/-- The phase angle `θ = J t / ħ`. -/
noncomputable def hopAngle (J ħ t : ℝ) : ℝ := J / ħ * t

theorem smul_hopGen (J ħ t : ℝ) :
    t • hopGen J ħ = (((-hopAngle J ħ t : ℝ) : ℂ) * Complex.I) • hopX := by
  rw [hopGen, matrix_real_smul, smul_smul, hopAngle]
  congr 1
  push_cast
  ring

/-- ★★ **The flow in closed form**: `U(t) = 1 + (cos θ − 1) P − i sin θ · X`. -/
theorem hopFlow_val_eq (J ħ t : ℝ) :
    ((hopFlow J ħ).flow t).val
      = 1 + ((Real.cos (hopAngle J ħ t) - 1 : ℝ) : ℂ) • oneExc
          + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • hopX := by
  rw [hopFlow_val, smul_hopGen, exp_smul_eq_cosh_sinh hopX_mul_hopX hopX_mul_oneExc]
  have hc : Complex.cosh (((-hopAngle J ħ t : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (hopAngle J ħ t) - 1 : ℝ) : ℂ) + 1 := by
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_neg]
    push_cast
    ring
  have hs : Complex.sinh (((-hopAngle J ħ t : ℝ) : ℂ) * Complex.I)
      = -(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ)) := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_neg]
    push_cast
    ring
  rw [hc, hs, add_sub_cancel_right]

/-! ### The column of the flow at a basis configuration -/

/-- The flow applied to the excitation at `A`: `cos θ · e_A − i sin θ · e_B`. -/
theorem hopFlow_mulVec_excA (J ħ t : ℝ) :
    ((hopFlow J ħ).flow t).val *ᵥ Pi.single excA (1 : ℂ)
      = ((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • Pi.single excA (1 : ℂ)
          + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • Pi.single excB (1 : ℂ) := by
  rw [mulVec_single_one, hopFlow_val_eq]
  funext c
  simp only [Matrix.col, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, oneExc, hopX, Matrix.single, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  by_cases hA : excA = c
  · subst hA
    simp [excA_ne_excB, excA_ne_excB.symm]
  · by_cases hB : excB = c
    · subst hB
      simp [hA, excA_ne_excB.symm]
    · simp [hA, hB, Ne.symm hA, Ne.symm hB]

/-- The flow fixes the vacuum. -/
theorem hopFlow_mulVec_vacC (J ħ t : ℝ) :
    ((hopFlow J ħ).flow t).val *ᵥ Pi.single vacC (1 : ℂ) = Pi.single vacC (1 : ℂ) := by
  rw [mulVec_single_one, hopFlow_val_eq]
  funext c
  simp only [Matrix.col, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, oneExc, hopX, Matrix.single, Matrix.of_apply, Pi.single_apply, smul_eq_mul]
  by_cases hv : c = vacC <;> simp [hv, vacC_ne_excA.symm, vacC_ne_excB.symm]

/-! ### Arena points and the receiver's readout -/

/-- The basis vector of a configuration. -/
noncomputable def basisVec (c : HopConfig) : EuclideanSpace ℂ HopConfig :=
  PiLp.single 2 c (1 : ℂ)

theorem basisVec_apply (c c' : HopConfig) :
    basisVec c c' = (Pi.single c (1 : ℂ) : HopConfig → ℂ) c' := rfl

theorem basisVec_ne_zero (c : HopConfig) : basisVec c ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [basisVec, PiLp.norm_single, norm_one, norm_zero] at this
  exact one_ne_zero this

/-- The arena point of message `b`: excitation `b` at `A`, nothing at `B`. -/
noncomputable def msgPoint (b : Fin 2) : FieldArena 2 2 :=
  Projectivization.mk ℂ (basisVec (msgConfig b)) (basisVec_ne_zero _)

theorem msgPoint_zero : msgPoint 0 = Projectivization.mk ℂ (basisVec vacC) (basisVec_ne_zero _) :=
  rfl

theorem msgPoint_one : msgPoint 1 = Projectivization.mk ℂ (basisVec excA) (basisVec_ne_zero _) :=
  rfl

/-- The receiver's observable: "the excitation sits at `B`". -/
noncomputable def occB : Matrix HopConfig HopConfig ℂ := single excB excB 1

/-- The Born weight of a basis projector at a ray: `‖v j‖² / ‖v‖²`. -/
theorem arenaObs_single_mk {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) (j : ι) :
    arenaObs (single j j (1 : ℂ)) (Projectivization.mk ℂ v hv) = ‖v j‖ ^ 2 / ‖v‖ ^ 2 := by
  rw [arenaObs, arenaDM_mk]
  have htr : (dmVec v * single j j (1 : ℂ)).trace = dmVec v j j := by
    rw [Matrix.trace, Finset.sum_eq_single j]
    · rw [Matrix.diag_apply]
      exact (mul_single_apply_same (1 : ℂ) j j j (dmVec v)).trans (mul_one _)
    · intro i _ hij
      rw [Matrix.diag_apply]
      exact mul_single_apply_of_ne (1 : ℂ) j j i i hij (dmVec v)
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [htr, dmVec_apply', mul_star_self_eq_norm_sq, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    RCLike.re_to_complex, Complex.ofReal_re, div_eq_inv_mul]

/-- The vector the flow produces from message `1`, in Euclidean form. -/
theorem toEuclideanLin_hopFlow_excA (J ħ t : ℝ) :
    Matrix.toEuclideanLin ((hopFlow J ħ).flow t).val (basisVec excA)
      = ((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • basisVec excA
          + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • basisVec excB := by
  ext c
  rw [toEuclideanLin_coord]
  have hfun : (fun j => basisVec excA j) = Pi.single excA (1 : ℂ) := funext fun j => rfl
  rw [hfun, hopFlow_mulVec_excA]
  simp only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, basisVec_apply]

theorem toEuclideanLin_hopFlow_vacC (J ħ t : ℝ) :
    Matrix.toEuclideanLin ((hopFlow J ħ).flow t).val (basisVec vacC) = basisVec vacC := by
  ext c
  rw [toEuclideanLin_coord]
  have hfun : (fun j => basisVec vacC j) = Pi.single vacC (1 : ℂ) := funext fun j => rfl
  rw [hfun, hopFlow_mulVec_vacC, basisVec_apply]

/-- The transferred vector has unit norm: `cos² θ + sin² θ = 1`. -/
theorem norm_transferred (J ħ t : ℝ) :
    ‖((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • basisVec excA
        + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • basisVec excB‖ = 1 := by
  set w := ((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • basisVec excA
      + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • basisVec excB with hw
  have hA : w excA = ((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) := by
    simp [hw, basisVec_apply, excA_ne_excB]
  have hB : w excB = -(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ)) := by
    simp [hw, basisVec_apply, excA_ne_excB.symm]
  have hother : ∀ c : HopConfig, c ≠ excA ∧ c ≠ excB → w c = 0 := by
    intro c hc
    simp [hw, basisVec_apply, hc.1, hc.2]
  have hsum : ∑ c : HopConfig, ‖w c‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_add excA excB excA_ne_excB
      (fun c _ hc => by rw [hother c hc, norm_zero]; norm_num)
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h), hA, hB]
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Real.cos_sq_add_sin_sq]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [← euclid_sum_norm_sq, hsum]
  have hnn : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith [sq_nonneg (‖w‖ - 1), sq_nonneg (‖w‖ + 1)]

/-- **The receiver's readout for message `1` is `sin² θ`.** -/
theorem receiver_readout_one (J ħ t : ℝ) :
    arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1))
      = Real.sin (hopAngle J ħ t) ^ 2 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_one, arenaKick_mk, occB,
    arenaObs_single_mk, toEuclideanLin_hopFlow_excA, norm_transferred]
  have hB : (((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • basisVec excA
      + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • basisVec excB) excB
        = -(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ)) := by
    simp [basisVec_apply, excA_ne_excB.symm]
  rw [hB, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, one_pow, div_one]

/-- **The receiver's readout for message `0` is `0`**: the vacuum does not move. -/
theorem receiver_readout_zero (J ħ t : ℝ) :
    arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 0)) = 0 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_zero, arenaKick_mk, occB,
    arenaObs_single_mk, toEuclideanLin_hopFlow_vacC, basisVec_apply,
    Pi.single_eq_of_ne vacC_ne_excB.symm, norm_zero]
  simp

/-! ### The hop time, the transfer, the return -/

/-- `τ_hop = π ħ / (2 J)`: the time of complete transfer. -/
noncomputable def hopTime (J ħ : ℝ) : ℝ := Real.pi * ħ / (2 * J)

/-- The round trip `2 τ_hop`. -/
noncomputable def roundTrip (J ħ : ℝ) : ℝ := 2 * hopTime J ħ

theorem hopTime_pos {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) : 0 < hopTime J ħ := by
  unfold hopTime
  positivity

/-- **The round trip is nonzero.** -/
theorem roundTrip_pos {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) : 0 < roundTrip J ħ := by
  unfold roundTrip
  linarith [hopTime_pos hJ hħ]

theorem hopAngle_hopTime {J ħ : ℝ} (hJ : J ≠ 0) (hħ : ħ ≠ 0) :
    hopAngle J ħ (hopTime J ħ) = Real.pi / 2 := by
  unfold hopAngle hopTime
  field_simp

theorem hopAngle_roundTrip {J ħ : ℝ} (hJ : J ≠ 0) (hħ : ħ ≠ 0) :
    hopAngle J ħ (roundTrip J ħ) = Real.pi := by
  unfold hopAngle roundTrip hopTime
  field_simp

/-- ★★ **Exact transfer with its phase**: at `τ_hop` the excitation at `A` is `−i` times the
excitation at `B`. -/
theorem transfer_at_hopTime {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    Matrix.toEuclideanLin ((hopFlow J ħ).flow (hopTime J ħ)).val (basisVec excA)
      = (-Complex.I) • basisVec excB := by
  rw [toEuclideanLin_hopFlow_excA, hopAngle_hopTime hJ.ne' hħ.ne', Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- ★★ **The echo is the Rabi return**: at `2 τ_hop` the excitation is back at `A` with phase
`−1`. -/
theorem return_at_roundTrip {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    Matrix.toEuclideanLin ((hopFlow J ħ).flow (roundTrip J ħ)).val (basisVec excA)
      = (-1 : ℂ) • basisVec excA := by
  rw [toEuclideanLin_hopFlow_excA, hopAngle_roundTrip hJ.ne' hħ.ne', Real.cos_pi, Real.sin_pi]
  simp

/-- At `τ_hop` the arena point of message `1` is the ray of the excitation at `B`. -/
theorem arenaFlow_hopTime {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 1)
      = Projectivization.mk ℂ (basisVec excB) (basisVec_ne_zero _) := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_one, arenaKick_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨-Complex.I, ?_⟩
  rw [transfer_at_hopTime hJ hħ]

/-- At `2 τ_hop` the arena point of message `1` is the message point again. -/
theorem arenaFlow_roundTrip {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (hopFlow J ħ).arenaFlow (roundTrip J ħ) (msgPoint 1) = msgPoint 1 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_one, arenaKick_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨-1, ?_⟩
  rw [return_at_roundTrip hJ hħ]

/-! ### Distinguishing the messages, partial transfer, influence -/

/-- ★★★ **At `τ_hop` the receiver's readout is `1` for message `1` and `0` for message `0`.** -/
theorem receiver_distinguishes {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    arenaObs occB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 1)) = 1
      ∧ arenaObs occB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 0)) = 0 := by
  refine ⟨?_, receiver_readout_zero J ħ _⟩
  rw [receiver_readout_one, hopAngle_hopTime hJ.ne' hħ.ne', Real.sin_pi_div_two, one_pow]

/-- ★ **Partial transfer before `τ_hop`**: for `0 < t < τ_hop` the readout is strictly between
`0` and `1` — complete transfer at `τ_hop` does not mean silence at earlier times. -/
theorem partial_transfer_before_hopTime {J ħ t : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (ht : 0 < t)
    (ht' : t < hopTime J ħ) :
    0 < arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1))
      ∧ arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1)) < 1 := by
  rw [receiver_readout_one]
  have hrate : 0 < J / ħ := div_pos hJ hħ
  have hθ0 : 0 < hopAngle J ħ t := mul_pos hrate ht
  have hθ1 : hopAngle J ħ t < Real.pi / 2 := by
    rw [← hopAngle_hopTime hJ.ne' hħ.ne']
    exact mul_lt_mul_of_pos_left ht' hrate
  have hsin : 0 < Real.sin (hopAngle J ħ t) :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (hopAngle J ħ t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  refine ⟨by positivity, ?_⟩
  have := Real.sin_sq_add_cos_sq (hopAngle J ħ t)
  nlinarith

/-- **Causal influence by comparison of preparations**: the two message points differ only in the
occupancy of `A` (`msgConfig_siteB`), and at `τ_hop` their receiver readouts differ. -/
theorem influence_of_message {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    arenaObs occB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 1))
      ≠ arenaObs occB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 0)) := by
  obtain ⟨h1, h0⟩ := receiver_distinguishes hJ hħ
  rw [h1, h0]
  exact one_ne_zero

/-! ### The package -/

/-- ★★★ **The signal exchange.** The hop is a field-structured flow; at `τ_hop = πħ/2J` the
excitation at `A` has become `−i` times the excitation at `B` and the receiver's readout is `1`
for message `1` and `0` for message `0`; before `τ_hop` the transfer is partial; at the nonzero
round trip `2 τ_hop` the arena point is the message point again. -/
theorem signal_exchange {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (hopFlow J ħ).edges = {(0, 1)}
      ∧ Matrix.toEuclideanLin ((hopFlow J ħ).flow (hopTime J ħ)).val (basisVec excA)
          = (-Complex.I) • basisVec excB
      ∧ arenaObs occB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 1)) = 1
      ∧ arenaObs occB ((hopFlow J ħ).arenaFlow (hopTime J ħ) (msgPoint 0)) = 0
      ∧ (∀ t, 0 < t → t < hopTime J ħ →
          0 < arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1))
            ∧ arenaObs occB ((hopFlow J ħ).arenaFlow t (msgPoint 1)) < 1)
      ∧ 0 < roundTrip J ħ
      ∧ (hopFlow J ħ).arenaFlow (roundTrip J ħ) (msgPoint 1) = msgPoint 1 :=
  ⟨rfl, transfer_at_hopTime hJ hħ, (receiver_distinguishes hJ hħ).1,
    (receiver_distinguishes hJ hħ).2, fun _ ht ht' => partial_transfer_before_hopTime hJ hħ ht ht',
    roundTrip_pos hJ hħ, arenaFlow_roundTrip hJ hħ⟩

end CSD.CV

end
