/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DetunedExchange

/-!
# The two-site exchange with both sites detuned

**Category:** 3-Local (CV; the carrier side of BACKLOG #198, the autonomous echo).

In the echo of #199 both stations carry a pointer, so both sites of the exchange are detuned by
their own back-reaction: the carrier's Hamiltonian is

  `H = J X + Δ_A n_A + Δ_B n_B = H(Δ_B − Δ_A) + Δ_A P`,

with `H(Δ)` the detuned exchange of `DetunedExchange.lean` and `P` the one-excitation projector.
`P` commutes with everything, so the flow is the detuned exchange **in the difference** times a
phase on the one-excitation sector:

  `U(t) = e^{−iΔ_A t/ħ · P} · U_{Δ_B − Δ_A}(t)`.

The sector phase is invisible to every observable that preserves the sector and to the rays of the
two messages, so the whole of #194's carrier algebra transfers to the two-site case with
`Δ = Δ_B − Δ_A`, and nothing new happens beyond the difference. What is new in this file is the
**return**: at the detuned round trip `πħ/Ω'` the carrier is back at `A`, as a ray, exactly.

* `twoDetunedH`, ★ `twoDetunedH_eq` — **`H = H(Δ_B − Δ_A) + Δ_A P`**; `sectorGen`, `twoDetunedGen`,
  `twoDetunedGen_eq`, `twoDetunedGen_zero_left` — at `Δ_A = 0` it is the detuned exchange;
* ★ `twoDetunedFlow J ħ Δ_A Δ_B : FieldStructuredFlow 2 2` — **the two-site detuned exchange is a
  field-structured flow on the one edge**; `sectorPhase`, `sectorPhase_eq`, `sectorPhase_unitary`,
  `sectorPhase_commute`; ★★ `twoDetunedFlow_val_eq` — **the flow is the sector phase times the
  detuned exchange in the difference**, by `exp_add_of_commute`;
* ★★ `arenaObs_twoDetunedFlow` — **every observable commuting with `P` reads the same along both
  flows, at every arena point**; `occB_twoDetunedFlow`, `occA_twoDetunedFlow`,
  `arenaObs_oneExc_twoDetunedFlow` (the sector is conserved);
* ★★ `twoDetunedFlow_arenaFlow_msgPoint_one` — **on the ray of message `1` the two flows agree**;
  `twoDetunedFlow_msgPoint_zero` — the vacuum is fixed;
* ★★ `twoDetuned_readout_B_one`, `twoDetuned_readout_A_one` — **the occupancies for message `1`
  are `(J/Ω')² sin²(Ω't/ħ)` at `B` and `1 − (J/Ω')² sin²(Ω't/ħ)` at `A`**, `Ω' = √(J² +
  (Δ_B − Δ_A)²/4)`; `twoDetuned_readout_B_zero`, `twoDetuned_readout_A_zero` — both vanish for
  message `0`;
* `detunedRoundTrip` — `πħ/Ω' = 2 × detunedHopTime`; ★★★ `detunedFlow_return`,
  `twoDetuned_return` — **at the detuned round trip the carrier is back at `A` as a ray**, for the
  detuned exchange and for the two-site flow; `twoDetuned_return_occA`, `twoDetuned_return_occB`
  — with `n_A = 1`, `n_B = 0` there;
* `occHistA`, `occHistA_eq`, `continuous_occHistA_prod`, `occAccumA`, `occAccumA_eq`,
  `hasDerivAt_occAccumA` — **the occupancy history of `A` and its integral**, in terms of the
  detuned exchange's `occHist`/`occAccum`, continuous jointly in the ray and both detunings — what
  the pointer at `A` in #199 integrates; `continuous_twoDetunedFlow_prod`.

## Honest scope

* Nothing here is a record; the pointers that produce `Δ_A`, `Δ_B` and read the occupancies are
  #199's. This file is the carrier.
* `Δ_A`, `Δ_B` are real parameters; in #199 they are functions of conserved torus angles, so the
  flow at fixed angles is exactly this one.
* `J > 0` is assumed where the closed form divides by `Ω'`; `ħ > 0` where the round trip is
  computed.

References: `specs/BACKLOG.md` #198, #199, #194, #183; `CV/DetunedExchange.lean` (`detunedH`,
`detunedFlow`, `detunedFlow_val_eq`, `occHist`, `occAccum`), `CV/SignalExchange.lean` (`hopX`,
`oneExc`, `occB`, `msgPoint`), `Mathlib/Analysis/Normed/Algebra/ExpUnique.lean`
(`exp_smul_eq_cosh_sinh`).
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Projectivization Matrix.UnitaryGroup
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

/-! ### More of the algebra of `P`, `n_A`, `n_B` -/

theorem oneExc_conjTranspose : oneExcᴴ = oneExc := by
  rw [oneExc, conjTranspose_add, single_conjTranspose, single_conjTranspose, star_one]

theorem oneExc_mul_occB : oneExc * occB = occB := by
  simp only [oneExc, occB, add_mul, single_mul_single_same, single_mul_single_hop _ excA_ne_excB,
    mul_one, zero_add]

theorem occB_mul_oneExc : occB * oneExc = occB := by
  simp only [oneExc, occB, mul_add, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB.symm, mul_one, zero_add]

theorem oneExc_mul_occA : oneExc * occA = occA := by
  simp only [oneExc, occA, add_mul, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB.symm, mul_one, add_zero]

theorem occA_mul_oneExc : occA * oneExc = occA := by
  simp only [oneExc, occA, mul_add, single_mul_single_same, single_mul_single_hop _ excA_ne_excB,
    mul_one, add_zero]

/-- A matrix times `P`, read in the column of `A`: `P` fixes `e_A`. -/
theorem mul_oneExc_apply_excA (M : Matrix HopConfig HopConfig ℂ) (c : HopConfig) :
    (M * oneExc) c excA = M c excA := by
  rw [oneExc, mul_add, Matrix.add_apply, mul_single_apply_same,
    mul_single_apply_of_ne (c := (1 : ℂ)) excB excB c excA excA_ne_excB, mul_one, add_zero]

/-- A matrix times `P`, read in the vacuum column: `P` kills the vacuum. -/
theorem mul_oneExc_apply_vacC (M : Matrix HopConfig HopConfig ℂ) (c : HopConfig) :
    (M * oneExc) c vacC = 0 := by
  rw [oneExc, mul_add, Matrix.add_apply,
    mul_single_apply_of_ne (c := (1 : ℂ)) excA excA c vacC vacC_ne_excA,
    mul_single_apply_of_ne (c := (1 : ℂ)) excB excB c vacC vacC_ne_excB, add_zero]

theorem oneExc_apply_excA_excA : oneExc excA excA = 1 := by
  simp [oneExc, Matrix.single, Matrix.of_apply, excA_ne_excB.symm]

theorem oneExc_apply_ne_excA {c : HopConfig} (hc : c ≠ excA) : oneExc c excA = 0 := by
  simp [oneExc, Matrix.single, Matrix.of_apply, hc.symm, excA_ne_excB.symm]

theorem commute_oneExc_detunedH (J Δ : ℝ) : Commute oneExc (detunedH J Δ) := by
  show oneExc * detunedH J Δ = detunedH J Δ * oneExc
  rw [detunedH, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
    oneExc_mul_hopX, hopX_mul_oneExc, oneExc_mul_occB, occB_mul_oneExc]

theorem commute_oneExc_detunedGen (J ħ Δ : ℝ) : Commute oneExc (detunedGen J ħ Δ) :=
  (commute_oneExc_detunedH J Δ).smul_right _

/-- `P` commutes with the detuned flow. -/
theorem oneExc_commute_detunedFlowVal (J ħ Δ t : ℝ) :
    oneExc * ((detunedFlow J ħ Δ).flow t).val = ((detunedFlow J ħ Δ).flow t).val * oneExc := by
  rw [detunedFlow_val]
  exact (((commute_oneExc_detunedGen J ħ Δ).smul_right t).exp_right).eq

/-! ### The Hamiltonian with both sites detuned -/

/-- `H = J X + Δ_A n_A + Δ_B n_B`. -/
noncomputable def twoDetunedH (J ΔA ΔB : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (J : ℂ) • hopX + (ΔA : ℂ) • occA + (ΔB : ℂ) • occB

theorem twoDetunedH_conjTranspose (J ΔA ΔB : ℝ) : (twoDetunedH J ΔA ΔB)ᴴ = twoDetunedH J ΔA ΔB := by
  rw [twoDetunedH, conjTranspose_add, conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    conjTranspose_smul, hopX_conjTranspose, occA_conjTranspose, occB_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal]

/-- ★ **The two-site Hamiltonian is the detuned exchange in the difference plus a sector energy**:
`H = H(Δ_B − Δ_A) + Δ_A P`. -/
theorem twoDetunedH_eq (J ΔA ΔB : ℝ) :
    twoDetunedH J ΔA ΔB = detunedH J (ΔB - ΔA) + (ΔA : ℂ) • oneExc := by
  rw [twoDetunedH, detunedH, oneExc_eq_occA_add_occB]
  push_cast
  module

/-- At `Δ_A = 0` the two-site Hamiltonian is the detuned exchange. -/
theorem twoDetunedH_zero_left (J Δ : ℝ) : twoDetunedH J 0 Δ = detunedH J Δ := by
  rw [twoDetunedH_eq, sub_zero, Complex.ofReal_zero, zero_smul, add_zero]

/-- The sector generator `−(i Δ_A/ħ) P`. -/
noncomputable def sectorGen (ħ ΔA : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (-(Complex.I * ((ΔA / ħ : ℝ) : ℂ))) • oneExc

theorem sectorGen_skew (ħ ΔA : ℝ) : (sectorGen ħ ΔA)ᴴ = -(sectorGen ħ ΔA) :=
  skew_neg_I_smul_of_hermitian (ΔA / ħ) oneExc_conjTranspose

/-- The Schrödinger generator `−(i/ħ) H`. -/
noncomputable def twoDetunedGen (J ħ ΔA ΔB : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (-(Complex.I * ((1 / ħ : ℝ) : ℂ))) • twoDetunedH J ΔA ΔB

theorem twoDetunedGen_skew (J ħ ΔA ΔB : ℝ) :
    (twoDetunedGen J ħ ΔA ΔB)ᴴ = -(twoDetunedGen J ħ ΔA ΔB) :=
  skew_neg_I_smul_of_hermitian (1 / ħ) (twoDetunedH_conjTranspose J ΔA ΔB)

/-- The generator splits as the detuned exchange's plus the sector generator. -/
theorem twoDetunedGen_eq (J ħ ΔA ΔB : ℝ) :
    twoDetunedGen J ħ ΔA ΔB = detunedGen J ħ (ΔB - ΔA) + sectorGen ħ ΔA := by
  rw [twoDetunedGen, twoDetunedH_eq, smul_add, detunedGen, sectorGen, smul_smul]
  congr 2
  push_cast
  ring

/-- At `Δ_A = 0` the generator is the detuned exchange's. -/
theorem twoDetunedGen_zero_left (J ħ Δ : ℝ) : twoDetunedGen J ħ 0 Δ = detunedGen J ħ Δ := by
  rw [twoDetunedGen_eq, sub_zero, sectorGen]
  simp

theorem commute_sectorGen_detunedGen (J ħ ΔA Δ : ℝ) :
    Commute (sectorGen ħ ΔA) (detunedGen J ħ Δ) :=
  (commute_oneExc_detunedGen J ħ Δ).smul_left _

theorem commute_oneExc_twoDetunedGen (J ħ ΔA ΔB : ℝ) :
    Commute oneExc (twoDetunedGen J ħ ΔA ΔB) := by
  rw [twoDetunedGen_eq]
  exact (commute_oneExc_detunedGen J ħ _).add_right ((Commute.refl oneExc).smul_right _)

theorem continuous_twoDetunedGen (J ħ : ℝ) :
    Continuous fun x : ℝ × ℝ => twoDetunedGen J ħ x.1 x.2 := by
  unfold twoDetunedGen twoDetunedH
  fun_prop

/-! ### The flow -/

/-- ★ **The two-site detuned exchange as a field-structured flow**: the one edge `(A, B)` carrying
`−(i/ħ)(J X + Δ_A n_A + Δ_B n_B)`. -/
noncomputable def twoDetunedFlow (J ħ ΔA ΔB : ℝ) : FieldStructuredFlow 2 2 where
  edges := {(0, 1)}
  piece := fun _ => twoDetunedGen J ħ ΔA ΔB
  piece_supported := by
    intro e he
    rw [Finset.mem_singleton] at he
    subst he
    exact supportedOn_pair _
  gen_skew := by
    rw [Finset.sum_singleton]
    exact twoDetunedGen_skew J ħ ΔA ΔB

theorem twoDetunedFlow_val (J ħ ΔA ΔB t : ℝ) :
    ((twoDetunedFlow J ħ ΔA ΔB).flow t).val = exp (t • twoDetunedGen J ħ ΔA ΔB) := by
  simp only [FieldStructuredFlow.flow_val, twoDetunedFlow, Finset.sum_singleton]

theorem twoDetunedFlow_isom (J ħ ΔA ΔB t : ℝ) :
    (((twoDetunedFlow J ħ ΔA ΔB).flow t).val)ᴴ * ((twoDetunedFlow J ħ ΔA ΔB).flow t).val = 1 := by
  have h := ((twoDetunedFlow J ħ ΔA ΔB).flow t).property
  rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h

/-- The flow is continuous jointly in both detunings and the time. -/
theorem continuous_twoDetunedFlowVal_prod (J ħ : ℝ) :
    Continuous fun x : (ℝ × ℝ) × ℝ => ((twoDetunedFlow J ħ x.1.1 x.1.2).flow x.2).val := by
  simp only [twoDetunedFlow_val]
  have hexp : Continuous (exp : Matrix HopConfig HopConfig ℂ → Matrix HopConfig HopConfig ℂ) :=
    continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt
  exact hexp.comp (continuous_snd.smul ((continuous_twoDetunedGen J ħ).comp continuous_fst))

theorem continuous_twoDetunedFlow_prod (J ħ : ℝ) :
    Continuous fun x : (ℝ × ℝ) × ℝ => (twoDetunedFlow J ħ x.1.1 x.1.2).flow x.2 :=
  continuous_induced_rng.2 (continuous_twoDetunedFlowVal_prod J ħ)

/-- The Schrödinger equation of the two-site flow. -/
theorem hasDerivAt_twoDetunedFlowVal (J ħ ΔA ΔB t : ℝ) :
    HasDerivAt (fun t : ℝ => ((twoDetunedFlow J ħ ΔA ΔB).flow t).val)
      (twoDetunedGen J ħ ΔA ΔB * ((twoDetunedFlow J ħ ΔA ΔB).flow t).val) t := by
  simp only [twoDetunedFlow_val]
  exact hasDerivAt_exp_smul_const' (twoDetunedGen J ħ ΔA ΔB) t

/-! ### The sector phase -/

/-- The sector phase `e^{−i Δ_A t/ħ · P}`. -/
noncomputable def sectorPhase (ħ ΔA t : ℝ) : Matrix HopConfig HopConfig ℂ :=
  exp (t • sectorGen ħ ΔA)

/-- `e^{c P} = 1 + (e^c − 1) P`. -/
theorem sectorPhase_eq (ħ ΔA t : ℝ) :
    sectorPhase ħ ΔA t
      = 1 + (Complex.exp (((-(ΔA * t / ħ) : ℝ) : ℂ) * Complex.I) - 1) • oneExc := by
  rw [sectorPhase, sectorGen, matrix_real_smul, smul_smul,
    exp_smul_eq_cosh_sinh oneExc_mul_oneExc oneExc_mul_oneExc]
  have ha : ((t : ℝ) : ℂ) * -(Complex.I * ((ΔA / ħ : ℝ) : ℂ))
      = ((-(ΔA * t / ħ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ha, add_assoc, ← add_smul, sub_add_eq_add_sub, Complex.cosh_add_sinh]

/-- The sector phase is unitary. -/
theorem sectorPhase_unitary (ħ ΔA t : ℝ) : (sectorPhase ħ ΔA t)ᴴ * sectorPhase ħ ΔA t = 1 := by
  have hX : (t • sectorGen ħ ΔA)ᴴ = -(t • sectorGen ħ ΔA) := by
    rw [matrix_real_smul, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      sectorGen_skew, smul_neg]
  rw [sectorPhase, ← Matrix.exp_conjTranspose, hX,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl (t • sectorGen ħ ΔA))),
    neg_add_cancel, exp_zero]

/-- The sector phase commutes with everything `P` commutes with. -/
theorem sectorPhase_commute (ħ ΔA t : ℝ) {A : Matrix HopConfig HopConfig ℂ}
    (hA : oneExc * A = A * oneExc) : sectorPhase ħ ΔA t * A = A * sectorPhase ħ ΔA t := by
  rw [sectorPhase_eq, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hA]

/-- The sector phase is the scalar `e^{−iΔ_A t/ħ}` on the column of `A` of anything commuting
with `P`. -/
theorem sectorPhase_mul_apply_excA (ħ ΔA t : ℝ) {M : Matrix HopConfig HopConfig ℂ}
    (hM : oneExc * M = M * oneExc) (c : HopConfig) :
    (sectorPhase ħ ΔA t * M) c excA
      = Complex.exp (((-(ΔA * t / ħ) : ℝ) : ℂ) * Complex.I) * M c excA := by
  rw [sectorPhase_eq, add_mul, one_mul, smul_mul_assoc, hM, Matrix.add_apply, Matrix.smul_apply,
    mul_oneExc_apply_excA, smul_eq_mul]
  ring

/-- The sector phase is the identity on the vacuum column. -/
theorem sectorPhase_mul_apply_vacC (ħ ΔA t : ℝ) {M : Matrix HopConfig HopConfig ℂ}
    (hM : oneExc * M = M * oneExc) (c : HopConfig) :
    (sectorPhase ħ ΔA t * M) c vacC = M c vacC := by
  rw [sectorPhase_eq, add_mul, one_mul, smul_mul_assoc, hM, Matrix.add_apply, Matrix.smul_apply,
    mul_oneExc_apply_vacC, smul_zero, add_zero]

/-- ★★ **The two-site flow is the sector phase times the detuned exchange in the difference.** -/
theorem twoDetunedFlow_val_eq (J ħ ΔA ΔB t : ℝ) :
    ((twoDetunedFlow J ħ ΔA ΔB).flow t).val
      = sectorPhase ħ ΔA t * ((detunedFlow J ħ (ΔB - ΔA)).flow t).val := by
  rw [twoDetunedFlow_val, detunedFlow_val, twoDetunedGen_eq, smul_add, add_comm, sectorPhase,
    Matrix.exp_add_of_commute _ _
      (((commute_sectorGen_detunedGen J ħ ΔA (ΔB - ΔA)).smul_left t).smul_right t)]

/-! ### Observables and rays agree with the detuned exchange -/

/-- ★★ **Every observable commuting with `P` reads the same along the two-site flow and the detuned
exchange in the difference, at every arena point.** -/
theorem arenaObs_twoDetunedFlow (J ħ ΔA ΔB : ℝ) {A : Matrix HopConfig HopConfig ℂ}
    (hA : oneExc * A = A * oneExc) (p : FieldArena 2 2) (t : ℝ) :
    arenaObs A ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t p)
      = arenaObs A ((detunedFlow J ħ (ΔB - ΔA)).arenaFlow t p) := by
  have hD : (sectorPhase ħ ΔA t)ᴴ * A * sectorPhase ħ ΔA t = A := by
    rw [Matrix.mul_assoc, ← sectorPhase_commute ħ ΔA t hA, ← Matrix.mul_assoc,
      sectorPhase_unitary, Matrix.one_mul]
  have key : ∀ D V : Matrix HopConfig HopConfig ℂ, Dᴴ * A * D = A →
      Vᴴ * Dᴴ * A * (D * V) = Vᴴ * A * V := by
    intro D V h
    rw [show Vᴴ * Dᴴ * A * (D * V) = Vᴴ * (Dᴴ * A * D) * V by simp only [Matrix.mul_assoc], h]
  rw [FieldStructuredFlow.arenaFlow, FieldStructuredFlow.arenaFlow, arenaObs_kick_conj,
    arenaObs_kick_conj, twoDetunedFlow_val_eq, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, conjTranspose_mul, key _ _ hD]

/-- The occupancy of `B` along the two-site flow is the detuned exchange's history. -/
theorem occB_twoDetunedFlow (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (t : ℝ) :
    arenaObs occB ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t p) = occHist J ħ (ΔB - ΔA) p t :=
  arenaObs_twoDetunedFlow J ħ ΔA ΔB (by rw [oneExc_mul_occB, occB_mul_oneExc]) p t

theorem occA_twoDetunedFlow (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (t : ℝ) :
    arenaObs occA ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t p)
      = arenaObs occA ((detunedFlow J ħ (ΔB - ΔA)).arenaFlow t p) :=
  arenaObs_twoDetunedFlow J ħ ΔA ΔB (by rw [oneExc_mul_occA, occA_mul_oneExc]) p t

/-- The one-excitation weight is the sum of the two occupancies. -/
theorem arenaObs_oneExc_eq (p : FieldArena 2 2) :
    arenaObs oneExc p = arenaObs occA p + arenaObs occB p := by
  rw [oneExc_eq_occA_add_occB, arenaObs_add]

/-- **The one-excitation sector is conserved** along the two-site flow. -/
theorem arenaObs_oneExc_twoDetunedFlow (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (t : ℝ) :
    arenaObs oneExc ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t p) = arenaObs oneExc p := by
  have hcomm : Commute oneExc ((twoDetunedFlow J ħ ΔA ΔB).flow t).val := by
    rw [twoDetunedFlow_val]
    exact ((commute_oneExc_twoDetunedGen J ħ ΔA ΔB).smul_right t).exp_right
  rw [FieldStructuredFlow.arenaFlow, arenaObs_kick_conj, Matrix.star_eq_conjTranspose,
    Matrix.mul_assoc, hcomm.eq, ← Matrix.mul_assoc, twoDetunedFlow_isom, Matrix.one_mul]

/-- ★★ **On the ray of message `1` the two-site flow is the detuned exchange in the difference.** -/
theorem twoDetunedFlow_arenaFlow_msgPoint_one (J ħ ΔA ΔB t : ℝ) :
    (twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 1)
      = (detunedFlow J ħ (ΔB - ΔA)).arenaFlow t (msgPoint 1) := by
  rw [FieldStructuredFlow.arenaFlow, FieldStructuredFlow.arenaFlow, msgPoint_one, arenaKick_mk,
    arenaKick_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    ⟨Complex.exp (((-(ΔA * t / ħ) : ℝ) : ℂ) * Complex.I), ?_⟩
  ext c
  rw [PiLp.smul_apply, toEuclideanLin_coord, toEuclideanLin_coord, twoDetunedFlow_val_eq]
  have hfun : (fun j => basisVec excA j) = Pi.single excA (1 : ℂ) := funext fun j => rfl
  rw [hfun, mulVec_single_one, mulVec_single_one, Matrix.col_apply, Matrix.col_apply,
    sectorPhase_mul_apply_excA ħ ΔA t (oneExc_commute_detunedFlowVal J ħ (ΔB - ΔA) t),
    smul_eq_mul]

/-- The vacuum column of the two-site flow is the vacuum. -/
theorem twoDetunedFlow_apply_vacC {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) (c : HopConfig) :
    ((twoDetunedFlow J ħ ΔA ΔB).flow t).val c vacC = if c = vacC then 1 else 0 := by
  rw [twoDetunedFlow_val_eq,
    sectorPhase_mul_apply_vacC ħ ΔA t (oneExc_commute_detunedFlowVal J ħ (ΔB - ΔA) t),
    detunedFlow_apply_vacC hJ]

/-- **The vacuum is fixed**: message `0` never moves. -/
theorem twoDetunedFlow_msgPoint_zero {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) :
    (twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 0) = msgPoint 0 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_zero, arenaKick_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul]
  ext c
  rw [toEuclideanLin_coord]
  have hfun : (fun j => basisVec vacC j) = Pi.single vacC (1 : ℂ) := funext fun j => rfl
  rw [hfun, mulVec_single_one, basisVec_apply]
  simp only [Matrix.col_apply, twoDetunedFlow_apply_vacC hJ, Pi.single_apply]

/-! ### The readouts of the two messages -/

theorem arenaObs_occA_msgPoint_one : arenaObs occA (msgPoint 1) = 1 := by
  rw [msgPoint_one, occA, arenaObs_single_mk, basisVec_apply, Pi.single_eq_same, norm_one,
    norm_basisVec]
  norm_num

theorem arenaObs_occB_msgPoint_one : arenaObs occB (msgPoint 1) = 0 := by
  rw [msgPoint_one, occB, arenaObs_single_mk, basisVec_apply,
    Pi.single_eq_of_ne excA_ne_excB.symm, norm_zero]
  simp

theorem arenaObs_occA_msgPoint_zero : arenaObs occA (msgPoint 0) = 0 := by
  rw [msgPoint_zero, occA, arenaObs_single_mk, basisVec_apply,
    Pi.single_eq_of_ne vacC_ne_excA.symm, norm_zero]
  simp

theorem arenaObs_occB_msgPoint_zero : arenaObs occB (msgPoint 0) = 0 := by
  rw [msgPoint_zero, occB, arenaObs_single_mk, basisVec_apply,
    Pi.single_eq_of_ne vacC_ne_excB.symm, norm_zero]
  simp

/-- ★★ **The receiver's occupancy for message `1`**: `(J/Ω')² sin²(Ω't/ħ)` with
`Ω' = √(J² + (Δ_B − Δ_A)²/4)`. -/
theorem twoDetuned_readout_B_one {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) :
    arenaObs occB ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 1))
      = (J / rabiFreq J (ΔB - ΔA)) ^ 2 * Real.sin (rabiAngle J ħ (ΔB - ΔA) t) ^ 2 := by
  rw [occB_twoDetunedFlow, occHist_msgPoint_one hJ]

/-- ★★ **The sender's occupancy for message `1`**: `1 − (J/Ω')² sin²(Ω't/ħ)`. -/
theorem twoDetuned_readout_A_one {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) :
    arenaObs occA ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 1))
      = 1 - (J / rabiFreq J (ΔB - ΔA)) ^ 2 * Real.sin (rabiAngle J ħ (ΔB - ΔA) t) ^ 2 := by
  have h := arenaObs_oneExc_twoDetunedFlow J ħ ΔA ΔB (msgPoint 1) t
  rw [arenaObs_oneExc_eq, arenaObs_oneExc_eq, arenaObs_occA_msgPoint_one,
    arenaObs_occB_msgPoint_one, twoDetuned_readout_B_one hJ] at h
  linarith

theorem twoDetuned_readout_B_zero {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) :
    arenaObs occB ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 0)) = 0 := by
  rw [twoDetunedFlow_msgPoint_zero hJ, arenaObs_occB_msgPoint_zero]

theorem twoDetuned_readout_A_zero {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) :
    arenaObs occA ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 0)) = 0 := by
  rw [twoDetunedFlow_msgPoint_zero hJ, arenaObs_occA_msgPoint_zero]

/-! ### The detuned round trip: the carrier returns to `A` -/

/-- The detuned round trip `πħ/Ω`. -/
noncomputable def detunedRoundTrip (J ħ Δ : ℝ) : ℝ := Real.pi * ħ / rabiFreq J Δ

theorem detunedRoundTrip_eq (J ħ Δ : ℝ) :
    detunedRoundTrip J ħ Δ = 2 * detunedHopTime J ħ Δ := by
  unfold detunedRoundTrip detunedHopTime
  ring

theorem detunedRoundTrip_pos {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    0 < detunedRoundTrip J ħ Δ := by
  unfold detunedRoundTrip
  have := rabiFreq_pos hJ Δ
  positivity

/-- At zero detuning the detuned round trip is the round trip of #183. -/
theorem detunedRoundTrip_zero {J : ℝ} (hJ : 0 ≤ J) (ħ : ℝ) :
    detunedRoundTrip J ħ 0 = roundTrip J ħ := by
  unfold detunedRoundTrip roundTrip hopTime
  rw [rabiFreq_zero hJ]
  ring

theorem rabiAngle_detunedRoundTrip {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    rabiAngle J ħ Δ (detunedRoundTrip J ħ Δ) = Real.pi := by
  have hΩ := (rabiFreq_pos hJ Δ).ne'
  unfold rabiAngle rabiRate detunedRoundTrip
  field_simp

/-- At the detuned round trip the detuned flow acts on `e_A` as the scalar `−e^{−iΔ πħ/(2Ωħ)}`. -/
theorem toEuclideanLin_detunedFlow_roundTrip {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    Matrix.toEuclideanLin ((detunedFlow J ħ Δ).flow (detunedRoundTrip J ħ Δ)).val
        (basisVec excA)
      = (-(Complex.exp (((-dynPhase ħ Δ (detunedRoundTrip J ħ Δ) : ℝ) : ℂ) * Complex.I)))
          • basisVec excA := by
  ext c
  rw [toEuclideanLin_coord, PiLp.smul_apply]
  have hfun : (fun j => basisVec excA j) = Pi.single excA (1 : ℂ) := funext fun j => rfl
  rw [hfun, mulVec_single_one, Matrix.col_apply, detunedFlow_val_eq hJ,
    rabiAngle_detunedRoundTrip hJ hħ, Real.sin_pi, Real.cos_pi, basisVec_apply]
  simp only [Complex.ofReal_zero, mul_zero, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hc : c = excA
  · subst hc
    rw [oneExc_apply_excA_excA, Pi.single_eq_same, ite_eq_left rfl]
    push_cast
    ring
  · rw [oneExc_apply_ne_excA hc, Pi.single_eq_of_ne hc, ite_eq_right hc]
    ring

/-- ★★★ **The return**: at the detuned round trip the carrier is back at `A`, as a ray, exactly. -/
theorem detunedFlow_return {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    (detunedFlow J ħ Δ).arenaFlow (detunedRoundTrip J ħ Δ) (msgPoint 1) = msgPoint 1 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_one, arenaKick_mk]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    ⟨_, (toEuclideanLin_detunedFlow_roundTrip hJ hħ Δ).symm⟩

/-- ★★★ **The return of the two-site flow**: at the detuned round trip in the difference, the
carrier of message `1` is back at `A` as a ray. -/
theorem twoDetuned_return {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (ΔA ΔB : ℝ) :
    (twoDetunedFlow J ħ ΔA ΔB).arenaFlow (detunedRoundTrip J ħ (ΔB - ΔA)) (msgPoint 1)
      = msgPoint 1 := by
  rw [twoDetunedFlow_arenaFlow_msgPoint_one, detunedFlow_return hJ hħ]

theorem twoDetuned_return_occA {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (ΔA ΔB : ℝ) :
    arenaObs occA ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow (detunedRoundTrip J ħ (ΔB - ΔA))
      (msgPoint 1)) = 1 := by
  rw [twoDetuned_return hJ hħ, arenaObs_occA_msgPoint_one]

theorem twoDetuned_return_occB {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (ΔA ΔB : ℝ) :
    arenaObs occB ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow (detunedRoundTrip J ħ (ΔB - ΔA))
      (msgPoint 1)) = 0 := by
  rw [twoDetuned_return hJ hħ, arenaObs_occB_msgPoint_one]

/-- The return repeats: every multiple of the detuned round trip returns the carrier. -/
theorem twoDetuned_return_nsmul {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (ΔA ΔB : ℝ) (n : ℕ) :
    (twoDetunedFlow J ħ ΔA ΔB).arenaFlow (n * detunedRoundTrip J ħ (ΔB - ΔA)) (msgPoint 1)
      = msgPoint 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, FieldStructuredFlow.arenaFlow_zero']
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, FieldStructuredFlow.arenaFlow_add,
      twoDetuned_return hJ hħ, ih]

/-! ### The occupancy history of `A` -/

/-- **The sender's occupancy history** along the two-site flow from `p`. -/
noncomputable def occHistA (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (s : ℝ) : ℝ :=
  arenaObs occA ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow s p)

/-- The history of `A` is the conserved sector weight minus the history of `B`. -/
theorem occHistA_eq (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (s : ℝ) :
    occHistA J ħ ΔA ΔB p s = arenaObs oneExc p - occHist J ħ (ΔB - ΔA) p s := by
  have h := arenaObs_oneExc_twoDetunedFlow J ħ ΔA ΔB p s
  rw [arenaObs_oneExc_eq ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow s p), occB_twoDetunedFlow] at h
  rw [occHistA]
  linarith

theorem occHistA_nonneg (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (s : ℝ) :
    0 ≤ occHistA J ħ ΔA ΔB p s := by
  rw [occHistA, occA, arenaObs_single_eq_momentMap]
  exact momentMap_nonneg _ _

theorem occHistA_le_one (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (s : ℝ) :
    occHistA J ħ ΔA ΔB p s ≤ 1 := by
  rw [occHistA, occA, arenaObs_single_eq_momentMap]
  have h := momentMap_sum_eq_one ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow s p)
  rw [← h]
  exact Finset.single_le_sum (fun c _ => momentMap_nonneg _ c) (Finset.mem_univ excA)

/-- **The history of `A` is continuous jointly in the ray, both detunings and the time.** -/
theorem continuous_occHistA_prod (J ħ : ℝ) :
    Continuous (Function.uncurry fun (x : FieldArena 2 2 × (ℝ × ℝ)) (s : ℝ) =>
      occHistA J ħ x.2.1 x.2.2 x.1 s) := by
  unfold Function.uncurry occHistA FieldStructuredFlow.arenaFlow
  have hU : Continuous fun y : (FieldArena 2 2 × (ℝ × ℝ)) × ℝ =>
      (twoDetunedFlow J ħ y.1.2.1 y.1.2.2).flow y.2 :=
    (continuous_twoDetunedFlow_prod J ħ).comp₂ (continuous_snd.comp continuous_fst) continuous_snd
  exact continuous_const.arenaObs (hU.arenaKick (continuous_fst.comp continuous_fst))

theorem continuous_occHistA (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) :
    Continuous fun s => occHistA J ħ ΔA ΔB p s := by
  simp_rw [occHistA_eq]
  exact continuous_const.sub (continuous_occHist J ħ _ p)

/-- **The accumulated occupancy of `A`** `∫₀ᵗ n_A(p(s)) ds`. -/
noncomputable def occAccumA (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, occHistA J ħ ΔA ΔB p s

/-- The accumulated occupancy of `A` is `t × (sector weight) − (accumulated occupancy of `B`)`. -/
theorem occAccumA_eq (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (t : ℝ) :
    occAccumA J ħ ΔA ΔB p t = t * arenaObs oneExc p - occAccum J ħ (ΔB - ΔA) p t := by
  unfold occAccumA occAccum
  simp_rw [occHistA_eq]
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 t)
    ((continuous_occHist J ħ _ p).intervalIntegrable 0 t), intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]

theorem occAccumA_zero (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) : occAccumA J ħ ΔA ΔB p 0 = 0 :=
  intervalIntegral.integral_same

theorem hasDerivAt_occAccumA (J ħ ΔA ΔB : ℝ) (p : FieldArena 2 2) (t : ℝ) :
    HasDerivAt (fun t => occAccumA J ħ ΔA ΔB p t) (occHistA J ħ ΔA ΔB p t) t := by
  unfold occAccumA
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_occHistA J ħ ΔA ΔB p).intervalIntegrable 0 t)
    ((continuous_occHistA J ħ ΔA ΔB p).stronglyMeasurableAtFilter volume _)
    (continuous_occHistA J ħ ΔA ΔB p).continuousAt

/-- **The accumulated occupancy of `A` is continuous jointly in the ray and both detunings.** -/
theorem continuous_occAccumA_prod (J ħ t : ℝ) :
    Continuous fun x : FieldArena 2 2 × (ℝ × ℝ) => occAccumA J ħ x.2.1 x.2.2 x.1 t := by
  unfold occAccumA
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x : FieldArena 2 2 × (ℝ × ℝ) => fun s => occHistA J ħ x.2.1 x.2.2 x.1 s)
    (continuous_occHistA_prod J ħ) 0 t

/-- The history of `A` for message `1`: `1 − (J/Ω')² sin²(Ω's/ħ)`. -/
theorem occHistA_msgPoint_one {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB s : ℝ) :
    occHistA J ħ ΔA ΔB (msgPoint 1) s
      = 1 - (J / rabiFreq J (ΔB - ΔA)) ^ 2 * Real.sin (rabiAngle J ħ (ΔB - ΔA) s) ^ 2 :=
  twoDetuned_readout_A_one hJ ħ ΔA ΔB s

theorem occHistA_msgPoint_zero {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB s : ℝ) :
    occHistA J ħ ΔA ΔB (msgPoint 0) s = 0 :=
  twoDetuned_readout_A_zero hJ ħ ΔA ΔB s

/-- The accumulated occupancy of `A` for message `1`: `t − (accumulated occupancy of `B`)`. -/
theorem occAccumA_msgPoint_one (J ħ ΔA ΔB t : ℝ) :
    occAccumA J ħ ΔA ΔB (msgPoint 1) t = t - occAccum J ħ (ΔB - ΔA) (msgPoint 1) t := by
  rw [occAccumA_eq, arenaObs_oneExc_eq, arenaObs_occA_msgPoint_one, arenaObs_occB_msgPoint_one,
    add_zero, mul_one]

theorem occAccumA_msgPoint_zero {J : ℝ} (hJ : 0 < J) (ħ ΔA ΔB t : ℝ) :
    occAccumA J ħ ΔA ΔB (msgPoint 0) t = 0 := by
  unfold occAccumA
  simp [occHistA_msgPoint_zero hJ]

/-- ★ **The two-site exchange with both sites detuned**, in one statement: the flow is the detuned
exchange in the difference up to the sector phase; the two messages' occupancies at both sites; the
vacuum fixed; and the return of the carrier to `A` at the detuned round trip. -/
theorem two_site_detuned {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (ΔA ΔB : ℝ) :
    (∀ t, ((twoDetunedFlow J ħ ΔA ΔB).flow t).val
        = sectorPhase ħ ΔA t * ((detunedFlow J ħ (ΔB - ΔA)).flow t).val)
    ∧ (∀ t, arenaObs occB ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 1))
        = (J / rabiFreq J (ΔB - ΔA)) ^ 2 * Real.sin (rabiAngle J ħ (ΔB - ΔA) t) ^ 2)
    ∧ (∀ t, arenaObs occA ((twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 1))
        = 1 - (J / rabiFreq J (ΔB - ΔA)) ^ 2 * Real.sin (rabiAngle J ħ (ΔB - ΔA) t) ^ 2)
    ∧ (∀ t, (twoDetunedFlow J ħ ΔA ΔB).arenaFlow t (msgPoint 0) = msgPoint 0)
    ∧ 0 < detunedRoundTrip J ħ (ΔB - ΔA)
    ∧ (twoDetunedFlow J ħ ΔA ΔB).arenaFlow (detunedRoundTrip J ħ (ΔB - ΔA)) (msgPoint 1)
        = msgPoint 1 :=
  ⟨fun t => twoDetunedFlow_val_eq J ħ ΔA ΔB t, fun t => twoDetuned_readout_B_one hJ ħ ΔA ΔB t,
    fun t => twoDetuned_readout_A_one hJ ħ ΔA ΔB t, fun t => twoDetunedFlow_msgPoint_zero hJ ħ ΔA ΔB t,
    detunedRoundTrip_pos hJ hħ _, twoDetuned_return hJ hħ ΔA ΔB⟩

end CSD.CV

end
