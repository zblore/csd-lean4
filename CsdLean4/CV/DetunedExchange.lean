/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.SignalExchange
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The detuned exchange: the hop with a state-dependent energy at the receiver

**Category:** 3-Local (CV; the carrier side of BACKLOG #194, the first internally activated write).

The signal exchange of `SignalExchange.lean` is the hop `H = J X`. When the receiver's site carries
an energy `Δ` — in #194 the back-reaction of a pointer coupled to the occupancy of `B` — the carrier's
Hamiltonian becomes

  `H(Δ) = J X + Δ n_B = (Δ/2) P + Ω Y`,   `Ω = √(J² + Δ²/4)`,   `Y = (J X + (Δ/2) Z)/Ω`,

with `P` the one-excitation projector and `Z = n_B − n_A`. The two pieces commute, `Y² = P`, and the
flow is the product of two closed-form exponentials (`ExpUnique.lean`):

  `U(t) = 1 + (e^{−iΔt/2ħ} cos(Ωt/ħ) − 1) P − i e^{−iΔt/2ħ} sin(Ωt/ħ) Y`.

The receiver's occupancy for message `1` is the detuned Rabi formula `(J/Ω)² sin²(Ωt/ħ)`: the
transfer is no longer complete, and the loss `1 − (J/Ω)² = (Δ/2)²/Ω²` is the explicit price of the
back-reaction. The vacuum is fixed, so message `0` produces no occupancy at all.

* `occA`, `zOp`, `rabiFreq`, `rabiY`, `detunedH`, `detunedGen`, ★ `detunedFlow J ħ Δ :
  FieldStructuredFlow 2 2` — **the detuned exchange is a field-structured flow on the same edge**;
  `detunedGen_zero` — at `Δ = 0` it is the hop of #183;
* ★★ `detunedFlow_val_eq` — **the flow in closed form**, by `exp_add_of_commute` and two uses of
  `exp_smul_eq_cosh_sinh`; `detunedFlow_msgPoint_zero` — the vacuum is fixed;
* ★★ `detuned_readout_one` — **the receiver's occupancy for message `1` is `(J/Ω)² sin²(Ωt/ħ)`**;
  `detuned_readout_zero`; ★ `detuned_readout_one_le`, `detuned_readout_one_peak`,
  `detuned_readout_one_lt_one`, `one_sub_div_rabiFreq_sq` — **the detuning loss**, attained at the
  detuned hop time and strictly positive whenever `Δ ≠ 0`;
* ★ `arenaObs_detunedH_arenaFlow` — **the carrier's energy `⟨H(Δ)⟩` is conserved along the flow**;
* `occHist`, `occAccum` — **the receiver's occupancy history and its time integral**, for every arena
  point; ★ `occAccum_add` — the integral obeys the flow's group law; ★ `hasDerivAt_occAccum` — its
  derivative is the occupancy; ★★ `occAccum_msgPoint_one` — **the closed form for message `1`**,
  `(J/Ω)² (Ωt/ħ − sin cos)/(2Ω/ħ)`; `occAccum_msgPoint_zero = 0`;
* `continuous_arenaDM`, `continuous_arenaObs_prod`, ★ `continuous_arenaKick_prod` — **the arena
  density, the observables and the unitary kick are continuous, jointly in all arguments**, by
  descent through the open quotient map `mk'`; `continuous_occHist_prod`, `continuous_occAccum_prod`
  — the history and its integral are continuous jointly in the ray and the detuning, which is what
  #194's skew product needs.

## Honest scope

* Nothing here is a record. The pointer that produces `Δ` and reads the occupancy is
  `RecordLayer/ActivatedWrite.lean`; this file is its carrier.
* `Δ` is a real parameter. In #194 it is a function of a conserved torus angle, so the flow at fixed
  angle is exactly this one; no time dependence appears anywhere.
* `J > 0` is assumed where the closed form divides by `Ω`; `ħ` enters only through the angles.

References: `specs/BACKLOG.md` #194, #183, #195; `CV/SignalExchange.lean` (`hopX`, `oneExc`,
`occB`, `msgPoint`, `receiver_readout_one`), `CV/FieldStructuredFlow.lean`, `CV/ArenaBridge.lean`
(`arenaObs_kick_conj`, `arenaDM_mk`), `Mathlib/Analysis/Normed/Algebra/ExpUnique.lean`,
`Mathlib/LinearAlgebra/Projectivization/Topology.lean` (`isOpenQuotientMap_mk'`).
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Projectivization Matrix.UnitaryGroup
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

/-! ### Continuity on the arena, jointly in all arguments -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The arena density is continuous**, by descent through the quotient map `mk'`: `arenaDM` is
defined through `Projectivization.rep`, which is not continuous, but `arenaDM (mk v) = dmVec v` and
`dmVec` is continuous on the nonzero vectors. -/
theorem continuous_arenaDM : Continuous (arenaDM : GenArena ι → Matrix ι ι ℂ) := by
  rw [Projectivization.continuous_iff]
  have hcomp : (arenaDM ∘ Projectivization.mk' ℂ)
      = fun v : {v : EuclideanSpace ℂ ι // v ≠ 0} => dmVec (v : EuclideanSpace ℂ ι) := by
    funext v
    exact arenaDM_mk v.2
  rw [hcomp]
  have hunit : Continuous fun v : {v : EuclideanSpace ℂ ι // v ≠ 0} =>
      unitVec (v : EuclideanSpace ℂ ι) := by
    refine continuous_pi fun i => ?_
    exact ((Complex.continuous_ofReal.comp continuous_subtype_val.norm).inv₀ fun v =>
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr v.2)).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp continuous_subtype_val)
  exact hunit.matrix_vecMulVec hunit.star

omit [DecidableEq ι] in
/-- Arena observables are continuous jointly in the ray and the operator. -/
theorem continuous_arenaObs_prod :
    Continuous fun x : GenArena ι × Matrix ι ι ℂ => arenaObs x.2 x.1 := by
  unfold arenaObs
  exact RCLike.continuous_re.comp
    (((continuous_arenaDM.comp continuous_fst).matrix_mul continuous_snd).matrix_trace)

omit [DecidableEq ι] in
theorem continuous_arenaObs (A : Matrix ι ι ℂ) : Continuous fun p : GenArena ι => arenaObs A p := by
  unfold arenaObs
  exact RCLike.continuous_re.comp ((continuous_arenaDM.matrix_mul continuous_const).matrix_trace)

omit [DecidableEq ι] in
/-- An arena observable of a continuous operator family at a continuous family of rays is
continuous. Stated in applied form so that it composes without unfolding `arenaObs`. -/
theorem _root_.Continuous.arenaObs {X : Type*} [TopologicalSpace X] {M : X → Matrix ι ι ℂ}
    {p : X → GenArena ι} (hM : Continuous M) (hp : Continuous p) :
    Continuous fun x => CSD.CV.arenaObs (M x) (p x) := by
  unfold CSD.CV.arenaObs
  exact RCLike.continuous_re.comp (((continuous_arenaDM.comp hp).matrix_mul hM).matrix_trace)

/-- ★ **The unitary kick is continuous jointly in the unitary and the ray**: `id × mk'` is an open
quotient map, and the lift `(U, v) ↦ mk (U v)` is continuous. -/
theorem continuous_arenaKick_prod :
    Continuous fun x : Matrix.unitaryGroup ι ℂ × GenArena ι => arenaKick x.1 x.2 := by
  have hq : IsOpenQuotientMap (Prod.map (id : Matrix.unitaryGroup ι ℂ → Matrix.unitaryGroup ι ℂ)
      (Projectivization.mk' ℂ (V := EuclideanSpace ℂ ι))) :=
    IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'
  rw [hq.isQuotientMap.continuous_iff]
  have hlin : Continuous fun x : Matrix.unitaryGroup ι ℂ × {v : EuclideanSpace ℂ ι // v ≠ 0} =>
      Matrix.toEuclideanLin x.1.val (x.2 : EuclideanSpace ℂ ι) := by
    refine continuous_induced_rng.2 ?_
    have h : (WithLp.ofLp ∘ fun x : Matrix.unitaryGroup ι ℂ × {v : EuclideanSpace ℂ ι // v ≠ 0} =>
        Matrix.toEuclideanLin x.1.val (x.2 : EuclideanSpace ℂ ι))
        = fun x => x.1.val *ᵥ fun j => (x.2 : EuclideanSpace ℂ ι) j := by
      funext x i
      exact toEuclideanLin_coord _ _ i
    rw [h]
    exact (continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp (continuous_subtype_val.comp continuous_snd))
  refine Continuous.congr (f := fun x : Matrix.unitaryGroup ι ℂ × {v : EuclideanSpace ℂ ι // v ≠ 0} =>
    arenaKick x.1 (Projectivization.mk ℂ x.2.1 x.2.2)) ?_ (fun x => rfl)
  simp_rw [arenaKick_mk]
  exact Projectivization.continuous_mk'.comp (hlin.subtype_mk _)

/-- The kick of a continuous family of unitaries at a continuous family of rays is continuous. -/
theorem _root_.Continuous.arenaKick {X : Type*} [TopologicalSpace X]
    {U : X → Matrix.unitaryGroup ι ℂ} {p : X → GenArena ι} (hU : Continuous U)
    (hp : Continuous p) : Continuous fun x => arenaKick (U x) (p x) :=
  continuous_arenaKick_prod.comp₂ hU hp

/-- The kick is the unitary action (general index type). -/
theorem arenaKick_eq_smul' (U : Matrix.unitaryGroup ι ℂ) (p : GenArena ι) :
    arenaKick U p = U • p := by
  conv_rhs => rw [← p.mk_rep]
  rw [smul_mk_eq_mk_toEuclideanLin]
  rfl

/-- Every unitary kick preserves the Fubini–Study measure at every reference point. -/
theorem arenaKick_measurePreserving (U : Matrix.unitaryGroup ι ℂ) (p₀ : GenArena ι) :
    MeasurePreserving (arenaKick U) (fsMeasure p₀) (fsMeasure p₀) := by
  have h : arenaKick U = fun p : GenArena ι => U • p := funext fun p => arenaKick_eq_smul' U p
  rw [h]
  exact ⟨(continuous_const_smul U).measurable, fsMeasure_smul_invariant U p₀⟩

omit [DecidableEq ι] in
theorem arenaObs_add (A B : Matrix ι ι ℂ) (p : GenArena ι) :
    arenaObs (A + B) p = arenaObs A p + arenaObs B p := by
  rw [arenaObs, arenaObs, arenaObs, Matrix.mul_add, Matrix.trace_add, map_add]

omit [DecidableEq ι] in
theorem arenaObs_real_smul (r : ℝ) (A : Matrix ι ι ℂ) (p : GenArena ι) :
    arenaObs ((r : ℂ) • A) p = r * arenaObs A p := by
  rw [arenaObs, arenaObs, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RCLike.re_to_complex,
    RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- The expectation of a basis projector at a ray is its moment coordinate. -/
theorem arenaObs_single_eq_momentMap (j : ι) (p : GenArena ι) :
    arenaObs (single j j (1 : ℂ)) p = momentMap p j := by
  conv_lhs => rw [← p.mk_rep]
  rw [arenaObs_single_mk]
  rfl

end Generic

/-! ### Generic facts about field-structured flows -/

theorem _root_.CSD.CV.FieldStructuredFlow.flow_zero {K N : ℕ} (F : FieldStructuredFlow K N) :
    F.flow 0 = 1 := by
  apply Subtype.ext
  rw [FieldStructuredFlow.flow_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem _root_.CSD.CV.FieldStructuredFlow.arenaFlow_zero' {K N : ℕ} (F : FieldStructuredFlow K N)
    (p : FieldArena K N) : F.arenaFlow 0 p = p := by
  rw [FieldStructuredFlow.arenaFlow, FieldStructuredFlow.flow_zero, arenaKick_eq_smul', one_smul]

theorem _root_.CSD.CV.FieldStructuredFlow.arenaFlow_measurePreserving {K N : ℕ}
    (F : FieldStructuredFlow K N) (t : ℝ) (p₀ : FieldArena K N) :
    MeasurePreserving (F.arenaFlow t) (fsMeasure p₀) (fsMeasure p₀) :=
  arenaKick_measurePreserving (F.flow t) p₀

/-! ### The occupancy of `A`, the imbalance `Z`, and their algebra -/

/-- The occupancy of `A`. -/
noncomputable def occA : Matrix HopConfig HopConfig ℂ := single excA excA 1

/-- The imbalance `Z = n_B − n_A`. -/
noncomputable def zOp : Matrix HopConfig HopConfig ℂ := occB - occA

theorem oneExc_eq_occA_add_occB : oneExc = occA + occB := rfl

theorem occB_conjTranspose : occBᴴ = occB := by
  rw [occB, single_conjTranspose, star_one]

theorem occA_conjTranspose : occAᴴ = occA := by
  rw [occA, single_conjTranspose, star_one]

theorem zOp_conjTranspose : zOpᴴ = zOp := by
  rw [zOp, conjTranspose_sub, occB_conjTranspose, occA_conjTranspose]

/-- Two matrix units whose inner indices differ multiply to zero. -/
theorem single_mul_single_hop (i : HopConfig) {j k l : HopConfig} (h : j ≠ k) :
    single i j (1 : ℂ) * single k l (1 : ℂ) = 0 :=
  single_mul_single_of_ne 1 i j k h 1

theorem zOp_mul_zOp : zOp * zOp = oneExc := by
  simp only [zOp, occA, occB, oneExc, sub_mul, mul_sub, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one,
    sub_zero, zero_sub, sub_neg_eq_add]
  exact add_comm _ _

theorem hopX_mul_zOp : hopX * zOp = single excA excB 1 - single excB excA 1 := by
  simp only [hopX, zOp, occA, occB, add_mul, mul_sub, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one]
  abel

theorem zOp_mul_hopX : zOp * hopX = single excB excA 1 - single excA excB 1 := by
  simp only [hopX, zOp, occA, occB, sub_mul, mul_add, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one,
    sub_zero, zero_sub]
  abel

theorem oneExc_mul_oneExc : oneExc * oneExc = oneExc := by
  simp only [oneExc, add_mul, mul_add, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one,
    zero_add, add_zero]

theorem oneExc_mul_hopX : oneExc * hopX = hopX := by
  simp only [oneExc, hopX, add_mul, mul_add, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one,
    zero_add, add_zero]

theorem oneExc_mul_zOp : oneExc * zOp = zOp := by
  simp only [oneExc, zOp, occA, occB, add_mul, mul_sub, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one]
  abel

theorem zOp_mul_oneExc : zOp * oneExc = zOp := by
  simp only [oneExc, zOp, occA, occB, sub_mul, mul_add, single_mul_single_same,
    single_mul_single_hop _ excA_ne_excB, single_mul_single_hop _ excA_ne_excB.symm, mul_one,
    zero_sub]
  abel

/-! ### The Rabi frequency and the rescaled traceless part -/

/-- The Rabi energy of the detuned hop: `Ω = √(J² + (Δ/2)²)`. -/
noncomputable def rabiFreq (J Δ : ℝ) : ℝ := Real.sqrt (J ^ 2 + (Δ / 2) ^ 2)

theorem rabiFreq_sq (J Δ : ℝ) : rabiFreq J Δ ^ 2 = J ^ 2 + (Δ / 2) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem rabiFreq_pos {J : ℝ} (hJ : 0 < J) (Δ : ℝ) : 0 < rabiFreq J Δ :=
  Real.sqrt_pos.mpr (by positivity)

theorem le_rabiFreq {J : ℝ} (hJ : 0 ≤ J) (Δ : ℝ) : J ≤ rabiFreq J Δ := by
  rw [rabiFreq, ← Real.sqrt_sq hJ]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Δ / 2), Real.sq_sqrt (sq_nonneg J)])

theorem rabiFreq_zero {J : ℝ} (hJ : 0 ≤ J) : rabiFreq J 0 = J := by
  simp [rabiFreq, Real.sqrt_sq hJ]

/-- The peak transfer `(J/Ω)²` is at most `1`. -/
theorem div_rabiFreq_sq_le_one {J : ℝ} (hJ : 0 < J) (Δ : ℝ) : (J / rabiFreq J Δ) ^ 2 ≤ 1 := by
  have hΩ := rabiFreq_pos hJ Δ
  rw [div_pow, div_le_one (by positivity), rabiFreq_sq]
  nlinarith [sq_nonneg (Δ / 2)]

theorem div_rabiFreq_sq_pos {J : ℝ} (hJ : 0 < J) (Δ : ℝ) : 0 < (J / rabiFreq J Δ) ^ 2 := by
  have hΩ := rabiFreq_pos hJ Δ
  positivity

/-- ★ **The detuning loss**: `1 − (J/Ω)² = (Δ/2)²/Ω²`. -/
theorem one_sub_div_rabiFreq_sq {J : ℝ} (hJ : 0 < J) (Δ : ℝ) :
    1 - (J / rabiFreq J Δ) ^ 2 = (Δ / 2) ^ 2 / rabiFreq J Δ ^ 2 := by
  have hΩ := (rabiFreq_pos hJ Δ).ne'
  rw [div_pow]
  field_simp
  rw [rabiFreq_sq]
  ring

/-- The detuning loss is strictly positive whenever `Δ ≠ 0`. -/
theorem div_rabiFreq_sq_lt_one {J : ℝ} (hJ : 0 < J) {Δ : ℝ} (hΔ : Δ ≠ 0) :
    (J / rabiFreq J Δ) ^ 2 < 1 := by
  have h := one_sub_div_rabiFreq_sq hJ Δ
  have hpos : 0 < (Δ / 2) ^ 2 / rabiFreq J Δ ^ 2 := by
    have := rabiFreq_pos hJ Δ
    have : (Δ / 2) ≠ 0 := by positivity
    positivity
  linarith

/-- The rescaled traceless part `Y = (J X + (Δ/2) Z)/Ω`, with `Y² = P` and `Y P = Y`. -/
noncomputable def rabiY (J Δ : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (((rabiFreq J Δ)⁻¹ : ℝ) : ℂ) • ((J : ℂ) • hopX + ((Δ / 2 : ℝ) : ℂ) • zOp)

theorem rabiY_mul_oneExc (J Δ : ℝ) : rabiY J Δ * oneExc = rabiY J Δ := by
  rw [rabiY, smul_mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, hopX_mul_oneExc,
    zOp_mul_oneExc]

theorem oneExc_mul_rabiY (J Δ : ℝ) : oneExc * rabiY J Δ = rabiY J Δ := by
  rw [rabiY, mul_smul_comm, mul_add, mul_smul_comm, mul_smul_comm, oneExc_mul_hopX,
    oneExc_mul_zOp]

theorem rabiY_mul_rabiY {J : ℝ} (hJ : 0 < J) (Δ : ℝ) : rabiY J Δ * rabiY J Δ = oneExc := by
  have hcross : hopX * zOp = -(zOp * hopX) := by
    rw [hopX_mul_zOp, zOp_mul_hopX, neg_sub]
  have hsq : ((J : ℂ) • hopX + ((Δ / 2 : ℝ) : ℂ) • zOp)
      * ((J : ℂ) • hopX + ((Δ / 2 : ℝ) : ℂ) • zOp)
      = ((J : ℂ) * J + ((Δ / 2 : ℝ) : ℂ) * ((Δ / 2 : ℝ) : ℂ)) • oneExc := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hopX_mul_hopX, zOp_mul_zOp, hcross]
    module
  have hΩ : (((rabiFreq J Δ)⁻¹ : ℝ) : ℂ) * (((rabiFreq J Δ)⁻¹ : ℝ) : ℂ)
      * ((J : ℂ) * J + ((Δ / 2 : ℝ) : ℂ) * ((Δ / 2 : ℝ) : ℂ)) = 1 := by
    have hpos := (rabiFreq_pos hJ Δ).ne'
    have h : ((rabiFreq J Δ)⁻¹ * (rabiFreq J Δ)⁻¹ * (J * J + Δ / 2 * (Δ / 2)) : ℝ) = 1 := by
      rw [show (J * J + Δ / 2 * (Δ / 2) : ℝ) = rabiFreq J Δ ^ 2 by rw [rabiFreq_sq]; ring]
      field_simp
    exact_mod_cast h
  rw [rabiY, smul_mul_assoc, mul_smul_comm, smul_smul, hsq, smul_smul, hΩ, one_smul]

/-! ### The detuned Hamiltonian, its generator and its flow -/

/-- The detuned Hamiltonian `H(Δ) = J X + Δ n_B`. -/
noncomputable def detunedH (J Δ : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (J : ℂ) • hopX + (Δ : ℂ) • occB

theorem detunedH_conjTranspose (J Δ : ℝ) : (detunedH J Δ)ᴴ = detunedH J Δ := by
  rw [detunedH, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hopX_conjTranspose,
    occB_conjTranspose, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]

/-- `H(Δ) = (Δ/2) P + Ω Y`. -/
theorem detunedH_eq {J : ℝ} (hJ : 0 < J) (Δ : ℝ) :
    detunedH J Δ = ((Δ / 2 : ℝ) : ℂ) • oneExc + ((rabiFreq J Δ : ℝ) : ℂ) • rabiY J Δ := by
  rw [rabiY, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (rabiFreq_pos hJ Δ).ne',
    Complex.ofReal_one, one_smul, detunedH, oneExc_eq_occA_add_occB, zOp]
  push_cast
  module

/-- The Schrödinger generator `−(i/ħ) H(Δ)`. -/
noncomputable def detunedGen (J ħ Δ : ℝ) : Matrix HopConfig HopConfig ℂ :=
  (-(Complex.I * ((1 / ħ : ℝ) : ℂ))) • detunedH J Δ

theorem detunedGen_skew (J ħ Δ : ℝ) : (detunedGen J ħ Δ)ᴴ = -(detunedGen J ħ Δ) :=
  skew_neg_I_smul_of_hermitian (1 / ħ) (detunedH_conjTranspose J Δ)

/-- At zero detuning the generator is the hop's. -/
theorem detunedGen_zero (J ħ : ℝ) : detunedGen J ħ 0 = hopGen J ħ := by
  rw [detunedGen, detunedH, hopGen, Complex.ofReal_zero, zero_smul, add_zero, smul_smul]
  congr 1
  push_cast
  ring

theorem continuous_detunedGen (J ħ : ℝ) : Continuous fun Δ : ℝ => detunedGen J ħ Δ := by
  unfold detunedGen detunedH
  fun_prop

/-- ★ **The detuned exchange as a field-structured flow**: the one edge `(A, B)` carrying `−(i/ħ)
(J X + Δ n_B)`. -/
noncomputable def detunedFlow (J ħ Δ : ℝ) : FieldStructuredFlow 2 2 where
  edges := {(0, 1)}
  piece := fun _ => detunedGen J ħ Δ
  piece_supported := by
    intro e he
    rw [Finset.mem_singleton] at he
    subst he
    exact supportedOn_pair _
  gen_skew := by
    rw [Finset.sum_singleton]
    exact detunedGen_skew J ħ Δ

theorem detunedFlow_val (J ħ Δ t : ℝ) :
    ((detunedFlow J ħ Δ).flow t).val = exp (t • detunedGen J ħ Δ) := by
  simp only [FieldStructuredFlow.flow_val, detunedFlow, Finset.sum_singleton]

/-- At zero detuning the flow is the hop's flow. -/
theorem detunedFlow_val_zero_detuning (J ħ t : ℝ) :
    ((detunedFlow J ħ 0).flow t).val = ((hopFlow J ħ).flow t).val := by
  rw [detunedFlow_val, hopFlow_val, detunedGen_zero]

/-- The flow is continuous jointly in the detuning and the time. -/
theorem continuous_detunedFlowVal_prod (J ħ : ℝ) :
    Continuous fun x : ℝ × ℝ => ((detunedFlow J ħ x.1).flow x.2).val := by
  simp only [detunedFlow_val]
  have hexp : Continuous (exp : Matrix HopConfig HopConfig ℂ → Matrix HopConfig HopConfig ℂ) :=
    continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt
  exact hexp.comp (continuous_snd.smul ((continuous_detunedGen J ħ).comp continuous_fst))

theorem continuous_detunedFlowVal (J ħ Δ : ℝ) :
    Continuous fun t : ℝ => ((detunedFlow J ħ Δ).flow t).val := by
  simp only [detunedFlow_val]
  have hexp : Continuous (exp : Matrix HopConfig HopConfig ℂ → Matrix HopConfig HopConfig ℂ) :=
    continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt
  exact hexp.comp (continuous_id.smul continuous_const)

/-- The unitary itself, as a continuous family in the detuning and the time. -/
theorem continuous_detunedFlow_prod (J ħ : ℝ) :
    Continuous fun x : ℝ × ℝ => (detunedFlow J ħ x.1).flow x.2 :=
  continuous_induced_rng.2 (continuous_detunedFlowVal_prod J ħ)

theorem continuous_detunedFlow (J ħ Δ : ℝ) : Continuous fun t : ℝ => (detunedFlow J ħ Δ).flow t :=
  continuous_induced_rng.2 (continuous_detunedFlowVal J ħ Δ)

/-- The Schrödinger equation of the detuned exchange: `U' = G U`, with the state-dependent
generator. -/
theorem hasDerivAt_detunedFlowVal (J ħ Δ t : ℝ) :
    HasDerivAt (fun t : ℝ => ((detunedFlow J ħ Δ).flow t).val)
      (detunedGen J ħ Δ * ((detunedFlow J ħ Δ).flow t).val) t := by
  simp only [detunedFlow_val]
  exact hasDerivAt_exp_smul_const' (detunedGen J ħ Δ) t

/-! ### The closed form -/

/-- The dynamical phase `Δ t/(2ħ)`. -/
noncomputable def dynPhase (ħ Δ t : ℝ) : ℝ := Δ * t / (2 * ħ)

/-- The Rabi rate `Ω/ħ`. -/
noncomputable def rabiRate (J ħ Δ : ℝ) : ℝ := rabiFreq J Δ / ħ

/-- The Rabi angle `Ω t/ħ`. -/
noncomputable def rabiAngle (J ħ Δ t : ℝ) : ℝ := rabiRate J ħ Δ * t

theorem rabiRate_pos {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) : 0 < rabiRate J ħ Δ :=
  div_pos (rabiFreq_pos hJ Δ) hħ

theorem smul_detunedGen {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    t • detunedGen J ħ Δ
      = (((-dynPhase ħ Δ t : ℝ) : ℂ) * Complex.I) • oneExc
        + (((-rabiAngle J ħ Δ t : ℝ) : ℂ) * Complex.I) • rabiY J Δ := by
  rw [detunedGen, detunedH_eq hJ, matrix_real_smul, smul_add, smul_smul, smul_smul, smul_add,
    smul_smul, smul_smul]
  congr 1
  · congr 1
    push_cast [dynPhase]
    ring
  · congr 1
    push_cast [rabiAngle, rabiRate]
    ring

/-- ★★ **The flow in closed form**:
`U(t) = 1 + (e^{−iΔt/2ħ} cos(Ωt/ħ) − 1) P − i e^{−iΔt/2ħ} sin(Ωt/ħ) Y`. -/
theorem detunedFlow_val_eq {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    ((detunedFlow J ħ Δ).flow t).val
      = 1 + (Complex.exp (((-dynPhase ħ Δ t : ℝ) : ℂ) * Complex.I)
            * (Real.cos (rabiAngle J ħ Δ t) : ℂ) - 1) • oneExc
        + (-(Complex.I * Complex.exp (((-dynPhase ħ Δ t : ℝ) : ℂ) * Complex.I)
            * (Real.sin (rabiAngle J ħ Δ t) : ℂ))) • rabiY J Δ := by
  rw [detunedFlow_val, smul_detunedGen hJ]
  set a : ℂ := ((-dynPhase ħ Δ t : ℝ) : ℂ) * Complex.I with ha
  set b : ℂ := ((-rabiAngle J ħ Δ t : ℝ) : ℂ) * Complex.I with hb
  have hcomm : Commute (a • oneExc) (b • rabiY J Δ) := by
    have h : Commute oneExc (rabiY J Δ) := by
      show oneExc * rabiY J Δ = rabiY J Δ * oneExc
      rw [oneExc_mul_rabiY, rabiY_mul_oneExc]
    exact (h.smul_left a).smul_right b
  rw [Matrix.exp_add_of_commute _ _ hcomm,
    exp_smul_eq_cosh_sinh oneExc_mul_oneExc oneExc_mul_oneExc a,
    exp_smul_eq_cosh_sinh (rabiY_mul_rabiY hJ Δ) (rabiY_mul_oneExc J Δ) b]
  have hb_cosh : Complex.cosh b = (Real.cos (rabiAngle J ħ Δ t) : ℂ) := by
    rw [hb, Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_neg]
  have hb_sinh : Complex.sinh b = -(Complex.I * (Real.sin (rabiAngle J ħ Δ t) : ℂ)) := by
    rw [hb, Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_neg]
    push_cast
    ring
  rw [hb_cosh, hb_sinh, ← Complex.cosh_add_sinh a]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    oneExc_mul_oneExc, oneExc_mul_rabiY]
  module

/-! ### Entries of the closed form -/

theorem oneExc_apply_vacC (i : HopConfig) : oneExc i vacC = 0 := by
  simp [oneExc, Matrix.single, Matrix.of_apply, vacC_ne_excA.symm, vacC_ne_excB.symm]

theorem rabiY_apply_vacC (J Δ : ℝ) (i : HopConfig) : rabiY J Δ i vacC = 0 := by
  simp [rabiY, zOp, occA, occB, hopX, Matrix.single, Matrix.of_apply, vacC_ne_excA.symm,
    vacC_ne_excB.symm]

theorem oneExc_apply_excB_excA : oneExc excB excA = 0 := by
  simp [oneExc, Matrix.single, Matrix.of_apply, excA_ne_excB, excA_ne_excB.symm]

theorem rabiY_apply_excB_excA (J Δ : ℝ) :
    rabiY J Δ excB excA = (((rabiFreq J Δ)⁻¹ : ℝ) : ℂ) * J := by
  simp [rabiY, zOp, occA, occB, hopX, Matrix.single, Matrix.of_apply, excA_ne_excB,
    excA_ne_excB.symm]

/-- The vacuum column of the flow is the vacuum: the vacuum is fixed. -/
theorem detunedFlow_apply_vacC {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) (i : HopConfig) :
    ((detunedFlow J ħ Δ).flow t).val i vacC = if i = vacC then 1 else 0 := by
  rw [detunedFlow_val_eq hJ]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, oneExc_apply_vacC,
    rabiY_apply_vacC]

/-- The transfer amplitude `U_{BA}(t) = −i e^{−iΔt/2ħ} · (J/Ω) sin(Ωt/ħ)`. -/
theorem detunedFlow_apply_excB_excA {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    ((detunedFlow J ħ Δ).flow t).val excB excA
      = -(Complex.I * Complex.exp (((-dynPhase ħ Δ t : ℝ) : ℂ) * Complex.I))
          * ((Real.sin (rabiAngle J ħ Δ t) * (J / rabiFreq J Δ) : ℝ) : ℂ) := by
  rw [detunedFlow_val_eq hJ]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, oneExc_apply_excB_excA,
    rabiY_apply_excB_excA, smul_eq_mul, ite_eq_right excA_ne_excB.symm]
  push_cast
  ring

theorem toEuclideanLin_detunedFlow_vacC {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    Matrix.toEuclideanLin ((detunedFlow J ħ Δ).flow t).val (basisVec vacC) = basisVec vacC := by
  ext c
  rw [toEuclideanLin_coord]
  have hfun : (fun j => basisVec vacC j) = Pi.single vacC (1 : ℂ) := funext fun j => rfl
  rw [hfun, mulVec_single_one, basisVec_apply]
  simp only [Matrix.col_apply, detunedFlow_apply_vacC hJ, Pi.single_apply]

/-- **The vacuum is fixed by the detuned flow**: message `0` never reaches the receiver. -/
theorem detunedFlow_msgPoint_zero {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    (detunedFlow J ħ Δ).arenaFlow t (msgPoint 0) = msgPoint 0 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_zero, arenaKick_mk]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by
    rw [one_smul, toEuclideanLin_detunedFlow_vacC hJ]⟩

theorem norm_basisVec (c : HopConfig) : ‖basisVec c‖ = 1 := by
  rw [basisVec, PiLp.norm_single, norm_one]

theorem detunedFlow_isom (J ħ Δ t : ℝ) :
    (((detunedFlow J ħ Δ).flow t).val)ᴴ * ((detunedFlow J ħ Δ).flow t).val = 1 := by
  have h := ((detunedFlow J ħ Δ).flow t).property
  rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h

/-! ### The receiver's readouts under detuning -/

/-- ★★ **The detuned Rabi formula**: the receiver's occupancy for message `1` is
`(J/Ω)² sin²(Ωt/ħ)`. -/
theorem detuned_readout_one {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1))
      = (J / rabiFreq J Δ) ^ 2 * Real.sin (rabiAngle J ħ Δ t) ^ 2 := by
  rw [FieldStructuredFlow.arenaFlow, msgPoint_one, arenaKick_mk, occB, arenaObs_single_mk,
    Matrix.norm_toEuclideanLin_of_isom (detunedFlow_isom J ħ Δ t), norm_basisVec, one_pow,
    div_one, toEuclideanLin_coord]
  have hfun : (fun j => basisVec excA j) = Pi.single excA (1 : ℂ) := funext fun j => rfl
  rw [hfun, mulVec_single_one, Matrix.col_apply, detunedFlow_apply_excB_excA hJ, norm_mul,
    norm_neg, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- The receiver's occupancy for message `0` is `0`. -/
theorem detuned_readout_zero {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 0)) = 0 := by
  rw [detunedFlow_msgPoint_zero hJ, msgPoint_zero, occB, arenaObs_single_mk, basisVec_apply,
    Pi.single_eq_of_ne vacC_ne_excB.symm, norm_zero]
  simp

/-- ★ **The detuning loss**: the readout never exceeds `(J/Ω)²`. -/
theorem detuned_readout_one_le {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1)) ≤ (J / rabiFreq J Δ) ^ 2 := by
  rw [detuned_readout_one hJ]
  have h1 := Real.sin_sq_le_one (rabiAngle J ħ Δ t)
  have h2 := div_rabiFreq_sq_pos hJ Δ
  nlinarith

/-- The detuned hop time `π ħ/(2Ω)`. -/
noncomputable def detunedHopTime (J ħ Δ : ℝ) : ℝ := Real.pi * ħ / (2 * rabiFreq J Δ)

theorem rabiAngle_detunedHopTime {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    rabiAngle J ħ Δ (detunedHopTime J ħ Δ) = Real.pi / 2 := by
  have hΩ := (rabiFreq_pos hJ Δ).ne'
  unfold rabiAngle rabiRate detunedHopTime
  field_simp

/-- ★ **The loss is attained**: at the detuned hop time the readout is exactly `(J/Ω)²`. -/
theorem detuned_readout_one_peak {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    arenaObs occB ((detunedFlow J ħ Δ).arenaFlow (detunedHopTime J ħ Δ) (msgPoint 1))
      = (J / rabiFreq J Δ) ^ 2 := by
  rw [detuned_readout_one hJ, rabiAngle_detunedHopTime hJ hħ, Real.sin_pi_div_two, one_pow,
    mul_one]

/-- With a nonzero detuning the transfer is never complete. -/
theorem detuned_readout_one_lt_one {J : ℝ} (hJ : 0 < J) (ħ : ℝ) {Δ : ℝ} (hΔ : Δ ≠ 0) (t : ℝ) :
    arenaObs occB ((detunedFlow J ħ Δ).arenaFlow t (msgPoint 1)) < 1 :=
  (detuned_readout_one_le hJ ħ Δ t).trans_lt (div_rabiFreq_sq_lt_one hJ hΔ)

/-! ### The carrier's energy is conserved -/

theorem detunedH_commute_flow (J ħ Δ t : ℝ) :
    Commute (detunedH J Δ) ((detunedFlow J ħ Δ).flow t).val := by
  rw [detunedFlow_val, detunedGen]
  exact (((Commute.refl (detunedH J Δ)).smul_right _).smul_right t).exp_right

/-- ★ **Energy conservation on the carrier**: `⟨H(Δ)⟩` is constant along the detuned flow. -/
theorem arenaObs_detunedH_arenaFlow (J ħ Δ t : ℝ) (p : FieldArena 2 2) :
    arenaObs (detunedH J Δ) ((detunedFlow J ħ Δ).arenaFlow t p) = arenaObs (detunedH J Δ) p := by
  rw [FieldStructuredFlow.arenaFlow, arenaObs_kick_conj, Matrix.star_eq_conjTranspose,
    Matrix.mul_assoc, (detunedH_commute_flow J ħ Δ t).eq, ← Matrix.mul_assoc,
    detunedFlow_isom, Matrix.one_mul]

/-- The energy of the detuned Hamiltonian at a ray: `J⟨X⟩ + Δ n_B`. -/
theorem arenaObs_detunedH (J Δ : ℝ) (p : FieldArena 2 2) :
    arenaObs (detunedH J Δ) p = J * arenaObs hopX p + Δ * momentMap p excB := by
  rw [detunedH, arenaObs_add, arenaObs_real_smul, arenaObs_real_smul, occB,
    arenaObs_single_eq_momentMap]

/-! ### The occupancy history and its time integral -/

/-- **The receiver's occupancy history** along the detuned exchange from `p`. -/
noncomputable def occHist (J ħ Δ : ℝ) (p : FieldArena 2 2) (s : ℝ) : ℝ :=
  arenaObs occB ((detunedFlow J ħ Δ).arenaFlow s p)

theorem occHist_eq_momentMap (J ħ Δ : ℝ) (p : FieldArena 2 2) (s : ℝ) :
    occHist J ħ Δ p s = momentMap ((detunedFlow J ħ Δ).arenaFlow s p) excB := by
  rw [occHist, occB, arenaObs_single_eq_momentMap]

theorem occHist_nonneg (J ħ Δ : ℝ) (p : FieldArena 2 2) (s : ℝ) : 0 ≤ occHist J ħ Δ p s := by
  rw [occHist_eq_momentMap]
  exact momentMap_nonneg _ _

theorem occHist_le_one (J ħ Δ : ℝ) (p : FieldArena 2 2) (s : ℝ) : occHist J ħ Δ p s ≤ 1 := by
  rw [occHist_eq_momentMap]
  have h := momentMap_sum_eq_one ((detunedFlow J ħ Δ).arenaFlow s p)
  rw [← h]
  exact Finset.single_le_sum (fun c _ => momentMap_nonneg _ c) (Finset.mem_univ excB)

/-- The history in Heisenberg form: the occupancy of the evolved ray is the expectation of the
evolved occupancy. -/
theorem occHist_eq_heis (J ħ Δ : ℝ) (p : FieldArena 2 2) (s : ℝ) :
    occHist J ħ Δ p s
      = arenaObs (star ((detunedFlow J ħ Δ).flow s).val * occB
          * ((detunedFlow J ħ Δ).flow s).val) p := by
  rw [occHist, FieldStructuredFlow.arenaFlow, arenaObs_kick_conj]

/-- **The history is continuous jointly in the ray, the detuning and the time**, stated in the
uncurried form the parametric-integral lemma consumes. -/
theorem continuous_occHist_prod (J ħ : ℝ) :
    Continuous (Function.uncurry fun (x : FieldArena 2 2 × ℝ) (s : ℝ) => occHist J ħ x.2 x.1 s) := by
  unfold Function.uncurry occHist FieldStructuredFlow.arenaFlow
  have hU : Continuous fun x : (FieldArena 2 2 × ℝ) × ℝ => (detunedFlow J ħ x.1.2).flow x.2 :=
    (continuous_detunedFlow_prod J ħ).comp₂ (continuous_snd.comp continuous_fst) continuous_snd
  exact continuous_const.arenaObs (hU.arenaKick (continuous_fst.comp continuous_fst))

theorem continuous_occHist (J ħ Δ : ℝ) (p : FieldArena 2 2) :
    Continuous fun s => occHist J ħ Δ p s := by
  unfold occHist FieldStructuredFlow.arenaFlow
  exact continuous_const.arenaObs ((continuous_detunedFlow J ħ Δ).arenaKick continuous_const)

/-- **The accumulated receiver occupancy** `∫₀ᵗ n_B(p(s)) ds`. -/
noncomputable def occAccum (J ħ Δ : ℝ) (p : FieldArena 2 2) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, occHist J ħ Δ p s

theorem occAccum_zero (J ħ Δ : ℝ) (p : FieldArena 2 2) : occAccum J ħ Δ p 0 = 0 :=
  intervalIntegral.integral_same

theorem occAccum_nonneg (J ħ Δ : ℝ) (p : FieldArena 2 2) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ occAccum J ħ Δ p t :=
  intervalIntegral.integral_nonneg ht fun s _ => occHist_nonneg J ħ Δ p s

theorem occAccum_le (J ħ Δ : ℝ) (p : FieldArena 2 2) {t : ℝ} (ht : 0 ≤ t) :
    occAccum J ħ Δ p t ≤ t := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (f := occHist J ħ Δ p)
    (g := fun _ => (1 : ℝ)) ht ((continuous_occHist J ħ Δ p).intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t) fun s _ => occHist_le_one J ħ Δ p s
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h
  exact h

/-- The history from the evolved ray is the shifted history. -/
theorem occHist_arenaFlow (J ħ Δ : ℝ) (p : FieldArena 2 2) (s u : ℝ) :
    occHist J ħ Δ ((detunedFlow J ħ Δ).arenaFlow s p) u = occHist J ħ Δ p (u + s) := by
  unfold occHist
  rw [FieldStructuredFlow.arenaFlow_add]

/-- ★ **The group law of the accumulated occupancy**: `A(p, s + t) = A(p, s) + A(U(s)p, t)`. -/
theorem occAccum_add (J ħ Δ : ℝ) (p : FieldArena 2 2) (s t : ℝ) :
    occAccum J ħ Δ p (s + t)
      = occAccum J ħ Δ p s + occAccum J ħ Δ ((detunedFlow J ħ Δ).arenaFlow s p) t := by
  unfold occAccum
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_occHist J ħ Δ p).intervalIntegrable 0 s)
    ((continuous_occHist J ħ Δ p).intervalIntegrable s (s + t))]
  congr 1
  simp_rw [occHist_arenaFlow]
  rw [intervalIntegral.integral_comp_add_right (fun u => occHist J ħ Δ p u) s, zero_add,
    add_comm t s]

/-- ★ **The pointer's rate**: the accumulated occupancy has derivative the occupancy. -/
theorem hasDerivAt_occAccum (J ħ Δ : ℝ) (p : FieldArena 2 2) (t : ℝ) :
    HasDerivAt (fun t => occAccum J ħ Δ p t) (occHist J ħ Δ p t) t := by
  unfold occAccum
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_occHist J ħ Δ p).intervalIntegrable 0 t)
    ((continuous_occHist J ħ Δ p).stronglyMeasurableAtFilter volume _)
    (continuous_occHist J ħ Δ p).continuousAt

theorem continuous_occAccum (J ħ Δ : ℝ) (p : FieldArena 2 2) :
    Continuous fun t => occAccum J ħ Δ p t := by
  unfold occAccum
  exact intervalIntegral.continuous_primitive
    (fun a b => (continuous_occHist J ħ Δ p).intervalIntegrable a b) 0

/-- **The accumulated occupancy is continuous jointly in the ray and the detuning**, at every fixed
time — the measurability #194's skew product needs. -/
theorem continuous_occAccum_prod (J ħ t : ℝ) :
    Continuous fun x : FieldArena 2 2 × ℝ => occAccum J ħ x.2 x.1 t := by
  unfold occAccum
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x : FieldArena 2 2 × ℝ => fun s => occHist J ħ x.2 x.1 s)
    (continuous_occHist_prod J ħ) 0 t

/-! ### The two messages -/

theorem occHist_msgPoint_one {J : ℝ} (hJ : 0 < J) (ħ Δ s : ℝ) :
    occHist J ħ Δ (msgPoint 1) s = (J / rabiFreq J Δ) ^ 2 * Real.sin (rabiAngle J ħ Δ s) ^ 2 :=
  detuned_readout_one hJ ħ Δ s

theorem occHist_msgPoint_zero {J : ℝ} (hJ : 0 < J) (ħ Δ s : ℝ) :
    occHist J ħ Δ (msgPoint 0) s = 0 :=
  detuned_readout_zero hJ ħ Δ s

/-- **The pointer starts at rest**: at `t = 0` nothing has arrived at the receiver. -/
theorem occHist_msgPoint_one_zero {J : ℝ} (hJ : 0 < J) (ħ Δ : ℝ) :
    occHist J ħ Δ (msgPoint 1) 0 = 0 := by
  rw [occHist_msgPoint_one hJ, rabiAngle, mul_zero, Real.sin_zero]
  ring

/-- **The activation is the arriving carrier**: on `(0, πħ/Ω)` the occupancy is strictly positive. -/
theorem occHist_msgPoint_one_pos {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) {s : ℝ}
    (hs : 0 < s) (hs' : s < Real.pi / rabiRate J ħ Δ) :
    0 < occHist J ħ Δ (msgPoint 1) s := by
  rw [occHist_msgPoint_one hJ]
  have hω := rabiRate_pos hJ hħ Δ
  have hθ : 0 < rabiAngle J ħ Δ s := mul_pos hω hs
  have hθ' : rabiAngle J ħ Δ s < Real.pi := by
    rw [rabiAngle]
    rwa [lt_div_iff₀ hω, mul_comm] at hs'
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ hθ'
  have := div_rabiFreq_sq_pos hJ Δ
  positivity

theorem occAccum_msgPoint_zero {J : ℝ} (hJ : 0 < J) (ħ Δ t : ℝ) :
    occAccum J ħ Δ (msgPoint 0) t = 0 := by
  unfold occAccum
  simp [occHist_msgPoint_zero hJ]

/-- ★★ **The accumulated occupancy for message `1` in closed form**:
`(J/Ω)² (Ωt/ħ − sin(Ωt/ħ) cos(Ωt/ħ)) / (2Ω/ħ)`. -/
theorem occAccum_msgPoint_one {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ t : ℝ) :
    occAccum J ħ Δ (msgPoint 1) t
      = (J / rabiFreq J Δ) ^ 2
        * (rabiAngle J ħ Δ t - Real.sin (rabiAngle J ħ Δ t) * Real.cos (rabiAngle J ħ Δ t))
        / (2 * rabiRate J ħ Δ) := by
  have hω := (rabiRate_pos hJ hħ Δ).ne'
  unfold occAccum
  simp_rw [occHist_msgPoint_one hJ]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_mul_left (f := fun x => Real.sin x ^ 2) (a := 0) (b := t)
    hω
  simp only [mul_zero] at h
  rw [rabiAngle]
  simp only [rabiAngle] at h ⊢
  rw [h, integral_sin_sq, Real.sin_zero, Real.cos_zero, smul_eq_mul]
  field_simp
  ring

end CSD.CV

end
