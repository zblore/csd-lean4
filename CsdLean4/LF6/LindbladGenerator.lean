/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CsdLean4.LF2.QuantumChannel
import CsdLean4.LF6.DephasingSemigroup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# LF6-9: the general Lindblad (GKSL) generator and its CPTP-generating structure

**Category:** 6-Local (the continuous-time open-system de-isolation frontier — the generator tier).

`LF6/DephasingSemigroup.lean` and `LF6/AmplitudeDamping.lean` exhibit the two canonical qubit dissipators
(T2 dephasing, T1 amplitude damping) **directly**, as the exact solutions of their master equations —
but neither defines the underlying generator, proves complete positivity, or links the exhibited channel
to a generator. This module supplies the missing generator tier: the general **Lindblad / GKSL**
generator and the structural properties that make its flow a CPTP semigroup.

    ℒ(ρ) = −i[H, ρ] + Σₖ ( Lₖ ρ Lₖ† − ½{Lₖ†Lₖ, ρ} )          (`lindbladGenerator`)

## Main results

* `lindbladGenerator` / `lindbladDissipator` — the GKSL generator and one dissipator term, for any
  Hamiltonian `H` and jump operators `Lₖ` on `Matrix n n ℂ`.
* `lindbladGenerator_trace` — **trace annihilation** `tr ℒ(ρ) = 0`: the commutator and every dissipator
  are traceless (cyclicity + the `½{L†L,ρ}` counterterm), so the generated flow is **trace-preserving**.
* `lindbladGenerator_isHermitian` — `ℒ` maps Hermitian to Hermitian (for `H` Hermitian): the flow
  **preserves Hermiticity**, so density operators stay Hermitian.
* `lindblad_dissipation_posSemidef` — the dissipative **jump** part `Σₖ Lₖ ρ Lₖ†` preserves positive
  semidefiniteness — the same Choi–Kraus CP witness (`PosSemidef.mul_mul_conjTranspose_same`,
  `posSemidef_sum`) used for `QuantumChannel.apply`. This is the complete-positivity structure of the
  dissipator.

## The dephasing instance (generator ↔ exhibited semigroup)

* `dephasingGenerator` + `dephasingGenerator_eq_lindblad` — the T2 generator `(γ/2)(σ_z ρ σ_z − ρ)` is the
  GKSL generator with `H = 0` and the single jump operator `L = √(γ/2)·σ_z` (so dephasing **is** a
  Lindblad instance).
* `dephasingChannel_master_equation` — the exhibited `dephasingChannel` **solves** its master equation:
  `d/dt Φ_t(ρ) = ℒ_deph(Φ_t(ρ))` entrywise. This is the concrete `Φ_t = e^{tℒ}` content — the exhibited
  semigroup is genuinely the generator's flow, not merely asserted to be.

## Honest scope

The generator, its trace/Hermiticity/CP structure, and the dephasing generator↔flow correspondence are
proved here. **Deferred (the genuinely Mathlib-scale residual):** complete positivity of the *exponentiated*
map `e^{tℒ}` for an **arbitrary** GKSL generator (as opposed to the concrete qubit channels, whose CP is
their exhibited Kraus form) — that needs matrix-exponential positivity in the L2-operator norm scope. The
generator-level CP witness (`lindblad_dissipation_posSemidef`) is the buildable core.

References: `LF2/QuantumChannel.lean` (`apply_posSemidef`, the Kraus CP witness reused here);
`LF2/ChoiConverse.lean` (`choi_iff_posSemidef`, the CP↔PSD-Choi characterisation);
`LF6/DephasingSemigroup.lean` (`dephasingChannel`, the exhibited T2 semigroup); `specs/future-work.md`
(LF6-2, LF6-9); `specs/BACKLOG.md`.
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace CSD.LF6

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]

/-- **One Lindblad dissipator term** `D_L(ρ) = L ρ L† − ½(L†L ρ + ρ L†L)` (the `k`-th GKSL summand). -/
noncomputable def lindbladDissipator (L ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  L * ρ * Lᴴ - (1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

/-- **The general Lindblad (GKSL) generator** `ℒ(ρ) = −i[H,ρ] + Σₖ D_{Lₖ}(ρ)` for a Hamiltonian `H` and
jump operators `L : ι → Matrix n n ℂ`. -/
noncomputable def lindbladGenerator (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  -Complex.I • (H * ρ - ρ * H) + ∑ k, lindbladDissipator (L k) ρ

/-! ### Trace annihilation ⟹ the flow is trace-preserving -/

/-- **A single dissipator is traceless.** `tr(L ρ L†) = tr(L†L ρ)` (cyclicity) exactly cancels the
`½{L†L, ρ}` counterterm. -/
theorem lindbladDissipator_trace (L ρ : Matrix n n ℂ) : (lindbladDissipator L ρ).trace = 0 := by
  have h1 : (L * ρ * Lᴴ).trace = (Lᴴ * L * ρ).trace := Matrix.trace_mul_cycle L ρ Lᴴ
  have h2 : (ρ * (Lᴴ * L)).trace = (Lᴴ * L * ρ).trace := Matrix.trace_mul_comm ρ (Lᴴ * L)
  simp only [lindbladDissipator, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, h1, h2,
    smul_eq_mul]
  ring

/-- **Trace annihilation** `tr ℒ(ρ) = 0`. The commutator is traceless (`tr(Hρ) = tr(ρH)`) and every
dissipator is traceless, so the Lindblad flow preserves the trace — it is trace-preserving. -/
theorem lindbladGenerator_trace (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    (lindbladGenerator H L ρ).trace = 0 := by
  simp only [lindbladGenerator, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_sum, Matrix.trace_mul_comm H ρ, sub_self, smul_zero, zero_add]
  exact Finset.sum_eq_zero fun k _ => lindbladDissipator_trace (L k) ρ

/-! ### Complete positivity of the dissipative jump part -/

/-- **The dissipative jump part `Σₖ Lₖ ρ Lₖ†` preserves positive semidefiniteness.** Each `Lₖ ρ Lₖ†` is
PSD when `ρ` is (`PosSemidef.mul_mul_conjTranspose_same`) and PSD is closed under sums — the same
Choi–Kraus complete-positivity witness as `QuantumChannel.apply_posSemidef`. -/
theorem lindblad_dissipation_posSemidef (L : ι → Matrix n n ℂ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : (∑ k, L k * ρ * (L k)ᴴ).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => hρ.mul_mul_conjTranspose_same (L k)

/-! ### Hermiticity preservation ⟹ the flow keeps states Hermitian -/

/-- `L ρ L†` is Hermitian when `ρ` is. -/
private theorem isHermitian_mul_mul_conjTranspose {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (L : Matrix n n ℂ) : (L * ρ * Lᴴ).IsHermitian := by
  show (L * ρ * Lᴴ)ᴴ = L * ρ * Lᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hρ.eq, Matrix.mul_assoc]

/-- **A single dissipator preserves Hermiticity.** `LρL†` is Hermitian, as is `½{L†L, ρ}` (the
anticommutator of the Hermitian `L†L` with the Hermitian `ρ`); their difference is Hermitian. -/
theorem lindbladDissipator_isHermitian {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (L : Matrix n n ℂ) :
    (lindbladDissipator L ρ).IsHermitian := by
  have hA : (L * ρ * Lᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose hρ L
  have hB : (Lᴴ * L * ρ + ρ * (Lᴴ * L)).IsHermitian := by
    show (Lᴴ * L * ρ + ρ * (Lᴴ * L))ᴴ = Lᴴ * L * ρ + ρ * (Lᴴ * L)
    rw [Matrix.conjTranspose_add,
      show (Lᴴ * L * ρ)ᴴ = ρ * (Lᴴ * L) by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hρ.eq],
      show (ρ * (Lᴴ * L))ᴴ = Lᴴ * L * ρ by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hρ.eq],
      add_comm]
  have hsB : ((1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))).IsHermitian := by
    show ((1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L)))ᴴ = (1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))
    rw [Matrix.conjTranspose_smul, show star (1 / 2 : ℂ) = 1 / 2 by norm_num, hB.eq]
  show (lindbladDissipator L ρ)ᴴ = lindbladDissipator L ρ
  unfold lindbladDissipator
  rw [Matrix.conjTranspose_sub, hA.eq, hsB.eq]

/-- **The Lindblad generator preserves Hermiticity** (for `H` Hermitian): `ℒ(ρ)` is Hermitian whenever
`ρ` is, so a Hermitian density operator stays Hermitian under the flow. The commutator part
`−i[H,ρ]` is Hermitian (`(−i[H,ρ])† = i[ρ,H]·… = −i[H,ρ]`) and each dissipator is Hermitian. -/
theorem lindbladGenerator_isHermitian {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (L : ι → Matrix n n ℂ) :
    (lindbladGenerator H L ρ).IsHermitian := by
  have hcomm : (-Complex.I • (H * ρ - ρ * H)).IsHermitian := by
    show (-Complex.I • (H * ρ - ρ * H))ᴴ = -Complex.I • (H * ρ - ρ * H)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hH.eq, hρ.eq, show star (-Complex.I) = Complex.I by simp,
      neg_smul, ← smul_neg, neg_sub]
  have hsum : (∑ k, lindbladDissipator (L k) ρ).IsHermitian := by
    show (∑ k, lindbladDissipator (L k) ρ)ᴴ = ∑ k, lindbladDissipator (L k) ρ
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => (lindbladDissipator_isHermitian hρ (L k)).eq
  show (lindbladGenerator H L ρ)ᴴ = lindbladGenerator H L ρ
  unfold lindbladGenerator
  rw [Matrix.conjTranspose_add, hcomm.eq, hsum.eq]

/-! ### The T2 dephasing instance: generator ↔ exhibited semigroup

The qubit dephasing generator `(γ/2)(σ_z ρ σ_z − ρ)` is the GKSL generator with `H = 0` and one jump
operator `L = √(γ/2)·σ_z`, and the exhibited `dephasingChannel` solves its master equation. -/

/-- The Pauli `σ_z = diag(1, −1)`. -/
noncomputable def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

@[simp] theorem sigmaZ_mul_self : sigmaZ * sigmaZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigmaZ_conjTranspose : sigmaZᴴ = sigmaZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, Matrix.conjTranspose_apply]

/-- **The T2 dephasing generator** `ℒ_deph(ρ) = (γ/2)(σ_z ρ σ_z − ρ)` — the RHS of the dephasing master
equation `dρ/dt = ℒ_deph(ρ)`. -/
noncomputable def dephasingGenerator (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (γ / 2 : ℂ) • (sigmaZ * ρ * sigmaZ - ρ)

@[simp] theorem dephasingGenerator_apply_00 (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingGenerator γ ρ 0 0 = 0 := by
  simp only [dephasingGenerator, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

@[simp] theorem dephasingGenerator_apply_11 (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingGenerator γ ρ 1 1 = 0 := by
  simp only [dephasingGenerator, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

@[simp] theorem dephasingGenerator_apply_01 (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingGenerator γ ρ 0 1 = -(γ : ℂ) * ρ 0 1 := by
  simp only [dephasingGenerator, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

@[simp] theorem dephasingGenerator_apply_10 (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingGenerator γ ρ 1 0 = -(γ : ℂ) * ρ 1 0 := by
  simp only [dephasingGenerator, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- **Dephasing is a Lindblad instance.** For `γ ≥ 0`, the T2 dephasing generator is the GKSL generator
with no Hamiltonian and the single jump operator `L = √(γ/2)·σ_z`:
`(γ/2)(σ_z ρ σ_z − ρ) = ℒ(ρ)` with `H = 0`, `L₀ = √(γ/2)·σ_z`. So the general trace/Hermiticity/CP
structure specialises to dephasing. -/
theorem dephasingGenerator_eq_lindblad {γ : ℝ} (hγ : 0 ≤ γ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingGenerator γ ρ
      = lindbladGenerator 0 (fun _ : Fin 1 => (Real.sqrt (γ / 2) : ℂ) • sigmaZ) ρ := by
  have hsq : (Real.sqrt (γ / 2) : ℂ) * (Real.sqrt (γ / 2) : ℂ) = (γ / 2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith), Complex.ofReal_div,
      Complex.ofReal_ofNat]
  simp only [lindbladGenerator, lindbladDissipator, Fin.sum_univ_one, zero_mul, mul_zero, sub_self,
    smul_zero, zero_add, Matrix.conjTranspose_smul, sigmaZ_conjTranspose, Complex.star_def,
    Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, smul_smul, hsq, sigmaZ_mul_self,
    Matrix.one_mul, Matrix.mul_one, dephasingGenerator, smul_sub]
  module

/-! ### The dephasing master equation: the exhibited semigroup is the generator's flow -/

/-- The complex decay factor `e^{-γt}·c` has derivative `−γ·e^{-γt}·c` in `t`. -/
private theorem hasDerivAt_expDecay (γ t : ℝ) (c : ℂ) :
    HasDerivAt (fun τ : ℝ => (Real.exp (-(γ * τ)) : ℂ) * c)
      (-(γ : ℂ) * (Real.exp (-(γ * t)) : ℂ) * c) t := by
  have hlin : HasDerivAt (fun τ : ℝ => -(γ * τ)) (-γ) t := by
    simpa using ((hasDerivAt_id t).const_mul γ).neg
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-(γ * τ))) (Real.exp (-(γ * t)) * -γ) t :=
    (Real.hasDerivAt_exp _).comp t hlin
  have hC : HasDerivAt (fun τ : ℝ => (Real.exp (-(γ * τ)) : ℂ))
      ((Real.exp (-(γ * t)) * -γ : ℝ) : ℂ) t := hexp.ofReal_comp
  have hmul := hC.mul_const c
  convert hmul using 1
  push_cast; ring

/-- **The dephasing master equation.** The exhibited T2 semigroup `dephasingChannel` **solves** its
Lindblad master equation entrywise: `d/dt Φ_t(ρ) = ℒ_deph(Φ_t(ρ))`. The populations are stationary
(`ℒ_deph` kills the diagonal, `Φ` is constant there); each coherence decays at rate `γ`
(`d/dt(e^{-γt}ρ₀₁) = −γ·e^{-γt}ρ₀₁`), which is exactly `ℒ_deph(Φ_t(ρ))` off-diagonal. So the directly
exhibited channel genuinely is the generator's flow (`Φ_t = e^{tℒ}`), not merely asserted to be. -/
theorem dephasingChannel_master_equation (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun τ => dephasingChannel γ τ ρ i j)
      (dephasingGenerator γ (dephasingChannel γ t ρ) i j) t := by
  fin_cases i <;> fin_cases j
  · simp only [Fin.isValue, Fin.zero_eta, dephasingChannel_apply_00, dephasingGenerator_apply_00]
    exact hasDerivAt_const t (ρ 0 0)
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, dephasingGenerator_apply_01,
      dephasingChannel_apply_01]
    convert hasDerivAt_expDecay γ t (ρ 0 1) using 1
    ring
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, dephasingGenerator_apply_10,
      dephasingChannel_apply_10]
    convert hasDerivAt_expDecay γ t (ρ 1 0) using 1
    ring
  · simp only [Fin.isValue, Fin.mk_one, dephasingChannel_apply_11, dephasingGenerator_apply_11]
    exact hasDerivAt_const t (ρ 1 1)
