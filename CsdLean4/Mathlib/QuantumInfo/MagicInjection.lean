/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Magic
public import CsdLean4.Mathlib.QuantumInfo.Channel

/-!
# T-gate injection: the magic state enacts `T` through Clifford gates and a measurement

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #66 and #67, the two rows of
`R-006` (`specs/magic-plan.md`, "The split").

The gate-teleportation circuit: data qubit `ψ` on wire `0`, the magic state `|A⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2`
(`magicState`) on wire `1`; `CNOT` with control `0` and target `1`; measure the ancilla in the
computational basis with outcome `m`; apply `S^m` to the data. The data qubit is then `T ψ` — up to
the normalisation `1/√2` of the outcome and, for `m = 1`, the global phase `e^{iπ/4}`:

`(S^m ⊗ ⟨m|) · CNOT · (ψ ⊗ |A⟩) = (1/√2) · e^{imπ/4} · T ψ`.

* `dataAnc ψ φ : QReg 2` — the product state (data, ancilla); `sCorr m` — the correction `S^m`
  on the data wire; `injectSlice φ m ψ : QReg 1` — the unnormalised data state after the circuit
  with resource `φ` and outcome `m`;
* ★★ `injectSlice_magicState` — **the injection identity** (row #66): with the resource
  `magicState`, `injectSlice magicState m ψ = (1/√2) e^{imπ/4} • T ψ`, for both outcomes;
  `norm_sq_injectSlice_magicState` — each outcome has probability `½`;
* ★ `injectSlice_zMagicState` — **the error transfers**: with the resource `Z|A⟩` the circuit
  yields `(1/√2)(−e^{iπ/4})^m • Z T ψ`;
* `injectionKraus φ m` — the Kraus operator `(S^m ⊗ ⟨m|) · CNOT · (1 ⊗ |φ⟩)` as a matrix on the data
  qubit; `injectionKraus_magicState`, `injectionKraus_zMagicState` — their closed forms
  `c_m • T` and `c'_m • Z T`;
* `injectionChannel : Channel` — the circuit as a quantum channel on the data qubit;
  ★★ `injectionChannel_apply` — **`T` enacted** (row #67, closes `R-006`): `Φ(ρ) = T ρ T†` for every
  `ρ`, consuming one magic state;
* `noisyInjectionChannel p` — the same with the resource `(1 − p)|A⟩⟨A| + p Z|A⟩⟨A|Z`;
  ★ `noisyInjectionChannel_apply` — `Φ_p(ρ) = (1 − p) T ρ T† + p Z T ρ T† Z`: a `Z`-error on the
  resource becomes a `Z`-error on the output, the error model that distillation (#75–#78) consumes.

## Honest scope

⚠️ One data qubit; the two-qubit circuit is written in the coordinate-operator model of
`Clifford.lean`/`Magic.lean` (wires `0` and `1` of `QReg 2`). The channel is the outcome-averaged
one with the classical correction applied; the measurement statistics are the `‖·‖²` of the slices.
Distillation of noisy magic states is BACKLOG #75–#79, Clifford+T density #68–#74.

References: D. Gottesman, I. Chuang, Nature 402 (1999) 390; S. Bravyi, A. Kitaev, PRA 71 (2005)
022316 §II; Nielsen–Chuang §10.6.2; `specs/magic-plan.md`; `specs/BACKLOG.md` #66, #67;
`specs/future-work.md`.
-/

@[expose] public section

open scoped ComplexConjugate
open Matrix

namespace QuantumInfo

/-! ### The circuit -/

/-- The two-qubit label `(x, m)`: data `x` on wire `0`, ancilla `m` on wire `1`. -/
def pair (x m : Fin 2) : Fin 2 → Fin 2 := ![x, m]

@[simp] lemma pair_zero (x m : Fin 2) : pair x m 0 = x := rfl

@[simp] lemma pair_one (x m : Fin 2) : pair x m 1 = m := rfl

/-- The product state `ψ ⊗ φ` on two qubits: data `ψ` on wire `0`, ancilla `φ` on wire `1`. -/
noncomputable def dataAnc (ψ φ : QReg 1) : QReg 2 :=
  (WithLp.equiv 2 ((Fin 2 → Fin 2) → ℂ)).symm (fun z => ψ (fun _ => z 0) * φ (fun _ => z 1))

@[simp] lemma dataAnc_apply (ψ φ : QReg 1) (z : Fin 2 → Fin 2) :
    dataAnc ψ φ z = ψ (fun _ => z 0) * φ (fun _ => z 1) := rfl

/-- The correction `S^m` on the data wire. -/
noncomputable def sCorr (m : Fin 2) (Φ : QReg 2) : QReg 2 :=
  if m = 0 then Φ else sGate 0 Φ

/-- The unnormalised data state after the injection circuit with resource `φ` and outcome `m`:
`(S^m ⊗ ⟨m|) · CNOT_{01} · (ψ ⊗ φ)`. -/
noncomputable def injectSlice (φ : QReg 1) (m : Fin 2) (ψ : QReg 1) : QReg 1 :=
  (WithLp.equiv 2 ((Fin 1 → Fin 2) → ℂ)).symm
    (fun x => sCorr m (cnotGate 0 1 (dataAnc ψ φ)) (pair (x 0) m))

@[simp] lemma injectSlice_apply (φ : QReg 1) (m : Fin 2) (ψ : QReg 1) (x : Fin 1 → Fin 2) :
    injectSlice φ m ψ x = sCorr m (cnotGate 0 1 (dataAnc ψ φ)) (pair (x 0) m) := rfl

lemma cnotFlip_pair (x m : Fin 2) : cnotFlip 0 1 (pair x m) = pair x (m + x) := by
  funext i
  fin_cases i <;> rfl

lemma fun_const_eq (x : Fin 1 → Fin 2) : (fun _ : Fin 1 => x 0) = x := by
  funext i
  rw [Subsingleton.elim i 0]

/-- The coordinate of the slice, before the case split on the outcome. -/
lemma injectSlice_apply_eq (φ : QReg 1) (m : Fin 2) (ψ : QReg 1) (x : Fin 1 → Fin 2) :
    injectSlice φ m ψ x
      = Complex.I ^ ((m : ℕ) * (x 0 : ℕ)) * (ψ x * φ (fun _ => m + x 0)) := by
  rw [injectSlice_apply, sCorr]
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) m with rfl | rfl
  · rw [if_pos rfl]
    simp [cnotFlip_pair, fun_const_eq]
  · rw [if_neg (by decide)]
    simp [cnotFlip_pair, fun_const_eq]

/-! ### The injection identity -/

lemma conj_tPhase : conj tPhase = tPhaseInv := by
  rw [tPhase, tPhaseInv, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma norm_tPhase : ‖tPhase‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma fin_two_one_add_one : ((1 : Fin 2) + 1 : Fin 2) = 0 := rfl

lemma signChar_one : signChar 1 = -1 := rfl

/-- ★★ **The injection identity** (BACKLOG #66): with the magic state as resource, the data qubit
after outcome `m` and the correction `S^m` is `(1/√2) e^{imπ/4} · T ψ`. -/
theorem injectSlice_magicState (m : Fin 2) (ψ : QReg 1) :
    injectSlice magicState m ψ = ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ)) • tGate 0 ψ := by
  ext x
  rw [injectSlice_apply_eq, magicState_apply, PiLp.smul_apply, smul_eq_mul, tGate_apply]
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) m with rfl | rfl <;>
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (x 0) with h | h <;>
    simp only [h, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_zero, mul_one,
      one_mul, zero_add, add_zero, fin_two_one_add_one]
  · ring
  · ring
  · ring
  · linear_combination (ψ x * (Real.sqrt 2 : ℂ)⁻¹) * tPhase_sq.symm

theorem norm_tGate (ψ : QReg 1) : ‖tGate 0 ψ‖ = ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tGate_apply, norm_mul, norm_pow, norm_tPhase, one_pow, one_mul]

/-- Each outcome of the injection has probability `½`: `‖slice‖² = ‖ψ‖²/2`. -/
theorem norm_sq_injectSlice_magicState (m : Fin 2) (ψ : QReg 1) :
    ‖injectSlice magicState m ψ‖ ^ 2 = ‖ψ‖ ^ 2 / 2 := by
  rw [injectSlice_magicState, norm_smul, norm_tGate, mul_pow, norm_mul, norm_inv, norm_pow,
    norm_tPhase, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
  ring

/-! ### The error transfers -/

/-- `Z|A⟩`, the magic state with a phase-flip error. -/
noncomputable def zMagicState : QReg 1 := pauliOp 0 (unitV 0) magicState

lemma zMagicState_apply (z : Fin 1 → Fin 2) :
    zMagicState z = signChar (z 0) * ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ ((z 0 : Fin 2) : ℕ)) := by
  rw [zMagicState, pauliOp_apply, add_zero, magicState_apply, pauliSign, bdot_unitV]

/-- ★ **A `Z`-error on the resource becomes a `Z`-error on the output**: with `Z|A⟩` the circuit
yields `(1/√2)(−e^{iπ/4})^m · Z T ψ`. -/
theorem injectSlice_zMagicState (m : Fin 2) (ψ : QReg 1) :
    injectSlice zMagicState m ψ
      = ((Real.sqrt 2 : ℂ)⁻¹ * (-tPhase) ^ (m : ℕ)) • pauliOp 0 (unitV 0) (tGate 0 ψ) := by
  ext x
  rw [injectSlice_apply_eq, zMagicState_apply, PiLp.smul_apply, smul_eq_mul, pauliOp_apply,
    add_zero, pauliSign, bdot_unitV, tGate_apply]
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) m with rfl | rfl <;>
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (x 0) with h | h <;>
    simp only [h, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_zero, mul_one,
      one_mul, zero_add, add_zero, signChar_zero, signChar_one, fin_two_one_add_one]
  · ring
  · ring
  · ring
  · linear_combination (ψ x * (Real.sqrt 2 : ℂ)⁻¹) * tPhase_sq.symm

/-! ### The Kraus operators and the channel -/

/-- The `T` gate as a matrix on one qubit. -/
noncomputable def tMat : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  Matrix.diagonal fun z => tPhase ^ ((z 0 : Fin 2) : ℕ)

/-- The `Z` gate as a matrix on one qubit. -/
def zMat : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  Matrix.diagonal fun z => signChar (z 0)

/-- The Kraus operator of outcome `m` with resource `φ`: the matrix of `ψ ↦ injectSlice φ m ψ`,
i.e. `(S^m ⊗ ⟨m|) · CNOT · (1 ⊗ |φ⟩)`. -/
noncomputable def injectionKraus (φ : QReg 1) (m : Fin 2) :
    Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  Matrix.of fun x y => injectSlice φ m (basisState y) x

lemma tGate_basisState_apply (x y : Fin 1 → Fin 2) :
    tGate 0 (basisState y) x = tMat x y := by
  rw [tGate_apply, basisState_apply, tMat, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h
    simp
  · rw [if_neg h, if_neg h, mul_zero]

lemma injectionKraus_magicState (m : Fin 2) :
    injectionKraus magicState m = ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ)) • tMat := by
  ext x y
  rw [injectionKraus, Matrix.of_apply, injectSlice_magicState, PiLp.smul_apply, smul_eq_mul,
    tGate_basisState_apply, Matrix.smul_apply, smul_eq_mul]

lemma injectionKraus_zMagicState (m : Fin 2) :
    injectionKraus zMagicState m
      = ((Real.sqrt 2 : ℂ)⁻¹ * (-tPhase) ^ (m : ℕ)) • (zMat * tMat) := by
  ext x y
  rw [injectionKraus, Matrix.of_apply, injectSlice_zMagicState, PiLp.smul_apply, smul_eq_mul,
    pauliOp_apply, add_zero, pauliSign, bdot_unitV, tGate_basisState_apply, Matrix.smul_apply,
    smul_eq_mul, zMat, Matrix.diagonal_mul]

lemma tMat_conjTranspose_mul : tMatᴴ * tMat = 1 := by
  rw [tMat, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext z
  rw [Pi.star_apply, star_pow, Complex.star_def, conj_tPhase, ← mul_pow, tPhaseInv_mul, one_pow]

lemma zMat_conjTranspose_mul : zMatᴴ * zMat = 1 := by
  rw [zMat, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext z
  rw [Pi.star_apply, Complex.star_def, conj_signChar, signChar_mul_self]

lemma zMat_mul_tMat_conjTranspose_mul : (zMat * tMat)ᴴ * (zMat * tMat) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc zMatᴴ,
    zMat_conjTranspose_mul, Matrix.one_mul, tMat_conjTranspose_mul]

lemma conjTranspose_smul_mul_smul (c : ℂ) (A B : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) :
    (c • A)ᴴ * (c • B) = (conj c * c) • (Aᴴ * B) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def]

lemma smul_mul_mul_conjTranspose_smul (c : ℂ) (A ρ B : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) :
    (c • A) * ρ * (c • B)ᴴ = (c * conj c) • (A * ρ * Bᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_def]

lemma conj_coeff_mul (m : Fin 2) :
    conj ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ)) * ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ))
      = (2 : ℂ)⁻¹ := by
  rw [map_mul, map_inv₀, Complex.conj_ofReal, map_pow, conj_tPhase]
  calc (Real.sqrt 2 : ℂ)⁻¹ * tPhaseInv ^ (m : ℕ) * ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ))
      = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (tPhaseInv * tPhase) ^ (m : ℕ) := by
        rw [mul_pow]
        ring
    _ = (2 : ℂ)⁻¹ := by
        rw [tPhaseInv_mul, one_pow, mul_one, ← mul_inv, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (by norm_num)]
        norm_num

lemma conj_coeff_mul' (m : Fin 2) :
    conj ((Real.sqrt 2 : ℂ)⁻¹ * (-tPhase) ^ (m : ℕ))
      * ((Real.sqrt 2 : ℂ)⁻¹ * (-tPhase) ^ (m : ℕ)) = (2 : ℂ)⁻¹ := by
  have h := conj_coeff_mul m
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) m with rfl | rfl
  · simpa using h
  · simp only [Fin.isValue, Fin.val_one, pow_one] at h ⊢
    rw [mul_neg, map_neg, neg_mul_neg]
    exact h

lemma coeff_mul_conj (m : Fin 2) :
    ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ)) * conj ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ (m : ℕ))
      = (2 : ℂ)⁻¹ := by
  rw [mul_comm]
  exact conj_coeff_mul m

lemma coeff_mul_conj' (m : Fin 2) :
    ((Real.sqrt 2 : ℂ)⁻¹ * (-tPhase) ^ (m : ℕ))
      * conj ((Real.sqrt 2 : ℂ)⁻¹ * (-tPhase) ^ (m : ℕ)) = (2 : ℂ)⁻¹ := by
  rw [mul_comm]
  exact conj_coeff_mul' m

/-- The two Kraus operators of the magic-state circuit are trace-preserving. -/
lemma sum_kraus_magicState :
    ∑ m : Fin 2, (injectionKraus magicState m)ᴴ * injectionKraus magicState m = 1 := by
  simp only [injectionKraus_magicState, conjTranspose_smul_mul_smul, tMat_conjTranspose_mul,
    conj_coeff_mul, Fin.sum_univ_two, ← add_smul]
  norm_num

lemma sum_kraus_zMagicState :
    ∑ m : Fin 2, (injectionKraus zMagicState m)ᴴ * injectionKraus zMagicState m = 1 := by
  simp only [injectionKraus_zMagicState, conjTranspose_smul_mul_smul,
    zMat_mul_tMat_conjTranspose_mul, conj_coeff_mul', Fin.sum_univ_two, ← add_smul]
  norm_num

lemma sum_apply_magicState (ρ : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) :
    ∑ m : Fin 2, injectionKraus magicState m * ρ * (injectionKraus magicState m)ᴴ
      = tMat * ρ * tMatᴴ := by
  simp only [injectionKraus_magicState, smul_mul_mul_conjTranspose_smul, coeff_mul_conj,
    Fin.sum_univ_two, ← add_smul]
  norm_num

lemma sum_apply_zMagicState (ρ : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) :
    ∑ m : Fin 2, injectionKraus zMagicState m * ρ * (injectionKraus zMagicState m)ᴴ
      = (zMat * tMat) * ρ * (zMat * tMat)ᴴ := by
  simp only [injectionKraus_zMagicState, smul_mul_mul_conjTranspose_smul, coeff_mul_conj',
    Fin.sum_univ_two, ← add_smul]
  norm_num

/-- **The injection channel** on the data qubit: Kraus operators `(S^m ⊗ ⟨m|) · CNOT · (1 ⊗ |A⟩)`,
`m = 0, 1`. -/
noncomputable def injectionChannel : Channel (Fin 1 → Fin 2) (Fin 1 → Fin 2) (Fin 2) where
  kraus := injectionKraus magicState
  tp := sum_kraus_magicState

/-- ★★ **`T` enacted by injection** (BACKLOG #67, closes `R-006`): the outcome-averaged, corrected
channel of the gate-teleportation circuit with one magic state is exactly `ρ ↦ T ρ T†`. -/
theorem injectionChannel_apply (ρ : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) :
    injectionChannel.apply ρ = tMat * ρ * tMatᴴ := by
  rw [Channel.apply_def]
  exact sum_apply_magicState ρ

/-- **The noisy injection channel**: the resource is `(1 − p)|A⟩⟨A| + p Z|A⟩⟨A|Z`, so the Kraus
operators are `√(1 − p)` times those of `|A⟩` and `√p` times those of `Z|A⟩`. -/
noncomputable def noisyInjectionChannel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel (Fin 1 → Fin 2) (Fin 1 → Fin 2) (Fin 2 × Bool) where
  kraus := fun me => if me.2 then (Real.sqrt p : ℂ) • injectionKraus zMagicState me.1
    else (Real.sqrt (1 - p) : ℂ) • injectionKraus magicState me.1
  tp := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_true, if_false, conjTranspose_smul_mul_smul,
      Finset.sum_add_distrib, ← Finset.smul_sum, sum_kraus_magicState, sum_kraus_zMagicState,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hp,
      Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
    rw [← add_smul, ← Complex.ofReal_add, show p + (1 - p) = 1 by ring, Complex.ofReal_one,
      one_smul]

/-- ★ **A `Z`-error on the resource is a `Z`-error on the output**: the noisy injection channel is
`(1 − p) T ρ T† + p Z T ρ T† Z`. -/
theorem noisyInjectionChannel_apply {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) :
    (noisyInjectionChannel p hp hp1).apply ρ
      = ((1 - p : ℝ) : ℂ) • (tMat * ρ * tMatᴴ)
        + (p : ℂ) • ((zMat * tMat) * ρ * (zMat * tMat)ᴴ) := by
  rw [Channel.apply_def, Fintype.sum_prod_type]
  simp only [noisyInjectionChannel, Fintype.sum_bool, Bool.false_eq_true, if_true, if_false,
    smul_mul_mul_conjTranspose_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
    sum_apply_magicState, sum_apply_zMagicState, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hp, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
  rw [add_comm]

end QuantumInfo

end
