/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.CliffordTUniversal
public import CsdLean4.Mathlib.QuantumInfo.SolovayKitaevCount

/-!
# Clifford+T synthesis with a gate count

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #309.

`CliffordTUniversal.lean` proves Clifford+T dense in `U(2ᵐ)` modulo phase, with no rate;
`SolovayKitaevCount.lean` gives words of length `K · log(1/ε)^c` on the determinant-one unitaries
(`su2Set`). This file composes them on `m` qubits.

* `gateOf_sub`, `gateOfLin`, ★ `exists_norm_gateOf_sub_le` — **lifting a single-qubit gate is
  bounded in the operator norm**, uniformly over the qubit (a linear map of finite-dimensional
  spaces; the constant `C` is not computed);
* `norm_mul_sub_mul_le_add` (errors add along a product of contractions), `norm_expI_smul`,
  `norm_le_one_of_mem_unitaryGroup`, `mem_unitaryGroup_of_mem_elementary`,
  `mem_unitaryGroup_of_mem_cliffordTGates`;
* `ctLetterCircuit`, `ctCircuit`, ★ `prod_ctCircuit`, `length_ctCircuit_le` — **a single-qubit
  word on qubit `j` is a Clifford+T circuit of at most seven gates a letter**, `T⁻¹` spelled as
  `T⁷`, so the circuit is over `H`, `T` and `CNOT` alone;
* ★ `exists_circuit_near_elementary`, ★ `exists_circuit_near_prod` — one elementary gate, and a
  product of `N` of them, after one phase, near a circuit: the errors add;
* ★★★ `exists_cliffordT_circuit_polylog` — **for every `m ≥ 1` there are `K`, `e` such that every
  unitary on `m` qubits, after one global phase, is within `ε ≤ e` of a Clifford+T circuit of at
  most `K · log(1/ε)^c` gates**, `c = skExponent ∈ (3, 4)`.

The route: `mem_prodLe_elementary` writes the unitary as an exact product of at most `elemCount m`
`CNOT`s and single-qubit gates (`306` on two qubits); each single-qubit factor is a phase times
a determinant-one unitary (Euler), approximated by #116's word at accuracy
`ε / ((elemCount m + 1) C)`; the phases collect into one. The logarithm of the finer accuracy is
at most twice `log(1/ε)` once `ε ≤ 1/((elemCount m + 1) C)`, so the exponent is #116's and only
`K` grows.

## Honest scope

⚠️ **`K` and `e` are existential.** #116's constants are (a net from compactness), and so is the
lift bound `C`. The exponent is quantitative; no constant is.
⚠️ **`K` grows with `m` through `elemCount m`**, which is exponential in `m` (`2ᵐ(2ᵐ − 1)/2`
two-level factors, and a control recursion of `3c + 14`). It is the count of this corpus's exact
decomposition, sufficient and not optimised; the statement is about the accuracy at fixed `m`.
⚠️ The exponent is #116's three-letter cost model; spelling `T⁻¹` as `T⁷` costs a factor `7` in `K`
and nothing in `c`. The literature's `3 + δ` stays unclaimed, and nothing is computed.
⚠️ The error is in the operator norm (`Matrix.Norms.L2Operator`), up to one global phase.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81;
M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information* §4.5 and Appendix 3;
`CliffordTUniversal.lean` (#73), `SolovayKitaevCount.lean` (#116), `ControlRecursion.lean` (#85),
`MultiControlled.lean` (#71), `Mathlib/LinearAlgebra/Matrix/TwoLevel.lean` (#70, #82);
`specs/BACKLOG.md` #309; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

open scoped Matrix.Norms.L2Operator

namespace QuantumInfo

namespace Controlled

open Euler TwoLevel

variable {m : ℕ}

/-! ### Lifting is bounded -/

theorem gateOf_sub (j : Fin m) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf j (A - B) = gateOf j A - gateOf j B := by
  rw [sub_eq_add_neg, gateOf_add, ← neg_one_smul ℂ B, gateOf_smul, neg_one_smul,
    ← sub_eq_add_neg]

/-- Lifting a single-qubit gate to `m` qubits, as a linear map. -/
noncomputable def gateOfLin (j : Fin m) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ where
  toFun := gateOf j
  map_add' := gateOf_add j
  map_smul' c M := gateOf_smul j c M

theorem gateOfLin_apply (j : Fin m) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    gateOfLin j M = gateOf j M := rfl

/-- ★ **Lifting a single-qubit gate is bounded in the operator norm, uniformly over the qubit**:
each lift is a linear map between finite-dimensional normed spaces. The constant is not computed. -/
theorem exists_norm_gateOf_sub_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (j : Fin m) (A B : Matrix (Fin 2) (Fin 2) ℂ),
      ‖gateOf j A - gateOf j B‖ ≤ C * ‖A - B‖ := by
  have hb : ∀ j : Fin m, ∃ c : ℝ, ∀ A : Matrix (Fin 2) (Fin 2) ℂ, ‖gateOf j A‖ ≤ c * ‖A‖ :=
    fun j => ⟨‖LinearMap.toContinuousLinearMap (gateOfLin j)‖, fun A => by
      simpa [gateOfLin_apply] using (LinearMap.toContinuousLinearMap (gateOfLin j)).le_opNorm A⟩
  choose c hc using hb
  have hsum : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  refine ⟨1 + ∑ j, |c j|, by linarith, fun j A B => ?_⟩
  rw [← gateOf_sub]
  have hcj : c j ≤ 1 + ∑ j, |c j| := by
    have h1 := Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg (c j))
      (Finset.mem_univ j)
    linarith [le_abs_self (c j)]
  exact (hc j (A - B)).trans (mul_le_mul_of_nonneg_right hcj (norm_nonneg _))

/-- **Errors add along a product of contractions.** -/
theorem norm_mul_sub_mul_le_add {E : Type*} [NormedRing E] {A B A' B' : E} (hB : ‖B‖ ≤ 1)
    (hA' : ‖A'‖ ≤ 1) : ‖A * B - A' * B'‖ ≤ ‖A - A'‖ + ‖B - B'‖ := by
  refine (CSD.SolovayKitaev.norm_mul_sub_mul_le' A B A' B').trans ?_
  have h1 := mul_le_mul_of_nonneg_left hB (norm_nonneg (A - A'))
  have h2 := mul_le_mul_of_nonneg_right hA' (norm_nonneg (B - B'))
  linarith

theorem norm_le_one_of_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim U 0, norm_zero]
    exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hU).le

theorem norm_expI_smul (φ : ℝ) {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ‖expI φ • A‖ = ‖A‖ := by
  rw [norm_smul, expI, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem mem_unitaryGroup_of_mem_elementary {g : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hg : g ∈ elementary m) : g ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  rcases hg with ⟨j, M, hM, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact gateOf_mem_unitaryGroup j hM
  · exact cnotGate'_mem_unitaryGroup a b hab

theorem mem_unitaryGroup_of_mem_cliffordTGates {g : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hg : g ∈ cliffordTGates m) : g ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  rcases hg with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact gateOf_mem_unitaryGroup j SU2.hGateM_mem_unitary
  · exact gateOf_mem_unitaryGroup j SU2.tGateM_mem_unitary
  · exact cnotGate'_mem_unitaryGroup a b hab

/-! ### A single-qubit word as a circuit -/

/-- The Clifford+T circuit of one letter of #117's alphabet on qubit `j`, with `T⁻¹ = T⁷` spelled
out as seven `T`s. -/
noncomputable def ctLetterCircuit (j : Fin m) (x : Fin 3) :
    List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :=
  ![[gateOf j CliffordT.hGateM], [gateOf j CliffordT.tGateM],
    List.replicate 7 (gateOf j CliffordT.tGateM)] x

/-- The Clifford+T circuit of a single-qubit word on qubit `j`. -/
noncomputable def ctCircuit (j : Fin m) (u : List (Fin 3)) :
    List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :=
  u.flatMap (ctLetterCircuit j)

theorem mem_cliffordTGates_of_mem_ctCircuit {j : Fin m} {u : List (Fin 3)}
    {g : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ} (hg : g ∈ ctCircuit j u) :
    g ∈ cliffordTGates m := by
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hg
  fin_cases x
  · have hx' : g = gateOf j CliffordT.hGateM := List.mem_singleton.mp hx
    exact Or.inl ⟨j, hx'⟩
  · have hx' : g = gateOf j CliffordT.tGateM := List.mem_singleton.mp hx
    exact Or.inr (Or.inl ⟨j, hx'⟩)
  · have hx' : g = gateOf j CliffordT.tGateM := List.eq_of_mem_replicate hx
    exact Or.inr (Or.inl ⟨j, hx'⟩)

theorem prod_ctLetterCircuit (j : Fin m) (x : Fin 3) :
    (ctLetterCircuit j x).prod = gateOf j (SU2.ctGen x) := by
  fin_cases x
  · show [gateOf j CliffordT.hGateM].prod = gateOf j CliffordT.hGateM
    rw [List.prod_singleton]
  · show [gateOf j CliffordT.tGateM].prod = gateOf j CliffordT.tGateM
    rw [List.prod_singleton]
  · show (List.replicate 7 (gateOf j CliffordT.tGateM)).prod = gateOf j (CliffordT.tGateM ^ 7)
    rw [List.prod_replicate]
    exact (map_pow (gateOfHom j) CliffordT.tGateM 7).symm

theorem length_ctLetterCircuit_le (j : Fin m) (x : Fin 3) : (ctLetterCircuit j x).length ≤ 7 := by
  fin_cases x
  · show [gateOf j CliffordT.hGateM].length ≤ 7
    simp
  · show [gateOf j CliffordT.tGateM].length ≤ 7
    simp
  · show (List.replicate 7 (gateOf j CliffordT.tGateM)).length ≤ 7
    simp

/-- ★ **A single-qubit word on qubit `j` is a Clifford+T circuit**, its value the lifted word. -/
theorem prod_ctCircuit (j : Fin m) (u : List (Fin 3)) :
    (ctCircuit j u).prod = gateOf j (SU2.ctEval u) := by
  induction u with
  | nil => simp [ctCircuit, gateOf_one]
  | cons x u ih =>
    simp only [ctCircuit] at ih ⊢
    rw [List.flatMap_cons, List.prod_append, prod_ctLetterCircuit, ih, SU2.ctEval_cons, gateOf_mul]

/-- … of at most seven gates a letter. -/
theorem length_ctCircuit_le (j : Fin m) (u : List (Fin 3)) :
    (ctCircuit j u).length ≤ 7 * u.length := by
  induction u with
  | nil => simp [ctCircuit]
  | cons x u ih =>
    simp only [ctCircuit] at ih ⊢
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have hx := length_ctLetterCircuit_le j x
    omega

/-! ### Approximating the exact product -/

section Approx

variable {K e C : ℝ}

/-- ★ **One elementary gate, after a phase, is within `C δ` of a Clifford+T circuit of at most
`7K log(1/δ)^c + 1` gates**, given a Solovay–Kitaev count `K log(1/δ)^c` on `su2Set` and a bound `C`
on the lift. A `CNOT` is its own circuit; a single-qubit gate is a phase times a determinant-one
unitary (Euler), which the word approximates. -/
theorem exists_circuit_near_elementary (hK : 0 < K)
    (hSK : ∀ ε : ℝ, 0 < ε → ε ≤ e → ∀ U ∈ SU2.su2Set, ∃ u : List (Fin 3),
      ‖U - SU2.ctEval u‖ ≤ ε ∧ (u.length : ℝ) ≤ K * (Real.log ε⁻¹) ^ SU2.skExponent)
    (hC0 : 0 ≤ C)
    (hC : ∀ (j : Fin m) (A B : Matrix (Fin 2) (Fin 2) ℂ), ‖gateOf j A - gateOf j B‖ ≤ C * ‖A - B‖)
    {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    {g : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ} (hg : g ∈ elementary m) :
    ∃ (φ : ℝ) (l : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)),
      (∀ x ∈ l, x ∈ cliffordTGates m) ∧
      (l.length : ℝ) ≤ 7 * K * (Real.log δ⁻¹) ^ SU2.skExponent + 1 ∧
      ‖expI φ • g - l.prod‖ ≤ C * δ := by
  have hlog : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ1)
  have hpow : 0 ≤ (Real.log δ⁻¹) ^ SU2.skExponent := Real.rpow_nonneg hlog _
  rcases hg with ⟨j, M, hM, rfl⟩ | ⟨a, b, hab, rfl⟩
  · obtain ⟨α, β, γ, δ', hM'⟩ := exists_euler hM
    have hV : rzMat β * ryMat γ * rzMat δ' ∈ SU2.su2Set :=
      ⟨mul_mem (mul_mem (rzMat_mem_unitaryGroup β) (ryMat_mem_unitaryGroup γ))
        (rzMat_mem_unitaryGroup δ'), rz_ry_rz_det β γ δ'⟩
    obtain ⟨u, hu, hlen⟩ := hSK δ hδ hδe _ hV
    refine ⟨-α, ctCircuit j u, fun x hx => mem_cliffordTGates_of_mem_ctCircuit hx, ?_, ?_⟩
    · have h7 : ((ctCircuit j u).length : ℝ) ≤ 7 * u.length := by
        exact_mod_cast length_ctCircuit_le j u
      nlinarith
    · rw [hM', ← gateOf_smul, smul_smul, ← expI_add, show -α + α = 0 by ring, expI_zero,
        one_smul, prod_ctCircuit]
      exact (hC j _ _).trans (mul_le_mul_of_nonneg_left hu hC0)
  · refine ⟨0, [cnotGate' a b], fun x hx => ?_, ?_, ?_⟩
    · rw [List.mem_singleton.mp hx]
      exact Or.inr (Or.inr ⟨a, b, hab, rfl⟩)
    · rw [List.length_singleton, Nat.cast_one]
      nlinarith [mul_nonneg hK.le hpow]
    · rw [expI_zero, one_smul, List.prod_singleton, sub_self, norm_zero]
      exact mul_nonneg hC0 hδ.le

/-- ★ **A product of elementary gates, after one phase, is within `N C δ` of a Clifford+T circuit
of at most `N (7K log(1/δ)^c + 1)` gates**, `N` the number of factors: the factors' errors add,
since every factor and every circuit is unitary. -/
theorem exists_circuit_near_prod (hK : 0 < K)
    (hSK : ∀ ε : ℝ, 0 < ε → ε ≤ e → ∀ U ∈ SU2.su2Set, ∃ u : List (Fin 3),
      ‖U - SU2.ctEval u‖ ≤ ε ∧ (u.length : ℝ) ≤ K * (Real.log ε⁻¹) ^ SU2.skExponent)
    (hC0 : 0 ≤ C)
    (hC : ∀ (j : Fin m) (A B : Matrix (Fin 2) (Fin 2) ℂ), ‖gateOf j A - gateOf j B‖ ≤ C * ‖A - B‖)
    {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (es : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)) (hes : ∀ g ∈ es, g ∈ elementary m) :
    ∃ (φ : ℝ) (l : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)),
      (∀ x ∈ l, x ∈ cliffordTGates m) ∧
      (l.length : ℝ) ≤ es.length * (7 * K * (Real.log δ⁻¹) ^ SU2.skExponent + 1) ∧
      ‖expI φ • es.prod - l.prod‖ ≤ es.length * (C * δ) := by
  induction es with
  | nil => exact ⟨0, [], by simp, by simp, by simp⟩
  | cons g es ih =>
    obtain ⟨φ₁, l₁, hl₁, hlen₁, hn₁⟩ :=
      exists_circuit_near_elementary hK hSK hC0 hC hδ hδe hδ1 (hes g (List.mem_cons_self ..))
    obtain ⟨φ₂, l₂, hl₂, hlen₂, hn₂⟩ := ih fun x hx => hes x (List.mem_cons_of_mem _ hx)
    refine ⟨φ₁ + φ₂, l₁ ++ l₂, fun x hx => ?_, ?_, ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact hl₁ x hx
      · exact hl₂ x hx
    · rw [List.length_append, List.length_cons]
      push_cast
      linarith
    · have hB : ‖expI φ₂ • es.prod‖ ≤ 1 := by
        rw [norm_expI_smul]
        exact norm_le_one_of_mem_unitaryGroup (unitaryGroup_list_prod_mem fun x hx =>
          mem_unitaryGroup_of_mem_elementary (hes x (List.mem_cons_of_mem _ hx)))
      have hA' : ‖l₁.prod‖ ≤ 1 := norm_le_one_of_mem_unitaryGroup
        (unitaryGroup_list_prod_mem fun x hx => mem_unitaryGroup_of_mem_cliffordTGates (hl₁ x hx))
      rw [List.prod_cons, List.prod_append, expI_add, smul_mul_smul_eq, List.length_cons]
      push_cast
      have h := norm_mul_sub_mul_le_add (A := expI φ₁ • g) (B' := l₂.prod) hB hA'
      linarith

end Approx

/-- ★★★ **Clifford+T synthesis with a gate count.** For every `m ≥ 1` there are `K` and `e` such
that every unitary on `m` qubits, after one global phase, is within `ε ≤ e` (operator norm) of a
Clifford+T circuit of at most `K · log(1/ε)^c` gates, `c = skExponent ∈ (3, 4)`. The exact product
of at most `elemCount m` elementary gates (`mem_prodLe_elementary`) is approximated factor by
factor, each single-qubit factor by #116's word at accuracy `ε / (elemCount m + 1) C`. -/
theorem exists_cliffordT_circuit_polylog (hm : 0 < m) :
    ∃ K e : ℝ, 0 < K ∧ 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e →
      ∀ U ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ,
        ∃ (φ : ℝ) (l : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)),
          (∀ g ∈ l, g ∈ cliffordTGates m) ∧
          (l.length : ℝ) ≤ K * (Real.log ε⁻¹) ^ SU2.skExponent ∧
          ‖expI φ • U - l.prod‖ ≤ ε := by
  obtain ⟨K₀, e₀, hK₀, he₀, hSK⟩ := SU2.exists_word_approx_polylog
  obtain ⟨C, hC1, hC⟩ := exists_norm_gateOf_sub_le (m := m)
  set E : ℝ := (elemCount m : ℝ) + 1 with hE
  have hE1 : 1 ≤ E := by rw [hE]; linarith [Nat.cast_nonneg (α := ℝ) (elemCount m)]
  have hEC : 1 ≤ E * C := one_le_mul_of_one_le_of_one_le hE1 hC1
  have hECpos : 0 < E * C := by linarith
  have hc0 : 0 ≤ SU2.skExponent := SU2.skExponent_pos.le
  have hexp1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  refine ⟨E * (7 * K₀ * 2 ^ SU2.skExponent + 1), min e₀ (min (E * C)⁻¹ (Real.exp (-1))),
    by positivity, lt_min he₀ (lt_min (inv_pos.mpr hECpos) (Real.exp_pos _)),
    fun ε hε hεe U hU => ?_⟩
  have hεe₀ : ε ≤ e₀ := hεe.trans (min_le_left _ _)
  have hεEC : ε ≤ (E * C)⁻¹ := hεe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεexp : ε ≤ Real.exp (-1) := hεe.trans ((min_le_right _ _).trans (min_le_right _ _))
  set δ : ℝ := ε / (E * C) with hδdef
  have hδ : 0 < δ := div_pos hε hECpos
  have hδε : δ ≤ ε := div_le_self hε.le hEC
  obtain ⟨es, hes_len, hes, rfl⟩ := mem_prodLe_elementary hm hU
  obtain ⟨φ, l, hl, hlen, hnorm⟩ := exists_circuit_near_prod hK₀ hSK (by linarith) hC hδ
    (hδε.trans hεe₀) (hδε.trans (hεexp.trans hexp1)) es hes
  have hN : (es.length : ℝ) ≤ E := by
    rw [hE]
    have : (es.length : ℝ) ≤ elemCount m := by exact_mod_cast hes_len
    linarith
  refine ⟨φ, l, hl, ?_, ?_⟩
  · -- the logarithms: `log(1/δ) ≤ 2 log(1/ε)` and `1 ≤ log(1/ε)`
    have hlogε : 1 ≤ Real.log ε⁻¹ := by
      have h := Real.log_le_log hε hεexp
      rw [Real.log_exp] at h
      rw [Real.log_inv]
      linarith
    have hECε : E * C ≤ ε⁻¹ := (le_inv_comm₀ hECpos hε).mpr hεEC
    have hlogEC : Real.log (E * C) ≤ Real.log ε⁻¹ := Real.log_le_log hECpos hECε
    have hlogδ : Real.log δ⁻¹ = Real.log (E * C) + Real.log ε⁻¹ := by
      rw [hδdef, inv_div, Real.log_div hECpos.ne' hε.ne', Real.log_inv, sub_eq_add_neg]
    have hlogδ0 : 0 ≤ Real.log δ⁻¹ := by
      rw [hlogδ]
      linarith [Real.log_nonneg hEC]
    have hpowδ : (Real.log δ⁻¹) ^ SU2.skExponent
        ≤ 2 ^ SU2.skExponent * (Real.log ε⁻¹) ^ SU2.skExponent := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow hlogδ0 (by rw [hlogδ]; linarith) hc0
    have hone : 1 ≤ (Real.log ε⁻¹) ^ SU2.skExponent := Real.one_le_rpow hlogε hc0
    have hX : 7 * K₀ * (Real.log δ⁻¹) ^ SU2.skExponent + 1
        ≤ (7 * K₀ * 2 ^ SU2.skExponent + 1) * (Real.log ε⁻¹) ^ SU2.skExponent := by
      have := mul_le_mul_of_nonneg_left hpowδ (by positivity : (0 : ℝ) ≤ 7 * K₀)
      nlinarith
    have hX0 : 0 ≤ 7 * K₀ * (Real.log δ⁻¹) ^ SU2.skExponent + 1 := by
      have := Real.rpow_nonneg hlogδ0 SU2.skExponent
      positivity
    calc (l.length : ℝ) ≤ es.length * (7 * K₀ * (Real.log δ⁻¹) ^ SU2.skExponent + 1) := hlen
      _ ≤ E * ((7 * K₀ * 2 ^ SU2.skExponent + 1) * (Real.log ε⁻¹) ^ SU2.skExponent) :=
          mul_le_mul hN hX hX0 (by linarith)
      _ = E * (7 * K₀ * 2 ^ SU2.skExponent + 1) * (Real.log ε⁻¹) ^ SU2.skExponent := by ring
  · calc ‖expI φ • es.prod - l.prod‖ ≤ es.length * (C * δ) := hnorm
      _ ≤ E * (C * δ) := mul_le_mul_of_nonneg_right hN (mul_nonneg (by linarith) hδ.le)
      _ = ε := by rw [hδdef]; field_simp

end Controlled

end QuantumInfo
