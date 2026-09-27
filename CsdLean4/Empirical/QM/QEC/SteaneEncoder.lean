/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneArbitrary
public import CsdLean4.Mathlib.QuantumInfo.BlockKron

/-!
# The Steane encoder, and the logical action of a one- or two-qubit operator

**Category:** 3-Local (Empirical, QM twin). BACKLOG #86, steps (c) and the crux of (d): what a
*concatenation* of the Steane code needs from level one.

`steaneEnc` is the encoder, the `128 × 2` matrix whose two columns are `|0̄⟩` and `|1̄⟩`. It is an
isometry (`steaneEnc_conjTranspose_mul`, from the orthonormality of the logical states) whose columns
are code states (`steaneProj_mul_steaneEnc`), so `KnillLaflamme.lean`'s encoder form applies: the
landed projector-form condition (`steane_knillLaflamme`) becomes
★ `steaneEnc_pauli_pair`, `steaneEncᴴ Eᵢᴴ Eⱼ steaneEnc = δᵢⱼ • 1`, **with no rank statement relating
`steaneEnc steaneEncᴴ` to `steaneProj`**.

The crux for the concatenation is that the *logical* action of an operator touching at most two
qubits is a scalar — distance three, read through the encoder:

* ★★ `steaneEnc_gateOf`: an arbitrary `2 × 2` operator on one qubit acts on the encoded qubit as the
  scalar `(G₀₀ + G₁₁)/2`. This is #61's span argument (`gateOf_eq_sum_pauliMat`) read through the
  encoder: the identity's Pauli coefficient survives, and every weight-one Pauli is detected;
* ★★ `exists_steaneEnc_gateOf_mul_gateOf`: two arbitrary operators on two qubits act as *some*
  scalar, because every product of two single-qubit Paulis is `±Eᵢᴴ Eⱼ` for two members of the error
  family (`exists_steaneEnc_pauli_mul`), and the family's Knill–Laflamme matrix is the identity;
* ★★ `exists_steaneEnc_blockKron`: the same statement for the tensor over blocks, in the shape the
  induction of #86 consumes — all blocks scalar except at most two named ones.

## Honest scope

⚠️ Two qubits is the limit, and it is the code's: a product of *three* single-qubit Paulis is not
`Eᵢᴴ Eⱼ` for the weight-one family, and indeed the logical action of a weight-three operator on the
Steane code need not be a scalar (the logical `X̄` has weight seven, `logicalX_steaneZero`).
⚠️ `exists_steaneEnc_gateOf_mul_gateOf` and `exists_steaneEnc_blockKron` give the scalar
existentially. The value is a product of the one-qubit scalars, but nothing downstream needs it: the
induction of #86 only needs that the logical action *is* a scalar.

## Source

A. Steane, *Error correcting codes in quantum theory*, PRL 77 (1996); E. Knill, R. Laflamme,
*Phys. Rev. A* 55 (1997) 900; M. Nielsen, I. Chuang, §10.6.1;
`Mathlib/QuantumInfo/KnillLaflamme.lean` (the encoder form), `Mathlib/QuantumInfo/BlockKron.lean`,
`Empirical/QM/QEC/SteaneArbitrary.lean` (#61, the span step); `specs/BACKLOG.md` #86;
`specs/steane-plan.md`; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo QuantumInfo.Controlled

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The encoder -/

/-- The **Steane encoder**: the isometry whose two columns are the logical states `|0̄⟩` and
`|1̄⟩`. -/
noncomputable def steaneEnc : Matrix (Fin 7 → Fin 2) (Fin 2) ℂ :=
  Matrix.of fun z a => if a = 0 then WithLp.ofLp steaneZero z else WithLp.ofLp steaneOne z

theorem steaneEnc_col_zero : (fun z => steaneEnc z 0) = WithLp.ofLp steaneZero := by
  funext z
  rw [steaneEnc, Matrix.of_apply, if_pos rfl]

theorem steaneEnc_col_one : (fun z => steaneEnc z 1) = WithLp.ofLp steaneOne := by
  funext z
  rw [steaneEnc, Matrix.of_apply, if_neg (by decide : ¬((1 : Fin 2) = 0))]

/-- The coordinate form of the inner product on the register. -/
theorem inner_eq_sum_star (ψ φ : QReg 7) :
    inner ℂ ψ φ = ∑ z, star (WithLp.ofLp ψ z) * WithLp.ofLp φ z := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun z _ => by rw [RCLike.inner_apply, Complex.star_def, mul_comm]

/-- ★ **The encoder is an isometry**: the logical states are orthonormal. -/
theorem steaneEnc_conjTranspose_mul : steaneEncᴴ * steaneEnc = 1 := by
  have hcol : ∀ a : Fin 2, (fun z => steaneEnc z a)
      = WithLp.ofLp (if a = 0 then steaneZero else steaneOne) := by
    intro a
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) a with ha | ha
    · rw [ha, if_pos rfl, steaneEnc_col_zero]
    · rw [ha, if_neg (by decide : ¬((1 : Fin 2) = 0)), steaneEnc_col_one]
  have hentry : ∀ a b : Fin 2, (steaneEncᴴ * steaneEnc) a b
      = inner ℂ (if a = 0 then steaneZero else steaneOne)
          (if b = 0 then steaneZero else steaneOne) := by
    intro a b
    rw [Matrix.mul_apply, inner_eq_sum_star]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Matrix.conjTranspose_apply, ← congrFun (hcol a) z, ← congrFun (hcol b) z]
  ext a b
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) a with ha | ha <;>
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) b with hb | hb <;>
    rw [hentry a b, ha, hb]
  · rw [if_pos rfl, inner_steaneZero_self, Matrix.one_apply_eq]
  · rw [if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0)), inner_steaneZero_steaneOne,
      Matrix.one_apply_ne (by decide : ¬((0 : Fin 2) = 1))]
  · rw [if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0)),
      Matrix.one_apply_ne (by decide : ¬((1 : Fin 2) = 0))]
    rw [← inner_conj_symm, inner_steaneZero_steaneOne, map_zero]
  · rw [if_neg (by decide : ¬((1 : Fin 2) = 0)), inner_steaneOne_self, Matrix.one_apply_eq]

/-- The columns of the encoder are code states. -/
theorem steaneProj_mul_steaneEnc : steaneProj * steaneEnc = steaneEnc := by
  ext z a
  have hcol : ∀ b : Fin 2, steaneProj *ᵥ (fun w => steaneEnc w b) = fun w => steaneEnc w b := by
    intro b
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) b with hb | hb
    · rw [hb, steaneEnc_col_zero, steaneProj_mulVec_steaneZero]
    · rw [hb, steaneEnc_col_one, steaneProj_mulVec_steaneOne]
  exact congrFun (hcol a) z

/-! ### The error family through the encoder -/

theorem steaneErr_none :
    pauliMat (errA none) (errB none) = (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) := by
  rw [show errA none = 0 from rfl, show errB none = 0 from rfl, pauliMat_zero]

/-- ★ **Knill–Laflamme in encoder form** for the single-qubit Paulis. -/
theorem steaneEnc_pauli_pair (i j : SingleErr) :
    steaneEncᴴ * (pauliMat (errA i) (errB i))ᴴ * pauliMat (errA j) (errB j) * steaneEnc
      = (1 : Matrix SingleErr SingleErr ℂ) i j • 1 :=
  encoder_of_knillLaflamme isCodeProjector_steaneProj steaneEnc_conjTranspose_mul
    steaneProj_mul_steaneEnc steane_knillLaflamme i j

/-- The logical action of a single error: the identity passes, every weight-one Pauli is detected. -/
theorem steaneEnc_pauli_single (j : SingleErr) :
    steaneEncᴴ * pauliMat (errA j) (errB j) * steaneEnc
      = (1 : Matrix SingleErr SingleErr ℂ) none j • 1 :=
  encoder_apply_of_eq_one isCodeProjector_steaneProj steaneEnc_conjTranspose_mul
    steaneProj_mul_steaneEnc steane_knillLaflamme steaneErr_none j

/-- A product of two single-qubit Paulis acts on the encoded qubit as a scalar: it is `±Eᵢᴴ Eⱼ`,
and the family's Knill–Laflamme matrix is the identity. -/
theorem exists_steaneEnc_pauli_mul (i j : SingleErr) :
    ∃ δ : ℂ, steaneEncᴴ * (pauliMat (errA i) (errB i) * pauliMat (errA j) (errB j)) * steaneEnc
      = δ • 1 := by
  have hE : pauliMat (errA i) (errB i)
      = pauliSign (errB i) (errA i) • (pauliMat (errA i) (errB i))ᴴ := by
    rw [pauliMat_conjTranspose, smul_smul, pauliSign_mul_self, one_smul]
  refine ⟨pauliSign (errB i) (errA i) * (1 : Matrix SingleErr SingleErr ℂ) i j, ?_⟩
  rw [hE, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, ← smul_smul, ← steaneEnc_pauli_pair i j]
  congr 1
  simp only [Matrix.mul_assoc]

/-! ### The logical action of an arbitrary operator on one or two qubits -/

/-- A finite sum of scalar multiples of the identity is one. -/
theorem exists_smul_one_of_forall {κ : Type*} [Fintype κ] {L : Type*} [DecidableEq L]
    (f : κ → Matrix L L ℂ) (h : ∀ i, ∃ γ : ℂ, f i = γ • 1) : ∃ γ : ℂ, ∑ i, f i = γ • 1 := by
  choose g hg using h
  exact ⟨∑ i, g i, by rw [Finset.sum_congr rfl fun i _ => hg i, ← Finset.sum_smul]⟩

/-- ★★ **The logical action of an arbitrary operator on one qubit is a scalar** — the trace
`(G₀₀ + G₁₁)/2`. The Paulis span the operators of a qubit (#61) and every weight-one Pauli is
detected, so only the identity's coefficient survives. -/
theorem steaneEnc_gateOf (b : Fin 7) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    steaneEncᴴ * gateOf b G * steaneEnc = ((G 0 0 + G 1 1) / 2) • 1 := by
  rw [gateOf_eq_sum_pauliMat b G]
  have hterm : ∀ i : SingleErr,
      steaneEncᴴ * (singleCoeff b G i • pauliMat (errA i) (errB i)) * steaneEnc
        = (singleCoeff b G i * (1 : Matrix SingleErr SingleErr ℂ) none i) • 1 := by
    intro i
    rw [Matrix.mul_smul, Matrix.smul_mul, steaneEnc_pauli_single i, smul_smul]
  rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_eq_single (none : SingleErr)]
  · rw [Matrix.one_apply_eq, mul_one]
    rfl
  · intro i _ hi
    rw [Matrix.one_apply_ne (Ne.symm hi), mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (none : SingleErr)) h

/-- ★★ **Two arbitrary operators on two qubits act as a scalar too** — distance three, in the form
the concatenation needs. -/
theorem exists_steaneEnc_gateOf_mul_gateOf (b₀ b₁ : Fin 7) (G₀ G₁ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ δ : ℂ, steaneEncᴴ * (gateOf b₀ G₀ * gateOf b₁ G₁) * steaneEnc = δ • 1 := by
  have hexp : gateOf b₀ G₀ * gateOf b₁ G₁
      = ∑ p : SingleErr × SingleErr,
          (singleCoeff b₀ G₀ p.1 * singleCoeff b₁ G₁ p.2) •
            (pauliMat (errA p.1) (errB p.1) * pauliMat (errA p.2) (errB p.2)) := by
    rw [gateOf_eq_sum_pauliMat b₀ G₀, gateOf_eq_sum_pauliMat b₁ G₁, Matrix.sum_mul,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hexp, Matrix.mul_sum, Matrix.sum_mul]
  refine exists_smul_one_of_forall _ fun p => ?_
  obtain ⟨δ, hδ⟩ := exists_steaneEnc_pauli_mul p.1 p.2
  refine ⟨singleCoeff b₀ G₀ p.1 * singleCoeff b₁ G₁ p.2 * δ, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, hδ, smul_smul]

/-- ★★ **The logical action of a tensor over blocks with at most two arbitrary slots is a
scalar.** The two named blocks may coincide, so this covers no arbitrary slot and one as well; it is
the shape the induction of #86 consumes, where the good blocks contribute scalars and at most two
blocks — one per error of the Knill–Laflamme pair — do not. -/
theorem exists_steaneEnc_blockKron (b₀ b₁ : Fin 7) (N : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ b, b ≠ b₀ → b ≠ b₁ → ∃ γ : ℂ, N b = γ • 1) :
    ∃ δ : ℂ, steaneEncᴴ * blockKron N * steaneEnc = δ • 1 := by
  have h' : ∀ b, ∃ (γ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      N b = γ • M ∧ (b ≠ b₀ → b ≠ b₁ → M = 1) := by
    intro b
    by_cases hb₀ : b = b₀
    · exact ⟨1, N b, (one_smul ℂ (N b)).symm, fun hc _ => absurd hb₀ hc⟩
    by_cases hb₁ : b = b₁
    · exact ⟨1, N b, (one_smul ℂ (N b)).symm, fun _ hc => absurd hb₁ hc⟩
    · obtain ⟨γ, hγ⟩ := h b hb₀ hb₁
      exact ⟨γ, 1, hγ, fun _ _ => rfl⟩
  choose γ M hNM hM1 using h'
  have hN : blockKron N = (∏ b, γ b) • blockKron M := by
    rw [show N = fun b => γ b • M b from funext hNM, blockKron_smul]
  by_cases hbb : b₀ = b₁
  · have hMeq : M = fun b => if b = b₀ then M b₀ else 1 := by
      funext b
      by_cases hb : b = b₀
      · rw [if_pos hb, hb]
      · rw [if_neg hb, hM1 b hb (by rw [← hbb]; exact hb)]
    have hg : blockKron M = gateOf b₀ (M b₀) := by
      conv_lhs => rw [hMeq]
      rw [blockKron_single_eq_gateOf]
    refine ⟨(∏ b, γ b) * ((M b₀ 0 0 + M b₀ 1 1) / 2), ?_⟩
    rw [hN, Matrix.mul_smul, Matrix.smul_mul, hg, steaneEnc_gateOf, smul_smul]
  · have hMeq : M = fun b =>
        (if b = b₀ then M b₀ else 1) * (if b = b₁ then M b₁ else 1) := by
      funext b
      by_cases hb₀ : b = b₀
      · rw [if_pos hb₀, if_neg (by rw [hb₀]; exact hbb), Matrix.mul_one, hb₀]
      · by_cases hb₁ : b = b₁
        · rw [if_neg hb₀, if_pos hb₁, Matrix.one_mul, hb₁]
        · rw [if_neg hb₀, if_neg hb₁, Matrix.one_mul, hM1 b hb₀ hb₁]
    obtain ⟨δ, hδ⟩ := exists_steaneEnc_gateOf_mul_gateOf b₀ b₁ (M b₀) (M b₁)
    refine ⟨(∏ b, γ b) * δ, ?_⟩
    rw [hN, Matrix.mul_smul, Matrix.smul_mul, hMeq, ← blockKron_mul, blockKron_single_eq_gateOf,
      blockKron_single_eq_gateOf, hδ, smul_smul]

end Steane
end QEC
end QM
end Empirical
end CSD
