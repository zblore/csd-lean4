/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Clifford
public import CsdLean4.Mathlib.QuantumInfo.AmplitudeAmplification

/-!
# The magic layer: the T gate escapes the Clifford closure (candidate 5)

**Category:** 1-Mathlib (CSD-free).

**Glossary:** https://glossary.constraintsurfacedynamics.com/magic-state/
Plain-language, CSD-role and formal statements of magic states, with this module as their
Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

The precise complement of the Gottesman–Knill mechanism (plan `specs/magic-plan.md`): GK-2
proved that H, S, CNOT conjugate every Pauli to a phase times a Pauli — the closure that
makes Clifford circuits classically trackable. This module proves the **boundary is real**:
the `T` gate (the π/8 gate) breaks it, which is why `T` is the standard route to universality
and why *magic states* are a resource.

* **The Clifford hierarchy, level by level:** `T² = S` (`tGate_tGate` — `T` sits one level
  above the Clifford group, its square descending into it), and ★ `tGate_conj_X`:
  `T X T† = (X + i·XZ)/√2` — conjugation by `T` carries the Pauli `X` **out of the Pauli
  family but into its Clifford-algebra span**: the level-3 hierarchy statement, as a closed
  operator identity.
* ★★ **The no-go** (`tGate_conj_X_not_pauli`): there are **no** `c, a, b` with
  `T X T† = c·X^a Z^b`. Together with GK-2 this brackets the Clifford group sharply: H, S,
  CNOT stay inside the Pauli-conjugation closure, `T` provably leaves it. The proof pins two
  coordinates and derives `1 = ±i` — a two-line arithmetic absurdity.
* **The magic state** `|T⟩ = T·H|0⟩` (`magicState`), coordinates `(1, e^{iπ/4})/√2`
  (`magicState_apply`), unit norm (`inner_magicState_self`) — the resource state whose
  consumption implements `T` by Clifford operations alone in the standard injection circuit.

**Honest scope.** This module formalises what magic **is** — the provable escape from the
Clifford closure and the resource state — not how it is **distilled**: the
Bravyi–Kitaev 15-to-1 protocol (and any distillation threshold claim) is a
program-verification-scale object, recorded as the named residue in the plan and not
attempted. No universality claim is made (that would need a gate-synthesis density theorem).
No priority claim of any kind (CL-061 rule).
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {n : ℕ}

/-! ## The T gate -/

/-- The T phase `e^{iπ/4}`. -/
noncomputable def tPhase : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The inverse T phase `e^{−iπ/4}`. -/
noncomputable def tPhaseInv : ℂ := Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I)

lemma tPhase_mul_inv : tPhase * tPhaseInv = 1 := by
  rw [tPhase, tPhaseInv, ← Complex.exp_add,
    show ((Real.pi / 4 : ℝ) : ℂ) * Complex.I + ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I = 0
      from by push_cast; ring, Complex.exp_zero]

lemma tPhaseInv_mul : tPhaseInv * tPhase = 1 := by
  rw [mul_comm]
  exact tPhase_mul_inv

/-- `T² = S` at the phase level: `(e^{iπ/4})² = i`. -/
lemma tPhase_sq : tPhase * tPhase = Complex.I := by
  rw [tPhase, ← Complex.exp_add,
    show ((Real.pi / 4 : ℝ) : ℂ) * Complex.I + ((Real.pi / 4 : ℝ) : ℂ) * Complex.I
        = (Real.pi : ℂ) / 2 * Complex.I from by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]

lemma tPhase_ne_zero : tPhase ≠ 0 := Complex.exp_ne_zero _

/-- `√2/2 = (√2)⁻¹`. -/
lemma sqrt_two_div_two : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  field_simp
  linarith [h22]

/-- The explicit value `e^{iπ/4} = (1 + i)/√2`. -/
lemma tPhase_eq : tPhase = (Real.sqrt 2 : ℂ)⁻¹ * (1 + Complex.I) := by
  rw [tPhase, exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four,
    sqrt_two_div_two]
  push_cast
  ring

/-- The explicit value `e^{−iπ/4} = (1 − i)/√2`. -/
lemma tPhaseInv_eq : tPhaseInv = (Real.sqrt 2 : ℂ)⁻¹ * (1 - Complex.I) := by
  rw [tPhaseInv, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four, sqrt_two_div_two]
  push_cast
  ring

/-- The **T gate** (π/8 gate) on qubit `j`: phase `e^{iπ/4}` on the `z_j = 1` branch. -/
noncomputable def tGate (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => tPhase ^ ((z j : Fin 2) : ℕ) * ψ z)

/-- The inverse T gate. -/
noncomputable def tGateInv (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => tPhaseInv ^ ((z j : Fin 2) : ℕ) * ψ z)

@[simp] lemma tGate_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    tGate j ψ z = tPhase ^ ((z j : Fin 2) : ℕ) * ψ z := rfl

@[simp] lemma tGateInv_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    tGateInv j ψ z = tPhaseInv ^ ((z j : Fin 2) : ℕ) * ψ z := rfl

lemma tGate_tGateInv (j : Fin n) (ψ : QReg n) : tGate j (tGateInv j ψ) = ψ := by
  ext z
  rw [tGate_apply, tGateInv_apply, ← mul_assoc, ← mul_pow, tPhase_mul_inv, one_pow, one_mul]

lemma tGateInv_tGate (j : Fin n) (ψ : QReg n) : tGateInv j (tGate j ψ) = ψ := by
  ext z
  rw [tGateInv_apply, tGate_apply, ← mul_assoc, ← mul_pow, tPhaseInv_mul, one_pow, one_mul]

/-- **The hierarchy descends:** `T² = S` — the square of the non-Clifford gate is
Clifford. -/
theorem tGate_tGate (j : Fin n) (ψ : QReg n) : tGate j (tGate j ψ) = sGate j ψ := by
  ext z
  rw [tGate_apply, tGate_apply, sGate_apply, ← mul_assoc, ← mul_pow, tPhase_sq]

/-! ## Conjugating `X`: out of the Pauli family, into its span -/

/-- The single-bit label at `j`. -/
def unitV (j : Fin n) : Fin n → Fin 2 := fun i => if i = j then 1 else 0

lemma unitV_apply_self (j : Fin n) : unitV j j = 1 := if_pos rfl

lemma bdot_unitV (j : Fin n) (w : Fin n → Fin 2) : bdot (unitV j) w = w j := by
  rw [bdot, Finset.sum_eq_single j
    (fun i _ hij => by rw [unitV, if_neg hij, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), unitV, if_pos rfl, one_mul]

/-- ★ **The level-3 hierarchy identity:** `T X T† = (X + i·XZ)/√2` — conjugation by `T`
carries the Pauli `X` out of the Pauli family, but only into its two-term Clifford-algebra
span. -/
theorem tGate_conj_X (j : Fin n) (ψ : QReg n) :
    tGate j (pauliOp (unitV j) 0 (tGateInv j ψ))
      = (Real.sqrt 2 : ℂ)⁻¹
          • (pauliOp (unitV j) 0 ψ + Complex.I • pauliOp (unitV j) (unitV j) ψ) := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_add, Pi.add_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, tGate_apply, pauliOp_apply,
    tGateInv_apply, pauliOp_apply, pauliOp_apply, pauliSign_zero_left, one_mul,
    pauliSign, bdot_unitV, Pi.add_apply z (unitV j) j, unitV_apply_self]
  generalize hu : z j = u
  generalize hX : ψ.ofLp (z + unitV j) = X
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) u with h | h <;> subst h
  · rw [show ((0 : Fin 2) + 1) = 1 from rfl, show signChar 1 = (-1 : ℂ) from rfl,
      show (((0 : Fin 2)) : ℕ) = 0 from rfl, show (((1 : Fin 2)) : ℕ) = 1 from rfl,
      pow_zero, pow_one, tPhaseInv_eq]
    ring
  · rw [show ((1 : Fin 2) + 1) = 0 from rfl, signChar_zero,
      show (((1 : Fin 2)) : ℕ) = 1 from rfl, show (((0 : Fin 2)) : ℕ) = 0 from rfl,
      pow_zero, pow_one, tPhase_eq]
    ring

/-- The T gate is homogeneous. -/
lemma tGate_smul (j : Fin n) (c : ℂ) (ψ : QReg n) :
    tGate j (c • ψ) = c • tGate j ψ := by
  ext z
  rw [tGate_apply, WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, tGate_apply]
  ring

/-- The T gate on a basis state: a pure phase. -/
lemma tGate_basisState (j : Fin n) (w : Fin n → Fin 2) :
    tGate j (basisState w) = tPhase ^ ((w j : Fin 2) : ℕ) • basisState w := by
  ext z
  rw [tGate_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply]
  by_cases hz : z = w
  · subst hz
    rfl
  · rw [if_neg hz, mul_zero, mul_zero]

/-- The inverse T gate on a basis state: a pure phase. -/
lemma tGateInv_basisState (j : Fin n) (w : Fin n → Fin 2) :
    tGateInv j (basisState w) = tPhaseInv ^ ((w j : Fin 2) : ℕ) • basisState w := by
  ext z
  rw [tGateInv_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply]
  by_cases hz : z = w
  · subst hz
    rfl
  · rw [if_neg hz, mul_zero, mul_zero]

/-- `T X T†` on a basis state, in closed form. -/
lemma tconjX_basisState (j : Fin n) (w : Fin n → Fin 2) :
    tGate j (pauliOp (unitV j) 0 (tGateInv j (basisState w)))
      = (tPhaseInv ^ ((w j : Fin 2) : ℕ)
          * tPhase ^ ((w j + 1 : Fin 2) : ℕ)) • basisState (w + unitV j) := by
  rw [tGateInv_basisState, pauliOp_smul, pauliOp_basisState, pauliSign_zero_left, one_smul,
    tGate_smul, tGate_basisState,
    show (w + unitV j) j = w j + 1 from by
      rw [Pi.add_apply, unitV_apply_self], smul_smul]

/-- ★★ **The no-go: `T` is not Clifford.** There are no `c, a, b` with
`T X T† = c · X^a Z^b` — the conjugation escape is genuine, not a phase artefact. Pinning
the two basis columns forces `1 = ±i`. -/
theorem tGate_conj_X_not_pauli :
    ¬ ∃ (c : ℂ) (a b : Fin 1 → Fin 2), ∀ ψ : QReg 1,
      tGate 0 (pauliOp (unitV 0) 0 (tGateInv 0 ψ)) = c • pauliOp a b ψ := by
  rintro ⟨c, a, b, h⟩
  have h0 := h (basisState (fun _ => 0))
  have h1 := h (basisState (fun _ => 1))
  rw [tconjX_basisState, pauliOp_basisState] at h0 h1
  have e0 := congrArg (fun v : QReg 1 => v ((fun _ => 0) + unitV 0)) h0
  have e1 := congrArg (fun v : QReg 1 => v ((fun _ => 1) + unitV 0)) h1
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply, if_true,
    show ((0 : Fin 2) + 1) = 1 from rfl, show ((1 : Fin 2) + 1) = 0 from rfl,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at e0 e1
  rcases (by decide : ∀ v : Fin 1 → Fin 2, v = (fun _ => 0) ∨ v = (fun _ => 1)) a
    with ha | ha <;> subst ha
  · -- `a = 0`: the target column is off the image — the coefficient must vanish
    rw [if_neg (by decide : ¬((fun _ => 0) + unitV 0 : Fin 1 → Fin 2)
        = (fun _ => 0) + (fun _ => 0)), mul_zero, mul_zero] at e0
    exact tPhase_ne_zero e0
  · -- `a = 1`: two phase equations combine to `1 = ±i`
    rw [if_pos (by decide : ((fun _ => 0) + unitV 0 : Fin 1 → Fin 2)
        = (fun _ => 0) + (fun _ => 1)), mul_one] at e0
    rw [if_pos (by decide : ((fun _ => 1) + unitV 0 : Fin 1 → Fin 2)
        = (fun _ => 1) + (fun _ => 1)), mul_one] at e1
    -- e0 : tPhase = c * pauliSign b (fun _ => 0); e1 : tPhaseInv = c * pauliSign b (fun _ => 1)
    rw [pauliSign, show bdot b (fun _ => 0) = 0 from by
        rw [bdot, Fin.sum_univ_one, mul_zero], signChar_zero, mul_one] at e0
    rw [pauliSign, show bdot b (fun _ => 1) = b 0 from by
        rw [bdot, Fin.sum_univ_one, mul_one]] at e1
    -- combine: I·χ(b0)² = (tPhase·χ(b0))·(tPhase·χ(b0)) ... derive 1 = ±i
    have hcomb : Complex.I = tPhase * tPhase := tPhase_sq.symm
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (b 0) with hb | hb <;> rw [hb] at e1
    · rw [signChar_zero, mul_one] at e1
      -- e0 : tPhase = c, e1 : tPhaseInv = c → I = tPhase² = tPhase·tPhaseInv = 1
      have : Complex.I = 1 := by
        rw [hcomb]
        nth_rewrite 2 [e0]
        rw [← e1, tPhase_mul_inv]
      have him := congrArg Complex.im this
      norm_num [Complex.I_im, Complex.one_im] at him
    · rw [show signChar 1 = (-1 : ℂ) from rfl, mul_neg_one] at e1
      -- e0 : tPhase = c, e1 : tPhaseInv = −c → I = tPhase² = −tPhase·tPhaseInv = −1
      have : Complex.I = -1 := by
        rw [hcomb]
        nth_rewrite 2 [e0]
        rw [show c = -tPhaseInv from by rw [e1, neg_neg], mul_neg, tPhase_mul_inv]
      have him := congrArg Complex.im this
      norm_num at him
  /-! ## The magic state -/

/-- The **magic state** `|T⟩ = T·H|0⟩` on one qubit. -/
noncomputable def magicState : QReg 1 :=
  tGate 0 (hGate 0 (basisState (fun _ => 0)))

/-- Coordinates: `|T⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2`. -/
lemma magicState_apply (z : Fin 1 → Fin 2) :
    magicState z = (Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ ((z 0 : Fin 2) : ℕ) := by
  rw [magicState, tGate_apply, hGate_apply, Fin.sum_univ_two]
  rw [show (Function.update z 0 0 : Fin 1 → Fin 2) = (fun _ => 0) from by
      funext i
      rw [Subsingleton.elim i 0, Function.update_self],
    show (Function.update z 0 1 : Fin 1 → Fin 2) = (fun _ => 1) from by
      funext i
      rw [Subsingleton.elim i 0, Function.update_self],
    basisState_apply, basisState_apply, if_pos rfl,
    if_neg (by intro hc; exact absurd (congrFun hc 0) (by decide))]
  simp only [mul_zero, mul_one, add_zero, signChar_zero]
  ring

/-- The magic state is a unit vector. -/
lemma inner_magicState_self : inner ℂ magicState magicState = 1 := by
  have hterm : ∀ z : Fin 1 → Fin 2,
      conj (magicState z) * magicState z = (2 : ℂ)⁻¹ := by
    intro z
    rw [magicState_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal,
      show conj tPhase = tPhaseInv from by
        rw [tPhase, tPhaseInv, ← Complex.exp_conj]
        congr 1
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring,
      show (Real.sqrt 2 : ℂ)⁻¹ * tPhaseInv ^ ((z 0 : Fin 2) : ℕ)
          * ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ ((z 0 : Fin 2) : ℕ))
        = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (tPhaseInv * tPhase)
            ^ ((z 0 : Fin 2) : ℕ) from by rw [mul_pow]; ring,
      tPhaseInv_mul, one_pow, mul_one, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply']
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end QuantumInfo
