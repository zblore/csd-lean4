/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderBand
public import CsdLean4.RecordLayer.TransponderDetuned

/-!
# The transponder with a band, in contact: each mode of the band turns on its own

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2) for the transponder of
UA-21; second brick on it).

With the band of UA-21 the level swap does not commute with the transponder's Hamiltonian,
so the solved orbits of `RecordLayer/TransponderRabi.lean` and
`RecordLayer/TransponderDetuned.lean` do not apply. They apply one mode at a time. The swap
is the identity on the sites, so for an eigenvector `u` of the second level's Hamiltonian
`H₁`, with eigenvalue `E₁`, the two states "`u` in the first level" and "`u` in the second"
span a plane that the transponder's Hamiltonian with the swap keeps. On that plane it is the
transponder with two level energies `E₀`, `E₁` and no hopping, which is solved.

Here the contact term is **not gated**: the swap acts everywhere, and there is no messenger.

* `exp_mulVec_eq_of_agree_on_pair`, `exp_smul_mulVec_eq_of_agree_on_pair` — two generators
  that agree on a plane kept by one of them have the same exponential on it;
* `levelSwap_mulVec_inLevel_one`, `levelProj_mulVec_inLevel_same`,
  `levelProj_mulVec_inLevel_of_ne`, `blockDiagonal_smul_one_mulVec_inLevel`,
  `detunedAxis_mulVec_inLevel_zero`;
* ★ `exp_levels_swap_mulVec_inLevel_zero` — the transponder with no hopping and the swap, on
  a first-level state, in closed form;
* ★★★ `exp_bandContact_mulVec_inLevel_zero` — **an eigenvector `u` of the band, placed in the
  first level, turns into the second at its own rate**: with `Ω² = g² + ((E₁ − E₀)/2)²`, the
  orbit is `e^{−i(E₀+E₁)s/2} ((cos Ωs + i (δ/Ω) sin Ωs) u₀ − i (g/Ω) sin Ωs · u₁)`;
* `levelProj_one_mulVec_exp_bandContact`, ★★★ `sum_norm_sq_levelProj_one_exp_bandContact` —
  **the second level then holds exactly `(g/Ω)² sin² (Ωs)` of the mode's weight**;
* ★★ `levelProj_one_mulVec_exp_bandContact_sum` — **for a sum of modes the launched wave
  function is the same sum with each amplitude multiplied by its own
  `−i e^{−i(E₀+E_m)s/2} (g/Ω_m) sin (Ω_m s)`**.

## Honest scope

⚠️ **No gate and no messenger.** The swap term acts at all times and at every site. That the
gated term of UA-19 (b) does the same while the carriers are in contact is not shown here.
So no launch by a meeting is shown.

⚠️ **Mode by mode.** The weight of the launched sum is not computed: that needs the modes'
orthogonality, and a bound for it needs the spread of the detunings `(E_m − E₀)/2` over the
packet's window.

⚠️ **`Ω > 0` is a hypothesis** for each mode: it fails only when `g = 0` and `E₁ = E₀`.

⚠️ **Flow times.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UA-21,
UO-26, UD-262, UD-265, UD-266; §9.4); `RecordLayer/TransponderBand.lean` (`bandBlocks`,
`inLevel`); `RecordLayer/TransponderDetuned.lean` (`detunedAxis`, `detunedAxis_mul_self`,
`blockDiagonal_smul_one_eq_add`); `RecordLayer/TransponderRabi.lean`
(`exp_neg_I_add_smul_of_commute_invol`); `RecordLayer/TransponderAtRest.lean`
(`exp_mulVec_stationary`); `RecordLayer/DiracArrival.lean` (`exp_mulVec_of_mulVec_eq_smul`,
whose proof the first lemma follows); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### Two generators that agree on a plane -/

section Agree

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Two generators that agree on a plane kept by one of them have the same exponential on
it.** `A` and `A'` agree on `v₀` and `v₁`, and `A'` maps each into their span. -/
theorem exp_mulVec_eq_of_agree_on_pair {A A' : Matrix m m ℂ} {v₀ v₁ : m → ℂ} {a b c d : ℂ}
    (h₀ : A *ᵥ v₀ = A' *ᵥ v₀) (h₁ : A *ᵥ v₁ = A' *ᵥ v₁)
    (i₀ : A' *ᵥ v₀ = a • v₀ + b • v₁) (i₁ : A' *ᵥ v₁ = c • v₀ + d • v₁) :
    exp A *ᵥ v₀ = exp A' *ᵥ v₀ := by
  have hpow : ∀ k : ℕ, (A ^ k) *ᵥ v₀ = (A' ^ k) *ᵥ v₀ ∧ (A ^ k) *ᵥ v₁ = (A' ^ k) *ᵥ v₁ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      constructor
      · rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h₀, i₀]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ih.1, ih.2]
      · rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h₁, i₁]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ih.1, ih.2]
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hA' := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A'
  let G : Matrix m m ℂ →+ (m → ℂ) :=
    { toFun := fun M => M *ᵥ v₀
      map_zero' := Matrix.zero_mulVec v₀
      map_add' := fun M N => Matrix.add_mulVec M N v₀ }
  have hG : Continuous G := Continuous.matrix_mulVec continuous_id continuous_const
  refine (hA.map G hG).unique ?_
  convert hA'.map G hG using 1
  funext k
  simp only [Function.comp_apply, G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mulVec,
    (hpow k).1]

/-- The same for a multiple of the two generators. -/
theorem exp_smul_mulVec_eq_of_agree_on_pair (z : ℂ) {A A' : Matrix m m ℂ} {v₀ v₁ : m → ℂ}
    {a b c d : ℂ} (h₀ : A *ᵥ v₀ = A' *ᵥ v₀) (h₁ : A *ᵥ v₁ = A' *ᵥ v₁)
    (i₀ : A' *ᵥ v₀ = a • v₀ + b • v₁) (i₁ : A' *ᵥ v₁ = c • v₀ + d • v₁) :
    exp (z • A) *ᵥ v₀ = exp (z • A') *ᵥ v₀ := by
  refine exp_mulVec_eq_of_agree_on_pair (v₁ := v₁) (a := z * a) (b := z * b) (c := z * c)
    (d := z * d) ?_ ?_ ?_ ?_
  · rw [Matrix.smul_mulVec, Matrix.smul_mulVec, h₀]
  · rw [Matrix.smul_mulVec, Matrix.smul_mulVec, h₁]
  · rw [Matrix.smul_mulVec, i₀, smul_add, smul_smul, smul_smul]
  · rw [Matrix.smul_mulVec, i₁, smul_add, smul_smul, smul_smul]

end Agree

/-! ### The level operators on a state in one level -/

section Levels

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The swap takes a second-level state to the same wave function in the first level. -/
theorem levelSwap_mulVec_inLevel_one (χ : n → ℂ) :
    levelSwap n *ᵥ inLevel 1 χ = inLevel 0 χ := by
  funext ⟨p, k⟩
  fin_cases k
  · show (levelSwap n *ᵥ inLevel 1 χ) (p, 0) = inLevel 0 χ (p, 0)
    rw [levelSwap_mulVec_zero]
    simp [inLevel]
  · show (levelSwap n *ᵥ inLevel 1 χ) (p, 1) = inLevel 0 χ (p, 1)
    rw [levelSwap_mulVec_one]
    simp [inLevel]

/-- A level's projector fixes a state in that level. -/
theorem levelProj_mulVec_inLevel_same (l : Fin 2) (χ : n → ℂ) :
    levelProj n l *ᵥ inLevel l χ = inLevel l χ := by
  funext q
  rw [levelProj, Matrix.mulVec_diagonal]
  by_cases hq : q.2 = l <;> simp [inLevel, hq]

/-- A level's projector annihilates a state in the other level. -/
theorem levelProj_mulVec_inLevel_of_ne {l k : Fin 2} (h : l ≠ k) (χ : n → ℂ) :
    levelProj n l *ᵥ inLevel k χ = 0 := by
  funext q
  rw [levelProj, Matrix.mulVec_diagonal]
  by_cases hq : q.2 = l
  · simp [inLevel, hq, h]
  · simp [hq]

/-- Level energies with no hopping act on a state in one level by that level's energy. -/
theorem blockDiagonal_smul_one_mulVec_inLevel (E : Fin 2 → ℝ) (l : Fin 2) (χ : n → ℂ) :
    Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        *ᵥ inLevel l χ
      = ((E l : ℝ) : ℂ) • inLevel l χ := by
  rw [blockDiagonal_mulVec_inLevel]
  show inLevel l ((((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, inLevel_smul]

/-- The axis of the detuned contact term on a first-level state. -/
theorem detunedAxis_mulVec_inLevel_zero (a b : ℝ) (χ : n → ℂ) :
    detunedAxis n a b *ᵥ inLevel 0 χ = (-(a : ℂ)) • inLevel 0 χ + (b : ℂ) • inLevel 1 χ := by
  rw [detunedAxis, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, levelProj_mulVec_inLevel_of_ne (l := 1) (k := 0) (by decide) χ,
    levelProj_mulVec_inLevel_same, levelSwap_mulVec_inLevel_zero, zero_sub, smul_neg,
    neg_smul]

/-- ★ **Two level energies, no hopping, and the swap, on a first-level state.** With
`Ω² = g² + ((E 1 − E 0)/2)²`, `Ω > 0`: the orbit of `χ` in the first level is
`e^{−i(E₀+E₁)s/2} ((cos Ωs + i (δ/Ω) sin Ωs) χ₀ − i (g/Ω) sin Ωs · χ₁)`, `δ = (E₁ − E₀)/2`. -/
theorem exp_levels_swap_mulVec_inLevel_zero (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2) (χ : n → ℂ) (s : ℝ) :
    exp (s • ((-Complex.I) • (Matrix.blockDiagonal
            (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
          + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 χ
      = Complex.exp (-(Complex.I * (((E 0 + E 1) / 2 : ℝ) : ℂ)) * s)
        • ((Complex.cos ((Ω * s : ℝ) : ℂ)
              + Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)
                * (((E 1 - E 0) / 2 / Ω : ℝ) : ℂ)) • inLevel 0 χ
          - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ) * ((g / Ω : ℝ) : ℂ))
            • inLevel 1 χ) := by
  have hab : ((E 1 - E 0) / 2 / Ω) ^ 2 + (g / Ω) ^ 2 = 1 := by
    calc ((E 1 - E 0) / 2 / Ω) ^ 2 + (g / Ω) ^ 2
        = (g ^ 2 + ((E 1 - E 0) / 2) ^ 2) / Ω ^ 2 := by ring
      _ = 1 := by rw [← hΩ2, div_self (pow_ne_zero 2 hΩ.ne')]
  have hWW : detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω)
      * detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω) = 1 := by
    rw [detunedAxis_mul_self, hab, Complex.ofReal_one, one_smul]
  have hWH := detunedAxis_mul_blockDiagonal_smul_one (n := n) ((E 1 - E 0) / 2 / Ω) (g / Ω)
    ((E 0 + E 1) / 2)
  have e1r : Ω * ((E 1 - E 0) / 2 / Ω) = (E 1 - E 0) / 2 := by
    field_simp
  have e2r : Ω * (g / Ω) = g := by
    field_simp
  have hsum : Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n
      = Matrix.blockDiagonal
          (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (Ω : ℂ) • detunedAxis n ((E 1 - E 0) / 2 / Ω) (g / Ω) := by
    rw [blockDiagonal_smul_one_eq_add E, detunedAxis]
    simp only [smul_add, smul_smul, ← Complex.ofReal_mul, e1r, e2r]
    rw [add_assoc]
  have hHm : ∀ l : Fin 2, Matrix.blockDiagonal
        (fun _ : Fin 2 => (((E 0 + E 1) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ inLevel l χ
      = (((E 0 + E 1) / 2 : ℝ) : ℂ) • inLevel l χ := fun l =>
    blockDiagonal_smul_one_mulVec_inLevel (fun _ => (E 0 + E 1) / 2) l χ
  rw [hsum, exp_neg_I_add_smul_of_commute_invol hWH hWW Ω s, ← Matrix.mulVec_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    detunedAxis_mulVec_inLevel_zero]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_add]
  rw [exp_mulVec_stationary (hHm 0) s, exp_mulVec_stationary (hHm 1) s]
  module

/-- ★★★ **A mode of the band, placed in the first level, turns into the second at its own
rate.** The transponder of UA-21 with any second-level Hamiltonian `H₁`, and the swap term
`g X` with no gate. For an eigenvector `u` of `H₁` with the real eigenvalue `E₁`, and `Ω > 0`
with `Ω² = g² + ((E₁ − E₀)/2)²`, the orbit of "`u` in the first level" is
`e^{−i(E₀+E₁)s/2} ((cos Ωs + i (δ/Ω) sin Ωs) u₀ − i (g/Ω) sin Ωs · u₁)`, `δ = (E₁ − E₀)/2`. -/
theorem exp_bandContact_mulVec_inLevel_zero (E₀ : ℝ) {H₁ : Matrix n n ℂ} {u : n → ℂ}
    {E₁ : ℝ} (hu : H₁ *ᵥ u = (E₁ : ℂ) • u) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E₁ - E₀) / 2) ^ 2) (s : ℝ) :
    exp (s • ((-Complex.I) • (Matrix.blockDiagonal (bandBlocks E₀ H₁)
          + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 u
      = Complex.exp (-(Complex.I * (((E₀ + E₁) / 2 : ℝ) : ℂ)) * s)
        • ((Complex.cos ((Ω * s : ℝ) : ℂ)
              + Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ)
                * (((E₁ - E₀) / 2 / Ω : ℝ) : ℂ)) • inLevel 0 u
          - (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ) * ((g / Ω : ℝ) : ℂ))
            • inLevel 1 u) := by
  obtain ⟨E, hE0, hE1⟩ : ∃ E : Fin 2 → ℝ, E 0 = E₀ ∧ E 1 = E₁ := ⟨![E₀, E₁], rfl, rfl⟩
  subst hE0 hE1
  have e : ∀ M : Matrix (n × Fin 2) (n × Fin 2) ℂ,
      s • ((-Complex.I) • M) = (((s : ℝ) : ℂ) * (-Complex.I)) • M := fun M => by
    rw [← smul_assoc, Complex.real_smul]
  have hb0 : Matrix.blockDiagonal (bandBlocks (E 0) H₁) *ᵥ inLevel 0 u
      = ((E 0 : ℝ) : ℂ) • inLevel 0 u := by
    rw [blockDiagonal_mulVec_inLevel]
    show inLevel 0 ((((E 0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ u) = _
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, inLevel_smul]
  have hb1 : Matrix.blockDiagonal (bandBlocks (E 0) H₁) *ᵥ inLevel 1 u
      = ((E 1 : ℝ) : ℂ) • inLevel 1 u := by
    rw [blockDiagonal_mulVec_inLevel]
    show inLevel 1 (H₁ *ᵥ u) = _
    rw [hu, inLevel_smul]
  have hf0 := blockDiagonal_smul_one_mulVec_inLevel E 0 u
  have hf1 := blockDiagonal_smul_one_mulVec_inLevel E 1 u
  have h₀ : (Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n)
        *ᵥ inLevel 0 u
      = (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n) *ᵥ inLevel 0 u := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, hb0, hf0]
  have h₁ : (Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n)
        *ᵥ inLevel 1 u
      = (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n) *ᵥ inLevel 1 u := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, hb1, hf1]
  have i₀ : (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n) *ᵥ inLevel 0 u
      = ((E 0 : ℝ) : ℂ) • inLevel 0 u + (g : ℂ) • inLevel 1 u := by
    rw [Matrix.add_mulVec, hf0, Matrix.smul_mulVec, levelSwap_mulVec_inLevel_zero]
  have i₁ : (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n) *ᵥ inLevel 1 u
      = (g : ℂ) • inLevel 0 u + ((E 1 : ℝ) : ℂ) • inLevel 1 u := by
    rw [Matrix.add_mulVec, hf1, Matrix.smul_mulVec, levelSwap_mulVec_inLevel_one, add_comm]
  rw [e, exp_smul_mulVec_eq_of_agree_on_pair _ h₀ h₁ i₀ i₁, ← e]
  exact exp_levels_swap_mulVec_inLevel_zero E g hΩ hΩ2 u s

/-- The second-level part of that orbit. -/
theorem levelProj_one_mulVec_exp_bandContact (E₀ : ℝ) {H₁ : Matrix n n ℂ} {u : n → ℂ}
    {E₁ : ℝ} (hu : H₁ *ᵥ u = (E₁ : ℂ) • u) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E₁ - E₀) / 2) ^ 2) (s : ℝ) :
    levelProj n 1 *ᵥ (exp (s • ((-Complex.I) • (Matrix.blockDiagonal (bandBlocks E₀ H₁)
          + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 u)
      = (-(Complex.exp (-(Complex.I * (((E₀ + E₁) / 2 : ℝ) : ℂ)) * s)
          * (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ) * ((g / Ω : ℝ) : ℂ))))
        • inLevel 1 u := by
  rw [exp_bandContact_mulVec_inLevel_zero E₀ hu g hΩ hΩ2 s, Matrix.mulVec_smul,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    levelProj_mulVec_inLevel_of_ne (l := 1) (k := 0) (by decide) u,
    levelProj_mulVec_inLevel_same, smul_zero, zero_sub, smul_neg, smul_smul, neg_smul]

/-- ★★★ **The second level holds exactly `(g/Ω)² sin² (Ωs)` of the mode's weight.** -/
theorem sum_norm_sq_levelProj_one_exp_bandContact (E₀ : ℝ) {H₁ : Matrix n n ℂ}
    {u : n → ℂ} {E₁ : ℝ} (hu : H₁ *ᵥ u = (E₁ : ℂ) • u) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E₁ - E₀) / 2) ^ 2) (s : ℝ) :
    ∑ q, ‖(levelProj n 1 *ᵥ (exp (s • ((-Complex.I)
          • (Matrix.blockDiagonal (bandBlocks E₀ H₁) + (g : ℂ) • levelSwap n)))
        *ᵥ inLevel 0 u)) q‖ ^ 2
      = (g / Ω) ^ 2 * Real.sin (Ω * s) ^ 2 * ∑ p, ‖u p‖ ^ 2 := by
  have hre : (-(Complex.I * (((E₀ + E₁) / 2 : ℝ) : ℂ)) * (s : ℂ)).re = 0 := by simp
  have hc : ‖-(Complex.exp (-(Complex.I * (((E₀ + E₁) / 2 : ℝ) : ℂ)) * s)
        * (Complex.I * Complex.sin ((Ω * s : ℝ) : ℂ) * ((g / Ω : ℝ) : ℂ)))‖
      = |Real.sin (Ω * s)| * |g / Ω| := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_exp, hre, Real.exp_zero,
      Complex.norm_I, ← Complex.ofReal_sin, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, one_mul, one_mul]
  rw [levelProj_one_mulVec_exp_bandContact E₀ hu g hΩ hΩ2 s]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, sum_norm_sq_inLevel, hc, mul_pow, sq_abs, sq_abs]
  ring

/-- ★★ **The launched wave function of a sum of modes.** Each mode's amplitude is multiplied
by its own factor `−i e^{−i(E₀+E_m)s/2} (g/Ω_m) sin (Ω_m s)`. -/
theorem levelProj_one_mulVec_exp_bandContact_sum {ι : Type*} (W : Finset ι) (E₀ : ℝ)
    {H₁ : Matrix n n ℂ} (u : ι → n → ℂ) (a : ι → ℂ) (E₁ : ι → ℝ)
    (hu : ∀ k ∈ W, H₁ *ᵥ u k = (E₁ k : ℂ) • u k) (g : ℝ) (Ω : ι → ℝ)
    (hΩ : ∀ k ∈ W, 0 < Ω k) (hΩ2 : ∀ k ∈ W, Ω k ^ 2 = g ^ 2 + ((E₁ k - E₀) / 2) ^ 2)
    (s : ℝ) :
    levelProj n 1 *ᵥ (exp (s • ((-Complex.I) • (Matrix.blockDiagonal (bandBlocks E₀ H₁)
          + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 (∑ k ∈ W, a k • u k))
      = inLevel 1 (∑ k ∈ W,
          (a k * -(Complex.exp (-(Complex.I * (((E₀ + E₁ k) / 2 : ℝ) : ℂ)) * s)
            * (Complex.I * Complex.sin ((Ω k * s : ℝ) : ℂ) * ((g / Ω k : ℝ) : ℂ)))) • u k) := by
  rw [inLevel_sum, Matrix.mulVec_sum, Matrix.mulVec_sum, inLevel_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [inLevel_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
    levelProj_one_mulVec_exp_bandContact E₀ (hu k hk) g (hΩ k hk) (hΩ2 k hk) s, smul_smul,
    inLevel_smul]

end Levels

end CSD.RecordLayer

end
