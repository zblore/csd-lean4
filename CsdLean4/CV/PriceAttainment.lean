/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.InteractionPrice
public import CsdLean4.CV.PowerCounting
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormEntry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Matrix.Basis

/-!
# P5-attainment: the linear price is attained — "costs at most" becomes "costs exactly"

**Category:** CV (continuous variables — the attainment half of P5;
`eft-pillars-plan.md` P5).

**Glossary:** https://glossary.constraintsurfacedynamics.com/interaction-price/
Plain-language, CSD-role and formal statements of the interaction price, with
this module as the Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

CV-9 priced locality violation from above: switching on a coupling `λ` moves
an `S`-supported observable at most `2·|τ|·|λ|·C·‖A‖` from the `S`-supported
subalgebra (`heisenberg_interactingU_near_supported`). Whether that linear
price is *attained* was CV-9's declared boundary. This module closes it with
a matching linear lower bound on a witness. Scoped first in
`specs/price-attainment-plan.md`.

* `norm_commutator_le_of_commute` — **the commutator functional**: any
  `S`-supported `B` commutes with a disjointly supported probe (CV-2b), so
  `‖[X,P]‖ ≤ 2·‖X−B‖·‖P‖` — a commutator against a unit probe bounds the
  distance to the whole `S`-supported subalgebra from below.
* The `K = N = 2` witness: `priceObs = modeOp 0 (single 0 1)`,
  `priceProbe = modeOp 1 (single 0 1)`, pair coupling
  `priceV c = [c₀ = 1 ∧ c₁ = 1]`. The interacting drive is a diagonal phase,
  so the commutator entry at `(config 00, config 11)` is computable exactly:
  the free phases cancel (energy is mode-additive), the coupling phases do
  not (the coupling reads both modes), and the entry has modulus
  `2·|sin(τλ/2)|` (`comm_entry_norm`).
* ★★ `price_lower_bound` — for EVERY `{0}`-supported `B`:
  `|sin(τλ/2)| ≤ ‖heisenberg (interactingU 2 2 τ λ priceV) priceObs − B‖`.
  No supported operator is closer than the sine of the accumulated coupling
  phase.
* ★★ `price_linear_attained` — **the sandwich** (`0 ≤ τλ ≤ π`, Jordan):
  `τλ/π ≤ dist(X, S-supported) ≤ 2·τλ`. The price of locality violation is
  **linear in the coupling on both sides**: CV-9's "costs at most" is now
  "costs exactly", up to the constant gap `[1/π, 2]`.

⚠️ Honest scope: attainment is an existence claim, and a witness is exactly
what it needs — one drive, one coupling shape, `K = N = 2`. No claim that
every drive saturates the bound, and the constants are not matched (on this
witness the distance is `2|sin(τλ/2)|`-shaped; the exact-distance
identification is not claimed here).

## References

`specs/price-attainment-plan.md` (scoping); `specs/eft-pillars-plan.md` (P5);
`specs/future-work.md`; `CV/InteractionPrice.lean` (CV-9, the upper bound);
`CV/DynamicalLocality.lean` (`heisenberg_phaseDiagU_apply`);
`CV/ModeLocality.lean` (`modeOp`, `commute_of_disjointSupport`);
`CV/PowerCounting.lean` (`l2_opNorm_modeOp_le`);
`Mathlib/Analysis/Matrix/L2OpNormEntry.lean` (`norm_entry_le_l2_opNorm`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix Real

namespace CSD.CV

variable {K N : ℕ}

/-! ### The commutator functional: distance from below -/

/-- **The commutator functional**: if `B` commutes with the probe `P`, the
commutator of `X` with `P` is controlled by the distance from `X` to `B`. In
use, `B` ranges over an `S`-supported subalgebra and `P` is a disjointly
supported probe, so this bounds the distance to the WHOLE subalgebra from
below by a single computable commutator. -/
lemma norm_commutator_le_of_commute [NeZero N]
    {X B P : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hBP : B * P = P * B) :
    ‖X * P - P * X‖ ≤ 2 * ‖X - B‖ * ‖P‖ := by
  have hsplit : X * P - P * X = (X - B) * P - P * (X - B) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hBP]
    abel
  rw [hsplit]
  calc ‖(X - B) * P - P * (X - B)‖
      ≤ ‖(X - B) * P‖ + ‖P * (X - B)‖ := norm_sub_le _ _
    _ ≤ ‖X - B‖ * ‖P‖ + ‖P‖ * ‖X - B‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X - B‖ * ‖P‖ := by ring

/-! ### Norm bricks -/

/-- The unit basis matrix has operator norm at most one. -/
lemma l2_opNorm_single_le_one :
    ‖Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)‖ ≤ 1 := by
  have hct : (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ
      = Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.single, Matrix.of_apply]
    split_ifs with h1 h2 h2 <;> simp_all [and_comm]
  have hdiag : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = Matrix.diagonal (fun i : Fin 2 => if i = 1 then (1 : ℂ) else 0) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.diagonal]
  have hsq : ‖Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)‖
      * ‖Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hct,
      Matrix.single_mul_single_same, one_mul, hdiag]
    exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun i => by
      split_ifs <;> simp
  nlinarith [norm_nonneg (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))]

/-- `‖1 − e^{iθ}‖ = 2·|sin(θ/2)|` — the exact chord length. -/
lemma norm_one_sub_exp_I_mul (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * θ)‖ = 2 * |Real.sin (θ / 2)| := by
  have hcos : (0 : ℝ) ≤ (1 - Real.cos θ) / 2 := by
    have := Real.cos_le_one θ
    linarith
  have hsq : ‖(1 : ℂ) - Complex.exp (Complex.I * θ)‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hrhs : (2 * |Real.sin (θ / 2)|) ^ 2 = 2 - 2 * Real.cos θ := by
    rw [mul_pow, Real.abs_sin_half, Real.sq_sqrt hcos]
    ring
  have h := hsq.trans hrhs.symm
  exact (pow_left_inj₀ (norm_nonneg _)
    (by positivity) two_ne_zero).mp h

/-- The conjugate of a diagonal phase is the inverse phase. -/
lemma star_exp_neg_I_mul_real (x : ℝ) :
    star (Complex.exp (-(Complex.I * x))) = Complex.exp (Complex.I * x) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

/-! ### The witness -/

/-- The witness pair coupling: `v(c) = 1` exactly when both modes sit at
level `1`. Bounded by `1`. -/
noncomputable def priceV : FieldConfig 2 2 → ℝ :=
  fun c => if c 0 = 1 ∧ c 1 = 1 then 1 else 0

lemma priceV_abs_le_one (c : FieldConfig 2 2) : |priceV c| ≤ 1 := by
  rw [priceV]
  split_ifs <;> norm_num

/-- The witness observable: the unit single-mode matrix at mode `0`. -/
noncomputable def priceObs : Matrix (FieldConfig 2 2) (FieldConfig 2 2) ℂ :=
  modeOp 0 (Matrix.single 0 1 1)

/-- The probe: the unit single-mode matrix at mode `1`. -/
noncomputable def priceProbe : Matrix (FieldConfig 2 2) (FieldConfig 2 2) ℂ :=
  modeOp 1 (Matrix.single 0 1 1)

lemma priceObs_supportedOn : SupportedOn {0} priceObs :=
  modeOp_supportedOn 0 _

lemma priceProbe_supportedOn : SupportedOn {1} priceProbe :=
  modeOp_supportedOn 1 _

lemma priceObs_norm_le_one : ‖priceObs‖ ≤ 1 :=
  le_trans (l2_opNorm_modeOp_le 0 _) l2_opNorm_single_le_one

lemma priceProbe_norm_le_one : ‖priceProbe‖ ≤ 1 :=
  le_trans (l2_opNorm_modeOp_le 1 _) l2_opNorm_single_le_one

/-! ### Entry evaluations: where each factor lives -/

/-- The witness observable out of `config (0,0)`: only into `config (1,0)`. -/
lemma priceObs_apply_c00 (e : FieldConfig 2 2) :
    priceObs ![0, 0] e = if e = ![1, 0] then 1 else 0 := by
  by_cases he : e = ![1, 0]
  · subst he
    rw [if_pos rfl, priceObs]
    have hag : ∀ k, k ≠ (0 : Fin 2) →
        (![0, 0] : FieldConfig 2 2) k = (![1, 0] : FieldConfig 2 2) k := by
      intro k hk
      fin_cases k
      · exact absurd rfl hk
      · rfl
    rw [modeOp_apply_of_agree 0 _ hag]
    simp [Matrix.single]
  · rw [if_neg he, priceObs]
    by_cases hag : ∀ k, k ≠ 0 → (![0, 0] : FieldConfig 2 2) k = e k
    · rw [modeOp_apply_of_agree 0 _ hag]
      have h1 : e 1 = 0 := (hag 1 (by decide)).symm
      have h0 : ¬((1 : Fin 2) = e 0) := by
        intro h
        exact he (funext fun k => by
          fin_cases k
          · exact h.symm
          · exact h1)
      simp only [Matrix.single, Matrix.of_apply]
      rw [if_neg (fun hc => h0 hc.2)]
    · rw [modeOp]
      exact if_neg hag

/-- The witness observable into `config (1,1)`: only out of `config (0,1)`. -/
lemma priceObs_apply_c11 (e : FieldConfig 2 2) :
    priceObs e ![1, 1] = if e = ![0, 1] then 1 else 0 := by
  by_cases he : e = ![0, 1]
  · subst he
    rw [if_pos rfl, priceObs]
    have hag : ∀ k, k ≠ (0 : Fin 2) →
        (![0, 1] : FieldConfig 2 2) k = (![1, 1] : FieldConfig 2 2) k := by
      intro k hk
      fin_cases k
      · exact absurd rfl hk
      · rfl
    rw [modeOp_apply_of_agree 0 _ hag]
    simp [Matrix.single]
  · rw [if_neg he, priceObs]
    by_cases hag : ∀ k, k ≠ 0 → e k = (![1, 1] : FieldConfig 2 2) k
    · rw [modeOp_apply_of_agree 0 _ hag]
      have h1 : e 1 = 1 := hag 1 (by decide)
      have h0 : ¬((0 : Fin 2) = e 0) := by
        intro h
        exact he (funext fun k => by
          fin_cases k
          · exact h.symm
          · exact h1)
      simp only [Matrix.single, Matrix.of_apply]
      rw [if_neg (fun hc => h0 hc.1)]
    · rw [modeOp]
      exact if_neg hag

/-- The probe into `config (1,1)`: only out of `config (1,0)`. -/
lemma priceProbe_apply_c11 (e : FieldConfig 2 2) :
    priceProbe e ![1, 1] = if e = ![1, 0] then 1 else 0 := by
  by_cases he : e = ![1, 0]
  · subst he
    rw [if_pos rfl, priceProbe]
    have hag : ∀ k, k ≠ (1 : Fin 2) →
        (![1, 0] : FieldConfig 2 2) k = (![1, 1] : FieldConfig 2 2) k := by
      intro k hk
      fin_cases k
      · rfl
      · exact absurd rfl hk
    rw [modeOp_apply_of_agree 1 _ hag]
    simp [Matrix.single]
  · rw [if_neg he, priceProbe]
    by_cases hag : ∀ k, k ≠ 1 → e k = (![1, 1] : FieldConfig 2 2) k
    · rw [modeOp_apply_of_agree 1 _ hag]
      have h0 : e 0 = 1 := hag 0 (by decide)
      have h1 : ¬((0 : Fin 2) = e 1) := by
        intro h
        exact he (funext fun k => by
          fin_cases k
          · exact h0
          · exact h.symm)
      simp only [Matrix.single, Matrix.of_apply]
      rw [if_neg (fun hc => h1 hc.1)]
    · rw [modeOp]
      exact if_neg hag

/-- The probe out of `config (0,0)`: only into `config (0,1)`. -/
lemma priceProbe_apply_c00 (e : FieldConfig 2 2) :
    priceProbe ![0, 0] e = if e = ![0, 1] then 1 else 0 := by
  by_cases he : e = ![0, 1]
  · subst he
    rw [if_pos rfl, priceProbe]
    have hag : ∀ k, k ≠ (1 : Fin 2) →
        (![0, 0] : FieldConfig 2 2) k = (![0, 1] : FieldConfig 2 2) k := by
      intro k hk
      fin_cases k
      · rfl
      · exact absurd rfl hk
    rw [modeOp_apply_of_agree 1 _ hag]
    simp [Matrix.single]
  · rw [if_neg he, priceProbe]
    by_cases hag : ∀ k, k ≠ 1 → (![0, 0] : FieldConfig 2 2) k = e k
    · rw [modeOp_apply_of_agree 1 _ hag]
      have h0 : e 0 = 0 := (hag 0 (by decide)).symm
      have h1 : ¬((1 : Fin 2) = e 1) := by
        intro h
        exact he (funext fun k => by
          fin_cases k
          · exact h0
          · exact h.symm)
      simp only [Matrix.single, Matrix.of_apply]
      rw [if_neg (fun hc => h1 hc.2)]
    · rw [modeOp]
      exact if_neg hag

/-! ### The phase bookkeeping -/

/-- The diagonal phase function of the witness drive. -/
noncomputable def priceF (τ lam : ℝ) : FieldConfig 2 2 → ℝ :=
  fun c => τ * (fieldEnergy c + lam * priceV c)

lemma interactingU_priceV (τ lam : ℝ) :
    interactingU 2 2 τ lam priceV = phaseDiagU (priceF τ lam) := rfl

/-- **The cross-difference of the phases is exactly the coupling phase**: the
free (energy) parts cancel because energy is mode-additive, and the coupling
survives because it reads both modes. -/
lemma priceF_cross (τ lam : ℝ) :
    (priceF τ lam ![0, 1] - priceF τ lam ![1, 1])
      - (priceF τ lam ![0, 0] - priceF τ lam ![1, 0]) = -(τ * lam) := by
  have hE : ∀ c : FieldConfig 2 2,
      fieldEnergy c = oscEnergy ((c 0 : ℕ)) + oscEnergy ((c 1 : ℕ)) := by
    intro c
    rw [show fieldEnergy c = ∑ k, oscEnergy ((c k : ℕ)) from rfl,
      Fin.sum_univ_two]
  simp only [priceF, priceV, hE]
  norm_num [show ((![0, 1] : FieldConfig 2 2) 0 : ℕ) = 0 from rfl,
    show ((![0, 1] : FieldConfig 2 2) 1 : ℕ) = 1 from rfl,
    show ((![1, 1] : FieldConfig 2 2) 0 : ℕ) = 1 from rfl,
    show ((![1, 1] : FieldConfig 2 2) 1 : ℕ) = 1 from rfl,
    show ((![0, 0] : FieldConfig 2 2) 0 : ℕ) = 0 from rfl,
    show ((![0, 0] : FieldConfig 2 2) 1 : ℕ) = 0 from rfl,
    show ((![1, 0] : FieldConfig 2 2) 0 : ℕ) = 1 from rfl,
    show ((![1, 0] : FieldConfig 2 2) 1 : ℕ) = 0 from rfl,
    show ¬((![0, 1] : FieldConfig 2 2) 0 = 1 ∧ (![0, 1] : FieldConfig 2 2) 1 = 1) from
      fun h => by exact absurd h.1 (by decide),
    show ((![1, 1] : FieldConfig 2 2) 0 = 1 ∧ (![1, 1] : FieldConfig 2 2) 1 = 1) from
      ⟨rfl, rfl⟩,
    show ¬((![0, 0] : FieldConfig 2 2) 0 = 1 ∧ (![0, 0] : FieldConfig 2 2) 1 = 1) from
      fun h => by exact absurd h.1 (by decide),
    show ¬((![1, 0] : FieldConfig 2 2) 0 = 1 ∧ (![1, 0] : FieldConfig 2 2) 1 = 1) from
      fun h => by exact absurd h.2 (by decide)]
  ring

/-! ### The commutator entry, exactly -/

/-- The `(config 00, config 11)` entry of `X·P` collapses to the single path
through `config (1,0)`. -/
lemma XP_entry (τ lam : ℝ) :
    (heisenberg (interactingU 2 2 τ lam priceV) priceObs * priceProbe) ![0, 0] ![1, 1]
      = Complex.exp (Complex.I * (priceF τ lam ![0, 0]))
        * Complex.exp (-(Complex.I * (priceF τ lam ![1, 0]))) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun e _ => by
    rw [priceProbe_apply_c11 e, mul_ite, mul_one, mul_zero]]
  rw [Finset.sum_ite_eq' Finset.univ (![1, 0] : FieldConfig 2 2) _,
    if_pos (Finset.mem_univ _)]
  rw [interactingU_priceV, heisenberg_phaseDiagU_apply,
    show priceObs ![0, 0] ![1, 0] = 1 from by
      rw [priceObs_apply_c00, if_pos rfl],
    star_exp_neg_I_mul_real]
  ring

/-- The `(config 00, config 11)` entry of `P·X` collapses to the single path
through `config (0,1)`. -/
lemma PX_entry (τ lam : ℝ) :
    (priceProbe * heisenberg (interactingU 2 2 τ lam priceV) priceObs) ![0, 0] ![1, 1]
      = Complex.exp (Complex.I * (priceF τ lam ![0, 1]))
        * Complex.exp (-(Complex.I * (priceF τ lam ![1, 1]))) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun e _ => by
    rw [priceProbe_apply_c00 e, ite_mul, one_mul, zero_mul]]
  rw [Finset.sum_ite_eq' Finset.univ (![0, 1] : FieldConfig 2 2) _,
    if_pos (Finset.mem_univ _)]
  rw [interactingU_priceV, heisenberg_phaseDiagU_apply,
    show priceObs ![0, 1] ![1, 1] = 1 from by
      rw [priceObs_apply_c11, if_pos rfl],
    star_exp_neg_I_mul_real]
  ring

/-- ★ **The commutator entry has modulus `2·|sin(τλ/2)|`, exactly.** The free
phases cancel between the two paths; the coupling phase does not. -/
lemma comm_entry_norm (τ lam : ℝ) :
    ‖(heisenberg (interactingU 2 2 τ lam priceV) priceObs * priceProbe
        - priceProbe * heisenberg (interactingU 2 2 τ lam priceV) priceObs)
      ![0, 0] ![1, 1]‖ = 2 * |Real.sin (τ * lam / 2)| := by
  rw [Matrix.sub_apply, XP_entry, PX_entry]
  set a := priceF τ lam ![0, 0] - priceF τ lam ![1, 0] with ha
  set b := priceF τ lam ![0, 1] - priceF τ lam ![1, 1] with hb
  have h1 : Complex.exp (Complex.I * (priceF τ lam ![0, 0]))
        * Complex.exp (-(Complex.I * (priceF τ lam ![1, 0])))
      = Complex.exp (Complex.I * (a : ℝ)) := by
    rw [← Complex.exp_add, ha]
    push_cast
    ring_nf
  have h2 : Complex.exp (Complex.I * (priceF τ lam ![0, 1]))
        * Complex.exp (-(Complex.I * (priceF τ lam ![1, 1])))
      = Complex.exp (Complex.I * (b : ℝ)) := by
    rw [← Complex.exp_add, hb]
    push_cast
    ring_nf
  rw [h1, h2,
    show Complex.exp (Complex.I * (a : ℝ)) - Complex.exp (Complex.I * (b : ℝ))
      = Complex.exp (Complex.I * (a : ℝ))
          * ((1 : ℂ) - Complex.exp (Complex.I * ((b - a : ℝ) : ℂ))) from by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      push_cast
      ring_nf,
    norm_mul,
    show ‖Complex.exp (Complex.I * (a : ℝ))‖ = 1 from by
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I a,
    one_mul, norm_one_sub_exp_I_mul,
    show b - a = -(τ * lam) from by rw [ha, hb]; exact priceF_cross τ lam]
  rw [show -(τ * lam) / 2 = -(τ * lam / 2) from by ring, Real.sin_neg, abs_neg]

/-! ### The attainment theorems -/

/-- ★★ **The linear price is attained from below**: EVERY `{0}`-supported
operator is at least `|sin(τλ/2)|` away from the interacting Heisenberg
observable. CV-9's declared attainment boundary closes on this witness. -/
theorem price_lower_bound (τ lam : ℝ)
    {B : Matrix (FieldConfig 2 2) (FieldConfig 2 2) ℂ}
    (hB : SupportedOn {0} B) :
    |Real.sin (τ * lam / 2)|
      ≤ ‖heisenberg (interactingU 2 2 τ lam priceV) priceObs - B‖ := by
  set X := heisenberg (interactingU 2 2 τ lam priceV) priceObs with hX
  have hdisj : Disjoint ({0} : Finset (Fin 2)) {1} := by decide
  have hcomm : B * priceProbe = priceProbe * B :=
    commute_of_disjointSupport hdisj hB priceProbe_supportedOn
  have hentry : 2 * |Real.sin (τ * lam / 2)|
      ≤ ‖X * priceProbe - priceProbe * X‖ := by
    rw [← comm_entry_norm τ lam]
    exact Matrix.norm_entry_le_l2_opNorm _ _ _
  have hcommbd : ‖X * priceProbe - priceProbe * X‖
      ≤ 2 * ‖X - B‖ * ‖priceProbe‖ := norm_commutator_le_of_commute hcomm
  have hprobe := priceProbe_norm_le_one
  nlinarith [norm_nonneg (X - B), norm_nonneg priceProbe]

/-- ★★ **The sandwich — the price is linear on both sides.** For
`0 ≤ τλ ≤ π`: every `{0}`-supported operator is at least `τλ/π` away
(Jordan's inequality on the exact sine), and some `{0}`-supported operator is
within `2τλ` (CV-9's upper bound at `C = 1`, `‖A‖ ≤ 1`). "Costs at most" is
now "costs exactly", up to the constant gap `[1/π, 2]`. -/
theorem price_linear_attained (τ lam : ℝ) (h0 : 0 ≤ τ * lam) (hπ : τ * lam ≤ π) :
    (∀ B, SupportedOn {0} B →
      τ * lam / π
        ≤ ‖heisenberg (interactingU 2 2 τ lam priceV) priceObs - B‖)
    ∧ (∃ B, SupportedOn {0} B ∧
      ‖heisenberg (interactingU 2 2 τ lam priceV) priceObs - B‖
        ≤ 2 * (τ * lam)) := by
  constructor
  · intro B hB
    refine le_trans ?_ (price_lower_bound τ lam hB)
    have hx : 0 ≤ τ * lam / 2 := by linarith
    have hx' : τ * lam / 2 ≤ π / 2 := by linarith
    have hj := Real.mul_le_sin hx hx'
    have hπ0 : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    calc τ * lam / π = 2 / π * (τ * lam / 2) := by field_simp
      _ ≤ Real.sin (τ * lam / 2) := hj
      _ ≤ |Real.sin (τ * lam / 2)| := le_abs_self _
  · obtain ⟨B, hBsupp, hBle⟩ :=
      heisenberg_interactingU_near_supported (S := {0}) τ lam priceV
        zero_le_one priceV_abs_le_one priceObs_supportedOn
    refine ⟨B, hBsupp, le_trans hBle ?_⟩
    have habs : |τ| * (|lam| * 1) = τ * lam := by
      rw [mul_one, ← abs_mul, abs_of_nonneg h0]
    rw [habs]
    calc 2 * (τ * lam) * ‖priceObs‖ ≤ 2 * (τ * lam) * 1 := by
          have := priceObs_norm_le_one
          gcongr
      _ = 2 * (τ * lam) := by ring

end CSD.CV
