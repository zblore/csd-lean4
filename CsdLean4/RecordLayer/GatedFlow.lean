/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.ODE.LipschitzFlow
public import CsdLean4.RecordLayer.RecordOccurrence
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# A Hamiltonian gated by a register: the reversible flow

**Category:** 7-SigmaLayer (the record layer). BACKLOG #274, first landing.

An `ActualOccurrence` needs a two-time law `evolve t u ∘ evolve s t = evolve s u` for **all**
`s, t, u`, so its dynamics must be invertible. A relay that fires once, or releases a messenger at a
state-dependent time, is not of that form as stated. The honest relay is a **gated Hamiltonian**:
the quantum state `Ψ` evolves by `−i (H₀ + c(Ψ, r) V) Ψ`, where the gate `c` is a function of the
state and of a classical register `r` that integrates a weight `w(Ψ)` of the state. This is an
autonomous vector field on the arena `(ι → ℂ) × ℝ`; when it is globally Lipschitz it generates a
global flow (`LipschitzWith.odeFlow`), and that flow is an admissible `evolve`.

* `GateArena`, `gatedField` (the field), `gatedField_fst`, `gatedField_eq`;
* `exists_lipschitzWith_mulVec` (a matrix acts Lipschitz), `lipschitzWith_gateScale` (**the gated
  state `c(x) • Ψ` is Lipschitz** when the gate is Lipschitz, bounded, and closed for `‖Ψ‖ ≥ R`);
  ★★ `exists_lipschitzWith_gatedField` — **the gated field is globally Lipschitz** under those
  hypotheses and a Lipschitz weight;
* ★★ `gatedFlow` — **the flow**, `gatedFlow_zero`, `gatedFlow_add` (the group law),
  `hasDerivAt_gatedFlow`, `hasDerivAt_gatedFlow_fst`/`_snd` (it solves the gated equation),
  `continuous_gatedFlow`, `measurable_gatedFlow`; `gatedEvolve` — **the two-time law**,
  `gatedEvolve_self`, `gatedEvolve_comp`, `measurable_gatedEvolve`: what `ActualOccurrence.evolve`
  needs;
* ★★ `isHermitian_gateHam`, `sum_norm_sq_gatedFlow` — **for Hermitian `H₀`, `V` the flow conserves
  `Σ‖Ψ_i‖²`**: the gate is a state-dependent real coefficient, so the generator stays Hermitian;
* ★ `register_gatedFlow` — **the register is the time integral of its weight along the orbit**;
  `register_mono_gatedFlow` (nonnegative weight: the register never decreases);
* ★★ `gatedFlow_fst_eq_of_gate_closed` — **while the gate is closed the state evolves freely**:
  if `c = 0` along the orbit on `[0, t]`, the state agrees there with any solution of
  `Ψ' = −i H₀ Ψ` from the same start (uniqueness);
* ★★★ `gated_register_flow` — the bundle.

## The finding

**The reversibility wall of #274 is passable.** The relay's release need not be an event in the
dynamics: a gate that is a function of the state and of a monotone register gives an autonomous,
globally Lipschitz field, hence a flow with the full two-time law, measurable, norm preserving, and
free while the gate is closed. What the relay instance (the next landing) adds is a specific gate
`c = φ(r) · w'(Ψ) · χ(‖Ψ‖)` with a kick Hamiltonian `V`, and the bound on the released state.

## Honest scope

⚠️ **The Lipschitz hypotheses are the consumer's.** The gate must be globally Lipschitz, bounded,
and closed for `‖Ψ‖ ≥ R`, and the weight globally Lipschitz; a quadratic Born weight is not globally
Lipschitz, so the instance composes it with a cutoff that is the identity on the physical region
(`Σ‖Ψ_i‖² ≤ 1`, preserved by the flow). On that region the field is the physical one.

⚠️ **The register is classical**: a real number driven by a weight of the state and feeding back
on the Hamiltonian, the hybrid law the record layer's registers already follow (`regFlow`,
`tickFlow`); nothing here is the ontic selection of one record (#266).

⚠️ **One quantum block and one register.** The relay's arena (two observers, two messengers, several
registers) is a block-diagonal `H₀` on a sum type with the gate reading one block and acting on
another; several registers are the next landing's generalisation.

References: `specs/BACKLOG.md` #274, #256, #254, #253, #266, #39;
`Mathlib/Analysis/ODE/LipschitzFlow.lean` (`LipschitzWith.odeFlow`, `odeFlow_add`,
`odeFlow_eq_of_hasDerivAt`, `measurable_odeFlow`); `RecordLayer/RecordOccurrence.lean`
(`ActualOccurrence`); `RecordLayer/DiracObservers.lean` (`regFlow`); `RecordLayer/DiracRateTicks.lean`
(`weightFlow`).
-/

@[expose] public section

open Set Metric Filter Topology MeasureTheory Complex
open scoped Matrix NNReal

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {ι : Type*} [Fintype ι]

/-- **The arena**: a quantum state on `ι` and one classical register. -/
abbrev GateArena (ι : Type*) : Type _ := (ι → ℂ) × ℝ

/-! ### The gated field -/

/-- **The gated field**: the state by `−i (H₀ + c(Ψ, r) V) Ψ`, the register by the weight `w Ψ`. -/
noncomputable def gatedField (H₀ V : Matrix ι ι ℂ) (c : (ι → ℂ) → ℝ → ℝ) (w : (ι → ℂ) → ℝ)
    (x : GateArena ι) : GateArena ι :=
  ((-I) • ((H₀ + ((c x.1 x.2 : ℝ) : ℂ) • V) *ᵥ x.1), w x.1)

theorem gatedField_fst (H₀ V : Matrix ι ι ℂ) (c : (ι → ℂ) → ℝ → ℝ) (w : (ι → ℂ) → ℝ)
    (x : GateArena ι) :
    (gatedField H₀ V c w x).1 = (-I) • ((H₀ + ((c x.1 x.2 : ℝ) : ℂ) • V) *ᵥ x.1) := rfl

theorem gatedField_snd (H₀ V : Matrix ι ι ℂ) (c : (ι → ℂ) → ℝ → ℝ) (w : (ι → ℂ) → ℝ)
    (x : GateArena ι) : (gatedField H₀ V c w x).2 = w x.1 := rfl

/-- The field split into its linear part and its gated part. -/
theorem gatedField_eq (H₀ V : Matrix ι ι ℂ) (c : (ι → ℂ) → ℝ → ℝ) (w : (ι → ℂ) → ℝ) :
    gatedField H₀ V c w = fun x =>
      (((-I) • H₀) *ᵥ x.1 + ((-I) • V) *ᵥ (((c x.1 x.2 : ℝ) : ℂ) • x.1), w x.1) := by
  funext x
  simp only [gatedField, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_add,
    smul_smul]
  rw [mul_comm (-I) ((c x.1 x.2 : ℝ) : ℂ)]

/-! ### Lipschitz -/

/-- A matrix acts as a Lipschitz map. -/
theorem exists_lipschitzWith_mulVec (A : Matrix ι ι ℂ) :
    ∃ K : ℝ≥0, LipschitzWith K fun Ψ : ι → ℂ => A *ᵥ Ψ := by
  set L : (ι → ℂ) →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  refine ⟨‖L‖₊, ?_⟩
  have h := L.lipschitzWith
  have e : (L : (ι → ℂ) → (ι → ℂ)) = fun Ψ => A *ᵥ Ψ := by
    funext Ψ
    simp [L]
  rwa [e] at h

/-- **The gated state is Lipschitz**: for a gate `c` that is Lipschitz, bounded by `C`, and closed
(`c = 0`) once `‖Ψ‖ ≥ R`, the map `(Ψ, r) ↦ c(Ψ, r) • Ψ` is globally Lipschitz. -/
theorem lipschitzWith_gateScale {c : (ι → ℂ) → ℝ → ℝ} {Lc : ℝ≥0} {C R : ℝ}
    (hc : LipschitzWith Lc fun x : GateArena ι => c x.1 x.2) (hC : 0 ≤ C)
    (hcb : ∀ x : GateArena ι, |c x.1 x.2| ≤ C) (hR : 0 ≤ R)
    (hc0 : ∀ (Ψ : ι → ℂ) (r : ℝ), R ≤ ‖Ψ‖ → c Ψ r = 0) :
    LipschitzWith ⟨Lc * R + C, by positivity⟩
      fun x : GateArena ι => ((c x.1 x.2 : ℝ) : ℂ) • x.1 := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  show dist _ _ ≤ (Lc * R + C) * dist x y
  rw [dist_eq_norm]
  have hd : dist x.1 y.1 ≤ dist x y := by
    have := LipschitzWith.prod_fst.dist_le_mul x y
    simpa using this
  rw [dist_eq_norm] at hd
  have hcd : |c x.1 x.2 - c y.1 y.2| ≤ Lc * dist x y := by
    have := hc.dist_le_mul x y
    rwa [Real.dist_eq] at this
  have hdist := dist_nonneg (x := x) (y := y)
  have key : ∀ (a b : ℝ) (Ψ Ψ' : ι → ℂ), ‖Ψ‖ < R → |b| ≤ C →
      ‖((a : ℝ) : ℂ) • Ψ - ((b : ℝ) : ℂ) • Ψ'‖ ≤ |a - b| * R + C * ‖Ψ - Ψ'‖ := by
    intro a b Ψ Ψ' hΨ hb
    have e : ((a : ℝ) : ℂ) • Ψ - ((b : ℝ) : ℂ) • Ψ' = ((a - b : ℝ) : ℂ) • Ψ + ((b : ℝ) : ℂ) • (Ψ - Ψ') := by
      push_cast
      rw [sub_smul, smul_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    gcongr
  by_cases hx : ‖x.1‖ < R
  · refine (key _ _ _ _ hx (hcb y)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hcd hR, mul_le_mul_of_nonneg_left hd hC]
  · rw [hc0 x.1 x.2 (not_lt.1 hx), Complex.ofReal_zero, zero_smul, zero_sub, norm_neg]
    by_cases hy : ‖y.1‖ < R
    · have h := key (c y.1 y.2) (c x.1 x.2) y.1 x.1 hy (hcb x)
      rw [hc0 x.1 x.2 (not_lt.1 hx), Complex.ofReal_zero, zero_smul, sub_zero, sub_zero,
        norm_sub_rev] at h
      rw [← neg_sub, abs_neg, hc0 x.1 x.2 (not_lt.1 hx), sub_zero] at hcd
      refine h.trans ?_
      have h1 := mul_le_mul_of_nonneg_right hcd hR
      have h2 := mul_le_mul_of_nonneg_left hd hC
      linarith
    · rw [hc0 y.1 y.2 (not_lt.1 hy), Complex.ofReal_zero, zero_smul, norm_zero]
      positivity

/-- ★★ **The gated field is globally Lipschitz** for a Lipschitz, bounded gate closed beyond `R`
and a Lipschitz weight. -/
theorem exists_lipschitzWith_gatedField (H₀ V : Matrix ι ι ℂ) {c : (ι → ℂ) → ℝ → ℝ}
    {w : (ι → ℂ) → ℝ} {Lc Lw : ℝ≥0} {C R : ℝ}
    (hc : LipschitzWith Lc fun x : GateArena ι => c x.1 x.2) (hC : 0 ≤ C)
    (hcb : ∀ x : GateArena ι, |c x.1 x.2| ≤ C) (hR : 0 ≤ R)
    (hc0 : ∀ (Ψ : ι → ℂ) (r : ℝ), R ≤ ‖Ψ‖ → c Ψ r = 0) (hw : LipschitzWith Lw w) :
    ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V c w) := by
  obtain ⟨K₁, h₁⟩ := exists_lipschitzWith_mulVec ((-I) • H₀)
  obtain ⟨K₂, h₂⟩ := exists_lipschitzWith_mulVec ((-I) • V)
  have hs := lipschitzWith_gateScale hc hC hcb hR hc0
  have hA : LipschitzWith (K₁ * 1) fun x : GateArena ι => ((-I) • H₀) *ᵥ x.1 :=
    h₁.comp LipschitzWith.prod_fst
  have hB := h₂.comp hs
  have hW : LipschitzWith (Lw * 1) fun x : GateArena ι => w x.1 := hw.comp LipschitzWith.prod_fst
  exact ⟨_, by rw [gatedField_eq]; exact (hA.add hB).prodMk hW⟩

/-! ### The flow -/

section Flow

variable {H₀ V : Matrix ι ι ℂ} {c : (ι → ℂ) → ℝ → ℝ} {w : (ι → ℂ) → ℝ}

/-- ★★ **The gated flow**: the global flow of the gated field. -/
noncomputable def gatedFlow (hL : ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V c w)) (t : ℝ)
    (x : GateArena ι) : GateArena ι :=
  (Classical.choose_spec hL).odeFlow t x

variable (hL : ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V c w))

theorem gatedFlow_zero (x : GateArena ι) : gatedFlow hL 0 x = x :=
  (Classical.choose_spec hL).odeFlow_zero x

/-- **The group law.** -/
theorem gatedFlow_add (s t : ℝ) (x : GateArena ι) :
    gatedFlow hL (s + t) x = gatedFlow hL t (gatedFlow hL s x) :=
  (Classical.choose_spec hL).odeFlow_add s t x

theorem hasDerivAt_gatedFlow (x : GateArena ι) (t : ℝ) :
    HasDerivAt (fun t => gatedFlow hL t x) (gatedField H₀ V c w (gatedFlow hL t x)) t :=
  (Classical.choose_spec hL).hasDerivAt_odeFlow x t

/-- **The state solves the gated equation** `Ψ' = −i (H₀ + c(Ψ, r) V) Ψ`. -/
theorem hasDerivAt_gatedFlow_fst (x : GateArena ι) (t : ℝ) :
    HasDerivAt (fun t => (gatedFlow hL t x).1)
      ((-I) • ((H₀ + ((c (gatedFlow hL t x).1 (gatedFlow hL t x).2 : ℝ) : ℂ) • V)
        *ᵥ (gatedFlow hL t x).1)) t :=
  (hasDerivAt_gatedFlow hL x t).fst

/-- **The register integrates the weight**: `r' = w Ψ`. -/
theorem hasDerivAt_gatedFlow_snd (x : GateArena ι) (t : ℝ) :
    HasDerivAt (fun t => (gatedFlow hL t x).2) (w (gatedFlow hL t x).1) t :=
  (hasDerivAt_gatedFlow hL x t).snd

theorem continuous_gatedFlow : Continuous fun p : ℝ × GateArena ι => gatedFlow hL p.1 p.2 :=
  (Classical.choose_spec hL).continuous_odeFlow

theorem continuous_gatedFlow_time (x : GateArena ι) : Continuous fun t => gatedFlow hL t x :=
  (Classical.choose_spec hL).continuous_odeFlow_time x

theorem measurable_gatedFlow (t : ℝ) : Measurable (gatedFlow hL t) :=
  (Classical.choose_spec hL).measurable_odeFlow t

/-- **The two-time law**: the evolution from `s` to `t`. -/
noncomputable def gatedEvolve (s t : OnticTime) : GateArena ι → GateArena ι :=
  gatedFlow hL (t - s)

theorem gatedEvolve_self (t : OnticTime) :
    gatedEvolve hL t t = (id : GateArena ι → GateArena ι) := by
  funext x
  simp only [gatedEvolve, sub_self, gatedFlow_zero, id]

theorem gatedEvolve_comp (s t u : OnticTime) :
    gatedEvolve hL t u ∘ gatedEvolve hL s t = (gatedEvolve hL s u : GateArena ι → GateArena ι) := by
  funext x
  simp only [gatedEvolve, Function.comp]
  rw [show u - s = (t - s) + (u - t) by ring, gatedFlow_add]

theorem measurable_gatedEvolve (s t : OnticTime) : Measurable (gatedEvolve hL s t) :=
  measurable_gatedFlow hL (t - s)

/-! ### Norm conservation -/

omit [Fintype ι] in
/-- A real gate keeps the generator Hermitian. -/
theorem isHermitian_gateHam (hH : H₀.IsHermitian) (hV : V.IsHermitian) (a : ℝ) :
    (H₀ + ((a : ℝ) : ℂ) • V).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH.eq, hV.eq, Complex.star_def,
    Complex.conj_ofReal]

/-- The squared norm as the Hermitian form. -/
theorem star_dotProduct_self_eq (Ψ : ι → ℂ) :
    star Ψ ⬝ᵥ Ψ = ((∑ i, ‖Ψ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']

/-- ★★ **For Hermitian `H₀`, `V` the gated flow conserves the norm**: `Σ‖Ψ_i(t)‖² = Σ‖Ψ_i(0)‖²`. -/
theorem sum_norm_sq_gatedFlow (hH : H₀.IsHermitian) (hV : V.IsHermitian) (x : GateArena ι)
    (t : ℝ) : ∑ i, ‖(gatedFlow hL t x).1 i‖ ^ 2 = ∑ i, ‖x.1 i‖ ^ 2 := by
  set Ψ : ℝ → ι → ℂ := fun t => (gatedFlow hL t x).1 with hΨ
  set F : ℝ → ℂ := fun t => star (Ψ t) ⬝ᵥ Ψ t with hF
  have hderiv : ∀ t, HasDerivAt F 0 t := by
    intro t
    set A : Matrix ι ι ℂ := H₀ + ((c (gatedFlow hL t x).1 (gatedFlow hL t x).2 : ℝ) : ℂ) • V
      with hA
    have hAh : A.IsHermitian := isHermitian_gateHam hH hV _
    have hd : HasDerivAt Ψ ((-I) • (A *ᵥ Ψ t)) t := hasDerivAt_gatedFlow_fst hL x t
    have hc := fun i => hasDerivAt_pi.1 hd i
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ((hc i).star).mul (hc i)
    have e : ∑ i ∈ Finset.univ, (star (((-I) • (A *ᵥ Ψ t)) i) * Ψ t i
        + star (Ψ t i) * ((-I) • (A *ᵥ Ψ t)) i) = 0 := by
      have h1 : ∑ i ∈ Finset.univ, (star (((-I) • (A *ᵥ Ψ t)) i) * Ψ t i
          + star (Ψ t i) * ((-I) • (A *ᵥ Ψ t)) i)
          = star ((-I) • (A *ᵥ Ψ t)) ⬝ᵥ Ψ t + star (Ψ t) ⬝ᵥ ((-I) • (A *ᵥ Ψ t)) := by
        rw [dotProduct, dotProduct, ← Finset.sum_add_distrib]
        rfl
      have e1 : star ((-I) • (A *ᵥ Ψ t)) ⬝ᵥ Ψ t = I * (star (Ψ t) ⬝ᵥ (A *ᵥ Ψ t)) := by
        rw [star_smul, smul_dotProduct, Matrix.star_dotProduct, hAh.star_dotProduct_mulVec_comm,
          star_neg, Complex.star_def, Complex.conj_I, neg_neg, smul_eq_mul]
      have e2 : star (Ψ t) ⬝ᵥ ((-I) • (A *ᵥ Ψ t)) = -I * (star (Ψ t) ⬝ᵥ (A *ᵥ Ψ t)) := by
        rw [dotProduct_smul, smul_eq_mul]
      rw [h1, e1, e2]
      ring
    rw [e] at hs
    exact hs
  have hconst : ∀ t, F t = F 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) t 0
  have h := hconst t
  simp only [hF, hΨ, gatedFlow_zero, star_dotProduct_self_eq] at h
  exact_mod_cast h

/-! ### The register -/

/-- ★ **The register is the time integral of its weight along the orbit.** -/
theorem register_gatedFlow (hw : Continuous w) (x : GateArena ι) (t : ℝ) :
    (gatedFlow hL t x).2 = x.2 + ∫ s in (0 : ℝ)..t, w (gatedFlow hL s x).1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := fun s => (gatedFlow hL s x).2) (f' := fun s => w (gatedFlow hL s x).1)
    (fun s _ => hasDerivAt_gatedFlow_snd hL x s)
    ((hw.comp (continuous_fst.comp (continuous_gatedFlow_time hL x))).intervalIntegrable 0 t)
  rw [h, gatedFlow_zero]
  ring

/-- A nonnegative weight never lets the register fall. -/
theorem register_mono_gatedFlow (hw : Continuous w) (hw0 : ∀ Ψ, 0 ≤ w Ψ) (x : GateArena ι)
    {t : ℝ} (ht : 0 ≤ t) : x.2 ≤ (gatedFlow hL t x).2 := by
  rw [register_gatedFlow hL hw]
  have := intervalIntegral.integral_nonneg (μ := volume) ht fun s _ => hw0 (gatedFlow hL s x).1
  linarith

/-! ### The gate closed -/

/-- ★★ **While the gate is closed the state evolves freely**: if `c = 0` along the orbit on
`[0, t]`, the state agrees there with any solution `γ` of `γ' = −i H₀ γ` from the same start. -/
theorem gatedFlow_fst_eq_of_gate_closed (x : GateArena ι) {t : ℝ}
    (hclosed : ∀ s ∈ Icc (0 : ℝ) t, c (gatedFlow hL s x).1 (gatedFlow hL s x).2 = 0)
    {γ : ℝ → ι → ℂ} (hγ : ∀ s, HasDerivAt γ ((-I) • (H₀ *ᵥ γ s)) s) (hγ0 : γ 0 = x.1) :
    ∀ s ∈ Icc (0 : ℝ) t, (gatedFlow hL s x).1 = γ s := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_mulVec ((-I) • H₀)
  have hK' : ∀ _ : ℝ, LipschitzWith K fun Ψ : ι → ℂ => (-I) • (H₀ *ᵥ Ψ) := fun _ => by
    simpa only [Matrix.smul_mulVec] using hK
  refine ODE_solution_unique (v := fun _ Ψ => (-I) • (H₀ *ᵥ Ψ)) (a := 0) (b := t)
    (f := fun s => (gatedFlow hL s x).1) (g := γ) hK'
    (fun s _ => (hasDerivAt_gatedFlow_fst hL x s).continuousAt.continuousWithinAt)
    (fun s hs => ?_) (fun s _ => (hγ s).continuousAt.continuousWithinAt)
    (fun s _ => (hγ s).hasDerivWithinAt) (by rw [gatedFlow_zero, hγ0])
  have h := (hasDerivAt_gatedFlow_fst hL x s).hasDerivWithinAt (s := Ici s)
  rwa [hclosed s (Ico_subset_Icc_self hs), Complex.ofReal_zero, zero_smul, add_zero] at h

/-! ### The bundle -/

/-- ★★★ **A Hamiltonian gated by a register generates a reversible flow** (BACKLOG #274, first
landing). For a gate `c(Ψ, r)` that is Lipschitz, bounded, and closed for `‖Ψ‖ ≥ R`, a Lipschitz
weight `w`, and Hermitian `H₀`, `V`:

* **the gated field is globally Lipschitz**, so it has a global flow `φ`;
* **the two-time law**: `φ_{s→t}` with `φ_{t→t} = id` and `φ_{t→u} ∘ φ_{s→t} = φ_{s→u}` for all
  `s, t, u` — what an `ActualOccurrence` needs — each `φ_{s→t}` measurable;
* **it solves the gated equation**: `Ψ' = −i (H₀ + c(Ψ, r) V) Ψ`, `r' = w Ψ`;
* **the norm is conserved**: `Σ‖Ψ_i(t)‖² = Σ‖Ψ_i(0)‖²`;
* **the register is the integral of its weight**, never falling when `w ≥ 0`;
* **while the gate is closed the state evolves freely** by `H₀`. -/
theorem gated_register_flow (H₀ V : Matrix ι ι ℂ) {c : (ι → ℂ) → ℝ → ℝ}
    {w : (ι → ℂ) → ℝ} {Lc Lw : ℝ≥0} {C R : ℝ}
    (hc : LipschitzWith Lc fun x : GateArena ι => c x.1 x.2) (hC : 0 ≤ C)
    (hcb : ∀ x : GateArena ι, |c x.1 x.2| ≤ C) (hR : 0 ≤ R)
    (hc0 : ∀ (Ψ : ι → ℂ) (r : ℝ), R ≤ ‖Ψ‖ → c Ψ r = 0) (hw : LipschitzWith Lw w)
    (hH : H₀.IsHermitian) (hV : V.IsHermitian) :
    ∃ hL : ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V c w),
      let φ := gatedFlow hL
      (∀ t, gatedEvolve hL t t = (id : GateArena ι → GateArena ι))
      ∧ (∀ s t u, gatedEvolve hL t u ∘ gatedEvolve hL s t = gatedEvolve hL s u)
      ∧ (∀ s t, Measurable (gatedEvolve hL s t))
      ∧ (∀ x t, HasDerivAt (fun t => (φ t x).1)
          ((-I) • ((H₀ + ((c (φ t x).1 (φ t x).2 : ℝ) : ℂ) • V) *ᵥ (φ t x).1)) t)
      ∧ (∀ x t, HasDerivAt (fun t => (φ t x).2) (w (φ t x).1) t)
      ∧ (∀ x t, ∑ i, ‖(φ t x).1 i‖ ^ 2 = ∑ i, ‖x.1 i‖ ^ 2)
      ∧ (∀ x t, (φ t x).2 = x.2 + ∫ s in (0 : ℝ)..t, w (φ s x).1)
      ∧ ((∀ Ψ, 0 ≤ w Ψ) → ∀ x t, 0 ≤ t → x.2 ≤ (φ t x).2)
      ∧ ∀ x t, (∀ s ∈ Icc (0 : ℝ) t, c (φ s x).1 (φ s x).2 = 0) →
          ∀ γ : ℝ → ι → ℂ, (∀ s, HasDerivAt γ ((-I) • (H₀ *ᵥ γ s)) s) → γ 0 = x.1 →
            ∀ s ∈ Icc (0 : ℝ) t, (φ s x).1 = γ s := by
  refine ⟨exists_lipschitzWith_gatedField H₀ V hc hC hcb hR hc0 hw, ?_⟩
  intro φ
  exact ⟨gatedEvolve_self _, gatedEvolve_comp _, measurable_gatedEvolve _,
    fun x t => hasDerivAt_gatedFlow_fst _ x t, fun x t => hasDerivAt_gatedFlow_snd _ x t,
    fun x t => sum_norm_sq_gatedFlow _ hH hV x t,
    fun x t => register_gatedFlow _ hw.continuous x t,
    fun hw0 x t ht => register_mono_gatedFlow _ hw.continuous hw0 x ht,
    fun x t hcl γ hγ hγ0 => gatedFlow_fst_eq_of_gate_closed _ x hcl hγ hγ0⟩

end Flow

end CSD.RecordLayer
