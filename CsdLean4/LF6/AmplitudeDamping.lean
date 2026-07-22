/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# LF6-2 (T1 tier): the qubit amplitude-damping (T1 relaxation) semigroup

**Category:** 6-Local (the continuous-time open-system de-isolation frontier, the "living-history" tier).

The companion of the T2 dephasing semigroup (`LF6/DephasingSemigroup.lean`). Where dephasing removes
coherence but conserves populations, **amplitude damping** (T1 relaxation) transfers population from the
excited state (index `1`) to the ground state (index `0`) — spontaneous emission / energy relaxation.
With `e := e^{-γt}` (the excited-state survival factor) and coherence factor `e^{-γt/2}`:

    Φ_t(ρ) = [[ρ₀₀ + (1−e)·ρ₁₁,   e^{-γt/2}·ρ₀₁],
              [e^{-γt/2}·ρ₁₀,      e·ρ₁₁        ]].

This is the exact solution of the Lindblad amplitude-damping equation
`dρ/dt = γ(L ρ L† − ½{L†L, ρ})` with `L = |0⟩⟨1|` (the lowering operator), damping rate `γ = 1/T1`. We
prove the defining semigroup and open-system properties, axiom-free:

* `dampingChannel_zero` — `Φ_0 = id`;
* `dampingChannel_semigroup` — `Φ_s ∘ Φ_t = Φ_{s+t}` (the Markovian composition law);
* `dampingChannel_trace` — `tr Φ_t(ρ) = tr ρ` (trace preservation — it is a channel);
* `dampingChannel_excited_population` — the excited population decays exactly as `e^{-γt}·ρ₁₁`;
* `dampingChannel_ground_population` — the ground population *gains* `(1−e^{-γt})·ρ₁₁` (population flows
  `1 → 0`); this is the T1 signature, absent from pure dephasing;
* `dampingChannel_coherence` — the coherence decays as `e^{-γt/2}·ρ₀₁` (at half the population rate — the
  `T2 ≤ 2T1` relation);
* `dampingChannel_excited_tendsto_zero` / `dampingChannel_coherence_tendsto_zero` — for `γ > 0` the
  excited population and the coherence both `→ 0` as `t → ∞`: the state relaxes to the ground state
  (continuous-time energy relaxation / einselection to the ground pointer).

## Honest scope

This is the **T1 amplitude-damping** instance, the population-transferring companion of T2 dephasing;
together they are the two canonical qubit dissipators. **Deferred (the general residual, unchanged):** the
general Lindblad generator `dρ/dt = -i[H,ρ] + Σ L_k ρ L_k† − ½{L_k†L_k, ρ}` and its complete positivity.
The semigroup is exhibited directly (not derived as `Φ_t = e^{tℒ}`). Reuses only Mathlib matrix +
`Real.exp` facts (CSD-free).

Reference: `specs/future-work.md` (LF6-2).
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace CSD
namespace LF6

/-- **The qubit amplitude-damping (T1) channel** at time `t`, rate `γ`. The excited population (index
`1`) decays by `e^{-γt}`, its lost weight `(1−e^{-γt})·ρ₁₁` flows into the ground population (index `0`),
and the coherence is damped by `e^{-γt/2}`. The exact solution of the Lindblad amplitude-damping
equation. -/
noncomputable def dampingChannel (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![ρ 0 0 + (1 - (Real.exp (-(γ * t)) : ℂ)) * ρ 1 1, (Real.exp (-(γ * t) / 2) : ℂ) * ρ 0 1;
     (Real.exp (-(γ * t) / 2) : ℂ) * ρ 1 0, (Real.exp (-(γ * t)) : ℂ) * ρ 1 1]

@[simp] lemma dampingChannel_apply_00 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 0 0 = ρ 0 0 + (1 - (Real.exp (-(γ * t)) : ℂ)) * ρ 1 1 := rfl
@[simp] lemma dampingChannel_apply_11 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 1 1 = (Real.exp (-(γ * t)) : ℂ) * ρ 1 1 := rfl
@[simp] lemma dampingChannel_apply_01 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 0 1 = (Real.exp (-(γ * t) / 2) : ℂ) * ρ 0 1 := rfl
@[simp] lemma dampingChannel_apply_10 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 1 0 = (Real.exp (-(γ * t) / 2) : ℂ) * ρ 1 0 := rfl

/-- **Semigroup identity `Φ_0 = id`.** At `t = 0`, `e^0 = 1`, so populations and coherences are
unchanged. -/
theorem dampingChannel_zero (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ 0 ρ = ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dampingChannel]

/-- `e^{-γs}·e^{-γt} = e^{-γ(s+t)}` (population factor). -/
lemma exp_mul_pop (γ s t : ℝ) (X : ℂ) :
    (Real.exp (-(γ * s)) : ℂ) * ((Real.exp (-(γ * t)) : ℂ) * X)
      = (Real.exp (-(γ * (s + t))) : ℂ) * X := by
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show -(γ * s) + -(γ * t) = -(γ * (s + t)) from by ring]

/-- `e^{-γs/2}·e^{-γt/2} = e^{-γ(s+t)/2}` (coherence factor). -/
lemma exp_mul_coh (γ s t : ℝ) (X : ℂ) :
    (Real.exp (-(γ * s) / 2) : ℂ) * ((Real.exp (-(γ * t) / 2) : ℂ) * X)
      = (Real.exp (-(γ * (s + t)) / 2) : ℂ) * X := by
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show -(γ * s) / 2 + -(γ * t) / 2 = -(γ * (s + t)) / 2 from by ring]

/-- **The Markovian semigroup law `Φ_s ∘ Φ_t = Φ_{s+t}`.** The amplitude-damping channels compose as a
one-parameter semigroup: the excited population factor `e^{-γt}` and the coherence factor `e^{-γt/2}`
each multiply, and the transferred ground weight accumulates consistently. -/
theorem dampingChannel_semigroup (γ s t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ s (dampingChannel γ t ρ) = dampingChannel γ (s + t) ρ := by
  have hpop : (Real.exp (-(γ * s)) : ℂ) * (Real.exp (-(γ * t)) : ℂ)
      = (Real.exp (-(γ * (s + t))) : ℂ) := by
    simpa using exp_mul_pop γ s t 1
  ext i j
  fin_cases i <;> fin_cases j
  · -- ground population: ρ₀₀ + (1−e_t)ρ₁₁ + (1−e_s)·e_t·ρ₁₁ = ρ₀₀ + (1−e_{s+t})ρ₁₁
    show (ρ 0 0 + (1 - (Real.exp (-(γ * t)) : ℂ)) * ρ 1 1)
        + (1 - (Real.exp (-(γ * s)) : ℂ)) * ((Real.exp (-(γ * t)) : ℂ) * ρ 1 1)
      = ρ 0 0 + (1 - (Real.exp (-(γ * (s + t))) : ℂ)) * ρ 1 1
    rw [← hpop]; ring
  · show (Real.exp (-(γ * s) / 2) : ℂ) * ((Real.exp (-(γ * t) / 2) : ℂ) * ρ 0 1)
        = (Real.exp (-(γ * (s + t)) / 2) : ℂ) * ρ 0 1
    exact exp_mul_coh γ s t (ρ 0 1)
  · show (Real.exp (-(γ * s) / 2) : ℂ) * ((Real.exp (-(γ * t) / 2) : ℂ) * ρ 1 0)
        = (Real.exp (-(γ * (s + t)) / 2) : ℂ) * ρ 1 0
    exact exp_mul_coh γ s t (ρ 1 0)
  · show (Real.exp (-(γ * s)) : ℂ) * ((Real.exp (-(γ * t)) : ℂ) * ρ 1 1)
        = (Real.exp (-(γ * (s + t))) : ℂ) * ρ 1 1
    exact exp_mul_pop γ s t (ρ 1 1)

/-- **Trace preservation.** `tr Φ_t(ρ) = tr ρ`: the weight lost from the excited population is exactly
gained by the ground population, so probability is conserved. -/
theorem dampingChannel_trace (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dampingChannel γ t ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, dampingChannel_apply_00,
    dampingChannel_apply_11]
  ring

/-- **Excited-population decay (T1 relaxation).** The excited-state population decays exactly as
`Φ_t(ρ)₁₁ = e^{-γt}·ρ₁₁` — exponential energy relaxation at rate `γ = 1/T1`. -/
theorem dampingChannel_excited_population (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 1 1 = (Real.exp (-(γ * t)) : ℂ) * ρ 1 1 := rfl

/-- **Ground-population gain (the T1 signature).** The ground population *increases* by the weight
`(1−e^{-γt})·ρ₁₁` lost from the excited state: population flows `1 → 0`. This is what distinguishes
amplitude damping from pure dephasing (which conserves both populations). -/
theorem dampingChannel_ground_population (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 0 0 = ρ 0 0 + (1 - (Real.exp (-(γ * t)) : ℂ)) * ρ 1 1 := rfl

/-- **Coherence decay.** The coherence decays as `Φ_t(ρ)₀₁ = e^{-γt/2}·ρ₀₁` — at *half* the population
decay rate, the exact statement of the `T2 ≤ 2T1` relation for pure amplitude damping. -/
theorem dampingChannel_coherence (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampingChannel γ t ρ 0 1 = (Real.exp (-(γ * t) / 2) : ℂ) * ρ 0 1 := rfl

/-- The complex decay factor `e^{-c t} → 0` as `t → ∞` (for `c > 0`). -/
lemma exp_decay {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => (Real.exp (-(c * t)) : ℂ)) Filter.atTop (nhds 0) := by
  have hlin : Filter.Tendsto (fun t : ℝ => -(c * t)) Filter.atTop Filter.atBot := by
    have h : Filter.Tendsto (fun t : ℝ => (-c) * t) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (show -c < 0 by linarith)
    simpa only [neg_mul] using h
  have hreal : Filter.Tendsto (fun t : ℝ => Real.exp (-(c * t))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa only [Complex.ofReal_zero, Function.comp_def] using
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal

/-- **Relaxation to the ground state: the excited population vanishes** as `t → ∞` (for `γ > 0`). The
diagonal `Φ_t(ρ)₁₁ → 0`: continuous-time energy relaxation empties the excited state. -/
theorem dampingChannel_excited_tendsto_zero {γ : ℝ} (hγ : 0 < γ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Filter.Tendsto (fun t => dampingChannel γ t ρ 1 1) Filter.atTop (nhds 0) := by
  simp only [dampingChannel_excited_population]
  simpa using (exp_decay hγ).mul_const (ρ 1 1)

/-- **The coherence vanishes** as `t → ∞` (for `γ > 0`). The off-diagonal `Φ_t(ρ)₀₁ → 0` at rate
`γ/2`: relaxation also destroys coherence, driving the state to the ground pointer. -/
theorem dampingChannel_coherence_tendsto_zero {γ : ℝ} (hγ : 0 < γ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Filter.Tendsto (fun t => dampingChannel γ t ρ 0 1) Filter.atTop (nhds 0) := by
  simp only [dampingChannel_coherence]
  have hhalf : Filter.Tendsto (fun t : ℝ => (Real.exp (-(γ * t) / 2) : ℂ)) Filter.atTop (nhds 0) :=
    (exp_decay (show (0 : ℝ) < γ / 2 by linarith)).congr
      (fun t => by rw [show -(γ / 2 * t) = -(γ * t) / 2 from by ring])
  simpa using hhalf.mul_const (ρ 0 1)

end LF6
end CSD
