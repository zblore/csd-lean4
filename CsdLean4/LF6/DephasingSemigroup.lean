/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# LF6-2 (bounded core): the qubit T2 dephasing quantum dynamical semigroup

**Category:** 6-Local (the continuous-time open-system de-isolation frontier, the "living-history" tier).

LF6-D realises measurement as a single deterministic de-isolation flow step. LF6-2 asks for the
*continuous-time* open-system version: a one-parameter quantum dynamical semigroup (the solution of a
Lindblad master equation) implementing decoherence. This module builds the canonical bounded instance —
the qubit **T2 dephasing** semigroup — as a self-contained computation:

    Φ_t(ρ) = [[ρ₀₀,           e^{-γt}·ρ₀₁],
              [e^{-γt}·ρ₁₀,   ρ₁₁      ]].

This is the exact solution of the Lindblad dephasing equation `dρ/dt = γ(σ_z ρ σ_z − ρ)/2` (dephasing
rate `γ = 1/T2`). We prove the defining semigroup and open-system properties, axiom-free:

* `dephasingChannel_zero` — `Φ_0 = id` (the semigroup identity);
* `dephasingChannel_semigroup` — `Φ_s ∘ Φ_t = Φ_{s+t}` (the Markovian composition law);
* `dephasingChannel_trace` — `tr Φ_t(ρ) = tr ρ` (trace preservation — it is a channel);
* `dephasingChannel_populations` — the diagonal `ρ₀₀, ρ₁₁` (the pointer populations) are conserved:
  dephasing is **population-preserving** (pure T2, no T1 relaxation);
* `dephasingChannel_coherence` — the off-diagonal coherence decays exactly as `e^{-γt}·ρ₀₁`;
* `dephasingChannel_coherence_tendsto_zero` — for `γ > 0` the coherence `→ 0` as `t → ∞`, so the state
  is driven to its pointer-diagonal (decohered) form: continuous-time einselection.

## Honest scope

This is the **T2 dephasing** instance — a genuine continuous-time de-isolation semigroup with monotone
decoherence to the pointer basis (coherence `→ 0`, populations preserved). It is the bounded core of
LF6-2. **Deferred (the general residual):** the general Lindblad generator
(`dρ/dt = -i[H,ρ] + Σ L_k ρ L_k† − ½{L_k†L_k, ρ}`), its complete positivity, and the T1
amplitude-damping channel — the full open-system tier. The generator/ODE derivation (that `Φ_t = e^{tℒ}`
for the Lindblad `ℒ`) is not built here; the semigroup is exhibited directly as the physical content.
Reuses only Mathlib matrix + `Real.exp` facts (CSD-free).

Reference: `specs/future-work.md` (LF6-2).
-/

open scoped BigOperators
open Matrix

namespace CSD
namespace LF6

/-- **The qubit T2 dephasing channel** at time `t` with rate `γ`: the diagonal (population) entries are
untouched, the off-diagonal (coherence) entries are damped by `e^{-γt}`. The exact solution of the
Lindblad dephasing equation. -/
noncomputable def dephasingChannel (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![ρ 0 0, (Real.exp (-(γ * t)) : ℂ) * ρ 0 1;
     (Real.exp (-(γ * t)) : ℂ) * ρ 1 0, ρ 1 1]

@[simp] lemma dephasingChannel_apply_00 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ t ρ 0 0 = ρ 0 0 := rfl
@[simp] lemma dephasingChannel_apply_11 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ t ρ 1 1 = ρ 1 1 := rfl
@[simp] lemma dephasingChannel_apply_01 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ t ρ 0 1 = (Real.exp (-(γ * t)) : ℂ) * ρ 0 1 := rfl
@[simp] lemma dephasingChannel_apply_10 (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ t ρ 1 0 = (Real.exp (-(γ * t)) : ℂ) * ρ 1 0 := rfl

/-- **Semigroup identity `Φ_0 = id`.** At `t = 0` the dephasing channel is the identity (`e^0 = 1`). -/
theorem dephasingChannel_zero (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ 0 ρ = ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dephasingChannel]

/-- **The Markovian semigroup law `Φ_s ∘ Φ_t = Φ_{s+t}`.** The dephasing channels compose as a
one-parameter semigroup: `e^{-γs}·e^{-γt} = e^{-γ(s+t)}`. This is the defining property of a quantum
dynamical (Markovian) semigroup — memoryless continuous-time evolution. -/
theorem dephasingChannel_semigroup (γ s t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ s (dephasingChannel γ t ρ) = dephasingChannel γ (s + t) ρ := by
  have hexp : ∀ X : ℂ, (Real.exp (-(γ * s)) : ℂ) * ((Real.exp (-(γ * t)) : ℂ) * X)
      = (Real.exp (-(γ * (s + t))) : ℂ) * X := by
    intro X
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      show -(γ * s) + -(γ * t) = -(γ * (s + t)) from by ring]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · show (Real.exp (-(γ * s)) : ℂ) * ((Real.exp (-(γ * t)) : ℂ) * ρ 0 1)
        = (Real.exp (-(γ * (s + t))) : ℂ) * ρ 0 1
    exact hexp (ρ 0 1)
  · show (Real.exp (-(γ * s)) : ℂ) * ((Real.exp (-(γ * t)) : ℂ) * ρ 1 0)
        = (Real.exp (-(γ * (s + t))) : ℂ) * ρ 1 0
    exact hexp (ρ 1 0)
  · rfl

/-- **Trace preservation.** `tr Φ_t(ρ) = tr ρ`: dephasing preserves the trace (probability), so it is a
genuine trace-preserving channel. -/
theorem dephasingChannel_trace (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dephasingChannel γ t ρ).trace = ρ.trace := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **Population preservation (pure T2, no T1).** The diagonal entries — the pointer-basis populations —
are conserved for all `t`: dephasing removes coherence without relaxing populations. -/
theorem dephasingChannel_populations (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ t ρ 0 0 = ρ 0 0 ∧ dephasingChannel γ t ρ 1 1 = ρ 1 1 :=
  ⟨rfl, rfl⟩

/-- **Coherence decay (the decoherence law).** The off-diagonal coherence decays exactly as
`Φ_t(ρ)₀₁ = e^{-γt}·ρ₀₁` — exponential suppression at rate `γ = 1/T2`. -/
theorem dephasingChannel_coherence (γ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingChannel γ t ρ 0 1 = (Real.exp (-(γ * t)) : ℂ) * ρ 0 1 := rfl

/-- The complex-valued decay factor `e^{-γt} → 0` as `t → ∞` (for `γ > 0`). -/
private lemma dephasing_decay {γ : ℝ} (hγ : 0 < γ) :
    Filter.Tendsto (fun t : ℝ => (Real.exp (-(γ * t)) : ℂ)) Filter.atTop (nhds 0) := by
  have hlin : Filter.Tendsto (fun t : ℝ => -(γ * t)) Filter.atTop Filter.atBot := by
    have h : Filter.Tendsto (fun t : ℝ => (-γ) * t) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (show -γ < 0 by linarith)
    simpa only [neg_mul] using h
  have hreal : Filter.Tendsto (fun t : ℝ => Real.exp (-(γ * t))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa only [Complex.ofReal_zero, Function.comp_def] using
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal

/-- **Monotone decoherence: the coherence vanishes as `t → ∞`** (for `γ > 0`). The off-diagonal element
`Φ_t(ρ)₀₁ → 0`: continuous-time de-isolation drives the state to the pointer (diagonal) basis — its
populations survive (`dephasingChannel_populations`), its coherence dies. This is the continuous-time
realisation of einselection to the pointer basis. -/
theorem dephasingChannel_coherence_tendsto_zero {γ : ℝ} (hγ : 0 < γ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Filter.Tendsto (fun t => dephasingChannel γ t ρ 0 1) Filter.atTop (nhds 0) := by
  simp only [dephasingChannel_coherence]
  simpa using (dephasing_decay hγ).mul_const (ρ 0 1)

end LF6
end CSD

