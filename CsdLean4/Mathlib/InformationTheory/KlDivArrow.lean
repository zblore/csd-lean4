/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Relative entropy is a Lyapunov function for a Markov dynamics

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). The general half of the
second law at a coarse-graining: what makes a divergence decrease, and what cannot make it decrease.

Mathlib has the three data-processing inequalities for `klDiv` (`klDiv_map_le`, `klDiv_trim_le`,
`klDiv_comp_right_le`). Two consequences that the arrow of time is usually stated as are not there,
and this file adds them.

* ★★ `klDiv_map_measurableEquiv` — **a reversible relabelling changes no divergence.** The data
  processing inequality applied in both directions along a measurable equivalence gives equality, so
  an invertible step produces *nothing*: whatever a coarse-grained second law produces comes from the
  coarse-graining or from the kernel, never from a reversible dynamics;
* ★★★ `klDiv_comp_le_of_stationary` — **the H-theorem.** If a Markov kernel fixes `π`, the divergence
  of any law from `π` is non-increasing under one step. This is the second law in its modern form: a
  Lyapunov function, with no symmetry, double stochasticity or detailed balance assumed — only
  stationarity of the reference;
* `Measure.compIterate` with ★★ `antitone_klDiv_compIterate` — and the divergence is **monotone along
  the whole trajectory**, which is what makes it an arrow rather than a one-step inequality.

## Honest scope

⚠️ **No kernel is constructed, and stationarity is a hypothesis.** The theorems say what follows from
having a Markov kernel with an invariant law; exhibiting one for a given dynamics is the consumer's
problem, and the H-theorem is vacuous for a kernel with no invariant measure.

⚠️ **Divergence, not Shannon entropy.** `klDiv q π` decreasing is equivalent to Shannon entropy
increasing only when `π` is uniform on a finite space, through
`klDiv q uniform = log (card) − H q`. That identity is *not* proved here: it needs the
Radon–Nikodym derivative of one finite-type measure against another, which is a separate piece of
work. Everything below is therefore about divergence from a reference law.

⚠️ **`klDiv` is `∞` off absolute continuity.** Both inequalities are then true and empty. The content
is for laws absolutely continuous with respect to the reference.

References: T. Cover, J. Thomas, *Elements of Information Theory*, 2nd ed., Thm 4.4.1 and §11
(relative entropy decreases under a Markov chain with the stationary distribution as reference);
`Mathlib.InformationTheory.KullbackLeibler.DataProcessing`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace MeasureTheory.Measure

/-! ### The whole trajectory -/

/-- The law after `n` steps of a kernel. -/
noncomputable def compIterate (μ : Measure α) (κ : Kernel α α) : ℕ → Measure α
  | 0 => μ
  | n + 1 => κ ∘ₘ μ.compIterate κ n

@[simp] theorem compIterate_zero (μ : Measure α) (κ : Kernel α α) :
    μ.compIterate κ 0 = μ := rfl

@[simp] theorem compIterate_succ (μ : Measure α) (κ : Kernel α α) (n : ℕ) :
    μ.compIterate κ (n + 1) = κ ∘ₘ μ.compIterate κ n := rfl

instance isProbabilityMeasure_compIterate (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) : IsProbabilityMeasure (μ.compIterate κ n) := by
  induction n with
  | zero => rw [compIterate_zero]; infer_instance
  | succ n ih => rw [compIterate_succ]; exact inferInstanceAs (IsProbabilityMeasure (κ ∘ₘ _))

end MeasureTheory.Measure

namespace InformationTheory

/-! ### A reversible step produces nothing -/

/-- ★★ **A reversible relabelling changes no divergence.** The data processing inequality holds along
`e` and along `e.symm`, so along a measurable equivalence it is an equality.

This is the half of a coarse-grained second law that is usually left implicit: an invertible step
produces no entropy, so whatever a coarse-grained law produces comes from the coarse-graining or from
the kernel. -/
theorem klDiv_map_measurableEquiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : α ≃ᵐ β) : klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have hmm : ∀ ρ : Measure α, (ρ.map e).map e.symm = ρ := fun ρ => by
    rw [Measure.map_map e.symm.measurable e.measurable,
      show (e.symm ∘ e : α → α) = id from funext e.symm_apply_apply, Measure.map_id]
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [hmm μ, hmm ν] at h

/-! ### The H-theorem -/

/-- ★★★ **The H-theorem.** If a Markov kernel fixes the reference law `π`, then the divergence of any
law from `π` is non-increasing under one step of the kernel.

Nothing is assumed beyond stationarity of `π`: no symmetry, no double stochasticity, no detailed
balance. The proof is the data processing inequality with the stationarity rewritten into its right
argument. -/
theorem klDiv_comp_le_of_stationary {μ π : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (κ : Kernel α α) [IsMarkovKernel κ] (hπ : κ ∘ₘ π = π) :
    klDiv (κ ∘ₘ μ) π ≤ klDiv μ π :=
  calc klDiv (κ ∘ₘ μ) π = klDiv (κ ∘ₘ μ) (κ ∘ₘ π) := by rw [hπ]
    _ ≤ klDiv μ π := klDiv_comp_right_le μ π κ

/-- ★★ **The divergence from a stationary law is monotone along the whole trajectory**, which is what
makes it an arrow of time rather than a one-step inequality. -/
theorem antitone_klDiv_compIterate {μ π : Measure α} [IsProbabilityMeasure μ]
    [IsFiniteMeasure π] (κ : Kernel α α) [IsMarkovKernel κ] (hπ : κ ∘ₘ π = π) :
    Antitone fun n : ℕ => klDiv (μ.compIterate κ n) π := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [Measure.compIterate_succ]
  exact klDiv_comp_le_of_stationary κ hπ

/-- ★ **And so no step of the trajectory is further from the stationary law than the start.** -/
theorem klDiv_compIterate_le {μ π : Measure α} [IsProbabilityMeasure μ] [IsFiniteMeasure π]
    (κ : Kernel α α) [IsMarkovKernel κ] (hπ : κ ∘ₘ π = π) (n : ℕ) :
    klDiv (μ.compIterate κ n) π ≤ klDiv μ π :=
  antitone_klDiv_compIterate κ hπ (Nat.zero_le n)

end InformationTheory

end
