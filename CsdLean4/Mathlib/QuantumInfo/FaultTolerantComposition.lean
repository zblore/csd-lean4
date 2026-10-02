/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.BlockKron

/-!
# Composing corrected gadgets along a circuit

**Category:** 1-Mathlib (CSD-free; staged for upstream).

BACKLOG #62's threshold programme has per-gadget theorems — a faulty transversal gate, Hadamard,
logical `X̄`/`Z̄` or two-block `CNOT` is corrected by one recovery channel — and the probabilistic
accounting over a circuit's locations. What it did not have is the step between them: **a circuit**,
and the statement that correcting each gadget in turn reproduces the ideal circuit. This module is
that step, abstractly:

* `IsCodeState P ρ` — the state is supported in the code space of the projector `P`;
* `IsCorrectedStep P ideal step` — the **two conditions a gadget must meet to be composable**:
  `step` (a faulty gadget followed by its recovery) returns the *ideal* gadget's output on code
  states, and the ideal gadget keeps code states in the code space. The second is the one that is
  easy to forget and does all the work in the induction: it is what hands the next gadget the
  hypothesis it needs;
* `Circuit`, `idealRun`, `correctedRun` — a circuit is a list of gadgets, each given by its ideal
  action and by the corrected step that implements it; the head acts first;
* ★ `isCodeState_idealRun` — the ideal run stays in the code space, gadget by gadget;
* ★★★ `correctedRun_eq_idealRun` — **the composition theorem**: a circuit whose every gadget is
  faulty and whose every fault is corrected computes exactly what the ideal circuit computes, on any
  code state.

The abstraction is deliberate. `step` is an arbitrary map on density operators, so it does not care
whether the recovery is an ideal channel or itself a faulty circuit: when #62(c) makes the recovery
gadget faulty, the same theorem applies to the new steps with no restatement.

## Honest scope

⚠️ **This is the deterministic half.** Nothing here counts faults or assigns them probabilities:
the hypothesis is that *every* gadget's fault is corrected, and the conclusion is exact equality. The
probability that a circuit's fault pattern is correctable is `Probability/CircuitThreshold.lean`
(#62(a)), and joining the two — one statement with a probability and an exact output — is #62(d2).

⚠️ **No level reduction.** A corrected step is a single level-1 object; the recursive simulation,
where a level-`k` gadget *is* a level-`(k−1)` circuit, is not here (#62(d2)). Nor is there any claim
that a given gadget set is universal or that a circuit computes anything in particular: `idealRun` is
whatever the list says it is.

References: D. Aharonov, M. Ben-Or, *Fault-tolerant quantum computation with constant error rate*,
SIAM J. Comput. 38 (2008) 1207 §§9–11 (rectangles and the simulation theorem);
`Probability/CircuitThreshold.lean`; `specs/BACKLOG.md` #62.
-/

@[expose] public section

open Matrix

noncomputable section

namespace QuantumInfo

variable {n : Type*} [Fintype n]

/-! ### Code states and corrected steps -/

/-- A state supported in the code space of the projector `P`. -/
def IsCodeState (P ρ : Matrix n n ℂ) : Prop := ρ = P * ρ * P

/-- A **corrected step**: `step` — think of a faulty gadget followed by its recovery — agrees with
the ideal gadget on code states, and the ideal gadget keeps code states in the code space. The two
conditions together are exactly what makes a *circuit* of such steps compose: the second is what
hands the next gadget the hypothesis it needs. -/
structure IsCorrectedStep (P : Matrix n n ℂ) (ideal step : Matrix n n ℂ → Matrix n n ℂ) :
    Prop where
  /-- On a code state the step returns the ideal gadget's output. -/
  recovers : ∀ ρ, IsCodeState P ρ → step ρ = ideal ρ
  /-- The ideal gadget keeps code states in the code space. -/
  preserves : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ)

/-! ### Circuits -/

/-- A **circuit**: a list of gadgets, each given by its ideal action and by the corrected step that
implements it. The head of the list acts first. -/
abbrev Circuit (n : Type*) :=
  List ((Matrix n n ℂ → Matrix n n ℂ) × (Matrix n n ℂ → Matrix n n ℂ))

/-- Running a list of maps, the head first. -/
def runMaps (steps : List (Matrix n n ℂ → Matrix n n ℂ)) (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  steps.foldl (fun σ S => S σ) ρ

omit [Fintype n] in
@[simp]
theorem runMaps_nil (ρ : Matrix n n ℂ) : runMaps [] ρ = ρ := rfl

omit [Fintype n] in
@[simp]
theorem runMaps_cons (S : Matrix n n ℂ → Matrix n n ℂ)
    (steps : List (Matrix n n ℂ → Matrix n n ℂ)) (ρ : Matrix n n ℂ) :
    runMaps (S :: steps) ρ = runMaps steps (S ρ) := rfl

/-- The circuit's ideal action: every gadget acting ideally. -/
def idealRun (c : Circuit n) (ρ : Matrix n n ℂ) : Matrix n n ℂ := runMaps (c.map Prod.fst) ρ

/-- The circuit as actually run: every gadget faulty, every fault corrected. -/
def correctedRun (c : Circuit n) (ρ : Matrix n n ℂ) : Matrix n n ℂ := runMaps (c.map Prod.snd) ρ

omit [Fintype n] in
@[simp]
theorem idealRun_nil (ρ : Matrix n n ℂ) : idealRun ([] : Circuit n) ρ = ρ := rfl

omit [Fintype n] in
@[simp]
theorem correctedRun_nil (ρ : Matrix n n ℂ) : correctedRun ([] : Circuit n) ρ = ρ := rfl

omit [Fintype n] in
@[simp]
theorem idealRun_cons (g : (Matrix n n ℂ → Matrix n n ℂ) × (Matrix n n ℂ → Matrix n n ℂ))
    (c : Circuit n) (ρ : Matrix n n ℂ) : idealRun (g :: c) ρ = idealRun c (g.1 ρ) := rfl

omit [Fintype n] in
@[simp]
theorem correctedRun_cons (g : (Matrix n n ℂ → Matrix n n ℂ) × (Matrix n n ℂ → Matrix n n ℂ))
    (c : Circuit n) (ρ : Matrix n n ℂ) : correctedRun (g :: c) ρ = correctedRun c (g.2 ρ) := rfl

/-- A circuit all of whose gadgets are corrected steps for the code `P`. -/
def IsCorrectedCircuit (P : Matrix n n ℂ) (c : Circuit n) : Prop :=
  ∀ g ∈ c, IsCorrectedStep P g.1 g.2

theorem isCorrectedCircuit_nil (P : Matrix n n ℂ) : IsCorrectedCircuit P ([] : Circuit n) := by
  intro g hg
  simp at hg

theorem IsCorrectedCircuit.tail {P : Matrix n n ℂ}
    {g : (Matrix n n ℂ → Matrix n n ℂ) × (Matrix n n ℂ → Matrix n n ℂ)} {c : Circuit n}
    (h : IsCorrectedCircuit P (g :: c)) : IsCorrectedCircuit P c :=
  fun g' hg' => h g' (List.mem_cons_of_mem _ hg')

theorem IsCorrectedCircuit.head {P : Matrix n n ℂ}
    {g : (Matrix n n ℂ → Matrix n n ℂ) × (Matrix n n ℂ → Matrix n n ℂ)} {c : Circuit n}
    (h : IsCorrectedCircuit P (g :: c)) : IsCorrectedStep P g.1 g.2 :=
  h g List.mem_cons_self

/-- ★ **The ideal run stays in the code space**, gadget by gadget. -/
theorem isCodeState_idealRun {P : Matrix n n ℂ} {c : Circuit n} (hc : IsCorrectedCircuit P c)
    {ρ : Matrix n n ℂ} (hρ : IsCodeState P ρ) : IsCodeState P (idealRun c ρ) := by
  induction c generalizing ρ with
  | nil => exact hρ
  | cons g c ih =>
    rw [idealRun_cons]
    exact ih hc.tail (hc.head.preserves ρ hρ)

/-- ★★★ **The composition theorem**: a circuit whose every gadget is faulty and whose every fault is
corrected computes exactly what the ideal circuit computes, on any code state. The induction is the
whole content: each corrected step returns the *ideal* output, and the ideal output is again a code
state, so the next gadget's hypothesis is available. Nothing here is special to a code or to a
gadget set — which is the point: when the recovery itself becomes a faulty circuit, the same theorem
applies to the new steps. -/
theorem correctedRun_eq_idealRun {P : Matrix n n ℂ} {c : Circuit n} (hc : IsCorrectedCircuit P c)
    {ρ : Matrix n n ℂ} (hρ : IsCodeState P ρ) : correctedRun c ρ = idealRun c ρ := by
  induction c generalizing ρ with
  | nil => rfl
  | cons g c ih =>
    rw [correctedRun_cons, idealRun_cons, hc.head.recovers ρ hρ]
    exact ih hc.tail (hc.head.preserves ρ hρ)

/-- A circuit of copies of one corrected gadget is corrected. -/
theorem isCorrectedCircuit_replicate {P : Matrix n n ℂ}
    {g : (Matrix n n ℂ → Matrix n n ℂ) × (Matrix n n ℂ → Matrix n n ℂ)}
    (h : IsCorrectedStep P g.1 g.2) (k : ℕ) :
    IsCorrectedCircuit P (List.replicate k g) := by
  intro g' hg'
  rw [List.eq_of_mem_replicate hg']
  exact h

end QuantumInfo

end

end
