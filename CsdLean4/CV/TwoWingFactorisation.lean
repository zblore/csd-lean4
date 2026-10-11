/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.TwoWingCone
public import CsdLean4.CV.CompositeArena

/-!
# The two-wing cone from the flow's own factorisation

**Category:** 3-Local (CV; the causal shape of the two-wing experiment, second route).
BACKLOG #139, taken the way CSD's own foundations prefer.

[`TwoWingCone.lean`](TwoWingCone.lean) gets the wings' causal separation from a **supplied coupling
graph**: `twoWingGraph` has no A–B edge, so the cones never meet. That left #131 with one arena and
**two dynamics** — the cone came from `graphInteractingU`, while the Born weights, the record history
and the CHSH value come from `LF6.localDeisolationFlow`, and nothing related them.

CSD does not want two. `specs/CSD-CHARTER.md` is explicit that "there is one flow and one
microstate", and the corpus gives the same discharge condition for Posit 1 and Posit 10 — derive it
from the de-isolation dynamics. The fully principled route is therefore one Hamiltonian generating
both, which is the `H_int` frontier (`R-016`) and has no cheap brick. **This file takes the reachable
form of the same idea: drop the second interaction and read the separation off the measurement flow
itself.**

## The point

`LF6.localFlowUnitary` is `reindex … (vnUnitary 2 ⊗ₖ vnUnitary 2)` and
`LF6.localDeisolation_factorises` says the dilation is `V_A ⊗ V_B`. **The measurement interaction is
already a product of per-wing unitaries.** A product unitary has disjoint per-wing support, and
disjoint supports commute — so the separation is a property of the *measurement*, with **no graph and
no period count**:

* ★★ `leftModes_two_two` and `rightModes_two_two` — `CompositeArena`'s mode blocks at
  `K₁ = K₂ = 2` **are** `TwoWingCone`'s wing mode sets, so that file's machinery and this one's are
  about the same regions (`by decide`);
* ★★★ `supportedOn_heisenberg_pow_of_factorised` — **the evolved A-observable stays A-local at every
  power of a factorised flow.** This is what replaces the cone: there is no ball to grow, because
  the B-factor acts trivially on an A-supported observable (`heisenberg_eq_of_disjoint`) and the
  A-factor cannot leave A's modes;
* ★★★ `arenaObs_kick_of_factorised` and ★★★ `recordStroke_comm_kick_of_factorised` — a B-wing
  intervention cannot steer A's reading or A's record write, **after any number of applications of
  the measurement interaction**, exactly;
* ★ `supportedOn_wingAModes_leftOp` and ★ `supportedOn_wingBModes_rightOp` — non-vacuity:
  every pair of per-wing operators gives the two factors, through `CompositeArena`'s
  `leftOp`/`rightOp`.

## What this changes for #131, and what it does not

**It changes what is assumed.** #131's standing caveat is that adjacency is *supplied* through `E`.
Here there is no `E`: the separation follows from the measurement interaction being a product over
the wings. The assumption moves from "the graph has no A–B edge" to "the apparatus couples each wing
to its own pointer", which is a statement about the experiment rather than about an auxiliary graph.

⚠️ **It is still an assumption.** `localDeisolation_factorises` holds *by construction* — LF6-A.3
chose a product dilation. So locality is still put in, just somewhere more physical. Deriving it is
`R-016`, and nothing here touches that.

⚠️ **Weaker than a cone, and deliberately.** A product unitary gives **static** locality — disjoint
supports commute — not a propagating bound with a velocity. That is the right statement for one
measurement: the question is whether the two wings' records can influence each other, and disjoint
support answers it exactly. A propagating cone matters only for a dynamics that is *not* a product,
i.e. if the wings were coupled, which this experiment says they are not.
[`TwoWingCone.lean`](TwoWingCone.lean) keeps the graded version for that case; neither file
supersedes the other.

⚠️ **The index alignment with `LF6` is checked but not formalised.** `LF6.jointDilEquiv` regroups
`((sᴀ,pᴀ),(s_b,p_b)) ↦ ((sᴀ,s_b),(pᴀ,p_b))`, so the dilated space is four `Fin 2` factors grouped per
wing, and `FieldConfig 4 2 = Fin 4 → Fin 2` is four `Fin 2` factors indexed by mode; under
`modes 0,1 = (sysA, ptrA)` and `modes 2,3 = (sysB, ptrB)` the de-isolation's tensor split *is* the
wing mode split, which is why `wingAModes = {0,1}` was the right choice. **Carrying
`localFlowUnitary` itself across that alignment is bookkeeping this file does not do**: the theorems
below are stated for *any* wing-factorised flow and instantiated at `leftOp`/`rightOp`, not at
`localFlowUnitary`. Until that is done, "the de-isolation flow satisfies the hypothesis" is a
checked claim about index conventions, not a theorem.

References: [`TwoWingCone.lean`](TwoWingCone.lean) (`wingAModes`, `wingBModes`, and the graph route
this is the alternative to), [`CompositeArena.lean`](CompositeArena.lean) (`leftModes`,
`rightModes`, `leftOp`, `rightOp`, `leftOp_supportedOn`, `composite_no_signalling` — the static
version of the same idea), [`SupportSpreading.lean`](SupportSpreading.lean)
(`heisenberg_eq_of_disjoint`, `heisenberg_supportedOn_union`),
[`ArenaBridge.lean`](ArenaBridge.lean) (`arenaObs_kick_of_disjointSupport`),
`LF6/LocalDeisolationFlow.lean` (`localFlowUnitary`, `localDeisolation_factorises`, `jointDilEquiv`
— the flow this is about, not imported); `specs/CSD-CHARTER.md` ("one flow and one microstate");
`specs/BACKLOG.md` #139, #131, `R-016`.
-/

@[expose] public section

open Matrix

noncomputable section

namespace CSD.CV

/-! ### The two files' mode regions agree -/

/-- ★★ **`CompositeArena`'s left block is A's wing.** So the composite machinery and
[`TwoWingCone.lean`](TwoWingCone.lean) are about the same modes, and nothing has been re-indexed
between them. -/
theorem leftModes_two_two : leftModes 2 2 = wingAModes := by decide

/-- ★★ **And the right block is B's wing.** -/
theorem rightModes_two_two : rightModes 2 2 = wingBModes := by decide

/-! ### The cone, from factorisation -/

variable {K N : ℕ} {S T : Finset (Fin K)}

/-- ★★★ **A wing-factorised flow cannot spread an A-local observable.** At every power of
`U_A * U_B`, the Heisenberg-evolved observable is still supported on A's modes: the B-factor acts
trivially on it (`heisenberg_eq_of_disjoint`) and the A-factor cannot take it outside A.

This is what replaces a light cone. There is no ball to grow — not because the propagation is slow,
but because the interaction does not couple the wings at all. -/
theorem supportedOn_heisenberg_pow_of_factorised (hST : Disjoint S T)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn S A)
    {UA UB : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    (hUA : SupportedOn S UA.val) (hUB : SupportedOn T UB.val) (n : ℕ) :
    SupportedOn S (heisenberg ((UA * UB) ^ n) A) := by
  have hcomm : Commute UA UB := by
    refine Subtype.ext ?_
    show UA.val * UB.val = UB.val * UA.val
    exact commute_of_disjointSupport hST hUA hUB
  have hpow : (UA * UB) ^ n = UA ^ n * UB ^ n := hcomm.mul_pow n
  have hval : ∀ (V : Matrix.unitaryGroup (FieldConfig K N) ℂ) (m : ℕ),
      ((V ^ m).val) = V.val ^ m := by
    intro V m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, pow_succ, ← ih]; rfl
  have hUAn : SupportedOn S (UA ^ n).val := by
    rw [hval]
    exact hUA.pow n
  have hUBn : SupportedOn T (UB ^ n).val := by
    rw [hval]
    exact hUB.pow n
  have hinner : SupportedOn S (heisenberg (UA ^ n) A) := by
    simpa using heisenberg_supportedOn_union hUAn hA
  rw [hpow, heisenberg_mul, heisenberg_eq_of_disjoint hST hUBn hinner]
  exact hinner

/-- ★★★ **A B-wing intervention cannot steer A's reading, exactly, after any number of applications
of a wing-factorised flow.** No graph, no period budget, no error term. -/
theorem arenaObs_kick_of_factorised [NeZero N] (hST : Disjoint S T)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn S A)
    {UA UB : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    (hUA : SupportedOn S UA.val) (hUB : SupportedOn T UB.val) (n : ℕ)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (p : FieldArena K N) :
    arenaObs (heisenberg ((UA * UB) ^ n) A) (arenaKick W p)
      = arenaObs (heisenberg ((UA * UB) ^ n) A) p :=
  arenaObs_kick_of_disjointSupport hST
    (supportedOn_heisenberg_pow_of_factorised hST hA hUA hUB n) hW p

/-- ★★★ **And it cannot steer A's record write.** The fibred form, which is the statement #131's
obligation (3) asks for — here with the separation read off the measurement interaction rather than
off a supplied graph. -/
theorem recordStroke_comm_kick_of_factorised [NeZero N] (hST : Disjoint S T)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn S A)
    {UA UB : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    (hUA : SupportedOn S UA.val) (hUB : SupportedOn T UB.val) (n : ℕ)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (g : ℝ → RecordFibre) (x : FibredFieldArena K N) :
    recordStroke (heisenberg ((UA * UB) ^ n) A) g (fibredKick W x)
      = fibredKick W (recordStroke (heisenberg ((UA * UB) ^ n) A) g x) :=
  recordStroke_comm_kick hST
    (supportedOn_heisenberg_pow_of_factorised hST hA hUA hUB n) hW g x

/-! ### Non-vacuity: every pair of per-wing unitaries gives such a flow -/

/-- ★ **The A-wing factor of a product flow**, as an operator on the four-mode configuration space:
`CompositeArena`'s `leftOp`, whose support is A's modes by `leftOp_supportedOn`. -/
theorem supportedOn_wingAModes_leftOp (U : Matrix (FieldConfig 2 2) (FieldConfig 2 2) ℂ) :
    SupportedOn wingAModes (leftOp (K₂ := 2) U) := by
  rw [← leftModes_two_two]
  exact leftOp_supportedOn U

/-- ★ **The B-wing factor.** -/
theorem supportedOn_wingBModes_rightOp (U : Matrix (FieldConfig 2 2) (FieldConfig 2 2) ℂ) :
    SupportedOn wingBModes (rightOp (K₁ := 2) U) := by
  rw [← rightModes_two_two]
  exact rightOp_supportedOn U

end CSD.CV

end

end
