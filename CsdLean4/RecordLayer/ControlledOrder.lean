/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ControlledStep
public import CsdLean4.RecordLayer.ActivatedWrite

/-!
# The second pointer displays only after the first has displayed

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer. BACKLOG #440, third brick (Task 5 of the author's plan "Unified
records, quantum measurement and emergent spacetime", workstream R; obligations UO-24 and
UO-25, item (5); the term of UA-20; `specs/unified-records-spacetime-task-plans.md` §3).

`LF4/ControlledStep.lean` shows that on the controlled arena the second pointer does not
move while the window of the first pointer's angle is shut. This module turns that into an
order of two displays in one run: if the window vanishes off a set `disp₁` of the first
pointer's positions, and the second pointer starts outside a set `disp₂` and is in it at
the flow time `T ≥ 0`, then the first pointer was in `disp₁` at some flow time in `[0, T]`.

* ★★★ `controlled_display_after_first` — the statement for any two sets of pointer
  positions;
* ★★ `controlled_displayArc_after_first` — both sets the displaying arc `displayArc` of the
  tick records.

## Honest scope

⚠️ **On the fibres `g(ψ₂) = 0`**, a null set of the second pointer's conserved angles, where
the first apparatus runs as if alone. Off them nothing is shown.

⚠️ **Positions of pointers in one run of the flow, not `RecordedFact`s.** No tick readout
and no record semantics are built for the controlled arena, so this is not yet "the second
recorded fact is established after the first".

⚠️ **The window is assumed to vanish off `disp₁`.** A smooth periodic profile supported in
the displaying arc is not exhibited here.

⚠️ **Only the order.** It does not say the second pointer does display once the first has;
the times are flow times and their order is the order of the flow parameter (UA-7).

⚠️ **UA-20.** The first pointer's moving angle is in the energy.

References: `specs/BACKLOG.md` #440; `specs/unified-record-spacetime-plan.md` (UA-7, UA-20,
UO-24, UO-25, UD-233, UD-241); `specs/unified-records-spacetime-task-plans.md` (§3);
`LF4/ControlledStep.lean` (`controlledEnergy`,
`hamiltonianFlow_controlledEnergy_of_lift_eq_zero`,
`controlled_pointer_fixed_of_window_eq_zero`); `RecordLayer/ActivatedWrite.lean`
(`displayArc`); `specs/future-work.md`.
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory CSD.LF4
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

noncomputable section

namespace CSD.RecordLayer

variable {N : ℕ} {f g b : ℝ → ℝ} {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
  (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- ★★★ **The second pointer displays only after the first has displayed.** On the
controlled arena, on a fibre where the second pointer's profile vanishes: if the window `b`
vanishes at every position of the first pointer outside `disp₁`, and the second pointer
starts outside `disp₂` and is in `disp₂` at the flow time `T ≥ 0`, then the first pointer is
in `disp₁` at some flow time of `[0, T]`. -/
theorem controlled_display_after_first (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hb : Function.Periodic b 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hcb : ContDiff ℝ ∞ b)
    (x : CPN (N + 1)) (θ ψ : KTorus) (h0 : hg.lift ψ.2 = 0) {disp₁ disp₂ : Set KTorus}
    (hwin : ∀ q : KTorus, q ∉ disp₁ → hb.lift q.1 = 0) (hψ : ψ ∉ disp₂) {T : ℝ}
    (hT : 0 ≤ T)
    (hdisp : ((stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) T ((x, θ), ψ)).2 ∈ disp₂) :
    ∃ u ∈ Set.Icc (0 : ℝ) T,
      ((stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) u ((x, θ), ψ)).1.2 ∈ disp₁ := by
  by_contra hcon
  refine hψ ?_
  have hshut : ∀ u ∈ Set.uIcc (0 : ℝ) T,
      hb.lift (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x u : ℝ) :
        AddCircle (1 : ℝ))) = 0 := by
    intro u hu
    rw [Set.uIcc_of_le hT] at hu
    refine hwin (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x u : ℝ) :
        AddCircle (1 : ℝ)), θ.2) fun hmem => hcon ⟨u, hu, ?_⟩
    rw [hamiltonianFlow_controlledEnergy_of_lift_eq_zero C hA hB hf hg hb hc hcg hcb u x θ ψ h0]
    exact hmem
  rw [controlled_pointer_fixed_of_window_eq_zero C hA hB hf hg hb hc hcg hcb T x θ ψ h0 hshut]
    at hdisp
  exact hdisp

/-- ★★ **With the displaying arc of the tick records.** If the window vanishes off the
displaying arc, the second pointer starts outside the arc and is in it at `T ≥ 0`, then the
first pointer is in the arc at some flow time of `[0, T]`. -/
theorem controlled_displayArc_after_first (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hb : Function.Periodic b 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hcb : ContDiff ℝ ∞ b)
    (x : CPN (N + 1)) (θ ψ : KTorus) (h0 : hg.lift ψ.2 = 0)
    (hwin : ∀ q : KTorus, q ∉ displayArc → hb.lift q.1 = 0) (hψ : ψ ∉ displayArc) {T : ℝ}
    (hT : 0 ≤ T)
    (hdisp : ((stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) T ((x, θ), ψ)).2 ∈ displayArc) :
    ∃ u ∈ Set.Icc (0 : ℝ) T,
      ((stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) u ((x, θ), ψ)).1.2
          ∈ displayArc :=
  controlled_display_after_first C hA hB hf hg hb hc hcg hcb x θ ψ h0 hwin hψ hT hdisp

end CSD.RecordLayer

end
