/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ArenaTorus
public import CsdLean4.RecordLayer.JointFlowTransfer
public import CsdLean4.Mathlib.MeasureTheory.InvariantTwist

/-!
# RecordLayer/JointLift: a back-reacting joint lift of the measurement stroke, on the arena

**Category:** dynamical measurement — `specs/BACKLOG.md` §A, the **instance** the
conditional transfer `JointFlowTransfer.lean` was waiting for.

## What this is

`JointFlowTransfer.lean` proved that *any* map `Φ` satisfying `IsJointLift c ε Φ` — pointer
driven by the fibrewise propagator, context rates and register conserved — inherits landing,
the `ε`-Born sandwich and the moment-marginal law. Until now the only instance was the
fibrewise witness itself (`isJointLift_pointerEvolve`), whose base does not move at all.

`jointLift c ε Δ` is a family of instances whose base **does** move:

  `jointLift c ε Δ y = pointerEvolve c ε (torusAct (Δ (conservedData c y)) y)`.

The point `y` is first twisted by a torus element `Δ(m, θ₁, q)` — a *shift* that may depend
on all the conserved data (the context rates `m = c.rate y.1.1`, the register `θ₁`, and the
pointer `q`) but on nothing else — and then the pointer is driven as before. Because the
twist moves the base only along its moment fibre and translates only the conjugate `θ₂`,
everything the stroke reads is untouched, and:

* ★★ `isJointLift_jointLift` — for every torus-invariant context and every shift `Δ`,
  `jointLift c ε Δ` **is** a joint lift. Hence, with no further work,
  `(isJointLift_jointLift …).landing`, `.born_lower`, `.born_upper`, `.outcomeSector_eq`,
  `.moment_marginal_unchanged` all hold for it.
* ★★ `jointLift_measurePreserving` — for every **measurable** shift, `jointLift c ε Δ`
  preserves the arena Liouville measure. This is the arena-level Liouville theorem for the
  back-reacting map, obtained without disintegrating along the moment fibres: the general
  invariant-twist lemma `MeasurePreserving.vadd_twist_of_invariant` applied to the
  arena torus of `ArenaTorus.lean`, composed with `pointerEvolve_measurePreserving`.
* `jointLift_fst`, `jointLift_conjugate` — the base is rotated by `phaseUnitary (Δ …).1`
  and `θ₂` is translated by `(Δ …).2`; `jointLift_base_moves_of_ne` gives the concrete
  base-moves witness: wherever the shift's phases differ on two coordinates supporting the
  state, the ontic base point genuinely moves.
* `jointLift_eq_pointerEvolve_of_shift_eq_zero` — where the shift vanishes the joint lift
  *is* the fibrewise witness, so the latter is the special case `Δ = 0`
  (`jointLift_zero`).

## What this does and does not settle

The shift `Δ` is a **parameter** here. This module proves that the whole class of
conserved-data twists is harmless to records, Born, and Liouville measure — the structural
statement "back-reaction lives in the torus directions and is invisible to the record". Which
`Δ` the interaction Hamiltonian actually produces is a separate question: the chart
computation in `SigmaLayer/UntriggeredFlow.lean` shows the conjugate coordinate absorbs
`-∫ ∂_m 𝓗`, and `RecordLayer/HamiltonianShift.lean` builds that shift from the pointer
trajectory. Nothing in this module identifies `jointLift` with the time-`1` map of a
Hamiltonian flow on the arena manifold (⚠️ RESIDUE(R-016)).

## References

`specs/frozen-base-obstruction-scoping.md` (brick 3); `specs/future-work.md`;
`RecordLayer/JointFlowTransfer.lean` (`IsJointLift`, the transfer theorems);
`RecordLayer/ArenaTorus.lean` (`torusAct`, `torusAct_measurePreserving`,
`ContextField.TorusInvariant`); `Mathlib/MeasureTheory/InvariantTwist.lean`
(`MeasurePreserving.vadd_twist_of_invariant`); `RecordLayer/PointerWeights.lean`
(`pointerEvolve`, `pointerEvolve_measurePreserving`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix.UnitaryGroup

variable {N : ℕ}

/-! ### The conserved data -/

/-- The data of an arena point that the measurement stroke conserves and a shift may read:
the context rates, the register coordinate, and the pointer. -/
abbrev ConservedData (N : ℕ) : Type := (Fin N → ℝ) × AddCircle (1 : ℝ) × Pointer N

/-- Read the conserved data of an arena point. -/
def conservedData (c : ContextField N) (y : PointerArena N N) : ConservedData N :=
  (c.rate y.1.1, y.1.2.1, y.2)

theorem measurable_conservedData (c : ContextField N) : Measurable (conservedData c) :=
  (measurable_pi_iff.mpr fun j => (c.measurable_rate j).comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)

/-- The torus action does not change the conserved data — for a torus-invariant context. -/
theorem conservedData_torusAct {c : ContextField N} (hct : c.TorusInvariant)
    (g : ArenaTorus N) (y : PointerArena N N) :
    conservedData c (torusAct g y) = conservedData c y := by
  unfold conservedData
  rw [torusAct_register, torusAct_snd, torusAct_fst_fst]
  congr 1
  funext j
  exact hct g.1 y.1.1 j

/-- The weights read only conserved data, so the torus action does not change them. -/
theorem pointerWeights_torusAct {c : ContextField N} (hct : c.TorusInvariant) (ε : ℝ)
    (g : ArenaTorus N) (y : PointerArena N N) :
    pointerWeights c ε (torusAct g y).1 = pointerWeights c ε y.1 := by
  have hrate : c.rate (torusAct g y).1.1 = c.rate y.1.1 := by
    rw [torusAct_fst_fst]
    funext j
    exact hct g.1 y.1.1 j
  funext j
  unfold pointerWeights
  rw [hrate, torusAct_register]

/-! ### The joint lift -/

/-- **The joint lift with shift `Δ`.** Twist the point by the torus element the conserved data
prescribes, then drive the pointer with the fibrewise propagator. -/
noncomputable def jointLift (c : ContextField N) (ε : ℝ) (Δ : ConservedData N → ArenaTorus N)
    (y : PointerArena N N) : PointerArena N N :=
  pointerEvolve c ε (torusAct (Δ (conservedData c y)) y)

variable (c : ContextField N) (ε : ℝ) (Δ : ConservedData N → ArenaTorus N)

/-- The base is rotated along its moment fibre and `θ₂` is translated; the register is fixed. -/
theorem jointLift_fst (y : PointerArena N N) :
    (jointLift c ε Δ y).1
      = (phaseUnitary (Δ (conservedData c y)).1 • y.1.1,
          (y.1.2.1, y.1.2.2 + (Δ (conservedData c y)).2)) := rfl

theorem jointLift_base (y : PointerArena N N) :
    (jointLift c ε Δ y).1.1 = phaseUnitary (Δ (conservedData c y)).1 • y.1.1 := rfl

theorem jointLift_register (y : PointerArena N N) :
    (jointLift c ε Δ y).1.2.1 = y.1.2.1 := rfl

/-- The conjugate coordinate absorbs the shift. -/
theorem jointLift_conjugate (y : PointerArena N N) :
    (jointLift c ε Δ y).1.2.2 = y.1.2.2 + (Δ (conservedData c y)).2 := rfl

/-- Where the shift vanishes, the joint lift is the fibrewise witness. -/
theorem jointLift_eq_pointerEvolve_of_shift_eq_zero {y : PointerArena N N}
    (h : Δ (conservedData c y) = 0) : jointLift c ε Δ y = pointerEvolve c ε y := by
  unfold jointLift
  rw [h, torusAct_zero]

/-- The fibrewise witness is the joint lift with zero shift. -/
@[simp] theorem jointLift_zero : jointLift c ε (fun _ => 0) = pointerEvolve c ε := by
  funext y
  exact jointLift_eq_pointerEvolve_of_shift_eq_zero c ε _ rfl

/-- **The joint lift is a joint lift** (for a torus-invariant context). All of
`JointFlowTransfer.lean` — landing, the `ε`-Born sandwich, the outcome-sector identity, the
moment-marginal law — now applies to a map whose base genuinely moves. -/
theorem isJointLift_jointLift {c : ContextField N} (hct : c.TorusInvariant) :
    IsJointLift c ε (jointLift c ε Δ) where
  pointer_eq y := by
    show couplingUU (pointerWeights c ε (torusAct (Δ (conservedData c y)) y).1) • y.2
      = couplingUU (pointerWeights c ε y.1) • y.2
    rw [pointerWeights_torusAct hct]
  rate_conserved y j := by
    rw [jointLift_base]
    exact hct _ _ j
  register_conserved _ := rfl

/-- **Liouville's theorem for the back-reacting joint lift.** For every measurable shift, the
joint lift preserves the arena Liouville measure `μ_FS ⊗ vol_{T²} ⊗ μ_FS^{ptr}`. The proof
never disintegrates along the moment fibres: the twist `y ↦ torusAct (Δ (conservedData c y)) y`
preserves measure by `MeasurePreserving.vadd_twist_of_invariant` — every `torusAct g` does,
Haar measure on the arena torus is a left-invariant probability, and the conserved data is
torus-invariant — and the fibrewise propagator preserves it by
`pointerEvolve_measurePreserving`. -/
theorem jointLift_measurePreserving {c : ContextField N}
    (hc : ∀ j, Continuous fun p => c.rate p j) (hct : c.TorusInvariant)
    {Δ : ConservedData N → ArenaTorus N} (hΔ : Measurable Δ)
    (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    MeasurePreserving (jointLift c ε Δ) (pointerLiouville p₀ q₀) (pointerLiouville p₀ q₀) := by
  have hT : MeasurePreserving (fun y => torusAct (Δ (conservedData c y)) y)
      (pointerLiouville p₀ q₀) (pointerLiouville p₀ q₀) :=
    MeasurePreserving.vadd_twist_of_invariant (torusHaar N) measurable_torusAct torusAct_add
      (fun g => torusAct_measurePreserving g p₀ q₀) (hΔ.comp (measurable_conservedData c))
      (fun g y => by rw [conservedData_torusAct hct])
  exact (pointerEvolve_measurePreserving c hc ε p₀ q₀).comp hT

/-- **The base moves.** Wherever the shift's phases differ on two coordinates that support the
state, the joint lift displaces the ontic base point — the back-reaction the fibrewise
witness could not show. (Together with `isJointLift_jointLift`, this is "the base moves and
the record survives" on the arena, not in a chart.) -/
theorem jointLift_base_moves_of_ne {y : PointerArena N N}
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) (hy : y.1.1 = Projectivization.mk ℂ v hv)
    {j k : Fin N} (hj : v j ≠ 0) (hk : v k ≠ 0)
    (hg : circlePhase ((Δ (conservedData c y)).1 j) ≠ circlePhase ((Δ (conservedData c y)).1 k)) :
    (jointLift c ε Δ y).1.1 ≠ y.1.1 := by
  rw [jointLift_base, hy]
  exact phaseUnitary_smul_mk_ne_of_ne _ hv hj hk hg

end CSD.RecordLayer
