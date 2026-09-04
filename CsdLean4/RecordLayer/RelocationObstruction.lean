/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerLuders
public import CsdLean4.Mathlib.Topology.Homotopy.FactorExchangeObstruction
public import CsdLean4.Mathlib.Topology.Homotopy.CircleFundamentalGroup

/-!
# SigmaLayer/RelocationObstruction: the collapse stroke is not generated

**Category:** dynamical measurement — the negative half of the
Hamiltonian-origin question.

`PointerGeneration.lean` closed the *record-creating* half: `rampedU_schrodinger`
exhibits the smooth witness's stroke as the flow of an explicit Hermitian
generator, so record creation is dynamics rather than a map wearing a
dynamical label. The *collapse* half was left as `pointerRelocate`, a case
split on the readout, proved measure-preserving by a partition argument.
This module shows that gap cannot be closed as posed: the bank-swap relocation
is **not** the time-one map of any flow, and neither is the obvious
non-permutation alternative.

## The two horns

* ★★ `pointerBankSwap_not_flow_time_one` — the relocation used on the record
  cylinders exchanges the system factor with bank slot `j`. Embed a circle in
  the system's torus coordinate; after the exchange that coordinate reads slot
  `j`, which the embedding held constant. So the exchange collapses a section
  onto a non-contractible space, and `not_isFlowTimeOne_of_section_collapsed`
  applies. Note this is *not* the flux obstruction of
  `PiecewiseHamiltonian.lean`: flux obstructs a symplectomorphism within the
  identity component, whereas the exchange never reaches that component, and
  the `H¹(ℂℙ^K) = 0` escape that saved the record stroke does not help because
  the obstruction lives in the bank's product structure.
* ★ `pointerImprint_not_injective` — the alternative that avoids permuting
  factors, writing the system into a slot rather than exchanging with it, is
  not injective, so it is not a homeomorphism, so it is not a flow map either.

## What this does and does not say

It says the *swap architecture's* collapse stroke cannot become dynamics, and
that the naive repair fails for an independent reason. Together with
`swap_not_blockLuders` (`DegenerateLuders.lean`), which shows the same
architecture cannot do degenerate Lüders for any fixed calibration, the swap
route is a witness that cannot be generated. It does **not** say collapse is
undynamical in general: a generated relocation must be a bijection that is not
a factor exchange, which points at the join and phase-slot routes
(`JoinLuders.lean`, `PhaseSlot.lean`), where state-dependence is produced by
the dynamics rather than by permuting coordinates.

It also constrains record proliferation: carrier maps that relocate a record by
permuting factors inherit the first horn, and imprint-style copies inherit the
second.

## References

`RecordLayer/PointerLuders.lean` (`pointerBankSwap`, `pointerRelocate`);
`RecordLayer/PointerGeneration.lean` (`rampedU_schrodinger`, the positive half);
`RecordLayer/PiecewiseHamiltonian.lean` (the flux obstruction this is *not*);
`RecordLayer/DegenerateLuders.lean` (`swap_not_blockLuders`);
`Mathlib/Topology/Homotopy/FactorExchangeObstruction.lean`;
`Mathlib/Topology/Homotopy/CircleFundamentalGroup.lean`; `specs/BACKLOG.md`.
-/

@[expose] public section

open ContinuousMap

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The exchange is continuous -/

/-- The bank swap is continuous: it permutes coordinates. -/
theorem continuous_pointerBankSwap (j : Fin N) :
    Continuous (pointerBankSwap (N := N) j) := by
  unfold pointerBankSwap
  fun_prop

/-- The bank swap as a bundled continuous map. -/
def bankSwapCM (j : Fin N) : C(PointerLudersArena N, PointerLudersArena N) :=
  ⟨pointerBankSwap j, continuous_pointerBankSwap j⟩

/-! ### The section a factor exchange collapses -/

/-- Embed a circle in the **system's** first torus angle, holding every other
coordinate fixed. In particular every bank slot is held at a constant point. -/
noncomputable def torusSection (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    C(AddCircle (1 : ℝ), PointerLudersArena N) :=
  ⟨fun θ => (((p₀, (θ, (0 : AddCircle (1 : ℝ)))), q₀),
      fun _ => (p₀, ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ))))), by fun_prop⟩

/-- Read the system's first torus angle. -/
def torusReadout : C(PointerLudersArena N, AddCircle (1 : ℝ)) :=
  ⟨fun y => y.1.1.2.1, by fun_prop⟩

theorem torusReadout_comp_section (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    (torusReadout (N := N)).comp (torusSection p₀ q₀) = ContinuousMap.id _ := by
  ext θ; rfl

/-- After the exchange the readout reports **slot `j`**, which the section held
constant. This is the collapse the obstruction consumes. -/
theorem torusReadout_comp_swap_comp_section (j : Fin N) (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    (torusReadout (N := N)).comp ((bankSwapCM j).comp (torusSection p₀ q₀))
      = ContinuousMap.const _ (0 : AddCircle (1 : ℝ)) := by
  ext θ; rfl

/-! ### Horn one: the exchange is not homotopic to the identity -/

/-- ★★ **The bank swap is not homotopic to the identity.** It collapses the
circle section of `torusSection` onto a point, and the circle is not
contractible. -/
theorem pointerBankSwap_not_homotopic_id (j : Fin N) (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    ¬ Homotopic (bankSwapCM j) (ContinuousMap.id (PointerLudersArena N)) :=
  not_homotopic_id_of_section_collapsed
    (AddCircle.not_contractibleSpace one_ne_zero)
    (torusSection p₀ q₀) torusReadout (bankSwapCM j)
    (torusReadout_comp_section p₀ q₀)
    ⟨0, torusReadout_comp_swap_comp_section j p₀ q₀⟩

/-- ★★ **The bank-swap relocation is not the time-one map of any flow.**

So the collapse stroke of the swap architecture cannot be generated, in the
sense that the record-creating stroke *is* generated
(`rampedU_schrodinger`). Any jointly continuous family joining the identity to
the relocation would be a homotopy, and there is none. -/
theorem pointerBankSwap_not_flow_time_one (j : Fin N) (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    ¬ ∃ φ : C(unitInterval × PointerLudersArena N, PointerLudersArena N),
        (∀ y, φ (0, y) = pointerBankSwap j y) ∧ (∀ y, φ (1, y) = y) :=
  not_isFlowTimeOne_of_section_collapsed
    (AddCircle.not_contractibleSpace one_ne_zero)
    (torusSection p₀ q₀) torusReadout (bankSwapCM j)
    (torusReadout_comp_section p₀ q₀)
    ⟨0, torusReadout_comp_swap_comp_section j p₀ q₀⟩

/-! ### Horn two: the non-permutation alternative is not injective -/

/-- The **imprint**: copy the system into bank slot `j` without removing it.
This is the natural way to broadcast a record without permuting factors. -/
def pointerImprint (j : Fin N) (y : PointerLudersArena N) : PointerLudersArena N :=
  ((y.1.1, y.1.2), Function.update y.2 j y.1.1)

/-- ★ **The imprint is not injective**, hence not a homeomorphism, hence not the
time-one map of any flow. Two arena points differing only in slot `j` are
identified, because the imprint overwrites that slot. -/
theorem pointerImprint_not_injective (j : Fin N) (q₀ : Pointer N)
    {a b : LF4.KSigma N} (hab : a ≠ b) :
    ¬ Function.Injective (pointerImprint (N := N) j) := by
  intro hinj
  have hkey : pointerImprint j ((a, q₀), fun _ => a)
      = pointerImprint j ((a, q₀), Function.update (fun _ => a) j b) := by
    simp [pointerImprint]
  have := hinj hkey
  have hslot := congrArg (fun y : PointerLudersArena N => y.2 j) this
  simp at hslot
  exact hab hslot

/-- ★ **No flow realises the imprint at time one**, since a flow map is a
homeomorphism and the imprint is not injective. -/
theorem pointerImprint_not_homeomorph (j : Fin N) (q₀ : Pointer N)
    {a b : LF4.KSigma N} (hab : a ≠ b) :
    ¬ ∃ e : PointerLudersArena N ≃ₜ PointerLudersArena N,
        ∀ y, e y = pointerImprint j y := by
  rintro ⟨e, he⟩
  refine pointerImprint_not_injective j q₀ hab ?_
  intro y₁ y₂ h
  exact e.injective (by rw [he, he]; exact h)

end CSD.RecordLayer
