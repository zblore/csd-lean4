/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusArrivalInstance
public import CsdLean4.RecordLayer.UnifiedEmissionReading

/-!
# Arrival and display on the torus: the profile and the Clifford family exhibited

**Category:** 7-SigmaLayer. BACKLOG #297, sixth brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

`RecordLayer/TorusArrivalInstance.lean` proves arrival, display and the two recorded counts
for an instance with numbers, with the pointer's profile, the Clifford family and the spinor
as hypotheses. Here they are exhibited.

* `pauli_two_mulVec_spinUp`, `star_spinUp_dotProduct` — the spinor `(1, 0)` is fixed by `σ_z`
  and has norm one;
* `arrivalFibre`, `arrivalFibre_mem_readyArc` — the pointer's start `(1/6, 0)`, a ready
  pointer;
* `arrivalRate_scaledTrainF` — for the profile `g · trainF` with `g = 4π/(75M)`, on the
  fibre `θ₂ = 0`, the rate is `−2 f'(0) = 8π/(75M)`;
* `arrivalPacket_ne_zero` — the flat packet of the instance for `σ_x`, `σ_y`, `σ_z` and the
  spinor `(1, 0)` is not zero;
* ★★★ `torusDetector_arrival_exhibited` — **the statement of
  `torusDetector_arrival_instance` for the Clifford family `σ_x`, `σ_y` with `σ_z`, the
  spinor `(1, 0)`, the profile `(4π/(75M)) · trainF` and the pointer's start `(1/6, 0)`. The
  only parameters left are the ring size `L = 8M` with `M ≥ 4·10⁶`, the labelling `e` of
  the basis and the base point `p₀` of the measure.**

## Honest scope

⚠️ **One fibre.** The pointer's conserved angle is `θ₂ = 0`, where the profile vanishes. This
is one point of the circle, a null set.

⚠️ **The labelling `e` is a parameter.** No bijection of `(Fin 2 → ZMod L) × Fin 2` with
`Fin (N + 1)` is chosen; one exists exactly when `N + 1 = 2 L²`.

⚠️ **The detector is the set of sites the box sweeps.** It is not a box of sites given in
advance, and its number of sites is not computed.

⚠️ **Between `3M/8` and `9M/8` nothing is said about the display.** No time of arrival.

⚠️ **Not composed with the bound against the graph distance** (`torusDetector_not_displayed`).

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297; `specs/unified-record-spacetime-plan.md` (UD-243,
UD-244); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/TorusArrivalInstance.lean` (`torusDetector_arrival_instance`,
`flatPacketD_ne_zero`); `CV/DiracLatticeD.lean` (`cliffordTwo`, `pauli`);
`RecordLayer/UnifiedEmissionReading.lean` (`scaledTrainF`, `scaledTrainF_lift_zero`,
`scaledTrainF_deriv_lift_zero`); `RecordLayer/ShearWitness.lean` (`readyArc`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The spinor -/

/-- The spinor `(1, 0)` is fixed by `σ_z`. -/
theorem pauli_two_mulVec_spinUp : pauli 2 *ᵥ (![1, 0] : Fin 2 → ℂ) = ![1, 0] := by
  ext i
  fin_cases i <;> simp [pauli, diracSz, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The spinor `(1, 0)` has norm one. -/
theorem star_spinUp_dotProduct : star (![1, 0] : Fin 2 → ℂ) ⬝ᵥ ![1, 0] = 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-! ### The pointer -/

/-- The pointer's start: displayed angle `1/6`, conserved angle `0`. -/
def arrivalFibre : KTorus := (((1 / 6 : ℝ) : CircleFibre), (0 : AddCircle (1 : ℝ)))

/-- The start is a ready pointer. -/
theorem arrivalFibre_mem_readyArc : arrivalFibre ∈ readyArc 2 := by
  show rep (((1 / 6 : ℝ) : CircleFibre)) ∈ Ioc (0 : ℝ) (shearWidth 2)
  rw [rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩, shearWidth_two]
  constructor <;> norm_num

/-- For the profile `g · trainF` with `g = 4π/(75M)`, on the fibre `θ₂ = 0`, the rate is
`−2 f'(0) = 8π/(75M)`. -/
theorem arrivalRate_scaledTrainF (M : ℕ) :
    -2 * (scaledTrainF_periodic (4 * Real.pi / (75 * M))).deriv_periodic.lift
        (0 : AddCircle (1 : ℝ)) = 8 * Real.pi / (75 * M) := by
  rw [scaledTrainF_deriv_lift_zero]
  ring

/-! ### The instance -/

section Exhibit

variable {L : ℕ} [NeZero L] {N : ℕ}

/-- The flat packet of the instance, for `σ_x`, `σ_y` with `σ_z` and the spinor `(1, 0)`, is
not zero. -/
theorem arrivalPacket_ne_zero {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) :
    (WithLp.toLp 2 (packetD (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1
        (![1, 0] : Fin 2 → ℂ) (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
        (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0) :
      EuclideanSpace ℂ ((Fin 2 → ZMod L) × Fin 2)) ≠ 0 :=
  flatPacketD_ne_zero cliffordTwo pauli_two_mulVec_spinUp star_spinUp_dotProduct one_pos _
    (fun _ => by norm_num) (fun _ => by omega)

/-- ★★★ **Arrival and display on the torus, with nothing assumed of the field or the
pointer.** Two dimensions, `L = 8M` sites per axis with `M ≥ 4·10⁶`, `J = 2`, `μ = 1`, the
Clifford family `σ_x`, `σ_y` with `σ_z`, the spinor `(1, 0)`. The flat packet has `400`
momenta per axis starting at `(M, 0)`; the detector is on the sites its moving box of sides
`3/4` sweeps during `[9M/8, 9M/4]`. The pointer's profile is `(4π/(75M)) · trainF` and it
starts at `(1/6, 0)`. Then the pointer is not displayed at any flow time up to `3M/8`, it is
displayed at `9M/4`, and the counts `0` at `3M/8` and `1` at `9M/4` are a record history of
the run's start. -/
theorem torusDetector_arrival_exhibited {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (e : (Fin 2 → ZMod L) × Fin 2 ≃ Fin (N + 1)) (p₀ : CPN (N + 1)) :
    ((∀ u, 0 ≤ u → u ≤ 3 * (M : ℝ) / 8 →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e
            (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (sweptBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 3 / 4)
              (9 * (M : ℝ) / 8) (9 * (M : ℝ) / 4) : Set (Fin 2 → ZMod L))))
          (scaledTrainF_periodic (4 * Real.pi / (75 * M)))
          (contDiff_scaledTrainF (4 * Real.pi / (75 * M)))) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)),
          arrivalFibre)).2 ∉ displayArc)
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e
            (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (sweptBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 3 / 4)
              (9 * (M : ℝ) / 8) (9 * (M : ℝ) / 4) : Set (Fin 2 → ZMod L))))
          (scaledTrainF_periodic (4 * Real.pi / (75 * M)))
          (contDiff_scaledTrainF (4 * Real.pi / (75 * M))))
        (9 * (M : ℝ) / 4)
        (idxArenaEquiv e (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)),
          arrivalFibre)).2 ∈ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)),
          arrivalFibre) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e
              (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
            (Matrix.reindex e e (siteSetProj Prod.fst
              (sweptBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 3 / 4)
                (9 * (M : ℝ) / 8) (9 * (M : ℝ) / 4) : Set (Fin 2 → ZMod L))))
            (scaledTrainF_periodic (4 * Real.pi / (75 * M)))
            (contDiff_scaledTrainF (4 * Real.pi / (75 * M))))
            p₀).semantics
          [TickReadout.startFact () (3 * (M : ℝ) / 8) 0,
            TickReadout.startFact () (9 * (M : ℝ) / 4) 1] :=
  torusDetector_arrival_instance hL hM e cliffordTwo pauli_two_mulVec_spinUp
    star_spinUp_dotProduct (scaledTrainF_periodic (4 * Real.pi / (75 * M)))
    (contDiff_scaledTrainF (4 * Real.pi / (75 * M))) p₀ (arrivalPacket_ne_zero hL hM)
    arrivalFibre_mem_readyArc (scaledTrainF_lift_zero (4 * Real.pi / (75 * M)))
    (arrivalRate_scaledTrainF M)

end Exhibit

end CSD.RecordLayer

end
