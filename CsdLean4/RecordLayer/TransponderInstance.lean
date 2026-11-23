/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderSecondLevel
public import CsdLean4.RecordLayer.TorusArrivalBox

/-!
# The second level fills after the meeting: an instance with numbers

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, items (1) and (2), the caused
return: a relation, a site and times for which the hypotheses of UD-256 hold).

`transponder_second_level_flatPacket_meeting_ge` takes as hypotheses that the packet's moving
box is apart from the transponder's sites up to `t₁` and wholly in contact from `t₂`. Here
they are met, for the two-dimensional packet of `RecordLayer/TorusArrivalBox.lean`, and the
lower bound is shown to be positive.

* `contactBox`, `contactSite`, `contactRel` — the contact region as a box of displacements
  about the origin (first coordinate on the arc `Re z > −1/4`, second on `Re z > 3/4`); the
  transponder's site, half a ring along the first axis; the relation "the messenger's
  displacement from the transponder is in the box";
* `toCircle_four_mul`, `contactRel_contactSite_iff` — on a ring of `8M` sites the messenger
  is in contact with the transponder exactly when it is on `arrivalBox`;
* `flatTailD_instance_le_fine` — for `M ≥ 10⁹` the packet's tail is at most `41/2000` up to
  the flow time `2M`;
* ★★★ `transponder_second_level_instance` — **two dimensions, `L = 8M` with `M ≥ 10⁹`,
  `J = 2`, `μ = 1`, `σ_x`, `σ_y` with `σ_z`, the flat packet of UD-243; one transponder at
  rest at `contactSite`, in its first level; the contact term with a strength `g`,
  `|g| M ≤ 1/100`. At the flow time `2M` the part of the state with the transponder in its
  second level has norm at least `(3/100) |g| M`.**

## Honest scope

⚠️ **A small amplitude.** With `|g| M ≤ 1/100` the bound is at most `3 · 10⁻⁴`. The margin
is thin: the box is apart up to `M/4` and wholly in contact only from `M`, and the whole of
the time between is counted as error. First order.

⚠️ **The contact region is wide**: more than half the ring along the first axis. It is the
region of `arrivalBox`, re-centred on the transponder.

⚠️ **One transponder, at rest, with one energy for both levels.** Its state is a basis state.

⚠️ **The amplitude in the second level, not its place.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-243, UD-245, UD-256, UD-257); `RecordLayer/TransponderSecondLevel.lean`
(`transponder_second_level_flatPacket_meeting_ge`); `RecordLayer/TorusArrivalBox.lean`
(`arrivalBox`, `arrivalBox_disjoint_movedBoxD`, `movedBoxD_subset_arrivalBox`,
`abs_angleZD_arrival_le`); `RecordLayer/TorusArrivalInstance.lean` (`flatTailD_fin_two`);
`RecordLayer/TorusArrivalExhibit.lean` (`pauli_two_mulVec_spinUp`); `CV/DiracPacketArcD.lean`
(`arcBoxD`, `mem_arcBoxD`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The contact region -/

section Contact

variable {L : ℕ} [NeZero L]

/-- **The contact region**, as a box of displacements about the origin: the first coordinate
on the arc `Re z > −1/4`, the second on the arc `Re z > 3/4`. -/
def contactBox (L : ℕ) [NeZero L] : Finset (Fin 2 → ZMod L) :=
  arcBoxD (![1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ)

/-- **The transponder's site**: half a ring of `8M` sites along the first axis. -/
def contactSite (L M : ℕ) : Fin 2 → ZMod L := ![((4 * M : ℕ) : ZMod L), 0]

/-- **In contact**: the messenger's displacement from the transponder is in the contact
region. -/
def contactRel (L : ℕ) [NeZero L] (a b : Fin 2 → ZMod L) : Prop := a - b ∈ contactBox L

instance contactRel.instDecidableRel (L : ℕ) [NeZero L] : DecidableRel (contactRel L) :=
  fun a b => inferInstanceAs (Decidable (a - b ∈ contactBox L))

/-- On a ring of `8M` sites the site `4M` is at the angle `π`. -/
theorem toCircle_four_mul {M : ℕ} (hL : L = 8 * M) (hM : 0 < M) :
    (ZMod.toCircle ((4 * M : ℕ) : ZMod L) : ℂ) = -1 := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [ZMod.toCircle_natCast]
  have e : 2 * (Real.pi : ℂ) * Complex.I * ((4 * M : ℕ) : ℂ) / (L : ℂ)
      = Real.pi * Complex.I := by
    rw [hL]
    push_cast
    field_simp
    ring
  rw [e, Complex.exp_pi_mul_I]

/-- The messenger is in contact with the transponder exactly when it is on `arrivalBox`. -/
theorem contactRel_contactSite_iff {M : ℕ} (hL : L = 8 * M) (hM : 0 < M)
    (a : Fin 2 → ZMod L) : contactRel L a (contactSite L M) ↔ a ∈ arrivalBox L := by
  have hz : (ZMod.toCircle ((a - contactSite L M) 0) : ℂ) = -(ZMod.toCircle (a 0) : ℂ) := by
    have e : a 0 = (a - contactSite L M) 0 + ((4 * M : ℕ) : ZMod L) := by
      simp [contactSite]
    have h : (ZMod.toCircle (a 0) : ℂ)
        = (ZMod.toCircle ((a - contactSite L M) 0 + ((4 * M : ℕ) : ZMod L)) : ℂ) := by
      rw [← e]
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, toCircle_four_mul hL hM, mul_neg_one] at h
    rw [h, neg_neg]
  have h1 : (a - contactSite L M) 1 = a 1 := by
    simp [contactSite]
  constructor
  · intro h
    have hc : a - contactSite L M
        ∈ arcBoxD (![1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ) := h
    show a ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ)
    refine mem_arcBoxD.2 fun i => ?_
    fin_cases i
    · have h0 : (-1 / 4 : ℝ)
          < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 0) : ℂ)).re :=
        mem_arcBoxD.1 hc 0
      rw [hz] at h0
      show (-1 / 4 : ℝ) < (star (-1 : ℂ) * (ZMod.toCircle (a 0) : ℂ)).re
      simpa using h0
    · have h0 : (3 / 4 : ℝ)
          < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 1) : ℂ)).re :=
        mem_arcBoxD.1 hc 1
      rw [h1] at h0
      exact h0
  · intro h
    have hc : a ∈ arcBoxD (![-1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ) := h
    show a - contactSite L M
      ∈ arcBoxD (![1, 1] : Fin 2 → ℂ) (![-1 / 4, 3 / 4] : Fin 2 → ℝ)
    refine mem_arcBoxD.2 fun i => ?_
    fin_cases i
    · have h0 : (-1 / 4 : ℝ) < (star (-1 : ℂ) * (ZMod.toCircle (a 0) : ℂ)).re :=
        mem_arcBoxD.1 hc 0
      show (-1 / 4 : ℝ)
        < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 0) : ℂ)).re
      rw [hz]
      simpa using h0
    · have h0 : (3 / 4 : ℝ) < (star (1 : ℂ) * (ZMod.toCircle (a 1) : ℂ)).re :=
        mem_arcBoxD.1 hc 1
      show (3 / 4 : ℝ)
        < (star (1 : ℂ) * (ZMod.toCircle ((a - contactSite L M) 1) : ℂ)).re
      rw [h1]
      exact h0

/-- With `L = 8M` and `M ≥ 10⁹` the packet's tail is at most `41/2000` up to the flow time
`2M`. -/
theorem flatTailD_instance_le_fine {M : ℕ} (hL : L = 8 * M) (hM : 1000000000 ≤ M) {τ : ℝ}
    (hτ : τ ≤ 2 * M) :
    flatTailD L 2 1 (fun _ : Fin 2 => 400) (fun _ => 400 * (2 * Real.pi / L))
        (fun _ => 3 / 4) τ ≤ 41 / 2000 := by
  have hMr : (1000000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hLr : (L : ℝ) = 8 * M := by rw [hL, Nat.cast_mul]; norm_num
  have hh : 2 * Real.pi / (L : ℝ) * M = Real.pi / 4 := by
    rw [hLr]
    field_simp
    ring
  rw [flatTailD_fin_two]
  generalize 2 * Real.pi / (L : ℝ) = x at hh ⊢
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hpos : 0 < x := by
    by_contra hx
    rw [not_lt] at hx
    nlinarith
  have h5 : x * 1000000000 ≤ x * M := mul_le_mul_of_nonneg_left hMr hpos.le
  have hs : x ≤ 8 / 10 ^ 10 := by linarith
  have h6 : τ * x ^ 2 ≤ Real.pi / 2 * x := by
    calc τ * x ^ 2 ≤ 2 * M * x ^ 2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg x)
      _ = 2 * (x * M) * x := by ring
      _ = Real.pi / 2 * x := by rw [hh]; ring
  have h7 : Real.pi / 2 * x ≤ 3.15 / 2 * (8 / 10 ^ 10) :=
    mul_le_mul (by linarith) hs hpos.le (by norm_num)
  have h8 : x ^ 2 ≤ x := by nlinarith
  linarith

end Contact

/-! ### The instance -/

section Instance

variable {L : ℕ} [NeZero L]

/-- ★★★ **The second level fills after the meeting, with numbers.** Two dimensions, `L = 8M`
sites per axis with `M ≥ 10⁹`, `J = 2`, `μ = 1`, the Clifford family `σ_x`, `σ_y` with `σ_z`,
the spinor `(1, 0)`, the flat packet of `400` momenta per axis starting at `(M, 0)`. One
transponder at rest with the energy `E` for both levels, at `contactSite`, in its first
level. The contact term has the relation `contactRel` and a strength `g` with
`|g| M ≤ 1/100`. At the flow time `2M` the part of the state with the transponder in its
second level has norm at least `(3/100) |g| M`. -/
theorem transponder_second_level_instance {M : ℕ} (hL : L = 8 * M) (hM : 1000000000 ≤ M)
    {g : ℝ} (hg : |g| * M ≤ 1 / 100) (E : ℝ) :
    3 / 100 * (|g| * M)
      ≤ Real.sqrt (∑ x, ‖((((1 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
            ⊗ₖ levelProj Unit 1)
          * exp ((2 * (M : ℝ)) • ((-Complex.I)
            • (compositeH
                (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
                (Matrix.blockDiagonal
                  fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ))
              + (g : ℂ) • gateOp Prod.fst (fun _ : Unit × Fin 2 => contactSite L M)
                  (contactRel L) (levelSwap Unit)))))
        *ᵥ fun y : ((Fin 2 → ZMod L) × Fin 2) × (Unit × Fin 2) =>
          packetD (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1
              (![1, 0] : Fin 2 → ℂ) (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
              (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0 y.1
            * (if y.2.2 = 0 then 1 else 0)) x‖ ^ 2) := by
  have hM0 : 0 < M := by omega
  have hM4 : 4000000 ≤ M := by omega
  have hMr : (1000000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have key := transponder_second_level_flatPacket_meeting_ge
    (fun _ : Unit × Fin 2 => contactSite L M) (contactRel L)
    (fun i j hij => absurd rfl hij) cliffordTwo pauli_two_mulVec_spinUp star_spinUp_dotProduct
    one_pos E g (![(M : ℤ), 0] : Fin 2 → ℤ) (Nw := fun _ => 400) (fun _ => by norm_num)
    (fun _ => by omega) (![Real.pi / 4, 0] : Fin 2 → ℝ)
    (w := fun _ => 400 * (2 * Real.pi / L)) (fun _ => by positivity)
    (abs_angleZD_arrival_le hL hM4) (γ := fun _ => 3 / 4) (fun _ => by norm_num)
    (fun q : Unit × Fin 2 => if q.2 = 0 then (1 : ℂ) else 0)
    (fun q hq => by simp [hq])
    (by simp [Fintype.sum_prod_type, Fin.sum_univ_two])
    ({contactSite L M} : Finset (Fin 2 → ZMod L))
    (fun q hq => absurd (Finset.mem_singleton_self _) hq)
    (t₁ := (M : ℝ) / 4) (t₂ := (M : ℝ)) (t := 2 * (M : ℝ)) (by positivity) (by linarith)
    (by linarith)
    (fun s hs hs1 a ha b hb hab => by
      rw [Finset.mem_singleton.1 hb] at hab
      exact Finset.disjoint_left.1 (arrivalBox_disjoint_movedBoxD hL hM4 hs hs1)
        ((contactRel_contactSite_iff hL hM0 a).1 hab) ha)
    (fun s hs hst a ha b hb => by
      rw [Finset.mem_singleton.1 hb]
      exact (contactRel_contactSite_iff hL hM0 a).2
        (movedBoxD_subset_arrivalBox hL hM4 hs hst ha))
  refine le_trans ?_ key
  -- the numbers
  have hT1 := flatTailD_instance_le_fine (L := L) hL hM (τ := (M : ℝ) / 4) (by linarith)
  have hT2 := flatTailD_instance_le_fine (L := L) hL hM (τ := 2 * (M : ℝ)) le_rfl
  have hs1 : Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 4)) ≤ 1432 / 10000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have hs2 : Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) (2 * (M : ℝ))) ≤ 1432 / 10000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have hn1 := Real.sqrt_nonneg (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 4))
  have hn2 := Real.sqrt_nonneg (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) (2 * (M : ℝ)))
  generalize Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) ((M : ℝ) / 4)) = a at hs1 hn1 ⊢
  generalize Real.sqrt (flatTailD L 2 1 (fun _ : Fin 2 => 400)
      (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4) (2 * (M : ℝ))) = b at hs2 hn2 ⊢
  have hP0 : 0 ≤ |g| * M := mul_nonneg (abs_nonneg g) hMpos.le
  have hE : |g| * (2 * (M : ℝ) - M) - |g| * (a * ((M : ℝ) / 4) + ((M : ℝ) - M / 4))
        - |g| * (b * (2 * (M : ℝ) - M))
        - |g| * (|g| * (a * ((M : ℝ) / 4) + (2 * (M : ℝ) - M / 4))) * (2 * M)
      = |g| * M - |g| * M * (a / 4 + 3 / 4) - |g| * M * b
        - 2 * (|g| * M) * (|g| * M) * (a / 4 + 7 / 4) := by ring
  rw [hE]
  generalize |g| * (M : ℝ) = P at hg hP0 ⊢
  have e1 : P * (a / 4 + 3 / 4) ≤ P * (7858 / 10000) :=
    mul_le_mul_of_nonneg_left (by linarith) hP0
  have e2 : P * b ≤ P * (1432 / 10000) := mul_le_mul_of_nonneg_left hs2 hP0
  have e3 : 2 * P * P * (a / 4 + 7 / 4) ≤ 2 * P * (1 / 100) * (17858 / 10000) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hg (by linarith)) (by linarith) (by linarith)
      (by positivity)
  linarith

end Instance

end CSD.RecordLayer

end
