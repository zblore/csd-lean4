/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusArrivalBox

/-!
# No display before the pointer's rate allows it, on every fibre

**Category:** 7-SigmaLayer. BACKLOG #297, eighth brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

The row's last listed remainder was the arrival statement composed with the bound against
the graph distance (`torusDetector_not_displayed`). That composition is not made here, for
two reasons stated in the scope below. What is proved instead is the bound that does hold
for the instance on every fibre and for every carrier state.

* ★★ `abs_idxPointerShift_le_rate` — on every fibre, for every carrier state and `t ≥ 0`:
  `|shift| ≤ 2 |f'(θ₂)| ‖B₀‖ t`;
* ★★ `graphDetector_not_displayed_of_rate` — a ready pointer is not displayed while
  `2 |f'(θ₂)| ‖B₀‖ t < 1/6`;
* ★★ `torusDetector_not_displayed_of_rate` — the same for the lattice Dirac field of any
  dimension and the projector on any set of sites: while `2 |f'(θ₂)| t < 1/6`;
* `abs_scaledTrainF_deriv_lift_le` — the profile `g · trainF` has `|f'| ≤ |g|` on every
  fibre;
* ★★★ `torusDetector_box_not_displayed_all_fibres` — **for the detector `arrivalBox` and the
  profile `(3/(16M)) · trainF` of `torusDetector_arrival_box`: from any ready pointer, on any
  fibre, for any carrier state, the pointer is not displayed at any flow time before
  `4M/9`.**

## Honest scope

⚠️ **This is not the bound against the graph distance.** It uses only that an occupancy is
at most `1`. It does not see where the carrier is.

⚠️ **The composition with `torusDetector_not_displayed` is not made.** That theorem asks for
a carrier whose ray is fixed by the projector on a set of sites `Y` that the growth from the
detector misses. The flat packet is a finite sum of plane waves; it is not shown to be
supported on any proper set of sites, so the hypothesis is not met by it. This module does
not prove that the hypothesis fails.

⚠️ **For this instance the graph-distance bound could give no later time than `4M/9`.** It
improves on the rate bound only while `(2 ‖H‖ t)^d / d! < 1`, which needs `2 ‖H‖ t < d`.
The free field's largest energy is `√33` (at the momentum `(π/2, π/2)`), and no site is
more than about `4.8M` steps from the detector, while `2 √33 · 4M/9 > 5M`. This is
arithmetic done by hand, not a Lean statement.

⚠️ **The display half is unchanged**: it holds on the fibre `θ₂ = 0` only
(`torusDetector_arrival_box`).

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297; `specs/unified-record-spacetime-plan.md` (UD-231,
UD-245, UD-246); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/GraphDetector.lean` (`abs_idxPointerShift_le_graph`,
`graphDetector_not_displayed`, `torusDetector_not_displayed`, `norm_siteSetProj_le`);
`RecordLayer/UnifiedCausalArrival.lean` (`abs_arenaObs_le`);
`RecordLayer/UnifiedDiracClock.lean` (`idxPointerShift`,
`hamiltonianFlow_coupledEnergy_reindex`); `RecordLayer/TorusArrivalBox.lean` (`arrivalBox`,
`torusDetector_arrival_box`); `RecordLayer/UnifiedEmissionReading.lean` (`scaledTrainF`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The rate bound -/

section Pointer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ}

/-- ★★ **A pointer's displacement is bounded by its rate**: on every fibre, for every carrier
state and `t ≥ 0`, `|shift| ≤ 2 |f'(θ₂)| ‖B₀‖ t`. -/
theorem abs_idxPointerShift_le_rate [Nonempty ι] (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (p : GenArena ι) {t : ℝ}
    (ht : 0 ≤ t) :
    |idxPointerShift hA hB hf φ p t| ≤ 2 * |hf.deriv_periodic.lift φ| * ‖B₀‖ * t := by
  unfold idxPointerShift
  have key : ‖∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)‖
      ≤ ‖B₀‖ * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => abs_arenaObs_le _ _
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at key
  rw [abs_mul, abs_mul, abs_neg, abs_two]
  calc 2 * |hf.deriv_periodic.lift φ|
        * |∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
      ≤ 2 * |hf.deriv_periodic.lift φ| * (‖B₀‖ * t) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg zero_le_two (abs_nonneg _))
    _ = _ := by ring

variable {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- ★★ **No display before the rate allows it.** From a ready pointer, on any fibre and for
any carrier state, the pointer is not displayed at the flow time `t ≥ 0` while
`2 |f'(θ₂)| ‖B₀‖ t < 1/6`. -/
theorem graphDetector_not_displayed_of_rate [Nonempty ι] (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (p : GenArena ι) {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ} (ht : 0 ≤ t)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * ‖B₀‖ * t < 1 / 6) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∉ displayArc := by
  rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
  exact pshift_notMem_displayArc hθ
    ((abs_idxPointerShift_le_rate hA hB hf θ.2 p ht).trans_lt hsmall)

end Pointer

/-! ### The torus -/

section Torus

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S] [Nonempty S]
  {L : ℕ} [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ} {f : ℝ → ℝ} {N : ℕ}

/-- ★★ **A detector on the torus is not displayed before its rate allows it.** The carrier is
the lattice Dirac field of any dimension, the pointer is coupled to the projector on any set
of sites `X`. From a ready pointer, on any fibre and for any carrier state, the pointer is
not displayed at the flow time `t ≥ 0` while `2 |f'(θ₂)| t < 1/6`. -/
theorem torusDetector_not_displayed_of_rate (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) (J μ : ℝ) (hf : Function.Periodic f 1)
    (hc : ContDiff ℝ ∞ f) (X : Set (κ → ZMod L)) [DecidablePred (· ∈ X)]
    (p : GenArena ((κ → ZMod L) × S)) {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ}
    (ht : 0 ≤ t) (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * t < 1 / 6) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst X)) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∉ displayArc := by
  have hBh : (siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L) X).IsHermitian :=
    siteSetProj_isHermitian _ X
  have hBn : ‖siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L) X‖ ≤ 1 :=
    norm_siteSetProj_le _ X
  refine graphDetector_not_displayed_of_rate e (latticeDiracHam_isHermitian h J μ) hBh hf hc p
    hθ ht (lt_of_le_of_lt ?_ hsmall)
  calc 2 * |hf.deriv_periodic.lift θ.2|
        * ‖siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L) X‖ * t
      ≤ 2 * |hf.deriv_periodic.lift θ.2| * 1 * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBn (mul_nonneg zero_le_two (abs_nonneg _))) ht
    _ = 2 * |hf.deriv_periodic.lift θ.2| * t := by ring

end Torus

/-! ### The instance -/

/-- The profile `g · trainF` has `|f'| ≤ |g|` on every fibre. -/
theorem abs_scaledTrainF_deriv_lift_le (g : ℝ) (φ : AddCircle (1 : ℝ)) :
    |(scaledTrainF_periodic g).deriv_periodic.lift φ| ≤ |g| := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective φ
  show |(scaledTrainF_periodic g).deriv_periodic.lift ((x : ℝ) : AddCircle (1 : ℝ))| ≤ |g|
  have h := (hasDerivAt_trainF x).const_mul g
  rw [Function.Periodic.lift_coe, show scaledTrainF g = fun x => g * trainF x from rfl, h.deriv,
    abs_mul, abs_neg]
  exact mul_le_of_le_one_right (abs_nonneg g) (Real.abs_cos_le_one _)

section Box

variable {L : ℕ} [NeZero L] {N : ℕ}

/-- ★★★ **The detector of `torusDetector_arrival_box` is not displayed before `4M/9`, on every
fibre.** Two dimensions, any ring size, `σ_x`, `σ_y` with `σ_z`, the detector `arrivalBox`,
the profile `(3/(16M)) · trainF`. From any ready pointer, on any fibre and for any carrier
state, the pointer is not displayed at any flow time `0 ≤ t < 4M/9`. -/
theorem torusDetector_box_not_displayed_all_fibres {M : ℕ} (hM : 0 < M)
    (e : (Fin 2 → ZMod L) × Fin 2 ≃ Fin (N + 1)) (p : GenArena ((Fin 2 → ZMod L) × Fin 2))
    {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ} (ht : 0 ≤ t) (htM : t < 4 * (M : ℝ) / 9) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e
            (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (arrivalBox L : Set (Fin 2 → ZMod L))))
          (scaledTrainF_periodic (3 / (16 * (M : ℝ))))
          (contDiff_scaledTrainF (3 / (16 * (M : ℝ))))) t
        (idxArenaEquiv e p, θ)).2 ∉ displayArc := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hg : 0 ≤ 3 / (16 * (M : ℝ)) := by positivity
  have hd := abs_scaledTrainF_deriv_lift_le (3 / (16 * (M : ℝ))) θ.2
  rw [abs_of_nonneg hg] at hd
  refine torusDetector_not_displayed_of_rate e cliffordTwo 2 1
    (scaledTrainF_periodic (3 / (16 * (M : ℝ)))) (contDiff_scaledTrainF (3 / (16 * (M : ℝ))))
    (arrivalBox L : Set (Fin 2 → ZMod L)) p hθ ht ?_
  have e1 : 2 * (3 / (16 * (M : ℝ))) * (4 * M / 9) = 1 / 6 := by
    field_simp
    ring
  calc 2 * |(scaledTrainF_periodic (3 / (16 * (M : ℝ)))).deriv_periodic.lift θ.2| * t
      ≤ 2 * (3 / (16 * (M : ℝ))) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd zero_le_two) ht
    _ < 2 * (3 / (16 * (M : ℝ))) * (4 * M / 9) :=
        mul_lt_mul_of_pos_left htM (by positivity)
    _ = 1 / 6 := e1

end Box

end CSD.RecordLayer

end
