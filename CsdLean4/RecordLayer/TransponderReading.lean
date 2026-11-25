/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderDetunedMeeting
public import CsdLean4.RecordLayer.TransponderAtRest
public import CsdLean4.RecordLayer.TorusArrival

/-!
# The meeting writes a record: a pointer that accumulates the transponder's second level

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (3): a reading of what the
meeting launches; the author's decision of 2026-11-25: the record is written by the pointer's
accumulated displacement, and is not a click whose probability follows the launched weight).

A pointer is coupled to the projector on the transponder's second level. Its displacement is
its rate times the accumulated occupancy of that level, so a small occupancy still carries
the pointer across its arcs if it lasts. Two runs are compared.

* **Without the contact term** the second level stays empty, on every fibre and for every
  state with the transponder in its first level: the pointer does not move, and its count is
  `0` at every flow time.
* **With the contact term**, for the flat packet and a transponder at rest: the count is `0`
  at `t₁`, before the packet's box reaches the transponder, and at least `1` at `t`.

## A pointer that accumulates

* `card_tickIndices_pos_of_ready`, `idxPointerShift_le_of_obs_le`,
  `idxPointerShift_eq_zero_of_obs_eq_zero`;
* ★★ `graphDetector_idle` — an observable that stays at `0` leaves the pointer at rest;
* ★★★ `graphDetector_accumulate_records` — occupancy at most `ε` up to `t₁` and at least `q`
  from `t₂`, with `κ ε t₁ ≤ 1/6` and `1/3 ≤ κ q (t − t₂)`: not displayed up to `t₁`, and the
  counts `0` at `t₁` and some `n ≥ 1` at `t` are a record history of the start. **No upper
  bound on the displacement is asked**, so the pointer may have gone round.

## The transponder's second level as the pointer's observable

* `one_kronecker_levelProj_isHermitian`, `one_kronecker_levelProj_mul_self`;
* `one_kronecker_levelProj_one_mulVec_prod`, `mul_exp_smul_mulVec_eq_zero`;
* `arenaObs_proj_kick_toLp` — the expectation of a projector along an orbit, as a sum;
* `toLp_ne_zero_of_sum_norm_sq_eq_one`;
* ★★★ `transponder_reading_control` — **no contact term: the count is `0`, on every fibre**;
* ★★★ `transponder_meeting_record` — **the contact term: count `0` before the meeting, at
  least `1` after**.

## Honest scope

⚠️ **The hypotheses of `transponder_meeting_record` are three inequalities.** They ask that
the amplitude bound of UD-263 stay above `ρ` on a whole window `[t₃, t]`, that
`κ ρ² (t − t₃) ≥ 1/3`, and that the leakage before the meeting obey
`κ (|g| √ε₁ t₁)² t₁ ≤ 1/6`. Together: `ρ² (t − t₃) ≥ 2 (|g| √ε₁ t₁)² t₁`. For the geometry of
UD-257 this fails by hand arithmetic (the left side is about a thirtieth of the right). A
geometry that meets them is in `RecordLayer/TransponderReadingInstance.lean` (UD-261).

⚠️ **The pointer reads the transponder's second level wherever the transponder is.** It is
not a receiver at a distance: nothing is shown to travel from the meeting. The record is
written where the transponder rests.

⚠️ **The record with the contact term is on the fibres where the pointer's profile
vanishes**, a null set of its conserved angle; there the carriers move as if the pointer
were absent. The control holds on every fibre.

⚠️ **A count of at least one**, read from the flow time `0`; its value is not bounded
above, and the pointer need not be displayed at `t`. The two levels may differ in energy
(UD-263); the instance of UD-261 has one energy for both. The times are flow times. No probability is derived or used.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-242, UD-252, UD-259, UD-260); `specs/unified-records-spacetime-task-plans.md` (§9);
`RecordLayer/TransponderDetunedMeeting.lean` (`transponder_detuned_flatPacket_meeting`);
`RecordLayer/TransponderAtRest.lean` (`transponder_launch_flatPacket_resting_le`);
`RecordLayer/TorusArrival.lean` (`graphDetector_isTickCount`, `arenaReadout`,
`graphDetector_arrival_records`); `RecordLayer/TickCountLaw.lean` (`isTickCount_pointer`);
`RecordLayer/DiracPointerClick.lean` (`diracClickProb_eq_zero_of_weight_le`, the cut-off
that a short reading of a small weight meets); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix NormedSpace Set MeasureTheory
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### A pointer that accumulates -/

/-- A ready pointer that has advanced past a third of a turn has at least one tick. -/
theorem card_tickIndices_pos_of_ready {x₀ Δ : ℝ} (h1 : x₀ ≤ 1 / 6) (hlo : 1 / 3 < x₀ + Δ) :
    0 < (tickIndices (1 / 6) (1 / 3) x₀ Δ).card := by
  refine Finset.card_pos.2 ⟨0, mem_tickIndices.2 ?_⟩
  rw [Int.cast_zero]
  constructor <;> linarith

section Pointer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ}

/-- On a fibre with rate `κ ≥ 0`, an observable of expectation at most `ε` up to `t` moves the
pointer by at most `κ ε t`. -/
theorem idxPointerShift_le_of_obs_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {p : GenArena ι} {t ε : ℝ} (ht : 0 ≤ t)
    (hε : ∀ s, 0 ≤ s → s ≤ t → arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) ≤ ε) :
    idxPointerShift hA hB hf φ p t ≤ -2 * hf.deriv_periodic.lift φ * (ε * t) := by
  unfold idxPointerShift
  refine mul_le_mul_of_nonneg_left ?_ hκ
  have a := intervalIntegral.integral_mono_on ht
    ((continuous_arenaObs_idxCarrierU hA hB hf φ p).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := ε)) fun s hs => hε s hs.1 hs.2
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at a
  linarith

/-- An observable of expectation `0` up to `t` does not move the pointer, on any fibre. -/
theorem idxPointerShift_eq_zero_of_obs_eq_zero (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) {p : GenArena ι} {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t → arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) = 0) :
    idxPointerShift hA hB hf φ p t = 0 := by
  unfold idxPointerShift
  have h : ∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)
      = ∫ _ in (0 : ℝ)..t, (0 : ℝ) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [Set.uIcc_of_le ht] at hs
      exact hz s hs.1 hs.2
  rw [h, intervalIntegral.integral_zero, mul_zero]

variable {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- ★★ **An observable that stays at `0` leaves the pointer at rest.** From a ready pointer,
on any fibre: if the detector's observable has expectation `0` along the carrier's orbit up
to `t ≥ 0`, the pointer is not displayed at any flow time up to `t`, and "the pointer has
counted `0` at `t`" is a recorded fact of the run's start. -/
theorem graphDetector_idle (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (p₀ : CPN (N + 1)) {p : GenArena ι}
    {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) = 0) :
    (∀ u, 0 ≤ u → u ≤ t →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) u
        (idxArenaEquiv e p, θ)).2 ∉ displayArc)
      ∧ ((idxArenaEquiv e p, θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy (Matrix.reindex e e A₀)
            (Matrix.reindex e e B₀) hf hc) p₀).semantics
          [TickReadout.startFact () t 0] := by
  have hzero : ∀ u, 0 ≤ u → u ≤ t → idxPointerShift hA hB hf θ.2 p u = 0 := fun u hu hut =>
    idxPointerShift_eq_zero_of_obs_eq_zero hA hB hf θ.2 hu fun s hs hsu =>
      hz s hs (hsu.trans hut)
  have hr : rep θ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hθ
  rw [shearWidth_two] at hr
  refine ⟨fun u hu hut => ?_, ?_⟩
  · rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
    exact pshift_notMem_displayArc_of_le hθ (hzero u hu hut).ge
      ((hzero u hu hut).le.trans (by norm_num))
  · have c0 := isTickCount_pointer (π := Prod.snd) (q := θ)
      (γ := fun s => (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) s
        (idxArenaEquiv e p, θ))
      (D := fun u => idxPointerShift hA hB hf θ.2 p u) ht
      (continuous_idxPointerShift hA hB hf θ.2 p).continuousOn
      (fun a ha b hb _ => by
        show idxPointerShift hA hB hf θ.2 p a ≤ idxPointerShift hA hB hf θ.2 p b
        rw [hzero a ha.1 ha.2, hzero b hb.1 hb.2])
      (idxPointerShift_zero hA hB hf θ.2 p)
      fun u _ _ => by
        rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
        rfl
    rw [hzero t ht le_rfl, card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
    refine (arenaReadout (contMDiff_coupledEnergy (Matrix.reindex e e A₀)
      (Matrix.reindex e e B₀) hf hc) p₀).mem_compatibleSet_startFacts
      [((), t, 0)] _ fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rw [hr']
    exact c0

/-- ★★★ **A pointer that accumulates a small occupancy to its threshold.** On a fibre with
rate `κ = −2 f'(θ₂) ≥ 0`, from a ready pointer: if the detector's observable has non-negative
expectation along the carrier's orbit up to `t`, at most `ε` up to `t₁` and at least `q` from
`t₂`, with `0 ≤ t₁ ≤ t₂ ≤ t`, `κ ε t₁ ≤ 1/6` and `1/3 ≤ κ q (t − t₂)`, then the pointer is not
displayed at any flow time up to `t₁`, and for some `n ≥ 1` the counts `0` at `t₁` and `n` at
`t` are a record history of the run's start. -/
theorem graphDetector_accumulate_records (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (p₀ : CPN (N + 1)) {p : GenArena ι}
    {θ : KTorus} (hθ : θ ∈ readyArc 2) (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2)
    {t₁ t₂ t ε q : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (hε : ∀ s, 0 ≤ s → s ≤ t₁ →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) ≤ ε)
    (hq : ∀ s, t₂ ≤ s → s ≤ t →
      q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (hbefore : -2 * hf.deriv_periodic.lift θ.2 * (ε * t₁) ≤ 1 / 6)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2 * (q * (t - t₂))) :
    (∀ u, 0 ≤ u → u ≤ t₁ →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) u
        (idxArenaEquiv e p, θ)).2 ∉ displayArc)
      ∧ ∃ n : ℕ, 0 < n ∧ ((idxArenaEquiv e p, θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy (Matrix.reindex e e A₀)
            (Matrix.reindex e e B₀) hf hc) p₀).semantics
          [TickReadout.startFact () t₁ 0, TickReadout.startFact () t n] := by
  have ht1 : t₁ ≤ t := h12.trans h2
  have hε0 : 0 ≤ ε := (h0 0 le_rfl (h1.trans ht1)).trans (hε 0 le_rfl h1)
  have hr : rep θ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hθ
  rw [shearWidth_two] at hr
  have hup : ∀ u, 0 ≤ u → u ≤ t₁ → idxPointerShift hA hB hf θ.2 p u ≤ 1 / 6 :=
    fun u hu hu1 =>
      ((idxPointerShift_le_of_obs_le hA hB hf hκ hu fun s hs hsu =>
        hε s hs (hsu.trans hu1)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu1 hε0) hκ)).trans hbefore
  have hlow := hlo.trans (le_idxPointerShift_of_dwell hA hB hf hκ (h1.trans h12) h2 h0 hq)
  refine ⟨fun u hu hu1 => ?_,
    (tickIndices (1 / 6) (1 / 3) (rep θ.1) (idxPointerShift hA hB hf θ.2 p t)).card, ?_, ?_⟩
  · rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
    have h0u := le_idxPointerShift_of_le hA hB hf hκ hu
      (fun s hs hsu => h0 s hs (hsu.trans (hu1.trans ht1)))
    exact pshift_notMem_displayArc_of_le hθ (by linarith) (hup u hu hu1)
  · exact card_tickIndices_pos_of_ready hr.2 (by linarith [hr.1])
  · have c0 := graphDetector_isTickCount e hA hB hf hc hκ h1
      (fun s hs hs1 => h0 s hs (hs1.trans ht1))
    rw [card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2, hup t₁ h1 le_rfl])] at c0
    have c1 := graphDetector_isTickCount e hA hB hf hc hκ (h1.trans ht1) h0
    refine (arenaReadout (contMDiff_coupledEnergy (Matrix.reindex e e A₀)
      (Matrix.reindex e e B₀) hf hc) p₀).mem_compatibleSet_startFacts
      [((), t₁, 0), ((), t, _)] _ fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    exacts [c0, c1]

end Pointer

/-! ### The expectation of a projector along an orbit -/

section Projector

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- A vector whose squared amplitudes sum to `1` is not zero. -/
theorem toLp_ne_zero_of_sum_norm_sq_eq_one {Ψ : m → ℂ} (h : ∑ x, ‖Ψ x‖ ^ 2 = 1) :
    (WithLp.toLp 2 Ψ : EuclideanSpace ℂ m) ≠ 0 := by
  intro h0
  have hΨ : Ψ = 0 := congrArg WithLp.ofLp h0
  rw [hΨ] at h
  simp at h

/-- A matrix commuting with the generator annihilates the orbit of a vector it annihilates. -/
theorem mul_exp_smul_mulVec_eq_zero {Q A : Matrix m m ℂ} (hQA : Q * A = A * Q) {Ψ : m → ℂ}
    (hΨ : Q *ᵥ Ψ = 0) (t : ℝ) : (Q * exp (t • A)) *ᵥ Ψ = 0 := by
  rw [Matrix.mul_exp_smul_eq_of_commute hQA t, ← Matrix.mulVec_mulVec, hΨ, Matrix.mulVec_zero]

/-- **The expectation of a Hermitian idempotent along an orbit**: for a unitary `U` and the
ray of `Ψ`, it is `Σ_x |(Q U Ψ)_x|² / Σ_x |Ψ_x|²`. -/
theorem arenaObs_proj_kick_toLp {Q : Matrix m m ℂ} (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (U : Matrix.unitaryGroup m ℂ) {Ψ : m → ℂ}
    (hp : (WithLp.toLp 2 Ψ : EuclideanSpace ℂ m) ≠ 0) :
    arenaObs Q (arenaKick U (Projectivization.mk ℂ _ hp))
      = (∑ x, ‖((Q * U.val) *ᵥ Ψ) x‖ ^ 2) / ∑ x, ‖Ψ x‖ ^ 2 := by
  have hU : (U.val)ᴴ * U.val = 1 := by
    have hmem := U.property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin Q) = Matrix.toEuclideanLin Q := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hQ.eq]
  have hmulQ : ∀ y : EuclideanSpace ℂ m, Matrix.toEuclideanLin (Q * Q) y
      = Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q y) := fun y =>
    DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 Q Q) y
  have hQw : ∀ y : EuclideanSpace ℂ m, (inner ℂ y (Matrix.toEuclideanLin Q y)).re
      = ‖Matrix.toEuclideanLin Q y‖ ^ 2 := fun y => by
    have h1 : inner ℂ y (Matrix.toEuclideanLin Q y)
        = inner ℂ (Matrix.toEuclideanLin Q y) (Matrix.toEuclideanLin Q y) := by
      calc inner ℂ y (Matrix.toEuclideanLin Q y)
          = inner ℂ y (Matrix.toEuclideanLin (Q * Q) y) := by rw [hQQ]
        _ = inner ℂ y (LinearMap.adjoint (Matrix.toEuclideanLin Q)
              (Matrix.toEuclideanLin Q y)) := by rw [hmulQ, hadj]
        _ = inner ℂ (Matrix.toEuclideanLin Q y) (Matrix.toEuclideanLin Q y) :=
            LinearMap.adjoint_inner_right _ _ _
    rw [h1, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [arenaKick_mk _ hp, arenaObs_mk_eq_inner, hQw, Matrix.norm_toEuclideanLin_of_isom hU,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [toEuclideanLin_coord, ← Matrix.mulVec_mulVec]
  rfl

end Projector

/-! ### The transponder's second level as the pointer's observable -/

section Transponder

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

omit [Fintype ι] [Fintype n] in
/-- The projector on one level of the transponder, on the composite, is Hermitian. -/
theorem one_kronecker_levelProj_isHermitian (l : Fin 2) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l).IsHermitian := by
  rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal, Matrix.IsHermitian,
    Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases hp : p.2.2 = l <;> simp [hp]

/-- The projector on one level of the transponder, on the composite, is idempotent. -/
theorem one_kronecker_levelProj_mul_self (l : Fin 2) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l) * ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l)
      = (1 : Matrix ι ι ℂ) ⊗ₖ levelProj n l := by
  rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases hp : p.2.2 = l <;> simp [hp]

/-- A product state whose transponder factor is in the first level has no part in the
second. -/
theorem one_kronecker_levelProj_one_mulVec_prod (ψ : ι → ℂ) {φ : n × Fin 2 → ℂ}
    (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) *ᵥ (fun y : ι × (n × Fin 2) => ψ y.1 * φ y.2)
      = 0 := by
  rw [← Matrix.diagonal_one, levelProj, Matrix.diagonal_kronecker_diagonal]
  funext y
  rw [Matrix.mulVec_diagonal]
  by_cases hy : y.2.2 = 1
  · simp [hφ y.2 hy]
  · simp [hy]

variable {f : ℝ → ℝ} {N : ℕ}

/-- ★★★ **Without the contact term the pointer does not move, on every fibre.** The pointer
is coupled to the projector on the transponder's second level; the carriers' energy is the
composite's free one, any Hermitian `M₀` for the messenger and any Hermitian block for each
level of the transponder. From a ready pointer and the ray of any state with the transponder
in its first level, on every fibre of the pointer's conserved angle: the pointer is not
displayed at any flow time up to `t ≥ 0`, and "the pointer has counted `0` at `t`" is a
recorded fact of the run's start. -/
theorem transponder_reading_control (e : ι × (n × Fin 2) ≃ Fin (N + 1)) {M₀ : Matrix ι ι ℂ}
    (hM : M₀.IsHermitian) {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (p₀ : CPN (N + 1))
    {Ψ : ι × (n × Fin 2) → ℂ} (hΨ : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) *ᵥ Ψ = 0)
    (hp : (WithLp.toLp 2 Ψ : EuclideanSpace ℂ (ι × (n × Fin 2))) ≠ 0) {θ : KTorus}
    (hθ : θ ∈ readyArc 2) {t : ℝ} (ht : 0 ≤ t) :
    (∀ u, 0 ≤ u → u ≤ t →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e (compositeH M₀ (Matrix.blockDiagonal T)))
          (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)) hf hc) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (compositeH M₀ (Matrix.blockDiagonal T)))
            (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)) hf hc) p₀).semantics
          [TickReadout.startFact () t 0] := by
  have hQh := one_kronecker_levelProj_isHermitian (ι := ι) (n := n) 1
  have hQQ := one_kronecker_levelProj_mul_self (ι := ι) (n := n) 1
  have hcomm : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * ((-Complex.I) • idxCoupledH (compositeH M₀ (Matrix.blockDiagonal T))
          ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) hf θ.2)
      = ((-Complex.I) • idxCoupledH (compositeH M₀ (Matrix.blockDiagonal T))
          ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) hf θ.2)
        * ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) := by
    simp only [idxCoupledH, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
      one_kronecker_mul_compositeH M₀ (levelProj_mul_blockDiagonal T 1)]
  refine graphDetector_idle e (compositeH_isHermitian hM (blockDiagonal_isHermitian hT)) hQh
    hf hc p₀ hθ ht fun s _ _ => ?_
  rw [arenaObs_proj_kick_toLp hQh hQQ, idxCarrierU_val,
    mul_exp_smul_mulVec_eq_zero hcomm hΨ s]
  simp

end Transponder

/-! ### The flat packet meets a transponder at rest -/

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ} {f : ℝ → ℝ} {N : ℕ}

/-- ★★★ **The meeting writes a record.** The messenger is the flat packet of the lattice
Dirac field of any dimension; the transponder is at rest with the level energies `E 0`,
`E 1`, in
a state of norm `1` in its first level, supported on the sites `B`; the contact term has
strength `g`; `Ω > 0` with `Ω² = g² + ((E 1 − E 0)/2)²`. A pointer is coupled to the projector on the transponder's second level. Take
`0 ≤ t₁ ≤ t₂ ≤ t₃ ≤ t`, with no site of the packet's moving box related to a site of `B` up
to `t₁` and every site of it related to every site of `B` from `t₂` to `t`, and `ρ ≥ 0` with

`ρ + |g| (√ε₁ t₁ + (t₂ − t₁)) + |g| √ε (t − t₂) ≤ (|g|/Ω) |sin (Ω (s − t₂))|` for
`t₃ ≤ s ≤ t`,

`ε₁ = flatTailD t₁`, `ε = flatTailD t`. On a fibre where the pointer's profile vanishes and
`κ = −2 f'(θ₂) ≥ 0`, from a ready pointer: if `κ (|g| √ε₁ t₁)² t₁ ≤ 1/6` and
`1/3 ≤ κ ρ² (t − t₃)`, then the pointer is not displayed at any flow time up to `t₁`, and for
some `n ≥ 1` the counts `0` at `t₁` and `n` at `t` are a record history of the run's
start. -/
theorem transponder_meeting_record
    (e : ((κ → ZMod L) × Sp) × (n × Fin 2) ≃ Fin (N + 1)) (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (p₀ : CPN (N + 1))
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    (hφn : ∑ q, ‖φ q‖ ^ 2 = 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0)
    (hp : (WithLp.toLp 2 (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) :
      EuclideanSpace ℂ (((κ → ZMod L) × Sp) × (n × Fin 2))) ≠ 0)
    {θ : KTorus} (hθ : θ ∈ readyArc 2) (h0 : hf.lift θ.2 = 0)
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {t₁ t₂ t₃ t ρ : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) (h3 : t₃ ≤ t) (hρ : 0 ≤ ρ)
    (hsep : ∀ s, 0 ≤ s → s ≤ t₁ → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b)
    (hcon : ∀ s, t₂ ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      r a b)
    (hamp : ∀ s, t₃ ≤ s → s ≤ t →
      ρ + |g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁))
          + |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * (t - t₂))
        ≤ |g| / Ω * |Real.sin (Ω * (s - t₂))|)
    (hbefore : -2 * hf.deriv_periodic.lift θ.2
      * ((|g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁)) ^ 2 * t₁) ≤ 1 / 6)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2 * (ρ ^ 2 * (t - t₃))) :
    (∀ u, 0 ≤ u → u ≤ t₁ →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e (compositeH (latticeDiracHam (L := L) α β J μ)
              (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))
          (Matrix.reindex e e
            ((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1))
          hf hc) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc)
      ∧ ∃ c : ℕ, 0 < c ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))
            (Matrix.reindex e e
              ((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1))
            hf hc) p₀).semantics
          [TickReadout.startFact () t₁ 0, TickReadout.startFact () t c] := by
  have ht2 : 0 ≤ t₂ := h1.trans h12
  have hM := latticeDiracHam_isHermitian (L := L) h J μ
  have hT : ∀ l : Fin 2, (((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hV : ((g : ℂ) • gateOp (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r
      (levelSwap n)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul,
      (gateOp_isHermitian Prod.fst τ r (levelSwap_isHermitian n) hτ).eq, Complex.star_def,
      Complex.conj_ofReal]
  have hA := (compositeH_isHermitian hM (blockDiagonal_isHermitian hT)).add hV
  have hQh := one_kronecker_levelProj_isHermitian (ι := (κ → ZMod L) × Sp) (n := n) 1
  have hQQ := one_kronecker_levelProj_mul_self (ι := (κ → ZMod L) × Sp) (n := n) 1
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  have hQ1 := norm_one_kronecker_levelProj_le (n := n) ((κ → ZMod L) × Sp) 1
  have hg := abs_nonneg g
  have hb0 : 0 ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ :=
    mul_nonneg (Real.sqrt_nonneg _) h1
  refine graphDetector_accumulate_records e hA hQh hf hc p₀ hθ hκ h1 (h12.trans h23) h3
    (fun s _ _ => ?_) (fun s hs hs1 => ?_) (fun s hs hst => ?_) hbefore hlo
  · rw [idxCarrierU_of_lift_eq_zero hA hQh hf h0, arenaObs_proj_kick_toLp hQh hQQ,
      idxFreeU_val, hΨ1, div_one]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  · rw [idxCarrierU_of_lift_eq_zero hA hQh hf h0, arenaObs_proj_kick_toLp hQh hQQ,
      idxFreeU_val, hΨ1, div_one]
    have hl := transponder_launch_flatPacket_resting_le τ r hτ h he hn hμ E g lo
      hN hNL k₀ hw0 hw hγ φ hφ hφn.le B hφB hs
      (fun s' hs' hs's => hsep s' hs' (hs's.trans hs1))
    have hm : Real.sqrt (flatTailD L J μ Nw w γ s) * s
        ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ :=
      mul_le_mul (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hs1)) hs1 hs
        (Real.sqrt_nonneg _)
    have hle := hl.trans ((mul_le_mul_of_nonneg_right hQ1
      (mul_nonneg hg (mul_nonneg (Real.sqrt_nonneg _) hs))).trans
      (le_of_eq_of_le (one_mul _) (mul_le_mul_of_nonneg_left hm hg)))
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)] at hsq
  · rw [idxCarrierU_of_lift_eq_zero hA hQh hf h0, arenaObs_proj_kick_toLp hQh hQQ,
      idxFreeU_val, hΨ1, div_one]
    have hs2 : t₂ ≤ s := h23.trans hs
    have key := (abs_le.1 (transponder_detuned_flatPacket_meeting τ r hτ h he hn hμ E g hΩ
      hΩ2 lo hN hNL k₀ hw0 hw hγ φ hφ hφn B hφB h1 h12 hs2 hsep
      (fun s' hs' hs's => hcon s' hs' (hs's.trans hst)))).1
    have hm : Real.sqrt (flatTailD L J μ Nw w γ s) * (s - t₂)
        ≤ Real.sqrt (flatTailD L J μ Nw w γ t) * (t - t₂) :=
      mul_le_mul (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hst))
        (by linarith) (by linarith) (Real.sqrt_nonneg _)
    have hm' := mul_le_mul_of_nonneg_left hm hg
    have hle : ρ ≤ Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
            ⊗ₖ levelProj n 1)
          * exp (s • ((-Complex.I)
            • (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
        *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2) := by
      linarith [hamp s hs hst, key, hm']
    have hsq := pow_le_pow_left₀ hρ hle 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)] at hsq

end Packet

end CSD.RecordLayer

end
