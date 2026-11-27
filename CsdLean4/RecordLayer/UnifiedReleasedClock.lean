/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedReturn
public import CsdLean4.RecordLayer.TransponderReading

/-!
# The clock of a released carrier: shut before the record, running after it

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4; route (γ1)
of the task plans).

`RecordLayer/UnifiedReleasedReturn.lean` puts the return carrier at its free state at the
clock `κ(t) = c ∫₀ᵗ b(a₀ + Δ(u)) du`, with `Δ` the displacement of the pointer that reads
the event and `b` the window. Here the clock is read off the occupancy that drives that
pointer, which is the quantum calculation it already had:

* while the occupancy is `0`, the pointer does not move and the clock is `0`: with the
  window shut at the pointer's start, **no meeting, no return**;
* while the occupancy is small, the pointer stays inside a stretch where the window is
  shut, and the clock is still `0`;
* once the occupancy has carried the pointer into a stretch where the window is open, and
  for as long as it stays there, the clock runs at the rate `c`.

* `windowClock_eq_zero`, `le_windowClock`, `windowClock_le` — the clock of a window along
  any continuous displacement;
* ★★ `releasedClock_eq_zero_of_obs_eq_zero` — occupancy `0`: the clock is `0`, on every
  fibre;
* ★★ `releasedClock_eq_zero_of_obs_le` — occupancy at most `ε`: the clock is `0` up to
  `t₁`;
* ★★★ `le_releasedClock_of_dwell` — **occupancy at least `q` from `t₂`: the clock is at least
  `c (t − t₀)`**, `t₀` the time by which the pointer is inside the open stretch;
* `releasedClock_le` — the clock is at most `c t`;
* `idxFreeU_zero`, ★★★ `hamiltonianFlow_released_return_idle` — **no meeting, no return, as a
  statement about the flow**: with the occupancy `0` up to `t` the return carrier is at `t`
  where it was prepared.

## Honest scope

⚠️ **The occupancy bounds are hypotheses.** They are the hypotheses of UD-260 on the
detector's observable; no carrier is substituted for which they hold, and UD-261's instance
is not composed with this.

⚠️ **The window is a profile of a real number** here: `b(a₀ + Δ)` with `a₀` the pointer's
start and `Δ` its displacement, both real. The pointer may go round more than once; the
statement about the running clock asks that it stay inside one open stretch, which bounds
the time (`κ t ≤ hi`).

⚠️ **A lower bound for the clock**, with the upper bound `c t`. The clock's exact value
needs the time at which the pointer crosses the window's edge, which is not located.

⚠️ **No arrival record.** No detector reads the return carrier. **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-26, UD-260, UD-273, UD-274; §9.4); `specs/unified-records-spacetime-task-plans.md` (§9,
route (γ1)); `RecordLayer/UnifiedReleasedReturn.lean` (`hamiltonianFlow_released_return`);
`RecordLayer/TransponderReading.lean` (`idxPointerShift_le_of_obs_le`,
`idxPointerShift_eq_zero_of_obs_eq_zero`); `RecordLayer/TorusArrival.lean`
(`le_idxPointerShift_of_dwell`, `continuous_idxPointerShift`);
`RecordLayer/GraphDetector.lean` (`le_idxPointerShift_of_le`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The clock of a window along a displacement -/

section Window

variable {b s : ℝ → ℝ}

/-- While the window is shut along the displacement, the clock is `0`. -/
theorem windowClock_eq_zero (c a₀ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ u, 0 ≤ u → u ≤ t → b (a₀ + s u) = 0) :
    c * ∫ u in (0 : ℝ)..t, b (a₀ + s u) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
    rw [Set.uIcc_of_le ht] at hu
    exact h u hu.1 hu.2, intervalIntegral.integral_zero, mul_zero]

/-- From a time `t₀` after which the window is open along the displacement, the clock runs
at the rate `c`. -/
theorem le_windowClock (hb : Continuous b) (hs : Continuous s) (hb0 : ∀ x, 0 ≤ b x) {c : ℝ}
    (hc : 0 ≤ c) (a₀ : ℝ) {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t)
    (h1 : ∀ u, t₀ ≤ u → u ≤ t → b (a₀ + s u) = 1) :
    c * (t - t₀) ≤ c * ∫ u in (0 : ℝ)..t, b (a₀ + s u) := by
  have hcont : Continuous fun u : ℝ => b (a₀ + s u) := hb.comp (continuous_const.add hs)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 t₀) (hcont.intervalIntegrable (μ := volume) t₀ t)
  have hA : 0 ≤ ∫ u in (0 : ℝ)..t₀, b (a₀ + s u) :=
    intervalIntegral.integral_nonneg h0 fun u _ => hb0 _
  have hB : ∫ u in t₀..t, b (a₀ + s u) = t - t₀ := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun u hu => by
      rw [Set.uIcc_of_le h01] at hu
      exact h1 u hu.1 hu.2]
    simp
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← hsplit, hB]
  linarith

/-- A window that is at most `1` gives a clock of at most `c t`. -/
theorem windowClock_le (hb : Continuous b) (hs : Continuous s) (hb1 : ∀ x, b x ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (a₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    c * ∫ u in (0 : ℝ)..t, b (a₀ + s u) ≤ c * t := by
  have hcont : Continuous fun u : ℝ => b (a₀ + s u) := hb.comp (continuous_const.add hs)
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h := intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun u _ => hb1 _
  simpa using h

end Window

/-! ### The clock from the occupancy that drives the pointer -/

section Pointer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f b : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ}

/-- ★★ **Occupancy `0`: the clock is `0`.** On any fibre, with the window shut at the
pointer's start: if the observable that drives the pointer has expectation `0` along the
carrier's orbit up to `t`, the clock of the released carrier is `0` at `t`. -/
theorem releasedClock_eq_zero_of_obs_eq_zero (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (c : ℝ) {a₀ : ℝ} (hba : b a₀ = 0)
    {p : GenArena ι} {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t → arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) = 0) :
    c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hA hB hf φ p u) = 0 :=
  windowClock_eq_zero (s := fun u => idxPointerShift hA hB hf φ p u) c a₀ ht
    fun u hu0 hut => by
      show b (a₀ + idxPointerShift hA hB hf φ p u) = 0
      rw [idxPointerShift_eq_zero_of_obs_eq_zero hA hB hf φ hu0
        (fun s hs hsu => hz s hs (hsu.trans hut)), add_zero, hba]

/-- ★★ **A small occupancy: the clock is still `0`.** On a fibre with rate
`κ = −2 f'(θ₂) ≥ 0`, the window shut on `[a₀, a₀ + δ]`: if the observable has expectation
between `0` and `ε` up to `t₁`, with `κ ε t₁ ≤ δ`, the clock is `0` at `t₁`. -/
theorem releasedClock_eq_zero_of_obs_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (c : ℝ) {a₀ δ : ℝ}
    (hbz : ∀ x, a₀ ≤ x → x ≤ a₀ + δ → b x = 0) {p : GenArena ι} {t₁ ε : ℝ} (ht : 0 ≤ t₁)
    (h0 : ∀ s, 0 ≤ s → s ≤ t₁ →
      0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p))
    (hε : ∀ s, 0 ≤ s → s ≤ t₁ →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) ≤ ε)
    (hδ : -2 * hf.deriv_periodic.lift φ * (ε * t₁) ≤ δ) :
    c * ∫ u in (0 : ℝ)..t₁, b (a₀ + idxPointerShift hA hB hf φ p u) = 0 := by
  have hε0 : 0 ≤ ε := (h0 0 le_rfl ht).trans (hε 0 le_rfl ht)
  refine windowClock_eq_zero (s := fun u => idxPointerShift hA hB hf φ p u) c a₀ ht
    fun u hu0 hut => ?_
  show b (a₀ + idxPointerShift hA hB hf φ p u) = 0
  have hlo := le_idxPointerShift_of_le hA hB hf hκ (q := 0) hu0
    (fun s hs hsu => h0 s hs (hsu.trans hut))
  have hup := idxPointerShift_le_of_obs_le hA hB hf hκ hu0
    (fun s hs hsu => hε s hs (hsu.trans hut))
  have hmono : -2 * hf.deriv_periodic.lift φ * (ε * u)
      ≤ -2 * hf.deriv_periodic.lift φ * (ε * t₁) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hut hε0) hκ
  rw [mul_zero, zero_mul] at hlo
  exact hbz _ (by linarith) (by linarith)

/-- ★★★ **Once the occupancy has turned the pointer into the window, the clock runs.** On a
fibre with rate `κ = −2 f'(θ₂) ≥ 0`; the window is continuous, non-negative, and `1` on
`[a₀ + lo, a₀ + hi]`; `c ≥ 0`. If the observable has expectation between `0` and `1` up to
`t` and at least `q` on `[t₂, t₀]`, with `t₂ ≤ t₀ ≤ t`, `lo ≤ κ q (t₀ − t₂)` and `κ t ≤ hi`,
the clock at `t` is at least `c (t − t₀)`. After `t₀` the occupancy may fall: the pointer does
not turn back. -/
theorem le_releasedClock_of_dwell (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (hbc : Continuous b) (hb0 : ∀ x, 0 ≤ b x)
    {c : ℝ} (hc : 0 ≤ c) {a₀ lo hi : ℝ} (hb1 : ∀ x, a₀ + lo ≤ x → x ≤ a₀ + hi → b x = 1)
    {p : GenArena ι} {t₂ t₀ t q : ℝ} (h2 : 0 ≤ t₂) (h20 : t₂ ≤ t₀) (h0t : t₀ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) ≤ 1)
    (hq : ∀ s, t₂ ≤ s → s ≤ t₀ →
      q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p))
    (hlo : lo ≤ -2 * hf.deriv_periodic.lift φ * (q * (t₀ - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift φ * t ≤ hi) :
    c * (t - t₀) ≤ c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hA hB hf φ p u) := by
  refine le_windowClock (s := fun u => idxPointerShift hA hB hf φ p u) hbc
    (continuous_idxPointerShift hA hB hf φ p) hb0 hc a₀ (h2.trans h20) h0t
    fun u hu0 hut => ?_
  show b (a₀ + idxPointerShift hA hB hf φ p u) = 1
  have hu : 0 ≤ u := (h2.trans h20).trans hu0
  have hlow := le_idxPointerShift_of_dwell hA hB hf hκ h2 h20
    (fun s hs hsu => h0 s hs (hsu.trans h0t)) hq
  have hmono : idxPointerShift hA hB hf φ p t₀ ≤ idxPointerShift hA hB hf φ p u :=
    monotoneOn_idxPointerShift hA hB hf hκ h0 ⟨h2.trans h20, h0t⟩ ⟨hu, hut⟩ hu0
  have hup := idxPointerShift_le_of_obs_le hA hB hf hκ hu
    (fun s hs hsu => hone s hs (hsu.trans hut))
  have hmono' : -2 * hf.deriv_periodic.lift φ * (1 * u)
      ≤ -2 * hf.deriv_periodic.lift φ * t := by
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left hut hκ
  exact hb1 _ (by linarith) (by linarith)

/-- The clock is at most `c t` for a window that is at most `1`. -/
theorem releasedClock_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (hbc : Continuous b)
    (hb1 : ∀ x, b x ≤ 1) {c : ℝ} (hc : 0 ≤ c) (a₀ : ℝ) (p : GenArena ι) {t : ℝ}
    (ht : 0 ≤ t) :
    c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hA hB hf φ p u) ≤ c * t :=
  windowClock_le (s := fun u => idxPointerShift hA hB hf φ p u) hbc
    (continuous_idxPointerShift hA hB hf φ p) hb1 hc a₀ ht

/-- The propagator at the time `0` is the identity. -/
theorem idxFreeU_zero (hA : A₀.IsHermitian) : idxFreeU hA 0 = 1 := by
  apply Subtype.ext
  rw [idxFreeU_val, zero_smul, exp_zero]
  rfl

end Pointer

/-! ### No meeting, no return -/

section Idle

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b : ℝ → ℝ} {N : ℕ}
  (e : ι × κ ≃ Fin (N + 1))

/-- ★★★ **No meeting, no return.** The composite of `hamiltonianFlow_released_return`, with
the window shut at the pointer's start. On any fibre and for any constant `c`: if the
observable that the pointer reads has expectation `0` along the earlier carriers' orbit up to
`t`, then at `t` the return carrier is at the ray where it was prepared, and the pointer has
not moved. -/
theorem hamiltonianFlow_released_return_idle (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b) (c : ℝ) (pa : GenArena ι) (r : GenArena κ)
    {a₀ : ℝ} (hba : b a₀ = 0) (φ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) = 0) :
    (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul
          (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
            (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
          (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
            ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb hcb) c) t
        (idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ))
      = (idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ t) pa) r),
          ((a₀ : AddCircle (1 : ℝ)), φ)) := by
  rw [hamiltonianFlow_released_return e hHa hP hHR hf hb hc hcb c pa r a₀ φ t,
    releasedClock_eq_zero_of_obs_eq_zero hHa hP hf φ c hba ht hz, idxFreeU_zero, arenaKick_one,
    idxPointerShift_eq_zero_of_obs_eq_zero hHa hP hf φ ht hz, add_zero]

end Idle

end CSD.RecordLayer

end
