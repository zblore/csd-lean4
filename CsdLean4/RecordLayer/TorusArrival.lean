/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusDetector
public import CsdLean4.RecordLayer.UnifiedRecordHistoryBridge
public import CsdLean4.RecordLayer.TickCountLaw

/-!
# Arrival and display in one run, and the detector's two counts as recorded facts

**Category:** 7-SigmaLayer. BACKLOG #297, fourth brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

`RecordLayer/TorusDetector.lean` shows a detector on the torus displays a packet that stays
in its box for the whole write. Here the packet arrives from outside, in the same run: up to
the flow time `t₁` the packet's moving box misses the detector's sites, from `t₂` to `t` it
is inside them. The pointer is not displayed up to `t₁` and is displayed at `t`. The arena
with one pointer is given a tick readout, and the two readings (count `0` at `t₁`, count `1`
at `t`) are a record history of the run's start.

## Two stages of one integral

* `integral_le_of_arrival`, `le_integral_of_dwell`;
* ★★ `idxPointerShift_le_of_arrival`, ★★ `le_idxPointerShift_of_dwell` — the pointer's
  displacement when the occupancy is at most `ε` up to `t₁` and at least `q` from `t₂`;
* `continuous_idxPointerShift`, `monotoneOn_idxPointerShift`.

## The arena as a dynamics with a tick readout

* `arenaDynamics` — the flow of any smooth energy on the one-pointer arena, with `μ_FS ⊗ vol`;
* `arenaReadout` — the pointer rests in `readyArc 2` and displays in `displayArc`;
* `card_tickIndices_eq_zero_of_ready`, `card_tickIndices_eq_one_of_ready`;
* ★★ `graphDetector_isTickCount` — the count of a detector whose pointer never turns back.

## Arrival, then display

* ★★★ `graphDetector_arrival_display` — not displayed up to `t₁`, displayed at `t`;
* ★★★ `graphDetector_arrival_records` — the counts `0` at `t₁` and `1` at `t` are a record
  history of the start, in the semantics of `arenaReadout`;
* `flatTailD`, `flatTailD_mono`;
* ★★★ `torusDetector_arrival_flatPacket` — both statements for the flat packet of the lattice
  Dirac field of any dimension, with `ε = flatTailD t₁`, `q = 1 − flatTailD t`.

## Honest scope

⚠️ **On the fibres where the profile vanishes**, a null set of the pointer's conserved angle.
There the carrier moves freely. Off them nothing is shown.

⚠️ **The times `t₁`, `t₂` are hypotheses on the moving box.** That the box of UD-222 misses
`X` up to `t₁` and lies in `X` from `t₂` is assumed; no instance with numbers is given, and
the inequalities `κ ε t₁ ≤ 1/6`, `1/3 ≤ κ q (t − t₂)`, `κ (ε t₁ + t − t₁) ≤ 2/3` are not shown
to be met by any packet. The box moves at the group velocity; the bound against the graph
distance is `torusDetector_not_displayed`, not composed here.

⚠️ **Between `t₁` and `t₂` nothing is said about the display.** The record is "count `0` at
`t₁`, count `1` at `t`", not a time of arrival.

⚠️ **One pointer, read from the start.** The readout has one pointer. The facts are counts
from the flow time `0`.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297; `specs/unified-record-spacetime-plan.md` (UD-222,
UD-231, UD-234, UD-242); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/TorusDetector.lean` (`arenaObs_siteSetProj_packetD`,
`torusDetector_displayed_flatPacket`); `RecordLayer/GraphDetector.lean`
(`graphDetector_displayed`, `le_idxPointerShift_of_le`);
`RecordLayer/UnifiedRecordHistoryBridge.lean` (`TickReadout`, `pentaReadout`);
`RecordLayer/TickCountLaw.lean` (`isTickCount_pointer`, `tickIndices`);
`LF4/ArenaVolume.lean` (`kMuL_map_hamiltonianFlow`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix NormedSpace Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### Two stages of one integral -/

/-- An integrand at most `ε` up to `t₁` and at most `1` after it. -/
theorem integral_le_of_arrival {o : ℝ → ℝ} (ho : Continuous o) {t₁ t ε : ℝ} (h1 : 0 ≤ t₁)
    (h2 : t₁ ≤ t) (hε : ∀ s, 0 ≤ s → s ≤ t₁ → o s ≤ ε) (hone : ∀ s, 0 ≤ s → s ≤ t → o s ≤ 1) :
    ∫ s in (0 : ℝ)..t, o s ≤ ε * t₁ + (t - t₁) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (ho.intervalIntegrable 0 t₁)
    (ho.intervalIntegrable t₁ t)]
  have a : ∫ s in (0 : ℝ)..t₁, o s ≤ ∫ _ in (0 : ℝ)..t₁, ε :=
    intervalIntegral.integral_mono_on h1 (ho.intervalIntegrable 0 t₁) intervalIntegrable_const
      fun s hs => hε s hs.1 hs.2
  have b : ∫ s in t₁..t, o s ≤ ∫ _ in t₁..t, (1 : ℝ) :=
    intervalIntegral.integral_mono_on h2 (ho.intervalIntegrable t₁ t) intervalIntegrable_const
      fun s hs => hone s (h1.trans hs.1) hs.2
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at a b
  linarith

/-- A non-negative integrand that is at least `q` from `t₂`. -/
theorem le_integral_of_dwell {o : ℝ → ℝ} (ho : Continuous o) {t₂ t q : ℝ} (h1 : 0 ≤ t₂)
    (h2 : t₂ ≤ t) (h0 : ∀ s, 0 ≤ s → s ≤ t → 0 ≤ o s) (hq : ∀ s, t₂ ≤ s → s ≤ t → q ≤ o s) :
    q * (t - t₂) ≤ ∫ s in (0 : ℝ)..t, o s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (ho.intervalIntegrable 0 t₂)
    (ho.intervalIntegrable t₂ t)]
  have a : 0 ≤ ∫ s in (0 : ℝ)..t₂, o s :=
    intervalIntegral.integral_nonneg h1 fun s hs => h0 s hs.1 (hs.2.trans h2)
  have b : ∫ _ in t₂..t, q ≤ ∫ s in t₂..t, o s :=
    intervalIntegral.integral_mono_on h2 intervalIntegrable_const (ho.intervalIntegrable t₂ t)
      fun s hs => hq s hs.1 hs.2
  simp only [intervalIntegral.integral_const, smul_eq_mul] at b
  linarith

section Pointer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ}

/-- The occupancy along the carrier's orbit is continuous in the flow time. -/
theorem continuous_arenaObs_idxCarrierU (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (p : GenArena ι) :
    Continuous fun s : ℝ => arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) :=
  (continuous_arenaObs B₀).comp ((continuous_idxCarrierU hA hB hf φ).arenaKick continuous_const)

/-- ★★ **A pointer's displacement when the carrier arrives late.** On a fibre with rate
`κ = −2 f'(θ₂) ≥ 0`: if the detector's observable has expectation at most `ε` up to `t₁` and
at most `1` up to `t ≥ t₁`, the displacement at `t` is at most `κ (ε t₁ + (t − t₁))`. -/
theorem idxPointerShift_le_of_arrival (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {p : GenArena ι} {t₁ t ε : ℝ} (h1 : 0 ≤ t₁)
    (h2 : t₁ ≤ t)
    (hε : ∀ s, 0 ≤ s → s ≤ t₁ → arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) ≤ ε)
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) ≤ 1) :
    idxPointerShift hA hB hf φ p t ≤ -2 * hf.deriv_periodic.lift φ * (ε * t₁ + (t - t₁)) := by
  unfold idxPointerShift
  exact mul_le_mul_of_nonneg_left
    (integral_le_of_arrival (continuous_arenaObs_idxCarrierU hA hB hf φ p) h1 h2 hε hone) hκ

/-- ★★ **A pointer's displacement once the carrier dwells.** On a fibre with rate `κ ≥ 0`:
if the detector's observable has non-negative expectation up to `t` and at least `q` from
`t₂ ≤ t`, the displacement at `t` is at least `κ q (t − t₂)`. -/
theorem le_idxPointerShift_of_dwell (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {p : GenArena ι} {t₂ t q : ℝ} (h1 : 0 ≤ t₂)
    (h2 : t₂ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t → 0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p))
    (hq : ∀ s, t₂ ≤ s → s ≤ t → q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)) :
    -2 * hf.deriv_periodic.lift φ * (q * (t - t₂)) ≤ idxPointerShift hA hB hf φ p t := by
  unfold idxPointerShift
  exact mul_le_mul_of_nonneg_left
    (le_integral_of_dwell (continuous_arenaObs_idxCarrierU hA hB hf φ p) h1 h2 h0 hq) hκ

/-- The pointer's displacement is continuous in the flow time. -/
theorem continuous_idxPointerShift (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (p : GenArena ι) :
    Continuous fun t : ℝ => idxPointerShift hA hB hf φ p t := by
  unfold idxPointerShift
  exact continuous_const.mul (intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => (continuous_arenaObs_idxCarrierU hA hB hf φ p).intervalIntegrable a b) 0)

/-- On a fibre with rate `κ ≥ 0` and a non-negative occupancy up to `T`, the pointer never
turns back before `T`. -/
theorem monotoneOn_idxPointerShift (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {p : GenArena ι} {T : ℝ}
    (h0 : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)) :
    MonotoneOn (fun t : ℝ => idxPointerShift hA hB hf φ p t) (Icc 0 T) := by
  intro s hs t ht hst
  have hc := continuous_arenaObs_idxCarrierU hA hB hf φ p
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s t)
  have hnn : 0 ≤ ∫ u in s..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ u) p) :=
    intervalIntegral.integral_nonneg hst fun u hu => h0 u (hs.1.trans hu.1) (hu.2.trans ht.2)
  show idxPointerShift hA hB hf φ p s ≤ idxPointerShift hA hB hf φ p t
  unfold idxPointerShift
  exact mul_le_mul_of_nonneg_left (by linarith) hκ

end Pointer

/-! ### The arena as a dynamics with a tick readout -/

section Arena

variable {N : ℕ}

/-- **The one-pointer arena as a `ConstraintDynamics`**: the flow of a smooth energy for
`arenaForm`, with the measure `μ_FS ⊗ vol`. -/
def arenaDynamics {H : KSigma (N + 1) → ℝ} (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H)
    (p₀ : CPN (N + 1)) : ConstraintDynamics (KSigma (N + 1)) where
  muL := ⟨kMuL p₀, inferInstanceAs (IsFiniteMeasure (kMuL p₀))⟩
  flow := (arenaForm_isSymplectic N).hamiltonianFlow hH
  measurable_flow t := ((arenaForm_isSymplectic N).continuous_hamiltonianFlow hH t).measurable
  flow_zero x :=
    integralFlow_zero ((arenaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH) x
  flow_add s t x :=
    integralFlow_add ((arenaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH)
      s t x
  flow_preserves t :=
    ⟨((arenaForm_isSymplectic N).continuous_hamiltonianFlow hH t).measurable,
      kMuL_map_hamiltonianFlow N p₀ hH t⟩

/-- **The tick readout of the arena's pointer**: it rests when its first angle is in
`readyArc 2` and displays when it is in `displayArc`. -/
def arenaReadout {H : KSigma (N + 1) → ℝ} (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H)
    (p₀ : CPN (N + 1)) : TickReadout (arenaDynamics hH p₀) Unit where
  rest _ := Prod.snd ⁻¹' readyArc 2
  disp _ := Prod.snd ⁻¹' displayArc
  continuous_flow :=
    continuous_integralFlow ((arenaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH)
  rest_sigmaClosed _ := isSigmaClosed_readyArc.preimage continuous_snd
  disp_sigmaClosed _ := isSigmaClosed_displayArc.preimage continuous_snd
  disjoint _ := readyArc_disjoint_displayArc.preimage _

end Arena

/-- A ready pointer that has advanced to at most a third of a turn has no tick. -/
theorem card_tickIndices_eq_zero_of_ready {x₀ Δ : ℝ} (h0 : 0 < x₀) (hΔ : x₀ + Δ ≤ 1 / 3) :
    (tickIndices (1 / 6) (1 / 3) x₀ Δ).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  rw [mem_tickIndices] at hk
  have a : ((-1 : ℤ) : ℝ) < (k : ℝ) := by
    push_cast
    linarith [hk.1]
  have b : (k : ℝ) < ((0 : ℤ) : ℝ) := by
    push_cast
    linarith [hk.2]
  have a' : (-1 : ℤ) < k := by exact_mod_cast a
  have b' : k < 0 := by exact_mod_cast b
  omega

/-- A ready pointer that has advanced past a third of a turn, and not past four thirds, has
one tick. -/
theorem card_tickIndices_eq_one_of_ready {x₀ Δ : ℝ} (h0 : 0 < x₀) (h1 : x₀ ≤ 1 / 6)
    (hlo : 1 / 3 < x₀ + Δ) (hhi : x₀ + Δ ≤ 4 / 3) :
    (tickIndices (1 / 6) (1 / 3) x₀ Δ).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext k
  rw [mem_tickIndices, Finset.mem_singleton]
  constructor
  · rintro ⟨hk1, hk2⟩
    have a : ((-1 : ℤ) : ℝ) < (k : ℝ) := by
      push_cast
      linarith
    have b : (k : ℝ) < ((1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 1 := by exact_mod_cast b
    omega
  · rintro rfl
    rw [Int.cast_zero]
    constructor <;> linarith

/-! ### Arrival, then display -/

section Detector

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ} {N : ℕ}
  (e : ι ≃ Fin (N + 1))

/-- ★★ **The count of a detector whose pointer never turns back.** On a fibre with rate
`κ ≥ 0` and a non-negative occupancy up to `T ≥ 0`, the run's count at `T` is the number of
turns of `tickIndices` for the displacement at `T`. -/
theorem graphDetector_isTickCount (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) {p : GenArena ι} {θ : KTorus}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {T : ℝ} (hT : 0 ≤ T)
    (h0 : ∀ s, 0 ≤ s → s ≤ T →
      0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p)) :
    IsTickCount {x : KSigma (N + 1) | x.2 ∈ readyArc 2} {x : KSigma (N + 1) | x.2 ∈ displayArc}
      (fun s => (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) s
        (idxArenaEquiv e p, θ)) T
      (tickIndices (1 / 6) (1 / 3) (rep θ.1) (idxPointerShift hA hB hf θ.2 p T)).card :=
  isTickCount_pointer (π := Prod.snd) (q := θ)
    (D := fun t => idxPointerShift hA hB hf θ.2 p t) hT
    (continuous_idxPointerShift hA hB hf θ.2 p).continuousOn
    (monotoneOn_idxPointerShift hA hB hf hκ h0) (idxPointerShift_zero hA hB hf θ.2 p)
    fun t _ _ => by
      rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
      rfl

/-- ★★★ **Arrival, then display, in one run.** On a fibre with rate `κ = −2 f'(θ₂) ≥ 0`, from
a ready pointer: if the detector's observable has expectation in `[0, 1]` along the carrier's
orbit up to `t`, at most `ε` up to `t₁` and at least `q` from `t₂`, with `0 ≤ t₁ ≤ t₂ ≤ t`,
`κ ε t₁ ≤ 1/6`, `1/3 ≤ κ q (t − t₂)` and `κ (ε t₁ + (t − t₁)) ≤ 2/3`, then the pointer is not
displayed at any flow time up to `t₁` and is displayed at `t`. -/
theorem graphDetector_arrival_display (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) {p : GenArena ι} {θ : KTorus}
    (hθ : θ ∈ readyArc 2) (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {t₁ t₂ t ε q : ℝ}
    (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) ≤ 1)
    (hε : ∀ s, 0 ≤ s → s ≤ t₁ →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) ≤ ε)
    (hq : ∀ s, t₂ ≤ s → s ≤ t →
      q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (hbefore : -2 * hf.deriv_periodic.lift θ.2 * (ε * t₁) ≤ 1 / 6)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2 * (q * (t - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift θ.2 * (ε * t₁ + (t - t₁)) ≤ 2 / 3) :
    (∀ u, 0 ≤ u → u ≤ t₁ →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) u
        (idxArenaEquiv e p, θ)).2 ∉ displayArc)
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∈ displayArc := by
  have ht1 : t₁ ≤ t := h12.trans h2
  have hε0 : 0 ≤ ε := (h0 0 le_rfl (h1.trans ht1)).trans (hε 0 le_rfl h1)
  refine ⟨fun u hu hu1 => ?_, ?_⟩
  · rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
    have hlow := le_idxPointerShift_of_le hA hB hf hκ hu
      (fun s hs hsu => h0 s hs (hsu.trans (hu1.trans ht1)))
    have hup := idxPointerShift_le_of_arrival hA hB hf hκ hu le_rfl
      (fun s hs hsu => hε s hs (hsu.trans hu1))
      (fun s hs hsu => hone s hs (hsu.trans (hu1.trans ht1)))
    have hmono : -2 * hf.deriv_periodic.lift θ.2 * (ε * u + (u - u))
        ≤ -2 * hf.deriv_periodic.lift θ.2 * (ε * t₁) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hκ
    exact pshift_notMem_displayArc_of_le hθ (by linarith) (by linarith)
  · rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
    exact pshift_mem_displayArc hθ
      (hlo.trans (le_idxPointerShift_of_dwell hA hB hf hκ (h1.trans h12) h2 h0 hq))
      ((idxPointerShift_le_of_arrival hA hB hf hκ h1 ht1 hε hone).trans hhi)

/-- ★★★ **The detector's two counts are a record history of the run's start.** Under the
hypotheses of `graphDetector_arrival_display`, the start of the run is in the compatible
region of the two facts "the pointer has counted `0` at `t₁`" and "the pointer has counted
`1` at `t`", in the record semantics of the arena's tick readout. -/
theorem graphDetector_arrival_records (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (p₀ : CPN (N + 1)) {p : GenArena ι}
    {θ : KTorus} (hθ : θ ∈ readyArc 2) (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2)
    {t₁ t₂ t ε q : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) ≤ 1)
    (hε : ∀ s, 0 ≤ s → s ≤ t₁ →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) ≤ ε)
    (hq : ∀ s, t₂ ≤ s → s ≤ t →
      q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (hbefore : -2 * hf.deriv_periodic.lift θ.2 * (ε * t₁) ≤ 1 / 6)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2 * (q * (t - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift θ.2 * (ε * t₁ + (t - t₁)) ≤ 2 / 3) :
    ((idxArenaEquiv e p, θ) : KSigma (N + 1))
      ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy (Matrix.reindex e e A₀)
          (Matrix.reindex e e B₀) hf hc) p₀).semantics
        [TickReadout.startFact () t₁ 0, TickReadout.startFact () t 1] := by
  have ht1 : t₁ ≤ t := h12.trans h2
  have hr : rep θ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hθ
  rw [shearWidth_two] at hr
  have c0 := graphDetector_isTickCount e hA hB hf hc hκ h1
    (fun s hs hs1 => h0 s hs (hs1.trans ht1))
  have hup1 := idxPointerShift_le_of_arrival hA hB hf hκ h1 le_rfl hε
    (fun s hs hs1 => hone s hs (hs1.trans ht1))
  rw [sub_self, add_zero] at hup1
  rw [card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
  have c1 := graphDetector_isTickCount e hA hB hf hc hκ (h1.trans ht1) h0
  have hlow := le_idxPointerShift_of_dwell hA hB hf hκ (h1.trans h12) h2 h0 hq
  have hup := idxPointerShift_le_of_arrival hA hB hf hκ h1 ht1 hε hone
  rw [card_tickIndices_eq_one_of_ready hr.1 hr.2 (by linarith [hr.1])
    (by linarith [hr.2])] at c1
  refine (arenaReadout (contMDiff_coupledEnergy (Matrix.reindex e e A₀)
    (Matrix.reindex e e B₀) hf hc) p₀).mem_compatibleSet_startFacts
    [((), t₁, 0), ((), t, 1)] _ fun r hr' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  exacts [c0, c1]

end Detector

/-! ### The flat packet on the torus -/

section Torus

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S] {L : ℕ}
  [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- **The bound on a flat packet's weight outside its moving box** at the flow time `τ ≥ 0`,
of `regionWeightD_flatPacket_compl_movedBoxD_le_window`:
`Σ_i (1/N_i + η + τ (2π/L) windowStepErrD_i) / (1 − γ_i)`. -/
def flatTailD (L : ℕ) (J μ : ℝ) (Nw : κ → ℕ) (w γ : κ → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, (1 / (Nw i : ℝ) + alignDefect L J μ
    + τ * (2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L))) / (1 - γ i)

omit [DecidableEq κ] [NeZero L] in
/-- The bound grows with the flow time. -/
theorem flatTailD_mono {J μ : ℝ} (hμ : 0 < μ) (Nw : κ → ℕ) {w γ : κ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hγ : ∀ i, γ i < 1) {s t : ℝ} (hst : s ≤ t) :
    flatTailD L J μ Nw w γ s ≤ flatTailD L J μ Nw w γ t := by
  unfold flatTailD
  refine Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right ?_ (sub_pos.2 (hγ i)).le
  have h2 : 0 ≤ 2 * Real.pi / L := div_nonneg (by positivity) (Nat.cast_nonneg L)
  have hc0 : 0 ≤ 2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L) :=
    mul_nonneg h2 (windowStepErrD_nonneg hμ hw0 i h2)
  have := mul_le_mul_of_nonneg_right hst hc0
  linarith

variable {f : ℝ → ℝ} {N : ℕ} [Nonempty S]

omit [Nonempty S] in
/-- ★★★ **A detector on the torus: the flat packet arrives, and then the pointer displays.**
For the flat packet of the lattice Dirac field with `μ > 0` on a window of `N_i < L` momenta
per axis within `w_i` of `k₀`, and a detector on the sites `X`: suppose the packet's moving
box misses `X` at every flow time up to `t₁` and lies in `X` from `t₂` to `t`, with
`0 ≤ t₁ ≤ t₂ ≤ t`. On a fibre where the profile vanishes and `κ = −2 f'(θ₂) ≥ 0`, from a
ready pointer, with `ε = flatTailD t₁` and `q = 1 − flatTailD t`: if `κ ε t₁ ≤ 1/6`,
`1/3 ≤ κ q (t − t₂)` and `κ (ε t₁ + (t − t₁)) ≤ 2/3`, then the pointer is not displayed at
any flow time up to `t₁`, it is displayed at `t`, and the counts `0` at `t₁` and `1` at `t`
are a record history of the run's start. -/
theorem torusDetector_arrival_flatPacket (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (p₀ : CPN (N + 1)) (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] {θ : KTorus}
    (hθ : θ ∈ readyArc 2) (h0 : hf.lift θ.2 = 0)
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {t₁ t₂ t : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2 : t₂ ≤ t)
    (hout : ∀ s, 0 ≤ s → s ≤ t₁ → Disjoint X (movedBoxD L J μ k₀ (fun _ => 1) γ s))
    (hin : ∀ s, t₂ ≤ s → s ≤ t → movedBoxD L J μ k₀ (fun _ => 1) γ s ⊆ X)
    (hbefore : -2 * hf.deriv_periodic.lift θ.2 * (flatTailD L J μ Nw w γ t₁ * t₁) ≤ 1 / 6)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2
      * ((1 - flatTailD L J μ Nw w γ t) * (t - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift θ.2
      * (flatTailD L J μ Nw w γ t₁ * t₁ + (t - t₁)) ≤ 2 / 3) :
    ((∀ u, 0 ≤ u → u ≤ t₁ →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst (X : Set (κ → ZMod L)))) hf hc) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc)
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst (X : Set (κ → ZMod L)))) hf hc) t
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∈ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
            (Matrix.reindex e e (siteSetProj Prod.fst (X : Set (κ → ZMod L)))) hf hc)
            p₀).semantics
          [TickReadout.startFact () t₁ 0, TickReadout.startFact () t 1] := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  have hnorm : ∀ s : ℝ, (chainInnerD
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)).re
        = 1 := fun s => by
    rw [chainInnerD_packetD_unitAmpD h he hn hμ hD, sum_flatAmpD_sq lo hN, Complex.ofReal_re]
  have hBh : (siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L)
      (X : Set (κ → ZMod L))).IsHermitian := siteSetProj_isHermitian _ _
  have hocc : ∀ s : ℝ,
      arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
          (arenaKick (idxCarrierU (latticeDiracHam_isHermitian (L := L) h J μ)
            hBh hf θ.2 s) (Projectivization.mk ℂ _ hp))
        = regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) s) X := fun s => by
    rw [idxCarrierU_of_lift_eq_zero _ _ hf h0,
      arenaObs_siteSetProj_packetD h J μ e₀ _ _ hp X s, hnorm 0, div_one]
  have hsplit : ∀ (s : ℝ) (A : Finset (κ → ZMod L)),
      regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) s) A
        + regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) s) Aᶜ = 1 := fun s A => by
    rw [regionWeightD_add_compl, hnorm s]
  have hcompl : ∀ s : ℝ, 0 ≤ s →
      regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) s) (movedBoxD L J μ k₀ (fun _ => 1) γ s)ᶜ
        ≤ flatTailD L J μ Nw w γ s := fun s hs => by
    have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
      lo hN hNL k₀ hw0 hw s hγ
    rw [abs_of_nonneg hs] at hh
    rw [flatTailD]
    exact hh
  have a0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxCarrierU (latticeDiracHam_isHermitian (L := L) h J μ)
          hBh hf θ.2 s) (Projectivization.mk ℂ _ hp)) :=
    fun s _ _ => by
      rw [hocc s]
      exact regionWeightD_nonneg _ _
  have a1 : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxCarrierU (latticeDiracHam_isHermitian (L := L) h J μ)
          hBh hf θ.2 s) (Projectivization.mk ℂ _ hp)) ≤ 1 :=
    fun s _ _ => by
      rw [hocc s]
      linarith [hsplit s X, regionWeightD_nonneg (packetD (L := L) α β J μ e₀
        (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s) Xᶜ]
  have aε : ∀ s, 0 ≤ s → s ≤ t₁ →
      arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxCarrierU (latticeDiracHam_isHermitian (L := L) h J μ)
          hBh hf θ.2 s) (Projectivization.mk ℂ _ hp))
        ≤ flatTailD L J μ Nw w γ t₁ := fun s hs hs1 => by
      rw [hocc s]
      exact ((regionWeightD_mono _ (le_compl_iff_disjoint_right.2 (hout s hs hs1))).trans
        (hcompl s hs)).trans (flatTailD_mono hμ Nw hw0 hγ hs1)
  have aq : ∀ s, t₂ ≤ s → s ≤ t →
      1 - flatTailD L J μ Nw w γ t
        ≤ arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
          (arenaKick (idxCarrierU (latticeDiracHam_isHermitian (L := L) h J μ)
            hBh hf θ.2 s) (Projectivization.mk ℂ _ hp)) :=
    fun s hs hst => by
      rw [hocc s]
      have hs0 : 0 ≤ s := (h1.trans h12).trans hs
      have hm := regionWeightD_mono (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) s) (hin s hs hst)
      linarith [hsplit s (movedBoxD L J μ k₀ (fun _ => 1) γ s), hcompl s hs0,
        flatTailD_mono (L := L) (J := J) hμ Nw hw0 hγ hst]
  exact ⟨graphDetector_arrival_display e (latticeDiracHam_isHermitian h J μ)
      hBh hf hc hθ hκ h1 h12 h2 a0 a1 aε aq hbefore hlo hhi,
    graphDetector_arrival_records e (latticeDiracHam_isHermitian h J μ)
      hBh hf hc p₀ hθ hκ h1 h12 h2 a0 a1 aε aq hbefore hlo hhi⟩

end Torus

end CSD.RecordLayer

end
