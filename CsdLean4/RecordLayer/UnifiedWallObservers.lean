/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedOddWall
public import CsdLean4.RecordLayer.UnifiedClockAtRest

/-!
# The carriers on the walled chain: where the messenger is, and a clock beside a wall

**Category:** 7-SigmaLayer (the record layer). BACKLOG #408 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; of item R2 of the list under
UD-164: the messenger through the reflection, the wall state of a two-level clock, and the
clock at rest beside a wall. No new assumption beyond UA-18 (a), (b).

#407 has the wall state of one Dirac packet with its weight controlled by hypotheses on the
packet's and the mirror packet's weights. This module discharges those hypotheses from #265,
shows that the wall state of a packet is itself a ring packet on the window joined with its
reflection, with odd amplitudes, and uses that for the two-level clock.

* ★★ `regionWeight_oddWall_away_le` — the messenger's wall state, at every packet time: its
  weight on a region away from the packet's predicted direction and from the mirror
  direction, times `1 − γ`, is at most twice the sum of the two budgets of #265;
* `oddExt`, ★★ `ringPacket_oddExt` — the wall state of a packet is the ring packet on
  `W ∪ −W` with the odd extension of the amplitudes; `sum_norm_oddExt`;
* ★ `devicePacket_oddExt`, `chainParity_devicePacket_wall`, `deviceRegionWeight_wall` — the
  two-level clock's packet on such a window: each level is a wall state, it is mirror-odd,
  and its weight on a region is the mean of the two levels' wall-state weights;
* ★★ `deviceRegionWeight_wall_away_le` — the clock's wall state away from the four predicted
  directions;
* `wallWindow`, `wallWindow_neg_notMem`, `sum_norm_flatAmpN_wall`,
  ★★★ `wall_clock_ticks` — **a clock at rest beside a wall ticks**: the modes `±1, …, ±N`
  with odd flat amplitudes are a mirror-odd device packet at reference momentum `0`, and it
  meets `narrow_clock_packet_ticks`: at least `n` ticks at the rate `Δ`.

## Exact scope

* **The odd sector of the ring**, as #407: not shown to be a chain with hard ends.
* **The reflection is a bound on weights.** `regionWeight_oddWall_away_le` says the wall
  state is, up to the budgets, within the two arcs about the packet's predicted direction
  and its mirror image, at every packet time, also while the two arcs cross at a wall. On the
  folded chain those two arcs are one place. The budgets are those of #265 and are not
  evaluated here for any window; no number is exhibited.
* **The clock beside the wall: ticks, with every hypothesis discharged; its place, not.**
  `wall_clock_ticks` has no hypothesis but the sizes. That this packet sits beside the wall
  follows from `deviceRegionWeight_wall_away_le` with the four budgets, which are not
  evaluated for `wallWindow`. This removes risk (iii) of UA-18: the modes `±1, …, ±N`
  replace the modes `0, …, N − 1`, whose mirror image is not orthogonal to them.
* **A moving clock's wall state does not yet tick.** For a window about a momentum `p₀ ≠ 0`
  the wall state's window `W ∪ −W` is not narrow about one momentum, so #391's theorem does
  not apply to it; the rates at `m` and `−m` are equal, and a version of #391 in the modulus
  of the momentum is owed.
* **Uncoupled carriers; one fibre and one start for the ticks**, as #391. No gate, no
  messenger with a clock, no history of UD-170.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-8,
UA-12, UA-18, UO-16, UD-142, UD-143, UD-164, UD-170, UD-173, UD-174, UD-175);
`RecordLayer/UnifiedOddWall.lean` (#407: `oddWall`, `regionWeight_oddWall_le`,
`chainParity_oddWall`); `RecordLayer/DiracArrival.lean` (#265: `regionWeight_ringPacket_le`);
`RecordLayer/UnifiedClockPacketLocalised.lean` (#392: `deviceRegionWeight_devicePacket`,
`flatAmpN`); `RecordLayer/UnifiedClockPacketInstance.lean` (#391:
`narrow_clock_packet_ticks`); `CV/DiracPacketLimit.lean` (`ringPacket`, `unitAmp`,
`limitErr`, `flat_sums`); `CV/DiracDevice.lean` (`devicePacket`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

section Wall

variable {L : ℕ} [NeZero L]

/-! ### The messenger through the reflection -/

/-- ★★ **Where the messenger's wall state is.** For a ring packet under the hypotheses of
#265's `regionWeight_ringPacket_le`, at every packet time `t`: the weight of its wall state on
a region `B` whose sites lie at `cos ≤ γ < 1` from the packet's predicted direction and from
the mirror direction, times `1 − γ`, is at most twice the sum of the packet's and the mirror
packet's budgets. -/
theorem regionWeight_oddWall_away_le {c μ ℓ P D p₀ : ℝ} (hc : 0 < c) (hμ : 0 < μ)
    (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {B : Finset (ZMod L)} {γ : ℝ} (hγ : γ < 1) (t : ℝ)
    (hB : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ (c * p₀) * t) ≤ γ)
    (hB' : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ (c * -p₀) * t) ≤ γ) :
    regionWeight (oddWall (L := L) c μ ℓ W β t) B * (1 - γ)
      ≤ 2 * ((1 - (transPhase (ringPacket (L := L) c μ ℓ W β 0)).re
              + |t| * limitErr c μ ℓ D P (ℓ / L))
            + (1 - (transPhase (mirrorPacket (L := L) c μ ℓ W β 0)).re
              + |t| * limitErr c μ ℓ D P (ℓ / L))) := by
  have hγ' : 0 < 1 - γ := by linarith
  have hWin' : ∀ m ∈ negWin W, (2 - lo - L : ℤ) ≤ m ∧ m + 1 < (2 - lo - L : ℤ) + L := by
    intro m hm
    obtain ⟨h1, h2⟩ := hWin (-m) ((mem_negWin W m).1 hm)
    constructor <;> omega
  have hWD' : ∀ m ∈ negWin W, |2 * Real.pi * m / ℓ - -p₀| ≤ D := by
    intro m hm
    have h := hWD (-m) ((mem_negWin W m).1 hm)
    rw [show 2 * Real.pi * (m : ℝ) / ℓ - -p₀
        = -(2 * Real.pi * ((-m : ℤ) : ℝ) / ℓ - p₀) by push_cast; ring, abs_neg]
    exact h
  have hβ' : ∑ m ∈ negWin W, ‖β (-m)‖ ^ 2 = 1 := by
    rw [negWin, Finset.sum_image (fun x _ y _ h => neg_injective h)]
    simpa using hβ
  have a := regionWeight_ringPacket_le (L := L) hc hμ hℓ hp₀ hD0 hWin hWD β hβ t hB
  have a' := regionWeight_ringPacket_le (L := L) (p₀ := -p₀) (P := P) hc hμ hℓ
    (by rw [abs_neg]; exact hp₀) hD0 hWin' hWD' (fun m => β (-m)) hβ' t hB'
  set bR := 1 - (transPhase (ringPacket (L := L) c μ ℓ W β 0)).re
    + |t| * limitErr c μ ℓ D P (ℓ / L) with hbR
  set bM := 1 - (transPhase (mirrorPacket (L := L) c μ ℓ W β 0)).re
    + |t| * limitErr c μ ℓ D P (ℓ / L) with hbM
  have a'' : regionWeight (mirrorPacket (L := L) c μ ℓ W β t) B * (1 - γ) ≤ bM := a'
  have hwR := regionWeight_nonneg (ringPacket (L := L) c μ ℓ W β t) B
  have hwM := regionWeight_nonneg (mirrorPacket (L := L) c μ ℓ W β t) B
  have hbR0 : 0 ≤ bR := le_trans (mul_nonneg hwR hγ'.le) a
  have hbM0 : 0 ≤ bM := le_trans (mul_nonneg hwM hγ'.le) a''
  have hτ : 0 ≤ (bR + bM) / (1 - γ) := div_nonneg (by linarith) hγ'.le
  have hR : regionWeight (ringPacket (L := L) c μ ℓ W β t) B ≤ (bR + bM) / (1 - γ) := by
    rw [le_div_iff₀ hγ']
    linarith
  have hM : regionWeight (mirrorPacket (L := L) c μ ℓ W β t) B ≤ (bR + bM) / (1 - γ) := by
    rw [le_div_iff₀ hγ']
    linarith
  have h := regionWeight_oddWall_le (L := L) B hτ hR hM
  calc regionWeight (oddWall (L := L) c μ ℓ W β t) B * (1 - γ)
      ≤ 2 * ((bR + bM) / (1 - γ)) * (1 - γ) := mul_le_mul_of_nonneg_right h hγ'.le
    _ = 2 * (bR + bM) := by field_simp

/-! ### The wall state as a packet on the window joined with its reflection -/

/-- **The odd extension of amplitudes** from a window `W` to `W ∪ −W`, over `√2`. -/
def oddExt (W : Finset ℤ) (β : ℤ → ℂ) (m : ℤ) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if m ∈ W then β m else -β (-m))

/-- ★★ **The wall state of a packet is the ring packet on `W ∪ −W` with the odd extension of
its amplitudes**, when no momentum of `W` is the opposite of another. -/
theorem ringPacket_oddExt (c μ ℓ : ℝ) {W : Finset ℤ} (hW : ∀ m ∈ W, -m ∉ W) (β : ℤ → ℂ)
    (t : ℝ) :
    ringPacket (L := L) c μ ℓ (W ∪ negWin W) (oddExt W β) t = oddWall c μ ℓ W β t := by
  have hdisj : Disjoint W (negWin W) :=
    Finset.disjoint_left.2 fun m hm hm' => hW m hm ((mem_negWin W m).1 hm')
  rw [oddWall, mirrorPacket, ringPacket, ringPacket, ringPacket, packet, packet, packet,
    Finset.sum_union hdisj, smul_add, smul_neg, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [smul_smul]
    congr 1
    simp only [unitAmp, oddExt, hm, ↓reduceIte]
    ring
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ∉ W := fun h => hW m h ((mem_negWin W m).1 hm)
    rw [smul_smul, ← neg_smul]
    congr 1
    simp only [unitAmp, oddExt, hm', ↓reduceIte]
    ring

omit [NeZero L] in
/-- The odd extension of normalised amplitudes is normalised. -/
theorem sum_norm_oddExt {W : Finset ℤ} (hW : ∀ m ∈ W, -m ∉ W) {β : ℤ → ℂ}
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) : ∑ m ∈ W ∪ negWin W, ‖oddExt W β m‖ ^ 2 = 1 := by
  have hdisj : Disjoint W (negWin W) :=
    Finset.disjoint_left.2 fun m hm hm' => hW m hm ((mem_negWin W m).1 hm')
  have hc : ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ ^ 2 = 1 / 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by norm_num)), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h1 : ∀ m ∈ W, ‖oddExt W β m‖ ^ 2 = 1 / 2 * ‖β m‖ ^ 2 := fun m hm => by
    simp only [oddExt, hm, ↓reduceIte]
    rw [norm_mul, mul_pow, hc]
  have h2 : ∀ m ∈ W, ‖oddExt W β (-m)‖ ^ 2 = 1 / 2 * ‖β m‖ ^ 2 := fun m hm => by
    simp only [oddExt, hW m hm, ↓reduceIte, neg_neg]
    rw [norm_mul, norm_neg, mul_pow, hc]
  rw [Finset.sum_union hdisj, negWin, Finset.sum_image (fun x _ y _ h => neg_injective h),
    Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, hβ]
  norm_num

/-! ### The two-level clock's wall state -/

/-- ★ **Each level of the clock's packet on `W ∪ −W` with odd amplitudes is a wall state.** -/
theorem devicePacket_oddExt (c ℓ μ₀ μ₁ : ℝ) {W : Finset ℤ} (hW : ∀ m ∈ W, -m ∉ W)
    (β : ℤ → ℂ) (t : ℝ) (p : ZMod L × Fin 2) (i : Fin 2) :
    devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (W ∪ negWin W) (oddExt W β) t (p, i)
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * oddWall c (levelMass μ₀ μ₁ i) ℓ W β t p := by
  rw [← ringPacket_oddExt c _ ℓ hW β t]
  rfl

/-- The clock's wall state is mirror-odd at each level. -/
theorem chainParity_devicePacket_wall (c ℓ μ₀ μ₁ : ℝ) {W : Finset ℤ} (hW : ∀ m ∈ W, -m ∉ W)
    (β : ℤ → ℂ) (t : ℝ) (i : Fin 2) :
    chainParity (fun p => devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (W ∪ negWin W)
        (oddExt W β) t (p, i))
      = -fun p => devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (W ∪ negWin W)
        (oddExt W β) t (p, i) := by
  have e : (fun p => devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (W ∪ negWin W)
        (oddExt W β) t (p, i))
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • oddWall c (levelMass μ₀ μ₁ i) ℓ W β t := by
    funext p
    rw [devicePacket_oddExt c ℓ μ₀ μ₁ hW β t p i]
    rfl
  rw [e, chainParity_smul, chainParity_oddWall, smul_neg]

/-- The clock's wall state has, on a region, the mean of its two levels' wall-state weights. -/
theorem deviceRegionWeight_wall (c ℓ μ₀ μ₁ : ℝ) {W : Finset ℤ} (hW : ∀ m ∈ W, -m ∉ W)
    (β : ℤ → ℂ) (t : ℝ) (B : Finset (ZMod L)) :
    deviceRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (W ∪ negWin W)
        (oddExt W β) t) B
      = (regionWeight (oddWall (L := L) c μ₀ ℓ W β t) B
          + regionWeight (oddWall (L := L) c μ₁ ℓ W β t) B) / 2 := by
  rw [deviceRegionWeight_devicePacket, ringPacket_oddExt c μ₀ ℓ hW,
    ringPacket_oddExt c μ₁ ℓ hW]

/-- ★★ **Where the clock's wall state is.** Under the hypotheses of
`regionWeight_oddWall_away_le` for both levels: the clock's weight on a region at
`cos ≤ γ < 1` from the four predicted directions, times `1 − γ`, is at most the sum of the
four budgets. -/
theorem deviceRegionWeight_wall_away_le {c μ₀ μ₁ ℓ P D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀)
    (h1 : 0 < μ₁) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hW : ∀ m ∈ W, -m ∉ W) (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {B : Finset (ZMod L)} {γ : ℝ} (hγ : γ < 1) (t : ℝ)
    (hB0 : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) * t) ≤ γ)
    (hB0' : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ₀ (c * -p₀) * t) ≤ γ)
    (hB1 : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ₁ (c * p₀) * t) ≤ γ)
    (hB1' : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ₁ (c * -p₀) * t) ≤ γ) :
    deviceRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ (W ∪ negWin W)
        (oddExt W β) t) B * (1 - γ)
      ≤ ((1 - (transPhase (ringPacket (L := L) c μ₀ ℓ W β 0)).re
            + |t| * limitErr c μ₀ ℓ D P (ℓ / L))
          + (1 - (transPhase (mirrorPacket (L := L) c μ₀ ℓ W β 0)).re
            + |t| * limitErr c μ₀ ℓ D P (ℓ / L)))
        + ((1 - (transPhase (ringPacket (L := L) c μ₁ ℓ W β 0)).re
            + |t| * limitErr c μ₁ ℓ D P (ℓ / L))
          + (1 - (transPhase (mirrorPacket (L := L) c μ₁ ℓ W β 0)).re
            + |t| * limitErr c μ₁ ℓ D P (ℓ / L))) := by
  have a0 := regionWeight_oddWall_away_le (L := L) hc h0 hℓ hp₀ hD0 hWin hWD β hβ hγ t hB0
    hB0'
  have a1 := regionWeight_oddWall_away_le (L := L) hc h1 hℓ hp₀ hD0 hWin hWD β hβ hγ t hB1
    hB1'
  rw [deviceRegionWeight_wall c ℓ μ₀ μ₁ hW]
  have e : (regionWeight (oddWall (L := L) c μ₀ ℓ W β t) B
        + regionWeight (oddWall (L := L) c μ₁ ℓ W β t) B) / 2 * (1 - γ)
      = (regionWeight (oddWall (L := L) c μ₀ ℓ W β t) B * (1 - γ)
        + regionWeight (oddWall (L := L) c μ₁ ℓ W β t) B * (1 - γ)) / 2 := by ring
  rw [e]
  linarith

end Wall

/-! ### A clock at rest beside a wall -/

/-- **The wall window**: the modes `1, …, N`. With its reflection it is `±1, …, ±N`. -/
def wallWindow (N : ℕ) : Finset ℤ := Finset.Ico 1 (1 + N)

theorem wallWindow_neg_notMem (N : ℕ) : ∀ m ∈ wallWindow N, -m ∉ wallWindow N := by
  intro m hm h
  rw [wallWindow, Finset.mem_Ico] at hm h
  omega

theorem sum_norm_flatAmpN_wall {N : ℕ} (hN : 0 < N) :
    ∑ m ∈ wallWindow N, ‖flatAmpN N m‖ ^ 2 = 1 := by
  have hpos : 0 ≤ 1 / Real.sqrt N := by positivity
  have h := (flat_sums 1 hN).1
  simpa [wallWindow, flatAmpN, Complex.norm_real, abs_of_nonneg hpos] using h

/-- ★★★ **A clock at rest beside a wall ticks.** The two-level clock's packet on the modes
`±1, …, ±N` of the ring of length `2π · 1200 n N`, with the odd extension of flat amplitudes:
it is the wall state of the packet on `1, …, N` (`devicePacket_oddExt`), mirror-odd
(`chainParity_devicePacket_wall`), and it meets `narrow_clock_packet_ticks` at reference
momentum `0`. For some strength the count at `T = 2π n/R` is at least `n`, and the
operational time per flow time is within `1/n + Δ` of `√(1 − v²)` with `v` the velocity term
at momentum `0`. -/
theorem wall_clock_ticks {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ))) ≠ 0) (N' : ℕ),
      n ≤ N'
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M (ringHop (1200 * n * N) M) 1 (1 + Δ) g
            trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          (2 * Real.pi * n / ringRate (1200 * n * N) M 0 Δ) N'
      ∧ |clockOpTime 1 (1 + Δ) N' / (2 * Real.pi * n / ringRate (1200 * n * N) M 0 Δ)
            - Real.sqrt (1 - (vRel 1 1 (ringSigma (1200 * n * N) M 0) / 1) ^ 2)|
          ≤ 1 / n + Δ := by
  have hK : 0 < 1200 * n * N := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : 3 * N ≤ M := by
    have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    have h2 : 3 * N ≤ 210000 * n ^ 2 * N := Nat.mul_le_mul_right N (by nlinarith)
    exact h2.trans hM
  have hz : (3 * N : ℤ) ≤ M := by exact_mod_cast h3
  have hmem : ∀ m ∈ wallWindow N ∪ negWin (wallWindow N), (-N : ℤ) ≤ m ∧ m ≤ N := by
    intro m hm
    rcases Finset.mem_union.1 hm with h | h
    · rw [wallWindow, Finset.mem_Ico] at h
      constructor <;> omega
    · have h' := (mem_negWin _ m).1 h
      rw [wallWindow, Finset.mem_Ico] at h'
      constructor <;> omega
  have hWin : ∀ m ∈ wallWindow N ∪ negWin (wallWindow N),
      (-N : ℤ) ≤ m ∧ m + 1 < (-N : ℤ) + ((M + 1 : ℕ) : ℤ) := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmem m hm
    refine ⟨h1, ?_⟩
    push_cast
    omega
  have hWD : ∀ m ∈ wallWindow N ∪ negWin (wallWindow N),
      |(m : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 0| ≤ 1 / (600 * n) := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmem m hm
    have h1' : (-(N : ℝ)) ≤ m := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ N := by exact_mod_cast h2
    have habs : |(m : ℝ)| ≤ N := abs_le.2 ⟨h1', h2'⟩
    have hden : (0 : ℝ) < 1200 * n * N := by positivity
    push_cast
    rw [sub_zero, abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
    nlinarith [abs_nonneg (m : ℝ)]
  obtain ⟨-, g, hΨ, N', a1, a2, -, a4⟩ := narrow_clock_packet_ticks (lo := -N) (p₀ := 0)
    (M := M) hn hK le_rfl (by norm_num) (by rw [mul_zero]; positivity) hWin (fun m hm => Or.inl (hWD m hm))
    (oddExt (wallWindow N) (flatAmpN N))
    (sum_norm_oddExt (wallWindow_neg_notMem N) (sum_norm_flatAmpN_wall hN)) hΔ0 hΔ
  exact ⟨g, hΨ, N', a1, a2, a4⟩

end CSD.RecordLayer

end
