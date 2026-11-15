/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracReturn
public import CsdLean4.RecordLayer.UnifiedArrivalRecord

/-!
# The wall: a packet minus its mirror image

**Category:** 7-SigmaLayer (the record layer). BACKLOG #407 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; of item R2 of the list under
UD-164, the wall for one Dirac carrier. No new assumption beyond UA-18 (a).

UA-18 (a) takes the chain with two walls to be the mirror-odd sector of the ring: reflect the
sites, change the sign of the lower component. #270 (`RecordLayer/DiracReturn.lean`) has that
mirror (`chainParity`), that it commutes with the energy, that it sends a packet to the
packet of the reflected window, and bounds for a packet *plus* its image (the even sector).
This module states the odd sector for any ring packet.

* `negWin`, `mem_negWin`, `mirrorPacket`, `chainParity_ringPacket_negWin`,
  `chainParity_mirrorPacket`, `chainParity_neg`;
* `oddWall` — a ring packet minus its mirror packet, over `√2`;
* ★★ `chainParity_oddWall` — it is mirror-odd at every packet time;
* ★ `odd_apply_eq_zero`, `oddWall_apply_eq_zero` — a mirror-odd state has no upper component
  at a site that is its own mirror image: the boundary condition of UA-18 (a);
* ★ `chainProp_oddWall` — the ring's evolution carries it to itself at the later time;
* `regionWeight_neg`, `chainInner_neg_right`, `chainInner_neg_neg`,
  `chainInner_ringPacket_mirrorPacket`, `chainInner_oddWall`;
* ★★ `regionWeight_oddWall_le` — where neither the packet nor its mirror packet has weight
  above `τ`, the wall state has at most `2τ`;
* ★★ `le_regionWeight_oddWall` — where both have all but `τ`, it has at least `1 − 2τ`;
* `ne_zero_of_chainInner_eq_one`, ★★★ `arenaObs_regionProj_oddWall` — along the uncoupled
  orbit of the wall state's ray, the expectation of a region projector is the wall state's
  weight on the region at that time.

## Exact scope

* **The odd sector of the ring, not a chain.** The carrier's index is still the ring's. That
  the odd sector with this energy is a chain of half the sites with hard ends and a `√2` hop
  at the end sites (UA-18 (a)) is not stated in Lean. What is shown is that the state is
  mirror-odd, stays so, and has no upper component at the self-mirror sites.
* **One Dirac carrier.** The messenger. A clock carrier has two levels (`deviceHam`); its
  wall state is not built. A clock at rest beside a wall is not orthogonal to its mirror
  image (UA-18, risk (iii)) and is not treated.
* **Weights from weights.** The two bounds take, as hypotheses, bounds on the packet's and on
  the mirror packet's weight on a region. #265's `regionWeight_ringPacket_le` gives such
  bounds for both (the mirror packet is a ring packet at the opposite momentum); no window,
  region or time is instantiated here, so no reflection is exhibited.
* **Orthogonality and norm are hypotheses** of the lower bound and of the arena statement:
  `chainInner_ringPacket_mirrorPacket` gives the orthogonality when no momentum of the window
  is the opposite of another modulo the ring; the packets' norms are #261's.
* **Uncoupled.** The orbit is the carrier's own; no pointer, gate or record.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-8,
UA-18, UO-16, UD-164, UD-173); `RecordLayer/DiracReturn.lean` (#270: `chainParity`,
`chainParity_ringPacket`, `chainInner_packet_packet`, `regionWeight_pair_le`,
`le_regionWeight_pair`, `chainInner_pair`, `wallState`); `RecordLayer/DiracArrival.lean`
(#265: `regionWeight`, `chainProp_packet`, `regionWeight_ringPacket_le`);
`RecordLayer/UnifiedArrivalRecord.lean` (`regionProj`, `arenaObs_regionProj_free_chainRay`);
`CV/DiracPacketLimit.lean` (`ringPacket`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

section Odd

variable {L : ℕ} [NeZero L]

/-- **The reflected window**: the momenta of `W` with the opposite sign. -/
def negWin (W : Finset ℤ) : Finset ℤ := W.image fun m => -m

theorem mem_negWin (W : Finset ℤ) (m : ℤ) : m ∈ negWin W ↔ -m ∈ W := by
  simp only [negWin, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [neg_neg]
  · intro h
    exact ⟨-m, h, neg_neg m⟩

/-- **The mirror packet** of a ring packet: the reflected window with the reflected
amplitudes. -/
def mirrorPacket (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) c μ ℓ (negWin W) (fun m => β (-m)) t

/-- The mirror of a ring packet is its mirror packet. -/
theorem chainParity_ringPacket_negWin (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    chainParity (ringPacket (L := L) c μ ℓ W β t) = mirrorPacket c μ ℓ W β t :=
  chainParity_ringPacket c μ ℓ (mem_negWin W) β t

theorem chainParity_mirrorPacket (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    chainParity (mirrorPacket (L := L) c μ ℓ W β t) = ringPacket c μ ℓ W β t := by
  rw [← chainParity_ringPacket_negWin, chainParity_chainParity]

omit [NeZero L] in
theorem chainParity_neg (φ : ZMod L × Fin 2 → ℂ) : chainParity (-φ) = -chainParity φ := by
  funext p
  simp only [chainParity, Pi.neg_apply]
  ring

/-- **The wall state of a packet**: the packet minus its mirror packet, over `√2`. -/
def oddWall (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
    • (ringPacket (L := L) c μ ℓ W β t + -mirrorPacket (L := L) c μ ℓ W β t)

/-- ★★ **The wall state is mirror-odd at every packet time.** -/
theorem chainParity_oddWall (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    chainParity (oddWall (L := L) c μ ℓ W β t) = -oddWall c μ ℓ W β t := by
  rw [oddWall, chainParity_smul, chainParity_add, chainParity_neg,
    chainParity_ringPacket_negWin, chainParity_mirrorPacket, ← smul_neg]
  congr 1
  rw [neg_add, neg_neg, add_comm]

omit [NeZero L] in
/-- ★ **A mirror-odd state has no upper component at a site that is its own mirror image.**
On the ring those are the site `0` and, for an even number of sites, the opposite site: the
two walls of UA-18 (a). -/
theorem odd_apply_eq_zero {φ : ZMod L × Fin 2 → ℂ} (h : chainParity φ = -φ) {k : ZMod L}
    (hk : -k = k) : φ (k, 0) = 0 := by
  have h1 := congrFun h (k, 0)
  simp only [chainParity, hk, Pi.neg_apply, ite_true, one_mul] at h1
  exact self_eq_neg.mp h1

theorem oddWall_apply_eq_zero (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) {k : ZMod L}
    (hk : -k = k) : oddWall (L := L) c μ ℓ W β t (k, 0) = 0 :=
  odd_apply_eq_zero (chainParity_oddWall c μ ℓ W β t) hk

/-- ★ **The ring's evolution carries the wall state to itself at the later time.** -/
theorem chainProp_oddWall (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (s : ℝ) :
    chainProp (L := L) (scaledHop c (ℓ / L)) μ s *ᵥ oddWall c μ ℓ W β 0
      = oddWall c μ ℓ W β s := by
  rw [oddWall, oddWall, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_neg,
    mirrorPacket, mirrorPacket, ringPacket, ringPacket, ringPacket, ringPacket,
    chainProp_packet, chainProp_packet]

omit [NeZero L] in
theorem regionWeight_neg (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight (-ψ) A = regionWeight ψ A := by
  simp only [regionWeight, siteWeight, Pi.neg_apply, norm_neg]

theorem chainInner_neg_right (u v : ZMod L × Fin 2 → ℂ) :
    chainInner u (-v) = -chainInner u v := by
  simp only [chainInner, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem chainInner_neg_neg (v : ZMod L × Fin 2 → ℂ) :
    chainInner (-v) (-v) = chainInner v v := by
  simp only [chainInner, Pi.neg_apply, star_neg, neg_mul_neg]

/-- **A packet and its mirror packet are orthogonal** when no momentum of the window is the
opposite of another modulo the ring. -/
theorem chainInner_ringPacket_mirrorPacket (c μ ℓ : ℝ) {W : Finset ℤ}
    (h : ∀ m ∈ W, ∀ m' ∈ W, (m : ZMod L) ≠ ((-m' : ℤ) : ZMod L)) (β : ℤ → ℂ) (t : ℝ) :
    chainInner (ringPacket (L := L) c μ ℓ W β t) (mirrorPacket c μ ℓ W β t) = 0 := by
  rw [mirrorPacket, ringPacket, ringPacket]
  refine chainInner_packet_packet _ _ (fun m hm m' hm' => ?_) _ _ t
  have h1 := h m hm (-m') ((mem_negWin W m').1 hm')
  rwa [neg_neg] at h1

variable {c μ ℓ : ℝ} {W : Finset ℤ} {β : ℤ → ℂ} {t : ℝ}

/-- The wall state of an orthogonal, normalised pair is normalised. -/
theorem chainInner_oddWall
    (hRM : chainInner (ringPacket (L := L) c μ ℓ W β t) (mirrorPacket c μ ℓ W β t) = 0)
    (hR1 : chainInner (ringPacket (L := L) c μ ℓ W β t) (ringPacket c μ ℓ W β t) = 1)
    (hM1 : chainInner (mirrorPacket (L := L) c μ ℓ W β t) (mirrorPacket c μ ℓ W β t) = 1) :
    chainInner (oddWall (L := L) c μ ℓ W β t) (oddWall c μ ℓ W β t) = 1 := by
  rw [oddWall]
  exact chainInner_pair (by rw [chainInner_neg_right, hRM, neg_zero]) hR1
    (by rw [chainInner_neg_neg]; exact hM1)

/-- ★★ **Where neither the packet nor its mirror packet is, the wall state is not.** -/
theorem regionWeight_oddWall_le (A : Finset (ZMod L)) {τ : ℝ} (hτ : 0 ≤ τ)
    (hR : regionWeight (ringPacket (L := L) c μ ℓ W β t) A ≤ τ)
    (hM : regionWeight (mirrorPacket (L := L) c μ ℓ W β t) A ≤ τ) :
    regionWeight (oddWall (L := L) c μ ℓ W β t) A ≤ 2 * τ := by
  rw [oddWall]
  exact regionWeight_pair_le A hτ hR (by rw [regionWeight_neg]; exact hM)

/-- ★★ **Where both the packet and its mirror packet are, the wall state is.** -/
theorem le_regionWeight_oddWall
    (hRM : chainInner (ringPacket (L := L) c μ ℓ W β t) (mirrorPacket c μ ℓ W β t) = 0)
    (hR1 : chainInner (ringPacket (L := L) c μ ℓ W β t) (ringPacket c μ ℓ W β t) = 1)
    (hM1 : chainInner (mirrorPacket (L := L) c μ ℓ W β t) (mirrorPacket c μ ℓ W β t) = 1)
    (A : Finset (ZMod L)) {τ : ℝ} (hτ : 0 ≤ τ)
    (hR : regionWeight (ringPacket (L := L) c μ ℓ W β t) Aᶜ ≤ τ)
    (hM : regionWeight (mirrorPacket (L := L) c μ ℓ W β t) Aᶜ ≤ τ) :
    1 - 2 * τ ≤ regionWeight (oddWall (L := L) c μ ℓ W β t) A := by
  rw [oddWall]
  exact le_regionWeight_pair (by rw [chainInner_neg_right, hRM, neg_zero]) hR1
    (by rw [chainInner_neg_neg]; exact hM1) A hτ hR (by rw [regionWeight_neg]; exact hM)

theorem ne_zero_of_chainInner_eq_one {ψ : ZMod L × Fin 2 → ℂ} (h : chainInner ψ ψ = 1) :
    ψ ≠ 0 := by
  rintro rfl
  simp [chainInner] at h

end Odd

/-! ### On the arena -/

section Arena

variable {M : ℕ}

/-- ★★★ **The wall state on the arena.** Along the uncoupled orbit of the ray of a normalised
wall state, the expectation of the projector of a region of sites at the flow time `s` is the
weight of the wall state at the packet time `s` on that region. -/
theorem arenaObs_regionProj_oddWall (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ)
    (hnorm : chainInner (oddWall (L := M + 1) c μ ℓ W β 0) (oddWall c μ ℓ W β 0) = 1)
    (A : Finset (ZMod (M + 1))) (s : ℝ) :
    arenaObs (regionProj A)
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (scaledHop c (ℓ / (M + 1 : ℕ))) μ) s)
          (chainRay (oddWall (L := M + 1) c μ ℓ W β 0) (ne_zero_of_chainInner_eq_one hnorm)))
      = regionWeight (oddWall (L := M + 1) c μ ℓ W β s) A := by
  rw [arenaObs_regionProj_free_chainRay, chainProp_oddWall, hnorm, Complex.one_re, div_one]

end Arena

end CSD.RecordLayer

end
