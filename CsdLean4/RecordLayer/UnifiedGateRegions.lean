/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGatedReading
public import CsdLean4.RecordLayer.UnifiedClockPacketLocalised

/-!
# The gate opens and closes: a messenger packet and a clock packet on one ring

**Category:** 7-SigmaLayer (the record layer). BACKLOG #395 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, fifth brick: Remainder (a) of #394, the carriers with regions exhibited. No new
assumption beyond UA-18.

#394 (`coincFlow_gated_reading`) reads a gated pointer under two hypotheses on where the two
carriers are: weight at most `ε` outside the relation while the gate is open, and at most `ε`
inside it while the gate is closed. This module proves both, with `ε` explicit, for a messenger
packet and a clock packet on one ring and the relation "within the angle `w`".

* `cos_add_le_cos_add` — the triangle inequality of the circle, in cosines;
* `ringNear` (two sites within the angle `w`), `ringArc` (the sites within `δ` of an angle),
  `mem_ringArc`; ★ `ringNear_of_mem_ringArc`, ★ `not_ringNear_of_mem_ringArc` — two arcs of
  half-angle `δ` whose centres are within `w − 2δ` hold only related pairs; if the centres are more than
  `w + 2δ` apart they hold no related pair;
* `one_sub_sum_arenaObs_siteSel`, `sum_arenaObs_siteSel_free_chainRay`,
  `arenaObs_siteSel_device`, `sum_arenaObs_siteSel_device_mk`,
  `sum_arenaObs_siteSel_free_deviceRay` — the occupancies of #394 along the uncoupled orbits
  are the region weights of #265 and #392;
* ★★ `ringGate_not_le`, ★★ `ringGate_le` — for any messenger ray and any clock ray: the weight
  outside (inside) the relation is at most the messenger's weight outside its arc plus the
  clock's weight outside its two arcs, when the arcs are near (apart);
* `ringPacket_ne_zero`, ★★ `one_sub_sum_arenaObs_ringArc_ringPacket_le`,
  ★★ `one_sub_sum_arenaObs_ringArc_devicePacket_le` — along the uncoupled orbit, a messenger
  packet's weight outside the arc about its predicted angle, times `1 − cos δ`, is at most
  #265's budget; a clock packet's weight outside the two arcs about its two levels' predicted
  angles is at most the mean of the two levels' budgets;
* `flatBudget`, `flat_packet_budget_time`, `flat_outside_arcs_le`, ★★★ `flat_gate_open`,
  ★★★ `flat_gate_closed` — for the flat clock packet of #392 and a flat
  messenger packet of rest energy `μ ≥ 1` on the same ring and window, at every flow time
  `s`: (weight outside the relation) `· (1 − cos δ)` is at most the sum of the two packets'
  budgets `flatBudget` at their packet times while the messenger's predicted angle is within
  `w − 2δ` of both levels' predicted angles, and the same bound holds for the weight inside
  the relation while it is more than `w + 2δ` from both. `flatBudget n N t` is
  `1/N + 1/(4 (1200 n N)²) + |t|/(360000 n² N)` (`flat_packet_budget_time`).

## Exact scope

* **Two hypotheses of #394 out of three.** `flat_gate_open` and `flat_gate_closed` are the
  hypotheses `hopen` and `hclosed` of `coincFlow_gated_reading` with `ε` the sum of the two
  budgets over `1 − cos δ`. The third hypothesis, the clock's swing with
  a margin, and the size conditions that tie `ε` to the number of ticks are not discharged
  here, and `coincFlow_gated_reading` is not applied. No reading is stated in this module.
* **Weights, not records.** Every statement bounds an expectation of a diagonal projector
  along the two carriers' uncoupled orbits. That is where the carriers are on the fibres where
  both profiles vanish and from a product start (#393), a null set of each.
* **Predicted angles, not times.** The conditions are on the predicted angles at one flow
  time. No flow time `t_a` or `t_b` is exhibited at which they hold, and the length of the
  interval between "open" and "closed" is not bounded here. By a calculation, not in Lean,
  that interval is `4δ` divided by the difference of the angular velocities.
* **The flat messenger is slow.** It has the clock's window of momenta about `1/2` and a rest
  energy `μ ≥ 1`, so its velocity `vRel 1 μ (1/2)` is at most the clock's; for `μ = 1` it
  does not separate from the clock's lower level. It is an exhibited pair for the gate, not
  the messenger of M6, whose speed must be within a stated error of `1`. The general lemmas
  (`one_sub_sum_arenaObs_ringArc_ringPacket_le`, `ringGate_not_le`, `ringGate_le`) take any
  ring packet with its own window, speed and rest energy.
* **The resolution is coarse**, as #392: the bound says something only when `1 − cos δ`
  exceeds the budget, so `δ` is large against `1/√N`.
* **A ring, two carriers.** UA-18 has a chain with walls and three carriers.
* **The relation is angular distance on the ring** (`cos` of the difference of the sites'
  angles at least `cos w`), for `0 ≤ w ≤ π`. It is symmetric and is a coincidence relation in
  the sense of UA-18 (c).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UD-143, UD-147, UD-148, UD-149, UD-150); `RecordLayer/UnifiedGatedReading.lean` (#394:
`coincFlow_gated_reading`, `arenaObs_coincProj_prodRay_le_of_disjoint`, `arenaObs_siteSel`,
`sum_arenaObs_siteSel`); `RecordLayer/UnifiedClockPacketLocalised.lean` (#392:
`deviceRegionWeight`, `deviceRegionWeight_devicePacket_le`, `flat_packet_start_le`,
`flat_packet_limitErr_le`, `flatWindow`, `flatAmpN`); `RecordLayer/DiracArrival.lean` (#265:
`regionWeight`,
`regionWeight_ringPacket_le`); `RecordLayer/UnifiedArrivalRecord.lean`
(`arenaObs_regionProj_free_chainRay`); `RecordLayer/UnifiedCoincidence.lean` (#390:
`coincProj`, `siteSel`); `RecordLayer/UnifiedDiracClock.lean` (`deviceRay`,
`idxFreeU_deviceHam_val`); `CV/DiracPacketLimit.lean` (#261: `dirac_packet_limit`,
`limitErr`, `ringPacket`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### Angles on the ring -/

/-- **The triangle inequality of the circle, in cosines.** If `θ` is within the angle `a` of
`0` and `φ` within `b`, then `θ + φ` is within `a + b`. -/
theorem cos_add_le_cos_add {θ φ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ Real.pi)
    (h1 : Real.cos a ≤ Real.cos θ) (h2 : Real.cos b ≤ Real.cos φ) :
    Real.cos (a + b) ≤ Real.cos (θ + φ) := by
  have haπ : a ≤ Real.pi := by linarith
  have hbπ : b ≤ Real.pi := by linarith
  have hα0 : 0 ≤ Real.arccos (Real.cos θ) := Real.arccos_nonneg _
  have hβ0 : 0 ≤ Real.arccos (Real.cos φ) := Real.arccos_nonneg _
  have hαa : Real.arccos (Real.cos θ) ≤ a := by
    have h := Real.arccos_le_arccos h1
    rwa [Real.arccos_cos ha haπ] at h
  have hβb : Real.arccos (Real.cos φ) ≤ b := by
    have h := Real.arccos_le_arccos h2
    rwa [Real.arccos_cos hb hbπ] at h
  have hcα : Real.cos (Real.arccos (Real.cos θ)) = Real.cos θ :=
    Real.cos_arccos (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
  have hcβ : Real.cos (Real.arccos (Real.cos φ)) = Real.cos φ :=
    Real.cos_arccos (Real.neg_one_le_cos φ) (Real.cos_le_one φ)
  have hsα : Real.sin (Real.arccos (Real.cos θ)) = |Real.sin θ| := by
    rw [Real.sin_arccos, Real.abs_sin_eq_sqrt_one_sub_cos_sq]
  have hsβ : Real.sin (Real.arccos (Real.cos φ)) = |Real.sin φ| := by
    rw [Real.sin_arccos, Real.abs_sin_eq_sqrt_one_sub_cos_sq]
  have hmono : Real.cos (a + b)
      ≤ Real.cos (Real.arccos (Real.cos θ) + Real.arccos (Real.cos φ)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hab (by linarith)
  have hprod : Real.sin θ * Real.sin φ ≤ |Real.sin θ| * |Real.sin φ| := by
    rw [← abs_mul]
    exact le_abs_self _
  have e := Real.cos_add θ φ
  rw [Real.cos_add (Real.arccos (Real.cos θ)), hcα, hcβ, hsα, hsβ] at hmono
  linarith

section Ring

variable (L : ℕ)

/-- **Two sites within the angle `w` of each other** on the ring of `L` sites: the cosine of
the difference of their angles is at least `cos w`. -/
def ringNear (w : ℝ) (k k' : ZMod L) : Prop :=
  Real.cos w ≤ Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi * k'.val / L)

noncomputable instance ringNear.instDecidableRel (w : ℝ) : DecidableRel (ringNear L w) :=
  fun _ _ => Classical.propDecidable _

variable [NeZero L]

/-- **The arc of half-angle `δ` about the angle `x`**: the sites whose angle has cosine
distance from `x` above `cos δ`. -/
noncomputable def ringArc (x δ : ℝ) : Finset (ZMod L) :=
  Finset.univ.filter fun k => Real.cos δ < Real.cos (2 * Real.pi * k.val / L - x)

variable {L}

theorem mem_ringArc {x δ : ℝ} {k : ZMod L} :
    k ∈ ringArc L x δ ↔ Real.cos δ < Real.cos (2 * Real.pi * k.val / L - x) := by
  rw [ringArc, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ k, h⟩⟩

/-- ★ **Near arcs hold only related pairs.** If the centres of two arcs of half-angle `δ` are
within the angle `w − 2δ` of each other, every site of the first is within `w` of every site
of the second. -/
theorem ringNear_of_mem_ringArc {w δ x y : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w)
    (hwπ : w ≤ Real.pi) (hxy : Real.cos (w - 2 * δ) ≤ Real.cos (x - y)) {k k' : ZMod L}
    (hk : k ∈ ringArc L x δ) (hk' : k' ∈ ringArc L y δ) : ringNear L w k k' := by
  rw [mem_ringArc] at hk hk'
  have hk'' : Real.cos δ ≤ Real.cos (y - 2 * Real.pi * k'.val / L) := by
    rw [← Real.cos_neg (y - 2 * Real.pi * k'.val / L), neg_sub]
    exact hk'.le
  have h1 := cos_add_le_cos_add hδ (by linarith) (by linarith) hk.le hxy
  have h2 := cos_add_le_cos_add (by linarith) hδ (by linarith) h1 hk''
  calc Real.cos w = Real.cos (δ + (w - 2 * δ) + δ) := by
        congr 1
        ring
    _ ≤ Real.cos (2 * Real.pi * k.val / L - x + (x - y) + (y - 2 * Real.pi * k'.val / L)) := h2
    _ = Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi * k'.val / L) := by
        congr 1
        ring

/-- ★ **Apart arcs hold no related pair.** If the centres of two arcs of half-angle `δ` are
more than the angle `w + 2δ` apart, no site of the first is within `w` of a site of the
second. -/
theorem not_ringNear_of_mem_ringArc {w δ x y : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) (hxy : Real.cos (x - y) < Real.cos (w + 2 * δ))
    {k k' : ZMod L} (hk : k ∈ ringArc L x δ) (hk' : k' ∈ ringArc L y δ) :
    ¬ ringNear L w k k' := by
  intro hn
  rw [mem_ringArc] at hk hk'
  have hkx : Real.cos δ ≤ Real.cos (x - 2 * Real.pi * k.val / L) := by
    rw [← Real.cos_neg (x - 2 * Real.pi * k.val / L), neg_sub]
    exact hk.le
  have h1 := cos_add_le_cos_add hδ hw (by linarith) hkx hn
  have h2 := cos_add_le_cos_add (by linarith) hδ (by linarith) h1 hk'.le
  have h3 : Real.cos (w + 2 * δ) ≤ Real.cos (x - y) :=
    calc Real.cos (w + 2 * δ) = Real.cos (δ + w + δ) := by
          congr 1
          ring
      _ ≤ Real.cos (x - 2 * Real.pi * k.val / L
            + (2 * Real.pi * k.val / L - 2 * Real.pi * k'.val / L)
            + (2 * Real.pi * k'.val / L - y)) := h2
      _ = Real.cos (x - y) := by
          congr 1
          ring
  linarith

end Ring

/-! ### Occupancies along the uncoupled orbits are region weights -/

section Weights

/-- The weight outside a set of sites is the sum of the occupancies of the other sites. -/
theorem one_sub_sum_arenaObs_siteSel {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]
    [DecidableEq S] (σ : ι → S) (I : Finset S) (p : GenArena ι) :
    1 - ∑ s ∈ I, arenaObs (siteSel σ s) p = ∑ s ∈ Iᶜ, arenaObs (siteSel σ s) p := by
  have h := sum_arenaObs_siteSel σ p
  rw [← Finset.sum_add_sum_compl I] at h
  linarith

variable {M : ℕ}

/-- **The messenger's occupancy of a region along its uncoupled orbit** is the region weight
of the evolved chain state over the norm. -/
theorem sum_arenaObs_siteSel_free_chainRay (J μ : ℝ) (A : Finset (ZMod (M + 1)))
    {ψ : ZMod (M + 1) × Fin 2 → ℂ} (hψ : ψ ≠ 0) (s : ℝ) :
    ∑ k ∈ A, arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s) (chainRay ψ hψ))
      = regionWeight (chainProp J μ s *ᵥ ψ) A / (chainInner ψ ψ).re := by
  rw [← arenaObs_regionProj_free_chainRay, arenaObs_regionProj]
  rfl

/-- The clock carrier's occupancy of a site: both components and both levels. -/
theorem arenaObs_siteSel_device (k : ZMod (M + 1))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) p
      = ∑ c : Fin 2, ∑ l : Fin 2, momentMap p ((k, c), l) := by
  rw [arenaObs_siteSel, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_eq_single k (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ k) h)]
  simp

/-- At the ray of `v` the clock carrier's occupancy of a region is the device weight of `v`
on the region over its squared norm. -/
theorem sum_arenaObs_siteSel_device_mk (A : Finset (ZMod (M + 1)))
    {v : EuclideanSpace ℂ ((ZMod (M + 1) × Fin 2) × Fin 2)} (hv : v ≠ 0) :
    ∑ k ∈ A, arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
        (Projectivization.mk ℂ v hv)
      = deviceRegionWeight v A / ‖v‖ ^ 2 := by
  rw [deviceRegionWeight, regionWeight, regionWeight, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [arenaObs_siteSel_device]
  simp only [momentMap_mk, siteWeight, Fin.sum_univ_two]
  ring

/-- **The clock carrier's occupancy of a region along its uncoupled orbit** is the device
weight of the evolved amplitude over the norm. -/
theorem sum_arenaObs_siteSel_free_deviceRay (J μ₀ μ₁ : ℝ) (A : Finset (ZMod (M + 1)))
    {Ψ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ ≠ 0) (s : ℝ) :
    ∑ k ∈ A, arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
        (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s) (deviceRay Ψ hΨ))
      = deviceRegionWeight (deviceProp J μ₀ μ₁ s *ᵥ Ψ) A / (deviceNorm Ψ).re := by
  have hU : ((idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s).val)ᴴ
      * (idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s).val = 1 := by
    have hmem := (idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s).property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  rw [deviceRay, arenaKick_mk, sum_arenaObs_siteSel_device_mk,
    Matrix.norm_toEuclideanLin_of_isom hU, norm_sq_toLp_device]
  congr 2
  rw [← idxFreeU_deviceHam_val]
  rfl

end Weights

/-! ### The gate from arcs, for any two rays -/

section Gate

variable {M : ℕ}

/-- ★★ **Near arcs: little weight outside the relation.** For any messenger ray and any clock
ray on the ring: if the messenger's arc about `x` is within `w − 2δ` of the clock's two arcs
about `y₀` and `y₁`, the weight outside "within `w`" is at most the messenger's weight
outside its arc plus the clock's weight outside its two arcs. -/
theorem ringGate_not_le {w δ x y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w) (hwπ : w ≤ Real.pi)
    (h0 : Real.cos (w - 2 * δ) ≤ Real.cos (x - y₀))
    (h1 : Real.cos (w - 2 * δ) ≤ Real.cos (x - y₁))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        fun k k' => ¬ ringNear (M + 1) w k k') (prodRay p q)
      ≤ (1 - ∑ k ∈ ringArc (M + 1) x δ,
            arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k) p)
        + (1 - ∑ k ∈ ringArc (M + 1) y₀ δ ∪ ringArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  refine arenaObs_coincProj_prodRay_le_of_disjoint _ _ _ _ _ (fun k hk k' hk' hn => hn ?_) p q
  rcases Finset.mem_union.1 hk' with h | h
  · exact ringNear_of_mem_ringArc hδ hw hwπ h0 hk h
  · exact ringNear_of_mem_ringArc hδ hw hwπ h1 hk h

/-- ★★ **Apart arcs: little weight inside the relation.** For any messenger ray and any clock
ray on the ring: if the messenger's arc about `x` is more than `w + 2δ` from the clock's two
arcs about `y₀` and `y₁`, the weight inside "within `w`" is at most the messenger's weight
outside its arc plus the clock's weight outside its two arcs. -/
theorem ringGate_le {w δ x y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (h0 : Real.cos (x - y₀) < Real.cos (w + 2 * δ))
    (h1 : Real.cos (x - y₁) < Real.cos (w + 2 * δ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)) (prodRay p q)
      ≤ (1 - ∑ k ∈ ringArc (M + 1) x δ,
            arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k) p)
        + (1 - ∑ k ∈ ringArc (M + 1) y₀ δ ∪ ringArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  refine arenaObs_coincProj_prodRay_le_of_disjoint _ _ _ _ _ (fun k hk k' hk' => ?_) p q
  rcases Finset.mem_union.1 hk' with h | h
  · exact not_ringNear_of_mem_ringArc hδ hw hwπ h0 hk h
  · exact not_ringNear_of_mem_ringArc hδ hw hwπ h1 hk h

end Gate

/-! ### A messenger packet and a clock packet stay in their arcs -/

section Packets

variable {M : ℕ}

/-- A ring packet of `dirac_packet_limit` is not the zero vector, at any packet time. -/
theorem ringPacket_ne_zero {c μ ℓ P D p₀ : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t : ℝ) :
    ringPacket (L := M + 1) c μ ℓ W β t ≠ 0 := fun h0 => by
  have h1 := (dirac_packet_limit (L := M + 1) hc hμ hℓ hp₀ hD0 hWin hWD β hβ).1 t
  rw [h0] at h1
  simp [chainInner] at h1

/-- ★★ **A messenger packet stays in the arc about its predicted angle.** Along the uncoupled
orbit from the packet time `t₀`, at the flow time `s`: the weight outside the arc of
half-angle `δ` about the predicted angle `Ω (t₀ + s)`, `Ω = (2π/ℓ) v(p₀)`, times `1 − cos δ`,
is at most `1 − Re T(0) + |t₀ + s| · limitErr`. -/
theorem one_sub_sum_arenaObs_ringArc_ringPacket_le {c μ ℓ P D p₀ : ℝ} (hc : 0 < c)
    (hμ : 0 < μ) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₀ : ℝ)
    (hψ : ringPacket (L := M + 1) c μ ℓ W β t₀ ≠ 0) (δ s : ℝ) :
    (1 - ∑ k ∈ ringArc (M + 1) (2 * Real.pi / ℓ * vRel c μ (c * p₀) * (t₀ + s)) δ,
        arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
              (scaledHop c (ℓ / (M + 1 : ℕ))) μ) s) (chainRay _ hψ))) * (1 - Real.cos δ)
      ≤ 1 - (transPhase (ringPacket (L := M + 1) c μ ℓ W β 0)).re
        + |t₀ + s| * limitErr c μ ℓ D P (ℓ / (M + 1 : ℕ)) := by
  have hn := (dirac_packet_limit (L := M + 1) hc hμ hℓ hp₀ hD0 hWin hWD β hβ).1 t₀
  have hshift : chainProp (L := M + 1) (scaledHop c (ℓ / (M + 1 : ℕ))) μ s
        *ᵥ ringPacket c μ ℓ W β t₀ = ringPacket c μ ℓ W β (t₀ + s) := by
    rw [ringPacket, ringPacket, ← chainProp_packet _ _ _ _ t₀,
      ← chainProp_packet _ _ _ _ (t₀ + s), Matrix.mulVec_mulVec, chainProp_add]
  rw [one_sub_sum_arenaObs_siteSel, sum_arenaObs_siteSel_free_chainRay, hn, Complex.one_re,
    div_one, hshift]
  refine regionWeight_ringPacket_le (L := M + 1) hc hμ hℓ hp₀ hD0 hWin hWD β hβ (t₀ + s)
    (fun k hk => ?_)
  rw [Finset.mem_compl, mem_ringArc, not_lt] at hk
  exact hk

/-- ★★ **A clock packet stays in the two arcs about its levels' predicted angles.** Along the
uncoupled orbit from the packet time `t₁`, at the flow time `s`: the weight outside the union
of the arcs of half-angle `δ` about the two levels' predicted angles `Ω_i (t₁ + s)`, times
`1 − cos δ`, is at most the mean of the two levels' budgets. -/
theorem one_sub_sum_arenaObs_ringArc_devicePacket_le {c μ₀ μ₁ ℓ P D p₀ : ℝ} (hc : 0 < c)
    (h0 : 0 < μ₀) (h1 : 0 < μ₁) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ}
    {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁ W β t₁ ≠ 0)
    (δ s : ℝ) :
    (1 - ∑ k ∈ ringArc (M + 1) (2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) * (t₁ + s)) δ
            ∪ ringArc (M + 1) (2 * Real.pi / ℓ * vRel c μ₁ (c * p₀) * (t₁ + s)) δ,
        arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁) s) (deviceRay _ hΨ))) * (1 - Real.cos δ)
      ≤ ((1 - (transPhase (ringPacket (L := M + 1) c μ₀ ℓ W β 0)).re
            + |t₁ + s| * limitErr c μ₀ ℓ D P (ℓ / (M + 1 : ℕ)))
          + (1 - (transPhase (ringPacket (L := M + 1) c μ₁ ℓ W β 0)).re
            + |t₁ + s| * limitErr c μ₁ ℓ D P (ℓ / (M + 1 : ℕ)))) / 2 := by
  have hD := (noWrap_distinct_of_window (L := M + 1) hWin).2
  have hn : (deviceNorm (devicePacket (L := M + 1) (scaledHop c (ℓ / (M + 1 : ℕ))) μ₀ μ₁ W β
      t₁)).re = 1 := by
    rw [deviceNorm_devicePacket h0 h1 hD, hβ]
    simp
  rw [one_sub_sum_arenaObs_siteSel, sum_arenaObs_siteSel_free_deviceRay, hn, div_one,
    deviceProp_devicePacket_shift]
  refine deviceRegionWeight_devicePacket_le (L := M + 1) hc h0 h1 hℓ hp₀ hD0 hWin hWD β hβ
    (t₁ + s) (fun k hk => ?_) (fun k hk => ?_)
  · rw [Finset.mem_compl, Finset.mem_union, not_or, mem_ringArc, not_lt] at hk
    exact hk.1
  · rw [Finset.mem_compl, Finset.mem_union, not_or, mem_ringArc, mem_ringArc, not_lt,
      not_lt] at hk
    exact hk.2

end Packets

/-! ### An exhibited pair: the flat clock packet and a flat messenger on the same ring -/

section Flat

/-- **The flat packet's budget at the packet time `t`**:
`1/N + 1/(4 (1200 n N)²) + |t|/(360000 n² N)`. The first two terms are the start's
localisation, the third the drift of #392's error rate. -/
def flatBudget (n N : ℕ) (t : ℝ) : ℝ :=
  1 / N + 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) + |t| * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)))

variable {n N M : ℕ}

/-- **The flat packet's budget, at each packet time.** For a level of rest energy `1 ≤ μ`:
`1 − Re T(0) + |t| · limitErr ≤ flatBudget n N t`, at every packet time. -/
theorem flat_packet_budget_time (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {μ : ℝ} (hμ : 1 ≤ μ) (t : ℝ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
          (flatAmpN N) 0)).re
      + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ flatBudget n N t := by
  have hstart := flat_packet_start_le hn hN hM hμ
  have hrate := (flat_packet_limitErr_le hn hN hM hμ).2
  have hdrift := mul_le_mul_of_nonneg_left hrate (abs_nonneg t)
  rw [flatBudget]
  linarith

/-- **The flat pair stays in its arcs.** For the flat clock packet of #392 and a flat messenger
packet of rest energy `μ ≥ 1` on the same ring and window, at every flow time `s`: the
messenger's weight outside the arc about its predicted angle plus the clock's weight outside
the arcs about its two levels' predicted angles, times `1 − cos δ`, is at most the sum of the
two budgets at the packet times `t₀ + s` and `t₁ + s`. -/
theorem flat_outside_arcs_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ}
    (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ) (t₀ t₁ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N) (flatAmpN N)
      t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ) (flatWindow n N)
      (flatAmpN N) t₁ ≠ 0) (δ s : ℝ) :
    ((1 - ∑ k ∈ ringArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 / 2) * (t₀ + s)) δ,
          arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
            (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ)))
        + (1 - ∑ k ∈ ringArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2) * (t₁ + s)) δ
            ∪ ringArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2) * (t₁ + s)) δ,
          arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))))
        * (1 - Real.cos δ)
      ≤ flatBudget n N (t₀ + s) + flatBudget n N (t₁ + s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have hWD : ∀ m ∈ flatWindow n N,
      |2 * Real.pi * m / ringLen (1200 * n * N) - 1 / 2| ≤ 1 / (600 * n) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * n * N : ℕ) : ℝ) := by exact_mod_cast hK
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N)
        = (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) := by
      rw [ringLen]
      have := Real.pi_pos
      field_simp
    rw [e]
    exact flatWindow_width hn hN m hm
  have hP : |(1 / 2 : ℝ)| ≤ 1 / 2 := by rw [abs_of_pos (by norm_num)]
  have hD0 : (0 : ℝ) ≤ 1 / (600 * n) := by positivity
  have hm := one_sub_sum_arenaObs_ringArc_ringPacket_le (M := M) (c := 1) (μ := μ)
    (ℓ := ringLen (1200 * n * N)) (P := 1 / 2) (D := 1 / (600 * n)) (p₀ := 1 / 2) one_pos
    (by linarith) (ringLen_pos hK) hP hD0 (flatWindow_mem_range hn hM) hWD (flatAmpN N)
    (sum_norm_flatAmpN n hN) t₀ hψ δ s
  have hc := one_sub_sum_arenaObs_ringArc_devicePacket_le (M := M) (c := 1) (μ₀ := 1)
    (μ₁ := 1 + Δ) (ℓ := ringLen (1200 * n * N)) (P := 1 / 2) (D := 1 / (600 * n))
    (p₀ := 1 / 2) one_pos one_pos (by linarith) (ringLen_pos hK) hP hD0
    (flatWindow_mem_range hn hM) hWD (flatAmpN N) (sum_norm_flatAmpN n hN) t₁ hΨ δ s
  simp only [one_mul] at hm hc
  have bm := flat_packet_budget_time hn hN hM hμ (t₀ + s)
  have b0 := flat_packet_budget_time hn hN hM (μ := 1) le_rfl (t₁ + s)
  have b1 := flat_packet_budget_time hn hN hM (μ := 1 + Δ) (by linarith) (t₁ + s)
  unfold ringHop
  rw [add_mul]
  linarith

/-- ★★★ **The gate is open while the flat messenger is near the flat clock.** At a flow time
`s` at which the messenger's predicted angle is within `w − 2δ` of both levels' predicted
angles: (weight outside "within `w`") `· (1 − cos δ)` is at most the sum of the two budgets
`flatBudget` at the packet times. This is the hypothesis `hopen` of `coincFlow_gated_reading`
(#394) at that flow time. -/
theorem flat_gate_open (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ}
    (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ) (t₀ t₁ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N) (flatAmpN N)
      t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ) (flatWindow n N)
      (flatAmpN N) t₁ ≠ 0) {w δ s : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w) (hwπ : w ≤ Real.pi)
    (h0 : Real.cos (w - 2 * δ)
      ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 / 2) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2) * (t₁ + s)))
    (h1 : Real.cos (w - 2 * δ)
      ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 / 2) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2) * (t₁ + s))) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ ringNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
        * (1 - Real.cos δ)
      ≤ flatBudget n N (t₀ + s) + flatBudget n N (t₁ + s) :=
  (mul_le_mul_of_nonneg_right (ringGate_not_le hδ hw hwπ h0 h1 _ _)
    (sub_nonneg.2 (Real.cos_le_one δ))).trans
    (flat_outside_arcs_le hn hN hM hμ hΔ0 t₀ t₁ hψ hΨ δ s)

/-- ★★★ **The gate is closed while the flat messenger is away from the flat clock.** At a
flow time `s` at which the messenger's predicted angle is more than `w + 2δ` from both
levels' predicted angles: (weight inside "within `w`") `· (1 − cos δ)` is at most the sum of
the two budgets `flatBudget` at the packet times. This is the hypothesis `hclosed` of
`coincFlow_gated_reading` (#394) at that flow time. -/
theorem flat_gate_closed (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ}
    (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ) (t₀ t₁ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N) (flatAmpN N)
      t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ) (flatWindow n N)
      (flatAmpN N) t₁ ≠ 0) {w δ s : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi)
    (h0 : Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 / 2) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2) * (t₁ + s))
      < Real.cos (w + 2 * δ))
    (h1 : Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 / 2) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2) * (t₁ + s))
      < Real.cos (w + 2 * δ)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
        * (1 - Real.cos δ)
      ≤ flatBudget n N (t₀ + s) + flatBudget n N (t₁ + s) :=
  (mul_le_mul_of_nonneg_right (ringGate_le hδ hw hwπ h0 h1 _ _)
    (sub_nonneg.2 (Real.cos_le_one δ))).trans
    (flat_outside_arcs_le hn hN hM hμ hΔ0 t₀ t₁ hψ hΨ δ s)

end Flat

end CSD.RecordLayer

end
