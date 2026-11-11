/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ChainCone
public import CsdLean4.RecordLayer.UnifiedClockSiteRecords

/-!
# A propagation bound for the coupled generators of the two-pointer arenas

**Category:** 7-SigmaLayer (the record layer). BACKLOG #361 — the author's programme "From `Σ` to
physical spacetime", milestone M5, obligation UO-15. `RecordLayer/ChainCone.lean` bounds the
spread of the free lattice Dirac generator. The arenas of #359 carry a different generator: the
free one plus one static term for each pointer (`diracTwoH`, `clockSiteH`). This module proves
the bound for those generators, and reads off it how far a pointer's displacement can respond to
an intervention made somewhere else on the ring.

**The interaction topology, stated as two predicates.** A matrix `G` on an index type with a site
map `σ` *hops at most one site* (`HopsOne σ G`) when every nonzero entry joins indices whose sites
are equal or adjacent on the ring. A matrix is *supported on* a set `X` of sites
(`SiteSuppOn σ X A`) when every nonzero entry has both indices over `X`. The free generators hop
at most one site (`hopsOne_diracHam`, `hopsOne_deviceHam`; the device's site map is
`deviceSite`). The three coupled operators move
nothing between sites (`hopsOne_siteProj`, `hopsOne_levelSwap`, `hopsOne_deviceSiteProj`). So the
coupled generators hop at most one site at every pair of pointer angles (`hopsOne_diracTwoGen`,
`hopsOne_clockSiteGen`). This is the topology that UA-8 and UA-13 of
`specs/unified-record-spacetime-plan.md` assume, written as a property of the generator.

**The cone bound for a generator that hops one site.** One commutator with such a generator
grows a support by one site (`siteSuppOn_adOne`), so `j` commutators grow it by `j`
(`siteSuppOn_adIter`). For a skew-Hermitian generator `S` that hops one site, an observable `A`
on `X` and a matrix `B` on `Y`, with `d` steps of growth from `X` missing `Y`:

  `‖[A(t), B]‖ ≤ 2 (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖`,  `t ≥ 0`

(`norm_commutator_hopsOne_le`; `norm_commutator_hopsOne_idOffOn_le` for a `B` that is the
identity off `Y`). The proof is the one of `norm_commutator_chain_le`, with the first `d` Taylor
terms commuting by support and the remainder priced by `norm_flowRemainder_le_factorial`. The
bound holds for the coupled generators because it uses only that they hop one site, and the
norm in it is the coupled generator's norm.

**Two interventions** (UA-14). Both are changes of the initial point of the arena.

1. *A kick.* A unitary `W` that is the identity off a set `Y` of sites (`IdOffOn σ Y W`) is
   applied to the carrier's initial ray. The occupancy read at time `t` moves by at most
   `2 (2 ‖H‖ t)^d / d! · ‖D‖` (`abs_arenaObs_flow_kick_sub_le`). At `t = 0` it does not move at
   all (`arenaObs_kick_of_idOffOn`).
2. *The other pointer's conserved angle.* The first pointer's angle `φ` enters the carrier's
   generator as the static term `g₁ f(φ) P_j`. Changing `φ` to `φ'` changes the generator by a
   matrix supported on the site `j`. A mean-value estimate along the interpolant
   `r ↦ τ_r^S (τ_{t−r}^{S'} D)` (`norm_heisenbergFlow_sub_le_of_commutator_le`) with the cone
   bound gives `‖τ_t^S D − τ_t^{S'} D‖ ≤ 2 (2 ‖S'‖ t)^d / d! · ‖D‖ ‖S − S'‖ · t`
   (`norm_heisenbergFlow_sub_hopsOne_le`).

**The response of a pointer.** A pointer's displacement is a multiple of the time integral of an
occupancy, so both bounds integrate (`abs_displacement_kick_sub_le`,
`abs_displacement_flow_sub_le`). On the arena of two site pointers, with `T_d(t)` the tail
`(2 ‖H‖ t)^d / d!`:

* the second pointer's response to a kick is at most `4 |g₂| |h'(χ)| T_d(t) t`
  (`abs_diracTwoKickResponseSnd_le`), and the first pointer's likewise
  (`abs_diracTwoKickResponseFst_le`), with `d` steps of growth from that pointer's site missing
  the kick's set `Y`;
* the second pointer's response to the first pointer's angle is at most
  `4 |g₂| |h'(χ)| |g₁| |f(φ) − f(φ')| T_d(t) t²` (`abs_diracTwoAngleResponseSnd_le`), and the
  first pointer's response to the second's angle likewise (`abs_diracTwoAngleResponseFst_le`),
  with `d` steps of growth from that pointer's site missing the other pointer's site, and `H`
  taken at the changed angle.

Each response is the difference, on the circle, of the pointer's moving angle between two runs of
`diracTwoPointerFlow` from the two initial points (`diracTwoPointerFlow_kick_snd`,
`diracTwoPointerFlow_angle_snd`, and the two for the first pointer). The second of these
stands beside the cross-talk bound of #359 (`abs_diracTwoShiftSnd_sub_le`), which does not depend
on the distance between the sites.

**The clock-and-site arena.** The site pointer's response to a kick is bounded the same way
(`abs_clockSiteKickResponseSnd_le`, `clockSiteFlow_kick_snd`). A position write of #360 whose
three displacement values clear their thresholds by that bound is written in the kicked run too
(`isRecordWrite_clockSiteFlow_site_of_kick`). The clock's pointer has no such bound. Its coupled
operator is the level swap, which acts at every site: any set of sites that supports it contains
every site (`mem_of_siteSuppOn_levelSwap`). So neither the clock pointer's response to a kick nor
either pointer's response to the other's angle on this arena is bounded here by distance. The
bounds of #359 stay the only ones for them.

**Ring distance.** A site reached by `d` steps of growth from `X` is `y + i` for some `y ∈ X` and
an integer `|i| ≤ d` (`exists_int_of_mem_growIter`). So the cone hypothesis holds when the two
sets are more than `d` apart on the ring (`disjoint_growIter_of_forall_ne`,
`disjoint_growIter_singleton`).

## Exact scope

* **Suppressed, not excluded.** For `t > 0` every bound is a factorial tail. It is small when
  `2 ‖H‖ t` is small against `d`, and it is not zero unless a prefactor vanishes. Nothing here
  says a remote intervention has no effect at a positive time. The one exact statement is at
  `t = 0` (`arenaObs_kick_of_idOffOn`). This argument gives no exact cone for a lattice with a
  continuous flow parameter; that none exists is not proved here.
* **Upper bounds.** No response is shown to be attained, and no lower bound inside the cone is
  given. A response that is not zero, for a kick one site away, is in
  `RecordLayer/UnifiedCausalArrival.lean` (#362). The speed in the tail is `2 ‖H‖`, the norm of
  the whole generator with both couplings in it. It is not optimised and it is not the group
  velocity of the chain.
* **An intervention is a change of the initial point.** The kick and the change of angle are
  not terms of the joint energy and no flow on the arena performs them. Which interventions are
  allowed is assumed (UA-14).
* **No event order is built.** The bounds limit a response. They do not define a relation between
  two record events, and no relation built from a threshold on a bound would be an order without
  further argument. The relation `CausalPrecedes` of `CV/RecordCausalOrder.lean` stays induced by
  an assumed graph.
* **Records.** One statement here is about a record: the position write of #360 on the
  clock-and-site arena survives a remote kick within stated margins. No instance in which the
  margins hold is exhibited, and `d` is at most about half the ring. On the arena of two site
  pointers no record is read, so the statements there are about displacements.
* **The clock's coupled operator is not local.** See above. On the clock-and-site arena this
  argument gives no delay for a tick record's response to a kick anywhere on the ring. That it
  responds is not shown.
* **All times are flow times** (UA-7). The angles `φ`, `χ` are conserved, so each coupling is a
  constant along a run.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-4, UA-5, UA-7, UA-8, UA-12, UA-13, UA-14, UO-15, UD-77 onward);
`RecordLayer/ChainCone.lean` (`SiteSupp`, `IdOff`, `grow`, `growIter`,
`norm_commutator_chain_le`); `CV/LiebRobinson.lean`
(`heisenbergFlow`, `adOne`, `adIter`, `flowRemainder`, `norm_flowRemainder_le_factorial`,
`hasDerivAt_heisenbergFlow`); `CV/ArenaBridge.lean` (`arenaObs_kick_conj`, `arenaObs_sub_le`,
`arena_lightcone`); `RecordLayer/UnifiedTwoPointer.lean` (`diracTwoH`, `clockSiteH`,
`diracTwoPointerFlow_apply`, `clockSiteFlow_apply`, `abs_diracTwoShiftSnd_sub_le`);
`RecordLayer/UnifiedClockSiteRecords.lean` (`isRecordWrite_clockSiteFlow_site`);
`CV/RecordCausalOrder.lean` (`CausalPrecedes`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Supports and hops over a site map -/

section SiteMap

variable {L : ℕ} {n : Type*}

/-- **Supported on a set of sites, over a site map** `σ`: every nonzero entry has both indices
over `X`. `SiteSupp` of `RecordLayer/ChainCone.lean` is the case `σ = Prod.fst`. -/
def SiteSuppOn (σ : n → ZMod L) (X : Finset (ZMod L)) (A : Matrix n n ℂ) : Prop :=
  ∀ p q, A p q ≠ 0 → σ p ∈ X ∧ σ q ∈ X

/-- **Hops at most one site**: every nonzero entry joins indices whose sites are equal or
adjacent on the ring. This is the interaction topology of a generator, stated on its entries. -/
def HopsOne (σ : n → ZMod L) (G : Matrix n n ℂ) : Prop :=
  ∀ p q, G p q ≠ 0 → σ q = σ p + 1 ∨ σ q = σ p - 1 ∨ σ q = σ p

/-- **The identity off a set of sites**: `W` has the entries of the identity wherever an index
lies over a site outside `Y`. `IdOff` of `RecordLayer/ChainCone.lean` is the case
`σ = Prod.fst`. -/
def IdOffOn [DecidableEq n] (σ : n → ZMod L) (Y : Finset (ZMod L)) (W : Matrix n n ℂ) : Prop :=
  ∀ p q, (σ p ∉ Y ∨ σ q ∉ Y) → W p q = if p = q then 1 else 0

/-- On the Dirac chain's index the support predicate is the one of `ChainCone.lean`. -/
theorem siteSuppOn_fst_iff {X : Finset (ZMod L)}
    {A : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ} :
    SiteSuppOn Prod.fst X A ↔ SiteSupp X A :=
  Iff.rfl

/-- On the Dirac chain's index the identity-off predicate is the one of `ChainCone.lean`. -/
theorem idOffOn_fst_iff {Y : Finset (ZMod L)}
    {W : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ} :
    IdOffOn Prod.fst Y W ↔ IdOff Y W :=
  Iff.rfl

/-- A multiple of a matrix supported on `X` is supported on `X`. -/
theorem SiteSuppOn.smul {σ : n → ZMod L} {X : Finset (ZMod L)} {A : Matrix n n ℂ} (c : ℂ)
    (hA : SiteSuppOn σ X A) : SiteSuppOn σ X (c • A) := fun p q h =>
  hA p q fun h0 => h (by rw [Matrix.smul_apply, h0, smul_zero])

/-- A diagonal matrix is supported on any set of sites that holds its nonzero entries. -/
theorem siteSuppOn_diagonal [DecidableEq n] {σ : n → ZMod L} {X : Finset (ZMod L)}
    {v : n → ℂ} (hv : ∀ p, v p ≠ 0 → σ p ∈ X) : SiteSuppOn σ X (Matrix.diagonal v) :=
  fun p q h => by
    have hpq : p = q := by
      by_contra hne
      exact h (Matrix.diagonal_apply_ne v hne)
    subst hpq
    rw [Matrix.diagonal_apply_eq] at h
    exact ⟨hv p h, hv p h⟩

/-- A sum of two matrices that hop at most one site hops at most one site. -/
theorem HopsOne.add {σ : n → ZMod L} {G K : Matrix n n ℂ} (hG : HopsOne σ G)
    (hK : HopsOne σ K) : HopsOne σ (G + K) := fun p q h => by
  by_cases hg : G p q = 0
  · refine hK p q fun h0 => h ?_
    rw [Matrix.add_apply, hg, h0, add_zero]
  · exact hG p q hg

/-- A multiple of a matrix that hops at most one site hops at most one site. -/
theorem HopsOne.smul {σ : n → ZMod L} {G : Matrix n n ℂ} (c : ℂ) (hG : HopsOne σ G) :
    HopsOne σ (c • G) := fun p q h =>
  hG p q fun h0 => h (by rw [Matrix.smul_apply, h0, smul_zero])

/-- A matrix whose nonzero entries stay on one site hops at most one site. -/
theorem hopsOne_of_site_eq {σ : n → ZMod L} {G : Matrix n n ℂ}
    (h : ∀ p q, G p q ≠ 0 → σ q = σ p) : HopsOne σ G := fun p q hpq =>
  Or.inr (Or.inr (h p q hpq))

/-- A diagonal matrix hops no site. -/
theorem hopsOne_diagonal [DecidableEq n] (σ : n → ZMod L) (v : n → ℂ) :
    HopsOne σ (Matrix.diagonal v) :=
  hopsOne_of_site_eq fun p q h => by
    by_contra hne
    exact h (Matrix.diagonal_apply_ne v fun e => hne (by rw [e]))

/-- A matrix that is the identity off `Y`, less the identity, is supported on `Y`. -/
theorem IdOffOn.siteSuppOn_sub_one [DecidableEq n] {σ : n → ZMod L} {Y : Finset (ZMod L)}
    {W : Matrix n n ℂ} (hW : IdOffOn σ Y W) : SiteSuppOn σ Y (W - 1) := fun p q h => by
  by_contra hc
  apply h
  rw [Matrix.sub_apply, Matrix.one_apply, hW p q (not_and_or.1 hc), sub_self]

/-- A site one step from a site of `X`, in either direction or none, is in `grow X`. -/
theorem mem_grow_of_step {X : Finset (ZMod L)} {a b : ZMod L} (hb : b ∈ X)
    (h : (b = a + 1 ∨ b = a - 1 ∨ b = a) ∨ (a = b + 1 ∨ a = b - 1 ∨ a = b)) :
    a ∈ grow X := by
  simp only [grow, Finset.mem_union, Finset.mem_image]
  rcases h with h | h
  · rcases h with e | e | e
    · exact Or.inr ⟨b, hb, by rw [e]; ring⟩
    · exact Or.inl (Or.inr ⟨b, hb, by rw [e]; ring⟩)
    · exact Or.inl (Or.inl (by rw [← e]; exact hb))
  · rcases h with e | e | e
    · exact Or.inl (Or.inr ⟨b, hb, e.symm⟩)
    · exact Or.inr ⟨b, hb, e.symm⟩
    · exact Or.inl (Or.inl (by rw [e]; exact hb))

/-- **A site reached by `d` steps of growth** from `X` is `y + i` for a site `y` of `X` and an
integer `i` with `|i| ≤ d`. -/
theorem exists_int_of_mem_growIter {X : Finset (ZMod L)} {d : ℕ} {x : ZMod L}
    (hx : x ∈ growIter X d) : ∃ y ∈ X, ∃ i : ℤ, |i| ≤ d ∧ x = y + i := by
  induction d generalizing x with
  | zero => exact ⟨x, hx, 0, by simp, by simp⟩
  | succ d ih =>
    have hx' : x ∈ grow (growIter X d) := hx
    simp only [grow, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with (h | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
    · obtain ⟨y, hy, i, hi, e⟩ := ih h
      have hi' := abs_le.1 hi
      exact ⟨y, hy, i, abs_le.2 ⟨by push_cast; linarith [hi'.1], by push_cast; linarith [hi'.2]⟩,
        e⟩
    · obtain ⟨y, hy, i, hi, e⟩ := ih hz
      have hi' := abs_le.1 hi
      refine ⟨y, hy, i + 1,
        abs_le.2 ⟨by push_cast; linarith [hi'.1], by push_cast; linarith [hi'.2]⟩, ?_⟩
      rw [e]
      push_cast
      ring
    · obtain ⟨y, hy, i, hi, e⟩ := ih hz
      have hi' := abs_le.1 hi
      refine ⟨y, hy, i - 1,
        abs_le.2 ⟨by push_cast; linarith [hi'.1], by push_cast; linarith [hi'.2]⟩, ?_⟩
      rw [e]
      push_cast
      ring

/-- **Far apart on the ring, so outside the cone.** If no site of `Y` is `x + i` for a site `x`
of `X` and an integer `|i| ≤ d`, then `d` steps of growth from `X` miss `Y`. -/
theorem disjoint_growIter_of_forall_ne {X Y : Finset (ZMod L)} {d : ℕ}
    (h : ∀ x ∈ X, ∀ y ∈ Y, ∀ i : ℤ, |i| ≤ d → y ≠ x + i) : Disjoint (growIter X d) Y :=
  Finset.disjoint_left.2 fun z hz hzY => by
    obtain ⟨x, hx, i, hi, e⟩ := exists_int_of_mem_growIter hz
    exact h x hx z hzY i hi e

/-- Two sites more than `d` apart on the ring: `d` steps of growth from one miss the other. -/
theorem disjoint_growIter_singleton {x y : ZMod L} {d : ℕ}
    (h : ∀ i : ℤ, |i| ≤ d → y ≠ x + i) : Disjoint (growIter {x} d) {y} :=
  disjoint_growIter_of_forall_ne fun a ha b hb i hi => by
    rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb]
    exact h i hi

/-- **One commutator with a generator that hops one site grows the support by one site.** -/
theorem siteSuppOn_adOne [Fintype n] [DecidableEq n] {σ : n → ZMod L} {X : Finset (ZMod L)}
    {G A : Matrix n n ℂ} (hG : HopsOne σ G) (hA : SiteSuppOn σ X A) :
    SiteSuppOn σ (grow X) (adOne G A) := by
  intro p q hpq
  rw [adOne, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply] at hpq
  by_contra hcon
  have h1 : ∀ r, G p r * A r q = 0 := fun r => by
    by_contra h2
    obtain ⟨hG1, hA1⟩ := mul_ne_zero_iff.1 h2
    obtain ⟨hr, hq⟩ := hA r q hA1
    exact hcon ⟨mem_grow_of_step hr (Or.inl (hG p r hG1)), subset_grow X hq⟩
  have h2 : ∀ r, A p r * G r q = 0 := fun r => by
    by_contra h2
    obtain ⟨hA1, hG1⟩ := mul_ne_zero_iff.1 h2
    obtain ⟨hp, hr⟩ := hA p r hA1
    exact hcon ⟨subset_grow X hp, mem_grow_of_step hr (Or.inr (hG r q hG1))⟩
  apply hpq
  rw [Finset.sum_eq_zero fun r _ => h1 r, Finset.sum_eq_zero fun r _ => h2 r, sub_self]

/-- **`j` commutators grow the support by `j` sites.** -/
theorem siteSuppOn_adIter [Fintype n] [DecidableEq n] {σ : n → ZMod L} {X : Finset (ZMod L)}
    {G A : Matrix n n ℂ} (hG : HopsOne σ G) (hA : SiteSuppOn σ X A) (j : ℕ) :
    SiteSuppOn σ (growIter X j) (adIter G j A) := by
  induction j with
  | zero => exact hA
  | succ j ih => exact siteSuppOn_adOne hG ih

/-- Matrices supported on disjoint sets of sites multiply to zero. -/
theorem mul_eq_zero_of_siteSuppOn_disjoint [Fintype n] {σ : n → ZMod L}
    {X Y : Finset (ZMod L)} {A B : Matrix n n ℂ} (hXY : Disjoint X Y) (hA : SiteSuppOn σ X A)
    (hB : SiteSuppOn σ Y B) : A * B = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  exact Finset.disjoint_left.1 hXY (hA p r h1).2 (hB r q h2).1

/-- Matrices supported on disjoint sets of sites commute. -/
theorem commute_of_siteSuppOn_disjoint [Fintype n] {σ : n → ZMod L} {X Y : Finset (ZMod L)}
    {A B : Matrix n n ℂ} (hXY : Disjoint X Y) (hA : SiteSuppOn σ X A) (hB : SiteSuppOn σ Y B) :
    A * B = B * A := by
  rw [mul_eq_zero_of_siteSuppOn_disjoint hXY hA hB,
    mul_eq_zero_of_siteSuppOn_disjoint hXY.symm hB hA]

/-- A matrix supported on `X` commutes with a matrix that is the identity off a disjoint `Y`. -/
theorem commute_of_siteSuppOn_idOffOn [Fintype n] [DecidableEq n] {σ : n → ZMod L}
    {X Y : Finset (ZMod L)} {A W : Matrix n n ℂ} (hXY : Disjoint X Y) (hA : SiteSuppOn σ X A)
    (hW : IdOffOn σ Y W) : A * W = W * A := by
  have h := commute_of_siteSuppOn_disjoint hXY hA hW.siteSuppOn_sub_one
  rw [mul_sub, sub_mul, mul_one, one_mul] at h
  exact sub_left_inj.1 h

/-! ### The cone bound -/

/-- **The factorial bound from commuting Taylor terms.** If the first `d` iterated commutators
of `A` with a skew-Hermitian generator commute with `B`, the commutator of the evolved `A` with
`B` is the commutator of the Taylor remainder: `‖[A(t), B]‖ ≤ 2 (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖`. -/
theorem norm_commutator_heisenbergFlow_le_of_adIter_commute [Fintype n] [DecidableEq n]
    [Nonempty n] {S : Matrix n n ℂ} (hS : Sᴴ = -S) (A B : Matrix n n ℂ) (d : ℕ)
    (hcomm : ∀ j < d, adIter S j A * B = B * adIter S j A) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ := by
  have hsplit : heisenbergFlow S t A
      = (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) + flowRemainder S A d t := by
    rw [flowRemainder]
    abel
  have hsum : (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) * B
      = B * ∑ j ∈ Finset.range d, flowCoef t j • adIter S j A := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm j (Finset.mem_range.1 hj)]
  have hrem := norm_flowRemainder_le_factorial hS A d ht
  rw [hsplit, add_mul, mul_add, hsum, add_sub_add_left_eq_sub]
  calc ‖flowRemainder S A d t * B - B * flowRemainder S A d t‖
      ≤ ‖flowRemainder S A d t * B‖ + ‖B * flowRemainder S A d t‖ := norm_sub_le _ _
    _ ≤ ‖flowRemainder S A d t‖ * ‖B‖ + ‖B‖ * ‖flowRemainder S A d t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖flowRemainder S A d t‖ * ‖B‖ := by ring
    _ ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial * ‖A‖) * ‖B‖ := by gcongr
    _ = _ := by ring

/-- ★★ **The cone bound for a generator that hops one site.** For a skew-Hermitian `S` that
hops at most one site, `A` supported on `X`, `B` supported on `Y`, and `d` steps of growth from
`X` missing `Y`: `‖[A(t), B]‖ ≤ 2 (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖` for `t ≥ 0`. The generator may
carry any terms that move nothing between sites. A factorial tail, not an exclusion. -/
theorem norm_commutator_hopsOne_le [Fintype n] [DecidableEq n] [Nonempty n] {σ : n → ZMod L}
    {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsOne σ S) {X Y : Finset (ZMod L)}
    {A B : Matrix n n ℂ} (hA : SiteSuppOn σ X A) (hB : SiteSuppOn σ Y B) {d : ℕ}
    (hcone : Disjoint (growIter X d) Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ :=
  norm_commutator_heisenbergFlow_le_of_adIter_commute hS A B d
    (fun j hj => commute_of_siteSuppOn_disjoint
      (Finset.disjoint_of_subset_left (growIter_mono X hj.le) hcone)
      (siteSuppOn_adIter hhop hA j) hB) ht

/-- ★★ **The cone bound against a kick.** The same bound with `B` replaced by a matrix `W` that
is the identity off `Y`. -/
theorem norm_commutator_hopsOne_idOffOn_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsOne σ S)
    {X Y : Finset (ZMod L)} {A W : Matrix n n ℂ} (hA : SiteSuppOn σ X A)
    (hW : IdOffOn σ Y W) {d : ℕ} (hcone : Disjoint (growIter X d) Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * W - W * heisenbergFlow S t A‖
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖A‖ * ‖W‖ :=
  norm_commutator_heisenbergFlow_le_of_adIter_commute hS A W d
    (fun j hj => commute_of_siteSuppOn_idOffOn
      (Finset.disjoint_of_subset_left (growIter_mono X hj.le) hcone)
      (siteSuppOn_adIter hhop hA j) hW) ht

/-! ### The response to a change of the generator -/

/-- **A mean-value bound between two flows.** If the commutator of the `S'`-evolved `D` with
`S − S'` is at most `C` up to time `t`, the two evolutions of `D` differ by at most `C t`. The
interpolant is `r ↦ τ_r^S (τ_{t−r}^{S'} D)`; no integral is taken. -/
theorem norm_heisenbergFlow_sub_le_of_commutator_le [Fintype n] [DecidableEq n] [Nonempty n]
    {S S' : Matrix n n ℂ} (hS : Sᴴ = -S) (D : Matrix n n ℂ) {C t : ℝ} (ht : 0 ≤ t)
    (hC : ∀ u, 0 ≤ u → u ≤ t →
      ‖heisenbergFlow S' u D * (S - S') - (S - S') * heisenbergFlow S' u D‖ ≤ C) :
    ‖heisenbergFlow S t D - heisenbergFlow S' t D‖ ≤ C * t := by
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun u : ℝ => heisenbergFlow S u (heisenbergFlow S' (t - u) D))
        (heisenbergFlow S r (heisenbergFlow S' (t - r) D * (S - S')
          - (S - S') * heisenbergFlow S' (t - r) D)) r := by
    intro r
    have hneg : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) r := hasDerivAt_neg r
    have hL : HasDerivAt (fun u : ℝ => exp ((-u) • S)) ((-1 : ℝ) • (exp ((-r) • S) * S)) r :=
      (hasDerivAt_exp_smul_const S (-r)).scomp r hneg
    have hR : HasDerivAt (fun u : ℝ => exp (u • S)) (exp (r • S) * S) r :=
      hasDerivAt_exp_smul_const S r
    have hg : HasDerivAt (fun u : ℝ => t - u) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub t
    have hY : HasDerivAt (fun u : ℝ => heisenbergFlow S' (t - u) D)
        ((-1 : ℝ) • (heisenbergFlow S' (t - r) D * S' - S' * heisenbergFlow S' (t - r) D)) r :=
      (hasDerivAt_heisenbergFlow S' D (t - r)).scomp r hg
    have hprod := (hL.mul hY).mul hR
    have hcommR : exp (r • S) * S = S * exp (r • S) :=
      (((Commute.refl S).smul_left r).exp_left).eq
    have hD : ∀ E E' Y : Matrix n n ℂ, E' * S = S * E' →
        ((-1 : ℝ) • (E * S) * Y + E * ((-1 : ℝ) • (Y * S' - S' * Y))) * E' + E * Y * (E' * S)
          = E * (Y * (S - S') - (S - S') * Y) * E' := by
      intro E E' Y hc
      rw [neg_one_smul, neg_one_smul, hc]
      noncomm_ring
    exact hprod.congr_deriv (hD _ _ _ hcommR)
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ‖heisenbergFlow S r (heisenbergFlow S' (t - r) D * (S - S')
          - (S - S') * heisenbergFlow S' (t - r) D)‖ ≤ C := fun r hr =>
    (norm_heisenbergFlow_le hS r _).trans (hC (t - r) (sub_nonneg.2 hr.2) (sub_le_self t hr.1))
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => heisenbergFlow S u (heisenbergFlow S' (t - u) D))
    (f' := fun r => heisenbergFlow S r (heisenbergFlow S' (t - r) D * (S - S')
      - (S - S') * heisenbergFlow S' (t - r) D))
    (s := Set.Icc (0 : ℝ) t) (C := C)
    (fun r _ => (hderiv r).hasDerivWithinAt) hbound (convex_Icc 0 t)
    (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht)
  simp only [sub_self, sub_zero, heisenbergFlow_zero] at hmvt
  rwa [Real.norm_eq_abs, abs_of_nonneg ht] at hmvt

/-- ★★ **Two generators that differ away from an observable evolve it almost alike.** For
skew-Hermitian `S`, `S'` with `S'` hopping at most one site, `D` supported on `X`, `S − S'`
supported on `Y`, and `d` steps of growth from `X` missing `Y`:
`‖τ_t^S D − τ_t^{S'} D‖ ≤ 2 (2 ‖S'‖ t)^d / d! · ‖D‖ ‖S − S'‖ · t` for `t ≥ 0`. -/
theorem norm_heisenbergFlow_sub_hopsOne_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S S' : Matrix n n ℂ} (hS : Sᴴ = -S) (hS' : S'ᴴ = -S')
    (hhop : HopsOne σ S') {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    (hΔ : SiteSuppOn σ Y (S - S')) {d : ℕ} (hcone : Disjoint (growIter X d) Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖heisenbergFlow S t D - heisenbergFlow S' t D‖
      ≤ 2 * ((2 * ‖S'‖ * t) ^ d / d.factorial) * ‖D‖ * ‖S - S'‖ * t :=
  norm_heisenbergFlow_sub_le_of_commutator_le hS D ht fun u hu hut =>
    (norm_commutator_hopsOne_le hS' hhop hD hΔ hcone hu).trans (by gcongr)

/-! ### On the arena -/

/-- Conjugation by the propagator of a skew-Hermitian generator is its Heisenberg flow. -/
theorem star_exp_smul_mul_exp_smul [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    (hS : Sᴴ = -S) (t : ℝ) (A : Matrix n n ℂ) :
    star (exp (t • S)) * A * exp (t • S) = heisenbergFlow S t A := by
  rw [heisenbergFlow, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
    Matrix.conjTranspose_real_smul_skew hS t, neg_smul]

/-- ★ **Exact at equal time.** An observable supported on `X` is not changed by a kick that is
the identity off a disjoint `Y`. This is the one exact exclusion of this module: it is the
statement at flow time zero. -/
theorem arenaObs_kick_of_idOffOn [Fintype n] [DecidableEq n] {σ : n → ZMod L}
    {X Y : Finset (ZMod L)} (hXY : Disjoint X Y) {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    {W : Matrix.unitaryGroup n ℂ} (hW : IdOffOn σ Y W.val) (p : GenArena n) :
    arenaObs D (arenaKick W p) = arenaObs D p := by
  rw [arenaObs_kick_conj]
  have hcomm : D * W.val = W.val * D := commute_of_siteSuppOn_idOffOn hXY hD hW
  have hWW : star W.val * W.val = 1 := by
    have hmem := W.property
    rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hWW, Matrix.one_mul]

/-- ★★ **The response of an occupancy to a kick.** The carrier moves by `exp (t S)` with `S`
skew-Hermitian and hopping at most one site. A kick `W`, the identity off `Y`, is applied to the
initial ray. An observable `D` on `X`, read at time `t ≥ 0`, moves by at most
`2 (2 ‖S‖ t)^d / d! · ‖D‖` when `d` steps of growth from `X` miss `Y`. -/
theorem abs_arenaObs_flow_kick_sub_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsOne σ S)
    {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    {W : Matrix.unitaryGroup n ℂ} (hW : IdOffOn σ Y W.val) {d : ℕ}
    (hcone : Disjoint (growIter X d) Y) {t : ℝ} (ht : 0 ≤ t) {U : Matrix.unitaryGroup n ℂ}
    (hU : U.val = exp (t • S)) (p : GenArena n) :
    |arenaObs D (arenaKick U (arenaKick W p)) - arenaObs D (arenaKick U p)|
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖D‖ := by
  rw [arenaObs_kick_conj U D (arenaKick W p), arenaObs_kick_conj W _ p,
    arenaObs_kick_conj U D p, hU, star_exp_smul_mul_exp_smul hS t D]
  refine (arenaObs_sub_le _ _ p).trans ?_
  set Z := heisenbergFlow S t D with hZ
  have hWW : star W.val * W.val = 1 := by
    have hmem := W.property
    rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  have hdefect : star W.val * Z * W.val - Z = star W.val * (Z * W.val - W.val * Z) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have hWs : ‖star W.val‖ = 1 := by
    rw [norm_star]
    exact CStarRing.norm_of_mem_unitary W.property
  rw [hdefect]
  calc ‖star W.val * (Z * W.val - W.val * Z)‖
      ≤ ‖star W.val‖ * ‖Z * W.val - W.val * Z‖ := norm_mul_le _ _
    _ = ‖Z * W.val - W.val * Z‖ := by rw [hWs, one_mul]
    _ ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖D‖ * ‖W.val‖ :=
        norm_commutator_hopsOne_idOffOn_le hS hhop hD hW hcone ht
    _ = 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖D‖ := by
        rw [CStarRing.norm_of_mem_unitary W.property, mul_one]

/-- ★★ **The response of an occupancy to a change of the generator.** Two carriers move by
`exp (t S)` and `exp (t S')` from the same ray, with `S − S'` supported on `Y`. An observable `D`
on `X`, read at time `t ≥ 0`, differs between them by at most
`2 (2 ‖S'‖ t)^d / d! · ‖D‖ ‖S − S'‖ · t` when `d` steps of growth from `X` miss `Y`. -/
theorem abs_arenaObs_flow_sub_flow_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S S' : Matrix n n ℂ} (hS : Sᴴ = -S) (hS' : S'ᴴ = -S')
    (hhop : HopsOne σ S') {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    (hΔ : SiteSuppOn σ Y (S - S')) {d : ℕ} (hcone : Disjoint (growIter X d) Y) {t : ℝ}
    (ht : 0 ≤ t) {U U' : Matrix.unitaryGroup n ℂ} (hU : U.val = exp (t • S))
    (hU' : U'.val = exp (t • S')) (p : GenArena n) :
    |arenaObs D (arenaKick U p) - arenaObs D (arenaKick U' p)|
      ≤ 2 * ((2 * ‖S'‖ * t) ^ d / d.factorial) * ‖D‖ * ‖S - S'‖ * t := by
  rw [arenaObs_kick_conj U D p, arenaObs_kick_conj U' D p, hU, hU',
    star_exp_smul_mul_exp_smul hS t D, star_exp_smul_mul_exp_smul hS' t D]
  exact (arenaObs_sub_le _ _ p).trans
    (norm_heisenbergFlow_sub_hopsOne_le hS hS' hhop hD hΔ hcone ht)

/-- Two integrals over `[0, t]` whose integrands stay within `C` differ by at most `C t`. -/
theorem abs_integral_sub_integral_le_of_abs_sub_le {F G : ℝ → ℝ} (hF : Continuous F)
    (hG : Continuous G) {C t : ℝ} (ht : 0 ≤ t) (h : ∀ s, 0 ≤ s → s ≤ t → |F s - G s| ≤ C) :
    |(∫ s in (0 : ℝ)..t, F s) - ∫ s in (0 : ℝ)..t, G s| ≤ C * t := by
  rw [← intervalIntegral.integral_sub (hF.intervalIntegrable 0 t) (hG.intervalIntegrable 0 t)]
  have key : ‖∫ s in (0 : ℝ)..t, (F s - G s)‖ ≤ C * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      rw [Set.uIoc_of_le ht] at hs
      exact h s hs.1.le hs.2
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at key

/-- The size of the difference of two displacements `−2 g c ∫`. -/
theorem abs_neg_two_mul_mul_mul_sub (g c a b : ℝ) :
    |-(2 * g) * c * a - -(2 * g) * c * b| = 2 * |g| * |c| * |a - b| := by
  rw [← mul_sub, abs_mul, abs_mul, abs_neg, abs_mul, abs_two]

/-- ★ **The integrated response to a kick**: at most `2 (2 ‖S‖ t)^d / d! · ‖D‖ · t`. -/
theorem abs_integral_arenaObs_flow_kick_sub_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsOne σ S)
    {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    {W : Matrix.unitaryGroup n ℂ} (hW : IdOffOn σ Y W.val) {d : ℕ}
    (hcone : Disjoint (growIter X d) Y) {U : ℝ → Matrix.unitaryGroup n ℂ} (hUc : Continuous U)
    (hU : ∀ s, (U s).val = exp (s • S)) (p : GenArena n) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
        - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)|
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖D‖ * t :=
  abs_integral_sub_integral_le_of_abs_sub_le
    ((continuous_arenaObs D).comp (hUc.arenaKick continuous_const))
    ((continuous_arenaObs D).comp (hUc.arenaKick continuous_const)) ht fun s hs hst =>
      (abs_arenaObs_flow_kick_sub_le hS hhop hD hW hcone hs (hU s) p).trans (by gcongr)

/-- ★ **The integrated response to a change of the generator**: at most
`2 (2 ‖S'‖ t)^d / d! · ‖D‖ ‖S − S'‖ · t²`. -/
theorem abs_integral_arenaObs_flow_sub_flow_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S S' : Matrix n n ℂ} (hS : Sᴴ = -S) (hS' : S'ᴴ = -S')
    (hhop : HopsOne σ S') {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    (hΔ : SiteSuppOn σ Y (S - S')) {d : ℕ} (hcone : Disjoint (growIter X d) Y)
    {U U' : ℝ → Matrix.unitaryGroup n ℂ} (hUc : Continuous U) (hUc' : Continuous U')
    (hU : ∀ s, (U s).val = exp (s • S)) (hU' : ∀ s, (U' s).val = exp (s • S'))
    (p : GenArena n) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
        - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U' s) p)|
      ≤ 2 * ((2 * ‖S'‖ * t) ^ d / d.factorial) * ‖D‖ * ‖S - S'‖ * t * t :=
  abs_integral_sub_integral_le_of_abs_sub_le
    ((continuous_arenaObs D).comp (hUc.arenaKick continuous_const))
    ((continuous_arenaObs D).comp (hUc'.arenaKick continuous_const)) ht fun s hs hst =>
      (abs_arenaObs_flow_sub_flow_le hS hS' hhop hD hΔ hcone hs (hU s) (hU' s) p).trans
        (by gcongr)

/-- ★ **A displacement's response to a kick.** A displacement `−2 g c ∫₀ᵗ ⟨D⟩` with `‖D‖ ≤ 1`
moves by at most `4 |g| |c| (2 ‖S‖ t)^d / d! · t`. -/
theorem abs_displacement_kick_sub_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsOne σ S)
    {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D) (hDn : ‖D‖ ≤ 1)
    {W : Matrix.unitaryGroup n ℂ} (hW : IdOffOn σ Y W.val) {d : ℕ}
    (hcone : Disjoint (growIter X d) Y) {U : ℝ → Matrix.unitaryGroup n ℂ} (hUc : Continuous U)
    (hU : ∀ s, (U s).val = exp (s • S)) (g c : ℝ) (p : GenArena n) {t : ℝ} (ht : 0 ≤ t) :
    |-(2 * g) * c * (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
        - -(2 * g) * c * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)|
      ≤ 4 * |g| * |c| * ((2 * ‖S‖ * t) ^ d / d.factorial) * t := by
  rw [abs_neg_two_mul_mul_mul_sub]
  have key := abs_integral_arenaObs_flow_kick_sub_le hS hhop hD hW hcone hUc hU p ht
  have hT : 0 ≤ (2 * ‖S‖ * t) ^ d / (d.factorial : ℝ) :=
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) ht) _)
      (Nat.cast_nonneg _)
  generalize (2 * ‖S‖ * t) ^ d / (d.factorial : ℝ) = T at key hT ⊢
  have hTt : 0 ≤ 2 * T * t := mul_nonneg (mul_nonneg zero_le_two hT) ht
  have h1 : 2 * T * ‖D‖ * t ≤ 2 * T * t := by
    have := mul_le_mul_of_nonneg_left hDn hTt
    linarith
  calc 2 * |g| * |c| * |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
          - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)|
      ≤ 2 * |g| * |c| * (2 * T * t) :=
        mul_le_mul_of_nonneg_left (key.trans h1)
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg _)) (abs_nonneg _))
    _ = 4 * |g| * |c| * T * t := by ring

/-- ★ **A displacement's response to a change of the generator.** A displacement
`−2 g c ∫₀ᵗ ⟨D⟩` with `‖D‖ ≤ 1` differs between two generators with `‖S − S'‖ ≤ δ` by at most
`4 |g| |c| δ (2 ‖S'‖ t)^d / d! · t²`. -/
theorem abs_displacement_flow_sub_le [Fintype n] [DecidableEq n] [Nonempty n]
    {σ : n → ZMod L} {S S' : Matrix n n ℂ} (hS : Sᴴ = -S) (hS' : S'ᴴ = -S')
    (hhop : HopsOne σ S') {X Y : Finset (ZMod L)} {D : Matrix n n ℂ} (hD : SiteSuppOn σ X D)
    (hDn : ‖D‖ ≤ 1) (hΔ : SiteSuppOn σ Y (S - S')) {δ : ℝ} (hΔn : ‖S - S'‖ ≤ δ) {d : ℕ}
    (hcone : Disjoint (growIter X d) Y) {U U' : ℝ → Matrix.unitaryGroup n ℂ}
    (hUc : Continuous U) (hUc' : Continuous U') (hU : ∀ s, (U s).val = exp (s • S))
    (hU' : ∀ s, (U' s).val = exp (s • S')) (g c : ℝ) (p : GenArena n) {t : ℝ} (ht : 0 ≤ t) :
    |-(2 * g) * c * (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
        - -(2 * g) * c * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U' s) p)|
      ≤ 4 * |g| * |c| * δ * ((2 * ‖S'‖ * t) ^ d / d.factorial) * t ^ 2 := by
  rw [abs_neg_two_mul_mul_mul_sub]
  have key := abs_integral_arenaObs_flow_sub_flow_le hS hS' hhop hD hΔ hcone hUc hUc' hU hU' p ht
  have hT : 0 ≤ (2 * ‖S'‖ * t) ^ d / (d.factorial : ℝ) :=
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) ht) _)
      (Nat.cast_nonneg _)
  generalize (2 * ‖S'‖ * t) ^ d / (d.factorial : ℝ) = T at key hT ⊢
  have hTt : 0 ≤ 2 * T * t * t := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hT) ht) ht
  have hprod : ‖D‖ * ‖S - S'‖ ≤ 1 * δ :=
    mul_le_mul hDn hΔn (norm_nonneg _) zero_le_one
  have h1 : 2 * T * ‖D‖ * ‖S - S'‖ * t * t ≤ 2 * T * δ * t * t := by
    have := mul_le_mul_of_nonneg_left hprod hTt
    linarith
  calc 2 * |g| * |c| * |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
          - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U' s) p)|
      ≤ 2 * |g| * |c| * (2 * T * δ * t * t) :=
        mul_le_mul_of_nonneg_left (key.trans h1)
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg _)) (abs_nonneg _))
    _ = 4 * |g| * |c| * δ * T * t ^ 2 := by ring

/-- The generator `−i H` has the norm of `H`. -/
theorem norm_neg_I_smul [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) :
    ‖(-Complex.I) • H‖ = ‖H‖ := by
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]

end SiteMap

/-! ### The generators of the two arenas hop at most one site -/

section Generators

variable {L : ℕ}

/-- **The site of an index of the two-level device.** -/
def deviceSite (L : ℕ) : (ZMod L × Fin 2) × Fin 2 → ZMod L := fun x => x.1.1

/-- The lattice Dirac Hamiltonian hops at most one site. -/
theorem hopsOne_diracHam (J μ : ℝ) : HopsOne Prod.fst (diracHam (L := L) J μ) := fun p q h => by
  by_contra hc
  simp only [not_or] at hc
  exact h (diracHam_apply_eq_zero J μ ⟨hc.1, hc.2.1, hc.2.2⟩)

/-- A site projector moves nothing between sites. -/
theorem hopsOne_siteProj (j : ZMod L) : HopsOne Prod.fst (siteProj j) := by
  unfold siteProj
  exact hopsOne_diagonal _ _

/-- The site projector `P_j` is supported on the site `j`. -/
theorem siteSuppOn_siteProj (j : ZMod L) : SiteSuppOn Prod.fst {j} (siteProj j) := by
  unfold siteProj
  exact siteSuppOn_diagonal fun p hp => by
    by_contra hne
    have hpj : ¬ p.1 = j := fun e => hne (Finset.mem_singleton.2 e)
    simp [hpj] at hp

/-- The device's Hamiltonian hops at most one site: each level carries a Dirac chain. -/
theorem hopsOne_deviceHam (J μ₀ μ₁ : ℝ) :
    HopsOne (deviceSite L) (deviceHam (L := L) J μ₀ μ₁) := by
  rintro ⟨p, a⟩ ⟨q, b⟩ h
  unfold deviceHam at h
  rw [Matrix.blockDiagonal_apply] at h
  split_ifs at h with hab
  · exact hopsOne_diracHam J _ p q h
  · exact absurd rfl h

/-- The level swap moves nothing between sites. -/
theorem hopsOne_levelSwap : HopsOne (deviceSite L) (levelSwap (ZMod L × Fin 2)) :=
  hopsOne_of_site_eq fun x y h => by
    by_contra hne
    have hxy : ¬ (x.1 = y.1 ∧ x.2 ≠ y.2) := fun hc => hne (by show y.1.1 = x.1.1; rw [hc.1])
    exact h (by simp only [levelSwap, Matrix.of_apply, hxy, ite_false])

/-- ★ **The level swap is supported on no proper set of sites**: any set of sites that supports
it contains every site. The clock's coupled operator acts at every site of the ring. -/
theorem mem_of_siteSuppOn_levelSwap {X : Finset (ZMod L)}
    (h : SiteSuppOn (deviceSite L) X (levelSwap (ZMod L × Fin 2))) (x : ZMod L) : x ∈ X :=
  (h ((x, 0), 0) ((x, 0), 1) (by simp [levelSwap])).1

variable {M : ℕ}

/-- The device's site projector moves nothing between sites. -/
theorem hopsOne_deviceSiteProj (k : ZMod (M + 1)) :
    HopsOne (deviceSite (M + 1)) (deviceSiteProj k) := by
  rw [deviceSiteProj_eq_diagonal]
  exact hopsOne_diagonal _ _

/-- The device's site projector `Q_k` is supported on the site `k`. -/
theorem siteSuppOn_deviceSiteProj (k : ZMod (M + 1)) :
    SiteSuppOn (deviceSite (M + 1)) {k} (deviceSiteProj k) := by
  rw [deviceSiteProj_eq_diagonal]
  exact siteSuppOn_diagonal fun x hx => by
    by_contra hne
    have hxk : ¬ x.1.1 = k := fun e => hne (Finset.mem_singleton.2 e)
    simp [hxk] at hx

end Generators

/-! ### Two site pointers: the responses -/

section DiracTwo

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (j k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The carrier's Hamiltonian with two site pointers is Hermitian. -/
theorem diracTwoH_isHermitian (φ χ : AddCircle (1 : ℝ)) :
    (diracTwoH J μ g₁ g₂ j k hf hh φ χ).IsHermitian := by
  rw [diracTwoH, ← idxTwoH_ofReal_smul]
  exact idxTwoH_isHermitian (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g₁ j)
    (siteProj_smul_isHermitian g₂ k) hf hh φ χ

/-- ★★ **The coupled generator of the two-site-pointer arena hops at most one site**, at every
pair of pointer angles. -/
theorem hopsOne_diracTwoGen (φ χ : AddCircle (1 : ℝ)) :
    HopsOne Prod.fst ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) := by
  unfold diracTwoH
  exact (((hopsOne_diracHam J μ).add ((hopsOne_siteProj j).smul _)).add
    ((hopsOne_siteProj k).smul _)).smul _

theorem continuous_diracTwoCarrierU (φ χ : AddCircle (1 : ℝ)) :
    Continuous fun t : ℝ => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ t :=
  continuous_idxTwoCarrierU (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g₁ j)
    (siteProj_smul_isHermitian g₂ k) hf hh φ χ

/-- Changing the first pointer's angle changes the Hamiltonian by a multiple of `P_j`. -/
theorem diracTwoH_sub_fst (φ φ' χ : AddCircle (1 : ℝ)) :
    diracTwoH J μ g₁ g₂ j k hf hh φ χ - diracTwoH J μ g₁ g₂ j k hf hh φ' χ
      = ((g₁ * (hf.lift φ - hf.lift φ') : ℝ) : ℂ) • siteProj j := by
  unfold diracTwoH
  rw [add_sub_add_right_eq_sub, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring

/-- Changing the second pointer's angle changes the Hamiltonian by a multiple of `P_k`. -/
theorem diracTwoH_sub_snd (φ χ χ' : AddCircle (1 : ℝ)) :
    diracTwoH J μ g₁ g₂ j k hf hh φ χ - diracTwoH J μ g₁ g₂ j k hf hh φ χ'
      = ((g₂ * (hh.lift χ - hh.lift χ') : ℝ) : ℂ) • siteProj k := by
  unfold diracTwoH
  rw [add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring

/-- ★★ **The second pointer's response to a kick.** A kick `W`, the identity off `Y`, is applied
to the carrier's initial ray. With `d` steps of growth from the site `k` missing `Y`, the second
pointer's displacement at `t ≥ 0` moves by at most `4 |g₂| |h'(χ)| (2 ‖H‖ t)^d / d! · t`, `H` the
coupled Hamiltonian. The kick is an intervention of UA-14, and `t` is a flow time (UA-7). -/
theorem abs_diracTwoKickResponseSnd_le {Y : Finset (ZMod (M + 1))}
    {W : Matrix.unitaryGroup (ZMod (M + 1) × Fin 2) ℂ} (hW : IdOffOn Prod.fst Y W.val) {d : ℕ}
    (hcone : Disjoint (growIter {k} d) Y) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ (arenaKick W p) t
        - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ p t|
      ≤ 4 * |g₂| * |hh.deriv_periodic.lift χ|
        * ((2 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ * t) ^ d / d.factorial) * t := by
  have key := abs_displacement_kick_sub_le
    (S := (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ)
    (idxFreeGen_skew (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ))
    (hopsOne_diracTwoGen J μ g₁ g₂ j k hf hh φ χ) (siteSuppOn_siteProj k) (norm_siteProj_le k)
    hW hcone (U := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ)
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ χ s) g₂ (hh.deriv_periodic.lift χ) p ht
  rw [norm_neg_I_smul] at key
  exact key

/-- ★★ **The first pointer's response to a kick**: at most
`4 |g₁| |f'(φ)| (2 ‖H‖ t)^d / d! · t`, with `d` steps of growth from the site `j` missing `Y`. -/
theorem abs_diracTwoKickResponseFst_le {Y : Finset (ZMod (M + 1))}
    {W : Matrix.unitaryGroup (ZMod (M + 1) × Fin 2) ℂ} (hW : IdOffOn Prod.fst Y W.val) {d : ℕ}
    (hcone : Disjoint (growIter {j} d) Y) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ (arenaKick W p) t
        - diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ p t|
      ≤ 4 * |g₁| * |hf.deriv_periodic.lift φ|
        * ((2 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ * t) ^ d / d.factorial) * t := by
  have key := abs_displacement_kick_sub_le
    (S := (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ)
    (idxFreeGen_skew (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ))
    (hopsOne_diracTwoGen J μ g₁ g₂ j k hf hh φ χ) (siteSuppOn_siteProj j) (norm_siteProj_le j)
    hW hcone (U := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ)
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ χ s) g₁ (hf.deriv_periodic.lift φ) p ht
  rw [norm_neg_I_smul] at key
  exact key

/-- ★★ **The second pointer's response to the first pointer's angle.** Two runs differ in the
first pointer's conserved angle, `φ` against `φ'`. With `d` steps of growth from the site `k`
missing the site `j`, the second pointer's displacements at `t ≥ 0` differ by at most
`4 |g₂| |h'(χ)| |g₁| |f(φ) − f(φ')| (2 ‖H'‖ t)^d / d! · t²`, `H'` the Hamiltonian at `φ'`. Unlike
the cross-talk bound `abs_diracTwoShiftSnd_sub_le` of #359, this one falls with the distance
between the sites. -/
theorem abs_diracTwoAngleResponseSnd_le {d : ℕ} (hcone : Disjoint (growIter {k} d) {j})
    (φ φ' χ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ p t
        - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ' χ p t|
      ≤ 4 * |g₂| * |hh.deriv_periodic.lift χ| * (|g₁| * |hf.lift φ - hf.lift φ'|)
        * ((2 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ' χ‖ * t) ^ d / d.factorial) * t ^ 2 := by
  have hsub : (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ
      - (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ' χ
      = (-Complex.I) • (((g₁ * (hf.lift φ - hf.lift φ') : ℝ) : ℂ) • siteProj j) := by
    rw [← smul_sub, diracTwoH_sub_fst]
  have hΔ : SiteSuppOn Prod.fst {j} ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ
      - (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ' χ) := by
    rw [hsub]
    exact ((siteSuppOn_siteProj j).smul _).smul _
  have hΔn : ‖(-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ
      - (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ' χ‖ ≤ |g₁| * |hf.lift φ - hf.lift φ'| := by
    rw [hsub, norm_neg_I_smul, ← abs_mul]
    exact norm_ofReal_smul_le _ (norm_siteProj_le j)
  have key := abs_displacement_flow_sub_le
    (idxFreeGen_skew (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ))
    (idxFreeGen_skew
      (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ' χ))
    (hopsOne_diracTwoGen J μ g₁ g₂ j k hf hh φ' χ) (siteSuppOn_siteProj k) (norm_siteProj_le k)
    hΔ hΔn hcone (U := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s)
    (U' := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ' χ s)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ' χ)
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ χ s)
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ' χ s) g₂ (hh.deriv_periodic.lift χ) p ht
  rw [norm_neg_I_smul] at key
  exact key

/-- ★★ **The first pointer's response to the second pointer's angle**: at most
`4 |g₁| |f'(φ)| |g₂| |h(χ) − h(χ')| (2 ‖H'‖ t)^d / d! · t²`, `H'` the Hamiltonian at `χ'`, with
`d` steps of growth from the site `j` missing the site `k`. -/
theorem abs_diracTwoAngleResponseFst_le {d : ℕ} (hcone : Disjoint (growIter {j} d) {k})
    (φ χ χ' : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ p t
        - diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ' p t|
      ≤ 4 * |g₁| * |hf.deriv_periodic.lift φ| * (|g₂| * |hh.lift χ - hh.lift χ'|)
        * ((2 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ'‖ * t) ^ d / d.factorial) * t ^ 2 := by
  have hsub : (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ
      - (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ'
      = (-Complex.I) • (((g₂ * (hh.lift χ - hh.lift χ') : ℝ) : ℂ) • siteProj k) := by
    rw [← smul_sub, diracTwoH_sub_snd]
  have hΔ : SiteSuppOn Prod.fst {k} ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ
      - (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ') := by
    rw [hsub]
    exact ((siteSuppOn_siteProj k).smul _).smul _
  have hΔn : ‖(-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ
      - (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ'‖ ≤ |g₂| * |hh.lift χ - hh.lift χ'| := by
    rw [hsub, norm_neg_I_smul, ← abs_mul]
    exact norm_ofReal_smul_le _ (norm_siteProj_le k)
  have key := abs_displacement_flow_sub_le
    (idxFreeGen_skew (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ))
    (idxFreeGen_skew
      (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ'))
    (hopsOne_diracTwoGen J μ g₁ g₂ j k hf hh φ χ') (siteSuppOn_siteProj j) (norm_siteProj_le j)
    hΔ hΔn hcone (U := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s)
    (U' := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ' s)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ')
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ χ s)
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ χ' s) g₁ (hf.deriv_periodic.lift φ) p ht
  rw [norm_neg_I_smul] at key
  exact key

/-- **The kick response is a difference of two runs of the joint flow**: the second pointer's
moving angle from the kicked initial point is its angle from the unkicked one, turned by the
response. -/
theorem diracTwoPointerFlow_kick_snd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (W : Matrix.unitaryGroup (ZMod (M + 1) × Fin 2) ℂ) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
        ((diracArenaEquiv M (arenaKick W p), θ), ψ)).2.1
      = (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)).2.1
        + ((diracTwoShiftSnd J μ g₁ g₂ j k hf hh θ.2 ψ.2 (arenaKick W p) t
            - diracTwoShiftSnd J μ g₁ g₂ j k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [diracTwoPointerFlow_apply, diracTwoPointerFlow_apply]
  simp only [AddCircle.coe_sub, add_assoc, add_sub_cancel]

/-- The first pointer's kick response as a difference of two runs of the joint flow. -/
theorem diracTwoPointerFlow_kick_fst (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (W : Matrix.unitaryGroup (ZMod (M + 1) × Fin 2) ℂ) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
        ((diracArenaEquiv M (arenaKick W p), θ), ψ)).1.2.1
      = (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)).1.2.1
        + ((diracTwoShiftFst J μ g₁ g₂ j k hf hh θ.2 ψ.2 (arenaKick W p) t
            - diracTwoShiftFst J μ g₁ g₂ j k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [diracTwoPointerFlow_apply, diracTwoPointerFlow_apply]
  simp only [AddCircle.coe_sub, add_assoc, add_sub_cancel]

/-- **The angle response is a difference of two runs of the joint flow** from initial points
that differ in the first pointer's conserved angle only. -/
theorem diracTwoPointerFlow_angle_snd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ₁ φ φ' : AddCircle (1 : ℝ)) (ψ : KTorus) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, (θ₁, φ)), ψ)).2.1
      = (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
          ((diracArenaEquiv M p, (θ₁, φ')), ψ)).2.1
        + ((diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ ψ.2 p t
            - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ' ψ.2 p t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [diracTwoPointerFlow_apply, diracTwoPointerFlow_apply]
  simp only [AddCircle.coe_sub, add_assoc, add_sub_cancel]

/-- The first pointer's angle response as a difference of two runs of the joint flow, from
initial points that differ in the second pointer's conserved angle only. -/
theorem diracTwoPointerFlow_angle_fst (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) (ψ₁ χ χ' : AddCircle (1 : ℝ)) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
        ((diracArenaEquiv M p, θ), (ψ₁, χ))).1.2.1
      = (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t
          ((diracArenaEquiv M p, θ), (ψ₁, χ'))).1.2.1
        + ((diracTwoShiftFst J μ g₁ g₂ j k hf hh θ.2 χ p t
            - diracTwoShiftFst J μ g₁ g₂ j k hf hh θ.2 χ' p t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [diracTwoPointerFlow_apply, diracTwoPointerFlow_apply]
  simp only [AddCircle.coe_sub, add_assoc, add_sub_cancel]

end DiracTwo

/-! ### The clock's pointer and a site pointer: the site pointer's response -/

section ClockSite

variable {M : ℕ} {f h : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ : ℝ) (k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The device's Hamiltonian with both pointers is Hermitian. -/
theorem clockSiteH_isHermitian (φ χ : AddCircle (1 : ℝ)) :
    (clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ).IsHermitian := by
  rw [clockSiteH, ← idxTwoH_ofReal_smul]
  exact idxTwoH_isHermitian (deviceHam_isHermitian J μ₀ μ₁)
    (isHermitian_ofReal_smul g₁ (levelSwap_isHermitian _)) (deviceSiteProj_smul_isHermitian g₂ k)
    hf hh φ χ

/-- ★★ **The coupled generator of the clock-and-site arena hops at most one site**, at every
pair of pointer angles. The level swap is not supported on any proper set of sites
(`mem_of_siteSuppOn_levelSwap`), and it moves nothing between them. -/
theorem hopsOne_clockSiteGen (φ χ : AddCircle (1 : ℝ)) :
    HopsOne (deviceSite (M + 1)) ((-Complex.I) • clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ) := by
  unfold clockSiteH
  exact (((hopsOne_deviceHam J μ₀ μ₁).add (hopsOne_levelSwap.smul _)).add
    ((hopsOne_deviceSiteProj k).smul _)).smul _

theorem continuous_clockSiteCarrierU (φ χ : AddCircle (1 : ℝ)) :
    Continuous fun t : ℝ => clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ t :=
  continuous_idxTwoCarrierU (deviceHam_isHermitian J μ₀ μ₁) (clockB_isHermitian g₁)
    (deviceSiteProj_smul_isHermitian g₂ k) hf hh φ χ

/-- ★★ **The site pointer's response to a kick, on the clock-and-site arena.** A kick `W`, the
identity off `Y`, is applied to the device's initial ray. With `d` steps of growth from the site
`k` missing `Y`, the site pointer's displacement at `t ≥ 0` moves by at most
`4 |g₂| |h'(χ)| (2 ‖H‖ t)^d / d! · t`, `H` the coupled Hamiltonian with the clock's coupling in
it. -/
theorem abs_clockSiteKickResponseSnd_le {Y : Finset (ZMod (M + 1))}
    {W : Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ}
    (hW : IdOffOn (deviceSite (M + 1)) Y W.val) {d : ℕ} (hcone : Disjoint (growIter {k} d) Y)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ}
    (ht : 0 ≤ t) :
    |clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ (arenaKick W p) t
        - clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t|
      ≤ 4 * |g₂| * |hh.deriv_periodic.lift χ|
        * ((2 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ * t) ^ d / d.factorial) * t := by
  have key := abs_displacement_kick_sub_le
    (S := (-Complex.I) • clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ)
    (idxFreeGen_skew
      (clockSiteH_isHermitian J μ₀ μ₁ g₁ g₂ k hf hh φ χ))
    (hopsOne_clockSiteGen J μ₀ μ₁ g₁ g₂ k hf hh φ χ) (siteSuppOn_deviceSiteProj k)
    (norm_deviceSiteProj_le k) hW hcone
    (U := fun s => clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s)
    (continuous_clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ)
    (fun s => clockSiteCarrierU_val J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) g₂ (hh.deriv_periodic.lift χ)
    p ht
  rw [norm_neg_I_smul] at key
  exact key

/-- The site pointer's kick response as a difference of two runs of `clockSiteFlow`. -/
theorem clockSiteFlow_kick_snd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (W : Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ) (t : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) :
    (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t
        ((clockArenaEquiv M (arenaKick W p), θ), ψ)).2.1
      = (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).2.1
        + ((clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 (arenaKick W p) t
            - clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [clockSiteFlow_apply, clockSiteFlow_apply]
  simp only [AddCircle.coe_sub, add_assoc, add_sub_cancel]

/-- ★★★ **The position write survives a remote kick, within margins.** On the clock-and-site
arena, let the site pointer's displacement in the unkicked run clear the three thresholds of
`isRecordWrite_clockSiteFlow_site` by the kick bound `4 |g₂| |h'(ψ₂)| (2 ‖H‖ τ)^d / d! · τ` at
each of the three times. Then the run from the kicked initial point writes the same position
record over the same flow times. The kick is the identity off `Y`, and `d` steps of growth from
the site `k` miss `Y`. The site pointer starts ready, on a fibre of nonnegative rate. The kick is
an intervention of UA-14, and the times are flow times (UA-7). No instance in which the three
margins hold is given. -/
theorem isRecordWrite_clockSiteFlow_site_of_kick (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {ψ : KTorus} (hψ : ψ ∈ readyArc 2) (θ : KTorus) (hκ : 0 ≤ rateAt g₂ 1 hh ψ.2)
    {Y : Finset (ZMod (M + 1))} {W : Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ}
    (hW : IdOffOn (deviceSite (M + 1)) Y W.val) {d : ℕ} (hcone : Disjoint (growIter {k} d) Y)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₀
      + 4 * |g₂| * |hh.deriv_periodic.lift ψ.2|
        * ((2 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2‖ * τ₀) ^ d / d.factorial) * τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₁
      - 4 * |g₂| * |hh.deriv_periodic.lift ψ.2|
        * ((2 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2‖ * τ₁) ^ d / d.factorial) * τ₁)
    (h₂ : clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p τ₂
      + 4 * |g₂| * |hh.deriv_periodic.lift ψ.2|
        * ((2 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2‖ * τ₂) ^ d / d.factorial) * τ₂
        ≤ 2 / 3) :
    IsRecordWrite
      (fun t => echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t
          ((clockArenaEquiv M (arenaKick W p), θ), ψ)))
      0 τ₀ τ₁ (τ₂ - τ₁) true := by
  have e₀ := abs_le.1
    (abs_clockSiteKickResponseSnd_le J μ₀ μ₁ g₁ g₂ k hf hh hW hcone θ.2 ψ.2 p hτ₀)
  have e₁ := abs_le.1
    (abs_clockSiteKickResponseSnd_le J μ₀ μ₁ g₁ g₂ k hf hh hW hcone θ.2 ψ.2 p (hτ₀.trans hτ₁))
  have e₂ := abs_le.1
    (abs_clockSiteKickResponseSnd_le J μ₀ μ₁ g₁ g₂ k hf hh hW hcone θ.2 ψ.2 p
      ((hτ₀.trans hτ₁).trans hτ₂))
  exact isRecordWrite_clockSiteFlow_site J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ hκ (arenaKick W p)
    hτ₀ hτ₁ hτ₂ (by linarith [e₀.2]) (by linarith [e₁.1]) (by linarith [e₂.2])

end ClockSite

end CSD.RecordLayer

end
