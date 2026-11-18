/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCausalOrder
public import CsdLean4.CV.DiracLatticeD

/-!
# The propagation bound over any site graph, and on the torus

**Category:** 7-SigmaLayer. BACKLOG #297, first brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, items 1 and 2).

`RecordLayer/ChainCone.lean` and `RecordLayer/UnifiedCausalOrder.lean` bound the spread of a
generator whose sites lie on a ring. The argument uses the ring only through one fact: a
commutator with the generator moves support by one step. This module states that fact for a
site map into any type with an adjacency relation, and reads the ring and the `d`-dimensional
torus off it.

## Any graph

* `SiteSuppG`, `HopsG`, `IdOffG`, `growG`, `growIterG`, `subset_growG`, `growIterG_mono`;
* ★★ `siteSuppG_adOne`, `siteSuppG_adIter` — a commutator with a generator that hops along
  the graph moves support by one step of growth;
* ★★★ `norm_commutator_graph_le` — the bound `‖[A(t), B]‖ ≤ 2 (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖`
  when `d` steps of growth from the sites of `A` miss the sites of `B`;
* ★★ `norm_commutator_graph_idOffG_le`, ★★ `norm_heisenbergFlow_sub_graph_le` — the same
  against a kick, and between two generators that differ away from the observable;
* ★★ `abs_arenaObs_flow_kick_sub_graph_le`, ★★ `abs_arenaObs_flow_sub_flow_graph_le` — the
  two responses of an occupancy on the arena;
* `rank_le_of_mem_growIterG`, `disjoint_growIterG_of_rank` — a criterion for the growth to
  miss a set, from any function that changes by at most one along an edge.

## The ring

* `ringAdj`, `HopsOne.hopsG`, `coe_grow`, `coe_growIter` — the predicates of
  `UnifiedCausalOrder.lean` are the case of the ring's graph.

## The torus

* `torusAdj`, ★★ `hopsG_latticeDiracHam` — the lattice Dirac Hamiltonian in any dimension
  hops along the torus's graph;
* `exists_int_of_mem_growIterG_torus`, `disjoint_growIterG_torus` — `d` steps of growth from
  `X` reach only sites `y + v` with `∑ i |v i| ≤ d`;
* ★★★ `norm_commutator_latticeDirac_le` — the bound for the lattice Dirac generator on the
  torus, with rate `2 ‖H‖`.

## Honest scope

⚠️ **Upper bounds with a factorial tail, not an exclusion.** Nothing here says an influence
arrives, and nothing vanishes outside the growth except at time zero.

⚠️ **The graph is given.** It is read off the entries of the generator. It is not derived
from anything else, and the bound orders nothing by itself: no event order, no metric.

⚠️ **The rate is `2 ‖S‖`**, the whole generator's norm, not the group velocity. For the torus
it is not computed as a number here.

⚠️ **The ring's theorems were not re-proved from these.** `HopsOne.hopsG` and `coe_growIter`
show that they are the case of the ring's graph; their existing proofs stand as they were.

⚠️ **No detector and no record.** The torus has no pointer coupled to it in this module.

References: `specs/BACKLOG.md` #297, #361; `specs/unified-record-spacetime-plan.md` (UD-230,
UA-14, UO-15); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/UnifiedCausalOrder.lean` (`HopsOne`, `SiteSuppOn`,
`norm_commutator_heisenbergFlow_le_of_adIter_commute`,
`norm_heisenbergFlow_sub_le_of_commutator_le`); `RecordLayer/ChainCone.lean` (`grow`,
`growIter`); `CV/DiracLatticeD.lean` (`latticeDiracHam`, `latticeDiracHam_apply_eq_zero`);
`CV/LiebRobinson.lean` (`heisenbergFlow`, `adOne`, `adIter`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### Supports and hops over a graph -/

section Graph

variable {V n : Type*}

/-- **Supported on a set of sites, over a site map** `σ` into any type. -/
def SiteSuppG (σ : n → V) (X : Set V) (A : Matrix n n ℂ) : Prop :=
  ∀ p q, A p q ≠ 0 → σ p ∈ X ∧ σ q ∈ X

/-- **Hops along the graph**: every nonzero entry joins indices whose sites are equal or
adjacent. -/
def HopsG (adj : V → V → Prop) (σ : n → V) (G : Matrix n n ℂ) : Prop :=
  ∀ p q, G p q ≠ 0 → σ p = σ q ∨ adj (σ p) (σ q)

/-- **The identity off a set of sites.** -/
def IdOffG [DecidableEq n] (σ : n → V) (Y : Set V) (W : Matrix n n ℂ) : Prop :=
  ∀ p q, (σ p ∉ Y ∨ σ q ∉ Y) → W p q = if p = q then 1 else 0

/-- **One step of growth**: the set with every site joined to it by an edge, in either
direction. -/
def growG (adj : V → V → Prop) (X : Set V) : Set V :=
  {a | a ∈ X ∨ ∃ b ∈ X, adj a b ∨ adj b a}

/-- `d` steps of growth. -/
def growIterG (adj : V → V → Prop) (X : Set V) : ℕ → Set V
  | 0 => X
  | d + 1 => growG adj (growIterG adj X d)

theorem subset_growG (adj : V → V → Prop) (X : Set V) : X ⊆ growG adj X := fun _ hx =>
  Or.inl hx

theorem growIterG_mono (adj : V → V → Prop) (X : Set V) {j d : ℕ} (h : j ≤ d) :
    growIterG adj X j ⊆ growIterG adj X d := by
  induction d with
  | zero => rw [Nat.le_zero.1 h]
  | succ d ih =>
    rcases Nat.lt_or_ge j (d + 1) with hj | hj
    · exact (ih (Nat.lt_succ_iff.1 hj)).trans (subset_growG adj _)
    · rw [le_antisymm h hj]

/-- A multiple of a matrix that hops along the graph hops along the graph. -/
theorem HopsG.smul {adj : V → V → Prop} {σ : n → V} {G : Matrix n n ℂ} (c : ℂ)
    (hG : HopsG adj σ G) : HopsG adj σ (c • G) := fun p q h =>
  hG p q fun h0 => h (by rw [Matrix.smul_apply, h0, smul_zero])

/-- A sum of two matrices that hop along the graph hops along the graph. -/
theorem HopsG.add {adj : V → V → Prop} {σ : n → V} {G K : Matrix n n ℂ}
    (hG : HopsG adj σ G) (hK : HopsG adj σ K) : HopsG adj σ (G + K) := fun p q h => by
  by_cases hg : G p q = 0
  · refine hK p q fun h0 => h ?_
    rw [Matrix.add_apply, hg, h0, add_zero]
  · exact hG p q hg

/-- A matrix that is the identity off `Y`, less the identity, is supported on `Y`. -/
theorem IdOffG.siteSuppG_sub_one [DecidableEq n] {σ : n → V} {Y : Set V}
    {W : Matrix n n ℂ} (hW : IdOffG σ Y W) : SiteSuppG σ Y (W - 1) := fun p q h => by
  by_contra hc
  apply h
  rw [Matrix.sub_apply, Matrix.one_apply, hW p q (not_and_or.1 hc), sub_self]

/-- ★★ **One commutator with a generator that hops along the graph grows the support by one
step.** -/
theorem siteSuppG_adOne [Fintype n] [DecidableEq n] {adj : V → V → Prop} {σ : n → V} {X : Set V}
    {G A : Matrix n n ℂ} (hG : HopsG adj σ G) (hA : SiteSuppG σ X A) :
    SiteSuppG σ (growG adj X) (adOne G A) := by
  intro p q hpq
  rw [adOne, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply] at hpq
  by_contra hcon
  have h1 : ∀ r, G p r * A r q = 0 := fun r => by
    by_contra h2
    obtain ⟨hG1, hA1⟩ := mul_ne_zero_iff.1 h2
    obtain ⟨hr, hq⟩ := hA r q hA1
    refine hcon ⟨?_, subset_growG adj X hq⟩
    rcases hG p r hG1 with e | e
    · exact Or.inl (e ▸ hr)
    · exact Or.inr ⟨σ r, hr, Or.inl e⟩
  have h2 : ∀ r, A p r * G r q = 0 := fun r => by
    by_contra h2
    obtain ⟨hA1, hG1⟩ := mul_ne_zero_iff.1 h2
    obtain ⟨hp, hr⟩ := hA p r hA1
    refine hcon ⟨subset_growG adj X hp, ?_⟩
    rcases hG r q hG1 with e | e
    · exact Or.inl (e ▸ hr)
    · exact Or.inr ⟨σ r, hr, Or.inr e⟩
  apply hpq
  rw [Finset.sum_eq_zero fun r _ => h1 r, Finset.sum_eq_zero fun r _ => h2 r, sub_self]

/-- **`j` commutators grow the support by `j` steps.** -/
theorem siteSuppG_adIter [Fintype n] [DecidableEq n] {adj : V → V → Prop} {σ : n → V} {X : Set V}
    {G A : Matrix n n ℂ} (hG : HopsG adj σ G) (hA : SiteSuppG σ X A) (j : ℕ) :
    SiteSuppG σ (growIterG adj X j) (adIter G j A) := by
  induction j with
  | zero => exact hA
  | succ j ih => exact siteSuppG_adOne hG ih

/-- Matrices supported on disjoint sets of sites multiply to zero. -/
theorem mul_eq_zero_of_siteSuppG_disjoint [Fintype n] {σ : n → V} {X Y : Set V}
    {A B : Matrix n n ℂ} (hXY : Disjoint X Y) (hA : SiteSuppG σ X A)
    (hB : SiteSuppG σ Y B) : A * B = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  exact Set.disjoint_left.1 hXY (hA p r h1).2 (hB r q h2).1

/-- Matrices supported on disjoint sets of sites commute. -/
theorem commute_of_siteSuppG_disjoint [Fintype n] {σ : n → V} {X Y : Set V}
    {A B : Matrix n n ℂ} (hXY : Disjoint X Y) (hA : SiteSuppG σ X A)
    (hB : SiteSuppG σ Y B) : A * B = B * A := by
  rw [mul_eq_zero_of_siteSuppG_disjoint hXY hA hB,
    mul_eq_zero_of_siteSuppG_disjoint hXY.symm hB hA]

/-- A matrix supported on `X` commutes with a matrix that is the identity off a disjoint
`Y`. -/
theorem commute_of_siteSuppG_idOffG [Fintype n] [DecidableEq n] {σ : n → V} {X Y : Set V}
    {A W : Matrix n n ℂ} (hXY : Disjoint X Y) (hA : SiteSuppG σ X A) (hW : IdOffG σ Y W) :
    A * W = W * A := by
  have h := commute_of_siteSuppG_disjoint hXY hA hW.siteSuppG_sub_one
  rw [mul_sub, sub_mul, mul_one, one_mul] at h
  exact sub_left_inj.1 h

/-! ### The bound -/

/-- ★★★ **The propagation bound over a graph.** For a skew-Hermitian `S` that hops along the
graph, `A` supported on `X`, `B` supported on `Y`, and `d` steps of growth from `X` missing
`Y`: `‖[A(t), B]‖ ≤ 2 (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖` for `t ≥ 0`. A factorial tail, not an
exclusion. -/
theorem norm_commutator_graph_le [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hhop : HopsG adj σ S) {X Y : Set V} {A B : Matrix n n ℂ} (hA : SiteSuppG σ X A)
    (hB : SiteSuppG σ Y B) {d : ℕ} (hcone : Disjoint (growIterG adj X d) Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ :=
  norm_commutator_heisenbergFlow_le_of_adIter_commute hS A B d
    (fun j hj => commute_of_siteSuppG_disjoint
      (Set.disjoint_of_subset_left (growIterG_mono adj X hj.le) hcone)
      (siteSuppG_adIter hhop hA j) hB) ht

/-- ★★ **The bound against a kick**: the same with `B` replaced by a matrix `W` that is the
identity off `Y`. -/
theorem norm_commutator_graph_idOffG_le [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hhop : HopsG adj σ S) {X Y : Set V} {A W : Matrix n n ℂ} (hA : SiteSuppG σ X A)
    (hW : IdOffG σ Y W) {d : ℕ} (hcone : Disjoint (growIterG adj X d) Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * W - W * heisenbergFlow S t A‖
      ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖A‖ * ‖W‖ :=
  norm_commutator_heisenbergFlow_le_of_adIter_commute hS A W d
    (fun j hj => commute_of_siteSuppG_idOffG
      (Set.disjoint_of_subset_left (growIterG_mono adj X hj.le) hcone)
      (siteSuppG_adIter hhop hA j) hW) ht

/-- ★★ **Two generators that differ away from an observable evolve it almost alike.** For
skew-Hermitian `S`, `S'` with `S'` hopping along the graph, `D` supported on `X`, `S − S'`
supported on `Y`, and `d` steps of growth from `X` missing `Y`:
`‖τ_t^S D − τ_t^{S'} D‖ ≤ 2 (2 ‖S'‖ t)^d / d! · ‖D‖ ‖S − S'‖ · t` for `t ≥ 0`. -/
theorem norm_heisenbergFlow_sub_graph_le [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S S' : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hS' : S'ᴴ = -S') (hhop : HopsG adj σ S') {X Y : Set V} {D : Matrix n n ℂ}
    (hD : SiteSuppG σ X D) (hΔ : SiteSuppG σ Y (S - S')) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow S t D - heisenbergFlow S' t D‖
      ≤ 2 * ((2 * ‖S'‖ * t) ^ d / d.factorial) * ‖D‖ * ‖S - S'‖ * t :=
  norm_heisenbergFlow_sub_le_of_commutator_le hS D ht fun u hu _ =>
    (norm_commutator_graph_le hS' hhop hD hΔ hcone hu).trans (by gcongr)

/-! ### On the arena -/

/-- ★★ **The response of an occupancy to a kick, over a graph.** The carrier moves by
`exp (t S)`. A kick `W`, the identity off `Y`, is applied to the initial ray. An observable
`D` on `X`, read at time `t ≥ 0`, moves by at most `2 (2 ‖S‖ t)^d / d! · ‖D‖` when `d` steps
of growth from `X` miss `Y`. -/
theorem abs_arenaObs_flow_kick_sub_graph_le [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hhop : HopsG adj σ S) {X Y : Set V} {D : Matrix n n ℂ} (hD : SiteSuppG σ X D)
    {W : Matrix.unitaryGroup n ℂ} (hW : IdOffG σ Y W.val) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) {t : ℝ} (ht : 0 ≤ t)
    {U : Matrix.unitaryGroup n ℂ} (hU : U.val = exp (t • S)) (p : GenArena n) :
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
        norm_commutator_graph_idOffG_le hS hhop hD hW hcone ht
    _ = 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖D‖ := by
        rw [CStarRing.norm_of_mem_unitary W.property, mul_one]

/-- ★★ **The response of an occupancy to a change of the generator, over a graph.** Two
carriers move by `exp (t S)` and `exp (t S')` from the same ray, with `S − S'` supported on
`Y`. An observable `D` on `X`, read at time `t ≥ 0`, differs between them by at most
`2 (2 ‖S'‖ t)^d / d! · ‖D‖ ‖S − S'‖ · t` when `d` steps of growth from `X` miss `Y`. -/
theorem abs_arenaObs_flow_sub_flow_graph_le [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S S' : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hS' : S'ᴴ = -S') (hhop : HopsG adj σ S') {X Y : Set V} {D : Matrix n n ℂ}
    (hD : SiteSuppG σ X D) (hΔ : SiteSuppG σ Y (S - S')) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) {t : ℝ} (ht : 0 ≤ t)
    {U U' : Matrix.unitaryGroup n ℂ} (hU : U.val = exp (t • S))
    (hU' : U'.val = exp (t • S')) (p : GenArena n) :
    |arenaObs D (arenaKick U p) - arenaObs D (arenaKick U' p)|
      ≤ 2 * ((2 * ‖S'‖ * t) ^ d / d.factorial) * ‖D‖ * ‖S - S'‖ * t := by
  rw [arenaObs_kick_conj U D p, arenaObs_kick_conj U' D p, hU, hU',
    star_exp_smul_mul_exp_smul hS t D, star_exp_smul_mul_exp_smul hS' t D]
  exact (arenaObs_sub_le _ _ p).trans
    (norm_heisenbergFlow_sub_graph_le hS hS' hhop hD hΔ hcone ht)

/-! ### When the growth misses a set -/

/-- **A rank bounds the growth.** If `g` vanishes on `X` and changes by at most one along an
edge, a site reached by `d` steps of growth from `X` has `g ≤ d`. -/
theorem rank_le_of_mem_growIterG {adj : V → V → Prop} {X : Set V} {g : V → ℕ}
    (hX : ∀ x ∈ X, g x = 0) (hstep : ∀ a b, adj a b ∨ adj b a → g a ≤ g b + 1) {d : ℕ}
    {x : V} (hx : x ∈ growIterG adj X d) : g x ≤ d := by
  induction d generalizing x with
  | zero => exact (hX x hx).le
  | succ d ih =>
    rcases hx with h | ⟨b, hb, hab⟩
    · exact (ih h).trans (Nat.le_succ d)
    · exact (hstep x b hab).trans (Nat.succ_le_succ (ih hb))

/-- **Far in rank, so outside the growth.** If every site of `Y` has rank above `d`, then `d`
steps of growth from `X` miss `Y`. -/
theorem disjoint_growIterG_of_rank {adj : V → V → Prop} {X Y : Set V} {g : V → ℕ}
    (hX : ∀ x ∈ X, g x = 0) (hstep : ∀ a b, adj a b ∨ adj b a → g a ≤ g b + 1) {d : ℕ}
    (hY : ∀ y ∈ Y, d < g y) : Disjoint (growIterG adj X d) Y :=
  Set.disjoint_left.2 fun z hz hzY =>
    absurd (rank_le_of_mem_growIterG hX hstep hz) (not_le.2 (hY z hzY))

end Graph

/-! ### The ring is a graph -/

section Ring

variable {L : ℕ} {n : Type*}

/-- **The ring's graph**: a site is joined to its two neighbours. -/
def ringAdj (a b : ZMod L) : Prop := b = a + 1 ∨ b = a - 1

/-- A generator that hops at most one site on the ring hops along the ring's graph. -/
theorem HopsOne.hopsG {σ : n → ZMod L} {G : Matrix n n ℂ} (hG : HopsOne σ G) :
    HopsG ringAdj σ G := fun p q h => by
  rcases hG p q h with e | e | e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)
  · exact Or.inl e.symm

/-- One site of growth on the ring is one step of growth in the ring's graph. -/
theorem coe_grow (X : Finset (ZMod L)) :
    (grow X : Set (ZMod L)) = growG ringAdj (X : Set (ZMod L)) := by
  ext a
  simp only [grow, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
    Finset.mem_coe, growG, Set.mem_ofPred_eq, ringAdj]
  constructor
  · rintro ((h | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, hb, Or.inr (Or.inl rfl)⟩
    · exact Or.inr ⟨b, hb, Or.inr (Or.inr rfl)⟩
  · rintro (h | ⟨b, hb, (e | e) | (e | e)⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨b, hb, by rw [e]; ring⟩
    · exact Or.inl (Or.inr ⟨b, hb, by rw [e]; ring⟩)
    · exact Or.inl (Or.inr ⟨b, hb, e.symm⟩)
    · exact Or.inr ⟨b, hb, e.symm⟩

/-- `d` sites of growth on the ring are `d` steps of growth in the ring's graph. -/
theorem coe_growIter (X : Finset (ZMod L)) (d : ℕ) :
    (growIter X d : Set (ZMod L)) = growIterG ringAdj (X : Set (ZMod L)) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (grow (growIter X d) : Set (ZMod L)) = growG ringAdj (growIterG ringAdj X d)
    rw [coe_grow, ih]

end Ring

/-! ### The torus -/

section Torus

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}

/-- **The torus's graph**: a site is joined to its two neighbours along each axis. -/
def torusAdj (a b : ι → ZMod L) : Prop :=
  ∃ i, b = a + Pi.single i 1 ∨ b = a - Pi.single i 1

omit [Fintype ι] in
theorem torusAdj_symm {a b : ι → ZMod L} (h : torusAdj a b) : torusAdj b a := by
  obtain ⟨i, e | e⟩ := h
  · exact ⟨i, Or.inr (by rw [e, add_sub_cancel_right])⟩
  · exact ⟨i, Or.inl (by rw [e, sub_add_cancel])⟩

/-- ★★ **The lattice Dirac Hamiltonian hops along the torus's graph**, in any dimension and
for any matrices on the spinor. -/
theorem hopsG_latticeDiracHam (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ) (J μ : ℝ) :
    HopsG torusAdj Prod.fst (latticeDiracHam (L := L) α β J μ) := fun p q h => by
  by_contra hc
  rw [not_or] at hc
  refine h (latticeDiracHam_apply_eq_zero α β J μ (fun i => ⟨fun e => ?_, fun e => ?_⟩)
    fun e => hc.1 e.symm)
  · exact hc.2 ⟨i, Or.inl e⟩
  · exact hc.2 ⟨i, Or.inr e⟩

/-- **A site reached by `d` steps of growth on the torus** from `X` is `y + v` for a site `y`
of `X` and integers `v` with `∑ i |v i| ≤ d`. -/
theorem exists_int_of_mem_growIterG_torus {X : Set (ι → ZMod L)} {d : ℕ} {x : ι → ZMod L}
    (hx : x ∈ growIterG torusAdj X d) :
    ∃ y ∈ X, ∃ v : ι → ℤ, ∑ i, |v i| ≤ d ∧ x = y + fun i => ((v i : ℤ) : ZMod L) := by
  induction d generalizing x with
  | zero =>
    refine ⟨x, hx, 0, by simp, ?_⟩
    ext i
    simp
  | succ d ih =>
    have hsingle : ∀ (v : ι → ℤ) (i : ι) (c : ℤ), |c| ≤ 1 →
        ∑ j, |(v + Pi.single i c : ι → ℤ) j| ≤ ∑ j, |v j| + 1 := by
      intro v i c hc
      calc ∑ j, |(v + Pi.single i c : ι → ℤ) j|
          ≤ ∑ j, (|v j| + if j = i then 1 else 0) := Finset.sum_le_sum fun j _ => by
            rw [Pi.add_apply]
            refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
            by_cases hj : j = i
            · subst hj
              simpa using hc
            · simp [hj]
        _ = ∑ j, |v j| + 1 := by
            rw [Finset.sum_add_distrib]
            simp
    have hstep : ∀ z ∈ growIterG torusAdj X d, ∀ (i : ι) (c : ℤ), |c| ≤ 1 →
        ∃ y ∈ X, ∃ v : ι → ℤ, ∑ j, |v j| ≤ ((d + 1 : ℕ) : ℤ)
          ∧ z + (Pi.single i ((c : ℤ) : ZMod L) : ι → ZMod L)
            = y + (fun j => ((v j : ℤ) : ZMod L) : ι → ZMod L) := by
      intro z hz i c hc
      obtain ⟨y, hy, v, hv, e⟩ := ih hz
      have hb := hsingle v i c hc
      refine ⟨y, hy, (v + Pi.single i c : ι → ℤ), ?_, ?_⟩
      · refine hb.trans ?_
        push_cast
        linarith
      rw [e]
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.add_apply, Pi.single_eq_same]
        push_cast
        ring
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj]
        push_cast
        ring
    rcases hx with h | ⟨b, hb, hab⟩
    · obtain ⟨y, hy, v, hv, e⟩ := ih h
      exact ⟨y, hy, v, hv.trans (by push_cast; linarith), e⟩
    · have hadj : torusAdj b x := hab.elim torusAdj_symm id
      obtain ⟨i, e | e⟩ := hadj
      · obtain ⟨y, hy, v, hv, e'⟩ := hstep b hb i 1 (by norm_num)
        refine ⟨y, hy, v, hv, ?_⟩
        rw [e, ← e']
        simp
      · obtain ⟨y, hy, v, hv, e'⟩ := hstep b hb i (-1) (by norm_num)
        refine ⟨y, hy, v, hv, ?_⟩
        rw [e, ← e', sub_eq_add_neg, ← Pi.single_neg]
        simp

/-- **Far apart on the torus, so outside the growth.** If no site of `Y` is `x + v` for a
site `x` of `X` and integers with `∑ i |v i| ≤ d`, then `d` steps of growth from `X` miss
`Y`. -/
theorem disjoint_growIterG_torus {X Y : Set (ι → ZMod L)} {d : ℕ}
    (h : ∀ x ∈ X, ∀ y ∈ Y, ∀ v : ι → ℤ, ∑ i, |v i| ≤ d →
      y ≠ x + fun i => ((v i : ℤ) : ZMod L)) :
    Disjoint (growIterG torusAdj X d) Y :=
  Set.disjoint_left.2 fun z hz hzY => by
    obtain ⟨x, hx, v, hv, e⟩ := exists_int_of_mem_growIterG_torus hz
    exact h x hx z hzY v hv e

variable [Fintype S] [DecidableEq S] [NeZero L] {α : ι → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- ★★★ **The propagation bound for the lattice Dirac generator on the torus.** With
`S = −i H` for the lattice Dirac Hamiltonian in any dimension, `A` supported on the sites `X`,
`B` on the sites `Y`, and `d` steps of growth from `X` missing `Y`:
`‖[A(t), B]‖ ≤ 2 (2 ‖H‖ t)^d / d! · ‖A‖ ‖B‖` for `t ≥ 0`. -/
theorem norm_commutator_latticeDirac_le [Nonempty S] (h : IsCliffordFamily α β) (J μ : ℝ)
    {X Y : Set (ι → ZMod L)} {A B : Matrix ((ι → ZMod L) × S) ((ι → ZMod L) × S) ℂ}
    (hA : SiteSuppG Prod.fst X A) (hB : SiteSuppG Prod.fst Y B) {d : ℕ}
    (hcone : Disjoint (growIterG torusAdj X d) Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow ((-Complex.I) • latticeDiracHam (L := L) α β J μ) t A * B
        - B * heisenbergFlow ((-Complex.I) • latticeDiracHam (L := L) α β J μ) t A‖
      ≤ 2 * ((2 * ‖latticeDiracHam (L := L) α β J μ‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ := by
  have hS : ((-Complex.I) • latticeDiracHam (L := L) α β J μ)ᴴ
      = -((-Complex.I) • latticeDiracHam (L := L) α β J μ) := by
    rw [Matrix.conjTranspose_smul, (latticeDiracHam_isHermitian h J μ).eq]
    simp
  have key := norm_commutator_graph_le hS ((hopsG_latticeDiracHam α β J μ).smul _) hA hB
    hcone ht
  rwa [norm_neg_I_smul] at key

end Torus

end CSD.RecordLayer

end
