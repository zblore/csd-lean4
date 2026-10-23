/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.SignalExchange

/-!
# The scheduled chain: exact transfer along `L` sites, and clock delay against graph distance

**Category:** 3-Local (CV; the network witness of the clock-and-echo programme).
BACKLOG #190 (out of #39; the residue of #188).

A *uniform* hopping Hamiltonian on a chain does not carry an excitation perfectly from end to end
(dispersion). Exact transmission along `L = n + 1` sites needs a **sequentially activated coupling
schedule**: the hop on edge `(k, k+1)` is switched on for one hop time `τ_hop`, in order, and
nothing else is ever on. This module builds that schedule as a visible modelling input and proves
what it transmits.

* `swapSites k k'`, ★ `swapHop k k'` — **the local hop on an arbitrary edge**: the exchange
  `σ⁺_k σ⁻_{k'} + σ⁻_k σ⁺_{k'}` on every background, i.e. the swap permutation matrix with its
  diagonal removed. `swapHop_mul_swapHop` (`X² = P`, the projector on the configurations the edge
  moves), `swapHop_mul_swapProj`, `swapHop_conjTranspose`, and ★ `swapHop_supportedOn` — the hop is
  **supported on its edge**, which the two-site hop of `SignalExchange.lean` never had to show;
* `edgeFlow J ħ k k' : FieldStructuredFlow L 2` — one coupling edge carrying the hop;
  ★★ `edgeFlow_val_eq` — its flow in closed form, `1 + (cos θ − 1) P − i sin θ · X`, by the ODE
  uniqueness of `ExpUnique.lean`; `toEuclideanLin_edgeFlow_single` — on a configuration the edge
  moves, `cos θ · e_c − i sin θ · e_{swap c}`; on one it does not move, the identity;
  ★★ `edgeFlow_transfer` — at `τ_hop` the excitation at `k` is `−i` times the excitation at `k'`;
* `Schedule K N` — **the scheduled generator**: a sequence of field-structured flows, one per stage of
  duration `τ`; `Schedule.completed m` (the product of the first `m` stages, in order),
  `Schedule.propagator t` (the completed stages below `t` and the running one, from switch-on at
  `0`), `Schedule.evolve s t = propagator t · (propagator s)⁻¹` with the two-time law
  (`evolve_self`, `evolve_comp`) — **a two-parameter dynamics, not a one-parameter group**;
  `propagator_at_stage`: at `m τ` the propagator is the completed product;
* `chainSchedule n J ħ : Schedule (n+1) 2` — **the chain's schedule**: stage `m < n` is the edge flow
  on `(m, m+1)`, every later stage is off (`FieldStructuredFlow.off`); its active edges are
  visible (`chainSchedule_edges_of_lt`, `chainSchedule_edges_of_le`) and lie on the path graph;
* ★★★ `chain_transfer` — **exact transfer with the accumulated phase**: at `m τ_hop` the excitation
  prepared at site `0` is `(−i)^m` times the excitation at site `m`, for every `m ≤ n`; in particular
  it reaches the far end at `n τ_hop = (L − 1) τ_hop` with phase `(−i)^{L−1}` (`chain_transfer_last`);
  `propagator_vac` — the vacuum never moves;
* `occAt k`, `chainMsg n b`, ★★ `chainReadout_one`, `chainReadout_zero`,
  ★★★ `receiver_distinguishes_chain` — **at `k τ_hop` the readout at site `k` is `1` for message `1`
  and `0` for message `0`**, and `excitation_position`: at `m τ_hop` the excitation is sharply at
  site `m` and nowhere else;
* `pathGraph n`, ★ `mem_graphBall_pathGraph` — **the path graph's balls about site `0` are the
  initial segments**; `graphDist E R k` — the graph distance as the least radius whose ball
  contains `k`; ★★ `graphDist_pathGraph : graphDist (pathGraph n) {0} k = k`;
* ★★★ `scheduled_chain` — the package.

## Drift check

The schedule is a modelling input, exactly as the brief warned: the dynamics that transmits is the
sequence of edge flows, each a field-structured flow in the sense of `FieldStructuredFlow.lean`,
and the row's own light cone (`FieldStructuredFlow.lightcone`) applies stage by stage. Nothing here
is a record; the clocks at the sites and the comparison of their readings with the graph distance are
`RecordLayer/ChainClocks.lean`. Successful transmission is a readout at a stated time; it is not a
propagation bound.

## Honest scope

* One excitation; the message is a one-bit occupancy at site `0`; the receiver at site `k` reads
  "the excitation sits at `k`", the basis projector of `SignalExchange.lean`, which coincides with
  the local occupancy on every state this dynamics reaches from the two preparations.
* The phase `(−i)^m` is relative to the chosen basis vectors; it is a theorem about this schedule,
  not an invariant of the chain.
* `J` and `ħ` are positive reals in consistent units; no numerical value is derived from either.
* Switch-on is at `0`: before it the propagator is the identity (`propagator_of_nonpos`), the
  convention of `RecordedExchange.lean`'s `hopOn`.

References: `specs/BACKLOG.md` #190, #188, #183, #186, #39; `CV/SignalExchange.lean`,
`CV/FieldStructuredFlow.lean`, `CV/SupportSpreading.lean` (`graphBall`), `CV/TwoCones.lean`
(`exists_dist_le_of_mem_graphBall`), `Mathlib/Analysis/Normed/Algebra/ExpUnique.lean`.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {L : ℕ}

/-! ### Configurations on `L` sites -/

/-- `L` sites, occupancy `0` or `1`. -/
abbrev ChainConfig (L : ℕ) := FieldConfig L 2

/-- The vacuum. -/
def vacL (L : ℕ) : ChainConfig L := fun _ => 0

/-- One excitation at site `k`. -/
def excAt (k : Fin L) : ChainConfig L := Pi.single k 1

theorem excAt_apply_self (k : Fin L) : excAt k k = 1 := Pi.single_eq_same k 1

theorem excAt_apply_of_ne {k j : Fin L} (h : j ≠ k) : excAt k j = 0 := Pi.single_eq_of_ne h 1

theorem excAt_injective : Function.Injective (excAt (L := L)) := by
  intro k k' h
  by_contra hne
  have := congrFun h k
  rw [excAt_apply_self, excAt_apply_of_ne hne] at this
  exact absurd this (by decide)

theorem vacL_apply (k : Fin L) : vacL L k = 0 := rfl

theorem excAt_ne_vacL (k : Fin L) : excAt k ≠ vacL L := by
  intro h
  have := congrFun h k
  rw [excAt_apply_self, vacL_apply] at this
  exact absurd this (by decide)

/-- The configuration with sites `k` and `k'` exchanged. -/
def swapSites (k k' : Fin L) (c : ChainConfig L) : ChainConfig L := c ∘ Equiv.swap k k'

theorem swapSites_apply_left (k k' : Fin L) (c : ChainConfig L) : swapSites k k' c k = c k' := by
  simp [swapSites]

theorem swapSites_apply_right (k k' : Fin L) (c : ChainConfig L) : swapSites k k' c k' = c k := by
  simp [swapSites]

theorem swapSites_apply_of_ne (k k' : Fin L) (c : ChainConfig L) {j : Fin L} (hj : j ≠ k)
    (hj' : j ≠ k') : swapSites k k' c j = c j := by
  simp [swapSites, Equiv.swap_apply_of_ne_of_ne hj hj']

theorem swapSites_swapSites (k k' : Fin L) (c : ChainConfig L) :
    swapSites k k' (swapSites k k' c) = c := by
  funext j
  simp [swapSites]

theorem swapSites_ne_self {k k' : Fin L} {c : ChainConfig L} (hc : c k ≠ c k') :
    swapSites k k' c ≠ c := by
  intro h
  have := congrFun h k
  rw [swapSites_apply_left] at this
  exact hc this.symm

/-- The swapped configuration, characterised on the two sites when the spectators agree. -/
theorem eq_swapSites_iff {k k' : Fin L} {c d : ChainConfig L}
    (hoff : ∀ j, j ≠ k → j ≠ k' → c j = d j) :
    d = swapSites k k' c ↔ d k = c k' ∧ d k' = c k := by
  constructor
  · rintro rfl
    exact ⟨swapSites_apply_left _ _ _, swapSites_apply_right _ _ _⟩
  · rintro ⟨h1, h2⟩
    funext j
    by_cases hjk : j = k
    · subst hjk
      rw [swapSites_apply_left, h1]
    · by_cases hjk' : j = k'
      · subst hjk'
        rw [swapSites_apply_right, h2]
      · rw [swapSites_apply_of_ne _ _ _ hjk hjk', hoff j hjk hjk']

/-- The hop's defining condition is symmetric in its two configurations. -/
theorem swap_cond_symm {k k' : Fin L} {c d : ChainConfig L}
    (h : c = swapSites k k' d ∧ d k ≠ d k') : d = swapSites k k' c ∧ c k ≠ c k' := by
  obtain ⟨rfl, h⟩ := h
  refine ⟨(swapSites_swapSites k k' d).symm, ?_⟩
  rw [swapSites_apply_left, swapSites_apply_right]
  exact h.symm

theorem swapSites_excAt (k k' : Fin L) : swapSites k k' (excAt k) = excAt k' := by
  funext j
  simp only [swapSites, Function.comp_apply, excAt, Pi.single_apply, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left]

/-! ### The hop on an edge, and the projector on what it moves -/

/-- ★ **The local hop on the edge `(k, k')`**: `σ⁺_k σ⁻_{k'} + σ⁻_k σ⁺_{k'}` on every background —
the swap permutation matrix with its diagonal removed. -/
noncomputable def swapHop (k k' : Fin L) : Matrix (ChainConfig L) (ChainConfig L) ℂ :=
  Matrix.of fun c d => if d = swapSites k k' c ∧ c k ≠ c k' then 1 else 0

/-- The projector on the configurations the edge moves. -/
noncomputable def swapProj (k k' : Fin L) : Matrix (ChainConfig L) (ChainConfig L) ℂ :=
  Matrix.diagonal fun c => if c k ≠ c k' then 1 else 0

theorem swapHop_apply (k k' : Fin L) (c d : ChainConfig L) :
    swapHop k k' c d = if d = swapSites k k' c ∧ c k ≠ c k' then 1 else 0 := rfl

/-- The hop's entries read the same from either side. -/
theorem swapHop_apply_symm (k k' : Fin L) (c d : ChainConfig L) :
    swapHop k k' d c = if d = swapSites k k' c ∧ c k ≠ c k' then 1 else 0 := by
  rw [swapHop_apply]
  exact if_congr ⟨swap_cond_symm, swap_cond_symm⟩ rfl rfl

theorem swapHop_mul_swapHop (k k' : Fin L) : swapHop k k' * swapHop k k' = swapProj k k' := by
  ext c d
  rw [Matrix.mul_apply, Finset.sum_eq_single (swapSites k k' c)]
  · rw [swapHop_apply, swapHop_apply, swapProj, Matrix.diagonal_apply, swapSites_swapSites,
      swapSites_apply_left, swapSites_apply_right]
    by_cases hcd : d = c
    · rw [hcd]
      by_cases hk : c k = c k'
      · simp [hk]
      · simp [hk, Ne.symm hk]
    · simp [hcd, Ne.symm hcd]
  · intro e _ he
    rw [swapHop_apply k k' c e, ite_eq_right (fun h => he h.1), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem swapHop_mul_swapProj (k k' : Fin L) : swapHop k k' * swapProj k k' = swapHop k k' := by
  ext c d
  rw [swapProj, Matrix.mul_diagonal, swapHop_apply]
  by_cases h : d = swapSites k k' c ∧ c k ≠ c k'
  · rw [ite_eq_left h, one_mul, h.1, swapSites_apply_left, swapSites_apply_right]
    simp [Ne.symm h.2]
  · rw [ite_eq_right h, zero_mul]

theorem swapHop_conjTranspose (k k' : Fin L) : (swapHop k k')ᴴ = swapHop k k' := by
  ext c d
  rw [Matrix.conjTranspose_apply, swapHop_apply_symm, swapHop_apply]
  split_ifs <;> simp

/-- ★ **The hop is supported on its edge**: it does not move the spectators, and its entries do not
depend on them. -/
theorem swapHop_supportedOn (k k' : Fin L) : SupportedOn {k, k'} (swapHop k k') where
  offDiag := by
    intro c d j hj hcd
    have hjk : j ≠ k ∧ j ≠ k' := by
      simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
    rw [swapHop_apply]
    refine ite_eq_right ?_
    rintro ⟨rfl, -⟩
    exact hcd (swapSites_apply_of_ne k k' c hjk.1 hjk.2).symm
  indep := by
    intro c d c' d' hS hS' hoff hoff'
    have hk : k ∈ ({k, k'} : Finset (Fin L)) := Finset.mem_insert_self k _
    have hk' : k' ∈ ({k, k'} : Finset (Fin L)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self k')
    have hoffS : ∀ j, j ≠ k → j ≠ k' → c j = d j := fun j hj hj' =>
      hoff j (by simp [Finset.mem_insert, Finset.mem_singleton, hj, hj'])
    have hoffS' : ∀ j, j ≠ k → j ≠ k' → c' j = d' j := fun j hj hj' =>
      hoff' j (by simp [Finset.mem_insert, Finset.mem_singleton, hj, hj'])
    rw [swapHop_apply, swapHop_apply]
    refine if_congr ?_ rfl rfl
    rw [eq_swapSites_iff hoffS, eq_swapSites_iff hoffS', hS k hk, hS k' hk', hS' k hk, hS' k' hk']

/-! ### The edge flow -/

/-- The Schrödinger generator `−(i J/ħ) X` of the hop on the edge `(k, k')`. -/
noncomputable def chainGen (J ħ : ℝ) (k k' : Fin L) : Matrix (ChainConfig L) (ChainConfig L) ℂ :=
  (-(Complex.I * ((J / ħ : ℝ) : ℂ))) • swapHop k k'

theorem chainGen_skew (J ħ : ℝ) (k k' : Fin L) : (chainGen J ħ k k')ᴴ = -(chainGen J ħ k k') :=
  skew_neg_I_smul_of_hermitian (J / ħ) (swapHop_conjTranspose k k')

/-- The field-structured flow with the one coupling edge `(k, k')` carrying the hop. -/
noncomputable def edgeFlow (J ħ : ℝ) (k k' : Fin L) : FieldStructuredFlow L 2 where
  edges := {(k, k')}
  piece := fun _ => chainGen J ħ k k'
  piece_supported := by
    intro e he
    rw [Finset.mem_singleton] at he
    subst he
    exact SupportedOn.smul _ (swapHop_supportedOn k k')
  gen_skew := by
    rw [Finset.sum_singleton]
    exact chainGen_skew J ħ k k'

theorem edgeFlow_edges (J ħ : ℝ) (k k' : Fin L) : (edgeFlow J ħ k k').edges = {(k, k')} := rfl

theorem edgeFlow_val (J ħ : ℝ) (k k' : Fin L) (t : ℝ) :
    ((edgeFlow J ħ k k').flow t).val = exp (t • chainGen J ħ k k') := by
  simp only [FieldStructuredFlow.flow_val, edgeFlow, Finset.sum_singleton]

theorem smul_chainGen (J ħ : ℝ) (k k' : Fin L) (t : ℝ) :
    t • chainGen J ħ k k' = (((-hopAngle J ħ t : ℝ) : ℂ) * Complex.I) • swapHop k k' := by
  rw [chainGen, matrix_real_smul, smul_smul, hopAngle]
  congr 1
  push_cast
  ring

/-- ★★ **The edge flow in closed form**: `U(t) = 1 + (cos θ − 1) P − i sin θ · X`. -/
theorem edgeFlow_val_eq (J ħ : ℝ) (k k' : Fin L) (t : ℝ) :
    ((edgeFlow J ħ k k').flow t).val
      = 1 + ((Real.cos (hopAngle J ħ t) - 1 : ℝ) : ℂ) • swapProj k k'
          + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • swapHop k k' := by
  rw [edgeFlow_val, smul_chainGen, exp_smul_eq_cosh_sinh (swapHop_mul_swapHop k k')
    (swapHop_mul_swapProj k k')]
  have hc : Complex.cosh (((-hopAngle J ħ t : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (hopAngle J ħ t) - 1 : ℝ) : ℂ) + 1 := by
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_neg]
    push_cast
    ring
  have hs : Complex.sinh (((-hopAngle J ħ t : ℝ) : ℂ) * Complex.I)
      = -(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ)) := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_neg]
    push_cast
    ring
  rw [hc, hs, add_sub_cancel_right]

/-- On a configuration the edge moves, the flow produces `cos θ · e_c − i sin θ · e_{swap c}`. -/
theorem edgeFlow_mulVec_single (J ħ : ℝ) {k k' : Fin L} {c : ChainConfig L} (hc : c k ≠ c k')
    (t : ℝ) :
    ((edgeFlow J ħ k k').flow t).val *ᵥ Pi.single c (1 : ℂ)
      = ((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • Pi.single c (1 : ℂ)
          + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • Pi.single (swapSites k k' c) (1 : ℂ) := by
  rw [mulVec_single_one, edgeFlow_val_eq]
  funext d
  simp only [Matrix.col, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, swapProj, Matrix.diagonal_apply, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  rw [swapHop_apply_symm]
  by_cases hd : d = c
  · subst hd
    simp [hc]
  · simp [hd, hc]

/-- On a configuration the edge does not move, the flow is the identity. -/
theorem edgeFlow_mulVec_single_of_eq (J ħ : ℝ) {k k' : Fin L} {c : ChainConfig L} (hc : c k = c k')
    (t : ℝ) :
    ((edgeFlow J ħ k k').flow t).val *ᵥ Pi.single c (1 : ℂ) = Pi.single c (1 : ℂ) := by
  rw [mulVec_single_one, edgeFlow_val_eq]
  funext d
  simp only [Matrix.col, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, swapProj, Matrix.diagonal_apply, Pi.single_apply, smul_eq_mul]
  rw [swapHop_apply_symm]
  by_cases hd : d = c
  · subst hd
    simp [hc]
  · simp [hd, hc]

/-! ### Euclidean form -/

/-- The basis vector of a configuration. -/
noncomputable def eVec (c : ChainConfig L) : EuclideanSpace ℂ (ChainConfig L) :=
  PiLp.single 2 c (1 : ℂ)

theorem eVec_apply (c d : ChainConfig L) : eVec c d = (Pi.single c (1 : ℂ) : ChainConfig L → ℂ) d :=
  rfl

theorem eVec_apply_self (c : ChainConfig L) : eVec c c = 1 := by
  rw [eVec_apply, Pi.single_eq_same]

theorem eVec_apply_of_ne {c d : ChainConfig L} (h : d ≠ c) : eVec c d = 0 := by
  rw [eVec_apply, Pi.single_eq_of_ne h]

theorem norm_eVec (c : ChainConfig L) : ‖eVec c‖ = 1 := by
  rw [eVec, PiLp.norm_single, norm_one]

theorem eVec_ne_zero (c : ChainConfig L) : eVec c ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [norm_eVec, norm_zero] at this
  exact one_ne_zero this

theorem toEuclideanLin_mul_apply (A B : Matrix (ChainConfig L) (ChainConfig L) ℂ)
    (v : EuclideanSpace ℂ (ChainConfig L)) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) :=
  DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 A B) v

theorem toEuclideanLin_one_apply (v : EuclideanSpace ℂ (ChainConfig L)) :
    Matrix.toEuclideanLin (1 : Matrix (ChainConfig L) (ChainConfig L) ℂ) v = v := by
  ext d
  rw [toEuclideanLin_coord, Matrix.one_mulVec]

theorem toEuclideanLin_edgeFlow_single (J ħ : ℝ) {k k' : Fin L} {c : ChainConfig L}
    (hc : c k ≠ c k') (t : ℝ) :
    Matrix.toEuclideanLin ((edgeFlow J ħ k k').flow t).val (eVec c)
      = ((Real.cos (hopAngle J ħ t) : ℝ) : ℂ) • eVec c
          + (-(Complex.I * (Real.sin (hopAngle J ħ t) : ℂ))) • eVec (swapSites k k' c) := by
  ext d
  rw [toEuclideanLin_coord]
  have hfun : (fun j => eVec c j) = Pi.single c (1 : ℂ) := funext fun j => rfl
  rw [hfun, edgeFlow_mulVec_single J ħ hc]
  simp only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, eVec_apply]

theorem toEuclideanLin_edgeFlow_single_of_eq (J ħ : ℝ) {k k' : Fin L} {c : ChainConfig L}
    (hc : c k = c k') (t : ℝ) :
    Matrix.toEuclideanLin ((edgeFlow J ħ k k').flow t).val (eVec c) = eVec c := by
  ext d
  rw [toEuclideanLin_coord]
  have hfun : (fun j => eVec c j) = Pi.single c (1 : ℂ) := funext fun j => rfl
  rw [hfun, edgeFlow_mulVec_single_of_eq J ħ hc, eVec_apply]

/-- ★★ **One stage transfers exactly, with phase `−i`**: at `τ_hop` the excitation at `k` has become
`−i` times the excitation at `k'`. -/
theorem edgeFlow_transfer {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L} (h : k ≠ k') :
    Matrix.toEuclideanLin ((edgeFlow J ħ k k').flow (hopTime J ħ)).val (eVec (excAt k))
      = (-Complex.I) • eVec (excAt k') := by
  have hc : excAt k k ≠ excAt k k' := by
    rw [excAt_apply_self, excAt_apply_of_ne (Ne.symm h)]
    decide
  rw [toEuclideanLin_edgeFlow_single J ħ hc, hopAngle_hopTime hJ.ne' hħ.ne', Real.cos_pi_div_two,
    Real.sin_pi_div_two, swapSites_excAt k k']
  simp

theorem edgeFlow_vac (J ħ : ℝ) (k k' : Fin L) (t : ℝ) :
    Matrix.toEuclideanLin ((edgeFlow J ħ k k').flow t).val (eVec (vacL L)) = eVec (vacL L) := by
  apply toEuclideanLin_edgeFlow_single_of_eq
  rfl

/-! ### The scheduled generator -/

namespace FieldStructuredFlow

variable {K N : ℕ}

/-- The flow with nothing switched on. -/
def off (K N : ℕ) : FieldStructuredFlow K N where
  edges := ∅
  piece := fun _ => 0
  piece_supported := fun e he => absurd he (Finset.notMem_empty e)
  gen_skew := by rw [Finset.sum_empty, Matrix.conjTranspose_zero, neg_zero]

theorem flow_zero (F : FieldStructuredFlow K N) : F.flow 0 = 1 := by
  apply Subtype.ext
  rw [flow_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem off_flow (t : ℝ) : (off K N).flow t = 1 := by
  apply Subtype.ext
  rw [flow_val]
  simp only [off, Finset.sum_empty, smul_zero, NormedSpace.exp_zero]
  rfl

end FieldStructuredFlow

/-- **A coupling schedule**: a sequence of field-structured flows, stage `m` switched on for the
duration `τ` after the first `m` stages. The scheduled generator is piecewise in time — a modelling
input, stated as data. -/
structure Schedule (K N : ℕ) where
  /-- The field-structured flow switched on during stage `m`. -/
  stage : ℕ → FieldStructuredFlow K N
  /-- The duration of each stage. -/
  τ : ℝ

namespace Schedule

variable {K N : ℕ}

/-- The product of the first `m` completed stages, in order: `U_{m−1}(τ) ⋯ U_0(τ)`. -/
noncomputable def completed (s : Schedule K N) : ℕ → Matrix.unitaryGroup (FieldConfig K N) ℂ
  | 0 => 1
  | m + 1 => (s.stage m).flow s.τ * completed s m

variable (s : Schedule K N)

@[simp] theorem completed_zero : s.completed 0 = 1 := by rw [completed]

theorem completed_succ (m : ℕ) : s.completed (m + 1) = (s.stage m).flow s.τ * s.completed m := by
  rw [completed]

/-- The propagator from switch-on at `0`: the completed stages below `t` and the running stage for
the remaining time. Before switch-on it is the identity. -/
noncomputable def propagator (t : ℝ) : Matrix.unitaryGroup (FieldConfig K N) ℂ :=
  (s.stage ⌊max t 0 / s.τ⌋₊).flow (max t 0 - ⌊max t 0 / s.τ⌋₊ * s.τ) * s.completed ⌊max t 0 / s.τ⌋₊

/-- The two-time propagator from `a` to `b`. -/
noncomputable def evolve (a b : ℝ) : Matrix.unitaryGroup (FieldConfig K N) ℂ :=
  s.propagator b * (s.propagator a)⁻¹

theorem evolve_self (t : ℝ) : s.evolve t t = 1 := mul_inv_cancel _

/-- ★ **The two-time composition law** of the scheduled dynamics. -/
theorem evolve_comp (a b c : ℝ) : s.evolve b c * s.evolve a b = s.evolve a c := by
  rw [evolve, evolve, evolve, mul_assoc, inv_mul_cancel_left]

theorem propagator_of_nonpos {t : ℝ} (ht : t ≤ 0) : s.propagator t = 1 := by
  rw [propagator, max_eq_right ht]
  simp only [zero_div, Nat.floor_zero, Nat.cast_zero, zero_mul, sub_zero,
    FieldStructuredFlow.flow_zero, completed_zero, one_mul]

theorem evolve_zero (t : ℝ) : s.evolve 0 t = s.propagator t := by
  rw [evolve, propagator_of_nonpos s le_rfl, inv_one, mul_one]

/-- **At the stage boundary `m τ` the propagator is the completed product.** -/
theorem propagator_at_stage (hτ : 0 < s.τ) (m : ℕ) : s.propagator (m * s.τ) = s.completed m := by
  have hm : (0 : ℝ) ≤ m * s.τ := by positivity
  rw [propagator, max_eq_left hm, mul_div_assoc, div_self hτ.ne', mul_one, Nat.floor_natCast,
    sub_self, FieldStructuredFlow.flow_zero, one_mul]

end Schedule

/-! ### The chain's schedule -/

variable {n : ℕ}

/-- **The chain's schedule** on `n + 1` sites: stage `m < n` is the edge flow on `(m, m+1)`; every
later stage is off. -/
noncomputable def chainSchedule (n : ℕ) (J ħ : ℝ) : Schedule (n + 1) 2 where
  stage := fun m =>
    if h : m < n then edgeFlow J ħ (Fin.castSucc ⟨m, h⟩) (Fin.succ ⟨m, h⟩)
    else FieldStructuredFlow.off (n + 1) 2
  τ := hopTime J ħ

theorem chainSchedule_τ (J ħ : ℝ) : (chainSchedule n J ħ).τ = hopTime J ħ := rfl

theorem chainSchedule_stage_of_lt (J ħ : ℝ) {m : ℕ} (h : m < n) :
    (chainSchedule n J ħ).stage m = edgeFlow J ħ (Fin.castSucc ⟨m, h⟩) (Fin.succ ⟨m, h⟩) := by
  simp [chainSchedule, h]

theorem chainSchedule_stage_of_le (J ħ : ℝ) {m : ℕ} (h : n ≤ m) :
    (chainSchedule n J ħ).stage m = FieldStructuredFlow.off (n + 1) 2 := by
  simp [chainSchedule, not_lt.mpr h]

/-- **The active edges are visible**: during stage `m < n` exactly the edge `(m, m+1)` is on. -/
theorem chainSchedule_edges_of_lt (J ħ : ℝ) {m : ℕ} (h : m < n) :
    ((chainSchedule n J ħ).stage m).edges = {(Fin.castSucc ⟨m, h⟩, Fin.succ ⟨m, h⟩)} := by
  rw [chainSchedule_stage_of_lt J ħ h, edgeFlow_edges]

/-- After the last stage nothing is on. -/
theorem chainSchedule_edges_of_le (J ħ : ℝ) {m : ℕ} (h : n ≤ m) :
    ((chainSchedule n J ħ).stage m).edges = ∅ := by
  rw [chainSchedule_stage_of_le J ħ h]
  rfl

/-- ★★★ **Exact transfer with the accumulated phase**: after `m ≤ n` completed stages the excitation
prepared at site `0` is `(−i)^m` times the excitation at site `m`. -/
theorem chain_transfer_completed {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    ∀ m (hm : m ≤ n),
      Matrix.toEuclideanLin ((chainSchedule n J ħ).completed m).val (eVec (excAt 0))
        = (-Complex.I) ^ m • eVec (excAt ⟨m, Nat.lt_succ_of_le hm⟩) := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [Schedule.completed_zero, OneMemClass.coe_one, toEuclideanLin_one_apply, pow_zero,
        one_smul]
      rfl
  | succ m ih =>
      intro hm
      have hlt : m < n := hm
      have hcast : (⟨m, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩ : Fin (n + 1))
          = Fin.castSucc ⟨m, hlt⟩ := rfl
      rw [Schedule.completed_succ, Submonoid.coe_mul, toEuclideanLin_mul_apply,
        ih (Nat.le_of_lt hlt), map_smul, chainSchedule_stage_of_lt J ħ hlt, chainSchedule_τ, hcast,
        edgeFlow_transfer hJ hħ Fin.castSucc_lt_succ.ne, smul_smul, ← pow_succ]
      rfl

/-- ★★★ **Exact transfer along the chain**: at `m τ_hop` (`m ≤ n`) the propagator carries the
excitation at site `0` to `(−i)^m` times the excitation at site `m`. -/
theorem chain_transfer {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {m : ℕ} (hm : m ≤ n) :
    Matrix.toEuclideanLin ((chainSchedule n J ħ).propagator (m * hopTime J ħ)).val (eVec (excAt 0))
      = (-Complex.I) ^ m • eVec (excAt ⟨m, Nat.lt_succ_of_le hm⟩) := by
  have h := Schedule.propagator_at_stage (chainSchedule n J ħ) (hopTime_pos hJ hħ) m
  rw [chainSchedule_τ] at h
  rw [h, chain_transfer_completed hJ hħ m hm]

/-- **The far end**: in `n τ_hop = (L − 1) τ_hop` the excitation reaches the last site with phase
`(−i)^{L−1}`. -/
theorem chain_transfer_last {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    Matrix.toEuclideanLin ((chainSchedule n J ħ).propagator (n * hopTime J ħ)).val (eVec (excAt 0))
      = (-Complex.I) ^ n • eVec (excAt (Fin.last n)) :=
  chain_transfer hJ hħ le_rfl

/-- The vacuum never moves, at any time. -/
theorem propagator_vac (J ħ t : ℝ) :
    Matrix.toEuclideanLin ((chainSchedule n J ħ).propagator t).val (eVec (vacL (n + 1)))
      = eVec (vacL (n + 1)) := by
  have hstage : ∀ (m : ℕ) (r : ℝ),
      Matrix.toEuclideanLin (((chainSchedule n J ħ).stage m).flow r).val (eVec (vacL (n + 1)))
        = eVec (vacL (n + 1)) := by
    intro m r
    by_cases h : m < n
    · rw [chainSchedule_stage_of_lt J ħ h, edgeFlow_vac]
    · rw [chainSchedule_stage_of_le J ħ (not_lt.mp h), FieldStructuredFlow.off_flow,
        OneMemClass.coe_one, toEuclideanLin_one_apply]
  have hcompl : ∀ m : ℕ,
      Matrix.toEuclideanLin ((chainSchedule n J ħ).completed m).val (eVec (vacL (n + 1)))
        = eVec (vacL (n + 1)) := by
    intro m
    induction m with
    | zero => rw [Schedule.completed_zero, OneMemClass.coe_one, toEuclideanLin_one_apply]
    | succ m ih => rw [Schedule.completed_succ, Submonoid.coe_mul, toEuclideanLin_mul_apply, ih, hstage]
  rw [Schedule.propagator, Submonoid.coe_mul, toEuclideanLin_mul_apply, hcompl, hstage]

/-! ### Arena points and the receivers' readouts -/

/-- The receiver at site `k` reads "the excitation sits at `k`". -/
noncomputable def occAt (k : Fin L) : Matrix (ChainConfig L) (ChainConfig L) ℂ :=
  single (excAt k) (excAt k) 1

/-- The sender's message `b` is the occupancy of site `0`; every other site is empty. -/
def chainMsgConfig (n : ℕ) : Fin 2 → ChainConfig (n + 1) := ![vacL (n + 1), excAt 0]

theorem chainMsgConfig_zero : chainMsgConfig n 0 = vacL (n + 1) := rfl

theorem chainMsgConfig_one : chainMsgConfig n 1 = excAt 0 := rfl

/-- The two preparations agree away from site `0`. -/
theorem chainMsgConfig_apply_of_ne (b : Fin 2) {j : Fin (n + 1)} (hj : j ≠ 0) :
    chainMsgConfig n b j = 0 := by
  fin_cases b
  · rfl
  · show excAt 0 j = 0
    exact excAt_apply_of_ne hj

/-- The arena point of message `b`. -/
noncomputable def chainMsg (n : ℕ) (b : Fin 2) : FieldArena (n + 1) 2 :=
  Projectivization.mk ℂ (eVec (chainMsgConfig n b)) (eVec_ne_zero _)

theorem chainMsg_zero :
    chainMsg n 0 = Projectivization.mk ℂ (eVec (vacL (n + 1))) (eVec_ne_zero _) := rfl

theorem chainMsg_one : chainMsg n 1 = Projectivization.mk ℂ (eVec (excAt 0)) (eVec_ne_zero _) := rfl

/-- The scheduled flow on the arena, from switch-on. -/
noncomputable def chainArenaFlow (J ħ t : ℝ) (p : FieldArena (n + 1) 2) : FieldArena (n + 1) 2 :=
  arenaKick ((chainSchedule n J ħ).propagator t) p

theorem norm_pow_neg_I_smul_eVec (m : ℕ) (c : ChainConfig L) :
    ‖(-Complex.I) ^ m • eVec c‖ = 1 := by
  rw [norm_smul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul, norm_eVec]

/-- **The receiver at `k` for message `1`, at the stage boundary `m τ_hop`**: `1` if `k = m`, `0`
otherwise — the excitation is sharply at site `m`. -/
theorem chainReadout_one {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {m : ℕ} (hm : m ≤ n)
    (k : Fin (n + 1)) :
    arenaObs (occAt k) (chainArenaFlow J ħ (m * hopTime J ħ) (chainMsg n 1))
      = if k = ⟨m, Nat.lt_succ_of_le hm⟩ then 1 else 0 := by
  rw [chainArenaFlow, chainMsg_one, arenaKick_mk, occAt, arenaObs_single_mk,
    chain_transfer hJ hħ hm, norm_pow_neg_I_smul_eVec, one_pow, div_one, PiLp.smul_apply,
    smul_eq_mul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  by_cases hk : k = ⟨m, Nat.lt_succ_of_le hm⟩
  · rw [hk, eVec_apply_self, norm_one, one_pow, ite_eq_left rfl]
  · rw [eVec_apply_of_ne (fun h => hk (excAt_injective h)), norm_zero, ite_eq_right hk]
    norm_num

/-- **The receiver at `k` for message `0` is `0` at every time**: the vacuum does not move. -/
theorem chainReadout_zero (J ħ t : ℝ) (k : Fin (n + 1)) :
    arenaObs (occAt k) (chainArenaFlow J ħ t (chainMsg n 0)) = 0 := by
  rw [chainArenaFlow, chainMsg_zero, arenaKick_mk, occAt, arenaObs_single_mk,
    propagator_vac, eVec_apply_of_ne (excAt_ne_vacL k), norm_zero]
  simp

/-- ★★★ **At `k τ_hop` the receiver at site `k` reads `1` for message `1` and `0` for message `0`.** -/
theorem receiver_distinguishes_chain {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (k : Fin (n + 1)) :
    arenaObs (occAt k) (chainArenaFlow J ħ ((k : ℕ) * hopTime J ħ) (chainMsg n 1)) = 1
      ∧ arenaObs (occAt k) (chainArenaFlow J ħ ((k : ℕ) * hopTime J ħ) (chainMsg n 0)) = 0 := by
  refine ⟨?_, chainReadout_zero J ħ _ k⟩
  rw [chainReadout_one hJ hħ (Nat.le_of_lt_succ k.isLt) k, ite_eq_left (Fin.ext rfl)]

/-- **The excitation's position**: at `m τ_hop` the readout at any other site is `0`. -/
theorem excitation_position {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {m : ℕ} (hm : m ≤ n)
    {k : Fin (n + 1)} (hk : k ≠ ⟨m, Nat.lt_succ_of_le hm⟩) :
    arenaObs (occAt k) (chainArenaFlow J ħ (m * hopTime J ħ) (chainMsg n 1)) = 0 := by
  rw [chainReadout_one hJ hħ hm k, ite_eq_right hk]

/-! ### The path graph and the graph distance -/

/-- The path graph on `n + 1` sites: the edges `(k, k+1)`. -/
def pathGraph (n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.image fun k : Fin n => (Fin.castSucc k, Fin.succ k)

theorem mem_pathGraph {e : Fin (n + 1) × Fin (n + 1)} :
    e ∈ pathGraph n ↔ ∃ k : Fin n, e = (Fin.castSucc k, Fin.succ k) := by
  simp only [pathGraph, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The schedule's active edges all lie on the path graph. -/
theorem chainSchedule_edges_subset (J ħ : ℝ) (m : ℕ) :
    ((chainSchedule n J ħ).stage m).edges ⊆ pathGraph n := by
  by_cases h : m < n
  · rw [chainSchedule_edges_of_lt J ħ h]
    intro e he
    rw [Finset.mem_singleton] at he
    exact mem_pathGraph.mpr ⟨⟨m, h⟩, he⟩
  · rw [chainSchedule_edges_of_le J ħ (not_lt.mp h)]
    exact Finset.empty_subset _

/-- The path graph on two sites is the hop graph of the two-site exchange. -/
theorem pathGraph_one : pathGraph 1 = {((0 : Fin 2), (1 : Fin 2))} := by decide

/-- ★ **The path graph's balls about site `0` are the initial segments.** -/
theorem mem_graphBall_pathGraph (d : ℕ) (j : Fin (n + 1)) :
    j ∈ graphBall (pathGraph n) {0} d ↔ j.val ≤ d := by
  induction d generalizing j with
  | zero =>
      rw [graphBall_zero, Finset.mem_singleton, Nat.le_zero, Fin.ext_iff, Fin.val_zero]
  | succ d ih =>
      rw [graphBall_succ, graphNeighborhood, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro (hj | ⟨e, he, hje⟩)
        · exact Nat.le_succ_of_le ((ih j).mp hj)
        · rw [Finset.mem_filter, mem_pathGraph] at he
          obtain ⟨⟨k, rfl⟩, hk⟩ := he
          rw [ih, ih, Fin.val_castSucc, Fin.val_succ] at hk
          rw [Finset.mem_insert, Finset.mem_singleton] at hje
          rcases hje with rfl | rfl
          · rw [Fin.val_castSucc]
            omega
          · rw [Fin.val_succ]
            omega
      · intro hj
        rcases Nat.lt_or_ge j.val (d + 1) with hlt | hge
        · exact Or.inl ((ih j).mpr (Nat.le_of_lt_succ hlt))
        · have hjd : j.val = d + 1 := le_antisymm hj hge
          have hdn : d < n := by omega
          refine Or.inr ⟨(Fin.castSucc ⟨d, hdn⟩, Fin.succ ⟨d, hdn⟩), ?_, ?_⟩
          · rw [Finset.mem_filter, mem_pathGraph]
            exact ⟨⟨⟨d, hdn⟩, rfl⟩, Or.inl ((ih _).mpr (le_of_eq (Fin.val_castSucc _)))⟩
          · rw [Finset.mem_insert, Finset.mem_singleton]
            exact Or.inr (Fin.ext hjd)

/-- **The graph distance** from a region to a site: the least radius whose graph ball contains it. -/
noncomputable def graphDist {K : ℕ} (E : Finset (Fin K × Fin K)) (R : Finset (Fin K)) (k : Fin K) :
    ℕ :=
  sInf {d | k ∈ graphBall E R d}

theorem graphDist_le_of_mem {K : ℕ} {E : Finset (Fin K × Fin K)} {R : Finset (Fin K)} {k : Fin K}
    {d : ℕ} (h : k ∈ graphBall E R d) : graphDist E R k ≤ d :=
  Nat.sInf_le h

theorem le_graphDist {K : ℕ} {E : Finset (Fin K × Fin K)} {R : Finset (Fin K)} {k : Fin K} {d : ℕ}
    (hne : ∃ d', k ∈ graphBall E R d') (h : ∀ d', k ∈ graphBall E R d' → d ≤ d') :
    d ≤ graphDist E R k :=
  le_csInf hne h

/-- ★★ **On the path graph the graph distance from site `0` to site `k` is `k`.** -/
theorem graphDist_pathGraph (k : Fin (n + 1)) : graphDist (pathGraph n) {0} k = k.val := by
  apply le_antisymm
  · exact graphDist_le_of_mem ((mem_graphBall_pathGraph k.val k).mpr le_rfl)
  · exact le_graphDist ⟨k.val, (mem_graphBall_pathGraph k.val k).mpr le_rfl⟩
      fun d hd => (mem_graphBall_pathGraph d k).mp hd

/-! ### The package -/

/-- ★★★ **The scheduled chain.** The schedule's active edges are visible and lie on the path graph;
the two-time law holds; at `m τ_hop` the excitation prepared at site `0` is `(−i)^m` times the
excitation at site `m`; at `k τ_hop` the receiver at `k` reads `1` for message `1` and `0` for
message `0`; and the graph distance from site `0` to site `k` is `k`. -/
theorem scheduled_chain {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (∀ m (h : m < n),
        ((chainSchedule n J ħ).stage m).edges = {(Fin.castSucc ⟨m, h⟩, Fin.succ ⟨m, h⟩)})
      ∧ (∀ m, n ≤ m → ((chainSchedule n J ħ).stage m).edges = ∅)
      ∧ (∀ a b c : ℝ, (chainSchedule n J ħ).evolve b c * (chainSchedule n J ħ).evolve a b
          = (chainSchedule n J ħ).evolve a c)
      ∧ (∀ m (hm : m ≤ n),
          Matrix.toEuclideanLin ((chainSchedule n J ħ).propagator (m * hopTime J ħ)).val
              (eVec (excAt 0))
            = (-Complex.I) ^ m • eVec (excAt ⟨m, Nat.lt_succ_of_le hm⟩))
      ∧ (∀ k : Fin (n + 1),
          arenaObs (occAt k) (chainArenaFlow J ħ ((k : ℕ) * hopTime J ħ) (chainMsg n 1)) = 1
            ∧ arenaObs (occAt k) (chainArenaFlow J ħ ((k : ℕ) * hopTime J ħ) (chainMsg n 0)) = 0)
      ∧ (∀ k : Fin (n + 1), graphDist (pathGraph n) {0} k = k.val) :=
  ⟨fun _ h => chainSchedule_edges_of_lt J ħ h, fun _ h => chainSchedule_edges_of_le J ħ h,
    fun _ _ _ => Schedule.evolve_comp _ _ _ _, fun _ hm => chain_transfer hJ hħ hm,
    fun k => receiver_distinguishes_chain hJ hħ k, graphDist_pathGraph⟩

end CSD.CV

end
