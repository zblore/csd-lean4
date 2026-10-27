/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ConeComparison

/-!
# A local Lieb–Robinson velocity

**Category:** 3-Local (CV; continuous variables — a Lieb–Robinson velocity from the local terms).
BACKLOG #213, the residue of #205's first brick.

`lrVelocity F = 4e‖Σ_e h_e‖` ([`TwoCones.lean`](TwoCones.lean)) is read off
`norm_commutator_spatial_factorial_le` ([`LiebRobinson.lean`](LiebRobinson.lean)), whose Taylor
remainder is priced by the norm of the *whole* generator. On a chain of `n` edges that slope is
between `n/2` and `n` times a single stage's (`pathFlow_lrVelocity_mul_hopTime_bounds`,
[`ConeComparison.lean`](ConeComparison.lean)), so the cone it bounds grows with the system.
This file proves the bound in its standard local form, with a velocity built from the largest
edge term and the graph's degree.

## What is proved

* `edgesTouching E Y`, `DegreeLE E Δ` (every site an end of at most `Δ` edges),
  `card_edgesTouching_le` (at most `Δ · |Y|` edges touch `Y`), and
  `disjoint_edge_of_mem_edgesTouching` (one step back along an edge loses one radius of the ball);
* ★★ `norm_commutator_step_le` — **one step of the iteration**: split the generator into the terms
  touching the probe's region and the rest; the rest commutes with the probe and only conjugates
  (`hasDerivAt_conjComm`), so the commutator grows at most like any comparison function `Φ` with
  `Φ' ≥ 2‖B‖ · #(touching) · φ`, where `φ` bounds each touching term's commutator
  (`image_norm_le_of_norm_deriv_right_le_deriv_boundary`);
* ★★★ `norm_commutator_local_le` — **the local Lieb–Robinson bound**: for edge-supported,
  individually skew-Hermitian terms of norm at most `γ` on a graph of degree at most `Δ`,
  `‖[A(t), B]‖ ≤ 2‖A‖‖B‖ · max(|Y|, 1) · (4Δγt)^d / d!` whenever the `d`-ball around `A`'s region
  misses `B`'s. By induction on `d`, the probe at each step replaced by the edge terms touching it;
* `localLRVelocity Δ γ = 8eΔγ` and ★★ `localRate_pow_div_factorial_le`: outside
  `localLRVelocity Δ γ · t ≤ d` the bound is at most `2^{-d}` (`lr_bound_le_half_pow`);
* ★ `arenaObs_kick_sub_le_commutator` (the arena half of `arena_lightcone`, for any commutator
  bound), ★★★ `lightcone_local`, ★★★ `record_lightcone_local` and ★★★
  `record_influence_le_of_separated_local` — `FieldStructuredFlow.lightcone`, `record_lightcone`
  and `record_influence_le_of_separated` re-derived at the local rate;
* on the chain: `degreeLE_pathGraph` (degree `2`), ★★★ `norm_commutator_pathFlow_le` (the whole
  chain at once, at rate `8|J/ħ|`), ★★★ `localLRVelocity_chain_mul_hopTime`
  (`v_loc · τ_hop = 8πe = 4 · 2πe` **for every length**) and ★★★
  `localLRVelocity_lt_lrVelocity_pathFlow` (beyond eight edges the local velocity is strictly the
  smaller, and the gap grows with `n`);
* ★★★ `local_lieb_robinson` — the capstone.

## Honest scope

⚠️ **Each edge term must be skew-Hermitian on its own.** `FieldStructuredFlow` asks only that the
assembled generator be skew; the iteration conjugates by the part of the generator away from the
probe, which needs that part skew. Every flow in the corpus that this file is applied to
(`edgeFlow`, `pathFlow`) satisfies it, and the theorems carry it as a hypothesis.

⚠️ **The constant is not optimised.** `8e` comes from the `4` of the iteration (two commutators,
each end of an edge) and the `2e` of the Stirling step; the chain's local cone is `4 · 2πe` hop-time
cones wide, four times a single stage's bound. What this file establishes is that the slope does not
grow with the system, not its best value.

⚠️ **`max(|Y|, 1)`** is the number of edges a probe on `Y` can touch at the first step, divided by
`Δ`. Probes on large regions pay for their size once, not per step.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md);
[`future-work.md`](../../specs/future-work.md); `CV/LiebRobinson.lean` (`hasDerivAt_conjComm`,
`norm_conj_eq`, `norm_commutator_spatial_factorial_le`), `CV/ArenaBridge.lean` (`arena_lightcone`),
`CV/FibredArenaBridge.lean` (`record_lightcone`), `CV/TwoCones.lean` (`lrVelocity`,
`record_influence_le_of_separated`), `CV/ConeComparison.lean`; Nachtergaele–Sims (2010);
`specs/BACKLOG.md` #213, #205, #39, #98.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### The edges touching a region, and a degree bound -/

/-- **The edges touching `Y`**: the coupling terms with an end in `Y`. Every other term commutes
with an observable supported on `Y`. -/
def edgesTouching (E : Finset (Fin K × Fin K)) (Y : Finset (Fin K)) : Finset (Fin K × Fin K) :=
  E.filter fun e => e.1 ∈ Y ∨ e.2 ∈ Y

theorem mem_edgesTouching {E : Finset (Fin K × Fin K)} {Y : Finset (Fin K)}
    {e : Fin K × Fin K} : e ∈ edgesTouching E Y ↔ e ∈ E ∧ (e.1 ∈ Y ∨ e.2 ∈ Y) :=
  Finset.mem_filter

/-- **A degree bound**: every site is an end of at most `Δ` edges. -/
def DegreeLE (E : Finset (Fin K × Fin K)) (Δ : ℕ) : Prop :=
  ∀ x : Fin K, (E.filter fun e => e.1 = x ∨ e.2 = x).card ≤ Δ

/-- Under a degree bound `Δ`, at most `Δ · |Y|` edges touch `Y`. -/
theorem card_edgesTouching_le {E : Finset (Fin K × Fin K)} {Δ : ℕ} (hdeg : DegreeLE E Δ)
    (Y : Finset (Fin K)) : (edgesTouching E Y).card ≤ Δ * Y.card := by
  have hsub : edgesTouching E Y ⊆ Y.biUnion fun x => E.filter fun e => e.1 = x ∨ e.2 = x := by
    intro e he
    rw [mem_edgesTouching] at he
    rw [Finset.mem_biUnion]
    rcases he.2 with h | h
    · exact ⟨e.1, h, Finset.mem_filter.2 ⟨he.1, Or.inl rfl⟩⟩
    · exact ⟨e.2, h, Finset.mem_filter.2 ⟨he.1, Or.inr rfl⟩⟩
  calc (edgesTouching E Y).card
      ≤ (Y.biUnion fun x => E.filter fun e => e.1 = x ∨ e.2 = x).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ Y, (E.filter fun e => e.1 = x ∨ e.2 = x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Y, Δ := Finset.sum_le_sum fun x _ => hdeg x
    _ = Δ * Y.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **One step back along an edge**: if the `(n + 1)`-ball around `R` misses `Y`, then the `n`-ball
misses every edge touching `Y`. -/
theorem disjoint_edge_of_mem_edgesTouching {E : Finset (Fin K × Fin K)} {R Y : Finset (Fin K)}
    {n : ℕ} (hdisj : Disjoint (graphBall E R (n + 1)) Y) {e : Fin K × Fin K}
    (he : e ∈ edgesTouching E Y) : Disjoint (graphBall E R n) {e.1, e.2} := by
  rw [mem_edgesTouching] at he
  have key : e.1 ∈ graphBall E R n ∨ e.2 ∈ graphBall E R n → False := by
    intro hin
    have h1 : e.1 ∈ graphBall E R (n + 1) := mem_graphNeighborhood_fst he.1 hin
    have h2 : e.2 ∈ graphBall E R (n + 1) := mem_graphNeighborhood_snd he.1 hin
    rcases he.2 with hy | hy
    · exact Finset.disjoint_left.1 hdisj h1 hy
    · exact Finset.disjoint_left.1 hdisj h2 hy
  rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

/-! ### One step of the iteration -/

section Step

variable [NeZero N] {E : Finset (Fin K × Fin K)}
  {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}

omit [NeZero N] in
/-- A sum of skew-Hermitian terms is skew-Hermitian. -/
theorem conjTranspose_sum_eq_neg {E' : Finset (Fin K × Fin K)}
    (hskew : ∀ e ∈ E', (G e)ᴴ = -(G e)) : (∑ e ∈ E', G e)ᴴ = -(∑ e ∈ E', G e) := by
  rw [Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hskew

/-- ★★ **One step of the Lieb–Robinson iteration.** Split the generator into the terms touching the
probe's region `Y` and the rest; the rest commutes with the probe and only conjugates. If each
touching term's commutator with the evolved observable is at most `φ`, then the commutator with the
probe grows at most like any `Φ` with `Φ(0) ≥ 0` and `Φ' ≥ 2‖B‖ · #(touching) · φ`. -/
theorem norm_commutator_step_le (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    (hskew : ∀ e ∈ E, (G e)ᴴ = -(G e)) {Y : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hB : SupportedOn Y B)
    (hAB : A * B = B * A) {φ Φ Φ' : ℝ → ℝ} (hΦ : ∀ s, HasDerivAt Φ (Φ' s) s) (hΦ0 : 0 ≤ Φ 0)
    {t : ℝ} (ht : 0 ≤ t)
    (hφ : ∀ s ∈ Set.Ico 0 t, ∀ e ∈ edgesTouching E Y,
      ‖heisenbergFlow (∑ e' ∈ E, G e') s A * G e - G e * heisenbergFlow (∑ e' ∈ E, G e') s A‖
        ≤ φ s)
    (hbound : ∀ s ∈ Set.Ico 0 t, 2 * ‖B‖ * (edgesTouching E Y).card * φ s ≤ Φ' s) :
    ‖heisenbergFlow (∑ e ∈ E, G e) t A * B - B * heisenbergFlow (∑ e ∈ E, G e) t A‖ ≤ Φ t := by
  have hne : Nonempty (FieldConfig K N) := ⟨fun _ => 0⟩
  set S := ∑ e ∈ E, G e with hSdef
  set T := ∑ e ∈ edgesTouching E Y, G e with hTdef
  set SY := ∑ e ∈ E.filter (fun e => ¬ (e.1 ∈ Y ∨ e.2 ∈ Y)), G e with hSYdef
  have hsplit : S = SY + T := by
    rw [hSdef, hSYdef, hTdef, edgesTouching, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not E _ G).symm
  have hSY : SYᴴ = -SY := conjTranspose_sum_eq_neg fun e he => hskew e (Finset.mem_filter.1 he).1
  have hcomm : SY * B = B * SY := by
    rw [hSYdef, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨heE, hnot⟩ := Finset.mem_filter.1 he
    refine commute_of_disjointSupport ?_ (hG e heE) hB
    rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact not_or.1 hnot
  have hderiv := fun s => hasDerivAt_conjComm (S := S) (S_X := SY) (T := T) A B hsplit hcomm s
  have hcont : ContinuousOn (conjComm S SY A B) (Set.Icc 0 t) :=
    fun s _ => (hderiv s).continuousAt.continuousWithinAt
  have h0 : ‖conjComm S SY A B 0‖ ≤ Φ 0 := by
    rw [conjComm_zero, sub_eq_zero.mpr hAB, norm_zero]
    exact hΦ0
  have hb : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖exp (s • SY)
        * ((heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
          - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A))
        * exp ((-s) • SY)‖ ≤ Φ' s := by
    intro s hs
    rw [norm_conj_eq hSY s]
    set F := heisenbergFlow S s A with hF
    have hFT : F * T - T * F = ∑ e ∈ edgesTouching E Y, (F * G e - G e * F) := by
      rw [hTdef, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have hnFT : ‖F * T - T * F‖ ≤ (edgesTouching E Y).card * φ s := by
      rw [hFT]
      calc ‖∑ e ∈ edgesTouching E Y, (F * G e - G e * F)‖
          ≤ ∑ e ∈ edgesTouching E Y, ‖F * G e - G e * F‖ := norm_sum_le _ _
        _ ≤ ∑ _e ∈ edgesTouching E Y, φ s := Finset.sum_le_sum fun e he => hφ s hs e he
        _ = (edgesTouching E Y).card * φ s := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ‖(F * T - T * F) * B - B * (F * T - T * F)‖
        ≤ ‖(F * T - T * F) * B‖ + ‖B * (F * T - T * F)‖ := norm_sub_le _ _
      _ ≤ ‖F * T - T * F‖ * ‖B‖ + ‖B‖ * ‖F * T - T * F‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖B‖ * ‖F * T - T * F‖ := by ring
      _ ≤ 2 * ‖B‖ * ((edgesTouching E Y).card * φ s) := by gcongr
      _ = 2 * ‖B‖ * (edgesTouching E Y).card * φ s := by ring
      _ ≤ Φ' s := hbound s hs
  have hres := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun s _ => (hderiv s).hasDerivWithinAt) h0 hΦ hb (Set.right_mem_Icc.2 ht)
  rwa [norm_conjComm hSY] at hres

end Step

/-! ### The iteration: a velocity from the local terms and the degree -/

/-- **The local rate** `4Δγ`: the iteration's growth rate per unit time, from a degree bound `Δ` and
a bound `γ` on every edge term. -/
noncomputable def localRate (Δ : ℕ) (γ : ℝ) : ℝ := 4 * Δ * γ

theorem localRate_nonneg (Δ : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ localRate Δ γ := by
  unfold localRate
  positivity

section Iteration

variable [NeZero N] {E : Finset (Fin K × Fin K)}
  {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}

/-- ★★★ **The local Lieb–Robinson bound.** For edge terms each supported on its edge, each
skew-Hermitian and each of norm at most `γ`, on a graph of degree at most `Δ`: an observable `A` on
`R` and a probe `B` on `Y` whose `n`-ball separation holds satisfy

  `‖[A(t), B]‖ ≤ 2‖A‖‖B‖ · max(|Y|, 1) · (4Δγ t)ⁿ / n!`  for `t ≥ 0`.

The rate `4Δγ` is built from the local terms and the degree, not from the whole generator, so it
does not grow with the size of the system. Proved by induction on `n` through
`norm_commutator_step_le`, the probe at each step replaced by the edge terms touching it. -/
theorem norm_commutator_local_le (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    (hskew : ∀ e ∈ E, (G e)ᴴ = -(G e)) {Δ : ℕ} (hdeg : DegreeLE E Δ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hγE : ∀ e ∈ E, ‖G e‖ ≤ γ) {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn R A) (n : ℕ) :
    ∀ {Y : Finset (Fin K)} {B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ},
      SupportedOn Y B → Disjoint (graphBall E R n) Y → ∀ {t : ℝ}, 0 ≤ t →
      ‖heisenbergFlow (∑ e ∈ E, G e) t A * B - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
        ≤ 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ n / n.factorial) := by
  have hne : Nonempty (FieldConfig K N) := ⟨fun _ => 0⟩
  have hS : (∑ e ∈ E, G e)ᴴ = -(∑ e ∈ E, G e) := conjTranspose_sum_eq_neg hskew
  have hc := localRate_nonneg Δ hγ
  induction n with
  | zero =>
    intro Y B _ _ t _
    have hF : ‖heisenbergFlow (∑ e ∈ E, G e) t A‖ ≤ ‖A‖ := norm_heisenbergFlow_le hS t A
    have hmax : (1 : ℝ) ≤ max (Y.card : ℝ) 1 := le_max_right _ _
    have hAB : 0 ≤ 2 * ‖A‖ * ‖B‖ := by positivity
    calc ‖heisenbergFlow (∑ e ∈ E, G e) t A * B - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
        ≤ ‖heisenbergFlow (∑ e ∈ E, G e) t A‖ * ‖B‖ + ‖B‖ * ‖heisenbergFlow (∑ e ∈ E, G e) t A‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 2 * ‖A‖ * ‖B‖ * 1 := by nlinarith [norm_nonneg B]
      _ ≤ 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1 := mul_le_mul_of_nonneg_left hmax hAB
      _ = 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1
            * ((localRate Δ γ * t) ^ 0 / (Nat.factorial 0 : ℝ)) := by simp
  | succ n ih =>
    intro Y B hB hdisj t ht
    have hAB : A * B = B * A :=
      commute_of_disjointSupport
        (Finset.disjoint_of_subset_left (graphBall_mono E R (Nat.zero_le (n + 1))) hdisj) hA hB
    refine norm_commutator_step_le hG hskew hB hAB
      (φ := fun s => 2 * ‖A‖ * γ * 2 * ((localRate Δ γ * s) ^ n / n.factorial))
      (Φ := fun s => 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1
        * ((localRate Δ γ * s) ^ (n + 1) / (n + 1).factorial))
      (Φ' := fun s => 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1 * localRate Δ γ
        * ((localRate Δ γ * s) ^ n / n.factorial)) ?_ ?_ ht ?_ ?_
    · intro s
      have h1 : HasDerivAt (fun x : ℝ => localRate Δ γ * x) (localRate Δ γ) s := by
        simpa using (hasDerivAt_id s).const_mul (localRate Δ γ)
      have h2 := ((h1.pow (n + 1)).div_const ((n + 1).factorial : ℝ)).const_mul
        (2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1)
      refine h2.congr_deriv ?_
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    · simp
    · intro s hs e he
      have heE := (mem_edgesTouching.1 he).1
      have hih := ih (hG e heE) (disjoint_edge_of_mem_edgesTouching hdisj he) hs.1
      have hcard : max (({e.1, e.2} : Finset (Fin K)).card : ℝ) 1 ≤ 2 := by
        have h2 : ({e.1, e.2} : Finset (Fin K)).card ≤ 2 := Finset.card_le_two
        exact max_le (by exact_mod_cast h2) (by norm_num)
      have hq : 0 ≤ (localRate Δ γ * s) ^ n / (n.factorial : ℝ) :=
        div_nonneg (pow_nonneg (mul_nonneg hc hs.1) n) (Nat.cast_nonneg _)
      refine hih.trans ?_
      have hA0 : 0 ≤ 2 * ‖A‖ := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hq
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hγE e heE) hA0) hcard
        (le_trans zero_le_one (le_max_right _ _)) (mul_nonneg hA0 hγ)
    · intro s hs
      have hq : 0 ≤ (localRate Δ γ * s) ^ n / (n.factorial : ℝ) :=
        div_nonneg (pow_nonneg (mul_nonneg hc hs.1) n) (Nat.cast_nonneg _)
      have hcard : ((edgesTouching E Y).card : ℝ) ≤ Δ * max (Y.card : ℝ) 1 := by
        have h := card_edgesTouching_le hdeg Y
        calc ((edgesTouching E Y).card : ℝ) ≤ ((Δ * Y.card : ℕ) : ℝ) := by exact_mod_cast h
          _ = Δ * (Y.card : ℝ) := by push_cast; ring
          _ ≤ Δ * max (Y.card : ℝ) 1 := by gcongr; exact le_max_left _ _
      have hK : 0 ≤ 2 * ‖A‖ * ‖B‖ * (4 * γ) * ((localRate Δ γ * s) ^ n / n.factorial) :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) hq
      calc 2 * ‖B‖ * ((edgesTouching E Y).card : ℝ)
            * (2 * ‖A‖ * γ * 2 * ((localRate Δ γ * s) ^ n / n.factorial))
          = ((edgesTouching E Y).card : ℝ)
            * (2 * ‖A‖ * ‖B‖ * (4 * γ) * ((localRate Δ γ * s) ^ n / n.factorial)) := by ring
        _ ≤ (Δ * max (Y.card : ℝ) 1)
            * (2 * ‖A‖ * ‖B‖ * (4 * γ) * ((localRate Δ γ * s) ^ n / n.factorial)) :=
          mul_le_mul_of_nonneg_right hcard hK
        _ = 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1 * localRate Δ γ
            * ((localRate Δ γ * s) ^ n / n.factorial) := by unfold localRate; ring

end Iteration

/-! ### The velocity -/

/-- **The local Lieb–Robinson velocity** `8eΔγ`, in sites per unit time. -/
noncomputable def localLRVelocity (Δ : ℕ) (γ : ℝ) : ℝ := 8 * Real.exp 1 * Δ * γ

/-- ★★ **Outside the local cone the bound is at most `2^{-d}`**: once
`localLRVelocity Δ γ · t ≤ d`, `(4Δγt)^d/d! ≤ 2^{-d}`. -/
theorem localRate_pow_div_factorial_le {Δ : ℕ} {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hvt : localLRVelocity Δ γ * t ≤ d) :
    (localRate Δ γ * t) ^ d / (d.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ d := by
  have hS : 0 ≤ 2 * (Δ : ℝ) * γ := by positivity
  have hv : 4 * Real.exp 1 * (2 * (Δ : ℝ) * γ) * t ≤ d := by
    have h : 4 * Real.exp 1 * (2 * (Δ : ℝ) * γ) * t = localLRVelocity Δ γ * t := by
      unfold localLRVelocity
      ring
    linarith
  have h := lr_bound_le_half_pow hS ht hd hv
  have he : localRate Δ γ * t = 2 * (2 * (Δ : ℝ) * γ) * t := by
    unfold localRate
    ring
  rwa [he]

/-! ### Back to the arena and the record -/

/-- **The kicked-minus-unkicked reading is at most the commutator**: the arena half of
`arena_lightcone`, stated for any skew generator so that any commutator bound can be fed in. -/
theorem arenaObs_kick_sub_le_commutator [NeZero N]
    {S : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hS : Sᴴ = -S) (t : ℝ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (W : Matrix.unitaryGroup (FieldConfig K N) ℂ) (p : FieldArena K N) :
    |arenaObs A (arenaKick (flowU hS t) (arenaKick W p))
        - arenaObs A (arenaKick (flowU hS t) p)|
      ≤ ‖heisenbergFlow S t A * W.val - W.val * heisenbergFlow S t A‖ := by
  have hne : Nonempty (FieldConfig K N) := ⟨fun _ => 0⟩
  rw [arenaObs_kick (flowU hS t) A (arenaKick W p),
    arenaObs_kick W (heisenberg (flowU hS t) A) p,
    arenaObs_kick (flowU hS t) A p,
    heisenberg_flowU hS t A]
  refine le_trans (arenaObs_sub_le _ _ p) ?_
  set X := heisenbergFlow S t A with hXdef
  have hWW : star W.val * W.val = 1 := by
    have hmem := W.property
    rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  have hdefect : heisenberg W X - X = star W.val * (X * W.val - W.val * X) := by
    rw [Matrix.mul_sub, heisenberg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hWW, Matrix.one_mul]
  rw [hdefect]
  have hWs : ‖star W.val‖ = 1 := by
    rw [norm_star]
    exact CStarRing.norm_of_mem_unitary W.property
  calc ‖star W.val * (X * W.val - W.val * X)‖
      ≤ ‖star W.val‖ * ‖X * W.val - W.val * X‖ := norm_mul_le _ _
    _ = ‖X * W.val - W.val * X‖ := by rw [hWs, one_mul]

section Flow

variable [NeZero N] (F : FieldStructuredFlow K N)

/-- ★★★ **The local arena light cone**: `arena_lightcone` with the local rate in place of the
whole generator's norm. -/
theorem lightcone_local (hskew : ∀ e ∈ F.edges, (F.piece e)ᴴ = -(F.piece e)) {Δ : ℕ}
    (hdeg : DegreeLE F.edges Δ) {γ : ℝ} (hγ : 0 ≤ γ) (hγE : ∀ e ∈ F.edges, ‖F.piece e‖ ≤ γ)
    {R Y : Finset (Fin K)} {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) {W : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    (hW : SupportedOn Y W.val) {d : ℕ} (hcone : Disjoint (graphBall F.edges R d) Y) {t : ℝ}
    (ht : 0 ≤ t) (p : FieldArena K N) :
    |arenaObs A (F.arenaFlow t (arenaKick W p)) - arenaObs A (F.arenaFlow t p)|
      ≤ 2 * ‖A‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial) := by
  refine (arenaObs_kick_sub_le_commutator F.gen_skew t A W p).trans ?_
  have h := norm_commutator_local_le F.piece_supported hskew hdeg hγ hγE hA d hW hcone ht
  rwa [CStarRing.norm_of_mem_unitary W.property, mul_one] at h

/-- ★★★ **The local record light cone**: `record_lightcone` with the local rate. A record written
through `A` on `R` moves under a kick on `Y` outside the `d`-ball by at most
`L_h L_g · 2‖A‖ max(|Y|, 1) (4Δγt)^d/d!`. -/
theorem record_lightcone_local (hskew : ∀ e ∈ F.edges, (F.piece e)ᴴ = -(F.piece e)) {Δ : ℕ}
    (hdeg : DegreeLE F.edges Δ) {γ : ℝ} (hγ : 0 ≤ γ) (hγE : ∀ e ∈ F.edges, ‖F.piece e‖ ≤ γ)
    {R Y : Finset (Fin K)} {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) {W : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    (hW : SupportedOn Y W.val) {d : ℕ} (hcone : Disjoint (graphBall F.edges R d) Y) {t : ℝ}
    (ht : 0 ≤ t) {Lh Lg : NNReal} {h : RecordFibre → ℝ} (hh : LipschitzWith Lh h)
    {g : ℝ → RecordFibre} (hg : LipschitzWith Lg g) (ω : ℝ × ℝ) (x : FibredFieldArena K N) :
    |h (recordStroke A g (F.fibredFlow ω t (fibredKick W x))).2
        - h (recordStroke A g (F.fibredFlow ω t x)).2|
      ≤ (Lh : ℝ) * (Lg : ℝ)
        * (2 * ‖A‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial)) := by
  have hbase := lightcone_local F hskew hdeg hγ hγE hA hW hcone ht x.1
  set u : ℝ := arenaObs A (F.arenaFlow t (arenaKick W x.1)) with hu
  set v : ℝ := arenaObs A (F.arenaFlow t x.1) with hv
  set θ : RecordFibre :=
    (x.2.1 + ((t * ω.1 : ℝ) : AddCircle (1 : ℝ)),
     x.2.2 + ((t * ω.2 : ℝ) : AddCircle (1 : ℝ))) with hθ
  have hfib₁ : (recordStroke A g (F.fibredFlow ω t (fibredKick W x))).2 = θ + g u := rfl
  have hfib₂ : (recordStroke A g (F.fibredFlow ω t x)).2 = θ + g v := rfl
  rw [hfib₁, hfib₂, ← Real.dist_eq]
  calc dist (h (θ + g u)) (h (θ + g v))
      ≤ (Lh : ℝ) * dist (θ + g u) (θ + g v) := hh.dist_le_mul _ _
    _ = (Lh : ℝ) * dist (g u) (g v) := by rw [dist_add_left]
    _ ≤ (Lh : ℝ) * ((Lg : ℝ) * dist u v) :=
        mul_le_mul_of_nonneg_left (hg.dist_le_mul u v) Lh.coe_nonneg
    _ ≤ (Lh : ℝ) * ((Lg : ℝ)
          * (2 * ‖A‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ Lg.coe_nonneg) Lh.coe_nonneg
        rw [Real.dist_eq]
        exact hbase
    _ = (Lh : ℝ) * (Lg : ℝ)
          * (2 * ‖A‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial)) := by
        ring

variable {V : Type*} [SeminormedAddCommGroup V]

/-- ★★★ **A record cannot be steered from outside the local cone**:
`record_influence_le_of_separated` with `localLRVelocity` in place of `lrVelocity`. Sites farther
than `d · hop` from `R`, and `localLRVelocity Δ γ · t ≤ d`, give at most
`L_h L_g · 2 max(|Y|, 1) 2^{-d} ‖A‖`. -/
theorem record_influence_le_of_separated_local
    (hskew : ∀ e ∈ F.edges, (F.piece e)ᴴ = -(F.piece e)) {Δ : ℕ} (hdeg : DegreeLE F.edges Δ)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγE : ∀ e ∈ F.edges, ‖F.piece e‖ ≤ γ)
    (emb : SiteEmbedding K V F.edges) {R Y : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn Y W.val) {d : ℕ}
    (hd : 1 ≤ d) (hsep : ∀ y ∈ Y, ∀ r ∈ R, (d : ℝ) * emb.hop < ‖emb.pos y - emb.pos r‖)
    {t : ℝ} (ht : 0 ≤ t) (hvt : localLRVelocity Δ γ * t ≤ d)
    {Lh Lg : NNReal} {h : RecordFibre → ℝ} (hh : LipschitzWith Lh h)
    {g : ℝ → RecordFibre} (hg : LipschitzWith Lg g) (ω : ℝ × ℝ) (x : FibredFieldArena K N) :
    |h (recordStroke A g (F.fibredFlow ω t (fibredKick W x))).2
        - h (recordStroke A g (F.fibredFlow ω t x)).2|
      ≤ (Lh : ℝ) * (Lg : ℝ) * (2 * max (Y.card : ℝ) 1 * (1 / 2 : ℝ) ^ d * ‖A‖) := by
  have hcone : Disjoint (graphBall F.edges R d) Y := disjoint_graphBall_of_separated emb R Y d hsep
  refine le_trans (record_lightcone_local F hskew hdeg hγ hγE hA hW hcone ht hh hg ω x) ?_
  have hbound := localRate_pow_div_factorial_le (Δ := Δ) hγ ht hd hvt
  have hK : 0 ≤ 2 * ‖A‖ * max (Y.card : ℝ) 1 := by positivity
  have hmul : 2 * ‖A‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial)
      ≤ 2 * max (Y.card : ℝ) 1 * (1 / 2 : ℝ) ^ d * ‖A‖ := by
    calc 2 * ‖A‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial)
        ≤ 2 * ‖A‖ * max (Y.card : ℝ) 1 * (1 / 2 : ℝ) ^ d := mul_le_mul_of_nonneg_left hbound hK
      _ = 2 * max (Y.card : ℝ) 1 * (1 / 2 : ℝ) ^ d * ‖A‖ := by ring
  exact mul_le_mul_of_nonneg_left hmul (by positivity)

end Flow

/-! ### The chain: a cone that does not grow with the chain -/

/-- Every site of the path graph is an end of at most two edges. -/
theorem degreeLE_pathGraph (n : ℕ) : DegreeLE (pathGraph n) 2 := by
  intro x
  set P : Finset (Fin n) := Finset.univ.filter fun k : Fin n => k.val = x.val with hP
  set Q : Finset (Fin n) := Finset.univ.filter fun k : Fin n => k.val + 1 = x.val with hQ
  have hPc : P.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => by
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  have hQc : Q.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => by
    simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  have hsub : (pathGraph n).filter (fun e => e.1 = x ∨ e.2 = x)
      ⊆ (P ∪ Q).image fun k => (Fin.castSucc k, Fin.succ k) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨k, rfl⟩ := mem_pathGraph.1 he.1
    refine Finset.mem_image.2 ⟨k, ?_, rfl⟩
    rcases he.2 with h | h
    · simp only at h
      subst h
      exact Finset.mem_union_left _ (by simp [hP])
    · simp only at h
      subst h
      exact Finset.mem_union_right _ (by simp [hQ])
  calc ((pathGraph n).filter fun e => e.1 = x ∨ e.2 = x).card
      ≤ ((P ∪ Q).image fun k => (Fin.castSucc k, Fin.succ k)).card := Finset.card_le_card hsub
    _ ≤ (P ∪ Q).card := Finset.card_image_le
    _ ≤ P.card + Q.card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

theorem pathFlow_piece_skew (n : ℕ) (J ħ : ℝ) :
    ∀ e ∈ (pathFlow n J ħ).edges, ((pathFlow n J ħ).piece e)ᴴ = -((pathFlow n J ħ).piece e) :=
  fun e _ => chainGen_skew J ħ e.1 e.2

theorem norm_pathFlow_piece_le (n : ℕ) (J ħ : ℝ) :
    ∀ e ∈ (pathFlow n J ħ).edges, ‖(pathFlow n J ħ).piece e‖ ≤ |J / ħ| :=
  fun _ he => (norm_chainGen J ħ (fst_ne_snd_of_mem_pathGraph he)).le

/-- ★★★ **The local cone of the chain does not depend on its length**: with degree `2` and edge
norm `|J/ħ|`, `v_loc · τ_hop = 8πe = 4 · 2πe`, for every number of edges. -/
theorem localLRVelocity_chain_mul_hopTime {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    localLRVelocity 2 |J / ħ| * hopTime J ħ = 4 * coneRatio := by
  rw [localLRVelocity, abs_of_pos (div_pos hJ hħ), hopTime, coneRatio]
  push_cast
  field_simp
  ring

/-- ★★★ **Beyond eight edges the local cone is the narrower one**: for `n > 8` the local velocity
is strictly below the whole-generator `lrVelocity (pathFlow n J ħ)`, and the gap grows with `n`. -/
theorem localLRVelocity_lt_lrVelocity_pathFlow {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {n : ℕ}
    (hn : 8 < n) : localLRVelocity 2 |J / ħ| < lrVelocity (pathFlow n J ħ) := by
  have hτ := hopTime_pos hJ hħ
  have h1 := localLRVelocity_chain_mul_hopTime hJ hħ
  have h2 := (pathFlow_lrVelocity_mul_hopTime_bounds hJ hħ n).1
  have hnR : (8 : ℝ) < n := by exact_mod_cast hn
  have hc := coneRatio_pos
  have hlt : localLRVelocity 2 |J / ħ| * hopTime J ħ
      < lrVelocity (pathFlow n J ħ) * hopTime J ħ := by
    rw [h1]
    nlinarith
  exact lt_of_mul_lt_mul_right hlt hτ.le

/-- ★★★ **The local bound on the whole chain at once**, at the length-independent rate
`localRate 2 |J/ħ| = 8|J/ħ|`. -/
theorem norm_commutator_pathFlow_le {n : ℕ} {J ħ : ℝ} {R : Finset (Fin (n + 1))}
    {A : Matrix (ChainConfig (n + 1)) (ChainConfig (n + 1)) ℂ} (hA : SupportedOn R A) (d : ℕ)
    {Y : Finset (Fin (n + 1))} {B : Matrix (ChainConfig (n + 1)) (ChainConfig (n + 1)) ℂ}
    (hB : SupportedOn Y B) (hcone : Disjoint (graphBall (pathGraph n) R d) Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖heisenbergFlow (pathFlow n J ħ).gen t A * B - B * heisenbergFlow (pathFlow n J ħ).gen t A‖
      ≤ 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1 * ((localRate 2 |J / ħ| * t) ^ d / d.factorial) :=
  norm_commutator_local_le (pathFlow n J ħ).piece_supported (pathFlow_piece_skew n J ħ)
    (degreeLE_pathGraph n) (abs_nonneg _) (norm_pathFlow_piece_le n J ħ) hA d hB hcone ht

/-! ### The capstone -/

/-- ★★★ **A local Lieb–Robinson velocity** (BACKLOG #213).
1. the local bound for any edge-supported skew family of degree `≤ Δ` and edge norm `≤ γ`, at
   rate `4Δγ`;
2. outside `localLRVelocity Δ γ · t ≤ d` that bound is at most `2^{-d}`;
3. on the chain, `v_loc · τ_hop = 4 · 2πe` for every length;
4. for `n > 8` edges the local velocity is strictly below the whole-generator one. -/
theorem local_lieb_robinson [NeZero N] {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (∀ {E : Finset (Fin K × Fin K)}
        {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ},
        (∀ e ∈ E, SupportedOn {e.1, e.2} (G e)) → (∀ e ∈ E, (G e)ᴴ = -(G e)) →
        ∀ {Δ : ℕ}, DegreeLE E Δ → ∀ {γ : ℝ}, 0 ≤ γ → (∀ e ∈ E, ‖G e‖ ≤ γ) →
        ∀ {R Y : Finset (Fin K)} {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ},
          SupportedOn R A → SupportedOn Y B → ∀ d : ℕ, Disjoint (graphBall E R d) Y →
          ∀ {t : ℝ}, 0 ≤ t →
          ‖heisenbergFlow (∑ e ∈ E, G e) t A * B - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
            ≤ 2 * ‖A‖ * ‖B‖ * max (Y.card : ℝ) 1 * ((localRate Δ γ * t) ^ d / d.factorial))
      ∧ (∀ {Δ : ℕ} {γ t : ℝ}, 0 ≤ γ → 0 ≤ t → ∀ {d : ℕ}, 1 ≤ d →
          localLRVelocity Δ γ * t ≤ d → (localRate Δ γ * t) ^ d / (d.factorial : ℝ) ≤ (1 / 2) ^ d)
      ∧ localLRVelocity 2 |J / ħ| * hopTime J ħ = 4 * coneRatio
      ∧ (∀ n : ℕ, 8 < n → localLRVelocity 2 |J / ħ| < lrVelocity (pathFlow n J ħ)) :=
  ⟨fun hG hskew _ hdeg _ hγ hγE _ _ _ _ hA hB d hcone _ ht =>
      norm_commutator_local_le hG hskew hdeg hγ hγE hA d hB hcone ht,
    fun hγ ht _ hd hvt => localRate_pow_div_factorial_le hγ ht hd hvt,
    localLRVelocity_chain_mul_hopTime hJ hħ,
    fun _ hn => localLRVelocity_lt_lrVelocity_pathFlow hJ hħ hn⟩

end CSD.CV

end
