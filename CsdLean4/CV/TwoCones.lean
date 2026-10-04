/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DispersionEarned
public import CsdLean4.CV.FibredArenaBridge
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The two cones: the record cone inside a kinematic cone

**Category:** 3-Local (CV; continuous variables — relativistic structure forced, not defined).
BACKLOG #98, out of #39.

The corpus had two cone structures that were never related:

* the **record cone** — `graphBall` on the coupling graph, and the Lieb–Robinson bound
  ★★ `record_lightcone` of [`FibredArenaBridge.lean`](FibredArenaBridge.lean), whose error term is
  `(2‖S‖t)^d / d!` at graph separation `d`;
* the **kinematic cone** of [`DispersionEarned.lean`](DispersionEarned.lean), where
  ★ `cone_preserving_is_boost` earns the boost group and ★★ `cone_symmetry_characterises_omega`
  then selects `ω = √(p² + m²)`.

Three facts about the starting point, established by reading the corpus rather than assumed:

1. **There was no cone object anywhere.** `record_lightcone` and `FieldStructuredFlow.lightcone` are
   *theorem* names; `DispersionEarned`'s "cone" is the pair of light **rays** `E = ±p`, entering only
   as the hypotheses `a + b = c + d` and `a − b = d − c`. There was nothing with a slope for the
   record cone to sit inside. `forwardCone` is that object.
2. **There was no map from sites to space.** `graphBall` lives on `Fin K` with integer hop counts,
   and the coupling graph carries no geometry. `SiteEmbedding` **posits** one, with a bound `hop` on
   the length of an edge. ⚠️ Note that `Fin K` is read as a *momentum* label in
   [`Dispersion.lean`](Dispersion.lean) and as a *graph site* label in
   [`SupportSpreading.lean`](SupportSpreading.lean); everything here takes the **site** reading, and
   the embedding is of sites into position space.
3. **The factorial bound needed is already in Mathlib**: `Stirling.le_factorial_stirling`, which
   holds for all `n` with no largeness hypothesis.

## What is proved

* `forwardCone V v` — `{(t, x) | ‖x‖ ≤ v·t, 0 ≤ t}`, the forward cone of slope `v` over any
  seminormed space, with `forwardCone_mono` in the slope;
* ★ `exists_dist_le_of_mem_graphBall` — **the geometric containment**: a site `d` hops from `R` is
  within `d · hop` of `R` in the embedding, by induction on hops. Hence ★★
  `mem_forwardCone_of_mem_graphBall`: with a time step `τ > 0`, **the `n`-step record cone embeds in
  the forward cone of slope `hop/τ`**, which is the statement #98 asked for;
* ★ `disjoint_graphBall_of_separated` — the contrapositive, and the usable direction: sites
  *Euclidean-far* from `R` are outside the graph ball, so `record_lightcone`'s hypothesis is
  discharged by geometry;
* ★ `pow_div_factorial_le` — `x^d/d! ≤ (e·x/d)^d`, from `Stirling.le_factorial_stirling`; hence
  ★★ `lr_bound_le_half_pow`: once `d ≥ lrVelocity · t` the Lieb–Robinson error is at most `2^{-d}`.
  `lrVelocity F = 4e‖S‖` **is** the cone's slope in hops per unit time;
* ★★★ `record_influence_le_of_separated` — **the capstone**: a record written in `R` cannot be
  steered from a region whose sites are farther than `d · hop` from `R`, to within
  `L_h L_g · 2 · 2^{-d} · ‖A‖`, whenever `d ≥ lrVelocity · t`. Geometric separation in the embedding
  gives geometric suppression, with the velocity appearing as a slope;
* ★★ `forwardCone_eq_nonnegSpan` and ★★ `mapsTo_forwardCone_of_rays` — the cone of slope `v` is the
  non-negative span of its two null rays, so a linear map fixing both rays forward **preserves the
  cone**;
* ★★★ `forwardCone_rays_is_boost` — **the link to `DispersionEarned`**: rescaling `x ↦ x/v` carries
  the slope-`v` cone to the slope-`1` cone, so a unimodular ray-preserving map of the slope-`v` cone
  **is a boost** at some rapidity. This is what makes the containment touch the kinematic side at
  theorem level rather than in prose;
* ★★★ `slope_cone_symmetry_characterises_omega` — and therefore **the slope is immaterial to P4**:
  for *any* `v > 0`, covariance under the unimodular symmetries of the slope-`v` cone plus rest
  energy `m` forces `ω = omega m`. So the Lieb–Robinson velocity can be the kinematic cone's slope
  without changing the dispersion that P4 selects.

## Honest scope

⚠️ **This is a containment, never an identification.** The record cone is shown to sit inside a
kinematic cone and the two cones' symmetry groups are shown to be the same group; **the two cones are
not identified**, and nothing here says the Lieb–Robinson velocity *is* a limiting speed. An
identification needs a continuum limit of the graph dynamics that the corpus does not have, and must
not be read into any statement below.

⚠️ **The embedding is posited, and so is the time step.** `SiteEmbedding` is data supplied by the
user of these theorems, not constructed: nothing derives a spatial arrangement of the coupling graph
from the dynamics, and `τ` is a conversion factor, not a derived lattice spacing in time. Every
"slope" below is therefore `hop/τ` or `4e‖S‖` in whatever units the embedding was given.

⚠️ **`lrVelocity` is an upper bound with a model-dependent constant**, read off
`record_lightcone`'s own error term. The `4e` is what the Stirling bound gives at the chosen
suppression `2^{-d}`; it is not sharp, and `Stirling.factorial_isEquivalent_stirling` would be the
route to a sharper constant. No claim is made that it is the smallest velocity that works.

⚠️ **One spatial dimension on the kinematic side.** `forwardCone` is stated over any seminormed
space, but the ray decomposition, the boost link and the `ω` corollary are `V = ℝ`: the `(E, p)`
plane of `DispersionEarned` is two-dimensional, so the symmetry statements are `1 + 1`. Nothing here
extends the boost link to higher dimensions.

⚠️ **The `(E, p)`/`(t, x)` relabelling is explicit, not a derivation.** `cone_preserving_is_boost` is
a statement about linear maps of a plane preserving two rays; applying it to `(t, x)` is a
relabelling of that plane, exactly as `DispersionEarned`'s own header warns. No duality between
position and momentum space is constructed or needed.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md);
[`future-work.md`](../../specs/future-work.md); [`eft-pillars-plan.md`](../../specs/eft-pillars-plan.md)
P4; `CV/DispersionEarned.lean`, `CV/FibredArenaBridge.lean`, `CV/SupportSpreading.lean`,
`CV/RecordInfluence.lean`; `specs/BACKLOG.md` #98, #39, #38.
-/

@[expose] public section

open MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### The forward cone of slope `v` -/

/-- **The forward cone of slope `v`** over a seminormed space: the pairs `(t, x)` of an elapsed time
and a displacement with `‖x‖ ≤ v · t`. The object the corpus did not have — `record_lightcone` and
`cone_preserving_is_boost` both speak of a cone without one. -/
def forwardCone (V : Type*) [SeminormedAddCommGroup V] (v : ℝ) : Set (ℝ × V) :=
  {q | ‖q.2‖ ≤ v * q.1 ∧ 0 ≤ q.1}

variable {V : Type*} [SeminormedAddCommGroup V]

@[simp] theorem mem_forwardCone {v : ℝ} {q : ℝ × V} :
    q ∈ forwardCone V v ↔ ‖q.2‖ ≤ v * q.1 ∧ 0 ≤ q.1 := Iff.rfl

theorem forwardCone_mono {v w : ℝ} (h : v ≤ w) : forwardCone V v ⊆ forwardCone V w := by
  intro q hq
  exact ⟨le_trans hq.1 (mul_le_mul_of_nonneg_right h hq.2), hq.2⟩

theorem zero_mem_forwardCone {v : ℝ} : ((0 : ℝ), (0 : V)) ∈ forwardCone V v := by
  simp

/-! ### A posited embedding of the coupling graph into space -/

/-- **A spatial arrangement of the coupling graph.** Positions for the sites and a bound `hop` on the
length of a coupling edge. ⚠️ This is **data, not a construction**: nothing in the corpus derives a
spatial arrangement from the dynamics, and the graph itself carries no geometry. -/
structure SiteEmbedding (K : ℕ) (V : Type*) [SeminormedAddCommGroup V]
    (edges : Finset (Fin K × Fin K)) where
  /-- The position of each site. -/
  pos : Fin K → V
  /-- The bound on the length of a coupling edge. -/
  hop : ℝ
  /-- The bound is non-negative. -/
  hop_nonneg : 0 ≤ hop
  /-- Every coupling edge joins sites within `hop` of each other. -/
  edge_le : ∀ e ∈ edges, ‖pos e.1 - pos e.2‖ ≤ hop

namespace SiteEmbedding

variable {edges : Finset (Fin K × Fin K)} (emb : SiteEmbedding K V edges)

theorem edge_le' {e : Fin K × Fin K} (he : e ∈ edges) : ‖emb.pos e.2 - emb.pos e.1‖ ≤ emb.hop := by
  rw [norm_sub_rev]
  exact emb.edge_le e he

end SiteEmbedding

/-! ### The geometric containment -/

/-- ★ **A site `n` hops from `R` is within `n · hop` of `R` in the embedding.** Induction on hops:
one step of `graphNeighborhood` either stays put or crosses one edge, and an edge is short by
hypothesis. This is the whole geometric content of #98. -/
theorem exists_dist_le_of_mem_graphBall {edges : Finset (Fin K × Fin K)}
    (emb : SiteEmbedding K V edges) (R : Finset (Fin K)) :
    ∀ (n : ℕ) {k : Fin K}, k ∈ graphBall edges R n →
      ∃ r ∈ R, ‖emb.pos k - emb.pos r‖ ≤ (n : ℝ) * emb.hop := by
  intro n
  induction n with
  | zero =>
      intro k hk
      rw [graphBall_zero] at hk
      exact ⟨k, hk, by simp⟩
  | succ n ih =>
      intro k hk
      rw [graphBall_succ, graphNeighborhood, Finset.mem_union] at hk
      -- either `k` was already inside, or it crossed one edge
      have hstep : ∃ s ∈ graphBall edges R n, ‖emb.pos k - emb.pos s‖ ≤ emb.hop := by
        rcases hk with hk | hk
        · exact ⟨k, hk, by simp [emb.hop_nonneg]⟩
        · obtain ⟨e, he, hke⟩ := Finset.mem_biUnion.1 hk
          obtain ⟨heE, hend⟩ := Finset.mem_filter.1 he
          have hke' : k = e.1 ∨ k = e.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hke
          rcases hend with h1 | h2
          · rcases hke' with hk1 | hk2
            · exact ⟨e.1, h1, by rw [hk1]; simpa using emb.hop_nonneg⟩
            · exact ⟨e.1, h1, by rw [hk2]; exact emb.edge_le' heE⟩
          · rcases hke' with hk1 | hk2
            · exact ⟨e.2, h2, by rw [hk1]; exact emb.edge_le e heE⟩
            · exact ⟨e.2, h2, by rw [hk2]; simpa using emb.hop_nonneg⟩
      obtain ⟨s, hs, hks⟩ := hstep
      obtain ⟨r, hr, hsr⟩ := ih hs
      refine ⟨r, hr, ?_⟩
      calc ‖emb.pos k - emb.pos r‖
          ≤ ‖emb.pos k - emb.pos s‖ + ‖emb.pos s - emb.pos r‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ emb.hop + (n : ℝ) * emb.hop := add_le_add hks hsr
        _ = ((n : ℝ) + 1) * emb.hop := by ring
        _ = ((n + 1 : ℕ) : ℝ) * emb.hop := by push_cast; ring

/-- ★★ **The record cone embeds in the forward cone of slope `hop/τ`.** With a time step `τ > 0`, a
site reached in `n` steps sits, relative to some site of `R`, at a displacement–time pair inside the
forward cone whose slope is one hop per time step. This is #98's containment. -/
theorem mem_forwardCone_of_mem_graphBall {edges : Finset (Fin K × Fin K)}
    (emb : SiteEmbedding K V edges) (R : Finset (Fin K)) {τ : ℝ} (hτ : 0 < τ) (n : ℕ)
    {k : Fin K} (hk : k ∈ graphBall edges R n) :
    ∃ r ∈ R, ((n : ℝ) * τ, emb.pos k - emb.pos r) ∈ forwardCone V (emb.hop / τ) := by
  obtain ⟨r, hr, hdist⟩ := exists_dist_le_of_mem_graphBall emb R n hk
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  refine ⟨r, hr, ?_, mul_nonneg (Nat.cast_nonneg n) hτ.le⟩
  calc ‖emb.pos k - emb.pos r‖ ≤ (n : ℝ) * emb.hop := hdist
    _ = emb.hop / τ * ((n : ℝ) * τ) := by field_simp

/-- A displacement longer than the cone allows is outside the cone. -/
theorem notMem_forwardCone_of_lt {v t : ℝ} {x : V} (h : v * t < ‖x‖) :
    (t, x) ∉ forwardCone V v := fun hq => absurd hq.1 (not_le.2 h)

/-- ★★ **Outside the cone is outside the record cone.** The contrapositive of the containment, in
cone language: a region no point of which is in the forward cone of slope `hop/τ` over `R` is
disjoint from the `n`-step record cone. This is what discharges `record_lightcone`'s `Disjoint`
hypothesis *geometrically*. -/
theorem disjoint_graphBall_of_notMem_forwardCone {edges : Finset (Fin K × Fin K)}
    (emb : SiteEmbedding K V edges) (R Y : Finset (Fin K)) {τ : ℝ} (hτ : 0 < τ) (n : ℕ)
    (hout : ∀ y ∈ Y, ∀ r ∈ R,
      ((n : ℝ) * τ, emb.pos y - emb.pos r) ∉ forwardCone V (emb.hop / τ)) :
    Disjoint (graphBall edges R n) Y := by
  refine Finset.disjoint_right.2 fun y hy hball => ?_
  obtain ⟨r, hr, hmem⟩ := mem_forwardCone_of_mem_graphBall emb R hτ n hball
  exact hout y hy r hr hmem

/-- ★ **Euclidean separation puts a region outside the record cone.** The practical form of
`disjoint_graphBall_of_notMem_forwardCone`: supply distances, not cone memberships. The time step
cancels, so the condition is the hop-count one, `n · hop`. -/
theorem disjoint_graphBall_of_separated {edges : Finset (Fin K × Fin K)}
    (emb : SiteEmbedding K V edges) (R Y : Finset (Fin K)) (n : ℕ)
    (hsep : ∀ y ∈ Y, ∀ r ∈ R, (n : ℝ) * emb.hop < ‖emb.pos y - emb.pos r‖) :
    Disjoint (graphBall edges R n) Y := by
  refine disjoint_graphBall_of_notMem_forwardCone emb R Y (τ := 1) one_pos n
    fun y hy r hr => notMem_forwardCone_of_lt ?_
  have h := hsep y hy r hr
  calc emb.hop / 1 * ((n : ℝ) * 1) = (n : ℝ) * emb.hop := by ring
    _ < ‖emb.pos y - emb.pos r‖ := h

/-! ### The Lieb–Robinson velocity, from Stirling's bound -/

/-- ★ **`x^d/d! ≤ (e·x/d)^d`.** The factorial lower bound is `Stirling.le_factorial_stirling`, which
holds for every `n`; the `√(2πd)` factor is at least one for `d ≥ 1` and is discarded. -/
theorem pow_div_factorial_le {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 1 ≤ d) :
    x ^ d / (d.factorial : ℝ) ≤ (Real.exp 1 * x / d) ^ d := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * d) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.pi_gt_three]
  have hstir : ((d : ℝ) / Real.exp 1) ^ d ≤ (d.factorial : ℝ) := by
    refine le_trans ?_ (Stirling.le_factorial_stirling d)
    have hnn : (0 : ℝ) ≤ ((d : ℝ) / Real.exp 1) ^ d := by positivity
    nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d.factorial : ℝ))]
  calc x ^ d = (Real.exp 1 * x / d) ^ d * ((d : ℝ) / Real.exp 1) ^ d := by
        rw [← mul_pow]
        congr 1
        field_simp
    _ ≤ (Real.exp 1 * x / d) ^ d * (d.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hstir (by positivity)

/-- **The Lieb–Robinson velocity of a structured flow**, in hops per unit time: the slope at which
`record_lightcone`'s error term is suppressed by `2^{-d}`. ⚠️ An upper bound with the constant that
the Stirling estimate happens to give at that suppression, not a sharp speed. -/
noncomputable def lrVelocity (F : FieldStructuredFlow K N) : ℝ :=
  4 * Real.exp 1 * ‖∑ e ∈ F.edges, F.piece e‖

theorem lrVelocity_nonneg (F : FieldStructuredFlow K N) : 0 ≤ lrVelocity F := by
  unfold lrVelocity
  positivity

/-- ★★ **Outside the cone of slope `lrVelocity`, the Lieb–Robinson error is at most `2^{-d}`.** The
inequality that turns `record_lightcone`'s factorial bound into a statement about a *cone*: the
suppression sets in exactly once the separation exceeds the velocity times the elapsed time. -/
theorem lr_bound_le_half_pow {S t : ℝ} (hS : 0 ≤ S) (ht : 0 ≤ t) {d : ℕ} (hd : 1 ≤ d)
    (hvt : 4 * Real.exp 1 * S * t ≤ (d : ℝ)) :
    (2 * S * t) ^ d / (d.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ d := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hx : (0 : ℝ) ≤ 2 * S * t := by positivity
  refine le_trans (pow_div_factorial_le hx hd) ?_
  refine pow_le_pow_left₀ (by positivity) ?_ d
  rw [div_le_iff₀ hdpos]
  nlinarith [Real.exp_pos (1 : ℝ)]

/-! ### The capstone: separation in space, suppression in the record -/

/-- ★★★ **A record cannot be steered from outside the kinematic cone.** The Lieb–Robinson cone of
★★ `record_lightcone` is here read through the embedding: if every site of the kicking region `Y` is
farther than `d · hop` from the read region `R`, and the elapsed time satisfies
`lrVelocity F · t ≤ d`, then the record readout differs from the unkicked one by at most
`L_h L_g · 2 · 2^{-d} · ‖A‖`. Geometric separation in space gives geometric suppression in the
record, and the velocity enters as the slope of the cone.

⚠️ **Containment, not identification**: this says the record cone *sits inside* a cone of slope
`lrVelocity F · hop`, not that the two cones coincide, and not that `lrVelocity` is a limiting
speed. -/
theorem record_influence_le_of_separated [NeZero N] (F : FieldStructuredFlow K N)
    {edges : Finset (Fin K × Fin K)} (hedges : edges = F.edges)
    (emb : SiteEmbedding K V edges) {R Y : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn Y W.val)
    {d : ℕ} (hd : 1 ≤ d)
    (hsep : ∀ y ∈ Y, ∀ r ∈ R, (d : ℝ) * emb.hop < ‖emb.pos y - emb.pos r‖)
    {t : ℝ} (ht : 0 ≤ t) (hvt : lrVelocity F * t ≤ (d : ℝ))
    {Lh Lg : NNReal} {h : RecordFibre → ℝ} (hh : LipschitzWith Lh h)
    {g : ℝ → RecordFibre} (hg : LipschitzWith Lg g)
    (ω : ℝ × ℝ) (x : FibredFieldArena K N) :
    |h (recordStroke A g (F.fibredFlow ω t (fibredKick W x))).2
        - h (recordStroke A g (F.fibredFlow ω t x)).2|
      ≤ (Lh : ℝ) * (Lg : ℝ) * (2 * (1 / 2 : ℝ) ^ d * ‖A‖) := by
  subst hedges
  have hcone : Disjoint (graphBall F.edges R d) Y :=
    disjoint_graphBall_of_separated emb R Y d hsep
  refine le_trans (record_lightcone F hA hW hcone ht hh hg ω x) ?_
  have hbound : (2 * ‖∑ e ∈ F.edges, F.piece e‖ * t) ^ d / (d.factorial : ℝ)
      ≤ (1 / 2 : ℝ) ^ d :=
    lr_bound_le_half_pow (norm_nonneg _) ht hd (by
      have := hvt
      unfold lrVelocity at this
      linarith)
  have hmul : (2 : ℝ) * ((2 * ‖∑ e ∈ F.edges, F.piece e‖ * t) ^ d / (d.factorial : ℝ)) * ‖A‖
      ≤ 2 * (1 / 2 : ℝ) ^ d * ‖A‖ := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by norm_num))
      (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left hmul (by positivity)

/-! ### The cone's symmetries are the boosts, at every slope -/

/-- ★★ **The forward cone of slope `v` is the non-negative span of its two null rays.** The
decomposition that makes "fixes both rays" imply "preserves the cone". -/
theorem forwardCone_eq_nonnegSpan {v : ℝ} (hv : 0 < v) (q : ℝ × ℝ) :
    q ∈ forwardCone ℝ v ↔
      ∃ s u : ℝ, 0 ≤ s ∧ 0 ≤ u ∧ q = (s + u, v * s - v * u) := by
  constructor
  · intro hq
    obtain ⟨hnorm, ht⟩ := hq
    rw [Real.norm_eq_abs, abs_le] at hnorm
    refine ⟨(q.1 + q.2 / v) / 2, (q.1 - q.2 / v) / 2, by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), zero_mul, ← neg_le_iff_add_nonneg']
      rw [le_div_iff₀ hv] at *
      nlinarith [hnorm.1], by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), zero_mul, sub_nonneg,
        div_le_iff₀ hv]
      nlinarith [hnorm.2], ?_⟩
    refine Prod.ext ?_ ?_ <;> field_simp <;> ring
  · rintro ⟨s, u, hs, hu, rfl⟩
    refine ⟨?_, by simpa using by linarith⟩
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

/-- ★★ **A linear map fixing both null rays forward preserves the cone.** The hypotheses say the map
sends `(1, v)` to a positive multiple of itself and `(1, −v)` likewise; the cone is their
non-negative span, so it is preserved. -/
theorem mapsTo_forwardCone_of_rays {v : ℝ} (hv : 0 < v) {a b c d : ℝ}
    (hRpos : 0 < a + b * v) (hR : c + d * v = v * (a + b * v))
    (hLpos : 0 < a - b * v) (hL : c - d * v = -v * (a - b * v)) :
    Set.MapsTo (fun q : ℝ × ℝ => (a * q.1 + b * q.2, c * q.1 + d * q.2))
      (forwardCone ℝ v) (forwardCone ℝ v) := by
  intro q hq
  obtain ⟨s, u, hs, hu, rfl⟩ := (forwardCone_eq_nonnegSpan hv q).1 hq
  refine (forwardCone_eq_nonnegSpan hv _).2
    ⟨s * (a + b * v), u * (a - b * v), by positivity, by positivity, ?_⟩
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    nlinarith [hR, hL]

/-- ★★★ **The symmetries of a cone of slope `v` are the boosts.** Rescaling `x ↦ x/v` carries the
slope-`v` cone to the slope-`1` cone, and
[`DispersionEarned.lean`](DispersionEarned.lean)'s ★ `cone_preserving_is_boost` then applies: a
unimodular linear map fixing both null rays of the slope-`v` cone **is** the boost at some rapidity,
read in the rescaled coordinate. This is the theorem-level link between the record cone's slope and
the kinematic side.

⚠️ Reading the plane `(t, x)` as the `(E, p)` plane is a **relabelling**, exactly as
`DispersionEarned`'s own header says; no position/momentum duality is constructed. -/
theorem forwardCone_rays_is_boost {v : ℝ} (hv : 0 < v) {a b c d : ℝ}
    (hR : c + d * v = v * (a + b * v)) (hRpos : 0 < a + b * v)
    (hL : c - d * v = -v * (a - b * v)) (hLpos : 0 < a - b * v)
    (hdet : a * d - b * c = 1) :
    ∃ χ : ℝ, ∀ t x : ℝ,
      a * t + b * x = boostE χ t (x / v) ∧ (c * t + d * x) / v = boostP χ t (x / v) := by
  have hv' : v ≠ 0 := ne_of_gt hv
  obtain ⟨χ, hχ⟩ := cone_preserving_is_boost
    (a := a) (b := b * v) (c := c / v) (d := d)
    (by field_simp; linarith) hRpos
    (by field_simp; linarith) hLpos
    (by field_simp; linarith [hdet])
  refine ⟨χ, fun t x => ?_⟩
  obtain ⟨h1, h2⟩ := hχ t (x / v)
  refine ⟨?_, ?_⟩
  · rw [← h1]
    field_simp
  · rw [← h2]
    field_simp

/-- ★★★ **The cone's slope is immaterial to the dispersion P4 selects.** For any `v > 0`, a
dispersion with rest energy `m` that is covariant under every unimodular symmetry of the slope-`v`
cone is `ω = √(p² + m²)`. So the Lieb–Robinson velocity may be taken as the kinematic cone's slope
without changing what `cone_symmetry_characterises_omega` forces — which is what makes the
containment of `record_influence_le_of_separated` compatible with P4 rather than merely adjacent to
it. -/
theorem slope_cone_symmetry_characterises_omega {ω : ℝ → ℝ} {m v : ℝ} (hm : 0 < m) (hv : 0 < v)
    (h0 : ω 0 = m)
    (hcov : ∀ a b c d : ℝ, 0 < a + b * v → c + d * v = v * (a + b * v) →
        0 < a - b * v → c - d * v = -v * (a - b * v) → a * d - b * c = 1 →
        ∀ p, a * ω p + b * v * p = ω (c / v * ω p + d * p)) :
    ω = omega m := by
  have hv' : v ≠ 0 := ne_of_gt hv
  refine (cone_symmetry_characterises_omega hm).1 ⟨h0, fun a' b' c' d' hR hRpos hL hLpos hdet p => ?_⟩
  have h := hcov a' (b' / v) (c' * v) d'
    (by field_simp; linarith)
    (by field_simp; linarith)
    (by field_simp; linarith)
    (by field_simp; linarith)
    (by field_simp; linarith [hdet]) p
  rw [show b' / v * v = b' from by field_simp,
    show c' * v / v = c' from by field_simp] at h
  exact h

end CSD.CV

end
