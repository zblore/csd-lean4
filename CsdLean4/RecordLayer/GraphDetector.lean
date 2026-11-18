/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GraphCone
public import CsdLean4.RecordLayer.UnifiedCausalArrival
public import CsdLean4.RecordLayer.DiracPointerThreshold

/-!
# A region detector on a graph: no display before the growth reaches it

**Category:** 7-SigmaLayer. BACKLOG #297, second brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, items 3 and 4).

A pointer is coupled to an observable `B₀` supported on a set of sites `X` of a graph. The
carrier starts on a set of sites `Y`. This module bounds the pointer's displacement by the
growth of `X` towards `Y`, and gives the condition for the pointer to display when the
carrier is on `X`.

## The carrier

* ★★ `norm_heisenbergFlow_mul_graph_le` — `‖A(t) B‖ ≤ (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖` when `d`
  steps of growth from the sites of `A` miss the sites of `B`;
* `arenaObs_mul_of_supp`, `mul_arenaDM_mk` — a ray supported on `Y`;
* ★★ `abs_arenaObs_flow_graph_le` — the occupancy of `X` by a carrier that starts on `Y`.

## The pointer

* `hopsG_idxCoupledGen`;
* ★★★ `abs_idxPointerShift_le_graph` — the displacement of a pointer coupled to `B₀` on `X`,
  for a carrier that starts on `Y`: at most `2 |f'(θ₂)| ‖B₀‖ (2 ‖H‖ t)^d / d! · t`, on every
  fibre, with `H` the coupled Hamiltonian;
* ★★★ `graphDetector_not_displayed` — a ready pointer is not displayed at `t` while that
  bound is below `1/6`;
* ★★ `le_idxPointerShift_of_le`, `idxPointerShift_le_of_le_one`,
  ★★ `graphDetector_displayed` — a ready pointer is displayed at `t` once the carrier has
  kept the occupancy of the detector's observable at least `q` up to `t`, with `1/3 ≤ κ q t`
  and `κ t ≤ 2/3`, `κ = −2 f'(θ₂)` the rate on the fibre.

## The torus

* `siteSetProj`, `siteSetProj_isHermitian`, `siteSuppG_siteSetProj`, `hopsG_siteSetProj`,
  `norm_siteSetProj_le`;
* ★★★ `torusDetector_not_displayed` — for the lattice Dirac carrier of any dimension and a
  detector on a set of sites `X`.

## Honest scope

⚠️ **Flow times.** Every time is a flow time. Nothing here is a time read by an observer.

⚠️ **The upper bound is a factorial tail.** `graphDetector_not_displayed` holds while
`2 |f'| ‖B₀‖ (2 ‖H‖ t)^d / d! · t < 1/6`. It is not an exclusion at a sharp time, and the
rate `2 ‖H‖` is the coupled Hamiltonian's norm, not the group velocity.

⚠️ **`graphDetector_displayed` takes the occupancy as a hypothesis.** That a packet on the
torus keeps the occupancy of a box of sites above `q` over a window is not shown here; the
packet's box weights are in `CV/DiracPacketWindowD.lean` and are not yet joined to the
arena's observable.

⚠️ **A display, not a tick count.** The pointer's readout at one time. No `TickReadout` is
built for this arena here, so the detector is not yet in a record history.

⚠️ **The graph is given**, as in `RecordLayer/GraphCone.lean`.

References: `specs/BACKLOG.md` #297, #363; `specs/unified-record-spacetime-plan.md` (UD-230,
UD-231, UA-5, UA-7, UO-15); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/GraphCone.lean` (`HopsG`, `SiteSuppG`, `growIterG`, `torusAdj`,
`hopsG_latticeDiracHam`); `RecordLayer/UnifiedDiracClock.lean` (`idxPointerShift`,
`hamiltonianFlow_coupledEnergy_reindex`); `RecordLayer/DiracPointerThreshold.lean`
(`pshift_mem_displayArc`, `pshift_notMem_displayArc`); `CV/LiebRobinson.lean`
(`flowRemainder`, `norm_flowRemainder_le_factorial`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The carrier -/

section Carrier

variable {V n : Type*} [Fintype n] [DecidableEq n]

/-- ★★ **An evolved observable against one it has not reached.** For a skew-Hermitian `S`
that hops along the graph, `A` supported on `X`, `B` on `Y`, and `d` steps of growth from `X`
missing `Y`: `‖A(t) B‖ ≤ (2 ‖S‖ t)^d / d! · ‖A‖ ‖B‖` for `t ≥ 0`. -/
theorem norm_heisenbergFlow_mul_graph_le [Nonempty n] {adj : V → V → Prop} {σ : n → V}
    {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsG adj σ S) {X Y : Set V}
    {A B : Matrix n n ℂ} (hA : SiteSuppG σ X A) (hB : SiteSuppG σ Y B) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * B‖ ≤ (2 * ‖S‖ * t) ^ d / d.factorial * ‖A‖ * ‖B‖ := by
  have hsplit : heisenbergFlow S t A
      = (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) + flowRemainder S A d t := by
    rw [flowRemainder]
    abel
  have hsum : (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) * B = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Matrix.smul_mul, mul_eq_zero_of_siteSuppG_disjoint
      (Set.disjoint_of_subset_left (growIterG_mono adj X (Finset.mem_range.1 hj).le) hcone)
      (siteSuppG_adIter hhop hA j) hB, smul_zero]
  rw [hsplit, add_mul, hsum, zero_add]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_flowRemainder_le_factorial hS A d ht) (norm_nonneg _))

omit [DecidableEq n] in
/-- An observable read at a ray whose density matrix `B` fixes may be multiplied by `B`. -/
theorem arenaObs_mul_of_supp {B : Matrix n n ℂ} {p : GenArena n}
    (hp : B * arenaDM p = arenaDM p) (Z : Matrix n n ℂ) :
    arenaObs (Z * B) p = arenaObs Z p := by
  rw [arenaObs, arenaObs, ← Matrix.mul_assoc, Matrix.trace_mul_comm (arenaDM p * Z) B,
    ← Matrix.mul_assoc, hp]

omit [DecidableEq n] in
/-- A vector fixed by `B` gives a ray whose density matrix `B` fixes. -/
theorem mul_arenaDM_mk {B : Matrix n n ℂ} {v : EuclideanSpace ℂ n} (hv : v ≠ 0)
    (hB : (B *ᵥ fun i => v i) = fun i => v i) :
    B * arenaDM (Projectivization.mk ℂ v hv) = arenaDM (Projectivization.mk ℂ v hv) := by
  rw [arenaDM_mk hv, dmVec, Matrix.mul_vecMulVec]
  congr 1
  have hu : unitVec v = (((‖v‖ : ℝ) : ℂ)⁻¹) • fun i => v i := rfl
  rw [hu, Matrix.mulVec_smul, hB]

/-- ★★ **The occupancy of `X` by a carrier that starts on `Y`.** The carrier moves by
`exp (t S)` from a ray whose density matrix is fixed by `B`, supported on `Y`. An observable
`D` on `X`, read at `t ≥ 0`, is at most `(2 ‖S‖ t)^d / d! · ‖D‖ ‖B‖` in size when `d` steps
of growth from `X` miss `Y`. -/
theorem abs_arenaObs_flow_graph_le [Nonempty n] {adj : V → V → Prop} {σ : n → V}
    {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsG adj σ S) {X Y : Set V}
    {D B : Matrix n n ℂ} (hD : SiteSuppG σ X D) (hB : SiteSuppG σ Y B) {p : GenArena n}
    (hp : B * arenaDM p = arenaDM p) {d : ℕ} (hcone : Disjoint (growIterG adj X d) Y)
    {t : ℝ} (ht : 0 ≤ t) {U : Matrix.unitaryGroup n ℂ} (hU : U.val = exp (t • S)) :
    |arenaObs D (arenaKick U p)| ≤ (2 * ‖S‖ * t) ^ d / d.factorial * ‖D‖ * ‖B‖ := by
  rw [arenaObs_kick_conj, hU, star_exp_smul_mul_exp_smul hS t D, ← arenaObs_mul_of_supp hp]
  exact (abs_arenaObs_le _ p).trans (norm_heisenbergFlow_mul_graph_le hS hhop hD hB hcone ht)

end Carrier

/-! ### The pointer -/

section Pointer

variable {V ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ}

omit [Fintype ι] [DecidableEq ι] in
/-- The coupled generator hops along the graph when both of its terms do. -/
theorem hopsG_idxCoupledGen {adj : V → V → Prop} {σ : ι → V} (hA : HopsG adj σ A₀)
    (hB : HopsG adj σ B₀) (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) :
    HopsG adj σ ((-Complex.I) • idxCoupledH A₀ B₀ hf φ) := by
  unfold idxCoupledH
  exact (hA.add (hB.smul _)).smul _

/-- ★★★ **A pointer's displacement before the growth reaches the carrier.** The pointer is
coupled to `B₀`, supported on `X`. The carrier starts at a ray whose density matrix is fixed
by `P`, supported on `Y` with `‖P‖ ≤ 1`. With `d` steps of growth from `X` missing `Y`, on
every fibre and for `t ≥ 0`:
`|shift| ≤ 2 |f'(θ₂)| ‖B₀‖ (2 ‖H‖ t)^d / d! · t`, `H` the coupled Hamiltonian. -/
theorem abs_idxPointerShift_le_graph [Nonempty ι] (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hf : Function.Periodic f 1) {adj : V → V → Prop} {σ : ι → V}
    (hAhop : HopsG adj σ A₀) (hBhop : HopsG adj σ B₀) {X Y : Set V}
    (hBX : SiteSuppG σ X B₀) {P : Matrix ι ι ℂ} (hP : SiteSuppG σ Y P) (hPn : ‖P‖ ≤ 1)
    {p : GenArena ι} (hp : P * arenaDM p = arenaDM p) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) (φ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |idxPointerShift hA hB hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * ‖B₀‖
        * ((2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial) * t := by
  unfold idxPointerShift
  have hS := idxFreeGen_skew (idxCoupledH_isHermitian hA hB hf φ)
  have hT : ∀ s : ℝ, 0 ≤ s →
      0 ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / (d.factorial : ℝ) := fun s hs =>
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) hs) _)
      (Nat.cast_nonneg _)
  have hb : ∀ s, 0 ≤ s → s ≤ t →
      |arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
        ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖ := fun s hs hst => by
    have h1 := abs_arenaObs_flow_graph_le hS (hopsG_idxCoupledGen hAhop hBhop hf φ) hBX hP hp
      hcone hs (idxCarrierU_val hA hB hf φ s)
    rw [norm_neg_I_smul] at h1
    have hmono : (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / (d.factorial : ℝ)
        ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) hs)
          (mul_le_mul_of_nonneg_left hst (mul_nonneg zero_le_two (norm_nonneg _))) d)
        (Nat.cast_nonneg _)
    calc |arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
        ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / d.factorial * ‖B₀‖ * ‖P‖ := h1
      _ ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / d.factorial * ‖B₀‖ * 1 :=
          mul_le_mul_of_nonneg_left hPn (mul_nonneg (hT s hs) (norm_nonneg _))
      _ ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
  have key : ‖∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)‖
      ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖ * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      rw [Set.uIoc_of_le ht] at hs
      exact hb s hs.1.le hs.2
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at key
  rw [abs_mul, abs_mul, abs_neg, abs_two]
  calc 2 * |hf.deriv_periodic.lift φ|
        * |∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
      ≤ 2 * |hf.deriv_periodic.lift φ|
        * ((2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖ * t) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg zero_le_two (abs_nonneg _))
    _ = _ := by ring

/-- ★★ **A pointer's displacement while the carrier is on the detector.** On a fibre with
rate `κ = −2 f'(θ₂) ≥ 0`, if the detector's observable has expectation at least `q` along the
carrier's orbit up to `t ≥ 0`, the displacement is at least `κ q t`. -/
theorem le_idxPointerShift_of_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {p : GenArena ι} {q t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ s, 0 ≤ s → s ≤ t → q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)) :
    -2 * hf.deriv_periodic.lift φ * q * t ≤ idxPointerShift hA hB hf φ p t := by
  unfold idxPointerShift
  have hcont : Continuous fun s : ℝ => arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) :=
    (continuous_arenaObs B₀).comp ((continuous_idxCarrierU hA hB hf φ).arenaKick continuous_const)
  have hint : ∫ _ in (0 : ℝ)..t, q
      ≤ ∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) :=
    intervalIntegral.integral_mono_on ht intervalIntegrable_const (hcont.intervalIntegrable 0 t)
      fun s hs => hq s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  calc -2 * hf.deriv_periodic.lift φ * q * t
      = -2 * hf.deriv_periodic.lift φ * (t * q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hint hκ

/-- On a fibre with rate `κ ≥ 0`, if the detector's observable has expectation at most `1`
along the orbit, the displacement is at most `κ t`. -/
theorem idxPointerShift_le_of_le_one (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {p : GenArena ι} {t : ℝ} (ht : 0 ≤ t)
    (h1 : ∀ s, 0 ≤ s → s ≤ t → arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) ≤ 1) :
    idxPointerShift hA hB hf φ p t ≤ -2 * hf.deriv_periodic.lift φ * t := by
  unfold idxPointerShift
  have hcont : Continuous fun s : ℝ => arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p) :=
    (continuous_arenaObs B₀).comp ((continuous_idxCarrierU hA hB hf φ).arenaKick continuous_const)
  have hint : ∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)
      ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) :=
    intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable 0 t) intervalIntegrable_const
      fun s hs => h1 s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hint
  exact mul_le_mul_of_nonneg_left hint hκ

variable {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- ★★★ **No display before the growth reaches the carrier.** On the arena of a carrier with
Hamiltonian `A₀` and a pointer coupled to `B₀` on the sites `X`: from a ready pointer and a
carrier that starts on `Y`, the pointer is not displayed at the flow time `t ≥ 0` while
`2 |f'(θ₂)| ‖B₀‖ (2 ‖H‖ t)^d / d! · t < 1/6`, `d` steps of growth from `X` missing `Y`. -/
theorem graphDetector_not_displayed [Nonempty ι] (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) {adj : V → V → Prop} {σ : ι → V}
    (hAhop : HopsG adj σ A₀) (hBhop : HopsG adj σ B₀) {X Y : Set V}
    (hBX : SiteSuppG σ X B₀) {P : Matrix ι ι ℂ} (hP : SiteSuppG σ Y P) (hPn : ‖P‖ ≤ 1)
    {p : GenArena ι} (hp : P * arenaDM p = arenaDM p) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ}
    (ht : 0 ≤ t)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * ‖B₀‖
        * ((2 * ‖idxCoupledH A₀ B₀ hf θ.2‖ * t) ^ d / d.factorial) * t < 1 / 6) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∉ displayArc := by
  rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
  exact pshift_notMem_displayArc hθ
    ((abs_idxPointerShift_le_graph hA hB hf hAhop hBhop hBX hP hPn hp hcone θ.2 ht).trans_lt
      hsmall)

/-- ★★ **Display while the carrier is on the detector.** On a fibre with rate
`κ = −2 f'(θ₂) ≥ 0`, from a ready pointer: if the detector's observable has expectation
between `q` and `1` along the carrier's orbit up to `t ≥ 0`, with `1/3 ≤ κ q t` and
`κ t ≤ 2/3`, the pointer is displayed at `t`. -/
theorem graphDetector_displayed (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) {p : GenArena ι} {θ : KTorus}
    (hθ : θ ∈ readyArc 2) (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {q t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ s, 0 ≤ s → s ≤ t →
      q ≤ arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p))
    (h1 : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs B₀ (arenaKick (idxCarrierU hA hB hf θ.2 s) p) ≤ 1)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2 * q * t)
    (hhi : -2 * hf.deriv_periodic.lift θ.2 * t ≤ 2 / 3) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∈ displayArc := by
  rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
  exact pshift_mem_displayArc hθ (hlo.trans (le_idxPointerShift_of_le hA hB hf hκ ht hq))
    ((idxPointerShift_le_of_le_one hA hB hf hκ ht h1).trans hhi)

end Pointer

/-! ### A set of sites, and the torus -/

section SiteSet

variable {V n : Type*} [DecidableEq n]

/-- **The projector on a set of sites**, over a site map. -/
def siteSetProj (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)] : Matrix n n ℂ :=
  Matrix.diagonal fun p => if σ p ∈ X then 1 else 0

theorem siteSetProj_isHermitian (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)] :
    (siteSetProj σ X).IsHermitian := by
  rw [siteSetProj]
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    ext p
    simp only [Pi.star_apply]
    split_ifs <;> simp)

/-- The projector on `X` is supported on `X`. -/
theorem siteSuppG_siteSetProj (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)] :
    SiteSuppG σ X (siteSetProj σ X) := fun p q h => by
  have hpq : p = q := by
    by_contra hne
    exact h (Matrix.diagonal_apply_ne _ hne)
  subst hpq
  rw [siteSetProj, Matrix.diagonal_apply_eq] at h
  have hp : σ p ∈ X := by
    by_contra hn
    exact h (by simp [hn])
  exact ⟨hp, hp⟩

/-- The projector on a set of sites hops nowhere, so it hops along every graph. -/
theorem hopsG_siteSetProj (adj : V → V → Prop) (σ : n → V) (X : Set V)
    [DecidablePred (· ∈ X)] : HopsG adj σ (siteSetProj σ X) := fun p q h => by
  have hpq : p = q := by
    by_contra hne
    exact h (Matrix.diagonal_apply_ne _ hne)
  exact Or.inl (by rw [hpq])

/-- The projector on a set of sites has operator norm at most `1`. -/
theorem norm_siteSetProj_le [Fintype n] (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)] :
    ‖siteSetProj σ X‖ ≤ 1 := by
  rw [siteSetProj]
  exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp

end SiteSet

section Torus

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S] [Nonempty S]
  {L : ℕ} [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ} {f : ℝ → ℝ} {N : ℕ}

/-- ★★★ **A detector on the torus is not displayed before the growth reaches the carrier.**
The carrier is the lattice Dirac field of any dimension. The pointer is coupled with strength
`g` to the projector on a set of sites `X`. The carrier starts at a ray fixed by the projector
on `Y`. With `d` steps of growth on the torus from `X` missing `Y`, a ready pointer is not
displayed at the flow time `t ≥ 0` while
`2 |f'(θ₂)| |g| (2 ‖H‖ t)^d / d! · t < 1/6`, `H` the coupled Hamiltonian. -/
theorem torusDetector_not_displayed (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) (J μ g : ℝ) (hf : Function.Periodic f 1)
    (hc : ContDiff ℝ ∞ f) (X Y : Set (κ → ZMod L)) [DecidablePred (· ∈ X)]
    [DecidablePred (· ∈ Y)] {p : GenArena ((κ → ZMod L) × S)}
    (hp : siteSetProj Prod.fst Y * arenaDM p = arenaDM p) {d : ℕ}
    (hcone : Disjoint (growIterG torusAdj X d) Y) {θ : KTorus} (hθ : θ ∈ readyArc 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * |g|
        * ((2 * ‖idxCoupledH (latticeDiracHam (L := L) α β J μ)
            ((g : ℂ) • siteSetProj Prod.fst X) hf θ.2‖ * t) ^ d / d.factorial) * t < 1 / 6) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e ((g : ℂ) • siteSetProj Prod.fst X)) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∉ displayArc := by
  have hB : ((g : ℂ) • siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L) X).IsHermitian :=
    (siteSetProj_isHermitian _ X).smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hBn : ‖(g : ℂ) • siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L) X‖ ≤ |g| := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg g) (norm_siteSetProj_le _ X)
  refine graphDetector_not_displayed e (latticeDiracHam_isHermitian h J μ) hB hf hc
    (hopsG_latticeDiracHam α β J μ) ((hopsG_siteSetProj torusAdj _ X).smul _)
    (fun a b hab => siteSuppG_siteSetProj _ X a b fun h0 => hab (by
      rw [Matrix.smul_apply, h0, smul_zero]))
    (siteSuppG_siteSetProj _ Y) (norm_siteSetProj_le _ Y) hp hcone hθ ht
    (lt_of_le_of_lt ?_ hsmall)
  have hT : 0 ≤ (2 * ‖idxCoupledH (latticeDiracHam (L := L) α β J μ)
      ((g : ℂ) • siteSetProj Prod.fst X) hf θ.2‖ * t) ^ d / (d.factorial : ℝ) :=
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) ht) _)
      (Nat.cast_nonneg _)
  have h2 : 0 ≤ 2 * |hf.deriv_periodic.lift θ.2| := mul_nonneg zero_le_two (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBn h2) hT) ht

end Torus

end CSD.RecordLayer

end
