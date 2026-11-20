/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusRateBound

/-!
# The graph-distance bound for a carrier that is only mostly on its set of sites

**Category:** 7-SigmaLayer. BACKLOG #297, ninth brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

`RecordLayer/GraphDetector.lean` bounds a detector's pointer before the growth from the
detector reaches the carrier, for a carrier whose ray is fixed by a matrix supported on a set
of sites `Y`. A packet is not of that kind: it has a tail outside any box. Here the
hypothesis is dropped and a term for the tail is added.

* ★★ `abs_arenaObs_mul_le_sqrt` — for a Hermitian idempotent `Q`:
  `|⟨Z Q⟩| ≤ ‖Z‖ √⟨Q⟩` at every ray;
* ★★★ `abs_arenaObs_flow_graph_le_tail` — for a Hermitian idempotent `P` supported on `Y`,
  any ray `p`, and `d` steps of growth from `X` missing `Y`:
  `|⟨D(t)⟩| ≤ (2 ‖S‖ t)^d / d! · ‖D‖ ‖P‖ + ‖D‖ √⟨1 − P⟩`;
* ★★ `abs_idxPointerShift_le_graph_tail`, `graphDetector_not_displayed_tail` — the pointer's
  displacement and the display, with the same added term;
* `siteSetProj_mul_self`, `arenaObs_one_sub` — the projector on a set of sites is idempotent;
  `⟨1 − P⟩ = 1 − ⟨P⟩`;
* ★★★ `torusDetector_not_displayed_tail` — the lattice Dirac field of any dimension, a
  carrier with at least `1 − ε` of its weight on `Y`: a ready pointer is not displayed while
  `2 |f'(θ₂)| |g| ((2 ‖H‖ t)^d / d! + √ε) t < 1/6`, on every fibre;
* ★★★ `torusDetector_not_displayed_flatPacket_tail` — **the flat packet of UD-222 with `Y` the
  box it starts in and `ε = flatTailD` at the flow time `0`.**

## Honest scope

⚠️ **The added term does not go to zero with the distance.** `√ε` is the square root of the
carrier's weight off `Y`; for a pointer of rate `κ` it allows a displacement `κ √ε t`
whatever `d` is. The bound is useful only up to flow times of order `1/(6 κ √ε)`.

⚠️ **An upper bound, a factorial tail**: not an exclusion at a sharp time. The rate is the
norm of the coupled Hamiltonian.

⚠️ **No instance with numbers.** No detector, packet and time are exhibited for which this
bound is the one that binds; for the instance of UD-245 the rate bound of UD-246 already
gives more.

⚠️ **Not composed with the display** of `torusDetector_arrival_box` in one statement.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297; `specs/unified-record-spacetime-plan.md` (UD-231,
UD-246, UD-247); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/GraphDetector.lean` (`norm_heisenbergFlow_mul_graph_le`,
`abs_arenaObs_flow_graph_le`, `abs_idxPointerShift_le_graph`, `torusDetector_not_displayed`,
`siteSetProj`); `CV/LiebRobinson.lean` (`norm_heisenbergFlow_le`);
`RecordLayer/DiracPointerClick.lean` (`arenaObs_mk_eq_inner`);
`RecordLayer/TorusDetector.lean` (`arenaObs_siteSetProj_mk`); `RecordLayer/TorusArrival.lean`
(`flatTailD`); `CV/DiracPacketWindowD.lean`
(`regionWeightD_flatPacket_compl_movedBoxD_le_window`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix Set MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The carrier -/

section Carrier

variable {V n : Type*} [Fintype n] [DecidableEq n]

/-- ★★ **An observable times a projector, at a ray with little weight on the projector.** For
a Hermitian idempotent `Q`: `|⟨Z Q⟩| ≤ ‖Z‖ √⟨Q⟩`. -/
theorem abs_arenaObs_mul_le_sqrt {Z Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (p : GenArena n) : |arenaObs (Z * Q) p| ≤ ‖Z‖ * Real.sqrt (arenaObs Q p) := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hmul : Matrix.toEuclideanLin (Z * Q) v
        = Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v) :=
      DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 Z Q) v
    have hmulQ : Matrix.toEuclideanLin (Q * Q) v
        = Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q v) :=
      DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 Q Q) v
    have hZ : ‖Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v)‖
        ≤ ‖Z‖ * ‖Matrix.toEuclideanLin Q v‖ := by
      have hh : Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v)
          = (EuclideanSpace.equiv n ℂ).symm (Z *ᵥ (Matrix.toEuclideanLin Q v).ofLp) := rfl
      rw [hh]
      exact Matrix.l2_opNorm_mulVec Z _
    have hadj : LinearMap.adjoint (Matrix.toEuclideanLin Q) = Matrix.toEuclideanLin Q := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hQ.eq]
    have hQw : (inner ℂ v (Matrix.toEuclideanLin Q v)).re
        = ‖Matrix.toEuclideanLin Q v‖ ^ 2 := by
      have h1 : inner ℂ v (Matrix.toEuclideanLin Q v)
          = inner ℂ (Matrix.toEuclideanLin Q v) (Matrix.toEuclideanLin Q v) := by
        calc inner ℂ v (Matrix.toEuclideanLin Q v)
            = inner ℂ v (Matrix.toEuclideanLin (Q * Q) v) := by rw [hQQ]
          _ = inner ℂ v (LinearMap.adjoint (Matrix.toEuclideanLin Q)
                (Matrix.toEuclideanLin Q v)) := by rw [hmulQ, hadj]
          _ = inner ℂ (Matrix.toEuclideanLin Q v) (Matrix.toEuclideanLin Q v) :=
              LinearMap.adjoint_inner_right _ _ _
      rw [h1, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [arenaObs_mk_eq_inner, arenaObs_mk_eq_inner, hmul, hQw]
    have hsq : Real.sqrt (‖Matrix.toEuclideanLin Q v‖ ^ 2 / ‖v‖ ^ 2)
        = ‖Matrix.toEuclideanLin Q v‖ / ‖v‖ := by
      rw [← div_pow, Real.sqrt_sq (div_nonneg (norm_nonneg _) hv0.le)]
    have hin : |(inner ℂ v (Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v))).re|
        ≤ ‖v‖ * (‖Z‖ * ‖Matrix.toEuclideanLin Q v‖) :=
      (Complex.abs_re_le_norm _).trans
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hZ (norm_nonneg _)))
    rw [hsq, abs_div, abs_of_pos (pow_pos hv0 2), div_le_iff₀ (pow_pos hv0 2)]
    calc |(inner ℂ v (Matrix.toEuclideanLin Z (Matrix.toEuclideanLin Q v))).re|
        ≤ ‖v‖ * (‖Z‖ * ‖Matrix.toEuclideanLin Q v‖) := hin
      _ = ‖Z‖ * (‖Matrix.toEuclideanLin Q v‖ / ‖v‖) * ‖v‖ ^ 2 := by
          field_simp

/-- ★★★ **The occupancy of `X` by a carrier that starts mostly on `Y`.** The carrier moves by
`exp (t S)` from any ray `p`. For a Hermitian idempotent `P` supported on `Y`, an observable
`D` on `X`, read at `t ≥ 0`, is at most
`(2 ‖S‖ t)^d / d! · ‖D‖ ‖P‖ + ‖D‖ √⟨1 − P⟩` in size when `d` steps of growth from `X` miss
`Y`. -/
theorem abs_arenaObs_flow_graph_le_tail [Nonempty n] {adj : V → V → Prop} {σ : n → V}
    {S : Matrix n n ℂ} (hS : Sᴴ = -S) (hhop : HopsG adj σ S) {X Y : Set V}
    {D P : Matrix n n ℂ} (hD : SiteSuppG σ X D) (hP : SiteSuppG σ Y P) (hPh : P.IsHermitian)
    (hPP : P * P = P) (p : GenArena n) {d : ℕ} (hcone : Disjoint (growIterG adj X d) Y)
    {t : ℝ} (ht : 0 ≤ t) {U : Matrix.unitaryGroup n ℂ} (hU : U.val = exp (t • S)) :
    |arenaObs D (arenaKick U p)|
      ≤ (2 * ‖S‖ * t) ^ d / d.factorial * ‖D‖ * ‖P‖
        + ‖D‖ * Real.sqrt (arenaObs (1 - P) p) := by
  rw [arenaObs_kick_conj, hU, star_exp_smul_mul_exp_smul hS t D]
  have hQh : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPh
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
      sub_zero]
  have hsplit : arenaObs (heisenbergFlow S t D) p
      = arenaObs (heisenbergFlow S t D * P) p
        + arenaObs (heisenbergFlow S t D * (1 - P)) p := by
    rw [← arenaObs_add, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (abs_arenaObs_le _ p).trans (norm_heisenbergFlow_mul_graph_le hS hhop hD hP hcone ht)
  · exact (abs_arenaObs_mul_le_sqrt hQh hQQ p).trans
      (mul_le_mul_of_nonneg_right (norm_heisenbergFlow_le hS t D) (Real.sqrt_nonneg _))

end Carrier

/-! ### The pointer -/

section Pointer

variable {V ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {A₀ B₀ : Matrix ι ι ℂ}

/-- ★★ **A pointer's displacement before the growth reaches a carrier that is mostly on
`Y`.** With `P` a Hermitian idempotent supported on `Y`, `‖P‖ ≤ 1`, and `d` steps of growth
from `X` missing `Y`, on every fibre, for every ray `p` and `t ≥ 0`:
`|shift| ≤ 2 |f'(θ₂)| ‖B₀‖ ((2 ‖H‖ t)^d / d! + √⟨1 − P⟩) t`. -/
theorem abs_idxPointerShift_le_graph_tail [Nonempty ι] (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hf : Function.Periodic f 1) {adj : V → V → Prop} {σ : ι → V}
    (hAhop : HopsG adj σ A₀) (hBhop : HopsG adj σ B₀) {X Y : Set V}
    (hBX : SiteSuppG σ X B₀) {P : Matrix ι ι ℂ} (hP : SiteSuppG σ Y P) (hPn : ‖P‖ ≤ 1)
    (hPh : P.IsHermitian) (hPP : P * P = P) (p : GenArena ι) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) (φ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |idxPointerShift hA hB hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * ‖B₀‖
        * ((2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial
          + Real.sqrt (arenaObs (1 - P) p)) * t := by
  unfold idxPointerShift
  have hS := idxFreeGen_skew (idxCoupledH_isHermitian hA hB hf φ)
  have hT : ∀ s : ℝ, 0 ≤ s →
      0 ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / (d.factorial : ℝ) := fun s hs =>
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) hs) _)
      (Nat.cast_nonneg _)
  have hb : ∀ s, 0 ≤ s → s ≤ t →
      |arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
        ≤ ((2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial
          + Real.sqrt (arenaObs (1 - P) p)) * ‖B₀‖ := fun s hs hst => by
    have h1 := abs_arenaObs_flow_graph_le_tail hS (hopsG_idxCoupledGen hAhop hBhop hf φ) hBX hP
      hPh hPP p hcone hs (idxCarrierU_val hA hB hf φ s)
    rw [norm_neg_I_smul] at h1
    have hmono : (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / (d.factorial : ℝ)
        ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) hs)
          (mul_le_mul_of_nonneg_left hst (mul_nonneg zero_le_two (norm_nonneg _))) d)
        (Nat.cast_nonneg _)
    have h2 : (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / d.factorial * ‖B₀‖ * ‖P‖
        ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖ :=
      calc (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / d.factorial * ‖B₀‖ * ‖P‖
          ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / d.factorial * ‖B₀‖ * 1 :=
            mul_le_mul_of_nonneg_left hPn (mul_nonneg (hT s hs) (norm_nonneg _))
        _ ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖ := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
    calc |arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
        ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * s) ^ d / d.factorial * ‖B₀‖ * ‖P‖
          + ‖B₀‖ * Real.sqrt (arenaObs (1 - P) p) := h1
      _ ≤ (2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial * ‖B₀‖
          + ‖B₀‖ * Real.sqrt (arenaObs (1 - P) p) := by linarith
      _ = _ := by ring
  have key : ‖∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)‖
      ≤ ((2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial
          + Real.sqrt (arenaObs (1 - P) p)) * ‖B₀‖ * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      rw [Set.uIoc_of_le ht] at hs
      exact hb s hs.1.le hs.2
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at key
  rw [abs_mul, abs_mul, abs_neg, abs_two]
  calc 2 * |hf.deriv_periodic.lift φ|
        * |∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxCarrierU hA hB hf φ s) p)|
      ≤ 2 * |hf.deriv_periodic.lift φ|
        * (((2 * ‖idxCoupledH A₀ B₀ hf φ‖ * t) ^ d / d.factorial
          + Real.sqrt (arenaObs (1 - P) p)) * ‖B₀‖ * t) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg zero_le_two (abs_nonneg _))
    _ = _ := by ring

variable {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- ★★ **No display before the growth reaches a carrier that is mostly on `Y`.** From a ready
pointer, on any fibre and for any ray `p`, the pointer is not displayed at the flow time
`t ≥ 0` while `2 |f'(θ₂)| ‖B₀‖ ((2 ‖H‖ t)^d / d! + √⟨1 − P⟩) t < 1/6`. -/
theorem graphDetector_not_displayed_tail [Nonempty ι] (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    {adj : V → V → Prop} {σ : ι → V} (hAhop : HopsG adj σ A₀) (hBhop : HopsG adj σ B₀)
    {X Y : Set V} (hBX : SiteSuppG σ X B₀) {P : Matrix ι ι ℂ} (hP : SiteSuppG σ Y P)
    (hPn : ‖P‖ ≤ 1) (hPh : P.IsHermitian) (hPP : P * P = P) (p : GenArena ι) {d : ℕ}
    (hcone : Disjoint (growIterG adj X d) Y) {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ}
    (ht : 0 ≤ t)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * ‖B₀‖
        * ((2 * ‖idxCoupledH A₀ B₀ hf θ.2‖ * t) ^ d / d.factorial
          + Real.sqrt (arenaObs (1 - P) p)) * t < 1 / 6) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc) t
        (idxArenaEquiv e p, θ)).2 ∉ displayArc := by
  rw [hamiltonianFlow_coupledEnergy_reindex e hA hB hf hc]
  exact pshift_notMem_displayArc hθ
    ((abs_idxPointerShift_le_graph_tail hA hB hf hAhop hBhop hBX hP hPn hPh hPP p hcone θ.2
      ht).trans_lt hsmall)

end Pointer

/-! ### A set of sites -/

section SiteSet

variable {V n : Type*} [Fintype n] [DecidableEq n]

/-- The projector on a set of sites is idempotent. -/
theorem siteSetProj_mul_self (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)] :
    siteSetProj σ X * siteSetProj σ X = siteSetProj σ X := by
  rw [siteSetProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext q
  split_ifs <;> simp

/-- `⟨1 − P⟩ = 1 − ⟨P⟩`. -/
theorem arenaObs_one_sub (P : Matrix n n ℂ) (p : GenArena n) :
    arenaObs (1 - P) p = 1 - arenaObs P p := by
  have h := arenaObs_add (1 - P) P p
  rw [sub_add_cancel, arenaObs_one] at h
  linarith

end SiteSet

/-! ### The torus -/

section Torus

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S] [Nonempty S]
  {L : ℕ} [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ} {f : ℝ → ℝ} {N : ℕ}

/-- ★★★ **A detector on the torus is not displayed before the growth reaches a carrier that
is mostly on `Y`.** The carrier is the lattice Dirac field of any dimension, at any ray with
at least `1 − ε` of its weight on the sites `Y`. The pointer is coupled with strength `g` to
the projector on `X`. With `d` steps of growth on the torus from `X` missing `Y`, a ready
pointer is not displayed at the flow time `t ≥ 0`, on any fibre, while
`2 |f'(θ₂)| |g| ((2 ‖H‖ t)^d / d! + √ε) t < 1/6`, `H` the coupled Hamiltonian. -/
theorem torusDetector_not_displayed_tail (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) (J μ g : ℝ) (hf : Function.Periodic f 1)
    (hc : ContDiff ℝ ∞ f) (X Y : Set (κ → ZMod L)) [DecidablePred (· ∈ X)]
    [DecidablePred (· ∈ Y)] (p : GenArena ((κ → ZMod L) × S)) {ε : ℝ}
    (hw : 1 - ε ≤ arenaObs (siteSetProj Prod.fst Y) p) {d : ℕ}
    (hcone : Disjoint (growIterG torusAdj X d) Y) {θ : KTorus} (hθ : θ ∈ readyArc 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * |g|
        * ((2 * ‖idxCoupledH (latticeDiracHam (L := L) α β J μ)
            ((g : ℂ) • siteSetProj Prod.fst X) hf θ.2‖ * t) ^ d / d.factorial
          + Real.sqrt ε) * t < 1 / 6) :
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
  refine graphDetector_not_displayed_tail e (latticeDiracHam_isHermitian h J μ) hB hf hc
    (hopsG_latticeDiracHam α β J μ) ((hopsG_siteSetProj torusAdj _ X).smul _)
    (fun a b hab => siteSuppG_siteSetProj _ X a b fun h0 => hab (by
      rw [Matrix.smul_apply, h0, smul_zero]))
    (siteSuppG_siteSetProj _ Y) (norm_siteSetProj_le _ Y) (siteSetProj_isHermitian _ Y)
    (siteSetProj_mul_self _ Y) p hcone hθ ht (lt_of_le_of_lt ?_ hsmall)
  have hT : 0 ≤ (2 * ‖idxCoupledH (latticeDiracHam (L := L) α β J μ)
      ((g : ℂ) • siteSetProj Prod.fst X) hf θ.2‖ * t) ^ d / (d.factorial : ℝ) :=
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) ht) _)
      (Nat.cast_nonneg _)
  have h2 : 0 ≤ 2 * |hf.deriv_periodic.lift θ.2| := mul_nonneg zero_le_two (abs_nonneg _)
  have hsq : Real.sqrt (arenaObs
      (1 - siteSetProj (Prod.fst : (κ → ZMod L) × S → κ → ZMod L) Y) p) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt (by rw [arenaObs_one_sub]; linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hBn h2) (add_le_add le_rfl hsq)
      (add_nonneg hT (Real.sqrt_nonneg _)) (mul_nonneg h2 (abs_nonneg g))) ht

/-- ★★★ **The flat packet.** The carrier is the flat packet of the lattice Dirac field, `Y`
the box of arcs it starts in. With `d` steps of growth from the detector's sites `X` missing
that box, a ready pointer is not displayed at the flow time `t ≥ 0`, on any fibre, while
`2 |f'(θ₂)| |g| ((2 ‖H‖ t)^d / d! + √ε₀) t < 1/6`, `ε₀` the packet's tail `flatTailD` at the
flow time `0`. -/
theorem torusDetector_not_displayed_flatPacket_tail (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (g : ℝ) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Set (κ → ZMod L)) [DecidablePred (· ∈ X)] {d : ℕ}
    (hcone : Disjoint (growIterG torusAdj X d)
      (movedBoxD L J μ k₀ (fun _ => 1) γ 0 : Set (κ → ZMod L)))
    {θ : KTorus} (hθ : θ ∈ readyArc 2) {t : ℝ} (ht : 0 ≤ t)
    (hsmall : 2 * |hf.deriv_periodic.lift θ.2| * |g|
        * ((2 * ‖idxCoupledH (latticeDiracHam (L := L) α β J μ)
            ((g : ℂ) • siteSetProj Prod.fst X) hf θ.2‖ * t) ^ d / d.factorial
          + Real.sqrt (flatTailD L J μ Nw w γ 0)) * t < 1 / 6) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e ((g : ℂ) • siteSetProj Prod.fst X)) hf hc) t
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  have hnorm : (chainInnerD
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) 0)
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) 0)).re
        = 1 := by
    rw [chainInnerD_packetD_unitAmpD h he hn hμ hD, sum_flatAmpD_sq lo hN, Complex.ofReal_re]
  have hsplit := regionWeightD_add_compl (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
    (unitAmpD L J μ (flatAmpD lo Nw)) 0) (movedBoxD L J μ k₀ (fun _ => 1) γ 0)
  rw [hnorm] at hsplit
  have hcompl : regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0) (movedBoxD L J μ k₀ (fun _ => 1) γ 0)ᶜ
      ≤ flatTailD L J μ Nw w γ 0 := by
    have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
      lo hN hNL k₀ hw0 hw 0 hγ
    rw [abs_of_nonneg le_rfl] at hh
    rw [flatTailD]
    exact hh
  have hv1 : ‖(WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S))‖ ^ 2
      = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact (re_chainInnerD_self _).symm.trans hnorm
  have hobs : arenaObs (siteSetProj Prod.fst
        (movedBoxD L J μ k₀ (fun _ => 1) γ 0 : Set (κ → ZMod L)))
        (Projectivization.mk ℂ _ hp)
      = regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0) (movedBoxD L J μ k₀ (fun _ => 1) γ 0) := by
    rw [arenaObs_siteSetProj_mk _ hp, hv1, div_one]
  exact torusDetector_not_displayed_tail e h J μ g hf hc X
    (movedBoxD L J μ k₀ (fun _ => 1) γ 0 : Set (κ → ZMod L)) (Projectivization.mk ℂ _ hp)
    (by rw [hobs]; linarith) hcone hθ ht hsmall

end Torus

end CSD.RecordLayer

end
