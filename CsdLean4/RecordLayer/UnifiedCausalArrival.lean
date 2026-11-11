/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCausalOrder
public import CsdLean4.RecordLayer.DiracPointerClick

/-!
# A response that arrives: the leading term of a pointer's response to a kick

**Category:** 7-SigmaLayer (the record layer). BACKLOG #362 — the author's programme "From `Σ` to
physical spacetime", milestone M5, condition (e2) of obligation UO-15 and Remainder (a) of #361.
`RecordLayer/UnifiedCausalOrder.lean` bounds a pointer's response to a remote kick from above.
Nothing there shows a response that is not zero. This module gives the response its leading
term, with an error of the next order, and computes that term for one carrier and one kick at
the site next to the detector's.

**The expansion** (any finite index, any skew-Hermitian generator). Let the first `d` iterated
commutators of `D` with `S` commute with the kick `W`. Then the response of the occupancy at
time `s ≥ 0` is its `d`-th Taylor term up to the next tail:

  `|(⟨D⟩ kicked − ⟨D⟩ unkicked)(s) − c_d(s) · Δ_d| ≤ 2 (2 ‖S‖ s)^(d+1) / (d+1)! · ‖D‖`,

with `c_d(s) = (−1)^d s^d / d!` (`flowCoef`) and `Δ_d` the change the kick makes in the
expectation of `ad_S^d D` at time `0` (`abs_arenaObs_flow_kick_sub_sub_le`). When `d` steps of
growth from the support of `D` reach the kick's set and `d − 1` do not, the hypothesis holds by
support (`commute_adIter_of_disjoint_growIter`). Integrated in time, a displacement
`−2 g c ∫₀ᵗ ⟨D⟩` with `‖D‖ ≤ 1` responds by

  `−2 g c · (−1)^d t^(d+1) / (d+1)! · Δ_d`

up to `4 |g| |c| (2 ‖S‖ t)^(d+1) / (d+1)! · t` (`abs_displacement_kick_sub_sub_le`).

**The kick.** `siteSignKick σ y` multiplies the amplitudes over the site `y` by `−1` and leaves
the others alone. It is the identity off `{y}` (`idOffOn_siteSignKick`).

**The instance: two site pointers, the kick one site from the second detector.** The carrier is
the ray of `e_(k,1) + e_(k−1,0)` (`arrivalRay`), an equal superposition over the detector's site
`k` and its neighbour. The kick is `siteSignKick Prod.fst (k − 1)`. It carries that ray to the
ray of `e_(k,1) − e_(k−1,0)` (`arenaKick_siteSignKick_arrivalRay`). The current into site `k`
changes by `2 J` (`arenaObs_adOne_diracTwoGen_arrivalRay_sub`), `J` the hopping strength. So for
every pair of pointer angles and every `t ≥ 0`:

  `|response of the second pointer − 2 g₂ h'(χ) J t²| ≤ 8 |g₂| |h'(χ)| ‖H‖² t³`

(`abs_diracTwoKickResponseSnd_sub_le`), and the response is at least
`2 |g₂| |h'(χ)| t² (|J| − 4 ‖H‖² t)` in size (`le_abs_diracTwoKickResponseSnd`). It is not zero
for `0 < t` with `4 ‖H‖² t < |J|` when `g₂ h'(χ) ≠ 0` (`diracTwoKickResponseSnd_ne_zero`).

## Exact scope

* **Distance one.** The kick is at the site next to the detector's. At that distance the cone
  bound of #361 holds with `d = 0` only, and it is `4 |g₂| |h'(χ)| t`. The response found here
  is of order `t²`, below it. For a kick `d` sites away the expansion gives the order `t^(d+1)`
  with coefficient `Δ_d`, and `Δ_d` is not computed here for `d ≥ 2`.
* **One carrier and one kick.** The carrier is a stated superposition over two sites and the
  kick a stated sign. No statement is made about other carriers or kicks. For a carrier on one
  site this kick changes nothing: it is a phase of the whole ray.
* **Short times.** The lower bound is positive for `t < |J| / (4 ‖H‖²)`. Nothing is said about
  later times.
* **A displacement, not a record.** No readout is on this arena (#361 Remainder (c)). The
  statement is that the pointer's moving angle differs between the two runs.
* **The intervention is assumed** (UA-14): a change of the initial ray, not a term of the joint
  energy. All times are flow times (UA-7).
* **No order is built.** A response that arrives from the neighbouring site does not define a
  relation between record events.
* **The ring has at least three sites**, stated as `k − 1 ≠ k + 1`. On a ring of two sites the
  two hops cancel in `diracHam`.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-8, UA-13, UA-14, UO-15 (e2), UD-82, UD-83); `RecordLayer/UnifiedCausalOrder.lean`
(`abs_diracTwoKickResponseSnd_le`, `norm_commutator_heisenbergFlow_le_of_adIter_commute`,
`commute_of_siteSuppOn_idOffOn`, `siteSuppOn_adIter`, `star_exp_smul_mul_exp_smul`);
`CV/LiebRobinson.lean` (`flowCoef`, `flowRemainder`, `norm_flowRemainder_le_factorial`);
`RecordLayer/DiracPointerClick.lean` (`pairRay`, `arenaObs_pairRay`);
`RecordLayer/UnifiedTwoPointer.lean` (`diracTwoH`, `diracTwoShiftSnd`,
`diracTwoPointerFlow_apply`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The expansion -/

section Expansion

variable {L : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- An observable that commutes with a kick has the same expectation after it. -/
theorem arenaObs_kick_of_commute {A : Matrix n n ℂ} {W : Matrix.unitaryGroup n ℂ}
    (hcomm : A * W.val = W.val * A) (p : GenArena n) :
    arenaObs A (arenaKick W p) = arenaObs A p := by
  rw [arenaObs_kick_conj]
  have hWW : star W.val * W.val = 1 := by
    have hmem := W.property
    rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hWW, Matrix.one_mul]

omit [DecidableEq n] in
/-- The expectation of a real multiple, for the real scalar action. -/
theorem arenaObs_smul_real (r : ℝ) (A : Matrix n n ℂ) (p : GenArena n) :
    arenaObs (r • A) p = r * arenaObs A p := by
  rw [← arenaObs_real_smul, Complex.coe_smul]

/-- An expectation is at most the operator norm. -/
theorem abs_arenaObs_le [Nonempty n] (A : Matrix n n ℂ) (p : GenArena n) :
    |arenaObs A p| ≤ ‖A‖ := by
  have h := arenaObs_sub_le A 0 p
  have h0 : arenaObs (0 : Matrix n n ℂ) p = 0 := by simp [arenaObs]
  rwa [h0, sub_zero, sub_zero] at h

/-- The iterated commutators that have not reached the kick's set commute with the kick. -/
theorem commute_adIter_of_disjoint_growIter {σ : n → ZMod L} {S D : Matrix n n ℂ}
    (hhop : HopsOne σ S) {X Y : Finset (ZMod L)} (hD : SiteSuppOn σ X D) {W : Matrix n n ℂ}
    (hW : IdOffOn σ Y W) {d : ℕ} (hcone : ∀ j < d, Disjoint (growIter X j) Y) :
    ∀ j < d, adIter S j D * W = W * adIter S j D := fun j hj =>
  commute_of_siteSuppOn_idOffOn (hcone j hj) (siteSuppOn_adIter hhop hD j) hW

/-- ★★ **The response of an occupancy to a kick, with its leading term.** If the first `d`
iterated commutators of `D` with the skew-Hermitian generator `S` commute with the kick `W`,
the response at time `s ≥ 0` is `flowCoef s d` times the change the kick makes in the
expectation of `ad_S^d D`, up to `2 (2 ‖S‖ s)^(d+1) / (d+1)! · ‖D‖`. -/
theorem abs_arenaObs_flow_kick_sub_sub_le [Nonempty n] {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    (D : Matrix n n ℂ) {W : Matrix.unitaryGroup n ℂ} {d : ℕ}
    (hcomm : ∀ j < d, adIter S j D * W.val = W.val * adIter S j D) {s : ℝ} (hs : 0 ≤ s)
    {U : Matrix.unitaryGroup n ℂ} (hU : U.val = exp (s • S)) (p : GenArena n) :
    |(arenaObs D (arenaKick U (arenaKick W p)) - arenaObs D (arenaKick U p))
        - flowCoef s d * (arenaObs (adIter S d D) (arenaKick W p) - arenaObs (adIter S d D) p)|
      ≤ 2 * ((2 * ‖S‖ * s) ^ (d + 1) / (d + 1).factorial) * ‖D‖ := by
  have hflow : ∀ q : GenArena n,
      arenaObs D (arenaKick U q) = arenaObs (heisenbergFlow S s D) q := fun q => by
    rw [arenaObs_kick_conj, hU, star_exp_smul_mul_exp_smul hS s D]
  have hsplit : heisenbergFlow S s D
      = (∑ j ∈ Finset.range d, flowCoef s j • adIter S j D) + flowCoef s d • adIter S d D
        + flowRemainder S D (d + 1) s := by
    rw [flowRemainder, Finset.sum_range_succ]
    abel
  have hsum : (∑ j ∈ Finset.range d, flowCoef s j • adIter S j D) * W.val
      = W.val * ∑ j ∈ Finset.range d, flowCoef s j • adIter S j D := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm j (Finset.mem_range.1 hj)]
  have hexp : ∀ q : GenArena n, arenaObs (heisenbergFlow S s D) q
      = arenaObs (∑ j ∈ Finset.range d, flowCoef s j • adIter S j D) q
        + flowCoef s d * arenaObs (adIter S d D) q
        + arenaObs (flowRemainder S D (d + 1) s) q := fun q => by
    rw [hsplit, arenaObs_add, arenaObs_add, arenaObs_smul_real]
  have hrem := norm_flowRemainder_le_factorial hS D (d + 1) hs
  have h1 := abs_arenaObs_le (flowRemainder S D (d + 1) s) (arenaKick W p)
  have h2 := abs_arenaObs_le (flowRemainder S D (d + 1) s) p
  rw [hflow, hflow, hexp, hexp, arenaObs_kick_of_commute hsum p]
  have hid : ∀ a b c e f : ℝ, (a + b + c - (a + e + f)) - (b - e) = c - f := fun _ _ _ _ _ => by
    ring
  have hmul : flowCoef s d * (arenaObs (adIter S d D) (arenaKick W p) - arenaObs (adIter S d D) p)
      = flowCoef s d * arenaObs (adIter S d D) (arenaKick W p)
        - flowCoef s d * arenaObs (adIter S d D) p := mul_sub _ _ _
  rw [hmul, hid]
  calc |arenaObs (flowRemainder S D (d + 1) s) (arenaKick W p)
          - arenaObs (flowRemainder S D (d + 1) s) p|
      ≤ |arenaObs (flowRemainder S D (d + 1) s) (arenaKick W p)|
        + |arenaObs (flowRemainder S D (d + 1) s) p| := abs_sub _ _
    _ ≤ ‖flowRemainder S D (d + 1) s‖ + ‖flowRemainder S D (d + 1) s‖ := add_le_add h1 h2
    _ ≤ 2 * ((2 * ‖S‖ * s) ^ (d + 1) / (d + 1).factorial * ‖D‖) := by linarith
    _ = _ := by ring

/-- The integral of the Taylor coefficient: `∫₀ᵗ (−1)^d s^d / d! = (−1)^d t^(d+1) / (d+1)!`. -/
theorem integral_flowCoef (d : ℕ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, flowCoef s d = (-1 : ℝ) ^ d / (d + 1).factorial * t ^ (d + 1) := by
  simp only [flowCoef]
  rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  have h1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (d.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- ★★ **A displacement's response to a kick, with its leading term.** A displacement
`−2 g c ∫₀ᵗ ⟨D⟩` with `‖D‖ ≤ 1` responds to the kick by
`−2 g c · (−1)^d t^(d+1) / (d+1)! · Δ_d` up to `4 |g| |c| (2 ‖S‖ t)^(d+1) / (d+1)! · t`, where
`Δ_d` is the change the kick makes in the expectation of `ad_S^d D`. -/
theorem abs_displacement_kick_sub_sub_le [Nonempty n] {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    {D : Matrix n n ℂ} (hDn : ‖D‖ ≤ 1) {W : Matrix.unitaryGroup n ℂ} {d : ℕ}
    (hcomm : ∀ j < d, adIter S j D * W.val = W.val * adIter S j D)
    {U : ℝ → Matrix.unitaryGroup n ℂ} (hUc : Continuous U) (hU : ∀ s, (U s).val = exp (s • S))
    (g c : ℝ) (p : GenArena n) {t : ℝ} (ht : 0 ≤ t) :
    |(-(2 * g) * c * (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
          - -(2 * g) * c * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
        - -(2 * g) * c * ((-1 : ℝ) ^ d / (d + 1).factorial * t ^ (d + 1)
            * (arenaObs (adIter S d D) (arenaKick W p) - arenaObs (adIter S d D) p))|
      ≤ 4 * |g| * |c| * ((2 * ‖S‖ * t) ^ (d + 1) / (d + 1).factorial) * t := by
  set Δ : ℝ := arenaObs (adIter S d D) (arenaKick W p) - arenaObs (adIter S d D) p with hΔ
  have hF : Continuous fun s : ℝ => arenaObs D (arenaKick (U s) (arenaKick W p)) :=
    (continuous_arenaObs D).comp (hUc.arenaKick continuous_const)
  have hG : Continuous fun s : ℝ => arenaObs D (arenaKick (U s) p) :=
    (continuous_arenaObs D).comp (hUc.arenaKick continuous_const)
  have hcoef : Continuous fun s : ℝ => flowCoef s d * Δ := by
    simp only [flowCoef]
    fun_prop
  have hT : 0 ≤ (2 * ‖S‖ * t) ^ (d + 1) / ((d + 1).factorial : ℝ) :=
    div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) ht) _)
      (Nat.cast_nonneg _)
  have hpt : ∀ s, 0 ≤ s → s ≤ t →
      |(arenaObs D (arenaKick (U s) (arenaKick W p)) - arenaObs D (arenaKick (U s) p))
          - flowCoef s d * Δ| ≤ 2 * ((2 * ‖S‖ * t) ^ (d + 1) / (d + 1).factorial) := by
    intro s hs hst
    refine (abs_arenaObs_flow_kick_sub_sub_le hS D hcomm hs (hU s) p).trans ?_
    have hmono : (2 * ‖S‖ * s) ^ (d + 1) / ((d + 1).factorial : ℝ)
        ≤ (2 * ‖S‖ * t) ^ (d + 1) / ((d + 1).factorial : ℝ) := by gcongr
    have hTs : 0 ≤ (2 * ‖S‖ * s) ^ (d + 1) / ((d + 1).factorial : ℝ) :=
      div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) hs) _)
        (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hDn (mul_nonneg zero_le_two hTs)
    linarith
  have hFG : Continuous fun s : ℝ =>
      arenaObs D (arenaKick (U s) (arenaKick W p)) - arenaObs D (arenaKick (U s) p) :=
    hF.sub hG
  have hint := abs_integral_sub_integral_le_of_abs_sub_le hFG hcoef ht hpt
  rw [intervalIntegral.integral_sub (hF.intervalIntegrable 0 t) (hG.intervalIntegrable 0 t),
    intervalIntegral.integral_mul_const, integral_flowCoef] at hint
  have hfac : (-(2 * g) * c * (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
          - -(2 * g) * c * ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
        - -(2 * g) * c * ((-1 : ℝ) ^ d / (d + 1).factorial * t ^ (d + 1) * Δ)
      = -(2 * g) * c * (((∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
          - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
        - (-1 : ℝ) ^ d / (d + 1).factorial * t ^ (d + 1) * Δ) := by ring
  rw [hfac, abs_mul, abs_mul, abs_neg, abs_mul, abs_two]
  generalize (2 * ‖S‖ * t) ^ (d + 1) / ((d + 1).factorial : ℝ) = T at hint hT ⊢
  calc 2 * |g| * |c| * |((∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) (arenaKick W p)))
            - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
          - (-1 : ℝ) ^ d / (d + 1).factorial * t ^ (d + 1) * Δ|
      ≤ 2 * |g| * |c| * (2 * T * t) :=
        mul_le_mul_of_nonneg_left hint
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg _)) (abs_nonneg _))
    _ = 4 * |g| * |c| * T * t := by ring

end Expansion

/-! ### The sign kick at a site -/

section SignKick

variable {L : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- **The sign kick at the site `y`**: the amplitudes over `y` are multiplied by `−1`. -/
noncomputable def siteSignKick (σ : n → ZMod L) (y : ZMod L) : Matrix.unitaryGroup n ℂ :=
  ⟨Matrix.diagonal fun x => if σ x = y then (-1 : ℂ) else 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    by_cases h : σ x = y <;> simp [h]⟩

theorem siteSignKick_val (σ : n → ZMod L) (y : ZMod L) :
    (siteSignKick σ y).val = Matrix.diagonal fun x => if σ x = y then (-1 : ℂ) else 1 :=
  rfl

/-- The sign kick at `y` is the identity off `{y}`. -/
theorem idOffOn_siteSignKick (σ : n → ZMod L) (y : ZMod L) :
    IdOffOn σ {y} (siteSignKick σ y).val := by
  intro p q h
  rw [siteSignKick_val, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    have hp : σ p ≠ y := by
      rcases h with h | h <;> exact fun e => h (Finset.mem_singleton.2 e)
    simp [hp]
  · simp [hpq]

end SignKick

/-! ### Two site pointers: a kick at the neighbouring site arrives -/

section DiracTwo

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (j k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The two indices of the carrier: the lower component at `k` and the upper at `k − 1`. -/
theorem arrival_ne (k : ZMod (M + 1)) :
    ((k, 1) : ZMod (M + 1) × Fin 2) ≠ (k - 1, 0) := fun h => by
  have := congrArg Prod.snd h
  simp at this

/-- **The carrier of the instance**: the ray of `e_(k,1) + e_(k−1,0)`. -/
noncomputable def arrivalRay (k : ZMod (M + 1)) : GenArena (ZMod (M + 1) × Fin 2) :=
  pairRay (arrival_ne k) 1

/-- The sign kick at `k − 1` carries the ray of `e_(k,1) + e_(k−1,0)` to the ray of
`e_(k,1) − e_(k−1,0)`. -/
theorem arenaKick_siteSignKick_arrivalRay {k : ZMod (M + 1)} (hk : k - 1 ≠ k) :
    arenaKick (siteSignKick Prod.fst (k - 1)) (arrivalRay k) = pairRay (arrival_ne k) (-1) := by
  rw [arrivalRay, pairRay, arenaKick_mk, pairRay]
  congr 1
  ext x
  rw [toEuclideanLin_coord, siteSignKick_val, Matrix.mulVec_diagonal]
  have hk' : k ≠ k - 1 := fun e => hk e.symm
  by_cases h1 : x = (k, 1)
  · subst h1
    simp [pairVec, hk']
  · by_cases h2 : x = (k - 1, 0)
    · subst h2
      simp [pairVec]
    ·       simp [pairVec, h1, h2]

/-- A matrix element between two basis vectors. -/
theorem inner_single_toEuclideanLin_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (a b : ι) :
    inner ℂ (EuclideanSpace.single a (1 : ℂ))
        (Matrix.toEuclideanLin A (EuclideanSpace.single b (1 : ℂ))) = A a b := by
  rw [EuclideanSpace.inner_single_left, toEuclideanLin_coord]
  simp [Matrix.mulVec, dotProduct]

/-- An entry of a commutator with a diagonal matrix. -/
theorem adOne_diagonal_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (v : ι → ℂ) (a b : ι) : adOne G (Matrix.diagonal v) a b = G a b * v b - v a * G a b := by
  rw [adOne, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The coupled generator between `(k, 1)` and `(k − 1, 0)`: `J`. -/
theorem diracTwoGen_apply_arrival (hk : k - 1 ≠ k + 1)
    (φ χ : AddCircle (1 : ℝ)) :
    ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) (k, 1) (k - 1, 0) = (J : ℂ) := by
  have h1 : ¬ k - 1 = k + 1 := hk
  have h2 : ¬ k - 1 = k := fun e => hk (by
    have h0 : (1 : ZMod (M + 1)) = 0 := by
      have := congrArg (fun z => k - z) e
      simpa using this
    rw [sub_eq_add_neg, h0, neg_zero])
  simp [diracTwoH, diracHam, siteProj, diracSx, h1, h2]
  ring_nf
  simp

/-- The coupled generator between `(k − 1, 0)` and `(k, 1)`: `−J`. -/
theorem diracTwoGen_apply_arrival' (hk : k - 1 ≠ k + 1)
    (φ χ : AddCircle (1 : ℝ)) :
    ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) (k - 1, 0) (k, 1) = -(J : ℂ) := by
  have h2 : ¬ k - 1 = k := fun e => hk (by
    have h0 : (1 : ZMod (M + 1)) = 0 := by
      have := congrArg (fun z => k - z) e
      simpa using this
    rw [sub_eq_add_neg, h0, neg_zero])
  have h3 : ¬ k = k - 1 := fun e => h2 e.symm
  have h4 : ¬ k = k - 1 - 1 := fun e => hk (by
    have := congrArg (fun z => z + 1) e
    simpa using this.symm)
  simp [diracTwoH, diracHam, siteProj, diracSx, h2, h3, h4]
  ring_nf
  simp

/-- ★★ **The kick changes the current into the detector's site by `2 J`.** At the carrier
`arrivalRay k`, the sign kick at `k − 1` changes the expectation of `[S, P_k]`, `S` the coupled
generator at any pair of pointer angles, by `2 J`. -/
theorem arenaObs_adOne_diracTwoGen_arrivalRay_sub (hk : k - 1 ≠ k + 1)
    (φ χ : AddCircle (1 : ℝ)) :
    arenaObs (adIter ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) 1 (siteProj k))
        (arenaKick (siteSignKick Prod.fst (k - 1)) (arrivalRay k))
      - arenaObs (adIter ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) 1 (siteProj k))
        (arrivalRay k) = 2 * J := by
  have h2 : k - 1 ≠ k := fun e => hk (by
    have h0 : (1 : ZMod (M + 1)) = 0 := by
      have := congrArg (fun z => k - z) e
      simpa using this
    rw [sub_eq_add_neg, h0, neg_zero])
  have hab : ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) (k, 1) (k - 1, 0) = (J : ℂ) :=
    diracTwoGen_apply_arrival J μ g₁ g₂ j k hf hh hk φ χ
  have hba : ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) (k - 1, 0) (k, 1) = -(J : ℂ) :=
    diracTwoGen_apply_arrival' J μ g₁ g₂ j k hf hh hk φ χ
  rw [arenaKick_siteSignKick_arrivalRay h2, arrivalRay, arenaObs_pairRay, arenaObs_pairRay]
  simp only [inner_single_toEuclideanLin_single]
  have hC : adIter ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) 1 (siteProj k)
      = adOne ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) (siteProj k) := rfl
  rw [hC]
  unfold siteProj
  simp only [adOne_diagonal_apply, hab, hba]
  have h3 : ¬ k - 1 = k := h2
  simp [h3]
  ring

/-- ★★★ **A kick at the neighbouring site arrives at the second pointer.** On the arena of two
site pointers, from the carrier `arrivalRay k` and for the sign kick at the site `k − 1`: the
second pointer's response at `t ≥ 0` is `2 g₂ h'(χ) J t²` up to `8 |g₂| |h'(χ)| ‖H‖² t³`, `H` the
coupled Hamiltonian, at every pair of pointer angles. The kick is an intervention of UA-14, and
`t` is a flow time (UA-7). -/
theorem abs_diracTwoKickResponseSnd_sub_le (hk : k - 1 ≠ k + 1)
    (φ χ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |(diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ
          (arenaKick (siteSignKick Prod.fst (k - 1)) (arrivalRay k)) t
        - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ (arrivalRay k) t)
        - 2 * g₂ * hh.deriv_periodic.lift χ * J * t ^ 2|
      ≤ 8 * |g₂| * |hh.deriv_periodic.lift χ| * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ^ 2
        * t ^ 3 := by
  have hcomm : ∀ i < 1, adIter ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) i (siteProj k)
        * (siteSignKick Prod.fst (k - 1)).val
      = (siteSignKick Prod.fst (k - 1)).val
        * adIter ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ) i (siteProj k) :=
    commute_adIter_of_disjoint_growIter (hopsOne_diracTwoGen J μ g₁ g₂ j k hf hh φ χ)
      (siteSuppOn_siteProj k) (idOffOn_siteSignKick Prod.fst (k - 1)) fun i hi => by
        have hi0 : i = 0 := by omega
        subst hi0
        refine Finset.disjoint_singleton.2 fun e => hk ?_
        have h0 : (1 : ZMod (M + 1)) = 0 := by
          have := congrArg (fun z => k - z) e
          simpa using this.symm
        rw [sub_eq_add_neg, h0, neg_zero, add_zero]
  have key := abs_displacement_kick_sub_sub_le
    (S := (-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ)
    (idxFreeGen_skew (diracTwoH_isHermitian J μ g₁ g₂ j k hf hh φ χ)) (norm_siteProj_le k)
    hcomm (U := fun s => diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s)
    (continuous_diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ)
    (fun s => diracTwoCarrierU_val J μ g₁ g₂ j k hf hh φ χ s) g₂ (hh.deriv_periodic.lift χ)
    (arrivalRay k) ht
  rw [arenaObs_adOne_diracTwoGen_arrivalRay_sub J μ g₁ g₂ j k hf hh hk φ χ, norm_neg_I_smul]
    at key
  have hlead : -(2 * g₂) * hh.deriv_periodic.lift χ
        * ((-1 : ℝ) ^ 1 / ((1 + 1).factorial : ℝ) * t ^ (1 + 1) * (2 * J))
      = 2 * g₂ * hh.deriv_periodic.lift χ * J * t ^ 2 := by
    norm_num [Nat.factorial]
    ring
  have hbound : 4 * |g₂| * |hh.deriv_periodic.lift χ|
        * ((2 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ * t) ^ (1 + 1) / ((1 + 1).factorial : ℝ)) * t
      = 8 * |g₂| * |hh.deriv_periodic.lift χ| * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ^ 2
        * t ^ 3 := by
    norm_num [Nat.factorial]
    ring
  rw [hlead, hbound] at key
  unfold diracTwoShiftSnd
  exact key

/-- ★★ **A lower bound for the response.** Its size is at least
`2 |g₂| |h'(χ)| t² (|J| − 4 ‖H‖² t)`. -/
theorem le_abs_diracTwoKickResponseSnd (hk : k - 1 ≠ k + 1)
    (φ χ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    2 * |g₂| * |hh.deriv_periodic.lift χ| * t ^ 2
        * (|J| - 4 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ^ 2 * t)
      ≤ |diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ
          (arenaKick (siteSignKick Prod.fst (k - 1)) (arrivalRay k)) t
        - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ (arrivalRay k) t| := by
  have key := abs_diracTwoKickResponseSnd_sub_le J μ g₁ g₂ j k hf hh hk φ χ ht
  have htri := abs_sub_abs_le_abs_sub (2 * g₂ * hh.deriv_periodic.lift χ * J * t ^ 2)
    (diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ
        (arenaKick (siteSignKick Prod.fst (k - 1)) (arrivalRay k)) t
      - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ (arrivalRay k) t)
  rw [abs_sub_comm] at key
  have hlead : |2 * g₂ * hh.deriv_periodic.lift χ * J * t ^ 2|
      = 2 * |g₂| * |hh.deriv_periodic.lift χ| * |J| * t ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg (pow_nonneg ht 2)]
  rw [hlead] at htri
  nlinarith [htri, key]

/-- ★★★ **The response is not zero.** For `g₂ h'(χ) ≠ 0`, `0 < t` and `4 ‖H‖² t < |J|`, the
second pointer's moving angle differs between the kicked and the unkicked run: the kick at the
neighbouring site is felt. -/
theorem diracTwoKickResponseSnd_ne_zero (hk : k - 1 ≠ k + 1)
    (hg : g₂ ≠ 0) (φ χ : AddCircle (1 : ℝ)) (hχ : hh.deriv_periodic.lift χ ≠ 0) {t : ℝ}
    (ht : 0 < t) (hsmall : 4 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ^ 2 * t < |J|) :
    diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ
        (arenaKick (siteSignKick Prod.fst (k - 1)) (arrivalRay k)) t
      - diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ (arrivalRay k) t ≠ 0 := by
  have key := le_abs_diracTwoKickResponseSnd J μ g₁ g₂ j k hf hh hk φ χ ht.le
  have hpos : 0 < 2 * |g₂| * |hh.deriv_periodic.lift χ| * t ^ 2
      * (|J| - 4 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ^ 2 * t) := by
    have h1 : 0 < |g₂| := abs_pos.2 hg
    have h2 : 0 < |hh.deriv_periodic.lift χ| := abs_pos.2 hχ
    have h3 : 0 < |J| - 4 * ‖diracTwoH J μ g₁ g₂ j k hf hh φ χ‖ ^ 2 * t := sub_pos.2 hsmall
    positivity
  exact abs_pos.1 (hpos.trans_le key)

end DiracTwo

end CSD.RecordLayer

end
