/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.CouplingWitness

/-!
# The half-life bound is attained (§H continuation: attainment)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

`RecordDegradation.lean` priced coupled driving by
`μ (intact n)ᶜ ≤ n • ε` and `CouplingWitness.lean` showed the bound bites
(`ε = 1/2`). This module closes the remaining question: **is the linear
rate real, or is the bound loose?** Answer: it is attained with equality.

The witness is the **cyclic-shift kick**: the base is the uniform cycle
`Fin m` under `x ↦ x + 1`, and the record coordinate is kicked exactly
when the base sits at `0`. Two structural facts make the analysis exact:
within any window of `n ≤ m` periods every trajectory visits the trigger
**at most once** (the shift is a cycle), and a single visit flips the
readout permanently within the window. Hence:

* `cyclicKick_iterate` — the closed-form trajectory (base advances, the
  record accumulates the visit indicators);
* `recordIntact_compl_cyclicKick` — the unstable set is EXACTLY the
  cylinder over the `n` base points that reach the trigger within the
  window (set equality, not an estimate);
* ★★ `cyclicKick_halfLife_attained` — on the window `n ≤ m`,
  `μ (intact n)ᶜ = n • ε` with `ε = 1/m`: **the record half-life bound is
  an equality for the cyclic kick — linear degradation at exactly the
  coupling rate is realised, so the generic bound is sharp.**

Honest scope: attainment on the window `n ≤ m` (after a full cycle the
second visit un-flips a `δ` of order two and the count saturates —
correctly so, since `n • ε` exceeds `1` there while measures cannot);
sharpness is exhibited for this drive, with no claim that every drive
attains its bound. Cross-references: `specs/external-library-map.md` §H,
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace CSD.Empirical.QuantumChaos

/-! ### The cyclic-shift kick -/

/-- The base dynamics: the uniform cycle on `Fin m`. -/
def cyclicShift (m : ℕ) [NeZero m] : Fin m → Fin m := fun x => x + 1

/-- The uniform probability measure on the cycle. -/
noncomputable def uniformFin (m : ℕ) : Measure (Fin m) :=
  ((m : ℝ≥0∞))⁻¹ • Measure.count

/-- **The cyclic kick**: the record is kicked exactly when the base sits
at `0`. -/
noncomputable def cyclicKick (m : ℕ) [NeZero m] (δ : RecordCircle) :
    Fin m × RecordCircle → Fin m × RecordCircle :=
  triggeredRecordKick (cyclicShift m) ({0} : Set (Fin m)) δ

/-- `Fin.ofNat` below one full cycle is faithful. -/
lemma ofNat_val_of_lt {m : ℕ} [NeZero m] {j : ℕ} (h : j < m) :
    (Fin.ofNat m j).val = j := by
  rw [show (Fin.ofNat m j).val = j % m from rfl, Nat.mod_eq_of_lt h]

/-- `Fin.ofNat` respects the successor. -/
lemma ofNat_succ {m : ℕ} [NeZero m] (k : ℕ) :
    Fin.ofNat m (k + 1) = Fin.ofNat m k + 1 := by
  apply Fin.val_injective
  rw [Fin.val_add, show (Fin.ofNat m k).val = k % m from rfl,
    show ((1 : Fin m)).val = 1 % m from rfl,
    show (Fin.ofNat m (k + 1)).val = (k + 1) % m from rfl]
  exact Nat.add_mod k 1 m

/-- The closed-form trajectory: the base advances one step per period and
the record accumulates the trigger-visit indicators. -/
lemma cyclicKick_iterate (m : ℕ) [NeZero m] (δ : RecordCircle) (x : Fin m)
    (r : RecordCircle) (k : ℕ) :
    (cyclicKick m δ)^[k] (x, r)
      = (x + Fin.ofNat m k,
          r + ∑ j ∈ Finset.range k,
            if x + Fin.ofNat m j = 0 then δ else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [cyclicKick, triggeredRecordKick]
    refine Prod.ext ?_ ?_
    · show cyclicShift m (x + Fin.ofNat m k) = x + Fin.ofNat m (k + 1)
      rw [cyclicShift, ofNat_succ, add_assoc]
    · show _ = r + ∑ j ∈ Finset.range (k + 1),
        if x + Fin.ofNat m j = 0 then δ else 0
      rw [Finset.sum_range_succ, ← add_assoc]
      by_cases hmem : x + Fin.ofNat m k = 0
      · rw [if_pos hmem,
          if_pos (show x + Fin.ofNat m k ∈ ({0} : Set (Fin m)) from hmem)]
      · rw [if_neg hmem,
          if_neg (show x + Fin.ofNat m k ∉ ({0} : Set (Fin m)) from hmem)]

/-! ### The unstable set, exactly -/

/-- **The unstable set is exactly the reach-the-trigger cylinder**: on a
window of at most one full cycle, a trajectory's readout changes iff its
base reaches `0` within the window (set equality, not an estimate). -/
theorem recordIntact_compl_cyclicKick {m : ℕ} [NeZero m]
    {δ : RecordCircle} (hδ : δ ≠ 0) {n : ℕ} (hn : n ≤ m) :
    (recordIntact (cyclicKick m δ) Prod.snd n)ᶜ
      = {x : Fin m | ∃ j, j < n ∧ x + Fin.ofNat m j = 0} ×ˢ Set.univ := by
  ext ⟨x, r⟩
  simp only [Set.mem_compl_iff, recordIntact, Set.mem_ofPred_eq, not_forall,
    Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true]
  constructor
  · rintro ⟨k, hkn, hne⟩
    by_contra hno
    push Not at hno
    apply hne
    rw [cyclicKick_iterate]
    show r + (∑ j ∈ Finset.range k,
        if x + Fin.ofNat m j = 0 then δ else 0) = r
    rw [Finset.sum_eq_zero, add_zero]
    intro j hj
    exact if_neg (hno j (lt_of_lt_of_le (Finset.mem_range.mp hj) hkn))
  · rintro ⟨j₀, hj₀n, hx⟩
    refine ⟨j₀ + 1, by omega, ?_⟩
    rw [cyclicKick_iterate]
    show ¬ (r + (∑ j ∈ Finset.range (j₀ + 1),
        if x + Fin.ofNat m j = 0 then δ else 0) = r)
    rw [show (∑ j ∈ Finset.range (j₀ + 1),
        if x + Fin.ofNat m j = 0 then δ else 0) = δ from ?_]
    · intro habs
      exact hδ (add_left_cancel (habs.trans (add_zero r).symm))
    · rw [Finset.sum_eq_single j₀]
      · rw [if_pos hx]
      · intro j hj hne'
        refine if_neg fun h0 => hne' ?_
        have hcast : Fin.ofNat m j = Fin.ofNat m j₀ :=
          add_left_cancel (h0.trans hx.symm)
        have hjm : j < m := by
          have := Finset.mem_range.mp hj
          omega
        have hj₀m : j₀ < m := by omega
        have := congrArg Fin.val hcast
        rwa [ofNat_val_of_lt hjm, ofNat_val_of_lt hj₀m] at this
      · intro habs
        exact absurd (Finset.self_mem_range_succ j₀) habs

/-! ### Attainment -/

/-- The reach set has exactly `n` points on the window. -/
lemma count_reachSet {m : ℕ} [NeZero m] {n : ℕ} (hn : n ≤ m) :
    Measure.count {x : Fin m | ∃ j, j < n ∧ x + Fin.ofNat m j = 0}
      = (n : ℝ≥0∞) := by
  classical
  have hS : {x : Fin m | ∃ j, j < n ∧ x + Fin.ofNat m j = 0}
      = ↑((Finset.range n).image (fun j : ℕ => -(Fin.ofNat m j))) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hxj⟩
      exact ⟨j, hj, (eq_neg_of_add_eq_zero_left hxj).symm⟩
    · rintro ⟨j, hj, hxj⟩
      exact ⟨j, hj, by rw [← hxj]; rw [neg_add_cancel]⟩
  rw [hS, Measure.count_apply_finset]
  congr 1
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro j hj j' hj' hne
  have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
  have hj'm : j' < m := lt_of_lt_of_le (Finset.mem_range.mp hj') hn
  have hcast : Fin.ofNat m j = Fin.ofNat m j' := neg_inj.mp hne
  have := congrArg Fin.val hcast
  rwa [ofNat_val_of_lt hjm, ofNat_val_of_lt hj'm] at this

/-- ★★ **The half-life bound is attained**: on the window `n ≤ m`, the
cyclic kick's unstable measure EQUALS `n • ε` with `ε = 1/m` the coupling
strength — linear record degradation at exactly the coupling rate is
realised, so the generic bound `recordIntact_compl_measure_le` is sharp. -/
theorem cyclicKick_halfLife_attained {m : ℕ} [NeZero m]
    {δ : RecordCircle} (hδ : δ ≠ 0) {n : ℕ} (hn : n ≤ m) :
    ((uniformFin m).prod volume)
        ((recordIntact (cyclicKick m δ) Prod.snd n)ᶜ)
      = n • ((uniformFin m).prod volume)
          (recordFlip (cyclicKick m δ) Prod.snd) := by
  rw [recordIntact_compl_cyclicKick hδ hn, Measure.prod_prod, measure_univ,
    mul_one,
    show cyclicKick m δ
      = triggeredRecordKick (cyclicShift m) ({0} : Set (Fin m)) δ from rfl,
    measure_recordFlip_triggeredRecordKick (cyclicShift m) _ hδ]
  rw [uniformFin, Measure.smul_apply, Measure.smul_apply,
    count_reachSet hn,
    show Measure.count ({0} : Set (Fin m)) = 1 from by
      rw [show ({0} : Set (Fin m)) = ({0} : Finset (Fin m)) from by simp,
        Measure.count_apply_finset]
      simp]
  rw [smul_eq_mul, smul_eq_mul, mul_one, nsmul_eq_mul, mul_comm]

end CSD.Empirical.QuantumChaos
