/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.LevelReduction

/-!
# Overlapping extended rectangles

**Category:** 1-Mathlib (CSD-free). BACKLOG #233 (split from ~~#229~~).

`ExtendedRectangle.lean` (~~#96~~) proved one extended rectangle at a time: with the single fault in
the leading recovery or the gadget the rectangle is corrected, and with it in the trailing recovery
the rectangle hands on a correctable deviation. `FaultTolerantComposition.lean` composes
**non-overlapping** corrected steps. With a recovery after every gadget the extended rectangles
**overlap** — recovery `k` trails gadget `k` and leads gadget `k + 1` — and a trailing-recovery fault
is not corrected inside its own rectangle. This file chains them, which is the step
Aliferis–Gottesman–Preskill's argument takes and #96 left open.

## The chain

The circuit is gadget `0`, recovery `0`, gadget `1`, recovery `1`, …: `ovRun R G k` runs the first
`k` gadget–recovery pairs and `ovIdeal g k` the first `k` ideal gadgets. The input is a code state, so
the first extended rectangle is the two-piece `rect` of #96 and the `k`-th, for `k ≥ 1`, is
`exRec (R (k − 1)) (G k) (R k)`.

* `IsFaultChain P D N g R G fR fG` — **the pieces, each with a fault flag**: an unflagged recovery is
  an `IsRecovery` for `D`, a flagged one a `DeviatesBy P D id`; an unflagged gadget is the ideal one,
  a flagged one a `DeviatesBy P D (g k)`; the ideal gadgets propagate `D` and keep the code. These are
  #96's three piecewise properties, one per piece, nothing about the composite;
* `lastFault fR k` — whether the recovery just run was flagged; `ExRecGood fR fG k` — **the `k`-th
  extended rectangle holds at most one flagged piece**: the recovery before gadget `k`, gadget `k`,
  recovery `k`;
* ★★★ `IsFaultChain.step` — **one overlapping rectangle**: a state that is exact unless the last
  recovery was flagged, and a correctable deviation of the ideal in any case, is carried to a state
  of the same kind. The four good cases are #96's: the leading fault is carried by the gadget and
  removed (`isCorrectedStep_exRec_leading`), a gadget fault is removed
  (`isCorrectedStep_exRec_gadget`), a trailing fault is handed on (`deviatesBy_exRec_trailing`);
* ★★★ `IsFaultChain.ovRun_spec` — **the invariant along the whole chain**: after `k` steps the
  state is `E (ovIdeal g k ρ)` with `E ∈ D`, and exactly `ovIdeal g k ρ` unless recovery `k − 1` was
  the flagged piece;
* ★★★ `IsFaultChain.decode_ovRun` — **with a final ideal decoding the output is the ideal one**.

## Counting faults in overlapping windows

* ★★ `measure_two_le_card_filter_le` — under independent faults at the locations, **two or more
  faults in a window `W`** have probability at most `C(|W|, 2) · ν(fault)²`, by the union bound over
  the window's pairs. The window's marginal never has to be computed: each pair event is a box;
* ★★★ `one_sub_le_measure_output_eq_windows` — **the join for overlapping windows**: if the output
  is ideal whenever every one of `N` windows of at most `w` locations holds at most one fault, the
  output is ideal with probability at least `1 − N · C(w, 2) · p²`. The windows may overlap; the union
  bound does not care.

## Honest scope

⚠️ **The flags are hypotheses about the pieces.** `IsFaultChain` says what a piece with and without
one fault does; that a concrete recovery circuit with one fault is a `DeviatesBy P D id` is a theorem
about that circuit, supplied at the Steane code by `Empirical/QM/QEC/SteaneOverlapMachine.lean`
(BACKLOG #233).

⚠️ **The input is a code state and the final decoding is ideal.** Encoding and the final read-out are
outside the chain.

⚠️ **Maps, not channels**, as in #62 (d1) and #96: nothing here imposes positivity or trace
preservation.

⚠️ **Independent faults of one rate.** The location measure is a product of one Bernoulli law;
correlated noise is outside the bound.

## References

P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97;
`Mathlib/QuantumInfo/ExtendedRectangle.lean` (~~#96~~), `Mathlib/QuantumInfo/LevelReduction.lean`
(~~#97~~, `one_sub_le_measure_output_eq`); `specs/BACKLOG.md` #233, #96, #97; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuantumInfo

variable {n : Type*} [Fintype n]

/-! ### The overlapping chain -/

/-- **The run**: `k` gadget–recovery pairs, gadget `j` then recovery `j`. -/
def ovRun (R G : ℕ → Matrix n n ℂ → Matrix n n ℂ) : ℕ → Matrix n n ℂ → Matrix n n ℂ
  | 0, ρ => ρ
  | k + 1, ρ => R k (G k (ovRun R G k ρ))

/-- **The ideal run**: the first `k` ideal gadgets. -/
def ovIdeal (g : ℕ → Matrix n n ℂ → Matrix n n ℂ) : ℕ → Matrix n n ℂ → Matrix n n ℂ
  | 0, ρ => ρ
  | k + 1, ρ => g k (ovIdeal g k ρ)

omit [Fintype n] in
@[simp] theorem ovRun_zero (R G : ℕ → Matrix n n ℂ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    ovRun R G 0 ρ = ρ := rfl

omit [Fintype n] in
@[simp] theorem ovRun_succ (R G : ℕ → Matrix n n ℂ → Matrix n n ℂ) (k : ℕ) (ρ : Matrix n n ℂ) :
    ovRun R G (k + 1) ρ = R k (G k (ovRun R G k ρ)) := rfl

omit [Fintype n] in
@[simp] theorem ovIdeal_zero (g : ℕ → Matrix n n ℂ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    ovIdeal g 0 ρ = ρ := rfl

omit [Fintype n] in
@[simp] theorem ovIdeal_succ (g : ℕ → Matrix n n ℂ → Matrix n n ℂ) (k : ℕ) (ρ : Matrix n n ℂ) :
    ovIdeal g (k + 1) ρ = g k (ovIdeal g k ρ) := rfl

omit [Fintype n] in
/-- The ideal run is the ideal gadgets folded in order: `ovIdeal` is `runMaps` of #62 (d1). -/
theorem runMaps_ofFn_eq_ovIdeal (g : ℕ → Matrix n n ℂ → Matrix n n ℂ) :
    ∀ (k : ℕ) (ρ : Matrix n n ℂ), runMaps (List.ofFn fun j : Fin k => g j) ρ = ovIdeal g k ρ
  | 0, ρ => rfl
  | k + 1, ρ => by
    rw [List.ofFn_succ', List.concat_eq_append, runMaps, List.foldl_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (fun σ S => S σ) ρ (List.ofFn fun i : Fin k => g i) = ovIdeal g k ρ from
      runMaps_ofFn_eq_ovIdeal g k ρ]
    rfl

/-- Whether the recovery run just before gadget `k` — recovery `k − 1` — was flagged. -/
def lastFault (fR : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => fR k

/-- **The `k`-th extended rectangle holds at most one flagged piece**: the recovery before gadget `k`,
gadget `k`, and recovery `k`. -/
def ExRecGood (fR fG : ℕ → Bool) (k : ℕ) : Prop :=
  (lastFault fR k).toNat + (fG k).toNat + (fR k).toNat ≤ 1

/-- **The pieces of an overlapping chain of `N` extended rectangles, each with a fault flag** — #96's
three piecewise properties, one per piece. An unflagged recovery corrects `D`, a flagged one deviates
by `D`; an unflagged gadget is ideal, a flagged one deviates by `D` from it; the ideal gadgets carry
`D` and keep the code. -/
structure IsFaultChain (P : Matrix n n ℂ) (D : Set (Matrix n n ℂ → Matrix n n ℂ)) (N : ℕ)
    (g R G : ℕ → Matrix n n ℂ → Matrix n n ℂ) (fR fG : ℕ → Bool) : Prop where
  /-- "No error" is correctable. -/
  id_mem : id ∈ D
  /-- An unflagged recovery corrects `D`. -/
  recovery : ∀ k < N, fR k = false → IsRecovery P (R k) D
  /-- A flagged recovery leaves a code state a `D`-deviation of itself. -/
  recovery_fault : ∀ k < N, fR k = true → DeviatesBy P D id (R k)
  /-- An unflagged gadget is the ideal one. -/
  gadget : ∀ k < N, fG k = false → G k = g k
  /-- A flagged gadget is the ideal one followed by a `D`-deviation. -/
  gadget_fault : ∀ k < N, fG k = true → DeviatesBy P D (g k) (G k)
  /-- Transversality. -/
  propagates : ∀ k < N, PropagatesD P D (g k)
  /-- The ideal gadgets keep code states in the code. -/
  preserves : ∀ k < N, ∀ ρ, IsCodeState P ρ → IsCodeState P (g k ρ)

namespace IsFaultChain

variable {P : Matrix n n ℂ} {D : Set (Matrix n n ℂ → Matrix n n ℂ)} {N : ℕ}
  {g R G : ℕ → Matrix n n ℂ → Matrix n n ℂ} {fR fG : ℕ → Bool}

/-- The ideal run keeps code states in the code. -/
theorem isCodeState_ovIdeal (h : IsFaultChain P D N g R G fR fG) {ρ : Matrix n n ℂ}
    (hρ : IsCodeState P ρ) : ∀ k ≤ N, IsCodeState P (ovIdeal g k ρ)
  | 0, _ => hρ
  | k + 1, hk => h.preserves k (by omega) _ (isCodeState_ovIdeal h hρ k (by omega))

/-- ★★★ **One overlapping rectangle.** A state `σ` that is a `D`-deviation of the code state `ψ`, and
equal to it unless the last recovery was flagged, is carried by gadget `k` and recovery `k` to a
`D`-deviation of `g k ψ`, equal to it unless recovery `k` is flagged — provided the `k`-th extended
rectangle holds at most one flagged piece. -/
theorem step (h : IsFaultChain P D N g R G fR fG) {k : ℕ} (hk : k < N) (hgood : ExRecGood fR fG k)
    {ψ σ : Matrix n n ℂ} (hψ : IsCodeState P ψ) (hσ : ∃ E ∈ D, σ = E ψ)
    (hσ' : lastFault fR k = false → σ = ψ) :
    (∃ E ∈ D, R k (G k σ) = E (g k ψ)) ∧ (fR k = false → R k (G k σ) = g k ψ) := by
  have hgψ := h.preserves k hk ψ hψ
  have exact : ∀ b : Bool, R k (G k σ) = g k ψ →
      (∃ E ∈ D, R k (G k σ) = E (g k ψ)) ∧ (b = false → R k (G k σ) = g k ψ) :=
    fun _ he => ⟨⟨id, h.id_mem, he⟩, fun _ => he⟩
  unfold ExRecGood at hgood
  cases hl : lastFault fR k <;> cases hg : fG k <;> cases hr : fR k <;>
    simp only [hl, hg, hr, Bool.toNat_true, Bool.toNat_false] at hgood <;> try omega
  · -- no flagged piece
    refine exact _ ?_
    rw [hσ' hl, h.gadget k hk hg]
    exact (h.recovery k hk hr).apply_of_isCodeState h.id_mem hgψ
  · -- the trailing recovery is flagged: the deviation is handed on
    rw [hσ' hl, h.gadget k hk hg]
    obtain ⟨E, hE, hEq⟩ := h.recovery_fault k hk hr (g k ψ) hgψ
    exact ⟨⟨E, hE, hEq⟩, fun h' => absurd h' (by simp)⟩
  · -- the gadget is flagged: the trailing recovery removes its deviation
    refine exact _ ?_
    rw [hσ' hl]
    obtain ⟨E, hE, hEq⟩ := h.gadget_fault k hk hg ψ hψ
    rw [hEq, h.recovery k hk hr E hE _ hgψ]
  · -- the leading recovery is flagged: the gadget carries its deviation, the recovery removes it
    refine exact _ ?_
    obtain ⟨E, hE, rfl⟩ := hσ
    obtain ⟨E', hE', hEq⟩ := h.propagates k hk E hE ψ hψ
    rw [h.gadget k hk hg, hEq, h.recovery k hk hr E' hE' _ hgψ]

/-- ★★★ **The invariant along the chain of overlapping rectangles.** If every extended rectangle holds
at most one flagged piece, then after `k ≤ N` steps the state is a `D`-deviation of the ideal run, and
exactly the ideal run unless recovery `k − 1` was flagged. -/
theorem ovRun_spec (h : IsFaultChain P D N g R G fR fG) (hgood : ∀ k < N, ExRecGood fR fG k)
    {ρ : Matrix n n ℂ} (hρ : IsCodeState P ρ) :
    ∀ k ≤ N, (∃ E ∈ D, ovRun R G k ρ = E (ovIdeal g k ρ))
      ∧ (lastFault fR k = false → ovRun R G k ρ = ovIdeal g k ρ)
  | 0, _ => ⟨⟨id, h.id_mem, rfl⟩, fun _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨hdev, hex⟩ := ovRun_spec h hgood hρ k (by omega)
    exact h.step (by omega) (hgood k (by omega)) (h.isCodeState_ovIdeal hρ k (by omega)) hdev hex

/-- ★★★ **With a final ideal decoding, the chain computes the ideal output.** Any recovery for `D`
applied after the last step returns the ideal run exactly. -/
theorem decode_ovRun (h : IsFaultChain P D N g R G fR fG) (hgood : ∀ k < N, ExRecGood fR fG k)
    {Rd : Matrix n n ℂ → Matrix n n ℂ} (hRd : IsRecovery P Rd D) {ρ : Matrix n n ℂ}
    (hρ : IsCodeState P ρ) : Rd (ovRun R G N ρ) = ovIdeal g N ρ := by
  obtain ⟨⟨E, hE, hEq⟩, -⟩ := h.ovRun_spec hgood hρ N le_rfl
  rw [hEq, hRd E hE _ (h.isCodeState_ovIdeal hρ N le_rfl)]

end IsFaultChain

/-! ### Two faults in a window -/

/-- ★★ **Two or more faults in a window are unlikely.** Under independent faults at the locations,
each with probability `ν {true}`, a window `W` holds two or more faults with probability at most
`C(|W|, 2) · ν {true}²`: two faults pick a pair of the window, and each pair is a box event. -/
theorem measure_two_le_card_filter_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : Measure Bool)
    [IsProbabilityMeasure ν] (W : Finset ι) :
    Measure.pi (fun _ : ι => ν) {ω | 2 ≤ (W.filter fun i => ω i = true).card}
      ≤ ((W.card.choose 2 : ℕ) : ℝ≥0∞) * ν {b | b = true} ^ 2 := by
  have hsub : {ω : ι → Bool | 2 ≤ (W.filter fun i => ω i = true).card}
      ⊆ ⋃ s ∈ W.powersetCard 2, {ω | ∀ i ∈ s, ω i = true} := by
    intro ω hω
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := W.filter fun i => ω i = true) hω
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_powersetCard.2
      ⟨hs.trans (Finset.filter_subset _ _), hcard⟩)) fun i hi => ?_
    exact (Finset.mem_filter.1 (hs hi)).2
  have hbox : ∀ s : Finset ι, s.card = 2 →
      Measure.pi (fun _ : ι => ν) {ω | ∀ i ∈ s, ω i = true} = ν {b | b = true} ^ 2 := by
    intro s hs
    have hset : {ω : ι → Bool | ∀ i ∈ s, ω i = true}
        = Set.univ.pi fun i => if i ∈ s then {b | b = true} else Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
      refine ⟨fun h i => ?_, fun h i hi => by simpa [hi] using h i⟩
      by_cases hi : i ∈ s
      · simpa [hi] using h i hi
      · simp [hi]
    rw [hset, Measure.pi_pi]
    simp only [apply_ite (ν ·), measure_univ]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hs]
  calc Measure.pi (fun _ : ι => ν) {ω | 2 ≤ (W.filter fun i => ω i = true).card}
      ≤ Measure.pi (fun _ : ι => ν) (⋃ s ∈ W.powersetCard 2, {ω | ∀ i ∈ s, ω i = true}) :=
        measure_mono hsub
    _ ≤ ∑ s ∈ W.powersetCard 2, Measure.pi (fun _ : ι => ν) {ω | ∀ i ∈ s, ω i = true} :=
        measure_biUnion_finset_le _ _
    _ = ∑ _s ∈ W.powersetCard 2, ν {b | b = true} ^ 2 :=
        Finset.sum_congr rfl fun s hs => hbox s (Finset.mem_powersetCard.1 hs).2
    _ = ((W.card.choose 2 : ℕ) : ℝ≥0∞) * ν {b | b = true} ^ 2 := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- ★★★ **The join for overlapping windows.** If the output is the ideal one whenever each of `N`
windows — of at most `w` locations each, overlapping or not — holds at most one fault, then under
independent faults of rate at most `p` the output is ideal with probability at least
`1 − N · C(w, 2) · p²`. -/
theorem one_sub_le_measure_output_eq_windows {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 ≤ p)
    (hν : ν {b | b = true} ≤ ENNReal.ofReal p) {N w : ℕ} (W : Fin N → Finset ι)
    (hW : ∀ j, (W j).card ≤ w) {out : (ι → Bool) → β} {ideal : β}
    (hgood : ∀ ω, (∀ j, ((W j).filter fun i => ω i = true).card ≤ 1) → out ω = ideal) :
    1 - (N : ℝ≥0∞) * ENNReal.ofReal ((w.choose 2 : ℝ) * p ^ 2)
      ≤ Measure.pi (fun _ : ι => ν) {ω | out ω = ideal} := by
  refine one_sub_le_measure_output_eq (Measure.pi fun _ : ι => ν)
    (fun j => {ω | 2 ≤ ((W j).filter fun i => ω i = true).card})
    (fun ω hω => hgood ω fun j => ?_) (fun j => ?_)
  · have := hω j
    simp only [Set.mem_ofPred_eq, not_le] at this
    omega
  · refine (measure_two_le_card_filter_le ν (W j)).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hp, ENNReal.ofReal_natCast]
    gcongr
    exact hW j

end QuantumInfo

end

end
