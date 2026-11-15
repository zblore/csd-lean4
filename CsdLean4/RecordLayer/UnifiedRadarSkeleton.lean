/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarReading
public import CsdLean4.RecordLayer.DiracTwoCharts

/-!
# M6 from the top: the Lorentz statement from five pointer histories

**Category:** 7-SigmaLayer (the record layer). BACKLOG #402 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16. No new assumption beyond UA-18.

This module states M6 once, from the top, as a conditional theorem about one run, and so
fixes the list of what remains. Five pointers of one run are read as in UA-18 (d); their
counts are the five readings of `radar_lorentz_error`; the conclusion is its Lorentz
statement with explicit errors. Everything not proved here is a named hypothesis.

* `IsGatedHistory` — the displacement of a pointer whose gate is open and then closes: within
  `δ < 1/12` of `(1/4)(1 − cos R t)` up to `t_a`, speed at most `v` on `[t_a, t_b]`, at most a
  sixth of a turn inside `[t_b, t_c]`;
* `IsGatedHistory.exists_count` — its count at every flow time of `[t_b, t_c]`, with
  `|2π N − R t_a| ≤ 2π (3 v (t_b − t_a) + 7/2)`, for a pointer read through any projection;
* `IsAwayHistory`, `IsAwayHistory.exists_count` — the same for a pointer whose gate is closed,
  open and closed again (#399), with the band of #398 as a field;
* `abs_div_sub_le_of_rate` — a count compared with a rate times a time, in the unit of the
  rest rate;
* ★★★ `radar_lorentz_of_histories` — one run `γ` with five pointers. If `B`'s emission,
  return and meeting pointers and `A`'s relay and meeting pointers have these histories, with
  `B`'s rate `√(1 − v²)` times `A`'s rate `R₀`, and the four flow times satisfy the two
  relations of a light signal and an observer of velocity `v`, then the five counts, in the
  unit `2π/R₀`, satisfy the Lorentz statement of `radar_lorentz_error` with errors read off
  the histories.

## Exact scope: what is assumed here and is still to be proved

This theorem is conditional. M6 is met only when each item below is a theorem about records
of one flow on the arena of UA-18, with values exhibited. None is, on that arena.

1. **The five histories.** That the pointers of the five-pointer flow, from a product of the
   three carriers, have displacements of these forms. For two carriers and two pointers the
   emission and return histories follow from where the carriers are (#394, #399, #400); for
   three carriers and five pointers nothing is proved.
2. **Where the carriers are.** That the messenger, `A`'s clock and `B`'s clock are together
   and apart at the stated flow times: packets on the chain with two walls, the reflection
   at the wall, `A` at rest, `B` moving. Not built.
3. **The two relations between the flow times**, `t_R − t_E = v (t_M − t_E)` and
   `t_Ret − t_R = v (t_M − t_Ret)`. They state the messenger's speed (one) and `B`'s velocity
   (`v`). By the test of UO-16 they may not stay hypotheses: they are to come from the band
   velocities of the packets.
4. **The moving clock's rate**, `R_B = √(1 − v²) R₀`. By the same test it may not stay a
   hypothesis: it is to come from UD-138.
5. **The band** of the return pointer (a field of `IsAwayHistory`), or the conditions of #400
   that imply it.
6. **Values** meeting all the inequalities together.
7. **An open set of the pointers' conserved angles** (UA-18 (g)); the histories above are
   known only on the fibres where the profiles vanish.

What the theorem does give: the logical shape of M6 with nothing hidden. The five readings
are numbers of tick records of five pointers of one run, each in its stated window (UA-18
(e)); the unit `2π/R₀` and the sums are arithmetic in the statement.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UD-147, UD-157, UD-163, UD-164); `RecordLayer/DiracTwoCharts.lean`
(`radar_lorentz_error`); `RecordLayer/UnifiedGatedReading.lean` (#394:
`gated_pointer_count`); `RecordLayer/UnifiedReturnReading.lean` (#399:
`away_pointer_count`); `RecordLayer/UnifiedWindowSwing.lean` (#398: the bands);
`RecordLayer/UnifiedRadarReading.lean` (#401).
-/

@[expose] public section

noncomputable section

open CSD.LF4 Set

namespace CSD.RecordLayer

/-! ### Two pointer histories -/

/-- **The history of a pointer whose gate is open and then closes**: its displacement `D` is
within `δ < 1/12` of `(1/4)(1 − cos R t)` up to `t_a`, changes at speed at most `v` on
`[t_a, t_b]`, and by at most a sixth of a turn inside `[t_b, t_c]`. -/
structure IsGatedHistory (D : ℝ → ℝ) (R δ v ta tb tc : ℝ) : Prop where
  rate_pos : 0 < R
  err_nonneg : 0 ≤ δ
  err_lt : δ < 1 / 12
  ta_nonneg : 0 ≤ ta
  ta_le : ta ≤ tb
  tb_le : tb ≤ tc
  swing : ∀ t, 0 ≤ t → t ≤ ta → |D t - 1 / 4 * (1 - Real.cos (R * t))| ≤ δ
  mid : ∀ s t, ta ≤ s → s ≤ t → t ≤ tb → |D t - D s| ≤ v * (t - s)
  closed : ∀ s t, tb ≤ s → s ≤ t → t ≤ tc → |D t - D s| ≤ 1 / 6

/-- **The count of a gated history.** A pointer read through the projection `π`, started at
`1/12`, with a gated history: at every flow time of `[t_b, t_c]` it has a count `N` with
`|2π N − R t_a| ≤ 2π (3 v (t_b − t_a) + 7/2)`. -/
theorem IsGatedHistory.exists_count {X : Type*} {π : X → KTorus} {γ : ℝ → X} {q : KTorus}
    {D : ℝ → ℝ} {R δ v ta tb tc : ℝ} (h : IsGatedHistory D R δ v ta tb tc)
    (hq : rep q.1 = 1 / 12) (hγ : ∀ t, 0 ≤ t → t ≤ tc → π (γ t) = pshift (D t) q) :
    ∀ t, tb ≤ t → t ≤ tc →
      ∃ N : ℕ, IsTickCount {x : X | π x ∈ readyArc 2} {x : X | π x ∈ displayArc} γ t N
        ∧ |(N : ℝ) * (2 * Real.pi) - R * ta| ≤ 2 * Real.pi * (3 * v * (tb - ta) + 7 / 2) := by
  have hπ := Real.pi_pos
  have h0 := h.err_nonneg
  have h1 := h.err_lt
  obtain ⟨Na, Nb, -, hNa', -, hNab, hNb', hwin⟩ := gated_pointer_count (Y := Unit)
    (γ := fun t => ((), π (γ t))) (q := q) (D := D) (A := 1 / 4) (v := v) h.rate_pos
    (by norm_num) h.err_nonneg h.ta_nonneg h.ta_le h.tb_le hγ h.swing
    (by rw [hq]; exact h.err_lt) (by rw [hq]; linarith) (by rw [hq]; linarith)
    (by rw [hq]; linarith) h.mid h.closed
  intro t hbt htc
  obtain ⟨N, hN, c1, c2⟩ := hwin t hbt htc
  refine ⟨N, hN, ?_⟩
  have hNa1 : (Na : ℝ) ≤ N := by exact_mod_cast hNab.trans c1
  have hN1 : (N : ℝ) ≤ Nb + 1 := by exact_mod_cast c2
  have htr : 0 ≤ 3 * v * (tb - ta) := by
    have := (abs_nonneg _).trans (h.mid ta tb le_rfl h.ta_le le_rfl)
    linarith
  rw [abs_le] at hNa' ⊢
  constructor
  · nlinarith [hNa'.1, hNa'.2]
  · nlinarith [hNa'.1, hNa'.2]

/-- **The history of a pointer whose gate is closed, open and closed again** (#399): within
`η₀ < 1/12` of its start up to `t_a`; speed at most `v` on `[t_a, t_b]` and `[t₃, t₄]`; within
`η < 1/12` of `(1/4)(1 − cos R t) − c` on `[t_b, t₃]`, with `1/12 − c` in one of the two bands
of #398; at most a sixth of a turn inside `[t₄, t₅]`. -/
structure IsAwayHistory (D : ℝ → ℝ) (R c v η₀ η ta tb t3 t4 t5 : ℝ) : Prop where
  rate_pos : 0 < R
  ta_nonneg : 0 ≤ ta
  ta_le : ta ≤ tb
  tb_le : tb ≤ t3
  t3_le : t3 ≤ t4
  t4_le : t4 ≤ t5
  start_lt : η₀ < 1 / 12
  closed0 : ∀ t, 0 ≤ t → t ≤ ta → |D t| ≤ η₀
  mid1 : ∀ a b, ta ≤ a → a ≤ b → b ≤ tb → |D b - D a| ≤ v * (b - a)
  err_nonneg : 0 ≤ η
  err_lt : η < 1 / 12
  swing : ∀ t, tb ≤ t → t ≤ t3 → |D t - (1 / 4 * (1 - Real.cos (R * t)) - c)| ≤ η
  band : (-1 / 6 + η < 1 / 12 - c ∧ 1 / 12 - c ≤ 1 / 6 - η)
    ∨ (-1 / 2 + η < 1 / 12 - c ∧ 1 / 12 - c < -1 / 6 - η)
  mid2 : ∀ a b, t3 ≤ a → a ≤ b → b ≤ t4 → |D b - D a| ≤ v * (b - a)
  closed1 : ∀ a b, t4 ≤ a → a ≤ b → b ≤ t5 → |D b - D a| ≤ 1 / 6

/-- **The count of an away history.** A pointer read through the projection `π`, started at
`1/12`, with an away history: at every flow time of `[t₄, t₅]` it has a count `N` with
`|2π N − R (t₃ − t_b)| ≤ 2π (3 v ((t_b − t_a) + (t₄ − t₃)) + 7)`. -/
theorem IsAwayHistory.exists_count {X : Type*} {π : X → KTorus} {γ : ℝ → X} {q : KTorus}
    {D : ℝ → ℝ} {R c v η₀ η ta tb t3 t4 t5 : ℝ}
    (h : IsAwayHistory D R c v η₀ η ta tb t3 t4 t5) (hq : rep q.1 = 1 / 12)
    (hγ : ∀ t, 0 ≤ t → t ≤ t5 → π (γ t) = pshift (D t) q) :
    ∀ t, t4 ≤ t → t ≤ t5 →
      ∃ N : ℕ, IsTickCount {x : X | π x ∈ readyArc 2} {x : X | π x ∈ displayArc} γ t N
        ∧ |(N : ℝ) * (2 * Real.pi) - R * (t3 - tb)|
            ≤ 2 * Real.pi * (3 * v * ((tb - ta) + (t4 - t3)) + 7) :=
  away_pointer_count (Y := Unit) (γ := fun t => ((), π (γ t))) (q := q) (D := D) h.rate_pos
    h.ta_nonneg h.ta_le h.tb_le h.t3_le h.t4_le hq hγ h.start_lt h.closed0 h.mid1 h.err_nonneg
    h.err_lt h.swing h.band h.mid2 h.closed1

/-! ### M6 from five histories -/

/-- A count compared with a rate times a flow time, in the unit of the rest rate: if
`|x − R t| ≤ E` and `R = s R₀`, then `|x/R₀ − s t| ≤ E/R₀`. -/
theorem abs_div_sub_le_of_rate {x R R₀ s t E : ℝ} (hR₀ : 0 < R₀) (hR : R = s * R₀)
    (h : |x - R * t| ≤ E) : |x / R₀ - s * t| ≤ E / R₀ := by
  have e : x / R₀ - s * t = (x - R * t) / R₀ := by
    rw [hR]
    field_simp
  rw [e, abs_div, abs_of_pos hR₀]
  exact div_le_div_of_nonneg_right h hR₀.le

/-- ★★★ **M6 from the top: the Lorentz statement from five pointer histories of one run.**
One run `γ` with five pointers, read through the projections `πe`, `πr`, `πμ` (observer `B`:
emission, return, meeting) and `πρ`, `πm` (observer `A`: relay, meeting), each started at
`1/12`. Suppose `B`'s emission and meeting pointers and `A`'s relay and meeting pointers have
gated histories, closing at the flow times `t_E`, `t_M`, `t_R`, `t_M`; `B`'s return pointer
has an away history, open from the end of the emission's closing to `t_Ret`; `B`'s rate is
`√(1 − v²) R₀` and `A`'s is `R₀`; and `t_R − t_E = v (t_M − t_E)`,
`t_Ret − t_R = v (t_M − t_Ret)`. Then at every choice of flow times in the five reading
windows the pointers have counts `N_e`, `N_r`, `N_μ`, `N_ρ`, `N_m`, and with
`e = 2π N_e/R₀`, `r = 2π (N_e + N_r)/R₀`, `μ = 2π N_μ/R₀`, `ρ = 2π N_ρ/R₀`, `m = 2π N_m/R₀`
the Lorentz boost of `A`'s chart `(ρ − m, 0)` is within the stated errors of `B`'s radar
chart `((e + r)/2 − μ, −(r − e)/2)`. -/
theorem radar_lorentz_of_histories {X : Type*} {πe πr πμ πρ πm : X → KTorus} {γ : ℝ → X}
    {qe qr qμ qρ qm : KTorus} {De Dr Dμ Dρ Dm : ℝ → ℝ}
    {v R₀ RB tE tR tRet tM : ℝ} {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ
      δm vm tbm tcm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀) (hRB : RB = Real.sqrt (1 - v ^ 2) * R₀)
    (hE : tR - tE = v * (tM - tE)) (hRet : tRet - tR = v * (tM - tRet))
    (hqe : rep qe.1 = 1 / 12) (hqr : rep qr.1 = 1 / 12) (hqμ : rep qμ.1 = 1 / 12)
    (hqρ : rep qρ.1 = 1 / 12) (hqm : rep qm.1 = 1 / 12)
    (hγe : ∀ t, 0 ≤ t → t ≤ tce → πe (γ t) = pshift (De t) qe)
    (hγr : ∀ t, 0 ≤ t → t ≤ t5 → πr (γ t) = pshift (Dr t) qr)
    (hγμ : ∀ t, 0 ≤ t → t ≤ tcμ → πμ (γ t) = pshift (Dμ t) qμ)
    (hγρ : ∀ t, 0 ≤ t → t ≤ tcρ → πρ (γ t) = pshift (Dρ t) qρ)
    (hγm : ∀ t, 0 ≤ t → t ≤ tcm → πm (γ t) = pshift (Dm t) qm)
    (He : IsGatedHistory De RB δe ve tE tbe tce)
    (Hr : IsAwayHistory Dr RB c vr η₀ η tE tbe tRet t4 t5)
    (Hμ : IsGatedHistory Dμ RB δμ vμ tM tbμ tcμ)
    (Hρ : IsGatedHistory Dρ R₀ δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory Dm R₀ δm vm tM tbm tcm) :
    ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : X | πe x ∈ readyArc 2} {x : X | πe x ∈ displayArc} γ se Ne
        ∧ IsTickCount {x : X | πr x ∈ readyArc 2} {x : X | πr x ∈ displayArc} γ sr Nr
        ∧ IsTickCount {x : X | πμ x ∈ readyArc 2} {x : X | πμ x ∈ displayArc} γ sμ Nμ
        ∧ IsTickCount {x : X | πρ x ∈ readyArc 2} {x : X | πρ x ∈ displayArc} γ sρ Nρ
        ∧ IsTickCount {x : X | πm x ∈ readyArc 2} {x : X | πm x ∈ displayArc} γ sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ (2 * Real.pi * (3 * ve * (tbe - tE) + 7 / 2) / R₀
                + (2 * Real.pi * (3 * ve * (tbe - tE) + 7 / 2)
                    + 2 * Real.pi * (3 * vr * ((tbe - tE) + (t4 - tRet)) + 7)
                    + RB * (tbe - tE)) / R₀) / 2
              + 2 * Real.pi * (3 * vμ * (tbμ - tM) + 7 / 2) / R₀
              + (2 * Real.pi * (3 * vρ * (tbρ - tR) + 7 / 2) / R₀
                  + 2 * Real.pi * (3 * vm * (tbm - tM) + 7 / 2) / R₀)
                / Real.sqrt (1 - v ^ 2)
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ (2 * Real.pi * (3 * ve * (tbe - tE) + 7 / 2) / R₀
                + (2 * Real.pi * (3 * ve * (tbe - tE) + 7 / 2)
                    + 2 * Real.pi * (3 * vr * ((tbe - tE) + (t4 - tRet)) + 7)
                    + RB * (tbe - tE)) / R₀) / 2
              + v * (2 * Real.pi * (3 * vρ * (tbρ - tR) + 7 / 2) / R₀
                  + 2 * Real.pi * (3 * vm * (tbm - tM) + 7 / 2) / R₀)
                / Real.sqrt (1 - v ^ 2) := by
  intro se hse1 hse2 sr hsr1 hsr2 sμ hsμ1 hsμ2 sρ hsρ1 hsρ2 sm hsm1 hsm2
  obtain ⟨Ne, hNe, be⟩ := He.exists_count hqe hγe se hse1 hse2
  obtain ⟨Nr, hNr, br⟩ := Hr.exists_count hqr hγr sr hsr1 hsr2
  obtain ⟨Nμ, hNμ, bμ⟩ := Hμ.exists_count hqμ hγμ sμ hsμ1 hsμ2
  obtain ⟨Nρ, hNρ, bρ⟩ := Hρ.exists_count hqρ hγρ sρ hsρ1 hsρ2
  obtain ⟨Nm, hNm, bm⟩ := Hm.exists_count hqm hγm sm hsm1 hsm2
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, hNe, hNr, hNμ, hNρ, hNm, ?_⟩
  have hRB0 : 0 ≤ RB * (tbe - tE) :=
    mul_nonneg He.rate_pos.le (sub_nonneg.2 He.ta_le)
  -- the return reading against `R_B t_Ret`
  have bret : |((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) - RB * tRet|
      ≤ 2 * Real.pi * (3 * ve * (tbe - tE) + 7 / 2)
        + 2 * Real.pi * (3 * vr * ((tbe - tE) + (t4 - tRet)) + 7) + RB * (tbe - tE) := by
    have b1 := abs_le.1 be
    have b2 := abs_le.1 br
    rw [abs_le]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, hRB0]
  have he := abs_div_sub_le_of_rate hR₀ hRB be
  have hr := abs_div_sub_le_of_rate hR₀ hRB bret
  have hμ := abs_div_sub_le_of_rate hR₀ hRB bμ
  have hρ := abs_div_sub_le_of_rate hR₀ (one_mul R₀).symm bρ
  have hm := abs_div_sub_le_of_rate hR₀ (one_mul R₀).symm bm
  rw [one_mul] at hρ hm
  exact radar_lorentz_error hv0 hv hE hRet he hr hμ hρ hm

end CSD.RecordLayer

end
