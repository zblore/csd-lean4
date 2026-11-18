/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedFibreRadar
public import CsdLean4.RecordLayer.UnifiedFibreDrift
public import CsdLean4.RecordLayer.UnifiedRadarStability
public import CsdLean4.RecordLayer.UnifiedTriCarrier
public import CsdLean4.RecordLayer.UnifiedWallHistories

/-!
# Histories off the fibres where the profiles vanish: the general pieces

**Category:** 7-SigmaLayer (the record layer). BACKLOG #430 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 9 of the research delivery
plan of 2026-11-16 (an open set of pointer angles), fifth part. No new assumption beyond
UA-18.

What the walled chain's open set of pointer angles needs and no earlier module has, none of
it specific to the walled chain.

* `abs_trainF_le`, `scaledTrainF_lift_coe`, `scaledTrainF_deriv_lift_coe`, `scaledTrainF_near`
  — the profile `g · trainF` and its derivative at an angle `x`: the value is at most
  `|g| |x|`, the derivative is at most `|g|` and within `2π |g| |x|` of its value `−g` at `0`;
* `isHermitian_real_smul`, `fibreH_isHermitian`, `norm_fibreH_sub_le`, ★ `fibre_rate_le` — the
  matrix of a fibre is Hermitian, within `Σ |a_i| ‖G_i‖` of the uncoupled one, and the drift
  rate of #428 is at most `ρ (20 γ² S² T + 14 γ S)` when the profile values are at most `γ ρ`;
* ★★ `IsGatedHistory.of_fibre`, `IsAwayHistory.of_fibre` — the histories of #427 for the
  offset displacement along the free orbit of another matrix;
* `coincShift_closed_le` — the true bound on a gate displacement while its gate is closed;
* `gateOp_fst_isHermitian`, `gateOpL_isHermitian` — the remaining gates are Hermitian;
* `freeShift_tri_gate_snd`, `freeShift_tri_gate_fst`, `freeShift_tri_pair`,
  `freeShift_tri_pairL` — on a product ray of three carriers the displacement of each of the
  five gates is a two-carrier gate displacement;
* `gatedErr_add`, `awayErr_add`, `exists_pos_le`, `exists_radius` — arithmetic;
* `NearStart`, `nearStart_start` — a pointer angle within `ρ` of the start `(1/12, 0)`;
* ★★★ `penta_radar_lorentz_near` (2026-11-18, BACKLOG #438) — the open statement with an
  explicit radius for a carrier with any index type, five Hermitian observables and any
  ray, from the histories of the five `freeShift`s; `tri_radar_lorentz_near` is its case
  for three carriers from a product ray;
* ★★★ `tri_radar_lorentz_open` — for three carriers and five gates with the profiles
  `g_i · trainF`: if the five two-carrier gate displacements have the histories of #402,
  each moves by less than `1/6` while its gate is closed and the band holds strictly, then
  for every `ϵ > 0` there is a radius `ρ > 0` such that from every five pointer angles
  within `ρ` of the start the five pointers have counts and the counts satisfy the Lorentz
  statement with the errors of #402 enlarged by `ϵ`.

## Exact scope

* **General statements about any carrier.** Nothing here is about the walled chain, and
  nothing here shows that any history of the uncoupled displacements holds:
  `tri_radar_lorentz_open` is conditional on the five of them.
* **The radius of `tri_radar_lorentz_open` is not explicit**; it does not depend on the
  labelling of the carrier's basis.
* **Bounds in the operator norm**; the radius they give depends on the norms of the gates.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-197, UD-198, UD-199, UD-200); `RecordLayer/UnifiedRadarStability.lean`
(#427: `IsGatedHistory.of_drift`, `IsAwayHistory.of_drift`);
`RecordLayer/UnifiedFibreDrift.lean` (#428: `freeShift_drift`);
`RecordLayer/UnifiedFibreRun.lean` (#428: `fibreH`); `RecordLayer/UnifiedTriCarrier.lean`
(#405: `gateOpL`, `gateOp_snd_isHermitian`, `coincShift_gate_snd`);
`RecordLayer/UnifiedWallHistories.lean` (#419: `isGatedHistory_coincShift`);
`RecordLayer/UnifiedGatedReading.lean` (`abs_coincShift_sub_le`);
`RecordLayer/UnifiedEmissionReading.lean` (`scaledTrainF`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The profile near its zero -/

/-- The profile `trainF` is at most `|x|`. -/
theorem abs_trainF_le (x : ℝ) : |trainF x| ≤ |x| := by
  have h := Real.abs_sin_sub_sin_le (2 * Real.pi * x) 0
  rw [Real.sin_zero, sub_zero, sub_zero, abs_mul, abs_of_pos Real.two_pi_pos] at h
  rw [trainF, abs_div, abs_neg, abs_of_pos Real.two_pi_pos, div_le_iff₀ Real.two_pi_pos]
  linarith only [h]

/-- The scaled profile at the angle `x`. -/
theorem scaledTrainF_lift_coe (g x : ℝ) :
    (scaledTrainF_periodic g).lift ((x : ℝ) : AddCircle (1 : ℝ)) = g * trainF x := by
  rw [Function.Periodic.lift_coe]
  rfl

/-- The derivative of the scaled profile at the angle `x`. -/
theorem scaledTrainF_deriv_lift_coe (g x : ℝ) :
    (scaledTrainF_periodic g).deriv_periodic.lift ((x : ℝ) : AddCircle (1 : ℝ))
      = -(g * Real.cos (2 * Real.pi * x)) := by
  have h := (hasDerivAt_trainF x).const_mul g
  rw [Function.Periodic.lift_coe, show scaledTrainF g = fun x => g * trainF x from rfl, h.deriv]
  ring

/-- ★ **The scaled profile near its zero.** At an angle `x` with `|x| ≤ ρ`, for a strength
`|g| ≤ γ`: the value is at most `γ ρ`, the derivative at most `γ`, and the derivative is
within `7 γ ρ` of its value `−g` at `0`. -/
theorem scaledTrainF_near {g γ ρ x : ℝ} {φ : AddCircle (1 : ℝ)}
    (hφ : φ = ((x : ℝ) : AddCircle (1 : ℝ))) (hg : |g| ≤ γ) (hx : |x| ≤ ρ) :
    |(scaledTrainF_periodic g).lift φ| ≤ γ * ρ
      ∧ |(scaledTrainF_periodic g).deriv_periodic.lift φ| ≤ γ
      ∧ |(scaledTrainF_periodic g).deriv_periodic.lift φ - -g| ≤ γ * (7 * ρ) := by
  subst hφ
  have hγ : 0 ≤ γ := (abs_nonneg g).trans hg
  have hρ : 0 ≤ ρ := (abs_nonneg x).trans hx
  refine ⟨?_, ?_, ?_⟩
  · rw [scaledTrainF_lift_coe, abs_mul]
    exact mul_le_mul hg ((abs_trainF_le x).trans hx) (abs_nonneg _) hγ
  · rw [scaledTrainF_deriv_lift_coe, abs_neg, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg g) (Real.abs_cos_le_one _)).trans hg
  · rw [scaledTrainF_deriv_lift_coe]
    have h := Real.abs_cos_sub_cos_le (2 * Real.pi * x) 0
    rw [Real.cos_zero, sub_zero, abs_mul, abs_of_pos Real.two_pi_pos] at h
    have e : -(g * Real.cos (2 * Real.pi * x)) - -g
        = -(g * (Real.cos (2 * Real.pi * x) - 1)) := by ring
    rw [e, abs_neg, abs_mul]
    have h7 : |Real.cos (2 * Real.pi * x) - 1| ≤ 7 * ρ := by
      have hπ := Real.pi_lt_d2
      have hx0 := abs_nonneg x
      nlinarith only [h, hx, hπ, hx0, Real.pi_pos]
    exact mul_le_mul hg h7 (abs_nonneg _) hγ

/-! ### Arithmetic -/

/-- The error of a gated count at a larger speed. -/
theorem gatedErr_add (v lam ta tb : ℝ) :
    gatedErr (v + lam) ta tb = gatedErr v ta tb + 6 * Real.pi * lam * (tb - ta) := by
  unfold gatedErr
  ring

/-- The error of an away count at a larger speed. -/
theorem awayErr_add (v lam ta tb t3 t4 : ℝ) :
    awayErr (v + lam) ta tb t3 t4
      = awayErr v ta tb t3 t4 + 6 * Real.pi * lam * ((tb - ta) + (t4 - t3)) := by
  unfold awayErr
  ring

/-- Two positive numbers have a positive lower bound. -/
theorem exists_pos_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ∃ s : ℝ, 0 < s ∧ s ≤ a ∧ s ≤ b :=
  ⟨min a b, lt_min ha hb, min_le_left _ _, min_le_right _ _⟩

/-- A radius small against a slack `s` and an error `ϵ`. -/
theorem exists_radius {s ϵ A B : ℝ} (hs : 0 < s) (hϵ : 0 < ϵ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ s ∧ ρ * A ≤ s ∧ ρ * B ≤ ϵ := by
  have hA1 : 0 < A + 1 := by linarith only [hA]
  have hB1 : 0 < B + 1 := by linarith only [hB]
  refine ⟨min 1 (min s (min (s / (A + 1)) (ϵ / (B + 1)))),
    lt_min one_pos (lt_min hs (lt_min (div_pos hs hA1) (div_pos hϵ hB1))), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_, ?_⟩
  · set ρ := min 1 (min s (min (s / (A + 1)) (ϵ / (B + 1))))
    have hρ0 : 0 < ρ := lt_min one_pos (lt_min hs (lt_min (div_pos hs hA1) (div_pos hϵ hB1)))
    have h1 : ρ ≤ s / (A + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ hA1] at h1
    linarith only [h1, hρ0]
  · set ρ := min 1 (min s (min (s / (A + 1)) (ϵ / (B + 1))))
    have hρ0 : 0 < ρ := lt_min one_pos (lt_min hs (lt_min (div_pos hs hA1) (div_pos hϵ hB1)))
    have h1 : ρ ≤ ϵ / (B + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ hB1] at h1
    linarith only [h1, hρ0]

/-! ### The matrix of a fibre -/

section Fibre

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {H H' G G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ}

omit [Fintype ν] [DecidableEq ν] in
/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_real_smul (hG : G.IsHermitian) (w : ℝ) : ((w : ℂ) • G).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hG.eq, Complex.star_def,
    Complex.conj_ofReal]

omit [Fintype ν] [DecidableEq ν] in
/-- The matrix of a fibre is Hermitian. -/
theorem fibreH_isHermitian (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian) (hG₂ : G₂.IsHermitian)
    (hG₃ : G₃.IsHermitian) (hG₄ : G₄.IsHermitian) (hG₅ : G₅.IsHermitian) (a b c d w : ℝ) :
    (fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w).IsHermitian := by
  unfold fibreH
  exact ((((hH.add (isHermitian_real_smul hG₅ w)).add (isHermitian_real_smul hG₄ d)).add
    (isHermitian_real_smul hG₃ c)).add (isHermitian_real_smul hG₁ a)).add
    (isHermitian_real_smul hG₂ b)

/-- The matrix of a fibre is within `Σ |a_i| ‖G_i‖` of the uncoupled one. -/
theorem norm_fibreH_sub_le (H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ) (a b c d w : ℝ) :
    ‖fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H‖
      ≤ |a| * ‖G₁‖ + |b| * ‖G₂‖ + |c| * ‖G₃‖ + |d| * ‖G₄‖ + |w| * ‖G₅‖ := by
  have e : fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H
      = (w : ℂ) • G₅ + (d : ℂ) • G₄ + (c : ℂ) • G₃ + (a : ℂ) • G₁ + (b : ℂ) • G₂ := by
    unfold fibreH
    abel
  have n : ∀ (x : ℝ) (G : Matrix ν ν ℂ), ‖(x : ℂ) • G‖ ≤ |x| * ‖G‖ := fun x G => by
    refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [e]
  have h1 := norm_add_le ((w : ℂ) • G₅ + (d : ℂ) • G₄ + (c : ℂ) • G₃ + (a : ℂ) • G₁)
    ((b : ℂ) • G₂)
  have h2 := norm_add_le ((w : ℂ) • G₅ + (d : ℂ) • G₄ + (c : ℂ) • G₃) ((a : ℂ) • G₁)
  have h3 := norm_add_le ((w : ℂ) • G₅ + (d : ℂ) • G₄) ((c : ℂ) • G₃)
  have h4 := norm_add_le ((w : ℂ) • G₅) ((d : ℂ) • G₄)
  linarith only [h1, h2, h3, h4, n w G₅, n d G₄, n c G₃, n a G₁, n b G₂]

/-- ★ **The drift rate on a fibre near the zero fibres.** If the five profile values are at
most `γ ρ`, the five observables and `G` have norm at most `S`, and the strength `z'` is at
most `γ` and within `7 γ ρ` of `z`: the drift rate of #428 up to `t_c ≤ T` is at most
`ρ (20 γ² S² T + 14 γ S)`. -/
theorem fibre_rate_le {a b c d w z z' γ S ρ T tc : ℝ} (ha : |a| ≤ γ * ρ) (hb : |b| ≤ γ * ρ)
    (hc : |c| ≤ γ * ρ) (hd : |d| ≤ γ * ρ) (hw : |w| ≤ γ * ρ) (h₁ : ‖G₁‖ ≤ S) (h₂ : ‖G₂‖ ≤ S)
    (h₃ : ‖G₃‖ ≤ S) (h₄ : ‖G₄‖ ≤ S) (h₅ : ‖G₅‖ ≤ S) (hG : ‖G‖ ≤ S) (hz' : |z'| ≤ γ)
    (hzz : |z' - z| ≤ γ * (7 * ρ)) (hρ : 0 ≤ ρ) (htc0 : 0 ≤ tc) (htc : tc ≤ T) :
    4 * |z'| * ‖G‖ * tc * ‖fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H‖ + 2 * |z' - z| * ‖G‖
      ≤ ρ * (20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) := by
  have hγ : 0 ≤ γ := (abs_nonneg z').trans hz'
  have hS : 0 ≤ S := (norm_nonneg G).trans hG
  have hT : 0 ≤ T := htc0.trans htc
  have hγρ : 0 ≤ γ * ρ := mul_nonneg hγ hρ
  have p : ∀ {x : ℝ} {K : Matrix ν ν ℂ}, |x| ≤ γ * ρ → ‖K‖ ≤ S → |x| * ‖K‖ ≤ γ * ρ * S :=
    fun hx hK => mul_le_mul hx hK (norm_nonneg _) hγρ
  have hE : ‖fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H‖ ≤ 5 * (γ * ρ) * S := by
    have := norm_fibreH_sub_le H G₁ G₂ G₃ G₄ G₅ a b c d w
    linarith only [this, p ha h₁, p hb h₂, p hc h₃, p hd h₄, p hw h₅]
  have hE0 : 0 ≤ ‖fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H‖ := norm_nonneg _
  have hz0 : 0 ≤ |z'| := abs_nonneg _
  have hG0 : 0 ≤ ‖G‖ := norm_nonneg _
  have t1 : 4 * |z'| * ‖G‖ * tc * ‖fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H‖
      ≤ 4 * γ * S * T * (5 * (γ * ρ) * S) := by
    have s1 : |z'| * ‖G‖ ≤ γ * S := mul_le_mul hz' hG hG0 hγ
    have s2 : |z'| * ‖G‖ * tc ≤ γ * S * T :=
      mul_le_mul s1 htc htc0 (mul_nonneg hγ hS)
    have s3 : |z'| * ‖G‖ * tc * ‖fibreH H G₁ G₂ G₃ G₄ G₅ a b c d w - H‖
        ≤ γ * S * T * (5 * (γ * ρ) * S) :=
      mul_le_mul s2 hE hE0 (mul_nonneg (mul_nonneg hγ hS) hT)
    linarith only [s3]
  have t2 : 2 * |z' - z| * ‖G‖ ≤ 2 * (γ * (7 * ρ)) * S := by
    have s1 : |z' - z| * ‖G‖ ≤ γ * (7 * ρ) * S :=
      mul_le_mul hzz hG hG0 (mul_nonneg hγ (by linarith only [hρ]))
    linarith only [s1]
  have e : 4 * γ * S * T * (5 * (γ * ρ) * S) + 2 * (γ * (7 * ρ)) * S
      = ρ * (20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) := by ring
  linarith only [t1, t2, e]

variable [Nonempty ν]

/-- ★★ **A gated history on a fibre.** If the displacement along the free orbit of `H` with
strength `z` has a gated history and moves by at most `c₀` while its gate is closed, then the
displacement along the free orbit of `H'` with strength `z'`, offset by `|η| ≤ η₀`, has a
gated history with error `δ + η₀ + lam t_c` and speed `v + lam`, for any `lam` at least the
drift rate of #428, provided the error stays below `1/12` and `c₀ + lam (t_c − t_b) ≤ 1/6`. -/
theorem IsGatedHistory.of_fibre {R δ v ta tb tc c₀ lam η₀ η z z' : ℝ} {p : GenArena ν}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (h : IsGatedHistory (freeShift hH G z p) R δ v ta tb tc)
    (hcl : ∀ s t, tb ≤ s → s ≤ t → t ≤ tc →
      |freeShift hH G z p t - freeShift hH G z p s| ≤ c₀)
    (hrate : 4 * |z'| * ‖G‖ * tc * ‖H' - H‖ + 2 * |z' - z| * ‖G‖ ≤ lam)
    (hη : |η| ≤ η₀) (hδ : δ + η₀ + lam * tc < 1 / 12) (hc : c₀ + lam * (tc - tb) ≤ 1 / 6) :
    IsGatedHistory (fun t => η + freeShift hH' G z' p t) R (δ + η₀ + lam * tc) (v + lam) ta
      tb tc := by
  have htc : 0 ≤ tc := h.ta_nonneg.trans (h.ta_le.trans h.tb_le)
  have hlam : 0 ≤ lam := le_trans (by positivity) hrate
  refine h.of_drift hcl hlam (fun s t hs hst ht => ?_) ?_ hδ hc
  · have d := freeShift_drift hH hH' G z z' p hs hst ht
    have e : (η + freeShift hH' G z' p t - freeShift hH G z p t)
          - (η + freeShift hH' G z' p s - freeShift hH G z p s)
        = (freeShift hH' G z' p t - freeShift hH G z p t)
          - (freeShift hH' G z' p s - freeShift hH G z p s) := by ring
    rw [e]
    exact d.trans (mul_le_mul_of_nonneg_right hrate (sub_nonneg.2 hst))
  · rw [freeShift_zero, freeShift_zero, add_zero, sub_zero]
    exact hη

/-- ★★ **An away history on a fibre.** The same for an away history, which moves by at most
`c₁` while its gate is closed again: start error `η₀ + ρ₀ + lam t₅`, error `η + ρ₀ + lam t₅`,
speed `v + lam`, the same offset. The band for the enlarged error is a hypothesis. -/
theorem IsAwayHistory.of_fibre {R c v η₀ η ta tb t3 t4 t5 c₁ lam ρ₀ ηs z z' : ℝ}
    {p : GenArena ν} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (h : IsAwayHistory (freeShift hH G z p) R c v η₀ η ta tb t3 t4 t5)
    (hcl : ∀ a b, t4 ≤ a → a ≤ b → b ≤ t5 →
      |freeShift hH G z p b - freeShift hH G z p a| ≤ c₁)
    (hrate : 4 * |z'| * ‖G‖ * t5 * ‖H' - H‖ + 2 * |z' - z| * ‖G‖ ≤ lam)
    (hηs : |ηs| ≤ ρ₀) (hη₀ : η₀ + ρ₀ + lam * t5 < 1 / 12)
    (hη : η + ρ₀ + lam * t5 < 1 / 12)
    (hband : (-1 / 6 + (η + ρ₀ + lam * t5) < 1 / 12 - c
        ∧ 1 / 12 - c ≤ 1 / 6 - (η + ρ₀ + lam * t5))
      ∨ (-1 / 2 + (η + ρ₀ + lam * t5) < 1 / 12 - c
        ∧ 1 / 12 - c < -1 / 6 - (η + ρ₀ + lam * t5)))
    (hc : c₁ + lam * (t5 - t4) ≤ 1 / 6) :
    IsAwayHistory (fun t => ηs + freeShift hH' G z' p t) R c (v + lam) (η₀ + ρ₀ + lam * t5)
      (η + ρ₀ + lam * t5) ta tb t3 t4 t5 := by
  have ht5 : 0 ≤ t5 :=
    h.ta_nonneg.trans (h.ta_le.trans (h.tb_le.trans (h.t3_le.trans h.t4_le)))
  have hlam : 0 ≤ lam := le_trans (by positivity) hrate
  refine h.of_drift hcl hlam (fun s t hs hst ht => ?_) ?_ hη₀ hη hband hc
  · have d := freeShift_drift hH hH' G z z' p hs hst ht
    have e : (ηs + freeShift hH' G z' p t - freeShift hH G z p t)
          - (ηs + freeShift hH' G z' p s - freeShift hH G z p s)
        = (freeShift hH' G z' p t - freeShift hH G z p t)
          - (freeShift hH' G z' p s - freeShift hH G z p s) := by ring
    rw [e]
    exact d.trans (mul_le_mul_of_nonneg_right hrate (sub_nonneg.2 hst))
  · rw [freeShift_zero, freeShift_zero, add_zero, sub_zero]
    exact hηs

end Fibre

/-! ### The true closing bound -/

section Closed

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {Y : Matrix κ κ ℂ}

/-- **The true closing bound.** While the two carriers have weight at most `ε` inside the
relation, on `[t_b, t_c]`, the gate displacement moves by at most `2 |z| ε (t_c − t_b)`. -/
theorem coincShift_closed_le (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (z : ℝ) (p : GenArena ι) (q : GenArena κ) {ε tb tc : ℝ} (hε : 0 ≤ ε)
    (hclosed : ∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε) :
    ∀ s t, tb ≤ s → s ≤ t → t ≤ tc →
      |coincShift hA hC (gateOp σ τ r Y) z p q t - coincShift hA hC (gateOp σ τ r Y) z p q s|
        ≤ 2 * |z| * ε * (tc - tb) := by
  intro s t hbs hst htc
  have h := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := ε) hst
    (fun u hsu hut => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans
      (hclosed u (hbs.trans hsu) (hut.trans htc)))
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hmono : 2 * |z| * ε * (t - s) ≤ 2 * |z| * ε * (tc - tb) :=
    mul_le_mul_of_nonneg_left (by linarith only [hbs, htc]) (by positivity)
  linarith only [h, hmono]

end Closed

/-! ### The gates of three carriers -/

section Gates

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] [Fintype S] [DecidableEq S]
  (σ : ι → S) (α : κa → S) (β : κb → S) (r : S → S → Prop) [DecidableRel r]

omit [Fintype S] [DecidableEq S] in
/-- The gate between the first carrier and the first member of a composite is Hermitian when
`Y` is Hermitian and does not move that member between sites. -/
theorem gateOp_fst_isHermitian {Y : Matrix κa κa ℂ} (hYh : Y.IsHermitian)
    (hY : ∀ i j, α i ≠ α j → Y i j = 0) :
    (gateOp σ (fun k : κa × κb => α k.1) r (Y ⊗ₖ (1 : Matrix κb κb ℂ))).IsHermitian := by
  refine gateOp_isHermitian σ _ r (kronecker_isHermitian hYh Matrix.isHermitian_one) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  rw [Matrix.kroneckerMap_apply, hY a a' h, zero_mul]

omit [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι] in
/-- The gate of two carriers with the operator on the first is Hermitian when `Y` is
Hermitian and does not move the first carrier between sites. -/
theorem gateOpL_isHermitian {Y : Matrix κa κa ℂ} (hYh : Y.IsHermitian)
    (hY : ∀ i j, α i ≠ α j → Y i j = 0) : (gateOpL α β r Y).IsHermitian := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [Matrix.conjTranspose_apply, gateOpL, coincProj, Matrix.diagonal_mul,
    Matrix.diagonal_mul, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.one_apply]
  have hYa : star (Y a' a) = Y a a' := hYh.apply a a'
  by_cases hb : b = b'
  · subst hb
    by_cases ha : α a = α a'
    · simp only [ha, ite_true, mul_one, star_mul', hYa]
      split_ifs <;> simp
    · simp [hY a a' ha, hY a' a (Ne.symm ha)]
  · simp [hb, Ne.symm hb]

variable {M₀ : Matrix ι ι ℂ} {A₀ : Matrix κa κa ℂ} {B₀ : Matrix κb κb ℂ}

/-- The displacement of the messenger's gate with the second clock, on a product ray of three
carriers. -/
theorem freeShift_tri_gate_snd (hM : M₀.IsHermitian) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (Y : Matrix κb κb ℂ) (z : ℝ) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) :
    freeShift (compositeH_isHermitian hM (compositeH_isHermitian hA hB))
        (gateOp σ (fun k : κa × κb => β k.2) r ((1 : Matrix κa κa ℂ) ⊗ₖ Y)) z
        (prodRay p (prodRay qa qb))
      = coincShift hM hB (gateOp σ β r Y) z p qb :=
  funext fun t => by
    rw [freeShift_prodRay hM (compositeH_isHermitian hA hB), coincShift_gate_snd σ β r hM hA hB]

/-- The displacement of the messenger's gate with the first clock, on a product ray of three
carriers. -/
theorem freeShift_tri_gate_fst (hM : M₀.IsHermitian) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (Y : Matrix κa κa ℂ) (z : ℝ) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) :
    freeShift (compositeH_isHermitian hM (compositeH_isHermitian hA hB))
        (gateOp σ (fun k : κa × κb => α k.1) r (Y ⊗ₖ (1 : Matrix κb κb ℂ))) z
        (prodRay p (prodRay qa qb))
      = coincShift hM hA (gateOp σ α r Y) z p qa :=
  funext fun t => by
    rw [freeShift_prodRay hM (compositeH_isHermitian hA hB), coincShift_gate_fst σ α r hM hA hB]

omit [Fintype S] [DecidableEq S] in
/-- The displacement of the two clocks' gate with the operator on the second, on a product
ray of three carriers. -/
theorem freeShift_tri_pair (hM : M₀.IsHermitian) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (Y : Matrix κb κb ℂ) (z : ℝ) (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb) :
    freeShift (compositeH_isHermitian hM (compositeH_isHermitian hA hB))
        ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r Y) z (prodRay p (prodRay qa qb))
      = coincShift hA hB (gateOp α β r Y) z qa qb :=
  funext fun t => by
    rw [freeShift_prodRay hM (compositeH_isHermitian hA hB),
      coincShift_one_kronecker_pair hM hA hB]

/-- The displacement of the two clocks' gate with the operator on the first, on a product
ray of three carriers. -/
theorem freeShift_tri_pairL (hM : M₀.IsHermitian) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (Y : Matrix κa κa ℂ) (z : ℝ) (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb) :
    freeShift (compositeH_isHermitian hM (compositeH_isHermitian hA hB))
        ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r Y) z (prodRay p (prodRay qa qb))
      = coincShift hB hA (gateOp β α (fun s s' => r s' s) Y) z qb qa :=
  funext fun t => by
    rw [freeShift_prodRay hM (compositeH_isHermitian hA hB),
      coincShift_one_kronecker_pair hM hA hB, coincShift_gateOpL]

end Gates

/-! ### The gates have norm at most one -/

section Norms

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian idempotent has norm at most `1`. -/
theorem norm_le_one_of_isHermitian_idem {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (h : P * P = P) : ‖P‖ ≤ 1 := by
  have h1 := CStarRing.norm_star_mul_self (x := P)
  rw [Matrix.star_eq_conjTranspose, hP.eq, h] at h1
  have h0 := norm_nonneg P
  by_contra h'
  rw [not_le] at h'
  have h2 : 0 < (‖P‖ - 1) * ‖P‖ := mul_pos (by linarith only [h']) (by linarith only [h'])
  nlinarith only [h1, h2]

/-- A Hermitian involution has norm at most `1`. -/
theorem norm_le_one_of_isHermitian_invol {U : Matrix n n ℂ} (hU : U.IsHermitian)
    (h : U * U = 1) : ‖U‖ ≤ 1 := by
  have h1 := CStarRing.norm_star_mul_self (x := U)
  rw [Matrix.star_eq_conjTranspose, hU.eq, h] at h1
  have h2 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
    norm_le_one_of_isHermitian_idem Matrix.isHermitian_one (one_mul 1)
  have h0 := norm_nonneg U
  nlinarith only [h1, h2, h0]

/-- A Hermitian idempotent times a Hermitian involution has norm at most `1`. -/
theorem norm_idem_mul_invol_le_one {P U : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hU : U.IsHermitian) (hUU : U * U = 1) : ‖P * U‖ ≤ 1 := by
  have h1 := norm_le_one_of_isHermitian_idem hP hPP
  have h2 := norm_le_one_of_isHermitian_invol hU hUU
  have h3 := norm_mul_le P U
  nlinarith only [h1, h2, h3, norm_nonneg P, norm_nonneg U]

end Norms

section GateNorms

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] (σ : ι → S) (α : κa → S) (β : κb → S)
  (r : S → S → Prop) [DecidableRel r]

/-- A gate with a Hermitian involution has norm at most `1`. -/
theorem norm_gateOp_le_one {κ : Type*} [Fintype κ] [DecidableEq κ] (τ : κ → S)
    {Y : Matrix κ κ ℂ} (hY : Y.IsHermitian) (hYY : Y * Y = 1) : ‖gateOp σ τ r Y‖ ≤ 1 := by
  rw [gateOp]
  refine norm_idem_mul_invol_le_one (coincProj_isHermitian σ τ r) (coincProj_mul_self σ τ r)
    (kronecker_isHermitian Matrix.isHermitian_one hY) ?_
  rw [← Matrix.mul_kronecker_mul, one_mul, hYY, Matrix.one_kronecker_one]

/-- **The five gates of three carriers have norm at most `1`** when the two gated operators
are Hermitian involutions. -/
theorem tri_gate_norms_le_one (r₁ r₂ r₃ r₄ r₅ : S → S → Prop) [DecidableRel r₁]
    [DecidableRel r₂] [DecidableRel r₃] [DecidableRel r₄] [DecidableRel r₅]
    {Ya : Matrix κa κa ℂ} {Yb : Matrix κb κb ℂ} (hYa : Ya.IsHermitian) (hYaa : Ya * Ya = 1)
    (hYb : Yb.IsHermitian) (hYbb : Yb * Yb = 1) :
    ‖gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ 1
      ∧ ‖gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ 1
      ∧ ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb‖ ≤ 1
      ∧ ‖gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))‖ ≤ 1
      ∧ ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya‖ ≤ 1 := by
  have i1 : ((1 : Matrix κa κa ℂ) ⊗ₖ Yb) * ((1 : Matrix κa κa ℂ) ⊗ₖ Yb) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, hYbb, Matrix.one_kronecker_one]
  have i2 : (Ya ⊗ₖ (1 : Matrix κb κb ℂ)) * (Ya ⊗ₖ (1 : Matrix κb κb ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, one_mul, hYaa, Matrix.one_kronecker_one]
  have h1b := kronecker_isHermitian (Matrix.isHermitian_one (n := κa)) hYb
  have ha1 := kronecker_isHermitian hYa (Matrix.isHermitian_one (n := κb))
  have pI : ∀ {P : Matrix (κa × κb) (κa × κb) ℂ}, P.IsHermitian → P * P = P →
      ∀ {U : Matrix (κa × κb) (κa × κb) ℂ}, U.IsHermitian → U * U = 1 →
      ‖(1 : Matrix ι ι ℂ) ⊗ₖ (P * U)‖ ≤ 1 := by
    intro P hP hPP U hU hUU
    have e : (1 : Matrix ι ι ℂ) ⊗ₖ (P * U)
        = ((1 : Matrix ι ι ℂ) ⊗ₖ P) * ((1 : Matrix ι ι ℂ) ⊗ₖ U) := by
      rw [← Matrix.mul_kronecker_mul, one_mul]
    rw [e]
    refine norm_idem_mul_invol_le_one (kronecker_isHermitian Matrix.isHermitian_one hP) ?_
      (kronecker_isHermitian Matrix.isHermitian_one hU) ?_
    · rw [← Matrix.mul_kronecker_mul, one_mul, hPP]
    · rw [← Matrix.mul_kronecker_mul, one_mul, hUU, Matrix.one_kronecker_one]
  refine ⟨norm_gateOp_le_one σ r₁ _ h1b i1, norm_gateOp_le_one σ r₂ _ h1b i1, ?_,
    norm_gateOp_le_one σ r₄ _ ha1 i2, ?_⟩
  · rw [gateOp]
    exact pI (coincProj_isHermitian α β r₃) (coincProj_mul_self α β r₃)
      (kronecker_isHermitian Matrix.isHermitian_one hYb)
      (by rw [← Matrix.mul_kronecker_mul, one_mul, hYbb, Matrix.one_kronecker_one])
  · rw [gateOpL]
    exact pI (coincProj_isHermitian α β r₅) (coincProj_mul_self α β r₅) ha1 i2

end GateNorms


/-! ### An open set of pointer angles, for three carriers and five gates -/

/-- **A pointer angle within `ρ` of the start `(1/12, 0)`**: its moving angle is `1/12 + η`
and its conserved angle is `x`, as classes modulo `1`, with `|η| < ρ` and `|x| < ρ`. -/
def NearStart (ρ : ℝ) (θ : KTorus) : Prop :=
  ∃ η x : ℝ, |η| < ρ ∧ |x| < ρ ∧ θ.1 = ((1 / 12 + η : ℝ) : AddCircle (1 : ℝ))
    ∧ θ.2 = ((x : ℝ) : AddCircle (1 : ℝ))

/-- The start itself is within any positive `ρ` of the start. -/
theorem nearStart_start {ρ : ℝ} (hρ : 0 < ρ) :
    NearStart ρ ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) :=
  ⟨0, 0, by rwa [abs_zero], by rwa [abs_zero], by rw [add_zero], rfl⟩

section PentaNear

variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
  {H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ}

/-- ★★★ **M6 from the top from every pointer angle within an explicit radius, for any carrier
and any ray.** The flow of UA-18's arena for a carrier with any index type, five Hermitian
observables of norm at most `S` and the profiles `g_i · trainF`, from any ray `P`. If the five
displacements `freeShift G_i (−g_i)` along the free orbit from `P` have the histories of
`radar_lorentz_of_histories` (#402) with a slack `s` below every margin, then every `ρ > 0`
with `ρ ≤ s/4`, `ρ C T ≤ s/4` and `ρ C (K₁ + K₂) ≤ ϵ`, `C = 20 γ² S² T + 14 γ S`, is a radius:
from every five pointer angles within `ρ` of `(1/12, 0)` the five pointers have counts and
the counts satisfy the Lorentz statement with the errors of #402 enlarged by `ϵ`. The ray
need not be a product of carriers' rays; `tri_radar_lorentz_near` is the case of three
carriers from a product ray. -/
theorem penta_radar_lorentz_near (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian)
    (hG₂ : G₂.IsHermitian) (hG₃ : G₃.IsHermitian) (hG₄ : G₄.IsHermitian)
    (hG₅ : G₅.IsHermitian) (g₁ g₂ g₃ g₄ g₅ : ℝ) (P : GenArena ν)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    {ce cr cμ cρ cm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (freeShift hH G₁ (-g₁) P) RB δe ve tE tbe tce)
    (Hr : IsAwayHistory (freeShift hH G₂ (-g₂) P) RB c vr η₀ η tE tbe tRet t4 t5)
    (Hμ : IsGatedHistory (freeShift hH G₃ (-g₃) P) RB δμ vμ tMB tbμ tcμ)
    (Hρ : IsGatedHistory (freeShift hH G₄ (-g₄) P) R₀ δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory (freeShift hH G₅ (-g₅) P) R₀ δm vm tMA tbm tcm)
    (hce : ∀ s t, tbe ≤ s → s ≤ t → t ≤ tce →
      |freeShift hH G₁ (-g₁) P t - freeShift hH G₁ (-g₁) P s| ≤ ce)
    (hcr : ∀ s t, t4 ≤ s → s ≤ t → t ≤ t5 →
      |freeShift hH G₂ (-g₂) P t - freeShift hH G₂ (-g₂) P s| ≤ cr)
    (hcμ : ∀ s t, tbμ ≤ s → s ≤ t → t ≤ tcμ →
      |freeShift hH G₃ (-g₃) P t - freeShift hH G₃ (-g₃) P s| ≤ cμ)
    (hcρ : ∀ s t, tbρ ≤ s → s ≤ t → t ≤ tcρ →
      |freeShift hH G₄ (-g₄) P t - freeShift hH G₄ (-g₄) P s| ≤ cρ)
    (hcm : ∀ s t, tbm ≤ s → s ≤ t → t ≤ tcm →
      |freeShift hH G₅ (-g₅) P t - freeShift hH G₅ (-g₅) P s| ≤ cm)
    {ϵ S γ T s ρ : ℝ}
    (hS1 : ‖G₁‖ ≤ S) (hS2 : ‖G₂‖ ≤ S) (hS3 : ‖G₃‖ ≤ S) (hS4 : ‖G₄‖ ≤ S) (hS5 : ‖G₅‖ ≤ S)
    (hγ1 : |g₁| ≤ γ) (hγ2 : |g₂| ≤ γ) (hγ3 : |g₃| ≤ γ) (hγ4 : |g₄| ≤ γ) (hγ5 : |g₅| ≤ γ)
    (hT1 : tce ≤ T) (hT2 : t5 ≤ T) (hT3 : tcμ ≤ T) (hT4 : tcρ ≤ T) (hT5 : tcm ≤ T)
    (sp : 0 < s) (q1 : s ≤ 1 / 12 - δe) (q2 : s ≤ 1 / 12 - η₀) (q3 : s ≤ 1 / 12 - η)
    (q4 : s ≤ 1 / 12 - c - (-1 / 6 + η)) (q5 : s ≤ 1 / 6 - η - (1 / 12 - c))
    (q6 : s ≤ 1 / 12 - δμ) (q7 : s ≤ 1 / 12 - δρ) (q8 : s ≤ 1 / 12 - δm)
    (q9 : s ≤ 1 / 6 - ce) (q10 : s ≤ 1 / 6 - cr) (q11 : s ≤ 1 / 6 - cμ)
    (q12 : s ≤ 1 / 6 - cρ) (q13 : s ≤ 1 / 6 - cm) (hρ0 : 0 < ρ) (hρs : ρ ≤ s / 4)
    (hρA' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * T) ≤ s / 4)
    (hρB' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe
        - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))) ≤ ϵ) :
    ∀ (N : ℕ) (e : ν ≃ Fin (N + 1)) (θ ψ χ ξ ζ : KTorus),
      NearStart ρ θ → NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
      ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e P, θ), ψ), χ), ξ), ζ)) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e P, θ), ψ), χ), ξ), ζ)) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e P, θ), ψ), χ), ξ), ζ)) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e P, θ), ψ), χ), ξ), ζ)) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e P, θ), ψ), χ), ξ), ζ)) sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr vμ tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ + ϵ := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hS1
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans hγ1
  -- the times
  have htbe0 : 0 ≤ tbe := He.ta_nonneg.trans He.ta_le
  have htce0 : 0 ≤ tce := htbe0.trans He.tb_le
  have ht40 : 0 ≤ t4 := (htbe0.trans Hr.tb_le).trans Hr.t3_le
  have ht50 : 0 ≤ t5 := ht40.trans Hr.t4_le
  have htbμ0 : 0 ≤ tbμ := Hμ.ta_nonneg.trans Hμ.ta_le
  have htcμ0 : 0 ≤ tcμ := htbμ0.trans Hμ.tb_le
  have htbρ0 : 0 ≤ tbρ := Hρ.ta_nonneg.trans Hρ.ta_le
  have htcρ0 : 0 ≤ tcρ := htbρ0.trans Hρ.tb_le
  have htbm0 : 0 ≤ tbm := Hm.ta_nonneg.trans Hm.ta_le
  have htcm0 : 0 ≤ tcm := htbm0.trans Hm.tb_le
  obtain ⟨Tm, hTm⟩ : ∃ Tm : ℝ, Tm = T := ⟨_, rfl⟩
  have hTm0 : 0 ≤ Tm := by linarith only [hTm, htce0, hT1]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 20 * γ ^ 2 * S ^ 2 * Tm + 14 * γ * S := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    positivity
  -- the error's coefficients
  have hsq : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith only [hv0, hv])
  have ka : 0 ≤ (tbe - tE) / R₀ := div_nonneg (sub_nonneg.2 He.ta_le) hR₀.le
  have kb : 0 ≤ ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀ :=
    div_nonneg (by linarith only [He.ta_le, Hr.t3_le]) hR₀.le
  have km : 0 ≤ (tbμ - tMB) / R₀ := div_nonneg (sub_nonneg.2 Hμ.ta_le) hR₀.le
  have kr : 0 ≤ (tbρ - tR) / R₀ := div_nonneg (sub_nonneg.2 Hρ.ta_le) hR₀.le
  have kq : 0 ≤ (tbm - tMA) / R₀ := div_nonneg (sub_nonneg.2 Hm.ta_le) hR₀.le
  have hK1 : 0 ≤ (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
    mul_nonneg (by positivity) (add_nonneg (add_nonneg (div_nonneg (add_nonneg ka kb)
      (by norm_num)) km) (div_nonneg (add_nonneg kr kq) hsq.le))
  have hK2 : 0 ≤ (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
    mul_nonneg (by positivity) (add_nonneg (div_nonneg (add_nonneg ka kb) (by norm_num))
      (div_nonneg (mul_nonneg hv0 (add_nonneg kr kq)) hsq.le))
  have hρA : ρ * (C * Tm) ≤ s / 4 := by
    rw [hC, hTm]
    exact hρA'
  have hρB : ρ * (C * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 -
      tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) /
          Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
   
            + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))) ≤ ϵ := by
    rw [hC, hTm]
    exact hρB'
  have hρC : 0 ≤ ρ * C := mul_nonneg hρ0.le hC0
  have mono : ∀ t : ℝ, 0 ≤ t → t ≤ Tm → ρ * C * t ≤ ρ * (C * Tm) := fun t _ ht => by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hC0) hρ0.le
  have mono' : ∀ t t' : ℝ, 0 ≤ t' → ρ * C * (t - t') ≤ ρ * C * t := fun t t' ht' =>
    mul_le_mul_of_nonneg_left (by linarith only [ht']) hρC
  have hk1 : ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet)))
      / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) ≤ ϵ := by
    have := mul_nonneg hρC hK2
    have e : ρ * (C * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 -
        tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
        + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))))
        = ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
            R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
          + ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
              R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by ring
    linarith only [this, e, hρB]
  have hk2 : ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet)))
      / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) ≤ ϵ := by
    have := mul_nonneg hρC hK1
    have e : ρ * (C * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 -
        tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
        + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))))
        = ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
            R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
          + ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
              R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by ring
    linarith only [this, e, hρB]
  rintro N e θ ψ χ ξ ζ ⟨ηe, xe, hηe, hxe, hθ1, hθ2⟩ ⟨ηr, xr, hηr, hxr, hψ1, hψ2⟩
    ⟨ημ, xμ, hημ, hxμ, hχ1, hχ2⟩ ⟨ηρ, xρ, hηρ, hxρ, hξ1, hξ2⟩ ⟨ηm, xm, hηm, hxm, hζ1, hζ2⟩
  have aθ := scaledTrainF_near hθ2 hγ1 hxe.le
  have aψ := scaledTrainF_near hψ2 hγ2 hxr.le
  have aχ := scaledTrainF_near hχ2 hγ3 hxμ.le
  have aξ := scaledTrainF_near hξ2 hγ4 hxρ.le
  have aζ := scaledTrainF_near hζ2 hγ5 hxm.le
  have hF := fibreH_isHermitian hH hG₁ hG₂ hG₃ hG₄ hG₅
    ((scaledTrainF_periodic g₁).lift θ.2) ((scaledTrainF_periodic g₂).lift ψ.2)
    ((scaledTrainF_periodic g₃).lift χ.2) ((scaledTrainF_periodic g₄).lift ξ.2)
    ((scaledTrainF_periodic g₅).lift ζ.2)
  have He' := IsGatedHistory.of_fibre (η₀ := ρ) (lam := ρ * C) hH hF He hce
      ((fibre_rate_le (T := Tm) aθ.1 aψ.1 aχ.1 aξ.1 aζ.1 hS1 hS2 hS3 hS4 hS5 hS1 aθ.2.1 aθ.2.2
        hρ0.le htce0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])).trans
        (le_of_eq (by rw [hC]))) hηe.le
      (by
        have := mono _ htce0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        linarith only [sp, this, hρs, hρA, q1])
      (by
        have := mono _ htce0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        have h' := mono' tce tbe htbe0
        linarith only [sp, this, h', hρA, q9])
  have Hr' := IsAwayHistory.of_fibre (ρ₀ := ρ) (lam := ρ * C) hH hF Hr hcr
      ((fibre_rate_le (T := Tm) aθ.1 aψ.1 aχ.1 aξ.1 aζ.1 hS1 hS2 hS3 hS4 hS5 hS2 aψ.2.1 aψ.2.2
        hρ0.le ht50 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])).trans
        (le_of_eq (by rw [hC]))) hηr.le
      (by
        have := mono _ ht50 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        linarith only [sp, this, hρs, hρA, q2])
      (by
        have := mono _ ht50 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        linarith only [sp, this, hρs, hρA, q3])
      (Or.inl (by
        have := mono _ ht50 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        constructor <;> linarith only [sp, this, hρs, hρA, q4, q5]))
      (by
        have := mono _ ht50 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        have h' := mono' t5 t4 ht40
        linarith only [sp, this, h', hρA, q10])
  have Hμ' := IsGatedHistory.of_fibre (η₀ := ρ) (lam := ρ * C) hH hF Hμ hcμ
      ((fibre_rate_le (T := Tm) aθ.1 aψ.1 aχ.1 aξ.1 aζ.1 hS1 hS2 hS3 hS4 hS5 hS3 aχ.2.1 aχ.2.2
        hρ0.le htcμ0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])).trans
        (le_of_eq (by rw [hC]))) hημ.le
      (by
        have := mono _ htcμ0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        linarith only [sp, this, hρs, hρA, q6])
      (by
        have := mono _ htcμ0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        have h' := mono' tcμ tbμ htbμ0
        linarith only [sp, this, h', hρA, q11])
  have Hρ' := IsGatedHistory.of_fibre (η₀ := ρ) (lam := ρ * C) hH hF Hρ hcρ
      ((fibre_rate_le (T := Tm) aθ.1 aψ.1 aχ.1 aξ.1 aζ.1 hS1 hS2 hS3 hS4 hS5 hS4 aξ.2.1 aξ.2.2
        hρ0.le htcρ0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])).trans
        (le_of_eq (by rw [hC]))) hηρ.le
      (by
        have := mono _ htcρ0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        linarith only [sp, this, hρs, hρA, q7])
      (by
        have := mono _ htcρ0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        have h' := mono' tcρ tbρ htbρ0
        linarith only [sp, this, h', hρA, q12])
  have Hm' := IsGatedHistory.of_fibre (η₀ := ρ) (lam := ρ * C) hH hF Hm hcm
      ((fibre_rate_le (T := Tm) aθ.1 aψ.1 aχ.1 aξ.1 aζ.1 hS1 hS2 hS3 hS4 hS5 hS5 aζ.2.1 aζ.2.2
        hρ0.le htcm0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])).trans
        (le_of_eq (by rw [hC]))) hηm.le
      (by
        have := mono _ htcm0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        linarith only [sp, this, hρs, hρA, q8])
      (by
        have := mono _ htcm0 (by linarith only [hTm, hT1, hT2, hT3, hT4, hT5])
        have h' := mono' tcm tbm htbm0
        linarith only [sp, this, h', hρA, q13])
  intro se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    penta_radar_lorentz_fibre e hH hG₁ hG₂ hG₃ hG₄ hG₅ (scaledTrainF_periodic g₁)
      (scaledTrainF_periodic g₂) (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄)
      (scaledTrainF_periodic g₅) (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂)
      (contDiff_scaledTrainF g₃) (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
      P hF hθ1 hψ1 hχ1 hξ1 hζ1 hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB
      hτR hτMA He' Hr' Hμ' Hρ' Hm' se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6.trans ?_, c7.trans ?_, c8.trans ?_⟩
  · simp only [gatedErr_add, awayErr_add]
    have key : ∀ x₁ x₂ x₃ x₄ x₅ : ℝ,
        (((x₁ + 6 * Real.pi * (ρ * C) * (tbe - tE)) / R₀ + κ * tE + τE)
          + (((x₁ + 6 * Real.pi * (ρ * C) * (tbe - tE)) + (x₂ + 6 * Real.pi * (ρ * C) * ((tbe -
              tE) + (t4 - tRet))) + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + ((x₃ + 6 * Real.pi * (ρ * C) * (tbμ - tMB)) / R₀ + κ * tMB + τMB)
          + (((x₄ + 6 * Real.pi * (ρ * C) * (tbρ - tR)) / R₀ + τR)
            + ((x₅ + 6 * Real.pi * (ρ * C) * (tbm - tMA)) / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
        = ((x₁ / R₀ + κ * tE + τE)
          + ((x₁ + x₂ + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + (x₃ / R₀ + κ * tMB + τMB)
          + ((x₄ / R₀ + τR)
            + (x₅ / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
          + ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
              R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by
      intro x₁ x₂ x₃ x₄ x₅
      ring
    rw [key]
    linarith only [hk1]
  · simp only [gatedErr_add, awayErr_add]
    have key : ∀ x₁ x₂ x₄ x₅ : ℝ,
        (((x₁ + 6 * Real.pi * (ρ * C) * (tbe - tE)) / R₀ + κ * tE + τE)
          + (((x₁ + 6 * Real.pi * (ρ * C) * (tbe - tE)) + (x₂ + 6 * Real.pi * (ρ * C) * ((tbe -
              tE) + (t4 - tRet))) + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + v * (((x₄ + 6 * Real.pi * (ρ * C) * (tbρ - tR)) / R₀ + τR)
            + ((x₅ + 6 * Real.pi * (ρ * C) * (tbm - tMA)) / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
        = ((x₁ / R₀ + κ * tE + τE)
          + ((x₁ + x₂ + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + v * ((x₄ / R₀ + τR)
            + (x₅ / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
          + ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
              R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by
      intro x₁ x₂ x₄ x₅
      ring
    rw [key]
    linarith only [hk2]
  · simp only [gatedErr_add]
    have hs1 : Real.sqrt (1 - v ^ 2) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg v] : 1 - v ^ 2 ≤ 1)
      rwa [Real.sqrt_one] at h
    have y1 : (tbρ - tR) / R₀ + (tbm - tMA) / R₀
        ≤ ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2) := by
      rw [le_div_iff₀ hsq]
      nlinarith only [add_nonneg kr kq, hs1]
    have y2 : (tbρ - tR) / R₀ + (tbm - tMA) / R₀
        ≤ ((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
          + (tbμ - tMB) / R₀
          + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2) := by
      linarith only [y1, div_nonneg (add_nonneg ka kb) (by norm_num : (0 : ℝ) ≤ 2), km]
    have y3 : ρ * C * (6 * Real.pi * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀))
        ≤ ρ * C * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
            R₀) / 2
          + (tbμ - tMB) / R₀
          + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left y2 (by positivity)) hρC
    have key : ∀ x y : ℝ,
        (x + 6 * Real.pi * (ρ * C) * (tbρ - tR)
            + (y + 6 * Real.pi * (ρ * C) * (tbm - tMA))) / R₀
          = (x + y) / R₀
            + ρ * C * (6 * Real.pi * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀)) := by
      intro x y
      ring
    rw [key]
    linarith only [y3, hk1]

end PentaNear

section TriOpen

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] [Fintype S] [DecidableEq S] [Nonempty ι] [Nonempty κa]
  [Nonempty κb] {M₀ : Matrix ι ι ℂ} {A₀ : Matrix κa κa ℂ}
  {B₀ : Matrix κb κb ℂ} {σ : ι → S} {α : κa → S} {β : κb → S}
  {r₁ r₂ r₃ r₄ r₅ : S → S → Prop} [DecidableRel r₁] [DecidableRel r₂] [DecidableRel r₃]
  [DecidableRel r₄] [DecidableRel r₅] {Ya : Matrix κa κa ℂ} {Yb : Matrix κb κb ℂ}

/-- ★★★ **M6 from the top from every pointer angle within an explicit radius, for three
carriers and five gates.** As `tri_radar_lorentz_open`, with the radius a hypothesis: let the
five gates have norm at most `S`, the five strengths size at most `γ`, the five reading
windows end by `T`, and `s > 0` be a slack below every margin of the five histories. Then
every `ρ > 0` with `ρ ≤ s/4`, `ρ C T ≤ s/4` and `ρ C (K₁ + K₂) ≤ ϵ`,
`C = 20 γ² S² T + 14 γ S`, `K₁`, `K₂` the coefficients of the two error components, is a
radius: from every five pointer angles within `ρ` of `(1/12, 0)` the five pointers have
counts and the counts satisfy the Lorentz statement with the errors of #402 enlarged by
`ϵ`. -/
theorem tri_radar_lorentz_near (hM : M₀.IsHermitian) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hYa : Ya.IsHermitian) (hYas : ∀ i j, α i ≠ α j → Ya i j = 0)
    (hYb : Yb.IsHermitian) (hYbs : ∀ i j, β i ≠ β j → Yb i j = 0) (g₁ g₂ g₃ g₄ g₅ : ℝ)
    (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    {ce cr cμ cρ cm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb) RB δe ve tE tbe tce)
    (Hr : IsAwayHistory (coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb) RB c vr η₀ η tE tbe
      tRet t4 t5)
    (Hμ : IsGatedHistory (coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb) RB δμ vμ tMB tbμ
      tcμ)
    (Hρ : IsGatedHistory (coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa) R₀ δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory
      (coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa) R₀ δm vm tMA tbm
      tcm)
    (hce : ∀ s t, tbe ≤ s → s ≤ t → t ≤ tce →
      |coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb t
        - coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb s| ≤ ce)
    (hcr : ∀ s t, t4 ≤ s → s ≤ t → t ≤ t5 →
      |coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb t
        - coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb s| ≤ cr)
    (hcμ : ∀ s t, tbμ ≤ s → s ≤ t → t ≤ tcμ →
      |coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb t
        - coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb s| ≤ cμ)
    (hcρ : ∀ s t, tbρ ≤ s → s ≤ t → t ≤ tcρ →
      |coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa t
        - coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa s| ≤ cρ)
    (hcm : ∀ s t, tbm ≤ s → s ≤ t → t ≤ tcm →
      |coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa t
        - coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa s| ≤ cm)
    {ϵ S γ T s ρ : ℝ}
    (hS1 : ‖gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ S)
    (hS2 : ‖gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ S)
    (hS3 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb‖ ≤ S)
    (hS4 : ‖gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))‖ ≤ S)
    (hS5 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya‖ ≤ S)
    (hγ1 : |g₁| ≤ γ) (hγ2 : |g₂| ≤ γ) (hγ3 : |g₃| ≤ γ) (hγ4 : |g₄| ≤ γ) (hγ5 : |g₅| ≤ γ)
    (hT1 : tce ≤ T) (hT2 : t5 ≤ T) (hT3 : tcμ ≤ T) (hT4 : tcρ ≤ T) (hT5 : tcm ≤ T)
    (sp : 0 < s) (q1 : s ≤ 1 / 12 - δe) (q2 : s ≤ 1 / 12 - η₀) (q3 : s ≤ 1 / 12 - η)
    (q4 : s ≤ 1 / 12 - c - (-1 / 6 + η)) (q5 : s ≤ 1 / 6 - η - (1 / 12 - c))
    (q6 : s ≤ 1 / 12 - δμ) (q7 : s ≤ 1 / 12 - δρ) (q8 : s ≤ 1 / 12 - δm)
    (q9 : s ≤ 1 / 6 - ce) (q10 : s ≤ 1 / 6 - cr) (q11 : s ≤ 1 / 6 - cμ)
    (q12 : s ≤ 1 / 6 - cρ) (q13 : s ≤ 1 / 6 - cm) (hρ0 : 0 < ρ) (hρs : ρ ≤ s / 4)
    (hρA' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * T) ≤ s / 4)
    (hρB' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe
        - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))) ≤ ϵ) :
    ∀ (N : ℕ) (e : ι × (κa × κb) ≃ Fin (N + 1)) (θ ψ χ ξ ζ : KTorus),
      NearStart ρ θ → NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
      ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr vμ tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ + ϵ := by
  have hAB := compositeH_isHermitian hA hB
  have hH := compositeH_isHermitian hM hAB
  have hG₁ := gateOp_snd_isHermitian (κa := κa) σ β r₁ hYb hYbs
  have hG₂ := gateOp_snd_isHermitian (κa := κa) σ β r₂ hYb hYbs
  have hG₃ : ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb).IsHermitian :=
    kronecker_isHermitian Matrix.isHermitian_one (gateOp_isHermitian α β r₃ hYb hYbs)
  have hG₄ := gateOp_fst_isHermitian (κb := κb) σ α r₄ hYa hYas
  have hG₅ : ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya).IsHermitian :=
    kronecker_isHermitian Matrix.isHermitian_one (gateOpL_isHermitian α β r₅ hYa hYas)
  rw [← freeShift_tri_gate_snd σ β r₁ hM hA hB Yb (-g₁) p qa qb] at He hce
  rw [← freeShift_tri_gate_snd σ β r₂ hM hA hB Yb (-g₂) p qa qb] at Hr hcr
  rw [← freeShift_tri_pair α β r₃ hM hA hB Yb (-g₃) p qa qb] at Hμ hcμ
  rw [← freeShift_tri_gate_fst σ α r₄ hM hA hB Ya (-g₄) p qa qb] at Hρ hcρ
  rw [← freeShift_tri_pairL α β r₅ hM hA hB Ya (-g₅) p qa qb] at Hm hcm
  exact penta_radar_lorentz_near hH hG₁ hG₂ hG₃ hG₄ hG₅ g₁ g₂ g₃ g₄ g₅
    (prodRay p (prodRay qa qb)) hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB hτR hτMA He Hr Hμ Hρ Hm
    hce hcr hcμ hcρ hcm hS1 hS2 hS3 hS4 hS5 hγ1 hγ2 hγ3 hγ4 hγ5 hT1 hT2 hT3 hT4 hT5 sp q1 q2
    q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 hρ0 hρs hρA' hρB'

/-- ★★★ **M6 from the top on an open set of pointer angles, for three carriers and five
gates.** The run `triRun` with the profiles `g_i · trainF`. Suppose the five two-carrier gate
displacements with the strengths `−g_i` have the histories of `radar_lorentz_of_histories`
(#402), each moves by less than `1/6` while its gate is closed (`c_e, …, c_m < 1/6`), and
the away history's band holds strictly. Then for every `ϵ > 0` there is a radius `ρ > 0`
such that, for every labelling of the carrier's basis, from every five pointer angles
within `ρ` of `(1/12, 0)` the five pointers have
counts at every choice of flow times in the five reading windows, and the counts satisfy the
Lorentz statement with the errors of #402 enlarged by `ϵ`. -/
theorem tri_radar_lorentz_open (hM : M₀.IsHermitian) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hYa : Ya.IsHermitian) (hYas : ∀ i j, α i ≠ α j → Ya i j = 0)
    (hYb : Yb.IsHermitian) (hYbs : ∀ i j, β i ≠ β j → Yb i j = 0) (g₁ g₂ g₃ g₄ g₅ : ℝ)
    (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    {ce cr cμ cρ cm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb) RB δe ve tE tbe tce)
    (Hr : IsAwayHistory (coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb) RB c vr η₀ η tE tbe
      tRet t4 t5)
    (Hμ : IsGatedHistory (coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb) RB δμ vμ tMB tbμ
      tcμ)
    (Hρ : IsGatedHistory (coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa) R₀ δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory
      (coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa) R₀ δm vm tMA tbm
      tcm)
    (hce : ∀ s t, tbe ≤ s → s ≤ t → t ≤ tce →
      |coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb t
        - coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb s| ≤ ce)
    (hcr : ∀ s t, t4 ≤ s → s ≤ t → t ≤ t5 →
      |coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb t
        - coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb s| ≤ cr)
    (hcμ : ∀ s t, tbμ ≤ s → s ≤ t → t ≤ tcμ →
      |coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb t
        - coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb s| ≤ cμ)
    (hcρ : ∀ s t, tbρ ≤ s → s ≤ t → t ≤ tcρ →
      |coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa t
        - coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa s| ≤ cρ)
    (hcm : ∀ s t, tbm ≤ s → s ≤ t → t ≤ tcm →
      |coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa t
        - coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa s| ≤ cm)
    (hse : ce < 1 / 6) (hsr : cr < 1 / 6) (hsμ : cμ < 1 / 6) (hsρ : cρ < 1 / 6)
    (hsm : cm < 1 / 6)
    (hband : -1 / 6 + η < 1 / 12 - c ∧ 1 / 12 - c < 1 / 6 - η) {ϵ : ℝ} (hϵ : 0 < ϵ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (e : ι × (κa × κb) ≃ Fin (N + 1)) (θ ψ χ ξ ζ : KTorus),
      NearStart ρ θ → NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
      ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb (scaledTrainF_periodic g₁)
                (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅)
              p qa qb θ ψ χ ξ ζ) sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr vμ tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ + ϵ := by
  -- the sizes
  have n1 := norm_nonneg (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb))
  have n2 := norm_nonneg (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb))
  have n3 := norm_nonneg ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb)
  have n4 := norm_nonneg (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ)))
  have n5 := norm_nonneg ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya)
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ : ∃ S : ℝ,
      ‖gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ S
      ∧ ‖gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ S
      ∧ ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb‖ ≤ S
      ∧ ‖gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))‖ ≤ S
      ∧ ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya‖ ≤ S :=
    ⟨‖gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖
        + ‖gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖
        + ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb‖
        + ‖gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))‖
        + ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya‖, by linarith only [n1, n2, n3, n4, n5],
      by linarith only [n1, n2, n3, n4, n5], by linarith only [n1, n2, n3, n4, n5],
      by linarith only [n1, n2, n3, n4, n5], by linarith only [n1, n2, n3, n4, n5]⟩
  have m1 := abs_nonneg g₁
  have m2 := abs_nonneg g₂
  have m3 := abs_nonneg g₃
  have m4 := abs_nonneg g₄
  have m5 := abs_nonneg g₅
  obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, hγ5⟩ : ∃ γ : ℝ, |g₁| ≤ γ ∧ |g₂| ≤ γ ∧ |g₃| ≤ γ ∧ |g₄| ≤ γ
      ∧ |g₅| ≤ γ :=
    ⟨|g₁| + |g₂| + |g₃| + |g₄| + |g₅|, by linarith only [m1, m2, m3, m4, m5],
      by linarith only [m1, m2, m3, m4, m5], by linarith only [m1, m2, m3, m4, m5],
      by linarith only [m1, m2, m3, m4, m5], by linarith only [m1, m2, m3, m4, m5]⟩
  have hS0 : 0 ≤ S := n1.trans hS1
  have hγ0 : 0 ≤ γ := m1.trans hγ1
  -- the times
  have htbe0 : 0 ≤ tbe := He.ta_nonneg.trans He.ta_le
  have htce0 : 0 ≤ tce := htbe0.trans He.tb_le
  have ht40 : 0 ≤ t4 := (htbe0.trans Hr.tb_le).trans Hr.t3_le
  have ht50 : 0 ≤ t5 := ht40.trans Hr.t4_le
  have htbμ0 : 0 ≤ tbμ := Hμ.ta_nonneg.trans Hμ.ta_le
  have htcμ0 : 0 ≤ tcμ := htbμ0.trans Hμ.tb_le
  have htbρ0 : 0 ≤ tbρ := Hρ.ta_nonneg.trans Hρ.ta_le
  have htcρ0 : 0 ≤ tcρ := htbρ0.trans Hρ.tb_le
  have htbm0 : 0 ≤ tbm := Hm.ta_nonneg.trans Hm.ta_le
  have htcm0 : 0 ≤ tcm := htbm0.trans Hm.tb_le
  -- the error's coefficients
  have hsq : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith only [hv0, hv])
  have ka : 0 ≤ (tbe - tE) / R₀ := div_nonneg (sub_nonneg.2 He.ta_le) hR₀.le
  have kb : 0 ≤ ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀ :=
    div_nonneg (by linarith only [He.ta_le, Hr.t3_le]) hR₀.le
  have km : 0 ≤ (tbμ - tMB) / R₀ := div_nonneg (sub_nonneg.2 Hμ.ta_le) hR₀.le
  have kr : 0 ≤ (tbρ - tR) / R₀ := div_nonneg (sub_nonneg.2 Hρ.ta_le) hR₀.le
  have kq : 0 ≤ (tbm - tMA) / R₀ := div_nonneg (sub_nonneg.2 Hm.ta_le) hR₀.le
  have hK1 : 0 ≤ (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
    mul_nonneg (by positivity) (add_nonneg (add_nonneg (div_nonneg (add_nonneg ka kb)
      (by norm_num)) km) (div_nonneg (add_nonneg kr kq) hsq.le))
  have hK2 : 0 ≤ (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
    mul_nonneg (by positivity) (add_nonneg (div_nonneg (add_nonneg ka kb) (by norm_num))
      (div_nonneg (mul_nonneg hv0 (add_nonneg kr kq)) hsq.le))
  -- the slack
  obtain ⟨s1, s1p, s1a, s1b⟩ := exists_pos_le (sub_pos.2 He.err_lt) (sub_pos.2 Hr.start_lt)
  obtain ⟨s2, s2p, s2a, s2b⟩ := exists_pos_le s1p (sub_pos.2 Hr.err_lt)
  obtain ⟨s3, s3p, s3a, s3b⟩ := exists_pos_le s2p (sub_pos.2 hband.1)
  obtain ⟨s4, s4p, s4a, s4b⟩ := exists_pos_le s3p (sub_pos.2 hband.2)
  obtain ⟨s5, s5p, s5a, s5b⟩ := exists_pos_le s4p (sub_pos.2 Hμ.err_lt)
  obtain ⟨s6, s6p, s6a, s6b⟩ := exists_pos_le s5p (sub_pos.2 Hρ.err_lt)
  obtain ⟨s7, s7p, s7a, s7b⟩ := exists_pos_le s6p (sub_pos.2 Hm.err_lt)
  obtain ⟨s8, s8p, s8a, s8b⟩ := exists_pos_le s7p (sub_pos.2 hse)
  obtain ⟨s9, s9p, s9a, s9b⟩ := exists_pos_le s8p (sub_pos.2 hsr)
  obtain ⟨s10, s10p, s10a, s10b⟩ := exists_pos_le s9p (sub_pos.2 hsμ)
  obtain ⟨s11, s11p, s11a, s11b⟩ := exists_pos_le s10p (sub_pos.2 hsρ)
  obtain ⟨s, sp, s12a, s12b⟩ := exists_pos_le s11p (sub_pos.2 hsm)
  have q1 : s ≤ 1 / 12 - δe := by
    linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6a, s5a, s4a, s3a, s2a, s1a]
  have q2 : s ≤ 1 / 12 - η₀ := by
    linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6a, s5a, s4a, s3a, s2a, s1b]
  have q3 : s ≤ 1 / 12 - η := by
    linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6a, s5a, s4a, s3a, s2b]
  have q4 : s ≤ 1 / 12 - c - (-1 / 6 + η) := by
    linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6a, s5a, s4a, s3b]
  have q5 : s ≤ 1 / 6 - η - (1 / 12 - c) := by
    linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6a, s5a, s4b]
  have q6 : s ≤ 1 / 12 - δμ := by
    linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6a, s5b]
  have q7 : s ≤ 1 / 12 - δρ := by linarith only [s12a, s11a, s10a, s9a, s8a, s7a, s6b]
  have q8 : s ≤ 1 / 12 - δm := by linarith only [s12a, s11a, s10a, s9a, s8a, s7b]
  have q9 : s ≤ 1 / 6 - ce := by linarith only [s12a, s11a, s10a, s9a, s8b]
  have q10 : s ≤ 1 / 6 - cr := by linarith only [s12a, s11a, s10a, s9b]
  have q11 : s ≤ 1 / 6 - cμ := by linarith only [s12a, s11a, s10b]
  have q12 : s ≤ 1 / 6 - cρ := by linarith only [s12a, s11b]
  have q13 : s ≤ 1 / 6 - cm := s12b
  obtain ⟨ρ, hρ0, -, hρs, hρA, hρB⟩ := exists_radius (s := s / 4) (ϵ := ϵ)
    (A := (20 * γ ^ 2 * S ^ 2 * (tce + t5 + tcμ + tcρ + tcm) + 14 * γ * S) * (tce + t5 + tcμ + tcρ
        + tcm))
    (B := (20 * γ ^ 2 * S ^ 2 * (tce + t5 + tcμ + tcρ + tcm) + 14 * γ * S) * ((6 * Real.pi *
        (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))))
    (by linarith only [sp]) hϵ (by positivity) (mul_nonneg (by positivity) (add_nonneg hK1 hK2))
  exact ⟨ρ, hρ0, tri_radar_lorentz_near hM hA hB hYa hYas hYb hYbs g₁ g₂ g₃ g₄ g₅ p qa qb
    hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB hτR hτMA He Hr Hμ Hρ Hm hce hcr hcμ hcρ hcm
    hS1 hS2 hS3 hS4 hS5 hγ1 hγ2 hγ3 hγ4 hγ5
    (by linarith only [htce0, ht50, htcμ0, htcρ0, htcm0])
    (by linarith only [htce0, ht50, htcμ0, htcρ0, htcm0])
    (by linarith only [htce0, ht50, htcμ0, htcρ0, htcm0])
    (by linarith only [htce0, ht50, htcμ0, htcρ0, htcm0])
    (by linarith only [htce0, ht50, htcμ0, htcρ0, htcm0])
    sp q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 hρ0 hρs hρA hρB⟩

end TriOpen

end CSD.RecordLayer

end
