/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.EraserDynamics

/-!
# Empirical/CSD/EraserSequential: mark, then erase — no revival (the row's residue)

**Category:** empirical CSD twin, dynamical tier — the two-stroke sequential composition,
closing the dynamical no-signalling + eraser row's recorded residue.

`EraserDynamics` proved the two single strokes: erasing the **coherent** Bell state restores
the fringes (`erased_rate`), and marking kills them (`marked_no_fringe`). This module
composes the strokes in the physically decisive order: **mark first — a record exists — then
erase.** The mark post-state is the which-path product `|j⟩⊗|j⟩` (`localProjB_bellE`); the
`±` erase stroke on *that* state gives marker outcomes with the same `1/2` weights
(`sequential_erase_weight`), but the system profile stays on the ray `[|j⟩]`
(`seqProfile_eq` — the erase stroke only rescales it), so the screen statistics remain flat
at every phase:

★ `sequential_no_revival` — **once a record exists, no later marker measurement revives the
fringe**, whatever its outcome. Interference is recoverable only *before* the record
(`erased_rate`), never after. This is the statistical face of what the corpus proves
structurally elsewhere: records are relocation with storage, not erasable bookkeeping —
"un-measuring" is not an operation the dynamics has.

⚠️ **Honest scope.** The strokes compose as state updates (the second stroke acts on the
first stroke's post-state); the two-time protocol plumbing carries over verbatim from the
single-stroke machinery and is not restated. The row's other recorded residue — the
measure-level "ensemble integral" form of no-signalling — is hereby **closed as
definitional** (2026-08-03): for finitely many outcomes the post ray-ensemble *is* the
discrete mixture `Σⱼ pⱼ·δ_{[Pⱼv]}`, and its barycenter statement *is*
`reduceA_localLudersOn_mixture`; recasting it as a Bochner integral would add a
`reduceA`-measurability lemma and no content. Revisit only if a continuum-outcome layer
ever appears.

## References

`specs/BACKLOG.md` (the row); `Empirical/CSD/EraserDynamics.lean` (the two single strokes);
`SigmaLayer/LocalLuders.lean` + `LocalLudersBasis.lean` (the machinery);
`SigmaLayer/RecordPersistence.lean` (the structural face of irreversibility).
-/

@[expose] public section

open MeasureTheory CSD.RecordLayer
open CSD.Empirical.QM.QuantumEraser
open CSD.Empirical.CSDBridge.QuantumEraserVolume
open CSD.Empirical.CSDBridge.EraserDynamics
open scoped LinearAlgebra.Projectivization

namespace CSD.Empirical.CSDBridge.EraserSequential

/-- The mark-stroke post-state for marker outcome `j`: the which-path product state. -/
noncomputable def markPost (j : Fin 2) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  EuclideanSpace.single ((j, j) : Fin 2 × Fin 2) (1 : ℂ)

/-- The `B`-slices of the mark post-state: the marker ray over the recorded path, zero
elsewhere. -/
lemma sliceB_markPost (j a : Fin 2) :
    sliceB (markPost j) a
      = if a = j then EuclideanSpace.single j (1 : ℂ) else 0 := by
  apply PiLp.ext
  intro k
  rw [sliceB_apply, markPost]
  rw [show (EuclideanSpace.single ((j, j) : Fin 2 × Fin 2) (1 : ℂ)) (a, k)
      = if (a, k) = (j, j) then 1 else 0 from PiLp.single_apply 2 ℂ (j, j) 1 (a, k)]
  rcases eq_or_ne a j with rfl | ha
  · rw [if_pos rfl]
    rw [show (EuclideanSpace.single a (1 : ℂ)) k = if k = a then 1 else 0 from
      PiLp.single_apply 2 ℂ a 1 k]
    exact if_congr (by rw [Prod.ext_iff]; simp) rfl rfl
  · rw [if_neg ha, if_neg (by rw [Prod.ext_iff]; rintro ⟨h1, _⟩; exact ha h1)]
    rfl

/-- The system profile of the second (erase) stroke, acting on the mark post-state. -/
noncomputable def seqProfile (j m : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun a => inner ℂ (pmVec m) (sliceB (markPost j) a)

/-- **The erase stroke cannot move the recorded path**: the second-stroke system profile is
a scalar multiple of the recorded ray `|j⟩` — erasing after the record only rescales. -/
theorem seqProfile_eq (j m : Fin 2) :
    seqProfile j m
      = (starRingEnd ℂ) (pmVec m j) • EuclideanSpace.single j (1 : ℂ) := by
  apply PiLp.ext
  intro a
  show (inner ℂ (pmVec m) (sliceB (markPost j) a) : ℂ)
    = ((starRingEnd ℂ) (pmVec m j) • EuclideanSpace.single j (1 : ℂ)) a
  rw [sliceB_markPost]
  show (inner ℂ (pmVec m) (if a = j then EuclideanSpace.single j (1 : ℂ) else 0) : ℂ)
    = (starRingEnd ℂ) (pmVec m j) * (EuclideanSpace.single j (1 : ℂ)) a
  rw [show (EuclideanSpace.single j (1 : ℂ)) a = if a = j then 1 else 0 from
    PiLp.single_apply 2 ℂ j 1 a]
  rcases eq_or_ne a j with rfl | ha
  · rw [if_pos rfl, if_pos rfl, mul_one]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    fin_cases a <;> simp [RCLike.inner_apply]
  · rw [if_neg ha, if_neg ha, mul_zero, inner_zero_right]

lemma normSq_pmVec_component (m j : Fin 2) : ‖pmVec m j‖ ^ 2 = 1 / 2 := by
  fin_cases j
  · show ‖pmVec m 0‖ ^ 2 = 1 / 2
    rw [pmVec_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹), sq, invSqrtTwo_mul_self]
  · show ‖pmVec m 1‖ ^ 2 = 1 / 2
    rw [pmVec_one, norm_mul, mul_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹)]
    have hs : |pmSign m| = 1 := by
      rcases pmSign_cases m with h | h <;> rw [h] <;> norm_num
    rw [hs, one_pow, one_mul, sq, invSqrtTwo_mul_self]

/-- **The second-stroke marker weights are still `1/2`** — the erase stroke's outcomes stay
unbiased on the marked state. -/
theorem sequential_erase_weight (j m : Fin 2) :
    ‖seqProfile j m‖ ^ 2 / ‖markPost j‖ ^ 2 = 1 / 2 := by
  have hE : ∀ w : EuclideanSpace ℂ (Fin 2), ‖w‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hprof : ‖seqProfile j m‖ ^ 2 = 1 / 2 := by
    rw [seqProfile_eq, norm_smul, mul_pow, RCLike.norm_conj, normSq_pmVec_component,
      PiLp.norm_single, norm_one, one_pow, mul_one]
  have hmark : ‖markPost j‖ ^ 2 = 1 := by
    rw [markPost, PiLp.norm_single, norm_one, one_pow]
  rw [hprof, hmark, div_one]

/-- ★ **No revival: once the mark record exists, erasing cannot restore the fringe.** The
screen rate after mark-`j`-then-erase-`m` is `1/2` at every phase, port, and marker
outcome — conditioning on the second stroke changes nothing, in exact contrast to the
pre-record erase stroke (`erased_rate`), whose conditioned fringes have full visibility.
Records are statistically irreversible. -/
theorem sequential_no_revival (φ : ℝ) {a : ℝ} (ha : a = 1 ∨ a = -1) (j m : Fin 2) :
    ‖(inner ℂ (sysE φ a) (seqProfile j m) : ℂ)‖ ^ 2
        / (‖sysE φ a‖ ^ 2 * ‖seqProfile j m‖ ^ 2)
      = 1 / 2 := by
  have hc : ‖(starRingEnd ℂ) (pmVec m j)‖ ^ 2 = 1 / 2 := by
    rw [RCLike.norm_conj, normSq_pmVec_component]
  have hc0 : ‖(starRingEnd ℂ) (pmVec m j)‖ ^ 2 ≠ 0 := by
    rw [hc]; norm_num
  rw [seqProfile_eq, inner_smul_right, norm_mul, mul_pow, norm_smul, mul_pow,
    PiLp.norm_single, norm_one, one_pow, mul_one]
  rw [show ‖sysE φ a‖ ^ 2 * ‖(starRingEnd ℂ) (pmVec m j)‖ ^ 2
      = ‖(starRingEnd ℂ) (pmVec m j)‖ ^ 2 * ‖sysE φ a‖ ^ 2 from mul_comm _ _]
  rw [mul_div_mul_left _ _ hc0]
  exact marked_no_fringe φ ha j

end CSD.Empirical.CSDBridge.EraserSequential
