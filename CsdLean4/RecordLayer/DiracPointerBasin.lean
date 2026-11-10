/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CellLawForced
public import CsdLean4.RecordLayer.DiracPointerClick

/-!
# The basin statistic of a rate field along the coupled flow of `Σ_*`: the conditional error bound

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #356 — milestone **M3, part C** of the
author's programme "From `Σ` to physical spacetime". Part B (`RecordLayer/DiracPointerClick.lean`,
#355) answered gate A with an obstruction: the click probability the coupled flow fixes is not the
quantum one, and the quantum weights enter the corpus only through the rate field of UA-6
(Posit 1). Gate A then asks that the result be kept as a *conditional* reconstruction. This module
is that half. It is conditional on UA-6 throughout and derives no weight.

M3's target is a bound `|P_{Σ_*}(i | ψ, M) − ⟨ψ, P_i ψ⟩| ≤ ε_meas` with every term of `ε_meas`
explicit. Part A (`epistemicMeasure_diracPointerFlow_globalBasin`) wrote the probability of the
basin of a rate field at time `t` as the `θ₂`-average of the rate at the coupled carrier, whose
generator has the detector's term in it. What was owed is the size of that term's effect.

**The statistic.** `diracBasinProb` is the probability, under the preparation law
`epistemicMeasure`, that the arena point is at time `t` in the basin of the basis state `a`. For a
torus-generated rate field (`IsTorusGenerated`, UA-6) the rate is the moment coordinate
(`torusGenerated_eq_momentMap`), and the basin probability is the `θ₂`-average of `diracWeight`,
the weight of `a` at the carrier moved by the coupled propagator (`diracBasinProb_eq_lintegral`).

**The error.** On the fibre `θ₂` the coupled propagator differs from the free one by at most
`|t| |g f(θ₂)|` in norm, and a weight moves by at most twice that. So with `|f| ≤ F` the basin
probability is within `2 |t| |g| F` of the weight quantum mechanics assigns to `a` at time `t` with
no detector attached (`abs_diracBasinProb_sub_zero_coupling_le`), and within
`2 |t| (‖H_D‖ + |g| F)` of the weight of `a` in the carrier as prepared
(`abs_diracBasinProb_sub_init_le`). With the coupling off there is no error
(`diracBasinProb_zero_coupling`): the error term is the detector's.

## Three generic facts

* `norm_single_self_le` — a basis projector has operator norm at most `1`;
* `momentMap_idxArenaEquiv` — the moment coordinates are carried by an index change;
* `abs_toReal_lintegral_ofReal_sub_le` — an average of numbers within `ε` of `w` is within `ε` of
  `w`.

## The weight of a basis state along the carrier's orbit

* `diracWeight`, `diracWeight_eq_momentMap`, `diracWeight_nonneg`, `diracWeight_zero`,
  `diracWeight_zero_coupling_congr`;
* ★ `diracWeight_zero_coupling_mk` — the free weight is `|(e^{−itH_D} ψ)_a|² / ‖ψ‖²`;
* ★★ `abs_diracWeight_sub_zero_coupling_le` — **the detector's disturbance of a weight** is at most
  `2 |t| |g f(θ₂)|`;
* ★ `abs_diracWeight_sub_init_le` — the weight over a short time.

## The basin of a torus-generated rate field

* `diracBasinProb`, `rate_diracArenaEquiv_of_isTorusGenerated`;
* ★★ `diracBasinProb_eq_lintegral` — the basin probability is the `θ₂`-average of the weight
  (exact);
* ★ `diracBasinProb_zero_coupling` — with the coupling off it is the free weight (exact);
* ★★★ `abs_diracBasinProb_sub_zero_coupling_le` — **the conditional error bound**:
  `ε_meas ≤ 2 |t| |g| F` against the free weight at time `t`;
* ★★ `abs_diracBasinProb_sub_init_le` — against the prepared state:
  `ε_meas ≤ 2 |t| (‖H_D‖ + |g| F)`.

## The check: the profile `trainF` at the coupling of the click law

* ★★ `abs_diracBasinProb_trainF_sub_le` — at `g = 1/(4T)` and readout time `T` the disturbance is
  at most `1/12`.

## Honest scope

* **Conditional on UA-6.** Every statement about `diracBasinProb` has `IsTorusGenerated c` as a
  hypothesis. By `torusGenerated_eq_momentMap` that hypothesis puts the quantum weights into the
  rate field. The theorems do not derive them, and by §6 of the contract they do not pass a gate.
  What is proved is how the coupled Hamiltonian flow carries a statistic that already has the
  quantum form, and by how much the detector's term moves it. The hypothesis has an instance,
  `isTorusGenerated_momentContext`.
* **Not the pointer's record.** The basin event is a region of the fibre angle `θ₁` cut by the rate
  field at the carrier's ray at time `t`. The pointer's displacement does not enter it (part A),
  and it is not the click event of part B. No relation between the two events is proved. The
  detector appears here only through its back-reaction on the carrier.
* **Which terms of `ε_meas` are present.** Back-reaction on the carrier (`2 |t| |g| F`) and finite
  time (`2 |t| ‖H_D‖`, only in the comparison with the prepared state). A transition region and a
  retention time are not terms: the event is read at one time and is not a threshold on the
  pointer.
* **Upper bounds.** The two error bounds are not shown to be attained, and no lower bound on the
  disturbance is proved. They carry information only where the right-hand side is below `1`.
* **The comparison weight.** `diracWeight J μ 0 …` is the weight at the carrier moved by
  `e^{−itH_D}` (`diracWeight_zero_coupling_mk`); it does not depend on the fibre
  (`diracWeight_zero_coupling_congr`), and the fibre argument `φ₀` in the statements is a dummy.
* **A basis state, not a site.** The outcome is a basis index `(site, spin)` of the ring. The basin
  of a site is the union of two disjoint basins; a bound for it follows with twice the error, and
  the bound with the same error is not proved here.
* **The fibre law is uniform** (UA-2), one pointer, one trial. Several detectors, one outcome per
  trial, repeated trials, no-signalling and sequential update are not treated.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1), the
  preparation law (UA-2) and its reading as the probability of a region (UA-3), the coupling (UA-5)
  and the propagation law (UA-8) are the definitions the statements are about; the profile, the
  coupling strength and the time are apparatus input (UA-4); **UA-6 is a named hypothesis.**

References: `specs/BACKLOG.md` #356, #355, #354, #350, #349; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UO-8, UO-12; UD-48; UD-55 to UD-57); `specs/POSITS.md`
(Posit 1); `RecordLayer/DiracPointerBorn.lean`
(`epistemicMeasure_diracPointerFlow_globalBasin`); `RecordLayer/CellLawForced.lean`
(`IsTorusGenerated`, `torusGenerated_eq_momentMap`, `isTorusGenerated_momentContext`);
`RecordLayer/GlobalBasin.lean` (`globalBasin`, `ContextField`);
`RecordLayer/DiracPointerWrite.lean` (`abs_arenaObs_arenaKick_sub_le`,
`norm_diracCarrierU_sub_le`, `diracCarrierU_zero_coupling_val`);
`RecordLayer/DiracPointerThreshold.lean` (`norm_diracCarrierU_sub_one_le`,
`norm_diracPointerH_le`); `RecordLayer/DiracPointerClick.lean` (`abs_trainF_lift_le`,
`diracPointer_clickLaw`); `CV/ArenaIndexBridge.lean` (`arenaObs_reindex`);
`CV/DetunedExchange.lean` (`arenaObs_single_eq_momentMap`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology ENNReal

namespace CSD.RecordLayer

/-! ### Three generic facts -/

section Generic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A basis projector has operator norm at most `1`. -/
theorem norm_single_self_le (a : ι) : ‖Matrix.single a a (1 : ℂ)‖ ≤ 1 := by
  have h : Matrix.single a a (1 : ℂ) = Matrix.diagonal fun b => if b = a then 1 else 0 := by
    ext b b'
    simp only [Matrix.single_apply, Matrix.diagonal_apply]
    by_cases hb : b = b'
    · subst hb
      by_cases ha : a = b
      · subst ha
        simp
      · simp [ha, Ne.symm ha]
    · by_cases ha : a = b
      · subst ha
        simp [hb]
      · simp [ha, hb]
  rw [h]
  exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun b => by split_ifs <;> simp

/-- **The moment coordinates are carried by an index change.** -/
theorem momentMap_idxArenaEquiv (e : ι ≃ κ) (p : GenArena ι) (a : ι) :
    momentMap (idxArenaEquiv e p) (e a) = momentMap p a := by
  rw [← arenaObs_single_eq_momentMap (e a) (idxArenaEquiv e p), ← arenaObs_single_eq_momentMap a p,
    ← arenaObs_reindex e (Matrix.single a a (1 : ℂ)) p]
  congr 1
  ext b b'
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply]
  by_cases h1 : e a = b
  · subst h1
    by_cases h2 : e a = b'
    · subst h2
      simp
    · have h2' : ¬ a = e.symm b' := fun h => h2 (by rw [h, Equiv.apply_symm_apply])
      simp [h2, h2']
  · have h1' : ¬ a = e.symm b := fun h => h1 (by rw [h, Equiv.apply_symm_apply])
    simp [h1, h1']

/-- **An average of numbers near `w` is near `w`.** Under a probability measure, if every `r x` is
within `ε` of `w ≥ 0`, so is the integral of `ENNReal.ofReal (r x)`. No measurability is asked. -/
theorem abs_toReal_lintegral_ofReal_sub_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {r : α → ℝ} {w ε : ℝ} (hw : 0 ≤ w) (h : ∀ x, |r x - w| ≤ ε) :
    |(∫⁻ x, ENNReal.ofReal (r x) ∂ν).toReal - w| ≤ ε := by
  have hε : 0 ≤ ε := by
    obtain ⟨x⟩ : Nonempty α := ν.nonempty_of_neZero
    exact (abs_nonneg _).trans (h x)
  have hup : ∫⁻ x, ENNReal.ofReal (r x) ∂ν ≤ ENNReal.ofReal (w + ε) := by
    calc ∫⁻ x, ENNReal.ofReal (r x) ∂ν
        ≤ ∫⁻ _, ENNReal.ofReal (w + ε) ∂ν :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (h x)).2])
      _ = ENNReal.ofReal (w + ε) := by rw [lintegral_const, measure_univ, mul_one]
  have hlo : ENNReal.ofReal (w - ε) ≤ ∫⁻ x, ENNReal.ofReal (r x) ∂ν := by
    calc ENNReal.ofReal (w - ε)
        = ∫⁻ _, ENNReal.ofReal (w - ε) ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ x, ENNReal.ofReal (r x) ∂ν :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (h x)).1])
  have hfin : ∫⁻ x, ENNReal.ofReal (r x) ∂ν ≠ ⊤ := (hup.trans_lt ENNReal.ofReal_lt_top).ne
  have h1 := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hlo
  have h2 := ENNReal.toReal_le_of_le_ofReal (by linarith) hup
  rw [abs_le]
  constructor <;> linarith

end Generic

/-! ### The weight of a basis state along the carrier's orbit -/

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-- **The weight of the basis state `a` along the carrier's orbit** on the fibre `θ₂ = φ`: the
expectation of `|a⟩⟨a|` at the ray moved by the coupled propagator. At `g = 0` it is the free
chain's, the weight quantum mechanics assigns to `a` at time `t` with no detector attached. -/
noncomputable def diracWeight (φ : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) : ℝ :=
  arenaObs (Matrix.single a a (1 : ℂ)) (arenaKick (diracCarrierU J μ g j hf φ t) p)

/-- The weight is the moment coordinate of the moved ray. -/
theorem diracWeight_eq_momentMap (φ : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracWeight J μ g j hf φ a p t
      = momentMap (arenaKick (diracCarrierU J μ g j hf φ t) p) a := by
  rw [diracWeight, arenaObs_single_eq_momentMap]

/-- A weight is nonnegative. -/
theorem diracWeight_nonneg (φ : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) : 0 ≤ diracWeight J μ g j hf φ a p t := by
  rw [diracWeight_eq_momentMap]
  exact momentMap_nonneg _ _

/-- At time `0` the weight is the carrier's own. -/
theorem diracWeight_zero (φ : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracWeight J μ g j hf φ a p 0 = momentMap p a := by
  rw [diracWeight, diracCarrierU_zero, arenaObs_kick_conj, ← arenaObs_single_eq_momentMap]
  simp

/-- With the coupling off the weight does not depend on the fibre. -/
theorem diracWeight_zero_coupling_congr (φ φ' : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    diracWeight J μ 0 j hf φ a p t = diracWeight J μ 0 j hf φ' a p t := by
  have h : diracCarrierU J μ 0 j hf φ t = diracCarrierU J μ 0 j hf φ' t := by
    apply Subtype.ext
    rw [diracCarrierU_zero_coupling_val, diracCarrierU_zero_coupling_val]
  rw [diracWeight, diracWeight, h]

/-- ★ **The free weight at the ray of `ψ`** is `|(e^{−itH_D} ψ)_a|² / ‖ψ‖²`. -/
theorem diracWeight_zero_coupling_mk (φ : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    {ψ : EuclideanSpace ℂ (ZMod (M + 1) × Fin 2)} (hψ : ψ ≠ 0) (t : ℝ) :
    diracWeight J μ 0 j hf φ a (Projectivization.mk ℂ ψ hψ) t
      = ‖(chainProp J μ t *ᵥ ⇑ψ) a‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have hU : ((diracCarrierU J μ 0 j hf φ t).val)ᴴ * (diracCarrierU J μ 0 j hf φ t).val = 1 := by
    have hmem := (diracCarrierU J μ 0 j hf φ t).property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  rw [diracWeight_eq_momentMap, arenaKick_mk _ hψ, momentMap_mk,
    Matrix.norm_toEuclideanLin_of_isom hU ψ]
  congr 2
  rw [← diracCarrierU_zero_coupling_val J μ j hf φ t]
  rfl

/-- ★★ **The detector's disturbance of a weight.** On the fibre `θ₂ = φ` the weight of a basis
state at the coupled carrier is within `2 |t| |g f(θ₂)|` of its weight at the free carrier. -/
theorem abs_diracWeight_sub_zero_coupling_le (φ φ' : AddCircle (1 : ℝ))
    (a : ZMod (M + 1) × Fin 2) (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    |diracWeight J μ g j hf φ a p t - diracWeight J μ 0 j hf φ' a p t|
      ≤ 2 * |t| * |g * hf.lift φ| := by
  rw [diracWeight_zero_coupling_congr J μ j hf φ' φ]
  refine (abs_arenaObs_arenaKick_sub_le _ _ (Matrix.single a a (1 : ℂ)) p).trans ?_
  calc 2 * ‖Matrix.single a a (1 : ℂ)‖
        * ‖(diracCarrierU J μ g j hf φ t).val - (diracCarrierU J μ 0 j hf φ t).val‖
      ≤ 2 * 1 * (|t| * |g * hf.lift φ|) := by
        gcongr
        · exact norm_single_self_le a
        · exact norm_diracCarrierU_sub_le J μ g j hf φ t
    _ = 2 * |t| * |g * hf.lift φ| := by ring

/-- ★ **The weight over a short time** is within `2 |t| (‖H_D‖ + |g f(θ₂)|)` of the weight the
carrier started with. -/
theorem abs_diracWeight_sub_init_le (φ : AddCircle (1 : ℝ)) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    |diracWeight J μ g j hf φ a p t - momentMap p a|
      ≤ 2 * |t| * (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) := by
  rw [← diracWeight_zero J μ g j hf φ a p]
  refine (abs_arenaObs_arenaKick_sub_le _ _ (Matrix.single a a (1 : ℂ)) p).trans ?_
  have hU : ‖(diracCarrierU J μ g j hf φ t).val - (diracCarrierU J μ g j hf φ 0).val‖
      ≤ |t| * (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) := by
    rw [diracCarrierU_zero]
    exact (norm_diracCarrierU_sub_one_le J μ g j hf φ t).trans
      (mul_le_mul_of_nonneg_left (norm_diracPointerH_le J μ g j hf φ) (abs_nonneg t))
  calc 2 * ‖Matrix.single a a (1 : ℂ)‖
        * ‖(diracCarrierU J μ g j hf φ t).val - (diracCarrierU J μ g j hf φ 0).val‖
      ≤ 2 * 1 * (|t| * (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|)) := by
        gcongr
        exact norm_single_self_le a
    _ = 2 * |t| * (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) := by ring

/-! ### The basin of a torus-generated rate field -/

/-- **The basin probability**: under the preparation law at the carrier's ray `p`, the probability
that the arena point is at time `t` in the basin of the basis state `a` cut by the rate field
`c`. -/
noncomputable def diracBasinProb (hc : ContDiff ℝ ∞ f) (c : ContextField (2 * M + 1 + 1)) (t : ℝ)
    (a : ZMod (M + 1) × Fin 2) (p : GenArena (ZMod (M + 1) × Fin 2)) : ℝ≥0∞ :=
  epistemicMeasure (diracArenaEquiv M p)
    (diracPointerFlow J μ g j hf hc t ⁻¹' globalBasin c (diracIdx M a))

/-- A torus-generated rate field on `Σ_*` gives the basis state `a` its moment coordinate. -/
theorem rate_diracArenaEquiv_of_isTorusGenerated {c : ContextField (2 * M + 1 + 1)}
    (h : IsTorusGenerated c) (p : GenArena (ZMod (M + 1) × Fin 2)) (a : ZMod (M + 1) × Fin 2) :
    c.rate (diracArenaEquiv M p) (diracIdx M a) = momentMap p a := by
  rw [torusGenerated_eq_momentMap c h]
  exact momentMap_idxArenaEquiv (diracIdx M) p a

/-- ★★ **The basin probability of a torus-generated field** is the weight of the basis state at
the coupled carrier, averaged over the conserved angle `θ₂`.

Conditional on the rate field being torus-generated (UA-6 of
`specs/unified-record-spacetime-plan.md`, Posit 1 of `specs/POSITS.md`): the weights are in `c`.
What is proved is how the flow carries them. -/
theorem diracBasinProb_eq_lintegral (hc : ContDiff ℝ ∞ f) {c : ContextField (2 * M + 1 + 1)}
    (h : IsTorusGenerated c) (t : ℝ) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracBasinProb J μ g j hf hc c t a p
      = ∫⁻ φ : AddCircle (1 : ℝ), ENNReal.ofReal (diracWeight J μ g j hf φ a p t) := by
  rw [diracBasinProb, epistemicMeasure_diracPointerFlow_globalBasin]
  refine lintegral_congr fun φ => ?_
  rw [rate_diracArenaEquiv_of_isTorusGenerated h, diracWeight_eq_momentMap]

/-- ★ **With the coupling off the basin probability is the free weight**, exactly: no error
term. -/
theorem diracBasinProb_zero_coupling (hc : ContDiff ℝ ∞ f) {c : ContextField (2 * M + 1 + 1)}
    (h : IsTorusGenerated c) (t : ℝ) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (φ₀ : AddCircle (1 : ℝ)) :
    diracBasinProb J μ 0 j hf hc c t a p = ENNReal.ofReal (diracWeight J μ 0 j hf φ₀ a p t) := by
  rw [diracBasinProb_eq_lintegral J μ 0 j hf hc h]
  have hcongr : ∀ φ : AddCircle (1 : ℝ),
      ENNReal.ofReal (diracWeight J μ 0 j hf φ a p t)
        = ENNReal.ofReal (diracWeight J μ 0 j hf φ₀ a p t) := fun φ => by
    rw [diracWeight_zero_coupling_congr J μ j hf φ φ₀]
  rw [lintegral_congr hcongr, lintegral_const, measure_univ, mul_one]

/-- ★★★ **The conditional error bound.** For a torus-generated rate field and a profile bounded by
`F`, the basin probability of the basis state `a` at time `t` is within `2 |t| |g| F` of the
weight of `a` at the free carrier. The error is the detector's back-reaction on the carrier and
nothing else.

Conditional on UA-6 (Posit 1): this is not a derivation of the weights from the flow. -/
theorem abs_diracBasinProb_sub_zero_coupling_le (hc : ContDiff ℝ ∞ f)
    {c : ContextField (2 * M + 1 + 1)} (h : IsTorusGenerated c) {F : ℝ}
    (hF : ∀ φ, |hf.lift φ| ≤ F) (t : ℝ) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (φ₀ : AddCircle (1 : ℝ)) :
    |(diracBasinProb J μ g j hf hc c t a p).toReal - diracWeight J μ 0 j hf φ₀ a p t|
      ≤ 2 * |t| * (|g| * F) := by
  rw [diracBasinProb_eq_lintegral J μ g j hf hc h]
  refine abs_toReal_lintegral_ofReal_sub_le volume (diracWeight_nonneg J μ 0 j hf φ₀ a p t)
    fun φ => (abs_diracWeight_sub_zero_coupling_le J μ g j hf φ φ₀ a p t).trans ?_
  rw [abs_mul]
  gcongr
  exact hF φ

/-- ★★ **The conditional error bound against the prepared state.** The basin probability at time
`t` is within `2 |t| (‖H_D‖ + |g| F)` of the weight of `a` in the carrier as prepared: the first
term is the carrier's own motion over the time `t`, the second the detector's back-reaction.

Conditional on UA-6 (Posit 1). -/
theorem abs_diracBasinProb_sub_init_le (hc : ContDiff ℝ ∞ f)
    {c : ContextField (2 * M + 1 + 1)} (h : IsTorusGenerated c) {F : ℝ}
    (hF : ∀ φ, |hf.lift φ| ≤ F) (t : ℝ) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    |(diracBasinProb J μ g j hf hc c t a p).toReal - momentMap p a|
      ≤ 2 * |t| * (‖diracHam (L := M + 1) J μ‖ + |g| * F) := by
  rw [diracBasinProb_eq_lintegral J μ g j hf hc h]
  refine abs_toReal_lintegral_ofReal_sub_le volume (momentMap_nonneg p a)
    fun φ => (abs_diracWeight_sub_init_le J μ g j hf φ a p t).trans ?_
  rw [abs_mul]
  gcongr
  exact hF φ

end Arena

/-! ### The check: the profile `trainF` at the coupling of the click law -/

section Check

variable (M : ℕ) (J μ : ℝ)

/-- ★★ **At the coupling of the click law** (`g = 1/(4T)`, profile `trainF`, readout time `T`) the
basin probability of a torus-generated field is within `1/12` of the free weight, for every
carrier, basis state and `T > 0`. Conditional on UA-6 (Posit 1). -/
theorem abs_diracBasinProb_trainF_sub_le (j : ZMod (M + 1)) {c : ContextField (2 * M + 1 + 1)}
    (h : IsTorusGenerated c) {T : ℝ} (hT : 0 < T) (a : ZMod (M + 1) × Fin 2)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (φ₀ : AddCircle (1 : ℝ)) :
    |(diracBasinProb J μ (1 / (4 * T)) j trainF_periodic contDiff_trainF c T a p).toReal
        - diracWeight J μ 0 j trainF_periodic φ₀ a p T| ≤ 1 / 12 := by
  refine (abs_diracBasinProb_sub_zero_coupling_le J μ (1 / (4 * T)) j trainF_periodic
    contDiff_trainF h abs_trainF_lift_le T a p φ₀).trans_eq ?_
  rw [abs_of_pos hT, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * T))]
  field_simp
  norm_num

end Check

end CSD.RecordLayer

end
