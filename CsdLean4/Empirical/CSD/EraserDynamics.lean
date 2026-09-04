/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.LocalLudersBasis
public import CsdLean4.Empirical.CSD.QuantumEraserVolume

/-!
# Empirical/CSD/EraserDynamics: the eraser as two local measurements (brick 3b)

**Category:** empirical CSD twin, dynamical tier — the eraser *process*, closing the
dynamical no-signalling + eraser row.

`QuantumEraserVolume` certifies the eraser's *statistics* (conditional fringes, the exact
dark-fringe zero) on the conditioned states `eraserOut`. This module derives those
conditioned states **from the measurement machinery itself**: the marker measurements are
the local Lüders maps of `LocalLuders`/`LocalLudersBasis` applied to the Bell path–marker
state, in the two bases the eraser story needs.

* **The joint state**: `bellE`, the corpus's `|00⟩ + |11⟩` as a Euclidean vector; its `B`
  slices are the computational rays (`sliceB_bellE`).
* **The mark arm** (computational marker basis): the post-state of marker outcome `j` is the
  which-path product state, `localProjB j bellE = |j⟩⊗|j⟩` (`localProjB_bellE`), and the
  system's screen statistics are **flat at every phase** (`marked_no_fringe` — rate `1/2`,
  `φ`-independent): which-path information kills the fringe, dynamically.
* **The erase arm** (`±` marker basis, an *instance* of `localProjOn`): the `±` family is a
  genuine `OrthonormalBasis` (`pmBasis`), the post-state factorises through the system
  profile `eraseProfile` (`localProjOn_pm_bellE`), and ★ **the dynamical post-state's screen
  amplitudes are exactly `√2 · eraserOut`** (`erased_amp`) — so every conditional statistic
  `QuantumEraserVolume` certifies for `eraserOut` is a statement about the state *this
  measurement dynamics produces*: the conditional rates (`erased_rate`), and the **exact
  dark-fringe zero from the dynamics** (`erased_dark`). The marker weights are `1/2`
  (`erased_weight`), the dynamical form of `eraser_marker_marginal`.

Together with `reduceA_localLudersOn_mixture` (Alice's marginal is invariant under either
arm — erasing is Bob-side conditioning, never Alice-side signalling), this is the dynamical
eraser: *mark kills the fringe, erase restores it in the conditioned records, and nothing
propagates to the unconditioned marginal.*

⚠️ **Honest scope.** The two arms are single measurement strokes on the composite; the
sequential mark-*then*-erase composition as one protocol run (two successive strokes on one
arena, `csd_sequential_born`-style) is bookkeeping over these states and remains recorded on
the BACKLOG row with the measure-level ensemble integral. The dynamical supplier of the
post-states is, as throughout the route, `BlockLudersObligation` inhabited by
`joinWitness_blockLuders` (through the brick-2 index bridge for the computational arm, and
its local-unitary rotation for the `±` arm).

## References

`specs/BACKLOG.md` (the row); `specs/future-work.md`;
`Empirical/CSD/QuantumEraserVolume.lean` (the statistics this module grounds dynamically);
`Empirical/QM/QuantumEraser.lean` (`bellVec`, `sysBra`, `markBra`);
`RecordLayer/LocalLuders.lean` + `LocalLudersBasis.lean` (the machinery).
-/

@[expose] public section

open MeasureTheory CSD.RecordLayer
open CSD.Empirical.QM.QuantumEraser
open CSD.Empirical.CSDBridge.QuantumEraserVolume
open scoped LinearAlgebra.Projectivization

namespace CSD.Empirical.CSDBridge.EraserDynamics

/-! ### The joint state -/

/-- The Bell path–marker state as a Euclidean vector. -/
noncomputable def bellE : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 QM.QuantumEraser.bellVec

@[simp] lemma bellE_apply (p : Fin 2 × Fin 2) : bellE p = QM.QuantumEraser.bellVec p := rfl

lemma bellVec_eq (p : Fin 2 × Fin 2) :
    QM.QuantumEraser.bellVec p = if p.1 = p.2 then 1 else 0 := by
  rcases p with ⟨a, k⟩
  fin_cases a <;> fin_cases k <;> rfl

lemma bellE_ne_zero : bellE ≠ 0 := by
  intro h
  have h1 : bellE ((0 : Fin 2), (0 : Fin 2)) = 0 := by rw [h]; rfl
  rw [bellE_apply, bellVec_eq] at h1
  simp at h1

/-- **The `B`-slices of the Bell state are the computational rays.** -/
lemma sliceB_bellE (a : Fin 2) :
    sliceB bellE a = EuclideanSpace.single a (1 : ℂ) := by
  apply PiLp.ext
  intro k
  rw [sliceB_apply, bellE_apply, bellVec_eq]
  rw [show (EuclideanSpace.single a (1 : ℂ)) k = if k = a then 1 else 0 from
    PiLp.single_apply 2 ℂ a 1 k]
  exact if_congr eq_comm rfl rfl

/-! ### The mark arm: which-path, no fringe -/

/-- **The computational marker measurement leaves the which-path product state**:
`Pⱼ |Φ⟩ = |j⟩ ⊗ |j⟩`. -/
theorem localProjB_bellE (j : Fin 2) :
    localProjB j bellE = EuclideanSpace.single ((j, j) : Fin 2 × Fin 2) (1 : ℂ) := by
  apply PiLp.ext
  intro ak
  rw [localProjB_apply]
  rw [show (EuclideanSpace.single ((j, j) : Fin 2 × Fin 2) (1 : ℂ)) ak
      = if ak = (j, j) then 1 else 0 from PiLp.single_apply 2 ℂ (j, j) 1 ak]
  rcases eq_or_ne ak.2 j with hk | hk
  · rw [if_pos hk, bellE_apply, bellVec_eq]
    rcases eq_or_ne ak.1 ak.2 with ha | ha
    · rw [if_pos ha, if_pos (by rw [Prod.ext_iff]; exact ⟨ha.trans hk, hk⟩)]
    · rw [if_neg ha,
        if_neg (by rw [Prod.ext_iff]; rintro ⟨h1, _⟩; exact ha (h1.trans hk.symm))]
  · rw [if_neg hk, if_neg (by rw [Prod.ext_iff]; rintro ⟨_, h2⟩; exact hk h2)]

/-- The screen-basis state, as a Euclidean vector. -/
noncomputable def sysE (φ a : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (sysBra φ a)

@[simp] lemma sysE_apply (φ a : ℝ) (i : Fin 2) : sysE φ a i = sysBra φ a i := rfl

lemma sysE_one_eq (φ a : ℝ) :
    sysE φ a 1 = (↑(a * Real.cos φ) : ℂ) + (↑(a * Real.sin φ) : ℂ) * Complex.I := by
  rw [sysE_apply]
  show (a : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I) = _
  push_cast
  ring

lemma normSq_sysE_one (φ : ℝ) {a : ℝ} (ha : a = 1 ∨ a = -1) : ‖sysE φ a 1‖ ^ 2 = 1 := by
  rw [sysE_one_eq, Complex.sq_norm, Complex.normSq_add_mul_I]
  rcases ha with ha | ha <;> subst ha <;>
    linear_combination Real.sin_sq_add_cos_sq φ

lemma normSq_sysE (φ : ℝ) {a : ℝ} (ha : a = 1 ∨ a = -1) : ‖sysE φ a‖ ^ 2 = 2 := by
  have hE : ‖sysE φ a‖ ^ 2 = ∑ i, ‖sysE φ a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hE, Fin.sum_univ_two, normSq_sysE_one φ ha]
  have h0 : sysE φ a 0 = 1 := rfl
  rw [h0]
  norm_num

/-- **The which-path state shows no fringe**: the screen rate is `1/2` at *every* phase and
screen port — the flat statistics of a marked path, produced by the mark stroke itself. -/
theorem marked_no_fringe (φ : ℝ) {a : ℝ} (ha : a = 1 ∨ a = -1) (j : Fin 2) :
    ‖(inner ℂ (sysE φ a) (EuclideanSpace.single j (1 : ℂ)) : ℂ)‖ ^ 2 / ‖sysE φ a‖ ^ 2
      = 1 / 2 := by
  have hin : (inner ℂ (sysE φ a) (EuclideanSpace.single j (1 : ℂ)) : ℂ)
      = (starRingEnd ℂ) (sysE φ a j) := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    fin_cases j <;>
      simp [RCLike.inner_apply]
  rw [hin, RCLike.norm_conj, normSq_sysE φ ha]
  have hnj : ‖sysE φ a j‖ ^ 2 = 1 := by
    fin_cases j
    · show ‖(1 : ℂ)‖ ^ 2 = 1
      simp
    · exact normSq_sysE_one φ ha
  rw [hnj]

/-! ### The ± marker basis -/

/-- The `±` sign of a marker index: `+1` for `0`, `−1` for `1`. -/
def pmSign (m : Fin 2) : ℝ := if m = 0 then 1 else -1

lemma pmSign_cases (m : Fin 2) : pmSign m = 1 ∨ pmSign m = -1 := by
  fin_cases m <;> simp [pmSign]

/-- The normalised `±` marker vectors `(|0⟩ ± |1⟩)/√2`. -/
noncomputable def pmVec (m : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2
    ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), ((pmSign m : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]

@[simp] lemma pmVec_zero (m : Fin 2) : pmVec m 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := rfl

@[simp] lemma pmVec_one (m : Fin 2) :
    pmVec m 1 = ((pmSign m : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := rfl

lemma invSqrtTwo_mul_self : ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma invSqrtTwo_eq : ((Real.sqrt 2)⁻¹ : ℝ) = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

lemma invSqrtTwoC_mul_self :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, invSqrtTwo_mul_self]

lemma inner_pmVec (i j : Fin 2) :
    (inner ℂ (pmVec i) (pmVec j) : ℂ) = (((1 + pmSign i * pmSign j) / 2 : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, pmVec_zero, pmVec_one, map_mul, Complex.conj_ofReal]
  have hreal : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹
      + pmSign j * (Real.sqrt 2)⁻¹ * (pmSign i * (Real.sqrt 2)⁻¹)
      = (1 + pmSign i * pmSign j) / 2 := by
    linear_combination (1 + pmSign i * pmSign j) * invSqrtTwo_mul_self
  exact_mod_cast hreal

/-- The `±` family is orthonormal. -/
lemma orthonormal_pmVec : Orthonormal ℂ pmVec := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_pmVec]
  fin_cases i <;> fin_cases j <;> norm_num [pmSign]

/-- **The `±` marker basis**, as a genuine orthonormal basis — the erase arm is an instance
of `localProjOn`, not a hand-built pair of projectors. -/
noncomputable def pmBasis : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (basisOfOrthonormalOfCardEqFinrank orthonormal_pmVec
    (by simp [finrank_euclideanSpace])).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact orthonormal_pmVec)

lemma pmBasis_coe : ⇑pmBasis = pmVec := by
  rw [pmBasis, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

/-! ### The erase arm: the conditioned states, from the dynamics -/

/-- The system profile of the `±`-conditioned post-state: the coefficient family of
`localProjOn pmBasis m bellE` (see `localProjOn_pm_bellE`). -/
noncomputable def eraseProfile (m : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun a => inner ℂ (pmVec m) (sliceB bellE a)

/-- The erase-arm post-state factorises: system profile ⊗ marker vector. -/
theorem localProjOn_pm_bellE (m : Fin 2) (ak : Fin 2 × Fin 2) :
    localProjOn pmBasis m bellE ak = eraseProfile m ak.1 * pmVec m ak.2 := by
  rw [localProjOn_apply]
  rw [show pmBasis m = pmVec m from congrFun pmBasis_coe m]
  rfl

lemma eraseProfile_apply (m a : Fin 2) :
    eraseProfile m a = (starRingEnd ℂ) (pmVec m a) := by
  show (inner ℂ (pmVec m) (sliceB bellE a) : ℂ) = _
  rw [sliceB_bellE, PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases a <;> simp [RCLike.inner_apply]

lemma normSq_eraseProfile (m : Fin 2) : ‖eraseProfile m‖ ^ 2 = 1 := by
  have hE : ∀ w : EuclideanSpace ℂ (Fin 2), ‖w‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hE]
  have hpm : ∑ k, ‖pmVec m k‖ ^ 2 = 1 := by
    rw [← hE, orthonormal_pmVec.1 m, one_pow]
  rw [← hpm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eraseProfile_apply, RCLike.norm_conj]

/-- ★ **The dynamical post-state's screen amplitudes are exactly `√2 · eraserOut`**: the
states the erase stroke produces are the states whose statistics `QuantumEraserVolume`
certifies — conditional fringes, dark zero, and all. -/
theorem erased_amp (φ : ℝ) (i m : Fin 2) :
    (inner ℂ (sysE φ (pmSign i)) (eraseProfile m) : ℂ)
      = ((Real.sqrt 2 : ℝ) : ℂ) * eraserOut φ (pmSign m) i := by
  have hinvC : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
    rw [invSqrtTwo_eq]
    push_cast
    ring
  have hconj1 : ∀ b : ℝ, (starRingEnd ℂ) (sysBra φ b 1) = (b : ℂ) * phaseC φ := by
    intro b
    show (starRingEnd ℂ)
      ((b : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)) = _
    rw [map_mul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_I, phaseC]
    ring
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, sysE_apply, eraseProfile_apply, pmVec_zero, pmVec_one,
    map_mul, Complex.conj_ofReal]
  rw [hconj1]
  have hconj0 : (starRingEnd ℂ) (sysBra φ (pmSign i) 0) = 1 := map_one _
  rw [hconj0]
  have hinvC' : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
    rw [← Complex.ofReal_inv]
    exact hinvC
  fin_cases i <;> fin_cases m <;>
    · simp only [pmSign]
      norm_num [eraserOut_zero, eraserOut_one]
      rw [hinvC']
      ring

/-- ★ **The dark fringe from the dynamics**: at `φ = π`, the `+`-conditioned post-state has
exactly zero amplitude at the bright port — the eraser's exact ontic zero, produced by the
erase stroke. -/
theorem erased_dark :
    (inner ℂ (sysE Real.pi (pmSign 0)) (eraseProfile 0) : ℂ) = 0 := by
  rw [erased_amp]
  have h0 : eraserOut Real.pi (pmSign 0) 0 = 0 := by
    rw [show pmSign 0 = 1 from rfl]
    exact eraserOut_pi_zero
  rw [h0, mul_zero]

/-- **The conditional screen rates of the dynamical post-state are the `eraserOut` rates** —
the fringes `QuantumEraserVolume` certifies, now as statistics of the measurement
dynamics' own output. -/
theorem erased_rate (φ : ℝ) (i m : Fin 2) :
    ‖(inner ℂ (sysE φ (pmSign i)) (eraseProfile m) : ℂ)‖ ^ 2
        / (‖sysE φ (pmSign i)‖ ^ 2 * ‖eraseProfile m‖ ^ 2)
      = ‖eraserOut φ (pmSign m) i‖ ^ 2 := by
  have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [erased_amp, norm_mul, mul_pow, h2, normSq_sysE φ (pmSign_cases i),
    normSq_eraseProfile, mul_one, mul_comm, mul_div_assoc, div_self (two_ne_zero), mul_one]

/-- **The marker weights are `1/2`** — the dynamical form of `eraser_marker_marginal`. -/
theorem erased_weight (m : Fin 2) :
    ‖localProjOn pmBasis m bellE‖ ^ 2 / ‖bellE‖ ^ 2 = 1 / 2 := by
  have hE2 : ∀ w : EuclideanSpace ℂ (Fin 2), ‖w‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hE4 : ∀ w : EuclideanSpace ℂ (Fin 2 × Fin 2), ‖w‖ ^ 2 = ∑ ak, ‖w ak‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hP : ‖localProjOn pmBasis m bellE‖ ^ 2 = 1 := by
    rw [hE4, Fintype.sum_prod_type]
    have hterm : ∀ a k, ‖localProjOn pmBasis m bellE (a, k)‖ ^ 2
        = ‖eraseProfile m a‖ ^ 2 * ‖pmVec m k‖ ^ 2 := by
      intro a k
      rw [show ((a, k) : Fin 2 × Fin 2) = (a, k) from rfl, localProjOn_pm_bellE,
        norm_mul, mul_pow]
    simp only [hterm]
    rw [← Finset.sum_mul_sum]
    have h1 : ∑ a, ‖eraseProfile m a‖ ^ 2 = 1 := by rw [← hE2, normSq_eraseProfile]
    have h2 : ∑ k, ‖pmVec m k‖ ^ 2 = 1 := by rw [← hE2, orthonormal_pmVec.1 m, one_pow]
    rw [h1, h2, mul_one]
  have hB : ‖bellE‖ ^ 2 = 2 := by
    rw [hE4, Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [bellE_apply, bellVec_eq]
    norm_num
  rw [hP, hB]

end CSD.Empirical.CSDBridge.EraserDynamics
