/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.MalusVolume
public import CsdLean4.LF4.ObservableFlow
public import CsdLean4.Empirical.QM.Gates.SingleQubit

/-!
# Empirical/Metrology: Ramsey interferometry as a parameter-driven Kähler flow

**Category:** 3-Local (CSD-ontic metrology layer; genuine volume derivation, not a
transport tag).

This is **item A1** of `specs/metrology-plan.md`: the Ramsey sequence
`|0⟩ → [π/2 pulse] → [free precession, phase φ(θ)] → [π/2 pulse] → measure`
realised in CSD. Two pieces:

1. **The phase flow** (`ramseyPhaseFlow`). The free-precession step is the diagonal
   unitary `diag(1, e^{iφ})` acting on the probe `Σ = ℂℙ¹`. It is the first
   *metrology* flow: a deterministic, **Fubini–Study-measure-preserving** symplectic
   flow on `Σ` driven by the external classical parameter `φ(θ) = ω·t`
   (`ramseyPhaseFlow_measurePreserving`), genuinely `≠ id`
   (`ramseyPhaseFlow_ne_id`). It is the `λ = (0,1)` instance of the audited
   diagonal-phase observable flow `LF4.obsFlow` (`diag(exp(i·t·λ))`); we reuse that
   machinery rather than reinvent it.

2. **The fringe** (`ramsey_fringe_volume`). The measurement-`|0⟩` probability is the
   standard symmetric Ramsey fringe `cos²(φ/2)`. The Ramsey output state `ramseyVec φ`
   is machine-checked to be the genuine interferometer output
   `H · diag(1,e^{iφ}) · H · |0⟩` (`ramseyVec_eq_circuit`, with the corpus Hadamard
   `QM.Gates.qmH` and the same diagonal the flow uses); it has `|0⟩`-amplitude `(1 + e^{iφ})/2`,
   so its Born weight is `‖(1 + e^{iφ})/2‖² = (1 + cos φ)/2 = cos²(φ/2)`. The fringe
   is therefore the **Malus reading** (`Empirical/CSD/MalusVolume.csd_malus_law`)
   with `θ = φ` the accumulated phase: the `|0⟩`-outcome moment-sublevel region cut
   by `[ramseyVec φ]` has Fubini–Study volume `cos²(φ/2)`, and i.i.d. FS-typicality
   frequencies converge to it via `LF4.qubit_born_frequency_convergence_uncond`. With
   `Born = FS volume` *derived* one layer down (the Duistermaat–Heckman /
   moment-map cluster, `fs_moment_pushforward_uniform`), this is carving-free and
   **Gleason-free** (foundational triple only, no `busch_effect_gleason`).

## What is and is not claimed

**Derived (Lean-checked, carving-free, Gleason-free).** The fringe value `cos²(φ/2)`
is the genuine Fubini–Study volume of the moment-sublevel region cut by the Ramsey
output ray, and i.i.d. FS frequencies converge to it. The phase flow is a genuine
`Φ ≠ id`, FS-measure-preserving deterministic dynamics on the probe `Σ = ℂℙ¹`.

**Honest scope / not claimed.** This is single-qubit (single-system) Ramsey. The
`Born = FS volume` identity is *imported* from the DH cluster, not re-derived here;
the concrete `SectorData` instances still carry `Φ = id` (this metrology phase flow
runs on the projective probe space, not threaded through `SectorData`). The
moment-region ↔ physical-detector identification is LF4-todo §14. The Quantum Fisher
Information = Fubini–Study metric (A2), the Heisenberg `1/N` limit (A3), and
decoherence as open symplectic drift (A4) are deferred per `specs/metrology-plan.md`;
the fringe sensitivity `dP/dφ = -(sin φ)/2` here (`ramsey_fringe_hasDerivAt`) is the
QFI precursor, with maximal slope at `φ = π/2`.

## Experimental verification

- Ramsey 1950: *Phys. Rev.* **78**, 695 (the method of separated oscillatory fields).
  The symmetric `cos²(φ/2)` fringe is the canonical two-pulse Ramsey signal (standard
  atomic-clock / interferometry references).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace Metrology

/-! ### The Ramsey phase flow (free precession) -/

/-- The free-precession diagonal `diag(1, e^{iφ})` is the `λ = (0,1)` observable
eigenvalue vector: `obsPhase ![0,1] φ = (exp(i·φ·0), exp(i·φ·1)) = (1, e^{iφ})`. -/
def ramseyLam : Fin 2 → ℝ := ![0, 1]

/-- **The Ramsey phase flow `Φ_φ`** (the free-precession step): the deterministic
self-map of the probe projective ontic space `Σ = ℂℙ¹` given by the action of the
free-precession unitary `diag(1, e^{iφ})`. It is the `λ = ramseyLam` instance of the
audited diagonal-phase observable flow `LF4.obsFlow`; the external parameter
`φ(θ) = ω·t` drives the flow. -/
noncomputable def ramseyPhaseFlow (φ : ℝ) : CPN 2 → CPN 2 :=
  CSD.LF4.obsFlow ramseyLam φ

lemma ramseyPhaseFlow_apply (φ : ℝ) (p : CPN 2) :
    ramseyPhaseFlow φ p = CSD.LF4.obsUnitary ramseyLam φ • p := rfl

/-- **FS-invariance of the Ramsey phase flow (the Liouville / `hΦ_pres` content).**
The first metrology flow: the parameter-`φ`-driven free precession preserves the
Fubini–Study typicality measure on the probe `Σ = ℂℙ¹`, so it is a physically
admissible deterministic ontic dynamics in the LF1 sense. Direct from the corpus's
U(2)-invariance via the diagonal-phase observable flow. -/
theorem ramseyPhaseFlow_measurePreserving (φ : ℝ) (p₀ : CPN 2) :
    MeasurePreserving (ramseyPhaseFlow φ)
      (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  CSD.LF4.obsFlow_measurePreserving ramseyLam φ p₀

/-- `ramseyLam = ![0,1]` is exactly the `N = 2` non-triviality eigenvalue witness
`obsLamWitness` of `ObservableFlow.lean`. -/
lemma ramseyLam_eq_obsLamWitness :
    ramseyLam = CSD.LF4.obsLamWitness (show (1 : ℕ) < 2 by norm_num) := by
  funext i
  fin_cases i <;>
    simp [ramseyLam, CSD.LF4.obsLamWitness, CSD.LF4.obsIdx1]

/-- **The Ramsey phase flow is genuinely not the identity** (at `φ = π`, the full
`diag(1,-1)` inversion). The computational-basis rays are fixed (they are eigenvectors
of the diagonal flow), so the witness is the superposition `[|0⟩+|1⟩]`, whose two
populated coordinates acquire the distinct phases `1` and `-1`. This is the genuine
`Φ ≠ id` half of the metrology flow. Reduces to the audited `LF4.obsFlow_ne_id`. -/
theorem ramseyPhaseFlow_ne_id : ramseyPhaseFlow Real.pi ≠ id := by
  have h := CSD.LF4.obsFlow_ne_id (N := 2) (show (1 : ℕ) < 2 by norm_num)
  rwa [ramseyPhaseFlow, ramseyLam_eq_obsLamWitness, show Real.pi = CSD.LF4.obsTWitness from rfl]

/-! ### The Ramsey output state and its fringe amplitude -/

/-- The **Ramsey output state** `H · diag(1, e^{iφ}) · H · |0⟩`, given in closed
form: `(1/2)·((1 + e^{iφ})|0⟩ + (1 - e^{iφ})|1⟩)`. That this closed form genuinely IS
the interferometer circuit output is machine-checked in `ramseyVec_eq_circuit` (not a
hand-check). Its `|0⟩`-amplitude is `(1 + e^{iφ})/2`, giving the fringe Born weight
`cos²(φ/2)` via `ramseyVec_amp_zero_sq`. -/
noncomputable def ramseyVec (φ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 ((1 + Complex.exp ((φ : ℂ) * Complex.I)) / 2)
    + EuclideanSpace.single 1 ((1 - Complex.exp ((φ : ℂ) * Complex.I)) / 2)

lemma ramseyVec_ofLp_zero (φ : ℝ) :
    (ramseyVec φ).ofLp 0 = (1 + Complex.exp ((φ : ℂ) * Complex.I)) / 2 := by
  simp [ramseyVec, EuclideanSpace.single]

lemma ramseyVec_ofLp_one (φ : ℝ) :
    (ramseyVec φ).ofLp 1 = (1 - Complex.exp ((φ : ℂ) * Complex.I)) / 2 := by
  simp [ramseyVec, EuclideanSpace.single]

/-- `e^{iφ} = cos φ + (sin φ)·i` (real/imaginary split of the free-precession phase). -/
lemma exp_phase_eq (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I)
      = (↑(Real.cos φ) : ℂ) + (↑(Real.sin φ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **The fringe Born weight (cosine branch).**
`‖(1 + e^{iφ})/2‖² = (1 + cos φ)/2 = cos²(φ/2)` — the symmetric Ramsey fringe. -/
lemma ramseyVec_amp_zero_sq (φ : ℝ) :
    ‖(1 + Complex.exp ((φ : ℂ) * Complex.I)) / 2‖ ^ 2 = Real.cos (φ / 2) ^ 2 := by
  have hw : (1 + Complex.exp ((φ : ℂ) * Complex.I)) / 2
      = (↑((1 + Real.cos φ) / 2) : ℂ) + (↑(Real.sin φ / 2) : ℂ) * Complex.I := by
    rw [exp_phase_eq]; push_cast; ring
  rw [Complex.sq_norm, hw, Complex.normSq_add_mul_I]
  have hcos2 : Real.cos (φ / 2) ^ 2 = 1 / 2 + Real.cos φ / 2 := by
    have h := Real.cos_sq (φ / 2)
    rwa [show 2 * (φ / 2) = φ by ring] at h
  rw [hcos2]
  linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq φ

/-- **The complementary fringe Born weight (sine branch).**
`‖(1 - e^{iφ})/2‖² = (1 - cos φ)/2 = sin²(φ/2)` — the `|1⟩` outcome. -/
lemma ramseyVec_amp_one_sq (φ : ℝ) :
    ‖(1 - Complex.exp ((φ : ℂ) * Complex.I)) / 2‖ ^ 2 = Real.sin (φ / 2) ^ 2 := by
  have hw : (1 - Complex.exp ((φ : ℂ) * Complex.I)) / 2
      = (↑((1 - Real.cos φ) / 2) : ℂ) + (↑(-(Real.sin φ) / 2) : ℂ) * Complex.I := by
    rw [exp_phase_eq]; push_cast; ring
  rw [Complex.sq_norm, hw, Complex.normSq_add_mul_I]
  have hsin2 : Real.sin (φ / 2) ^ 2 = 1 / 2 - Real.cos φ / 2 := by
    have hc := Real.cos_sq (φ / 2)
    have hsc := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at hc
    linarith
  rw [hsin2]
  linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq φ

lemma ramseyVec_norm (φ : ℝ) : ‖ramseyVec φ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, ramseyVec_ofLp_zero, ramseyVec_ofLp_one]
  rw [ramseyVec_amp_zero_sq, ramseyVec_amp_one_sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]

lemma ramseyVec_ne_zero (φ : ℝ) : ramseyVec φ ≠ 0 := by
  intro h
  have hz : ‖ramseyVec φ‖ = 0 := by rw [h, norm_zero]
  rw [ramseyVec_norm] at hz
  exact one_ne_zero hz

/-! ### The Ramsey output state IS the interferometer circuit `H · D(φ) · H · |0⟩` -/

/-- The **free-precession diagonal** `D(φ) = diag(1, e^{iφ})` — the same diagonal the
flow `ramseyPhaseFlow` uses (see `ramseyD_eq_obsUnitary`). -/
noncomputable def ramseyD (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, Complex.exp ((φ : ℂ) * Complex.I)]

/-- `D(φ)` is exactly the unitary generating the Ramsey phase flow: the free-precession
matrix in the circuit and the generator of `ramseyPhaseFlow` are the same object
(`obsPhase ramseyLam φ = (exp(i·φ·0), exp(i·φ·1)) = (1, e^{iφ})`, up to `mul_comm`). -/
lemma ramseyD_eq_obsUnitary (φ : ℝ) :
    ramseyD φ = (CSD.LF4.obsUnitary ramseyLam φ).val := by
  rw [CSD.LF4.obsUnitary_val, ramseyD]
  congr 1
  funext i
  fin_cases i <;> simp [CSD.LF4.obsPhase, ramseyLam, mul_comm]

/-- **The Ramsey output state is the genuine interferometer circuit output**, machine
checked: `ramseyVec φ = H · D(φ) · H · |0⟩`, with `H` the corpus Hadamard
`QM.Gates.qmH = (1/√2)!![1,1;1,-1]` and `D(φ) = diag(1, e^{iφ})` the free-precession
phase. Both output coordinates reduce (via `Fin`-casing) to the already-proved
`ramseyVec_ofLp_*` amplitudes `(1 ± e^{iφ})/2`. This turns the docstring's
`H·diag·H·|0⟩` from a hand-check into a kernel-checked identity. -/
theorem ramseyVec_eq_circuit (φ : ℝ) :
    ramseyVec φ
      = Matrix.toEuclideanLin QM.Gates.qmH
          (Matrix.toEuclideanLin (ramseyD φ)
            (Matrix.toEuclideanLin QM.Gates.qmH (EuclideanSpace.single 0 (1 : ℂ)))) := by
  have key : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2),
      (Matrix.toEuclideanLin M v).ofLp i = ∑ j, M i j * v.ofLp j := fun M v i => by
    rw [Matrix.toLpLin_apply]; rfl
  have hsqA : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i
  fin_cases i
  · simp only [key, Fin.sum_univ_two, QM.Gates.qmH, ramseyD, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, PiLp.single_apply, Fin.mk_zero, Fin.isValue,
      ramseyVec_ofLp_zero]
    norm_num
    linear_combination (-(1 + Complex.exp ((φ : ℂ) * Complex.I))) * hsqA
  · simp only [key, Fin.sum_univ_two, QM.Gates.qmH, ramseyD, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, PiLp.single_apply, Fin.mk_one, Fin.isValue,
      ramseyVec_ofLp_one]
    norm_num
    linear_combination (-(1 - Complex.exp ((φ : ℂ) * Complex.I))) * hsqA

/-! ### The Ramsey fringe as a derived Kähler volume -/

/-- The **Ramsey fringe** `P(|0⟩ | φ) = cos²(φ/2)` (the measurement-`|0⟩`
probability). -/
noncomputable def ramseyFringe (φ : ℝ) : ℝ := Real.cos (φ / 2) ^ 2

/-- **Interferometer maximum**: at zero accumulated phase the fringe is `1`
(constructive). -/
theorem ramsey_fringe_max : ramseyFringe 0 = 1 := by
  simp [ramseyFringe]

/-- **Interferometer minimum**: at `φ = π` the fringe is `0` (destructive). -/
theorem ramsey_fringe_min : ramseyFringe Real.pi = 0 := by
  rw [ramseyFringe, Real.cos_pi_div_two]
  norm_num

/-- **The Ramsey fringe as a derived Kähler-volume frequency.**
For i.i.d. trials drawing microstates from the Fubini–Study typicality measure on the
probe `Σ = ℂℙ¹`, the empirical frequency of the moment-sublevel `|0⟩`-outcome region
cut by the Ramsey output ray `[ramseyVec φ]` converges almost surely to the standard
symmetric Ramsey fringe `cos²(φ/2)` (`= ramseyFringe φ`).

The limit is `‖⟨e₀, ramseyVec φ⟩‖² = ‖(1 + e^{iφ})/2‖² = cos²(φ/2)`, with
`volume = Born` *derived* from the moment map (no carving), foundational triple only
(no `busch_effect_gleason`). The Ramsey fringe is the Malus reading
(`Empirical/CSD/MalusVolume.csd_malus_law`) with `θ = φ` the accumulated phase. The
identification of the region with the physical detector outcome is LF4-todo §14. -/
theorem ramsey_fringe_volume
    (φ : ℝ) (p₀ : CPN 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                momentMap (Projectivization.mk ℂ (ramseyVec φ) (ramseyVec_ne_zero φ)) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ (ramseyVec φ) (ramseyVec_ne_zero φ)) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (ramseyFringe φ)) := by
  have h := qubit_born_frequency_convergence_uncond p₀ (ramseyVec φ)
    (ramseyVec_ne_zero φ) (ramseyVec_norm φ) X hX hlaw hindep
  have hv : ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (ramseyVec φ)‖ ^ 2
      = ramseyFringe φ := by
    rw [CSDBridge.SternGerlachVolume.normSq_inner_single_zero, ramseyVec_ofLp_zero,
        ramseyVec_amp_zero_sq]
    rfl
  rwa [hv] at h

/-! ### Fringe sensitivity (the QFI precursor) -/

set_option backward.isDefEq.respectTransparency false in
/-- **Fringe sensitivity** `dP/dφ = -(sin φ)/2` (the slope of `cos²(φ/2)`). The
maximal-sensitivity operating point is `φ = π/2`, where `|dP/dφ| = 1/2`
(`ramsey_sensitivity_at_quadrature`). This is the precursor to the Quantum Fisher
Information = Fubini–Study metric statement (A2), deferred per
`specs/metrology-plan.md`. -/
theorem ramsey_fringe_hasDerivAt (φ : ℝ) :
    HasDerivAt ramseyFringe (-(Real.sin φ) / 2) φ := by
  have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) φ := by
    simpa using (hasDerivAt_id φ).div_const 2
  have h2 := (Real.hasDerivAt_cos (φ / 2)).comp φ h1
  have h3 := h2.pow 2
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  convert h3 using 1 <;>
    first
      | rfl
      | (simp only [Function.comp_apply]; rw [hs]; push_cast; ring)

/-- The fringe slope is maximal in magnitude at quadrature `φ = π/2`: `dP/dφ = -1/2`. -/
theorem ramsey_sensitivity_at_quadrature :
    (-(Real.sin (Real.pi / 2)) / 2 : ℝ) = -(1 / 2) := by
  rw [Real.sin_pi_div_two]; norm_num

end Metrology
end Empirical
end CSD
