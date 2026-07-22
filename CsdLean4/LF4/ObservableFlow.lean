/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.MomentMap
import CsdLean4.LF1.GeneralFrequency
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive

/-!
# The measured observable's Hamiltonian flow on `Σ = ℂℙ^{N-1}`

**Category:** 3-Local (The measured observable's Hamiltonian flow on `Σ = ℂℙ^{N-1}`).

The first physically-meaningful `Φ ≠ id` in the corpus. A measurement context is a choice of
observable `Â` (the apparatus measures `Â`), diagonal `diag(λ)` in its eigenbasis. Its
Hamiltonian flow on `Σ` is the one-parameter unitary group `t ↦ exp(i t Â)`, acting on
`ℂℙ^{N-1}` by `obsFlow λ t [ψ] = [exp(i t Â) ψ]`.

This file establishes that `obsFlow` is a genuine **measure-preserving** deterministic flow
whose **conserved quantities are exactly the Born weights**:

* `obsFlow_measurePreserving` — `Φ` preserves the Fubini–Study (typicality) measure, via the
  corpus's U(N)-invariance `fubiniStudyMeasure_smul_invariant`. So it is an admissible ontic
  flow (Liouville), unlike a generic relabeling.
* `momentMap_obsFlow` (**headline**) — the moment-map coordinates are invariant along the
  flow: `momentMap (obsFlow λ t p) i = momentMap p i`. Combined with
  `momentMap_mk_eq_inner_sq` (moment coordinate = Born weight `‖⟨eᵢ,ψ⟩‖²`) and the
  Duistermaat–Heckman result (`fs_born_volume_ratio_N`, Born = FS-volume), this says: **the
  Born weights are the constants of motion of the measured observable's own flow, and equal
  the typicality volumes.** This is the concrete realisation of "the measurement context
  constrains the volumes in `Σ`."

**Honest scope.** The proof of conservation is light (the phases have modulus one). The
content is the *identification*: a measure-preserving `Φ ≠ id` whose conserved quantities are
the Born volumes (`momentMap_obsFlow`), tying the observable's dynamics to those volumes.
The `Φ ≠ id` claim is now separately witnessed by `obsFlow_ne_id` (mirroring `kFlow_ne_id`):
because `obsFlow` is a *diagonal phase* flow, every computational basis ray `[eᵢ]` is an
eigenvector and is **fixed**, so the witness is necessarily a **superposition** ray — the
`|0⟩+|1⟩` ray, whose two coordinates pick up the distinct phases `1` and `-1` (at
`lam := indicator of index 1`, `t := π`), so its image `(1,-1,0,…)` is non-collinear with
`(1,1,0,…)`. What is *not* here is the
measurement **event** — the flow conserves the populations (a non-disturbing / compatible
measurement at the ontic level), it does not carry microstates into pointer regions and
commit an outcome. That measurement-dynamics content is now built in the **LF5 layer**
(`CsdLean4/LF5/`, single-system projective tier complete: `measurementFlow ≠ id`,
`measurement_flow_born_frequency`, the per-microstate outcome function `vnPointerOutcome`);
the deeper D1 strata (entangled de-isolation, instance-level dynamics) remain open.
-/

open scoped LinearAlgebra.Projectivization
open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter

namespace CSD
namespace LF4

variable {N : ℕ}

/-- The unit-modulus phase `exp(i t λᵢ)` of the observable `diag(λ)` at time `t`. -/
noncomputable def obsPhase (lam : Fin N → ℝ) (t : ℝ) (i : Fin N) : ℂ :=
  Complex.exp (Complex.I * ((t * lam i : ℝ) : ℂ))

/-- The phase has modulus one (it lies on the unit circle). -/
@[simp] lemma obsPhase_norm (lam : Fin N → ℝ) (t : ℝ) (i : Fin N) :
    ‖obsPhase lam t i‖ = 1 := by
  rw [obsPhase, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The defining unitarity of each phase: `star (phase) · phase = 1`. -/
lemma obsPhase_star_mul (lam : Fin N → ℝ) (t : ℝ) (i : Fin N) :
    star (obsPhase lam t i) * obsPhase lam t i = 1 := by
  rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj']
  rw [obsPhase_norm]
  norm_num

/-- The **observable's unitary** `exp(i t Â) = diag(exp(i t λᵢ))` as an element of `U(N)`. -/
noncomputable def obsUnitary (lam : Fin N → ℝ) (t : ℝ) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨diagonal (obsPhase lam t), by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [show (fun i => star (obsPhase lam t) i * obsPhase lam t i) = fun _ => (1 : ℂ) from
      funext fun i => by rw [Pi.star_apply]; exact obsPhase_star_mul lam t i]
    exact Matrix.diagonal_one⟩

@[simp] lemma obsUnitary_val (lam : Fin N → ℝ) (t : ℝ) :
    (obsUnitary lam t).val = diagonal (obsPhase lam t) := rfl

/-- The observable's action on a Hilbert vector is the diagonal phase action. -/
lemma obsUnitary_toEuclideanLin_apply (lam : Fin N → ℝ) (t : ℝ)
    (v : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (Matrix.toEuclideanLin (obsUnitary lam t).val v) i = obsPhase lam t i * v i := by
  rw [obsUnitary_val, Matrix.toLpLin_apply]
  simp [Matrix.mulVec_diagonal]

/-- The observable's flow is **norm-preserving** on the Hilbert space (it is unitary),
in squared-norm form. -/
lemma obsUnitary_normSq (lam : Fin N → ℝ) (t : ℝ) (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin (obsUnitary lam t).val) v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [obsUnitary_toEuclideanLin_apply, norm_mul, obsPhase_norm, one_mul]

/-- The diagonal phase action sends a nonzero vector to a nonzero vector. -/
lemma obsUnitary_apply_ne_zero (lam : Fin N → ℝ) (t : ℝ)
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin (obsUnitary lam t).val) v ≠ 0 := fun hz => by
  have h := obsUnitary_normSq lam t v
  rw [hz, norm_zero, zero_pow (two_ne_zero)] at h
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv) h.symm

/-- The **measured observable's Hamiltonian flow** on `Σ = ℂℙ^{N-1}`:
`obsFlow λ t [ψ] = [exp(i t Â) ψ]`. -/
noncomputable def obsFlow (lam : Fin N → ℝ) (t : ℝ) : CPN N → CPN N :=
  fun p => obsUnitary lam t • p

/-- **The flow preserves the Fubini–Study (typicality) measure** — an admissible ontic flow
(Liouville). Direct from the corpus's U(N)-invariance. -/
theorem obsFlow_measurePreserving (lam : Fin N → ℝ) (t : ℝ) (p₀ : CPN N) :
    MeasurePreserving (obsFlow lam t) (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) where
  measurable := (continuous_const_smul (obsUnitary lam t)).measurable
  map_eq := fubiniStudyMeasure_smul_invariant (obsUnitary lam t) p₀

/-! ## Non-triviality witness (`Φ ≠ id`) -/

/-- Index `0` packaged with the `1 < N` bound (avoids `OfNat (Fin N) 0`, no `NeZero`). -/
def obsIdx0 (hN : 1 < N) : Fin N := ⟨0, by omega⟩
/-- Index `1` packaged with the `1 < N` bound. -/
def obsIdx1 (hN : 1 < N) : Fin N := ⟨1, hN⟩

lemma obsIdx0_ne_obsIdx1 (hN : 1 < N) : obsIdx0 hN ≠ obsIdx1 hN := by
  simp [obsIdx0, obsIdx1, Fin.ext_iff]

/-- The observable witnessing non-triviality: `diag(λ)` with `λ = ` the indicator of index
`obsIdx1`. At `t = π` its phases are `exp(0) = 1` (index 0) and `exp(iπ) = -1` (index 1). -/
noncomputable def obsLamWitness (hN : 1 < N) : Fin N → ℝ :=
  fun i => if i = obsIdx1 hN then 1 else 0

/-- The time witnessing non-triviality: `t = π`. -/
noncomputable def obsTWitness : ℝ := Real.pi

@[simp] lemma obsPhase_obsLamWitness_zero (hN : 1 < N) :
    obsPhase (obsLamWitness hN) obsTWitness (obsIdx0 hN) = 1 := by
  have : obsLamWitness hN (obsIdx0 hN) = 0 := if_neg (obsIdx0_ne_obsIdx1 hN)
  simp only [obsPhase, this, mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

@[simp] lemma obsPhase_obsLamWitness_one (hN : 1 < N) :
    obsPhase (obsLamWitness hN) obsTWitness (obsIdx1 hN) = -1 := by
  have hl : obsLamWitness hN (obsIdx1 hN) = 1 := if_pos rfl
  simp only [obsPhase, obsTWitness, hl, mul_one]
  rw [show (Complex.I * ((Real.pi : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I by
        ring,
    Complex.exp_pi_mul_I]

/-- The `|0⟩ + |1⟩` superposition vector — a non-eigenvector of every diagonal phase
flow (its two populated coordinates differ in phase under `obsLamWitness`/`obsTWitness`). -/
noncomputable def obsWitnessVec (hN : 1 < N) : EuclideanSpace ℂ (Fin N) :=
  EuclideanSpace.single (obsIdx0 hN) (1 : ℂ) + EuclideanSpace.single (obsIdx1 hN) (1 : ℂ)

lemma obsWitnessVec_apply_zero (hN : 1 < N) : (obsWitnessVec hN) (obsIdx0 hN) = 1 := by
  simp only [obsWitnessVec, PiLp.add_apply, PiLp.single_apply,
    if_neg (obsIdx0_ne_obsIdx1 hN), add_zero, if_true]

lemma obsWitnessVec_apply_one (hN : 1 < N) :
    (obsWitnessVec hN) (obsIdx1 hN) = 1 := by
  simp only [obsWitnessVec, PiLp.add_apply, PiLp.single_apply,
    if_neg (obsIdx0_ne_obsIdx1 hN).symm, zero_add, if_true]

lemma obsWitnessVec_ne_zero (hN : 1 < N) : obsWitnessVec hN ≠ 0 := fun h => by
  have := obsWitnessVec_apply_zero hN
  rw [h] at this
  simp at this

/-- **The observable's flow is genuinely not the identity** (for `1 < N`). Because `obsFlow`
is a *diagonal phase* flow, every computational basis ray `[eᵢ]` is an eigenvector and is
**fixed** — so the witness must be a **superposition**. The `|0⟩ + |1⟩` ray
`[obsWitnessVec]` is moved: under `obsLamWitness`/`obsTWitness` its coordinates `0` and
`⟨1,hN⟩` acquire the distinct phases `1` and `-1`, so the image coordinate vector `(1,-1,…)`
is non-collinear with `(1,1,…)`. Any `c • v = (phase·v)` forces `c = 1` at coordinate `0` and
`c = -1` at coordinate `⟨1,hN⟩`, a contradiction. Mirrors `kFlow_ne_id`'s role as the named
non-triviality witness. -/
theorem obsFlow_ne_id (hN : 1 < N) :
    obsFlow (N := N) (obsLamWitness hN) obsTWitness ≠ id := by
  haveI : NeZero N := ⟨by omega⟩
  intro hid
  set v := obsWitnessVec hN with hv
  have hv0 : v ≠ 0 := obsWitnessVec_ne_zero hN
  -- The flow on the ray `[v]`, written as `mk` of the diagonal-phase image.
  have hmove : obsFlow (obsLamWitness hN) obsTWitness (Projectivization.mk ℂ v hv0)
      = Projectivization.mk ℂ
          ((Matrix.toEuclideanLin (obsUnitary (obsLamWitness hN) obsTWitness).val) v)
          (obsUnitary_apply_ne_zero _ _ hv0) := by
    rw [obsFlow]
    exact smul_mk_eq_mk _ _ _
  -- The flow fixes the ray (`Φ = id`), contradicting non-collinearity.
  rw [hid, id_eq] at hmove
  rw [eq_comm, Projectivization.mk_eq_mk_iff'] at hmove
  obtain ⟨c, hc⟩ := hmove
  -- Evaluate `c • v = phase · v` at coordinate `obsIdx0`: `c = 1`.
  have hc0 := congrFun (congrArg WithLp.ofLp hc) (obsIdx0 hN)
  rw [obsUnitary_toEuclideanLin_apply, obsPhase_obsLamWitness_zero,
    obsWitnessVec_apply_zero] at hc0
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, one_mul] at hc0
  rw [obsWitnessVec_apply_zero, mul_one] at hc0
  -- Evaluate at coordinate `obsIdx1`: `c = -1`.
  have hc1 := congrFun (congrArg WithLp.ofLp hc) (obsIdx1 hN)
  rw [obsUnitary_toEuclideanLin_apply, obsPhase_obsLamWitness_one,
    obsWitnessVec_apply_one] at hc1
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at hc1
  rw [obsWitnessVec_apply_one, mul_one, mul_one] at hc1
  -- `1 = c = -1`, contradiction.
  rw [hc0] at hc1
  exact (by norm_num : (1 : ℂ) ≠ -1) hc1

/-- **Headline: the Born weights are conserved along the observable's flow.** The moment-map
coordinates (= Born weights, `momentMap_mk_eq_inner_sq`) are invariant under `obsFlow`:
`momentMap (obsFlow λ t p) i = momentMap p i`. The measured observable's own dynamics has the
Born weights as its constants of motion. -/
theorem momentMap_obsFlow [NeZero N] (lam : Fin N → ℝ) (t : ℝ) (p : CPN N) (i : Fin N) :
    momentMap (obsFlow lam t p) i = momentMap p i := by
  have hrep : obsFlow lam t p
      = Projectivization.mk ℂ ((Matrix.toEuclideanLin (obsUnitary lam t).val) p.rep)
          (obsUnitary_apply_ne_zero lam t p.rep_nonzero) := by
    rw [obsFlow]
    conv_lhs => rw [← Projectivization.mk_rep p]
    exact smul_mk_eq_mk _ _ _
  rw [hrep, momentMap_mk]
  unfold momentMap
  congr 1
  · rw [obsUnitary_toEuclideanLin_apply, norm_mul, obsPhase_norm, one_mul]
  · rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [obsUnitary_toEuclideanLin_apply, norm_mul, obsPhase_norm, one_mul]

/-! ## D1c-2: the concrete base `SectorData` with a physically-meaningful `Φ = obsFlow ≠ id`

D1c-1 (`LF4/KahlerFlow.lean`, `kSectorDataFlow`) discharged the "`Φ = id` in the
concrete Kähler instance" debt with a *free* `T²`-fibre translation `kFlow`: a
genuine measure-preserving `Φ ≠ id`, but dynamically trivial — a fibre shift that
acts as the identity on the actual projective state space. This block is the
**physically-meaningful** strengthening: it rebuilds the base instance
`cpSectorData` (`Σ = P = ℂℙ^{N-1}`, `μL = fubiniStudyMeasure`, `π = id`) with
`Φ := obsFlow lam t`, the **Hamiltonian flow `t ↦ exp(i t Â)` of a diagonal
observable `Â = diag(λ)` acting on the Fubini–Study Kähler base** by
`obsFlow lam t [ψ] = [exp(i t Â) ψ]`. This is dynamics on the real projective
state space, not a trivial fibre shift.

Only the three flow-related `OnticSetup` fields change (`Φ`, `hΦ_pres`, and the
derived `measurable_Φ`); `μL`, `Ω0`, and their hypotheses are reused verbatim from
`cpOnticSetup`. The `SectorData` `G = U(N)`-action fields (`measurable_smul_σ`,
`measurable_smul_P`, `hμL_inv`, `hπ_equiv`) are about the `U(N)`-action and
`π = id`, never about `Φ`, so they are reused verbatim from `cpSectorData`
(`hμL_inv` reads `toOntic.μL`, which is unchanged `= fubiniStudyMeasure p₀`).

**Strictly stronger than D1c-1.** `kFlow` is a free `T²`-fibre translation
(`kFlow_preserves_rays`: it fixes every projective ray `[ψ]`); `obsFlow` is a
Hamiltonian flow *on* the projective base, moving superposition rays
(`obsFlow_ne_id`: the `|0⟩+|1⟩` ray acquires distinct coordinate phases `1`, `-1`).
So D1c-2 gives the concrete base instance genuine physical dynamics on the actual
Kähler state space.

**Honest scope.** `obsFlow` is a *single observable's* periodic phase flow. It is
**not** the de-isolation / measurement flow `Φ_vN` (the dilated-space dynamics of
LF5, the fuller deferred D1c content), and it is **not** ergodic / mixing (a
periodic phase flow cannot be). **A5 is untouched** — D1c is
necessary-but-not-sufficient for deriving the sector + Fubini–Study typicality from
the dynamics: A5 additionally needs the flow ergodic / mixing to *force* `μFS`,
which `obsFlow` is not. So D1c-2 supplies the concrete base instance with genuine
physical dynamics; the A5 ergodicity content remains the open gap. -/

variable [NeZero N]

/-- The base `OnticSetup` with the **physically-meaningful** flow `Φ := obsFlow lam t`.
Identical to `cpOnticSetup p₀` except for the three flow fields: `Φ` is the
observable's Hamiltonian flow on `ℂℙ^{N-1}`, `hΦ_pres` is
`obsFlow_measurePreserving` (FS-invariance, genuine Liouville content, not
`MeasurePreserving.id`). `μL`, `Ω0`, and their hypotheses are reused. -/
noncomputable def cpOnticSetupFlow (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    CSD.LF1.OnticSetup (CPN N) where
  μL := ⟨fubiniStudyMeasure p₀, inferInstance⟩
  Φ := obsFlow lam t
  hΦ_pres := obsFlow_measurePreserving lam t p₀
  Ω0 := Set.univ
  hΩ0_meas := MeasurableSet.univ
  hΩ0_nonzero := by
    show (fubiniStudyMeasure p₀) Set.univ ≠ 0
    rw [measure_univ]; exact one_ne_zero

/-- **The concrete base `SectorData` carrying a physically-meaningful
measure-preserving `Φ ≠ id`.** Identical to `cpSectorData p₀` except its
underlying ontic data is `cpOnticSetupFlow p₀ lam t` (so `Φ = obsFlow lam t`, the
observable's Hamiltonian flow on the Fubini–Study base). The `G = U(N)` action
fields are reused verbatim from `cpSectorData`; none of them mention `Φ`. -/
noncomputable def cpSectorDataFlow (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    CSD.LF2.SectorData (CPN N) (CPN N) (Matrix.unitaryGroup (Fin N) ℂ) where
  toOntic := cpOnticSetupFlow p₀ lam t
  π := id
  measurable_π := measurable_id
  measurable_smul_σ := (cpSectorData p₀).measurable_smul_σ
  measurable_smul_P := (cpSectorData p₀).measurable_smul_P
  hμL_inv := (cpSectorData p₀).hμL_inv
  hπ_equiv := (cpSectorData p₀).hπ_equiv

/-- The instance's flow is exactly `obsFlow lam t` (definitional). -/
@[simp] lemma cpSectorDataFlow_phi (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    (cpSectorDataFlow p₀ lam t).toOntic.Φ = obsFlow lam t := rfl

/-- **D1c-2 headline.** The concrete base `SectorData` genuinely carries a
*physically-meaningful* `Φ ≠ id`: the observable's Hamiltonian flow `exp(i t Â)`
on the Fubini–Study Kähler base `ℂℙ^{N-1}`. Strictly stronger than D1c-1's free
`T²`-fibre translation (`kSectorDataFlow_phi_ne_id`), which fixes every projective
ray. Reuses `obsFlow_ne_id` (witnesses `obsLamWitness hN`, `obsTWitness`). -/
theorem cpSectorDataFlow_phi_ne_id (p₀ : CPN N) (hN : 1 < N) :
    (cpSectorDataFlow p₀ (obsLamWitness hN) obsTWitness).toOntic.Φ ≠ id :=
  obsFlow_ne_id hN

/-- The instance's flow is measure-preserving for the Fubini–Study / Liouville
volume `fubiniStudyMeasure p₀` (the genuine `hΦ_pres` content surfaced on the
`SectorData`). -/
theorem cpSectorDataFlow_phi_measurePreserving (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    MeasureTheory.MeasurePreserving (cpSectorDataFlow p₀ lam t).toOntic.Φ
      (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  obsFlow_measurePreserving lam t p₀

/-- **Non-vacuity link to LF1.** The LF1 deterministic-typicality theorem is
non-vacuous on `cpSectorDataFlow`: for i.i.d. preparation draws, the empirical
frequency of a measurable outcome region `O` evaluated on the states evolved by
the **instance's own flow** `(cpSectorDataFlow p₀ lam t).toOntic.Φ` converges
almost surely to the ontic volume ratio `(fubiniStudyMeasure p₀ O).toReal`. The
moving flow that pins the limit is the `SectorData`'s own physically-meaningful
`Φ = obsFlow lam t ≠ id`, and `obsFlow_measurePreserving` is what makes
`law(obsFlow ∘ sampleₙ) = fubiniStudyMeasure p₀`. LF1's `freq_tendsto_of_iid`
is cited, not re-proved (the same route as `kSectorDataFlow_frequency_convergence`). -/
theorem cpSectorDataFlow_frequency_convergence
    (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (sample : ℕ → Ω → CPN N) (hsample : ∀ n, Measurable (sample n))
    (hlaw : ∀ n, Measure.map (sample n) Pr = fubiniStudyMeasure p₀)
    {O : Set (CPN N)} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            (((cpSectorDataFlow p₀ lam t).toOntic.Φ ∘ sample n) ⁻¹' O)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                (((cpSectorDataFlow p₀ lam t).toOntic.Φ ∘ sample i) ⁻¹' O)
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (fubiniStudyMeasure p₀ O).toReal) := by
  have hmp := cpSectorDataFlow_phi_measurePreserving p₀ lam t
  -- Measure preservation is load-bearing: it pins the law of the evolved trials.
  have hlaw' : ∀ n,
      Measure.map ((cpSectorDataFlow p₀ lam t).toOntic.Φ ∘ sample n) Pr
        = fubiniStudyMeasure p₀ := fun n => by
    rw [← Measure.map_map hmp.measurable (hsample n), hlaw n, hmp.map_eq]
  exact LF1.freq_tendsto_of_iid (fun n => hmp.measurable.comp (hsample n)) hlaw' hO hindep

end LF4
end CSD
