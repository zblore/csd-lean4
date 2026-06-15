import CsdLean4.LF4.MomentMap
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive

/-!
# The measured observable's Hamiltonian flow on `Σ = ℂℙ^{N-1}`

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
Caveat (honest): the `Φ ≠ id` claim is true for `obsFlow` but is **not separately witnessed
here** — unlike `kFlow`, which carries an explicit `kFlow_ne_id`; an analogous
`obsFlow_ne_id` would close the gap and is cheap follow-up. What is *not* here is the
measurement **event** — the flow conserves the populations (a non-disturbing / compatible
measurement at the ontic level), it does not carry microstates into pointer regions and
commit an outcome. That measurement-dynamics content is now built in the **LF5 layer**
(`CsdLean4/LF5/`, single-system projective tier complete: `measurementFlow ≠ id`,
`measurement_flow_born_frequency`, the per-microstate outcome function `vnPointerOutcome`);
the deeper D1 strata (entangled de-isolation, instance-level dynamics) remain open.
-/

open scoped LinearAlgebra.Projectivization
open Matrix MeasureTheory Matrix.UnitaryGroup

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
  rw [obsUnitary_val, Matrix.toEuclideanLin_apply]
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

end LF4
end CSD
