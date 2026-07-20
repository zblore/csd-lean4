import CsdLean4.LF4.SingletKahler
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.ContextMap

/-!
# LF4 §14.2 at N = 4: two-qubit Pauli observables on the singlet preparation

**Category:** 3-Local (LF4 §14.2 extension to N = 4 — two-qubit Pauli
spectral decomposition on the singlet `Σ = ℂℙ³ × T²` instance).

Lifts the §14.2 single-qubit Pauli pattern (`SingleQubitKahler.lean`,
`pauliDot_observable_correspondence`) to the **three two-qubit Pauli
forms** on the singlet preparation:

- `σ·a ⊗ I` (left wing)  — `sigmaDotLeftOntic`,
- `I ⊗ σ·b` (right wing) — `sigmaDotRightOntic`,
- `σ·a ⊗ σ·b` (joint)    — `sigmaDotJointOntic`.

Each observable has eigenvalues `±1` with rank-2 eigenspaces in the
4-dimensional 2-qubit space. The spectral decomposition over the
existing four singlet sectors `kRegion ctx s t` gives the ontic
counterpart as an eigenvalue-weighted sum of sector indicators.

## §14.2 correspondence for the three forms

| Form                | Eigenvalue weight on sector `(s,t)` | Integral against `kMuPsi` | Singlet expectation         |
|---------------------|-------------------------------------|----------------------------|-----------------------------|
| `σ·a ⊗ I`           | `s.val`                             | `0`                        | `0`                         |
| `I ⊗ σ·b`           | `t.val`                             | `0`                        | `0`                         |
| `σ·a ⊗ σ·b`         | `s.val · t.val`                     | `−a·b`                     | `−a·b`                      |

Both sides of each correspondence theorem land on the same value via
independent routes:
- **Hilbert side**: the existing LF3 singlet-expectation theorems
  (`singlet_left/right_pauli_expectation_zero`, `singlet_pauli_correlation`).
- **Ontic side**: sector-marginal/correlation identities from LF3
  (`marginal_a_eq_half`, `marginal_b_eq_half`,
  `context_correlation_eq_neg_dot`), integrated through
  `kMuPsi_kRegion` (the singlet sector carving identity).

## Why this gives Mermin–Peres for free

Each of the nine Mermin–Peres 3×3-grid observables is an instance of
one of the three forms (`σ_a ⊗ I`, `I ⊗ σ_b`, or `σ_a ⊗ σ_b` for
appropriate axes). The §14.2 correspondence theorems below give the
per-observable Hilbert ↔ ontic match. Combined with the existing MP
combinatorial impossibility (`Empirical/QM/Contextuality/MerminPeres.lean`'s
`no_lhv_mermin_peres` and `mermin_peres_R0..R2, C0..C2`), the
contextuality proof is now available at the LF3-chain level.

For Hardy, three of the four observables (the single-qubit Paulis on
each side) are instances of `sigmaDotLeft` and `sigmaDotRight`. The
full Hardy joint-frequency lift additionally requires per-Hardy-context
preparations and joint outcome regions; that is a follow-up tranche.

## Tier-2 honesty (unchanged)

The singlet sector regions `kRegion ctx s t` are carved to volume
`P_st ctx.a ctx.b s t` by construction. The §14.2 integration identities
hold because Hilbert and ontic sides equal the same prescribed values
through independent routes. Not a derivation; faithful realisation.

## Axiom posture

Foundational triple only. Reuses `kRegion_measurable`, `kMuPsi_kRegion`
from `SingletKahler.lean`; reuses the LF3 marginal/correlation algebra.
-/

open MeasureTheory Matrix Finset
open CSD.LF3

namespace CSD
namespace LF4

variable (ctx : CSD.LF3.MeasurementContext)

/-! ### Algebraic helpers: sector-weighted `P_st` sums -/

private lemma sum_sign_val : ∑ s : Sign, (s.val : ℝ) = 0 := by
  rw [Sign.sum_univ]
  simp [Sign.val]

private lemma sum_sectorLeft_PSt_eq_zero (a b : DetectorSetting) :
    ∑ st : Sign × Sign, st.1.val * P_st a b st.1 st.2 = 0 := by
  rw [Fintype.sum_prod_type]
  -- Goal: ∑ s, ∑ t, s.val * P_st a b s t = 0
  simp_rw [← Finset.mul_sum, marginal_a_eq_half a b]
  rw [← Finset.sum_mul, sum_sign_val, zero_mul]

private lemma sum_sectorRight_PSt_eq_zero (a b : DetectorSetting) :
    ∑ st : Sign × Sign, st.2.val * P_st a b st.1 st.2 = 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  -- Goal: ∑ t, ∑ s, t.val * P_st a b s t = 0
  simp_rw [← Finset.mul_sum, marginal_b_eq_half a b]
  rw [← Finset.sum_mul, sum_sign_val, zero_mul]

/-! ### The three §14.2 ontic counterparts -/

/-- Ontic counterpart of `σ·a ⊗ I` on the singlet: signed-indicator over
the four singlet sectors, weighted by the **left** sign of each sector
`(s, t)`. -/
noncomputable def sigmaDotLeftOntic (σ : KSigma 4) : ℝ :=
  ∑ st : Sign × Sign,
    st.1.val * Set.indicator (kRegion ctx st.1 st.2) (fun _ => (1 : ℝ)) σ

/-- Ontic counterpart of `I ⊗ σ·b` on the singlet: signed by the
**right** sign of each sector. -/
noncomputable def sigmaDotRightOntic (σ : KSigma 4) : ℝ :=
  ∑ st : Sign × Sign,
    st.2.val * Set.indicator (kRegion ctx st.1 st.2) (fun _ => (1 : ℝ)) σ

/-- Ontic counterpart of `σ·a ⊗ σ·b` on the singlet: signed by the
**product** of the sector signs. -/
noncomputable def sigmaDotJointOntic (σ : KSigma 4) : ℝ :=
  ∑ st : Sign × Sign,
    st.1.val * st.2.val *
      Set.indicator (kRegion ctx st.1 st.2) (fun _ => (1 : ℝ)) σ

/-! ### Integration identities (§14.2 ontic-side values) -/

/-- For each sector, the indicator of `kRegion ctx s t` is integrable
against `kMuPsi`. -/
private lemma indicator_kRegion_integrable (s t : Sign) :
    Integrable
      (Set.indicator (kRegion ctx s t) (fun _ : KSigma 4 => (1 : ℝ))) kMuPsi :=
  (integrable_const (1 : ℝ)).indicator (kRegion_measurable ctx s t)

/-- The integral of a sector-weighted indicator sum is the corresponding
`P_st`-weighted scalar sum. The shared computational step underlying
all three §14.2 forms. -/
private lemma weighted_indicator_sum_integral (w : Sign × Sign → ℝ) :
    ∫ σ, (∑ st : Sign × Sign,
            w st * Set.indicator (kRegion ctx st.1 st.2)
              (fun _ => (1 : ℝ)) σ) ∂kMuPsi
      = ∑ st : Sign × Sign, w st * P_st ctx.a ctx.b st.1 st.2 := by
  rw [integral_finsetSum _
        (fun st _ => (indicator_kRegion_integrable ctx st.1 st.2).const_mul (w st))]
  congr 1
  ext st
  rw [integral_const_mul, integral_indicator (kRegion_measurable ctx st.1 st.2),
      setIntegral_const, smul_eq_mul, Measure.real, kMuPsi_kRegion,
      ENNReal.toReal_ofReal (P_st_nonneg ctx.a ctx.b st.1 st.2), mul_one]

/-- **`σ·a ⊗ I` ontic integral.** Vanishes by the left marginal `Σ_t P_st = 1/2`
and `Σ_s s.val = 0`. -/
lemma sigmaDotLeftOntic_integral :
    ∫ σ, sigmaDotLeftOntic ctx σ ∂kMuPsi = 0 := by
  unfold sigmaDotLeftOntic
  rw [weighted_indicator_sum_integral ctx (fun st => (st.1.val : ℝ))]
  exact sum_sectorLeft_PSt_eq_zero ctx.a ctx.b

/-- **`I ⊗ σ·b` ontic integral.** Vanishes by the right marginal. -/
lemma sigmaDotRightOntic_integral :
    ∫ σ, sigmaDotRightOntic ctx σ ∂kMuPsi = 0 := by
  unfold sigmaDotRightOntic
  rw [weighted_indicator_sum_integral ctx (fun st => (st.2.val : ℝ))]
  exact sum_sectorRight_PSt_eq_zero ctx.a ctx.b

/-- **`σ·a ⊗ σ·b` ontic integral.** Equals `−a·b` via the LF3 singlet
correlation `context_correlation_eq_neg_dot`. -/
lemma sigmaDotJointOntic_integral :
    ∫ σ, sigmaDotJointOntic ctx σ ∂kMuPsi = -(dotR ctx.a ctx.b) := by
  unfold sigmaDotJointOntic
  -- Rearrange `s.val * t.val * indicator = (s.val * t.val) * indicator`.
  have h_assoc :
      (fun σ => ∑ st : Sign × Sign,
        st.1.val * st.2.val *
          Set.indicator (kRegion ctx st.1 st.2) (fun _ : KSigma 4 => (1 : ℝ)) σ)
      = (fun σ => ∑ st : Sign × Sign,
        (st.1.val * st.2.val) *
          Set.indicator (kRegion ctx st.1 st.2) (fun _ : KSigma 4 => (1 : ℝ)) σ) := rfl
  rw [show (∫ σ, ∑ st : Sign × Sign,
              st.1.val * st.2.val *
                Set.indicator (kRegion ctx st.1 st.2)
                  (fun _ : KSigma 4 => (1 : ℝ)) σ ∂kMuPsi)
        = (∫ σ, ∑ st : Sign × Sign,
              (st.1.val * st.2.val) *
                Set.indicator (kRegion ctx st.1 st.2)
                  (fun _ : KSigma 4 => (1 : ℝ)) σ ∂kMuPsi) from by rfl]
  rw [weighted_indicator_sum_integral ctx (fun st => (st.1.val * st.2.val : ℝ))]
  exact context_correlation_eq_neg_dot ctx

/-! ### Observable correspondence theorems (§14.2 at N = 4) -/

/-- **§14.2 observable correspondence for `σ·a ⊗ I` on the singlet.** Both
sides equal `0`: the Hilbert side via `singlet_left_pauli_expectation_zero`,
the ontic side via `sigmaDotLeftOntic_integral`. -/
theorem sigmaDotLeft_observable_correspondence :
    expectation (sigmaDotLeft ctx.a)
      = ((∫ σ, sigmaDotLeftOntic ctx σ ∂kMuPsi : ℝ) : ℂ) := by
  rw [singlet_left_pauli_expectation_zero, sigmaDotLeftOntic_integral]
  norm_cast

/-- **§14.2 observable correspondence for `I ⊗ σ·b` on the singlet.** -/
theorem sigmaDotRight_observable_correspondence :
    expectation (sigmaDotRight ctx.b)
      = ((∫ σ, sigmaDotRightOntic ctx σ ∂kMuPsi : ℝ) : ℂ) := by
  rw [singlet_right_pauli_expectation_zero, sigmaDotRightOntic_integral]
  norm_cast

/-- **§14.2 observable correspondence for `σ·a ⊗ σ·b` on the singlet.** Both
sides equal `−a·b`: the Hilbert side via `singlet_pauli_correlation`, the
ontic side via `sigmaDotJointOntic_integral`. -/
theorem sigmaDotJoint_observable_correspondence :
    expectation (sigmaDotJoint ctx.a ctx.b)
      = ((∫ σ, sigmaDotJointOntic ctx σ ∂kMuPsi : ℝ) : ℂ) := by
  rw [singlet_pauli_correlation, sigmaDotJointOntic_integral]
  unfold dotR
  push_cast
  ring

end LF4
end CSD
