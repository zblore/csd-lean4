/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.AmplitudeAmplification
public import CsdLean4.Mathlib.QuantumInfo.JointRegister
public import CsdLean4.Mathlib.QuantumInfo.PhaseEstimation

/-!
# Amplitude estimation: the kickback marginal and the per-index success bound (BHMT Thm 12)

**Category:** 1-Mathlib (CSD-free).

**Glossary:** https://glossary.constraintsurfacedynamics.com/amplitude-estimation/
Plain-language, CSD-role and formal statements of amplitude estimation, with this module as
its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

The assembly of the three prepared layers (plan `specs/amplitude-amplification-plan.md`,
AA-5b): phase estimation run on the amplification step `Q` estimates the rotation angle `θ`,
hence the amplitude `a = sin²θ`.

* **The kickback state** `kickbackState T φ G ψ = (1/√T) ∑_x |x⟩ ⊗ Qˣψ` — the joint state a
  controlled-`Q` ladder prepares.
* ★ **The two-branch phase form** (`kickbackState_ampState`): on the rotation plane the
  kickback state is EXACTLY a sum of two product states,
  `c₊·(phaseStateR (θ/π)) ⊗ v₊ + c₋·(phaseStateR (−θ/π)) ⊗ v₋`, with orthogonal eigenvector
  companions `v±` and branch coefficients of modulus `1/2` — the eigen-decomposition of
  `ampState` threaded through the iterated eigen-action.
* ★ **The exact marginal** (`amplitude_estimation_marginal`): after the counting-register
  inverse QFT, the Born marginal at every index `c` is the **half-half mixture**
  `(P₊(c) + P₋(c))/2` of the two single-phase counting distributions — every cross-term dead
  against `⟪v₊, v₋⟫ = 0` (`probLeft_add_tensor_orthogonal`).
* ★★ **The success bound** (`amplitude_estimation`): at any index `c` within the
  closest-index window of `θ/π` (the hypothesis of `phase_estimation_lower_bound`), the
  marginal carries at least `2/π²`.
* ★ **The accuracy reading** (`amplitude_estimation_close`): any index in that window yields
  the estimate `ã = sin²(πc/T)` with `|ã − a| ≤ π√(a(1−a))/T + π²/(4T²)` — the AA-5a error
  algebra at `ε = π/(2T)`. (BHMT state `2π√(a(1−a))/T + π²/T²` from `ε = π/T`; the
  closest-index window gives the sharper constant.)

## Honest scope

The `2/π²` is the **single-branch, single-index** bound: the `+` branch's `4/π²` halves
against the branch weight, and the `−` branch's contribution at the same index is kept only as
`≥ 0`. BHMT's `8/π²` (Thm 12 via their Thm 11) counts both rounding directions of both
branches; that strengthening is `Fin` wraparound bookkeeping on the mirror index `T − c` and
is not attempted here — the exact marginal (`amplitude_estimation_marginal`) is stated in full,
so the refinement is downstream arithmetic on a closed form, the same posture as
`Grover.lean`'s deferrals. Query counting is by rounds of the abstract step; no controlled-gate
decomposition is claimed. The construction takes the rotation-plane data (`g`, `b`, `θ`) as
input — the plane exists for any state with `0 < goodProb < 1` (`ampState_decomposition` in
`AmplitudeAmplification.lean`).
-/

@[expose] public section

open scoped ComplexConjugate
open scoped Matrix

namespace QuantumInfo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (T : ℕ) [NeZero T]

/-! ## The kickback state -/

/-- The **phase-kickback state** of the amplification step: `(1/√T) ∑_x |x⟩ ⊗ Qˣψ`, the joint
counting/work state a controlled-`Q` ladder prepares from `|counting uniform⟩ ⊗ ψ`. -/
noncomputable def kickbackState (φ : EuclideanSpace ℂ ι) (G : Finset ι)
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (Fin T × ι) :=
  (Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T, tensorState (basisState x) ((ampStep φ G)^[(x : ℕ)] ψ)

/-- The `+` branch coefficient `(−i/2)e^{iθ}`. -/
noncomputable def branchPlus (θ : ℝ) : ℂ :=
  -Complex.I / 2 * Complex.exp ((θ : ℝ) * Complex.I)

/-- The `−` branch coefficient `(i/2)e^{−iθ}`. -/
noncomputable def branchMinus (θ : ℝ) : ℂ :=
  Complex.I / 2 * Complex.exp ((-θ : ℝ) * Complex.I)

omit [Fintype ι] [DecidableEq ι] [NeZero T] in
lemma norm_branchPlus (θ : ℝ) : ‖branchPlus θ‖ = 1 / 2 := by
  rw [branchPlus, norm_mul, Complex.norm_exp]
  simp [Complex.norm_I]

omit [Fintype ι] [DecidableEq ι] [NeZero T] in
lemma norm_branchMinus (θ : ℝ) : ‖branchMinus θ‖ = 1 / 2 := by
  rw [branchMinus, norm_mul, Complex.norm_exp]
  simp [Complex.norm_I]

variable {G : Finset ι} {g b : EuclideanSpace ℂ ι}

omit [NeZero T] in
/-- ★ **The two-branch phase form of the kickback state.** On the rotation plane, the kickback
state of `Q = ampStep (ampState θ) G` on `ψ = ampState θ` is exactly a sum of two product
states: each eigen-branch picks up the geometric phase `e^{±2ixθ}`, which is the phase state
`phaseStateR T (±θ/π)` on the counting register. -/
theorem kickbackState_ampState (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    kickbackState T (ampState g b θ) G (ampState g b θ)
      = tensorState (branchPlus θ • phaseStateR T (θ / Real.pi)) (eigenPlus g b)
        + tensorState (branchMinus θ • phaseStateR T (-(θ / Real.pi))) (eigenMinus g b) := by
  have hiter : ∀ x : Fin T, (ampStep (ampState g b θ) G)^[(x : ℕ)] (ampState g b θ)
      = (branchPlus θ * Complex.exp ((2 * (x : ℕ) * θ : ℝ) * Complex.I)) • eigenPlus g b
        + (branchMinus θ * Complex.exp ((-(2 * (x : ℕ) * θ) : ℝ) * Complex.I))
            • eigenMinus g b := by
    intro x
    rw [congrArg ((ampStep (ampState g b θ) G)^[(x : ℕ)]) (ampState_eq_eigen g b θ),
      ampStep_iterate_add, ampStep_iterate_smul, ampStep_iterate_smul,
      ampStep_iterate_eigenPlus hgg hbb hgb hgsupp hbsupp θ (x : ℕ),
      ampStep_iterate_eigenMinus hgg hbb hgb hgsupp hbsupp θ (x : ℕ),
      smul_smul, smul_smul, branchPlus, branchMinus]
  have hsum : ∀ x : Fin T,
      tensorState (basisState x) ((ampStep (ampState g b θ) G)^[(x : ℕ)] (ampState g b θ))
        = tensorState ((branchPlus θ * Complex.exp ((2 * (x : ℕ) * θ : ℝ) * Complex.I))
              • basisState x) (eigenPlus g b)
          + tensorState ((branchMinus θ * Complex.exp ((-(2 * (x : ℕ) * θ) : ℝ) * Complex.I))
              • basisState x) (eigenMinus g b) := by
    intro x
    rw [hiter x, tensorState_add_right, tensorState_smul_right, tensorState_smul_right,
      ← tensorState_smul_left, ← tensorState_smul_left]
  rw [kickbackState, Finset.sum_congr rfl fun x _ => hsum x, Finset.sum_add_distrib,
    smul_add, ← tensorState_sum_left, ← tensorState_sum_left, ← tensorState_smul_left,
    ← tensorState_smul_left]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2
  · -- (√T)⁻¹ • ∑ x (c₊ e^{2ixθ}) • |x⟩ = c₊ • phaseStateR T (θ/π)
    rw [phaseStateR, smul_comm (branchPlus θ) ((Real.sqrt T : ℂ)⁻¹)]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul,
      show ((2 * (x : ℕ) * θ : ℝ) : ℂ) * Complex.I
          = 2 * (Real.pi : ℂ) * Complex.I * ((θ / Real.pi : ℝ) : ℂ) * ((x : ℕ) : ℂ) from by
        push_cast
        field_simp]
  · rw [phaseStateR, smul_comm (branchMinus θ) ((Real.sqrt T : ℂ)⁻¹)]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul,
      show ((-(2 * (x : ℕ) * θ) : ℝ) : ℂ) * Complex.I
          = 2 * (Real.pi : ℂ) * Complex.I * ((-(θ / Real.pi) : ℝ) : ℂ) * ((x : ℕ) : ℂ) from by
        push_cast
        field_simp]

/-! ## The exact counting marginal, and the success bound -/

omit [DecidableEq ι] [NeZero T] in
/-- The inverse QFT as the first-factor kernel: definitional bridge. -/
lemma toEuclideanLin_qftInv (ψ : EuclideanSpace ℂ (Fin T)) :
    Matrix.toEuclideanLin (qftMatrix T)ᴴ ψ = applyQFTinv T ψ := rfl

omit [NeZero T] in
/-- ★ **The exact counting marginal of the processed kickback state:** at every index `c`, the
Born marginal after the counting-register inverse QFT is the **half-half mixture** of the two
single-phase distributions. No cross-terms: the eigenvector companions are orthogonal. -/
theorem amplitude_estimation_marginal (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (c : Fin T) :
    probLeft (matrixLeft (qftMatrix T)ᴴ
        (kickbackState T (ampState g b θ) G (ampState g b θ))) c
      = (prob (applyQFTinv T (phaseStateR T (θ / Real.pi))) c
          + prob (applyQFTinv T (phaseStateR T (-(θ / Real.pi)))) c) / 2 := by
  rw [kickbackState_ampState T hgg hbb hgb hgsupp hbsupp θ, matrixLeft_add,
    matrixLeft_tensorState, matrixLeft_tensorState, LinearMap.map_smul, LinearMap.map_smul,
    toEuclideanLin_qftInv, toEuclideanLin_qftInv,
    probLeft_add_tensor_orthogonal _ _ _ _ (inner_eigenPlus_eigenMinus hgg hbb hgb) c,
    sum_sq_eigenPlus hgg hbb hgb, sum_sq_eigenMinus hgg hbb hgb,
    WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, norm_mul, norm_mul, norm_branchPlus, norm_branchMinus, prob, prob]
  ring

/-- ★★ **The amplitude-estimation success bound (BHMT Thm 12, per-index form).** At any
counting index `c` within the closest-index window of `θ/π`, the measured marginal carries at
least `2/π²`: the `+` branch's `4/π²` phase-estimation weight, halved by the branch
probability. -/
theorem amplitude_estimation (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (c : Fin T)
    (hclose : |θ / Real.pi - (c : ℝ) / T| ≤ 1 / (2 * T)) :
    2 / Real.pi ^ 2 ≤ probLeft (matrixLeft (qftMatrix T)ᴴ
        (kickbackState T (ampState g b θ) G (ampState g b θ))) c := by
  rw [amplitude_estimation_marginal T hgg hbb hgb hgsupp hbsupp θ c]
  have h1 := phase_estimation_lower_bound T (θ / Real.pi) c hclose
  have h2 : 0 ≤ prob (applyQFTinv T (phaseStateR T (-(θ / Real.pi)))) c := by
    rw [prob]
    positivity
  have h3 := add_le_add h1 h2
  calc 2 / Real.pi ^ 2 = (4 / Real.pi ^ 2 + 0) / 2 := by ring
    _ ≤ (prob (applyQFTinv T (phaseStateR T (θ / Real.pi))) c
          + prob (applyQFTinv T (phaseStateR T (-(θ / Real.pi)))) c) / 2 := by linarith

/-- ★ **The accuracy of the estimate (BHMT Lemma 7 instantiated).** Any index in the
closest-index window yields the amplitude estimate `ã = sin²(πc/T)` with
`|ã − a| ≤ π√(a(1−a))/T + π²/(4T²)`. -/
theorem amplitude_estimation_close {a : ℝ} (ha0 : 0 ≤ a)
    {θ : ℝ} (hθ : Real.sin θ = Real.sqrt a) (hθc : Real.cos θ = Real.sqrt (1 - a))
    (c : Fin T) (hclose : |θ / Real.pi - (c : ℝ) / T| ≤ 1 / (2 * T)) :
    |Real.sin (Real.pi * c / T) ^ 2 - a|
      ≤ Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / (4 * T ^ 2) := by
  have hT : (0 : ℝ) < T := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hδ : |Real.pi * c / T - θ| ≤ Real.pi / (2 * T) := by
    have hstep : |Real.pi * c / T - θ| = Real.pi * |θ / Real.pi - (c : ℝ) / T| := by
      rw [abs_sub_comm,
        show θ - Real.pi * c / T = Real.pi * (θ / Real.pi - (c : ℝ) / T) from by
          field_simp,
        abs_mul, abs_of_pos Real.pi_pos]
    rw [hstep]
    calc Real.pi * |θ / Real.pi - (c : ℝ) / T| ≤ Real.pi * (1 / (2 * T)) :=
          mul_le_mul_of_nonneg_left hclose Real.pi_pos.le
      _ = Real.pi / (2 * T) := by ring
  have h := amplitude_estimation_error ha0 hθ hθc hδ
  calc |Real.sin (Real.pi * c / T) ^ 2 - a|
      ≤ 2 * Real.sqrt (a * (1 - a)) * (Real.pi / (2 * T)) + (Real.pi / (2 * T)) ^ 2 := h
    _ = Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / (4 * T ^ 2) := by
        field_simp
        ring

end QuantumInfo
