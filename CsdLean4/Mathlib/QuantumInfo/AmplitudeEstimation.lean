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
# Amplitude estimation: the kickback marginal, the success bounds and BHMT's `8/π²`

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

* ★★ **BHMT's literal `8/π²` (their Theorem 11, `k = 1`)** (`amplitude_estimation_bhmt`): with
  `c` the lower of the two grid points straddling `Tθ/π`, the accepted set
  `straddleIndices T c = {c, c + 1, −c, −(c + 1)}` carries at least `8/π²`
  (`amplitude_estimation_straddle`) and every index in it decodes within
  `2π√(a(1−a))/T + π²/T²` (`amplitude_estimation_straddle_close`) — the paper's constants.

## Honest scope

`amplitude_estimation` is the single-branch, single-index `2/π²`. The **mirror section**
doubles it: the `−` branch's distribution is the exact mirror image of the `+` branch's
(`prob_applyQFTinv_phaseStateR_neg`, a conjugation symmetry), so the mirror index `−c` also
carries `2/π²` (`amplitude_estimation_mirror`), both indices yield the **same** estimate
`sin²(πc/T)` (`sin_sq_mirror`), and the pair carries `4/π²` (★ `amplitude_estimation_pair`);
when `c = −c` (only `c = 0`, or `c = T/2` for even `T`) that pair sum double-counts one index —
the bound still holds literally, but the "measure c or −c" reading collapses to a single index
there. The **straddle section** reaches the paper's `8/π²` by counting **both rounding
directions**: the two-index Dirichlet bound `phase_estimation_two_index` (the kernel
inequality `f(δ) + f(δ − 1/T) ≥ 8/π²`, `PhaseEstimation.lean`) on each branch, the accepted set
a `Finset` so that coincidences merge rather than double-count. Query counting is by rounds of
the abstract step; no controlled-gate decomposition is claimed. The construction takes the
rotation-plane data (`g`, `b`, `θ`) as input — the plane exists for any state with
`0 < goodProb < 1` (`ampState_decomposition` in `AmplitudeAmplification.lean`).
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

/-! ## The mirror index: both branches counted

The `−` branch's counting distribution is the exact mirror image of the `+` branch's: negating
the phase and the index conjugates every amplitude. So the mirror index `−c` carries the `−`
branch's `4/π²`, it decodes to the **same** amplitude estimate, and accepting `{c, −c}`
doubles the success bound to `4/π²`. -/

omit [Fintype ι] [DecidableEq ι] [NeZero T] in
/-- The `ℕ`-value of the negated index: `(−c : Fin T) = (T − c) % T`. -/
lemma val_neg_fin (c : Fin T) : ((-c : Fin T) : ℕ) = (T - (c : ℕ)) % T := by
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **The conjugation symmetry:** negating both the phase and the counting index conjugates
the processed amplitude. -/
lemma applyQFTinv_phaseStateR_neg_neg (φ : ℝ) (c : Fin T) :
    applyQFTinv T (phaseStateR T (-φ)) (-c)
      = (starRingEnd ℂ) (applyQFTinv T (phaseStateR T φ) c) := by
  rw [applyQFTinv_phaseStateR_apply, applyQFTinv_phaseStateR_apply, map_mul, map_sum]
  congr 1
  · rw [map_inv₀, map_natCast]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.exp_conj,
      show (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I
            * (↑(φ - ((c : ℕ) : ℝ) / (T : ℝ)) : ℂ) * ↑(x : ℕ))
          = -(2 * ↑Real.pi * Complex.I * (↑(φ - ((c : ℕ) : ℝ) / (T : ℝ)) : ℂ) * ↑(x : ℕ))
        from by
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_natCast]
      ring]
    by_cases hc : c = 0
    · subst hc
      rw [neg_zero]
      congr 1
      simp only [Fin.val_zero]
      push_cast
      ring
    · have hm : ((-c : Fin T) : ℕ) = T - (c : ℕ) := by
        rw [val_neg_fin, Nat.mod_eq_of_lt]
        have h0 : 0 < (c : ℕ) := Nat.pos_of_ne_zero (fun h => hc (Fin.ext h))
        omega
      have hT : ((T : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
      rw [hm,
        show (2 * ↑Real.pi * Complex.I
              * (↑(-φ - ((T - (c : ℕ) : ℕ) : ℝ) / (T : ℝ)) : ℂ) * ↑(x : ℕ))
            = -(2 * ↑Real.pi * Complex.I * (↑(φ - ((c : ℕ) : ℝ) / (T : ℝ)) : ℂ) * ↑(x : ℕ))
              + (-(x : ℕ) : ℤ) * (2 * ↑Real.pi * Complex.I) from by
          push_cast [Nat.cast_sub c.isLt.le]
          have hTc : ((T : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.cast_ne_zero.mpr (NeZero.ne T)
          field_simp
          ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- **The mirror distribution:** the `−` branch at the mirror index equals the `+` branch at
the original index. -/
lemma prob_applyQFTinv_phaseStateR_neg (φ : ℝ) (c : Fin T) :
    prob (applyQFTinv T (phaseStateR T (-φ))) (-c)
      = prob (applyQFTinv T (phaseStateR T φ)) c := by
  rw [prob, prob, applyQFTinv_phaseStateR_neg_neg, RCLike.norm_conj]

omit [Fintype ι] [DecidableEq ι] in
/-- **The mirror index decodes to the same estimate:** `sin²(π·(−c)/T) = sin²(π·c/T)`. -/
lemma sin_sq_mirror (c : Fin T) :
    Real.sin (Real.pi * ((-c : Fin T) : ℕ) / T) ^ 2
      = Real.sin (Real.pi * (c : ℕ) / T) ^ 2 := by
  by_cases hc : c = 0
  · subst hc
    rw [neg_zero]
  · have hm : ((-c : Fin T) : ℕ) = T - (c : ℕ) := by
      rw [val_neg_fin, Nat.mod_eq_of_lt]
      have h0 : 0 < (c : ℕ) := Nat.pos_of_ne_zero (fun h => hc (Fin.ext h))
      omega
    have hT : ((T : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
    rw [hm,
      show Real.pi * ((T - (c : ℕ) : ℕ) : ℝ) / T = Real.pi - Real.pi * ((c : ℕ) : ℝ) / T
        from by
        push_cast [Nat.cast_sub c.isLt.le]
        field_simp,
      Real.sin_pi_sub]

/-- **The mirror index also carries `2/π²`:** under the same closest-index hypothesis for
`θ/π`, the `−` branch concentrates at `−c`. -/
theorem amplitude_estimation_mirror (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (c : Fin T)
    (hclose : |θ / Real.pi - (c : ℝ) / T| ≤ 1 / (2 * T)) :
    2 / Real.pi ^ 2 ≤ probLeft (matrixLeft (qftMatrix T)ᴴ
        (kickbackState T (ampState g b θ) G (ampState g b θ))) (-c) := by
  rw [amplitude_estimation_marginal T hgg hbb hgb hgsupp hbsupp θ (-c)]
  have h1 : 4 / Real.pi ^ 2 ≤ prob (applyQFTinv T (phaseStateR T (-(θ / Real.pi)))) (-c) := by
    rw [prob_applyQFTinv_phaseStateR_neg]
    exact phase_estimation_lower_bound T (θ / Real.pi) c hclose
  have h2 : 0 ≤ prob (applyQFTinv T (phaseStateR T (θ / Real.pi))) (-c) := by
    rw [prob]
    positivity
  calc 2 / Real.pi ^ 2 = (0 + 4 / Real.pi ^ 2) / 2 := by ring
    _ ≤ (prob (applyQFTinv T (phaseStateR T (θ / Real.pi))) (-c)
          + prob (applyQFTinv T (phaseStateR T (-(θ / Real.pi)))) (-c)) / 2 := by
        linarith [add_le_add h2 h1]

/-- ★ **The both-branch success bound (the mirror refinement):** the pair `{c, −c}` — two
indices decoding to the **same** estimate (`sin_sq_mirror`) — jointly carries at least
`4/π²`. When `c = −c` (only `c = 0`, or `c = T/2` for even `T`) the sum double-counts a
single index; the inequality still holds literally. BHMT's `8/π²` counts both rounding
directions: `amplitude_estimation_straddle` below. -/
theorem amplitude_estimation_pair (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (c : Fin T)
    (hclose : |θ / Real.pi - (c : ℝ) / T| ≤ 1 / (2 * T)) :
    4 / Real.pi ^ 2 ≤ probLeft (matrixLeft (qftMatrix T)ᴴ
          (kickbackState T (ampState g b θ) G (ampState g b θ))) c
        + probLeft (matrixLeft (qftMatrix T)ᴴ
          (kickbackState T (ampState g b θ) G (ampState g b θ))) (-c) := by
  have h1 := amplitude_estimation T hgg hbb hgb hgsupp hbsupp θ c hclose
  have h2 := amplitude_estimation_mirror T hgg hbb hgb hgsupp hbsupp θ c hclose
  have h4 : (4 : ℝ) / Real.pi ^ 2 = 2 / Real.pi ^ 2 + 2 / Real.pi ^ 2 := by ring
  rw [h4]
  exact add_le_add h1 h2

/-! ## Both rounding directions: BHMT's literal `8/π²` (Theorem 11, `k = 1`)

`amplitude_estimation_pair` counts one grid point per branch. Counting **both** grid points
straddling `Tθ/π` — `c` at phase distance `δ ∈ [0, 1/T]` below and `c + 1` at `1/T − δ` above
— and their mirrors for the `−` branch gives the paper's constant: the two-index Dirichlet
bound `phase_estimation_two_index` on each branch, halved by the branch weight and summed.
The accepted set is a `Finset`, so coincidences among the four indices are merged, never
double-counted; every accepted index decodes within the paper's error
`2π√(a(1−a))/T + π²/T²`. -/

/-- The accepted counting indices: both grid points straddling `Tθ/π` and their mirrors. -/
def straddleIndices (c : Fin T) : Finset (Fin T) := {c, c + 1, -c, -(c + 1)}

omit [Fintype ι] [DecidableEq ι] in
/-- For `T ≥ 2` the two straddling indices are distinct. -/
lemma ne_add_one_fin (hT : 2 ≤ T) (c : Fin T) : c ≠ c + 1 := by
  intro h
  have hv := congrArg Fin.val h
  rcases Nat.lt_or_ge ((c : ℕ) + 1) T with hlt | hge
  · rw [val_add_one_fin_of_lt T hlt] at hv
    omega
  · have hc : (c : ℕ) + 1 = T := by have := c.isLt; omega
    rw [val_add_one_fin_of_eq T hc] at hv
    omega

/-- ★★ **The both-rounding success bound (BHMT Theorem 11, `k = 1`, the probability half).**
If `c` sits at phase distance `0 ≤ θ/π − c/T ≤ 1/T` below `θ/π`, the four accepted indices
`{c, c + 1, −c, −(c + 1)}` jointly carry at least `8/π²` of the measured marginal: each branch
puts `8/π²` on its own straddling pair (`phase_estimation_two_index`, the `−` branch through
the mirror `prob_applyQFTinv_phaseStateR_neg`), and the branch weights are `1/2` each. -/
theorem amplitude_estimation_straddle (hT : 2 ≤ T) (hgg : inner ℂ g g = 1)
    (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0)
    (hbsupp : ∀ i ∈ G, b i = 0) (θ : ℝ) (c : Fin T)
    (hlo : 0 ≤ θ / Real.pi - (c : ℝ) / T) (hhi : θ / Real.pi - (c : ℝ) / T ≤ 1 / T) :
    8 / Real.pi ^ 2 ≤ ∑ i ∈ straddleIndices T c, probLeft (matrixLeft (qftMatrix T)ᴴ
        (kickbackState T (ampState g b θ) G (ampState g b θ))) i := by
  obtain ⟨Pp, hPp⟩ : ∃ Pp : Fin T → ℝ,
      Pp = fun i => prob (applyQFTinv T (phaseStateR T (θ / Real.pi))) i := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ Pm : Fin T → ℝ,
      Pm = fun i => prob (applyQFTinv T (phaseStateR T (-(θ / Real.pi)))) i := ⟨_, rfl⟩
  have hM : ∀ i, probLeft (matrixLeft (qftMatrix T)ᴴ
      (kickbackState T (ampState g b θ) G (ampState g b θ))) i = (Pp i + Pm i) / 2 := by
    intro i
    rw [hPp, hPm]
    exact amplitude_estimation_marginal T hgg hbb hgb hgsupp hbsupp θ i
  have hPp0 : ∀ i, 0 ≤ Pp i := fun i => by rw [hPp]; exact prob_nonneg _ _
  have hPm0 : ∀ i, 0 ≤ Pm i := fun i => by rw [hPm]; exact prob_nonneg _ _
  have hne : c ≠ c + 1 := ne_add_one_fin T hT c
  have hne' : -c ≠ -(c + 1) := fun h => hne (neg_injective h)
  -- the `+` branch on its straddling pair, and the `−` branch on the mirrored pair
  have hplus : 8 / Real.pi ^ 2 ≤ Pp c + Pp (c + 1) := by
    rw [hPp]
    exact phase_estimation_two_index T (θ / Real.pi) c hlo hhi
  have hminus : Pm (-c) + Pm (-(c + 1)) = Pp c + Pp (c + 1) := by
    rw [hPp, hPm]
    beta_reduce
    rw [prob_applyQFTinv_phaseStateR_neg, prob_applyQFTinv_phaseStateR_neg]
  -- the pairs sit inside the accepted set
  have hsub1 : ({c, c + 1} : Finset (Fin T)) ⊆ straddleIndices T c := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [straddleIndices, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsub2 : ({-c, -(c + 1)} : Finset (Fin T)) ⊆ straddleIndices T c := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [straddleIndices, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hS1 : Pp c + Pp (c + 1) ≤ ∑ i ∈ straddleIndices T c, Pp i := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun i _ _ => hPp0 i
  have hS2 : Pm (-c) + Pm (-(c + 1)) ≤ ∑ i ∈ straddleIndices T c, Pm i := by
    rw [← Finset.sum_pair hne']
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i _ _ => hPm0 i
  calc 8 / Real.pi ^ 2 = (8 / Real.pi ^ 2 + 8 / Real.pi ^ 2) / 2 := by ring
    _ ≤ (∑ i ∈ straddleIndices T c, Pp i + ∑ i ∈ straddleIndices T c, Pm i) / 2 := by
        linarith
    _ = ∑ i ∈ straddleIndices T c, (Pp i + Pm i) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i ∈ straddleIndices T c, probLeft (matrixLeft (qftMatrix T)ᴴ
        (kickbackState T (ampState g b θ) G (ampState g b θ))) i :=
        Finset.sum_congr rfl fun i _ => (hM i).symm

omit [Fintype ι] [DecidableEq ι] in
/-- ★ **The accuracy of every accepted index (BHMT Lemma 7 at `ε = π/T`).** Each index in
`straddleIndices T c` decodes to `ã = sin²(πi/T)` with `|ã − a| ≤ 2π√(a(1−a))/T + π²/T²` —
the paper's literal constants. The upper index `c + 1` is read modulo `T`; at the wrap it
decodes to `sin²(0) = sin²(π) = 0`. -/
theorem amplitude_estimation_straddle_close {a : ℝ} (ha0 : 0 ≤ a) {θ : ℝ}
    (hθ : Real.sin θ = Real.sqrt a) (hθc : Real.cos θ = Real.sqrt (1 - a)) (c : Fin T)
    (hlo : 0 ≤ θ / Real.pi - (c : ℝ) / T) (hhi : θ / Real.pi - (c : ℝ) / T ≤ 1 / T)
    {i : Fin T} (hi : i ∈ straddleIndices T c) :
    |Real.sin (Real.pi * i / T) ^ 2 - a|
      ≤ 2 * Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / T ^ 2 := by
  have hTpos : (0 : ℝ) < T := by have := NeZero.ne T; positivity
  have hTR : (T : ℝ) ≠ 0 := hTpos.ne'
  have hπ : 0 < Real.pi := Real.pi_pos
  have hε : 2 * Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / T ^ 2
      = 2 * Real.sqrt (a * (1 - a)) * (Real.pi / T) + (Real.pi / T) ^ 2 := by ring
  -- the lower index
  have hc : |Real.sin (Real.pi * c / T) ^ 2 - a|
      ≤ 2 * Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / T ^ 2 := by
    rw [hε]
    apply amplitude_estimation_error ha0 hθ hθc
    have e : Real.pi * c / T - θ = -(Real.pi * (θ / Real.pi - (c : ℝ) / T)) := by
      field_simp
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos hπ, abs_of_nonneg hlo]
    calc Real.pi * (θ / Real.pi - (c : ℝ) / T) ≤ Real.pi * (1 / T) :=
          mul_le_mul_of_nonneg_left hhi hπ.le
      _ = Real.pi / T := by ring
  -- the upper index, unwrapped
  have hc1 : |Real.sin (Real.pi * ((c + 1 : Fin T) : ℕ) / T) ^ 2 - a|
      ≤ 2 * Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / T ^ 2 := by
    have hval : Real.sin (Real.pi * ((c + 1 : Fin T) : ℕ) / T) ^ 2
        = Real.sin (Real.pi * ((c : ℝ) + 1) / T) ^ 2 := by
      rcases Nat.lt_or_ge ((c : ℕ) + 1) T with hlt | hge
      · rw [val_add_one_fin_of_lt T hlt]
        push_cast
        rfl
      · have hcn : (c : ℕ) + 1 = T := by have := c.isLt; omega
        have hcR : ((c : ℕ) : ℝ) + 1 = T := by exact_mod_cast hcn
        rw [val_add_one_fin_of_eq T hcn, Nat.cast_zero, mul_zero, zero_div, Real.sin_zero,
          hcR, mul_div_cancel_right₀ _ hTR, Real.sin_pi]
    rw [hval, hε]
    apply amplitude_estimation_error ha0 hθ hθc
    have e : Real.pi * ((c : ℝ) + 1) / T - θ
        = Real.pi * (1 / T - (θ / Real.pi - (c : ℝ) / T)) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos hπ, abs_of_nonneg (by linarith)]
    calc Real.pi * (1 / T - (θ / Real.pi - (c : ℝ) / T)) ≤ Real.pi * (1 / T) :=
          mul_le_mul_of_nonneg_left (by linarith) hπ.le
      _ = Real.pi / T := by ring
  -- the four cases, the mirrors decoding to the same estimates
  simp only [straddleIndices, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hc
  · exact hc1
  · rw [sin_sq_mirror]; exact hc
  · rw [sin_sq_mirror]; exact hc1

/-- ★★ **BHMT Theorem 11 (`k = 1`).** For `T ≥ 2` and a lower straddling index `c` of `θ/π`
(one exists for every `0 ≤ θ/π < 1`, `exists_straddle_index`), every accepted index decodes
within `2π√(a(1−a))/T + π²/T²` of `a = sin²θ`, and the accepted set carries probability at
least `8/π²`. -/
theorem amplitude_estimation_bhmt (hT : 2 ≤ T) (hgg : inner ℂ g g = 1)
    (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0)
    (hbsupp : ∀ i ∈ G, b i = 0) {a : ℝ} (ha0 : 0 ≤ a) {θ : ℝ}
    (hθ : Real.sin θ = Real.sqrt a) (hθc : Real.cos θ = Real.sqrt (1 - a)) (c : Fin T)
    (hlo : 0 ≤ θ / Real.pi - (c : ℝ) / T) (hhi : θ / Real.pi - (c : ℝ) / T ≤ 1 / T) :
    (∀ i ∈ straddleIndices T c, |Real.sin (Real.pi * i / T) ^ 2 - a|
        ≤ 2 * Real.pi * Real.sqrt (a * (1 - a)) / T + Real.pi ^ 2 / T ^ 2)
      ∧ 8 / Real.pi ^ 2 ≤ ∑ i ∈ straddleIndices T c, probLeft (matrixLeft (qftMatrix T)ᴴ
          (kickbackState T (ampState g b θ) G (ampState g b θ))) i :=
  ⟨fun _ hi => amplitude_estimation_straddle_close T ha0 hθ hθc c hlo hhi hi,
    amplitude_estimation_straddle T hT hgg hbb hgb hgsupp hbsupp θ c hlo hhi⟩

end QuantumInfo
