/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Hadamard
public import CsdLean4.Mathlib.QuantumInfo.AmplitudeAmplification

/-!
# Grover's search algorithm (R5+) — as an instance of amplitude amplification

**Category:** 3-Local (QM-validity).

Grover's algorithm: search for a single marked item `w : Fin n → Fin 2` in an unstructured
database of `N = 2ⁿ` items. The search step is the composition of the **oracle** (phase flip on
`w`, `I - 2|w⟩⟨w|`) and the **diffusion** operator (inversion about the mean, `2|s⟩⟨s| - I`,
where `|s⟩` is the uniform superposition).

*Rebuilt 2026-08-29 (plan `specs/amplitude-amplification-plan.md`, brick AA-3):* the step
operators are proved to be the **BHMT amplification step** of
`Mathlib/QuantumInfo/AmplitudeAmplification.lean` — `oracle w = oracleFlip {w}`
(`oracle_eq_oracleFlip`) and `diffusion = reflect uniformState` (`diffusion_eq_reflect`) — and
the headline is **re-derived from the general theorem**: the uniform state is the rotation-plane
state at the Grover angle (`uniformState_eq_ampState`), so `ampStep_iterate` gives

  `grover_success : prob ((groverStep w)^[k] uniformState) w = sin²((2k+1)·θ)`,

`sin θ = 1/√N`. The file's previous self-contained rotation development (the `symState`
coefficient family and its operator-action lemmas) is **retired** — the general two-reflection
rotation now carries it, and keeping both would be exactly the parallel-development duplication
the Algorithm Atlas assessment (RESULT 4) documents. New at the same stroke, free from the
general theorem: the **`k`-marked-items** distribution `grover_multi_success`, which the
single-marked file could not state.

**Honest scope.** QM-validity breadth: genuine reflection operators on the `EuclideanSpace`
inner-product structure; amplitudes real, carried as `ℂ`-coercions. The optimal iteration count
and the success bound live with the general theorem (`amplitude_amplification_succeeds`,
`amplification_query_bound`) — the deferral the earlier version of this file recorded is closed
there, not here. Round counting is abstract-step counting; no oracle model is claimed.

**Extraction cost record (the atlas assessment's priced pilot, AA-3):** the rebuild of this
file on the general theorem — bridge lemmas, plane instantiation, re-derived headlines, deleted
parallel development — took ≈25 minutes wall-clock including two build-fix iterations
(2026-08-29, 14:22–14:47 session segment). The full AA-1..AA-3 session (general module written
and debugged + this refactor) was ≈90 minutes. See `specs/amplitude-amplification-plan.md`.
-/

@[expose] public section

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace Grover

variable {n : ℕ}

/-- The database size `N = 2ⁿ` as a real number. -/
noncomputable def databaseSize (n : ℕ) : ℝ := 2 ^ n

/-- The all-ones vector `J = ∑ z |z⟩`: amplitude `1` on every basis state. -/
noncomputable def J (n : ℕ) : QReg n := ∑ z, basisState z

lemma J_coord (z : Fin n → Fin 2) : J n z = ∑ x, (basisState x z) := by
  have h : (J n).ofLp = ∑ x, (basisState x).ofLp := by
    rw [J]
    exact map_sum (WithLp.addEquiv 2 ((Fin n → Fin 2) → ℂ)) basisState Finset.univ
  calc J n z = (J n).ofLp z := rfl
    _ = (∑ x, (basisState x).ofLp) z := by rw [h]
    _ = ∑ x, (basisState x z) := by rw [Finset.sum_apply]

@[simp] lemma J_apply (z : Fin n → Fin 2) : J n z = 1 := by
  rw [J_coord, Finset.sum_eq_single z]
  · rw [basisState_apply, if_pos rfl]
  · intro b _ hb; rw [basisState_apply]; rw [if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The **uniform superposition** `|s⟩ = (1/√N) ∑ z |z⟩`. -/
noncomputable def uniformState : QReg n := (Real.sqrt (databaseSize n))⁻¹ • J n

@[simp] lemma uniformState_apply (z : Fin n → Fin 2) :
    (uniformState : QReg n) z = (Real.sqrt (databaseSize n) : ℂ)⁻¹ := by
  rw [uniformState, WithLp.ofLp_smul, Pi.smul_apply, J_apply, Complex.real_smul, mul_one,
    Complex.ofReal_inv]

/-- `√(2ⁿ) = (√2)ⁿ` (the principal root commutes with the nonnegative power). -/
lemma sqrt_two_pow_eq (n : ℕ) : Real.sqrt ((2 : ℝ) ^ n) = Real.sqrt 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]

/-- **The Grover entry point is the Hadamard output:** `uniformState = H^⊗n |0ⁿ⟩`. This ties the
uniform superposition (defined here as the normalized all-ones vector) to the R2 Hadamard layer,
where `Hn_apply_zero` gives the same amplitude `(√2⁻¹)ⁿ = (√(2ⁿ))⁻¹` on every basis state. -/
lemma uniformState_eq_hadamard : (uniformState : QReg n) = applyHn (basisState 0) := by
  ext z
  rw [uniformState_apply, Hn_apply_zero, databaseSize, sqrt_two_pow_eq, Complex.ofReal_pow,
    inv_pow]

/-- The **oracle** `O_w = I - 2|w⟩⟨w|`: a phase flip on the marked item `w`. -/
noncomputable def oracle (w : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  ψ - (2 * ψ w) • basisState w

/-- The **diffusion** operator `2|s⟩⟨s| - I`: inversion about the mean. -/
noncomputable def diffusion (ψ : QReg n) : QReg n :=
  (2 * inner ℂ (uniformState) ψ) • uniformState - ψ

/-- One **Grover step**: oracle then diffusion. -/
noncomputable def groverStep (w : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  diffusion (oracle w ψ)

/-! ## The bridge: Grover's operators ARE the BHMT amplification step -/

/-- **The oracle is the good-set reflection at `G = {w}`.** -/
lemma oracle_eq_oracleFlip (w : Fin n → Fin 2) (ψ : QReg n) :
    oracle w ψ = oracleFlip {w} ψ := by
  ext z
  rw [oracleFlip_apply, oracle, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul,
    Pi.smul_apply, basisState_apply, smul_eq_mul]
  simp only [Finset.mem_singleton]
  split_ifs with h
  · rw [h]
    ring
  · ring

/-- **The diffusion is the reflection about the uniform state.** -/
lemma diffusion_eq_reflect (ψ : QReg n) : diffusion ψ = reflect uniformState ψ := rfl

/-- **One Grover step is one amplification step** at `φ = uniformState`, `G = {w}`. -/
lemma groverStep_eq_ampStep (w : Fin n → Fin 2) :
    groverStep w = ampStep (uniformState : QReg n) {w} := by
  funext ψ
  rw [groverStep, oracle_eq_oracleFlip, diffusion_eq_reflect, ampStep]

/-! ## The rotation plane: `|w⟩` and the normalized rest -/

/-- `1 ≤ 2ⁿ` as a real, hence `0 ≤ 2ⁿ - 1`. -/
lemma one_le_two_pow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
  calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
    _ ≤ (2 : ℝ) ^ n := by apply pow_le_pow_right₀ (by norm_num) (Nat.zero_le n)

/-- For `n ≥ 1`, `2 ≤ 2ⁿ` as a real, hence `1 ≤ 2ⁿ - 1`. -/
lemma two_le_two_pow (hn : 1 ≤ n) : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
  calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
    _ ≤ (2 : ℝ) ^ n := by apply pow_le_pow_right₀ (by norm_num) hn

/-- `√(N-1) · √(N-1) = N - 1`. -/
lemma sqrt_sub_one_mul_self :
    Real.sqrt ((2 : ℝ) ^ n - 1) * Real.sqrt ((2 : ℝ) ^ n - 1) = (2 : ℝ) ^ n - 1 :=
  Real.mul_self_sqrt (by linarith [one_le_two_pow (n := n)])

lemma sqrt_sub_one_ne (hn : 1 ≤ n) : Real.sqrt ((2 : ℝ) ^ n - 1) ≠ 0 := by
  rw [Real.sqrt_ne_zero (by linarith [one_le_two_pow (n := n)])]
  linarith [two_le_two_pow hn]

/-- The **normalized rest state** `(√(N-1))⁻¹ (J − |w⟩)`: the bad unit component of the uniform
state against `{w}`. -/
noncomputable def restState (w : Fin n → Fin 2) : QReg n :=
  (Real.sqrt ((2 : ℝ) ^ n - 1) : ℂ)⁻¹ • (J n - basisState w)

lemma restState_apply (w z : Fin n → Fin 2) :
    restState w z
      = (Real.sqrt ((2 : ℝ) ^ n - 1) : ℂ)⁻¹ * (1 - if z = w then 1 else 0) := by
  rw [restState, WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_sub, Pi.sub_apply, J_apply,
    basisState_apply, smul_eq_mul]

/-- `∑ z, (if z = w then a else b) = a + (N-1)·b`. -/
lemma sum_ite_single (w : Fin n → Fin 2) (a b : ℂ) :
    (∑ z : (Fin n → Fin 2), (if z = w then a else b)) = a + ((2 : ℂ) ^ n - 1) * b := by
  have hsplit : ∀ z : (Fin n → Fin 2),
      (if z = w then a else b) = b + (if z = w then a - b else 0) := by
    intro z; split <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ w (fun _ => a - b),
    if_pos (Finset.mem_univ w)]
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The marked basis state is supported on `{w}`. -/
lemma basisState_supp (w : Fin n → Fin 2) :
    ∀ z ∉ ({w} : Finset (Fin n → Fin 2)), basisState w z = 0 := by
  intro z hz
  rw [basisState_apply, if_neg (by simpa using hz)]

/-- The rest state vanishes on `{w}`. -/
lemma restState_supp (w : Fin n → Fin 2) :
    ∀ z ∈ ({w} : Finset (Fin n → Fin 2)), restState w z = 0 := by
  intro z hz
  rw [restState_apply, if_pos (by simpa using hz), sub_self, mul_zero]

/-- `⟨|w⟩, |w⟩⟩ = 1`. -/
lemma inner_basis_self (w : Fin n → Fin 2) :
    inner ℂ (basisState w : QReg n) (basisState w) = 1 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single w]
  · rw [RCLike.inner_apply', basisState_apply, if_pos rfl, map_one, one_mul]
  · intro z _ hz
    rw [RCLike.inner_apply', basisState_apply, if_neg hz, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `⟨rest, rest⟩ = 1` for `n ≥ 1`. -/
lemma inner_rest_self (hn : 1 ≤ n) (w : Fin n → Fin 2) :
    inner ℂ (restState w : QReg n) (restState w) = 1 := by
  have hs := sqrt_sub_one_mul_self (n := n)
  have hne := sqrt_sub_one_ne hn
  rw [PiLp.inner_apply]
  have hterm : ∀ z : Fin n → Fin 2,
      inner ℂ (restState w z) (restState w z)
        = if z = w then (0 : ℂ) else ((((2 : ℝ) ^ n - 1)⁻¹ : ℝ) : ℂ) := by
    intro z
    by_cases h : z = w
    · rw [if_pos h, RCLike.inner_apply', restState_apply, if_pos h, sub_self, mul_zero,
        map_zero, zero_mul]
    · rw [if_neg h, RCLike.inner_apply', restState_apply, if_neg h, sub_zero, mul_one,
        map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, hs,
        Complex.ofReal_inv]
  rw [Finset.sum_congr rfl fun z _ => hterm z, sum_ite_single w (0 : ℂ) _, zero_add]
  have hNne : ((2 : ℝ) ^ n - 1) ≠ 0 :=
    ne_of_gt (by linarith [two_le_two_pow (n := n) hn])
  rw [show ((2 : ℂ) ^ n - 1) = (((2 : ℝ) ^ n - 1 : ℝ) : ℂ) from by push_cast; ring,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hNne, Complex.ofReal_one]

/-- `⟨|w⟩, rest⟩ = 0`. -/
lemma inner_basis_rest (w : Fin n → Fin 2) :
    inner ℂ (basisState w : QReg n) (restState w) = 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single w]
  · rw [RCLike.inner_apply', restState_supp w w (by simp), mul_zero]
  · intro z _ hz
    rw [RCLike.inner_apply', basisState_apply, if_neg hz, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The uniform state is the rotation-plane state at the Grover angle:** given
`sin θ = 1/√N`, `cos θ = √(N-1)/√N`, `uniformState = ampState |w⟩ rest θ`. -/
lemma uniformState_eq_ampState (hn : 1 ≤ n) (w : Fin n → Fin 2) {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) :
    (uniformState : QReg n) = ampState (basisState w) (restState w) θ := by
  have hne := sqrt_sub_one_ne hn
  ext z
  rw [uniformState_apply, ampState_apply, basisState_apply, restState_apply, databaseSize]
  by_cases h : z = w
  · rw [if_pos h, sub_self, mul_zero, mul_zero, add_zero, mul_one, hsin,
      Complex.ofReal_inv]
  · rw [if_neg h, mul_zero, zero_add, sub_zero, mul_one, hcos]
    have hN : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := by positivity
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    field_simp

/-- `∑ z ∈ {w}, ‖(basisState w) z‖² = 1`. -/
lemma basisState_weight (w : Fin n → Fin 2) :
    ∑ z ∈ ({w} : Finset (Fin n → Fin 2)), ‖basisState w z‖ ^ 2 = 1 := by
  rw [Finset.sum_singleton, basisState_apply, if_pos rfl, norm_one, one_pow]

/-! ## The headline, re-derived from the general theorem -/

/-- **Grover success probability (headline):** after `k` Grover steps from the uniform
superposition, the probability of measuring the marked item `w` is `sin²((2k+1)·θ)`, where
`θ` is the Grover rotation half-angle (`sin θ = 1/√N`, `cos θ = √(N-1)/√N`). Re-derived from
`ampStep_iterate` (BHMT) via the operator identity `groverStep_eq_ampStep`. -/
theorem grover_success {n : ℕ} (hn : 1 ≤ n) (w : Fin n → Fin 2) (k : ℕ) (θ : ℝ)
    (hsin : Real.sin θ = (Real.sqrt (2 ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt (2 ^ n - 1) / Real.sqrt (2 ^ n)) :
    prob ((groverStep w)^[k] uniformState) w = Real.sin ((2 * k + 1) * θ) ^ 2 := by
  rw [groverStep_eq_ampStep w, uniformState_eq_ampState hn w hsin hcos,
    ampStep_iterate (inner_basis_self w) (inner_rest_self hn w) (inner_basis_rest w)
      (basisState_supp w) (restState_supp w) θ k]
  rw [prob, ampState_apply, basisState_apply, if_pos rfl, mul_one,
    restState_supp w w (by simp), mul_zero, add_zero, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- **Optimal iteration gives certainty:** when the accumulated angle hits `π/2`, i.e.
`(2k+1)·θ = π/2`, the marked item is measured with probability `1`. (The general
closest-integer bound is `amplitude_amplification_succeeds` in
`Mathlib/QuantumInfo/AmplitudeAmplification.lean`.) -/
theorem grover_certain {n : ℕ} (hn : 1 ≤ n) (w : Fin n → Fin 2) (k : ℕ) (θ : ℝ)
    (hsin : Real.sin θ = (Real.sqrt (2 ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt (2 ^ n - 1) / Real.sqrt (2 ^ n))
    (hopt : (2 * k + 1) * θ = Real.pi / 2) :
    prob ((groverStep w)^[k] uniformState) w = 1 := by
  rw [grover_success hn w k θ hsin hcos, hopt, Real.sin_pi_div_two, one_pow]

/-! ## The `k`-marked generalisation — free from the general theorem -/

/-- Each uniform amplitude has squared norm `N⁻¹`. -/
lemma uniform_amp_sq (z : Fin n → Fin 2) :
    ‖(uniformState : QReg n) z‖ ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
  rw [uniformState_apply, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, databaseSize,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ (2:ℝ) ^ n)]

/-- The uniform state is a unit vector. -/
lemma uniformState_norm : ‖(uniformState : QReg n)‖ = 1 := by
  have h := normSq_eq_sum_prob (uniformState : QReg n)
  have hsum : ∑ z, prob (uniformState : QReg n) z = 1 := by
    have hterm : ∀ z : Fin n → Fin 2, prob (uniformState : QReg n) z = ((2 : ℝ) ^ n)⁻¹ :=
      fun z => uniform_amp_sq z
    rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n from by push_cast; ring]
    exact mul_inv_cancel₀ (by positivity)
  rw [hsum] at h
  nlinarith [norm_nonneg (uniformState : QReg n)]

/-- The uniform success probability against a good set of size `k` is `k/N`. -/
lemma goodProb_uniform (G : Finset (Fin n → Fin 2)) :
    goodProb G (uniformState : QReg n) = G.card / (2 : ℝ) ^ n := by
  rw [goodProb, Finset.sum_congr rfl fun z _ => uniform_amp_sq z, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]

/-- ★ **The `k`-marked-items Grover distribution.** For a good set `G` of size strictly between
`0` and `N` on the uniform start, `j` amplification rounds give success probability exactly
`sin²((2j+1)·arcsin √(|G|/N))` — the generalisation the single-marked development could not
state, obtained as a direct instance of `amplitude_amplification`. -/
theorem grover_multi_success {n : ℕ} (G : Finset (Fin n → Fin 2))
    (hG0 : 0 < G.card) (hG1 : G.card < 2 ^ n) (j : ℕ) :
    goodProb G ((ampStep (uniformState : QReg n) G)^[j] uniformState)
      = Real.sin ((2 * j + 1)
          * Real.arcsin (Real.sqrt (G.card / (2 : ℝ) ^ n))) ^ 2 := by
  have ha : goodProb G (uniformState : QReg n) = G.card / (2 : ℝ) ^ n :=
    goodProb_uniform G
  have h := amplitude_amplification G (uniformState : QReg n) uniformState_norm
    (by rw [ha]; positivity)
    (by
      rw [ha, div_lt_one (by positivity : (0:ℝ) < (2:ℝ) ^ n)]
      exact_mod_cast hG1)
    j
  rw [ha] at h
  exact h

end Grover
end QM
end Empirical
end CSD
