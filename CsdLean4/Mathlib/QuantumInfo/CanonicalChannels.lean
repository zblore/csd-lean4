import CsdLean4.Mathlib.QuantumInfo.Stinespring

/-!
# Canonical quantum channels

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This file (phase C3 of `specs/channels-plan.md`) records the standard named channels as
inhabitants of `QuantumInfo.Channel`:

* `Channel.unitaryChannel U hU` — a **unitary channel** `ρ ↦ U ρ Uᴴ` (a single Kraus
  operator `U`, `Uᴴ U = 1`). Generalises `Channel.id` (`= unitaryChannel 1`).
* `Channel.traceOutChannel` — the **trace-out (partial-trace) channel** `ρ ↦ traceRight ρ`
  on `ℂ^(s ⊗ env)`, the literal "discard the environment". Obtained for free from the C2
  Stinespring machinery as `ofIsometry 1`.
* `Channel.mixedUnitaryChannel U hU p hp0 hp` — a **mixed-unitary (random-unitary) channel**
  `ρ ↦ ∑ᵢ pᵢ • (Uᵢ ρ Uᵢᴴ)` for a probability vector `p` and unitaries `Uᵢ`, with Kraus
  operators `√pᵢ • Uᵢ`. This is the Cat-1-clean generalisation of the dephasing /
  depolarizing / bit-flip channels: each of those is `mixedUnitaryChannel` with a concrete
  Pauli family (assembled by the consumer, which supplies the Paulis — keeping this file
  Pauli-free).

The dephasing/depolarizing/bit-flip channels named in the plan are instances of
`mixedUnitaryChannel`; the QEC error channel (phase C4) is the bit-flip instance.
-/

open Matrix
open scoped ComplexOrder Kronecker

-- Several lemmas use only a subset of the section instances; silence the section-var linter.
set_option linter.unusedSectionVars false

namespace QuantumInfo
namespace Channel

/-! ### Unitary channel -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **unitary channel** `ρ ↦ U ρ Uᴴ` of a unitary `U` (`Uᴴ U = 1`): a single Kraus
operator. Generalises `Channel.id` (which is `unitaryChannel 1`). -/
noncomputable def unitaryChannel (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    Channel n n PUnit where
  kraus _ := U
  tp := by simpa using hU

@[simp] lemma unitaryChannel_apply (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix n n ℂ) : (unitaryChannel U hU).apply ρ = U * ρ * Uᴴ := by
  rw [apply_def]; simp [unitaryChannel]

/-! ### Trace-out channel -/

/-- The **trace-out channel** on `ℂ^(s ⊗ env)`: discard the environment, `ρ ↦ traceRight ρ`.
It is the C2 Stinespring channel of the identity isometry. -/
noncomputable def traceOutChannel (s env : Type*) [Fintype s] [Fintype env]
    [DecidableEq s] [DecidableEq env] : Channel (s × env) s env :=
  ofIsometry (1 : Matrix (s × env) (s × env) ℂ) (by simp)

@[simp] lemma traceOutChannel_apply (s env : Type*) [Fintype s] [Fintype env]
    [DecidableEq s] [DecidableEq env] (ρ : Matrix (s × env) (s × env) ℂ) :
    (traceOutChannel s env).apply ρ = Matrix.traceRight ρ := by
  unfold traceOutChannel
  rw [ofIsometry_apply]
  simp

/-! ### Mixed-unitary (random-unitary) channel -/

/-- Helper: `star (√r : ℂ) = (√r : ℂ)` (the square root is real). -/
private lemma star_ofReal_sqrt {r : ℝ} :
    star ((Real.sqrt r : ℂ)) = (Real.sqrt r : ℂ) := by
  rw [← starRingEnd_apply, Complex.conj_ofReal]

/-- Helper: for `r ≥ 0`, `star (√r : ℂ) * (√r : ℂ) = (r : ℂ)`. -/
private lemma star_ofReal_sqrt_mul {r : ℝ} (hr : 0 ≤ r) :
    star ((Real.sqrt r : ℂ)) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  rw [star_ofReal_sqrt, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]

/-- The **mixed-unitary (random-unitary) channel** `ρ ↦ ∑ᵢ pᵢ • (Uᵢ ρ Uᵢᴴ)`: a convex
combination (probabilities `p`, `∑ pᵢ = 1`, `pᵢ ≥ 0`) of unitary conjugations, with Kraus
operators `√pᵢ • Uᵢ`. The dephasing / depolarizing / bit-flip channels are the instances
with a concrete Pauli family for `U`. -/
noncomputable def mixedUnitaryChannel {ι : Type*} [Fintype ι] (U : ι → Matrix n n ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    Channel n n ι where
  kraus i := (Real.sqrt (p i) : ℂ) • U i
  tp := by
    have hterm : ∀ i, ((Real.sqrt (p i) : ℂ) • U i)ᴴ * ((Real.sqrt (p i) : ℂ) • U i)
        = (p i : ℂ) • (1 : Matrix n n ℂ) := by
      intro i
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        star_ofReal_sqrt_mul (hp0 i), hU i]
    simp_rw [hterm]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hp, Complex.ofReal_one, one_smul]

@[simp] lemma mixedUnitaryChannel_apply {ι : Type*} [Fintype ι] (U : ι → Matrix n n ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (ρ : Matrix n n ℂ) :
    (mixedUnitaryChannel U hU p hp0 hp).apply ρ
      = ∑ i, (p i : ℂ) • (U i * ρ * (U i)ᴴ) := by
  rw [apply_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((Real.sqrt (p i) : ℂ) • U i) * ρ * ((Real.sqrt (p i) : ℂ) • U i)ᴴ = _
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    star_ofReal_sqrt]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp0 i)]

/-! ### Local channel: `Φ ⊗ id` (Alice acts, Bob idle) -/

/-- Kronecker-with-identity commutes with finite sums on the left factor. -/
private lemma sum_kronecker_one {p' n' ι' : Type*} [Fintype ι'] {b' : Type*} [DecidableEq b']
    (f : ι' → Matrix p' n' ℂ) :
    (∑ i, f i) ⊗ₖ (1 : Matrix b' b' ℂ) = ∑ i, (f i ⊗ₖ (1 : Matrix b' b' ℂ)) := by
  ext x z
  simp [Matrix.sum_apply, Finset.sum_mul]

variable {p ι : Type*} [Fintype p] [Fintype ι]

/-- The **local channel** `Φ ⊗ id_b`: Alice applies the channel `Φ` to her factor while
Bob's factor `b` is left idle. Kraus operators `Φ.kraus i ⊗ I_b`. -/
noncomputable def tensorRight (Φ : Channel n p ι) (b : Type*) [Fintype b] [DecidableEq b] :
    Channel (n × b) (p × b) ι where
  kraus i := Φ.kraus i ⊗ₖ (1 : Matrix b b ℂ)
  tp := by
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.mul_one]
    rw [← sum_kronecker_one, Φ.tp, one_kronecker_one]

@[simp] lemma tensorRight_apply (Φ : Channel n p ι) (b : Type*) [Fintype b] [DecidableEq b]
    (ρ : Matrix (n × b) (n × b) ℂ) :
    (Φ.tensorRight b).apply ρ
      = ∑ i, (Φ.kraus i ⊗ₖ (1 : Matrix b b ℂ)) * ρ * (Φ.kraus i ⊗ₖ (1 : Matrix b b ℂ))ᴴ := by
  rw [apply_def]; rfl

end Channel
end QuantumInfo
