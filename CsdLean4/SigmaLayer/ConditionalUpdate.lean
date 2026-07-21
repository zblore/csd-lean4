import CsdLean4.SigmaLayer.Luders

/-!
# FND/ConditionalUpdate: the general (non-projective) conditional state update

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Ledger target **T7**, the general conditional post-measurement state update, of which the Lüders update
(**T8**, `FND/Luders.lean`) is the sharp-projective special case.

A general measurement outcome is described by a measurement operator (Kraus operator) `M`: the effect
measured is `E = M† M` (a positive operator `0 ≤ E ≤ I`; every effect arises as `M = √E`), the outcome
probability on a unit state `x` is `updateWeight M x = ‖M x‖² = Re⟨x, E x⟩`
(`updateWeight_eq_re_inner`), and the post-measurement state is the normalised transformed state
`stateUpdate M x = (‖M x‖)⁻¹ • M x`. We prove:

* **normalisation** (`stateUpdate_norm`): the updated state is a unit vector when the outcome is possible;
* **Born consistency** (`updateWeight_eq_re_inner`): the weight is the effect expectation `Re⟨x, E x⟩`;
* **sequential (chained-measurement) rule** (`stateUpdate_sequential`): for a second measurement operator
  `N`, `updateWeight N (stateUpdate M x) = updateWeight N (M x) / updateWeight M x` — the conditional
  probability of the second outcome given the first is the joint over the first (Wigner's formula for
  sequential measurements; general conditionalisation, no sharpness assumed).

Lüders is the special case (`stateUpdate_eq_ludersUpdate`): when `M = P` is a projection, `stateUpdate P`
is definitionally `ludersUpdate P`, and the sequential rule reduces to `ludersUpdate_conditional`. So T7
subsumes T8, and unlike T8 needs neither self-adjointness nor idempotence of the measurement operator.

General finite-dimensional complex inner product space; no new postulate.
-/

open scoped ComplexConjugate

set_option linter.unusedSectionVars false

namespace CSD.SigmaLayer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The outcome probability of a measurement operator.** `‖M x‖²`, the Born weight of the effect
`E = M† M` on the state `x`. -/
noncomputable def updateWeight (M : E →ₗ[ℂ] E) (x : E) : ℝ := ‖M x‖ ^ 2

/-- **The general conditional state update.** The normalised transformed state `(‖M x‖)⁻¹ • M x` (and
`0` on the null set `M x = 0`). For a projection this is the Lüders update. -/
noncomputable def stateUpdate (M : E →ₗ[ℂ] E) (x : E) : E := ((‖M x‖ : ℂ))⁻¹ • M x

/-- **Born consistency.** The outcome probability is the effect expectation `Re⟨x, M† M x⟩`: with the
effect `E = M† M`, `updateWeight M x = Re⟨x, E x⟩`, the `LF2.POVM`/effect weight convention. -/
theorem updateWeight_eq_re_inner (M : E →ₗ[ℂ] E) (x : E) :
    updateWeight M x = (inner ℂ x ((LinearMap.adjoint M) (M x))).re := by
  rw [updateWeight, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Normalisation.** The updated state is a unit vector whenever the outcome is possible
(`M x ≠ 0`). -/
theorem stateUpdate_norm (M : E →ₗ[ℂ] E) (x : E) (hx : M x ≠ 0) :
    ‖stateUpdate M x‖ = 1 := by
  rw [stateUpdate, norm_smul, norm_inv, Complex.norm_real, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- **Sequential (chained-measurement) rule.** For a second measurement operator `N` applied after the
`M`-update, the outcome probability is the conditional probability
`updateWeight N (M x) / updateWeight M x`: the joint probability of both outcomes divided by the first
outcome's probability. This is Wigner's formula for sequential measurements, the general
conditionalisation of the Born weights, holding for arbitrary (non-sharp) measurement operators. -/
theorem stateUpdate_sequential (N M : E →ₗ[ℂ] E) (x : E) (_hx : M x ≠ 0) :
    updateWeight N (stateUpdate M x) = updateWeight N (M x) / updateWeight M x := by
  simp only [updateWeight, stateUpdate]
  rw [map_smul, norm_smul, mul_pow, norm_inv, Complex.norm_real, norm_norm, inv_pow,
    div_eq_mul_inv, mul_comm]

/-- **Lüders is the sharp special case of T7.** For a projection `P`, the general conditional update
`stateUpdate P` is exactly the Lüders update `ludersUpdate P`. -/
theorem stateUpdate_eq_ludersUpdate (P : E →ₗ[ℂ] E) (x : E) :
    stateUpdate P x = ludersUpdate P x := rfl

/-- **T7: the general conditional state update, its three defining properties.** For any measurement
operator `M`, the conditional update `stateUpdate M` is normalised, its outcome weight is the effect
expectation `Re⟨x, M† M x⟩`, and it obeys the sequential (chained-measurement) conditionalisation rule.
Subsumes the Lüders update `luders_capstone` (T8), which is the projective special case. -/
theorem conditionalUpdate_capstone (M : E →ₗ[ℂ] E) :
    (∀ x, M x ≠ 0 → ‖stateUpdate M x‖ = 1)
    ∧ (∀ x, updateWeight M x = (inner ℂ x ((LinearMap.adjoint M) (M x))).re)
    ∧ (∀ (N : E →ₗ[ℂ] E) x, M x ≠ 0 →
        updateWeight N (stateUpdate M x) = updateWeight N (M x) / updateWeight M x) :=
  ⟨fun x hx => stateUpdate_norm M x hx,
    fun x => updateWeight_eq_re_inner M x,
    fun N x hx => stateUpdate_sequential N M x hx⟩

end CSD.SigmaLayer
