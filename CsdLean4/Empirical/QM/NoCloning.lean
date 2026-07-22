/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Empirical: No-cloning theorem

**Category:** 3-Local (currently placed under `CsdLean4/Empirical/`
alongside CSD-specific empirical-prediction re-exports). The content
itself is QM-generic — no CSD ontology, no `OnticSetup` / `SectorData`
/ singlet machinery — and is **promotion-ready to 2-Framework** (or
even 1-Mathlib) on demand. Extraction to `CsdLean4/Framework/QM/` or
upstreaming to `Mathlib/QuantumMechanics/NoCloning.lean` is deferred
until LF4 creates the `Framework/` subtree (CONVENTIONS.md §1.Cat-2).

Wootters-Zurek 1982 no-cloning theorem: in quantum mechanics, there is
no unitary operation on a joint Hilbert space `H ⊗ H` that, for an
arbitrary unit input state `ψ ∈ H` and a fixed unit "blank" state `e0`,
produces the cloned pair `ψ ⊗ ψ` from `ψ ⊗ e0`.

We deliver the **two-state form** of the theorem: for any pair of unit
input states `ψ, φ`, if a (linear) isometry `U : Htensor → Htensor`
clones both `ψ` and `φ` from the same blank, then `⟨ψ, φ⟩ ∈ {0, 1}`
(i.e. the two states are either orthogonal or equal up to phase).

This is the load-bearing content of the no-cloning theorem; the
"no-universal-cloner" formulation (a single `U` cloning *all* unit
states) is a direct corollary (for any two non-equal non-orthogonal
unit states, the two-state form already gives a contradiction).

## Abstraction over the tensor structure

The theorem is stated abstractly over an arbitrary `tensor : H → H →
Htensor` together with the **tensor inner-product factorisation**
`⟨tensor a b, tensor c d⟩ = ⟨a, c⟩ · ⟨b, d⟩`. Concrete instances
include:

- `H := EuclideanSpace ℂ (Fin n)`, `Htensor := EuclideanSpace ℂ (Fin n
  × Fin n)`, `tensor ψ e0 := fun (i, j) => ψ i * e0 j`.
- The Mathlib `TensorProduct ℂ H H` once equipped with the standard
  inner product.

By stating the theorem at the abstract level, we avoid committing to
either the Kronecker realisation or Mathlib's `TensorProduct`
machinery, leaving the choice to callers.

## Experimental verification

The no-cloning theorem is verified in every QM experiment where
cloning would be needed but does not occur. Direct experimental tests
include the impossibility of broadcasting an unknown polarisation
state of a single photon (Lamas-Linares et al. 2002, *Science* **296**,
712, demonstrates the universal-cloning bound `5/6` for optimal
approximate cloning; the exact no-cloning bound `< 1` follows
immediately from the theorem below).

## Source

Wootters and Zurek 1982, *Nature* **299**, 802; Dieks 1982,
*Phys. Lett. A* **92**, 271 (simultaneous independent derivation).
-/

open ComplexConjugate

namespace CSD
namespace Empirical
namespace NoCloning

variable {H Htensor : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]

/-- **No-cloning theorem (two-state form).** Let `H` and `Htensor` be
complex inner product spaces, `tensor : H → H → Htensor` a binary
pairing whose inner-product factorises as `⟨tensor a b, tensor c d⟩
= ⟨a, c⟩ · ⟨b, d⟩`, and `e0 : H` a fixed unit "blank" state.

If `U : Htensor → Htensor` is an isometry (preserves inner products)
that clones two unit states `ψ, φ : H` (with `‖ψ‖ = ‖φ‖ = 1`) from the
same blank, i.e. `U(tensor ψ e0) = tensor ψ ψ` and
`U(tensor φ e0) = tensor φ φ`, then `⟨ψ, φ⟩ ∈ {0, 1}`.

**On the unit-norm hypotheses.** The algebraic step
`⟨ψ, φ⟩ = ⟨ψ, φ⟩²` and its consequence `⟨ψ, φ⟩ ∈ {0, 1}` go through
regardless of normalisation. The unit-norm hypotheses are stated to
match the Wootters-Zurek operational reading ("orthogonal or equal up
to phase"), which requires `‖ψ‖ = ‖φ‖ = 1` for the second alternative
to mean what it says — only at unit norm does `⟨ψ, φ⟩ = 1` force
`φ = ψ` (Cauchy-Schwarz saturation).

**Proof.** Isometry preservation gives
```
⟨ψ, φ⟩ = ⟨ψ, φ⟩ · 1 = ⟨ψ, φ⟩ · ⟨e0, e0⟩         (e0 unit)
       = ⟨tensor ψ e0, tensor φ e0⟩              (tensor factorisation)
       = ⟨U (tensor ψ e0), U (tensor φ e0)⟩       (isometry)
       = ⟨tensor ψ ψ, tensor φ φ⟩                 (cloning)
       = ⟨ψ, φ⟩ · ⟨ψ, φ⟩.                          (tensor factorisation)
```
So `⟨ψ, φ⟩ = ⟨ψ, φ⟩²`, hence `⟨ψ, φ⟩ · (1 − ⟨ψ, φ⟩) = 0`, hence
`⟨ψ, φ⟩ ∈ {0, 1}`. -/
theorem no_cloning_two_state
    (tensor : H → H → Htensor)
    (h_tensor_inner : ∀ a b c d : H,
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (e0 : H) (he0 : ‖e0‖ = 1)
    (ψ φ : H) (_hψ : ‖ψ‖ = 1) (_hφ : ‖φ‖ = 1)
    (U : Htensor → Htensor)
    (hU : ∀ x y : Htensor, inner ℂ (U x) (U y) = inner ℂ x y)
    (h_clone_ψ : U (tensor ψ e0) = tensor ψ ψ)
    (h_clone_φ : U (tensor φ e0) = tensor φ φ) :
    inner ℂ ψ φ = 0 ∨ inner ℂ ψ φ = 1 := by
  have h_e0_inner : inner ℂ e0 e0 = (1 : ℂ) := by
    rw [@inner_self_eq_norm_sq_to_K ℂ _ _ _, he0]
    simp
  -- Apply isometry preservation to the cloning identities.
  have h_iso :
      inner ℂ (tensor ψ e0) (tensor φ e0)
        = inner ℂ (tensor ψ ψ) (tensor φ φ) := by
    calc inner ℂ (tensor ψ e0) (tensor φ e0)
        = inner ℂ (U (tensor ψ e0)) (U (tensor φ e0)) := (hU _ _).symm
      _ = inner ℂ (tensor ψ ψ) (tensor φ φ) := by rw [h_clone_ψ, h_clone_φ]
  -- Use tensor inner-product factorisation on both sides.
  rw [h_tensor_inner, h_tensor_inner, h_e0_inner, mul_one] at h_iso
  -- h_iso : ⟨ψ, φ⟩ = ⟨ψ, φ⟩ * ⟨ψ, φ⟩
  -- Conclude ⟨ψ, φ⟩ ∈ {0, 1}.
  have h_quad : inner ℂ ψ φ * (1 - inner ℂ ψ φ) = 0 := by
    have := h_iso
    ring_nf
    linear_combination this
  rcases mul_eq_zero.mp h_quad with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination -h)

/-- **No universal cloner (corollary).** No (linear) isometry can
clone every unit state from a fixed blank. Concretely: there exist
unit states `ψ, φ ∈ H` (in any inner product space of dimension ≥ 2)
such that no isometry `U` can clone both simultaneously, because no
two non-orthogonal non-equal unit states have `⟨ψ, φ⟩ ∈ {0, 1}`.

The corollary is *constructive at the level of states*: given any two
unit states `ψ, φ` with `⟨ψ, φ⟩ ∉ {0, 1}` (which exist in any inner
product space of dimension ≥ 2), `no_cloning_two_state` applied to
them rules out a universal cloner. -/
theorem no_universal_cloner_of_witness
    (tensor : H → H → Htensor)
    (h_tensor_inner : ∀ a b c d : H,
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (e0 : H) (he0 : ‖e0‖ = 1)
    (ψ φ : H) (hψ_unit : ‖ψ‖ = 1) (hφ_unit : ‖φ‖ = 1)
    (h_neither : inner ℂ ψ φ ≠ 0 ∧ inner ℂ ψ φ ≠ 1) :
    ¬ ∃ U : Htensor → Htensor,
        (∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) ∧
        U (tensor ψ e0) = tensor ψ ψ ∧
        U (tensor φ e0) = tensor φ φ := by
  rintro ⟨U, hU, hψ, hφ⟩
  obtain h | h := no_cloning_two_state tensor h_tensor_inner e0 he0
    ψ φ hψ_unit hφ_unit U hU hψ hφ
  · exact h_neither.1 h
  · exact h_neither.2 h

end NoCloning
end Empirical
end CSD
