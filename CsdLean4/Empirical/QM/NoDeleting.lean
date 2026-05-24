import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Empirical: No-deleting theorem

**Category:** 3-Local (currently placed under `CsdLean4/Empirical/`
alongside the QM-generic no-go theorems). The content is QM-generic —
no CSD ontology, no `OnticSetup` / `SectorData` machinery — and is
**promotion-ready to 2-Framework** (or 1-Mathlib) on demand, mirroring
`Empirical/QM/NoCloning.lean`. Extraction to `CsdLean4/Framework/QM/`
or upstreaming is deferred until LF4 creates the `Framework/` subtree
(CONVENTIONS.md §1.Cat-2).

Pati-Braunstein 2000 no-deleting theorem: the logical dual of
no-cloning. Given two copies of an unknown state `ψ`, there is no
unitary operation that deletes one copy against a fixed ancilla — i.e.
no `U` with `U(ψ ⊗ ψ) = ψ ⊗ e0` for arbitrary unknown `ψ`. Where
no-cloning forbids `ψ ⊗ e0 ↦ ψ ⊗ ψ`, no-deleting forbids the reverse
`ψ ⊗ ψ ↦ ψ ⊗ e0`.

We deliver the **two-state form**: for any pair of unit states `ψ, φ`,
if a (linear) isometry `U : Htensor → Htensor` deletes the second copy
of both `ψ` and `φ` against the same blank `e0`, then
`⟨ψ, φ⟩ ∈ {0, 1}` (orthogonal or equal up to phase). The
"no-universal-deleter" formulation is the direct corollary.

## Abstraction over the tensor structure

Stated abstractly over an arbitrary `tensor : H → H → Htensor` with the
**tensor inner-product factorisation**
`⟨tensor a b, tensor c d⟩ = ⟨a, c⟩ · ⟨b, d⟩`, exactly as in
`Empirical/QM/NoCloning.lean`. Concrete instances:

- `H := EuclideanSpace ℂ (Fin n)`, `Htensor := EuclideanSpace ℂ
  (Fin n × Fin n)`, `tensor ψ e0 := fun (i, j) => ψ i * e0 j`.
- The Mathlib `TensorProduct ℂ H H` once equipped with the standard
  inner product.

## Relation to no-cloning

The proof is the inner-product mirror of `no_cloning_two_state`: the
isometry now carries `tensor ψ ψ` to `tensor ψ e0` (the deletion
direction). Isometry preservation plus the tensor factorisation give
`⟨ψ, φ⟩² = ⟨ψ, φ⟩` (the same fixed-point equation, with the two sides
of the no-cloning identity swapped), hence `⟨ψ, φ⟩ ∈ {0, 1}`.

## Experimental verification

The no-deleting bound is confirmed wherever exact deletion of an
unknown state would be required but cannot occur; it underwrites the
information-conservation reading of quantum erasure experiments. The
exact bound `< 1` follows immediately from the theorem below, parallel
to the no-cloning case.

## Source

Pati and Braunstein 2000, *Nature* **404**, 164 ("Impossibility of
deleting an unknown quantum state").
-/

open ComplexConjugate

namespace CSD
namespace Empirical
namespace NoDeleting

variable {H Htensor : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]

/-- **No-deleting theorem (two-state form).** Let `H` and `Htensor` be
complex inner product spaces, `tensor : H → H → Htensor` a binary
pairing whose inner-product factorises as `⟨tensor a b, tensor c d⟩
= ⟨a, c⟩ · ⟨b, d⟩`, and `e0 : H` a fixed unit "blank" state.

If `U : Htensor → Htensor` is an isometry (preserves inner products)
that deletes the second copy of two unit states `ψ, φ : H` (with
`‖ψ‖ = ‖φ‖ = 1`) against the same blank, i.e.
`U(tensor ψ ψ) = tensor ψ e0` and `U(tensor φ φ) = tensor φ e0`, then
`⟨ψ, φ⟩ ∈ {0, 1}`.

**On the unit-norm hypotheses.** As in `no_cloning_two_state`, the
algebraic core `⟨ψ, φ⟩² = ⟨ψ, φ⟩` holds regardless of normalisation;
the unit-norm hypotheses are stated so that the second alternative
`⟨ψ, φ⟩ = 1` carries its operational meaning (`φ = ψ` up to phase, by
Cauchy-Schwarz saturation).

**Proof.** Isometry preservation gives
```
⟨ψ, φ⟩ · ⟨ψ, φ⟩ = ⟨tensor ψ ψ, tensor φ φ⟩          (tensor factorisation)
                = ⟨U (tensor ψ ψ), U (tensor φ φ)⟩   (isometry)
                = ⟨tensor ψ e0, tensor φ e0⟩         (deletion)
                = ⟨ψ, φ⟩ · ⟨e0, e0⟩ = ⟨ψ, φ⟩.        (tensor factorisation, e0 unit)
```
So `⟨ψ, φ⟩² = ⟨ψ, φ⟩`, hence `⟨ψ, φ⟩ · (1 − ⟨ψ, φ⟩) = 0`, hence
`⟨ψ, φ⟩ ∈ {0, 1}`. -/
theorem no_deleting_two_state
    (tensor : H → H → Htensor)
    (h_tensor_inner : ∀ a b c d : H,
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (e0 : H) (he0 : ‖e0‖ = 1)
    (ψ φ : H) (_hψ : ‖ψ‖ = 1) (_hφ : ‖φ‖ = 1)
    (U : Htensor → Htensor)
    (hU : ∀ x y : Htensor, inner ℂ (U x) (U y) = inner ℂ x y)
    (h_del_ψ : U (tensor ψ ψ) = tensor ψ e0)
    (h_del_φ : U (tensor φ φ) = tensor φ e0) :
    inner ℂ ψ φ = 0 ∨ inner ℂ ψ φ = 1 := by
  have h_e0_inner : inner ℂ e0 e0 = (1 : ℂ) := by
    rw [@inner_self_eq_norm_sq_to_K ℂ _ _ _, he0]
    simp
  -- Apply isometry preservation to the deletion identities.
  have h_iso :
      inner ℂ (tensor ψ ψ) (tensor φ φ)
        = inner ℂ (tensor ψ e0) (tensor φ e0) := by
    calc inner ℂ (tensor ψ ψ) (tensor φ φ)
        = inner ℂ (U (tensor ψ ψ)) (U (tensor φ φ)) := (hU _ _).symm
      _ = inner ℂ (tensor ψ e0) (tensor φ e0) := by rw [h_del_ψ, h_del_φ]
  -- Use tensor inner-product factorisation on both sides.
  rw [h_tensor_inner, h_tensor_inner, h_e0_inner, mul_one] at h_iso
  -- h_iso : ⟨ψ, φ⟩ * ⟨ψ, φ⟩ = ⟨ψ, φ⟩
  -- Conclude ⟨ψ, φ⟩ ∈ {0, 1}.
  have h_quad : inner ℂ ψ φ * (1 - inner ℂ ψ φ) = 0 := by
    linear_combination -h_iso
  rcases mul_eq_zero.mp h_quad with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination -h)

/-- **No universal deleter (corollary).** No (linear) isometry can
delete a copy of every unit state against a fixed blank. Given any two
unit states `ψ, φ` with `⟨ψ, φ⟩ ∉ {0, 1}` (which exist in any inner
product space of dimension ≥ 2), `no_deleting_two_state` applied to them
rules out a universal deleter. -/
theorem no_universal_deleter_of_witness
    (tensor : H → H → Htensor)
    (h_tensor_inner : ∀ a b c d : H,
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (e0 : H) (he0 : ‖e0‖ = 1)
    (ψ φ : H) (hψ_unit : ‖ψ‖ = 1) (hφ_unit : ‖φ‖ = 1)
    (h_neither : inner ℂ ψ φ ≠ 0 ∧ inner ℂ ψ φ ≠ 1) :
    ¬ ∃ U : Htensor → Htensor,
        (∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) ∧
        U (tensor ψ ψ) = tensor ψ e0 ∧
        U (tensor φ φ) = tensor φ e0 := by
  rintro ⟨U, hU, hψ, hφ⟩
  obtain h | h := no_deleting_two_state tensor h_tensor_inner e0 he0
    ψ φ hψ_unit hφ_unit U hU hψ hφ
  · exact h_neither.1 h
  · exact h_neither.2 h

end NoDeleting
end Empirical
end CSD
