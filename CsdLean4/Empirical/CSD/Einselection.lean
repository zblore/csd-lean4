import CsdLean4.LF6.Decoherence
import CsdLean4.Empirical.QM.Gates.SingleQubit

/-!
# Empirical/CSD: einselection / pointer-basis selection (Build 15a)

**Category:** 6-Local (the open-system / decoherence stratum of D1; the first
einselection result on the LF6-B decoherence machinery).

Decoherence (LF6-B.1, `LF6/Decoherence.lean`) does not merely make the system
state mixed: it **selects a preferred basis**. The reduced state
`decohereReduced ψ = partialTraceRight (V |ψ⟩⟨ψ| Vᴴ)` is *diagonal* in the
measurement (pointer) basis `{eⱼ}` — its off-diagonal coherences vanish there
(`decoherence_offdiagonal_vanish`) — but its coherences **persist** in a rotated
basis. This basis-selectivity is Zurek's einselection: the "why a preferred
basis" content.

## The qubit computation (concrete witness)

For `N = 2`, `decohereReduced ψ = diagonal (p₀, p₁)` with `pⱼ = ‖⟨eⱼ,ψ⟩‖²`
(= `ψⱼ · star ψⱼ`, `decohereReduced_eq_diagonal`). Conjugating by the Hadamard
`qmH` rotates into the `{(e₀±e₁)/√2}` basis:

```
qmH · diag(p₀,p₁) · qmH = (1/2) · !![p₀+p₁, p₀−p₁; p₀−p₁, p₀+p₁],
```

so the rotated-basis off-diagonal entry `(0,1)` equals `(p₀ − p₁)/2`. This is
**nonzero whenever `p₀ ≠ p₁`** (`decohere_hadamard_offDiag` +
`decohere_not_diagonal_in_rotated_basis`). The pointer basis `{e₀,e₁}` is
genuinely einselected: it is the one basis in which the decohered state is
diagonal.

The `p₀ ≠ p₁` hypothesis is **load-bearing and honest**: at `p₀ = p₁` the
reduced state is the fully mixed `(1/2)·I`, which is diagonal in *every* basis,
so there is no preferred basis to select. Einselection is the statement that for
a *generic* superposition (distinct Born weights) the diagonalising basis is
unique.

## Deliverables

- `decohere_hadamard_offDiag` — the rotated off-diagonal value
  `(qmH · ρ_red · qmH) 0 1 = (ψ₀·star ψ₀ − ψ₁·star ψ₁)/2`, every qubit `ψ`
  (computed, not asserted).
- `decohere_diagonal_in_pointer_basis` — `ρ_red` is `Matrix.diagonal` in `{eⱼ}`
  (restates `decohereReduced_eq_diagonal`): the pointer basis is special.
- `decohere_not_diagonal_in_rotated_basis` (THE einselection witness) — for any
  qubit with `p₀ ≠ p₁`, the Hadamard-rotated reduced state has a nonzero `(0,1)`
  off-diagonal: coherence persists in the rotated basis.
- `einselectionWitness` — a concrete superposition `(2,1)` with `p₀ = 4 ≠ 1 = p₁`
  (non-vacuity), and `einselectionWitness_offDiag` — its rotated off-diagonal is
  `3/2 ≠ 0`.
- `einselection` (capstone) — diagonal in the pointer basis (off-diag `0`) AND
  off-diagonal `3/2 ≠ 0` in the Hadamard rotation, for the witness.

## Honest scope and the contrast with #29 (`LF4/TypicalityForcing.lean`)

Einselection here is the **basis selection imposed by the de-isolation /
partial-trace in the pointer basis** (LF6-B). It contrasts sharply with the
typicality layer: `fubiniStudy_forced_by_symmetry` (#29) shows the Fubini–Study
typicality measure is the *unique* `U(N)`-invariant probability measure — it is
basis-**covariant** and picks **no** basis. The preferred basis therefore does
**not** come from the symmetric typicality / sector structure; it comes from the
**measurement context** — which basis the de-isolation couples to and traces in.
Einselection is the symmetry-breaking-by-context layered on the symmetric
substrate.

This is the QM-validity / open-system reading; the CSD content is the
de-isolation reading of which basis is selected. **Honest scope:** single-system;
the pointer basis is the de-isolation's computational basis (the context's
choice). Deriving *which* basis a given physical environment selects (Zurek's
predictability-sieve dynamics, a Hamiltonian-level account) is **not** modelled —
here the basis is the de-isolation's by construction, and the theorem is that
decoherence is basis-**selective** (diagonal in exactly one basis up to
degeneracy), not that the basis is derived from an environment Hamiltonian.

All exports are foundational-triple-only (off `busch_effect_gleason`): the result
is concrete `Matrix` arithmetic on `Fin 2` over the LF6-B `decohereReduced`.
-/

open Matrix
open CSD.LF6 CSD.Empirical.QM.Gates

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Einselection

/-! ### The rotated-basis off-diagonal (the core computation) -/

/-- `((√2)⁻¹)² = 1/2`, the Hadamard normalisation squared (cf. `qmH_mul_self`). -/
private lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **The Hadamard-rotated off-diagonal of the decohered qubit state.**
`(qmH · decohereReduced ψ · qmH) 0 1 = (ψ₀·star ψ₀ − ψ₁·star ψ₁)/2 = (p₀ − p₁)/2`.
Computed from `decohereReduced_eq_diagonal` + concrete `Fin 2` matrix arithmetic:
`qmH = s·!![1,1;1,-1]` with `s² = 1/2`, and `!![1,1;1,-1]·diag(p₀,p₁)·!![1,1;1,-1]`
has `(0,1)` entry `p₀ − p₁`. -/
theorem decohere_hadamard_offDiag (ψ : EuclideanSpace ℂ (Fin 2)) :
    (qmH * decohereReduced ψ * qmH) 0 1
      = (ψ 0 * star (ψ 0) - ψ 1 * star (ψ 1)) / 2 := by
  rw [decohereReduced_eq_diagonal, qmH, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sqrt_two_inv_sq, Matrix.smul_apply, smul_eq_mul]
  have hM : (!![(1 : ℂ), 1; 1, -1] * Matrix.diagonal (fun i => ψ i * star (ψ i))
              * !![(1 : ℂ), 1; 1, -1]) 0 1
            = ψ 0 * star (ψ 0) - ψ 1 * star (ψ 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Fin.isValue,
      Fin.reduceEq, if_true, if_false, mul_zero, add_zero, zero_add]
    rw [show !![(1 : ℂ), 1; 1, -1] 0 0 = 1 from rfl,
      show !![(1 : ℂ), 1; 1, -1] 0 1 = 1 from rfl,
      show !![(1 : ℂ), 1; 1, -1] 1 1 = -1 from rfl]
    ring
  rw [hM]; ring

/-! ### (1) Diagonal in the pointer basis -/

/-- **The decohered state is diagonal in the pointer basis `{eⱼ}`** (restates
`decohereReduced_eq_diagonal`): `decohereReduced ψ = diagonal (j ↦ ψⱼ·star ψⱼ)`.
The off-diagonal coherences vanish (`decoherence_offdiagonal_vanish`) — the pointer
basis is the special, diagonalising basis. -/
theorem decohere_diagonal_in_pointer_basis {N : ℕ} [NeZero N] (ψ : EuclideanSpace ℂ (Fin N)) :
    decohereReduced ψ = Matrix.diagonal (fun i => ψ i * star (ψ i)) :=
  decohereReduced_eq_diagonal ψ

/-! ### (2) NOT diagonal in the Hadamard-rotated basis (the einselection witness) -/

/-- **THE einselection witness: coherence persists in the rotated basis.**
For any qubit `ψ` whose two Born weights differ (`p₀ ≠ p₁`, i.e.
`ψ₀·star ψ₀ ≠ ψ₁·star ψ₁`), the Hadamard-conjugated reduced state has a **nonzero**
`(0,1)` off-diagonal `(p₀ − p₁)/2`. So the decohered state is diagonal in the
pointer basis but NOT in the Hadamard-rotated basis: the pointer basis is genuinely
selected, not arbitrary. The `p₀ ≠ p₁` hypothesis is load-bearing — at `p₀ = p₁`
the state is fully mixed and diagonal in every basis. -/
theorem decohere_not_diagonal_in_rotated_basis (ψ : EuclideanSpace ℂ (Fin 2))
    (hp : ψ 0 * star (ψ 0) ≠ ψ 1 * star (ψ 1)) :
    (qmH * decohereReduced ψ * qmH) 0 1 ≠ 0 := by
  rw [decohere_hadamard_offDiag, div_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr hp, by norm_num⟩

/-! ### Concrete non-vacuity witness -/

/-- A concrete qubit superposition `(2, 1)` with distinct Born weights
`p₀ = 4 ≠ 1 = p₁` (unnormalised; the einselection off-diagonal is scale-covariant
and its non-vanishing depends only on `p₀ ≠ p₁`). -/
noncomputable def einselectionWitness : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (2 : ℂ) + EuclideanSpace.single 1 (1 : ℂ)

@[simp] lemma einselectionWitness_apply_zero : einselectionWitness 0 = 2 := by
  simp [einselectionWitness]

@[simp] lemma einselectionWitness_apply_one : einselectionWitness 1 = 1 := by
  simp [einselectionWitness]

/-- The witness has distinct Born weights: `p₀ = 4 ≠ 1 = p₁`. Non-vacuity for
`decohere_not_diagonal_in_rotated_basis`. -/
lemma einselectionWitness_weights_ne :
    einselectionWitness 0 * star (einselectionWitness 0)
      ≠ einselectionWitness 1 * star (einselectionWitness 1) := by
  simp only [einselectionWitness_apply_zero, einselectionWitness_apply_one, star_one,
    star_ofNat]
  norm_num

/-- **The witness's rotated off-diagonal is `3/2 ≠ 0`.** Concrete value of the
einselection coherence in the Hadamard-rotated basis: `(p₀ − p₁)/2 = (4 − 1)/2 = 3/2`. -/
theorem einselectionWitness_offDiag :
    (qmH * decohereReduced einselectionWitness * qmH) 0 1 = 3 / 2 := by
  rw [decohere_hadamard_offDiag, einselectionWitness_apply_zero, einselectionWitness_apply_one,
    star_one, star_ofNat]
  norm_num

/-! ### Capstone -/

/-- **The einselection capstone: decoherence selects the pointer basis `{e₀,e₁}`.**
For the witness superposition (distinct Born weights):

1. **diagonal in the pointer basis** — `decohereReduced einselectionWitness 0 1 = 0`
   (`decoherence_offdiagonal_vanish`): the pointer basis is the diagonalising one;
2. **off-diagonal in the Hadamard rotation** —
   `(qmH · ρ_red · qmH) 0 1 = 3/2` (`einselectionWitness_offDiag`);
3. **and it is nonzero** — coherence persists in the rotated basis, so the pointer
   basis is genuinely selected.

This is the "why a preferred basis" result: decoherence is basis-**selective**.
The selected basis is the de-isolation's pointer (computational) basis — the
**measurement context's** choice — NOT the symmetric Fubini–Study typicality
(`LF4.fubiniStudy_forced_by_symmetry`, #29: the unique `U(N)`-invariant law,
basis-COVARIANT, picks no basis). Einselection is symmetry-breaking-by-context on
the symmetric substrate. Honest scope: single-system; the basis is posited as the
de-isolation's context, not derived from an environment Hamiltonian. -/
theorem einselection :
    decohereReduced einselectionWitness 0 1 = 0
    ∧ (qmH * decohereReduced einselectionWitness * qmH) 0 1 = 3 / 2
    ∧ (qmH * decohereReduced einselectionWitness * qmH) 0 1 ≠ 0 := by
  refine ⟨decoherence_offdiagonal_vanish einselectionWitness (by decide), einselectionWitness_offDiag, ?_⟩
  rw [einselectionWitness_offDiag]; norm_num

end Einselection
end CSDBridge
end Empirical
end CSD
